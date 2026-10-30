#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minecraft Java 通用版本下载器 v4.0
使用 BMCLAPI / MCBBS / 官方源 多镜像智能加速下载。
并发下载小文件、复用 HTTPS 连接；大文件分段下载，支持校验与续传。
支持 1.12 至最新版本，树形版本选择界面。
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import json
import os
import sys
import threading
import time
import hashlib
import urllib.request
import urllib.error
import urllib.parse
import ssl
import http.client
import re
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue
import platform as pf

# ============================================================
# 全局常量
# ============================================================
SSL_CONTEXT = ssl.create_default_context()
USER_AGENT = "MCUniDownloader/4.0"
CHUNK_SIZE = 256 * 1024          # 256KB 读取块
SEGMENT_MIN_SIZE = 4 * 1024 * 1024   # 4MB 以上启用分段
SEGMENT_SIZE = 4 * 1024 * 1024      # 每段 4MB
MAX_SEGMENTS = 8                    # 最大分段数（PCL2 风格）
DEFAULT_THREADS = 32
MAX_THREADS = 64
MIN_VERSION = "1.12"

# ============================================================
# 多镜像源配置（PCL2 加速策略：多源 fallback + 智能选路）
# ============================================================
MIRRORS = {
    "BMCLAPI (推荐)": {
        "version_manifest": "https://bmclapi2.bangbang93.com/mc/game/version_manifest.json",
        "version_manifest_v2": "https://bmclapi2.bangbang93.com/mc/game/version_manifest_v2.json",
        "version_json": "https://bmclapi2.bangbang93.com/version/{version}/json",
        "version_client": "https://bmclapi2.bangbang93.com/version/{version}/client",
        "libraries": "https://bmclapi2.bangbang93.com/maven/{path}",
        "asset_index": "https://bmclapi2.bangbang93.com/v1/packages/{sha1}/{id}.json",
        "asset_file": "https://bmclapi2.bangbang93.com/assets/{prefix}/{hash}",
        "forge": "https://bmclapi2.bangbang93.com/forge/{path}",
        "fabric": "https://bmclapi2.bangbang93.com/fabric/{path}",
    },
    "MCBBS": {
        "version_manifest": "https://download.mcbbs.net/mc/game/version_manifest.json",
        "version_manifest_v2": "https://download.mcbbs.net/mc/game/version_manifest_v2.json",
        "version_json": "https://download.mcbbs.net/version/{version}/json",
        "version_client": "https://download.mcbbs.net/version/{version}/client",
        "libraries": "https://download.mcbbs.net/maven/{path}",
        "asset_index": "https://download.mcbbs.net/v1/packages/{sha1}/{id}.json",
        "asset_file": "https://download.mcbbs.net/assets/{prefix}/{hash}",
        "forge": "https://download.mcbbs.net/forge/{path}",
        "fabric": "https://download.mcbbs.net/fabric/{path}",
    },
}

# 官方备用源
OFFICIAL_URLS = {
    "version_manifest": "https://launchermeta.mojang.com/mc/game/version_manifest.json",
    "version_manifest_v2": "https://launchermeta.mojang.com/mc/game/version_manifest_v2.json",
    "libraries": "https://libraries.minecraft.net/{path}",
    "asset_file": "https://resources.download.minecraft.net/{prefix}/{hash}",
}


def http_get(url, timeout=30):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    return urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT)


class ReusableHTTP:
    """
    每个线程持有持久连接（HTTP keep-alive），
    实现连接复用减少握手开销，类似 PCL2 的连接池策略。
    """
    def __init__(self):
        self.local = threading.local()

    def close(self):
        connections = getattr(self.local, "connections", {})
        for conn in connections.values():
            try:
                conn.close()
            except Exception:
                pass
        self.local.connections = {}

    def open(self, url, headers=None, timeout=30):
        headers = dict(headers or {})
        headers["User-Agent"] = USER_AGENT
        headers["Connection"] = "keep-alive"
        for _ in range(6):
            parts = urllib.parse.urlsplit(url)
            if parts.scheme not in ("https", "http"):
                raise ValueError(f"Unsupported URL: {url}")
            origin = (parts.scheme, parts.hostname, parts.port)
            connections = getattr(self.local, "connections", None)
            if connections is None:
                connections = self.local.connections = {}
            conn = connections.get(origin)
            if conn is None or getattr(conn, "_closed", False):
                cls = http.client.HTTPSConnection if parts.scheme == "https" else http.client.HTTPConnection
                try:
                    conn = cls(parts.hostname, parts.port or (443 if parts.scheme == "https" else 80), timeout=timeout)
                except Exception:
                    raise
                connections[origin] = conn
            try:
                conn.timeout = timeout
                path = urllib.parse.urlunsplit(("", "", parts.path or "/", parts.query, ""))
                conn.request("GET", path, headers=headers)
                resp = conn.getresponse()
            except (OSError, http.client.HTTPException):
                connections.pop(origin, None)
                try:
                    conn.close()
                except Exception:
                    pass
                raise
            if resp.status in (301, 302, 303, 307, 308):
                location = resp.getheader("Location")
                try:
                    resp.read()
                    resp.close()
                except Exception:
                    pass
                if not location:
                    raise OSError("Missing redirect location")
                url = urllib.parse.urljoin(url, location)
                continue
            if resp.status not in (200, 206):
                status = resp.status
                try:
                    resp.read()
                    resp.close()
                except Exception:
                    pass
                raise OSError(f"HTTP {status}: {url}")
            return resp
        raise OSError(f"Too many redirects: {url}")


def remove_if_exists(path):
    try:
        Path(path).unlink()
    except FileNotFoundError:
        pass


class DownloadWorker:
    """
    核心下载器：多镜像 fallback + 分段下载 + SHA1校验 + 断点续传
    参考 PCL2 启动器下载策略优化：
    - 多源智能 fallback
    - 大文件 4~8 段并发下载
    - 连接池复用
    - 失败自动重试 + 切换源
    """

    def __init__(self, mirror_name, target_dir, version_id, progress_callback,
                 log_callback, done_callback, num_threads=DEFAULT_THREADS):
        self.mirror_name = mirror_name
        self.mirror = MIRRORS[mirror_name]
        self.target_dir = Path(target_dir)
        self.version_id = version_id
        self.progress_cb = progress_callback
        self.log_cb = log_callback
        self.done_cb = done_callback
        self.cancelled = False
        self.http = ReusableHTTP()
        self.num_threads = num_threads
        self.stats_lock = threading.Lock()
        self.downloaded_count = 0
        self.failed_count = 0
        self.skipped_count = 0
        self.total_count = 0
        self.bytes_received = 0
        self._batch_start = 0

    def log(self, msg):
        self.log_cb(msg)

    def update_progress(self, value, text=""):
        self.progress_cb(value, text)

    def start(self):
        thread = threading.Thread(target=self.run, daemon=True)
        thread.start()

    def cancel(self):
        self.cancelled = True
        self.log("[CANCEL] 用户取消下载...")

    @staticmethod
    def _content_range(value):
        match = re.fullmatch(r"bytes (\d+)-(\d+)/(\d+)", value or "")
        return tuple(map(int, match.groups())) if match else None

    def _stream_to_part(self, url, part, start=0, end=None, total=None):
        """流式下载，支持 Range 分段"""
        headers = {}
        if start or end is not None:
            headers["Range"] = f"bytes={start}-{'' if end is None else end}"
        resp = self.http.open(url, headers, timeout=30)
        try:
            if start or end is not None:
                length = self._content_range(resp.getheader("Content-Range"))
                if resp.status != 206 or not length or length[0] != start:
                    raise ValueError("Server did not honor requested byte range")
            expected = end - start + 1 if end is not None else None
            if expected is None and resp.getheader("Content-Length"):
                expected = int(resp.getheader("Content-Length"))
            count = 0
            mode = "ab" if start else "wb"
            with open(part, mode) as out:
                while True:
                    if self.cancelled:
                        raise InterruptedError("cancelled")
                    block = resp.read(CHUNK_SIZE)
                    if not block:
                        break
                    count += len(block)
                    if expected is not None and count > expected:
                        raise ValueError("Response exceeded expected size")
                    out.write(block)
                    with self.stats_lock:
                        self.bytes_received += len(block)
            if expected is not None and count != expected:
                raise ValueError(f"Incomplete response: {count} / {expected}")
        finally:
            try:
                resp.close()
            except Exception:
                pass

    def _download_with_resume(self, url, dest_path, check_sha1):
        """支持断点续传的下载"""
        part = dest_path.with_name(dest_path.name + ".part")
        offset = 0
        if part.exists() and check_sha1:
            offset = part.stat().st_size
        if offset:
            try:
                self._stream_to_part(url, part, start=offset)
            except ValueError:
                remove_if_exists(part)
                self._stream_to_part(url, part)
        else:
            self._stream_to_part(url, part)
        if check_sha1 and self._sha1(part) != check_sha1:
            remove_if_exists(part)
            raise ValueError("SHA1 mismatch")
        os.replace(part, dest_path)

    def _segmented_download(self, url, dest_path, total):
        """
        分段下载大文件（PCL2 风格：多段并发下载后合并）
        自动根据文件大小计算分段数（2~8 段）
        """
        seg_count = min(MAX_SEGMENTS, max(2, (total + SEGMENT_SIZE - 1) // SEGMENT_SIZE), self.num_threads)
        segments = []
        for idx in range(seg_count):
            start = total * idx // seg_count
            end = total * (idx + 1) // seg_count - 1
            part = dest_path.with_name(f"{dest_path.name}.part.{idx}")
            size = part.stat().st_size if part.exists() else 0
            if size > end - start + 1:
                part.unlink()
                size = 0
            segments.append((part, start, end, size))

        def fetch(seg):
            part, start, end, size = seg
            if size < end - start + 1:
                self._stream_to_part(url, part, start=start + size, end=end, total=total)

        with ThreadPoolExecutor(max_workers=seg_count) as pool:
            list(pool.map(fetch, segments))

        combined = dest_path.with_name(dest_path.name + ".part")
        with open(combined, "wb") as out:
            for part, start, end, size in segments:
                with open(part, "rb") as src:
                    while True:
                        block = src.read(CHUNK_SIZE)
                        if not block:
                            break
                        out.write(block)
        if combined.stat().st_size != total:
            remove_if_exists(combined)
            for part, _, _, _ in segments:
                remove_if_exists(part)
            raise ValueError("Segment size mismatch")
        return combined, [s[0] for s in segments]

    def _download_single(self, urls, dest_path, description="", check_sha1=None, size=None):
        """
        智能单文件下载：
        - 优先使用主镜像源
        - 主源失败自动 fallback 到其他源
        - 大文件自动启用分段下载
        - SHA1 校验确保完整性
        """
        if self.cancelled:
            return False, "cancelled"
        dest_path = Path(dest_path)
        dest_path.parent.mkdir(parents=True, exist_ok=True)
        # 已存在且校验通过则跳过
        if dest_path.exists() and check_sha1 and self._sha1(dest_path) == check_sha1:
            return True, "skipped"
        if dest_path.exists() and not check_sha1:
            return True, "skipped"

        candidates = list(dict.fromkeys(urls if isinstance(urls, (list, tuple)) else [urls]))
        error = "no download source"

        for url in candidates:
            for attempt in range(3):
                if self.cancelled:
                    return False, "cancelled"
                try:
                    # 大文件 + 支持 Range -> 分段下载
                    if check_sha1 and size and size >= SEGMENT_MIN_SIZE and self.num_threads > 1:
                        try:
                            probe = self.http.open(url, {"Range": "bytes=0-0"}, timeout=20)
                            try:
                                ranges = self._content_range(probe.getheader("Content-Range"))
                                ranged = probe.status == 206 and ranges == (0, 0, size)
                            finally:
                                try:
                                    probe.close()
                                except Exception:
                                    pass
                        except Exception:
                            ranged = False

                        if ranged:
                            part, seg_parts = self._segmented_download(url, dest_path, size)
                            if check_sha1 and self._sha1(part) != check_sha1:
                                remove_if_exists(part)
                                for seg in seg_parts:
                                    remove_if_exists(seg)
                                raise ValueError("SHA1 mismatch after segmented download")
                            os.replace(part, dest_path)
                            for seg in seg_parts:
                                remove_if_exists(seg)
                            return True, "ok"

                    # 普通下载
                    self._download_with_resume(url, dest_path, check_sha1)
                    return True, "ok"
                except Exception as exc:
                    error = str(exc)
                    self.http.close()
                    if not self.cancelled and attempt < 2:
                        time.sleep(0.3 * (attempt + 1))
        return False, "cancelled" if self.cancelled else error

    def _download_worker_thread(self, task_queue, results_queue):
        """工作线程：从队列取任务并下载"""
        while not self.cancelled:
            try:
                task = task_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if task is None:
                break
            urls, dest, desc, sha1, size = task
            try:
                ok, status = self._download_single(urls, dest, desc, sha1, size)
            except Exception as exc:
                ok, status = False, str(exc)
            results_queue.put((desc, ok, status))

    def _download_batch(self, tasks, step_name, progress_start, progress_end):
        """
        并发批量下载（PCL2 风格：线程池 + 任务队列）
        """
        if not tasks:
            return True

        tasks = list({str(task[1]): task for task in tasks}.values())
        self.total_count = len(tasks)
        batch_time = time.monotonic()
        batch_bytes = self.bytes_received
        self.downloaded_count = 0
        self.failed_count = 0
        self.skipped_count = 0

        task_queue = queue.Queue()
        results_queue = queue.Queue()

        for t in tasks:
            task_queue.put(t)
        for _ in range(min(self.num_threads, len(tasks))):
            task_queue.put(None)

        threads = []
        for _ in range(min(self.num_threads, len(tasks))):
            t = threading.Thread(target=self._download_worker_thread,
                                 args=(task_queue, results_queue), daemon=True)
            t.start()
            threads.append(t)

        completed = 0
        last_update = time.time()
        while completed < len(tasks) and not self.cancelled:
            try:
                desc, ok, status = results_queue.get(timeout=0.5)
                completed += 1
                if status == "skipped":
                    self.skipped_count += 1
                elif ok:
                    self.downloaded_count += 1
                else:
                    self.failed_count += 1
                    if status != "cancelled":
                        self.log(f"  [FAIL] {desc[:60]}: {status}")

                now = time.time()
                if now - last_update > 0.2 or completed == len(tasks):
                    last_update = now
                    pct = progress_start + int((completed / len(tasks)) * (progress_end - progress_start))
                    elapsed = time.monotonic() - batch_time
                    speed_mib = (self.bytes_received - batch_bytes) / max(0.001, elapsed) / 1048576
                    speed_info = f" ({speed_mib:.1f} MiB/s)" if speed_mib > 0 else ""
                    skip_info = f" [跳过:{self.skipped_count}]" if self.skipped_count else ""
                    self.update_progress(pct, f"{step_name} {completed}/{len(tasks)}{speed_info}{skip_info}")
            except queue.Empty:
                continue

        for t in threads:
            t.join(timeout=35)

        return not self.cancelled and self.failed_count == 0

    @staticmethod
    def _sha1(filepath):
        h = hashlib.sha1()
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(8192), b""):
                h.update(chunk)
        return h.hexdigest()

    @staticmethod
    def _get_os():
        system = pf.system().lower()
        if system == "windows":
            return "windows"
        elif system == "darwin":
            return "osx"
        return "linux"

    @staticmethod
    def _check_rules(rules):
        if not rules:
            return True
        allow = False
        for rule in rules:
            action = rule.get("action", "allow")
            os_match = True
            if "os" in rule:
                os_rule = rule["os"]
                current_os = DownloadWorker._get_os()
                if "name" in os_rule:
                    os_match = (os_rule["name"] == current_os)
            if os_match:
                allow = action == "allow"
        return allow

    def _should_download_natives(self, classifier_name):
        system = self._get_os()
        if system == "windows":
            return "windows" in classifier_name
        elif system == "osx":
            return "osx" in classifier_name or "macos" in classifier_name
        elif system == "linux":
            return "linux" in classifier_name
        return False

    def _create_launcher_files(self):
        self.log("\n[INFO] 创建启动器配置文件...")
        profiles_path = self.target_dir / "launcher_profiles.json"
        if not profiles_path.exists():
            profiles = {
                "profiles": {
                    "(Default)": {
                        "name": "(Default)",
                        "type": "custom",
                        "created": time.strftime("%Y-%m-%dT%H:%M:%S.000Z"),
                        "lastUsed": time.strftime("%Y-%m-%dT%H:%M:%S.000Z"),
                        "lastVersionId": self.version_id,
                        "javaDir": "",
                        "resolution": {"width": 854, "height": 480}
                    }
                },
                "selectedProfile": "(Default)",
                "clientToken": "00000000-0000-0000-0000-000000000000",
                "authenticationDatabase": {},
                "LauncherVersion": {"name": "MCUniDownloader", "format": 21, "profilesFormat": 1}
            }
            profiles_path.write_text(json.dumps(profiles, indent=2, ensure_ascii=False))
            self.log("  [OK] launcher_profiles.json 已创建")

    def _verify_install(self):
        self.log("\n[INFO] 验证安装完整性...")
        version_dir = self.target_dir / "versions" / self.version_id
        checks = [
            (version_dir / f"{self.version_id}.json", "版本配置文件"),
            (version_dir / f"{self.version_id}.jar", "客户端JAR"),
            (self.target_dir / "libraries", "依赖库目录"),
            (self.target_dir / "assets", "资源目录"),
        ]
        all_ok = True
        for path, desc in checks:
            if path.exists():
                self.log(f"  [OK] {desc}: {path}")
            else:
                self.log(f"  [FAIL] {desc}: 缺失")
                all_ok = False
        return all_ok

    def _try_fetch_manifest(self):
        """智能获取 manifest：多源 fallback"""
        sources = [
            self.mirror.get("version_manifest_v2"),
            self.mirror.get("version_manifest"),
            OFFICIAL_URLS["version_manifest_v2"],
            OFFICIAL_URLS["version_manifest"],
        ]
        for url in sources:
            if not url:
                continue
            try:
                with self.http.open(url, timeout=15) as resp:
                    return json.loads(resp.read())
            except Exception:
                self.http.close()
                continue
        raise Exception("无法从任何源获取版本列表")

    def _build_source_urls(self, url_template, fallback_template=None, fallback_url=None):
        """构建多源 URL 列表（主源 + 备用源 + 官方源）"""
        urls = []
        if url_template:
            urls.append(url_template)
        if fallback_template:
            urls.append(fallback_template)
        if fallback_url:
            urls.append(fallback_url)
        return list(dict.fromkeys(urls))

    def run(self):
        t0 = time.time()
        try:
            self.log("=" * 55)
            self.log(f"[INFO] 开始下载 Minecraft {self.version_id}")
            self.log(f"[INFO] 目标目录: {self.target_dir}")
            self.log(f"[INFO] 镜像源: {self.mirror_name}")
            self.log(f"[INFO] 并发线程: {self.num_threads}")
            self.log(f"[INFO] 分段阈值: {SEGMENT_MIN_SIZE // 1024 // 1024}MB, 最大分段: {MAX_SEGMENTS}")
            self.log("=" * 55)

            # ========== Step 1: 获取版本 manifest ==========
            self.update_progress(0, "正在连接镜像源获取版本信息...")
            self.log("\n[STEP 1/5] 获取版本信息...")
            manifest = self._try_fetch_manifest()
            self.log("  [OK] 版本 manifest 加载成功")

            version_info = None
            for v in manifest.get("versions", []):
                if v["id"] == self.version_id:
                    version_info = v
                    break
            if not version_info:
                self.log(f"[ERROR] 未找到版本 {self.version_id}")
                self.done_cb(False)
                return

            # ========== Step 2: 下载版本 JSON 和客户端 JAR ==========
            self.update_progress(5, "正在下载版本配置和客户端...")
            self.log("\n[STEP 2/5] 下载版本配置和客户端...")

            # 版本 JSON
            version_json_data = None
            vjson_sources = self._build_source_urls(
                self.mirror.get("version_json", "").format(version=self.version_id),
            )
            if version_info.get("url"):
                vjson_sources.append(version_info["url"])
            for url in vjson_sources:
                try:
                    with self.http.open(url, timeout=30) as resp:
                        version_json_data = resp.read()
                    break
                except Exception:
                    self.http.close()
                    continue

            if not version_json_data:
                self.log("[ERROR] 无法下载版本 JSON")
                self.done_cb(False)
                return

            version_json = json.loads(version_json_data)
            version_dir = self.target_dir / "versions" / self.version_id
            version_dir.mkdir(parents=True, exist_ok=True)
            json_path = version_dir / f"{self.version_id}.json"
            json_path.write_bytes(version_json_data)
            self.log(f"  [OK] {self.version_id}.json")

            # 客户端 JAR
            client_info = version_json.get("downloads", {}).get("client", {})
            client_mirror = self.mirror.get("version_client", "").format(version=self.version_id)
            client_sources = [client_mirror]
            if client_info.get("url"):
                client_sources.append(client_info["url"])
            client_jar_path = version_dir / f"{self.version_id}.jar"
            client_sha1 = client_info.get("sha1")
            client_size = client_info.get("size")
            ok, status = self._download_single(client_sources, client_jar_path, "客户端JAR",
                                               client_sha1, client_size)
            if ok:
                self.log(f"  [OK] {self.version_id}.jar ({'已跳过' if status == 'skipped' else '已下载'})")
            else:
                self.log(f"  [FAIL] {self.version_id}.jar: {status}")

            # ========== Step 3: 并发下载依赖库 ==========
            self.update_progress(15, "准备下载依赖库...")
            self.log(f"\n[STEP 3/5] 下载依赖库 (并发 {self.num_threads} 线程)...")
            libraries = version_json.get("libraries", [])
            lib_tasks = []
            for lib in libraries:
                if not self._check_rules(lib.get("rules", [])):
                    continue
                lib_name = lib.get("name", "unknown")
                lib_downloads = lib.get("downloads", {})

                artifact = lib_downloads.get("artifact")
                if artifact:
                    mirror_url = self.mirror.get("libraries", "").format(path=artifact["path"])
                    official_url = OFFICIAL_URLS["libraries"].format(path=artifact["path"])
                    sources = [mirror_url, official_url]
                    lib_path = self.target_dir / "libraries" / artifact["path"]
                    lib_tasks.append((sources, lib_path, lib_name[:50], artifact.get("sha1"), artifact.get("size")))

                classifiers = lib_downloads.get("classifiers", {})
                for cls_name, cls_info in classifiers.items():
                    if "natives" in cls_name and not self._should_download_natives(cls_name):
                        continue
                    mirror_url = self.mirror.get("libraries", "").format(path=cls_info["path"])
                    official_url = OFFICIAL_URLS["libraries"].format(path=cls_info["path"])
                    sources = [mirror_url, official_url]
                    lib_path = self.target_dir / "libraries" / cls_info["path"]
                    lib_tasks.append((sources, lib_path, f"{lib_name[:30]} ({cls_name[:15]})",
                                      cls_info.get("sha1"), cls_info.get("size")))

            self._batch_start = time.time()
            libraries_ok = self._download_batch(lib_tasks, "依赖库", 15, 50)
            elapsed_libs = time.time() - self._batch_start
            self.log(f"  依赖库: 下载 {self.downloaded_count}, 跳过 {self.skipped_count}, "
                     f"失败 {self.failed_count} ({elapsed_libs:.1f}s)")

            # ========== Step 4: 下载资源文件 ==========
            self.update_progress(50, "正在下载资源文件...")
            self.log(f"\n[STEP 4/5] 下载资源文件 (并发 {self.num_threads} 线程)...")
            asset_index_id = version_json.get("assetIndex", {}).get("id") or version_json.get("assets", "legacy")
            asset_index_info = version_json.get("assetIndex", {})

            assets_ok = False
            asset_index_data = None
            if asset_index_info:
                asset_index_sha1 = asset_index_info.get("sha1", "")
                ai_mirror = self.mirror.get("asset_index", "").format(sha1=asset_index_sha1, id=asset_index_id)
                try:
                    with self.http.open(ai_mirror, timeout=30) as resp:
                        asset_index_data = resp.read()
                    self.log("  [OK] 资源索引下载完成")
                except Exception as e:
                    self.log(f"  [WARN] 资源索引下载失败: {e}")

            if asset_index_data:
                asset_index = json.loads(asset_index_data)
                ai_dir = self.target_dir / "assets" / "indexes"
                ai_dir.mkdir(parents=True, exist_ok=True)
                ai_path = ai_dir / f"{asset_index_id}.json"
                ai_path.write_bytes(asset_index_data)

                objects = asset_index.get("objects", {})
                asset_tasks = []
                for obj_name, obj_info in objects.items():
                    hash_val = obj_info["hash"]
                    hash_prefix = hash_val[:2]
                    asset_mirror = self.mirror.get("asset_file", "").format(prefix=hash_prefix, hash=hash_val)
                    asset_official = OFFICIAL_URLS["asset_file"].format(prefix=hash_prefix, hash=hash_val)
                    sources = [asset_mirror, asset_official]
                    asset_path = self.target_dir / "assets" / "objects" / hash_prefix / hash_val
                    asset_tasks.append((sources, asset_path, f"assets/{obj_name[:30]}",
                                        hash_val, obj_info.get("size")))

                self._batch_start = time.time()
                assets_ok = self._download_batch(asset_tasks, "资源文件", 50, 95)
                elapsed_assets = time.time() - self._batch_start
                self.log(f"  资源文件: 下载 {self.downloaded_count}, 跳过 {self.skipped_count}, "
                         f"失败 {self.failed_count} ({elapsed_assets:.1f}s)")

            # ========== Step 5: 完成 ==========
            if self.cancelled or not (ok and libraries_ok and assets_ok):
                self.log("[WARN] 下载已取消或存在失败文件；重新下载时已校验文件会自动跳过。")
                self.done_cb(False)
                return

            self._create_launcher_files()
            self.update_progress(100, "下载完成！")
            total_time = time.time() - t0
            self.log("\n" + "=" * 55)
            self.log(f"[DONE] Minecraft {self.version_id} 下载完成！")
            self.log(f"[DONE] 耗时: {total_time:.1f}秒 ({total_time / 60:.1f}分钟)")
            self.log(f"[DONE] 游戏目录: {self.target_dir}")
            self.log(f"[DONE] PCL2 / HMCL 启动器可直接选择此目录作为游戏目录")
            self.done_cb(self._verify_install())

        except Exception as e:
            self.log(f"\n[ERROR] 错误: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.done_cb(False)


# ============================================================
# GUI 应用（树形版本选择）
# ============================================================
class MCUniDownloaderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Minecraft Java 通用版本下载器 v4.0")
        self.root.geometry("820x680")
        self.root.resizable(True, True)

        # DPI 感知
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

        self.worker = None
        self.version_list = []          # 所有版本
        self.version_details = {}       # {vid: info}
        self.version_tree = {}          # {major_ver: [version_info, ...]}
        self._build_ui()
        self._load_versions_async()

    def _build_ui(self):
        main_frame = ttk.Frame(self.root, padding=12)
        main_frame.pack(fill=tk.BOTH, expand=True)

        # 标题
        title_frame = ttk.Frame(main_frame)
        title_frame.pack(fill=tk.X, pady=(0, 8))
        ttk.Label(title_frame, text="Minecraft Java 通用版本下载器 v4.0",
                  font=("Microsoft YaHei UI", 15, "bold")).pack(side=tk.LEFT)
        ttk.Label(title_frame, text="1.12 ~ 最新版 | PCL2 多源加速",
                  font=("Microsoft YaHei UI", 9)).pack(side=tk.RIGHT)

        # 镜像选择
        mirror_frame = ttk.LabelFrame(main_frame, text="下载镜像源", padding=8)
        mirror_frame.pack(fill=tk.X, pady=4)
        self.mirror_var = tk.StringVar(value=list(MIRRORS.keys())[0])
        mirror_combo = ttk.Combobox(mirror_frame, textvariable=self.mirror_var,
                                    values=list(MIRRORS.keys()), state="readonly", width=30)
        mirror_combo.pack(side=tk.LEFT, padx=4)
        ttk.Label(mirror_frame, text="自动多源 fallback: 主源失败自动切换备用源",
                  font=("Microsoft YaHei UI", 8)).pack(side=tk.RIGHT, padx=4)

        # 线程设置
        thread_frame = ttk.Frame(main_frame)
        thread_frame.pack(fill=tk.X, pady=2)
        ttk.Label(thread_frame, text="并发线程数:", font=("Microsoft YaHei UI", 9)).pack(side=tk.LEFT, padx=4)
        self.thread_var = tk.IntVar(value=DEFAULT_THREADS)
        thread_spin = ttk.Spinbox(thread_frame, from_=1, to=MAX_THREADS, textvariable=self.thread_var, width=5)
        thread_spin.pack(side=tk.LEFT, padx=4)
        ttk.Label(thread_frame, text=f"(1-{MAX_THREADS}; 推荐 32-48；大文件最多 {MAX_SEGMENTS} 路分段)",
                  font=("Microsoft YaHei UI", 8)).pack(side=tk.LEFT, padx=4)

        # 版本选择（树形）
        ver_frame = ttk.LabelFrame(main_frame, text="选择版本 (大版本分组)", padding=8)
        ver_frame.pack(fill=tk.X, pady=4)

        # 树形控件
        tree_frame = ttk.Frame(ver_frame)
        tree_frame.pack(fill=tk.X, side=tk.LEFT, expand=True)

        self.version_tree_widget = ttk.Treeview(tree_frame, height=8, show="tree", selectmode="browse")
        self.version_tree_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.version_tree_widget.yview)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.version_tree_widget.configure(yscrollcommand=tree_scroll.set)
        self.version_tree_widget.bind("<<TreeviewSelect>>", self._on_tree_select)

        # 版本信息
        info_frame = ttk.Frame(ver_frame)
        info_frame.pack(side=tk.RIGHT, padx=8)
        self.ver_info_label = ttk.Label(info_frame, text="", font=("Microsoft YaHei UI", 9),
                                         wraplength=200)
        self.ver_info_label.pack(anchor=tk.W)
        ttk.Button(info_frame, text="刷新", width=8,
                   command=self._load_versions_async).pack(pady=4)

        # 目录选择
        dir_frame = ttk.LabelFrame(main_frame, text="游戏目录 (.minecraft)", padding=8)
        dir_frame.pack(fill=tk.X, pady=4)
        self.dir_var = tk.StringVar()
        default_dir = self._get_default_minecraft_dir()
        self.dir_var.set(str(default_dir))
        dir_entry = ttk.Entry(dir_frame, textvariable=self.dir_var, width=55)
        dir_entry.pack(side=tk.LEFT, padx=4, fill=tk.X, expand=True)
        ttk.Button(dir_frame, text="浏览...", width=8,
                   command=self._browse_dir).pack(side=tk.RIGHT, padx=2)

        # 下载控制
        ctrl_frame = ttk.Frame(main_frame)
        ctrl_frame.pack(fill=tk.X, pady=6)
        self.download_btn = ttk.Button(ctrl_frame, text="开始下载",
                                       command=self._start_download, width=16)
        self.download_btn.pack(side=tk.LEFT, padx=4)
        self.cancel_btn = ttk.Button(ctrl_frame, text="取消",
                                     command=self._cancel_download, width=10, state=tk.DISABLED)
        self.cancel_btn.pack(side=tk.LEFT, padx=4)

        # 进度条
        self.progress_var = tk.DoubleVar(value=0)
        self.progress_bar = ttk.Progressbar(main_frame, variable=self.progress_var,
                                            maximum=100, length=400, mode='determinate')
        self.progress_bar.pack(fill=tk.X, pady=4)
        self.status_label = ttk.Label(main_frame, text="就绪 - 请选择版本和目录后点击开始下载",
                                      font=("Microsoft YaHei UI", 9))
        self.status_label.pack(fill=tk.X)

        # 日志
        log_frame = ttk.LabelFrame(main_frame, text="下载日志", padding=4)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=4)
        self.log_text = scrolledtext.ScrolledText(log_frame, height=10,
                                                   font=("Consolas", 9), wrap=tk.WORD,
                                                   state=tk.DISABLED)
        self.log_text.pack(fill=tk.BOTH, expand=True)

        # 提示
        tip_frame = ttk.Frame(main_frame)
        tip_frame.pack(fill=tk.X, pady=(4, 0))
        ttk.Label(tip_frame,
                  text="提示: 下载完成后，打开 PCL2 / HMCL 启动器 → 设置 → 游戏目录 → 选择本程序设置的目录",
                  font=("Microsoft YaHei UI", 8), foreground="gray").pack(side=tk.LEFT)

    def _get_default_minecraft_dir(self):
        appdata = os.environ.get("APPDATA", "")
        if appdata:
            return Path(appdata) / ".minecraft"
        return Path.home() / ".minecraft"

    def _browse_dir(self):
        d = filedialog.askdirectory(title="选择 .minecraft 目录")
        if d:
            self.dir_var.set(d)

    def _version_sort_key(self, vid):
        """
        版本排序 key：将版本号拆分为可比较的元组。
        数字部分转为 (0, int_val)，字符串部分转为 (1, str_val)，
        确保数字始终排在字符串前，避免 Python3 的混合类型比较错误。
        """
        parts = re.split(r'[.\-_]', vid)
        result = []
        for p in parts:
            try:
                result.append((0, int(p)))
            except ValueError:
                result.append((1, p.lower()))
        return result

    def _get_major_version(self, vid):
        """提取大版本号，如 1.21.4 -> 1.21, 1.20.6 -> 1.20, 1.19.4 -> 1.19"""
        parts = vid.split(".")
        if len(parts) >= 2:
            try:
                major = f"{parts[0]}.{parts[1]}"
                return major
            except Exception:
                pass
        return vid

    def _version_gte_1_12(self, vid):
        """
        判断版本是否 >= 1.12。
        处理标准版本号（如 1.12.2）和快照版本号（如 23w14a、1.12.2-pre1）。
        """
        try:
            # 处理带后缀的版本号（如 1.12.2-pre1 -> 1.12.2）
            clean = re.split(r'[-_]', vid)[0]
            parts = clean.split(".")
            if len(parts) >= 2:
                major = int(parts[0])
                minor = int(parts[1])
                if major > 1:
                    return True
                if major == 1 and minor >= 12:
                    return True
        except Exception:
            pass
        return False

    def _load_versions_async(self):
        self.version_tree_widget.delete(*self.version_tree_widget.get_children())
        self._log("[INFO] 正在从 BMCLAPI 加载全量版本列表...")

        def load():
            try:
                # 尝试多源获取 manifest
                manifest = None
                for url in [
                    "https://bmclapi2.bangbang93.com/mc/game/version_manifest_v2.json",
                    "https://bmclapi2.bangbang93.com/mc/game/version_manifest.json",
                    "https://download.mcbbs.net/mc/game/version_manifest_v2.json",
                    "https://launchermeta.mojang.com/mc/game/version_manifest_v2.json",
                    "https://launchermeta.mojang.com/mc/game/version_manifest.json",
                ]:
                    try:
                        with ReusableHTTP().open(url, timeout=15) as resp:
                            manifest = json.loads(resp.read())
                        break
                    except Exception:
                        continue

                if not manifest:
                    raise Exception("无法从任何源获取版本列表")

                versions = []
                ver_details = {}
                for v in manifest.get("versions", []):
                    vid = v["id"]
                    # 过滤：只保留 1.12 及以上版本
                    if not self._version_gte_1_12(vid):
                        continue
                    # 过滤掉特殊版本（如 frewi, coffee 等非常规名称）
                    vtype = v.get("type", "")
                    if vtype not in ("release", "snapshot", "old_alpha", "old_beta"):
                        continue
                    versions.append(v)
                    ver_details[vid] = v

                # 按大版本分组
                tree = {}
                for v in versions:
                    vid = v["id"]
                    major = self._get_major_version(vid)
                    if major not in tree:
                        tree[major] = []
                    tree[major].append(v)

                # 每个大版本内按版本号降序
                for major in tree:
                    tree[major].sort(key=lambda x: self._version_sort_key(x["id"]), reverse=True)

                # 大版本按降序排列
                def major_sort_key(major):
                    parts = major.split(".")
                    try:
                        return (int(parts[0]), int(parts[1]))
                    except Exception:
                        return (0, 0)

                sorted_majors = sorted(tree.keys(), key=major_sort_key, reverse=True)

                self.root.after(0, lambda: self._update_version_tree(tree, sorted_majors, ver_details))
            except Exception as e:
                self.root.after(0, lambda: self._log(f"[ERROR] 加载版本失败: {e}"))

        threading.Thread(target=load, daemon=True).start()

    def _update_version_tree(self, tree, sorted_majors, ver_details):
        """更新树形版本列表"""
        self.version_details = ver_details
        self.version_tree = {}

        for major in sorted_majors:
            versions = tree[major]
            # 大版本节点
            release_count = sum(1 for v in versions if v.get("type") == "release")
            snapshot_count = sum(1 for v in versions if v.get("type") == "snapshot")
            label = f"{major}  (正式版×{release_count}, 快照×{snapshot_count})"
            parent = self.version_tree_widget.insert("", tk.END, text=label, open=False)

            for v in versions:
                vid = v["id"]
                vtype = v.get("type", "")
                if vtype == "release":
                    tag = "正式版"
                elif vtype == "snapshot":
                    tag = "快照"
                elif vtype == "old_alpha":
                    tag = "经典Alpha"
                elif vtype == "old_beta":
                    tag = "经典Beta"
                else:
                    tag = vtype
                display = f"{vid}  [{tag}]"
                self.version_tree_widget.insert(parent, tk.END, text=display, values=(vid,))
                self.version_tree[vid] = v

        total = sum(len(tree[m]) for m in sorted_majors)
        self._log(f"[INFO] 加载完成: {len(sorted_majors)} 个大版本, 共 {total} 个版本 (1.12 ~ 最新)")

        # 默认展开最新的大版本
        children = self.version_tree_widget.get_children()
        if children:
            first = children[0]
            self.version_tree_widget.item(first, open=True)

    def _on_tree_select(self, event):
        selection = self.version_tree_widget.selection()
        if not selection:
            return
        item = selection[0]
        values = self.version_tree_widget.item(item, "values")
        if values:
            vid = values[0]
            v = self.version_details.get(vid, {})
            vtype = v.get("type", "unknown")
            release_time = v.get("releaseTime", "N/A")
            self.ver_info_label.config(text=f"版本: {vid}\n类型: {vtype}\n发布时间: {release_time[:10]}")
            self.selected_version = vid
        else:
            # 点击了大版本节点，显示信息
            text = self.version_tree_widget.item(item, "text")
            self.ver_info_label.config(text=f"{text}\n\n点击下方版本进行选择")

    def _start_download(self):
        if not hasattr(self, "selected_version") or not self.selected_version:
            messagebox.showwarning("提示", "请先选择要下载的版本！")
            return

        version_id = self.selected_version
        target_dir = self.dir_var.get().strip()
        mirror_name = self.mirror_var.get()

        if not target_dir:
            messagebox.showwarning("提示", "请设置游戏目录！")
            return

        Path(target_dir).mkdir(parents=True, exist_ok=True)
        self.download_btn.config(state=tk.DISABLED)
        self.cancel_btn.config(state=tk.NORMAL)
        self.progress_var.set(0)

        self._log("\n" + "=" * 55)
        self._log(f"[INFO] 准备下载: {version_id}")
        self.status_label.config(text="正在启动下载...")
        self.root.update_idletasks()

        num_threads = max(1, min(MAX_THREADS, self.thread_var.get()))
        self.worker = DownloadWorker(
            mirror_name=mirror_name,
            target_dir=target_dir,
            version_id=version_id,
            progress_callback=self._on_progress,
            log_callback=self._log,
            done_callback=self._on_download_done,
            num_threads=num_threads,
        )
        self.worker.start()
        self._log(f"[INFO] 下载线程已启动 ({num_threads} 线程, 最大 {MAX_SEGMENTS} 分段)")

    def _cancel_download(self):
        if self.worker:
            self.worker.cancel()
        self.cancel_btn.config(state=tk.DISABLED)

    def _on_progress(self, value, text):
        self.root.after(0, lambda: self.progress_var.set(value))
        if text:
            self.root.after(0, lambda: self.status_label.config(text=text))

    def _on_download_done(self, success):
        self.root.after(0, lambda: self.download_btn.config(state=tk.NORMAL))
        self.root.after(0, lambda: self.cancel_btn.config(state=tk.DISABLED))
        if success:
            self.root.after(0, lambda: self.status_label.config(
                text="下载完成！PCL2 / HMCL 启动器可直接使用此目录"))
            self.root.after(0, lambda: messagebox.showinfo(
                "完成", f"Minecraft {getattr(self, 'selected_version', '')} 下载完成！\n\n"
                         f"目录: {self.dir_var.get()}\n\n"
                         f"打开 PCL2 / HMCL 启动器，设置游戏目录到此路径即可游戏。"))
        else:
            self.root.after(0, lambda: self.status_label.config(text="下载失败或部分失败"))

    def _log(self, msg):
        def _do():
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        self.root.after(0, _do)


def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        available_themes = style.theme_names()
        if "vista" in available_themes:
            style.theme_use("vista")
        elif "clam" in available_themes:
            style.theme_use("clam")
    except Exception:
        pass
    app = MCUniDownloaderApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
