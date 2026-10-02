#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
登录验证脚本 —— 携带账号密码登录，并判断登录是否成功。

【两种用法】
  1. 单条检测：命令行直接给 --url / -u / -p
  2. 批量检测：--file 指向一个文本文件，每行一条 "url:username:password"

【判定规则】（按优先级从高到低）
  0. 页面要求验证码/二次验证（验证码/滑块/短信/recaptcha 等特征词）→ 验证码
     （**最高优先级**，脚本无法自动完成，转入「需人工复核」文档单独输出，
      不进成功清单、也不判失败）
  1. 接口明确返回认证失败（JSON 非 0 业务码 / success=false / HTTP 401·403）→ 失败
  2. 登录失败特征词存在（密码错误 / 认证失败 / login failed …）→ 失败
  3. 跳回登录页 / 跳到 CAS 统一认证页 → 失败
  4. 有强会话凭据（auth_token / access_token / login_token / jwt 等，凭据本身就是证据，
     可叠加跳转证据）→ 成功
  5. 登录表单消失 + 出现登录后元素（退出登录/我的账户/dashboard …）→ 成功
     （必须对照匿名基线：匿名页有表单且现在没了、且该元素匿名页没有）
  6. 实质跳转到登录后页面 → 成功
  7. 兜底：登录前后页面内容相似度 ≤80%（变化明显）→ 成功；
     相似度 >80%（内容未变）→ 异常（不武断判失败，避免漏掉正确密码，留待人工复核）
其余 → 异常（无明确证据，保守不判成功）。

  验证码条目单独写文档：<根域名>_captcha.txt，与成功文档 <根域名>.txt 分开，
  供人工复核，绝不与成功账密混在一起。

  * 「强会话凭据」≠ 通用会话 Cookie。ASPSESSIONIDxxxx / ASP.NET_SessionId / JSESSIONID /
    PHPSESSID / sessionid / sid 这类通用会话标识**匿名访问就会下发**，登录失败时也下发，
    一律不作为成功证据（只有 auth_token / access_token / login_token / jwt 等才算）。

三条防误判的核心约束（都踩过坑，别回退）：
  * JS 跳转（window.location / document.location / location.replace）不单独作为成功
    证据。站点首页常自带 document.location='.../index.jsp' 这类静态跳转，匿名访问
    就能拿到；脚本会用「匿名基线」比对，匿名时也存在的跳转一律不算登录证据。
    无会话凭据时，即使目标含 index/home/main 等词也不判成功。
  * 「跳转」只认实质跳转：http→https、加/去 www、去默认端口这类 URL 规范化不算；
    根路径 "/" 也不算登录后页面（匿名访问就能到首页）。
  * "表单消失 + 出现登录后元素"同样要过匿名基线。门户站/静态首页压根没有登录框
    （"消失"天然成立），且首页静态链接里常带 /dashboard 这类词，匿名访问就能看到。
    因此要求：匿名页确有表单、且该元素匿名页没有；拿不到基线则不启用这条规则。

成功不再靠"页面上有欢迎语"这类单薄字眼；要看页面文字请用
--check-contains（验证页文字）或 --success-contains（登录响应文字，命中即成功、
未命中不判失败）显式指定。
密码为空的条目会直接跳过（空密码登录成功几乎必然是误判）。
退出码：单条 0=成功 1=失败 2=请求异常；批量 0=全部成功 1=存在失败/异常 2=参数错误。

【卡死防护】
  * --hard-timeout：单条任务的硬上限（超过就丢弃，不再等待），默认 timeout*4+5 秒
  * --max-time：整轮批量检测的总时限，到点立即结束并输出已完成的结果
  * --max-bytes：单个响应体最多读多少字节（防止慢速流/超大页面无限读取）
  * --dns-timeout：DNS 解析超时（requests 的 timeout 不覆盖 DNS，这是卡死主因之一）

示例：
  python login_request.py --url https://example.com/login -u admin -p 123456
  python login_request.py --url https://example.com/login -u admin -p 123456 --check-contains "我的订单"
  python login_request.py --file accounts.txt --timeout 3 --concurrency 20
  python login_request.py --file accounts.txt --timeout 3 --concurrency 32 --hard-timeout 12 --max-time 1800
"""

import argparse
import difflib
import getpass
import json
import os
import re
import socket
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as FuturesTimeoutError
from urllib.parse import urlencode, urlparse

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

try:
    import requests  # type: ignore

    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

# ---------- 特征词 ----------
# 验证码特征词：出现在响应里即归入「需人工复核」类别，单独输出、不进成功清单。
# 注意：验证码是**最高优先级**——一旦页面要求验证码/滑块/短信/二次验证，脚本无法自动
# 完成，无论后续是否出现"登录后元素"或"会话凭据"，都不能判成功（那些极可能是验证码
# 页面自带的干扰元素），一律转入人工复核文档。
CAPTCHA_WORDS = [
    "验证码", "验证码输入", "请输入验证码", "输入验证码", "图形验证码", "图片验证码",
    "短信验证码", "手机验证码", "动态验证码", "滑动验证", "滑块验证", "拖动验证",
    "拖动滑块", "请完成验证", "完成验证", "人机验证", "安全验证", "校验码",
    "captcha", "captchaimage", "verifycode", "verification code", "verification_code",
    "image code", "imgcode", "check code", "checkcode", "slide verify", "slider",
    "security code", "securitycode", "recaptcha", "geetest", "hcaptcha",
]

# 失败特征词：出现在响应里即判失败。
FAIL_WORDS = [
    "密码错误", "账号或密码错误", "用户名或密码错误", "账号不存在", "用户不存在", "账号已锁定",
    "验证码错误", "验证码不正确", "验证码失效", "登录失败", "未授权", "请先登录", "认证失败",
    "登录已过期", "会话已过期", "凭据无效", "令牌无效", "无权访问", "尚未登录",
    "invalid password", "invalid credentials", "bad credentials", "incorrect password",
    "login failed", "login error", "unauthorized", "authentication failed", "access denied",
    "user not found", "wrong password", "invalid username", "invalid token", "token expired",
]

# 登录后元素：只有登录成功、进入个人中心/工作台后才可能出现的界面元素。
# 用途：配合"登录表单消失"一起判断——表单没了 + 出现这些元素 → 成功。
POST_LOGIN_ELEMENTS = [
    "退出登录", "退出系统", "注销登录", "注销", "我的订单", "我的账户", "账户设置",
    "个人中心", "用户中心", "我的工作台", "控制台", "修改密码", "安全退出",
    "sign out", "log out", "logout", "signout", "my account", "my profile",
    "dashboard", "workspace", "my dashboard",
]

# ---------- Cookie 分级 ----------
# 强凭据：仅当 Cookie 名整体以这些词为核心时才算。注意 sessionid/sid 不能作为强凭据——
# ASP 的 ASPSESSIONIDxxxx、JSP 的 JSESSIONID、PHP 的 PHPSESSID 都是「匿名访问就下发」的
# 通用会话标识，登录失败时也会下发，绝不能当作登录成功证据。
STRONG_COOKIE_PAT = re.compile(r"^(?:.*_)?(?:auth_?token|access_?token|refresh_?token|jwt|"
                               r"login_?token|sid$|session_?token|token$)", re.I)
# 通用会话 Cookie：用「前缀/精确」匹配，优先级高于强凭据正则。
# ASPSESSIONIDxxxx / ASP.NET_SessionId / JSESSIONID / PHPSESSID 等都归这里。
WEAK_COOKIE_PAT = re.compile(
    r"^(?:aspsessionid|asp\.net_sessionid|jsessionid|phpsessid|"
    r"laravel_session|ci_session|ci_session_id|session$|_session$|"
    r"csrftoken|csrf_?token|xsrf-?token|sessid|sid$)", re.I)
COOKIE_ATTRS = {"path", "domain", "expires", "max-age", "secure", "httponly", "samesite", "priority", "partitioned"}

# ---------- 页面 / URL 特征 ----------
LOGIN_PAGE_PAT = re.compile(r'<form[^>]+(login|signin)|name=["\']password["\']|type=["\']password["\']', re.I)
LOGIN_URL_PAT = re.compile(r"/(login|signin|sign_in|sign-in|passport|session/new)(/|$|\?)", re.I)
# 注意：不含 ^/$ —— 根路径 "/" 对匿名访问也能直接到达，不能作为"登录后页面"证据。
HOME_URL_PAT = re.compile(r"home|index|dashboard|console|profile|account|workbench|main|portal|user", re.I)
JS_REDIRECT_PAT = re.compile(
    r"""(?:window|top|self|parent|document)\s*\.\s*location(?:\.href)?\s*=\s*["']([^"']{2,500})["']"""
    r"""|location\s*\.\s*replace\s*\(\s*["']([^"']{2,500})["']"""
    r"""|location\s*\.\s*href\s*=\s*["']([^"']{2,500})["']""", re.I)

# 这些 window.xxx() / 语句不是页面跳转，绝不能当作登录后跳转证据
JS_NON_REDIRECT_PAT = re.compile(
    r"""(?:window|top|self|parent|document)\s*\.\s*(?:resizeTo|scrollTo|scroll|moveTo|open|print|focus|blur|close|alert|confirm|setTimeout|setInterval|addEventListener|history\.(?:back|go))\b""",
    re.I)

# CAS / 统一身份认证登录页的跳转目标：跳去这些 = 仍未登录
CAS_LOGIN_PAT = re.compile(r"cas\s*login|caslogin|authserver|sso\s*login|passport", re.I)

# ---------- 自动表单字段 ----------
INPUT_TAG_RE = re.compile(r"(?is)<input\b[^>]*>")
FORM_RE = re.compile(r"(?is)<form\b[^>]*>(.*?)</form>")
TEXTAREA_SELECT_RE = re.compile(r"""(?is)<(textarea|select)\b[^>]*name=["']([^"']+)["']""")
# 这些字段由命令行参数控制，不能从页面里抽取覆盖
FIELD_SKIP_NAMES = {
    "username", "password", "user", "pass", "pwd", "userid", "user_id", "account",
    "captcha", "verifycode", "validatecode", "valicode", "checkcode", "authcode",
    "image_code", "imgcode", "code", "verify", "vcode", "randcode", "randomcode",
    "submit", "reset", "button", "remember", "rememberme", "remember_me", "remember-me",
    "autologin", "auto_login", "chkrememberme",
}
INPUT_SKIP_TYPES = {"password", "submit", "button", "reset", "image", "file", "checkbox", "radio"}
HTML_ENT = {"&quot;": '"', "&#39;": "'", "&apos;": "'", "&lt;": "<", "&gt;": ">", "&nbsp;": " ", "&amp;": "&"}


def out(msg=""):
    """统一输出并立即刷新（重定向到文件时也能看到实时进度）。"""
    print(msg, flush=True)


def _unescape_unicode(text):
    if "\\u" not in text:
        return text
    try:
        return re.sub(r"\\u([0-9a-fA-F]{4})", lambda m: chr(int(m.group(1), 16)), text)
    except Exception:
        return text


def _unescape_html(s):
    for k, v in HTML_ENT.items():
        s = s.replace(k, v)
    return s


def _cookie_names_from_headers(raw):
    names = [m.group(1) for m in re.finditer(r"([A-Za-z0-9_\-\.]+)\s*=", raw or "")]
    return [n for n in names if n.lower() not in COOKIE_ATTRS]


def _classify_cookies(cookies):
    """把 Cookie 分成 (strong, weak)。

    关键顺序：先判定「通用会话 Cookie」——ASPSESSIONIDxxx / JSESSIONID / PHPSESSID 这类
    匿名访问就会下发的标识，必须归 weak，绝不能因名字里碰巧含 sessionid/sid 而进 strong。
    """
    strong, weak = [], []
    for c in cookies:
        name = c.lower()
        if WEAK_COOKIE_PAT.search(name):
            weak.append(c)
        elif STRONG_COOKIE_PAT.search(name):
            strong.append(c)
        else:
            weak.append(c)
    return strong, weak


def _decode(raw, header_enc=None):
    """按 meta/header 声明的字符集解码，失败逐个回退。"""
    encs = []
    m = re.search(rb"(?is)<meta[^>]+charset=[\"']?\s*([A-Za-z0-9_\-]+)", raw[:4096])
    if m:
        encs.append(m.group(1).decode("ascii", "ignore"))
    if header_enc:
        encs.append(header_enc)
    encs += ["utf-8", "gb18030", "latin-1"]
    for e in encs:
        try:
            return raw.decode(e)
        except (UnicodeDecodeError, LookupError):
            continue
    return raw.decode("utf-8", errors="replace")


def _json_evidence(text):
    """解析 JSON 响应里的结构化成功/失败证据，返回 (True/False, 说明) 或 None。"""
    try:
        data = json.loads(text)
    except Exception:
        return None
    if not isinstance(data, dict):
        return None

    for k in ("success", "ok", "succeeded", "isLogin", "is_login", "logged_in", "authenticated"):
        v = data.get(k)
        if isinstance(v, bool):
            return v, f"JSON 字段 {k}={str(v).lower()}"

    for k in ("code", "errcode", "errno", "ret", "error_code", "result_code", "respCode", "status_code"):
        v = data.get(k)
        val = v if isinstance(v, int) and not isinstance(v, bool) else (
            int(v) if isinstance(v, str) and re.fullmatch(r"-?\d+", v.strip()) else None)
        if val is None:
            continue
        if val == 0 or 200 <= val < 300:
            return True, f"JSON 业务码 {k}={val}（0/2xx 视为成功）"
        return False, f"JSON 业务码 {k}={val}（非 0 视为失败码；若贵系统约定不同，请用 --fail-contains 指定）"

    for k in ("status", "result", "state"):
        v = data.get(k)
        if isinstance(v, str):
            low = v.strip().lower()
            if low in ("ok", "success", "succeed", "successful", "pass", "true", "logged_in"):
                return True, f"JSON 字段 {k}={v!r}"
            if low in ("fail", "failed", "error", "false", "invalid", "unauthorized", "denied"):
                return False, f"JSON 字段 {k}={v!r}"

    for k in ("token", "access_token", "id_token", "jwt", "sessionid", "session_id", "sessionId", "ticket"):
        v = data.get(k)
        if isinstance(v, str) and v.strip():
            return True, f"JSON 返回 {k} 凭据"
    for k in ("user", "userInfo", "user_info", "profile", "account"):
        if isinstance(data.get(k), dict) and data.get(k):
            return True, f"JSON 返回 {k} 用户信息"
    return None


# --------------------------------------------------------------------------- #
# DNS 预解析（带超时）—— requests 的 timeout 不覆盖 getaddrinfo，是卡死主因之一
# --------------------------------------------------------------------------- #
_dns_cache = {}
_dns_lock = threading.Lock()
_dns_pool = ThreadPoolExecutor(max_workers=16, thread_name_prefix="dns")


def resolve_host(host, timeout=3.0):
    """解析主机名，超时返回 None。结果做进程内缓存。"""
    if not host:
        return True
    if re.fullmatch(r"[\d.]+", host):  # 纯 IP，无需解析
        return True
    with _dns_lock:
        if host in _dns_cache:
            return _dns_cache[host]
    try:
        fut = _dns_pool.submit(socket.getaddrinfo, host, None, socket.AF_UNSPEC, socket.SOCK_STREAM)
        fut.result(timeout=timeout)
        ok = True
    except Exception:
        ok = None  # None = 解析超时/失败
    with _dns_lock:
        _dns_cache[host] = ok
    return ok


def dns_precheck(url, timeout=3.0):
    """返回 (是否可解析, 主机名)。"""
    host = urlparse(url).hostname or ""
    return resolve_host(host, timeout), host


# --------------------------------------------------------------------------- #
# 会话（跨请求保持 Cookie）
# --------------------------------------------------------------------------- #
class HttpSession:
    """优先 requests.Session，回退 urllib + cookiejar；两者都能跨请求保持 Cookie。"""

    def __init__(self, proxy=None, env_proxy=True):
        self.engine = "requests" if HAS_REQUESTS else "urllib"
        if HAS_REQUESTS:
            self._s = requests.Session()
            self._s.trust_env = env_proxy
            if proxy:
                self._s.proxies = {"http": proxy, "https": proxy}
        else:
            import http.cookiejar
            import urllib.request

            self._cj = http.cookiejar.CookieJar()
            handlers = [urllib.request.HTTPCookieProcessor(self._cj)]
            if proxy:
                handlers.append(urllib.request.ProxyHandler({"http": proxy, "https": proxy}))
            elif not env_proxy:
                handlers.append(urllib.request.ProxyHandler({}))  # 空映射 = 不读环境变量里的代理
            self._opener = urllib.request.build_opener(*handlers)

    def close(self):
        if HAS_REQUESTS:
            try:
                self._s.close()
            except Exception:
                pass

    def request(self, method, url, headers=None, data=None, json_body=None, timeout=15,
                max_bytes=1048576, read_timeout=None):
        """返回 dict(status, headers, text, final_url, cookies, truncated)。

        timeout 只作用于单次 socket 操作；read_timeout 是"读完整响应体"的总预算——
        服务器每几秒喂一小块时单次 recv 永不超时，只有总预算能挡住这种慢速流。
        """
        headers = dict(headers or {})
        headers.setdefault("User-Agent", UA)
        headers.setdefault("Accept", "*/*")
        if read_timeout is None:
            read_timeout = max(timeout * 3, 5)

        if HAS_REQUESTS:
            resp = self._s.request(method, url, headers=headers, data=data, json=json_body,
                                   timeout=timeout, allow_redirects=True, stream=True)
            cookies = list(resp.cookies.keys()) or _cookie_names_from_headers(resp.headers.get("Set-Cookie", ""))
            status, final_url, hdrs = resp.status_code, resp.url, dict(resp.headers)
            # 逐块读取：max_bytes 防超大页面，read_timeout 防慢速流
            chunks, total, truncated = [], 0, False
            deadline = time.monotonic() + read_timeout
            try:
                for chunk in resp.iter_content(chunk_size=32768):
                    if not chunk:
                        continue
                    chunks.append(chunk)
                    total += len(chunk)
                    if total >= max_bytes or time.monotonic() > deadline:
                        truncated = True
                        break
            except Exception:
                pass
            finally:
                try:
                    resp.close()
                except Exception:
                    pass
            text = _decode(b"".join(chunks), resp.encoding)
        else:
            import urllib.request
            import urllib.error

            if json_body is not None:
                body = json.dumps(json_body, ensure_ascii=False).encode("utf-8")
                headers["Content-Type"] = "application/json"
            elif data is not None:
                body = urlencode(data).encode("utf-8")
                headers["Content-Type"] = "application/x-www-form-urlencoded"
            else:
                body = None

            req = urllib.request.Request(url, data=body, headers=headers, method=method.upper())
            try:
                resp = self._opener.open(req, timeout=timeout)
            except urllib.error.HTTPError as e:  # 4xx/5xx 也有响应体，需照常读取
                resp = e
            with resp:
                # 分块读 + 时间预算，避免 read(n) 一次性阻塞在慢速流上
                chunks, total, truncated = [], 0, False
                deadline = time.monotonic() + read_timeout
                while True:
                    if total >= max_bytes or time.monotonic() >= deadline:
                        truncated = True
                        break
                    block = resp.read(min(65536, max_bytes - total))
                    if not block:
                        break
                    chunks.append(block)
                    total += len(block)
                raw = b"".join(chunks)
                cookies = _cookie_names_from_headers("; ".join(resp.headers.get_all("Set-Cookie") or []))
            status, final_url, hdrs = resp.code, resp.geturl(), dict(resp.headers)
            text = _decode(raw, resp.headers.get_content_charset())

        return {"status": status, "headers": hdrs, "text": _unescape_unicode(text),
                "final_url": final_url, "cookies": cookies, "truncated": truncated}

    def post_login(self, url, payload, as_json=False, timeout=15, max_bytes=1048576, read_timeout=None):
        return self.request("POST", url, data=None if as_json else payload,
                            json_body=payload if as_json else None,
                            timeout=timeout, max_bytes=max_bytes, read_timeout=read_timeout)


# --------------------------------------------------------------------------- #
# 自动抽取登录页表单字段
# --------------------------------------------------------------------------- #
def _attr(tag, name):
    m = re.search(r"""(?is)\b%s\s*=\s*(?:["']([^"']*)["']|([^\s"'>=]+))""" % re.escape(name), tag)
    if not m:
        return None
    return m.group(1) if m.group(1) is not None else m.group(2)


def extract_form_fields(html):
    """从登录页 HTML 抽取需要一并提交的隐藏/预设字段（CAS 的 lt/execution/_eventId、CSRF token 等）。

    只取"含密码框的那个 form"里的字段，避免把搜索框、验证码框等无关字段带进去。
    """
    if not html:
        return {}
    forms = FORM_RE.findall(html)
    scope = html
    for f in forms:
        if re.search(r"""type\s*=\s*["']?password""", f, re.I):
            scope = f
            break

    fields = {}
    for tag in INPUT_TAG_RE.findall(scope):
        name = _attr(tag, "name")
        if not name:
            continue
        if name.lower() in FIELD_SKIP_NAMES:
            continue
        typ = (_attr(tag, "type") or "text").strip().lower()
        if typ in INPUT_SKIP_TYPES:
            continue
        value = _unescape_html(_attr(tag, "value") or "")
        # 未勾选的 checkbox 不提交
        if typ == "checkbox" and not re.search(r"(?i)\bchecked\b", tag):
            continue
        fields[name] = value

    for tag, name in TEXTAREA_SELECT_RE.findall(scope):
        if name.lower() not in FIELD_SKIP_NAMES:
            fields.setdefault(name, "")

    # CAS 常见：页面上没有 _eventId 时需要补上
    if any(k in fields for k in ("lt", "execution")) and "_eventId" not in fields:
        fields["_eventId"] = "submit"
    return fields


# --------------------------------------------------------------------------- #
# 判定
# --------------------------------------------------------------------------- #
def judge_login_response(r, login_url, success_contains=None, fail_contains=None, anon=None):
    """分析登录接口响应，返回 (verdict, reason, info)，verdict ∈ {success, fail, unknown, captcha}。

    判定优先级（从高到低）：
      0. 页面要求验证码/二次验证（验证码/滑块/短信/recaptcha 等特征词）→ captcha
         （**最高优先级**，需人工复核，单独输出、不进成功清单）
      1. 显式 --fail-contains 命中 → 失败
      2. 接口明确返回认证失败（JSON 非 0 业务码 / success=false / HTTP 401·403·其他 4xx·5xx）
      3. 登录失败特征词（密码错误 / 认证失败 / login failed …）
      4. 显式 --success-contains 命中 → 成功；**未命中不判定失败，继续按后续规则判断**
      5. 被重定向回登录页 → 失败
      6. 脚本跳转到 CAS / 统一身份认证登录页（caslogin/authserver/passport）→ 失败
      7. 有强会话凭据且「实质跳转」到登录后页面 → 成功
      8. 有强会话凭据且脚本跳转（非静态）→ 成功
      9. 有强会话凭据（凭据本身就是证据，不依赖跳转）→ 成功
     10. 登录表单消失 + 出现登录后元素 → 成功（**必须能拿到匿名基线**：
          匿名页有表单且现在没了、且该元素匿名页没有，才算有效；拿不到基线则不启用）
     11. 响应仍是登录表单 → 失败
     12. 实质跳转到登录后页面（且匿名访问不会落到同一地址）→ 成功
     13. 无凭据的 JS 跳转 → 目标含 login/error/fail/cas 判失败，其余一律 unknown
     14. 仅通用会话 Cookie（ASPSESSIONIDxxxx/JSESSIONID/PHPSESSID 等）→ unknown
      其余 → unknown。

    「强会话凭据」仅指 auth_token / access_token / login_token / jwt 这类「登录后才签发」
    的 Cookie 或 JSON 字段；而 ASPSESSIONIDxxxx / ASP.NET_SessionId / JSESSIONID / PHPSESSID
    / sessionid / sid 等通用会话标识**匿名访问就会下发**，登录失败时也会下发，绝不作为
    成功证据（见 STRONG_COOKIE_PAT / WEAK_COOKIE_PAT）。

    三条防误判的核心约束（踩过坑，别回退）：
      A. JS 跳转不单独作为成功证据。站点首页常自带
         document.location='.../index.jsp' 这类静态跳转，匿名访问就有；且 index/home/
         main 这类名字太常见，靠跳转目标名字猜必然误判。只有伴随会话凭据才算证据。
      B. 「跳转」只认实质跳转。http→https、加/去 www、去默认端口这类 URL 规范化
         不算；根路径 "/" 也不算登录后页面（匿名就能到首页）；匿名访问也会落到
         同一地址的重定向（门户站统一 302 到 /index.jsp）同样不算。
      C. 「强会话凭据」必须是**本次登录响应中新出现**的——匿名基线里同名 Cookie 已存在，
         或匿名访问就下发了同名 JSON 凭据，都不能作为成功证据（避免靠 Cookie 名字
         猜而误报；很多站点非登录接口也会返回 token 字段）。

    anon：匿名基线响应（登录前 GET 的结果）。用于识别「站点固有静态跳转」——
    若匿名页面里存在相同的 JS 跳转目标，则该跳转与登录无关，不作为成功证据。

    info 里会带上 has_credential / has_form / post_login_hit / js_target / js_is_static
    等证据，供 judge_protected_page 做二次仲裁。
    """
    text, status = r["text"], r["status"]

    # 0. 验证码检测（最高优先级）：页面出现验证码/滑块/短信/二次验证特征词，说明该站点
    #    需要人工交互才能登录，脚本无法自动完成。此时无论后续是否出现"登录后元素"或
    #    "会话凭据"都不能判成功——那些极可能是验证码页面自带的干扰元素。归入
    #    verdict="captcha"，由调用方单独写入「需人工复核」文档，不进成功清单。
    low_text = text.lower()
    for w in CAPTCHA_WORDS:
        if w.lower() in low_text:
            return "captcha", f"页面要求验证码/二次验证（命中特征词 {w!r}），需人工复核", {}

    # 显式指定的失败关键字
    if fail_contains and fail_contains in text:
        return "fail", f"命中失败关键字 {fail_contains!r}", {}

    # 1. 接口明确返回认证失败（业务码 / 布尔 success / HTTP 状态）
    ev = _json_evidence(text)
    if ev is not None and ev[0] is False:
        return "fail", ev[1], {}
    if status in (401, 403):
        return "fail", f"HTTP 状态码 {status}（未授权/禁止访问）", {}
    if status >= 400:
        return "fail", f"HTTP 状态码 {status}", {}

    # 2. 登录失败特征词
    for w in FAIL_WORDS:
        if w.lower() in text.lower():
            return "fail", f"响应含失败特征词 {w!r}", {}

    # 3. 显式 --success-contains：命中即成功；未命中不判定为失败，继续按后续规则判断
    if success_contains and success_contains in text:
        return "success", f"命中成功关键字 {success_contains!r}", {}

    # 收集行为证据
    # 只认「实质跳转」——http→https、加/去 www 这类 URL 规范化不算登录跳转
    redirected = _is_substantive_redirect(login_url, r["final_url"])
    redirected_to_login = redirected and LOGIN_URL_PAT.search(urlparse(r["final_url"]).path)
    redirected_to_home = redirected and HOME_URL_PAT.search(urlparse(r["final_url"]).path)
    # 排除「站点固有重定向」：匿名访问最终也落到同一地址，说明这重定向与登录无关
    # （如门户站统一 302 到 /index.jsp）。与静态 JS 跳转的处理保持一致。
    if redirected_to_home and anon is not None:
        try:
            if _normalized_key(anon.get("final_url") or "") == _normalized_key(r["final_url"]):
                redirected_to_home = False
        except Exception:
            pass
    # 收集强/弱 Cookie，以及 JSON 业务凭据
    strong, weak = _classify_cookies(r["cookies"])
    # 关键：匿名基线里已有的同名 Cookie，不能作为「本次登录新签发」的凭据。
    # 很多站点匿名访问就下发 token/auth 等命名的 Cookie（或非登录接口也返回 token 字段），
    # 纯靠名字判断必然误报。只有匿名基线里不存在、登录后才出现的强凭据才算数。
    anon_cookies = set((anon or {}).get("cookies") or [])
    strong = [c for c in strong if c not in anon_cookies]

    has_credential = bool(strong) or (ev is not None and ev[0] is True)
    has_form = bool(LOGIN_PAGE_PAT.search(text))
    post_login_hit = next((w for w in POST_LOGIN_ELEMENTS if w.lower() in text.lower()), None)

    # 关键：规则「表单消失 + 出现登录后元素」必须对照匿名基线才成立。
    #   ① 匿名页本来就没表单 → 谈不上"表单消失"（很多门户站压根没有登录框）；
    #   ② "登录后元素"匿名页里也有 → 那是站点固有文案（如首页静态链接里带 /dashboard），
    #      与登录无关，绝不能当作登录成功的证据。
    anon_text = (anon or {}).get("text") or ""
    anon_has_form = bool(anon_text) and bool(LOGIN_PAGE_PAT.search(anon_text))
    if post_login_hit and anon_text and post_login_hit.lower() in anon_text.lower():
        post_login_hit = None  # 站点固有文案，不算证据
    js_res = _js_redirect_target(text)
    js_target = js_res[0] if js_res else None
    js_is_cas = js_res[1] if js_res else False

    # 关键：判断这段 JS 跳转是不是"站点固有的静态跳转"——
    # 很多站点首页/门户页自带一段 document.location='...index.jsp'，匿名访问就能拿到。
    # 这类跳转跟登录毫无关系，绝不能当作登录成功证据。
    js_is_static = False
    if js_target and anon is not None:
        try:
            anon_js = _js_redirect_target(anon.get("text") or "")
            if anon_js and anon_js[0] == js_target:
                js_is_static = True
        except Exception:
            pass

    info = {
        "strong": strong, "weak": weak, "redirected": redirected,
        "has_credential": has_credential, "has_form": has_form,
        "anon_has_form": anon_has_form, "has_anon_baseline": bool(anon_text),
        "post_login_hit": post_login_hit, "js_target": js_target,
        "js_is_static": js_is_static,
    }

    # 被重定向回登录页 = 明确失败
    if redirected_to_login:
        return "fail", f"被重定向到登录页 {r['final_url']}，鉴权未通过", info

    # 脚本跳转到 CAS / 统一身份认证登录页 = 仍未登录
    if js_is_cas and not has_credential:
        return "fail", f"脚本跳转到认证登录页 {js_target}，鉴权未通过", info

    # 7. 有 token/session 且「实质跳转」到登录后页面 → 成功
    if has_credential and redirected_to_home:
        return "success", f"下发会话凭据且跳转到登录后页面 {r['final_url']}", info
    # 8. 有 token/session 且脚本跳转（排除站点固有静态跳转）→ 成功
    #    注：若 js_is_static（匿名访问也有同样跳转），此处不判成功，
    #    但凭据本身已是证据，会落到规则 9 判成功。
    if has_credential and js_target and not js_is_static \
            and not LOGIN_URL_PAT.search(js_target.lower()) and not js_is_cas:
        return "success", f"下发会话凭据且脚本跳转到 {js_target}", info

    # 9. 有 token/session（凭据本身就是证据，不依赖跳转）
    if has_credential:
        cred_desc = ", ".join(strong) if strong else "业务码/JSON 返回凭据"
        return "success", f"服务端下发会话凭据：{cred_desc}", info

    # 10. 登录表单消失 + 出现登录后元素 → 成功
    #     必须同时满足两个基线条件，否则极易误判：
    #       · 匿名页确实有表单（"消失"才成立；本来就没表单的门户站不算）
    #       · 该元素匿名页没有（否则是站点固有文案，如首页静态链接里的 /dashboard）
    #     拿不到匿名基线时一律不启用本规则，保守判 unknown。
    if anon_has_form and not has_form and post_login_hit:
        return "success", f"登录表单消失且出现登录后元素 {post_login_hit!r}", info
    if not has_form and post_login_hit and not anon_text:
        return "unknown", (f"响应无登录表单且出现 {post_login_hit!r}，但缺少匿名基线、"
                           f"无法确认该元素是登录后新增的，不足以判定成功"), info

    # 11. 响应仍是登录表单 → 登录未生效
    if has_form and status < 300:
        return "fail", "响应内容仍是登录表单，未通过鉴权", info

    # 12. 实质跳转到登录后页面（无凭据，但服务端确实重定向了）
    if redirected_to_home:
        return "success", f"已跳转到登录后页面 {r['final_url']}", info

    # 13. 无凭据的 JS 跳转：一律不作为成功证据
    #     站点首页常自带 document.location='.../index.jsp' 这类静态跳转，匿名访问就有；
    #     没有会话凭据时无法区分"登录跳转"和"站点固有跳转"，只能判证据不足。
    if js_target:
        low = js_target.lower()
        if LOGIN_URL_PAT.search(low) or "error" in low or "fail" in low or js_is_cas:
            return "fail", f"脚本跳转到 {js_target or '登录页'}，鉴权未通过", info
        if js_is_static:
            return "unknown", (f"响应含脚本跳转到 {js_target}，但匿名访问时该跳转同样存在，"
                               f"属站点固有跳转、与登录无关；且无会话凭据，不足以判定成功"), info
        return "unknown", (f"响应含脚本跳转到 {js_target}，但无会话凭据、无法确认是登录后页面，"
                           f"不足以判定成功"), info

    # 14. 仅通用 Cookie（JSESSIONID/PHPSESSID 等）：登录失败时也会下发，不算证据
    if weak:
        return "unknown", (f"仅收到通用 Cookie（{', '.join(weak)}），这类 Cookie 登录失败时也会下发，"
                           f"不足以证明成功；HTTP {status} 同样不能作为成功依据"), info
    return "unknown", f"HTTP {status}，但未找到任何成功证据（无业务码、无会话 Cookie、无跳转）", info


def _js_redirect_target(text):
    """从响应中提取真正的「页面跳转」目标，返回 (target, is_cas_login)。

    刻意排除两类假信号：
    1. window.resizeTo / scrollTo / open / alert 等非跳转语句；
    2. 空目标 / "#" / "javascript:..." 这类占位赋值。

    is_cas_login：跳转目标是 CAS / 统一身份认证登录页（说明仍未登录）。
    """
    # 先剔除明显的非跳转语句，避免它们的位置干扰后续 search
    m = JS_REDIRECT_PAT.search(text)
    if not m:
        return None
    target = (m.group(1) or m.group(2) or m.group(3) or "").strip()
    low = target.lower()
    if not target or target in ("#", "javascript:;", "javascript:void(0)"):
        return None
    if low.startswith("javascript:"):
        return None
    return target, bool(CAS_LOGIN_PAT.search(low))


def _normalized_key(url):
    """把 URL 归一化到「协议无关 + 去 www + 去默认端口 + 去尾斜杠」的 key。

    用于判断两次访问是否指向"实质相同的页面"——http→https、加/去 www、
    加/去默认端口这类 URL 规范化跳转，不应被视为"登录导致的跳转"。
    """
    try:
        p = urlparse(url)
        host = (p.hostname or "").lower()
        if host.startswith("www."):
            host = host[4:]
        # 去掉默认端口
        port = p.port
        if (p.scheme == "http" and port == 80) or (p.scheme == "https" and port == 443):
            port = None
        path = (p.path or "/").rstrip("/") or "/"
        return f"{host}:{port or ''}/{path}"
    except Exception:
        return url


def _is_substantive_redirect(login_url, final_url):
    """判断 final_url 相对 login_url 是否发生了「实质跳转」。

    排除两类与登录无关的跳转：
    1. 纯协议升级（http→https）；
    2. host 微调（加/去 www、去默认端口）。
    只有跳到不同 host、或不同 path（非根路径规范化）时才视为实质跳转。
    """
    if not final_url or final_url == login_url:
        return False
    return _normalized_key(final_url) != _normalized_key(login_url)


def _is_login_wall(r):
    """该响应是否是"登录墙"（跳登录页 / 401 / 登录表单 / 提示未登录）。"""
    if r["status"] in (401, 403):
        return f"HTTP {r['status']}"
    if LOGIN_URL_PAT.search(urlparse(r["final_url"]).path):
        return f"被重定向到登录页 {r['final_url']}"
    if LOGIN_PAGE_PAT.search(r["text"]):
        return "返回的是登录表单"
    for w in ("请先登录", "尚未登录", "未授权", "登录已过期", "会话已过期", "无权访问",
              "unauthorized", "access denied", "please log in", "please sign in"):
        if w.lower() in r["text"].lower():
            return f"页面提示 {w!r}"
    return None


def judge_protected_page(anon, auth, contains=None, login_verdict=None, login_reason=""):
    """
    对比"登录前（匿名）"与"登录后"访问同一页面的内容，返回 (verdict, reason, info)。

    规则（结合登录响应证据与页面行为证据）：
      1. 接口明确返回认证失败 / 登录后仍被拦截（登录墙 / 401·403）→ 失败
      2. 登录前后表单消失 + 出现登录后元素 → 成功
      3. 登录响应已明确成功（凭据/跳转）→ 以它为准，页面相似度不作否决
      4. 指定了 contains：出现即成功、未出现即失败
      5. 兜底：登录前后内容相似度 ≤80%（变化明显）→ 成功；
         相似度 >80%（内容未变）→ **异常**（不判失败，避免漏掉 SPA 等正确密码，留待复核）
    """
    anon_plain = _plain_text(anon["text"])
    auth_plain = _plain_text(auth["text"])
    ratio = _diff_ratio(anon_plain, auth_plain)
    added = _added_snippets(anon_plain, auth_plain)
    info = {"ratio": ratio, "added": added, "anon_len": len(anon_plain), "auth_len": len(auth_plain)}

    # 登录后页面的行为特征
    anon_has_form = bool(LOGIN_PAGE_PAT.search(anon["text"]))
    auth_has_form = bool(LOGIN_PAGE_PAT.search(auth["text"]))
    auth_post_login_hit = next(
        (w for w in POST_LOGIN_ELEMENTS if w.lower() in auth["text"].lower()), None)
    # 与 judge_login_response 一致：匿名页里也有的元素属站点固有文案，不算登录证据
    if auth_post_login_hit and auth_post_login_hit.lower() in anon["text"].lower():
        auth_post_login_hit = None
    info.update({
        "anon_has_form": anon_has_form, "auth_has_form": auth_has_form,
        "auth_post_login_hit": auth_post_login_hit,
    })

    # 1. 登录后仍是登录墙
    wall = _is_login_wall(auth)
    if wall and login_verdict not in ("success", "captcha"):
        return "fail", f"登录后仍被拦截（{wall}）", info
    if auth["status"] >= 400 and login_verdict not in ("success", "captcha"):
        return "fail", f"登录后访问返回 HTTP {auth['status']}", info

    # 指定了登录后才会出现的内容：以它为准（优先级最高，用户显式指定）
    if contains:
        if contains in auth["text"]:
            return "success", f"页面出现 {contains!r}", info
        return "fail", f"页面未出现 {contains!r}", info

    # 登录响应已明确失败（接口返回认证失败/失败特征词）→ 页面特征不作翻案
    if login_verdict == "fail":
        return "fail", f"登录响应判定失败：{login_reason}", info

    # 登录响应判定为验证码/二次验证 → 转入人工复核，页面特征不作翻案（绝不判成功）
    if login_verdict == "captcha":
        return "captcha", f"登录响应判定需人工复核：{login_reason}", info

    # 2. 表单消失 + 出现登录后元素 → 成功
    if anon_has_form and not auth_has_form and auth_post_login_hit:
        return "success", f"登录表单消失且出现登录后元素 {auth_post_login_hit!r}", info

    # 3. 登录响应已明确成功 → 以它为准（页面相似度不作否决）
    if login_verdict == "success":
        return "success", f"登录响应已给出成功证据：{login_reason}", info

    # 5. 兜底：内容相似度
    #    宁可放过成功误报，也绝不漏掉正确密码：相似度低（内容变化明显）→ 判成功；
    #    相似度高（内容几乎没变）时**不再武断判失败**——很多正确登录后站点返回几乎
    #    相同的页面（SPA 单页应用登录态由 JS 异步加载、或登录后停留在一个骨架不变的
    #    确认页），此时若判 fail 就会漏掉真实正确的密码。故改为退回「异常」，留待人工复核。
    if ratio > 0.8:
        return "unknown", f"登录前后内容相似度 {ratio:.0%}（>80%），内容未发生明显变化，需人工复核", info
    return "success", f"登录前后内容相似度 {ratio:.0%}（≤80%），内容已发生变化", info


def _plain_text(html):
    """HTML → 纯文本，便于做内容差异比较（忽略标签与脚本样式）。"""
    if html and len(html) > 300000:  # 超大页面先截断，正则替换本身就够慢
        html = html[:150000] + html[-150000:]
    t = re.sub(r"(?is)<(script|style|noscript)\b.*?</\1>", " ", html or "")
    t = re.sub(r"(?s)<[^>]+>", " ", t)
    t = t.replace("&nbsp;", " ").replace("&amp;", "&").replace("&lt;", "<").replace("&gt;", ">")
    return re.sub(r"\s+", " ", t).strip()


def _diff_ratio(a, b):
    """两段文本的相似度（0~1），1 表示完全一致。逐级早停，避免长文本上的二次开销。"""
    if not a and not b:
        return 1.0
    if a == b:
        return 1.0
    sm = difflib.SequenceMatcher(None, a, b, autojunk=True)
    if sm.real_quick_ratio() < 0.5:  # 长度差异已足够大，不必精算
        return sm.real_quick_ratio()
    if sm.quick_ratio() < 0.5:  # 字符集差异已足够大
        return sm.quick_ratio()
    return sm.ratio()


def _added_snippets(anon_text, auth_text, max_n=3, min_len=6):
    """找出登录后新增的内容片段（按词对比，返回最长的几段）。"""
    a_words, b_words = anon_text.split(), auth_text.split()
    if len(a_words) > 4000 or len(b_words) > 4000:
        a_words, b_words = a_words[:4000], b_words[:4000]
    sm = difflib.SequenceMatcher(None, a_words, b_words, autojunk=True)
    added = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ("replace", "insert"):
            seg = " ".join(b_words[j1:j2]).strip()
            if len(seg) >= min_len:
                added.append(seg)
    added.sort(key=len, reverse=True)
    return added[:max_n]


def preview(text, limit=300):
    return re.sub(r"\s+", " ", text).strip()[:limit]


# --------------------------------------------------------------------------- #
# 单条检测
# --------------------------------------------------------------------------- #
def _brief_error(e):
    """把网络异常压成一行人话——原始堆栈在批量输出里是噪音。"""
    name = type(e).__name__
    msg = re.sub(r"\s+", " ", str(e))
    low = msg.lower()
    if "timeout" in name.lower() or "timed out" in low:
        return f"请求超时（{name}）"
    if "10061" in msg or "refused" in low:
        return "连接被拒绝（端口未开放或服务未启动）"
    if "10060" in msg or "10051" in msg or "unreachable" in low:
        return "网络不可达"
    if "getaddrinfo" in low or "name or service not known" in low or "nodename nor servname" in low:
        return "域名解析失败"
    if "ssl" in name.lower() or "certificate" in low:
        return f"SSL/证书错误（{name}）"
    if "too many redirects" in low:
        return "重定向次数过多（疑似登录循环）"
    if "aborted" in low or "reset by peer" in low or "max retries" in low:
        return "连接被中断（对端重置或代理拒绝）"
    return f"{name}: {msg[:120]}"


def check_one(url, username, password, args, check_url):
    """单条检测入口，负责兜住所有网络异常。

    返回 (verdict, reason, detail)，verdict ∈ {success, fail, unknown, error}。
    """
    sess = HttpSession(proxy=args.proxy, env_proxy=args.env_proxy)
    try:
        return _check_one_inner(sess, url, username, password, args, check_url)
    except Exception as e:  # noqa: BLE001
        return "error", _brief_error(e), ""
    finally:
        sess.close()


def _check_one_inner(sess, url, username, password, args, check_url):
    """对单个 url:username:password 做一次完整检测。

    返回 (verdict, reason, detail)，verdict ∈ {success, fail, unknown, error}。
    """
    try:
        # ---------- 0. DNS 预检（requests 的 timeout 不覆盖域名解析，这是卡死主因之一）----------
        if not resolve_host(urlparse(url).hostname or "", args.dns_timeout):
            return "error", f"DNS 解析失败或超时（>{args.dns_timeout:.0f}s），已跳过", ""

        payload = {args.user_field: username, args.pass_field: password}

        # ---------- 1. 先 GET 登录页：既是匿名基线，也用于抽取隐藏字段 ----------
        anon = None
        page_html = ""
        if check_url or args.auto_fields:
            try:
                anon = sess.request("GET", url, timeout=args.timeout, max_bytes=args.max_bytes,
                                    read_timeout=args.read_timeout)
                page_html = anon["text"]
            except Exception:
                anon = None

        hidden = {}
        if args.auto_fields and page_html:
            hidden = extract_form_fields(page_html)
            for k, v in hidden.items():
                payload.setdefault(k, v)

        # ---------- 2. 登录 ----------
        login_r = sess.post_login(url, payload, as_json=args.as_json,
                                  timeout=args.timeout, max_bytes=args.max_bytes,
                                  read_timeout=args.read_timeout)
        login_verdict, login_reason, login_info = judge_login_response(
            login_r, url, args.success_contains, args.fail_contains, anon=anon)

        # ---------- 3. 带会话访问验证页（权威判据：登录前后内容对比）----------
        verdict, reason, detail = login_verdict, login_reason, ""

        if check_url and anon is not None:
            auth = sess.request("GET", check_url, timeout=args.timeout, max_bytes=args.max_bytes,
                                read_timeout=args.read_timeout)
            verdict, reason, p_info = judge_protected_page(
                anon, auth, args.check_contains, login_verdict, login_reason)

            if args.verbose:
                detail = (
                    f"匿名 GET {check_url}: HTTP {anon['status']} -> {anon['final_url']}\n"
                    f"登录 POST {url}: HTTP {login_r['status']}"
                    + (f" -> {login_r['final_url']}" if login_r["final_url"] != url else "") + "\n"
                    f"已登录 GET {check_url}: HTTP {auth['status']} -> {auth['final_url']}"
                )
                if hidden:
                    detail += f"\n自动携带页面字段: {', '.join(sorted(hidden))}"
                if p_info.get("ratio") is not None:
                    detail += (f"\n内容相似度 {p_info['ratio']:.1%}"
                               f"（匿名 {p_info['anon_len']} 字 → 登录后 {p_info['auth_len']} 字）")
                    for s in p_info.get("added", [])[:2]:
                        detail += f"\n登录后新增: {preview(s, 100)}"
                detail += f"\n判定依据: {reason}"
        elif args.verbose:
            detail = f"登录 POST {url}: HTTP {login_r['status']}\n判定依据: {login_reason}"
            if hidden:
                detail += f"\n自动携带页面字段: {', '.join(sorted(hidden))}"

        if verdict == "unknown":
            reason += "（建议对该站点单独用 -v --check-contains '登录后页面特征文字' 复核）"
        return verdict, reason, detail
    except Exception as e:  # noqa: BLE001
        return "error", _brief_error(e), ""


def run_with_ceiling(fn, ceiling, timeout_result):
    """在守护线程里跑 fn，超过 ceiling 秒就不再等待，直接返回 timeout_result。

    Python 无法强杀线程，但把任务放进守护线程后主线程可以"不等它"继续走，
    卡住的线程最多再活一个 timeout 周期就会自己结束。
    """
    box = {}

    def target():
        try:
            box["v"] = fn()
        except BaseException as e:  # noqa: BLE001 - 子线程异常必须带回主线程
            box["v"] = ("error", f"{type(e).__name__}: {e}", "")

    th = threading.Thread(target=target, daemon=True)
    th.start()
    th.join(ceiling)
    if th.is_alive():
        return timeout_result
    return box.get("v", ("error", "未知内部错误", ""))


VERDICT_LABELS = {"success": "成功", "fail": "失败", "unknown": "异常", "error": "异常", "captcha": "验证码"}


def run_one_hard(item, args, hard_timeout):
    """单条检测的并发任务，带硬超时，返回 7 元组。"""
    idx, (url, username, password) = item
    res = run_with_ceiling(
        lambda: check_one(url, username, password, args, None if args.no_check else (args.check_url or url)),
        hard_timeout,
        ("error", f"超过硬超时 {hard_timeout:.0f}s 未返回，已跳过", ""))
    verdict, reason, detail = res
    return idx, url, username, password, VERDICT_LABELS.get(verdict, "异常"), reason, detail


def load_targets(path):
    """读取批量文件，每行 url:username:password（忽略空行和 # 开头的注释）。

    会被跳过并计入 errors 的三类：
      1. 地址不是 http:// 或 https:// 开头；
      2. 用户名或密码含冒号（无法与分隔符区分）；
      3. 密码为空——空密码登录成功几乎必然是误判（无登录框的静态页也会"原样返回"），
         与其产生假阳性不如直接跳过，避免污染成功清单。
    """
    target_re = re.compile(r"^(.*):([^/:]+):([^:]*)$")

    targets, errors = [], []
    with open(path, "r", encoding="utf-8-sig") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if not line.startswith(("http://", "https://")):
                errors.append(f"第 {lineno} 行格式错误（地址需 http:// 或 https:// 开头）：{raw.strip()}")
                continue

            m = target_re.match(line)
            if not m:
                errors.append(f"第 {lineno} 行格式错误（应为 url:username:password，且用户名/密码不能含冒号）：{raw.strip()}")
                continue
            url, username, password = m.group(1), m.group(2), m.group(3)
            sp = urlparse(url)
            if sp.scheme not in ("http", "https") or not sp.netloc or ":" in (sp.path or ""):
                errors.append(f"第 {lineno} 行用户名或密码含冒号（不允许包含 ':'）：{raw.strip()}")
                continue
            # 空密码：登录成功几乎必然是误判，直接跳过而不是产生假阳性
            if not password:
                errors.append(f"第 {lineno} 行密码为空，已跳过（空密码判成功通常是误判）：{raw.strip()}")
                continue
            targets.append((url, username, password))
    return targets, errors


def fmt_dur(sec):
    if sec < 60:
        return f"{sec:.1f}s"
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h{m:02d}m{s:02d}s" if h else f"{m}m{s:02d}s"


def net_desc(args):
    """描述实际出网方式——很多"卡住"其实是请求被塞进了看不见的代理。"""
    if args.proxy:
        return f"经指定代理 {args.proxy}"
    if not args.env_proxy:
        return "直连（已忽略环境变量代理）"
    try:
        import urllib.request

        p = "; ".join(f"{k}={v}" for k, v in sorted(urllib.request.getproxies().items()))
    except Exception:
        p = ""
    return f"经环境代理 {p}" if p else "直连"


# 常见的二级后缀（如 com.cn / edu.cn / gov.cn），这类域名取最后三段才算根域名
_MULTI_TLD = {
    "com.cn", "net.cn", "org.cn", "gov.cn", "edu.cn", "ac.cn", "mil.cn",
    "com.hk", "net.hk", "org.hk", "edu.hk", "gov.hk",
    "com.tw", "net.tw", "org.tw", "edu.tw", "gov.tw",
    "com.mo", "net.mo", "org.mo", "edu.mo", "gov.mo",
    "com.sg", "com.my", "co.jp", "co.uk", "org.uk", "ac.uk", "gov.uk", "co.kr", "or.kr",
}


def root_domain(url):
    """从 URL 提取根域名，用于命名结果文档。

    例如 https://sf.ncepu.edu.cn/xysf/ -> ncepu.edu.cn
         https://webvpn.ncepu.edu.cn/   -> ncepu.edu.cn
         https://www.example.com/login  -> example.com
    解析失败时退化为按 host 去 www/端口。
    """
    try:
        host = (urlparse(url).hostname or "").lower()
    except Exception:
        host = ""
    if not host:
        return "_unknown"
    # 去掉前导 www. 和端口
    host = host.split(":")[0]
    if host.startswith("www."):
        host = host[4:]
    # 纯 IP 地址原样返回，不做域名切段
    if re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", host):
        return host
    parts = host.split(".")
    if len(parts) <= 2:
        return host
    # 末两段是二级后缀（如 edu.cn）→ 取三段；否则取两段
    tail2 = ".".join(parts[-2:])
    if tail2 in _MULTI_TLD:
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def write_success_files(success_list, output_dir, script_dir):
    """把成功清单按根域名分组写入文档，每份文档命名为 <根域名>.txt。

    每行格式：url:username:password。同一根域名下所有成功条目汇总到一个文件。
    返回写出的文件路径列表。
    """
    if not success_list:
        return []
    groups = {}
    for _, url, username, password in success_list:
        groups.setdefault(root_domain(url), []).append((url, username, password))

    out_dir = output_dir or script_dir
    try:
        os.makedirs(out_dir, exist_ok=True)
    except Exception:
        out_dir = script_dir

    written = []
    for domain, items in groups.items():
        # 域名里可能混入路径字符，做一次安全清洗
        safe = re.sub(r"[^0-9a-zA-Z.\-_]", "_", domain) or "_unknown"
        path = os.path.join(out_dir, f"{safe}.txt")
        try:
            with open(path, "w", encoding="utf-8") as f:
                for url, username, password in items:
                    f.write(f"{url}:{username}:{password}\n")
            written.append(path)
        except Exception as e:  # noqa: BLE001 - 写盘失败不能中断整个检测
            out(f"[写文档失败] {safe}.txt：{_brief_error(e)}")
    return written


def write_captcha_files(captcha_list, output_dir, script_dir):
    """把「需人工复核（验证码/二次验证）」清单按根域名分组写入文档。

    文档命名为 <根域名>_captcha.txt，与成功文档（<根域名>.txt）分开，避免污染成功清单。
    每行格式：url:username:password。返回写出的文件路径列表。
    """
    if not captcha_list:
        return []
    groups = {}
    for _, url, username, password in captcha_list:
        groups.setdefault(root_domain(url), []).append((url, username, password))

    out_dir = output_dir or script_dir
    try:
        os.makedirs(out_dir, exist_ok=True)
    except Exception:
        out_dir = script_dir

    written = []
    for domain, items in groups.items():
        safe = re.sub(r"[^0-9a-zA-Z.\-_]", "_", domain) or "_unknown"
        path = os.path.join(out_dir, f"{safe}_captcha.txt")
        try:
            with open(path, "w", encoding="utf-8") as f:
                for url, username, password in items:
                    f.write(f"{url}:{username}:{password}\n")
            written.append(path)
        except Exception as e:  # noqa: BLE001 - 写盘失败不能中断整个检测
            out(f"[写文档失败] {safe}_captcha.txt：{_brief_error(e)}")
    return written


def main():
    ap = argparse.ArgumentParser(
        description="携带账号密码登录并验证是否成功。支持单条（--url -u -p）或批量（--file）。")
    ap.add_argument("--file", default=None,
                    help="批量检测文件，每行一条 'url:username:password'（# 开头为注释）")
    ap.add_argument("--url", help="登录接口地址（单条模式，与 -u/-p 搭配）")
    ap.add_argument("-u", "--username", help="用户名 / 账号（单条模式）")
    ap.add_argument("-p", "--password", default=None, help="密码（省略则交互输入，或读环境变量 LOGIN_PASSWORD）")
    ap.add_argument("--user-field", default="username", help="用户名字段名（默认 username）")
    ap.add_argument("--pass-field", default="password", help="密码字段名（默认 password）")
    ap.add_argument("--json", action="store_true", dest="as_json", help="以 JSON 格式提交（默认表单）")
    ap.add_argument("--check-url", default=None,
                    help="登录后访问该地址做行为验证（默认：登录页本身；也可填必须登录才能访问的页面）")
    ap.add_argument("--no-check", action="store_true",
                    help="关闭行为验证，只看登录接口响应（不推荐）")
    ap.add_argument("--check-contains", default=None,
                    help="验证页中应出现的内容（如昵称、'我的订单'），出现即视为成功")
    ap.add_argument("--success-contains", default=None,
                    help="登录响应中出现该字符串即视为成功；未命中不判定失败，继续按其他规则判断")
    ap.add_argument("--fail-contains", default=None, help="登录响应中出现该字符串即视为失败")
    ap.add_argument("--auto-fields", dest="auto_fields", action="store_true", default=True,
                    help="自动从登录页抽取并携带隐藏字段，如 CAS 的 lt/execution/_eventId、CSRF token（默认开启）")
    ap.add_argument("--no-auto-fields", dest="auto_fields", action="store_false",
                    help="关闭自动抽取隐藏字段")
    ap.add_argument("--timeout", type=float, default=8.0, help="单次请求的超时秒数（默认 8）")
    ap.add_argument("--concurrency", type=int, default=20,
                    help="批量检测并发数（默认 20，即同时最多检测 20 个站点）")
    ap.add_argument("--hard-timeout", type=float, default=None,
                    help="单条任务的硬超时秒数（超时直接丢弃，默认 (timeout+read-timeout)*2+5）")
    ap.add_argument("--max-time", type=float, default=None,
                    help="整轮批量检测的总时限秒数，到点立即结束并输出已完成结果")
    ap.add_argument("--max-bytes", type=int, default=524288,
                    help="单个响应体最多读取的字节数（默认 512KB，防止超大页面耗尽内存）")
    ap.add_argument("--read-timeout", type=float, default=None,
                    help="读取单个响应体的总时间预算秒数（默认 timeout*2，最低 5s）。"
                         "服务器每几秒喂一小块时单次 recv 永不超时，只有这个预算能挡住慢速流")
    ap.add_argument("--dns-timeout", type=float, default=3.0,
                    help="DNS 解析超时秒数（默认 3；requests 的 timeout 不覆盖 DNS）")
    ap.add_argument("--progress-every", type=int, default=25,
                    help="每完成多少条打印一行进度统计（默认 25，0 关闭）")
    ap.add_argument("--proxy", default=None,
                    help="显式指定代理（如 http://127.0.0.1:8080），指定后不再读取环境变量里的代理")
    ap.add_argument("--no-env-proxy", dest="env_proxy", action="store_false", default=True,
                    help="忽略 HTTP_PROXY/HTTPS_PROXY 环境变量，全部直连")
    ap.add_argument("-v", "--verbose", action="store_true", help="打印详细诊断信息（相似度、状态码、响应预览等）")
    ap.add_argument("--output-dir", default=None,
                    help="成功结果文档输出目录（默认与脚本同目录）。每个根域名生成一个独立文档")
    args = ap.parse_args()

    if args.timeout <= 0:
        ap.error("--timeout 必须大于 0")
    read_timeout = args.read_timeout if args.read_timeout else max(args.timeout * 2, 5)
    args.read_timeout = read_timeout
    hard_timeout = args.hard_timeout if args.hard_timeout else (args.timeout + read_timeout) * 2 + 5

    # 结果文档默认写到脚本所在目录（可用 --output-dir 覆盖）
    _script_dir = os.path.dirname(os.path.abspath(__file__))

    # ---------- 批量模式 ----------
    if args.file:
        targets, parse_errors = load_targets(args.file)
        if parse_errors:
            out(f"[格式错误] 共 {len(parse_errors)} 条，已跳过：")
            for e in parse_errors:
                out(f"  {e}")
            out()
        if not targets:
            out("批量文件里没有可检测的有效条目。")
            return 2

        concurrency = max(1, args.concurrency)
        out(f"共 {len(targets)} 条有效条目待检测（并发 {concurrency}，超时 {args.timeout}s，"
            f"硬超时 {hard_timeout:.0f}s"
            + (f"，总时限 {fmt_dur(args.max_time)}" if args.max_time else "") + "）：")
        out(f"网络：{net_desc(args)}；引擎：{'requests' if HAS_REQUESTS else 'urllib'}")

        n_success = n_fail = n_error = n_captcha = 0
        done = 0
        success_list = []
        captcha_list = []
        print_lock = threading.Lock()
        t_start = time.monotonic()

        pwd_map = {i: pwd for i, (_, _, pwd) in enumerate(targets, 1)}

        def emit(idx, url, username, label, reason, detail):
            nonlocal done, n_success, n_fail, n_error, n_captcha
            with print_lock:
                done += 1
                if label == "成功":
                    n_success += 1
                    success_list.append((idx, url, username, pwd_map.get(idx, "")))
                elif label == "验证码":
                    n_captcha += 1
                    captcha_list.append((idx, url, username, pwd_map.get(idx, "")))
                elif label == "失败":
                    n_fail += 1
                else:
                    n_error += 1
                out(f"[{done}/{len(targets)}] {label} | {url} | {username} | {reason}")
                if args.verbose and detail:
                    for ln in detail.splitlines():
                        out(f"      {ln}")
                if args.progress_every and done % args.progress_every == 0:
                    el = time.monotonic() - t_start
                    eta = el / done * (len(targets) - done)
                    out(f"  -- 进度 {done}/{len(targets)} ({done/len(targets):.1%}) | "
                        f"成功 {n_success} 失败 {n_fail} 异常 {n_error} 验证码 {n_captcha} | "
                        f"已用 {fmt_dur(el)} 预计剩余 {fmt_dur(eta)}")

        def summary():
            out()
            out("-" * 60)
            out(f"汇总：成功 {n_success} / 失败 {n_fail} / 异常 {n_error} / 验证码 {n_captcha} / 共 {len(targets)}"
                f"（实际完成 {done} 条，用时 {fmt_dur(time.monotonic() - t_start)}）")
            success_list.sort(key=lambda x: x[0])
            if success_list:
                out()
                out(f"成功清单（{len(success_list)} 条，格式 url:username:password）：")
                for _, url, username, password in success_list:
                    out(f"{url}:{username}:{password}")
                # 按根域名写结果文档
                written = write_success_files(success_list, args.output_dir, _script_dir)
                if written:
                    out()
                    out(f"已按根域名写出 {len(written)} 份成功结果文档：")
                    for p in written:
                        out(f"  {p}")
            # 验证码/二次验证 → 单独输出到「需人工复核」文档，绝不与成功清单混在一起
            captcha_list.sort(key=lambda x: x[0])
            if captcha_list:
                out()
                out(f"验证码清单（{len(captcha_list)} 条，需人工复核，格式 url:username:password）：")
                for _, url, username, password in captcha_list:
                    out(f"{url}:{username}:{password}")
                written = write_captcha_files(captcha_list, args.output_dir, _script_dir)
                if written:
                    out()
                    out(f"已按根域名写出 {len(written)} 份验证码复核文档（<域名>_captcha.txt）：")
                    for p in written:
                        out(f"  {p}")
            if n_error:
                out()
                out(f"提示：{n_error} 条判为「异常」（无明确成功/失败证据）。这类站点通常需要"
                    f"验证码、加密密码或短信二次验证，脚本无法自动登录；对重点站点建议单独用 "
                    f"-v --check-contains '登录后页面特征文字' 复核。")

        with ThreadPoolExecutor(max_workers=concurrency, thread_name_prefix="chk") as ex:
            futures = [ex.submit(run_one_hard, item, args, hard_timeout)
                       for item in enumerate(targets, 1)]
            try:
                for fut in as_completed(futures, timeout=args.max_time):
                    idx, url, username, _pwd, label, reason, detail = fut.result()
                    emit(idx, url, username, label, reason, detail)
            except KeyboardInterrupt:
                out("\n[中断] 已取消，输出已完成的结果……")
                summary()
                os._exit(130)
            # 注意：Python 3.10 的 concurrent.futures.TimeoutError 并不继承内建 TimeoutError，两个都要接
            except (FuturesTimeoutError, TimeoutError):
                out(f"\n[总时限] 已达 {fmt_dur(args.max_time or 0)}，中止剩余任务并输出已完成结果……")
                summary()
                os._exit(0)  # 直接退出，不等残留的守护线程
            except Exception as e:  # noqa: BLE001
                out(f"\n[异常] {type(e).__name__}: {e}")
                summary()
                os._exit(1)

        summary()
        return 0 if n_fail == 0 and n_error == 0 else 1

    # ---------- 单条模式 ----------
    if not args.url or not args.username:
        ap.error("单条模式需要 --url 和 -u；或使用 --file 指定批量文件")
    for u in filter(None, (args.url, args.check_url)):
        if urlparse(u).scheme not in ("http", "https"):
            ap.error(f"地址必须以 http:// 或 https:// 开头：{u}")

    check_url = args.check_url if args.check_url else (None if args.no_check else args.url)
    password = args.password or os.environ.get("LOGIN_PASSWORD") or getpass.getpass("密码（不回显）: ")

    ok, host = dns_precheck(args.url, args.dns_timeout)
    if not ok:
        out(f"请求异常：DNS 解析失败或超时 {host}（{args.dns_timeout}s）")
        return 2

    verdict, reason, detail = run_with_ceiling(
        lambda: check_one(args.url, args.username, password, args, check_url),
        hard_timeout,
        ("error", f"超过硬超时 {hard_timeout:.0f}s 未返回（可调 --hard-timeout）", ""))

    if args.verbose and detail:
        out(detail)

    if verdict == "success":
        out("登录成功")
        code = 0
    elif verdict == "captcha":
        out(f"需人工复核（{reason}）")
        code = 1
    elif verdict == "error":
        out(f"请求异常：{reason}")
        code = 2
    else:
        out(f"登录失败（{reason}）")  # fail 或无明确证据（unknown）一律按保守原则判为失败
        code = 1
    return code


if __name__ == "__main__":
    sys.exit(main())
