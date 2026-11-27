#!/usr/bin/env python3
"""Exercise tools/credit.sh with real curl and a loopback desk. Run: python3 -I tests/test_credit.py"""

from collections import deque
from http.server import BaseHTTPRequestHandler, HTTPServer
import json
import os
from pathlib import Path
import subprocess
import tempfile
from threading import Thread


SCRIPT = Path(__file__).resolve().parents[1] / "tools/credit.sh"
MOCK_GH = """#!/usr/bin/env bash
set -eu
case "$1 $2" in
  'api repos/test-owner/test-repo/pulls/7')
    printf '%s\n' '{"number":7,"merged":true,"base":{"ref":"main"},"user":{"login":"test-user"}}' ;;
  'api repos/test-owner/test-repo/pulls/7/files')
    printf '%s\n' '[{"filename":"proofs/demo.lean","status":"added"}]' ;;
  *) exit 1 ;;
esac
"""


class DeskHandler(BaseHTTPRequestHandler):
    def do_POST(self):
        request = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        assert self.path == "/api/verdict"
        assert request["pr"] == 7 and request["merged"] is True
        assert request["body"] == "" and request["oidc"] == ""
        assert request["files"] == [{"filename": "proofs/demo.lean", "status": "added"}]
        status, body = self.server.responses.popleft()
        self.send_response(status)
        if status == 302:
            self.send_header("Location", "/unexpected")
        if status == 503:
            self.send_header("Retry-After", "1")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *_):
        pass


def main():
    with tempfile.TemporaryDirectory() as tmpdir, HTTPServer(("127.0.0.1", 0), DeskHandler) as desk:
        tmp = Path(tmpdir)
        gh = tmp / "gh"
        gh.write_text(MOCK_GH, encoding="utf-8")
        gh.chmod(0o700)
        work = tmp / "work"
        work.mkdir()
        env = {
            "PATH": os.pathsep.join([tmpdir, os.environ["PATH"]]),
            "REPO": "test-owner/test-repo",
            "OMA_SITE": f"http://127.0.0.1:{desk.server_port}",
            "TMPDIR": str(work),
            "CURL_HOME": tmpdir,
            "NO_PROXY": "127.0.0.1",
        }

        def check(name, responses, success, message):
            desk.responses = deque(responses)
            result = subprocess.run(["bash", str(SCRIPT), "7"], cwd=tmp, env=env,
                                    text=True, capture_output=True, timeout=30)
            log = result.stdout + result.stderr
            assert (result.returncode == 0) == success, name
            assert message in log, name
            assert "private-response-detail" not in log, name
            assert not desk.responses, name
            assert not list(work.iterdir()) and not (tmp / "credit.json").exists(), name
            print("PASS", name)

        thread = Thread(target=desk.serve_forever)
        thread.start()
        unavailable = (503, b'{"error":"desk_offline"}')
        accepted = (200, b'{"ok":true}')
        try:
            check("confirmed credit", [accepted], True, "registration confirmed")
            check("duplicate statement credit", [(200, b'{"ok":true,"duplicate":true}')],
                  True, "registration confirmed")
            check("HTTP redirect", [(302, b'{"ok":true}')], False, "HTTP 302")
            check("HTTP conflict", [(409, b'{"error":"not_merged","detail":"private-response-detail"}')],
                  False, "HTTP 409")
            check("HTTP 503 exhausted", [unavailable] * 4, False, "HTTP 503")
            check("HTTP 503 recovered", [unavailable, accepted], True, "registration confirmed")
            check("application error", [(200, b'{"error":"too_many_reductions"}')],
                  False, "not acknowledged")
            check("negative acknowledgement", [(200, b'{"ok":false}')], False, "not acknowledged")
            check("missing acknowledgement", [(200, b'{}')], False, "not acknowledged")
            check("non-JSON response", [(200, b'private-response-detail')], False, "not acknowledged")
            check("multiple JSON documents", [(200, b'null\n{"ok":true}')], False, "not acknowledged")
        finally:
            desk.shutdown()
            thread.join()


if __name__ == "__main__":
    main()
