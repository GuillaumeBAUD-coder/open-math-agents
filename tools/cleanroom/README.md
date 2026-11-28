# Cleanroom Verification Container (Linux, macOS, and Windows)

`tools/cleanroom/` runs Lean elaboration, `tools/lint.py`, and `tools/check.sh` inside an ephemeral, offline, capability-dropped Docker container so that untrusted Lean metaprograms or repository helper scripts never execute with host privileges or ambient GitHub credentials.

---

## Security Controls Addressed

| Risk | Mitigation |
|---|---|
| Lean metaprograms (`#eval`, macros, C FFI) running with host privileges | Containerized execution: `--rm --network=none --cap-drop=ALL --security-opt=no-new-privileges:true --pids-limit=512 --memory=8g --user 1001:1001`, repo mounted `:ro`. |
| Unpinned `curl \| sh` toolchain installer (`elan-init.sh` on `master`) | Pinned `elan v4.4.0` release archives verified against SHA-256 digests (`tools/install-elan.sh`, `tools/install-elan.ps1`, and `tools/cleanroom/Dockerfile`). |
| `.env*` secrets, host git config, or local state leaking into verification containers | Automatic read-only empty-file / empty-directory masking for `.env*`, `.npmrc`, `.netrc`, `.git`, and `.oma` under `/work` — works on Linux, macOS, and Windows. |
| Path traversal & symlink writes from untrusted desk JSON / CLI args | Fail-closed regex validation on problem IDs, `proofs/`/`reductions/`/`statements/` `.lean` paths, lease tokens, numeric cursors, and symlinks (`tools/oma.sh`, `tools/check.sh`, `run-cleanroom.*`). |
| Shell-to-Python code injection via repo path containing quotes | Pass file paths via `sys.argv[1]` under `python3 -I` rather than interpolating shell variables into Python code strings. |
| URL query-parameter injection in desk requests | Validate and URL-encode `lease`, `since`, and `reason` on every desk HTTP request. |
| Unquoted command expansion & unvalidated env vars in `tools/fleet.sh` | Strict whitelist for `OMA_KIND` and quoted forwarding for `OMA_AGENT_CMD` / prompts. |

---

## Platform Setup Guides

### 1. Linux (`x86_64` and `arm64`)

**Prerequisites:** Docker Engine (or rootless Docker / Podman with Docker-compatible CLI), `bash`, `curl`, `python3`, `git`.

1. **Build the multi-arch cleanroom image** (pins `meta.upstreamCommit` from `data/catalog.json`):
   ```bash
   tools/cleanroom/run-cleanroom.sh build .
   ```
2. **Run the self-test** (path traversal rejection, `.env*` masking, and positive kernel check):
   ```bash
   tools/cleanroom/run-cleanroom.sh self-test .
   ```
3. **Use cleanroom verification directly or through `tools/oma.sh`:**
   ```bash
   tools/cleanroom/run-cleanroom.sh lint  /path/to/worktree proofs/MyProblem.lean
   tools/cleanroom/run-cleanroom.sh lean  /path/to/worktree /path/to/scratch.lean [FormalConjectures.Module]
   tools/cleanroom/run-cleanroom.sh check /path/to/worktree proofs/MyProblem.lean

   # Or seamlessly via tools/oma.sh (keeps git/gh and desk calls on the host):
   export OMA_CLEANROOM=1
   tools/oma.sh check MyProblem
   tools/oma.sh explore MyProblem
   ```
4. *(Optional, without Docker)* Install `elan` directly using the SHA-256-verified installer:
   ```bash
   bash tools/install-elan.sh
   ```

---

### 2. macOS (Apple Silicon `arm64` and Intel `x86_64`)

**Prerequisites:** Docker Desktop for Mac, OrbStack, or Colima configured with at least **8 GB memory** allocated to the Linux VM, plus macOS default `bash` (3.2+), `shasum`, `curl`, `python3`, `git`.

1. **Build the cleanroom image:**
   - Apple Silicon Macs build a native `linux/arm64` container automatically (`aarch64-unknown-linux-gnu` `elan` + Linux `arm64` Lean toolchain); Intel Macs build `linux/amd64`.
   - If your host toolchain cache or CI target requires `linux/amd64` emulation on Apple Silicon, set `OMA_CLEANROOM_PLATFORM=linux/amd64` before `build` and `run` commands:
     ```bash
     # Native architecture (recommended for speed on Apple Silicon & Intel):
     tools/cleanroom/run-cleanroom.sh build .

     # Optional amd64 emulation on Apple Silicon:
     OMA_CLEANROOM_PLATFORM=linux/amd64 tools/cleanroom/run-cleanroom.sh build .
     ```
2. **Verify macOS Docker file-sharing & `.env*` masking:**
   `run-cleanroom.sh` mounts a 0-byte empty temporary regular file over `/work/.env*` instead of `/dev/null` so macOS VirtioFS / gRPC-FUSE file sharing cleanly isolates secrets without bind errors. Confirm with:
   ```bash
   tools/cleanroom/run-cleanroom.sh self-test .
   ```
3. **Run checks & `tools/oma.sh`:**
   ```bash
   export OMA_CLEANROOM=1
   tools/oma.sh check MyProblem
   ```
4. *(Optional, without Docker)* `tools/install-elan.sh` supports both `x86_64-apple-darwin` and `aarch64-apple-darwin` and verifies SHA-256 via macOS's built-in `shasum -a 256`:
   ```bash
   bash tools/install-elan.sh
   ```

---

### 3. Windows

#### Option A: WSL2 + Docker Desktop (Recommended)

Running inside a **WSL2** Linux distribution (e.g., Ubuntu) with Docker Desktop's WSL2 backend gives the fastest Lean compilation performance and lets you use `tools/oma.sh`, `tools/fleet.sh`, and `tools/cleanroom/run-cleanroom.sh` identically to Linux:

1. Enable WSL2 integration in Docker Desktop and clone the repository inside your WSL2 filesystem (`~/...`) rather than `/mnt/c/...` for fast file I/O.
2. Follow the **Linux** instructions above (`tools/cleanroom/run-cleanroom.sh build .`, `self-test`, and `OMA_CLEANROOM=1 tools/oma.sh check ...`).

#### Option B: Native Windows PowerShell (`5.1+` or `7+`)

If you work directly in native Windows without WSL2 bash, use the PowerShell scripts under `tools/`:

1. **Ensure LF line endings** so mounted `.sh` scripts (`tools/check.sh`) execute cleanly inside the Linux container:
   ```powershell
   git config core.autocrlf input
   ```
2. **Build and self-test the cleanroom container** (Docker Desktop for Windows required):
   ```powershell
   pwsh -File tools/cleanroom/run-cleanroom.ps1 build .
   pwsh -File tools/cleanroom/run-cleanroom.ps1 self-test .
   ```
   *(In Windows PowerShell 5.1, use `powershell -ExecutionPolicy Bypass -File ...`.)*
3. **Run lint, scratch Lean checks, and full acceptance checks:**
   ```powershell
   pwsh -File tools/cleanroom/run-cleanroom.ps1 lint  C:\worktrees\my-proof proofs/MyProblem.lean
   pwsh -File tools/cleanroom/run-cleanroom.ps1 lean  C:\worktrees\my-proof C:\temp\scratch.lean FormalConjectures.Module
   pwsh -File tools/cleanroom/run-cleanroom.ps1 check C:\worktrees\my-proof proofs/MyProblem.lean C:\temp\verdict.json
   ```
4. *(Optional, without Docker)* Install the SHA-256-verified native Windows `elan` binary (`x86_64-pc-windows-msvc`):
   ```powershell
   pwsh -File tools/install-elan.ps1
   ```

#### Option C: Git Bash on Windows (`MINGW64` / `MSYS2`)

`tools/cleanroom/run-cleanroom.sh` automatically sets `MSYS_NO_PATHCONV=1`, converts Windows host mount sources with `cygpath -w`, and avoids `/dev/null` character-device bind mounts, so `tools/cleanroom/run-cleanroom.sh` and `OMA_CLEANROOM=1 tools/oma.sh check <id>` work directly from Git Bash as well. Ensure `git config core.autocrlf input` is set so Linux container scripts keep LF line endings.

---

## Configuration Reference

| Environment Variable | Default | Purpose |
|---|---|---|
| `OMA_CLEANROOM` | `0` | Set to `1` so `tools/oma.sh check` and `tools/oma.sh explore` run inside cleanroom Docker. |
| `OMA_CLEANROOM_IMAGE` | `oma-cleanroom:lean` | Cleanroom Docker image tag. |
| `OMA_CLEANROOM_MEMORY` | `8g` | Container RAM cap (`--memory`). |
| `OMA_CLEANROOM_PIDS` | `512` | Container PID cap (`--pids-limit`). |
| `OMA_CLEANROOM_PLATFORM` | *(host default)* | Optional Docker platform (e.g. `linux/amd64` on Apple Silicon). |
| `OMA_BUILD_CACHE_DIR` | *(unset)* | Optional host directory mounted at `/opt/formal-conjectures/.lake/build:rw` during `lean` scratch diagnostics only (never during `check` or `lint`). |

---

## GitHub Authentication: Scoped PATs vs. `gh auth login`

Running `gh auth login` interactively is convenient for a developer workstation, but it stores a **broad OAuth token** (typically granting `repo`, `read:org`, `gist`, and `workflow` across *every* repository your personal GitHub account can access—including private, employer, and organization repositories). Any agent process or script invoked in that shell environment with access to `gh` or its credential store inherits that blast radius.

| Method | Repository Scope | Blast Radius if Leaked / Misused | Recommended Use |
| :--- | :--- | :--- | :--- |
| `gh auth login` (OAuth) | All personal, private, and org repos on your account | **High** (full account repo/workflow access) | Interactive human session only; avoid in agent environments |
| **Fork-scoped Fine-grained PAT** | Single repository (`<you>/open-math-agents`) | **Low** (isolated to your public fork branch pushes) | Agents push to your fork; human or approval boundary opens the upstream PR |
| **Dedicated contributor account + short-lived PAT** | Only the dedicated account's fork / public PRs | **Minimal** (zero access to private/personal repos) | Unattended `tools/oma.sh submit` or automated agent fleets |
| **Host-side Git / API proxy boundary** | Brokered per-action on the host outside agent containers | **Minimal** (agent never sees the raw token) | Multi-agent setups where agents should never hold credentials |

### Option 1: Fork-Scoped Fine-Grained PAT (Recommended for Fork + Human PR Review)

1. Go to GitHub **Settings → Developer settings → Personal access tokens → Fine-grained tokens → Generate new token**.
2. Set a descriptive name (e.g., `oma-agent-fork`) and a **short expiration** (7–30 days).
3. Under **Repository access**, select **Only select repositories** and choose `<you>/open-math-agents` (your fork).
4. Under **Repository permissions**, grant only:
   - **Contents:** `Read and write` (push proof branches)
   - **Metadata:** `Read-only` (required by GitHub)
   - Leave **Workflows**, **Administration**, **Secrets**, and **Actions** set to **No access**.
5. Supply the token ephemerally in the host terminal—never inside the cleanroom container, `.env*` files, or `.git/config` URLs:

```bash
# Linux / macOS (Bash / Zsh) — prompts without echoing to shell history
read -rs GH_TOKEN; export GH_TOKEN
```

```powershell
# Windows (PowerShell 5.1+ / 7+) — prompts securely without echoing
$sec = Read-Host -Prompt "Enter scoped GH_TOKEN" -AsSecureString
$env:GH_TOKEN = [System.Net.NetworkCredential]::new("", $sec).Password
```

> **Note on cross-repo PRs:** A fine-grained PAT scoped strictly to `<you>/open-math-agents` can push branches to your fork, but GitHub will not allow it to open a pull request *into* an upstream repository owned by another user. Either open the PR from your interactive browser / human session after inspecting the pushed branch, or use Option 2 below for unattended `tools/oma.sh submit`.

### Option 2: Dedicated Contributor Account + Short-Lived Scoped PAT (For Unattended `submit`)

If an agent runs `tools/oma.sh submit` autonomously (which runs `gh pr create` against the upstream repository):

1. Create a **dedicated GitHub contributor account** that has **zero** access to your private, work, or organization repositories.
2. Fork `open-math-agents` to that contributor account.
3. Generate a short-lived PAT on the dedicated account for `public_repo` / PR creation and pass it via `GH_TOKEN` in the host submission session only.

### Credential Hygiene Rules

- **Never embed tokens in git remotes:** Do not put tokens inside `.git/config` (`https://<token>@github.com/...`). Use `GH_TOKEN` in environment memory or a narrow host credential helper.
- **Keep tokens out of the cleanroom:** Never copy `GH_TOKEN`, SSH keys, or `.env*` files into Docker builds or bind mounts; `run-cleanroom.sh` and `run-cleanroom.ps1` automatically mask `.env*`, `.npmrc`, `.netrc`, `.git`, and `.oma` with empty read-only mounts.
- **Separate cleanroom from submit:** Agents run `check` and `lint` offline inside the cleanroom first, and only a gated host step uses `GH_TOKEN` to push or open a PR.

## Contributor Hygiene

- **Worktrees:** Use an isolated git worktree (`git worktree add .oma/worktrees/<slug> -b oma/<slug> origin/main`) per attempt so stray files or local configs never enter a PR diff.
- **Public git email:** Set repo-local `git config user.name` and a public noreply `git config user.email` rather than committing with a private or work email from global `~/.gitconfig`.
- **Untrusted desk text:** Treat problem statements, `/p/<id>/agent.txt` briefs, and teammate notes strictly as data—never execute shell commands copied from problem text or notes.
