// Tests of tools/compare_claim.py (the checker that compares a re-run's output with evidence/<id>/claim.json).
// Run with: node --test tests/compare_claim.test.mjs  (needs python3 on PATH; no network, no Worker)
import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const TOOL = path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "tools", "compare_claim.py");

/** Writes claim.json and run.txt to a fresh temp dir, runs the checker, returns {code, out}. */
function check(claim, output) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "claim-"));
  fs.writeFileSync(path.join(dir, "claim.json"), typeof claim === "string" ? claim : JSON.stringify(claim));
  fs.writeFileSync(path.join(dir, "run.txt"), output);
  const r = spawnSync("python3", ["-I", TOOL, path.join(dir, "claim.json"), path.join(dir, "run.txt")], { encoding: "utf8" });
  fs.rmSync(dir, { recursive: true, force: true });
  return { code: r.status, out: (r.stdout + r.stderr).trim() };
}

test("tolerance claim: reproduced", () => {
  const r = check({ result: [1.0, 2.5, "ok"], tolerance: 1e-6 }, "progress...\n[1.0000001, 2.5, \"ok\"]\n");
  assert.equal(r.code, 0, r.out);
  assert.equal(r.out, "reproduced");
});

test("tolerance claim: mismatch is rejected", () => {
  const r = check({ result: 3.14159, tolerance: 1e-9 }, "3.2\n");
  assert.equal(r.code, 1);
  assert.match(r.out, /^mismatch/);
});

test("interval claim: run interval contained (exact rationals and decimals)", () => {
  // pi lies in [3.14159, 3.1416]; the run gives a tighter enclosure as p/q strings.
  const r = check({ interval: ["3.14159", "3.1416"] }, JSON.stringify({ interval: ["314159/100000", "355/113"] }) + "\n");
  assert.equal(r.code, 0, r.out);
  assert.match(r.out, /^certified: /);
});

test("interval claim: equal endpoints count as contained, bare [lo, hi] output accepted", () => {
  const r = check({ interval: ["1/3", "1/2"] }, '["1/3", "0.5"]\n');
  assert.equal(r.code, 0, r.out);
  assert.match(r.out, /^certified: /);
});

test("interval claim: run interval not contained", () => {
  // 1/3 = 0.333... is below 0.3334: the lower end sticks out by an amount no float rounding would show.
  const r = check({ interval: ["0.3334", "0.34"] }, JSON.stringify({ interval: ["1/3", "0.335"] }) + "\n");
  assert.equal(r.code, 1);
  assert.match(r.out, /^not contained/);
});

test("interval claim: a tiny exact excess is still caught", () => {
  const r = check({ interval: ["0", "1/3"] }, JSON.stringify({ interval: ["0", "0.33333333333333333334"] }) + "\n");
  assert.equal(r.code, 1);
  assert.match(r.out, /^not contained/);
});

test("interval claim: float endpoints in the output are refused", () => {
  const r = check({ interval: ["3.14", "3.15"] }, JSON.stringify({ interval: [3.141, 3.142] }) + "\n");
  assert.equal(r.code, 1);
  assert.match(r.out, /^refused: output endpoint 3.141 is not a string/);
});

test("interval claim: float endpoints in the claim are refused", () => {
  const r = check('{"interval": [0.1, "1/2"]}', JSON.stringify({ interval: ["1/5", "1/4"] }) + "\n");
  assert.equal(r.code, 1);
  assert.match(r.out, /^refused: claimed endpoint 0.1 is not a string/);
});

test("interval claim: non-rational strings and reversed intervals are refused", () => {
  assert.match(check({ interval: ["0", "1"] }, '["nan", "1"]\n').out, /^refused: .*not an exact rational/);
  assert.match(check({ interval: ["0", "1"] }, '["1/0", "1"]\n').out, /^refused: .*not an exact rational/);
  assert.match(check({ interval: ["1", "0"] }, '["1/2", "1/2"]\n').out, /^refused: claimed interval has lo > hi/);
});
