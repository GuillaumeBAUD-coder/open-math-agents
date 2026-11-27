---
title: Kernel-Verified Disproofs of Three Open Conjectures of Zhi-Wei Sun Without native_decide
date: 2026-11-27
summary: Pure-kernel Lean 4 disproofs of OeisA261876.conjecture_3 (n = 56271), OeisA234360.conjecture_4 (n = 3998), and OeisA234360.conjecture_1 (n = 4722) via two-pointer four-square scanning, windowed GMP Fermat reflection, midpoint splitting, and ECM witness harvesting.
author: Jon McBee (coracle-us) with Gemini agents (oeis-hunter, lean-a92243, referee, referee-2, infra)
---

This paper documents three machine-checked disproofs of open number-theoretic conjectures of Zhi-Wei Sun from Google DeepMind's `formal-conjectures` repository (pinned commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Lean `v4.33.1`). All three disproofs are verified entirely inside the Lean 4 kernel by pure definitional reduction (`rfl`), with zero `native_decide`, zero `sorry`, and axioms strictly within `[propext, Classical.choice, Quot.sound]`. The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24592749](https://doi.org/10.5281/zenodo.24592749) ([record 24592749](https://zenodo.org/records/24592749), concept DOI `10.5281/zenodo.24592748`).

- `OeisA261876.conjecture_3` is refuted at triple `(42, 98, 14)` and `n = 56271` ([PR #2951](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2951), `OeisA261876.conjecture_3.lean`, `473` lines, `19,867` bytes).
- `OeisA234360.conjecture_4` is refuted at `n = 3998` ([PR #3140](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3140), `OeisA234360.conjecture_4.lean`, `1,629` lines, `74,367` bytes).
- `OeisA234360.conjecture_1` is refuted at `n = 4722` ([PR #3375](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3375), `OeisA234360.conjecture_1.lean`, `2,721` lines, `479,021` bytes).

Every counterexample above is also the exact smallest counterexample to its respective conjecture.

# Prior Work and Mathematical Context

In [OEIS A261876](https://oeis.org/A261876) and [arXiv:1604.06723](https://arxiv.org/abs/1604.06723), Zhi-Wei Sun proposed refinements of Lagrange's four-square theorem requiring an auxiliary polynomial in the coordinates to be a square. In [OEIS A234360](https://oeis.org/A234360), Sun conjectured that several exponential expressions involving Euler's totient $\varphi(n - k)$ always produce at least one prime for $0 < k < n$.

In [arXiv:2608.11941](https://arxiv.org/abs/2608.11941), T. Adamczewski disproved one sibling in each file: `OeisA261876.conjecture_2` (at $n = 69383$) and `OeisA234360.conjecture_2` (at $n = 1408$). Neither witness refutes the remaining open conjectures: at $n = 1408$, `OeisA234360.conjecture_1` holds via $k = 1402$ ($1403^2 + 1402 = 1969811$, prime) and `OeisA234360.conjecture_4` holds for all $4 \le n \le 3997$.

# 1. Disproof of `OeisA261876.conjecture_3` at $n = 56271$

## Statement

The target `OeisA261876.conjecture_3` (`FormalConjectures/OEIS/261876.lean`) asserts that for every triple $t = (c_1, c_2, c_3)$ in the seven-element set `OeisA261876.triples` and every $n \in \mathbb{N}$, there exist $x, y, z, w \in \mathbb{N}$ such that $n = x^2 + y^2 + z^2 + w^2$ and

$$Q_t(x, y, z) = xy(c_1 x^2 + c_2 y^2 + c_3 z^2)$$

is a perfect square. Our theorem `OMA.disproof` in `OeisA261876.conjecture_3.lean` specializes to $t = (42, 98, 14) \in \text{triples}$ (proved by `by decide`) and $n = 56271$, and applies `OeisA261876Disproof.no_rep_56271`.

## Proof Idea and Key Lean Lemmas

1. **Mod-8 parity reduction (`sq_mod8_cases`, `no_rep_56271`, `noSq24_of_even_three_odd`):** Since $56271 \equiv 7 \pmod{8}$ and every square satisfies $a^2 \bmod 8 \in \{0, 1, 4\}$, any four-square decomposition of $56271$ has exactly one coordinate $e \equiv 2 \pmod{4}$ (so $e = 4t + 2$ with $0 \le t \le 58$) and three odd coordinates. Sorting the three odd coordinates into $1 \le u \le v \le s$ and applying the four-element permutation symmetry lemmas (`NoSq6_swap12`, `NoSq6_swap23`, `NoSq24_swap12`, `NoSq24_swap23`, `NoSq24_swap34`) reduces all $37516$ ordered representations to $1588$ unordered quadruples, checking all $24$ ordered triples drawn from $\{e, u, v, s\}$ because $42 \ne 98$.
2. **Two-pointer sum-of-two-squares scanner (`checkE`, `checkU`, `checkVS`, `checkE_sound`, `checkU_sound`, `checkVS_sound`):** For each fixed $e$ and odd $u$ with $3 u^2 \le 56271 - e^2$, let $\mathrm{rem} = 56271 - e^2 - u^2$. The scanner starts at $v = u$ and odd $s_0 = \mathrm{sStart}(\mathrm{rem})$ (certified odd by `sStart_odd` and satisfying $(s_0 + 1)^2 > \mathrm{rem}$), advancing $v \leftarrow v + 2$ when $v^2 + s^2 < \mathrm{rem}$ and $s \leftarrow s - 2$ when $v^2 + s^2 > \mathrm{rem}$.
3. **Structural bracketed non-square test (`notSq`, `notSq_sound`):** Rather than reducing `Nat.sqrt` on $11$-digit numbers in the kernel, `notSq` first rejects $v \equiv 0 \pmod{7}$ with $v \not\equiv 0 \pmod{49}$ (eliminating most candidates since $14 \mid Q$) and quadratic non-residues modulo $16$, $9$, and $5$, then falls back to a $20$-step binary search `isqrtBin` whose output $r$ only needs to satisfy the two inequalities $r^2 < v < (r + 1)^2$.
4. **Parallel kernel check (`checkE_t_0` through `checkE_t_19`, `checkE_blk_20` through `checkE_blk_56`, `checkE_all`):** All $59$ values of $t$ are verified across $35$ load-balanced pure-`rfl` theorems in `80.37s` real (`183.66s` user, `2.79 GiB` direct `lean` peak memory footprint on Apple M5 Max).

# 2. Disproof of `OeisA234360.conjecture_4` at $n = 3998$

## Statement

The target `OeisA234360.conjecture_4` (`FormalConjectures/OEIS/234360.lean`) asserts that for every $n > 3$ there exist $0 < k < n$ and a prime $p$ satisfying

$$(p + 1)^2 = k^2 (k + 1)^{\varphi(n - k)}.$$

Our theorem `OMA.disproof` in `OeisA234360.conjecture_4.lean` specializes to $n = 3998$ and applies `OeisA234360Disproof.no_witness_3998`.

## Proof Idea and Key Lean Lemmas

1. **Boundary cases $k \in \{3996, 3997\}$ (`not_sq_3997`, `not_sq_3998`, `no_witness_3998`):** Here $\varphi(1) = \varphi(2) = 1$, forcing $r^2 = 3997$ or $r^2 = 3998$, which contradicts $63^2 = 3969 < 3997 < 3998 < 4096 = 64^2$.
2. **Even-totient reduction for $1 \le k \le 3995$ (`no_witness_3998`):** For $d = 3998 - k \ge 3$, `Nat.totient_even` writes $\varphi(d) = 2 m_k$, and `Nat.pow_left_injective` uniquely forces $p = N_k := k (k + 1)^{m_k} - 1$.
3. **Certified Euler totient (`findOddFacAux_spec`, `findFac_spec`, `fastTotAux_eq`, `fastTotient_eq`):** Trial factoring up to $67$ (`findOddFacAux d 32 3`, since $67^2 = 4489 > 3997$) and recursion of depth $13$ (`fastTotAux 13 d`) certify $\mathrm{fastTotient}(d) = \varphi(d)$ for all $1 \le d \le 3997$ via `Nat.totient_mul_of_prime_of_dvd` and `Nat.totient_mul`.
4. **Modular-divisor elimination (`powModAux_eq`, `capPowAux_le`, `not_prime_of_divCheck`):** Exactly $3755$ indices are eliminated by an explicit proper divisor $3 \le q_k < 2^{48}$ checked modulo $q_k$ without constructing $N_k$, with `capPowAux` certifying $q_k < N_k$.
5. **Strict 8-bit windowed GMP Fermat elimination (`powMulAux_eq`, `powNat_eq`, `splitChunksAux_eval`, `pow2Win8_mod`, `pow2Chunk64_mod`, `pow2ModChunks64_mod`, `not_prime_of_fermat2_fail`, `not_prime_of_fermat2Fail`):** The remaining $240$ indices (up to $15684$ bits, total $1474776$ bits) are eliminated by verifying $2^{N_k - 1} \bmod N_k \ne 1$ using `powNat` (avoiding `exponentiation.threshold = 256`), 64-bit MSB-first chunking, 8-bit windowing, and strict chunk forcing `if acc' == 0 then 0 else ...`, combined across $32$ parallel Fermat buckets (`fermatBucket_0_ok` through `fermatBucket_31_ok`, `fermatBuckets_all_ok`, `inFermatBuckets_sound`) and $40$ divisor chunks (`divChunk_0_ok` through `divChunk_39_ok`, `checkDivChunk_sound`, `not_prime_all_range`). The file compiles in `111.13s` real (`257.37s` user, `2.98 GiB` direct `lean` peak memory footprint on Apple M5 Max).

# 3. Disproof of `OeisA234360.conjecture_1` at $n = 4722$

## Statement

The target `OeisA234360.conjecture_1` (`FormalConjectures/OEIS/234360.lean`) asserts that for all $n > 1$, the count `OeisA234360.a n` of integers $k \in \{1, \dots, n - 1\}$ for which

$$N_k = (k + 1)^{\varphi(n - k)} + k$$

is prime satisfies $0 < a(n)$. Our theorem `OMA.disproof` in `OeisA234360.conjecture_1.lean` specializes to $n = 4722$ and applies `OeisA234360C1Disproof.no_witness_4722`, which extracts a hypothetical prime witness via `Finset.card_pos` and refutes it with `not_prime_all_range`.

## Kernel Engineering Improvements and Key Lean Lemmas

The initial certificate for $n = 4722$ contained $648$ Fermat base-2 composites totaling $9510823$ bits (maximum $38052$ bits at $k = 643$). Four upgrades brought the pure-kernel Lean proof comfortably within CI's `512 KiB` source limit, `30 min` timeout, and GitHub `ubuntu-latest` runner memory capacity:

1. **ECM witness harvesting:** Running trial division, Pollard $p - 1$, Williams $p + 1$, and 14-thread Suyama Montgomery ECM Stage 1 and Stage 2 harvested $256$ additional divisors ($\le 103$ bits)—including the $63$-bit divisor $7194908883887750191$ of the $38052$-bit case $k = 643$—expanding the divisor set to $4329$ cases (`not_prime_of_divCheck`, `fastTotient_eq` extended to $4721$ via `findOddFacAux d 35 3`) and shrinking the Fermat set to $392$ cases totaling $5818889$ bits (max $38028$ bits at $k = 583$).
2. **Single-occurrence squaring and warning-free bounds (`pow2Win8Pow`, `sq_mod_step`, `pow2Win8Pow_mod`, `pow2Chunk64Pow_mod`, `pow2ModChunks64Pow_mod`, `cand_bound_gen`, `cand_sub_one_lt`):** Replacing `(acc * acc) % n` with `(acc ^ 2) % n` eliminates WHNF AST duplication while staying below `exponentiation.threshold = 256`, and abstracting exponent literals into variables in `cand_bound_gen` achieves zero compiler warnings.
3. **Midpoint checkpoint splitting (`evalChunks_append`, `fermat2Mid1`, `fermat2Mid2`, `not_prime_of_fermat2Mid`):** All $42$ largest remaining Fermat cases ($28154$ to $38028$ bits) are split at the midpoint chunk $M$ via a hexadecimal checkpoint `mid_<k>` (for example `mid_583`, `fmid_583_1`, `fmid_583_2`), verified across $84$ independent half-length `rfl` theorems that cut per-theorem peak working memory from $1.56\,\mathrm{GiB}$ down to $\approx 440\,\mathrm{MB}$.
4. **Linear-time combination (`midFermat_cons_sound`, `midFermat_all_sound`, `midFermat_sound`, `fb_ok`, `fermatBuckets_all_ok`, `checkDivChunk_sound`, `not_prime_all_range`):** Replacing `simp` over long bucket lists with linear term combinators and a depth-6 binary dispatch over $48$ divisor chunks eliminates quadratic elaboration overhead. The complete file (`467.8 KiB`) compiles with exit `0`, zero errors, zero warnings, `559.99s` real (`9.33 min`, `1521.91s` user, `4.33 GiB` direct `lean` peak footprint in independent uncontended referee verification), and verbatim axioms `[propext, Classical.choice, Quot.sound]`.

# Companion Non-Formalized Remark on `OeisA234360.conjecture_3`

In our companion Zenodo preprint ([DOI 10.5281/zenodo.24592749](https://doi.org/10.5281/zenodo.24592749)), we also report a doubly-verified exact-GMP counterexample to the fourth and final open conjecture in `FormalConjectures/OEIS/234360.lean`, namely `OeisA234360.conjecture_3` ($k (k + 1)^{\varphi(n - k)} + 1$ prime), at exact smallest $n = 7588$ ($6541$ explicit divisors $< 2^{62}$ plus $1046$ Fermat base-2 composites up to $65462$ bits; independently confirmed with zero errors by a blind second-agent GMP audit, which calibrated single-file Lean 4 CI runtime at $\approx 69$ min unpolished). Because that fourth disproof has not yet been accepted by the Lean 4 kernel, it is recorded here solely as an unformalized companion remark and is excluded from the kernel-verified claims above.

# Credit and Provenance

- **Author and project owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Archival preprint:** [Zenodo DOI 10.5281/zenodo.24592749](https://doi.org/10.5281/zenodo.24592749) ([https://zenodo.org/records/24592749](https://zenodo.org/records/24592749), concept DOI `10.5281/zenodo.24592748`).
- **Agents and models:** Multi-agent research swarm running Gemini models—`oeis-hunter` (counterexample discovery, minimality verification, Lamport proofs), `lean-a92243` (Lean 4 formalization, windowed GMP Fermat and midpoint-splitting reflection engine, Montgomery ECM factorer, manuscript), `referee` and `referee-2` (blind adversarial mathematical and Lean audits), and `infra` (pinned toolchain setup, live PR collision checks, and `tools/check.sh` dry-runs).
- **Prior work built upon:** Zhi-Wei Sun ([OEIS A261876](https://oeis.org/A261876), [OEIS A234360](https://oeis.org/A234360), [arXiv:1604.06723](https://arxiv.org/abs/1604.06723)), the Google DeepMind `formal-conjectures` authors, T. Adamczewski ([arXiv:2608.11941](https://arxiv.org/abs/2608.11941)), and the Mathlib and Lean 4 communities.
