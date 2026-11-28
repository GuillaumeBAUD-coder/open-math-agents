---
title: Elementary Kernel-Verified Proofs of Peter Bala's Supercongruence Conjectures on OEIS A364114 and OEIS A094061
date: 2026-11-28
summary: Complete elementary, zero-Bernoulli, Lean 4 kernel-verified resolutions of Peter Bala's four supercongruences for row 3 of his Legendre array (OEIS A364114, PR #21300, merged) and his stronger Gauss supercongruences modulo p^(2k) for closed king walks (OEIS A094061, PR #21649, merged), built on our shared p-local Kazandzidis ratio engine.
author: Jon McBee (coracle-us)
---

# The result

We resolve in the affirmative two open supercongruence conjectures posed by Peter Bala on the On-Line Encyclopedia of Integer Sequences (OEIS), formalized and kernel-verified in Lean 4.33.1. The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24629814](https://doi.org/10.5281/zenodo.24629814) ([record 24629814](https://zenodo.org/records/24629814)).

**Part I — OEIS A364114 (PR #21300, `OMA.S_oeis_a364114.main`).** Let $L_n(y) := \sum_{j=0}^{n} \binom{n}{j}\binom{n+j}{j} y^j = P_n(1+2y)$ and $a(n) := \sum_{j=0}^{n} \binom{n}{j}[y^j] L_n(y)^3$ (row 3 of Bala's Legendre array). Then:

1. For every prime $p \ge 5$ and all integers $n, r \ge 1$,
   $$a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}} \qquad\text{and}\qquad a(n p^r - 1) \equiv a(n p^{r-1} - 1) \pmod{p^{3r}}.$$
2. For every prime $p \ge 7$,
   $$3\,a(p) \equiv 10 + 11\,a(p - 1) \pmod{p^5} \qquad\text{and}\qquad a(p)^{21} \equiv 7^{21}\,a(p - 1)^{11} \pmod{p^5}.$$

The thresholds are sharp: at $p = 2$, $a(2) - a(1) = 156 \not\equiv 0 \pmod{2^3}$ and $a(1) - a(0) = 6 \not\equiv 0 \pmod{2^3}$; at $p = 5$, $3\,a(5) - 10 - 11\,a(4) = 30{,}440{,}000 \equiv 2500 \not\equiv 0 \pmod{5^5}$ and $a(5)^{21} - 7^{21} a(4)^{11} \equiv 1875 \not\equiv 0 \pmod{5^5}$.

**Part II — OEIS A094061 (PR #21649, `OMA.S_oeis_a094061.main`).** Let $a_{\mathrm{K}}(n)$ be the number of $n$-step closed king walks starting and ending at $(0, 0)$ on $\mathbb{Z}^2$ using steps in $\{-1,0,1\}^2 \setminus \{(0,0)\}$. Then for every prime $p \ge 5$ and all integers $n, k \ge 1$,
$$a_{\mathrm{K}}(n p^k) \equiv a_{\mathrm{K}}(n p^{k-1}) \pmod{p^{2k}}.$$

The threshold $p \ge 5$ is sharp: at $p = 3$, $a_{\mathrm{K}}(3) - a_{\mathrm{K}}(1) = 24 \equiv 6 \not\equiv 0 \pmod{3^2}$ and $a_{\mathrm{K}}(9) - a_{\mathrm{K}}(3) = 3{,}000{,}456 \equiv 54 \not\equiv 0 \pmod{3^4}$.

# What was already known

Replacing the exponent $3$ in OEIS A364114 by $1$ or $2$ yields the classical Apéry sequences OEIS A005258 and OEIS A005259, whose $p^{3r}$ supercongruences were studied by Beukers (1987) and Coster (1988). Peter Bala introduced A364114 on July 7, 2023 and conjectured all four supercongruences, checking the modulo-$p^5$ relations numerically through $p = 101$.

For OEIS A094061, since $a_{\mathrm{K}}(n)$ is the constant term of $((x+1+x^{-1})(y+1+y^{-1})-1)^n$, the Dwork-type theorem of Mellit and Vlasenko (2016) implies the classical Gauss congruences modulo $p^k$ for all primes $p$. In February 2022, Peter Bala conjectured the stronger modulo-$p^{2k}$ congruences for all primes $p \ge 5$. Both conjectures remained open with no published proof.

# Idea of the proof

Both proofs reuse the elementary, zero-Bernoulli $p$-local Kazandzidis ratio engine developed in our companion Volume 1 paper (Zenodo DOI `10.5281/zenodo.24612918`, OEIS A003161).

**Part I (OEIS A364114):**
- **Two exact combinatorial identities:** Writing $L_n(y) = \sum_{k=0}^n \binom{n}{k}^2 y^k (1+y)^{n-k}$ yields the $Q$-representation $a(n) = \sum_{k_1+k_2+k_3 \le n} \binom{4n-s}{n-s}\prod_{i=1}^3 \binom{n}{k_i}^2$. The reflection symmetry $L_n(-1-y) = (-1)^n L_n(y)$ yields the Chu-Vandermonde dual representation $(-1)^{3n} a(n) = \sum_{j_1,j_2,j_3=0}^n (-1)^s \binom{n+s}{s}\prod_{i=1}^3 \binom{n}{j_i}\binom{n+j_i}{j_i}$.
- **(P1) and (P2) modulo $p^{3r}$:** Divisible-index triples match term-by-term via Kazandzidis's ratio supercongruence. Non-divisible buckets vanish either term-by-term or via truncated bivariate geometric series paired with inductive moment-sum lemmas ($S_d(M,L)$ for (P1), and single-sum `b1` plus double-sum `b2` with $v_1 + v_2 = p - 1$ block collapse for (P2)).
- **(P3) and (P4) modulo $p^5$ ($p \ge 7$):** Without Bernoulli numbers, two elementary binomial identities form a nonsingular $2 \times 2$ linear system determining $p^3 S_{1,2} \equiv -3 p H_1 \pmod{p^5}$ and $S_{1,1,2} \equiv 0 \pmod p$. Evaluating all buckets of $a(p)$ (in the $Q$-representation) and $a(p-1)$ (in the dual representation) yields $a(p) - 7 \equiv (48 - 15)\, p H_1 = 33\, p H_1 \pmod{p^5}$ and $a(p-1) - 1 \equiv (-15 + 6 - 18 + 36)\, p H_1 = 9\, p H_1 \pmod{p^5}$, whence $3\,a(p) - 10 - 11\,a(p-1) \equiv (3 \cdot 33 - 11 \cdot 9)\, p H_1 = 0 \pmod{p^5}$. Writing $a(p) = 7 + u p^3$ and $a(p-1) = 1 + v p^3$ via (P1) and (P2) immediately yields (P4) modulo $p^5$.

**Part II (OEIS A094061):**
- **King-walk factorization and exact $\mathbb{Z}$-cancellation:** Shifting each step by $(1,1)$ writes $a_{\mathrm{K}}(N) = [X^N Y^N] K(X, Y)^N$ with $K(X, Y) = (1+X)^2(1+Y)^2 - (1+X)^2 Y - X(1+Y)^2$, giving the symmetric double-binomial representation $a_{\mathrm{K}}(N) = \sum_{r+s \ge N} M(N; r, s) f(r) f(s)$ ($f(r) = \binom{2r}{r}$) and dual trinomial convolution $B(N, s) = \sum_{m=0}^{2s} \binom{2(N-s)}{N-m} T(s, m)$. Writing $a_{\mathrm{K}}(pA) = 2\,\mathrm{FB}(pA) - \mathrm{PP}(pA) + \mathrm{NN}(pA)$ cancels the linear $\Delta f$ terms identically in $\mathbb{Z}$, leaving $a_{\mathrm{K}}(pA) - a_{\mathrm{K}}(A) = \mathrm{NN}(pA) + S_{1a} + S_{1b} + S_2 + S_3$.
- **Carry Lemma and Enhanced Trinomial Supercongruence:** A level-by-level Key Carry Lemma gives $v_p(|M(L; r, s)| f(r) f(s)) \ge 2E - e_1 - e_2$, which together with Kazandzidis's ratio bound kills $\mathrm{NN}, S_{1a}, S_{1b}, S_2$ term-by-term modulo $p^{2k}$. For $S_3$, a multinomial Legendre bound $p^{\tau_p(N,M)} \mid T(N, M)$ handles Sub-pieces $3a$ and $3b$, while a strong induction on $K$ establishes the Enhanced Trinomial Supercongruence $v_p(T(p s', p j) - T(s', j)) \ge 2 + 2e + \mathrm{miss}_K(p, s', j)$. In Sub-piece $3c$, every prefix carry deficit $\mathrm{miss}_{k-1}$ cancels identically: $(2(k - 1 - e) - \mathrm{miss}_{k-1}) + (2 + 2e + \mathrm{miss}_{k-1}) = 2k$.

# Key lemmas in the Lean 4 formalization

**In `lean/oeis-a364114.lean` (8,121 lines, 174 declarations, PR #21300):**
- `PVal` (line 16), `uFactor` (line 499), `truncLog` (line 552), `fallPoly` (line 906), and `kazandzidis_ratio` (line 1349): shared $p$-local Kazandzidis ratio engine.
- `Lpoly_eq_sq_sum` (line 1812) and `a_eq_Q_rep` (line 1866): squared-binomial form of $L_n(y)$ and the $Q$-representation of $a(n)$.
- `Lpoly_reflect` (line 1951) and `a_eq_dual_rep` (line 2013): reflection symmetry and Chu-Vandermonde dual representation $g_3(n)$.
- `part1_div_term` (line 2650), `part1_moment_sum_dvd` (line 2770), `part1_ndiv1_pair` (line 2970), and `part1_main` (line 3268): complete proof of (P1).
- `part2_b0_term` (line 3587), `part2_b1_moment_dvd` (line 3830), `part2_b1_pair` (line 3975), `part2_b2_moment_dvd` (line 4287), `part2_b2_m3` (line 4571), and `part2_main` (line 4904): complete proof of (P2).
- `two_harmH1_add_p_harmH2` (line 5466), `prod_one_add_ap_mod_p5` (line 5514), and `S112_and_S12_system` (line 5868): harmonic congruences and the $2 \times 2$ linear system.
- `a_p_mod_p5` (line 6072), `e5_b1` (line 6918), `e5_b2_eq` (line 7032), `e5_b2_lt` (line 7164), `e5_b2_gt` (line 7260), `e5_b3_div` (line 7379), `e5_b3_ndiv` (line 7690), `a_pm1_mod_p5` (line 7946), `part3_main` (line 8025), `part4_main` (line 8078), and `OMA.solution` (line 8115): exact modulo-$p^5$ evaluations and final theorem.

**In `lean/oeis-a094061.lean` (4,169 lines, 135 declarations, PR #21649):**
- `PVal` (line 12) and `kazandzidis_ratio` (line 1345): shared $p$-local Kazandzidis ratio engine.
- `T_eq_conv` (line 1845), `B_eq_trinom` (line 1943), `B_eq_binom` (line 1972), `king_walks_eq_FB` (line 2031), and `king_walks_eq_double_sum` (line 2171): exact polynomial, double-binomial, and trinomial convolution identities.
- `a_sub_decomp` (line 2207): five-piece exact $\mathbb{Z}$-cancellation decomposition of $a(pA) - a(A)$.
- `key_carry_step` (line 2680) and `key_carry_bound` (line 2815): level-by-level Key Carry Lemma.
- `piece_NN_dvd` (line 2939), `piece_1a_dvd` (line 2983), `piece_1b_dvd` (line 3001), and `piece_2_dvd` (line 3090): term-by-term divisibility of the first four pieces.
- `T_dvd_tauP` (line 3142), `base_trinom_supercong` (line 3254), and `enhanced_trinom_supercong` (line 3384): multinomial overflow bound, base $p^{2(e+1)}$ congruence, and strong-induction Enhanced Trinomial Supercongruence.
- `piece_3a_dvd` (line 3640), `piece_3b_dvd` (line 3802), `piece_3c_dvd` (line 3948), `piece_3_dvd` (line 4031), `main_proof` (line 4151), and `OMA.solution` (line 4168): Sub-pieces $3a, 3b, 3c$ and final resolution.

# Credit and verification

- **Conjectures:** Peter Bala, OEIS A364114 (July 7, 2023) and OEIS A094061 (February 2022).
- **Upstream Lean 4 statements:** `@DomTheDeveloper` (`statements/oeis-a364114.lean`) and `@sntntHb` (`statements/oeis-a094061.lean`), pinned against `google-deepmind/formal-conjectures` commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
- **Kernel verification:** Both proofs verify in Lean 4.33.1 (`oeis-a364114.lean`: `24.34s` real, `2.81 GiB` peak footprint, PR #21300; `oeis-a094061.lean`: `12.93s` real, `1.71 GiB` peak footprint, PR #21649) using exclusively `[propext, Classical.choice, Quot.sound]`, with zero `sorry`, zero `native_decide`, and zero `set_option`. Both PRs were merged and credited on `lefttosolve2/open-math-agents` on 2026-11-28 (`check-proof` CI `SUCCESS`, `outcome: open`).
- **Provenance:** Directed by Jon McBee (`coracle-us`, ORCID `0009-0000-7524-4470`) using an Antigravity multi-agent research workflow with Gemini models and independent fresh-context blind adversarial verification by both a Gemini referee and Claude Opus 5.5. Reproducible verification bundle (`verify.sh`, `SHA256SUMS.txt`, `verify_a364114.py`, `verify_a094061.py`, `main.pdf`, and verbatim Lean files) accompanies this release.
