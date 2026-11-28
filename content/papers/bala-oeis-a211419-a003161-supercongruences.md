---
title: Elementary kernel-verified proofs of two open conjectures of Peter Bala on OEIS A003161 and A211419
date: 2026-11-27
summary: We give completely elementary, Lean 4 kernel-verified proofs of two open OEIS conjectures of Peter Bala: the p^(3k) supercongruence b(n p^k) = b(n p^(k-1)) (mod p^(3k)) for p >= 5 on OEIS A003161 (2,883 lines, PR #10575), proved via an elementary truncated-logarithm Kazandzidis congruence and inductive binomial-square moments, and all six factorial-ratio divisibility conjectures on OEIS A211419 (873 lines, PR #10547), proved via Legendre valuation analysis, an explicit p = 2 Extra-Bit Lemma, and a unified constructive uniform multiplier M(r).
author: Jon McBee (coracle-us)
---

# The results

We settle two open number-theoretic conjectures posed by Peter Bala on the On-Line Encyclopedia of Integer Sequences (OEIS) by completely elementary $p$-local arguments formalized in Lean 4 (`v4.33.1`) against the upstream Left to Solve (`open-math-agents`) statements. The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24612918](https://doi.org/10.5281/zenodo.24612918) ([record 24612918](https://zenodo.org/records/24612918), concept DOI `10.5281/zenodo.24612917`).

- **OEIS A003161 supercongruence (`OMA.solution` in `proofs/oeis-a003161.lean`, [PR #10575](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10575)):** Let $a(m) = \sum_{k=0}^{\lfloor m/2 \rfloor} \bigl(\binom{m}{k} - \binom{m}{k-1}\bigr)^3$ and $b(n) = a(2n - 1)$ (Peter Bala, March 20, 2023). For every prime $p \ge 5$ and all positive integers $n, k \ge 1$, $b(n p^k) \equiv b(n p^{k-1}) \pmod{p^{3k}}$.
- **OEIS A211419 six-part divisibilities (`OMA.solution` in `proofs/oeis-a211419.lean`, [PR #10547](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10547)):** Let $T(n) = \frac{(6n)!(2n)!}{(4n)!(3n)!n!}$ (Peter Bala, August 26, 2025). For all $n \ge 0$, $(n+1) \mid 5\,T(n)$, $(4n+1) \mid T(n)$, and $(6n-1) \mid T(n)$. Moreover, for every integer $r \ge 1$, the three $r$-fold products $\prod_{i=1}^{r}(n+i)$, $\prod_{i=0}^{r-1}(4n+2i+1)$, and $\prod_{i=0}^{r-1}(6n-2i-1)$ each divide $M(r)\,T(n)$ for all $n \ge 0$ with the explicit uniform positive multiplier $M(r) = \prod_{p \le 12r} p^{2r^2 + 12r + 2}$.

# What was already known

- For OEIS A003161, Gould (1974, Problem E2384) studied divisibility properties of ballot-difference power sums and Miana, Ohtsuka, and Romero (2017, `arXiv:1602.04347`) established the exact algebraic ballot cube-sum formula reducing $b(n)$ to sums of squared binomial coefficients, while Wolstenholme (1862) and Kazandzidis (1968, 1969) established foundational binomial supercongruences modulo $p^3$. Bala's March 2023 $p^{3k}$ supercongruence conjecture on A003161 (and the closely related entries A003162 and A183069) remained open.
- For OEIS A211419, integrality of $T(n)$ is a classical member of the family of integral factorial ratios classified via Legendre step functions by Bober (2009, `arXiv:0709.1977`). All six divisibility assertions (C1)-(C6) posted by Bala in August 2025 remained open conjectures on OEIS.

# Proof of the A003161 supercongruence

Define $H(n) = \sum_{r=0}^{n-1}\binom{n-1+r}{r}^2$. Via Pascal bilinear telescoping (`pascal_telescope`), a partial cubic binomial-sum identity (`ohtsuka_tauraso`), the Miana-Ohtsuka-Romero cube-sum identity (`miana_cube_sum`), and a square-moment telescope (`square_moment_telescope`), we obtain the exact reduction

$$2b(n) = \binom{2n-1}{n-1}\left(3H(n) - \binom{2n-1}{n-1}^2\right).$$

Because $p \ge 5$ is odd, it suffices to prove $\binom{2N-1}{N-1} \equiv \binom{2M-1}{M-1} \pmod{p^{3k}}$ and $H(N) \equiv H(M) \pmod{p^{3k}}$, where $N = np^k$ and $M = np^{k-1}$.

To avoid $p$-adic analysis, Dwork theory, modular forms, and Bernoulli numbers, we work exclusively in the $p$-local ring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ (`PVal`). Pairing $i$ with $p - i$ expresses each factorial block $u(x) = \prod_{i=1}^{p-1}\frac{xp+i}{i}$ as $\prod_{i=1}^{(p-1)/2}\bigl(1 + \frac{p^2 x(x+1)}{i(p-i)}\bigr)$, and the finite truncated logarithm $\operatorname{Log}_E(1 + z) = \sum_{m=1}^{E} \frac{(-1)^{m-1}}{m} z^m$ satisfies both the approximate homomorphism law modulo $p^E \mathbb{Z}_{(p)}$ (via the exact polynomial derivative $P'(X) = (-1)^{E-1} y \sum_{t=0}^{E-1} X^t(X + y + Xy)^{E-1-t}$) and injectivity on $p^2\mathbb{Z}_{(p)}$. Expressing $\sum_{j=0}^{N-1}(j(j+1))^r$ in the falling-factorial basis yields an odd polynomial $F_r \in \mathbb{Q}[X]$ with $p^{r-1} F_r \in \mathbb{Z}_{(p)}[X]$, and polynomial divisibility $bc(b+c) \mid (b+c)^t - b^t - c^t$ for every odd $t \ge 3$ gives a completely self-contained proof of the Kazandzidis ratio supercongruence

$$\frac{\binom{(b+c)p}{bp}}{\binom{b+c}{b}} - 1 \in p^{3 + v_p(b) + v_p(c) + v_p(b+c)} \mathbb{Z}_{(p)}.$$

Setting $b = c = M$ immediately proves the central binomial congruence modulo $p^{3k}$. Setting $b = r$, $c = M$ matches the divisible-index terms $j = pr$ of $H(N)$ term-by-term with $H(M)$: writing $A = \binom{Mp-1+pr}{pr}$ and $B = \binom{M-1+r}{r}$, the two integer identities $rB = M\binom{M-1+r}{r-1}$ and $(M+r)B = M\binom{M+r}{r}$ absorb both $v_p(r)$ and $v_p(M+r)$ inside $A^2 - B^2 = B^2(A/B - 1)(A/B + 1)$, yielding $v_p(A^2 - B^2) \ge 3 + 3v_p(M) \ge 3k$.

For the non-divisible indices $j = qp + s$ ($0 \le q < M$, $1 \le s \le p - 1$), absorption and the shifted binomial congruence $\binom{(M+q)p+u}{qp+u} \equiv \binom{M+q}{q} \pmod{p^k}$ give $\binom{Mp-1+qp+s}{qp+s}^2 \equiv \frac{(Mp)^2}{(qp+s)^2}\binom{M+q}{q}^2 \pmod{p^{3k}\mathbb{Z}_{(p)}}$. Expanding $(qp+s)^{-2}$ to order $k$ decouples the double sum over $q$ and $s$, and an induction on $m$ (`moment_sum_dvd`) proves $p^m \mid \sum_{q=0}^{np^m-1}\binom{np^m+q}{q}^2$ and $p^{m+1} \mid p^d \sum_{q=0}^{np^m-1}\binom{np^m+q}{q}^2 q^d$ for all $d \ge 1$. Combined with Wolstenholme's $\sum_{s=1}^{p-1} s^{-2} \in p\mathbb{Z}_{(p)}$ at $d = 0$, every term vanishes modulo $p^{3k}$.

# Proof of the A211419 divisibilities

By Legendre's formula, the $p$-adic valuation of $T(n)$ decomposes exactly as

$$v_p(T(n)) = \sum_{e \ge 1} f(n \bmod p^e, p^e), \qquad f(r, q) = \left\lfloor\frac{6r}{q}\right\rfloor + \left\lfloor\frac{2r}{q}\right\rfloor - \left\lfloor\frac{4r}{q}\right\rfloor - \left\lfloor\frac{3r}{q}\right\rfloor.$$

Checking the $8$ intervals partitioned by denominators $2, 3, 4, 6$ shows $f(r, q) \in \{0, 1\}$, with $f(r, q) = 1$ precisely when $r/q \in [1/6, 1/4) \cup [1/2, 3/4) \cup [5/6, 1)$.

- **Conjectures C2 and C3:** Whenever $q = p^e \mid (4n+1)$ ($q$ odd, $\ge 3$), $4(n \bmod q) + 1 = mq$ with $m \in \{1, 3\}$, placing $(n \bmod q)/q$ in $[1/6, 1/4)$ or $[1/2, 3/4)$. Whenever $q = p^e \mid (6n-1)$ ($n \ge 1$, $\gcd(q, 6) = 1$, $q \ge 5$), $6(n \bmod q) - 1 = mq$ with $m \in \{1, 5\}$, placing $(n \bmod q)/q$ in $[1/6, 1/4)$ or $[5/6, 1)$. Hence $f = 1$ at every $1 \le e \le v_p(|A|)$.
- **Conjecture C1 and the Extra-Bit Lemma:** Whenever $q = p^e \mid (n+1)$, $n \bmod q = q - 1$, and $f(q - 1, q) = 1$ for every $q \ge 2$ except $q = 4$ and $q = 5$. At $p = 5$, the factor $5$ absorbs the single miss $q = 5$ (which is sharp at $n = 4, 9, 19, 34, \dots$). At $p = 2$ with $k = v_2(n+1) \ge 2$, setting $L = \lfloor \log_2 n\rfloor$, our Extra-Bit Lemma (`extra_bit_p2`) proves that either $e_* = L + 1 > k$ places $n/2^{L+1} \in [1/2, 3/4) \cup [5/6, 1)$, or else $3 \cdot 2^{L+1} \le 4n < 4 \cdot 2^{L+1}$ and $e_* = L + 3 > k$ places $n/2^{L+3} \in [1/6, 1/4)$. This single extra bit above $k$ compensates for the missing $e = 2$ term unconditionally.
- **Conjectures C4, C5, and C6:** One unified master theorem (`uniform_prod_dvd`) proves that for any $r$ nonzero integer functions $g_0, \dots, g_{r-1}$ with pairwise gaps bounded by $B$ and large prime-power hits landing where $f(n \bmod p^{e - s(p)}, p^{e - s(p)}) = 1$ (with shift $s(3) = 1$ for C6 and $s \equiv 0$ otherwise), taking $B = 2r$ and $T_0 = 12r$ forces every prime $p > T_0$ to divide at most one factor $g_i(n)$ while every small prime $p \le T_0$ is uniformly absorbed by $E = rB + T_0 + 2 = 2r^2 + 12r + 2$, giving the explicit positive multiplier $M(r) = \prod_{p \le 12r} p^{2r^2 + 12r + 2}$.

# Key lemmas in the Lean 4 formalizations

All line numbers below refer to the two verbatim proof files against pinned `formal-conjectures` commit `9097e2f90e66` (Lean `v4.33.1`).

1. **`proofs/oeis-a003161.lean` (2,883 lines, 150,428 bytes, SHA-256 `6b5b9c0cf2e843c351d502991153b217080eff7bed37d9039676d2556706a458`, PR `#10575`):** `H` (line 17), `choose_absorb_int` (line 22), `pascal_telescope` (line 43), `ohtsuka_tauraso` (line 76), `miana_cube_sum` (line 165), `square_moment_telescope` (line 340), and `two_mul_b_eq` (line 383) establish the exact algebraic reduction of $2b(n)$.
2. **Elementary Kazandzidis toolkit in `proofs/oeis-a003161.lean` (lines 462-2186):** `PVal` (line 462), `sum_inv_sq_mod_p` (line 759), `sum_pair_inv_mod_p` (line 884), `uFactor` (line 945), `uFactor_pair` (line 948), `truncLog` (line 998), `truncLog_mul_sub` (line 1028), `truncLog_inj` (line 1308), `fallPoly` (line 1352), `power_sum_odd_poly` (line 1492), `odd_pow_sub_dvd` (line 1635), `choose_mul_p_ratio` (line 1707), `kazandzidis_ratio` (line 1795), `central_choose_supercong` (line 2033), and `H_div_term_supercong` (line 2085).
3. **Non-divisible vanishing and assembly in `proofs/oeis-a003161.lean` (lines 2193-2883):** `choose_p_shift_general` (line 2193), `choose_shift_mod_pow` (line 2275), `choose_pred_sq_pval` (line 2304), `moment_sum_dvd` (line 2409), `inv_sq_geom_series` (line 2593), `H_ndiv_supercong` (line 2704), `H_supercong` (line 2831), `main_proof` (line 2858), and `OMA.solution` (line 2882).
4. **`proofs/oeis-a211419.lean` (873 lines, 41,069 bytes, SHA-256 `9cbfc240314e6f9c4c9e7ff74a620800644b20989a118f646bd6204ee97a5b6d`, PR `#10547`):** `numNat` (line 7), `denNat` (line 10), `fStep` (line 32), `fStep_le_aux` (line 35), `fStep_eq_one_I1` (line 82), `fStep_eq_one_I2` (line 91), `fStep_eq_one_I3` (line 105), `div_step_identity` (line 119), `legendre_excess` (line 127), and `int_dvd_of_padicValNat_le` (line 151) establish the Legendre valuation framework.
5. **Direct conjuncts and unified master theorem in `proofs/oeis-a211419.lean` (lines 198-873):** `extra_bit_p2` (line 198), `fStep_pred_self` (line 240), `conj1` (line 247), `conj2` (line 397), `conj3` (line 463), `padicValNat_prod_natAbs` (line 548), `uniform_prod_dvd` (line 561), `conj4` (line 697), `conj5` (line 732), `conj6` (line 773), and `OMA.solution` (line 871).

# Credit and verification

- **Author and agent owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Agent and independent blind verification workflow:** Proof discovery (`vcdim-prover`, `lean-a92243`), Lean 4 formalization (`lean-vcdim`, `lean-a92243`), manuscript drafting (`referee`), and submission packaging (`infra`) were carried out using an Antigravity multi-agent research workflow running Gemini models, following Loader, Oppenheim, and Osborne (2026, DOI `10.5281/zenodo.22670687`) and Lamport (1995). Independent fresh-context blind adversarial verification (zero-code-reuse exact arithmetic scripts plus standalone `tools/check.sh` Lean 4.33.1 kernel runs) was performed on Claude Opus 5.5 for `oeis-a211419` (PR `#10547`) and in an independent fresh-context Gemini referee session for `oeis-a003161` (PR `#10575`) after Claude Opus 5.5 encountered API quota exhaustion.
- **Independent checks:** Both `proofs/oeis-a003161.lean` (`tools/check.sh` `verdict: accepted`, `29.68s`; `11.12s` via `lake env lean`) and `proofs/oeis-a211419.lean` (`tools/check.sh` `verdict: accepted`; `5.04s` real / `1.04 GiB` peak memory via `lake env /usr/bin/time -l lean`) passed `tools/lint.py` (`ok: true`, `errors: []`) against pinned `formal-conjectures` commit `9097e2f90e66` (Lean `v4.33.1`), depending exclusively on `[propext, Classical.choice, Quot.sound]` with zero `sorry` and zero `native_decide`.
- **Prior work built upon:** J. Wolstenholme (1862), G. S. Kazandzidis (1968, 1969), H. W. Gould (1974), L. Lamport (1995), J. W. Bober (2009), P. J. Miana, H. Ohtsuka, and N. Romero (2017), P. Bala (OEIS A003161, 2023; OEIS A211419, 2025), D. Loader, J. Oppenheim, and T. J. Osborne (2026), `@sntntHb` (`statements/oeis-a003161.lean`), and `@senamakel` (`statements/oeis-a211419.lean`).
