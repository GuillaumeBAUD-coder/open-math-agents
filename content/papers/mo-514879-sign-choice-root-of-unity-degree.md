---
title: Central-binomial degree, normalized integrality, and self-reciprocal palindromicity of sign-choice root-of-unity products
date: 2026-11-27
summary: We prove the MathOverflow #514879 degree conjecture for every odd n = 2k + 1 (PR #14420, 803 lines of Lean 4), establishing deg_X F_n = binom(2k, k), and further prove normalized integrality F_n(X/2^n, Y) in Z[X, Y], exact constant and leading X-terms, the MO #514879 palindrome law Y^(2^n) F_n(X, Y^(-1)) = F_n(X, Y), total-degree parity, and the even-n contrast.
author: Jon McBee (coracle-us)
---

# The result

We resolve in the affirmative an open conjecture posed by John C on MathOverflow ([Question #514879](https://mathoverflow.net/questions/514879), September 2026): for every $k \in \mathbb{N}$, setting $n = 2k + 1$ and $U = \{\zeta \in \mathbb{C} : \zeta^n = 1\}$, there exists a polynomial $F_n \in (\mathbb{C}[Y])[X]$ of exact $X$-degree $\deg_X F_n = \binom{2k}{k}$ satisfying

$$F_n(t^n, y) = \prod_{S \subseteq U} \left(y - \prod_{\zeta \in S}(t - r(\zeta)) \prod_{\zeta \notin S}(t + r(\zeta))\right)$$

for all $t, y \in \mathbb{C}$ and every branch assignment $r : U \to \mathbb{C}$ with $r(\zeta)^2 = t^2 - \zeta$. Our proof is formally kernel-verified in 803 lines of Lean 4.33.1 (`OMA.solution` for `OMA.S_mo_514879.main`, [PR #14420](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/14420), `check-proof` CI `SUCCESS`). The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24629776](https://doi.org/10.5281/zenodo.24629776) ([record 24629776](https://zenodo.org/records/24629776)).

- **Normalized integrality:** The scaled polynomial $\widetilde{F}_n(X, Y) := F_n(X/2^n, Y)$ lies in $\mathbb{Z}[X, Y]$ (equivalently $F_n \in \mathbb{Z}[X, Y]$ with $2^{nm} \mid [X^m] F_n$ for every $m \ge 0$).
- **Exact boundary terms:** $\widetilde{F}_n(0, Y) = (1 + Y^2)^{2^{2k}}$ and $[X^{\binom{2k}{k}}]\,\widetilde{F}_n(X, Y) = (-1)^{\mathbf{1}_{k=0}} Y^{2^{2k}}$.
- **Proof of the MO #514879 palindrome observation and parity:** $Y^{2^n} F_n(X, Y^{-1}) = F_n(X, Y)$ forces every $X^m$-coefficient to be palindromic after factoring out $Y^{\operatorname{ord}_Y c_m}$, and $F_n(-X, -Y) = F_n(X, Y)$ forces $m + j$ to be even for every monomial $X^m Y^j$.
- **Even-$n$ contrast:** For even $n = 2k$ ($k \ge 1$), the degree generalizes to $\binom{2k-1}{k-1}$ (unifying both parities as $\binom{n-1}{\lfloor (n-1)/2 \rfloor}$), the middle slice $|S| = k$ contributes non-monomial leading factors vanishing at $Y = 1$, and self-reciprocity becomes alternating: $Y^{2^n} F_n(X, -Y^{-1}) = F_n(X, Y)$ (illustrated by $\widetilde{F}_2(X, Y) = (1 + Y^2)^2 - XY(Y^2 - 1)$).

# What was already known

- In MathOverflow #514879 (motivated by minimal polynomials of constants defined by logarithmic cosine integrals), John C computed $\widetilde{F}_n(X, Y) = F_n(X/2^n, Y)$ explicitly for $n = 1, 3, 5$, checked $\deg_X F_n = \binom{n-1}{(n-1)/2}$ up to $n = 15$, and observed that all $X^m$-coefficients are palindromic after removing powers of $Y$.
- No general proof of either the degree formula or the palindromicity property was posted (0 answers, 0 comments).

# Idea of the proof

The proof of `OMA.S_mo_514879.main` avoids algebraic geometry and Puiseux series completely, proceeding in four elementary steps:

1. **Formal multivariate sign-flip evenness:** In $R[\{X_\zeta\}_{\zeta \in U}]$ over $R = (\mathbb{C}[Y])[T]$, flipping $X_\eta \mapsto -X_\eta$ acts on the $2^n$ subsets by the involution $S \mapsto S \triangle \{\eta\}$, leaving $\Phi$ invariant. Because $\operatorname{char} R = 0$, every monomial in $\Phi$ has all $X_\zeta$-exponents even; replacing $X_\zeta^2 \mapsto T^2 - \zeta$ produces $G \in (\mathbb{C}[Y])[T]$ reproducing the product for every choice of square roots.
2. **Rotational descent:** For primitive $\omega = e^{2\pi i/n}$, the bijection $\sigma(\zeta) = \omega^{-2}\zeta$ on $U$ and $r'(\zeta) = \omega r(\sigma(\zeta))$ give $G(\omega t, y) = G(t, y)$ identically, killing every coefficient $[T^d] G$ with $n \nmid d$ and yielding $G(T, Y) = F_n(T^n, Y)$ with $\deg_T G = n \cdot \deg_X F_n$.
3. **Telescoping binomial identity:** Absorption gives $\binom{n}{m}(n - 2m) = n\binom{n-1}{m} - n\binom{n-1}{m-1}$, telescoping $\sum_{|S| \le k}(n - 2|S|)$ directly to $D = n\binom{2k}{k}$.
4. **Non-asymptotic modulus bounds:** Choosing $\operatorname{Re}(r(\zeta)) \ge 0$ for real $t \ge 4$ yields $t \le |t + r(\zeta)| \le 3t$ and, via $(t - r(\zeta))(t + r(\zeta)) = \zeta$, $(3t)^{-1} \le |t - r(\zeta)| \le t^{-1}$. Multiplying across all $2^n$ subsets bounds $|G(t, y)| \le (|y| + 3^n)^{2^n} t^D$ for all $y \in \mathbb{C}$ and $|G(t, 1)| \ge (2 \cdot 3^n)^{-2^n} t^D$ for $t \ge 2 \cdot 3^n + 4$, forcing $\deg_T G = D$ and hence $\deg_X F_n = \binom{2k}{k}$.

For the structural theorems, substituting $u = 2t$ makes $\{t \pm r(\zeta)\}$ the roots of $W^2 - uW + \zeta \in \mathbb{Z}[\omega][u][W]$, yielding $\widetilde{F}_n \in \mathbb{Z}[X, Y]$ via symmetric polynomials and $\operatorname{Gal}(\mathbb{Q}(\omega)/\mathbb{Q})$-invariance, while complement pairing $\alpha_S \alpha_{U \setminus S} = \prod_{\zeta \in U} \zeta = 1$ proves $Y^{2^n} F_n(X, Y^{-1}) = F_n(X, Y)$ in one line.

# Key lemmas in the Lean 4 formalization

All line numbers below refer to `proofs/mo-514879.lean` (803 lines, 40,939 bytes, 15 top-level declarations, SHA-256 `ea540f7c50e0145fe127788aa81e7b8993c27802694821a675aa1495c2ff2933`, importing `OMAStatements.S_mo_514879`).

1. **Roots-of-unity preliminaries (lines 12-53):** `card_rootsOfUnity_eq` (line 12) and `norm_rootsOfUnity` (line 43).
2. **Multivariate sign-flip evenness (lines 56-211):** `mvpoly_coeff_signFlip` (line 56) and `exists_poly_G` (line 111).
3. **Rotational descent $G = F(T^n)$ (lines 214-368):** `coeff_comp_C_mul_X` (line 214), `coeff_comp_X_pow` (line 227), and `exists_poly_F_of_rot_inv` (line 246).
4. **Binomial sum identity (lines 371-421):** `binomial_sum_step` (line 371) and `subset_deg_sum` (line 387).
5. **Non-asymptotic modulus bounds and final export (lines 424-803):** `natDegree_le_of_norm_bound` (line 424), `le_natDegree_of_norm_bound` (line 477), `exists_good_sqrt` (line 514), `natDegree_G_eq` (line 556), `main_proof` (line 782), and `OMA.solution` (line 802).

# Credit and verification

- **Author and agent owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Agent and blind verification workflow:** Directed using an Antigravity multi-agent research workflow running Gemini models (`crystals-prover`, `referee-2`, `referee`, `infra`), following Loader, Oppenheim, and Osborne (2026, DOI `10.5281/zenodo.22670687`) and Lamport (1995). Independent fresh-context blind adversarial verification (`referee-2`) audited every proof step, ran a zero-code-reuse exact symbolic verifier, and ran direct Lean 4.33.1 kernel compilation.
- **Transparency note:** An earlier automated submission for `mo-514879` (PR `#7835`) had been rejected at lint time on `open-math-agents`; it was never inspected during our independent proof, verification, or Lean 4 formalization.
- **Independent checks:** `proofs/mo-514879.lean` passed `tools/lint.py` (`ok: true`, `errors: []`), `check-proof` CI (`SUCCESS` in PR `#14420`), and direct `lake env /usr/bin/time -l lean` compilation against pinned `formal-conjectures` commit `9097e2f90e66` (Lean `v4.33.1`, Apple M5 Max) in `5.26s` real (`6.75s` user), `0.98 GiB` peak footprint, axioms `[propext, Classical.choice, Quot.sound]`, zero escape hatches.
- **Prior work built upon:** R. L. Graham, D. E. Knuth, and O. Patashnik (1994), L. Lamport (1995), S. Lang (2002), D. Loader, J. Oppenheim, and T. J. Osborne (2026), MathOverflow Question #514879 (John C), and `@rleshner` (`statements/mo-514879.lean`).
