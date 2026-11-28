---
title: Closed-form evaluation of product-Cauchy integer-lattice sums via finite character orthogonality and Chebyshev polynomials
date: 2026-11-27
summary: We prove the MathOverflow #484639 conjecture in full generality (PR #18266, 1,375 lines of Lean 4), expressing every product-Cauchy sum over a full-rank integer lattice V Z^n (d = |det V|) via an explicit integer Chebyshev polynomial P_V(cosh(pi/d)), establish its universal structural invariants, strict uniqueness, and one-parameter lambda > 0 extension, and classify all 14 index-(2,3,4) sublattices of Z^2.
author: Jon McBee (coracle-us)
---

# The result

We resolve in the affirmative an open conjecture posed on MathOverflow ([Question #484639](https://mathoverflow.net/questions/484639), December 2024): for every dimension $n \ge 1$ and every nonsingular integer matrix $V \in M_n(\mathbb{Z})$ with $d := |\det V| \in \mathbb{N}_{>0}$, the product-Cauchy lattice sum $S(V) := \sum_{a \in \mathbb{Z}^n} \prod_{j=0}^{n-1} (1 + (Va)_j^2)^{-1}$ admits the exact closed-form evaluation

$$S(V) = \frac{\pi^n}{\sinh^n(\pi)\, d}\, P_V\!\left(\cosh\!\left(\frac{\pi}{d}\right)\right)$$

with the explicit integer Chebyshev polynomial

$$P_V(X) := \sum_{r \in H^\perp(V)} \prod_{j=0}^{n-1} T_{|d - 2r_j|}(X) \in \mathbb{Z}[X], \qquad H^\perp(V) := \left\{r \in \{0, \dots, d-1\}^n : d \mid V^T r\right\},$$

where $|H^\perp(V)| = d$ and $T_m \in \mathbb{Z}[X]$ is the $m$-th Chebyshev polynomial of the first kind. Our proof is formally kernel-verified in 1,375 lines of Lean 4.33.1 (`OMA.solution` for `OMA.S_mo_484639.main`, [PR #18266](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18266), `check-proof` CI `SUCCESS`). The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24629767](https://doi.org/10.5281/zenodo.24629767) ([record 24629767](https://zenodo.org/records/24629767)).

- **Universal structural invariants and uniqueness:** For every nonsingular $V \in M_n(\mathbb{Z})$ ($d = |\det V| \ge 1$), $\deg P_V = nd$, $\operatorname{lc}(P_V) = 2^{n(d-1)}$, $P_V(-X) = (-1)^{nd} P_V(X)$, $P_V(1) = d$, $P_V$ is invariant under right-multiplication by $\mathrm{GL}_n(\mathbb{Z})$ and left-multiplication by the hyperoctahedral group $B_n = \{\pm 1\}^n \rtimes S_n$, and direct sums satisfy the Chebyshev composition law $P_{V_1 \oplus V_2}(X) = P_{V_1}(T_{d_2}(X)) P_{V_2}(T_{d_1}(X))$. By the Gelfond-Schneider transcendence of $e^\pi$, $\cosh(\pi/d)$ is transcendental, making $P_V \in \mathbb{Q}[X]$ strictly unique.
- **One-parameter $\lambda > 0$ universality and explicit families:** The identical polynomial $P_V$ evaluates $S_\lambda(V) := \sum_{a \in \mathbb{Z}^n} \prod_{j=0}^{n-1} (\lambda^2 + (Va)_j^2)^{-1} = \frac{\pi^n}{\lambda^n \sinh^n(\pi\lambda)\, d} P_V(\cosh(\pi\lambda/d))$ for every $\lambda > 0$, specializing to $P_{[d]}(X) = X U_{d-1}(X)$ in $n = 1$ and $P_{D_n}(X) = (2X^2 - 1)^n + 1$ for the $n$-dimensional checkerboard lattice $D_n$.
- **Complete 2D index-$(2, 3, 4)$ classification:** All $3 + 4 + 7 = 14$ Hermite normal forms of index $d \in \{2, 3, 4\}$ in $\mathbb{Z}^2$ collapse into $2 + 2 + 4 = 8$ $B_2$-orbits and $8$ distinct Chebyshev polynomials, recovering all four MathOverflow #484639 examples coefficient-for-coefficient.

# What was already known

- For $n = 1$ ($\Lambda = d\mathbb{Z}$), the classical cotangent series gives $S([d]) = \frac{\pi}{d}\coth(\pi/d)$; for $d = 1$ ($\Lambda = \mathbb{Z}^n$), the product factors directly into $(\pi\coth\pi)^n$.
- In MathOverflow #484639, the proposer verified four $2$-dimensional lattices by calculator ($d = 2$: $\{4x^4 - 2x^2, 4x^4 - 4x^2 + 2\}$; $d = 3$: $16x^6 - 24x^4 + 11x^2$ for $\{(4,1)^T, (1,1)^T\}$; $d = 4$: $64x^8 - 128x^6 + 88x^4 - 24x^2 + 4$ for $\{(3,1)^T, (2,2)^T\}$), noted that $n \ge 3$ was intractable by hand, and posted an unaccepted self-attempt via formal Dirac-comb manipulations explicitly left incomplete.

# Idea of the proof

The proof is completely elementary and avoids $n$-dimensional Poisson summation, tempered distributions, and Pontryagin duality:

1. **Hermite upper-triangularization over $\mathbb{Z}$:** Unimodular column operations (row-by-row Euclidean reduction from bottom row $n-1$ up to row $0$) construct $T = VU$ with $U \in \mathrm{GL}_n(\mathbb{Z})$, $T$ upper-triangular, and $t_i := T_{i,i} > 0$, preserving $V\mathbb{Z}^n = T\mathbb{Z}^n$, $d = \prod_i t_i$, and $H^\perp(V) = H^\perp(T)$.
2. **Backwards-peeling character orthogonality:** For prefix products $P_m = \prod_{j < m} t_j$ and prefix solution sets $H_m \subseteq \{0, \dots, d-1\}^m$, induction establishes $d \mid P_m r_j$, forcing $t_m \mid \sum_{j < m} T_{j,m} r_j$ and yielding an exact $t_m$-to-$1$ fiber bijection $H_{m+1} \simeq H_m \times \mathrm{Fin}\, t_m$. Finite geometric root-of-unity summation then peels one coordinate at a time to prove $\sum_{r \in H^\perp} \exp(\frac{2\pi i}{d} r \cdot k) = d \cdot \mathbf{1}_{k \in T\mathbb{Z}^n}$ and $|H^\perp| = d$.
3. **1D Fourier factorization and Chebyshev collapse:** Injectively reindexing $S(V)$ over $\mathbb{Z}^n$, inserting the finite character indicator, interchanging the finite sum over $H^\perp$ with the absolutely summable $n$-fold lattice series, and factoring into $n$ copies of the $1$-dimensional Fourier series $\sum_{m \in \mathbb{Z}} e^{2\pi i m x}/(1 + m^2) = \frac{\pi}{\sinh\pi}\cosh(\pi(1 - 2x))$ on $\mathbb{R}/\mathbb{Z}$ evaluates each factor at $x_j = r_j/d$ to $\frac{\pi}{\sinh\pi} T_{|d-2r_j|}(\cosh(\pi/d))$ via $T_m(\cosh x) = \cosh(mx)$.

# Key lemmas in the Lean 4 formalization

All line numbers below refer to `proofs/mo-484639.lean` (1,375 lines, 67,983 bytes, 36 top-level declarations, SHA-256 `ddba42614b4eb1d3b731216676242e2632688d177188f91e7498c2ee7c61009e`, importing `OMAStatements.S_mo_484639`).

1. **Chebyshev hyperbolic identity (lines 20-46):** `chebyshev_T_eval_cosh` (line 20).
2. **1D Fourier series on `AddCircle (1 : ℝ)` (lines 49-282):** `summable_one_div_one_add_sq_nat` (line 49), `summable_one_div_one_add_sq_int` (line 58), `intervalIntegral_cexp_mul` (line 65), `cexp_two_pi_I_mul_int` (line 80), and `tsum_exp_div_one_add_sq` (line 85).
3. **Hermite upper-triangularization over $\mathbb{Z}$ (lines 286-666):** `ColEquiv` (line 286), `colEquiv_refl` (line 289), `colEquiv_trans` (line 292), `colEquiv_det_natAbs` (line 298), `colEquiv_range_mulVec` (line 306), `swapColMat` (line 317), `negColMat` (line 337), `addColMat` (line 354), `exists_nonzero_prefix_of_det_ne_zero` (line 439), `eliminate_row` (line 478), and `exists_upperTriangular_hermite` (line 629).
4. **Backwards-peeling character orthogonality (lines 670-1137):** `geom_sum_roots_unity` (line 670), `diagNat` (line 719), `prefixProd` (line 732), `HPrefix` (line 764), `hPrefix_dvd_invariant` (line 770), and `sum_char_HPrefix` (line 820).
5. **Product factorization and final theorem (lines 1141-1375):** `finSuccFunEquiv` (line 1141), `summable_and_tsum_fin_prod` (line 1147), `mulVec_injective_of_det_ne_zero` (line 1193), `main_proof` (line 1213), and `OMA.solution` (line 1374).

# Credit and verification

- **Author and agent owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Agent and blind verification workflow:** Directed using an Antigravity multi-agent research workflow running Gemini models (`oeis-hunter`, `referee-2`, `referee`, `infra`), following Loader, Oppenheim, and Osborne (2026, DOI `10.5281/zenodo.22670687`) and Lamport (1995). Independent fresh-context blind adversarial verification (`referee-2`) audited every proof step, ran a zero-code-reuse exact/50-digit Decimal verifier, and ran direct Lean 4.33.1 kernel compilation.
- **Independent checks:** `proofs/mo-484639.lean` passed `tools/lint.py` (`ok: true`, `errors: []`), `check-proof` CI (`SUCCESS` in PR `#18266`), and direct `lake env /usr/bin/time -l lean` compilation against pinned `formal-conjectures` commit `9097e2f90e66` (Lean `v4.33.1`, Apple M5 Max) in `6.84s` real (`8.23s` user), `1.01 GiB` peak footprint, axioms `[propext, Classical.choice, Quot.sound]`, zero escape hatches.
- **Prior work built upon:** C. Hermite (1851), A. O. Gelfond (1934), A. Baker (1975), L. Lamport (1995), J. C. Mason and D. C. Handscomb (2003), E. M. Stein and R. Shakarchi (2003), D. Loader, J. Oppenheim, and T. J. Osborne (2026), MathOverflow Question #484639, and `@Dugongue` (`statements/mo-484639.lean`, PR `#11897`).
