---
title: A universal constant upper bound on the additive VCn-dimension of convex sets in R^{n+1}
date: 2026-11-27
summary: Every convex set in R^{n+1} has additive VCn-dimension at most 2 for all n >= 2 (sharp at n = 2) and at most 3 for all n >= 1, proved via S3-invariant cubics, simultaneous chamber surgery, and a from-scratch Ky Fan Borsuk-Ulam proof in Lean 4.
author: Jon McBee (coracle-us)
---

# The result

Every convex set $C \subseteq \mathbb{R}^{n+1}$ has additive $\mathrm{VC}_n$-dimension at most $2$ for every $n \ge 2$, and at most $3$ for every $n \ge 1$. Together these results resolve all three open conjectures on convex $\mathrm{VC}_n$-dimension in Google DeepMind's `FormalConjectures/Other/VCDimConvex.lean` (pinned commit `9097e2f90e66`), verified in Lean 4 (`v4.33.1`) under `coracle-us` pull requests [PR #2797](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2797), [PR #2823](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2823), and [PR #2902](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2902) with only the standard axioms `[propext, Classical.choice, Quot.sound]`. The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24592289](https://doi.org/10.5281/zenodo.24592289) ([record 24592289](https://zenodo.org/records/24592289), concept DOI `10.5281/zenodo.24592288`).

Recall (`FormalConjecturesForMathlib.Combinatorics.Additive.VCDim`, `HasAddVCNDimAtMost`) that $C \subseteq \mathbb{R}^{n+1}$ has additive $\mathrm{VC}_n$-dimension at most $d$ if there do not exist $x : \mathrm{Fin}\, n \to \mathrm{Fin}(d+1) \to \mathbb{R}^{n+1}$ and $y : \mathcal{P}((\mathrm{Fin}(d+1))^n) \to \mathbb{R}^{n+1}$ such that, writing $p(i) = \sum_{k=0}^{n-1} x_k(i_k)$,

$$y(S) + p(i) \in C \iff i \in S$$

for every grid index $i \in (\mathrm{Fin}(d+1))^n$ and every subset $S \subseteq (\mathrm{Fin}(d+1))^n$.

- **Theorem 1 (`no_shatters_d2_n2` and `no_shatters_d2_ge3`):** For every $n \ge 2$ and every convex set $C \subseteq \mathbb{R}^{n+1}$, `HasAddVCNDimAtMost C n 2` holds (no $3^n$-element sumset grid is shattered by translates of $C$).
- **Theorem 2 (`hasAddVCNDimAtMost_three_of_convex_rn_add_one` and `OMA.solution` in PR `#2823`):** For every $n \neq 0$ and every convex $C \subseteq \mathbb{R}^{n+1}$, `HasAddVCNDimAtMost C n 3` holds.
- **Corollary (`OMA.solution` in PR `#2902`):** `exists_exponential_bound_hasAddVCNDimAtMost_n_of_convex_rn_add_one` holds with constant $c = 3$, since $3 \le 3^n$ for all $n \ge 1$ and `HasAddVCNDimAtMost.mono` lifts the uniform bound $3$ to $3^n$.
- **Direct $\mathbb{R}^3$ theorem (`OMA.solution` in PR `#2797`):** `hasAddVCNDimAtMost_two_two_of_convex_r3` holds for every convex $C \subseteq \mathbb{R}^3$, independently proved in 870 lines without topology.

# What was already known

- For $n = 1$, every convex set in $\mathbb{R}^2$ has additive $\mathrm{VC}$-dimension at most $3$ (Naszodi and Taschuk, 2010), which is sharp for a unit disk shattering three vertices of an equilateral triangle, while convex sets in $\mathbb{R}^3$ can shatter infinite sets.
- Higher-arity $\mathrm{VC}_n$-dimension arose in model theory (Shelah; Chernikov, Palacin, and Takeuchi, 2019) and higher-order arithmetic regularity (Terry and Wolf, 2021 and 2025).
- For general $n \ge 1$, convex sets in $\mathbb{R}^{n+2}$ can have infinite additive $\mathrm{VC}_n$-dimension (`exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost`).
- In $\mathbb{R}^{n+1}$, Kenta Kitamura formally verified two milestones in Lean 4: a counterexample showing that $\mathrm{VC}_2(C) \le 1$ fails for some convex $C \subseteq \mathbb{R}^3$ (`KitaKen1/vcdim-convex-counterexample`), and a finite upper bound $\mathrm{VC}_n(C) \le 2^{8(n+2)^n} - 1$ for all $n \ge 1$ (`KitaKen1/vcdim-convex-finite-bound`). Our Theorem 1 matches Kitamura's lower bound at $n = 2$ (fixing the exact maximum at $2$) and collapses the double-exponential upper bound to the constant $2$ for all $n \ge 2$.

# Idea of the proof

Suppose for contradiction that a convex set $C \subseteq \mathbb{R}^{n+1}$ ($n \ge 2$) shatters a $3^n$-element sumset grid $P = \{p(i) : i \in (\mathrm{Fin}\, 3)^n\}$.

First, convexity gives two elementary obstructions. Omitting any single grid point shows that every $p(i)$ is an extreme point of $\operatorname{conv}(P)$, so each factor $\{x_k(0), x_k(1), x_k(2)\}$ is a non-degenerate triangle spanning a $2$-plane $H_k$, and the kernel $W = \ker(\Phi)$ of the summation map $\Phi(v_0, \dots, v_{n-1}) = \sum_k v_k$ intersects every product of vertex cones $\prod_k K_k(a_k)$ only at $0$ (`strict_convex_pos` and `no_pos_sum`). Second, for any two subsets $S_a, S_b \subseteq (\mathrm{Fin}\, 3)^n$, the nonzero difference $w = y(S_b) - y(S_a)$ cannot lie in the positive cone spanned by $p(q) - p(S_a)$ for any $q \in S_b \setminus S_a$, nor in the positive cone spanned by $p(S_b) - p(p_0)$ for any $p_0 \in S_a \setminus S_b$ (`forbidden_forward`, `forbidden_backward`, `y_sub_ne_zero`).

Next, on each $2$-plane $H_k$ with basis $e_{k,1} = x_k(1) - x_k(0)$ and $e_{k,2} = x_k(2) - x_k(0)$, we introduce the odd homogeneous cubic

$$\phi_k(\alpha e_{k,1} + \beta e_{k,2}) = \alpha \beta (\alpha + \beta)$$

defined in Lean as `cubicF`. A direct algebraic calculation (`coneCoord_cubic`, `cubic_pos_iff`, `cubic_nonneg_iff`) shows that $\phi_k$ is invariant under all six permutations of the triangle vertices and satisfies $\phi_k(v) \ge 0$ if and only if $v \in K_k(0) \cup K_k(1) \cup K_k(2)$. Consequently, the map $F = (f_0, \dots, f_{n-1}) : W \to \mathbb{R}^n$ never lands in $\mathbb{R}_{\ge 0}^n \cup \mathbb{R}_{\le 0}^n$ on $W \setminus \{0\}$ (`cubicF_not_nonneg`, `cubicF_not_nonpos`). By the Borsuk-Ulam theorem (`borsuk_ulam`), this forces $\dim W = n - 1$ exactly and $\Phi$ surjective (`ker_finrank_and_surj`).

When $n = 2$, $\dim W = 1$ gives a single nonzero vector $z_0 \in W$ with $f_0(z_0) < 0 < f_1(z_0)$, producing a strictly positive linear relation among four one-step edge vectors. Writing $w = y(S_b) - y(S_a)$ for $M_a = \{(1,0),(2,0)\}$ and $M_b = \{(0,1),(0,2)\}$ as a minimal nonnegative combination of these four vectors forces one coefficient to vanish, immediately violating forward or backward avoidance (`no_shatters_d2_n2`).

When $n = m + 3 \ge 3$, we avoid singular homology and Brouwer degree completely by performing simultaneous radial surgery across all chambers on the $L^\infty$-unit sphere `cubeBdry (m + 1)` of $W \cong \mathbb{R}^{m+2}$. Let $\bar{F}(z) = \pi_E(F(z)) / \|\pi_E(F(z))\|_\infty$ be the normalized odd zero-sum projection (`piE`), and set $q_* = (-1, \frac{1}{m+2}, \dots, \frac{1}{m+2})$ (`qstar`). Any preimage $\bar{F}(z) = q_*$ must satisfy $f_0(z) < 0 < f_1(z) = \dots = f_{m+2}(z)$, so $\bar{F}^{-1}(q_*)$ lies inside the pairwise disjoint open convex chambers $U_a$ ($a \in (\mathrm{Fin}\, 3)^{m+3}$) where $f_0 < 0$ and $f_k > 0$ ($k \ge 1$). Because $f_0 < 0$ strictly on every closed chamber $D_a$, the closures $D_a$ and $-D_b$ are disjoint across opposite signs.

Inside each nonempty chamber $D_a$, we pick $z_0 \in J_a$ with $\mu_{0,1}(z_0) = 1$, parametrize $D_a$ radially on $V_0 = \ker(\mu_{0,1})$ via the Minkowski gauge $M(x) \in [0, 1]$, and apply the two-subset pair $M_a = \{i_0 \neq a_0,\, i_{k \ge 1} = a_k\}$, $M_b = \{i_0 = a_0,\, i_{k \ge 1} \neq a_k\}$ (`MaSet`, `MbSet`, `forward_avoidance`, `backward_avoidance`). Minimizing along $z_0$ gives a continuous boundary map $\Phi_{\mathrm{rec}} : V_0 \to \partial \Delta^{m+1}$ whose restriction to radius $R$ converges uniformly to the asymptotic limit $\Phi_\infty$ on the sphere of $V_0$. Splicing $\Phi_{\mathrm{rec}}$ into $\bar{F}$ across four closed radial bands $r \in [\frac{3}{4}, 1], [\frac{1}{2}, \frac{3}{4}], [\frac{1}{4}, \frac{1}{2}], [0, \frac{1}{4}]$ and applying the simplex embedding `PsiInv` replaces $\bar{F}$ on $D_a$ by a continuous map avoiding $\pm q_*$ while leaving $\partial D_a$ untouched (`chamber_surgery`).

Pasting all chambers $D_a$, their antipodes $-D_a$, and the exterior closed set (`continuousOn_biUnion_of_isClosed`) produces a continuous odd map $\widetilde{F} : \partial([-1,1]^{m+2}) \to S_\infty(E) \setminus \{\pm q_*\}$. Its coordinate equatorial projection $g_j(z) = \widetilde{F}(z)_{j+1} + \widetilde{F}(z)_0 / (m + 2)$ vanishes at some point $z$ by `borsuk_ulam`, which together with $\sum_k \widetilde{F}(z)_k = 0$ and $\|\widetilde{F}(z)\|_\infty = 1$ forces $\widetilde{F}(z) = \pm q_*$ (`no_odd_map_avoiding_qstar`, `no_shatters_d2_ge3`), contradiction.

For $n = 1$ ($d = 3$), Radon's theorem in $\mathbb{R}^2$ pairs the four points into intersecting diagonals, and the resulting four forbidden cones cover $\mathbb{R}^2 \setminus \{0\}$ (`d3_n1_four_sectors`, `no_shatters_d3_n1`).

# Key lemmas in the Lean 4 formalization

All line numbers below refer to `proofs/VCDimConvex.hasAddVCNDimAtMost_n_two_of_convex_rn_add_one.lean` (4,376 lines, SHA-256 `0fa32f804a75df70e2e4afa2d30312a6bbb63e5d32bd66eced6a003016acddcc`). The exponential-bound file (`proofs/VCDimConvex.exists_exponential_bound_hasAddVCNDimAtMost_n_of_convex_rn_add_one.lean`, 4,370 lines, SHA-256 `930325277d711615de03e0641ffdb0853fe93ec7d8eb0f571977d750af6b726d`) shares the identical formal proof body (lines 25-4363) and concludes with `c = 3` at lines 4365-4370.

1. **Combinatorial Ky Fan lemma and Borsuk-Ulam (lines 35-1608):** `kyFan_simplex_parity` (line 276) establishes the single-simplex mod-2 alternating-label identity. `CubeSimplex` (line 397) encodes the antipodally reflected Kuhn triangulation of $\partial([-N, N]^{k+1})$. `pairStep` (line 620), `pairStep_involutive` (line 675), `pairStep_ne_of_not_equator` (line 798), `pairStep_preserves_faceVerts` (line 832), and `embedEquator` (line 1007) implement the 5-case facet-pairing involution and equator bijection. `kyFan_cube_parity` (line 1179) proves odd parity by induction on dimension, and `borsuk_ulam` (line 1435) deduces the $L^\infty$-sphere Borsuk-Ulam theorem on `cubeBdry m` (line 1400) via compactness and uniform continuity.
2. **Convex position and two-subset obstructions (lines 1614-1713):** `strict_convex_pos` (line 1623), `forbidden_forward` (line 1647), `forbidden_backward` (line 1689), and `y_sub_ne_zero` (line 1705).
3. **$S_3$-invariant cubics and kernel dimension (lines 1715-2039):** `coneCoord_cubic` (line 1741), `cubic_pos_iff` (line 1754), `cubic_nonneg_iff` (line 1774), `no_pos_sum` (line 1816), `cubicF_not_nonneg` (line 1935), `cubicF_not_nonpos` (line 1948), and `ker_finrank_and_surj` (line 1957).
4. **Chamber coordinates, simplex embedding, and surgery (lines 2042-3430):** `sum_muCoord_uVec` (line 2089), `forward_avoidance` (line 2141), `backward_avoidance` (line 2210), `PsiInv_ne_neg_qstar` (line 2460), `PsiInv_ne_qstar` (line 2466), `PsiInv_H0_eq_Fbar` (line 2498), `no_odd_map_avoiding_qstar` (line 2528), and the 4-band surgery theorem `chamber_surgery` (line 2582).
5. **Main contradiction and base cases (lines 3432-4376):** `no_shatters_d2_ge3` (line 3432) handles all $n \ge 3$; `no_shatters_d2_n2` (line 3761) handles $n = 2$; `d3_n1_four_sectors` (line 3854) and `no_shatters_d3_n1` (line 3986) handle $n = 1$; `hasAddVCNDimAtMost_three_of_convex_rn_add_one` (line 4351) combines all cases on `Fin (n + 1) -> R`; and `OMA.solution` (line 4365) transports across `EuclideanSpace.equiv (Fin (n + 1)) R`.
6. **Standalone $\mathbb{R}^3$ proof (`proofs/VCDimConvex.hasAddVCNDimAtMost_two_two_of_convex_r3.lean`, PR `#2797`, 870 lines, SHA-256 `a912186c20da824c...`):** `sign_normal_form` (line 272), `canonical_basis` (line 400), `no_shatters_grid_r3` (line 656), and `OMA.solution` (line 864).

# Credit and verification

- **Author and agent owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Archival preprint:** [Zenodo DOI 10.5281/zenodo.24592289](https://doi.org/10.5281/zenodo.24592289) ([https://zenodo.org/records/24592289](https://zenodo.org/records/24592289), concept DOI `10.5281/zenodo.24592288`).
- **Agent and verification workflow:** Proof discovery, homology-free blueprint design, Lean 4 formalization, and independent second-agent blind verification were executed using an Antigravity multi-agent research swarm running Gemini models (`vcdim-prover`, `lean-vcdim`, `referee`, `referee-2`, and `infra`).
- **Independent checks:** All three Lean files were audited against `FormalConjectures/Other/VCDimConvex.lean` (commit `9097e2f90e66`), passed `tools/lint.py` (`ok: true`, `errors: []`), `tools/check.sh` (`verdict: accepted`, `0` errors, `0` warnings, axioms `[propext, Classical.choice, Quot.sound]`), and live GitHub Actions CI (`COMPLETED / SUCCESS`) on pull requests [PR #2797](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2797), [PR #2823](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2823), and [PR #2902](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2902).
- **Prior work built upon:** J. Radon (1921), K. Borsuk (1933), K. Fan (1952), M. Naszodi and S. Taschuk (2010), A. Chernikov, D. Palacin, and K. Takeuchi (2019), C. Terry and J. Wolf (2021, 2025), Google DeepMind's Formal Conjectures authors (2025), and K. Kitamura (2026).
