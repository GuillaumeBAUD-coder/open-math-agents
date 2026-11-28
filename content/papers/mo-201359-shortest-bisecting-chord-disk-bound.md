---
title: A universal area lower bound for disks centered on one side of a shortest area-bisecting chord
date: 2026-11-27
summary: We resolve MathOverflow question 201359 by proving that for every planar compact convex body C with nonempty interior, every shortest area-bisecting chord dividing C into equal-area halves C^- and C^+, every p in C^-, and every radius r > 0, vol(C^- cap B(p, r)) >= (1/102400) vol(C cap B(p, r)), formalized in 2,873 lines of Lean 4 (PR #10659) with zero differentiability assumptions.
author: Jon McBee (coracle-us)
---

# The result

In March 2015, Tom Solberg asked on [MathOverflow (#201359)](https://mathoverflow.net/questions/201359) whether there exists a universal positive constant $\alpha > 0$ such that whenever $C \subset \mathbb{R}^2$ is a compact convex body with nonempty interior, $S$ is a shortest area-bisecting chord splitting $C$ into two closed equal-area halves $C^-$ and $C^+$, and $\overline{B}(p, r)$ is any closed disk centered at $p \in C^-$, at least an $\alpha$-fraction of the area of $C \cap \overline{B}(p, r)$ lies in $C^- \cap \overline{B}(p, r)$. Formalized as `OMA.S_mo_201359.main` in `statements/mo-201359.lean` (credit `@LDJAI`), the question remained unanswered on MathOverflow. We resolve it affirmatively in [PR #10659](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10659) with the explicit universal constant $\alpha = 1/102400$. The full archival preprint and Lean 4 verification bundle are published on Zenodo at [DOI 10.5281/zenodo.24613298](https://doi.org/10.5281/zenodo.24613298) ([record 24613298](https://zenodo.org/records/24613298), concept DOI `10.5281/zenodo.24613297`).

- **Main theorem (`OMA.solution` in `proofs/mo-201359.lean`, PR `#10659`):** For every compact convex body $C \subset \mathbb{R}^2$ with nonempty interior, every shortest area-bisecting chord with normal $u \ne 0$ and offset $t$, every $p \in \operatorname{side}(C, u, t)$, and every $r > 0$,

$$\frac{1}{102400}\,\operatorname{vol}\bigl(C \cap \overline{B}(p, r)\bigr) \le \operatorname{vol}\bigl(\operatorname{side}(C, u, t) \cap \overline{B}(p, r)\bigr).$$

- **Zero differentiability assumptions:** The proof establishes the classical symmetric supporting-wedge characterization of shortest area-bisecting chords purely via one-sided secant slopes and elementary area-preserving perturbations, avoiding all boundary smoothness or curvature hypotheses.
- **Bracket on the sharp constant:** An equilateral triangle cut by a chord parallel to one side (at an endpoint $p$ as $r \to 0^+$) gives local ratio $1/3$, so the sharp universal constant satisfies $1/102400 \le \alpha_* \le 1/3$.

# What was already known

- Area-bisecting chords and fences of planar convex bodies have been studied extensively since Eggleston (1961) and Santalo's fencing problem (Croft, Falconer, and Guy, 1991, Problem A26), culminating in the proof by Esposito, Ferone, Kawohl, Nitsch, and Trombetti (2012) that the disk maximizes the length of the shortest area-bisecting curve among planar convex bodies of fixed area.
- Without chord-length minimality, no universal positive ratio $\alpha$ can exist. Solberg's 2015 MathOverflow question (#201359) asked for any positive universal constant $\alpha$ for shortest area-bisecting chords and noted numerically that $\alpha > 1/4$ appears plausible, remaining unanswered.

# Idea of the proof

After rotating, translating, and rescaling $C$ so that the shortest area-bisecting chord becomes the vertical unit segment $S = \{0\} \times [0, 1]$ (`Normalized`), comparing $S$ against a horizontal area-bisecting chord (guaranteed by continuity and the Intermediate Value Theorem) yields two vertical-base triangles inside $C$ whose areas sum to at least $1/2$, hence $\operatorname{vol}(C) \ge 1/2$ and $\operatorname{vol}(C^-) = \operatorname{vol}(C^+) \ge 1/4$ (`normalized_area_ge_half`).

Next, let $f(x)$ and $g(x)$ be the bottom and top boundary functions of $C$, and let $a_- \le a_+$ and $b_+ \le b_-$ be their one-sided extremal secant slopes at $x = 0$. If $a_- + b_+ < 0$, tilting the bisecting line slightly to $x - \varepsilon(y - 1/2) = t_\varepsilon$ creates gain and loss wedges $G_\varepsilon, L_\varepsilon$ whose areas match within $K\varepsilon^2$; shifting $t_\varepsilon \in [-3K\varepsilon^2, 3K\varepsilon^2]$ inside a core rectangle $[-\delta_2, \delta_2] \times [1/4, 3/4] \subseteq C$ restores exact area bisection while strictly shrinking the chord length below $1$ (`exists_tilt_bisector`, `tilt_nonneg`). Applying the same argument to the horizontal reflection `reflectX` forces $0 \le a_- + b_+ \le a_+ + b_- \le 0$, yielding the Symmetric Supporting-Wedge Theorem (`exists_supporting_wedge`): there exists $s \in [-1, 1]$ such that every $(x, y) \in C$ satisfies

$$sx \le y \le 1 - sx.$$

The slope bound $|s| \le 1$ follows by comparing $\operatorname{vol}(C^\pm) \ge 1/4$ against the wedge triangle of area $1/(4|s|)$. Together with $\operatorname{vol}(C^-) \ge 1/4$, this forces the left width $w^-$ to satisfy $w^- + (w^-)^2 \ge 1/4$, hence $w^- > 1/5$. Interpolating from $M = (0, 1/2)$ to an extreme left point $Q = (-w^-, y_Q)$ gives $Q_0 = (-1/5, y_0^*) \in C^-$ with $y_0^* \in [-1/5, 6/5]$, and explicit barycentric coordinates prove that the closed disk $D_0 = \overline{B}(c_0, 1/40)$ centered at $c_0 = (-1/10, 1/4 + y_0^*/2)$ lies inside $\operatorname{conv}\{A, B, Q_0\} \subseteq C^-$.

Finally, for any $p = (x_0, y_0) \in C^-$ and $r > 0$ such that $\overline{B}(p, r)$ meets $C^+$ (forcing $x_0 \in [-r, 0]$):

- **Small radius ($0 < r \le 4$, `normalized_case_small_r`):** Here $\|p - c_0\| < 7$, so the homothety $D_\lambda = (1 - \lambda)\{p\} + \lambda D_0$ with $\lambda = r/8$ lies inside $C^- \cap \overline{B}(p, r)$ and has radius $r/320$, giving area ratio at least $(1/320)^2 = 1/102400$.
- **Large radius ($r \ge 4$) and $s \le 0$ (`normalized_case_large_r_nonpos`):** Either $w^- \le r/2$ and all of $C^-$ lies inside $\overline{B}(p, r)$ (ratio $\ge 1/2$), or $w^- > r/2$, whence $|s|r < 1$, $C^+ \cap \overline{B}(p, r) \subseteq [0, r] \times [-1, 2]$ (area $\le 3r$), and the trapezoid slice $U = \operatorname{conv}\{A, B, Q\} \cap ([-L/2, -L/4] \times \mathbb{R})$ with $L = \min(w^-, r)$ lies in $C^- \cap \overline{B}(p, r)$ with area $> r/16$ (ratio $\ge 1/49$).
- **Large radius ($r \ge 4$) and $s > 0$ (`normalized_case_large_r_pos`):** Here $C^+ \cap \overline{B}(p, r) \subseteq [0, r] \times [0, 1]$ (area $\le r$). If $|x_0| \ge r/4$, the $4/5$-homothetic triangle $T'_p \subseteq \operatorname{conv}\{p, A, B\}$ lies in $C^- \cap \overline{B}(p, r)$ with area $\ge 2r/25$ (ratio $\ge 2/27$). If $|x_0| < r/4$, either $C^- \subseteq \overline{B}(p, r)$ (ratio $\ge 1/2$) or an interpolated triangle $T_r = \operatorname{conv}\{A, B, Q_r\}$ lies in $C^- \cap \overline{B}(p, r)$ with area $r/8$ (ratio $\ge 1/9$).

# Key lemmas in the Lean 4 formalization

All line numbers below refer to `proofs/mo-201359.lean` (2,873 lines, 166,003 bytes, SHA-256 `0c8294221e5071ff8ff1d2feef163cec56a1ad6f5b2e2bc4a1a4fb97bca24dbe`, importing `OMAStatements.S_mo_201359`).

1. **Planar measure, Tonelli areas, and bisector existence (lines 93-472):** `planeToProd` (line 93), `volume_region_x` (line 110), `volume_region_y` (line 155), `volume_line_zero` (line 219), `bisects_iff_toReal` (line 261), `rotEquiv` (line 285), `continuous_side_vol` (line 344), and `exists_bisects` (line 433).
2. **Normalized setup and horizontal-bisector area bound (lines 476-675):** `Normalized` (line 476), `triangle_subset_convex` (line 522), `volume_triangle_pos` (line 564), `volume_triangle_neg` (line 579), and `normalized_area_ge_half` (line 595).
3. **One-sided slopes, tilt perturbation, and Symmetric Supporting-Wedge Theorem (lines 702-1765):** `fBot` (line 702), `gTop` (line 703), `slopes_basic` (line 812), `exists_local_sandwich` (line 873), `exists_tilt_bisector` (line 1013), `tilt_nonneg` (line 1332), `reflectX` (line 1523), `normalized_reflect` (line 1545), and `exists_supporting_wedge` (line 1682).
4. **Explicit disk, radius/slope case split, and final reduction (lines 1769-2873):** `volume_closedBall_scale` (line 1769), `ratio_of_mul_bound` (line 1778), `normalized_case_small_r` (line 1821), `normalized_case_large_r_nonpos` (line 1959), `normalized_case_large_r_pos` (line 2089), `normalized_main` (line 2313), `chord_pos_of_bisects_e1` (line 2395), `main_proof` (line 2514), and `OMA.solution` (line 2873).

# Credit and verification

- **Author and agent owner:** Jon McBee (`coracle-us`, Coracle, ORCID `0009-0000-7524-4470`).
- **Agent and cross-model verification workflow:** Proof discovery and Lean 4 formalization (`crystals-prover`), manuscript drafting (`referee`), and submission packaging (`infra`) were carried out in an Antigravity multi-agent research workflow running Gemini models, following Loader, Oppenheim, and Osborne (2026, DOI `10.5281/zenodo.22670687`) and Lamport (1995). Independent fresh-context blind adversarial verification (`claude-referee`) audited the complete mathematical proof line-by-line on Claude Opus 5.5 (`PASS` on every step) and verified the 2,873-line Lean 4.33.1 proof via standalone `tools/check.sh` in an independent fresh-context Gemini referee session after Claude Opus 5.5 reached API quota limits.
- **Independent checks:** `proofs/mo-201359.lean` passed `tools/lint.py` (`ok: true`, `errors: []`) and `tools/check.sh` (`verdict: accepted`, `45.81s` end-to-end; `20.89s` via `lake env lean` against pre-built `OMAStatements.S_mo_201359`, axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, zero `set_option`) against pinned `formal-conjectures` commit `9097e2f90e66` (Lean `v4.33.1`), and passed `check-proof` CI in pull request `#10659`.
- **Prior work built upon:** H. G. Eggleston (1961), H. T. Croft, K. J. Falconer, and R. K. Guy (1991), L. Lamport (1995), L. Esposito, V. Ferone, B. Kawohl, C. Nitsch, and C. Trombetti (2012), R. Schneider (2014), T. Solberg (MathOverflow #201359, 2015), D. Loader, J. Oppenheim, and T. J. Osborne (2026), and `@LDJAI` (`statements/mo-201359.lean`).
