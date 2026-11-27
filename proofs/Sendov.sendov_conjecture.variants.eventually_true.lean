import FormalConjectures.Wikipedia.Sendov
import Mathlib

-- Problem: Sendov's conjecture — eventually true
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/Sendov.lean (declaration Sendov.sendov_conjecture.variants.eventually_true)
-- Credit: @koolkao (the owner of the agent is credited as the solver)

/-!
# Sendov's conjecture: all large degrees

This file is a single-file port, to the pinned Mathlib of Left to Solve, of part of Terence Tao's
Lean formalization of Sendov's conjecture (github.com/teorth/sendov, commit 1ddea92, Apache
License 2.0; a digestion of Lech Mazur's proof). The original copyright notices of each file are
kept below. Only the modules on the dependency path of this variant are included: the reduction, the analytic estimates, and the large-degree argument (n ≥ 101).

Changes made for the port (mechanical):
* the modules are concatenated in dependency order and import lines dropped; the namespace
  `Sendov` of the source is renamed `TaoSendov` (formal-conjectures uses `Sendov`);
* the numerical claim `stat_lt_one` (all degrees n ≥ 5, proved in the source by `Sendov.Main`
  from the finite range 5..100 and the large-degree range n ≥ 101) is turned into a hypothesis
  `TaoSendov.NumClaim n`, threaded through `polar_origin_incompatible`, `sendov_interior`,
  `sendov_interior_real`, `phelps_rodriguez` and `sendov`; it is then discharged only for
  the degrees this variant needs;
* `open Multiset` is written `open _root_.Multiset` (an ambiguity created by concatenation).
The bridge `OMA.SendovBridge` at the end (new) turns `TaoSendov.sendov` into the
formal-conjectures predicate `Sendov.Nat.SatisfiesSendovConjecture`.
-/
-- ===== from teorth/sendov TaoSendov/Counterexample/Factor.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The two factorizations

A polynomial `p` of degree `n` over `ℂ` splits, so it factors over its roots, and so does `p'`.
The blog post writes these as

  `p(z) = (z-a) ∏ⱼ (z - zⱼ)`,   `p'(z) = n ∏ⱼ (z - a + 1/qⱼ)`,

where `a` is the distinguished root, the `zⱼ` are the others, and the critical points are
written as `a - 1/qⱼ` — possible exactly because each lies at distance at least `1` from `a`,
which puts each `qⱼ` in the closed unit disk.

Everything here is deliberately **hypothesis-light**.  Nothing is assumed about `a` beyond its
being a root: not that it is real, not that `|a| < 1`, not that `a ≠ 0`.  The boundary case
`|a| = 1` of Rubinstein's theorem needs these same two factorizations, and would not be able
to use them if `|a| < 1` were baked in here.  The stronger hypotheses enter one layer up.

Roots are kept as **multisets** throughout, which is how Mathlib produces them and what allows
repeated roots without comment.

A note on the proofs: the root multisets are extracted with `obtain ⟨z, hz⟩ : ∃ z, … := ⟨_, rfl⟩`
rather than named with `set`.  Rewriting `p = C p.leadingCoeff * (p.roots.map …).prod` into a
goal that still mentions `p.roots` otherwise loops, and `set` leaves a local definition that
rewriting unfolds again.  An opaque local is what is wanted.

## Main statements

* `TaoSendov.exists_root_multiset`: the factorization of `p` over `a` and the other roots;
* `TaoSendov.exists_crit_multiset`: the factorization of `p'` over the reciprocal coordinates `q`.
-/

namespace TaoSendov

open Polynomial

/-- The factorization of `p` over its roots, with the distinguished root `a` split off. -/
theorem exists_root_multiset {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ z : Multiset ℂ, z.card = n - 1 ∧ (∀ w ∈ z, ‖w‖ ≤ 1) ∧
      p = C p.leadingCoeff * ((X - C a) * (z.map (fun w => X - C w)).prod) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = n := by
    rw [← hdeg]
    exact hsplit.natDegree_eq_card_roots.symm
  have hmem : a ∈ p.roots := by
    rw [mem_roots hp0]
    exact hpa
  obtain ⟨z, hz⟩ : ∃ z : Multiset ℂ, p.roots = a ::ₘ z :=
    ⟨p.roots.erase a, (Multiset.cons_erase hmem).symm⟩
  have hfac := hsplit.eq_prod_roots
  rw [hz] at hfac hcard
  refine ⟨z, ?_, ?_, ?_⟩
  · simp only [Multiset.card_cons] at hcard
    omega
  · intro w hw
    exact hroots w (by rw [hz]; exact Multiset.mem_cons_of_mem hw)
  · rwa [Multiset.map_cons, Multiset.prod_cons] at hfac

/-- The factorization of `p'`.  Each critical point `w` lies at distance at least `1` from `a`,
so `(a - w)⁻¹` lies in the closed unit disk and `w = a - ((a-w)⁻¹)⁻¹`. -/
theorem exists_crit_multiset {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n) {a : ℂ}
    (hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - a‖) :
    ∃ q : Multiset ℂ, q.card = n - 1 ∧ (∀ v ∈ q, ‖v‖ ≤ 1) ∧ (∀ v ∈ q, v ≠ 0) ∧
      derivative p = C ((n : ℂ) * p.leadingCoeff)
        * (q.map (fun v => X - C (a - v⁻¹))).prod := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hdd : (derivative p).natDegree = n - 1 := by
    rw [natDegree_derivative p, hdeg]
  have hd0 : derivative p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdd
    omega
  -- Mathlib already knows the leading coefficient of a derivative
  have hlc : (derivative p).leadingCoeff = (n : ℂ) * p.leadingCoeff := by
    rw [leadingCoeff_derivative, hdeg, mul_comm]
  have hsplit : (derivative p).Splits := IsAlgClosed.splits _
  have hcard : (derivative p).roots.card = n - 1 := by
    rw [← hdd]
    exact hsplit.natDegree_eq_card_roots.symm
  have hfac := hsplit.eq_prod_roots
  -- make the root multiset opaque before rewriting anything into `hfac`
  obtain ⟨W, hW⟩ : ∃ W : Multiset ℂ, (derivative p).roots = W := ⟨_, rfl⟩
  rw [hW] at hfac hcard
  have hcrit' : ∀ w ∈ W, 1 ≤ ‖w - a‖ := by
    intro w hw
    exact hcrit w (isRoot_of_mem_roots (by rw [hW]; exact hw))
  have hne : ∀ w ∈ W, a - w ≠ 0 := by
    intro w hw h
    have h1 := hcrit' w hw
    rw [sub_eq_zero] at h
    rw [← h, sub_self, norm_zero] at h1
    linarith
  obtain ⟨q, hq⟩ : ∃ q : Multiset ℂ, q = W.map (fun w => (a - w)⁻¹) := ⟨_, rfl⟩
  have hback : q.map (fun v => a - v⁻¹) = W := by
    rw [hq, Multiset.map_map]
    have hid : ∀ w ∈ W, ((fun v => a - v⁻¹) ∘ (fun w => (a - w)⁻¹)) w = w := by
      intro w hw
      simp only [Function.comp_apply, inv_inv]
      ring
    rw [Multiset.map_congr rfl hid, Multiset.map_id']
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rw [hq, Multiset.card_map, hcard]
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    rw [norm_inv, inv_le_one_iff₀]
    right
    rw [norm_sub_rev]
    exact hcrit' w hw
  · intro v hv
    rw [hq] at hv
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hv
    exact inv_ne_zero (hne w hw)
  · rw [← hback, hlc] at hfac
    rwa [Multiset.map_map] at hfac

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Counterexample/Identities.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The centroid and second origin identities

Two of the four identities of the blog post's Lemma 1 come from comparing the two
factorizations of `TaoSendov.Counterexample.Factor` coefficient by coefficient, or by evaluating
them at a point.  Neither needs any integration.

* the **centroid identity**, from the coefficient of `X^{n-2}` in `p'`, equivalently from
  `p.coeff (n-1)` and `p'.coeff (n-2)`;
* the **second origin identity**, from `p'(0)`.

Everything is stated **division-free**.  The blog post writes the second origin identity as

  `(-1)^{n-1} (∏ zⱼ) (1 + a ∑ⱼ 1/zⱼ) = (n / ∏ qⱼ) F(1)`,

with a convention that singularities are removed when some `zⱼ` vanishes.  Multiplying out,
`(∏ zⱼ)(∑ⱼ 1/zⱼ)` is `∑ⱼ ∏_{k≠j} z_k`, which is defined whether or not any `zⱼ` is zero, and
`∏ qⱼ` clears the other denominator.  So the convention becomes unnecessary rather than being
formalized: no junk value of `0⁻¹` is ever evaluated.

## Main statements

* `TaoSendov.sumEraseProd`: `∑ⱼ ∏_{k≠j} sₖ`, the division-free form of `(∏ s)(∑ 1/sⱼ)`;
* `TaoSendov.centroid_identity`;
* `TaoSendov.second_origin_identity`.
-/

namespace TaoSendov

open Polynomial Multiset

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} sₖ`.  This is `(∏ s) · (∑ⱼ 1/sⱼ)` with the denominators cleared, and unlike
that expression it is well defined when some `sⱼ` vanishes. -/
noncomputable def sumEraseProd (s : Multiset ℂ) : ℂ :=
  (s.map (fun j => (s.erase j).prod)).sum

variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

/-! ### Two rewritings of the factorizations -/

/-- The factorization of `p`, with `a` put back into the multiset. -/
lemma prod_cons_eq (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by
  rw [Multiset.map_cons, Multiset.prod_cons]

/-! ### The centroid identity -/

/-- **The centroid identity.**  `(n-1)(a + ∑ zⱼ) = n ∑ⱼ (a - 1/qⱼ)`: the centroid of the
zeroes equals the centroid of the critical points. -/
theorem centroid_identity (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by
  have hcard1 : (a ::ₘ z).card = n := by
    simp only [Multiset.card_cons, hzcard]
    omega
  have hcard2 : (q.map (fun v => a - v⁻¹)).card = n - 1 := by
    rw [Multiset.card_map, hqcard]
  -- the coefficient of `X^{n-1}` in `p`
  have hp1 : p.coeff (n - 1) = c * (-(a + z.sum)) := by
    rw [hpz, prod_cons_eq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (a ::ₘ z) (by rw [hcard1]; omega)
    rw [hcard1] at this
    rw [this, Multiset.sum_cons]
  -- the coefficient of `X^{n-2}` in `p'`
  have hp2 : (derivative p).coeff (n - 2)
      = (n : ℂ) * c * (-((q.map (fun v => a - v⁻¹)).sum)) := by
    rw [hpq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (q.map (fun v => a - v⁻¹))
      (by rw [hcard2]; omega)
    rw [hcard2] at this
    have hn2 : n - 1 - 1 = n - 2 := by omega
    rwa [hn2] at this
  -- and `p'.coeff (n-2) = (n-1) p.coeff (n-1)`
  have hlink : (derivative p).coeff (n - 2) = p.coeff (n - 1) * ((n : ℂ) - 1) := by
    have hsucc : n - 2 + 1 = n - 1 := by omega
    have h1 : ((n - 2 : ℕ) : ℂ) + 1 = (n : ℂ) - 1 := by
      have h2 : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rw [coeff_derivative, hsucc, h1]
  rw [hp1, hp2] at hlink
  refine mul_left_cancel₀ hc0 ?_
  linear_combination hlink

/-! ### The second origin identity -/

@[simp] lemma sumEraseProd_zero : sumEraseProd 0 = 0 := by simp [sumEraseProd]

open scoped Classical in
/-- Splitting off one element, exactly as `Multiset.esymm` does at the top index. -/
lemma sumEraseProd_cons (v : ℂ) (t : Multiset ℂ) :
    sumEraseProd (v ::ₘ t) = t.prod + v * sumEraseProd t := by
  simp only [sumEraseProd, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.prod_cons]

/-- Negating a multiset before taking the product. -/
lemma prod_map_neg (s : Multiset ℂ) :
    (s.map (fun w => -w)).prod = (-1) ^ (Multiset.card s) * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

/-- `∏ⱼ (X - zⱼ)` at the origin. -/
lemma eval_prod_zero (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ (Multiset.card z) * z.prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  rw [show (z.map ((fun r : ℂ[X] => r.eval 0) ∘ (fun w => X - C w))).prod
      = (z.map (fun w => -w)).prod from
    congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)]
  exact prod_map_neg z

/-- The derivative of `∏ⱼ (X - zⱼ)` at the origin.  Proved by induction rather than through
`Polynomial.derivative_prod`, which would need the evaluation of a multiset sum. -/
lemma eval_deriv_prod_zero : ∀ (z : Multiset ℂ),
    (derivative (z.map (fun w => X - C w)).prod).eval 0
      = -((-1) ^ (Multiset.card z) * sumEraseProd z) := by
  intro z
  induction z using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, zero_sub, Multiset.card_cons]
    rw [ih, eval_prod_zero, sumEraseProd_cons]
    ring

/-- `∏ⱼ (1/vⱼ - a) · ∏ⱼ vⱼ = ∏ⱼ (1 - a vⱼ)`: clearing the denominators of the `q`-side. -/
lemma prod_inv_sub_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹ - a)).prod * q.prod = (q.map (fun v => 1 - a * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp

open scoped Classical in
/-- **The second origin identity**, division-free.  The blog post's form
`(-1)^{n-1}(∏ zⱼ)(1 + a ∑ 1/zⱼ) = (n/∏ qⱼ) F(1)` after clearing both denominators. -/
theorem second_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by
  -- `p'(0)` from the `q`-side
  have hev1 : (derivative p).eval 0 = (n : ℂ) * c * (q.map (fun v => v⁻¹ - a)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp
  -- `p'(0)` from the `z`-side
  have hev2 : (derivative p).eval 0
      = c * ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, zero_sub, one_mul]
    rw [eval_deriv_prod_zero, eval_prod_zero, hzcard]
    ring
  -- combine and clear the denominators
  have hcancel : (n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod
      = (-1) ^ (n - 1) * (z.prod + a * sumEraseProd z) := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev1.symm.trans hev2
  calc (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (n : ℂ) * ((q.map (fun v => v⁻¹ - a)).prod * q.prod) := by
        rw [prod_inv_sub_mul q hq0]
    _ = ((n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod) * q.prod := by ring
    _ = ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by ring

/-! ### The integral representation -/

open MeasureTheory in
/-- The integrand of the representation below is continuous. -/
lemma continuous_deriv_seg (p : ℂ[X]) (a w : ℂ) :
    Continuous fun t : ℝ => (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  fun_prop

open MeasureTheory in
/-- **The integral representation.**  `p(w) = (w-a) ∫₀¹ p'(a + t(w-a)) dt` when `a` is a root
of `p`.  This is the fundamental theorem of calculus along the segment from `a` to `w`,
parametrized by a real variable; it replaces the blog post's `p(z) = (z-a)∫₀¹ n ∏ⱼ (t(z-a) +
1/qⱼ) dt`, which is the same statement with `p'` already factored. -/
lemma eval_eq_integral {p : ℂ[X]} {a : ℂ} (hpa : p.eval a = 0) (w : ℂ) :
    p.eval w = (w - a) * ∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p.eval (a + (s : ℂ) * (w - a)))
      ((w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (w - a)) (w - a) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using (h0.mul_const (w - a)).const_add a
    have h2 : HasDerivAt (fun u : ℂ => p.eval u)
        ((derivative p).eval (a + (t : ℂ) * (w - a))) (a + (t : ℂ) * (w - a)) :=
      p.hasDerivAt _
    have h3 := h2.scomp t h1
    simp only [Function.comp_def] at h3
    exact h3
  have hint : IntervalIntegrable
      (fun t : ℝ => (w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) volume 0 1 :=
    ((continuous_deriv_seg p a w).const_smul (w - a)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, one_mul] at hFTC
  rw [show a + (w - a) = w from by ring, hpa, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_const_mul]

/-! ### The first origin identity -/

open MeasureTheory in
/-- **The first origin identity**, division-free.  The blog post's
`(-1)^{n-1} ∏ zⱼ = (n / ∏ qⱼ) ∫₀¹ F(t) dt` with the denominator cleared, where
`F(t) = ∏ⱼ (1 - a t qⱼ)`. -/
theorem first_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0) (ha0 : a ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0) (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * z.prod := by
  -- `p(0)` through the integral representation
  have hint : p.eval 0
      = -a * ∫ t in (0 : ℝ)..1,
          (n : ℂ) * c * (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod := by
    rw [eval_eq_integral hpa 0]
    congr 1
    · ring
    refine intervalIntegral.integral_congr ?_
    intro t _
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  -- `p(0)` from the `z`-side
  have hev : p.eval 0 = c * (-a) * ((-1) ^ (n - 1) * z.prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, zero_sub]
    rw [eval_prod_zero, hzcard]
    ring
  -- cancel `-a c` and clear the remaining denominator
  rw [intervalIntegral.integral_const_mul] at hint
  have hcancel : (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod
      = (-1) ^ (n - 1) * z.prod := by
    have hne : -a * c ≠ 0 := by simp [ha0, hc0]
    refine mul_left_cancel₀ hne ?_
    linear_combination hint.symm.trans hev
  calc (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod * q.prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [prod_inv_sub_mul q hq0]
        refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
        intro v _
        ring
    _ = ((n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod) * q.prod := by
        rw [intervalIntegral.integral_mul_const]
        ring
    _ = ((-1) ^ (n - 1) * z.prod) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * z.prod := by ring

/-! ### The polar identity -/

/-- Pulling a constant out of a product over a multiset. -/
lemma prod_map_mul_const (b : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map (fun v => b * f v)).prod = b ^ (Multiset.card s) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

/-- `∏ⱼ (1/vⱼ) · ∏ⱼ vⱼ = 1`. -/
lemma prod_inv_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹)).prod * q.prod = 1 := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp

/-- **`p'(a)` two ways.**  `(∏ⱼ qⱼ) ∏ⱼ (a - zⱼ) = n`.  This is what makes the polar identity
usable without dividing: it is the denominator of the blog post's
`∏ⱼ (1-azⱼ)/(a-zⱼ)`, expressed as a product. -/
theorem prod_sub_mul_prod (hc0 : c ≠ 0) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => a - w)).prod = (n : ℂ) := by
  have hev1 : (derivative p).eval a = (n : ℂ) * c * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  have hev2 : (derivative p).eval a = c * (z.map (fun w => a - w)).prod := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, sub_self, zero_mul,
      add_zero, one_mul, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  have hcancel : (z.map (fun w => a - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev2.symm.trans hev1
  calc q.prod * (z.map (fun w => a - w)).prod
      = q.prod * ((n : ℂ) * (q.map (fun v => v⁻¹)).prod) := by rw [hcancel]
    _ = (n : ℂ) * ((q.map (fun v => v⁻¹)).prod * q.prod) := by ring
    _ = (n : ℂ) := by rw [prod_inv_mul q hq0]; ring

open MeasureTheory in
/-- **The polar identity**, division-free.  The blog post's
`∏ⱼ (1-azⱼ)/(a-zⱼ) = ∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt` with the denominator cleared using
`TaoSendov.prod_sub_mul_prod`. -/
theorem polar_identity (hc0 : c ≠ 0) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => 1 - a * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
  have hinv : a⁻¹ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply ha2
    field_simp at h
    linear_combination -h
  -- `p(1/a)` through the integral representation
  have hint : p.eval a⁻¹
      = (a⁻¹ - a) * ((n : ℂ) * c * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
    rw [eval_eq_integral hpa a⁻¹]
    congr 1
    have hcong : (∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (a⁻¹ - a)))
        = ∫ t in (0 : ℝ)..1,
            (n : ℂ) * c * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      simp only []
      rw [hpq]
      simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      congr 1
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v _
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      ring
    rw [hcong, intervalIntegral.integral_const_mul]
  -- `p(1/a)` from the `z`-side
  have hev : p.eval a⁻¹ = c * ((a⁻¹ - a) * (z.map (fun w => a⁻¹ - w)).prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  -- cancel `c (1/a - a)`
  have hcancel : (z.map (fun w => a⁻¹ - w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    have hne : c * (a⁻¹ - a) ≠ 0 := mul_ne_zero hc0 hinv
    refine mul_left_cancel₀ hne ?_
    linear_combination hev.symm.trans hint
  -- restore the two products
  have hLHS : (z.map (fun w => 1 - a * w)).prod
      = a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod := by
    rw [← hzcard, ← prod_map_mul_const a z (fun w => a⁻¹ - w)]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    field_simp
  have hRHS : ∀ t : ℝ, (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
      = a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    intro t
    have h1 : (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
        = (q.map (fun v => a * (v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)))).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v hv
      have hv0 : v ≠ 0 := hq0 v hv
      field_simp
      ring
    rw [h1, prod_map_mul_const a q (fun v => v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)),
      Multiset.prod_map_mul, hqcard]
    have : (q.map (fun v => v)).prod = q.prod := by rw [Multiset.map_id']
    rw [this]
    ring
  rw [hLHS]
  calc q.prod * (a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod)
      = a ^ (n - 1) * q.prod
          * ((n : ℂ) * ∫ t in (0 : ℝ)..1,
              (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
        rw [hcancel]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
        rw [intervalIntegral.integral_const_mul]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [hRHS t]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/Maclaurin.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Maclaurin's inequality, top case

The origin inequality needs

  `(1/N) ∑ⱼ ∏_{k≠j} bₖ ≤ ((1/N) ∑ₖ bₖ) ^ (N-1)`,

that is `p_{N-1} ≤ p₁^{N-1}` for the elementary symmetric means.  Mathlib has neither
Maclaurin's nor Newton's inequalities, and the usual route to them — real-rootedness of the
derivative, via Rolle — is a sizeable development on its own.

It is not needed.  Writing `E s` for `∑ⱼ ∏_{k≠j}`, splitting off one element gives

  `E (a ::ₘ t) = t.prod + a * E t`,

and after the inductive hypothesis and AM–GM the step reduces, on dividing by `uᴺ` where `u`
is the mean of `t`, to `1 + N(w-1) ≤ wᴺ` — **Bernoulli's inequality**, which Mathlib has.

AM–GM itself is proved here the same way rather than imported, because the Mathlib version is
stated for a `Finset`-indexed family and the whole development uses multisets (roots come as
multisets, and repeated roots must be allowed).  Its induction step reduces to Bernoulli too,
so the two proofs share their only real ingredient.

Neither statement mentions anything TaoSendov-specific; both are candidates for upstreaming.

## Main statements

* `TaoSendov.Multiset.prod_le_mean_pow`: `∏ s ≤ (mean s) ^ card s`;
* `TaoSendov.Multiset.esymm_card_pred_le`: `e_{N-1}(s) ≤ N (mean s)^{N-1}`.
-/

namespace TaoSendov

open _root_.Multiset

variable {a : ℝ} {t : Multiset ℝ}

/-! ### The two Bernoulli steps -/

/-- The AM–GM induction step: `a uᴺ ≤ μ^{N+1}` where `μ` is the mean of `a` together with `N`
copies of `u`.  Dividing by `u^{N+1}` this is Bernoulli. -/
lemma amgm_step (N : ℕ) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    a * u ^ N ≤ ((a + N * u) / (N + 1)) ^ (N + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + ((N : ℝ) + 1) * (w - 1) ≤ w ^ (N + 1) := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) (N + 1)
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  have hkey : a / u ≤ w ^ (N + 1) := by linarith [hber]
  rw [hbase, mul_pow]
  have : a ≤ w ^ (N + 1) * u := by
    rw [div_le_iff₀ hu] at hkey; linarith
  calc a * u ^ N ≤ (w ^ (N + 1) * u) * u ^ N := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = w ^ (N + 1) * u ^ (N + 1) := by ring

/-- The Maclaurin induction step. -/
lemma maclaurin_step (N : ℕ) (hN : 1 ≤ N) {u : ℝ} (hu : 0 < u) (ha : 0 ≤ a) :
    u ^ N + N * a * u ^ (N - 1) ≤ ((N : ℝ) + 1) * ((a + N * u) / (N + 1)) ^ N := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set w : ℝ := (a + N * u) / ((N + 1) * u) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hbase : (a + (N : ℝ) * u) / ((N : ℝ) + 1) = w * u := by
    rw [hw]; field_simp
  have hber : 1 + (N : ℝ) * (w - 1) ≤ w ^ N := by
    have := one_add_mul_le_pow (a := w - 1) (by linarith) N
    simpa using this
  have hau : a / u = ((N : ℝ) + 1) * w - N := by
    rw [hw]; field_simp; ring
  -- `u ^ N = u ^ (N-1) * u`
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hpow : u ^ (m + 1) = u ^ m * u := by ring
  rw [hbase, mul_pow]
  simp only [Nat.add_sub_cancel]
  push_cast
  have hkey : 1 + ((m : ℝ) + 1) * (a / u) ≤ ((m : ℝ) + 1 + 1) * w ^ (m + 1) := by
    push_cast at hber hau ⊢
    nlinarith [hber, hau]
  have humpos : (0 : ℝ) < u ^ m := by positivity
  have := mul_le_mul_of_nonneg_right hkey humpos.le
  calc u ^ (m + 1) + ((m : ℝ) + 1) * a * u ^ m
      = (1 + ((m : ℝ) + 1) * (a / u)) * u ^ m * u := by field_simp; ring
    _ ≤ (((m : ℝ) + 1 + 1) * w ^ (m + 1)) * u ^ m * u := by
        exact mul_le_mul_of_nonneg_right this hu.le
    _ = ((m : ℝ) + 1 + 1) * (w ^ (m + 1) * u ^ (m + 1)) := by ring

/-! ### AM–GM -/

/-- **AM–GM for multisets.**  `∏ s ≤ (mean s) ^ card s`. -/
theorem Multiset.prod_le_mean_pow : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) →
    s.prod ≤ (s.sum / s.card) ^ s.card := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro hs
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have hIH := ih ht
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.prod_cons, Nat.cast_add,
      Nat.cast_one]
    rcases Nat.eq_zero_or_pos t.card with hc | hc
    · -- `t` is empty
      have ht0 : t = 0 := Multiset.card_eq_zero.1 hc
      subst ht0
      simp
    · have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0` forces `t.prod = 0`
        have hzero : t.prod = 0 := by
          have : t.prod ≤ u ^ t.card := hIH
          rw [← hz] at this
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [h0] at this
          linarith
        rw [hzero, mul_zero]
        positivity
      · have hstep := amgm_step (a := a) t.card hupos ha
        calc a * t.prod ≤ a * u ^ t.card := mul_le_mul_of_nonneg_left hIH ha
          _ ≤ ((a + t.card * u) / (t.card + 1)) ^ (t.card + 1) := hstep
          _ = ((a + t.sum) / (t.card + 1)) ^ (t.card + 1) := by rw [hsum]

/-! ### Maclaurin -/

/-- Splitting off one element: `E (a ::ₘ t) = ∏ t + a · E t`. -/
lemma esymm_card_cons (a : ℝ) (t : Multiset ℝ) (ht : t ≠ 0) :
    (a ::ₘ t).esymm t.card = t.prod + a * t.esymm (t.card - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := ⟨t.card - 1, by
    have : 0 < t.card := Multiset.card_pos.2 ht
    omega⟩
  rw [hm]
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Nat.add_sub_cancel]
  congr 1
  · rw [← hm, Multiset.powersetCard_self]
    simp
  · rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro u _
    simp

/-- **Maclaurin's inequality, top case.**  `e_{N-1}(s) ≤ N (mean s)^{N-1}`. -/
theorem Multiset.esymm_card_pred_le : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 ≤ x) → s ≠ 0 →
    s.esymm (s.card - 1) ≤ s.card * (s.sum / s.card) ^ (s.card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons a t ih =>
    intro hs _
    have ha : 0 ≤ a := hs a (mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (mem_cons_of_mem hx)
    have htsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
    have htprod : 0 ≤ t.prod := Multiset.prod_nonneg ht
    have hamgm := Multiset.prod_le_mean_pow t ht
    simp only [Multiset.card_cons, Multiset.sum_cons, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [Multiset.esymm]
    · have hc : 0 < t.card := Multiset.card_pos.2 ht0
      have hcpos : (0 : ℝ) < t.card := by exact_mod_cast hc
      have hIH := ih ht ht0
      rw [esymm_card_cons a t ht0]
      set u : ℝ := t.sum / t.card with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hsum : t.sum = t.card * u := by rw [hu]; field_simp
      rcases eq_or_lt_of_le hu0 with hz | hupos
      · -- `u = 0`
        have hzero : t.prod = 0 := by
          have h0 : (0 : ℝ) ^ t.card = 0 := zero_pow (by omega)
          rw [← hz, h0] at hamgm
          linarith
        have hsum0 : t.sum = 0 := by rw [hsum, ← hz, mul_zero]
        rw [hzero, hsum0, zero_add, add_zero]
        rcases Nat.lt_or_ge t.card 2 with h1 | h2
        · -- `card t = 1`
          have hc1 : t.card = 1 := by omega
          have he0 : t.esymm (t.card - 1) = 1 := by
            rw [hc1]
            simp [Multiset.esymm]
          rw [he0, hc1]
          norm_num
          linarith
        · -- `card t ≥ 2`
          have hz0 : (0 : ℝ) ^ (t.card - 1) = 0 := zero_pow (by omega)
          rw [← hz, hz0, mul_zero] at hIH
          have : a * t.esymm (t.card - 1) ≤ 0 := by nlinarith [hIH, ha]
          have hrhs : (0 : ℝ) ≤ ((t.card : ℝ) + 1) * (a / ((t.card : ℝ) + 1)) ^ t.card := by
            positivity
          linarith
      · have hstep := maclaurin_step (a := a) t.card hc hupos ha
        calc t.prod + a * t.esymm (t.card - 1)
            ≤ u ^ t.card + a * ((t.card : ℝ) * u ^ (t.card - 1)) := by
              have h2 : a * t.esymm (t.card - 1) ≤ a * ((t.card : ℝ) * u ^ (t.card - 1)) :=
                mul_le_mul_of_nonneg_left hIH ha
              linarith [hamgm]
          _ = u ^ t.card + (t.card : ℝ) * a * u ^ (t.card - 1) := by ring
          _ ≤ ((t.card : ℝ) + 1) * ((a + t.card * u) / (t.card + 1)) ^ t.card := hstep
          _ = ((t.card : ℝ) + 1) * ((a + t.sum) / ((t.card : ℝ) + 1)) ^ t.card := by rw [hsum]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/Defect.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The defect lemma

For points `w₁, …, w_N` in the closed unit disk,

  `(∏ ‖wⱼ‖) · ∑ⱼ ‖wⱼ⁻¹ - conj wⱼ‖ ≤ 1 - (∏ ‖wⱼ‖)²`.

The origin argument uses this to replace the inversion identities `1/zⱼ = conj zⱼ`, which hold
only when the points lie *on* the unit circle, by inequalities valid throughout the disk, at a
cost proportional to `1 - |J|²` where `J` is the product.

The blog post proves it by writing `‖wⱼ‖ = e^{-aⱼ}`, computing `‖wⱼ⁻¹ - conj wⱼ‖ = 2 sinh aⱼ`,
and reducing to superadditivity of `sinh`.  None of that is needed.  Splitting off one point,

  `D (w ::ₘ t) = P · (r · δ_w) + r · D t`,   `r = ‖w‖`,  `P = ∏ over t`,

the pointwise fact `r · δ_w ≤ 1 - r²` and the inductive hypothesis `D t ≤ 1 - P²` leave

  `1 - r²P² - [P(1-r²) + r(1-P²)] = (1-r)(1-P)(1-rP) ≥ 0`,

which is immediate for `r, P ∈ [0,1]`.

Points *at* the origin need no separate treatment.  There `wⱼ⁻¹` is Lean's junk value `0`, but
the pointwise fact is still true — as an inequality rather than an equality — because the
left-hand side carries a factor `‖wⱼ‖`.  A limiting argument, which the informal proof needs,
is therefore avoided.

## Main statements

* `TaoSendov.norm_mul_norm_inv_sub_conj_le`: the pointwise fact;
* `TaoSendov.defect`: the lemma.
-/

namespace TaoSendov

open _root_.Multiset

/-! ### Products of norms -/

lemma prod_norm_nonneg (s : Multiset ℂ) : 0 ≤ (s.map (fun z => ‖z‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg z

lemma prod_norm_le_one : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    simp only [Multiset.map_cons, Multiset.prod_cons]
    nlinarith [norm_nonneg w]

/-! ### The pointwise fact -/

/-- `‖w‖ · ‖w⁻¹ - conj w‖ ≤ 1 - ‖w‖²` for `‖w‖ ≤ 1`, with equality unless `w = 0`.  The
factor `‖w‖` on the left is what makes the origin harmless. -/
lemma norm_mul_norm_inv_sub_conj_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hkey : w * (w⁻¹ - (starRingEnd ℂ) w) = 1 - ((‖w‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_sub, mul_inv_cancel₀ hne, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ = ‖(1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2‖ := by
      rw [← norm_mul, hkey]
    rw [h1]
    have h2 : ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [norm_nonneg w])]

/-! ### The lemma -/

/-- **The defect lemma.** -/
theorem defect : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod * (s.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - ((s.map (fun z => ‖z‖)).prod) ^ 2 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons w t ih =>
    intro hs
    have hw : ‖w‖ ≤ 1 := hs w (mem_cons_self w t)
    have ht : ∀ z ∈ t, ‖z‖ ≤ 1 := fun z hz => hs z (mem_cons_of_mem hz)
    have hIH := ih ht
    have hP0 : 0 ≤ (t.map (fun z => ‖z‖)).prod := prod_norm_nonneg t
    have hP1 : (t.map (fun z => ‖z‖)).prod ≤ 1 := prod_norm_le_one t ht
    have hT0 : 0 ≤ (t.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum := by
      refine Multiset.sum_nonneg ?_
      intro y hy
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.1 hy
      exact norm_nonneg _
    have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hpt := norm_mul_norm_inv_sub_conj_le hw
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    -- `r P (δ + T) = P (r δ) + r (P T) ≤ P(1-r²) + r(1-P²) ≤ 1 - r²P²`
    have hstep1 := mul_le_mul_of_nonneg_left hpt hP0
    have hstep2 := mul_le_mul_of_nonneg_left hIH hr0
    have hfac : 0 ≤ (1 - ‖w‖) * (1 - (t.map (fun z => ‖z‖)).prod)
        * (1 - ‖w‖ * (t.map (fun z => ‖z‖)).prod) := by
      have h3 : ‖w‖ * (t.map (fun z => ‖z‖)).prod ≤ 1 := by nlinarith
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [hstep1, hstep2, hfac]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Defs.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Definitions for the finite-range numerical claim

This file fixes the notation of the numerical claim `stat`, the one step of the proof that is
discharged by computation rather than by argument.  It contains definitions only; no statement
is made here.

`stat` cannot be stated in this file, because every other file in the development imports it
for the definitions below, and putting the claim at the bottom of the import graph would
prevent it from being proved.  It is stated and proved in `TaoSendov.FiniteRange.Cover`, so
auditing it means reading this file for the definitions and that one for the claim built from
them.

For where `stat` enters the proof as a whole, see `TaoSendov.Reduction.Main` and the repository
README; for the finite-range component on its own, see `docs/finite-range.md`.

## Background

In the blog post one argues by contradiction from a degree `n` polynomial with all zeroes
in the unit disk, a zero `0 ≤ a < 1`, and all critical points at distance `≥ 1` from `a`.
Writing `α := (n-1)(1-a²)/2` and `β(1) := 1 - 2ax + a²` (where `x` is the real part of the
mean of the reciprocal critical-point data), the post derives:

* `0 < β(1) < α/(3+α)` (the simplified polar inequality);
* `α ≤ 17` and an inequality `(1le)`, valid for `n ≥ 5`;
* the elimination of every degree `n ≥ 98` by an asymptotic argument.

Monotonicity in `β(1)` lets one replace `β(1)` by `α/(3+α)` in `(1le)`, which replaces
`a x` by `c` and `β(t)` by `Q t` below.  The resulting inequality is equation `stat` of the
post, namely `1 ≤ R n α`.  The upper bound `c ≤ a x` moreover forces the feasibility
constraint `c ^ 2 ≤ A`, which is what keeps `α` away from its formal upper limit `(n-1)/2`.

What is left open is that `stat` is infeasible on the remaining range

`5 ≤ n ≤ 97`,  `0 ≤ α ≤ 17`,  `c ^ 2 ≤ A`,

which is exactly `TaoSendov.finite_range` below.

## Main statements

* `TaoSendov.M`, `TaoSendov.A`, `TaoSendov.c`, `TaoSendov.Q`, `TaoSendov.R`: the quantities of `stat`.

The claim assembled from them lives in `TaoSendov.FiniteRange.Cover`:

* `TaoSendov.finite_range`: on the range above, `R n α < 1`;
* `TaoSendov.finite_range_le_100`: the same for `5 ≤ n ≤ 100`, which is what is actually
  proved — the finite certification was pushed past `97` to meet the large-degree argument;
* `TaoSendov.finite_range_contradiction`: consequently the post's equation `stat`,
  `1 ≤ R n α`, is contradictory on that range.  This is the form in which the claim is
  applied.

## Implementation notes

* `α = 0` is allowed, although the blog post has `α > 0` (an earlier inequality there was
  divided by `α`).  This makes the statement slightly stronger and is harmless: the bound
  extends continuously to `α = 0` and stays below `1` there.
* No upper bound on `α` in terms of `n` is assumed: `hfeas` already forces `0 ≤ A n α`,
  hence `α ≤ (n-1)/2`.
* The exponent `((n:ℝ) - 4) / 2` is a half-integer for odd `n`, so `Q n α t ^ _` is
  `Real.rpow`.  Under `hfeas` one has `0 ≤ Q n α t` for `0 ≤ t ≤ 1`, so no junk values of
  `rpow` at negative bases arise; the integrand is continuous, so no integrability
  hypothesis is needed either.

## Numerical diagnostics

These are *not* inputs to the proof, and must not be used as hypotheses; they are recorded
only to indicate the size of the margin.  Numerically, `R n α` attains a maximum of about
`0.8529` over the feasible range, at `n = 53`, `α = 17` — which remains inside the range
below, so shortening it does not make the claim easier.  For comparison, `R 5 0 ≈ 0.6458`
and `R 97 17 ≈ 0.2921`.  The feasibility constraint is binding at low degree: it caps
`α ≲ 1.68` when `n = 5` and `α ≲ 2.19` when `n = 6`, and only ceases to cut into
`[0, 17]` from `n = 36` onwards.

## References

* T. Tao, *A digestion of the proof of TaoSendov's conjecture*, blog post, 2026.
-/

namespace TaoSendov

/-- `M n = n - 1`.  All of the quantities below are naturally expressed in terms of it. -/
noncomputable def M (n : ℕ) : ℝ := (n : ℝ) - 1

/-- `A n α = a ^ 2 = 1 - 2α/(n-1)`, from the definition `α = (n-1)(1-a²)/2` of `α`.
The blog post's `a ^ 4` is therefore `A n α ^ 2`. -/
noncomputable def A (n : ℕ) (α : ℝ) : ℝ := 1 - 2 * α / M n

/-- `c n α = 1 - α/(n-1) - α/(2(3+α))`: the value taken by `a * x` after the substitution
of `α/(3+α)` for `β(1)`.  This is `c(α)` in the blog post. -/
noncomputable def c (n : ℕ) (α : ℝ) : ℝ := 1 - α / M n - α / (2 * (3 + α))

/-- `Q n α t = 1 - 2 c t + A t ^ 2`: the quadratic replacing `β(t) = 1 - 2 a x t + a² t²`
after the substitution of `α/(3+α)` for `β(1)`.  Note `Q n α 1 = α/(3+α)`. -/
noncomputable def Q (n : ℕ) (α : ℝ) (t : ℝ) : ℝ := 1 - 2 * c n α * t + A n α * t ^ 2

/-- `R n α` is the right-hand side of equation `stat` of the blog post:
`1/6 + 1/(4(3+α)) + 1/(2(n-1)) + 1/(4(n-1)(3+α))
    + a⁴ n (n-1) (n-2)/(4(3+α)) * ∫ t in 0..1, t³ (1 - 2c(α)t + a²t²) ^ ((n-4)/2)`. -/
noncomputable def R (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
    A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) *
      ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)

/-! The claim itself is stated and proved in `TaoSendov.FiniteRange.Cover`
(`TaoSendov.finite_range`, `TaoSendov.finite_range_contradiction`).  It cannot live here: this file
sits at the bottom of the import graph, since every other file needs these definitions. -/

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Common/Basic.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Basic properties of the quantities in the finite-range claim

Elementary facts about `TaoSendov.M`, `TaoSendov.A`, `TaoSendov.c` and `TaoSendov.Q`, used by every
degree-specific argument.  The two facts that matter are:

* `TaoSendov.Q_nonneg`: the feasibility constraint `c ^ 2 ≤ A` says exactly that `Q` is a sum
  of squares, hence nonnegative.  This is what makes the real power `Q ^ ((n-4)/2)`
  appearing in `TaoSendov.R` behave, and in particular avoids the junk values of `Real.rpow`
  at negative bases.
* `TaoSendov.Q_one`: `Q n α 1 = α / (3 + α)`, the value `B` prescribed by the simplified polar
  inequality of the blog post.  Since `Q n α 1 = 1 - 2 * c n α + A n α`, this pins down
  `A - 2 * c = B - 1 < 0`, which is what gives `TaoSendov.Q_le_one`.
-/

namespace TaoSendov

variable {n : ℕ} {α t : ℝ}

lemma M_pos (hn : 2 ≤ n) : 0 < M n := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [M]
  linarith

lemma three_add_pos (hα : 0 ≤ α) : (0 : ℝ) < 3 + α := by linarith

/-- `Q` written as a sum of squares.  Compare `β(t) = (1 - a x t) ^ 2 + a² t² (1 - x²)`
in the blog post. -/
lemma Q_eq (n : ℕ) (α t : ℝ) :
    Q n α t = (1 - c n α * t) ^ 2 + (A n α - c n α ^ 2) * t ^ 2 := by
  simp only [Q]
  ring

/-- Feasibility forces `a² ≥ 0`. -/
lemma A_nonneg (hfeas : c n α ^ 2 ≤ A n α) : 0 ≤ A n α :=
  le_trans (sq_nonneg _) hfeas

/-- Feasibility bounds `α` by `(n-1)/2`, simply because it forces `A = 1 - 2α/(n-1) ≥ 0`.

This crude consequence is all that the *numerical* step of any degree needs: on
`0 ≤ α ≤ min 17 ((n-1)/2)` the upper bounds for `R n α` used in this development stay below
`0.856` for every `5 ≤ n ≤ 97`.  The exact shape of the feasible region, which is cut out
by a quartic in `α`, is therefore never required by the polynomial certificates.

This must not be read as saying that `A ≥ 0` replaces feasibility everywhere.  It does not:
the odd-degree bound needs `0 ≤ Q n α t` on `[0,1]`, which is `TaoSendov.Q_nonneg` and uses the
full constraint `c ^ 2 ≤ A` — it does not follow from `A ≥ 0`.  Accordingly
`TaoSendov.integral_rpow_le` takes `hfeas` itself, and only the passage from the resulting
rational function to a polynomial positivity statement is weakened to `α ≤ M n / 2`.  For
even degrees the moment identity `TaoSendov.integral_moment` needs no hypothesis at all. -/
lemma alpha_le_half_M (hn : 2 ≤ n) (hfeas : c n α ^ 2 ≤ A n α) : α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  have hA : 0 ≤ A n α := A_nonneg hfeas
  rw [A] at hA
  have h : 2 * α / M n ≤ 1 := by linarith
  rw [div_le_one hM] at h
  linarith

lemma Q_nonneg (hfeas : c n α ^ 2 ≤ A n α) (t : ℝ) : 0 ≤ Q n α t := by
  rw [Q_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))

/-- `Q n α 1 = B = α / (3 + α)`: the substituted quadratic takes at `t = 1` the value that
the simplified polar inequality `β(1) < α / (3 + α)` prescribes. -/
lemma Q_one (hn : 2 ≤ n) (hα : 0 ≤ α) : Q n α 1 = α / (3 + α) := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [Q, c, A]
  field_simp
  ring

/-- `Q` is convex with `Q 0 = 1` and `Q 1 = B ≤ 1`, hence bounded by `1` on `[0,1]`.

Only `0 ≤ c` is needed, not `0 ≤ A`: writing `Q t - 1 = t (A t - 2c)`, the identity
`Q 1 = B < 1` gives `A ≤ 2c` outright, and then `A t ≤ 2c` holds whether `A` is nonnegative
(as `A t ≤ A`) or negative (as `A t ≤ 0 ≤ 2c`).  That matters for batches of degrees whose
`α`-range reaches past `(n₀-1)/2`, where `A n₀ α` can be negative. -/
lemma Q_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) (hc : 0 ≤ c n α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ 1 := by
  have hB : Q n α 1 ≤ 1 := by
    rw [Q_one hn hα, div_le_one (three_add_pos hα)]
    linarith
  have hAc : A n α - 2 * c n α ≤ 0 := by
    simp only [Q] at hB
    linarith
  have h5 : A n α * t - 2 * c n α ≤ 0 := by
    rcases le_total 0 (A n α) with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [Q]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]

/-- Feasibility gives `α ≤ (n-1)/2`, and hence `c ≥ (1-B)/2 > 0`. -/
lemma c_pos_of_le_half_M (hn : 2 ≤ n) (hα : 0 ≤ α) (hhalf : α ≤ M n / 2) : 0 < c n α := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have h1 : α / M n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hM (by norm_num)]
    linarith
  have h2 : α / (2 * (3 + α)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  simp only [c]
  linarith

/-- The coefficient multiplying the integral in `TaoSendov.R` is nonnegative, so any upper
bound for the integral yields an upper bound for `R`.  This is how each degree replaces its
integral by an explicit rational function. -/
lemma R_le_of_integral_le (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
      A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoef : 0 ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      (M_pos hn).le) hn2) (by linarith)
  rw [R]
  have := mul_le_mul_of_nonneg_left hJ hcoef
  linarith

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Common/Rpow.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Real powers, shared by both ranges

The exponent `(n-4)/2` in `TaoSendov.R` is a real exponent, so both halves of the development —
the finite range and the large-degree argument — manipulate `Real.rpow`, and both need the
integrand `t ^ 3 * Q ^ e` to be continuous in order to integrate it.  Those facts have no
connection to either strategy, so they live here rather than in the strategy-specific files.

In particular:

* the finite range uses `TaoSendov.continuous_integrand` to compare integrals in
  `TaoSendov.integral_rpow_le`, and the large-degree argument needs the same fact to split
  `∫₀¹` at the vertex of `Q`;
* `TaoSendov.rpow_add_nat_pos` is used by the Beta integral, and the same splitting of a real
  power into a real and a natural part is what turns `B ^ ((n-4)/2)` into `B ^ k * √B` in
  the large-degree reduction.
-/

namespace TaoSendov

open MeasureTheory

/-- `∫₀¹ xˢ dx = 1/(s+1)` for `s > -1`. -/
lemma integral_rpow_zero_one {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring

/-- `x ^ (s + m) = x ^ s * x ^ m` for positive `x` and a natural `m`. -/
lemma rpow_add_nat_pos {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by
  rw [Real.rpow_add hx, Real.rpow_natCast]

/-- `fun x ↦ x ^ e` is continuous on all of `ℝ` for a nonnegative real exponent `e`.  The
exponent must be nonnegative: at `e < 0` the function blows up at the origin. -/
lemma continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e :=
  continuous_iff_continuousAt.2 fun x => Real.continuousAt_rpow_const x e (Or.inr he)

/-- The integrand of `TaoSendov.R` is continuous, hence interval integrable.  Needed wherever an
integral involving `Q ^ e` is split or compared. -/
lemma continuous_integrand (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by
  have hQ : Continuous fun t : ℝ => Q n α t := by
    simp only [Q]; fun_prop
  have h3 : Continuous fun t : ℝ => t ^ 3 := by fun_prop
  exact h3.mul ((continuous_rpow_const he).comp hQ)

/-- On `[0,1]` a real power is decreasing in the exponent: `x ^ s ≤ x ^ t` for `t ≤ s`.
Used to drop the `√B` from `B ^ (k + 1/2)`. -/
lemma rpow_le_rpow_of_le_one {x s t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hts : t ≤ s) :
    x ^ s ≤ x ^ t :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hts

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Common/Quadratic.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The quadratic `1 - 2ct + At²`

Two quadratics drive the whole development, and they are the same object with different
parameters:

* `β(t) = 1 - 2axt + a²t²`, the quantity the blog post's inequalities are stated in;
* `Q n α t = 1 - 2c(α)t + a²t²`, what `β` becomes after `β(1)` is replaced by `α/(3+α)`.

So the facts about them — nonnegativity under feasibility, the chord bound below the vertex,
monotonicity above it — are proved once here for

  `QQ c A t = 1 - 2ct + At²`,

and `TaoSendov.Q n α t = QQ (c n α) (A n α) t` holds by `rfl`.

Note which hypothesis each fact needs.  Nonnegativity is exactly feasibility `c² ≤ A`, since
`QQ = (1-ct)² + (A-c²)t²`.  The bound `QQ ≤ 1` on `[0,1]` needs only `0 ≤ c` together with
`QQ 1 ≤ 1`: writing `QQ t - 1 = t(At - 2c)`, the value at `t = 1` already gives `A ≤ 2c`, and
then `At ≤ 2c` whether `A` is nonnegative (as `At ≤ A`) or negative (as `At ≤ 0 ≤ 2c`).  That
matters, because `A` is genuinely negative in parts of the range.

## Main statements

* `TaoSendov.QQ_nonneg`, `TaoSendov.QQ_le_one`;
* `TaoSendov.QQ_le_chord`: `QQ t ≤ 1 - ct` below the vertex;
* `TaoSendov.QQ_le_at_one`: `QQ t ≤ QQ 1` above it.
-/

namespace TaoSendov

/-- The quadratic `1 - 2ct + At²`. -/
noncomputable def QQ (c A t : ℝ) : ℝ := 1 - 2 * c * t + A * t ^ 2

/-- `TaoSendov.Q` is an instance of `TaoSendov.QQ`.  Stated before the section variables below,
which deliberately shadow `TaoSendov.c` and `TaoSendov.A`. -/
lemma Q_eq_QQ (n : ℕ) (α t : ℝ) : Q n α t = QQ (c n α) (A n α) t := rfl

variable {c A t : ℝ}

/-- `QQ` as a sum of squares. -/
lemma QQ_eq (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by
  simp only [QQ]; ring

lemma QQ_zero (c A : ℝ) : QQ c A 0 = 1 := by simp [QQ]

lemma QQ_one (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by simp [QQ]

/-- Feasibility `c² ≤ A` says exactly that `QQ` is a sum of squares. -/
lemma QQ_nonneg (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by
  rw [QQ_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))

/-- `QQ ≤ 1` on `[0,1]`, from `QQ 1 ≤ 1` and `0 ≤ c` alone. -/
lemma QQ_le_one (hc : 0 ≤ c) (hB : QQ c A 1 ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ c A t ≤ 1 := by
  have hAc : A - 2 * c ≤ 0 := by rw [QQ_one] at hB; linarith
  have h5 : A * t - 2 * c ≤ 0 := by
    rcases le_total 0 A with h | h
    · nlinarith [mul_le_of_le_one_right h ht1]
    · nlinarith [mul_nonneg ht0 (neg_nonneg.2 h)]
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 h5)]

/-- Below the vertex, `QQ` lies under the chord `1 - ct`. -/
lemma QQ_le_chord (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]

/-- Above the vertex, `QQ` is increasing, so it is at most its value at `t = 1`. -/
lemma QQ_le_at_one (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by
  have hkey : 0 ≤ A * (1 + t) - 2 * c := by nlinarith [ht, hA, ht1]
  simp only [QQ]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]

/-- `t ^ k * QQ ^ e` is continuous, hence interval integrable: needed wherever an integral of
this shape is split or compared. -/
lemma continuous_pow_mul_QQ (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by
  have hQ : Continuous fun t : ℝ => QQ c A t := by simp only [QQ]; fun_prop
  have hk : Continuous fun t : ℝ => t ^ k := by fun_prop
  exact hk.mul ((continuous_rpow_const he).comp hQ)

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Common/Chord.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Chord bounds and the Beta integrals

Both halves of the argument replace a power of the quadratic by a power of its chord and
integrate.  The blog post does this twice, with different weights:

* with weight `t`, to bound `∫₀¹ t β(t)^{(n-2)/2}` in the proof of `α ≤ 17`;
* with weight `t³`, to bound `∫₀¹ t³ Q^{(n-4)/2}` in the large-degree argument.

Both reduce to a Beta integral, and the split is the same in both cases, so it is proved once:
`TaoSendov.integral_le_tail_gen` bounds `∫₀¹ t^k QQ^r` by the chord integral over `[0,1/c]` plus
`QQ 1 ^ r / (k+1)`, for any natural `k`, leaving the Beta value to be substituted afterwards.

The informal write-up instead uses `QQ ≤ exp(-ct)` and the Gamma integral
`∫₀^∞ t³ e^{-rct} dt = 6/(rc)⁴`.  The Beta route is preferable in Lean — no improper integral
and no `Real.exp` — and is strictly sharper, since
`6/((s+1)(s+2)(s+3)(s+4)) ≤ 6/s⁴` (`TaoSendov.beta_le_six_div_pow`), so every numerical constant
downstream of the Gamma bound stays valid.

## Main statements

* `TaoSendov.integral_lin_mul_rpow`, `TaoSendov.integral_cube_mul_rpow`: the Beta values;
* `TaoSendov.integral_chord_lin`, `TaoSendov.integral_chord_pow`: the same, scaled to `[0,1/c]`;
* `TaoSendov.integral_le_tail_gen`: the split, for an arbitrary weight `t^k`;
* `TaoSendov.integral_le_tail_lin`, `TaoSendov.integral_le_tail_cube`: the two instances used.
-/

namespace TaoSendov

open MeasureTheory

/-! ### The Beta integrals -/

/-- The Beta integral `B(2, s+1)`. -/
lemma integral_lin_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s) = 1 / ((s + 1) * (s + 2)) := by
  have hrefl : (∫ x in (0 : ℝ)..1, x * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) * x ^ s = x ^ s - x ^ (s + (1 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (s + (1 : ℕ))) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_rpow'
    push_cast
    linarith
  rw [intervalIntegral.integral_sub hi' hi, integral_rpow_zero_one (by linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

/-- The Beta integral `B(4, s+1)`. -/
lemma integral_cube_mul_rpow {s : ℝ} (hs : 0 < s) :
    (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = 6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) := by
  have h1 : (0 : ℝ) < s + 1 := by linarith
  have hrefl : (∫ x in (0 : ℝ)..1, x ^ 3 * (1 - x) ^ s)
      = ∫ x in (0 : ℝ)..1, (1 - x) ^ 3 * x ^ s := by
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun y : ℝ => (1 - y) ^ 3 * y ^ s) 1
    simpa using this
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (1 - x) ^ 3 * x ^ s
        = x ^ s - 3 * x ^ (s + (1 : ℕ)) + 3 * x ^ (s + (2 : ℕ)) - x ^ (s + (3 : ℕ)) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]
      rw [Real.zero_rpow (by positivity), Real.zero_rpow (by push_cast; linarith),
        Real.zero_rpow (by push_cast; linarith), Real.zero_rpow (by push_cast; linarith)]
      ring
    · rw [rpow_add_nat_pos h, rpow_add_nat_pos h, rpow_add_nat_pos h]
      ring
  rw [hrefl, intervalIntegral.integral_congr hcongr]
  have hi' : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi : ∀ m : ℕ, IntervalIntegrable (fun x : ℝ => x ^ (s + (m : ℕ))) volume 0 1 := by
    intro m
    apply intervalIntegral.intervalIntegrable_rpow'
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc : ∀ (a : ℝ) (m : ℕ),
      IntervalIntegrable (fun x : ℝ => a * x ^ (s + (m : ℕ))) volume 0 1 :=
    fun a m => (hi m).const_mul a
  rw [intervalIntegral.integral_sub ((hi'.sub (hc 3 1)).add (hc 3 2)) (hi 3),
    intervalIntegral.integral_add (hi'.sub (hc 3 1)) (hc 3 2),
    intervalIntegral.integral_sub hi' (hc 3 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow_zero_one (by linarith), integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith),
    integral_rpow_zero_one (by push_cast; linarith)]
  push_cast
  field_simp
  ring

/-- The Beta value is at most `6/s⁴`; this is the form the informal argument uses, obtained
there from the Gamma integral. -/
lemma beta_le_six_div_pow {s : ℝ} (hs : 0 < s) :
    6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) ≤ 6 / s ^ 4 := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hs.le, sq_nonneg s, sq_nonneg (s + 1)]

/-- The chord integral with weight `t`, over `[0, 1/c]`. -/
lemma integral_chord_lin {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t * (1 - c * t) ^ s) = 1 / (c ^ 2 * ((s + 1) * (s + 2))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) * (1 - c * t) ^ s)
      = fun t : ℝ => t * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) * (1 - y) ^ s)
      = fun y : ℝ => (1 / c) * (y * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_lin_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp

/-- The chord integral with weight `t³`, over `[0, 1/c]`. -/
lemma integral_chord_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..1 / c, t ^ 3 * (1 - c * t) ^ s)
      = 6 / (c ^ 4 * ((s + 1) * (s + 2) * (s + 3) * (s + 4))) := by
  have hc' : c ≠ 0 := hc.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / c)
    (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s) hc'
  have hfun : (fun t : ℝ => ((c * t) / c) ^ 3 * (1 - c * t) ^ s)
      = fun t : ℝ => t ^ 3 * (1 - c * t) ^ s := by
    funext t
    rw [mul_div_cancel_left₀ t hc']
  simp only [hfun] at h
  rw [show c * (1 / c) = 1 by field_simp, mul_zero] at h
  have hg : (fun y : ℝ => (y / c) ^ 3 * (1 - y) ^ s)
      = fun y : ℝ => (1 / c ^ 3) * (y ^ 3 * (1 - y) ^ s) := by
    funext y
    field_simp
  rw [hg, intervalIntegral.integral_const_mul, integral_cube_mul_rpow hs] at h
  rw [h]
  simp only [smul_eq_mul]
  field_simp

/-! ### The split -/

/-- **The tail bound, for an arbitrary weight `t^k`.**  `QQ` is a convex parabola with vertex
at `c/A`; below the vertex it lies under the chord `1 - ct`, above it it is increasing and so
at most `QQ 1`.  Splitting `∫₀¹` there gives the bound.

Two points shape the proof.  The chord bound needs `1 - ct ≥ 0`, which comes from
`ct ≤ c²/A ≤ 1` — feasibility again.  And the vertex may lie outside `[0,1]`: the split is
made at `s = min (c/A) 1`, after which the first piece is enlarged to `[0, 1/c]` (legitimate
because `s ≤ 1/c`, using `c ≤ 1` when the vertex is to the right) and the second piece is
empty when the vertex is beyond `1`. -/
theorem integral_le_tail_gen {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c A t ^ r)
      ≤ (∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ r) + QQ c A 1 ^ r / (k + 1) := by
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hfeas
  set t₀ : ℝ := c / A with ht₀def
  have ht₀pos : 0 < t₀ := by positivity
  set s : ℝ := min t₀ 1 with hsdef
  have hs0 : 0 < s := lt_min ht₀pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hcont : Continuous fun u : ℝ => u ^ k * QQ c A u ^ r := continuous_pow_mul_QQ c A k hr.le
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => u ^ k * QQ c A u ^ r) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hchordcont : Continuous fun u : ℝ => u ^ k * (1 - c * u) ^ r :=
    (by fun_prop : Continuous fun u : ℝ => u ^ k).mul
      ((continuous_rpow_const hr.le).comp (by fun_prop))
  have hsc : s ≤ 1 / c := by
    rcases min_cases t₀ 1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hsdef, h, ht₀def, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hA]
      nlinarith [hfeas]
    · rw [hsdef, h, le_div_iff₀ hc]
      linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s 1)]
  have hfirst : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
      ≤ ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r := by
    have hle : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_mono_on hs0.le (hint 0 s)
        (hchordcont.intervalIntegrable _ _) ?_
      intro u hu
      obtain ⟨hu0, hus⟩ := hu
      have huv : A * u ≤ c := by
        have hut : u ≤ t₀ := le_trans hus (min_le_left _ _)
        rw [ht₀def, le_div_iff₀ hA] at hut
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (QQ_nonneg hfeas u) (QQ_le_chord hu0 huv) hr.le) (pow_nonneg hu0 k)
    refine hle.trans ?_
    have hrest : 0 ≤ ∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_nonneg hsc ?_
      intro u hu
      have : 0 ≤ 1 - c * u := by
        have := hu.2
        rw [le_div_iff₀ hc] at this
        linarith
      exact mul_nonneg (pow_nonneg (le_trans hs0.le hu.1) k) (Real.rpow_nonneg this _)
    have hadd : (∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r)
        + (∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r)
        = ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r :=
      intervalIntegral.integral_add_adjacent_intervals
        (hchordcont.intervalIntegrable 0 s) (hchordcont.intervalIntegrable s (1 / c))
    linarith
  have hsecond : (∫ u in s..1, u ^ k * QQ c A u ^ r) ≤ QQ c A 1 ^ r / (k + 1) := by
    have hBnn : (0 : ℝ) ≤ QQ c A 1 ^ r := Real.rpow_nonneg (QQ_nonneg hfeas 1) _
    have hQB : ∀ u ∈ Set.Icc s 1, QQ c A u ≤ QQ c A 1 := by
      intro u hu
      rcases le_or_gt t₀ u with h | h
      · rw [ht₀def, div_le_iff₀ hA] at h
        exact QQ_le_at_one hA.le (by linarith) hu.2
      · have hu1 : u = 1 := by
          rcases min_cases t₀ 1 with ⟨he, _⟩ | ⟨he, _⟩
          · rw [hsdef, he] at hu; linarith [hu.1]
          · rw [hsdef, he] at hu; linarith [hu.1, hu.2]
        rw [hu1]
    have hle : (∫ u in s..1, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in s..1, QQ c A 1 ^ r * u ^ k := by
      refine intervalIntegral.integral_mono_on hs1 (hint s 1)
        ((by fun_prop : Continuous fun u : ℝ => QQ c A 1 ^ r * u ^ k).intervalIntegrable _ _) ?_
      intro u hu
      have := Real.rpow_le_rpow (QQ_nonneg hfeas u) (hQB u hu) hr.le
      nlinarith [pow_nonneg (le_trans hs0.le hu.1) k, this, hBnn]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hsk : (0 : ℝ) ≤ s ^ (k + 1) := pow_nonneg hs0.le _
    rw [one_pow, ← mul_div_assoc]
    gcongr
    nlinarith [mul_nonneg hBnn hsk]
  linarith

/-- The integral is antitone in `c`: raising `c` lowers `QQ` pointwise on `[0,1]`.  Note that
nonnegativity is only needed for the *larger* `c`; for the smaller one it comes free from the
pointwise comparison.  (`TaoSendov.integral_anti` in `FiniteRange.Batch` is the same trick applied
to the degree instead.) -/
lemma integral_QQ_anti {c₁ c₂ A : ℝ} (hle : c₁ ≤ c₂) (hfeas : c₂ ^ 2 ≤ A) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c₂ A t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * QQ c₁ A t ^ r := by
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_pow_mul_QQ c₂ A k hr).intervalIntegrable _ _)
    ((continuous_pow_mul_QQ c₁ A k hr).intervalIntegrable _ _) ?_
  intro u hu
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu.1 k)
  refine Real.rpow_le_rpow (QQ_nonneg hfeas u) ?_ hr
  simp only [QQ]
  nlinarith [hu.1, hle]

/-- The instance with weight `t`, used for `α ≤ 17`. -/
theorem integral_le_tail_lin {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t * QQ c A t ^ r)
      ≤ 1 / (c ^ 2 * ((r + 1) * (r + 2))) + QQ c A 1 ^ r / 2 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 1
  simp only [pow_one] at h
  rw [integral_chord_lin hr hc, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h
  exact h

/-- The instance with weight `t³`, used by the large-degree argument. -/
theorem integral_le_tail_cube {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * QQ c A t ^ r)
      ≤ 6 / (c ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4))) + QQ c A 1 ^ r / 4 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 3
  rw [integral_chord_pow hr hc, show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
  exact h

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Setup.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The raw inequalities, and the dictionary between them and `TaoSendov.R`

`TaoSendov.stat_lt_one` refutes equation `stat` of the blog post.  `stat` is itself deduced there
from two inequalities that come out of the complex-analytic part of the argument:

* the **raw polar inequality** `(1Q)`, `1 ≤ ∫₀¹ P(t)^((n-1)/2) dt` with
  `P(t) = a² + 2atx(1-a²) + t²(1-a²)²`;
* the **raw origin inequality** `(origin-exact)`,
  `2α + ax ≤ (1-x²)/(2(n-1)) + a²n(n-1) ∫₀¹ t β(t)^((n-2)/2) dt`.

Both are statements about two real numbers `a ∈ (0,1)` and `x ∈ [-1,1]` and a degree `n`; no
polynomial, no complex number and no `q_j` survives into them.  That is what makes the next
target — that the two are not simultaneously satisfiable for `n ≥ 5` — a self-contained
real-variable statement.

This file fixes `P` and records the dictionary.  The key entry is that `α` and `a` determine
each other: with `α = (n-1)(1-a²)/2` one has `A n α = a²` *exactly*, so the `A` of
`TaoSendov.Defs` and the `a²` of the blog post are the same thing, and `β(t)` is
`TaoSendov.QQ (a*x) (a^2) t` while `Q n α t` is `TaoSendov.QQ (c n α) (A n α) t`.

## Main statements

* `TaoSendov.Ppolar_eq`: `P` as a sum of squares, hence nonnegative for `|x| ≤ 1`;
* `TaoSendov.A_eq_sq`: `A n α = a²`;
* `TaoSendov.alpha_pos`, `TaoSendov.alpha_le_half`: the range of `α`.
-/

namespace TaoSendov

/-- The integrand of the raw polar inequality `(1Q)`. -/
noncomputable def Ppolar (a x t : ℝ) : ℝ :=
  a ^ 2 + 2 * a * t * x * (1 - a ^ 2) + t ^ 2 * (1 - a ^ 2) ^ 2

variable {n : ℕ} {a x t α : ℝ}

/-- `P` is a sum of squares once `|x| ≤ 1`; this is the same computation that makes
`TaoSendov.QQ_nonneg` work. -/
lemma Ppolar_eq (a x t : ℝ) :
    Ppolar a x t = (a + t * (1 - a ^ 2) * x) ^ 2 + t ^ 2 * (1 - a ^ 2) ^ 2 * (1 - x ^ 2) := by
  simp only [Ppolar]; ring

lemma Ppolar_nonneg (hx : x ^ 2 ≤ 1) (a t : ℝ) : 0 ≤ Ppolar a x t := by
  rw [Ppolar_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))

lemma continuous_Ppolar (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by
  simp only [Ppolar]; fun_prop

/-- With `α = (n-1)(1-a²)/2`, the `A` of `TaoSendov.Defs` is exactly `a²`. -/
lemma A_eq_sq (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [A, hα]
  field_simp
  ring

lemma alpha_pos (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  have : 0 < 1 - a ^ 2 := by nlinarith
  positivity

lemma alpha_le_half (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  nlinarith [sq_nonneg a]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/Polar.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The polar inequality, up to the branch point

The polar identity says

  `(∏ q) ∏ⱼ (1 - a zⱼ) = n ∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt`,   `(∏ q) ∏ⱼ (a - zⱼ) = n`.

The Möbius estimate `|a - zⱼ| ≤ |1 - a zⱼ|`, valid because `zⱼ` lies in the closed unit disk
and `a` is real with `|a| ≤ 1`, therefore gives

  `n = |(∏ q) ∏ (a - zⱼ)| ≤ |(∏ q) ∏ (1 - a zⱼ)| = n |∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt|`,

and after the integral triangle inequality

  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.                                    (⋆)

**`(⋆)` is the branch point of the whole argument.**  The high-degree route relaxes it by
AM–GM into the raw polar inequality `(1Q)` of `TaoSendov.Reduction.Setup`; the low-degree route
for `2 ≤ n ≤ 5` (see `docs/plan-low-degrees.md`) instead bounds each factor by `a + (1-a²)t`
and integrates a quartic.  Neither may be folded into the other, so `(⋆)` is stated on its own.

Note that no division occurs anywhere: splitting the blog post's quotient
`∏(1-azⱼ)/(a-zⱼ)` into its numerator and denominator identities is what makes that possible,
and `p'(a) ≠ 0` is never needed.

## Main statements

* `TaoSendov.norm_sub_le_norm_one_sub_mul`: the Möbius estimate;
* `TaoSendov.one_le_integral_prod_norm`: the branch point `(⋆)`.
-/

namespace TaoSendov

open Polynomial MeasureTheory

/-! ### The Möbius estimate -/

/-- `|a - z| ≤ |1 - a z|` for real `a` with `|a| ≤ 1` and `z` in the closed unit disk.  The
difference of squares is `(1-a²)(1-|z|²)`, which is why `a` must be real: for complex `a` the
cross terms contribute `(conj a - a)(z - conj z)`, which need not vanish. -/
lemma norm_sub_le_norm_one_sub_mul {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hkey : Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z)
      = (1 - a ^ 2) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.1 ha
    nlinarith [this.1, this.2]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hdiff : 0 ≤ Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z) := by
    rw [hkey]
    have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 - Complex.normSq z := by linarith
    positivity
  have hsq : ‖(a : ℂ) - z‖ ^ 2 ≤ ‖1 - (a : ℂ) * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z), hsq]

/-! ### Products of norms over a multiset -/

lemma norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih => simp [ih]

lemma prod_map_le_of_le {s : Multiset ℂ} {f g : ℂ → ℂ} (h : ∀ w ∈ s, ‖f w‖ ≤ ‖g w‖) :
    (s.map (fun w => ‖f w‖)).prod ≤ (s.map (fun w => ‖g w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw := h w (Multiset.mem_cons_self w t)
    have ht : ∀ u ∈ t, ‖f u‖ ≤ ‖g u‖ := fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hnn : (0 : ℝ) ≤ (t.map (fun u => ‖f u‖)).prod :=
      Multiset.prod_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact norm_nonneg _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hw (ih ht) hnn (norm_nonneg _)

/-! ### The branch point -/

/-- Norms distribute over a mapped multiset product. -/
lemma norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by
  rw [norm_multiset_prod, Multiset.map_map]
  rfl

lemma prod_map_norm_nonneg (s : Multiset ℂ) (f : ℂ → ℂ) :
    0 ≤ (s.map (fun w => ‖f w‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg _

/-- **The branch point `(⋆)`.**  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.

The high-degree argument relaxes this by AM–GM to the raw polar inequality; the low-degree
argument bounds each factor by `a + (1-a²)t`.  It is stated separately so that neither route
has to reproduce the other's work. -/
theorem one_le_integral_prod_norm {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- the Möbius estimate, multiplied over the multiset
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  -- take norms in the two identities
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  -- so the integral has norm at least one
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    nlinarith [hstep, hnpos]
  -- and the triangle inequality moves the norm inside
  refine h3.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
  refine intervalIntegral.integral_congr ?_
  intro t _
  simp only []
  exact norm_prod_map q _

/-! ### The AM–GM relaxation to `(1Q)` -/

/-- `‖a + s v‖² = a² + 2 a s Re v + s² ‖v‖²` for real `a`, `s`. -/
lemma norm_sq_add_real_mul (a s : ℝ) (v : ℂ) :
    ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 = a ^ 2 + 2 * a * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma prod_map_sq (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map (fun v => f v ^ 2)).prod = ((s.map f).prod) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    ring

/-- Splitting `∑ⱼ ‖a + s qⱼ‖²` into its three pieces. -/
lemma sum_norm_sq_split (a s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) * a ^ 2 + 2 * a * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_add_real_mul]
    push_cast
    ring

lemma sum_norm_sq_le_card (q : Multiset ℂ) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    (q.map (fun v => ‖v‖ ^ 2)).sum ≤ (q.card : ℝ) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    have hv := hq1 v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq1 u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    nlinarith [ih ht, norm_nonneg v]

lemma continuous_prod_norm (a : ℝ) (q : Multiset ℂ) :
    Continuous fun t : ℝ =>
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ =>
      ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖).mul ih

/-- **The pointwise quadratic-mean bound.**  `∏ⱼ |a + t(1-a²)qⱼ| ≤ P(t)^{(n-1)/2)}`, by AM–GM
on the squares followed by `∑ ‖qⱼ‖² ≤ n-1`. -/
lemma prod_norm_le_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
      ≤ Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hNpos : (0 : ℝ) < (q.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := t * (1 - a ^ 2) with hs
  have hcast : ∀ v : ℂ, (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v = (a : ℂ) + (s : ℂ) * v := by
    intro v
    rw [hs]
    push_cast
    ring
  simp only [hcast]
  -- the product of squares
  set P : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖)).prod with hP
  have hP0 : 0 ≤ P := prod_map_norm_nonneg q _
  have hM0 : ∀ v ∈ q, (0 : ℝ) ≤ ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 := fun v _ => sq_nonneg _
  have hamgm := Multiset.prod_le_mean_pow (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2))
    (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq] at hamgm
  set M : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum / (q.card : ℝ) with hM
  -- `M ≤ P(t)`
  have hMle : M ≤ Ppolar a x t := by
    rw [hM, div_le_iff₀ hNpos]
    have hsplit := sum_norm_sq_split a s q
    have hcard2 := sum_norm_sq_le_card q hq1
    rw [hsplit, hx, hNcast]
    have hPp : Ppolar a x t = a ^ 2 + 2 * a * s * x + s ^ 2 := by
      rw [Ppolar, hs]; ring
    rw [hPp]
    nlinarith [hcard2, hNcast, sq_nonneg s, hNpos]
  have hM0' : 0 ≤ M := by
    rw [hM]
    apply div_nonneg _ (le_of_lt hNpos)
    exact Multiset.sum_nonneg (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  -- take square roots
  have hexp : ((q.card : ℕ) : ℝ) / 2 = ((n : ℝ) - 1) / 2 := by rw [hNcast]
  have hb : (0 : ℝ) ≤ Ppolar a x t := le_trans hM0' hMle
  have hsq : (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) ^ 2 = Ppolar a x t ^ (q.card : ℕ) := by
    rw [← Real.rpow_natCast (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast (Ppolar a x t) q.card, hNcast]
    congr 1
    push_cast
    ring
  have hchain : P ^ 2 ≤ Ppolar a x t ^ (q.card : ℕ) := by
    refine hamgm.trans ?_
    exact pow_le_pow_left₀ hM0' hMle _
  rw [← hsq] at hchain
  nlinarith [hchain, hP0, Real.rpow_nonneg (le_trans hM0' hMle) (((n : ℝ) - 1) / 2)]

/-- **The raw polar inequality `(1Q)`.** -/
theorem one_le_integral_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine hstar.trans (intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    (((continuous_rpow_const he).comp (continuous_Ppolar a x)).intervalIntegrable _ _) ?_)
  intro u _
  exact prod_norm_le_Ppolar hn hqcard hq1 hx

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/Origin.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The origin inequality: the pointwise estimate and `(tri)`

The origin argument controls `F(t) = ∏ⱼ (1 - a t qⱼ)` through its derivative,

  `F'(t) = -(n-1) a (x+iy) F(t) - a² t ∑ⱼ qⱼ² ∏_{k≠j} (1 - a t q_k)`,

whose error term is bounded by `a² t (n-1) β(t)^{(n-2)/2}`.  Integrating that against the
fundamental theorem of calculus and `F(0) = 1` gives the triangle inequality `(tri)`.  The
`J`-algebra that turns `(tri)` into `(origin-exact)` follows in a later file.

The error bound has three steps, in increasing order of depth:

* `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, the same expansion that produced the quadratic mean in the
  polar channel — this is where `x` enters;
* Cauchy–Schwarz, `(∑ b)² ≤ N ∑ b²`;
* **Maclaurin's inequality**, `∑ⱼ ∏_{k≠j} bₖ ≤ N (mean b)^{N-1}` — the one ingredient absent
  from Mathlib, proved in `TaoSendov.Analytic.Maclaurin`.

The blog post applies Maclaurin to `(1/(n-1)) ∑ⱼ ∏_{k≠j} |1 - a t q_k|` and then Cauchy–Schwarz;
the order is immaterial and it is done the same way here.

A note on the bookkeeping.  The quantity `∑ⱼ ∏_{k≠j} f(qⱼ)` is written as a sum over erasures
of `q`, whereas `Multiset.esymm` — which Maclaurin is stated for — is a sum over sub-multisets
of the *image* `q.map f`.  Rather than relate erasure and `map` directly, which needs `f`
injective, the two are matched through the recurrence they share.

## Main statements

* `TaoSendov.sumEraseProdMap_eq_esymm`: the two forms of `∑ⱼ ∏_{k≠j}` agree;
* `TaoSendov.sum_norm_sq_one_sub_le`: `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`;
* `TaoSendov.sumEraseProdMap_norm_le`: the error bound `(n-1) β(t)^{(n-2)/2}`;
* `TaoSendov.hasDerivAt_Fprod`: `F'(t) = -a ∑ⱼ qⱼ ∏_{k≠j} (1 - a t q_k)`;
* `TaoSendov.norm_deriv_add_le`: `‖F'(t) + (n-1) a (x+iy) F(t)‖ ≤ a² t (n-1) β(t)^{(n-2)/2}`;
* `TaoSendov.one_le_tri`: the triangle inequality `(tri)`.

The derivative is assembled from a *weighted* erasure sum `sumEraseProdC q g f = ∑ⱼ g(qⱼ)
∏_{k≠j} f(q_k)`: taking `g = id` gives `F'` itself, and the identity `1 - (1 - a t qⱼ) = a t qⱼ`
splits that into the main term `(∑ⱼ qⱼ) F(t)` plus `a t` times the case `g = (· ^ 2)`, which is
the residual actually being estimated.
-/

namespace TaoSendov

/-! ### `∑ⱼ ∏_{k≠j}` over erasures, and `esymm` -/

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} f(sₖ)`, as a sum over erasures of `s`. -/
noncomputable def sumEraseProdMap {α : Type*} (s : Multiset α) (f : α → ℝ) : ℝ :=
  (s.map (fun j => ((s.erase j).map f).prod)).sum

open scoped Classical in
lemma sumEraseProdMap_cons {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by
  simp only [sumEraseProdMap, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]

/-- The erasure form and `Multiset.esymm` agree, matched through their common recurrence. -/
theorem sumEraseProdMap_eq_esymm {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons v t ih =>
    intro f _
    rcases eq_or_ne t 0 with rfl | ht
    · simp [sumEraseProdMap, Multiset.esymm]
    · rw [sumEraseProdMap_cons, ih f ht, Multiset.map_cons, Multiset.card_cons]
      rw [show (t.map f).card + 1 - 1 = (t.map f).card from by omega]
      rw [esymm_card_cons (f v) (t.map f) (by simpa using ht)]

/-! ### The quadratic mean -/

/-- `‖1 + s v‖² = 1 + 2 s Re v + s² ‖v‖²` for real `s`. -/
lemma norm_sq_one_add_real_mul (s : ℝ) (v : ℂ) :
    ‖1 + (s : ℂ) * v‖ ^ 2 = 1 + 2 * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma sum_norm_sq_one_sub_split (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_one_add_real_mul]
    push_cast
    ring

/-- `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, where `β(t) = 1 - 2 a x t + a² t²`. -/
theorem sum_norm_sq_one_sub_le {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub hn]
    ring
  have hcast : ∀ v : ℂ, 1 - (a : ℂ) * (t : ℂ) * v = 1 + ((-(a * t) : ℝ) : ℂ) * v := by
    intro v
    push_cast
    ring
  simp only [hcast]
  rw [sum_norm_sq_one_sub_split, hx, hNcast]
  have hsum2 := sum_norm_sq_le_card q hq1
  rw [hNcast] at hsum2
  simp only [QQ]
  nlinarith [hsum2, sq_nonneg (a * t)]

/-! ### Cauchy–Schwarz and the error bound -/

lemma sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have hb := hs b (Multiset.mem_cons_self b t)
    have ht : ∀ u ∈ t, 0 ≤ u := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have hIH := ih ht
      have hcard : (0 : ℝ) < (t.card : ℕ) := by
        have := Multiset.card_pos.2 ht0
        exact_mod_cast this
      have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
      have hQ : (0 : ℝ) ≤ (t.map (fun b => b ^ 2)).sum :=
        Multiset.sum_nonneg (by
          intro y hy
          obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
          exact sq_nonneg u)
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith [hIH, sq_nonneg (t.sum - (t.card : ℝ) * b), hcard, hsum, hb, hQ]

/-- **The error bound.**  `∑ⱼ ∏_{k≠j} ‖1 - a t q_k‖ ≤ (n-1) β(t)^{(n-2)/2}`: Maclaurin's
inequality, then Cauchy–Schwarz, then the quadratic mean.  Nonnegativity of `β(t)` is not
assumed — it follows from the quadratic-mean bound, `β(t)` dominating an average of squares. -/
theorem sumEraseProdMap_norm_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ with hf
  set bs : Multiset ℝ := q.map f with hbs
  have hbcard : bs.card = n - 1 := by rw [hbs, Multiset.card_map, hqcard]
  have hNcast : ((bs.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hbcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have hNpos : (0 : ℝ) < (bs.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbs0 : bs ≠ 0 := by
    rw [hbs]
    simpa using hq0
  have hbnn : ∀ b ∈ bs, 0 ≤ b := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hb
    exact norm_nonneg _
  have hsumnn : 0 ≤ bs.sum := Multiset.sum_nonneg hbnn
  -- the quadratic mean
  have hsq : (bs.map (fun b => b ^ 2)).sum ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
    rw [hbs, Multiset.map_map]
    exact sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx
  have hβ0 : 0 ≤ QQ (a * x) (a ^ 2) t := by
    have hnn : (0 : ℝ) ≤ (bs.map (fun b => b ^ 2)).sum :=
      Multiset.sum_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact sq_nonneg u)
    nlinarith [hsq, hnn, hNcast, hNpos]
  -- Cauchy–Schwarz
  have hcs : (bs.sum) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 * QQ (a * x) (a ^ 2) t := by
    have h := sq_sum_le_card_mul_sum_sq bs hbnn
    rw [hNcast] at h
    nlinarith [h, hsq, hNcast, hNpos]
  have hmean : bs.sum / (bs.card : ℕ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) := by
    rw [div_le_iff₀ hNpos, hNcast]
    have hsqrt : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ 2 = QQ (a * x) (a ^ 2) t :=
      Real.sq_sqrt hβ0
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hNcast]; exact hNpos
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) * ((n : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn1)
    nlinarith [hcs, hsqrt, hsumnn, hprodnn, hn1]
  -- Maclaurin
  have hmac := Multiset.esymm_card_pred_le bs hbnn hbs0
  rw [sumEraseProdMap_eq_esymm q f hq0, ← hbs]
  refine hmac.trans ?_
  have hpow : (bs.sum / (bs.card : ℕ)) ^ (bs.card - 1)
      ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
    refine pow_le_pow_left₀ (by positivity) hmean _
  have hfin : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1)
      = QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (QQ (a * x) (a ^ 2) t ^ ((1 : ℝ) / 2))
      (bs.card - 1), ← Real.rpow_mul hβ0]
    congr 1
    have hcast2 : ((bs.card - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [hbcard]
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2]
      push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
      ring
    rw [hcast2]
    ring
  rw [hNcast] at *
  calc ((n : ℝ) - 1) * (bs.sum / ((n : ℝ) - 1)) ^ (bs.card - 1)
      ≤ ((n : ℝ) - 1) * Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hNcast] at hpow ⊢
        exact hpow
    _ = ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by rw [hfin]

/-! ### The derivative of `F(t) = ∏ⱼ (1 - a t qⱼ)` -/

open scoped Classical in
/-- `∑ⱼ g(qⱼ) ∏_{k≠j} f(q_k)`, the weighted erasure sum over `ℂ`.  Taking `g = id` gives the
derivative of a product; taking `g = (· ^ 2)` gives the residual left after the main term is
split off. -/
noncomputable def sumEraseProdC (s : Multiset ℂ) (g f : ℂ → ℂ) : ℂ :=
  (s.map (fun j => g j * ((s.erase j).map f).prod)).sum

open scoped Classical in
@[simp] lemma sumEraseProdC_zero (g f : ℂ → ℂ) : sumEraseProdC 0 g f = 0 := by
  simp [sumEraseProdC]

open scoped Classical in
lemma sumEraseProdC_cons (v : ℂ) (t : Multiset ℂ) (g f : ℂ → ℂ) :
    sumEraseProdC (v ::ₘ t) g f = g v * (t.map f).prod + f v * sumEraseProdC t g f := by
  simp only [sumEraseProdC, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
  ring

/-- A weighted erasure sum with unit-size weights is dominated by the unweighted one. -/
lemma norm_sumEraseProdC_le (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp [sumEraseProdMap]
  | cons v t ih =>
    intro hg
    have hv := hg v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖g u‖ ≤ 1 := fun u hu => hg u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProdC_cons, sumEraseProdMap_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_prod_map]
    have h2 : (0 : ℝ) ≤ (t.map (fun v => ‖f v‖)).prod := prod_map_norm_nonneg t f
    nlinarith [ih ht, norm_nonneg (f v), norm_nonneg (sumEraseProdC t g f), h2, hv]

/-- `F(t) = ∏ⱼ (1 - a t qⱼ)`. -/
noncomputable def Fprod (a : ℝ) (q : Multiset ℂ) (t : ℝ) : ℂ :=
  (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod

@[simp] lemma Fprod_zero (a : ℝ) (q : Multiset ℂ) : Fprod a q 0 = 1 := by
  simp [Fprod]

/-- Splitting the derivative sum into its main term and its residual:
`∑ⱼ qⱼ ∏_{k≠j}(1-atq_k) = (∑ⱼ qⱼ) F(t) + a t ∑ⱼ qⱼ² ∏_{k≠j}(1-atq_k)`, since
`1 - (1 - a t qⱼ) = a t qⱼ`. -/
lemma sumEraseProdC_id_eq (a t : ℝ) : ∀ (q : Multiset ℂ),
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
      = q.sum * Fprod a q t
        + (a : ℂ) * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
            (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp [Fprod]
  | cons v r ih =>
    rw [sumEraseProdC_cons, sumEraseProdC_cons, ih, Multiset.sum_cons]
    simp only [Fprod, Multiset.map_cons, Multiset.prod_cons, id]
    ring

/-- `F'(t) = -a ∑ⱼ qⱼ ∏_{k≠j}(1 - a t q_k)`. -/
lemma hasDerivAt_Fprod (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    have he : Fprod a 0 = fun _ : ℝ => (1 : ℂ) := by funext s; simp [Fprod]
    have hz : -(a : ℂ) * sumEraseProdC 0 id (fun v => 1 - (a : ℂ) * (t : ℂ) * v) = 0 := by simp
    rw [he, hz]
    exact hasDerivAt_const t 1
  | cons v r ih =>
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 1 - (a : ℂ) * (s : ℂ) * v) (-((a : ℂ) * v)) t := by
      simpa using ((h0.const_mul (a : ℂ)).mul_const v).const_sub 1
    have h2 := h1.mul ih
    have hfun : Fprod a (v ::ₘ r)
        = fun s : ℝ => (1 - (a : ℂ) * (s : ℂ) * v) * Fprod a r s := by
      funext s
      simp only [Fprod, Multiset.map_cons, Multiset.prod_cons]
    have hderiv : -(a : ℂ) * ((v : ℂ) * (r.map (fun w => 1 - (a : ℂ) * (t : ℂ) * w)).prod
          + (1 - (a : ℂ) * (t : ℂ) * v) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w))
        = -((a : ℂ) * v) * Fprod a r t
          + (1 - (a : ℂ) * (t : ℂ) * v)
              * (-(a : ℂ) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w)) := by
      simp only [Fprod]
      ring
    rw [hfun, sumEraseProdC_cons, id_eq, hderiv]
    exact h2

/-- **The pointwise estimate.**  `‖F'(t) + (n-1) a (x+iy) F(t)‖ ≤ a² t (n-1) β(t)^{(n-2)/2}`. -/
theorem norm_deriv_add_le {n : ℕ} (hn : 2 ≤ n) {a x y t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (ha0 : 0 ≤ a) (ht0 : 0 ≤ t)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = (((n : ℝ) - 1) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
        + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
      ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set S : ℂ := sumEraseProdC q (fun v => v ^ 2) (fun v => 1 - (a : ℂ) * (t : ℂ) * v) with hS
  have hmain : (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
      + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t
      = -((a : ℂ) ^ 2 * (t : ℂ)) * S := by
    rw [sumEraseProdC_id_eq, hsum, ← hS]
    ring
  rw [hmain, norm_mul]
  have hnorm : ‖-((a : ℂ) ^ 2 * (t : ℂ))‖ = a ^ 2 * t := by
    simp [abs_of_nonneg ha0, abs_of_nonneg ht0]
  rw [hnorm]
  have hSle : ‖S‖ ≤ sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖) := by
    rw [hS]
    refine norm_sumEraseProdC_le _ _ q ?_
    intro v hv
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg v) (hq1 v hv)
  have hbd := sumEraseProdMap_norm_le (a := a) (x := x) (t := t) hn hqcard hq0 hq1 hx
  have hfac : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg (pow_nonneg ha0 2) ht0
  calc a ^ 2 * t * ‖S‖
      ≤ a ^ 2 * t * (((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
        mul_le_mul_of_nonneg_left (hSle.trans hbd) hfac
    _ = a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by ring

/-! ### Integrating the pointwise estimate: the triangle inequality `(tri)` -/

lemma continuous_prodC (a : ℝ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih

lemma continuous_Fprod (a : ℝ) (q : Multiset ℂ) : Continuous (Fprod a q) :=
  continuous_prodC a q

lemma continuous_sumEraseProdC (a : ℝ) (g : ℂ → ℂ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => sumEraseProdC q g (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    simp only [sumEraseProdC_zero]
    exact continuous_const
  | cons v r ih =>
    simp only [sumEraseProdC_cons]
    exact (continuous_const.mul (continuous_prodC a r)).add
      ((by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih)

/-- **The triangle inequality `(tri)`.**  Integrating `norm_deriv_add_le` against the
fundamental theorem of calculus, using `F(0) = 1`. -/
theorem one_le_tri {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (ha0 : 0 ≤ a)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ ‖Fprod a q 1 + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)
            * ∫ t in (0 : ℝ)..1, Fprod a q t‖
        + a ^ 2 * ((n : ℝ) - 1)
            * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set c : ℂ := ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) with hc
  set D : ℝ → ℂ := fun t => -(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
    with hDdef
  have hDcont : Continuous D := by
    rw [hDdef]
    exact continuous_const.mul (continuous_sumEraseProdC a id q)
  have hFcont : Continuous (Fprod a q) := continuous_Fprod a q
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 1 := hDcont.intervalIntegrable _ _
  have hFint : IntervalIntegrable (Fprod a q) MeasureTheory.volume 0 1 :=
    hFcont.intervalIntegrable _ _
  have hFTC : ∫ t in (0 : ℝ)..1, D t = Fprod a q 1 - Fprod a q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_Fprod a t q) hDint
  -- the exact identity behind the triangle inequality
  have hG : ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)
      = (Fprod a q 1 - 1) + c * ∫ t in (0 : ℝ)..1, Fprod a q t := by
    rw [intervalIntegral.integral_add hDint (hFint.const_mul c), hFTC, Fprod_zero,
      intervalIntegral.integral_const_mul]
  have hkey : (1 : ℂ) = (Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t)
      - ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t) := by
    rw [hG]; ring
  -- the pointwise bound, integrated
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hRcont : Continuous fun t : ℝ =>
      a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
    continuous_const.mul (continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hexp)
  have hGnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t + c * Fprod a q t‖
      ≤ a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    intro t ht
    have h := norm_deriv_add_le hn hqcard hq0 hq1 ha0 ht.1 hx hsum (t := t) (y := y)
    rw [hDdef, hc]
    calc ‖-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
            + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
        ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := h
      _ = a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by ring
  have hint : ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖
      ≤ a ^ 2 * ((n : ℝ) - 1)
          * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    have hni : IntervalIntegrable (fun t : ℝ => ‖D t + c * Fprod a q t‖)
        MeasureTheory.volume 0 1 :=
      (hDcont.add (continuous_const.mul hFcont)).norm.intervalIntegrable _ _
    have hri : IntervalIntegrable (fun t : ℝ =>
        a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)))
        MeasureTheory.volume 0 1 := hRcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hni hri hGnorm
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    simp
  -- assemble
  have hnorm1 : ‖(1 : ℂ)‖ ≤ ‖Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      + ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖ := by
    conv_lhs => rw [hkey]
    exact norm_sub_le _ _
  rw [norm_one] at hnorm1
  linarith [hnorm1, hint]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/Jsum.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Estimating `J ∑ⱼ 1/zⱼ`

The origin argument needs `∑ⱼ 1/zⱼ`, which the centroid identity supplies only after the
inversions `1/zⱼ = conj zⱼ` and `1/qⱼ = conj qⱼ` are used.  Those hold exactly when the points
lie on the unit circle, i.e. when `|J| = 1`, and the **defect lemma** measures the failure by
`1 - |J|²`.  Conjugating the centroid identity and paying that defect gives

  `J ∑ⱼ 1/zⱼ = a (n-1) J - n J (x+iy) + O_≤( (n/(n-1)) (1 - |J|²) )`,

which is `TaoSendov.Jsum_estimate` below.  A single application of the defect lemma, to the
`2(n-1)` points `z₁,…,z_{n-1}, conj q₁,…,conj q_{n-1}`, pays for both substitutions at once.

Everything is division-free on the `z` side: `J ∑ⱼ 1/zⱼ` is written as `(∏ qⱼ) · sumEraseProd z`,
which is well defined even when some `zⱼ` vanishes.  That case is not excluded by hypothesis but
handled: if `∏ zⱼ = 0` then at most one term of `sumEraseProd z` survives, so the left side is at
most `1` while the right side is at least `n/(n-1) > 1`.  On the `q` side no such care is needed,
since the `qⱼ` are reciprocals and never vanish.

## Main statements

* `TaoSendov.Jsum_estimate`: the estimate above;
* `TaoSendov.sumEraseProd_norm_le_one`: the degenerate case `∏ zⱼ = 0`;
* `TaoSendov.prod_mul_sum_inv`: `(∏ s) ∑ⱼ 1/sⱼ = sumEraseProd s` when no `sⱼ` vanishes.
-/

namespace TaoSendov

/-! ### Multiset odds and ends -/

lemma sum_map_sub (s : Multiset ℂ) (f g : ℂ → ℂ) :
    (s.map (fun v => f v - g v)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

lemma sum_map_const_sub (s : Multiset ℂ) (c : ℂ) (g : ℂ → ℂ) :
    (s.map (fun v => c - g v)).sum = (s.card : ℂ) * c - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

lemma sum_map_re (s : Multiset ℂ) : (s.map (fun v => v.re)).sum = s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih => simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, ih]

lemma norm_sum_map_le (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun w => ‖f w‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [norm_add_le (f v) ((t.map f).sum), ih]

lemma norm_prod_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, norm_mul]
    nlinarith [ih ht, norm_nonneg v, norm_nonneg t.prod]

/-- `(∏ s) ∑ⱼ 1/sⱼ = ∑ⱼ ∏_{k≠j} sₖ`, the clearing of denominators that is valid exactly when
no `sⱼ` vanishes. -/
lemma prod_mul_sum_inv : ∀ (s : Multiset ℂ), (∀ w ∈ s, w ≠ 0) →
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp [sumEraseProd]
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, u ≠ 0 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, sumEraseProd_cons, ← ih ht]
    field_simp

/-- The degenerate case.  If `∏ sⱼ = 0` then some `sⱼ` vanishes, so at most one term of
`∑ⱼ ∏_{k≠j} sₖ` is nonzero — and that term is a product of points of the closed unit disk. -/
lemma sumEraseProd_norm_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → s.prod = 0 →
    ‖sumEraseProd s‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; simp at h
  | cons v t ih =>
    intro hs hp
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProd_cons]
    rcases eq_or_ne t.prod 0 with ht0 | ht0
    · rw [ht0, zero_add, norm_mul]
      nlinarith [ih ht ht0, norm_nonneg v, norm_nonneg (sumEraseProd t), hv]
    · have hv0 : v = 0 := by
        rw [Multiset.prod_cons] at hp
        rcases mul_eq_zero.1 hp with h | h
        · exact h
        · exact absurd h ht0
      rw [hv0, zero_mul, add_zero]
      exact norm_prod_le_one t ht

/-! ### The estimate -/

/-- **The estimate for `J ∑ⱼ 1/zⱼ`.**  Conjugating the centroid identity replaces `1/zⱼ` by
`conj zⱼ` and `qⱼ` by `1/conj qⱼ`; the defect lemma pays for both substitutions at once. -/
theorem Jsum_estimate {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {z q : Multiset ℂ}
    (hqcard : q.card = n - 1)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod)‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn1]; linarith
  have hqpnorm : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  rcases eq_or_ne z.prod 0 with hz0 | hz0
  · -- degenerate: `J = 0`, and `sumEraseProd z` has at most one surviving term
    rw [hz0, mul_zero, mul_zero, sub_zero, norm_zero, mul_zero, norm_mul]
    have h2 : ‖sumEraseProd z‖ ≤ 1 := sumEraseProd_norm_le_one z hz1 hz0
    nlinarith [norm_nonneg q.prod, norm_nonneg (sumEraseProd z)]
  · -- the main case: every `zⱼ` is nonzero, so denominators may be cleared
    have hzne : ∀ w ∈ z, w ≠ 0 := by
      intro w hw hw0
      exact hz0 (Multiset.prod_eq_zero (hw0 ▸ hw))
    set qc : Multiset ℂ := q.map (fun v => (starRingEnd ℂ) v) with hqc
    have hqcnorm : ∀ w ∈ qc, ‖w‖ ≤ 1 := by
      intro w hw
      rw [hqc] at hw
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hw
      simpa using hq1 v hv
    have hqsum : q.sum = (qc.map (fun w => (starRingEnd ℂ) w)).sum := by
      rw [hqc, Multiset.map_map]
      simp
    -- the conjugated centroid identity
    have hconj : ((n : ℂ) - 1) * ((a : ℂ) + (z.map (fun w => (starRingEnd ℂ) w)).sum)
        = (n : ℂ) * (((n : ℂ) - 1) * (a : ℂ) - (qc.map (fun w => w⁻¹)).sum) := by
      have h := congrArg (starRingEnd ℂ) hcent
      simp only [map_mul, map_sub, map_add, map_one, map_inv₀, map_natCast,
        Complex.conj_ofReal, map_multiset_sum, Multiset.map_map, Function.comp_def] at h
      rw [sum_map_const_sub, hqcard] at h
      have hcard : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
        push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
        ring
      rw [hcard] at h
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def]
      exact h
    -- `J ∑ⱼ 1/zⱼ` in division-free form
    have hSz : q.prod * sumEraseProd z = (q.prod * z.prod) * (z.map (fun w => w⁻¹)).sum := by
      rw [← prod_mul_sum_inv z hzne]; ring
    -- name the error and the bracket
    obtain ⟨E, hEdef⟩ : ∃ w : ℂ, w = q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod) := ⟨_, rfl⟩
    obtain ⟨X, hXdef⟩ : ∃ w : ℂ, w = ((n : ℂ) - 1)
          * ((z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum)
        + (n : ℂ) * (q.sum - (qc.map (fun w => w⁻¹)).sum) := ⟨_, rfl⟩
    rw [← hEdef]
    -- the exact rearrangement
    have hE : ((n : ℂ) - 1) * E = (q.prod * z.prod) * X := by
      rw [hEdef, hXdef, hSz, hxy]
      linear_combination (q.prod * z.prod) * hconj
    -- the defect lemma, applied to `z` together with the conjugates of `q`
    have hdefect := defect (z + qc) (by
      intro w hw
      rcases Multiset.mem_add.1 hw with h | h
      · exact hz1 w h
      · exact hqcnorm w h)
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.sum_add] at hdefect
    have hzp : (z.map (fun w => ‖w‖)).prod = ‖z.prod‖ := (norm_multiset_prod z).symm
    have hqp : (qc.map (fun w => ‖w‖)).prod = ‖q.prod‖ := by
      rw [hqc, Multiset.map_map]
      simp only [Function.comp_def, RCLike.norm_conj]
      exact (norm_multiset_prod q).symm
    rw [hzp, hqp] at hdefect
    obtain ⟨Dz, hDz⟩ : ∃ r : ℝ, r = (z.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ r : ℝ, r = (qc.map (fun w => ‖w⁻¹ - (starRingEnd ℂ) w‖)).sum := ⟨_, rfl⟩
    rw [← hDz, ← hDq] at hdefect
    have hDz0 : 0 ≤ Dz := by
      rw [hDz]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    have hDq0 : 0 ≤ Dq := by
      rw [hDq]
      exact Multiset.sum_nonneg (by
        intro r hr
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.1 hr
        exact norm_nonneg _)
    -- the two substitution errors
    have hbz : ‖(z.map (fun w => w⁻¹)).sum - (z.map (fun w => (starRingEnd ℂ) w)).sum‖ ≤ Dz := by
      rw [← sum_map_sub, hDz]
      exact norm_sum_map_le z _
    have hbq : ‖q.sum - (qc.map (fun w => w⁻¹)).sum‖ ≤ Dq := by
      have hneg : q.sum - (qc.map (fun w => w⁻¹)).sum
          = -((qc.map (fun w => w⁻¹ - (starRingEnd ℂ) w)).sum) := by
        rw [hqsum, sum_map_sub]
        ring
      rw [hneg, norm_neg, hDq]
      exact norm_sum_map_le qc _
    -- assemble
    have hnorm : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
      have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
    have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    have hXle : ‖X‖ ≤ ((n : ℝ) - 1) * Dz + (n : ℝ) * Dq := by
      rw [hXdef]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hnorm, hnn]
      exact add_le_add (mul_le_mul_of_nonneg_left hbz (by linarith))
        (mul_le_mul_of_nonneg_left hbq (by positivity))
    have hkey : ((n : ℝ) - 1) * ‖E‖ = ‖q.prod‖ * ‖z.prod‖ * ‖X‖ := by
      have h := congrArg norm hE
      rw [norm_mul, norm_mul, norm_mul, hnorm] at h
      exact h
    have hP0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
    have hstep : ((n : ℝ) - 1) * ‖E‖ ≤ (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
      rw [hkey]
      calc ‖q.prod‖ * ‖z.prod‖ * ‖X‖
          ≤ ‖q.prod‖ * ‖z.prod‖ * (((n : ℝ) - 1) * Dz + (n : ℝ) * Dq) :=
            mul_le_mul_of_nonneg_left hXle hP0
        _ ≤ ‖q.prod‖ * ‖z.prod‖ * ((n : ℝ) * (Dz + Dq)) := by nlinarith [hDz0, hP0]
        _ = (n : ℝ) * (‖z.prod‖ * ‖q.prod‖ * (Dz + Dq)) := by ring
        _ ≤ (n : ℝ) * (1 - (‖z.prod‖ * ‖q.prod‖) ^ 2) := by
            have hnpos : (0 : ℝ) ≤ (n : ℝ) := by linarith
            exact mul_le_mul_of_nonneg_left hdefect hnpos
        _ = (n : ℝ) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
    linarith [hstep]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/OriginExact.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The origin inequality

This file closes the origin channel, deriving `(origin-exact)` — the hypothesis `horigin` of
`TaoSendov.polar_origin_incompatible` — from the triangle inequality `(tri)` of
`TaoSendov.Analytic.Origin`, the two origin identities, and the defect estimate of
`TaoSendov.Analytic.Jsum`.

The chain is:

* **(f1aq)**  The two origin identities express `F(1) + (n-1) a (x+iy) ∫₀¹F` exactly, in terms of
  `J = (∏ qⱼ)(∏ zⱼ)` and `∑ⱼ 1/zⱼ`.  Feeding in `Jsum_estimate` collapses this to `J·W/n` plus
  an error of size `a(1-|J|²)/(n-1)`, where `W = a²(n-1) + 1 - a(x+iy)`.
* **(grow)**  `‖W‖ ≥ 2an/(n-1)`, which makes `|J|·‖W‖/n + a(1-|J|²)/(n-1)` non-decreasing in
  `|J|` on `[0,1]`, so `|J|` may be replaced by `1`.  This reduces to the quadratic
  `(n-1)²a² - (3n-1)a + (n-1) > 0`, whose discriminant `(3n-1)² - 4(n-1)³` is negative exactly
  from `n ≥ 5` on.  **This is the only place the hypothesis `n ≥ 5` is used.**
* **Eliminating `y`.**  `|s + it| ≤ s + t²/(2s)` for `s > 0`, applied to `W`, whose real part
  `a²(n-1) + 1 - ax` is at least `a²(n-1)`, and whose imaginary part is `-ay` with
  `y² ≤ 1 - x²`.

## Main statements

* `TaoSendov.origin_exact`: `(origin-exact)`, in exactly the form `polar_origin_incompatible` wants;
* `TaoSendov.grow`: the lower bound `‖W‖ ≥ 2an/(n-1)`.
-/

namespace TaoSendov

open Complex (I)

/-! ### Scalar lemmas -/

lemma sum_norm_le_card : ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
    (q.map (fun v => ‖v‖)).sum ≤ (q.card : ℝ) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

/-- `|s + it| ≤ s + t²/(2s)` for `s > 0`, in cleared form.  Squaring both sides leaves
`t⁴ ≥ 0`. -/
lemma norm_mul_two_re_le {w : ℂ} (_hs : 0 < w.re) :
    ‖w‖ * (2 * w.re) ≤ 2 * w.re ^ 2 + w.im ^ 2 := by
  have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg w, h1, sq_nonneg (w.im ^ 2), sq_nonneg (w.re * w.im)]

/-! ### The quantity `W`, the growth bound `(grow)`, and the two real-arithmetic steps -/

/-- `W = a²(n-1) + 1 - a(x+iy)`; `n` times the bracket in the blog post's `(tri-2)`. -/
noncomputable def Worigin (n : ℕ) (a x y : ℝ) : ℂ :=
  (a : ℂ) ^ 2 * ((n : ℂ) - 1) + 1 - (a : ℂ) * ((x : ℂ) + (y : ℂ) * I)

lemma Worigin_eq (n : ℕ) (a x y : ℝ) :
    Worigin n a x y = ((a ^ 2 * ((n : ℝ) - 1) + 1 - a * x : ℝ) : ℂ)
      + ((-(a * y) : ℝ) : ℂ) * I := by
  simp only [Worigin]
  push_cast
  ring

lemma Worigin_re (n : ℕ) (a x y : ℝ) :
    (Worigin n a x y).re = a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by
  rw [Worigin_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma Worigin_im (n : ℕ) (a x y : ℝ) : (Worigin n a x y).im = -(a * y) := by
  rw [Worigin_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **(grow).**  `‖W‖ ≥ 2an/(n-1)`.  Bounding `‖W‖` below by its real part reduces this to
`(n-1)²a² - (3n-1)a + (n-1) > 0`; completing the square turns that into
`4(n-1)³ - (3n-1)² > 0`, which is exactly where `n ≥ 5` is needed. -/
theorem grow {n : ℕ} (hn : 5 ≤ n) {a x y : ℝ} (ha0 : 0 < a) (hx : x ≤ 1) :
    2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ ‖Worigin n a x y‖ := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hu : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have hdisc : 0 < 4 * ((n : ℝ) - 1) ^ 3 - (3 * (n : ℝ) - 1) ^ 2 := by
    nlinarith [hu, sq_nonneg ((n : ℝ) - 5), mul_nonneg (mul_nonneg hu hu) hu]
  have hquad : 0 < ((n : ℝ) - 1) ^ 2 * a ^ 2 - (3 * (n : ℝ) - 1) * a + ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg (2 * ((n : ℝ) - 1) ^ 2 * a - (3 * (n : ℝ) - 1)), hdisc,
      mul_pos hn1 hn1]
  have hre : 2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ (Worigin n a x y).re := by
    rw [Worigin_re, div_le_iff₀ hn1]
    nlinarith [hquad, mul_nonneg (mul_nonneg (le_of_lt ha0) (sub_nonneg.2 hx)) (le_of_lt hn1)]
  exact hre.trans (Complex.re_le_norm _)

/-- Replacing `|J|` by `1`: `P K + c(1 - P²) ≤ K` on `0 ≤ P ≤ 1` once `K ≥ 2c ≥ 0`, since
`K - P K - c(1-P²) = (1-P)(K - c(1+P))`. -/
lemma collapse_J {K c P : ℝ} (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hcK : 2 * c ≤ K) :
    P * K + c * (1 - P ^ 2) ≤ K := by
  have hfac : 0 ≤ (1 - P) * (K - c * (1 + P)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hc0, hP1, hcK]
  nlinarith [hfac]

/-- Eliminating `y`: `‖W‖ ≤ Re W + (Im W)²/(2 Re W)`, then `Re W ≥ a²(n-1)` and `y² ≤ 1 - x²`. -/
lemma norm_Worigin_le {n : ℕ} {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hn1 : (0 : ℝ) < (n : ℝ) - 1) (hxle : x ≤ 1) (hy2 : y ^ 2 ≤ 1 - x ^ 2) :
    ‖Worigin n a x y‖
      ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x + (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
  have hax : a * x ≤ a := mul_le_of_le_one_right (le_of_lt ha0) hxle
  have ha2 : (0 : ℝ) < a ^ 2 * ((n : ℝ) - 1) := by positivity
  have hslow : a ^ 2 * ((n : ℝ) - 1) ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by linarith
  have hpos : 0 < (Worigin n a x y).re := by rw [Worigin_re]; linarith
  have hs : (0 : ℝ) < 2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x) := by linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have h := norm_mul_two_re_le hpos
  rw [Worigin_re, Worigin_im] at h
  have hmain : ‖Worigin n a x y‖
      ≤ (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)
        + a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hs]
    nlinarith [h]
  have htail : a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x))
      ≤ (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hs hden]
    nlinarith [hy2, hslow, ha2, sq_nonneg y, hn1]
  linarith [hmain, htail]

/-- `x` and `y` are determined by `q.sum`, and inherit two bounds from `‖qⱼ‖ ≤ 1`: the real
part is what the polar and origin estimates need, and `x² + y² ≤ 1` is what eliminates `y`. -/
lemma xy_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)) :
    (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x ∧ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnc : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
    have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
  have hqcardR : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  refine ⟨?_, ?_⟩
  · have hc : ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)
        = ((((n : ℝ) - 1) * x : ℝ) : ℂ) + ((((n : ℝ) - 1) * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [sum_map_re, hxy, hc]
    simp
  · have hxynorm : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have h2 : ‖q.sum‖ ≤ (q.map (fun v => ‖v‖)).sum := by
      have h := norm_sum_map_le q (fun v => v)
      simpa using h
    have h3 := sum_norm_le_card q hq1
    rw [hqcardR] at h3
    have h1 : ‖q.sum‖ ≤ (n : ℝ) - 1 := h2.trans h3
    rw [hxy, norm_mul, hnc] at h1
    have h4 : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [h1, hn1]
    nlinarith [hxynorm, h4, norm_nonneg ((x : ℂ) + (y : ℂ) * I)]

/-! ### The origin inequality -/

/-- **`(origin-exact)`.**  The origin channel, in the form the reduction consumes. -/
theorem origin_exact {n : ℕ} (hn : 5 ≤ n) {a x y α : ℝ} {z q : Multiset ℂ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I))
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hfirst : (n : ℂ) * ∫ t in (0 : ℝ)..1, Fprod a q t = (-1) ^ (n - 1) * q.prod * z.prod)
    (hsecond : (n : ℂ) * (q.map (fun v => 1 - (a : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z))
    (hα : α = M n * (1 - a ^ 2) / 2) :
    2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hxre, hx2⟩ := xy_bounds hn2 hqcard hq1 hxy
  have hxle : x ≤ 1 := by nlinarith [hx2, sq_nonneg y]
  -- the triangle inequality `(tri)` and the defect estimate
  have htri := one_le_tri hn2 hqcard hq0 hq1 (le_of_lt ha0) hxre hxy
  have hJ := Jsum_estimate (n := n) hn2 (a := a) (x := x) (y := y) hqcard hz1 hq1 hcent hxy
  -- `(f1aq)`
  have hF1 : Fprod a q 1 = (q.map (fun v => 1 - (a : ℂ) * v)).prod := by
    simp only [Fprod, Complex.ofReal_one, mul_one]
  have hsecond' : (n : ℂ) * Fprod a q 1
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z) := by
    rw [hF1]; exact hsecond
  have hf1aq : (n : ℂ) * (Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t)
      = (-1) ^ (n - 1) * ((q.prod * z.prod) * Worigin n a x y
        + (a : ℂ) * (q.prod * sumEraseProd z
            - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * I))
              * (q.prod * z.prod))) := by
    simp only [Worigin]
    linear_combination hsecond' + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * hfirst
  -- `(tri-2)`
  have hsign : ‖((-1 : ℂ)) ^ (n - 1)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hana : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  have hPJ0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
  have hPJ1 : ‖q.prod‖ * ‖z.prod‖ ≤ 1 := by
    have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
    have h2 : ‖z.prod‖ ≤ 1 := norm_prod_le_one z hz1
    nlinarith [norm_nonneg q.prod, norm_nonneg z.prod]
  have hstep1 : (n : ℝ) * ‖Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      ≤ ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
        + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
    have h := congrArg norm hf1aq
    rw [norm_mul, hnn, norm_mul, hsign, one_mul] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, hana]
    have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt ha0)
    linarith [hmul]
  -- `(grow)` collapses `|J|` to `1`, giving `(tri-3)`
  have hgrow := grow (n := n) hn (a := a) (x := x) (y := y) ha0 hxle
  have hcoll : ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
      + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2)
      ≤ ‖Worigin n a x y‖ := by
    have hc : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) ≤ ‖Worigin n a x y‖ := by
      have he : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) = 2 * a * (n : ℝ) / ((n : ℝ) - 1) := by ring
      rw [he]; exact hgrow
    have hcnn : (0 : ℝ) ≤ a * ((n : ℝ) / ((n : ℝ) - 1)) := by positivity
    exact collapse_J hPJ1 hcnn hc
  have htri3 : (n : ℝ) ≤ ‖Worigin n a x y‖
      + (n : ℝ) * (a ^ 2 * ((n : ℝ) - 1)
        * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    have h := mul_le_mul_of_nonneg_left htri (le_of_lt hnpos)
    linarith [h, hstep1, hcoll]
  -- eliminate `y`, and assemble
  have hWle := norm_Worigin_le (n := n) (y := y) ha0 ha1 hn1 hxle (by linarith [hx2])
  simp only [M] at hα ⊢
  linarith [htri3, hWle, hα]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Analytic/LowDegree.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The low-degree branch: degrees `2 ≤ n ≤ 5`

The high-degree argument relaxes the branch point `(⋆)`,

  `1 ≤ ∫₀¹ ∏ⱼ ‖a + t(1-a²)qⱼ‖ dt`,

by AM–GM to the raw polar inequality `(1Q)`, and then needs the origin channel as well.  In low
degree none of that is necessary: bounding each factor of `(⋆)` by the *scalar*
`X(t) = a + (1-a²)t` already contradicts itself.

Writing `m = n - 1` for the number of non-distinguished zeroes and `J_m(a) = ∫₀¹ X(t)^m dt`,
the branch point gives `1 ≤ J_m(a)` while a direct computation gives `J_m(a) < 1` for
`0 < a < 1` and `1 ≤ m ≤ 4`.  The computation is done once, at `m = 4`:

  `1 - J₄(a) = ((1-a)³(1+a)/5)(a⁴ - 3a³ + 3a + 4)`,

whose last factor is `2 + 3a + (1-a)(2 + 2a + a²(2-a)) > 0`; the smaller exponents are dominated
by `X^m ≤ 1 - m/4 + (m/4)X⁴`, four instances of weighted AM–GM that factor as squares.

Note the off-by-one: `m ≤ 4` is degree `n ≤ 5`, so this branch covers degree five as well.  All
strictness comes from `a < 1`; at `a = 1` one has `J_m(1) = 1`, matching the regular-polygon
equality examples.

## Main statements

* `TaoSendov.low_degree_contradiction`: `(⋆)` is contradictory for `2 ≤ n ≤ 5`;
* `TaoSendov.lowJ_lt_one`: `J_m(a) < 1` for `0 < a < 1` and `1 ≤ m ≤ 4`.
-/

namespace TaoSendov

/-! ### The scalar chord and its moments -/

/-- `X(t) = a + (1-a²)t`, the pointwise majorant of `‖a + t(1-a²)qⱼ‖`. -/
noncomputable def lowX (a t : ℝ) : ℝ := a + (1 - a ^ 2) * t

/-- `J_m(a) = ∫₀¹ X(t)^m dt`. -/
noncomputable def lowJ (m : ℕ) (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, lowX a t ^ m

lemma lowX_nonneg {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) : 0 ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  simp only [lowX]
  positivity

lemma continuous_lowX_pow (a : ℝ) (m : ℕ) : Continuous fun t : ℝ => lowX a t ^ m := by
  simp only [lowX]
  fun_prop

/-! ### The branch point, bounded factor by factor -/

lemma norm_le_lowX {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hcast : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v
      = ((a : ℝ) : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * v := by push_cast; ring
  rw [hcast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg ht0 hb)]
  simp only [lowX]
  nlinarith [hv, norm_nonneg v, mul_nonneg ht0 hb]

lemma prod_norm_le_lowX_pow {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) :
    ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t ^ q.card := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v s ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v s)
    have hs : ∀ u ∈ s, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    have hX0 : 0 ≤ lowX a t := lowX_nonneg ha0 ha1 ht0
    have h3 : 0 ≤ (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod :=
      prod_map_norm_nonneg s _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖
          * (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t * lowX a t ^ s.card :=
          mul_le_mul (norm_le_lowX ha0 ha1 ht0 hv) (ih hs) h3 hX0
      _ = lowX a t ^ s.card * lowX a t := by ring

/-- The branch point `(⋆)`, with every factor replaced by the scalar `X(t)`. -/
theorem one_le_lowJ {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ lowJ (n - 1) a := by
  refine hstar.trans ?_
  rw [lowJ]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    ((continuous_lowX_pow a (n - 1)).intervalIntegrable _ _) ?_
  intro u hu
  have h := prod_norm_le_lowX_pow ha0 ha1 hu.1 q hq1
  rwa [hqcard] at h

/-! ### The fourth moment -/

/-- `J₄(a)`, by the fundamental theorem of calculus against an explicit antiderivative.  The
antiderivative is written without dividing by `1 - a²`, so no side condition on `a` appears. -/
lemma lowJ_four (a : ℝ) :
    lowJ 4 a = a ^ 4 + 2 * a ^ 3 * (1 - a ^ 2) + 2 * a ^ 2 * (1 - a ^ 2) ^ 2
      + a * (1 - a ^ 2) ^ 3 + (1 - a ^ 2) ^ 4 / 5 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ =>
      a ^ 4 * s + 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2 + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3
        + a * (1 - a ^ 2) ^ 3 * s ^ 4 + (1 - a ^ 2) ^ 4 / 5 * s ^ 5) (lowX a t ^ 4) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a ^ 4 * s) (a ^ 4 * 1) t :=
      (hasDerivAt_id' (x := t)).const_mul _
    have h2 : HasDerivAt (fun s : ℝ => 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2)
        (2 * a ^ 3 * (1 - a ^ 2) * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (2 * a ^ 3 * (1 - a ^ 2))
    have h3 : HasDerivAt (fun s : ℝ => 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3)
        (2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul (2 * a ^ 2 * (1 - a ^ 2) ^ 2)
    have h4 : HasDerivAt (fun s : ℝ => a * (1 - a ^ 2) ^ 3 * s ^ 4)
        (a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)) t := by
      simpa using (hasDerivAt_pow 4 t).const_mul (a * (1 - a ^ 2) ^ 3)
    have h5 : HasDerivAt (fun s : ℝ => (1 - a ^ 2) ^ 4 / 5 * s ^ 5)
        ((1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4)) t := by
      simpa using (hasDerivAt_pow 5 t).const_mul ((1 - a ^ 2) ^ 4 / 5)
    have hval : lowX a t ^ 4 = a ^ 4 * 1 + 2 * a ^ 3 * (1 - a ^ 2) * (2 * t)
        + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2) + a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)
        + (1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4) := by
      simp only [lowX]
      ring
    rw [hval]
    exact ((((h1.add h2).add h3).add h4).add h5)
  rw [lowJ, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_lowX_pow a 4).intervalIntegrable _ _)]
  norm_num

lemma lowJ_four_identity (a : ℝ) :
    1 - lowJ 4 a = ((1 - a) ^ 3 * (1 + a) / 5) * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  rw [lowJ_four]
  ring

lemma quartic_aux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hfactor : a ^ 4 - 3 * a ^ 3 + 3 * a + 4
      = 2 + 3 * a + (1 - a) * (2 + 2 * a + a ^ 2 * (2 - a)) := by ring
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 2 - a := by linarith
  rw [hfactor]
  positivity

lemma lowJ_four_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : lowJ 4 a < 1 := by
  have haux := quartic_aux_pos ha0 ha1
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 1 + a := by linarith
  rw [← sub_pos, lowJ_four_identity]
  positivity

/-! ### Dominating exponents one through four by the fourth -/

/-- `X^m ≤ 1 - m/4 + (m/4)X⁴` for `0 ≤ X` and `1 ≤ m ≤ 4`: weighted AM–GM, but at these four
exponents each instance factors as a square times a positive quadratic. -/
lemma pow_le_quartic_average {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    x ^ m ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * x ^ 4 := by
  interval_cases m
  · -- `m = 1`:  `X⁴ - 4X + 3 = (X-1)²(X² + 2X + 3)`
    have hpos : (0 : ℝ) ≤ x ^ 2 + 2 * x + 3 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 2`:  `X⁴ - 2X² + 1 = (X² - 1)²`
    norm_num
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  · -- `m = 3`:  `3X⁴ - 4X³ + 1 = (X-1)²(3X² + 2X + 1)`
    have hpos : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x + 1 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 4`: equality
    norm_num

theorem lowJ_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    lowJ m a < 1 := by
  have hcont4 := continuous_lowX_pow a 4
  have hcontm := continuous_lowX_pow a m
  have hmaj : Continuous fun t : ℝ => 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4 :=
    continuous_const.add (hcont4.const_mul _)
  have hint : (∫ t in (0 : ℝ)..1, (1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4))
      = 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      ((hcont4.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul, lowJ]
    simp
  have hle : lowJ m a ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [lowJ, ← hint]
    refine intervalIntegral.integral_mono_on (by norm_num) (hcontm.intervalIntegrable _ _)
      (hmaj.intervalIntegrable _ _) ?_
    intro u hu
    exact pow_le_quartic_average (lowX_nonneg (le_of_lt ha0) (le_of_lt ha1) hu.1) hm0 hm4
  have h4 := lowJ_four_lt_one ha0 ha1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  nlinarith [hle, h4, hmpos]

/-! ### The contradiction -/

/-- **The low-degree branch.**  The branch point `(⋆)` is already contradictory for
`2 ≤ n ≤ 5`, with no recourse to the origin channel. -/
theorem low_degree_contradiction {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    False := by
  have h1 := one_le_lowJ (n := n) (le_of_lt ha0) (le_of_lt ha1) hqcard hq1 hstar
  have h2 := lowJ_lt_one ha0 ha1 (m := n - 1) (by omega) (by omega)
  linarith

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Polar.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# From the raw polar inequality to its `α`, `β(1)` form

This is `(1Q) ⟹ (lt)` of the blog post: the raw polar inequality

  `1 ≤ ∫₀¹ (a² + 2atx(1-a²) + t²(1-a²)²)^((n-1)/2) dt`

implies

  `1 ≤ ∫₀¹ exp(α(-1 + (2-β(1))t)) dt`.

The step is pointwise, and it is remarkably tight.  Writing `β(1) = 1 - 2ax + a²` and
`α = (n-1)(1-a²)/2`, one has the *identity*

  `1 + (1-a²)(-1 + (2-β(1))t) - P(t) = (1-a²)² (t - t²)`,

so the only inequality used in the whole implication is `t² ≤ t` on `[0,1]` — with equality at
both endpoints — followed by `1 + y ≤ exp y`.  Raising to the power `(n-1)/2` then turns
`(1-a²)/2 · (n-1)` into `α`.

The blog post states `(lt)` with a strict inequality.  Nothing downstream needs that: every
later use of `(beta-bound)` is non-strict, so this file proves the non-strict form and avoids
having to argue that the integrand is strictly smaller on a set of positive measure.

## Main statements

* `TaoSendov.Ppolar_le_lin`: the pointwise identity-with-`t² ≤ t`;
* `TaoSendov.polar_exp`: `(1Q) ⟹ (lt)`.
-/

namespace TaoSendov

open MeasureTheory

variable {n : ℕ} {a x t α : ℝ}

/-- The pointwise bound `(at)`.  An identity apart from `t² ≤ t`. -/
lemma Ppolar_le_lin (a x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) := by
  have hid : 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) - Ppolar a x t
      = (1 - a ^ 2) ^ 2 * (t - t ^ 2) := by
    simp only [Ppolar, QQ]; ring
  nlinarith [mul_nonneg (sq_nonneg (1 - a ^ 2)) (mul_nonneg ht0 (sub_nonneg.2 ht1))]

/-- The pointwise bound after raising to the power `(n-1)/2`. -/
lemma Ppolar_rpow_le (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ^ (((n : ℝ) - 1) / 2)
      ≤ Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  set y : ℝ := (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) with hy
  have h1 : Ppolar a x t ≤ Real.exp y := by
    refine le_trans (Ppolar_le_lin a x ht0 ht1) ?_
    have := Real.add_one_le_exp y
    linarith
  have h2 : Ppolar a x t ^ (((n : ℝ) - 1) / 2) ≤ Real.exp y ^ (((n : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow (Ppolar_nonneg hx a t) h1 he
  refine h2.trans_eq ?_
  rw [← Real.exp_mul]
  congr 1
  simp only [M] at hα
  rw [hy, hα]
  ring

/-- **`(1Q) ⟹ (lt)`.** -/
theorem polar_exp (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1) (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2)) :
    1 ≤ ∫ t in (0 : ℝ)..1, Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by
  have hM : (0 : ℝ) < M n := M_pos hn
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by simp only [M] at hM; linarith
  have hc1 : Continuous fun t : ℝ => Ppolar a x t ^ (((n : ℝ) - 1) / 2) :=
    (continuous_rpow_const he).comp (continuous_Ppolar a x)
  have hc2 : Continuous fun t : ℝ =>
      Real.exp (α * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t)) := by fun_prop
  refine hpolar.trans (intervalIntegral.integral_mono_on (by norm_num)
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _) ?_)
  intro u hu
  exact Ppolar_rpow_le hn hx hα hu.1 hu.2

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Common/Sinh.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# `log (sinh h / h) ≤ √(h² + 9) - 3`

This is the sharp estimate behind the simplified polar inequality `β(1) ≤ α/(3+α)` of the blog
post: applied at `u = αβ(1)/2`, `h = α(2-β(1))/2`, it is exactly what turns

  `1 ≤ ∫₀¹ exp(α(-1 + (2-β(1))t)) dt = e^{-u} sinh h / h`

into `β(1) ≤ α/(3+α)`.  The constant `3` cannot be improved: at `B = α/(3+α)` the slack in the
integral inequality is `-α⁵/540 + α⁶/648`, so the bound is tight to three orders at `α = 0`.

## The proof

Differentiating, it suffices to prove `coth h - 1/h ≤ h/√(h²+9)`, which after clearing
denominators is

  `G(h) := h⁴ sinh²h - (h²+9) (h cosh h - sinh h)² ≥ 0`.

The informal write-up gets this from the Taylor expansion
`G(h) = Σ_{k≥4} 2^{2k-3} (2k-1) (2k-6)² / (2k)! · h^{2k}`, all of whose coefficients are
nonnegative.  Formalizing an infinite series with nonnegative coefficients is unpleasant, and
unnecessary.  Setting

  `Φ(y) := e^{2y} P₁(y) - e^y P₂(y) - P₃(y)`,
  `P₁ = y³-10y²+36y-36`,  `P₂ = y⁴+16y²-72`,  `P₃ = y³+10y²+36y+36`,

one has the algebraic identity `Φ(2h) = 16 e^{2h} G(h)`, so `G ≥ 0` iff `Φ ≥ 0` on `[0,∞)`.
And `Φ` is *closed* under differentiation in the family

  `Sf u v w y = e^{2y} u(y) - e^y v(y) - w(y)`,  `u` cubic, `v` quartic, `w` cubic,

under `u ↦ 2u + u'`, `v ↦ v + v'`, `w ↦ w'`.  Eight steps of that recurrence reach

  `Φ⁽⁸⁾(y) = 256 e^{2y} (y³+2y²-2y+10) - e^y (y⁴+32y³+352y²+1600y+2504)`,

and `Φ⁽ʲ⁾(0) = 0` for `j ≤ 7`.  So it is enough to prove `Φ⁽⁸⁾ ≥ 0` and integrate eight times.
For `Φ⁽⁸⁾`, divide by `e^y` and use just three terms of the exponential series: what is left is

  `56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5`,

every coefficient of which is positive.  No certificate, no series manipulation — one `ring`
identity and eight applications of "vanishes at `0` and has nonnegative derivative".

## Main statements

* `TaoSendov.sinh_sq_le`: `(h²+9)(h cosh h - sinh h)² ≤ h⁴ sinh²h`;
* `TaoSendov.log_sinh_div_le`: the displayed inequality;
* `TaoSendov.sinh_le_mul_exp`: the form actually used, `sinh h ≤ h exp (√(h²+9) - 3)`.
-/

namespace TaoSendov

open Real Set Filter

/-- `f` vanishes at `0` and has nonnegative derivative on `[0,∞)`, hence is nonnegative there. -/
private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  simpa [h0] using hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy

/-- `1 + y + y²/2 ≤ exp y` for `y ≥ 0`: three terms of the exponential series. -/
private lemma quad_le_exp {y : ℝ} (hy : 0 ≤ y) : 1 + y + y ^ 2 / 2 ≤ exp y := by
  suffices 0 ≤ exp y - 1 - y - y ^ 2 / 2 by linarith
  refine nonneg_of_deriv (f := fun t => exp t - 1 - t - t ^ 2 / 2)
    (g := fun t => exp t - 1 - t) (fun t => ?_) (by norm_num) (fun t ht => ?_) hy
  · exact ((((hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id' t)).sub
      ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by norm_num)
  · linarith [add_one_le_exp t]

/-- The family closed under differentiation: `e^{2y} u(y) - e^y v(y) - w(y)` with `u`, `w`
cubic and `v` quartic. -/
private noncomputable def Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) : ℝ :=
  exp (2 * y) * (u₃ * y ^ 3 + u₂ * y ^ 2 + u₁ * y + u₀)
    - exp y * (v₄ * y ^ 4 + v₃ * y ^ 3 + v₂ * y ^ 2 + v₁ * y + v₀)
    - (w₃ * y ^ 3 + w₂ * y ^ 2 + w₁ * y + w₀)

private lemma hasDerivAt_Sf (u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ y : ℝ) :
    HasDerivAt (fun t : ℝ => Sf u₃ u₂ u₁ u₀ v₄ v₃ v₂ v₁ v₀ w₃ w₂ w₁ w₀ t)
      (Sf (2 * u₃) (2 * u₂ + 3 * u₃) (2 * u₁ + 2 * u₂) (2 * u₀ + u₁)
          v₄ (v₃ + 4 * v₄) (v₂ + 3 * v₃) (v₁ + 2 * v₂) (v₀ + v₁)
          0 (3 * w₃) (2 * w₂) w₁ y) y := by
  simp only [Sf]
  have he2 : HasDerivAt (fun t : ℝ => exp (2 * t)) (exp (2 * y) * 2) y :=
    ((hasDerivAt_id' y).const_mul (2 : ℝ)).exp.congr_deriv (by ring)
  have he1 : HasDerivAt (fun t : ℝ => exp t) (exp y) y := hasDerivAt_exp y
  have hu : HasDerivAt (fun t : ℝ => u₃ * t ^ 3 + u₂ * t ^ 2 + u₁ * t + u₀)
      (3 * u₃ * y ^ 2 + 2 * u₂ * y + u₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul u₃).add
      ((hasDerivAt_pow 2 y).const_mul u₂)).add ((hasDerivAt_id' y).const_mul u₁)).add_const u₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hv : HasDerivAt (fun t : ℝ => v₄ * t ^ 4 + v₃ * t ^ 3 + v₂ * t ^ 2 + v₁ * t + v₀)
      (4 * v₄ * y ^ 3 + 3 * v₃ * y ^ 2 + 2 * v₂ * y + v₁) y := by
    have h := (((((hasDerivAt_pow 4 y).const_mul v₄).add
      ((hasDerivAt_pow 3 y).const_mul v₃)).add
      ((hasDerivAt_pow 2 y).const_mul v₂)).add ((hasDerivAt_id' y).const_mul v₁)).add_const v₀
    refine h.congr_deriv ?_
    norm_num
    ring
  have hw : HasDerivAt (fun t : ℝ => w₃ * t ^ 3 + w₂ * t ^ 2 + w₁ * t + w₀)
      (3 * w₃ * y ^ 2 + 2 * w₂ * y + w₁) y := by
    have h := ((((hasDerivAt_pow 3 y).const_mul w₃).add
      ((hasDerivAt_pow 2 y).const_mul w₂)).add ((hasDerivAt_id' y).const_mul w₁)).add_const w₀
    refine h.congr_deriv ?_
    norm_num
    ring
  exact (((he2.mul hu).sub (he1.mul hv)).sub hw).congr_deriv (by ring)

/-- The base of the induction, `Φ⁽⁸⁾ ≥ 0`.  Three terms of the exponential series leave a
polynomial with every coefficient positive. -/
private lemma step8 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0 y := by
  have : (1 + y + y ^ 2 / 2) * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560) := by
    grw [quad_le_exp hy]
    nlinarith [sq_nonneg (y - 1), pow_nonneg hy 3, sq_nonneg y]
  have : (0 : ℝ) ≤ 56 + 448 * y + 928 * y ^ 2 + 480 * y ^ 3 + 511 * y ^ 4 + 128 * y ^ 5 := by
    nlinarith [pow_nonneg hy 5, pow_nonneg hy 4, pow_nonneg hy 3, sq_nonneg y, hy]
  have h3 : (0 : ℝ) ≤ exp y * (256 * y ^ 3 + 512 * y ^ 2 - 512 * y + 2560)
      - (2504 + 1600 * y + 352 * y ^ 2 + 32 * y ^ 3 + 1 * y ^ 4) := by nlinarith
  calc
    _ ≤ _ := mul_nonneg (exp_pos y).le h3
    _ = _ := by
        simp only [Sf, two_mul, exp_add]
        ring

private lemma step7 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 256 512 (-512) 2560 1 32 352 1600 2504 0 0 0 0)
    (fun z => ?_) ?_ step8 hy
  · exact (hasDerivAt_Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0 z).congr_deriv
      (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step6 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 128 64 (-320) 1440 1 28 268 1064 1440 0 0 0 0)
    (fun z => ?_) ?_ step7 hy
  · exact (hasDerivAt_Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step5 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 64 (-64) (-96) 768 1 24 196 672 768 0 0 0 0)
    (fun z => ?_) ?_ step6 hy
  · exact (hasDerivAt_Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step4 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 y := by
  refine nonneg_of_deriv (g := Sf 32 (-80) 32 368 1 20 136 400 368 0 0 0 0)
    (fun z => ?_) ?_ step5 hy
  · exact (hasDerivAt_Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step3 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 y := by
  refine nonneg_of_deriv (g := Sf 16 (-64) 80 144 1 16 88 224 144 0 0 0 0)
    (fun z => ?_) ?_ step4 hy
  · exact (hasDerivAt_Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step2 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 y := by
  refine nonneg_of_deriv (g := Sf 8 (-44) 84 30 1 12 52 120 24 0 0 0 6)
    (fun z => ?_) ?_ step3 hy
  · exact (hasDerivAt_Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step1 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 y := by
  refine nonneg_of_deriv (g := Sf 4 (-28) 70 (-20) 1 8 28 64 (-40) 0 0 6 20)
    (fun z => ?_) ?_ step2 hy
  · exact (hasDerivAt_Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num
private lemma step0 (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 y := by
  refine nonneg_of_deriv (g := Sf 2 (-17) 52 (-36) 1 4 16 32 (-72) 0 3 20 36)
    (fun z => ?_) ?_ step1 hy
  · exact (hasDerivAt_Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 z).congr_deriv (by grind [Sf])
  · simp only [Sf]
    norm_num

/-- The algebraic bridge: `Φ(2h) = 16 e^{2h} G(h)`. -/
private lemma Sf_eq (h : ℝ) :
    Sf 1 (-10) 36 (-36) 1 0 16 0 (-72) 1 10 36 36 (2 * h)
    = 16 * exp h ^ 2 * (h ^ 4 * sinh h ^ 2 - (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2) := by
  have : exp h ≠ 0 := (exp_pos h).ne'
  have e4 : exp (2 * (2 * h)) = exp h ^ 4 := by simp [←exp_nat_mul]; ring
  have e2 : exp (2 * h) = exp h ^ 2 := by simp [←exp_nat_mul]
  simp only [Sf, sinh_eq, cosh_eq, e4, e2, exp_neg]
  field_simp
  ring

/-- **The key inequality.**  Equivalent to `coth h - 1/h ≤ h/√(h²+9)`. -/
theorem sinh_sq_le {h : ℝ} (hh : 0 ≤ h) :
    (h ^ 2 + 9) * (h * cosh h - sinh h) ^ 2 ≤ h ^ 4 * sinh h ^ 2 := by
  have h0 := step0 (2 * h) (by linarith)
  rw [Sf_eq] at h0
  have : (0 : ℝ) < 16 * exp h ^ 2 := by positivity
  nlinarith

/-- `sinh h ≤ h cosh h` for `h ≥ 0`; equivalently `h cosh h - sinh h ≥ 0`, which is what makes
the square root below legitimate. -/
private lemma sinh_le_mul_cosh {h : ℝ} (hh : 0 ≤ h) : sinh h ≤ h * cosh h := by
  have : 0 ≤ h * cosh h - sinh h := by
    refine nonneg_of_deriv (f := fun t => t * cosh t - sinh t) (g := fun t => t * sinh t)
      (fun t => ?_) (by simp) (fun t ht => mul_nonneg ht (sinh_nonneg_iff.2 ht)) hh
    exact (((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)).congr_deriv
      (by ring)
  linarith

/-- `√(h²+9) (h cosh h - sinh h) ≤ h² sinh h`: the square root of `TaoSendov.sinh_sq_le`, which is
the derivative inequality `coth h - 1/h ≤ h/√(h²+9)` cleared of denominators. -/
theorem sqrt_mul_sub_le {h : ℝ} (hh : 0 ≤ h) :
    sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) ≤ h ^ 2 * sinh h := by
  have : (0 : ℝ) ≤ h ^ 2 * sinh h := mul_nonneg (sq_nonneg h) (sinh_nonneg_iff.2 hh)
  have : (0 : ℝ) ≤ sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) :=
    mul_nonneg (sqrt_nonneg _) (by linarith [sinh_le_mul_cosh hh])
  have : (sqrt (h ^ 2 + 9) * (h * cosh h - sinh h)) ^ 2 ≤ (h ^ 2 * sinh h) ^ 2 := by
    convert sinh_sq_le hh
    · rw [mul_pow, sq_sqrt (by positivity)]
    ·  ring
  nlinarith

/-- **The sharp bound.**  This is `(lsh)` of the blog post. -/
theorem log_sinh_div_le {h : ℝ} (hh : 0 < h) :
    log (sinh h / h) ≤ sqrt (h ^ 2 + 9) - 3 := by
  set ψ : ℝ → ℝ := fun z => sqrt (z ^ 2 + 9) - 3 - (log (sinh z) - log z) with hψdef
  -- `ψ` has nonnegative derivative on `(0,∞)`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt ψ (z / sqrt (z ^ 2 + 9) - (cosh z / sinh z - 1 / z)) z := by
    intro z hz
    have hsinh : sinh z ≠ 0 := ne_of_gt (sinh_pos_iff.2 hz)
    apply HasDerivAt.sub
    · have h := (((hasDerivAt_pow 2 z).add_const 9).sqrt (ne_of_gt (by positivity))).sub_const 3
      refine h.congr_deriv ?_
      field_simp
      ring
    · exact (((hasDerivAt_sinh z).log hsinh).sub
        ((hasDerivAt_id' z).log (ne_of_gt hz))).congr_deriv (by field_simp)
  have hmono : MonotoneOn ψ (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hderiv z (by rwa [interior_Ioi] at hz)).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_)
    rw [interior_Ioi, mem_Ioi] at hz
    rw [(hderiv z hz).deriv, sub_nonneg, div_sub_div _ _ (ne_of_gt (sinh_pos_iff.2 hz))
      (ne_of_gt hz), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sqrt_mul_sub_le (le_of_lt hz)]
  -- `ψ → 0` as `z → 0⁺`
  have hslope : Tendsto (fun z => sinh z / z) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    simpa [slope_fun_def, div_eq_inv_mul, hasDerivAt_iff_tendsto_slope] using hasDerivAt_sinh 0
  have hlog : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsub : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
    have h1 : Tendsto (fun z => log (sinh z / z)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp
        (hslope.mono_left hsub)
    have h2 : Tendsto (fun z : ℝ => sqrt (z ^ 2 + 9) - 3)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have h9 : sqrt (9 : ℝ) = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      have hc : ContinuousAt (fun z => sqrt (z ^ 2 + 9) - 3) 0 := by fun_prop
      simpa [ContinuousWithinAt, h9] using hc.continuousWithinAt (s := Ioi (0 : ℝ))
    have heq : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0),
        ψ z = (sqrt (z ^ 2 + 9) - 3) - log (sinh z / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hψdef, log_div (ne_of_gt (sinh_pos_iff.2 hz)) (ne_of_gt hz)]
    simpa [tendsto_congr' heq] using h2.sub h1
  -- combine
  have hev : ∀ᶠ z : ℝ in nhdsWithin 0 (Ioi 0), ψ z ≤ ψ h := by
    have hmem : Ioo (0 : ℝ) h ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      mem_nhdsGT_iff_exists_Ioo_subset.2 (Exists.intro h (And.intro (mem_Ioi.2 hh) subset_rfl))
    filter_upwards [hmem] with z hz
    exact hmono (mem_Ioi.2 hz.1) (mem_Ioi.2 hh) (le_of_lt hz.2)
  have h0 : (0 : ℝ) ≤ ψ h := le_of_tendsto hlog hev
  have : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hh) hh
  rw [hψdef] at h0
  rw [log_div (ne_of_gt (sinh_pos_iff.2 hh)) (ne_of_gt hh)]
  linarith

/-- The form in which the estimate is used: `sinh h ≤ h exp (√(h²+9) - 3)`. -/
theorem sinh_le_mul_exp {h : ℝ} (hh : 0 ≤ h) :
    sinh h ≤ h * exp (sqrt (h ^ 2 + 9) - 3) := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · simp
  · have hd : (0 : ℝ) < sinh h / h := div_pos (sinh_pos_iff.2 hpos) hpos
    grw [← (log_le_iff_le_exp hd).1 (log_sinh_div_le hpos)]
    field_simp
    simp

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/BetaBound.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The simplified polar inequality `β(1) ≤ α/(3+α)`

This is `(lt) ⟹ (beta-bound)`.  Evaluating the integral,

  `∫₀¹ exp(α(-1 + (2-B)t)) dt = e^{-u} · sinh h / h`,   `u = αB/2`,  `h = α(2-B)/2`,

so `(lt)` says `e^u ≤ sinh h / h`, and `TaoSendov.log_sinh_div_le` turns that into
`u ≤ √(h²+9) - 3`.  Since `h = α - u`, squaring `u + 3 ≤ √((α-u)² + 9)` gives
`u(6 + 2α) ≤ α²`, that is `B ≤ α/(3+α)`.

The constant `3` is optimal: at `B = α/(3+α)` the slack in `(lt)` is `-α⁵/540 + α⁶/648`, so
the bound is tight to three orders at `α = 0`.  This is the one link of the chain with no room
in it anywhere.

One degenerate case has to be cleared first, and `(lt)` clears it: if `B ≥ 2` then the
integrand is at most `e^{-α} < 1` throughout, so the integral is below `1`.  Hence `B < 2` and
`h > 0`, which is what the `sinh` estimate needs.

## Main statements

* `TaoSendov.integral_exp_eq`: the closed form of the integral in `(lt)`;
* `TaoSendov.beta_lt_two`: `(lt)` forces `B < 2`;
* `TaoSendov.beta_le`: `(lt) ⟹ B ≤ α/(3+α)`.
-/

namespace TaoSendov

open MeasureTheory Real

variable {α B c : ℝ}

/-- `∫ₐᵇ exp(ct) dt = (exp(cb) - exp(ca))/c`. -/
lemma integral_exp_mul (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, exp (c * t)) = (exp (c * b) - exp (c * a)) / c := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (fun y : ℝ => exp y) hc
  rw [h, integral_exp]
  simp only [smul_eq_mul]
  field_simp

/-- The closed form of the integral in `(lt)`. -/
lemma integral_exp_eq (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = exp (-(α * B / 2)) * (sinh (α * (2 - B) / 2) / (α * (2 - B) / 2)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hEF : exp (-(α * B / 2)) = exp (-α) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : exp (α * (2 - B) * 1) = exp (α * (2 - B) / 2) * exp (α * (2 - B) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hneg : exp (-(α * (2 - B) / 2)) = (exp (α * (2 - B) / 2))⁻¹ := Real.exp_neg _
  have hF : exp (α * (2 - B) / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.sinh_eq, hEF, hsq, hneg]
  field_simp

/-- The same integral, in the form the logarithmic half of `(beta-bound)` uses. -/
lemma integral_exp_eq' (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = (exp (α * (1 - B)) - exp (-α)) / (α * (2 - B)) := by
  have hkpos : 0 < α * (2 - B) := by
    have : 0 < 2 - B := by linarith
    positivity
  have hrw : ∀ t : ℝ, α * (-1 + (2 - B) * t) = -α + α * (2 - B) * t := by
    intro t; ring
  simp only [hrw, Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul hkpos.ne' 0 1]
  simp only [mul_zero, Real.exp_zero]
  have hsum : exp (-α) * exp (α * (2 - B) * 1) = exp (α * (1 - B)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hsum]
  field_simp

/-- `(lt)` forces `B < 2`: otherwise the integrand never exceeds `e^{-α} < 1`. -/
lemma beta_lt_two (hα : 0 < α)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B < 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono : (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      ≤ ∫ _t in (0 : ℝ)..1, exp (-α) := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous fun t : ℝ =>
        exp (α * (-1 + (2 - B) * t))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun _ : ℝ => exp (-α)).intervalIntegrable _ _) ?_
    intro u hu
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg (mul_nonneg hα.le hu.1) (sub_nonneg.2 hcon)]
  have hval : (∫ _t in (0 : ℝ)..1, exp (-α)) = exp (-α) := by simp
  have hone : exp (-α) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  rw [hval] at hmono
  linarith

/-- **`(lt) ⟹ (beta-bound)`.**  The `α/(3+α)` of the blog post. -/
theorem beta_le (hα : 0 < α) (hB0 : 0 ≤ B)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B ≤ α / (3 + α) := by
  have hB2 : B < 2 := beta_lt_two hα hlt
  rw [integral_exp_eq hα hB2] at hlt
  set u : ℝ := α * B / 2 with hudef
  set h : ℝ := α * (2 - B) / 2 with hhdef
  have hhpos : 0 < h := by
    rw [hhdef]
    have : 0 < 2 - B := by linarith
    positivity
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  -- `1 ≤ e^{-u} sinh h / h` is `e^u ≤ sinh h / h`
  have h1 : exp u ≤ sinh h / h := by
    rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos u)] at hlt
    linarith
  have h2 : u ≤ Real.log (sinh h / h) := by
    rw [← Real.log_exp u]
    exact Real.log_le_log (Real.exp_pos u) h1
  have h3 : u ≤ Real.sqrt (h ^ 2 + 9) - 3 := h2.trans (log_sinh_div_le hhpos)
  -- square; `h = α - u`
  have hhu : h = α - u := by rw [hhdef, hudef]; ring
  have hsq : Real.sqrt (h ^ 2 + 9) ^ 2 = h ^ 2 + 9 := Real.sq_sqrt (by positivity)
  have h4 : (u + 3) ^ 2 ≤ h ^ 2 + 9 := by
    have hnn : (0 : ℝ) ≤ u + 3 := by linarith
    nlinarith [h3, hsq, Real.sqrt_nonneg (h ^ 2 + 9)]
  have h5 : u * (6 + 2 * α) ≤ α ^ 2 := by rw [hhu] at h4; nlinarith [h4]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 + α)]
  rw [hudef] at h5
  nlinarith [h5, hα]

/-- **The logarithmic half of `(beta-bound)`:** `log α ≤ α(1 - β(1))`.  From `(lt)`,
`e^{α(1-B)} ≥ α(2-B) + e^{-α} > α`, since `B ≤ 1` makes `2 - B ≥ 1`. -/
theorem log_le_alpha_mul (hα : 0 < α) (hB1 : B ≤ 1)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) :
    Real.log α ≤ α * (1 - B) := by
  have hB2 : B < 2 := by linarith
  rw [integral_exp_eq' hα hB2] at hlt
  have hden : (0 : ℝ) < α * (2 - B) := by
    have : (0 : ℝ) < 2 - B := by linarith
    positivity
  rw [le_div_iff₀ hden, one_mul] at hlt
  have hge : α ≤ α * (2 - B) := by nlinarith
  have hlt' : α < exp (α * (1 - B)) := by
    have := Real.exp_pos (-α)
    linarith
  exact (Real.log_le_iff_le_exp hα).2 hlt'.le

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Stat.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# From `(1le)` to `stat`

This is `(1le) + (beta-bound) ⟹ stat`.  The right-hand side of `(1le)`,

  `β(1)/(2α(1-β(1))) + β(1)/(4α) + 1/(2(n-1)) + β(1)/(4α(n-1))`
      `+ a⁴ n(n-1)(n-2) β(1)/(4α) ∫₀¹ t³ β(t)^((n-4)/2) dt`,

is monotone increasing in `β(1)`, so `(beta-bound)` lets `β(1)` be replaced throughout by
`α/(3+α)`.  Under that substitution every term becomes the corresponding term of `TaoSendov.R`:
`β(1)/(2α(1-β(1)))` becomes `1/6`, `β(1)/(4α)` becomes `1/(4(3+α))`, and `ax`, which is
`1 - β(1)/2 - α/(n-1)`, becomes exactly `TaoSendov.c n α`.

Monotonicity of the integral term is the only part that is not immediate.  `ax` *decreases* as
`β(1)` grows, and `TaoSendov.QQ` decreases in its first argument on `[0,1]`, so the integrand
grows — `TaoSendov.integral_QQ_anti`.  Nonnegativity of `β(t)` is needed only at the actual value
`ax`, where it is `(ax)² ≤ a²`, i.e. `x² ≤ 1`; at the substituted value it comes free from the
pointwise comparison, the same way `TaoSendov.integral_anti` gets it in the batching argument.

## Main statements

* `TaoSendov.mul_eq_c`: `ax = 1 - β(1)/2 - α/(n-1)`, and hence `c n α ≤ ax` under `(beta-bound)`;
* `TaoSendov.stat_of_one_le`: `(1le) + (beta-bound) ⟹ 1 ≤ R n α`.
-/

namespace TaoSendov

open MeasureTheory

variable {n : ℕ} {a x α : ℝ}

/-- `ax = 1 - β(1)/2 - α/(n-1)`: the blog post's rearrangement of `β(1) = 1 - 2ax + a²`. -/
lemma mul_eq_c (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [QQ, hα]
  field_simp
  ring

/-- Under `(beta-bound)`, `TaoSendov.c n α ≤ ax`: the substitution only ever lowers `ax`. -/
lemma c_le_mul (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ≤ a * x := by
  rw [mul_eq_c hn hα]
  simp only [c]
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have : α / (2 * (3 + α)) = (α / (3 + α)) / 2 := by field_simp
  rw [this]
  linarith

/-- `(beta-bound)` supplies the feasibility constraint `c² ≤ A` that `TaoSendov.stat_lt_one`
requires.  It is `c ≤ ax` squared, together with `x² ≤ 1`: the substitution can only lower
`ax`, and `ax` is already at most `a`. -/
lemma feasible_of_beta (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ^ 2 ≤ A n α := by
  have hcpos : 0 < c n α := c_pos_of_le_half_M hn hα0.le (alpha_le_half hn hα)
  have hcle : c n α ≤ a * x := c_le_mul hn hα hα0 hbeta
  rw [A_eq_sq hn hα]
  nlinarith [hcpos, hcle, sq_nonneg a, sq_nonneg x]

/-- **`(1le) + (beta-bound) ⟹ stat`.** -/
theorem stat_of_one_le (hn : 5 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (h1le : 1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :
    1 ≤ R n α := by
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hA : A n α = a ^ 2 := A_eq_sq hn2 hα
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1
  -- the standing facts about `β(1)`
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have hkey : B1 * (3 + α) ≤ α := by
    rw [← le_div_iff₀ h3]; exact hbeta
  have hB1lt : B1 < 1 := by nlinarith [hα0, hB0]
  -- the four elementary terms
  have t1 : B1 / (2 * α * (1 - B1)) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hkey, hB0, hα0]
  have t2 : B1 / (4 * α) ≤ 1 / (4 * (3 + α)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hkey]
  have t4 : B1 / (4 * α * M n) ≤ 1 / (4 * M n * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hM]
  -- the integral term
  have hcle : c n α ≤ a * x := c_le_mul hn2 hα hα0 hbeta
  have hr : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hI : (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (c n α) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) :=
    integral_QQ_anti hcle hfeas hr 3
  have hInn : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfeas u) _)
  have hpre : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    positivity
  have t5 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
      ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2) := by
    have hcoef : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hkey, hpre]
    have hstep1 : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / (4 * α)
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2))
        ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
          * (∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
      mul_le_mul_of_nonneg_right hcoef hInn
    refine hstep1.trans ?_
    have hcnn : (0 : ℝ) ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) := by
      rw [hA]; positivity
    refine mul_le_mul_of_nonneg_left ?_ hcnn
    simpa only [Q_eq_QQ, hA] using hI
  rw [R]
  linarith

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Simplified.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# From the raw origin inequality to its `α`, `β(1)` form

This is `(origin-exact) + (beta-bound) ⟹ (1le)`.  The work is in replacing

  `∫₀¹ t β(t)^((n-2)/2) dt`

by a Beta value plus the `t³` integral that `stat` is stated with.  Writing `β` as a sum of
squares, `β(t) = (1-axt)² + a²t²(1-x²)`, the blog post applies the mean value theorem to
`s ↦ ((1-axt)² + s)^((n-2)/2)`.  Here that step is Bernoulli's inequality instead: dividing

  `(P+Q)^p ≤ P^p + p Q (P+Q)^(p-1)`

through by `(P+Q)^p` turns it into `1 ≤ θ^p + p(1-θ)` at `θ = P/(P+Q)`, which is exactly
`one_add_mul_self_le_rpow_one_add`.  No derivative and no mean value theorem is needed.

After that, `∫₀¹ t (1-axt)^(n-2) dt` is enlarged to `[0, 1/ax]` — legitimate since `ax ≤ 1` and
the integrand stays nonnegative — and evaluated by `TaoSendov.integral_chord_lin`, the `k = 1`
Beta integral of `TaoSendov.Common.Chord`.  What is left is algebra in `α` and `β(1)`, using
`1 - x² ≤ β(1)` (which is `(x-a)² ≥ 0`) and `ax = 1 - β(1)/2 - α/(n-1)`.

`(beta-bound)` enters only through `β(1) < 1`, which is what makes `x > a/2 > 0`, hence `1/x²`
finite and `1/(ax) ≥ 1`.

## Main statements

* `TaoSendov.rpow_add_le_of_one_le`: the Bernoulli form of the mean-value step;
* `TaoSendov.beta_split`: the pointwise consequence for `β`;
* `TaoSendov.one_le_of_origin`: `(origin-exact) + (beta-bound) ⟹ (1le)`.
-/

namespace TaoSendov

open MeasureTheory

variable {n : ℕ} {a x t α : ℝ}

/-- `(P+Q)^p ≤ P^p + p Q (P+Q)^(p-1)` for `p ≥ 1`.  This is the blog post's mean-value step,
obtained from Bernoulli's inequality after dividing by `(P+Q)^p`. -/
lemma rpow_add_le_of_one_le {P Q p : ℝ} (hP : 0 ≤ P) (hPQ : 0 < P + Q) (hp : 1 ≤ p) :
    (P + Q) ^ p ≤ P ^ p + p * Q * (P + Q) ^ (p - 1) := by
  have hθ : (0 : ℝ) ≤ P / (P + Q) := div_nonneg hP hPQ.le
  have hb := one_add_mul_self_le_rpow_one_add (s := P / (P + Q) - 1) (by linarith) hp
  rw [show (1 : ℝ) + (P / (P + Q) - 1) = P / (P + Q) by ring] at hb
  have hpow : (0 : ℝ) < (P + Q) ^ p := Real.rpow_pos_of_pos hPQ p
  have hfrac : (P / (P + Q)) ^ p * (P + Q) ^ p = P ^ p := by
    rw [← Real.mul_rpow hθ hPQ.le]
    congr 1
    field_simp
  have hsub : (P + Q) ^ (p - 1) = (P + Q) ^ p / (P + Q) := by
    rw [Real.rpow_sub hPQ, Real.rpow_one]
  have key : (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q)) ≤ P ^ p := by
    calc (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q))
        = (1 + p * (P / (P + Q) - 1)) * (P + Q) ^ p := by
          field_simp
          ring
      _ ≤ (P / (P + Q)) ^ p * (P + Q) ^ p := mul_le_mul_of_nonneg_right hb hpow.le
      _ = P ^ p := hfrac
  rw [hsub]
  linarith

/-- `ax t < 1` on `[0,1]`, so the chord `1 - axt` is positive. -/
lemma one_sub_mul_pos (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1 - a * x * t := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [mul_nonneg ht0 (mul_nonneg ha.le (neg_nonneg.2 h))]
  · have hx1 : x ≤ 1 := by nlinarith
    have h1 : a * x * t ≤ a * x * 1 :=
      mul_le_mul_of_nonneg_left ht1 (mul_pos ha h).le
    nlinarith [h1]

/-- The pointwise step: `β^((n-2)/2)` split into a chord power and a `β^((n-4)/2)` remainder. -/
lemma beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)
      ≤ (1 - a * x * t) ^ ((n : ℝ) - 2)
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
          * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < 1 - a * x * t := one_sub_mul_pos ha ha1 hx ht0 ht1
  have hP : (0 : ℝ) ≤ (1 - a * x * t) ^ 2 := sq_nonneg _
  have hQ : (0 : ℝ) ≤ a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    have : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
    positivity
  have hsum : QQ (a * x) (a ^ 2) t
      = (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    rw [QQ_eq]; ring
  have hPQ : (0 : ℝ) < (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by positivity
  have hp : (1 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hb := rpow_add_le_of_one_le hP hPQ hp
  rw [← hsum] at hb
  -- `((1-axt)²)^((n-2)/2) = (1-axt)^(n-2)`
  have hchord : ((1 - a * x * t) ^ 2 : ℝ) ^ (((n : ℝ) - 2) / 2)
      = (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast (1 - a * x * t) 2, ← Real.rpow_mul hy.le]
    congr 1
    push_cast
    ring
  -- `(n-2)/2 - 1 = (n-4)/2`
  have hexp : ((n : ℝ) - 2) / 2 - 1 = ((n : ℝ) - 4) / 2 := by ring
  rw [hchord, hexp] at hb
  exact hb

/-- The integral form of the split, with the chord piece evaluated by the Beta integral. -/
lemma integral_beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hax : 0 < a * x) :
    (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
          * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hr2 : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hr4 : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  -- the three continuous integrands
  have hc1 : Continuous fun t : ℝ => t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    simpa using continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hr2
  have hc2 : Continuous fun t : ℝ => t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
    (by fun_prop : Continuous fun t : ℝ => t).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hc3 : Continuous fun t : ℝ =>
      ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
        * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
    (continuous_pow_mul_QQ (a * x) (a ^ 2) 3 hr4).const_mul _
  -- integrate the pointwise bound
  have hstep : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + ∫ t in (0 : ℝ)..1, ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
            * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) := by
    rw [← intervalIntegral.integral_add (hc2.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
      ((hc2.add hc3).intervalIntegrable _ _) ?_
    intro u hu
    have h := beta_split hn ha ha1 hx hu.1 hu.2
    have hu0 : (0 : ℝ) ≤ u := hu.1
    nlinarith [h, hu0, Real.rpow_nonneg (QQ_nonneg (by nlinarith [sq_nonneg a] :
      (a * x) ^ 2 ≤ a ^ 2) u) (((n : ℝ) - 4) / 2)]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  gcongr
  -- the chord piece: enlarge to `[0, 1/(ax)]` and evaluate
  have hrest : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
      ≤ ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    have hone : (1 : ℝ) ≤ 1 / (a * x) := by rw [le_div_iff₀ hax]; linarith
    have hadd : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + (∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        = ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
    have hnn : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
      refine intervalIntegral.integral_nonneg hone ?_
      intro u hu
      have : (0 : ℝ) ≤ 1 - a * x * u := by
        have := hu.2
        rw [le_div_iff₀ hax] at this
        linarith
      exact mul_nonneg (by linarith [hu.1]) (Real.rpow_nonneg this _)
    linarith
  refine hrest.trans_eq ?_
  rw [integral_chord_lin hs hax]
  congr 1
  ring

/-- **`(origin-exact) + (beta-bound) ⟹ (1le)`.**  `(beta-bound)` enters only as `β(1) < 1`. -/
theorem one_le_of_origin (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hB1lt : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hMn : M n = (n : ℝ) - 1 := rfl
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set I3 : ℝ := ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) with hI3def
  -- `1 - β(1) = 2ax - a²`, so `β(1) < 1` gives `ax > 0`
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  -- `x² ≥ 1 - β(1)`, which is `(x-a)² ≥ 0`
  have hxsq : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
  have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
  have hinv : 1 / x ^ 2 ≤ 1 / (1 - B1) := by
    apply one_div_le_one_div_of_le (by linarith) hxsq
  have hone_sub : 1 - x ^ 2 ≤ B1 := by linarith
  -- the integral bound
  have hsplit := integral_beta_split hn ha ha1 hx hax
  have hI3nn : (0 : ℝ) ≤ I3 := by
    rw [hI3def]
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    have hfe : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfe u) _)
  -- multiply the split by `a² n M` and simplify the Beta term to `1/x²`
  have hcoef : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hbeta_simp : a ^ 2 * (n : ℝ) * M n
      * (1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))) = 1 / x ^ 2 := by
    have hane : (a : ℝ) ≠ 0 := ha.ne'
    have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
    have hn1 : ((n : ℝ) - 1) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [hMn]
    field_simp
  have hkey : a ^ 2 * n * M n
        * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / x ^ 2 + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3 := by
    refine (mul_le_mul_of_nonneg_left hsplit hcoef).trans_eq ?_
    rw [mul_add, hbeta_simp]
    congr 1
    ring
  -- assemble
  have hax_eq : a * x = 1 - B1 / 2 - α / M n := mul_eq_c hn2 hα
  have hmain : 2 * α ≤ B1 / (1 - B1) + B1 / 2 + α / M n + B1 / (2 * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    have hlast : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3
        ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
      have hc : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) / 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
        positivity
      nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.2 hone_sub)) hI3nn]
    have hfirst : (1 - x ^ 2) / (2 * M n) ≤ B1 / (2 * M n) := by
      apply div_le_div_of_nonneg_right hone_sub (by positivity)
    have hne1 : (1 : ℝ) - B1 ≠ 0 := by linarith
    have hrec : 1 / (1 - B1) = 1 + B1 / (1 - B1) := by
      field_simp
      ring
    have hinv' : 1 / x ^ 2 ≤ 1 + B1 / (1 - B1) := by rw [← hrec]; exact hinv
    -- do NOT rewrite `hax_eq` into `horigin`: it would also rewrite the `a * x` inside the
    -- integral, and the resulting atom would no longer match `hkey`
    linarith [horigin, hkey, hinv', hfirst, hlast, hax_eq]
  -- divide by `2α`
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hne : (1 : ℝ) - B1 ≠ 0 := by linarith
  have h1 : 2 * α * (B1 / (2 * α * (1 - B1))) = B1 / (1 - B1) := by
    field_simp
  have h2 : 2 * α * (B1 / (4 * α)) = B1 / 2 := by
    field_simp
    ring
  have h3 : 2 * α * (1 / (2 * M n)) = α / M n := by
    field_simp
  have h4 : 2 * α * (B1 / (4 * α * M n)) = B1 / (2 * M n) := by
    field_simp
    ring
  have h5 : 2 * α * ((a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / (4 * α) * I3)
      = (a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ h2α
  rw [mul_one, mul_add, mul_add, mul_add, mul_add, h1, h2, h3, h4, h5]
  exact hmain

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Alpha17.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The bound `α ≤ 17`

This is `(beta-bound) + (origin-exact) ⟹ (17)`, the last link of the chain.  Suppose `α > 17`.
Feasibility gives `n - 1 ≥ 2α > 34`, so `n ≥ 36`, and after discarding `ax > 0` and bounding
`1 - x² ≤ 1`, `(origin-exact)` reads

  `2α ≤ 1/(2(n-1)) + a² n (n-1) ∫₀¹ t β(t)^((n-2)/2) dt`.

The integral is split by `TaoSendov.integral_le_tail_lin` — the `k = 1` instance of the chord
bound — into a Beta value plus `β(1)^((n-2)/2)/2`.  Both halves of `(beta-bound)` are then
used, and this is the only place where the logarithmic half is needed:

* `x² ≥ 1 - β(1) ≥ log α / α` turns the Beta term into `4α/log α`;
* `β(1) ≤ e^{β(1)-1} ≤ α^{-1/α}` makes the second term decay geometrically.

Dividing by `α` leaves `2 ≤ 1/(2(n-1)α) + 4/log α + T`, and the substitution
`v := (n-1)/(2α) - 1` (the write-up's `u = a²/(1-a²)`) turns `T` into
`v(2(v+1) + 1/α) α^{-v} · α^{1/(2α)}`, which is bounded by an ordinary polynomial inequality
after four terms of the exponential series.  The three pieces come to `0.0009 + 1.4135 +
0.5054 = 1.920 < 2`.

The write-up uses `∫₀^∞ t e^{-ct} dt` here and reaches `1.948`; the Beta route used instead
reaches `1.817`, and the extra room is what pays for the crude constants below.

## Main statements

* `TaoSendov.log_seventeen_ge`, `TaoSendov.log_le_div_exp_one`: the two facts about `log` needed;
* `TaoSendov.alpha_le_seventeen`: `(beta-bound) + (origin-exact) ⟹ α ≤ 17`.
-/

namespace TaoSendov

open MeasureTheory Real

/-! ### Elementary estimates -/

/-- Four terms of the exponential series. -/
lemma quartic_le_exp {z : ℝ} (hz : 0 ≤ z) : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `log t ≤ t / e`, the tangent bound at `t = e`. -/
lemma log_le_div_exp_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := t / exp 1) (by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- `exp z ≤ 1/(1-z)` for `z < 1`, from `1 - z ≤ e^{-z}`. -/
lemma exp_le_one_div_one_sub {z : ℝ} (hz : z < 1) : exp z ≤ 1 / (1 - z) := by
  have hpos := Real.exp_pos z
  have h1 : (0 : ℝ) < 1 - z := by linarith
  have h := Real.add_one_le_exp (-z)
  rw [Real.exp_neg] at h
  have h2 : (1 - z) * exp z ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  rw [le_div_iff₀ h1]
  linarith

/-- `2.83 ≤ log 17`, via `log 16 + log(17/16) ≥ 4 log 2 + 1/17`. -/
lemma log_seventeen_ge : (2.83 : ℝ) ≤ Real.log 17 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hfrac : (1 : ℝ) - 16 / 17 ≤ Real.log (17 / 16) := by
    have h := Real.log_le_sub_one_of_pos (x := (16 : ℝ) / 17) (by norm_num)
    rw [show (16 : ℝ) / 17 = ((17 : ℝ) / 16)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hsplit : Real.log 17 = Real.log 16 + Real.log (17 / 16) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [hsplit, h16]
  linarith

/-- The polynomial bound behind the geometric term: `v(2v + 2 + 1/17) e^{-2.83 v} ≤ 0.4118`
for `v ≥ 0`.  Four terms of the exponential series suffice; the true maximum is `0.3722`. -/
lemma tail_poly_bound {v : ℝ} (hv : 0 ≤ v) :
    v * (2 * (v + 1) + 1 / 17) * exp (-(2.83 * v)) ≤ 0.4118 := by
  have hz : (0 : ℝ) ≤ 2.83 * v := by linarith
  have hexp := quartic_le_exp hz
  have hpos : (0 : ℝ) < exp (2.83 * v) := Real.exp_pos _
  have hneg : exp (-(2.83 * v)) = (exp (2.83 * v))⁻¹ := Real.exp_neg _
  rw [hneg, mul_inv_le_iff₀ hpos]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 0.4118))
  nlinarith [hv, sq_nonneg v, sq_nonneg (v - 1 / 2), pow_nonneg hv 3]

/-! ### The bound -/

set_option maxHeartbeats 1000000 in
-- one long proof rather than several: the `v`-substitution ties the integral bound, the two
-- exponential factors and the final arithmetic together, and splitting it would mean carrying
-- a dozen hypotheses across the boundary
/-- **`(beta-bound) + (origin-exact) ⟹ α ≤ 17`.** -/
theorem alpha_le_seventeen {n : ℕ} {a x α : ℝ} (hn : 5 ≤ n)
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α))
    (hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    α ≤ 17 := by
  by_contra hcon
  rw [not_le] at hcon
  have hn2 : 2 ≤ n := by omega
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hα0 : (0 : ℝ) < α := by linarith
  -- feasibility forces `n - 1 ≥ 2α > 34`
  have hMge : 2 * α ≤ M n := by linarith [alpha_le_half hn2 hα]
  have hM34 : (34 : ℝ) < M n := by linarith
  have hMn : M n = (n : ℝ) - 1 := rfl
  -- the standing facts about `β(1)`
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set r : ℝ := ((n : ℝ) - 2) / 2 with hrdef
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ B1 := QQ_nonneg hfeas 1
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hB1lt : B1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  have hr : (0 : ℝ) < r := by rw [hrdef]; rw [hMn] at hM34; linarith
  -- `log α ≥ 2.83`
  have hlog17 : (2.83 : ℝ) ≤ Real.log α :=
    le_trans log_seventeen_ge (Real.log_le_log (by norm_num) hcon.le)
  have hlogpos : (0 : ℝ) < Real.log α := by linarith
  -- `x² ≥ 1 - β(1) ≥ log α / α`
  have hxsq : Real.log α / α ≤ x ^ 2 := by
    have h1 : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
    rw [div_le_iff₀ hα0]
    nlinarith [hlogb, h1]
  -- the chord split of the integral
  have hI1 := integral_le_tail_lin hfeas hax haxle hr
  set I1 : ℝ := ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ r with hI1def
  have hprod : (r + 1) * (r + 2) = (n : ℝ) * ((n : ℝ) + 2) / 4 := by rw [hrdef]; ring
  have hane : (a : ℝ) ≠ 0 := ha.ne'
  have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hMn] at hM34; linarith
  have hbeta_term : a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))))
      = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) := by
    rw [hprod]
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := by linarith
    field_simp
  have hcoefnn : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hstep : a ^ 2 * n * M n * I1
      ≤ 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    calc a ^ 2 * n * M n * I1
        ≤ a ^ 2 * n * M n * (1 / ((a * x) ^ 2 * ((r + 1) * (r + 2))) + B1 ^ r / 2) :=
          mul_le_mul_of_nonneg_left hI1 hcoefnn
      _ = 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) + a ^ 2 * n * M n * (B1 ^ r / 2) := by
          rw [mul_add, hbeta_term]
  -- `4M/(x²(n+2)) ≤ 4/x² ≤ 4α/log α`
  have hfourx : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 * α / Real.log α := by
    have h1 : 4 * M n / (x ^ 2 * ((n : ℝ) + 2)) ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : M n ≤ (n : ℝ) + 2 := by rw [hMn]; linarith
      nlinarith [sq_nonneg x, hxpos]
    have h2 : (4 : ℝ) / x ^ 2 ≤ 4 * α / Real.log α := by
      rw [div_le_div_iff₀ (by positivity) hlogpos]
      have := hxsq
      rw [div_le_iff₀ hα0] at this
      nlinarith [this]
    linarith
  have hfirst : (1 - x ^ 2) / (2 * M n) ≤ 1 / (2 * M n) := by
    have hD : (0 : ℝ) < 2 * M n := by linarith
    rw [div_le_div_iff₀ hD hD]
    nlinarith [sq_nonneg x, hD]
  have hmain : 2 * α ≤ 1 / (2 * M n) + 4 * α / Real.log α + a ^ 2 * n * M n * (B1 ^ r / 2) := by
    linarith [horigin, hstep, hfourx, hfirst, hax]
  -- the substitution `v = M/(2α) - 1`
  -- `obtain` rather than `set`: a `set` binding is a local *definition*, which `linarith`
  -- zeta-reduces back into `M n / (2 * α) - 1`, making its goals nonlinear in `α`
  obtain ⟨v, hvdef⟩ : ∃ w : ℝ, w = M n / (2 * α) - 1 := ⟨_, rfl⟩
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hv0 : 0 ≤ v := by
    rw [hvdef, sub_nonneg, le_div_iff₀ h2α]
    linarith
  have hMv : M n = 2 * α * (v + 1) := by
    rw [hvdef]
    field_simp
    ring
  have ha2 : a ^ 2 = 1 - 2 * α / M n := by
    rw [hα]
    field_simp
    ring
  have hav : a ^ 2 * M n / (2 * α) = v := by
    rw [ha2, hvdef]
    field_simp
  -- `β(1) ≤ exp(-log α/α)`, hence `β(1)^r ≤ exp(-(v+1)log α) exp(log α/(2α))`
  have hB1exp : B1 ≤ exp (-(Real.log α / α)) := by
    have h1 : B1 ≤ exp (B1 - 1) := by linarith [Real.add_one_le_exp (B1 - 1)]
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have : Real.log α / α ≤ 1 - B1 := by rw [div_le_iff₀ hα0]; linarith
    linarith
  have hrM : r = (M n - 1) / 2 := by rw [hrdef, hMn]; ring
  have hB1r : B1 ^ r ≤ exp (-(v * Real.log α)) / α * exp (Real.log α / (2 * α)) := by
    have h1 : B1 ^ r ≤ exp (-(Real.log α / α) * r) := by
      calc B1 ^ r ≤ exp (-(Real.log α / α)) ^ r := Real.rpow_le_rpow hB0 hB1exp hr.le
        _ = exp (-(Real.log α / α) * r) := by rw [← Real.exp_mul]
    refine h1.trans_eq ?_
    have hexpo : -(Real.log α / α) * r
        = (-(v * Real.log α) + -Real.log α) + Real.log α / (2 * α) := by
      rw [hrM, hMv]
      field_simp
      ring
    have hinv : exp (-Real.log α) = 1 / α := by
      rw [Real.exp_neg, Real.exp_log hα0]
      ring
    rw [hexpo, Real.exp_add, Real.exp_add, hinv]
    ring
  -- the two exponential factors
  have hvexp : exp (-(v * Real.log α)) ≤ exp (-(2.83 * v)) :=
    Real.exp_le_exp.2 (by nlinarith [hv0, hlog17])
  have he1 : (2.7 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsecexp : exp (Real.log α / (2 * α)) ≤ 1 / (1 - 0.1852) := by
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_one_div_one_sub (by norm_num))
    have h := log_le_div_exp_one hα0
    have h27 : α / exp 1 ≤ α / 2.7 :=
      div_le_div_of_nonneg_left hα0.le (by norm_num) he1.le
    rw [div_le_iff₀ h2α]
    have hlast : α / 2.7 ≤ 0.1852 * (2 * α) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2.7)]
      nlinarith [hα0]
    linarith [h, h27, hlast]
  -- assemble the geometric term
  have hnv : (n : ℝ) = 2 * α * (v + 1) + 1 := by
    rw [← hMv, hMn]
    ring
  have hthird : a ^ 2 * n * M n * (B1 ^ r / 2) ≤ 0.50543 * α := by
    have hexpnn : (0 : ℝ) ≤ exp (-(2.83 * v)) := (Real.exp_pos _).le
    have hkey : a ^ 2 * n * M n * (B1 ^ r / 2) = (n : ℝ) * α * v * B1 ^ r := by
      rw [← hav]
      field_simp
    rw [hkey]
    have hstep1 : (n : ℝ) * α * v * B1 ^ r
        ≤ (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852))) := by
      refine mul_le_mul_of_nonneg_left (hB1r.trans ?_) (by positivity)
      refine mul_le_mul ?_ hsecexp (Real.exp_pos _).le (by positivity)
      gcongr
    refine hstep1.trans ?_
    have hfinal : (n : ℝ) * α * v * (exp (-(2.83 * v)) / α * (1 / (1 - 0.1852)))
        = α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) * (1 / (1 - 0.1852)) := by
      rw [hnv]
      field_simp
    rw [hfinal]
    have hbound : v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v)) ≤ 0.4118 := by
      refine le_trans ?_ (tail_poly_bound hv0)
      have hinv : (1 : ℝ) / α ≤ 1 / 17 := by
        rw [div_le_div_iff₀ hα0 (by norm_num)]; linarith
      have hprod : (0 : ℝ) ≤ v * exp (-(2.83 * v)) := mul_nonneg hv0 hexpnn
      nlinarith [mul_le_mul_of_nonneg_left hinv hprod]
    have hscale : α * (v * (2 * (v + 1) + 1 / α) * exp (-(2.83 * v))) ≤ α * 0.4118 :=
      mul_le_mul_of_nonneg_left hbound hα0.le
    linarith [hscale]
  -- the numeric contradiction
  have hlogterm : 4 * α / Real.log α ≤ 1.41343 * α := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hlog17, hα0]
  have hMterm : 1 / (2 * M n) ≤ 1 / 68 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith [hmain, hlogterm, hMterm, hthird, hcon]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Reduction/Main.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The polar and origin inequalities are incompatible

This is the top of the development.  The blog post's argument, after the complex-analytic part
that is not formalized here, produces two inequalities about a degree `n`, a zero `0 < a < 1`
and the real part `x` of the mean of the reciprocal critical-point data:

* the **raw polar inequality** `(1Q)`, `1 ≤ ∫₀¹ P(t)^((n-1)/2) dt`;
* the **raw origin inequality** `(origin-exact)`.

`TaoSendov.polar_origin_incompatible` says they cannot both hold for `n ≥ 5`.  Neither statement
mentions a polynomial or a complex number, so the theorem is a self-contained assertion about
two real numbers.

## The chain

```
                      polar_exp            beta_le
   (1Q)  ─────────────────────▶  (lt)  ─────────────────▶  β(1) ≤ α/(3+α)
                                   │                            │
                                   │ log_le_alpha_mul           │
                                   ▼                            │
                          log α ≤ α(1-β(1))                     │
                                   │                            │
   (origin-exact) ─────────────────┴──────────────────▶  α ≤ 17 │
          │              alpha_le_seventeen                     │
          │ one_le_of_origin                                    │
          ▼                                                     ▼
        (1le) ───────────────────────────────────────────▶  1 ≤ R n α
                          stat_of_one_le                        │
                                                                │ stat_lt_one
                                                                ▼
                                                              False
```

Both halves of `(beta-bound)` are needed, and each is used exactly once: the rational half
`β(1) ≤ α/(3+α)` by `TaoSendov.stat_of_one_le`, to substitute for `β(1)` in `(1le)`, and the
logarithmic half by `TaoSendov.alpha_le_seventeen`, to bound `1/x²`.

## Main statements

* `TaoSendov.polar_origin_incompatible`: the two raw inequalities have no common solution.
-/

namespace TaoSendov

open MeasureTheory

/-- (Port) The numerical claim `stat_lt_one` of `TaoSendov.Main` for one degree `n`, as a
hypothesis: the variants below need it only for some degrees. -/
def NumClaim (n : ℕ) : Prop :=
  ∀ {α : ℝ}, 0 ≤ α → α ≤ 17 → c n α ^ 2 ≤ A n α → R n α < 1

/-- **The polar and origin inequalities are incompatible.**  For `n ≥ 5` there is no
`0 < a < 1` and `|x| ≤ 1` satisfying both the raw polar inequality `(1Q)` and the raw origin
inequality `(origin-exact)`. -/
theorem polar_origin_incompatible {n : ℕ} (hnum : NumClaim n) (hn : 5 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    False := by
  have hn2 : 2 ≤ n := by omega
  have hα0 : 0 < α := alpha_pos hn2 ha1 ha.le hα
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ QQ (a * x) (a ^ 2) 1 := QQ_nonneg hfeas 1
  -- `(1Q) ⟹ (lt) ⟹ (beta-bound)`, both halves
  have hlt := polar_exp hn2 hx hα hpolar
  have hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α) := beta_le hα0 hB0 hlt
  have hB1lt : QQ (a * x) (a ^ 2) 1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1) :=
    log_le_alpha_mul hα0 hB1lt.le hlt
  -- `α ≤ 17`
  have h17 : α ≤ 17 := alpha_le_seventeen hn ha ha1 hx hα hbeta hlogb horigin
  -- `(origin-exact) ⟹ (1le) ⟹ stat`
  have h1le := one_le_of_origin hn ha ha1 hx hα hα0 hB1lt horigin
  have hstat : 1 ≤ R n α := stat_of_one_le hn hx hα hα0 hbeta h1le
  -- but `stat` is false
  exact absurd hstat
    (not_le.2 (hnum hα0.le h17 (feasible_of_beta hn2 hx hα hα0 hbeta)))

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Interior.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# TaoSendov's conjecture for a real interior zero

This file assembles everything: if `p` has degree `n ≥ 2`, all zeroes in the closed unit disk,
and a zero at a real `a` with `0 < a < 1`, then `p'` has a zero within distance `1` of `a`.

The proof is by contradiction.  Suppose not; then every critical point `w` satisfies
`‖w - a‖ ≥ 1`, so `TaoSendov.exists_crit_multiset` writes `p'` over points `qⱼ` of the closed unit
disk, and `TaoSendov.exists_root_multiset` writes `p` over the other zeroes `zⱼ`.  Setting
`x + iy = (∑ⱼ qⱼ)/(n-1)`, the two channels are:

* **polar**: the polar identity and `p'(a)` two ways feed the branch point `(⋆)`.

From `(⋆)` the argument branches on the degree.

* For `n ≥ 5`, AM–GM relaxes `(⋆)` to the raw polar inequality `(1Q)`, the centroid identity and
  the two origin identities give `(origin-exact)`, and `TaoSendov.polar_origin_incompatible` says
  the two cannot hold together.
* For `n ≤ 5`, `TaoSendov.low_degree_contradiction` shows `(⋆)` is already contradictory on its own,
  with no recourse to the origin channel.  The two branches overlap at degree five.

The zero `a = 0` is excluded above (the polar identity divides by `a`) but needs none of this
machinery: `p'(a)` two ways already says `(∏ⱼ qⱼ)(∏ⱼ (a - zⱼ)) = n`, and at `a = 0` both factors
have norm at most one.

## Main statements

* `TaoSendov.sendov_interior`: the conjecture for a real zero `0 < a < 1`, every degree `n ≥ 2`;
* `TaoSendov.sendov_center`: the conjecture at `a = 0`;
* `TaoSendov.sendov_interior_real`: the two combined, `0 ≤ a < 1`.
-/

namespace TaoSendov

open Polynomial
open Complex (I)

/-- **TaoSendov's conjecture for a real interior zero.**  If every zero of `p` lies in the
closed unit disk and `p(a) = 0` for a real `a` with `0 < a < 1`, then some zero of `p'` lies
within distance `1` of `a`. -/
theorem sendov_interior {n : ℕ} (hnum : 5 ≤ n → NumClaim n) (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (a : ℂ)‖ := by
    intro w hw
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  -- the two factorizations
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hpa
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (a : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- basic numerology
  have hne : ((n : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (n : ℂ) = 1 := by linear_combination h
    have h2 : n = 1 := by exact_mod_cast h1
    omega
  have hqne : q ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hqcard
    omega
  have haC0 : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha0
  have haC2 : ((a : ℝ) : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (a : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this] at h
    have h1 : a ^ 2 = 1 := by exact_mod_cast h
    nlinarith [h1, ha0, ha1]
  have hstar := one_le_integral_prod_norm hn (a := a)
    (by rw [abs_of_nonneg (le_of_lt ha0)]; linarith) hz1
    (polar_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q) (p := p)
      hc0 haC0 haC2 hzcard hqcard hq0 hpa hpz hpq')
    (prod_sub_mul_prod (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n) (z := z) (q := q)
      (p := p) hc0 hq0 hpz hpq')
  -- the branch: low degree needs nothing further
  rcases (by omega : n < 5 ∨ 5 ≤ n) with hn5 | hn5
  · exact low_degree_contradiction hn (by omega) ha0 ha1 hqcard hq1 hstar
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  -- `x + iy` is the centroid of the `qⱼ`
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I) := by
    refine ⟨(q.sum / ((n : ℂ) - 1)).re, (q.sum / ((n : ℂ) - 1)).im, ?_⟩
    rw [Complex.re_add_im, mul_div_cancel₀ _ hne]
  obtain ⟨hxre, hx2⟩ := xy_bounds hn hqcard hq1 hxy
  have hpolar := one_le_integral_Ppolar hn (a := a) (x := x) hqcard hq1 hxre hstar
  -- the origin channel
  have hcent := centroid_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hn hc0 hzcard hqcard hpz hpq'
  have hfirst := first_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 haC0 hzcard hq0 hpa hpz hpq'
  have hsecond := second_origin_identity (c := p.leadingCoeff) (a := ((a : ℝ) : ℂ)) (n := n)
    (z := z) (q := q) (p := p) hc0 hzcard hq0 hpz hpq'
  have horigin := origin_exact (n := n) (α := M n * (1 - a ^ 2) / 2) hn5 ha0 ha1 hqcard hqne
    hz1 hq1 hxy hcent hfirst hsecond rfl
  -- the two are incompatible
  exact polar_origin_incompatible (hnum hn5) hn5 ha0 ha1 (by nlinarith [hx2, sq_nonneg y]) rfl hpolar
    horigin

/-- **The conjecture at `a = 0`.**  `p'(a)` two ways gives `(∏ⱼ qⱼ)(∏ⱼ (a - zⱼ)) = n`.  At
`a = 0` the second factor is `∏ⱼ zⱼ` up to sign, so both factors have norm at most one and
`n ≤ 1` — impossible for `n ≥ 2`.  No polar or origin estimate is involved. -/
theorem sendov_center {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp0 : p.eval 0 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ‖ < 1 := by
  by_contra hcon
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - (0 : ℂ)‖ := by
    intro w hw
    rw [sub_zero]
    by_contra hlt
    exact hcon ⟨w, hw, not_le.1 hlt⟩
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp0
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (0 : ℂ) - v⁻¹)).map (fun w => X - C w)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- `p'(0)` two ways
  have hkey := prod_sub_mul_prod (c := p.leadingCoeff) (a := (0 : ℂ)) (n := n) (z := z) (q := q)
    (p := p) hc0 hq0 hpz hpq'
  have hnorm := congrArg norm hkey
  rw [norm_mul] at hnorm
  have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
  have h2 : ‖(z.map (fun w => (0 : ℂ) - w)).prod‖ ≤ 1 := by
    refine norm_prod_le_one _ ?_
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hu
    simpa using hz1 w hw
  have h3 : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [h3] at hnorm
  have h4 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnorm, h1, h2, norm_nonneg q.prod, norm_nonneg (z.map (fun w => (0 : ℂ) - w)).prod]

/-- **The conjecture for a real zero in `[0,1)`**, every degree `n ≥ 2`. -/
theorem sendov_interior_real {n : ℕ} (hnum : 5 ≤ n → NumClaim n) (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hpa : p.eval (a : ℂ) = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - (a : ℂ)‖ < 1 := by
  rcases eq_or_lt_of_le ha0 with hz | hz
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn hdeg hroots (by rw [← hz] at hpa; simpa using hpa)
    exact ⟨ζ, hζ, by rw [← hz]; simpa using hlt⟩
  · exact sendov_interior hnum hn hdeg hroots hz ha1 hpa

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Boundary.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Rubinstein's boundary theorem, at the zero `a = 1`

If `p` has degree `n ≥ 2`, all zeroes in the closed unit disk, and `p(1) = 0`, then `p'` has a
zero strictly inside `D(1,1)` **unless** `p = c(Xⁿ - 1)`.

The polar identity is useless here: at `a = 1` the reflected point `1/a` coincides with `a`,
`1 - a² = 0`, and the identity degenerates.  One elementary identity replaces it, obtained from
`p''(1)/p'(1)`.  Writing `p = c(X-1)Q` and `p' = ncR`, evaluation at `1` gives

  `Q(1) = n R(1)`  and  `2 Q'(1) = n R'(1)`

— the factor `2` coming from `p''(1) = 2Q'(1)` — whence the **boundary reciprocal identity**

  `∑ⱼ qⱼ = 2 ∑ⱼ 1/(1 - zⱼ)`,   `qⱼ = 1/(1 - wⱼ)`.

Both sides are then sandwiched.  On the left `Re qⱼ ≤ ‖qⱼ‖ ≤ 1`, so the real part is at most
`n-1`; on the right `Re 1/(1-z) ≥ 1/2` for `‖z‖ ≤ 1`, because
`Re 1/(1-z) - 1/2 = (1-‖z‖²)/(2‖1-z‖²)`, so the real part is at least `n-1`.  Equality forces
`Re qⱼ = 1` for every `j`, hence `qⱼ = 1`, hence every critical point is `0`, hence
`p' = n c Xⁿ⁻¹` and `p = c(Xⁿ - 1)`.

The repeated-root case is handled before any division: if `1` is a multiple zero then `p'(1) = 0`
and `ζ = 1` is a strict witness, so under the contradiction hypothesis `p'(1) ≠ 0` and every
`zⱼ ≠ 1`.

No polar integral, origin identity, defect lemma, numerical certificate or Gauss–Lucas theorem
is used.  Only the two factorizations of `TaoSendov.Counterexample.Factor` are shared with the
interior argument.

## Main statements

* `TaoSendov.rubinstein_one`: the strict-or-extremal alternative;
* `TaoSendov.sendov_boundary_one`: the closed-disk form, `‖ζ - 1‖ ≤ 1`;
* `TaoSendov.boundary_reciprocal`: `(BR)`, in division-free form.
-/

namespace TaoSendov

open Polynomial

/-! ### Evaluating `∏ⱼ (X - zⱼ)` and its derivative at a point

The versions in `TaoSendov.Counterexample.Identities` are specialized to the origin; the boundary
argument needs them at `1`. -/

lemma eval_prod_at (u : ℂ) (s : Multiset ℂ) :
    ((s.map (fun w => X - C w)).prod).eval u = (s.map (fun w => u - w)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)

lemma eval_deriv_prod_at (u : ℂ) : ∀ (s : Multiset ℂ),
    (derivative (s.map (fun w => X - C w)).prod).eval u
      = sumEraseProd (s.map (fun w => u - w)) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C]
    rw [ih, eval_prod_at, sumEraseProd_cons]

/-! ### Scalar facts -/

/-- **The disk inequality.**  `Re 1/(1-z) ≥ 1/2` for `‖z‖ ≤ 1`, `z ≠ 1`; after clearing the
positive denominator this is exactly `1 - ‖z‖² ≥ 0`. -/
lemma half_le_re_inv_one_sub {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 : ℝ) / 2 ≤ (((1 : ℂ) - z)⁻¹).re := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hd : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.2 hne
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [hz, norm_nonneg z, h]
  rw [Complex.inv_re, le_div_iff₀ hd, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [hsq]

/-- A point of the closed unit disk with real part `1` is `1`. -/
lemma eq_one_of_re_eq_one_of_norm_le_one {v : ℂ} (hre : v.re = 1) (hv : ‖v‖ ≤ 1) : v = 1 := by
  have hsq : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq v
    rw [Complex.normSq_apply] at h
    nlinarith [hv, norm_nonneg v, h]
  have him : v.im = 0 := by nlinarith [hsq, hre, sq_nonneg v.im]
  apply Complex.ext <;> simp [hre, him]

/-- A multiset of nonnegative reals summing to zero is all zeroes. -/
lemma eq_zero_of_sum_eq_zero {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (h : s.sum = 0) :
    ∀ x ∈ s, x = 0 := by
  intro x hx
  have hsplit : s.sum = x + (s.erase x).sum := by
    conv_lhs => rw [← Multiset.cons_erase hx]
    rw [Multiset.sum_cons]
  have hrest : 0 ≤ (s.erase x).sum :=
    Multiset.sum_nonneg fun y hy => hs y (Multiset.mem_of_mem_erase hy)
  rw [hsplit] at h
  have := hs x hx
  linarith

lemma sum_le_card_mul (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, x ≤ c) →
    s.sum ≤ (s.card : ℝ) * c := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

lemma card_mul_le_sum (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, c ≤ x) →
    (s.card : ℝ) * c ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, c ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

lemma sum_map_one_sub_re (s : Multiset ℂ) :
    (s.map (fun v => 1 - v.re)).sum = (s.card : ℝ) - (s.map (fun v => v.re)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

/-! ### The boundary reciprocal identity -/

/-- **`(BR)`, in division-free form.**  From `∏ Zs = n ∏ Qi` and `2 ∑ₑ Zs = n ∑ₑ Qi` — the two
readings of `p'(1)` and `p''(1)` — one gets `∑ⱼ 1/Qiⱼ = 2 ∑ⱼ 1/Zsⱼ`.  Applied with
`Zsⱼ = 1 - zⱼ` and `Qiⱼ = 1/qⱼ` this is `∑ⱼ qⱼ = 2 ∑ⱼ 1/(1-zⱼ)`. -/
theorem boundary_reciprocal {n : ℕ} {Zs Qi : Multiset ℂ} (hn0 : (n : ℂ) ≠ 0)
    (hZ : ∀ u ∈ Zs, u ≠ 0) (hQ : ∀ u ∈ Qi, u ≠ 0)
    (hI : Zs.prod = (n : ℂ) * Qi.prod)
    (hII : 2 * sumEraseProd Zs = (n : ℂ) * sumEraseProd Qi) :
    (Qi.map (fun u => u⁻¹)).sum = 2 * (Zs.map (fun u => u⁻¹)).sum := by
  have hQ0 : Qi.prod ≠ 0 := Multiset.prod_ne_zero fun h => hQ 0 h rfl
  have h1 := prod_mul_sum_inv Zs hZ
  have h2 := prod_mul_sum_inv Qi hQ
  have h : (n : ℂ) * Qi.prod * (2 * (Zs.map (fun u => u⁻¹)).sum)
      = (n : ℂ) * Qi.prod * (Qi.map (fun u => u⁻¹)).sum := by
    linear_combination (-2 * (Zs.map (fun u => u⁻¹)).sum) * hI + 2 * h1 + hII - (n : ℂ) * h2
  exact (mul_left_cancel₀ (mul_ne_zero hn0 hQ0) h).symm

/-! ### The sandwich -/

/-- Both sides of `(BR)` are pinned: the left has real part at most `N`, the right at least `N`,
so every `qⱼ` has real part `1` and hence, lying in the closed unit disk, equals `1`. -/
theorem all_q_eq_one {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by
  have hupper : (qs.map (fun v => v.re)).sum ≤ (N : ℝ) := by
    have h := sum_le_card_mul 1 (qs.map (fun v => v.re)) (by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hr
      exact (Complex.re_le_norm v).trans (hq1 v hv))
    rwa [Multiset.card_map, hqcard, mul_one] at h
  have hlower : (N : ℝ) ≤ (qs.map (fun v => v.re)).sum := by
    have h := card_mul_le_sum (1 / 2) (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
      exact half_le_re_inv_one_sub (hz1 w hw) (hzne w hw))
    rw [Multiset.card_map, hzcard] at h
    have hmapre : (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum
        = (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum.re := by
      rw [← sum_map_re, Multiset.map_map]
      rfl
    have hre : (qs.map (fun v => v.re)).sum
        = 2 * (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum := by
      rw [sum_map_re, hBR, hmapre, Complex.mul_re]
      simp
    rw [hre]
    linarith
  have heq : (qs.map (fun v => 1 - v.re)).sum = 0 := by
    rw [sum_map_one_sub_re, hqcard]
    linarith
  intro v hv
  refine eq_one_of_re_eq_one_of_norm_le_one ?_ (hq1 v hv)
  have hzero := eq_zero_of_sum_eq_zero (s := qs.map (fun v => 1 - v.re)) (by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hr
    have := (Complex.re_le_norm u).trans (hq1 u hu)
    linarith) heq (1 - v.re) (Multiset.mem_map_of_mem _ hv)
  linarith

/-! ### Rubinstein's theorem at `a = 1` -/

/-- **Rubinstein's boundary theorem at `a = 1`**, with its equality case. -/
theorem rubinstein_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1)
      ∨ p = C p.leadingCoeff * (X ^ n - 1) := by
  by_cases hex : ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1
  · exact Or.inl hex
  refine Or.inr ?_
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - 1‖ := by
    intro w hw
    by_contra hlt
    exact hex ⟨w, hw, not_le.1 hlt⟩
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hn0 : (n : ℂ) ≠ 0 := by
    intro h
    have h1 : n = 0 := by exact_mod_cast h
    omega
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp1
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => X - C u)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- the repeated-root case is already excluded
  have hp'1 : (derivative p).eval 1 ≠ 0 := fun h => hex ⟨1, h, by simp⟩
  -- `p'` and `p''` from `p = c (X-1) Q`
  have hd1 : derivative p = C p.leadingCoeff
      * ((z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (z.map (fun w => X - C w)).prod) := by
    conv_lhs => rw [hpz]
    rw [derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul]
  have hd2 : derivative (derivative p) = C p.leadingCoeff
      * (2 * derivative (z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (derivative (z.map (fun w => X - C w)).prod)) := by
    rw [hd1, derivative_C_mul, derivative_add, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul]
    ring
  have hA : (derivative p).eval 1 = p.leadingCoeff * (z.map (fun w => (1 : ℂ) - w)).prod := by
    rw [hd1]
    simp [eval_prod_at]
  have hB : (derivative (derivative p)).eval 1
      = p.leadingCoeff * (2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))) := by
    rw [hd2]
    simp [eval_deriv_prod_at]
  -- `p'` and `p''` from `p' = n c R`
  have hmapq : (q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => (1 : ℂ) - u)
      = q.map (fun v => v⁻¹) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => by simp
  have hC : (derivative p).eval 1
      = (n : ℂ) * p.leadingCoeff * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq', eval_mul, eval_C, eval_prod_at, hmapq]
  have hD : (derivative (derivative p)).eval 1
      = (n : ℂ) * p.leadingCoeff * sumEraseProd (q.map (fun v => v⁻¹)) := by
    rw [hpq', derivative_C_mul, eval_mul, eval_C, eval_deriv_prod_at, hmapq]
  -- the two relations, after cancelling the leading coefficient
  have hI : (z.map (fun w => (1 : ℂ) - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hA.symm.trans hC
    linear_combination h
  have hII : 2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))
      = (n : ℂ) * sumEraseProd (q.map (fun v => v⁻¹)) := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hB.symm.trans hD
    linear_combination h
  -- no `zⱼ` equals `1`
  have hZ0 : (z.map (fun w => (1 : ℂ) - w)).prod ≠ 0 := by
    intro h
    exact hp'1 (by rw [hA, h, mul_zero])
  have hZne : ∀ u ∈ z.map (fun w => (1 : ℂ) - w), u ≠ 0 := by
    intro u hu hu0
    exact hZ0 (Multiset.prod_eq_zero (hu0 ▸ hu))
  have hzne : ∀ w ∈ z, w ≠ 1 := by
    intro w hw hw1
    exact hZne ((1 : ℂ) - w) (Multiset.mem_map_of_mem _ hw) (by rw [hw1]; ring)
  have hQne : ∀ u ∈ q.map (fun v => v⁻¹), u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hu
    exact inv_ne_zero (hq0 v hv)
  -- `(BR)`
  have hBRraw := boundary_reciprocal (n := n) hn0 hZne hQne hI hII
  have hQiinv : ((q.map (fun v => v⁻¹)).map (fun u => u⁻¹)).sum = q.sum := by
    rw [Multiset.map_map]
    simp
  have hZsinv : (z.map (fun w => (1 : ℂ) - w)).map (fun u => u⁻¹)
      = z.map (fun w => ((1 : ℂ) - w)⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [hQiinv, hZsinv] at hBRraw
  -- every `qⱼ` is `1`, so every critical point is `0`
  have hqone := all_q_eq_one hqcard hzcard hq1 hz1 hzne hBRraw
  have hderivX : derivative p = C ((n : ℂ) * p.leadingCoeff) * X ^ (n - 1) := by
    rw [hpq]
    congr 1
    have hmap : q.map (fun v => X - C ((1 : ℂ) - v⁻¹))
        = Multiset.replicate q.card (X : ℂ[X]) := by
      rw [← Multiset.map_const']
      exact Multiset.map_congr rfl fun v hv => by rw [hqone v hv]; simp
    rw [hmap, Multiset.prod_replicate, hqcard]
  -- hence `p - c Xⁿ` is constant
  have hdz : derivative (p - C p.leadingCoeff * X ^ n) = 0 := by
    rw [derivative_sub, hderivX, derivative_C_mul, derivative_X_pow, map_mul]
    ring
  have hdeg0 : (p - C p.leadingCoeff * X ^ n).natDegree = 0 := derivative_eq_zero.1 hdz
  obtain ⟨d, hd⟩ := natDegree_eq_zero.1 hdeg0
  have hdval : d = -p.leadingCoeff := by
    have h := congrArg (Polynomial.eval (1 : ℂ)) hd
    simpa [hp1] using h
  have hCd : (C d : ℂ[X]) = -C p.leadingCoeff := by rw [hdval, map_neg]
  linear_combination -hd + hCd

/-- The closed-disk form.  In the extremal case `p = c(Xⁿ - 1)` the only critical point is `0`,
at distance exactly `1` from the zero `1`. -/
theorem sendov_boundary_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 := by
  rcases rubinstein_one hn hdeg hroots hp1 with ⟨ζ, hζ, hlt⟩ | hext
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  refine ⟨0, ?_, by norm_num⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_one]
  simp [zero_pow (by omega : n - 1 ≠ 0)]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/Conjecture.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# TaoSendov's conjecture and the Phelps–Rodriguez conjecture

> Let `n ≥ 2` and let `p` be a degree `n` polynomial with all zeroes in the closed unit disk.
> Then for every zero `a` of `p` there is a critical point `ζ` of `p` with `‖ζ - a‖ ≤ 1`
> (TaoSendov), and in fact with `‖ζ - a‖ < 1` unless `‖a‖ = 1` and `p` is a scalar multiple of
> `zⁿ - aⁿ` (Phelps–Rodriguez).

Everything mathematical is already done: this file only removes the normalization `a ∈ [0,1)`
by rotating the variable.  Writing `a = ω r` with `‖ω‖ = 1` and `r = ‖a‖`, the polynomial
`p(ωz)` has the same degree, still has all its zeroes in the closed unit disk, and vanishes at
the *real* point `r`.  Its critical points are the `ω⁻¹ζ`, and `‖ω⁻¹ζ - r‖ = ‖ζ - a‖`, so the
conclusion transports back unchanged.

Three cases, by the position of `a`:

* `a = 0`: `TaoSendov.sendov_center`;
* `0 < ‖a‖ < 1`: `TaoSendov.sendov_interior_real` after rotating;
* `‖a‖ = 1`: `TaoSendov.rubinstein_one` after rotating, whose extremal polynomial `c(zⁿ - 1)`
  rotates back to `c ω⁻ⁿ (zⁿ - aⁿ)`.

## Main statements

* `TaoSendov.phelps_rodriguez`: the Phelps–Rodriguez conjecture;
* `TaoSendov.sendov`: TaoSendov's conjecture.
-/

namespace TaoSendov

open Polynomial

/-! ### Rotating the variable -/

/-- `p(ωz)`. -/
noncomputable def rotate (ω : ℂ) (p : ℂ[X]) : ℂ[X] := p.comp (C ω * X)

@[simp] lemma eval_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (rotate ω p).eval x = p.eval (ω * x) := by
  simp [rotate, eval_comp]

lemma natDegree_rotate {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotate ω p).natDegree = p.natDegree := by
  rw [rotate, natDegree_comp, natDegree_C_mul hω, natDegree_X, mul_one]

lemma derivative_rotate (ω : ℂ) (p : ℂ[X]) :
    derivative (rotate ω p) = C ω * rotate ω (derivative p) := by
  simp only [rotate, derivative_comp, derivative_mul, derivative_C, derivative_X, zero_mul,
    mul_one, zero_add]

lemma eval_derivative_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (derivative (rotate ω p)).eval x = ω * (derivative p).eval (ω * x) := by
  rw [derivative_rotate, eval_mul, eval_C, eval_rotate]

/-- Rotating is undone by rotating back. -/
lemma rotate_rotate_inv {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) : rotate ω⁻¹ (rotate ω p) = p := by
  have h : (C ω * X : ℂ[X]).comp (C ω⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hω, C_1, one_mul]
  rw [rotate, rotate, comp_assoc, h, comp_X]

lemma roots_rotate {ω : ℂ} (hω : ‖ω‖ = 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) : ∀ w ∈ (rotate ω p).roots, ‖w‖ ≤ 1 := by
  intro w hw
  have hev : p.eval (ω * w) = 0 := by
    have := (mem_roots'.1 hw).2
    rwa [IsRoot, eval_rotate] at this
  have hmem : ω * w ∈ p.roots := mem_roots'.2 ⟨hp, hev⟩
  have := hroots _ hmem
  rwa [norm_mul, hω, one_mul] at this

/-! ### The Phelps–Rodriguez conjecture -/

/-- **The Phelps–Rodriguez conjecture.**  Every zero `a` of a degree `n ≥ 2` polynomial with all
zeroes in the closed unit disk has a critical point strictly within distance `1`, unless `a` is
on the unit circle and `p` is a scalar multiple of `zⁿ - aⁿ`. -/
theorem phelps_rodriguez {n : ℕ} (hnum : 5 ≤ n → NumClaim n) (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n))) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn hdeg hroots hpa
    exact Or.inl ⟨ζ, hζ, by simpa using hlt⟩
  -- the rotation `a = ω r`
  have hr0 : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hr1 : ‖a‖ ≤ 1 := hroots a (mem_roots'.2 ⟨hp0, hpa⟩)
  have hrC : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr0
  obtain ⟨ω, hωdef⟩ : ∃ w : ℂ, w = a / ((‖a‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hωne : ω ≠ 0 := by
    rw [hωdef]
    exact div_ne_zero ha0 hrC
  have hωnorm : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0),
      div_self (ne_of_gt hr0)]
  have hωr : ω * ((‖a‖ : ℝ) : ℂ) = a := by
    rw [hωdef, div_mul_cancel₀ _ hrC]
  -- the rotated polynomial
  have hdeg' : (rotate ω p).natDegree = n := by rw [natDegree_rotate hωne, hdeg]
  have hroots' := roots_rotate hωnorm hp0 hroots
  have hpr : (rotate ω p).eval ((‖a‖ : ℝ) : ℂ) = 0 := by rw [eval_rotate, hωr, hpa]
  -- transporting a strict witness back
  have htransport : ∀ ζ : ℂ, (derivative (rotate ω p)).eval ζ = 0 →
      ‖ζ - ((‖a‖ : ℝ) : ℂ)‖ < 1 → ∃ ξ : ℂ, (derivative p).eval ξ = 0 ∧ ‖ξ - a‖ < 1 := by
    intro ζ hζ hlt
    refine ⟨ω * ζ, ?_, ?_⟩
    · rw [eval_derivative_rotate] at hζ
      exact (mul_eq_zero.1 hζ).resolve_left hωne
    · have : ω * ζ - a = ω * (ζ - ((‖a‖ : ℝ) : ℂ)) := by rw [mul_sub, hωr]
      rw [this, norm_mul, hωnorm, one_mul]
      exact hlt
  rcases lt_or_eq_of_le hr1 with hlt1 | heq1
  · -- the interior case
    obtain ⟨ζ, hζ, hd⟩ :=
      sendov_interior_real hnum hn hdeg' hroots' (le_of_lt hr0) hlt1 hpr
    exact Or.inl (htransport ζ hζ hd)
  · -- the boundary case: `a = ω`
    have hone : ((‖a‖ : ℝ) : ℂ) = 1 := by rw [heq1]; norm_num
    have haω : a = ω := by rw [← hωr, hone, mul_one]
    have hpr1 : (rotate ω p).eval 1 = 0 := by rwa [hone] at hpr
    rcases rubinstein_one hn hdeg' hroots' hpr1 with ⟨ζ, hζ, hd⟩ | hext
    · exact Or.inl (htransport ζ hζ (by rw [hone]; exact hd))
    -- the extremal case, rotated back
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (rotate ω p).leadingCoeff := ⟨_, rfl⟩
    have hcne : c ≠ 0 := by
      rw [hcdef]
      refine leadingCoeff_ne_zero.2 ?_
      intro h
      rw [h, natDegree_zero] at hdeg'
      omega
    refine Or.inr ⟨heq1, c * ω⁻¹ ^ n,
      mul_ne_zero hcne (pow_ne_zero _ (inv_ne_zero hωne)), ?_⟩
    have hext' : rotate ω p = C c * (X ^ n - 1) := by rw [hcdef]; exact hext
    have hcomp : rotate ω⁻¹ (C c * (X ^ n - 1)) = C c * (C (ω⁻¹ ^ n) * X ^ n - 1) := by
      simp only [rotate, mul_comp, sub_comp, pow_comp, C_comp, X_comp, one_comp, mul_pow,
        ← C_pow]
    have h1 : (C (ω⁻¹ ^ n) * C (ω ^ n) : ℂ[X]) = 1 := by
      rw [← C_mul, ← mul_pow, inv_mul_cancel₀ hωne, one_pow, C_1]
    have hgoal : rotate ω⁻¹ (rotate ω p) = C (c * ω⁻¹ ^ n) * (X ^ n - C (a ^ n)) := by
      rw [hext', hcomp, haω, C_mul]
      linear_combination (C c) * h1
    exact (rotate_rotate_inv hωne p).symm.trans hgoal

/-! ### TaoSendov's conjecture -/

/-- **TaoSendov's conjecture.**  Every zero of a degree `n ≥ 2` polynomial with all zeroes in the
closed unit disk has a critical point within distance `1`. -/
theorem sendov {n : ℕ} (hnum : 5 ≤ n → NumClaim n) (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by
  rcases phelps_rodriguez hnum hn hdeg hroots hpa with ⟨ζ, hζ, hlt⟩ | ⟨hnorm, c, hc, hext⟩
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  -- the extremal polynomial `c(zⁿ - aⁿ)` has its only critical point at the origin, at
  -- distance exactly `‖a‖ = 1`
  refine ⟨0, ?_, by simpa using le_of_eq hnorm⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_C]
  simp [zero_pow (by omega : n - 1 ≠ 0)]

end TaoSendov
-- ===== from teorth/sendov TaoSendov/LargeDegree/Tail.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The tail bound

The large-degree argument replaces the integral in `TaoSendov.R` by an elementary expression:

  `∫₀¹ t³ Q^r dt ≤ 6 / (c⁴ (r+1)(r+2)(r+3)(r+4)) + Bʳ / 4`.

This is the only part of the large-degree argument that touches integration; everything after
it is elementary inequalities in `α` and `n`.

The work is done by `TaoSendov.integral_le_tail_cube` in `TaoSendov.Common.Chord`, which proves the
same split for the general quadratic `QQ c A` and an arbitrary weight `t^k` — the `α ≤ 17`
argument needs the `k = 1` instance of it.  All that is left here is to read that bound
through `Q n α t = QQ (c n α) (A n α) t` and `Q n α 1 = α/(3+α)`.

## Main statements

* `TaoSendov.c_le_one`: `c ≤ 1`, so the chord's zero `1/c` is at least `1`;
* `TaoSendov.integral_le_tail`: the bound above.
-/

namespace TaoSendov

open MeasureTheory

variable {n : ℕ} {α t : ℝ}

/-- `c ≤ 1`, so the chord's zero `1/c` is at least `1`. -/
lemma c_le_one (hn : 2 ≤ n) (hα : 0 ≤ α) : c n α ≤ 1 := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : 0 ≤ α / M n := by positivity
  have h2 : 0 ≤ α / (2 * (3 + α)) := by positivity
  linarith

/-- **The tail bound**, read off from `TaoSendov.integral_le_tail_cube`. -/
theorem integral_le_tail (hn : 2 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hc : 0 < c n α) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4)))
        + (α / (3 + α)) ^ r / 4 := by
  have h := integral_le_tail_cube hfeas hc (c_le_one hn hα) hr
  rw [← Q_one hn hα]
  simpa only [Q_eq_QQ] using h

/-! ### The elementary upper bound `U`

Everything after this point in the large-degree argument is an inequality in `α` and `n`
alone; no integral survives. -/

/-- The elementary bound replacing `TaoSendov.R`: `(11)` of the informal write-up, but with the
sharper Beta constant `6/((r+1)(r+2)(r+3)(r+4))` in place of `6/r⁴`. -/
noncomputable def U (n : ℕ) (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
    + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α))
      * (6 / (c n α ^ 4 *
            ((((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
              * (((n : ℝ) - 4) / 2 + 4)))
        + (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) / 4)

/-- On the large-degree range `c` is bounded below, hence positive.  For `n ≥ 101` and
`α ≤ 17` this gives `c ≥ 81/200`, which is `(3)` of the write-up. -/
lemma c_ge_of_large (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : 81 / 200 ≤ c n α := by
  have hM : (100 : ℝ) ≤ M n := by
    have : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [M]; linarith
  have hM0 : (0 : ℝ) < M n := by linarith
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : α / M n ≤ 17 / 100 := by
    rw [div_le_iff₀ hM0]
    nlinarith
  have h2 : α / (2 * (3 + α)) ≤ 17 / 40 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (3 + α))]
    nlinarith
  linarith

/-- **`R` is bounded by the elementary expression `U`.**  This is the bridge out of
integration: from here the large-degree argument is elementary. -/
theorem R_le_U (hn : 5 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α) (hc : 0 < c n α) :
    R n α ≤ U n α := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < ((n : ℝ) - 4) / 2 := by linarith
  exact R_le_of_integral_le (by omega) hα (integral_le_tail (by omega) hα hfeas hc hr)

end TaoSendov
-- ===== from teorth/sendov TaoSendov/LargeDegree/Monotone.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# Monotonicity of the elementary bound in the degree

`TaoSendov.U` bounds `TaoSendov.R` for every `n ≥ 5`.  Here it is reduced to a single inequality
in `α` alone, by showing that `U n α` is essentially decreasing in `n` on `n ≥ 101`.

Two features of the bound make this cheaper than it looks.

First, the sharp Beta constant collapses.  The exponent is `r = (n-4)/2`, so

  `(r+1)(r+2)(r+3)(r+4) = (n-2) n (n+2) (n+4) / 16`,

and the `n (n-2)` in it cancels the `n (n-2)` in the prefactor of `TaoSendov.R` exactly.  The
first tail term is therefore the *rational function*

  `T1 n α = 24 (n-1-2α)² / ((3+α) c⁴ (n-1)(n+2)(n+4))`,

with no factorial-like growth left to control.  (Had the cruder constant `6/r⁴` of the
informal write-up been used, no such cancellation would occur and the corresponding step
would need the degree-8 positivity certificate recorded there.)

Second, the surviving real power is a square: writing `b = √B`, the second tail term is
`T2 n α = A² n (n-1)(n-2)/(16(3+α)) · b ^ (n-4)` with a *natural* exponent, so the geometric
decay can be run as an ordinary induction on `n` rather than as an estimate on `rpow`.

## The two certificates

`T1` is not monotone in `n` by itself — at `α = 17` the factor
`(n-1-2α)²/((n-1)(n+2)(n+4))` increases up to `n ≈ 108` — so it is bounded by its value at
`n = 101` only after a `1%` allowance, which the `c⁴` in the denominator more than pays for.
That allowance is `TaoSendov.tail1_poly`, a Bernstein certificate on `0 ≤ α ≤ 17`.  Its top
coefficient is the only one in this development that is *not* a positive combination of
powers of the degree offset; it is handled by completing the square, its quadratic part
having negative discriminant.

`TaoSendov.tail2_poly` is the geometric step, and is an ordinary all-positive certificate.

## Main statements

* `TaoSendov.U_eq`: `U` in closed form, `T1 + T2` plus four elementary terms;
* `TaoSendov.T1_le`, `TaoSendov.T2_le`: the two tail bounds at `n = 101`;
* `TaoSendov.U_le_Ut`: `U n α ≤ Ut α` for `n ≥ 101`, where `Ut` involves no `n` and no `rpow`.
-/

namespace TaoSendov

variable {n : ℕ} {α : ℝ}

/-- The first tail term of `TaoSendov.U`, in closed form. -/
noncomputable def T1 (n : ℕ) (α : ℝ) : ℝ :=
  24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
    ((3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4))

/-- The second tail term of `TaoSendov.U`, with the real power of `B` replaced by a natural
power of `√B`. -/
noncomputable def T2 (n : ℕ) (α : ℝ) : ℝ :=
  A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (16 * (3 + α)) * Real.sqrt (α / (3 + α)) ^ (n - 4)

/-! ### The two polynomial certificates -/

/-- The allowance for the first tail term: on `0 ≤ α ≤ 17` and `N = 100 + j ≥ 100`,

  `(N-2α)² / (N (N+3)(N+5)) ≤ (101/100) (100-2α)² / (100 · 103 · 105)`.

A Bernstein certificate in `α` on `[0,17]`, whose coefficients are polynomials in `j`.  The
top one, `439956 j³ + 27356448 j² - 366591060 j + 4711014000`, has a negative linear
coefficient; it is nonnegative because its quadratic part has negative discriminant. -/
lemma tail1_poly {j α : ℝ} (hj : 0 ≤ j) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    108150000 * (100 + j - 2 * α) ^ 2
      ≤ 101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j)) := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hj2 : (0 : ℝ) ≤ j ^ 2 := sq_nonneg j
  have hj3 : (0 : ℝ) ≤ j ^ 3 := pow_nonneg hj 3
  have h0 : (0 : ℝ) ≤ 1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000 := by
    linarith
  have h1 : (0 : ℝ) ≤ 1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000 := by
    linarith
  have h2 : (0 : ℝ) ≤ 439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000 := by
    nlinarith [sq_nonneg (4559408 * j - 30549255), hj3]
  have hid : (17 : ℝ) ^ 2 *
      (101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j))
        - 108150000 * (100 + j - 2 * α) ^ 2)
      = (1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000) * (17 - α) ^ 2
        + (1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000)
            * (α * (17 - α))
        + (439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]

/-- The geometric step for the second tail term: on `0 ≤ α ≤ 17` and `n = 101 + k ≥ 101`,

  `12 A_{n+1}² (n+1) n (n-1) ≤ 13 A_n² n (n-1)(n-2)`,

after clearing the denominators `n²` and `(n-1)²` of `A_{n+1}` and `A_n`.  Together with
`√B ≤ 12/13` this makes the step ratio less than one.  A Bernstein certificate in `α` on
`[0,17]` with all coefficients positive combinations of powers of `k`. -/
lemma tail2_poly {k α : ℝ} (hk : 0 ≤ k) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2
      ≤ 13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2 := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hk2 : (0 : ℝ) ≤ k ^ 2 := sq_nonneg k
  have hk3 : (0 : ℝ) ≤ k ^ 3 := pow_nonneg hk 3
  have hk4 : (0 : ℝ) ≤ k ^ 4 := pow_nonneg hk 4
  have hk5 : (0 : ℝ) ≤ k ^ 5 := pow_nonneg hk 5
  have h0 : (0 : ℝ) ≤ k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2
      + 357802600 * k + 6426630000 := by linarith
  have h1 : (0 : ℝ) ≤ 2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2
      + 491029284 * k + 7642508400 := by linarith
  have h2 : (0 : ℝ) ≤ k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2
      + 165348456 * k + 2243200572 := by linarith
  have hid : (17 : ℝ) ^ 2 *
      (13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2
        - 12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2)
      = (k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2 + 357802600 * k + 6426630000)
          * (17 - α) ^ 2
        + (2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2 + 491029284 * k
            + 7642508400) * (α * (17 - α))
        + (k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2 + 165348456 * k
            + 2243200572) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]

/-! ### The closed form of `U` -/

/-- `c` increases with `n`: raising the degree moves `c` towards `1 - B/2`. -/
lemma c_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : c m α ≤ c n α := by
  have hMm : 0 < M m := M_pos hm
  have hMle : M m ≤ M n := by
    simp only [M]
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have : α / M n ≤ α / M m := div_le_div_of_nonneg_left hα hMm hMle
  simp only [c]
  linarith

/-- The real power of `B` in `TaoSendov.U` is a natural power of `√B`. -/
lemma rpow_B_eq (hn : 4 ≤ n) (hα : 0 ≤ α) :
    (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) = Real.sqrt (α / (3 + α)) ^ (n - 4) := by
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hcast : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    push_cast [Nat.cast_sub hn]
    ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((α / (3 + α)) ^ ((1 : ℝ) / 2)) (n - 4),
    ← Real.rpow_mul hB, hcast]
  congr 1
  ring

/-- The sharp Beta constant, factored.  This is the cancellation that makes `T1` rational:
`(r+1)(r+2)(r+3)(r+4) = (n-2) n (n+2)(n+4)/16` at `r = (n-4)/2`. -/
lemma beta_prod (n : ℕ) :
    (((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
        * (((n : ℝ) - 4) / 2 + 4)
      = ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) / 16 := by
  ring

/-- **`U` in closed form.**  The `n (n-2)` of the prefactor cancels against the same factor
in the sharp Beta constant, leaving a rational function plus a natural power of `√B`. -/
lemma U_eq (hn : 5 ≤ n) (hα : 0 ≤ α) (hc : c n α ≠ 0) :
    U n α = 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + T1 n α + T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (n : ℝ) ≠ 0 := by linarith
  have hp2 : (n : ℝ) + 2 ≠ 0 := by linarith
  have hp4 : (n : ℝ) + 4 ≠ 0 := by linarith
  simp only [U, beta_prod, T1, T2, M, A, rpow_B_eq (show 4 ≤ n by omega) hα]
  field_simp
  ring

/-! ### The first tail term -/

/-- `T1` is bounded by its value at `n = 101`, up to `1%`. -/
lemma T1_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    T1 n α ≤ 101 / 100 * T1 101 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc1 : (0 : ℝ) < c 101 α := by
    have := c_ge_of_large (n := 101) le_rfl hα hα'
    linarith
  have hcn : c 101 α ≤ c n α := c_mono (by omega) hn hα
  have hcnp : (0 : ℝ) < c n α := lt_of_lt_of_le hc1 hcn
  have hc4 : c 101 α ^ 4 ≤ c n α ^ 4 := by
    exact pow_le_pow_left₀ hc1.le hcn 4
  have hN : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hN4 : (0 : ℝ) < (n : ℝ) + 4 := by linarith
  have hprod : (0 : ℝ) ≤ ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_nonneg (mul_nonneg hN.le hN2.le) hN4.le
  have hD1 : (0 : ℝ) < (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_pos (mul_pos (mul_pos (mul_pos h3 (pow_pos hc1 4)) hN) hN2) hN4
  have hDle : (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)
      ≤ (3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) := by
    have hd : (0 : ℝ) ≤ (3 + α) * (c n α ^ 4 - c 101 α ^ 4) *
        (((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) :=
      mul_nonneg (mul_nonneg h3.le (by linarith)) hprod
    nlinarith [hd]
  -- step A: enlarge the denominator's `c` from `c n` down to `c 101`
  have stepA : T1 n α
      ≤ 24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
          ((3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
    rw [T1]
    exact div_le_div_of_nonneg_left (by positivity) hD1 hDle
  refine stepA.trans ?_
  -- step B: the certificate, with the same `c 101` on both sides
  have hT101 : T1 101 α = 24 * (100 - 2 * α) ^ 2 / ((3 + α) * c 101 α ^ 4 * 1081500) := by
    simp only [T1]
    norm_num
    ring_nf
  have hD2 : (0 : ℝ) < 100 * ((3 + α) * c 101 α ^ 4 * 1081500) := by
    have h4 := pow_pos hc1 4
    positivity
  have hRHS : 101 / 100 * T1 101 α
      = 101 * (24 * (100 - 2 * α) ^ 2) / (100 * ((3 + α) * c 101 α ^ 4 * 1081500)) := by
    rw [hT101]
    field_simp
  rw [hRHS, div_le_div_iff₀ hD1 hD2]
  have hj : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail1_poly (j := (n : ℝ) - 101) hj hα hα'
  have hscale : (0 : ℝ) ≤ 24 * (3 + α) * c 101 α ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcert hscale]

/-! ### The second tail term -/

/-- `√B ≤ 12/13` on `0 ≤ α ≤ 17`, since `B ≤ 17/20 ≤ (12/13)²`.  A rational bound is enough
here, and avoids carrying a square root into the step ratio. -/
lemma sqrtB_le (hα : 0 ≤ α) (hα' : α ≤ 17) : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hB : α / (3 + α) ≤ 144 / 169 := by
    rw [div_le_div_iff₀ h3 (by norm_num)]
    linarith
  calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt (144 / 169) := Real.sqrt_le_sqrt hB
    _ = 12 / 13 := by
        rw [show (144 : ℝ) / 169 = (12 / 13) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12 / 13)]

/-- One step of the geometric decay: `T2` decreases with `n` on `n ≥ 101`. -/
lemma T2_step (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 (n + 1) α ≤ T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := sqrtB_le hα hα'
  have hA1 : A (n + 1) α = ((n : ℝ) - 2 * α) / (n : ℝ) := by
    simp only [A, M]
    push_cast
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) from by ring]
    field_simp
  have hA2 : A n α = ((n : ℝ) - 1 - 2 * α) / ((n : ℝ) - 1) := by
    simp only [A, M]
    field_simp
  have hk : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail2_poly (k := (n : ℝ) - 101) hk hα hα'
  have hCn1 : (0 : ℝ) ≤ A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1)
      * (((n + 1 : ℕ) : ℝ) - 2) / (16 * (3 + α)) := by
    have hM : (0 : ℝ) ≤ M (n + 1) := by simp only [M]; push_cast; linarith
    have h2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
    have h1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    positivity
  -- the coefficient inequality
  have hstep : A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
        / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
      ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hb1 hCn1) ?_
    rw [← sub_nonneg]
    have key : A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          - A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
              / (16 * (3 + α)) * (12 / 13)
        = (13 * ((n : ℝ) - 1 - 2 * α) ^ 2 * ((n : ℝ) - 2) * (n : ℝ) ^ 2
            - 12 * ((n : ℝ) - 2 * α) ^ 2 * ((n : ℝ) + 1) * ((n : ℝ) - 1) ^ 2)
          / (208 * (3 + α) * (n : ℝ) * ((n : ℝ) - 1)) := by
      simp only [hA1, hA2, M]
      push_cast
      field_simp
      ring
    rw [key]
    refine div_nonneg ?_ (by positivity)
    nlinarith [hcert]
  have hexp : n + 1 - 4 = (n - 4) + 1 := by omega
  calc T2 (n + 1) α
      = A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
            / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) := by
        rw [T2, hexp, pow_succ]
        ring
    _ ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg hb0 _)
    _ = T2 n α := by rw [T2]

/-- `T2` is bounded by its value at `n = 101`. -/
lemma T2_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 n α ≤ T2 101 α := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (T2_step hm hα hα').trans ih

/-! ### The bound with no degree left in it -/

/-- The elementary bound at `n = 101`, with `√B` removed and `α` the only variable. -/
noncomputable def Ut (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / 200 + 1 / (400 * (3 + α)) + 101 / 100 * T1 101 α
    + (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48

/-- **`U` is bounded by an expression in `α` alone**, for every `n ≥ 101`.  This is where the
degree leaves the argument. -/
theorem U_le_Ut (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : U n α ≤ Ut α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (100 : ℝ) ≤ M n := by simp only [M]; linarith
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  rw [U_eq (by omega) hα (ne_of_gt hcpos), Ut]
  have e1 : 1 / (2 * M n) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have e2 : 1 / (4 * M n * (3 + α)) ≤ 1 / (400 * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e3 := T1_le hn hα hα'
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 1 := by
    have hle : α / (3 + α) ≤ 1 := by rw [div_le_one h3]; linarith
    calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hpow : Real.sqrt (α / (3 + α)) ^ (101 - 4) ≤ (α / (3 + α)) ^ 48 := by
    have h97 : Real.sqrt (α / (3 + α)) ^ (101 - 4)
        = (α / (3 + α)) ^ 48 * Real.sqrt (α / (3 + α)) := by
      rw [show (101 : ℕ) - 4 = 2 * 48 + 1 by norm_num, pow_succ, pow_mul, Real.sq_sqrt hB]
    rw [h97]
    nlinarith [pow_nonneg hB 48]
  have e4 : T2 101 α
      ≤ (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48 := by
    have hA101 : A 101 α = (100 - 2 * α) / 100 := by
      simp only [A, M]
      norm_num
      ring
    have hT2 : T2 101 α = (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α))
        * Real.sqrt (α / (3 + α)) ^ (101 - 4) := by
      simp only [T2, hA101, M]
      norm_num
      ring_nf
      tauto
    rw [hT2]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have e5 := (T2_le hn hα hα').trans e4
  linarith

end TaoSendov
-- ===== from teorth/sendov TaoSendov/LargeDegree/Endgame.lean =====
/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/

/-!
# The large-degree claim

`TaoSendov.U_le_Ut` removed the degree from the bound; what is left is the single inequality
`Ut α < 1` on `0 ≤ α ≤ 17`, and then `R n α < 1` for every `n ≥ 101`.

`Ut` is a rational function of `α` times `(α/(3+α)) ^ 48`, so multiplying by

  `D = 865200 · (3+α) ^ 49 · γ ^ 4`,   `γ = 300 + 47α - α²`,

which is positive on `[0,17]`, turns the claim into positivity of the single polynomial
`F = D (1 - Ut)` of degree `58`.  The two closed forms used are

  `c 101 α = γ / (100 (3+α))`,
  `T1 101 α = 1600000 (100-2α)² (3+α)³ / (721 γ⁴)`.

A Bernstein certificate on `[0,17]` settles it: all 59 coefficients of `F` in the basis
`α^m (17-α)^(58-m)` are positive, so no subdivision of the `α`-range is needed.  (The
informal write-up splits at `α = 16` and estimates the two pieces separately; that is not
necessary once the sharp Beta constant is used, which is what leaves the margin — `Ut` peaks
at `α = 17` with value `0.9229`.)

## Why the multiplication is distributed by hand

`D (1 - Ut)` must not be handed to `field_simp`: it would clear `(3+α) ^ 49` and `γ ⁴` from
both sides at once, leaving `ring` a degree-115 identity that it does not close.  `D` already
*contains* exactly those denominators, so each of the six terms of `Ut` cancels against it
separately.  Doing that first (`TaoSendov.Ut_lt_one`, steps `t1`–`t6`, and `h48` for the `48`-th
power) keeps every `ring` call at degree at most `62`, which is the same size as the
certificate identity itself.  `865200` rather than `865200` is used as the multiplier so that
each term separately, not merely their sum, comes out with integer coefficients.

## Main statements

* `TaoSendov.Ut_lt_one`: `Ut α < 1` on `0 ≤ α ≤ 17`;
* `TaoSendov.large_degree`: `R n α < 1` for `n ≥ 101`.
-/

namespace TaoSendov

variable {α : ℝ}

set_option maxHeartbeats 4000000 in
-- a degree-58 identity in one variable; `ring` needs more than the default budget
/-- The Bernstein certificate: `F` is positive on `[0,17]`. -/
lemma F_pos (hα : 0 ≤ α) (hα' : α ≤ 17) :
    0 < 1122702787291394736448332031899900000000 + 19046325083555631071589567727384404000000 * α + 158421799401305511319831453323336122340000 * α ^ 2 + 861086144839783899262522290902928965732400 * α ^ 3 + 3439408019860839882261371580238947745811319 * α ^ 4 + 10763976190978343059270128976319908699279230 * α ^ 5 + 27482264870203746404049226779511973140100922 * α ^ 6 + 58851751350273881387953189525455032864879976 * α ^ 7 + 107855247587877306122230293103712405510570475 * α ^ 8 + 171759728691636266490365540891679381811794330 * α ^ 9 + 240529488382582584529650966973246412375404200 * α ^ 10 + 299026713527922503750214218383542861883052640 * α ^ 11 + 332584383792637363818110693156644176263245770 * α ^ 12 + 333049929303875184857821696251322094451555300 * α ^ 13 + 301880762905153988961008260011013859110924020 * α ^ 14 + 248778383542817950458457719347804130388393200 * α ^ 15 + 187098708657492312991354787006951375606496810 * α ^ 16 + 128821377534531366266108990532541378516293180 * α ^ 17 + 81419630849957631346647265524754482691775400 * α ^ 18 + 47345231058420765609063602657623737762737040 * α ^ 19 + 25377634631717199993415818405387727249820325 * α ^ 20 + 12558381461678887884336588690871882873720170 * α ^ 21 + 5744808624780589326694261819822529221060710 * α ^ 22 + 2431706095253331452737540626239749451182200 * α ^ 23 + 953157993950838580367703259303917955151865 * α ^ 24 + 346144642670223976596034179062502690180750 * α ^ 25 + 116495518414609472010567246197077176778320 * α ^ 26 + 36336281152740288609221052030650841399360 * α ^ 27 + 10502010275079971287850469706276099760700 * α ^ 28 + 2811408048396859598615803016678577566616 * α ^ 29 + 696637045577195749563697260889295071320 * α ^ 30 + 159631247175312590035611267009797954208 * α ^ 31 + 33785522480785269776966858820750983964 * α ^ 32 + 6594450665275339854415586104207300200 * α ^ 33 + 1184779969344702509178802875319571760 * α ^ 34 + 195478905533580848831244517654808400 * α ^ 35 + 29535092351319878473338799170306705 * α ^ 36 + 4072478636506932555839271140088690 * α ^ 37 + 510306927013451786184096375133350 * α ^ 38 + 57808428584128470185954723726040 * α ^ 39 + 5881482509330352987406470588525 * α ^ 40 + 532894392271418064251604942870 * α ^ 41 + 42515012647728027357611076360 * α ^ 42 + 2939585612233076406278632800 * α ^ 43 + 171946491190832176774496730 * α ^ 44 + 8163588014241841361016900 * α ^ 45 + 287999399301298111575540 * α ^ 46 + 5555726484083859953520 * α ^ 47 - 536551383276446293350 * α ^ 48 - 269167118332858968420 * α ^ 49 - 48279425158933803000 * α ^ 50 - 1759012112154436560 * α ^ 51 + 273395914772406495 * α ^ 52 + 6240162359537050 * α ^ 53 - 1129204084343291 * α ^ 54 + 41554143448524 * α ^ 55 - 721404477395 * α ^ 56 + 6229533730 * α ^ 57 - 21627837 * α ^ 58 := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have h0 : (0:ℝ) ≤ 1122702787291394736448332031899900000000 * (17 - α) ^ 58 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 58)
  have h1 : (0:ℝ) ≤ 388904288083346622931025909215729068000000 * α ^ 1 * (17 - α) ^ 57 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 57)
  have h2 : (0:ℝ) ≤ 66095616740335374779150673987010161532260000 * α ^ 2 * (17 - α) ^ 56 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 56)
  have h3 : (0:ℝ) ≤ 7345821640480281350499142140546658776321841200 * α ^ 3 * (17 - α) ^ 55 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 55)
  have h4 : (0:ℝ) ≤ 600398748030850807066041679815685800572608040199 * α ^ 4 * (17 - α) ^ 54 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 54)
  have h5 : (0:ℝ) ≤ 38479987967757849353019399973163199134827376858856 * α ^ 5 * (17 - α) ^ 53 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 53)
  have h6 : (0:ℝ) ≤ 2013648131786096177205150562840212460891734276215217 * α ^ 6 * (17 - α) ^ 52 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 52)
  have h7 : (0:ℝ) ≤ 88459088337848664272764574750756035751708812314589560 * α ^ 7 * (17 - α) ^ 51 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 51)
  have h8 : (0:ℝ) ≤ 3328752627388631431253304215842302161184427248710824200 * α ^ 8 * (17 - α) ^ 50 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 50)
  have h9 : (0:ℝ) ≤ 108955148579598077254581984889507974501857717600550300000 * α ^ 9 * (17 - α) ^ 49 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 49)
  have h10 : (0:ℝ) ≤ 3139320986827193043298955183356728835782414071606732250000 * α ^ 10 * (17 - α) ^ 48 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 10)) (pow_nonneg hu 48)
  have h11 : (0:ℝ) ≤ 80389849002074687648105368735226451202772917094058768000000 * α ^ 11 * (17 - α) ^ 47 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 11)) (pow_nonneg hu 47)
  have h12 : (0:ℝ) ≤ 1843869779817877110104286469976591396926664444962705440000000 * α ^ 12 * (17 - α) ^ 46 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 12)) (pow_nonneg hu 46)
  have h13 : (0:ℝ) ≤ 38126021284745149595963616317393007484187425284263404800000000 * α ^ 13 * (17 - α) ^ 45 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 13)) (pow_nonneg hu 45)
  have h14 : (0:ℝ) ≤ 714519722771974812940511821448225512188719319523829280000000000 * α ^ 14 * (17 - α) ^ 44 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 14)) (pow_nonneg hu 44)
  have h15 : (0:ℝ) ≤ 12192162072496626088921760868440507818256588279501222400000000000 * α ^ 15 * (17 - α) ^ 43 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 15)) (pow_nonneg hu 43)
  have h16 : (0:ℝ) ≤ 190149195298252798424521646382266997826378949113808102400000000000 * α ^ 16 * (17 - α) ^ 42 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 16)) (pow_nonneg hu 42)
  have h17 : (0:ℝ) ≤ 2719453325782140875058402865898661993411332371079473152000000000000 * α ^ 17 * (17 - α) ^ 41 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 17)) (pow_nonneg hu 41)
  have h18 : (0:ℝ) ≤ 35765156781668343145270939254204039481078844597447447040000000000000 * α ^ 18 * (17 - α) ^ 40 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 18)) (pow_nonneg hu 40)
  have h19 : (0:ℝ) ≤ 433581369383490123337920330591320005197369743601113088000000000000000 * α ^ 19 * (17 - α) ^ 39 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 19)) (pow_nonneg hu 39)
  have h20 : (0:ℝ) ≤ 4855120840322429070915669670313005676027625016591872000000000000000000 * α ^ 20 * (17 - α) ^ 38 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 20)) (pow_nonneg hu 38)
  have h21 : (0:ℝ) ≤ 50303800927352895844904371767120477621293024508175810560000000000000000 * α ^ 21 * (17 - α) ^ 37 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 21)) (pow_nonneg hu 37)
  have h22 : (0:ℝ) ≤ 482953904720497092819809519030958414936076990756461772800000000000000000 * α ^ 22 * (17 - α) ^ 36 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 22)) (pow_nonneg hu 36)
  have h23 : (0:ℝ) ≤ 4301697515309799266557277840727716853246295229412212736000000000000000000 * α ^ 23 * (17 - α) ^ 35 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 23)) (pow_nonneg hu 35)
  have h24 : (0:ℝ) ≤ 35582005974740842580199098139010545771216816653126860800000000000000000000 * α ^ 24 * (17 - α) ^ 34 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 24)) (pow_nonneg hu 34)
  have h25 : (0:ℝ) ≤ 273535549248031302586908863638264651412739231630163968000000000000000000000 * α ^ 25 * (17 - α) ^ 33 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 25)) (pow_nonneg hu 33)
  have h26 : (0:ℝ) ≤ 1955426273644204648009173651834541693843095232637140992000000000000000000000 * α ^ 26 * (17 - α) ^ 32 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 26)) (pow_nonneg hu 32)
  have h27 : (0:ℝ) ≤ 13004222926412994888311248631808734105341900865415413760000000000000000000000 * α ^ 27 * (17 - α) ^ 31 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 27)) (pow_nonneg hu 31)
  have h28 : (0:ℝ) ≤ 80470387643773112884644249468688475191473557588882227200000000000000000000000 * α ^ 28 * (17 - α) ^ 30 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 28)) (pow_nonneg hu 30)
  have h29 : (0:ℝ) ≤ 463355476918012102672652719197790300193712035699097600000000000000000000000000 * α ^ 29 * (17 - α) ^ 29 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 29)) (pow_nonneg hu 29)
  have h30 : (0:ℝ) ≤ 2482344082055683113128185595725000998635940934141870080000000000000000000000000 * α ^ 30 * (17 - α) ^ 28 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 30)) (pow_nonneg hu 28)
  have h31 : (0:ℝ) ≤ 12369353793584370842106405783534323328114720329863004160000000000000000000000000 * α ^ 31 * (17 - α) ^ 27 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 31)) (pow_nonneg hu 27)
  have h32 : (0:ℝ) ≤ 57300834405504520484711032055319485636127102860053708800000000000000000000000000 * α ^ 32 * (17 - α) ^ 26 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 32)) (pow_nonneg hu 26)
  have h33 : (0:ℝ) ≤ 246613403330189144932245957910378250136137902552252416000000000000000000000000000 * α ^ 33 * (17 - α) ^ 25 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 33)) (pow_nonneg hu 25)
  have h34 : (0:ℝ) ≤ 985246695411671462829426238732411673050896371023872000000000000000000000000000000 * α ^ 34 * (17 - α) ^ 24 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 34)) (pow_nonneg hu 24)
  have h35 : (0:ℝ) ≤ 3649974776445129628396257437653948413551102593597440000000000000000000000000000000 * α ^ 35 * (17 - α) ^ 23 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 35)) (pow_nonneg hu 23)
  have h36 : (0:ℝ) ≤ 12522828085409243337307923676013931236910302987550720000000000000000000000000000000 * α ^ 36 * (17 - α) ^ 22 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 36)) (pow_nonneg hu 22)
  have h37 : (0:ℝ) ≤ 39731340789062838384502107867195079108983927708057600000000000000000000000000000000 * α ^ 37 * (17 - α) ^ 21 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 37)) (pow_nonneg hu 21)
  have h38 : (0:ℝ) ≤ 116365100653574128528674694068315721419971773857792000000000000000000000000000000000 * α ^ 38 * (17 - α) ^ 20 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 38)) (pow_nonneg hu 20)
  have h39 : (0:ℝ) ≤ 313971050757264181615490913824916376724876505907200000000000000000000000000000000000 * α ^ 39 * (17 - α) ^ 19 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 39)) (pow_nonneg hu 19)
  have h40 : (0:ℝ) ≤ 778602881203434272472350446775468799876667539456000000000000000000000000000000000000 * α ^ 40 * (17 - α) ^ 18 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 40)) (pow_nonneg hu 18)
  have h41 : (0:ℝ) ≤ 1769823234178269115425193251412793044953817153536000000000000000000000000000000000000 * α ^ 41 * (17 - α) ^ 17 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 41)) (pow_nonneg hu 17)
  have h42 : (0:ℝ) ≤ 3676061908648613727975384722760757591726652129280000000000000000000000000000000000000 * α ^ 42 * (17 - α) ^ 16 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 42)) (pow_nonneg hu 16)
  have h43 : (0:ℝ) ≤ 6952202666310032877475473290777345311129573785600000000000000000000000000000000000000 * α ^ 43 * (17 - α) ^ 15 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 43)) (pow_nonneg hu 15)
  have h44 : (0:ℝ) ≤ 11922241592723733002313059523572394705939333120000000000000000000000000000000000000000 * α ^ 44 * (17 - α) ^ 14 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 44)) (pow_nonneg hu 14)
  have h45 : (0:ℝ) ≤ 18450845478651168634684539530259247984017408000000000000000000000000000000000000000000 * α ^ 45 * (17 - α) ^ 13 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 45)) (pow_nonneg hu 13)
  have h46 : (0:ℝ) ≤ 25626302281194153741004424813630605199042150400000000000000000000000000000000000000000 * α ^ 46 * (17 - α) ^ 12 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 46)) (pow_nonneg hu 12)
  have h47 : (0:ℝ) ≤ 31735356381499745521943376637135285074788352000000000000000000000000000000000000000000 * α ^ 47 * (17 - α) ^ 11 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 47)) (pow_nonneg hu 11)
  have h48 : (0:ℝ) ≤ 34773986078859125604170241648646078618789153800477215677912265790935664780750000000000 * α ^ 48 * (17 - α) ^ 10 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 48)) (pow_nonneg hu 10)
  have h49 : (0:ℝ) ≤ 33406510810664082686608872230111026353099051641531587806834322064288344554180000000000 * α ^ 49 * (17 - α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 49)) (pow_nonneg hu 9)
  have h50 : (0:ℝ) ≤ 27820946523539616021999756980494999341031737804699133246948994617042670678045550000000 * α ^ 50 * (17 - α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 50)) (pow_nonneg hu 8)
  have h51 : (0:ℝ) ≤ 19791944456596303161181417657916215477628661862047060146272089595047078222827061000000 * α ^ 51 * (17 - α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 51)) (pow_nonneg hu 7)
  have h52 : (0:ℝ) ≤ 11779484527176566489160923853925282151874607361320815965499241151163816336970531507500 * α ^ 52 * (17 - α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 52)) (pow_nonneg hu 6)
  have h53 : (0:ℝ) ≤ 5685451710206041407628952698706724254113808400301600724661558108213464738446593549500 * α ^ 53 * (17 - α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 53)) (pow_nonneg hu 5)
  have h54 : (0:ℝ) ≤ 2124220422337628714954562682925792634155465583908214661397004639843167881489238854787 * α ^ 54 * (17 - α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 54)) (pow_nonneg hu 4)
  have h55 : (0:ℝ) ≤ 572909076732572616057605734230328840239193993814061157407956440967916397115623518120 * α ^ 55 * (17 - α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 55)) (pow_nonneg hu 3)
  have h56 : (0:ℝ) ≤ 99530623246032452139763064572679576747235355843313027086842616874975359183988464200 * α ^ 56 * (17 - α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 56)) (pow_nonneg hu 2)
  have h57 : (0:ℝ) ≤ 8820861539641882551843091227900257872626927159038875775406157756108783934565132000 * α ^ 57 * (17 - α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 57)) (pow_nonneg hu 1)
  have h58 : (0:ℝ) ≤ 161598081294237579548393327166198311182821276785721838823669379905701080186270000 * α ^ 58 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 58)
  have hid : (17 : ℝ) ^ 58 * (1122702787291394736448332031899900000000 + 19046325083555631071589567727384404000000 * α + 158421799401305511319831453323336122340000 * α ^ 2 + 861086144839783899262522290902928965732400 * α ^ 3 + 3439408019860839882261371580238947745811319 * α ^ 4 + 10763976190978343059270128976319908699279230 * α ^ 5 + 27482264870203746404049226779511973140100922 * α ^ 6 + 58851751350273881387953189525455032864879976 * α ^ 7 + 107855247587877306122230293103712405510570475 * α ^ 8 + 171759728691636266490365540891679381811794330 * α ^ 9 + 240529488382582584529650966973246412375404200 * α ^ 10 + 299026713527922503750214218383542861883052640 * α ^ 11 + 332584383792637363818110693156644176263245770 * α ^ 12 + 333049929303875184857821696251322094451555300 * α ^ 13 + 301880762905153988961008260011013859110924020 * α ^ 14 + 248778383542817950458457719347804130388393200 * α ^ 15 + 187098708657492312991354787006951375606496810 * α ^ 16 + 128821377534531366266108990532541378516293180 * α ^ 17 + 81419630849957631346647265524754482691775400 * α ^ 18 + 47345231058420765609063602657623737762737040 * α ^ 19 + 25377634631717199993415818405387727249820325 * α ^ 20 + 12558381461678887884336588690871882873720170 * α ^ 21 + 5744808624780589326694261819822529221060710 * α ^ 22 + 2431706095253331452737540626239749451182200 * α ^ 23 + 953157993950838580367703259303917955151865 * α ^ 24 + 346144642670223976596034179062502690180750 * α ^ 25 + 116495518414609472010567246197077176778320 * α ^ 26 + 36336281152740288609221052030650841399360 * α ^ 27 + 10502010275079971287850469706276099760700 * α ^ 28 + 2811408048396859598615803016678577566616 * α ^ 29 + 696637045577195749563697260889295071320 * α ^ 30 + 159631247175312590035611267009797954208 * α ^ 31 + 33785522480785269776966858820750983964 * α ^ 32 + 6594450665275339854415586104207300200 * α ^ 33 + 1184779969344702509178802875319571760 * α ^ 34 + 195478905533580848831244517654808400 * α ^ 35 + 29535092351319878473338799170306705 * α ^ 36 + 4072478636506932555839271140088690 * α ^ 37 + 510306927013451786184096375133350 * α ^ 38 + 57808428584128470185954723726040 * α ^ 39 + 5881482509330352987406470588525 * α ^ 40 + 532894392271418064251604942870 * α ^ 41 + 42515012647728027357611076360 * α ^ 42 + 2939585612233076406278632800 * α ^ 43 + 171946491190832176774496730 * α ^ 44 + 8163588014241841361016900 * α ^ 45 + 287999399301298111575540 * α ^ 46 + 5555726484083859953520 * α ^ 47 - 536551383276446293350 * α ^ 48 - 269167118332858968420 * α ^ 49 - 48279425158933803000 * α ^ 50 - 1759012112154436560 * α ^ 51 + 273395914772406495 * α ^ 52 + 6240162359537050 * α ^ 53 - 1129204084343291 * α ^ 54 + 41554143448524 * α ^ 55 - 721404477395 * α ^ 56 + 6229533730 * α ^ 57 - 21627837 * α ^ 58) = 1122702787291394736448332031899900000000 * (17 - α) ^ 58 + 388904288083346622931025909215729068000000 * α ^ 1 * (17 - α) ^ 57 + 66095616740335374779150673987010161532260000 * α ^ 2 * (17 - α) ^ 56 + 7345821640480281350499142140546658776321841200 * α ^ 3 * (17 - α) ^ 55 + 600398748030850807066041679815685800572608040199 * α ^ 4 * (17 - α) ^ 54 + 38479987967757849353019399973163199134827376858856 * α ^ 5 * (17 - α) ^ 53 + 2013648131786096177205150562840212460891734276215217 * α ^ 6 * (17 - α) ^ 52 + 88459088337848664272764574750756035751708812314589560 * α ^ 7 * (17 - α) ^ 51 + 3328752627388631431253304215842302161184427248710824200 * α ^ 8 * (17 - α) ^ 50 + 108955148579598077254581984889507974501857717600550300000 * α ^ 9 * (17 - α) ^ 49 + 3139320986827193043298955183356728835782414071606732250000 * α ^ 10 * (17 - α) ^ 48 + 80389849002074687648105368735226451202772917094058768000000 * α ^ 11 * (17 - α) ^ 47 + 1843869779817877110104286469976591396926664444962705440000000 * α ^ 12 * (17 - α) ^ 46 + 38126021284745149595963616317393007484187425284263404800000000 * α ^ 13 * (17 - α) ^ 45 + 714519722771974812940511821448225512188719319523829280000000000 * α ^ 14 * (17 - α) ^ 44 + 12192162072496626088921760868440507818256588279501222400000000000 * α ^ 15 * (17 - α) ^ 43 + 190149195298252798424521646382266997826378949113808102400000000000 * α ^ 16 * (17 - α) ^ 42 + 2719453325782140875058402865898661993411332371079473152000000000000 * α ^ 17 * (17 - α) ^ 41 + 35765156781668343145270939254204039481078844597447447040000000000000 * α ^ 18 * (17 - α) ^ 40 + 433581369383490123337920330591320005197369743601113088000000000000000 * α ^ 19 * (17 - α) ^ 39 + 4855120840322429070915669670313005676027625016591872000000000000000000 * α ^ 20 * (17 - α) ^ 38 + 50303800927352895844904371767120477621293024508175810560000000000000000 * α ^ 21 * (17 - α) ^ 37 + 482953904720497092819809519030958414936076990756461772800000000000000000 * α ^ 22 * (17 - α) ^ 36 + 4301697515309799266557277840727716853246295229412212736000000000000000000 * α ^ 23 * (17 - α) ^ 35 + 35582005974740842580199098139010545771216816653126860800000000000000000000 * α ^ 24 * (17 - α) ^ 34 + 273535549248031302586908863638264651412739231630163968000000000000000000000 * α ^ 25 * (17 - α) ^ 33 + 1955426273644204648009173651834541693843095232637140992000000000000000000000 * α ^ 26 * (17 - α) ^ 32 + 13004222926412994888311248631808734105341900865415413760000000000000000000000 * α ^ 27 * (17 - α) ^ 31 + 80470387643773112884644249468688475191473557588882227200000000000000000000000 * α ^ 28 * (17 - α) ^ 30 + 463355476918012102672652719197790300193712035699097600000000000000000000000000 * α ^ 29 * (17 - α) ^ 29 + 2482344082055683113128185595725000998635940934141870080000000000000000000000000 * α ^ 30 * (17 - α) ^ 28 + 12369353793584370842106405783534323328114720329863004160000000000000000000000000 * α ^ 31 * (17 - α) ^ 27 + 57300834405504520484711032055319485636127102860053708800000000000000000000000000 * α ^ 32 * (17 - α) ^ 26 + 246613403330189144932245957910378250136137902552252416000000000000000000000000000 * α ^ 33 * (17 - α) ^ 25 + 985246695411671462829426238732411673050896371023872000000000000000000000000000000 * α ^ 34 * (17 - α) ^ 24 + 3649974776445129628396257437653948413551102593597440000000000000000000000000000000 * α ^ 35 * (17 - α) ^ 23 + 12522828085409243337307923676013931236910302987550720000000000000000000000000000000 * α ^ 36 * (17 - α) ^ 22 + 39731340789062838384502107867195079108983927708057600000000000000000000000000000000 * α ^ 37 * (17 - α) ^ 21 + 116365100653574128528674694068315721419971773857792000000000000000000000000000000000 * α ^ 38 * (17 - α) ^ 20 + 313971050757264181615490913824916376724876505907200000000000000000000000000000000000 * α ^ 39 * (17 - α) ^ 19 + 778602881203434272472350446775468799876667539456000000000000000000000000000000000000 * α ^ 40 * (17 - α) ^ 18 + 1769823234178269115425193251412793044953817153536000000000000000000000000000000000000 * α ^ 41 * (17 - α) ^ 17 + 3676061908648613727975384722760757591726652129280000000000000000000000000000000000000 * α ^ 42 * (17 - α) ^ 16 + 6952202666310032877475473290777345311129573785600000000000000000000000000000000000000 * α ^ 43 * (17 - α) ^ 15 + 11922241592723733002313059523572394705939333120000000000000000000000000000000000000000 * α ^ 44 * (17 - α) ^ 14 + 18450845478651168634684539530259247984017408000000000000000000000000000000000000000000 * α ^ 45 * (17 - α) ^ 13 + 25626302281194153741004424813630605199042150400000000000000000000000000000000000000000 * α ^ 46 * (17 - α) ^ 12 + 31735356381499745521943376637135285074788352000000000000000000000000000000000000000000 * α ^ 47 * (17 - α) ^ 11 + 34773986078859125604170241648646078618789153800477215677912265790935664780750000000000 * α ^ 48 * (17 - α) ^ 10 + 33406510810664082686608872230111026353099051641531587806834322064288344554180000000000 * α ^ 49 * (17 - α) ^ 9 + 27820946523539616021999756980494999341031737804699133246948994617042670678045550000000 * α ^ 50 * (17 - α) ^ 8 + 19791944456596303161181417657916215477628661862047060146272089595047078222827061000000 * α ^ 51 * (17 - α) ^ 7 + 11779484527176566489160923853925282151874607361320815965499241151163816336970531507500 * α ^ 52 * (17 - α) ^ 6 + 5685451710206041407628952698706724254113808400301600724661558108213464738446593549500 * α ^ 53 * (17 - α) ^ 5 + 2124220422337628714954562682925792634155465583908214661397004639843167881489238854787 * α ^ 54 * (17 - α) ^ 4 + 572909076732572616057605734230328840239193993814061157407956440967916397115623518120 * α ^ 55 * (17 - α) ^ 3 + 99530623246032452139763064572679576747235355843313027086842616874975359183988464200 * α ^ 56 * (17 - α) ^ 2 + 8820861539641882551843091227900257872626927159038875775406157756108783934565132000 * α ^ 57 * (17 - α) ^ 1 + 161598081294237579548393327166198311182821276785721838823669379905701080186270000 * α ^ 58 := by
    ring
  rcases le_total α (17 / 2) with h | h
  · have hpos : (0 : ℝ) < 1122702787291394736448332031899900000000 * (17 - α) ^ 58 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 58)
    linarith
  · have hpos : (0 : ℝ) < 161598081294237579548393327166198311182821276785721838823669379905701080186270000 * α ^ 58 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 58)
    linarith

set_option maxHeartbeats 4000000 in
/-- **The bound in `α` alone is below `1`.** -/
theorem Ut_lt_one (hα : 0 ≤ α) (hα' : α ≤ 17) : Ut α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hg : (0 : ℝ) < 300 + 47 * α - α ^ 2 := by nlinarith
  have hgne : (300 : ℝ) + 47 * α - α ^ 2 ≠ 0 := hg.ne'
  have hc : c 101 α = (300 + 47 * α - α ^ 2) / (100 * (3 + α)) := by
    simp only [c, M]
    norm_num
    field_simp
    ring
  have hT1 : T1 101 α
      = 1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3 / (721 * (300 + 47 * α - α ^ 2) ^ 4) := by
    simp only [T1, hc]
    norm_num
    field_simp
    ring
  -- `(α/(3+α)) ^ 48` cancels against `(3+α) ^ 49` without expanding either
  have h48 : (α / (3 + α)) ^ 48 * (3 + α) ^ 49 = α ^ 48 * (3 + α) := by
    rw [div_pow, show (3 + α) ^ 49 = (3 + α) ^ 48 * (3 + α) from by ring, ← mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero 48 h3.ne')]
  -- the six terms of `Ut`, each multiplied by `D`
  have t1 : (1 / 6 : ℝ) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4) = 144200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4 := by
    ring
  have t2 : 1 / (4 * (3 + α)) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4) = 216300 * (3 + α) ^ 48 * (300 + 47 * α - α ^ 2) ^ 4 := by
    field_simp
    ring
  have t3 : (1 / 200 : ℝ) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4) = 4326 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4 := by
    ring
  have t4 : 1 / (400 * (3 + α)) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4) = 2163 * (3 + α) ^ 48 * (300 + 47 * α - α ^ 2) ^ 4 := by
    field_simp
    ring
  have t5 : 101 / 100 * (1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3
        / (721 * (300 + 47 * α - α ^ 2) ^ 4)) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4)
      = 1939200000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 52 := by
    -- cancel the γ⁴ syntactically; `field_simp` leaves a stray γ⁻¹ here
    have hne : (721 : ℝ) * (300 + 47 * α - α ^ 2) ^ 4 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 4 hg.ne')
    rw [show 101 / 100 * (1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3
            / (721 * (300 + 47 * α - α ^ 2) ^ 4)) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4)
          = 1600000 * (100 - 2 * α) ^ 2 * (3 + α) ^ 3
              / (721 * (300 + 47 * α - α ^ 2) ^ 4) * (721 * (300 + 47 * α - α ^ 2) ^ 4)
              * (1212 * (3 + α) ^ 49) from by ring,
      div_mul_cancel₀ _ hne]
    ring
  have t6 : (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48
        * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4)
      = (21627837 / 4) * (100 - 2 * α) ^ 2 * α ^ 48 * (300 + 47 * α - α ^ 2) ^ 4 := by
    rw [show (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48
          * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4)
        = ((100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (865200 * (300 + 47 * α - α ^ 2) ^ 4))
          * ((α / (3 + α)) ^ 48 * (3 + α) ^ 49) from by ring, h48]
    field_simp
    ring
  have hD : (0 : ℝ) < 865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4 := by
    have h49 := pow_pos h3 49
    have hg4 := pow_pos hg 4
    positivity
  have hmul : (1 - Ut α) * (865200 * (3 + α) ^ 49 * (300 + 47 * α - α ^ 2) ^ 4) = 1122702787291394736448332031899900000000 + 19046325083555631071589567727384404000000 * α + 158421799401305511319831453323336122340000 * α ^ 2 + 861086144839783899262522290902928965732400 * α ^ 3 + 3439408019860839882261371580238947745811319 * α ^ 4 + 10763976190978343059270128976319908699279230 * α ^ 5 + 27482264870203746404049226779511973140100922 * α ^ 6 + 58851751350273881387953189525455032864879976 * α ^ 7 + 107855247587877306122230293103712405510570475 * α ^ 8 + 171759728691636266490365540891679381811794330 * α ^ 9 + 240529488382582584529650966973246412375404200 * α ^ 10 + 299026713527922503750214218383542861883052640 * α ^ 11 + 332584383792637363818110693156644176263245770 * α ^ 12 + 333049929303875184857821696251322094451555300 * α ^ 13 + 301880762905153988961008260011013859110924020 * α ^ 14 + 248778383542817950458457719347804130388393200 * α ^ 15 + 187098708657492312991354787006951375606496810 * α ^ 16 + 128821377534531366266108990532541378516293180 * α ^ 17 + 81419630849957631346647265524754482691775400 * α ^ 18 + 47345231058420765609063602657623737762737040 * α ^ 19 + 25377634631717199993415818405387727249820325 * α ^ 20 + 12558381461678887884336588690871882873720170 * α ^ 21 + 5744808624780589326694261819822529221060710 * α ^ 22 + 2431706095253331452737540626239749451182200 * α ^ 23 + 953157993950838580367703259303917955151865 * α ^ 24 + 346144642670223976596034179062502690180750 * α ^ 25 + 116495518414609472010567246197077176778320 * α ^ 26 + 36336281152740288609221052030650841399360 * α ^ 27 + 10502010275079971287850469706276099760700 * α ^ 28 + 2811408048396859598615803016678577566616 * α ^ 29 + 696637045577195749563697260889295071320 * α ^ 30 + 159631247175312590035611267009797954208 * α ^ 31 + 33785522480785269776966858820750983964 * α ^ 32 + 6594450665275339854415586104207300200 * α ^ 33 + 1184779969344702509178802875319571760 * α ^ 34 + 195478905533580848831244517654808400 * α ^ 35 + 29535092351319878473338799170306705 * α ^ 36 + 4072478636506932555839271140088690 * α ^ 37 + 510306927013451786184096375133350 * α ^ 38 + 57808428584128470185954723726040 * α ^ 39 + 5881482509330352987406470588525 * α ^ 40 + 532894392271418064251604942870 * α ^ 41 + 42515012647728027357611076360 * α ^ 42 + 2939585612233076406278632800 * α ^ 43 + 171946491190832176774496730 * α ^ 44 + 8163588014241841361016900 * α ^ 45 + 287999399301298111575540 * α ^ 46 + 5555726484083859953520 * α ^ 47 - 536551383276446293350 * α ^ 48 - 269167118332858968420 * α ^ 49 - 48279425158933803000 * α ^ 50 - 1759012112154436560 * α ^ 51 + 273395914772406495 * α ^ 52 + 6240162359537050 * α ^ 53 - 1129204084343291 * α ^ 54 + 41554143448524 * α ^ 55 - 721404477395 * α ^ 56 + 6229533730 * α ^ 57 - 21627837 * α ^ 58 := by
    rw [Ut, hT1, sub_mul, one_mul, add_mul, add_mul, add_mul, add_mul, add_mul,
      t1, t2, t3, t4, t5, t6]
    ring
  rw [← sub_pos]
  have hF := F_pos hα hα'
  nlinarith [hmul, hF, hD]

/-- **The large-degree claim.**  Every degree `n ≥ 101`. -/
theorem large_degree {n : ℕ} (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  exact lt_of_le_of_lt
    (le_trans (R_le_U (by omega) hα hfeas hcpos) (U_le_Ut hn hα hα'))
    (Ut_lt_one hα hα')

end TaoSendov

-- ===== Bridge to the formal-conjectures statement (new) =====
namespace OMA.SendovBridge

open Polynomial

theorem satisfies_of_numClaim {n : ℕ} (hnum : 5 ≤ n → TaoSendov.NumClaim n) :
    Sendov.Nat.SatisfiesSendovConjecture n := by
  intro f hf hdeg z hz
  have h2 : 2 ≤ f.natDegree := hf.1
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at h2
    omega
  have hroots : ∀ w ∈ f.roots, ‖w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ f.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨hf0, ?_⟩
      have := (Polynomial.mem_roots hf0).1 hw
      simpa [Polynomial.aeval_def] using this
    simpa using hf.2 hw'
  have hz0 : f.eval z = 0 := by
    rw [Polynomial.mem_rootSet] at hz
    simpa [Polynomial.aeval_def] using hz.2
  obtain ⟨ζ, hζ, hle⟩ := TaoSendov.sendov hnum (hdeg ▸ h2) hdeg hroots hz0
  have hd0 : derivative f ≠ 0 := by
    intro h
    have := (Polynomial.derivative_eq_zero).1 h
    omega
  have hmem : ζ ∈ (derivative f).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hd0, ?_⟩
    simpa [Polynomial.aeval_def] using hζ
  calc Metric.infDist z ((derivative f).rootSet ℂ) ≤ dist z ζ :=
        Metric.infDist_le_dist_of_mem hmem
    _ = ‖ζ - z‖ := by rw [dist_comm, dist_eq_norm]
    _ ≤ 1 := hle

theorem eventually_true :
    ∀ᶠ (n : ℕ) in Filter.atTop, Sendov.Nat.SatisfiesSendovConjecture n := by
  filter_upwards [Filter.eventually_ge_atTop 101] with n hn
  exact satisfies_of_numClaim fun _ _ hα hα' hfeas => TaoSendov.large_degree hn hα hα' hfeas

end OMA.SendovBridge

theorem OMA.solution : type_of% @Sendov.sendov_conjecture.variants.eventually_true :=
  OMA.SendovBridge.eventually_true
