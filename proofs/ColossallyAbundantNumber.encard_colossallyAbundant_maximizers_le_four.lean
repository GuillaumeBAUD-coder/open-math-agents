import FormalConjectures.Wikipedia.ColossallyAbundantNumber
import Mathlib

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-ca-maximizers/blob/eabb6173b6271ce4b6ca91c92caab5adb5d44060/CARatiosFC/Maximizers.lean  (theorem encard_colossallyAbundant_maximizers_le_four)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE)
The six exponentials theorem it uses is vendored in that repo from carlok/six-exponentials-lean (commit
b42d65be65fc4e4a7cea3ba965aabea8f1df8028), Copyright (c) 2026 Carlo Perassi, Apache-2.0 (LICENSE.six-exponentials).
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: flattened SixExponentials/Basic/*.lean (eleven files, in dependency order), CARatiosFC/SixExpPrimes.lean, CARatiosFC/Local.lean and CARatiosFC/Maximizers.lean into one file under namespace OMAPort_CA; removed the module-system lines
(module, public import, public section); replaced attribute [local instance] Matrix.seminormedAddCommGroup by a let
inside the proof of siegel_entrywise; renamed lemmas to their names at the older Mathlib (ite_eq_left/right to
if_pos/if_neg, dite_eq_left/right to dif_pos/dif_neg, prod_le_prod0 to prod_le_prod, Nat.factorization_prod_pow_eq_self
to Nat.prod_pow_factorization_eq_self); dropped the non-vacuity check tie_two from Local.lean; the final theorem is
stated as OMA.solution and applied to the original theorem.
-/

/-
NOTICE of the original package (retained as required by Apache-2.0, section 4(d)):

ColossallyAbundantMaximizers (standalone package)
Copyright 2026 Sky (GitHub: ChironTheCentaur)

The original work in this package (CARatiosFC/, LeanClassics/, ColossallyAbundantMaximizers.lean, check.py,
AxiomAudit.lean, PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

SixExponentials.lean and SixExponentials/Basic/*.lean are copied byte for byte from carlok/six-exponentials-lean,
commit b42d65be65fc4e4a7cea3ba965aabea8f1df8028, Copyright (c) 2026 Carlo Perassi, licensed under the Apache License,
Version 2.0 (see LICENSE.six-exponentials; provenance in vendor/SOURCE.txt, hashes in vendor/SHA256SUMS).

The definitions in CARatiosFC/Defs.lean and the statements of encard_colossallyAbundant_maximizers_le_four
(CARatiosFC/Maximizers.lean) and alaoglu_erdos_prime_or_semiprime_ratio (CARatiosFC/Ratio.lean) are copied verbatim
from google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/ColossallyAbundantNumber.lean, commit ea8e3e19),
Copyright The Formal Conjectures Authors, licensed under the Apache License, Version 2.0.
-/

namespace OMAPort_CA

/- ===== SixExponentials/Basic/SXDefs.lean ===== -/
/-
Origin: `Diaz/SXDefs.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`@[expose] public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

# Definitions for the six-exponentials mission, as the platform states them

Mirrored from Prove2Me's `SX` definition node. The Diaz node
`DiazModulus.six_exponentials` rests on `SX.six_exponentials_of_numberField`, which is
stated in these terms, so they are carried here verbatim.
-/



/-
# Definitions bundle for the six exponentials theorem

Everything the five statements of the `six-exp` ladder need that Mathlib (rev
`0df444a3`) does not have. Nothing here is a mathematical result: four `def`s,
five structural lemmas whose proofs are pure bookkeeping, and one computation
(`exp_expExponent_mul_latticeSum`) that is the arithmetic bridge every rung uses.
-/

open Complex Finset

namespace SixExponentials.SX

variable {d l : ℕ}

/-- The box of multi-indices `λ : Fin d → ℕ` with every coordinate `< L`.
This is the index set of the coefficients of the auxiliary exponential polynomial. -/
def box (d L : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ => Finset.range L

@[simp] theorem mem_box {L : ℕ} {lam : Fin d → ℕ} :
    lam ∈ box d L ↔ ∀ i, lam i < L := by
  simp [box, Fintype.mem_piFinset]

/-- The lattice point `∑ j, m j • y j`. As `m` ranges over `ℕ ^ l` these are the points at
which the auxiliary function is made to vanish. -/
def latticeSum (y : Fin l → ℂ) (m : Fin l → ℕ) : ℂ := ∑ j, (m j : ℂ) * y j

/-- The exponent `∑ i, λ i • x i` attached to a multi-index `λ`. -/
def expExponent (x : Fin d → ℂ) (lam : Fin d → ℕ) : ℂ := ∑ i, (lam i : ℂ) * x i

/-- The auxiliary function `F(z) = ∑_{λ ∈ box d L} p λ * exp (⟨λ, x⟩ * z)`:
a `ℤ`-linear combination of the monomials in `exp (x 0 * z), …, exp (x (d-1) * z)`
of partial degree `< L`. -/
noncomputable def expSum (x : Fin d → ℂ) (L : ℕ) (p : (Fin d → ℕ) → ℤ) : ℂ → ℂ :=
  fun z => ∑ lam ∈ box d L, (p lam : ℂ) * Complex.exp (expExponent x lam * z)

/-- `f` has order of growth at most `ρ`. Mathlib has no order-of-growth theory at this
revision; the auxiliary function of Schneider's method has order `1`, and this predicate is
what an abstract form of the criterion would quantify over. -/
def OrderAtMost (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (c * ‖z‖ ^ ρ)

theorem differentiable_expSum (x : Fin d → ℂ) (L : ℕ) (p : (Fin d → ℕ) → ℤ) :
    Differentiable ℂ (expSum x L p) := by
  unfold expSum
  fun_prop

@[simp] theorem expSum_zero (x : Fin d → ℂ) (L : ℕ) (z : ℂ) :
    expSum x L (fun _ => 0) z = 0 := by simp [expSum]

@[simp] theorem latticeSum_zero (y : Fin l → ℂ) : latticeSum y (fun _ => 0) = 0 := by
  simp [latticeSum]

/-- The arithmetic bridge: at a lattice point the auxiliary function's exponentials are
monomials in the six numbers `exp (x i * y j)`. This is what puts the values of `expSum`
inside the number field generated by them. -/
theorem exp_expExponent_mul_latticeSum (x : Fin d → ℂ) (y : Fin l → ℂ)
    (lam : Fin d → ℕ) (m : Fin l → ℕ) :
    Complex.exp (expExponent x lam * latticeSum y m)
      = ∏ i, ∏ j, Complex.exp (x i * y j) ^ (lam i * m j) := by
  have hsum : expExponent x lam * latticeSum y m
      = ∑ i, ∑ j, ((lam i * m j : ℕ) : ℂ) * (x i * y j) := by
    rw [expExponent, latticeSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [hsum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => Complex.exp_nat_mul _ _

end SixExponentials.SX

/- ===== SixExponentials/Basic/cauchy_estimate_with_zeros.lean ===== -/
/-
Origin: `Diaz/Mirror/cauchy_estimate_with_zeros.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `FourExp.cauchy_estimate_with_zeros`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/FourExp.cauchy_estimate_with_zeros__b133f53b.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
Names and spellings that changed between the platform's Mathlib revision and the one
pinned here were updated to match, and proof steps that became no-ops there were
dropped; the mathematics is unchanged.
-/



namespace SixExponentials

open Finset Metric

namespace FourExpCauchy

lemma order_sub_self (a : ℂ) : analyticOrderAt (· - a) a = 1 := by
  have := analyticOrderAt_centeredMonomial (n := 1) (z₀ := a)
  simp_all [pow_one]

lemma order_sub_of_ne {a b : ℂ} (h : b ≠ a) : analyticOrderAt (· - a) b = 0 :=
  analyticOrderAt_eq_zero.2 (Or.inr (by simp [sub_eq_zero, h]))

/-- Divide out one zero of an entire function with `dslope`. -/
lemma peel_one (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a : ℂ) (ha : F a = 0) :
    Differentiable ℂ (dslope F a) ∧ ∀ z, F z = (z - a) * dslope F a z := by
  refine ⟨?_, fun z => ?_⟩
  · exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := Set.univ) (f := F) (c := a) Filter.univ_mem).2
        hF.differentiableOn)
  · have h := sub_smul_dslope F a z
    simp only [smul_eq_mul, ha, sub_zero] at h
    exact h.symm

/-- Divide out a zero of order at least `k`, keeping the orders at every other point. -/
lemma peel (a : ℂ) : ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (k : ℕ∞) ≤ analyticOrderAt F a →
    ∃ D : ℂ → ℂ, Differentiable ℂ D ∧ (∀ z, F z = (z - a) ^ k * D z) ∧
      ∀ b, b ≠ a → analyticOrderAt D b = analyticOrderAt F b
  | 0, F, hF, _ => ⟨F, hF, fun z => by simp, fun _ _ => rfl⟩
  | k + 1, F, hF, hk => by
    have hFa : F a = 0 := by
      have h0 : analyticOrderAt F a ≠ 0 := by
        intro h
        rw [h] at hk
        simp at hk
      exact (analyticOrderAt_ne_zero.1 h0).2
    obtain ⟨hD1, hfac⟩ := peel_one F hF a hFa
    have hFeq : F = (· - a) * dslope F a := funext fun z => hfac z
    have hord : ∀ b, analyticOrderAt F b
        = analyticOrderAt (· - a) b + analyticOrderAt (dslope F a) b := by
      intro b
      conv_lhs => rw [hFeq]
      exact analyticOrderAt_mul (analyticAt_id.sub analyticAt_const) (hD1.analyticAt b)
    have hk' : (k : ℕ∞) ≤ analyticOrderAt (dslope F a) a := by
      have h1 := hord a
      rw [order_sub_self] at h1
      rw [h1] at hk
      generalize analyticOrderAt (dslope F a) a = x at hk ⊢
      induction x using ENat.recTopCoe with
      | top => simp
      | coe x =>
        norm_cast at hk ⊢
        omega
    obtain ⟨D, hD, hfacD, hordD⟩ := peel a k (dslope F a) hD1 hk'
    refine ⟨D, hD, fun z => by rw [hfac z, hfacD z]; ring, fun b hb => ?_⟩
    rw [hordD b hb, hord b, order_sub_of_ne hb, zero_add]

/-- An entire function is divisible by the polynomial carrying its zeros on a finite set. -/
lemma factor (S : Finset ℂ) : ∀ (n : ℂ → ℕ) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ a ∈ S, (n a : ℕ∞) ≤ analyticOrderAt F a) →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = (∏ a ∈ S, (z - a) ^ n a) * G z := by
  induction S using Finset.induction_on with
  | empty => intro n F hF _; exact ⟨F, hF, fun z => by simp⟩
  | insert a S haS ih =>
    intro n F hF hn
    obtain ⟨D, hD, hfac, hord⟩ := peel a (n a) F hF (hn a (mem_insert_self a S))
    obtain ⟨G, hG, hfacG⟩ := ih n D hD (fun b hb => by
      rw [hord b (fun h => haS (h ▸ hb))]
      exact hn b (mem_insert_of_mem hb))
    exact ⟨G, hG, fun z => by rw [hfac z, hfacG z, prod_insert haS]; ring⟩

end FourExpCauchy

theorem cauchy_estimate_with_zeros
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ) (hR : ρ + 1 < R)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - c‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - c‖ = R → ‖F z‖ ≤ M) (s : ℕ) :
    ‖iteratedDeriv s F c‖
      ≤ (s.factorial : ℝ) * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ (∑ z ∈ S, analyticOrderNatAt F z) * M := by
  obtain ⟨G, hG, hfac⟩ := FourExpCauchy.factor S (analyticOrderNatAt F) F hF (fun a _ => by
    unfold analyticOrderNatAt
    generalize analyticOrderAt F a = x
    induction x using ENat.recTopCoe <;> simp)
  set N := ∑ z ∈ S, analyticOrderNatAt F z with hN
  have hR0 : 0 < R := by linarith
  have hRρ : 0 < R - ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (c + R) (by simp [abs_of_pos hR0]))
  -- On the sphere of radius `R` every factor `z - a` has norm at least `R - ρ`.
  have hGsphere : ∀ z : ℂ, ‖z - c‖ = R → ‖G z‖ ≤ M / (R - ρ) ^ N := by
    intro z hz
    have hP : (R - ρ) ^ N ≤ ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod (fun _ _ => pow_nonneg hRρ.le _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ hRρ.le
      have h1 := norm_sub_norm_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    rw [le_div_iff₀ (pow_pos hRρ N)]
    calc ‖G z‖ * (R - ρ) ^ N
        ≤ ‖G z‖ * ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ :=
          mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = ‖F z‖ := by rw [hfac z, norm_mul, mul_comm]
      _ ≤ M := hM z hz
  -- Maximum principle for `G` on the disc of radius `R`.
  have hGball : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖G w‖ ≤ M / (R - ρ) ^ N := by
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl
      (fun y hy => hGsphere y (by
        rw [frontier_ball _ hR0.ne'] at hy
        simpa [mem_sphere_iff_norm] using hy))
      (by rw [closure_ball _ hR0.ne', mem_closedBall_iff_norm]; exact hw)
  -- On the unit sphere every factor `z - a` has norm at most `ρ + 1`.
  have hFsmall : ∀ z ∈ sphere c 1, ‖F z‖ ≤ ((ρ + 1) / (R - ρ)) ^ N * M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hP : ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ ≤ (ρ + 1) ^ N := by
      rw [norm_prod, hN, ← prod_pow_eq_pow_sum]
      refine prod_le_prod (fun _ _ => norm_nonneg _) (fun a ha => ?_)
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h1 := norm_sub_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      linarith [hS a ha]
    have hGz := hGball z (by rw [hz]; linarith)
    calc ‖F z‖ = ‖∏ a ∈ S, (z - a) ^ analyticOrderNatAt F a‖ * ‖G z‖ := by
          rw [hfac z, norm_mul]
      _ ≤ (ρ + 1) ^ N * (M / (R - ρ) ^ N) :=
          mul_le_mul hP hGz (norm_nonneg _) (pow_nonneg (by linarith) _)
      _ = ((ρ + 1) / (R - ρ)) ^ N * M := by rw [div_pow]; ring
  -- Cauchy's estimate on the unit circle; the factor `R / (R - 1) ≥ 1` is slack.
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos
    hF.diffContOnCl hFsmall
  simp only [one_pow, div_one] at hC
  have hRR : 1 ≤ R / (R - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hK : 0 ≤ ((ρ + 1) / (R - ρ)) ^ N * M :=
    mul_nonneg (pow_nonneg (div_nonneg (by linarith) hRρ.le) _) hM0
  have hf : (0 : ℝ) ≤ s.factorial := by positivity
  calc ‖iteratedDeriv s F c‖ ≤ s.factorial * (((ρ + 1) / (R - ρ)) ^ N * M) := hC
    _ = s.factorial * 1 * (((ρ + 1) / (R - ρ)) ^ N * M) := by ring
    _ ≤ s.factorial * (R / (R - 1)) * (((ρ + 1) / (R - ρ)) ^ N * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRR hf) hK
    _ = s.factorial * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ N * M := by ring

end SixExponentials

/- ===== SixExponentials/Basic/expPoly_grid_estimate.lean ===== -/
/-
Origin: `Diaz/Mirror/expPoly_grid_estimate.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `Transcendence.expPoly_grid_estimate`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/Transcendence.expPoly_grid_estimate__a1309f19.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.Transcendence

/-
# A Cauchy estimate for an exponential polynomial on a grid

Let `F(z) = ∑ c_k z^(e_k) e^(ω_k z)` vanish to order `n` at every point `∑ m'_j y_j` with
`m'_j < t_j`. These `∏ t_j` points are distinct, since the `y_j` are `ℚ`-linearly independent, and
they lie within `ρ = ∑ A_j |y_j|` of the target `w = ∑ m_j y_j` (`m_j < A_j`). On the circle of
radius `R = (ρ + 1) u` about `w` we have `|z| ≤ Z`, so `|F(z)| ≤ (∑ |c_k|) Z^E e^(W Z)`. The Cauchy
estimate with zeros bounds `|F⁽ʳ⁾(w)|` by `r! · R/(R - 1) · ((ρ + 1)/(R - ρ))^(n ∏ t_j)` times this
maximum, and for `u ≥ 2` we have `R/(R - 1) ≤ 2` and `(ρ + 1)/(R - ρ) ≤ 1/(u - 1)`.
-/

theorem expPoly_grid_estimate {ι κ : Type*} [Fintype ι] (y : ι → ℂ)
    (hy : LinearIndependent ℚ y) (s : Finset κ) (c ω : κ → ℂ) (e : κ → ℕ) (F : ℂ → ℂ)
    (hF : ∀ z, F z = ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z))
    (W : ℝ) (E : ℕ) (hω : ∀ k ∈ s, ‖ω k‖ ≤ W) (he : ∀ k ∈ s, e k ≤ E)
    (t A : ι → ℕ) (htA : ∀ j, t j ≤ A j) (n : ℕ)
    (hvan : ∀ m : ι → ℕ, (∀ j, m j < t j) → ∀ i < n,
      iteratedDeriv i F (∑ j, (m j : ℂ) * y j) = 0)
    (u Z : ℝ) (hu : 2 ≤ u) (hZ : (∑ j, (A j : ℝ) * ‖y j‖ + 1) * (u + 1) ≤ Z)
    (m : ι → ℕ) (hm : ∀ j, m j < A j) (r : ℕ) :
    ‖iteratedDeriv r F (∑ j, (m j : ℂ) * y j)‖
      ≤ (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ ((∏ j, t j) * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
  classical
  have hFd : Differentiable ℂ F := by
    rw [show F = fun z => ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z) from funext hF]
    fun_prop
  set ρ : ℝ := ∑ j, (A j : ℝ) * ‖y j‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- the lattice points `∑ m' j * y j`, `m' j < t j`, are pairwise distinct
  set P : Finset ℂ := (Fintype.piFinset fun j => Finset.range (t j)).image
    (fun m' : ι → ℕ => ∑ j, (m' j : ℂ) * y j) with hP
  have hcard : P.card = ∏ j, t j := by
    rw [hP, Finset.card_image_of_injective, Fintype.card_piFinset]
    · simp
    intro a b hab
    have := hy.fintypeLinearCombination_injective (a₁ := fun j => (a j : ℚ))
      (a₂ := fun j => (b j : ℚ)) (by simpa [Fintype.linearCombination_apply, Rat.smul_def] using hab)
    funext j; exact_mod_cast congrFun this j
  -- every point of the grid is within `ρ` of the target
  have hdist : ∀ m' : ι → ℕ, (∀ j, m' j < A j) →
      ‖∑ j, (m' j : ℂ) * y j - ∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    intro m' hm'
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_mul, norm_mul, show (m' j : ℂ) - (m j : ℂ) = (((m' j : ℝ) - (m j : ℝ) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have a1 : (m' j : ℝ) < A j := by exact_mod_cast hm' j
    have a2 : (m j : ℝ) < A j := by exact_mod_cast hm j
    exact mul_le_mul_of_nonneg_right (abs_sub_le_iff.2 ⟨by linarith [(m j).cast_nonneg (α := ℝ)],
      by linarith [(m' j).cast_nonneg (α := ℝ)]⟩) (norm_nonneg _)
  have hw : ‖∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    simpa using hdist (fun _ => 0) fun j => (Nat.zero_le _).trans_lt (hm j)
  -- the bound on the circle of radius `(ρ + 1) * u` around the target
  have hZ1 : 1 ≤ Z := by nlinarith
  have hM : ∀ z : ℂ, ‖z - ∑ j, (m j : ℂ) * y j‖ = (ρ + 1) * u →
      ‖F z‖ ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    intro z hz
    have hzZ : ‖z‖ ≤ Z := by
      have := norm_le_insert' z (∑ j, (m j : ℂ) * y j)
      nlinarith
    rw [hF, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    gcongr
    · exact (pow_le_pow_left₀ (norm_nonneg _) hzZ _).trans (pow_le_pow_right₀ hZ1 (he k hk))
    · exact (Complex.re_le_norm _).trans (by
        rw [norm_mul]; exact mul_le_mul (hω k hk) hzZ (norm_nonneg _) ((norm_nonneg _).trans (hω k hk)))
  -- the target and the grid; every grid point is a zero of order at least `n`
  set w : ℂ := ∑ j, (m j : ℂ) * y j with hwdef
  set R : ℝ := (ρ + 1) * u with hR
  have hPw : ∀ z ∈ P, ‖z - w‖ ≤ ρ := fun z hz => by
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    exact hdist m' fun j => ((by simpa using Fintype.mem_piFinset.1 hm' j) : m' j < t j).trans_le (htA j)
  have hM0 : 0 ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    have : 0 ≤ Z ^ E := pow_nonneg (by linarith) _
    positivity
  by_cases hF0 : F = 0
  · rw [hF0, iteratedDeriv_const_zero, norm_zero]
    have : 0 ≤ 1 / (u - 1) := div_nonneg zero_le_one (by linarith)
    positivity
  have hle : P.card * n ≤ ∑ z ∈ P, analyticOrderNatAt F z := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun z hz => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    have h1 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFd.analyticAt _)).2
      (hvan m' fun j => by simpa using Fintype.mem_piFinset.1 hm' j)
    rw [← Nat.cast_analyticOrderNatAt fun h => hF0
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ fun u => hFd.analyticAt u).1 h)] at h1
    exact_mod_cast h1
  -- the Cauchy estimate on the circle of radius `R = (ρ + 1) u` around the target
  have key := SixExponentials.cauchy_estimate_with_zeros F hFd w ρ R _ hρ0 (by nlinarith) P hPw hM r
  refine key.trans ?_
  have h1 : R / (R - 1) ≤ 2 := by rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have h2 : (ρ + 1) / (R - ρ) ≤ 1 / (u - 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; nlinarith
  have h3 : 0 ≤ (ρ + 1) / (R - ρ) := div_nonneg (by positivity) (by nlinarith)
  have h4 : (ρ + 1) / (R - ρ) ≤ 1 := h2.trans (by rw [div_le_one (by linarith)]; linarith)
  rw [← hcard]
  calc _ ≤ (r.factorial : ℝ) * 2 * ((ρ + 1) / (R - ρ)) ^ (P.card * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity))
          (pow_le_pow_of_le_one h3 h4 hle) (by positivity) (by positivity)) hM0
    _ ≤ _ := by gcongr

end SixExponentials.Transcendence

/- ===== SixExponentials/Basic/exists_denom_house_monomial_le.lean ===== -/
/-
Origin: `Diaz/Mirror/exists_denom_house_monomial_le.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `Transcendence.exists_denom_house_monomial_le`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/Transcendence.exists_denom_house_monomial_le__1e823e1b.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.Transcendence

/-
# A common denominator with a house bound for monomials

Since `K` is algebraic over `ℤ`, one non-zero integer `b` makes every `b θᵢ` an algebraic integer.
If `∑ eᵢ ≤ E`, then `b ^ E ∏ θᵢ ^ eᵢ = b ^ (E - ∑ eᵢ) ∏ (b θᵢ) ^ eᵢ` is an algebraic integer, and as
the house is submultiplicative, its house is at most `H ^ E` for `H = 1 + house b + ∑ house (b θᵢ)`.
-/

open NumberField

namespace S7W4_exists_denom_house_monomial_le

/-- The house of a finite indexed product is at most the product of the houses. -/
lemma house_prod_le' {K ι : Type*} [Field K] [NumberField K] (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa only [house, map_prod] using Finset.norm_prod_le s (fun i => canonicalEmbedding K (f i))

end S7W4_exists_denom_house_monomial_le

open S7W4_exists_denom_house_monomial_le in
theorem exists_denom_house_monomial_le {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (θ : ι → K) : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧ ∀ (e : ι → ℕ) (E : ℕ),
      ∑ i, e i ≤ E → IsIntegral ℤ (b ^ E * ∏ i, θ i ^ e i) ∧ house (b ^ E * ∏ i, θ i ^ e i) ≤ H ^ E := by
  classical
  -- a non-zero integer clearing the denominators of all the `θ i`
  have : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image θ)
  obtain ⟨b, hb0, hb, hbθ⟩ : ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∀ i, IsIntegral ℤ (b * θ i) :=
    ⟨y, Int.cast_ne_zero.mpr hy0, isIntegral_intCast y, fun i => by
      simpa only [zsmul_eq_mul] using hy (θ i) (Finset.mem_image_of_mem θ (Finset.mem_univ i))⟩
  -- one constant bounding `1`, `house b` and every `house (b * θ i)`
  set H : ℝ := 1 + house b + ∑ i, house (b * θ i) with hH
  have hs : 0 ≤ ∑ i, house (b * θ i) := Finset.sum_nonneg fun i _ => house_nonneg _
  have hH1 : 1 ≤ H := by linarith [house_nonneg b]
  have hHb : house b ≤ H := by linarith
  have hHθ (i : ι) : house (b * θ i) ≤ H := by
    linarith [house_nonneg b,
      Finset.single_le_sum (fun j _ => house_nonneg (b * θ j)) (Finset.mem_univ i)]
  have hpow (x : K) (h : house x ≤ H) (n : ℕ) : house (x ^ n) ≤ H ^ n := by
    simpa only [house, map_pow] using (norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) h n)
  refine ⟨b, hb0, hb, H, hH1, fun e E hE => ?_⟩
  -- distribute the denominator over the monomial
  have key : b ^ E * ∏ i, θ i ^ e i = b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]
  rw [key]
  refine ⟨(hb.pow _).mul (IsIntegral.prod _ fun i _ => (hbθ i).pow _), ?_⟩
  calc house (b ^ (E - ∑ i, e i) * ∏ i, (b * θ i) ^ e i)
      ≤ house (b ^ (E - ∑ i, e i)) * ∏ i, house ((b * θ i) ^ e i) :=
        (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left (house_prod_le' _ _) (house_nonneg _))
    _ ≤ H ^ (E - ∑ i, e i) * ∏ i, H ^ e i := by
        -- written as norms, all the factors are visibly non-negative
        simp only [house]
        gcongr with i
        exacts [hpow b hHb _, hpow _ (hHθ i) _]
    _ = H ^ E := by rw [Finset.prod_pow_eq_pow_sum, ← pow_add, Nat.sub_add_cancel hE]

end SixExponentials.Transcendence

/- ===== SixExponentials/Basic/liouville_house.lean ===== -/
/-
Origin: `Diaz/Mirror/liouville_house.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `Transcendence.liouville_house`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/Transcendence.liouville_house__74580a12.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.Transcendence

open NumberField

-- Liouville's inequality in house form, with an integer denominator: `N(cα)` is a nonzero
-- integer, and `|N(cα)| ≤ ‖σ(cα)‖ · house(cα)^(d-1)` (Mathlib's `norm_norm_le_norm_mul_house_pow`).
theorem liouville_house {K : Type*} [Field K] [NumberField K] {α : K} (hα : α ≠ 0)
    {c : ℤ} (hc : c ≠ 0) (hcα : IsIntegral ℤ ((c : K) * α)) (σ : K →+* ℂ) :
    1 ≤ |(c : ℝ)| ^ Module.finrank ℚ K * ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  set d := Module.finrank ℚ K
  have hd : 1 ≤ d := Module.finrank_pos
  set γ : 𝓞 K := ⟨(c : K) * α, hcα⟩
  have hγ0 : γ ≠ 0 := fun h ↦ mul_ne_zero (Int.cast_ne_zero.mpr hc) hα
    (show algebraMap (𝓞 K) K γ = 0 by rw [h, map_zero])
  have h1 : (1 : ℝ) ≤ ‖Algebra.norm ℚ ((c : K) * α)‖ := by
    have hne : Algebra.norm ℤ γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ0
    rw [show (c : K) * α = algebraMap (𝓞 K) K γ from rfl, ← Algebra.coe_norm_int,
      ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  refine h1.trans ((norm_norm_le_norm_mul_house_pow _ σ).trans ?_)
  have hh : house ((c : K) * α) ≤ |(c : ℝ)| * house α := by
    simpa using house_mul_le (c : K) α
  calc ‖σ ((c : K) * α)‖ * house ((c : K) * α) ^ (d - 1)
      ≤ (|(c : ℝ)| * ‖σ α‖) * (|(c : ℝ)| * house α) ^ (d - 1) :=
        mul_le_mul (le_of_eq (by rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]))
          (pow_le_pow_left₀ (house_nonneg _) hh _) (pow_nonneg (house_nonneg _) _) (by positivity)
  _ = |(c : ℝ)| ^ d * ‖σ α‖ * house α ^ (d - 1) := by
        rw [mul_pow]; nth_rw 3 [show d = (d - 1) + 1 by omega]; ring

end SixExponentials.Transcendence

/- ===== SixExponentials/Basic/siegel_entrywise.lean ===== -/
/-
Origin: `Diaz/Mirror/siegel_entrywise.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `Transcendence.siegel_entrywise`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/Transcendence.siegel_entrywise__bd349ebf.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.Transcendence

/-
# Siegel's lemma with an entrywise bound

Let `A` be an integer matrix with `m` rows, `n ≥ 2m` columns and entries of absolute value at most
`B ≥ 1`. With no rows, a unit vector is a non-zero siegel_entrywise of `A t = 0`. Otherwise Siegel's lemma
gives a non-zero integer siegel_entrywise with `|t_b| ≤ (n · max(1, ‖A‖))^(m / (n - m))`, where `‖A‖ ≤ B`
is the largest absolute value of an entry. The exponent `m / (n - m)` lies in `[0, 1]` and
`n B ≥ 1`, so `|t_b| ≤ n B`.
-/

theorem siegel_entrywise {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)
    (hβ : 0 < Fintype.card β) (hcard : 2 * Fintype.card α ≤ Fintype.card β) {B : ℝ}
    (hB : 1 ≤ B) (hA : ∀ a b, |(A a b : ℝ)| ≤ B) :
    ∃ t : β → ℤ, t ≠ 0 ∧ (∀ a, ∑ b, A a b * t b = 0) ∧
      ∀ b, |(t b : ℝ)| ≤ Fintype.card β * B := by
  letI : SeminormedAddCommGroup (Matrix α β ℤ) := Matrix.seminormedAddCommGroup
  classical
  have hn1 : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · -- no equations: a unit vector will do
    obtain ⟨b0⟩ : Nonempty β := Fintype.card_pos_iff.1 hβ
    have : IsEmpty α := Fintype.card_eq_zero_iff.1 h0
    refine ⟨Pi.single b0 1, fun h => by simpa using congrFun h b0, fun a => isEmptyElim a,
      fun b => ?_⟩
    by_cases hb : b = b0
    · subst hb; simp; nlinarith
    · simp [hb]; positivity
  · obtain ⟨t, ht0, hAt, hnorm⟩ :=
      Int.Matrix.exists_ne_zero_int_vec_norm_le A (by omega) hpos
    refine ⟨t, ht0, fun a => by simpa [Matrix.mulVec, dotProduct] using congrFun hAt a,
      fun b => ?_⟩
    have hmax : max 1 ‖A‖ ≤ B := max_le hB <| (Matrix.norm_le_iff (by linarith)).2
      fun i j => by rw [Int.norm_eq_abs]; exact hA i j
    have h2 : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hcard
    have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    -- with at least twice as many unknowns as equations the Siegel exponent is at most one
    have he1 : ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have he0 : (0 : ℝ) ≤ ((Fintype.card α : ℕ) : ℝ) / ((Fintype.card β : ℕ) - (Fintype.card α : ℕ)) :=
      div_nonneg hm.le (by linarith)
    have hbase : (1 : ℝ) ≤ Fintype.card β * B := by nlinarith
    calc |(t b : ℝ)| = ‖t b‖ := (Int.norm_eq_abs _).symm
      _ ≤ ‖t‖ := norm_le_pi_norm t b
      _ ≤ _ := hnorm
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (((Fintype.card α : ℕ) : ℝ) /
            ((Fintype.card β : ℕ) - (Fintype.card α : ℕ))) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hmax (by positivity)) he0
      _ ≤ ((Fintype.card β : ℝ) * B) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase he1
      _ = Fintype.card β * B := Real.rpow_one _

end SixExponentials.Transcendence

/- ===== SixExponentials/Basic/descent_step.lean ===== -/
/-
Origin: `Diaz/Mirror/descent_step.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `SX.descent_step`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/SX.descent_step__bec25c95.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.SX

open Complex

open NumberField

/-
The descent step of the six exponentials theorem.

Suppose `F = expSum x L p` vanishes at the lattice points `∑ m j • y j` with every `m j < N`,
but not at some `w = ∑ m j • y j` with every `m j ≤ N`.
* Upper bound. `F` is an exponential polynomial with coefficients `p λ` and frequencies
  `⟨λ, x⟩` of modulus `≤ L X`, `X = ∑ |x i|`. The `N ^ l` zeros are distinct because the `y j` are
  ℚ-linearly independent, and the grid estimate with radius parameter `u = 3` gives
  `|F w| ≤ 2 · 2^(-N^l) · B e^{4 X (2Y + 1) L N}`, `Y = ∑ |y j|`, where `B = L^d e^{c L M}`
  bounds `∑ |p λ|`.
* Lower bound. `F w` is the image of `β = ∑ p λ ∏ θ_ij ^ (λ i m j)`, `θ_ij = exp (x i y j) ∈ K`.
  With a common denominator `b` of the `θ_ij`, `b^E β` (`E = d l L N`) is a nonzero algebraic
  integer of house `≤ B G^E`, and Liouville's inequality gives
  `1 ≤ G^E |F w| (B G^E)^([K:ℚ] - 1)`.
* Together, `2^(N^l) ≤ exp (C L N)`. With `L^d ≤ c M^l ≤ c N^l` and `d l ≥ d + l + 1` this forces
  `N (log 2)^d ≤ C^d c`, which fails once `N ≥ M ≥ M₀`.
-/

theorem descent_step
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K)
    (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : ℕ, 0 < L → (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l →
      ∀ p : (Fin d → ℕ) → ℤ, (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) →
        ∀ N : ℕ, M ≤ N →
          (∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0) →
          (∀ m : Fin l → ℕ, (∀ j, m j < N + 1) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := {}
  set rk := Module.finrank ℚ K with hrk
  have hrk1 : 1 ≤ rk := Module.finrank_pos
  set σ : K →+* ℂ := K.val.toRingHom
  -- the numbers `exp (x i * y j)` as elements of `K`, a common denominator `b` and a house bound
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩ 
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := Transcendence.exists_denom_house_monomial_le θ
  set G : ℝ := max 1 (house b) * H
  have hHG : H ≤ G := le_mul_of_one_le_left (by positivity) (le_max_left 1 (house b))
  have hbG : house b ≤ G := (le_max_right 1 (house b)).trans (le_mul_of_one_le_right (by positivity) hH1)
  have hG1 : 1 ≤ G := hH1.trans hHG
  set X := ∑ i, ‖x i‖
  set Y := ∑ j, ‖y j‖
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set C : ℝ := 1 + rk * (d + c) + 4 * X * (2 * Y + 1) + d * l * rk * Real.log G with hC
  have hC0 : 0 ≤ C := by have := Real.log_nonneg hG1; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1, fun M hM L hL hLc p hp N hMN hvan m hm => ?_⟩
  by_contra hne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_pos _).trans_le (hM.trans hMN)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set B : ℝ := (L : ℝ) ^ d * Real.exp (c * L * M) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (Real.one_le_exp (by positivity))
  have hpB : ∑ lam ∈ SX.box d L, |(p lam : ℝ)| ≤ B := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun lam _ => hp lam).trans_eq ?_
    simp [SX.box, Fintype.card_piFinset, hB]
  -- the analytic upper bound: the grid estimate with `u = 3`
  have hup : ‖SX.expSum x L p (SX.latticeSum y m)‖
      ≤ 2 * (1 / 2) ^ (N ^ l) * (B * Real.exp (L * X * (4 * N * (2 * Y + 1)))) := by
    have h := Transcendence.expPoly_grid_estimate y hy (SX.box d L) (fun lam => (p lam : ℂ))
      (SX.expExponent x) (fun _ => 0) (SX.expSum x L p) (fun z => by simp [SX.expSum]) (L * X) 0
      (fun lam hlam => ?_) (fun _ _ => le_rfl) (fun _ => N) (fun _ => N + 1) (fun _ => N.le_succ) 1
      (fun m' hm' i hi => ?_) 3 (4 * N * (2 * Y + 1)) (by norm_num) ?_ m hm 0
    · simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.norm_intCast] at h
      norm_num at h
      refine h.trans ?_
      gcongr
    · rw [SX.mem_box] at hlam
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.mul_sum _ _ _).symm)
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hlam i).le) (norm_nonneg _)
    · rw [Nat.lt_one_iff.1 hi, iteratedDeriv_zero]; exact hvan m' hm'
    · rw [← Finset.mul_sum]; push_cast; nlinarith
  -- the arithmetic lower bound: the value lies in `K` and Liouville's inequality applies
  set E : ℕ := d * l * L * N with hE
  set β : K := ∑ lam ∈ SX.box d L, (p lam : K) * ∏ ij, θ ij ^ (lam ij.1 * m ij.2) with hβ
  have heE : ∀ lam ∈ SX.box d L, ∑ ij : Fin d × Fin l, lam ij.1 * m ij.2 ≤ E := fun lam hlam =>
    (Finset.sum_le_card_nsmul _ _ (L * N) fun ij _ => Nat.mul_le_mul ((SX.mem_box.1 hlam) ij.1).le
      (Nat.lt_succ_iff.1 (hm ij.2))).trans_eq (by simp [hE]; ring)
  have hσβ : σ β = SX.expSum x L p (SX.latticeSum y m) := by
    rw [hβ, SX.expSum, map_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, map_intCast, map_prod, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl
  have hβ0 : β ≠ 0 := fun h => hne (by rw [← hσβ, h, map_zero])
  have hδ : b ^ E * β = ∑ lam ∈ SX.box d L, (p lam : K) * (b ^ E * ∏ ij, θ ij ^ (lam ij.1 * m ij.2)) := by
    rw [hβ, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hint : IsIntegral ℤ (((1 : ℤ) : K) * (b ^ E * β)) := by
    rw [Int.cast_one, one_mul, hδ]
    exact IsIntegral.sum _ fun lam hlam =>
      (isIntegral_algebraMap (x := p lam)).mul (hbH _ E (heE lam hlam)).1
  have hhouse : house (b ^ E * β) ≤ B * G ^ E := by
    rw [hδ]
    refine (house_sum_le_sum_house _ _).trans ((Finset.sum_le_sum (g := fun lam => |(p lam : ℝ)| * G ^ E)
      fun lam hlam => (house_mul_le _ _).trans ?_).trans ?_)
    · rw [house_intCast, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left ((hbH _ E (heE lam hlam)).2.trans (by gcongr)) (abs_nonneg _)
    · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hpB (by positivity)
  have hliou := Transcendence.liouville_house (mul_ne_zero (pow_ne_zero E hb0) hβ0) one_ne_zero hint σ
  rw [Int.cast_one, abs_one, one_pow, one_mul, map_mul, map_pow, norm_mul, norm_pow, hσβ] at hliou
  -- combining the two bounds: `2 ^ (N ^ l) ≤ exp (C L N)`
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrk1
  have hLN : (1 : ℝ) ≤ L * N := one_le_mul_of_one_le_of_one_le hL1 hN1
  have hBexp : B ≤ Real.exp ((d + c) * (L * N)) := by
    have h1 : (L : ℝ) ≤ Real.exp (L * N) :=
      (by linarith [Real.add_one_le_exp ((L : ℝ) - 1)] : (L : ℝ) ≤ Real.exp (L - 1)).trans
        (Real.exp_le_exp.2 (by nlinarith))
    have h2 : c * L * M ≤ c * (L * N) := by
      rw [mul_assoc]; gcongr
    rw [add_mul, Real.exp_add, hB, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 d) (Real.exp_le_exp.2 h2) (by positivity)
      (by positivity)
  have hkey : (2 : ℝ) ^ (N ^ l) ≤ Real.exp (C * (L * N)) := by
    have hσb : ‖σ b‖ ^ E ≤ G ^ E := pow_le_pow_left₀ (norm_nonneg _) ((norm_embedding_le_house b σ).trans hbG) E
    have hG0 : 0 ≤ G := by linarith
    have hB0 : 0 ≤ B := by linarith
    have h1 := hliou.trans (mul_le_mul (mul_le_mul hσb hup (norm_nonneg _) (pow_nonneg hG0 E))
      (pow_le_pow_left₀ (house_nonneg _) hhouse _) (pow_nonneg (house_nonneg _) _) (by positivity))
    rw [← hrk, hk, Nat.add_sub_cancel_left] at h1
    calc (2 : ℝ) ^ (N ^ l) ≤ 2 ^ (N ^ l) * (G ^ E * (2 * (1 / 2) ^ (N ^ l) *
          (B * Real.exp (L * X * (4 * N * (2 * Y + 1))))) * (B * G ^ E) ^ k) := by
          simpa using mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ (N ^ l))
      _ = 2 * B ^ (1 + k) * G ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [mul_pow B (G ^ E) k, ← pow_mul G E k, one_div, inv_pow]; field_simp; ring
      _ ≤ Real.exp (L * N) * Real.exp ((d + c) * (L * N)) ^ (1 + k) *
          Real.exp (G.log) ^ (E * (1 + k)) * Real.exp (L * X * (4 * N * (2 * Y + 1))) := by
          rw [Real.exp_log (by positivity)]
          gcongr
          exact (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1).trans (Real.exp_le_exp.2 hLN)
      _ = Real.exp (C * (L * N)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
            hC, hk, hE]
          push_cast; ring_nf
  -- the endgame: `N ^ l log 2 ≤ C L N` and `L ^ d ≤ c N ^ l` force `N (log 2) ^ d ≤ C ^ d c`
  have h2 : (N : ℝ) ^ l * Real.log 2 ≤ C * (L * N) := by
    have := Real.log_le_log (by positivity) hkey
    rwa [Real.log_pow, Real.log_exp, Nat.cast_pow] at this
  have hLc' : (L : ℝ) ^ d ≤ c * N ^ l := hLc.trans (by gcongr)
  have hNd : (N : ℝ) ^ (l + d) * N ≤ N ^ (l * d) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hN1 (by rw [Nat.mul_comm]; omega)
  have hend : (N : ℝ) * Real.log 2 ^ d ≤ C ^ d * c := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < N ^ (l + d))
    calc (N : ℝ) ^ (l + d) * (N * Real.log 2 ^ d) = (N ^ (l + d) * N) * Real.log 2 ^ d := by ring
      _ ≤ N ^ (l * d) * Real.log 2 ^ d := by gcongr
      _ = ((N : ℝ) ^ l * Real.log 2) ^ d := by rw [mul_pow, ← pow_mul]
      _ ≤ (C * (L * N)) ^ d := by gcongr
      _ = C ^ d * (L : ℝ) ^ d * (N : ℝ) ^ d := by rw [mul_pow, mul_pow, ← mul_assoc]
      _ ≤ C ^ d * (c * (N : ℝ) ^ l) * (N : ℝ) ^ d := by gcongr
      _ = (N : ℝ) ^ (l + d) * (C ^ d * c) := by ring
  have hlt : C ^ d * c / Real.log 2 ^ d < N := by
    have h3 : ((⌈C ^ d * c / Real.log 2 ^ d⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hM.trans hMN
    push_cast at h3
    linarith [Nat.le_ceil (C ^ d * c / Real.log 2 ^ d)]
  rw [div_lt_iff₀ (by positivity)] at hlt
  linarith

end SixExponentials.SX

/- ===== SixExponentials/Basic/eq_zero_of_expSum_vanishes.lean ===== -/
/-
Origin: `Diaz/Mirror/eq_zero_of_expSum_vanishes.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `SX.eq_zero_of_expSum_vanishes`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/SX.eq_zero_of_expSum_vanishes__b95d3c48.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
Names and spellings that changed between the platform's Mathlib revision and the one
pinned here were updated to match, and proof steps that became no-ops there were
dropped; the mathematics is unchanged.
-/



namespace SixExponentials.SX

open Complex

namespace ZeroAux

variable {d l : ℕ}

/-- The character attached to a multi-index: `m ↦ exp (⟨λ,x⟩ * ⟨m,y⟩)`, a monoid
homomorphism out of `ℕ^l` written multiplicatively. -/
noncomputable def chi (x : Fin d → ℂ) (y : Fin l → ℂ) (lam : Fin d → ℕ) :
    Multiplicative (Fin l → ℕ) →* ℂ where
  toFun m := Complex.exp (SX.expExponent x lam * SX.latticeSum y (Multiplicative.toAdd m))
  map_one' := by
    show Complex.exp (SX.expExponent x lam * SX.latticeSum y 0) = 1
    simp [SX.latticeSum]
  map_mul' a b := by
    have hadd : SX.latticeSum y (Multiplicative.toAdd a + Multiplicative.toAdd b)
        = SX.latticeSum y (Multiplicative.toAdd a) + SX.latticeSum y (Multiplicative.toAdd b) := by
      simp only [SX.latticeSum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply]
      push_cast; ring
    show Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [show Multiplicative.toAdd (a * b)
          = Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
      hadd, mul_add, Complex.exp_add]

end ZeroAux

open ZeroAux in
theorem eq_zero_of_expSum_vanishes
    {d l : ℕ} (hl : 2 ≤ l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (L : ℕ) (p : (Fin d → ℕ) → ℤ)
    (h : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0) :
    ∀ lam ∈ SX.box d L, p lam = 0 := by
  classical
  -- `λ ↦ χ_λ` is injective; this is where `hx`, `hy` and `2 ≤ l` are spent
  have hinj : Function.Injective (chi x y (l := l)) := by
    intro lam mu hEq
    -- evaluating at the unit vectors: `(A - B) * y j ∈ 2πi ℤ`
    have hval : ∀ j : Fin l, ∃ n : ℤ,
        (SX.expExponent x lam - SX.expExponent x mu) * y j
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      intro j
      have hls : SX.latticeSum y
          (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))) = y j := by
        show SX.latticeSum y (Pi.single j (1 : ℕ)) = y j
        rw [SX.latticeSum, Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ j) hb
      have hpt := DFunLike.congr_fun hEq (Multiplicative.ofAdd (Pi.single j (1 : ℕ)))
      simp only [chi, MonoidHom.coe_mk, OneHom.coe_mk, hls] at hpt
      have h1 : Complex.exp ((SX.expExponent x lam - SX.expExponent x mu) * y j) = 1 := by
        rw [sub_mul, Complex.exp_sub, hpt, div_self (Complex.exp_ne_zero _)]
      exact Complex.exp_eq_one_iff.mp h1
    by_cases hAB : SX.expExponent x lam - SX.expExponent x mu = 0
    · -- `⟨λ - μ, x⟩ = 0`, so `λ = μ` by `ℚ`-linear independence of `x`
      have hAB0 : ∑ i, (lam i : ℂ) * x i = ∑ i, (mu i : ℂ) * x i := by
        simpa [SX.expExponent] using sub_eq_zero.mp hAB
      have key : ∑ i, (((lam i : ℚ) - (mu i : ℚ))) • x i = (0 : ℂ) := by
        have e : ∀ i : Fin d, (((lam i : ℚ) - (mu i : ℚ))) • x i
            = (lam i : ℂ) * x i - (mu i : ℂ) * x i := by
          intro i; rw [Rat.smul_def]; push_cast; ring
        simp only [e, Finset.sum_sub_distrib, hAB0, sub_self]
      have hz := (Fintype.linearIndependent_iff.mp hx) (fun i => (lam i : ℚ) - (mu i : ℚ)) key
      funext i
      have : (lam i : ℚ) = (mu i : ℚ) := sub_eq_zero.mp (hz i)
      exact_mod_cast this
    · exfalso
      have hi0 : (0 : ℕ) < l := by omega
      have hi1 : (1 : ℕ) < l := by omega
      set i0 : Fin l := ⟨0, hi0⟩ with hi0def
      set i1 : Fin l := ⟨1, hi1⟩ with hi1def
      have hne : i0 ≠ i1 := by simp [hi0def, hi1def, Fin.ext_iff]
      obtain ⟨n0, hn0⟩ := hval i0
      obtain ⟨n1, hn1⟩ := hval i1
      have hcomb : (n1 : ℂ) * y i0 - (n0 : ℂ) * y i1 = 0 := by
        have hw : (SX.expExponent x lam - SX.expExponent x mu)
            * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1) = 0 := by
          have hr : (SX.expExponent x lam - SX.expExponent x mu)
              * ((n1 : ℂ) * y i0 - (n0 : ℂ) * y i1)
              = (n1 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i0)
                - (n0 : ℂ) * ((SX.expExponent x lam - SX.expExponent x mu) * y i1) := by ring
          rw [hr, hn0, hn1]; ring
        rcases mul_eq_zero.mp hw with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      set g : Fin l → ℚ :=
        fun j => if j = i0 then (n1 : ℚ) else if j = i1 then -(n0 : ℚ) else 0 with hgdef
      have hsum : ∑ j, g j • y j = (0 : ℂ) := by
        rw [← Finset.sum_subset (Finset.subset_univ ({i0, i1} : Finset (Fin l)))]
        · rw [Finset.sum_pair hne]
          simp only [hgdef, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
          rw [Rat.smul_def, Rat.smul_def]
          push_cast
          linear_combination hcomb
        · intro j _ hj
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          simp [hgdef, hj.1, hj.2]
      have hg := (Fintype.linearIndependent_iff.mp hy) g hsum
      have hn0z : n0 = 0 := by
        have := hg i1
        simp only [hgdef, if_neg (Ne.symm hne), if_pos rfl] at this
        exact_mod_cast neg_eq_zero.mp this
      have hy0 : y i0 = 0 := by
        have : (SX.expExponent x lam - SX.expExponent x mu) * y i0 = 0 := by
          rw [hn0, hn0z]; simp
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hAB
        · exact h1
      exact hy.ne_zero i0 hy0
  -- Dedekind independence of characters, transported along the injection
  have hli : LinearIndependent ℂ (fun lam : Fin d → ℕ => ⇑(chi x y lam)) :=
    (linearIndependent_monoidHom (Multiplicative (Fin l → ℕ)) ℂ).comp _ hinj
  have hzero : ∑ lam ∈ SX.box d L, ((p lam : ℂ)) • (⇑(chi x y lam)) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, chi,
      MonoidHom.coe_mk, OneHom.coe_mk]
    exact h (Multiplicative.toAdd m)
  intro lam hlam
  have := linearIndependent_iff'.mp hli (SX.box d L) (fun lam => (p lam : ℂ)) hzero lam hlam
  exact_mod_cast this

end SixExponentials.SX

/- ===== SixExponentials/Basic/exists_aux_expSum.lean ===== -/
/-
Origin: `Diaz/Mirror/exists_aux_expSum.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `SX.exists_aux_expSum`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/SX.exists_aux_expSum__0dbfc434.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
Names and spellings that changed between the platform's Mathlib revision and the one
pinned here were updated to match, and proof steps that became no-ops there were
dropped; the mathematics is unchanged.
-/



namespace SixExponentials.SX

/-
# The auxiliary function of the six exponentials theorem

Let `K` be the number field containing the numbers `exp (x i * y j)`, and `n = [K : ℚ]`.
For each `M`, let `L` be least with `2 n M ^ l ≤ L ^ d`. We look for integers `p λ`, one for each
`λ` in the box `[0, L) ^ d`, not all zero, such that for every `m` in `[0, M) ^ l`
`∑_λ p λ ∏_{i,j} exp (x i * y j) ^ (λ i * m j) = 0`.
These are `M ^ l` linear equations in `L ^ d` unknowns, with coefficients in `K`.

A common denominator `b` of the numbers `exp (x i * y j)` makes each coefficient
`b ^ T ∏ exp (x i * y j) ^ (λ i * m j)`, with `T = d l L M`, an algebraic integer of house at most
`H ^ T`. Written in an integral basis of `K`, each equation becomes `n` equations over `ℤ` whose
entries are bounded by a constant times `H ^ T`, and there are still at least twice as many
unknowns as equations. Siegel's lemma gives a nonzero exists_aux_expSum of size at most `L ^ d` times that
bound, which is `exp (O (L M))`. Finally
`exp (⟨λ, x⟩ ∑_j m j y j) = ∏_{i,j} exp (x i * y j) ^ (λ i * m j)`,
so the equations say that the exponential sum `SX.expSum x L p` vanishes at `SX.latticeSum y m`.
-/

open Complex

namespace AuxSiegel

open NumberField Transcendence

/-- Siegel's lemma over a number field, with rational integer unknowns. A system of linear
equations with algebraic integer coefficients of house at most `A`, with at least `2 [K : ℚ]`
times as many unknowns as equations, has a nonzero integer exists_aux_expSum whose entries are at most
the number of unknowns times `max 1 (c_K A)`. The constant `c_K` is `[K : ℚ]` times the largest
entry of the inverse transpose of the matrix `(σ ω)`, `σ` running over the complex embeddings and
`ω` over an integral basis: it bounds the integer coordinates of an algebraic integer by its
house. The proof writes each equation in that basis and applies Siegel's lemma over `ℤ`. -/
theorem exists_int_kernel {K : Type*} [Field K] [NumberField K] [DecidableEq (K →+* ℂ)]
    {ρ κ : Type*} [Fintype ρ] [Fintype κ] (a : ρ → κ → K) (ha : ∀ k l, IsIntegral ℤ (a k l))
    {A : ℝ} (hA : ∀ k l, house (a k l) ≤ A) (hκ : 0 < Fintype.card κ)
    (hcard : 2 * (Fintype.card ρ * Module.finrank ℚ K) ≤ Fintype.card κ) :
    ∃ t : κ → ℤ, t ≠ 0 ∧ (∀ k, ∑ l, (t l : K) * a k l = 0) ∧
      ∀ l, |(t l : ℝ)| ≤ Fintype.card κ *
        max 1 (Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * A) := by
  classical
  set c : ℝ := Module.finrank ℚ K * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ with hc
  set bas := (RingOfIntegers.basis K).reindex (equivReindex K).symm with hbas
  -- the integer coordinates of an algebraic integer are bounded by `c` times its house
  have hrepr : ∀ (x : 𝓞 K) r, |((bas.repr x r : ℤ) : ℝ)| ≤ c * house (algebraMap (𝓞 K) K x) := by
    intro x r
    have h := house.basis_repr_norm_le_const_mul_house K x r
    simp only [Module.Basis.repr_reindex_apply, integralBasis_repr_apply,
      eq_intCast, Rat.cast_intCast, Complex.norm_intCast] at h
    simp only [hbas, Module.Basis.repr_reindex_apply]
    exact_mod_cast h
  have hc0 : 0 ≤ c := by positivity
  let a' : ρ → κ → 𝓞 K := fun k l => ⟨a k l, ha k l⟩
  -- one equation over `ℤ` for each equation and each coordinate
  obtain ⟨t, ht0, hker, hbd⟩ := siegel_entrywise
    (fun (kr : ρ × (K →+* ℂ)) l => bas.repr (a' kr.1 l) kr.2) hκ
    (by rw [Fintype.card_prod, Embeddings.card]; exact hcard) (le_max_left 1 (c * A))
    (fun kr l => (hrepr _ _).trans <|
      (mul_le_mul_of_nonneg_left (hA _ _) hc0).trans (le_max_right _ _))
  refine ⟨t, ht0, fun k => ?_, hbd⟩
  -- each equation holds coordinatewise, hence in `𝓞 K`, hence in `K`
  have h0 : bas.repr (∑ l, t l • a' k l) = 0 := by
    ext r
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    rw [← hker (k, r)]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h1 := congrArg (algebraMap (𝓞 K) K) (bas.repr.map_eq_zero_iff.mp h0)
  rw [map_sum, map_zero] at h1
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h1
  rw [map_zsmul, zsmul_eq_mul]; rfl

end AuxSiegel

open NumberField Transcendence AuxSiegel in
open SX in
theorem exists_aux_expSum
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l ∧
        ∃ p : (Fin d → ℕ) → ℤ,
          (∃ lam ∈ SX.box d L, p lam ≠ 0) ∧
          (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) ∧
          (∀ m : Fin l → ℕ, (∀ j, m j < M) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  have : NumberField K := ⟨⟩
  obtain ⟨hd, hl⟩ : 0 < d ∧ 0 < l := by
    constructor <;> (apply Nat.pos_of_ne_zero; rintro rfl; simp at hdl)
  set n := Module.finrank ℚ K with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  -- the numbers `exp (x i * y j)` in `K`: a denominator `b` and a house bound `H` for monomials
  set V : K →+* ℂ := (IntermediateField.val K).toRingHom
  set θ : Fin d × Fin l → K := fun ij => ⟨Complex.exp (x ij.1 * y ij.2), hK ij.1 ij.2⟩
  obtain ⟨b, hb0, -, H, hH1, hbH⟩ := exists_denom_house_monomial_le θ
  -- the constant of Siegel's lemma over `K`, and the constant `c`
  set W : ℝ := max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖)
  have hWH : 1 ≤ W * H := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hH1
  have hlog : 0 ≤ Real.log (W * H) := Real.log_nonneg hWH
  set c : ℝ := 2 ^ d * (2 * n) + d + d * l * Real.log (W * H) with hc
  refine ⟨c, by positivity, 1, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- `L` is least with `2 n M ^ l ≤ L ^ d`
  have hex : ∃ L : ℕ, 2 * n * M ^ l ≤ L ^ d := ⟨2 * n * M ^ l, Nat.le_self_pow hd.ne' _⟩
  set L := Nat.find hex
  have hL : 2 * n * M ^ l ≤ L ^ d := Nat.find_spec hex
  have hMl : 1 ≤ M ^ l := Nat.one_le_pow _ _ hM
  have hL0 : 0 < L := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_pow hd.ne'] at hL; nlinarith
  have hLub : L ^ d ≤ 2 ^ d * (2 * n * M ^ l) := by
    rcases Nat.lt_or_ge L 2 with h | h
    · rw [show L = 1 by omega, one_pow]
      exact le_trans (by nlinarith) (Nat.le_mul_of_pos_left _ (by positivity))
    · have hmin : ¬ 2 * n * M ^ l ≤ (L - 1) ^ d := Nat.find_min hex (by omega)
      calc L ^ d ≤ (2 * (L - 1)) ^ d := Nat.pow_le_pow_left (by omega) d
        _ = 2 ^ d * (L - 1) ^ d := mul_pow _ _ _
        _ ≤ 2 ^ d * (2 * n * M ^ l) := Nat.mul_le_mul_left _ (by omega)
  have hLc : (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l := by
    have h1 : ((L ^ d : ℕ) : ℝ) ≤ ((2 ^ d * (2 * n * M ^ l) : ℕ) : ℝ) := by exact_mod_cast hLub
    push_cast at h1
    calc (L : ℝ) ^ d ≤ 2 ^ d * (2 * n) * (M : ℝ) ^ l := by linarith
      _ ≤ c * (M : ℝ) ^ l := by
        gcongr; rw [hc]; have := mul_nonneg (by positivity : (0 : ℝ) ≤ d * l) hlog; linarith
  -- the system: one equation for each `m`, one unknown for each `λ` in the box
  set T := d * l * L * M with hT
  have hE : ∀ (m : Fin l → Fin M) (lam : ↥(SX.box d L)),
      ∑ ij : Fin d × Fin l, lam.1 ij.1 * (m ij.2 : ℕ) ≤ T := fun m lam => by
    calc _ ≤ ∑ _ij : Fin d × Fin l, L * M := Finset.sum_le_sum fun ij _ =>
          Nat.mul_le_mul (SX.mem_box.1 lam.2 ij.1).le (m ij.2).2.le
      _ = T := by simp [hT, Fintype.card_prod]; ring
  have hcardρ : Fintype.card (Fin l → Fin M) = M ^ l := by simp
  have hcardκ : Fintype.card ↥(SX.box d L) = L ^ d := by
    rw [Fintype.card_coe]; simp [SX.box]
  obtain ⟨t, ht0, hker, hbd⟩ := exists_int_kernel
    (fun (m : Fin l → Fin M) (lam : ↥(SX.box d L)) =>
      b ^ T * ∏ ij : Fin d × Fin l, θ ij ^ (lam.1 ij.1 * (m ij.2 : ℕ)))
    (fun m lam => (hbH _ T (hE m lam)).1) (fun m lam => (hbH _ T (hE m lam)).2)
    (by rw [hcardκ]; positivity) (by rw [hcardρ, hcardκ, ← hn]; linarith [hL])
  -- the height: `L ^ d max 1 (c_K H ^ T) ≤ exp (d L) (W H) ^ T ≤ exp (c L M)`
  have hT1 : T ≠ 0 := by positivity
  have hheight : ∀ lam, |(t lam : ℝ)| ≤ Real.exp (c * L * M) := by
    intro lam
    refine (hbd lam).trans ?_
    rw [hcardκ, ← hn]
    push_cast
    have h1 : max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ (W * H) ^ T := by
      rw [mul_pow]
      refine max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _))
        (one_le_pow₀ hH1)) ?_
      exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans
        (le_self_pow₀ (le_max_left _ _) hT1)) (by positivity)
    have h2 : (L : ℝ) ^ d ≤ Real.exp (d * L) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith [Real.add_one_le_exp (L : ℝ)]) d
    have h3 : (W * H) ^ T = Real.exp (T * Real.log (W * H)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have h4 : (d : ℝ) * L + T * Real.log (W * H) ≤ c * L * M := by
      have hL1 : (0 : ℝ) ≤ L := L.cast_nonneg
      have h5 : (d : ℝ) * L ≤ d * L * M := le_mul_of_one_le_right (by positivity) hM1
      have h6 : (0 : ℝ) ≤ 2 ^ d * (2 * n) * L * M := by positivity
      rw [hc, hT]; push_cast; nlinarith
    calc (L : ℝ) ^ d * max 1 ((n : ℝ) * ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖ * H ^ T)
        ≤ Real.exp (d * L) * Real.exp (T * Real.log (W * H)) :=
          h3 ▸ mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ Real.exp (c * L * M) := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 h4
  -- `p` is `t` on the box and zero outside it
  set p : (Fin d → ℕ) → ℤ := fun lam => if h : lam ∈ SX.box d L then t ⟨lam, h⟩ else 0
  have hpt : ∀ lam : ↥(SX.box d L), p lam.1 = t lam := fun lam => dif_pos lam.2
  refine ⟨L, hL0, hLc, p, ?_, fun lam => ?_, fun m hm => ?_⟩
  · obtain ⟨lam, hlam⟩ := Function.ne_iff.1 ht0
    exact ⟨lam.1, lam.2, by rw [hpt]; simpa using hlam⟩
  · by_cases h : lam ∈ SX.box d L
    · simpa only [hpt ⟨lam, h⟩] using hheight ⟨lam, h⟩
    · rw [show p lam = 0 from dif_neg h, Int.cast_zero, abs_zero]; exact (Real.exp_pos _).le
  · -- the equation of index `m`, divided by `b ^ T` and read in `ℂ`
    have h2 : ∑ lam : ↥(SX.box d L), (t lam : K) * ∏ ij : Fin d × Fin l,
        θ ij ^ (lam.1 ij.1 * m ij.2) = 0 := by
      have h1 := hker (fun j => ⟨m j, hm j⟩)
      simp_rw [mul_left_comm _ (b ^ T), ← Finset.mul_sum] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hb0)
    have h3 := congrArg V h2
    simp only [map_sum, map_mul, map_intCast, map_prod, map_pow, map_zero] at h3
    rw [SX.expSum, ← Finset.sum_coe_sort (SX.box d L)]
    refine Eq.trans (Finset.sum_congr rfl fun lam _ => ?_) h3
    rw [hpt, SX.exp_expExponent_mul_latticeSum, Fintype.prod_prod_type]
    rfl

end SixExponentials.SX

/- ===== SixExponentials/Basic/six_exponentials_of_numberField.lean ===== -/
/-
Origin: `Diaz/Mirror/six_exponentials_of_numberField.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `SX.six_exponentials_of_numberField`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/SX.six_exponentials_of_numberField__e54a15db.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
-/



namespace SixExponentials.SX

/- # Assembly check: rung 2 from rungs 3, 4, 5.  Must contain no `sorry`. -/

open Complex

theorem six_exponentials_of_numberField
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    ∃ i j, Complex.exp (x i * y j) ∉ K := by
  classical
  have hl2 : 2 ≤ l := by
    by_contra hcl
    push_neg at hcl
    interval_cases l <;> omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc, M₁, haux⟩ := SX.exists_aux_expSum hdl x y hx hy K hcon
  obtain ⟨M₀, hdesc⟩ := SX.descent_step hdl x y hx hy K hcon c hc
  set M : ℕ := max M₀ M₁ + 1 with hMdef
  obtain ⟨L, hL0, hLc, p, ⟨lam0, hlam0mem, hlam0⟩, hph, hvan⟩ :=
    haux M (by omega)
  have key : ∀ N : ℕ, M ≤ N →
      ∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hvan
    | succ N hN ih => exact hdesc M (by omega) L hL0 hLc p hph N hN ih
  have hall : ∀ m : Fin l → ℕ, SX.expSum x L p (SX.latticeSum y m) = 0 := by
    intro m
    refine key (max M (Finset.univ.sup m + 1)) (le_max_left _ _) m fun j => ?_
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j)))
      (le_max_right _ _)
  exact hlam0 (SX.eq_zero_of_expSum_vanishes hl2 x y hx hy L p hall lam0 hlam0mem)

end SixExponentials.SX

/- ===== SixExponentials/Basic/six_exponentials.lean ===== -/
/-
Origin: `Diaz/Mirror/six_exponentials.lean` in https://github.com/carlok/diaz-modulus-lean
(commit edb9c5b92df0935ed6834e1d965fe9c18cfa21bb), Apache-2.0.

Copied verbatim except for what the Lean module system needs (`module`, `public import`,
`public section`) and the renames of the import paths and of the namespaces
`Diaz`, `SX`, `Transcendence` to `SixExponentials`, `SixExponentials.SX`,
`SixExponentials.Transcendence`. The header of the origin file follows; the paths it
names are in diaz-modulus-lean.

Mirrored from Prove2Me: `DiazModulus.six_exponentials`.

Ported mechanically from the accepted submission archived as
`archive/prove2me/DiazModulus.six_exponentials__b4ee3ac8.lean`. Statement and proof are the platform's; only
imports, namespaces and the theorem's name were rewritten.
Names and spellings that changed between the platform's Mathlib revision and the one
pinned here were updated to match, and proof steps that became no-ops there were
dropped; the mathematics is unchanged.
-/



namespace SixExponentials

/- # Assembly check: the target from rung 2.  Must contain no `sorry`. -/

open Complex ComplexConjugate

theorem six_exponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by
  classical
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  set S : Set ℂ := Set.range (fun q : Fin 2 × Fin 3 => Complex.exp (x q.1 * y q.2)) with hS
  have hSfin : S.Finite := Set.finite_range _
  have : Finite S := hSfin.to_subtype
  have hint : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨q, rfl⟩
    exact (hcon q.1 q.2).isIntegral
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  obtain ⟨i, j, hij⟩ :=
    SX.six_exponentials_of_numberField (d := 2) (l := 3) (by omega) x y hx hy
      (IntermediateField.adjoin ℚ S)
  exact hij (IntermediateField.subset_adjoin ℚ S ⟨(i, j), rfl⟩)

end SixExponentials

/- ===== CARatiosFC/SixExpPrimes.lean ===== -/

/-
# Three primes cannot share a non-integral rational-valued exponent (six exponentials)

`CARatiosFC.int_of_three_primes_rpow_rat`: if `p, q, r` are distinct primes and `x : ℝ` makes `p^x`, `q^x`, `r^x`
all rational, then `x ∈ ℤ`. This is the corollary of the six exponentials theorem (Lang 1966, Ramachandra 1968)
used by Alaoglu and Erdős (1944, p. 455, there credited to Siegel for prime bases).

* If `x ∉ ℚ`, then `(1, x)` and `(log p, log q, log r)` are each ℚ-linearly independent, so by
  `SixExponentials.six_exponentials` one of `p, q, r, p^x, q^x, r^x` is transcendental: none is.
* If `x = s ∈ ℚ` and `p^s = a ∈ ℚ`, then `a^(den s) = p^(num s)`, so taking `p`-adic valuations
  `num s = den s · v_p(a)` and `s = v_p(a) ∈ ℤ`.

The six exponentials theorem is used as vendored from carlok/six-exponentials-lean (see `vendor/SOURCE.txt`).
-/

open Real

namespace CARatiosFC

/-- `p`-adic valuation of a product of integer powers of primes. -/
private lemma padicValRat_prime_zpow_self {p : ℕ} (hp : p.Prime) (n : ℤ) :
    haveI := Fact.mk hp
    padicValRat p ((p : ℚ) ^ n) = n := by
  have := Fact.mk hp
  rw [padicValRat.zpow, padicValRat.self hp.one_lt, mul_one]

private lemma padicValRat_prime_zpow_other {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℤ) :
    haveI := Fact.mk hp
    padicValRat p ((q : ℚ) ^ n) = 0 := by
  have := Fact.mk hp
  rw [padicValRat.zpow, padicValRat.of_nat, mul_eq_zero]
  right
  have : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  simp [padicValNat.eq_zero_of_not_dvd this]

/-- Integer relation `n₀ log p + n₁ log q + n₂ log r = 0` between distinct primes forces `n₀ = 0`. -/
lemma int_log_rel_first {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) {n₀ n₁ n₂ : ℤ}
    (h : (n₀ : ℝ) * Real.log p + n₁ * Real.log q + n₂ * Real.log r = 0) : n₀ = 0 := by
  have := Fact.mk hp
  set Q : ℚ := (p : ℚ) ^ n₀ * (q : ℚ) ^ n₁ * (r : ℚ) ^ n₂ with hQ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hz : ∀ (a : ℕ) (n : ℤ), (0 : ℝ) < a → ((a : ℝ) ^ n) = Real.exp (n * Real.log a) := by
    intro a n ha
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos ha, mul_comm]
  have hQ1 : (Q : ℝ) = 1 := by
    rw [hQ]
    push_cast
    rw [hz p n₀ hp0, hz q n₁ hq0, hz r n₂ hr0, ← Real.exp_add, ← Real.exp_add, h, Real.exp_zero]
  have hQ1' : Q = 1 := by exact_mod_cast hQ1
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hrne : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hv : padicValRat p Q = n₀ := by
    rw [hQ, padicValRat.mul (mul_ne_zero (zpow_ne_zero _ hpne) (zpow_ne_zero _ hqne)) (zpow_ne_zero _ hrne),
      padicValRat.mul (zpow_ne_zero _ hpne) (zpow_ne_zero _ hqne),
      padicValRat_prime_zpow_self hp, padicValRat_prime_zpow_other hp hq hpq,
      padicValRat_prime_zpow_other hp hr hpr]
    ring
  rw [hQ1', padicValRat.one] at hv
  exact hv.symm

/-- The logarithms of three distinct primes are linearly independent over `ℚ` (as complex numbers). -/
lemma linearIndependent_log_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    LinearIndependent ℚ ![((Real.log p : ℝ) : ℂ), ((Real.log q : ℝ) : ℂ), ((Real.log r : ℝ) : ℂ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Rat.smul_def] at hg
  have hreal : ((g 0 : ℝ) * Real.log p + (g 1 : ℝ) * Real.log q + (g 2 : ℝ) * Real.log r) = 0 := by
    have h' := congrArg Complex.re hg
    simp only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] at h'
    exact h'
  -- clear denominators
  set d : ℕ := (g 0).den * (g 1).den * (g 2).den with hd
  have hdpos : (0 : ℚ) < d := by
    rw [hd]; push_cast; positivity
  have hint : ∀ a : ℚ, a.den ∣ d → ∃ n : ℤ, a * d = n := by
    intro a hdvd
    refine ⟨(a * d).num, ?_⟩
    have hden : (a * d).den = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk]; push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num, ← Int.cast_natCast k, ← Int.cast_mul]
      exact Rat.den_intCast _
    exact (Rat.coe_int_num_of_den_eq_one hden).symm
  obtain ⟨n₀, h₀⟩ := hint (g 0) (Dvd.intro ((g 1).den * (g 2).den) (by rw [hd]; ring))
  obtain ⟨n₁, h₁⟩ := hint (g 1) (Dvd.intro ((g 0).den * (g 2).den) (by rw [hd]; ring))
  obtain ⟨n₂, h₂⟩ := hint (g 2) (Dvd.intro_left _ (by rw [hd]))
  have hrel : (n₀ : ℝ) * Real.log p + n₁ * Real.log q + n₂ * Real.log r = 0 := by
    have e₀ : (n₀ : ℝ) = (g 0 : ℝ) * d := by exact_mod_cast h₀.symm
    have e₁ : (n₁ : ℝ) = (g 1 : ℝ) * d := by exact_mod_cast h₁.symm
    have e₂ : (n₂ : ℝ) = (g 2 : ℝ) * d := by exact_mod_cast h₂.symm
    rw [e₀, e₁, e₂]
    linear_combination (d : ℝ) * hreal
  have z₀ : n₀ = 0 := int_log_rel_first hp hq hr hpq hpr hrel
  have z₁ : n₁ = 0 := int_log_rel_first (n₀ := n₁) (n₁ := n₀) (n₂ := n₂) hq hp hr hpq.symm hqr (by linear_combination hrel)
  have z₂ : n₂ = 0 := int_log_rel_first (n₀ := n₂) (n₁ := n₀) (n₂ := n₁) hr hp hq hpr.symm hqr.symm (by linear_combination hrel)
  have hdne : (d : ℚ) ≠ 0 := hdpos.ne'
  intro i
  fin_cases i
  · simpa [z₀, hdne] using h₀
  · simpa [z₁, hdne] using h₁
  · simpa [z₂, hdne] using h₂

/-- If `p^s` is rational for a prime `p` and a rational `s`, then `s` is an integer. -/
lemma int_of_rat_rpow_rat {p : ℕ} (hp : p.Prime) {s : ℚ} {a : ℚ} (ha : (p : ℝ) ^ (s : ℝ) = a) :
    ∃ k : ℤ, (s : ℝ) = k := by
  have := Fact.mk hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hapos : (0 : ℝ) < a := ha ▸ Real.rpow_pos_of_pos hp0 _
  have hane : a ≠ 0 := by
    intro h; rw [h] at hapos; simp at hapos
  -- a ^ den = p ^ num
  have key : (a : ℝ) ^ s.den = (p : ℝ) ^ s.num := by
    rw [← ha, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_intCast]
    congr 1
    have := Rat.mul_den_eq_num s
    exact_mod_cast this
  have keyQ : a ^ s.den = (p : ℚ) ^ s.num := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact key
  have hv := congrArg (padicValRat p) keyQ
  rw [padicValRat.pow, padicValRat_prime_zpow_self hp] at hv
  refine ⟨padicValRat p a, ?_⟩
  have hden : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hs : (s : ℝ) = (s.num : ℝ) / s.den := by exact_mod_cast (Rat.num_div_den s).symm
  rw [hs, ← hv]
  push_cast
  field_simp

private lemma isAlgebraic_of_eq_rat {z : ℂ} {a : ℚ} (h : z = (a : ℂ)) : IsAlgebraic ℚ z := by
  rw [h]
  exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) a

/-- **Three primes and a rational-valued exponent** (six exponentials theorem): if `p, q, r` are distinct primes
and `p^x, q^x, r^x` are all rational, then `x` is an integer. -/
theorem int_of_three_primes_rpow_rat {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {x : ℝ}
    (hxp : ∃ a : ℚ, (p : ℝ) ^ x = a) (hxq : ∃ b : ℚ, (q : ℝ) ^ x = b)
    (hxr : ∃ c : ℚ, (r : ℝ) ^ x = c) :
    ∃ k : ℤ, x = k := by
  obtain ⟨a, ha⟩ := hxp
  by_cases hrat : ∃ s : ℚ, x = s
  · obtain ⟨s, rfl⟩ := hrat
    exact int_of_rat_rpow_rat hp ha
  exfalso
  push Not at hrat
  obtain ⟨b, hb⟩ := hxq
  obtain ⟨c, hc⟩ := hxr
  have hx : LinearIndependent ℚ ![(1 : ℂ), (x : ℂ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Rat.smul_def, mul_one] at hst
    have hre := congrArg Complex.re hst
    simp at hre
    by_cases ht : t = 0
    · subst ht; simpa using hre
    · exfalso
      apply hrat (-s / t)
      have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linarith
  have hy := linearIndependent_log_three_primes hp hq hr hpq hpr hqr
  obtain ⟨i, j, hT⟩ := SixExponentials.six_exponentials _ _ hx hy
  apply hT
  have e1 : ∀ m : ℕ, 0 < m → Complex.exp (1 * ((Real.log m : ℝ) : ℂ)) = ((m : ℚ) : ℂ) := by
    intro m hm
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hm)]
    push_cast; rfl
  have ex : ∀ (m : ℕ) (e : ℚ), 0 < m → (m : ℝ) ^ x = e →
      Complex.exp ((x : ℂ) * ((Real.log m : ℝ) : ℂ)) = (e : ℂ) := by
    intro m e hm he
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm, ← Real.rpow_def_of_pos (by exact_mod_cast hm), he]
    push_cast; rfl
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact isAlgebraic_of_eq_rat (e1 p hp.pos)
  · exact isAlgebraic_of_eq_rat (e1 q hq.pos)
  · exact isAlgebraic_of_eq_rat (e1 r hr.pos)
  · exact isAlgebraic_of_eq_rat (ex p a hp.pos ha)
  · exact isAlgebraic_of_eq_rat (ex q b hq.pos hb)
  · exact isAlgebraic_of_eq_rat (ex r c hr.pos hc)

end CARatiosFC

/- ===== CARatiosFC/Local.lean ===== -/

/-
# R2: structure of the maximizers of `σ(n)/n^(1+ε)` for a fixed `ε > 0`

Write `g ε n = σ(n) / n^(1+ε)` (`gEps`). This file proves, unconditionally and for every real `ε > 0`:

1. `gEps_mul_of_coprime`, `gEps_eq_prod`: `g ε` is multiplicative and
   `g ε n = ∏ p ∈ P, g ε (p ^ v_p(n))` for any finite `P ⊇ n.primeFactors`.
2. Per prime `p`: `g ε (p^(a+1)) - g ε (p^a) = (1 - δ·σ(p^a)) / c^(a+1)` with `c = p^(1+ε)`, `δ = c - p > 0`
   (`gEps_succ_sub`). Since `σ(p^a)` is strictly increasing, `a ↦ g ε (p^a)` rises strictly up to
   `A = topExp ε p = min {a | 1 ≤ δ σ(p^a)}`, then falls strictly from `A + 1`. Hence (`isMaxExp_iff`) the exponents
   maximizing `g ε (p^·)` are exactly `A`, plus `A + 1` iff `Tie ε p : δ·σ(p^A) = 1`.
   A tie forces `p^ε ∈ ℚ` (`tie_rpow_rat`) and `ε < 1` (`tie_lt_one`). If `p^(1+ε) > p + 1` the only maximizing
   exponent is `0` (`isMaxExp_iff_of_large`).
3. `isMaxG_iff`: `n ≥ 1` maximizes `g ε` over `n ≥ 1` iff every exponent `v_p(n)` maximizes `g ε (p^·)`.
4. `not_three_ties` (six exponentials, via `int_of_three_primes_rpow_rat`): no three distinct primes tie, so
   `encard_maximizers_le_four`: `{n | n maximizes g ε over n ≥ 1}.encard ≤ 4`.

The mathematics is Alaoglu–Erdős (1944, §§3–4); the six exponentials theorem is Lang–Ramachandra's.
-/

open scoped ArithmeticFunction.sigma
open Real

namespace CARatiosFC

/-- `g ε n = σ(n) / n^(1+ε)`, the quantity in formal-conjectures' colossally abundant definitions. -/
noncomputable def gEps (ε : ℝ) (n : ℕ) : ℝ := (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)

lemma gEps_one (ε : ℝ) : gEps ε 1 = 1 := by simp [gEps]

lemma gEps_mul_of_coprime (ε : ℝ) {m n : ℕ} (h : m.Coprime n) :
    gEps ε (m * n) = gEps ε m * gEps ε n := by
  unfold gEps
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_div_mul_comm]

lemma gEps_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ gEps ε n := by
  unfold gEps; positivity

lemma gEps_pos (ε : ℝ) {n : ℕ} (hn : n ≠ 0) : 0 < gEps ε n := by
  unfold gEps
  have h1 : 0 < σ 1 n := ArithmeticFunction.sigma_pos 1 n hn
  have h1' : (0 : ℝ) < σ 1 n := by exact_mod_cast h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have := Real.rpow_pos_of_pos hn' (1 + ε)
  positivity

/-- Euler product of `g ε` over any finite set of primes containing the prime factors. -/
lemma gEps_eq_prod (ε : ℝ) {n : ℕ} (hn : n ≠ 0) {P : Finset ℕ} (hP : n.primeFactors ⊆ P) :
    gEps ε n = ∏ p ∈ P, gEps ε (p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization (gEps ε) (fun x y h => gEps_mul_of_coprime ε h) (gEps_one ε) hn]
  exact Finsupp.prod_of_support_subset _ (by rwa [Nat.support_factorization]) _
    (fun p _ => by simp [gEps_one])

/- ## One prime -/

/-- `σ(p^a)` as a real number. -/
noncomputable def sig (p a : ℕ) : ℝ := (σ 1 (p ^ a) : ℝ)

lemma sigma_prime_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ (a + 1)) = p * σ 1 (p ^ a) + 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, ArithmeticFunction.sigma_one_apply_prime_pow hp,
    Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma sig_zero (p : ℕ) : sig p 0 = 1 := by simp [sig]

lemma sig_succ {p : ℕ} (hp : p.Prime) (a : ℕ) : sig p (a + 1) = p * sig p a + 1 := by
  unfold sig; rw [sigma_prime_pow_succ hp]; push_cast; ring

lemma sig_nonneg (p a : ℕ) : 0 ≤ sig p a := by unfold sig; positivity

lemma sig_ge {p : ℕ} (hp : p.Prime) : ∀ a : ℕ, (a : ℝ) + 1 ≤ sig p a
  | 0 => by simp [sig_zero]
  | a + 1 => by
    have ih := sig_ge hp a
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    rw [sig_succ hp]; push_cast
    nlinarith [sig_nonneg p a]

lemma sig_pos {p : ℕ} (hp : p.Prime) (a : ℕ) : 0 < sig p a := by
  have := sig_ge hp a; have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith

lemma sig_strictMono {p : ℕ} (hp : p.Prime) : StrictMono (sig p) := by
  refine strictMono_nat_of_lt_succ fun a => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  rw [sig_succ hp]; nlinarith [sig_nonneg p a]

lemma gEps_prime_pow (ε : ℝ) (p a : ℕ) : gEps ε (p ^ a) = sig p a / ((p : ℝ) ^ (1 + ε)) ^ a := by
  unfold gEps sig
  push_cast
  rw [Real.rpow_pow_comm (Nat.cast_nonneg p)]

/-- `c = p^(1+ε)` and `δ = c - p`. -/
noncomputable def delta (ε : ℝ) (p : ℕ) : ℝ := (p : ℝ) ^ (1 + ε) - p

lemma delta_pos {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) : 0 < delta ε p := by
  unfold delta
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have := Real.rpow_lt_rpow_of_exponent_lt hp1 (show (1 : ℝ) < 1 + ε by linarith)
  rw [Real.rpow_one] at this
  linarith

lemma gEps_succ_sub (ε : ℝ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    gEps ε (p ^ (a + 1)) - gEps ε (p ^ a) =
      (1 - delta ε p * sig p a) / ((p : ℝ) ^ (1 + ε)) ^ (a + 1) := by
  rw [gEps_prime_pow, gEps_prime_pow, sig_succ hp]
  have hc : 0 < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  unfold delta
  field_simp
  ring

/-- The largest exponent at which `a ↦ g ε (p^a)` is still rising: `min {a | 1 ≤ δ σ(p^a)}`. -/
noncomputable def topExp (ε : ℝ) (p : ℕ) : ℕ := sInf {a : ℕ | 1 ≤ delta ε p * sig p a}

/-- `p` ties: two consecutive exponents both maximize `g ε (p^·)`. -/
def Tie (ε : ℝ) (p : ℕ) : Prop := delta ε p * sig p (topExp ε p) = 1

lemma topExp_set_nonempty {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    {a : ℕ | 1 ≤ delta ε p * sig p a}.Nonempty := by
  have hδ := delta_pos hε hp
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / delta ε p)
  refine ⟨n, ?_⟩
  have h1 : 1 < n * delta ε p := (div_lt_iff₀ hδ).mp hn
  have h2 := sig_ge hp n
  show 1 ≤ delta ε p * sig p n
  nlinarith

lemma one_le_topExp {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    1 ≤ delta ε p * sig p (topExp ε p) :=
  Nat.sInf_mem (topExp_set_nonempty hε hp)

lemma lt_one_of_lt_topExp {ε : ℝ} {p a : ℕ} (h : a < topExp ε p) : delta ε p * sig p a < 1 :=
  not_le.mp (Nat.notMem_of_lt_sInf h)

/-- Exponents maximizing `g ε (p^·)`. -/
def IsMaxExp (ε : ℝ) (p a : ℕ) : Prop := ∀ b : ℕ, gEps ε (p ^ b) ≤ gEps ε (p ^ a)

/-- Per-prime argmax: `{A}` or, exactly when `p` ties, `{A, A + 1}`. -/
theorem isMaxExp_iff {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    IsMaxExp ε p a ↔ a = topExp ε p ∨ (Tie ε p ∧ a = topExp ε p + 1) := by
  set A := topExp ε p with hAdef
  set f : ℕ → ℝ := fun b => gEps ε (p ^ b) with hf
  have hδ := delta_pos hε hp
  have hc : 0 < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have hden : ∀ k : ℕ, 0 < ((p : ℝ) ^ (1 + ε)) ^ (k + 1) := fun k => pow_pos hc _
  have hdiff : ∀ k, f (k + 1) - f k = (1 - delta ε p * sig p k) / ((p : ℝ) ^ (1 + ε)) ^ (k + 1) :=
    fun k => gEps_succ_sub ε hp k
  have up : ∀ k, k < A → f k < f (k + 1) := by
    intro k hk
    have h1 := lt_one_of_lt_topExp hk
    have : 0 < f (k + 1) - f k := by rw [hdiff]; exact div_pos (by linarith) (hden k)
    linarith
  have down : ∀ k, A + 1 ≤ k → f (k + 1) < f k := by
    intro k hk
    have h1 := one_le_topExp hε hp
    have h2 : sig p A < sig p k := sig_strictMono hp (by omega)
    have h3 : 1 < delta ε p * sig p k := by nlinarith
    have : f (k + 1) - f k < 0 := by rw [hdiff]; exact div_neg_of_neg_of_pos (by linarith) (hden k)
    linarith
  have step_le : f (A + 1) ≤ f A := by
    have h1 := one_le_topExp hε hp
    have : f (A + 1) - f A ≤ 0 := by rw [hdiff]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (hden A).le
    linarith
  have step_eq : f (A + 1) = f A ↔ Tie ε p := by
    have e := hdiff A
    constructor
    · intro h
      rw [h, sub_self] at e
      have := (div_eq_zero_iff.mp e.symm).resolve_right (hden A).ne'
      show delta ε p * sig p A = 1
      linarith
    · intro h
      have h' : delta ε p * sig p A = 1 := h
      rw [h', sub_self, zero_div, sub_eq_zero] at e
      exact e
  have up_chain : ∀ d b, b + d < A → f b < f (b + d + 1) := by
    intro d
    induction d with
    | zero => intro b hb; simpa using up b (by omega)
    | succ d ih =>
      intro b hb
      have h1 := ih b (by omega)
      have h2 := up (b + d + 1) (by omega)
      have e : b + (d + 1) + 1 = b + d + 1 + 1 := by ring
      rw [e]; linarith
  have below : ∀ b, b < A → f b < f A := by
    intro b hb
    have := up_chain (A - b - 1) b (by omega)
    have e : b + (A - b - 1) + 1 = A := by omega
    rwa [e] at this
  have down_chain : ∀ d, f (A + 1 + d + 1) < f (A + 1) := by
    intro d
    induction d with
    | zero => simpa using down (A + 1) le_rfl
    | succ d ih =>
      have h2 := down (A + 1 + d + 1) (by omega)
      have e : A + 1 + (d + 1) + 1 = A + 1 + d + 1 + 1 := by ring
      rw [e]; linarith
  have above : ∀ b, A + 1 < b → f b < f (A + 1) := by
    intro b hb
    have := down_chain (b - A - 2)
    have e : A + 1 + (b - A - 2) + 1 = b := by omega
    rwa [e] at this
  have hAmax : ∀ b, f b ≤ f A := by
    intro b
    rcases lt_trichotomy b A with h | h | h
    · exact (below b h).le
    · rw [h]
    · rcases Nat.lt_or_ge (A + 1) b with h' | h'
      · linarith [above b h']
      · have : b = A + 1 := by omega
        rw [this]; exact step_le
  constructor
  · intro hmax
    have hmax' : ∀ b, f b ≤ f a := hmax
    rcases lt_trichotomy a A with h | h | h
    · linarith [below a h, hmax' A]
    · exact Or.inl h
    · rcases Nat.lt_or_ge (A + 1) a with h' | h'
      · linarith [above a h', hmax' A]
      · have ha : a = A + 1 := by omega
        refine Or.inr ⟨step_eq.mp ?_, ha⟩
        rw [ha] at hmax'
        exact le_antisymm step_le (hmax' A)
  · rintro (h | ⟨ht, h⟩)
    · intro b; rw [h]; exact hAmax b
    · intro b
      show f b ≤ f a
      rw [h, step_eq.mpr ht]; exact hAmax b

/-- Large primes (`p^(1+ε) > p + 1`): the only maximizing exponent is `0`. -/
theorem isMaxExp_iff_of_large {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    (hlarge : (p : ℝ) + 1 < (p : ℝ) ^ (1 + ε)) (a : ℕ) : IsMaxExp ε p a ↔ a = 0 := by
  have hδ : 1 < delta ε p := by unfold delta; linarith
  have h0 : topExp ε p = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.sInf_le (show 1 ≤ delta ε p * sig p 0 by rw [sig_zero, mul_one]; exact hδ.le)
  have hnt : ¬ Tie ε p := by
    unfold Tie; rw [h0, sig_zero, mul_one]; exact hδ.ne'
  rw [isMaxExp_iff hε hp, h0]
  simp [hnt]

lemma tie_delta {ε : ℝ} {p : ℕ} (ht : Tie ε p) : (p : ℝ) ^ (1 + ε) = p + 1 / sig p (topExp ε p) := by
  have h : delta ε p * sig p (topExp ε p) = 1 := ht
  unfold delta at h
  have hs : sig p (topExp ε p) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  field_simp
  linarith

/-- A tie makes `p^ε` rational. -/
theorem tie_rpow_rat {ε : ℝ} {p : ℕ} (hp : p.Prime) (ht : Tie ε p) : ∃ x : ℚ, (p : ℝ) ^ ε = x := by
  have h := tie_delta ht
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.rpow_add hp0, Real.rpow_one] at h
  refine ⟨((p : ℚ) + 1 / (σ 1 (p ^ topExp ε p) : ℚ)) / p, ?_⟩
  push_cast
  unfold sig at h
  field_simp
  linarith

/-- A tie forces `ε < 1`. -/
theorem tie_lt_one {ε : ℝ} {p : ℕ} (hp : p.Prime) (ht : Tie ε p) : ε < 1 := by
  have h := tie_delta ht
  have hs1 : 1 ≤ sig p (topExp ε p) := by have := sig_ge hp (topExp ε p); have := Nat.cast_nonneg (α := ℝ) (topExp ε p); linarith
  have hinv : 1 / sig p (topExp ε p) ≤ 1 := by rw [div_le_one (by linarith)]; exact hs1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < p := by linarith
  have hlt : (p : ℝ) ^ (1 + ε) < (p : ℝ) ^ (2 : ℝ) := by
    rw [h, Real.rpow_two]; nlinarith
  have := (Real.rpow_lt_rpow_left_iff hp1).mp hlt
  linarith

/-- Six exponentials: no three distinct primes tie for the same `ε > 0`. -/
theorem not_three_ties {ε : ℝ} (hε : 0 < ε) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (tp : Tie ε p) (tq : Tie ε q) (tr : Tie ε r) : False := by
  obtain ⟨k, hk⟩ := int_of_three_primes_rpow_rat hp hq hr hpq hpr hqr
    (tie_rpow_rat hp tp) (tie_rpow_rat hq tq) (tie_rpow_rat hr tr)
  have h1 := tie_lt_one hp tp
  rw [hk] at hε h1
  have a : (0 : ℤ) < k := by exact_mod_cast hε
  have b : k < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- All tied primes lie in a set `{q, r}`. -/
theorem ties_subset_pair {ε : ℝ} (hε : 0 < ε) : ∃ q r : ℕ, ∀ p, p.Prime → Tie ε p → p = q ∨ p = r := by
  classical
  by_cases h1 : ∃ q, q.Prime ∧ Tie ε q
  · obtain ⟨q, hq, tq⟩ := h1
    by_cases h2 : ∃ r, r.Prime ∧ Tie ε r ∧ r ≠ q
    · obtain ⟨r, hr, tr, hrq⟩ := h2
      refine ⟨q, r, fun p hp tp => ?_⟩
      by_contra hne
      push Not at hne
      exact not_three_ties hε hq hr hp hrq.symm (Ne.symm hne.1) (Ne.symm hne.2) tq tr tp
    · refine ⟨q, q, fun p hp tp => Or.inl ?_⟩
      by_contra hne
      exact h2 ⟨p, hp, tp, hne⟩
  · exact ⟨0, 0, fun p hp tp => (h1 ⟨p, hp, tp⟩).elim⟩

/- ## Global maximizers -/

/-- `n ≥ 1` maximizes `g ε` over all `m ≥ 1`. -/
def IsMaxG (ε : ℝ) (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → gEps ε m ≤ gEps ε n

/-- Global argmax = product of the per-prime argmaxes. -/
theorem isMaxG_iff (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    IsMaxG ε n ↔ ∀ p, p.Prime → IsMaxExp ε p (n.factorization p) := by
  have hn0 : n ≠ 0 := by omega
  constructor
  · rintro ⟨-, hmax⟩ p hp b
    by_contra hlt
    push Not at hlt
    set a := n.factorization p
    set k := n / p ^ a with hk
    have hnk : p ^ a * k = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hk0 : k ≠ 0 := (Nat.ordCompl_pos p hn0).ne'
    have hcop : (p ^ b).Coprime k := (Nat.coprime_ordCompl hp hn0).pow_left b
    have hcop' : (p ^ a).Coprime k := (Nat.coprime_ordCompl hp hn0).pow_left a
    have hm : 1 ≤ p ^ b * k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hk0)
    have h1 := hmax _ hm
    rw [gEps_mul_of_coprime ε hcop, ← hnk, gEps_mul_of_coprime ε hcop'] at h1
    have := gEps_pos ε hk0
    nlinarith
  · intro h
    refine ⟨hn, fun m hm => ?_⟩
    have hm0 : m ≠ 0 := by omega
    rw [gEps_eq_prod ε hm0 (Finset.subset_union_left (s₂ := n.primeFactors)),
      gEps_eq_prod ε hn0 (Finset.subset_union_right (s₁ := m.primeFactors))]
    refine Finset.prod_le_prod (fun _ _ => gEps_nonneg _ _) fun p hp => ?_
    have hpp : p.Prime := by
      rcases Finset.mem_union.mp hp with h' | h' <;> exact Nat.prime_of_mem_primeFactors h'
    exact h p hpp _

/-- At most four `n ≥ 1` maximize `σ(n)/n^(1+ε)`, for every `ε > 0`. -/
theorem encard_maximizers_le_four {ε : ℝ} (hε : 0 < ε) : {n : ℕ | IsMaxG ε n}.encard ≤ 4 := by
  obtain ⟨q, r, hqr⟩ := ties_subset_pair hε
  set f : ℕ → Bool × Bool :=
    fun n => (decide (n.factorization q = topExp ε q), decide (n.factorization r = topExp ε r)) with hf
  have hinj : Set.InjOn f {n : ℕ | IsMaxG ε n} := by
    intro n hn n' hn' hfn
    have hn0 : n ≠ 0 := by have := hn.1; omega
    have hn0' : n' ≠ 0 := by have := hn'.1; omega
    have key : ∀ p, p.Prime → n.factorization p = n'.factorization p := by
      intro p hp
      have h1 := (isMaxExp_iff hε hp _).mp ((isMaxG_iff ε hn.1).mp hn p hp)
      have h2 := (isMaxExp_iff hε hp _).mp ((isMaxG_iff ε hn'.1).mp hn' p hp)
      by_cases ht : Tie ε p
      · have hsame : (n.factorization p = topExp ε p ↔ n'.factorization p = topExp ε p) := by
          rcases hqr p hp ht with rfl | rfl
          · have := congrArg Prod.fst hfn
            simpa [hf] using this
          · have := congrArg Prod.snd hfn
            simpa [hf] using this
        rcases h1 with h1 | ⟨-, h1⟩ <;> rcases h2 with h2 | ⟨-, h2⟩
        · omega
        · exact absurd (hsame.mp h1) (by omega)
        · exact absurd (hsame.mpr h2) (by omega)
        · omega
      · simp only [ht, false_and, or_false] at h1 h2
        omega
    exact Nat.eq_of_factorization_eq hn0 hn0' fun p => by
      by_cases hp : p.Prime
      · exact key p hp
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  calc {n : ℕ | IsMaxG ε n}.encard = (f '' {n : ℕ | IsMaxG ε n}).encard := hinj.encard_image.symm
    _ ≤ (Set.univ : Set (Bool × Bool)).encard := Set.encard_le_encard (Set.subset_univ _)
    _ = 4 := by simp [Set.encard_univ]

end CARatiosFC

/- ===== CARatiosFC/Maximizers.lean ===== -/

/-
# R3: formal-conjectures' `encard_colossallyAbundant_maximizers_le_four`

formal-conjectures maximizes `g ε k = σ(k)/k^(1+ε)` over `k > 1`, R2 (`encard_maximizers_le_four`) over `k ≥ 1`.
Write `M₂` for FC's set `{n > 1 | ∀ k > 1, g ε k ≤ g ε n}`. Since `g ε 1 = 1`:

* if every `n ∈ M₂` has `g ε n ≥ 1`, each one also beats `k = 1`, so `M₂ ⊆ {n | IsMaxG ε n}` and R2 gives `≤ 4`;
* otherwise some `n₀ ∈ M₂` has `g ε n₀ < 1`, so `g ε 2 ≤ g ε n₀ < 1`, i.e. `3 < 2^(1+ε)`. Then every prime is
  large (`(p+1)/p^(1+ε) ≤ 3/2^(1+ε) < 1`), each `a ↦ g ε (p^a)` is strictly decreasing, and every `n > 1`, `n ≠ 2`
  has `g ε n < g ε 2` (`gEps_lt_gEps_two`). So `M₂ ⊆ {2}`.

The statement of `encard_colossallyAbundant_maximizers_le_four` is formal-conjectures' (commit `ea8e3e19`) verbatim;
`controls/ca_ratios_fc_fidelity.py` checks it. Unconditional, standard axioms.
-/

open scoped ArithmeticFunction.sigma

namespace CARatiosFC

/-- `g ε (p^1) = (p + 1) / p^(1+ε)`, and for primes `p ≥ 3` this is `< g ε 2` (for any `ε ≥ 0`). -/
lemma gEps_prime_lt_two {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    gEps ε p < gEps ε 2 := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm hp2)))
  have hs' : σ 1 p = p + 1 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
    simpa [Finset.sum_range_succ, add_comm] using this
  have hs2 : σ 1 2 = 3 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    simpa [Finset.sum_range_succ] using this
  unfold gEps
  rw [hs', hs2]
  push_cast
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Real.rpow_add hp0, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_one]
  have hpe : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) (by linarith) hε
  have h2e : (0 : ℝ) < 2 ^ ε := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A large prime (`p + 1 < p^(1+ε)`) has `a ↦ g ε (p^a)` strictly decreasing. -/
lemma gEps_pow_strictAnti {ε : ℝ} {p : ℕ} (hp : p.Prime)
    (hlarge : (p : ℝ) + 1 < (p : ℝ) ^ (1 + ε)) : StrictAnti fun a : ℕ => gEps ε (p ^ a) := by
  apply strictAnti_nat_of_succ_lt
  intro a
  have hδ : 1 < delta ε p := by unfold delta; linarith
  have hsig : 1 ≤ sig p a := by have := sig_ge hp a; have : (0 : ℝ) ≤ a := a.cast_nonneg; linarith
  have hc : 0 < ((p : ℝ) ^ (1 + ε)) ^ (a + 1) :=
    pow_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) _
  have hsub := gEps_succ_sub ε hp a
  have hneg : (1 - delta ε p * sig p a) / ((p : ℝ) ^ (1 + ε)) ^ (a + 1) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) hc
  linarith

/-- If `g ε 2 < 1` then every prime is large: `p + 1 < p^(1+ε)`. -/
lemma large_of_gEps_two_lt_one {ε : ℝ} (hε : 0 < ε) (h2 : gEps ε 2 < 1) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) + 1 < (p : ℝ) ^ (1 + ε) := by
  have hle : gEps ε p ≤ gEps ε 2 := by
    rcases eq_or_ne p 2 with rfl | hp2
    · exact le_rfl
    · exact (gEps_prime_lt_two hε.le hp hp2).le
  have hs' : σ 1 p = p + 1 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
    simpa [Finset.sum_range_succ, add_comm] using this
  have hlt : gEps ε p < 1 := lt_of_le_of_lt hle h2
  unfold gEps at hlt
  rw [hs'] at hlt
  push_cast at hlt
  have hc : 0 < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  rwa [div_lt_one hc] at hlt

/-- If `g ε 2 < 1`, then `g ε k ≤ 1` for every `k ≥ 1` (so `1` is the global maximizer). -/
lemma gEps_le_one_of_two {ε : ℝ} (hε : 0 < ε) (h2 : gEps ε 2 < 1) {k : ℕ} (hk : 1 ≤ k) : gEps ε k ≤ 1 := by
  have h1 : IsMaxG ε 1 := (isMaxG_iff ε le_rfl).mpr fun p hp =>
    (isMaxExp_iff_of_large hε hp (large_of_gEps_two_lt_one hε h2 hp) _).mpr (by simp)
  have := h1.2 k hk
  rwa [gEps_one] at this

/-- Split `n` at a prime `p`: `g ε n = g ε (p^v_p(n)) * g ε (n / p^v_p(n))`. -/
lemma gEps_split (ε : ℝ) {n p : ℕ} (hp : p.Prime) (hn0 : n ≠ 0) :
    gEps ε n = gEps ε (p ^ n.factorization p) * gEps ε (n / p ^ n.factorization p) := by
  have hcop : (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
    (Nat.coprime_ordCompl hp hn0).pow_left _
  rw [← gEps_mul_of_coprime ε hcop, Nat.ordProj_mul_ordCompl_eq_self n p]

/-- If `g ε 2 < 1`, every `n > 1` has `g ε n < 1`. -/
lemma gEps_lt_one_of_two {ε : ℝ} (hε : 0 < ε) (h2 : gEps ε 2 < 1) {n : ℕ} (hn : 1 < n) : gEps ε n < 1 := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have ha : 1 ≤ n.factorization p :=
    (hp.dvd_iff_one_le_factorization hn0).mp (Nat.minFac_dvd n)
  have hanti := gEps_pow_strictAnti hp (large_of_gEps_two_lt_one hε h2 hp)
  have hpa : gEps ε (p ^ n.factorization p) < 1 := by
    have := hanti (show 0 < n.factorization p by omega)
    simpa [gEps_one] using this
  have hk : 1 ≤ n / p ^ n.factorization p := Nat.ordCompl_pos p hn0
  have hk1 := gEps_le_one_of_two hε h2 hk
  rw [gEps_split ε hp hn0]
  have := gEps_nonneg ε (p ^ n.factorization p)
  have := gEps_nonneg ε (n / p ^ n.factorization p)
  nlinarith

/-- If `g ε 2 < 1`, every `n > 1` other than `2` has `g ε n < g ε 2`. -/
theorem gEps_lt_gEps_two {ε : ℝ} (hε : 0 < ε) (h2 : gEps ε 2 < 1) {n : ℕ} (hn : 1 < n) (hn2 : n ≠ 2) :
    gEps ε n < gEps ε 2 := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set a := n.factorization p
  have ha : 1 ≤ a := (hp.dvd_iff_one_le_factorization hn0).mp (Nat.minFac_dvd n)
  set k := n / p ^ a
  have hk : 1 ≤ k := Nat.ordCompl_pos p hn0
  have hanti := gEps_pow_strictAnti hp (large_of_gEps_two_lt_one hε h2 hp)
  have hsplit : gEps ε n = gEps ε (p ^ a) * gEps ε k := gEps_split ε hp hn0
  have hpa0 := gEps_nonneg ε (p ^ a)
  have hk0 := gEps_nonneg ε k
  have hk1 := gEps_le_one_of_two hε h2 hk
  -- `g ε (p^a) ≤ g ε p ≤ g ε 2`
  have hpa_le : gEps ε (p ^ a) ≤ gEps ε p := by
    have := hanti.antitone ha; simpa using this
  have hp_le : gEps ε p ≤ gEps ε 2 := by
    rcases eq_or_ne p 2 with h | h
    · rw [h]
    · exact (gEps_prime_lt_two hε.le hp h).le
  by_cases hstrict : gEps ε (p ^ a) < gEps ε 2
  · rw [hsplit]; nlinarith
  · -- equality forces `p = 2` and `a = 1`, so `k > 1` and `g ε k < 1`
    have hp2 : p = 2 := by
      by_contra h
      have := gEps_prime_lt_two hε.le hp h
      exact hstrict (lt_of_le_of_lt hpa_le this)
    have ha1 : a = 1 := by
      by_contra h
      have := hanti (show 1 < a by omega)
      simp only [pow_one] at this
      exact hstrict (lt_of_lt_of_le this hp_le)
    have hk2 : 1 < k := by
      by_contra h
      have hk1' : k = 1 := by omega
      apply hn2
      have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [show n / p ^ n.factorization p = k from rfl, hk1', show n.factorization p = a from rfl, ha1, hp2] at this
      omega
    have hklt := gEps_lt_one_of_two hε h2 hk2
    have hpa_pos : 0 < gEps ε (p ^ a) := gEps_pos ε (pow_ne_zero _ hp.ne_zero)
    rw [hsplit]
    nlinarith

/-- By the six exponentials theorem [La66, Ra68], for each $\varepsilon > 0$, at most four integers
$n > 1$ simultaneously maximize $\sigma_1(n) / n^{1+\varepsilon}$ [AE44, EN75]. -/
theorem encard_colossallyAbundant_maximizers_le_four (ε : ℝ) (hε : 0 < ε) :
    Set.encard {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)} ≤ 4 := by
  set M := {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 < k →
      (σ 1 k : ℝ) / (k : ℝ) ^ (1 + ε) ≤ (σ 1 n : ℝ) / (n : ℝ) ^ (1 + ε)} with hM
  by_cases hc : ∀ n ∈ M, 1 ≤ gEps ε n
  · -- every FC maximizer also beats `k = 1`
    have hsub : M ⊆ {n : ℕ | IsMaxG ε n} := by
      intro n hn
      refine ⟨hn.1.le, fun m hm => ?_⟩
      rcases eq_or_lt_of_le hm with rfl | hm1
      · rw [gEps_one]; exact hc n hn
      · exact hn.2 m hm1
    exact (Set.encard_le_encard hsub).trans (encard_maximizers_le_four hε)
  · push Not at hc
    obtain ⟨n₀, hn₀, hlt⟩ := hc
    have h2 : gEps ε 2 < 1 := lt_of_le_of_lt (hn₀.2 2 (by norm_num)) hlt
    have hsub : M ⊆ {2} := by
      intro n hn
      by_contra hn2
      have := gEps_lt_gEps_two hε h2 hn.1 hn2
      exact absurd (hn.2 2 (by norm_num)) (not_le.mpr this)
    calc M.encard ≤ ({2} : Set ℕ).encard := Set.encard_le_encard hsub
      _ = 1 := Set.encard_singleton 2
      _ ≤ 4 := by norm_num

end CARatiosFC

end OMAPort_CA

theorem OMA.solution :
    type_of% @ColossallyAbundantNumber.encard_colossallyAbundant_maximizers_le_four :=
  fun ε hε => OMAPort_CA.CARatiosFC.encard_colossallyAbundant_maximizers_le_four ε hε
