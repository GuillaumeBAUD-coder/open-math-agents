import FormalConjectures.ErdosProblems.«69»
import Mathlib

/-!
# Erdős 69: verification and integration of the external six-term proof

Credit: Hanan Beer (@hananzlt), pinned-source verification, compatibility,
integration and submission. The mathematical formalization is reused from
plby/lean-proofs, added by Boris Alexeev; its authorship is not claimed here.
Source: https://github.com/plby/lean-proofs
Pinned commit: 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
The source describes six-term cancellation and composite dilations.
Its Erdos697PrimeHarmonic file is released under Apache 2.0, as retained below.
The prime Mertens dependency is from frenzymath/FormalPantheon, BoundedGaps/Maynard/PrimeMertens.lean,
commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1 (Apache 2.0).
FormalPantheon maintainers are credited for that dependency. Original notices
are preserved. The only proof-body edit is a proposition-valued letI changed
to let in summable_nonprimeMangoldtTerm, as requested by the Lean style linter.

The irrationality of this series was proved by Terence Tao and Joni Teräväinen,
Quantitative correlations and some problems on prime factors of consecutive
integers, arXiv:2512.01739 (2025). This submission is formalization reuse and
verification, not a claim to a new mathematical result.
-/


/- Source module 1: ErdosProblems.Erdos69.ResidueAverages -/
section SourceModule1
/-
# Quantitative residue-class averages

All errors are uniform in the modulus and the residue. No limiting
equidistribution statement is substituted for the finite estimate.
-/

namespace Erdos69.Elementary

def residueCount (T d v : ℕ) : ℕ := T.count (fun k ↦ k ≡ v [MOD d])

noncomputable def residueFrequency (T d v : ℕ) : ℝ := (residueCount T d v : ℝ) / T

theorem residueCount_eq (T d v : ℕ) (hd : 0 < d) :
    residueCount T d v = T / d + if v % d < T % d then 1 else 0 :=
  Nat.count_modEq_card T hd v

theorem residueCount_error (T d v : ℕ) (hd : 0 < d) :
    |(residueCount T d v : ℝ) - (T : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrem : ((T % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt T hd
  have hrem0 : (0 : ℝ) ≤ ((T % d : ℕ) : ℝ) := by positivity
  have hdecomp : (T : ℝ) = (d : ℝ) * ((T / d : ℕ) : ℝ) + ((T % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod T d).symm
  have hquot : (T : ℝ) / d = ((T / d : ℕ) : ℝ) + ((T % d : ℕ) : ℝ) / d := by
    rw [div_eq_iff hdR.ne']
    field_simp
    nlinarith [hdecomp]
  have hfrac0 : (0 : ℝ) ≤ ((T % d : ℕ) : ℝ) / d := div_nonneg hrem0 hdR.le
  have hfrac1 : ((T % d : ℕ) : ℝ) / d < 1 := (div_lt_one hdR).mpr hrem
  rw [residueCount_eq T d v hd, hquot]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- The finite average differs from `1/d` by at most `1/T`. -/
theorem residueFrequency_error (T d v : ℕ) (hT : 0 < T) (hd : 0 < d) :
    |residueFrequency T d v - (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hid : residueFrequency T d v - (1 : ℝ) / d =
      ((residueCount T d v : ℝ) - (T : ℝ) / d) / T := by
    unfold residueFrequency
    field_simp
  rw [hid, abs_div, abs_of_pos hTR]
  exact div_le_div_of_nonneg_right (residueCount_error T d v hd) hTR.le

/-- A coprime affine congruence is exactly one residue class, even when
the modulus is composite. -/
theorem exists_affine_residue (d Q b : ℕ) (hd : 0 < d) (hQ : Q.Coprime d) :
    ∃ v : ℕ, ∀ t : ℕ, d ∣ b + Q * t ↔ t ≡ v [MOD d] := by
  let : NeZero d := ⟨hd.ne'⟩
  let z : ZMod d := -((Q : ZMod d)⁻¹ * (b : ZMod d))
  refine ⟨z.val, fun t ↦ ?_⟩
  have hinv : (Q : ZMod d)⁻¹ * (Q : ZMod d) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one Q hQ
  have hinv' : (Q : ZMod d) * (Q : ZMod d)⁻¹ = 1 := by
    rw [mul_comm]
    exact hinv
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  change (b : ZMod d) + (Q : ZMod d) * (t : ZMod d) = 0 ↔ (t : ZMod d) = z
  constructor
  · intro ht
    have h := congrArg (fun w : ZMod d ↦ (Q : ZMod d)⁻¹ * w) ht
    rw [mul_add, ← mul_assoc, hinv, one_mul, mul_zero] at h
    dsimp [z]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  · intro ht
    rw [ht]
    dsimp [z]
    rw [mul_neg, ← mul_assoc, hinv', one_mul, add_neg_cancel]

def affineResidueCount (T d Q b : ℕ) : ℕ := T.count (fun t ↦ d ∣ b + Q * t)

theorem affineResidueCount_error (T d Q b : ℕ) (hd : 0 < d) (hQ : Q.Coprime d) :
    |(affineResidueCount T d Q b : ℝ) - (T : ℝ) / d| ≤ 1 := by
  obtain ⟨v, hv⟩ := exists_affine_residue d Q b hd hQ
  have heq : affineResidueCount T d Q b = residueCount T d v := by
    unfold affineResidueCount residueCount
    congr 1
    funext t
    exact propext (hv t)
  rw [heq]
  exact residueCount_error T d v hd

theorem affineResidueFrequency_error (T d Q b : ℕ) (hT : 0 < T)
    (hd : 0 < d) (hQ : Q.Coprime d) :
    |(affineResidueCount T d Q b : ℝ) / T - (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  obtain ⟨v, hv⟩ := exists_affine_residue d Q b hd hQ
  have heq : affineResidueCount T d Q b = residueCount T d v := by
    unfold affineResidueCount residueCount
    congr 1
    funext t
    exact propext (hv t)
  rw [heq]
  exact residueFrequency_error T d v hT hd

end Erdos69.Elementary

end SourceModule1

/- Source module 2: ErdosProblems.Erdos69.FiniteExpectation -/
section SourceModule2
/-
# Finite probability laws

Finite weighted sums suffice for the moment comparison. This module keeps
normalization and nonnegativity explicit.
-/

open scoped BigOperators

namespace Erdos69.Elementary

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

noncomputable def mean (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ x, μ.mass x * f x

noncomputable def complexMean (μ : FiniteLaw Ω) (f : Ω → ℂ) : ℂ :=
  ∑ x, (μ.mass x : ℂ) * f x

theorem mean_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.mean f := Finset.sum_nonneg (fun x _ ↦ mul_nonneg (μ.nonneg x) (hf x))

theorem mean_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum (fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

@[simp] theorem mean_const (μ : FiniteLaw Ω) (c : ℝ) : μ.mean (fun _ ↦ c) = c := by
  rw [mean, ← Finset.sum_mul, μ.total, one_mul]

theorem mean_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun x ↦ f x + g x) = μ.mean f + μ.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun x ↦ f x - g x) = μ.mean f - μ.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun x ↦ f x * c) = μ.mean f * c := by
  simp [mean, mul_assoc, Finset.sum_mul]

theorem mean_const_mul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.mean (fun x ↦ c * f x) = c * μ.mean f := by
  simpa only [mul_comm] using μ.mean_mul_const f c

theorem mean_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.mean (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem abs_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.mean f| ≤ μ.mean (fun x ↦ |f x|) := by
  calc
    |μ.mean f| ≤ ∑ x, |μ.mass x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.mean (fun x ↦ |f x|) := by
      simp [mean, abs_mul, abs_of_nonneg (μ.nonneg _)]

theorem complexMean_real (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.complexMean (fun x ↦ (f x : ℂ)) = (μ.mean f : ℂ) := by
  simp [complexMean, mean]

theorem complexMean_sub (μ : FiniteLaw Ω) (f g : Ω → ℂ) :
    μ.complexMean (fun x ↦ f x - g x) = μ.complexMean f - μ.complexMean g := by
  simp [complexMean, mul_sub, Finset.sum_sub_distrib]

theorem norm_complexMean_le (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    ‖μ.complexMean f‖ ≤ μ.mean (fun x ↦ ‖f x‖) := by
  calc
    ‖μ.complexMean f‖ ≤ ∑ x, ‖(μ.mass x : ℂ) * f x‖ := norm_sum_le _ _
    _ = μ.mean (fun x ↦ ‖f x‖) := by
      simp [mean, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg _)]

theorem norm_complexMean_sub_le (μ : FiniteLaw Ω) (f g : Ω → ℂ) :
    ‖μ.complexMean f - μ.complexMean g‖ ≤ μ.mean (fun x ↦ ‖f x - g x‖) := by
  rw [← μ.complexMean_sub]
  exact μ.norm_complexMean_le _

noncomputable def uniform (T : ℕ) (hT : 0 < T) : FiniteLaw (Fin T) where
  mass := fun _ ↦ (1 : ℝ) / T
  nonneg := fun _ ↦ by positivity
  total := by
    have h : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    simp [h]

noncomputable def categorical (ι : Type*) [Fintype ι] (p : ℕ)
    (hp : 0 < p) (hcard : Fintype.card ι ≤ p) : FiniteLaw (Option ι) where
  mass := fun i ↦ match i with
    | none => 1 - (Fintype.card ι : ℝ) / p
    | some _ => (1 : ℝ) / p
  nonneg := by
    intro i
    cases i with
    | none =>
      apply sub_nonneg.mpr
      apply (div_le_one (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
      exact_mod_cast hcard
    | some i => positivity
  total := by
    rw [Fintype.sum_option]
    simp [div_eq_mul_inv]

noncomputable def independentProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) : FiniteLaw (ι → Ω) := by
  classical
  exact {
    mass := fun x ↦ ∏ i, (μ i).mass (x i)
    nonneg := fun x ↦ Finset.prod_nonneg (fun i _ ↦ (μ i).nonneg (x i))
    total := by rw [← Fintype.prod_sum]; simp [FiniteLaw.total]
  }

theorem independentProduct_mean_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (f : ι → Ω → ℝ) :
    (independentProduct μ).mean (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, (μ i).mean (f i) := by
  classical
  unfold mean independentProduct
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ (μ i).mass x * f i x)).symm

theorem independentProduct_complexMean_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (f : ι → Ω → ℂ) :
    (independentProduct μ).complexMean (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, (μ i).complexMean (f i) := by
  classical
  unfold complexMean independentProduct
  simp only [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ ((μ i).mass x : ℂ) * f i x)).symm

def optionalValue {ι : Type*} (c : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => c i

theorem categorical_mean {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (c : ι → ℝ) :
    (categorical ι p hp hc).mean (optionalValue c) = (∑ i, c i) / p := by
  simp [mean, categorical, optionalValue, Fintype.sum_option, div_eq_mul_inv,
    ← Finset.sum_mul, mul_comm]

theorem categorical_mean_square {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (c : ι → ℝ) :
    (categorical ι p hp hc).mean (fun x ↦ optionalValue c x ^ 2) =
      (∑ i, c i ^ 2) / p := by
  simp [mean, categorical, optionalValue, Fintype.sum_option, div_eq_mul_inv,
    ← Finset.mul_sum, mul_comm]

theorem optionalValue_abs_le {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (x : Option ι) : |optionalValue c x| ≤ ∑ i, |c i| := by
  cases x with
  | none => simp only [optionalValue, abs_zero]; positivity
  | some i => exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (c j)) (Finset.mem_univ i)

theorem sum_sq_le_mass_sq {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    (∑ i, c i ^ 2) ≤ (∑ i, |c i|) ^ 2 := by
  simpa only [sq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i ↦ |c i|)
      (fun i _ ↦ abs_nonneg (c i))

end FiniteLaw

end Erdos69.Elementary

end SourceModule2

/- Source module 3: ErdosProblems.Erdos69.JointResidues -/
section SourceModule3
/- # Joint residue events and their finite averages -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem modEq_finset_prod_iff {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (h : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j))) (a b : ℕ) :
    a ≡ b [MOD ∏ i ∈ s, d i] ↔ ∀ i ∈ s, a ≡ b [MOD d i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert i s hi ih =>
    have hs : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j)) :=
      h.mono (by simp)
    have hcop : (d i).Coprime (∏ j ∈ s, d j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      exact h (by simp) (by simp [hj]) (by intro hij; subst j; exact hi hj)
    rw [Finset.prod_insert hi, ← Nat.modEq_and_modEq_iff_modEq_mul hcop, ih hs]
    simp

theorem exists_joint_residue {ι : Type*} (s : Finset ι) (d r : ι → ℕ)
    (hd : ∀ i ∈ s, 0 < d i)
    (hcop : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j))) :
    ∃ v : ℕ, ∀ t : ℕ,
      (∀ i ∈ s, t ≡ r i [MOD d i]) ↔ t ≡ v [MOD ∏ i ∈ s, d i] := by
  classical
  let c := Nat.chineseRemainderOfFinset r d s (fun i hi ↦ (hd i hi).ne') hcop
  refine ⟨c.val, fun t ↦ ?_⟩
  rw [modEq_finset_prod_iff s d hcop]
  constructor
  · intro ht i hi
    exact (ht i hi).trans (c.property i hi).symm
  · intro ht i hi
    exact (ht i hi).trans (c.property i hi)

namespace FiniteLaw

theorem uniform_mean_indicator (T : ℕ) (hT : 0 < T)
    (P : ℕ → Prop) [DecidablePred P] :
    (uniform T hT).mean (fun t ↦ if P t.val then (1 : ℝ) else 0) =
      (T.count P : ℝ) / T := by
  simp only [mean, uniform, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun t ↦ if P t then (1 : ℝ) else 0) T]
  rw [Nat.count_eq_card_filter_range]
  simp [Finset.sum_boole, div_eq_mul_inv, mul_comm]

theorem uniform_mean_residue_error (T d v : ℕ) (hT : 0 < T) (hd : 0 < d) :
    |(uniform T hT).mean (fun t ↦ if t.val ≡ v [MOD d] then (1 : ℝ) else 0) -
      (1 : ℝ) / d| ≤ (1 : ℝ) / T := by
  rw [uniform_mean_indicator T hT (fun t ↦ t ≡ v [MOD d])]
  exact residueFrequency_error T d v hT hd

theorem uniform_mean_joint_residue_error {ι : Type*} (s : Finset ι)
    (d r : ι → ℕ) (hd : ∀ i ∈ s, 0 < d i)
    (hcop : Set.Pairwise (s : Set ι) (fun i j ↦ (d i).Coprime (d j)))
    (T : ℕ) (hT : 0 < T) :
    |(uniform T hT).mean (fun t ↦
      ∏ i ∈ s, (if t.val ≡ r i [MOD d i] then (1 : ℝ) else 0)) -
        (1 : ℝ) / (∏ i ∈ s, d i : ℕ)| ≤ (1 : ℝ) / T := by
  classical
  obtain ⟨v, hv⟩ := exists_joint_residue s d r hd hcop
  simp_rw [Finset.prod_boole, hv]
  exact uniform_mean_residue_error T _ v hT (Finset.prod_pos hd)

end FiniteLaw

end Erdos69.Elementary

end SourceModule3

/- Source module 4: ErdosProblems.Erdos69.FiniteMoments -/
section SourceModule4
/-
# Finite moment comparison

A uniform error for each joint product gives a moment error controlled by
the full absolute coefficient mass. In particular there is no suppressed
dependence on the number of shifts.
-/

open scoped BigOperators

namespace Erdos69.Elementary

namespace FiniteLaw

variable {Ω Ω' ι : Type*} [Fintype Ω] [Fintype Ω'] [Fintype ι]

theorem mean_power_sum (μ : FiniteLaw Ω) (c : ι → ℝ) (X : ι → Ω → ℝ) (m : ℕ) :
    μ.mean (fun x ↦ (∑ i, c i * X i x) ^ m) =
      ∑ k : Fin m → ι, (∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [μ.mean_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact μ.mean_const_mul _ _

/-- Quantitative comparison of the `m`-th moments, from uniform joint-product errors. -/
theorem moment_error_le (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (c : ι → ℝ) (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ) (m : ℕ) (δ : ℝ)
    (hjoint : ∀ k : Fin m → ι,
      |μ.mean (fun x ↦ ∏ j, X (k j) x) - ν.mean (fun x ↦ ∏ j, Y (k j) x)| ≤ δ) :
    |μ.mean (fun x ↦ (∑ i, c i * X i x) ^ m) -
      ν.mean (fun x ↦ (∑ i, c i * Y i x) ^ m)| ≤
        δ * (∑ i, |c i|) ^ m := by
  rw [mean_power_sum, mean_power_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin m → ι,
        ((∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) -
          (∏ j, c (k j)) * ν.mean (fun x ↦ ∏ j, Y (k j) x))| ≤
        ∑ k : Fin m → ι,
          |(∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) -
            (∏ j, c (k j)) * ν.mean (fun x ↦ ∏ j, Y (k j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin m → ι, |∏ j, c (k j)| * δ := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hjoint k) (abs_nonneg _)
    _ = δ * (∑ i, |c i|) ^ m := by
      rw [← Finset.sum_mul, Fintype.sum_pow]
      simp only [Finset.abs_prod]
      ring

end FiniteLaw

end Erdos69.Elementary

end SourceModule4

/- Source module 5: ErdosProblems.Erdos69.CategoricalJoint -/
section SourceModule5
/- # Repeated coordinates in categorical moment comparisons -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω ρ ι : Type*} [Fintype Ω] [Fintype ρ] [Fintype ι]
  [DecidableEq ρ] [DecidableEq ι]

theorem mean_point_indicator [DecidableEq Ω] (μ : FiniteLaw Ω) (a : Ω) :
    μ.mean (fun x ↦ if x = a then (1 : ℝ) else 0) = μ.mass a := by
  classical
  simp [mean]

omit [DecidableEq ι] in
theorem categorical_mass_of_ne_none (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (a : Option ι) (ha : a ≠ none) :
    (categorical ι p hp hc).mass a = (1 : ℝ) / p := by
  cases a with
  | none => exact (ha rfl).elim
  | some i => rfl

theorem independentProduct_mean_partial_assignment (μ : ρ → FiniteLaw (Option ι))
    (s : Finset ρ) (a : ρ → Option ι) :
    (independentProduct μ).mean (fun x ↦
      if ∀ p ∈ s, x p = a p then (1 : ℝ) else 0) = ∏ p ∈ s, (μ p).mass (a p) := by
  have heq (x : ρ → Option ι) :
      (if ∀ p ∈ s, x p = a p then (1 : ℝ) else 0) =
        ∏ p, (if p ∈ s then (if x p = a p then (1 : ℝ) else 0) else 1) := by
    rw [Finset.prod_ite_mem_eq, Finset.prod_boole]
    split_ifs <;> rfl
  simp_rw [heq]
  rw [independentProduct_mean_prod μ
    (fun p x ↦ if p ∈ s then (if x = a p then (1 : ℝ) else 0) else 1)]
  have hmean (p : ρ) :
      (μ p).mean (fun x ↦ if p ∈ s then (if x = a p then (1 : ℝ) else 0) else 1) =
        if p ∈ s then (μ p).mass (a p) else 1 := by
    split_ifs <;> simp [mean_point_indicator]
  simp_rw [hmean]
  exact Finset.prod_ite_mem_eq _ _

theorem categorical_mean_partial_assignment (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (s : Finset ρ) (a : ρ → Option ι)
    (ha : ∀ j ∈ s, a j ≠ none) :
    (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
      (fun x ↦ if ∀ j ∈ s, x j = a j then (1 : ℝ) else 0) =
        ∏ j ∈ s, (1 : ℝ) / p j := by
  rw [independentProduct_mean_partial_assignment]
  exact Finset.prod_congr rfl (fun j hj ↦ categorical_mass_of_ne_none _ _ _ _ (ha j hj))

theorem categorical_tuple_comparison (μ : FiniteLaw Ω) (A : Ω → ρ → Option ι)
    (p : ρ → ℕ) (hp : ∀ j, 0 < p j) (hc : ∀ j, Fintype.card ι ≤ p j)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hjoint : ∀ (s : Finset ρ) (a : ρ → Option ι), (∀ j ∈ s, a j ≠ none) →
      |μ.mean (fun x ↦ if ∀ j ∈ s, A x j = a j then (1 : ℝ) else 0) -
        ∏ j ∈ s, (1 : ℝ) / p j| ≤ δ)
    (m : ℕ) (f : Fin m → ρ × ι) :
    |μ.mean (fun x ↦ ∏ k, (if A x (f k).1 = some (f k).2 then (1 : ℝ) else 0)) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
        (fun x ↦ ∏ k, (if x (f k).1 = some (f k).2 then (1 : ℝ) else 0))| ≤ δ := by
  classical
  simp_rw [Fintype.prod_boole]
  by_cases hex : ∃ a : ρ → Option ι, ∀ k, a (f k).1 = some (f k).2
  · obtain ⟨a, ha⟩ := hex
    let s : Finset ρ := Finset.univ.image (fun k ↦ (f k).1)
    have heq (x : ρ → Option ι) :
        (∀ k, x (f k).1 = some (f k).2) ↔ ∀ j ∈ s, x j = a j := by
      constructor
      · intro hx j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        exact (hx k).trans (ha k).symm
      · intro hx k
        exact (hx _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).trans (ha k)
    have hn (j : ρ) (hj : j ∈ s) : a j ≠ none := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      rw [ha k]
      simp
    simp_rw [heq]
    rw [categorical_mean_partial_assignment p hp hc s a hn]
    exact hjoint s a hn
  · have hn (x : ρ → Option ι) : ¬∀ k, x (f k).1 = some (f k).2 := by
      intro hx
      exact hex ⟨x, hx⟩
    simp only [if_neg (hn _), mean_const, sub_self, abs_zero]
    exact hδ

end Erdos69.Elementary.FiniteLaw

end SourceModule5

/- Source module 6: ErdosProblems.Erdos69.ResidueModel -/
section SourceModule6
/- # The categorical model of distinct residue classes -/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def residueOutcome {ι : Type*} (d : ℕ) (r : ι → ℕ) (t : ℕ) : Option ι := by
  classical
  exact if h : ∃ i, t ≡ r i [MOD d] then some h.choose else none

theorem residueOutcome_eq_some_iff {ι : Type*} (d : ℕ) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) (t : ℕ) (i : ι) :
    residueOutcome d r t = some i ↔ t ≡ r i [MOD d] := by
  classical
  unfold residueOutcome
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro heq
      simpa only [heq] using h.choose_spec
    · intro ht
      exact hr _ _ (h.choose_spec.symm.trans ht)
  · constructor
    · intro heq
      cases heq
    · intro ht
      exact (h ⟨i, ht⟩).elim

theorem card_le_of_distinct_residues {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) : Fintype.card ι ≤ d := by
  let f : ι → Fin d := fun i ↦ ⟨r i % d, Nat.mod_lt _ hd⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hr i j (congrArg Fin.val hij)
  simpa using Fintype.card_le_of_injective f hf

def assignedResidue {ι : Type*} (r : ι → ℕ) : Option ι → ℕ
  | none => 0
  | some i => r i

theorem residueOutcome_eq_assignment_iff {ι : Type*} (d : ℕ) (r : ι → ℕ)
    (hr : ∀ i j, r i ≡ r j [MOD d] → i = j) (t : ℕ)
    (a : Option ι) (ha : a ≠ none) :
    residueOutcome d r t = a ↔ t ≡ assignedResidue r a [MOD d] := by
  cases a with
  | none => exact (ha rfl).elim
  | some i => exact residueOutcome_eq_some_iff d r hr t i

namespace FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]

omit [Fintype ι] in
theorem uniform_residue_partial_assignment_error (p : ρ → ℕ)
    (hp : ∀ j, 0 < p j) (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (T : ℕ) (hT : 0 < T) (s : Finset ρ) (a : ρ → Option ι)
    (ha : ∀ j ∈ s, a j ≠ none) :
    |(uniform T hT).mean (fun t ↦ if ∀ j ∈ s, residueOutcome (p j) (r j) t = a j
      then (1 : ℝ) else 0) - ∏ j ∈ s, (1 : ℝ) / p j| ≤ (1 : ℝ) / T := by
  classical
  have heq (t : ℕ) : (∀ j ∈ s, residueOutcome (p j) (r j) t = a j) ↔
      ∀ j ∈ s, t ≡ assignedResidue (r j) (a j) [MOD p j] := by
    apply forall₂_congr
    intro j hj
    exact residueOutcome_eq_assignment_iff _ _ (hr j) _ _ (ha j hj)
  simp_rw [heq]
  have h := uniform_mean_joint_residue_error s p (fun j ↦ assignedResidue (r j) (a j))
    (fun j _ ↦ hp j) (fun i _ j _ hij ↦ hcop hij) T hT
  simp_rw [Finset.prod_boole] at h
  simp only [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one] at h ⊢
  convert h using 2
  congr 2
  funext t
  split_ifs <;> rfl

theorem uniform_residue_tuple_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (T : ℕ) (hT : 0 < T) (m : ℕ) (f : Fin m → ρ × ι) :
    |(uniform T hT).mean (fun t ↦
      ∏ k, (if t.val ≡ r (f k).1 (f k).2 [MOD p (f k).1] then (1 : ℝ) else 0)) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j)
        (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))).mean
        (fun x ↦ ∏ k, (if x (f k).1 = some (f k).2 then (1 : ℝ) else 0))| ≤
          (1 : ℝ) / T := by
  have h := categorical_tuple_comparison (uniform T hT)
    (fun t j ↦ residueOutcome (p j) (r j) t) p hp
    (fun j ↦ card_le_of_distinct_residues _ (hp j) (r j) (hr j))
    (1 / T) (by positivity)
    (uniform_residue_partial_assignment_error p hp hcop r hr T hT) m f
  simpa only [residueOutcome_eq_some_iff _ _ (hr _)] using h

theorem optionalValue_eq_sum_indicators (c : ι → ℝ) (a : Option ι) :
    optionalValue c a = ∑ i, c i * (if a = some i then (1 : ℝ) else 0) := by
  cases a with
  | none => simp [optionalValue]
  | some i => simp [optionalValue]

omit [DecidableEq ι] in
theorem residue_moment_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (r : ρ → ι → ℕ) (hr : ∀ j i k, r j i ≡ r j k [MOD p j] → i = k)
    (c : ι → ℝ) (T : ℕ) (hT : 0 < T) (m : ℕ) :
    |(uniform T hT).mean (fun t ↦
        (∑ j, ∑ i, c i * (if t.val ≡ r j i [MOD p j] then (1 : ℝ) else 0)) ^ m) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j)
        (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))).mean
          (fun x ↦ (∑ j, optionalValue c (x j)) ^ m)| ≤
        (1 : ℝ) / T * ((Fintype.card ρ : ℝ) * ∑ i, |c i|) ^ m := by
  classical
  let μ := uniform T hT
  let ν := independentProduct (fun j ↦ categorical ι (p j) (hp j)
    (card_le_of_distinct_residues _ (hp j) (r j) (hr j)))
  let X : (ρ × ι) → Fin T → ℝ := fun a t ↦
    if t.val ≡ r a.1 a.2 [MOD p a.1] then 1 else 0
  let Y : (ρ × ι) → (ρ → Option ι) → ℝ := fun a x ↦
    if x a.1 = some a.2 then 1 else 0
  have h := moment_error_le μ ν (fun a : ρ × ι ↦ c a.2) X Y m (1 / T)
    (uniform_residue_tuple_error p hp hcop r hr T hT m)
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  simpa only [μ, ν, X, Y, ← optionalValue_eq_sum_indicators] using h

end FiniteLaw

end Erdos69.Elementary

end SourceModule6

/- Source module 7: ErdosProblems.Erdos69.SixTermCancellation -/
section SourceModule7
/-
# Six-term cancellation

The two explicit six-point patterns cancel the directions `{1,2,4}` and
`{3,5,6}`. Their product cancels six consecutive directions using only
36 signed terms, rather than 64.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def hexDigit : Fin 6 → ℕ := ![0, 1, 2, 4, 5, 6]

def hexSign : Fin 6 → ℤ := ![1, -1, -1, 1, 1, -1]

def hexInterceptA : Fin 6 → ℕ := ![0, 4, 2, 10, 8, 12]

def hexInterceptB : Fin 6 → ℕ := ![0, 3, 12, 18, 27, 30]

theorem hexDigit_lt_seven (i : Fin 6) : hexDigit i < 7 := by
  fin_cases i <;> norm_num [hexDigit]

theorem hexDigit_injective : Function.Injective hexDigit := by
  decide

@[simp] theorem hexDigit_eq_zero_iff (i : Fin 6) : hexDigit i = 0 ↔ i = 0 := by
  fin_cases i <;> norm_num [hexDigit]

theorem hexSign_sq (i : Fin 6) : hexSign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [hexSign]

theorem hexSign_abs (i : Fin 6) : |hexSign i| = 1 := by
  fin_cases i <;> norm_num [hexSign]

theorem hexInterceptA_le (i : Fin 6) : hexInterceptA i ≤ 6 * hexDigit i := by
  fin_cases i <;> norm_num [hexInterceptA, hexDigit]

theorem hexInterceptB_le (i : Fin 6) : hexInterceptB i ≤ 6 * hexDigit i := by
  fin_cases i <;> norm_num [hexInterceptB, hexDigit]

theorem sum_hexSign : ∑ i : Fin 6, hexSign i = 0 := by
  norm_num [Fin.sum_univ_succ, hexSign]

def hexSignedSum (mu : Fin 6 → ℕ) (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : Fin 6, (hexSign i : ℝ) * f ((hexDigit i : ℤ) * h - mu i)

theorem hexSignedSum_A_one (f : ℤ → ℝ) : hexSignedSum hexInterceptA 1 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]

theorem hexSignedSum_A_two (f : ℤ → ℝ) : hexSignedSum hexInterceptA 2 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]
  ring

theorem hexSignedSum_A_four (f : ℤ → ℝ) : hexSignedSum hexInterceptA 4 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]

theorem hexSignedSum_B_three (f : ℤ → ℝ) : hexSignedSum hexInterceptB 3 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]

theorem hexSignedSum_B_five (f : ℤ → ℝ) : hexSignedSum hexInterceptB 5 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]
  ring

theorem hexSignedSum_B_six (f : ℤ → ℝ) : hexSignedSum hexInterceptB 6 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]

abbrev BlockLabel := Fin 6 × Fin 6

def blockDigit (i : BlockLabel) : ℕ := hexDigit i.1 + 7 * hexDigit i.2

def blockIntercept (i : BlockLabel) : ℕ := hexInterceptA i.1 + 7 * hexInterceptB i.2

def blockSign (i : BlockLabel) : ℤ := hexSign i.1 * hexSign i.2

theorem blockDigit_lt (i : BlockLabel) : blockDigit i < 49 := by
  have h₁ := hexDigit_lt_seven i.1
  have h₂ := hexDigit_lt_seven i.2
  dsimp [blockDigit]
  omega

theorem blockDigit_injective : Function.Injective blockDigit := by
  intro i j hij
  have hi := hexDigit_lt_seven i.1
  have hj := hexDigit_lt_seven j.1
  have h₁ : hexDigit i.1 = hexDigit j.1 := by
    dsimp [blockDigit] at hij
    omega
  have h₂ : hexDigit i.2 = hexDigit j.2 := by
    dsimp [blockDigit] at hij
    omega
  exact Prod.ext (hexDigit_injective h₁) (hexDigit_injective h₂)

theorem blockIntercept_le (i : BlockLabel) : blockIntercept i ≤ 6 * blockDigit i := by
  have h₁ := hexInterceptA_le i.1
  have h₂ := hexInterceptB_le i.2
  dsimp [blockIntercept, blockDigit]
  omega

theorem blockSign_abs (i : BlockLabel) : |blockSign i| = 1 := by
  simp [blockSign, abs_mul, hexSign_abs]

theorem sum_blockSign : ∑ i : BlockLabel, blockSign i = 0 := by
  simp [blockSign, Fintype.sum_prod_type, ← Finset.mul_sum, sum_hexSign]

def blockSignedSum (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : BlockLabel, (blockSign i : ℝ) *
    f ((blockDigit i : ℤ) * h - blockIntercept i)

theorem blockSignedSum_first (h : ℤ) (f : ℤ → ℝ) :
    blockSignedSum h f = ∑ j : Fin 6, (hexSign j : ℝ) *
      hexSignedSum hexInterceptA h
        (fun t ↦ f (t + 7 * ((hexDigit j : ℤ) * h - hexInterceptB j))) := by
  unfold blockSignedSum
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [hexSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have harg : ((blockDigit (i, j) : ℕ) : ℤ) * h - blockIntercept (i, j) =
      ((hexDigit i : ℤ) * h - hexInterceptA i) +
        7 * ((hexDigit j : ℤ) * h - hexInterceptB j) := by
    simp only [blockDigit, blockIntercept, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [harg]
  simp only [blockSign, Int.cast_mul]
  ring

theorem blockSignedSum_second (h : ℤ) (f : ℤ → ℝ) :
    blockSignedSum h f = ∑ i : Fin 6, (hexSign i : ℝ) *
      hexSignedSum hexInterceptB h
        (fun t ↦ f (((hexDigit i : ℤ) * h - hexInterceptA i) + 7 * t)) := by
  unfold blockSignedSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [hexSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have harg : ((blockDigit (i, j) : ℕ) : ℤ) * h - blockIntercept (i, j) =
      ((hexDigit i : ℤ) * h - hexInterceptA i) +
        7 * ((hexDigit j : ℤ) * h - hexInterceptB j) := by
    simp only [blockDigit, blockIntercept, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [harg]
  simp only [blockSign, Int.cast_mul]
  ring

theorem blockSignedSum_vanish {h : ℕ} (hpos : 1 ≤ h) (hle : h ≤ 6)
    (f : ℤ → ℝ) : blockSignedSum h f = 0 := by
  interval_cases h
  · simp [blockSignedSum_first, hexSignedSum_A_one]
  · simp [blockSignedSum_first, hexSignedSum_A_two]
  · simp [blockSignedSum_second, hexSignedSum_B_three]
  · simp [blockSignedSum_first, hexSignedSum_A_four]
  · simp [blockSignedSum_second, hexSignedSum_B_five]
  · simp [blockSignedSum_second, hexSignedSum_B_six]

end Erdos69.Elementary

end SourceModule7

/- Source module 8: ErdosProblems.Erdos69.IteratedCancellation -/
section SourceModule8
/-
# Iterated cancellation patterns

A pattern with `m` blocks has `36^m` signed terms, distinct slopes below
`49^m`, and cancels every direction from one through `6*m`.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def PatternLabel : ℕ → Type
  | 0 => PUnit
  | m + 1 => BlockLabel × PatternLabel m

instance patternFintype : (m : ℕ) → Fintype (PatternLabel m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    letI := patternFintype m
    inferInstanceAs (Fintype (BlockLabel × PatternLabel m))

def patternDigit : (m : ℕ) → PatternLabel m → ℕ
  | 0, _ => 0
  | m + 1, i => blockDigit i.1 + 49 * patternDigit m i.2

def patternIntercept : (m : ℕ) → PatternLabel m → ℕ
  | 0, _ => 0
  | m + 1, i => blockIntercept i.1 +
      49 * (patternIntercept m i.2 + 6 * patternDigit m i.2)

def patternSign : (m : ℕ) → PatternLabel m → ℤ
  | 0, _ => 1
  | m + 1, i => blockSign i.1 * patternSign m i.2

def patternZero : (m : ℕ) → PatternLabel m
  | 0 => PUnit.unit
  | m + 1 => ((0, 0), patternZero m)

theorem card_patternLabel (m : ℕ) : Fintype.card (PatternLabel m) = 36 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (BlockLabel × PatternLabel m) = _
    simp [Fintype.card_prod, BlockLabel, ih, pow_succ, Nat.mul_comm]

theorem patternDigit_lt (m : ℕ) (i : PatternLabel m) : patternDigit m i < 49 ^ m := by
  induction m with
  | zero => simp [patternDigit]
  | succ m ih =>
    have h₁ := blockDigit_lt i.1
    have h₂ := ih i.2
    simp only [patternDigit, pow_succ]
    omega

theorem patternDigit_injective (m : ℕ) : Function.Injective (patternDigit m) := by
  induction m with
  | zero =>
    intro i j _
    change PUnit at i j
    cases i
    cases j
    rfl
  | succ m ih =>
    rintro ⟨a, i⟩ ⟨b, j⟩ hij
    have ha := blockDigit_lt a
    have hb := blockDigit_lt b
    have h₁ : blockDigit a = blockDigit b := by
      simp only [patternDigit] at hij
      omega
    have h₂ : patternDigit m i = patternDigit m j := by
      simp only [patternDigit] at hij
      omega
    exact Prod.ext (blockDigit_injective h₁) (ih h₂)

theorem patternIntercept_le (m : ℕ) (i : PatternLabel m) :
    patternIntercept m i ≤ 6 * m * patternDigit m i := by
  induction m with
  | zero => simp [patternIntercept]
  | succ m ih =>
    have h₁ := blockIntercept_le i.1
    have h₂ := ih i.2
    simp only [patternIntercept, patternDigit]
    nlinarith [Nat.zero_le (m * blockDigit i.1)]

theorem patternSign_abs (m : ℕ) (i : PatternLabel m) : |patternSign m i| = 1 := by
  induction m with
  | zero => simp [patternSign]
  | succ m ih => simp [patternSign, abs_mul, blockSign_abs, ih]

theorem patternSign_abs_real (m : ℕ) (i : PatternLabel m) :
    |(patternSign m i : ℝ)| = 1 := by
  exact_mod_cast patternSign_abs m i

@[simp] theorem patternDigit_zero (m : ℕ) : patternDigit m (patternZero m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternDigit, patternZero, blockDigit, hexDigit, ih]

@[simp] theorem patternIntercept_zero (m : ℕ) : patternIntercept m (patternZero m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternIntercept, patternZero, blockIntercept,
      hexInterceptA, hexInterceptB, ih]

@[simp] theorem patternSign_zero (m : ℕ) : patternSign m (patternZero m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [patternSign, patternZero, blockSign, hexSign, ih]

theorem patternDigit_eq_zero_iff (m : ℕ) (i : PatternLabel m) :
    patternDigit m i = 0 ↔ i = patternZero m := by
  constructor
  · intro h
    apply patternDigit_injective m
    simpa using h
  · rintro rfl
    exact patternDigit_zero m

theorem sum_patternSign {m : ℕ} (hm : 0 < m) :
    ∑ i : PatternLabel m, patternSign m i = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    change (∑ i : BlockLabel × PatternLabel m, blockSign i.1 * patternSign m i.2) = 0
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_blockSign, zero_mul]

theorem sum_abs_patternSign (m : ℕ) :
    ∑ i : PatternLabel m, |(patternSign m i : ℝ)| = (36 : ℝ) ^ m := by
  simp [patternSign_abs_real, card_patternLabel]

def patternPhase (m : ℕ) (i : PatternLabel m) (h : ℤ) : ℤ :=
  (patternDigit m i : ℤ) * h - patternIntercept m i

theorem patternPhase_succ (m : ℕ) (a : BlockLabel) (i : PatternLabel m) (h : ℤ) :
    patternPhase (m + 1) (a, i) h =
      (blockDigit a : ℤ) * h - blockIntercept a + 49 * patternPhase m i (h - 6) := by
  simp only [patternPhase, patternDigit, patternIntercept, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

noncomputable def patternSignedSum (m : ℕ) (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : PatternLabel m, (patternSign m i : ℝ) * f (patternPhase m i h)

theorem patternSignedSum_first (m : ℕ) (h : ℤ) (f : ℤ → ℝ) :
    patternSignedSum (m + 1) h f =
      ∑ i : PatternLabel m, (patternSign m i : ℝ) *
        blockSignedSum h (fun t ↦ f (t + 49 * patternPhase m i (h - 6))) := by
  unfold patternSignedSum
  change (∑ i : BlockLabel × PatternLabel m, _) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [blockSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [patternPhase_succ]
  simp only [patternSign, Int.cast_mul]
  ring

theorem patternSignedSum_tail (m : ℕ) (h : ℤ) (f : ℤ → ℝ) :
    patternSignedSum (m + 1) h f =
      ∑ a : BlockLabel, (blockSign a : ℝ) *
        patternSignedSum m (h - 6)
          (fun t ↦ f ((blockDigit a : ℤ) * h - blockIntercept a + 49 * t)) := by
  unfold patternSignedSum
  change (∑ i : BlockLabel × PatternLabel m, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [patternPhase_succ]
  simp only [patternSign, Int.cast_mul]
  ring

/-- All of the first `6*m` directions cancel, for an arbitrary test function. -/
theorem patternSignedSum_vanish (m : ℕ) {h : ℕ} (hpos : 1 ≤ h) (hle : h ≤ 6 * m)
    (f : ℤ → ℝ) : patternSignedSum m h f = 0 := by
  induction m generalizing h f with
  | zero => omega
  | succ m ih =>
    by_cases hsmall : h ≤ 6
    · rw [patternSignedSum_first]
      simp [blockSignedSum_vanish hpos hsmall]
    · have hsubpos : 1 ≤ h - 6 := by omega
      have hsuble : h - 6 ≤ 6 * m := by omega
      have hcast : (h : ℤ) - 6 = ((h - 6 : ℕ) : ℤ) := by omega
      rw [patternSignedSum_tail, hcast]
      simp [ih hsubpos hsuble]

theorem pattern_mass_ratio (m : ℕ) :
    (36 : ℝ) ^ m / 2 ^ (6 * m) = (9 / 16 : ℝ) ^ m := by
  rw [pow_mul, ← div_pow]
  congr 1
  norm_num

end Erdos69.Elementary

end SourceModule8

/- Source module 9: ErdosProblems.Erdos69.CompositeDilations -/
section SourceModule9
/-
# Pairwise coprime composite dilations

The slopes are explicit rough integers, not conjectural prime patterns.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def roughDilation (P j : ℕ) : ℕ := 1 + primorial P * (1 + j)

theorem roughDilation_pos (P j : ℕ) : 0 < roughDilation P j := by
  simp [roughDilation]

theorem prime_gt_of_dvd_roughDilation {P j p : ℕ} (hp : p.Prime)
    (hd : p ∣ roughDilation P j) : P < p := by
  by_contra! hle
  have hv := hp.dvd_primorial_iff.mpr hle
  have hm : p ∣ primorial P * (1 + j) := dvd_mul_of_dvd_left hv _
  have hone : p ∣ 1 := by
    have h := Nat.dvd_sub hd hm
    simpa [roughDilation] using h
  exact hp.not_dvd_one hone

private theorem roughDilation_sub {j k : ℕ} (P : ℕ) :
    roughDilation P k - roughDilation P j = primorial P * (k - j) := by
  simp [roughDilation, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]

theorem roughDilation_coprime_of_lt {P j k : ℕ} (hjk : j < k) (hk : k ≤ P) :
    (roughDilation P j).Coprime (roughDilation P k) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpj hpk
  have hgt := prime_gt_of_dvd_roughDilation hp hpj
  have hd : p ∣ primorial P * (k - j) := by
    rw [← roughDilation_sub P]
    exact Nat.dvd_sub hpk hpj
  rcases hp.dvd_mul.mp hd with hv | hdiff
  · have hle := hp.dvd_primorial_iff.mp hv
    omega
  · have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hjk) hdiff
    omega

theorem roughDilation_coprime {P j k : ℕ} (hj : j ≤ P) (hk : k ≤ P) (hne : j ≠ k) :
    (roughDilation P j).Coprime (roughDilation P k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact roughDilation_coprime_of_lt h hk
  · exact (roughDilation_coprime_of_lt h hj).symm

def patternDilation (m P : ℕ) (i : PatternLabel m) : ℕ :=
  roughDilation P (patternDigit m i)

def patternOffset (m P : ℕ) (i : PatternLabel m) : ℕ :=
  primorial P * patternIntercept m i

theorem patternDilation_pos (m P : ℕ) (i : PatternLabel m) :
    0 < patternDilation m P i := roughDilation_pos _ _

theorem patternDilation_pairwise (m P : ℕ) (hP : 49 ^ m ≤ P) :
    Pairwise (fun i j : PatternLabel m ↦
      (patternDilation m P i).Coprime (patternDilation m P j)) := by
  intro i j hij
  apply roughDilation_coprime
  · exact (patternDigit_lt m i).le.trans hP
  · exact (patternDigit_lt m j).le.trans hP
  · exact fun h ↦ hij (patternDigit_injective m h)

/-- The congruences needed for every dilation are simultaneously soluble. -/
theorem exists_pattern_residue (m P : ℕ) (hP : 49 ^ m ≤ P) :
    ∃ n : ℕ, ∀ i : PatternLabel m, n ≡ patternOffset m P i [MOD patternDilation m P i] := by
  classical
  let c := Nat.chineseRemainderOfFinset (patternOffset m P) (patternDilation m P)
    Finset.univ
    (fun i _ ↦ (patternDilation_pos m P i).ne')
    (fun i _ j _ hij ↦ patternDilation_pairwise m P hP hij)
  exact ⟨c.val, fun i ↦ c.property i (Finset.mem_univ i)⟩

end Erdos69.Elementary

end SourceModule9

/- Source module 10: ErdosProblems.Erdos69.ElementaryArithmetic -/
section SourceModule10
/-
# Arithmetic foundations of the elementary proof of Erdős problem 69

The distinct-prime-divisor count, convergence of the exact binary series,
and the overlap correction for composite dilations.
-/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

/-- The number of distinct prime divisors. -/
def omegaCount (n : ℕ) : ℕ := n.primeFactors.card

@[simp] theorem omegaCount_zero : omegaCount 0 = 0 := by
  simp [omegaCount]

@[simp] theorem omegaCount_one : omegaCount 1 = 0 := by
  simp [omegaCount]

theorem omegaCount_eq_cardDistinctFactors (n : ℕ) :
    omegaCount n = ArithmeticFunction.cardDistinctFactors n := by
  simp [omegaCount, ArithmeticFunction.cardDistinctFactors_apply,
    ← Nat.toFinset_factors, List.card_toFinset]

theorem omegaCount_le_add_one (n : ℕ) : omegaCount n ≤ n + 1 := by
  unfold omegaCount
  calc
    n.primeFactors.card ≤ (Finset.range (n + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hprime, hdvd, hn⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd))
    _ = n + 1 := Finset.card_range _

/-- The exact real number in Erdős problem 69; the terms at zero and one vanish. -/
def binaryOmegaSum : ℝ := ∑' n : ℕ, (omegaCount n : ℝ) / 2 ^ n

theorem summable_omegaCount_div_two_pow :
    Summable (fun n : ℕ ↦ (omegaCount n : ℝ) / 2 ^ n) := by
  have hgeo : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hweighted : Summable (fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 1 (r := (1 / 2 : ℝ)) (by norm_num)
  have hmajor : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) / 2 ^ n) := by
    simpa [div_eq_mul_inv, add_mul, one_div, inv_pow] using hweighted.add hgeo
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) _ hmajor
  intro n
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast omegaCount_le_add_one n) (by positivity)

/-- Inclusion-exclusion for distinct prime factors, with no coprimality assumption. -/
theorem omegaCount_gcd_add_mul (a m : ℕ) :
    omegaCount (a.gcd m) + omegaCount (a * m) = omegaCount a + omegaCount m := by
  simpa [omegaCount] using
    Nat.sum_primeFactors_gcd_add_sum_primeFactors_mul a m (fun _ ↦ (1 : ℕ))

theorem omegaCount_mul_real (a m : ℕ) :
    (omegaCount (a * m) : ℝ) =
      omegaCount a + omegaCount m - omegaCount (a.gcd m) := by
  have h : (omegaCount (a.gcd m) : ℝ) + omegaCount (a * m) =
      omegaCount a + omegaCount m := by
    exact_mod_cast omegaCount_gcd_add_mul a m
  linarith

theorem primeFactors_gcd_eq_filter {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (a.gcd m).primeFactors = a.primeFactors.filter (fun p ↦ p ∣ m) := by
  rw [Nat.primeFactors_gcd ha hm]
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, (Nat.mem_primeFactors.mp h.2).2.1⟩
  · intro h
    exact ⟨h.1, Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp h.1).1, h.2, hm⟩⟩

theorem omegaCount_gcd_real {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (omegaCount (a.gcd m) : ℝ) =
      ∑ p ∈ a.primeFactors, if p ∣ m then (1 : ℝ) else 0 := by
  rw [omegaCount, primeFactors_gcd_eq_filter ha hm]
  simp

theorem omegaCount_mul_indicator {a m : ℕ} (ha : a ≠ 0) (hm : m ≠ 0) :
    (omegaCount (a * m) : ℝ) = omegaCount a + omegaCount m -
      ∑ p ∈ a.primeFactors, if p ∣ m then (1 : ℝ) else 0 := by
  rw [omegaCount_mul_real, omegaCount_gcd_real ha hm]

end

end Erdos69.Elementary

end SourceModule10

/- Source module 11: ErdosProblems.Erdos69.RoughSizeBounds -/
section SourceModule11
/-
# Elementary size estimates for the rough composite dilations

These estimates use the elementary bound `primorial P ≤ 4^P`.
-/

open scoped BigOperators

namespace Erdos69.Elementary

theorem roughDilation_le (P j : ℕ) :
    roughDilation P j ≤ 2 * primorial P * (1 + j) := by
  have hv : 0 < primorial P * (1 + j) := Nat.mul_pos (primorial_pos P) (by omega)
  dsimp [roughDilation]
  nlinarith

theorem log_primorial_le (P : ℕ) :
    Real.log (primorial P : ℝ) ≤ (P : ℝ) * Real.log 4 := by
  have h : (primorial P : ℝ) ≤ (4 : ℝ) ^ P := by
    exact_mod_cast primorial_le_four_pow P
  have hlog := Real.log_le_log (by exact_mod_cast primorial_pos P) h
  simpa [Real.log_pow] using hlog

theorem log_roughDilation_le {P j : ℕ} (hP : 1 ≤ P) (hj : j ≤ P) :
    Real.log (roughDilation P j : ℝ) ≤ 5 * (P : ℝ) := by
  have hv : (0 : ℝ) < primorial P := by exact_mod_cast primorial_pos P
  have hjpos : (0 : ℝ) < 1 + (j : ℝ) := by positivity
  have hupper : (roughDilation P j : ℝ) ≤ 2 * (primorial P : ℝ) * (1 + (j : ℝ)) := by
    exact_mod_cast roughDilation_le P j
  have hlog := Real.log_le_log
    (by exact_mod_cast roughDilation_pos P j) hupper
  rw [Real.log_mul (mul_pos (by norm_num) hv).ne' hjpos.ne',
    Real.log_mul (by norm_num) hv.ne'] at hlog
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlogj := Real.log_le_sub_one_of_pos hjpos
  have hlogV := log_primorial_le P
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hjR : (j : ℝ) ≤ P := by exact_mod_cast hj
  nlinarith

theorem sum_log_primeFactors_subset_le {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : s ⊆ n.primeFactors) :
    ∑ p ∈ s, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hp (p : ℕ) (hps : p ∈ s) : p.Prime :=
    (Nat.mem_primeFactors.mp (hs hps)).1
  have hd : (∏ p ∈ s, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset s n.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd n)
  have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hps ↦ (hp p hps).pos)
  have hle : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn hd
  have hlog := Real.log_le_log (by exact_mod_cast hprodpos) hle
  rw [Nat.cast_prod, Real.log_prod (fun p hps ↦ by
    exact_mod_cast (hp p hps).ne_zero)] at hlog
  exact hlog

theorem card_primeFactors_subset_mul_log_le {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : s ⊆ n.primeFactors) {R : ℝ} (hR : 0 < R)
    (hlarge : ∀ p ∈ s, R ≤ (p : ℝ)) :
    (s.card : ℝ) * Real.log R ≤ Real.log (n : ℝ) := by
  calc
    (s.card : ℝ) * Real.log R = ∑ p ∈ s, Real.log R := by simp
    _ ≤ ∑ p ∈ s, Real.log (p : ℝ) :=
      Finset.sum_le_sum (fun p hp ↦ Real.log_le_log hR (hlarge p hp))
    _ ≤ Real.log (n : ℝ) := sum_log_primeFactors_subset_le hn s hs

theorem omegaCount_mul_log_two_le {n : ℕ} (hn : 0 < n) :
    (omegaCount n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  apply card_primeFactors_subset_mul_log_le hn n.primeFactors (by rfl) (by norm_num)
  intro p hp
  exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le

theorem roughDilation_reciprocal_mass_le {P j : ℕ} (hP : 2 ≤ P) (hj : j ≤ P) :
    (∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / p) ≤
      5 / Real.log (P : ℝ) := by
  have hPR : (1 : ℝ) < P := by exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : ℝ) < P := by positivity
  have hlogpos : 0 < Real.log (P : ℝ) := Real.log_pos hPR
  have hlarge (p : ℕ) (hp : p ∈ (roughDilation P j).primeFactors) : (P : ℝ) ≤ p := by
    have hp' := Nat.mem_primeFactors.mp hp
    exact_mod_cast (prime_gt_of_dvd_roughDilation hp'.1 hp'.2.1).le
  have hcard := card_primeFactors_subset_mul_log_le (roughDilation_pos P j)
    (roughDilation P j).primeFactors (by rfl) hPpos hlarge
  have hsize := log_roughDilation_le (show 1 ≤ P by omega) hj
  calc
    (∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / p) ≤
        ∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / P := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hPpos (hlarge p hp)
    _ = ((roughDilation P j).primeFactors.card : ℝ) / P := by simp [div_eq_mul_inv]
    _ ≤ 5 / Real.log (P : ℝ) := by
      rw [div_le_div_iff₀ hPpos hlogpos]
      exact hcard.trans hsize

end Erdos69.Elementary

end SourceModule11

/- Source module 12: ErdosProblems.Erdos69.AugmentedModulus -/
section SourceModule12
/-
# Adding collision primes without changing dilation valuations

Only prime factors not already in the product of the dilations are added.
Consequently division by any one dilation leaves a coprime progression step.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def newPrimeFactors (A D : ℕ) : Finset ℕ := D.primeFactors.filter (fun p ↦ ¬p ∣ A)

def newPrimeProduct (A D : ℕ) : ℕ := ∏ p ∈ newPrimeFactors A D, p

def augmentedModulus (A D : ℕ) : ℕ := A * newPrimeProduct A D

theorem newPrimeProduct_pos (A D : ℕ) : 0 < newPrimeProduct A D := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos

theorem newPrimeProduct_dvd (A D : ℕ) : newPrimeProduct A D ∣ D := by
  apply dvd_trans _ (Nat.prod_primeFactors_dvd D)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem newPrimeProduct_coprime (A D : ℕ) : A.Coprime (newPrimeProduct A D) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpD, hpA⟩ := Finset.mem_filter.mp hp
  exact (Nat.Prime.coprime_iff_not_dvd (Nat.mem_primeFactors.mp hpD).1).mpr hpA |>.symm

theorem augmentedModulus_pos {A D : ℕ} (hA : 0 < A) : 0 < augmentedModulus A D :=
  Nat.mul_pos hA (newPrimeProduct_pos A D)

theorem dvd_augmentedModulus (A D : ℕ) : A ∣ augmentedModulus A D := dvd_mul_right _ _

theorem prime_dvd_augmentedModulus {A D p : ℕ} (hD : D ≠ 0) (hp : p.Prime)
    (hpD : p ∣ D) : p ∣ augmentedModulus A D := by
  by_cases hpA : p ∣ A
  · exact hpA.trans (dvd_augmentedModulus A D)
  · apply dvd_mul_of_dvd_right
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, hpD, hD⟩, hpA⟩)

theorem log_augmentedModulus_le {A D : ℕ} (hA : 0 < A) (hD : 0 < D) :
    Real.log (augmentedModulus A D : ℝ) ≤ Real.log A + Real.log D := by
  have hR := newPrimeProduct_pos A D
  have hle := Nat.le_of_dvd hD (newPrimeProduct_dvd A D)
  rw [augmentedModulus, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  gcongr

theorem coprime_augmentedModulus_quotient {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hc : Pairwise (fun i j ↦ (a i).Coprime (a j))) (D : ℕ) (i : ι) :
    (augmentedModulus (∏ j, a j) D / a i).Coprime (a i) := by
  classical
  let A := ∏ j, a j
  have hprod : A = a i * ∏ j ∈ Finset.univ.erase i, a j := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hadvd : a i ∣ A := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hr : (newPrimeProduct A D).Coprime (a i) :=
    (newPrimeProduct_coprime A D).symm.of_dvd_right hadvd
  have hcprod : (∏ j ∈ Finset.univ.erase i, a j).Coprime (a i) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro j hj
    exact hc (Finset.mem_erase.mp hj).1
  change (A * newPrimeProduct A D / a i).Coprime (a i)
  nth_rw 1 [hprod]
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (ha i)]
  exact hcprod.mul_left hr

end Erdos69.Elementary

end SourceModule12

/- Source module 13: ErdosProblems.Erdos69.CollisionPrimes -/
section SourceModule13
/- # Primes at which two retained shifts coincide -/

open scoped BigOperators

namespace Erdos69.Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def collisionProduct (r : ι → ℕ) : ℕ :=
  ∏ i, ∏ j, if i = j then 1 else Nat.dist (r i) (r j)

theorem collisionProduct_pos (r : ι → ℕ) (hr : Function.Injective r) :
    0 < collisionProduct r := by
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  split_ifs with hij
  · omega
  · exact Nat.dist_pos_of_ne (fun heq ↦ hij (hr heq))

theorem dist_dvd_collisionProduct (r : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    Nat.dist (r i) (r j) ∣ collisionProduct r := by
  have h₁ : (if i = j then 1 else Nat.dist (r i) (r j)) ∣
      ∏ k, if i = k then 1 else Nat.dist (r i) (r k) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  rw [if_neg hij] at h₁
  exact h₁.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem dvd_dist_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) : p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.modEq_iff_dvd' hab).mp h
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (Nat.modEq_iff_dvd' hba).mp h.symm

theorem distinct_residues_outside_augmentedModulus (r : ι → ℕ)
    (hr : Function.Injective r) (A p : ℕ) (hp : p.Prime)
    (hpQ : ¬p ∣ augmentedModulus A (collisionProduct r)) :
    ∀ i j, r i ≡ r j [MOD p] → i = j := by
  intro i j hij
  by_contra hne
  apply hpQ
  exact prime_dvd_augmentedModulus (collisionProduct_pos r hr).ne' hp
    ((dvd_dist_of_modEq hij).trans (dist_dvd_collisionProduct r hne))

theorem collisionProduct_le (r : ι → ℕ) (M : ℕ) (hM : 1 ≤ M) (hr : ∀ i, r i ≤ M) :
    collisionProduct r ≤ M ^ (Fintype.card ι * Fintype.card ι) := by
  have hdist (i j : ι) : Nat.dist (r i) (r j) ≤ M := by
    rw [Nat.dist_eq_max_sub_min]
    exact (Nat.sub_le _ _).trans (max_le (hr i) (hr j))
  calc
    collisionProduct r ≤ ∏ _i : ι, ∏ _j : ι, M := by
      apply Finset.prod_le_prod'
      intro i hi
      apply Finset.prod_le_prod'
      intro j hj
      split_ifs <;> first | exact hM | exact hdist i j
    _ = _ := by simp [← pow_mul]

theorem log_collisionProduct_le (r : ι → ℕ) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (hrM : ∀ i, r i ≤ M) :
    Real.log (collisionProduct r : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 * Real.log M := by
  have hD := collisionProduct_pos r hr
  have hle := collisionProduct_le r M hM hrM
  have hlog : Real.log (collisionProduct r : ℝ) ≤
      Real.log ((M : ℝ) ^ (Fintype.card ι * Fintype.card ι)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hle
  rw [Real.log_pow, Nat.cast_mul] at hlog
  simpa only [pow_two] using hlog

end Erdos69.Elementary

end SourceModule13

/- Source module 14: ErdosProblems.Erdos69.AffineResidueModel -/
section SourceModule14
/- # Residue models for the actual affine progression -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem exists_affine_residues {ρ ι : Type*} (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k) :
    ∃ r : ρ → ι → ℕ,
      (∀ j i t, p j ∣ b + Q * t + s i ↔ t ≡ r j i [MOD p j]) ∧
      ∀ j i k, r j i ≡ r j k [MOD p j] → i = k := by
  classical
  choose r hr using fun j i ↦ exists_affine_residue (p j) Q (b + s i) (hp j) (hQ j)
  have hr' (j : ρ) (i : ι) (t : ℕ) :
      p j ∣ b + Q * t + s i ↔ t ≡ r j i [MOD p j] := by
    simpa only [Nat.add_right_comm] using hr j i t
  refine ⟨r, hr', ?_⟩
  intro j i k hik
  have hi := (hr' j i (r j i)).mpr Nat.ModEq.rfl
  have hk := (hr' j k (r j i)).mpr hik
  have heq : b + Q * r j i + s i ≡ b + Q * r j i + s k [MOD p j] :=
    (Nat.modEq_zero_iff_dvd.mpr hi).trans (Nat.modEq_zero_iff_dvd.mpr hk).symm
  exact hs j i k (heq.add_left_cancel' _)

namespace FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ]

theorem affine_moment_error (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (T : ℕ) (hT : 0 < T) (m : ℕ) :
    |(uniform T hT).mean (fun t ↦
        (∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0)) ^ m) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
        (fun x ↦ (∑ j, optionalValue c (x j)) ^ m)| ≤
      (1 : ℝ) / T * ((Fintype.card ρ : ℝ) * ∑ i, |c i|) ^ m := by
  obtain ⟨r, hr, hrdist⟩ := exists_affine_residues p hp Q b hQ s hs
  simp_rw [hr]
  exact residue_moment_error p hp hcop r hrdist c T hT m

end FiniteLaw

end Erdos69.Elementary

end SourceModule14

/- Source module 15: ErdosProblems.Erdos69.FourierPhase -/
section SourceModule15
open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def fourierPhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem fourierPhase_zero : fourierPhase 0 = 1 := by
  simp [fourierPhase]

@[simp] theorem norm_fourierPhase (x : ℝ) : ‖fourierPhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem fourierPhase_add (x y : ℝ) :
    fourierPhase (x + y) = fourierPhase x * fourierPhase y := by
  simp [fourierPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierPhase_sub_mul (x y : ℝ) :
    fourierPhase (x - y) * fourierPhase y = fourierPhase x := by
  rw [← fourierPhase_add, sub_add_cancel]

theorem norm_fourierPhase_sub_one_le (x : ℝ) :
    ‖fourierPhase x - 1‖ ≤ 2 * Real.pi * |x| := by
  unfold fourierPhase
  rw [mul_comm ((2 * Real.pi * x : ℝ) : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |Real.sin (2 * Real.pi * x / 2)| ≤ 2 * |2 * Real.pi * x / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2 * Real.pi * |x| := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      ring

theorem norm_fourierPhase_sub_le (x y : ℝ) :
    ‖fourierPhase x - fourierPhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : fourierPhase x - fourierPhase y =
      (fourierPhase (x - y) - 1) * fourierPhase y := by
    rw [sub_mul, fourierPhase_sub_mul, one_mul]
  rw [heq, norm_mul, norm_fourierPhase, mul_one]
  exact norm_fourierPhase_sub_one_le (x - y)

@[simp] theorem fourierPhase_intCast (z : ℤ) : fourierPhase (z : ℝ) = 1 := by
  unfold fourierPhase
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  congr 1
  push_cast
  ring

theorem fourierPhase_add_intCast (x : ℝ) (z : ℤ) :
    fourierPhase (x + z) = fourierPhase x := by
  rw [fourierPhase_add, fourierPhase_intCast, mul_one]

theorem fourierPhase_neg (x : ℝ) : fourierPhase (-x) = star (fourierPhase x) := by
  unfold fourierPhase
  change Complex.exp ((2 * Real.pi * -x : ℝ) * Complex.I) =
    (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_ofNat, map_ofNat]
  ring

theorem fourierPhase_sub (x y : ℝ) :
    fourierPhase (x - y) = fourierPhase x * star (fourierPhase y) := by
  rw [sub_eq_add_neg, fourierPhase_add, fourierPhase_neg]

theorem fourierPhase_sub_realPart (x y : ℝ) :
    (fourierPhase (x - y)).re =
      (fourierPhase x).re * (fourierPhase y).re +
        (fourierPhase x).im * (fourierPhase y).im := by
  rw [fourierPhase_sub, Complex.mul_re]
  simp

theorem fourierPhase_realPart (x : ℝ) :
    (fourierPhase x).re = Real.cos (2 * Real.pi * x) := by
  simp only [fourierPhase, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem fourierPhase_realPart_le_one (x : ℝ) : (fourierPhase x).re ≤ 1 := by
  rw [fourierPhase_realPart]
  exact Real.cos_le_one _

noncomputable def phaseDeficit (x y : ℝ) : ℝ := 1 - (fourierPhase (x - y)).re

theorem phaseDeficit_nonneg (x y : ℝ) : 0 ≤ phaseDeficit x y :=
  sub_nonneg.mpr (fourierPhase_realPart_le_one _)

theorem phaseDeficit_symm (x y : ℝ) : phaseDeficit x y = phaseDeficit y x := by
  simp only [phaseDeficit, fourierPhase_sub_realPart]
  ring

theorem fourierPhase_deficit_lower {x : ℝ} (hx : |x| ≤ 1 / 2) :
    8 * x ^ 2 ≤ 1 - (fourierPhase x).re := by
  have harg : |Real.pi * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hnorm : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hnorm] at hsin
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |x|) hsin 2
  simp only [mul_pow, sq_abs] at hsquare
  rw [fourierPhase_realPart, show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
    Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem norm_mean_fourierPhase_le_one (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ≤ 1 := by
  simpa only [norm_fourierPhase, μ.mean_const] using
    μ.norm_complexMean_le (fun x ↦ fourierPhase (X x))

theorem norm_mean_fourierPhase_sub_le (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      μ.complexMean (fun x ↦ fourierPhase (Y x))‖ ≤
        (2 * Real.pi) * μ.mean (fun x ↦ |X x - Y x|) := by
  calc
    _ ≤ μ.mean (fun x ↦ ‖fourierPhase (X x) - fourierPhase (Y x)‖) :=
      μ.norm_complexMean_sub_le _ _
    _ ≤ μ.mean (fun x ↦ (2 * Real.pi) * |X x - Y x|) :=
      μ.mean_mono (fun x ↦ norm_fourierPhase_sub_le _ _)
    _ = _ := μ.mean_const_mul _ _

end FiniteLaw

end Erdos69.Elementary

end SourceModule15

/- Source module 16: ErdosProblems.Erdos69.FourierTaylor -/
section SourceModule16
/-
# A polynomial remainder bound on the imaginary axis

The bound has no exponential factor in the argument. This is needed when
only finitely many moments of the arithmetic model have been estimated.
-/

open scoped BigOperators
open Set

namespace Erdos69.Elementary

theorem iteratedDeriv_cexp_real_parameter (z : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ Complex.exp (z * t)) =
      fun t : ℝ ↦ z ^ n * Complex.exp (z * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t))
        (Complex.exp (z * t) * z) t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).const_mul z).cexp
    rw [(hd.const_mul (z ^ n)).deriv]
    ring

theorem norm_exp_sub_taylor_imaginary (z : ℂ) (hz : z.re = 0) (n : ℕ) :
    ‖Complex.exp z - ∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial‖ ≤
      ‖z‖ ^ (n + 1) / n.factorial := by
  let f : ℝ → ℂ := fun t ↦ Complex.exp (z * t)
  have hcont (j : ℕ) : ContDiff ℝ j f := by
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hderiv (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin j f (Icc 0 1) t = z ^ j * Complex.exp (z * t) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hcont j).contDiffAt ht]
    exact congrFun (iteratedDeriv_cexp_real_parameter z j) t
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) f (Icc 0 1) t‖ ≤ ‖z‖ ^ (n + 1) := by
    rw [hderiv _ _ ht, norm_mul, norm_pow, Complex.norm_exp]
    simp [Complex.mul_re, hz]
  have htaylor : taylorWithinEval f n (Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hderiv k 0 (by simp)]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1) (x := 1)
    (n := n) (by norm_num) (hcont (n + 1)).contDiffOn (by simp) hbound
  rw [htaylor] at h
  simpa [f] using h

noncomputable def phaseTaylor (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, ((2 * Real.pi : ℝ) * Complex.I) ^ k /
    k.factorial * (x : ℂ) ^ k

theorem fourierPhase_taylor_remainder (n : ℕ) (x : ℝ) :
    ‖fourierPhase x - phaseTaylor (n + 1) x‖ ≤
      (2 * Real.pi * |x|) ^ (n + 1) / n.factorial := by
  let z : ℂ := (2 * Real.pi * x : ℝ) * Complex.I
  have hz : z.re = 0 := by simp [z]
  have hnorm : ‖z‖ = 2 * Real.pi * |x| := by
    simp [z, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hpoly : (∑ k ∈ Finset.range (n + 1), z ^ k / k.factorial) =
      phaseTaylor (n + 1) x := by
    apply Finset.sum_congr rfl
    intro k hk
    have hz' : z = ((2 * Real.pi : ℝ) * Complex.I) * (x : ℂ) := by
      dsimp [z]
      push_cast
      ring
    rw [hz', mul_pow]
    ring
  have h := norm_exp_sub_taylor_imaginary z hz n
  rw [hpoly, hnorm] at h
  exact h

end Erdos69.Elementary

end SourceModule16

/- Source module 17: ErdosProblems.Erdos69.FourierTransfer -/
section SourceModule17
/- # Transfer of characteristic functions from finitely many moments -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem complexMean_const_mul (μ : FiniteLaw Ω) (c : ℂ) (f : Ω → ℂ) :
    μ.complexMean (fun x ↦ c * f x) = c * μ.complexMean f := by
  simp [complexMean, Finset.mul_sum, mul_left_comm]

theorem complexMean_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι)
    (f : ι → Ω → ℂ) :
    μ.complexMean (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.complexMean (f i) := by
  simp only [complexMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem complexMean_phaseTaylor (μ : FiniteLaw Ω) (X : Ω → ℝ) (n : ℕ) :
    μ.complexMean (fun x ↦ phaseTaylor n (X x)) =
      ∑ k ∈ Finset.range n, ((2 * Real.pi : ℝ) * Complex.I) ^ k /
        k.factorial * (μ.mean (fun x ↦ X x ^ k) : ℂ) := by
  simp only [phaseTaylor, complexMean_sum, complexMean_const_mul, ← Complex.ofReal_pow,
    complexMean_real]

theorem phaseTaylor_moment_error (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ k < n, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ) :
    ‖μ.complexMean (fun x ↦ phaseTaylor n (X x)) -
      ν.complexMean (fun y ↦ phaseTaylor n (Y y))‖ ≤
        δ * ∑ k ∈ Finset.range n, (2 * Real.pi) ^ k / k.factorial := by
  rw [complexMean_phaseTaylor, complexMean_phaseTaylor, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ‖((2 * Real.pi : ℝ) * Complex.I) ^ k / k.factorial *
          (μ.mean (fun x ↦ X x ^ k) : ℂ) -
          ((2 * Real.pi : ℝ) * Complex.I) ^ k / k.factorial *
          (ν.mean (fun y ↦ Y y ^ k) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ((2 * Real.pi) ^ k / k.factorial) * δ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← mul_sub, norm_mul, norm_div, norm_pow, ← Complex.ofReal_sub]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, Complex.norm_natCast, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_comm] using
        mul_le_mul (h k (Finset.mem_range.mp hk)) (le_refl ((2 * Real.pi) ^ k / k.factorial))
          (by positivity) hδ
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem mean_phaseTaylor_remainder (μ : FiniteLaw Ω) (X : Ω → ℝ) (n : ℕ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x))‖ ≤
        (2 * Real.pi) ^ (n + 1) / n.factorial * μ.mean (fun x ↦ |X x| ^ (n + 1)) := by
  calc
    _ ≤ μ.mean (fun x ↦ ‖fourierPhase (X x) - phaseTaylor (n + 1) (X x)‖) :=
      μ.norm_complexMean_sub_le _ _
    _ ≤ μ.mean (fun x ↦ (2 * Real.pi * |X x|) ^ (n + 1) / n.factorial) :=
      μ.mean_mono (fun x ↦ fourierPhase_taylor_remainder n (X x))
    _ = _ := by simp only [mul_pow, div_eq_mul_inv, mul_right_comm, mean_const_mul]

theorem fourier_moment_transfer (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ k < n + 1, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      ν.complexMean (fun y ↦ fourierPhase (Y y))‖ ≤
        δ * (∑ k ∈ Finset.range (n + 1), (2 * Real.pi) ^ k / k.factorial) +
        (2 * Real.pi) ^ (n + 1) / n.factorial *
          (μ.mean (fun x ↦ |X x| ^ (n + 1)) + ν.mean (fun y ↦ |Y y| ^ (n + 1))) := by
  have h₁ := μ.mean_phaseTaylor_remainder X n
  have h₂ := phaseTaylor_moment_error μ ν X Y (n + 1) δ hδ h
  have h₃ := ν.mean_phaseTaylor_remainder Y n
  have htri := norm_sub_le_norm_sub_add_norm_sub (μ.complexMean (fun x ↦ fourierPhase (X x)))
    (μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x)))
    (ν.complexMean (fun y ↦ fourierPhase (Y y)))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (μ.complexMean (fun x ↦ phaseTaylor (n + 1) (X x)))
    (ν.complexMean (fun y ↦ phaseTaylor (n + 1) (Y y)))
    (ν.complexMean (fun y ↦ fourierPhase (Y y)))
  rw [norm_sub_rev (ν.complexMean (fun y ↦ phaseTaylor (n + 1) (Y y)))] at htri'
  nlinarith

theorem mean_abs_power_le_exponential (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    μ.mean (fun x ↦ |X x| ^ n) ≤
      (n.factorial : ℝ) / s ^ n *
        (μ.mean (fun x ↦ Real.exp (s * X x)) +
          μ.mean (fun x ↦ Real.exp (-s * X x))) := by
  rw [← mean_add, ← mean_const_mul]
  apply μ.mean_mono
  intro x
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hsp : 0 < s ^ n := pow_pos hs n
  have hp := Real.pow_div_factorial_le_exp (s * |X x|)
    (mul_nonneg hs.le (abs_nonneg (X x))) n
  have hexp : Real.exp (s * |X x|) ≤ Real.exp (s * X x) + Real.exp (-s * X x) := by
    rcases le_total 0 (X x) with hx | hx
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-s * X x)]
    · rw [abs_of_nonpos hx]
      have heq : s * -X x = -s * X x := by ring
      rw [heq]
      linarith [Real.exp_pos (s * X x)]
  have hp' := hp.trans hexp
  rw [mul_pow, div_le_iff₀ hf] at hp'
  calc
    |X x| ^ n = (s ^ n * |X x| ^ n) / s ^ n := by field_simp
    _ ≤ ((Real.exp (s * X x) + Real.exp (-s * X x)) * n.factorial) / s ^ n :=
      div_le_div_of_nonneg_right hp' hsp.le
    _ = _ := by ring

end Erdos69.Elementary.FiniteLaw

end SourceModule17

/- Source module 18: ErdosProblems.Erdos69.EvenMomentTransfer -/
section SourceModule18
/- # A quantitative Fourier transfer from even moments -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem even_moment_mean_le (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (m : ℕ) (hm : Even m) (δ : ℝ)
    (h : |μ.mean (fun x ↦ X x ^ m) - ν.mean (fun y ↦ Y y ^ m)| ≤ δ) :
    μ.mean (fun x ↦ |X x| ^ m) ≤ ν.mean (fun y ↦ |Y y| ^ m) + δ := by
  simp only [hm.pow_abs]
  linarith [(abs_le.mp h).2]

theorem fourier_even_transfer (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ)
    (X : Ω → ℝ) (Y : Ξ → ℝ) (m : ℕ) (hm : 0 < m) (hme : Even m)
    (δ E : ℝ) (hδ : 0 ≤ δ)
    (hmom : ∀ k ≤ m, |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ δ)
    (hplus : ν.mean (fun y ↦ Real.exp ((4 * Real.pi) * Y y)) ≤ E)
    (hminus : ν.mean (fun y ↦ Real.exp (-(4 * Real.pi) * Y y)) ≤ E) :
    ‖μ.complexMean (fun x ↦ fourierPhase (X x)) -
      ν.complexMean (fun y ↦ fourierPhase (Y y))‖ ≤
        δ * (1 + m) * Real.exp (2 * Real.pi) + 4 * m * E * (1 / 2 : ℝ) ^ m := by
  have hmn : m - 1 + 1 = m := by omega
  have htransfer := fourier_moment_transfer μ ν X Y (m - 1) δ hδ
    (fun k hk ↦ hmom k (by omega))
  rw [hmn] at htransfer
  have hactual := even_moment_mean_le μ ν X Y m hme δ (hmom m le_rfl)
  have hmodel := mean_abs_power_le_exponential ν Y (4 * Real.pi) (by positivity) m
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have hscale : 0 ≤ (m.factorial : ℝ) / (4 * Real.pi) ^ m := by positivity
  have hmodel' : ν.mean (fun y ↦ |Y y| ^ m) ≤
      (m.factorial : ℝ) / (4 * Real.pi) ^ m * (2 * E) := by
    exact hmodel.trans (mul_le_mul_of_nonneg_left (by linarith) hscale)
  have hpref : (2 * Real.pi) ^ m / (m - 1).factorial =
      (m : ℝ) * ((2 * Real.pi) ^ m / m.factorial) := by
    have hf : (m.factorial : ℝ) = m * ((m - 1).factorial : ℝ) := by
      nth_rw 1 [← hmn]
      rw [Nat.factorial_succ, Nat.cast_mul]
      congr 1
      exact_mod_cast hmn
    rw [hf]
    field_simp
  have hpref_le : (2 * Real.pi) ^ m / (m - 1).factorial ≤
      m * Real.exp (2 * Real.pi) := by
    rw [hpref]
    exact mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (2 * Real.pi) (by positivity) m) (by positivity)
  have hpoly := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.pi) m
  have hrem : (2 * Real.pi) ^ m / (m - 1).factorial *
      (μ.mean (fun x ↦ |X x| ^ m) + ν.mean (fun y ↦ |Y y| ^ m)) ≤
        (2 * Real.pi) ^ m / (m - 1).factorial * δ + 4 * m * E * (1 / 2 : ℝ) ^ m := by
    have hsum : μ.mean (fun x ↦ |X x| ^ m) + ν.mean (fun y ↦ |Y y| ^ m) ≤
        δ + 4 * E * (m.factorial : ℝ) / (4 * Real.pi) ^ m := by
      calc
        _ ≤ δ + 2 * ν.mean (fun y ↦ |Y y| ^ m) := by linarith
        _ ≤ δ + 2 * ((m.factorial : ℝ) / (4 * Real.pi) ^ m * (2 * E)) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ (2 * Real.pi) ^ m / (m - 1).factorial *
          (δ + 4 * E * (m.factorial : ℝ) / (4 * Real.pi) ^ m) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
        rw [mul_add]
        congr 1
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hratio : (2 * Real.pi) ^ m / (4 * Real.pi) ^ m = (1 / 2 : ℝ) ^ m := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
        calc
          _ = 4 * m * E * ((2 * Real.pi) ^ m / (4 * Real.pi) ^ m) := by
            rw [hpref]
            field_simp
          _ = _ := by rw [hratio]
  have hδpoly := mul_le_mul_of_nonneg_left hpoly hδ
  have hδpref := mul_le_mul_of_nonneg_right hpref_le hδ
  nlinarith

end Erdos69.Elementary.FiniteLaw

end SourceModule18

/- Source module 19: ErdosProblems.Erdos69.ExponentialMoments -/
section SourceModule19
/-
# Exponential moments of the finite independent model
-/

open scoped BigOperators

namespace Erdos69.Elementary

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem exp_le_one_add_add_square {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using hx)
  simp only [Real.norm_eq_abs, sq_abs] at h
  have hle := le_abs_self (Real.exp x - 1 - x)
  linarith

theorem mean_exp_le (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ)
    (hmean : μ.mean X = 0) (hsmall : ∀ x, |t * X x| ≤ 1) :
    μ.mean (fun x ↦ Real.exp (t * X x)) ≤
      Real.exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2)) := by
  calc
    μ.mean (fun x ↦ Real.exp (t * X x)) ≤
        μ.mean (fun x ↦ 1 + t * X x + (t * X x) ^ 2) :=
      μ.mean_mono (fun x ↦ exp_le_one_add_add_square (hsmall x))
    _ = 1 + t ^ 2 * μ.mean (fun x ↦ X x ^ 2) := by
      simp only [mul_pow, μ.mean_add, μ.mean_const, μ.mean_const_mul, hmean,
        mul_zero, add_zero]
    _ ≤ Real.exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2)) := by
      simpa only [add_comm] using Real.add_one_le_exp (t ^ 2 * μ.mean (fun x ↦ X x ^ 2))

theorem categorical_mean_exp_le {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : Fintype.card ι ≤ p) (c : ι → ℝ)
    (hzero : ∑ i, c i = 0) (t ε : ℝ)
    (hmass : ∑ i, |c i| ≤ ε) (hsmall : |t| * ε ≤ 1) :
    (categorical ι p hp hcard).mean (fun x ↦ Real.exp (t * optionalValue c x)) ≤
      Real.exp (t ^ 2 * ε ^ 2 / p) := by
  have hε : 0 ≤ ε := (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)).trans hmass
  have hm : (categorical ι p hp hcard).mean (optionalValue c) = 0 := by
    rw [categorical_mean, hzero, zero_div]
  have hs (x : Option ι) : |t * optionalValue c x| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left
      ((optionalValue_abs_le c x).trans hmass) (abs_nonneg t)).trans hsmall
  have hvar : (categorical ι p hp hcard).mean (fun x ↦ optionalValue c x ^ 2) ≤ ε ^ 2 / p := by
    rw [categorical_mean_square]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (sum_sq_le_mass_sq c).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)) hmass 2)
  calc
    _ ≤ Real.exp (t ^ 2 *
        (categorical ι p hp hcard).mean (fun x ↦ optionalValue c x ^ 2)) :=
      mean_exp_le _ _ t hm hs
    _ ≤ Real.exp (t ^ 2 * ε ^ 2 / p) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hvar (sq_nonneg t)

theorem independentProduct_mean_exp_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (X : ι → Ω → ℝ) (t : ℝ) :
    (independentProduct μ).mean (fun x ↦ Real.exp (t * ∑ i, X i (x i))) =
      ∏ i, (μ i).mean (fun x ↦ Real.exp (t * X i x)) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact independentProduct_mean_prod μ (fun i x ↦ Real.exp (t * X i x))

theorem independentProduct_mean_exp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (X : ι → Ω → ℝ) (t : ℝ) (v : ι → ℝ)
    (hlocal : ∀ i, (μ i).mean (fun x ↦ Real.exp (t * X i x)) ≤ Real.exp (v i)) :
    (independentProduct μ).mean (fun x ↦ Real.exp (t * ∑ i, X i (x i))) ≤
      Real.exp (∑ i, v i) := by
  rw [independentProduct_mean_exp_sum, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun i _ ↦ (μ i).mean_nonneg (fun x ↦ (Real.exp_pos _).le))
    (fun i _ ↦ hlocal i)

end FiniteLaw

end Erdos69.Elementary

end SourceModule19

/- Source module 20: ErdosProblems.Erdos69.SmallPrimeFourier -/
section SourceModule20
/- # Quantitative characteristic-function comparison on an affine progression -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ]

theorem categorical_product_mean_exp_le (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (hzero : ∑ i, c i = 0)
    (t ε : ℝ) (hmass : ∑ i, |c i| ≤ ε) (hsmall : |t| * ε ≤ 1) :
    (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
      (fun x ↦ Real.exp (t * ∑ j, optionalValue c (x j))) ≤
        Real.exp (t ^ 2 * ε ^ 2 * ∑ j, (1 : ℝ) / p j) := by
  have h := independentProduct_mean_exp_le
    (fun j ↦ categorical ι (p j) (hp j) (hc j)) (fun _ ↦ optionalValue c) t
    (fun j ↦ t ^ 2 * ε ^ 2 / p j)
    (fun j ↦ categorical_mean_exp_le (p j) (hp j) (hc j) c hzero t ε hmass hsmall)
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem affine_fourier_transfer (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (hzero : ∑ i, c i = 0)
    (ε B : ℝ) (hmass : ∑ i, |c i| ≤ ε) (hsmall : 4 * Real.pi * ε ≤ 1)
    (hB : 1 ≤ B) (hsize : (Fintype.card ρ : ℝ) * ε ≤ B)
    (T : ℕ) (hT : 0 < T) (m : ℕ) (hm : 0 < m) (hme : Even m) :
    ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
        (∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0))) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).complexMean
        (fun x ↦ fourierPhase (∑ j, optionalValue c (x j)))‖ ≤
      (B ^ m / T) * (1 + m) * Real.exp (2 * Real.pi) +
        4 * m * Real.exp ((4 * Real.pi) ^ 2 * ε ^ 2 * ∑ j, (1 : ℝ) / p j) *
          (1 / 2 : ℝ) ^ m := by
  let μ := uniform T hT
  let ν := independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))
  let X : Fin T → ℝ := fun t ↦
    ∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0)
  let Y : (ρ → Option ι) → ℝ := fun x ↦ ∑ j, optionalValue c (x j)
  have hBn : 0 ≤ B := by linarith
  have hmoment (k : ℕ) (hk : k ≤ m) :
      |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ B ^ m / T := by
    have h := affine_moment_error p hp hcop Q b hQ s hs hc c T hT k
    apply h.trans
    calc
      _ ≤ (1 : ℝ) / T * B ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans hsize
      _ ≤ (1 : ℝ) / T * B ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hk) (by positivity)
      _ = _ := by ring
  have hplus := categorical_product_mean_exp_le p hp hc c hzero (4 * Real.pi) ε hmass
    (by simpa only [abs_of_pos (by positivity : 0 < 4 * Real.pi)] using hsmall)
  have hminus := categorical_product_mean_exp_le p hp hc c hzero (-(4 * Real.pi)) ε hmass
    (by simpa only [abs_neg, abs_of_pos (by positivity : 0 < 4 * Real.pi)] using hsmall)
  simp only [neg_sq] at hminus
  exact fourier_even_transfer μ ν X Y m hm hme (B ^ m / T) _ (by positivity)
    hmoment hplus hminus

end Erdos69.Elementary.FiniteLaw

end SourceModule20

/- Source module 21: ErdosProblems.Erdos69.FourierDeficit -/
section SourceModule21
/-
# A quantitative deficit for the independent characteristic function
-/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem complexMean_re (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    (μ.complexMean f).re = μ.mean (fun x ↦ (f x).re) := by
  simp [complexMean, mean, Complex.mul_re]

theorem complexMean_im (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    (μ.complexMean f).im = μ.mean (fun x ↦ (f x).im) := by
  simp [complexMean, mean, Complex.mul_im]

theorem complexMean_norm_sq (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    ‖μ.complexMean f‖ ^ 2 =
      μ.mean (fun x ↦ (f x).re) ^ 2 + μ.mean (fun x ↦ (f x).im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, complexMean_re, complexMean_im]
  ring

theorem mean_pair_phaseDeficit (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.mean (fun x ↦ μ.mean (fun y ↦ phaseDeficit (X x) (X y))) =
      1 - ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ^ 2 := by
  rw [complexMean_norm_sq]
  simp only [phaseDeficit, fourierPhase_sub_realPart, mean_sub, mean_add,
    mean_const, mean_const_mul, mean_mul_const]
  ring

theorem two_point_deficit_le (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (a b : Ω) (hab : a ≠ b) :
    2 * μ.mass a * μ.mass b * phaseDeficit (X a) (X b) ≤
      1 - ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ ^ 2 := by
  classical
  let F : Ω × Ω → ℝ := fun z ↦ μ.mass z.1 * μ.mass z.2 * phaseDeficit (X z.1) (X z.2)
  have hnonneg (z : Ω × Ω) : 0 ≤ F z :=
    mul_nonneg (mul_nonneg (μ.nonneg _) (μ.nonneg _)) (phaseDeficit_nonneg _ _)
  have hpairs : (a, b) ≠ (b, a) := fun h ↦ hab (congrArg Prod.fst h)
  have hsum : (∑ z ∈ ({(a, b), (b, a)} : Finset (Ω × Ω)), F z) ≤ ∑ z, F z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun z _ _ ↦ hnonneg z)
  have hleft : (∑ z ∈ ({(a, b), (b, a)} : Finset (Ω × Ω)), F z) =
      2 * μ.mass a * μ.mass b * phaseDeficit (X a) (X b) := by
    simp only [Finset.sum_pair hpairs, F, phaseDeficit_symm (X b) (X a)]
    ring
  have hright : (∑ z, F z) =
      μ.mean (fun x ↦ μ.mean (fun y ↦ phaseDeficit (X x) (X y))) := by
    simp [F, Fintype.sum_prod_type, mean, Finset.mul_sum, mul_assoc]
  rw [hleft, hright, mean_pair_phaseDeficit] at hsum
  exact hsum

theorem categorical_fourier_deficit {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : 2 * Fintype.card ι ≤ p) (c : ι → ℝ)
    (i : ι) (hi : |c i| ≤ 1 / 2) :
    8 * c i ^ 2 / p ≤
      1 - ‖(categorical ι p hp (by omega)).complexMean
        (fun x ↦ fourierPhase (optionalValue c x))‖ ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcR : 2 * (Fintype.card ι : ℝ) ≤ p := by exact_mod_cast hcard
  have hhalf : (1 / 2 : ℝ) ≤ 1 - (Fintype.card ι : ℝ) / p := by
    have h := (div_le_iff₀ hpR).mpr (show (Fintype.card ι : ℝ) ≤ (1 / 2 : ℝ) * p by linarith)
    linarith
  have hdef := two_point_deficit_le (categorical ι p hp (by omega))
    (optionalValue c) none (some i) (by simp)
  simp only [categorical, optionalValue] at hdef
  rw [phaseDeficit_symm 0 (c i), phaseDeficit, sub_zero] at hdef
  have hlow := fourierPhase_deficit_lower hi
  have hnonneg := sub_nonneg.mpr (fourierPhase_realPart_le_one (c i))
  have hweight : (1 : ℝ) / p ≤ 2 * (1 - (Fintype.card ι : ℝ) / p) * (1 / p) := by
    calc
      (1 : ℝ) / p = (2 * (1 / 2)) * (1 / p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith :
        2 * (1 / 2 : ℝ) ≤ 2 * (1 - (Fintype.card ι : ℝ) / p)) (by positivity)
  calc
    8 * c i ^ 2 / p ≤ (1 / p) * (1 - (fourierPhase (c i)).re) := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        mul_le_mul_of_nonneg_right hlow (inv_nonneg.mpr hpR.le)
    _ ≤ 2 * (1 - (Fintype.card ι : ℝ) / p) * (1 / p) *
        (1 - (fourierPhase (c i)).re) := mul_le_mul_of_nonneg_right hweight hnonneg
    _ ≤ _ := hdef

theorem categorical_fourier_norm_le {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 0 < p) (hcard : 2 * Fintype.card ι ≤ p) (c : ι → ℝ)
    (i : ι) (hi : |c i| ≤ 1 / 2) :
    ‖(categorical ι p hp (by omega)).complexMean
      (fun x ↦ fourierPhase (optionalValue c x))‖ ≤ Real.exp (-4 * c i ^ 2 / p) := by
  have hdef := categorical_fourier_deficit p hp hcard c i hi
  have hexp := Real.one_sub_le_exp_neg (8 * c i ^ 2 / p)
  have heq : Real.exp (-(8 * c i ^ 2 / p)) = (Real.exp (-4 * c i ^ 2 / p)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [heq] at hexp
  have hnonneg := norm_nonneg ((categorical ι p hp (by omega)).complexMean
    (fun x ↦ fourierPhase (optionalValue c x)))
  have hpos := Real.exp_pos (-4 * c i ^ 2 / p)
  nlinarith

end Erdos69.Elementary.FiniteLaw

end SourceModule21

/- Source module 22: ErdosProblems.Erdos69.FourierProduct -/
section SourceModule22
/- # Decay of the independent prime characteristic function -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem fourierPhase_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    fourierPhase (∑ i ∈ s, f i) = ∏ i ∈ s, fourierPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierPhase_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourierPhase_add, ih]

namespace FiniteLaw

variable {ρ ι Ω : Type*} [Fintype ρ] [Fintype ι] [Fintype Ω] [DecidableEq ρ]

theorem independentProduct_fourier_sum (μ : ρ → FiniteLaw Ω) (X : ρ → Ω → ℝ) :
    (independentProduct μ).complexMean (fun x ↦ fourierPhase (∑ j, X j (x j))) =
      ∏ j, (μ j).complexMean (fun x ↦ fourierPhase (X j x)) := by
  simp_rw [fourierPhase_sum]
  exact independentProduct_complexMean_prod μ (fun j x ↦ fourierPhase (X j x))

theorem categorical_product_fourier_le (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (s : Finset ρ)
    (hs : ∀ j ∈ s, 2 * Fintype.card ι ≤ p j)
    (c : ι → ℝ) (i : ι) (hi : |c i| ≤ 1 / 2) :
    ‖(independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).complexMean
      (fun x ↦ fourierPhase (∑ j, optionalValue c (x j)))‖ ≤
        Real.exp (-4 * c i ^ 2 * ∑ j ∈ s, (1 : ℝ) / p j) := by
  classical
  rw [independentProduct_fourier_sum (fun j ↦ categorical ι (p j) (hp j) (hc j))
    (fun _ ↦ optionalValue c), norm_prod]
  have hlocal (j : ρ) :
      ‖(categorical ι (p j) (hp j) (hc j)).complexMean
          (fun x ↦ fourierPhase (optionalValue c x))‖ ≤
        if j ∈ s then Real.exp (-4 * c i ^ 2 / p j) else 1 := by
    split_ifs with hj
    · exact categorical_fourier_norm_le (p j) (hp j) (hs j hj) c i hi
    · exact norm_mean_fourierPhase_le_one _ _
  calc
    _ ≤ ∏ j, if j ∈ s then Real.exp (-4 * c i ^ 2 / p j) else 1 :=
      Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ hlocal j)
    _ = ∏ j ∈ s, Real.exp (-4 * c i ^ 2 / p j) := Finset.prod_ite_mem_eq _ _
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end FiniteLaw

end Erdos69.Elementary

end SourceModule22

/- Source module 23: BoundedGaps.Maynard.PrimeMertens -/
section SourceModule23
noncomputable section

/-
# A bounded-error prime Mertens estimate

This proves the arithmetic input needed by the `kappa = 1` specialization of
GGPY2009, Lemma 4.  The von Mangoldt harmonic sum is compared with
`log (n !) / n`; the contribution from non-prime prime powers is then removed
using its summability in pinned Mathlib.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction

noncomputable def mangoldtHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)

noncomputable def primeLogHarmonicSum (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)

private noncomputable def mangoldtFloorAverage (n : ℕ) : ℝ :=
  (∑ d ∈ Ioc 0 n,
    ArithmeticFunction.vonMangoldt d * (n / d : ℕ)) / (n : ℝ)

private noncomputable def nonprimeMangoldtHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n,
    (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)

theorem sum_Ioc_log_eq_log_factorial (n : ℕ) :
    (∑ m ∈ Ioc 0 n, Real.log m) = Real.log n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ,
        Nat.cast_mul, Real.log_mul]
      · ring
      · exact_mod_cast Nat.succ_ne_zero n
      · exact_mod_cast Nat.factorial_ne_zero n

theorem sum_Ioc_log_eq_mangoldt_floor (n : ℕ) :
    (∑ m ∈ Ioc 0 n, Real.log m) =
      ∑ d ∈ Ioc 0 n,
        ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
  calc
    (∑ m ∈ Ioc 0 n, Real.log m) =
        ∑ m ∈ Ioc 0 n,
          (ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta) m := by
      apply sum_congr rfl
      intro m hm
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl
    _ = _ := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
      ArithmeticFunction.vonMangoldt n

private theorem floorAverage_le_harmonic {n : ℕ} (hn : 0 < n) :
    mangoldtFloorAverage n ≤ mangoldtHarmonicSum n := by
  unfold mangoldtFloorAverage mangoldtHarmonicSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro d hd
  have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hfloor : ((n / d : ℕ) : ℝ) / n ≤ 1 / (d : ℝ) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hdPos)]
    norm_cast
    simpa only [one_mul] using Nat.div_mul_le_self n d
  calc
    ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) =
        ArithmeticFunction.vonMangoldt d * (((n / d : ℕ) : ℝ) / n) := by
      ring
    _ ≤ ArithmeticFunction.vonMangoldt d * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d / (d : ℝ) := by ring

private theorem harmonic_le_floorAverage_add_psi {n : ℕ} (hn : 0 < n) :
    mangoldtHarmonicSum n ≤ mangoldtFloorAverage n + Chebyshev.psi n / n := by
  unfold mangoldtHarmonicSum mangoldtFloorAverage
  calc
    (∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)) ≤
        ∑ d ∈ Ioc 0 n,
          (ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) +
            ArithmeticFunction.vonMangoldt d / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hmod := Nat.mod_lt n hdPos
      have hdecomp := Nat.div_add_mod n d
      have hnd : n ≤ (n / d + 1) * d := by
        calc
          n = d * (n / d) + n % d := hdecomp.symm
          _ ≤ d * (n / d) + d := Nat.add_le_add_left hmod.le _
          _ = (n / d + 1) * d := by
            rw [Nat.add_mul, one_mul, Nat.mul_comm (n / d) d]
      have hfloor : (1 : ℝ) / d ≤
          ((n / d : ℕ) : ℝ) / n + 1 / n := by
        calc
          (1 : ℝ) / d ≤ ((n / d + 1 : ℕ) : ℝ) / n := by
            rw [div_le_div_iff₀ (by exact_mod_cast hdPos) (by exact_mod_cast hn)]
            norm_cast
            simpa only [one_mul] using hnd
          _ = ((n / d : ℕ) : ℝ) / n + 1 / n := by
            push_cast
            ring
      calc
        ArithmeticFunction.vonMangoldt d / (d : ℝ) =
            ArithmeticFunction.vonMangoldt d * (1 / (d : ℝ)) := by ring
        _ ≤ ArithmeticFunction.vonMangoldt d *
            (((n / d : ℕ) : ℝ) / n + 1 / n) :=
          mul_le_mul_of_nonneg_left hfloor ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt d * (n / d : ℕ) / (n : ℝ) +
            ArithmeticFunction.vonMangoldt d / (n : ℝ) := by ring
    _ = (∑ d ∈ Ioc 0 n,
          ArithmeticFunction.vonMangoldt d * (n / d : ℕ)) / (n : ℝ) +
        Chebyshev.psi n / n := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      congr 2
      simp [Chebyshev.psi]

private theorem log_sub_one_le_floorAverage {n : ℕ} (hn : 0 < n) :
    Real.log n - 1 ≤ mangoldtFloorAverage n := by
  have hsum := sum_Ioc_log_eq_mangoldt_floor n
  have hfactorial := sum_Ioc_log_eq_log_factorial n
  have hstirling := Stirling.le_log_factorial_stirling hn.ne'
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hbasic : (n : ℝ) * Real.log n - n ≤ Real.log n ! := by
    linarith
  unfold mangoldtFloorAverage
  rw [← hsum, hfactorial]
  apply (le_div_iff₀ (by exact_mod_cast hn)).2
  nlinarith

private theorem floorAverage_le_log {n : ℕ} (hn : 0 < n) :
    mangoldtFloorAverage n ≤ Real.log n := by
  have hsum := sum_Ioc_log_eq_mangoldt_floor n
  have hfactorial := sum_Ioc_log_eq_log_factorial n
  have hfacReal : (n ! : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hlogFac : Real.log (n ! : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hfacReal
  rw [Real.log_pow] at hlogFac
  unfold mangoldtFloorAverage
  rw [← hsum, hfactorial]
  apply (div_le_iff₀ (by exact_mod_cast hn)).2
  nlinarith

theorem abs_mangoldtHarmonicSum_sub_log_le (n : ℕ) :
    |mangoldtHarmonicSum n - Real.log n| ≤ Real.log 4 + 4 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog4 : (0 : ℝ) ≤ Real.log (4 : ℝ) :=
        Real.log_nonneg (by norm_num)
      linarith
    simpa [mangoldtHarmonicSum] using hC
  have hlowerFloor := log_sub_one_le_floorAverage hn
  have hupperFloor := floorAverage_le_log hn
  have hfloorLe := floorAverage_le_harmonic hn
  have hharmonicUpper := harmonic_le_floorAverage_add_psi hn
  have hpsi := Chebyshev.psi_le_const_mul_self
    (show (0 : ℝ) ≤ n by positivity)
  have hpsiDiv : Chebyshev.psi n / n ≤ Real.log 4 + 4 := by
    apply (div_le_iff₀ (by exact_mod_cast hn)).2
    simpa [mul_comm] using hpsi
  rw [abs_le]
  constructor
  · have hC : (1 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog4 : (0 : ℝ) ≤ Real.log (4 : ℝ) :=
        Real.log_nonneg (by norm_num)
      linarith
    linarith
  · linarith

theorem exists_uniform_abs_mangoldtHarmonicSum_sub_log :
    ∃ C : ℝ, ∀ n : ℕ,
      |mangoldtHarmonicSum n - Real.log n| ≤ C :=
  ⟨Real.log 4 + 4, abs_mangoldtHarmonicSum_sub_log_le⟩

private theorem mangoldtHarmonicSum_eq_prime_add_nonprime (n : ℕ) :
    mangoldtHarmonicSum n =
      primeLogHarmonicSum n + nonprimeMangoldtHarmonicSum n := by
  classical
  unfold mangoldtHarmonicSum primeLogHarmonicSum
    nonprimeMangoldtHarmonicSum
  calc
    (∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)) =
        ∑ d ∈ Ioc 0 n,
          ((if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ) +
            (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hp : d.Prime <;> simp [hp]
    _ = (∑ d ∈ Ioc 0 n,
          (if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ)) +
        ∑ d ∈ Ioc 0 n,
          (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      calc
        (∑ d ∈ Ioc 0 n,
            (if d.Prime then ArithmeticFunction.vonMangoldt d else 0) / (d : ℝ)) =
            ∑ p ∈ (Ioc 0 n).filter Nat.Prime,
              ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
          simp only [ite_div, zero_div, Finset.sum_filter]
        _ = ∑ p ∈ Nat.primesLE n,
              ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
          apply Finset.sum_congr
          · rw [Nat.primesLE_eq_filter_Icc_one]
            ext p
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨hp, hpn⟩, hprime⟩
              exact ⟨⟨Nat.succ_le_iff.mpr hp, hpn⟩, hprime⟩
            · rintro ⟨⟨hp, hpn⟩, hprime⟩
              exact ⟨⟨Nat.succ_le_iff.mp hp, hpn⟩, hprime⟩
          · intro p hp
            rfl
        _ = ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime
            (Nat.prime_of_mem_primesLE hp)]

private theorem summable_nonprimeMangoldtTerm :
    Summable fun n : ℕ =>
      (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) / (n : ℝ) := by
  let : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  have hcast : ∀ n : ℕ, (n : ZMod 1) = 0 :=
    fun n => Subsingleton.elim _ _
  simpa [ArithmeticFunction.vonMangoldt.residueClass, hcast] using
    (ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (0 : ZMod 1))

theorem exists_uniform_abs_primeLogHarmonicSum_sub_log :
    ∃ C : ℝ, ∀ n : ℕ,
      |primeLogHarmonicSum n - Real.log n| ≤ C := by
  let f : ℕ → ℝ := fun d =>
    (if d.Prime then 0 else ArithmeticFunction.vonMangoldt d) / (d : ℝ)
  refine ⟨Real.log 4 + 4 + ∑' d : ℕ, f d, fun n => ?_⟩
  have hfNonneg (d : ℕ) : 0 ≤ f d := by
    unfold f
    split_ifs <;> positivity
  have hfSummable : Summable f := summable_nonprimeMangoldtTerm
  have hnonprimeNonneg : 0 ≤ nonprimeMangoldtHarmonicSum n := by
    change 0 ≤ ∑ d ∈ Ioc 0 n, f d
    exact Finset.sum_nonneg fun d hd => hfNonneg d
  have hnonprimeLe : nonprimeMangoldtHarmonicSum n ≤ ∑' d : ℕ, f d := by
    change (∑ d ∈ Ioc 0 n, f d) ≤ ∑' d : ℕ, f d
    exact hfSummable.sum_le_tsum (Ioc 0 n) fun d hd => hfNonneg d
  have hsplit := mangoldtHarmonicSum_eq_prime_add_nonprime n
  have heq : primeLogHarmonicSum n - Real.log n =
      (mangoldtHarmonicSum n - Real.log n) -
        nonprimeMangoldtHarmonicSum n := by
    rw [hsplit]
    ring
  rw [heq]
  calc
    |(mangoldtHarmonicSum n - Real.log n) -
        nonprimeMangoldtHarmonicSum n| ≤
        |mangoldtHarmonicSum n - Real.log n| +
          |nonprimeMangoldtHarmonicSum n| := abs_sub _ _
    _ ≤ (Real.log 4 + 4) + (∑' d : ℕ, f d) := by
      apply add_le_add (abs_mangoldtHarmonicSum_sub_log_le n)
      rwa [abs_of_nonneg hnonprimeNonneg]

end BoundedGaps.Maynard

end
end SourceModule23

/- Source module 24: ErdosProblems.Erdos697.Erdos697PrimeHarmonic -/
section SourceModule24
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
# Reciprocal-prime Mertens estimate for Erdős Problem 697

The pinned analytic dependency proves Mertens' estimate with logarithmic
prime weights.  Finite Abel summation removes that logarithm here.  The
result is the bounded-error form

`∑_{p ≤ x} 1/p = log (log x) + O(1)`,

with all constants quantified and no additional assumptions.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos697.PrimeHarmonic

noncomputable section

/-- The reciprocal-prime sum up to a natural endpoint. -/
def sum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

/-- Abel summation converts the logarithmically weighted prime sum into the
ordinary reciprocal-prime sum. -/
theorem sum_eq_primeLogHarmonic_abel {x : ℕ} (hx : 2 ≤ x) :
    sum x =
      BoundedGaps.Maynard.primeLogHarmonicSum x / Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2) := by
  classical
  let c : ℕ → ℝ := fun n =>
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hCumulative (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        BoundedGaps.Maynard.primeLogHarmonicSum m := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    calc
      (∑ n ∈ Finset.Icc 0 m, c n) =
          ∑ n ∈ (Finset.Icc 0 m).filter Nat.Prime,
            Real.log (n : ℝ) / (n : ℝ) := by
              simp [c, Finset.sum_filter]
      _ = ∑ p ∈ Nat.primesLE m,
            Real.log (p : ℝ) / (p : ℝ) := by
              rw [Nat.primesLE_eq_filter_Icc_zero]
  have hWeighted :
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) = sum x := by
    unfold sum
    calc
      (∑ n ∈ Finset.Icc 0 x, (Real.log (n : ℝ))⁻¹ * c n) =
          ∑ n ∈ (Finset.Icc 0 x).filter Nat.Prime,
            (1 : ℝ) / n := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro n hn
              by_cases hp : n.Prime
              · have hlog : Real.log (n : ℝ) ≠ 0 := hp.log_ne_zero
                simp [c, hp]
                field_simp
              · simp [c, hp]
      _ = ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p := by
            rw [Nat.primesLE_eq_filter_Icc_zero]
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDifferentiable : ∀ t ∈ Set.Icc (2 : ℝ) (x : ℝ),
      DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1])
      (by linarith [ht.1]) (by linarith [ht.1])
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ => (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hAbel := sum_mul_eq_sub_integral_mul₁ c
    (f := fun t : ℝ => (Real.log t)⁻¹)
    (by norm_num [c]) (by norm_num [c]) (x : ℝ)
    hDifferentiable hDerivIntegrable
  rw [← intervalIntegral.integral_of_le hxReal] at hAbel
  have hIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
          deriv (fun u : ℝ => (Real.log u)⁻¹) t *
            ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    change deriv (fun u : ℝ => (Real.log u)⁻¹) t *
        (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
      -(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
        (t * Real.log t ^ 2))
    rw [hCumulative, Real.deriv_inv_log_apply]
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    field_simp
  rw [Nat.floor_natCast, hWeighted, hCumulative, hIntegral] at hAbel
  calc
    sum x =
        (Real.log (x : ℝ))⁻¹ *
            BoundedGaps.Maynard.primeLogHarmonicSum x -
          -(∫ t in (2 : ℝ)..(x : ℝ),
            BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
              (t * Real.log t ^ 2)) := hAbel
    _ = BoundedGaps.Maynard.primeLogHarmonicSum x /
          Real.log (x : ℝ) +
        ∫ t in (2 : ℝ)..(x : ℝ),
          BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
            (t * Real.log t ^ 2) := by
      simp only [div_eq_mul_inv]
      ring

private theorem intervalIntegrable_primeLogHarmonic_div
    {x : ℕ} (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t : ℝ =>
        BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
          (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
  classical
  let c : ℕ → ℝ := fun n =>
    if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0
  have hCumulative (m : ℕ) :
      (∑ n ∈ Finset.Icc 0 m, c n) =
        BoundedGaps.Maynard.primeLogHarmonicSum m := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    calc
      (∑ n ∈ Finset.Icc 0 m, c n) =
          ∑ n ∈ (Finset.Icc 0 m).filter Nat.Prime,
            Real.log (n : ℝ) / (n : ℝ) := by
              simp [c, Finset.sum_filter]
      _ = ∑ p ∈ Nat.primesLE m,
            Real.log (p : ℝ) / (p : ℝ) := by
              rw [Nat.primesLE_eq_filter_Icc_zero]
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hDerivIntegrable : IntegrableOn
      (deriv fun t : ℝ => (Real.log t)⁻¹)
      (Set.Icc (2 : ℝ) (x : ℝ)) := by
    refine ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousWithinAt.congr ?_
        (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one ?_ ?_)
      · linarith [ht.1]
      · linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hProductIntegrable : IntegrableOn
      (fun t : ℝ =>
        deriv (fun u : ℝ => (Real.log u)⁻¹) t *
          ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)
      (Set.Icc (2 : ℝ) (x : ℝ)) :=
    integrableOn_mul_sum_Icc c (a := (2 : ℝ)) (b := (x : ℝ))
      (m := 0) (by norm_num) hDerivIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxReal]
  apply hProductIntegrable.neg.congr_fun _ measurableSet_Icc
  intro t ht
  change -(deriv (fun u : ℝ => (Real.log u)⁻¹) t *
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)) = _
  rw [hCumulative, Real.deriv_inv_log_apply]
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1])
      (by linarith [ht.1])
  field_simp

/-- Mertens' reciprocal-prime theorem with one uniform absolute constant. -/
theorem exists_uniform_abs_sum_sub_log_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      |sum x - Real.log (Real.log (x : ℝ))| ≤ C := by
  obtain ⟨C₀, hC₀⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  let C : ℝ :=
    |1 - Real.log (Real.log 2)| +
      C₀ / Real.log 2 + (C₀ + Real.log 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀nonneg : 0 ≤ C₀ := by
    exact (abs_nonneg
      (BoundedGaps.Maynard.primeLogHarmonicSum 2 - Real.log 2)).trans
        (hC₀ 2)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx
  have hxReal : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxOne : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hxOne
  rw [sum_eq_primeLogHarmonic_abel hx]
  let E : ℕ → ℝ := fun n =>
    BoundedGaps.Maynard.primeLogHarmonicSum n - Real.log n
  have hE (n : ℕ) : |E n| ≤ C₀ := hC₀ n
  let B : ℝ := C₀ + Real.log 2
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hsplitEndpoint :
      BoundedGaps.Maynard.primeLogHarmonicSum x /
          Real.log (x : ℝ) =
        1 + E x / Real.log (x : ℝ) := by
    dsimp [E]
    field_simp
    ring
  have hfloorLogError (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
      |Real.log (⌊t⌋₊ : ℝ) - Real.log t| ≤ Real.log 2 := by
    have hfloorNat : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht.1
    have hfloorPos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (by omega : 0 < ⌊t⌋₊)
    have htPos : 0 < t := by linarith [ht.1]
    have hfloorLe : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith [ht.1])
    have htLt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have haddLe : (⌊t⌋₊ : ℝ) + 1 ≤ 2 * (⌊t⌋₊ : ℝ) := by
      exact_mod_cast (show ⌊t⌋₊ + 1 ≤ 2 * ⌊t⌋₊ by omega)
    have htLe : t ≤ 2 * (⌊t⌋₊ : ℝ) := (le_of_lt htLt).trans haddLe
    have hlogFloorLe : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact hfloorPos)
        (by simp only [Set.mem_Ioi]; exact htPos) hfloorLe
    have htwoFloorPos : 0 < 2 * (⌊t⌋₊ : ℝ) := mul_pos (by norm_num) hfloorPos
    have hlogTLe : Real.log t ≤ Real.log (2 * (⌊t⌋₊ : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact htPos)
        (by simp only [Set.mem_Ioi]; exact htwoFloorPos) htLe
    rw [abs_of_nonpos (sub_nonpos.mpr hlogFloorLe)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hfloorPos.ne'] at hlogTLe
    linarith
  have hFloorNumerator (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
      |BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ - Real.log t| ≤ B := by
    have htri := abs_sub_le
      (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊)
      (Real.log (⌊t⌋₊ : ℝ)) (Real.log t)
    dsimp [B]
    exact htri.trans (add_le_add (hC₀ ⌊t⌋₊) (hfloorLogError t ht))
  have hMainIntegrable : IntervalIntegrable
      (fun t : ℝ => Real.log t / (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    have hden : t * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    fun_prop
  have hErrorIntegrable : IntervalIntegrable
      (fun t : ℝ =>
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2))
      volume (2 : ℝ) (x : ℝ) := by
    convert (intervalIntegrable_primeLogHarmonic_div hx).sub hMainIntegrable using 1
    ext t
    ring
  have hIntegralSplit :
      (∫ t in (2 : ℝ)..(x : ℝ),
        BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ /
          (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..(x : ℝ),
        (Real.log t) / (t * Real.log t ^ 2)) +
      (∫ t in (2 : ℝ)..(x : ℝ),
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2)) := by
    rw [← intervalIntegral.integral_add hMainIntegrable hErrorIntegrable]
    · apply intervalIntegral.integral_congr
      intro t _
      ring
  have hMainIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ),
        Real.log t / (t * Real.log t ^ 2)) =
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) := by
    calc
      (∫ t in (2 : ℝ)..(x : ℝ),
          Real.log t / (t * Real.log t ^ 2)) =
          ∫ t in (2 : ℝ)..(x : ℝ), t⁻¹ / Real.log t := by
            apply intervalIntegral.integral_congr
            intro t _
            by_cases ht0 : t = 0
            · simp [ht0]
            by_cases hlog : Real.log t = 0
            · simp [hlog]
            field_simp
      _ = Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) :=
        integral_inv_div_log (a := (2 : ℝ)) (b := (x : ℝ))
          (by norm_num) hxOne
  have hKernelIntegral :
      (∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹) =
        (Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹ := by
    calc
      (∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹) =
          ∫ t in (2 : ℝ)..(x : ℝ), t⁻¹ / Real.log t ^ 2 := by
            apply intervalIntegral.integral_congr
            intro t _
            by_cases ht0 : t = 0
            · simp [ht0]
            by_cases hlog : Real.log t = 0
            · simp [hlog]
            field_simp
      _ = (Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹ :=
        integral_inv_div_log_sq (a := (2 : ℝ)) (b := (x : ℝ))
          (by norm_num) hxOne
  have hKernelIntegrable : IntervalIntegrable
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹)
      volume (2 : ℝ) (x : ℝ) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    have htIcc : t ∈ Set.Icc (2 : ℝ) (x : ℝ) := by
      simpa [Set.uIcc_of_le hxReal] using ht
    have ht0 : t ≠ 0 := by linarith [htIcc.1]
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [htIcc.1])
        (by linarith [htIcc.1])
    have hden : t * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    fun_prop
  have hErrorIntegral :
      |∫ t in (2 : ℝ)..(x : ℝ),
        (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
          Real.log t) / (t * Real.log t ^ 2)| ≤ B / Real.log 2 := by
    have hMajorant := hKernelIntegrable.const_mul B
    have hPointwise (t : ℝ) (ht : t ∈ Set.Icc (2 : ℝ) (x : ℝ)) :
        ‖(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)‖ ≤
          B * (t * Real.log t ^ 2)⁻¹ := by
      have htOne : 1 < t := by linarith [ht.1]
      have hdenPos : 0 < t * Real.log t ^ 2 :=
        mul_pos (by linarith [ht.1]) (sq_pos_of_pos (Real.log_pos htOne))
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenPos, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hFloorNumerator t ht)
        (inv_nonneg.mpr hdenPos.le)
    calc
      |∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)| =
          ‖∫ t in (2 : ℝ)..(x : ℝ),
            (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
              Real.log t) / (t * Real.log t ^ 2)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          ‖(BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hxReal
      _ ≤ ∫ t in (2 : ℝ)..(x : ℝ),
          B * (t * Real.log t ^ 2)⁻¹ :=
            intervalIntegral.integral_mono_on hxReal hErrorIntegrable.norm
              hMajorant hPointwise
      _ = B * ((Real.log 2)⁻¹ - (Real.log (x : ℝ))⁻¹) := by
            rw [intervalIntegral.integral_const_mul, hKernelIntegral]
      _ ≤ B / Real.log 2 := by
            have hinvx : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hlogx.le
            have := mul_le_mul_of_nonneg_left
              (sub_le_self (Real.log 2)⁻¹ hinvx) hBnonneg
            simpa [div_eq_mul_inv] using this
  have hEndpointError : |E x / Real.log (x : ℝ)| ≤ C₀ / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogx]
    apply div_le_div₀ hC₀nonneg (hE x) hlog2
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hx)
  rw [hsplitEndpoint, hIntegralSplit, hMainIntegral]
  have hrewrite :
      1 + E x / Real.log (x : ℝ) +
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) +
            (∫ t in (2 : ℝ)..(x : ℝ),
              (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
                Real.log t) / (t * Real.log t ^ 2))) -
          Real.log (Real.log (x : ℝ)) =
        (1 - Real.log (Real.log 2)) +
          E x / Real.log (x : ℝ) +
          (∫ t in (2 : ℝ)..(x : ℝ),
            (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
              Real.log t) / (t * Real.log t ^ 2)) := by ring
  rw [hrewrite]
  calc
    |(1 - Real.log (Real.log 2)) + E x / Real.log (x : ℝ) +
        (∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2))| ≤
      |1 - Real.log (Real.log 2)| + |E x / Real.log (x : ℝ)| +
        |∫ t in (2 : ℝ)..(x : ℝ),
          (BoundedGaps.Maynard.primeLogHarmonicSum ⌊t⌋₊ -
            Real.log t) / (t * Real.log t ^ 2)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |1 - Real.log (Real.log 2)| + C₀ / Real.log 2 +
        B / Real.log 2 := by linarith
    _ = C := by rfl

end

end Erdos697.PrimeHarmonic

end SourceModule24

/- Source module 25: ErdosProblems.Erdos69.PrimeMassBounds -/
section SourceModule25
/-
# Elementary reciprocal-prime bounds

We reuse the repository's unconditional, bounded-error Mertens theorem.
Its proof uses the von Mangoldt divisor identity and finite Abel summation.
-/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, (1 : ℝ) / p

theorem exists_primeReciprocal_error_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C := by
  exact Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log

theorem reciprocal_primeFactors_le_cutoff (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R) :
    (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) ≤
      primeReciprocalSum R + Real.log Q / ((R : ℝ) * Real.log 2) := by
  classical
  let small := Q.primeFactors.filter (fun p ↦ p ≤ R)
  let large := Q.primeFactors.filter (fun p ↦ ¬p ≤ R)
  have hsmall : small ⊆ Nat.primesLE R := by
    intro p hp
    obtain ⟨hpQ, hpR⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpR, (Nat.mem_primeFactors.mp hpQ).1⟩
  have hs : (∑ p ∈ small, (1 : ℝ) / p) ≤ primeReciprocalSum R :=
    Finset.sum_le_sum_of_subset_of_nonneg hsmall (fun _ _ _ ↦ by positivity)
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hlarge : (∑ p ∈ large, (1 : ℝ) / p) ≤ (large.card : ℝ) / R := by
    calc
      _ ≤ ∑ _p ∈ large, (1 : ℝ) / R := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : R < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le hRR (by exact_mod_cast hpR.le)
      _ = _ := by simp [div_eq_mul_inv]
  have hcard : (large.card : ℝ) ≤ omegaCount Q := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hlog := omegaCount_mul_log_two_le hQ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have homega : (omegaCount Q : ℝ) ≤ Real.log Q / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  have hl : (∑ p ∈ large, (1 : ℝ) / p) ≤ Real.log Q / ((R : ℝ) * Real.log 2) := by
    calc
      _ ≤ (large.card : ℝ) / R := hlarge
      _ ≤ (Real.log Q / Real.log 2) / R :=
        div_le_div_of_nonneg_right (hcard.trans homega) hRR.le
      _ = _ := by ring
  have hsplit : (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) =
      (∑ p ∈ small, (1 : ℝ) / p) + ∑ p ∈ large, (1 : ℝ) / p := by
    exact (Finset.sum_filter_add_sum_filter_not Q.primeFactors (fun p ↦ p ≤ R) _).symm
  rw [hsplit]
  exact add_le_add hs hl

noncomputable def goodPrimes (Q L y : ℕ) : Finset ℕ :=
  (Nat.primesLE y).filter (fun p ↦ L < p ∧ ¬p ∣ Q)

theorem goodPrime_reciprocal_lower (Q L y : ℕ) (hQ : 0 < Q) :
    primeReciprocalSum y - primeReciprocalSum L -
      (∑ p ∈ Q.primeFactors, (1 : ℝ) / p) ≤
        ∑ p ∈ goodPrimes Q L y, (1 : ℝ) / p := by
  classical
  have hcover : Nat.primesLE y ⊆ goodPrimes Q L y ∪ Nat.primesLE L ∪ Q.primeFactors := by
    intro p hp
    by_cases hL : L < p
    · by_cases hd : p ∣ Q
      · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primesLE.mp hp).2, hd, hQ.ne'⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hp, hL, hd⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Nat.mem_primesLE.mpr ⟨by omega, (Nat.mem_primesLE.mp hp).2⟩))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ ↦ (1 : ℝ) / p)
    hcover (fun p _ _ ↦ by positivity)
  have hule (s t : Finset ℕ) : (∑ p ∈ s ∪ t, (1 : ℝ) / p) ≤
      (∑ p ∈ s, (1 : ℝ) / p) + ∑ p ∈ t, (1 : ℝ) / p := by
    have heq := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun p : ℕ ↦ (1 : ℝ) / p)
    have hn : 0 ≤ ∑ p ∈ s ∩ t, (1 : ℝ) / p := Finset.sum_nonneg (fun _ _ ↦ by positivity)
    linarith
  have hu₁ := hule (goodPrimes Q L y ∪ Nat.primesLE L) Q.primeFactors
  have hu₂ := hule (goodPrimes Q L y) (Nat.primesLE L)
  unfold primeReciprocalSum
  linarith

end Erdos69.Elementary

end SourceModule25

/- Source module 26: ErdosProblems.Erdos69.BinarySeries -/
section SourceModule26
open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

/-- The binary tail starting at `n`, with its first term unscaled. -/
def binaryTail (n : ℕ) : ℝ := ∑' k : ℕ, (omegaCount (n + k) : ℝ) / 2 ^ k

private theorem scaled_shift_term (n k : ℕ) :
    (2 : ℝ) ^ n * ((omegaCount (k + n) : ℝ) / 2 ^ (k + n)) =
      (omegaCount (n + k) : ℝ) / 2 ^ k := by
  rw [pow_add, Nat.add_comm k n]
  field_simp

theorem summable_binaryTail (n : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (n + k) : ℝ) / 2 ^ k) := by
  have h := ((summable_nat_add_iff n).2 summable_omegaCount_div_two_pow).mul_left
    ((2 : ℝ) ^ n)
  exact h.congr (scaled_shift_term n)

theorem binaryTail_eq_scaled_shift (n : ℕ) :
    binaryTail n = (2 : ℝ) ^ n *
      ∑' k : ℕ, (omegaCount (k + n) : ℝ) / 2 ^ (k + n) := by
  rw [binaryTail, ← tsum_mul_left]
  exact tsum_congr fun k ↦ (scaled_shift_term n k).symm

theorem binaryTail_add_prefix (n : ℕ) :
    (∑ i ∈ Finset.range n, (omegaCount i : ℝ) * 2 ^ (n - i)) + binaryTail n =
      (2 : ℝ) ^ n * binaryOmegaSum := by
  have hsplit := summable_omegaCount_div_two_pow.sum_add_tsum_nat_add n
  have hprefix : (2 : ℝ) ^ n *
      (∑ i ∈ Finset.range n, (omegaCount i : ℝ) / 2 ^ i) =
      ∑ i ∈ Finset.range n, (omegaCount i : ℝ) * 2 ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_sub₀ (2 : ℝ) (by norm_num) (Finset.mem_range.mp hi).le]
    ring
  rw [binaryTail_eq_scaled_shift, ← hprefix, ← mul_add, hsplit, binaryOmegaSum]

/-- The positive-index tail occurring in the irrationality argument. -/
def positiveBinaryTail (n : ℕ) : ℝ := binaryTail n - omegaCount n

theorem positiveBinaryTail_eq_tsum (n : ℕ) :
    positiveBinaryTail n =
      ∑' k : ℕ, (omegaCount (n + (k + 1)) : ℝ) / 2 ^ (k + 1) := by
  have h := (summable_binaryTail n).tsum_eq_zero_add
  simp only [Nat.add_zero, pow_zero, div_one] at h
  change binaryTail n = _ at h
  unfold positiveBinaryTail
  linarith

theorem integer_mul_binaryTail {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (n : ℕ) :
    ∃ t : ℤ, (q : ℝ) * binaryTail n = t := by
  let t : ℤ := (2 : ℤ) ^ n * z -
    (q : ℤ) * ∑ i ∈ Finset.range n, (omegaCount i : ℤ) * 2 ^ (n - i)
  refine ⟨t, ?_⟩
  have hp := congrArg (fun x : ℝ ↦ (q : ℝ) * x) (binaryTail_add_prefix n)
  have hr : (q : ℝ) * ((2 : ℝ) ^ n * binaryOmegaSum) = (2 : ℝ) ^ n * z := by
    rw [mul_left_comm, h]
  rw [hr] at hp
  dsimp [t]
  push_cast
  nlinarith only [hp]

theorem integer_mul_positiveBinaryTail {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (n : ℕ) :
    ∃ t : ℤ, (q : ℝ) * positiveBinaryTail n = t := by
  obtain ⟨t, ht⟩ := integer_mul_binaryTail h n
  refine ⟨t - (q : ℤ) * omegaCount n, ?_⟩
  simp only [positiveBinaryTail, mul_sub, ht, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]

theorem exists_integer_multiple_of_not_irrational
    (h : ¬ Irrational binaryOmegaSum) :
    ∃ q : ℕ, 0 < q ∧ ∃ z : ℤ, (q : ℝ) * binaryOmegaSum = z := by
  obtain ⟨r, hr⟩ := exists_rat_of_not_irrational h
  refine ⟨r.den, r.den_pos, r.num, ?_⟩
  rw [hr, Rat.cast_def]
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  field_simp

theorem binaryOmegaSum_eq_tsum_from_two :
    binaryOmegaSum =
      ∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2) := by
  have h := summable_omegaCount_div_two_pow.sum_add_tsum_nat_add 2
  simpa [binaryOmegaSum, Finset.sum_range_succ, omegaCount_eq_cardDistinctFactors] using
    h.symm

end

end Erdos69.Elementary

end SourceModule26

/- Source module 27: ErdosProblems.Erdos69.CompositeTails -/
section SourceModule27
open scoped BigOperators

namespace Erdos69.Elementary

noncomputable section

def divisibilityTail (p m : ℕ) : ℝ :=
  ∑' k : ℕ, (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)

def compositeCorrection (a m : ℕ) : ℝ := ∑ p ∈ a.primeFactors, divisibilityTail p m

def dilatedPositiveTail (a m : ℕ) : ℝ :=
  ∑' k : ℕ, (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1)

theorem summable_binary_weights : Summable (fun k : ℕ ↦ (1 : ℝ) / 2 ^ (k + 1)) := by
  simpa [pow_succ', div_mul_eq_div_div] using summable_geometric_two' (1 : ℝ)

theorem tsum_binary_weights : (∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1)) = 1 := by
  simpa [pow_succ', div_mul_eq_div_div] using tsum_geometric_two' (1 : ℝ)

theorem summable_divisibilityTail (p m : ℕ) :
    Summable (fun k : ℕ ↦
      (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)) := by
  apply Summable.of_nonneg_of_le (fun k ↦ by positivity) _ summable_binary_weights
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

theorem divisibilityTail_nonneg (p m : ℕ) : 0 ≤ divisibilityTail p m := by
  unfold divisibilityTail
  exact tsum_nonneg fun k ↦ by positivity

theorem divisibilityTail_le_one (p m : ℕ) : divisibilityTail p m ≤ 1 := by
  rw [← tsum_binary_weights]
  apply Summable.tsum_le_tsum _ (summable_divisibilityTail p m) summable_binary_weights
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

theorem compositeCorrection_nonneg (a m : ℕ) : 0 ≤ compositeCorrection a m := by
  exact Finset.sum_nonneg fun p _ ↦ divisibilityTail_nonneg p m

theorem summable_constant_binary_weights (a : ℝ) :
    Summable (fun k : ℕ ↦ a / 2 ^ (k + 1)) := by
  simpa [pow_succ', div_mul_eq_div_div] using summable_geometric_two' a

theorem tsum_constant_binary_weights (a : ℝ) :
    (∑' k : ℕ, a / 2 ^ (k + 1)) = a := by
  simpa [pow_succ', div_mul_eq_div_div] using tsum_geometric_two' a

theorem summable_positiveBinaryTail (m : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (m + (k + 1)) : ℝ) / 2 ^ (k + 1)) :=
  (summable_nat_add_iff 1).2 (summable_binaryTail m)

theorem compositeCorrection_eq_tsum (a m : ℕ) :
    compositeCorrection a m =
      ∑' k : ℕ, ∑ p ∈ a.primeFactors,
        (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
  exact (Summable.tsum_finsetSum fun p _ ↦ summable_divisibilityTail p m).symm

/-- Exact correction formula for an arbitrary positive composite dilation. -/
theorem dilatedPositiveTail_eq {a : ℕ} (ha : a ≠ 0) (m : ℕ) :
    dilatedPositiveTail a m =
      positiveBinaryTail m + omegaCount a - compositeCorrection a m := by
  have hconst := summable_constant_binary_weights (omegaCount a : ℝ)
  have htail := summable_positiveBinaryTail m
  have hcorr := summable_sum (s := a.primeFactors)
    (fun p _ ↦ summable_divisibilityTail p m)
  have hpoint (k : ℕ) :
      (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1) =
        (omegaCount a : ℝ) / 2 ^ (k + 1) +
          (omegaCount (m + (k + 1)) : ℝ) / 2 ^ (k + 1) -
            ∑ p ∈ a.primeFactors,
              (if p ∣ m + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1) := by
    rw [omegaCount_mul_indicator ha (by omega), sub_div, add_div, Finset.sum_div]
  unfold dilatedPositiveTail
  simp_rw [hpoint]
  rw [(hconst.add htail).tsum_sub hcorr, hconst.tsum_add htail,
    tsum_constant_binary_weights, ← positiveBinaryTail_eq_tsum,
    ← compositeCorrection_eq_tsum]
  ring

theorem summable_dilatedPositiveTail {a : ℕ} (ha : a ≠ 0) (m : ℕ) :
    Summable (fun k : ℕ ↦ (omegaCount (a * (m + (k + 1))) : ℝ) / 2 ^ (k + 1)) := by
  have hconst := summable_constant_binary_weights (omegaCount a : ℝ)
  have htail := summable_positiveBinaryTail m
  have hcorr := summable_sum (s := a.primeFactors)
    (fun p _ ↦ summable_divisibilityTail p m)
  apply ((hconst.add htail).sub hcorr).congr
  intro k
  rw [omegaCount_mul_indicator ha (by omega), sub_div, add_div, Finset.sum_div]

/-- Rationality of the original series gives an integer after adding the
explicit composite correction; primality of the dilation is unnecessary. -/
theorem integer_mul_corrected_dilatedTail {q a : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (ha : a ≠ 0) (m : ℕ) :
    ∃ t : ℤ, (q : ℝ) *
      (dilatedPositiveTail a m + compositeCorrection a m) = t := by
  obtain ⟨t, ht⟩ := integer_mul_positiveBinaryTail h m
  refine ⟨t + (q : ℤ) * omegaCount a, ?_⟩
  rw [dilatedPositiveTail_eq ha, sub_add_cancel, mul_add, ht]
  push_cast
  rfl

end

end Erdos69.Elementary

end SourceModule27

/- Source module 28: ErdosProblems.Erdos69.CorrectionAverages -/
section SourceModule28
/- # Mean correction for composite dilations -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem summable_mean (μ : FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ x, Summable (fun k ↦ f k x)) :
    Summable (fun k ↦ μ.mean (f k)) := by
  exact summable_sum (fun x _ ↦ (hf x).mul_left (μ.mass x))

theorem mean_tsum (μ : FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ x, Summable (fun k ↦ f k x)) :
    μ.mean (fun x ↦ ∑' k, f k x) = ∑' k, μ.mean (f k) := by
  unfold mean
  calc
    _ = ∑ x, ∑' k, μ.mass x * f k x :=
      Finset.sum_congr rfl (fun x _ ↦ ((hf x).tsum_mul_left (μ.mass x)).symm)
    _ = _ := (Summable.tsum_finsetSum (fun x _ ↦ (hf x).mul_left (μ.mass x))).symm

theorem mean_div_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun x ↦ f x / c) = μ.mean f / c := by
  simp only [div_eq_mul_inv, mean_mul_const]

theorem uniform_divisibility_mean_le (T p Q b : ℕ) (hT : 0 < T)
    (hp : 0 < p) (hQ : Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ if p ∣ b + Q * t.val then (1 : ℝ) else 0) ≤
      (1 : ℝ) / p + 1 / T := by
  rw [uniform_mean_indicator T hT (fun t ↦ p ∣ b + Q * t)]
  have h := affineResidueFrequency_error T p Q b hT hp hQ
  have hupper := (abs_le.mp h).2
  change (T.count (fun t ↦ p ∣ b + Q * t) : ℝ) / T ≤ _
  unfold affineResidueCount at hupper
  linarith

theorem uniform_divisibilityTail_le (T p Q b : ℕ) (hT : 0 < T)
    (hp : 0 < p) (hQ : Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ divisibilityTail p (b + Q * t.val)) ≤
      (1 : ℝ) / p + 1 / T := by
  let f : ℕ → Fin T → ℝ := fun k t ↦
    (if p ∣ b + Q * t.val + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)
  have hf (t : Fin T) : Summable (fun k ↦ f k t) := summable_divisibilityTail _ _
  have heq : (uniform T hT).mean (fun t ↦ divisibilityTail p (b + Q * t.val)) =
      ∑' k, (uniform T hT).mean (f k) := mean_tsum _ f hf
  rw [heq, ← tsum_constant_binary_weights ((1 : ℝ) / p + 1 / T)]
  apply Summable.tsum_le_tsum _ (summable_mean _ f hf) (summable_constant_binary_weights _)
  intro k
  dsimp [f]
  rw [mean_div_const]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := uniform_divisibility_mean_le T p Q (b + (k + 1)) hT hp hQ
  simpa only [Nat.add_right_comm] using h

theorem uniform_compositeCorrection_le (T a Q b : ℕ) (hT : 0 < T)
    (hQ : ∀ p ∈ a.primeFactors, Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ compositeCorrection a (b + Q * t.val)) ≤
      (∑ p ∈ a.primeFactors, (1 : ℝ) / p) + (omegaCount a : ℝ) / T := by
  simp only [compositeCorrection, mean_sum]
  calc
    _ ≤ ∑ p ∈ a.primeFactors, ((1 : ℝ) / p + 1 / T) := by
      apply Finset.sum_le_sum
      intro p hp
      exact uniform_divisibilityTail_le T p Q b hT
        (Nat.mem_primeFactors.mp hp).1.pos (hQ p hp)
    _ = _ := by simp [Finset.sum_add_distrib, omegaCount, div_eq_mul_inv]

end Erdos69.Elementary.FiniteLaw

end SourceModule28

/- Source module 29: ErdosProblems.Erdos69.LargePrimeAverages -/
section SourceModule29
/- # Finite averages of prime factors above a cutoff -/

open scoped BigOperators

namespace Erdos69.Elementary

def largePrimeCount (n y : ℕ) : ℕ := (n.primeFactors.filter (fun p ↦ y < p)).card

noncomputable def smallPrimeCount (n y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE y, if p ∣ n then (1 : ℝ) else 0

theorem primeFactors_filter_le (n y : ℕ) (hn : 0 < n) :
    n.primeFactors.filter (fun p ↦ p ≤ y) = (Nat.primesLE y).filter (fun p ↦ p ∣ n) := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE]
  have hn0 := hn.ne'
  tauto

theorem omegaCount_eq_small_add_large (n y : ℕ) (hn : 0 < n) :
    (omegaCount n : ℝ) = smallPrimeCount n y + largePrimeCount n y := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := n.primeFactors) (p := fun p ↦ p ≤ y)
  rw [primeFactors_filter_le n y hn] at hcard
  have heq : n.primeFactors.filter (fun p ↦ ¬p ≤ y) =
      n.primeFactors.filter (fun p ↦ y < p) := by ext p; simp
  rw [heq] at hcard
  unfold omegaCount smallPrimeCount largePrimeCount
  rw [Finset.sum_boole]
  exact_mod_cast hcard.symm

theorem largePrimeCount_le_log (n R : ℕ) (hn : 0 < n) (hR : 1 < R) :
    (largePrimeCount n R : ℝ) ≤ Real.log n / Real.log R := by
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  apply (le_div_iff₀ (Real.log_pos hRR)).mpr
  apply card_primeFactors_subset_mul_log_le hn _ (Finset.filter_subset _ _)
    (by exact_mod_cast (lt_trans zero_lt_one hR))
  intro p hp
  exact_mod_cast (Finset.mem_filter.mp hp).2.le

def primeWindow (y R : ℕ) : Finset ℕ := (Nat.primesLE R).filter (fun p ↦ y < p)

theorem smallPrimeCount_difference (n y R : ℕ) (hyR : y ≤ R) :
    smallPrimeCount n R - smallPrimeCount n y =
      ∑ p ∈ primeWindow y R, if p ∣ n then (1 : ℝ) else 0 := by
  classical
  have hs : Nat.primesLE R = Nat.primesLE y ∪ primeWindow y R := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, primeWindow, Finset.mem_filter]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hd : Disjoint (Nat.primesLE y) (primeWindow y R) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpy := (Nat.mem_primesLE.mp hp).1
    have hyp := (Finset.mem_filter.mp hq).2
    omega
  unfold smallPrimeCount
  rw [hs, Finset.sum_union hd]
  ring

theorem largePrimeCount_split_bound (n y R : ℕ) (hn : 0 < n) (hR : 1 < R)
    (hyR : y ≤ R) :
    (largePrimeCount n y : ℝ) ≤
      (∑ p ∈ primeWindow y R, if p ∣ n then (1 : ℝ) else 0) + Real.log n / Real.log R := by
  have hy := omegaCount_eq_small_add_large n y hn
  have hR' := omegaCount_eq_small_add_large n R hn
  have hs := smallPrimeCount_difference n y R hyR
  have ht := largePrimeCount_le_log n R hn hR
  linarith

theorem primeWindow_reciprocal_eq (y R : ℕ) (hyR : y ≤ R) :
    (∑ p ∈ primeWindow y R, (1 : ℝ) / p) = primeReciprocalSum R - primeReciprocalSum y := by
  classical
  have hfilter : (Nat.primesLE R).filter (fun p ↦ ¬y < p) = Nat.primesLE y := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE R)
    (fun p ↦ y < p) (fun p : ℕ ↦ (1 : ℝ) / p)
  rw [hfilter] at hsum
  unfold primeWindow primeReciprocalSum
  linarith

namespace FiniteLaw

theorem uniform_largePrimeCount_le (T Q b y R X : ℕ) (hT : 0 < T)
    (hQ : 0 < Q) (hQy : Q ≤ y) (hyR : y ≤ R) (hR : 1 < R)
    (hpos : ∀ t : Fin T, 0 < b + Q * t.val)
    (hupper : ∀ t : Fin T, b + Q * t.val ≤ X) :
    (uniform T hT).mean (fun t ↦ (largePrimeCount (b + Q * t.val) y : ℝ)) ≤
      primeReciprocalSum R - primeReciprocalSum y +
        ((primeWindow y R).card : ℝ) / T + Real.log X / Real.log R := by
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hpoint (t : Fin T) : (largePrimeCount (b + Q * t.val) y : ℝ) ≤
      (∑ p ∈ primeWindow y R, if p ∣ b + Q * t.val then (1 : ℝ) else 0) +
        Real.log X / Real.log R := by
    apply (largePrimeCount_split_bound _ y R (hpos t) hR hyR).trans
    gcongr
    · exact_mod_cast hpos t
    · exact_mod_cast hupper t
  have hmean := (uniform T hT).mean_mono hpoint
  rw [mean_add, mean_const, mean_sum] at hmean
  have hpmean : (∑ p ∈ primeWindow y R,
      (uniform T hT).mean (fun t ↦ if p ∣ b + Q * t.val then (1 : ℝ) else 0)) ≤
        ∑ p ∈ primeWindow y R, ((1 : ℝ) / p + 1 / T) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpR, hyp⟩ := Finset.mem_filter.mp hp
    have hprime := (Nat.mem_primesLE.mp hpR).2
    have hcop : Q.Coprime p := by
      apply Nat.Coprime.symm
      apply (hprime.coprime_iff_not_dvd).mpr
      intro hd
      have hpQ := Nat.le_of_dvd hQ hd
      omega
    exact uniform_divisibility_mean_le T p Q b hT hprime.pos hcop
  rw [Finset.sum_add_distrib, primeWindow_reciprocal_eq y R hyR] at hpmean
  simp only [Finset.sum_const, nsmul_eq_mul] at hpmean
  have hcard : ((primeWindow y R).card : ℝ) * ((1 : ℝ) / T) =
      ((primeWindow y R).card : ℝ) / T := by ring
  rw [hcard] at hpmean
  linarith

end FiniteLaw

end Erdos69.Elementary

end SourceModule29

/- Source module 30: ErdosProblems.Erdos69.PatternShifts -/
section SourceModule30
/- # The retained shifts and their unique smallest element -/

open scoped BigOperators

namespace Erdos69.Elementary

def patternShift (m P : ℕ) (i : PatternLabel m) (h : ℕ) : ℕ :=
  patternDilation m P i * h - patternOffset m P i

theorem patternIntercept_le_digit_mul {m h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    patternIntercept m i ≤ patternDigit m i * h := by
  calc
    patternIntercept m i ≤ 6 * m * patternDigit m i := patternIntercept_le m i
    _ ≤ h * patternDigit m i := Nat.mul_le_mul_right _ hh
    _ = _ := Nat.mul_comm _ _

theorem patternShift_eq {m P h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    patternShift m P i h = (primorial P + 1) * h +
      primorial P * (patternDigit m i * h - patternIntercept m i) := by
  unfold patternShift patternDilation roughDilation patternOffset
  have hle := patternIntercept_le_digit_mul hh i
  have heq : (1 + primorial P * (1 + patternDigit m i)) * h =
      (primorial P + 1) * h + primorial P * (patternDigit m i * h) := by ring
  rw [heq, Nat.add_sub_assoc (Nat.mul_le_mul_left _ hle), Nat.mul_sub_left_distrib]

theorem patternShift_zero (m P h : ℕ) :
    patternShift m P (patternZero m) h = (primorial P + 1) * h := by
  simp [patternShift, patternDilation, roughDilation, patternOffset,
    patternDigit_zero, patternIntercept_zero, add_comm]

theorem patternShift_lower {m P h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    (primorial P + 1) * h ≤ patternShift m P i h := by
  rw [patternShift_eq hh]
  omega

theorem patternShift_strict_of_ne_zero {m P h : ℕ} (hh : 6 * m < h)
    (i : PatternLabel m) (hi : i ≠ patternZero m) :
    (primorial P + 1) * h < patternShift m P i h := by
  have hd : 0 < patternDigit m i := by
    have hne : patternDigit m i ≠ 0 := by
      intro hz
      exact hi ((patternDigit_eq_zero_iff m i).mp hz)
    omega
  have hmul : 6 * m * patternDigit m i < patternDigit m i * h := by
    simpa only [Nat.mul_comm (6 * m)] using Nat.mul_lt_mul_of_pos_left hh hd
  have hsub : 0 < patternDigit m i * h - patternIntercept m i :=
    Nat.sub_pos_of_lt ((patternIntercept_le m i).trans_lt hmul)
  rw [patternShift_eq hh.le]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (primorial_pos P) hsub)

theorem patternShift_pos {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    0 < patternShift m P i h := by
  have hbase : 0 < (primorial P + 1) * h := Nat.mul_pos (by omega) (by omega)
  exact hbase.trans_le (patternShift_lower hh.le i)

theorem patternShift_minimal {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    (primorial P + 1) * (6 * m + 1) ≤ patternShift m P i h := by
  exact (Nat.mul_le_mul_left _ (by omega : 6 * m + 1 ≤ h)).trans
    (patternShift_lower hh.le i)

theorem patternShift_eq_minimal_iff {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    patternShift m P i h = (primorial P + 1) * (6 * m + 1) ↔
      i = patternZero m ∧ h = 6 * m + 1 := by
  constructor
  · intro heq
    have hbase := patternShift_lower (P := P) hh.le i
    have hh' : h = 6 * m + 1 := by
      rw [heq] at hbase
      have hle : h ≤ 6 * m + 1 := by nlinarith
      omega
    refine ⟨?_, hh'⟩
    by_contra hi
    have hs := patternShift_strict_of_ne_zero hh i hi (P := P)
    rw [heq, hh'] at hs
    exact (lt_irrefl _ hs)
  · rintro ⟨rfl, rfl⟩
    exact patternShift_zero m P _

theorem patternShift_le_dilation_mul (m P h : ℕ) (i : PatternLabel m) :
    patternShift m P i h ≤ patternDilation m P i * h := Nat.sub_le _ _

end Erdos69.Elementary

end SourceModule30

/- Source module 31: ErdosProblems.Erdos69.PatternCoefficients -/
section SourceModule31
/- # Grouping the retained terms by their actual shift -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev PatternTerm (m H : ℕ) := PatternLabel m × Fin H

def termShift (m P H : ℕ) (t : PatternTerm m H) : ℕ :=
  patternShift m P t.1 (6 * m + 1 + t.2.val)

noncomputable def termCoefficient (m H : ℕ) (q : ℝ) (t : PatternTerm m H) : ℝ :=
  q * (patternSign m t.1 : ℝ) / 2 ^ (6 * m + 1 + t.2.val)

def retainedShifts (m P H : ℕ) : Finset ℕ := Finset.univ.image (termShift m P H)

noncomputable def shiftCoefficient (m P H : ℕ) (q : ℝ) (r : ℕ) : ℝ :=
  ∑ t : PatternTerm m H, if termShift m P H t = r then termCoefficient m H q t else 0

theorem termShift_mem (m P H : ℕ) (t : PatternTerm m H) :
    termShift m P H t ∈ retainedShifts m P H :=
  Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

theorem sum_shiftCoefficient (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r) =
      ∑ t : PatternTerm m H, termCoefficient m H q t := by
  unfold shiftCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [termShift_mem]

theorem sum_termCoefficient {m : ℕ} (hm : 0 < m) (H : ℕ) (q : ℝ) :
    (∑ t : PatternTerm m H, termCoefficient m H q t) = 0 := by
  unfold termCoefficient
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  dsimp only
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hs : (∑ i : PatternLabel m, (patternSign m i : ℝ)) = 0 := by
    exact_mod_cast sum_patternSign hm
  rw [hs, mul_zero, zero_div]

theorem sum_shiftCoefficient_zero {m : ℕ} (hm : 0 < m) (P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r) = 0 := by
  rw [sum_shiftCoefficient, sum_termCoefficient hm]

theorem abs_shiftCoefficient_mass_le (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, |shiftCoefficient m P H q r|) ≤
      ∑ t : PatternTerm m H, |termCoefficient m H q t| := by
  calc
    _ ≤ ∑ r ∈ retainedShifts m P H,
        ∑ t : PatternTerm m H, |if termShift m P H t = r then termCoefficient m H q t else 0| :=
      Finset.sum_le_sum (fun r _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp [apply_ite abs, termShift_mem]

theorem finite_binary_tail_le (K H : ℕ) :
    (∑ k : Fin H, (1 : ℝ) / 2 ^ (K + 1 + k.val)) ≤ (1 : ℝ) / 2 ^ K := by
  have heq (k : ℕ) : (1 : ℝ) / 2 ^ (K + 1 + k) =
      (1 / 2 ^ K) * (1 / 2 ^ (k + 1)) := by
    rw [show K + 1 + k = K + (k + 1) by omega, pow_add]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (1 : ℝ) / 2 ^ (K + 1 + k)) H]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have hb : (∑ k ∈ Finset.range H, (1 : ℝ) / 2 ^ (k + 1)) ≤ 1 := by
    calc
      _ ≤ ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1) :=
        summable_binary_weights.sum_le_tsum (Finset.range H) (fun _ _ ↦ by positivity)
      _ = 1 := tsum_binary_weights
  simpa using mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 / 2 ^ K)

theorem termCoefficient_mass_le (m H : ℕ) (q : ℝ) :
    (∑ t : PatternTerm m H, |termCoefficient m H q t|) ≤
      |q| * (36 : ℝ) ^ m / 2 ^ (6 * m) := by
  have heq : (∑ t : PatternTerm m H, |termCoefficient m H q t|) =
      |q| * (36 : ℝ) ^ m * ∑ k : Fin H, (1 : ℝ) / 2 ^ (6 * m + 1 + k.val) := by
    simp [termCoefficient, Fintype.sum_prod_type, abs_mul,
      patternSign_abs_real, ← Finset.mul_sum, card_patternLabel, div_eq_mul_inv,
      mul_assoc]
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (finite_binary_tail_le (6 * m) H)
    (by positivity : 0 ≤ |q| * (36 : ℝ) ^ m)
  simpa only [mul_one_div] using h

theorem shiftCoefficient_mass_le (m P H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, |shiftCoefficient m P H q r|) ≤
      |q| * (9 / 16 : ℝ) ^ m := by
  have h := (abs_shiftCoefficient_mass_le m P H q).trans (termCoefficient_mass_le m H q)
  rwa [mul_div_assoc, pattern_mass_ratio] at h

theorem retainedShifts_card_le (m P H : ℕ) :
    (retainedShifts m P H).card ≤ 36 ^ m * H := by
  have h := Finset.card_image_le (f := termShift m P H) (s := Finset.univ)
  simpa only [retainedShifts, Finset.card_univ, Fintype.card_prod, card_patternLabel,
    Fintype.card_fin] using h

theorem termShift_eq_minimal_iff (m P H : ℕ) (t : PatternTerm m H) :
    termShift m P H t = (primorial P + 1) * (6 * m + 1) ↔
      t.1 = patternZero m ∧ t.2.val = 0 := by
  rw [termShift, patternShift_eq_minimal_iff (by omega)]
  simp

theorem minimal_mem_retainedShifts (m P H : ℕ) (hH : 0 < H) :
    (primorial P + 1) * (6 * m + 1) ∈ retainedShifts m P H := by
  apply Finset.mem_image.mpr
  refine ⟨(patternZero m, ⟨0, hH⟩), Finset.mem_univ _, ?_⟩
  exact (termShift_eq_minimal_iff m P H _).mpr ⟨rfl, rfl⟩

theorem shiftCoefficient_minimal (m P H : ℕ) (hH : 0 < H) (q : ℝ) :
    shiftCoefficient m P H q ((primorial P + 1) * (6 * m + 1)) =
      q / 2 ^ (6 * m + 1) := by
  classical
  unfold shiftCoefficient
  simp_rw [termShift_eq_minimal_iff]
  rw [Fintype.sum_prod_type]
  let z : Fin H := ⟨0, hH⟩
  have hz (k : Fin H) : k.val = 0 ↔ k = z := by
    exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
  simp only [hz]
  simp [termCoefficient, z, ite_and]

theorem sum_grouped_shift_test (m P H : ℕ) (q : ℝ) (f : ℕ → ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * f r) =
      ∑ t : PatternTerm m H, termCoefficient m H q t * f (termShift m P H t) := by
  unfold shiftCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [ite_mul, zero_mul]
  simp [termShift_mem]

end Erdos69.Elementary

end SourceModule31

/- Source module 32: ErdosProblems.Erdos69.TailCancellation -/
section SourceModule32
/- # Applying the cancellation pattern to arithmetic tails -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem pattern_shift_int_identity (m P n h : ℕ) (i : PatternLabel m) :
    (n : ℤ) + (patternDilation m P i : ℤ) * h - patternOffset m P i =
      n + ((primorial P : ℤ) + 1) * h + (primorial P : ℤ) * patternPhase m i h := by
  simp only [patternDilation, roughDilation, patternOffset, patternPhase,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem pattern_shift_toNat (m P n h : ℕ) (i : PatternLabel m) :
    ((n : ℤ) + ((primorial P : ℤ) + 1) * h +
      (primorial P : ℤ) * patternPhase m i h).toNat =
        n + patternDilation m P i * h - patternOffset m P i := by
  rw [← pattern_shift_int_identity]
  rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_sub]

theorem initial_arithmetic_cancellation (m P n h : ℕ) (hpos : 1 ≤ h) (hle : h ≤ 6 * m)
    (f : ℕ → ℝ) :
    (∑ i : PatternLabel m, (patternSign m i : ℝ) *
      f (n + patternDilation m P i * h - patternOffset m P i)) = 0 := by
  have hs := patternSignedSum_vanish m hpos hle
    (fun t ↦ f (((n : ℤ) + ((primorial P : ℤ) + 1) * h + (primorial P : ℤ) * t).toNat))
  simpa only [patternSignedSum, pattern_shift_toNat] using hs

theorem dilation_quotient_shift {a b n : ℕ} (ha : 0 < a) (hb : b ≤ n)
    (hn : n ≡ b [MOD a]) (h : ℕ) :
    a * ((n - b) / a + h) = n + a * h - b := by
  have hd : a ∣ n - b := (Nat.modEq_iff_dvd' hb).mp hn.symm
  obtain ⟨k, hk⟩ := hd
  rw [Nat.mul_add, hk, Nat.mul_div_cancel_left _ ha]
  omega

theorem corrected_signed_tail_integer {ι : Type*} [Fintype ι]
    {q : ℕ} {z : ℤ} (h : (q : ℝ) * binaryOmegaSum = z)
    (a m : ι → ℕ) (ha : ∀ i, a i ≠ 0) (s : ι → ℤ) :
    ∃ t : ℤ, (q : ℝ) * (∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (m i)) +
      (q : ℝ) * (∑ i, (s i : ℝ) * compositeCorrection (a i) (m i)) = t := by
  classical
  choose t ht using fun i ↦ integer_mul_corrected_dilatedTail h (ha i) (m i)
  refine ⟨∑ i, s i * t i, ?_⟩
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (s i : ℝ) * ((q : ℝ) * (dilatedPositiveTail (a i) (m i) +
        compositeCorrection (a i) (m i))) := by ring
    _ = _ := by rw [ht i]

end Erdos69.Elementary

end SourceModule32

/- Source module 33: ErdosProblems.Erdos69.RationalPhase -/
section SourceModule33
/- # The Fourier consequence of rationality of the original series -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

@[simp] theorem complexMean_const (μ : FiniteLaw Ω) (c : ℂ) :
    μ.complexMean (fun _ ↦ c) = c := by
  rw [complexMean, ← Finset.sum_mul, ← Complex.ofReal_sum, μ.total]
  simp

theorem norm_phase_mean_sub_one_le (μ : FiniteLaw Ω) (U C : Ω → ℝ)
    (h : ∀ x, ∃ z : ℤ, U x + C x = z) :
    ‖μ.complexMean (fun x ↦ fourierPhase (U x)) - 1‖ ≤
      2 * Real.pi * μ.mean (fun x ↦ |C x|) := by
  have hid (x : Ω) : fourierPhase (U x + C x) = 1 := by
    obtain ⟨z, hz⟩ := h x
    rw [hz, fourierPhase_intCast]
  have hbound := norm_mean_fourierPhase_sub_le μ U (fun x ↦ U x + C x)
  simpa only [hid, complexMean_const, sub_add_cancel_left, abs_neg] using hbound

theorem abs_signed_correction_le {ι : Type*} [Fintype ι] (q : ℝ) (s : ι → ℤ)
    (hs : ∀ i, |(s i : ℝ)| = 1) (a b : ι → ℕ) :
    |q * ∑ i, (s i : ℝ) * compositeCorrection (a i) (b i)| ≤
      |q| * ∑ i, compositeCorrection (a i) (b i) := by
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
  calc
    _ ≤ ∑ i, |(s i : ℝ) * compositeCorrection (a i) (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_mul, hs, abs_of_nonneg (compositeCorrection_nonneg _ _)]

theorem rational_signed_tail_phase_le {ι : Type*} [Fintype ι]
    {q : ℕ} {z : ℤ} (h : (q : ℝ) * binaryOmegaSum = z)
    (μ : FiniteLaw Ω) (a : ι → ℕ) (ha : ∀ i, a i ≠ 0)
    (s : ι → ℤ) (hs : ∀ i, |(s i : ℝ)| = 1) (b : Ω → ι → ℕ) :
    ‖μ.complexMean (fun x ↦ fourierPhase
      ((q : ℝ) * ∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (b x i))) - 1‖ ≤
        2 * Real.pi * q * ∑ i, μ.mean (fun x ↦ compositeCorrection (a i) (b x i)) := by
  have hphase := norm_phase_mean_sub_one_le μ
    (fun x ↦ (q : ℝ) * ∑ i, (s i : ℝ) * dilatedPositiveTail (a i) (b x i))
    (fun x ↦ (q : ℝ) * ∑ i, (s i : ℝ) * compositeCorrection (a i) (b x i))
    (fun x ↦ corrected_signed_tail_integer h a (b x) ha s)
  have habs := μ.mean_mono (fun x ↦ abs_signed_correction_le (q : ℝ) s hs a (b x))
  simp only [Nat.abs_cast, mean_const_mul, mean_sum] at habs
  exact hphase.trans (by
    have hmul := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 2 * Real.pi)
    simpa only [mul_assoc] using hmul)

end Erdos69.Elementary.FiniteLaw

end SourceModule33

/- Source module 34: ErdosProblems.Erdos69.PrimeDecomposition -/
section SourceModule34
/- # Separating fixed, small free, and large prime contributions -/

open scoped BigOperators

namespace Erdos69.Elementary

def freePrimes (Q y : ℕ) : Finset ℕ := (Nat.primesLE y).filter (fun p ↦ ¬p ∣ Q)

noncomputable def fixedPrimeCount (Q y b : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE y).filter (fun p ↦ p ∣ Q), if p ∣ b then (1 : ℝ) else 0

theorem smallPrimeCount_affine_split (Q y b t : ℕ) :
    smallPrimeCount (b + Q * t) y = fixedPrimeCount Q y b +
      ∑ p ∈ freePrimes Q y, if p ∣ b + Q * t then (1 : ℝ) else 0 := by
  classical
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE y) (fun p ↦ p ∣ Q)
    (fun p ↦ if p ∣ b + Q * t then (1 : ℝ) else 0)
  have hfixed : (∑ p ∈ (Nat.primesLE y).filter (fun p ↦ p ∣ Q),
      if p ∣ b + Q * t then (1 : ℝ) else 0) = fixedPrimeCount Q y b := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpQ := (Finset.mem_filter.mp hp).2
    simp only [← Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpQ t)]
  rw [hfixed] at hsum
  exact hsum.symm

theorem weighted_omega_affine_decomposition {ι : Type*} [Fintype ι]
    (Q y b t : ℕ) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ i, 0 < b + Q * t + s i) :
    (∑ i, c i * (omegaCount (b + Q * t + s i) : ℝ)) =
      (∑ i, c i * fixedPrimeCount Q y (b + s i)) +
      (∑ p ∈ freePrimes Q y, ∑ i, c i *
        (if p ∣ b + Q * t + s i then (1 : ℝ) else 0)) +
      ∑ i, c i * (largePrimeCount (b + Q * t + s i) y : ℝ) := by
  have hsmall (i : ι) : smallPrimeCount (b + Q * t + s i) y =
      fixedPrimeCount Q y (b + s i) +
        ∑ p ∈ freePrimes Q y, if p ∣ b + Q * t + s i then (1 : ℝ) else 0 := by
    simpa only [Nat.add_right_comm] using smallPrimeCount_affine_split Q y (b + s i) t
  simp_rw [omegaCount_eq_small_add_large _ y (hpos _), hsmall, mul_add]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := freePrimes Q y)]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem norm_mean_fourierPhase_add_const (μ : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (c + X x))‖ =
      ‖μ.complexMean (fun x ↦ fourierPhase (X x))‖ := by
  simp only [fourierPhase_add, complexMean_const_mul, norm_mul, norm_fourierPhase, one_mul]

theorem norm_mean_fourierPhase_compare_shift (μ : FiniteLaw Ω) (W Z : Ω → ℝ) (c : ℝ) :
    ‖μ.complexMean (fun x ↦ fourierPhase (W x))‖ ≤
      ‖μ.complexMean (fun x ↦ fourierPhase (Z x))‖ +
        2 * Real.pi * μ.mean (fun x ↦ |W x - (c + Z x)|) := by
  have h := norm_mean_fourierPhase_sub_le μ W (fun x ↦ c + Z x)
  have ht := norm_le_norm_add_norm_sub
    (μ.complexMean (fun x ↦ fourierPhase (c + Z x)))
    (μ.complexMean (fun x ↦ fourierPhase (W x)))
  rw [norm_sub_rev] at ht
  rw [norm_mean_fourierPhase_add_const] at ht
  linarith

theorem weighted_largePrime_mean_le {ι : Type*} [Fintype ι]
    (T Q b y R X : ℕ) (hT : 0 < T) (hQ : 0 < Q) (hQy : Q ≤ y)
    (hyR : y ≤ R) (hR : 1 < R) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ (t : Fin T) i, 0 < b + Q * t.val + s i)
    (hupper : ∀ (t : Fin T) i, b + Q * t.val + s i ≤ X) :
    (uniform T hT).mean (fun t ↦
      |∑ i, c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)|) ≤
        (∑ i, |c i|) * (primeReciprocalSum R - primeReciprocalSum y +
          ((primeWindow y R).card : ℝ) / T + Real.log X / Real.log R) := by
  have habs (t : Fin T) : |∑ i, c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)| ≤
      ∑ i, |c i| * (largePrimeCount (b + Q * t.val + s i) y : ℝ) := by
    calc
      _ ≤ ∑ i, |c i * (largePrimeCount (b + Q * t.val + s i) y : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, Nat.abs_cast]
  apply ((uniform T hT).mean_mono habs).trans
  rw [mean_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [mean_const_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (c i))
  have h := uniform_largePrimeCount_le T Q (b + s i) y R X hT hQ hQy hyR hR
    (fun t ↦ by simpa only [Nat.add_right_comm] using hpos t i)
    (fun t ↦ by simpa only [Nat.add_right_comm] using hupper t i)
  simpa only [Nat.add_right_comm] using h

theorem affine_omega_fourier_compare_small {ι : Type*} [Fintype ι]
    (T Q b y R X : ℕ) (hT : 0 < T) (hQ : 0 < Q) (hQy : Q ≤ y)
    (hyR : y ≤ R) (hR : 1 < R) (s : ι → ℕ) (c : ι → ℝ)
    (hpos : ∀ (t : Fin T) i, 0 < b + Q * t.val + s i)
    (hupper : ∀ (t : Fin T) i, b + Q * t.val + s i ≤ X) :
    ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
      (∑ i, c i * (omegaCount (b + Q * t.val + s i) : ℝ)))‖ ≤
        ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
          (∑ p ∈ freePrimes Q y, ∑ i, c i *
            (if p ∣ b + Q * t.val + s i then (1 : ℝ) else 0)))‖ +
        2 * Real.pi * (∑ i, |c i|) *
          (primeReciprocalSum R - primeReciprocalSum y + ((primeWindow y R).card : ℝ) / T +
            Real.log X / Real.log R) := by
  have hcompare := norm_mean_fourierPhase_compare_shift (uniform T hT)
    (fun t ↦ ∑ i, c i * (omegaCount (b + Q * t.val + s i) : ℝ))
    (fun t ↦ ∑ p ∈ freePrimes Q y, ∑ i, c i *
      (if p ∣ b + Q * t.val + s i then (1 : ℝ) else 0))
    (∑ i, c i * fixedPrimeCount Q y (b + s i))
  simp_rw [weighted_omega_affine_decomposition Q y b _ s c (hpos _),
    add_sub_cancel_left] at hcompare ⊢
  have hlarge := weighted_largePrime_mean_le T Q b y R X hT hQ hQy hyR hR s c hpos hupper
  have hmul := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ 2 * Real.pi)
  calc
    _ ≤ _ := hcompare
    _ ≤ _ := by linarith

end FiniteLaw

end Erdos69.Elementary

end SourceModule34

/- Source module 35: ErdosProblems.Erdos69.Parameters -/
section SourceModule35
/-
# Integer parameter hierarchy

All cutoffs are integer powers, so no floor or ceiling approximation enters
the moment comparison. Write `N = 36^m`, `B = N^4`. We retain `2*B` terms
after the initial `6*m` cancellations, use `y = 2^(2^B)` as the small-prime
cutoff, and average over `T = y^(40*B)` progression indices. The intermediate
cutoff is exactly the square root `R = y^(20*B)`.

This choice makes the pointwise omitted tail small: its logarithmic size is
of order `B*2^B`, whereas its binary denominator contains `2^(2*B)`.
-/

namespace Erdos69.Elementary

def patternSize (m : ℕ) : ℕ := 36 ^ m
def fluctuationScale (m : ℕ) : ℕ := patternSize m ^ 4
def dilationPrimeCutoff (m : ℕ) : ℕ := 2 ^ (patternSize m ^ 2)
def excludedPrimeCutoff (m : ℕ) : ℕ := 2 ^ (patternSize m ^ 3)
def retainedLength (m : ℕ) : ℕ := 2 * fluctuationScale m
def smallPrimeCutoff (m : ℕ) : ℕ := 2 ^ (2 ^ fluctuationScale m)
def progressionLength (m : ℕ) : ℕ := smallPrimeCutoff m ^ (40 * fluctuationScale m)
def intermediatePrimeCutoff (m : ℕ) : ℕ := smallPrimeCutoff m ^ (20 * fluctuationScale m)
def momentOrder (m : ℕ) : ℕ := 2 * fluctuationScale m

theorem patternSize_pos (m : ℕ) : 0 < patternSize m := by unfold patternSize; positivity
theorem fluctuationScale_pos (m : ℕ) : 0 < fluctuationScale m :=
  Nat.pow_pos (patternSize_pos m)
theorem dilationPrimeCutoff_pos (m : ℕ) : 0 < dilationPrimeCutoff m := by
  unfold dilationPrimeCutoff; positivity
theorem smallPrimeCutoff_pos (m : ℕ) : 0 < smallPrimeCutoff m := by
  unfold smallPrimeCutoff; positivity
theorem progressionLength_pos (m : ℕ) : 0 < progressionLength m :=
  Nat.pow_pos (smallPrimeCutoff_pos m)
theorem retainedLength_pos (m : ℕ) : 0 < retainedLength m :=
  Nat.mul_pos (by norm_num) (fluctuationScale_pos m)
theorem momentOrder_pos (m : ℕ) : 0 < momentOrder m := retainedLength_pos m
theorem momentOrder_even (m : ℕ) : Even (momentOrder m) := even_two_mul _

theorem initialLength_le_patternSize (m : ℕ) : 6 * m ≤ patternSize m := by
  induction m with
  | zero => simp [patternSize]
  | succ m ih =>
    have hp := patternSize_pos m
    have heq : patternSize (m + 1) = patternSize m * 36 := by simp [patternSize, pow_succ]
    rw [heq]
    omega

theorem digitRange_le_patternSize_square (m : ℕ) : 49 ^ m ≤ patternSize m ^ 2 := by
  have h : (49 : ℕ) ≤ 36 ^ 2 := by norm_num
  calc
    49 ^ m ≤ (36 ^ 2) ^ m := Nat.pow_le_pow_left h m
    _ = patternSize m ^ 2 := by
      simp only [patternSize, ← pow_mul]
      rw [Nat.mul_comm 2 m]

theorem digitRange_le_dilationPrimeCutoff (m : ℕ) : 49 ^ m ≤ dilationPrimeCutoff m := by
  exact (digitRange_le_patternSize_square m).trans Nat.lt_two_pow_self.le

theorem intermediatePrimeCutoff_square (m : ℕ) :
    intermediatePrimeCutoff m ^ 2 = progressionLength m := by
  unfold intermediatePrimeCutoff progressionLength
  rw [← pow_mul]
  congr 1
  omega

theorem smallPrimeCutoff_moment_ratio (m : ℕ) :
    progressionLength m = smallPrimeCutoff m ^ momentOrder m *
      smallPrimeCutoff m ^ (38 * fluctuationScale m) := by
  unfold progressionLength momentOrder
  rw [← pow_add]
  congr 1
  omega

end Erdos69.Elementary

end SourceModule35

/- Source module 36: ErdosProblems.Erdos69.Construction -/
section SourceModule36
/- # The explicit CRT progression associated with a cancellation pattern -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev ConstructionShift (m : ℕ) :=
  ↥(retainedShifts m (dilationPrimeCutoff m) (retainedLength m))

def constructionDilation (m : ℕ) : PatternLabel m → ℕ :=
  patternDilation m (dilationPrimeCutoff m)

def constructionOffset (m : ℕ) : PatternLabel m → ℕ :=
  patternOffset m (dilationPrimeCutoff m)

def constructionProduct (m : ℕ) : ℕ := ∏ i, constructionDilation m i

def constructionCollisionProduct (m : ℕ) : ℕ :=
  collisionProduct (fun r : ConstructionShift m ↦ r.val)

def constructionModulus (m : ℕ) : ℕ :=
  augmentedModulus (constructionProduct m) (constructionCollisionProduct m)

def constructionMaxDilation (m : ℕ) : ℕ :=
  roughDilation (dilationPrimeCutoff m) (dilationPrimeCutoff m)

theorem constructionDilation_pos (m : ℕ) (i : PatternLabel m) :
    0 < constructionDilation m i := patternDilation_pos _ _ _

theorem constructionDilation_pairwise (m : ℕ) :
    Pairwise (fun i j : PatternLabel m ↦
      (constructionDilation m i).Coprime (constructionDilation m j)) :=
  patternDilation_pairwise m _ (digitRange_le_dilationPrimeCutoff m)

theorem constructionProduct_pos (m : ℕ) : 0 < constructionProduct m :=
  Finset.prod_pos (fun i _ ↦ constructionDilation_pos m i)

theorem constructionCollisionProduct_pos (m : ℕ) : 0 < constructionCollisionProduct m :=
  collisionProduct_pos _ Subtype.val_injective

theorem constructionModulus_pos (m : ℕ) : 0 < constructionModulus m :=
  augmentedModulus_pos (constructionProduct_pos m)

theorem constructionDilation_dvd_modulus (m : ℕ) (i : PatternLabel m) :
    constructionDilation m i ∣ constructionModulus m :=
  (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans
    (dvd_augmentedModulus (constructionProduct m) (constructionCollisionProduct m))

theorem construction_quotient_coprime (m : ℕ) (i : PatternLabel m) :
    (constructionModulus m / constructionDilation m i).Coprime (constructionDilation m i) := by
  classical
  exact coprime_augmentedModulus_quotient (constructionDilation m)
    (constructionDilation_pos m) (constructionDilation_pairwise m) _ i

theorem constructionDilation_le_max (m : ℕ) (i : PatternLabel m) :
    constructionDilation m i ≤ constructionMaxDilation m := by
  have hd := (patternDigit_lt m i).le.trans (digitRange_le_dilationPrimeCutoff m)
  unfold constructionDilation patternDilation constructionMaxDilation roughDilation
  gcongr

theorem constructionOffset_le (m : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ 6 * m * constructionMaxDilation m := by
  have hm := patternIntercept_le m i
  have hD := constructionDilation_le_max m i
  have hbase : constructionOffset m i ≤ 6 * m * constructionDilation m i := by
    unfold constructionOffset patternOffset constructionDilation patternDilation roughDilation
    nlinarith
  exact hbase.trans (Nat.mul_le_mul_left _ hD)

noncomputable def constructionResidue (m : ℕ) : ℕ :=
  (Nat.chineseRemainderOfFinset (constructionOffset m) (constructionDilation m) Finset.univ
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun _ _ _ _ hij ↦ constructionDilation_pairwise m hij)).val

theorem constructionResidue_modEq (m : ℕ) (i : PatternLabel m) :
    constructionResidue m ≡ constructionOffset m i [MOD constructionDilation m i] :=
  (Nat.chineseRemainderOfFinset (constructionOffset m) (constructionDilation m) Finset.univ
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun _ _ _ _ hij ↦ constructionDilation_pairwise m hij)).property i (Finset.mem_univ i)

theorem constructionResidue_lt_product (m : ℕ) :
    constructionResidue m < constructionProduct m :=
  Nat.chineseRemainderOfFinset_lt_prod (constructionOffset m) (constructionDilation m)
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun _ _ _ _ hij ↦ constructionDilation_pairwise m hij)

noncomputable def constructionBase (m : ℕ) : ℕ :=
  constructionResidue m + constructionModulus m * (6 * m * constructionMaxDilation m + 1)

theorem constructionOffset_le_base (m : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ constructionBase m := by
  have hQ := constructionModulus_pos m
  have hb := constructionOffset_le m i
  unfold constructionBase
  nlinarith

theorem constructionBase_modEq (m : ℕ) (i : PatternLabel m) :
    constructionBase m ≡ constructionOffset m i [MOD constructionDilation m i] := by
  have hQ := constructionDilation_dvd_modulus m i
  have hmul : constructionDilation m i ∣
      constructionModulus m * (6 * m * constructionMaxDilation m + 1) := dvd_mul_of_dvd_left hQ _
  have h := (constructionResidue_modEq m i).add (Nat.modEq_zero_iff_dvd.mpr hmul)
  simpa only [constructionBase, Nat.add_zero] using h

theorem construction_shifts_distinct_mod_prime (m p : ℕ) (hp : p.Prime)
    (hpQ : ¬p ∣ constructionModulus m) :
    ∀ r s : ConstructionShift m, r.val ≡ s.val [MOD p] → r = s :=
  distinct_residues_outside_augmentedModulus _ Subtype.val_injective _ p hp hpQ

noncomputable def constructionCoefficient (m : ℕ) (q : ℝ) (r : ConstructionShift m) : ℝ :=
  shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r.val

def constructionFirstShift (m : ℕ) : ConstructionShift m :=
  ⟨(primorial (dilationPrimeCutoff m) + 1) * (6 * m + 1),
    minimal_mem_retainedShifts m _ _ (retainedLength_pos m)⟩

theorem constructionCoefficient_zero_sum {m : ℕ} (hm : 0 < m) (q : ℝ) :
    (∑ r : ConstructionShift m, constructionCoefficient m q r) = 0 := by
  rw [show (∑ r : ConstructionShift m, constructionCoefficient m q r) =
      ∑ r ∈ retainedShifts m (dilationPrimeCutoff m) (retainedLength m),
        shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r from
      Finset.sum_coe_sort _ _]
  exact sum_shiftCoefficient_zero hm _ _ q

theorem constructionCoefficient_mass_le (m : ℕ) (q : ℝ) :
    (∑ r : ConstructionShift m, |constructionCoefficient m q r|) ≤
      |q| * (9 / 16 : ℝ) ^ m := by
  change (∑ r : ConstructionShift m,
    |shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r.val|) ≤ _
  rw [Finset.sum_coe_sort (retainedShifts m (dilationPrimeCutoff m) (retainedLength m))
    (fun r ↦ |shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r|)]
  exact shiftCoefficient_mass_le m _ _ q

theorem constructionCoefficient_first (m : ℕ) (q : ℝ) :
    constructionCoefficient m q (constructionFirstShift m) = q / 2 ^ (6 * m + 1) :=
  shiftCoefficient_minimal m _ _ (retainedLength_pos m) q

theorem constructionShift_card_le (m : ℕ) :
    Fintype.card (ConstructionShift m) ≤ patternSize m * retainedLength m := by
  simpa only [Fintype.card_coe, patternSize] using
    retainedShifts_card_le m (dilationPrimeCutoff m) (retainedLength m)

noncomputable def constructionPoint (m t : ℕ) : ℕ :=
  constructionBase m + constructionModulus m * t

theorem constructionPoint_pos (m t : ℕ) : 0 < constructionPoint m t := by
  have hQ := constructionModulus_pos m
  unfold constructionPoint constructionBase
  positivity

theorem constructionOffset_le_point (m t : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ constructionPoint m t :=
  (constructionOffset_le_base m i).trans (Nat.le_add_right _ _)

theorem constructionPoint_modEq (m t : ℕ) (i : PatternLabel m) :
    constructionPoint m t ≡ constructionOffset m i [MOD constructionDilation m i] := by
  have h := (constructionBase_modEq m i).add
    (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (constructionDilation_dvd_modulus m i) t))
  simpa only [constructionPoint, Nat.add_zero] using h

theorem construction_quotient_affine (m t : ℕ) (i : PatternLabel m) :
    (constructionPoint m t - constructionOffset m i) / constructionDilation m i =
      (constructionBase m - constructionOffset m i) / constructionDilation m i +
        (constructionModulus m / constructionDilation m i) * t := by
  have hdiv := constructionDilation_dvd_modulus m i
  have hmul : constructionDilation m i * (constructionModulus m / constructionDilation m i) =
      constructionModulus m := Nat.mul_div_cancel' hdiv
  have heq : constructionPoint m t - constructionOffset m i =
      (constructionBase m - constructionOffset m i) +
        constructionDilation m i * ((constructionModulus m / constructionDilation m i) * t) := by
    rw [← Nat.mul_assoc, hmul]
    have hb := constructionOffset_le_base m i
    unfold constructionPoint
    omega
  rw [heq, Nat.add_mul_div_left _ _ (constructionDilation_pos m i)]

end Erdos69.Elementary

end SourceModule36

/- Source module 37: ErdosProblems.Erdos69.ConstructionBounds -/
section SourceModule37
/- # Logarithmic size of the CRT construction -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem patternSize_ge_thirtysix {m : ℕ} (hm : 0 < m) : 36 ≤ patternSize m := by
  change 36 ≤ 36 ^ m
  simpa using Nat.pow_le_pow_right (by norm_num : 0 < 36) (show 1 ≤ m by omega)

theorem constructionMaxDilation_pos (m : ℕ) : 0 < constructionMaxDilation m :=
  roughDilation_pos _ _

theorem log_constructionMaxDilation_le (m : ℕ) :
    Real.log (constructionMaxDilation m : ℝ) ≤ 5 * dilationPrimeCutoff m :=
  log_roughDilation_le (dilationPrimeCutoff_pos m) le_rfl

theorem log_constructionProduct_le (m : ℕ) :
    Real.log (constructionProduct m : ℝ) ≤ 5 * patternSize m * dilationPrimeCutoff m := by
  rw [constructionProduct, Nat.cast_prod, Real.log_prod
    (fun i _ ↦ by exact_mod_cast (constructionDilation_pos m i).ne')]
  calc
    _ ≤ ∑ _i : PatternLabel m, (5 : ℝ) * dilationPrimeCutoff m := by
      apply Finset.sum_le_sum
      intro i hi
      have hlog : Real.log (constructionDilation m i : ℝ) ≤
          Real.log (constructionMaxDilation m : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast constructionDilation_pos m i)
        exact_mod_cast constructionDilation_le_max m i
      exact hlog.trans (log_constructionMaxDilation_le m)
    _ = _ := by simp [card_patternLabel, patternSize]; ring

theorem constructionShift_le (m : ℕ) (r : ConstructionShift m) :
    r.val ≤ constructionMaxDilation m * (6 * m + retainedLength m) := by
  obtain ⟨⟨i, k⟩, ht, heq⟩ := Finset.mem_image.mp r.property
  rw [← heq]
  apply (patternShift_le_dilation_mul m (dilationPrimeCutoff m) _ i).trans
  exact Nat.mul_le_mul (constructionDilation_le_max m i) (by have hk := k.isLt; omega)

theorem log_constructionModulus_raw (m : ℕ) :
    Real.log (constructionModulus m : ℝ) ≤
      5 * patternSize m * dilationPrimeCutoff m +
      ((patternSize m : ℝ) * retainedLength m) ^ 2 *
        (5 * dilationPrimeCutoff m + (6 * m + retainedLength m)) := by
  have hM : 0 < constructionMaxDilation m * (6 * m + retainedLength m) :=
    Nat.mul_pos (constructionMaxDilation_pos m) (by have h := retainedLength_pos m; omega)
  have hcollision := log_collisionProduct_le (fun r : ConstructionShift m ↦ r.val)
    Subtype.val_injective _ hM (constructionShift_le m)
  have hlogM : Real.log (constructionMaxDilation m * (6 * m + retainedLength m) : ℕ) ≤
      5 * dilationPrimeCutoff m + (6 * m + retainedLength m : ℕ) := by
    have hlen : (0 : ℝ) < (6 * m + retainedLength m : ℕ) := by
      exact_mod_cast (show 0 < 6 * m + retainedLength m by have h := retainedLength_pos m; omega)
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (constructionMaxDilation_pos m).ne') hlen.ne']
    have hloglen := Real.log_le_sub_one_of_pos hlen
    linarith [log_constructionMaxDilation_le m]
  have hcard : (Fintype.card (ConstructionShift m) : ℝ) ≤
      (patternSize m : ℝ) * retainedLength m := by exact_mod_cast constructionShift_card_le m
  have hCl : Real.log (constructionCollisionProduct m : ℝ) ≤
      ((patternSize m : ℝ) * retainedLength m) ^ 2 *
        (5 * dilationPrimeCutoff m + (6 * m + retainedLength m)) := by
    apply hcollision.trans
    gcongr
    exact_mod_cast hlogM
  exact (log_augmentedModulus_le (constructionProduct_pos m)
    (constructionCollisionProduct_pos m)).trans (add_le_add (log_constructionProduct_le m) hCl)

theorem patternSize_pow_five_le_primeCutoff {m : ℕ} (hm : 0 < m) :
    patternSize m ^ 5 ≤ dilationPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  calc
    patternSize m ^ 5 ≤ (2 ^ patternSize m) ^ 5 :=
      Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (patternSize m * 5) := by rw [pow_mul]
    _ ≤ 2 ^ (patternSize m ^ 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith

theorem polynomial_primeCutoff_le_excluded {m : ℕ} (hm : 0 < m) :
    patternSize m ^ 12 * dilationPrimeCutoff m ≤ excludedPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m * 12 + patternSize m ^ 2 ≤ patternSize m ^ 3 := by
    have h₁ := Nat.mul_le_mul_right (patternSize m) (show 12 ≤ patternSize m by omega)
    have h₂ := Nat.mul_le_mul_right (patternSize m ^ 2) (show 2 ≤ patternSize m by omega)
    nlinarith
  calc
    _ ≤ (2 ^ patternSize m) ^ 12 * dilationPrimeCutoff m :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = 2 ^ (patternSize m * 12 + patternSize m ^ 2) := by
      rw [dilationPrimeCutoff, pow_add, pow_mul]
    _ ≤ excludedPrimeCutoff m := Nat.pow_le_pow_right (by norm_num) hexp

theorem total_retainedLength_le_size_pow_five {m : ℕ} (hm : 0 < m) :
    6 * m + retainedLength m ≤ patternSize m ^ 5 := by
  have hN := patternSize_ge_thirtysix hm
  have hpow : patternSize m ≤ patternSize m ^ 4 := by
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)
  have hthree : 3 * patternSize m ^ 4 ≤ patternSize m * patternSize m ^ 4 :=
    Nat.mul_le_mul_right _ (by omega)
  unfold retainedLength fluctuationScale
  have hK := initialLength_le_patternSize m
  calc
    _ ≤ 3 * patternSize m ^ 4 := by omega
    _ ≤ patternSize m * patternSize m ^ 4 := hthree
    _ = patternSize m ^ 5 := by ring

theorem log_constructionModulus_le_size_polynomial {m : ℕ} (hm : 0 < m) :
    Real.log (constructionModulus m : ℝ) ≤ (patternSize m : ℝ) ^ 12 * dilationPrimeCutoff m := by
  let N : ℝ := patternSize m
  let P : ℝ := dilationPrimeCutoff m
  have hN : 36 ≤ N := by dsimp [N]; exact_mod_cast patternSize_ge_thirtysix hm
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hlen : ((6 * m + retainedLength m : ℕ) : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast (total_retainedLength_le_size_pow_five hm).trans
      (patternSize_pow_five_le_primeCutoff hm)
  have hH : (retainedLength m : ℝ) = 2 * N ^ 4 := by
    simp [retainedLength, fluctuationScale, N]
  have hraw := log_constructionModulus_raw m
  have hraw' : Real.log (constructionModulus m : ℝ) ≤
      5 * N * P + (N * (2 * N ^ 4)) ^ 2 * (5 * P + P) := by
    apply hraw.trans
    rw [hH]
    gcongr
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hH] using hlen
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlow : N ^ 2 ≤ N ^ 11 := pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ 5 * N * P + (N * (2 * N ^ 4)) ^ 2 * (5 * P + P) := hraw'
    _ ≤ N ^ 2 * P + (N * (2 * N ^ 4)) ^ 2 * (N * P) := by
      apply add_le_add
      · nlinarith [mul_nonneg (show 0 ≤ N - 5 by linarith) (mul_nonneg hN0 hP)]
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith
    _ = (N ^ 2 + 4 * N ^ 11) * P := by ring
    _ ≤ (5 * N ^ 11) * P := by gcongr; linarith
    _ ≤ N ^ 12 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have h := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ N by linarith)
        (pow_nonneg hN0 11)
      simpa only [pow_succ', show N ^ (11 + 1) = N ^ 12 by rfl] using h

theorem log_constructionModulus_le_excluded {m : ℕ} (hm : 0 < m) :
    Real.log (constructionModulus m : ℝ) ≤ excludedPrimeCutoff m := by
  apply (log_constructionModulus_le_size_polynomial hm).trans
  exact_mod_cast polynomial_primeCutoff_le_excluded hm

end Erdos69.Elementary

end SourceModule37

/- Source module 38: ErdosProblems.Erdos69.ParameterLimits -/
section SourceModule38
/- # Limits governing the explicit parameter hierarchy -/

open Filter
open scoped Topology

namespace Erdos69.Elementary

noncomputable def coefficientMassBound (q : ℝ) (m : ℕ) : ℝ := |q| * (9 / 16 : ℝ) ^ m
noncomputable def firstCoefficient (q : ℝ) (m : ℕ) : ℝ := q / 2 ^ (6 * m + 1)

theorem tendsto_patternSize : Tendsto patternSize atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 36)

theorem tendsto_fluctuationScale : Tendsto fluctuationScale atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_patternSize
  filter_upwards with m
  change patternSize m ≤ patternSize m ^ 4
  simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)

theorem tendsto_inverse_patternSize :
    Tendsto (fun m ↦ (1 : ℝ) / patternSize m) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_patternSize

theorem tendsto_coefficientMassBound (q : ℝ) :
    Tendsto (coefficientMassBound q) atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ ↦ |q| * (9 / 16 : ℝ) ^ m) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 16)
      (by norm_num : (9 / 16 : ℝ) < 1)).const_mul |q|

theorem tendsto_index_mul_coefficientMassBound (q : ℝ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) * coefficientMassBound q m) atTop (𝓝 0) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (9 / 16 : ℝ)) (by norm_num)).summable.tendsto_atTop_zero
  simpa only [coefficientMassBound, mul_left_comm, mul_zero] using h.const_mul |q|

theorem tendsto_coefficientMassBound_affine (q A D : ℝ) :
    Tendsto (fun m ↦ coefficientMassBound q m * (A * m + D)) atTop (𝓝 0) := by
  have h₁ := (tendsto_index_mul_coefficientMassBound q).const_mul A
  have h₂ := (tendsto_coefficientMassBound q).mul_const D
  convert! h₁.add h₂ using 1
  · funext m
    ring
  · ring_nf

theorem tendsto_index_add_one_div_two_pow :
    Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) / 2 ^ k) atTop (𝓝 0) := by
  have h₁ := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)).summable.tendsto_atTop_zero
  have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  convert! h₁.add h₂ using 1
  · funext k
    simp only [div_pow, one_pow]
    ring
  · ring_nf

theorem tendsto_scale_tail :
    Tendsto (fun m ↦ ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m)
      atTop (𝓝 0) :=
  tendsto_index_add_one_div_two_pow.comp tendsto_fluctuationScale

theorem firstCoefficient_square_scale (q : ℝ) (m : ℕ) :
    firstCoefficient q m ^ 2 * fluctuationScale m =
      (q ^ 2 / 4) * (6561 / 16 : ℝ) ^ m := by
  have hden : (2 : ℝ) ^ (6 * m + 1) = 2 * (64 : ℝ) ^ m := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have hscale : (fluctuationScale m : ℝ) = ((36 : ℝ) ^ 4) ^ m := by
    simp only [fluctuationScale, patternSize, Nat.cast_pow, Nat.cast_ofNat, pow_right_comm]
  have hratio : (6561 / 16 : ℝ) = 36 ^ 4 / 64 ^ 2 := by norm_num
  rw [firstCoefficient, hden, hscale, hratio]
  simp_rw [div_pow]
  rw [pow_right_comm (64 : ℝ) 2 m]
  ring

theorem tendsto_firstCoefficient_square_scale {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ firstCoefficient q m ^ 2 * fluctuationScale m) atTop atTop := by
  simp_rw [firstCoefficient_square_scale]
  exact (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 6561 / 16)).const_mul_atTop (by positivity)

theorem tendsto_independent_decay {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ Real.exp (-(firstCoefficient q m ^ 2 * fluctuationScale m)))
      atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_firstCoefficient_square_scale hq))

end Erdos69.Elementary

end SourceModule38

/- Source module 39: ErdosProblems.Erdos69.CutoffBounds -/
section SourceModule39
/- # Comparisons and exact logarithms of the integer cutoffs -/

namespace Erdos69.Elementary

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem log_log_two_nonpos : Real.log (Real.log (2 : ℝ)) ≤ 0 :=
  Real.log_nonpos (Real.log_pos (by norm_num)).le log_two_le_one

theorem log_dilationPrimeCutoff (m : ℕ) :
    Real.log (dilationPrimeCutoff m : ℝ) = (patternSize m : ℝ) ^ 2 * Real.log 2 := by
  simp [dilationPrimeCutoff, Real.log_pow]

theorem log_smallPrimeCutoff (m : ℕ) :
    Real.log (smallPrimeCutoff m : ℝ) = (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [smallPrimeCutoff, Real.log_pow]

theorem log_progressionLength (m : ℕ) :
    Real.log (progressionLength m : ℝ) =
      40 * fluctuationScale m * (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [progressionLength, Real.log_pow, log_smallPrimeCutoff, mul_assoc]

theorem log_intermediatePrimeCutoff (m : ℕ) :
    Real.log (intermediatePrimeCutoff m : ℝ) =
      20 * fluctuationScale m * (2 : ℝ) ^ fluctuationScale m * Real.log 2 := by
  simp [intermediatePrimeCutoff, Real.log_pow, log_smallPrimeCutoff, mul_assoc]

theorem log_excludedPrimeCutoff (m : ℕ) :
    Real.log (excludedPrimeCutoff m : ℝ) = (patternSize m : ℝ) ^ 3 * Real.log 2 := by
  simp [excludedPrimeCutoff, Real.log_pow]

theorem smallPrimeCutoff_ge_two (m : ℕ) : 2 ≤ smallPrimeCutoff m := by
  unfold smallPrimeCutoff
  have h : 0 < 2 ^ fluctuationScale m := by positivity
  exact Nat.one_lt_two_pow h.ne'

theorem excludedPrimeCutoff_ge_two (m : ℕ) : 2 ≤ excludedPrimeCutoff m := by
  unfold excludedPrimeCutoff
  exact Nat.one_lt_two_pow (Nat.pow_pos (patternSize_pos m)).ne'

theorem log_log_smallPrimeCutoff (m : ℕ) :
    Real.log (Real.log (smallPrimeCutoff m : ℝ)) =
      (fluctuationScale m : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  rw [log_smallPrimeCutoff, Real.log_mul (by positivity)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', Real.log_pow]

theorem log_log_intermediate_sub_small (m : ℕ) :
    Real.log (Real.log (intermediatePrimeCutoff m : ℝ)) -
      Real.log (Real.log (smallPrimeCutoff m : ℝ)) =
        Real.log (20 : ℝ) + 4 * m * Real.log 36 := by
  have hscale : (0 : ℝ) < fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  have hlogy : 0 < Real.log (smallPrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast smallPrimeCutoff_ge_two m)
  have hlogR : Real.log (intermediatePrimeCutoff m : ℝ) =
      (20 * fluctuationScale m : ℝ) * Real.log (smallPrimeCutoff m : ℝ) := by
    simp [intermediatePrimeCutoff, Real.log_pow]
  rw [hlogR, Real.log_mul (by positivity) hlogy.ne', add_sub_cancel_right,
    Real.log_mul (by norm_num) hscale.ne']
  simp only [fluctuationScale, patternSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

theorem twice_excluded_le_two_pow_scale {m : ℕ} (hm : 0 < m) :
    2 * excludedPrimeCutoff m ≤ 2 ^ fluctuationScale m := by
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m ^ 3 + 1 ≤ patternSize m ^ 4 := by
    have hp := Nat.pow_pos (patternSize_pos m) (n := 3)
    have hmul := Nat.mul_le_mul_right (patternSize m ^ 3) (show 2 ≤ patternSize m by omega)
    nlinarith
  unfold excludedPrimeCutoff fluctuationScale
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hexp

theorem constructionModulus_le_smallPrimeCutoff {m : ℕ} (hm : 0 < m) :
    constructionModulus m ≤ smallPrimeCutoff m := by
  have hbound := log_constructionModulus_le_excluded hm
  have htwo : (2 : ℝ) * excludedPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast twice_excluded_le_two_pow_scale hm
  have hlog : Real.log (constructionModulus m : ℝ) ≤ Real.log (smallPrimeCutoff m : ℝ) := by
    rw [log_smallPrimeCutoff]
    have hp : 0 ≤ (2 : ℝ) ^ fluctuationScale m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right half_le_log_two hp]
  have hQ : (0 : ℝ) < constructionModulus m := by exact_mod_cast constructionModulus_pos m
  have hy : (0 : ℝ) < smallPrimeCutoff m := by exact_mod_cast smallPrimeCutoff_pos m
  exact_mod_cast (Real.log_le_log_iff hQ hy).mp hlog

theorem twice_shift_card_le_excluded {m : ℕ} (hm : 0 < m) :
    2 * Fintype.card (ConstructionShift m) ≤ excludedPrimeCutoff m := by
  have hcard := constructionShift_card_le m
  have hN := patternSize_ge_thirtysix hm
  have hexp : patternSize m * 5 + 2 ≤ patternSize m ^ 3 := by
    have hmul := Nat.mul_le_mul_right (patternSize m ^ 2) (show 2 ≤ patternSize m by omega)
    nlinarith
  calc
    _ ≤ 4 * patternSize m ^ 5 := by
      unfold retainedLength fluctuationScale at hcard
      calc
        _ ≤ 2 * (patternSize m * (2 * patternSize m ^ 4)) := Nat.mul_le_mul_left 2 hcard
        _ = _ := by ring
    _ ≤ 4 * (2 ^ patternSize m) ^ 5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = 2 ^ (patternSize m * 5 + 2) := by rw [pow_add, pow_mul]; ring
    _ ≤ excludedPrimeCutoff m := Nat.pow_le_pow_right (by norm_num) hexp

end Erdos69.Elementary

end SourceModule39

/- Source module 40: ErdosProblems.Erdos69.ParameterPrimeMass -/
section SourceModule40
/- # Reciprocal-prime mass in the chosen parameter regime -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem primeReciprocalSum_lower {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (x : ℕ) (hx : 2 ≤ x) : Real.log (Real.log (x : ℝ)) - C ≤ primeReciprocalSum x := by
  linarith [(abs_le.mp (hC x hx)).1]

theorem primeReciprocalSum_upper {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (x : ℕ) (hx : 2 ≤ x) : primeReciprocalSum x ≤ Real.log (Real.log (x : ℝ)) + C := by
  linarith [(abs_le.mp (hC x hx)).2]

theorem smallPrime_reciprocal_upper {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (m : ℕ) : primeReciprocalSum (smallPrimeCutoff m) ≤
      (fluctuationScale m : ℝ) * (Real.log 2 + C + 1) := by
  have hu := primeReciprocalSum_upper hC _ (smallPrimeCutoff_ge_two m)
  rw [log_log_smallPrimeCutoff] at hu
  have hB : (1 : ℝ) ≤ fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  nlinarith [log_log_two_nonpos]

theorem excludedPrime_reciprocal_upper {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (m : ℕ) : primeReciprocalSum (excludedPrimeCutoff m) ≤
      (patternSize m : ℝ) ^ 3 * Real.log 2 + C := by
  have hu := primeReciprocalSum_upper hC _ (excludedPrimeCutoff_ge_two m)
  have hp : 0 < Real.log (excludedPrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast excludedPrimeCutoff_ge_two m)
  have hlog := Real.log_le_sub_one_of_pos hp
  rw [log_excludedPrimeCutoff] at hlog hu
  linarith

theorem construction_primeFactor_reciprocal_le {m : ℕ} (hm : 0 < m) :
    (∑ p ∈ (constructionModulus m).primeFactors, (1 : ℝ) / p) ≤
      primeReciprocalSum (excludedPrimeCutoff m) + 1 / Real.log 2 := by
  have h := reciprocal_primeFactors_le_cutoff (constructionModulus m) (excludedPrimeCutoff m)
    (constructionModulus_pos m) (by have hp := excludedPrimeCutoff_ge_two m; omega)
  apply h.trans
  apply add_le_add le_rfl
  have hp : (0 : ℝ) < excludedPrimeCutoff m := by
    exact_mod_cast (show 0 < excludedPrimeCutoff m by have h := excludedPrimeCutoff_ge_two m; omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    Real.log (constructionModulus m : ℝ) / ((excludedPrimeCutoff m : ℝ) * Real.log 2) ≤
        (excludedPrimeCutoff m : ℝ) / ((excludedPrimeCutoff m : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right (log_constructionModulus_le_excluded hm) (by positivity)
    _ = _ := by field_simp

theorem goodPrime_mass_parameter_lower {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) :
    ((fluctuationScale m : ℝ) - 2 * (patternSize m : ℝ) ^ 3) * Real.log 2 +
      Real.log (Real.log 2) - 3 * C - 1 / Real.log 2 ≤
        ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
          (1 : ℝ) / p := by
  have hl := goodPrime_reciprocal_lower (constructionModulus m) (excludedPrimeCutoff m)
    (smallPrimeCutoff m) (constructionModulus_pos m)
  have hs := primeReciprocalSum_lower hC _ (smallPrimeCutoff_ge_two m)
  rw [log_log_smallPrimeCutoff] at hs
  have he := excludedPrime_reciprocal_upper hC m
  have hf := construction_primeFactor_reciprocal_le hm
  linarith

theorem eventually_goodPrime_mass_ge_quarter {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C) :
    ∀ᶠ m : ℕ in atTop, (fluctuationScale m : ℝ) / 4 ≤
      ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
        (1 : ℝ) / p := by
  let D := 3 * C + 1 / Real.log 2 - Real.log (Real.log 2)
  have hB : Tendsto (fun m ↦ (fluctuationScale m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_fluctuationScale
  filter_upwards [eventually_ge_atTop (1 : ℕ), hB.eventually (eventually_ge_atTop (8 * D))]
    with m hm hlarge
  have hm0 : 0 < m := by omega
  have hN : (8 : ℝ) ≤ patternSize m := by
    have hn := patternSize_ge_thirtysix hm0
    exact_mod_cast (show 8 ≤ patternSize m by omega)
  have hBcast : (fluctuationScale m : ℝ) = (patternSize m : ℝ) ^ 4 := by
    simp [fluctuationScale]
  have hsmall : 8 * (patternSize m : ℝ) ^ 3 ≤ fluctuationScale m := by
    rw [hBcast]
    have h := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ (patternSize m : ℝ) ^ 3)
    nlinarith
  have hpos : 0 ≤ (fluctuationScale m : ℝ) - 2 * (patternSize m : ℝ) ^ 3 := by
    nlinarith [show (0 : ℝ) ≤ (patternSize m : ℝ) ^ 3 by positivity]
  have hhalf := mul_le_mul_of_nonneg_right half_le_log_two hpos
  have hl := goodPrime_mass_parameter_lower hC hm0
  dsimp [D] at hlarge
  nlinarith

end Erdos69.Elementary

end SourceModule40

/- Source module 41: ErdosProblems.Erdos69.ConstructionModel -/
section SourceModule41
/- # The finite prime model for the explicit construction -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev ConstructionPrime (m : ℕ) := ↥(freePrimes (constructionModulus m) (smallPrimeCutoff m))

theorem constructionPrime_prime (m : ℕ) (p : ConstructionPrime m) : p.val.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp p.property).1).2

theorem constructionPrime_pos (m : ℕ) (p : ConstructionPrime m) : 0 < p.val :=
  (constructionPrime_prime m p).pos

theorem constructionPrime_not_dvd (m : ℕ) (p : ConstructionPrime m) :
    ¬p.val ∣ constructionModulus m := (Finset.mem_filter.mp p.property).2

theorem constructionPrime_coprime (m : ℕ) (p : ConstructionPrime m) :
    (constructionModulus m).Coprime p.val :=
  ((constructionPrime_prime m p).coprime_iff_not_dvd.mpr (constructionPrime_not_dvd m p)).symm

theorem constructionPrime_pairwise (m : ℕ) :
    Pairwise (fun p r : ConstructionPrime m ↦ p.val.Coprime r.val) := by
  intro p r hpr
  apply (constructionPrime_prime m p).coprime_iff_not_dvd.mpr
  intro hd
  have heq : p.val = r.val := (Nat.dvd_prime (constructionPrime_prime m r)).mp hd |>.resolve_left
    (constructionPrime_prime m p).ne_one
  exact hpr (Subtype.ext heq)

theorem constructionPrime_distinct_residues (m : ℕ) (p : ConstructionPrime m) :
    ∀ r s : ConstructionShift m, r.val ≡ s.val [MOD p.val] → r = s :=
  construction_shifts_distinct_mod_prime m p.val (constructionPrime_prime m p)
    (constructionPrime_not_dvd m p)

theorem constructionShift_card_le_prime (m : ℕ) (p : ConstructionPrime m) :
    Fintype.card (ConstructionShift m) ≤ p.val :=
  card_le_of_distinct_residues _ (constructionPrime_pos m p) _
    (constructionPrime_distinct_residues m p)

noncomputable def constructionPrimeLaw (m : ℕ) :
    FiniteLaw (ConstructionPrime m → Option (ConstructionShift m)) :=
  FiniteLaw.independentProduct (fun p ↦ FiniteLaw.categorical (ConstructionShift m) p.val
    (constructionPrime_pos m p) (constructionShift_card_le_prime m p))

noncomputable def constructionModelValue (q : ℝ) (m : ℕ)
    (x : ConstructionPrime m → Option (ConstructionShift m)) : ℝ :=
  ∑ p, FiniteLaw.optionalValue (constructionCoefficient m q) (x p)

noncomputable def constructionSmallValue (q : ℝ) (m t : ℕ) : ℝ :=
  ∑ p : ConstructionPrime m, ∑ r : ConstructionShift m,
    constructionCoefficient m q r *
      (if p.val ∣ constructionPoint m t + r.val then (1 : ℝ) else 0)

theorem constructionPrime_reciprocal_le (m : ℕ) :
    (∑ p : ConstructionPrime m, (1 : ℝ) / p.val) ≤ primeReciprocalSum (smallPrimeCutoff m) := by
  rw [Finset.sum_coe_sort (freePrimes (constructionModulus m) (smallPrimeCutoff m))
    (fun p : ℕ ↦ (1 : ℝ) / p)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ ↦ by positivity)

theorem construction_goodPrime_sum (m : ℕ) :
    (∑ p ∈ (Finset.univ : Finset (ConstructionPrime m)).filter
        (fun p ↦ excludedPrimeCutoff m < p.val), (1 : ℝ) / p.val) =
      ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
        (1 : ℝ) / p := by
  rw [Finset.sum_filter,
    Finset.sum_coe_sort (freePrimes (constructionModulus m) (smallPrimeCutoff m))
      (fun p ↦ if excludedPrimeCutoff m < p then (1 : ℝ) / p else 0), ← Finset.sum_filter]
  have heq : (freePrimes (constructionModulus m) (smallPrimeCutoff m)).filter
      (fun p ↦ excludedPrimeCutoff m < p) =
        goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m) := by
    ext p
    simp [freePrimes, goodPrimes, and_left_comm, and_comm, and_assoc]
  rw [heq]

theorem constructionModel_fourier_le {m : ℕ} (hm : 0 < m) (q : ℝ)
    (hfirst : |firstCoefficient q m| ≤ 1 / 2) :
    ‖(constructionPrimeLaw m).complexMean (fun x ↦ fourierPhase (constructionModelValue q m x))‖ ≤
      Real.exp (-4 * firstCoefficient q m ^ 2 *
        ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
          (1 : ℝ) / p) := by
  classical
  let S := (Finset.univ : Finset (ConstructionPrime m)).filter
    (fun p ↦ excludedPrimeCutoff m < p.val)
  have hS (p : ConstructionPrime m) (hp : p ∈ S) :
      2 * Fintype.card (ConstructionShift m) ≤ p.val :=
    (twice_shift_card_le_excluded hm).trans (Finset.mem_filter.mp hp).2.le
  have hc : |constructionCoefficient m q (constructionFirstShift m)| ≤ 1 / 2 := by
    simpa only [constructionCoefficient_first, firstCoefficient] using hfirst
  have h := FiniteLaw.categorical_product_fourier_le (fun p : ConstructionPrime m ↦ p.val)
    (constructionPrime_pos m) (constructionShift_card_le_prime m) S hS
    (constructionCoefficient m q) (constructionFirstShift m) hc
  rw [constructionCoefficient_first, construction_goodPrime_sum] at h
  exact h

noncomputable def constructionLaw (m : ℕ) : FiniteLaw (Fin (progressionLength m)) :=
  FiniteLaw.uniform _ (progressionLength_pos m)

noncomputable def smallCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase (constructionSmallValue q m t.val))

noncomputable def modelCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionPrimeLaw m).complexMean (fun x ↦ fourierPhase (constructionModelValue q m x))

theorem constructionPrime_card_le (m : ℕ) :
    Fintype.card (ConstructionPrime m) ≤ smallPrimeCutoff m := by
  have hsubset : freePrimes (constructionModulus m) (smallPrimeCutoff m) ⊆
      Finset.Icc 1 (smallPrimeCutoff m) := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  have hcard := Finset.card_le_card hsubset
  simpa only [Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem firstCoefficient_abs_le_mass (q : ℝ) (m : ℕ) :
    |firstCoefficient q m| ≤ coefficientMassBound q m := by
  have hsingle : |constructionCoefficient m q (constructionFirstShift m)| ≤
      ∑ r : ConstructionShift m, |constructionCoefficient m q r| :=
    Finset.single_le_sum (fun r _ ↦ abs_nonneg (constructionCoefficient m q r))
      (Finset.mem_univ (constructionFirstShift m))
  rw [constructionCoefficient_first] at hsingle
  exact hsingle.trans (constructionCoefficient_mass_le m q)

theorem construction_fourier_transfer_raw {m : ℕ} (hm : 0 < m) (q : ℝ)
    (hε : coefficientMassBound q m ≤ 1)
    (hsmall : 4 * Real.pi * coefficientMassBound q m ≤ 1) :
    ‖smallCharacteristic q m - modelCharacteristic q m‖ ≤
      ((smallPrimeCutoff m : ℝ) ^ momentOrder m / progressionLength m) * (1 + momentOrder m) *
        Real.exp (2 * Real.pi) +
        4 * momentOrder m *
          Real.exp ((4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 *
            ∑ p : ConstructionPrime m, (1 : ℝ) / p.val) * (1 / 2 : ℝ) ^ momentOrder m := by
  have hsize : (Fintype.card (ConstructionPrime m) : ℝ) * coefficientMassBound q m ≤
      smallPrimeCutoff m := by
    calc
      _ ≤ (Fintype.card (ConstructionPrime m) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      _ ≤ _ := by simpa using (show (Fintype.card (ConstructionPrime m) : ℝ) ≤ smallPrimeCutoff m by
          exact_mod_cast constructionPrime_card_le m)
  exact FiniteLaw.affine_fourier_transfer (fun p : ConstructionPrime m ↦ p.val)
    (constructionPrime_pos m) (constructionPrime_pairwise m)
    (constructionModulus m) (constructionBase m) (constructionPrime_coprime m)
    (fun r : ConstructionShift m ↦ r.val) (constructionPrime_distinct_residues m)
    (constructionShift_card_le_prime m) (constructionCoefficient m q)
    (constructionCoefficient_zero_sum hm q) (coefficientMassBound q m) (smallPrimeCutoff m)
    (constructionCoefficient_mass_le m q) hsmall
    (by have h := smallPrimeCutoff_ge_two m; exact_mod_cast (show 1 ≤ smallPrimeCutoff m by omega))
    hsize (progressionLength m) (progressionLength_pos m) (momentOrder m)
    (momentOrder_pos m) (momentOrder_even m)

end Erdos69.Elementary

end SourceModule41

/- Source module 42: ErdosProblems.Erdos69.MomentErrorBounds -/
section SourceModule42
/- # Vanishing error in the concrete finite-moment comparison -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem construction_moment_ratio_le (m : ℕ) :
    (smallPrimeCutoff m : ℝ) ^ momentOrder m / progressionLength m ≤
      (1 : ℝ) / 2 ^ fluctuationScale m := by
  have hy : (0 : ℝ) < smallPrimeCutoff m := by exact_mod_cast smallPrimeCutoff_pos m
  have hp : (2 : ℝ) ^ fluctuationScale m ≤
      (smallPrimeCutoff m : ℝ) ^ (38 * fluctuationScale m) := by
    calc
      _ ≤ (smallPrimeCutoff m : ℝ) ^ fluctuationScale m :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast smallPrimeCutoff_ge_two m) _
      _ ≤ _ := pow_le_pow_right₀ (by
        have h := smallPrimeCutoff_ge_two m
        exact_mod_cast (show 1 ≤ smallPrimeCutoff m by omega)) (by omega)
  calc
    _ = (1 : ℝ) / (smallPrimeCutoff m : ℝ) ^ (38 * fluctuationScale m) := by
      rw [smallPrimeCutoff_moment_ratio, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      field_simp
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hp

noncomputable def modelComparisonError (m : ℕ) : ℝ :=
  (2 * Real.exp (2 * Real.pi) + 8) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m

theorem tendsto_modelComparisonError : Tendsto modelComparisonError atTop (𝓝 0) := by
  have h := tendsto_scale_tail.const_mul (2 * Real.exp (2 * Real.pi) + 8)
  change Tendsto (fun m ↦ (2 * Real.exp (2 * Real.pi) + 8) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using h

theorem construction_mgf_exp_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (q : ℝ) (m : ℕ)
    (hε : (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 * (Real.log 2 + C + 1) ≤ Real.log 2) :
    Real.exp ((4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 *
      ∑ p : ConstructionPrime m, (1 : ℝ) / p.val) ≤ (2 : ℝ) ^ fluctuationScale m := by
  have hmass := (constructionPrime_reciprocal_le m).trans (smallPrime_reciprocal_upper hC0 hC m)
  have h₁ := mul_le_mul_of_nonneg_left hmass
    (by positivity : 0 ≤ (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2)
  have h₂ := mul_le_mul_of_nonneg_right hε
    (by positivity : (0 : ℝ) ≤ fluctuationScale m)
  have he : Real.exp ((fluctuationScale m : ℝ) * Real.log 2) = (2 : ℝ) ^ fluctuationScale m := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [← he]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem construction_fourier_transfer_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) (q : ℝ) (hε : coefficientMassBound q m ≤ 1)
    (hsmall : 4 * Real.pi * coefficientMassBound q m ≤ 1)
    (hmgf : (4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 * (Real.log 2 + C + 1) ≤ Real.log 2) :
    ‖smallCharacteristic q m - modelCharacteristic q m‖ ≤ modelComparisonError m := by
  have h := construction_fourier_transfer_raw hm q hε hsmall
  have he := construction_mgf_exp_le hC0 hC q m hmgf
  have hr := construction_moment_ratio_le m
  apply h.trans
  calc
    _ ≤ ((1 : ℝ) / 2 ^ fluctuationScale m) * (1 + momentOrder m) * Real.exp (2 * Real.pi) +
        4 * momentOrder m * (2 : ℝ) ^ fluctuationScale m * (1 / 2 : ℝ) ^ momentOrder m := by
      gcongr
    _ = ((1 + 2 * fluctuationScale m) * Real.exp (2 * Real.pi) + 8 * fluctuationScale m) /
        (2 : ℝ) ^ fluctuationScale m := by
      simp only [momentOrder, Nat.cast_mul, Nat.cast_ofNat, pow_mul, div_pow, one_pow]
      rw [pow_right_comm (2 : ℝ) 2 (fluctuationScale m)]
      field_simp
      ring
    _ ≤ modelComparisonError m := by
      unfold modelComparisonError
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [Real.exp_pos (2 * Real.pi)]

theorem tendsto_small_sub_model_norm (q : ℝ) :
    Tendsto (fun m ↦ ‖smallCharacteristic q m - modelCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := tendsto_coefficientMassBound q
  have hsmall := hε.const_mul (4 * Real.pi)
  have hmgf := ((hε.pow 2).const_mul ((4 * Real.pi) ^ 2)).mul_const (Real.log 2 + C + 1)
  simp only [mul_zero, zero_pow (by omega : 2 ≠ 0), zero_mul] at hsmall hmgf
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _
    tendsto_modelComparisonError
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hmgf.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
    with m hm he hs hg
  exact construction_fourier_transfer_le hC0 hC (by omega) q he.le hs.le hg.le

end Erdos69.Elementary

end SourceModule42

/- Source module 43: ErdosProblems.Erdos69.ProgressionBounds -/
section SourceModule43
/- # A common upper bound for all sampled integers and retained shifts -/

namespace Erdos69.Elementary

def constructionUpperBound (m : ℕ) : ℕ :=
  (constructionModulus m + 1) * (6 * m + retainedLength m + progressionLength m + 3) *
    (constructionMaxDilation m + 1)

theorem constructionResidue_le_modulus (m : ℕ) : constructionResidue m ≤ constructionModulus m :=
  (constructionResidue_lt_product m).le.trans
    (Nat.le_of_dvd (constructionModulus_pos m) (dvd_augmentedModulus _ _))

theorem constructionPoint_add_le_upper (m t r : ℕ) (ht : t ≤ progressionLength m)
    (hr : r ≤ constructionMaxDilation m * (6 * m + retainedLength m)) :
    constructionPoint m t + r ≤ constructionUpperBound m := by
  let Q := constructionModulus m
  let A := constructionMaxDilation m
  let K := 6 * m
  let H := retainedLength m
  let T := progressionLength m
  have hA : 1 ≤ A := constructionMaxDilation_pos m
  have hb : constructionBase m ≤ Q * (K * A + 2) := by
    have hn := constructionResidue_le_modulus m
    unfold constructionBase
    dsimp [Q, K, A]
    nlinarith
  calc
    constructionPoint m t + r ≤ Q * (K * A + 2 + T) + A * (K + H) := by
      unfold constructionPoint
      dsimp [Q, K, A, H, T] at *
      nlinarith
    _ ≤ Q * (A * (K + T + 2)) + A * (K + H) := by
      gcongr
      nlinarith
    _ ≤ (Q + 1) * A * (K + H + T + 2) := by
      have hnonneg := Nat.zero_le (Q * A * H + A * T + 2 * A)
      nlinarith only [hnonneg]
    _ ≤ (Q + 1) * (K + H + T + 3) * (A + 1) := by
      nlinarith
    _ = constructionUpperBound m := rfl

theorem sampled_shift_le_upper (m : ℕ) (t : Fin (progressionLength m)) (r : ConstructionShift m) :
    constructionPoint m t.val + r.val ≤ constructionUpperBound m :=
  constructionPoint_add_le_upper m t.val r.val t.isLt.le (constructionShift_le m r)

theorem sampled_dilation_le_upper (m : ℕ) (t : Fin (progressionLength m)) (i : PatternLabel m) :
    constructionPoint m t.val + constructionDilation m i ≤ constructionUpperBound m := by
  apply constructionPoint_add_le_upper m t.val _ t.isLt.le
  apply (constructionDilation_le_max m i).trans
  have hlen : 1 ≤ 6 * m + retainedLength m := by have h := retainedLength_pos m; omega
  simpa using Nat.mul_le_mul_left (constructionMaxDilation m) hlen

theorem log_nat_add_one_le (n : ℕ) (hn : 0 < n) :
    Real.log (n + 1 : ℕ) ≤ Real.log (n : ℝ) + 1 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * n := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have h := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by norm_num) hpos.ne'] at h
  linarith [log_two_le_one]

theorem log_nat_add_le_log_mul (T C : ℕ) (hT : 0 < T) :
    Real.log (T + C : ℕ) ≤ Real.log (T : ℝ) + Real.log (C + 1 : ℕ) := by
  have hle : T + C ≤ T * (C + 1) := by nlinarith
  have h := Real.log_le_log
    (by exact_mod_cast (show 0 < T + C by omega) : (0 : ℝ) < (T + C : ℕ))
    (by exact_mod_cast hle : ((T + C : ℕ) : ℝ) ≤ (T : ℝ) * (C + 1 : ℕ))
  rwa [Real.log_mul (by positivity) (by positivity)] at h

theorem six_primeCutoff_add_five_le_excluded {m : ℕ} (hm : 0 < m) :
    6 * dilationPrimeCutoff m + 5 ≤ excludedPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  have hP := dilationPrimeCutoff_pos m
  have hpow : 11 ≤ patternSize m ^ 12 := by
    have h : patternSize m ≤ patternSize m ^ 12 := by
      simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 12 by omega)
    omega
  apply le_trans _ (polynomial_primeCutoff_le_excluded hm)
  nlinarith

theorem log_constructionUpperBound_le {m : ℕ} (hm : 0 < m) :
    Real.log (constructionUpperBound m : ℝ) ≤
      Real.log (progressionLength m : ℝ) + 2 * excludedPrimeCutoff m := by
  have hQ := constructionModulus_pos m
  have hA := constructionMaxDilation_pos m
  have hT := progressionLength_pos m
  have hlen : 6 * m + retainedLength m ≤ dilationPrimeCutoff m :=
    (total_retainedLength_le_size_pow_five hm).trans (patternSize_pow_five_le_primeCutoff hm)
  have hlogQ := log_nat_add_one_le _ hQ
  have hlogA := log_nat_add_one_le _ hA
  have hlogsum := log_nat_add_le_log_mul (progressionLength m)
    (6 * m + retainedLength m + 3) hT
  have hlogC := Real.log_le_sub_one_of_pos
    (by positivity : (0 : ℝ) < ((6 * m + retainedLength m + 3 + 1 : ℕ) : ℝ))
  have hsum : 6 * m + retainedLength m + progressionLength m + 3 =
      progressionLength m + (6 * m + retainedLength m + 3) := by omega
  unfold constructionUpperBound
  rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), hsum]
  have hsize : (6 : ℝ) * dilationPrimeCutoff m + 5 ≤ excludedPrimeCutoff m := by
    exact_mod_cast six_primeCutoff_add_five_le_excluded hm
  have hlenR : ((6 * m + retainedLength m : ℕ) : ℝ) ≤ dilationPrimeCutoff m := by
    exact_mod_cast hlen
  push_cast at hlogC hlogsum hlogQ hlogA hlenR ⊢
  linarith [log_constructionModulus_le_excluded hm, log_constructionMaxDilation_le m]

end Erdos69.Elementary

end SourceModule43

/- Source module 44: ErdosProblems.Erdos69.CharacteristicLimits -/
section SourceModule44
/- # Vanishing of the concrete small-prime characteristic function -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem tendsto_modelCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖modelCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := (tendsto_coefficientMassBound q).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _
    (tendsto_independent_decay hq)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hε, eventually_goodPrime_mass_ge_quarter hC]
    with m hm he hmass
  have hi : |firstCoefficient q m| ≤ 1 / 2 := (firstCoefficient_abs_le_mass q m).trans he.le
  have h := constructionModel_fourier_le (by omega : 0 < m) q hi
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4 * firstCoefficient q m ^ 2)
  nlinarith

theorem tendsto_smallCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖smallCharacteristic q m‖) atTop (𝓝 0) := by
  have h := (tendsto_modelCharacteristic_norm hq).add (tendsto_small_sub_model_norm q)
  simp only [add_zero] at h
  apply squeeze_zero (fun m ↦ norm_nonneg _) _ h
  intro m
  have ht := norm_le_norm_add_norm_sub (modelCharacteristic q m) (smallCharacteristic q m)
  simpa only [norm_sub_rev (modelCharacteristic q m)] using ht

end Erdos69.Elementary

end SourceModule44

/- Source module 45: ErdosProblems.Erdos69.LargePrimeErrorBounds -/
section SourceModule45
/- # Removing the large-prime contribution in the concrete construction -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem smallPrimeCutoff_le_intermediate (m : ℕ) :
    smallPrimeCutoff m ≤ intermediatePrimeCutoff m := by
  have hB := fluctuationScale_pos m
  simpa only [intermediatePrimeCutoff, pow_one] using Nat.pow_le_pow_right (smallPrimeCutoff_pos m)
    (show 1 ≤ 20 * fluctuationScale m by omega)

theorem intermediatePrimeCutoff_ge_two (m : ℕ) : 2 ≤ intermediatePrimeCutoff m :=
  (smallPrimeCutoff_ge_two m).trans (smallPrimeCutoff_le_intermediate m)

theorem primeWindow_card_le (y R : ℕ) : (primeWindow y R).card ≤ R := by
  have hsubset : primeWindow y R ⊆ Finset.Icc 1 R := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsubset

theorem primeWindow_frequency_le_one (m : ℕ) :
    ((primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card : ℝ) /
      progressionLength m ≤ 1 := by
  have hR := intermediatePrimeCutoff_ge_two m
  have hcard := primeWindow_card_le (smallPrimeCutoff m) (intermediatePrimeCutoff m)
  have hle : (primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card ≤
      progressionLength m := by
    rw [← intermediatePrimeCutoff_square]
    nlinarith
  exact (div_le_one (by exact_mod_cast progressionLength_pos m : (0 : ℝ) < progressionLength m)).mpr
    (by exact_mod_cast hle)

theorem upper_log_ratio_le_three {m : ℕ} (hm : 0 < m) :
    Real.log (constructionUpperBound m : ℝ) / Real.log (intermediatePrimeCutoff m : ℝ) ≤ 3 := by
  have hpos : 0 < Real.log (intermediatePrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast intermediatePrimeCutoff_ge_two m)
  apply (div_le_iff₀ hpos).mpr
  have hX := log_constructionUpperBound_le hm
  have hE : (2 : ℝ) * excludedPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast twice_excluded_le_two_pow_scale hm
  have hB : (1 : ℝ) ≤ fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  have hpow : 0 ≤ (2 : ℝ) ^ fluctuationScale m := by positivity
  have hlower := mul_le_mul_of_nonneg_right half_le_log_two hpow
  have hmul := mul_le_mul_of_nonneg_right hB hpow
  rw [log_progressionLength] at hX
  rw [log_intermediatePrimeCutoff]
  nlinarith [mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ (20 : ℝ) * fluctuationScale m)]

theorem largePrime_parameter_error_le {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) :
    primeReciprocalSum (intermediatePrimeCutoff m) - primeReciprocalSum (smallPrimeCutoff m) +
      ((primeWindow (smallPrimeCutoff m) (intermediatePrimeCutoff m)).card : ℝ) /
        progressionLength m +
      Real.log (constructionUpperBound m : ℝ) / Real.log (intermediatePrimeCutoff m : ℝ) ≤
        Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4 := by
  have hR := primeReciprocalSum_upper hC _ (intermediatePrimeCutoff_ge_two m)
  have hy := primeReciprocalSum_lower hC _ (smallPrimeCutoff_ge_two m)
  have hlog := log_log_intermediate_sub_small m
  linarith [primeWindow_frequency_le_one m, upper_log_ratio_le_three hm]

noncomputable def constructionRetainedValue (q : ℝ) (m t : ℕ) : ℝ :=
  ∑ r : ConstructionShift m,
    constructionCoefficient m q r * omegaCount (constructionPoint m t + r.val)

noncomputable def retainedCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase (constructionRetainedValue q m t.val))

theorem construction_retained_compare_small {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) (q : ℝ) :
    ‖retainedCharacteristic q m‖ ≤ ‖smallCharacteristic q m‖ +
      2 * Real.pi * coefficientMassBound q m * (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4) := by
  have h := FiniteLaw.affine_omega_fourier_compare_small
    (progressionLength m) (constructionModulus m) (constructionBase m)
    (smallPrimeCutoff m) (intermediatePrimeCutoff m) (constructionUpperBound m)
    (progressionLength_pos m) (constructionModulus_pos m)
    (constructionModulus_le_smallPrimeCutoff hm)
    (smallPrimeCutoff_le_intermediate m) (by have h := intermediatePrimeCutoff_ge_two m; omega)
    (fun r : ConstructionShift m ↦ r.val) (constructionCoefficient m q)
    (fun t r ↦ by
      have hp := constructionPoint_pos m t.val
      change 0 < constructionPoint m t.val + r.val
      omega)
    (sampled_shift_le_upper m)
  have heq (t : Fin (progressionLength m)) :
      (∑ p ∈ freePrimes (constructionModulus m) (smallPrimeCutoff m),
        ∑ r : ConstructionShift m, constructionCoefficient m q r *
          (if p ∣ constructionBase m + constructionModulus m * t.val + r.val then (1 : ℝ) else 0)) =
        constructionSmallValue q m t.val := by
    exact (Finset.sum_coe_sort _ _).symm
  simp_rw [heq] at h
  apply h.trans
  apply add_le_add le_rfl
  have hnonneg : 0 ≤ Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4 := by positivity
  calc
    _ ≤ 2 * Real.pi * (∑ r : ConstructionShift m, |constructionCoefficient m q r|) *
        (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4) := by
      exact mul_le_mul_of_nonneg_left (largePrime_parameter_error_le hC hm) (by positivity)
    _ ≤ _ := by
      gcongr
      exact constructionCoefficient_mass_le m q

theorem tendsto_retainedCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖retainedCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := tendsto_coefficientMassBound_affine q (4 * Real.log 36) (Real.log 20 + 2 * C + 4)
  have he : Tendsto (fun m : ℕ ↦ 2 * Real.pi * coefficientMassBound q m *
      (Real.log 20 + 4 * m * Real.log 36 + 2 * C + 4)) atTop (𝓝 0) := by
    convert! hε.const_mul (2 * Real.pi) using 1
    · funext m
      ring
    · ring_nf
  have hlim := (tendsto_smallCharacteristic_norm hq).add he
  simp only [add_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact construction_retained_compare_small hC0 hC (by omega) q

end Erdos69.Elementary

end SourceModule45

/- Source module 46: ErdosProblems.Erdos69.PointwiseTail -/
section SourceModule46
/- # Pointwise logarithmic control of the omitted binary tail -/

open scoped BigOperators

namespace Erdos69.Elementary

theorem omega_affine_le_log_add (n a b h : ℕ) (ha : 0 < a) :
    (omegaCount (n + a * h - b) : ℝ) ≤ Real.log (n + a : ℕ) / Real.log 2 + h := by
  have hna : 0 < n + a := by omega
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog0 : 0 ≤ Real.log (n + a : ℕ) := Real.log_nonneg (by exact_mod_cast hna)
  by_cases hz : n + a * h - b = 0
  · rw [hz, omegaCount_zero, Nat.cast_zero]
    positivity
  have hpos : 0 < n + a * h - b := by omega
  have hpow : h + 1 ≤ 2 ^ h := Nat.lt_two_pow_self
  have hle : n + a * h - b ≤ (n + a) * 2 ^ h := by
    calc
      _ ≤ n + a * h := Nat.sub_le _ _
      _ ≤ (n + a) * (h + 1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hlog := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < ((n + a * h - b : ℕ) : ℝ))
    (by exact_mod_cast hle : ((n + a * h - b : ℕ) : ℝ) ≤ (n + a : ℕ) * (2 : ℝ) ^ h)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hw := omegaCount_mul_log_two_le hpos
  have hfinal : (omegaCount (n + a * h - b) : ℝ) * Real.log 2 ≤
      Real.log (n + a : ℕ) + h * Real.log 2 := hw.trans hlog
  calc
    _ ≤ (Real.log (n + a : ℕ) + h * Real.log 2) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hfinal
    _ = _ := by field_simp

theorem hasSum_index_binary_weights :
    HasSum (fun k : ℕ ↦ (k : ℝ) / 2 ^ (k + 1)) 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)).div_const 2
  convert! h using 1
  · funext k
    simp only [pow_succ, div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow]
    ring
  · norm_num

theorem hasSum_linear_binary_tail (C : ℝ) (L : ℕ) :
    HasSum (fun k : ℕ ↦ (C + L + 1 + k) / 2 ^ (L + 1 + k))
      ((C + L + 2) / 2 ^ L) := by
  have hc : HasSum (fun k : ℕ ↦ (C + L + 1) / 2 ^ (k + 1)) (C + L + 1) := by
    simpa only [tsum_constant_binary_weights] using
      (summable_constant_binary_weights (C + L + 1)).hasSum
  have h := (hc.add hasSum_index_binary_weights).mul_left ((1 : ℝ) / 2 ^ L)
  convert! h using 1
  · funext k
    rw [show L + 1 + k = L + (k + 1) by omega, pow_add]
    ring
  · ring

theorem summable_omega_affine_tail (n a b L : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ ↦ (omegaCount (n + a * (L + 1 + k) - b) : ℝ) /
      2 ^ (L + 1 + k)) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _
    (hasSum_linear_binary_tail (Real.log (n + a : ℕ) / Real.log 2) L).summable
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := omega_affine_le_log_add n a b (L + 1 + k) ha
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem omega_affine_tail_le (n a b L : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, (omegaCount (n + a * (L + 1 + k) - b) : ℝ) / 2 ^ (L + 1 + k)) ≤
      (Real.log (n + a : ℕ) / Real.log 2 + L + 2) / 2 ^ L := by
  rw [← (hasSum_linear_binary_tail (Real.log (n + a : ℕ) / Real.log 2) L).tsum_eq]
  apply Summable.tsum_le_tsum _ (summable_omega_affine_tail n a b L ha)
    (hasSum_linear_binary_tail _ _).summable
  intro k
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := omega_affine_le_log_add n a b (L + 1 + k) ha
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

end Erdos69.Elementary

end SourceModule46

/- Source module 47: ErdosProblems.Erdos69.TailTruncation -/
section SourceModule47
/- # Exact truncation of the signed arithmetic tails -/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def arithmeticTailTerm (m P n k : ℕ) : ℝ :=
  ∑ i : PatternLabel m, (patternSign m i : ℝ) *
    (omegaCount (n + patternDilation m P i * (k + 1) - patternOffset m P i) : ℝ) /
      2 ^ (k + 1)

noncomputable def arithmeticTail (m P n : ℕ) : ℝ := ∑' k, arithmeticTailTerm m P n k

theorem summable_arithmeticTailTerm (m P n : ℕ) : Summable (arithmeticTailTerm m P n) := by
  apply summable_sum
  intro i hi
  have h := (summable_omega_affine_tail n (patternDilation m P i) (patternOffset m P i) 0
    (patternDilation_pos m P i)).mul_left (patternSign m i : ℝ)
  simpa only [Nat.zero_add, Nat.add_comm 1, mul_div_assoc] using h

theorem arithmeticTailTerm_initial_zero (m P n k : ℕ) (hk : k < 6 * m) :
    arithmeticTailTerm m P n k = 0 := by
  unfold arithmeticTailTerm
  rw [← Finset.sum_div, initial_arithmetic_cancellation m P n (k + 1)
    (by omega) (by omega) (fun a ↦ (omegaCount a : ℝ)), zero_div]

theorem signed_dilatedTail_eq_arithmeticTail (m P n : ℕ)
    (hn : ∀ i, n ≡ patternOffset m P i [MOD patternDilation m P i])
    (hb : ∀ i, patternOffset m P i ≤ n) :
    (∑ i : PatternLabel m, (patternSign m i : ℝ) *
      dilatedPositiveTail (patternDilation m P i)
        ((n - patternOffset m P i) / patternDilation m P i)) = arithmeticTail m P n := by
  have heq (i : PatternLabel m) :
      (patternSign m i : ℝ) * dilatedPositiveTail (patternDilation m P i)
        ((n - patternOffset m P i) / patternDilation m P i) =
      ∑' k : ℕ, (patternSign m i : ℝ) *
        (omegaCount (n + patternDilation m P i * (k + 1) - patternOffset m P i) : ℝ) /
          2 ^ (k + 1) := by
    rw [dilatedPositiveTail, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [dilation_quotient_shift (patternDilation_pos m P i) (hb i) (hn i)]
    ring
  simp_rw [heq]
  unfold arithmeticTail arithmeticTailTerm
  apply (Summable.tsum_finsetSum _).symm
  intro i hi
  have h := (summable_omega_affine_tail n (patternDilation m P i) (patternOffset m P i) 0
    (patternDilation_pos m P i)).mul_left (patternSign m i : ℝ)
  simpa only [Nat.zero_add, Nat.add_comm 1, mul_div_assoc] using h

theorem arithmeticTail_split (m P n H : ℕ) :
    arithmeticTail m P n =
      (∑ k ∈ Finset.range H, arithmeticTailTerm m P n (6 * m + k)) +
        ∑' k, arithmeticTailTerm m P n (k + (6 * m + H)) := by
  have h := (summable_arithmeticTailTerm m P n).sum_add_tsum_nat_add (6 * m + H)
  rw [Finset.sum_range_add] at h
  have hzero : (∑ k ∈ Finset.range (6 * m), arithmeticTailTerm m P n k) = 0 := by
    exact Finset.sum_eq_zero (fun k hk ↦ arithmeticTailTerm_initial_zero m P n k
      (Finset.mem_range.mp hk))
  rw [hzero, zero_add] at h
  exact h.symm

theorem retained_sum_eq_prefix (m P n H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * omegaCount (n + r)) =
      q * ∑ k ∈ Finset.range H, arithmeticTailTerm m P n (6 * m + k) := by
  rw [sum_grouped_shift_test, Fintype.sum_prod_type, Finset.sum_comm,
    ← Fin.sum_univ_eq_sum_range (fun k ↦ arithmeticTailTerm m P n (6 * m + k)) H,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold arithmeticTailTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : patternOffset m P i ≤ patternDilation m P i * (6 * m + 1 + k.val) := by
    unfold patternOffset patternDilation roughDilation
    have hh := patternIntercept_le_digit_mul (by omega : 6 * m ≤ 6 * m + 1 + k.val) i
    nlinarith
  have heq : n + termShift m P H (i, k) =
      n + patternDilation m P i * (6 * m + k.val + 1) - patternOffset m P i := by
    unfold termShift patternShift
    rw [show 6 * m + 1 + k.val = 6 * m + k.val + 1 by omega] at hle ⊢
    dsimp only
    omega
  simp only [termCoefficient, heq]
  rw [show 6 * m + 1 + k.val = 6 * m + k.val + 1 by omega]
  ring

theorem arithmetic_remainder_abs_le (m P n L : ℕ) :
    |∑' k, arithmeticTailTerm m P n (k + L)| ≤
      ∑ i : PatternLabel m,
        (Real.log (n + patternDilation m P i : ℕ) / Real.log 2 + L + 2) / 2 ^ L := by
  let g : PatternLabel m → ℕ → ℝ := fun i k ↦
    (omegaCount (n + patternDilation m P i * (L + 1 + k) - patternOffset m P i) : ℝ) /
      2 ^ (L + 1 + k)
  have hg (i : PatternLabel m) : Summable (g i) :=
    summable_omega_affine_tail n _ _ L (patternDilation_pos m P i)
  have hgn (i : PatternLabel m) (k : ℕ) : 0 ≤ g i k := by dsimp [g]; positivity
  have hpoint (k : ℕ) : arithmeticTailTerm m P n (k + L) =
      ∑ i : PatternLabel m, (patternSign m i : ℝ) * g i k := by
    unfold arithmeticTailTerm
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [g]
    rw [show k + L + 1 = L + 1 + k by omega]
    ring
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun i _ ↦ (hg i).mul_left (patternSign m i : ℝ))]
  simp_rw [Summable.tsum_mul_left _ (hg _)]
  calc
    _ ≤ ∑ i : PatternLabel m, |(patternSign m i : ℝ) * ∑' k, g i k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : PatternLabel m, ∑' k, g i k := by
      simp [abs_mul, patternSign_abs_real, abs_of_nonneg (tsum_nonneg (hgn _))]
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ omega_affine_tail_le n _ _ L
      (patternDilation_pos m P i))

theorem arithmeticTail_truncation_error (m P n H : ℕ) (q : ℝ) :
    |q * arithmeticTail m P n -
      ∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * omegaCount (n + r)| ≤
      |q| * ∑ i : PatternLabel m,
        (Real.log (n + patternDilation m P i : ℕ) / Real.log 2 + (6 * m + H) + 2) /
          2 ^ (6 * m + H) := by
  rw [retained_sum_eq_prefix, arithmeticTail_split m P n H, mul_add, add_sub_cancel_left,
    abs_mul]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_left (arithmetic_remainder_abs_le m P n (6 * m + H)) (abs_nonneg q)

end Erdos69.Elementary

end SourceModule47

/- Source module 48: ErdosProblems.Erdos69.TruncationErrorBounds -/
section SourceModule48
/- # Vanishing truncation error for the full signed tails -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

noncomputable def fullCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase
    (q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val)))

theorem construction_tail_point_error (q : ℝ) (m : ℕ) (t : Fin (progressionLength m)) :
    |q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) -
      constructionRetainedValue q m t.val| ≤
      coefficientMassBound q m *
        (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
          2 ^ retainedLength m := by
  have h := arithmeticTail_truncation_error m (dilationPrimeCutoff m) (constructionPoint m t.val)
    (retainedLength m) q
  have hsum : constructionRetainedValue q m t.val =
      ∑ r ∈ retainedShifts m (dilationPrimeCutoff m) (retainedLength m),
        shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r *
          omegaCount (constructionPoint m t.val + r) := by
    exact Finset.sum_coe_sort (retainedShifts m (dilationPrimeCutoff m) (retainedLength m))
      (fun r ↦ shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r *
        omegaCount (constructionPoint m t.val + r))
  rw [hsum]
  apply h.trans
  have hlog (i : PatternLabel m) :
      Real.log (constructionPoint m t.val + constructionDilation m i : ℕ) ≤
      Real.log (constructionUpperBound m : ℝ) := by
    apply Real.log_le_log (by have hp := constructionPoint_pos m t.val; positivity)
    exact_mod_cast sampled_dilation_le_upper m t i
  calc
    _ ≤ |q| * ∑ _i : PatternLabel m,
        (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
          2 ^ (6 * m + retainedLength m) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hd : Real.log (constructionPoint m t.val +
          patternDilation m (dilationPrimeCutoff m) i : ℕ) / Real.log 2 ≤
          Real.log (constructionUpperBound m : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right (hlog i) (Real.log_pos (by norm_num)).le
      linarith only [hd]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_patternLabel, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, pow_add]
      rw [show |q| * ((36 : ℝ) ^ m *
          ((Real.log (constructionUpperBound m : ℝ) / Real.log 2 +
            (6 * m + retainedLength m) + 2) / (2 ^ (6 * m) * 2 ^ retainedLength m))) =
          (|q| * ((36 : ℝ) ^ m / 2 ^ (6 * m))) *
            (Real.log (constructionUpperBound m : ℝ) / Real.log 2 +
              (6 * m + retainedLength m) + 2) / 2 ^ retainedLength m by ring]
      rw [pattern_mass_ratio]
      rfl

noncomputable def truncationError (m : ℕ) : ℝ :=
  (46 + 2 / Real.log 2) * ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m

theorem tendsto_truncationError : Tendsto truncationError atTop (𝓝 0) := by
  change Tendsto (fun m ↦ (46 + 2 / Real.log 2) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using tendsto_scale_tail.const_mul (46 + 2 / Real.log 2)

theorem construction_tail_factor_le {m : ℕ} (hm : 0 < m) :
    (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
      2 ^ retainedLength m ≤ truncationError m := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hX := log_constructionUpperBound_le hm
  rw [log_progressionLength] at hX
  have hE : (excludedPrimeCutoff m : ℝ) ≤ (2 : ℝ) ^ fluctuationScale m := by
    have h := twice_excluded_le_two_pow_scale hm
    exact_mod_cast (show excludedPrimeCutoff m ≤ 2 ^ fluctuationScale m by omega)
  have hK : (6 * m : ℕ) ≤ fluctuationScale m := by
    apply (initialLength_le_patternSize m).trans
    change patternSize m ≤ patternSize m ^ 4
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)
  have hKR : (6 : ℝ) * m ≤ fluctuationScale m := by exact_mod_cast hK
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ fluctuationScale m := one_le_pow₀ (by norm_num)
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ fluctuationScale m := by positivity
  have hB : (0 : ℝ) ≤ fluctuationScale m := by positivity
  have hX' : Real.log (constructionUpperBound m : ℝ) / Real.log 2 ≤
      (40 * fluctuationScale m + 2 / Real.log 2) * (2 : ℝ) ^ fluctuationScale m := by
    apply (div_le_iff₀ hlog2).mpr
    have he := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  unfold truncationError retainedLength
  push_cast
  rw [pow_mul, pow_right_comm (2 : ℝ) 2 (fluctuationScale m)]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpowpos) hpowpos).mpr
  have hmul := mul_le_mul_of_nonneg_right hX' hpowpos.le
  have hrest := mul_le_mul_of_nonneg_right hpow
    (by positivity : (0 : ℝ) ≤ 3 * fluctuationScale m + 2)
  have hconst : 0 ≤ 2 / Real.log 2 := by positivity
  nlinarith [mul_nonneg hconst hB]

theorem tendsto_full_sub_retained_norm (q : ℝ) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m - retainedCharacteristic q m‖) atTop (𝓝 0) := by
  have hlim := tendsto_truncationError.const_mul (2 * Real.pi)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_coefficientMassBound q).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with m hm hε
  have hpoint (t : Fin (progressionLength m)) :
      |q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) -
        constructionRetainedValue q m t.val| ≤ truncationError m := by
    apply (construction_tail_point_error q m t).trans
    rw [mul_div_assoc]
    calc
      _ ≤ coefficientMassBound q m * truncationError m :=
        mul_le_mul_of_nonneg_left (construction_tail_factor_le (by omega)) (by
          unfold coefficientMassBound; positivity)
      _ ≤ truncationError m := by
        have hn : 0 ≤ truncationError m := by unfold truncationError; positivity
        nlinarith
  have h := FiniteLaw.norm_mean_fourierPhase_sub_le (constructionLaw m)
    (fun t ↦ q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val))
    (fun t ↦ constructionRetainedValue q m t.val)
  apply h.trans
  have hmean := (constructionLaw m).mean_mono hpoint
  rw [FiniteLaw.mean_const] at hmean
  exact mul_le_mul_of_nonneg_left hmean (by positivity)

theorem tendsto_fullCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m‖) atTop (𝓝 0) := by
  have h := (tendsto_retainedCharacteristic_norm hq).add (tendsto_full_sub_retained_norm q)
  simp only [add_zero] at h
  apply squeeze_zero (fun m ↦ norm_nonneg _) _ h
  intro m
  have ht := norm_le_norm_add_norm_sub (retainedCharacteristic q m) (fullCharacteristic q m)
  simpa only [norm_sub_rev (retainedCharacteristic q m)] using ht

end Erdos69.Elementary

end SourceModule48

/- Source module 49: ErdosProblems.Erdos69.CorrectionErrorBounds -/
section SourceModule49
/- # Rationality forces the full characteristic function to approach one -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem dilationPrimeCutoff_ge_two (m : ℕ) : 2 ≤ dilationPrimeCutoff m := by
  unfold dilationPrimeCutoff
  exact Nat.one_lt_two_pow (Nat.pow_pos (patternSize_pos m)).ne'

theorem constructionDilation_log_le (m : ℕ) (i : PatternLabel m) :
    Real.log (constructionDilation m i : ℝ) ≤ 5 * dilationPrimeCutoff m := by
  apply le_trans _ (log_constructionMaxDilation_le m)
  exact Real.log_le_log (by exact_mod_cast constructionDilation_pos m i)
    (by exact_mod_cast constructionDilation_le_max m i)

theorem constructionDilation_omega_le (m : ℕ) (i : PatternLabel m) :
    (omegaCount (constructionDilation m i) : ℝ) ≤ 5 * dilationPrimeCutoff m / Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact (omegaCount_mul_log_two_le (constructionDilation_pos m i)).trans
    (constructionDilation_log_le m i)

theorem constructionDilation_reciprocal_le (m : ℕ) (i : PatternLabel m) :
    (∑ p ∈ (constructionDilation m i).primeFactors, (1 : ℝ) / p) ≤
      5 / Real.log (dilationPrimeCutoff m : ℝ) :=
  roughDilation_reciprocal_mass_le (dilationPrimeCutoff_ge_two m)
    ((patternDigit_lt m i).le.trans (digitRange_le_dilationPrimeCutoff m))

theorem construction_correction_mean_le (m : ℕ) (i : PatternLabel m) :
    (constructionLaw m).mean (fun t ↦ compositeCorrection (constructionDilation m i)
      ((constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)) ≤
        5 / Real.log (dilationPrimeCutoff m : ℝ) +
          5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m) := by
  simp_rw [construction_quotient_affine]
  have h := FiniteLaw.uniform_compositeCorrection_le
    (progressionLength m) (constructionDilation m i)
    (constructionModulus m / constructionDilation m i)
    ((constructionBase m - constructionOffset m i) / constructionDilation m i)
    (progressionLength_pos m) (fun p hp ↦
      (construction_quotient_coprime m i).of_dvd_right (Nat.mem_primeFactors.mp hp).2.1)
  apply h.trans
  have hw := div_le_div_of_nonneg_right (constructionDilation_omega_le m i)
    (by positivity : (0 : ℝ) ≤ progressionLength m)
  have hr := constructionDilation_reciprocal_le m i
  calc
    _ ≤ 5 / Real.log (dilationPrimeCutoff m : ℝ) +
        (5 * dilationPrimeCutoff m / Real.log 2) / progressionLength m := add_le_add hr hw
    _ = _ := by ring

theorem rational_fullCharacteristic_bound {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (m : ℕ) :
    ‖fullCharacteristic q m - 1‖ ≤ 2 * Real.pi * q * patternSize m *
      (5 / Real.log (dilationPrimeCutoff m : ℝ) +
        5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) := by
  have hphase := FiniteLaw.rational_signed_tail_phase_le h (constructionLaw m)
    (constructionDilation m) (fun i ↦ (constructionDilation_pos m i).ne')
    (patternSign m) (patternSign_abs_real m)
    (fun t i ↦ (constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)
  have heq (t : Fin (progressionLength m)) :
      (∑ i : PatternLabel m, (patternSign m i : ℝ) * dilatedPositiveTail (constructionDilation m i)
        ((constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)) =
        arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) :=
    signed_dilatedTail_eq_arithmeticTail m _ _ (constructionPoint_modEq m t.val)
      (constructionOffset_le_point m t.val)
  simp_rw [heq] at hphase
  apply hphase.trans
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (PatternLabel m))) ↦
    construction_correction_mean_le m i)
  simp only [Finset.sum_const, Finset.card_univ, card_patternLabel, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * Real.pi * (q : ℝ))
  simpa only [patternSize, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hmul

theorem size_primeCutoff_ratio_le {m : ℕ} (hm : 0 < m) :
    (patternSize m : ℝ) * dilationPrimeCutoff m / progressionLength m ≤
      (1 : ℝ) / 2 ^ fluctuationScale m := by
  have hNpow : patternSize m ≤ patternSize m ^ 12 := by
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 12 by omega)
  have hNP : patternSize m * dilationPrimeCutoff m ≤ 2 ^ fluctuationScale m := by
    apply (Nat.mul_le_mul_right _ hNpow).trans
    apply (polynomial_primeCutoff_le_excluded hm).trans
    have h := twice_excluded_le_two_pow_scale hm
    omega
  have hT : 2 ^ (2 * fluctuationScale m) ≤ progressionLength m := by
    calc
      _ ≤ 2 ^ (40 * fluctuationScale m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.pow_le_pow_left (smallPrimeCutoff_ge_two m) _
  have hNPR : (patternSize m : ℝ) * dilationPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast hNP
  have hTR : ((2 : ℝ) ^ fluctuationScale m) ^ 2 ≤ progressionLength m := by
    have h := hT
    rw [Nat.mul_comm 2, pow_mul] at h
    exact_mod_cast h
  apply (div_le_div_iff₀ (by exact_mod_cast progressionLength_pos m : (0 : ℝ) < progressionLength m)
    (by positivity : (0 : ℝ) < 2 ^ fluctuationScale m)).mpr
  have hmul := mul_le_mul_of_nonneg_right hNPR (by positivity : (0 : ℝ) ≤ 2 ^ fluctuationScale m)
  nlinarith

noncomputable def correctionError (q : ℝ) (m : ℕ) : ℝ :=
  (5 * |q| / Real.log 2) * ((1 : ℝ) / patternSize m + 1 / 2 ^ fluctuationScale m)

theorem tendsto_correctionError (q : ℝ) : Tendsto (correctionError q) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp tendsto_fluctuationScale
  have hp' : Tendsto (fun m ↦ (1 : ℝ) / 2 ^ fluctuationScale m) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, Function.comp_def] using hp
  change Tendsto (fun m ↦ (5 * |q| / Real.log 2) *
    ((1 : ℝ) / patternSize m + 1 / 2 ^ fluctuationScale m)) atTop (𝓝 0)
  simpa only [add_zero, mul_zero] using
    (tendsto_inverse_patternSize.add hp').const_mul (5 * |q| / Real.log 2)

theorem construction_correction_error_le {m : ℕ} (hm : 0 < m) (q : ℝ) (hq : 0 ≤ q) :
    q * patternSize m * (5 / Real.log (dilationPrimeCutoff m : ℝ) +
      5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) ≤ correctionError q m := by
  have hN : (0 : ℝ) < patternSize m := by exact_mod_cast patternSize_pos m
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [log_dilationPrimeCutoff]
  have heq : q * patternSize m * (5 / ((patternSize m : ℝ) ^ 2 * Real.log 2) +
      5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) =
      (5 * q / Real.log 2) * ((1 : ℝ) / patternSize m +
        (patternSize m : ℝ) * dilationPrimeCutoff m / progressionLength m) := by
    field_simp
  rw [heq, correctionError, abs_of_nonneg hq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (size_primeCutoff_ratio_le hm)

theorem tendsto_full_sub_one_norm_of_rational {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m - 1‖) atTop (𝓝 0) := by
  have hlim := (tendsto_correctionError (q : ℝ)).const_mul (2 * Real.pi)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  apply (rational_fullCharacteristic_bound h m).trans
  have hb := mul_le_mul_of_nonneg_left (construction_correction_error_le (m := m) (by omega) (q : ℝ)
    (by positivity)) (by positivity : 0 ≤ 2 * Real.pi)
  simpa only [mul_assoc] using hb

end Erdos69.Elementary

end SourceModule49

/- Source module 50: ErdosProblems.Erdos69 -/
section SourceModule50
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-
# Erdős Problem 69: elementary six-term cancellation proof

The development uses six-term cancellation and pairwise coprime composite
dilations, followed by elementary prime estimates and finite CRT moments.

The six-term pattern cancels the initial tail terms. Composite dilations
replace prime-tuple inputs, with an explicit correction whose mean tends
to zero. Finite CRT moment comparison then forces the characteristic
function of the remaining signed tail to tend to zero. Rationality would
force the same characteristic function to tend to one.

The earlier analytic modules `HalaszMean`, `MinorArc`, and `RoughSelberg`
remain available as separate imports; they are not used by this proof.
-/

namespace Erdos69.Elementary

/-- Irrationality of the binary Lambert series of the number of distinct
prime factors. The terms at zero and one vanish. -/
theorem irrational_binaryOmegaSum : Irrational binaryOmegaSum := by
  by_contra h
  obtain ⟨q, hq, z, hz⟩ := exists_integer_multiple_of_not_irrational h
  have hzero := tendsto_fullCharacteristic_norm (q := (q : ℝ)) (by exact_mod_cast hq)
  have hone := tendsto_full_sub_one_norm_of_rational hz
  have hlim := hzero.add hone
  simp only [add_zero] at hlim
  have hbound (m : ℕ) : (1 : ℝ) ≤ ‖fullCharacteristic q m‖ + ‖fullCharacteristic q m - 1‖ := by
    simpa only [norm_one] using norm_le_norm_add_norm_sub (fullCharacteristic q m) (1 : ℂ)
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim hbound
  norm_num at hfalse

end Erdos69.Elementary

namespace Erdos69

/-- Erdős problem 69, with the exact series starting at `n = 2`. -/
theorem irrational_omega_series :
    Irrational (∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2)) := by
  rw [← Elementary.binaryOmegaSum_eq_tsum_from_two]
  exact Elementary.irrational_binaryOmegaSum

/-- The binary series counting distinct prime factors is irrational. -/
theorem source_erdos_69 :
    Irrational (∑' n : ℕ,
      (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2)) :=
  irrational_omega_series

end Erdos69

end SourceModule50

theorem OMA.solution : type_of% @Erdos69.erdos_69 := by
  exact Erdos69.irrational_omega_series
