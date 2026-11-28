import OMAStatements.S_itp_courtade_kumar

namespace OMA.R_itp_courtade_kumar_R1

open OMA.S_itp_courtade_kumar
open scoped BigOperators

-- The upper bound in the entropy-difference presentation of Chen et al.
-- Published proof: https://arxiv.org/abs/2609.24931
-- Lean formalization: https://github.com/dpwoodru/general-courtade-kumar-lean
def H1 : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 < p → p < (1 : ℝ) / 2 → ∀ f : Cube n → Bool,
    ((∑ b : Bool, Real.negMulLog (functionMarginal p f b)) +
      (∑ y : Cube n, Real.negMulLog (observationMarginal p f y)) -
      (∑ z : Bool × Cube n, Real.negMulLog (jointProbability p f z.1 z.2))) / ell ≤
      1 - binaryEntropy p

-- The finite-sum bridge from the catalog's log-ratio formula.
def H2 : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 < p → p < (1 : ℝ) / 2 → ∀ f : Cube n → Bool,
    mutualInformation p f =
      ((∑ b : Bool, Real.negMulLog (functionMarginal p f b)) +
        (∑ y : Cube n, Real.negMulLog (observationMarginal p f y)) -
        (∑ z : Bool × Cube n, Real.negMulLog (jointProbability p f z.1 z.2))) / ell

lemma cubeCard (n : ℕ) : (Fintype.card (Cube n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Cube]

lemma sumCoordinate {n : ℕ} (i : Fin n) (g : Bool → ℝ) :
    (∑ x : Cube n, g (x i)) = (2 : ℝ) ^ n * (g false + g true) / 2 := by
  let flip : Cube n ≃ Cube n :=
    { toFun := fun x j => !(x j)
      invFun := fun x j => !(x j)
      left_inv := by
        intro x
        funext j
        simp
      right_inv := by
        intro x
        funext j
        simp }
  have hflip : (∑ x : Cube n, g (!(x i))) = ∑ x : Cube n, g (x i) :=
    Equiv.sum_comp flip (fun x => g (x i))
  have hsum :
      (∑ x : Cube n, g (x i)) + (∑ x : Cube n, g (!(x i))) =
        (2 : ℝ) ^ n * (g false + g true) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : Cube n, (g false + g true) := by
        apply Finset.sum_congr rfl
        intro x _
        cases x i <;> simp [add_comm]
      _ = _ := by simp [nsmul_eq_mul, mul_add]
  rw [hflip] at hsum
  linarith

lemma dictatorJoint {n : ℕ} (p : ℝ) (i : Fin n) (b : Bool) (y : Cube n) :
    jointProbability p (fun x => x i) b y =
      (if b = y i then 1 - p else p) / (2 : ℝ) ^ n := by
  classical
  let w : Fin n → Bool → ℝ := fun j v => if v = y j then 1 - p else p
  let k : Fin n → Bool → ℝ := fun j v => if j = i ∧ v ≠ b then 0 else w j v
  have hprod (x : Cube n) :
      (if x i = b then bitFlipKernel p x y else 0) = ∏ j, k j (x j) := by
    by_cases hx : x i = b
    · rw [if_pos hx, bitFlipKernel]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [k, w, hx]
      · simp [k, w, hj]
    · rw [if_neg hx, Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [k, hx]
  have hi : (∑ v : Bool, k i v) = w i b := by
    cases b <;> simp [k]
  have hj (j : Fin n) (hne : j ≠ i) : (∑ v : Bool, k j v) = 1 := by
    cases hy : y j <;> simp [k, w, hne, hy]
  unfold jointProbability cubeAverage
  simp_rw [hprod]
  rw [← Fintype.prod_sum k, Fintype.prod_eq_single i hj, hi]

lemma dictatorMarginal {n : ℕ} (p : ℝ) (i : Fin n) (b : Bool) :
    functionMarginal p (fun x => x i) b = 1 / 2 := by
  unfold functionMarginal
  simp_rw [dictatorJoint, ← Finset.sum_div]
  rw [sumCoordinate i (fun v => if b = v then 1 - p else p)]
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  cases b <;> simp <;> field_simp [hn]

lemma dictatorObservation {n : ℕ} (p : ℝ) (i : Fin n) (y : Cube n) :
    observationMarginal p (fun x => x i) y = 1 / (2 : ℝ) ^ n := by
  unfold observationMarginal
  simp_rw [dictatorJoint, ← Finset.sum_div]
  cases y i <;> simp [add_comm]

lemma dictatorAttains {n : ℕ} (p : ℝ) (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (i : Fin n) : mutualInformation p (fun x => x i) = 1 - binaryEntropy p := by
  have hq : 0 < 1 - p := by linarith
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hell : ell ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hterm (w : ℝ) (hw : 0 < w) :
      (if 0 < w / (2 : ℝ) ^ n then
        w / (2 : ℝ) ^ n * Real.log ((w / (2 : ℝ) ^ n) / ((1 / 2) * (1 / (2 : ℝ) ^ n)))
       else 0) =
        w * Real.log (2 * w) / (2 : ℝ) ^ n := by
    rw [if_pos (div_pos hw hN)]
    have hratio : (w / (2 : ℝ) ^ n) / ((1 / 2) * (1 / (2 : ℝ) ^ n)) = 2 * w := by
      field_simp [hN.ne'] <;> ring
    rw [hratio]
    ring
  unfold mutualInformation
  simp_rw [dictatorJoint, dictatorMarginal, dictatorObservation]
  rw [Finset.sum_comm]
  have hsum (y : Cube n) :
      (∑ b : Bool, if 0 < (if b = y i then 1 - p else p) / (2 : ℝ) ^ n then
        (if b = y i then 1 - p else p) / (2 : ℝ) ^ n *
          Real.log (((if b = y i then 1 - p else p) / (2 : ℝ) ^ n) /
            ((1 / 2) * (1 / (2 : ℝ) ^ n))) else 0) =
      (p * Real.log (2 * p) + (1 - p) * Real.log (2 * (1 - p))) / (2 : ℝ) ^ n := by
    rw [Fintype.sum_bool]
    cases y i <;>
      simp only [Bool.true_eq_false, Bool.false_eq_true, if_false, if_true] <;>
      rw [hterm p hp, hterm (1 - p) hq] <;> ring
  simp_rw [hsum]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, cubeCard]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq.ne']
  unfold binaryEntropy xlogx
  change ((2 : ℝ) ^ n *
      ((p * (ell + Real.log p) + (1 - p) * (ell + Real.log (1 - p))) /
        (2 : ℝ) ^ n)) / ell =
    1 - (-(p * Real.log p + (1 - p) * Real.log (1 - p))) / ell
  field_simp [hN.ne', hell] <;> ring

theorem main : H1 → H2 → type_of% @OMA.S_itp_courtade_kumar.main := by
  intro entropyBound modelBridge n p hp hp'
  refine ⟨?_, dictatorAttains p hp hp'⟩
  intro f
  rw [modelBridge n p hp hp' f]
  exact entropyBound n p hp hp' f

end OMA.R_itp_courtade_kumar_R1
