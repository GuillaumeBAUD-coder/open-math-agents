import FormalConjectures.ErdosProblems.«1204»
import Mathlib.NumberTheory.SelbergSieve

/-!
# The least diameter of an admissible tuple

Translate an admissible tuple by the Chinese remainder theorem so that its image
misses the multiples of every prime up to the sieve level. For a tuple of size
`k`, take level `k^(1-δ)`. The interval Selberg sieve then bounds the size by
`2 * diameter / ((1-δ) * log k) + o(k)`.

The interval sieve estimates below are adapted from Arend Mellendijk's
formalization in PrimeNumberTheoremAnd, commit 55270df80721 (Apache 2.0).
The sources are the files AuxResults, Basic, Selberg and SelbergBounds under
Mathlib/NumberTheory/Sieve, and BrunTitchmarsh. Where available, the lemmas from
Mathlib.NumberTheory.SelbergSieve are used directly.
-/

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ 
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP

end Aux
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)

abbrev selbergTerms := BoundingSieve.selbergTerms (s := s)

theorem selbergTerms_apply (d : ℕ) :
    (SelbergSieve.selbergTerms s) d = s.nu d * ∏ p ∈ d.primeFactors, 1/(1 - s.nu p) := by
  simpa only [selbergTerms, one_div] using BoundingSieve.selbergTerms_apply (s := s) d
section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < (SelbergSieve.selbergTerms s) l := by
  exact BoundingSieve.selbergTerms_pos hl
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  exact BoundingSieve.selbergTerms_isMultiplicative
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by
  exact BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ s.totalMass * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
  by simpa only [selbergTerms, one_div] using BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := s) w
end LambdaSquared

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
section
noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0

theorem selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  
  apply symm
  rw [sum_mul_subst d s.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * (s.nu d) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared (SelbergSieve.selbergWeights s)

theorem weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨(SelbergSieve.selbergMuPlus s), BoundingSieve.upperMoebius_lambdaSquared (SelbergSieve.selbergWeights s) (s.weight_one_of_selberg)⟩

theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms (s.toBoundingSieve)) l *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private theorem _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ s.level ↔
    (k * m) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k s.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |(SelbergSieve.selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| (SelbergSieve.selbergWeights s) d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := s.toBoundingSieve)) d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| (BoundingSieve.rem (s := s.toBoundingSieve)) d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      s.totalMass / (SelbergSieve.selbergBoundingSum s) +
        ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |(BoundingSieve.rem (s := s.toBoundingSieve)) d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ s.totalMass * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
section
open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

theorem prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

theorem primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

theorem sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num

theorem Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · apply hP p <| Nat.prime_of_mem_primeFactors hp
          trans (m:ℝ)
          · exact_mod_cast Nat.le_of_mem_primeFactors hp
          trans (Real.sqrt s.level)
          · exact hm.2
          apply sqrt_le_self s.level s.one_le_level
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw[←hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw[hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw[hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp[h]
      simp
    · intro p hpp _
      rw[hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [if_neg, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log <| Real.sqrt s.level)
  · rw [ge_iff_le]; simp_rw[one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end Sieve
end
end

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
section
open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace BrunTitchmarsh

def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply Sieve.siftedSum_eq
  · exact fun _ _ ↦ rfl
  · exact hz
  · rfl

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x ↦ x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨n/d, ⟨Nat.div_lt_div_of_lt_of_dvd hd han,
      Nat.div_le_div_right (Nat.le_floor hnb)⟩, Nat.div_mul_cancel hd⟩
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).mp ha, Nat.mul_le_of_le_div d r b ha'⟩,
      Nat.dvd_mul_left d r⟩

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b)).card =
      b / d - a / d := by
  rw [Ioc_filter_dvd_eq _ _ _ hd, Finset.card_image_of_injective _ <| mul_left_injective₀ hd,
    Nat.card_Ioc]

include hx in
theorem multSum_eq (d : ℕ) (hd : d ≠ 0) :
    multSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold multSum
  rw [primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hx)]
  · rw [BrunTitchmarsh.card_Ioc_filter_dvd _ _ _ hd]

include hx in
theorem rem_eq (d : ℕ) (hd : d ≠ 0) :
    rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold rem
  rw [multSum_eq x y z hx hz d hd]
  simp [primeInterSieve, if_neg hd]

theorem Nat.ceil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · exact_mod_cast Nat.ceil_le_floor_add_one x
  · gcongr
    exact Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) :
    ∃ C, |C| ≤ 1 ∧ ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  simp only [add_sub_cancel, and_true]
  rw [abs_le]
  refine ⟨by linarith [Nat.lt_floor_add_one x], by linarith [Nat.floor_le hx]⟩

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧ ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  simp only [add_sub_cancel, and_true, abs_le]
  refine ⟨by linarith [Nat.le_ceil x], ?_⟩
  rw [tsub_le_iff_right, add_comm]
  exact Nat.ceil_le_self_add_one x hx

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  exact floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧ ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  · obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
    obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
    rw [hC₁, hC₂]
    refine ⟨C₁ + C₂/d, ?_, by ring⟩
    have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
    have : |C₂/d| ≤ |C₂| := by
      rw [abs_div]
      refine div_le_self (abs_nonneg C₂) ?_
      simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith

include hx hy in
theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) :
    |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| ≤ 5 := by
  rw [rem_eq _ _ _ hx hz _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw [Nat.le_floor_iff, ← add_le_add_iff_right 1]
    · rw_mod_cast [Nat.sub_add_cancel (by simp [hx])]
      linarith [Nat.ceil_le_self_add_one x (le_of_lt hx)]
    linarith
  rw [hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw [hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    rw [(by ring_nf : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂| = |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)|)]
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| ≤
        |(↑d)⁻¹ - (↑d)⁻¹ * C₃| + |C₁ - C₂| := abs_add_le _ _
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃| ≤
        |(↑d)⁻¹| + |(↑d)⁻¹ * C₃| := abs_sub _ _
    have : |C₁ - C₂| ≤ |C₁| + |C₂| := abs_sub _ _
    have : |(d:ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv, Nat.abs_cast]
      exact Nat.cast_inv_le_one _
    have : |(↑d)⁻¹ * C₃| ≤ |C₃| := by
      rw [inv_mul_eq_div, abs_div]
      refine div_le_self (abs_nonneg _) ?_
      rw [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge : (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · exact rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

include hx hy in
theorem primeSieve_rem_sum_le :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d *
          |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  refine rem_sum_le_of_const (primeInterSieve x y z hz) 5 (fun d hd ↦ ?_)
  apply abs_rem_le _ _ _ <;> linarith

include hx hy in
theorem siftedSum_le (hz : 1 < z) :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z (le_of_lt hz)))
      ≤ 2 * y / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1 + Real.log z) ^ 3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · exact boudingSum_ge _ _ _ _
  · exact primeSieve_rem_sum_le x y z hx hy _

end BrunTitchmarsh
end
end

open Finset Filter Erdos1204

/-- An admissible tuple exists at the defining infimum. -/
private theorem minimum_attained (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∀ a ∈ S, a ≤ A k := by
  classical
  apply Nat.sInf_mem (s := {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∀ a ∈ S, a ≤ m})
  let S := (range k).image (fun i => k.factorial * i)
  have hc : S.card = k := by
    rw [show S = _ from rfl, card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left k.factorial_pos h), card_range]
  refine ⟨k.factorial * k, S, hc, ?_, ?_⟩
  · intro p hp
    have : Fact p.Prime := ⟨hp⟩
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      rintro a ha
      obtain ⟨i, _, rfl⟩ := mem_image.mp ha
      have hf : (k.factorial : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_factorial hp.pos hpk)
      simp [hf]
    · have hn : S.image (fun a : ℕ => (a : ZMod p)) ≠ univ := by
        intro h
        have hh := card_image_le (s := S) (f := fun a => (a : ZMod p))
        rw [h, card_univ, ZMod.card, hc] at hh
        omega
      have hex : ∃ r : ZMod p, r ∉ S.image (fun a : ℕ => (a : ZMod p)) := by
        by_contra! hf
        exact hn (Finset.eq_univ_of_forall hf)
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, fun a ha he => hr (mem_image.mpr ⟨a, ha, he⟩)⟩
  · rintro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact Nat.mul_le_mul_left _ (le_of_lt (mem_range.mp hi))

/-- Choose a common translate avoiding zero at every small prime. -/
private theorem translate_avoiding (S : Finset ℕ) (hS : IsAdmissible S) (N : ℕ) :
    ∃ t : ℕ, 0 < t ∧ ∀ a ∈ S, ∀ p : ℕ, p.Prime → p ≤ N → ¬p ∣ t + a := by
  classical
  let P := (range (N+1)).filter Nat.Prime
  let r (p : ℕ) : ZMod p := if h : p.Prime then (hS p h).choose else 0
  let b (p : ℕ) : ℕ := (-r p - 1).val
  obtain ⟨u, hu⟩ := Nat.chineseRemainderOfFinset b id P
    (fun p hp => (mem_filter.mp hp).2.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).2 hpq)
  refine ⟨u + 1, by omega, ?_⟩
  intro a ha p hp hpN hd
  have : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod p) = -r p - 1 := by
    have h := (ZMod.natCast_eq_natCast_iff u (b p) p).2 (hu p (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩))
    simpa [b] using h
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  rw [hu'] at hz
  have ha' : (a : ZMod p) = r p := by linear_combination hz
  exact (hS p hp).choose_spec a ha (by simpa [r, hp] using ha')

private theorem finite_bound {S : Finset ℕ} (hs : IsAdmissible S) {m : ℕ}
    (hm : 0 < m) (hsupp : ∀ a ∈ S, a ≤ m) {z : ℝ} (hz : 1 < z) :
    (S.card : ℝ) ≤ 2 * m / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  classical
  obtain ⟨t, ht, hav⟩ := translate_avoiding S hs ⌊z⌋₊
  have hsubset : S.image (t + ·) ⊆ (Icc (Nat.ceil (t : ℝ)) (Nat.floor ((t : ℝ) + m))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) := by
    rintro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    apply mem_filter.mpr
    constructor
    · simp only [Nat.ceil_natCast, ← Nat.cast_add, Nat.floor_natCast, mem_Icc]
      exact ⟨by omega, Nat.add_le_add_left (hsupp a ha) t⟩
    · exact fun p hp hpz => hav a ha p hp (Nat.le_floor hpz)
  have h := BrunTitchmarsh.siftedSum_le (t : ℝ) (m : ℝ) z (by exact_mod_cast ht)
    (by exact_mod_cast hm) hz
  rw [BrunTitchmarsh.siftedSum_eq_card] at h
  have hc := card_le_card hsubset
  rw [card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)] at hc
  exact le_trans (by exact_mod_cast hc) h

theorem OMA.solution : type_of% @Erdos1204.erdos_1204.variants.A_lower := by
  intro ε hε
  let δ := min ε (1/2 : ℝ)
  have hd : 0 < δ := lt_min hε (by norm_num)
  have hde : δ ≤ ε := min_le_left _ _
  have hdh : δ ≤ 1/2 := min_le_right _ _
  have hu : 0 < 1 - δ := by linarith
  have hsmall := ((isLittleO_log_rpow_rpow_atTop 3 hd).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < δ / 40 by positivity)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog, eventually_ge_atTop 2] with k hs hl hk
  change 1 ≤ Real.log (k : ℝ) at hl
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hL : 0 < Real.log k := by linarith
  change ‖Real.log (k : ℝ) ^ (3 : ℝ)‖ ≤ δ / 40 * ‖(k : ℝ) ^ δ‖ at hs
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hs
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hs
  let z : ℝ := (k : ℝ) ^ (1 - δ)
  have hz : 1 < z := Real.one_lt_rpow hk1 hu
  have hzlog : Real.log z = (1 - δ) * Real.log k := Real.log_rpow hk0 _
  have hzl : Real.log z ≤ Real.log k := by rw [hzlog]; nlinarith [mul_nonneg hd.le hL.le]
  have hpow : (1 + Real.log z)^3 ≤ (2 * Real.log k)^3 := by
    gcongr <;> linarith [Real.log_pos hz]
  have hzid : z * (k : ℝ) ^ δ = k := by
    rw [show z = _ from rfl, ← Real.rpow_add hk0, sub_add_cancel, Real.rpow_one]
  have herr : 5 * z * (1 + Real.log z)^3 ≤ δ * k := by
    calc
      _ ≤ 5 * z * (2 * Real.log k)^3 := by gcongr
      _ = (40 * z) * Real.log k ^ 3 := by ring
      _ ≤ (40 * z) * (δ / 40 * (k : ℝ) ^ δ) := by gcongr
      _ = δ * k := by calc
        _ = δ * (z * (k : ℝ)^δ) := by ring
        _ = _ := by rw [hzid]
  obtain ⟨S, hcard, hS, hsup⟩ := minimum_attained k
  have hm : 0 < A k := by
    by_contra! h
    have hsub : S ⊆ {0} := fun a ha => by simpa using (show a = 0 by have := hsup a ha; omega)
    have hc := card_le_card hsub
    simp [hcard] at hc
    omega
  have h := finite_bound hS hm hsup hz
  rw [hcard] at h
  have hdiv : (1-δ) * k ≤ 2 * A k / Real.log z := by linarith
  have hb := (le_div_iff₀ (Real.log_pos hz)).mp hdiv
  rw [hzlog] at hb
  have hw : (1 / 2 - ε) ≤ (1 - δ)^2 / 2 := by nlinarith [sq_nonneg δ]
  calc
    _ ≤ ((1 - δ)^2 / 2) * k * Real.log k := by gcongr
    _ ≤ A k := by linarith only [hb]
