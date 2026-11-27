import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1
import Mathlib

/-! # Sieving a linear progression

For primes dividing the common modulus or the difference of the progression,
remove a least populated residue class. The Chinese remainder theorem lets us
translate the survivors to an interval on which the ordinary Selberg sieve
applies. The small exceptional primes cost at most the Mertens product and
the total reciprocal mass of the large exceptional primes tends to zero.

The explicit lower Mertens product bound is from @sebastianbachmaier's
merged Erdős 1141 proof. The interval sieve and translation adapt
@marcusbuffett's merged Erdős 1204 proof.
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



namespace OMA_M3
open Real Finset

noncomputable def Sm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p / p
noncomputable def Lm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, -Real.log (1 - 1 / (p:ℝ))
noncomputable def Qm (n : ℕ) : ℝ := ∏ p ∈ (range (n + 1)).filter Nat.Prime, (1 - 1 / (p:ℝ))
noncomputable def cM : ℝ := 2 * Real.log 2 - 1 + 1 / 12
noncomputable def Hm (n : ℕ) : ℝ :=
  Lm n - Real.log (Real.log n) + (Real.log n + cM - Sm n) / Real.log n + 1 / n

lemma filter_succ (n : ℕ) : (range (n + 2)).filter Nat.Prime =
    if (n+1).Prime then insert (n+1) ((range (n+1)).filter Nat.Prime)
    else (range (n+1)).filter Nat.Prime := by
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (range (n+1)).filter Nat.Prime := by simp

lemma Sm_succ (n : ℕ) : Sm (n+1) = Sm n +
    (if (n+1).Prime then Real.log ((n:ℝ)+1) / ((n:ℝ)+1) else 0) := by
  unfold Sm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Lm_succ (n : ℕ) : Lm (n+1) = Lm n +
    (if (n+1).Prime then -Real.log (1 - 1 / ((n:ℝ)+1)) else 0) := by
  unfold Lm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_succ (n : ℕ) : Qm (n+1) = Qm n *
    (if (n+1).Prime then (1 - 1 / ((n:ℝ)+1)) else 1) := by
  unfold Qm
  rw [filter_succ]
  split_ifs
  · rw [prod_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_nonneg (n : ℕ) : 0 ≤ Qm n := by
  unfold Qm
  apply prod_nonneg
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma Qm_anti (n : ℕ) : ∀ m, n ≤ m → Qm m ≤ Qm n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [Qm_succ]
    refine le_trans ?_ ih
    split_ifs
    · have h0 := Qm_nonneg m
      have h1 : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
      nlinarith
    · simp

lemma Qm_eq_exp (n : ℕ) : Qm n = Real.exp (- Lm n) := by
  unfold Qm Lm
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 0 < 1 - 1 / (p:ℝ) := by
    have : 1 / (p:ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  rw [neg_neg, Real.exp_log this]

lemma log_fact_le (t : ℕ) (ht : 1 ≤ t) :
    Real.log (t.factorial) ≤ ((t:ℝ)+1) * Real.log t - t + 1 := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    have htp : (0:ℝ) < t := by exact_mod_cast ht
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((t:ℝ)+1)/t) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h1
    have h2 : 1 - (t:ℝ) / (t+1) = 1 / (t+1) := by field_simp; ring
    rw [h2] at h1
    have h3 : 1 ≤ ((t:ℝ)+1) * (Real.log (t+1) - Real.log t) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    push_cast
    nlinarith

lemma sum_div_log_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, ((t / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (t.factorial) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s := (range (t+1)).filter Nat.Prime) ?_ ?_)
  · apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
    rw [Nat.factorization_factorial hpp (Nat.lt_succ_of_le (Nat.log_le_self p t))]
    have h1 : 1 ∈ Ico 1 (t+1) := by
      simp only [mem_Ico]; have := hpp.two_le; omega
    have := Finset.single_le_sum (f := fun i => t / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simp only [pow_one] at this
    exact_mod_cast this
  · intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hpp, Nat.dvd_factorial hpp.pos hpt, Nat.factorial_ne_zero t⟩
  · intro p _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

lemma theta_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, Real.log p ≤ 2 * Real.log 2 * t := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg t)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range] at h
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [this] at h
  linarith

lemma log_aux (t : ℝ) (ht : 64 ≤ t) : Real.log t + 1 ≤ t / 12 := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (x := t / 64) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num), h64] at h1
  have := Real.log_two_lt_d9
  linarith

lemma mertens1 (t : ℕ) (ht : 64 ≤ t) : Sm t ≤ Real.log t + cM := by
  have htr : (64:ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t:ℝ) * Sm t ≤ ∑ p ∈ (range (t+1)).filter Nat.Prime,
      (((t / p : ℕ) : ℝ) * Real.log p + Real.log p) := by
    unfold Sm
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp2 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hlt := Nat.lt_mul_div_succ t hpp.pos
    have hle : (t:ℝ) ≤ p * (((t / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
    have : (t:ℝ) / p ≤ ((t / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp2]; linarith
    have hl := Real.log_natCast_nonneg p
    calc (t:ℝ) * (Real.log p / p) = ((t:ℝ) / p) * Real.log p := by ring
      _ ≤ (((t / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right this hl
      _ = _ := by ring
  rw [sum_add_distrib] at h1
  have h2 := sum_div_log_le t
  have h3 := theta_le t
  have h4 := log_fact_le t (by omega)
  have h5 := log_aux t htr
  have htp : (0:ℝ) < t := by linarith
  have key : (t:ℝ) * Sm t ≤ t * (Real.log t + cM) := by
    unfold cM; nlinarith
  exact le_of_mul_le_mul_left key htp

lemma key_ineq (a b u : ℝ) (ha : 0 < a) (hab : a < b) (hu : -a ≤ u) :
    u / b - Real.log b ≤ u / a - Real.log a := by
  have hb : 0 < b := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (x := b / a) (by positivity)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have e1 : u / b - u / a = -(u * (b - a)) / (a * b) := by field_simp; ring
  have e2 : 1 - a / b = (b - a) / b := by field_simp
  have h2 : -(u * (b - a)) / (a * b) ≤ (b - a) / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    have : 0 < b - a := by linarith
    have : -u * (b - a) ≤ a * (b - a) := mul_le_mul_of_nonneg_right (by linarith) this.le
    nlinarith
  linarith

lemma H_step (m : ℕ) (hm : 64 ≤ m) : Hm (m+1) ≤ Hm m := by
  have hS := mertens1 m hm
  have hmr : (64:ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < Real.log m := Real.log_pos (by linarith)
  have hab : Real.log m < Real.log ((m:ℝ)+1) := Real.log_lt_log (by linarith) (by linarith)
  have hb : 0 < Real.log ((m:ℝ)+1) := by linarith
  have K := key_ineq _ _ (cM - Sm m) ha hab (by linarith)
  have hD : -Real.log (1 - 1 / ((m:ℝ)+1)) ≤ 1 / m := by
    have e : 1 - 1 / ((m:ℝ)+1) = ((m:ℝ)+1)⁻¹ * m := by field_simp; ring
    have := Real.log_le_sub_one_of_pos (x := ((m:ℝ)+1) / m) (by positivity)
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_inv]
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e2 : ((m:ℝ)+1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have hinv : 1 / ((m:ℝ)+1) ≤ 1 / m := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hinv0 : 0 ≤ 1 / ((m:ℝ)+1) := by positivity
  have ea : (Real.log m + cM - Sm m) / Real.log m = 1 + (cM - Sm m) / Real.log m := by
    field_simp; ring
  unfold Hm
  rw [Lm_succ, Sm_succ]
  push_cast
  rw [ea]
  split_ifs
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + Real.log ((m:ℝ)+1) / ((m:ℝ)+1)))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) - 1 / ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + 0))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith

lemma H_le (n : ℕ) (hn : 64 ≤ n) : Hm n ≤ Hm 64 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (H_step n hn) ih

lemma log_ge (p q m : ℕ) (hq : 0 < q) (h : 2 ^ m ≤ p ^ q) :
    (m:ℝ) / q * Real.log 2 ≤ Real.log p := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; rw [zero_pow hq.ne'] at h; have := Nat.one_le_two_pow (n := m); omega
    · exact h0
  have : (m:ℝ) * Real.log 2 ≤ q * Real.log p := by
    rw [← Real.log_pow, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_le_iff₀ hq']
  linarith

lemma filt64 : (Finset.range 65).filter Nat.Prime =
    {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61} := by decide

lemma Q64 : Qm 64 = 770527199232000/5855632691117327 := by
  unfold Qm
  rw [filt64]
  norm_num [prod_insert]

lemma S64 : (419/100 : ℝ) * Real.log 2 ≤ Sm 64 := by
  unfold Sm
  rw [filt64]
  norm_num [sum_insert]
  have h3 := log_ge 3 2 3 (by norm_num) (by norm_num)
  have h5 := log_ge 5 4 9 (by norm_num) (by norm_num)
  have h7 := log_ge 7 4 11 (by norm_num) (by norm_num)
  have h11 := log_ge 11 3 10 (by norm_num) (by norm_num)
  have h13 := log_ge 13 3 11 (by norm_num) (by norm_num)
  have h17 := log_ge 17 1 4 (by norm_num) (by norm_num)
  have h19 := log_ge 19 1 4 (by norm_num) (by norm_num)
  have h23 := log_ge 23 2 9 (by norm_num) (by norm_num)
  have h29 := log_ge 29 4 19 (by norm_num) (by norm_num)
  have h31 := log_ge 31 4 19 (by norm_num) (by norm_num)
  have h37 := log_ge 37 1 5 (by norm_num) (by norm_num)
  have h41 := log_ge 41 3 16 (by norm_num) (by norm_num)
  have h43 := log_ge 43 3 16 (by norm_num) (by norm_num)
  have h47 := log_ge 47 2 11 (by norm_num) (by norm_num)
  have h53 := log_ge 53 3 17 (by norm_num) (by norm_num)
  have h59 := log_ge 59 4 23 (by norm_num) (by norm_num)
  have h61 := log_ge 61 4 23 (by norm_num) (by norm_num)
  norm_num at h3 h5 h7 h11 h13 h17 h19 h23 h29 h31 h37 h41 h43 h47 h53 h59 h61
  have := Real.log_two_gt_d9
  linarith

lemma H64 : Hm 64 ≤ Real.log 3 := by
  have hL : Lm 64 = -Real.log (Qm 64) := by
    rw [Qm_eq_exp, Real.log_exp]; ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hℓ : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have hℓpos : 0 < Real.log 64 := by rw [hℓ]; linarith
  have hS := S64
  have hX : (Real.log 64 + cM - Sm 64) / Real.log 64 ≤ 0.44 - 1/64 := by
    rw [div_le_iff₀ hℓpos]; unfold cM; rw [hℓ]; linarith
  have hE : Real.exp 0.44 ≤ 3 * Real.log 64 * (770527199232000/5855632691117327) := by
    have e : Real.exp (0.44:ℝ) = Real.exp 0.055 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 0.055 ≤ 1 / (1 - 0.055) :=
      Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    have h2 : Real.exp 0.055 ^ 8 ≤ (1 / (1 - 0.055)) ^ 8 :=
      pow_le_pow_left₀ (Real.exp_pos _).le h1 8
    rw [e, hℓ]
    norm_num at h2 ⊢
    linarith
  have hlog : (0.44:ℝ) ≤ Real.log 3 + Real.log (Real.log 64)
      + Real.log (770527199232000/5855632691117327) := by
    have := Real.log_le_log (Real.exp_pos _) hE
    rw [Real.log_exp, Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by norm_num) hℓpos.ne'] at this
    exact this
  unfold Hm
  rw [hL, Q64]
  simp only [Nat.cast_ofNat]
  linarith

lemma big (n : ℕ) (hn : 64 ≤ n) : 1 / (3 * Real.log n) ≤ Qm n := by
  have hH := le_trans (H_le n hn) H64
  have hS := mertens1 n hn
  have hnr : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hnn : 0 ≤ (Real.log n + cM - Sm n) / Real.log n := div_nonneg (by linarith) hlogpos.le
  have h1n : 0 ≤ 1 / (n:ℝ) := by positivity
  have hL : Lm n ≤ Real.log 3 + Real.log (Real.log n) := by unfold Hm at hH; linarith
  rw [Qm_eq_exp]
  have e : 1 / (3 * Real.log n) = Real.exp (-(Real.log 3 + Real.log (Real.log n))) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hlogpos]
    rw [one_div]
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

end OMA_M3

open Finset
namespace Progression360

/-- Excluding a least frequent class costs at most a reciprocal prime fraction. -/
theorem thin (P T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ U ⊆ T, (T.card : ℝ) * ∏ p ∈ P, (1 - 1/(p : ℝ)) ≤ U.card ∧
      ∀ p ∈ P, ∃ r : ZMod p, ∀ k ∈ U, (k : ZMod p) ≠ r := by
  classical
  induction P using Finset.induction_on generalizing T with
  | empty => exact ⟨T, Subset.rfl, by simp, by simp⟩
  | @insert p P hnot ih =>
    have hp := hP p (mem_insert_self _ _)
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨U, hUT, hsize, hmiss⟩ := ih T (fun q hq => hP q (mem_insert_of_mem hq))
    let f (k : ℕ) : ZMod p := k
    obtain ⟨j, _, hj⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
      (s := U) (t := (univ : Finset (ZMod p))) (f := f) (n := U.card / p + 1) (by
        rw [card_univ, ZMod.card]; exact Nat.lt_mul_div_succ _ hp.pos)
    let V := U.filter fun k => f k ≠ j
    have hV : V.card + (U.filter fun k => f k = j).card = U.card := by
      simpa [V, add_comm] using U.card_filter_add_card_filter_not (fun k => f k = j)
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hjle : (U.filter fun k => f k = j).card * p ≤ U.card :=
      (Nat.le_div_iff_mul_le hp.pos).mp (by omega)
    have hreal : (U.card : ℝ) * (1 - 1/(p : ℝ)) ≤ V.card := by
      have he : (V.card : ℝ) + (U.filter fun k => f k = j).card = U.card := by exact_mod_cast hV
      have hh : ((U.filter fun k => f k = j).card : ℝ) * p ≤ U.card := by exact_mod_cast hjle
      rw [mul_sub, mul_one, ← div_eq_mul_one_div, sub_le_iff_le_add]
      linarith [(le_div_iff₀ hpR).2 hh]
    refine ⟨V, (filter_subset _ _).trans hUT, ?_, ?_⟩
    · rw [prod_insert hnot, mul_comm (1 - 1 / (p : ℝ)), ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right hsize (by
        have : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
        exact sub_nonneg.mpr ((div_le_one hpR).mpr this))).trans hreal
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact ⟨j, fun k hk => (mem_filter.mp hk).2⟩
      · obtain ⟨r, hr⟩ := hmiss q hq
        exact ⟨r, fun k hk => hr k (mem_filter.mp hk).1⟩

/-- Exact ratio between the weights lost at small primes and a lower bound on losses
from the remaining large primes. -/
theorem product_union_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    1 - ∑ p ∈ S, 1/(p : ℝ) ≤ ∏ p ∈ S, (1 - 1/(p : ℝ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have prime := hS p (mem_insert_self _ _)
    have hrec : 0 ≤ 1 - 1/(p : ℝ) := by
      have pp : (1:ℝ) < p := by exact_mod_cast prime.one_lt
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr pp.le)
    have hh := mul_le_mul_of_nonneg_left (ih (fun q hq => hS q (mem_insert_of_mem hq))) hrec
    rw [sum_insert hp, prod_insert hp]
    have hsum : 0 ≤ ∑ i ∈ S, 1/(i:ℝ) := by positivity
    apply le_trans _ hh
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1/(p:ℝ)) hsum]

end Progression360

open Finset Filter
namespace Progression360
theorem translate_avoiding (S : Finset ℕ) (N : ℕ) (hS : ∀ p : ℕ, p.Prime → p ≤ N → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r) :
    ∃ t : ℕ, 0 < t ∧ ∀ a ∈ S, ∀ p : ℕ, p.Prime → p ≤ N → ¬p ∣ t + a := by
  classical
  let P := (range (N+1)).filter Nat.Prime
  let r (p : ℕ) : ZMod p := if h : p.Prime ∧ p ≤ N then (hS p h.1 h.2).choose else 0
  let b (p : ℕ) : ℕ := (-r p - 1).val
  obtain ⟨u, hu⟩ := Nat.chineseRemainderOfFinset b id P
    (fun p hp => (mem_filter.mp hp).2.ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).2 hpq)
  refine ⟨u + 1, by omega, ?_⟩
  intro a ha p hp hpN hd
  haveI : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod p) = -r p - 1 := by
    have h := (ZMod.natCast_eq_natCast_iff u (b p) p).2 (hu p (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩))
    simpa [b] using h
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hz
  rw [hu'] at hz
  have ha' : (a : ZMod p) = r p := by linear_combination hz
  exact (hS p hp hpN).choose_spec a ha (by simpa [r, hp, hpN] using ha')

theorem finite_bound {S : Finset ℕ} {m : ℕ}
    (hm : 0 < m) (hsupp : ∀ a ∈ S, a ≤ m) {z : ℝ} (hz : 1 < z)
    (hs : ∀ p : ℕ, p.Prime → p ≤ ⌊z⌋₊ → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r) :
    (S.card : ℝ) ≤ 2 * m / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  classical
  obtain ⟨t, ht, hav⟩ := translate_avoiding S ⌊z⌋₊ hs
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


end Progression360

open Filter
namespace Progression360
theorem sieve_error : ∀ᶠ r : ℕ in atTop, ∀ L : ℕ, (r : ℝ)^(1/16 : ℝ) ≤ L →
    let z := (r : ℝ)^(1/17 : ℝ)
    1 < z ∧ z ≤ r ∧ 0 < Real.log r ∧
    2 * L / Real.log z + 5 * z * (1 + Real.log z)^3 ≤ 35 * L / Real.log r := by
  have hsmall := ((isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0:ℝ) < 1/272)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show (0:ℝ) < 1/40 by norm_num)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hsmall, hlog, eventually_ge_atTop 2] with r hs hl hr
  change 1 ≤ Real.log (r : ℝ) at hl
  change ‖Real.log (r : ℝ) ^ (4 : ℝ)‖ ≤ 1/40 * ‖(r : ℝ)^(1/272 : ℝ)‖ at hs
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hs
  intro L hL
  let z := (r : ℝ)^(1/17 : ℝ)
  have hr1 : 1 < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hpos : 0 < (r : ℝ) := by linarith
  have hz := Real.one_lt_rpow hr1 (by norm_num : (0:ℝ) < 1/17)
  have hzle : z ≤ r := by
    calc
      z ≤ (r : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1.le (by norm_num)
      _ = _ := Real.rpow_one _
  have hzl : Real.log z = (1/17) * Real.log r := Real.log_rpow hpos _
  have hlogr : 0 < Real.log (r : ℝ) := by linarith
  refine ⟨hz, hzle, hlogr, ?_⟩
  change 2 * (L : ℝ) / Real.log z + 5 * z * (1 + Real.log z)^3 ≤ _
  have hcube : (1 + Real.log z)^3 ≤ (2*Real.log r)^3 := by
    gcongr <;> linarith [Real.log_pos hz]
  have hzsum : z * (r : ℝ)^(1/272 : ℝ) = (r : ℝ)^(1/16 : ℝ) := by
    dsimp [z]; rw [← Real.rpow_add hpos]; norm_num
  have herr : 5 * z * (1+Real.log z)^3 * Real.log r ≤ L := calc
    _ ≤ 5 * z * (2 * Real.log r)^3 * Real.log r := by gcongr
    _ = z * (40 * (Real.log r)^4) := by ring
    _ ≤ z * (r : ℝ)^(1/272 : ℝ) := by gcongr; linarith only [hs]
    _ ≤ _ := hzsum.trans_le hL
  have hterm := (le_div_iff₀ hlogr).2 herr
  rw [hzl] at *
  calc
    _ ≤ 2 * (L:ℝ) / ((1 / 17) * Real.log r) + L / Real.log r := by linarith only [hterm]
    _ = _ := by ring
end Progression360

open Finset
namespace Progression360
theorem thin_divisors (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n)
    (hlog : 128 ≤ Real.log n) (T : Finset ℕ) :
    ∃ U ⊆ T, (T.card : ℝ) ≤ 7 * Real.log (Real.log n) * U.card ∧
      ∀ p : ℕ, p.Prime → p ∣ b*n → ∃ j : ZMod p, ∀ k ∈ U, (k : ZMod p) ≠ j := by
  classical
  let x := Real.log (n : ℝ)
  let Y := ⌊x^2⌋₊
  let A := (range (Y+1)).filter Nat.Prime
  let B := (b*n).primeFactors.filter fun p => Y < p
  have hx : 128 ≤ x := hlog
  have hx0 : 0 < x := by linarith
  have hll : 0 < Real.log x := Real.log_pos (by linarith)
  have hY : 64 ≤ Y := Nat.le_floor (by norm_num; nlinarith)
  have hlogY : Real.log (Y:ℝ) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by exact_mod_cast (show 0 < Y by omega))
        (Nat.floor_le (sq_nonneg _))
      _ = _ := by rw [Real.log_pow]; norm_num
  have hA := OMA_M3.big Y hY
  change 1/(3*Real.log (Y:ℝ)) ≤ ∏ p ∈ A, (1-1/(p:ℝ)) at hA
  obtain ⟨V, hVT, hV, hVm⟩ := thin A T (fun p hp => (mem_filter.mp hp).2)
  have hVA : (T.card:ℝ) ≤ 6*Real.log x * V.card := by
    have hly : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
    have hs := (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (T.card:ℝ))).trans hV
    rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)] at hs
    nlinarith [mul_le_mul_of_nonneg_right hlogY (by positivity : 0 ≤ (V.card:ℝ))]
  have hBP : ∀ p ∈ B, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  obtain ⟨U, hUV, hU, hUm⟩ := thin B V hBP
  have hcard : (B.card : ℝ) ≤ 4*x := by
    have hnprod := Nat.mul_pos hb hn
    have hbase : 2 ^ (b*n).primeFactors.card ≤ b*n := calc
      _ = ∏ _p ∈ (b*n).primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ (b*n).primeFactors, p := Finset.prod_le_prod' fun p hp =>
        (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ _ := Nat.le_of_dvd hnprod (Nat.prod_primeFactors_dvd _)
    have hp2 : (2:ℝ)^((b*n).primeFactors.card) ≤ (n:ℝ)^2 := by
      exact_mod_cast hbase.trans (by simpa [sq] using Nat.mul_le_mul_right n hbn)
    have hh := Real.log_le_log (by positivity) hp2
    rw [Real.log_pow, Real.log_pow] at hh
    have hc := Finset.card_filter_le (b*n).primeFactors (fun p => Y < p)
    change B.card ≤ (b*n).primeFactors.card at hc
    have hcr : (B.card:ℝ) ≤ (b*n).primeFactors.card := by exact_mod_cast hc
    have hh' : ((b*n).primeFactors.card : ℝ) * Real.log 2 ≤ 2*x := by simpa [x] using hh
    have hhalf : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hj := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ ((b*n).primeFactors.card : ℝ) by positivity)
    linarith only [hcr, hh', hj]
  have hsmall : (∑ p ∈ B, 1/(p:ℝ)) ≤ 1/16 := calc
    _ ≤ ∑ _p ∈ B, 1/x^2 := Finset.sum_le_sum fun p hp =>
      one_div_le_one_div_of_le (sq_pos_of_pos hx0) ((Nat.lt_of_floor_lt (mem_filter.mp hp).2).le)
    _ = B.card / x^2 := by simp [div_eq_mul_inv]
    _ ≤ 1/16 := (div_le_iff₀ (sq_pos_of_pos hx0)).2 (by nlinarith [mul_nonneg hx0.le (show 0 ≤ x-128 by linarith)])
  have hprod : (15/16:ℝ) ≤ ∏ p ∈ B, (1-1/(p:ℝ)) :=
    le_trans (by linarith only [hsmall]) (product_union_bound B hBP)
  have hUV' := (mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (V.card:ℝ))).trans hU
  have hVC : (V.card : ℝ) ≤ (16/15:ℝ) * U.card := by linarith
  refine ⟨U, hUV.trans hVT, hVA.trans ?_, ?_⟩
  · change 6 * Real.log x * (V.card:ℝ) ≤ 7 * Real.log x * U.card
    have := mul_le_mul_of_nonneg_left hVC (show 0 ≤ 6*Real.log x by positivity)
    nlinarith [mul_nonneg hll.le (by positivity : 0 ≤ (U.card:ℝ))]
  · intro p hp hpd
    by_cases hpY : p ≤ Y
    · have hmem : p ∈ A := mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
      obtain ⟨j,hj⟩ := hVm p hmem
      exact ⟨j,fun k hk => hj k (hUV hk)⟩
    · exact hUm p (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hpd,(Nat.mul_pos hb hn).ne'⟩,by omega⟩)
end Progression360

open Filter Finset
namespace Progression360
theorem progression_bound :
    ∀ᶠ n : ℕ in atTop, ∀ r a b L : ℕ, (n : ℝ)^(1/10 : ℝ) ≤ r → r ≤ n →
    1 ≤ b → b ≤ n → (r : ℝ)^(1/16 : ℝ) ≤ L →
    let P := (range r).image (Nat.nth Nat.Prime) \ n.primeFactors
    (((range L).filter fun k ↦ ∀ p ∈ P, ¬ p ∣ a + b*k).card : ℝ) ≤
      256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ) := by
  classical
  obtain ⟨R,hR⟩ := eventually_atTop.mp sieve_error
  have hnr := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (R : ℝ)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 128
  filter_upwards [hnr,hlog,eventually_ge_atTop 1] with n hnR hnlog hn r a b L hrn _ hb hbn hL
  change (R:ℝ) ≤ (n:ℝ)^(1/10 : ℝ) at hnR
  change 128 ≤ Real.log (n:ℝ) at hnlog
  have hr : R ≤ r := by exact_mod_cast hnR.trans hrn
  let z := (r : ℝ)^(1/17 : ℝ)
  obtain ⟨hz, hzr, hlr, herr⟩ := hR r hr L hL
  let P := (range r).image (Nat.nth Nat.Prime) \ n.primeFactors
  let T := (range L).filter fun k ↦ ∀ p ∈ P, ¬ p ∣ a + b*k
  obtain ⟨U, hUT, hsize, hbad⟩ := thin_divisors n b hn hb hbn hnlog T
  have hLp : 0 < L := by
    have hrpos : 0 < (r:ℝ) := by
      have : 0 < (n:ℝ)^(1/10 : ℝ) := by positivity
      exact this.trans_le hrn
    have : 0 < (L:ℝ) := (Real.rpow_pos_of_pos hrpos _).trans_le hL
    exact_mod_cast this
  have hadm : ∀ p : ℕ, p.Prime → p ≤ ⌊z⌋₊ → ∃ j : ZMod p, ∀ k ∈ U, (k : ZMod p) ≠ j := by
    intro p hp hpz
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hpd : p ∣ b*n
    · exact hbad p hp hpd
    have hpb : ¬ p ∣ b := fun h => hpd (dvd_mul_of_dvd_left h n)
    have hpn : ¬ p ∣ n := fun h => hpd (dvd_mul_of_dvd_right h b)
    have hip : Nat.count Nat.Prime p < r := by
      have hcast := (Nat.le_floor_iff (by positivity : 0 ≤ z)).mp hpz
      have hpr : p ≤ r := by exact_mod_cast hcast.trans hzr
      have hh := Nat.add_two_le_nth_prime (Nat.count Nat.Prime p)
      rw [Nat.nth_count hp] at hh
      omega
    have hP : p ∈ P := mem_sdiff.mpr ⟨mem_image.mpr
      ⟨Nat.count Nat.Prime p, mem_range.mpr hip, Nat.nth_count hp⟩,
      fun h => hpn (Nat.dvd_of_mem_primeFactors h)⟩
    have hbz : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff _ _).mp h)
    refine ⟨-(a : ZMod p) / b, ?_⟩
    intro k hk he
    have hnz := (mem_filter.mp (hUT hk)).2 p hP
    apply hnz
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    have eh := (eq_div_iff hbz).mp he
    linear_combination eh
  have hs := finite_bound hLp (fun k hk => (mem_range.mp (mem_filter.mp (hUT hk)).1).le) hz hadm
  have hll : 0 ≤ Real.log (Real.log (n:ℝ)) := Real.log_nonneg (by linarith)
  change (T.card:ℝ) ≤ _
  calc
    _ ≤ 7 * Real.log (Real.log (n:ℝ)) * (35*L / Real.log (r:ℝ)) :=
      hsize.trans (mul_le_mul_of_nonneg_left (hs.trans herr) (by positivity))
    _ ≤ _ := by
      rw [mul_div_assoc' (7 * Real.log (Real.log (n:ℝ)))]
      apply div_le_div_of_nonneg_right _ hlr.le
      nlinarith [mul_nonneg hll (by positivity : 0 ≤ (L:ℝ))]
end Progression360

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1.H2 :=
  Progression360.progression_bound
