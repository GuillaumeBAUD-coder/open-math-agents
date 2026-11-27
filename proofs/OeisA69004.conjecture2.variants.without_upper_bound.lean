import FormalConjectures.OEIS.«69004»
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The proposed lower bound for A069004 fails along powers of a suitable fixed squarefree integer.
A finite Selberg upper bound controls the norm values. The character modulo four supplies a
logarithmic denominator, which grows by the reciprocal totient factor of the chosen integer.

Credit: @cjchaffin, using Codex. GPT-6.2 Astra developed the paper sieve argument and
GPT-6.2 Sol constructed and verified the Lean proof.
-/

section

-- Upper Möbius inversion and the optimal finite support for the Selberg weights.

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace BoundingSieve

private theorem sum_upper_moebius {P : ℕ} (hP : P ≠ 0) {l : ℕ} (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then
      ∑ m ∈ P.divisors, if d ∣ m then (μ (m / d) : ℝ) * f m else 0 else 0) = f l := by
  classical
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  have hm (m : ℕ) (hmP : m ∈ P.divisors) :
      (∑ d ∈ P.divisors, if l ∣ d then
        if d ∣ m then (μ (m / d) : ℝ) else 0 else 0) = if m = l then 1 else 0 := by
    have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hP (dvd_of_mem_divisors hmP)
    by_cases hlm : l ∣ m
    · simp_rw [← ite_and, ← sum_filter]
      have hfilter : (P.divisors.filter fun d => l ∣ d ∧ d ∣ m) =
          m.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [mem_filter, mem_divisors]
        exact ⟨fun h => ⟨⟨h.2.2, hm0⟩, h.2.1⟩,
          fun h => ⟨⟨h.1.1.trans (dvd_of_mem_divisors hmP), hP⟩, h.2, h.1.1⟩⟩
      rw [hfilter]
      have hsum : (∑ d ∈ m.divisors.filter (fun d => l ∣ d), (μ (m / d) : ℝ)) =
          ∑ e ∈ (m / l).divisors, (μ ((m / l) / e) : ℝ) := by
        refine sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
        · intro d hd
          rw [mem_filter, mem_divisors] at hd
          rw [mem_divisors]
          exact ⟨Nat.div_dvd_div hd.2 hd.1.1,
            Nat.ne_of_gt (Nat.div_pos (le_of_dvd (Nat.pos_of_ne_zero hm0) hlm)
              (pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP)))⟩
        · intro d hd e he eq
          have hd' := (mem_filter.mp hd).2
          have he' := (mem_filter.mp he).2
          exact (Nat.div_mul_cancel hd').symm.trans (by rw [eq, Nat.div_mul_cancel he'])
        · intro e he
          have he' := dvd_of_mem_divisors he
          refine ⟨e * l, mem_filter.mpr ⟨mem_divisors.mpr ⟨?_, hm0⟩, dvd_mul_left _ _⟩, ?_⟩
          · rw [← Nat.div_mul_cancel hlm]
            exact Nat.mul_dvd_mul he' (dvd_refl l)
          · exact Nat.mul_div_cancel _ (pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP))
        · intro d hd
          have hld := (mem_filter.mp hd).2
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm l, Nat.div_mul_cancel hld]
      rw [hsum]
      rw [Nat.sum_div_divisors (m / l) (fun e => (μ e : ℝ))]
      have hμ : (∑ e ∈ (m / l).divisors, (μ e : ℝ)) = if m / l = 1 then 1 else 0 := by
        have h := DFunLike.congr_fun (ArithmeticFunction.moebius_mul_coe_zeta) (m / l)
        rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
        exact_mod_cast h
      rw [hμ]
      have heq : m / l = 1 ↔ m = l := by
        constructor
        · intro h
          simpa [h] using (Nat.div_mul_cancel hlm).symm
        · rintro rfl
          exact Nat.div_self (pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero hP))
      simp [heq]
    · have hml : m ≠ l := fun h => hlm (h ▸ dvd_refl l)
      rw [if_neg hml]
      refine sum_eq_zero fun d _ => ?_
      split_ifs with hld hdm
      · exact (hlm (hld.trans hdm)).elim
      · rfl
      · rfl
  calc
    _ = ∑ m ∈ P.divisors, (∑ d ∈ P.divisors, if l ∣ d then
          if d ∣ m then (μ (m / d) : ℝ) else 0 else 0) * f m := by
      simp only [sum_mul, ite_mul, zero_mul]
    _ = f l := by
      rw [sum_congr rfl fun m hmP => congrArg (· * f m) (hm m hmP)]
      simp [ite_mul, mem_divisors.mpr ⟨hl, hP⟩]

variable (s : BoundingSieve)

/-- Diagonal terms with indices at most the chosen integer cutoff. -/
noncomputable def selbergCut (z d : ℕ) : ℝ := if d ≤ z then s.selbergTerms d else 0

/-- The normalizing denominator for the optimized upper-bound sieve. -/
noncomputable def selbergDenominator (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, s.selbergCut z d

/-- Finite support weights obtained by upper Möbius inversion. -/
noncomputable def optimalWeights (z d : ℕ) : ℝ :=
  ((∑ m ∈ s.prodPrimes.divisors, if d ∣ m then
    (μ (m / d) : ℝ) * ((μ m : ℝ) * s.selbergCut z m) else 0) / s.nu d) /
    s.selbergDenominator z

theorem selbergCut_nonneg {z d : ℕ} (hd : d ∣ s.prodPrimes) : 0 ≤ s.selbergCut z d := by
  unfold selbergCut
  split_ifs
  · exact (s.selbergTerms_pos hd).le
  · exact le_rfl

theorem selbergDenominator_pos {z : ℕ} (hz : 1 ≤ z) : 0 < s.selbergDenominator z := by
  have hm : 1 ∈ s.prodPrimes.divisors :=
    mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩
  apply lt_of_lt_of_le ((s.selbergTerms_pos (one_dvd s.prodPrimes)))
  simpa only [selbergDenominator, selbergCut, if_pos hz] using
    (single_le_sum (f := s.selbergCut z)
      (fun d hd => s.selbergCut_nonneg (dvd_of_mem_divisors hd)) hm)

theorem optimalWeights_one {z : ℕ} (hz : 1 ≤ z) : s.optimalWeights z 1 = 1 := by
  unfold optimalWeights
  simp only [one_dvd, if_true, Nat.div_one, s.nu_mult.map_one, div_one]
  have hsum : (∑ m ∈ s.prodPrimes.divisors,
      (μ m : ℝ) * ((μ m : ℝ) * s.selbergCut z m)) = s.selbergDenominator z := by
    apply sum_congr rfl
    intro m hm
    have hμ : (μ m : ℝ) ^ 2 = 1 := by
      exact_mod_cast moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hm)
    rw [← mul_assoc, ← pow_two, hμ, one_mul]
  rw [hsum, div_self (s.selbergDenominator_pos hz).ne']

theorem optimalWeights_eq_zero_of_lt {z d : ℕ} (h : z < d) : s.optimalWeights z d = 0 := by
  unfold optimalWeights
  have hsum : (∑ m ∈ s.prodPrimes.divisors, if d ∣ m then
      (μ (m / d) : ℝ) * ((μ m : ℝ) * s.selbergCut z m) else 0) = 0 := by
    refine sum_eq_zero fun m hm => ?_
    split_ifs with hdm
    · have hm0 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
        (dvd_of_mem_divisors hm))
      simp [selbergCut, not_le_of_gt (h.trans_le (Nat.le_of_dvd hm0 hdm))]
    · rfl
  rw [hsum, zero_div, zero_div]

theorem optimalWeights_upper_sum {z l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * s.optimalWeights z d else 0) =
      ((μ l : ℝ) * s.selbergCut z l) / s.selbergDenominator z := by
  let f : ℕ → ℝ := fun d => (μ d : ℝ) * s.selbergCut z d
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then
        ∑ m ∈ s.prodPrimes.divisors, if d ∣ m then
          (μ (m / d) : ℝ) * f m else 0 else 0) / s.selbergDenominator z := by
      rw [div_eq_mul_inv, sum_mul]
      refine sum_congr rfl fun d hd => ?_
      split_ifs with hld
      · have hdν := (s.nu_pos_of_dvd_prodPrimes (dvd_of_mem_divisors hd)).ne'
        unfold optimalWeights f
        simp only [div_eq_mul_inv, ← mul_assoc]
        congr 1
        rw [mul_comm (s.nu d), mul_assoc, mul_inv_cancel₀ hdν, mul_one]
      · simp
    _ = _ := by rw [sum_upper_moebius s.prodPrimes_ne_zero hl]

theorem optimalWeights_mainSum {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (lambdaSquared (s.optimalWeights z)) = (s.selbergDenominator z)⁻¹ := by
  have hden := (s.selbergDenominator_pos hz).ne'
  rw [mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    _ = ∑ l ∈ s.prodPrimes.divisors, s.selbergCut z l / (s.selbergDenominator z) ^ 2 := by
      refine sum_congr rfl fun l hl => ?_
      rw [s.optimalWeights_upper_sum (dvd_of_mem_divisors hl)]
      have hμ : (μ l : ℝ) ^ 2 = 1 := by
        exact_mod_cast moebius_sq_eq_one_of_squarefree (s.squarefree_of_mem_divisors_prodPrimes hl)
      by_cases h : l ≤ z
      · have hg := (s.selbergTerms_pos (dvd_of_mem_divisors hl)).ne'
        simp only [selbergCut, if_pos h, div_pow, mul_pow, hμ, one_mul]
        field_simp
      · simp [selbergCut, h]
    _ = _ := by
      simp only [div_eq_mul_inv, ← sum_mul]
      change s.selbergDenominator z * ((s.selbergDenominator z) ^ 2)⁻¹ = _
      field_simp

theorem abs_optimalWeights_le_inv_nu {z d : ℕ} (hz : 1 ≤ z) (hd : d ∣ s.prodPrimes) :
    |s.optimalWeights z d| ≤ (s.nu d)⁻¹ := by
  have hdν := s.nu_pos_of_dvd_prodPrimes hd
  have hg := s.selbergDenominator_pos hz
  unfold optimalWeights
  simp only [abs_div, abs_of_pos hdν, abs_of_pos hg]
  apply (div_le_iff₀ hg).2
  rw [inv_mul_eq_div]
  apply div_le_div_of_nonneg_right _ hdν.le
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  split_ifs
  · have hcut := s.selbergCut_nonneg (z := z) (dvd_of_mem_divisors hm)
    have hm1 : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := m))
    have hmd1 : |(μ (m / d) : ℝ)| ≤ 1 := by
      exact_mod_cast (abs_moebius_le_one (n := m / d))
    rw [abs_mul, abs_mul, abs_of_nonneg hcut]
    exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) hcut) hmd1).trans
      (mul_le_of_le_one_left hcut hm1)
  · simpa only [abs_zero] using s.selbergCut_nonneg (z := z) (dvd_of_mem_divisors hm)

theorem optimal_lambdaSquared_eq_zero_of_lt {z d : ℕ} (h : z ^ 2 < d) :
    lambdaSquared (s.optimalWeights z) d = 0 := by
  unfold lambdaSquared
  refine sum_eq_zero fun a had => sum_eq_zero fun b hbd => ?_
  by_cases ha : a ≤ z
  · by_cases hb : b ≤ z
    · have hd0 := Nat.pos_of_ne_zero (mem_divisors.mp had).2
      have ha0 := pos_of_dvd_of_pos (dvd_of_mem_divisors had) hd0
      have hb0 := pos_of_dvd_of_pos (dvd_of_mem_divisors hbd) hd0
      have hlec : a.lcm b ≤ z ^ 2 := by
        simpa only [pow_two] using (Nat.lcm_le_mul ha0 hb0).trans (Nat.mul_le_mul ha hb)
      have hneq : d ≠ a.lcm b := ne_of_gt (hlec.trans_lt h)
      simp only [hneq, if_false]
    · simp [s.optimalWeights_eq_zero_of_lt (not_le.mp hb)]
  · simp [s.optimalWeights_eq_zero_of_lt (not_le.mp ha)]

theorem siftedSum_le_optimal {z : ℕ} (hz : 1 ≤ z)
    (hν : ∀ d, d ∣ s.prodPrimes → (d : ℝ)⁻¹ ≤ s.nu d)
    (hrem : ∀ d, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
    s.siftedSum ≤ s.totalMass / s.selbergDenominator z + (z : ℝ) ^ 10 := by
  have hw (d : ℕ) (hd : d ∣ s.prodPrimes) : |s.optimalWeights z d| ≤ (z : ℝ) := by
    by_cases h : d ≤ z
    · have hdν := s.nu_pos_of_dvd_prodPrimes hd
      have hd0 : (0 : ℝ) < d := by
        exact_mod_cast pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero)
      have hmul : 1 ≤ s.nu d * (d : ℝ) := by
        exact (div_le_iff₀ hd0).mp (by simpa only [one_div] using hν d hd)
      have hinv : (s.nu d)⁻¹ ≤ (d : ℝ) := by
        simpa only [one_div] using (div_le_iff₀ hdν).mpr
          (by simpa only [mul_comm] using hmul : (1 : ℝ) ≤ (d : ℝ) * s.nu d)
      have hdz : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast h
      exact (s.abs_optimalWeights_le_inv_nu hz hd).trans (hinv.trans hdz)
    · rw [s.optimalWeights_eq_zero_of_lt (not_le.mp h), abs_zero]
      positivity
  have hsq (d : ℕ) (hd : d ∣ s.prodPrimes) (hle : d ≤ z ^ 2) :
      |lambdaSquared (s.optimalWeights z) d| ≤ (z : ℝ) ^ 6 := by
    unfold lambdaSquared
    have hdcard : (d.divisors.card : ℝ) ≤ (z : ℝ) ^ 2 := by
      exact_mod_cast (Nat.card_divisors_le_self d).trans hle
    have hrow (a : ℕ) (ha : a ∈ d.divisors) :
        |∑ b ∈ d.divisors, if d = a.lcm b then
            s.optimalWeights z a * s.optimalWeights z b else 0| ≤ (z : ℝ) ^ 4 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ _b ∈ d.divisors, (z : ℝ) ^ 2 := by
          refine sum_le_sum fun b hb => ?_
          split_ifs
          · rw [abs_mul, pow_two]
            exact mul_le_mul (hw a ((dvd_of_mem_divisors ha).trans hd))
              (hw b ((dvd_of_mem_divisors hb).trans hd)) (abs_nonneg _) (by positivity)
          · rw [abs_zero]
            positivity
        _ ≤ (z : ℝ) ^ 4 := by
          rw [sum_const, nsmul_eq_mul]
          calc
            _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hdcard (by positivity)
            _ = _ := by ring
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _a ∈ d.divisors, (z : ℝ) ^ 4 := sum_le_sum hrow
      _ ≤ (z : ℝ) ^ 6 := by
        rw [sum_const, nsmul_eq_mul]
        calc
          _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_right hdcard (by positivity)
          _ = _ := by ring
  have herr : s.errSum (lambdaSquared (s.optimalWeights z)) ≤ (z : ℝ) ^ 10 := by
    classical
    let D := s.prodPrimes.divisors.filter fun d => d ≤ z ^ 2
    have hD : D.card ≤ z ^ 2 := by
      have hsub : D ⊆ Icc 1 (z ^ 2) := by
        intro d hd
        have ⟨hm, hb⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨pos_of_dvd_of_pos (dvd_of_mem_divisors hm)
          (Nat.pos_of_ne_zero s.prodPrimes_ne_zero), hb⟩
      simpa using card_le_card hsub
    calc
      _ = ∑ d ∈ D, |lambdaSquared (s.optimalWeights z) d| * |s.rem d| := by
        unfold errSum D
        rw [sum_filter]
        refine sum_congr rfl fun d _ => ?_
        split_ifs with h
        · rfl
        · simp [s.optimal_lambdaSquared_eq_zero_of_lt (not_le.mp h)]
      _ ≤ ∑ _d ∈ D, (z : ℝ) ^ 8 := by
        refine sum_le_sum fun d hd => ?_
        have ⟨hm, hb⟩ := mem_filter.mp hd
        calc
          _ ≤ (z : ℝ) ^ 6 * (z : ℝ) ^ 2 :=
            mul_le_mul (hsq d (dvd_of_mem_divisors hm) hb)
              ((hrem d (dvd_of_mem_divisors hm)).trans (by exact_mod_cast hb))
              (abs_nonneg _) (by positivity)
          _ = _ := by ring
      _ ≤ (z : ℝ) ^ 10 := by
        rw [sum_const, nsmul_eq_mul]
        calc
          _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 8 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (by positivity)
          _ = _ := by ring
  calc
    _ ≤ s.totalMass * s.mainSum (lambdaSquared (s.optimalWeights z)) +
        s.errSum (lambdaSquared (s.optimalWeights z)) :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius _
        (upperMoebius_lambdaSquared _ (s.optimalWeights_one hz))
    _ ≤ _ := by
      rw [s.optimalWeights_mainSum hz, ← div_eq_mul_inv]
      exact add_le_add le_rfl herr


end BoundingSieve

end

section

-- Local congruences for the quadratic polynomial in the sequence A069004.

namespace OeisA69004

open Finset

theorem a_eq_card_prime_values (n : ℕ) :
    a n = ((Ico 1 n).filter fun s => (n ^ 2 + s ^ 2).Prime).card := by
  unfold a
  exact sum_boole _ _

theorem not_dvd_prime_value {p n s : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (hval : (n ^ 2 + s ^ 2).Prime) : ¬ p ∣ n ^ 2 + s ^ 2 := by
  intro h
  rcases (Nat.dvd_prime hval).mp h with h₁ | h₂
  · exact hp.ne_one h₁
  · have hn : 2 ≤ n := hp.two_le.trans hpn
    have hnn : n < n ^ 2 := by
      have := Nat.mul_le_mul_right n hn
      nlinarith
    omega

theorem root_iff_zero_of_dvd {p n : ℕ} [Fact p.Prime] (hpn : p ∣ n) (x : ZMod p) :
    (n : ZMod p) ^ 2 + x ^ 2 = 0 ↔ x = 0 := by
  rw [(ZMod.natCast_eq_zero_iff n p).mpr hpn]
  simp [pow_eq_zero_iff]

theorem exists_root_pair_of_one_mod_four {p n : ℕ} [Fact p.Prime]
    (hp : p % 4 = 1) (hn : ¬ p ∣ n) :
    ∃ y : ZMod p, y ≠ -y ∧ ∀ x : ZMod p,
      (n : ZMod p) ^ 2 + x ^ 2 = 0 ↔ x = y ∨ x = -y := by
  have hp' : p.Prime := Fact.out
  have hn' : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n p).mp h)
  have hs : IsSquare (-1 : ZMod p) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨r, hr⟩ := hs
  have hr' : r ^ 2 = -1 := by rw [pow_two, ← hr]
  have hroot : ((n : ZMod p) * r) ^ 2 = -((n : ZMod p) ^ 2) := by
    rw [mul_pow, hr', mul_neg, mul_one]
  have hr0 : (n : ZMod p) * r ≠ 0 := by
    refine mul_ne_zero hn' ?_
    intro h
    simp [h] at hr'
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    have := hp'.two_le
    omega
  refine ⟨(n : ZMod p) * r, ?_, fun x => ?_⟩
  · intro heq
    have hzero : (2 : ZMod p) * ((n : ZMod p) * r) = 0 := by
      rw [two_mul]
      nth_rw 1 [heq]
      exact neg_add_cancel _
    exact (mul_ne_zero htwo hr0) hzero
  · rw [add_comm, ← eq_neg_iff_add_eq_zero, ← hroot, sq_eq_sq_iff_eq_or_eq_neg]

theorem disproof_of_counterexample {n : ℕ} (hn : 1 < n)
    (h : 5 * a n < Nat.primeCounting n) :
    ¬ (type_of% @conjecture2.variants.without_upper_bound) := by
  intro hc
  exact (not_le_of_gt h) (hc.1 n hn)


end OeisA69004

end

section

-- Uniform counting bounds for a union of residue classes.

namespace OeisA69004

open Finset

def residueCount (M d : ℕ) (R : Finset ℕ) : ℕ :=
  ((range M).filter fun t => t % d ∈ R).card

theorem residueCount_lower {M d : ℕ} {R : Finset ℕ} (hR : R ⊆ range d) :
    R.card * (M / d) ≤ residueCount M d R := by
  rw [residueCount, ← card_range (M / d), ← card_product]
  refine card_le_card_of_injOn (fun a : ℕ × ℕ => a.1 + d * a.2) ?_ ?_
  · rintro ⟨r, k⟩ ha
    have hr := mem_range.mp (hR (mem_product.mp ha).1)
    have hk := mem_range.mp (mem_product.mp ha).2
    have he : (r + d * k) % d = r := by simp [Nat.mod_eq_of_lt hr]
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    swap
    · change (r + d * k) % d ∈ R
      rw [he]
      exact (mem_product.mp ha).1
    calc
      r + d * k < d + d * k := Nat.add_lt_add_right hr _
      _ = d * (k + 1) := by ring
      _ ≤ d * (M / d) := Nat.mul_le_mul_left d (by omega)
      _ ≤ M := Nat.mul_div_le M d
  · rintro ⟨r, k⟩ ha ⟨u, l⟩ hb he
    have hr := mem_range.mp (hR (mem_product.mp ha).1)
    have hu := mem_range.mp (hR (mem_product.mp hb).1)
    have hru := congrArg (fun z : ℕ => z % d) he
    simp [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hu] at hru
    have hd : 0 < d := by omega
    change r + d * k = u + d * l at he
    have hkl : k = l := by
      apply Nat.eq_of_mul_eq_mul_left hd
      omega
    exact Prod.ext hru hkl

theorem residueCount_upper {M d : ℕ} {R : Finset ℕ} :
    residueCount M d R ≤ R.card * (M / d + 1) := by
  rw [residueCount, ← card_range (M / d + 1), ← card_product]
  refine card_le_card_of_injOn (fun t : ℕ => (t % d, t / d)) ?_ ?_
  · intro t ht
    obtain ⟨ht, hr⟩ := mem_filter.mp ht
    have ht' := (mem_range.mp ht).le
    exact mem_product.mpr ⟨hr, mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ht'))⟩
  · intro t _ u _ he
    have hmod := congrArg Prod.fst he
    have hdiv := congrArg Prod.snd he
    change t % d = u % d at hmod
    change t / d = u / d at hdiv
    calc
      t = t % d + d * (t / d) := (Nat.mod_add_div t d).symm
      _ = u % d + d * (u / d) := by rw [hmod, hdiv]
      _ = u := Nat.mod_add_div u d

theorem residueCount_error {M d : ℕ} {R : Finset ℕ} (hd : 0 < d) (hR : R ⊆ range d) :
    |(residueCount M d R : ℝ) - (R.card : ℝ) * M / d| ≤ R.card := by
  have hlow : (R.card : ℝ) * (↑(M / d) : ℝ) ≤ (residueCount M d R : ℝ) := by
    exact_mod_cast residueCount_lower (M := M) hR
  have hhigh : (residueCount M d R : ℝ) ≤ (R.card : ℝ) * (↑(M / d) + 1 : ℝ) := by
    exact_mod_cast residueCount_upper (M := M) (d := d) (R := R)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : (↑(M / d) : ℝ) ≤ (M : ℝ) / d := by
    apply (le_div_iff₀ hd').mpr
    exact_mod_cast Nat.div_mul_le_self M d
  have hquot' : (M : ℝ) / d ≤ (↑(M / d) + 1 : ℝ) := by
    apply (div_le_iff₀ hd').mpr
    exact_mod_cast (Nat.lt_mul_div_succ M hd).le.trans_eq (Nat.mul_comm d (M / d + 1))
  have hcard : (0 : ℝ) ≤ R.card := by positivity
  have hl := mul_le_mul_of_nonneg_left hquot hcard
  have hu := mul_le_mul_of_nonneg_left hquot' hcard
  rw [mul_div_assoc, abs_le]
  constructor <;> nlinarith


end OeisA69004

end

section

-- Counting roots of the norm polynomial modulo coprime products.

namespace OeisA69004

open Finset

def normRoots (n d : ℕ) : Finset ℕ :=
  (range d).filter fun r => d ∣ n ^ 2 + r ^ 2

theorem normRoots_subset (n d : ℕ) : normRoots n d ⊆ range d :=
  filter_subset _ _

theorem dvd_norm_iff_mod_mem {n d s : ℕ} (hd : 0 < d) :
    d ∣ n ^ 2 + s ^ 2 ↔ s % d ∈ normRoots n d := by
  let : NeZero d := ⟨hd.ne'⟩
  rw [normRoots, mem_filter]
  simp only [mem_range, Nat.mod_lt _ hd, true_and]
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_mod]

private def normRootEquiv (n d : ℕ) [NeZero d] :
    {r // r ∈ normRoots n d} ≃ {x : ZMod d // (n : ZMod d) ^ 2 + x ^ 2 = 0} where
  toFun r := ⟨(r.1 : ZMod d), by
    have h := (mem_filter.mp r.2).2
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr h⟩
  invFun x := ⟨x.1.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt x.1), by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    simpa only [ZMod.natCast_zmod_val] using x.2⟩⟩
  left_inv r := Subtype.ext (by
    change (r.1 : ZMod d).val = r.1
    exact ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp r.2).1))
  right_inv x := Subtype.ext (ZMod.natCast_zmod_val x.1)

theorem normRoots_card_mul (n : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.Coprime b) : (normRoots n (a * b)).card = (normRoots n a).card * (normRoots n b).card := by
  classical
  let : NeZero a := ⟨ha⟩
  let : NeZero b := ⟨hb⟩
  let : NeZero (a * b) := ⟨Nat.mul_ne_zero ha hb⟩
  let e := ZMod.chineseRemainder h
  let ep : {x : ZMod (a * b) // (n : ZMod (a * b)) ^ 2 + x ^ 2 = 0} ≃
      {y : ZMod a × ZMod b //
        (n : ZMod a) ^ 2 + y.1 ^ 2 = 0 ∧ (n : ZMod b) ^ 2 + y.2 ^ 2 = 0} :=
    e.toEquiv.subtypeEquiv fun x => by
      rw [← e.map_eq_zero_iff, map_add, map_pow, map_pow, map_natCast]
      exact Prod.mk_inj
  let E := (normRootEquiv n (a * b)).trans
    (ep.trans (Equiv.subtypeProdEquivProd.trans ((normRootEquiv n a).symm.prodCongr
      (normRootEquiv n b).symm)))
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_congr E

theorem normRoots_card_one (n : ℕ) : (normRoots n 1).card = 1 := by
  simp [normRoots]

theorem normRoots_card_of_dvd {n p : ℕ} [Fact p.Prime] (h : p ∣ n) :
    (normRoots n p).card = 1 := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let R : Finset (ZMod p) := {0}
  have E := (normRootEquiv n p).trans
    ((Equiv.refl (ZMod p)).subtypeEquiv (q := fun x => x ∈ R)
      (fun x => (root_iff_zero_of_dvd h x).trans (by simp [R])))
  have hcard : Fintype.card ↥(normRoots n p) = Fintype.card ↥R := Fintype.card_congr E
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  simpa [R] using hcard

theorem normRoots_card_of_one_mod_four {n p : ℕ} [Fact p.Prime] (h : p % 4 = 1)
    (hn : ¬ p ∣ n) : (normRoots n p).card = 2 := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨y, hy, hy'⟩ := exists_root_pair_of_one_mod_four h hn
  let R : Finset (ZMod p) := {y, -y}
  let E := (normRootEquiv n p).trans ((Equiv.refl (ZMod p)).subtypeEquiv (q := fun x => x ∈ R)
    (fun x => (hy' x).trans (by simp [R])))
  have hcard : Fintype.card ↥(normRoots n p) = Fintype.card ↥R := Fintype.card_congr E
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  simpa [R, hy] using hcard


end OeisA69004

end

section

-- Specialization of the finite Selberg upper bound to the norm polynomial.

namespace OeisA69004

open Finset Nat ArithmeticFunction

private theorem normRoots_card_prod (n : ℕ) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    (normRoots n (∏ p ∈ T, p)).card = ∏ p ∈ T, (normRoots n p).card := by
  induction T using Finset.induction_on with
  | empty => simp [normRoots_card_one]
  | @insert p T hp ih =>
    have hpp := hT p (mem_insert_self _ _)
    have hT' q (hq : q ∈ T) := hT q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp]
    rw [normRoots_card_mul n hpp.ne_zero
      (prod_ne_zero_iff.mpr fun q hq => (hT' q hq).ne_zero) ?_, ih hT']
    exact Coprime.prod_right fun q hq => hpp.coprime_iff_not_dvd.mpr
      fun hd => hp (((hT' q hq).dvd_iff_eq hpp.ne_one).mp hd ▸ hq)

noncomputable def normDensity (n : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p => ((normRoots n p).card : ℝ) / p

theorem normDensity_eq {n d : ℕ} (hd : Squarefree d) :
    normDensity n d = ((normRoots n d).card : ℝ) / d := by
  have hprod := prod_primeFactors_of_squarefree hd
  have hcard := normRoots_card_prod n d.primeFactors (fun _ hp => prime_of_mem_primeFactors hp)
  rw [hprod] at hcard
  rw [normDensity, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero, prod_div_distrib,
    ← Nat.cast_prod, ← Nat.cast_prod, hcard, hprod]

private theorem norm_injective (n : ℕ) : Function.Injective (fun s : ℕ => n ^ 2 + s ^ 2) :=
  (show StrictMono (fun s : ℕ => n ^ 2 + s ^ 2) from
    fun _ _ h => Nat.add_lt_add_left (Nat.pow_lt_pow_left h (by decide)) _).injective

noncomputable def normSieve (n P : ℕ) (hP : Squarefree P)
    (hρ : ∀ p, p.Prime → p ∣ P → 1 ≤ (normRoots n p).card ∧ (normRoots n p).card < p) :
    BoundingSieve where
  support := (range n).image fun s => n ^ 2 + s ^ 2
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := n
  nu := normDensity n
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp hpp := by
    rw [normDensity_eq hp.squarefree]
    exact div_pos (by exact_mod_cast Nat.lt_of_succ_le (hρ p hp hpp).1) (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime p hp hpp := by
    rw [normDensity_eq hp.squarefree, div_lt_one (by exact_mod_cast hp.pos)]
    exact_mod_cast (hρ p hp hpp).2

variable {n P : ℕ} {hP : Squarefree P}
variable {hρ : ∀ p, p.Prime → p ∣ P → 1 ≤ (normRoots n p).card ∧ (normRoots n p).card < p}

theorem normSieve_multSum {d : ℕ} (hd : 0 < d) :
    (normSieve n P hP hρ).multSum d = residueCount n d (normRoots n d) := by
  rw [BoundingSieve.multSum]
  change (∑ q ∈ (range n).image (fun s => n ^ 2 + s ^ 2),
      (if d ∣ q then (1 : ℝ) else 0)) = _
  rw [sum_image (norm_injective n).injOn]
  simp_rw [dvd_norm_iff_mod_mem hd]
  rw [residueCount, ← sum_boole]

theorem a_le_normSieve_siftedSum (hp : ∀ p, p.Prime → p ∣ P → p ≤ n) :
    (a n : ℝ) ≤ (normSieve n P hP hρ).siftedSum := by
  rw [BoundingSieve.siftedSum, a_eq_card_prime_values]
  change _ ≤ ∑ q ∈ (range n).image (fun s => n ^ 2 + s ^ 2),
    (if P.Coprime q then (1 : ℝ) else 0)
  rw [sum_image (norm_injective n).injOn, ← sum_boole]
  calc
    _ ≤ ∑ s ∈ Ico 1 n, (if P.Coprime (n ^ 2 + s ^ 2) then (1 : ℝ) else 0) := ?_
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  · refine sum_le_sum fun s hs => ?_
    split_ifs with hs' hcop
    · rfl
    · exfalso
      have hpd := not_not.mp ((hs'.coprime_iff_not_dvd).not.mp fun h => hcop h.symm)
      have hspos : 1 ≤ s := (mem_Ico.mp hs).1
      have hn : 1 < n := hspos.trans_lt (mem_Ico.mp hs).2
      have hnn : n < n ^ 2 + s ^ 2 := by nlinarith
      exact (not_le_of_gt hnn) (hp _ hs' hpd)
    · exact zero_le_one
    · exact le_rfl
  · intro s hs
    exact mem_range.mpr (mem_Ico.mp hs).2

theorem normSieve_rem {d : ℕ} (hd : d ∣ P) :
    |(normSieve n P hP hρ).rem d| ≤ (d : ℝ) := by
  have hd' : 0 < d := pos_of_dvd_of_pos hd (pos_of_ne_zero hP.ne_zero)
  rw [BoundingSieve.rem, normSieve_multSum hd']
  change |(residueCount n d (normRoots n d) : ℝ) - normDensity n d * n| ≤ d
  rw [normDensity_eq (hP.squarefree_of_dvd hd)]
  rw [div_mul_eq_mul_div]
  refine (residueCount_error hd' (normRoots_subset n d)).trans ?_
  exact_mod_cast (show (normRoots n d).card ≤ d by
    simpa using card_le_card (normRoots_subset n d))

theorem normSieve_nu_lower {d : ℕ} (hd : d ∣ P) :
    (d : ℝ)⁻¹ ≤ (normSieve n P hP hρ).nu d := by
  have hdf := hP.squarefree_of_dvd hd
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast pos_of_dvd_of_pos hd (pos_of_ne_zero hP.ne_zero)
  have hcard : 1 ≤ (normRoots n d).card := by
    have hprod := normRoots_card_prod n d.primeFactors (fun _ hp => prime_of_mem_primeFactors hp)
    rw [prod_primeFactors_of_squarefree hdf] at hprod
    rw [hprod]
    exact Finset.one_le_prod' fun p hp => (hρ p (prime_of_mem_primeFactors hp)
      ((dvd_of_mem_primeFactors hp).trans hd)).1
  change (d : ℝ)⁻¹ ≤ normDensity n d
  rw [normDensity_eq hdf, ← one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hd0.le

theorem a_le_selbergDenominator {z : ℕ} (hz : 1 ≤ z)
    (hp : ∀ p, p.Prime → p ∣ P → p ≤ n) :
    (a n : ℝ) ≤ (n : ℝ) / (normSieve n P hP hρ).selbergDenominator z + (z : ℝ) ^ 10 :=
  (a_le_normSieve_siftedSum (hP := hP) (hρ := hρ) hp).trans
    ((normSieve n P hP hρ).siftedSum_le_optimal hz
      (fun _ hd => normSieve_nu_lower (hρ := hρ) hd)
      (fun _ hd => normSieve_rem (hρ := hρ) hd))


end OeisA69004

end

section

-- A finite lower bound from the alternating real character modulo four.

namespace OeisA69004

open Finset

noncomputable def charFour (e : ℕ) : ℝ := ((ZMod.χ₄ (e : ZMod 4) : ℤ) : ℝ)

private theorem charFour_eq (e : ℕ) :
    charFour e = if e % 2 = 0 then 0 else if e % 4 = 1 then 1 else -1 := by
  rw [charFour, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

private theorem harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  unfold harmonic
  positivity

private theorem harmonic_mono_real : Monotone (fun n => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ, Rat.cast_add]
  exact le_add_of_nonneg_right (by positivity)

noncomputable def harmonicWeight (z e : ℕ) : ℝ := (harmonic (z / e) : ℝ) / e

private theorem harmonicWeight_nonneg (z e : ℕ) : 0 ≤ harmonicWeight z e :=
  div_nonneg (harmonic_nonneg_real _) (by positivity)

private theorem harmonicWeight_antitone_on_pos {z a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    harmonicWeight z b ≤ harmonicWeight z a := by
  unfold harmonicWeight
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact div_le_div_of_nonneg_right
    (harmonic_mono_real (Nat.div_le_div_left hab ha)) (by positivity) |>.trans
    (div_le_div_of_nonneg_left (harmonic_nonneg_real _) ha' hab')

private theorem harmonicWeight_vanish {z e : ℕ} (h : z < e) :
    harmonicWeight z e = 0 := by
  simp [harmonicWeight, Nat.div_eq_of_lt h]

private theorem charFour_blocks (f : ℕ → ℝ) (k : ℕ) :
    (∑ e ∈ range (4 * k), charFour e * f e) =
      ∑ j ∈ range k, (f (4 * j + 1) - f (4 * j + 3)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 4 * (k + 1) = (4 * k + 1) + 1 + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    have h0 : charFour (4 * k) = 0 := by rw [charFour_eq, if_pos (by omega)]
    have h1 : charFour (4 * k + 1) = 1 := by rw [charFour_eq, if_neg (by omega), if_pos (by omega)]
    have h2 : charFour (4 * k + 1 + 1) = 0 := by rw [charFour_eq, if_pos (by omega)]
    have h3 : charFour (4 * k + 1 + 1 + 1) = -1 := by
      rw [charFour_eq, if_neg (by omega), if_neg (by omega)]
    rw [h0, h1, h2, h3]
    rw [show 4 * k + 1 + 1 + 1 = 4 * k + 3 by omega]
    ring

theorem charFour_harmonic_lower (z : ℕ) :
    (2 : ℝ) / 3 * harmonic z ≤ ∑ e ∈ range (z + 1), charFour e * harmonicWeight z e := by
  classical
  have hpad : (∑ e ∈ range (z + 1), charFour e * harmonicWeight z e) =
      ∑ e ∈ range (4 * (z + 1)), charFour e * harmonicWeight z e := by
    apply sum_subset
    · exact range_mono (by omega)
    · intro e _ he
      rw [harmonicWeight_vanish (show z < e by simpa using he), mul_zero]
  rw [hpad, charFour_blocks, sum_range_succ']
  have htail : 0 ≤ ∑ i ∈ range z,
      (harmonicWeight z (4 * (i + 1) + 1) - harmonicWeight z (4 * (i + 1) + 3)) :=
    sum_nonneg fun i _ => sub_nonneg.mpr
      (harmonicWeight_antitone_on_pos (by omega) (by omega))
  have h3 : harmonicWeight z 3 ≤ (harmonic z : ℝ) / 3 := by
    exact div_le_div_of_nonneg_right
      (harmonic_mono_real (Nat.div_le_self _ _)) (by norm_num)
  have h1 : harmonicWeight z 1 = (harmonic z : ℝ) := by simp [harmonicWeight]
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [h1]
  linarith


end OeisA69004

end

section

-- Rearranging the finite divisor sum that controls the sieve denominator.

namespace OeisA69004

open Finset Nat

noncomputable def normDivisorCoefficient (m : ℕ) : ℝ :=
  ∑ e ∈ m.divisors, charFour e

theorem normDivisorCoefficient_harmonic (z : ℕ) :
    (∑ m ∈ Icc 1 z, normDivisorCoefficient m / (m : ℝ)) =
      ∑ e ∈ range (z + 1), charFour e * harmonicWeight z e := by
  classical
  simp only [normDivisorCoefficient, harmonicWeight, harmonic, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, mul_sum, sum_mul]
  rw [sum_sigma', sum_sigma']
  refine sum_bij (fun a _ => ⟨a.2, a.1 / a.2 - 1⟩) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hm, he⟩ := mem_sigma.mp ha
    obtain ⟨hm1, hmz⟩ := mem_Icc.mp hm
    obtain ⟨hd, hm0⟩ := mem_divisors.mp he
    have he0 := pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm0)
    have hez := (le_of_dvd (Nat.pos_of_ne_zero hm0) hd).trans hmz
    have hq := le_div_iff_mul_le he0 |>.mpr
      (show (a.1 / a.2) * a.2 ≤ z from (Nat.div_mul_cancel hd).le.trans hmz)
    have hq0 := Nat.div_pos (le_of_dvd (Nat.pos_of_ne_zero hm0) hd) he0
    refine mem_sigma.mpr ⟨?_, ?_⟩
    · change a.2 ∈ range (z + 1)
      exact mem_range.mpr (by omega)
    · change a.1 / a.2 - 1 ∈ range (z / a.2)
      exact mem_range.mpr (by omega)
  · intro a ha b hb heq
    obtain ⟨had, ha0⟩ := mem_divisors.mp (mem_sigma.mp ha).2
    obtain ⟨hbd, hb0⟩ := mem_divisors.mp (mem_sigma.mp hb).2
    have hav := le_of_dvd (Nat.pos_of_ne_zero ha0) had
    have hbv := le_of_dvd (Nat.pos_of_ne_zero hb0) hbd
    have ha2 := pos_of_dvd_of_pos had (Nat.pos_of_ne_zero ha0)
    have hb2 := pos_of_dvd_of_pos hbd (Nat.pos_of_ne_zero hb0)
    have haq := Nat.div_pos hav ha2
    have hbq := Nat.div_pos hbv hb2
    have h₂ : a.2 = b.2 := congrArg Sigma.fst heq
    have hh := Sigma.mk.inj_iff.mp heq
    have hq : a.1 / a.2 = b.1 / b.2 := by
      have h := eq_of_heq hh.2
      omega
    cases a with | mk am ae =>
    cases b with | mk bm be =>
    change ae = be at h₂
    subst be
    have hm : am = bm := (Nat.div_mul_cancel had).symm.trans (by rw [hq, Nat.div_mul_cancel hbd])
    subst bm
    rfl
  · intro b hb
    obtain ⟨he, hk⟩ := mem_sigma.mp hb
    have hk' := mem_range.mp hk
    have he0 : 0 < b.1 := by
      by_contra! h
      have hz : b.1 = 0 := by omega
      simp [hz] at hk'
    have hm0 := Nat.mul_pos (Nat.succ_pos b.2) he0
    have hmz := (le_div_iff_mul_le he0).mp (Nat.succ_le_of_lt hk')
    refine ⟨⟨(b.2 + 1) * b.1, b.1⟩, mem_sigma.mpr
      ⟨mem_Icc.mpr ⟨hm0, hmz⟩, mem_divisors.mpr ⟨dvd_mul_left _ _, hm0.ne'⟩⟩, ?_⟩
    simp [Nat.mul_div_cancel _ he0]
  · intro a ha
    obtain ⟨hd, hm0⟩ := mem_divisors.mp (mem_sigma.mp ha).2
    have hm := Nat.pos_of_ne_zero hm0
    have he := pos_of_dvd_of_pos hd hm
    have hq := Nat.div_pos (le_of_dvd hm hd) he
    have hq' : a.1 / a.2 - 1 + 1 = a.1 / a.2 := by omega
    have hmul : ((a.1 / a.2 : ℕ) : ℝ) * (a.2 : ℝ) = (a.1 : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd
    rw [hq', ← hmul, mul_inv]

theorem normDivisorCoefficient_lower (z : ℕ) :
    (2 : ℝ) / 3 * harmonic z ≤ ∑ m ∈ Icc 1 z, normDivisorCoefficient m / (m : ℝ) := by
  rw [normDivisorCoefficient_harmonic]
  exact charFour_harmonic_lower z


end OeisA69004

end

section

-- The local coefficient at each prime power of the norm divisor sum.

namespace OeisA69004

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta

private theorem charFour_mul (a b : ℕ) : charFour (a * b) = charFour a * charFour b := by
  unfold charFour
  rw [Nat.cast_mul, map_mul, Int.cast_mul]

private theorem charFour_pow (a k : ℕ) : charFour (a ^ k) = charFour a ^ k := by
  unfold charFour
  rw [Nat.cast_pow, map_pow, Int.cast_pow]

private noncomputable def charFourArithmetic : ArithmeticFunction ℝ where
  toFun := charFour
  map_zero' := by norm_num [charFour, ZMod.χ₄]

private theorem charFourArithmetic_mult : charFourArithmetic.IsMultiplicative :=
  ⟨by norm_num [charFourArithmetic, charFour], fun {a b} _ => charFour_mul a b⟩

private noncomputable def normCoefficients : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * charFourArithmetic

private theorem normCoefficients_apply (m : ℕ) : normCoefficients m = normDivisorCoefficient m := by
  unfold normCoefficients normDivisorCoefficient
  rw [coe_zeta_mul_apply]
  rfl

private theorem normCoefficients_mult : normCoefficients.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul charFourArithmetic_mult

theorem normDivisorCoefficient_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    normDivisorCoefficient (p ^ k) = ∑ j ∈ range (k + 1), charFour p ^ j := by
  unfold normDivisorCoefficient
  rw [sum_divisors_prime_pow hp]
  simp_rw [charFour_pow]

theorem normDivisorCoefficient_two (k : ℕ) : normDivisorCoefficient (2 ^ k) = 1 := by
  rw [normDivisorCoefficient_pow prime_two]
  have hz : charFour 2 = 0 := by norm_num [charFour, ZMod.χ₄]
  simp only [hz]
  rw [sum_range_succ']
  simp [zero_pow (Nat.succ_ne_zero _)]

theorem normDivisorCoefficient_one_mod_four {p : ℕ} (hp : p.Prime)
    (h : p % 4 = 1) (k : ℕ) : normDivisorCoefficient (p ^ k) = (k : ℝ) + 1 := by
  rw [normDivisorCoefficient_pow hp]
  have h' : charFour p = 1 := by
    unfold charFour
    rw [ZMod.χ₄_nat_one_mod_four h]
    norm_num
  simp [h']

theorem normDivisorCoefficient_three_mod_four {p : ℕ} (hp : p.Prime)
    (h : p % 4 = 3) (k : ℕ) : normDivisorCoefficient (p ^ k) = if Even k then 1 else 0 := by
  rw [normDivisorCoefficient_pow hp]
  have h' : charFour p = -1 := by
    unfold charFour
    rw [ZMod.χ₄_nat_three_mod_four h]
    norm_num
  simp only [h', ← Fin.sum_univ_eq_sum_range, Fin.sum_neg_one_pow, Nat.even_add_one, ite_not]

theorem normDivisorCoefficient_factorization {n : ℕ} (hn : n ≠ 0) :
    normDivisorCoefficient n =
      ∏ p ∈ n.primeFactors, normDivisorCoefficient (p ^ n.factorization p) := by
  simp_rw [← normCoefficients_apply]
  have hcop : (n.primeFactors : Set ℕ).Pairwise
      (Function.onFun Coprime (fun p => p ^ n.factorization p)) := by
    intro p hp q hq hne
    exact ((coprime_primes (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq)).mpr
      hne).pow _ _
  calc
    _ = normCoefficients (∏ p ∈ n.primeFactors, p ^ n.factorization p) :=
      congrArg (fun n => normCoefficients n) (prod_primeFactors_pow_factorization hn)
    _ = _ := normCoefficients_mult.map_prod _ _ hcop

theorem normDivisorCoefficient_nonneg (n : ℕ) : 0 ≤ normDivisorCoefficient n := by
  by_cases h : n = 0
  · simp [h, normDivisorCoefficient]
  rw [normDivisorCoefficient_factorization h]
  apply prod_nonneg
  intro p hp
  have hprime := prime_of_mem_primeFactors hp
  rcases hprime.eq_two_or_odd with rfl | hodd
  · rw [normDivisorCoefficient_two]
    positivity
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hmod with hmod | hmod
  · rw [normDivisorCoefficient_one_mod_four hprime hmod]
    positivity
  · rw [normDivisorCoefficient_three_mod_four hprime hmod]
    split_ifs <;> positivity


end OeisA69004

end

section

-- Finite geometric and telescoping product bounds for residue sieves.

namespace OeisA69004

open Finset

theorem finite_geometric_upper {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) (N : ℕ) :
    (∑ k ∈ range N, r ^ k) ≤ (1 - r)⁻¹ := by
  rw [← tsum_geometric_of_lt_one h₀ h₁]
  exact (summable_geometric_of_lt_one h₀ h₁).sum_le_tsum _ (fun k _ => pow_nonneg h₀ k)

theorem finite_geometric_succ_upper {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) (N : ℕ) :
    (∑ k ∈ range N, r ^ (k + 1)) ≤ r * (1 - r)⁻¹ := by
  simp_rw [pow_succ']
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (finite_geometric_upper h₀ h₁ N) h₀

theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    omega

noncomputable def squareEuler (p : ℕ) : ℝ := (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹

theorem squareEuler_one_le {p : ℕ} (hp : 2 ≤ p) : 1 ≤ squareEuler p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp'
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  unfold squareEuler
  rw [← one_div]
  apply (le_div_iff₀ (by nlinarith)).mpr
  nlinarith [sq_nonneg ((p : ℝ)⁻¹)]

private theorem squareEuler_succ (n : ℕ) :
    squareEuler (n + 2) = ((n : ℝ) + 2)^2 / (((n : ℝ) + 1) * ((n : ℝ) + 3)) := by
  have h0 : (0 : ℝ) ≤ n := by positivity
  have ha : (n : ℝ) + 1 ≠ 0 := by linarith
  have hb : (n : ℝ) + 2 ≠ 0 := by linarith
  have hc : (n : ℝ) + 3 ≠ 0 := by linarith
  have hd : ((n : ℝ) + 2)^2 - 1 ≠ 0 := by nlinarith
  unfold squareEuler
  push_cast
  field_simp
  ring

theorem squareEuler_range (N : ℕ) :
    (∏ p ∈ range N, squareEuler (p + 2)) = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num
  | succ n ih =>
    rw [prod_range_succ, ih, squareEuler_succ]
    push_cast
    have h0 : (0 : ℝ) ≤ n := by positivity
    have ha : (n : ℝ) + 1 ≠ 0 := by linarith
    have hb : (n : ℝ) + 2 ≠ 0 := by linarith
    have hc : (n : ℝ) + 3 ≠ 0 := by linarith
    field_simp
    ring

theorem squareEuler_prod_le (T : Finset ℕ) {z : ℕ} (hT : T ⊆ Icc 2 z) :
    (∏ p ∈ T, squareEuler p) ≤ 2 := by
  classical
  let R : Finset ℕ := (range z).image fun p => p + 2
  have hTR : T ⊆ R := by
    intro p hp
    have ⟨hp2, hpz⟩ := mem_Icc.mp (hT hp)
    exact mem_image.mpr ⟨p - 2, mem_range.mpr (by omega), by omega⟩
  calc
    _ ≤ ∏ p ∈ R, squareEuler p :=
      prod_le_prod_of_subset_of_one_le hTR
        (fun p hp => zero_le_one.trans
          (squareEuler_one_le ((mem_Icc.mp (hT hp)).1))) (fun p hp _ => by
        obtain ⟨q, _, rfl⟩ := mem_image.mp hp
        exact squareEuler_one_le (by omega))
    _ = 2 * ((z : ℝ) + 1) / ((z : ℝ) + 2) := by
      dsimp [R]
      rw [prod_image (fun _ _ _ _ h => by omega), squareEuler_range]
    _ ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith


end OeisA69004

end

section

-- Bounding the prime factors of the truncated Euler expansion.

namespace OeisA69004

open Finset Nat

noncomputable def normPrimeWeight (p k : ℕ) : ℝ :=
  normDivisorCoefficient (p ^ k) / (p : ℝ) ^ k

theorem normPrimeWeight_nonneg (p k : ℕ) : 0 ≤ normPrimeWeight p k :=
  div_nonneg (normDivisorCoefficient_nonneg _) (by positivity)

@[simp] theorem normPrimeWeight_zero (p : ℕ) : normPrimeWeight p 0 = 1 := by
  have h : normDivisorCoefficient 1 = 1 := by
    simpa only [pow_zero] using normDivisorCoefficient_two 0
  simp [normPrimeWeight, h]

theorem normPrimeWeight_two_sum (z : ℕ) :
    (∑ k ∈ range (z + 1), normPrimeWeight 2 k) ≤ 2 := by
  simpa [normPrimeWeight, normDivisorCoefficient_two, one_div, inv_pow] using
    sum_geometric_two_le (z + 1)

theorem normPrimeWeight_one_mod_four_sum {p : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 1) (z : ℕ) :
    (∑ k ∈ range z, normPrimeWeight p (k + 1)) ≤ 2 / ((p : ℝ) - 2) := by
  have hp' : (2 : ℝ) < p := by
    have := hp.two_le
    exact_mod_cast (show 2 < p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ (2 : ℝ) / p := by positivity
  have hr1 : (2 : ℝ) / p < 1 := (div_lt_one hp0).mpr hp'
  calc
    _ ≤ ∑ k ∈ range z, ((2 : ℝ) / p) ^ (k + 1) := by
      refine sum_le_sum fun k _ => ?_
      unfold normPrimeWeight
      rw [normDivisorCoefficient_one_mod_four hp hmod, div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast succ_le_two_pow (k + 1)
    _ ≤ (2 / (p : ℝ)) * (1 - 2 / (p : ℝ))⁻¹ :=
      finite_geometric_succ_upper hr0 hr1 z
    _ = _ := by
      have hb : (p : ℝ) - 2 ≠ 0 := by linarith
      have hc : 1 - 2 / (p : ℝ) ≠ 0 := by linarith
      field_simp

theorem normPrimeWeight_three_mod_four_sum {p : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 3) (z : ℕ) :
    (∑ k ∈ range (z + 1), normPrimeWeight p (2 * k)) ≤ squareEuler p := by
  have hr : ((p : ℝ)⁻¹)^2 < 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
    have hh : 0 < (p : ℝ)⁻¹ := by positivity
    nlinarith
  have heq (k : ℕ) : normPrimeWeight p (2 * k) = (((p : ℝ)⁻¹)^2)^k := by
    have he : Even (2 * k) := ⟨k, by omega⟩
    rw [normPrimeWeight, normDivisorCoefficient_three_mod_four hp hmod, if_pos he,
      one_div, ← inv_pow, pow_mul]
  simp_rw [heq]
  exact finite_geometric_upper (by positivity) hr (z + 1)

theorem normPrimeWeight_factorization {n : ℕ} (hn : n ≠ 0) :
    normDivisorCoefficient n / (n : ℝ) =
      ∏ p ∈ n.primeFactors, normPrimeWeight p (n.factorization p) := by
  simp only [normPrimeWeight, prod_div_distrib, ← Nat.cast_pow, ← Nat.cast_prod]
  rw [← normDivisorCoefficient_factorization hn, ← prod_primeFactors_pow_factorization hn]


end OeisA69004

end

section

-- Grouping the positive norm coefficients by their prime factors in the class 1 modulo 4.

namespace OeisA69004

open Finset Nat

def intervalPrimes (z : ℕ) : Finset ℕ := (Icc 2 z).filter Nat.Prime

def firstClassSupport (m : ℕ) : Finset ℕ := m.primeFactors.filter (fun p => p % 4 = 1)

private def exponentBox (z : ℕ) (D : Finset ℕ) (p : ℕ) : Finset ℕ :=
  if p = 2 then range (z + 1)
  else if p % 4 = 1 then
    if p ∈ D then (range z).image Nat.succ else {0}
  else (range (z + 1)).image (fun k => 2 * k)

private theorem primeFactors_subset_intervalPrimes {m z : ℕ} (hm : 0 < m) (hmz : m ≤ z) :
    m.primeFactors ⊆ intervalPrimes z := by
  intro p hp
  have h := prime_of_mem_primeFactors hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h.two_le, (le_of_dvd hm (dvd_of_mem_primeFactors hp)).trans hmz⟩, h⟩

private theorem factorization_ne_zero_iff_mem {m p : ℕ} :
    m.factorization p ≠ 0 ↔ p ∈ m.primeFactors := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]

private theorem factorization_mem_exponentBox {m z p : ℕ} (hm : 0 < m) (hmz : m ≤ z)
    (hB : normDivisorCoefficient m ≠ 0) (hp : p ∈ intervalPrimes z) :
    m.factorization p ∈ exponentBox z (firstClassSupport m) p := by
  have hp' := (mem_filter.mp hp).2
  have he := (factorization_lt p hm.ne').trans_le hmz
  unfold exponentBox
  split_ifs with htwo hone hmem
  · exact mem_range.mpr (by omega)
  · have hmem' := (mem_filter.mp hmem).1
    have hpos : 0 < m.factorization p := by
      exact Nat.pos_of_ne_zero (factorization_ne_zero_iff_mem.mpr hmem')
    refine mem_image.mpr ⟨m.factorization p - 1, mem_range.mpr (by omega), ?_⟩
    omega
  · have hfalse : p ∉ m.primeFactors := fun h => hmem (mem_filter.mpr ⟨h, hone⟩)
    have heq : m.factorization p = 0 := by
      exact not_not.mp (fun h => hfalse (factorization_ne_zero_iff_mem.mp h))
    simp [heq]
  · have hodd : p % 2 = 1 := hp'.eq_two_or_odd.resolve_left htwo
    have hthree : p % 4 = 3 := by omega
    have hev : Even (m.factorization p) := by
      by_contra hnot
      have hne : m.factorization p ≠ 0 := fun h => hnot (by simp [h])
      have hmem' := factorization_ne_zero_iff_mem.mp hne
      apply hB
      rw [normDivisorCoefficient_factorization hm.ne']
      exact prod_eq_zero hmem' (by rw [normDivisorCoefficient_three_mod_four hp' hthree, if_neg hnot])
    obtain ⟨e, heq⟩ := hev
    exact mem_image.mpr ⟨e, mem_range.mpr (by omega), by omega⟩

private theorem normWeight_extend_product {m z : ℕ} (hm : 0 < m) (hmz : m ≤ z) :
    normDivisorCoefficient m / (m : ℝ) =
      ∏ p ∈ intervalPrimes z, normPrimeWeight p (m.factorization p) := by
  rw [normPrimeWeight_factorization hm.ne']
  refine prod_subset (primeFactors_subset_intervalPrimes hm hmz) ?_
  intro p _ hp
  have hzero : m.factorization p = 0 := by
    exact not_not.mp (fun h => hp (factorization_ne_zero_iff_mem.mp h))
  simp [hzero]

theorem coefficient_fiber_le_box (z : ℕ) (D : Finset ℕ) :
    (∑ m ∈ (Icc 1 z).filter (fun m => firstClassSupport m = D),
      normDivisorCoefficient m / (m : ℝ)) ≤
      ∏ p ∈ intervalPrimes z, ∑ k ∈ exponentBox z D p, normPrimeWeight p k := by
  classical
  let M := (Icc 1 z).filter (fun m => firstClassSupport m = D)
  let N := M.filter (fun m => normDivisorCoefficient m ≠ 0)
  have hn (m : ℕ) (hm : m ∈ N) :
      0 < m ∧ m ≤ z ∧ firstClassSupport m = D ∧ normDivisorCoefficient m ≠ 0 := by
    simpa [N, M, and_assoc, Nat.succ_le_iff] using hm
  have hzer :
      (∑ m ∈ N, normDivisorCoefficient m / (m : ℝ)) =
        ∑ m ∈ M, normDivisorCoefficient m / (m : ℝ) := by
    refine sum_subset (filter_subset _ _) fun m hm hnm => ?_
    have hz : normDivisorCoefficient m = 0 := by
      simpa only [N, mem_filter, hm, true_and, not_not] using hnm
    rw [hz, zero_div]
  rw [← show (∑ m ∈ N, _) = ∑ m ∈ M, _ from hzer]
  rw [prod_sum]
  let f := fun (m : ℕ) (p : ℕ) (_ : p ∈ intervalPrimes z) => m.factorization p
  have hf (m : ℕ) (hm : m ∈ N) :
      f m ∈ (intervalPrimes z).pi (exponentBox z D) := by
    obtain ⟨h1, h2, h3, h4⟩ := hn m hm
    refine mem_pi.mpr fun p hp => ?_
    rw [← h3]
    exact factorization_mem_exponentBox h1 h2 h4 hp
  have hfinj : Set.InjOn f N := by
    intro m hm l hl hml
    apply factorization_inj (hn m hm).1.ne' (hn l hl).1.ne'
    ext p
    by_cases hp : p ∈ intervalPrimes z
    · exact congrFun (congrFun hml p) hp
    · have hmp := fun h => hp (primeFactors_subset_intervalPrimes (hn m hm).1 (hn m hm).2.1 h)
      have hlp := fun h => hp (primeFactors_subset_intervalPrimes (hn l hl).1 (hn l hl).2.1 h)
      have hm0 : m.factorization p = 0 := by
        exact not_not.mp (fun h => hmp (factorization_ne_zero_iff_mem.mp h))
      have hl0 : l.factorization p = 0 := by
        exact not_not.mp (fun h => hlp (factorization_ne_zero_iff_mem.mp h))
      rw [hm0, hl0]
  calc
    _ = ∑ a ∈ N.image f, ∏ p ∈ (intervalPrimes z).attach, normPrimeWeight p.1 (a p.1 p.2) := by
      rw [sum_image hfinj]
      refine sum_congr rfl fun m hm => ?_
      simp only [f]
      exact (normWeight_extend_product (hn m hm).1 (hn m hm).2.1).trans
        (prod_attach (intervalPrimes z) (fun p => normPrimeWeight p (m.factorization p))).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun a ha => by obtain ⟨m, hm, rfl⟩ := mem_image.mp ha; exact hf m hm)
      (fun _ _ _ => prod_nonneg fun p _ => normPrimeWeight_nonneg _ _)

noncomputable def firstClassEuler (D : Finset ℕ) : ℝ :=
  ∏ p ∈ D, 2 / ((p : ℝ) - 2)

theorem coefficient_fiber_le_euler (z : ℕ) (D : Finset ℕ)
    (hD : D ⊆ (intervalPrimes z).filter fun p => p % 4 = 1) :
    (∑ m ∈ (Icc 1 z).filter (fun m => firstClassSupport m = D),
      normDivisorCoefficient m / (m : ℝ)) ≤ 4 * firstClassEuler D := by
  classical
  let T := intervalPrimes z
  let A := fun p : ℕ => if p = 2 then (2 : ℝ) else 1
  let B := fun p : ℕ => if p ∈ D then 2 / ((p : ℝ) - 2) else 1
  let C := fun p : ℕ => if p % 4 = 3 then squareEuler p else 1
  have hD' : D ⊆ T := fun p hp => (mem_filter.mp (hD hp)).1
  have hloc (p : ℕ) (hp : p ∈ T) :
      (∑ j ∈ exponentBox z D p, normPrimeWeight p j) ≤ A p * B p * C p := by
    have hpp := (mem_filter.mp hp).2
    by_cases h2 : p = 2
    · subst p
      have h2D : 2 ∉ D := by
        intro h
        have hmod := (mem_filter.mp (hD h)).2
        norm_num at hmod
      simpa [A, B, C, h2D, exponentBox] using normPrimeWeight_two_sum z
    by_cases h1 : p % 4 = 1
    · by_cases hmem : p ∈ D
      · simp only [A, B, C, exponentBox, h1, h2, hmem, ↓reduceIte, one_mul,
          if_neg (by decide : (1 : ℕ) ≠ 3), mul_one]
        rw [sum_image Nat.succ_injective.injOn]
        exact normPrimeWeight_one_mod_four_sum hpp h1 z
      · simp [A, B, C, exponentBox, h1, h2, hmem]
    · have h3 : p % 4 = 3 := by have := hpp.eq_two_or_odd.resolve_left h2; omega
      have hmem : p ∉ D := fun h => h1 (mem_filter.mp (hD h)).2
      simp only [A, B, C, exponentBox, h3, h2, hmem, ↓reduceIte, one_mul,
        if_neg (by decide : (3 : ℕ) ≠ 1)]
      rw [sum_image (fun _ _ _ _ h => by omega)]
      exact normPrimeWeight_three_mod_four_sum hpp h3 z
  have hA : (∏ p ∈ T, A p) ≤ 2 := by
    unfold A
    rw [← prod_filter]
    by_cases h : 2 ∈ T
    · have he : T.filter (· = 2) = {2} := by ext p; simp only [mem_filter, mem_singleton]; aesop
      simp [he]
    · have he : T.filter (· = 2) = ∅ := by ext p; simp only [mem_filter, notMem_empty, iff_false]; aesop
      simp [he]
  have hC : (∏ p ∈ T, C p) ≤ 2 := by
    unfold C
    rw [← prod_filter]
    exact squareEuler_prod_le _ (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).1)
  have hC0 : 0 ≤ ∏ p ∈ T, C p := prod_nonneg fun p hp => by
    unfold C
    split_ifs
    · exact zero_le_one.trans (squareEuler_one_le (mem_Icc.mp (mem_filter.mp hp).1).1)
    · positivity
  have hB : (∏ p ∈ T, B p) = firstClassEuler D := by
    unfold B firstClassEuler
    rw [← prod_filter]
    congr 1
    ext p
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hD' h, h⟩⟩
  have hD0 : 0 ≤ firstClassEuler D := by
    unfold firstClassEuler
    refine prod_nonneg fun p hp => ?_
    have hh := mem_filter.mp (hD hp)
    have h2 := (mem_filter.mp hh.1).2.two_le
    have h2' : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr h2'.le)
  calc
    _ ≤ _ := coefficient_fiber_le_box z D
    _ ≤ ∏ p ∈ T, A p * B p * C p :=
      prod_le_prod (fun _ _ => sum_nonneg fun _ _ => normPrimeWeight_nonneg _ _) hloc
    _ = (∏ p ∈ T, A p) * firstClassEuler D * (∏ p ∈ T, C p) := by
      rw [prod_mul_distrib, prod_mul_distrib, hB]
    _ ≤ _ := by
      have h4 : (∏ p ∈ T, A p) * (∏ p ∈ T, C p) ≤ 4 := by
        calc
          _ ≤ (2 : ℝ) * 2 := mul_le_mul hA hC hC0 (by norm_num)
          _ = 4 := by norm_num
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right h4 hD0


end OeisA69004

end

section

-- Finite prime sets and products for the local exclusion conditions.

namespace OeisA69004

open Finset Nat

def primeOneSet (z : ℕ) : Finset ℕ :=
  (intervalPrimes z).filter (fun p => p % 4 = 1)

def primeThreeSet (z : ℕ) : Finset ℕ :=
  (intervalPrimes z).filter (fun p => p % 4 = 3)

def primeProd (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

theorem squarefree_primeProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (primeProd P) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [primeProd]
  | @insert p P hp ih =>
    have hpp := hP p (mem_insert_self _ _)
    have hP' q (hq : q ∈ P) := hP q (mem_insert_of_mem hq)
    unfold primeProd
    rw [prod_insert hp, Nat.squarefree_mul_iff]
    exact ⟨Coprime.prod_right fun q hq =>
      (coprime_primes hpp (hP' q hq)).mpr (fun h => hp (h ▸ hq)),
      hpp.squarefree, ih hP'⟩

theorem exists_three_mod_four_prime_dvd {n : ℕ} (hn : n % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  classical
  by_contra h
  push Not at h
  have hn0 : n ≠ 0 := by omega
  have htwo : ¬ 2 ∣ n := by omega
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) : p % 4 = 1 := by
    have hprime := prime_of_mem_primeFactors hp
    have hd := dvd_of_mem_primeFactors hp
    have hne : p ≠ 2 := fun hp => htwo (hp ▸ hd)
    have hodd := hprime.eq_two_or_odd.resolve_left hne
    have hh := h p hprime hd
    omega
  have hf (p : ℕ) (hp : p ∈ n.primeFactors) : (p : ZMod 4) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hfactor p hp
  have hcast : (n : ZMod 4) = 1 := by
    calc
      _ = (↑(∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ZMod 4) :=
        congrArg (fun m : ℕ => (m : ZMod 4)) (prod_primeFactors_pow_factorization hn0)
      _ = _ := by
        push_cast
        apply prod_eq_one
        intro p hp
        rw [hf p hp, one_pow]
  have hno : n % 4 = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hcast
    exact hcast
  omega

theorem exists_primeThreeSet_dvd {n : ℕ} (hn : n % 4 = 3) :
    ∃ p ∈ primeThreeSet n, p ∣ n := by
  obtain ⟨p, hp, hpn, h3⟩ := exists_three_mod_four_prime_dvd hn
  have hn0 : 0 < n := by omega
  exact ⟨p, mem_filter.mpr ⟨mem_filter.mpr
    ⟨mem_Icc.mpr ⟨hp.two_le, le_of_dvd hn0 hpn⟩, hp⟩, h3⟩, hpn⟩


end OeisA69004

end

section

-- The one-modulo-four part of the sieve denominator grows at least logarithmically.

namespace OeisA69004

open Finset Nat

def firstClassSupports (z : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 z).image firstClassSupport

theorem firstClassSupports_subset {D : Finset ℕ} {z : ℕ} (hD : D ∈ firstClassSupports z) :
    D ⊆ primeOneSet z := by
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hD
  obtain ⟨hm1, hmz⟩ := mem_Icc.mp hm
  intro p hp
  obtain ⟨hpm, hp1⟩ := mem_filter.mp hp
  have hpp := prime_of_mem_primeFactors hpm
  have hpz := (le_of_dvd hm1 (dvd_of_mem_primeFactors hpm)).trans hmz
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.two_le, hpz⟩, hpp⟩, hp1⟩

theorem firstClassSupports_prod_le {D : Finset ℕ} {z : ℕ} (hD : D ∈ firstClassSupports z) :
    primeProd D ≤ z := by
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hD
  obtain ⟨hm1, hmz⟩ := mem_Icc.mp hm
  have hsub : firstClassSupport m ⊆ m.primeFactors := filter_subset _ _
  have hdvd : primeProd (firstClassSupport m) ∣ m := by
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd m)
  exact (le_of_dvd hm1 hdvd).trans hmz

noncomputable def firstClassSum (z : ℕ) : ℝ :=
  ∑ D ∈ firstClassSupports z, firstClassEuler D

theorem harmonic_le_six_firstClassSum (z : ℕ) :
    (harmonic z : ℝ) / 6 ≤ firstClassSum z := by
  classical
  have h := normDivisorCoefficient_lower z
  have hsum : (∑ D ∈ firstClassSupports z,
       ∑ m ∈ (Icc 1 z).filter (fun m => firstClassSupport m = D),
         normDivisorCoefficient m / (m : ℝ)) =
      ∑ m ∈ Icc 1 z, normDivisorCoefficient m / (m : ℝ) :=
    sum_fiberwise_of_maps_to (fun m hm => mem_image_of_mem firstClassSupport hm) _
  rw [← hsum] at h
  have hu : (∑ D ∈ firstClassSupports z,
      ∑ m ∈ (Icc 1 z).filter (fun m => firstClassSupport m = D),
        normDivisorCoefficient m / (m : ℝ)) ≤ 4 * firstClassSum z := by
    rw [firstClassSum, mul_sum]
    exact sum_le_sum fun D hD => coefficient_fiber_le_euler z D (firstClassSupports_subset hD)
  linarith

theorem log_le_six_firstClassSum (z : ℕ) :
    Real.log ((z : ℝ) + 1) / 6 ≤ firstClassSum z := by
  have h := log_add_one_le_harmonic z
  push_cast at h
  exact (div_le_div_of_nonneg_right h (by norm_num)).trans (harmonic_le_six_firstClassSum z)


end OeisA69004

end

section

-- Finite counting for the reciprocal sum of primes in the class 3 modulo 4.

namespace OeisA69004

open Finset Nat Real

noncomputable def threeReciprocals (z : ℕ) : ℝ :=
  ∑ p ∈ primeThreeSet z, (p : ℝ)⁻¹

theorem primeThreeSet_mono : Monotone primeThreeSet := by
  intro a b hab p hp
  obtain ⟨hh, h3⟩ := mem_filter.mp hp
  obtain ⟨hI, hpp⟩ := mem_filter.mp hh
  exact mem_filter.mpr ⟨mem_filter.mpr
    ⟨mem_Icc.mpr ⟨(mem_Icc.mp hI).1, (mem_Icc.mp hI).2.trans hab⟩, hpp⟩, h3⟩

private theorem primeThreeSet_prime {z p : ℕ} (hp : p ∈ primeThreeSet z) : p.Prime :=
  (mem_filter.mp (mem_filter.mp hp).1).2

private theorem coprime_four_primeThreeProd (z : ℕ) :
    (4 : ℕ).Coprime (primeProd (primeThreeSet z)) := by
  unfold primeProd
  refine Coprime.prod_right fun p hp => Nat.Coprime.symm ?_
  have hprime := primeThreeSet_prime hp
  rw [hprime.coprime_iff_not_dvd]
  intro h
  have hle := le_of_dvd (by decide : 0 < 4) h
  have hp2 := hprime.two_le
  have hmod := (mem_filter.mp hp).2
  interval_cases p <;> omega

private theorem card_positiveMultiples_le (N p : ℕ) (hp0 : 0 < p) :
    (((Icc 1 N).filter fun j => p ∣ j).card : ℝ) ≤ (N : ℝ) / p := by
  have h : ((Icc 1 N).filter fun j => p ∣ j).card ≤ N / p := by
    calc
      _ ≤ (Icc 1 (N / p)).card := by
        refine card_le_card_of_injOn (fun n : ℕ => n / p) ?_ ?_
        · intro n hn
          obtain ⟨hnI, hdvd⟩ := mem_filter.mp hn
          have hn' := mem_Icc.mp hnI
          exact mem_Icc.mpr ⟨Nat.div_pos (le_of_dvd hn'.1 hdvd) hp0,
            Nat.div_le_div_right hn'.2⟩
        · intro a ha b hb he
          change a / p = b / p at he
          calc
            a = a / p * p := (Nat.div_mul_cancel (mem_filter.mp ha).2).symm
            _ = b / p * p := by rw [he]
            _ = b := Nat.div_mul_cancel (mem_filter.mp hb).2
      _ = _ := by simp
  have hreal : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ (by exact_mod_cast hp0)).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  exact (by exact_mod_cast h : (_ : ℝ) ≤ ((N / p : ℕ) : ℝ)).trans hreal

theorem totient_le_threeTail (z : ℕ) :
    let Q := primeProd (primeThreeSet z)
    (Q.totient : ℝ) ≤ (4 * (Q : ℝ)) *
      ∑ p ∈ primeThreeSet (max z (4 * Q)) \ primeThreeSet z, (p : ℝ)⁻¹ := by
  classical
  let Q := primeProd (primeThreeSet z)
  let T := primeThreeSet (max z (4 * Q)) \ primeThreeSet z
  let U := (range Q).filter fun r => Q.Coprime r
  let C := T.biUnion fun p => (Icc 1 (4 * Q)).filter (fun n => p ∣ n)
  have hQ : Q ≠ 0 := (squarefree_primeProd (fun p hp => primeThreeSet_prime hp)).ne_zero
  have hcop : (4 : ℕ).Coprime Q := coprime_four_primeThreeProd z
  have hUC : U.card ≤ C.card := by
    let f (r : ℕ) : ℕ := (Nat.chineseRemainder hcop 3 r).val
    refine card_le_card_of_injOn f ?_ ?_
    · intro r hr
      have hn : f r < 4 * Q := Nat.chineseRemainder_lt_mul hcop 3 r (by decide) hQ
      have h3 : f r % 4 = 3 := (Nat.chineseRemainder hcop 3 r).prop.1
      have hq := (Nat.chineseRemainder hcop 3 r).prop.2
      obtain ⟨p, hp, hpn⟩ := exists_primeThreeSet_dvd h3
      have hpprime := primeThreeSet_prime hp
      have hsub : p ∈ primeThreeSet (max z (4 * Q)) :=
        primeThreeSet_mono (hn.le.trans (le_max_right _ _)) hp
      have hnot : p ∉ primeThreeSet z := by
        intro hmem
        have hpQ : p ∣ Q := Finset.dvd_prod_of_mem id hmem
        have hmod := hq.of_dvd hpQ
        have hpr : p ∣ r := by
          apply Nat.dvd_of_mod_eq_zero
          change f r % p = r % p at hmod
          rw [← hmod]
          exact Nat.mod_eq_zero_of_dvd hpn
        exact (hpprime.coprime_iff_not_dvd.mp ((mem_filter.mp hr).2.of_dvd_left hpQ)) hpr
      exact mem_biUnion.mpr ⟨p, mem_sdiff.mpr ⟨hsub, hnot⟩,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hn.le⟩, hpn⟩⟩
    · intro a ha b hb h
      change f a = f b at h
      have ea := (Nat.chineseRemainder hcop 3 a).prop.2
      have eb := (Nat.chineseRemainder hcop 3 b).prop.2
      change f a ≡ a [MOD Q] at ea
      change f b ≡ b [MOD Q] at eb
      rw [h] at ea
      exact (ea.symm.trans eb).eq_of_lt_of_lt
        (mem_range.mp (mem_filter.mp ha).1) (mem_range.mp (mem_filter.mp hb).1)
  calc
    (Q.totient : ℝ) = (U.card : ℝ) := rfl
    _ ≤ (C.card : ℝ) := by exact_mod_cast hUC
    _ ≤ ∑ p ∈ T, (((Icc 1 (4 * Q)).filter fun n => p ∣ n).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ p ∈ T, ((4 : ℝ) * Q) * (p : ℝ)⁻¹ := by
      refine sum_le_sum fun p hp => ?_
      have hp0 := (primeThreeSet_prime (mem_sdiff.mp hp).1).pos
      simpa [div_eq_mul_inv] using card_positiveMultiples_le (4 * Q) p hp0
    _ = _ := (mul_sum _ _ _).symm


noncomputable def threeSurvival (z : ℕ) : ℝ :=
  ∏ p ∈ primeThreeSet z, (1 - (p : ℝ)⁻¹)

theorem threeSurvival_eq_totient (z : ℕ) :
    let Q := primeProd (primeThreeSet z)
    threeSurvival z = (Q.totient : ℝ) / Q := by
  let Q := primeProd (primeThreeSet z)
  have hQ : Q ≠ 0 := (squarefree_primeProd (fun p hp => primeThreeSet_prime hp)).ne_zero
  have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors Q)
  push_cast at hh
  have hpF : Q.primeFactors = primeThreeSet z := Nat.primeFactors_prod
    (fun p hp => primeThreeSet_prime hp)
  rw [hpF] at hh
  change threeSurvival z = (Q.totient : ℝ) / Q
  rw [hh, mul_div_cancel_left₀ _ (by exact_mod_cast hQ)]
  rfl

private theorem exp_neg_two_le_one_sub {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h₂ : 0 < 1 + 2 * x := by linarith
  calc
    Real.exp (-(2 * x)) = (Real.exp (2 * x))⁻¹ := Real.exp_neg _
    _ ≤ (1 + 2 * x)⁻¹ := inv_anti₀ h₂ (by
      simpa only [add_comm] using Real.add_one_le_exp (2 * x))
    _ ≤ 1 - x := by
      rw [← one_div, div_le_iff₀ h₂]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hx2)]

theorem threeSurvival_bounds (z : ℕ) :
    Real.exp (-(2 * threeReciprocals z)) ≤ threeSurvival z ∧
      threeSurvival z ≤ Real.exp (-threeReciprocals z) := by
  have hx (p : ℕ) (hp : p ∈ primeThreeSet z) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast (primeThreeSet_prime hp).two_le)
  unfold threeSurvival threeReciprocals
  constructor
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    exact prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun p hp => exp_neg_two_le_one_sub (by positivity) (hx p hp))
  · rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine prod_le_prod (fun p hp => by linarith [hx p hp]) fun p _ => ?_
    simpa only [neg_add_eq_sub] using Real.add_one_le_exp (-(p : ℝ)⁻¹)

theorem threeReciprocals_unbounded : ¬ BddAbove (Set.range threeReciprocals) := by
  intro hbounded
  let B := sSup (Set.range threeReciprocals)
  let δ := Real.exp (-(2 * B)) / 8
  have hδ : 0 < δ := by positivity
  obtain ⟨x, ⟨z, rfl⟩, hz⟩ :=
    exists_lt_of_lt_csSup (s := Set.range threeReciprocals)
      ⟨threeReciprocals 0, ⟨0, rfl⟩⟩ (show B - δ < B by linarith)
  let Q := primeProd (primeThreeSet z)
  have hQ : 0 < Q := Nat.pos_of_ne_zero
    (squarefree_primeProd (fun p hp => primeThreeSet_prime hp)).ne_zero
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  let W := max z (4 * Q)
  have hB (u : ℕ) : threeReciprocals u ≤ B := le_csSup hbounded ⟨u, rfl⟩
  have ht := sum_sdiff (f := fun p : ℕ => (p : ℝ)⁻¹)
    (primeThreeSet_mono (show z ≤ W from le_max_left _ _))
  change (∑ p ∈ primeThreeSet W \ primeThreeSet z, (p : ℝ)⁻¹) + threeReciprocals z =
    threeReciprocals W at ht
  have htail : (∑ p ∈ primeThreeSet W \ primeThreeSet z, (p : ℝ)⁻¹) < δ := by
    linarith [hB W]
  have hlow : Real.exp (-(2 * B)) ≤ threeSurvival z :=
    (Real.exp_le_exp.mpr (by linarith [hB z])).trans (threeSurvival_bounds z).1
  have hu : threeSurvival z ≤ 4 * ∑ p ∈ primeThreeSet W \ primeThreeSet z, (p : ℝ)⁻¹ := by
    rw [threeSurvival_eq_totient]
    change (Q.totient : ℝ) / Q ≤ 4 * ∑ p ∈ primeThreeSet W \ primeThreeSet z, (p : ℝ)⁻¹
    apply (div_le_iff₀ hQ').mpr
    calc
      _ ≤ (4 * (Q : ℝ)) * (∑ p ∈ primeThreeSet W \ primeThreeSet z, (p : ℝ)⁻¹) :=
        totient_le_threeTail z
      _ = _ := by ring
  have he := Real.exp_pos (-(2 * B))
  change _ < Real.exp (-(2 * B)) / 8 at htail
  linarith

theorem exists_threeSurvival_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ z, threeSurvival z < ε := by
  by_contra h
  push Not at h
  apply threeReciprocals_unbounded
  refine ⟨-Real.log ε, ?_⟩
  rintro _ ⟨z, rfl⟩
  have he := (h z).trans (threeSurvival_bounds z).2
  rw [← Real.exp_log hε, Real.exp_le_exp] at he
  linarith


end OeisA69004

end

section

-- Adding primes in the class 3 modulo 4 to the norm sieve.

namespace OeisA69004

open Finset Nat

theorem primeOneSet_mono : Monotone primeOneSet := by
  intro a b hab p hp
  obtain ⟨hh, h1⟩ := mem_filter.mp hp
  obtain ⟨hI, hpp⟩ := mem_filter.mp hh
  exact mem_filter.mpr ⟨mem_filter.mpr
    ⟨mem_Icc.mpr ⟨(mem_Icc.mp hI).1, (mem_Icc.mp hI).2.trans hab⟩, hpp⟩, h1⟩

theorem prime_of_mem_primeOneSet {z p : ℕ} (hp : p ∈ primeOneSet z) : p.Prime :=
  (mem_filter.mp (mem_filter.mp hp).1).2

theorem prime_of_mem_primeThreeSet {z p : ℕ} (hp : p ∈ primeThreeSet z) : p.Prime :=
  (mem_filter.mp (mem_filter.mp hp).1).2

theorem primeOneSet_disjoint_primeThreeSet (z x : ℕ) :
    Disjoint (primeOneSet z) (primeThreeSet x) := by
  rw [Finset.disjoint_left]
  intro p h1 h3
  have hh1 := (mem_filter.mp h1).2
  have hh3 := (mem_filter.mp h3).2
  omega

def mixedPrimes (x z : ℕ) : Finset ℕ := primeOneSet z ∪ primeThreeSet x

theorem prime_of_mem_mixedPrimes {x z p : ℕ} (hp : p ∈ mixedPrimes x z) : p.Prime :=
  (mem_union.mp hp).elim prime_of_mem_primeOneSet prime_of_mem_primeThreeSet

theorem mixedPrimeProd_squarefree (x z : ℕ) : Squarefree (primeProd (mixedPrimes x z)) :=
  squarefree_primeProd fun _ hp => prime_of_mem_mixedPrimes hp

theorem prime_dvd_primeProd_iff {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime)
    {p : ℕ} (hp : p.Prime) : p ∣ primeProd T ↔ p ∈ T := by
  show p ∣ (∏ q ∈ T, q) ↔ p ∈ T
  conv_rhs => rw [← Nat.primeFactors_prod hT, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨hp, h, (squarefree_primeProd hT).ne_zero⟩, fun h => h.2.1⟩

theorem normRoots_card_of_mem_mixedPrimes {x z e p : ℕ} (he : 0 < e)
    (hp : p ∈ mixedPrimes x z) :
    (normRoots ((primeProd (primeThreeSet x)) ^ e) p).card =
      if p % 4 = 1 then 2 else 1 := by
  have hp' := prime_of_mem_mixedPrimes hp
  let : Fact p.Prime := ⟨hp'⟩
  have hQ := prime_dvd_primeProd_iff (T := primeThreeSet x)
    (fun _ hq => prime_of_mem_primeThreeSet hq) hp'
  rcases mem_union.mp hp with h1 | h3
  · have hm := (mem_filter.mp h1).2
    rw [if_pos hm]
    apply normRoots_card_of_one_mod_four hm
    intro hd
    have hmem := hQ.mp (hp'.dvd_of_dvd_pow hd)
    have h3 := (mem_filter.mp hmem).2
    omega
  · have hm := (mem_filter.mp h3).2
    rw [if_neg (by omega)]
    apply normRoots_card_of_dvd
    exact dvd_pow (hQ.mpr h3) he.ne'

theorem normRoots_bounds_mixed {x z e p : ℕ} (he : 0 < e) (hp : p.Prime)
    (hd : p ∣ primeProd (mixedPrimes x z)) :
    1 ≤ (normRoots ((primeProd (primeThreeSet x)) ^ e) p).card ∧
      (normRoots ((primeProd (primeThreeSet x)) ^ e) p).card < p := by
  have hm := (prime_dvd_primeProd_iff (fun _ h => prime_of_mem_mixedPrimes h) hp).mp hd
  rw [normRoots_card_of_mem_mixedPrimes he hm]
  have h2 := hp.two_le
  split_ifs <;> omega

noncomputable def mixedSieve (x z e : ℕ) (he : 0 < e) : BoundingSieve :=
  normSieve ((primeProd (primeThreeSet x)) ^ e) (primeProd (mixedPrimes x z))
    (mixedPrimeProd_squarefree x z) (fun _ hp hd => normRoots_bounds_mixed he hp hd)

noncomputable def mixedFactor (p : ℕ) : ℝ :=
  if p % 4 = 1 then 2 / ((p : ℝ) - 2) else 1 / ((p : ℝ) - 1)

theorem mixedSieve_selbergTerms {x z e d : ℕ} (he : 0 < e)
    (hd : d ∣ primeProd (mixedPrimes x z)) :
    (mixedSieve x z e he).selbergTerms d = ∏ p ∈ d.primeFactors, mixedFactor p := by
  let S := mixedSieve x z e he
  change S.selbergTerms d = _
  have hdf := (mixedPrimeProd_squarefree x z).squarefree_of_dvd hd
  rw [BoundingSieve.selbergTerms_apply, ← S.nu_mult.prod_primeFactors hdf, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hm := (prime_dvd_primeProd_iff (fun _ h => prime_of_mem_mixedPrimes h) hpp).mp hpd
  change normDensity _ p * (1 - normDensity _ p)⁻¹ = _
  rw [normDensity_eq hpp.squarefree, normRoots_card_of_mem_mixedPrimes he hm]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  unfold mixedFactor
  split_ifs with h
  · have hp3 : (2 : ℝ) < p := by
      have := hpp.two_le
      exact_mod_cast (show 2 < p by omega)
    push_cast
    have hneq : (p : ℝ) - 2 ≠ 0 := by linarith
    have hneq' : 1 - 2 / (p : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr ((div_lt_one hp0).mpr hp3).ne'
    field_simp
  · push_cast
    have hneq : (p : ℝ) - 1 ≠ 0 := by linarith
    have hneq' : 1 - 1 / (p : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr ((div_lt_one hp0).mpr (by linarith)).ne'
    field_simp


end OeisA69004

end

section

-- Multiplying the logarithmic factor by the contribution of the selected primes modulo four.

namespace OeisA69004

open Finset Nat

private noncomputable def thirdClassEuler (E : Finset ℕ) : ℝ :=
  ∏ q ∈ E, 1 / ((q : ℝ) - 1)

private theorem thirdClassEuler_powerset (x : ℕ) :
    (∑ E ∈ (primeThreeSet x).powerset, thirdClassEuler E) = (threeSurvival x)⁻¹ := by
  rw [threeSurvival, ← Finset.prod_inv_distrib]
  unfold thirdClassEuler
  rw [← Finset.prod_one_add]
  refine prod_congr rfl fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primeThreeSet hp).two_le
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2' : 1 - (p : ℝ)⁻¹ ≠ 0 := by
    exact sub_ne_zero.mpr (inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < p)).ne'
  field_simp
  ring

private theorem primeProd_union_pair_facts {x z w : ℕ}
    (hwz : w * primeProd (primeThreeSet x) ≤ z)
    {D E : Finset ℕ} (hD : D ∈ firstClassSupports w) (hE : E ⊆ primeThreeSet x) :
    D ⊆ primeOneSet z ∧ Disjoint D E ∧
      primeProd (D ∪ E) ∣ primeProd (mixedPrimes x z) ∧ primeProd (D ∪ E) ≤ z := by
  have hx : 0 < primeProd (primeThreeSet x) :=
    Nat.pos_of_ne_zero (squarefree_primeProd (fun _ hp => prime_of_mem_primeThreeSet hp)).ne_zero
  have hw : w ≤ z := (Nat.le_mul_of_pos_right _ hx).trans hwz
  have hDz : D ⊆ primeOneSet z :=
    (firstClassSupports_subset hD).trans (primeOneSet_mono hw)
  have hdis := (primeOneSet_disjoint_primeThreeSet z x).mono hDz hE
  have hU : D ∪ E ⊆ mixedPrimes x z := union_subset_union hDz hE
  have hdiv : primeProd (D ∪ E) ∣ primeProd (mixedPrimes x z) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hU
  have hleE : primeProd E ≤ primeProd (primeThreeSet x) :=
    le_of_dvd hx (Finset.prod_dvd_prod_of_subset _ _ _ hE)
  have hle : primeProd (D ∪ E) ≤ z := by
    unfold primeProd
    rw [prod_union hdis]
    exact (Nat.mul_le_mul (firstClassSupports_prod_le hD) hleE).trans hwz
  exact ⟨hDz, hdis, hdiv, hle⟩

private theorem mixedSelbergCut_pair {x z w e : ℕ} (he : 0 < e)
    (hwz : w * primeProd (primeThreeSet x) ≤ z)
    {D E : Finset ℕ} (hD : D ∈ firstClassSupports w) (hE : E ⊆ primeThreeSet x) :
    (mixedSieve x z e he).selbergCut z (primeProd (D ∪ E)) =
      firstClassEuler D * thirdClassEuler E := by
  obtain ⟨hDz, hdis, hdvd, hle⟩ := primeProd_union_pair_facts hwz hD hE
  rw [BoundingSieve.selbergCut, if_pos hle, mixedSieve_selbergTerms he hdvd]
  have hP : ∀ p ∈ D ∪ E, p.Prime := fun p hp => (mem_union.mp hp).elim
    (fun h => prime_of_mem_primeOneSet (hDz h)) (fun h => prime_of_mem_primeThreeSet (hE h))
  change (∏ p ∈ (∏ p ∈ D ∪ E, p).primeFactors, mixedFactor p) = _
  rw [Nat.primeFactors_prod hP, Finset.prod_union hdis, firstClassEuler, thirdClassEuler]
  congr 1
  · refine prod_congr rfl fun p hp => ?_
    exact if_pos ((mem_filter.mp (hDz hp)).2)
  · refine prod_congr rfl fun p hp => ?_
    have h3 := (mem_filter.mp (hE hp)).2
    exact if_neg (by omega)

theorem mixedDenominator_lower {x z w e : ℕ} (he : 0 < e)
    (hwz : w * primeProd (primeThreeSet x) ≤ z) :
    firstClassSum w / threeSurvival x ≤ (mixedSieve x z e he).selbergDenominator z := by
  classical
  let S := mixedSieve x z e he
  let B := firstClassSupports w ×ˢ (primeThreeSet x).powerset
  let f (a : Finset ℕ × Finset ℕ) := primeProd (a.1 ∪ a.2)
  have ha (a : Finset ℕ × Finset ℕ) (h : a ∈ B) :
      a.1 ⊆ primeOneSet z ∧ a.2 ⊆ primeThreeSet x := by
    obtain ⟨h1, h2⟩ := mem_product.mp h
    exact ⟨(primeProd_union_pair_facts hwz h1 (mem_powerset.mp h2)).1, mem_powerset.mp h2⟩
  have hprim (a : Finset ℕ × Finset ℕ) (h : a ∈ B) :
      ∀ p ∈ a.1 ∪ a.2, p.Prime :=
    fun _ h' => (mem_union.mp h').elim
      (fun h' => prime_of_mem_primeOneSet ((ha a h).1 h'))
      (fun h' => prime_of_mem_primeThreeSet ((ha a h).2 h'))
  have hdis := Finset.disjoint_left.mp (primeOneSet_disjoint_primeThreeSet z x)
  have hleft (a : Finset ℕ × Finset ℕ) (h : a ∈ B) :
      (a.1 ∪ a.2) ∩ primeOneSet z = a.1 := by
    ext p
    simp only [mem_inter, mem_union]
    refine ⟨fun ⟨hU, h1⟩ => ?_, fun h1 => ⟨Or.inl h1, (ha a h).1 h1⟩⟩
    exact hU.elim id fun h2 => False.elim (hdis h1 ((ha a h).2 h2))
  have hright (a : Finset ℕ × Finset ℕ) (h : a ∈ B) :
      (a.1 ∪ a.2) ∩ primeThreeSet x = a.2 := by
    ext p
    simp only [mem_inter, mem_union]
    refine ⟨fun ⟨hU, h2⟩ => ?_, fun h2 => ⟨Or.inr h2, (ha a h).2 h2⟩⟩
    exact hU.elim (fun h1 => False.elim (hdis ((ha a h).1 h1) h2)) id
  have hf : Set.InjOn f B := by
    intro a ha b hb hab
    have hS : a.1 ∪ a.2 = b.1 ∪ b.2 := by
      calc
        _ = (f a).primeFactors := (Nat.primeFactors_prod (hprim a ha)).symm
        _ = (f b).primeFactors := congrArg Nat.primeFactors hab
        _ = _ := Nat.primeFactors_prod (hprim b hb)
    exact Prod.ext
      ((hleft a ha).symm.trans (by rw [hS, hleft b hb]))
      ((hright a ha).symm.trans (by rw [hS, hright b hb]))
  have hsub : B.image f ⊆ S.prodPrimes.divisors := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    obtain ⟨h1, h2⟩ := mem_product.mp ha
    have hdvd := (primeProd_union_pair_facts hwz h1 (mem_powerset.mp h2)).2.2.1
    exact mem_divisors.mpr ⟨hdvd, (mixedPrimeProd_squarefree x z).ne_zero⟩
  calc
    firstClassSum w / threeSurvival x =
        ∑ a ∈ B, firstClassEuler a.1 * thirdClassEuler a.2 := by
      rw [div_eq_mul_inv, ← thirdClassEuler_powerset x, firstClassSum, sum_mul_sum]
      exact (sum_product' (firstClassSupports w) (primeThreeSet x).powerset
        (fun D E => firstClassEuler D * thirdClassEuler E)).symm
    _ = ∑ a ∈ B, S.selbergCut z (f a) := by
      refine sum_congr rfl fun a ha => ?_
      obtain ⟨h1, h2⟩ := mem_product.mp ha
      exact (mixedSelbergCut_pair he hwz h1 (mem_powerset.mp h2)).symm
    _ = ∑ d ∈ B.image f, S.selbergCut z d := (sum_image hf).symm
    _ ≤ S.selbergDenominator z := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ hd _ => S.selbergCut_nonneg (dvd_of_mem_divisors hd))


end OeisA69004

end

section

-- Turning an arbitrarily small normalized sieve bound into the exact disproof.

namespace OeisA69004

open Filter Real

theorem disproof_of_frequent_small_norm_counts
    (hs : ∀ B : ℝ, 0 < B → ∃ᶠ n : ℕ in atTop,
      (a n : ℝ) ≤ (n : ℝ) / (B * Real.log n) + Real.sqrt n) :
    ¬ (type_of% @conjecture2.variants.without_upper_bound) := by
  let C : ℝ := Real.log 2
  have hC : 0 < C := Real.log_pos (by norm_num)
  have hB : 0 < 40 / C := div_pos (by norm_num) hC
  have hfreq := hs (40 / C) hB
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log n ≤ (C / 40) * Real.sqrt n := by
    have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have he := hsmall.bound (show 0 < C / 40 by positivity)
    filter_upwards [he] with n hn
    change ‖Real.log (n : ℝ)‖ ≤ (C / 40) * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ at hn
    have hnp : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnp] at hn
    rw [Real.sqrt_eq_rpow]
    exact (le_abs_self _).trans hn
  obtain ⟨n, hsmall, hlogn, hn8⟩ :=
    (hfreq.and_eventually (hlog.and (eventually_ge_atTop 8))).exists
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hroot : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hsqrtle : √(n : ℝ) ≤ n := (Real.sqrt_le_iff).mpr ⟨hn0.le, by nlinarith⟩
  have hmul := mul_le_mul_of_nonneg_right hsmall hln.le
  have herror := mul_le_mul_of_nonneg_left hlogn (Real.sqrt_nonneg (n : ℝ))
  have herror' : √(n : ℝ) * Real.log n ≤ (C / 40) * n := by
    calc
      _ ≤ √(n : ℝ) * ((C / 40) * √(n : ℝ)) := herror
      _ = _ := by rw [mul_left_comm, hroot]
  have hfirst : ((n : ℝ) / (40 / C * Real.log n)) * Real.log n = C * n / 40 := by
    field_simp
  rw [add_mul, hfirst] at hmul
  have hlogplus : Real.log ((n : ℝ) + 1) ≤ C * n / 2 := by
    calc
      _ ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = C + Real.log n := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ C + C / 40 * √(n : ℝ) := by linarith
      _ ≤ C + C / 40 * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsqrtle (show 0 ≤ C / 40 by positivity)
        linarith
      _ ≤ _ := by
        have hx : (8 : ℝ) ≤ n := by exact_mod_cast hn8
        nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hx)]
  have hpi := (div_le_iff₀ hln).mp (Chebyshev.pi_ge n)
  change (n : ℝ) * C - Real.log ((n : ℝ) + 1) ≤
    (Nat.primeCounting n : ℝ) * Real.log n at hpi
  have hb : (5 * (a n : ℝ)) * Real.log n <
      (Nat.primeCounting n : ℝ) * Real.log n := by
    have hpos : 0 < C * (n : ℝ) := mul_pos hC hn0
    nlinarith
  have hc' := lt_of_mul_lt_mul_right hb hln.le
  exact disproof_of_counterexample (n := n) (by omega) (by exact_mod_cast hc')


end OeisA69004

end

section

-- Scaling the sieve parameters and negating the exact pinned declaration.

namespace OeisA69004

open Finset Nat Real Filter

private theorem frequent_upper_bound (B : ℝ) (hB : 0 < B) :
    ∃ᶠ n : ℕ in atTop, (a n : ℝ) ≤ (n : ℝ) / (B * Real.log n) + Real.sqrt n := by
  have hε : 0 < min (1 / 2 : ℝ) (1 / (390 * B)) :=
    lt_min (by norm_num) (by positivity)
  obtain ⟨x, hx⟩ := exists_threeSurvival_lt hε
  have hxs : threeSurvival x < 1 / (390 * B) := hx.trans_le (min_le_right _ _)
  have hx1 : threeSurvival x < 1 := hx.trans ((min_le_left _ _).trans_lt (by norm_num))
  have hs0 : 0 < threeSurvival x :=
    (exp_pos _).trans_le (threeSurvival_bounds x).1
  let Q : ℕ := primeProd (primeThreeSet x)
  have hQ0 : 0 < Q :=
    Nat.pos_of_ne_zero (squarefree_primeProd (fun _ hp => prime_of_mem_primeThreeSet hp)).ne_zero
  have hQ : 1 < Q := by
    by_contra! h
    have h1 : Q = 1 := by omega
    rw [threeSurvival_eq_totient] at hx1
    change ((Q.totient : ℝ) / Q) < 1 at hx1
    simp [h1] at hx1
  have hQ' : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hQl : 0 < log (Q : ℝ) := log_pos hQ'
  rw [frequently_atTop]
  intro N
  let k : ℕ := N + 2
  have hk : 2 ≤ k := by omega
  let w := Q ^ (k - 1)
  let z := Q ^ k
  let e := 32 * k + 1
  have he : 0 < e := by dsimp [e]; omega
  let n := Q ^ e
  have hn : N ≤ n := by
    calc
      N ≤ k + 1 := by dsimp [k]; omega
      _ ≤ 2 ^ k := succ_le_two_pow k
      _ ≤ Q ^ k := Nat.pow_le_pow_left (by omega) _
      _ ≤ n := Nat.pow_le_pow_right hQ0 (by dsimp [e]; omega)
  refine ⟨n, hn, ?_⟩
  have hz : 1 ≤ z := Nat.pow_pos hQ0
  have hzn : z ≤ n := Nat.pow_le_pow_right hQ0 (by dsimp [e]; omega)
  have hQn : Q ≤ n := by
    have hp := Nat.pow_le_pow_right hQ0 (show 1 ≤ e by omega)
    simpa only [pow_one] using hp
  have hwz : w * Q ≤ z := by
    dsimp [w, z]
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hlogn : log (n : ℝ) = (e : ℝ) * log (Q : ℝ) := by
    simp [n, Nat.cast_pow, Real.log_pow]
  have hlogw : log (w : ℝ) = ((k - 1 : ℕ) : ℝ) * log (Q : ℝ) := by
    simp [w, Nat.cast_pow, Real.log_pow]
  have hn1 : 1 < n := Nat.one_lt_pow he.ne' hQ
  have hln : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn1)
  have hG := mixedDenominator_lower (x := x) (e := e) he hwz
  let S := mixedSieve x z e he
  change firstClassSum w / threeSurvival x ≤ S.selbergDenominator z at hG

  have h65 : (e : ℝ) / 65 ≤ ((k - 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by norm_num)).mpr
    exact_mod_cast (show e ≤ (k - 1) * 65 by dsimp [e]; omega)
  have hw0 : 0 < w := Nat.pow_pos hQ0
  have hwLarge : log (w : ℝ) ≤ log ((w : ℝ) + 1) :=
    log_le_log (by exact_mod_cast hw0) (by linarith)
  have hfirst : log (n : ℝ) / 390 ≤ firstClassSum w := by
    have hm := mul_le_mul_of_nonneg_right h65 hQl.le
    calc
      _ ≤ log (w : ℝ) / 6 := by rw [hlogn, hlogw]; linarith
      _ ≤ log ((w : ℝ) + 1) / 6 := div_le_div_of_nonneg_right hwLarge (by norm_num)
      _ ≤ _ := log_le_six_firstClassSum w
  have hsB : B * threeSurvival x ≤ 1 / 390 := by
    calc
      _ ≤ B * (1 / (390 * B)) := mul_le_mul_of_nonneg_left hxs.le hB.le
      _ = _ := by field_simp [hB.ne']
  have hden : B * log (n : ℝ) ≤ S.selbergDenominator z := by
    refine ((le_div_iff₀ hs0).mpr ?_).trans hG
    calc
      (B * log (n : ℝ)) * threeSurvival x = (B * threeSurvival x) * log (n : ℝ) := by ring
      _ ≤ (1 / 390) * log (n : ℝ) := mul_le_mul_of_nonneg_right hsB hln.le
      _ = log (n : ℝ) / 390 := by ring
      _ ≤ _ := hfirst
  have ha : (a n : ℝ) ≤ (n : ℝ) / S.selbergDenominator z + (z : ℝ) ^ 10 := by
    apply a_le_selbergDenominator (hP := mixedPrimeProd_squarefree x z)
      (hρ := fun _ hp hd => normRoots_bounds_mixed he hp hd) hz
    intro p hp hd
    have hm := (prime_dvd_primeProd_iff (fun _ h => prime_of_mem_mixedPrimes h) hp).mp hd
    rcases mem_union.mp hm with h1 | h3
    · exact ((mem_Icc.mp (mem_filter.mp (mem_filter.mp h1).1).1).2).trans hzn
    · refine (le_of_dvd hQ0 ?_).trans hQn
      exact (prime_dvd_primeProd_iff (fun _ h => prime_of_mem_primeThreeSet h) hp).mpr h3
  have herr : (z : ℝ) ^ 10 ≤ sqrt (n : ℝ) := by
    have heq : ((z ^ 10) ^ 2 : ℕ) ≤ n := by
      dsimp [z, n]
      rw [← pow_mul, ← pow_mul]
      exact Nat.pow_le_pow_right hQ0 (by dsimp [e]; omega)
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast heq)
  exact ha.trans (add_le_add
    (div_le_div_of_nonneg_left (by positivity) (mul_pos hB hln) hden) herr)

end OeisA69004

/-- The proposed uniform lower bound fails along powers of suitable fixed squarefree integers. -/
theorem OMA.disproof : ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) :=
  OeisA69004.disproof_of_frequent_small_norm_counts OeisA69004.frequent_upper_bound

end
