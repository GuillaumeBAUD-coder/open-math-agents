import OMAReductions.R_Erdos240_erdos_240_variants_tijdeman_finite_R1

-- Step Erdos240.erdos_240.variants.tijdeman_finite.R1.H3: hypothesis H3 of reduction Erdos240.erdos_240.variants.tijdeman_finite.R1

/-!
Take `b p = v_p(y) - v_p(x)`. Since every prime factor of `x` and of `y` lies in `S`, we have
`log x = ∑_{p ∈ S} v_p(x) log p`, and the same for `y`. Each exponent satisfies
`2 ^ v_p(n) ≤ p ^ v_p(n) ≤ n`, so `v_p(n) ≤ log n / log 2`, and the difference of two numbers in
`[0, B]` has absolute value at most `B`.
-/

namespace OMA

theorem logsum (S : Finset ℕ) (n : ℕ) (hS : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    exact hS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    rw [hp]
    simp

theorem fact_le (n p : ℕ) (hn : 0 < n) :
    (n.factorization p : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases hp : p.Prime
  · have h1 : p ^ n.factorization p ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    have h2 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    have h3 : ((2 : ℝ)) ^ n.factorization p ≤ (n : ℝ) := by
      exact_mod_cast le_trans h2 h1
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at h4
    rw [le_div_iff₀ hl2]
    exact h4
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    simp only [Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hn1) hl2.le

end OMA

theorem OMA.solution : OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1.H3 := by
  unfold OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1.H3
  intro S x y hx hy hSx hSy
  refine ⟨fun p => (y.factorization p : ℤ) - (x.factorization p : ℤ), ?_, ?_⟩
  · rw [OMA.logsum S y hSy, OMA.logsum S x hSx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    push_cast
    ring
  · intro p _
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx1 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hy1 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
    have hxm : (x : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_left x y
    have hym : (y : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_right x y
    have a1 := OMA.fact_le x p hx
    have a2 := OMA.fact_le y p hy
    have b1 : Real.log (x : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hx1 hxm) hl2.le
    have b2 : Real.log (y : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hy1 hym) hl2.le
    have c1 : (0 : ℝ) ≤ (x.factorization p : ℝ) := Nat.cast_nonneg _
    have c2 : (0 : ℝ) ≤ (y.factorization p : ℝ) := Nat.cast_nonneg _
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [abs_le]
    constructor <;> linarith
