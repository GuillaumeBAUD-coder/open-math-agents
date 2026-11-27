import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1
import Mathlib

/-! # A small-power bound for the divisor function
Separate the primes below a fixed cutoff from the remaining prime factors.
Bernoulli's inequality absorbs each small-prime exponent at a fixed cost. -/

namespace OMA.DivisorPower711

open Filter

lemma weak_power (α : ℝ) (hα : 0 < α) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ y : ℕ, y ≠ 0 → (y.divisors.card : ℝ) ≤ K * (y : ℝ)^α := by
  classical
  let b := (2:ℝ)^α
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hα
  let C := max 1 (1 / (b-1))
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCb : 1 ≤ C*(b-1) := (div_le_iff₀ (by linarith)).mp (le_max_right _ _)
  have hsmall (a : ℕ) : (a+1:ℝ) ≤ C*b^a := by
    have hBern := one_add_mul_sub_le_pow (show -1 ≤ b by linarith) a
    have ha := mul_le_mul_of_nonneg_left hCb (Nat.cast_nonneg a)
    have h' := mul_le_mul_of_nonneg_left hBern hC0
    nlinarith
  have hlarge (a : ℕ) : a+1 ≤ 2^a := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ]
      omega
  have hg : Tendsto (fun n : ℕ => (n:ℝ)^α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hg.eventually_ge_atTop 2)
  refine ⟨C^T, one_le_pow₀ hC, ?_⟩
  intro y hy
  let S := y.primeFactors
  let coeff (p : ℕ) : ℝ := if p < T then C else 1
  let v (p : ℕ) : ℝ := ((p : ℝ)^(y.factorization p))^α
  have hfactor (p : ℕ) (hp : p ∈ S) :
      ((y.factorization p + 1 : ℕ) : ℝ) ≤ coeff p * v p := by
    let a := y.factorization p
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hv : v p = ((p : ℝ)^α)^a := by
      dsimp [v, a]
      rw [← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity), mul_comm]
    rw [hv]
    by_cases h : p < T
    · simp only [coeff, if_pos h, Nat.cast_add, Nat.cast_one]
      exact (hsmall a).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^α) (Real.rpow_le_rpow (by norm_num) hp2 hα.le) a) hC0)
    · simp only [coeff, if_neg h, one_mul]
      calc
        _ ≤ (2:ℝ)^a := by exact_mod_cast hlarge a
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) (hT p (by omega)) _
  have hprod : (∏ p ∈ S, v p) = (y:ℝ)^α := by
    rw [show (∏ p ∈ S, v p) = (∏ p ∈ S, (p:ℝ)^y.factorization p)^α from
      Real.finsetProd_rpow S _ (fun i _ => by positivity) α]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hy).symm
  have hcount : (S.filter (· < T)).card ≤ T := by
    have hs : S.filter (· < T) ⊆ Finset.range T := fun _ h => Finset.mem_range.mpr (Finset.mem_filter.mp h).2
    simpa using Finset.card_le_card hs
  have hcoeff : (∏ p ∈ S, coeff p) ≤ C^T := by
    have heq : (∏ p ∈ S, coeff p) = C^(S.filter (· < T)).card := by
      rw [← Finset.prod_const]
      exact (Finset.prod_filter _ _).symm
    rw [heq]
    exact pow_le_pow_right₀ hC hcount
  calc
    _ = ∏ p ∈ S, ((y.factorization p+1 : ℕ) : ℝ) := by
      rw [Nat.card_divisors hy, Nat.cast_prod]
    _ ≤ ∏ p ∈ S, coeff p * v p :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) hfactor
    _ = (∏ p ∈ S, coeff p)*(y:ℝ)^α := by rw [Finset.prod_mul_distrib,hprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)

end OMA.DivisorPower711

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1.H1 := by
  intro δ hδ
  obtain ⟨K,hK,hall⟩ := OMA.DivisorPower711.weak_power (δ/6) (by positivity)
  have hg : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(δ/2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually_ge_atTop K, Filter.eventually_ge_atTop (1:ℕ)] with n hn hn1 y hy hle
  have hx : (y:ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast hle
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ K*(y:ℝ)^(δ/6) := hall y hy.ne'
    _ ≤ (n:ℝ)^(δ/2)*((n:ℝ)^3)^(δ/6) :=
      mul_le_mul hn (Real.rpow_le_rpow (by positivity) hx (by positivity)) (by positivity) (by positivity)
    _ = (n:ℝ)^δ := by
      rw [← Real.rpow_natCast_mul hn0.le 3, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
