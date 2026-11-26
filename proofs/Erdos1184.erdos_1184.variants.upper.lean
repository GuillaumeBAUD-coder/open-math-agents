import FormalConjectures.ErdosProblems.«1184»

/-! A binomial-coefficient bound for intervals containing large prime factors. -/

open Finset

namespace OMA.Erdos1184Upper

lemma intervalProduct (n k : ℕ) :
    (∏ i ∈ Icc 1 k, (n + i)) = (n + 1).ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_Icc_succ_top (Nat.succ_pos k) (fun i => n + i), ih, Nat.ascFactorial_succ]
    ring

-- The selected prime factors divide the interval product term by term.
-- They are all coprime to k!, so their product survives in the binomial coefficient.
lemma pow_count_le_choose (n k : ℕ) (hk : 2 ≤ k) :
    k ^ Erdos1184.f n k ≤ (n + k).choose k := by
  let S := (Icc 1 k).filter fun i => k < (n + i).maxPrimeFac
  let P := ∏ i ∈ S, (n + i).maxPrimeFac
  have hlarge (i : ℕ) (hi : i ∈ S) : k < (n + i).maxPrimeFac :=
    (mem_filter.mp hi).2
  have hdvd : P ∣ ∏ i ∈ Icc 1 k, (n + i) := by
    apply dvd_trans (prod_dvd_prod_of_dvd (fun i => (n + i).maxPrimeFac)
      (fun i => n + i) (s := S) (fun _ _ => Nat.maxPrimeFac_dvd))
    exact prod_dvd_prod_of_subset S (Icc 1 k) (fun i => n + i) (filter_subset _ _)
  have hcop : P.Coprime k.factorial := by
    apply Nat.Coprime.prod_left
    intro i hi
    have hi₁ := (mem_Icc.mp (mem_filter.mp hi).1).1
    have hle := Nat.le_of_dvd (show 0 < n + i by omega) Nat.maxPrimeFac_dvd
    have hlt := hlarge i hi
    exact (Nat.prime_maxPrimeFac_of_one_lt (n + i) (by omega)).coprime_factorial_of_lt hlt
  rw [intervalProduct, Nat.ascFactorial_eq_factorial_mul_choose] at hdvd
  exact (pow_card_le_prod S (fun i => (n + i).maxPrimeFac) k
    (fun i hi => (hlarge i hi).le)).trans
    (Nat.le_of_dvd (Nat.choose_pos (by omega)) (hcop.dvd_of_dvd_mul_left hdvd))

end OMA.Erdos1184Upper

theorem OMA.solution : type_of% @Erdos1184.erdos_1184.variants.upper := by
  intro α k n hk hn
  have hk₁ : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hk₀ : 0 < (k : ℝ) := zero_lt_one.trans hk₁
  have hlog : 0 < Real.log k := Real.log_pos hk₁
  have hcount : (k : ℝ) ^ Erdos1184.f n k ≤ ((n + k).choose k : ℝ) := by
    exact_mod_cast OMA.Erdos1184Upper.pow_count_le_choose n k hk
  have hchoose : ((n + k).choose k : ℝ) < ((n : ℝ) + k) ^ k / k.factorial := by
    simpa only [Nat.cast_add] using
      (Nat.choose_lt_pow_div (α := ℝ) (n := n + k) (by omega) hk)
  have hc := Real.log_lt_log (by positivity) (hcount.trans_lt hchoose)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hc
  have hf := Real.log_le_log (by positivity)
    (Real.pow_div_factorial_le_exp (x := (k : ℝ)) hk₀.le k)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hf
  have hnlog := Real.log_le_log (show 0 < (n : ℝ) + k by positivity)
    (show (n : ℝ) + k ≤ (k : ℝ) ^ α by linarith)
  rw [Real.log_rpow hk₀] at hnlog
  have hscaled := mul_le_mul_of_nonneg_left hnlog hk₀.le
  have h : ((Erdos1184.f n k : ℝ) - k * (α - 1)) * Real.log k < k := by
    nlinarith only [hc, hf, hscaled]
  linarith [(lt_div_iff₀ hlog).2 h]
