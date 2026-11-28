import OMAStatements.S_oeis_a014307
import Mathlib

/-! A014307: the e.g.f. A of the first column of the Kurkov triangle (m = 2) satisfies
A^2 (2 - e^x) = e^x. Row entries satisfy R(n, k) = sum_t C(n-k, t) b(k+t) for 1 <= k <= n, where
b(j) = R(j, 0); at k = 1 this gives 2 b(n+1) = b(n) + sum_t C(n, t) b(t+1), i.e. A' (2 - e^x) = A,
so G = A^2 (2 - e^x) satisfies G' = G and G(0) = 1. -/

namespace OMA.Helpers

open OMA.S_oeis_a014307 PowerSeries Finset


theorem A014_k0s (n : ℕ) : kurkovR 2 (n + 1) 0 = ∑ j ∈ range (n + 1), kurkovR 2 n j := by
  rw [kurkovR]

theorem A014_kss (n k : ℕ) : kurkovR 2 (n + 1) (k + 1) =
    2 * (∑ j ∈ range (n + 1), kurkovR 2 n j) - ∑ j ∈ range (k + 1), kurkovR 2 n j := by
  rw [kurkovR]

theorem A014_kdiff (n k : ℕ) :
    kurkovR 2 (n + 1) (k + 1) = kurkovR 2 (n + 1) (k + 2) + kurkovR 2 n (k + 1) := by
  rw [A014_kss, A014_kss, sum_range_succ _ (k + 1)]; ring

theorem A014_ktop (n : ℕ) : kurkovR 2 (n + 1) (n + 1) = kurkovR 2 (n + 1) 0 := by
  rw [A014_kss, A014_k0s]; ring

noncomputable def A014_Fq (m k : ℕ) : ℚ := ∑ t ∈ range (m + 1), (m.choose t : ℚ) * kurkovR 2 (k + t) 0

theorem A014_Fq_zero (k : ℕ) : A014_Fq 0 k = kurkovR 2 k 0 := by simp [A014_Fq]

theorem A014_Fq_succ (m k : ℕ) : A014_Fq (m + 1) k = A014_Fq m k + A014_Fq m (k + 1) := by
  unfold A014_Fq
  rw [sum_range_succ' _ (m + 1), sum_range_succ' (fun t => (m.choose t : ℚ) * kurkovR 2 (k + t) 0)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib]
  rw [sum_range_succ (fun t => ((m.choose (t + 1) : ℕ) : ℚ) * kurkovR 2 (k + (t + 1)) 0) m]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right]
  have e : ∑ t ∈ range (m + 1), (m.choose t : ℚ) * kurkovR 2 (k + (t + 1)) 0 =
      ∑ t ∈ range (m + 1), (m.choose t : ℚ) * kurkovR 2 (k + 1 + t) 0 := by
    apply sum_congr rfl
    intro t _
    rw [show k + (t + 1) = k + 1 + t by omega]
  rw [e]
  ring

theorem A014_kclosed : ∀ n d k : ℕ, 1 ≤ k → k + d = n → kurkovR 2 n k = A014_Fq d k := by
  intro n
  induction n with
  | zero => intro d k hk hkd; omega
  | succ n ihn =>
    intro d
    induction d with
    | zero =>
      intro k hk hkd
      have : k = n + 1 := by omega
      subst this
      rw [A014_ktop, A014_Fq_zero]
    | succ d ihd =>
      intro k hk hkd
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [A014_kdiff, ihd (k' + 2) (by omega) (by omega), ihn d (k' + 1) (by omega) (by omega), A014_Fq_succ]
      ring

theorem A014_krec (n : ℕ) : 2 * kurkovR 2 (n + 1) 0 =
    kurkovR 2 n 0 + ∑ t ∈ range (n + 1), (n.choose t : ℚ) * kurkovR 2 (t + 1) 0 := by
  have h1 := A014_kclosed (n + 1) n 1 le_rfl (by omega)
  rw [A014_kss, sum_range_one, ← A014_k0s] at h1
  unfold A014_Fq at h1
  have e : ∀ t, 1 + t = t + 1 := fun t => by omega
  simp only [e] at h1
  linarith

theorem A014_fact_inv_mul (n i : ℕ) (hi : i ≤ n) :
    ((i.factorial : ℚ))⁻¹ * ((n - i).factorial : ℚ)⁻¹ = (n.choose i : ℚ) / n.factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial hi
  have h' : ((n.choose i : ℚ)) * i.factorial * (n - i).factorial = n.factorial := by exact_mod_cast h
  have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n - i).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

theorem A014_coeff_exp (n : ℕ) : coeff n expSeries = ((n.factorial : ℚ))⁻¹ := by
  simp [expSeries]

theorem A014_dexp : derivative ℚ expSeries = expSeries := by
  ext n
  rw [coeff_derivative, A014_coeff_exp, A014_coeff_exp, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem A014_dA_eq (A : PowerSeries ℚ) (hA : ∀ n : ℕ, coeff n A = kurkovR 2 n 0 / (n.factorial : ℚ)) :
    derivative ℚ A * (2 - expSeries) = A := by
  ext n
  have hd : ∀ i : ℕ, coeff i (derivative ℚ A) = kurkovR 2 (i + 1) 0 / (i.factorial : ℚ) := by
    intro i
    rw [coeff_derivative, hA, Nat.factorial_succ]
    push_cast
    have : (i.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  rw [mul_sub, map_sub, show (derivative ℚ A * 2) = (2 : ℚ) • derivative ℚ A by
    rw [smul_eq_C_mul, mul_comm]; rfl]
  rw [map_smul, hd, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hA]
  have hs : ∑ k ∈ range (n + 1), coeff (k, n - k).1 (derivative ℚ A) * coeff (k, n - k).2 expSeries
      = (∑ t ∈ range (n + 1), (n.choose t : ℚ) * kurkovR 2 (t + 1) 0) / (n.factorial : ℚ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    simp only
    rw [hd, A014_coeff_exp, div_eq_mul_inv, mul_assoc, A014_fact_inv_mul n k (by omega)]
    ring
  rw [hs, smul_eq_mul]
  have := A014_krec n
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith

end OMA.Helpers

open OMA.Helpers OMA.S_oeis_a014307 PowerSeries Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a014307.main := by
  intro A hA
  have h1 := A014_dA_eq A hA
  have hdG : derivative ℚ (A ^ 2 * (2 - expSeries)) = A ^ 2 * (2 - expSeries) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, map_sub, A014_dexp]
    have h2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := by
      have := (derivative ℚ).map_natCast (A := PowerSeries ℚ) 2
      exact_mod_cast this
    rw [h2]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    linear_combination (2 * A) * h1
  have hc : constantCoeff (A ^ 2 * (2 - expSeries)) = 1 := by
    have h0 : constantCoeff A = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hA]; simp [kurkovR]
    have he : constantCoeff expSeries = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, A014_coeff_exp]; simp
    have h2 : constantCoeff (2 : PowerSeries ℚ) = 2 := map_ofNat _ 2
    simp [h0, he, h2]
    norm_num
  ext n
  induction n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, hc, A014_coeff_exp]; simp
  | succ n ih =>
    have := congrArg (coeff n) hdG
    rw [coeff_derivative, ih, A014_coeff_exp] at this
    rw [A014_coeff_exp, Nat.factorial_succ]
    push_cast
    have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
    field_simp at this
    linarith

