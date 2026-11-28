import OMAStatements.S_oeis_a189912
import Mathlib

namespace OMA.P189912

open OMA.S_oeis_a189912

lemma cbf_even (j : ℕ) : centralBinomFloor (2 * j) = (j + 1) * catalan j := by
  unfold centralBinomFloor
  rw [Nat.mul_div_cancel_left j (by norm_num), succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]

lemma choose_odd (j : ℕ) : (2 * j + 1).choose j = (2 * j + 1) * catalan j := by
  have h1 : (2 * j + 1) * (2 * j).choose j = (2 * j + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (2 * j) j
  rw [Nat.choose_symm_half] at h1
  have h2 : (2 * j).choose j = (j + 1) * catalan j := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  rw [h2] at h1
  have h3 : (j + 1) * ((2 * j + 1).choose j) = (j + 1) * ((2 * j + 1) * catalan j) := by
    linarith
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j) h3

lemma cbf_odd (j : ℕ) : centralBinomFloor (2 * j + 1) = (2 * j + 1) * catalan j := by
  unfold centralBinomFloor
  rw [show (2 * j + 1) / 2 = j from by omega, choose_odd]

lemma cbf_even_succ (j : ℕ) : centralBinomFloor (2 * j + 2) = 2 * ((2 * j + 1) * catalan j) := by
  unfold centralBinomFloor
  rw [show (2 * j + 2) / 2 = j + 1 from by omega, Nat.choose_succ_succ, Nat.choose_symm_half, choose_odd]
  ring

lemma ext_even (j : ℕ) : extCatalan (2 * j) = catalan j := by
  unfold extCatalan
  rw [cbf_odd, cbf_even, Nat.gcd_mul_right]
  have hc : Nat.gcd (2 * j + 1) (j + 1) = 1 := by
    have e : 2 * j + 1 = j + (j + 1) := by ring
    rw [e, Nat.gcd_add_self_left]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right j)
  rw [hc, one_mul]

lemma ext_odd (j : ℕ) : extCatalan (2 * j + 1) = (2 * j + 1) * catalan j := by
  unfold extCatalan
  rw [show 2 * j + 1 + 1 = 2 * j + 2 from rfl, cbf_even_succ, cbf_odd]
  exact Nat.gcd_eq_right (Dvd.intro_left 2 rfl)

lemma sum_even_odd (f : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

theorem main' : type_of% @OMA.S_oeis_a189912.main := by
  intro n
  have h1 : a n = ∑ k ∈ Finset.range (2 * (n / 2 + 1)), Nat.choose n k * extCatalan k := by
    unfold a
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx
      rw [Finset.mem_range] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  rw [h1, sum_even_odd]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hle : 2 * j ≤ n := by omega
  rw [ext_even, ext_odd]
  unfold motzkinCoeff
  have h2 : n.choose (2 * j + 1) * (2 * j + 1) = n.choose (2 * j) * (n - 2 * j) :=
    Nat.choose_succ_right_eq n (2 * j)
  have h3 : n + 1 - 2 * j = (n - 2 * j) + 1 := by omega
  rw [h3]
  calc n.choose (2 * j) * catalan j + n.choose (2 * j + 1) * ((2 * j + 1) * catalan j)
      = n.choose (2 * j) * catalan j + (n.choose (2 * j + 1) * (2 * j + 1)) * catalan j := by ring
    _ = n.choose (2 * j) * catalan j + (n.choose (2 * j) * (n - 2 * j)) * catalan j := by rw [h2]
    _ = (n - 2 * j + 1) * (n.choose (2 * j) * catalan j) := by ring

end OMA.P189912

theorem OMA.solution : type_of% @OMA.S_oeis_a189912.main := OMA.P189912.main'
