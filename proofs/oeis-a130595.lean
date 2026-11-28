import OMAStatements.S_oeis_a130595
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: the inverse of the truncated Pascal matrix is the signed binomial matrix
-- (-1)^(i+j) C(i,j), by the alternating sum identity sum_j (-1)^j C(i,j) C(j,k) = (-1)^k [i=k].
-- So T(n,k) = (-1)^(n+k) C(n,k), and the recurrence reduces to Pascal's rule together with
-- (k+1) C(n,k+1) = (n-k) C(n,k).

open Finset

namespace OMA.A130595Proof

open OMA.S_oeis_a130595

lemma alt (n : ℕ) : (∑ m ∈ range (n + 1), (-1:ℚ) ^ m * (n.choose m : ℚ)) = if n = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := n)
  have h2 : ((∑ m ∈ range (n + 1), ((-1) ^ m * ↑(n.choose m) : ℤ) : ℤ) : ℚ) = ((if n = 0 then 1 else 0 : ℤ) : ℚ) := by rw [h]
  push_cast at h2
  rw [h2]

lemma key (N i k : ℕ) (hi : i ≤ N) :
    ∑ j ∈ range (N+1), ((-1:ℚ)^(i+j) * (i.choose j) * (j.choose k)) = if i = k then 1 else 0 := by
  by_cases hki : k ≤ i
  · rw [← Finset.sum_subset (s₁ := Ico k (i+1))]
    · rw [Finset.sum_Ico_eq_sum_range]
      have e : ∀ m ∈ range (i + 1 - k), (-1:ℚ)^(i+(k+m)) * (i.choose (k+m)) * ((k+m).choose k)
          = ((-1:ℚ)^(i+k) * i.choose k) * ((-1:ℚ)^m * ((i-k).choose m)) := by
        intro m hm
        have hm' : k + m ≤ i := by simp at hm; omega
        have := Nat.choose_mul (n := i) (k := k+m) (s := k) (by omega)
        rw [mul_assoc, ← Nat.cast_mul, this, Nat.add_sub_cancel_left]
        push_cast; ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      have : i + 1 - k = (i - k) + 1 := by omega
      rw [this, alt]
      by_cases h : i = k
      · subst h; simp
      · have : i - k ≠ 0 := by omega
        simp [this, h]
    · intro j hj; simp at hj ⊢; omega
    · intro j hj hj2
      simp at hj hj2
      by_cases h1 : j < k
      · simp [Nat.choose_eq_zero_of_lt h1]
      · have : i < j := by omega
        simp [Nat.choose_eq_zero_of_lt this]
  · have : i ≠ k := by omega
    rw [if_neg this]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h1 : j ≤ i
    · simp [Nat.choose_eq_zero_of_lt (show j < k by omega)]
    · simp [Nat.choose_eq_zero_of_lt (show i < j by omega)]

def S (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := fun i j => (-1:ℚ)^((i:ℕ)+j) * (Nat.choose i j : ℚ)

lemma inv_eq (N : ℕ) : (pascal N)⁻¹ = S N := by
  apply Matrix.inv_eq_left_inv
  ext i k
  simp only [Matrix.mul_apply, S, pascal, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1:ℚ)^((i:ℕ)+j) * (Nat.choose i j : ℚ) * (Nat.choose j k : ℚ)) (N+1)]
  rw [key N i k (by omega)]
  simp [Fin.ext_iff]

lemma T_eq (n k : ℕ) (h : k ≤ n) : T n k = (-1:ℚ)^(n+k) * n.choose k := by
  simp [T, h, inv_eq, S]

theorem main' : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    T n k = ((n : ℚ) - k + 1) * T (n - 1) (k - 1) + ((k : ℚ) - 1) * T (n - 1) k := by
  intro n k hk hkn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [T_eq _ _ hkn, T_eq _ _ (by omega)]
  by_cases hjm : j + 1 ≤ m
  · rw [T_eq _ _ hjm]
    -- C(m+1,j+1) = C(m,j) + C(m,j+1); (j+1) C(m+1,j+1) = (m+1) C(m,j)
    have h1 : ((m+1).choose (j+1) : ℚ) = m.choose j + m.choose (j+1) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have h2 : ((m.choose (j+1)) : ℚ) * (j+1) = m.choose j * (m - j) := by
      have := Nat.choose_succ_right_eq m j
      have hc : ((m - j : ℕ) : ℚ) = (m:ℚ) - j := by rw [Nat.cast_sub (by omega)]
      rw [← hc]; exact_mod_cast this
    have hp1 : (-1:ℚ)^(m+1+(j+1)) = (-1)^(m+j) := by
      rw [show m+1+(j+1) = m+j+2 by ring, pow_add]; norm_num
    have hp2 : (-1:ℚ)^(m+(j+1)) = -(-1)^(m+j) := by rw [← add_assoc, pow_succ]; ring
    rw [hp1, hp2, h1]; push_cast
    linear_combination ((-1:ℚ)^(m+j)) * h2
  · have hj : j = m := by omega
    subst hj
    rw [T, dif_neg (by omega)]
    simp
end OMA.A130595Proof

open OMA.A130595Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a130595.main := main'
