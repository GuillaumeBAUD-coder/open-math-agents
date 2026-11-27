import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1

-- Credit: @jagong-cmu

namespace ErdosMoserH1

open Finset

lemma powerSum_eq_range (k n : ℕ) (hk : 0 < k) :
    ErdosMoser.powerSum k (n + 1) = ∑ i ∈ range (n + 1), i ^ k := by
  unfold ErdosMoser.powerSum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (a := 0) (by omega), Nat.zero_pow hk,
    zero_add]

lemma dvd_two_mul_sum (k n : ℕ) (hk : Odd k) :
    n ∣ 2 * ∑ i ∈ range (n + 1), i ^ k := by
  have h : ∑ i ∈ range (n + 1), (n - i) ^ k = ∑ i ∈ range (n + 1), i ^ k := by
    have := Finset.sum_range_reflect (fun i => i ^ k) (n + 1)
    simpa using this
  rw [two_mul]
  nth_rewrite 1 [← h]
  rw [← Finset.sum_add_distrib]
  apply Finset.dvd_sum
  intro i hi
  have hi' : i ≤ n := by simp at hi; omega
  have := hk.nat_add_dvd_pow_add_pow (n - i) i
  rwa [Nat.sub_add_cancel hi'] at this

theorem h1 : ∀ k m : ℕ, 0 < k → 0 < m → Odd k → ErdosMoser.powerSum k m = m ^ k → k = 1 ∧ m = 3 := by
  intro k m hk hm ho h
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [powerSum_eq_range k n hk] at h
  have hd := dvd_two_mul_sum k n ho
  rw [h] at hd
  have h1 : n ∣ (n + 1) ^ k - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (n + 1) 1 k
    simpa using this
  have hpos : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : n ∣ 2 * (n + 1) ^ k - 2 * ((n + 1) ^ k - 1) := Nat.dvd_sub hd (dvd_mul_of_dvd_right h1 2)
  have h3 : 2 * (n + 1) ^ k - 2 * ((n + 1) ^ k - 1) = 2 := by omega
  rw [h3] at h2
  have hn : n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at h
    omega
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · -- m = 2: the sum is 1, but 2 ^ k is at least 2
    have h2k : 2 ≤ (1 + 1) ^ k := Nat.le_self_pow (by omega) 2
    have hs : ∑ i ∈ range (1 + 1), i ^ k = 1 := by
      simp [Finset.sum_range_succ, Nat.zero_pow hk]
    rw [hs] at h
    omega
  · -- m = 3: 1 + 2 ^ k = 3 ^ k forces k = 1
    have hs : ∑ i ∈ range (2 + 1), i ^ k = 1 + 2 ^ k := by
      simp [Finset.sum_range_succ, Nat.zero_pow hk]
    rw [hs] at h
    refine ⟨?_, by norm_num⟩
    by_contra hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h23 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have e3 : (2 + 1) ^ (j + 2) = 9 * 3 ^ j := by ring
    have e2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    rw [e3, e2] at h
    omega

end ErdosMoserH1

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := ErdosMoserH1.h1
