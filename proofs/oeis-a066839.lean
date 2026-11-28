import OMAStatements.S_oeis_a066839
import Mathlib

namespace OMA.P066839

open OMA.S_oeis_a066839 Finset

/-- m + (m+2) + ... + (m + 2(k-1)) = k*(m + k) - k. -/
lemma sum_form (k m : ℕ) : ∑ i ∈ range k, (m + 2 * i) + k = k * (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : (k + 1) * (m + (k + 1)) = k * (m + k) + m + 2 * k + 1 := by ring
    omega

end OMA.P066839

theorem OMA.solution : type_of% @OMA.S_oeis_a066839.main := by
  intro n hn
  unfold OMA.S_oeis_a066839.a OMA.S_oeis_a066839.totalParts
  symm
  apply Finset.sum_nbij' (fun p : ℕ × ℕ => p.1) (fun k : ℕ => (k, n / k + 1 - k))
  · -- forward membership
    rintro ⟨k, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hk1, hkn⟩, hm1, hmn⟩, hs⟩ := hp
    have h := OMA.P066839.sum_form k m
    rw [hs] at h
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, by omega⟩, ?_⟩
    · have hd : k ∣ n + k := ⟨m + k, h⟩
      exact (Nat.dvd_add_self_right).mp hd
    · nlinarith
  · -- backward membership
    intro k hk
    simp only [Finset.mem_filter, Nat.mem_divisors] at hk
    obtain ⟨⟨hdvd, hn0⟩, hkk⟩ := hk
    have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hdvd (by omega)
    obtain ⟨q, rfl⟩ := hdvd
    have hq : k * q / k = q := Nat.mul_div_cancel_left q hkpos
    have hkq : k ≤ q := Nat.le_of_mul_le_mul_left hkk hkpos
    have hqn : q ≤ k * q := Nat.le_mul_of_pos_left q hkpos
    have hkn : k ≤ k * q := by nlinarith
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    rw [hq]
    refine ⟨⟨⟨hkpos, hkn⟩, by omega, by omega⟩, ?_⟩
    have h := OMA.P066839.sum_form k (q + 1 - k)
    have e : q + 1 - k + k = q + 1 := by omega
    rw [e] at h
    have e2 : k * (q + 1) = k * q + k := by ring
    omega
  · -- left inverse
    rintro ⟨k, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hk1, hkn⟩, hm1, hmn⟩, hs⟩ := hp
    have h := OMA.P066839.sum_form k m
    rw [hs] at h
    have hn' : n = k * (m + k - 1) := by
      have e : k * (m + k) = k * (m + k - 1) + k := by
        have : m + k = (m + k - 1) + 1 := by omega
        rw [this, Nat.mul_succ]
        simp
      omega
    have hdiv : n / k = m + k - 1 := by
      rw [hn']
      exact Nat.mul_div_cancel_left _ (by omega)
    simp only [Prod.mk.injEq, true_and]
    omega
  · -- right inverse
    intro k hk
    rfl
  · -- values
    rintro ⟨k, m⟩ hp
    rfl
