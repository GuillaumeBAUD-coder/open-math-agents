import OMAStatements.S_oeis_a286013
import Mathlib

namespace OMA.S_oeis_a286013

lemma pt (t k : ℕ) : partTotal t k = k * t + firstRow k := by
  simp [partTotal, firstRow, Finset.sum_add_distrib, mul_comm]

lemma iff_t (n k t : ℕ) (hk : 0 < k) :
    partTotal t k = n ↔ firstRow k ≤ n ∧ k ∣ n - firstRow k ∧ t = (n - firstRow k) / k := by
  rw [pt]
  constructor
  · rintro rfl
    refine ⟨by omega, ?_, ?_⟩
    · simp
    · simp [Nat.mul_div_cancel_left _ hk]
  · rintro ⟨h1, ⟨c, hc⟩, rfl⟩
    rw [hc, Nat.mul_div_cancel_left _ hk]
    omega

lemma row (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∑ t ∈ Finset.range n, if partTotal t k = n then t + k else 0) = entry n k := by
  by_cases h : firstRow k ≤ n ∧ k ∣ n - firstRow k
  · have hF : 0 < firstRow k := by
      simp only [firstRow]
      exact Finset.sum_pos (fun i _ => by omega) ⟨0, by simp; omega⟩
    have ht : (n - firstRow k) / k < n := by
      calc (n - firstRow k) / k ≤ n - firstRow k := Nat.div_le_self _ _
        _ < n := by omega
    rw [Finset.sum_eq_single ((n - firstRow k) / k)]
    · rw [if_pos ((iff_t n k _ hk).2 ⟨h.1, h.2, rfl⟩)]
      simp [entry, h.1, h.2, add_comm]
    · intro b _ hb
      rw [if_neg]
      intro hh
      exact hb (((iff_t n k b hk).1 hh).2.2)
    · intro hn; exact absurd (Finset.mem_range.2 ht) hn
  · rw [Finset.sum_eq_zero]
    · simp [entry, h]
    · intro t _
      rw [if_neg]
      intro hh
      have := (iff_t n k t hk).1 hh
      exact h ⟨this.1, this.2.1⟩

end OMA.S_oeis_a286013

open OMA.S_oeis_a286013 in
theorem OMA.solution : type_of% @OMA.S_oeis_a286013.main := by
  refine ⟨?_, ?_⟩
  · intro n k hn hk he
    have hF : firstRow k ≤ n ∧ k ∣ n - firstRow k := by
      by_contra hc
      simp [entry, hc] at he
    refine ⟨(n - firstRow k) / k, ⟨(iff_t n k _ hk).2 ⟨hF.1, hF.2, rfl⟩, ?_⟩, ?_⟩
    · simp [entry, hF.1, hF.2, add_comm]
    · rintro t ⟨h1, _⟩
      exact ((iff_t n k t hk).1 h1).2.2
  · intro n hn
    unfold largestParts
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.1 hj
    exact (row n (j+1) (by omega) (by omega)).symm
