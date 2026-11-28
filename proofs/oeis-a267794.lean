import OMAStatements.S_oeis_a267794
import Mathlib

/-!
# A267794: maximal number of successive zeros after a positive term is k

Proof idea. The list terms k n is the list s(0), ..., s(n-1), so the next term is computed from
values of s. When some earlier block matches the last k terms, the largest such index g satisfies
g < n-k, so the term n-k-g is positive. The terms s(0), ..., s(k) are zero, and s(k+1) = 1.

Part 1 uses j = k+1. For n from k+2 to 2k+1 the last k terms contain the only 1, at position k+1,
while every earlier block placed at an index i < n-k has a zero term there, so s(n) = 0. At
n = 2k+2 the last k terms are all zero and match the block at i = 0, so s(2k+2) > 0.

Part 2: if s(j+1), ..., s(j+k) are all zero, then at n = j+k+1 the last block is all zeros and
matches the block at i = 0 < j+1, so s(j+k+1) > 0.
-/

namespace OMA.P267794

open OMA.S_oeis_a267794

lemma length_terms (k n : ℕ) : (terms k n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [terms, ih]

lemma s_eq (k n : ℕ) : s k n = next k (terms k n) := by
  unfold s
  rw [terms, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_terms])]
  simp [length_terms]

lemma getD_terms (k n m : ℕ) (h : m < n) : (terms k n).getD m 0 = s k m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [terms, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_terms]; exact h'),
        ← List.getD_eq_getElem?_getD, ih h']
    · subst h'; rfl

lemma next_spec (k n : ℕ) (h : k ≤ n) (i : ℕ) (hi : i < n - k)
    (hm : ∀ t, t < k → s k (i + t) = s k (n - k + t)) :
    ∃ g, g < n - k ∧ s k n = n - k - g := by
  have hP : ∀ i' t, i' < n - k → t < k →
      ((terms k n).getD (i' + t) 0 = (terms k n).getD ((terms k n).length - k + t) 0 ↔
        s k (i' + t) = s k (n - k + t)) := by
    intro i' t hi' ht
    rw [length_terms, getD_terms k n _ (by omega), getD_terms k n _ (by omega)]
  have hex : ∃ i, i < (terms k n).length - k ∧ ∀ t, t < k →
      (terms k n).getD (i + t) 0 = (terms k n).getD ((terms k n).length - k + t) 0 := by
    refine ⟨i, by rw [length_terms]; exact hi, fun t ht => (hP i t hi ht).mpr (hm t ht)⟩
  have hspec := Nat.findGreatest_spec (P := fun i => i < (terms k n).length - k ∧
          ∀ t, t < k → (terms k n).getD (i + t) 0 = (terms k n).getD ((terms k n).length - k + t) 0)
    (m := i) (n := (terms k n).length - k) (by rw [length_terms]; omega)
      ⟨by rw [length_terms]; exact hi, fun t ht => (hP i t hi ht).mpr (hm t ht)⟩
  refine ⟨Nat.findGreatest (fun i => i < (terms k n).length - k ∧
          ∀ t, t < k → (terms k n).getD (i + t) 0 = (terms k n).getD ((terms k n).length - k + t) 0)
        ((terms k n).length - k), ?_, ?_⟩
  · exact lt_of_lt_of_eq hspec.1 (by rw [length_terms])
  · rw [s_eq]; unfold next
    rw [if_neg (by rw [length_terms]; omega), if_pos hex, length_terms]

lemma next_zero (k n : ℕ) (h : k ≤ n)
    (hno : ∀ i, i < n - k → ∃ t, t < k ∧ s k (i + t) ≠ s k (n - k + t)) : s k n = 0 := by
  rw [s_eq]; unfold next
  rw [if_neg (by rw [length_terms]; omega)]
  rw [if_neg]
  rintro ⟨i, hi, hm⟩
  rw [length_terms] at hi hm
  obtain ⟨t, ht, hne⟩ := hno i hi
  apply hne
  have := hm t ht
  rwa [getD_terms k n _ (by omega), getD_terms k n _ (by omega)] at this

lemma s_small (k m : ℕ) (h : m ≤ k) : s k m = 0 := by
  rcases Nat.lt_or_ge m k with h' | h'
  · rw [s_eq]; unfold next; rw [if_pos (by rw [length_terms]; exact h')]
  · exact next_zero k m h' (fun i hi => by omega)

lemma s_k1 (k : ℕ) : s k (k + 1) = 1 := by
  obtain ⟨g, hg, he⟩ := next_spec k (k + 1) (by omega) 0 (by omega) (fun t ht => by
    rw [s_small k _ (by omega), s_small k _ (by omega)])
  rw [he]; omega

lemma s_mid (k t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ k) : s k (k + 1 + t) = 0 := by
  apply next_zero k _ (by omega)
  intro i hi
  refine ⟨k + 1 - (k + 1 + t - k), by omega, ?_⟩
  rw [s_small k (i + _) (by omega)]
  have : k + 1 + t - k + (k + 1 - (k + 1 + t - k)) = k + 1 := by omega
  rw [this, s_k1]; omega

theorem part2 (k j : ℕ) : ∃ t : ℕ, 1 ≤ t ∧ t ≤ k + 1 ∧ s k (j + t) ≠ 0 := by
  by_cases hz : ∀ t, 1 ≤ t → t ≤ k → s k (j + t) = 0
  · refine ⟨k + 1, by omega, le_refl _, ?_⟩
    obtain ⟨g, hg, he⟩ := next_spec k (j + (k + 1)) (by omega) 0 (by omega) (fun t ht => by
      rw [s_small k _ (by omega)]
      have : j + (k + 1) - k + t = j + (t + 1) := by omega
      rw [this, hz (t + 1) (by omega) (by omega)])
    rw [he]; omega
  · push Not at hz
    obtain ⟨t, h1, h2, h3⟩ := hz
    exact ⟨t, h1, by omega, h3⟩

end OMA.P267794

theorem OMA.solution : type_of% @OMA.S_oeis_a267794.main := by
  intro k hk
  refine ⟨⟨k + 1, by rw [OMA.P267794.s_k1]; omega,
    fun t h1 h2 => OMA.P267794.s_mid k t h1 h2, ?_⟩,
    fun j _ => OMA.P267794.part2 k j⟩
  obtain ⟨g, hg, he⟩ := OMA.P267794.next_spec k (k + 1 + k + 1) (by omega) 0 (by omega)
    (fun t ht => by
      rw [OMA.P267794.s_small k _ (by omega)]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have : k + 1 + k + 1 - k + 0 = k + 1 + 1 := by omega
        rw [this, OMA.P267794.s_mid k 1 (le_refl _) hk]
      · have : k + 1 + k + 1 - k + t = k + 1 + (t + 1) := by omega
        rw [this, OMA.P267794.s_mid k (t + 1) (by omega) (by omega)])
  rw [he]; omega
