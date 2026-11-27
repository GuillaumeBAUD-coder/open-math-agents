import OMAStatements.S_oeis_a047239
import Mathlib

-- Problem: A047239: Numbers that are congruent to {1, 2} (mod 6).
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a047239.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of Kimberling's description of A047239.

Every term `a(i)`, `i ≥ 1`, is `1` or `2` modulo `6`, so a sum of three terms is `3, 4, 5` or `0`
modulo `6`; hence `a(n)` is never such a sum and it is a candidate (it exceeds `a(n-1)`).
For even `n` there is no integer strictly between `a(n-1) = 3n-5` and `a(n) = 3n-4`. For odd
`n = 2t+1` the integers strictly between are `6t-3, 6t-2, 6t-1, 6t`, which equal
`a(2t-1)+1+1`, `a(2t-1)+1+2`, `a(2t-1)+2+2` and `a(2t)+2+2` (with `a 1 = 1`, `a 2 = 2`).
-/

namespace A047239Proof

open OMA.S_oeis_a047239

lemma a_mod (i : ℕ) (hi : 1 ≤ i) : a i % 6 = 1 ∨ a i % 6 = 2 := by
  unfold a
  split_ifs <;> omega

lemma a_val (i : ℕ) : a i = if i % 2 = 1 then 3 * i - 2 else 3 * i - 4 := rfl

end A047239Proof

open A047239Proof OMA.S_oeis_a047239

theorem OMA.solution : type_of% @OMA.S_oeis_a047239.main := by
  intro n hn
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [a_val]; split_ifs <;> omega
  · rw [a_val, a_val]; split_ifs <;> omega
  · intro i j k hi hij hjk hkn h
    have h1 := a_mod i hi
    have h2 := a_mod j (by omega)
    have h3 := a_mod k (by omega)
    have h4 := a_mod n (by omega)
    omega
  · rintro m ⟨hm0, hm1, hm2⟩
    by_contra hlt
    rw [not_le] at hlt
    have ha1 : a 1 = 1 := rfl
    have ha2 : a 2 = 2 := rfl
    rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
    · have e1 : a n = 6 * t - 4 := by rw [a_val]; split_ifs <;> omega
      have e2 : a (n - 1) = 6 * t - 5 := by rw [a_val]; split_ifs <;> omega
      omega
    · have ht1 : 1 ≤ t := by omega
      have e1 : a n = 6 * t + 1 := by rw [a_val]; split_ifs <;> omega
      have e2 : a (n - 1) = 6 * t - 4 := by rw [a_val]; split_ifs <;> omega
      have hb : a (2 * t - 1) = 6 * t - 5 := by rw [a_val]; split_ifs <;> omega
      have hc : a (2 * t) = 6 * t - 4 := by rw [a_val]; split_ifs <;> omega
      have key : m = 6 * t - 3 ∨ m = 6 * t - 2 ∨ m = 6 * t - 1 ∨ m = 6 * t := by omega
      rcases key with rfl | rfl | rfl | rfl
      · exact hm2 1 1 (2 * t - 1) le_rfl le_rfl (by omega) (by omega) (by rw [ha1, hb]; omega)
      · rcases Nat.lt_or_ge t 2 with h1 | h2
        · exact hm2 1 1 2 le_rfl (by norm_num) (by norm_num) (by omega)
            (by rw [ha1, ha2]; omega)
        · exact hm2 1 2 (2 * t - 1) le_rfl (by norm_num) (by omega) (by omega)
            (by rw [ha1, ha2, hb]; omega)
      · rcases Nat.lt_or_ge t 2 with h1 | h2
        · exact hm2 1 2 2 le_rfl (by norm_num) le_rfl (by omega)
            (by rw [ha1, ha2]; omega)
        · exact hm2 2 2 (2 * t - 1) (by norm_num) le_rfl (by omega) (by omega)
            (by rw [ha2, hb]; omega)
      · exact hm2 2 2 (2 * t) (by norm_num) le_rfl (by omega) (by omega)
          (by rw [ha2, hc]; omega)
