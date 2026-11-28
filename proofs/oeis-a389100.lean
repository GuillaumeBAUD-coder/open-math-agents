import OMAStatements.S_oeis_a389100
import Mathlib

/-
A389100: every term of A387054 is a term of A389100.

k lies in a bad interval [a, b] and k itself is not in A070003. If a < b we are done. If a = b
then k = a and the product over the interval is k, so k would be in A070003.
-/

namespace OMA.P389100

lemma main' (P : ℕ → Prop) : ∀ k : ℕ,
    ((∃ a b : ℕ, (1 ≤ a ∧ a ≤ b ∧ P (∏ i ∈ Finset.Icc a b, i)) ∧ a ≤ k ∧ k ≤ b) ∧ ¬ P k) →
      ∃ a b : ℕ, (1 ≤ a ∧ a ≤ b ∧ P (∏ i ∈ Finset.Icc a b, i)) ∧ a < b ∧ a ≤ k ∧ k ≤ b := by
  rintro k ⟨⟨a, b, hbad, hak, hkb⟩, hk⟩
  refine ⟨a, b, hbad, lt_of_le_of_ne (hak.trans hkb) ?_, hak, hkb⟩
  rintro rfl
  obtain rfl : k = a := le_antisymm hkb hak
  exact hk (by simpa using hbad.2.2)

end OMA.P389100

theorem OMA.solution : type_of% @OMA.S_oeis_a389100.main := OMA.P389100.main' OMA.S_oeis_a389100.SqGpfDvd
