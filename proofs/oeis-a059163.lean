import OMAStatements.S_oeis_a059163
import Mathlib

open OMA.S_oeis_a059163

theorem OMA.solution : type_of% @OMA.S_oeis_a059163.main := by
  intro n
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  set r := ruler (n / 3 + 1) with hr
  have hr1 : 1 ≤ r := by simp [hr, ruler]
  obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  unfold a A059129 element' element phrase
  rw [← hr, hs]
  interval_cases h : n % 3 <;> simp [List.sum_cons, pow_succ] <;> ring
