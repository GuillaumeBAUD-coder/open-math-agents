import OMAStatements.S_oeis_a004767
import Mathlib

/-!
# OEIS A004767: odd `m` whose Collatz successor `(3m+1)/2` is odd and larger

Write the odd number `m` as `2j + 1`. Then `(3m + 1)/2 = 3j + 2`, which always exceeds `m`
and is odd exactly when `j` is odd, i.e. when `m = 4n + 3`.
-/

open OMA.S_oeis_a004767

theorem OMA.solution : type_of% @OMA.S_oeis_a004767.main := by
  intro m hm
  obtain ⟨j, rfl⟩ := hm
  have hval : (3 * (2 * j + 1) + 1) / 2 = 3 * j + 2 := by omega
  rw [hval]
  unfold a
  constructor
  · rintro ⟨⟨i, hi⟩, -⟩
    exact ⟨j / 2, by omega⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨3 * n + 2, by omega⟩, by omega⟩
