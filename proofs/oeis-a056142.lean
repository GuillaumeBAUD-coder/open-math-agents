import OMAStatements.S_oeis_a056142

/-!
The statement fails for `n = 121`: its decimal word is `[1, 2, 1]`, whose prefix word
`[1, 2, 1] ++ [1, 2] ++ [1] = [1, 2, 1, 1, 2, 1]` is a palindrome, although the digits `1` and `2`
of `121` differ.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a056142.main) := by
  intro h
  have hw : OMA.S_oeis_a056142.decimalWord 121 = [1, 2, 1] := by
    simp [OMA.S_oeis_a056142.decimalWord]
  have h12 := h 121 (by rw [hw]; decide)
    (by rw [hw]; decide) 1 (by rw [hw]; decide) 2 (by rw [hw]; decide)
  exact absurd h12 (by decide)
