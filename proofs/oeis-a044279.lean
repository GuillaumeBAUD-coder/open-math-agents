import OMAStatements.S_oeis_a044279

/-!
# The digit-sum conjecture for OEIS A044279

Sequence by Clark Kimberling. Conjecture by Harvey P. Dale.
Source: https://oeis.org/A044279
Credit: @ptlom (with Codex)

Mathlib lists digits from least to most significant, so [1, 3] represents
the substring 31 in the usual base-nine notation. The digit sum is decimal.
If the final base-nine digit is at least two, subtracting one preserves
every earlier digit. Any occurrence of 31 must then also occur in k - 1.
The remaining final digits, zero and one, give the two residues modulo nine.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a044279.main := by
  intro k hk occurs absent
  have digitSum := Nat.modEq_digits_sum 9 10 (by decide) k
  change k % 9 = _ at digitSum
  rw [← digitSum]
  by_contra! rem
  apply absent
  rw [Nat.digits_def' (by decide : 1 < 9) hk] at occurs
  rw [Nat.digits_def' (by decide : 1 < 9) (by omega : 0 < k - 1),
    show (k - 1) / 9 = k / 9 by omega]
  apply List.infix_cons
  rcases List.infix_cons_iff.mp occurs with head | tail
  · have := (List.cons_prefix_cons.mp head).1
    omega
  · exact tail
