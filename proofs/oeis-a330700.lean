import OMAStatements.S_oeis_a330700

/-!
# Disproof of A330700 (Spezia's principal-minor comment, 2019)

The comment states: for `n > 1`, `a(n) = |e2(M(n))|`, where `a(n) = (n-1)n(2n^2+4n-1)/6`
and `e2` is the sum of all principal minors of size 2 of the matrix
`M(n)[i,j] = i*j` if `i < 3` or `j < 3`, and `2(i+j) - 4` otherwise (indices `1..n`).

It fails at `n = 2`: `M(2) = [[1,2],[2,4]]`, whose only principal minor of size 2 is
`det M(2) = 1*4 - 2*2 = 0`, so `|e2(M(2))| = 0`, while `a(2) = 1*2*15/6 = 5`.

Both sides are finite computations on numerals, so the kernel settles them.
-/

open OMA.S_oeis_a330700

namespace A330700Disproof

/-- The closed form at `n = 2` is `1 * 2 * 15 / 6 = 5`. -/
theorem a_two : a 2 = 5 := by norm_num [a]

/-- The only principal minor of size 2 of `M(2) = [[1,2],[2,4]]` is `1*4 - 2*2 = 0`. -/
theorem e2_two : e2 (M 2) = 0 := by decide

end A330700Disproof

/-- The printed conjecture at `n = 2` reads `5 = 0`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a330700.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  have e1 : a 2 = 5 := A330700Disproof.a_two
  have e2h : e2 (M 2) = 0 := A330700Disproof.e2_two
  rw [e1, e2h] at h2
  norm_num at h2
