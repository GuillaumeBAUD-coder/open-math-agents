import OMAStatements.S_oeis_a347365

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: 6n+1 and 6n+5 are odd, so (-1)^m = -1 and a(m) = 3m; then 3m/3 = m.

open OMA.S_oeis_a347365

theorem OMA.solution : type_of% @OMA.S_oeis_a347365.main := by
  intro n
  have h1 : ((-1 : ℤ)) ^ (6 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  have h5 : ((-1 : ℤ)) ^ (6 * n + 5) = -1 := by
    rw [show 6 * n + 5 = 2 * (3 * n + 2) + 1 by ring, pow_succ, pow_mul]; norm_num
  constructor
  · unfold a; rw [h1]; push_cast; omega
  · unfold a; rw [h5]; push_cast; omega
