import OMAStatements.S_oeis_a002716

open OMA.S_oeis_a002716 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002716.main := by
  have key (n : ℕ) : a (2*n) = 2^2^(n+1) - 2^2^n + 1 ∧ a (2*n+1) = 2^2^(n+1) + 1 := by
    induction n with
    | zero => simp [a]
    | succ n ih =>
      simp [a, mul_add, pow_succ, pow_mul, ih]
      constructor <;> ring
  exact fun n => (key n).2
