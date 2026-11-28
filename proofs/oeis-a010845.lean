import OMAStatements.S_oeis_a010845

-- Original proof: @LAPRAI. Shorter proof: @dwilfand-sys.

theorem OMA.solution : type_of% @OMA.S_oeis_a010845.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      simp [OMA.S_oeis_a010845.a, Nat.cast_succ] <;> ring
