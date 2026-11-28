import OMAStatements.S_oeis_a100873

theorem OMA.solution : type_of% @OMA.S_oeis_a100873.main := by
  intro p _ hq
  have := Fact.mk hq
  have h : ((p ^ (p + 2) + 2 : ℕ) : ZMod (p + 2)) = 0 := by
    push_cast
    rw [ZMod.pow_card]
    have e : ((p : ZMod (p + 2)) + 2) = ((p + 2 : ℕ) : ZMod (p + 2)) := by push_cast; ring
    rw [e, ZMod.natCast_self]
  exact (ZMod.natCast_eq_zero_iff _ _).mp h
