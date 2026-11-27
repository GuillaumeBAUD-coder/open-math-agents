import OMAStatements.S_oeis_a244628

theorem OMA.solution : type_of% @OMA.S_oeis_a244628.main := by
  intro p hp hmod
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 2 < p), Nat.zero_mod] at h'
    omega
  have hns : ¬ IsSquare (2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_two_iff hp2]
    omega
  have h : (2 : ZMod p) ^ (p / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one p h2 with h1 | h1
    · exact absurd ((ZMod.euler_criterion p h2).2 h1) hns
    · exact h1
  have hk : (p - 1) / 2 = p / 2 := by omega
  have hc : ((2 ^ (p / 2) : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [h, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one]
    ring
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : p - 1 < p)] at hc
  rw [hk]
  exact hc
