import OMAStatements.S_oeis_a007310

-- Credit: @yuka30240
-- Multiplying the mean of the first n fourteenth powers by 90 clears its denominators.
private def numerator {R : Type*} [Ring R] (x : R) : R :=
  6*x^14 + 45*x^13 + 105*x^12 - 273*x^10 + 715*x^8 - 1287*x^6 +
    1365*x^4 - 691*x^2 + 105

private theorem powerSum (n : ℕ) :
    90 * ((∑ k ∈ Finset.Icc 1 n, k^14 : ℕ) : ℤ) = n * numerator (n : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ n.zero_le)]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_succ]
    rw [mul_add, ih]
    unfold numerator
    ring

set_option maxRecDepth 4096 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007310.main := by
  intro n hn
  have residues : ∀ x : ZMod 90, (x.val % 6 = 1 ∨ x.val % 6 = 5) ↔ numerator x = 0 := by
    decide
  rw [← Int.natCast_dvd_natCast, ← mul_dvd_mul_iff_left (by decide : (90 : ℤ) ≠ 0),
    powerSum, mul_comm 90, mul_dvd_mul_iff_left (by positivity : (n : ℤ) ≠ 0)]
  refine Iff.trans ?_ (ZMod.intCast_zmod_eq_zero_iff_dvd _ 90)
  simpa [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 6 ∣ 90), numerator]
    using residues (n : ZMod 90)
