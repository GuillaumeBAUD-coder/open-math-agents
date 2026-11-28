import OMAStatements.S_oeis_a276674

open Nat ArithmeticFunction

lemma t : ∀ n, φ (2 * n) ≤ n
  | 0 => .refl
  | n + 1 => by
    rcases (n + 1).even_or_odd with ⟨j, hj⟩ | h
    · simp [hj, ← two_mul, totient_two_mul_of_even, t j]
    · simp [totient_two_mul_of_odd h, totient_le]

theorem OMA.solution : type_of% @OMA.S_oeis_a276674.main := by
  intro x m _ _ h
  if hs : 2 < x then
    obtain ⟨c, hc⟩ := (neg_one_pow_eq_one_iff_even fun h =>
      @ZMod.neg_one_ne_one x ⟨hs⟩ (Units.ext_iff.1 h)).1 (pow_carmichael _)
    obtain ⟨j, rfl⟩ : 2 ∣ x := by omega
    have := t j
    have := le_of_dvd (by simp; omega) (carmichael_dvd_totient (2 * j))
    omega
  else omega
