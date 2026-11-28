import OMAStatements.S_oeis_a364086

-- Problem: A364086: Fixed points of A002326, i.e., numbers k such that A002326(k) = k.
-- Upstream: formal-conjectures statements/oeis-a364086.lean:0 (declaration OMA.S_oeis_a364086.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: 2 is coprime to n = 2k+1, so 2^phi(n) = 1 in ZMod n (Euler) and the order of 2
-- divides phi(n). If the order is 2k, then k > 0 (phi(n) > 0) and 2k <= phi(n) < n = 2k+1,
-- so phi(n) = n - 1 and n is prime; the order condition is then the primitive root condition.
-- The converse is immediate.

open OMA.S_oeis_a364086 in
theorem OMA.solution : type_of% @OMA.S_oeis_a364086.main := by
  intro k
  unfold A002326 HasPrimitiveRoot2
  rw [show 2 * k + 1 - 1 = 2 * k by omega]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have hcop : Nat.Coprime 2 (2 * k + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have h1 : Nat.ModEq (2 * k + 1) (2 ^ Nat.totient (2 * k + 1)) 1 := Nat.ModEq.pow_totient hcop
    have h2 : ((2 ^ Nat.totient (2 * k + 1) : ℕ) : ZMod (2 * k + 1)) = ((1 : ℕ) : ZMod (2 * k + 1)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have h3 : (2 : ZMod (2 * k + 1)) ^ Nat.totient (2 * k + 1) = 1 := by
      push_cast at h2
      exact h2
    have h4 : orderOf (2 : ZMod (2 * k + 1)) ∣ Nat.totient (2 * k + 1) :=
      orderOf_dvd_of_pow_eq_one h3
    rw [h] at h4
    have h5 : 0 < Nat.totient (2 * k + 1) := Nat.totient_pos.mpr (by omega)
    have h6 : 0 < 2 * k := Nat.pos_of_dvd_of_pos h4 h5
    have h7 : 2 * k ≤ Nat.totient (2 * k + 1) := Nat.le_of_dvd h5 h4
    have h8 : Nat.totient (2 * k + 1) < 2 * k + 1 := Nat.totient_lt (2 * k + 1) (by omega)
    exact (Nat.totient_eq_iff_prime (by omega)).mp (by omega)
  · intro h
    exact h.2
