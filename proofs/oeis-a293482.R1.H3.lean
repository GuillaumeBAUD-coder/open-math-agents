import OMAReductions.R_oeis_a293482_R1
import Mathlib

-- Step oeis-a293482.R1.H3: hypothesis H3 of reduction oeis-a293482.R1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: for p prime with p % 5 in {2,3,4}, 5 divides neither p nor p - 1, so
-- phi(p^e) = p^(e-1) * (p - 1) is coprime to 5. Hence x -> x^5 is a bijection of
-- (ZMod p^e)ˣ (powCoprime), and a (p^e) = phi(p^e) = (p - 1) * p^(e-1).

open OMA.S_oeis_a293482

namespace A293482H3

theorem card_pow5 (n : ℕ) [NeZero n] (h : Nat.Coprime (Nat.totient n) 5) :
    a n = Nat.totient n := by
  have hcard : Nat.card (ZMod n)ˣ = Nat.totient n := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hc : Nat.Coprime (Nat.card (ZMod n)ˣ) 5 := by rw [hcard]; exact h
  have hs : Function.Surjective (fun x : (ZMod n)ˣ => x ^ 5) := by
    intro y
    exact ⟨(powCoprime hc).symm y, by
      simpa [powCoprime_apply] using (powCoprime hc).apply_symm_apply y⟩
  unfold a
  rw [hs.range_eq, Nat.card_univ, hcard]

theorem cop5 (m : ℕ) (h : ¬ 5 ∣ m) : Nat.Coprime m 5 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h)

end A293482H3

theorem OMA.solution : OMA.R_oeis_a293482_R1.H3 := by
  intro p e hp hmod he
  have h2 := hp.two_le
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : Nat.Coprime (Nat.totient (p ^ e)) 5 := by
    rw [Nat.totient_prime_pow hp he]
    refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (A293482H3.cop5 _ ?_))
      (A293482H3.cop5 _ ?_) <;> omega
  rw [A293482H3.card_pow5 _ hcop, Nat.totient_prime_pow hp he, mul_comm]
