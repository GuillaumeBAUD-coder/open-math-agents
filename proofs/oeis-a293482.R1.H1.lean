import OMAReductions.R_oeis_a293482_R1
import Mathlib

-- Step oeis-a293482.R1.H1: hypothesis H1 of reduction oeis-a293482.R1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: phi(2^e) is a power of 2, hence coprime to 5, so x -> x^5 is a bijection
-- of (ZMod 2^e)ˣ (powCoprime). The range is everything, so a (2^e) = phi(2^e), which is
-- 1 for e <= 1 and 2^(e-1) for e >= 1.

open OMA.S_oeis_a293482

namespace A293482H1

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

theorem cop2 (e : ℕ) : Nat.Coprime (Nat.totient (2 ^ e)) 5 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two he]
    norm_num
    exact Nat.Coprime.pow_left _ (by norm_num)

end A293482H1

theorem OMA.solution : OMA.R_oeis_a293482_R1.H1 := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [A293482H1.card_pow5 _ (A293482H1.cop2 e)]
    interval_cases e <;> simp
  · rw [A293482H1.card_pow5 _ (A293482H1.cop2 e), Nat.totient_prime_pow Nat.prime_two he]
    simp
