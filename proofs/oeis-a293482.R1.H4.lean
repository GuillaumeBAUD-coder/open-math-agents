import OMAReductions.R_oeis_a293482_R1
import Mathlib

-- Step oeis-a293482.R1.H4: hypothesis H4 of reduction oeis-a293482.R1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: for an odd prime p, (ZMod p^e)ˣ is cyclic (ZMod.isCyclic_units_of_prime_pow),
-- so the image of x -> x^5 is the range of powMonoidHom 5, of card phi / gcd(phi, 5)
-- (IsCyclic.card_powMonoidHom_range). For p % 5 = 1, 5 divides p - 1, hence divides
-- phi(p^e) = p^(e-1) * (p - 1), so gcd = 5 and a (p^e) = (p - 1) * p^(e-1) / 5.

open OMA.S_oeis_a293482

namespace A293482H4

theorem card_cyc (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    a (p ^ e) = Nat.totient (p ^ e) / (Nat.totient (p ^ e)).gcd 5 := by
  have := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard : Nat.card (ZMod (p ^ e))ˣ = Nat.totient (p ^ e) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hs : Set.range (fun x : (ZMod (p ^ e))ˣ => x ^ 5) =
      ((powMonoidHom 5 : (ZMod (p ^ e))ˣ →* (ZMod (p ^ e))ˣ).range : Set _) := by
    rw [MonoidHom.coe_range]; rfl
  unfold a
  rw [hs]
  have := IsCyclic.card_powMonoidHom_range (G := (ZMod (p ^ e))ˣ) 5
  rw [hcard] at this
  exact this

end A293482H4

theorem OMA.solution : OMA.R_oeis_a293482_R1.H4 := by
  intro p e hp hmod he
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hmod
  have h2 := hp.two_le
  rw [A293482H4.card_cyc p e hp hp2, Nat.totient_prime_pow hp he]
  have hd : 5 ∣ p ^ (e - 1) * (p - 1) :=
    Dvd.dvd.mul_left (by omega) _
  rw [Nat.gcd_eq_right hd, mul_comm]
