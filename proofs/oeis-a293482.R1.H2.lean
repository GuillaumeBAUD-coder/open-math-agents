import OMAReductions.R_oeis_a293482_R1
import Mathlib

-- Step oeis-a293482.R1.H2: hypothesis H2 of reduction oeis-a293482.R1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: (ZMod 5^e)ˣ is cyclic (ZMod.isCyclic_units_of_prime_pow), so the image of
-- x -> x^5 has card phi / gcd(phi, 5) (IsCyclic.card_powMonoidHom_range). For e = 1,
-- phi = 4 and gcd(4, 5) = 1, giving 4. For e >= 2, phi = 5^(e-1) * 4 is divisible by 5,
-- so gcd = 5 and a (5^e) = 4 * 5^(e-2).

open OMA.S_oeis_a293482

namespace A293482H2

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

end A293482H2

theorem OMA.solution : OMA.R_oeis_a293482_R1.H2 := by
  have hp : Nat.Prime 5 := Nat.prime_five
  refine ⟨?_, ?_⟩
  · have := A293482H2.card_cyc 5 1 hp (by norm_num)
    rw [pow_one] at this
    rw [this, Nat.totient_prime hp]; decide
  · intro e he
    rw [A293482H2.card_cyc 5 e hp (by norm_num), Nat.totient_prime_pow hp (by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
    have h1 : k + 2 - 1 = k + 1 := by omega
    have h2 : k + 2 - 2 = k := by omega
    rw [h1, h2, pow_succ]
    have hd : 5 ∣ 5 ^ k * 5 * (5 - 1) := ⟨5 ^ k * 4, by ring⟩
    rw [Nat.gcd_eq_right hd]
    have : 5 ^ k * 5 * (5 - 1) = (4 * 5 ^ k) * 5 := by ring
    rw [this, Nat.mul_div_cancel _ (by norm_num)]
