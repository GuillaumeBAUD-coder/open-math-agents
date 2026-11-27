import OMAStatements.S_oeis_a197918
import Mathlib

/-! In the last five binary digits, a forbidden common bit with 22 either
puts all the bits of the prime 5 in p, or all those of the prime 17 in p. -/
namespace Deldor14.XorPrimes
open OMA.S_oeis_a197918
private theorem split_xor (p q : ℕ) (hq : q<32) :
    p ^^^ q = 32*(p/32) + (p%32 ^^^ q) := by
  have m := Nat.xor_mod_two_pow (a:=p) (b:=q) (n:=5)
  have d := Nat.xor_div_two_pow (a:=p) (b:=q) (n:=5)
  change (p ^^^ q)%32 = (p%32 ^^^ q%32) at m
  change (p ^^^ q)/32 = (p/32 ^^^ q/32) at d
  rw [Nat.mod_eq_of_lt hq] at m
  rw [Nat.div_eq_of_lt hq,Nat.xor_zero] at d
  omega
theorem result : type_of% @OMA.S_oeis_a197918.main := by
  intro p term p2 p5 p17
  obtain ⟨_,low,avoid⟩ := term
  have h4 : p%4=1 := low.resolve_left p2
  let r : Fin 32 := ⟨p%32,Nat.mod_lt _ (by decide)⟩
  have tab : ∀ i : Fin 32, i.val%4=1 →
      (i.val ^^^ 22)=i.val+22 ∨ (5 ≤ i.val ∧ (i.val ^^^ 5)+5=i.val) ∨
      (17 ≤ i.val ∧ (i.val ^^^ 17)+17=i.val) := by decide +kernel
  have h := tab r (by simpa only [r,Nat.mod_mod_of_dvd _ (by decide : 4∣32)] using h4)
  change (p%32 ^^^ 22)=p%32+22 ∨ (5≤p%32 ∧ (p%32 ^^^ 5)+5=p%32) ∨
      (17≤p%32 ∧ (p%32 ^^^ 17)+17=p%32) at h
  rcases h with good | ⟨lo,bad⟩ | ⟨lo,bad⟩
  · rw [split_xor p 22 (by decide),good]
    omega
  · exfalso
    apply avoid 5 (by decide) (by omega)
    rw [split_xor p 5 (by decide)]
    omega
  · exfalso
    apply avoid 17 (by decide) (by omega)
    rw [split_xor p 17 (by decide)]
    omega
end Deldor14.XorPrimes
theorem OMA.solution : type_of% @OMA.S_oeis_a197918.main := Deldor14.XorPrimes.result
