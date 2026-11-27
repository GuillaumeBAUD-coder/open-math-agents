import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

-- Credit: @Hennyrick
-- B. Poonen, Acta Arithmetica 86 (1998), section 4, equation (13).

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1

/-- The difference is a cube prime to five and its quartic cofactor is a cube. -/
def H1 : Prop :=
  ∀ {v s t : Nat}, 0 < v → 0 < s → 0 < t → Nat.Coprime (s^3) v → ¬ 5 ∣ s →
    (if s % 3 = 0 then v % 9 = 2 ∨ v % 9 = 7
     else v % 9 = 0 ∨ (v + s^3) % 9 = 0) →
    let d := s^3
    (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) ≠ t^3

/-- The difference is 25 times a cube and its quartic cofactor is five times a cube. -/
def H2 : Prop :=
  ∀ {v s t : Nat}, 0 < v → 0 < s → 0 < t → Nat.Coprime (25*s^3) v → ¬ 5 ∣ t →
    (if s % 3 = 0 then v % 9 = 1 ∨ v % 9 = 8
     else v % 9 = 3*s^3 % 9 ∨ (v + s^3) % 9 = 0) →
    let d := 25*s^3
    (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) ≠ 5*t^3

open Fin.CommRing

theorem difference_factor (v d : Nat) :
    (v+d)^5 = v^5 + d * (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) := by ring

/-- The only common prime factor of the two integral factors is potentially
5; the equality also determines the entire gcd. -/
theorem gcd_quartic {v d : Nat} (hc : d.Coprime v) :
    Nat.gcd d ((5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3))) = Nat.gcd d 5 := by
  rw [Nat.gcd_add_mul_left_right]
  exact (hc.pow_right 4).symm.gcd_mul_right_cancel_right 5

/-- If 5 divides the difference, the quartic contains exactly one factor of
5. This is independent of whether the original product is a cube. -/
theorem quartic_has_one_five {v d : Nat} (hc : d.Coprime v) (hd : 5 ∣ d) :
    ∃ g : Nat, (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = 5*g ∧ Nat.Coprime (5*d) g := by
  obtain ⟨e,he⟩ := hd
  let g := v^4 + d*(2*v^3+2*v^2*d+v*d^2+25*e^3)
  have hq : (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = 5*g := by dsimp [g]; rw [he]; ring
  have hg : Nat.Coprime d g := by
    change Nat.gcd d (v^4+d*_) = 1
    rw [Nat.gcd_add_mul_left_right]
    exact hc.pow_right 4
  have h5 : Nat.Coprime 5 g := Nat.Coprime.coprime_dvd_left ⟨e,he⟩ hg
  exact ⟨g,hq,h5.mul_left hg⟩

private theorem coprime_cubes {u v w : Nat} (hc : Nat.Coprime u v) (h : u*v=w^3) :
    ∃ s t : Nat, u=s^3 ∧ v=t^3 := by
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow (by simp [gcd_eq_nat_gcd, hc.gcd_eq_one]) h
  have hc' := hc.symm
  obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow (by simp [gcd_eq_nat_gcd, hc'.gcd_eq_one])
    ((Nat.mul_comm _ _).trans h)
  exact ⟨s,t,hs,ht⟩

/-- In Poonen's §4 notation for u⁵+(-v)⁵=w³, the multiplier m of equation
(13) is exactly 1 or 25. The case m=5 disappears because the quartic
factor has exactly one factor of 5 whenever 5 divides the difference. -/
theorem exact_cubic_twists {v d w : Nat} (hc : Nat.Coprime d v)
    (he : (v+d)^5 = v^5+w^3) :
    (¬5 ∣ d ∧ ∃ s t : Nat, d = s^3 ∧ (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = t^3) ∨
    (5 ∣ d ∧ ∃ s t : Nat, d = 25*s^3 ∧ (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = 5*t^3 ∧ ¬5 ∣ t) := by
  have hmul : d*(5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = w^3 := Nat.add_left_cancel
    ((difference_factor v d).symm.trans he)
  by_cases hd : 5 ∣ d
  · right
    refine ⟨hd, ?_⟩
    obtain ⟨g,hq,hc5d⟩ := quartic_has_one_five hc hd
    have hc5 : Nat.Coprime 5 g := hc5d.coprime_mul_right
    have hprod : (5*d)*g=w^3 := by rw [← hmul,hq]; ring
    obtain ⟨s,t,hs,ht⟩ := coprime_cubes hc5d hprod
    have h5s : 5 ∣ s := Nat.prime_five.dvd_of_dvd_pow ⟨d,hs.symm⟩
    obtain ⟨s',hs'⟩ := h5s
    have hd' : d = 25*s'^3 := by rw [hs',Nat.mul_pow] at hs; omega
    have h5t : ¬5 ∣ t := by
      intro htt
      have h5pow : t ∣ t^3 := by simp
      have hgd : 5 ∣ g := ht ▸ htt.trans h5pow
      have hh := hc5.eq_one_of_dvd hgd
      contradiction
    exact ⟨s',t,hd',by rw [hq,ht],h5t⟩
  · left
    refine ⟨hd, ?_⟩
    have h5 : Nat.Coprime d 5 := (Nat.prime_five.coprime_iff_not_dvd.mpr hd).symm
    have hcg : Nat.Coprime d ((5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3))) := by
      change Nat.gcd d (5*v^4 + d*_) = 1
      rw [Nat.gcd_add_mul_left_right]
      exact h5.mul_right (hc.pow_right 4)
    exact coprime_cubes hcg hmul

set_option maxHeartbeats 1000000 in
theorem residues_one {s v t : Nat} (hc : Nat.Coprime s v)
    (h : let d := s^3
         (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = t^3) :
    if s % 3 = 0 then v % 9 = 2 ∨ v % 9 = 7
     else v % 9 = 0 ∨ (v + s^3) % 9 = 0 := by
  have table : ∀ S V T : Fin 9, ¬(S.val % 3 = 0 ∧ V.val % 3 = 0) →
      (let d := S^3
       (5*V^4 + d*(10*V^3+10*V^2*d+5*V*d^2+d^3)) = T^3) →
      (if S.val % 3 = 0 then V.val % 9 = 2 ∨ V.val % 9 = 7
     else V.val % 9 = 0 ∨ (V.val + S.val^3) % 9 = 0) := by decide +kernel
  have hcop : ¬(s % 3 = 0 ∧ v % 3 = 0) := by
    rintro ⟨hs,hv⟩
    have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hs) (Nat.dvd_of_mod_eq_zero hv)
    rw [hc.gcd_eq_one] at hd
    have := Nat.dvd_one.mp hd
    contradiction
  have hfin := congrArg (fun n : Nat => (n : Fin 9)) h
  push_cast at hfin
  have ht := table (s:Fin 9) (v:Fin 9) (t:Fin 9)
    (by simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hcop) hfin
  simp only [Fin.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9),
    Nat.mod_mod] at ht
  have hadd : (v%9 + (s%9)^3) % 9 = (v+s^3)%9 := by
    rw [Nat.add_mod (v%9), Nat.mod_mod, ← Nat.pow_mod, ← Nat.add_mod]
  rw [hadd] at ht
  exact ht

set_option maxHeartbeats 1000000 in
theorem residues_twenty_five {s v t : Nat} (hc : Nat.Coprime s v)
    (h : let d := 25*s^3
         (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) = 5*t^3) :
    if s % 3 = 0 then v % 9 = 1 ∨ v % 9 = 8
     else v % 9 = 3*s^3 % 9 ∨ (v + s^3) % 9 = 0 := by
  have table : ∀ S V T : Fin 9, ¬(S.val % 3 = 0 ∧ V.val % 3 = 0) →
      (let d := 25*S^3
       (5*V^4 + d*(10*V^3+10*V^2*d+5*V*d^2+d^3)) = 5*T^3) →
      (if S.val % 3 = 0 then V.val % 9 = 1 ∨ V.val % 9 = 8
     else V.val % 9 = 3*S.val^3 % 9 ∨ (V.val + S.val^3) % 9 = 0) := by decide +kernel
  have hcop : ¬(s % 3 = 0 ∧ v % 3 = 0) := by
    rintro ⟨hs,hv⟩
    have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hs) (Nat.dvd_of_mod_eq_zero hv)
    rw [hc.gcd_eq_one] at hd
    have := Nat.dvd_one.mp hd
    contradiction
  have hfin := congrArg (fun n : Nat => (n : Fin 9)) h
  push_cast at hfin
  have ht := table (s:Fin 9) (v:Fin 9) (t:Fin 9)
    (by simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hcop) hfin
  simp only [Fin.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9),
    Nat.mod_mod] at ht
  have hadd : (v%9 + (s%9)^3) % 9 = (v+s^3)%9 := by
    rw [Nat.add_mod (v%9), Nat.mod_mod, ← Nat.pow_mod, ← Nat.add_mod]
  rw [hadd] at ht
  have hmul : 3*(s%9)^3 % 9 = 3*s^3 % 9 := by
    rw [Nat.mul_mod 3, ← Nat.pow_mod, ← Nat.mul_mod]
  rw [hmul] at ht
  exact ht

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1.H2 := by
  intro h1 h2 u v w _ hv hw hc he
  have hgt : v < u := by
    apply Nat.lt_of_not_ge
    intro hle
    have := Nat.pow_le_pow_left hle 5
    have := Nat.pow_pos (n := 3) (by omega : 0 < w)
    omega
  let d := u-v
  have hdpos : 0 < d := by dsimp [d]; omega
  have hu : u = v+d := by dsimp [d]; omega
  have hdc : Nat.Coprime d v := by
    change Nat.gcd (u-v) v = 1
    rw [Nat.gcd_sub_self_left hgt.le]
    exact hc
  have hqp : 0 < (5*v^4 + d*(10*v^3+10*v^2*d+5*v*d^2+d^3)) := by have := Nat.pow_pos (n := 4) (by omega : 0 < v); omega
  rcases exact_cubic_twists hdc (hu ▸ he) with ⟨hn,s,t,hs,ht⟩ | ⟨_,s,t,hs,ht,hnt⟩
  · have hsp : 0 < s := by by_contra! h; simp [show s=0 by omega] at hs; omega
    have htp : 0 < t := by by_contra! h; simp [show t=0 by omega] at ht; omega
    have hn' : ¬5 ∣ s := fun h => hn (hs ▸ h.trans (by simp))
    have hsc : s.Coprime v := Nat.Coprime.coprime_dvd_left
      (show s ∣ d by rw [hs]; simp) hdc
    rw [hs] at ht
    exact h1 (by omega) hsp htp (hs ▸ hdc) hn' (residues_one hsc ht) ht
  · have hsp : 0 < s := by by_contra! h; simp [show s=0 by omega] at hs; omega
    have htp : 0 < t := by by_contra! h; simp [show t=0 by omega] at ht; omega
    have hsc : s.Coprime v := Nat.Coprime.coprime_dvd_left
      (show s ∣ d by rw [hs]; exact (show s ∣ s^3 by simp).trans (Nat.dvd_mul_left _ _)) hdc
    rw [hs] at ht
    exact h2 (by omega) hsp htp (hs ▸ hdc) hnt (residues_twenty_five hsc ht) ht

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H2_R1
