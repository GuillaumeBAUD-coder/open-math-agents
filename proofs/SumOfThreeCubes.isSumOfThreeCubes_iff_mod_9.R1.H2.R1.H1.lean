import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Factorization.Induction

/-!
The finite-congruence counterpart of Colliot-Thélène and Wittenberg's
p-adic solubility theorem (Lemma 4.5, arXiv:0911.3539) is separated from
the integral local-global implication. Their theorem identifies the only
exception as the 3-adic obstruction at 4 or 5 modulo 9.
The preceding split into necessity and sufficiency is due to @ihateSAS.
-/

namespace OMA.ThreeCubesLocal
open Finset
open scoped Pointwise

theorem prime_field (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    ∃ x y z : ZMod p, x ≠ 0 ∧ a=x^3+y^3+z^3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let S : Finset (ZMod p) := univ.image (fun x : ZMod p => x^3)
  have hz : 0 ∈ S := mem_image.mpr ⟨0,mem_univ _,by simp⟩
  have fibers (b : ZMod p) :
      (((univ : Finset (ZMod p)).erase 0).filter (fun x => x^3=b)).card ≤ 3 := by
    apply le_trans (card_le_card (t := (Polynomial.nthRoots 3 b).toFinset) ?_)
    · exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    · intro x hx
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide : 0<3)).mpr (mem_filter.mp hx).2)
  have count := Finset.card_le_mul_card_image_of_maps_to
    (f := fun x : ZMod p => x^3) (s := (univ : Finset (ZMod p)).erase 0)
    (t := S.erase 0) (fun x hx => mem_erase.mpr
      ⟨pow_ne_zero _ (mem_erase.mp hx).1,mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩)
    3 (fun b _ => fibers b)
  rw [card_erase_of_mem (mem_univ _),card_univ,ZMod.card,card_erase_of_mem hz] at count
  have hs : S.Nonempty := ⟨0,hz⟩
  have hspos := card_pos.mpr hs
  have hp0 := hp.pos
  have hc1 := ZMod.cauchy_davenport hp hs hs
  have hss : (S+S).Nonempty := ⟨0,by simpa using (Finset.add_mem_add hz hz)⟩
  have hc2 := ZMod.cauchy_davenport hp hss hs
  have hc : (S+S+S).card = Fintype.card (ZMod p) := by
    apply le_antisymm (Finset.card_le_univ _)
    rw [ZMod.card]
    omega
  have cover : S+S+S = univ := (Finset.card_eq_iff_eq_univ _).mp hc
  by_cases ha : a=0
  · exact ⟨1,-1,0,one_ne_zero,by rw [ha]; ring⟩
  have haS : a ∈ S+S+S := cover ▸ mem_univ _
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_add.mp haS
  obtain ⟨s,hs,t,ht,hst⟩ := Finset.mem_add.mp hu
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hs
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp ht
  obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hv
  have he : a=x^3+y^3+z^3 := by rw [hx,hy,hz,hst,huv]
  by_cases hxn : x=0
  · by_cases hyn : y=0
    · have hzn : z ≠ 0 := by intro e; simp [hxn,hyn,e] at he; exact ha he
      exact ⟨z,x,y,hzn,by simpa [hxn,hyn,add_comm] using he⟩
    · exact ⟨y,x,z,hyn,by simpa only [add_comm (x^3)] using he⟩
  · exact ⟨x,y,z,hxn,he⟩

end OMA.ThreeCubesLocal

namespace OMA.ThreeCubesLocal

theorem good_power (p : ℕ) (hp : p.Prime) (h3 : p≠3) (n : ℤ) (e : ℕ) :
    ∃ x y z w : ℤ, (x : ZMod p) ≠ 0 ∧ n=x^3+y^3+z^3+(p:ℤ)^(e+1)*w := by
  letI : Fact p.Prime := ⟨hp⟩
  induction e with
  | zero =>
    obtain ⟨a,b,c,ha,hs⟩ := prime_field p hp (n : ZMod p)
    have hd : (p:ℤ) ∣ n-(a.val:ℤ)^3-(b.val:ℤ)^3-(c.val:ℤ)^3 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      simpa [ZMod.natCast_zmod_val,hs] using
        (show a^3+b^3+c^3-a^3-b^3-c^3=0 by ring)
    obtain ⟨w,hw⟩ := hd
    exact ⟨a.val,b.val,c.val,w,by simpa using ha,by simp only [Nat.zero_add,pow_one]; omega⟩
  | succ e ih =>
    obtain ⟨x,y,z,w,hx,hw⟩ := ih
    have hthree : (3:ZMod p) ≠ 0 := by
      intro h
      rcases (Nat.dvd_prime Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff 3 p).mp h) with e|e
      · exact hp.ne_one e
      · exact h3 e
    have hunit : (3*(x:ZMod p)^2) ≠ 0 := mul_ne_zero hthree (pow_ne_zero _ hx)
    let b : ℤ := ((w : ZMod p)/(3*(x : ZMod p)^2)).val
    have hb : (b : ZMod p)=(w:ZMod p)/(3*(x:ZMod p)^2) := by simp [b]
    have hdiv : (p:ℤ) ∣ w-3*x^2*b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hb]
      field_simp [hunit] <;> ring
    obtain ⟨l,hl⟩ := hdiv
    let D : ℤ := (p:ℤ)^e
    have hpow : (p:ℤ)^(e+1)=(p:ℤ)*D := pow_succ' _ _
    have hpow' : (p:ℤ)^(e+1+1)=(p:ℤ)*((p:ℤ)*D) := by rw [pow_succ',hpow]
    rw [hpow] at hw
    refine ⟨x+(p:ℤ)*D*b,y,z,l-3*x*D*b^2-(p:ℤ)*D^2*b^3,?_,?_⟩
    · simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
        zero_mul,add_zero] using hx
    · rw [hpow',hw]
      linear_combination ((p:ℤ)*D)*hl

theorem base_nine (n : ℤ) (hn : ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) :
    ∃ x y z w : ℤ, (x : ZMod 3) ≠ 0 ∧ n=x^3+y^3+z^3+9*w := by
  have table : ∀ a : ZMod 9, a≠4 → a≠5 →
      ∃ x y z : ZMod 9, x.val%3≠0 ∧ a=x^3+y^3+z^3 := by decide +kernel
  have h4 : (n:ZMod 9) ≠ 4 := fun h =>
    hn (Or.inl ((ZMod.intCast_eq_intCast_iff n 4 9).mp h))
  have h5 : (n:ZMod 9) ≠ 5 := fun h =>
    hn (Or.inr ((ZMod.intCast_eq_intCast_iff n 5 9).mp h))
  obtain ⟨a,b,c,ha,hs⟩ := table (n:ZMod 9) h4 h5
  have hd : (9:ℤ) ∣ n-(a.val:ℤ)^3-(b.val:ℤ)^3-(c.val:ℤ)^3 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    push_cast
    simpa [ZMod.natCast_zmod_val,hs] using
      (show a^3+b^3+c^3-a^3-b^3-c^3=0 by ring)
  obtain ⟨w,hw⟩ := hd
  refine ⟨a.val,b.val,c.val,w,?_,by omega⟩
  change (a.val : ZMod 3) ≠ 0
  exact fun h => ha (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h))

theorem three_power (n : ℤ) (hn : ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) (e : ℕ) :
    ∃ x y z w : ℤ, (x : ZMod 3) ≠ 0 ∧ n=x^3+y^3+z^3+(3:ℤ)^(e+2)*w := by
  induction e with
  | zero => exact base_nine n hn
  | succ e ih =>
    obtain ⟨x,y,z,w,hx,hw⟩ := ih
    have sq : ∀ a : ZMod 3, a ≠ 0 → a^2=1 := by decide
    have hdiv : (3:ℤ) ∣ w-x^2*w := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      push_cast
      rw [sq _ hx,one_mul,sub_self]
    obtain ⟨l,hl⟩ := hdiv
    let D : ℤ := 3^e
    have hpow : (3:ℤ)^(e+2)=9*D := by rw [pow_add]; dsimp only [D]; ring
    have hpow' : (3:ℤ)^(e+1+2)=27*D := by
      rw [show e+1+2=(e+2)+1 by omega,pow_succ',hpow]; ring
    rw [hpow] at hw
    refine ⟨x+3*D*w,y,z,l-D*x*w^2-D^2*w^3,?_,?_⟩
    · simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,show (3:ZMod 3)=0 by decide,
        zero_mul,add_zero] using hx
    · rw [hpow',hw]
      linear_combination (9*D)*hl

end OMA.ThreeCubesLocal

namespace OMA.ThreeCubesLocal

theorem from_integers {m : ℕ} {n x y z w : ℤ} (h : n=x^3+y^3+z^3+(m:ℤ)*w) :
    ∃ a b c : ZMod m, (n:ZMod m)=a^3+b^3+c^3 := by
  refine ⟨x,y,z,?_⟩
  rw [h]
  push_cast
  simp

theorem all_moduli (n : ℤ) (hn : ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) :
    ∀ m : ℕ, 0<m → ∃ x y z : ZMod m, (n:ZMod m)=x^3+y^3+z^3 := by
  apply Nat.recOnPrimeCoprime
  · intro hm; omega
  · intro p e hp hm
    rcases e with _|e
    · change ∃ x y z : ZMod 1, (n:ZMod 1)=x^3+y^3+z^3
      exact ⟨0,0,0,Subsingleton.elim _ _⟩
    by_cases h3 : p=3
    · subst p
      cases e with
      | zero =>
        obtain ⟨x,y,z,_,h⟩ := prime_field 3 Nat.prime_three (n:ZMod 3)
        change ∃ x y z : ZMod 3, (n:ZMod 3)=x^3+y^3+z^3
        exact ⟨x,y,z,h⟩
      | succ e =>
        obtain ⟨x,y,z,w,_,h⟩ := three_power n hn e
        apply from_integers (x:=x) (y:=y) (z:=z) (w:=w)
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
    · obtain ⟨x,y,z,w,_,h⟩ := good_power p hp h3 n e
      apply from_integers (x:=x) (y:=y) (z:=z) (w:=w)
      simpa only [Nat.cast_pow] using h
  · intro a b ha hb hab hA hB _
    obtain ⟨x,y,z,h⟩ := hA (by omega)
    obtain ⟨x',y',z',h'⟩ := hB (by omega)
    let E := ZMod.chineseRemainder hab
    refine ⟨E.symm (x,x'),E.symm (y,y'),E.symm (z,z'),E.injective ?_⟩
    simp only [map_intCast,map_add,map_pow,RingEquiv.apply_symm_apply]
    exact Prod.ext h h'

theorem local_criterion (n : ℤ) :
    (∀ m : ℕ, 0<m → ∃ x y z : ZMod m, (n:ZMod m)=x^3+y^3+z^3) ↔
    ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) := by
  refine ⟨?_,all_moduli n⟩
  intro h hn
  obtain ⟨x,y,z,he⟩ := h 9 (by decide)
  have obstruction : ∀ a b c : ZMod 9, a^3+b^3+c^3 ≠ 4 ∧ a^3+b^3+c^3 ≠ 5 := by decide +kernel
  rcases hn with h4|h5
  · exact (obstruction x y z).1 (he.symm.trans ((ZMod.intCast_eq_intCast_iff n 4 9).mpr h4))
  · exact (obstruction x y z).2 (he.symm.trans ((ZMod.intCast_eq_intCast_iff n 5 9).mpr h5))

end OMA.ThreeCubesLocal

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1_H2_R1.H1 := OMA.ThreeCubesLocal.local_criterion
