import FormalConjectures.ErdosProblems.«1085»
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Repeated distances in a three-dimensional lattice

For every odd prime p there are exactly p(p+1) vectors of square length -1
modulo p. Combine these local counts by the Chinese remainder theorem over
small odd primes. Among the compatible lattice vectors in a cube, some exact
squared length occurs unusually often. Translating the corresponding
displacements gives the logarithmic enhancement of the cubic-grid bound.
-/

/- A finite lower Euler-product estimate obtained by writing each integer as
a square times a squarefree number. Its prime factors will be the moduli used
for the three-dimensional lattice construction. -/

namespace OMA.Mertens1085

open Filter Finset Real

private lemma inv_sq_sum (k : ℕ) :
    ∑ a ∈ Icc 1 k, ((a : ℝ)^2)⁻¹ ≤ 2 - (k:ℝ)⁻¹ := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
    push_cast at *
    have hk : 0 < (k:ℝ)+1 := by positivity
    by_cases hz : k = 0
    · subst k; norm_num
    have hl : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hz
    have diff : (((k:ℝ)+1)^2)⁻¹ ≤ (k:ℝ)⁻¹ - ((k:ℝ)+1)⁻¹ := by
      field_simp
      nlinarith
    linarith

private lemma harmonic_le_product (k : ℕ) :
    Real.log ((k+1:ℕ):ℝ) ≤ 2 * ∏ p ∈ k.primesLE, (1+1/(p:ℝ)) := by
  classical
  choose sqfree root factor free using Nat.sq_mul_squarefree
  let code (n : ℕ) := (root n,(sqfree n).primeFactors)
  let eval (z : ℕ × Finset ℕ) : ℕ := z.1^2 * ∏ p ∈ z.2, p
  have decode_code (n : ℕ) : eval (code n) = n := by
    simpa only [eval,code,Nat.prod_primeFactors_of_squarefree (free n)] using factor n
  let ds := Icc 1 k
  let ps := k.primesLE.powerset
  have map {n} (hn : n ∈ ds) : code n ∈ ds ×ˢ ps := by
    obtain ⟨hn1,hn2⟩ := Finset.mem_Icc.mp hn
    have hnpos : 0 < (root n)^2 * sqfree n := by rw [factor]; omega
    have hs : 0 < root n := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hnpos
    have hq : 0 < sqfree n := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hnpos
    have hsle : root n ≤ n := by
      exact ((Nat.le_self_pow (by decide : (2:ℕ) ≠ 0) _).trans
        (Nat.le_mul_of_pos_right _ hq)).trans_eq (factor n)
    have hqle : sqfree n ≤ n := (Nat.le_mul_of_pos_left _ (pow_pos hs 2)).trans_eq (factor n)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hs,hsle.trans hn2⟩,Finset.mem_powerset.mpr ?_⟩
    intro p hp
    apply Nat.mem_primesLE.mpr
    exact ⟨(Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)).trans (hqle.trans hn2),
      Nat.prime_of_mem_primeFactors hp⟩
  let weight (z : ℕ × Finset ℕ) : ℝ := ((eval z : ℝ))⁻¹
  have H : Real.log ((k+1:ℕ):ℝ) ≤ ∑ n ∈ ds, weight (code n) := by
    simpa only [ds,weight,decode_code,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using log_add_one_le_harmonic k
  have embed : ∑ n ∈ ds, weight (code n) ≤ ∑ z ∈ ds ×ˢ ps, weight z := by
    rw [← Finset.sum_image (f := weight) (g := code)
      (fun a _ b _ eq => (decode_code a).symm.trans ((congrArg eval eq).trans (decode_code b)))]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr fun n hn => map hn) (fun _ _ _ => by dsimp [weight]; positivity)
  let W := ∏ p ∈ k.primesLE, (1+1/(p:ℝ))
  have expand : ∑ z ∈ ds ×ˢ ps, weight z = (∑ a ∈ ds, ((a:ℝ)^2)⁻¹)*W := by
    simp only [W,one_div,Finset.prod_one_add,Finset.sum_product,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro s _
    simp [weight,eval,Nat.cast_prod,Finset.prod_inv_distrib,mul_comm]
  apply (H.trans embed).trans
  rw [expand]
  have hW : 0 ≤ W := Finset.prod_nonneg fun p _ => by positivity
  apply mul_le_mul_of_nonneg_right _ hW
  exact (inv_sq_sum k).trans (sub_le_self _ (by positivity))

/-- Odd prime moduli totaling at most half the grid side, with a product
gain of at least one sixth of its iterated logarithm. -/
theorem prime_supply : ∀ᶠ q : ℕ in atTop, ∃ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p ∧ Odd p) ∧ 2 ≤ ∏ p ∈ S, p ∧
    2 * (∏ p ∈ S, p) ≤ q ∧
    (1/6:ℝ) * Real.log (Real.log q) ≤ ∏ p ∈ S, (1+1/(p:ℝ)) := by
  filter_upwards [eventually_ge_atTop 64] with q hq
  let k := Nat.log 4 q
  have hq0 : q ≠ 0 := by omega
  have hk : 3 ≤ k := (Nat.le_log_iff_pow_le (by decide : 1 < 4) hq0).mpr hq
  have h₂ : 2 ∈ k.primesLE := Nat.mem_primesLE.mpr ⟨by omega,Nat.prime_two⟩
  let S := k.primesLE.erase 2
  have prime {p} (hp : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_erase.mp hp).2
  refine ⟨S,(fun p hp => ⟨prime hp,(prime hp).odd_of_ne_two (Finset.mem_erase.mp hp).1⟩),?_,?_,?_⟩
  · have h₃ : 3 ∈ S := Finset.mem_erase.mpr ⟨by decide,Nat.mem_primesLE.mpr ⟨hk,Nat.prime_three⟩⟩
    have h := Finset.single_le_prod' (s := S) (f := id)
      (fun p hp => (prime hp).one_le) h₃
    exact (by decide : 2 ≤ 3).trans h
  · calc
      2 * (∏ p ∈ S, p) = primorial k := by
        exact k.primesLE.mul_prod_erase id h₂
      _ ≤ 4^k := primorial_le_four_pow _
      _ ≤ q := Nat.pow_log_le_self _ hq0
  · have hqpos : (1:ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    have hpow : (q:ℝ) < (4:ℝ)^(k+1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1<4) q
    have hlog := Real.log_lt_log (zero_lt_one.trans hqpos) hpow
    rw [Real.log_pow] at hlog
    have hfour : Real.log 4 ≤ ((k+1:ℕ):ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      have hk' : 3 ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast (show 3 ≤ k+1 by omega)
      linarith
    have bound : Real.log (q:ℝ) ≤ (((k+1:ℕ):ℝ))^2 :=
      hlog.le.trans (by rw [sq]; gcongr)
    have loglog := Real.log_le_log (Real.log_pos hqpos) bound
    rw [Real.log_pow] at loglog
    let W := ∏ p ∈ S, (1+1/(p:ℝ))
    have hW : (1+1/(2:ℝ))*W = ∏ p ∈ k.primesLE, (1+1/(p:ℝ)) := by
      simpa [W,S] using k.primesLE.mul_prod_erase (fun p : ℕ => (1+1/(p:ℝ))) h₂
    have heuler := harmonic_le_product k
    rw [← hW] at heuler
    change (1/6:ℝ)*Real.log (Real.log q) ≤ W
    norm_num at loglog heuler ⊢
    linarith

end OMA.Mertens1085

/- The sphere of square length -1 over an odd prime field has p(p+1) points. -/

namespace OMA.LocalSphere1085

private abbrev Hyp (K : Type*) [Field K] :=
  {t : K × K × K // t.1 * t.2.1 = t.2.2^2 - 1}

private def hypParam {K : Type*} [Field K] (v : (Kˣ × K) ⊕ (Bool × K)) : Hyp K :=
  match v with
  | .inl (a,c) => ⟨(a,(c^2-1)/a,c), by simp [field]⟩
  | .inr (b,y) => ⟨(0,y,if b then 1 else -1), by cases b <;> norm_num⟩

private lemma hyp_bij {K : Type*} [Field K] (ht : (2:K) ≠ 0) :
    Function.Bijective (hypParam (K := K)) := by
  classical
  have hdiff : (1:K) ≠ -1 := by intro h; apply ht; linear_combination h
  constructor
  · rintro (⟨a,c⟩ | ⟨i,b⟩) (⟨d,f⟩ | ⟨j,e⟩) he
    · have h := congrArg Subtype.val he
      simp only [hypParam, Prod.mk.injEq] at h
      exact congrArg Sum.inl (Prod.ext (Units.ext h.1) h.2.2)
    · have h := congrArg (fun t : Hyp K => t.val.1) he
      exact (a.ne_zero h).elim
    · have h := congrArg (fun t : Hyp K => t.val.1) he
      exact (d.ne_zero h.symm).elim
    · have h := congrArg Subtype.val he
      cases i <;> cases j <;> simp_all [hypParam, hdiff.symm]
  · rintro ⟨⟨a,b,c⟩, he⟩
    change a*b = c^2-1 at he
    by_cases ha : a = 0
    · subst a
      have hc : (c-1)*(c+1) = 0 := by linear_combination -he
      rcases mul_eq_zero.mp hc with hc | hc
      · have hc' : c = 1 := by linear_combination hc
        exact ⟨.inr (true,b), by subst c; rfl⟩
      · have hc' : c = -1 := by linear_combination hc
        exact ⟨.inr (false,b), by subst c; rfl⟩
    · refine ⟨.inl (Units.mk0 a ha,c), Subtype.ext ?_⟩
      simp only [hypParam, Units.val_mk0, Prod.mk.injEq, true_and, and_true]
      exact (div_eq_iff ha).mpr (by linear_combination -he)

private def Sphere (K : Type*) [Field K] := {v : Fin 3 → K // ∑ i, v i ^ 2 = -1}

private def unroll {K : Type*} [Field K] (a b : K) (hab : a^2+b^2 = -1)
    (ht : (2:K) ≠ 0) (t : Hyp K) : Sphere K := by
  obtain ⟨⟨A,B,v⟩,hn⟩ := t
  change A*B = v^2-1 at hn
  let u := (B-A)/2
  refine ⟨![a*u-b*v, b*u+a*v, (A+B)/2], ?_⟩
  rw [Fin.sum_univ_three]
  change (a*u-b*v)^2 + (b*u+a*v)^2 + ((A+B)/2)^2 = -1
  dsimp only [u]
  field_simp
  linear_combination ((B-A)^2+4*v^2)*hab + 4*hn

private lemma unroll_bij {K : Type*} [Field K] (a b : K) (hab : a^2+b^2 = -1)
    (ht : (2:K) ≠ 0) : Function.Bijective (unroll a b hab ht) := by
  let inv (v : Sphere K) : Hyp K := by
    let x := v.1 0
    let y := v.1 1
    let z := v.1 2
    refine ⟨(z+a*x+b*y,z-a*x-b*y,b*x-a*y),?_⟩
    have hv : x^2+y^2+z^2 = -1 := by simpa [x,y,z,Fin.sum_univ_three] using v.2
    change (z+a*x+b*y)*(z-a*x-b*y) = (b*x-a*y)^2-1
    linear_combination hv - (x^2+y^2)*hab
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inv, ?_, ?_⟩
  · rintro ⟨⟨A,B,v⟩,hn⟩
    apply Subtype.ext
    simp [inv,unroll,Prod.ext_iff,id, Matrix.cons_val]
    constructor
    · field_simp; linear_combination (B-A)*hab
    constructor
    · field_simp; linear_combination (A-B)*hab
    · field_simp; linear_combination -2*v*hab
  · intro v
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [inv,unroll,id, Matrix.cons_val]
      field_simp
      linear_combination -2*(v.1 0)*hab
    · simp [inv,unroll,id, Matrix.cons_val]
      field_simp
      linear_combination -2*(v.1 1)*hab
    · simp [inv,unroll,id, Matrix.cons_val]
      field_simp
      ring

theorem local_card (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    Nat.card {v : Fin 3 → ZMod p // ∑ i, (v i)^2 = -1} = p*(p+1) := by
  let : Fact p.Prime := ⟨hp⟩
  have ht : (2 : ZMod p) ≠ 0 := by
    change ((2:ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hodd ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)
  obtain ⟨a,b,hab⟩ := ZMod.sq_add_sq p (-1)
  have e := Equiv.ofBijective _ ((unroll_bij a b hab ht).comp (hyp_bij ht))
  change Nat.card (Sphere (ZMod p)) = _
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum,Fintype.card_prod,ZMod.card_units,ZMod.card,Fintype.card_bool]
  have := hp.pos
  have h := Nat.sub_add_cancel (by omega : 1 ≤ p)
  nlinarith [congrArg (fun x : ℕ => x*p) h]

end OMA.LocalSphere1085

/- CRT and pigeonholing radii of lattice points in a three-dimensional box. -/
namespace OMA.Lattice1085
open Finset
open scoped Classical

private abbrev Sol (R : Type*) [CommRing R] := {v : Fin 3 → R // ∑ i, (v i)^2 = -1}

private def transport {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T) :
    Sol R ≃ Sol T where
  toFun v := ⟨fun i => e (v.val i),by simpa using congrArg e v.property⟩
  invFun v := ⟨fun i => e.symm (v.val i),by simpa using congrArg e.symm v.property⟩
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp

private def separate (R T : Type*) [CommRing R] [CommRing T] : Sol (R × T) ≃ Sol R × Sol T where
  toFun v := (⟨fun i => (v.val i).1,by simpa [Fin.sum_univ_three] using congrArg Prod.fst v.property⟩,
    ⟨fun i => (v.val i).2,by simpa [Fin.sum_univ_three] using congrArg Prod.snd v.property⟩)
  invFun v := ⟨fun i => (v.1.val i,v.2.val i),by
    apply Prod.ext
    · simpa [Fin.sum_univ_three] using v.1.property
    · simpa [Fin.sum_univ_three] using v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma crt (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    (hl : ∀ p ∈ S, Nat.card (Sol (ZMod p)) = p*(p+1)) :
    Nat.card (Sol (ZMod (∏ p ∈ S, p))) =
      (∏ p ∈ S, p) * ∏ p ∈ S, (p+1) := by
  induction S using Finset.induction with
  | empty =>
    simp only [prod_empty,one_mul]
    have : Nonempty (Sol (ZMod 1)) := ⟨⟨0,Subsingleton.elim ..⟩⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,this⟩
  | @insert p S hnot ih =>
    have hp' := hp p (mem_insert_self ..)
    have hS := fun x (hx : x ∈ S) => hp x (mem_insert_of_mem hx)
    have hc : p.Coprime (∏ x ∈ S, x) := hp'.coprime_iff_not_dvd.mpr (by
      intro h
      obtain ⟨x,hx,hd⟩ := (hp'.prime.dvd_finsetProd_iff id).mp h
      exact hnot ((Nat.prime_dvd_prime_iff_eq hp' (hS _ hx)).mp hd ▸ hx))
    rw [prod_insert hnot,prod_insert hnot]
    rw [Nat.card_congr ((transport (ZMod.chineseRemainder hc)).trans (separate _ _)),
      Nat.card_prod,hl p (mem_insert_self ..),ih hS (fun x hx => hl x (mem_insert_of_mem hx))]
    ring

private def normSq (v : Fin 3 → ℕ) := ∑ i, (v i)^2

private lemma tile (M q : ℕ) [NeZero M] :
    ∃ T : Finset (Fin 3 → ℕ),
      T.card = (q/M)^3 * Nat.card (Sol (ZMod M)) ∧
      ∀ v ∈ T, (∀ i, v i < q) ∧ M ∣ normSq v+1 := by
  let I := Sol (ZMod M) × (Fin 3 → Fin (q/M))
  let f (i : I) (k : Fin 3) := (i.1.val k).val + M*(i.2 k).val
  have hinj : Function.Injective f := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have he (k : Fin 3) := congrFun h k
    have hv (k : Fin 3) : a.val k=b.val k := by
      have h' := congrArg (fun n : ℕ => (n:ZMod M)) (he k)
      simpa [f] using h'
    have hij (k : Fin 3) : i k=j k := by
      have h' := he k
      dsimp only [f] at h'
      rw [hv k] at h'
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left (NeZero.pos M) (Nat.add_left_cancel h'))
    exact Prod.ext (Subtype.ext (funext hv)) (funext hij)
  refine ⟨univ.image f,?_,?_⟩
  · rw [card_image_of_injective _ hinj,card_univ]
    simp [I,Nat.card_eq_fintype_card,mul_comm]
  · intro v hv
    obtain ⟨⟨a,i⟩,_,rfl⟩ := mem_image.mp hv
    constructor
    · intro k
      have h₁ := (a.val k).val_lt
      have h₂ := (i k).isLt
      calc f (a,i) k < M*((i k).val+1) := by dsimp [f]; rw [Nat.mul_add]; omega
           _ ≤ M*(q/M) := Nat.mul_le_mul_left _ h₂
           _ ≤ q := Nat.mul_div_le _ _
    · apply (ZMod.natCast_eq_zero_iff ..).mp
      simp [normSq,f,a.property]

private lemma heavy_radius {T : Finset (Fin 3 → ℕ)} {M q : ℕ} (hM : 2 ≤ M)
    (hsize : 2*M ≤ q) (hT : ∀ v ∈ T, (∀ i, v i < q) ∧ M ∣ normSq v+1) :
    ∃ r : ℕ, 0 < r ∧ ∃ D : Finset (Fin 3 → ℕ),
      T.card ≤ (3*q^2/M)*D.card ∧ ∀ d ∈ D, (∀ i, d i < q) ∧ normSq d=r := by
  let keys := Icc 1 (3*q^2/M)
  let key (v : Fin 3 → ℕ) := (normSq v+1)/M
  let fiber (n : ℕ) := T.filter (fun v => key v=n)
  have hK : 1 ≤ 3*q^2/M := (Nat.le_div_iff_mul_le (by omega : 0<M)).mpr (by nlinarith)
  obtain ⟨k,hk,hmax⟩ := exists_max_image keys (fun t => (fiber t).card)
    (show keys.Nonempty from ⟨1,mem_Icc.mpr ⟨le_rfl,hK⟩⟩)
  have maps : (T : Set _).MapsTo key keys := by
    intro v hv
    obtain ⟨h,dvd⟩ := hT v hv
    have hmul := Nat.div_mul_cancel dvd
    have hle (i : Fin 3) : (v i)^2 < q^2 := Nat.pow_lt_pow_left (h i) (by decide)
    apply mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le (by omega : 0<M)).mpr
      have := Nat.le_of_dvd (by omega : 0<normSq v+1) dvd
      simpa
    · apply Nat.div_le_div_right
      simp only [normSq,Fin.sum_univ_three]
      have := hle 0; have := hle 1; have := hle 2
      omega
  have hkm : 1 ≤ k := (mem_Icc.mp hk).1
  have hkm' : M ≤ k*M := by simpa using Nat.mul_le_mul_right M hkm
  refine ⟨k*M-1,by omega,fiber k,?_,?_⟩
  · calc T.card = ∑ t ∈ keys, (fiber t).card := card_eq_sum_card_fiberwise maps
         _ ≤ ∑ _t ∈ keys, (fiber k).card := sum_le_sum fun t ht => hmax t ht
         _ = _ := by simp [keys,Nat.card_Icc]
  · intro v hv
    obtain ⟨hv,he⟩ := mem_filter.mp hv
    obtain ⟨hbox,hd⟩ := hT v hv
    have he' : (normSq v+1)/M=k := he
    have hu := Nat.div_mul_cancel hd
    rw [he'] at hu
    exact ⟨hbox,by omega⟩

theorem three_squares (S : Finset ℕ) (q : ℕ) (hp : ∀ p ∈ S, p.Prime)
    (hlocal : ∀ p ∈ S, Nat.card {v : Fin 3 → ZMod p // ∑ i, (v i)^2 = -1} = p*(p+1))
    (hM : 2 ≤ ∏ p ∈ S, p) (hsize : 2*(∏ p ∈ S, p) ≤ q) :
    ∃ r : ℕ, 0 < r ∧ ∃ D : Finset (Fin 3 → ℕ),
      (q:ℝ)*(∏ p ∈ S, (1+1/(p:ℝ))) ≤ 32*(D.card:ℝ) ∧
      ∀ d ∈ D, (∀ i, d i < q) ∧ ∑ i, (d i)^2 = r := by
  let M := ∏ p ∈ S, p
  let R := ∏ p ∈ S, (p+1)
  change 2 ≤ M at hM
  change 2*M ≤ q at hsize
  have hMp : 0 < M := by omega
  have hqp : 0 < q := by omega
  have : NeZero M := ⟨hMp.ne'⟩
  obtain ⟨T,hT,hbox⟩ := tile M q
  obtain ⟨r,hr,D,hD,hnorm⟩ := heavy_radius hM hsize hbox
  have hcrt : Nat.card (Sol (ZMod M))=M*R := crt S hp hlocal
  rw [hT,hcrt] at hD
  have scaled : q ≤ 2*M*(q/M) := by
    have h₁ : 1 ≤ q/M := (Nat.le_div_iff_mul_le hMp).mpr (by omega)
    have h₂ := Nat.mul_le_mul_left M h₁
    have h₃ := Nat.mod_add_div q M
    have h₄ := Nat.mod_lt q hMp
    nlinarith
  have hnat : (q^2*M)*(q*R) ≤ (q^2*M)*(24*M*D.card) := by
    calc (q^2*M)*(q*R) = q^3*(M*R) := by ring
         _ ≤ (2*M*(q/M))^3*(M*R) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left scaled _)
         _ = 8*M^3*((q/M)^3*(M*R)) := by ring
         _ ≤ 8*M^3*((3*q^2/M)*D.card) := Nat.mul_le_mul_left _ hD
         _ = (8*M^2*D.card)*((3*q^2/M)*M) := by ring
         _ ≤ (8*M^2*D.card)*(3*q^2) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ M)
         _ = _ := by ring
  have coarse : q*R ≤ 24*M*D.card := Nat.le_of_mul_le_mul_left hnat (by positivity)
  have coarser : (q:ℝ)*R ≤ 24*(M:ℝ)*D.card := by exact_mod_cast coarse
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hMp
  have ratio : (∏ p ∈ S, (1+1/(p:ℝ))) = (R:ℝ)/M := by
    simp only [R,M,Nat.cast_prod,Nat.cast_add,Nat.cast_one,←prod_div_distrib]
    apply prod_congr rfl
    intro p h
    have hpos : (p:ℝ) ≠ 0 := by exact_mod_cast (hp p h).ne_zero
    field_simp
  refine ⟨r,hr,D,?_,hnorm⟩
  rw [ratio,mul_div_assoc']
  apply (div_le_iff₀ hMr).mpr
  nlinarith [mul_nonneg hMr.le (Nat.cast_nonneg D.card : 0 ≤ (D.card:ℝ))]

end OMA.Lattice1085

/- Translation of integral equal-length vectors inside a cubic grid. -/

namespace OMA.Grid3D1085
open Finset
open scoped EuclideanGeometry Classical

private noncomputable def pt (t : ℝ) (v : Fin 3 → ℕ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (v i:ℝ)/t)

private lemma pt_inj {t : ℝ} (ht : t ≠ 0) : Function.Injective (pt t) := by
  intro v w he
  funext i
  have hi : (v i:ℝ)/t = (w i:ℝ)/t :=
    congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z i) he
  exact_mod_cast (div_left_inj' ht).mp hi

private lemma length_one {r : ℕ} (hr : 0 < r) (v d : Fin 3 → ℕ) (hn : ∑ i, d i^2 = r) :
    dist (pt (Real.sqrt r) v) (pt (Real.sqrt r) (v+d)) = 1 := by
  rw [EuclideanSpace.dist_eq]
  have ht : (0:ℝ) < Real.sqrt r := by positivity
  have hsum : ∑ i, (d i:ℝ)^2 = r := by exact_mod_cast hn
  apply (Real.sqrt_eq_iff_eq_sq (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)).mpr
  have term (i : Fin 3) :
      dist ((pt (Real.sqrt r) v) i) ((pt (Real.sqrt r) (v+d)) i)^2 =
      (d i:ℝ)^2 / (Real.sqrt r)^2 := by
    change dist ((v i:ℝ)/_) ((((v i+d i):ℕ):ℝ)/_) ^ 2 = _
    rw [Real.dist_eq,sq_abs,Nat.cast_add,add_div]
    ring
  simp_rw [term]
  rw [← Finset.sum_div, hsum, Real.sq_sqrt (by positivity)]
  field_simp

private theorem le_extremal (Q : Finset (EuclideanSpace ℝ (Fin 3))) (n : ℕ) (hQ : Q.card = n) :
    unitDistNum Q ≤ Erdos1085.f 3 n := by
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (T : Finset (EuclideanSpace ℝ (Fin 3))) (_ : T.card = n) => unitDistNum T) ?_ Q hQ
  refine ⟨n.choose 2, ?_⟩
  intro k hk
  rcases Set.mem_iUnion.mp hk with ⟨T,h⟩
  obtain ⟨hc,rfl⟩ := Set.mem_range.mp h
  simpa only [hc] using unitDistNum_le_choose_two T


theorem grid (q n r : ℕ) (hr : 0 < r) (hsize : (2*q)^3 ≤ n) (D : Finset (Fin 3 → ℕ))
    (hd : ∀ d ∈ D, (∀ i, d i < q) ∧ ∑ i, d i^2 = r) :
    q^3 * D.card ≤ 2 * Erdos1085.f 3 n := by
  classical
  let t := Real.sqrt (r:ℝ)
  have ht : t ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  let B (s : ℕ) := Fintype.piFinset fun _ : Fin 3 => range s
  have bc (s : ℕ) : (B s).card = s^3 := by simp [B]
  let Q₀ := (B (2*q)).image (pt t)
  have budget : Q₀.card ≤ n := card_image_le.trans ((bc _).le.trans hsize)
  obtain ⟨Q,sub,hQ⟩ := Infinite.exists_superset_card_eq Q₀ n budget
  let U := Q.sym2.filter fun e => dist e.out.1 e.out.2 = 1
  let ordered (e : Sym2 (EuclideanSpace ℝ (Fin 3))) : Finset ((EuclideanSpace ℝ (Fin 3)) × (EuclideanSpace ℝ (Fin 3))) := {e.out,e.out.swap}
  have lift {a b : (EuclideanSpace ℝ (Fin 3))} (ha : a ∈ Q) (hb : b ∈ Q) (h : dist a b = 1) :
      (a,b) ∈ U.biUnion ordered := by
    let e := Sym2.mk a b
    have he : Sym2.mk e.out.1 e.out.2 = Sym2.mk a b := e.out_eq
    have cases := Sym2.eq_iff.mp he
    apply mem_biUnion.mpr
    refine ⟨e,mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,?_⟩,?_⟩
    · rcases cases with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp_all [dist_comm]
    · rcases cases with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact mem_insert_self _ _ |> (fun H => (show e.out = (a,b) from Prod.ext h₁ h₂) ▸ H)
      · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext h₂.symm h₁.symm))
  let enc (pd : (Fin 3 → ℕ) × (Fin 3 → ℕ)) := (pt t pd.1,pt t (pd.1+pd.2))
  have inject : Function.Injective enc := by
    rintro ⟨p,d⟩ ⟨q,e⟩ he
    have hx : p = q := pt_inj ht (congrArg Prod.fst he)
    have hy : p+d = q+e := pt_inj ht (congrArg Prod.snd he)
    subst q
    exact Prod.ext rfl (add_left_cancel hy)
  have send : ∀ pd ∈ B q ×ˢ D, enc pd ∈ U.biUnion ordered := by
    rintro ⟨p,d⟩ hpd
    obtain ⟨hp,hD⟩ := mem_product.mp hpd
    obtain ⟨hb,hn⟩ := hd _ hD
    have hbi (i : Fin 3) : p i < q := mem_range.mp (Fintype.mem_piFinset.mp hp i)
    apply lift
    · apply sub (mem_image.mpr ⟨p,Fintype.mem_piFinset.mpr ?_,rfl⟩)
      intro i
      exact mem_range.mpr (by have := hbi i; omega)
    · apply sub (mem_image.mpr ⟨p+d,Fintype.mem_piFinset.mpr ?_,rfl⟩)
      intro i
      apply mem_range.mpr
      change p i + d i < 2*q
      have : d i < q := hb i
      have := hbi i
      omega
    · exact length_one hr p d hn
  have lower := card_le_card_of_injOn enc send inject.injOn
  rw [card_product, bc] at lower
  have hQle := le_extremal Q n hQ
  have upper : (U.biUnion ordered).card ≤ U.card*2 := calc
    _ ≤ ∑ e ∈ U, (ordered e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ U, 2 := sum_le_sum (fun e _ => card_le_two)
    _ = _ := by simp
  change (U.biUnion ordered).card ≤ (unitDistNum Q)*2 at upper
  omega

end OMA.Grid3D1085

/- Comparing the side of the grid with the cube root of the requested size. -/

namespace OMA.ThreeScale1085

open Filter Real
open scoped Topology

theorem from_grid {c : ℝ} (hc : 0 < c)
    (grid : ∀ᶠ q : ℕ in atTop, ∀ n : ℕ, (2*q)^3 ≤ n →
      c * log (log (q:ℝ)) * (q:ℝ)^4 ≤ 64*(Erdos1085.f 3 n:ℝ)) :
    type_of% @Erdos1085.erdos_1085.variants.lower_d3 := by
  let R (n : ℕ) := (n:ℝ)^((1:ℝ)/3)
  let Q (n : ℕ) := ⌊R n / 2⌋₊
  have hR : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1:ℝ)/3)).comp tendsto_natCast_atTop_atTop
  have hQ : Tendsto Q atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_div_const_atTop_of_pos (by norm_num : (0:ℝ) < 2)).mpr hR)
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ) |>.comp hQ
  have hlog := tendsto_log_atTop.comp hcast
  apply Asymptotics.IsBigO.of_bound (32768/c)
  filter_upwards [hQ.eventually grid, hQ.eventually_ge_atTop 4,
    (tendsto_log_atTop.comp hlog).eventually_ge_atTop (log 6),
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 3,
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1]
    with n hgrid hq hllq hlq hn hlogn
  let q := Q n
  have hq4 : (4:ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0:ℝ) < q := by linarith
  have hn1 : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1<n)
  have hRpos : 0 ≤ R n := by dsimp [R]; positivity
  have hR3 : R n ^ 3 = n := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have lo : (q:ℝ) ≤ R n / 2 := Nat.floor_le (by positivity)
  have hi : R n / 2 < (q:ℝ) + 1 := Nat.lt_floor_add_one _
  have hsize : (2*q)^3 ≤ n := by
    have hle : 2*(q:ℝ) ≤ R n := by linarith
    exact_mod_cast (pow_le_pow_left₀ (by positivity) hle 3).trans hR3.le
  have hrb : R n ≤ 4*(q:ℝ) := by linarith
  have hnq : (n:ℝ) ≤ (4*(q:ℝ))^3 := hR3.ge.trans (pow_le_pow_left₀ hRpos hrb 3)
  have hl4 := Real.log_le_log (by norm_num : (0:ℝ) < 4) hq4
  have hln := Real.log_le_log (by positivity : 0 < (n:ℝ)) hnq
  rw [Real.log_pow, Real.log_mul (by norm_num) hqp.ne'] at hln
  norm_num only [Nat.cast_ofNat] at hln
  have hl6 : log (n:ℝ) ≤ 6*log (q:ℝ) := by linarith
  have hlgn := Real.log_le_log (Real.log_pos hn1) hl6
  change 1 ≤ log (q:ℝ) at hlq
  rw [Real.log_mul (by norm_num) (by linarith)] at hlgn
  change log 6 ≤ log (log (q:ℝ)) at hllq
  have hcompare : log (log (n:ℝ)) ≤ 2*log (log (q:ℝ)) := by linarith
  have hnlog : 0 ≤ log (log (n:ℝ)) := log_nonneg hlogn
  have hR4 : (n:ℝ)^(4/3:ℝ) = R n ^4 := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hg := hgrid n hsize
  change c*log (log (q:ℝ))*(q:ℝ)^4 ≤ 64*(Erdos1085.f 3 n:ℝ) at hg
  change ‖(n:ℝ)^(4/3:ℝ)*log (log (n:ℝ))‖ ≤ (32768/c)*‖(Erdos1085.f 3 n:ℝ)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hnlog),
    abs_of_nonneg (Nat.cast_nonneg _), hR4]
  have hprod := mul_le_mul (pow_le_pow_left₀ hRpos hrb 4) hcompare hnlog (by positivity)
  rw [div_mul_eq_mul_div,le_div_iff₀ hc]
  nlinarith only [mul_le_mul_of_nonneg_right hprod hc.le, hg]

end OMA.ThreeScale1085

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.lower_d3 := by
  apply OMA.ThreeScale1085.from_grid (c := 1/6) (by norm_num)
  filter_upwards [OMA.Mertens1085.prime_supply] with q hq
  obtain ⟨S,hp,hM,hsize,hprod⟩ := hq
  obtain ⟨r,hr,D,hD,hds⟩ := OMA.Lattice1085.three_squares S q (fun p h => (hp p h).1)
    (fun p h => OMA.LocalSphere1085.local_card p (hp p h).1 (by have := (hp p h).2; rintro rfl; norm_num at this))
    hM hsize
  intro n hn
  have hgrid := OMA.Grid3D1085.grid q n r hr hn D hds
  have hgr : (q:ℝ)^3 * D.card ≤ 2*(Erdos1085.f 3 n:ℝ) := by exact_mod_cast hgrid
  nlinarith only [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (q:ℝ)^4),
    mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ (q:ℝ)^3), hgr]
