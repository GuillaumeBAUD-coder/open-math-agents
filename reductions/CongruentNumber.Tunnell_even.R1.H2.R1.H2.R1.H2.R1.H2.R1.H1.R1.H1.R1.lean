import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1
import Mathlib

/-!
A nonzero balanced product of torsion-coordinate differences on the congruent-number curve is an algebraic unit when the translation order is prime to the conductor. Complex uniformization realizes the indicated Weierstrass division product as exactly such a balanced product.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
open Complex NumberField IsDedekindDomain IntermediateField IsLocalRing Set MeasureTheory
open scoped Classical NumberField

def H1 : Prop :=
  ∀ n m a:ℕ, n%8=2 → 2<n → (4*n).Coprime (a*m) →
  let A:=algebraicClosure ℚ ℂ
  let W:WeierstrassCurve A:=⟨0,0,0,-(n:A)^2,0⟩
  ∀ X:W.toAffine.Point→A, (X 0=0 ∧ ∀ x y (h:W.toAffine.Nonsingular x y), X (.some x y h)=x) → ∀ (ι κ:Type) [Fintype ι] [Fintype κ] (w:ι→ℤ)
    (U:ι→W.toAffine.Point) (V:W.toAffine.Point) (Q:κ→W.toAffine.Point),
  let H:=∏ i,(∏ j,(X (U i+V)-X (Q j)))^w i
  (∑ i,w i=0) → (∀ i,addOrderOf (U i)=4*n) → (m • V=0) → (∀ j,a • Q j=0) → (∀ j,Q j≠0) → (H≠0) →
    ∃ u:(𝓞 A)ˣ, u.val.val=H

def H2 : Prop :=
  ∀ (n : ℕ) (hn : 0<n),
  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩
  let a := 1+3*(4*n)
  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)
  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩
  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=
    let m := (b v).norm.natAbs
    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0
  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →
  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)
  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),
    (M.weierstrassP z-M.weierstrassP (t j))
  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),
    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v
  n%8=2 → 2<n → ∀ m:ℕ, 0 < m → (4*n).Coprime (a*m) → ∀ z:ℂ, (m:ℂ)*z∈M.lattice →
  let A:=algebraicClosure ℚ ℂ
  let W:WeierstrassCurve A:=⟨0,0,0,-(n:A)^2,0⟩
  ∃ X:W.toAffine.Point→A, (X 0=0 ∧ ∀ x y (h:W.toAffine.Nonsingular x y), X (.some x y h)=x) ∧ ∃ (ι κ:Type) (hi:Fintype ι) (hk:Fintype κ), letI:=hi; letI:=hk;
    ∃ (w:ι→ℤ) (U:ι→W.toAffine.Point) (V:W.toAffine.Point) (Q:κ→W.toAffine.Point),
    let H:=∏ i,(∏ j,(X (U i+V)-X (Q j)))^w i
    (∑ i,w i=0) ∧ (∀ i,addOrderOf (U i)=4*n) ∧ (m • V=0) ∧ (∀ j,a • Q j=0) ∧ (∀ j,Q j≠0) ∧ (H≠0) ∧ (H:ℂ)=G z

theorem main : H1 → H2 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro arithmetic represent
  refine fun n hn M h₁ h₂ hmod hlarge m hm hcop z hz => ?_
  obtain ⟨X,hX,ι,κ,hi,hk,w,U,V,Q,hw,hU,hV,hQ,hQ₀,hH,e⟩ :=
    represent n hn M h₁ h₂ hmod hlarge m hm hcop z hz
  letI:=hi
  letI:=hk
  obtain ⟨u,hu⟩:=arithmetic n m _ hmod hlarge hcop X hX ι κ w U V Q hw hU hV hQ hQ₀ hH
  exact ⟨u,(congrArg (fun a:algebraicClosure ℚ ℂ => (a:ℂ)) hu).trans e⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
