import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Determinant lifting proof extracted from @steveDOTdigital, merged PR 3226, commit 0b94f39. -/
namespace OMA.Lift1818
open Finset

-- Dependence on the perturbations is affine when the step size squares to zero.
private def AffineStep {I R : Type*} [CommRing R] (t : R) (f : (I → R) → R) : Prop :=
  ∃ L : (I → R) →ₗ[R] R, ∀ h, f h = f 0 + t*L h

private lemma affine_const {I R : Type*} [CommRing R] (t r : R) :
    AffineStep (I:=I) t (fun _ => r) := ⟨0,by simp⟩

private lemma affine_add {I R : Type*} [CommRing R] {t : R} {f g : (I → R) → R}
    (hf : AffineStep t f) (hg : AffineStep t g) : AffineStep t (fun h => f h+g h) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨M,hM⟩ := hg
  refine ⟨L+M,fun h => ?_⟩
  change f h+g h = f 0+g 0 + t*(L h+M h)
  rw [hL h,hM h]
  ring

private lemma affine_mul {I R : Type*} [CommRing R] {t : R} (nilp : t^2=0)
    {f g : (I → R) → R} (hf : AffineStep t f) (hg : AffineStep t g) :
    AffineStep t (fun h => f h*g h) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨M,hM⟩ := hg
  refine ⟨f 0 • M + g 0 • L,fun h => ?_⟩
  change f h*g h = f 0*g 0 + t*(f 0*M h+g 0*L h)
  rw [hL h,hM h]
  linear_combination L h*M h*nilp

private lemma affine_inv {I : Type*} {n : ℕ} {t : ZMod n} (nilp : t^2=0)
    {f : (I → ZMod n) → ZMod n} (hf : AffineStep t f) (unit : IsUnit (f 0)) :
    AffineStep t (fun h => (f h)⁻¹) := by
  obtain ⟨L,hL⟩ := hf
  let b := (f 0)⁻¹
  have ub : f 0*b=1 := ZMod.mul_inv_of_unit _ unit
  refine ⟨(-b^2) • L,fun h => ?_⟩
  change (f h)⁻¹=b+t*(-b^2*L h)
  apply ZMod.inv_eq_of_mul_eq_one
  rw [hL h]
  linear_combination (1-t*b*L h)*ub - b^2*(L h)^2*nilp

private lemma affine_det {I J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]
    {t : R} (nilp : t^2=0) (A : (I→R) → Matrix J J R)
    (lin : ∀ i j, AffineStep t (fun h => A h i j)) :
    AffineStep t (fun h => (A h).det) := by
  classical
  let S : Subsemiring ((I→R)→R) := {
    carrier := {f | AffineStep t f}
    zero_mem' := affine_const t 0
    one_mem' := affine_const t 1
    add_mem' := affine_add
    mul_mem' := affine_mul nilp }
  have prod (σ : Equiv.Perm J) : (fun h => ∏ i,A h (σ i) i) ∈ S := by
    have h := S.prod_mem (t:=univ) (f:=fun (i:J) (h:I→R) => A h (σ i) i) (fun i _ => lin (σ i) i)
    convert h using 1
    ext x
    simp only [Finset.prod_apply]
  change (fun h => (A h).det) ∈ S
  let w (σ : Equiv.Perm J) (h : I→R) := ((Equiv.Perm.sign σ:ℤ):R)*(∏ i,A h (σ i) i)
  have val (σ : Equiv.Perm J) : w σ ∈ S := S.mul_mem (affine_const t ((Equiv.Perm.sign σ:ℤ):R)) (prod σ)
  have sum := S.sum_mem (t:=univ) (f:=w) (fun σ _ => val σ)
  convert sum using 1
  ext h
  simp [Matrix.det_apply',w,Finset.sum_apply]
-- The only permutation-invariant linear functional on the coordinate axes is
-- a multiple of their sum. Common rescaling annihilates that multiple here.
private lemma affine_stationary {I R : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CommRing R]
    {t : R} {F : (I→R)→R} (lin : AffineStep t F)
    (unit : IsUnit (Fintype.card I : R))
    (axis : ∀ i j : I, F (Pi.single i 1) = F (Pi.single j 1))
    (scale : F (fun _ => 1)=F 0) (h : I→R) : F h = F 0 := by
  classical
  obtain ⟨L,hL⟩ := lin
  let i₀ : I := Classical.choice ‹Nonempty I›
  let D := t • L
  have axes (i : I) : D (Pi.single i 1) = D (Pi.single i₀ 1) := by
    have eq := axis i i₀
    rw [hL (Pi.single i 1),hL (Pi.single i₀ 1)] at eq
    exact add_left_cancel eq
  have one : D (fun _ => 1) = 0 := by
    have e := hL (fun _ => 1)
    rw [scale] at e
    exact (add_eq_left.mp e.symm)
  have null : D (Pi.single i₀ 1) = 0 := by
    have sum := congrArg D (univ_sum_single (fun _ : I => (1:R)))
    rw [map_sum,one] at sum
    simp only [axes,sum_const,card_univ,nsmul_eq_mul] at sum
    apply unit.mul_left_cancel
    simpa only [mul_zero] using sum
  rw [hL h]
  suffices z : D h=0 by change F 0+D h=F 0; rw [z,add_zero]
  rw [←univ_sum_single h,map_sum]
  apply sum_eq_zero
  intro i _
  have e : Pi.single i (h i) = h i • Pi.single i (1:R) := by
    ext j
    by_cases eq : j=i <;> simp [eq,Pi.single_apply]
  rw [e,map_smul,axes,null,smul_zero]
private lemma nil_prime (p : ℕ) : (p:ZMod (p^2))^2=0 := by rw [←Nat.cast_pow,ZMod.natCast_self]

-- Raising a representative to p is independent of its lift modulo p.
private lemma lift_pow_mod {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((a%p:ℕ):ZMod (p^2))^p = (a:ZMod (p^2))^p := by
  let x := ((a%p:ℕ):ZMod (p^2))
  let d := ((a/p:ℕ):ZMod (p^2))
  have rep : x+(p:ZMod (p^2))*d=(a:ZMod (p^2)) := by
    simpa only [x,d,Nat.cast_add,Nat.cast_mul] using congrArg (fun v:ℕ => (v:ZMod (p^2))) (Nat.mod_add_div a p)
  have zero : ((p:ZMod (p^2))*d)^p=0 := by
    rw [mul_pow,pow_eq_zero_of_le (n:=p) hp.two_le (nil_prime p),zero_mul]
  obtain ⟨w,hw⟩ := (Commute.all x ((p:ZMod (p^2))*d)).exists_add_pow_prime_eq hp
  change x^p=_
  rw [←rep,hw,zero,add_zero]
  linear_combination -(x*d*w)*(nil_prime p)

private noncomputable def liftHom (p : ℕ) (hp : p.Prime) : ZMod p →* ZMod (p^2) where
  toFun z := (z.val : ZMod (p^2))^p
  map_one' := by haveI : Fact (1<p) := ⟨hp.one_lt⟩; rw [ZMod.val_one,Nat.cast_one,one_pow]
  map_mul' x y := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    rw [ZMod.val_mul,lift_pow_mod hp,Nat.cast_mul,mul_pow]

private lemma lift_reduces (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) (liftHom p hp x) = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  change ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) (ZMod p) ((x.val : ZMod (p^2))^p)=x
  rw [map_pow,map_natCast,ZMod.natCast_zmod_val,ZMod.pow_card]

private lemma delta_multiple (p : ℕ) (hp : p.Prime) (z : ZMod (p^2))
    (vanish : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) z=0) :
    ∃ d : ZMod (p^2), z=(p:ZMod (p^2))*d := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have v : (z.val:ZMod p)=0 := by
    simpa only [map_natCast] using ((ZMod.natCast_zmod_val z).symm ▸ vanish :
      ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) (ZMod p) (z.val : ZMod (p^2)) = 0)
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp v
  exact ⟨k, by calc z = (z.val:ZMod (p^2)) := (ZMod.natCast_zmod_val z).symm
                    _ = _ := by rw [hk,Nat.cast_mul]⟩
private lemma unit_of_reduction_ne {p : ℕ} (hp : p.Prime) (z : ZMod (p^2))
    (nonzero : ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) (ZMod p) z ≠ 0) : IsUnit z := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [←ZMod.natCast_zmod_val z]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
  intro dvd
  apply nonzero
  rw [←ZMod.natCast_zmod_val z,map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd

private noncomputable def residueIndex {d p : ℕ} (hp : p.Prime) (size : d+1=p) :
    Fin d ≃ (ZMod p)ˣ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have nonzero (i : Fin d) : ((i.val+1:ℕ):ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff (i.val+1) p).mp hz
    have tooBig := Nat.le_of_dvd (Nat.succ_pos i.val) h
    have := i.isLt
    omega
  have pos (u : (ZMod p)ˣ) : 0 < (u:ZMod p).val := Nat.pos_of_ne_zero
    (fun e => u.ne_zero ((ZMod.val_eq_zero _).mp e))
  refine {
    toFun := fun i => Units.mk0 _ (nonzero i)
    invFun := fun u => ⟨(u:ZMod p).val-1, by have := (u:ZMod p).val_lt; have := pos u; omega⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    apply Fin.ext
    change (((i.val+1:ℕ):ZMod p).val)-1=i.val
    rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
    omega
  · intro u
    apply Units.ext
    change (((u:ZMod p).val-1+1:ℕ):ZMod p)=(u:ZMod p)
    rw [Nat.sub_add_cancel (pos u),ZMod.natCast_zmod_val]

private lemma residueIndex_apply {d p : ℕ} (hp : p.Prime) (size : d+1=p) (i : Fin d) :
    ((residueIndex hp size i : (ZMod p)ˣ):ZMod p)=((i.val+1:ℕ):ZMod p) := rfl

private lemma lift_index {d p : ℕ} (hp : p.Prime) (size : d+1=p) (i : Fin d) :
    liftHom p hp ((residueIndex hp size i : (ZMod p)ˣ):ZMod p) =
      ((i.val+1:ℕ):ZMod (p^2))^p := by
  change (((((i.val+1:ℕ):ZMod p).val : ℕ):ZMod (p^2)))^p=_
  rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
private lemma affine_sub {I R : Type*} [CommRing R] {t : R} {f g : (I → R) → R}
    (hf : AffineStep t f) (hg : AffineStep t g) : AffineStep t (fun h => f h-g h) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨M,hM⟩ := hg
  refine ⟨L-M,fun h => ?_⟩
  change f h-g h = f 0-g 0 + t*(L h-M h)
  rw [hL h,hM h]
  ring

private noncomputable def kernelMatrix {I : Type*} [DecidableEq I] {n : ℕ} (x : I → ZMod n) :
    Matrix I I (ZMod n) := fun i j => if i=j then 0 else x i*(x i-x j)⁻¹

private lemma kernel_affine {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (y : I→ZMod n) {t : ZMod n} (nilp : t^2=0)
    (diff : ∀ i j, i≠j → IsUnit (y i-y j)) :
    AffineStep t (fun h => (kernelMatrix (fun i => y i*(1+t*h i))).det) := by
  apply affine_det nilp
  intro i j
  by_cases eq : i=j
  · subst j; simpa [kernelMatrix] using affine_const (I:=I) t 0
  have node (i : I) : AffineStep t (fun h => y i*(1+t*h i)) := by
    refine ⟨y i • LinearMap.proj i,fun h => ?_⟩
    change y i*(1+t*h i)=y i*(1+t*0)+t*(y i*h i)
    ring
  have delta := affine_sub (node i) (node j)
  have unit : IsUnit (y i*(1+t*(0 : I→ZMod n) i)-y j*(1+t*(0 : I→ZMod n) j)) := by
    simpa using diff i j eq
  simpa only [kernelMatrix,if_neg eq] using affine_mul nilp (node i) (affine_inv nilp delta unit)

private lemma kernel_scale {I : Type*} [DecidableEq I] {n : ℕ} (x : I→ZMod n) (z : ZMod n)
    (uz : IsUnit z) (diff : ∀ i j, i≠j → IsUnit (x i-x j)) :
    kernelMatrix (fun i => z*x i) = kernelMatrix x := by
  ext i j
  by_cases eq : i=j
  · simp [kernelMatrix,eq]
  simp only [kernelMatrix,if_neg eq,←mul_sub]
  have inv : (z*(x i-x j))⁻¹=z⁻¹*(x i-x j)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [mul_mul_mul_comm,ZMod.mul_inv_of_unit _ uz,ZMod.mul_inv_of_unit _ (diff _ _ eq),mul_one]
  rw [inv,mul_mul_mul_comm,ZMod.mul_inv_of_unit _ uz,one_mul]

private lemma kernel_relabel {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (x : I→ZMod n) (e : Equiv.Perm I) :
    (kernelMatrix (fun i => x (e i))).det = (kernelMatrix x).det := by
  have eq : kernelMatrix (fun i => x (e i))=(kernelMatrix x).submatrix e e := by
    ext i j
    simp [kernelMatrix]
  rw [eq,Matrix.det_submatrix_equiv_self]

private lemma kernel_stationary {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {n : ℕ}
    (y : I→ZMod n) {t : ZMod n} (nilp : t^2=0) (card : IsUnit (Fintype.card I : ZMod n))
    (transitive : ∀ a b : I, ∃ e : Equiv.Perm I, e a=b ∧ ∃ z : ZMod n, IsUnit z ∧ ∀ i, y (e i)=z*y i)
    (sep : ∀ (h : I→ZMod n) i j, i≠j → IsUnit (y i*(1+t*h i)-y j*(1+t*h j))) (h : I→ZMod n) :
    (kernelMatrix (fun i => y i*(1+t*h i))).det = (kernelMatrix y).det := by
  let X (v : I→ZMod n) (i:I) := y i*(1+t*v i)
  let F (v : I→ZMod n) := (kernelMatrix (X v)).det
  have zero : X 0=y := by ext i; simp [X]
  have diff (i j : I) (ij : i≠j) : IsUnit (y i-y j) := by simpa using sep 0 i j ij
  have lin : AffineStep t F := kernel_affine y nilp diff
  have axis (a b : I) : F (Pi.single a 1)=F (Pi.single b 1) := by
    obtain ⟨e,ea,z,uz,mul⟩ := transitive a b
    have re : (fun i => X (Pi.single b 1) (e i)) = fun i => z*X (Pi.single a 1) i := by
      ext i
      by_cases eq : i=a
      · subst i; simp [X,←ea,mul,mul_assoc]
      · have ne : e i ≠ b := ea ▸ e.injective.ne eq
        simp [X,Pi.single_eq_of_ne eq,Pi.single_eq_of_ne ne,mul]
    dsimp only [F]
    rw [←kernel_relabel (X (Pi.single b 1)) e,re,kernel_scale _ z uz (sep _)]
  have common : F (fun _ => 1)=F 0 := by
    dsimp only [F]
    rw [zero]
    have ux : IsUnit (1+t) := IsUnit.of_mul_eq_one (1-t) (by linear_combination -nilp)
    have eq : X (fun _ => 1) = fun i => (1+t)*y i := by ext i; simp [X,mul_comm]
    rw [eq,kernel_scale _ _ ux diff]
  have ans := affine_stationary lin card axis common h
  simpa only [F,zero] using ans

-- The normalized determinant at 1,...,d equals the determinant on their
-- multiplicative lifts. Multiplication permutes the nonzero residues transitively.
private lemma actual_lift {d p : ℕ} (hp : p.Prime) (size : d+1=p) :
    let a (i : Fin d) := ((i.val+1:ℕ) : ZMod (p^2))
    (kernelMatrix a).det = (kernelMatrix (fun i => (a i)^p)).det := by
  classical
  have pp := hp.two_le
  haveI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let r := residueIndex hp size
  let a (i:Fin d) := ((i.val+1:ℕ):ZMod (p^2))
  let y (i:Fin d) := liftHom p hp ((r i):(ZMod p))
  let red := ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) (ZMod p)
  have yr (i:Fin d) : red (y i) = (r i:ZMod p) := lift_reduces p hp _
  have ar (i:Fin d) : red (a i) = (r i:ZMod p) := by rw [residueIndex_apply]; exact map_natCast red _
  have yu (i:Fin d) : IsUnit (y i) := (r i).isUnit.map (liftHom p hp)
  have transi (i j : Fin d) : ∃ e : Equiv.Perm (Fin d), e i=j ∧ ∃ z : ZMod (p^2), IsUnit z ∧ ∀ k, y (e k)=z*y k := by
    let b := (r j)*(r i)⁻¹
    let e := (r.trans (Equiv.mulLeft b)).trans r.symm
    have eq (k:Fin d) : r (e k)=b*r k := by simp [e]
    refine ⟨e,r.injective ?_,liftHom p hp (b:ZMod p),b.isUnit.map _,?_⟩
    · rw [eq]; simp [b]
    · intro k
      simp only [y,eq,Units.val_mul,map_mul]
  have card : IsUnit (Fintype.card (Fin d):ZMod (p^2)) := by
    rw [Fintype.card_fin]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
    intro dvd
    have := Nat.le_of_dvd (by omega : 0 < d) dvd
    omega
  have sep (h:Fin d→ZMod (p^2)) (i j:Fin d) (ne:i≠j) :
      IsUnit (y i*(1+(p:ZMod (p^2))*h i)-y j*(1+(p:ZMod (p^2))*h j)) := by
    apply unit_of_reduction_ne hp
    change red _ ≠ 0
    simp only [map_sub,map_mul,map_add,map_one,map_natCast,ZMod.natCast_self,zero_mul,add_zero,mul_one,yr]
    exact sub_ne_zero.mpr (fun eq => ne (r.injective (Units.ext eq)))
  have offsets (i:Fin d) : ∃ b : ZMod (p^2), a i-y i=(p:ZMod (p^2))*b :=
    delta_multiple p hp _ (by change red _=0; rw [map_sub,ar,yr,sub_self])
  choose b hb using offsets
  let h (i:Fin d) := b i*(y i)⁻¹
  have rep : (fun i => y i*(1+(p:ZMod (p^2))*h i))=a := by
    ext i
    calc _ = y i+((p:ZMod (p^2))*b i)*(y i*(y i)⁻¹) := by dsimp only [h]; ring
         _ = _ := by rw [ZMod.mul_inv_of_unit _ (yu i),mul_one,←hb]; ring
  have ans := kernel_stationary y (nil_prime p) card transi sep h
  rw [rep] at ans
  have yEq : y = fun i => (a i)^p := funext (lift_index hp size)
  rw [yEq] at ans
  exact ans

private theorem lift_input : ∀ m : ℕ, (2*m+1).Prime →
  let p := 2*m+1
  let C : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else ((i.val : ZMod (p^2))-j.val)⁻¹
  let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
  let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else y i*(y i-y j)⁻¹
  ((2*m).factorial : ZMod (p^2))*C.det = B.det := by
  intro m hp
  let p := 2*m+1
  let a (i:Fin (2*m)) := ((i.val+1:ℕ):ZMod (p^2))
  let C : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else ((i.val : ZMod (p^2))-j.val)⁻¹
  have matrix : kernelMatrix a = Matrix.diagonal a*C := by
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases eq : i=j
    · simp [C,kernelMatrix,eq]
    · simp [C,kernelMatrix,eq,a]
  have prod : (∏ i : Fin (2*m), a i) = ((2*m).factorial:ZMod (p^2)) := by
    change (∏ i : Fin (2*m), (((i.val+1):ℕ):ZMod (p^2)))=_
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((i+1:ℕ):ZMod (p^2))) (2*m),←Nat.cast_prod,prod_range_add_one_eq_factorial]
  have h := actual_lift hp (d:=2*m) rfl
  change (kernelMatrix a).det = _ at h
  rw [matrix,Matrix.det_mul,Matrix.det_diagonal,prod] at h
  exact h
end OMA.Lift1818

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1.H1 := OMA.Lift1818.lift_input
