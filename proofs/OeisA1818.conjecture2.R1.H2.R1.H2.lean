import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
/-! We prove Sun's reciprocal-difference determinant congruence modulo p².
Its degree-zero normalization is stationary under first-order perturbations of
the lifted roots of unity. Fourier diagonalization on those roots and a
binomial proof of Morley's congruence finish the evaluation. -/

namespace OMA.SunCauchyDet

open Finset

-- The product of the positive odd integers is the odd part of (2m)!.
private lemma odd_factorial (m : ℕ) :
    (∏ i ∈ range m, (2*i+1))*2^m*m.factorial=(2*m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ,pow_succ,Nat.factorial_succ,show 2*(m+1)=2*m+1+1 by omega,
      Nat.factorial_succ,Nat.factorial_succ,←ih]
    ring

private lemma odd_binomial (m : ℕ) :
    2^(2*m)*(∏ i ∈ range m, (2*i+1))^2 =
      (2*m).factorial*(2*m).choose m := by
  have fac := odd_factorial m
  have comb := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega)
  rw [show 2*m-m=m by omega] at comb
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos m))
  let O : ℕ := ∏ i ∈ range m, (2*i+1)
  change 2^(2*m)*O^2*(m.factorial*m.factorial) = _
  calc _ = (O*2^m*m.factorial)^2 := by rw [two_mul,pow_add]; ring
       _ = _ := by rw [show O*2^m*m.factorial=(2*m).factorial from fac,pow_two]; nlinarith only [congrArg (fun t => (2*m).factorial*t) comb]

-- The even list of odd eigenvalues comes in opposite pairs.
private lemma odd_spectrum {R : Type*} [CommRing R] (m : ℕ) :
    (∏ i : Fin (2*m), (2*(i.val:R)+1-2*(m:R))) =
      (-1:R)^m * (((∏ i ∈ range m, (2*i+1)):ℕ):R)^2 := by
  let f (i:ℕ) := (2*(i:R)+1-2*(m:R))
  let g (i:ℕ) := (2*(i:R)+1)
  have cast : (((∏ i ∈ range m, (2*i+1)):ℕ):R) = ∏ i ∈ range m,g i := by
    simp [g]
  rw [cast]
  change (∏ i : Fin (2*m),f i.val) = _
  rw [Fin.prod_univ_eq_prod_range, two_mul m,prod_range_add]
  have left : (∏ i ∈ range m,f i)=∏ i ∈ range m, (-1:R)*g i := by
    rw [←prod_range_reflect f m]
    apply prod_congr rfl
    intro i hi
    have h := mem_range.mp hi
    dsimp [f,g]
    push_cast [Nat.cast_sub (show i+1 ≤ m by omega), Nat.cast_sub (show i ≤ m-1 by omega),
      Nat.cast_sub (show 1 ≤ m by omega)]
    ring
  have right : (∏ i ∈ range m,f (m+i))=∏ i ∈ range m,g i := by
    apply prod_congr rfl
    intro i _
    dsimp [f,g]
    push_cast
    ring
  rw [left,right,prod_mul_distrib]
  simp only [prod_const,card_range,pow_two]
  ring

private lemma prime_nil (p : ℕ) : (p : ZMod (p^2))^2 = 0 := by
  rw [←Nat.cast_pow,ZMod.natCast_self]

private lemma nat_unit {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    IsUnit (k : ZMod (p^2)) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
      (fun h => (Nat.le_of_dvd hk h).not_gt hkp)

-- Multiplying the successive binomial factors leaves only the linear harmonic term.
private lemma binomial_first_order {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (-1 : ZMod (p^2))^k * ((p-1).choose k : ℕ) =
      1-(p : ZMod (p^2))*∑ i ∈ range k, ((i+1:ℕ) : ZMod (p^2))⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    let t : ZMod (p^2) := ((k+1:ℕ):ZMod (p^2))
    have unit := nat_unit hp (Nat.succ_pos k) hk
    have eq : (((p-1).choose (k+1):ℕ):ZMod (p^2))*t =
        (((p-1).choose k:ℕ):ZMod (p^2))*((p:ZMod (p^2))-t) := by
      have cast := congrArg (fun n : ℕ => (n:ZMod (p^2))) (Nat.choose_succ_right_eq (p-1) k)
      have sub : p-1-k=p-(k+1) := by omega
      rw [sub] at cast
      change (((p-1).choose (k+1)*(k+1) : ℕ) : ZMod (p^2)) = (((p-1).choose k*(p-(k+1)):ℕ):ZMod (p^2)) at cast
      simpa only [Nat.cast_mul,Nat.cast_sub hk.le,t] using cast
    have next : (((p-1).choose (k+1):ℕ):ZMod (p^2)) =
        (((p-1).choose k:ℕ):ZMod (p^2))*((p:ZMod (p^2))*t⁻¹-1) := calc
      _ = ((((p-1).choose (k+1):ℕ):ZMod (p^2))*t)*t⁻¹ := by rw [mul_assoc,ZMod.mul_inv_of_unit _ unit,mul_one]
      _ = _ := by rw [eq,mul_assoc,sub_mul,ZMod.mul_inv_of_unit _ unit]
    let H : ZMod (p^2) := ∑ i ∈ range k, ((i+1:ℕ):ZMod (p^2))⁻¹
    have prev := ih (by omega : k < p)
    rw [pow_succ (-1:ZMod (p^2)),next,sum_range_succ]
    change (-1:ZMod (p^2))^k*(-1)*((((p-1).choose k:ℕ):ZMod (p^2))*((p:ZMod (p^2))*t⁻¹-1)) = 1-(p:ZMod (p^2))*(H+t⁻¹)
    calc _ = ((-1:ZMod (p^2))^k * (((p-1).choose k:ℕ):ZMod (p^2)))*(1-(p:ZMod (p^2))*t⁻¹) := by ring
         _ = (1-(p:ZMod (p^2))*H)*(1-(p:ZMod (p^2))*t⁻¹) := by rw [prev]
         _ = _ := by linear_combination H*t⁻¹ * (prime_nil p)

private lemma row_term {p k : ℕ} (hp : p.Prime) (hk : k+1 < p) :
    (p.choose (k+1) : ZMod (p^2)) = (p : ZMod (p^2))*(-1)^k*((k+1:ℕ):ZMod (p^2))⁻¹ := by
  have pp := hp.pos
  have eqn := Nat.add_one_mul_choose_eq (p-1) k
  rw [Nat.sub_add_cancel pp] at eqn
  let t := ((k+1:ℕ):ZMod (p^2))
  have u := nat_unit hp (Nat.succ_pos k) hk
  have cast : (p : ZMod (p^2))*((p-1).choose k:ℕ) = (p.choose (k+1):ℕ)*t := by
    simpa only [Nat.cast_mul,t] using congrArg (fun v : ℕ => (v:ZMod (p^2))) eqn
  have h := binomial_first_order hp k (by omega)
  let H := ∑ i ∈ range k, ((i+1:ℕ):ZMod (p^2))⁻¹
  have sgn : ((-1:ZMod (p^2))^k)^2=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul]; simp
  have mul : (p : ZMod (p^2))*((p-1).choose k:ℕ)=(p : ZMod (p^2))*(-1)^k := by
    have mulh := congrArg (fun v : ZMod (p^2) => (p:ZMod (p^2)) * (-1)^k * v) h
    change (p:ZMod (p^2)) * (-1)^k * ((-1)^k*((p-1).choose k:ℕ)) =
      (p:ZMod (p^2)) * (-1)^k * (1-(p:ZMod (p^2))*H) at mulh
    linear_combination mulh - ((p:ZMod (p^2))*((p-1).choose k:ℕ))*sgn - ((-1:ZMod (p^2))^k*H)*(prime_nil p)
  calc _ = ((p.choose (k+1):ZMod (p^2))*t)*t⁻¹ := by rw [mul_assoc,ZMod.mul_inv_of_unit _ u,mul_one]
       _ = _ := by rw [←cast,mul]

private lemma harmonic_pair {p : ℕ} (hp : p.Prime) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (total : a+b=p) :
    (p:ZMod (p^2))*((a:ZMod (p^2))⁻¹ + (b:ZMod (p^2))⁻¹) = 0 := by
  have ua := nat_unit hp ha (by omega)
  have ub := nat_unit hp hb (by omega)
  have eq : (a:ZMod (p^2))+(b:ZMod (p^2))=p := by rw [←Nat.cast_add,total]
  calc
    _ = (p:ZMod (p^2))*(((a:ZMod (p^2))+(b:ZMod (p^2)))*((a:ZMod (p^2))⁻¹*(b:ZMod (p^2))⁻¹)) := by
      rw [add_mul]
      rw [show (a:ZMod (p^2))*((a:ZMod (p^2))⁻¹*(b:ZMod (p^2))⁻¹) = (b:ZMod (p^2))⁻¹ by rw [←mul_assoc,ZMod.mul_inv_of_unit _ ua,one_mul]]
      rw [show (b:ZMod (p^2))*((a:ZMod (p^2))⁻¹*(b:ZMod (p^2))⁻¹) = (a:ZMod (p^2))⁻¹ by rw [mul_left_comm,ZMod.mul_inv_of_unit _ ub,mul_one]]
      ring
    _ = 0 := by rw [eq,←mul_assoc,←pow_two,prime_nil,zero_mul]

private lemma harmonic_all {p m : ℕ} (hp : p.Prime) (odd : 2*m+1=p) :
    (p:ZMod (p^2))*∑ i ∈ range (2*m), ((i+1:ℕ):ZMod (p^2))⁻¹ = 0 := by
  let f (i:ℕ) := (p:ZMod (p^2))*((i+1:ℕ):ZMod (p^2))⁻¹
  rw [mul_sum]
  change ∑ i ∈ range (2*m), f i = 0
  rw [two_mul,sum_range_add]
  rw [←sum_range_reflect (fun i => f (m+i)) m,←sum_add_distrib]
  apply sum_eq_zero
  intro i hi
  have il := mem_range.mp hi
  dsimp only [f]
  rw [←mul_add]
  exact harmonic_pair hp _ _ (by omega) (by omega) (by omega)

private lemma alternating {p m : ℕ} (hp : p.Prime) (odd : 2*m+1=p) :
    (∑ i ∈ range (2*m), (p:ZMod (p^2))*(-1)^i*((i+1:ℕ):ZMod (p^2))⁻¹) =
      -(p:ZMod (p^2))*(∑ j ∈ range m, ((j+1:ℕ):ZMod (p^2))⁻¹) := by
  let f (i:ℕ) := (p:ZMod (p^2))*((i+1:ℕ):ZMod (p^2))⁻¹
  let g (i:ℕ) := (p:ZMod (p^2))*(-1)^i*((i+1:ℕ):ZMod (p^2))⁻¹
  have layer (k : ℕ) (hk : k ≤ m) :
      (∑ i ∈ range (2*k),g i)=(∑ i ∈ range (2*k),f i)-(∑ j ∈ range k,f j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prev := ih (by omega)
      have ua := nat_unit hp (Nat.succ_pos k) (by omega : k+1 < p)
      have ub := nat_unit hp (by omega : 0 < 2*k+1+1) (by omega : 2*k+1+1 < p)
      let a := ((k+1:ℕ):ZMod (p^2))
      let b := ((2*k+1+1:ℕ):ZMod (p^2))
      have ba : b=2*a := by dsimp [b,a]; push_cast; ring
      have inv : 2*b⁻¹=a⁻¹ := calc
        _ = (2*b⁻¹)*(a*a⁻¹) := by rw [ZMod.mul_inv_of_unit _ ua,mul_one]
        _ = (b*b⁻¹)*a⁻¹ := by rw [ba]; ring
        _ = _ := by rw [ZMod.mul_inv_of_unit _ ub,one_mul]
      have evenpow : (-1:ZMod (p^2))^(2*k)=1 := by rw [pow_mul]; simp
      have evenVal : g (2*k)=f (2*k) := by simp [g,f,evenpow]
      have oddVal : g (2*k+1)= -f (2*k+1) := by simp [g,f,pow_succ (-1:ZMod (p^2)),evenpow]
      have halve : 2*f (2*k+1)=f k := by
        change 2*((p:ZMod (p^2))*b⁻¹)=(p:ZMod (p^2))*a⁻¹
        rw [mul_left_comm,inv]
      rw [show 2*(k+1)=2*k+1+1 by omega,sum_range_succ,sum_range_succ,sum_range_succ,
        sum_range_succ,sum_range_succ,prev,evenVal,oddVal]
      linear_combination -halve
  have all := harmonic_all hp odd
  rw [mul_sum] at all
  change (∑ i ∈ range (2*m),g i) = _
  rw [layer m le_rfl,show (∑ i ∈ range (2*m),f i)=0 from all,zero_sub,neg_mul,mul_sum]

private theorem morley_mod_square {p m : ℕ} (hp : p.Prime) (odd : 2*m+1=p) :
    (-1 : ZMod (p^2))^m * ((2*m).choose m:ℕ) = (4 : ZMod (p^2))^(p-1) := by
  have p2 := hp.two_le
  have mpos : 0 < m := by omega
  let H := ∑ i ∈ range m, ((i+1:ℕ):ZMod (p^2))⁻¹
  have first := binomial_first_order hp m (by omega)
  rw [show p-1=2*m by omega] at first
  have total : (2:ZMod (p^2))^p =
      2+(∑ i ∈ range (2*m), (p:ZMod (p^2))*(-1)^i*((i+1:ℕ):ZMod (p^2))⁻¹) := by
    have raw := congrArg (fun z:ℕ => (z:ZMod (p^2))) (Nat.sum_range_choose p)
    simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat] at raw
    rw [←raw, sum_range_succ,Nat.choose_self,Nat.cast_one]
    let f (j : ℕ) := (p.choose j : ZMod (p^2))
    have mid : (∑ i ∈ range p, f i)=(∑ i ∈ range (2*m), f (i+1))+f 0 := calc
      _ = ∑ i ∈ range (2*m+1), f i := congrArg (fun v : ℕ => ∑ i ∈ range v, f i) odd.symm
      _ = _ := sum_range_succ' f _
    change (∑ i ∈ range p, f i)+1 = _
    rw [mid]
    simp only [f,Nat.choose_zero_right,Nat.cast_one]
    have terms : (∑ i ∈ range (2*m), (p.choose (i+1):ZMod (p^2))) =
      ∑ i ∈ range (2*m), (p:ZMod (p^2))*(-1)^i*((i+1:ℕ):ZMod (p^2))⁻¹ :=
      sum_congr rfl (fun i hi => row_term hp (by have := mem_range.mp hi; omega))
    rw [terms]
    ring
  rw [alternating hp odd] at total
  have half : 2*((2:ZMod (p^2))^(p-1)) = 2-(p:ZMod (p^2))*H := by
    have pow : (2:ZMod (p^2))^p=(2:ZMod (p^2))^(p-1)*2 := calc
      _ = (2:ZMod (p^2))^(p-1+1) := congrArg (fun e : ℕ => (2:ZMod (p^2))^e) (by omega)
      _ = _ := pow_succ _ _
    rw [pow] at total
    change _ = 2 + -(p:ZMod (p^2))*H at total
    linear_combination total
  have unit : IsUnit (2:ZMod (p^2)) := by
    simpa using nat_unit hp (by decide : 0<2) (by omega : 2<p)
  have four : IsUnit (4:ZMod (p^2)) := by convert unit.mul unit using 1 <;> norm_num
  have eqfour : (4:ZMod (p^2))^(p-1)=((2:ZMod (p^2))^(p-1))^2 := by
    rw [show (4:ZMod (p^2))=2^2 by norm_num,←pow_mul,Nat.mul_comm,pow_mul]
  rw [eqfour,first]
  change 1-(p:ZMod (p^2))*H = _
  apply four.mul_left_cancel
  have squares := congrArg (fun z : ZMod (p^2) => z^2) half
  linear_combination -squares - H^2*(prime_nil p)

/-- Lift the nonzero residues to their Teichmüller representatives. Multiplying the
original determinant by the product of its nodes normalizes its degree to zero. -/
def H1 : Prop := ∀ m : ℕ, (2*m+1).Prime →
  let p := 2*m+1
  let C : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else ((i.val : ZMod (p^2))-j.val)⁻¹
  let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
  let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else y i*(y i-y j)⁻¹
  ((2*m).factorial : ZMod (p^2))*C.det = B.det

/-- The normalized kernel on the lifted roots of unity has a Fourier eigenbasis.
Twice its eigenvalues run through the odd integers from 1-2m to 2m-1. -/
def H2 : Prop := ∀ m : ℕ, (2*m+1).Prime →
  let p := 2*m+1
  let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
  let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else y i*(y i-y j)⁻¹
  ∃ V : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)), IsUnit V.det ∧
    ((2 : ZMod (p^2)) • B)*V =
      V*Matrix.diagonal (fun i : Fin (2*m) => 2*(i.val:ZMod (p^2))+1-2*m)

private theorem combine : H1 → H2 → OMA.R_OeisA1818_conjecture2_R1_H2_R1.H2 := by
  intro lift spectrum p hp hn
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hn
  have odd : 2*m+1=p := by omega
  subst p
  let p := 2*m+1
  let C : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else ((i.val : ZMod (p^2))-j.val)⁻¹
  let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
  let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else y i*(y i-y j)⁻¹
  have hLift : ((2*m).factorial : ZMod (p^2))*C.det=B.det := lift m hp
  obtain ⟨V,vu,hV⟩ := spectrum m hp
  change ((2:ZMod (p^2)) • B)*V = V*Matrix.diagonal
    (fun i : Fin (2*m) => 2*(i.val:ZMod (p^2))+1-2*m) at hV
  have de := congrArg Matrix.det hV
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_smul,Matrix.det_diagonal,
    Fintype.card_fin,odd_spectrum,mul_comm V.det] at de
  have pair := vu.mul_right_cancel de
  let O := (((∏ i ∈ range m, (2*i+1)):ℕ):ZMod (p^2))
  let L := ((2*m).factorial:ZMod (p^2))
  let A := ((2*m).choose m:ZMod (p^2))
  have hodd : (2:ZMod (p^2))^(2*m)*O^2=L*A := by
    simpa only [O,L,A,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      congrArg (fun z : ℕ => (z:ZMod (p^2))) (odd_binomial m)
  have mor : (-1:ZMod (p^2))^m*A=4^(2*m) := by simpa [p,A] using morley_mod_square hp (m:=m) rfl
  have comb : (4:ZMod (p^2))^(2*m)*B.det=L*(4:ZMod (p^2))^(2*m) := calc
    _ = (2:ZMod (p^2))^(2*m)*((2:ZMod (p^2))^(2*m)*B.det) := by
      rw [show (4:ZMod (p^2))=2*2 by norm_num,mul_pow,mul_assoc]
    _ = (-1:ZMod (p^2))^m*((2:ZMod (p^2))^(2*m)*O^2) := by rw [pair]; ring
    _ = _ := by rw [hodd,←mor]; ring
  have mp := hp.two_le
  have four : IsUnit (4:ZMod (p^2)) := by
    have u := nat_unit hp (by decide : 0<2) (by dsimp [p]; omega : 2<p)
    convert u.mul u using 1 <;> norm_num
  have lu : IsUnit L := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
    exact fun h => ((Nat.Prime.dvd_factorial hp).mp h).not_gt (show 2*m<p by dsimp [p]; omega)
  rw [mul_comm L] at comb
  have b := (four.pow (2*m)).mul_left_cancel comb
  change C.det = 1
  apply lu.mul_left_cancel
  rw [mul_one]
  exact hLift.trans b

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

-- Orthogonality over the ring modulo p² follows because a primitive character
-- value differs from one by a unit whenever its exponent is between 1 and p-2.
private lemma teich_orthogonal {p : ℕ} [NeZero p] (hp : p.Prime) (k : ℕ) (pos : 0<k) (lt : k<p-1) :
    (∑ x : (ZMod p)ˣ, (liftHom p hp (x:ZMod p))^k)=0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card,ZMod.card_units] at hg
  have ne : (g:ZMod p)^k ≠ 1 := by
    intro eq
    have unitEq : g^k=1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val,Units.val_one] using eq)
    have d := orderOf_dvd_of_pow_eq_one unitEq
    rw [hg] at d
    exact (Nat.le_of_dvd pos d).not_gt lt
  let v := liftHom p hp (g:ZMod p)
  have diff : IsUnit (v^k-1) := by
    apply unit_of_reduction_ne hp
    dsimp only [v]
    rw [map_sub,map_one,map_pow,lift_reduces]
    exact sub_ne_zero.mpr ne
  let f (x:(ZMod p)ˣ) := (liftHom p hp (x:ZMod p))^k
  have reindex := Equiv.sum_comp (Equiv.mulLeft g) f
  have scale : (∑ x, f (g*x))=v^k*∑ x,f x := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    simp [f,v,mul_pow]
  change ∑ x,f (g*x)=∑ x,f x at reindex
  rw [scale] at reindex
  change (∑ x,f x)=0
  apply diff.mul_left_cancel
  rw [sub_mul,one_mul,reindex,sub_self,mul_zero]

private noncomputable def groupWeight {G : Type*} [CommGroup G] [DecidableEq G] {N : ℕ}
    (φ : G →* ZMod N) (g : G) : ZMod N := if g=1 then 0 else (1-φ g)⁻¹

private lemma inverse_pair {G : Type*} [CommGroup G] [DecidableEq G] {N : ℕ}
    (φ : G →* ZMod N) (nonzero : ∀ g : G, g≠1 → IsUnit (1-φ g)) {g : G} (h : g≠1) :
    groupWeight φ g + groupWeight φ g⁻¹ = 1 := by
  have h' : g⁻¹ ≠ 1 := by simpa only [ne_eq,inv_eq_one] using h
  let x := φ g
  let y := φ g⁻¹
  have xy : x*y=1 := by dsimp [x,y]; rw [←map_mul,mul_inv_cancel,map_one]
  have u : IsUnit (1-x) := nonzero g h
  have w := ZMod.mul_inv_of_unit _ u
  have yy : (1-y)⁻¹= -x*(1-x)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    have e : (1-y)*(-x)=1-x := by linear_combination xy
    rw [←mul_assoc,e,w]
  simp only [groupWeight,if_neg h,if_neg h']
  change (1-x)⁻¹+(1-y)⁻¹=1
  rw [yy]
  linear_combination w

private lemma eigen_sums {G : Type*} [Fintype G] [CommGroup G] [DecidableEq G] {N : ℕ}
    (φ : G →* ZMod N) (nonzero : ∀ g : G, g≠1 → IsUnit (1-φ g)) (d : ℕ)
    (card : Fintype.card G = d) (orth : ∀ k : ℕ, 0<k → k<d → ∑ g : G, (φ g)^k=0)
    (k : ℕ) (hk : k<d) :
    2*(∑ g : G, groupWeight φ g*(φ g)^(k+1)) = 2*(k:ZMod N)+1-d := by
  classical
  let mu (k:ℕ) := ∑ g : G, groupWeight φ g*(φ g)^k
  have pair (g:G) : groupWeight φ g + groupWeight φ g⁻¹ = if g=1 then 0 else 1 := by
    by_cases h : g=1
    · simp [h,groupWeight]
    · simp [h,inverse_pair φ nonzero h]
  have base : 2*mu 0 = (d:ZMod N)-1 := by
    have re := Equiv.sum_comp (Equiv.inv G) (groupWeight φ)
    change (∑ i : G,groupWeight φ i⁻¹)=_ at re
    calc
      _ = (∑ g:G,groupWeight φ g)+(∑ g:G,groupWeight φ g⁻¹) := by rw [re,two_mul]; simp [mu]
      _ = ∑ g:G,(groupWeight φ g+groupWeight φ g⁻¹) := sum_add_distrib.symm
      _ = ∑ g:G,((1:ZMod N)-(if g=1 then 1 else 0)) := by
        apply sum_congr rfl; intro g _
        rw [pair]; split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib]; simp [card]
  have recurrence (j:ℕ) : mu j-mu (j+1) = (∑ g:G,(φ g)^j)-1 := by
    dsimp only [mu]
    rw [←sum_sub_distrib]
    have localEq (g:G) : groupWeight φ g*(φ g)^j-groupWeight φ g*(φ g)^(j+1) =
        (φ g)^j-(if g=1 then 1 else 0) := by
      by_cases h : g=1
      · simp [h,groupWeight]
      · simp only [groupWeight,if_neg h,sub_zero,pow_succ]
        have u := ZMod.inv_mul_of_unit _ (nonzero g h)
        linear_combination (φ g)^j*u
    simp_rw [localEq]
    rw [sum_sub_distrib]
    simp
  change 2*mu (k+1)=_
  induction k with
  | zero =>
    have recu := recurrence 0
    simp [card] at recu
    push_cast
    linear_combination base - 2*recu
  | succ k ih =>
    have prev := ih (by omega)
    have recu := recurrence (k+1)
    rw [orth _ (by omega) hk,zero_sub] at recu
    push_cast
    linear_combination prev - 2*recu

private lemma fourier_matrix {G : Type*} [Fintype G] [CommGroup G] [DecidableEq G] {N d : ℕ}
    (φ : G →* ZMod N) (r : Fin d ≃ G) (diff : ∀ a b : G, a≠b → IsUnit (φ a-φ b))
    (orth : ∀ k : ℕ, 0<k → k<d → ∑ g : G, (φ g)^k=0) :
    let y (i : Fin d) := φ (r i)
    ∃ V : Matrix (Fin d) (Fin d) (ZMod N), IsUnit V.det ∧
      ((2:ZMod N) • kernelMatrix y)*V =
        V*Matrix.diagonal (fun i : Fin d => 2*(i.val:ZMod N)+1-d) := by
  classical
  let y (i:Fin d) := φ (r i)
  let V := Matrix.diagonal y*Matrix.vandermonde y
  have vu (g:G) : IsUnit (φ g) := (Group.isUnit g).map φ
  have nonzero (g:G) (h:g≠1) : IsUnit (1-φ g) := by simpa using diff 1 g (Ne.symm h)
  have eig := eigen_sums φ nonzero d ((Fintype.card_congr r.symm).trans (Fintype.card_fin _)) orth
  refine ⟨V,?_,?_⟩
  · dsimp only [V]
    rw [Matrix.det_mul,Matrix.det_diagonal,Matrix.det_vandermonde]
    exact (IsUnit.prod_univ_iff.mpr fun i => vu _).mul
      (IsUnit.prod_univ_iff.mpr fun i => IsUnit.prod_iff.mpr fun j hj =>
        diff _ _ (r.injective.ne (ne_of_gt (mem_Ioi.mp hj))))
  have ve (i k : Fin d) : V i k = (y i)^(k.val+1) := by
    dsimp only [V]
    rw [Matrix.diagonal_mul,Matrix.vandermonde_apply,pow_succ,mul_comm]
  have entry (i j : Fin d) : kernelMatrix y i j = groupWeight φ ((r i)⁻¹*r j) := by
    by_cases eq : i=j
    · simp [eq,kernelMatrix,groupWeight]
    have h : (r i)⁻¹*r j≠1 := by
      intro he
      apply eq
      apply r.injective
      simpa only [mul_inv_cancel_left,mul_one] using (congrArg (fun t : G => r i*t) he).symm
    simp only [kernelMatrix,if_neg eq,groupWeight,if_neg h]
    let z := φ ((r i)⁻¹*r j)
    have zy : y i*z=y j := by dsimp [y,z]; rw [←map_mul]; simp
    have split : y i-y j=y i*(1-z) := by rw [mul_sub,mul_one,zy]
    have inv : (y i*(1-z))⁻¹=(y i)⁻¹*(1-z)⁻¹ := by
      apply ZMod.inv_eq_of_mul_eq_one
      rw [mul_mul_mul_comm,ZMod.mul_inv_of_unit _ (vu _),ZMod.mul_inv_of_unit _ (nonzero _ h),one_mul]
    change y i*(y i-y j)⁻¹ = (1-z)⁻¹
    rw [split,inv,←mul_assoc,ZMod.mul_inv_of_unit _ (vu _),one_mul]
  ext i k
  rw [Matrix.mul_apply,Matrix.mul_diagonal,ve]
  let e : G ≃ Fin d := (Equiv.mulLeft (r i)).trans r.symm
  let f (j:Fin d) := (2:ZMod N)*kernelMatrix y i j * (y j)^(k.val+1)
  change (∑ j, (2:ZMod N)*kernelMatrix y i j*V j k) = _
  simp_rw [ve]
  change (∑ j,f j)=_
  rw [←Equiv.sum_comp e f]
  have fact (g:G) : f (e g) = (y i)^(k.val+1)*(2*(groupWeight φ g*(φ g)^(k.val+1))) := by
    have rg : r (e g)=r i*g := by simp [e]
    dsimp only [f]
    rw [entry,rg,inv_mul_cancel_left]
    change 2*groupWeight φ g* (φ (r (e g)))^(k.val+1) = _
    rw [rg,map_mul,mul_pow]
    dsimp only [y]
    ring
  simp_rw [fact]
  rw [←mul_sum,←mul_sum,eig k.val k.isLt]

private theorem fourier_input : ∀ m : ℕ, (2*m+1).Prime →
  let p := 2*m+1
  let y (i : Fin (2*m)) := ((i.val+1 : ℕ) : ZMod (p^2))^p
  let B : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)) := fun i j =>
    if i=j then 0 else y i*(y i-y j)⁻¹
  ∃ V : Matrix (Fin (2*m)) (Fin (2*m)) (ZMod (p^2)), IsUnit V.det ∧
    ((2 : ZMod (p^2)) • B)*V =
      V*Matrix.diagonal (fun i : Fin (2*m) => 2*(i.val:ZMod (p^2))+1-2*m) := by
  intro m hp
  let d := 2*m
  let p := 2*m+1
  haveI : Fact p.Prime := ⟨hp⟩
  let r : Fin d ≃ (ZMod p)ˣ := residueIndex hp rfl
  let φ : (ZMod p)ˣ →* ZMod (p^2) := (liftHom p hp).comp (Units.coeHom (ZMod p))
  have diff (a b : (ZMod p)ˣ) (h : a≠b) : IsUnit (φ a-φ b) := by
    apply unit_of_reduction_ne hp
    rw [map_sub]
    change (ZMod.castHom _ (ZMod p)) (liftHom p hp (a:ZMod p)) -
      (ZMod.castHom _ (ZMod p)) (liftHom p hp (b:ZMod p)) ≠ 0
    rw [lift_reduces,lift_reduces]
    exact sub_ne_zero.mpr (fun eq => h (Units.ext eq))
  have orth (k : ℕ) (pos : 0<k) (lt : k<d) : (∑ g, (φ g)^k)=0 :=
    teich_orthogonal hp k pos (by dsimp [p,d] at *; omega)
  have res := fourier_matrix φ r diff orth
  have label (i : Fin d) : φ (r i)=((i.val+1:ℕ):ZMod (p^2))^p := lift_index hp rfl i
  dsimp only at res
  simp only [label,d,Nat.cast_mul,Nat.cast_ofNat] at res
  obtain ⟨V,inv,eq⟩ := res
  refine ⟨V,inv,?_⟩
  convert eq using 1
  congr 1

end OMA.SunCauchyDet

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1.H2 := by
  exact OMA.SunCauchyDet.combine OMA.SunCauchyDet.lift_input OMA.SunCauchyDet.fourier_input
