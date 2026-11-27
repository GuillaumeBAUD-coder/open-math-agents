import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
/-! Normalize the reciprocal-difference determinant to degree zero and pass to
the lifted nonzero residues. A Fourier eigenbasis and invariance under lifting
are the two inputs. The signed product of odd eigenvalues is evaluated using
a direct proof of Morley's congruence modulo the square of the prime. -/

namespace OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1

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

theorem main : H1 → H2 → OMA.R_OeisA1818_conjecture2_R1_H2_R1.H2 := by
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

end OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1
