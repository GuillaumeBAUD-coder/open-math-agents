import OMAReductions.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1
import Mathlib

/-!
# The ordinary quartic output at prime powers

When s⁴+t⁴ is a power of a single odd prime, the primitive representation
of its p-th power as a sum of two squares is unique up to order and signs.
Taking t even, the imaginary part of (s²+i t²)ᵖ divided by t² is p modulo
eight. Being a square up to sign forces p to be 1 or 7 modulo eight.
For the base 17, reduction modulo five removes the negative sign case.
The square tests modulo 73 and 181 then force p = 1 modulo 360.

For the separate link to the rational-point classification, see E. V. Flynn
and J. L. Wetherell, "Covering collections and a challenge problem of Serre",
https://www.impan.pl/shop/en/publication/transaction/download/product/83714.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1_H1_R1

def H1 : Prop :=
  ∀ {a b s t p q e : ℕ}, 1<a → 1<b → 0<s → 0<t → a.Coprime b →
    s.Coprime t → p.Prime → 5≤p → (p%4=1 ∨ 5 ∣ a*b) → q.Prime → 0<e →
    s^4+t^4=q^e → (p%8=1 ∨ p%8=7) → (q^e=17 → p%360=1) →
    (p%36=1 → (t^2 ≡ 4*s^2 [MOD 181] ∨ s^2 ≡ 4*t^2 [MOD 181]) → p%180=1) →
    a^4+b^4 ≠ (s^4+t^4)^p

def H2 : Prop :=
  ∀ {a b s t p : ℕ}, 1<a → 1<b → 0<s → 0<t → a.Coprime b →
    s.Coprime t → p.Prime → 5≤p → (p%4=1 ∨ 5 ∣ a*b) →
    (∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q ∣ s^4+t^4 ∧ r ∣ s^4+t^4) →
    a^4+b^4 ≠ (s^4+t^4)^p

namespace PrimePowerQuartic

private theorem oriented {x y u v N : ℤ} (pos : 0<N)
    (lhs : x^2+y^2=N) (rhs : u^2+v^2=N)
    (det : N ∣ x*v-y*u) (dot : N ∣ x*u+y*v) :
    (u=x ∨ u= -x) ∧ (v=y ∨ v= -y) ∨
    (u=y ∨ u= -y) ∧ (v=x ∨ v= -x) := by
  obtain ⟨r,dr⟩ := det
  obtain ⟨s,ds⟩ := dot
  have unity : r^2+s^2=1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 pos.ne')
    calc
      N^2*(r^2+s^2) = (N*r)^2+(N*s)^2 := by ring
      _ = (x^2+y^2)*(u^2+v^2) := by rw [←dr,←ds]; ring
      _ = N^2*1 := by rw [lhs,rhs]; ring
  have U : u=x*s-y*r := by
    apply mul_left_cancel₀ pos.ne'
    linear_combination x*ds-y*dr-u*lhs
  have V : v=x*r+y*s := by
    apply mul_left_cancel₀ pos.ne'
    linear_combination x*dr+y*ds-v*lhs
  have rl : -1≤r := by nlinarith [sq_nonneg s]
  have rh : r≤1 := by nlinarith [sq_nonneg s]
  have sl : -1 ≤ s := by nlinarith [sq_nonneg r]
  have sh : s≤1 := by nlinarith [sq_nonneg r]
  interval_cases r <;> interval_cases s <;> simp_all

/-- Equal primitive norms at an odd prime power give the same coordinates
up to signs and order. Only two nondivisibility tests are needed. -/
theorem unique_coordinates {q : ℕ} (prime : q.Prime) (qo : q≠2) (n : ℕ)
    {x y u v : ℤ} (lhs : x^2+y^2=(q:ℤ)^n) (rhs : u^2+v^2=(q:ℤ)^n)
    (hy : ¬(q:ℤ) ∣ y) (hu : ¬(q:ℤ) ∣ u) :
    (u=x ∨ u= -x) ∧ (v=y ∨ v= -y) ∨
    (u=y ∨ u= -y) ∧ (v=x ∨ v= -x) := by
  have qp : Prime (q:ℤ) := Int.prime_iff_natAbs_prime.mpr prime
  have ht : ¬(q:ℤ) ∣ 2 := by
    intro d
    exact qo ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp
      (Int.natCast_dvd_natCast.mp (show (q:ℤ) ∣ (2:ℕ) from d)))
  have allD : (q:ℤ)^n ∣ (x*v-y*u)*(x*v+y*u) := by
    refine ⟨v^2-y^2,?_⟩
    linear_combination v^2*lhs-y^2*rhs
  have get {Y : ℤ} (Ynorm : x^2+Y^2=(q:ℤ)^n) (free : ¬(q:ℤ) ∣ Y)
      (d : (q:ℤ)^n ∣ x*v-Y*u) : (q:ℤ)^n ∣ x*u+Y*v := by
    apply qp.pow_dvd_of_dvd_mul_left n free
    have id : Y*(x*u+Y*v)=(q:ℤ)^n*v-x*(x*v-Y*u) := by linear_combination v*Ynorm
    rw [id]
    exact dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right d _)
  have pos : 0<(q:ℤ)^n := pow_pos (by exact_mod_cast prime.pos) _
  by_cases h : (q:ℤ) ∣ x*v+y*u
  · have free : ¬(q:ℤ) ∣ x*v-y*u := by
      intro d
      have prod : (q:ℤ) ∣ 2*y*u := by
        rw [show 2*y*u=(x*v+y*u)-(x*v-y*u) by ring]
        exact dvd_sub h d
      rcases qp.dvd_or_dvd prod with f|f
      · exact (qp.dvd_or_dvd f).elim ht hy
      · exact hu f
    have plus := qp.pow_dvd_of_dvd_mul_left n free allD
    have d : (q:ℤ)^n ∣ x*v-(-y)*u := by simpa using plus
    have L : x^2+(-y)^2=(q:ℤ)^n := by simpa using lhs
    have s := oriented pos L rhs d (get L (by simpa using hy) d)
    simp only [neg_neg] at s
    tauto
  · have d := qp.pow_dvd_of_dvd_mul_right n h allD
    exact oriented pos lhs rhs d (get lhs hy d)

private theorem no_shared {s t q : ℕ} (cop : s.Coprime t) (prime : q.Prime)
    (d : q ∣ s^4+t^4) : ¬ q ∣ s := by
  intro hs
  have h4 := hs.trans (dvd_pow_self s (by decide : 4≠0))
  have ht := prime.dvd_of_dvd_pow ((Nat.dvd_add_iff_right h4).mpr d)
  exact prime.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd hs ht)

/-- A Gaussian integer whose norm vanishes modulo q has z²=2 Re(z) z
modulo q. This prevents powers of a primitive factor from having both
coordinates zero there. -/
private theorem real_mod (z : GaussianInt) (q : ℕ)
    (hn : (z.re:ZMod q)^2+(z.im:ZMod q)^2=0) (k : ℕ) :
    ((z^(k+1)).re:ZMod q)=(2*z.re)^k*z.re ∧
    ((z^(k+1)).im:ZMod q)=(2*z.re)^k*z.im := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ z (k+1), Zsqrtd.re_mul,Zsqrtd.im_mul]
    push_cast
    rw [ih.1,ih.2,pow_succ]
    constructor
    · linear_combination -((2*(z.re:ZMod q))^k)*hn
    · ring

private theorem odd_output {a b c p : ℕ} (ab : a.Coprime b) (hp : 2≤p)
    (eq : a^4+b^4=c^p) : Odd c := by
  apply Nat.odd_iff.mpr
  by_contra! even
  have d : 2 ∣ c := by omega
  have four : 4 ∣ c^p := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow c hp)
  have e : (a:ZMod 4)^4+(b:ZMod 4)^4=0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).2 (eq ▸ four : 4 ∣ a^4+b^4)
    simpa using h
  have tab : ∀ x y : ZMod 4, x^4+y^4=0 → x.val%2=0 ∧ y.val%2=0 := by decide +kernel
  have bad := tab _ _ e
  simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2∣4)] at bad
  exact Nat.prime_two.not_dvd_one (ab.gcd_eq_one ▸ Nat.dvd_gcd
    (Nat.dvd_of_mod_eq_zero bad.1) (Nat.dvd_of_mod_eq_zero bad.2))

/-- The imaginary part of a power, up to terms divisible by the cube of
the imaginary part of its base. -/
private theorem expand (z : GaussianInt) (k : ℕ) : ∃ h j : ℤ,
    (z^(k+1)).re=z.re^(k+1)+z.im^2*h ∧
    (z^(k+1)).im=z.im*((k+1:ℕ)*z.re^k+z.im^2*j) := by
  induction k with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨h,j,hr,hi⟩ := ih
    refine ⟨h*z.re-((k+1:ℕ)*z.re^k+z.im^2*j),h+j*z.re,?_,?_⟩ <;>
      rw [pow_succ z (k+1)] <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,hr,hi] <;>
      push_cast <;> simp only [pow_succ] <;> ring

/-- Both coordinates of the indicated Gaussian power are signed squares. -/
theorem square_coordinates {a b s t p q e : ℕ} (ab : a.Coprime b) (st : s.Coprime t)
    (hp : 2≤p) (prime : q.Prime) (he : 0<e) (base : s^4+t^4=q^e)
    (eq : a^4+b^4=(s^4+t^4)^p) :
    let z : GaussianInt := ⟨(s:ℤ)^2,(t:ℤ)^2⟩
    ((∃ m : ℤ, (z^p).re=m^2 ∨ (z^p).re= -(m^2)) ∧
     (∃ m : ℤ, (z^p).im=m^2 ∨ (z^p).im= -(m^2))) := by
  let z : GaussianInt := ⟨(s:ℤ)^2,(t:ℤ)^2⟩
  have dc : q ∣ s^4+t^4 := base ▸ dvd_pow_self q he.ne'
  have odd := odd_output ab hp eq
  have qo : q≠2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr dc)
  have ds := no_shared st prime dc
  have db : ¬q ∣ b := no_shared ab.symm prime (by
    rw [add_comm,eq]
    exact dc.trans (dvd_pow_self _ (by omega)))
  have qb : ¬(q:ℤ) ∣ (b:ℤ)^2 := fun h => db (Int.natCast_dvd_natCast.mp
    ((show Prime (q:ℤ) from Int.prime_iff_natAbs_prime.mpr prime).dvd_of_dvd_pow h))
  let _ : Fact q.Prime := ⟨prime⟩
  have nzero : (z.re:ZMod q)^2+(z.im:ZMod q)^2=0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr dc
    change (((s:ℤ)^2:ℤ):ZMod q)^2+(((t:ℤ)^2:ℤ):ZMod q)^2=0
    push_cast
    simpa [←pow_mul] using h
  have zr : (z.re:ZMod q)≠0 := by
    change (((s:ℤ)^2:ℤ):ZMod q)≠0
    push_cast
    exact pow_ne_zero _ (fun h => ds ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have two : (2:ZMod q)≠0 := fun h => qo ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h)))
  have zu : ¬(q:ℤ) ∣ (z^p).re := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show p≠0 by omega)
    rw [(real_mod z q nzero k).1]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero two zr)) zr
  have L : ((a:ℤ)^2)^2+((b:ℤ)^2)^2=(q:ℤ)^(e*p) := by
    have h := eq
    rw [base,←pow_mul] at h
    exact_mod_cast (by simpa [←pow_mul] using h :
      (a^2)^2+(b^2)^2=q^(e*p))
  have hn : Zsqrtd.normMonoidHom z=(q:ℤ)^e := by
    change ((s:ℤ)^2)*((s:ℤ)^2)-(-1)*((t:ℤ)^2)*((t:ℤ)^2)=_
    have h : (s:ℤ)^4+(t:ℤ)^4=(q:ℤ)^e := by exact_mod_cast base
    linear_combination h
  have R : (z^p).re^2+(z^p).im^2=(q:ℤ)^(e*p) := by
    rw [pow_mul,←hn,←map_pow]
    change _=(z^p).re*(z^p).re-(-1)*(z^p).im*(z^p).im
    ring
  rcases unique_coordinates prime qo (e*p) L R qb zu with ⟨u,v⟩|⟨u,v⟩
  · exact ⟨⟨a,u⟩,⟨b,v⟩⟩
  · exact ⟨⟨b,u⟩,⟨a,v⟩⟩

private theorem residue_oriented {s t p : ℕ} (hs : Odd s) (ht : Even t) (htp : 0<t)
    (po : Odd p) (sq : ∃ m : ℤ,
      ((⟨(s:ℤ)^2,(t:ℤ)^2⟩:GaussianInt)^p).im=m^2 ∨
      ((⟨(s:ℤ)^2,(t:ℤ)^2⟩:GaussianInt)^p).im= -(m^2)) : p%8=1 ∨ p%8=7 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show p≠0 by obtain ⟨k,hk⟩ := po; omega)
  let z : GaussianInt := ⟨(s:ℤ)^2,(t:ℤ)^2⟩
  obtain ⟨_,j,_,J⟩ := expand z k
  let K : ℤ := (k+1:ℕ)*((s:ℤ)^2)^k+((t:ℤ)^2)^2*j
  change (z^(k+1)).im=(t:ℤ)^2*K at J
  obtain ⟨m,hm⟩ := sq
  change (z^(k+1)).im=m^2 ∨ (z^(k+1)).im= -(m^2) at hm
  rw [J] at hm
  have d : (t:ℤ)^2 ∣ m^2 := by
    rcases hm with h|h
    · exact ⟨K,h.symm⟩
    · exact ⟨-K,by linear_combination h⟩
  obtain ⟨w,hw⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp d
  have signed : K=w^2 ∨ K= -(w^2) := by
    rw [hw,mul_pow] at hm
    have nz : (t:ℤ)^2≠0 := by positivity
    exact hm.imp (mul_left_cancel₀ nz) (fun h => mul_left_cancel₀ nz (by simpa using h))
  have s8 : (s:ZMod 8)^2=1 := by
    obtain ⟨i,hi⟩ := hs
    rw [hi]; push_cast
    exact (by decide +kernel : ∀ x : ZMod 8, (2*x+1)^2=1) _
  have t8 : ((t:ZMod 8)^2)^2=0 := by
    obtain ⟨i,hi⟩ := ht
    rw [hi]; push_cast
    exact (by decide +kernel : ∀ x : ZMod 8, ((x+x)^2)^2=0) _
  have K8 : (K:ZMod 8)=((k+1:ℕ):ZMod 8) := by
    dsimp [K]; push_cast; simp [s8,t8]
  have residue : ((k+1:ℕ):ZMod 8)=(w:ZMod 8)^2 ∨
      ((k+1:ℕ):ZMod 8)= -((w:ZMod 8)^2) := by
    rw [←K8]
    exact signed.imp (fun h => by simp [h]) (fun h => by simp [h])
  have table : ∀ x w : ZMod 8, x.val%2=1 → (x=w^2 ∨ x= -(w^2)) →
      x.val=1 ∨ x.val=7 := by decide +kernel
  exact table ((k+1:ℕ):ZMod 8) _ (by
    rw [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2∣8)]
    exact Nat.odd_iff.mp po) residue

theorem prime_power_residues {a b s t p q e : ℕ} (ab : a.Coprime b) (st : s.Coprime t)
    (hs : 0<s) (ht : 0<t) (pp : p.Prime) (hp : 5≤p)
    (qp : q.Prime) (he : 0<e) (base : s^4+t^4=q^e) (eq : a^4+b^4=(s^4+t^4)^p) :
    p%8=1 ∨ p%8=7 := by
  have po := pp.odd_of_ne_two (by omega)
  have parity := Nat.odd_add.mp (odd_output ab (by omega) eq)
  have swap := Nat.odd_add'.mp (odd_output ab (by omega) eq)
  by_cases h : Odd s
  · have ev : Even t := by
      apply Nat.not_odd_iff_even.mp
      exact fun j => (Nat.not_even_iff_odd.mpr j.pow) (parity.mp h.pow)
    exact residue_oriented h ev ht po (square_coordinates ab st (by omega) qp he base eq).2
  · have ev : Even s := Nat.not_odd_iff_even.mp h
    have od : Odd t := by
      exact (Nat.odd_pow_iff (by decide : 4≠0)).mp (swap.mpr (ev.pow_of_ne_zero (by decide)))
    exact residue_oriented od ev hs po (square_coordinates ab st.symm (by omega) qp he
      (by simpa [add_comm] using base) (by simpa [add_comm] using eq)).2

/-- For the smallest odd quartic base, the two reductions of i modulo 73
give a stronger test. They send 1+4i to 36 and 39. -/
theorem seventeen {a b p : ℕ} (ab : a.Coprime b) (pp : p.Prime) (hp : 5≤p)
    (eq : a^4+b^4=17^p) : p%72=1 := by
  have base : 1^4+2^4=17^1 := by decide
  have eq' : a^4+b^4=(1^4+2^4)^p := eq
  have residues := prime_power_residues ab (by decide : Nat.Coprime 1 2) (by decide)
    (by decide) pp hp (by decide : Nat.Prime 17) (by decide) base eq'
  have mod8 : p%8=1 := by
    rcases residues with h|h
    · exact h
    · have e := congrArg (fun n : ℕ => (n:ZMod 5)) eq
      have pk : p=4*(p/4)+3 := by omega
      have e' : (a:ZMod 5)^4+(b:ZMod 5)^4=3 := by
        push_cast at e
        rw [pk,pow_add,pow_mul,show (17:ZMod 5)^4=1 by decide,one_pow,one_mul] at e
        exact e.trans (by decide)
      exact ((by decide +kernel : ∀ x y : ZMod 5, x^4+y^4≠3) _ _ e').elim
  let z : GaussianInt := ⟨1,4⟩
  obtain ⟨u,v⟩ := square_coordinates ab (by decide : Nat.Coprime 1 2) (by omega)
    (by decide : Nat.Prime 17) (by decide) base eq'
  have charTest (d : ℤ) (sq : ∃ m : ℤ, d=m^2 ∨ d= -(m^2)) :
      (d:ZMod 73)^36=0 ∨ (d:ZMod 73)^36=1 := by
    have table : ∀ x : ZMod 73, (x^2)^36=0 ∨ (x^2)^36=1 := by decide +kernel
    obtain ⟨m,hm|hm⟩ := sq <;> rw [hm] <;> push_cast
    · exact table (m:ZMod 73)
    · rw [(show Even 36 by decide).neg_pow]
      exact table (m:ZMod 73)
  have re := charTest (z^p).re u
  have im := charTest (z^p).im v
  let F : GaussianInt →+* ZMod 73 := Zsqrtd.lift ⟨27,by decide⟩
  let G : GaussianInt →+* ZMod 73 := Zsqrtd.lift ⟨46,by decide⟩
  have plus := map_pow F z p
  have minus := map_pow G z p
  change ((z^p).re:ZMod 73)+(z^p).im*27=(F z)^p at plus
  change ((z^p).re:ZMod 73)+(z^p).im*46=(G z)^p at minus
  rw [show F z=36 by decide +kernel] at plus
  rw [show G z=39 by decide +kernel] at minus
  have U : 37*((36:ZMod 73)^p+39^p)=(z^p).re := by
    calc
      _ = (37*2:ZMod 73)*(z^p).re+(37*(27+46):ZMod 73)*(z^p).im := by rw [←plus,←minus]; ring
      _ = _ := by rw [show (37*2:ZMod 73)=1 by decide, show (37*(27+46):ZMod 73)=0 by decide]; simp
  have V : 23*((36:ZMod 73)^p-39^p)=(z^p).im := by
    calc
      _ = (23*(27-46):ZMod 73)*(z^p).im := by rw [←plus,←minus]; ring
      _ = _ := by rw [show (23*(27-46):ZMod 73)=1 by decide]; simp
  have periodic (x : ZMod 73) (unit : x^72=1) : x^p=x^(p%72) := by
    conv_lhs => rw [←Nat.mod_add_div p 72]
    rw [pow_add,pow_mul,unit,one_pow,mul_one]
  rw [←U,periodic 36 (by decide),periodic 39 (by decide)] at re
  rw [←V,periodic 36 (by decide),periodic 39 (by decide)] at im
  have tab : ∀ j : Fin 72, j.val%8=1 → j.val%3≠0 →
      ((37*((36:ZMod 73)^j.val+39^j.val))^36=0 ∨ (37*((36:ZMod 73)^j.val+39^j.val))^36=1) →
      ((23*((36:ZMod 73)^j.val-39^j.val))^36=0 ∨ (23*((36:ZMod 73)^j.val-39^j.val))^36=1) →
      j.val=1 := by decide +kernel
  have three : p%3≠0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) pp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  exact tab ⟨p%72,by omega⟩ (by simpa [Nat.mod_mod_of_dvd _ (by decide : 8∣72)] using mod8)
    (by simpa [Nat.mod_mod_of_dvd _ (by decide : 3∣72)] using three) re im

/-- If t² is 4s² modulo 181, division by s² identifies the Gaussian
base with 1+4i in that residue field. For exponents equal to 1 modulo
36, a signed square imaginary coordinate forces p equal to 1 modulo 180. -/
theorem sieve_181 {a b s t p q e : ℕ} (ab : a.Coprime b) (st : s.Coprime t)
    (hp : 2≤p) (qp : q.Prime) (he : 0<e) (base : s^4+t^4=q^e)
    (eq : a^4+b^4=(s^4+t^4)^p) (h36 : p%36=1)
    (cong : t^2 ≡ 4*s^2 [MOD 181]) : p%180=1 := by
  let _ : Fact (Nat.Prime 181) := ⟨by norm_num1⟩
  let z : GaussianInt := ⟨(s:ℤ)^2,(t:ℤ)^2⟩
  have sq : ∃ m : ℤ, (z^p).im=m^2 ∨ (z^p).im= -(m^2) :=
    (square_coordinates ab st hp qp he base eq).2
  have ratio : (t:ZMod 181)^2=4*(s:ZMod 181)^2 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr cong
  have ns : (s:ZMod 181)≠0 := by
    intro zero
    have tz : (t:ZMod 181)=0 := by simpa [zero] using ratio
    exact (by decide : ¬181 ∣ 1) (st.gcd_eq_one ▸ Nat.dvd_gcd
      ((ZMod.natCast_eq_zero_iff _ _).mp zero) ((ZMod.natCast_eq_zero_iff _ _).mp tz))
  let F : GaussianInt →+* ZMod 181 := Zsqrtd.lift ⟨19,by decide⟩
  let G : GaussianInt →+* ZMod 181 := Zsqrtd.lift ⟨162,by decide⟩
  have plus := map_pow F z p
  have minus := map_pow G z p
  change ((z^p).re:ZMod 181)+(z^p).im*19=(F z)^p at plus
  change ((z^p).re:ZMod 181)+(z^p).im*162=(G z)^p at minus
  have fz : F z=(s:ZMod 181)^2*77 := by
    change (((s:ℤ)^2:ℤ):ZMod 181)+(((t:ℤ)^2:ℤ):ZMod 181)*19=_
    push_cast; rw [ratio,←show (1+4*19:ZMod 181)=77 by decide]; ring
  have gz : G z=(s:ZMod 181)^2*106 := by
    change (((s:ℤ)^2:ℤ):ZMod 181)+(((t:ℤ)^2:ℤ):ZMod 181)*162=_
    push_cast; rw [ratio,←show (1+4*162:ZMod 181)=106 by decide]; ring
  have switch : ((s:ZMod 181)^2)^p=((s:ZMod 181)^p)^2 := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have im : ((z^p).im:ZMod 181)=((s:ZMod 181)^p)^2*(81*(77^p-106^p)) := by
    calc
      _ = (81*(19-162):ZMod 181)*(z^p).im := by rw [show (81*(19-162):ZMod 181)=1 by decide,one_mul]
      _ = 81*((F z)^p-(G z)^p) := by rw [←plus,←minus]; ring
      _ = _ := by rw [fz,gz,mul_pow,mul_pow,switch]; ring
  have periodic (x : ZMod 181) (unit : x^180=1) : x^p=x^(p%180) := by
    conv_lhs => rw [←Nat.mod_add_div p 180]
    rw [pow_add,pow_mul,unit,one_pow,mul_one]
  rw [periodic 77 (ZMod.pow_card_sub_one_eq_one (by decide)),
    periodic 106 (ZMod.pow_card_sub_one_eq_one (by decide))] at im
  let j : Fin 5 := ⟨(p%180)/36,by omega⟩
  have idx : p%180=36*j.val+1 := by dsimp [j]; omega
  rw [idx] at im
  have tab : ∀ k : Fin 5, ∀ m : ZMod 181,
      (81*((77:ZMod 181)^(36*k.val+1)-106^(36*k.val+1))=m^2 ∨
       81*((77:ZMod 181)^(36*k.val+1)-106^(36*k.val+1))= -(m^2)) →
      k.val=0 := by decide +kernel
  obtain ⟨m,hm⟩ := sq
  have h : ((z^p).im:ZMod 181)=(m:ZMod 181)^2 ∨ ((z^p).im:ZMod 181)= -((m:ZMod 181)^2) :=
    hm.imp (fun h => by simp [h]) (fun h => by simp [h])
  rw [im] at h
  have nz := pow_ne_zero 2 (pow_ne_zero p ns)
  have lift : j.val=0 := by
    apply tab j ((m:ZMod 181)/(s:ZMod 181)^p)
    rw [div_pow]
    rcases h with h|h
    · left; apply (eq_div_iff nz).mpr; simpa [mul_comm] using h
    · right; rw [←neg_div]; apply (eq_div_iff nz).mpr; simpa [mul_comm] using h
  rw [idx,lift]

theorem seventeen_mod_360 {a b p : ℕ} (ab : a.Coprime b) (pp : p.Prime) (hp : 5≤p)
    (eq : a^4+b^4=17^p) : p%360=1 := by
  have h := seventeen ab pp hp eq
  have g := sieve_181 (s:=1) (t:=2) (q:=17) (e:=1) ab (by decide) (by omega)
    (by decide) (by decide) (by decide) eq (by omega) (by decide)
  omega

/-- A second prime base to which the same obstruction applies, since
2 · 66 + 49 = 181. All four excluded classes recur modulo 180. -/
theorem base_24739537 {a b p : ℕ} (ab : a.Coprime b) (hp : 2≤p)
    (h36 : p%36=1) (h180 : p%180≠1) : a^4+b^4≠24739537^p := by
  intro eq
  exact h180 (sieve_181 (s:=66) (t:=49) (q:=24739537) (e:=1) ab (by decide)
    hp (by norm_num1) (by decide) (by decide) eq h36 (by decide))

/-- The positive affine rational-point classification of Flynn and
Wetherell implies the full primitive base-17 exclusion. Their classification
is an explicit premise here. -/
theorem seventeen_of_rational_points
    (classify : ∀ x y : ℚ, 0<x → 0<y → x^4+y^4=17 →
      (x=1 ∧ y=2) ∨ (x=2 ∧ y=1))
    {a b p : ℕ} (ha : 0<a) (hb : 0<b) (ab : a.Coprime b) (pp : p.Prime) (hp : 5≤p) :
    a^4+b^4≠17^p := by
  intro eq
  have mod72 := seventeen ab pp hp eq
  let d : ℕ := 17^(p/4)
  have hd : 0<d := pow_pos (by decide) _
  have hdq : (d:ℚ)≠0 := by exact_mod_cast hd.ne'
  have sd : 17 ∣ d := dvd_pow_self _ (by omega : p/4≠0)
  have scale : a^4+b^4=17*d^4 := by
    calc
      _ = 17^p := eq
      _ = 17^(1+(p/4)*4) := congrArg (fun n : ℕ => 17^n) (by omega)
      _ = _ := by rw [pow_add,pow_mul,pow_one]
  have curve : ((a:ℚ)/d)^4+((b:ℚ)/d)^4=17 := by
    rw [div_pow,div_pow,←add_div,div_eq_iff (pow_ne_zero 4 hdq)]
    exact_mod_cast scale
  have divides (u n : ℕ) (h : (u:ℚ)/d=n) : d ∣ u := by
    have h' : u=n*d := by exact_mod_cast (div_eq_iff hdq).mp h
    exact h' ▸ dvd_mul_left _ _
  obtain h|h := classify _ _ (by positivity) (by positivity) curve
  all_goals
    have both : d ∣ a.gcd b := Nat.dvd_gcd (divides _ _ h.1) (divides _ _ h.2)
    exact (by decide : ¬17 ∣ 1) (ab.gcd_eq_one ▸ sd.trans both)

end PrimePowerQuartic

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1.H1 := by
  intro one many a b s t p ha hb hs ht ab st pp hp five eq
  by_cases h : IsPrimePow (s^4+t^4)
  · obtain ⟨q,e,qp,he,base⟩ := (isPrimePow_nat_iff _).mp h
    exact one ha hb hs ht ab st pp hp five qp he base.symm
      (PrimePowerQuartic.prime_power_residues ab st hs ht pp hp qp he base.symm eq)
      (fun v => PrimePowerQuartic.seventeen_mod_360 ab pp hp (by simpa [←base,v] using eq))
      (fun mod36 ratio => by
        rcases ratio with h|h
        · exact PrimePowerQuartic.sieve_181 ab st (by omega) qp he base.symm eq mod36 h
        · exact PrimePowerQuartic.sieve_181 ab st.symm (by omega) qp he
            (by simpa [add_comm] using base.symm) (by simpa [add_comm] using eq) mod36 h) eq
  · have bound : 2 ≤ s^4+t^4 := by
      have sPos : 0<s^4 := pow_pos hs _
      have tPos : 0<t^4 := pow_pos ht _
      omega
    obtain ⟨q,hq,r,hr,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le bound).mp h
    obtain ⟨qp,qd,_⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨rp,rd,_⟩ := Nat.mem_primeFactors.mp hr
    exact many ha hb hs ht ab st pp hp five ⟨q,r,qp,rp,ne,qd,rd⟩ eq
end OMA.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1_H1_R1
