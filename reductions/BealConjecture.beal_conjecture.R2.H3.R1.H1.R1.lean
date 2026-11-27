import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1
import Mathlib

-- Credit: @ubuwaits

/-!
# The cubic case of the square-plus-power equation

The pure cubic square-root statement H1 implies the complete odd-base
classification u²+d³=2ᵏ for k>2. When 3 does not divide k, the square
root yields integers A,B with A>0, B dividing A², and B²=A³+2ᵏ.
It follows that B is a signed power of two and 3 divides k. For k=3t,
the factors 2ᵗ−d and 2²ᵗ+2ᵗd+d² are squares after their common divisor
is removed. This divisor divides three, and the first factor is one
modulo eight. The square second factor then forces t<5. The unique
solution is 13²+7³=2⁹.

The quintic and large-prime hypotheses correspond to the remaining inputs
in Bennett and Skinner (2004), Theorem 8.4. The latter uses Theorem 1.2.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1

/-- The linear cubic-field factor of this square has an integral square root.
The variables a,b,c are its coordinates in the basis 1, ∛2, ∛4. -/
def H1 : Prop :=
  ∀ {d u q j : ℕ}, d%2=1 → u%2=1 → d.Coprime u → 0<q → (j=1 ∨ j=2) →
    d^3+u^2=2^(3*q+j) → ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
      2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
      2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0)

/-- The remaining quintic case, with its necessary residue and coprimality conditions. -/
def H2 : Prop :=
  ∀ {u d k : ℕ}, u%2=1 → d%8=7 → 1<d → u.Coprime d → 2<k → k%2=1 →
    u^2+d^5≠2^k

/-- The remaining odd prime exponents in the specialization of
Bennett and Skinner's Theorem 1.2. -/
def H3 : Prop :=
  ∀ {u d p k : ℕ}, u%2=1 → d%8=7 → 1<d → u.Coprime d → p.Prime → 7≤p →
    2<k → k%2=1 → u^2+d^p≠2^k

namespace BealMordell

/-- A positive cube equal to a difference of distinct powers of two has
its lower exponent divisible by three. -/
private theorem cube_gap_valuation {a k h : ℕ} (ha : 0<a) (gap : a^3+2^k=2^h) : 3∣k := by
  have less : k<h := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
    have := Nat.pow_pos (n:=3) ha
    omega)
  let z := 2^(h-k)-1
  have big : 1 < 2^(h-k) := Nat.one_lt_two_pow (by omega)
  have pe : 2∣2^(h-k) := dvd_pow_self _ (by omega)
  have oz : ¬2∣z := by dsimp [z]; omega
  have nz : z≠0 := by dsimp [z]; omega
  have f : a^3=2^k*z := by
    have ep : 2^h=2^k*2^(h-k) := by rw [←pow_add]; congr 1; omega
    have ez : 2^(h-k)=z+1 := by dsimp [z]; omega
    rw [ep,ez,Nat.mul_add,Nat.mul_one] at gap
    omega
  have val := congrArg (fun n : ℕ => n.factorization 2) f
  rw [Nat.factorization_mul (by positivity) nz,Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,Nat.factorization_eq_zero_of_not_dvd oz,
    Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at val
  exact ⟨a.factorization 2,by omega⟩

/-- The symmetric functions of a square root in the pure cubic field
give integral coordinates A,B with B dividing A² and B²=A³+2ᵏ.
Positivity of A then forces three to divide k. -/
theorem square_coordinates_force_three {d k : ℕ} (hd : 0<d)
    {a b c P Q : ℤ} (ha : a^2+4*b*c= -(d:ℤ))
    (hb : 2*a*b+2*c^2=P) (hc : 2*a*c+b^2=Q) (pq : P*Q=0)
    (power : 2*P^3+4*Q^3=(2:ℤ)^k) : 3∣k := by
  let T := 3*a
  let S := 3*(a^2-2*b*c)
  let N := a^3+2*b^3+4*c^3-6*a*b*c
  have ht : T^2=2*S-3*(d:ℤ) := by dsimp [T,S]; linear_combination 3*ha
  have hs : S^2-2*T*N=3*(d:ℤ)^2 := by
    have e : S^2-2*T*N=3*((a^2+4*b*c)^2-2*(2*a*b+2*c^2)*(2*a*c+b^2)) := by
      dsimp [S,T,N]; ring
    rw [e,ha,hb,hc]
    linear_combination -6*pq
  have hn : N^2+(d:ℤ)^3=(2:ℤ)^k := by
    have e : N^2=(a^2+4*b*c)^3+2*(2*a*b+2*c^2)^3+4*(2*a*c+b^2)^3-
        6*(a^2+4*b*c)*(2*a*b+2*c^2)*(2*a*c+b^2) := by dsimp [N]; ring
    rw [e,ha,hb,hc]
    linear_combination power+6*(d:ℤ)*pq
  let A := S-(d:ℤ)
  let B := T*S-N
  have apos : 0<A := by dsimp [A]; nlinarith [sq_nonneg T]
  have eA : 2*T*B=3*A^2 := by
    dsimp [A,B]
    linear_combination 2*S*ht+hs
  have eB : B^2=A^3+(2:ℤ)^k := by
    dsimp [A,B]
    linear_combination S^2*ht+S*hs+hn
  have dvdA : B∣A^2 := ⟨2*a,by dsimp [T] at eA; linarith only [eA]⟩
  have dvdA' : B∣A^3 := dvdA.trans (pow_dvd_pow A (by decide : 2≤3))
  have dvdB : B∣(2:ℤ)^k := by
    rw [show (2:ℤ)^k=B^2-A^3 by omega]
    exact dvd_sub (dvd_pow_self _ (by decide : 2≠0)) dvdA'
  have nd : B.natAbs∣(2:ℕ)^k := by
    simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 by decide] using (Int.natAbs_dvd_natAbs.mpr dvdB)
  obtain ⟨h,_,bh⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp nd
  have b2 : B^2=(2:ℤ)^(2*h) := by
    have n : (B.natAbs:ℤ)^2=B^2 := by rw [Int.natCast_natAbs,sq_abs]
    rw [←n,bh]
    push_cast
    rw [←pow_mul,Nat.mul_comm]
  have aeq : (A.toNat:ℤ)=A := Int.toNat_of_nonneg apos.le
  have agap : A.toNat^3+2^k=2^(2*h) := by
    exact_mod_cast (show (A.toNat:ℤ)^3+(2:ℤ)^k=(2:ℤ)^(2*h) by rw [aeq,←eB,b2])
  exact cube_gap_valuation (by omega) agap

end BealMordell

namespace BealMordell

private theorem square_parts {A B u : ℕ} (ha : 0<A) (h : A*B=u^2) :
    ∃ a b : ℕ, A=A.gcd B*a^2 ∧ B=A.gcd B*b^2 := by
  let g := A.gcd B
  let x := A/g
  let y := B/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left B ha
  have cx : g*x=A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have cy : g*y=B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have cp : x.Coprime y := Nat.coprime_div_gcd_div_gcd gp
  have du : g^2∣u^2 := ⟨x*y,by rw [←h,←cx,←cy]; ring⟩
  obtain ⟨v,hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp du
  have hxy : x*y=v^2 := by
    apply Nat.mul_left_cancel (Nat.pow_pos (n:=2) gp)
    rw [←cx,←cy,hv] at h
    linear_combination h
  obtain ⟨a,ea⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp)) hxy
  obtain ⟨b,eb⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp.symm)) ((Nat.mul_comm _ _).trans hxy)
  exact ⟨a,b,by rw [←ea]; exact cx.symm,by rw [←eb]; exact cy.symm⟩

private theorem base_seven {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : d%8=7 := by
  obtain ⟨v,hv⟩ := Nat.odd_iff.mpr hu
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  have h := congrArg (fun w : ℕ => (w:ZMod 8)) eqn
  rw [zero,hv] at h
  push_cast at h
  have tab : ∀ a b : ZMod 8, (2*a+1)^2+b^3=0 → b=7 := by decide +kernel
  have result := congrArg ZMod.val (tab _ _ h)
  simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using result

private theorem cubic_cofactor_square {d t u : ℕ} (ht : 3≤t) (hd : d%8=7)
    (hlt : d<2^t) (eqn : u^2+d^3=(2^t)^3) :
    ∃ z : ℕ, (2^t)^2+2^t*d+d^2=z^2 := by
  let W := 2^t
  let A := W-d
  let B := W^2+W*d+d^2
  let g := A.gcd B
  have WA : W=A+d := by dsimp [A,W]; omega
  have pos : 0<A := by dsimp [A,W]; omega
  have product : A*B=u^2 := by
    change u^2+d^3=W^3 at eqn
    dsimp [B]
    rw [WA] at eqn ⊢
    linear_combination -eqn
  have wd : W.Coprime d := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left t
  have cp : A.Coprime d := Nat.coprime_add_self_left.mp (WA ▸ wd)
  have ga : g∣A := Nat.gcd_dvd_left _ _
  have gb : g∣B := Nat.gcd_dvd_right _ _
  have identity : B=A*(W+2*d)+3*d^2 := by dsimp [B]; rw [WA]; ring
  have g3d : g∣3*d^2 := (Nat.dvd_add_iff_right (ga.trans (dvd_mul_right _ _))).mpr (identity ▸ gb)
  have g3 : g∣3 := ((Nat.Coprime.coprime_dvd_left ga cp).pow_right 2).dvd_of_dvd_mul_right g3d
  obtain ⟨a,b,eqA,eqB⟩ := square_parts pos product
  change A=g*a^2 at eqA
  change B=g*b^2 at eqB
  rcases (Nat.dvd_prime Nat.prime_three).mp g3 with one|three
  · exact ⟨b,by simpa [one] using eqB⟩
  have wz : (W:ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 ht)
  have dz : (d:ZMod 8)=7 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using hd
  have eq := congrArg (fun v : ℕ => (v:ZMod 8)) (WA.trans (by rw [eqA,three]))
  push_cast at eq
  rw [wz,dz] at eq
  exact ((by decide +kernel : ∀ a : ZMod 8, 0≠3*a^2+7) _ eq).elim

private theorem square_cofactor_small {d z t : ℕ} (hd : d%2=1)
    (hlt : d<2^t) (he : (2^t)^2+2^t*d+d^2=z^2) : t<5 := by
  by_contra! ht
  let L := 2^(t-2)
  let W := 2^t
  let S := d+2*L
  have lp : 0<L := Nat.two_pow_pos _
  have wL : W=4*L := by
    change 2^t=4*2^(t-2)
    calc
      2^t=2^(2+(t-2)) := by congr 1; omega
      _=4*2^(t-2) := by rw [pow_add]; rfl
  change W^2+W*d+d^2=z^2 at he
  change d<W at hlt
  have diff : z^2=S^2+12*L^2 := by dsimp [S]; rw [wL] at he; linear_combination -he
  have gt : S<z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by nlinarith [Nat.pow_pos (n:=2) lp])
  have zlt : z<2*W := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    rw [←he]
    nlinarith [Nat.pow_lt_pow_left hlt (by decide : 2≠0),Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos t)]
  have oddS : S%2=1 := by dsimp [S]; omega
  have oddZ : z%2=1 := by
    have e := congrArg (fun n : ℕ => n%2) diff
    change z^2%2=(S^2+12*L^2)%2 at e
    have ev : (12*L^2)%2=0 := Nat.mod_eq_zero_of_dvd ((by decide : 2∣12).trans (dvd_mul_right _ _))
    rw [Nat.pow_mod z,Nat.add_mod (S^2),Nat.pow_mod S,oddS,ev] at e
    by_contra hn
    have e0 : z%2=0 := by omega
    simp [e0] at e
  let r := (z-S)/2
  let v := r+S
  have zr : z=2*r+S := by dsimp [r]; omega
  have prod : r*v=3*L^2 := by
    dsimp [v]; rw [zr] at diff; nlinarith only [diff]
  let e := 2*(t-2)
  have dv : 2^e∣r*v := by rw [prod]; dsimp [e,L]; rw [Nat.mul_comm 2 (t-2),pow_mul]; exact dvd_mul_left _ _
  have vt : v≤z := by dsimp [v]; omega
  have rt : r≤z := by omega
  have bound : 2^e≤z := by
    by_cases oddr : r%2=1
    · have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣r)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [v]; omega) (cp.dvd_of_dvd_mul_left dv)).trans vt
    · have oddv : v%2=1 := by dsimp [v]; omega
      have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣v)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [r]; omega) (cp.dvd_of_dvd_mul_right dv)).trans rt
  have grow : 2*W≤2^e := by
    change 2*2^t≤2^e
    rw [Nat.mul_comm,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  omega

/-- When the exponent of two is a positive multiple of three, the
difference of cubes has only the solution 13²+7³=2⁹ for k>2. -/
theorem triple_shift {u d k : ℕ} (hu : u%2=1)
    (hk : 2<k) (divides : 3∣k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  obtain ⟨t,et⟩ := divides
  have e : u^2+d^3=(2^t)^3 := by rw [←pow_mul,Nat.mul_comm t 3,←et]; exact eqn
  have lt : d<2^t := (Nat.pow_lt_pow_iff_left (by decide : 3≠0)).mp (by have := Nat.pow_pos (n:=2) (show 0<u by omega); omega)
  have seven := base_seven hu hk eqn
  have th : 3≤t := by
    by_contra! h
    have bound := Nat.pow_le_pow_right (n:=2) (by decide) (show t≤2 by omega)
    norm_num at bound
    omega
  obtain ⟨z,hz⟩ := cubic_cofactor_square th seven lt e
  have small := square_cofactor_small (by omega) lt hz
  have eqt : t=3 := by
    by_contra neq
    have t4 : t=4 := by omega
    rw [t4] at lt
    norm_num at lt
    have choices : d=7 ∨ d=15 := by omega
    have ek : k=12 := by omega
    have e11 := congrArg (fun v : ℕ => (v:ZMod 11)) eqn
    have tab : ∀ x : ZMod 11, x^2+7^3≠2^12 ∧ x^2+15^3≠2^12 := by decide +kernel
    rw [ek] at e11
    rcases choices with rfl|rfl
    · exact (tab u).1 (by exact_mod_cast e11)
    · exact (tab u).2 (by exact_mod_cast e11)
  have eqk : k=9 := by omega
  rw [eqt] at lt
  have eqd : d=7 := by norm_num at lt; omega
  rw [eqk,eqd] at eqn
  norm_num at eqn
  exact ⟨by nlinarith,eqd,eqk⟩

end BealMordell

namespace BealMordell

private theorem coprime_bases {u d k : ℕ} (hu : u%2=1) (eqn : u^2+d^3=2^k) :
    d.Coprime u := by
  apply Nat.coprime_of_dvd
  intro l lp ld lu
  have dv : l∣2^k := eqn ▸ dvd_add (lu.trans (dvd_pow_self _ (by decide : 2≠0)))
    (ld.trans (dvd_pow_self _ (by decide : 3≠0)))
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

/-- The pure cubic square descent is the only number-field input to the
complete classification with odd bases. -/
theorem cubic_from_coordinates
    (roots : ∀ {d u q j : ℕ}, d%2=1 → u%2=1 → d.Coprime u → 0<q → (j=1 ∨ j=2) →
      d^3+u^2=2^(3*q+j) → ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
        2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
        2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0))
    {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  apply triple_shift hu hk _ eqn
  by_contra bad
  let q := k/3
  let j := k%3
  have sj : j=1 ∨ j=2 := by dsimp [j]; omega
  have kk : k=3*q+j := by dsimp [q,j]; omega
  have h : d^3+u^2=2^(3*q+j) := by rw [←kk,Nat.add_comm]; exact eqn
  obtain ⟨a,b,c,ha,hb,hc⟩ := roots hd hu (coprime_bases hu eqn) (by dsimp [q]; omega) sj h
  apply bad (square_coordinates_force_three (by omega : 0<d) ha hb hc _ _)
  · rcases sj with e|e <;> simp [e]
  · rw [kk]
    have p : ((2:ℤ)^q)^3=(2:ℤ)^(3*q) := by rw [←pow_mul,Nat.mul_comm]
    rcases sj with e|e <;> simp [e,p,pow_add] <;> ring

end BealMordell

namespace BealMordell

/-- The sole positive odd-base solution for k above two. -/
theorem classify_odd (roots : H1) {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : u=13 ∧ d=7 ∧ k=9 :=
  cubic_from_coordinates roots hu hd hk eqn

private theorem equal_two_orders {p q k a b : ℕ} (ha : a%2=1) (hb : b%2=1)
    (eqn : 2^p*a+2^q*b=2^k) : p=q := by
  have exclude {p q a b : ℕ} (lt : p<q) (oa : a%2=1) (ob : b%2=1)
      (h : 2^p*a+2^q*b=2^k) : False := by
    have qsplit : 2^q=2^p*2^(q-p) := by rw [←pow_add]; congr 1; omega
    let z := a+2^(q-p)*b
    have f : 2^p*z=2^k := by dsimp [z]; rw [qsplit] at h; linear_combination h
    have g : 1<z := by
      dsimp [z]
      have pos := Nat.mul_pos (Nat.two_pow_pos (q-p)) (show 0<b by omega)
      omega
    have pk : p<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←f]; simpa using Nat.mul_lt_mul_of_pos_left g (Nat.two_pow_pos p))
    have ksplit : 2^k=2^p*2^(k-p) := by rw [←pow_add]; congr 1; omega
    rw [ksplit] at f
    have ez := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos p) f
    have dv : 2∣z := ez ▸ dvd_pow_self 2 (by omega)
    have ev : 2∣2^(q-p)*b := (dvd_pow_self 2 (by omega : q-p≠0)).trans (dvd_mul_right _ _)
    dsimp [z] at dv
    omega
  rcases lt_trichotomy p q with lt|eq|lt
  · exact (exclude lt ha hb eqn).elim
  · exact eq
  · exact (exclude lt hb ha ((Nat.add_comm _ _).trans eqn)).elim

/-- Every positive solution is a weighted power-of-two multiple of
(1,1,1) or (13,7,9). -/
theorem classify_positive (roots : H1) {u d k : ℕ} (hu : 0<u) (hd : 0<d) :
    u^2+d^3=2^k ↔ ∃ t : ℕ,
      (u=2^(3*t) ∧ d=2^(2*t) ∧ k=6*t+1) ∨
      (u=13*2^(3*t) ∧ d=7*2^(2*t) ∧ k=6*t+9) := by
  constructor
  · intro h
    obtain ⟨i,a,oa,eu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.ne' 2 (by decide)
    obtain ⟨j,b,ob,ed⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' 2 (by decide)
    have opa : a^2%2=1 := by rw [Nat.pow_mod,show a%2=1 by omega]
    have opb : b^3%2=1 := by rw [Nat.pow_mod,show b%2=1 by omega]
    have f : 2^(i*2)*a^2+2^(j*3)*b^3=2^k := by simpa only [eu,ed,mul_pow,←pow_mul] using h
    have same := equal_two_orders opa opb f
    let t := i/3
    have ei : i=3*t := by dsimp [t]; omega
    have ej : j=2*t := by dsimp [t]; omega
    have fact : 2^(6*t)*(a^2+b^3)=2^k := by
      rw [show i*2=6*t by omega,show j*3=6*t by omega,←Nat.mul_add] at f
      exact f
    have sum : 1<a^2+b^3 := by omega
    have kk : 6*t<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←fact]; simpa using Nat.mul_lt_mul_of_pos_left sum (Nat.two_pow_pos (6*t)))
    let l := k-6*t
    have kl : k=6*t+l := by dsimp [l]; omega
    have red : a^2+b^3=2^l := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (6*t))
      rw [fact,←pow_add,←kl]
    refine ⟨t,?_⟩
    by_cases large : 2<l
    · obtain ⟨ea,eb,el⟩ := classify_odd roots (by omega) (by omega) large red
      right
      exact ⟨by rw [eu,ei,ea,Nat.mul_comm],by rw [ed,ej,eb,Nat.mul_comm],by omega⟩
    · have bound : 2^l≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : l≤2)
      have ea : a=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤a by omega) 2
        norm_num at this; omega
      have eb : b=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤b by omega) 3
        norm_num at this; omega
      have el : l=1 := by
        rw [ea,eb] at red
        have e : (2:ℕ)^1=2^l := by simpa using red
        exact ((Nat.pow_right_inj (by decide : 1<2)).mp e).symm
      left
      exact ⟨by rw [eu,ei,ea,Nat.mul_one],by rw [ed,ej,eb,Nat.mul_one],by omega⟩
  · rintro ⟨t,h|h⟩ <;> obtain ⟨rfl,rfl,rfl⟩ := h <;>
      simp only [mul_pow,←pow_mul,pow_add,show 3*t*2=6*t by omega,
        show 2*t*3=6*t by omega] <;> ring

/-- If one summand has an even exponent above two and the other has
exponent divisible by three, a power-of-two output forces two even bases. -/
theorem even_bases_of_dyadic_result (roots : H1) {a b x y k : ℕ} (hx : 2<x) (hy : 0<y) (hk : 2<k)
    (dx : 2∣x) (dy : 3∣y) (h : a^x+b^y=2^k) : 2∣a ∧ 2∣b := by
  obtain ⟨r,er⟩ := dx
  obtain ⟨s,es⟩ := dy
  have hr : 1<r := by omega
  have hs : 0<s := by omega
  have e : (a^r)^2+(b^s)^3=2^k := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm r 2,Nat.mul_comm s 3,←er,←es]; exact h
  have parity (A n : ℕ) (hn : 0<n) : A^n%2=A%2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one A with he|he <;> rw [he] <;> simp [hn.ne']
  have even : (2^k)%2=0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have pe := congrArg (fun n : ℕ => n%2) h
  change (a^x+b^y)%2=(2^k)%2 at pe
  rw [Nat.add_mod,parity a x (by omega),parity b y hy,even] at pe
  by_contra! no
  have oa : a%2=1 := by omega
  have ob : b%2=1 := by omega
  have az : a^r%2=1 := (parity a r (by omega)).trans oa
  have bz : b^s%2=1 := (parity b s hs).trans ob
  have sol := (classify_odd roots az bz hk e).1
  have unit := (Nat.Prime.pow_eq_iff (by decide : Nat.Prime 13)).mp sol
  omega

/-- Beal's stated common-divisor conclusion for either order of an even
exponent and a multiple of three when the output base is a power of two. -/
theorem beal_even_cube_dyadic (roots : H1) {a b c x y z : ℕ} (ha : a≠0) (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (output : ∃ t : ℕ, 0<t ∧ c=2^t)
    (exponents : (2∣x ∧ 3∣y) ∨ (3∣x ∧ 2∣y)) (h : a^x+b^y=c^z) :
    1 < Finset.gcd {a,b,c} id := by
  obtain ⟨t,ht,ec⟩ := output
  have kt : 2<t*z := by nlinarith
  rw [ec,←pow_mul] at h
  have bases : 2∣a ∧ 2∣b := by
    rcases exponents with ⟨dx,dy⟩|⟨dx,dy⟩
    · exact even_bases_of_dyadic_result roots hx (by omega) kt dx dy h
    · exact (even_bases_of_dyadic_result roots hy (by omega) kt dy dx ((Nat.add_comm _ _).trans h)).symm
  have dc : 2∣c := ec ▸ dvd_pow_self _ ht.ne'
  have dv : 2 ∣ Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact bases.1
    · exact bases.2
    · exact dc
  have pos : Finset.gcd {a,b,c} id ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨a,Finset.mem_insert_self _ _,ha⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero pos) dv

end BealMordell

/-- An odd square and a power summing to a multiple of eight force the
power to have odd exponent and base seven modulo eight. -/
private theorem residues {u d p k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k)
    (h : u^2+d^p=2^k) : p%2=1 ∧ d%8=7 := by
  have square {a : ℕ} (odd : a%2=1) : (a:ZMod 8)^2=1 := by
    obtain ⟨v,ev⟩ := Nat.odd_iff.mpr odd
    rw [ev]; push_cast
    exact (by decide +kernel : ∀ v : ZMod 8, (2*v+1)^2=1) _
  have eqn := congrArg (fun a : ℕ => (a:ZMod 8)) h
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  rw [zero] at eqn
  push_cast at eqn
  rw [square hu] at eqn
  rcases Nat.even_or_odd p with ⟨j,ej⟩|⟨j,ej⟩
  · rw [show p=2*j by omega,pow_mul,square hd,one_pow] at eqn
    exact (by decide : (1:ZMod 8)+1≠0) eqn |>.elim
  · rw [ej,pow_succ,pow_mul,square hd,one_pow,one_mul] at eqn
    have ed : (d:ZMod 8)=7 := (by decide +kernel : ∀ a : ZMod 8, 1+a=0 → a=7) _ eqn
    refine ⟨by omega,?_⟩
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using congrArg ZMod.val ed

private theorem prime_power_coprime {u d p k : ℕ} (hu : u%2=1) (hp : 0<p)
    (eqn : u^2+d^p=2^k) : u.Coprime d := by
  apply Nat.coprime_of_dvd
  intro l lp lu ld
  have dv : l∣2^k := eqn ▸ dvd_add (lu.trans (dvd_pow_self _ (by decide : 2≠0)))
    (ld.trans (dvd_pow_self _ hp.ne'))
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.H1 := by
  intro roots fifth large u d m k hu hd big hm hk ko eqn
  let p := m.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨j,ej⟩ := Nat.minFac_dvd m
  change m=p*j at ej
  have jp : 0<j := by
    by_contra! zero
    have j0 : j=0 := by omega
    rw [j0,Nat.mul_zero] at ej
    omega
  let D := d^j
  have dp : 1<D := Nat.one_lt_pow jp.ne' big
  have od : D%2=1 := by dsimp [D]; rw [Nat.pow_mod,hd,one_pow]; decide
  have e : u^2+D^p=2^k := by dsimp [D]; rw [←pow_mul,Nat.mul_comm j p,←ej]; exact eqn
  obtain ⟨po,seven⟩ := residues hu od hk e
  have cop := prime_power_coprime hu prime.pos e
  have p2 := prime.two_le
  by_cases p3 : p=3
  · rw [p3] at e
    exact (BealMordell.cubic_from_coordinates roots hu od hk e).1
  by_cases p5 : p=5
  · rw [p5] at e
    exact (fifth hu seven dp cop hk ko e).elim
  exact (large hu seven dp cop prime (by omega) hk ko e).elim

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1
