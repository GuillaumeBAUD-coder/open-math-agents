import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Pell
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic

/-! Smooth quadratic values and necessary divisibility of large exceptions to Erdős 889. -/

namespace Erdos889.QuadraticSmooth

private theorem split_factor_exponent (e : ℕ) :
    ∃ i j : ℕ, e=i+j*2 ∧ i≤3 ∧ (0 < j → 2 ≤ i) := by
  by_cases small : e≤3
  · exact ⟨e,0,by omega,small,by omega⟩
  · exact ⟨2+e%2,(e-2)/2,by omega,by omega,by omega⟩

private theorem smooth_square_decomposition (T n : ℕ) (hn : 0 < n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q ≤ T) :
    ∃ D y : ℕ, D≤(T+1).factorial^3 ∧ 0 < D ∧ 0 < y ∧ n=D*y^2 ∧
      ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    refine ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit,?_⟩
    intro q pq div
    have := Nat.le_of_dvd (by decide : 0<1) div
    have := pq.two_le
    omega
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q ≤ t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := ih m pos smaller
    obtain ⟨i,j,ei,i3,ji⟩ := split_factor_exponent e
    have small : p^i ≤ (t+2)^3 :=
      (Nat.pow_le_pow_right (show 0 < p by dsimp [p]; omega) i3).trans
        (Nat.pow_le_pow_left (show p ≤ t+2 by dsimp [p]; omega) 3)
    have total : D*p^i ≤ (t+1+1).factorial^3 := by
      have bound := Nat.mul_le_mul cap small
      rw [Nat.factorial_succ (t+1),mul_pow,Nat.mul_comm ((t+1+1)^3)]
      exact bound
    refine ⟨D*p^i,y*p^j,total,Nat.mul_pos hD (pow_pos (by dsimp [p]; omega) _),
      Nat.mul_pos hy (pow_pos (by dsimp [p]; omega) _),?_,?_⟩
    · calc
        n = p^e*m := fac.symm
        _ = _ := by rw [form,ei,pow_add,pow_mul,mul_pow]; ring
    · intro q pq dq
      rcases pq.dvd_mul.mp dq with fromY|fromP
      · exact dvd_mul_of_dvd_left (divisors q pq fromY) _
      · have jp : 0 < j := by
          by_contra! low
          have zero : j=0 := by omega
          rw [zero,pow_zero] at fromP
          have := Nat.le_of_dvd (by decide : 0<1) fromP
          have := pq.two_le
          omega
        have pp : p.Prime := by
          by_contra np
          have zero : e=0 := Nat.factorization_eq_zero_of_not_prime n np
          omega
        have same := (Nat.prime_dvd_prime_iff_eq pq pp).mp (pq.dvd_of_dvd_pow fromP)
        rw [same]
        exact dvd_mul_of_dvd_right (pow_dvd_pow p (ji jp)) _

/-- Every square-plus-one supported on primes at most T gives a negative Pell
equation with D in an explicit finite interval. Each prime dividing its
positive y-coordinate has its square dividing D. -/
theorem quadratic_smooth_decomposition (T x : ℕ)
    (smooth : ∀ q : ℕ, q.Prime → q∣x^2+1 → q ≤ T) :
    ∃ D ∈ Finset.Icc 1 ((T+1).factorial^3), ∃ y : ℕ, 0 < D ∧ 0 < y ∧
      x^2+1=D*y^2 ∧ ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := smooth_square_decomposition T (x^2+1) (by omega) smooth
  exact ⟨D,Finset.mem_Icc.mpr ⟨hD,cap⟩,y,hD,hy,form,divisors⟩

end Erdos889.QuadraticSmooth

namespace Erdos889.PellValuation

-- BEGIN PELL VALUATION
private theorem pell_expansion_remainder {d : ℤ} (z : Pell.Solution₁ d) (n : ℕ) :
    ∃ L K : ℤ, (z^(n+1)).x=z.x^(n+1)+d*L ∧
      (z^(n+1)).y=z.y*((n+1 : ℕ)*(z.x^n)+d*K) := by
  induction n with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨L,K,hx,hy⟩ := ih
    refine ⟨L*z.x+(z^(n+1)).y*z.y,L+K*z.x,?_,?_⟩
    · change (z^(n+1)*z).x=z.x^(n+1+1)+d*(L*z.x+(z^(n+1)).y*z.y)
      rw [Pell.Solution₁.x_mul,hx,pow_succ z.x (n+1)]
      ring
    · change (z^(n+1)*z).y=z.y*((n+1+1:ℕ)*z.x^(n+1)+d*(L+K*z.x))
      rw [Pell.Solution₁.y_mul,hx,hy,pow_succ z.x n]
      push_cast
      ring

private theorem pell_prime_multiplier {D l q : ℕ} (z : Pell.Solution₁ (D:ℤ))
    (pl : l.Prime) (pq : q.Prime) (dq : q^2∣D) :
    ∃ k : ℕ, (z^l).y.natAbs=z.y.natAbs*k ∧ k≠0 ∧ k.factorization q=l.factorization q := by
  let _ : Fact q.Prime := ⟨pq⟩
  obtain ⟨_,K,_,hy⟩ := pell_expansion_remainder z (l-1)
  rw [Nat.sub_add_cancel pl.one_le] at hy
  obtain ⟨h,dh⟩ := dq
  have dint : (D:ℤ)=(q:ℤ)^2*h := by exact_mod_cast dh
  have zd : (D:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr (dh ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by decide : (2:ℕ)≠0)) h)
  have xz : (z.x:ZMod q)≠0 := by
    intro zero
    have f := congrArg (fun v:ℤ => (v:ZMod q)) z.prop
    push_cast at f
    rw [zd,zero,zero_pow two_ne_zero,zero_mul,sub_zero] at f
    exact zero_ne_one f
  let a := z.x^(l-1)
  have an : (a:ZMod q)≠0 := by dsimp [a]; push_cast; exact pow_ne_zero _ xz
  have no {c : ℤ} (hc : (c:ZMod q)≠0) : ¬q∣c.natAbs :=
    fun dd => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr dd))
  by_cases same : l=q
  · subst l
    let c := a+(q:ℤ)*h*K
    have cn : ¬q∣c.natAbs := no (by simpa [c] using an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    have yq : (z^q).y=z.y*((q:ℤ)*c) := by
      rw [hy]
      dsimp only [a,c]
      linear_combination z.y*K*dint
    refine ⟨q*c.natAbs,?_,mul_ne_zero pq.ne_zero nc,?_⟩
    · rw [yq]; simp only [Int.natAbs_mul,Int.natAbs_natCast]
    · rw [Nat.factorization_mul pq.ne_zero nc,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd cn,add_zero]
  · have nl : ¬q∣l := fun h => same ((Nat.prime_dvd_prime_iff_eq pq pl).mp h).symm
    have lv : (l:ZMod q)≠0 := fun h => nl ((ZMod.natCast_eq_zero_iff _ _).mp h)
    let c := (l:ℤ)*a+(D:ℤ)*K
    have cn : ¬q∣c.natAbs := no (by
      dsimp only [c]
      push_cast
      rw [zd,zero_mul,add_zero]
      exact mul_ne_zero lv an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    refine ⟨c.natAbs,?_,nc,?_⟩
    · rw [hy,Int.natAbs_mul]
    · rw [Nat.factorization_eq_zero_of_not_dvd cn,Nat.factorization_eq_zero_of_not_dvd nl]

/-- At a prime whose square divides D, the imaginary coordinate of a Pell power gains exactly the exponent's valuation. -/
theorem pell_factorization_y_pow {D q n : ℕ} (eps : Pell.Solution₁ (D : ℤ))
    (pq : q.Prime) (dq : q^2∣D) (hn : 0 < n) :
    (eps^n).y.natAbs.factorization q = (n*eps.y.natAbs).factorization q := by
  by_cases hzero : eps.y=0
  · obtain ⟨_,_,_,hy⟩ := pell_expansion_remainder eps (n-1)
    rw [Nat.sub_add_cancel hn,hzero,zero_mul] at hy
    simp [hy,hzero]
  have base : eps.y.natAbs≠0 := fun h => hzero (Int.natAbs_eq_zero.mp h)
  have all : ∀ j : ℕ, j≠0 → (eps^j).y.natAbs≠0 ∧
      (eps^j).y.natAbs.factorization q=(j*eps.y.natAbs).factorization q := by
    apply induction_on_primes
    · simp
    · simp [base]
    · intro l a pl ih nz
      have ap : a≠0 := fun e => nz (by rw [e,mul_zero])
      obtain ⟨nonzero,ihv⟩ := ih ap
      obtain ⟨k,mult,kpos,kv⟩ := pell_prime_multiplier (eps^a) pl pq dq
      have e : eps^(l*a)=(eps^a)^l := by rw [←pow_mul,Nat.mul_comm]
      rw [e,mult]
      refine ⟨mul_ne_zero nonzero kpos,?_⟩
      rw [Nat.factorization_mul nonzero kpos,Finsupp.add_apply,kv,ihv,Nat.mul_assoc,
        Nat.factorization_mul pl.ne_zero (mul_ne_zero ap base),Finsupp.add_apply,Nat.add_comm]
  exact (all n hn.ne').2
-- END PELL VALUATION
end Erdos889.PellValuation

namespace Erdos889.QuadraticSmooth

private theorem cube_le_two_pow {m : ℕ} (hm : 10 ≤ m) : m^3≤2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have step : (k+1)^3≤2*k^3 := by
      have k2 : 5*k ≤ k^2 := by nlinarith [Nat.mul_le_mul_right k (show 5 ≤ k by omega)]
      nlinarith [Nat.mul_le_mul_right (k^2) (show 5 ≤ k by omega)]
    omega

private theorem pell_growth {D : ℤ} (eps : Pell.Solution₁ D) (hx : 1 < eps.x)
    (hy : 0 < eps.y) (n : ℕ) : (2:ℤ)^n*eps.y ≤ (eps^(n+1)).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sx := Pell.Solution₁.x_pow_pos (show 0 < eps.x by omega) (n+1)
    have sy := Pell.Solution₁.y_pow_succ_pos (show 0 < eps.x by omega) hy n
    have grow := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ eps.x by omega) sy.le
    rw [pow_succ, show n+1+1=(n+1)+1 by rfl, pow_succ eps (n+1),Pell.Solution₁.y_mul]
    nlinarith [mul_pos sx hy]

private theorem quadratic_twist_bound (D : ℕ)
    (valuation : ∀ (eps : Pell.Solution₁ (D:ℤ)) (q n : ℕ), q.Prime → q^2∣D →
      0 < n → 1 < eps.x → 0 < eps.y →
      ((eps^n).y.natAbs).factorization q=(n*eps.y.natAbs).factorization q) :
    ∃ B : ℕ, ∀ x y : ℕ, 0 < y → x^2+1=D*y^2 →
      (∀ q : ℕ, q.Prime → q∣y → q^2∣D) → x ≤ B := by
  classical
  by_cases has : ∃ e : Pell.Solution₁ (D:ℤ), Pell.IsFundamental e
  · obtain ⟨eps,he⟩ := has
    let Y := eps.y.natAbs
    refine ⟨D*(10+4*D*Y)*Y,?_⟩
    intro x y hy eq support
    by_cases hx : x=0
    · omega
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : sol.x=2*(x:ℤ)^2+1 := rfl
    have sy : sol.y=2*(x:ℤ)*y := rfl
    obtain ⟨n,hn⟩ := he.eq_pow_of_nonneg (a:=sol) (by rw [sx]; positivity) (by rw [sy]; positivity)
    have nz : 0 < n := by
      by_contra! h
      have : n=0 := by omega
      rw [this,pow_zero] at hn
      have eqy := congrArg Pell.Solution₁.y hn
      rw [sy,Pell.Solution₁.y_one] at eqy
      have : 0<(x:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hx
      have pos : 0<2*(x:ℤ)*y := by positivity
      omega
    have YY : 0 < Y := by dsimp [Y]; exact Int.natAbs_pos.mpr he.2.1.ne'
    have imag : (eps^n).y.natAbs=2*x*y := by
      rw [←hn,sy,Int.natAbs_mul,Int.natAbs_mul]
      rfl
    have ydiv : y∣n*Y := by
      apply (Nat.factorization_le_iff_dvd hy.ne' (Nat.mul_pos nz YY).ne').mp
      intro q
      by_cases pq : q.Prime
      · by_cases dy : q∣y
        · have div : y∣2*x*y := dvd_mul_left _ _
          have nonz : 2*x*y≠0 := by positivity
          have le := (Nat.factorization_le_iff_dvd hy.ne' nonz).mpr div q
          rw [←imag,valuation eps q n pq (support q pq dy) nz he.1 he.2.1] at le
          exact le
        · simp [Nat.factorization_eq_zero_of_not_dvd dy]
      · simp [Nat.factorization_eq_zero_of_not_prime _ pq]
    have ybound := Nat.le_of_dvd (Nat.mul_pos nz YY) ydiv
    have Dx : x ≤ D*y := by
      have hD : 0 < D := by exact_mod_cast he.d_pos
      by_contra! large
      have h := Nat.mul_le_mul (show 1 ≤ D by omega) (Nat.le_refl (D*y^2))
      nlinarith [Nat.mul_self_lt_mul_self large]
    have expBound : 2^n*Y ≤ 4*x*y := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nz.ne'
      have low := pell_growth eps he.1 he.2.1 j
      have eqy := congrArg Pell.Solution₁.y hn
      rw [←eqy,sy] at low
      have castY : (Y:ℤ)=eps.y := Int.natAbs_of_nonneg he.2.1.le
      change (2:ℕ)^(j+1)*Y ≤ 4*x*y
      zify
      rw [castY,pow_succ]
      linarith
    have nbound : n≤10+4*D*Y := by
      by_cases big : 10 ≤ n
      · have cube := cube_le_two_pow big
        have upper := Nat.mul_le_mul Dx ybound
        have upper' := Nat.mul_le_mul (Nat.mul_le_mul_left D ybound) (Nat.le_refl (n*Y))
        have all : n^3*Y≤(4*D*Y)*(n^2*Y) := by
          nlinarith [Nat.mul_le_mul_right Y cube]
        have eqN : n^3*Y=n*(n^2*Y) := by ring
        rw [eqN] at all
        have := Nat.le_of_mul_le_mul_right all (by positivity : 0 < n^2*Y)
        omega
      · omega
    exact Dx.trans (by calc
      D*y ≤ D*(n*Y) := Nat.mul_le_mul_left _ ybound
      _ ≤ D*((10+4*D*Y)*Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ nbound)
      _ = _ := by ring)
  · refine ⟨0,?_⟩
    intro x y hy eq _
    by_contra! xbig
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : 1 < sol.x := by
      change 1<2*(x:ℤ)^2+1
      have hxZ : 0<(x:ℤ) := by exact_mod_cast xbig
      nlinarith [sq_pos_of_pos hxZ]
    exact has (Pell.IsFundamental.exists_of_not_isSquare
      (Pell.Solution₁.d_pos_of_one_lt_x sx) (Pell.Solution₁.d_nonsquare_of_one_lt_x sx))


/-- The greatest prime factor of x²+1 eventually exceeds each fixed bound. -/
theorem large_prime_of_square_add_one (T : ℕ) : ∃ B : ℕ, ∀ x : ℕ, B < x →
    ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣x^2+1 := by
  classical
  have bounds (D : ℕ) := quadratic_twist_bound D (fun eps q n pr dv hn _ _ =>
    Erdos889.PellValuation.pell_factorization_y_pow eps pr dv hn)
  choose bound covers using bounds
  let ds := Finset.Icc 1 ((T+1).factorial^3)
  refine ⟨ds.sup bound,?_⟩
  intro x hx
  by_contra missing
  have smooth (q : ℕ) (pr : q.Prime) (dv : q∣x^2+1) : q ≤ T := by
    by_contra! big
    exact missing ⟨q,pr,big,dv⟩
  obtain ⟨D,hd,y,_,hy,eq,dv⟩ := quadratic_smooth_decomposition T x smooth
  exact (not_lt_of_ge ((covers D x y hy eq dv).trans (Finset.le_sup (f:=bound) hd))) hx

end Erdos889.QuadraticSmooth

namespace Erdos889.EventualPrimeDivisibility

open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem smooth_fourth_decomposition (T n : ℕ) (hn : 0 < n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q ≤ T) :
    ∃ C z : ℕ, C ≤ T.factorial^3 ∧ 0 < C ∧ 0 < z ∧ n=C*z^4 := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    exact ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit⟩
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q ≤ t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨C,z,cap,hC,hz,form⟩ := ih m pos smaller
    have ppos : 0 < p := by dsimp [p]; omega
    have small : p^(e%4) ≤ p^3 := Nat.pow_le_pow_right ppos (by omega)
    have total : C*p^(e%4)≤(t+1).factorial^3 := by
      rw [Nat.factorial_succ,mul_pow,Nat.mul_comm ((t+1)^3)]
      exact Nat.mul_le_mul cap small
    refine ⟨C*p^(e%4),z*p^(e/4),total,Nat.mul_pos hC (pow_pos ppos _),
      Nat.mul_pos hz (pow_pos ppos _),?_⟩
    have ei : e=e%4+(e/4)*4 := by rw [Nat.mul_comm (e/4) 4,Nat.mod_add_div]
    calc
      n = p^e*m := fac.symm
      _ = p^(e%4+(e/4)*4)*(C*z^4) := by rw [←ei,form]
      _ = _ := by rw [pow_add,pow_mul,mul_pow]; ring

private theorem two_quadratic_factors {T u : ℕ} (hT : 4 ≤ T)
    (h₁ : ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣u^2+1)
    (h₂ : ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣(u+2)^2+1) :
    ∃ q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ T < q ∧ T < s ∧ q∣(u+1)^4+4 ∧ s∣(u+1)^4+4 := by
  obtain ⟨q,pq,hq,dq⟩ := h₁
  obtain ⟨s,ps,hs,ds⟩ := h₂
  let z := u+1
  let L := u^2+1
  let R := (u+2)^2+1
  change q∣L at dq
  change s∣R at ds
  have fac : (u+1)^4+4=L*R := by dsimp only [L,R]; ring
  refine ⟨q,s,pq,ps,?_,hq,hs,fac ▸ dvd_mul_of_dvd_left dq _,fac ▸ dvd_mul_of_dvd_right ds _⟩
  rintro rfl
  have diff : R=L+4*z := by dsimp only [R,L,z]; ring
  rw [diff] at ds
  have d4 := (Nat.dvd_add_iff_right dq).mpr ds
  have dz : q∣z := (pq.dvd_mul.mp d4).resolve_left (by
    intro dv; have := Nat.le_of_dvd (by decide : 0<4) dv; omega)
  have sum := dvd_add dq (dvd_mul_of_dvd_right dz 2)
  rw [show L+2*z=z^2+2 by dsimp only [L,z]; ring] at sum
  have sq : q∣z^2 := dz.trans (dvd_pow_self z (by decide : 2≠0))
  have bad := (Nat.dvd_add_iff_right sq).mpr sum
  have := Nat.le_of_dvd (by decide : 0<2) bad
  omega

/-- For any fixed prime q, if the largest prime factor of x²+1 tends to
infinity, all sufficiently large lowercase Erdős 889 solutions are divisible by q. -/
theorem eventual_prime_divisibility
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B < x → ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣x^2+1)
    (q : ℕ) (pq : q.Prime) :
    ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 → q∣n := by
  let M := q.factorial^3
  let T := q+4*M
  have mp : 0 < M := pow_pos q.factorial_pos 3
  have hT : 4 ≤ T := by dsimp only [T]; omega
  obtain ⟨K,hK⟩ := quadratic T
  refine ⟨M*(K+2)^4,?_⟩
  intro n hn sol
  by_contra avoid
  let k := q-n%q
  have rem := Nat.mod_lt n pq.pos
  have nr : n%q≠0 := fun z => avoid (Nat.dvd_of_mod_eq_zero z)
  have kp : 0 < k := by dsimp only [k]; omega
  have kq : k < q := by dsimp only [k]; omega
  have qd : q∣n+k := by
    refine ⟨n/q+1,?_⟩
    have h := Nat.mod_add_div n q
    rw [Nat.mul_add,mul_one]
    dsimp only [k]
    omega
  have smooth (r : ℕ) (pr : r.Prime) (dr : r∣n+k) : r ≤ q := by
    by_contra! large
    exact two_primes kp pq pr (by omega) kq (by omega) qd dr sol
  obtain ⟨C,z,cap,_cp,_zp,form⟩ := smooth_fourth_decomposition q (n+k) (by omega) smooth
  change C ≤ M at cap
  have large : K+2 < z := by
    by_contra! low
    have cmp := Nat.mul_le_mul cap (Nat.pow_le_pow_left low 4)
    omega
  let u := z-1
  have zu : z=u+1 := by dsimp only [u]; omega
  have ku : K < u := by omega
  obtain ⟨a,b,pa,pb,ne,ha,hb,da,db⟩ := two_quadratic_factors hT (hK u ku) (hK (u+2) (by omega))
  have fac : n+(k+4*C)=C*((u+1)^4+4) := by
    rw [zu] at form
    calc
      _ = (n+k)+4*C := by omega
      _ = _ := by rw [form]; ring
  have ub : k+4*C ≤ T := by dsimp only [T]; omega
  exact two_primes (k:=k+4*C) (by omega) pa pb ne (by omega) (by omega)
    (fac ▸ dvd_mul_of_dvd_right da C) (fac ▸ dvd_mul_of_dvd_right db C) sol


/-- Each fixed prime divides every sufficiently large exceptional starting point. -/
theorem eventually_divides_bad (q : ℕ) (pq : q.Prime) :
    ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 → q∣n :=
  eventual_prime_divisibility Erdos889.QuadraticSmooth.large_prime_of_square_add_one q pq

end Erdos889.EventualPrimeDivisibility

namespace Erdos889.UniformPowers
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem fifth_order {b q : ℕ} (pb : b.Prime) (ob : Odd b) (pq : q.Prime)
    (dq : q ∣ 2^b+1) (small : q < b) : q=3 := by
  -- The order of -2 divides both the prime b and q-1. It must be one.
  let _ : Fact q.Prime := ⟨pq⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^b+1) q).mpr dq
  push_cast at zero
  have eq : (-2 : ZMod q)^b=1 := by rw [ob.neg_pow]; linear_combination -zero
  have ne : (-2 : ZMod q) ≠ 0 := by
    intro h
    rw [h,zero_pow pb.ne_zero] at eq
    exact zero_ne_one eq
  have cases := (Nat.dvd_prime pb).mp (orderOf_dvd_of_pow_eq_one eq)
  have one : orderOf (-2 : ZMod q)=1 := cases.resolve_right (by
    intro same
    have dd := ZMod.orderOf_dvd_card_sub_one ne
    rw [same] at dd
    have := Nat.le_of_dvd (show 0 < q-1 by have := pq.two_le; omega) dd
    omega)
  have nz := orderOf_eq_one_iff.mp one
  have z : ((3 : ℕ) : ZMod q)=0 := by push_cast; linear_combination -nz
  exact (Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff _ _).mp z)

private theorem mersenne_left_factor {b L : ℕ} (pb : b.Prime) (lb : L < b) (hb : 3 < b) :
    ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1 := by
  have ob := pb.odd_of_ne_two (by omega)
  have no9 : ¬9 ∣ 2^b+1 := by
    have b3 : ¬3 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pb).mp h
      omega
    obtain ⟨w,hw⟩ := ob
    have rem : b%6=1 ∨ b%6=5 := by omega
    have pow : Nat.ModEq 9 (2^b) (2^(b%6)) := by
      have h : Nat.ModEq 9 (2^6) 1 := by decide
      calc
        2^b = 2^(b%6)*(2^6)^(b/6) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%6)*1^(b/6) [MOD 9] := (h.pow _).mul_left _
        _ = _ := by simp
    change 2^b%9=2^(b%6)%9 at pow
    rcases rem with h|h <;> rw [h] at pow <;> norm_num at pow <;> omega
  by_contra! none
  have big := Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ b by omega)
  norm_num at big
  have eq : 2^b+1=3^(2^b+1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have upper : q ≤ L := by by_contra! high; exact none q pq high dq
      exact fifth_order pb ob pq dq (by omega))
  generalize (2^b+1).primeFactorsList.length = e at eq
  have e2 : 2 ≤ e := by
    by_contra! bad
    interval_cases e <;> norm_num at eq
    all_goals omega
  exact no9 (eq ▸ (pow_dvd_pow (3 : ℕ) e2))


-- Reused when integrating into the reduction.
private theorem binary_plus_prime {s e : ℕ} (ps : s.Prime) (oe : Odd e) (dv : s∣2^e+1) :
    s%8=1 ∨ s%8=3 := by
  obtain ⟨j,hj⟩ := oe
  have epos : 0 < e := by omega
  have d2 := dvd_pow_self (2:ℕ) epos.ne'
  have ne : s≠2 := by rintro rfl; omega
  let _ : Fact s.Prime := ⟨ps⟩
  apply (ZMod.exists_sq_eq_neg_two_iff (p:=s) ne).mp
  refine ⟨(2:ZMod s)^(j+1),?_⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^e+1) s).mpr dv
  push_cast at zero
  rw [←pow_add,show j+1+(j+1)=e+1 by omega,pow_succ]
  linear_combination -2*zero

private theorem nonsplit_prime {N : ℕ} (seven : N%8=7) :
    ∃ s : ℕ, s.Prime ∧ s∣N ∧ ¬(s%8=1 ∨ s%8=3) := by
  by_contra missing
  have ok (l : List ℕ) (h : ∀ s ∈ l, s%8=1 ∨ s%8=3) : l.prod%8=1 ∨ l.prod%8=3 := by
    induction l with
    | nil => decide
    | cons a t ih =>
      have ha := h a (by simp)
      have ht := ih (fun u hu => h u (by simp [hu]))
      rw [List.prod_cons,Nat.mul_mod]
      rcases ha with h|h <;> rcases ht with w|w <;> rw [h,w] <;> decide
  have result := ok N.primeFactorsList (by
    intro s hs
    by_contra bad
    exact missing ⟨s,Nat.prime_of_mem_primeFactorsList hs,Nat.dvd_of_mem_primeFactorsList hs,bad⟩)
  rw [Nat.prod_primeFactorsList (by omega)] at result
  omega

theorem finite_prime_threshold (L : ℕ) : ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 →
    ∀ s : ℕ, s ≤ L → s.Prime → s∣n := by
  induction L with
  | zero =>
    refine ⟨0,?_⟩
    intro n hn sol s low ps
    have := ps.two_le
    omega
  | succ l ih =>
    obtain ⟨A,hA⟩ := ih
    by_cases prime : (l+1).Prime
    · obtain ⟨B,hB⟩ := Erdos889.EventualPrimeDivisibility.eventually_divides_bad _ prime
      refine ⟨max A B,?_⟩
      intro n hn sol s le ps
      by_cases same : s=l+1
      · exact same ▸ hB n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol
      · exact hA n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol s (by omega) ps
    · refine ⟨A,?_⟩
      intro n hn sol s le ps
      have ne : s≠l+1 := by rintro rfl; exact prime ps
      exact hA n hn sol s (by omega) ps

/-- A single bound suffices for all odd exponents from three through any prescribed R. -/
theorem bounded_odd_mersenne_exclusion (R : ℕ) : ∃ B : ℕ, ∀ n p b r : ℕ,
    B < n → p.Prime → p+1=2^b → 3 ≤ r → Odd r → r ≤ R → n+1=p^r → Erdos889.v_l 1 n≠1 := by
  let T := 2^R+1
  obtain ⟨B,allpr⟩ := finite_prime_threshold T
  refine ⟨max B ((2^(T+4))^R),?_⟩
  intro n p b r large pp base rlo odd upper eq sol
  have bigb : T+4 < b := by
    by_contra! small
    have hp := Nat.pow_le_pow_right (by decide : 0<2) small
    have a := Nat.pow_le_pow_left (show p≤2^(T+4) by omega) r
    have h := Nat.pow_le_pow_right (by positivity : 0<2^(T+4)) upper
    have m := Nat.le_max_right B ((2^(T+4))^R)
    omega
  have hb4 : 4 < b := lt_of_le_of_lt (Nat.le_add_left 4 T) bigb
  have ep : p=2^b-1 := by omega
  have pb := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have ob := pb.odd_of_ne_two (by omega)
  let k := 2^r+1
  have kT : k ≤ T := by dsimp [k,T]; exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) upper) 1
  have kp : 0 < k := by dsimp [k]; positivity
  have shift : n+k=p^r+2^r := by dsimp [k]; omega
  have db : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have dr : 8∣2^r := pow_dvd_pow 2 rlo
  have pm : Nat.ModEq 8 p 7 := by change p%8=7%8; omega
  have prm : Nat.ModEq 8 (p^r) 7 := by
    obtain ⟨j,hj⟩ := odd
    calc
      p^r ≡ 7^r [MOD 8] := pm.pow _
      _ = (7^2)^j*7 := by rw [hj,pow_succ,pow_mul]
      _ ≡ 1^j*7 [MOD 8] := ((by decide : Nat.ModEq 8 (7^2) 1).pow j).mul_right 7
      _ = 7 := by simp
  have sev : (p^r+2^r)%8=7 := by change (p^r)%8=7%8 at prm; omega
  obtain ⟨s,ps,ds,wrong⟩ := nonsplit_prime sev
  have hs : k < s := by
    by_contra! small
    have dn := allpr n (lt_of_le_of_lt (Nat.le_max_left ..) large) sol s (small.trans kT) ps
    have ds2 : s∣n+k := shift.symm ▸ ds
    have dk : s∣k := (Nat.dvd_add_iff_right dn).mpr ds2
    exact wrong (binary_plus_prime ps odd dk)
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show k < b by omega) (by omega)
  have diff : q≠s := by rintro rfl; exact wrong (binary_plus_prime pq ob dq)
  have dbase : q∣p+2 := by convert dq using 1; omega
  have together := dbase.trans (odd.nat_add_dvd_pow_add_pow p 2)
  exact two_primes kp pq ps diff hq hs (shift ▸ together) (shift ▸ ds) sol

/-- Any fixed finite range of exponents at least three admits a single bound, for arbitrary bases. -/
theorem bounded_power_exclusion (R : ℕ) : ∃ B : ℕ, ∀ n x r : ℕ,
    B < n → 1 < x → 3 ≤ r → r ≤ R → n+1=x^r → Erdos889.v_l 1 n≠1 := by
  obtain ⟨B,hB⟩ := bounded_odd_mersenne_exclusion R
  refine ⟨max B 81,?_⟩
  intro n x r large hx hr upper eq sol
  have lb := Nat.le_max_right B 81
  have hB' := Nat.le_max_left B 81
  have odd_base {y j : ℕ} (hj : 0 < j) (e : n+1=y^j) : Odd y := by
    apply Nat.not_even_iff_odd.mp
    intro even
    have dd : 2∣n+1 := e ▸ (even_iff_two_dvd.mp even).trans (dvd_pow_self y hj.ne')
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  have rule {y j : ℕ} (hy : 1 < y) (lo : 3 ≤ j) (hi : j ≤ R)
      (oj : Odd j) (e : n+1=y^j) : False := by
    have oy := odd_base (by omega) e
    obtain ⟨b,base⟩ := odd_power_root_neighbor oy hy oj (by omega) e sol
    have pure := prime_power_succ (n:=n) (by omega) sol
    rw [e,isPrimePow_pow_iff (by omega : j≠0)] at pure
    obtain ⟨p,a,pp,pa,he⟩ := (isPrimePow_nat_iff _).mp pure
    have op := pp.odd_of_ne_two (by
      rintro rfl
      have div := dvd_pow_self (2:ℕ) pa.ne'
      rw [he] at div
      exact (Nat.not_even_iff_odd.mpr oy) (even_iff_two_dvd.mpr div))
    have one := mersenne_power_exponent op pp.one_lt pa (he.symm ▸ base)
    rw [one,pow_one] at he
    subst y
    exact hB n p b j (by omega) pp base lo oj hi e sol
  by_cases o : Odd r
  · exact rule hx hr upper o eq
  · have even : r%2=0 := by rw [Nat.odd_iff] at o; omega
    by_cases four : r%4=0
    · let y := x^(r/4)
      have ey : n+1=y^4 := by dsimp [y]; rw [←pow_mul,show r/4*4=r by omega,eq]
      have bigy : 3 < y := by
        by_contra! small
        have ly := Nat.pow_le_pow_left small 4
        norm_num at ly
        omega
      obtain ⟨p,q,pp,pq,ne,hp,hq,dp,dq⟩ := fourth_power_witness (odd_base (by decide) ey) bigy
      have rearr : n+5=y^4+4 := by omega
      exact two_primes (k:=5) (by decide) pp pq ne hp hq (rearr ▸ dp) (rearr ▸ dq) sol
    · have e : n+1=(x^2)^(r/2) := by rw [←pow_mul, show 2*(r/2)=r by omega,eq]
      exact rule (by nlinarith) (by omega) (by omega) (by rw [Nat.odd_iff]; omega) e

end Erdos889.UniformPowers

namespace Erdos889.PrimitivePowers
open Polynomial


private theorem power_cyclotomic_order {p n q : ℕ} (hn : 0 < n) (pq : q.Prime)
    (hd : q ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs) :
    orderOf (p : ZMod q) = n / q ^ n.factorization q ∧
      n / q ^ n.factorization q ∣ q - 1 := by
  let : Fact q.Prime := ⟨pq⟩
  have hr : IsRoot (cyclotomic n (ZMod q)) (Nat.castRingHom (ZMod q) p) := by
    have c : ((p : ℤ) : ZMod q) = ↑(Int.castRingHom (ZMod q) p) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod q), eval_map, Nat.coe_castRingHom,
      ← Int.cast_natCast, c, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact_mod_cast hd
  have hc : ¬q ∣ p := pq.coprime_iff_not_dvd.mp (coprime_of_root_cyclotomic hn hr).symm
  let m := n / q ^ n.factorization q
  let : NeZero (m : ZMod q) := NeZero.of_not_dvd _ (Nat.not_dvd_ordCompl pq hn.ne')
  have form : q ^ n.factorization q * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hr' : (cyclotomic (q ^ n.factorization q * m) (ZMod q)).IsRoot (p : ZMod q) := by
    rw [form]
    exact hr
  have eqn := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hr').eq_orderOf
  refine ⟨eqn.symm, ?_⟩
  rw [show n / q ^ n.factorization q = orderOf (p : ZMod q) from eqn]
  exact ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hc)

private theorem power_cyclotomic_div {p n d : ℕ} (hp : 1 ≤ p) (hd : d ∈ n.properDivisors) :
    (p ^ d - 1) * ((cyclotomic n ℤ).eval (p : ℤ)).natAbs ∣ p ^ n - 1 := by
  have h := eval_dvd (x := (p : ℤ))
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hd)
  simp only [eval_mul, eval_sub, eval_X_pow, eval_one] at h
  have castpow (k : ℕ) : (p : ℤ)^k - 1 = ((p^k-1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hp), Nat.cast_pow, Nat.cast_one]
  have h' := Int.natAbs_dvd_natAbs.mpr h
  simpa only [castpow, Int.natAbs_mul, Int.natAbs_natCast] using h'

private theorem power_cyclotomic_no_square {p n q : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (hn : 2 < n) (pq : q.Prime) (dn : q ∣ n)
    (hF : q ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs) :
    ¬ q^2 ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs := by
  let : Fact q.Prime := ⟨pq⟩
  let d := n / q
  let a := p^d
  have form : d*q=n := Nat.div_mul_cancel dn
  have dpos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) dn) pq.pos
  have apos : 1 < a := Nat.one_lt_pow dpos.ne' (by omega : 1 < p)
  have dmem : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr
    ⟨⟨q,form.symm⟩, Nat.div_lt_self (by omega) pq.one_lt⟩
  have divF := power_cyclotomic_div (p := p) (by omega) dmem
  have power : a^q=p^n := by rw [show a = p ^ d by rfl, ← pow_mul, form]
  rw [← power] at divF
  change (a-1) * _ ∣ a^q-1 at divF
  obtain ⟨ordp,orddiv⟩ := power_cyclotomic_order (by omega) pq hF
  have total : q ^ n.factorization q * (n / q ^ n.factorization q) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n q
  intro hs
  have div2 : (a-1)*q^2 ∣ a^q-1 := (Nat.mul_dvd_mul_left _ hs).trans divF
  by_cases qt : q=2
  · subst q
    have m1 : n / 2 ^ n.factorization 2 = 1 := Nat.dvd_one.mp orddiv
    rw [m1, mul_one] at total
    have ee : 2 ≤ n.factorization 2 := by
      by_contra! h
      interval_cases h' : n.factorization 2 <;> simp at total <;> omega
    obtain ⟨k,hk⟩ : ∃ k, n.factorization 2 = k+2 := ⟨_, (Nat.sub_add_cancel ee).symm⟩
    have dk : d = 2^k*2 := by rw [hk, pow_succ, pow_succ] at total; omega
    have ak : a = (p^(2^k))^2 := by change p^d = _; rw [dk,pow_mul]
    have neq : a^2-1=(a-1)*(a+1) := by
      have hh : a-1+1=a := by omega
      rw [← hh]
      simp only [Nat.add_sub_cancel]
      have e : (a-1+1)^2=(a-1)*(a-1+1+1)+1 := by ring
      omega
    rw [neq] at div2
    have ff := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < a-1) div2
    obtain ⟨j,hj⟩ := oddp.pow (n:=2^k)
    rw [ak,hj] at ff
    obtain ⟨z,hz⟩ := ff
    have eh : (2*j+1)^2+1 = 4*(j*j+j)+2 := by ring
    omega

  · have md : orderOf (p : ZMod q) ∣ n := ⟨q^n.factorization q, by
      rw [ordp,mul_comm,total]⟩
    have ax : (a : ZMod q)^q = 1 := by
      rw [show a = p^d from rfl, Nat.cast_pow, ← pow_mul, form]
      exact orderOf_dvd_iff_pow_eq_one.mp md
    rw [ZMod.pow_card] at ax
    have hdiv : q ∣ a-1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, ax, sub_self]
    have na : ¬ q ∣ a := by
      intro h
      have := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [ax] at this
      exact one_ne_zero this
    have vv := padicValNat.pow_sub_pow (p:=q) (x:=a) (y:=1)
      (pq.odd_of_ne_two qt) apos hdiv na pq.ne_zero
    simp only [one_pow,padicValNat_self] at vv
    obtain ⟨u,hu⟩ := div2
    have hpos := Nat.one_lt_pow pq.ne_zero apos
    have u0 : u ≠ 0 := by intro e; rw [e,mul_zero] at hu; omega
    rw [hu, padicValNat.mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ pq.ne_zero)) u0,
      padicValNat.mul (by omega) (pow_ne_zero _ pq.ne_zero), padicValNat.pow,
      padicValNat_self] at vv
    omega

private theorem power_primitive_prime {p n : ℕ} (hp : 3 ≤ p) (oddp : Odd p) (hn : 2 < n) :
    ∃ q : ℕ, q.Prime ∧ orderOf (p : ZMod q) = n := by
  let F := ((cyclotomic n ℤ).eval (p : ℤ)).natAbs
  have hF : 1 < F := lt_of_le_of_lt (by omega : 1 ≤ p-1)
    (sub_one_lt_natAbs_cyclotomic_eval (n:=n) (by omega) (by omega))
  by_contra miss
  have dividing {q : ℕ} (pq : q.Prime) (dv : q ∣ F) : q ∣ n := by
    by_contra nd
    have o := (power_cyclotomic_order (p:=p) (n:=n) (by omega) pq dv).1
    simp [Nat.factorization_eq_zero_of_not_dvd nd] at o
    exact miss ⟨q,pq,o⟩
  have lesser {q s : ℕ} (pq : q.Prime) (ps : s.Prime) (hq : q ∣ F)
      (hs : s ∣ F) (ne : s ≠ q) : s < q := by
    have hd := dividing ps hs
    have form := Nat.ordProj_mul_ordCompl_eq_self n q
    change q^n.factorization q * (n/q^n.factorization q)=n at form
    rw [← form] at hd
    rcases ps.dvd_mul.mp hd with h | h
    · exact (ne ((Nat.prime_dvd_prime_iff_eq ps pq).mp (ps.dvd_of_dvd_pow h))).elim
    · have hlt := Nat.le_of_dvd (by have := pq.one_lt; omega : 0 < q-1)
        (h.trans (power_cyclotomic_order (p:=p) (n:=n) (by omega) pq hq).2)
      omega
  obtain ⟨q,pq,hq⟩ := Nat.exists_prime_and_dvd (n:=F) (by omega)
  have fpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : F ≠ 0) (p:=q) (by
    intro s ps hs
    by_contra ne
    have h := lesser pq ps hq hs ne
    have h' := lesser ps pq hs hq (Ne.symm ne)
    omega)
  have dn := dividing pq hq
  have tdiv := Nat.totient_dvd_of_dvd dn
  rw [Nat.totient_prime pq] at tdiv
  have tle := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0 < n)) tdiv
  have qF : q < F := calc
    q ≤ 2^(q-1) := by have h : q-1 < 2^(q-1) := Nat.lt_two_pow_self; omega
    _ ≤ (p-1)^n.totient := by gcongr <;> omega
    _ < F := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (by omega) (by omega)
  have len : 2 ≤ F.primeFactorsList.length := by
    by_contra! h
    interval_cases he : F.primeFactorsList.length <;> simp at fpow <;> omega
  apply power_cyclotomic_no_square hp oddp hn pq dn hq
  change q^2 ∣ F
  conv_rhs => rw [fpow]
  exact pow_dvd_pow q len

private theorem power_primitive_plus {p k : ℕ} (hp : 3 ≤ p) (oddp : Odd p) (hk : 1 < k) :
    ∃ q : ℕ, q.Prime ∧ orderOf (p : ZMod q) = 2*k ∧ 2*k < q ∧ q ∣ p^k+1 := by
  obtain ⟨q,pq,eqo⟩ := power_primitive_prime hp oddp (n:=2*k) (by omega)
  let : Fact q.Prime := ⟨pq⟩
  have eq1 := pow_orderOf_eq_one (p : ZMod q)
  rw [eqo] at eq1
  have p0 : (p : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : 2*k ≠ 0)] at eq1
    exact zero_ne_one eq1
  have dl := ZMod.orderOf_dvd_card_sub_one p0
  rw [eqo] at dl
  have small := Nat.le_of_dvd (by have := pq.one_lt; omega : 0 < q-1) dl
  refine ⟨q,pq,eqo,by omega,?_⟩
  have sq1 : ((p : ZMod q)^k)^2 = 1 := by rw [← pow_mul,Nat.mul_comm k 2]; exact eq1
  rcases sq_eq_one_iff.mp sq1 with bad | good
  · have dk := orderOf_dvd_of_pow_eq_one bad
    rw [eqo] at dk
    have := Nat.le_of_dvd (by omega : 0 < k) dk
    omega
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_pow,good,neg_add_cancel]

private theorem power_exponent_odd_witness {p k u t : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (ht : 1 < t) (oddt : Odd t) (hk : 1 < k) (gap : p^u < 2*k) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^(t*k+u)+d ∧ s ∣ p^(t*k+u)+d := by
  have ltprod : k < t*k := by nlinarith
  obtain ⟨q,pq,oq,hq,dq⟩ := power_primitive_plus hp oddp (k:=t*k) (by omega)
  obtain ⟨s,ps,os,hs,ds⟩ := power_primitive_plus hp oddp hk
  have differ : q ≠ s := by intro e; subst s; omega
  have d3 : p^k+1 ∣ p^(t*k)+1 := by
    rw [Nat.mul_comm t k, pow_mul]
    simpa only [one_pow] using oddt.nat_add_dvd_pow_add_pow (p^k) 1
  have factor : p^(t*k+u)+p^u=(p^(t*k)+1)*p^u := by rw [pow_add,add_mul,one_mul]
  refine ⟨p^u,q,s,pq,ps,differ,by omega,by omega,?_,?_⟩ <;> rw [factor]
  · exact dvd_mul_of_dvd_left dq _
  · exact dvd_mul_of_dvd_left (ds.trans d3) _

theorem power_missing_exponent_bound {p r : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (pr : r.Prime) (hr : 5 ≤ r)
    (miss : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d) :
    2*(r-2) ≤ 3*p^2 := by
  have nz : r%3 ≠ 0 := by
    intro eqn
    have dv := Nat.dvd_of_mod_eq_zero eqn
    have eqr := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) pr).mp dv
    omega
  by_contra! h
  have pp : p ≤ p^2 := by nlinarith
  let k := r/3
  have hk : 1 < k := by dsimp [k]; omega
  have eu := Nat.mod_add_div r 3
  change r%3+3*k=r at eu
  by_cases eqn : r%3=1
  · have ww := power_exponent_odd_witness hp oddp (u:=1) (by decide : 1 < 3)
      (by decide) hk (by simp; omega)
    apply miss
    rwa [show 3*k+1=r by omega] at ww
  · have ww := power_exponent_odd_witness hp oddp (u:=2) (by decide : 1 < 3)
      (by decide) hk (by omega)
    apply miss
    rwa [show 3*k+2=r by omega] at ww



theorem power_missing_exponent_linear {p r : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (modr : r%3 = 1)
    (miss : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d) :
    2*(r-1) ≤ 3*p := by
  by_contra! h
  let k := r/3
  have eu := Nat.mod_add_div r 3
  change r%3+3*k=r at eu
  have ww := power_exponent_odd_witness hp oddp (u:=1) (by decide : 1 < 3)
    (by decide) (k:=k) (by omega) (by simp; omega)
  apply miss
  rwa [show 3*k+1=r by omega] at ww



private theorem prime_power_order_two {l k : ℕ} (pl : l.Prime) (hk : 0 < k) :
    ∃ q : ℕ, q.Prime ∧ orderOf (2 : ZMod q) = l ^ k := by
  have hn := Nat.one_lt_pow hk.ne' pl.one_lt
  let F := ((cyclotomic (l^k) ℤ).eval 2).natAbs
  have hf : 1 < F := sub_one_lt_natAbs_cyclotomic_eval (q:=2) hn (by decide)
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (n:=F) (by omega)
  let : Fact q.Prime := ⟨pq⟩
  have eqn := (power_cyclotomic_order (p:=2) (n:=l^k) (by omega) pq dq).1
  by_cases nd : q ∣ l^k
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pq pl).mp (pq.dvd_of_dvd_pow nd)
    rw [Nat.factorization_pow_self pq, Nat.div_self (pow_pos pq.pos _)] at eqn
    have h := pow_orderOf_eq_one (2 : ZMod q)
    simp only [Nat.cast_ofNat] at eqn
    rw [eqn,pow_one] at h
    have z : (1 : ZMod q)=0 := by linear_combination h
    exact (one_ne_zero z).elim
  · simp only [Nat.factorization_eq_zero_of_not_dvd nd,pow_zero,Nat.div_one,Nat.cast_ofNat] at eqn
    exact ⟨q,pq,eqn⟩

/-- Local divisibility of a Mersenne power predecessor forces a congruence on its index. -/
theorem mersenne_index_multiple_of_fixed_modulus {m p b r : ℕ}
    (hm : 0 < m) (hp : 0 < p) (hb : 0 < b) (pr : r.Prime)
    (hr : 2^m < r) (base : p+1=2^b)
    (allDiv : ∀ q : ℕ, q.Prime → q ∣ 2^m-1 → q ∣ p^r-1) : m ∣ b-1 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro l k pl d
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨q,pq,oq⟩ := prime_power_order_two pl hk
  let : Fact q.Prime := ⟨pq⟩
  have jm : (2 : ZMod q)^m=1 := orderOf_dvd_iff_pow_eq_one.mp (oq ▸ d)
  have htm : 1 < 2^m := Nat.one_lt_pow hm.ne' (by decide)
  have dm : q ∣ 2^m-1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, jm, sub_self]
  have qr := Nat.le_of_dvd (by omega : 0 < 2^m-1) dm
  have dp := (ZMod.natCast_eq_zero_iff _ _).mpr (allDiv q pq dm)
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hp), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at dp
  have notzero : (p : ZMod q) ≠ 0 := by
    intro z
    rw [z,zero_pow pr.ne_zero] at dp
    exact zero_ne_one dp
  have od := ZMod.orderOf_dvd_card_sub_one notzero
  have ol := Nat.le_of_dvd (by have := pq.one_lt; omega : 0 < q-1) od
  have rdiv := orderOf_dvd_of_pow_eq_one dp
  have one : orderOf (p : ZMod q)=1 := by
    rcases (Nat.dvd_prime pr).mp rdiv with eq | eq
    · exact eq
    · omega
  have pp := pow_orderOf_eq_one (p : ZMod q)
  rw [one,pow_one] at pp
  have bq : (p : ZMod q)+1=2^b := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ZMod q)) base
  rw [pp,one_add_one_eq_two] at bq
  have twon : (2 : ZMod q) ≠ 0 := by
    intro q2
    rw [q2,zero_pow hm.ne'] at jm
    exact zero_ne_one jm
  have prod : (2 : ZMod q)^(b-1)*2=1*2 := by
    rw [← pow_succ, show b-1+1=b by omega, ← bq, one_mul]
  exact oq ▸ orderOf_dvd_of_pow_eq_one (mul_right_cancel₀ twon prod)


/-- Every fixed positive modulus eventually divides the Mersenne index minus one. -/
theorem eventually_index_multiple_of_fixed_modulus (bad : ℕ → Prop)
    (divisibility : ∀ L : ℕ, ∃ B : ℕ, ∀ n : ℕ, B < n → bad n →
      ∀ q : ℕ, q ≤ L → q.Prime → q ∣ n)
    (bounded : ∀ R : ℕ, ∃ B : ℕ, ∀ n p r : ℕ,
      B < n → 1 < p → 3 ≤ r → r ≤ R → n+1=p^r → ¬bad n)
    (m : ℕ) (hm : 0 < m) :
    ∃ B : ℕ, ∀ n p r b : ℕ, B < n → bad n → p.Prime → r.Prime → 3 ≤ r →
      p+1=2^b → n+1=p^r → m ∣ b-1 := by
  obtain ⟨C,hC⟩ := divisibility (2^m)
  obtain ⟨D,hD⟩ := bounded (2^m)
  refine ⟨max C D,?_⟩
  intro n p r b hn sol pp pr r3 base he
  have hc := (Nat.le_max_left C D).trans_lt hn
  have hd := (Nat.le_max_right C D).trans_lt hn
  have hi : 2^m < r := by
    by_contra! h
    exact hD n p r hd pp.one_lt r3 h he sol
  have bh : 0 < b := by
    by_contra! neg
    have bz : b=0 := by omega
    rw [bz,pow_zero] at base
    have := pp.two_le
    omega
  apply mersenne_index_multiple_of_fixed_modulus hm pp.pos bh pr hi base
  intro q pq dq
  have hp := Nat.one_lt_pow hm.ne' (by decide : 1 < 2)
  have le := Nat.le_of_dvd (by omega : 0 < 2^m-1) dq
  rw [show p^r-1=n by omega]
  exact hC n hc sol q (by omega) pq


end Erdos889.PrimitivePowers
namespace Erdos889.Missing
open Finset

lemma fresh_iff {n k p : ℕ} (hp : 0 < p) (hd : p ∣ n+k) :
    (∀ i ∈ range k, ¬p ∣ n+i) ↔ k < p := by
  constructor
  · intro h
    by_contra! hle
    have hdiff : n + (k-p) = n+k-p := by omega
    exact h (k-p) (mem_range.mpr (by omega)) (hdiff ▸ Nat.dvd_sub hd (dvd_refl p))
  · intro h i hi hdiv
    have hi' := mem_range.mp hi
    have hsub : n+k-(n+i) = k-i := by omega
    have hd' : p ∣ k-i := hsub ▸ Nat.dvd_sub hd hdiv
    have := Nat.le_of_dvd (by omega : 0 < k-i) hd'
    omega

theorem v_as_card (n k : ℕ) :
    v n k = ((n+k).primeFactors.filter (k < ·)).card := by
  unfold v
  congr 1
  ext p
  simp only [mem_filter]
  exact and_congr_right fun h => fresh_iff (Nat.prime_of_mem_primeFactors h).pos
    (Nat.dvd_of_mem_primeFactors h)

-- BEGIN MISSING WITNESS
/-- Absence of a two-prime witness exactly bounds every count at the predecessor, and offset one attains the bound. -/
theorem predecessor_solution_of_missing {N : ℕ} (big : 1 < N)
    (none : ¬ ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ N+d ∧ s ∣ N+d) : v_l 1 (N-1)=1 := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    have bound : v (N-1) k ≤ 1 := by
      rw [v_as_card,Finset.card_le_one]
      intro q hq s hs
      obtain ⟨cq,bq⟩ := Finset.mem_filter.mp hq
      obtain ⟨cs,bs⟩ := Finset.mem_filter.mp hs
      have eq : N+(k-1)=(N-1)+k := by omega
      by_contra ne
      exact none ⟨k-1,q,s,Nat.prime_of_mem_primeFactors cq,Nat.prime_of_mem_primeFactors cs,ne,
        by omega,by omega,eq ▸ Nat.dvd_of_mem_primeFactors cq,eq ▸ Nat.dvd_of_mem_primeFactors cs⟩
    exact_mod_cast bound
  · obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show N≠1 by omega)
    have eq : N-1+1=N := by omega
    have first : 1 ≤ v (N-1) 1 := by
      rw [v_as_card,eq]
      exact Finset.card_pos.mpr ⟨q,Finset.mem_filter.mpr ⟨pq.mem_primeFactors dq (by omega),pq.one_lt⟩⟩
    exact (show (1 : ℕ∞) ≤ (v (N-1) 1 : ℕ∞) by exact_mod_cast first).trans
      (le_iSup_of_le 1 (le_iSup_of_le (by decide : 1≤1) le_rfl))
-- END MISSING WITNESS

end Erdos889.Missing

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H3_R1
open Erdos889
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2


open Finset
private theorem seventeen_smooth_cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

private theorem seventeen_smooth_legendre (m n : ℕ) [Fact m.Prime] (hm : 2 < m) :
    legendreSym m (n:ℤ) = if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1 := by
  have cast : ((n:ℤ):ZMod m)=(n:ZMod m) := by simp
  by_cases z : n%m=0
  · rw [if_pos z,legendreSym.eq_zero_iff,cast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero z
  rw [if_neg z]
  have nz : ((n:ℤ):ZMod m)≠0 := by
    intro h
    rw [cast] at h
    exact z (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff n m).mp h))
  have power : ((n%m)^(m/2))%m=1 ↔ (n:ZMod m)^(m/2)=1 := by
    have eq := ZMod.natCast_eq_natCast_iff' ((n%m)^(m/2)) 1 m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at eq
    simpa only [Nat.cast_pow,ZMod.natCast_mod,Nat.cast_one] using eq.symm
  have sign := legendreSym.eq_pow m (n:ℤ)
  rw [cast] at sign
  rcases legendreSym.eq_one_or_neg_one m nz with h|h
  · rw [h,Int.cast_one] at sign
    rw [h,if_pos (power.mpr sign.symm)]
  · rw [h,Int.cast_neg,Int.cast_one] at sign
    rw [h,if_neg]
    intro bad
    have eq : (-1:ZMod m)=1 := sign.trans (power.mp bad)
    have zero : ((2:ℕ):ZMod m)=0 := by push_cast; linear_combination -eq
    have dd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    have le := Nat.le_of_dvd (by decide) dd
    omega

private theorem seventeen_smooth_character_mul (m : ℕ) (ok : m=4 ∨ m=8 ∨ (m.Prime ∧ 2 < m)) :
    let char (n : ℕ) : ℤ := if m=4 then (if n%2=0 then 0 else if n%4=1 then 1 else -1)
    else if m=8 then (if n%2=0 then 0 else if n%8=1 ∨ n%8=7 then 1 else -1)
    else if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1
    ∀ u v, char (u*v)=char u*char v := by
  dsimp only
  rcases ok with rfl|rfl|⟨pm,hm⟩
  · intro u v
    simp only [if_true]
    simpa only [ZMod.χ₄_nat_eq_if_mod_four] using
      (show ZMod.χ₄ ((u*v:ℕ):ZMod 4)=ZMod.χ₄ (u:ZMod 4)*ZMod.χ₄ (v:ZMod 4) by rw [Nat.cast_mul,map_mul])
  · intro u v
    simp only [show (8:ℕ)≠4 by decide,if_false,if_true]
    simpa only [ZMod.χ₈_nat_eq_if_mod_eight] using
      (show ZMod.χ₈ ((u*v:ℕ):ZMod 8)=ZMod.χ₈ (u:ZMod 8)*ZMod.χ₈ (v:ZMod 8) by rw [Nat.cast_mul,map_mul])
  · intro u v
    let _ : Fact m.Prime := ⟨pm⟩
    have n4 : m≠4 := by rintro rfl; norm_num at pm
    have n8 : m≠8 := by rintro rfl; norm_num at pm
    simp only [n4,n8,if_false,←seventeen_smooth_legendre m _ hm,Nat.cast_mul,legendreSym.mul]

-- BEGIN SEVENTEEN
private theorem seventeen_smooth_powMod_eq (a e m : ℕ) : (fun (a e m : ℕ) => Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m) (fun _ f n => (f (n/2))^2 * a^(n%2) % m) (e.log2+1) e) a e m = a^e % m := by
  let f (k : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m)
    (fun _ g n => (g (n/2))^2 * a^(n%2) % m) k
  have aux (k n : ℕ) (bound : n<2^k) : f k n = a^n % m := by
    induction k generalizing n with
    | zero =>
      have h : n=0 := by simpa using bound
      subst n
      simp [f]
    | succ k ih =>
      have half : n/2 < 2^k := by rw [pow_succ] at bound; omega
      change (f k (n/2))^2 * a^(n%2) % m = a^n % m
      rw [ih _ half]
      calc
        _ = ((a^(n/2))^2 * a^(n%2))%m :=
          ((Nat.mod_modEq _ _).pow 2).mul_right _
        _ = a^n % m := by
          rw [← pow_mul,← pow_add,show n/2*2+n%2=n by omega]
  change f (e.log2+1) e = a^e % m
  apply aux (e.log2+1) e
  by_cases h : e=0
  · subst e
    decide
  · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)


private theorem seventeen_smooth_residue {p b T k m : ℕ} (base : p+1=2^b) (idx : b%T=k)
    (hm : 1 < m) (per : 2^T%m=1) :
    Nat.ModEq m p ((2^k%m+m-1)%m) := by
  have period : Nat.ModEq m (2^T) 1 := by change 2^T%m=1%m; rwa [Nat.mod_eq_of_lt hm]
  have c := seventeen_smooth_cycle period b
  rw [idx,←base] at c
  have h : Nat.ModEq m ((2^k%m+m-1)+1) (2^k) := by
    rw [show 2^k%m+m-1+1=2^k%m+m by omega]
    change (2^k%m+m)%m=2^k%m
    simp
  exact (Nat.ModEq.add_right_cancel' 1 (c.trans h.symm)).trans (Nat.mod_modEq _ _).symm

private theorem mersenne_character_primes : ∀ s ∈ [3,5,7,11,13,17,19,23,29,31,37,41,43,53,67,71,73,79,89,103,127,131,137,151,157,191,211,229,239,281,307,313,337,397,409,433,457,571,613,631,761,911,919,937,953,991,1009,1217,1249,1321,1483,1597,1873,2129,2281,2521,3121,3191,3361,3433,4733,6271,6841,9241,10711,11287,13681,14449,18481,21169,30097,34511] , Nat.Prime s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num1

private theorem mersenne_character_row {r p b T k : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%T=k)
    (d q : ℕ) (S ms : List ℕ) (pm : ℕ → ℕ → ℕ → ℕ)
    (hpm : ∀ a e m, pm a e m=a^e%m)
    {pool : List ℕ} (facts : ∀ s ∈ pool, s.Prime)
    (ok :
      let V (m : ℕ) := ((pm 2 k m+m-1)%m)^r+d
      let C (m n : ℕ) : ℤ := if n%m=0 then 0 else if pm (n%m) (m/2) m=1 then 1 else -1
      q∈pool ∧ d+1 < q ∧ q∈S ∧ pm 2 T q=1 ∧ V q%q=0 ∧
      (∀ s ∈ List.range (d+2), s.Prime → s∈S ∨ (pm 2 T s=1 ∧ V s%s≠0)) ∧
      (∀ m ∈ ms, m∈pool ∧ 2 < m ∧ m≠4 ∧ m≠8 ∧ pm 2 T m=1) ∧
      (∀ s ∈ S, (ms.map (fun m => C m s)).prod=1) ∧
      (ms.map (fun m => C m (V m))).prod= -1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^r+d ∧ s ∣ p^r+d := by
  let V (m : ℕ) := ((pm 2 k m+m-1)%m)^r+d
  let C (m n : ℕ) : ℤ := if n%m=0 then 0 else if pm (n%m) (m/2) m=1 then 1 else -1
  obtain ⟨qm,large,qmem,qper,qzero,small,mods,good,bad⟩ := ok
  have pq := facts q qm
  have red {m : ℕ} (hm : 1 < m) (per : pm 2 T m=1) : Nat.ModEq m (p^r+d) (V m) := by
    dsimp only [V]; rw [hpm]
    exact ((seventeen_smooth_residue base idx hm ((hpm ..) ▸ per)).pow r).add_right d
  have dq : q ∣ p^r+d := Nat.modEq_zero_iff_dvd.mp ((red pq.one_lt qper).trans qzero)
  by_contra missing
  have support (s : ℕ) (ps : s.Prime) (ds : s ∣ p^r+d) : s∈S := by
    by_cases h : s=q
    · exact h ▸ qmem
    by_cases high : d+1 < s
    · exact (missing ⟨d,q,s,pq,ps,Ne.symm h,large,high,dq,ds⟩).elim
    rcases small s (List.mem_range.mpr (by omega)) ps with mem|⟨per,nonzero⟩
    · exact mem
    exact (nonzero ((red ps.one_lt per).symm.trans (Nat.modEq_zero_iff_dvd.mpr ds))).elim
  let chi (n : ℕ) := (ms.map (fun m => C m n)).prod
  have mul (u v : ℕ) : chi (u*v)=chi u*chi v := by
    have gm (m) (hm : m∈ms) : C m (u*v)=C m u*C m v := by
      obtain ⟨known,lt,h4,h8,_⟩ := mods m hm
      have prim := facts m known
      simpa only [C,hpm,h4,h8,if_false] using
        (seventeen_smooth_character_mul m (Or.inr (Or.inr ⟨prim,lt⟩)) u v)
    have gen (l : List ℕ) (h : ∀ m ∈ l, C m (u*v)=C m u*C m v) :
        (l.map (fun m => C m (u*v))).prod=(l.map (fun m => C m u)).prod*(l.map (fun m => C m v)).prod := by
      induction l with
      | nil => simp
      | cons m tail ih =>
        simp only [List.map_cons,List.prod_cons]
        rw [h m (by simp),ih (fun j hj => h j (by simp [hj]))]
        ring
    exact gen ms gm
  have neg : chi (p^r+d)= -1 := by
    apply Eq.trans (congrArg List.prod (List.map_congr_left (l:=ms) (f:=fun m => C m (p^r+d)) (g:=fun m => C m (V m)) ?_)) bad
    intro m hm
    obtain ⟨_,lt,_,_,per⟩ := mods m hm
    have eq : (p^r+d)%m=V m%m := red (by omega) per
    simp only [C,eq]
  have one : chi 1=1 := by
    have h := mul 1 (p^r+d)
    rw [one_mul,neg] at h
    omega
  have gen (l : List ℕ) (h : ∀ s ∈ l,s ∈ S) : chi l.prod=1 := by
    induction l with
    | nil => exact one
    | cons s tail ih =>
      rw [List.prod_cons,mul,show chi s=1 from good s (h s (by simp)),one_mul]
      exact ih (fun j hj => h j (by simp [hj]))
  have pos := gen (p^r+d).primeFactorsList (fun s h => support s (Nat.prime_of_mem_primeFactorsList h) (Nat.dvd_of_mem_primeFactorsList h))
  rw [Nat.prod_primeFactorsList (by positivity),neg] at pos
  contradiction


set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_361 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=361) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 14 29 [2,3,5,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_673 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=673) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_841 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=841) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 8 37 [2,3,37] [433] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 8 37 [2,3,37] [337] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1321 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1321) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1513 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1513) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 5 11 [2,3,11] [1321] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1793 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1793) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 2 7 [2,3,7] [2521] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1873 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1873) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 5 11 [2,3,11] [1321] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_2161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 8 29 [2,3,29] [14449] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_2521 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=2521) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 1 34511 [2,34511] [953] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_5041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=5041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 10 239 [2,11,239] [10711] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_7561 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=7561) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 21 613 [2,11,613] [137] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_12601 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=12601) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 10 137 [2,11,137] [3,5,103] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_15121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=15121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 33 307 [2,17,23,307] [409] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_17641 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=17641) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 47 103 [2,3,23,47,103] [34511] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_20161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=20161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 1 103 [2,103] [137] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_22681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=22681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 7 409 [2,409] [103] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_25201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=25201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 1 103 [2,103] [409] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_27721 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=27721) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 1 613 [2,613] [103] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_30241 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=30241) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 38 239 [2,3,13,23,239] [7,11,17,19,137] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_32761 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=32761) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 53 307 [2,3,23,47,53,307] [7,11,17,19,137] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_35281 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=35281) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 17 307 [2,3,307] [409] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_37801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=37801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 46 103 [2,23,47,103] [919] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_40321 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=40321) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  mersenne_character_row (r:=17) hp base idx 57 103 [2,23,29,47,53,103] [3,5,7,409] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

private theorem seventeen_compact_coset {G : Type*} [Monoid G] {v : G} {M b o : ℕ}
    (idx : b%M=1) (per : v^o=1) :
    (v^b)^(o/o.gcd M)=v^(o/o.gcd M) := by
  have form : b = 1+M*(b/M) := by have h := Nat.mod_add_div b M; rw [idx] at h; exact h.symm
  have dm : o∣M*(o/o.gcd M) := by
    rw [←Nat.mul_div_assoc M (Nat.gcd_dvd_left o M),Nat.mul_comm M o,←Nat.lcm_eq_mul_div]
    exact Nat.dvd_lcm_left o M
  obtain ⟨s,hs⟩ := dm
  let h := o/o.gcd M
  have exp : b*h=h+o*(s*(b/M)) := by
    calc
      b*h=(1+M*(b/M))*h := congrArg (·*h) form
      _ = h+(M*h)*(b/M) := by ring
      _ = h+o*(s*(b/M)) := by rw [show M*h=o*s from hs]; ring
  change (v^b)^h = v^h
  rw [←pow_mul,exp,pow_add,pow_mul,per,one_pow,mul_one]

private theorem seventeen_compact_root_exclusion {p b q o w : ℕ}
    (pq : q.Prime) (lo : 2 < q) (base : p+1=2^b) (idx : b%42840=1)
    (mult : q∣p^17+131072) (nd : ¬q∣p+2)
    (per : 2^o%q=1) (w19 : w^17%q=1) (wn : w%q≠1)
    (reject : ∀ i ∈ List.range 16,
      let y := (q+1-(2*w^(i+1))%q)%q
      y^(o/o.gcd 42840)%q≠2^(o/o.gcd 42840)%q) : False := by
  let _ : Fact q.Prime := ⟨pq⟩
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  have mod1 (v : ℕ) : (v:ZMod q)=1 ↔ v%q=1 := by
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt pq.one_lt] using ZMod.natCast_eq_natCast_iff' v 1 q
  have two : (2:ZMod q)≠0 := by
    intro h
    have d := (ZMod.natCast_eq_zero_iff 2 q).mp h
    have := Nat.le_of_dvd (by decide : 0<2) d
    omega
  let z := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr mult
  push_cast at zero
  have z19 : z^17=1 := by dsimp [z]; rw [div_pow,div_eq_iff (pow_ne_zero _ two)]; linear_combination -zero
  have primitive : IsPrimitiveRoot (w:ZMod q) 17 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime
    (by simpa only [Nat.cast_pow] using (mod1 _).mpr w19) (fun h => wn ((mod1 _).mp h)))
  obtain ⟨i,hi,iw⟩ := primitive.eq_pow_of_pow_eq_one z19
  have wv : (w:ZMod q)^i * 2 = -(p:ZMod q) := (eq_div_iff two).mp iw
  have i0 : i≠0 := by
    rintro rfl
    rw [pow_zero,one_mul] at wv
    apply nd
    apply (ZMod.natCast_eq_zero_iff (p+2) q).mp
    push_cast
    linear_combination wv
  let y := (q+1-(2*w^i)%q)%q
  have bound : (2*w^i)%q ≤ q+1 := by have := Nat.mod_lt (2*w^i) pq.pos; omega
  have cast : (y:ZMod q)=(2:ZMod q)^b := by
    dsimp [y]
    rw [ZMod.natCast_mod,Nat.cast_sub bound,Nat.cast_add,ZMod.natCast_self,Nat.cast_one,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow]
    have bp := congrArg (fun n : ℕ => (n:ZMod q)) base
    push_cast at bp ⊢
    linear_combination bp - wv
  have cycle : (2:ZMod q)^o=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using (mod1 _).mpr per
  have projected := seventeen_compact_coset idx cycle
  rw [←cast] at projected
  have bad := reject (i-1) (List.mem_range.mpr (show i-1<16 by omega))
  rw [show i-1+1=i by omega] at bad
  apply bad
  apply (ZMod.natCast_eq_natCast_iff' _ _ q).mp
  push_cast
  exact projected

private theorem seventeen_compact_pow_eq (a e m : ℕ) : (fun (a e m : ℕ) => Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m) (fun _ f n => (f (n/2))^2 * a^(n%2) % m) (e.log2+1) e) a e m = a^e % m := by
  let f (k : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m)
    (fun _ g n => (g (n/2))^2 * a^(n%2) % m) k
  have aux (k n : ℕ) (bound : n<2^k) : f k n = a^n % m := by
    induction k generalizing n with
    | zero =>
      have h : n=0 := by simpa using bound
      subst n
      simp [f]
    | succ k ih =>
      have half : n/2 < 2^k := by rw [pow_succ] at bound; omega
      change (f k (n/2))^2 * a^(n%2) % m = a^n % m
      rw [ih _ half]
      calc
        _ = ((a^(n/2))^2 * a^(n%2))%m :=
          ((Nat.mod_modEq _ _).pow 2).mul_right _
        _ = a^n % m := by
          rw [← pow_mul,← pow_add,show n/2*2+n%2=n by omega]
  change f (e.log2+1) e = a^e % m
  apply aux (e.log2+1) e
  by_cases h : e=0
  · subst e
    decide
  · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)

private theorem seventeen_compact_legendre (m n : ℕ) [Fact m.Prime] (hm : 2 < m) :
    legendreSym m (n:ℤ) = if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1 := by
  have cast : ((n:ℤ):ZMod m)=(n:ZMod m) := by simp
  by_cases z : n%m=0
  · rw [if_pos z,legendreSym.eq_zero_iff,cast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero z
  rw [if_neg z]
  have nz : ((n:ℤ):ZMod m)≠0 := by
    intro h
    rw [cast] at h
    exact z (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff n m).mp h))
  have power : ((n%m)^(m/2))%m=1 ↔ (n:ZMod m)^(m/2)=1 := by
    have eq := ZMod.natCast_eq_natCast_iff' ((n%m)^(m/2)) 1 m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at eq
    simpa only [Nat.cast_pow,ZMod.natCast_mod,Nat.cast_one] using eq.symm
  have sign := legendreSym.eq_pow m (n:ℤ)
  rw [cast] at sign
  rcases legendreSym.eq_one_or_neg_one m nz with h|h
  · rw [h,Int.cast_one] at sign
    rw [h,if_pos (power.mpr sign.symm)]
  · rw [h,Int.cast_neg,Int.cast_one] at sign
    rw [h,if_neg]
    intro bad
    have eq : (-1:ZMod m)=1 := sign.trans (power.mp bad)
    have zero : ((2:ℕ):ZMod m)=0 := by push_cast; linear_combination -eq
    have dd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    have le := Nat.le_of_dvd (by decide) dd
    omega

set_option maxRecDepth 12000 in
private theorem seventeen_compact_interval {i start p b : ℕ} {N : ℤ} (cells : List ℕ)
    (pm : ℕ → ℕ → ℕ → ℕ) (eq : ∀ a e m, pm a e m=a^e%m)
    (checked : (cells.zipIdx start).all (fun entry =>
      let tok := entry.1
      let q := 34*entry.2+1
      if tok=0 then decide (q < 2)
      else if tok < 1024 then decide (1 < tok ∧ tok < q ∧ q%tok=0)
      else if tok=1024 then
        let a := (N%(q:ℤ)).toNat
        decide (a%q≠0 ∧ pm (a%q) (q/2) q=1)
      else
        let o := (tok-1025)/131072
        let w := (tok-1025)%131072
        decide (pm 2 o q=1 ∧ w^17%q=1 ∧ w%q≠1) &&
          (List.range 16).all (fun k =>
            let y := (q+1-(2*w^(k+1))%q)%q
            decide (pm y (o/o.gcd 42840) q≠pm 2 (o/o.gcd 42840) q)))=true)
    (low : start ≤ i) (high : i < start+cells.length)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym N (34*i+1)=1 := by
  let q := 34*i+1
  have qlo : 2 < q := by dsimp [q]; have := pq.two_le; omega
  have inside : i-start < cells.length := by omega
  let tok := cells[i-start]
  have mem : (tok,i) ∈ cells.zipIdx start := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    ⟨low, List.getElem?_eq_getElem inside⟩
  have h := List.all_eq_true.mp checked (tok,i) mem
  dsimp only at h
  by_cases z : tok=0
  · rw [if_pos z] at h
    have := of_decide_eq_true h
    omega
  rw [if_neg z] at h
  by_cases sm : tok<1024
  · rw [if_pos sm] at h
    obtain ⟨a,l,d⟩ := of_decide_eq_true h
    have := (Nat.dvd_prime pq).mp (Nat.dvd_iff_mod_eq_zero.mpr d)
    omega
  rw [if_neg sm] at h
  by_cases pos : tok=1024
  · rw [if_pos pos] at h
    obtain ⟨nz,pow1⟩ := of_decide_eq_true h
    let a := (N%(q:ℤ)).toNat
    have cast : (a:ℤ)=N%(q:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg N (by exact_mod_cast (show q≠0 by omega)))
    let _ : Fact q.Prime := ⟨pq⟩
    change jacobiSym N q=1
    rw [jacobiSym.mod_left N q,←cast,←jacobiSym.legendreSym.to_jacobiSym,seventeen_compact_legendre q a qlo,
      if_neg nz,if_pos (by simpa only [←eq] using pow1)]
  rw [if_neg pos] at h
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨period,root,nontriv⟩ := of_decide_eq_true head
  exfalso
  rw [eq] at period
  apply seventeen_compact_root_exclusion (o:=(tok-1025)/131072) (w:=(tok-1025)%131072) pq qlo base idx mult nd period root nontriv
  intro k hk
  have reject := of_decide_eq_true (List.all_eq_true.mp tail k hk)
  simpa only [eq] using reject


set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_0 {i p b : ℕ} (ix : i/128=0) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=0) (cells:=[0,5,3,6685761,8914040,3,5,15598725,3,1024,11,3,26739749,1024,3,7,5,3,80217675,1024,3,5,7,3,19,23,3,20055457,8914723,3,1024,5,3,1024,13,3,5,1024,3,1024,89130301,3,11012367,7,3,1024,5,3,23,1024,3,5,29,3,11,122553354,3,7,1024,3,13,5,3,6687509,7,3,5,43,3,102500113,1024,3,31,13,3,167119914,5,3,7,1024,3,5,1024,3,1024,7,3,11,41,3,26740717,5,3,138153842,23,3,5,1024,3,7,19,3,454559816,31,3,467929912,5,3,1024,11,3,5,13,3,508037136,1024,3,23,1024,3,7,5,3,47,1024,3,5,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<128; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_1 {i p b : ℕ} (ix : i/128=1) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=128) (cells:=[3,41,44565988,3,67,34870458,3,1024,5,3,13,29,3,5,11,3,59,129240931,3,1024,7,3,222823791,5,3,11,1024,3,5,19,3,354290873,71304879,3,7,23,3,31,5,3,29,7,3,5,1024,3,61,11,3,13,1024,3,200543423,5,3,7,1024,3,5,416679046,3,1024,7,3,13375823,50596767,3,19,5,3,1024,67,3,5,900207641,3,7,1024,3,1024,11,3,37,5,3,949225349,19,3,5,47,3,11,245109333,3,989333279,1024,3,7,5,3,1024,13,3,5,7,3,73,61,3,1024,1060638123,3,1024,5,3,541464612,543688160,3,5,37,3,1024,1024,3,11,7,3,13])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<256; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_2 {i p b : ℕ} (ix : i/128=2) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=256) (cells:=[5,3,31,1024,3,5,59,3,47,1024,3,7,13,3,1203244513,5,3,1216619480,7,3,5,1234442290,3,53,1024,3,43,1024,3,11,5,3,7,31,3,5,38280336,3,13,7,3,1024,1024,3,101,5,3,225056183,1024,3,5,11,3,7,83,3,103,29,3,140380497,5,3,11,1024,3,5,1434982194,3,23,43,3,6688151,19,3,7,5,3,13,41,3,5,7,3,755373466,11,3,29,107,3,1024,5,3,1024,1024,3,5,392171157,3,92801583,1024,3,61,7,3,1024,5,3,1024,1024,3,5,1024,3,1024,23,3,7,11,3,41,5,3,187179916,7,3,5,31,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<384; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_3 {i p b : ℕ} (ix : i/128=3) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=384) (cells:=[11,13,3,1024,79,3,89,5,3,7,1755845330,3,5,104079248,3,1024,7,3,1024,71,3,47,5,3,1024,1822691321,3,5,1024,3,7,103,3,11,61,3,311959578,5,3,19,13,3,5,1024,3,29,1916287403,3,37,1024,3,7,5,3,53,11,3,5,7,3,31,1024,3,332008962,1024,3,11,5,3,73,43,3,5,41,3,1024,1024,3,23,7,3,97,5,3,347617118,37,3,5,11,3,71,31,3,7,1024,3,19,5,3,11,7,3,5,29,3,13,436743873,3,1024,1024,3,1024,5,3,7,19,3,5,13,3,280772866,7,3,1129712158,23,3,757607994,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<512; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_4 {i p b : ℕ} (ix : i/128=4) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=512) (cells:=[3,2286172062,1024,3,5,1024,3,7,231737113,3,1024,1165373841,3,2339641833,5,3,13,1024,3,5,1185426265,3,67,1192116603,3,19,11,3,7,5,3,37,53,3,5,7,3,11,1024,3,137,1024,3,113,5,3,2486699371,83,3,5,97,3,127,1024,3,13,7,3,508036830,5,3,2553554247,29,3,5,23,3,430060784,13,3,7,43,3,2607035237,5,3,1024,7,3,5,1024,3,19,15598721,3,53,1024,3,23,5,3,7,11,3,5,1352533098,3,904664707,7,3,1024,19,3,11,5,3,2754092032,13,3,5,163057287,3,7,79,3,1024,131,3,31,5,3,2820943362,1024,3,5,11,3,474620101])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<640; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_5 {i p b : ℕ} (ix : i/128=5) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=640) (cells:=[47,3,83,1432768942,3,7,5,3,11,2892246689,3,5,7,3,37,1024,3,89,13,3,245111397,5,3,1477325326,107,3,5,1024,3,23,11,3,73,7,3,59,5,3,3021490191,1024,3,5,1024,3,13,1024,3,7,149,3,29,5,3,1024,7,3,5,13,3,1024,389954768,3,1024,11,3,1024,5,3,7,3159628503,3,5,43,3,11,7,3,1024,3199737409,3,1024,5,3,13,103,3,5,19,3,7,3253219612,3,543689308,1024,3,67,5,3,23,1646672347,3,5,3306691027,3,41,73,3,11,29,3,7,5,3,3355721274,31,3,5,7,3,131,1024,3,13,1700143273,3,19,5,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<768; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_6 {i p b : ℕ} (ix : i/128=6) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=768) (cells:=[1024,11,3,5,1024,3,1024,13,3,29,7,3,11,5,3,79,19,3,5,1024,3,139,1024,3,7,59,3,354302420,5,3,43,7,3,5,11,3,1791502740,101,3,23,83,3,240663079,5,3,7,13,3,5,1024,3,1024,7,3,19,1024,3,1024,5,3,47,71,3,5,1853890537,3,7,11,3,149,1024,3,13,5,3,1024,1024,3,5,31,3,1261195916,757602939,3,59,13,3,7,5,3,3823658025,1024,3,5,7,3,29,1024,3,41,11,3,45625164,5,3,1024,3894940331,3,5,229922239,3,11,1960848324,3,3930595611,7,3,788795747,5,3,109,167,3,5,13,3,113,1024])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<896; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_7 {i p b : ℕ} (ix : i/128=7) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=896) (cells:=[3,7,19,3,71,5,3,2012111589,7,3,5,1024,3,31,4055383989,3,11,37,3,53,5,3,7,1024,3,5,23,3,89,7,3,43,139,3,103,5,3,1385968746,11,3,5,1024,3,7,31,3,1024,1024,3,11,5,3,1056204190,41,3,5,2121294970,3,163,19,3,13,4269297944,3,7,5,3,137,73,3,5,7,3,47,13,3,1024,4336151995,3,724202169,5,3,11,1024,3,5,173,3,2192601555,107,3,37,7,3,41,5,3,19,260579971,3,5,109,3,1024,11,3,7,67,3,4478735991,5,3,132123814,7,3,5,19,3,23,77993457,3,151,1024,3,79,5,3,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1024; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_8 {i p b : ℕ} (ix : i/128=8) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1024) (cells:=[37,3,5,1024,3,59,7,3,1149785893,11,3,13,5,3,29,1024,3,5,71,3,7,931427378,3,97,13,3,19,5,3,521414526,1024,3,5,83,3,2359698738,23,3,4732760842,47,3,7,5,3,1024,19,3,5,7,3,13,1024,3,11,1024,3,1024,5,3,23,1207700594,3,5,13,3,61,1024,3,107,7,3,31,5,3,37,11,3,5,89,3,1024,4924383575,3,7,101,3,11,5,3,13,7,3,5,163,3,1024,113,3,1024,1024,3,29,5,3,7,23,3,5,11,3,5053632181,7,3,67,5071449094,3,83,5,3,11,97,3,5,59,3,7,61,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1152; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_9 {i p b : ℕ} (ix : i/128=9) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1152) (cells:=[13,197,3,173,5,3,1024,157,3,5,1024,3,19,11,3,2600342848,151,3,7,5,3,1742509994,179,3,5,7,3,1024,53,3,5267528785,19,3,43,5,3,31,1024,3,5,1328036347,3,1024,41,3,1024,7,3,1024,5,3,893537701,13,3,5,1024,3,11,5392321551,3,7,1024,3,109,5,3,1024,7,3,5,418944236,3,1024,5459166085,3,1024,43,3,13,5,3,7,1024,3,5,137,3,103,7,3,11,13,3,1024,5,3,1390446204,1024,3,5,164114653,3,7,71,3,79,329799908,3,62430215,5,3,2814268961,11,3,5,23,3,13,29,3,61,1024,3,7,5,3,19,1024])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1280; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_10 {i p b : ℕ} (ix : i/128=10) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1280) (cells:=[3,5,7,3,149,1024,3,1024,717520930,3,23,5,3,338977312,5766675647,3,5,11,3,29,289675662,3,1024,7,3,5815675899,5,3,11,1024,3,5,31,3,43,1024,3,7,41,3,37,5,3,1024,7,3,5,2956876228,3,73,11,3,1024,61,3,19,5,3,7,53,3,5,103,3,187203319,7,3,13,1024,3,197,5,3,179,19,3,5,29,3,7,13,3,6069728189,11,3,2027720120,5,3,193,89,3,5,1024,3,11,1024,3,6136566840,6140993444,3,7,5,3,59,1024,3,5,7,3,83,167,3,19,6207858281,3,3108375870,5,3,1024,13,3,5,73,3,1024,23,3,11])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1408; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_11 {i p b : ℕ} (ix : i/128=11) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1408) (cells:=[7,3,191,5,3,107,131,3,5,1024,3,3161898714,1024,3,7,3170804667,3,13,5,3,23,7,3,5,181,3,6390586812,97,3,6403924511,13,3,11,5,3,7,29,3,5,1024,3,19,7,3,808867821,127,3,61,5,3,89,113,3,5,11,3,7,1024,3,31,19,3,151,5,3,11,23,3,5,13,3,1024,824470129,3,41,3304491296,3,7,5,3,552607033,1024,3,5,7,3,79,11,3,23,31,3,1024,5,3,13,418942393,3,5,1024,3,1024,6729282279,3,101,7,3,1024,5,3,1024,1024,3,5,6782763496,3,3395848503,19,3,7,11,3,6818402524,5,3,47,7,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1536; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_12 {i p b : ℕ} (ix : i/128=12) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1536) (cells:=[5,1024,3,11,1024,3,13,23,3,131,5,3,7,1024,3,5,1024,3,6925364854,7,3,167,6943189259,3,29,5,3,19,41,3,5,1024,3,7,1024,3,11,79,3,3509503749,5,3,7032322583,37,3,5,19,3,1024,1024,3,3536201138,1024,3,7,5,3,1024,11,3,5,7,3,1024,891334142,3,1024,3571861119,3,11,5,3,1194341934,227,3,5,23,3,7192756703,43,3,2402062164,7,3,13,5,3,139,1024,3,5,11,3,97,157,3,7,13,3,23,5,3,11,7,3,5,1024,3,3663233647,1024,3,29,137,3,294160313,5,3,7,1024,3,5,53,3,13,7,3,1024,3705580983])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1664; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_13 {i p b : ℕ} (ix : i/128=13) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1664) (cells:=[3,824453941,5,3,929223750,7437821289,3,5,13,3,7,3732300797,3,19,59,3,239,5,3,1024,31,3,5,41,3,1024,37,3,1024,11,3,7,5,3,13,61,3,5,7,3,11,29,3,127,951500042,3,53,5,3,1024,101,3,5,1024,3,211,3832569001,3,7674021770,7,3,89,5,3,41,7705201675,3,5,1024,3,19,1024,3,7,1024,3,67,5,3,3883815785,7,3,5,1024,3,7794340224,13,3,71,19,3,3910584982,5,3,7,11,3,5,139,3,37,7,3,73,47,3,11,5,3,23,7905768229,3,5,31,3,7,1024,3,1024,1024,3,137,5,3,3984065846,13,3,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1792; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_14 {i p b : ℕ} (ix : i/128=14) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1792) (cells:=[11,3,181,3999717266,3,1024,113,3,7,5,3,11,83,3,5,7,3,8061725723,19,3,1009398324,1024,3,13,5,3,8101883376,23,3,5,8119693457,3,4064300161,11,3,1357025992,7,3,43,5,3,8168680599,127,3,5,481600333,3,31,73,3,7,223,3,1024,5,3,19,7,3,5,1024,3,13,59,3,103,11,3,345414558,5,3,7,4153445781,3,5,13,3,11,7,3,1390434304,43,3,37,5,3,1024,29,3,5,61,3,7,1024,3,83,23,3,179,5,3,13,71,3,5,8453937572,3,1024,1024,3,11,89,3,7,5,3,29,47,3,5,7,3,59,4267089940,3,1024,1024,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1920; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_15 {i p b : ℕ} (ix : i/128=15) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1920) (cells:=[97,5,3,151,11,3,5,1024,3,1024,211,3,13,7,3,11,5,3,131,1024,3,5,8654438623,3,157,13,3,7,107,3,1024,5,3,1024,7,3,5,11,3,43,103,3,19,31,3,71,5,3,7,1024,3,5,1098538282,3,41,7,3,1024,109,3,23,5,3,191,13,3,5,260452186,3,7,11,3,89,1024,3,29,5,3,8904009945,1024,3,5,43,3,61,8935236587,3,4472113313,67,3,7,5,3,527762754,1024,3,5,7,3,19,173,3,1024,11,3,31,5,3,53,149,3,5,59,3,11,1024,3,9077815136,7,3,139,5,3,4552273286,325358328,3,5,79])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2048; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_16 {i p b : ℕ} (ix : i/128=16) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2048) (cells:=[3,13,47,3,7,29,3,107,5,3,167,7,3,5,13,3,1024,61,3,11,1024,3,401099184,5,3,7,151,3,5,9256079940,3,1024,7,3,29,1024,3,1024,5,3,13,11,3,5,1024,3,7,19,3,37,1024,3,11,5,3,4685988815,1024,3,5,71,3,1024,1024,3,1024,1024,3,7,5,3,23,4721610941,3,5,7,3,257,75789045,3,13,4741673334,3,3164121597,5,3,11,37,3,5,113,3,1588796710,13,3,67,7,3,3186374819,5,3,199,31,3,5,19,3,1024,11,3,7,239,3,271,5,3,251,7,3,5,1024,3,29,89,3,1613308224,1024,3,4846406085])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2176; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_17 {i p b : ℕ} (ix : i/128=17) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2176) (cells:=[5,3,7,13,3,5,1024,3,1024,7,3,23,11,3,19,5,3,173,1024,3,5,9790889824,3,7,131,3,1024,1024,3,13,5,3,37,19,3,5,2464462777,3,9866591588,127,3,43,13,3,7,5,3,1024,1024,3,5,7,3,1024,9937928573,3,11,23,3,332039874,5,3,47,269,3,5,31,3,13,37,3,19,7,3,113,5,3,1024,11,3,5,13,3,89,43,3,7,1024,3,11,5,3,59,7,3,5,1024,3,1024,1024,3,10147371355,73,3,5080382614,5,3,7,79,3,5,11,3,223,7,3,1024,53,3,1024,5,3,11,5122728626,3,5,23,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2304; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_18 {i p b : ℕ} (ix : i/128=18) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2304) (cells:=[7,109,3,1024,97,3,1024,5,3,3435991995,29,3,5,1024,3,37,11,3,13,19,3,7,5,3,1024,75772614,3,5,7,3,1024,13,3,181,1488497563,3,1738091529,5,3,29,1024,3,5,199,3,1024,10472725673,3,211,7,3,5247544734,5,3,1024,1024,3,5,10526179622,3,11,191,3,7,1024,3,61,5,3,3525052407,7,3,5,1024,3,47,19,3,10615262098,1024,3,83,5,3,7,43,3,5,167,3,23,7,3,11,971565832,3,13,5,3,1024,5356670017,3,5,1024,3,7,67,3,1024,13,3,157,5,3,19,11,3,5,1024,3,73,41,3,179,31,3,7,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2432; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_19 {i p b : ℕ} (ix : i/128=19) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2432) (cells:=[3,10842605163,10847042703,3,5,7,3,13,23,3,79,5443597427,3,59,5,3,454581988,1024,3,5,11,3,10936195953,1024,3,139,7,3,1827167075,5,3,11,1024,3,5,37,3,127,137,3,7,47,3,19,5,3,13,7,3,5,1024,3,1024,11,3,1024,29,3,31,5,3,7,19,3,5,73,3,1024,7,3,97,1024,3,53,5,3,269,23,3,5,223,3,7,233,3,13,11,3,47,5,3,109,5624043167,3,5,151,3,11,13,3,19,71,3,7,5,3,1024,173,3,5,7,3,67,11341683545,3,1024,41,3,277,5,3,61,1024,3,5,1024,3,167])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2560; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_20 {i p b : ℕ} (ix : i/128=20) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2560) (cells:=[1024,3,11,7,3,1024,5,3,1024,13,3,5,157,3,1024,29,3,7,23,3,1916283649,5,3,31,7,3,5,1024,3,19,107,3,320884125,131,3,11,5,3,7,97,3,5,1024,3,29,7,3,137,13,3,11631335504,5,3,11644753233,31,3,5,11,3,7,229,3,59,101,3,149,5,3,11,1024,3,5,109,3,13,1024,3,1024,257,3,7,5,3,73,1024,3,5,7,3,1024,11,3,37,1024,3,5915983586,5,3,3948428856,1024,3,5,29,3,53,19,3,5942716391,7,3,23,5,3,13,1024,3,5,1024,3,79,746519061,3,7,11,3,11965618278,5,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2688; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_21 {i p b : ℕ} (ix : i/128=21) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2688) (cells:=[1024,7,3,5,1024,3,11,6005104598,3,107,1024,3,1203297895,5,3,7,89,3,5,31,3,1024,7,3,13,1024,3,2016604328,5,3,12112698733,193,3,5,19,3,7,13,3,11,1024,3,1024,5,3,43,1024,3,5,12197299312,3,23,59,3,4073255286,1024,3,7,5,3,233,11,3,5,7,3,4091042358,47,3,1024,79,3,11,5,3,37,13,3,5,1024,3,31,53,3,307,7,3,6183365994,5,3,29,19,3,5,11,3,103,23,3,7,3106152768,3,13,5,3,11,7,3,5,61,3,59,31,3,47,13,3,283,5,3,7,1024,3,5,67,3,241,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2816; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_22 {i p b : ℕ} (ix : i/128=22) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2816) (cells:=[3,19,1024,3,1024,5,3,53,1024,3,5,277,3,7,12611762574,3,1024,12625166238,3,41,5,3,1024,6325949309,3,5,13,3,6337108211,1024,3,6343846863,11,3,7,5,3,1412766340,23,3,5,7,3,11,1024,3,31,311,3,29,5,3,13,12785626943,3,5,1024,3,19,239,3,23,7,3,181,5,3,83,3213114380,3,5,103,3,120361567,97,3,7,19,3,257,5,3,12914883792,7,3,5,12932693951,3,6470801904,43,3,13,1024,3,163,5,3,7,11,3,5,41,3,61,7,3,4340663222,23,3,11,5,3,113,53,3,5,1024,3,7,73,3,1024,191,3,1024,5,3,47])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2944; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_23 {i p b : ℕ} (ix : i/128=23) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2944) (cells:=[199,3,5,11,3,4380709542,19,3,29,13159929502,3,7,5,3,11,13,3,5,7,3,179,1024,3,281,1024,3,1024,5,3,271,13253531993,3,5,127,3,1024,11,3,53,7,3,13,5,3,19,1024,3,5,23,3,1024,79,3,7,13,3,1114116055,5,3,6691421146,7,3,5,19,3,263,29,3,3355782968,11,3,23,5,3,7,6727096110,3,5,37,3,11,7,3,101,1024,3,71,5,3,4505564371,43,3,5,13,3,7,41,3,293,157,3,19,5,3,31,83,3,5,3400306074,3,1024,241,3,11,173,3,7,5,3,13,19,3,5,7,3,1024,13681387952,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3072; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_24 {i p b : ℕ} (ix : i/128=24) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3072) (cells:=[149,163,3,1024,5,3,229,11,3,5,1024,3,23,1024,3,1024,7,3,11,5,3,103,59,3,5,29,3,1024,3453765437,3,7,1024,3,193,5,3,1731356610,7,3,5,11,3,239,13,3,131,1024,3,43,5,3,7,1740301373,3,5,6967734555,3,191,7,3,83,37,3,33467767,5,3,13984349892,1024,3,5,317,3,7,11,3,67,1024,3,668522822,5,3,23,13,3,5,1024,3,19,880211547,3,4697197837,41,3,7,5,3,1024,1024,3,5,7,3,311,7074680995,3,109,11,3,13,5,3,1024,29,3,5,1024,3,11,14216090501,3,1024,7,3,7119242479,5,3,227,23])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3200; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_25 {i p b : ℕ} (ix : i/128=25) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3200) (cells:=[3,5,1024,3,41,1024,3,7,420543727,3,1024,5,3,29,7,3,5,1024,3,13,256299583,3,11,1024,3,47,5,3,7,101,3,5,13,3,31,7,3,1024,89,3,1024,5,3,71,11,3,5,53,3,7,1024,3,603947239,1024,3,11,5,3,13,1024,3,5,1024,3,1024,31,3,113,23,3,7,5,3,19,1024,3,5,7,3,143347736,3654304152,3,151,7315354636,3,61,5,3,11,14657351854,3,5,19,3,14679644289,1024,3,13,7,3,29,5,3,7359841892,1024,3,5,229,3,14746488812,11,3,7,1024,3,269,5,3,37,7,3,5,179,3,3703412018,423399573,3,31])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3328; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_26 {i p b : ℕ} (ix : i/128=26) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3328) (cells:=[7415559713,3,19,5,3,7,14857846397,3,5,23,3,107,7,3,199,11,3,4969012185,5,3,67,13,3,5,7469023530,3,7,37,3,157,29,3,23,5,3,1024,220548034,3,5,7502469920,3,1024,149,3,1024,73,3,7,5,3,43,131,3,5,7,3,7540377090,71,3,11,13,3,79,5,3,5040318015,167,3,5,15138611863,3,163,7575980884,3,103,7,3,15174210317,5,3,949285105,11,3,5,1024,3,13,67,3,7,251,3,11,5,3,181,7,3,5,13,3,23,139,3,2549121311,151,3,1024,5,3,7,1024,3,5,11,3,19,7,3,233,59,3,41,5,3,11,15392610458,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3456; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_27 {i p b : ℕ} (ix : i/128=27) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3456) (cells:=[5,15405942290,3,7,47,3,1024,19,3,1024,5,3,61,79,3,5,97,3,29,11,3,1024,1024,3,7,5,3,1024,1024,3,5,7,3,313,15553028519,3,13,113,3,1557566185,5,3,23,1024,3,5,918093535,3,109,13,3,43,7,3,131,5,3,31,157,3,5,197,3,11,19,3,7,1024,3,209488404,5,3,280839619,7,3,5,29,3,15749145560,263,3,241,15766919082,3,37,5,3,7,13,3,5,83,3,67,7,3,11,107,3,7921374773,5,3,19,1024,3,5,163,3,7,53,3,23,3975197009,3,13,5,3,41,11,3,5,19,3,1024,1024,3,313079226,13])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3584; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_28 {i p b : ℕ} (ix : i/128=28) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3584) (cells:=[3,7,5,3,1998793128,1024,3,5,7,3,89,1024,3,1024,71,3,1024,5,3,1024,181,3,5,11,3,13,16087843153,3,127,7,3,19,5,3,11,29,3,5,13,3,1024,59,3,7,293,3,83,5,3,101,7,3,5,31,3,1024,11,3,1024,1024,3,40127123,5,3,7,1024,3,5,227,3,283,7,3,1024,277,3,107,5,3,2720714789,1024,3,5,8171022001,3,7,3271117649,3,19,11,3,8188746704,5,3,1024,43,3,5,23,3,11,349,3,13,37,3,7,5,3,307,1024,3,5,7,3,31,13,3,191,137,3,23,5,3,139,1024,3,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3712; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_29 {i p b : ℕ} (ix : i/128=29) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3712) (cells:=[61,3,197,1655628850,3,11,7,3,1024,5,3,8295776420,53,3,5,1024,3,19,31,3,7,1024,3,29,5,3,73,7,3,5,47,3,695221092,1024,3,8349251932,19,3,11,5,3,7,1024,3,5,16742963048,3,1024,7,3,37,97,3,13,5,3,8396070146,16796444127,3,5,11,3,7,1024,3,53,13,3,842285233,5,3,11,1024,3,5,331,3,47,1024,3,31,29,3,7,5,3,263,37,3,5,7,3,13,11,3,8482863651,43,3,281,5,3,16992460848,103,3,5,13,3,41,23,3,29,7,3,5682088558,5,3,157,211,3,5,113,3,61,101,3,7,11,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3840; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_30 {i p b : ℕ} (ix : i/128=30) (lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3840) (cells:=[137,5,3,13,7,3,5,139,3,11,223,3,1024,269,3,2229761])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3856; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12288 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_catalog {i p b : ℕ} (lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  have range : i/128<31 := by omega
  interval_cases h : i/128
  · exact seventeen_compact_chunk_0 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_1 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_2 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_3 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_4 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_5 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_6 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_7 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_8 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_9 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_10 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_11 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_12 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_13 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_14 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_15 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_16 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_17 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_18 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_19 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_20 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_21 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_22 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_23 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_24 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_25 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_26 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_27 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_28 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_29 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_30 h lim pq base idx mult nd

private theorem seventeen_compact_last_fifth {b q : ℕ} (pb : b.Prime) (ob : Odd b) (pq : q.Prime)
    (dq : q ∣ 2^b+1) (small : q < b) : q=3 := by
  -- The order of -2 divides both the prime b and q-1. It must be one.
  let _ : Fact q.Prime := ⟨pq⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^b+1) q).mpr dq
  push_cast at zero
  have eq : (-2 : ZMod q)^b=1 := by rw [ob.neg_pow]; linear_combination -zero
  have ne : (-2 : ZMod q) ≠ 0 := by
    intro h
    rw [h,zero_pow pb.ne_zero] at eq
    exact zero_ne_one eq
  have cases := (Nat.dvd_prime pb).mp (orderOf_dvd_of_pow_eq_one eq)
  have one : orderOf (-2 : ZMod q)=1 := cases.resolve_right (by
    intro same
    have dd := ZMod.orderOf_dvd_card_sub_one ne
    rw [same] at dd
    have := Nat.le_of_dvd (show 0 < q-1 by have := pq.two_le; omega) dd
    omega)
  have nz := orderOf_eq_one_iff.mp one
  have z : ((3 : ℕ) : ZMod q)=0 := by push_cast; linear_combination -nz
  exact (Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff _ _).mp z)

private theorem seventeen_compact_last_left {b L : ℕ} (pb : b.Prime) (lb : L < b) (hb : 3 < b) :
    ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1 := by
  have ob := pb.odd_of_ne_two (by omega)
  have no9 : ¬9 ∣ 2^b+1 := by
    have b3 : ¬3 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pb).mp h
      omega
    obtain ⟨w,hw⟩ := ob
    have rem : b%6=1 ∨ b%6=5 := by omega
    have pow : Nat.ModEq 9 (2^b) (2^(b%6)) := by
      have h : Nat.ModEq 9 (2^6) 1 := by decide
      calc
        2^b = 2^(b%6)*(2^6)^(b/6) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%6)*1^(b/6) [MOD 9] := (h.pow _).mul_left _
        _ = _ := by simp
    change 2^b%9=2^(b%6)%9 at pow
    rcases rem with h|h <;> rw [h] at pow <;> norm_num at pow <;> omega
  by_contra! none
  have big := Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ b by omega)
  norm_num at big
  have eq : 2^b+1=3^(2^b+1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have upper : q ≤ L := by by_contra! high; exact none q pq high dq
      exact seventeen_compact_last_fifth pb ob pq dq (by omega))
  generalize (2^b+1).primeFactorsList.length = e at eq
  have e2 : 2 ≤ e := by
    by_contra! bad
    interval_cases e <;> norm_num at eq
    all_goals omega
  exact no9 (eq ▸ (pow_dvd_pow (3 : ℕ) e2))


-- Reused when integrating into the reduction.
private theorem seventeen_compact_last_cycle {b m o : ℕ} (hm : Nat.ModEq m (2^o) 1) :
    Nat.ModEq m (2^b) (2^(b%o)) := by
  calc
    2^b = 2^(b%o)*(2^o)^(b/o) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ 2^(b%o)*1^(b/o) [MOD m] := (hm.pow _).mul_left _
    _ = _ := by simp


private theorem seventeen_compact_last_order {q p : ℕ} (pq : q.Prime) (q2 : q≠2)
    (d : q ∣ p^17+131072) (nd : ¬q ∣ p+2) : 17 ∣ q-1 := by
  let _ : Fact q.Prime := ⟨pq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    exact q2 eq
  let t : ZMod q := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr d
  push_cast at zero
  have eq : t^17=1 := by
    dsimp [t]
    rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]
    linear_combination -zero
  have t1 : t≠1 := by
    intro h
    dsimp [t] at h
    rw [div_eq_iff h2] at h
    apply nd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    linear_combination -h
  have t0 : t≠0 := by rintro h; rw [h] at eq; simp at eq
  have ord : orderOf t = 17 := ((Nat.dvd_prime (by decide : Nat.Prime 17)).mp
    (orderOf_dvd_of_pow_eq_one eq)).resolve_left (fun h => t1 (orderOf_eq_one_iff.mp h))
  exact ord ▸ ZMod.orderOf_dvd_card_sub_one t0


private theorem seventeen_compact_scaled {p F m k : ℕ} (fac : p^17+131072=(p+2)*F)
    (h : Nat.ModEq m p k) : Nat.ModEq m ((k+2)*F) (k^17+131072) := by
  calc
    (k+2)*F ≡ (p+2)*F [MOD m] := ((h.add_right 2).mul_right F).symm
    _ = p^17+131072 := fac.symm
    _ ≡ k^17+131072 [MOD m] := (h.pow 17).add_right _



private theorem seventeen_compact_common_prime {p F q : ℕ} (fac : p^17+131072=(p+2)*F) (fpos : F≠0)
    (qp : q.Prime) (qlo : 2 < q) (left : q∣p+2) (right : q∣F) : q=17 := by
  let _ : Fact q.Prime := ⟨qp⟩
  have qnp : ¬q∣p := by intro dp; have := Nat.le_of_dvd (by decide : 0<2) ((Nat.dvd_add_iff_right dp).mpr left); omega
  have val := padicValNat.pow_add_pow (x:=p) (y:=2) (qp.odd_of_ne_two (by omega)) left qnp (by decide : Odd 17)
  change padicValNat q (p^17+131072)=_ at val
  rw [fac,padicValNat.mul (by omega) fpos] at val
  have nz := (dvd_iff_padicValNat_ne_zero fpos).mp right
  have l : q∣17 := (dvd_iff_padicValNat_ne_zero (by decide : (17:ℕ)≠0)).mpr (by omega)
  exact (Nat.prime_dvd_prime_iff_eq qp (by decide)).mp l

private theorem seventeen_compact_cofactor_negative {p b F D : ℕ}
    (base : p+1=2^b) (hb : 131073 < b) (idx : b%42840=1) (fac : p^17+131072=(p+2)*F)
    (per : Nat.ModEq (3*D) (2^42840) 1) (cop : Nat.Coprime 8 D) (big : 43691 < D)
    (a8 : Nat.ModEq 8 7 (4*D+43691)) (ad : Nat.ModEq D 43691 (4*D+43691))
    (jac : jacobiSym (-(2*(D:ℤ))) (4*D+43691) = -1) :
    jacobiSym (-(2*(D:ℤ))) F = -1 := by
  have div8 : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have f8 : Nat.ModEq 8 F 7 := by
    calc
      F = 1*F := (one_mul _).symm
      _ ≡ (7+2)*F [MOD 8] := (show Nat.ModEq 8 1 (7+2) by decide).mul_right _
      _ ≡ 7^17+131072 [MOD 8] := seventeen_compact_scaled fac p8
      _ ≡ 7 [MOD 8] := by decide
  have fv : F%8=7 := f8
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have pred : Nat.ModEq (3*D) p 1 := by
    have z := seventeen_compact_last_cycle (b:=b) per
    rw [idx,pow_one,←base] at z
    exact Nat.ModEq.add_right_cancel' 1 z
  have fd : Nat.ModEq D F 43691 := Nat.ModEq.mul_left_cancel' (by decide : (3:ℕ)≠0) (seventeen_compact_scaled fac pred)
  have total : Nat.ModEq (8*D) F (4*D+43691) := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨f8.trans a8,fd.trans ad⟩
  rw [jacobiSym.mod_right _ fo]
  have abs : 4*(-(2*(D:ℤ))).natAbs=8*D := by simp; omega
  rw [abs]
  have rem : F%(8*D)=4*D+43691 := Eq.trans total (Nat.mod_eq_of_lt (by omega))
  rwa [rem]


private theorem seventeen_compact_last_abstract {p b F : ℕ} {A : ℤ}
    (pp : p.Prime) (base : p+1=2^b) (hb : 131073 < b) (idx : b%42840=1)
    (fac : p^17+131072=(p+2)*F) (minus : jacobiSym A F = -1)
    (catalog : ∀ {i : ℕ}, i<3856 → (34*i+1).Prime → 34*i+1∣p^17+131072 → ¬34*i+1∣p+2 →
      jacobiSym A (34*i+1)=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^17+d ∧ s∣p^17+d := by
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have eight : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have z := seventeen_compact_scaled fac p8
  change (9*F)%8=7 at z
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have fpos : F≠0 := by omega
  obtain ⟨s,ps,ds,minusS⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one minus
  have slo : 2 < s := lt_of_le_of_ne ps.two_le (Ne.symm (fo.ne_two_of_dvd_nat ds))
  obtain ⟨q,pq,qhi,qleft⟩ := seventeen_compact_last_left pb hb (show 3 < b by omega)
  have dx : q∣p+2 := by convert qleft using 1; omega
  have mult : s∣p^17+131072 := fac ▸ dvd_mul_of_dvd_right ds _
  have nd : ¬s∣p+2 := by
    intro h
    have es := seventeen_compact_common_prime fac fpos ps slo h ds
    have dL : s∣2^b+1 := by convert h using 1; omega
    have eq3 := seventeen_compact_last_fifth pb (pb.odd_of_ne_two (by omega)) ps dL (by omega)
    omega
  by_cases large : 131073 < s
  · have ne : q≠s := by rintro rfl; have := seventeen_compact_common_prime fac fpos pq (by omega) dx ds; omega
    exact ⟨131072,q,s,pq,ps,ne,qhi,large,fac ▸ dvd_mul_of_dvd_left dx _,mult⟩
  exfalso
  obtain ⟨j,hj⟩ := seventeen_compact_last_order ps (by omega) mult nd
  obtain ⟨u,hu⟩ := ps.odd_of_ne_two (by omega)
  let i := (s-1)/34
  have es : 34*i+1=s := by dsimp [i]; omega
  have bd : i<3856 := by dsimp [i]; omega
  have posS : jacobiSym A s=1 := by
    rw [←es]
    exact catalog bd (es ▸ ps) (es ▸ mult) (es ▸ nd)
  omega

set_option maxRecDepth 32768 in
private theorem seventeen_compact_discriminant_period : Nat.ModEq (3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055) (2^42840) 1 := by
  change 2^42840%(3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055)=1%(3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055)
  rw [←seventeen_compact_pow_eq]
  decide +kernel

set_option maxRecDepth 32768 in
private theorem seventeen_compact_discriminant_value : jacobiSym (-(2*(165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055:ℤ))) (4*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055+43691) = -1 := by norm_num1


set_option maxRecDepth 32768 in
/-- The projected seventeenth roots exclude the final Mersenne-index congruence class. -/
theorem seventeen_last_compact_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 131073 < b) (idx : b%42840=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      q∣p^17+d ∧ s∣p^17+d := by
  obtain ⟨F,fac⟩ : p+2∣p^17+131072 := (by decide : Odd 17).nat_add_dvd_pow_add_pow p 2
  have bad := seventeen_compact_cofactor_negative base hb idx fac seventeen_compact_discriminant_period
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) seventeen_compact_discriminant_value
  apply seventeen_compact_last_abstract pp base hb idx fac bad
  intro i lim ps mult nd
  exact seventeen_compact_catalog lim ps base idx mult nd


/-- Every seventeenth power with Mersenne index greater than 131073 has a two-prime witness. -/
theorem mersenne_seventeen_large_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 131073 < b)
    (coarseRule : (¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d) →
      b%2520 ∈ ([1,361,673,841,1201,1321,1513,1681,1793,1873,2161] : List ℕ)) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
    q ∣ p^17+d ∧ s ∣ p^17+d := by
  by_contra missing
  have rems := coarseRule missing
  have reduced0 : b%2520=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rems
    rcases rems with h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (case17_2520_361 pp.pos base h)).elim
    · exact (missing (case17_2520_673 pp.pos base h)).elim
    · exact (missing (case17_2520_841 pp.pos base h)).elim
    · exact (missing (case17_2520_1201 pp.pos base h)).elim
    · exact (missing (case17_2520_1321 pp.pos base h)).elim
    · exact (missing (case17_2520_1513 pp.pos base h)).elim
    · exact (missing (case17_2520_1681 pp.pos base h)).elim
    · exact (missing (case17_2520_1793 pp.pos base h)).elim
    · exact (missing (case17_2520_1873 pp.pos base h)).elim
    · exact (missing (case17_2520_2161 pp.pos base h)).elim
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have form : b%42840=1+2520*((b/2520)%17) := by omega
  have indiv : b%17≠0 := by
    intro z
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 17) pb).mp (Nat.dvd_of_mod_eq_zero z)
    omega
  have rems2 : b%42840 ∈ [1,2521,5041,7561,12601,15121,17641,20161,22681,25201,27721,30241,32761,35281,37801,40321] := by
    have tab : ∀ t ∈ List.range 17, (1+2520*t)%17≠0 → 1+2520*t ∈ [1,2521,5041,7561,12601,15121,17641,20161,22681,25201,27721,30241,32761,35281,37801,40321] := by decide +kernel
    have z : b%42840%17≠0 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 17∣42840)]
    rw [form] at z ⊢
    exact tab _ (List.mem_range.mpr (Nat.mod_lt _ (by decide))) z
  have reduced1 : b%42840=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rems2
    rcases rems2 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (case17_42840_2521 pp.pos base h)).elim
    · exact (missing (case17_42840_5041 pp.pos base h)).elim
    · exact (missing (case17_42840_7561 pp.pos base h)).elim
    · exact (missing (case17_42840_12601 pp.pos base h)).elim
    · exact (missing (case17_42840_15121 pp.pos base h)).elim
    · exact (missing (case17_42840_17641 pp.pos base h)).elim
    · exact (missing (case17_42840_20161 pp.pos base h)).elim
    · exact (missing (case17_42840_22681 pp.pos base h)).elim
    · exact (missing (case17_42840_25201 pp.pos base h)).elim
    · exact (missing (case17_42840_27721 pp.pos base h)).elim
    · exact (missing (case17_42840_30241 pp.pos base h)).elim
    · exact (missing (case17_42840_32761 pp.pos base h)).elim
    · exact (missing (case17_42840_35281 pp.pos base h)).elim
    · exact (missing (case17_42840_37801 pp.pos base h)).elim
    · exact (missing (case17_42840_40321 pp.pos base h)).elim
  exact missing (seventeen_last_compact_witness pp base hb reduced1)

theorem mersenne_seventeenth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b≤131073
  · exact ep ▸ seventeen_bounded_witness pb small
  · have hi : 131073 < b := by omega
    exact mersenne_seventeen_large_witness pp base hi (seventeen_coarse pb pp base hi)

/-- No solution immediately precedes a nontrivial seventeenth power. -/
theorem seventeenth_power_exclusion {n x : ℕ} (hx : 1 < x)
    (eq : n+1=x^17) : v_l 1 n ≠ 1 := by
  intro sol
  have bound : 32 ≤ x^17 := by
    have a := Nat.pow_le_pow_left (show 2 ≤ x by omega) 17
    norm_num at a
    omega
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^17 := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx (by decide : Odd 17) (by decide) eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : (17:ℕ)≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := mersenne_seventeenth_witness pp base
  have rearr : n+(d+1)=p^17+d := by omega
  exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (rearr ▸ dq) (rearr ▸ ds) sol


private theorem nineteen_offset_mod {p b m u q d : ℕ} (base : p+1=2^b)
    (rem : b%m=u) (period : 2^m%q=1) (large : 1 < q)
    (hit : (((2^u-1)%q)^19+d)%q=0) : q ∣ p^19+d := by
  have period' : Nat.ModEq q (2^m) 1 := by change 2^m%q=1%q; rwa [Nat.mod_eq_of_lt large]
  have cyc := seventeen_smooth_cycle period' b
  rw [rem,←base] at cyc
  have right : 2^u-1+1=2^u := by have := @Nat.one_le_two_pow u; omega
  have lhs : Nat.ModEq q p (2^u-1) := Nat.ModEq.add_right_cancel' 1 (right ▸ cyc)
  have canonical := lhs.trans (Nat.mod_modEq _ q).symm
  have finish := (canonical.pow 19).add_right d
  exact Nat.modEq_zero_iff_dvd.mp (finish.trans hit)

private theorem nineteen_small_offset_prime {v : ℕ} (h : v ∈ [7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,181,241,281,421,433,1429,38737]) : v.Prime := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
/-- Finite congruence witnesses for the nineteenth power of a Mersenne prime. -/
theorem nineteen_coarse_from_eight {p b : ℕ} (pb : b.Prime) (_pp : p.Prime)
    (base : p+1=2^b) (hb : 8 < b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^19+d ∧ s ∣ p^19+d) :
    b%2520 ∈ ([1,37,121,181,221,241,311,361,401,421,491,541,661,697,781,841,961,1021,1031,1081,1117,1121,1201,1247,1261,1297,1381,1441,1481,1501,1571,1621,1661,1681,1751,1801,1921,2041,2101,2221,2281,2327,2341,2377,2381,2461] : List ℕ) := by
  let rows : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [(10,3,3,11,0),(10,9,2,11,31),(12,7,3,13,0),(9,2,3,73,0),(28,5,3,29,0),(21,20,4,7,127),(72,35,10,19,241),(180,97,19,31,37),(72,53,10,17,19),(72,17,37,73,433),(180,77,34,41,73),(120,107,10,41,241),(180,107,10,19,41),(360,71,15,17,181),(360,157,59,61,38737),(70,27,39,43,71),(420,337,59,61,71),(84,17,5,13,29),(252,97,54,73,113),(504,95,17,29,433),(1260,577,36,43,181),(1260,131,76,109,281),(140,47,9,11,29),(504,347,95,433,1429),(840,611,14,17,421),(1260,157,14,37,71),(1260,527,24,29,181),(1260,877,12,43,181)]
  let rems : List ℕ := [1,37,121,181,221,241,311,361,401,421,491,541,661,697,781,841,961,1021,1031,1081,1117,1121,1201,1247,1261,1297,1381,1441,1481,1501,1571,1621,1661,1681,1751,1801,1921,2041,2101,2221,2281,2327,2341,2377,2381,2461]
  change b%2520 ∈ rems
  have tests : (List.range 40).all (fun row => (List.range 63).all (fun col =>
      let i := 63*row+col
      decide (i%2=0 ∨ i%3=0 ∨ i%5=0 ∨ i%7=0 ∨ i ∈ rems) ||
      rows.any (fun z => i%z.1 == z.2.1))) = true := by decide +kernel
  have test (i : Fin 2520) (h2 : i.val%2≠0) (h3 : i.val%3≠0) (h5 : i.val%5≠0)
      (h7 : i.val%7≠0) (hm : i.val ∉ rems) : ∃ z ∈ rows, i.val%z.1=z.2.1 := by
    have testRow := List.all_eq_true.mp tests (i.val/63) (List.mem_range.mpr (by have := i.isLt; omega))
    have obs := List.all_eq_true.mp testRow (i.val%63) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
    dsimp only at obs
    rw [show 63*(i.val/63)+i.val%63=i.val by omega] at obs
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,beq_iff_eq] at obs
    exact obs.resolve_left (fun t => t.elim h2 (fun t => t.elim h3 (fun t => t.elim h5 (fun t => t.elim h7 hm))))
  have data : ∀ z ∈ rows,
      z.1 ∣ 2520 ∧ z.2.2.2.1 ∈ [7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,181,241,281,421,433,1429,38737] ∧ z.2.2.1+1 < z.2.2.2.1 ∧ 2^z.1%z.2.2.2.1=1 ∧ (((2^z.2.1-1)%z.2.2.2.1)^19+z.2.2.1)%z.2.2.2.1=0 ∧
      ((z.2.2.2.2=0 ∧ z.2.2.1=3 ∧ z.2.2.2.1 ≤ 73) ∨ (z.2.2.2.2 ∈ [7,11,13,17,19,29,31,37,41,43,61,71,73,109,113,127,181,241,281,421,433,1429,38737] ∧ z.2.2.1+1 < z.2.2.2.2 ∧ z.2.2.2.1≠z.2.2.2.2 ∧ 2^z.1%z.2.2.2.2=1 ∧ (((2^z.2.1-1)%z.2.2.2.2)^19+z.2.2.1)%z.2.2.2.2=0)) := by
    decide +kernel
  by_contra bad
  have ndiv (z : ℕ) (pz : z.Prime) (hz : z≤7) : b%z≠0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pz pb).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have n2 := ndiv 2 (by decide) (by decide)
  have n3 := ndiv 3 (by decide) (by decide)
  have n5 := ndiv 5 (by decide) (by decide)
  have n7 := ndiv 7 (by decide) (by decide)
  obtain ⟨⟨t,u,d,q,s⟩,mem,rule⟩ := test ⟨b%2520,Nat.mod_lt _ (by decide)⟩
    (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) bad
  obtain ⟨dt,qmem,qb,qo,qHit,rest⟩ := data _ mem
  have pq := nineteen_small_offset_prime qmem
  change b%2520%t=u at rule
  rw [Nat.mod_mod_of_dvd _ dt] at rule
  have dq := nineteen_offset_mod base rule qo pq.one_lt qHit
  rcases rest with ⟨_,rfl,small⟩|⟨smem,sb,ne,so,sHit⟩
  · change q ≤ 73 at small
    change 3+1 < q at qb
    have congr : 2^(b-1) ∣ q-1 := mersenne_four_prime_congruence base (pb.odd_of_ne_two (by omega)) (by omega)
      (by decide : Odd 19) pq qb dq missing
    have low := Nat.le_of_dvd (show 0 < q-1 by omega) congr
    have lb := Nat.pow_le_pow_right (by decide : 0<2) (show 8 ≤ b-1 by omega)
    norm_num at lb
    omega
  · have ps := nineteen_small_offset_prime smem
    exact missing ⟨d,q,s,pq,ps,ne,qb,sb,dq,nineteen_offset_mod base rule so ps.one_lt sHit⟩


set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_37 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=37) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 9 11 [2,5,11] [151] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 12 43 [2,13,43] [337] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_181 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=181) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 127 [2,5,127] [14449] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_221 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=221) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_241 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=241) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_311 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=311) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_361 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=361) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 8 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_401 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=401) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_421 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=421) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [3,5,17] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_491 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=491) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [1009] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_541 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=541) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 10 17 [2,11,17] [433] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_661 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=661) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_697 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=697) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 211 [2,3,211] [1321] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_781 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=781) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [3361] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_841 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=841) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 13 433 [2,7,433] [3,37] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_961 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=961) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [14449] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1021 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1021) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 127 [2,5,127] [631] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1031 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1031) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1081 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1081) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1117 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1117) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 211 [2,3,211] [1321] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [1009] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 8 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1247 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1247) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1261 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1261) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 10 17 [2,11,17] [433] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1297 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1297) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 9 11 [2,5,11] [151] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1381 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1381) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 10 17 [2,11,17] [21169] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1441 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1441) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 127 [2,5,127] [14449] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1481 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1481) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1501 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1501) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1571 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1571) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1621 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1621) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 8 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1661 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1661) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [3,5,11,37] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1751 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1751) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [2521] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 12 43 [2,13,43] [337] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_1921 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1921) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [14449] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2101 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2101) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 10 17 [2,11,17] [21169] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2221 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2221) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 19 [2,7,19] [3361] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2281 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2281) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 127 [2,5,127] [631] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2327 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2327) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 5 [2,3,5] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2341 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2341) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2377 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2377) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 211 [2,3,211] [1321] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2381 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2381) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 7 [2,5,7] [3361] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_2520_2461 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2461) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 8 29 [2,3,29] [71] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_2521 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=2521) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 1 229 [2,229] [457] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_5041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=5041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 49 191 [2,5,23,47,191] [2281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_7561 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=7561) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 89 229 [2,3,5,23,47,53,59,67,79,83,89,229] [7,11,13,41,191] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_10081 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=10081) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 39 191 [2,5,23,191] [2281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_12601 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=12601) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 7 191 [2,191] [3,229] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_15121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=15121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 58 1217 [2,23,47,53,59,1217] [7,11,17,229] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_17641 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=17641) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 67 761 [2,17,23,47,53,59,67,761] [13,19,191] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_20161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=20161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 69 571 [2,5,7,23,47,53,59,67,571] [3,11,13,17,19,29,31,37,191] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_22681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=22681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 12 2129 [2,13,2129] [3,5,457] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_25201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=25201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 14 1597 [2,3,5,1597] [191] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_30241 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=30241) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 1 1597 [2,1597] [2281] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_32761 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=32761) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 1 1597 [2,1597] [5,229] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_35281 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=35281) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 7 191 [2,191] [6841] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_37801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=37801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 15 2129 [2,2129] [13681] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_40321 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=40321) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 87 761 [2,11,23,47,53,59,67,79,83,761] [13,17,41,43,457] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_42841 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=42841) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 1 191 [2,191] [457] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_47880_45361 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%47880=45361) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 18 229 [2,19,229] [2129] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_47881 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=47881) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 16 23 [2,17,23] [6271] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_95761 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=95761) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 17 11287 [2,3,11287] [7,17,23] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_143641 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=143641) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 9 67 [2,5,67] [9241] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_239401 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=239401) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 20 23 [2,3,7,23] [30097] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_287281 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=287281) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 89 [2,7,89] [11287] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_335161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=335161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 17 23 [2,3,23] [7,11,67] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_383041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=383041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 6 397 [2,7,397] [18481] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_430921 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=430921) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 12 67 [2,13,67] [991] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_526680_478801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%526680=478801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 4 23 [2,5,23] [3191] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_526681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=526681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 1 1483 [2,1483] [3433] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_1053361 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=1053361) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 2 53 [2,3,53] [937] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_1580041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=1580041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 15 157 [2,157] [3121] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_2106721 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=2106721) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 5 131 [2,3,131] [1873] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_2633401 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=2633401) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 10 79 [2,11,79] [313] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_3160081 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=3160081) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 17 157 [2,3,157] [911] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_4213441 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=4213441) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 14 53 [2,3,5,53] [3121] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_4740121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=4740121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 18 1249 [2,19,1249] [911] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_5266801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=5266801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 12 4733 [2,13,4733] [79] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_5793481 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=5793481) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 9 157 [2,5,157] [911] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem smooth_6846840_6320161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%6846840=6320161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d :=
  mersenne_character_row (r:=19) hp base idx 3 79 [2,79] [313] _ seventeen_smooth_powMod_eq mersenne_character_primes (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem nineteen_last_class {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) (hb : 19 < b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d) : b%6846840=1 := by
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have mem0 := nineteen_coarse_from_eight pb pp base (by omega) missing
  have stage0 : b%2520=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem0
    rcases mem0 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (smooth_2520_37 pp.pos base h)).elim
    · exact (missing (smooth_2520_121 pp.pos base h)).elim
    · exact (missing (smooth_2520_181 pp.pos base h)).elim
    · exact (missing (smooth_2520_221 pp.pos base h)).elim
    · exact (missing (smooth_2520_241 pp.pos base h)).elim
    · exact (missing (smooth_2520_311 pp.pos base h)).elim
    · exact (missing (smooth_2520_361 pp.pos base h)).elim
    · exact (missing (smooth_2520_401 pp.pos base h)).elim
    · exact (missing (smooth_2520_421 pp.pos base h)).elim
    · exact (missing (smooth_2520_491 pp.pos base h)).elim
    · exact (missing (smooth_2520_541 pp.pos base h)).elim
    · exact (missing (smooth_2520_661 pp.pos base h)).elim
    · exact (missing (smooth_2520_697 pp.pos base h)).elim
    · exact (missing (smooth_2520_781 pp.pos base h)).elim
    · exact (missing (smooth_2520_841 pp.pos base h)).elim
    · exact (missing (smooth_2520_961 pp.pos base h)).elim
    · exact (missing (smooth_2520_1021 pp.pos base h)).elim
    · exact (missing (smooth_2520_1031 pp.pos base h)).elim
    · exact (missing (smooth_2520_1081 pp.pos base h)).elim
    · exact (missing (smooth_2520_1117 pp.pos base h)).elim
    · exact (missing (smooth_2520_1121 pp.pos base h)).elim
    · exact (missing (smooth_2520_1201 pp.pos base h)).elim
    · exact (missing (smooth_2520_1247 pp.pos base h)).elim
    · exact (missing (smooth_2520_1261 pp.pos base h)).elim
    · exact (missing (smooth_2520_1297 pp.pos base h)).elim
    · exact (missing (smooth_2520_1381 pp.pos base h)).elim
    · exact (missing (smooth_2520_1441 pp.pos base h)).elim
    · exact (missing (smooth_2520_1481 pp.pos base h)).elim
    · exact (missing (smooth_2520_1501 pp.pos base h)).elim
    · exact (missing (smooth_2520_1571 pp.pos base h)).elim
    · exact (missing (smooth_2520_1621 pp.pos base h)).elim
    · exact (missing (smooth_2520_1661 pp.pos base h)).elim
    · exact (missing (smooth_2520_1681 pp.pos base h)).elim
    · exact (missing (smooth_2520_1751 pp.pos base h)).elim
    · exact (missing (smooth_2520_1801 pp.pos base h)).elim
    · exact (missing (smooth_2520_1921 pp.pos base h)).elim
    · exact (missing (smooth_2520_2041 pp.pos base h)).elim
    · exact (missing (smooth_2520_2101 pp.pos base h)).elim
    · exact (missing (smooth_2520_2221 pp.pos base h)).elim
    · exact (missing (smooth_2520_2281 pp.pos base h)).elim
    · exact (missing (smooth_2520_2327 pp.pos base h)).elim
    · exact (missing (smooth_2520_2341 pp.pos base h)).elim
    · exact (missing (smooth_2520_2377 pp.pos base h)).elim
    · exact (missing (smooth_2520_2381 pp.pos base h)).elim
    · exact (missing (smooth_2520_2461 pp.pos base h)).elim
  have form1 : b%47880=1+2520*((b/2520)%19) := by omega
  have nz1 : b%19≠0 := by
    intro z
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 19) pb).mp (Nat.dvd_of_mod_eq_zero z)
    omega
  have mem1 : b%47880 ∈ [1,2521,5041,7561,10081,12601,15121,17641,20161,22681,25201,30241,32761,35281,37801,40321,42841,45361] := by
    have tab : ∀ t ∈ List.range 19, (1+2520*t)%19≠0 → 1+2520*t ∈ [1,2521,5041,7561,10081,12601,15121,17641,20161,22681,25201,30241,32761,35281,37801,40321,42841,45361] := by decide +kernel
    have z : b%47880%19≠0 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 19∣47880)]
    rw [form1] at z ⊢
    exact tab _ (List.mem_range.mpr (Nat.mod_lt _ (by decide))) z
  have stage1 : b%47880=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem1
    rcases mem1 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (smooth_47880_2521 pp.pos base h)).elim
    · exact (missing (smooth_47880_5041 pp.pos base h)).elim
    · exact (missing (smooth_47880_7561 pp.pos base h)).elim
    · exact (missing (smooth_47880_10081 pp.pos base h)).elim
    · exact (missing (smooth_47880_12601 pp.pos base h)).elim
    · exact (missing (smooth_47880_15121 pp.pos base h)).elim
    · exact (missing (smooth_47880_17641 pp.pos base h)).elim
    · exact (missing (smooth_47880_20161 pp.pos base h)).elim
    · exact (missing (smooth_47880_22681 pp.pos base h)).elim
    · exact (missing (smooth_47880_25201 pp.pos base h)).elim
    · exact (missing (smooth_47880_30241 pp.pos base h)).elim
    · exact (missing (smooth_47880_32761 pp.pos base h)).elim
    · exact (missing (smooth_47880_35281 pp.pos base h)).elim
    · exact (missing (smooth_47880_37801 pp.pos base h)).elim
    · exact (missing (smooth_47880_40321 pp.pos base h)).elim
    · exact (missing (smooth_47880_42841 pp.pos base h)).elim
    · exact (missing (smooth_47880_45361 pp.pos base h)).elim
  have form2 : b%526680=1+47880*((b/47880)%11) := by omega
  have nz2 : b%11≠0 := by
    intro z
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 11) pb).mp (Nat.dvd_of_mod_eq_zero z)
    omega
  have mem2 : b%526680 ∈ [1,47881,95761,143641,239401,287281,335161,383041,430921,478801] := by
    have tab : ∀ t ∈ List.range 11, (1+47880*t)%11≠0 → 1+47880*t ∈ [1,47881,95761,143641,239401,287281,335161,383041,430921,478801] := by decide +kernel
    have z : b%526680%11≠0 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 11∣526680)]
    rw [form2] at z ⊢
    exact tab _ (List.mem_range.mpr (Nat.mod_lt _ (by decide))) z
  have stage2 : b%526680=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem2
    rcases mem2 with h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (smooth_526680_47881 pp.pos base h)).elim
    · exact (missing (smooth_526680_95761 pp.pos base h)).elim
    · exact (missing (smooth_526680_143641 pp.pos base h)).elim
    · exact (missing (smooth_526680_239401 pp.pos base h)).elim
    · exact (missing (smooth_526680_287281 pp.pos base h)).elim
    · exact (missing (smooth_526680_335161 pp.pos base h)).elim
    · exact (missing (smooth_526680_383041 pp.pos base h)).elim
    · exact (missing (smooth_526680_430921 pp.pos base h)).elim
    · exact (missing (smooth_526680_478801 pp.pos base h)).elim
  have form3 : b%6846840=1+526680*((b/526680)%13) := by omega
  have nz3 : b%13≠0 := by
    intro z
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 13) pb).mp (Nat.dvd_of_mod_eq_zero z)
    omega
  have mem3 : b%6846840 ∈ [1,526681,1053361,1580041,2106721,2633401,3160081,4213441,4740121,5266801,5793481,6320161] := by
    have tab : ∀ t ∈ List.range 13, (1+526680*t)%13≠0 → 1+526680*t ∈ [1,526681,1053361,1580041,2106721,2633401,3160081,4213441,4740121,5266801,5793481,6320161] := by decide +kernel
    have z : b%6846840%13≠0 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 13∣6846840)]
    rw [form3] at z ⊢
    exact tab _ (List.mem_range.mpr (Nat.mod_lt _ (by decide))) z
  have stage3 : b%6846840=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem3
    rcases mem3 with h|h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (smooth_6846840_526681 pp.pos base h)).elim
    · exact (missing (smooth_6846840_1053361 pp.pos base h)).elim
    · exact (missing (smooth_6846840_1580041 pp.pos base h)).elim
    · exact (missing (smooth_6846840_2106721 pp.pos base h)).elim
    · exact (missing (smooth_6846840_2633401 pp.pos base h)).elim
    · exact (missing (smooth_6846840_3160081 pp.pos base h)).elim
    · exact (missing (smooth_6846840_4213441 pp.pos base h)).elim
    · exact (missing (smooth_6846840_4740121 pp.pos base h)).elim
    · exact (missing (smooth_6846840_5266801 pp.pos base h)).elim
    · exact (missing (smooth_6846840_5793481 pp.pos base h)).elim
    · exact (missing (smooth_6846840_6320161 pp.pos base h)).elim
  exact stage3



private theorem nineteen_root_exclusion {p b q o w : ℕ}
    (pq : q.Prime) (lo : 2 < q) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : q∣p^19+524288) (nd : ¬q∣p+2)
    (per : 2^o%q=1) (w19 : w^19%q=1) (wn : w%q≠1)
    (reject : ∀ i ∈ List.range 18,
      let y := (q+1-(2*w^(i+1))%q)%q
      y^(o/o.gcd 6846840)%q≠2^(o/o.gcd 6846840)%q) : False := by
  let _ : Fact q.Prime := ⟨pq⟩
  let _ : Fact (Nat.Prime 19) := ⟨by decide⟩
  have mod1 (v : ℕ) : (v:ZMod q)=1 ↔ v%q=1 := by
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt pq.one_lt] using ZMod.natCast_eq_natCast_iff' v 1 q
  have two : (2:ZMod q)≠0 := by
    intro h
    have d := (ZMod.natCast_eq_zero_iff 2 q).mp h
    have := Nat.le_of_dvd (by decide : 0<2) d
    omega
  let z := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr mult
  push_cast at zero
  have z19 : z^19=1 := by dsimp [z]; rw [div_pow,div_eq_iff (pow_ne_zero _ two)]; linear_combination -zero
  have primitive : IsPrimitiveRoot (w:ZMod q) 19 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime
    (by simpa only [Nat.cast_pow] using (mod1 _).mpr w19) (fun h => wn ((mod1 _).mp h)))
  obtain ⟨i,hi,iw⟩ := primitive.eq_pow_of_pow_eq_one z19
  have wv : (w:ZMod q)^i * 2 = -(p:ZMod q) := (eq_div_iff two).mp iw
  have i0 : i≠0 := by
    rintro rfl
    rw [pow_zero,one_mul] at wv
    apply nd
    apply (ZMod.natCast_eq_zero_iff (p+2) q).mp
    push_cast
    linear_combination wv
  let y := (q+1-(2*w^i)%q)%q
  have bound : (2*w^i)%q ≤ q+1 := by have := Nat.mod_lt (2*w^i) pq.pos; omega
  have cast : (y:ZMod q)=(2:ZMod q)^b := by
    dsimp [y]
    rw [ZMod.natCast_mod,Nat.cast_sub bound,Nat.cast_add,ZMod.natCast_self,Nat.cast_one,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow]
    have bp := congrArg (fun n : ℕ => (n:ZMod q)) base
    push_cast at bp ⊢
    linear_combination bp - wv
  have cycle : (2:ZMod q)^o=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using (mod1 _).mpr per
  have projected := seventeen_compact_coset idx cycle
  rw [←cast] at projected
  have bad := reject (i-1) (List.mem_range.mpr (show i-1<18 by omega))
  rw [show i-1+1=i by omega] at bad
  apply bad
  apply (ZMod.natCast_eq_natCast_iff' _ _ q).mp
  push_cast
  exact projected

set_option maxRecDepth 12000 in
private theorem nineteen_interval {i start p b : ℕ} {N : ℤ} (cells : List ℕ)
    (pm : ℕ → ℕ → ℕ → ℕ) (eq : ∀ a e m, pm a e m=a^e%m)
    (checked : (cells.zipIdx start).all (fun entry =>
      let tok := entry.1
      let q := 38*entry.2+1
      if tok=0 then decide (q < 2)
      else if tok < 1024 then decide (1 < tok ∧ tok < q ∧ q%tok=0)
      else if tok=1024 then
        let a := (N%(q:ℤ)).toNat
        decide (a%q≠0 ∧ pm (a%q) (q/2) q=1)
      else
        let o := (tok-1025)/524288
        let w := (tok-1025)%524288
        decide (pm 2 o q=1 ∧ w^19%q=1 ∧ w%q≠1) &&
          (List.range 18).all (fun k =>
            let y := (q+1-(2*w^(k+1))%q)%q
            decide (pm y (o/o.gcd 6846840) q≠pm 2 (o/o.gcd 6846840) q)))=true)
    (low : start ≤ i) (high : i < start+cells.length)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) : jacobiSym N (38*i+1)=1 := by
  let q := 38*i+1
  have qlo : 2 < q := by dsimp [q]; have := pq.two_le; omega
  have inside : i-start < cells.length := by omega
  let tok := cells[i-start]
  have mem : (tok,i) ∈ cells.zipIdx start := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    ⟨low, List.getElem?_eq_getElem inside⟩
  have h := List.all_eq_true.mp checked (tok,i) mem
  dsimp only at h
  by_cases z : tok=0
  · rw [if_pos z] at h
    have := of_decide_eq_true h
    omega
  rw [if_neg z] at h
  by_cases sm : tok<1024
  · rw [if_pos sm] at h
    obtain ⟨a,l,d⟩ := of_decide_eq_true h
    have := (Nat.dvd_prime pq).mp (Nat.dvd_iff_mod_eq_zero.mpr d)
    omega
  rw [if_neg sm] at h
  by_cases pos : tok=1024
  · rw [if_pos pos] at h
    obtain ⟨nz,pow1⟩ := of_decide_eq_true h
    let a := (N%(q:ℤ)).toNat
    have cast : (a:ℤ)=N%(q:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg N (by exact_mod_cast (show q≠0 by omega)))
    let _ : Fact q.Prime := ⟨pq⟩
    change jacobiSym N q=1
    rw [jacobiSym.mod_left N q,←cast,←jacobiSym.legendreSym.to_jacobiSym,seventeen_smooth_legendre q a qlo,
      if_neg nz,if_pos (by simpa only [←eq] using pow1)]
  rw [if_neg pos] at h
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨period,root,nontriv⟩ := of_decide_eq_true head
  exfalso
  rw [eq] at period
  apply nineteen_root_exclusion (o:=(tok-1025)/524288) (w:=(tok-1025)%524288) pq qlo base idx mult nd period root nontriv
  intro k hk
  have reject := of_decide_eq_true (List.all_eq_true.mp tail k hk)
  simpa only [eq] using reject


set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_0 {i p b : ℕ} (ix : i/128=0) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=0)
    (cells:=[0,3,7,5,3,1024,39847116,3,5,7,3,1024,39847202,3,13,1024,3,1024,5,3,199231101,17,3,5,11,3,23,13,3,1024,7,3,79693657,5,3,11,37,3,5,776997278,3,1024,1024,3,7,29,3,1024,5,3,996149458,7,3,5,1024,3,278922906,11,3,1024,99617104,3,1235225435,5,3,7,13,3,5,43,3,1024,7,3,29,1024,3,767037046,5,3,796919843,1024,3,5,31,3,7,1733300223,3,17,11,3,13,5,3,23,41,3,5,53,3,11,2032144152,3,59,13,3,7,5,3,37,2211449683,3,5,7,3,1024,1165494685,3,139463353,1024,3,2430602300,5,3,249038366,2510296353,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<128; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_1 {i p b : ℕ} (ix : i/128=1) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=128)
    (cells:=[5,1024,3,13,29,3,11,7,3,41,5,3,17,23,3,5,13,3,31,37,3,7,1024,3,53,5,3,43,7,3,5,1024,3,29,47,3,23,1024,3,11,5,3,7,67,3,5,17,3,1024,7,3,3566214084,896533829,3,3625980897,5,3,79,3705673509,3,5,11,3,7,1024,3,73,3884975522,3,1024,5,3,11,667427013,3,5,169348625,3,4104129528,1024,3,13,23,3,7,5,3,4283442093,1075840478,3,5,7,3,37,11,3,2231373426,17,3,4522516885,5,3,1024,1024,3,5,1553993956,3,1024,2360878170,3,31,7,3,17,5,3,1024,4901049672,3,5,826809473,3,5000667248,61,3,7,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<256; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_2 {i p b : ℕ} (ix : i/128=2) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=256)
    (cells:=[3,2560101863,5,3,41,7,3,5,79,3,11,73,3,1024,31,3,1024,5,3,7,17,3,5,23,3,59,7,3,43,2839029367,3,13,5,3,103,1932529920,3,5,1024,3,7,328740588,3,11,13,3,23,5,3,67,29,3,5,3078102000,3,53,71,3,6255815359,1024,3,7,5,3,1593839434,11,3,5,7,3,13,17,3,172495335,1314926603,3,11,5,3,29,113,3,5,13,3,1024,41,3,17,7,3,6913268322,5,3,47,1024,3,5,11,3,83,3556258114,3,7,3586131962,3,7212114090,5,3,11,7,3,5,37,3,23,67,3,61,1494223643,3,288887739,5,3,7,1265122338,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<384; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_3 {i p b : ℕ} (ix : i/128=3) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=384)
    (cells:=[637537486,3,1024,7,3,1024,7769959877,3,488119843,5,3,17,101,3,5,59,3,7,2669688836,3,13,1024,3,1024,5,3,8168415364,1024,3,5,1024,3,129511046,13,3,1024,11,3,7,5,3,31,8487189007,3,5,7,3,11,1075843883,3,1024,61,3,1024,5,3,23,4393019306,3,5,47,3,17,1024,3,113,7,3,89,5,3,1813006101,13,3,5,1024,3,4592253052,97,3,7,41,3,1024,5,3,53,7,3,5,1024,3,1024,1583890831,3,109,17,3,13,5,3,7,11,3,5,1024,3,47,7,3,9841947524,13,3,11,5,3,1024,79,3,5,107,3,7,777011160,3,23,1024,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<512; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_4 {i p b : ℕ} (ix : i/128=4) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=512)
    (cells:=[2550149602,5,3,10260326161,5140138862,3,5,11,3,13,83,3,1024,71,3,7,5,3,11,17,3,5,7,3,1024,1024,3,1534086625,1024,3,43,5,3,139,1024,3,5,31,3,10977553656,11,3,37,7,3,61,5,3,13,5588399290,3,5,1024,3,137,29,3,7,11356092492,3,5697984303,5,3,1024,7,3,5,1024,3,5787637386,17,3,1024,11,3,1024,5,3,7,37,3,5,622856224,3,11,7,3,13,151,3,11993614755,5,3,83,1024,3,5,1024,3,7,13,3,1024,12252619399,3,1024,5,3,3088078261,687348762,3,5,23,3,12471781237,1024,3,11,89,3,7,5,3,59,1024,3,5,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<640; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_5 {i p b : ℕ} (ix : i/128=5) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=640)
    (cells:=[3,1024,31,3,1603809680,127,3,23,5,3,17,11,3,5,29,3,97,6544689003,3,79,7,3,11,5,3,37,358630231,3,5,1024,3,43,1024,3,7,113,3,13,5,3,1024,7,3,5,11,3,131,13687088766,3,1024,13,3,1024,5,3,7,6933201697,3,5,101,3,17,7,3,31,73,3,67,5,3,2829061017,41,3,5,43,3,7,11,3,89,1024,3,14384368453,5,3,1024,47,3,5,13,3,14563679219,1024,3,14623456577,17,3,7,5,3,61,29,3,5,7,3,1024,1024,3,7461161509,11,3,17,5,3,13,1024,3,5,15121533641,3,11,23,3,1902657071,7,3,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<768; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_6 {i p b : ℕ} (ix : i/128=6) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=768)
    (cells:=[5,3,29,83,3,5,67,3,37,1024,3,7,7769957979,3,1024,5,3,23,7,3,5,1024,3,1024,7889491534,3,11,1024,3,31,5,3,7,61,3,5,8009027301,3,109,7,3,71,16137601022,3,59,5,3,1024,11,3,5,1024,3,7,1024,3,173,107,3,11,5,3,3307216912,23,3,5,41,3,1024,17,3,1024,137,3,7,5,3,163,13,3,5,7,3,73,1024,3,17,1024,3,29,5,3,11,8576860740,3,5,1024,3,17253286102,47,3,1024,7,3,13,5,3,41,1024,3,5,307260134,3,8776073156,11,3,7,13,3,37,5,3,31,7,3,5,53,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<896; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_7 {i p b : ℕ} (ix : i/128=7) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=896)
    (cells:=[79,89,3,127,23,3,151,5,3,7,1024,3,5,9054998932,3,13,7,3,47,11,3,1304969911,5,3,1145578796,31,3,5,13,3,7,1024,3,43,59,3,107,5,3,1024,3108009078,3,5,17,3,9373764079,18767426780,3,29,1024,3,7,5,3,13,71,3,5,7,3,17,41,3,11,191,3,139,5,3,1024,1024,3,5,23,3,1024,43,3,19404983105,7,3,137,5,3,167,11,3,5,61,3,89,6554677915,3,7,17,3,11,5,3,1024,7,3,5,1024,3,906520416,13,3,1024,181,3,17,5,3,7,103,3,5,11,3,10120881190,7,3,1024,83,3,71,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1024; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_8 {i p b : ℕ} (ix : i/128=8) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1024)
    (cells:=[3,11,127,3,5,10250389749,3,7,1024,3,20600343437,37,3,157,5,3,1024,13,3,5,97,3,1024,11,3,1024,1024,3,7,5,3,47,10519348441,3,5,7,3,23,7052748565,3,1024,707287232,3,13,5,3,73,1024,3,5,1024,3,31,3576178261,3,131,7,3,1024,5,3,10808201344,1024,3,5,29,3,11,17,3,7,1024,3,1024,5,3,1024,7,3,5,10997501853,3,13,23,3,17,7371508395,3,1024,5,3,7,11117024264,3,5,13,3,41,7,3,11,1024,3,113,5,3,23,1024,3,5,1024,3,7,1024,3,22692254005,1024,3,1024,5,3,13,11,3,5,47,3,191]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1152; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_9 {i p b : ℕ} (ix : i/128=9) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1152)
    (cells:=[1912609356,3,22991084350,1534094650,3,7,5,3,17,11565291597,3,5,7,3,59,61,3,31,173,3,1024,5,3,23409483681,23,3,5,11,3,1024,7849646528,3,13,7,3,43,5,3,11,1024,3,5,17,3,47,13,3,7,31,3,1024,5,3,29,7,3,5,1024,3,17,11,3,24186494363,8068836375,3,103,5,3,7,1024,3,5,193,3,1024,7,3,1024,43,3,6136292996,5,3,71,13,3,5,197,3,7,109,3,41,11,3,24843940813,5,3,1024,137,3,5,1024,3,11,37,3,25083007513,3137869985,3,7,5,3,53,1024,3,5,7,3,25322079536,1024,3,1024,13,3,12720847449,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1280; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_10 {i p b : ℕ} (ix : i/128=10) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1280)
    (cells:=[127,1024,3,5,59,3,1024,1024,3,11,7,3,29,5,3,25800262197,17,3,5,1024,3,13,65060973,3,7,101,3,1024,5,3,67,7,3,5,13,3,43,1024,3,26278375262,103,3,11,5,3,7,41,3,5,13238808608,3,37,7,3,163,97,3,23,5,3,13,131,3,5,11,3,7,17,3,1024,29,3,83,5,3,11,227,3,5,43,3,1024,73,3,17,4532504894,3,7,5,3,79,53,3,5,7,3,3426789299,11,3,13,229,3,1024,5,3,1024,31,3,5,1024,3,2131798242,13,3,1024,7,3,13916183933,5,3,1024,4652032161,3,5,1024,3,23,127]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1408; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_11 {i p b : ℕ} (ix : i/128=11) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1408)
    (cells:=[3,7,11,3,7032804002,5,3,17,7,3,5,1024,3,11,1024,3,53,1024,3,211,5,3,7,13,3,5,1024,3,197,7,3,149,199278824,3,37,5,3,43,28808632121,3,5,17,3,7,23,3,11,1024,3,13,5,3,109,59,3,5,95978913,3,17,107,3,14633418822,13,3,7,5,3,23,11,3,5,7,3,167,199,3,14782871857,2958569397,3,11,5,3,41,29705121815,3,5,1024,3,13,163,3,1024,7,3,1024,5,3,1024,151,3,5,11,3,67,269004854,3,7,6036675257,3,17,5,3,11,7,3,5,29,3,103,30422388592,3,97,53,3,15261030730,5,3,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1536; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_12 {i p b : ℕ} (ix : i/128=12) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1536)
    (cells:=[7650423924,3,5,233,3,31,7,3,23,15390532492,3,30820824184,5,3,1024,17,3,5,1024,3,7,15510070143,3,31059891693,1942542899,3,1024,5,3,1024,10399802180,3,5,109,3,31298963493,31,3,13,11,3,7,5,3,3147874027,73,3,5,7,3,11,13,3,15828834035,23,3,15858677025,5,3,2888867278,1024,3,5,10618981170,3,83,17,3,1024,7,3,79,5,3,193,29,3,5,32155639501,3,16097752589,43,3,7,5379208082,3,1024,5,3,1024,7,3,5,103,3,1024,1024,3,31,1024,3,1024,5,3,7,11,3,5,1364764009,3,32793185807,7,3,223,1024,3,11,5,3,61,1024,3,5,23,3,7,137,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1664; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_13 {i p b : ℕ} (ix : i/128=13) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1664)
    (cells:=[37,13,3,1024,5,3,17,11097115619,3,5,11,3,878766063,16705394921,3,1024,418438655,3,7,5,3,11,79,3,5,7,3,13,113,3,1024,41,3,59,5,3,1024,37,3,5,13,3,241,11,3,101,7,3,67,5,3,34167892033,61,3,5,34247574181,3,17,1633717491,3,7,5727864376,3,29,5,3,13,7,3,5,131,3,41,149,3,1024,11,3,53,5,3,7,43,3,5,1024,3,11,7,3,34944868407,17,3,179,5,3,47,1024,3,5,1024,3,7,83,3,13,1024,3,17,5,3,37,2211496751,3,5,67,3,17741434310,13,3,11,29,3,7,5,3,251,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1792; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_14 {i p b : ℕ} (ix : i/128=14) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1792)
    (cells:=[3,5,7,3,139,23,3,137,73,3,1024,5,3,113,11,3,5,1024,3,1024,37,3,29,7,3,11,5,3,23,13,3,5,1024,3,1024,36399281340,3,7,197,3,43,5,3,103,7,3,5,11,3,1024,1024,3,79,1024,3,13,5,3,7,31,3,5,47,3,1024,7,3,41,13,3,173,5,3,131,23,3,5,1024,3,7,11,3,17,43,3,1024,5,3,199,18737575684,3,5,1024,3,13,37594642539,3,23,1024,3,7,5,3,107,109,3,5,7,3,29,1024,3,18966683486,11,3,1024,5,3,181,101,3,5,38132561871,3,11,97,3,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<1920; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_15 {i p b : ℕ} (ix : i/128=15) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=1920)
    (cells:=[7,3,1024,5,3,13,1024,3,5,19215743171,3,1024,1024,3,7,23,3,1024,5,3,1024,7,3,5,31,3,73,241,3,11,38849780291,3,1024,5,3,7,239,3,5,17,3,43,7,3,13,89,3,1024,5,3,1024,11,3,5,1024,3,7,13,3,157,67,3,11,5,3,1024,163,3,5,1024,3,39666607396,59,3,39726359045,47,3,7,5,3,1048646232,1024,3,5,7,3,31,53,3,20012638402,17,3,101,5,3,11,13,3,5,73,3,61,13428132556,3,10081023128,7,3,17,5,3,8088729178,113,3,5,37,3,20281593252,11,3,7,1024,3,13,5,3,20371256308,7,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2048; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_16 {i p b : ℕ} (ix : i/128=16) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2048)
    (cells:=[5,1024,3,59,1024,3,89,13,3,20490788601,5,3,7,17,3,5,41,3,1024,7,3,20610364720,11,3,1024,5,3,29,10340010470,3,5,199,3,7,61,3,5189978113,1024,3,71,5,3,43,181,3,5,13,3,23,1024,3,31,10459561030,3,7,5,3,41,191,3,5,7,3,97,17,3,11,179,3,1024,5,3,13,1024,3,5,21158232632,3,1024,131,3,17,7,3,1024,5,3,42535492418,11,3,5,1024,3,21327571877,23,3,7,37,3,11,5,3,1024,7,3,5,1024,3,1130412825,1024,3,13,79,3,29,5,3,7,53,3,5,11,3,1024,7,3,43312556201,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2176; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_17 {i p b : ℕ} (ix : i/128=17) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2176)
    (cells:=[3,1024,5,3,11,67,3,5,149,3,7,41,3,193,1024,3,31,5,3,239,1024,3,5,1024,3,1024,11,3,61,209194314,3,7,5,3,137,13,3,5,7,3,107,1024,3,37,29,3,1024,5,3,4432887563,1024,3,5,71,3,17,89,3,23,7,3,13,5,3,1024,1024,3,5,269,3,11,103,3,7,13,3,5608372565,5,3,44926245512,7,3,5,1024,3,151,43,3,227,17,3,277,5,3,7,211,3,5,45304827826,3,13,7,3,11,23,3,17,5,3,31,1024,3,5,13,3,7,251,3,179,1024,3,191,5,3,71,11,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2304; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_18 {i p b : ℕ} (ix : i/128=18) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2304)
    (cells:=[1024,3,1024,29,3,1024,41,3,7,5,3,13,17,3,5,7,3,89,46261149242,3,47,53,3,1024,5,3,37,283,3,5,11,3,29,23280038348,3,1024,7,3,1024,5,3,11,59,3,5,23,3,41,139,3,7,46918608266,3,1024,5,3,1024,7,3,5,3924903098,3,1024,11,3,23598790231,113,3,23,5,3,7,1024,3,5,1024,3,173,7,3,17,23758199244,3,61,5,3,1024,43,3,5,29,3,7,79,3,1024,11,3,97,5,3,59,13,3,5,31,3,11,151,3,1024,1024,3,7,5,3,253818097,197,3,5,7,3,1024,16117703059,3,241,107,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2432; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_19 {i p b : ℕ} (ix : i/128=19) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2432)
    (cells:=[13,5,3,17,12133112368,3,5,5399164206,3,23,71,3,11,7,3,1024,5,3,157,48831229309,3,5,48890942865,3,643919199,73,3,7,8168412482,3,1024,5,3,47,7,3,5,17,3,13,1024,3,41,163,3,11,5,3,7,29,3,5,13,3,17,7,3,1024,1024,3,281,5,3,1024,327178179,3,5,11,3,7,31,3,1024,1024,3,1024,5,3,11,1024,3,5,83,3,67,101,3,50185963537,17,3,7,5,3,229,1024,3,5,7,3,50425026411,11,3,50484810236,2658188991,3,17,5,3,263,223,3,5,277,3,1024,50743805613,3,13,7,3,37,5,3,79,23,3,5,47]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2560; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_20 {i p b : ℕ} (ix : i/128=20) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2560)
    (cells:=[3,307,13,3,7,11,3,1024,5,3,61,7,3,5,1024,3,11,1024,3,23,1024,3,59,5,3,7,51520739516,3,5,37,3,1024,7,3,51680205822,31,3,29,5,3,1024,13,3,5,1024,3,7,157,3,11,1155543698,3,1024,5,3,1024,8686484120,3,5,1024,3,137,17,3,26138966314,23,3,7,5,3,139,11,3,5,7,3,1024,26268416210,3,17,13,3,11,5,3,26348112061,1024,3,5,43,3,131,179,3,1024,7,3,31,5,3,26497561450,1024,3,5,11,3,13,1024,3,7,241,3,26617054948,5,3,11,7,3,5,13,3,26706734937,5937060193,3,29,1024,3,53533014310]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2688; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_21 {i p b : ℕ} (ix : i/128=21) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2688)
    (cells:=[5,3,7,1024,3,5,23,3,53,7,3,1024,37,3,1024,5,3,13,53911536537,3,5,113,3,7,257,3,151,18030270484,3,23,5,3,41,1024,3,5,17,3,71,173,3,1024,11,3,7,5,3,43,6813715454,3,5,7,3,11,29,3,13,1024,3,47,5,3,31,107,3,5,229,3,518045731,13,3,59,7,3,103,5,3,27543529547,89,3,5,139,3,29,27613267975,3,7,17,3,27663031908,5,3,149,7,3,5,67,3,23,1024,3,27782651759,97,3,17,5,3,7,11,3,5,55764381822,3,163,7,3,127,133695398,3,11,5,3,55983498414,37,3,5,61,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2816; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_22 {i p b : ℕ} (ix : i/128=22) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2816)
    (cells:=[7,167,3,1024,101,3,13,5,3,1024,17,3,5,11,3,179,23,3,56461706124,13,3,7,5,3,11,47,3,5,7,3,83,1024,3,28380277241,1024,3,28410135828,5,3,23,14225075719,3,5,1024,3,13,11,3,43,7,3,1024,5,3,191,79,3,5,13,3,293,17,3,7,1024,3,57417945989,5,3,37,7,3,5,311,3,57597242559,1024,3,17,11,3,283,5,3,7,23,3,5,211,3,11,7,3,1024,1024,3,239,5,3,58075427818,29,3,5,19385081118,3,7,37,3,23,41,3,58314522713,5,3,1024,127,3,5,1024,3,31,233,3,11,2440662867,3,7,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<2944; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_23 {i p b : ℕ} (ix : i/128=23) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=2944)
    (cells:=[3,17,1024,3,5,7,3,58792631210,13,3,1024,11774540250,3,313,5,3,1024,11,3,5,163,3,41,31,3,257,7,3,11,5,3,1693559074,29645386685,3,5,17,3,1024,47,3,7,67,3,223,5,3,1024,7,3,5,11,3,17,61,3,1024,1024,3,59808721987,5,3,7,59888464982,3,5,29974104215,3,1024,7,3,53,1024,3,13,5,3,1024,1024,3,5,15061827567,3,7,11,3,31,13,3,29,5,3,1024,43,3,5,23,3,73,1024,3,131,251,3,7,5,3,60764995992,269,3,5,7,3,13,1024,3,1024,11,3,23,5,3,1024,263,3,5,13,3,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3072; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_24 {i p b : ℕ} (ix : i/128=24) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3072)
    (cells:=[107,3,199,7,3,1024,5,3,7670374578,17,3,5,1024,3,1024,6833611204,3,7,29,3,1024,5,3,13,7,3,5,61741301878,3,1024,61800984216,3,11,30930379279,3,37,5,3,7,1024,3,5,73,3,1024,7,3,29,53,3,31,5,3,1024,11,3,5,31169536056,3,7,17,3,13,62458467552,3,11,5,3,1024,10429753495,3,5,37,3,1024,13,3,17,62757350861,3,7,5,3,1024,1024,3,5,7,3,113,1024,3,1024,43,3,151,5,3,11,41,3,5,103,3,31637737905,23,3,107,7,3,1024,5,3,127,13,3,5,179,3,63574216112,11,3,7,317,3,31846913059,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3200; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_25 {i p b : ℕ} (ix : i/128=25) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3200)
    (cells:=[17,7,3,5,109,3,29,21297672152,3,197,223,3,13,5,3,7,1024,3,5,1024,3,32085916417,7,3,101,11,3,149,5,3,1024,59,3,5,17,3,7,32245375674,3,1024,1024,3,349,5,3,1024,23,3,5,331,3,13,191,3,1024,37,3,7,5,3,73,83,3,5,7,3,79,1024,3,11,313,3,1024,5,3,97,16316990183,3,5,53,3,1024,1024,3,32713571118,7,3,1024,5,3,13,11,3,5,41,3,251,1024,3,7,89,3,11,5,3,1024,7,3,5,1024,3,47,127,3,1024,23,3,33042308342,5,3,7,1024,3,5,11,3,211,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3328; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_26 {i p b : ℕ} (ix : i/128=26) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3328)
    (cells:=[3,13,1024,3,53,5,3,11,17,3,5,31,3,7,13,3,83,79,3,193,5,3,66741954809,29,3,5,1024,3,1024,11,3,1024,440439397,3,7,5,3,71,37,3,5,7,3,1024,97,3,1024,277,3,33639935336,5,3,29,13,3,5,23,3,1024,17,3,89,7,3,157,5,3,1024,1024,3,5,227,3,11,67777931687,3,7,47,3,13,5,3,67937331020,7,3,5,1024,3,271,41,3,173,13,3,109,5,3,7,101,3,5,1024,3,1024,7,3,11,13687091187,3,131,5,3,37,229,3,5,4901076190,3,7,7630584940,3,34357130350,119637217,3,47,5,3,17]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3456; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_27 {i p b : ℕ} (ix : i/128=27) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3456)
    (cells:=[11,3,5,13,3,1024,293,3,139,2301231247,3,7,5,3,69132721995,69152560105,3,5,7,3,23,37,3,73,1024,3,307,5,3,13,23150473158,3,5,11,3,53,1024,3,31,7,3,1024,5,3,11,1024,3,5,1024,3,17,71,3,7,83,3,317,5,3,1024,7,3,5,70108920211,3,67,11,3,13,29,3,101,5,3,7,109,3,5,3705763656,3,1024,7,3,181,17,3,1024,5,3,23,47,3,5,157,3,7,43,3,29,11,3,17,5,3,4432959376,1024,3,5,1024,3,11,89,3,1024,23708378101,3,7,5,3,71224576944,13,3,5,7,3,41,79,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3584; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_28 {i p b : ℕ} (ix : i/128=28) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3584)
    (cells:=[1024,59,3,31,5,3,14304775009,17,3,5,71603154743,3,1024,53,3,11,7,3,13,5,3,1024,1024,3,5,1024,3,71941851455,29,3,7,13,3,1024,5,3,151,7,3,5,1024,3,227,24086936315,3,239,1024,3,11,5,3,7,233,3,5,72499659115,3,13,7,3,59,36309704018,3,1024,5,3,53,1024,3,5,11,3,7,36429181328,3,17,23,3,37,5,3,11,1024,3,5,36548723778,3,199,1024,3,149,359,3,7,5,3,13,43,3,5,7,3,1024,11,3,103,1024,3,9194450608,5,3,73615301137,18408883320,3,5,29,3,1024,73754754921,3,41,7,3,6714157543,5,3,17,31]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3712; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_29 {i p b : ℕ} (ix : i/128=29) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3712)
    (cells:=[3,5,107,3,18508422019,137,3,7,11,3,67,5,3,37106508927,7,3,5,23,3,11,13,3,47,1024,3,1024,5,3,7,37265937618,3,5,17,3,283,7,3,109,4980763489,3,23,5,3,293,53,3,5,83,3,7,59,3,11,173,3,43,5,3,15022018922,13,3,5,75189199431,3,1024,1024,3,163,379,3,7,5,3,37704201211,11,3,5,7,3,71,103,3,75587729007,17,3,11,5,3,197,1024,3,5,31,3,75826726299,1024,3,53,7,3,17,5,3,29,12671051880,3,5,11,3,23,311,3,7,191,3,41,5,3,11,7,3,5,89,3,13,38222225967,3,113]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3840; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_30 {i p b : ℕ} (ix : i/128=30) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3840)
    (cells:=[337,3,83,5,3,7,17,3,5,13,3,61,7,3,137,263,3,97,5,3,38451282984,38461248757,3,5,38491135164,3,7,23,3,233,199,3,1024,5,3,13,1024,3,5,223,3,139,1024,3,37,11,3,7,5,3,23,77520216349,3,5,7,3,11,17,3,229,1024,3,29,5,3,179,1024,3,5,41,3,331,61,3,13,7,3,73,5,3,1024,37,3,5,1024,3,193,13,3,7,1024,3,39168635218,5,3,4126195723,7,3,5,43,3,1024,163,3,19644079131,1024,3,127,5,3,7,11,3,5,97,3,39407667749,7,3,23,29,3,11,5,3,17,13,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<3968; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_31 {i p b : ℕ} (ix : i/128=31) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=3968)
    (cells:=[5,47,3,7,149,3,79173881136,1024,3,79,5,3,3964735178,13218886166,3,5,11,3,167,1024,3,29,31,3,7,5,3,11,1024,3,5,7,3,39855974655,26577328094,3,71,13,3,1024,5,3,15978227466,79911046006,3,5,1024,3,17,11,3,1024,7,3,1024,5,3,43,1024,3,5,283,3,13,37,3,7,107,3,1024,5,3,1024,7,3,5,13,3,11515493167,29,3,251,11,3,31,5,3,7,79,3,5,1024,3,11,7,3,389,113,3,17,5,3,13,1024,3,5,23,3,7,1024,3,81265707058,227,3,181,5,3,40692722472,9045119690,3,5,40732525019,3,83,131,3,11,61]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4096; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_32 {i p b : ℕ} (ix : i/128=32) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4096)
    (cells:=[3,7,5,3,1024,17,3,5,7,3,37,239,3,13,47,3,1024,5,3,81983012586,11,3,5,193,3,149,13,3,67,7,3,11,5,3,82281853344,9144687074,3,5,29,3,73,1024,3,7,13746985396,3,107,5,3,31,7,3,5,11,3,82700242926,17,3,43,41,3,47,5,3,7,13,3,5,1024,3,23,7,3,17,211,3,10389847993,5,3,59,31,3,5,1024,3,7,11,3,1024,109,3,13,5,3,89,67,3,5,197,3,41,43,3,1024,13,3,7,5,3,41888009782,277,3,5,7,3,83895604031,23,3,79,11,3,37,5,3,17,29,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4224; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_33 {i p b : ℕ} (ix : i/128=33) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4224)
    (cells:=[151,3,11,1024,3,271,7,3,42156953029,5,3,23,119578666,3,5,13,3,1024,331,3,7,97,3,84612866600,5,3,29,7,3,5,17,3,1024,83,3,11,1024,3,1024,5,3,7,1024,3,5,31,3,17,7,3,1024,1024,3,42605231905,5,3,10658779667,11,3,5,173,3,7,1024,3,349,4498400776,3,11,5,3,1024,1024,3,5,85648892819,3,353,1024,3,13,17,3,7,5,3,1024,1024,3,5,7,3,401,13,3,41,167,3,17,5,3,11,43,3,5,43123247272,3,31,7192221464,3,157,7,3,29,5,3,83,293,3,5,383,3,239,11,3,7,23,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4352; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_34 {i p b : ℕ} (ix : i/128=34) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4352)
    (cells:=[59,5,3,73,7,3,5,71,3,1024,31,3,10868068226,37,3,87003635542,5,3,7,1024,3,5,347,3,1024,7,3,87242694030,11,3,13,5,3,43681170163,1024,3,5,43720904683,3,7,47,3,87541444808,13,3,1024,5,3,61,41,3,5,113,3,1024,17,3,1024,103,3,7,5,3,87959848730,14663365133,3,5,7,3,13,1024,3,11,1024,3,1024,5,3,71,163,3,5,13,3,101,139,3,37,7,3,23,5,3,53,11,3,5,1024,3,79,1024,3,7,31,3,11,5,3,13,7,3,5,1024,3,12710845771,199,3,1024,59,3,1024,5,3,7,37,3,5,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4480; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_35 {i p b : ℕ} (ix : i/128=35) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4480)
    (cells:=[3,1024,7,3,1024,131,3,167,5,3,11,157,3,5,89533793529,3,7,1024,3,13,271,3,1024,5,3,193,83,3,5,17,3,23,11,3,337,17990422097,3,7,5,3,1024,45035952113,3,5,7,3,17,1024,3,59,79,3,1024,5,3,1024,97,3,5,137,3,43,1024,3,1024,7,3,1024,5,3,37,13,3,5,1024,3,11,23,3,7,17,3,1024,5,3,41,7,3,5,29,3,91067900618,71,3,73,1024,3,13,5,3,7,1024,3,5,43,3,229,7,3,11,13,3,211,5,3,283,15261064912,3,5,1024,3,7,1024,3,53,1024,3,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4608; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_36 {i p b : ℕ} (ix : i/128=36) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4608)
    (cells:=[5,3,31,11,3,5,1024,3,13,45992275360,3,92024227544,419,3,7,5,3,181,23,3,5,7,3,92263170240,1024,3,293,89,3,1024,5,3,1024,31,3,5,11,3,1024,41,3,23,7,3,1024,5,3,11,29,3,5,1024,3,37,17,3,7,269,3,92980550787,5,3,43,7,3,5,47,3,137,11,3,17,1024,3,1024,5,3,7,93358960993,3,5,1024,3,93458566410,7,3,13,23,3,1024,5,3,9363828577,1024,3,5,1024,3,7,13,3,127,11,3,1024,5,3,139,1024,3,5,103,3,11,1024,3,89,409,3,7,5,3,17,94255506545,3,5,7,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4736; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_37 {i p b : ℕ} (ix : i/128=37) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4736)
    (cells:=[1024,15729306295,3,101,281,3,367,5,3,1024,13,3,5,1024,3,1024,359,3,11,7,3,163,5,3,277,227,3,5,17,3,61,79,3,7,41,3,13,5,3,421,7,3,5,1024,3,17,1024,3,107,13,3,11,5,3,7,1024,3,5,67,3,31,7,3,43,179,3,251,5,3,157,181,3,5,11,3,7,1024,3,95909235914,17,3,1024,5,3,11,167,3,5,13,3,96148226252,31,3,48104057448,29,3,7,5,3,313,127,3,5,7,3,1024,11,3,1024,9652685702,3,96566604600,5,3,13,337,3,5,139,3,23,1024,3,29,7,3,47,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4864; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_38 {i p b : ℕ} (ix : i/128=38) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4864)
    (cells:=[3,199,17,3,5,53,3,1024,1673580607,3,7,11,3,1024,5,3,607710409,7,3,5,12163032897,3,11,1024,3,13,1024,3,12182940072,5,3,7,1024,3,5,1024,3,48821237789,7,3,331,1024,3,263,5,3,97821771627,1024,3,5,836789867,3,7,17,3,11,31,3,53,5,3,23,1024,3,5,1024,3,98240159792,646498300,3,17,14045839841,3,7,5,3,9842078708,11,3,5,7,3,29,1024,3,61,137,3,11,5,3,98718222957,47,3,5,1024,3,49419036868,157,3,1024,7,3,13,5,3,1024,23,3,5,11,3,173,1024,3,7,13,3,31,5,3,11,7,3,5,1024,3,89]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<4992; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_39 {i p b : ℕ} (ix : i/128=39) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=4992)
    (cells:=[1024,3,23,67,3,49777648396,5,3,7,59,3,5,29,3,13,7,3,131,61,3,73,5,3,149,41,3,5,13,3,7,1024,3,25023338533,257,3,1024,5,3,1024,37,3,5,233,3,17,277,3,419,11,3,7,5,3,13,1024,3,5,7,3,11,25162755524,3,100690564629,1024,3,41,5,3,59,1024,3,5,199,3,311,1024,3,71,7,3,50524717042,5,3,31,1024,3,5,101188710042,3,53,113,3,7,73,3,17,5,3,127,7,3,5,101487561790,3,25381997135,13,3,1024,43,3,101646997688,5,3,7,11,3,5,23,3,359,7,3,373,101905977118,3,11,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5120; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_40 {i p b : ℕ} (ix : i/128=40) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5120)
    (cells:=[29,17,3,5,1024,3,7,1024,3,67,151,3,23,5,3,20460870796,13,3,5,11,3,51211944162,37,3,47,1024,3,7,5,3,11,1024,3,5,7,3,51361488035,1902781761,3,1024,1024,3,13,5,3,1024,109,3,5,89,3,1024,11,3,1024,7,3,1024,5,3,41,1024,3,5,1024,3,43,53,3,7,1024,3,1024,5,3,113,7,3,5,31,3,13,1024,3,1024,11,3,29,5,3,7,71,3,5,13,3,11,7,3,1024,293,3,1024,5,3,211,1024,3,5,43,3,7,1024,3,103,331,3,59,5,3,13,79,3,5,101,3,163,23]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5248; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_41 {i p b : ℕ} (ix : i/128=41) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5248)
    (cells:=[3,11,104595559844,3,7,5,3,397,1024,3,5,7,3,31,41,3,172573378,29,3,233,5,3,23,11,3,5,17,3,157,193,3,13,7,3,11,5,3,47,1024,3,5,1024,3,17,13,3,7,105492040879,3,1024,5,3,2639791308,7,3,5,11,3,105711150795,1024,3,1024,11754566013,3,97,5,3,7,23,3,5,107,3,241,7,3,307,17,3,37,5,3,67,13,3,5,1024,3,7,11,3,23,1024,3,17,5,3,101,53,3,5,181,3,106607714668,29,3,31,59,3,7,5,3,353,137,3,5,7,3,1024,106926514598,3,1024,11,3,1024,5,3,107085908378]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5376; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_42 {i p b : ℕ} (ix : i/128=42) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5376)
    (cells:=[17,3,5,47,3,11,1024,3,109,7,3,1024,5,3,1024,1024,3,5,35821642502,3,13,67,3,7,53792099225,3,131,5,3,1024,7,3,5,13,3,107803121417,4901164457,3,11,347,3,1024,5,3,7,113,3,5,71,3,41,7,3,1024,108181631814,3,151,5,3,13,11,3,5,29,3,7,227,3,17,1024,3,11,5,3,73,108600027822,3,5,23,3,4940963248,54359755619,3,108759377317,1024,3,7,5,3,54439490017,108898955837,3,5,7,3,127,269,3,13,37,3,23,5,3,11,54598939746,3,5,18209603003,3,109297372210,13,3,167,7,3,1024,5,3,17,457,3,5,1024,3,1024,11,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5504; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_43 {i p b : ℕ} (ix : i/128=43) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5504)
    (cells:=[7,53,3,1024,5,3,1024,7,3,5,1024,3,179,6106465797,3,401,47,3,1024,5,3,7,13,3,5,17,3,67,7,3,113,11,3,1024,5,3,31,239,3,5,191,3,7,101,3,37,110572500122,3,13,5,3,29,1024,3,5,61,3,55395929214,241,3,1024,13,3,7,5,3,110971003825,31,3,5,7,3,1024,55555203813,3,11,17,3,1024,5,3,83,37,3,5,55674818684,3,13,23,3,111449077050,7,3,17,5,3,1024,11,3,5,13,3,111688237993,1024,3,7,1024,3,11,5,3,23,7,3,5,1024,3,1024,112006925167,3,56023531788,1024,3,1024,5,3,7,17]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5632; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_44 {i p b : ℕ} (ix : i/128=44) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5632)
    (cells:=[3,5,11,3,79,7,3,1024,107,3,29,5,3,11,103,3,5,56272561770,3,7,397,3,1024,37554907079,3,1024,5,3,37,23,3,5,31,3,112883449962,11,3,13,1024,3,7,5,3,379,1024,3,5,7,3,61,13,3,23,349,3,1024,5,3,463,37793887050,3,5,1024,3,263,37,3,17,7,3,43,5,3,1024,1024,3,5,59,3,11,56900087299,3,7,79,3,53,5,3,5180126239,7,3,5,443,3,31,283,3,29,23,3,67,5,3,7,57139091522,3,5,114337830683,3,269,7,3,11,43,3,13,5,3,17,83,3,5,41,3,7,31,3,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5760; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_45 {i p b : ℕ} (ix : i/128=45) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5760)
    (cells:=[13,3,347,5,3,1024,11,3,5,1024,3,37,137,3,313,115055189622,3,7,5,3,239,1024,3,5,7,3,13,29,3,1024,6071437179,3,89,5,3,41,257,3,5,11,3,17,47,3,1024,7,3,1024,5,3,11,461,3,5,38610804110,3,29,1024,3,7,109,3,23,5,3,13,7,3,5,359,3,43,11,3,83,17,3,58145232363,5,3,7,173,3,5,1024,3,1024,7,3,47,31,3,17,5,3,271,193,3,5,116728698410,3,7,337,3,13,11,3,116888081272,5,3,1024,38989285095,3,5,29,3,11,13,3,1024,1024,3,7,5,3,151,17,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<5888; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_46 {i p b : ℕ} (ix : i/128=46) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=5888)
    (cells:=[5,7,3,23,181,3,97,1024,3,331,5,3,29386351860,1024,3,5,157,3,117664976727,117684917252,3,11,7,3,31,5,3,95476046,13,3,5,37,3,71,117983879401,3,7,61,3,1024,5,3,118143086635,7,3,5,1024,3,1024,17,3,118322487207,1024,3,11,5,3,7,118461920194,3,5,59260815417,3,101,7,3,17,13,3,59340710958,5,3,23,29,3,5,11,3,7,197,3,1024,89,3,1024,5,3,11,1024,3,5,127,3,13,53,3,3137427193,1024,3,7,5,3,29,97,3,5,7,3,1024,11,3,311,41,3,119577703151,5,3,17,23,3,5,389,3,1024,1024,3,173,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6016; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_47 {i p b : ℕ} (ix : i/128=47) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6016)
    (cells:=[3,59938208161,5,3,13,59978076942,3,5,1024,3,1024,1024,3,7,11,3,1024,5,3,53,7,3,5,17,3,11,439,3,241,1024,3,61,5,3,7,120553855086,3,5,379,3,17,7,3,13,60366540877,3,1024,5,3,1024,353,3,5,211,3,7,13,3,11,23,3,29,5,3,30282984257,1024,3,5,47,3,1024,313,3,43,17,3,7,5,3,1024,11,3,5,7,3,60775044403,1024,3,37,139,3,11,5,3,79,13,3,5,1024,3,1024,191,3,1024,7,3,59,5,3,1024,271,3,5,11,3,47,43,3,7,29,3,13,5,3,11,7,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6144; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_48 {i p b : ℕ} (ix : i/128=48) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6144)
    (cells:=[23,3,122446520302,109,3,1024,13,3,1024,5,3,7,449,3,5,40901849461,3,103,7,3,29,12282619243,3,23,5,3,122924623126,40981666458,3,5,41001639895,3,7,1024,3,1024,73,3,123163663681,5,3,97,1024,3,5,13,3,31,17,3,53,11,3,7,5,3,61761136450,67,3,5,7,3,11,149,3,17,367,3,113,5,3,13,8845932557,3,5,1024,3,61970355494,29,3,163,7,3,1024,5,3,61,124139966475,3,5,124199719211,3,23,89,3,7,59,3,193,5,3,307,7,3,5,83,3,29,37,3,13,1024,3,1024,5,3,7,11,3,5,103,3,124837174669,7,3,1024,1024,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6272; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_49 {i p b : ℕ} (ix : i/128=49) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6272)
    (cells:=[11,5,3,263271869,71,3,5,269,3,7,23,3,31,241,3,41,5,3,479,61,3,5,11,3,419,1024,3,59,53,3,7,5,3,11,13,3,5,7,3,17,1024,3,1024,31,3,1024,5,3,137,401,3,5,167,3,37,11,3,1024,7,3,13,5,3,67,1024,3,5,126291746370,3,63165793846,1024,3,7,13,3,43,5,3,227,7,3,5,126590463545,3,149,63325275195,3,1024,11,3,17,5,3,7,47,3,5,41,3,11,7,3,23,157,3,31,5,3,1024,1024,3,5,13,3,7,163,3,107,43,3,293,5,3,1024,17,3,5,73]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6400; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_50 {i p b : ℕ} (ix : i/128=50) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6400)
    (cells:=[3,1024,67,3,11,1024,3,7,5,3,13,179,3,5,7,3,1024,59,3,353,23,3,277,5,3,29,11,3,5,1024,3,1024,233,3,128184251977,7,3,11,5,3,12830542260,21387441105,3,5,64191787246,3,397,17,3,7,131,3,32135953111,5,3,128602842423,7,3,5,11,3,1024,13,3,17,1024,3,128841720240,5,3,7,1024,3,5,37,3,43,7,3,129080783909,56850383,3,129140612980,5,3,263,129220233643,3,5,23,3,7,11,3,129379607333,43133176826,3,239,5,3,16187513075,13,3,5,89,3,1024,47,3,1024,597874432,3,7,5,3,17,1024,3,5,7,3,1024,139,3,16247377401,11,3,13]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6528; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_51 {i p b : ℕ} (ix : i/128=51) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6528)
    (cells:=[5,3,26019556325,18588343064,3,5,1024,3,11,1024,3,1024,7,3,1024,5,3,73,1024,3,5,17,3,113,307,3,7,223,3,101,5,3,71,7,3,5,1024,3,13,257,3,11,29,3,1024,5,3,7,283,3,5,13,3,23,7,3,79,37,3,131232511209,5,3,179,11,3,5,31,3,7,65715866580,3,29,17,3,11,5,3,13,373,3,5,1024,3,131710710822,1024,3,127,41,3,7,5,3,1024,311,3,5,7,3,132009588463,23,3,66034717659,1024,3,1024,5,3,11,33052235099,3,5,44089525341,3,1024,383,3,13,7,3,229,5,3,23,17,3,5,149,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6656; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_52 {i p b : ℕ} (ix : i/128=52) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6656)
    (cells:=[31,11,3,7,11057439524,3,1024,5,3,233,7,3,5,1024,3,53,1024,3,1024,26597260494,3,487,5,3,7,66552746664,3,5,66582731888,3,29,7,3,157,11,3,109,5,3,47,13,3,5,277,3,7,17,3,33390923557,66791725006,3,281,5,3,107,44567822185,3,5,14862596552,3,66901488626,1024,3,17,1024,3,7,5,3,1024,134001840039,3,5,7,3,137,349,3,11,13,3,67,5,3,13428281980,127,3,5,29,3,1024,83,3,31,7,3,16815013294,5,3,197,11,3,5,101,3,13,1024,3,7,23,3,11,5,3,17,7,3,5,13,3,6136390174,43,3,41,31,3,1024,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6784; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_53 {i p b : ℕ} (ix : i/128=53) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6784)
    (cells:=[3,7,135197311501,3,5,11,3,151,7,3,1024,135376496676,3,181,5,3,11,109,3,5,17,3,7,37,3,1024,251,3,379,5,3,1024,1024,3,5,45284952947,3,17,11,3,257,167,3,7,5,3,53,29,3,5,7,3,47,73,3,13,61,3,31,5,3,68186465260,157,3,5,1024,3,136492343337,13,3,1024,7,3,23,5,3,29,41,3,5,97,3,11,457,3,7,1024,3,17,5,3,136970253627,7,3,5,173,3,37,103,3,1024,22861834333,3,1024,5,3,7,13,3,5,137348832346,3,1024,7,3,11,79,3,41,5,3,1024,17,3,5,22941449132,3,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<6912; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_54 {i p b : ℕ} (ix : i/128=54) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=6912)
    (cells:=[14160095,3,1024,71,3,13,5,3,439,11,3,5,107,3,23,138006419063,3,1024,13,3,7,5,3,31,53,3,5,7,3,1024,151,3,367,23060968409,3,29,5,3,1024,1024,3,5,11,3,13,17,3,1024,7,3,61,5,3,11,31,3,5,13,3,1024,23,3,7,239,3,47,5,3,69531309742,7,3,5,41,3,71,11,3,53,139261521651,3,37,5,3,7,83,3,5,317,3,223,7,3,17442771722,29,3,59,5,3,1024,263,3,5,193,3,7,23300124308,3,109,11,3,1024,5,3,17,313,3,5,37,3,11,70049318309,3,13,43,3,7,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7040; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_55 {i p b : ℕ} (ix : i/128=55) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7040)
    (cells:=[17532324464,23,3,5,7,3,1024,13,3,10031205706,1024,3,173,5,3,140556377113,73,3,5,17,3,251,101,3,11,7,3,1024,5,3,140855472789,47,3,5,140935087031,3,17,23499243279,3,7,1024,3,1024,5,3,1024,7,3,5,1024,3,467,29,3,1024,53,3,11,5,3,7,149,3,5,1024,3,1024,7,3,1024,17,3,13,5,3,1024,113,3,5,11,3,7,127,3,211,13,3,17,5,3,11,233,3,5,419,3,8885853837,79,3,67,37,3,7,5,3,61,1024,3,5,7,3,13,11,3,1024,97,3,1024,5,3,157,17,3,5,13,3,307,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7168; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_56 {i p b : ℕ} (ix : i/128=56) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7168)
    (cells:=[3,1024,7,3,1024,5,3,1024,389,3,5,23,3,71533516677,1024,3,7,11,3,1024,5,3,13,7,3,5,461,3,11,491,3,71,23907773814,3,23,5,3,7,61,3,5,23937561141,3,143664565364,7,3,31,11057484821,3,139,5,3,1024,331,3,5,223,3,7,1024,3,11,41,3,2251368736,5,3,144142729986,131,3,5,144222451151,3,1024,13,3,151,31,3,7,5,3,43,11,3,5,7,3,36140243146,1024,3,47,1024,3,11,5,3,359,29,3,5,281,3,23,18110014113,3,263,7,3,1024,5,3,17,13,3,5,11,3,1024,1024,3,7,145238515953,3,1024,5,3,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7296; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_57 {i p b : ℕ} (ix : i/128=57) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7296)
    (cells:=[7,3,5,1024,3,421,59,3,433,89,3,13,5,3,7,367,3,5,17,3,317,7,3,145816059647,13,3,1024,5,3,37,167,3,5,1024,3,7,73037783130,3,229,211,3,1024,5,3,23,71,3,5,1024,3,13,1024,3,97,11,3,7,5,3,269,139,3,5,7,3,11,37,3,233,17,3,131,5,3,146832266494,1024,3,5,79,3,127,24495499836,3,43,7,3,17,5,3,13,23,3,5,61,3,1024,1024,3,7,151,3,103,5,3,31,7,3,5,18438836054,3,1024,67,3,23,147629167728,3,71,5,3,7,11,3,5,49269701313,3,73,7,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7424; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_58 {i p b : ℕ} (ix : i/128=58) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7424)
    (cells:=[13,283,3,11,5,3,349,31,3,5,1024,3,7,13,3,148206789082,29,3,148266752443,5,3,1024,97,3,5,11,3,1024,199,3,191,23,3,7,5,3,11,74322716005,3,5,7,3,53,17,3,29,1024,3,1024,5,3,148924116627,13,3,5,59,3,271,11,3,17,7,3,1024,5,3,241,1024,3,5,47,3,443,347,3,7,103,3,13,5,3,1024,7,3,5,1024,3,61,1024,3,149701010649,11,3,41,5,3,7,181,3,5,23,3,11,7,3,1024,277,3,79,5,3,17,1024,3,5,1024,3,7,463,3,1024,15031986785,3,23,5,3,281,43]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7552; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_59 {i p b : ℕ} (ix : i/128=59) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7552)
    (cells:=[3,5,13,3,29,1024,3,11,1024,3,7,5,3,389,107,3,5,7,3,173,53,3,1024,1024,3,83,5,3,13,11,3,5,37,3,17,151155603838,3,1024,7,3,11,5,3,257,1024,3,5,41,3,75717376334,1024,3,7,1024,3,7976580275,5,3,1024,7,3,5,11,3,23,31,3,13,17,3,151852704353,5,3,7,50644253026,3,5,131,3,157,7,3,139,47,3,17,5,3,41,1024,3,5,1024,3,7,11,3,1024,1024,3,313,5,3,461,59,3,5,1024,3,89,23,3,179,76354906586,3,7,5,3,223,13,3,5,7,3,76464342311,76474430895,3,31]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7680; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_60 {i p b : ℕ} (ix : i/128=60) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7680)
    (cells:=[11,3,47,5,3,23,1024,3,5,25531453790,3,11,239,3,61,7,3,13,5,3,1743290270,29,3,5,76743313550,3,103,153546333193,3,7,13,3,227,5,3,59,7,3,5,521,3,76912531973,17,3,11,373,3,479,5,3,7,23,3,5,154084147931,3,13,7,3,17,197,3,67,5,3,15430558310,11,3,5,13,3,7,271,3,23,61,3,11,5,3,131,77311161409,3,5,1024,3,43,71,3,37,503,3,7,5,3,13,47,3,5,7,3,457,109,3,53,8616932835,3,499,5,3,11,383,3,5,113,3,1024,1024,3,14125502822,7,3,1024,5,3,77749343578,37,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7808; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_61 {i p b : ℕ} (ix : i/128=61) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7808)
    (cells:=[5,43,3,155618380725,11,3,7,51899311694,3,29,5,3,1024,7,3,5,17,3,83,13,3,77988521568,233,3,19504579163,5,3,7,191,3,5,89,3,17,7,3,347,11,3,1024,5,3,199,1024,3,5,163,3,7,293,3,73,39148807182,3,8244197318,5,3,31,13,3,5,23,3,156813506307,956588412,3,156873348880,17,3,7,5,3,37,1024,3,5,7,3,41,107,3,11,53,3,13,5,3,43,31,3,5,157371438216,3,1024,1024,3,29,7,3,113,5,3,1024,11,3,5,1024,3,1024,37,3,7,3586163410,3,11,5,3,401,7,3,5,1024,3,13,73,3,158068821703,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<7936; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_62 {i p b : ℕ} (ix : i/128=62) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=7936)
    (cells:=[3,197,5,3,7,1024,3,5,11,3,1024,7,3,379,317,3,449,5,3,11,1024,3,5,1024,3,7,29,3,47,313,3,1024,5,3,13,101,3,5,158865600445,3,1024,11,3,193,71,3,7,5,3,1024,1024,3,5,7,3,29,83,3,17,149,3,409,5,3,109,1024,3,5,578029687,3,79,23,3,13,7,3,1024,5,3,103,525458307,3,5,8408729697,3,11,13,3,7,467,3,191,5,3,23,7,3,5,397,3,20012606584,1024,3,1024,1024,3,1024,5,3,7,1024,3,5,29,3,31,7,3,11,1024,3,1024,5,3,61,13,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8064; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_63 {i p b : ℕ} (ix : i/128=63) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8064)
    (cells:=[181,3,7,43,3,59,1024,3,101,5,3,83,11,3,5,17,3,80498951699,31,3,277,79,3,7,5,3,173,41,3,5,7,3,17,1024,3,23,13,3,37,5,3,47,89,3,5,11,3,1024,281,3,1024,7,3,1024,5,3,11,61,3,5,40463614266,3,13,1024,3,7,17,3,41,5,3,162073329853,7,3,5,13,3,81096416993,11,3,31,23,3,17,5,3,7,73,3,5,162451965417,3,1024,7,3,1024,81285636626,3,269,5,3,13,227,3,5,1024,3,7,193,3,383,11,3,81455085362,5,3,163,17,3,5,353,3,11,59,3,1024,139,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8192; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_64 {i p b : ℕ} (ix : i/128=64) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8192)
    (cells:=[7,5,3,89,43,3,5,7,3,179,163408257097,3,13,4302075141,3,8605678597,5,3,1024,67,3,5,23,3,1024,13,3,11,7,3,97,5,3,1743526797,54628780740,3,5,1024,3,163985836267,17,3,7,32813213462,3,23,5,3,521,7,3,5,82122657056,3,47,164304585075,3,17,37,3,11,5,3,7,13,3,5,157,3,53,7,3,71,127,3,317,5,3,164762943397,1024,3,5,11,3,7,1024,3,164942162275,9164632158,3,13,5,3,11,499,3,5,1024,3,165181365870,27533612180,3,271,13,3,7,5,3,17,151,3,5,7,3,23,11,3,11824356235,29,3,41399917915,5,3,107,251,3,5,97]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8320; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_65 {i p b : ℕ} (ix : i/128=65) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8320)
    (cells:=[3,13,79,3,37,7,3,109,5,3,31,197,3,5,13,3,1024,41,3,7,11,3,359,5,3,67,7,3,5,83168564254,3,11,23,3,166436342805,8761016047,3,541,5,3,7,31,3,5,59,3,257,7,3,1024,73,3,1024,5,3,23,1024,3,5,1024,3,7,443,3,11,17,3,47,5,3,211,419,3,5,307,3,20909376769,29,3,13,20919272412,3,7,5,3,1024,11,3,5,7,3,43,13,3,1024,131,3,11,5,3,53,23,3,5,20978997327,3,29,103,3,1024,7,3,83995226874,5,3,37,17,3,5,11,3,1024,149,3,7,1024,3,199]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8448; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_66 {i p b : ℕ} (ix : i/128=66) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8448)
    (cells:=[5,3,11,7,3,5,31,3,1024,1024,3,1024,41,3,89,5,3,7,168667741033,3,5,1024,3,373,7,3,1024,168847084352,3,13,5,3,79,47,3,5,29,3,7,17,3,1024,13,3,467,5,3,167,1024,3,5,169325121751,3,41,56461835936,3,17,11,3,7,5,3,169544438790,56521548817,3,5,7,3,11,1024,3,127,569,3,169783373608,5,3,1024,53,3,5,13,3,8945452487,1024,3,1024,7,3,353,5,3,43,59,3,5,1024,3,37,31,3,7,8965481019,3,1024,5,3,13,7,3,5,23,3,85280370111,223,3,421,271,3,251,5,3,7,11,3,5,170819625727,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8576; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_67 {i p b : ℕ} (ix : i/128=67) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8576)
    (cells:=[42714993815,7,3,53,571,3,11,5,3,113,509,3,5,17,3,7,1024,3,13,1024,3,1024,5,3,29,211,3,5,11,3,17,13,3,31,97,3,7,5,3,11,1024,3,5,7,3,1024,47,3,41,487,3,171875552054,5,3,1024,1024,3,5,1024,3,107,11,3,1024,7,3,1024,5,3,86117234876,13,3,5,137,3,23,1024,3,7,1024,3,17,5,3,1024,7,3,5,43153420558,3,1024,1024,3,43,11,3,13,5,3,7,439,3,5,172911295268,3,11,7,3,86505527063,13,3,29,5,3,71,17,3,5,37,3,7,23,3,173309966900,269,3,31,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8704; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_68 {i p b : ℕ} (ix : i/128=68) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8704)
    (cells:=[3,1024,41,3,5,1024,3,13,43,3,11,57876382651,3,7,5,3,23,1024,3,5,7,3,173847866873,401,3,89,157,3,389,5,3,73,11,3,5,83,3,1024,17,3,1024,7,3,11,5,3,13,193,3,5,151,3,1024,29077667342,3,7,43631459946,3,233,5,3,87312612106,7,3,5,11,3,1024,1024,3,29,3884987268,3,59,5,3,7,29157500570,3,5,1024,3,137,7,3,13,175122875323,3,61,5,3,31,79,3,5,1024,3,7,11,3,97,37,3,1024,5,3,17,113,3,5,67,3,1024,87830610840,3,1024,1024,3,7,5,3,443,31,3,5,7,3,175939601391]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8832; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_69 {i p b : ℕ} (ix : i/128=69) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8832)
    (cells:=[29,3,1024,11,3,1024,5,3,283,13,3,5,17,3,11,227,3,1024,7,3,263,5,3,1024,88218966851,3,5,58832520039,3,17,176557404631,3,7,1024,3,13,5,3,41,7,3,5,6096732859,3,331,8039186682,3,11,13,3,176955635657,5,3,7,59011999884,3,5,149,3,1024,7,3,177194984841,17,3,53,5,3,127,11,3,5,23,3,7,89,3,1024,19723977570,3,11,5,3,277,37,3,5,13,3,1024,197,3,113,1024,3,7,5,3,177912197344,463,3,5,7,3,241,229,3,131,383,3,103,5,3,11,17,3,5,29715221895,3,47,41,3,59,7,3,107,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<8960; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_70 {i p b : ℕ} (ix : i/128=70) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=8960)
    (cells:=[1024,1024,3,5,1024,3,1024,11,3,7,43,3,89374548049,5,3,61,7,3,5,1024,3,31,191,3,13,421,3,179047631081,5,3,7,59709376376,3,5,179186969908,3,23,7,3,179286672275,11,3,1024,5,3,17940615565,29,3,5,6903498760,3,7,31,3,17,67,3,1024,5,3,22463282301,1024,3,5,139,3,1024,37,3,293,1024,3,7,5,3,29,13,3,5,7,3,1024,23,3,11,47,3,1024,5,3,1024,1024,3,5,1024,3,43,30073918834,3,1024,7,3,13,5,3,17,11,3,5,251,3,83,59,3,7,13,3,11,5,3,1024,7,3,5,22622586514,3,379,4642206506]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9088; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_71 {i p b : ℕ} (ix : i/128=71) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9088)
    (cells:=[3,569,109,3,47,5,3,7,179,3,5,11,3,13,7,3,1024,31,3,271,5,3,11,23,3,5,13,3,7,1024,3,197,5678157271,3,29,5,3,1024,239,3,5,1024,3,59,11,3,23,12133097187,3,7,5,3,13,1597813937,3,5,7,3,367,1024,3,67,17,3,457,5,3,182394688187,91207419460,3,5,60824876294,3,491,53,3,479,7,3,17,5,3,1024,107,3,5,89,3,11,241,3,7,23,3,182932531029,5,3,43,7,3,5,1024,3,79,13,3,1024,1024,3,137,5,3,7,17,3,5,1024,3,1024,7,3,11,183490558882,3,37,5,3,53]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9216; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_72 {i p b : ℕ} (ix : i/128=72) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9216)
    (cells:=[67,3,5,61,3,7,1024,3,409,397,3,547,5,3,1024,11,3,5,211,3,281,83,3,41,4844738461,3,7,5,3,92094070230,73,3,5,7,3,103,17,3,1024,1024,3,13,5,3,31,4393149443,3,5,11,3,4502589390,29,3,17,7,3,23,5,3,11,15400563132,3,5,503,3,127,521,3,7,1024,3,1024,5,3,1024,7,3,5,1024,3,13,11,3,449,1024,3,139,5,3,7,185403191865,3,5,13,3,1024,7,3,43,307,3,1024,5,3,17,41,3,5,30960558675,3,7,47,3,71,11,3,131,5,3,13,149,3,5,1024,3,11,1024,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9344; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_73 {i p b : ℕ} (ix : i/128=73) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9344)
    (cells:=[93080321173,1024,3,7,5,3,67,1024,3,5,7,3,4905306658,43,3,1024,37,3,41,5,3,239,186598430050,3,5,1024,3,17,1024,3,11,7,3,1024,5,3,93438898762,93448664129,3,5,31,3,97,13,3,7,12472055043,3,73,5,3,229,7,3,5,577,3,1024,61,3,1024,17,3,11,5,3,7,1024,3,5,187554604171,3,1024,7,3,359,311,3,17,5,3,557,13,3,5,11,3,7,1024,3,37,62657721589,3,1024,5,3,11,29,3,5,41,3,31,62737497948,3,94126200512,1024,3,7,5,3,1024,17,3,5,7,3,233,11,3,47137934261,13,3,188610627321,5,3,29,37]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9472; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_74 {i p b : ℕ} (ix : i/128=74) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9472)
    (cells:=[3,5,173,3,1024,31,3,23,7,3,188909374910,5,3,41,43,3,5,113,3,13,107,3,7,11,3,167,5,3,1024,7,3,5,13,3,11,17,3,151,389,3,181,5,3,7,431,3,5,189646525197,3,4991801746,7,3,17,23,3,189805895843,5,3,13,587,3,5,63315355347,3,7,95002741081,3,11,2640018578,3,71,5,3,37,1024,3,5,10569320439,3,67,31717389659,3,439,191,3,7,5,3,103,11,3,5,7,3,593,41,3,13,31,3,11,5,3,17,1024,3,5,347,3,1024,13,3,1024,7,3,101,5,3,373,1024,3,5,11,3,353,13657246204,3,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9600; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_75 {i p b : ℕ} (ix : i/128=75) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9600)
    (cells:=[1024,3,113,5,3,11,7,3,5,17,3,73,10639186967,3,1024,29,3,23,5,3,7,13,3,5,229,3,17,7,3,1024,1024,3,31,5,3,109,31996444862,3,5,53,3,7,192097059933,3,29,96078574509,3,13,5,3,192256452597,257,3,5,1024,3,37,10688739772,3,241,11,3,7,5,3,79,64191895316,3,5,7,3,11,157,3,27533781282,1024,3,17,5,3,96427394422,1024,3,5,71,3,13,1024,3,283,7,3,53,5,3,193153248584,607,3,5,13,3,43,29,3,7,1024,3,61,5,3,197,7,3,5,1024,3,193,1024,3,139,96825869427,3,571,5,3,7,11,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9728; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_76 {i p b : ℕ} (ix : i/128=76) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9728)
    (cells:=[5,1024,3,29,7,3,1024,83,3,11,5,3,1024,5107360773,3,5,43,3,7,1024,3,97114726655,47,3,67,5,3,23,31,3,5,11,3,1024,17,3,13,19454910665,3,7,5,3,11,194667344859,3,5,7,3,269,13,3,17,59,3,503,5,3,97473030573,64988972114,3,5,29,3,1024,11,3,195125529229,7,3,47,5,3,1024,23,3,5,37,3,1024,65128398364,3,7,163,3,179,5,3,195544008278,7,3,5,67,3,97831816027,251,3,23,11,3,421,5,3,7,167,3,5,65307642214,3,11,7,3,59,199,3,13,5,3,1024,1024,3,5,31,3,7,317,3,41,13]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9856; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_77 {i p b : ℕ} (ix : i/128=77) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9856)
    (cells:=[3,463,5,3,98220249490,1024,3,5,17,3,1024,211,3,11,23,3,7,5,3,196739230241,29,3,5,7,3,13,137,3,49229772880,1024,3,1024,5,3,61,11,3,5,13,3,1024,71,3,389,7,3,11,5,3,29,337,3,5,193,3,31,98738172585,3,7,17,3,1024,5,3,13,7,3,5,11,3,347,233,3,307,401,3,17,5,3,7,41,3,5,23,3,113,7,3,99056918735,1024,3,431,5,3,198233472643,61,3,5,1024,3,7,11,3,13,461,3,23,5,3,1024,17,3,5,33102012123,3,563,13,3,1024,89,3,7,5,3,541,79,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<9984; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_78 {i p b : ℕ} (ix : i/128=78) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=9984)
    (cells:=[7,3,157,131,3,37,11,3,29,5,3,199129931115,33191711653,3,5,199209607378,3,11,43,3,31,7,3,1024,5,3,53,13,3,5,199508645417,3,59,17,3,7,67,3,199667963741,5,3,1024,7,3,5,1024,3,23,47,3,11,31,3,13,5,3,7,33341185797,3,5,1024,3,1024,7,3,73,13,3,100133043184,5,3,181,11,3,5,41,3,7,1713584050,3,89,97,3,11,5,3,200624389452,109,3,5,200704094378,3,13,23,3,29,1024,3,7,5,3,17,487,3,5,7,3,201042759417,101,3,1024,1024,3,31,5,3,11,1024,3,5,197,3,201341516779,67120729913,3,1024,7,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10112; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_79 {i p b : ℕ} (ix : i/128=79) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10112)
    (cells:=[100730421064,5,3,13,53,3,5,17,3,1024,11,3,7,1024,3,1024,5,3,201819684495,7,3,5,59,3,17,29,3,79,1024,3,202058633991,5,3,7,23,3,5,1024,3,1024,7,3,13,11,3,1024,5,3,233,5327317143,3,5,101248497231,3,7,13,3,23,17,3,50664201796,5,3,202716057095,101368069529,3,5,613,3,71,41,3,1024,101457865980,3,7,5,3,31,271,3,5,7,3,1024,449,3,11,331,3,203254042100,5,3,101656920107,13,3,5,227,3,37,101726938011,3,1024,7,3,43,5,3,47,11,3,5,29,3,523,569,3,7,149,3,11,5,3,1024,7,3,5,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10240; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_80 {i p b : ℕ} (ix : i/128=80) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10240)
    (cells:=[3,107,89,3,51022918921,13,3,367,5,3,7,204230100340,3,5,11,3,61,7,3,97,43,3,29207081774,5,3,11,1024,3,5,11366248800,3,7,17,3,1024,53,3,1024,5,3,113,103,3,5,13,3,1024,11,3,17,41001709592,3,7,5,3,193,102563567756,3,5,7,3,197,353,3,51321784283,41,3,23,5,3,13,29,3,5,31,3,83,61,3,191,7,3,37,5,3,1024,1024,3,5,102892141784,3,11,167,3,7,433,3,1024,5,3,17,7,3,5,1024,3,41,1024,3,13,206202481969,3,1024,5,3,7,97,3,5,37,3,47,7,3,11,6883672081,3,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10368; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_81 {i p b : ℕ} (ix : i/128=81) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10368)
    (cells:=[5,3,59,206621071263,3,5,17,3,7,103370495231,3,149,131,3,241,5,3,1024,11,3,5,43,3,17,1024,3,71,101,3,7,5,3,2726426992,13,3,5,7,3,207318402538,31,3,1024,1024,3,103719209821,5,3,151,397,3,5,11,3,461,23,3,127,7,3,13,5,3,11,207816503479,3,5,53,3,227,199,3,7,13,3,17,5,3,23,7,3,5,1024,3,409,11,3,208274852417,47,3,157,5,3,7,34735945202,3,5,1024,3,13,7,3,31,37,3,383,5,3,43,17,3,5,13,3,7,83,3,26109165188,11,3,53,5,3,208991830095,23,3,5,293,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10496; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_82 {i p b : ℕ} (ix : i/128=82) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10496)
    (cells:=[11,104565664691,3,167,31,3,7,5,3,13,113,3,5,7,3,131,173,3,23,1024,3,104764973101,5,3,52397658236,541,3,5,52417612810,3,209709079000,17,3,11,7,3,1024,5,3,1024,71,3,5,557,3,105004179276,1024,3,7,105043942768,3,59,5,3,97,7,3,5,1024,3,67,13,3,210366412252,23,3,11,5,3,7,151,3,5,223,3,349,7,3,210665323287,251,3,277,5,3,337,37,3,5,11,3,7,1024,3,105482141855,103,3,41,5,3,11,13,3,5,1024,3,29,379,3,43,35213841643,3,7,5,3,211382746179,211402588201,3,5,7,3,109,11,3,113,347,3,13,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10624; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_83 {i p b : ℕ} (ix : i/128=83) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10624)
    (cells:=[3,163,233,3,5,17,3,211801171652,13238821065,3,491,7,3,619,5,3,1024,281,3,5,601,3,17,43,3,7,11,3,23,5,3,31,7,3,5,29,3,11,1024,3,311,59,3,212518266484,5,3,7,1024,3,5,13,3,1024,7,3,257,17,3,212816939038,5,3,173,31,3,5,1024,3,7,37,3,11,197,3,17,5,3,13,191,3,5,137,3,73,179,3,373,10160971023,3,7,5,3,41,11,3,5,7,3,23,71204779513,3,59,109,3,11,5,3,1024,17,3,5,1024,3,53473493647,47,3,13,7,3,214012604016,5,3,107036284597,29,3,5,11,3,214191848732]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10752; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_84 {i p b : ℕ} (ix : i/128=84) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10752)
    (cells:=[13,3,7,214271444110,3,67,5,3,11,7,3,5,1024,3,37,23,3,229,214570313915,3,107305216146,5,3,7,43,3,5,31,3,499,7,3,47,35811860214,3,293,5,3,23,13,3,5,71682878963,3,7,41,3,17,2241670065,3,1024,5,3,53,71762464210,3,5,431,3,1024,1024,3,83,11,3,7,5,3,71,283,3,5,7,3,11,467,3,1024,13,3,107902960187,5,3,199,23,3,5,215944889750,3,31,59,3,1024,7,3,216104198791,5,3,17,216184175183,3,5,277,3,13,108152079883,3,7,409,3,29,5,3,89,7,3,5,13,3,439,31,3,193,216662283565,3,37,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<10880; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_85 {i p b : ℕ} (ix : i/128=85) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=10880)
    (cells:=[7,11,3,5,17,3,179,7,3,1024,227,3,11,5,3,13,1024,3,5,103,3,7,1024,3,131,23,3,217299624393,5,3,607,53,3,5,11,3,108739736735,337,3,217538691166,29,3,7,5,3,11,217678154280,3,5,7,3,217777924558,127,3,13,17,3,1024,5,3,1024,1024,3,5,1024,3,218076835677,11,3,29,7,3,17,5,3,43651438592,263,3,5,218335718239,3,41,71,3,7,31,3,347,5,3,139,7,3,5,23,3,54668754917,1024,3,1024,11,3,218793780189,5,3,7,13,3,5,1024,3,11,7,3,1024,1024,3,23,5,3,167,101,3,5,271,3,7,29]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11008; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_86 {i p b : ℕ} (ix : i/128=86) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11008)
    (cells:=[3,1024,43870658568,3,13,5,3,223,647,3,5,47,3,1024,1024,3,11,13,3,7,5,3,219750428042,173,3,5,7,3,29,17,3,1024,443,3,219989429862,5,3,22005124234,11,3,5,61,3,13,109,3,17,7,3,11,5,3,487,110183929136,3,5,13,3,23,193,3,7,53,3,1024,5,3,1024,7,3,5,11,3,1024,373,3,41,157,3,79,5,3,7,1024,3,5,29,3,557,7,3,37,36857859682,3,101,5,3,17,221264320644,3,5,139,3,7,11,3,163,137,3,227,5,3,31,269,3,5,149,3,221663044279,1024,3,13,577,3,7,5,3,23]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11136; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_87 {i p b : ℕ} (ix : i/128=87) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11136)
    (cells:=[37,3,5,7,3,181,13,3,73,11,3,1024,5,3,641,31,3,5,1024,3,11,307,3,67,7,3,222379932488,5,3,22244057857,41,3,5,37086980101,3,61,37096642891,3,7,71,3,111339434161,5,3,1024,7,3,5,113,3,127,1024,3,11,17,3,1024,5,3,7,59,3,5,1024,3,433,7,3,23,1024,3,13,5,3,29,11,3,5,359,3,7,73,3,263,13,3,11,5,3,111817533254,67,3,5,53,3,223754810142,61,3,1024,44767238264,3,7,5,3,431,17,3,5,7,3,13,37,3,43,23,3,137,5,3,11,619,3,5,13,3,1024,224372468095,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11264; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_88 {i p b : ℕ} (ix : i/128=88) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11264)
    (cells:=[1024,7,3,224471908688,5,3,109,1024,3,5,191,3,1024,11,3,7,499,3,53,5,3,13,7,3,5,41,3,503,17,3,467,225029812037,3,29,5,3,7,47,3,5,101,3,31,7,3,17,11,3,83,5,3,1024,37574909335,3,5,23,3,7,181,3,13,233,3,225667443443,5,3,41,1024,3,5,167,3,56461672882,13,3,1024,1024,3,7,5,3,593,241,3,5,7,3,1024,1024,3,11,29,3,1024,5,3,17,353,3,5,1024,3,521,1024,3,1024,7,3,1024,5,3,226623553898,11,3,5,109,3,1024,617,3,7,1024,3,11,5,3,269,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11392; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_89 {i p b : ℕ} (ix : i/128=89) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11392)
    (cells:=[3,5,17,3,1024,1024,3,31,1024,3,13,5,3,7,227241199150,3,5,11,3,17,7,3,103,13,3,113730160147,5,3,11,43,3,5,1024,3,7,67,3,1024,31,3,37,5,3,571,73,3,5,227898819781,3,13,11,3,1024,17,3,7,5,3,257,1024,3,5,7,3,229,23,3,71,1024,3,17,5,3,191,10877976906,3,5,37,3,29,151,3,1024,7,3,114327949131,5,3,13,114367944645,3,5,281,3,11,1024,3,7,228914739845,3,31,5,3,45802856651,7,3,5,229094295080,3,167,229154101272,3,57298412157,22921775689,3,43,5,3,7,421,3,5,1024,3,239,7,3,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11520; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_90 {i p b : ℕ} (ix : i/128=90) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11520)
    (cells:=[97,3,1024,5,3,107,23,3,5,29,3,7,13,3,401,41,3,61,5,3,1024,11,3,5,449,3,271,17,3,23,43,3,7,5,3,211,157,3,5,7,3,67,1024,3,17,1024,3,127,5,3,230508688804,13,3,5,11,3,41,89,3,251,7,3,73,5,3,11,1024,3,5,38481403950,3,337,2062262732,3,7,23,3,13,5,3,53,7,3,5,1024,3,231225870237,11,3,59,13,3,1024,5,3,7,29,3,5,1024,3,383,7,3,1024,1024,3,231644150704,5,3,47,199,3,5,433,3,7,38640737085,3,1024,11,3,1024,5,3,29,193,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11648; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_91 {i p b : ℕ} (ix : i/128=91) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11648)
    (cells:=[5,13,3,11,29018129578,3,37,73,3,7,5,3,563,347,3,5,7,3,17,1024,3,1024,283,3,71,5,3,13,116310360144,3,5,43,3,1024,25860015775,3,11,7,3,23,5,3,131,37,3,5,127,3,1024,1024,3,7,17,3,233138498325,5,3,116599319732,7,3,5,31,3,1024,599,3,13,367,3,11,5,3,7,313,3,5,47,3,1024,7,3,1024,12300058063,3,29,5,3,1024,14613700564,3,5,11,3,7,1024,3,116987885137,263,3,1024,5,3,11,17,3,5,317,3,23,1024,3,53,39049213527,3,7,5,3,37,13,3,5,7,3,31,11,3,151,234592730408]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11776; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_92 {i p b : ℕ} (ix : i/128=92) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11776)
    (cells:=[3,1024,5,3,1544104074,41,3,5,58693228280,3,59,234831866090,3,1024,7,3,13,5,3,523,1024,3,5,235071250903,3,73,17,3,7,11,3,1024,5,3,83,7,3,5,71,3,11,271,3,17,9812438452,3,41,5,3,7,103,3,5,67,3,13,7,3,235768363505,167,3,117914153878,5,3,58972081810,117954022827,3,5,13,3,7,191,3,11,1024,3,1024,5,3,331,19684237594,3,5,1024,3,4074374741,113,3,31,47,3,7,5,3,13,11,3,5,7,3,37,29,3,587,29585985960,3,11,5,3,71,236804534163,3,5,1024,3,1024,1024,3,23,7,3,1024,5,3,23708417265,1024,3,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<11904; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_93 {i p b : ℕ} (ix : i/128=93) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=11904)
    (cells:=[11,3,29,223,3,7,101,3,47,5,3,11,7,3,5,1024,3,17,13,3,109,151,3,1024,5,3,7,1024,3,5,569,3,118900516945,7,3,237860366250,23,3,1024,5,3,41,1024,3,5,1024,3,7,131,3,238159324235,17,3,31,5,3,179,13,3,5,29,3,238398097776,349,3,1024,11,3,7,5,3,113,83,3,5,7,3,11,1024,3,119378727209,1024,3,13,5,3,673,1024,3,5,239,3,29874767263,643,3,617,7,3,167,5,3,97,17,3,5,23,3,101,3148888910,3,7,1024,3,1024,5,3,73,7,3,5,37,3,13,41,3,199,67,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12032; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_94 {i p b : ℕ} (ix : i/128=94) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12032)
    (cells:=[23,5,3,7,11,3,5,13,3,1024,7,3,1024,1024,3,11,5,3,31,29,3,5,1024,3,7,17,3,83,107,3,240310987960,5,3,13,43,3,5,11,3,317,631,3,17,127,3,7,5,3,11,31,3,5,7,3,61,409,3,120424579358,6176172462,3,163,5,3,48193621232,1024,3,5,241048042335,3,23,11,3,13,7,3,491,5,3,1024,89,3,5,79,3,6352499355,13,3,7,1024,3,241506158582,5,3,17,7,3,5,1024,3,1024,1024,3,1024,11,3,1024,5,3,7,1024,3,5,541,3,11,7,3,509,41,3,43,5,3,1024,13,3,5,17]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12160; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_95 {i p b : ℕ} (ix : i/128=95) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12160)
    (cells:=[3,7,419,3,67,40394104766,3,29,5,3,23,1024,3,5,31,3,17,4492824701,3,11,4333360155,3,7,5,3,1024,331,3,5,7,3,41,1024,3,47,13,3,269,5,3,89,11,3,5,20261732928,3,1024,81066653923,3,37,7,3,11,5,3,1024,23,3,5,311,3,13,12815944237,3,7,29,3,17,5,3,1024,7,3,5,11,3,31,121898892430,3,23,71,3,173,5,3,7,37,3,5,1024,3,109,7,3,29,163,3,233,5,3,13,17,3,5,122167713080,3,7,11,3,61,1024,3,79,5,3,244554175402,683,3,5,1024,3,43,1024,3,577,23,3,7]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12288; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_96 {i p b : ℕ} (ix : i/128=96) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12288)
    (cells:=[5,3,1024,359,3,5,7,3,97,503,3,13,11,3,1024,5,3,1024,1024,3,5,1024,3,11,13,3,41,7,3,59,5,3,37,40912127842,3,5,43,3,1024,281,3,7,61,3,251,5,3,47,7,3,5,1024,3,29,53,3,11,131,3,313,5,3,7,13,3,5,23,3,123084309197,7,3,271,31,3,1024,5,3,67,11,3,5,443,3,7,229,3,1024,82182577622,3,11,5,3,17,107,3,5,41121161206,3,1024,383,3,1024,13,3,7,5,3,53,41,3,5,7,3,397,247084742556,3,1024,123572342255,3,1024,5,3,11,247263753376,3,5,17,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12416; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_97 {i p b : ℕ} (ix : i/128=97) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12416)
    (cells:=[13,123691846874,3,247423389187,7,3,31,5,3,1024,1024,3,5,13,3,17,11,3,7,59,3,41,5,3,1024,7,3,5,103,3,23,601,3,367,248040747210,3,61,5,3,7,127,3,5,82740263664,3,1024,7,3,1024,11,3,89,5,3,248439554571,1024,3,5,83,3,7,1024,3,227,24864304482,3,17,5,3,137,29,3,5,1024,3,1024,23,3,13,248937648294,3,7,5,3,433,53,3,5,7,3,1024,13,3,11,1024,3,1024,5,3,23,17,3,5,41,3,487,1024,3,71,7,3,249574806684,5,3,311,11,3,5,263,3,1024,1024,3,7,113,3,11,5]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12544; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_98 {i p b : ℕ} (ix : i/128=98) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12544)
    (cells:=[3,293,7,3,5,1024,3,241,1024,3,53,1024,3,83,5,3,7,23,3,5,11,3,67,7,3,1024,47,3,13,5,3,11,223,3,5,37,3,7,43,3,17,13,3,97,5,3,250830063074,1024,3,5,1024,3,653,11,3,1024,1024,3,7,5,3,1024,251148684556,3,5,7,3,13,59,3,149,1024,3,47,5,3,31428471901,41908190349,3,5,13,3,199,439,3,6621582231,7,3,62916889275,5,3,17,1024,3,5,31,3,11,41,3,7,89,3,251965915645,5,3,13,7,3,5,1024,3,1024,42027458393,3,252204749054,29,3,252264400623,5,3,7,71,3,5,17,3,59]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12672; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_99 {i p b : ℕ} (ix : i/128=99) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12672)
    (cells:=[7,3,11,1024,3,73,5,3,151,42107501112,3,5,97,3,7,109,3,13,37,3,307,5,3,467,11,3,5,23,3,31,13,3,1024,317,3,7,5,3,127,43,3,5,7,3,6666939548,126680494019,3,36200348049,17,3,23,5,3,126759914839,461,3,5,11,3,607,31,3,89,7,3,17,5,3,11,13,3,5,163,3,79,29,3,7,73,3,63514610790,5,3,254117533887,7,3,5,137,3,173,11,3,37,41,3,13,5,3,7,17,3,5,421,3,29,7,3,254595553157,13,3,254655327053,5,3,1024,563,3,5,59,3,7,241,3,31,11,3,43,5,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12800; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_100 {i p b : ℕ} (ix : i/128=100) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12800)
    (cells:=[503,37,3,5,193,3,11,1024,3,107,1024,3,7,5,3,1024,367,3,5,7,3,211,17,3,15968342685,31,3,1024,5,3,229,151,3,5,29,3,1024,23,3,11,7,3,255850848200,5,3,13,255930396358,3,5,1024,3,256029940737,47,3,7,179,3,128074868645,5,3,23,7,3,5,1024,3,256328842953,85449934635,3,131,85469616403,3,11,5,3,7,379,3,5,61,3,11665255168,7,3,13,1024,3,31,5,3,17,449,3,5,11,3,7,13,3,47,1024,3,1024,5,3,11,23,3,5,42864584027,3,1024,37,3,257285220319,28589493715,3,7,5,3,101,29,3,5,7,3,43,11]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<12928; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_101 {i p b : ℕ} (ix : i/128=101) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=12928)
    (cells:=[3,23,1024,3,128822125993,5,3,257703314773,13,3,5,337,3,17,1024,3,1024,7,3,373,5,3,29,181,3,5,1024,3,233,647,3,7,11,3,13,5,3,1024,7,3,5,43,3,11,83,3,19883511802,13,3,1024,5,3,7,1024,3,5,1024,3,37,7,3,129389778359,258799243260,3,17,5,3,1024,479,3,5,307,3,7,1024,3,11,14394642277,3,1024,5,3,259197724129,31,3,5,13,3,1024,1024,3,259377142218,1024,3,7,5,3,59,11,3,5,7,3,53,211,3,179,67,3,11,5,3,13,14434402920,3,5,23,3,259914779675,1024,3,347,7,3,41,5,3,43]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13056; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_102 {i p b : ℕ} (ix : i/128=102) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13056)
    (cells:=[547,3,5,11,3,149,61,3,7,43382621713,3,23,5,3,11,7,3,5,1024,3,1024,17,3,13,43432243071,3,260632087861,5,3,7,28968013092,3,5,491,3,127,7,3,17,29,3,37,5,3,1024,1024,3,5,31,3,7,173,3,130585017670,1024,3,130614991312,5,3,73,1024,3,5,1024,3,1024,101,3,29,11,3,7,5,3,107,13,3,5,7,3,11,53,3,1024,1024,3,261827762209,5,3,17,261907248690,3,5,1024,3,262006774893,311,3,1024,7,3,13,5,3,227,1024,3,5,1024,3,31,509,3,7,13,3,271,5,3,41,7,3,5,17,3,47,23,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13184; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_103 {i p b : ℕ} (ix : i/128=103) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13184)
    (cells:=[43,2918781042,3,461,5,3,7,11,3,5,139,3,13,7,3,1024,2739582928,3,11,5,3,23,87700900811,3,5,13,3,7,1024,3,1024,263281842969,3,1024,5,3,79,83,3,5,11,3,541,43,3,131780802257,17,3,7,5,3,11,67,3,5,7,3,131900101508,263819728159,3,613,37,3,17,5,3,13893701172,23,3,5,88019978435,3,197,11,3,31,7,3,131,5,3,457,97,3,5,29,3,264397440927,331420719,3,7,47,3,1024,5,3,173,7,3,5,151,3,313,13,3,1024,11,3,66204315940,5,3,7,53,3,5,79,3,11,7,3,83,71,3,137,5,3,24107201407,88398199881]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13312; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_104 {i p b : ℕ} (ix : i/128=104) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13312)
    (cells:=[3,5,409,3,7,44219142602,3,37,23,3,47,5,3,132736781137,13,3,5,691,3,113,17,3,11,37953306513,3,7,5,3,449,109,3,5,7,3,1024,277,3,17,1024,3,13,5,3,14003916219,11,3,5,149,3,1024,1024,3,523,7,3,11,5,3,67,103,3,5,1024,3,71,1024,3,7,41,3,266609180776,5,3,29,7,3,5,11,3,13,179,3,1024,431,3,1024,5,3,7,133494034584,3,5,13,3,1024,7,3,133573863183,267166788913,3,23,5,3,709,47,3,5,419,3,7,11,3,293,101,3,267505519450,5,3,13,1024,3,5,17,3,1024,67,3,267744890462]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13440; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_105 {i p b : ℕ} (ix : i/128=105) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13440)
    (cells:=[157,3,7,5,3,31,89,3,5,7,3,17,1024,3,211,11,3,79,5,3,97,1024,3,5,1024,3,11,37,3,13,7,3,29,5,3,479,31,3,5,353,3,23,13,3,7,17,3,1024,5,3,1024,7,3,5,181,3,19205744686,59,3,11,1024,3,17,5,3,7,257,3,5,599,3,269179102961,7,3,269239038016,241,3,229,5,3,7088660974,11,3,5,131,3,7,23,3,1024,29,3,11,5,3,89,17,3,5,401,3,37,269,3,41,473507842,3,7,5,3,23,14209403412,3,5,7,3,59,47,3,29,13,3,1024,5,3,11,191,3]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13568; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_106 {i p b : ℕ} (ix : i/128=106) (_lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13568)
    (cells:=[5,31,3,43,518331783,3,270434539326,7,3,103,5,3,491,137,3,5,11276446697,3,13,11,3,7,1024,3,397,5,3,270852929391,7,3,5,13,3,135486464872,270992169598,3,17,135526107329,3,271091931352,5,3,7,61,3,5,43,3,421,7,3,23,11,3,14283733500,5,3,13,41,3,5,467,3,7,1024,3,379,1024,3,1024,5,3,587,569,3,5,135914760849,3,29,1024,3,601,197,3,7,5,3,17,317,3,5,7,3,1024,31,3,11,23,3,41,5,3,113,272366738432,3,5,59,3,509,13,3,1024,7,3,1024,5,3,1024,11,3,5,17,3,223,136392532758,3,7,272845125115]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13696; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_chunk_107 {i p b : ℕ} (ix : i/128=107) (lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) :
    jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  apply nineteen_interval (start:=13696)
    (cells:=[3,11,5,3,43,7,3,5,29,3,17,30342884866,3,136561864317,1024,3,349,5,3,7,13,3,5,11,3,1024,7,3,31,1024,3,359,5,3,11,71,3,5,23,3,7,151,3,273721766449,17,3,13,5,3,47,229,3,5,41,3,97,11,3,157,13,3,7,5,3,27414333604,1024,3,5,7,3,1024,541,3,193,1024,3,67,5,3,499,1024,3,5,1024,3,13,1024,3,137309015390,7,3,1024,5,3,41,17,3,5,13,3,11,1024]) _ seventeen_smooth_powMod_eq
  · decide +kernel
  · omega
  · change i<13798; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12288 in
set_option maxHeartbeats 10000000 in
private theorem nineteen_catalog {i p b : ℕ} (lim : i<13798)
    (pq : (38*i+1).Prime) (base : p+1=2^b) (idx : b%6846840=1)
    (mult : 38*i+1∣p^19+524288) (nd : ¬38*i+1∣p+2) : jacobiSym (-391035178779996329449236816443734232647452603072641795948876077150975820130862595441922486498941071882816867824315388573225175768680893108421376378983372299943455330892950147235348631773604592604678447332237143113469720098242103281420055644856037785161736735425856157954560153850544888628977603398339456970530202860920630614947175033832797221034039435595695465592692344306825029207341588734266880888310448854670323096165600769522378433915480506702 : ℤ) (38*i+1)=1 := by
  have range : i/128<108 := by omega
  interval_cases h : i/128
  · exact nineteen_chunk_0 h lim pq base idx mult nd
  · exact nineteen_chunk_1 h lim pq base idx mult nd
  · exact nineteen_chunk_2 h lim pq base idx mult nd
  · exact nineteen_chunk_3 h lim pq base idx mult nd
  · exact nineteen_chunk_4 h lim pq base idx mult nd
  · exact nineteen_chunk_5 h lim pq base idx mult nd
  · exact nineteen_chunk_6 h lim pq base idx mult nd
  · exact nineteen_chunk_7 h lim pq base idx mult nd
  · exact nineteen_chunk_8 h lim pq base idx mult nd
  · exact nineteen_chunk_9 h lim pq base idx mult nd
  · exact nineteen_chunk_10 h lim pq base idx mult nd
  · exact nineteen_chunk_11 h lim pq base idx mult nd
  · exact nineteen_chunk_12 h lim pq base idx mult nd
  · exact nineteen_chunk_13 h lim pq base idx mult nd
  · exact nineteen_chunk_14 h lim pq base idx mult nd
  · exact nineteen_chunk_15 h lim pq base idx mult nd
  · exact nineteen_chunk_16 h lim pq base idx mult nd
  · exact nineteen_chunk_17 h lim pq base idx mult nd
  · exact nineteen_chunk_18 h lim pq base idx mult nd
  · exact nineteen_chunk_19 h lim pq base idx mult nd
  · exact nineteen_chunk_20 h lim pq base idx mult nd
  · exact nineteen_chunk_21 h lim pq base idx mult nd
  · exact nineteen_chunk_22 h lim pq base idx mult nd
  · exact nineteen_chunk_23 h lim pq base idx mult nd
  · exact nineteen_chunk_24 h lim pq base idx mult nd
  · exact nineteen_chunk_25 h lim pq base idx mult nd
  · exact nineteen_chunk_26 h lim pq base idx mult nd
  · exact nineteen_chunk_27 h lim pq base idx mult nd
  · exact nineteen_chunk_28 h lim pq base idx mult nd
  · exact nineteen_chunk_29 h lim pq base idx mult nd
  · exact nineteen_chunk_30 h lim pq base idx mult nd
  · exact nineteen_chunk_31 h lim pq base idx mult nd
  · exact nineteen_chunk_32 h lim pq base idx mult nd
  · exact nineteen_chunk_33 h lim pq base idx mult nd
  · exact nineteen_chunk_34 h lim pq base idx mult nd
  · exact nineteen_chunk_35 h lim pq base idx mult nd
  · exact nineteen_chunk_36 h lim pq base idx mult nd
  · exact nineteen_chunk_37 h lim pq base idx mult nd
  · exact nineteen_chunk_38 h lim pq base idx mult nd
  · exact nineteen_chunk_39 h lim pq base idx mult nd
  · exact nineteen_chunk_40 h lim pq base idx mult nd
  · exact nineteen_chunk_41 h lim pq base idx mult nd
  · exact nineteen_chunk_42 h lim pq base idx mult nd
  · exact nineteen_chunk_43 h lim pq base idx mult nd
  · exact nineteen_chunk_44 h lim pq base idx mult nd
  · exact nineteen_chunk_45 h lim pq base idx mult nd
  · exact nineteen_chunk_46 h lim pq base idx mult nd
  · exact nineteen_chunk_47 h lim pq base idx mult nd
  · exact nineteen_chunk_48 h lim pq base idx mult nd
  · exact nineteen_chunk_49 h lim pq base idx mult nd
  · exact nineteen_chunk_50 h lim pq base idx mult nd
  · exact nineteen_chunk_51 h lim pq base idx mult nd
  · exact nineteen_chunk_52 h lim pq base idx mult nd
  · exact nineteen_chunk_53 h lim pq base idx mult nd
  · exact nineteen_chunk_54 h lim pq base idx mult nd
  · exact nineteen_chunk_55 h lim pq base idx mult nd
  · exact nineteen_chunk_56 h lim pq base idx mult nd
  · exact nineteen_chunk_57 h lim pq base idx mult nd
  · exact nineteen_chunk_58 h lim pq base idx mult nd
  · exact nineteen_chunk_59 h lim pq base idx mult nd
  · exact nineteen_chunk_60 h lim pq base idx mult nd
  · exact nineteen_chunk_61 h lim pq base idx mult nd
  · exact nineteen_chunk_62 h lim pq base idx mult nd
  · exact nineteen_chunk_63 h lim pq base idx mult nd
  · exact nineteen_chunk_64 h lim pq base idx mult nd
  · exact nineteen_chunk_65 h lim pq base idx mult nd
  · exact nineteen_chunk_66 h lim pq base idx mult nd
  · exact nineteen_chunk_67 h lim pq base idx mult nd
  · exact nineteen_chunk_68 h lim pq base idx mult nd
  · exact nineteen_chunk_69 h lim pq base idx mult nd
  · exact nineteen_chunk_70 h lim pq base idx mult nd
  · exact nineteen_chunk_71 h lim pq base idx mult nd
  · exact nineteen_chunk_72 h lim pq base idx mult nd
  · exact nineteen_chunk_73 h lim pq base idx mult nd
  · exact nineteen_chunk_74 h lim pq base idx mult nd
  · exact nineteen_chunk_75 h lim pq base idx mult nd
  · exact nineteen_chunk_76 h lim pq base idx mult nd
  · exact nineteen_chunk_77 h lim pq base idx mult nd
  · exact nineteen_chunk_78 h lim pq base idx mult nd
  · exact nineteen_chunk_79 h lim pq base idx mult nd
  · exact nineteen_chunk_80 h lim pq base idx mult nd
  · exact nineteen_chunk_81 h lim pq base idx mult nd
  · exact nineteen_chunk_82 h lim pq base idx mult nd
  · exact nineteen_chunk_83 h lim pq base idx mult nd
  · exact nineteen_chunk_84 h lim pq base idx mult nd
  · exact nineteen_chunk_85 h lim pq base idx mult nd
  · exact nineteen_chunk_86 h lim pq base idx mult nd
  · exact nineteen_chunk_87 h lim pq base idx mult nd
  · exact nineteen_chunk_88 h lim pq base idx mult nd
  · exact nineteen_chunk_89 h lim pq base idx mult nd
  · exact nineteen_chunk_90 h lim pq base idx mult nd
  · exact nineteen_chunk_91 h lim pq base idx mult nd
  · exact nineteen_chunk_92 h lim pq base idx mult nd
  · exact nineteen_chunk_93 h lim pq base idx mult nd
  · exact nineteen_chunk_94 h lim pq base idx mult nd
  · exact nineteen_chunk_95 h lim pq base idx mult nd
  · exact nineteen_chunk_96 h lim pq base idx mult nd
  · exact nineteen_chunk_97 h lim pq base idx mult nd
  · exact nineteen_chunk_98 h lim pq base idx mult nd
  · exact nineteen_chunk_99 h lim pq base idx mult nd
  · exact nineteen_chunk_100 h lim pq base idx mult nd
  · exact nineteen_chunk_101 h lim pq base idx mult nd
  · exact nineteen_chunk_102 h lim pq base idx mult nd
  · exact nineteen_chunk_103 h lim pq base idx mult nd
  · exact nineteen_chunk_104 h lim pq base idx mult nd
  · exact nineteen_chunk_105 h lim pq base idx mult nd
  · exact nineteen_chunk_106 h lim pq base idx mult nd
  · exact nineteen_chunk_107 h lim pq base idx mult nd

private theorem nineteen_last_order {q p : ℕ} (pq : q.Prime) (q2 : q≠2)
    (d : q ∣ p^19+524288) (nd : ¬q ∣ p+2) : 19 ∣ q-1 := by
  let _ : Fact q.Prime := ⟨pq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    exact q2 eq
  let t : ZMod q := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr d
  push_cast at zero
  have eq : t^19=1 := by
    dsimp [t]
    rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]
    linear_combination -zero
  have t1 : t≠1 := by
    intro h
    dsimp [t] at h
    rw [div_eq_iff h2] at h
    apply nd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    linear_combination -h
  have t0 : t≠0 := by rintro h; rw [h] at eq; simp at eq
  have ord : orderOf t = 19 := ((Nat.dvd_prime (by decide : Nat.Prime 19)).mp
    (orderOf_dvd_of_pow_eq_one eq)).resolve_left (fun h => t1 (orderOf_eq_one_iff.mp h))
  exact ord ▸ ZMod.orderOf_dvd_card_sub_one t0


private theorem nineteen_scaled {p F m k : ℕ} (fac : p^19+524288=(p+2)*F)
    (h : Nat.ModEq m p k) : Nat.ModEq m ((k+2)*F) (k^19+524288) := by
  calc
    (k+2)*F ≡ (p+2)*F [MOD m] := ((h.add_right 2).mul_right F).symm
    _ = p^19+524288 := fac.symm
    _ ≡ k^19+524288 [MOD m] := (h.pow 19).add_right _



private theorem nineteen_common_prime {p F q : ℕ} (fac : p^19+524288=(p+2)*F) (fpos : F≠0)
    (qp : q.Prime) (qlo : 2 < q) (left : q∣p+2) (right : q∣F) : q=19 := by
  let _ : Fact q.Prime := ⟨qp⟩
  have qnp : ¬q∣p := by intro dp; have := Nat.le_of_dvd (by decide : 0<2) ((Nat.dvd_add_iff_right dp).mpr left); omega
  have val := padicValNat.pow_add_pow (x:=p) (y:=2) (qp.odd_of_ne_two (by omega)) left qnp (by decide : Odd 19)
  change padicValNat q (p^19+524288)=_ at val
  rw [fac,padicValNat.mul (by omega) fpos] at val
  have nz := (dvd_iff_padicValNat_ne_zero fpos).mp right
  have l : q∣19 := (dvd_iff_padicValNat_ne_zero (by decide : (19:ℕ)≠0)).mpr (by omega)
  exact (Nat.prime_dvd_prime_iff_eq qp (by decide)).mp l

private theorem nineteen_cofactor_negative {p b F D : ℕ}
    (base : p+1=2^b) (hb : 524289 < b) (idx : b%6846840=1) (fac : p^19+524288=(p+2)*F)
    (per : Nat.ModEq (3*D) (2^6846840) 1) (cop : Nat.Coprime 8 D) (big : 174763 < D)
    (a8 : Nat.ModEq 8 7 (4*D+174763)) (ad : Nat.ModEq D 174763 (4*D+174763))
    (jac : jacobiSym (-(2*(D:ℤ))) (4*D+174763) = -1) :
    jacobiSym (-(2*(D:ℤ))) F = -1 := by
  have div8 : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have f8 : Nat.ModEq 8 F 7 := by
    calc
      F = 1*F := (one_mul _).symm
      _ ≡ (7+2)*F [MOD 8] := (show Nat.ModEq 8 1 (7+2) by decide).mul_right _
      _ ≡ 7^19+524288 [MOD 8] := nineteen_scaled fac p8
      _ ≡ 7 [MOD 8] := by decide
  have fv : F%8=7 := f8
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have pred : Nat.ModEq (3*D) p 1 := by
    have z := seventeen_compact_last_cycle (b:=b) per
    rw [idx,pow_one,←base] at z
    exact Nat.ModEq.add_right_cancel' 1 z
  have fd : Nat.ModEq D F 174763 := Nat.ModEq.mul_left_cancel' (by decide : (3:ℕ)≠0) (nineteen_scaled fac pred)
  have total : Nat.ModEq (8*D) F (4*D+174763) := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨f8.trans a8,fd.trans ad⟩
  rw [jacobiSym.mod_right _ fo]
  have abs : 4*(-(2*(D:ℤ))).natAbs=8*D := by simp; omega
  rw [abs]
  have rem : F%(8*D)=4*D+174763 := Eq.trans total (Nat.mod_eq_of_lt (by omega))
  rwa [rem]


private theorem nineteen_last_abstract {p b F : ℕ} {A : ℤ}
    (pp : p.Prime) (base : p+1=2^b) (hb : 524289 < b) (idx : b%6846840=1)
    (fac : p^19+524288=(p+2)*F) (minus : jacobiSym A F = -1)
    (catalog : ∀ {i : ℕ}, i<13798 → (38*i+1).Prime → 38*i+1∣p^19+524288 → ¬38*i+1∣p+2 →
      jacobiSym A (38*i+1)=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^19+d ∧ s∣p^19+d := by
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have eight : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have z := nineteen_scaled fac p8
  change (9*F)%8=7 at z
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have fpos : F≠0 := by omega
  obtain ⟨s,ps,ds,minusS⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one minus
  have slo : 2 < s := lt_of_le_of_ne ps.two_le (Ne.symm (fo.ne_two_of_dvd_nat ds))
  obtain ⟨q,pq,qhi,qleft⟩ := seventeen_compact_last_left pb hb (show 3 < b by omega)
  have dx : q∣p+2 := by convert qleft using 1; omega
  have mult : s∣p^19+524288 := fac ▸ dvd_mul_of_dvd_right ds _
  have nd : ¬s∣p+2 := by
    intro h
    have es := nineteen_common_prime fac fpos ps slo h ds
    have dL : s∣2^b+1 := by convert h using 1; omega
    have eq3 := seventeen_compact_last_fifth pb (pb.odd_of_ne_two (by omega)) ps dL (by omega)
    omega
  by_cases large : 524289 < s
  · have ne : q≠s := by rintro rfl; have := nineteen_common_prime fac fpos pq (by omega) dx ds; omega
    exact ⟨524288,q,s,pq,ps,ne,qhi,large,fac ▸ dvd_mul_of_dvd_left dx _,mult⟩
  exfalso
  obtain ⟨j,hj⟩ := nineteen_last_order ps (by omega) mult nd
  obtain ⟨u,hu⟩ := ps.odd_of_ne_two (by omega)
  let i := (s-1)/38
  have es : 38*i+1=s := by dsimp [i]; omega
  have bd : i<13798 := by dsimp [i]; omega
  have posS : jacobiSym A s=1 := by
    rw [←es]
    exact catalog bd (es ▸ ps) (es ▸ mult) (es ▸ nd)
  omega

set_option maxRecDepth 32768 in
private theorem nineteen_discriminant_period : Nat.ModEq (3*195517589389998164724618408221867116323726301536320897974438038575487910065431297720961243249470535941408433912157694286612587884340446554210688189491686149971727665446475073617674315886802296302339223666118571556734860049121051640710027822428018892580868367712928078977280076925272444314488801699169728485265101430460315307473587516916398610517019717797847732796346172153412514603670794367133440444155224427335161548082800384761189216957740253351) (2^6846840) 1 := by
  change 2^6846840%(3*195517589389998164724618408221867116323726301536320897974438038575487910065431297720961243249470535941408433912157694286612587884340446554210688189491686149971727665446475073617674315886802296302339223666118571556734860049121051640710027822428018892580868367712928078977280076925272444314488801699169728485265101430460315307473587516916398610517019717797847732796346172153412514603670794367133440444155224427335161548082800384761189216957740253351)=1%(3*195517589389998164724618408221867116323726301536320897974438038575487910065431297720961243249470535941408433912157694286612587884340446554210688189491686149971727665446475073617674315886802296302339223666118571556734860049121051640710027822428018892580868367712928078977280076925272444314488801699169728485265101430460315307473587516916398610517019717797847732796346172153412514603670794367133440444155224427335161548082800384761189216957740253351)
  rw [←seventeen_smooth_powMod_eq]
  decide +kernel

set_option maxRecDepth 32768 in
private theorem nineteen_discriminant_value : jacobiSym (-(2*(195517589389998164724618408221867116323726301536320897974438038575487910065431297720961243249470535941408433912157694286612587884340446554210688189491686149971727665446475073617674315886802296302339223666118571556734860049121051640710027822428018892580868367712928078977280076925272444314488801699169728485265101430460315307473587516916398610517019717797847732796346172153412514603670794367133440444155224427335161548082800384761189216957740253351:ℤ))) (4*195517589389998164724618408221867116323726301536320897974438038575487910065431297720961243249470535941408433912157694286612587884340446554210688189491686149971727665446475073617674315886802296302339223666118571556734860049121051640710027822428018892580868367712928078977280076925272444314488801699169728485265101430460315307473587516916398610517019717797847732796346172153412514603670794367133440444155224427335161548082800384761189216957740253351+174763) = -1 := by norm_num1


set_option maxRecDepth 32768 in
/-- The projected nineteenth roots exclude the final Mersenne-index congruence class. -/
theorem nineteen_last_uniform_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 524289 < b) (idx : b%6846840=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      q∣p^19+d ∧ s∣p^19+d := by
  obtain ⟨F,fac⟩ : p+2∣p^19+524288 := (by decide : Odd 19).nat_add_dvd_pow_add_pow p 2
  have bad := nineteen_cofactor_negative base hb idx fac nineteen_discriminant_period
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) nineteen_discriminant_value
  apply nineteen_last_abstract pp base hb idx fac bad
  intro i lim ps mult nd
  exact nineteen_catalog lim ps base idx mult nd


/-- All Mersenne prime bases admit a two-prime witness for exponent nineteen. -/
theorem mersenne_nineteenth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^19+d ∧ s ∣ p^19+d := by
  have ep : p=2^b-1 := by omega
  have hb1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb := (Nat.prime_of_pow_sub_one_prime hb1 (ep ▸ pp)).2
  by_cases hb : 19 < b
  · by_contra missing
    have idx := nineteen_last_class pp base hb missing
    exact missing (nineteen_last_uniform_witness pp base (by omega) idx)
  · have table : ∀ j ∈ List.range 20, j.Prime → j=2 ∨ j=3 ∨ j=5 ∨ j=7 ∨ j=11 ∨ j=13 ∨ j=17 ∨ j=19 := by decide +kernel
    have js := table b (List.mem_range.mpr (by omega)) pb
    rcases js with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> subst p
    · exact ⟨7,11,17,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨12,19,23,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨4,7,67,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨15,17,23,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨25,37,43,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨17,19,23,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨5,13,29,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩
    · exact ⟨2,5,11,by decide,by decide,by decide,by decide,by decide,by decide +kernel,by decide +kernel⟩

open Erdos889

/-- No solution immediately precedes a nontrivial nineteenth power. -/
theorem nineteenth_power_exclusion {n x : ℕ} (hx : 1 < x)
    (eq : n+1=x^19) : v_l 1 n ≠ 1 := by
  intro sol
  have bound : 32 ≤ x^19 := by
    have a := Nat.pow_le_pow_left (show 2 ≤ x by omega) 19
    norm_num at a
    omega
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^19 := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx (by decide : Odd 19) (by decide) eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : (19:ℕ)≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := mersenne_nineteenth_witness pp base
  have rearr : n+(d+1)=p^19+d := by omega
  exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (rearr ▸ dq) (rearr ▸ ds) sol



/-- The remaining prime exponents congruent to 1 modulo three, with a chosen modulus for the Mersenne index. -/
def H1 : Prop := ∃ P R B M : ℕ, 0 < M ∧ ∀ p r : ℕ, p.Prime → Odd p → 31 < p → P < p →
    r.Prime → 23 ≤ r → R < r → r%3=1 → 2*(r-1) ≤ 3*p →
    (∃ b : ℕ, p+1=2^b ∧ M ∣ b-1 ∧ (2^(b-1) ∣ r-1 → ∃ t : ℕ, r-1=2^t)) →
    B < p^r → ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^r+d ∧ s∣p^r+d

/-- The remaining prime exponents congruent to 2 modulo three, with a chosen modulus for the Mersenne index. -/
def H2 : Prop := ∃ P R B M : ℕ, 0 < M ∧ ∀ p r : ℕ, p.Prime → Odd p → 31 < p → P < p →
    r.Prime → 23 ≤ r → R < r → r%3=2 → 2*(r-2) ≤ 3*p^2 →
    (∃ b : ℕ, p+1=2^b ∧ M ∣ b-1 ∧ (2^(b-1) ∣ r-1 → ∃ t : ℕ, r-1=2^t)) →
    B < p^r → ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^r+d ∧ s∣p^r+d

theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H3 := by
  rintro ⟨P,R,A,M,hM,left⟩ ⟨Q,S,B,N,hN,right⟩
  let X := max (max P Q) 31
  let Y := max (max R S) 23
  obtain ⟨C,hC⟩ := Erdos889.UniformPowers.finite_prime_threshold X
  obtain ⟨D,hD⟩ := Erdos889.UniformPowers.bounded_power_exclusion Y
  obtain ⟨E,hE⟩ := Erdos889.PrimitivePowers.eventually_index_multiple_of_fixed_modulus
    (fun n => Erdos889.v_l 1 n = 1) Erdos889.UniformPowers.finite_prime_threshold
    Erdos889.UniformPowers.bounded_power_exclusion (M*N) (Nat.mul_pos hM hN)
  refine ⟨max (max (max A B) (max C D)) E+1,?_⟩
  rintro p r pp op hp pr low ⟨b,base,align,_⟩ _ large
  by_contra missing
  have hOld := Nat.le_max_left (max (max A B) (max C D)) E
  have hNew := Nat.le_max_right (max (max A B) (max C D)) E
  have hAB := Nat.le_max_left (max A B) (max C D)
  have hCD := Nat.le_max_right (max A B) (max C D)
  have hA := Nat.le_max_left A B
  have hB := Nat.le_max_right A B
  have h1 := Nat.le_max_left C D
  have h2 := Nat.le_max_right C D
  have eq : p^r-1+1=p^r := by omega
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1 < p^r) missing
  have joint := hE (p^r-1) p r b (by omega) sol pp pr (by omega) base eq
  have leftIndex : M ∣ b-1 := (dvd_mul_right M N).trans joint
  have rightIndex : N ∣ b-1 := (dvd_mul_left N M).trans joint
  have bigp : X < p := by
    by_contra! small
    have dp := hC (p^r-1) (by omega) sol p small pp
    have dr := dvd_pow_self p (by omega : r≠0)
    have dn : p∣(p^r-1)+1 := eq.symm ▸ dr
    have d1 := (Nat.dvd_add_iff_right dp).mpr dn
    exact pp.not_dvd_one d1
  have bigr : Y < r := by
    by_contra! small
    exact hD (p^r-1) p r (by omega) pp.one_lt (by omega) small eq sol
  have x1 := Nat.le_max_left P Q
  have x2 := Nat.le_max_right P Q
  have x3 := Nat.le_max_left (max P Q) 31
  have x4 := Nat.le_max_right (max P Q) 31
  have y1 := Nat.le_max_left R S
  have y2 := Nat.le_max_right R S
  have y3 := Nat.le_max_left (max R S) 23
  have y4 := Nat.le_max_right (max R S) 23
  dsimp only [X] at bigp
  dsimp only [Y] at bigr
  by_cases hm : r%3=1
  · exact missing (left p r pp op (by omega) (by omega) pr (by omega) (by omega) hm
      (Erdos889.PrimitivePowers.power_missing_exponent_linear (by omega) op hm missing)
      ⟨b,base,leftIndex,align⟩ (by omega))
  · have nz : r%3≠0 := by
      intro z
      have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pr).mp (Nat.dvd_of_mod_eq_zero z)
      omega
    exact missing (right p r pp op (by omega) (by omega) pr (by omega) (by omega) (by omega)
      (Erdos889.PrimitivePowers.power_missing_exponent_bound (by omega) op pr (by omega) missing)
      ⟨b,base,rightIndex,align⟩ (by omega))

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H3_R1
