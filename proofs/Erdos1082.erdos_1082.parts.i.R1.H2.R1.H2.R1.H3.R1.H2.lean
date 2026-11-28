import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-! Explicit two-isogeny descent on the conductor-15 elliptic curve and the short chords of a diameter pentagon. The two square-class obstructions come from congruences modulo 16 and 9. After two doublings, the dyadic denominator increases at each further doubling, giving a descent without a general Mordell-Weil theorem. -/

section
/-! The two-adic denominator of a doubled point provides a strict descent on the conductor-15 curve. -/
namespace Erdos1082Elliptic
noncomputable section

def doubleX (x:ℚ):=(x^2-16)^2/(4*x*(x+1)*(x+16))
def generalX (x:ℚ):Prop:= x≠0 ∧ x+1≠0 ∧ x+16≠0 ∧ x^2-16≠0


lemma unit_minus (q:ℚ) (nz:q≠0) (ne:q-1≠0) (unit:(padicValRat 2) q=0) : 0<(padicValRat 2) (q-1) := by
  have vn:padicValInt 2 q.num=padicValInt 2 (q.den:ℤ) := by
    rw [padicValInt.of_nat]
    change (padicValInt 2 q.num:ℤ)-padicValNat 2 q.den=0 at unit
    omega
  have n0:q.num≠0 := Rat.num_ne_zero.mpr nz
  have d0:(q.den:ℤ)≠0 := by exact_mod_cast q.den_nz
  have nd:(¬(2:ℤ)∣q.num) ∨ (¬(2:ℤ)∣(q.den:ℤ)) := by
    by_contra! h
    obtain ⟨m,n,be⟩:=q.isCoprime_num_den
    have d:(2:ℤ)∣1 := be ▸ dvd_add (dvd_mul_of_dvd_right h.1 m) (dvd_mul_of_dvd_right h.2 n)
    norm_num at d
  have both:padicValInt 2 q.num=0 ∧ padicValInt 2 (q.den:ℤ)=0 := by
    rcases nd with hn|hd
    · have h:=padicValInt.eq_zero_of_not_dvd hn;exact ⟨h,vn ▸ h⟩
    · have h:=padicValInt.eq_zero_of_not_dvd hd;exact ⟨vn.trans h,h⟩
  have hn:¬(2:ℤ)∣q.num := by simpa [padicValInt.eq_zero_iff,n0] using both.1
  have hd:¬(2:ℤ)∣(q.den:ℤ) := fun h => (padicValInt.eq_zero_iff.mp both.2).elim (by decide) (fun hh => hh.elim d0 (fun nd => nd h))
  have eq:q-1=((q.num-(q.den:ℤ):ℤ):ℚ)/(q.den:ℚ) := by
    nth_rw 1 [←q.num_div_den];push_cast;field_simp
  have zz:q.num-(q.den:ℤ)≠0 := by intro e;rw [eq,e,Int.cast_zero,zero_div] at ne;exact ne rfl
  have vc:padicValInt 2 (q.num-(q.den:ℤ))≠0 := by
    intro z;have h:=padicValInt.eq_zero_iff.mp z;omega
  rw [eq,padicValRat.div (by exact_mod_cast zz) (by exact_mod_cast q.den_nz),padicValRat.of_int,padicValRat.of_nat]
  rw [padicValInt.of_nat] at both
  omega

lemma valfour:(padicValRat 2) 4=2 := by rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow,show (padicValRat 2) (2:ℚ)=1 from padicValRat.self (by decide : 1<(2:ℕ))];norm_num
lemma valsixteen:(padicValRat 2) 16=4 := by rw [show (16:ℚ)=(2:ℚ)^4 by norm_num,padicValRat.pow,show (padicValRat 2) (2:ℚ)=1 from padicValRat.self (by decide : 1<(2:ℕ))];norm_num

lemma double_valuation (x:ℚ) (g:generalX x) :
    (padicValRat 2) (doubleX x)=2*(padicValRat 2) (x^2-16)-(2+(padicValRat 2) x+(padicValRat 2) (x+1)+(padicValRat 2) (x+16)) := by
  obtain ⟨hx,h1,h16,h4⟩:=g
  unfold doubleX
  rw [padicValRat.div (pow_ne_zero _ h4) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) h1) h16),
      padicValRat.mul (mul_ne_zero (mul_ne_zero (by norm_num) hx) h1) h16,
      padicValRat.mul (mul_ne_zero (by norm_num) hx) h1,padicValRat.mul (by norm_num) hx,
      padicValRat.pow,valfour]
  rfl

lemma double_profile (x:ℚ) (g:generalX x) :
    ((padicValRat 2) x<0 → (padicValRat 2) (doubleX x)=(padicValRat 2) x-2) ∧
    ((padicValRat 2) x≠2 → Even ((padicValRat 2) x) → (padicValRat 2) (doubleX x)<0) ∧ (padicValRat 2) (doubleX x)≠2 := by
  obtain ⟨hx,h1,h16,h4⟩:=g
  have val:=double_valuation x ⟨hx,h1,h16,h4⟩
  have a (b:ℚ) (bn:b≠0) (xn:x+b≠0) (n:ℤ) (nv:(padicValRat 2) b=n) :
      min ((padicValRat 2) x) n≤(padicValRat 2) (x+b) ∧ ((padicValRat 2) x≠n → (padicValRat 2) (x+b)=min ((padicValRat 2) x) n) := by
    rw [←nv]
    exact ⟨padicValRat.min_le_padicValRat_add xn,fun dif=>padicValRat.add_eq_min xn hx bn dif⟩
  have a1:=a 1 (by decide) h1 0 (by simp)
  have a16:=a 16 (by decide) h16 4 valsixteen
  have vneg:(padicValRat 2) (-16)=4 := by rw [padicValRat.neg,valsixteen]
  have sq:(padicValRat 2) (x^2)=2*(padicValRat 2) x := padicValRat.pow x
  have b (ne:(padicValRat 2) x≠2):(padicValRat 2) (x^2-16)=min (2*(padicValRat 2) x) 4 := by
    rw [sub_eq_add_neg]
    rw [padicValRat.add_eq_min (by simpa only [sub_eq_add_neg] using h4) (pow_ne_zero _ hx) (by decide)
      (by rw [sq,vneg];omega),sq,vneg]
  by_cases eq:(padicValRat 2) x=2
  · have y0:x^2/16≠0 := div_ne_zero (pow_ne_zero _ hx) (by decide)
    have vv:(padicValRat 2) (x^2/16)=0 := by rw [padicValRat.div (pow_ne_zero _ hx) (by decide),sq,eq,valsixteen];norm_num
    have ne:x^2/16-1≠0 := by intro z;apply h4;linarith
    have gain:=unit_minus _ y0 ne vv
    rw [show x^2/16-1=(x^2-16)/16 by ring,padicValRat.div h4 (by decide),valsixteen] at gain
    rw [a1.2 (by omega),a16.2 (by omega),eq] at val
    refine ⟨by omega,by omega,by omega⟩
  · rw [b eq] at val
    by_cases e0:(padicValRat 2) x=0
    · rw [a16.2 (by omega),e0] at val
      exact ⟨by omega,by omega,by omega⟩
    by_cases e4:(padicValRat 2) x=4
    · rw [a1.2 (by omega),e4] at val
      exact ⟨by omega,by omega,by omega⟩
    rw [a1.2 e0,a16.2 e4] at val
    refine ⟨by omega,?_,by omega⟩
    rintro _ ⟨k,ek⟩;omega
end
end Erdos1082Elliptic
end

section
/-! Rational maps and torsion translations in the elementary descent. -/
namespace Erdos1082Elliptic
noncomputable section

def projectX (u:ℚ):=(u-9)*(u-25)/(4*u)
def doubleOther (u:ℚ):=(u^2-225)^2/(4*u*(u-9)*(u-25))

lemma upper_lift (x y r:ℚ) (pos:0<x) (rp:0<r) (rs:x=r^2) (curve:y^2=x*(x+1)*(x+16)) :
    ∃u z:ℚ,25<u ∧ projectX u=x ∧ z^2=u*(u-9)*(u-25) := by
  let b:=|y|/r
  have bp:0≤b := div_nonneg (abs_nonneg y) rp.le
  have bq:b^2=(x+1)*(x+16) := by
    unfold b;rw [div_pow,sq_abs,←rs,div_eq_iff pos.ne'];linear_combination curve
  have top:4<b := by nlinarith only [bq,bp,pos,sq_nonneg x]
  let u:=2*x+17+2*b
  have up:25<u := by unfold u;linarith
  have eq:u^2-(4*x+34)*u+225=0 := by unfold u;linear_combination 4*bq
  refine ⟨u,2*r*u,up,?_,?_⟩
  · unfold projectX;apply (div_eq_iff (by linarith : 4*u≠0)).mpr;linear_combination eq
  · linear_combination -u*eq-4*u^2*rs

lemma lower_lift (u z r:ℚ) (up:0<u) (us:u=r^2) (curve:z^2=u*(u-9)*(u-25)) :
    ∃x y:ℚ,y^2=x*(x+1)*(x+16) ∧ doubleX x=projectX u := by
  have rn:r≠0 := by intro e;subst r;norm_num at us;linarith
  let b:=z/r
  have bq:b^2=(u-9)*(u-25) := by unfold b;rw [div_pow,←us,div_eq_iff up.ne'];linear_combination curve
  let x:=(u-17+b)/2
  have eq:x^2-(u-17)*x+16=0 := by unfold x;linear_combination bq/4
  have xn:x≠0 := by intro e;rw [e] at eq;norm_num at eq
  have pr:(x+1)*(x+16)=u*x := by linear_combination eq
  have n1:x+1≠0 := by intro q;rw[q,zero_mul] at pr;exact (mul_ne_zero up.ne' xn) pr.symm
  have n16:x+16≠0 := by intro q;rw[q,mul_zero] at pr;exact (mul_ne_zero up.ne' xn) pr.symm
  refine ⟨x,r*x,?_,?_⟩
  · linear_combination -x*eq-x^2*us
  · have numer:(x^2-16)^2=x^2*((u-9)*(u-25)) := by linear_combination (x^2+16+(u-17)*x)*eq
    have den:4*x*(x+1)*(x+16)=4*u*x^2 := by linear_combination 4*x*pr
    unfold projectX doubleX;rw [numer,den];field_simp [xn,up.ne'] <;> ring

lemma reciprocal (x:ℚ) (xp:0<x) : doubleX (16/x)=doubleX x := by
  unfold doubleX
  have xn:x≠0:=xp.ne'
  have n1:x+1≠0:=by linarith
  have n16:x+16≠0:=by linarith
  have m1:16/x+1≠0:=by positivity
  have m16:16/x+16≠0:=by positivity
  field_simp [xn,n1,n16,m1,m16];ring

lemma commute (u:ℚ) (up:0<u) (n9:u-9≠0) (n25:u-25≠0)
    (n15:u^2-225≠0) (jp:0<projectX u) : doubleX (projectX u)=projectX (doubleOther u) := by
  have jn:(u-9)*(u-25)≠0:=mul_ne_zero n9 n25
  have j1:projectX u+1≠0:=by linarith
  have j16:projectX u+16≠0:=by linarith
  have dn:doubleOther u≠0:=div_ne_zero (pow_ne_zero 2 n15) (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) up.ne') n9) n25)
  unfold doubleX
  change _=(doubleOther u-9)*(doubleOther u-25)/(4*doubleOther u)
  field_simp [jp.ne',j1,j16,dn]
  unfold doubleOther projectX
  field_simp [up.ne',n9,n25];ring

lemma lift_translation (u z:ℚ) (up:25<u) (not45:u≠45) (curve:z^2=u*(u-9)*(u-25)) (sq:∃r:ℚ,u=5*r^2) :
    ∃v w r:ℚ,0<v ∧ v=r^2 ∧ w^2=v*(v-9)*(v-25) ∧
      doubleX (doubleX (projectX v))=doubleX (doubleX (projectX u)) := by
  obtain ⟨r,ur⟩:=sq
  have rn:r≠0 := by intro h;rw [h] at ur;norm_num at ur;linarith
  let m:=(z-20)/(u-5)
  let c:=20-5*m
  let v:=m^2+29-u
  have zz:z=m*u+c := by dsimp [c,m];field_simp [show u-5≠0 by linarith];ring
  have sum:u+v=m^2+29 := by dsimp [v];ring
  have prod:u*v=5*(m-4)^2 := by
    apply (mul_left_cancel₀ (by linarith : u-5≠0))
    rw [zz] at curve;unfold c at curve;unfold v
    linear_combination curve
  have big0:0<v := by
    have mn:m≠4 := by
      intro h
      have e:u*v=0 := by rw [prod,h];norm_num
      have ve: v=0 := (mul_eq_zero.mp e).resolve_left (by linarith)
      apply not45;rw [h] at sum;linarith
    by_contra! hv
    have neg:=mul_nonpos_of_nonneg_of_nonpos (show 0≤u by linarith) hv
    nlinarith only [prod,sq_pos_of_ne_zero (sub_ne_zero.mpr mn),neg]
  have small9:v<9 := by
    have e:(u-9)*(v-9)= -4*(m+5)^2 := by linear_combination prod-9*sum
    have mn:m+5≠0 := by
      intro h
      have z:(u-9)*(v-9)=0 := by rw [e,h];norm_num
      have vv: v-9=0 := (mul_eq_zero.mp z).resolve_left (by linarith)
      apply not45
      have mm:m=(-5) := by linarith
      rw [mm] at sum;linarith
    by_contra! ge
    have nw:=mul_nonneg (show 0≤u-9 by linarith) (sub_nonneg.mpr ge)
    nlinarith only [e,nw,sq_pos_of_ne_zero mn]
  have vc:(m*v+c)^2=v*(v-9)*(v-25) := by
    unfold c
    linear_combination -(v-5)*sum*v+(v-5)*prod
  have vs:v=((m-4)/r)^2 := by rw [div_pow,eq_div_iff (pow_ne_zero _ rn)]; rw [ur] at prod;linear_combination prod/5
  refine ⟨v,m*v+c,(m-4)/r,big0,vs,vc,?_⟩
  have jp:0<projectX u:=div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have jv:0<projectX v:=div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
  have un:u^2-225≠0:=by nlinarith
  have vn:v^2-225≠0:=by nlinarith [mul_pos (show 0<15-v by linarith) (show 0<15+v by linarith)]
  have du:25<doubleOther u := by
    unfold doubleOther
    apply (lt_div_iff₀ (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (by linarith))).mpr
    nlinarith only [sq_pos_of_ne_zero (mul_ne_zero (show u-5≠0 by linarith) (sub_ne_zero.mpr not45))]
  have ap:(doubleOther u-25)*(doubleOther v-25)=400 := by
    have fact (z:ℚ) (nz:z≠0) (n9:z-9≠0) (n25:z-25≠0) :
        doubleOther z-25=((z-5)*(z-45))^2/(4*z*(z-9)*(z-25)) := by
      unfold doubleOther;field_simp [nz,n9,n25];ring
    rw [fact u (by linarith) (by linarith) (by linarith),fact v (by linarith) (by linarith) (by linarith)]
    have p5:(u-5)*(v-5)=5*(m-4)^2-5*(m^2+29)+25 := by linear_combination prod-5*sum
    have p45:(u-45)*(v-45)=5*(m-4)^2-45*(m^2+29)+45^2 := by linear_combination prod-45*sum
    have p9:(u-9)*(v-9)=5*(m-4)^2-9*(m^2+29)+9^2 := by linear_combination prod-9*sum
    have p25:(u-25)*(v-25)=5*(m-4)^2-25*(m^2+29)+25^2 := by linear_combination prod-25*sum
    field_simp [show u≠0 by linarith,show u-9≠0 by linarith,show u-25≠0 by linarith,show v≠0 by linarith,show v-9≠0 by linarith,show v-25≠0 by linarith]
    calc
      _ = ((u-5)*(v-5))^2*((u-45)*(v-45))^2 := by ring
      _ = 6400*(u*v)*((u-9)*(v-9))*((u-25)*(v-25)) := by rw [p5,p45,prod,p9,p25];ring
      _ = _ := by ring
  have dv:25<doubleOther v := by by_contra! h;have bad:=mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr du.le) (sub_nonpos.mpr h); linarith
  rw [commute v big0 (by linarith) (by linarith) vn jv,commute u (by linarith) (by linarith) (by linarith) un jp]
  have general (s t:ℚ) (hs:25<s) (ht:25<t) (dis:(s-25)*(t-25)=400) : projectX t=16/projectX s := by
    have st:t=25+400/(s-25) := by field_simp [show s-25≠0 by linarith];linear_combination dis
    unfold projectX;field_simp [show s≠0 by linarith,show t≠0 by linarith,show s-9≠0 by linarith,show s-25≠0 by linarith]
    rw [st];field_simp [show s-25≠0 by linarith];ring
  rw [general _ _ du dv ap]
  apply reciprocal
  exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
end
end Erdos1082Elliptic
end

section
/-! Square classes of rational points on the pair of two-isogenous curves attached to a repeated pentagon chord. -/
namespace Erdos1082Elliptic
noncomputable section

lemma rational_square_of_even (x:ℚ) (xp:0<x) (even:∀p:ℕ,p.Prime→Even (padicValRat p x)) : ∃r:ℚ,x=r^2 := by
  classical
  let n:=x.num.natAbs*x.den
  have pos:0<n := Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_pos.mpr xp).ne') x.pos
  have fact (p:ℕ) (hp:p.Prime) : Even (n.factorization p) := by
    haveI:Fact p.Prime:=⟨hp⟩
    obtain ⟨z,hz⟩:=even p hp
    change (padicValNat p x.num.natAbs:ℤ)-padicValNat p x.den=z+z at hz
    rw [Nat.factorization_def _ hp]
    dsimp [n]
    rw [padicValNat.mul (Int.natAbs_ne_zero.mpr (Rat.num_pos.mpr xp).ne') x.den_nz]
    refine ⟨(padicValNat p x.num.natAbs+padicValNat p x.den)/2,?_⟩
    omega
  let root:=∏p∈n.factorization.support,p^(n.factorization p/2)
  have equ:root^2=n := by
    refine Eq.trans ?_ (Nat.prod_factorization_pow_eq_self pos.ne')
    change (∏p∈n.factorization.support,p^(n.factorization p/2))^2=∏p∈n.factorization.support,p^n.factorization p
    rw [←Finset.prod_pow]
    apply Finset.prod_congr rfl; intro p hp
    rw [←pow_mul];congr 1
    obtain ⟨b,hb⟩:=fact p (Nat.prime_of_mem_primeFactors ((Nat.support_factorization n) ▸ hp))
    omega
  refine ⟨(root:ℚ)/(x.den:ℚ),?_⟩
  have e:((root:ℚ)^2)=(x.num.natAbs:ℚ)*(x.den:ℚ) := by exact_mod_cast equ
  have hn:((x.num.natAbs:ℕ):ℚ)=(x.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) (Int.natAbs_of_nonneg (Rat.num_pos.mpr xp).le)
  rw [hn] at e
  nth_rw 1 [←Rat.num_div_den x]
  have dn:(x.den:ℚ)≠0 := by exact_mod_cast x.den_nz
  field_simp [dn]
  linear_combination -e

lemma even_away (p:ℕ) [Fact p.Prime] (x y r s:ℚ) (e:y^2=x*(x+r)*(x+s)) (xyz:x≠0) (xr:x+r≠0) (xs:x+s≠0)
    (r0:r≠0) (s0:s≠0) (rv:padicValRat p r=0) (sv:padicValRat p s=0) : Even (padicValRat p x) := by
  have vals:2*padicValRat p y=padicValRat p x+padicValRat p (x+r)+padicValRat p (x+s) := by
    have h:=congrArg (padicValRat p) e
    simpa only [padicValRat.pow,Nat.cast_ofNat,padicValRat.mul (mul_ne_zero xyz xr) xs,padicValRat.mul xyz xr] using h
  rcases lt_trichotomy (padicValRat p x) 0 with h|h|h
  · rw [padicValRat.add_eq_of_lt xr xyz r0 (rv ▸ h),padicValRat.add_eq_of_lt xs xyz s0 (sv ▸ h)] at vals
    exact ⟨padicValRat p y-padicValRat p x,by omega⟩
  · exact ⟨0,by omega⟩
  · have ex:padicValRat p (x+r)=0 := by rw [add_comm,padicValRat.add_eq_of_lt (add_comm x r ▸ xr) r0 xyz (rv ▸ h),rv]
    have es:padicValRat p (x+s)=0 := by rw [add_comm,padicValRat.add_eq_of_lt (add_comm x s ▸ xs) s0 xyz (sv ▸ h),sv]
    rw [ex,es] at vals; exact ⟨padicValRat p y,by omega⟩
end
end Erdos1082Elliptic
end

section
/-! Local square obstructions for the two elliptic descent coverings. -/
namespace Erdos1082Elliptic
lemma integral_quartic (d A c:ℤ) (r q:ℚ) (h:q^2=(d:ℚ)*r^4+A*r^2+c) :
    ∃u v z:ℤ, IsCoprime u v ∧ z^2=d*u^4+A*u^2*v^2+c*v^4 := by
  let u:=r.num; let v:ℤ:=r.den
  have rd:(u:ℚ)=r*(v:ℚ) := by
    exact (div_eq_iff (by dsimp [v];exact_mod_cast r.den_nz : (v:ℚ)≠0)).mp (by simpa [u,v] using r.num_div_den)
  let N:=d*u^4+A*u^2*v^2+c*v^4
  have sq:IsSquare (N:ℚ) := by
    refine ⟨q*(v:ℚ)^2,?_⟩
    unfold N;push_cast; rw [rd]; linear_combination -(v:ℚ)^4*h
  obtain ⟨z,hz⟩:=Rat.isSquare_intCast_iff.mp sq
  exact ⟨u,v,z,r.isCoprime_num_den,by simpa [N,pow_two] using hz.symm⟩

lemma quartic_of_class (d A B c:ℤ) (x y r:ℚ) (r0:r≠0) (d0:d≠0) (dc:d*c=B)
    (shape:x=(d:ℚ)*r^2) (curve:y^2=x*(x^2+(A:ℚ)*x+B)) :
    ∃u v z:ℤ, IsCoprime u v ∧ z^2=d*u^4+A*u^2*v^2+c*v^4 := by
  apply integral_quartic d A c r (y/(d*r))
  have inz:(d:ℚ)≠0 := by exact_mod_cast d0
  field_simp [inz,r0]
  rw [←dc,shape] at curve
  push_cast at curve
  linear_combination curve

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma no_two_class (u v z:ℤ) (cop:IsCoprime u v) (h:z^2=2*u^4+17*u^2*v^2+8*v^4) : False := by
  have hh:(z:ZMod 16)^2=2*(u:ZMod 16)^4+17*(u:ZMod 16)^2*(v:ZMod 16)^2+8*(v:ZMod 16)^4 := by simpa using congrArg (Int.castRingHom (ZMod 16)) h
  have table : ∀a b c:ZMod 16,c^2=2*a^4+17*a^2*b^2+8*b^4 → 8*a=0 ∧ 8*b=0 := by decide
  obtain ⟨ea,eb⟩:=table _ _ _ hh
  obtain ⟨s,t,bez⟩:=cop
  have vv:(s:ZMod 16)*u+(t:ZMod 16)*v=1 := by simpa using congrArg (Int.castRingHom (ZMod 16)) bez
  have bad:(8:ZMod 16)=0 := by linear_combination -8*vv+(s:ZMod 16)*ea+(t:ZMod 16)*eb
  exact (by decide : (8:ZMod 16)≠0) bad

set_option maxRecDepth 10000 in
lemma no_three_class (d c u v z:ℤ) (which:(d=3 ∧ c=75) ∨ (d=15 ∧ c=15))
    (cop:IsCoprime u v) (h:z^2=d*u^4-34*u^2*v^2+c*v^4) : False := by
  have hh:(z:ZMod 9)^2=(d:ZMod 9)*(u:ZMod 9)^4-34*(u:ZMod 9)^2*(v:ZMod 9)^2+(c:ZMod 9)*(v:ZMod 9)^4 := by simpa using congrArg (Int.castRingHom (ZMod 9)) h
  have both:3*(u:ZMod 9)=0 ∧ 3*(v:ZMod 9)=0 := by
    rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (by decide : ∀a b c:ZMod 9,c^2=3*a^4-34*a^2*b^2+75*b^4 → 3*a=0 ∧ 3*b=0) _ _ _ hh
    · exact (by decide : ∀a b c:ZMod 9,c^2=15*a^4-34*a^2*b^2+15*b^4 → 3*a=0 ∧ 3*b=0) _ _ _ hh
  obtain ⟨s,t,bez⟩:=cop
  have vv:(s:ZMod 9)*u+(t:ZMod 9)*v=1 := by simpa using congrArg (Int.castRingHom (ZMod 9)) bez
  have bad:(3:ZMod 9)=0 := by linear_combination -3*vv+(s:ZMod 9)*both.1+(t:ZMod 9)*both.2
  exact (by decide : (3:ZMod 9)≠0) bad
end Erdos1082Elliptic
end

section
/-! The first curve has positive x-coordinates in the trivial square class and the second in classes 1 and 5. -/
namespace Erdos1082Elliptic
noncomputable section
open Classical

def selector (p:ℕ) (x:ℚ):ℚ := if Even (padicValRat p x) then 1 else p

lemma selector_pos {p:ℕ} (hp:p.Prime) (x:ℚ) : 0<selector p x := by
  unfold selector;split
  · norm_num
  · exact_mod_cast hp.pos

lemma selector_even (p q:ℕ) (hp:p.Prime) (hq:q.Prime) (x:ℚ) (xz:x≠0)
    (keep:q=p ∨ Even (padicValRat q x)) : Even (padicValRat q (x/selector p x)) := by
  haveI:Fact p.Prime:=⟨hp⟩;haveI:Fact q.Prime:=⟨hq⟩
  by_cases eq:q=p
  · subst q
    unfold selector
    split_ifs with h
    · simpa using h
    · rw [padicValRat.div xz (by exact_mod_cast hp.ne_zero : (p:ℚ)≠0),padicValRat.self hp.one_lt]
      exact Int.even_sub_one.mpr h
  · have e:=keep.resolve_left eq
    unfold selector; split_ifs
    · simpa using e
    · rw [padicValRat.div xz (by exact_mod_cast hp.ne_zero : (p:ℚ)≠0),padicValRat.of_nat,padicValNat_primes eq,Int.natCast_zero,sub_zero]
      exact e

lemma squareclass_one (x y:ℚ) (pos:0<x) (curve:y^2=x*(x+1)*(x+16)) : ∃q:ℚ,x=q^2 := by
  let d:=selector 2 x
  have good (p:ℕ) (hp:p.Prime) : Even (padicValRat p (x/d)) := by
    apply selector_even 2 p (by decide) hp x pos.ne'
    by_cases eq:p=2
    · exact Or.inl eq
    right
    haveI:Fact p.Prime:=⟨hp⟩;haveI:Fact (Nat.Prime 2):=⟨by decide⟩
    have v16:padicValRat p (16:ℚ)=0 := by
      rw [show (16:ℚ)=(2:ℚ)^4 by norm_num,padicValRat.pow,show (2:ℚ)=((2:ℕ):ℚ) by rfl,padicValRat.of_nat,padicValNat_primes eq];simp
    exact even_away p x y 1 16 curve pos.ne' (by linarith) (by linarith) (by norm_num) (by norm_num) (by simp) v16
  obtain ⟨r,hr⟩:=rational_square_of_even (x/d) (div_pos pos (selector_pos (by decide : Nat.Prime 2) x)) good
  by_cases e:Even (padicValRat 2 x)
  · exact ⟨r,by simpa [d,selector,e] using hr⟩
  · have h:x=2*r^2 := by simpa [d,selector,e] using (div_eq_iff (selector_pos (by decide : Nat.Prime 2) x).ne').mp hr |>.trans (mul_comm _ _)
    have rn:r≠0 := by intro zr; rw [zr] at h; norm_num at h; linarith
    obtain ⟨u,v,z,hcop,heq⟩:=quartic_of_class 2 17 16 8 x y r rn (by decide) (by decide) h (by linear_combination curve)
    exact (no_two_class u v z hcop heq).elim

lemma squareclass_five (x y:ℚ) (pos:0<x) (e9:x-9≠0) (e25:x-25≠0) (curve:y^2=x*(x-9)*(x-25)) :
    (∃q:ℚ,x=q^2) ∨ (∃q:ℚ,x=5*q^2) := by
  let d:=selector 3 x
  let x':=x/d
  let f:=selector 5 x'
  have dx:0<d := selector_pos (by decide : Nat.Prime 3) _
  have px:0<x' := div_pos pos dx
  have good (p:ℕ) (hp:p.Prime) : Even (padicValRat p (x'/f)) := by
    apply selector_even 5 p (by decide) hp x' px.ne'
    by_cases eq:p=5
    · exact Or.inl eq
    · right;apply selector_even 3 p (by decide) hp x pos.ne'
      by_cases e:p=3
      · exact Or.inl e
      · right
        haveI:Fact p.Prime:=⟨hp⟩;haveI:Fact (Nat.Prime 3):=⟨by decide⟩;haveI:Fact (Nat.Prime 5):=⟨by decide⟩
        have small (q:ℕ) [Fact q.Prime] (pq:p≠q):padicValRat p (-((q:ℚ)^2))=0 := by
          rw [padicValRat.neg,padicValRat.pow,padicValRat.of_nat,padicValNat_primes pq];simp
        exact even_away p x y (-9) (-25) (by simpa only [sub_eq_add_neg] using curve) pos.ne' (by simpa only [sub_eq_add_neg] using e9) (by simpa only [sub_eq_add_neg] using e25)
          (by norm_num) (by norm_num) (by convert small 3 e using 1 <;> norm_num) (by convert small 5 eq using 1 <;> norm_num)
  obtain ⟨r,hr⟩:=rational_square_of_even (x'/f) (div_pos px (selector_pos (by decide : Nat.Prime 5) x')) good
  have shape:x=(d*f)*r^2 := by
    have hh:=(div_eq_iff (selector_pos (by decide : Nat.Prime 5) x').ne').mp hr
    have hid:x=x'*d := (div_eq_iff dx.ne').mp (show x/d=x' by rfl)
    rw [hid,hh];ring
  have rn:r≠0 := by intro zr;rw [zr] at shape;norm_num at shape;linarith
  have D:d=1 ∨ d=3 := by dsimp [d,selector];split <;> simp
  have F:f=1 ∨ f=5 := by dsimp [f,selector];split <;> simp
  rcases D with d1|d3 <;> rcases F with f1|f5
  · exact Or.inl ⟨r,by simpa [d1,f1] using shape⟩
  · exact Or.inr ⟨r,by simpa [d1,f5] using shape⟩
  · obtain ⟨u,v,z,hcop,heq⟩:=quartic_of_class 3 (-34) 225 75 x y r rn (by decide) (by decide)
      (by simpa [d3,f1] using shape) (by linear_combination curve)
    exact (no_three_class 3 75 u v z (Or.inl ⟨rfl,rfl⟩) hcop (by linear_combination heq)).elim
  · obtain ⟨u,v,z,hcop,heq⟩:=quartic_of_class 15 (-34) 225 15 x y r rn (by decide) (by decide)
      (by norm_num [d3,f5] at shape ⊢; exact shape) (by linear_combination curve)
    exact (no_three_class 15 15 u v z (Or.inr ⟨rfl,rfl⟩) hcop (by linear_combination heq)).elim
end
end Erdos1082Elliptic
end

section
/-! An elementary two-isogeny descent excludes positive non-torsion rational points of conductor 15. -/
namespace Erdos1082Elliptic
noncomputable section

lemma good_of_double (x:ℚ) (h:doubleX x≠0) : generalX x := by
  have den:4*x*(x+1)*(x+16)≠0 := (div_ne_zero_iff.mp h).2
  have num:(x^2-16)^2≠0 := (div_ne_zero_iff.mp h).1
  exact ⟨((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp den).1).1).2),
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp den).1).2,(mul_ne_zero_iff.mp den).2,
    fun e => num (by rw [e];norm_num)⟩

lemma positive_data (x y:ℚ) (px:0<x) (g:generalX x) (curve:y^2=x*(x+1)*(x+16)) :
    0<doubleX (doubleX x) ∧ generalX (doubleX (doubleX x)) ∧ padicValRat 2 (doubleX (doubleX x))<0 := by
  have dp (x:ℚ) (px:0<x) (g:generalX x) : 0<doubleX x := by
    exact div_pos (sq_pos_of_ne_zero g.2.2.2) (by positivity)
  have even (x y:ℚ) (g:generalX x) (curve:y^2=x*(x+1)*(x+16)) : Even (padicValRat 2 (doubleX x)) := by
    have d:y≠0 := by intro e;rw [e,zero_pow (by decide : 2≠0)] at curve;exact (mul_ne_zero (mul_ne_zero g.1 g.2.1) g.2.2.1) curve.symm
    have eq : doubleX x=((x^2-16)/(2*y))^2 := by
      unfold doubleX;rw [div_pow,mul_pow,curve];ring
    rw [eq,padicValRat.pow]; exact ⟨_,by ring⟩
  have gd (t:ℚ) (tp:0<t) (n:padicValRat 2 t≠2) : generalX t := by
    refine ⟨tp.ne',by linarith,by linarith,?_⟩
    intro e;have et:t=4 := by nlinarith only [tp,e]
    exact n (et ▸ valfour)
  have pp:=dp x px g
  have g2:=gd _ pp (double_profile x g).2.2
  have p2:=dp _ pp g2
  have v2:padicValRat 2 (doubleX (doubleX x))<0 :=
    (double_profile _ g2).2.1 (double_profile x g).2.2 (even x y g curve)
  exact ⟨p2,gd _ p2 (by omega),v2⟩

lemma positive_translate (x y:ℚ) (g:generalX x) (curve:y^2=x*(x+1)*(x+16)) :
    ∃a b:ℚ,0<a ∧ b^2=a*(a+1)*(a+16) ∧ doubleX a=doubleX x := by
  by_cases pos:0<x
  · exact ⟨x,y,pos,curve,rfl⟩
  have nx:x<0 := lt_of_le_of_ne (le_of_not_gt pos) g.1
  have low:0<x+16 := by
    by_contra! h
    have t:=mul_pos_of_neg_of_neg nx (show x+1<0 by linarith)
    have u:=mul_neg_of_pos_of_neg t (lt_of_le_of_ne h g.2.2.1)
    nlinarith only [curve,u,sq_nonneg y]
  have hi:x+1<0 := by
    by_contra! h
    have t:=mul_neg_of_neg_of_pos nx (lt_of_le_of_ne h g.2.1.symm)
    have u:=mul_neg_of_neg_of_pos t low
    nlinarith only [curve,u,sq_nonneg y]
  let a:= -(x+16)/(x+1)
  let b:=15*y/(x+1)^2
  have ap:0<a := div_pos_of_neg_of_neg (neg_neg_of_pos low) hi
  refine ⟨a,b,ap,?_,?_⟩
  · dsimp [a,b];field_simp [g.2.1];linear_combination 225*curve
  · unfold doubleX
    have a1:a+1≠0:=by linarith
    have a16:a+16≠0:=by linarith
    field_simp [g.1,g.2.1,g.2.2.1,ap.ne',a1,a16]
    unfold a;field_simp [g.2.1];ring

lemma descending_point (x y:ℚ) (xp:0<x) (g:generalX x) (curve:y^2=x*(x+1)*(x+16)) :
    ∃a b:ℚ,0<a ∧ generalX a ∧ b^2=a*(a+1)*(a+16) ∧
      doubleX (doubleX x)=doubleX (doubleX (doubleX a)) := by
  obtain ⟨r,hr⟩:=squareclass_one x y xp curve
  have rp:r≠0 := by intro e;rw [e] at hr;norm_num at hr;linarith
  obtain ⟨u,z,up,ju,cu⟩:=upper_lift x y |r| xp (abs_pos.mpr rp) (by rw [sq_abs,←hr]) curve
  have ex : ∃q w:ℚ,w^2=q*(q+1)*(q+16) ∧ doubleX (doubleX x)=doubleX (doubleX (doubleX q)) := by
    rcases squareclass_five u z (by linarith) (by linarith) (by linarith) cu with sq|five
    · obtain ⟨k,ks⟩:=sq
      obtain ⟨q,w,cq,dq⟩:=lower_lift u z k (by linarith) ks cu
      exact ⟨q,w,cq,by rw [dq,ju]⟩
    · have ne:u≠45 := by
        intro h;rw [h] at ju;norm_num [projectX] at ju;apply g.2.2.2;rw [←ju];norm_num
      obtain ⟨v,w,k,vp,ks,cw,eq⟩:=lift_translation u z up ne cu five
      obtain ⟨q,b,cq,dq⟩:=lower_lift v w k vp ks cw
      exact ⟨q,b,cq,by rw [dq,eq,ju]⟩
  obtain ⟨q,w,cq,ee⟩:=ex
  have p2:=(positive_data x y xp g curve).1
  have dn:doubleX q≠0 := by intro h;rw [ee,h] at p2;norm_num [doubleX] at p2
  obtain ⟨a,b,ap,ac,ad⟩:=positive_translate q w (good_of_double q dn) cq
  exact ⟨a,b,ap,good_of_double a (ad ▸ dn),ac,by rw [ad,←ee]⟩

theorem conductor_fifteen (x y:ℚ) (xp:0<x) (curve:y^2=x*(x+1)*(x+16)) : x=4 := by
  classical
  by_contra ex
  have g:generalX x := ⟨xp.ne',by linarith,by linarith,by intro h;apply ex;nlinarith only [h,xp]⟩
  let Bad (n:ℕ):Prop:=∃x y:ℚ,0<x ∧ generalX x ∧ y^2=x*(x+1)*(x+16) ∧
    (-padicValRat 2 (doubleX (doubleX x))).toNat=n
  have hex:∃n,Bad n := ⟨_,x,y,xp,g,curve,rfl⟩
  obtain ⟨p,q,pp,pg,pc,pmin⟩:=Nat.find_spec hex
  obtain ⟨a,b,ap,ag,ac,dub⟩:=descending_point p q pp pg pc
  obtain ⟨_,g2,neg⟩:=positive_data a b ap ag ac
  have vv:=(double_profile _ g2).1 neg
  have smaller:Nat.find hex≤(-padicValRat 2 (doubleX (doubleX a))).toNat :=
    Nat.find_min' hex ⟨a,b,ap,ag,ac,rfl⟩
  rw [dub,vv] at pmin
  omega
end
end Erdos1082Elliptic
end

section
/-! Exact Gram determinant identities for three equal short chords of an equidiagonal pentagon. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

def chordTable (w:Fin 5→ℝ) (i j:Fin 5) := if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j
def dotEntry (w:Fin 5→ℝ) (i j:Fin 5) := chordTable w 0 i+chordTable w 0 j-chordTable w i j
def detThree (p q r s t u v w z:ℝ) := p*(t*z-u*w)-q*(s*z-u*v)+r*(s*w-t*v)
def minorZero (w:Fin 5→ℝ) := ∀i j k l m n:Fin 5,detThree
  (dotEntry w i l) (dotEntry w i m) (dotEntry w i n)
  (dotEntry w j l) (dotEntry w j m) (dotEntry w j n)
  (dotEntry w k l) (dotEntry w k m) (dotEntry w k n)=0

lemma plane_minors (p:Fin 5→ℝ²) (s:ℝ) (w:Fin 5→ℝ)
    (table:∀i j,chordTable w i j=s*dist (p i) (p j)^2) : minorZero w := by
  let coord (a b:ℝ²) := (a 0-b 0)^2+(a 1-b 1)^2
  have ds (a b:ℝ²) : dist a b^2=coord a b := by
    rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]; simp [coord,Real.dist_eq]
  let x (i:Fin 5) := p i 0-p 0 0
  let y (i:Fin 5) := p i 1-p 0 1
  have entry (i j:Fin 5) : dotEntry w i j=2*s*(x i*x j+y i*y j) := by
    simp only [dotEntry,table,ds,coord,x,y]; ring
  intro i j k l m n
  simp only [detThree,entry]; ring

set_option maxHeartbeats 500000 in
lemma three_chords_0 (a b c:ℝ) (h:minorZero ![a,a,a,b,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (b+1-a) (b+a-1) (b+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (b+1-a) (b+b-0) (b+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (1+1-c) (1+b-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (1+a-a) (1+b-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (b+1-a) (b+b-0) (b+1-1) (1+1-c) (1+b-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-9*a^3/8-a^2*b/4+143*a^2/32+19*a*b/8+57*a/128-19*b^2*c/8+5*b*c/32-271*b/64-19*c^3/8+195*c^2/32-281*c/128-4841/128)*g1+(9*a^3/4+a^2*b/2-143*a^2/16-19*a*b/4-57*a/64+19*b^2*c/4-5*b*c/16+271*b/32+19*c^3/4-309*c^2/16+1907*c/64+1741/128)*g2+(-9*a^3/8-a^2*b/4+143*a^2/32+19*a*b/8+57*a/128-19*b^2*c/8+5*b*c/32-271*b/64-19*c^3/8+271*c^2/32-1365*c/128-1097/64)*g3+(17*a^3/8+a^2*b/2+a^2*c/4-335*a^2/32-99*a*b/16-23*a*c/16+1671*a/128+19*b^2*c/8-5*b*c/32+63*b/4+19*c/16-603/128)*g4+(-17*a^3/4-a^2*b-a^2*c/2+263*a^2/16+57*a*b/8+19*a*c/8-527*a/64-19*b^2*c/4-19*b^2/4+5*b*c/16-233*b/16+19*c^2/8-195*c/32+777/128)*g5+(33*a^3/8+a^2*b+3*a^2*c/4-503*a^2/32-95*a*b/16-57*a*c/16+1695*a/128+19*b^2*c/8+19*b^2/8-5*b*c/32+107*b/8-19*c^3/4+347*c^2/16-3417*c/64+3889/128)*g6+(17*a^3/8+a^2*b/2+a^2*c/4-207*a^2/32-19*a*b/16-19*a*c/16-329*a/128+19*b^2*c/8+19*b^2/8-5*b*c/32+19*b/16+19*c^2/8-247*c/16+4233/128)*g7+(-25*a^3/8-3*a^2*b/4-a^2*c/2+383*a^2/32+19*a*b/4+19*a*c/8-1111*a/128-19*b^2*c/8+5*b*c/32-661*b/64+19*c^3/8-347*c^2/32+4233*c/128-2501/128)*g8+(a^3+a^2*b/4+a^2*c/4-15*a^2/4-19*a*b/16-19*a*c/16+73*a/16+195*b/64-19*c^3/8+347*c^2/32-3341*c/128+1477/128)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_1 (a b c:ℝ) (h:minorZero ![a,a,b,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-a) (a+1-1) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (a+1-a) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (1+1-c) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (1+a-b) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-b) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  linear_combination (-4*a^2*c+6*a^2-11*a*c+33*a/2-45*c+135/2)*g0+(8*a^2*c-12*a^2+22*a*c-33*a+90*c-225)*g1+(-4*a^3-8*a^2*c-3*a^2-22*a*c-23*a-90*c+180)*g2+(-90)*g3+(90)*g4+(8*a^3+30*a^2+112*a-90)*g5+(180)*g6+(-8*a^3-22*a^2-82*a+112)*g7+(-90)*g8

set_option maxHeartbeats 500000 in
lemma three_chords_2 (a b c:ℝ) (h:minorZero ![a,a,b,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+c-a) (a+1-1) (a+a-0) (a+c-1) (c+1-a) (c+a-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (c+1-a) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (1+1-a) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g7 g8 g9
  linear_combination (a^3+a^2*b/4+a^2*c/4-15*a^2/4-21*a*b/16-21*a*c/16+79*a/16+255*b/64+17*c^2/8-191*c/64+1441/128)*g0+(-7*a^3/8-a^2*b/4-a^2*c/4+95*a^2/32+a*b/4+21*a*c/16-1109*a/128+17*b^2*c/8+15*b*c/32-187*b/64-17*c^2/4-311*c/64-55/8)*g1+(-17*a^3/8-a^2*b/2-a^2*c/2+265*a^2/32+59*a*b/16+21*a*c/8-787*a/128-17*b^2*c/8-17*b^2/8-15*b*c/32-289*b/32+17*c^2/8-189*c/32+247/16)*g2+(9*a^3/8+a^2*b/4+a^2*c/4-145*a^2/32-19*a*b/8-21*a*c/16+155*a/128+17*b^2*c/8+15*b*c/32+323*b/64-693*c/64+1001/64)*g3+(-a^3/8+25*a^2/32+17*a*b/16+477*a/128-17*b^2*c/8-15*b*c/32-17*b/16+17*c^2/8+251*c/32-561/128)*g4+(17*a^3/8+a^2*b/2+a^2*c/2-265*a^2/32-59*a*b/16-21*a*c/8+787*a/128+17*b^2*c/8+17*b^2/8+15*b*c/32+289*b/32-17*c^2/8+189*c/32-247/16)*g5+(-a^3-a^2*b/4-a^2*c/4+3*a^2/2-21*a*b/16+13*a*c/16+33*a/8-17*b^2/8+291*b/64-19*c/64-21/8)*g7+(a^3+a^2*b/4+a^2*c/4-15*a^2/4-21*a*b/16-21*a*c/16+79*a/16-17*b^2/8+255*b/64+17*c^2/8-561*c/64+459/64)*g8+(7*a^2/4+17*a*b/8-97*a/16+17*b^2/8-155*b/32-17*c^2/8+223*c/32-2585/128)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_3 (a b c:ℝ) (h:minorZero ![a,b,a,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (1+a-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-b) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-35*b*c+105*b/2+495*c/4-1485/8)*g1+(32*b*c-105*b-219*c+669)*g2+(-16*b*c+105*b/2+219*c/2-669/2)*g3+(-8*a^3-10*a^2+22*a*b*c+24*a*b+219*a*c/2-2451*a/4+24*b^2-11*b*c-453*b/2-105*c/4+5311/8)*g4+(8*a^3+14*a^2-22*a*b*c-24*a*b-219*a*c/2+2479*a/4-32*b^2+267*b-949/2)*g5+(-4*a^3-7*a^2+11*a*b*c+12*a*b+219*a*c/4-2479*a/8+16*b^2-437*b/2-146*c+1595/2)*g6+(-57*b/2-57*c/2+351/2)*g7+(297*b/2+349*c/2-1719/2)*g8+(-60*b-73*c+342)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_4 (a b c:ℝ) (h:minorZero ![a,b,a,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (c+1-b) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (c+1-b) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (1+1-a) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (1+a-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (c+1-b) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (90)*g1+(-180)*g2+(90)*g3+(-4*a^2*c+6*a^2-11*a*c+33*a/2-45*c-45/2)*g4+(8*a^2*c-12*a^2+22*a*c-33*a+90*c+45)*g5+(-4*a^3-8*a^2*c-3*a^2-22*a*c-23*a-90*c)*g6+(-90)*g7+(8*a^3+30*a^2+112*a+180)*g8+(-8*a^3-22*a^2-82*a+22)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_5 (a b c:ℝ) (h:minorZero ![a,b,c,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-b) (a+1-1) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (1+1-a) (1+a-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (1+a-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-b) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-245/32)*g0+(-9*a^3/8-a^2*b/4-5*a^2*c/8+39*a^2/16+5*a*b/8+25*a*c/16-113*a/32-35*b/16+35*c/16+245/16)*g1+(-245/16)*g2+(-a^3-a^2*b/4-a^2*c/4+15*a^2/4+5*a*b/8+5*a*c/8-23*a/8-35*b/16-35*c/16+175/8)*g3+(17*a^3/8+a^2*b/2+7*a^2*c/8-71*a^2/16-5*a*b/4-35*a*c/16+181*a/32+35*b/8-105/16)*g4+(-2*a^3-a^2*b/2-a^2*c/2+4*a^2+5*a*b/4+5*a*c/4-17*a/4-35*b/8-35*c/8+105/8)*g5+(-245/16)*g6+(-a^3/8-3*a^2*c/8+7*a^2/16+15*a*c/16-45*a/32+35*c/8-105/16)*g7+(9*a^3/8+a^2*b/4+5*a^2*c/8-39*a^2/16-5*a*b/8-25*a*c/16+113*a/32+35*b/16-35*c/16+245/16)*g8+(-9*a^2/4-7*a*b/8-7*a*c/8+39*a/8+35*b/16+35*c/16-471/32)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_6 (a b c:ℝ) (h:minorZero ![b,a,a,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (1+1-c) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  linear_combination (a^3+a^2*b/4+a^2*c/4-2*a^2+3*a*b/4+a*c-9*a/8-3*b/32+63*c/64-13/64)*g0+(-25*a^3/8-3*a^2*b/4-a^2*c/2+41*a^2/8-9*a*b/4-2*a*c+255*a/64+9*b/32-63*c/64-121/64)*g1+(33*a^3/8+a^2*b+3*a^2*c/4-57*a^2/8+3*a*b+3*a*c-327*a/64-5*b/2+63*c/32+57/64)*g2+(-9*a^3/8-a^2*b/4+9*a^2/8-3*a*b/4+111*a/64+3*b/32+63*c/64+19/32)*g3+(17*a^3/8+a^2*b/2+a^2*c/4-25*a^2/8+3*a*b/2+a*c-183*a/64-3*b/16-51/64)*g4+(-17*a^3/4-a^2*b-a^2*c/2+11*a^2/4-17*a*b/4-2*a*c+231*a/32+3*b/8-63/64)*g5+(9*a^3/4+a^2*b/2-9*a^2/4+3*a*b/2-111*a/32-3*b/16-63*c/32+109/64)*g6+(17*a^3/8+a^2*b/2+a^2*c/4-29*a^2/8+3*a*b+3*a*c/4-167*a/64+5*b^2/8-73*b/16-c+263/64)*g7+(-9*a^3/8-a^2*b/4+9*a^2/8-3*a*b/4+111*a/64+3*b/32+63*c/64+223/64)*g8

set_option maxHeartbeats 500000 in
lemma three_chords_7 (a b c:ℝ) (h:minorZero ![b,a,a,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+c-a) (b+1-1) (b+b-0) (b+c-1) (c+1-a) (c+b-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (c+1-a) (c+b-1) (c+1-1)=0 at g1
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (1+b-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-4*a^2*c/3+2*a^2+7*a*c/9-7*a/6+5*c/27-10/27)*g0+(4*a^3/3+8*a^2*c/3-31*a^2/9-14*a*c/9+23*a/18-10*c/27+10/27)*g1+(4*a^3/3+5*a^2/9-19*a/18-5/27)*g3+(-4*a^3/3-4*a^2*c/3+13*a^2/9+7*a*c/9-a/9+5*c/27)*g4+(-5/54)*g5+(-5/27)*g6+(-4*a^3/3+4*a^2*c/3-11*a^2/9-7*a*c/9+25*a/9-5*c/27-16/27)*g7+(4*a^3/3-8*a^2*c/3+41*a^2/9+14*a*c/9-61*a/18+10*c/27-5/9)*g8+(4*a^2*c/3-2*a^2-7*a*c/9+7*a/6-5*c/27+5/27)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_8 (a b c:ℝ) (h:minorZero ![b,a,c,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (1+1-a) (1+b-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (1+b-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (a+1-a) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-8*a^3-48*a^2*b^2+2*a^2-1132*a*b^2+842*a*b*c+597*a*b+249*a*c+719*a/2+696*b^2-106*b*c-1185*b-57*c-881/2)*g0+(8*a^3+48*a^2*b^2-2*a^2+1180*a*b^2-842*a*b*c-597*a*b-249*a*c-719*a/2+476*b^2-429*b*c+351*b/2-225*c/2-65/4)*g1+(-4*a^3-24*a^2*b^2+a^2-590*a*b^2+421*a*b*c+597*a*b/2+249*a*c/2+719*a/4-190*b^2+213*b*c-2033*b/2+153*c/2-1415/4)*g2+(291*b*c-873*b/2+207*c/2-621/4)*g3+(-24*a*b^2-590*b^2+122*b*c+675*b+33*c+297)*g4+(32*a*b^2+772*b^2-388*b*c+301*b-138*c+87/2)*g5+(-16*a*b^2-460*b^2+244*b*c+342*b+66*c+198)*g6+(-8*a*b^2-206*b^2+194*b*c-257*b+69*c-69)*g7+(8*a*b^2+222*b^2-122*b*c-558*b-33*c-441/2)*g8+(8*b^2+96*b+18)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_9 (a b c:ℝ) (h:minorZero ![b,c,a,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-c) (b+1-1) (b+b-0) (b+a-1) (a+1-c) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (a+1-c) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (a+1-c) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (a+1-c) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-a^2/2+21*a*b/8+21*a*c/8-219*a/8+21*b^2/8+21*b*c/4-125*b/8-63*c^2/8+41*c/8+1223/16)*g0+(a^3+a^2*b/4+a^2*c/4+3*a^2/4+a*b/4+a*c/4+109*a/4-63*b/8-21*c^2/2+315*c/8-559/8)*g1+(-9*a^2/2-75*a/2-21*c/2+104)*g2+(-9*a^3/8-a^2*b/4+a^2*c/4+45*a^2/8-a*b/4+a*c/4+913*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8+63*b/8+65*c/8-112)*g3+(-a^3-a^2*b/4-a^2*c/4+3*a^2/2-a*b/4-a*c/4-17*a/2+63*b/8+21*c^2/2-231*c/8+10)*g4+(-a^3/8+a^2*c/2+15*a^2/8+a*c/2+749*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8-21*c^2/2+53*c/2-497/8)*g5+(a^3/8-a^2*c/2-15*a^2/8-a*c/2-749*a/16+21*b^2*c/8+63*b*c^2/8-125*b*c/8+21*c^2/2-53*c/2+497/8)*g6+(17*a^3/8+a^2*b/2-57*a^2/8+a*b/2-777*a/16+21*b^2*c/8+63*b*c^2/8-125*b*c/8-63*b/4+857/16)*g7+(-25*a^3/8-3*a^2*b/4-a^2*c/4+105*a^2/8-3*a*b/4-a*c/4+1241*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8+189*b/8+19*c/8-793/8)*g8+(a^3+a^2*b/4+a^2*c/4-6*a^2+a*b/4+a*c/4-29*a-63*b/8-19*c/8+729/16)*g9

end Erdos1082Second
end
end

section
/-! The sharp energy inequality for alternating steps around a closed five-cycle. -/
open scoped BigOperators
noncomputable section
namespace Erdos1082Second

def nextPair (v:Fin 5→ℝ) (i:Fin 5) := v i+v (i+1)
def signless (v:Fin 5→ℝ) (i:Fin 5) := 2*v i+v (i-1)+v (i+1)
def squareSum (v:Fin 5→ℝ) := ∑ i,v i^2

lemma dot_signless (v:Fin 5→ℝ) : ∑i,v i*signless v i=squareSum (nextPair v) := by
  simp only [squareSum,signless,nextPair,Fin.sum_univ_succ]
  change v 0*(2*v 0+v 4+v 1)+(v 1*(2*v 1+v 0+v 2)+(v 2*(2*v 2+v 1+v 3)+
    (v 3*(2*v 3+v 2+v 4)+(v 4*(2*v 4+v 3+v 0)+0)))) =
    (v 0+v 1)^2+((v 1+v 2)^2+((v 2+v 3)^2+((v 3+v 4)^2+((v 4+v 0)^2+0))))
  ring

lemma square_signless (v:Fin 5→ℝ) (closed:∑i,v i=0) :
    squareSum (signless v)=3*squareSum (nextPair v)-squareSum v := by
  simp only [squareSum,signless,nextPair,Fin.sum_univ_succ] at closed ⊢
  change v 0+(v 1+(v 2+(v 3+(v 4+0))))=0 at closed
  change (2*v 0+v 4+v 1)^2+((2*v 1+v 0+v 2)^2+((2*v 2+v 1+v 3)^2+
    ((2*v 3+v 2+v 4)^2+((2*v 4+v 3+v 0)^2+0)))) =
    3*((v 0+v 1)^2+((v 1+v 2)^2+((v 2+v 3)^2+((v 3+v 4)^2+((v 4+v 0)^2+0)))))-
    ((v 0)^2+((v 1)^2+((v 2)^2+((v 3)^2+((v 4)^2+0)))))
  linear_combination (v 0+v 1+v 2+v 3+v 4)*closed

lemma gram (v:Fin 5→ℝ) (s t:ℝ) :
    0 ≤ s^2*squareSum (signless v)-2*s*t*squareSum (nextPair v)+t^2*squareSum v := by
  rw [←dot_signless]
  have h : 0 ≤ ∑i,(s*signless v i-t*v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  convert h using 1
  unfold squareSum
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pentagon_energy (X Y:Fin 5→ℝ) (hx:∑i,X i=0) (hy:∑i,Y i=0) :
    (3-Real.sqrt 5)*(squareSum X+squareSum Y)≤2*(squareSum (nextPair X)+squareSum (nextPair Y)) := by
  let A:=squareSum X+squareSum Y
  let E:=squareSum (nextPair X)+squareSum (nextPair Y)
  change (3-Real.sqrt 5)*A≤2*E
  have An : 0≤A := add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (X i)) (Finset.sum_nonneg fun i _ => sq_nonneg (Y i))
  have En : 0≤E := add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rcases An.eq_or_lt with h|h
  · rw [←h,mul_zero]; linarith
  have gx := gram X A E
  have gy := gram Y A E
  rw [square_signless X hx] at gx
  rw [square_signless Y hy] at gy
  have q: 0≤A*(3*A*E-A^2-E^2) := by
    dsimp only [A,E] at *
    nlinarith only [gx,gy]
  have q' := nonneg_of_mul_nonneg_right q h
  have r : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  by_contra! bad
  have upper : 0<(3+Real.sqrt 5)*A-2*E := by nlinarith [mul_pos h (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<5))]
  have neg := mul_neg_of_pos_of_neg upper (sub_neg.mpr bad)
  nlinarith only [neg,q',show (Real.sqrt 5)^2*A^2=5*A^2 by rw [r]]
end Erdos1082Second
end
end

section
/-! The next distance after a five-cycle diameter is at least the diameter divided by the golden ratio. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

theorem short_chord (p:Fin 5→ℂ) (M d:ℝ) (side:∀i,dist (p i) (p (i+1))=M)
    (short:∀i,dist (p i) (p (i+1+1))≤d) : (3-Real.sqrt 5)*M^2≤2*d^2 := by
  let X (i:Fin 5) := (p i).re-(p (i+1)).re
  let Y (i:Fin 5) := (p i).im-(p (i+1)).im
  have tel (w:Fin 5→ℝ) : ∑ i,(w i-w (i+1))=0 := by
    simp only [Fin.sum_univ_succ]
    change (w 0-w 1)+((w 1-w 2)+((w 2-w 3)+((w 3-w 4)+((w 4-w 0)+0))))=0
    ring
  have spec := pentagon_energy X Y (tel _) (tel _)
  have length (z w:ℂ) : (z.re-w.re)^2+(z.im-w.im)^2=dist z w^2 := by
    rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]; ring
  have edge (i:Fin 5) : (X i)^2+(Y i)^2=M^2 := (length _ _).trans (by rw [side])
  have skip (i:Fin 5) : (nextPair X i)^2+(nextPair Y i)^2≤d^2 := by
    dsimp only [nextPair,X,Y]
    rw [sub_add_sub_cancel,sub_add_sub_cancel,length]
    exact pow_le_pow_left₀ dist_nonneg (short i) _
  have su: squareSum X+squareSum Y=5*M^2 := by
    unfold squareSum; rw [←Finset.sum_add_distrib]; simp [edge]
  have ku: squareSum (nextPair X)+squareSum (nextPair Y)≤5*d^2 := by
    unfold squareSum; rw [←Finset.sum_add_distrib]
    exact (Finset.sum_le_sum fun i _ => skip i).trans_eq (by simp)
  rw [su] at spec
  nlinarith only [spec,ku]

set_option maxHeartbeats 800000 in
theorem diameter_second_golden (A:Finset ℝ²) (M d:ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (cyc:∃a b c d e:A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (hd:∀u∈(distanceSet A).erase M,u≤d) : (3-Real.sqrt 5)*M^2≤2*d^2 := by
  classical
  obtain ⟨a,b,c,q,e,nd,ab,bc,cq,qe,ea⟩ := cyc
  let z : Fin 5→A := ![a,b,c,q,e]
  let F := Complex.orthonormalBasisOneI.repr.symm
  have iso (x y:ℝ²) : dist (F x) (F y)=dist x y := by rw [dist_eq_norm,←map_sub,F.norm_map,dist_eq_norm]
  have ed (i:Fin 5) : dist (z i).1 (z (i+1)).1=M := by fin_cases i <;> assumption
  have ex := (OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter.diameter_exclusions A M hM bound).1
  have ne (w x y u v : A) (hn : [w,x,y,u,v].Nodup) (wx:dist w.1 x.1=M)
      (xy:dist x.1 y.1=M) (uv:dist u.1 v.1=M) : dist w.1 y.1≤d := by
    have notmax : dist w.1 y.1≠M := fun h => ex ⟨w,x,y,u,v,hn,wx,xy,h,uv⟩
    have wny : w≠y := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at hn
      exact hn.1.2.1
    exact hd _ (Finset.mem_erase.mpr ⟨notmax,Finset.mem_image.mpr ⟨(w.1,y.1),Finset.mem_offDiag.mpr
      ⟨w.2,y.2,Subtype.coe_injective.ne wny⟩,rfl⟩⟩)
  apply short_chord (fun i => F (z i).1) M d (fun i => (iso _ _).trans (ed i))
  intro i
  rw [iso]
  apply ne (z i) (z (i+1)) (z (i+1+1)) (z (i+1+1+1)) (z (i+1+1+1+1)) _ (ed i) (ed (i+1)) (ed (i+1+1+1))
  fin_cases i
  · change [a,b,c,q,e].Nodup
    exact nd
  · change [b,c,q,e,a].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [c,q,e,a,b].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [q,e,a,b,c].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [e,a,b,c,q].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
end Erdos1082Second
end
end

section
/-! If three pentagon short chords reach the second distance, then their ratio is forced. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma three_equal_value (w:Fin 5→ℝ) (h:minorZero w) (a:ℝ)
    (count:3≤(Finset.univ.filter fun i => w i=a).card) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  classical
  obtain ⟨B,sub,n⟩:=Finset.exists_subset_card_eq count
  have e (i:Fin 5) (hi:i∈B) : w i=a := (Finset.mem_filter.mp (sub hi)).2
  have cases : ∀S:Finset (Fin 5), S.card=3 → (0∈S ∧ 1∈S ∧ 2∈S) ∨ (0∈S ∧ 1∈S ∧ 3∈S) ∨ (0∈S ∧ 1∈S ∧ 4∈S) ∨ (0∈S ∧ 2∈S ∧ 3∈S) ∨ (0∈S ∧ 2∈S ∧ 4∈S) ∨ (0∈S ∧ 3∈S ∧ 4∈S) ∨ (1∈S ∧ 2∈S ∧ 3∈S) ∨ (1∈S ∧ 2∈S ∧ 4∈S) ∨ (1∈S ∧ 3∈S ∧ 4∈S) ∨ (2∈S ∧ 3∈S ∧ 4∈S) := by decide
  rcases cases B n with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,a,w 3,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_0 a (w 3) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_1 a (w 2) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_2 a (w 2) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_3 a (w 1) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_4 a (w 1) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_5 a (w 1) (w 2) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_6 a (w 0) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_7 a (w 0) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_8 a (w 0) (w 2) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,w 1,a,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_9 a (w 0) (w 1) (eq ▸ h)

lemma normalized_minor (p:Fin 5→ℝ²) (M:ℝ) (hM:0<M) (unit:∀i,dist (p i) (p (i+1))=M) :
    minorZero (fun i => (M^2)⁻¹*dist (p i) (p (i+2))^2) := by
  apply plane_minors p ((M^2)⁻¹)
  intro i j
  by_cases ij:i=j
  · simp [chordTable,ij]
  by_cases e:j=i+1 ∨ i=j+1
  · have de:dist (p i) (p j)=M := by
      rcases e with rfl|rfl
      · exact unit i
      · exact (dist_comm _ _).trans (unit j)
    simp [chordTable,ij,e,de,hM.ne']
  by_cases e2:j=i+2
  · rw [chordTable,if_neg ij,if_neg e,if_pos e2,e2]
  have e3 : i=j+2 := (by decide : ∀i j:Fin 5,i≠j → ¬(j=i+1 ∨ i=j+1) → j≠i+2 → i=j+2) i j ij e e2
  simp [chordTable,ij,e,e2,←e3,dist_comm (p i) (p j)]

lemma equal_or_below_two (p:Fin 5→ℝ²) (M d:ℝ) (hM:0<M) (hd:0≤d) (dm:d<M)
    (unit:∀i,dist (p i) (p (i+1))=M)
    (strict:(3-Real.sqrt 5)*M^2<2*d^2) :
    (Finset.univ.filter fun i => dist (p i) (p (i+2))=d).card≤2 := by
  classical
  let w (i:Fin 5):=(M^2)⁻¹*dist (p i) (p (i+2))^2
  let a:=(M^2)⁻¹*d^2
  have eq:a*M^2=d^2 := by dsimp [a]; field_simp
  have ap:0≤a := by dsimp [a]; positivity
  have al:a<1 := by
    by_contra! h
    have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg M)
    rw [eq,one_mul] at hh
    nlinarith only [hh,mul_pos (sub_pos.mpr dm) (add_pos_of_pos_of_nonneg hM hd)]
  have lo:3-Real.sqrt 5<2*a := by
    by_contra! h
    have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg M)
    rw [mul_assoc,eq] at hh
    exact strict.not_ge hh
  have rt : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have rootpos:0<Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have p1:a-1≠0 := sub_ne_zero.mpr al.ne
  have p2:a+1≠0 := by linarith
  have p3:4*a-1≠0 := by intro q; nlinarith
  have p4:a^2-3*a+1≠0 := by
    intro q
    have h:=mul_pos (sub_pos.mpr lo) (show 0<(3+Real.sqrt 5)-2*a by linarith)
    nlinarith only [h,q,rt]
  by_contra! bad
  have sub:(Finset.univ.filter fun i => dist (p i) (p (i+2))=d)⊆Finset.univ.filter (fun i => w i=a) := by
    intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [w,a,(Finset.mem_filter.mp hi).2]⟩
  have vv:=three_equal_value w (normalized_minor p M hM unit) a (by have := Finset.card_le_card sub; omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero p1 p2) p3) p4 vv
end Erdos1082Second
end
end

section
/-! A diameter five-cycle is metrically regular as soon as three short chords agree. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

set_option maxHeartbeats 1200000 in
lemma rigid_0 (a b c:ℝ) (h:minorZero ![a,a,a,b,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (b+1-a) (b+a-1) (b+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (b+1-a) (b+b-0) (b+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (1+1-c) (1+b-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (1+a-a) (1+b-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (b+1-a) (b+b-0) (b+1-1) (1+1-c) (1+b-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-a^3/4-a^2*b/2+57*a^2/32+33*a*b/16-33*a/32-b^2*c+25*b*c/32-7*b/4-c^3+105*c^2/32-21*c/64-941/64)*g1+(a^3/2+a^2*b-57*a^2/16-33*a*b/8+33*a/16+2*b^2*c-25*b*c/16+7*b/2+2*c^3-153*c^2/16+27*c/2+361/64)*g2+(-a^3/4-a^2*b/2+57*a^2/32+33*a*b/16-33*a/32-b^2*c+25*b*c/32-7*b/4-c^3+137*c^2/32-295*c/64-217/32)*g3+(a^3/4+a^2*b-89*a^2/32-39*a*b/8-3*a*c/16+201*a/32+b^2*c-25*b*c/32+245*b/32+3*c/16-15/4)*g4+(-a^3/2-2*a^2*b+81*a^2/16+29*a*b/4+3*a*c/8-117*a/16-2*b^2*c-2*b^2+25*b*c/16-6*b+c^2-105*c/32+217/64)*g5+(a^3/4+2*a^2*b-129*a^2/32-27*a*b/4-9*a*c/16+285*a/32+b^2*c+b^2-25*b*c/32+11*b/2-2*c^3+169*c^2/16-727*c/32+709/64)*g6+(a^3/4+a^2*b-73*a^2/32-21*a*b/8-3*a*c/16+45*a/32+b^2*c+b^2-25*b*c/32-9*b/32+c^2-13*c/2+903/64)*g7+(-a^3/4-3*a^2*b/2+105*a^2/32+83*a*b/16+3*a*c/8-201*a/32-b^2*c+25*b*c/32-17*b/4+c^3-169*c^2/32+853*c/64-491/64)*g8+(a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8+5*b/4-c^3+169*c^2/32-711*c/64+141/32)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-7*a^3/8+a^2*b/4-91*a^2/32-17*a*b/8-373*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-119*c^2/32-43*c/128+4485/128)*g1+(7*a^3/4-a^2*b/2+91*a^2/16+17*a*b/4+373*a/64-19*b^2*c/4-71*b*c/16-195*b/32-19*c^3/4+233*c^2/16-1127*c/64-2457/128)*g2+(-7*a^3/8+a^2*b/4-91*a^2/32-17*a*b/8-373*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-195*c^2/32+737*c/128+1157/64)*g3+(-a^3/8-a^2*b/2-a^2*c/4+187*a^2/32+91*a*b/16+19*a*c/16-523*a/128-19*b^2*c/8-71*b*c/32-43*b/4-15*c/16-209/128)*g4+(a^3/4+a^2*b+a^2*c/2-179*a^2/16-49*a*b/8-15*a*c/8-269*a/64+19*b^2*c/4+19*b^2/4+71*b*c/16+157*b/16-19*c^2/8+119*c/32+155/128)*g5+(-17*a^3/8-a^2*b-3*a^2*c/4+355*a^2/32+79*a*b/16+45*a*c/16+61*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-69*b/8+19*c^3/4-271*c^2/16+2789*c/64-4333/128)*g6+(-a^3/8-a^2*b/2-a^2*c/4+123*a^2/32+11*a*b/16+15*a*c/16+901*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-19*b/16-19*c^2/8+247*c/16-3909/128)*g7+(9*a^3/8+3*a^2*b/4+a^2*c/2-267*a^2/32-4*a*b-15*a*c/8-165*a/128+19*b^2*c/8+71*b*c/32+433*b/64-19*c^3/8+271*c^2/32-3909*c/128+3313/128)*g8+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+15*a*b/16+15*a*c/16-13*a/16-119*b/64+19*c^3/8-271*c^2/32+2713*c/128-1585/128)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (9*a^3/8+a^2*b/4-107*a^2/32-17*a*b/8-629*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-119*c^2/32-43*c/128+4549/128)*g1+(-9*a^3/4-a^2*b/2+107*a^2/16+17*a*b/4+629*a/64-19*b^2*c/4-71*b*c/16-195*b/32-19*c^3/4+233*c^2/16-1127*c/64-2585/128)*g2+(9*a^3/8+a^2*b/4-107*a^2/32-17*a*b/8-629*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-195*c^2/32+737*c/128+1189/64)*g3+(-17*a^3/8-a^2*b/2-a^2*c/4+203*a^2/32+91*a*b/16+19*a*c/16-267*a/128-19*b^2*c/8-71*b*c/32-43*b/4-15*c/16-273/128)*g4+(17*a^3/4+a^2*b+a^2*c/2-195*a^2/16-49*a*b/8-15*a*c/8-525*a/64+19*b^2*c/4+19*b^2/4+71*b*c/16+157*b/16-19*c^2/8+119*c/32+283/128)*g5+(-33*a^3/8-a^2*b-3*a^2*c/4+371*a^2/32+79*a*b/16+45*a*c/16+317*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-69*b/8+19*c^3/4-271*c^2/16+2789*c/64-4397/128)*g6+(-17*a^3/8-a^2*b/2-a^2*c/4+139*a^2/32+11*a*b/16+15*a*c/16+1157*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-19*b/16-19*c^2/8+247*c/16-3973/128)*g7+(25*a^3/8+3*a^2*b/4+a^2*c/2-283*a^2/32-4*a*b-15*a*c/8-421*a/128+19*b^2*c/8+71*b*c/32+433*b/64-19*c^3/8+271*c^2/32-3909*c/128+3377/128)*g8+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+15*a*b/16+15*a*c/16-13*a/16-119*b/64+19*c^3/8-271*c^2/32+2713*c/128-1585/128)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_1 (a b c:ℝ) (h:minorZero ![a,a,b,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-a) (a+1-1) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (a+1-a) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (1+1-c) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (1+a-b) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-b) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-2*a^2+3*a/2-1/2)*g0+(-2*a^3+4*a^2-3*a+1)*g1+(2*a^3-2*a^2*c-a^2-8*a*c+15*a-16)*g2+(4*a^2*c-6*a^2+16*a*c-24*a)*g5+(-4*a^2*c+6*a^2+2*a*b-14*a*c+18*a+8*b+8*c-24)*g7
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (2*a^2*b+6*a^2*c-12*a^2-5*a*b/2+25*a*c/2-15*a+b/2+113*c/2-171/2)*g0+(-4*a^2*b-12*a^2*c+24*a^2+5*a*b-25*a*c+30*a-b-113*c+567/2)*g1+(4*a^3+4*a^2*b+12*a^2*c-5*a^2-5*a*b+25*a*c+41*a+b+113*c-455/2)*g2+(225/2)*g3+(-225/2)*g4+(-8*a^3-38*a^2-142*a+113)*g5+(-225)*g6+(8*a^3+28*a^2+209*a/2-281/2)*g7+(225/2)*g8
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (4*a^2*c-6*a^2+15*a*c-45*a/2+56*c-84)*g0+(-8*a^2*c+12*a^2-30*a*c+45*a-112*c+561/2)*g1+(4*a^3+8*a^2*c+7*a^2+30*a*c+26*a+112*c-449/2)*g2+(225/2)*g3+(-225/2)*g4+(-8*a^3-38*a^2-142*a+113)*g5+(-225)*g6+(8*a^3+28*a^2+209*a/2-281/2)*g7+(225/2)*g8
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_2 (a b c:ℝ) (h:minorZero ![a,a,b,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+c-a) (a+1-1) (a+a-0) (a+c-1) (c+1-a) (c+a-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (c+1-a) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (1+1-a) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8+43*b/32+c^2-93*c/32+291/64)*g0+(a^3/4-a^2*b/2-9*a^2/32+17*a*b/16+3*a*c/16-267*a/64+b^2*c-19*b*c/32-27*b/32-2*c^2+71*c/32-71/32)*g1+(-a^3/4-a^2*b+81*a^2/32+29*a*b/8+3*a*c/8-237*a/64-b^2*c-b^2+19*b*c/32-51*b/16+c^2-115*c/32+187/32)*g2+(a^3/4+a^2*b/2-57*a^2/32-33*a*b/16-3*a*c/16+69*a/64+b^2*c-19*b*c/32+59*b/32-115*c/32+55/8)*g3+(-a^3/4+33*a^2/32+a*b/2+99*a/64-b^2*c+19*b*c/32-b/2+c^2+11*c/16-149/64)*g4+(a^3/4+a^2*b-81*a^2/32-29*a*b/8-3*a*c/8+237*a/64+b^2*c+b^2-19*b*c/32+51*b/16-c^2+115*c/32-187/32)*g5+(-a^2*b/2+a^2/2+5*a*b/16+3*a*c/16-b^2+53*b/16-5*c/16-5/2)*g7+(a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8-b^2+43*b/32+c^2-77*c/16+41/8)*g8+(a^2/4+a*b-9*a/4+b^2-99*b/32-c^2+131*c/32-365/64)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16-171*b/64-17*c^2/8+139*c/64-1525/128)*g0+(23*a^3/8+a^2*b/4+a^2*c/4-83*a^2/32-17*a*c/16+473*a/128-17*b^2*c/8-83*b*c/32+103*b/64+17*c^2/4+467*c/64+59/8)*g1+(a^3/8+a^2*b/2+a^2*c/2-181*a^2/32-51*a*b/16-17*a*c/8-17*a/128+17*b^2*c/8+17*b^2/8+83*b*c/32+205*b/32-17*c^2/8+121*c/32-155/16)*g2+(7*a^3/8-a^2*b/4-a^2*c/4+93*a^2/32+17*a*b/8+17*a*c/16+169*a/128-17*b^2*c/8-83*b*c/32-239*b/64+745*c/64-1053/64)*g3+(-15*a^3/8-5*a^2/32-17*a*b/16-321*a/128+17*b^2*c/8+83*b*c/32+17*b/16-17*c^2/8-303*c/32+581/128)*g4+(-a^3/8-a^2*b/2-a^2*c/2+181*a^2/32+51*a*b/16+17*a*c/8+17*a/128-17*b^2*c/8-17*b^2/8-83*b*c/32-205*b/32+17*c^2/8-121*c/32+155/16)*g5+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+25*a*b/16-9*a*c/16-41*a/8+17*b^2/8-207*b/64-33*c/64+21/8)*g7+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16+17*b^2/8-171*b/64-17*c^2/8+645*c/64-775/64)*g8+(-7*a^2/4-17*a*b/8+69*a/16-17*b^2/8+87*b/32+17*c^2/8-155*c/32+2541/128)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16-171*b/64-17*c^2/8+139*c/64-1525/128)*g0+(7*a^3/8+a^2*b/4+a^2*c/4-67*a^2/32-17*a*c/16+729*a/128-17*b^2*c/8-83*b*c/32+103*b/64+17*c^2/4+467*c/64+55/8)*g1+(17*a^3/8+a^2*b/2+a^2*c/2-197*a^2/32-51*a*b/16-17*a*c/8-273*a/128+17*b^2*c/8+17*b^2/8+83*b*c/32+205*b/32-17*c^2/8+121*c/32-147/16)*g2+(-9*a^3/8-a^2*b/4-a^2*c/4+109*a^2/32+17*a*b/8+17*a*c/16+425*a/128-17*b^2*c/8-83*b*c/32-239*b/64+745*c/64-1085/64)*g3+(a^3/8-21*a^2/32-17*a*b/16-577*a/128+17*b^2*c/8+83*b*c/32+17*b/16-17*c^2/8-303*c/32+645/128)*g4+(-17*a^3/8-a^2*b/2-a^2*c/2+197*a^2/32+51*a*b/16+17*a*c/8+273*a/128-17*b^2*c/8-17*b^2/8-83*b*c/32-205*b/32+17*c^2/8-121*c/32+147/16)*g5+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+25*a*b/16-9*a*c/16-41*a/8+17*b^2/8-207*b/64-33*c/64+21/8)*g7+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16+17*b^2/8-171*b/64-17*c^2/8+645*c/64-775/64)*g8+(-7*a^2/4-17*a*b/8+69*a/16-17*b^2/8+87*b/32+17*c^2/8-155*c/32+2541/128)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_3 (a b c:ℝ) (h:minorZero ![a,b,a,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (1+a-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-b) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-2*b*c^2+3*b*c-33*c^2/2+291*c/4-72)*g1+(8*b*c^2-6*b*c+30*c^2-162*c+327)*g2+(-4*b*c^2+3*b*c-15*c^2+81*c-327/2)*g3+(-4*a^2*b-24*a^2-12*a*b*c^2+24*a*b*c-24*a*b-9*a*c^2+165*a*c/2-321*a+8*b^2*c-12*b^2+6*b*c^2-3*b*c-30*b-9*c^2/2-153*c/4+324)*g4+(4*a^2*b+24*a^2+12*a*b*c^2-24*a*b*c+26*a*b+9*a*c^2-165*a*c/2+348*a-8*b^2*c+12*b^2-18*b*c+62*b+45*c-225)*g5+(-2*a^2*b-12*a^2-6*a*b*c^2+12*a*b*c-13*a*b-9*a*c^2/2+165*a*c/4-174*a+4*b^2*c-6*b^2-17*b*c-31*b-132*c+783/2)*g6+(-15*a+9*b*c-9*b+9*c^2-48*c+105)*g7+(15*a+19*b*c+9*b-9*c^2+174*c-432)*g8+(-14*b*c-63*c+327/2)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (38*b*c-57*b+38*c^2-171*c+171)*g1+(-24*a*b-76*b*c+114*b-76*c^2+318*c-532)*g2+(12*a*b+38*b*c-57*b+38*c^2-159*c+266)*g3+(8*a^3+8*a^2*b*c+24*a^2*b-7*a^2-8*a*b^2+30*a*b*c-69*a*b+38*a*c^2-111*a*c+438*a-34*b^2-76*b*c+192*b+90*c-504)*g4+(-8*a^3-8*a^2*b*c-24*a^2*b+3*a^2+8*a*b^2-38*a*b*c+69*a*b-38*a*c^2+111*a*c-428*a+38*b^2+76*b*c-204*b-114*c+380)*g5+(4*a^3+4*a^2*b*c+12*a^2*b-3*a^2/2-4*a*b^2+19*a*b*c-69*a*b/2+19*a*c^2-111*a*c/2+214*a-7*b^2-38*b*c+216*b+283*c-682)*g6+(4*a*b*c-12*a*b-17*a/2-19*b*c+69*b/2-19*c^2+159*c/2-128)*g7+(-4*a*b*c+12*a*b+17*a/2-12*b^2+19*b*c-373*b/2+19*c^2-687*c/2+734)*g8+(6*b^2+76*b+132*c-303)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (39*b*c-117*b/2-579*c/4+1737/8)*g1+(-32*b*c+117*b+255*c-806)*g2+(16*b*c-117*b/2-255*c/2+403)*g3+(8*a^3+16*a^2-30*a*b*c-24*a*b-255*a*c/2+3013*a/4-24*b^2+15*b*c+513*b/2+117*c/4-6443/8)*g4+(-8*a^3-22*a^2+30*a*b*c+24*a*b+255*a*c/2-3055*a/4+32*b^2-303*b+1135/2)*g5+(4*a^3+11*a^2-15*a*b*c-12*a*b-255*a*c/4+3055*a/8-16*b^2+497*b/2+184*c-964)*g6+(69*b/2+69*c/2-216)*g7+(-341*b/2-437*c/2+1041)*g8+(68*b+92*c-825/2)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_4 (a b c:ℝ) (h:minorZero ![a,b,a,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (c+1-b) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (c+1-b) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (1+1-a) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (1+a-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (c+1-b) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-2*a^2+3*a/2-1/2)*g4+(-2*a^3+4*a^2-3*a+1)*g5+(2*a^3-2*a^2*c-a^2-8*a*c+15*a-16)*g6+(4*a^2*c-6*a^2+16*a*c-24*a)*g8+(-4*a^2*c+6*a^2+2*a*b-14*a*c+18*a+8*b+8*c-24)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-225/2)*g1+(225)*g2+(-225/2)*g3+(2*a^2*b+6*a^2*c-12*a^2-5*a*b/2+25*a*c/2-15*a+b/2+113*c/2+27)*g4+(-4*a^2*b-12*a^2*c+24*a^2+5*a*b-25*a*c+30*a-b-113*c-54)*g5+(4*a^3+4*a^2*b+12*a^2*c-5*a^2-5*a*b+25*a*c+41*a+b+113*c-5/2)*g6+(225/2)*g7+(-8*a^3-38*a^2-142*a-449/2)*g8+(8*a^3+28*a^2+209*a/2-28)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-225/2)*g1+(225)*g2+(-225/2)*g3+(4*a^2*c-6*a^2+15*a*c-45*a/2+56*c+57/2)*g4+(-8*a^2*c+12*a^2-30*a*c+45*a-112*c-57)*g5+(4*a^3+8*a^2*c+7*a^2+30*a*c+26*a+112*c+1/2)*g6+(225/2)*g7+(-8*a^3-38*a^2-142*a-449/2)*g8+(8*a^3+28*a^2+209*a/2-28)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_5 (a b c:ℝ) (h:minorZero ![a,b,c,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-b) (a+1-1) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (1+1-a) (1+a-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (1+a-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-b) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-1535/128)*g0+(-a^3/4-a^2*b/2-3*a^2*c/4+53*a^2/32+29*a*b/16+101*a*c/32-805*a/128-225*b/64+215*c/64+385/16)*g1+(-1535/64)*g2+(-a^2*b/2+3*a^2/4+29*a*b/16+7*a*c/16-27*a/8-225*b/64-215*c/64+275/8)*g3+(a^3/4+a^2*b+3*a^2*c/4-69*a^2/32-29*a*b/8-115*a*c/32+1269*a/128+225*b/32-665/64)*g4+(-a^2*b+a^2+29*a*b/8+7*a*c/8-29*a/4-225*b/32-215*c/32+165/8)*g5+(-1545/64)*g6+(-a^3/4-3*a^2*c/4+37*a^2/32+87*a*c/32-341*a/128+215*c/32-655/64)*g7+(a^3/4+a^2*b/2+3*a^2*c/4-53*a^2/32-29*a*b/16-101*a*c/32+805*a/128+225*b/64-215*c/64+385/16)*g8+(-a^2/4-a*b-3*a*c/4+19*a/8+137*b/32+115*c/32-3057/128)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (175/32)*g0+(-7*a^3/8+a^2*b/4+5*a^2*c/8-13*a^2/16-3*a*b/8-15*a*c/16+99*a/32+25*b/16-25*c/16-179/16)*g1+(175/16)*g2+(a^3+a^2*b/4+a^2*c/4-11*a^2/4-3*a*b/8-3*a*c/8-7*a/8+25*b/16+25*c/16-117/8)*g3+(-a^3/8-a^2*b/2-7*a^2*c/8+29*a^2/16+3*a*b/4+21*a*c/16-103*a/32-25*b/8+75/16)*g4+(2*a^3+a^2*b/2+a^2*c/2-2*a^2-3*a*b/4-3*a*c/4+a/4+25*b/8+25*c/8-71/8)*g5+(175/16)*g6+(-15*a^3/8+3*a^2*c/8+3*a^2/16-9*a*c/16+95*a/32-25*c/8+67/16)*g7+(7*a^3/8-a^2*b/4-5*a^2*c/8+13*a^2/16+3*a*b/8+15*a*c/16-99*a/32-25*b/16+25*c/16-171/16)*g8+(a^2/4+7*a*b/8+7*a*c/8-17*a/8-21*b/16-21*c/16+309/32)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (175/32)*g0+(9*a^3/8+a^2*b/4+5*a^2*c/8-21*a^2/16-3*a*b/8-15*a*c/16+35*a/32+25*b/16-25*c/16-171/16)*g1+(175/16)*g2+(a^3+a^2*b/4+a^2*c/4-11*a^2/4-3*a*b/8-3*a*c/8-7*a/8+25*b/16+25*c/16-117/8)*g3+(-17*a^3/8-a^2*b/2-7*a^2*c/8+37*a^2/16+3*a*b/4+21*a*c/16-39*a/32-25*b/8+67/16)*g4+(2*a^3+a^2*b/2+a^2*c/2-2*a^2-3*a*b/4-3*a*c/4+a/4+25*b/8+25*c/8-71/8)*g5+(175/16)*g6+(a^3/8+3*a^2*c/8-5*a^2/16-9*a*c/16+31*a/32-25*c/8+75/16)*g7+(-9*a^3/8-a^2*b/4-5*a^2*c/8+21*a^2/16+3*a*b/8+15*a*c/16-35*a/32-25*b/16+25*c/16-179/16)*g8+(a^2/4+7*a*b/8+7*a*c/8-17*a/8-21*b/16-21*c/16+309/32)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_6 (a b c:ℝ) (h:minorZero ![b,a,a,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (1+1-c) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^2*b/2-a^2/2-5*a*b/8+a*c/8+5*a/2-5*b/8+19*c/32-13/32)*g0+(-a^3/4-3*a^2*b/2+21*a^2/16+15*a*b/8-a*c/4-179*a/32+15*b/8-19*c/32-3/32)*g1+(a^3/4+2*a^2*b-29*a^2/16-5*a*b/2+3*a*c/8+259*a/32-27*b/16+19*c/16-89/32)*g2+(-a^3/4-a^2*b/2+5*a^2/16+5*a*b/8-19*a/32+5*b/8+19*c/32-17/16)*g3+(a^3/4+a^2*b-13*a^2/16-5*a*b/4+a*c/8+99*a/32-5*b/4+21/32)*g4+(-a^3/2-2*a^2*b+9*a^2/8+a*b-a*c/4-107*a/16+5*b/2-19/32)*g5+(a^3/2+a^2*b-5*a^2/8-5*a*b/4+19*a/16-5*b/4-19*c/16+63/32)*g6+(a^3/4+a^2*b-13*a^2/16-5*a*b/4+a*c/8+123*a/32+3*b^2/4-11*b/16-c/8-105/32)*g7+(-a^3/4-a^2*b/2+5*a^2/16+5*a*b/8-19*a/32+5*b/8+19*c/32-39/32)*g8
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+a^2-a*b-5*a*c/4+25*a/8-21*b/32+93*c/64-55/64)*g0+(9*a^3/8+3*a^2*b/4+a^2*c/2-3*a^2/2+3*a*b+5*a*c/2-475*a/64+63*b/32-93*c/64+29/64)*g1+(-17*a^3/8-a^2*b-3*a^2*c/4+5*a^2/2-4*a*b-15*a*c/4+675*a/64+b/8+93*c/32-333/64)*g2+(-7*a^3/8+a^2*b/4+a^2/2+a*b-75*a/64+21*b/32+93*c/64-23/32)*g3+(-a^3/8-a^2*b/2-a^2*c/4+a^2/2-2*a*b-5*a*c/4+275*a/64-21*b/16-9/64)*g4+(a^3/4+a^2*b+a^2*c/2+5*a^2/2+21*a*b/4+5*a*c/2-211*a/32+21*b/8-93/64)*g5+(7*a^3/4-a^2*b/2-a^2-2*a*b+75*a/32-21*b/16-93*c/32+127/64)*g6+(-a^3/8-a^2*b/2-a^2*c/4-a^2-7*a*b/2-a*c+323*a/64-5*b^2/8+35*b/16+5*c/4-251/64)*g7+(-7*a^3/8+a^2*b/4+a^2/2+a*b-75*a/64+21*b/32+93*c/64-11/64)*g8
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+a^2-a*b-5*a*c/4+25*a/8-21*b/32+93*c/64-55/64)*g0+(25*a^3/8+3*a^2*b/4+a^2*c/2-2*a^2+3*a*b+5*a*c/2-603*a/64+63*b/32-93*c/64+61/64)*g1+(-33*a^3/8-a^2*b-3*a^2*c/4+3*a^2-4*a*b-15*a*c/4+803*a/64+b/8+93*c/32-365/64)*g2+(9*a^3/8+a^2*b/4+a*b-203*a/64+21*b/32+93*c/64-7/32)*g3+(-17*a^3/8-a^2*b/2-a^2*c/4+a^2-2*a*b-5*a*c/4+403*a/64-21*b/16-41/64)*g4+(17*a^3/4+a^2*b+a^2*c/2+3*a^2/2+21*a*b/4+5*a*c/2-339*a/32+21*b/8-29/64)*g5+(-9*a^3/4-a^2*b/2-2*a*b+203*a/32-21*b/16-93*c/32+63/64)*g6+(-17*a^3/8-a^2*b/2-a^2*c/4-a^2/2-7*a*b/2-a*c+451*a/64-5*b^2/8+35*b/16+5*c/4-283/64)*g7+(9*a^3/8+a^2*b/4+a*b-203*a/64+21*b/32+93*c/64+21/64)*g8
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_7 (a b c:ℝ) (h:minorZero ![b,a,a,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+c-a) (b+1-1) (b+b-0) (b+c-1) (c+1-a) (c+b-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (c+1-a) (c+b-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (1+b-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-10*a^2/3+17*a/18-5*c/18-5/12)*g0+(-2*a^3+2*a^2*c/3+17*a^2/3+a*c/6-77*a/36-5*b/9+5*c/9+5/6)*g1+(5/6-5*c/9)*g2+(2*a^2*c/3-a^2+a*c/6-a/4-5*b/9+5/6)*g3+(a^3-2*a^2*c/3-7*a^2/3-a*c/6+43*a/36+5*b/9-5*c/18-5/12)*g4+(-5*c/18-5/12)*g5+(5/6)*g6+(-a^3-2*a^2*c/3+13*a^2/3+2*a*b/3-a*c/6-61*a/36+b+5*c/18-13/12)*g7+(2*a^3+2*a^2*c/3-23*a^2/3+a*c/6+59*a/36-5*b/9-5/6)*g8+(-a^3+10*a^2/3-17*a/18-5*c/18+5/4)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (2*a^2*b+10*a^2*c/3-8*a^2-5*a*b/2-35*a*c/18+20*a/3+b/2-25*c/54+19/108)*g0+(-4*a^3/3-4*a^2*b-20*a^2*c/3+127*a^2/9+5*a*b+35*a*c/9-457*a/36-b+25*c/27+29/27)*g1+(-4*a^3/3-17*a^2/9+23*a/36+26/27)*g3+(4*a^3/3+2*a^2*b+10*a^2*c/3-55*a^2/9-5*a*b/2-35*a*c/18+217*a/36+b/2-25*c/54-5/4)*g4+(25/108)*g5+(25/54)*g6+(4*a^3/3-2*a^2*b-10*a^2*c/3+59*a^2/9+5*a*b/2+35*a*c/18-313*a/36-b/2+25*c/54+187/108)*g7+(-4*a^3/3+4*a^2*b+20*a^2*c/3-161*a^2/9-5*a*b-35*a*c/9+503*a/36+b-25*c/27+7/18)*g8+(-2*a^2*b-10*a^2*c/3+8*a^2+5*a*b/2+35*a*c/18-20*a/3-b/2+25*c/54+31/108)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (4*a^2*c/3-2*a^2+5*a*c/9-5*a/6-26*c/27+181/108)*g0+(-4*a^3/3-8*a^2*c/3+19*a^2/9-10*a*c/9+83*a/36+52*c/27-52/27)*g1+(-4*a^3/3-17*a^2/9+23*a/36+26/27)*g3+(4*a^3/3+4*a^2*c/3-a^2/9+5*a*c/9-53*a/36-26*c/27+1/4)*g4+(25/108)*g5+(25/54)*g6+(4*a^3/3-4*a^2*c/3+5*a^2/9-5*a*c/9-43*a/36+26*c/27+25/108)*g7+(-4*a^3/3+8*a^2*c/3-53*a^2/9+10*a*c/9-37*a/36-52*c/27+61/18)*g8+(-4*a^2*c/3+2*a^2-5*a*c/9+5*a/6+26*c/27-131/108)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_8 (a b c:ℝ) (h:minorZero ![b,a,c,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (1+1-a) (1+b-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (1+b-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (a+1-a) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-4*a^2*b+6*a^2-24*a*b^3+20*a*b^2*c-102*a*b^2+66*a*b*c+351*a*b-135*a*c^2+261*a*c-999*a/4+16*b^3-4*b^2*c+42*b^2-6*b*c-283*b+81*c^2-225*c+753/4)*g0+(4*a^2*b-6*a^2+24*a*b^3-20*a*b^2*c+102*a*b^2-66*a*b*c-351*a*b+135*a*c^2-261*a*c+999*a/4+8*b^3-10*b^2*c+51*b^2-60*b*c-56*b+27*c^2/2+72*c-219/8)*g1+(-2*a^2*b+3*a^2-12*a*b^3+10*a*b^2*c-51*a*b^2+33*a*b*c+351*a*b/2-135*a*c^2/2+261*a*c/2-999*a/8-4*b^3+2*b^2*c-27*b^2+54*b*c-44*b+27*c^2/2-9*c/2-93/8)*g2+(6*b^2*c-9*b^2-81*c^2/2+108*c-567/8)*g3+(-12*b^3+4*b^2*c-42*b^2+33*b*c+327*b/2-27*c^2+45*c/2-36)*g4+(16*b^3-8*b^2*c+72*b^2-63*b*c-351*b/2+54*c^2-171*c+297/2)*g5+(-8*b^3+8*b^2*c-48*b^2+12*b*c+168*b-54*c^2+126*c-207/2)*g6+(-4*b^3+4*b^2*c-24*b^2+18*b*c+48*b-27*c^2+171*c/2-117/2)*g7+(4*b^3-4*b^2*c+18*b^2-6*b*c-96*b+27*c^2-45*c/2+45/2)*g8+(12*b-18)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (8*a^3+52*a^2*b^2-2*a^2+1487*a*b^2-2223*a*b*c/2-3225*a*b/4-270*a*c-897*a/2-913*b^2+305*b*c/2+6255*b/4+48*c+531)*g0+(-8*a^3-52*a^2*b^2+2*a^2-1539*a*b^2+2223*a*b*c/2+3225*a*b/4+270*a*c+897*a/2-620*b^2+2227*b*c/4-1617*b/8+267*c/2+63/4)*g1+(4*a^3+26*a^2*b^2-a^2+1539*a*b^2/2-2223*a*b*c/4-3225*a*b/8-135*a*c-897*a/4+238*b^2-1109*b*c/4+10681*b/8-183*c/2+1653/4)*g2+(-1545*b*c/4+4635*b/8-225*c/2+675/4)*g3+(26*a*b^2+1543*b^2/2-323*b*c/2-1821*b/2-69*c/2-693/2)*g4+(-34*a*b^2-1999*b^2/2+515*b*c-383*b+150*c-75/2)*g5+(16*a*b^2+600*b^2-323*b*c-921*b/2-69*c-243)*g6+(8*a*b^2+264*b^2-515*b*c/2+677*b/2-75*c+75)*g7+(-8*a*b^2-290*b^2+323*b*c/2+1473*b/2+69*c/2+513/2)*g8+(-10*b^2-120*b-45/2)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (8*a^3+48*a^2*b^2-2*a^2+1156*a*b^2-1157*a*b*c-1417*a*b/2-48*a*c^3+4189*a*c^2/2-5242*a*c+331*a/8-716*b^2+295*b*c+2695*b/2+48*c^3-2527*c^2/2+2924*c+12575/8)*g0+(-8*a^3-48*a^2*b^2+2*a^2-1204*a*b^2+1157*a*b*c+1417*a*b/2+48*a*c^3-4189*a*c^2/2+5242*a*c-331*a/8+12*b^2*c-494*b^2+846*b*c-697*b-12*c^3-833*c^2/4+299*c/4+6375/16)*g1+(4*a^3+24*a^2*b^2-a^2+602*a*b^2-1157*a*b*c/2-1417*a*b/4-24*a*c^3+4189*a*c^2/4-2621*a*c+331*a/16-12*b^2*c+172*b^2-567*b*c+1245*b/2+20*c^3-661*c^2/4-873*c+49361/16)*g2+(12*b^2*c-18*b^2-12*c^3+2507*c^2/4-9205*c/4+33315/16)*g3+(24*a*b^2-12*b^2*c+616*b^2-1141*b*c/2-1041*b/4-12*c^3+841*c^2/2-1415*c/4-2015)*g4+(-32*a*b^2+12*b^2*c-766*b^2+1799*b*c/2+715*b/4+16*c^3-881*c^2+3354*c-2120)*g5+(16*a*b^2+468*b^2-370*b*c-385*b-24*c^3+833*c^2-2028*c-1523/4)*g6+(8*a*b^2+198*b^2-257*b*c-111*b/2-8*c^3+865*c^2/2-6811*c/4+5113/4)*g7+(-8*a*b^2-242*b^2+185*b*c+645*b/2+12*c^3-817*c^2/2+1581*c/4+1601)*g8+(-4*b^2-130*b+4*c^2+10*c-45/2)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_9 (a b c:ℝ) (h:minorZero ![b,c,a,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-c) (b+1-1) (b+b-0) (b+a-1) (a+1-c) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (a+1-c) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (a+1-c) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (a+1-c) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a*b+5*a*c/4-99*a/8+b^2+9*b*c/4-213*b/32-13*c^2/4+69*c/32+4787/128)*g0+(a^2*b/2-a^2/4-15*a*b/16+7*a*c/16+59*a/4-243*b/64-9*c^2/2+1043*c/64-1843/64)*g1+(-a^2/2-37*a/2-9*c/2+45)*g2+(-a^3/4-a^2*b/2+31*a^2/32+15*a*b/16+7*a*c/16+3287*a/128-b^2*c-13*b*c^2/4+213*b*c/32+243*b/64+99*c/64-3043/64)*g3+(-a^2*b/2+a^2/2+15*a*b/16-7*a*c/16-11*a/2+243*b/64+9*c^2/2-755*c/64+3)*g4+(-a^3/4+7*a^2/32+7*a*c/8+2807*a/128-b^2*c-13*b*c^2/4+213*b*c/32-9*c^2/2+283*c/32-99/4)*g5+(a^3/4-7*a^2/32-7*a*c/8-2807*a/128+b^2*c+13*b*c^2/4-213*b*c/32+9*c^2/2-283*c/32+99/4)*g6+(a^3/4+a^2*b-47*a^2/32-15*a*b/8-2583*a/128+b^2*c+13*b*c^2/4-213*b*c/32-243*b/32+2739/128)*g7+(-a^3/4-3*a^2*b/2+79*a^2/32+45*a*b/16-7*a*c/16+4247*a/128-b^2*c-13*b*c^2/4+213*b*c/32+729*b/64+189*c/64-161/4)*g8+(a^2*b/2-a^2-15*a*b/16+7*a*c/16-13*a-243*b/64-189*c/64+2413/128)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-3*a^2/2-21*a*b/8-21*a*c/8+227*a/8-21*b^2/8-21*b*c/4+13*b+63*c^2/8-5*c/2-1045/16)*g0+(-a^3-a^2*b/4-a^2*c/4+9*a^2/4-a*b/2-a*c/2-29*a+61*b/8+21*c^2/2-317*c/8+561/8)*g1+(a^2/2+43*a+21*c/2-209/2)*g2+(-7*a^3/8+a^2*b/4-a^2*c/4+a*b/2-a*c/2-1029*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-61*b/8-109*c/8+919/8)*g3+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+a*b/2+a*c/2+15*a/2-61*b/8-21*c^2/2+233*c/8-10)*g4+(-15*a^3/8-a^2*c/2+11*a^2/4-a*c-805*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c+21*c^2/2-129*c/4+259/4)*g5+(15*a^3/8+a^2*c/2-11*a^2/4+a*c+805*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c-21*c^2/2+129*c/4-259/4)*g6+(-a^3/8-a^2*b/2+5*a^2/2-a*b+909*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c+61*b/4-947/16)*g7+(9*a^3/8+3*a^2*b/4+a^2*c/4-11*a^2/2+3*a*b/2+a*c/2-1477*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-183*b/8+25*c/8+108)*g8+(-a^3-a^2*b/4-a^2*c/4+3*a^2-a*b/2-a*c/2+71*a/2+61*b/8-25*c/8-781/16)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-3*a^2/2-21*a*b/8-21*a*c/8+227*a/8-21*b^2/8-21*b*c/4+13*b+63*c^2/8-5*c/2-1045/16)*g0+(-a^3-a^2*b/4-a^2*c/4+9*a^2/4-a*b/2-a*c/2-29*a+61*b/8+21*c^2/2-317*c/8+561/8)*g1+(a^2/2+43*a+21*c/2-209/2)*g2+(9*a^3/8+a^2*b/4-a^2*c/4-a^2/2+a*b/2-a*c/2-1061*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-61*b/8-109*c/8+923/8)*g3+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+a*b/2+a*c/2+15*a/2-61*b/8-21*c^2/2+233*c/8-10)*g4+(a^3/8-a^2*c/2+9*a^2/4-a*c-837*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c+21*c^2/2-129*c/4+261/4)*g5+(-a^3/8+a^2*c/2-9*a^2/4+a*c+837*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c-21*c^2/2+129*c/4-261/4)*g6+(-17*a^3/8-a^2*b/2+3*a^2-a*b+941*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c+61*b/4-955/16)*g7+(25*a^3/8+3*a^2*b/4+a^2*c/4-6*a^2+3*a*b/2+a*c/2-1509*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-183*b/8+25*c/8+217/2)*g8+(-a^3-a^2*b/4-a^2*c/4+3*a^2-a*b/2-a*c/2+71*a/2+61*b/8-25*c/8-781/16)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

end Erdos1082Second
end
end

section
/-! The symmetry constraints imposed by a pair of equal short chords. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

set_option maxHeartbeats 1000000 in
lemma pair_rigid_0 (a b c d:ℝ) (h:minorZero ![a,a,b,c,d]) (ap:0<a) (al:a<1) (cl:c<1) (dl:d<1) : b=d ∧ c=(a-1)^2 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+c-a) (a+1-1) (a+a-0) (a+c-1) (c+1-a) (c+a-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-d) (a+1-1) (a+a-0) (a+1-b) (c+1-a) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-d) (a+1-1) (a+c-1) (a+1-b) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-d) (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-d) (a+1-1) (a+a-0) (a+1-b) (1+1-d) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-d) (a+1-1) (a+c-1) (a+1-b) (1+1-d) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-d) (a+a-0) (a+c-1) (a+1-b) (1+a-b) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-d) (c+1-a) (c+c-0) (c+1-1) (1+1-d) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-d) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (a-1)*(c-2*a-1)*(b-d)=0 := by linear_combination (1/2)*g0+(-1)*g1+(1/2)*g2+(-1/2)*g3
  have h1 : (a-1)*(c-2*a-1)*(c-(a-1)^2)=0 := by linear_combination (-a/2-d/3+5/2)*g0+(a-2*b/3-35*c/12+7*d/3-7)*g1+(-7*a/4+25*b/12-c/6+d/2-15/4)*g2+(-11*a/4+11*b/4+11*c/4+5*d/6-77/12)*g3+(-3*a+41*c/6+3)*g4+(-2*a+4*b/3+2*c-5/3)*g5+(20/3-4*d/3)*g6+(-13*a/2+b/3-c/6-1/6)*g7+(-a+2*b/3+35*c/12-d/3-19/12)*g8+(11*a/2-11*c/4-2*d/3-13/12)*g9
  have nz:(a-1)*(c-2*a-1)≠0 := mul_ne_zero (by linarith) (by linarith)
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left nz),sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left nz)⟩

set_option maxHeartbeats 1000000 in
lemma pair_rigid_1 (a b c d:ℝ) (h:minorZero ![a,b,a,c,d]) (ap:0<a) (al:a<1) (cl:c<1) (dl:d<1) : c=d ∧ b=(d-1)^2 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-d) (a+1-1) (a+a-0) (a+1-a) (c+1-b) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-d) (a+1-1) (a+c-1) (a+1-a) (c+1-b) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-d) (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-d) (a+1-1) (a+a-0) (a+1-a) (1+1-d) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-d) (a+1-1) (a+c-1) (a+1-a) (1+1-d) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-d) (a+a-0) (a+c-1) (a+1-a) (1+a-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-d) (c+1-b) (c+c-0) (c+1-1) (1+1-d) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-d) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (c+d-3)*(c-d)=0 := by linear_combination (-1/2)*g1+(1)*g2+(-1/2)*g3+(1/2)*g4+(-1)*g5+(1/2)*g6+(1/2)*g7+(-1/2)*g8
  have h1 : (c+d-3)*(b-(d-1)^2)=0 := by linear_combination (1/2-d/2)*g1+(d-1)*g2+(1/2-d/2)*g3+(d/2-1)*g4+(2-d)*g5+(d/2-3/2)*g6+(d/2-1/2)*g7+(3/2-d/2)*g8+(-1/2)*g9
  have nz:c+d-3≠0 := by linarith
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left nz),sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left nz)⟩

end Erdos1082Second
end
end

section
/-! Three equal short chords force all five short chords of a diameter cycle to coincide. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma rigid_value (w:Fin 5→ℝ) (h:minorZero w) (wp:∀i,0≤w i) (wl:∀i,w i<1) (a:ℝ)
    (count:3≤(Finset.univ.filter fun i => w i=a).card) : (∀i,w i=a) ∧ a^2-3*a+1=0 := by
  classical
  obtain ⟨B,sub,n⟩:=Finset.exists_subset_card_eq count
  have e (i:Fin 5) (hi:i∈B) : w i=a := (Finset.mem_filter.mp (sub hi)).2
  have cases : ∀S:Finset (Fin 5), S.card=3 → (0∈S ∧ 1∈S ∧ 2∈S) ∨ (0∈S ∧ 1∈S ∧ 3∈S) ∨ (0∈S ∧ 1∈S ∧ 4∈S) ∨ (0∈S ∧ 2∈S ∧ 3∈S) ∨ (0∈S ∧ 2∈S ∧ 4∈S) ∨ (0∈S ∧ 3∈S ∧ 4∈S) ∨ (1∈S ∧ 2∈S ∧ 3∈S) ∨ (1∈S ∧ 2∈S ∧ 4∈S) ∨ (1∈S ∧ 3∈S ∧ 4∈S) ∨ (2∈S ∧ 3∈S ∧ 4∈S) := by decide
  rcases cases B n with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,a,w 3,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_0 a (w 3) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 3).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_1 a (w 2) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 2).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_2 a (w 2) (w 3) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 2).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_3 a (w 1) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_4 a (w 1) (w 3) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_5 a (w 1) (w 2) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 2).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_6 a (w 0) (w 4) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_7 a (w 0) (w 3) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_8 a (w 0) (w 2) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 2).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,w 1,a,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_9 a (w 0) (w 1) (eq ▸ h) (e _ h1 ▸ wp 2) (e _ h1 ▸ wl 2) (wl 0).le (wl 1).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl

theorem diameter_pentagon_rigid (A:Finset ℝ²) (M:ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (z:Fin 5→A) (inj:Function.Injective z) (edges:∀i,dist (z i).1 (z (i+1)).1=M)
    (r:ℝ) (count:3≤(Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r).card) :
    ∀i,dist (z i).1 (z (i+2)).1=r := by
  classical
  let p (i:Fin 5):=(z i).1
  let w (i:Fin 5):=(M^2)⁻¹*dist (p i) (p (i+2))^2
  have hm : (M^2)⁻¹>0 := inv_pos.mpr (sq_pos_of_pos hM)
  have pos (i) : 0≤w i := mul_nonneg hm.le (sq_nonneg _)
  have ex:=(OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter.diameter_exclusions A M hM bound).1
  have lt (i) : w i<1 := by
    have neq : dist (p i) (p (i+2))≠M := by
      intro de
      have hn : [i,i+1,i+2,i+3,i+4].Nodup := (by decide : ∀j:Fin 5,[j,j+1,j+2,j+3,j+4].Nodup) i
      have no : [z i,z (i+1),z (i+2),z (i+3),z (i+4)].Nodup := hn.map inj
      apply ex ⟨z i,z (i+1),z (i+2),z (i+3),z (i+4),no,edges i,?_,de,?_⟩
      · simpa [add_assoc] using edges (i+1)
      · simpa [add_assoc] using edges (i+3)
    have ds : dist (p i) (p (i+2))<M := lt_of_le_of_ne (bound _ _) neq
    have sq : dist (p i) (p (i+2))^2<M^2 := by nlinarith [dist_nonneg (x:=p i) (y:=p (i+2)),mul_pos (sub_pos.mpr ds) (add_pos_of_pos_of_nonneg hM (dist_nonneg (x:=p i) (y:=p (i+2))))]
    change (M^2)⁻¹*_ < 1
    rw [←inv_mul_cancel₀ (sq_pos_of_pos hM).ne']
    exact mul_lt_mul_of_pos_left sq hm
  let a:=(M^2)⁻¹*r^2
  have inc : (Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r)⊆Finset.univ.filter (fun i => w i=a) := by
    intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [w,a,p,(Finset.mem_filter.mp hi).2]⟩
  have rigid:=rigid_value w (normalized_minor p M hM edges) pos lt a (by have :=Finset.card_le_card inc; omega)
  obtain ⟨j,hj⟩:=Finset.card_pos.mp (show 0<(Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r).card by omega)
  have rn:0≤r := (Finset.mem_filter.mp hj).2 ▸ dist_nonneg
  intro i
  have val:=rigid.1 i
  change (M^2)⁻¹*dist (p i) (p (i+2))^2=(M^2)⁻¹*r^2 at val
  exact (pow_left_inj₀ dist_nonneg rn (by decide : 2≠0)).mp (mul_left_cancel₀ hm.ne' val)
end Erdos1082Second
end
end

section
/-! A symmetric pair of equal short chords determines a second pair and the remaining squared chord. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma pair_chain (w:Fin 5→ℝ) (minors:∀k:Fin 5,minorZero (fun i => w (k+i)))
    (lo:∀i,0<w i) (hi:∀i,w i<1) (k:Fin 5) :
    (w k=w (k+1) → w (k+2)=w (k+4) ∧ w (k+3)=(w k-1)^2) ∧
    (w k=w (k+2) → w (k+3)=w (k+4) ∧ w (k+1)=(w (k+4)-1)^2) := by
  let u (i:Fin 5):=w (k+i)
  have u0:u 0=w k := by simp [u]
  constructor
  · intro eq
    have h1:u 1=u 0 := eq.symm.trans u0.symm
    have form:u=![u 0,u 0,u 2,u 3,u 4] := by funext i; fin_cases i <;> first | exact h1 | rfl
    have h:minorZero u:=minors k
    have v:=pair_rigid_0 _ _ _ _ (form ▸ h) (lo _) (hi _) (hi _) (hi _)
    simpa only [u,add_zero] using v
  · intro eq
    have h2:u 2=u 0 := eq.symm.trans u0.symm
    have form:u=![u 0,u 1,u 0,u 3,u 4] := by funext i; fin_cases i <;> first | exact h2 | rfl
    have h:minorZero u:=minors k
    have v:=pair_rigid_1 _ _ _ _ (form ▸ h) (lo _) (hi _) (hi _) (hi _)
    simpa only [u,add_zero] using v

lemma short_palette (w:Fin 5→ℝ) (minors:∀k:Fin 5,minorZero (fun i => w (k+i)))
    (lo:∀i,0<w i) (hi:∀i,w i<1) :
    (Finset.univ.image w).card=1 ∨ (Finset.univ.image w).card=3 ∨ (Finset.univ.image w).card=5 := by
  classical
  let S:=Finset.univ.image w
  change S.card=1 ∨ S.card=3 ∨ S.card=5
  by_cases bij:Function.Injective w
  · right; right; dsimp [S]; rw [Finset.card_image_of_injective _ bij]; decide
  have dup:∃i j:Fin 5,i≠j ∧ w i=w j := by
    by_contra! h; exact bij (fun i j eq => by_contra fun ne => h i j ne eq)
  obtain ⟨i,j,ij,val⟩:=dup
  have adjacent : ∃k:Fin 5,w k=w (k+1) ∨ w k=w (k+2) := by
    rcases (by decide : ∀i j:Fin 5,i≠j → j=i+1 ∨ i=j+1 ∨ j=i+2 ∨ i=j+2) i j ij with t|t|t|t
    · exact ⟨i,Or.inl (val.trans (congrArg w t))⟩
    · exact ⟨j,Or.inl (val.symm.trans (congrArg w t))⟩
    · exact ⟨i,Or.inr (val.trans (congrArg w t))⟩
    · exact ⟨j,Or.inr (val.symm.trans (congrArg w t))⟩
  obtain ⟨k,hk⟩:=adjacent
  have cov: ∀j:Fin 5,j=k ∨ j=k+1 ∨ j=k+2 ∨ j=k+3 ∨ j=k+4 := (by decide : ∀k j:Fin 5,j=k ∨ j=k+1 ∨ j=k+2 ∨ j=k+3 ∨ j=k+4) k
  have atMost:S.card≤3 := by
    rcases hk with e|e
    · have eq:=(pair_chain w minors lo hi k).1 e
      have sub:S⊆{w k,w (k+2),w (k+3)} := by
        intro x hx; obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
        rcases cov j with rfl|rfl|rfl|rfl|rfl <;> simp [←e,←eq.1]
      exact (Finset.card_le_card sub).trans (Finset.card_le_three)
    · have eq:=(pair_chain w minors lo hi k).2 e
      have sub:S⊆{w k,w (k+1),w (k+4)} := by
        intro x hx; obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
        rcases cov j with rfl|rfl|rfl|rfl|rfl <;> simp [←e,eq.1]
      exact (Finset.card_le_card sub).trans Finset.card_le_three
  by_cases h:S.card=3
  · exact Or.inr (Or.inl h)
  left
  obtain ⟨a,ha,hm⟩:=Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s:=Finset.univ) (t:=S) (n:=2)
    (fun i hi => Finset.mem_image_of_mem w hi) (by change S.card*2<5; omega)
  have base:minorZero w := by simpa only [zero_add] using minors 0
  have all:=(rigid_value w base (fun i => (lo i).le) hi a (by omega)).1
  have se:S={a} := by ext x; simp [S,all,eq_comm]
  simp [se]
end Erdos1082Second
end
end

section
/-! Exact row constraints for an outside point of the symmetric irregular diameter pentagon. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Twelve

def basePoly (a b:ℝ) := a^2*b+b^2-3*a*b-2*b+1
def hcoord (u v:ℝ) := 1+u-v
def vcoord (a u v w:ℝ) := 2*(u+a-w)-a*hcoord u v
def pairing (a u₀ u₁ u₂ v₀ v₁ v₂ l:ℝ) :=
  (4*a-a^2)*(2*(u₀+v₀-l)-hcoord u₀ u₁*hcoord v₀ v₁)-vcoord a u₀ u₁ u₂*vcoord a v₀ v₁ v₂
def palette (a b t:ℝ) : Fin 4→ℝ := ![a,b,(a-1)^2,t]

def admissible (a b t:ℝ) (r:Fin 5→Fin 4) : Prop :=
  let u:=fun i => palette a b t (r i)
  basePoly a b=0 ∧ pairing a (u 0) (u 1) (u 2) (u 0) (u 1) (u 2) 0=0 ∧
    pairing a (u 0) (u 1) (u 2) ((a-1)^2) a 1 (u 3)=0 ∧
    pairing a (u 0) (u 1) (u 2) 1 b b (u 4)=0

def dsq (u v:ℝ²) := (u 0-v 0)^2+(u 1-v 1)^2
lemma dsq_eq (u v:ℝ²) : dsq u v=dist u v^2 := by
  rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]; simp [dsq,Real.dist_eq]

def gpair (a b c d₀ d₁ d₂ e₀ e₁ e₂ h:ℝ) :=
  let g:=a+b-c
  let u:=a+d₀-d₁
  let v:=b+d₀-d₂
  let w:=a+e₀-e₁
  let z:=b+e₀-e₂
  2*b*u*w-g*(u*z+v*w)+2*a*v*z-(4*a*b-g^2)*(d₀+e₀-h)

lemma gram (o e f x y:ℝ²) (s:ℝ) :
    gpair (s*dsq o e) (s*dsq o f) (s*dsq e f)
      (s*dsq o x) (s*dsq e x) (s*dsq f x) (s*dsq o y) (s*dsq e y) (s*dsq f y) (s*dsq x y)=0 := by
  unfold gpair dsq; ring

lemma pair_of_gram {a u v w p q r h:ℝ} (g:gpair 1 a 1 u v w p q r h=0) :
    pairing a u v w p q r h=0 := by
  unfold pairing vcoord hcoord
  unfold gpair at g
  linear_combination -2*g

lemma base_poly_of_minor (a b:ℝ) (H:Erdos1082Second.minorZero ![a,a,b,(a-1)^2,b]) : basePoly a b=0 := by
  have g:=H 1 2 4 1 2 4
  change Erdos1082Second.detThree (1+1-0) (1+a-1) (1+1-b) (a+1-1) (a+a-0) (a+1-b)
    (1+1-b) (1+a-b) (1+1-0)=0 at g
  unfold Erdos1082Second.detThree at g
  unfold basePoly
  linear_combination -1/2*g

theorem actual_row (a b t s:ℝ) (p:Fin 5→ℝ²) (x:ℝ²) (r:Fin 5→Fin 4)
    (table:∀i j,Erdos1082Second.chordTable ![a,a,b,(a-1)^2,b] i j=s*dist (p i) (p j)^2)
    (row:∀i,palette a b t (r i)=s*dist (p i) x^2) : admissible a b t r := by
  have b0:=base_poly_of_minor a b (Erdos1082Second.plane_minors p s _ table)
  have g0:=gram (p 0) (p 1) (p 2) x x s
  have g3:=gram (p 0) (p 1) (p 2) x (p 3) s
  have g4:=gram (p 0) (p 1) (p 2) x (p 4) s
  simp only [dsq_eq,dist_self,zero_pow (by decide : 2≠0),mul_zero,←row,←table,dist_comm x (p 3),dist_comm x (p 4)] at g0 g3 g4
  exact ⟨b0,pair_of_gram g0,pair_of_gram g3,pair_of_gram g4⟩
end Erdos1082Twelve
end
end

section
/-! Univariate obstruction factors for the symmetric irregular pentagon. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Twelve
def factorValue (i:Fin 33) (a:ℝ) : ℝ := ![2*a-1,2*a^2-6*a+1,3*a^2-9*a+4,4*a^2+5*a-3,a^2-4*a+1,a^2-5*a+3,10*a^3-53*a^2+79*a-27,2*a^3-5*a^2-4*a+4,a^3-2*a^2-3*a+1,a^3-3*a^2-a+4,a^3-4*a+1,a^3-5*a^2+6*a-1,a^3-6*a^2+8*a-1,a^3-6*a^2+9*a-3,5*a^4-16*a^3+19*a^2-8*a+1,5*a^4-24*a^3+32*a^2-16*a+4,a^4-2*a^3-3*a^2+1,a^4-4*a^3+2*a^2+4*a-2,a^4-4*a^3+2*a^2+5*a-3,a^4-4*a^3+3*a^2+1,4*a^5-12*a^4-5*a^3+18*a^2-8*a+1,4*a^5-44*a^4+184*a^3-355*a^2+299*a-75,a^5-10*a^4+29*a^3-30*a^2+10*a-1,a^5-4*a^4+a^3+8*a^2-6*a+1,a^5-5*a^4+5*a^3+5*a^2-6*a+1,a^5-9*a^4+23*a^3-5*a^2-30*a+9,10*a^6-48*a^5+64*a^4-20*a^3-a^2-2*a+1,2*a^6-24*a^5+106*a^4-210*a^3+181*a^2-52*a+1,a^6-6*a^5+10*a^4-a^3-5*a^2-2*a+1,a^7-6*a^6+7*a^5+12*a^4-14*a^3-12*a^2+1,2*a^8-17*a^7+45*a^6-16*a^5-89*a^4+76*a^3+45*a^2-37*a+4,4*a^8-44*a^7+189*a^6-396*a^5+414*a^4-200*a^3+42*a^2-6*a+1,5*a^8-44*a^7+151*a^6-261*a^5+250*a^4-150*a^3+71*a^2-25*a+4] i

structure Legal (a b t : ℝ) : Prop where
  pos : 0<a
  lt_one : a<1
  distinct : a≠(a-1)^2
  tb : t≠b
  tc : t≠(a-1)^2

lemma exclude_degenerate {a b t:ℝ} (h:Legal a b t) :
    a≠0 ∧ a-1≠0 ∧ a-2≠0 ∧ a-3≠0 ∧ a-4≠0 ∧ a^2-3*a+1≠0 := by
  have hp:=h.pos; have hl:=h.lt_one
  refine ⟨hp.ne',by linarith,by linarith,by linarith,by linarith,?_⟩
  intro e; apply h.distinct; nlinarith only [e]

end Erdos1082Twelve
end
end

section
namespace Erdos1082Twelve

def word (r:Fin 5→Fin 4):ℕ := 256*(r 0).val+64*(r 1).val+16*(r 2).val+4*(r 3).val+(r 4).val

lemma word_injective : Function.Injective word := by
  intro r s e
  have hr (i:Fin 5) := (r i).isLt
  have hs (i:Fin 5) := (s i).isLt
  have r0:=hr 0; have r1:=hr 1; have r2:=hr 2; have r3:=hr 3; have r4:=hr 4
  have s0:=hs 0; have s1:=hs 1; have s2:=hs 2; have s3:=hs 3; have s4:=hs 4
  unfold word at e
  have eq0: (r 0).val=(s 0).val := by omega
  have eq1: (r 1).val=(s 1).val := by omega
  have eq2: (r 2).val=(s 2).val := by omega
  have eq3: (r 3).val=(s 3).val := by omega
  have eq4: (r 4).val=(s 4).val := by omega
  funext i; apply Fin.ext; fin_cases i <;> assumption

def reflectWord (r:Fin 5→Fin 4): Fin 5→Fin 4 := ![r 3,r 2,r 1,r 0,r 4]

def options (j:Fin 33) : Finset ℕ := ![{163},{83,242,316,964},{198,306,601},{860},{3,523},{301,343,376,724,901},{423},{863},{240},{501},{30,263,493,780,834,949},{163},{540,840},{683},{942},{503,862},{461,821},{762},{500},{263},{781},{940},{243},{441,741},{241},{1020},{502},{1022},{761},{783},{943},{782},{941}] j

lemma options_card (j:Fin 33) : (options j).card≤6 := by fin_cases j <;> decide

def fits (a:ℝ) (r:Fin 5→Fin 4) : Prop := ∃j:Fin 33,factorValue j a=0 ∧ word r∈options j
end Erdos1082Twelve
end

section
/-! A nonregular diameter pentagon with a repeated short chord has a canonical symmetric labeling. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Twelve
open Erdos1082Second

theorem canonical_shape (w:Fin 5→ℝ) (rot:∀k:Fin 5,minorZero (fun i => w (k+i)))
    (lo:∀i,0<w i) (hi:∀i,w i<1) (small:¬Function.Injective w) (nonreg:¬∀i,w i=w 0) :
    ∃k:Fin 5,∃a b:ℝ,0<a ∧ a<1 ∧ a≠b ∧ a≠(a-1)^2 ∧ b≠(a-1)^2 ∧
      0<b ∧ b<1 ∧ 0<(a-1)^2 ∧ (a-1)^2<1 ∧ (fun i:Fin 5 => w (k+i))=![a,a,b,(a-1)^2,b] := by
  classical
  have dup:∃i j:Fin 5,i≠j ∧ w i=w j := by
    by_contra! h; exact small (fun i j eq => by_contra fun ne => h i j ne eq)
  obtain ⟨i,j,ij,val⟩:=dup
  have adjacent : ∃k:Fin 5,w k=w (k+1) := by
    have alt:∃k:Fin 5,w k=w (k+1) ∨ w k=w (k+2) := by
      rcases (by decide : ∀i j:Fin 5,i≠j → j=i+1 ∨ i=j+1 ∨ j=i+2 ∨ i=j+2) i j ij with t|t|t|t
      · exact ⟨i,Or.inl (val.trans (congrArg w t))⟩
      · exact ⟨j,Or.inl (val.symm.trans (congrArg w t))⟩
      · exact ⟨i,Or.inr (val.trans (congrArg w t))⟩
      · exact ⟨j,Or.inr (val.symm.trans (congrArg w t))⟩
    obtain ⟨k,one|two⟩:=alt
    · exact ⟨k,one⟩
    · refine ⟨k+3,?_⟩
      simpa [add_assoc] using ((pair_chain w rot lo hi k).2 two).1
  obtain ⟨k,eq⟩:=adjacent
  obtain ⟨bd,cd⟩:=(pair_chain w rot lo hi k).1 eq
  let a:=w k; let b:=w (k+2)
  have shape : (fun i:Fin 5 => w (k+i))=![a,a,b,(a-1)^2,b] := by
    funext i; fin_cases i
    · exact congrArg w (add_zero k)
    · exact eq.symm
    · rfl
    · exact cd
    · exact bd.symm
  let S:=Finset.univ.image w
  have image_eq : S={a,b,(a-1)^2} := by
    ext q
    constructor
    · intro h; obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp h
      rcases (by decide : ∀k j:Fin 5,j=k ∨ j=k+1 ∨ j=k+2 ∨ j=k+3 ∨ j=k+4) k j with h|h|h|h|h
      · simp [h,a]
      · simp [h,←eq,a]
      · simp [h,b]
      · simp [h,cd,a]
      · simp [h,←bd,b]
    · intro h; simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl|rfl|rfl
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ (k+2))
      · exact Finset.mem_image.mpr ⟨k+3,Finset.mem_univ _,cd⟩
  have three : S.card=3 := by
    have cut : S.card<5 := by
      by_contra! h
      apply small
      apply Set.injOn_univ.mp; simpa only [Finset.coe_univ] using (Finset.injOn_of_card_image_eq (s:=Finset.univ) (f:=w) (by change S.card=5; exact le_antisymm (by simpa using (Finset.card_image_le (f:=w) (s:=Finset.univ))) h))
    rcases short_palette w rot lo hi with one|three|five
    · obtain ⟨v,hv⟩:=Finset.card_eq_one.mp one
      have all (j:Fin 5) : w j=v := Finset.mem_singleton.mp (hv ▸ Finset.mem_image_of_mem w (Finset.mem_univ j))
      exact (nonreg (fun i => (all i).trans (all 0).symm)).elim
    · exact three
    · change S.card=5 at five; omega
  rw [image_eq] at three
  have few (x y:ℝ) (sub:({a,b,(a-1)^2}:Finset ℝ)⊆{x,y}) : False := by
    have c2 := (Finset.card_le_card sub).trans Finset.card_le_two
    omega
  have ab:a≠b := by intro h; apply few b ((a-1)^2); intro x hx; simpa [h] using hx
  have ac:a≠(a-1)^2 := by intro h; apply few a b; intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; grind
  have bc:b≠(a-1)^2 := by intro h; apply few a b; intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; grind
  exact ⟨k,a,b,lo _,hi _,ab,ac,bc,lo _,hi _,cd ▸ lo (k+3),cd ▸ hi (k+3),shape⟩
end Erdos1082Twelve
end
end

section
/-! A rational parametrization of the repeated-chord base equation by a conductor-15 elliptic curve. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Elliptic
open Erdos1082Second Erdos1082Twelve

lemma chord_curve {K:Type*} [Field K] (a b:K) (an:a≠0)
    (eq:a^2*b+b^2-3*a*b-2*b+1=0) :
    let x:=12/a-4
    let y:=12*(2*b+a^2-3*a-2)/a^2
    y^2=x*(x+1)*(x+16) := by
  dsimp
  field_simp [an]
  linear_combination 576*eq

theorem repeated_short_field (K:Subfield ℝ) (w:Fin 5→ℝ)
    (rot:∀k:Fin 5,minorZero (fun i=>w (k+i))) (lo:∀i,0<w i) (hi:∀i,w i<1)
    (mem:∀i,w i∈K) (small:¬Function.Injective w) :
    Real.sqrt 5∈K ∨ ∃x y:K, (8:K)<x ∧ y^2=x*(x+1)*(x+16) := by
  by_cases reg:∀i,w i=w 0
  · left
    have v:w 0=(w 0-1)^2 := (reg (0+3)).symm.trans (((pair_chain w rot lo hi 0).1 (reg (0+1)).symm).2)
    have eq:Real.sqrt 5=3-2*w 0 := by
      have pos:=hi 0
      nlinarith only [v,Real.sq_sqrt (show (0:ℝ)≤5 by norm_num),Real.sqrt_nonneg 5,pos]
    rw [eq];exact K.sub_mem (by exact_mod_cast natCast_mem K 3) (K.mul_mem (by exact_mod_cast natCast_mem K 2) (mem _))
  · right
    obtain ⟨k,a,b,ap,al,ab,ac,bc,bp,bl,cp,cl,shape⟩:=canonical_shape w rot lo hi small reg
    have ma:a∈K := by have h:=congrFun shape 0;rw [←show w (k+0)=a from h];exact mem _
    have mb:b∈K := by have h:=congrFun shape 2;rw [←show w (k+2)=b from h];exact mem _
    have minors:=rot k; rw [shape] at minors
    have eq:=base_poly_of_minor a b minors
    let A:K:=⟨a,ma⟩;let B:K:=⟨b,mb⟩
    have ap':0<A := ap
    have al':A<1 := al
    have Kcurve:A^2*B+B^2-3*A*B-2*B+1=0 := by apply Subtype.ext;exact eq
    refine ⟨12/A-4,12*(2*B+A^2-3*A-2)/A^2,?_,chord_curve A B ap'.ne' Kcurve⟩
    have div:12<12/A := (lt_div_iff₀ ap').mpr (by linarith)
    linarith
end Erdos1082Elliptic
end
end

section
/-! A diameter pentagon with commensurable squared chord lengths has five distinct short chords. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Elliptic
open Erdos1082Second Erdos1082Twelve

lemma injective_rational_chords (w:Fin 5→ℝ) (rot:∀k:Fin 5,minorZero (fun i=>w (k+i)))
    (lo:∀i,0<w i) (hi:∀i,w i<1) (rat:∀i,∃q:ℚ,(q:ℝ)=w i) : Function.Injective w := by
  let K:Subfield ℝ:=(Rat.castHom ℝ).fieldRange
  have mem (i):w i∈K := RingHom.mem_fieldRange.mpr (rat i)
  by_contra sm
  rcases repeated_short_field K w rot lo hi mem sm with sqrt5|⟨x,y,big,eq⟩
  · have ir:Irrational (Real.sqrt 5) := (by decide : Nat.Prime 5).irrational_sqrt
    exact ir (RingHom.mem_fieldRange.mp sqrt5)
  · obtain ⟨u,hu⟩:=RingHom.mem_fieldRange.mp x.2
    obtain ⟨v,hv⟩:=RingHom.mem_fieldRange.mp y.2
    change (u:ℝ)=(x:ℝ) at hu
    change (v:ℝ)=(y:ℝ) at hv
    have pos:(8:ℚ)<u := by exact_mod_cast (hu ▸ big : (8:ℝ)<(u:ℝ))
    have cc:(v:ℝ)^2=(u:ℝ)*((u:ℝ)+1)*((u:ℝ)+16) := by rw [hu,hv];exact congrArg Subtype.val eq
    have c:v^2=u*(u+1)*(u+16) := by exact_mod_cast cc
    have impossible:=conductor_fifteen u v (by linarith) c
    linarith

theorem rational_pentagon_distinct (A:Finset ℝ²) (M:ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (z:Fin 5→A) (inj:Function.Injective z) (edges:∀i,dist (z i).1 (z (i+1)).1=M)
    (commens:∃s:ℝ,0<s ∧ ∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q) :
    Function.Injective (fun i:Fin 5 => dist (z i).1 (z (i+2)).1) := by
  classical
  let p (i:Fin 5):=(z i).1
  let w (i:Fin 5):=(M^2)⁻¹*dist (p i) (p (i+2))^2
  have hm : (M^2)⁻¹>0 := inv_pos.mpr (sq_pos_of_pos hM)
  have pos (i) : 0≤w i := mul_nonneg hm.le (sq_nonneg _)
  have ex:=(OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter.diameter_exclusions A M hM bound).1
  have lt (i) : w i<1 := by
    have neq : dist (p i) (p (i+2))≠M := by
      intro de
      have hn : [i,i+1,i+2,i+3,i+4].Nodup := (by decide : ∀j:Fin 5,[j,j+1,j+2,j+3,j+4].Nodup) i
      have no : [z i,z (i+1),z (i+2),z (i+3),z (i+4)].Nodup := hn.map inj
      apply ex ⟨z i,z (i+1),z (i+2),z (i+3),z (i+4),no,edges i,?_,de,?_⟩
      · simpa [add_assoc] using edges (i+1)
      · simpa [add_assoc] using edges (i+3)
    have ds : dist (p i) (p (i+2))<M := lt_of_le_of_ne (bound _ _) neq
    have sq : dist (p i) (p (i+2))^2<M^2 := by nlinarith [dist_nonneg (x:=p i) (y:=p (i+2)),mul_pos (sub_pos.mpr ds) (add_pos_of_pos_of_nonneg hM (dist_nonneg (x:=p i) (y:=p (i+2))))]
    change (M^2)⁻¹*_ < 1
    rw [←inv_mul_cancel₀ (sq_pos_of_pos hM).ne']
    exact mul_lt_mul_of_pos_left sq hm
  have pos' (i) : 0<w i := by
    have ij:i≠i+2 := (by decide : ∀k:Fin 5,k≠k+2) i
    exact mul_pos hm (sq_pos_of_pos (dist_pos.mpr (Subtype.coe_injective.ne (inj.ne ij))))
  have rot (k:Fin 5) : minorZero (fun i => w (k+i)) := by
    have heq (i:Fin 5) : dist (p (k+i)) (p (k+(i+1)))=M := by simpa [add_assoc,p] using edges (k+i)
    simpa only [w,add_assoc] using normalized_minor (fun i => p (k+i)) M hM heq
  obtain ⟨s,sp,comm⟩:=commens
  obtain ⟨r,hr⟩:=comm (p 0) (z 0).2 (p (0+1)) (z (0+1)).2
  rw [show dist (p 0) (p (0+1))=M from edges 0] at hr
  have rn:(r:ℝ)≠0 := by intro e;rw [e,mul_zero] at hr;exact (sq_pos_of_pos hM).ne' hr
  have rat (i:Fin 5):∃q:ℚ,(q:ℝ)=w i := by
    obtain ⟨q,h⟩:=comm (p i) (z i).2 (p (i+2)) (z (i+2)).2
    refine ⟨q/r,?_⟩
    dsimp only [w];rw [Rat.cast_div,h,hr];field_simp [rn,sp.ne']
  have good:=injective_rational_chords w rot pos' lt rat
  intro i j ee
  exact good (congrArg (fun d:ℝ => (M^2)⁻¹*d^2) ee)
end Erdos1082Elliptic
end
end

open EuclideanGeometry
theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H2 := by
  intro A _ M hm bound z inj edges rat
  exact Erdos1082Elliptic.rational_pentagon_distinct A M hm bound z inj edges rat
