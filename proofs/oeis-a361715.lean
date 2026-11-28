import OMAStatements.S_oeis_a361715

/-!
# OEIS A361715

Peter Bala conjectured the adjacent prime-power congruence for this
binomial sum. His prime-level note (https://oeis.org/A361715/a361715.pdf)
factors each nonzero-index summand into a cubic prefactor and a product
of shifted ratios. Here that factorization is used at arbitrary prime powers. Separate indices divisible by the
scaling prime, then group the difference by their valuations. Only
the final two nonunit groups need weighted reciprocal-sum cancellation.
The unit group is handled by complete residue blocks and two low-level
expansions.

The localization and prime-power reduction infrastructure is adapted
from @physbuzz's A008793 proof (open-math-agents PR 13260) and our
rectangular-box formalization for A352656.
-/

namespace A361715

open Finset OMA.S_oeis_a361715

def summand (n k : ℕ) : ℕ := (n.choose k)^2 * (n+k-1).choose k

def factor {R : Type*} [CommRing R] (x : R) : R := (1-x)^2*(1+x)

def weight (n k : ℕ) : ℚ := ∏ j ∈ Ico 1 k, factor ((n:ℚ)/j)

lemma summand_recur (n k : ℕ) (_hn : 0<n) (hk : k<n) :
    (summand n (k+1):ℚ)*(k+1)^3 = (summand n k:ℚ)*((n:ℚ)-k)^2*(n+k) := by
  have hd := Nat.add_one_mul_choose_eq (n+k-1) k
  rw [show n+k-1+1=n+k by omega] at hd
  have h₁ : ((n+k:ℕ):ℚ)*((n+k-1).choose k:ℚ) =
      ((n+k).choose (k+1):ℚ)*(k+1) := by exact_mod_cast hd
  have h₂ : (n.choose (k+1):ℚ)*(k+1)=(n.choose k:ℚ)*((n:ℚ)-k) := by
    have h := congrArg (fun z : ℕ => (z:ℚ)) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub hk.le] at h
    exact h
  unfold summand
  rw [show n+(k+1)-1=n+k by omega]
  push_cast
  calc
    _ = ((n.choose (k+1):ℚ)*(k+1))^2 * (((n+k).choose (k+1):ℚ)*(k+1)) := by ring
    _ = _ := by rw [h₂,←h₁]; push_cast; ring

lemma weight_succ (n k : ℕ) (hk : 1≤k) :
    weight n (k+1) = weight n k * factor ((n:ℚ)/k) := by
  unfold weight
  rw [prod_Ico_succ_top hk]

lemma summand_formula {n k : ℕ} (hk0 : 0<k) (hk : k≤n) :
    (summand n k:ℚ) = ((n:ℚ)/k)^3 * weight n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k=0
    · subst k
      simp [summand,weight,Nat.choose_one_right]
      ring
    have hk1 : 1≤k := by omega
    have hkn : k<n := by omega
    apply mul_right_cancel₀ (show ((k:ℚ)+1)^3≠0 by positivity)
    rw [summand_recur n k (by omega) hkn, ih (by omega) hkn.le, weight_succ n k hk1]
    unfold factor
    push_cast
    have hkq : (k:ℚ)≠0 := by exact_mod_cast h
    have hsq : (k:ℚ)+1≠0 := by positivity
    field_simp [hkq,hsq]
    ring

lemma sum_summands {n : ℕ} (hn : 0<n) :
    a n = 1 + ∑ k ∈ Ico 1 n, summand n k := by
  change ∑ k ∈ range n, summand n k = _
  have e : insert 0 (Ico 1 n) = range n := by
    ext k
    simp only [mem_insert,mem_Ico,mem_range]
    omega
  rw [←e, sum_insert (by simp)]
  simp [summand]

end A361715

namespace A361715
open Finset

def localRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | ∃ a : ℤ, ∃ b : ℕ, ¬p∣b ∧ q*b=a}
  zero_mem' := ⟨0,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  one_mem' := ⟨1,1,(Fact.out : p.Prime).not_dvd_one,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*d+c*b,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (d:ℚ)*he+(b:ℚ)*hf
  mul_mem' := by
    rintro x y ⟨a,b,hb,he⟩ ⟨c,d,hd,hf⟩
    refine ⟨a*c,b*d,fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd,?_⟩
    push_cast
    linear_combination (y*(d:ℚ))*he+(a:ℚ)*hf
  neg_mem' := by
    rintro x ⟨a,b,hb,h⟩
    exact ⟨-a,b,hb,by push_cast; linarith⟩

lemma linv {p : ℕ} [Fact p.Prime] (x : ℕ) (hx : ¬p∣x) : (x:ℚ)⁻¹ ∈ localRing p := by
  have hn : x≠0 := by rintro rfl; simp at hx
  exact ⟨1,x,hx,by simp [hn]⟩

lemma int_from_local {p : ℕ} [Fact p.Prime] {m : ℤ} {k : ℕ} {u : ℚ}
    (hu : u∈localRing p) (hm : (m:ℚ)=(p:ℚ)^k*u) : (p:ℤ)^k ∣ m := by
  obtain ⟨a,b,hb,he⟩ := hu
  have h : (p:ℤ)^k∣m*(b:ℤ) := by
    refine ⟨a,?_⟩
    exact_mod_cast (show (m:ℚ)*b=(p:ℚ)^k*a by rw [hm,mul_assoc,he])
  have cop : IsCoprime ((p:ℤ)^k) (b:ℤ) := by
    exact (Nat.Coprime.isCoprime ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hb)).pow_left
  exact cop.dvd_of_dvd_mul_right h

lemma first_power {R : Type*} [CommRing R] (z v : R) (k : ℕ) :
    z^2 ∣ (1+z*v)^k-1-z*(k:R)*v := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨u*(1+z*v)+(k:R)*v^2,?_⟩
    rw [pow_succ]; push_cast
    linear_combination (1+z*v)*hu

lemma first_product {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι → R) (k : ι → ℕ) :
    z^2 ∣ (∏ x ∈ s, (1+z*v x)^(k x))-1-z*∑ x ∈ s,(k x:R)*v x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨a,ha⟩ := first_power z (v i) (k i)
    obtain ⟨b,hb⟩ := ih
    rw [prod_insert hi,sum_insert hi]
    let w := ∑ x ∈ s,(k x:R)*v x
    let e := ∏ x ∈ s,(1+z*v x)^(k x)
    change e-1-z*w=z^2*b at hb
    change z^2 ∣ (1+z*v i)^(k i)*e-1-z*((k i:R)*v i+w)
    refine ⟨a*e+b+((k i:R)*v i)*(w+z*b),?_⟩
    linear_combination e*ha+(1+z*(k i:R)*v i)*hb

end A361715

/-! Reduction of these rationals modulo a prime power. -/

namespace A361715
variable {p r : ℕ} [Fact p.Prime]

private lemma reduce_exists (hr : 0<r) (x : localRing p) :
    ∃ z : ZMod (p^r), ∀ (a : ℤ) (b : ℕ), ¬p∣b → (x:ℚ)*b=a → z*b=a := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have ub := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hb
  refine ⟨(a:ZMod (p^r))*(b:ZMod (p^r))⁻¹,?_⟩
  intro c d hd hf
  have eq : a*(d:ℤ)=c*(b:ℤ) := by
    exact_mod_cast (show (a:ℚ)*d=(c:ℚ)*b by rw [← he,← hf]; ring)
  have eq' := congrArg (fun t : ℤ => (t : ZMod (p^r))) eq
  push_cast at eq'
  have bi := ZMod.mul_inv_of_unit _ ub
  linear_combination (b:ZMod (p^r))⁻¹*eq'+(c:ZMod (p^r))*bi

noncomputable def red (hr : 0<r) (x : localRing p) := (reduce_exists hr x).choose

lemma red_spec (hr : 0<r) (x : localRing p) (a : ℤ) (b : ℕ) (hb : ¬p∣b)
    (he : (x:ℚ)*b=a) : red hr x*b=a := (reduce_exists hr x).choose_spec a b hb he

noncomputable def reduce (hr : 0<r) : localRing p →+* ZMod (p^r) where
  toFun := red hr
  map_zero' := by simpa using red_spec (p:=p) hr 0 0 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_one' := by simpa using red_spec (p:=p) hr 1 1 1 (Fact.out : p.Prime).not_dvd_one (by simp)
  map_add' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x+y) (a*d+c*b) (b*d) hbd (by push_cast; linear_combination (d:ℚ)*he+(b:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(d:ZMod (p^r))*hx-(b:ZMod (p^r))*hy
  map_mul' := by
    intro x y
    obtain ⟨a,b,hb,he⟩ := x.property
    obtain ⟨c,d,hd,hf⟩ := y.property
    have hbd : ¬p∣b*d := fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim hb hd
    have hz := red_spec hr (x*y) (a*c) (b*d) hbd (by push_cast; linear_combination (y.val*(d:ℚ))*he+(a:ℚ)*hf)
    have hx := red_spec hr x a b hb he
    have hy := red_spec hr y c d hd hf
    apply ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hbd).mul_left_inj.mp
    push_cast at hz ⊢
    linear_combination hz-(red hr y*(d:ZMod (p^r)))*hx-(a:ZMod (p^r))*hy

lemma ker_reduce (hr : 0<r) (x : localRing p) (h : reduce hr x=0) : (p:localRing p)^r ∣ x := by
  obtain ⟨a,b,hb,he⟩ := x.property
  have hz := red_spec hr x a b hb he
  change red hr x = 0 at h
  rw [h,zero_mul] at hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz.symm
  let inv : localRing p := ⟨(b:ℚ)⁻¹,linv b hb⟩
  have bn : b≠0 := by rintro rfl; simp at hb
  refine ⟨(k:localRing p)*inv,Subtype.ext ?_⟩
  change (x:ℚ)=(p:ℚ)^r*((k:ℚ)*(b:ℚ)⁻¹)
  field_simp [bn]
  have hq := congrArg (fun t : ℤ => (t:ℚ)) hk
  push_cast at hq
  linear_combination he+hq

noncomputable def invNat (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : ¬p∣k) : localRing p :=
  ⟨(k:ℚ)⁻¹,linv k hk⟩

lemma red_inv (hr : 0<r) (k : ℕ) (hk : ¬p∣k) : reduce hr (invNat p k hk)=(k:ZMod (p^r))⁻¹ := by
  have hn : k≠0 := by rintro rfl; simp at hk
  have he := red_spec hr (invNat p k hk) 1 k hk (by simp [invNat,hn])
  have un := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hk
  change red hr _ = _
  apply un.mul_left_inj.mp
  simpa only [ZMod.inv_mul_of_unit _ un,Int.cast_one] using he

end A361715

/-! Inverse-square sums over complete blocks of residues. -/

namespace A361715
open Finset
variable {p r : ℕ} [Fact p.Prime]

noncomputable def safe (p : ℕ) [Fact p.Prime] (x : ℕ) : localRing p :=
  if h : ¬p∣x then invNat p x h else 0

lemma safe_inv (x : ℕ) (h : ¬p∣x) : (x:localRing p)*safe p x = 1 := by
  have nz : x≠0 := by rintro rfl; simp at h
  apply Subtype.ext
  simp [safe,h,invNat,nz]

noncomputable def invSq (P : ℕ) (z : ZMod P) : ZMod P := by classical exact if IsUnit z then z⁻¹^2 else 0

lemma three_sum_zero (modulus : ℕ) [NeZero modulus] (htwo : IsUnit (2 : ZMod modulus)) :
    3*(∑ z : ZMod modulus, invSq modulus z)=0 := by
  classical
  let u := htwo.unit
  have ue : (u:ZMod modulus)=2 := htwo.unit_spec
  have perm := Equiv.sum_comp u.mulLeft (invSq modulus)
  have point (z : ZMod modulus) : 4*invSq modulus (u.mulLeft z)=invSq modulus z := by
    change 4*invSq modulus ((u:ZMod modulus)*z)=_
    rw [ue]
    by_cases hz : IsUnit z
    · simp only [invSq,if_pos hz,if_pos (htwo.mul hz)]
      have a := ZMod.mul_inv_of_unit _ (htwo.mul hz)
      have b := ZMod.mul_inv_of_unit _ hz
      have he : 2*((2:ZMod modulus)*z)⁻¹=z⁻¹ := by
        apply hz.mul_left_inj.mp
        linear_combination a-b
      calc
        4*((2:ZMod modulus)*z)⁻¹^2=(2*((2:ZMod modulus)*z)⁻¹)^2 := by ring
        _ = _ := by rw [he]
    · have bad : ¬ IsUnit ((2:ZMod modulus)*z) := fun h => hz (isUnit_of_mul_isUnit_right h)
      simp [invSq,hz,bad]
  have hs : 4*(∑ z : ZMod modulus, invSq modulus z)=(∑ z : ZMod modulus, invSq modulus z) := by
    conv_lhs => rw [← perm,Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => point z
  linear_combination hs

lemma periodic_sum {P : ℕ} [NeZero P] (hP : 0<P) (n : ℕ) (f : ZMod P → ZMod P) :
    (∑ x ∈ range (n*P), f x)=(n:ZMod P)*∑ z : ZMod P, f z := by
  have block : (∑ x ∈ range P, f x)=∑ z : ZMod P, f z := by
    cases P with
    | zero => omega
    | succ P =>
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      congr 1
      exact ZMod.natCast_zmod_val (n:=P+1) (show ZMod (P+1) from i)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add,block,Nat.cast_succ]
    ring

lemma three_square_local (r N : ℕ) (hr : 0<r) (hN : p^r∣N) (hodd : p≠2) :
    (p:localRing p)^r ∣ 3*(∑ x ∈ range N, (safe p x)^2) := by
  apply ker_reduce hr
  let P := p^r
  have hP : 0<P := pow_pos (Fact.out : p.Prime).pos _
  let _ : NeZero P := ⟨hP.ne'⟩
  have nd2 : ¬p∣2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with bad|bad
    · exact (Fact.out : p.Prime).ne_one bad
    · exact hodd bad
  have hu : IsUnit (2:ZMod P) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr nd2
  have each (x : ℕ) : reduce hr (safe p x)^2=invSq P x := by
    by_cases hx : p∣x
    · have bad := mt (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mp (not_not.mpr hx)
      simp [safe,hx,invSq,P,bad]
    · have good := (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hr).mpr hx
      simp [safe,hx,red_inv,invSq,P,good]
  obtain ⟨n,hn⟩ := hN
  simp only [map_mul,map_ofNat,map_sum,map_pow,each]
  have he : N=n*P := by simpa only [P,mul_comm] using hn
  rw [he,periodic_sum hP]
  linear_combination (n:ZMod P)*three_sum_zero P hu

end A361715

namespace A361715
open Finset
variable {p : ℕ} [Fact p.Prime]

def small (p L : ℕ) := (Ico 1 L).filter (fun x => ¬ p ∣ x)
omit [Fact p.Prime] in
lemma reflection {R : Type*} [AddCommMonoid R] {N : ℕ} (hN : p∣N) (f : ℕ → R) :
    (∑ x ∈ small p N,f (N-x))=∑ x ∈ small p N,f x := by
  apply sum_bij (fun x _ => N-x)
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intro x hx y hy he
    have := mem_Ico.mp (mem_filter.mp hx).1
    have := mem_Ico.mp (mem_filter.mp hy).1
    omega
  · intro x hx
    obtain ⟨hr,hd⟩ := mem_filter.mp hx
    obtain ⟨lo,hi⟩ := mem_Ico.mp hr
    refine ⟨N-x,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro h
    have hh := Nat.dvd_sub hN h
    rw [show N-(N-x)=x by omega] at hh; exact hd hh
  · intros; rfl

end A361715
namespace A361715

open Finset

variable {p : ℕ} [Fact p.Prime]

private lemma valuation_decomp {k : ℕ} (hk : k≠0) :
    k=p^(padicValNat p k)*(k/p^(padicValNat p k)) ∧ ¬p∣k/p^(padicValNat p k) := by
  have d : p^padicValNat p k∣k := (padicValNat_dvd_iff_le hk).2 le_rfl
  have h : p^padicValNat p k*(k/p^padicValNat p k)=k := Nat.mul_div_cancel' d
  refine ⟨h.symm,?_⟩
  rintro ⟨z, hz⟩
  apply pow_succ_padicValNat_not_dvd (p:=p) hk
  refine ⟨z,?_⟩
  nth_rw 1 [←h]
  rw [hz,pow_succ,mul_assoc]

private lemma valuation_lt {r k : ℕ} (hk0 : 0<k) (hk : k<p^r) : padicValNat p k<r := by
  by_contra! h
  have hd : p^r∣k := (padicValNat_dvd_iff_le hk0.ne').2 h
  exact (not_le_of_gt hk) (Nat.le_of_dvd hk0 hd)

noncomputable def localRatio (p r k : ℕ) [Fact p.Prime] : localRing p :=
  (p:localRing p)^(r-padicValNat p k)*safe p (k/p^(padicValNat p k))

lemma localRatio_coe {r k : ℕ} (hk0 : 0<k) (hk : k<p^r) :
    (localRatio p r k:ℚ)=(p:ℚ)^r/k := by
  obtain ⟨he,hnd⟩ := valuation_decomp (p:=p) hk0.ne'
  have hpow : (p:ℚ)^(r-padicValNat p k)*(p:ℚ)^padicValNat p k=(p:ℚ)^r := by
    rw [←pow_add,Nat.sub_add_cancel (valuation_lt (p:=p) hk0 hk).le]
  have hs : (safe p (k/p^padicValNat p k):ℚ)*(k/p^padicValNat p k:ℕ)=1 := by
    have hh := congrArg (fun q : localRing p => (q:ℚ)) (safe_inv (k/p^padicValNat p k) hnd)
    change ((k/p^padicValNat p k:ℕ):ℚ)*(safe p (k/p^padicValNat p k):ℚ)=1 at hh
    simpa only [mul_comm] using hh
  change (p:ℚ)^(r-padicValNat p k)*(safe p (k/p^padicValNat p k):ℚ)=_
  apply (eq_div_iff (show (k:ℚ)≠0 by positivity)).mpr
  rw [show (k:ℚ)=(p:ℚ)^padicValNat p k*((k/p^padicValNat p k:ℕ):ℚ) by exact_mod_cast he]
  linear_combination (p:ℚ)^(r-padicValNat p k)*(p:ℚ)^padicValNat p k*hs + hpow

lemma localRatio_unit {k r : ℕ} (hk : ¬p∣k) :
    localRatio p r k=(p:localRing p)^r*safe p k := by
  simp only [localRatio,padicValNat.eq_zero_of_not_dvd hk,Nat.sub_zero,pow_zero,Nat.div_one]

lemma localRatio_in_p {k r : ℕ} (hk0 : 0<k) (hk : k<p^r) :
    (p:localRing p) ∣ localRatio p r k := by
  rw [localRatio]
  apply dvd_mul_of_dvd_left
  simpa only [pow_one] using
    pow_dvd_pow (p:localRing p) (show 1≤r-padicValNat p k by
      have := valuation_lt (p:=p) hk0 hk
      omega)

lemma localRatio_mul {r k : ℕ} (hk : k≠0) :
    localRatio p r (p*k)=localRatio p (r-1) k := by
  have hp := (Fact.out : p.Prime)
  unfold localRatio
  rw [padicValNat.mul hp.ne_zero hk, padicValNat_self, add_comm 1 (padicValNat p k), pow_succ']
  rw [Nat.mul_div_mul_left _ _ hp.pos]
  rw [show r-(padicValNat p k+1)=r-1-padicValNat p k by omega]

noncomputable def localWeight (p r k : ℕ) [Fact p.Prime] : localRing p :=
  ∏ j ∈ Ico 1 k, factor (localRatio p r j)

noncomputable def unitWeight (p r k : ℕ) [Fact p.Prime] : localRing p :=
  ∏ j ∈ (Ico 1 k).filter (fun j => ¬p∣j), factor ((p:localRing p)^r*safe p j)

lemma localWeight_coe {r k : ℕ} (hk : k≤p^r) :
    (localWeight p r k:ℚ)=weight (p^r) k := by
  unfold localWeight weight
  change (localRing p).subtype _ = _
  rw [map_prod]
  apply prod_congr rfl
  intro j hj
  unfold factor
  rw [map_mul,map_pow,map_sub,map_add,map_one]
  have h := mem_Ico.mp hj
  change (1-(localRatio p r j:ℚ))^2*(1+(localRatio p r j:ℚ))=_
  rw [localRatio_coe (by omega) (h.2.trans_le hk)]
  push_cast; rfl

lemma summand_local {r k : ℕ} (hk0 : 0<k) (hk : k<p^r) :
    (summand (p^r) k:localRing p)=localRatio p r k^3*localWeight p r k := by
  apply Subtype.ext
  change (summand (p^r) k:ℚ)=(localRatio p r k:ℚ)^3*(localWeight p r k:ℚ)
  rw [summand_formula hk0 hk.le,localRatio_coe hk0 hk,localWeight_coe hk.le]
  push_cast; rfl

lemma localWeight_split (r k : ℕ) :
    localWeight p r (p*k)=localWeight p (r-1) k * unitWeight p r (p*k) := by
  let S := Ico 1 (p*k)
  let D := S.filter (fun j => p∣j)
  let E := S.filter (fun j => ¬p∣j)
  have hp := (Fact.out : p.Prime).pos
  have hd : (∏ j ∈ D, factor (localRatio p r j))=localWeight p (r-1) k := by
    symm
    unfold localWeight
    apply prod_bij (fun j _ => p*j)
    · intro j hj
      have h := mem_Ico.mp hj
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hp h.1,Nat.mul_lt_mul_of_pos_left h.2 hp⟩,dvd_mul_right _ _⟩
    · intro i hi j hj h
      exact Nat.eq_of_mul_eq_mul_left hp h
    · intro j hj
      obtain ⟨h, u, hu⟩ := mem_filter.mp hj
      have hh := mem_Ico.mp h
      refine ⟨u,mem_Ico.mpr ⟨?_,?_⟩,hu.symm⟩
      · by_contra! hz
        have : u=0 := by omega
        simp [this] at hu
        omega
      · have key : j<p*k := hh.2
        rw [hu] at key
        exact Nat.lt_of_mul_lt_mul_left key
    · intro j hj
      have h := mem_Ico.mp hj
      rw [localRatio_mul (by omega)]
  have he : (∏ j ∈ E, factor (localRatio p r j))=unitWeight p r (p*k) := by
    unfold unitWeight
    apply prod_congr rfl
    intro j hj
    rw [localRatio_unit (mem_filter.mp hj).2]
  have hprod : (∏ j ∈ D, factor (localRatio p r j))*(∏ j ∈ E, factor (localRatio p r j)) =
      localWeight p r (p*k) := prod_filter_mul_prod_filter_not ..
  rw [←hprod,hd,he]

lemma summand_scale {r k : ℕ} (hr : 0<r) (hk0 : 0<k) (hk : k<p^(r-1)) :
    (summand (p^r) (p*k):localRing p)=
      (summand (p^(r-1)) k:localRing p)*unitWeight p r (p*k) := by
  have hp := (Fact.out : p.Prime).pos
  have hpk : p*k<p^r := by
    have he : p^r=p*p^(r-1) := by nth_rw 1 [show r=r-1+1 by omega]; rw [pow_succ']
    exact he ▸ (Nat.mul_lt_mul_of_pos_left hk hp)
  rw [summand_local (Nat.mul_pos hp hk0) hpk, summand_local hk0 hk,
    localRatio_mul hk0.ne',localWeight_split,mul_assoc]

end A361715
namespace A361715

open Finset

lemma factor_shape {R : Type*} [CommRing R] (x : R) :
    factor x = 1-x-x^2+x^3 := by unfold factor; ring

lemma product_expansion_two {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι→R) :
    z^3 ∣ 2*((∏ i ∈ s, factor (z*v i))-1)+2*z*(∑ i ∈ s,v i) -
      z^2*((∑ i ∈ s,v i)^2-3*(∑ i ∈ s,v i^2)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨u,hu⟩ := ih
    rw [prod_insert hi,sum_insert hi,sum_insert hi]
    let S := ∑ j ∈ s,v j
    let T := ∑ j ∈ s,v j^2
    let a := v i
    let P := ∏ j ∈ s,factor (z*v j)
    let F := factor (z*a)
    change 2*(P-1)+2*z*S-z^2*(S^2-3*T)=z^3*u at hu
    change z^3∣2*(F*P-1)+2*z*(a+S)-z^2*((a+S)^2-3*(a^2+T))
    refine ⟨F*u+2*a^3+2*S*a^2-2*z*S*a^3-(a+z*a^2-z^2*a^3)*(S^2-3*T),?_⟩
    have hf : F=1-z*a-z^2*a^2+z^3*a^3 := by
      dsimp [F]; rw [factor_shape]; ring
    rw [hf]
    linear_combination (1-z*a-z^2*a^2+z^3*a^3)*hu

lemma product_expansion_one {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (z : R) (v : ι→R) :
    z^2 ∣ (∏ i ∈ s, factor (z*v i))-1+z*(∑ i ∈ s,v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨u,hu⟩ := ih
    rw [prod_insert hi,sum_insert hi]
    let S := ∑ j ∈ s,v j
    let a := v i
    let P := ∏ j ∈ s,factor (z*v j)
    let F := factor (z*a)
    change P-1+z*S=z^2*u at hu
    change z^2∣F*P-1+z*(a+S)
    refine ⟨F*u-a^2+z*a^3+(a+z*a^2-z^2*a^3)*S,?_⟩
    have hf : F=1-z*a-z^2*a^2+z^3*a^3 := by
      dsimp [F]; rw [factor_shape]; ring
    rw [hf]
    linear_combination (1-z*a-z^2*a^2+z^3*a^3)*hu

end A361715
namespace A361715

open Finset

lemma prod_congruence {R ι : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (q : R) (a b : ι→R) (h : ∀ i∈s, q∣a i-b i) :
    q∣(∏ i ∈ s,a i)-(∏ i ∈ s,b i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨u,hu⟩ := h i (mem_insert_self i s)
    obtain ⟨v,hv⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    rw [prod_insert hi,prod_insert hi]
    refine ⟨u*(∏ j ∈ s,b j)+a i*v,?_⟩
    linear_combination (∏ j ∈ s,b j)*hu + a i*hv

lemma factor_one_dvd {R : Type*} [CommRing R] (x : R) :
    x ∣ factor x-1 := by
  refine ⟨-1-x+x^2,?_⟩
  rw [factor_shape]
  ring

variable {p : ℕ} [Fact p.Prime]

lemma localWeight_one_mod {r k : ℕ} (hk : k≤p^r) :
    (p:localRing p)∣localWeight p r k-1 := by
  have h := prod_congruence (Ico 1 k) (p:localRing p)
    (fun j => factor (localRatio p r j)) (fun _ => 1) (fun j hj => by
      have he := mem_Ico.mp hj
      exact (localRatio_in_p (by omega) (he.2.trans_le hk)).trans (factor_one_dvd _))
  simpa only [localWeight,prod_const_one] using h

lemma localWeight_filtered {r k m : ℕ} (hm : m≤r+1) (hk : k≤p^r) :
    (p:localRing p)^m ∣ localWeight p r k -
      ∏ j ∈ (Ico 1 k).filter (fun j => p^(r+1-m)∣j), factor (localRatio p r j) := by
  rw [localWeight,prod_filter]
  apply prod_congruence
  intro j hj
  split
  · simp
  rename_i h
  have hj1 := mem_Ico.mp hj
  have vlt : padicValNat p j<r+1-m := by
    by_contra! hv
    exact h ((padicValNat_dvd_iff_le (by omega)).2 hv)
  have d : (p:localRing p)^m∣localRatio p r j := by
    unfold localRatio
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (show m≤r-padicValNat p j by omega)) _
  have := hj1.2.trans_le hk
  exact d.trans (factor_one_dvd _)

lemma filter_multiple_block {P b u : ℕ} (_hP : 0<P) (hu0 : 0<u) (hu : u≤P) :
    (Ico 1 (b*P+u)).filter (fun j => P∣j)=(Ico 1 ((b+1)*P)).filter (fun j => P∣j) := by
  ext j
  simp only [mem_filter,mem_Ico]
  constructor
  · rintro ⟨⟨hj1,hj2⟩,hd⟩
    exact ⟨⟨hj1,by rw [Nat.add_mul,one_mul]; omega⟩,hd⟩
  · rintro ⟨⟨hj1,hj2⟩,k,rfl⟩
    have hk : k≤b := by
      rw [mul_comm (b+1) P] at hj2
      have hh := Nat.lt_of_mul_lt_mul_left hj2
      omega
    have hh : P*k≤b*P := by simpa only [mul_comm] using Nat.mul_le_mul_left P hk
    exact ⟨⟨hj1,by omega⟩,dvd_mul_right _ _⟩

end A361715

namespace A361715

section InverseExpansion

variable {R : Type*} [CommRing R]
variable {x y t : R}

theorem shifted_inverse_relation {a b : R} (ha : a*x=1) (hb : b*y=1) (ht : b=a+t) :
    y-x= -t*x*y := by
  rw [ht] at hb
  linear_combination x*hb-y*ha

theorem inv_first (h : y-x= -t*x*y) :
    t^2 ∣ y-(x-t*x^2) := by
  refine ⟨x^2*y,?_⟩
  linear_combination (1-t*x)*h

theorem inv_second (h : y-x= -t*x*y) :
    t^3 ∣ y-(x-t*x^2+t^2*x^3) := by
  refine ⟨-x^3*y,?_⟩
  linear_combination (1-t*x+t^2*x^2)*h

theorem inv_third (h : y-x= -t*x*y) :
    t^4 ∣ y-(x-t*x^2+t^2*x^3-t^3*x^4) := by
  refine ⟨x^4*y,?_⟩
  linear_combination (1-t*x+t^2*x^2-t^3*x^3)*h

theorem inv_sq_first (h : y-x= -t*x*y) :
    t^2 ∣ y^2-(x^2-2*t*x^3) := by
  have h₁ := (inv_first h).trans (sub_dvd_pow_sub_pow y (x-t*x^2) 2)
  have h₂ : t^2 ∣ (x-t*x^2)^2-(x^2-2*t*x^3) := ⟨x^4,by ring⟩
  simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂

theorem inv_sq_second (h : y-x= -t*x*y) :
    t^3 ∣ y^2-(x^2-2*t*x^3+3*t^2*x^4) := by
  have h₁ := (inv_second h).trans (sub_dvd_pow_sub_pow y (x-t*x^2+t^2*x^3) 2)
  have h₂ : t^3 ∣ (x-t*x^2+t^2*x^3)^2-(x^2-2*t*x^3+3*t^2*x^4) :=
    ⟨-2*x^5 + t*x^6,by ring⟩
  simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂

theorem inv_cube_first (h : y-x= -t*x*y) :
    t^2 ∣ y^3-(x^3-3*t*x^4) := by
  have h₁ := (inv_first h).trans (sub_dvd_pow_sub_pow y (x-t*x^2) 3)
  have h₂ : t^2 ∣ (x-t*x^2)^3-(x^3-3*t*x^4) := ⟨3*x^5-t*x^6,by ring⟩
  simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂

theorem inv_cube_second (h : y-x= -t*x*y) :
    t^3 ∣ y^3-(x^3-3*t*x^4+6*t^2*x^5) := by
  have h₁ := (inv_second h).trans (sub_dvd_pow_sub_pow y (x-t*x^2+t^2*x^3) 3)
  have h₂ : t^3 ∣ (x-t*x^2+t^2*x^3)^3-(x^3-3*t*x^4+6*t^2*x^5) :=
    ⟨-7*x^6+6*t*x^7-3*t^2*x^8+t^3*x^9,by ring⟩
  simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂

end InverseExpansion

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def H (p m K : ℕ) [Fact p.Prime] : localRing p :=
  ∑ j ∈ small p K, (safe p j)^m

private lemma safe_not_dvd_two (hp : p≠2) : ¬p∣2 := by
  intro h
  exact ((Nat.dvd_prime Nat.prime_two).mp h).elim (Fact.out : p.Prime).ne_one hp

private lemma safe_not_dvd_three (hp : p≠3) : ¬p∣3 := by
  intro h
  exact ((Nat.dvd_prime Nat.prime_three).mp h).elim (Fact.out : p.Prime).ne_one hp

lemma dvd_cancel_two (hp : p≠2) {q v : localRing p} (h : q∣2*v) : q∣v := by
  obtain ⟨u,hu⟩ := h
  have eq := safe_inv 2 (safe_not_dvd_two hp)
  norm_cast at eq
  refine ⟨u*safe p 2,?_⟩
  linear_combination safe p 2*hu - v*eq

omit [Fact p.Prime] in
private lemma reflect_unit {K j : ℕ} (hK : p∣K) (hj : j∈small p K) : ¬p∣K-j := by
  have hlt := (mem_Ico.mp (mem_filter.mp hj).1).2
  intro h
  have d := Nat.dvd_sub hK h
  rw [show K-(K-j)=j by omega] at d
  exact (mem_filter.mp hj).2 d

private lemma reflect_inverse {K j : ℕ} (hK : p∣K) (hj : j∈small p K) :
    safe p (K-j)-(-safe p j)= -(K:localRing p)*(-safe p j)*safe p (K-j) := by
  have a := safe_inv j (mem_filter.mp hj).2
  have b := safe_inv (K-j) (reflect_unit hK hj)
  have lo := (mem_Ico.mp (mem_filter.mp hj).1).2.le
  exact shifted_inverse_relation (show (-(j:localRing p))*(-safe p j)=1 by simpa using a)
    b (by rw [Nat.cast_sub lo]; ring)

lemma harmonic_odd_dvd {m K : ℕ} (hp : p≠2) (hK : p∣K) (hm : Odd m) :
    (K:localRing p)∣H p m K := by
  apply dvd_cancel_two hp
  unfold H
  rw [two_mul]
  nth_rw 2 [← reflection hK (fun j => (safe p j)^m)]
  rw [←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := reflect_inverse hK hj
  have d : (K:localRing p)∣safe p (K-j)-(-safe p j) := by
    refine ⟨-(-safe p j)*safe p (K-j),?_⟩
    rw [h]; ring
  have rd := d.trans (sub_dvd_pow_sub_pow (safe p (K-j)) (-safe p j) m)
  rw [hm.neg_pow] at rd
  simpa [sub_neg_eq_add,add_comm] using rd

lemma harmonic_first_reflection {K : ℕ} (hK : p∣K) :
    (K:localRing p)^3 ∣ 2*H p 1 K+(K:localRing p)*H p 2 K+(K:localRing p)^2*H p 3 K := by
  unfold H
  rw [two_mul]
  nth_rw 2 [← reflection hK (fun j => (safe p j)^1)]
  rw [mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib,←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inv_second (reflect_inverse hK hj)
  convert h using 1; ring

lemma harmonic_first_bound {K : ℕ} (hp : p≠2) (hK : p∣K) :
    (K:localRing p)^3 ∣ 2*H p 1 K+(K:localRing p)*H p 2 K := by
  obtain ⟨u,hu⟩ := harmonic_odd_dvd hp hK (by decide : Odd (3:ℕ))
  have d : (K:localRing p)^3 ∣ (K:localRing p)^2*H p 3 K := ⟨u,by rw [hu]; ring⟩
  have h := dvd_sub (harmonic_first_reflection hK) d
  simpa only [add_sub_cancel_right] using h

lemma harmonic_first_reflection_sharp {K : ℕ} (hK : p∣K) :
    (K:localRing p)^4 ∣ 2*H p 1 K+(K:localRing p)*H p 2 K+
      (K:localRing p)^2*H p 3 K+(K:localRing p)^3*H p 4 K := by
  unfold H
  rw [two_mul]
  nth_rw 2 [← reflection hK (fun j => (safe p j)^1)]
  rw [mul_sum,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib,←sum_add_distrib,←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inv_third (reflect_inverse hK hj)
  convert h using 1; ring

lemma harmonic_cube_reflection {K : ℕ} (hK : p∣K) :
    (K:localRing p)^2 ∣ 2*H p 3 K+3*(K:localRing p)*H p 4 K := by
  unfold H
  rw [two_mul]
  nth_rw 2 [← reflection hK (fun j => (safe p j)^3)]
  rw [mul_sum,←sum_add_distrib,←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inv_cube_first (reflect_inverse hK hj)
  convert h using 1; ring

lemma harmonic_range {m K : ℕ} (hm : 0 < m) :
    H p m K = ∑ j ∈ range K,(safe p j)^m := by
  unfold H
  apply sum_subset
  · intro j hj
    exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hj).1).2
  · intro j hj hno
    have hd : p∣j := by
      by_cases z : j=0
      · simp [z]
      by_contra! h
      exact hno (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hj⟩,h⟩)
    simp [safe,hd,hm.ne']

lemma harmonic_square {r K : ℕ} (hr : 0<r) (hK : p^r∣K) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)^r ∣ H p 2 K := by
  have h := three_square_local (p:=p) r K hr hK hp2
  rw [←harmonic_range (by decide : 0<(2:ℕ))] at h
  obtain ⟨u,hu⟩ := h
  have eq := safe_inv 3 (safe_not_dvd_three hp3)
  norm_cast at eq
  refine ⟨u*safe p 3,?_⟩
  linear_combination safe p 3*hu - H p 2 K*eq

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def RBlock (p m P b : ℕ) [Fact p.Prime] : localRing p :=
  ∑ j ∈ small p P, (safe p (b*P+j))^m

private lemma local_zero_of_dvd {j : ℕ} (hj : p∣j) : safe p j=0 := by
  simp [safe,hj]

omit [Fact p.Prime] in
private lemma unit_shift {P b j : ℕ} (hP : p∣P) (hj : ¬ p∣j) : ¬p∣b*P+j :=
  fun h => hj ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hP b)).mpr h)

private lemma inverse_shift {P b j : ℕ} (hP : p∣P) (hj : ¬p∣j) :
    safe p (b*P+j)-safe p j =
       -((b*P:ℕ):localRing p)*safe p j*safe p (b*P+j) := by
  apply shifted_inverse_relation (safe_inv j hj) (safe_inv (b*P+j) (unit_shift hP hj))
  push_cast
  ring

omit [Fact p.Prime] in
theorem completeBlocks {R : Type*} [AddCommMonoid R] {P : ℕ}
    (hP : p ∣ P) (f : ℕ → R) (hf : ∀ x, p ∣ x → f x = 0) (b n : ℕ) :
    (∑ x ∈ Ico (b*P) ((b+n)*P), f x) =
      ∑ i ∈ range n, ∑ j ∈ small p P, f ((b+i)*P+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← Finset.sum_Ico_consecutive f (Nat.mul_le_mul_right P (by omega))
      (Nat.mul_le_mul_right P (show b+n ≤ b+(n+1) by omega)), ih]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show (b+(n+1))*P-(b+n)*P=P by
      rw [show b+(n+1)=b+n+1 by omega,Nat.add_mul,one_mul]; omega]
    symm
    apply sum_subset
    · intro j hj
      exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hj).1).2
    · intro j hj hout
      apply hf
      have jp : p ∣ j := by
        by_cases jz : j=0
        · simp [jz]
        by_contra h
        exact hout (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hj⟩,h⟩)
      exact dvd_add (dvd_mul_of_dvd_right hP _) jp

lemma harmonic_blocks {m P : ℕ} (hm : 0 < m) (hP : p∣P) (n : ℕ) :
    H p m (n*P) = ∑ b ∈ range n, RBlock p m P b := by
  have he := completeBlocks hP (fun j => (safe p j)^m)
    (fun j hj => by rw [local_zero_of_dvd hj,zero_pow hm.ne']) 0 n
  simpa only [harmonic_range hm,zero_mul,zero_add,←range_eq_Ico,RBlock] using he

private lemma to_pow_dvd {R : Type*} [CommRing R] {q u : R} (h : q∣u) (k : ℕ) :
    q^k ∣ u^k := pow_dvd_pow_of_dvd h k

private lemma cast_mul_dvd_pow (s b : ℕ) :
    (p:localRing p)^s∣((b*p^s:ℕ):localRing p) := by
  refine ⟨(b:localRing p),?_⟩
  push_cast
  ring

private lemma square_block_first {P b : ℕ} (hP : p∣P) :
    ((b*P:ℕ):localRing p)^2 ∣
      RBlock p 2 P b-(H p 2 P-2*((b*P:ℕ):localRing p)*H p 3 P) := by
  unfold RBlock H
  rw [mul_sum,←sum_sub_distrib,←sum_sub_distrib]
  exact Finset.dvd_sum fun j hj => inv_sq_first (inverse_shift hP (mem_filter.mp hj).2)

private lemma square_block_second {P b : ℕ} (hP : p∣P) :
    ((b*P:ℕ):localRing p)^3 ∣
      RBlock p 2 P b-(H p 2 P-2*((b*P:ℕ):localRing p)*H p 3 P+
        3*((b*P:ℕ):localRing p)^2*H p 4 P) := by
  unfold RBlock H
  rw [mul_sum,mul_sum,←sum_sub_distrib,←sum_add_distrib,←sum_sub_distrib]
  exact Finset.dvd_sum fun j hj => inv_sq_second (inverse_shift hP (mem_filter.mp hj).2)

private lemma cube_block_second {P b : ℕ} (hP : p∣P) :
    ((b*P:ℕ):localRing p)^3 ∣
      RBlock p 3 P b-(H p 3 P-3*((b*P:ℕ):localRing p)*H p 4 P+
        6*((b*P:ℕ):localRing p)^2*H p 5 P) := by
  unfold RBlock H
  rw [mul_sum,mul_sum,←sum_sub_distrib,←sum_add_distrib,←sum_sub_distrib]
  exact Finset.dvd_sum fun j hj => inv_cube_second (inverse_shift hP (mem_filter.mp hj).2)

lemma square_blocks_mod {s : ℕ} (hs : 0 < s) (hp : p≠2) (n : ℕ) :
    (p:localRing p)^(2*s) ∣ H p 2 (n*p^s)-(n:localRing p)*H p 2 (p^s) := by
  have pd : p∣p^s := dvd_pow_self p hs.ne'
  rw [harmonic_blocks (by decide) pd,
    show (n:localRing p)*H p 2 (p^s)=∑ _ ∈ range n,H p 2 (p^s) by simp,
    ←sum_sub_distrib,mul_comm 2 s,pow_mul]
  apply Finset.dvd_sum
  intro b _
  have hh : (p:localRing p)^s∣H p 3 (p^s) := by
    simpa using harmonic_odd_dvd hp pd (by decide : Odd (3:ℕ))
  have hd : ((p:localRing p)^s)^2 ∣
      (2:localRing p)*((b*p^s:ℕ):localRing p)*H p 3 (p^s) := by
    have hmul := mul_dvd_mul (cast_mul_dvd_pow (p:=p) s b) hh
    simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm] using dvd_mul_of_dvd_right hmul (2:localRing p)
  have he := (to_pow_dvd (cast_mul_dvd_pow (p:=p) s b) 2).trans (square_block_first pd)
  convert dvd_sub he hd using 1 ; ring

private lemma reduced_harmonic_prime {m : ℕ} (hm : 0 < m) (n : ℕ) :
    reduce (p:=p) (r:=1) (by decide) (H p m (n*p)) =
      (n:ZMod (p^1))*∑ z : ZMod (p^1), z⁻¹^m := by
  have hr : 0 < (1:ℕ) := by decide
  have hP : 0 < p^1 := pow_pos (Fact.out : p.Prime).pos _
  let _ : NeZero (p^1) := ⟨hP.ne'⟩
  have hu (x : ℕ) : reduce (p:=p) hr (safe p x)^m = (((x:ZMod (p^1))⁻¹)^m) := by
    by_cases hx : p∣x
    · have hcast : (x:ZMod (p^1))=0 := (ZMod.natCast_eq_zero_iff _ _).2 (by simpa only [pow_one] using hx)
      simp [local_zero_of_dvd hx,hcast,hm.ne', ZMod.inv_zero]
    · simp [safe,hx,red_inv hr]
  rw [harmonic_range hm,map_sum]
  simp only [map_pow,hu]
  rw [show n*p=n*(p^1) by rw [pow_one]]
  exact periodic_sum hP n (fun z => z⁻¹^m)

lemma harmonic_small_power {m : ℕ} (hm : 0 < m) (hlt : m < p-1) (n : ℕ) :
    (p:localRing p) ∣ H p m (n*p) := by
  have hr : 0 < (1:ℕ) := by decide
  let _ : Fact (Nat.Prime (p^1)) := ⟨by simpa only [pow_one] using (Fact.out : p.Prime)⟩
  have eq := Equiv.sum_comp (Equiv.inv (ZMod (p^1))) (fun z : ZMod (p^1) => z^m)
  have hz := FiniteField.sum_pow_lt_card_sub_one (ZMod (p^1)) m (by simpa only [ZMod.card,pow_one] using hlt)
  change (∑ z : ZMod (p^1), z⁻¹^m) = _ at eq
  have he := reduced_harmonic_prime (p:=p) hm n
  rw [eq,hz,mul_zero] at he
  simpa only [pow_one] using ker_reduce hr _ he

lemma harmonic_four_at_prime (hp : 7≤p) (n : ℕ) :
    (p:localRing p)∣H p 4 (n*p) := harmonic_small_power (by decide) (by omega) n

private lemma harmonic_cube_at_prime (hp : 7≤p) (n : ℕ) :
    (p:localRing p)^2∣H p 3 (n*p) := by
  have hK : p∣n*p := dvd_mul_left .. 
  have hb := harmonic_cube_reflection (p:=p) hK
  have hd := harmonic_four_at_prime (p:=p) hp n
  have hs : (p:localRing p)∣((n*p:ℕ):localRing p) := by
    simpa only [pow_one] using cast_mul_dvd_pow (p:=p) 1 n
  have h1 := (pow_dvd_pow_of_dvd hs 2).trans hb
  have h2 : (p:localRing p)^2 ∣ 3*((n*p:ℕ):localRing p)*H p 4 (n*p) := by
    rw [pow_two,mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul hs hd) _
  apply dvd_cancel_two (by omega : p≠2)
  simpa only [add_sub_cancel_right] using dvd_sub h1 h2

lemma square_blocks_sharp (hp : 7≤p) (n : ℕ) :
    (p:localRing p)^3 ∣ H p 2 (n*p)-(n:localRing p)*H p 2 p := by
  rw [harmonic_blocks (by decide) (dvd_refl p),
    show (n:localRing p)*H p 2 p=∑ _ ∈ range n,H p 2 p by simp,
    ←sum_sub_distrib]
  have h3 : (p:localRing p)^2 ∣ H p 3 p := by
    simpa using harmonic_cube_at_prime (p:=p) hp 1
  have h4 : (p:localRing p) ∣ H p 4 p := by
    simpa using harmonic_four_at_prime (p:=p) hp 1
  apply Finset.dvd_sum
  intro b _
  have hs : (p:localRing p)∣((b*p:ℕ):localRing p) := by
    simpa only [pow_one] using cast_mul_dvd_pow (p:=p) 1 b
  have h1 := (pow_dvd_pow_of_dvd hs 3).trans (square_block_second (p:=p) (b:=b) (dvd_refl p))
  have h2 : (p:localRing p)^3 ∣ 2*((b*p:ℕ):localRing p)*H p 3 p := by
    rw [pow_succ',mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul hs h3) _
  have h4' : (p:localRing p)^3 ∣ 3*((b*p:ℕ):localRing p)^2*H p 4 p := by
    rw [pow_succ,mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul (pow_dvd_pow_of_dvd hs 2) h4) _
  convert dvd_add (dvd_sub h1 h2) h4' using 1 ; ring

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

private lemma block_reflected_relation {P b j : ℕ} (hP : p∣P) (hj : j∈small p P) :
    safe p (b*P+(P-j))-(-safe p (b*P+j)) =
      -(((2*b+1)*P:ℕ):localRing p)*(-safe p (b*P+j))*safe p (b*P+(P-j)) := by
  have jp := (mem_filter.mp hj).2
  have jl := (mem_Ico.mp (mem_filter.mp hj).1).2.le
  have jp' := reflect_unit hP hj
  apply shifted_inverse_relation
    (show (-(↑(b*P+j):localRing p))*(-safe p (b*P+j))=1 by
      simpa only [neg_mul_neg] using safe_inv (b*P+j) (unit_shift hP jp))
    (safe_inv _ (unit_shift hP jp'))
  push_cast
  rw [Nat.cast_sub jl]
  ring

private lemma block_cube_reflection {P b : ℕ} (hP : p∣P) :
    (((2*b+1)*P:ℕ):localRing p)^2 ∣
      2*RBlock p 3 P b+3*(((2*b+1)*P:ℕ):localRing p)*RBlock p 4 P b := by
  rw [two_mul (RBlock p 3 P b)]
  unfold RBlock
  nth_rw 2 [← reflection hP (fun j => (safe p (b*P+j))^3)]
  rw [mul_sum,←sum_add_distrib,←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inv_cube_first (block_reflected_relation (b:=b) hP hj)
  convert h using 1 ; ring

private lemma modulus_of_reflection {s : ℕ} (hs : 0 < s) (hp : p≠2) (b d : ℕ)
    (hsq : d≤2*s) (hfour : (p:localRing p)^d ∣
      ((p:localRing p)^s)*RBlock p 4 (p^s) b) :
    (p:localRing p)^d∣RBlock p 3 (p^s) b := by
  have hd := cast_mul_dvd_pow (p:=p) s (2*b+1)
  have hleft : (p:localRing p)^d ∣
        (((2*b+1)*p^s:ℕ):localRing p)^2 :=
    (pow_dvd_pow _ hsq).trans (by
      rw [mul_comm 2 s,pow_mul]
      exact pow_dvd_pow_of_dvd hd 2)
  have he := hleft.trans (block_cube_reflection (b:=b) (dvd_pow_self p hs.ne'))
  have ht : (p:localRing p)^d ∣
      3*(((2*b+1)*p^s:ℕ):localRing p)*RBlock p 4 (p^s) b := by
    obtain ⟨w,hw⟩ := hfour
    refine ⟨3*((2*b+1:ℕ):localRing p)*w,?_⟩
    push_cast
    linear_combination 3*(2*(b:localRing p)+1)*hw
  apply dvd_cancel_two hp
  simpa only [add_sub_cancel_right] using dvd_sub he ht

lemma cube_block_large_zero {s : ℕ} (hs : 3 ≤ s) (hp : p≠2) (b : ℕ) :
    (p:localRing p)^3 ∣ RBlock p 3 (p^s) b :=
  modulus_of_reflection (by omega) hp b 3 (by omega)
    (dvd_mul_of_dvd_left (pow_dvd_pow _ hs) _)

private lemma harmonic_four_p_sq :
    (p:localRing p) ∣ H p 4 (p^2) := by
  have hr : 0 < (1:ℕ) := by decide
  have he := reduced_harmonic_prime (p:=p) (m:=4) (by decide) p
  have hz : (p:ZMod (p^1))=0 := by
    exact (ZMod.natCast_eq_zero_iff _ _).2 (by simp)
  rw [hz,zero_mul,←pow_two] at he
  simpa only [pow_one] using ker_reduce hr _ he

private lemma fourth_block_diff {P : ℕ} (hP : p∣P) (b : ℕ) :
    (p:localRing p)∣RBlock p 4 P b-H p 4 P := by
  unfold H RBlock
  rw [←sum_sub_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inverse_shift (b:=b) hP (mem_filter.mp hj).2
  obtain ⟨q,hq⟩ := dvd_mul_of_dvd_right hP b
  have hcast : (((b*P:ℕ):localRing p))=(p:localRing p)*(q:localRing p) := by exact_mod_cast hq
  apply dvd_trans _ (sub_dvd_pow_sub_pow _ _ 4)
  refine ⟨-(q:localRing p)*safe p j*safe p (b*P+j),?_⟩
  rw [h,hcast]
  ring

lemma cube_block_p_sq_zero (hp : p≠2) (b : ℕ) :
    (p:localRing p)^3 ∣ RBlock p 3 (p^2) b := by
  have hfour : (p:localRing p)∣RBlock p 4 (p^2) b := by
    have he := fourth_block_diff (p:=p) (P:=p^2) (dvd_pow_self p (by decide)) b
    simpa only [sub_add_cancel] using dvd_add he harmonic_four_p_sq
  apply modulus_of_reflection (by decide : 0 < (2:ℕ)) hp b 3 (by decide)
  rw [pow_succ']
  convert mul_dvd_mul (dvd_refl ((p:localRing p)^2)) hfour using 1 ; ring

private lemma harmonic_cube_reflection_sharp {K : ℕ} (hK : p∣K) :
    (K:localRing p)^3 ∣ 2*H p 3 K+3*(K:localRing p)*H p 4 K+6*(K:localRing p)^2*H p 5 K := by
  unfold H
  rw [two_mul]
  nth_rw 2 [← reflection hK (fun j => (safe p j)^3)]
  rw [mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib,←sum_add_distrib]
  apply Finset.dvd_sum
  intro j hj
  have h := inv_cube_second (reflect_inverse hK hj)
  convert h using 1 ; ring

lemma cube_block_three (hp : 7 ≤ p) (b : ℕ) :
    (p:localRing p)^3 ∣
      2*RBlock p 3 p b+3*((2*b+1:ℕ):localRing p)*(p:localRing p)*H p 4 p := by
  have hf : (p:localRing p)∣H p 5 p := by
    simpa only [one_mul] using harmonic_small_power (p:=p) (m:=5) (by decide) (by omega) 1
  have dq : (p:localRing p)^3∣(p:localRing p)^2*H p 5 p := by
    rw [pow_succ]
    exact mul_dvd_mul_left _ hf
  have qr := harmonic_cube_reflection_sharp (p:=p) (dvd_refl p)
  have q := dvd_sub qr (dvd_mul_of_dvd_right dq (6:localRing p))
  have hd : (p:localRing p)∣((b*p:ℕ):localRing p) := by
    simpa only [pow_one] using cast_mul_dvd_pow (p:=p) 1 b
  have dd := (pow_dvd_pow_of_dvd hd 3).trans (cube_block_second (p:=p) (b:=b) (dvd_refl p))
  obtain ⟨h,hh⟩ := dd
  obtain ⟨t,ht⟩ := q
  obtain ⟨v,hv⟩ := dq
  refine ⟨2*h+t+12*(b:localRing p)^2*v,?_⟩
  push_cast at hh ⊢
  linear_combination 2*hh+ht+12*(b:localRing p)^2*hv

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

lemma mul_dvd_power {R : Type*} [CommMonoid R] {q a b : R} {i j : ℕ}
    (h : q^i∣a) (k : q^j∣b) : q^(i+j)∣a*b := by
  rw [pow_add]
  exact mul_dvd_mul h k

lemma cast_pow_dvd {s K : ℕ} (h : p^s∣K) :
    (p:localRing p)^s∣(K:localRing p) := by
  simpa only [Nat.cast_pow] using (Nat.cast_dvd_cast (α:=localRing p) h)

lemma harmonic_one {s K : ℕ} (hs : 0<s) (hK : p^s∣K) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)^(2*s)∣H p 1 K := by
  have pd := (dvd_pow_self p hs.ne').trans hK
  have dk := cast_pow_dvd hK
  have hdiv : (p:localRing p)^(s*3)∣(K:localRing p)^3 := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd dk 3
  have he := (pow_dvd_pow (p:localRing p) (show 2*s ≤ s*3 by omega)).trans
    (hdiv.trans (harmonic_first_bound hp2 pd))
  have hsq : (p:localRing p)^(2*s)∣(K:localRing p)*H p 2 K := by
    simpa only [two_mul] using mul_dvd_power dk (harmonic_square hs hK hp2 hp3)
  apply dvd_cancel_two hp2
  simpa only [add_sub_cancel_right] using dvd_sub he hsq

lemma harmonic_one_sharp {K : ℕ} (hK : p∣K) (hp2 : p≠2)
    (h4 : (p:localRing p)∣H p 4 K) :
    (p:localRing p)^4∣2*H p 1 K+(K:localRing p)*H p 2 K := by
  have dk := Nat.cast_dvd_cast (α:=localRing p) hK
  have hc := (pow_dvd_pow_of_dvd dk 2).trans (harmonic_cube_reflection hK)
  have h3part : (p:localRing p)^2∣3*(K:localRing p)*H p 4 K := by
    rw [mul_assoc]
    apply dvd_mul_of_dvd_right
    simpa only [pow_one] using mul_dvd_power (i:=1) (j:=1)
      (show (p:localRing p)^1∣(K:localRing p) by simpa) (show (p:localRing p)^1∣H p 4 K by simpa)
  have h3 : (p:localRing p)^2∣H p 3 K := by
    apply dvd_cancel_two hp2
    simpa only [add_sub_cancel_right] using dvd_sub hc h3part
  have hbase := (pow_dvd_pow_of_dvd dk 4).trans (harmonic_first_reflection_sharp hK)
  have h₃ : (p:localRing p)^4∣(K:localRing p)^2*H p 3 K :=
    mul_dvd_power (pow_dvd_pow_of_dvd dk 2) h3
  have h₄ : (p:localRing p)^4∣(K:localRing p)^3*H p 4 K :=
    mul_dvd_power (j:=1) (pow_dvd_pow_of_dvd dk 3) (by simpa)
  convert dvd_sub (dvd_sub hbase h₄) h₃ using 1
  ring

lemma unit_expansion (r K : ℕ) :
    (p:localRing p)^(3*r) ∣ 2*(unitWeight p r K-1)+2*(p:localRing p)^r*H p 1 K -
     (p:localRing p)^(2*r)*((H p 1 K)^2-3*H p 2 K) := by
  have h := product_expansion_two (small p K) ((p:localRing p)^r) (safe p)
  simpa only [H,unitWeight,small,pow_one,←pow_mul, Nat.mul_comm] using h

lemma unit_error_lower {r s K : ℕ} (hsr : s≤r) (hs : 0<s)
    (hk : p^s∣K) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)^(r+2*s)∣unitWeight p r K-1 := by
  let q : localRing p := p
  have h1 := harmonic_one hs hk hp2 hp3
  have h2 := harmonic_square hs hk hp2 hp3
  have d1 : q^(r+2*s)∣2*q^r*H p 1 K := by
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_power (dvd_refl (q^r)) h1) _
  have d2aux : q^s∣H p 1 K^2-3*H p 2 K := by
    apply dvd_sub
    · have z := (pow_dvd_pow q (show s≤2*s by omega)).trans h1
      simpa only [pow_two] using dvd_mul_of_dvd_left z (H p 1 K)
    · exact dvd_mul_of_dvd_right h2 _
  have d2 : q^(r+2*s)∣q^(2*r)*((H p 1 K)^2-3*H p 2 K) :=
    (pow_dvd_pow q (show r+2*s≤2*r+s by omega)).trans (mul_dvd_power (dvd_refl _) d2aux)
  have d := (pow_dvd_pow q (show r+2*s≤3*r by omega)).trans (unit_expansion (p:=p) r K)
  apply dvd_cancel_two hp2
  convert dvd_sub (dvd_add d d2) d1 using 1
  dsimp [q]
  ring

lemma unit_error_upper {r s K u d e target : ℕ} (hs : 0<s) (hsr : s≤r)
    (hk : p^s∣K) (hp2 : p≠2) (hp3 : p≠3)
    (hd : target≤r+d) (he : target≤r+s+e) (hq : target≤2*r+4*s) (hbase : target≤3*r)
    (hH1 : (p:localRing p)^d∣2*H p 1 K+(K:localRing p)*H p 2 K)
    (hH2 : (p:localRing p)^e∣H p 2 K-(u:localRing p)*H p 2 (p^s)) :
    (p:localRing p)^target ∣
      2*(unitWeight p r K-1)-
      ((p:localRing p)^r*K-3*(p:localRing p)^(2*r))*((u:localRing p)*H p 2 (p^s)) := by
  let q : localRing p := p
  have err := (pow_dvd_pow q hbase).trans (unit_expansion (p:=p) r K)
  have first : q^target∣q^r*(2*H p 1 K+(K:localRing p)*H p 2 K) :=
    (pow_dvd_pow q hd).trans (mul_dvd_power (dvd_refl _) hH1)
  have h1 := harmonic_one hs hk hp2 hp3
  have sqH1 : q^(4*s)∣(H p 1 K)^2 := by
    rw [show 4*s=2*s*2 by ring,pow_mul]
    exact pow_dvd_pow_of_dvd h1 2
  have quad : q^target∣q^(2*r)*(H p 1 K)^2 :=
    (pow_dvd_pow q hq).trans (mul_dvd_power (dvd_refl _) sqH1)
  have coeK := cast_pow_dvd hk
  have dz : q^(r+s)∣q^r*K-3*q^(2*r) := by
    apply dvd_sub (mul_dvd_power (dvd_refl _) coeK)
    exact dvd_mul_of_dvd_right (pow_dvd_pow q (show r+s≤2*r by omega)) _
  have last : q^target∣(q^r*K-3*q^(2*r))*(H p 2 K-(u:localRing p)*H p 2 (p^s)) :=
    (pow_dvd_pow q he).trans (mul_dvd_power dz hH2)
  convert dvd_add (dvd_add (dvd_sub err first) quad) last using 1
  ring

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def divWeight (p r K m : ℕ) [Fact p.Prime] : localRing p :=
  ∏ j ∈ (Ico 1 K).filter (fun j => m∣j), factor (localRatio p r j)

lemma localWeight_factor {r K : ℕ} :
    localWeight p r K = divWeight p r K p * unitWeight p r K := by
  unfold localWeight divWeight unitWeight
  rw [←prod_filter_mul_prod_filter_not (Ico 1 K) (fun j => p∣j)]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [localRatio_unit (mem_filter.mp hj).2]

lemma divWeight_multiple (r b : ℕ) :
    divWeight p r (p*b) p=localWeight p (r-1) b := by
  have hp := (Fact.out : p.Prime).pos
  symm
  unfold localWeight divWeight
  apply prod_bij (fun j _ => p*j)
  · intro j hj
    have h := mem_Ico.mp hj
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hp h.1,Nat.mul_lt_mul_of_pos_left h.2 hp⟩,dvd_mul_right _ _⟩
  · intro i hi j hj h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro j hj
    obtain ⟨h, u, rfl⟩ := mem_filter.mp hj
    have hh := mem_Ico.mp h
    refine ⟨u,mem_Ico.mpr ⟨?_,Nat.lt_of_mul_lt_mul_left hh.2⟩,rfl⟩
    by_contra! h0
    have e : u=0 := by omega
    rw [e,mul_zero] at hh
    omega
  · intro j hj
    have h := mem_Ico.mp hj
    rw [localRatio_mul (by omega)]

lemma unit_weight_compare {r b j : ℕ} (hr : 3≤r) (h0 : 0<j) (hPj : j ≤ p^(r-2))
    (hk : b*p^(r-2)+j≤p^r) :
    (p:localRing p)^3 ∣
      localWeight p r (b*p^(r-2)+j)-divWeight p r ((b+1)*p^(r-2)) (p^(r-2)) := by
  have h := localWeight_filtered (p:=p) (m:=3) (by omega) hk
  rw [show r+1-3=r-2 by omega, filter_multiple_block (pow_pos (Fact.out : p.Prime).pos _) h0 hPj] at h
  exact h

lemma localWeight_endpoint_control {r b : ℕ} (hr : 3≤r) (hk : (b+1)*p^(r-2) ≤ p^r) :
    (p:localRing p) ∣ divWeight p r ((b+1)*p^(r-2)) (p^(r-2))-1 := by
  have d := localWeight_filtered (p:=p) (m:=3) (by omega) hk
  rw [show r+1-3=r-2 by omega] at d
  change (p:localRing p)^3 ∣ localWeight p r ((b+1)*p^(r-2)) -
    divWeight p r ((b+1)*p^(r-2)) (p^(r-2)) at d
  have d' : (p:localRing p)∣localWeight p r ((b+1)*p^(r-2)) -
    divWeight p r ((b+1)*p^(r-2)) (p^(r-2)) :=
      (show (p:localRing p)∣(p:localRing p)^3 from dvd_pow_self _ (by decide)).trans d
  simpa only [sub_sub_sub_cancel_left] using dvd_sub (localWeight_one_mod hk) d'

lemma unit_weight_level_two {b j : ℕ} (h0 : 0<j) (hj : j≤p) :
    localWeight p 2 (b*p+j)=localWeight p 1 (b+1)*unitWeight p 2 (b*p+j) := by
  rw [localWeight_factor]
  have hd : divWeight p 2 (b*p+j) p=divWeight p 2 ((b+1)*p) p := by
    unfold divWeight
    rw [filter_multiple_block (Fact.out : p.Prime).pos h0 hj]
  rw [hd,mul_comm (b+1) p,divWeight_multiple]

lemma unitWeight_linear (r K : ℕ) :
    (p:localRing p)^(2*r)∣unitWeight p r K-1+(p:localRing p)^r*H p 1 K := by
  have h := product_expansion_one (small p K) ((p:localRing p)^r) (safe p)
  simpa only [H,unitWeight,small,pow_one,←pow_mul, Nat.mul_comm] using h

end A361715
namespace A361715

open Finset OMA.S_oeis_a361715
variable {p : ℕ} [Fact p.Prime]

noncomputable def V (p r : ℕ) [Fact p.Prime] : localRing p :=
  ∑ k ∈ small p (p^r), (safe p k)^3*localWeight p r k

noncomputable def D (p r : ℕ) [Fact p.Prime] : localRing p :=
  ∑ k ∈ Ico 1 (p^(r-1)), (summand (p^(r-1)) k:localRing p)*(unitWeight p r (p*k)-1)

lemma a_diff {r : ℕ} (hr : 0<r) :
    (a (p^r):localRing p)-(a (p^(r-1)):localRing p)=
      (p:localRing p)^(3*r)*V p r+D p r := by
  let S := Ico 1 (p^r)
  let P := S.filter (fun k => p∣k)
  let P' := small p (p^r)
  let f := fun k => (summand (p^r) k:localRing p)
  have hp := (Fact.out : p.Prime).pos
  have e : p^r=p*p^(r-1) := by nth_rw 1 [show r=r-1+1 by omega]; rw [pow_succ']
  have part : (∑ k∈P,f k)+(∑ k∈P',f k)=∑ k∈S,f k :=
    sum_filter_add_sum_filter_not ..
  have divs : (∑ k∈P,f k) =
      ∑ k ∈ Ico 1 (p^(r-1)), (summand (p^(r-1)) k:localRing p)*unitWeight p r (p*k) := by
    symm
    apply sum_bij (fun k _ => p*k)
    · intro k hk
      have h := mem_Ico.mp hk
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hp h.1,?_⟩,dvd_mul_right _ _⟩
      rw [e]
      exact Nat.mul_lt_mul_of_pos_left h.2 hp
    · intro i hi j hj he
      exact Nat.eq_of_mul_eq_mul_left hp he
    · intro k hk
      obtain ⟨h, j, rfl⟩ := mem_filter.mp hk
      obtain ⟨l,u⟩ := mem_Ico.mp h
      refine ⟨j,mem_Ico.mpr ⟨?_,?_⟩,rfl⟩
      · by_contra! bad
        have e : j=0 := by omega
        rw [e,mul_zero] at l
        omega
      · rw [e] at u
        exact Nat.lt_of_mul_lt_mul_left u
    · intro k hk
      have h := mem_Ico.mp hk
      exact (summand_scale hr (by omega) h.2).symm
  have units : (∑ k∈P',f k)=(p:localRing p)^(3*r)*V p r := by
    unfold V
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    obtain ⟨h,hd⟩ := mem_filter.mp hk
    obtain ⟨l,u⟩ := mem_Ico.mp h
    dsimp [f]
    rw [summand_local (by omega) u,localRatio_unit hd,mul_pow,←pow_mul,mul_comm r 3]
    ring
  rw [sum_summands (pow_pos hp r),sum_summands (pow_pos hp (r-1))]
  push_cast
  change (1+∑ k∈S,f k)-(1+_)=_
  rw [←part,divs,units]
  unfold D
  simp only [mul_sub,mul_one,sum_sub_distrib]
  ring

lemma finish {r : ℕ} (hr : 0<r)
    (hV : (p:localRing p)^3∣V p r)
    (hD : (p:localRing p)^(3*r+3)∣D p r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r+3)] := by
  have e := dvd_add (mul_dvd_power (dvd_refl ((p:localRing p)^(3*r))) hV) hD
  rw [←a_diff hr] at e
  obtain ⟨u,hu⟩ := e
  have eq : (((a (p^r):ℤ)-(a (p^(r-1)):ℤ):ℤ):ℚ)=(p:ℚ)^(3*r+3)*(u:ℚ) := by
    have he := congrArg (fun z : localRing p => (z:ℚ)) hu
    push_cast
    exact he
  apply Nat.ModEq.symm
  apply Nat.modEq_iff_dvd.mpr
  push_cast
  exact int_from_local u.property eq

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

private lemma odd_sum (n : ℕ) :
    (∑ b ∈ range n, (2*(b:localRing p)+1))=(n:localRing p)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih]
    push_cast
    ring

lemma weighted_affine_block_sum {n : ℕ} {C : localRing p} {F T : ℕ → localRing p}
    (hp2 : p≠2) (hn : p∣n) (hC : (p:localRing p)^2∣C)
    (hF : ∀ b<n, (p:localRing p)∣F b-1)
    (hT : ∀ b<n, (p:localRing p)^3∣2*T b+C*(2*(b:localRing p)+1)) :
    (p:localRing p)^3∣∑ b∈range n,F b*T b := by
  let q : localRing p := p
  apply dvd_cancel_two hp2
  have h (b : ℕ) (hb : b∈range n) :
      q^3∣2*(F b*T b)+C*(2*(b:localRing p)+1) := by
    have h₁ := dvd_mul_of_dvd_right (hT b (mem_range.mp hb)) (F b)
    have hf := hF b (mem_range.mp hb)
    have h₂ : q^3∣(F b-1)*C*(2*(b:localRing p)+1) := by
      apply dvd_mul_of_dvd_left
      exact mul_dvd_power (i:=1) (j:=2) (by simpa only [pow_one]) hC
    convert dvd_sub h₁ h₂ using 1
    ring
  have hs := Finset.dvd_sum h
  rw [sum_add_distrib,←mul_sum,←mul_sum,odd_sum] at hs
  have hnR : q∣(n:localRing p) := Nat.cast_dvd_cast hn
  have hnPow : q^3∣C*(n:localRing p)^2 := by
    apply mul_dvd_power (i:=2) (j:=1) hC
    simpa only [pow_one,pow_two] using dvd_mul_of_dvd_left hnR (n:localRing p)
  simpa only [add_sub_cancel_right] using dvd_sub hs hnPow

lemma V_blocks {r P n : ℕ} (e : p^r=n*P) (hP : p∣P) :
    V p r=∑ b ∈ range n, ∑ j∈small p P,
      (safe p (b*P+j))^3*localWeight p r (b*P+j) := by
  let f := fun k => (safe p k)^3*localWeight p r k
  have hf (i : ℕ) (hi : p∣i) : f i=0 := by simp [f,safe,hi]
  have erange : V p r=∑ k∈range (p^r), f k := by
    unfold V
    apply sum_subset
    · intro k hk
      exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hk).1).2
    · intro k hk ho
      apply hf
      by_cases z : k=0
      · simp [z]
      by_contra! h
      exact ho (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,mem_range.mp hk⟩,h⟩)
  have hIco : Ico 0 (n*P)=range (n*P) := by ext i; simp
  rw [erange,e,←hIco]
  simpa only [Nat.zero_mul,Nat.zero_add] using completeBlocks hP f hf 0 n

lemma V_high_blocks {r : ℕ} (hr : 3≤r) :
    (p:localRing p)^3 ∣ V p r -
      ∑ b ∈ range (p^2),
        divWeight p r ((b+1)*p^(r-2)) (p^(r-2))*RBlock p 3 (p^(r-2)) b := by
  let P := p^(r-2)
  have hpP : p∣P := dvd_pow_self _ (by omega)
  have e : p^r=p^2*P := by dsimp [P]; rw [←pow_add]; congr 1; omega
  rw [V_blocks e hpP,←sum_sub_distrib]
  apply Finset.dvd_sum
  intro b hb
  unfold RBlock
  rw [mul_sum,←sum_sub_distrib]
  apply Finset.dvd_sum
  intro j hj
  have jl := mem_Ico.mp (mem_filter.mp hj).1
  have hbP : (b+1)*P≤p^r := by
    rw [e]
    exact Nat.mul_le_mul_right _ (by have := mem_range.mp hb; omega)
  have hbJ : b*p^(r-2)+j≤p^r := by
    change b*P+j≤p^r
    rw [Nat.add_mul,one_mul] at hbP
    omega
  have hpt := unit_weight_compare (p:=p) (r:=r) (b:=b) (j:=j) hr (by omega) jl.2.le hbJ
  have h := dvd_mul_of_dvd_right hpt ((safe p (b*P+j))^3)
  convert h using 1
  ring

lemma V_high_zero_from_blocks {r : ℕ} (hr : 3≤r)
    (h : ∀ b<p^2, (p:localRing p)^3∣RBlock p 3 (p^(r-2)) b) :
    (p:localRing p)^3∣V p r := by
  have hd : (p:localRing p)^3 ∣ ∑ b ∈ range (p^2),
      divWeight p r ((b+1)*p^(r-2)) (p^(r-2))*RBlock p 3 (p^(r-2)) b :=
    Finset.dvd_sum fun b hb => dvd_mul_of_dvd_right (h b (mem_range.mp hb)) _
  simpa only [sub_add_cancel] using dvd_add (V_high_blocks hr) hd

lemma V_three_affine (hp2 : p≠2) {C : localRing p}
    (hC : (p:localRing p)^2∣C)
    (hblock : ∀ b<p^2, (p:localRing p)^3 ∣ 2*RBlock p 3 p b+C*(2*(b:localRing p)+1)) :
    (p:localRing p)^3∣V p 3 := by
  let F := fun b => divWeight p 3 ((b+1)*p) p
  have he := weighted_affine_block_sum (p:=p) (n:=p^2) (F:=F)
    (T:=fun b => RBlock p 3 p b) hp2 (dvd_pow_self _ (by decide)) hC (fun b hb => by
      have hh : (b+1)*p^(3-2) ≤ p^3 := by
        have hm := Nat.mul_le_mul_right p (show b+1≤p^2 by omega)
        rw [show 3-2=1 by decide, pow_one,show p^3=p^2*p from pow_succ p 2]
        exact hm
      simpa only [F,show 3-2=1 by decide,pow_one] using
        localWeight_endpoint_control (p:=p) (by decide : 3≤3) hh) hblock
  have hc := V_high_blocks (p:=p) (by decide : 3≤3)
  have hc' : (p:localRing p)^3∣ V p 3-∑ b∈range (p^2),F b*RBlock p 3 p b := by
    simpa only [F,show 3-2=1 by decide,pow_one] using hc
  simpa only [sub_add_cancel] using dvd_add hc' he

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

private lemma inv_shift_prime {b j : ℕ} (hj : ¬p∣j) :
    (p:localRing p)∣safe p (b*p+j)-safe p j := by
  have hd : ¬p∣b*p+j := fun h => hj (Nat.dvd_add_iff_right (dvd_mul_left _ _) |>.mpr h)
  have eq : ((b*p+j:ℕ):localRing p)=(j:localRing p)+((b:localRing p)*p) := by
    push_cast
    ring
  have eh := shifted_inverse_relation (safe_inv j hj) (safe_inv (b*p+j) hd) eq
  refine ⟨-(b:localRing p)*safe p j*safe p (b*p+j),?_⟩
  rw [eh]
  ring

lemma H_one_slice {b j : ℕ} (hp2 : p≠2) :
    (p:localRing p)∣H p 1 (b*p+j)-H p 1 j := by
  have hB : p∣b*p := dvd_mul_left _ _
  have h₁ := (Nat.cast_dvd_cast (α:=localRing p) hB).trans
    (harmonic_odd_dvd hp2 hB (by decide : Odd (1:ℕ)))
  rw [harmonic_range (by decide : 0 < (1:ℕ)),harmonic_range (by decide : 0 < (1:ℕ)),
    sum_range_add, ←harmonic_range (by decide : 0 < (1:ℕ))]
  have h₂ : (p:localRing p) ∣ (∑ i∈range j, safe p (b*p+i)^1) - ∑ i∈range j, safe p i^1 := by
    rw [←sum_sub_distrib]
    apply Finset.dvd_sum
    intro i hi
    simp only [pow_one]
    by_cases h : p∣i
    · have hh := dvd_add hB h
      simp [safe,h,hh]
    · exact inv_shift_prime h
  convert dvd_add h₁ h₂ using 1
  ring

private lemma two_block_point {b j : ℕ} (hb : b<p) (hj : j∈small p p)
    (hSlice : (p:localRing p)∣H p 1 (b*p+j)-H p 1 j) :
    (p:localRing p)^3∣
      (safe p (b*p+j))^3*localWeight p 2 (b*p+j)-
      ((safe p (b*p+j))^3*localWeight p 1 (b+1)-
        (p:localRing p)^2*((safe p j)^3*H p 1 j)) := by
  let q : localRing p := p
  let F := localWeight p 1 (b+1)
  let x := safe p (b*p+j)
  let y := safe p j
  have jl := mem_Ico.mp (mem_filter.mp hj).1
  have w := unit_weight_level_two (p:=p) (b:=b) (j:=j) (by omega) jl.2.le
  have d0 := (pow_dvd_pow q (show 3≤2*2 by decide)).trans (unitWeight_linear (p:=p) 2 (b*p+j))
  have d1 : q^3∣q^2*(H p 1 (b*p+j)-H p 1 j) :=
    mul_dvd_power (i:=2) (j:=1) (dvd_refl _) (by simpa only [pow_one])
  have hu : q^3∣unitWeight p 2 (b*p+j)-1+q^2*H p 1 j := by
    convert dvd_sub d0 d1 using 1
    dsimp [q]
    ring
  have d2 : q^3∣ (x^3*F)*(unitWeight p 2 (b*p+j)-1+q^2*H p 1 j) :=
    dvd_mul_of_dvd_right hu _
  have d3 : q∣x^3-y^3 :=
    (inv_shift_prime (b:=b) (mem_filter.mp hj).2).trans (sub_dvd_pow_sub_pow x y 3)
  have dF : q∣F-1 := localWeight_one_mod (p:=p) (by simpa only [pow_one] using Nat.succ_le_of_lt hb)
  have d4 : q∣x^3*F-y^3 := by
    convert dvd_add (dvd_mul_of_dvd_right dF (x^3)) d3 using 1
    ring
  have dp : q^3∣q^2*((x^3*F-y^3)*H p 1 j) :=
    mul_dvd_power (i:=2) (j:=1) (dvd_refl _) (by
      simpa only [pow_one] using dvd_mul_of_dvd_left d4 (H p 1 j))
  rw [w]
  change q^3∣x^3*(F*unitWeight p 2 (b*p+j))-(x^3*F-q^2*(y^3*H p 1 j))
  convert dvd_sub d2 dp using 1
  ring

lemma V_two_affine (hp2 : p≠2) {C : localRing p}
    (hC : (p:localRing p)^2∣C)
    (hblock : ∀ b<p, (p:localRing p)^3 ∣ 2*RBlock p 3 p b+C*(2*(b:localRing p)+1))
    (hSlice : ∀ b<p, ∀ j∈small p p, (p:localRing p)∣H p 1 (b*p+j)-H p 1 j) :
    (p:localRing p)^3∣V p 2 := by
  let F := fun b => localWeight p 1 (b+1)
  let q : localRing p := p
  let A := ∑ b∈range p,F b*RBlock p 3 p b
  let B := ∑ j∈small p p,(safe p j)^3*H p 1 j
  have hd : q^3∣A := weighted_affine_block_sum hp2 (dvd_refl _) hC (fun b hb =>
    localWeight_one_mod (p:=p) (by simpa only [pow_one] using Nat.succ_le_of_lt hb)) hblock
  have d : q^3∣V p 2-(A-q^3*B) := by
    rw [V_blocks (by rw [pow_two]) (dvd_refl p)]
    have e (b : ℕ) (hb : b∈range p) :
        q^3∣(∑ j∈small p p,(safe p (b*p+j))^3*localWeight p 2 (b*p+j))-
          (F b*RBlock p 3 p b-q^2*B) := by
      unfold RBlock B
      rw [mul_sum,mul_sum,←sum_sub_distrib,←sum_sub_distrib]
      apply Finset.dvd_sum
      intro j hj
      have hh := two_block_point (mem_range.mp hb) hj (hSlice b (mem_range.mp hb) j hj)
      convert hh using 1
      dsimp [F,q]
      ring
    have hh := Finset.dvd_sum e
    rw [sum_sub_distrib,sum_sub_distrib] at hh
    have count : (∑ _∈range p,q^2*B)=q^3*B := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      dsimp [q]
      ring
    rw [count] at hh
    exact hh
  have hz : q^3∣A-q^3*B := dvd_sub hd (dvd_mul_right _ _)
  simpa only [sub_add_cancel] using dvd_add d hz

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def DTerm (p r k : ℕ) [Fact p.Prime] : localRing p :=
  (summand (p^(r-1)) k:localRing p)*(unitWeight p r (p*k)-1)

noncomputable def DShell (p r s : ℕ) [Fact p.Prime] : localRing p :=
  ∑ u∈small p (p^(r-s)), (safe p u)^3*localWeight p (r-1) (p^(s-1)*u)*
    (unitWeight p r (p^s*u)-1)

lemma padicVal_mul_pow_unit {t u : ℕ} (hu : ¬p∣u) :
    padicValNat p (p^t*u)=t := by
  have h0 : u≠0 := by rintro rfl; exact hu (dvd_zero _)
  have hp := (Fact.out : p.Prime).pos
  rw [padicValNat.mul (pow_pos hp _).ne' h0,padicValNat.prime_pow,padicValNat.eq_zero_of_not_dvd hu,add_zero]

lemma localRatio_mul_pow_unit {r t u : ℕ} (hu : ¬p∣u) :
    localRatio p r (p^t*u)=(p:localRing p)^(r-t)*safe p u := by
  have hp := (Fact.out : p.Prime).pos
  rw [localRatio,padicVal_mul_pow_unit hu,Nat.mul_div_cancel_left u (pow_pos hp _)]

lemma D_shell_exact {r s : ℕ} (hs : 0<s) (hsr : s<r) :
    (∑ k∈(Ico 1 (p^(r-1))).filter (fun k => padicValNat p k+1=s), DTerm p r k) =
      (p:localRing p)^(3*(r-s))*DShell p r s := by
  let t := s-1
  have hpt : 0<p^t := pow_pos (Fact.out : p.Prime).pos _
  have et : p^t*p^(r-s)=p^(r-1) := by rw [←pow_add]; congr 1; dsimp [t]; omega
  have etc : p*p^t=p^s := by rw [←pow_succ']; congr 1; dsimp [t]; omega
  unfold DShell
  rw [mul_sum]
  symm
  apply sum_bij (fun u _ => p^t*u)
  · intro u hu
    obtain ⟨h,hd⟩ := mem_filter.mp hu
    obtain ⟨l,hi⟩ := mem_Ico.mp h
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.mul_pos hpt l,?_⟩,?_⟩
    · rw [←et]
      exact Nat.mul_lt_mul_of_pos_left hi hpt
    · rw [padicVal_mul_pow_unit hd]
      dsimp [t]
      omega
  · intro u _ v _ hh
    exact Nat.eq_of_mul_eq_mul_left hpt hh
  · intro k hk
    obtain ⟨h,ht⟩ := mem_filter.mp hk
    obtain ⟨l,hi⟩ := mem_Ico.mp h
    obtain ⟨decomp,pu⟩ := valuation_decomp (p:=p) (show k≠0 by omega)
    have te : padicValNat p k=t := by dsimp [t]; omega
    rw [te] at decomp pu
    have pp : k/p^t < p^(r-s) := by
      rw [decomp,←et] at hi
      exact Nat.lt_of_mul_lt_mul_left hi
    exact ⟨k/p^t,mem_filter.mpr ⟨mem_Ico.mpr ⟨by
      have z : k/p^t≠0 := fun e => by rw [e,mul_zero] at decomp; omega
      exact Nat.one_le_iff_ne_zero.mpr z,pp⟩,pu⟩,decomp.symm⟩
  · intro u hu
    obtain ⟨h,hd⟩ := mem_filter.mp hu
    obtain ⟨l,hi⟩ := mem_Ico.mp h
    have h0 : 0<p^t*u := Nat.mul_pos hpt l
    have hb : p^t*u<p^(r-1) := by rw [←et]; exact Nat.mul_lt_mul_of_pos_left hi hpt
    unfold DTerm
    rw [summand_local h0 hb,localRatio_mul_pow_unit hd,mul_pow,←pow_mul,
      ←mul_assoc p (p^t) u,etc]
    have ee : (r-1-t)*3=3*(r-s) := by dsimp [t]; omega
    rw [ee]
    ring

lemma D_term_low {r k : ℕ} (hp2 : p≠2) (hp3 : p≠3) (hk : k∈Ico 1 (p^(r-1)))
    (hlo : padicValNat p k+1 ≤ r-3) :
    (p:localRing p)^(3*r+3)∣DTerm p r k := by
  obtain ⟨k0,kh⟩ := mem_Ico.mp hk
  let s := padicValNat p k+1
  have s0 : 0<s := by dsimp [s]; omega
  have hs : s≤r-3 := hlo
  have dv : p^s∣p*k := by
    dsimp [s]
    rw [pow_succ']
    exact Nat.mul_dvd_mul (dvd_refl p)
      ((padicValNat_dvd_iff_le (show k≠0 by omega)).2 le_rfl)
  have hl := unit_error_lower (show s≤r by omega) s0 dv hp2 hp3
  have d : (p:localRing p)^(r-s)∣localRatio p (r-1) k := by
    unfold localRatio
    have ee : r-1-padicValNat p k=r-s := by dsimp [s]; omega
    rw [ee]
    exact dvd_mul_right _ _
  have dc : (p:localRing p)^(3*(r-s))∣(summand (p^(r-1)) k:localRing p) := by
    rw [summand_local (by omega) kh, mul_comm 3 (r-s),pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd d 3) _
  exact (pow_dvd_pow _ (show 3*r+3≤3*(r-s)+(r+2*s) by omega)).trans (mul_dvd_power dc hl)

lemma D_from_shells {r : ℕ} (hr : 2≤r) (hp2 : p≠2) (hp3 : p≠3)
    (ht : (p:localRing p)^(3*r)∣DShell p r (r-1))
    (hn : 3≤r → (p:localRing p)^(3*r-3)∣DShell p r (r-2)) :
    (p:localRing p)^(3*r+3)∣D p r := by
  let S := Ico 1 (p^(r-1))
  let v := fun k => padicValNat p k+1
  let T := S.filter (fun k => v k=r-1)
  let M := (S.filter fun k => v k≠r-1).filter (fun k => v k=r-2)
  let L := (S.filter fun k => v k≠r-1).filter (fun k => v k≠r-2)
  have p1 : (∑ k∈T,DTerm p r k)+(∑ k∈S.filter (fun k => v k≠r-1),DTerm p r k)=D p r :=
    sum_filter_add_sum_filter_not ..
  have p2 : (∑ k∈M,DTerm p r k)+(∑ k∈L,DTerm p r k)=
      ∑ k∈S.filter (fun k => v k≠r-1),DTerm p r k :=
    sum_filter_add_sum_filter_not ..
  have htop : (p:localRing p)^(3*r+3)∣∑ k∈T,DTerm p r k := by
    change (p:localRing p)^(3*r+3)∣∑ k∈S.filter (fun k => padicValNat p k+1=r-1),DTerm p r k
    rw [D_shell_exact (by omega : 0<r-1) (by omega : r-1<r)]
    have ee : 3*(r-(r-1))=3 := by omega
    rw [ee,show 3*r+3=3+3*r by omega]
    exact mul_dvd_power (dvd_refl _) ht
  have hmid : (p:localRing p)^(3*r+3)∣∑ k∈M,DTerm p r k := by
    by_cases h3 : 3≤r
    · have eq : M=S.filter (fun k => padicValNat p k+1=r-2) := by
        ext k
        simp only [M,v,mem_filter]
        constructor
        · intro h; exact ⟨h.1.1,h.2⟩
        · intro h; exact ⟨⟨h.1,by omega⟩,h.2⟩
      rw [eq,show S=Ico 1 (p^(r-1)) from rfl,D_shell_exact (by omega : 0<r-2) (by omega : r-2<r)]
      have ee : 3*(r-(r-2))=6 := by omega
      rw [ee,show 3*r+3=6+(3*r-3) by omega]
      exact mul_dvd_power (dvd_refl _) (hn h3)
    · have e : M=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro k hk
        have h := (mem_filter.mp hk).2
        dsimp [v] at h
        omega
      simp [e]
  have hlo : (p:localRing p)^(3*r+3)∣∑ k∈L,DTerm p r k := by
    apply Finset.dvd_sum
    intro k hk
    have hf := mem_filter.mp (show k∈(S.filter (fun k => v k≠r-1)).filter (fun k => v k≠r-2) from hk)
    obtain ⟨h,h₁⟩ := mem_filter.mp hf.1
    have h₂ := hf.2
    have kh := mem_Ico.mp h
    have vl := valuation_lt (p:=p) (show 0<k by omega) kh.2
    apply D_term_low hp2 hp3 h
    dsimp [v] at h₁ h₂
    omega
  rw [←p1,←p2]
  exact dvd_add htop (dvd_add hmid hlo)

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

noncomputable def WH (p r s m : ℕ) [Fact p.Prime] : localRing p :=
  ∑ u∈small p (p^(r-s)), (safe p u)^m*localWeight p (r-1) (p^(s-1)*u)

lemma weighted_harmonic_mod {r s m : ℕ} (hs : 0<s) (hsr : s<r) :
    (p:localRing p)∣WH p r s m-H p m (p^(r-s)) := by
  unfold WH H
  rw [←sum_sub_distrib]
  apply Finset.dvd_sum
  intro u hu
  have hu' := (mem_Ico.mp (mem_filter.mp hu).1).2
  have e : p^(s-1)*p^(r-s)=p^(r-1) := by rw [←pow_add]; congr 1; omega
  have hu'' : p^(s-1)*u≤p^(r-1) := by
    rw [←e]
    exact Nat.mul_le_mul_left _ hu'.le
  have he := dvd_mul_of_dvd_right (localWeight_one_mod hu'') ((safe p u)^m)
  convert he using 1
  ring

lemma weighted_harmonic_one {r s : ℕ} (hs : 0<s) (hsr : s<r) (hp2 : p≠2) :
    (p:localRing p)∣WH p r s 1 := by
  have P : p∣p^(r-s) := dvd_pow_self _ (by omega)
  have d := (Nat.cast_dvd_cast (α:=localRing p) P).trans
    (harmonic_odd_dvd hp2 P (by decide : Odd (1:ℕ)))
  simpa only [sub_add_cancel] using dvd_add (weighted_harmonic_mod (m:=1) hs hsr) d

lemma weighted_harmonic_two {r s : ℕ} (hs : 0<s) (hsr : s<r) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)∣WH p r s 2 := by
  have P : p∣p^(r-s) := dvd_pow_self _ (by omega)
  have d : (p:localRing p)∣H p 2 (p^(r-s)) := by
    simpa only [pow_one] using harmonic_square (p:=p) (show 0<(1:ℕ) by decide) (by simpa only [pow_one]) hp2 hp3
  simpa only [sub_add_cancel] using dvd_add (weighted_harmonic_mod (m:=2) hs hsr) d

lemma shell_cancel {r s target : ℕ} (hp2 : p≠2)
    (hMain : ∀ u∈small p (p^(r-s)), (p:localRing p)^target ∣
      2*(unitWeight p r (p^s*u)-1)-
      ((p:localRing p)^r*((p^s*u:ℕ):localRing p)-3*(p:localRing p)^(2*r))*
        ((u:localRing p)*H p 2 (p^s)))
    (hA : (p:localRing p)^target∣(p:localRing p)^(r+s)*H p 2 (p^s)*WH p r s 1)
    (hB : (p:localRing p)^target∣3*(p:localRing p)^(2*r)*H p 2 (p^s)*WH p r s 2) :
    (p:localRing p)^target∣DShell p r s := by
  let q : localRing p := p
  let Q := H p 2 (p^s)
  let C1 := q^(r+s)*Q
  let C2 := 3*q^(2*r)*Q
  let W := fun u => localWeight p (r-1) (p^(s-1)*u)
  let U := fun u => unitWeight p r (p^s*u)-1
  have d (u : ℕ) (hu : u∈small p (p^(r-s))) :
      q^target∣2*((safe p u)^3*W u*U u)-
        (C1*((safe p u)^1*W u)-C2*((safe p u)^2*W u)) := by
    have z := dvd_mul_of_dvd_right (hMain u hu) ((safe p u)^3*W u)
    have hi := safe_inv u (mem_filter.mp hu).2
    have hi₁ : (u:localRing p)^2*(safe p u)^3=safe p u := by
      rw [show (u:localRing p)^2*(safe p u)^3=((u:localRing p)*safe p u)^2*safe p u by ring,hi]
      simp
    have hi₂ : (u:localRing p)*(safe p u)^3=(safe p u)^2 := by
      rw [show (u:localRing p)*(safe p u)^3=((u:localRing p)*safe p u)*(safe p u)^2 by ring,hi,one_mul]
    convert z using 1
    dsimp [q,C1,C2,Q,W,U]
    push_cast
    rw [pow_add,pow_one]
    linear_combination ((p:localRing p)^r*(p:localRing p)^s*H p 2 (p^s)*localWeight p (r-1) (p^(s-1)*u))*hi₁
      - (3*(p:localRing p)^(2*r)*H p 2 (p^s)*localWeight p (r-1) (p^(s-1)*u))*hi₂
  have h := Finset.dvd_sum d
  rw [sum_sub_distrib, sum_sub_distrib,←mul_sum,←mul_sum,←mul_sum] at h
  change q^target∣2*DShell p r s-(C1*WH p r s 1-C2*WH p r s 2) at h
  change q^target∣C1*WH p r s 1 at hA
  change q^target∣C2*WH p r s 2 at hB
  apply dvd_cancel_two hp2
  simpa only [sub_add_cancel] using dvd_add h (dvd_sub hA hB)

lemma harmonic_first_pow {s K : ℕ} (hs : 0<s) (hK : p^s∣K) (hp2 : p≠2) :
    (p:localRing p)^(3*s)∣2*H p 1 K+(K:localRing p)*H p 2 K := by
  have d := pow_dvd_pow_of_dvd (cast_pow_dvd hK) 3
  have h := d.trans (harmonic_first_bound hp2 ((dvd_pow_self p hs.ne').trans hK))
  simpa only [←pow_mul,mul_comm s 3] using h

lemma penultimate_shell {r : ℕ} (hr : 3≤r) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)^(3*r-3)∣DShell p r (r-2) := by
  let s := r-2
  have hs : 0<s := by dsimp [s]; omega
  have hsr : s<r := by dsimp [s]; omega
  have hQ : (p:localRing p)^s∣H p 2 (p^s) := harmonic_square hs (dvd_refl _) hp2 hp3
  apply shell_cancel (r:=r) (s:=s) hp2
  · intro u hu
    have hk : p^s∣p^s*u := dvd_mul_right _ _
    apply unit_error_upper (s:=s) (d:=3*s) (e:=2*s) hs hsr.le hk hp2 hp3
      (by dsimp [s]; omega) (by dsimp [s]; omega) (by dsimp [s]; omega) (by omega)
      (harmonic_first_pow hs hk hp2)
    simpa only [mul_comm (p^s) u] using square_blocks_mod (p:=p) hs hp2 u
  · have d₁ := mul_dvd_power (dvd_refl ((p:localRing p)^(r+s))) hQ
    have d₂ : (p:localRing p)^1∣WH p r s 1 := by
      simpa only [pow_one] using weighted_harmonic_one hs hsr hp2
    have h := mul_dvd_power d₁ d₂
    rw [show 3*r-3=(r+s+s)+1 by dsimp [s]; omega]
    exact h
  · have d₁ := mul_dvd_power (dvd_refl ((p:localRing p)^(2*r))) hQ
    have hd := (pow_dvd_pow (p:localRing p) (show 3*r-3≤2*r+s by dsimp [s]; omega)).trans d₁
    rw [mul_assoc 3 _ _,mul_assoc 3 _ _]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _

lemma top_shell {r : ℕ} (hr : 2≤r) (hp2 : p≠2) (hp3 : p≠3)
    (hseven : r=2 → 7≤p)
    (hWeight : (p:localRing p)^2∣WH p r (r-1) 1) :
    (p:localRing p)^(3*r)∣DShell p r (r-1) := by
  let s := r-1
  have hs : 0<s := by dsimp [s]; omega
  have hsr : s<r := by dsimp [s]; omega
  have hQ : (p:localRing p)^s∣H p 2 (p^s) := harmonic_square hs (dvd_refl _) hp2 hp3
  apply shell_cancel (r:=r) (s:=s) hp2
  · intro u hu
    have hk : p^s∣p^s*u := dvd_mul_right _ _
    by_cases hr' : 3≤r
    · apply unit_error_upper (s:=s) (d:=3*s) (e:=2*s) hs hsr.le hk hp2 hp3
        (by dsimp [s]; omega) (by dsimp [s]; omega) (by dsimp [s]; omega) (by omega)
        (harmonic_first_pow hs hk hp2)
      simpa only [mul_comm (p^s) u] using square_blocks_mod (p:=p) hs hp2 u
    · have e : r=2 := by omega
      have s1 : s=1 := by dsimp [s]; omega
      have kp : p∣p^s*u := by simpa only [s1,pow_one] using hk
      have hp7 := hseven e
      apply unit_error_upper (s:=s) (d:=4) (e:=3) hs hsr.le hk hp2 hp3
        (by omega) (by omega) (by dsimp [s]; omega) (by omega)
      · apply harmonic_one_sharp kp hp2
        simpa only [s1,pow_one,mul_comm p u] using harmonic_four_at_prime (p:=p) hp7 u
      · simpa only [s1,pow_one,mul_comm p u] using square_blocks_sharp (p:=p) hp7 u
  · have h := mul_dvd_power (mul_dvd_power (dvd_refl ((p:localRing p)^(r+s))) hQ) hWeight
    rw [show 3*r=(r+s+s)+2 by dsimp [s]; omega]
    exact h
  · have d₁ := mul_dvd_power (dvd_refl ((p:localRing p)^(2*r))) hQ
    have d₂ : (p:localRing p)^1∣WH p r s 2 := by
      simpa only [pow_one] using weighted_harmonic_two hs hsr hp2 hp3
    have h := dvd_mul_of_dvd_right (mul_dvd_power d₁ d₂) (3:localRing p)
    rw [show 3*r=(2*r+s)+1 by dsimp [s]; omega]
    simpa only [mul_assoc] using h

end A361715
namespace A361715

open Finset
variable {p : ℕ} [Fact p.Prime]

lemma weight_top_linear {r u : ℕ} (hr : 2 ≤ r) (hu : u ∈ small p p) :
    (p : localRing p)^2 ∣
      localWeight p (r-1) (p^(r-2)*u)-1+(p : localRing p)*H p 1 u := by
  have hp := (Fact.out : p.Prime).pos
  have hup := (mem_Ico.mp (mem_filter.mp hu).1).2
  let M := p^(r-2)
  have hM : 0 < M := pow_pos hp _
  have hP : M*p=p^(r-1) := by
    dsimp [M]
    rw [←pow_succ, show r-2+1=r-1 by omega]
  have hk : M*u < p^(r-1) := by
    rw [←hP]
    exact Nat.mul_lt_mul_of_pos_left hup hM
  have hprod : localWeight p 1 u =
      ∏ j ∈ (Ico 1 (M*u)).filter (fun j => M∣j), factor (localRatio p (r-1) j) := by
    unfold localWeight
    apply prod_bij (fun j _ => M*j)
    · intro j hj
      have h := mem_Ico.mp hj
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨?_,Nat.mul_lt_mul_of_pos_left h.2 hM⟩,dvd_mul_right _ _⟩
      exact Nat.mul_pos hM h.1
    · intro i hi j hj h
      exact Nat.eq_of_mul_eq_mul_left hM h
    · intro j hj
      obtain ⟨h,v,rfl⟩ := mem_filter.mp hj
      have hv := mem_Ico.mp h
      refine ⟨v,mem_Ico.mpr ⟨?_,Nat.lt_of_mul_lt_mul_left hv.2⟩,rfl⟩
      by_contra! h0
      have e : v=0 := by omega
      rw [e,mul_zero] at hv
      omega
    · intro j hj
      congr 1
      have hj' := mem_Ico.mp hj
      have hjp : 0 < j := hj'.1
      have hMjp : 0 < M*j := Nat.mul_pos hM hjp
      have hMj : M*j < p^(r-1) :=
        (Nat.mul_lt_mul_of_pos_left hj'.2 hM).trans hk
      apply Subtype.ext
      have hjp' : j < p^1 := by simpa using hj'.2.trans hup
      rw [localRatio_coe hjp hjp',localRatio_coe hMjp hMj,pow_one]
      have hPQ : (M : ℚ)*(p : ℚ)=(p : ℚ)^(r-1) := by exact_mod_cast hP
      rw [←hPQ,Nat.cast_mul]
      field_simp [show (M:ℚ)≠0 by positivity,show (j:ℚ)≠0 by positivity]
  have hd := localWeight_filtered (p:=p) (r:=r-1) (k:=M*u) (m:=2) (by omega) hk.le
  rw [show r-1+1-2=r-2 by omega] at hd
  change (p:localRing p)^2 ∣ localWeight p (r-1) (M*u) -
    ∏ j ∈ (Ico 1 (M*u)).filter (fun j => M∣j), factor (localRatio p (r-1) j) at hd
  rw [←hprod] at hd
  have huweight : localWeight p 1 u = unitWeight p 1 u := by
    rw [localWeight_factor]
    have he : (Ico 1 u).filter (fun j => p∣j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      have ⟨h,hdv⟩ := mem_filter.mp hj
      have hj' := mem_Ico.mp h
      exact (not_le_of_gt (hj'.2.trans hup)) (Nat.le_of_dvd hj'.1 hdv)
    simp [divWeight,he]
  have hlin := unitWeight_linear (p:=p) 1 u
  rw [←huweight] at hlin
  convert dvd_add hd (show (p:localRing p)^2 ∣
      localWeight p 1 u-1+(p:localRing p)*H p 1 u by simpa using hlin) using 1
  dsimp [M]
  ring

omit [Fact p.Prime] in
private lemma small_succ (K : ℕ) :
    small p (K+1) = if p∣K then small p K else insert K (small p K) := by
  by_cases h : p∣K
  · rw [if_pos h]
    ext j
    simp only [small,mem_filter,mem_Ico]
    constructor
    · rintro ⟨⟨hj1,hj2⟩,hn⟩
      have he : j≠K := by rintro rfl; exact hn h
      exact ⟨⟨hj1,by omega⟩,hn⟩
    · exact fun ⟨⟨a,b⟩,c⟩ => ⟨⟨a,by omega⟩,c⟩
  · rw [if_neg h]
    have hK : 1≤K := by cases K <;> simp_all
    ext j
    simp only [small,mem_filter,mem_Ico,mem_insert]
    constructor
    · rintro ⟨⟨hj1,hj2⟩,hn⟩
      by_cases e : j=K
      · exact Or.inl e
      · exact Or.inr ⟨⟨hj1,by omega⟩,hn⟩
    · rintro (rfl | ⟨⟨a,b⟩,c⟩)
      · exact ⟨⟨hK,by omega⟩,h⟩
      · exact ⟨⟨a,by omega⟩,c⟩

lemma harmonic_prefix_pairs (K : ℕ) :
    2 * (∑ u ∈ small p K, safe p u * H p 1 u) =
      (H p 1 K)^2 - H p 2 K := by
  induction K with
  | zero => simp [small,H]
  | succ K ih =>
    by_cases h : p∣K
    · have hs : small p (K+1) = small p K := by simp [small_succ,h]
      have he (m : ℕ) : H p m (K+1) = H p m K := by simp only [H,hs]
      rw [hs,he,he]
      exact ih
    · have hs : small p (K+1) = insert K (small p K) := by simp [small_succ,h]
      have hn : K ∉ small p K := by simp [small]
      have he (m : ℕ) : H p m (K+1) = (safe p K)^m + H p m K := by
        simp only [H,hs,sum_insert hn]
      rw [hs,sum_insert hn,he,he,pow_one]
      linear_combination ih

lemma top_weighted_reciprocal {r : ℕ} (hr : 2 ≤ r) (hp2 : p≠2) (hp3 : p≠3) :
    (p:localRing p)^2 ∣
      ∑ u ∈ small p p, safe p u * localWeight p (r-1) (p^(r-2)*u) := by
  let q := (p:localRing p)
  let S := ∑ u ∈ small p p, safe p u * H p 1 u
  have hQ2 : q ∣ H p 2 p := by
    simpa [q] using harmonic_square (p:=p) (r:=1) (K:=p) (by decide) (by simp) hp2 hp3
  have hm : q^2 ∣ q*H p 2 p := by simpa [pow_two] using mul_dvd_mul_left q hQ2
  have hQ1 : q^2 ∣ H p 1 p := by
    have hb := harmonic_first_bound hp2 (dvd_refl p)
    have hb' : q^2 ∣ 2*H p 1 p+q*H p 2 p :=
      (pow_dvd_pow q (by decide : (2:ℕ)≤3)).trans hb
    apply dvd_cancel_two hp2
    simpa only [add_sub_cancel_right] using dvd_sub hb' hm
  have hS : q ∣ S := by
    apply dvd_cancel_two hp2
    change q ∣ 2 * (∑ u ∈ small p p, safe p u * H p 1 u)
    rw [harmonic_prefix_pairs]
    have h : q∣H p 1 p := (dvd_pow_self q (by decide : (2:ℕ)≠0)).trans hQ1
    exact dvd_sub (h.trans (dvd_pow_self _ (by decide : (2:ℕ)≠0))) hQ2
  have hpS : q^2 ∣ q*S := by simpa [pow_two] using mul_dvd_mul_left q hS
  have herror : q^2 ∣ ∑ u ∈ small p p, safe p u *
      (localWeight p (r-1) (p^(r-2)*u)-1+q*H p 1 u) := by
    apply Finset.dvd_sum
    intro u hu
    exact dvd_mul_of_dvd_right (weight_top_linear hr hu) _
  have hrewrite : (∑ u ∈ small p p, safe p u *
      (localWeight p (r-1) (p^(r-2)*u)-1+q*H p 1 u)) =
      (∑ u ∈ small p p, safe p u * localWeight p (r-1) (p^(r-2)*u)) - H p 1 p + q*S := by
    have he : H p 1 p = ∑ u ∈ small p p,safe p u := by simp [H]
    rw [he]
    dsimp only [S]
    rw [mul_sum,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    ring
  rw [hrewrite] at herror
  convert dvd_add (dvd_sub herror hpS) hQ1 using 1
  ring

end A361715

namespace A361715
open OMA.S_oeis_a361715

theorem exceptions : ∀ r : ℕ, 2 ≤ r → r ≤ 3 →
    a (5^r) ≡ a (5^(r-1)) [MOD 5^(3*r+3)] := by
  intro r lo hi
  interval_cases r <;> decide +kernel

end A361715
namespace A361715

open Finset OMA.S_oeis_a361715

private theorem all_levels (p r : ℕ) (hp : p.Prime) (hp5 : 5≤p) (hr : 2≤r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r+3)] := by
  by_cases hsmall : p=5 ∧ r≤3
  · rcases hsmall with ⟨rfl, h⟩
    exact exceptions r hr h
  let _ : Fact p.Prime := ⟨hp⟩
  have h2 : p≠2 := by omega
  have h3 : p≠3 := by omega
  have h7 (h : r≤3) : 7≤p := by
    have h5 : p≠5 := fun he => hsmall ⟨he,h⟩
    have h6 : p≠6 := fun he => (by decide : ¬(6:ℕ).Prime) (he ▸ hp)
    omega
  have hV : (p:localRing p)^3∣V p r := by
    by_cases h4 : 4≤r
    · apply V_high_zero_from_blocks (by omega)
      intro b hb
      by_cases hr4 : r=4
      · rw [hr4,show 4-2=2 by decide]
        exact cube_block_p_sq_zero h2 b
      · exact cube_block_large_zero (by omega) h2 b
    · have hp7 := h7 (by omega)
      let C := 3*(p:localRing p)*H p 4 p
      have hC : (p:localRing p)^2∣C := by
        have h := harmonic_four_at_prime (p:=p) hp7 1
        rw [one_mul] at h
        have hh := mul_dvd_power (i:=1) (j:=1) (dvd_refl ((p:localRing p)^1))
          (show (p:localRing p)^1∣H p 4 p by simpa only [pow_one])
        simpa only [C,pow_one,mul_assoc] using dvd_mul_of_dvd_right hh (3:localRing p)
      have ha (b : ℕ) : (p:localRing p)^3∣2*RBlock p 3 p b+C*(2*(b:localRing p)+1) := by
        have h := cube_block_three (p:=p) hp7 b
        convert h using 1
        dsimp [C]
        push_cast
        ring
      have rr : r=2 ∨ r=3 := by omega
      rcases rr with rfl|rfl
      · exact V_two_affine h2 hC (fun b _ => ha b) (fun _ _ _ _ => H_one_slice h2)
      · exact V_three_affine h2 hC (fun b _ => ha b)
  have hW : (p:localRing p)^2∣WH p r (r-1) 1 := by
    unfold WH
    rw [show r-(r-1)=1 by omega,show r-1-1=r-2 by omega,pow_one]
    simp only [pow_one]
    exact top_weighted_reciprocal hr h2 h3
  have hD := D_from_shells hr h2 h3 (top_shell hr h2 h3 (fun h => h7 (by omega)) hW)
    (fun h => penultimate_shell h h2 h3)
  exact finish (by omega) hV hD

end A361715

theorem OMA.solution : type_of% @OMA.S_oeis_a361715.main :=
  A361715.all_levels
