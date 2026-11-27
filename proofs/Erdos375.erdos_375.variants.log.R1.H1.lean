import OMAReductions.R_Erdos375_erdos_375_variants_log_R1

section R1Section
/- Ramachandra, Shorey and Tijdeman (1975), section 2. The first application
of their approximation argument either supplies the logarithmic form or
forces a large family. Removing one maximal prime-power factor for each
prime leaves cofactors whose product divides the factorial. At the cubic
scale this forces many elements with exactly one assigned prime. -/
namespace OMA.Erdos375H1R1
open Filter Finset Real

-- The finite factorial bound after assigning each prime to one position
-- where its valuation is maximal. A counts unassigned positions, B the
-- positions with exactly one assigned prime.
def H1 : Prop := ∀ n k : ℕ, ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  ∃ (a : ℕ) (B : Finset (Fin k)) (p e u : Fin k → ℕ), B ⊆ J ∧
    J.card ≤ 2*a+B.card ∧ (n+1)^a ≤ k.factorial ∧
    (∏ i ∈ B, u i) ≤ k.factorial ∧ Set.InjOn p B ∧
    ∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)

-- First-stage extraction from a small obstruction (the proof of Lemma 6).
def H2 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∃ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  δ*(log n/log (log n))^2 ≤ J.card ∨ ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

-- Second-stage extraction (the close cofactors and close exponents on
-- pages 116–118). This statement concerns individual factorizations.
def H3 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∀ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ (B : Finset (Fin k)) (p e u : Fin k → ℕ),
    δ*(log n/log (log n))^2 ≤ B.card → (∏ i ∈ B, u i) ≤ k.factorial →
    Set.InjOn p B →
    (∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)) →
    ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

theorem main : H1 → H2 → H3 → OMA.R_Erdos375_erdos_375_variants_log_R1.H1 := by
  intro extraction small large b hb S₀
  obtain ⟨δ,hδ,c₁,hc₁,hs⟩ := small b hb S₀
  obtain ⟨c₂,hc₂,hl⟩ := large b hb S₀ (δ/2) (by positivity)
  let c := min (min c₁ c₂) (min 1 (δ/12))
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤c₁ := (min_le_left ..).trans (min_le_left ..)
  have hc2 : c≤c₂ := (min_le_left ..).trans (min_le_right ..)
  have hc3 : c≤1 := (min_le_right ..).trans (min_le_left ..)
  have hcd : c≤δ/12 := (min_le_right ..).trans (min_le_right ..)
  refine ⟨c,hc,?_⟩
  have tlog : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tll : Tendsto (fun n : ℕ => log (log (n:ℝ))) atTop atTop :=
    tendsto_log_atTop.comp tlog
  filter_upwards [hs,hl,tlog.eventually_ge_atTop 1,tll.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with n hs hl hlog hll hn
  intro k hk J P hJ hP
  let L := log (n:ℝ)
  let l := log L
  let Q := L/l
  change 1≤L at hlog
  change 1≤l at hll
  change (k:ℝ)<c*Q^3 at hk
  have lp : 0<l := by linarith
  have Lp : 0<L := by linarith
  have qp : 0<Q := div_pos Lp lp
  have ql : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hll)])
  have kpos : 0<k := by
    have : J.card ≤ k := (card_le_card (subset_univ J)).trans_eq (by simp)
    omega
  rcases hs k (hk.trans_le (mul_le_mul_of_nonneg_right hc1 (pow_nonneg qp.le _))) J hJ hP with hbig|done
  · obtain ⟨a,B,p,e,u,_,hcard,hpow,hfac,hinj,hsingle⟩ := extraction n k J hJ hP
    change δ*Q^2 ≤ _ at hbig
    have hkc : (k:ℝ) ≤ L^3 := calc
      _ ≤ c*Q^3 := hk.le
      _ ≤ 1*L^3 := mul_le_mul hc3 (pow_le_pow_left₀ qp.le ql 3) (pow_nonneg qp.le _) zero_le_one
      _ = _ := one_mul _
    have hkl : log (k:ℝ) ≤ 3*l := by
      have v := log_le_log (by exact_mod_cast kpos) hkc
      rwa [Real.log_pow] at v
    have hnZ : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have kn : (n:ℝ)^a ≤ (k:ℝ)^k := by
      exact_mod_cast (Nat.pow_le_pow_left (Nat.le_succ n) a).trans (hpow.trans k.factorial_le_pow)
    have lg := log_le_log (pow_pos hnZ a) kn
    rw [Real.log_pow,Real.log_pow] at lg
    change (a:ℝ)*L ≤ (k:ℝ)*log k at lg
    have ha : (a:ℝ)*L ≤ 3*c*Q^2*L := calc
      _ ≤ (k:ℝ)*log k := lg
      _ ≤ (c*Q^3)*(3*l) := mul_le_mul hk.le hkl (log_natCast_nonneg _) (by positivity)
      _ = _ := by dsimp [Q]; field_simp <;> ring
    have ha' : (a:ℝ) ≤ 3*c*Q^2 := le_of_mul_le_mul_right ha Lp
    have hB : δ/2*Q^2 ≤ (B.card:ℝ) := by
      have hcard' : (J.card:ℝ) ≤ 2*(a:ℝ)+(B.card:ℝ) := by exact_mod_cast hcard
      nlinarith only [hbig,hcard',ha',mul_le_mul_of_nonneg_right hcd (sq_nonneg Q)]
    exact hl k (hk.trans_le (mul_le_mul_of_nonneg_right hc2 (pow_nonneg qp.le _))) B p e u hB hfac hinj hsingle
  · exact done

end OMA.Erdos375H1R1
end R1Section

section L1Section
namespace OMA.L1
/- For each prime, assign a row where its valuation is largest. The powers
at every other row divide its distance to that row. Distinct prime powers
are coprime, so their full product divides the factorial. -/
open Finset

private lemma product_dist {k : ℕ} (j:Fin k) (S:Finset (Fin k)) :
    (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) ∣ k.factorial := by
  classical
  let L := S.filter (fun i => i.val<j.val)
  let R := S.filter (fun i => j.val < i.val)
  have injL : Set.InjOn (fun i:Fin k => j.val-i.val) ↑L := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have injR : Set.InjOn (fun i:Fin k => i.val-j.val) ↑R := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have lsub : L.image (fun i => j.val-i.val) ⊆ Icc 1 j.val := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    exact mem_Icc.mpr ⟨by omega,Nat.sub_le ..⟩
  have rsub : R.image (fun i => i.val-j.val) ⊆ Icc 1 (k-j.val) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    have := i.isLt
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have left := prod_dvd_prod_of_subset _ _ id lsub
  have right := prod_dvd_prod_of_subset _ _ id rsub
  have prodI (n:ℕ) : ∏ i∈Icc 1 n,id i=n.factorial := by
    have e : Icc 1 n=Ico 1 (n+1) := by ext i; simp
    rw [e]; exact prod_Ico_id_eq_factorial n
  rw [prod_image injL,prodI] at left
  rw [prod_image injR,prodI] at right
  have eq : (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) =
       (∏ i∈L, (j.val-i.val))*(∏ i∈R,(i.val-j.val)) := by
    dsimp only [L,R]
    rw [prod_filter,prod_filter,←prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    by_cases h:i.val<j.val <;> simp [h,show i.val<j.val → ¬j.val < i.val from fun a => a.asymm]
  rw [eq]
  exact (Nat.mul_dvd_mul left right).trans (Nat.factorial_mul_factorial_dvd_factorial j.isLt.le)

private lemma off_max {n k p:ℕ} (_hp:p.Prime) (J:Finset (Fin k)) (j:Fin k)
    (maxi:∀ i∈J, (n+i.val+1).factorization p ≤ (n+j.val+1).factorization p) :
    (∏ i∈J, p^(if i=j then 0 else (n+i.val+1).factorization p)) ∣ k.factorial := by
  apply dvd_trans _ (product_dist j J)
  apply prod_dvd_prod_of_dvd
  intro i hi
  by_cases eq:i=j
  · simp [eq]
  rw [if_neg eq]
  have dl := Nat.ordProj_dvd (n+i.val+1) p
  have dr : p^(n+i.val+1).factorization p ∣ n+j.val+1 :=
    (pow_dvd_pow _ (maxi i hi)).trans (Nat.ordProj_dvd _ _)
  by_cases lt:i.val<j.val
  · rw [if_pos lt]
    have h := Nat.dvd_sub dr dl
    rwa [show n+j.val+1-(n+i.val+1)=j.val-i.val by omega] at h
  · have gt : j.val < i.val := by have ne : i.val≠j.val := fun h => eq (Fin.ext h); omega
    rw [if_neg lt,if_pos gt]
    have h := Nat.dvd_sub dl dr
    rwa [show n+i.val+1-(n+j.val+1)=i.val-j.val by omega] at h

theorem l1_proof : OMA.Erdos375H1R1.H1 := by
  classical
  intro n k J P deficit small
  have jne : J.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
  let w (i:Fin k) := n+i.val+1
  have wp (i:Fin k) : 0<w i := Nat.succ_pos _
  let e (i:Fin k) (p:ℕ) := (w i).factorization p
  have ex (p:ℕ) := J.exists_max_image (fun i => e i p) jne
  choose f fj mx using ex
  let F (i:Fin k) := P.filter (fun p => f p=i)
  let Z := J.filter (fun i => (F i).card=0)
  let B := J.filter (fun i => (F i).card=1)
  have pprime (p:ℕ) (hp:p∈P) : p.Prime := by
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors h
  have psum : ∑ i∈J,(F i).card = P.card := (card_eq_sum_card_fiberwise (f:=f) (s:=P) (t:=J) (fun p _ => fj p)).symm
  have count : J.card ≤ 2*Z.card+B.card := by
    have point (i:Fin k) : 2≤(F i).card+2*(if (F i).card=0 then 1 else 0)+(if (F i).card=1 then 1 else 0) := by split_ifs <;> omega
    have h := sum_le_sum (s:=J) (fun i _ => point i)
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,psum] at h
    simp only [sum_const,nsmul_eq_mul] at h
    have z : ∑ i∈J,(if (F i).card=0 then 1 else 0) = Z.card := (card_filter ..).symm
    have b : ∑ i∈J,(if (F i).card=1 then 1 else 0) = B.card := (card_filter ..).symm
    rw [z,b] at h
    change J.card*2 ≤ P.card+2*Z.card+B.card at h
    omega
  let v (i:Fin k) (p:ℕ) := if i=f p then 0 else e i p
  let u (i:Fin k) := ∏ p∈P,p^(v i p)
  have u0 (i:Fin k) : 0<u i := prod_pos fun p hp => pow_pos (pprime p hp).pos _
  have all : ∏ i∈J,u i ∣ k.factorial := by
    change (∏ i∈J,∏ p∈P,p^(v i p)) ∣ _
    rw [prod_comm]
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq pq
      apply Nat.coprime_iff_isRelPrime.mp
      apply Nat.Coprime.prod_left
      intro i _
      apply Nat.Coprime.prod_right
      intro j _
      exact (((pprime p hp).coprime_iff_not_dvd.mpr (fun h => pq (((Nat.dvd_prime (pprime q hq)).mp h).resolve_left (pprime p hp).ne_one))).pow_left _).pow_right _
    · intro p hp
      exact off_max (pprime p hp) J (f p) (mx p)
  have bound (T:Finset (Fin k)) (hT:T⊆J) : ∏ i∈T,u i ≤ k.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos k) ((prod_dvd_prod_of_subset _ _ u hT).trans all)
  let remn (i:Fin k) := ∏ p∈P,p^(if i=f p then e i p else 0)
  have split (i:Fin k) (hi:i∈J) : w i = u i*remn i := by
    have sub : (w i).primeFactors⊆P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
    have prod : ∏ p∈P, p^(e i p) = w i := by
      apply Eq.trans _ (Nat.prod_primeFactors_pow_factorization (wp i).ne').symm
      change ∏ p∈P, p^(e i p) = ∏ p∈(w i).primeFactors,p^(e i p)
      symm
      apply prod_subset sub
      intro p _ hp
      have z : (w i).factorization p=0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [e,z]
    rw [←prod]
    dsimp only [u,remn]
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases eq:i=f p <;> simp [v,eq]
  have zero (i:Fin k) (hi:i∈Z) : n+1≤u i := by
    obtain ⟨ij,empty⟩ := mem_filter.mp hi
    have no (p:ℕ) (hp:p∈P) : i≠f p := by
      intro eq
      have h : p∈F i := mem_filter.mpr ⟨hp,eq.symm⟩
      rw [card_eq_zero.mp empty] at h
      exact notMem_empty _ h
    have r : remn i=1 := prod_eq_one (fun p hp => by simp [no p hp])
    have e := split i ij
    rw [r,mul_one] at e
    dsimp [w] at e
    omega
  have get (i:Fin k) (hi:i∈B) : ∃ q:ℕ,F i={q} := card_eq_one.mp (mem_filter.mp hi).2
  let p (i:Fin k) := if h:i∈B then (get i h).choose else 0
  have singleton (i:Fin k) (hi:i∈B) : F i={p i} := by simpa [p,hi] using (get i hi).choose_spec
  have member (i:Fin k) (hi:i∈B) : p i∈P ∧ f (p i)=i := by
    have h : p i∈F i := by rw [singleton i hi]; simp
    exact mem_filter.mp h
  refine ⟨Z.card,B,p,fun i => e i (p i),u,filter_subset ..,count,?_,bound B (filter_subset ..),?_,?_⟩
  · calc (n+1)^Z.card = ∏ i∈Z,(n+1) := (prod_const _).symm
         _ ≤ ∏ i∈Z,u i := prod_le_prod' (fun i hi => zero i hi)
         _ ≤ _ := bound Z (filter_subset ..)
  · intro i hi j hj eq
    exact (member i hi).2.symm.trans ((congrArg f eq).trans (member j hj).2)
  · intro i hi
    refine ⟨pprime _ (member i hi).1,small _ (member i hi).1,u0 i,?_⟩
    have r : remn i=(p i)^(e i (p i)) := by
      dsimp [remn]
      rw [prod_eq_single_of_mem (p i) (member i hi).1 (fun q hq ne => ?_),if_pos (member i hi).2.symm]
      have no : i≠f q := by
        intro eq
        have h : q∈F i := mem_filter.mpr ⟨hq,eq.symm⟩
        rw [singleton i hi] at h
        exact ne (mem_singleton.mp h)
      simp [no]
    exact (split i (mem_filter.mp hi).1).trans (congrArg (u i * ·) r)
end OMA.L1
end L1Section

section L2Section
/- The first-stage extraction of Ramachandra, Shorey and Tijdeman, Section 2.
For a small Hall obstruction choose h around d log(n)/(1000 log log n).
A common multiple of its cofactors and the pairwise gcd bounds show that
fewer than h cofactors have log larger than d log(n)/16. The unassigned
rows all have large cofactors, so at least a quarter of log(n)/log log(n)
rows have a unique assigned prime and a small cofactor. -/
namespace OMA.GrimmSmall
open Finset Real Filter
open scoped Topology

-- Assign primes to maximum-valuation rows. All retained cofactors divide
-- a common integer at most k to the power card J; the gcd of any two of
-- them divides a nonzero difference of row indices and hence is at most k.
private def Structural : Prop := ∀ n k : ℕ, ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card<J.card → (∀ p∈P,p<k) →
  ∃ (Z B : Finset (Fin k)) (p e u : Fin k → ℕ),
    Z⊆J ∧ B⊆J ∧ J.card≤2*Z.card+B.card ∧ n+1≤k^J.card ∧
    (∀ i∈J,0<u i) ∧ (∀ i∈Z,n+1≤u i) ∧
    (∀ W⊆J, ∏ i∈W,u i ≤ k^(J.card+W.card^2)) ∧
    ∀ i∈B,(p i).Prime ∧ p i<k ∧ n+i.val+1=u i*(p i)^(e i)

-- Rounding prime exponents down to a common bin and absorbing the
-- residual powers in the small cofactors gives a pair of near logarithms.
private def Rounded : Prop := ∀ b : ℝ, 0<b → ∀ S₀ : ℝ, ∃ d:ℝ, 0<d ∧ d≤1/100 ∧
  ∀ᶠ n : ℕ in atTop, ∀ k:ℕ, (k:ℝ)<(log n/log (log n))^3 →
  ∀ (B:Finset (Fin k)) (p e u:Fin k→ℕ),
    (log n/log (log n))/4≤B.card →
    (∀ i∈B,(p i).Prime ∧ p i<k ∧ 0<u i ∧ log (u i:ℝ)≤d*log n/16 ∧ n+i.val+1=u i*(p i)^(e i)) →
    ∃ (S:ℝ) (x y:ℚ) (m:ℤ), S₀≤S ∧ S≤(n:ℝ)^b ∧ 0<x ∧ 0<y ∧
    ((x.num.natAbs+x.den:ℕ):ℝ)≤(log S)^16 ∧ ((y.num.natAbs+y.den:ℕ):ℝ)≤S ∧
    2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (y:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (x:ℝ)-log (y:ℝ)| ∧
    |(m:ℝ)*log (x:ℝ)-log (y:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

private theorem main : Structural → Rounded → OMA.Erdos375H1R1.H2 := by
  classical
  intro structural near b hb S₀
  obtain ⟨d,dp,dc,near⟩ := near b hb S₀
  let δ := d^2/100000000
  refine ⟨δ,by dsimp [δ]; positivity,1,one_pos,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have smalllog := isLittleO_log_id_atTop.bound (show 0<d/2000 by positivity)
  filter_upwards [near,eventually_ge_atTop 2,tL.eventually_ge_atTop 1,tl.eventually_ge_atTop 1,
    tL.eventually smalllog] with n near hn hL hl raw
  intro k hk J P deficit small
  let L := log (n:ℝ)
  let l := log L
  let Q := L/l
  change 1≤L at hL
  change 1≤l at hl
  change ‖l‖≤d/2000*‖L‖ at raw
  rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith)] at raw
  have hQ : 2000/d≤Q := by
    apply (le_div_iff₀ (show 0<l by linarith)).mpr
    rw [div_mul_eq_mul_div,div_le_iff₀ dp]
    linarith
  simp only [one_mul] at hk
  change (k:ℝ)<Q^3 at hk
  by_cases big:δ*Q^2≤J.card
  · exact Or.inl big
  right
  obtain ⟨Z,B,p,e,u,zJ,bJ,count,nk,up,zero,products,rows⟩ := structural n k J deficit small
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have kp : 0<k := by
    obtain ⟨i,_⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
    exact Nat.zero_lt_of_lt i.isLt
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have qp : 0<Q := div_pos Lp lp
  have qrel : Q*l=L := div_mul_cancel₀ _ lp.ne'
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kL := hk.le.trans (pow_le_pow_left₀ qp.le qL 3)
  have lk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kL
    rwa [log_pow] at h
  have jlow : Q≤3*(J.card:ℝ) := by
    have lg := log_le_log np (by exact_mod_cast (Nat.le_succ n).trans nk : (n:ℝ)≤(k:ℝ)^J.card)
    rw [log_pow] at lg
    apply (div_le_iff₀ lp).mpr
    linarith only [lg,mul_le_mul_of_nonneg_left lk (Nat.cast_nonneg J.card (α:=ℝ))]
  let T := d*L/16
  let h := ⌊d*Q/1000⌋₊
  have y2 : 2≤d*Q/1000 := by have ht := (div_le_iff₀ dp).mp hQ; linarith
  have hup : (h:ℝ)≤d*Q/1000 := Nat.floor_le (by linarith)
  have hlo : d*Q/2000≤(h:ℝ) := by
    have h' := Nat.lt_floor_add_one (d*Q/1000)
    change d*Q/1000<(h:ℝ)+1 at h'
    linarith
  let D := J.filter (fun i => T<log (u i:ℝ))
  have few : D.card<h := by
    by_contra! many
    obtain ⟨W,wD,wc⟩ := exists_subset_card_eq many
    have wJ := wD.trans (show D ⊆ J from filter_subset ..)
    have lo : (h:ℝ)*T ≤ ∑ i∈W, log (u i:ℝ) := by
      rw [←wc,←nsmul_eq_mul,←sum_const]
      exact sum_le_sum fun i hi => (mem_filter.mp (wD hi)).2.le
    have lg := log_le_log (prod_pos (s:=W) (fun i hi => show 0<(u i:ℝ) by exact_mod_cast up i (wJ hi)))
      (show (∏ i∈W,(u i:ℝ))≤(k:ℝ)^(J.card+W.card^2) by exact_mod_cast products W wJ)
    rw [log_prod (fun i hi => by exact_mod_cast (up i (wJ hi)).ne'),log_pow,wc] at lg
    push_cast at lg
    have cost := lo.trans (lg.trans (mul_le_mul_of_nonneg_left lk (by positivity)))
    have jless : (J.card:ℝ)<δ*Q^2 := lt_of_not_ge big
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg h (α:=ℝ)) hup 2
    have upper := mul_le_mul_of_nonneg_right (add_le_add jless.le h2) (show 0≤3*l by positivity)
    have left := mul_le_mul_of_nonneg_right hlo (show 0≤T by dsimp [T]; positivity)
    have bad := left.trans (cost.trans upper)
    dsimp only [T,δ] at bad
    rw [←qrel] at bad
    nlinarith only [bad,mul_pos (mul_pos (sq_pos_of_pos dp) (sq_pos_of_pos qp)) lp]
  have zd : Z⊆D := by
    intro i hi
    have lg := log_le_log np (by exact_mod_cast (Nat.le_succ n).trans (zero i hi) : (n:ℝ)≤u i)
    have tl : T<L := by dsimp [T]; nlinarith only [Lp,mul_le_mul_of_nonneg_right dc Lp.le]
    exact mem_filter.mpr ⟨zJ hi,tl.trans_le lg⟩
  let G := B \ D
  have gc : B.card≤G.card+D.card := by
    have h := card_le_card (s:=B) (t:=G∪D) (by intro i hi; by_cases h:i∈D; exact mem_union_right _ h; exact mem_union_left _ (mem_sdiff.mpr ⟨hi,h⟩))
    exact h.trans (card_union_le ..)
  have he : J.card≤G.card+3*h := by have := card_le_card zd; omega
  have he' : (J.card:ℝ)≤(G.card:ℝ)+3*h := by exact_mod_cast he
  have enough : Q/4≤(G.card:ℝ) := by nlinarith only [jlow,he',hup,mul_le_mul_of_nonneg_right dc qp.le,qp.le]
  refine near k hk G p e u enough ?_
  intro i hi
  obtain ⟨ib,id⟩ := mem_sdiff.mp hi
  have data := rows i ib
  refine ⟨data.1,data.2.1,up i (bJ ib),le_of_not_gt (fun h => id (mem_filter.mpr ⟨bJ ib,h⟩)),data.2.2⟩

private lemma small_prod {α:Type*} [DecidableEq α] {w:α→ℕ} {k:ℕ} (S:Finset α)
    (pos:∀ i∈S, 0<w i) (kp:0<k)
    (cross:∀ i∈S, ∀ j∈S, i≠j → (w i).gcd (w j)≤k) :
    ∏ i∈S,w i ≤ S.lcm w * k^(S.card^2) := by
  classical
  have gcdprod (x:ℕ) (U:Finset α) : x.gcd (∏ i∈U,w i) ∣ ∏ i∈U,x.gcd (w i) := by
    induction U using Finset.induction_on with
    | empty => simp
    | insert i U hi ih =>
      rw [prod_insert hi,prod_insert hi]
      exact (gcd_mul_dvd_mul_gcd x (w i) _).trans (Nat.mul_dvd_mul_left _ ih)
  induction S using Finset.induction_on with
  | empty => simp
  | insert a V hi ih =>
    have vp (i:α) (h:i∈V) := pos i (mem_insert_of_mem h)
    have va := pos a (mem_insert_self ..)
    have ihprod := ih vp (fun i h j h' ne => cross i (mem_insert_of_mem h) j (mem_insert_of_mem h') ne)
    have gd : (w a).gcd (V.lcm w) ∣ ∏ i∈V,(w a).gcd (w i) :=
      (Nat.gcd_dvd_gcd_of_dvd_right _ (V.lcm_dvd_prod w)).trans (gcdprod _ _)
    have pg : 0<∏ i∈V,(w a).gcd (w i) := prod_pos (fun i _ => Nat.gcd_pos_of_pos_left _ va)
    have gb : (w a).gcd (V.lcm w) ≤ k^V.card := (Nat.le_of_dvd pg gd).trans (by
      rw [←prod_const (s:=V) k]
      exact prod_le_prod' fun i h => cross a (mem_insert_self ..) i (mem_insert_of_mem h) (fun e => hi (e ▸ h)))
    rw [prod_insert hi,lcm_insert,card_insert_of_notMem hi]
    calc (w a)*(∏ i∈V,w i) ≤ (w a)*(V.lcm w*k^(V.card^2)) := Nat.mul_le_mul_left _ ihprod
         _ = (w a).lcm (V.lcm w) * ((w a).gcd (V.lcm w) * k^(V.card^2)) := by
            calc _ = ((w a)*(V.lcm w))*k^(V.card^2) := by ring
                 _ = ((w a).gcd (V.lcm w)*(w a).lcm (V.lcm w))*k^(V.card^2) := by rw [Nat.gcd_mul_lcm]
                 _ = _ := by ring
         _ ≤ (w a).lcm (V.lcm w) * (k^V.card*k^(V.card^2)) := by gcongr
         _ ≤ _ := by
            rw [←pow_add]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right kp (by nlinarith))

private theorem structural : Structural := by
  classical
  intro n k J P deficit small
  have jne : J.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
  let w (i:Fin k) := n+i.val+1
  have wp (i:Fin k) : 0<w i := Nat.succ_pos _
  let e (i:Fin k) (p:ℕ) := (w i).factorization p
  have ex (p:ℕ) := J.exists_max_image (fun i => e i p) jne
  choose f fj mx using ex
  let F (i:Fin k) := P.filter (fun p => f p=i)
  let Z := J.filter (fun i => (F i).card=0)
  let B := J.filter (fun i => (F i).card=1)
  have pprime (p:ℕ) (hp:p∈P) : p.Prime := by
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors h
  have psum : ∑ i∈J,(F i).card = P.card := (card_eq_sum_card_fiberwise (f:=f) (s:=P) (t:=J) (fun p _ => fj p)).symm
  have count : J.card ≤ 2*Z.card+B.card := by
    have point (i:Fin k) : 2≤(F i).card+2*(if (F i).card=0 then 1 else 0)+(if (F i).card=1 then 1 else 0) := by split_ifs <;> omega
    have h := sum_le_sum (s:=J) (fun i _ => point i)
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,psum] at h
    simp only [sum_const,nsmul_eq_mul] at h
    have z : ∑ i∈J,(if (F i).card=0 then 1 else 0) = Z.card := (card_filter ..).symm
    have b : ∑ i∈J,(if (F i).card=1 then 1 else 0) = B.card := (card_filter ..).symm
    rw [z,b] at h
    change J.card*2 ≤ P.card+2*Z.card+B.card at h
    omega
  let v (i:Fin k) (p:ℕ) := if i=f p then 0 else e i p
  let u (i:Fin k) := ∏ p∈P,p^(v i p)
  have u0 (i:Fin k) : 0<u i := prod_pos fun p hp => pow_pos (pprime p hp).pos _
  let remn (i:Fin k) := ∏ p∈P,p^(if i=f p then e i p else 0)
  have split (i:Fin k) (hi:i∈J) : w i = u i*remn i := by
    have sub : (w i).primeFactors⊆P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
    have prod : ∏ p∈P, p^(e i p) = w i := by
      apply Eq.trans _ (Nat.prod_primeFactors_pow_factorization (wp i).ne').symm
      change ∏ p∈P, p^(e i p) = ∏ p∈(w i).primeFactors,p^(e i p)
      symm
      apply prod_subset sub
      intro p _ hp
      have z : (w i).factorization p=0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [e,z]
    rw [←prod]
    dsimp only [u,remn]
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases eq:i=f p <;> simp [v,eq]
  have zero (i:Fin k) (hi:i∈Z) : n+1≤u i := by
    obtain ⟨ij,empty⟩ := mem_filter.mp hi
    have no (p:ℕ) (hp:p∈P) : i≠f p := by
      intro eq
      have h : p∈F i := mem_filter.mpr ⟨hp,eq.symm⟩
      rw [card_eq_zero.mp empty] at h
      exact notMem_empty _ h
    have r : remn i=1 := prod_eq_one (fun p hp => by simp [no p hp])
    have e := split i ij
    rw [r,mul_one] at e
    dsimp [w] at e
    omega
  have get (i:Fin k) (hi:i∈B) : ∃ q:ℕ,F i={q} := card_eq_one.mp (mem_filter.mp hi).2
  let p (i:Fin k) := if h:i∈B then (get i h).choose else 0
  have singleton (i:Fin k) (hi:i∈B) : F i={p i} := by simpa [p,hi] using (get i hi).choose_spec
  have member (i:Fin k) (hi:i∈B) : p i∈P ∧ f (p i)=i := by
    have h : p i∈F i := by rw [singleton i hi]; simp
    exact mem_filter.mp h
  have kp : 0<k := by obtain ⟨i,_⟩ := jne; exact Nat.zero_lt_of_lt i.isLt
  have vcap (i:Fin k) (ii:i∈J) (p:ℕ) (ph:p∈P) : p^(v i p)≤k := by
    by_cases eq:i=f p
    · simpa [v,eq] using (show 1≤k by omega)
    rw [show v i p=e i p by simp [v,eq]]
    have dw : p^(e i p)∣w i := Nat.ordProj_dvd _ _
    have dm : p^(e i p)∣w (f p) := (pow_dvd_pow _ (mx p i ii)).trans (Nat.ordProj_dvd _ _)
    have ne : i.val≠(f p).val := fun h => eq (Fin.ext h)
    rcases lt_or_gt_of_ne ne with h|h
    · have dif := Nat.dvd_sub dm dw
      have E : w (f p)-w i=(f p).val-i.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans (f p).isLt.le)
    · have dif := Nat.dvd_sub dw dm
      have E : w i-w (f p)=i.val-(f p).val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans i.isLt.le)
  let A := ∏ q∈P,q^(J.sup (fun i => v i q))
  have cap : A≤k^J.card := by
    apply le_trans _ (Nat.pow_le_pow_right kp deficit.le)
    rw [←prod_const (s:=P) k]
    apply prod_le_prod'
    intro q hq
    obtain ⟨i,ii,eq⟩ := exists_mem_eq_sup J jne (fun i => v i q)
    rw [eq]
    exact vcap i ii q hq
  have ud (i:Fin k) (ii:i∈J) : u i∣A := by
    apply prod_dvd_prod_of_dvd
    intro q _
    exact pow_dvd_pow _ (le_sup (s:=J) (f:=fun i => v i q) ii)
  have Ap : 0<A := prod_pos fun q hq => pow_pos (pprime q hq).pos _
  have missing : ∃ i∈J,i∉P.image f := by
    by_contra! cover
    have h := (card_le_card cover).trans card_image_le
    omega
  obtain ⟨i,ij,absent⟩ := missing
  have iz : i∈Z := mem_filter.mpr ⟨ij,card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (by
    intro q h
    exact absent (mem_image.mpr ⟨q,(mem_filter.mp h).1,(mem_filter.mp h).2⟩)))⟩
  have nk := (zero i iz).trans ((Nat.le_of_dvd Ap (ud i ij)).trans cap)
  have udiv (i:Fin k) (ii:i∈J) : u i ∣ w i := ⟨remn i,split i ii⟩
  have gcdcap (i:Fin k) (ii:i∈J) (j:Fin k) (jj:j∈J) (ij:i≠j) : (u i).gcd (u j)≤k := by
    let g := (u i).gcd (u j)
    have di : g∣w i := (Nat.gcd_dvd_left ..).trans (udiv i ii)
    have dj : g∣w j := (Nat.gcd_dvd_right ..).trans (udiv j jj)
    have ne : i.val≠j.val := fun h => ij (Fin.ext h)
    rcases lt_or_gt_of_ne ne with h|h
    · have dif := Nat.dvd_sub dj di
      have E : w j-w i=j.val-i.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans j.isLt.le)
    · have dif := Nat.dvd_sub di dj
      have E : w i-w j=i.val-j.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans i.isLt.le)
  refine ⟨Z,B,p,fun i => e i (p i),u,filter_subset ..,filter_subset ..,count,nk,fun i _ => u0 i,zero,?_,?_⟩
  · intro W wJ
    have h := small_prod W (fun i _ => u0 i) kp (fun i hi j hj ne => gcdcap i (wJ hi) j (wJ hj) ne)
    have lc := (Nat.le_of_dvd Ap (show W.lcm u∣A from lcm_dvd (fun j hj => ud j (wJ hj)))).trans cap
    rw [pow_add]
    exact h.trans (Nat.mul_le_mul_right _ lc)


  · intro i hi
    refine ⟨pprime _ (member i hi).1,small _ (member i hi).1,?_⟩
    have r : remn i=(p i)^(e i (p i)) := by
      dsimp [remn]
      rw [prod_eq_single_of_mem (p i) (member i hi).1 (fun q hq ne => ?_),if_pos (member i hi).2.symm]
      have no : i≠f q := by
        intro eq
        have h : q∈F i := mem_filter.mpr ⟨hq,eq.symm⟩
        rw [singleton i hi] at h
        exact ne (mem_singleton.mp h)
      simp [no]
    exact (split i (mem_filter.mp hi).1).trans (congrArg (u i * ·) r)


private lemma height_div {a b:ℕ} (ha:0<a) (hb:0<b) :
    (((a:ℚ)/b).num.natAbs+((a:ℚ)/b).den) ≤ a+b := by
  have bd : ((b:ℤ))≠0 := by exact_mod_cast hb.ne'
  have n := Rat.num_dvd (a:ℤ) bd
  have d := Rat.den_dvd (a:ℤ) (b:ℤ)
  rw [Rat.divInt_eq_div] at n d
  push_cast at n d
  have hn := Int.natAbs_dvd_natAbs.mpr n
  have hd := Int.natAbs_dvd_natAbs.mpr d
  simp only [Int.natAbs_natCast] at hn hd
  exact Nat.add_le_add (Nat.le_of_dvd ha hn) (Nat.le_of_dvd hb hd)

private lemma log_near {x y N K:ℝ} (np:0<N) (kx:0≤K) (hx:N≤x) (hy:N≤y)
    (xa:x≤N+K) (ya:y≤N+K) : |log x-log y| ≤ K/N := by
  have xp := np.trans_le hx
  have yp := np.trans_le hy
  have one (v w:ℝ) (vp:0<v) (wp:0<w) (h:N≤w) (up:v≤N+K) : log v-log w≤K/N := by
    rw [←log_div vp.ne' wp.ne']
    have b := log_le_sub_one_of_pos (div_pos vp wp)
    have h' : v/w ≤ (N+K)/N :=
      div_le_div₀ (by linarith) up np h
    have e : (N+K)/N = 1+K/N := by field_simp
    linarith only [b,h',e]
  exact abs_sub_le_iff.mpr ⟨one x y xp yp hy xa,one y x yp xp hx ya⟩

private lemma logpower (a R:ℝ) (ha:0<a) (hR:0<R) :
    ∀ᶠ x:ℝ in atTop, (log x)^8 ≤ a*x^R := by
  have h := (isLittleO_log_rpow_rpow_atTop 8 hR).bound ha
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx h1
  simpa only [Real.rpow_natCast,Real.rpow_ofNat, Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (log_nonneg h1) _),
    abs_of_nonneg (rpow_nonneg (zero_le_one.trans h1) _)] using hx

private lemma rounded_pair {k:ℕ} (B:Finset (Fin k)) (p e u:Fin k→ℕ) (L l d:ℝ)
    (hL:1≤L) (hl:1≤l) (dp:0<d) (dc:d≤1/100)
    (size:L/l/4≤B.card) (big:100 < l^2) (bigD:100/d ≤ l^2) (slow:l^8≤d*L)
    (co:∀ i∈B,0<u i ∧ 0<p i ∧ log (u i:ℝ)≤d*L/16 ∧ log (p i:ℝ)≤3*l ∧ (e i:ℝ)≤4*L) :
    ∃ i∈B, ∃ j∈B, i≠j ∧ ∃ (m a b:ℕ), 0<a ∧ 0<b ∧
    u i*(p i)^(e i)=a*(p i)^m ∧ u j*(p j)^(e j)=b*(p j)^m ∧
    log (a:ℝ)≤d*L/4 ∧ log (b:ℝ)≤d*L/4 ∧ |log (a:ℝ)-log (b:ℝ)|≤l^6 ∧ (m:ℝ)≤4*L := by
  classical
  have lp : 0<l := by linarith
  have Lp : 0<L := by linarith
  let K := ⌊L/l^3⌋₊
  have scale : 2≤L/l^3 := by
    apply (le_div_iff₀ (pow_pos lp _)).mpr
    have e := pow_le_pow_right₀ hl (by decide : 3≤8)
    nlinarith only [e,slow,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have kp : 0<K := Nat.floor_pos.mpr (by linarith)
  have kr : 0<(K:ℝ) := by exact_mod_cast kp
  have kup : (K:ℝ)≤L/l^3 := Nat.floor_le (by positivity)
  have klo : L/l^3≤2*(K:ℝ) := by
    have h := Nat.lt_floor_add_one (L/l^3)
    change L/l^3<(K:ℝ)+1 at h
    linarith [show 1≤(K:ℝ) by exact_mod_cast kp]
  let m (i:Fin k) := (e i/K)*K
  let a (i:Fin k) := u i*(p i)^(e i%K)
  have afact (i:Fin k) : u i*(p i)^(e i)=a i*(p i)^(m i) := by
    dsimp [a,m]
    rw [mul_assoc,←pow_add,Nat.mul_comm (e i/K) K,Nat.mod_add_div]
  have apos (i:Fin k) (hi:i∈B) : 0<a i := by dsimp [a]; exact Nat.mul_pos (co i hi).1 (pow_pos (co i hi).2.1 _)
  have alog (i:Fin k) (hi:i∈B) : log (a i:ℝ)≤d*L/4 := by
    obtain ⟨up,pp,ul,pl,_⟩ := co i hi
    dsimp [a]
    rw [Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast up.ne') (by positivity [pp]),log_pow]
    have er : ((e i%K:ℕ):ℝ)≤L/l^3 := (show ((e i%K:ℕ):ℝ)≤(K:ℝ) by exact_mod_cast (Nat.mod_lt _ kp).le).trans kup
    have mul := mul_le_mul er pl (log_natCast_nonneg _) (by positivity)
    have small : (L/l^3)*(3*l)≤d*L/8 := by
      rw [show L/l^3*(3*l)=3*L/l^2 by field_simp]
      apply (div_le_iff₀ (sq_pos_of_pos lp)).mpr
      have h := (div_le_iff₀ dp).mp bigD
      nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
    linarith only [ul,mul,small,mul_pos dp Lp]
  have alL (i:Fin k) (hi:i∈B) : log (a i:ℝ)≤L := (alog i hi).trans (by nlinarith only [mul_le_mul_of_nonneg_right dc Lp.le,Lp.le])
  let bins := range (⌊8*l^3⌋₊+1) ×ˢ range (⌊L/l^6⌋₊+1)
  let key (i:Fin k) := (e i/K,⌊log (a i:ℝ)/l^6⌋₊)
  have maps (i:Fin k) (hi:i∈B) : key i∈bins := by
    apply mem_product.mpr
    constructor
    · apply mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_floor_iff (by positivity)).mpr
      have dd := Nat.cast_div_le (α:=ℝ) (m:=e i) (n:=K)
      apply dd.trans
      apply (div_le_iff₀ kr).mpr
      have h := (div_le_iff₀ (pow_pos lp 3)).mp klo
      nlinarith only [h,(co i hi).2.2.2.2]
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (alL i hi) (by positivity))))
  have count : bins.card<B.card := by
    have w1 : 1≤L/l^6 := by
      apply (le_div_iff₀ (pow_pos lp _)).mpr
      have e := pow_le_pow_right₀ hl (by decide : 6≤8)
      nlinarith only [e,slow,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
    have r1 : 1≤l^3 := one_le_pow₀ hl
    have a₁ := Nat.floor_le (show 0≤8*l^3 by positivity)
    have a₂ := Nat.floor_le (show 0≤L/l^6 by positivity)
    have bound : (bins.card:ℝ)≤18*L/l^3 := by
      simp only [bins,card_product,card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      have h := mul_le_mul (show (⌊8*l^3⌋₊:ℝ)+1≤9*l^3 by linarith) (show (⌊L/l^6⌋₊:ℝ)+1 ≤ 2*(L/l^6) by linarith) (by positivity) (by positivity)
      exact h.trans_eq (by field_simp; ring)
    have low : 18*L/l^3 < L/l/4 := by
      rw [show L/l/4=(l^2/4)*(L/l^3) by field_simp,mul_div_assoc]
      exact mul_lt_mul_of_pos_right (by linarith) (div_pos Lp (pow_pos lp _))
    exact_mod_cast (bound.trans_lt low).trans_le size
  obtain ⟨i,bi,j,bj,ne,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to count maps
  have first : e i/K=e j/K := congrArg Prod.fst eq
  have second : ⌊log (a i:ℝ)/l^6⌋₊=⌊log (a j:ℝ)/l^6⌋₊ := congrArg Prod.snd eq
  have wp : 0<l^6 := pow_pos lp _
  have li := Nat.floor_le (div_nonneg (log_natCast_nonneg (a i)) wp.le)
  have lj := Nat.floor_le (div_nonneg (log_natCast_nonneg (a j)) wp.le)
  have ui := Nat.lt_floor_add_one (log (a i:ℝ)/l^6)
  have uj := Nat.lt_floor_add_one (log (a j:ℝ)/l^6)
  rw [second] at li ui
  have diff : |log (a i:ℝ)/l^6-log (a j:ℝ)/l^6|≤1 := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  rw [←sub_div,abs_div,abs_of_pos wp,div_le_iff₀ wp,one_mul] at diff
  have ms : m i=m j := congrArg (· * K) first
  refine ⟨i,bi,j,bj,ne,m i,a i,a j,apos i bi,apos j bj,afact i,by rw [ms]; exact afact j,alog i bi,alog j bj,diff,?_⟩
  exact (show (m i:ℝ)≤(e i:ℝ) by exact_mod_cast Nat.div_mul_le_self (e i) K).trans (co i bi).2.2.2.2

private lemma forms {n k X Y a b p q e:ℕ} {S:ℝ} (nels:X≠Y)
    (xp:0<X) (yp:0<Y) (pa:0<a) (pb:0<b) (pp:0<p) (pq:0<q)
    (splX:X=a*p^e) (splY:Y=b*q^e) (np:0<n)
    (nx:n≤X) (ny:n≤Y) (xk:X≤n+k) (yk:Y≤n+k)
    (small:(k:ℝ)/n<(n:ℝ)^(-(1/2:ℝ))) (sp:0<S)
    (prime:(p:ℝ)+(q:ℝ)≤(log S)^16)
    (lo:2*log S/log (log S)≤(e:ℝ)) (hi:(e:ℝ)≤(log S)^16)
    (la:log (a:ℝ)≤log S-log 2) (lb:log (b:ℝ)≤log S-log 2)
    (delta:|log (a:ℝ)-log (b:ℝ)|≤(log S)^(3/4:ℝ)) :
    ∃ (u v:ℚ) (m:ℤ), 0<u ∧ 0<v ∧ ((u.num.natAbs+u.den:ℕ):ℝ)≤(log S)^16 ∧
    ((v.num.natAbs+v.den:ℕ):ℝ)≤S ∧ 2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (v:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧
    |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ)) := by
  let u : ℚ := (p:ℚ)/q
  let v : ℚ := (b:ℚ)/a
  have h₁ := Nat.cast_le (α:=ℝ).mpr (height_div pp pq)
  have h₂ := Nat.cast_le (α:=ℝ).mpr (height_div pb pa)
  push_cast at h₁ h₂
  have ca : (a:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pa) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have cb : (b:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pb) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have lu : log (u:ℝ)=log (p:ℝ)-log (q:ℝ) := by simp [u,log_div,pp.ne',pq.ne']
  have lv : log (v:ℝ)=log (b:ℝ)-log (a:ℝ) := by simp [v,log_div,pa.ne',pb.ne']
  have xl (z c d:ℕ) (hc:0<c) (hd:0<d) (eq:z=c*d^e) :
      log (z:ℝ)=log (c:ℝ)+(e:ℝ)*log (d:ℝ) := by rw [eq,Nat.cast_mul,Nat.cast_pow,log_mul (by positivity) (by positivity),log_pow]
  have hX := xl _ _ _ pa pp splX
  have hY := xl _ _ _ pb pq splY
  have eq : (e:ℝ)*log (u:ℝ)-log (v:ℝ)=log (X:ℝ)-log (Y:ℝ) := by rw [lu,lv,hX,hY]; ring
  have logne : log (X:ℝ)≠log (Y:ℝ) := fun h => nels (by exact_mod_cast (Real.log_injOn_pos (show (0:ℝ)<X by exact_mod_cast xp) (show (0:ℝ)<Y by exact_mod_cast yp) h))
  have close := log_near (x:=(X:ℝ)) (y:=(Y:ℝ)) (by exact_mod_cast np : (0:ℝ)<n) (Nat.cast_nonneg k) (by exact_mod_cast nx) (by exact_mod_cast ny)
    (by exact_mod_cast xk) (by exact_mod_cast yk)
  refine ⟨u,v,e,by dsimp [u]; positivity,by dsimp [v]; positivity,?_,?_,?_,?_,?_,?_,?_⟩
  · push_cast
    exact h₁.trans prime
  · push_cast
    exact h₂.trans (by linarith)
  · simpa using lo
  · simpa using hi
  · rwa [lv,abs_sub_comm]
  · rw [Int.cast_natCast,eq]; exact abs_pos.mpr (sub_ne_zero.mpr logne)
  · rw [Int.cast_natCast,eq]; exact close.trans_lt small

private theorem rounded : Rounded := by
  classical
  intro b hb S₀
  let d := min b (1/100:ℝ)
  have dp : 0<d := lt_min hb (by norm_num)
  have db : d≤b := min_le_left .. 
  have dc : d≤1/100 := min_le_right ..
  refine ⟨d,dp,dc,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have tD := (tendsto_const_mul_atTop_of_pos dp).mpr tL
  have tS := tendsto_exp_atTop.comp tD
  have tl2 := (tendsto_pow_atTop (by decide : 2≠0)).comp tl
  filter_upwards [eventually_ge_atTop 2,tL.eventually_ge_atTop 8,tl.eventually_ge_atTop 1,
    tl.eventually_ge_atTop (-2*log d),tL.eventually_ge_atTop (2/d^2),
    tD.eventually_ge_atTop 8,tS.eventually_ge_atTop S₀,tl2.eventually_gt_atTop (100+100/d),
    tL.eventually (logpower d 1 dp one_pos),tN.eventually (logpower 1 (1/2) one_pos (by norm_num))]
    with n hn hL hl hdlog hdL hD hS hδl hpow hNpow
  let L := log (n:ℝ)
  let l := log L
  let S := exp (d*L)
  let T := d*L/4
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change 8≤L at hL
  change 1≤l at hl
  change -2*log d ≤ l at hdlog
  change 2/d^2≤L at hdL
  change 8≤d*L at hD
  change S₀≤S at hS
  change 100+100/d<l^2 at hδl
  change l^8 ≤ d*L^(1:ℝ) at hpow
  rw [rpow_one] at hpow
  change L^8≤1*(n:ℝ)^(1/2:ℝ) at hNpow
  rw [one_mul,←sqrt_eq_rpow] at hNpow
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have sp : 0<S := exp_pos _
  have ls : log S=d*L := log_exp _
  have llS : l/2≤log (log S) := by rw [ls,log_mul dp.ne' Lp.ne']; change _≤log d+l; linarith
  have Spow : S≤(n:ℝ)^b := by rw [rpow_def_of_pos np]; apply exp_le_exp.mpr; dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_right db Lp.le]
  have sp2 : L≤(d*L)^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos dp)).mp hdL
    nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
  have cap16 : 4*L^3 ≤ (d*L)^16 := calc
    _ ≤ L^4 := by nlinarith only [mul_nonneg (show 0≤L-4 by linarith) (pow_nonneg Lp.le 3)]
    _ ≤ ((d*L)^2)^4 := pow_le_pow_left₀ Lp.le sp2 _
    _ = (d*L)^8 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have width : l^6 ≤ (log S)^(3/4:ℝ) := by
    rw [ls]
    calc l^6 = (l^8)^(3/4:ℝ) := by rw [←rpow_natCast_mul lp.le]; norm_num
         _ ≤ _ := rpow_le_rpow (by positivity) hpow (by norm_num)
  have wL : l^4≤L := by
    have h := pow_le_pow_right₀ hl (by decide : 4≤8)
    nlinarith only [h,hpow,mul_le_mul_of_nonneg_right dc Lp.le]
  intro k hk B p e u size row
  let Q := L/l
  change (k:ℝ)<Q^3 at hk
  change Q/4 ≤ (B.card:ℝ) at size
  have qp : 0<Q := div_pos Lp lp
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kl : (k:ℝ)≤L^3 := hk.le.trans (pow_le_pow_left₀ qp.le qL _)
  have root : (k:ℝ)<sqrt n := by
    have h : L^3<L^8 := pow_lt_pow_right₀ (by linarith) (by decide)
    exact kl.trans_lt (h.trans_le hNpow)
  have kn : k≤n := by
    have h := Real.sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)))
    exact_mod_cast root.le.trans h
  have ks : (k:ℝ)/n < (n:ℝ)^(-(1/2:ℝ)) := by
    rw [←show sqrt (n:ℝ)/n=(n:ℝ)^(-(1/2:ℝ)) by rw [sqrt_eq_rpow,show (n:ℝ)^(-(1/2:ℝ))=(n:ℝ)^((1/2:ℝ)-1) by norm_num,rpow_sub np,rpow_one]]
    exact div_lt_div_of_pos_right root np
  have bp : B.Nonempty := card_pos.mp (by exact_mod_cast (show 0<Q/4 by positivity).trans_le size)
  obtain ⟨ib,hib⟩ := bp
  have kp : 0<k := (row ib hib).1.pos.trans (row ib hib).2.1
  have logk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kl
    rwa [log_pow] at h
  let X (i:Fin k) := n+i.val+1
  have bounds (i:Fin k) : n≤X i ∧ X i≤n+k := by dsimp [X]; have := i.isLt; omega
  have xl (i:Fin k) (bi:i∈B) : log (X i:ℝ)=log (u i:ℝ)+(e i:ℝ)*log (p i:ℝ) := by
    have hi := row i bi
    dsimp only [X]
    rw [hi.2.2.2.2,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast hi.2.2.1.ne') (by positivity [hi.1.pos]),log_pow]
  have Llo (i:Fin k) : L≤log (X i:ℝ) := log_le_log np (by exact_mod_cast (bounds i).1)
  have Lup (i:Fin k) : log (X i:ℝ)≤2*L := by
    have h : (X i:ℝ)≤(n:ℝ)^2 := by exact_mod_cast ((bounds i).2.trans (by nlinarith : n+k≤n^2))
    have h' := log_le_log (by dsimp [X]; positivity) h
    rwa [log_pow] at h'
  have expbd (i:Fin k) (bi:i∈B) : (e i:ℝ)≤4*L := by
    have pp := (row i bi).1
    have lg := log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast pp.two_le : (2:ℝ)≤p i)
    have h := mul_le_mul_of_nonneg_left (show 1/2≤log (p i:ℝ) by linarith [log_two_gt_d9]) (Nat.cast_nonneg (e i))
    linarith only [h,xl i bi, Lup i,log_natCast_nonneg (u i)]
  obtain ⟨i,bi,j,bj,ij,m,a,b',ap,bp',fa,fb,ai,aj,close,mcap⟩ := rounded_pair B p e u L l d (by linarith) hl dp dc size
    (by linarith [show 0<100/d by positivity]) (by linarith) hpow (by
      intro z hz
      have h := row z hz
      exact ⟨h.2.2.1,h.1.pos,h.2.2.2.1,(log_le_log (show (0:ℝ)<p z by exact_mod_cast h.1.pos) (by exact_mod_cast h.2.1.le)).trans logk,expbd z hz⟩)
  have fX : X i=a*(p i)^m := (row i bi).2.2.2.2.trans fa
  have fY : X j=b'*(p j)^m := (row j bj).2.2.2.2.trans fb
  have lX : log (X i:ℝ)=log (a:ℝ)+(m:ℝ)*log (p i:ℝ) := by
    rw [fX,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast ap.ne') (by positivity [(row i bi).1.pos]),log_pow]
  have emin : 2*log S/log (log S)≤(m:ℝ) := by
    have plog := (log_le_log (show (0:ℝ)<p i by exact_mod_cast (row i bi).1.pos) (by exact_mod_cast (row i bi).2.1.le)).trans logk
    have h := mul_le_mul_of_nonneg_left plog (Nat.cast_nonneg m (α:=ℝ))
    have main : L ≤ T+(m:ℝ)*(3*l) := by dsimp [T]; linarith only [lX,Llo i,ai,h]
    apply (div_le_iff₀ (by linarith : 0<log (log S))).mpr
    rw [ls]
    have mult := mul_le_mul_of_nonneg_left llS (Nat.cast_nonneg m (α:=ℝ))
    dsimp [T] at main
    rw [ls] at mult
    linarith only [main,mult,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have ne : X i≠X j := by intro h; apply ij; apply Fin.ext; dsimp [X] at h; omega
  have heights : (p i:ℝ)+(p j:ℝ)≤(log S)^16 := by
    rw [ls]
    have pi : (p i:ℝ) ≤ k := by exact_mod_cast (row i bi).2.1.le
    have pj : (p j:ℝ) ≤ k := by exact_mod_cast (row j bj).2.1.le
    linarith only [pi,pj,kl,cap16,pow_nonneg Lp.le 3]
  have endE : (m:ℝ)≤(log S)^16 := by
    rw [ls]
    have h := pow_le_pow_right₀ (by linarith : 1≤L) (by decide : 1≤3)
    rw [pow_one] at h
    linarith only [mcap,h,cap16]
  have room : T≤log S-log 2 := by rw [ls]; dsimp [T]; linarith [log_two_lt_d9]
  obtain ⟨x,y,m,xx,yy,hx,hy,low,high,lv,nonzero,near⟩ := forms ne (by dsimp [X]; omega) (by dsimp [X]; omega)
    ap bp' (row i bi).1.pos (row j bj).1.pos fX fY
    (by omega : 0<n) (bounds i).1 (bounds j).1 (bounds i).2 (bounds j).2 ks sp heights emin endE (ai.trans room) (aj.trans room) (close.trans width)
  exact ⟨S,x,y,m,hS,Spow,xx,yy,hx,hy,low,high,lv,nonzero,near⟩


end OMA.GrimmSmall

theorem l2_proof : OMA.Erdos375H1R1.H2 :=
  OMA.GrimmSmall.main OMA.GrimmSmall.structural OMA.GrimmSmall.rounded
end L2Section

section L3Section
namespace OMA.L3
/- Ramachandra, Shorey and Tijdeman's large-obstruction extraction.
The factorial product bound leaves many rows with a small cofactor.
Two rows have the same prime exponent and the logarithms of their
cofactors occupy the same short interval. Subtracting their logarithmic
factorizations gives the required nonzero linear form. -/
open Finset Real Filter
open scoped Topology

private lemma height_div {a b:ℕ} (ha:0<a) (hb:0<b) :
    (((a:ℚ)/b).num.natAbs+((a:ℚ)/b).den) ≤ a+b := by
  have bd : ((b:ℤ))≠0 := by exact_mod_cast hb.ne'
  have n := Rat.num_dvd (a:ℤ) bd
  have d := Rat.den_dvd (a:ℤ) (b:ℤ)
  rw [Rat.divInt_eq_div] at n d
  push_cast at n d
  have hn := Int.natAbs_dvd_natAbs.mpr n
  have hd := Int.natAbs_dvd_natAbs.mpr d
  simp only [Int.natAbs_natCast] at hn hd
  exact Nat.add_le_add (Nat.le_of_dvd ha hn) (Nat.le_of_dvd hb hd)

private lemma log_near {x y N K:ℝ} (np:0<N) (kx:0≤K) (hx:N≤x) (hy:N≤y)
    (xa:x≤N+K) (ya:y≤N+K) : |log x-log y| ≤ K/N := by
  have xp := np.trans_le hx
  have yp := np.trans_le hy
  have one (v w:ℝ) (vp:0<v) (wp:0<w) (h:N≤w) (up:v≤N+K) : log v-log w≤K/N := by
    rw [←log_div vp.ne' wp.ne']
    have b := log_le_sub_one_of_pos (div_pos vp wp)
    have h' : v/w ≤ (N+K)/N :=
      div_le_div₀ (by linarith) up np h
    have e : (N+K)/N = 1+K/N := by field_simp
    linarith only [b,h',e]
  exact abs_sub_le_iff.mpr ⟨one x y xp yp hy xa,one y x yp xp hx ya⟩

private lemma logpower (a R:ℝ) (ha:0<a) (hR:0<R) :
    ∀ᶠ x:ℝ in atTop, (log x)^8 ≤ a*x^R := by
  have h := (isLittleO_log_rpow_rpow_atTop 8 hR).bound ha
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx h1
  simpa only [Real.rpow_natCast,Real.rpow_ofNat, Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (log_nonneg h1) _),
    abs_of_nonneg (rpow_nonneg (zero_le_one.trans h1) _)] using hx

private lemma find_pair {α:Type} [DecidableEq α] (B:Finset α) (u e:α→ℕ) (E:ℕ) (L l T δ:ℝ)
    (hL:1≤L) (hl:1≤l) (hT:0<T) (tL:T≤L) (dl:0<δ)
    (width:l^4≤L) (large:100 < δ*l^2) (cap:(E:ℝ)+1 ≤ 6*L)
    (size:δ*(L/l)^2 ≤ B.card)
    (sum:∑ i∈B, log (u i:ℝ) ≤ (δ*(L/l)^2)*T/4)
    (exp:∀ i∈B, e i≤E) :
    ∃ i∈B, ∃ j∈B, i≠j ∧ e i=e j ∧ log (u i:ℝ)≤T ∧ log (u j:ℝ)≤T ∧
      |log (u i:ℝ)-log (u j:ℝ)|≤l^4 := by
  classical
  let G := B.filter (fun i => log (u i:ℝ)≤T)
  let Z := B \ G
  have cost : (Z.card:ℝ)*T≤∑ i∈B, log (u i:ℝ) := by
    calc _ = ∑ _i∈Z,T := by simp
         _ ≤ ∑ i∈Z,log (u i:ℝ) := by
           apply sum_le_sum
           intro i hi
           obtain ⟨bi,ng⟩ := mem_sdiff.mp hi
           exact le_of_lt (lt_of_not_ge (fun h => ng (mem_filter.mpr ⟨bi,h⟩)))
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i _ _ => log_natCast_nonneg _)
  have zb : (Z.card:ℝ)≤δ*(L/l)^2/4 := by apply le_of_mul_le_mul_right _ hT; linarith only [cost,sum]
  have ecard : (Z.card:ℝ)+(G.card:ℝ)=B.card := by exact_mod_cast (card_sdiff_add_card_eq_card (show G⊆B from filter_subset ..) : Z.card+G.card=B.card)
  let bins := range (E+1) ×ˢ range (⌊L/l^4⌋₊+1)
  let key (i:α) := (e i,⌊log (u i:ℝ)/l^4⌋₊)
  have lp : 0<l := by linarith
  have wP : 0<l^4 := pow_pos lp _
  have maps (i:α) (hi:i∈G) : key i∈bins := by
    obtain ⟨bi,lt⟩ := mem_filter.mp hi
    exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (exp i bi)),
      mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (lt.trans tL) wP.le)))⟩
  have less : bins.card<G.card := by
    have fl := Nat.floor_le (show 0≤L/l^4 by positivity)
    have denom : 1 ≤ L/l^4 := (le_div_iff₀ wP).mpr (by simpa using width)
    have binsB : (bins.card:ℝ) ≤ 12*L^2/l^4 := by
      dsimp [bins]
      simp only [card_product,card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      have h := mul_le_mul cap (show (⌊L/l^4⌋₊:ℝ)+1 ≤ 2*(L/l^4) by linarith) (by positivity) (by positivity)
      exact h.trans_eq (by ring)
    have ratio : 12*L^2/l^4 < δ*(L/l)^2/2 := by
      rw [show δ*(L/l)^2/2=(δ*l^2/2)*(L^2/l^4) by field_simp,mul_div_assoc]
      exact mul_lt_mul_of_pos_right (by linarith) (div_pos (by positivity) wP)
    have pos : 0≤δ*(L/l)^2 := mul_nonneg dl.le (sq_nonneg _)
    have right : δ*(L/l)^2/2 ≤ (G.card:ℝ) := by linarith only [size,ecard,zb,pos]
    exact_mod_cast (binsB.trans_lt ratio).trans_le right
  obtain ⟨i,hi,j,hj,ne,kij⟩ := exists_ne_map_eq_of_card_lt_of_maps_to less maps
  have ei : e i=e j := congrArg Prod.fst kij
  have eq : ⌊log (u i:ℝ)/l^4⌋₊=⌊log (u j:ℝ)/l^4⌋₊ := congrArg Prod.snd kij
  have li := Nat.floor_le (div_nonneg (log_natCast_nonneg (u i)) wP.le)
  have lj := Nat.floor_le (div_nonneg (log_natCast_nonneg (u j)) wP.le)
  have ui := Nat.lt_floor_add_one (log (u i:ℝ)/l^4)
  have uj := Nat.lt_floor_add_one (log (u j:ℝ)/l^4)
  rw [eq] at li ui
  have diff : |log (u i:ℝ)/l^4-log (u j:ℝ)/l^4|≤1 := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  rw [←sub_div,abs_div,abs_of_pos wP, div_le_iff₀ wP, one_mul] at diff
  exact ⟨i,(mem_filter.mp hi).1,j,(mem_filter.mp hj).1,ne,ei,(mem_filter.mp hi).2,(mem_filter.mp hj).2,diff⟩

private lemma forms {n k X Y a b p q e:ℕ} {S:ℝ} (nels:X≠Y)
    (xp:0<X) (yp:0<Y) (pa:0<a) (pb:0<b) (pp:0<p) (pq:0<q)
    (splX:X=a*p^e) (splY:Y=b*q^e) (np:0<n)
    (nx:n≤X) (ny:n≤Y) (xk:X≤n+k) (yk:Y≤n+k)
    (small:(k:ℝ)/n<(n:ℝ)^(-(1/2:ℝ))) (sp:0<S)
    (prime:(p:ℝ)+(q:ℝ)≤(log S)^16)
    (lo:2*log S/log (log S)≤(e:ℝ)) (hi:(e:ℝ)≤(log S)^16)
    (la:log (a:ℝ)≤log S-log 2) (lb:log (b:ℝ)≤log S-log 2)
    (delta:|log (a:ℝ)-log (b:ℝ)|≤(log S)^(3/4:ℝ)) :
    ∃ (u v:ℚ) (m:ℤ), 0<u ∧ 0<v ∧ ((u.num.natAbs+u.den:ℕ):ℝ)≤(log S)^16 ∧
    ((v.num.natAbs+v.den:ℕ):ℝ)≤S ∧ 2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (v:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧
    |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ)) := by
  let u : ℚ := (p:ℚ)/q
  let v : ℚ := (b:ℚ)/a
  have h₁ := Nat.cast_le (α:=ℝ).mpr (height_div pp pq)
  have h₂ := Nat.cast_le (α:=ℝ).mpr (height_div pb pa)
  push_cast at h₁ h₂
  have ca : (a:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pa) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have cb : (b:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pb) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have lu : log (u:ℝ)=log (p:ℝ)-log (q:ℝ) := by simp [u,log_div,pp.ne',pq.ne']
  have lv : log (v:ℝ)=log (b:ℝ)-log (a:ℝ) := by simp [v,log_div,pa.ne',pb.ne']
  have xl (z c d:ℕ) (hc:0<c) (hd:0<d) (eq:z=c*d^e) :
      log (z:ℝ)=log (c:ℝ)+(e:ℝ)*log (d:ℝ) := by rw [eq,Nat.cast_mul,Nat.cast_pow,log_mul (by positivity) (by positivity),log_pow]
  have hX := xl _ _ _ pa pp splX
  have hY := xl _ _ _ pb pq splY
  have eq : (e:ℝ)*log (u:ℝ)-log (v:ℝ)=log (X:ℝ)-log (Y:ℝ) := by rw [lu,lv,hX,hY]; ring
  have logne : log (X:ℝ)≠log (Y:ℝ) := fun h => nels (by exact_mod_cast (Real.log_injOn_pos (show (0:ℝ)<X by exact_mod_cast xp) (show (0:ℝ)<Y by exact_mod_cast yp) h))
  have close := log_near (x:=(X:ℝ)) (y:=(Y:ℝ)) (by exact_mod_cast np : (0:ℝ)<n) (Nat.cast_nonneg k) (by exact_mod_cast nx) (by exact_mod_cast ny)
    (by exact_mod_cast xk) (by exact_mod_cast yk)
  refine ⟨u,v,e,by dsimp [u]; positivity,by dsimp [v]; positivity,?_,?_,?_,?_,?_,?_,?_⟩
  · push_cast
    exact h₁.trans prime
  · push_cast
    exact h₂.trans (by linarith)
  · simpa using lo
  · simpa using hi
  · rwa [lv,abs_sub_comm]
  · rw [Int.cast_natCast,eq]; exact abs_pos.mpr (sub_ne_zero.mpr logne)
  · rw [Int.cast_natCast,eq]; exact close.trans_lt small

theorem l3_proof : OMA.Erdos375H1R1.H3 := by
  classical
  intro b hb S₀ δ hδ
  let d := min b (1/100:ℝ)
  have dp : 0<d := lt_min hb (by norm_num)
  have db : d≤b := min_le_left .. 
  have dc : d≤1/100 := min_le_right ..
  let c := min 1 (δ*d/100)
  have cp : 0<c := lt_min one_pos (by positivity)
  have c1 : c≤1 := min_le_left ..
  have cd : c≤δ*d/100 := min_le_right ..
  refine ⟨c,cp,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have tD := (tendsto_const_mul_atTop_of_pos dp).mpr tL
  have tS := tendsto_exp_atTop.comp tD
  have tl2 := (tendsto_pow_atTop (by decide : 2≠0)).comp tl
  filter_upwards [eventually_ge_atTop 2,tL.eventually_ge_atTop 8,tl.eventually_ge_atTop 1,
    tl.eventually_ge_atTop (-2*log d),tL.eventually_ge_atTop (2/d^2),
    tD.eventually_ge_atTop 8,tS.eventually_ge_atTop S₀,tl2.eventually_gt_atTop (100/δ),
    tL.eventually (logpower d 1 dp one_pos),tN.eventually (logpower 1 (1/2) one_pos (by norm_num))]
    with n hn hL hl hdlog hdL hD hS hδl hpow hNpow
  let L := log (n:ℝ)
  let l := log L
  let S := exp (d*L)
  let T := d*L/4
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change 8≤L at hL
  change 1≤l at hl
  change -2*log d ≤ l at hdlog
  change 2/d^2≤L at hdL
  change 8≤d*L at hD
  change S₀≤S at hS
  change 100/δ<l^2 at hδl
  change l^8 ≤ d*L^(1:ℝ) at hpow
  rw [rpow_one] at hpow
  change L^8≤1*(n:ℝ)^(1/2:ℝ) at hNpow
  rw [one_mul,←sqrt_eq_rpow] at hNpow
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have sp : 0<S := exp_pos _
  have ls : log S=d*L := log_exp _
  have llS : l/2≤log (log S) := by rw [ls,log_mul dp.ne' Lp.ne']; change _≤log d+l; linarith
  have Spow : S≤(n:ℝ)^b := by rw [rpow_def_of_pos np]; apply exp_le_exp.mpr; dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_right db Lp.le]
  have sp2 : L≤(d*L)^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos dp)).mp hdL
    nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
  have cap16 : 4*L^3 ≤ (d*L)^16 := calc
    _ ≤ L^4 := by nlinarith only [mul_nonneg (show 0≤L-4 by linarith) (pow_nonneg Lp.le 3)]
    _ ≤ ((d*L)^2)^4 := pow_le_pow_left₀ Lp.le sp2 _
    _ = (d*L)^8 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have width : l^4 ≤ (log S)^(3/4:ℝ) := by
    rw [ls]
    calc l^4 ≤ l^6 := pow_le_pow_right₀ hl (by decide)
         _ = (l^8)^(3/4:ℝ) := by rw [←rpow_natCast_mul lp.le]; norm_num
         _ ≤ _ := rpow_le_rpow (by positivity) hpow (by norm_num)
  have wL : l^4≤L := by
    have h := pow_le_pow_right₀ hl (by decide : 4≤8)
    nlinarith only [h,hpow,mul_le_mul_of_nonneg_right dc Lp.le]
  intro k hk B p e u size fac _inj row
  let Q := L/l
  change (k:ℝ)<c*Q^3 at hk
  change δ*Q^2 ≤ (B.card:ℝ) at size
  have qp : 0<Q := div_pos Lp lp
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kl : (k:ℝ)≤L^3 := calc
    _ ≤ c*Q^3 := hk.le
    _ ≤ 1*L^3 := mul_le_mul c1 (pow_le_pow_left₀ qp.le qL _) (by positivity) (by norm_num)
    _ = _ := one_mul _
  have root : (k:ℝ)<sqrt n := by
    have h : L^3<L^8 := pow_lt_pow_right₀ (by linarith) (by decide)
    exact kl.trans_lt (h.trans_le hNpow)
  have kn : k≤n := by
    have h := Real.sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)))
    exact_mod_cast root.le.trans h
  have ks : (k:ℝ)/n < (n:ℝ)^(-(1/2:ℝ)) := by
    rw [←show sqrt (n:ℝ)/n=(n:ℝ)^(-(1/2:ℝ)) by rw [sqrt_eq_rpow,show (n:ℝ)^(-(1/2:ℝ))=(n:ℝ)^((1/2:ℝ)-1) by norm_num,rpow_sub np,rpow_one]]
    exact div_lt_div_of_pos_right root np
  have bp : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hδ (sq_pos_of_pos qp)).trans_le size)
  obtain ⟨ib,hib⟩ := bp
  have kp : 0<k := (row ib hib).1.pos.trans (row ib hib).2.1
  have logk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kl
    rwa [log_pow] at h
  have prod : ∑ i∈B,log (u i:ℝ) ≤ (k:ℝ)*log k := by
    have h : (∏ i∈B,(u i:ℝ))≤(k:ℝ)^k := by exact_mod_cast fac.trans k.factorial_le_pow
    have pos : 0<∏ i∈B,(u i:ℝ) := prod_pos fun i hi => by exact_mod_cast (row i hi).2.2.1
    have hlog := log_le_log pos h
    rwa [log_prod (fun i hi => by exact_mod_cast (row i hi).2.2.1.ne'),log_pow] at hlog
  have cost : ∑ i∈B,log (u i:ℝ) ≤ δ*Q^2*T/4 := by
    apply prod.trans
    calc _ ≤ (c*Q^3)*(3*l) := mul_le_mul hk.le logk (log_natCast_nonneg _) (by positivity)
         _ = 3*c*Q^2*L := by dsimp [Q]; field_simp <;> ring
         _ ≤ _ := by dsimp [T]; nlinarith only [mul_le_mul_of_nonneg_right cd (mul_nonneg (sq_nonneg Q) Lp.le),mul_nonneg (mul_nonneg hδ.le dp.le) (mul_nonneg (sq_nonneg Q) Lp.le)]
  let X (i:Fin k) := n+i.val+1
  have bounds (i:Fin k) : n≤X i ∧ X i≤n+k := by dsimp [X]; have := i.isLt; omega
  have xl (i:Fin k) (bi:i∈B) : log (X i:ℝ)=log (u i:ℝ)+(e i:ℝ)*log (p i:ℝ) := by
    have hi := row i bi
    dsimp only [X]
    rw [hi.2.2.2,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast hi.2.2.1.ne') (by positivity [hi.1.pos]),log_pow]
  have Llo (i:Fin k) : L≤log (X i:ℝ) := log_le_log np (by exact_mod_cast (bounds i).1)
  have Lup (i:Fin k) : log (X i:ℝ)≤2*L := by
    have h : (X i:ℝ)≤(n:ℝ)^2 := by exact_mod_cast ((bounds i).2.trans (by nlinarith : n+k≤n^2))
    have h' := log_le_log (by dsimp [X]; positivity) h
    rwa [log_pow] at h'
  have expbd (i:Fin k) (bi:i∈B) : (e i:ℝ)≤4*L := by
    have pp := (row i bi).1
    have lg := log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast pp.two_le : (2:ℝ)≤p i)
    have h := mul_le_mul_of_nonneg_left (show 1/2≤log (p i:ℝ) by linarith [log_two_gt_d9]) (Nat.cast_nonneg (e i))
    linarith only [h,xl i bi, Lup i,log_natCast_nonneg (u i)]
  let E := ⌊4*L⌋₊
  have eNat (i:Fin k) (bi:i∈B) : e i≤E := (Nat.le_floor_iff (by positivity)).mpr (expbd i bi)
  have ecap : (E:ℝ)+1≤6*L := by have h := Nat.floor_le (show 0≤4*L by positivity); change (E:ℝ)≤4*L at h; linarith
  have tlb : 0<T := by dsimp [T]; positivity
  have thresholdL : T≤L := by dsimp [T]; nlinarith only [mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  obtain ⟨i,bi,j,bj,ij,ee,ai,aj,close⟩ := find_pair B u e E L l T δ (by linarith) hl tlb thresholdL hδ wL
    (by have h := (div_lt_iff₀ hδ).mp hδl; linarith) ecap size cost eNat
  have emin : 2*log S/log (log S)≤(e i:ℝ) := by
    have plog := (log_le_log (show (0:ℝ)<p i by exact_mod_cast (row i bi).1.pos) (by exact_mod_cast (row i bi).2.1.le)).trans logk
    have h := mul_le_mul_of_nonneg_left plog (Nat.cast_nonneg (e i) (α:=ℝ))
    have main : L ≤ T+(e i:ℝ)*(3*l) := by linarith only [xl i bi,Llo i,ai,h]
    apply (div_le_iff₀ (by linarith : 0<log (log S))).mpr
    rw [ls]
    have mult := mul_le_mul_of_nonneg_left llS (Nat.cast_nonneg (e i) (α:=ℝ))
    dsimp [T] at main
    rw [ls] at mult
    linarith only [main,mult,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have same : X j=u j*(p j)^(e i) := by rw [ee]; exact (row j bj).2.2.2
  have ne : X i≠X j := by intro h; apply ij; apply Fin.ext; dsimp [X] at h; omega
  have heights : (p i:ℝ)+(p j:ℝ)≤(log S)^16 := by
    rw [ls]
    have pi : (p i:ℝ) ≤ k := by exact_mod_cast (row i bi).2.1.le
    have pj : (p j:ℝ) ≤ k := by exact_mod_cast (row j bj).2.1.le
    linarith only [pi,pj,kl,cap16,pow_nonneg Lp.le 3]
  have endE : (e i:ℝ)≤(log S)^16 := by
    rw [ls]
    have h := pow_le_pow_right₀ (by linarith : 1≤L) (by decide : 1≤3)
    rw [pow_one] at h
    linarith only [expbd i bi,h,cap16]
  have room : T≤log S-log 2 := by rw [ls]; dsimp [T]; linarith [log_two_lt_d9]
  obtain ⟨x,y,m,xx,yy,hx,hy,low,high,lv,nonzero,near⟩ := forms ne (by dsimp [X]; omega) (by dsimp [X]; omega)
    (row i bi).2.2.1 (row j bj).2.2.1 (row i bi).1.pos (row j bj).1.pos (row i bi).2.2.2 same
    (by omega : 0<n) (bounds i).1 (bounds j).1 (bounds i).2 (bounds j).2 ks sp heights emin endE (ai.trans room) (aj.trans room) (close.trans width)
  exact ⟨S,x,y,m,hS,Spow,xx,yy,hx,hy,low,high,lv,nonzero,near⟩
end OMA.L3
end L3Section

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_log_R1.H1 :=
  OMA.Erdos375H1R1.main OMA.L1.l1_proof l2_proof OMA.L3.l3_proof
