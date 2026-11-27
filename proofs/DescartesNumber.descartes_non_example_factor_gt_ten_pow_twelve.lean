import FormalConjectures.Wikipedia.DescartesNumber
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.MaxPowDiv

/-!
A kernel-checked version of the Descartes factorization bound of
[László Tóth](https://cmst.eu/articles/on-the-density-of-spoof-odd-perfect-numbers/).

An odd spoof prime makes the divisor sum odd, so the other factor is a square.
A geometric-series bound for the divisor sum restricts the square root to
multiples of a short list of products of small primes. The remaining cases use
exact divisor sums from prime-power factorization.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace OMA.DescartesSearch

private def trialProduct : ℕ := 19590340644999083431262508198206381046123972390589368223882605328968666316379870661851951648789482321596229559115436019149189529725215266728292282990852649023362731392404017939142010958261393634959471483757196721672243410067118516227661133135192488848989914892157188308679896875137439519338903968094905549750386407106033836586660683539201011635917900039904495065203299749542985993134669814805318474080581207891125910

private def check (ok : ℕ → Bool) (lo n : ℕ) : Bool :=
  if n = 0 then true
  else if n = 1 then ok lo
  else check ok lo (n/2) && check ok (lo+n/2) (n-n/2)
termination_by n
decreasing_by all_goals omega

private theorem check_sound (ok : ℕ → Bool) (lo len : ℕ) (h : check ok lo len = true)
    {i : ℕ} (hlo : lo ≤ i) (hhi : i < lo+len) : ok i = true := by
  rw [check] at h
  split_ifs at h with h0 h1
  · omega
  · have : i = lo := by omega
    simpa [this] using h
  · rw [Bool.and_eq_true] at h
    by_cases hleft : i < lo+len/2
    · exact check_sound ok lo (len/2) h.1 hlo hleft
    · exact check_sound ok (lo+len/2) (len-len/2) h.2 (by omega) (by omega)
termination_by len
decreasing_by all_goals omega

private def passesTrialProduct (p : ℕ) : Bool :=
  (p < 2) || (p.minFac != p) || (trialProduct % p == 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem trial_certificate : check passesTrialProduct 0 1001 = true := by decide +kernel

private theorem prime_dvd_trialProduct (p : ℕ) (hp : p.Prime) (hle : p ≤ 1000) :
    p ∣ trialProduct := by
  have hc := check_sound _ 0 1001 trial_certificate (Nat.zero_le p) (by omega)
  have hn : ¬ p < 2 := Nat.not_lt_of_ge hp.two_le
  simpa [passesTrialProduct,hn,hp.minFac_eq, Nat.dvd_iff_mod_eq_zero] using hc

private def candidatePrime (n : ℕ) : ℕ :=
  let g := Nat.gcd n trialProduct
  if g = 1 then n else g.minFac

private theorem candidatePrime_spec {n : ℕ} (hn : 1 < n) (hbound : n ≤ 1000000) :
    (candidatePrime n).Prime ∧ candidatePrime n ∣ n := by
  unfold candidatePrime
  dsimp only
  split_ifs with hg
  · refine ⟨?_, dvd_refl _⟩
    by_contra hnp
    have hndvd := Nat.minFac_dvd n
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hs := Nat.minFac_sq_le_self (show 0 < n by omega) hnp
    have hle : n.minFac ≤ 1000 := by
      by_contra! hc
      have hsq := Nat.pow_le_pow_left hc 2
      norm_num at hsq
      omega
    have hd := Nat.dvd_gcd hndvd (prime_dvd_trialProduct n.minFac hp hle)
    rw [hg] at hd
    exact hp.not_dvd_one hd
  · exact ⟨Nat.minFac_prime hg, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)⟩

private def geom (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + p * geom p k

private theorem geom_eq (p k : ℕ) : geom p k = ∑ i ∈ range k,p^i := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [geom, ih, sum_range_succ', pow_zero, Nat.add_comm 1, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [pow_succ, mul_comm]

private def fastSigmaSq : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel+1, n =>
    if n ≤ 1 then 1
    else
      let p := candidatePrime n
      let a := p.maxPowDvdDiv n
      geom p (2*a.1+1) * fastSigmaSq fuel a.2

private theorem fastSigmaSq_spec (fuel n : ℕ) (hn : 0 < n)
    (hpow : n ≤ 2^fuel) (hbound : n ≤ 1000000) : fastSigmaSq fuel n = σ 1 (n^2) := by
  induction fuel generalizing n with
  | zero =>
    have h : n = 1 := by simp only [pow_zero] at hpow; omega
    simp [h,fastSigmaSq]
  | succ k ih =>
    by_cases ht : n ≤ 1
    · have h : n = 1 := by omega
      simp [h,fastSigmaSq]
    · have hnt : 1 < n := by omega
      let p := candidatePrime n
      have ⟨hp,hpd⟩ := candidatePrime_spec hnt hbound
      let e := padicValNat p n
      let q := Nat.divMaxPow n p
      have he : 1 ≤ e :=
        (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hn.ne').mp (by simpa using hpd)
      have hq : p^e*q = n := Nat.pow_padicValNat_mul_divMaxPow p n
      have hq0 : 0 < q := by
        apply Nat.pos_of_ne_zero
        intro h
        rw [h,mul_zero] at hq
        omega
      have hqc : ¬ p ∣ q := Nat.not_dvd_divMaxPow hp.one_lt hn.ne'
      have hqle : q ≤ 2^k := by
        have hpe : 2 ≤ p^e := hp.two_le.trans (Nat.le_pow (by omega : 0 < e))
        have hm := Nat.mul_le_mul_right q hpe
        rw [hq] at hm
        rw [pow_succ,Nat.mul_comm] at hpow
        omega
      have hqb : q ≤ 1000000 := (Nat.le_of_dvd hn ⟨p^e,by rw [mul_comm,hq]⟩).trans hbound
      have hc : (p^(2*e)).Coprime (q^2) :=
        ((hp.coprime_iff_not_dvd.mpr hqc).pow_left _).pow_right _
      rw [fastSigmaSq, if_neg ht]
      change geom p (2*e+1) * fastSigmaSq k q = σ 1 (n^2)
      rw [geom_eq, ih q hq0 hqle hqb, ← hq, mul_pow, ← pow_mul, Nat.mul_comm e 2,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
        ArithmeticFunction.sigma_one_apply_prime_pow hp]

private def passes (n : ℕ) : Bool :=
  let s := fastSigmaSq 20 n
  let d := 2*n^2-s
  (n == 1) || (n == 3003) || (d == 0) || (s % d != 0)

private theorem sigma_odd_of_factorization {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    Odd (σ 1 m) := by
  obtain ⟨hm,hw⟩ := Nat.odd_mul.mp h.2.1
  have hc : w.Coprime (w+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hd : w ∣ σ 1 m := hc.dvd_of_dvd_mul_right ⟨2*m,by simpa [mul_comm w] using h.2.2.2⟩
  obtain ⟨k,hk⟩ := hd
  have hw0 : 0 < w := by obtain ⟨v,hv⟩ := hw; omega
  obtain ⟨v,hv⟩ : Even (w+1) := by obtain ⟨v,hv⟩ := hw; exact ⟨v+1,by omega⟩
  have he : w * (k*(v+v)) = w*(2*m) := by
    calc
      _ = σ 1 m * (w+1) := by rw [hk,hv]; ring
      _ = _ := by rw [h.2.2.2]; ring
  have he' := Nat.eq_of_mul_eq_mul_left hw0 he
  have hm' : m = k*v := by
    have hterm : k*(v+v) = 2*(k*v) := by ring
    omega
  rw [hk]
  exact hw.mul ((Nat.odd_mul.mp (hm' ▸ hm)).1)

private theorem exists_odd_square_of_sigma {m : ℕ} (hm : Odd m) (hs : Odd (σ 1 m)) :
    ∃ r : ℕ, Odd r ∧ m = r^2 := by
  have hm0 : m ≠ 0 := by obtain ⟨v,hv⟩ := hm; omega
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0] at hs
  simp only [mul_one] at hs
  have he (p : ℕ) (hp : p ∈ m.primeFactors) : Even (m.factorization p) := by
    let a := m.factorization p
    let F := fun p : ℕ => ∑ i ∈ range (m.factorization p + 1), p^i
    have hF : Odd (F p) := by
      by_contra! hb
      have h2 : 2 ∣ F p := even_iff_two_dvd.mp ((Nat.not_odd_iff_even).mp hb)
      exact (Nat.not_even_iff_odd.mpr hs)
        (even_iff_two_dvd.mpr (h2.trans (Finset.dvd_prod_of_mem F hp)))
    have hodd : Odd p := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have ha : Odd (a+1) := by
      change Odd (∑ i ∈ range (a+1),p^i) at hF
      rw [Finset.odd_sum_iff_odd_card_odd] at hF
      have hall : ∀ i ∈ range (a+1), Odd (p^i) := fun _ _ => hodd.pow
      simpa only [Finset.filter_true_of_mem hall, Finset.card_range] using hF
    obtain ⟨j,hj⟩ := ha
    exact ⟨j,by omega⟩
  refine ⟨∏ p ∈ m.primeFactors,p^(m.factorization p/2), ?_, ?_⟩
  · have hq : (∏ p ∈ m.primeFactors,p^(m.factorization p/2)) ∣ m := by
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
      exact prod_dvd_prod_of_dvd _ _ (fun _ _ => pow_dvd_pow _ (Nat.div_le_self _ _))
    exact hm.of_dvd_nat hq
  · rw [← Finset.prod_pow]
    calc
      m = ∏ p ∈ m.primeFactors,p^m.factorization p := Nat.prod_primeFactors_pow_factorization hm0
      _ = _ := by
        apply prod_congr rfl
        intro p hp
        rw [← pow_mul, show m.factorization p / 2 * 2 = m.factorization p by
          obtain ⟨k,hk⟩ := he p hp
          omega]

private theorem bound_weight {n : ℕ} (hn : 0 < n) :
    σ 1 n * (∏ p ∈ n.primeFactors,(p-1)) ≤ n * (∏ p ∈ n.primeFactors,p) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne',
    ← Finset.prod_mul_distrib]
  conv_rhs =>
    lhs
    rw [Nat.prod_primeFactors_pow_factorization hn.ne']
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hx : p-1+1 = p := by have := hprime.one_lt; omega
  have hsub := geom_sum_mul_add (p-1) (n.factorization p + 1)
  rw [hx] at hsub
  simp only [mul_one,pow_succ _ (n.factorization p)] at hsub ⊢
  omega

private theorem ratio_ge_nine_fifths {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    9*m ≤ 5*σ 1 m := by
  have hwodd := (Nat.odd_mul.mp h.2.1).2
  have hw9 : 9 ≤ w := by
    by_contra! hw
    have hv : ∀ u : Fin 9, ¬ (u.val.Composite ∧ Odd u.val) := by decide
    exact hv ⟨w,hw⟩ ⟨h.1,hwodd⟩
  have he := h.2.2.2
  have hσ : σ 1 m ≤ 2*m := by
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt (by omega : 0 < w)
    have hq : σ 1 m * w ≤ σ 1 m * (w+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hd : (2*m-σ 1 m)*w = σ 1 m := by
    rw [Nat.sub_mul, Nat.mul_succ] at *
    omega
  have hmul := Nat.mul_le_mul_left (2*m-σ 1 m) hw9
  rw [hd] at hmul
  omega

private def smallPrimes : List ℕ := [3,5,7,11,13,17,19,23,29,31]
private def searchBases : List ℕ := [15,21,429,561,663,85085,627,741,95095,759,897,115115,22287,957,871131]

private def admissible (P D k : ℕ) : Bool :=
  !(P * 32^k ≤ 1000000 && 9*D*31^k ≤ 5*P*32^k) || searchBases.any (fun b => P%b==0)

private def checkMasks : List ℕ → ℕ → ℕ → Bool
  | [], P, D => admissible P D 0 && admissible P D 1 && admissible P D 2 && admissible P D 3
  | p::ps, P, D => checkMasks ps P D && checkMasks ps (P*p) (D*(p-1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem mask_certificate : checkMasks smallPrimes 1 1 = true := by decide +kernel

private theorem mask_sound (ps : List ℕ) (P D : ℕ) (hnd : ps.Nodup)
    (h : checkMasks ps P D = true) (S : Finset ℕ) (hS : S ⊆ ps.toFinset)
    (k : ℕ) (hk : k ≤ 3) : admissible (P * ∏ p ∈ S,p) (D * ∏ p ∈ S,(p-1)) k = true := by
  classical
  induction ps generalizing P D S with
  | nil =>
    have hs : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    subst S
    simp only [prod_empty,mul_one]
    simp only [checkMasks,Bool.and_eq_true] at h
    obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    · exact h.1.1.1
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  | cons p ps ih =>
    have ⟨hp,hps⟩ := List.nodup_cons.mp hnd
    simp only [checkMasks,Bool.and_eq_true] at h
    by_cases hpm : p ∈ S
    · have hsub : S.erase p ⊆ ps.toFinset := by
        intro q hq
        have hqS := hS (Finset.mem_of_mem_erase hq)
        simpa only [List.mem_toFinset, List.mem_cons,
          show q ≠ p from Finset.ne_of_mem_erase hq, false_or] using hqS
      rw [← Finset.insert_erase hpm,prod_insert (Finset.notMem_erase p S),
        prod_insert (Finset.notMem_erase p S),← mul_assoc,← mul_assoc]
      exact ih (P*p) (D*(p-1)) hps h.2 (S.erase p) hsub
    · have hsub : S ⊆ ps.toFinset := by
        intro q hq
        have hqS := hS hq
        have hqp : q ≠ p := fun hc => hpm (hc ▸ hq)
        simpa only [List.mem_toFinset,List.mem_cons,hqp,false_or] using hqS
      exact ih P D hps h.1 S hsub

private theorem prune {r : ℕ} (hr : Odd r) (hle : r ≤ 1000000)
    (hs : 9*r^2 ≤ 5*σ 1 (r^2)) : ∃ b ∈ searchBases, b ∣ r := by
  classical
  let S := r.primeFactors.filter (fun p => p≤31)
  let T := r.primeFactors.filter (fun p => ¬ p≤31)
  have hS : S ⊆ smallPrimes.toFinset := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hp2 : 2 < p := by
      have he := hr.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
      have := hpr.two_le
      rw [Nat.odd_iff] at he
      omega
    have hup := (mem_filter.mp hp).2
    have hi : ∀ p : Fin 32, 2 < p.val → p.val.Prime → p.val ∈ smallPrimes.toFinset := by decide +kernel
    exact hi ⟨p,by omega⟩ hp2 hpr
  have hr0 : 0 < r := by obtain ⟨v,hv⟩ := hr; omega
  have he := bound_weight (show 0 < r^2 by positivity)
  rw [Nat.primeFactors_pow _ (by decide : 2 ≠ 0)] at he
  have hrad : (∏ p ∈ r.primeFactors,p) ∣ r := Nat.prod_primeFactors_dvd _
  have hD : 9*(∏ p ∈ r.primeFactors,(p-1)) ≤ 5*(∏ p ∈ r.primeFactors,p) := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < r^2 by positivity)
    calc
      _ = (9*r^2)*(∏ p ∈ r.primeFactors,(p-1)) := by ring
      _ ≤ (5*σ 1 (r^2))*(∏ p ∈ r.primeFactors,(p-1)) := Nat.mul_le_mul_right _ hs
      _ = 5*(σ 1 (r^2) * (∏ p ∈ r.primeFactors,(p-1))) := by ring
      _ ≤ 5*(r^2*(∏ p ∈ r.primeFactors,p)) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  have hsplit (f : ℕ → ℕ) : (∏ p ∈ S,f p) * (∏ p ∈ T,f p) = ∏ p ∈ r.primeFactors,f p :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← hsplit (fun p => p),← hsplit (fun p => (p-1))] at hD
  rw [← hsplit (fun p => p)] at hrad
  have hPbound : (∏ p ∈ S,p)*32^T.card ≤ 1000000 := by
    refine (Nat.mul_le_mul_left _
      (show 32^T.card ≤ ∏ p ∈ T,p from ?_)).trans ((Nat.le_of_dvd hr0 hrad).trans hle)
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => by have := (mem_filter.mp hp).2; omega
  have hP0 : 0 < ∏ p ∈ S,p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
  have hk : T.card ≤ 3 := by
    by_contra! hc
    have hq : 32^4 ≤ 32^T.card := Nat.pow_le_pow_right (by decide) (by omega)
    have : 32^T.card ≤ (∏ p ∈ S,p)*32^T.card :=
      by simpa using Nat.mul_le_mul_right (32^T.card) hP0
    have := hq.trans (this.trans hPbound)
    norm_num at this
  have hq : (∏ p ∈ T,p) * 31^T.card ≤ (∏ p ∈ T,(p-1))*32^T.card := by
    rw [← Finset.prod_const,← Finset.prod_const,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro p hp
    have := (mem_filter.mp hp).2
    omega
  have hT0 : 0 < ∏ p ∈ T,(p-1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    omega
  have hineq : 9*(∏ p ∈ S,(p-1))*31^T.card ≤ 5*(∏ p ∈ S,p)*32^T.card := by
    refine Nat.le_of_mul_le_mul_right ?_ hT0
    calc
      _ = (9*((∏ p ∈ S,(p-1))*(∏ p ∈ T,(p-1))))*31^T.card := by ring
      _ ≤ (5*((∏ p ∈ S,p)*(∏ p ∈ T,p)))*31^T.card := Nat.mul_le_mul_right _ hD
      _ = (5*(∏ p ∈ S,p))*((∏ p ∈ T,p)*31^T.card) := by ring
      _ ≤ (5*(∏ p ∈ S,p))*((∏ p ∈ T,(p-1))*32^T.card) := Nat.mul_le_mul_left _ hq
      _ = _ := by ring
  have hcert := mask_sound smallPrimes 1 1 (by decide) mask_certificate S hS T.card hk
  simp only [one_mul,admissible,decide_eq_true hPbound,decide_eq_true hineq,
    Bool.true_and,Bool.not_true,Bool.false_or,List.any_eq_true,
    beq_iff_eq,← Nat.dvd_iff_mod_eq_zero] at hcert
  obtain ⟨b,hb,hbd⟩ := hcert
  exact ⟨b,hb,hbd.trans ((dvd_mul_right _ _).trans hrad)⟩

private theorem deficit_mul {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    (2*m-σ 1 m)*w = σ 1 m := by
  have he := h.2.2.2
  have hw : 0 < w := h.1.1.trans' (by decide)
  have hσ : σ 1 m ≤ 2*m := by
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt hw
    have hq : σ 1 m * w ≤ σ 1 m * (w+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [Nat.sub_mul]
  rw [Nat.mul_succ] at he
  omega

theorem lower_of_checked
    (progressions : ∀ b ∈ searchBases, ∀ i : ℕ, b*(2*i+1) ≤ 1000000 → passes (b*(2*i+1)) = true)
    (m w : ℕ) (h : DescartesNumber.IsDescartesFactorization m w)
    (hne : m * w ≠ DescartesNumber.descartesExample) : 10^12 < m := by
  by_contra! hbound
  have hm := (Nat.odd_mul.mp h.2.1).1
  obtain ⟨r,hr,rfl⟩ := exists_odd_square_of_sigma hm (sigma_odd_of_factorization h)
  have hrb : r ≤ 1000000 := by
    by_contra! hnot
    have hp : 1000001^2 ≤ r^2 := Nat.pow_le_pow_left hnot 2
    norm_num at hp hbound
    omega
  have hr0 : 0 < r := by obtain ⟨i,hi⟩ := hr; omega
  obtain ⟨b,hb,t,hrt⟩ := prune hr hrb (ratio_ge_nine_fifths h)
  obtain ⟨i,hi⟩ := (Nat.odd_mul.mp (show Odd (b*t) from hrt ▸ hr)).2
  have hre : r = b*(2*i+1) := by rw [hrt,hi]
  have hcheck : passes r = true := by
    rw [hre]
    exact progressions b hb i (hre ▸ hrb)
  have hσ := fastSigmaSq_spec 20 r hr0 (by exact hrb.trans (by decide)) hrb
  have hd := deficit_mul h
  have hpos := ArithmeticFunction.sigma_pos 1 (r^2) (pow_ne_zero 2 hr0.ne')
  have hd0 : 2*r^2-σ 1 (r^2) ≠ 0 := by
    intro he
    rw [he,zero_mul] at hd
    omega
  have hmod : σ 1 (r^2) % (2*r^2-σ 1 (r^2)) = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨w,hd.symm⟩
  have hroots : r = 1 ∨ r = 3003 := by
    simpa [passes,hσ,hd0,hmod] using hcheck
  rcases hroots with rfl | rfl
  · have hw1 : w = 1 := by simpa using hd
    exact (Nat.ne_of_gt h.1.1) hw1
  · have hs : σ 1 (3003^2) = 18035199 := by
      rw [← fastSigmaSq_spec 20 3003 (by decide) (by decide) (by decide)]
      decide +kernel
    rw [hs] at hd
    norm_num at hd
    have hw : w = 22021 := by omega
    apply hne
    rw [hw]
    decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_0 : check (fun i => passes (15*(2*i+1))) 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_1 : check (fun i => passes (15*(2*i+1))) 1024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_2 : check (fun i => passes (15*(2*i+1))) 2048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_3 : check (fun i => passes (15*(2*i+1))) 3072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_4 : check (fun i => passes (15*(2*i+1))) 4096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_5 : check (fun i => passes (15*(2*i+1))) 5120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_6 : check (fun i => passes (15*(2*i+1))) 6144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_7 : check (fun i => passes (15*(2*i+1))) 7168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_8 : check (fun i => passes (15*(2*i+1))) 8192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_9 : check (fun i => passes (15*(2*i+1))) 9216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_10 : check (fun i => passes (15*(2*i+1))) 10240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_11 : check (fun i => passes (15*(2*i+1))) 11264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_12 : check (fun i => passes (15*(2*i+1))) 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_13 : check (fun i => passes (15*(2*i+1))) 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_14 : check (fun i => passes (15*(2*i+1))) 14336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_15 : check (fun i => passes (15*(2*i+1))) 15360 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_16 : check (fun i => passes (15*(2*i+1))) 16384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_17 : check (fun i => passes (15*(2*i+1))) 17408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_18 : check (fun i => passes (15*(2*i+1))) 18432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_19 : check (fun i => passes (15*(2*i+1))) 19456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_20 : check (fun i => passes (15*(2*i+1))) 20480 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_21 : check (fun i => passes (15*(2*i+1))) 21504 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_22 : check (fun i => passes (15*(2*i+1))) 22528 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_23 : check (fun i => passes (15*(2*i+1))) 23552 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_24 : check (fun i => passes (15*(2*i+1))) 24576 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_25 : check (fun i => passes (15*(2*i+1))) 25600 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_26 : check (fun i => passes (15*(2*i+1))) 26624 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_27 : check (fun i => passes (15*(2*i+1))) 27648 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_28 : check (fun i => passes (15*(2*i+1))) 28672 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_29 : check (fun i => passes (15*(2*i+1))) 29696 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_30 : check (fun i => passes (15*(2*i+1))) 30720 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_31 : check (fun i => passes (15*(2*i+1))) 31744 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block15_32 : check (fun i => passes (15*(2*i+1))) 32768 565 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_0 : check (fun i => passes (21*(2*i+1))) 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_1 : check (fun i => passes (21*(2*i+1))) 1024 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_2 : check (fun i => passes (21*(2*i+1))) 2048 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_3 : check (fun i => passes (21*(2*i+1))) 3072 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_4 : check (fun i => passes (21*(2*i+1))) 4096 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_5 : check (fun i => passes (21*(2*i+1))) 5120 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_6 : check (fun i => passes (21*(2*i+1))) 6144 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_7 : check (fun i => passes (21*(2*i+1))) 7168 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_8 : check (fun i => passes (21*(2*i+1))) 8192 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_9 : check (fun i => passes (21*(2*i+1))) 9216 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_10 : check (fun i => passes (21*(2*i+1))) 10240 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_11 : check (fun i => passes (21*(2*i+1))) 11264 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_12 : check (fun i => passes (21*(2*i+1))) 12288 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_13 : check (fun i => passes (21*(2*i+1))) 13312 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_14 : check (fun i => passes (21*(2*i+1))) 14336 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_15 : check (fun i => passes (21*(2*i+1))) 15360 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_16 : check (fun i => passes (21*(2*i+1))) 16384 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_17 : check (fun i => passes (21*(2*i+1))) 17408 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_18 : check (fun i => passes (21*(2*i+1))) 18432 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_19 : check (fun i => passes (21*(2*i+1))) 19456 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_20 : check (fun i => passes (21*(2*i+1))) 20480 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_21 : check (fun i => passes (21*(2*i+1))) 21504 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_22 : check (fun i => passes (21*(2*i+1))) 22528 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block21_23 : check (fun i => passes (21*(2*i+1))) 23552 258 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block429_0 : check (fun i => passes (429*(2*i+1))) 0 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block429_1 : check (fun i => passes (429*(2*i+1))) 1024 142 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block561_0 : check (fun i => passes (561*(2*i+1))) 0 891 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block663_0 : check (fun i => passes (663*(2*i+1))) 0 754 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block85085_0 : check (fun i => passes (85085*(2*i+1))) 0 6 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block627_0 : check (fun i => passes (627*(2*i+1))) 0 797 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block741_0 : check (fun i => passes (741*(2*i+1))) 0 675 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block95095_0 : check (fun i => passes (95095*(2*i+1))) 0 5 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block759_0 : check (fun i => passes (759*(2*i+1))) 0 659 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block897_0 : check (fun i => passes (897*(2*i+1))) 0 557 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block115115_0 : check (fun i => passes (115115*(2*i+1))) 0 4 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block22287_0 : check (fun i => passes (22287*(2*i+1))) 0 22 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block957_0 : check (fun i => passes (957*(2*i+1))) 0 522 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem block871131_0 : check (fun i => passes (871131*(2*i+1))) 0 1 = true := by
  decide +kernel


private theorem passesBase15 (i : ℕ) (hi : i < 33333) : passes (15*(2*i+1)) = true := by
  by_cases h0 : i < 1024
  · exact check_sound _ _ _ block15_0 (by omega) h0
  by_cases h1 : i < 2048
  · exact check_sound _ _ _ block15_1 (by omega) h1
  by_cases h2 : i < 3072
  · exact check_sound _ _ _ block15_2 (by omega) h2
  by_cases h3 : i < 4096
  · exact check_sound _ _ _ block15_3 (by omega) h3
  by_cases h4 : i < 5120
  · exact check_sound _ _ _ block15_4 (by omega) h4
  by_cases h5 : i < 6144
  · exact check_sound _ _ _ block15_5 (by omega) h5
  by_cases h6 : i < 7168
  · exact check_sound _ _ _ block15_6 (by omega) h6
  by_cases h7 : i < 8192
  · exact check_sound _ _ _ block15_7 (by omega) h7
  by_cases h8 : i < 9216
  · exact check_sound _ _ _ block15_8 (by omega) h8
  by_cases h9 : i < 10240
  · exact check_sound _ _ _ block15_9 (by omega) h9
  by_cases h10 : i < 11264
  · exact check_sound _ _ _ block15_10 (by omega) h10
  by_cases h11 : i < 12288
  · exact check_sound _ _ _ block15_11 (by omega) h11
  by_cases h12 : i < 13312
  · exact check_sound _ _ _ block15_12 (by omega) h12
  by_cases h13 : i < 14336
  · exact check_sound _ _ _ block15_13 (by omega) h13
  by_cases h14 : i < 15360
  · exact check_sound _ _ _ block15_14 (by omega) h14
  by_cases h15 : i < 16384
  · exact check_sound _ _ _ block15_15 (by omega) h15
  by_cases h16 : i < 17408
  · exact check_sound _ _ _ block15_16 (by omega) h16
  by_cases h17 : i < 18432
  · exact check_sound _ _ _ block15_17 (by omega) h17
  by_cases h18 : i < 19456
  · exact check_sound _ _ _ block15_18 (by omega) h18
  by_cases h19 : i < 20480
  · exact check_sound _ _ _ block15_19 (by omega) h19
  by_cases h20 : i < 21504
  · exact check_sound _ _ _ block15_20 (by omega) h20
  by_cases h21 : i < 22528
  · exact check_sound _ _ _ block15_21 (by omega) h21
  by_cases h22 : i < 23552
  · exact check_sound _ _ _ block15_22 (by omega) h22
  by_cases h23 : i < 24576
  · exact check_sound _ _ _ block15_23 (by omega) h23
  by_cases h24 : i < 25600
  · exact check_sound _ _ _ block15_24 (by omega) h24
  by_cases h25 : i < 26624
  · exact check_sound _ _ _ block15_25 (by omega) h25
  by_cases h26 : i < 27648
  · exact check_sound _ _ _ block15_26 (by omega) h26
  by_cases h27 : i < 28672
  · exact check_sound _ _ _ block15_27 (by omega) h27
  by_cases h28 : i < 29696
  · exact check_sound _ _ _ block15_28 (by omega) h28
  by_cases h29 : i < 30720
  · exact check_sound _ _ _ block15_29 (by omega) h29
  by_cases h30 : i < 31744
  · exact check_sound _ _ _ block15_30 (by omega) h30
  by_cases h31 : i < 32768
  · exact check_sound _ _ _ block15_31 (by omega) h31
  exact check_sound _ _ _ block15_32 (by omega) (by omega)

private theorem passesBase21 (i : ℕ) (hi : i < 23810) : passes (21*(2*i+1)) = true := by
  by_cases h0 : i < 1024
  · exact check_sound _ _ _ block21_0 (by omega) h0
  by_cases h1 : i < 2048
  · exact check_sound _ _ _ block21_1 (by omega) h1
  by_cases h2 : i < 3072
  · exact check_sound _ _ _ block21_2 (by omega) h2
  by_cases h3 : i < 4096
  · exact check_sound _ _ _ block21_3 (by omega) h3
  by_cases h4 : i < 5120
  · exact check_sound _ _ _ block21_4 (by omega) h4
  by_cases h5 : i < 6144
  · exact check_sound _ _ _ block21_5 (by omega) h5
  by_cases h6 : i < 7168
  · exact check_sound _ _ _ block21_6 (by omega) h6
  by_cases h7 : i < 8192
  · exact check_sound _ _ _ block21_7 (by omega) h7
  by_cases h8 : i < 9216
  · exact check_sound _ _ _ block21_8 (by omega) h8
  by_cases h9 : i < 10240
  · exact check_sound _ _ _ block21_9 (by omega) h9
  by_cases h10 : i < 11264
  · exact check_sound _ _ _ block21_10 (by omega) h10
  by_cases h11 : i < 12288
  · exact check_sound _ _ _ block21_11 (by omega) h11
  by_cases h12 : i < 13312
  · exact check_sound _ _ _ block21_12 (by omega) h12
  by_cases h13 : i < 14336
  · exact check_sound _ _ _ block21_13 (by omega) h13
  by_cases h14 : i < 15360
  · exact check_sound _ _ _ block21_14 (by omega) h14
  by_cases h15 : i < 16384
  · exact check_sound _ _ _ block21_15 (by omega) h15
  by_cases h16 : i < 17408
  · exact check_sound _ _ _ block21_16 (by omega) h16
  by_cases h17 : i < 18432
  · exact check_sound _ _ _ block21_17 (by omega) h17
  by_cases h18 : i < 19456
  · exact check_sound _ _ _ block21_18 (by omega) h18
  by_cases h19 : i < 20480
  · exact check_sound _ _ _ block21_19 (by omega) h19
  by_cases h20 : i < 21504
  · exact check_sound _ _ _ block21_20 (by omega) h20
  by_cases h21 : i < 22528
  · exact check_sound _ _ _ block21_21 (by omega) h21
  by_cases h22 : i < 23552
  · exact check_sound _ _ _ block21_22 (by omega) h22
  exact check_sound _ _ _ block21_23 (by omega) (by omega)

private theorem passesBase429 (i : ℕ) (hi : i < 1166) : passes (429*(2*i+1)) = true := by
  by_cases h0 : i < 1024
  · exact check_sound _ _ _ block429_0 (by omega) h0
  exact check_sound _ _ _ block429_1 (by omega) (by omega)

private theorem passesBase561 (i : ℕ) (hi : i < 891) : passes (561*(2*i+1)) = true := by
  exact check_sound _ _ _ block561_0 (by omega) (by omega)

private theorem passesBase663 (i : ℕ) (hi : i < 754) : passes (663*(2*i+1)) = true := by
  exact check_sound _ _ _ block663_0 (by omega) (by omega)

private theorem passesBase85085 (i : ℕ) (hi : i < 6) : passes (85085*(2*i+1)) = true := by
  exact check_sound _ _ _ block85085_0 (by omega) (by omega)

private theorem passesBase627 (i : ℕ) (hi : i < 797) : passes (627*(2*i+1)) = true := by
  exact check_sound _ _ _ block627_0 (by omega) (by omega)

private theorem passesBase741 (i : ℕ) (hi : i < 675) : passes (741*(2*i+1)) = true := by
  exact check_sound _ _ _ block741_0 (by omega) (by omega)

private theorem passesBase95095 (i : ℕ) (hi : i < 5) : passes (95095*(2*i+1)) = true := by
  exact check_sound _ _ _ block95095_0 (by omega) (by omega)

private theorem passesBase759 (i : ℕ) (hi : i < 659) : passes (759*(2*i+1)) = true := by
  exact check_sound _ _ _ block759_0 (by omega) (by omega)

private theorem passesBase897 (i : ℕ) (hi : i < 557) : passes (897*(2*i+1)) = true := by
  exact check_sound _ _ _ block897_0 (by omega) (by omega)

private theorem passesBase115115 (i : ℕ) (hi : i < 4) : passes (115115*(2*i+1)) = true := by
  exact check_sound _ _ _ block115115_0 (by omega) (by omega)

private theorem passesBase22287 (i : ℕ) (hi : i < 22) : passes (22287*(2*i+1)) = true := by
  exact check_sound _ _ _ block22287_0 (by omega) (by omega)

private theorem passesBase957 (i : ℕ) (hi : i < 522) : passes (957*(2*i+1)) = true := by
  exact check_sound _ _ _ block957_0 (by omega) (by omega)

private theorem passesBase871131 (i : ℕ) (hi : i < 1) : passes (871131*(2*i+1)) = true := by
  exact check_sound _ _ _ block871131_0 (by omega) (by omega)

private theorem progression_check (b : ℕ) (hb : b ∈ searchBases) (i : ℕ)
    (hi : b*(2*i+1) ≤ 1000000) : passes (b*(2*i+1)) = true := by
  simp only [searchBases,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact passesBase15 i (by omega)
  · exact passesBase21 i (by omega)
  · exact passesBase429 i (by omega)
  · exact passesBase561 i (by omega)
  · exact passesBase663 i (by omega)
  · exact passesBase85085 i (by omega)
  · exact passesBase627 i (by omega)
  · exact passesBase741 i (by omega)
  · exact passesBase95095 i (by omega)
  · exact passesBase759 i (by omega)
  · exact passesBase897 i (by omega)
  · exact passesBase115115 i (by omega)
  · exact passesBase22287 i (by omega)
  · exact passesBase957 i (by omega)
  · exact passesBase871131 i (by omega)

end OMA.DescartesSearch

theorem OMA.solution : type_of% @DescartesNumber.descartes_non_example_factor_gt_ten_pow_twelve :=
  OMA.DescartesSearch.lower_of_checked OMA.DescartesSearch.progression_check