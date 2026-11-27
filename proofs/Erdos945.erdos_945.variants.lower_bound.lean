import FormalConjectures.ErdosProblems.«945»

/-!
# Distinct divisor counts on consecutive integers

We use the prime markers of Erdős and Mirsky, *The distribution of values of the
divisor function d(n)* (1952), §11. For each position we choose a distinct prime
`p` and prescribe valuation `p - 1` there using the Chinese remainder theorem.
After removing translates with any other large valuation, the divisor count at
each position is divisible by its own marker alone among the chosen primes.
Chebyshev's bounds control the number of available markers and the CRT modulus.
-/

open Finset Filter Real
open scoped BigOperators Function
namespace E945
private lemma ap_card (b B d T : ℕ) (hc : d.Coprime B) :
    ((range T).filter fun t => d ∣ B*t+b).card ≤ T/d+1 := by
  have h := Finset.card_le_card_of_injOn (s := (range T).filter fun t => d ∣ B*t+b)
      (t := range (T/d+1)) (fun t => t/d) (by
        intro t ht
        have ht' := mem_range.mp (mem_filter.mp ht).1
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt ht')))) (by
        intro u hu v hv he
        have hm := (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hu).2).trans
          (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hv).2).symm
        have hr : u % d = v % d := Nat.ModEq.cancel_left_of_coprime hc
          (Nat.ModEq.add_right_cancel' b hm)
        change u/d = v/d at he
        have h1 := Nat.div_add_mod u d
        have h2 := Nat.div_add_mod v d
        rw [he, hr] at h1
        omega)
  simpa using h

private lemma factor_bound {k : ℕ} (hk : 8 ≤ k) : 4*k ≤ 2^(k-2) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [show n+1-2 = (n-2)+1 by omega, pow_succ]
    omega

/-- Among the first cubic-many translates, one avoids all large prime powers coprime to the modulus. -/
private lemma choose_t {k b B : ℕ} (hk : 8 ≤ k) (hB : k ≤ B) :
    ∃ t < B^3, ∀ i < k, ∀ q ∈ Ioc 1 B, q.Coprime B →
      ¬q^k ∣ B*t + (b+i+1) := by
  classical
  let T := B^3
  let Q := (Ioc 1 B).filter (fun q => q.Coprime B)
  let bad (i q : ℕ) := (range T).filter fun t => q^k ∣ B*t+(b+i+1)
  let badI i := Q.biUnion (bad i)
  let allBad := (range k).biUnion badI
  have hT : (0:ℝ) < T := by exact_mod_cast (show 0 < B^3 from pow_pos (by omega) _)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum (i : ℕ) : ((badI i).card : ℝ) ≤ (T:ℝ)/(4*k) + B := by
    have hd (q : ℕ) (hq : q ∈ Q) : ((bad i q).card : ℝ) ≤
        (T:ℝ)/(4*k) * ((q:ℝ)^2)⁻¹ + 1 := by
      obtain ⟨hm,hc⟩ := mem_filter.mp hq
      have hq2 := (mem_Ioc.mp hm).1
      have hpow : 4*k*q^2 ≤ q^k := by
        calc
          _ ≤ 2^(k-2)*q^2 := Nat.mul_le_mul_right _ (factor_bound hk)
          _ ≤ q^(k-2)*q^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
          _ = _ := by rw [← pow_add]; congr 1; omega
      have hraw : (bad i q).card ≤ T/(q^k)+1 := ap_card _ _ _ _ (hc.pow_left _)
      calc
        _ ≤ ((T/(q^k)+1 : ℕ):ℝ) := by exact_mod_cast hraw
        _ ≤ (T:ℝ)/(q:ℝ)^k + 1 := by
          push_cast
          gcongr
          exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := T) (n := q^k))
        _ ≤ _ := by
          rw [← div_eq_mul_inv, div_div]
          gcongr
          exact_mod_cast hpow
    calc
      _ ≤ ∑ q ∈ Q, ((bad i q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Q, ((T:ℝ)/(4*k) * ((q:ℝ)^2)⁻¹ + 1) := sum_le_sum (fun q hq => hd q hq)
      _ ≤ ∑ q ∈ Ioc 1 B, ((T:ℝ)/(4*k) * ((q:ℝ)^2)⁻¹ + 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ ≤ _ := by
        rw [sum_add_distrib, ← mul_sum]
        have hrec := sum_Ioc_inv_sq_le_sub (α := ℝ) (n := B) (k := 1) (by decide) (by omega)
        have hh : (∑ i ∈ Ioc 1 B, ((i:ℝ)^2)⁻¹) ≤ 1 := by
          simp only [Nat.cast_one,inv_one] at hrec
          linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) B)]
        simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_left hh (show 0 ≤ (T:ℝ)/(4*k) by positivity)
        · exact_mod_cast Nat.sub_le B 1
  have hbad : (allBad.card : ℝ) ≤ (k:ℝ)*((T:ℝ)/(4*k)+B) := by
    calc
      _ ≤ ∑ i ∈ range k, ((badI i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ range k, ((T:ℝ)/(4*k)+B) := sum_le_sum (by intros; apply hsum)
      _ = _ := by simp [mul_add]
  have hsmall : allBad.card < T := by
    have hkB : (k:ℝ) ≤ B := by exact_mod_cast hB
    have hB8 : (8:ℝ) ≤ B := by exact_mod_cast hk.trans hB
    have hT' : (T:ℝ)=(B:ℝ)^3 := by simp [T]
    have h1 : (k:ℝ)*((T:ℝ)/(4*k)) = (T:ℝ)/4 := by field_simp
    rw [mul_add, h1,hT'] at hbad
    have hs : (0:ℝ) ≤ (B:ℝ)^2 * (B-8) := by positivity
    exact_mod_cast (show (allBad.card:ℝ) < (T:ℝ) by rw [hT']; nlinarith [mul_le_mul_of_nonneg_right hkB (Nat.cast_nonneg (α:=ℝ) B)])
  obtain ⟨t,ht,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := range T) (s := allBad)
    (by simpa using hsmall)
  refine ⟨t,mem_range.mp ht,?_⟩
  intro i hi q hq hc hdiv
  exact hout (mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_biUnion.mpr
    ⟨q,mem_filter.mpr ⟨hq,hc⟩,mem_filter.mpr ⟨ht,hdiv⟩⟩⟩)
private def modulus {k : ℕ} (p : Fin k → ℕ) : ℕ := ∏ i, p i ^ p i

/-- Give each position its own prime divisor of its divisor count. -/
private lemma distinct_run {k : ℕ} (hk : 8 ≤ k) (p : Fin k → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, (p i).Prime) (hlarge : ∀ i, k+1 < p i) :
    ∃ n : ℕ, n+k ≤ (modulus p)^5 ∧ (Set.Ioc n (n+k)).InjOn Erdos945.τ := by
  classical
  let B := modulus p
  let D (i : Fin k) := p i ^ p i
  let V (i : Fin k) := p i ^ (p i - 1)
  have hD (i) : D i ∣ B := Finset.dvd_prod_of_mem D (mem_univ i)
  have hV (i) : p i ∣ V i := dvd_pow_self _ (by have := (hp i).two_le; omega)
  have hVD (i) : V i ∣ D i := pow_dvd_pow _ (Nat.sub_le _ _)
  have hVp (i) : p i ≤ V i := Nat.le_of_dvd (pow_pos (hp i).pos _) (hV i)
  let i0 : Fin k := ⟨0, by omega⟩
  have hB0 : 0 < B := Finset.prod_pos (fun i _ => pow_pos (hp i).pos _)
  have hB : k ≤ B := (hlarge i0).le.trans' (by omega) |>.trans <|
    Nat.le_of_dvd hB0 ((hV i0).trans ((hVD i0).trans (hD i0)))
  let a (i : Fin k) := V i - (i.val+1)
  have hne : ∀ i ∈ (univ : Finset (Fin k)), D i ≠ 0 := fun i _ => pow_ne_zero _ (hp i).ne_zero
  have hco : Set.Pairwise (univ : Finset (Fin k)) (Nat.Coprime on D) := by
    intro i _ j _ hij
    exact (((hp i).coprime_iff_not_dvd.mpr (fun hh => hij <| hinj <|
      (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hh)).pow_left _).pow_right _
  let crt := Nat.chineseRemainderOfFinset a D univ hne hco
  let b := crt.val
  have hb : b < B := Nat.chineseRemainderOfFinset_lt_prod a D hne hco
  obtain ⟨t,ht,havoid⟩ := choose_t (b := b) hk hB
  let n := B*t + b
  let z (i : Fin k) := n+(i.val+1)
  have hz (i) : z i ≠ 0 := by simp [z]
  have hcon (i) : z i ≡ V i [MOD D i] := by
    have hbt : B*t ≡ 0 [MOD D i] := Nat.modEq_zero_iff_dvd.mpr
      ((hD i).trans (dvd_mul_right B t))
    have h := ((hbt.add (crt.property i (mem_univ _))).add_right (i.val+1))
    simpa only [zero_add, a, Nat.sub_add_cancel (show i.val+1 ≤ V i by
      have := hlarge i; have := hVp i; omega)] using h
  have hfact (i) : (z i).factorization (p i) + 1 = p i := by
    have hlo := ((hp i).pow_dvd_iff_le_factorization (hz i)).mp <|
      ((hcon i).dvd_iff (hVD i)).mpr dvd_rfl
    have hhi : ¬ D i ∣ z i := by
      rw [(hcon i).dvd_iff dvd_rfl]
      exact Nat.not_dvd_of_pos_of_lt (pow_pos (hp i).pos _)
        (pow_lt_pow_right₀ (hp i).one_lt (by have := (hp i).two_le; omega))
    change ¬ (p i)^(p i) ∣ z i at hhi
    rw [(hp i).pow_dvd_iff_le_factorization (hz i)] at hhi
    omega
  have hdpi (i) : p i ∣ z i := ((hcon i).dvd_iff ((hV i).trans (hVD i))).mpr (hV i)
  have hnle : n+k ≤ B^5 := by
    have h4 : B ≤ B^4 := Nat.le_self_pow (by decide) _
    have h3 : 3*B^4 ≤ B*B^4 := Nat.mul_le_mul_right _ (by omega)
    have hbt := Nat.mul_le_mul_left B ht.le
    dsimp [n]
    nlinarith
  have hs (i : Fin k) {q : ℕ} (hq : q.Prime) (hother : q ≠ p i)
      (hdq : q ∣ z i) : (z i).factorization q < k := by
    by_contra! h
    have hd := (hq.pow_dvd_iff_le_factorization (hz i)).mpr h
    have hc : q.Coprime B := by
      apply hq.coprime_iff_not_dvd.mpr
      intro he
      obtain ⟨j, _, hj⟩ := hq.prime.exists_mem_finset_dvd he
      have heq : q = p j := (Nat.prime_dvd_prime_iff_eq hq (hp j)).mp (hq.dvd_of_dvd_pow hj)
      have hm := (Nat.modEq_zero_iff_dvd.mpr hdq).trans
        (Nat.modEq_zero_iff_dvd.mpr (heq ▸ hdpi j)).symm
      have hmm := Nat.ModEq.add_left_cancel' n hm
      have hqi := hlarge j
      have heij : i = j := Fin.ext <| by have := hmm.eq_of_lt_of_lt (by omega) (by omega); omega
      exact hother (heij ▸ heq)
    have hqB : q ≤ B := by
      have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hz i)) hd
      have h2 : z i ≤ B^5 := (Nat.add_le_add_left (show i.val+1 ≤ k by omega) n).trans hnle
      by_contra! hh
      have h3 : B^5 < q^5 := Nat.pow_lt_pow_left hh (by decide)
      have h4 : q^5 ≤ q^k := Nat.pow_le_pow_right hq.pos (by omega)
      omega
    exact havoid i i.isLt q (mem_Ioc.mpr ⟨hq.one_lt,hqB⟩) hc (by simpa [z,n,Nat.add_assoc] using hd)
  have hmark (i j : Fin k) : p j ∣ Erdos945.τ (z i) ↔ j = i := by
    rw [Erdos945.τ,Nat.card_divisors (hz i)]
    constructor
    · intro hd
      obtain ⟨q,hq,hval⟩ := (hp j).prime.exists_mem_finset_dvd hd
      by_cases he : q = p i
      · rw [he,hfact] at hval
        exact hinj ((Nat.prime_dvd_prime_iff_eq (hp j) (hp i)).mp hval)
      · obtain ⟨hqp,hdq,_⟩ := Nat.mem_primeFactors.mp hq
        have hh := hs i hqp he hdq
        have hl := Nat.le_of_dvd (Nat.succ_pos _) hval
        have := hlarge j
        omega
    · intro hij
      subst j
      have hmem := Nat.mem_primeFactors.mpr ⟨hp i,hdpi i,hz i⟩
      simpa only [hfact] using Finset.dvd_prod_of_mem (fun q => (z i).factorization q + 1) hmem
  refine ⟨n,hnle,?_⟩
  intro x hx y hy hxy
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  let i : Fin k := ⟨x-n-1, by omega⟩
  let j : Fin k := ⟨y-n-1, by omega⟩
  have hxi : x = z i := by dsimp [z,i]; omega
  have hyj : y = z j := by dsimp [z,j]; omega
  rw [hxi,hyj] at hxy
  have hi := (hmark i i).mpr rfl
  rw [hxy] at hi
  rw [hxi,hyj,(hmark j i).mp hi]

private lemma run_length (Q : ℕ) (hπ : 32 ≤ Q.primeCounting) :
    ∃ n : ℕ, let k := Q.primeCounting/4
             log (n+k : ℕ) ≤ 5 * log 4 * (Q:ℝ)^2 ∧
             (Set.Ioc n (n+k)).InjOn Erdos945.τ := by
  classical
  let k := Q.primeCounting/4
  have hk : 8 ≤ k := by dsimp [k]; omega
  let S := Q.primesLE \ range (k+2)
  have hS : k ≤ S.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := Q.primesLE) (t := range (k+2))
    rw [Nat.primesLE_card_eq_primeCounting,card_range] at h
    dsimp [S,k] at *
    omega
  obtain ⟨p,hp⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin k) (s := S) (by simpa using hS)
  have hm (i : Fin k) : p i ∈ S := hp ⟨i,rfl⟩
  have hprime (i) := (Nat.mem_primesLE.mp (mem_sdiff.mp (hm i)).1).2
  have hle (i) := (Nat.mem_primesLE.mp (mem_sdiff.mp (hm i)).1).1
  have hlarge (i) : k+1 < p i := by
    have h := (mem_sdiff.mp (hm i)).2
    simp only [mem_range, not_lt] at h
    omega
  obtain ⟨n,hn,hinj⟩ := distinct_run hk p p.injective hprime hlarge
  have hlogB : log (modulus p : ℝ) ≤ (Q:ℝ)*(log 4 * Q) := by
    simp only [modulus, Nat.cast_prod, Nat.cast_pow, Real.log_prod
      (fun i (_ : i ∈ (univ : Finset (Fin k))) => pow_ne_zero (p i) (by exact_mod_cast (hprime i).ne_zero : (p i:ℝ) ≠ 0)),
      Real.log_pow]
    calc
      _ ≤ ∑ i, (Q:ℝ)*log (p i) := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hle i) (Real.log_nonneg (by exact_mod_cast (hprime i).one_le)))
      _ = (Q:ℝ) * ∑ q ∈ univ.image p, log q := by rw [Finset.mul_sum, Finset.sum_image p.injective.injOn]
      _ ≤ (Q:ℝ) * ∑ q ∈ Q.primesLE, log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨i,_,rfl⟩ := mem_image.mp hq
          exact (mem_sdiff.mp (hm i)).1
        · intro q hq _
          exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_le)
      _ ≤ _ := by rw [← Chebyshev.theta_eq_sum_primesLE_log]; gcongr; exact Chebyshev.theta_le_log4_mul_x (by positivity)
  refine ⟨n, ?_, hinj⟩
  change log ((n+k:ℕ):ℝ) ≤ _
  calc
    _ ≤ log ((modulus p : ℝ)^5) := Real.log_le_log (by exact_mod_cast (show 0<n+k by omega)) (by exact_mod_cast hn)
    _ ≤ _ := by rw [Real.log_pow]; norm_num; nlinarith

end E945

open E945 Erdos945 in
theorem OMA.solution : type_of% @Erdos945.erdos_945.variants.lower_bound := by
  let Q (x : ℕ) := ⌊√(log x)/10⌋₊
  have hlog : Tendsto (fun x : ℕ => log x) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQ : Tendsto Q atTop atTop := tendsto_nat_floor_atTop.comp <|
    (Real.tendsto_sqrt_atTop.comp hlog).atTop_div_const (by norm_num : (0:ℝ)<10)
  have hlittle := Real.isLittleO_log_id_atTop.bound (show 0 < (1/8:ℝ) by norm_num)
  have hQ1 : Tendsto (fun x => (Q x:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun x => le_add_of_nonneg_right zero_le_one) (tendsto_natCast_atTop_atTop.comp hQ)
  apply Asymptotics.IsBigO.of_bound 640
  filter_upwards [((Nat.tendsto_primeCounting.comp hQ).eventually_ge_atTop 32),
    hQ.eventually_ge_atTop 2, hlog.eventually_ge_atTop 4, hQ1.eventually hlittle] with x hπ h2 hl hh
  let q := Q x
  let k := q.primeCounting / 4
  change 32 ≤ q.primeCounting at hπ
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast h2
  have hq0 : (0:ℝ) < q := by linarith
  have hlogq : 0 < log q := Real.log_pos (by linarith)
  change ‖log ((q:ℝ)+1)‖ ≤ 1/8 * ‖(q:ℝ)+1‖ at hh
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith : (1:ℝ)≤q+1)),
    abs_of_nonneg (by linarith : (0:ℝ)≤q+1)] at hh
  have hπq := (div_le_iff₀ hlogq).mp (Chebyshev.pi_ge q)
  have hquarter : (q:ℝ)/4 ≤ (q.primeCounting:ℝ)*log q := by
    nlinarith [mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ log 2 by linarith [Real.log_two_gt_d9]) hq0.le]
  have hk : q.primeCounting ≤ 8*k := by dsimp [k]; omega
  have hqfl : (q:ℝ) ≤ √(log x)/10 := Nat.floor_le (by positivity)
  have hqfl' : √(log x)/10 < (q:ℝ)+1 := Nat.lt_floor_add_one _
  have hs := Real.sq_sqrt (show 0 ≤ log x by linarith)
  have hs0 := Real.sqrt_nonneg (log x)
  have hqsize : (q:ℝ) ≤ log x := by nlinarith
  have hqlog := Real.log_le_log hq0 hqsize
  obtain ⟨n, hn, hi⟩ := E945.run_length q hπ
  change log ((n+k:ℕ):ℝ) ≤ _ at hn
  have hlog4 : log 4 ≤ 2 := by
    have h := Real.log_pow (2:ℝ) 2
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hfits : n+k ≤ x := by
    have hnx : log ((n+k:ℕ):ℝ) ≤ log x := by
      nlinarith [mul_le_mul_of_nonneg_right hlog4 (sq_nonneg (q:ℝ)), sq_nonneg (√(log x)-10*q),
        mul_nonneg (show 0 ≤ √(log x)-10*q by linarith) (show 0 ≤ √(log x)+10*q by positivity)]
    exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast (show 0 < n+k by dsimp [k]; omega))
      (show (0:ℝ)<x by
        by_contra! hh
        have hx : x=0 := by exact_mod_cast (le_antisymm hh (Nat.cast_nonneg _))
        norm_num [hx] at hl)).mp hnx
  have hkF : k ≤ F x := by
    apply le_csSup (s := {j : ℕ | ∃ n : ℕ, (n:ℝ)+j ≤ (x:ℝ) ∧ (Set.Ioc n (n+j)).InjOn τ})
    · use x
      rintro j ⟨u,hu,_⟩
      have : u+j ≤ x := by exact_mod_cast hu
      omega
    · exact ⟨n,by exact_mod_cast hfits,hi⟩
  have hkq : (q.primeCounting:ℝ)*log q ≤ (8*k : ℝ)*log (log x) := by
    apply mul_le_mul (by exact_mod_cast hk) hqlog hlogq.le (by positivity)
  have hlpos : 0 < log (log x) := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hs0 hlpos.le), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (F x))]
  apply (div_le_iff₀ hlpos).2
  have hlast := mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ F x by exact_mod_cast hkF) hlpos.le
  nlinarith

