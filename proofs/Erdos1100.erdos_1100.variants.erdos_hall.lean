import FormalConjectures.ErdosProblems.«1100»

/-!
# Consecutive divisors supported on a narrow window of primes

The divisor-block argument is from Erdős and Hall (1978), section 3,
https://www.renyi.hu/~p_erdos/1978-26.pdf. The prime window uses a wider
interval so that Chebyshev estimates suffice for the asymptotic argument.
-/

namespace OMA.Erdos1100

open Finset

private theorem block_bound (P : Finset ℕ) (L R k : ℕ)
    (hL : 0 < L)
    (hP : ∀ p ∈ P, p.Prime ∧ L ≤ p ∧ p ≤ R)
    (hsmall : ∀ j < k, R ^ j < L ^ k)
    (hlarge : R ^ k < L ^ (k + 1)) :
    P.card.choose k ≤ Erdos1100.tauPerp (∏ p ∈ P, p) + R ^ k / L + 2 := by
  classical
  let n := ∏ p ∈ P, p
  change P.card.choose k ≤ Erdos1100.tauPerp n + R ^ k / L + 2
  have hp {p : ℕ} (h : p ∈ P) : p.Prime := (hP p h).1
  have hprime : n.primeFactors = P := Nat.primeFactors_prod fun _ h => hp h
  have hsf : Squarefree n := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpm q hqm hne
      exact Nat.coprime_iff_isRelPrime.mp <| (hp hpm).coprime_iff_not_dvd.mpr <| fun h =>
        hne (((hp hqm).eq_one_or_self_of_dvd p h).resolve_left (hp hpm).ne_one)
    · exact fun p h => (hp h).squarefree
  have hn : 0 < n := Nat.pos_of_ne_zero hsf.ne_zero
  have hfinite : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hfinset : hfinite.toFinset = n.divisors := by
    ext d
    simp [hn.ne']
  let f := Nat.nth (· ∣ n)
  let d := n.divisors.card
  have hfmem {i : ℕ} (hi : i < d) : f i ∣ n := by
    apply Nat.nth_mem_of_lt_card hfinite
    simpa [hfinset] using hi
  have hflt {i j : ℕ} (hij : i < j) (hj : j < d) : f i < f j := by
    apply Nat.nth_lt_nth_of_lt_card hfinite hij
    simpa [hfinset] using hj
  have hfle {i j : ℕ} (hij : i ≤ j) (hj : j < d) : f i ≤ f j := by
    apply Nat.nth_le_nth_of_lt_card hfinite hij
    simpa [hfinset] using hj
  let I := (range d).filter fun i => L ^ k ≤ f i ∧ f i ≤ R ^ k
  let C := (P.powersetCard k).image fun S => ∏ p ∈ S, p
  have prod_bounds (S : Finset ℕ) (hS : S ⊆ P) :
      L ^ S.card ≤ (∏ p ∈ S, p) ∧ (∏ p ∈ S, p) ≤ R ^ S.card := by
    simpa only [prod_const] using
      (show (∏ _ ∈ S, L) ≤ (∏ p ∈ S, p) ∧ (∏ p ∈ S, p) ≤ (∏ _ ∈ S, R) from
        ⟨prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hP p (hS hp)).2.1),
          prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hP p (hS hp)).2.2)⟩)
  have hblock (a : ℕ) : a ∈ C ↔ a ∣ n ∧ L ^ k ≤ a ∧ a ≤ R ^ k := by
    constructor
    · intro ha
      obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hS
      have hbounds := prod_bounds S hsub
      rw [hcard] at hbounds
      exact ⟨prod_dvd_prod_of_subset _ _ _ hsub, hbounds⟩
    · rintro ⟨ha, hmin, hmax⟩
      have hsub : a.primeFactors ⊆ P := hprime ▸ Nat.primeFactors_mono ha hn.ne'
      have hprod : ∏ p ∈ a.primeFactors, p = a :=
        Nat.prod_primeFactors_of_squarefree (hsf.squarefree_of_dvd ha)
      have hb := prod_bounds a.primeFactors hsub
      rw [hprod] at hb
      have hcard : a.primeFactors.card = k := by
        apply le_antisymm
        · by_contra! hh
          have hh' := pow_le_pow_right₀ (show 1 ≤ L by omega)
            (show k + 1 ≤ a.primeFactors.card by omega)
          exact (not_lt_of_ge (hh'.trans (hb.1.trans hmax))) hlarge
        · by_contra! hh
          exact (not_lt_of_ge (hmin.trans hb.2)) (hsmall _ hh)
      exact mem_image.mpr ⟨a.primeFactors, mem_powersetCard.mpr ⟨hsub, hcard⟩, hprod⟩
  have hmap : I.image f = C := by
    ext a
    rw [hblock]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := mem_image.mp h
      obtain ⟨hir, hib⟩ := mem_filter.mp hi
      exact ⟨hfmem (mem_range.mp hir), hib⟩
    · rintro ⟨ha, hmin, hmax⟩
      have hindex : Nat.count (· ∣ n) a < d := by
        simpa [hfinset] using Nat.count_lt_card hfinite ha
      have hith : f (Nat.count (· ∣ n) a) = a := Nat.nth_count ha
      exact mem_image.mpr ⟨_, mem_filter.mpr ⟨mem_range.mpr hindex, by simpa only [hith] using And.intro hmin hmax⟩, hith⟩
  have hcardI : I.card = P.card.choose k := by
    have hinj : (I : Set ℕ).InjOn f := by
      apply (Nat.nth_injOn hfinite).mono
      intro i hi
      have hib := mem_range.mp ((mem_filter.mp (show i ∈ I from hi)).1)
      simpa [hfinset, Set.mem_Iio] using hib
    rw [← card_image_of_injOn hinj, hmap]
    rw [show C = (P.powersetCard k).image (fun S => ∏ p ∈ S, p) from rfl,
      card_image_of_injOn, card_powersetCard]
    intro S hS T hT he
    have hST (U : Finset ℕ) (hU : U ∈ P.powersetCard k) :
        (∏ p ∈ U, p).primeFactors = U :=
      Nat.primeFactors_prod fun p hp' => hp ((mem_powersetCard.mp hU).1 hp')
    change (∏ p ∈ S, p) = ∏ p ∈ T, p at he
    rw [← hST S hS, ← hST T hT, he]
  rcases I.eq_empty_or_nonempty with hI | hI
  · have hz : P.card.choose k = 0 := by rw [← hcardI, hI, card_empty]
    rw [hz]
    exact Nat.zero_le _
  let imax := I.max' hI
  have himax : imax ∈ I := I.max'_mem hI
  have himaxlt : imax < d := mem_range.mp ((mem_filter.mp himax).1)
  let J := I.erase imax
  let Good := J.filter fun i => Nat.Coprime (f i) (f (i + 1))
  let Bad := J.filter fun i => ¬Nat.Coprime (f i) (f (i + 1))
  have hJ {i : ℕ} (hi : i ∈ J) : i ∈ I ∧ i + 1 ∈ I ∧ i + 1 < d := by
    obtain ⟨hne, hiI⟩ := mem_erase.mp hi
    have hle : i ≤ imax := I.le_max' i hiI
    have hs : i + 1 ≤ imax := by omega
    have hslt := hs.trans_lt himaxlt
    have hiB := (mem_filter.mp hiI).2
    have hmB := (mem_filter.mp himax).2
    exact ⟨hiI, mem_filter.mpr ⟨mem_range.mpr hslt, hiB.1.trans (hfle (by omega) hslt),
      (hfle hs himaxlt).trans hmB.2⟩, hslt⟩
  have hgood : Good.card ≤ Erdos1100.tauPerp n := by
    let G := Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
      Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1))
    unfold Erdos1100.tauPerp
    change Good.card ≤ G.card
    rw [← card_image_of_injective G Fin.val_injective]
    apply card_le_card
    intro i hi
    obtain ⟨hij, hic⟩ := mem_filter.mp hi
    have hix : i < d - 1 := by have := (hJ hij).2.2; omega
    exact mem_image.mpr ⟨⟨i, hix⟩, mem_filter.mpr ⟨mem_univ _, hic⟩, rfl⟩
  have hgap {i : ℕ} (hi : i ∈ Bad) : f i + L ≤ f (i + 1) := by
    obtain ⟨hij, hic⟩ := mem_filter.mp hi
    obtain ⟨_, hi', hi''⟩ := hJ hij
    have hn1 : Nat.gcd (f i) (f (i + 1)) ≠ 1 :=
      fun h => hic (Nat.coprime_iff_gcd_eq_one.mpr h)
    obtain ⟨q, hqp, hqg⟩ := Nat.exists_prime_and_dvd hn1
    have hq1 := hqg.trans (Nat.gcd_dvd_left (f i) (f (i + 1)))
    have hq2 := hqg.trans (Nat.gcd_dvd_right (f i) (f (i + 1)))
    have hqP : q ∈ P :=
      hprime ▸ Nat.mem_primeFactors.mpr ⟨hqp, hq2.trans (hfmem hi''), hn.ne'⟩
    have hLd : L ≤ q := (hP q hqP).2.1
    have hdif : 0 < f (i + 1) - f i := Nat.sub_pos_of_lt (hflt (by omega) hi'')
    have hqle := Nat.le_of_dvd hdif (Nat.dvd_sub hq2 hq1)
    omega
  have hbad : Bad.card ≤ R ^ k / L + 1 := by
    rw [← card_range (R ^ k / L + 1)]
    apply card_le_card_of_injOn (fun i => f i / L)
    · intro i hi
      have hiI := (hJ (mem_filter.mp (show i ∈ Bad from hi)).1).1
      have hib := (mem_filter.mp hiI).2.2
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hib))
    · intro i hi j hj heq
      have hav {i j : ℕ} (hi : i ∈ Bad) (hj : j ∈ Bad) (hij : i < j) :
          f i / L < f j / L := by
        have hjI := (hJ (mem_filter.mp hj).1).1
        have hjr := mem_range.mp ((mem_filter.mp hjI).1)
        have hbound := (hgap hi).trans (hfle (show i + 1 ≤ j by omega) hjr)
        have he := Nat.div_le_div_right (c := L) hbound
        rw [Nat.add_div_right _ hL] at he
        omega
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (hav hi hj hij).ne heq |>.elim
      · rfl
      · exact (hav hj hi hji).ne heq.symm |>.elim
  have hJcard : J.card = I.card - 1 := card_erase_of_mem himax
  have hsplit : Good.card + Bad.card = J.card := card_filter_add_card_filter_not (s := J) _
  omega

end OMA.Erdos1100

namespace OMA.Erdos1100

open Filter Asymptotics Finset
open scoped Classical

private def primesInWindow (L : ℕ) : Finset ℕ :=
  (Nat.primesLE (8 * L)) \ Nat.primesLE L

private theorem prime_window_member {L p : ℕ} (h : p ∈ primesInWindow L) :
    p.Prime ∧ L ≤ p ∧ p ≤ 8 * L := by
  obtain ⟨hp, hnp⟩ := Finset.mem_sdiff.mp h
  obtain ⟨hhi, hprime⟩ := Nat.mem_primesLE.mp hp
  exact ⟨hprime, le_of_not_ge fun hlo => hnp (Nat.mem_primesLE.mpr ⟨hlo, hprime⟩), hhi⟩

private theorem prime_window_sum (L : ℕ) :
    ∑ p ∈ primesInWindow L, Real.log p =
      Chebyshev.theta (8 * (L : ℝ)) - Chebyshev.theta (L : ℝ) := by
  have hsub : Nat.primesLE L ⊆ Nat.primesLE (8 * L) :=
    Nat.primesLE_mono (by omega)
  have h := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) hsub
  change (∑ p ∈ primesInWindow L, Real.log p) + (∑ p ∈ Nat.primesLE L, Real.log p) =
    ∑ p ∈ Nat.primesLE (8 * L), Real.log p at h
  rw [← Chebyshev.theta_eq_sum_primesLE_log, ← Chebyshev.theta_eq_sum_primesLE_log] at h
  push_cast at h
  linarith

private theorem theta_window_lower :
    ∀ᶠ L : ℕ in atTop,
      (L : ℝ) ≤ Chebyshev.theta (8 * (L : ℝ)) - Chebyshev.theta (L : ℝ) := by
  have hT : Tendsto (fun L : ℕ => 8 * (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
  have hT' : Tendsto (fun L : ℕ => 8 * (L : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hT
  have hlog := hT.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num : (0 : ℝ) < 1 / 16))
  have hlog' := hT'.eventually
    (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog, hlog'] with L hL hn1 hn2
  have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h8 : (0 : ℝ) ≤ 8 * (L : ℝ) := by positivity
  have hlogSmall : Real.log (8 * (L : ℝ)) ≤ (1 / 16) * Real.sqrt (8 * (L : ℝ)) := by
    change ‖Real.log _‖ ≤ (1 / 16) * ‖(8 * (L : ℝ)) ^ ((1 : ℝ) / 2)‖ at hn1
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs] at hn1
    exact (le_abs_self _).trans hn1
  have hlogSmall' : Real.log (8 * (L : ℝ) + 1) ≤ (1 / 8) * (8 * (L : ℝ) + 1) := by
    change ‖Real.log _‖ ≤ (1 / 8) * ‖8 * (L : ℝ) + 1‖ at hn2
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 8 * (L : ℝ) + 1)] using hn2)
  have hmul := mul_le_mul_of_nonneg_left hlogSmall (Real.sqrt_nonneg (8 * (L : ℝ)))
  have hsq := Real.sq_sqrt h8
  have hmul' : 2 * Real.sqrt (8 * (L : ℝ)) * Real.log (8 * (L : ℝ)) ≤ L := by
    nlinarith only [hmul, hsq]
  have hlower := Chebyshev.theta_ge (8 * L)
  push_cast at hlower
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (L : ℝ)) (by positivity)
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hupper
  nlinarith only [hlower, hupper, hlogSmall', hmul', h1,
    mul_le_mul_of_nonneg_right hlog2 (by positivity : (0 : ℝ) ≤ (L : ℝ))]

private theorem prime_window_large :
    ∀ᶠ L : ℕ in atTop,
      8 ≤ L ∧
      (L : ℝ) / (2 * Real.log (L : ℝ)) ≤ (primesInWindow L).card ∧
      0 < (∏ p ∈ primesInWindow L, p) ∧
      Real.log ((∏ p ∈ primesInWindow L, p : ℕ) : ℝ) ≤ 16 * (L : ℝ) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ), theta_window_lower] with L hL htheta
  have h8 : (8 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have hlog8 : Real.log (8 * (L : ℝ)) ≤ 2 * Real.log (L : ℝ) := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity : (L : ℝ) ≠ 0)]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8]
  have hsum : (∑ p ∈ primesInWindow L, Real.log p) ≤
      ((primesInWindow L).card : ℝ) * (2 * Real.log (L : ℝ)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro p hp
    obtain ⟨hprime, _, hupper⟩ := prime_window_member hp
    exact (Real.log_le_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hupper : (p : ℝ) ≤ 8 * (L : ℝ))).trans hlog8
  have hprod : 0 < (∏ p ∈ primesInWindow L, p) :=
    prod_pos fun p hp => (prime_window_member hp).1.pos
  refine ⟨hL, (div_le_iff₀ (by positivity)).mpr (htheta.trans_eq (prime_window_sum L).symm |>.trans hsum),
    hprod, ?_⟩
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (prime_window_member hp).1.ne_zero),
    prime_window_sum]
  have htheta0 : 0 ≤ Chebyshev.theta (L : ℝ) := Chebyshev.theta_nonneg _
  have hupper := Chebyshev.theta_le_log4_mul_x (x := 8 * (L : ℝ)) (by positivity)
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at *
    linarith
  nlinarith only [htheta0, hupper, mul_le_mul_of_nonneg_right hlog4
    (by positivity : (0 : ℝ) ≤ 8 * (L : ℝ))]

end OMA.Erdos1100

namespace OMA.Erdos1100

open Filter Asymptotics Finset

private theorem choose_lower (m k : ℕ) (hk : 0 < k) (hm : 2 * k ≤ m) :
    ((m : ℝ) / (2 * (k : ℝ))) ^ k ≤ (m.choose k : ℝ) := by
  have hm' : (m : ℝ) / 2 ≤ (m + 1 - k : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hh : 2 * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  calc
    _ = ((m : ℝ) / 2) ^ k / (k : ℝ) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp [hkp.ne']
    _ ≤ ((m + 1 - k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hm' _) (by positivity)
    _ ≤ ((m + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ _ := Nat.pow_le_choose k m

private theorem scale_estimates {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hδε : δ < ε) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ Real.log 40 ≤ t ∧ 2 * Real.log 8 ≤ t ∧
      2 ≤ t ^ (1 - δ) ∧ 32 ≤ t ^ (ε - δ) ∧
      Real.log (32 * t ^ 2) ≤ (1 / 2) * t ^ δ := by
  have hlog := (isLittleO_log_rpow_atTop hδ).bound (by norm_num : (0 : ℝ) < 1 / 8)
  have hpow4 := (tendsto_rpow_atTop hδ).eventually_ge_atTop (4 * Real.log 32)
  have hpow2 := (tendsto_rpow_atTop (sub_pos.mpr hδ1)).eventually_ge_atTop (2 : ℝ)
  have hpow32 := (tendsto_rpow_atTop (sub_pos.mpr hδε)).eventually_ge_atTop (32 : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 40),
    eventually_ge_atTop (2 * Real.log 8), hpow2, hpow32, hlog, hpow4]
      with t ht h40 h8 hp2 hp32 hl hp4
  have htpos : 0 < t := by linarith
  have hr : 0 ≤ t ^ δ := Real.rpow_nonneg htpos.le _
  rw [Real.norm_of_nonneg (Real.log_nonneg ht), Real.norm_of_nonneg hr] at hl
  refine ⟨ht, h40, h8, hp2, hp32, ?_⟩
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ htpos.ne'), Real.log_pow]
  norm_num
  linarith

private theorem positive_epsilon (ε : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) :
    ∀ᶠ x : ℝ in atTop,
      ∃ n : ℕ, (n : ℝ) < x ∧
        Real.exp (Real.log (Real.log x) ^ (2 - ε)) < (Erdos1100.tauPerp n : ℝ) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hδε : δ < ε := by dsimp [δ]; linarith
  let L := fun x : ℝ => ⌊Real.log x / 20⌋₊
  let t := fun x : ℝ => Real.log (L x : ℝ)
  have hlogDiv : Tendsto (fun x : ℝ => Real.log x / 20) atTop atTop := by
    simpa only [div_eq_mul_inv] using Real.tendsto_log_atTop.atTop_mul_const
      (by norm_num : (0 : ℝ) < (20 : ℝ)⁻¹)
  have hL : Tendsto L atTop atTop := tendsto_nat_floor_atTop.comp hlogDiv
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hL)
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (1 : ℝ)
  filter_upwards [hL.eventually prime_window_large, ht.eventually (scale_estimates hδ hδ1 hδε),
    eventually_ge_atTop (Real.exp 1), hll] with x hxpr hxt hx hll
  let l := L x
  let s := t x
  let k := ⌊s ^ (1 - δ)⌋₊
  let P := primesInWindow l
  let m := P.card
  let n := ∏ p ∈ P, p
  obtain ⟨hl8, hm, hn, hnlog⟩ := hxpr
  obtain ⟨hs1, hs40, hs8, hs2, hs32, hslog⟩ := hxt
  change (l : ℝ) / (2 * s) ≤ (m : ℝ) at hm
  change Real.log (n : ℝ) ≤ 16 * (l : ℝ) at hnlog
  change 0 < n at hn
  change 1 ≤ Real.log (Real.log x) at hll
  change Real.log (32 * s ^ 2) ≤ (1 / 2) * s ^ δ at hslog
  have hsp : 0 < s := by linarith
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hlogpos : 0 < Real.log x := by
    have hx1 : (1 : ℝ) < x := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx
    exact Real.log_pos hx1
  have hk_le : (k : ℝ) ≤ s ^ (1 - δ) := Nat.floor_le (Real.rpow_nonneg hsp.le _)
  have hk_ge : s ^ (1 - δ) / 2 ≤ (k : ℝ) := by
    have hfloor : s ^ (1 - δ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hkpos : 0 < k := by
    exact_mod_cast (show (0 : ℝ) < (k : ℝ) by linarith)
  have hk_s : (k : ℝ) ≤ s := by
    calc
      _ ≤ s ^ (1 - δ) := hk_le
      _ ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
      _ = s := Real.rpow_one _
  let Q := 32 * s ^ 2
  let B := (l : ℝ) / (4 * s ^ 2)
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by
    dsimp [Q]
    nlinarith only [sq_nonneg (s - 1), hs1])
  have hs_add_pow : s ^ (1 - δ) * s ^ δ = s := by
    rw [← Real.rpow_add hsp, show 1 - δ + δ = 1 by ring, Real.rpow_one]
  have hQpow : Q ^ k ≤ Real.exp (s / 2) := by
    apply (Real.log_le_iff_le_exp (pow_pos hQpos k)).mp
    rw [Real.log_pow]
    calc
      (k : ℝ) * Real.log Q ≤ s ^ (1 - δ) * Real.log Q :=
        mul_le_mul_of_nonneg_right hk_le hlogQ
      _ ≤ s ^ (1 - δ) * ((1 / 2) * s ^ δ) :=
        mul_le_mul_of_nonneg_left hslog (Real.rpow_nonneg hsp.le _)
      _ = s / 2 := by rw [← mul_assoc, mul_right_comm, hs_add_pow]; ring
  have hQexp : Q ≤ Real.exp (s / 2) := by
    apply (Real.log_le_iff_le_exp hQpos).mp
    have hpow : s ^ δ ≤ s := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hs1 (show δ ≤ 1 by linarith)
    linarith
  have hExpL : Real.exp s = (l : ℝ) := Real.exp_log hlpos
  have hExpSq : Real.exp (s / 2) ^ 2 = (l : ℝ) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (s / 2) = s by norm_num; ring, hExpL]
  have hBexp : Real.exp (s / 2) ≤ B := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * s ^ 2)).mpr
    have hsQ : 4 * s ^ 2 ≤ Real.exp (s / 2) := by
      have h : 4 * s ^ 2 ≤ Q := by
        dsimp [Q]
        nlinarith only [sq_nonneg s]
      exact h.trans hQexp
    calc
      _ ≤ Real.exp (s / 2) * Real.exp (s / 2) :=
        mul_le_mul_of_nonneg_left hsQ (Real.exp_nonneg _)
      _ = (l : ℝ) := by rw [← pow_two, hExpSq]
  have hfloorL : Real.log x / 20 < (l : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLle : (l : ℝ) ≤ Real.log x / 20 := Nat.floor_le (by positivity)
  have hsloglog : Real.log (Real.log x) ≤ 2 * s := by
    have hlr : (8 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl8
    have hbound : Real.log x ≤ 40 * (l : ℝ) := by linarith
    have hlog := Real.log_le_log hlogpos hbound
    rw [Real.log_mul (by norm_num) hlpos.ne'] at hlog
    change Real.log (Real.log x) ≤ 2 * Real.log (l : ℝ)
    exact hlog.trans (by linarith [hs40])
  have hs8exp : 8 ≤ Real.exp (s / 2) := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 8)).mp
    linarith
  have h4log : Real.log 4 ≤ Real.log 8 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hEl : Real.exp (s / 2) ≤ (l : ℝ) / 4 := by
    calc
      _ ≤ Real.exp (s - Real.log 4) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub, hExpL, Real.exp_log (by norm_num)]
  have h8k : (8 : ℕ) ^ k < l := by
    have h8Q : (8 : ℝ) ≤ Q := by
      dsimp [Q]
      nlinarith only [sq_nonneg (s - 1), hs1]
    have hr := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) h8Q k).trans (hQpow.trans hEl)
    exact_mod_cast (show (8 : ℝ) ^ k < (l : ℝ) by linarith)
  have hsep (j : ℕ) (hj : j ≤ k) : (8 * l) ^ j < l ^ (j + 1) := by
    rw [mul_pow, pow_succ]
    have hi := (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 8) hj).trans_lt h8k
    simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_right hi
      (pow_pos (by omega : 0 < l) j)
  have hblock := block_bound P l (8 * l) k (by omega)
    (fun _ hp => prime_window_member hp)
    (fun j hj => (hsep j hj.le).trans_le
      (pow_le_pow_right₀ (by omega : 1 ≤ l) (by omega)))
    (hsep k le_rfl)
  have hBmul : B * (2 * s) = (l : ℝ) / (2 * s) := by
    dsimp [B]
    field_simp [hsp.ne']
    <;> ring
  have hB1 : 1 ≤ B := by linarith
  have h2k : 2 * k ≤ m := by
    have hb := mul_le_mul_of_nonneg_right hB1 (by positivity : 0 ≤ 2 * s)
    rw [one_mul, hBmul] at hb
    exact_mod_cast (show 2 * (k : ℝ) ≤ (m : ℝ) by linarith [hb.trans hm])
  have hBmk : B ≤ (m : ℝ) / (2 * (k : ℝ)) := by
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < 2 * k by omega) :
      0 < 2 * (k : ℝ))).mpr
    calc
      _ ≤ B * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hBpos.le
      _ ≤ (m : ℝ) := hBmul.trans_le hm
  let Y := B ^ k
  have hY : Y ≤ (m.choose k : ℝ) :=
    (pow_le_pow_left₀ hBpos.le hBmk _).trans (choose_lower m k hkpos h2k)
  have hBQ : B * Q = 8 * (l : ℝ) := by
    dsimp [B, Q]
    field_simp [hsp.ne']
    <;> ring
  have hGap : (((8 * l) ^ k / l : ℕ) : ℝ) ≤ Y / 4 := by
    apply Nat.cast_div_le.trans
    push_cast
    rw [← hBQ, mul_pow]
    calc
      _ ≤ Y * ((l : ℝ) / 4) / (l : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hQpow.trans hEl) (pow_nonneg hBpos.le _)) hlpos.le
      _ = _ := by field_simp [hlpos.ne']
  have hYexp : Real.exp ((k : ℝ) * (s / 2)) ≤ Y := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hBexp _
  have hY8 : 8 ≤ Y := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    have h := mul_le_mul_of_nonneg_right hk1 (by positivity : 0 ≤ s / 2)
    rw [one_mul] at h
    exact hs8exp.trans ((Real.exp_le_exp.mpr h).trans hYexp)
  have htau : Y / 2 ≤ (Erdos1100.tauPerp n : ℝ) := by
    change m.choose k ≤ Erdos1100.tauPerp n + (8 * l) ^ k / l + 2 at hblock
    have hc : (m.choose k : ℝ) ≤ (Erdos1100.tauPerp n : ℝ) +
        (((8 * l) ^ k / l : ℕ) : ℝ) + 2 := by exact_mod_cast hblock
    linarith
  let U := Real.log (Real.log x) ^ (2 - ε)
  have hU : U ≤ 4 * s ^ (2 - ε) := by
    have he2 : 0 ≤ 2 - ε := by linarith
    have h4 : (2 : ℝ) ^ (2 - ε) ≤ 4 := by
      calc
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num [Real.rpow_two]
    calc
      _ ≤ (2 * s) ^ (2 - ε) :=
        Real.rpow_le_rpow (by linarith) hsloglog he2
      _ = (2 : ℝ) ^ (2 - ε) * s ^ (2 - ε) :=
        Real.mul_rpow (by norm_num) hsp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hsp.le _)
  have hsk : s ^ (2 - δ) / 4 ≤ (k : ℝ) * (s / 2) := by
    calc
      _ = (s ^ (1 - δ) / 2) * (s / 2) := by
        have hh : s ^ (1 - δ) * s = s ^ (2 - δ) := by
          calc
            _ = s ^ (1 - δ) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hsp, show 1 - δ + 1 = 2 - δ by ring]
        nlinarith only [hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right hk_ge (by positivity)
  have hsexp : 8 * s ^ (2 - ε) ≤ s ^ (2 - δ) / 4 := by
    have hpow := mul_le_mul_of_nonneg_right hs32 (Real.rpow_nonneg hsp.le (2 - ε))
    rw [← Real.rpow_add hsp, show (ε - δ) + (2 - ε) = 2 - δ by ring] at hpow
    linarith
  have hsE1 : 1 ≤ s ^ (2 - ε) := Real.one_le_rpow hs1 (by linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hUexp : Real.exp U < Y / 4 := by
    calc
      _ < Real.exp ((k : ℝ) * (s / 2) - Real.log 4) := Real.exp_lt_exp.mpr (by linarith)
      _ = Real.exp ((k : ℝ) * (s / 2)) / 4 := by rw [Real.exp_sub, Real.exp_log (by norm_num)]
      _ ≤ _ := div_le_div_of_nonneg_right hYexp (by norm_num)
  refine ⟨n, ?_, hUexp.trans_le (by linarith [htau, hY8])⟩
  apply (Real.log_lt_log_iff (by exact_mod_cast hn) hxpos).mp
  linarith

end OMA.Erdos1100

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_hall := by
  intro ε hε
  let η := min ε 1
  have hη : 0 < η := lt_min hε zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  filter_upwards [OMA.Erdos1100.positive_epsilon η hη hη1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (1 : ℝ)] with x hx hx1
  obtain ⟨n, hnx, hn⟩ := hx
  refine ⟨n, hnx, ?_⟩
  apply lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hn
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
