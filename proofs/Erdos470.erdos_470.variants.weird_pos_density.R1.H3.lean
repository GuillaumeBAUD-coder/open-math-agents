import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1
import Mathlib

-- Step Erdos470.erdos_470.variants.weird_pos_density.R1.H3: hypothesis H3 of reduction
-- Erdos470.erdos_470.variants.weird_pos_density.R1
-- Credit: @ivillar
-- The perfect numbers have natural density zero.
--
-- Proof. An even perfect number is `2 ^ k * q` with `q = 2 ^ (k + 1) - 1` prime
-- (Euclid-Euler; the proof below is copied from Mathlib's Archive, Wiedijk 100 theorems no. 70,
-- by Aaron Anderson, since the Archive is not importable here). Hence it equals
-- `q * ((q + 1) / 2)` for a prime `q` below it. An odd perfect number `n` satisfies
-- `σ n = 2 n ≡ 2 (mod 4)`; as `σ (p ^ e)` has the parity of `e + 1` for odd `p`, exactly one
-- prime has odd exponent, so `n = q * M ^ 2` with `q` prime. Fix `T`. Perfect numbers below `b`
-- are then of the form `q * ((q + 1) / 2)` or `q * M ^ 2` with `M ≤ T` (at most `(T + 1) π(b)`
-- of these), or are divisible by `M ^ 2` for some `M > T` (at most `b ∑_{M > T} 1 / M ^ 2 ≤
-- 2 b / (T + 1)` of these). Chebyshev's bound `π(b) = O(b / log b)` finishes the proof.

open Filter Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OMA.Erdos470H3

/-! ### Euclid-Euler, copied from Mathlib's Archive (Wiedijk 100 theorems no. 70) -/

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem euclid_euler {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  obtain ⟨k, m, hmodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hm : ¬Even m := Nat.not_even_iff_odd.mpr hmodd
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-! ### Odd perfect numbers are a prime times a square -/

lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp (hp.pow (n := k))]
    omega

lemma odd_perfect_form {n : ℕ} (hn0 : n ≠ 0) (hodd : Odd n) (hσ : σ 1 n = 2 * n) :
    ∃ q M : ℕ, q.Prime ∧ n = q * M ^ 2 := by
  classical
  have hfac : σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hn0,
      Finsupp.prod, Nat.support_factorization]
  have hpar : ∀ p ∈ n.primeFactors,
      σ 1 (p ^ n.factorization p) % 2 = (n.factorization p + 1) % 2 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpodd : Odd p := Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
    rw [sigma_one_apply_prime_pow hpp]
    exact geom_sum_mod_two hpodd _
  have hn2 := Nat.odd_iff.mp hodd
  set O := n.primeFactors.filter (fun p => Odd (n.factorization p)) with hOdef
  have hO_ne : O.Nonempty := by
    by_contra hO
    rw [Finset.not_nonempty_iff_eq_empty] at hO
    have h2 : ¬ 2 ∣ σ 1 n := by
      rw [hfac, Prime.dvd_finset_prod_iff Nat.prime_two.prime]
      rintro ⟨p, hp, hdvd⟩
      have hev : Even (n.factorization p) := by
        by_contra hne
        rw [Nat.not_even_iff_odd] at hne
        have hpO : p ∈ O := Finset.mem_filter.mpr ⟨hp, hne⟩
        rw [hO] at hpO
        simp at hpO
      have := hpar p hp
      obtain ⟨r, hr⟩ := hev
      omega
    exact h2 ⟨n, hσ⟩
  have hO_uniq : ∀ p ∈ O, ∀ p' ∈ O, p = p' := by
    intro p hp p' hp'
    by_contra hne
    rw [Finset.mem_filter] at hp hp'
    have hsub : ({p, p'} : Finset ℕ) ⊆ n.primeFactors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp.1
      · exact hp'.1
    have hdvd := Finset.prod_dvd_prod_of_subset _ _ (fun p => σ 1 (p ^ n.factorization p)) hsub
    rw [Finset.prod_pair hne, ← hfac, hσ] at hdvd
    have e1 : 2 ∣ σ 1 (p ^ n.factorization p) := by
      have := hpar p hp.1
      obtain ⟨r, hr⟩ := hp.2
      omega
    have e2 : 2 ∣ σ 1 (p' ^ n.factorization p') := by
      have := hpar p' hp'.1
      obtain ⟨r, hr⟩ := hp'.2
      omega
    have h4 : 2 * 2 ∣ 2 * n := (Nat.mul_dvd_mul e1 e2).trans hdvd
    obtain ⟨c, hc⟩ := h4
    omega
  obtain ⟨q, hqO⟩ := hO_ne
  have hq := Finset.mem_filter.mp hqO
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
  have hexp : ∀ p, n.factorization p = (if q = p then 1 else 0) + 2 * (n.factorization p / 2) := by
    intro p
    by_cases hpq : p = q
    · subst hpq
      obtain ⟨r, hr⟩ := hq.2
      simp only [if_true]
      omega
    · have hqp' : q ≠ p := Ne.symm hpq
      simp only [hqp', if_false]
      by_cases hp : p ∈ n.primeFactors
      · have hev : Even (n.factorization p) := by
          by_contra hne
          rw [Nat.not_even_iff_odd] at hne
          exact hpq (hO_uniq p (Finset.mem_filter.mpr ⟨hp, hne⟩) q hqO)
        obtain ⟨r, hr⟩ := hev
        omega
      · have h0 : n.factorization p = 0 := by
          rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
        omega
  let f : ℕ →₀ ℕ := Finsupp.mapRange (fun e => e / 2) (by norm_num) n.factorization
  let M := f.prod (· ^ ·)
  have hfsupp : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    have hp' : p ∈ n.factorization.support := Finsupp.support_mapRange hp
    rw [Nat.support_factorization] at hp'
    exact Nat.prime_of_mem_primeFactors hp'
  have hMf : M.factorization = f := Nat.prod_pow_factorization_eq_self hfsupp
  have hM0 : M ≠ 0 := by
    simp only [M, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hfsupp p hp).ne_zero)
  refine ⟨q, M, hqp, ?_⟩
  apply Nat.eq_of_factorization_eq hn0 (mul_ne_zero hqp.ne_zero (pow_ne_zero 2 hM0))
  intro p
  rw [Nat.factorization_mul hqp.ne_zero (pow_ne_zero 2 hM0), Nat.factorization_pow, hMf,
    hqp.factorization]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, f,
    Finsupp.mapRange_apply]
  exact hexp p

/-! ### Counting -/

lemma card_primesBelow_le (b : ℕ) : #(Nat.primesBelow b) ≤ Nat.primeCounting b := by
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact Nat.monotone_primeCounting' (Nat.le_succ b)

lemma cover (T b n : ℕ) (hn0 : 0 < n) (hsum : ∑ d ∈ n.properDivisors, d = n) (hnb : n < b) :
    n ∈ ((Nat.primesBelow b).image (fun q => q * ((q + 1) / 2))) ∪
      ((Nat.primesBelow b ×ˢ Finset.Icc 1 T).image (fun x => x.1 * x.2 ^ 2)) ∪
      ((Finset.Ioo T b).biUnion (fun M => (Finset.Ioc 0 b).filter (fun m => M ^ 2 ∣ m))) := by
  have hperf : Nat.Perfect n := ⟨hsum, hn0⟩
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨k, hpr, rfl⟩ := euclid_euler hev hperf
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [Finset.mem_image]
    refine ⟨mersenne (k + 1), ?_, ?_⟩
    · rw [Nat.mem_primesBelow]
      refine ⟨?_, hpr⟩
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have : mersenne (k + 1) ≤ 2 ^ k * mersenne (k + 1) := Nat.le_mul_of_pos_left _ this
      omega
    · rw [succ_mersenne, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  · have hσ : σ 1 n = 2 * n := by
      rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, hsum]
      ring
    obtain ⟨q, M, hq, rfl⟩ := odd_perfect_form hn0.ne' hodd hσ
    have hM : 1 ≤ M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h
        simp at hn0
      · exact h
    have hMM : M ≤ M ^ 2 := by nlinarith
    have hqM : q ≤ q * M ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have hMq : M ^ 2 ≤ q * M ^ 2 := Nat.le_mul_of_pos_left _ hq.pos
    by_cases hMT : M ≤ T
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨(q, M), Finset.mem_product.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hq⟩,
        Finset.mem_Icc.mpr ⟨hM, hMT⟩⟩, rfl⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨M, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, hnb.le⟩, dvd_mul_left _ _⟩⟩

lemma count_le (T b : ℕ) :
    (({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.Iio b).ncard : ℝ) ≤
      ((T : ℝ) + 1) * (Nat.primeCounting b : ℝ) + b * (2 / ((T : ℝ) + 1)) := by
  set E := (Nat.primesBelow b).image (fun q => q * ((q + 1) / 2)) with hE
  set A := (Nat.primesBelow b ×ˢ Finset.Icc 1 T).image (fun x => x.1 * x.2 ^ 2) with hA
  set B := (Finset.Ioo T b).biUnion (fun M => (Finset.Ioc 0 b).filter (fun m => M ^ 2 ∣ m))
    with hB
  have hsub : ({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.Iio b) ⊆
      ((E ∪ A ∪ B : Finset ℕ) : Set ℕ) := by
    rintro n ⟨⟨hn0, hsum⟩, hnb⟩
    exact cover T b n hn0 hsum hnb
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : #(E ∪ A ∪ B) ≤ #E + #A + #B :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hEc : #E ≤ Nat.primeCounting b := Finset.card_image_le.trans (card_primesBelow_le b)
  have hAc : #A ≤ Nat.primeCounting b * T := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right _ (card_primesBelow_le b)
  have hBn : #B ≤ ∑ M ∈ Finset.Ioo T b, b / M ^ 2 := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun M _ => ?_)
    rw [Nat.Ioc_filter_dvd_card_eq_div]
  have hBc : (#B : ℝ) ≤ b * (2 / ((T : ℝ) + 1)) := by
    calc (#B : ℝ) ≤ ((∑ M ∈ Finset.Ioo T b, b / M ^ 2 : ℕ) : ℝ) := by exact_mod_cast hBn
      _ = ∑ M ∈ Finset.Ioo T b, ((b / M ^ 2 : ℕ) : ℝ) := Nat.cast_sum _ _
      _ ≤ ∑ M ∈ Finset.Ioo T b, (b : ℝ) * ((M : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro M _
          calc ((b / M ^ 2 : ℕ) : ℝ) ≤ (b : ℝ) / ((M ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
            _ = (b : ℝ) * ((M : ℝ) ^ 2)⁻¹ := by push_cast; ring
      _ = b * ∑ M ∈ Finset.Ioo T b, ((M : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ b * (2 / ((T : ℝ) + 1)) := by
          gcongr
          exact sum_Ioo_inv_sq_le T b
  have hsum : (({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.Iio b).ncard : ℝ) ≤
      (#E : ℝ) + #A + #B := by
    exact_mod_cast h1.trans h2
  have hEr : (#E : ℝ) ≤ Nat.primeCounting b := by exact_mod_cast hEc
  have hAr : (#A : ℝ) ≤ (Nat.primeCounting b : ℝ) * T := by exact_mod_cast hAc
  nlinarith

end OMA.Erdos470H3

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H3 := by
  unfold OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H3
  unfold Set.HasDensity
  set P := {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} with hP
  have hpd : ∀ b : ℕ, P.partialDensity Set.univ b = ((P ∩ Set.Iio b).ncard : ℝ) / b := by
    intro b
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  refine (tendsto_congr hpd).mpr ?_
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun b =>
    lt_of_lt_of_le ha (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), fun a ha => ?_⟩
  obtain ⟨T, hT⟩ := exists_nat_gt (4 / a)
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have h4 : 4 < a * ((T : ℝ) + 1) := by
    have := (div_lt_iff₀ ha).mp hT
    nlinarith
  set δ := a / (4 * ((T : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hpi : ∀ᶠ b : ℕ in atTop, (Nat.primeCounting b : ℝ) ≤ δ * b := by
    have h1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le one_pos)
    have h2 := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop ((Real.log 4 + 1) / δ))
    filter_upwards [h1, h2, eventually_ge_atTop 2] with b hb1 hb2 hb3
    simp only [Function.comp, Nat.floor_natCast] at hb1 hb2
    have hb3r : (2 : ℝ) ≤ b := by exact_mod_cast hb3
    have hlogpos : 0 < Real.log b := Real.log_pos (by linarith)
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hl4 : 0 < Real.log 4 + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    calc (Nat.primeCounting b : ℝ) ≤ (Real.log 4 + 1) * b / Real.log b := hb1
      _ ≤ δ * b := by
        rw [div_le_iff₀ hlogpos]
        have := (div_le_iff₀ hδ).mp hb2
        nlinarith
  filter_upwards [hpi, eventually_ge_atTop 2] with b hb hb2
  have hbpos : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb2
    linarith
  rw [div_lt_iff₀ hbpos]
  have hc := OMA.Erdos470H3.count_le T b
  have hTδ : ((T : ℝ) + 1) * δ = a / 4 := by
    rw [hδdef]
    field_simp
  have h2T : b * (2 / ((T : ℝ) + 1)) < a * b / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hT1 (by norm_num)]
    nlinarith
  calc ((P ∩ Set.Iio b).ncard : ℝ) ≤ ((T : ℝ) + 1) * (Nat.primeCounting b : ℝ) +
        b * (2 / ((T : ℝ) + 1)) := hc
    _ ≤ ((T : ℝ) + 1) * (δ * b) + b * (2 / ((T : ℝ) + 1)) := by gcongr
    _ < a * b := by
        have : ((T : ℝ) + 1) * (δ * b) = a / 4 * b := by rw [← mul_assoc, hTδ]
        rw [this]
        nlinarith
