import FormalConjectures.ErdosProblems.«1052»

-- Reduction Erdos1052.erdos_1052.R1 of Erdős Problem 1052
-- Credit: @adammcarter
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Notation: a unitary perfect N is written 2^m * s with s odd (s = N / 2^m, m the 2-adic
-- valuation), and sigma*(N) = 2 * N, where sigma* is the sum of all unitary divisors.
--
-- PROVED BELOW, no hypothesis needed (M. V. Subbarao and L. J. Warren, "Unitary perfect
-- numbers", Canad. Math. Bull. 9 (1966), 147-153):
--   * sum_udiv_eq_prod: sigma*(N) is the product of (1 + p^a) over the prime powers p^a || N;
--   * finite_card_primeFactors (their Theorem 4): for each k only finitely many unitary
--     perfect numbers have exactly k distinct primes;
--   * card_primeFactors_le (from their Lemma 1 (3.2)): N has at most m + 2 distinct primes.
-- Together these show that the target is equivalent to "m is bounded".  The two hypotheses
-- split that statement according to whether the odd part s is squarefree.
--
-- H1 (KNOWN, published): S. W. Graham, "Unitary perfect numbers with squarefree odd part",
--    Fibonacci Quart. 27 (1989), no. 4, 317-322.  Theorem on p. 317, transcribed from the
--    scanned paper with symbols retyped: if 2^m s is a unitary perfect number and s is
--    squarefree, then either m = 1 and s = 3, m = 2 and s = 3*5, or m = 6 and s = 3*5*7*13.
--    (There s denotes an odd squarefree number.)  These are 6, 60 and 87360.  The case m = 0,
--    odd n, is covered by Subbarao-Warren Theorem 1: there is no odd unitary perfect number.
--    The other two known examples, 90 = 2 * 3^2 * 5 and Wall's 2^18 * 3 * 5^4 * 7 * ..., have
--    a non-squarefree odd part.
-- H2 (OPEN, the core of the problem): m is bounded over the unitary perfect numbers whose odd
--    part is not squarefree.  It follows from the target, and with H1 it gives the target, so
--    it carries all of the remaining difficulty; no proof is known.

namespace OMA.R_Erdos1052_erdos_1052_R1

-- Graham 1989: a unitary perfect number with squarefree odd part is 6, 60 or 87360.
def H1 : Prop :=
  ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → Squarefree (n / 2 ^ padicValNat 2 n) →
    n = 6 ∨ n = 60 ∨ n = 87360

-- The 2-adic valuation is bounded over unitary perfect numbers with non-squarefree odd part.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    padicValNat 2 n ≤ A

-- Membership in the set of all unitary divisors of n (n itself included).
theorem mem_udiv {n d : ℕ} :
    d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  simp [and_assoc]

theorem self_mem_udiv {n : ℕ} (hn : n ≠ 0) :
    n ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  rw [mem_udiv, Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact ⟨dvd_rfl, hn, Nat.coprime_one_right n⟩

theorem proper_eq_erase (n : ℕ) :
    Erdos1052.properUnitaryDivisors n = (Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors).erase n := by
  ext d
  simp only [Erdos1052.properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd, hc⟩
    exact ⟨h2.ne, ⟨hd, by omega⟩, hc⟩
  · rintro ⟨hne, ⟨hd, hn⟩, hc⟩
    have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
    exact ⟨⟨Nat.pos_of_ne_zero hd0,
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hne⟩, hd, hc⟩

theorem sum_udiv_eq_sum_proper_add {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      (∑ i ∈ Erdos1052.properUnitaryDivisors n, i) + n := by
  rw [proper_eq_erase, Finset.sum_erase_add _ _ (self_mem_udiv hn)]

-- A unitary perfect number is positive and its unitary divisor sum equals 2 * n.
theorem sum_udiv_of_isUnitaryPerfect {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    0 < n ∧ ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d = 2 * n := by
  obtain ⟨hs, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [sum_udiv_eq_sum_proper_add hpos.ne', hs]
  ring

theorem factorization_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) (p : ℕ) :
    d.factorization p = if p ∈ d.primeFactors then n.factorization p else 0 := by
  obtain ⟨hd, hn, hc⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hq : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  split_ifs with hp
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n / d := by
      intro h'
      have := Nat.dvd_gcd hpd h'
      rw [hc.gcd_eq_one] at this
      exact hpp.not_dvd_one this
    conv_rhs => rw [hmul]
    rw [Nat.factorization_mul hd0 hq, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · by_contra h'
    exact hp (Nat.support_factorization d ▸ Finsupp.mem_support_iff.mpr h')

theorem ppart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    ∏ p ∈ S, p ^ n.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

theorem factorization_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (q : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p).factorization q = if q ∈ S then n.factorization q else 0 := by
  rw [Nat.factorization_prod (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (hS hp)).factorization_pow, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

theorem primeFactors_ppart {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_ppart hS]
  split_ifs with h
  · simp only [h, iff_true]
    exact Finsupp.mem_support_iff.mp (by rw [Nat.support_factorization]; exact hS h)
  · simp [h]

theorem ppart_mem_udiv {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p) ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors := by
  have h0 := ppart_ne_zero hS
  have hdvd : (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd h0 hn]
    intro q
    rw [factorization_ppart hS]
    split_ifs <;> simp
  refine mem_udiv.mpr ⟨hdvd, hn, Nat.coprime_of_dvd fun p hp h1 h2 => ?_⟩
  have hq : n / (∏ p ∈ S, p ^ n.factorization p) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero h0)).ne'
  have e1 := (hp.dvd_iff_one_le_factorization h0).mp h1
  have e2 := (hp.dvd_iff_one_le_factorization hq).mp h2
  rw [factorization_ppart hS] at e1
  rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, factorization_ppart hS] at e2
  split_ifs at e1 e2 <;> omega

theorem eq_ppart_of_mem_udiv {n d : ℕ}
    (h : d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors) :
    d = ∏ p ∈ d.primeFactors, p ^ n.factorization p := by
  obtain ⟨hd, hn, -⟩ := mem_udiv.mp h
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  have hsub := Nat.primeFactors_mono hd hn
  exact Nat.eq_of_factorization_eq hd0 (ppart_ne_zero hsub) fun q => by
    rw [factorization_of_mem_udiv h, factorization_ppart hsub]

-- Product formula: the unitary divisor sum of n is the product of (1 + p^a) over p^a || n.
theorem sum_udiv_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ Finset.filter (fun d => Nat.Coprime d (n / d)) n.divisors, d =
      ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Finset.prod_one_add]
  exact Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ p ∈ S, p ^ n.factorization p)
    (fun d hd => Finset.mem_powerset.mpr (Nat.primeFactors_mono (mem_udiv.mp hd).1 hn))
    (fun S hS => ppart_mem_udiv hn (Finset.mem_powerset.mp hS))
    (fun d hd => (eq_ppart_of_mem_udiv hd).symm)
    (fun S hS => primeFactors_ppart (Finset.mem_powerset.mp hS))
    (fun d hd => eq_ppart_of_mem_udiv hd)

theorem prod_primeFactors_pow_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
  (eq_ppart_of_mem_udiv (self_mem_udiv hn)).symm

-- For every k and every real r there are only finitely many k-element sets T of positive
-- naturals with prod over q in T of (1 + 1/q) equal to r.
theorem finite_finsets_prod_one_add_inv (k : ℕ) : ∀ r : ℝ,
    {T : Finset ℕ | T.card = k ∧ (∀ q ∈ T, 0 < q) ∧ ∏ q ∈ T, (1 + (q : ℝ)⁻¹) = r}.Finite := by
  induction k with
  | zero =>
    intro r
    refine (Set.finite_singleton (∅ : Finset ℕ)).subset ?_
    rintro T ⟨hT, -, -⟩
    exact Set.mem_singleton_iff.mpr (Finset.card_eq_zero.mp hT)
  | succ k ih =>
    intro r
    by_cases hr : 1 < r
    · have hlim : Filter.Tendsto (fun m : ℕ => ((1 : ℝ) + (m : ℝ)⁻¹) ^ (k + 1))
          Filter.atTop (nhds 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa using this.pow (k + 1)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hr))
      refine (Set.Finite.biUnion (Set.finite_lt_nat N) fun m _ =>
        (ih (r / (1 + (m : ℝ)⁻¹))).image (insert m)).subset ?_
      rintro T ⟨hcard, hpos, hprod⟩
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      set m := T.min' hne with hm
      have hmT : m ∈ T := Finset.min'_mem T hne
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hmT
      have hfac : (0 : ℝ) < 1 + (m : ℝ)⁻¹ := by positivity
      have hsplit := Finset.mul_prod_erase T (fun q : ℕ => (1 + (q : ℝ)⁻¹)) hmT
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
      refine ⟨m, ?_, T.erase m, ⟨?_, ?_, ?_⟩, Finset.insert_erase hmT⟩
      · by_contra hlt
        have hle : r ≤ (1 + (m : ℝ)⁻¹) ^ (k + 1) := by
          rw [← hprod, ← hcard, ← Finset.prod_const]
          refine Finset.prod_le_prod (fun q hq => by positivity) (fun q hq => ?_)
          have hq0 : (0 : ℝ) < q := by exact_mod_cast hpos q hq
          have : (m : ℝ) ≤ q := by exact_mod_cast Finset.min'_le T q hq
          linarith [inv_anti₀ hm0 this]
        exact absurd (hN m (by omega)) (not_lt.mpr hle)
      · rw [Finset.card_erase_of_mem hmT, hcard]; rfl
      · exact fun q hq => hpos q (Finset.mem_of_mem_erase hq)
      · rw [eq_div_iff hfac.ne', mul_comm, hsplit, hprod]
    · refine Set.Finite.subset (Set.finite_empty) ?_
      rintro T ⟨hcard, hpos, hprod⟩
      exfalso
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨m, hmT⟩ := hne
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hmT
      have hsplit := Finset.mul_prod_erase T (fun q : ℕ => (1 + (q : ℝ)⁻¹)) hmT
      have h1 : 1 ≤ ∏ q ∈ T.erase m, (1 + (q : ℝ)⁻¹) :=
        Finset.one_le_prod fun q hq => by
          have : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
          linarith
      have h2 : (0 : ℝ) < (m : ℝ)⁻¹ := by positivity
      have : 1 < (1 + (m : ℝ)⁻¹) * ∏ q ∈ T.erase m, (1 + (q : ℝ)⁻¹) := by nlinarith
      rw [hsplit, hprod] at this
      exact hr this

-- Subbarao-Warren 1966, Theorem 4: for each fixed k, only finitely many unitary perfect
-- numbers have exactly k distinct prime factors.
theorem finite_card_primeFactors (k : ℕ) :
    {n | Erdos1052.IsUnitaryPerfect n ∧ n.primeFactors.card = k}.Finite := by
  refine ((finite_finsets_prod_one_add_inv k 2).image (fun T => ∏ q ∈ T, q)).subset ?_
  rintro n ⟨h, hk⟩
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  have hn0 : n ≠ 0 := hpos.ne'
  have hexp : ∀ p ∈ n.primeFactors, 0 < n.factorization p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0
      (Nat.dvd_of_mem_primeFactors hp)
  have hinj : Set.InjOn (fun p => p ^ n.factorization p) n.primeFactors := by
    intro p hp p' hp' heq
    have e1 := Nat.primeFactors_prime_pow (hexp p hp).ne' (Nat.prime_of_mem_primeFactors hp)
    have e2 := Nat.primeFactors_prime_pow (hexp p' hp').ne' (Nat.prime_of_mem_primeFactors hp')
    simp only at heq
    rw [heq, e2] at e1
    exact (Finset.singleton_inj.mp e1).symm
  have hself : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := prod_primeFactors_pow_self hn0
  have hR : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) = n := by exact_mod_cast hself
  have hS : ∏ p ∈ n.primeFactors, ((1 : ℝ) + (p : ℝ) ^ n.factorization p) = 2 * n := by
    rw [sum_udiv_eq_prod hn0] at hs
    exact_mod_cast hs
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  refine ⟨n.primeFactors.image (fun p => p ^ n.factorization p), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, hk]
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · rw [Finset.prod_image hinj]
    have : ∀ p ∈ n.primeFactors, (1 + (((p ^ n.factorization p : ℕ)) : ℝ)⁻¹) =
        ((1 : ℝ) + (p : ℝ) ^ n.factorization p) / ((p : ℝ) ^ n.factorization p) := by
      intro p hp
      have : (0 : ℝ) < (p : ℝ) ^ n.factorization p := by
        have := (Nat.prime_of_mem_primeFactors hp).pos
        positivity
      push_cast
      field_simp
      ring
    rw [Finset.prod_congr rfl this, Finset.prod_div_distrib, hS, hR]
    field_simp
  · show ∏ q ∈ n.primeFactors.image (fun p => p ^ n.factorization p), q = n
    rw [Finset.prod_image hinj, hself]

-- Balance equation: for a unitary perfect n the product of (1 + p^a) over p^a || n is 2 * n.
theorem prod_eq_two_mul {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect h
  rw [← sum_udiv_eq_prod hpos.ne']
  exact hs

-- A unitary perfect n has at most v_2(n) + 1 odd prime factors.
theorem card_odd_primeFactors_le {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    (n.primeFactors.filter (fun p => p ≠ 2)).card ≤ padicValNat 2 n + 1 := by
  have hpos : 0 < n := h.2
  have h1 := prod_eq_two_mul h
  have hev : ∀ p ∈ n.primeFactors.filter (fun p => p ≠ 2), 2 ∣ 1 + p ^ n.factorization p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have hpo : Odd p := (Nat.prime_of_mem_primeFactors hp1).odd_of_ne_two hp2
    rw [add_comm, ← even_iff_two_dvd]
    exact (hpo.pow).add_one
  have hdvd : 2 ^ (n.primeFactors.filter (fun p => p ≠ 2)).card ∣ 2 * n := by
    rw [← h1, ← Finset.prod_const]
    exact (Finset.prod_dvd_prod_of_dvd _ _ hev).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := (padicValNat_dvd_iff_le (by omega : 2 * n ≠ 0)).mp hdvd
  rw [padicValNat.mul (by norm_num) hpos.ne', padicValNat_self] at hle
  omega

-- Subbarao-Warren 1966, from Lemma 1 (3.2): a unitary perfect n has at most v_2(n) + 2
-- distinct prime factors.
theorem card_primeFactors_le {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) :
    n.primeFactors.card ≤ padicValNat 2 n + 2 := by
  have hT := card_odd_primeFactors_le h
  have hsub : n.primeFactors ⊆ insert 2 (n.primeFactors.filter (fun p => p ≠ 2)) := by
    intro p hp
    by_cases h2 : p = 2
    · simp [h2]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, h2⟩)
  calc n.primeFactors.card
      ≤ (insert 2 (n.primeFactors.filter (fun p => p ≠ 2))).card := Finset.card_le_card hsub
    _ ≤ (n.primeFactors.filter (fun p => p ≠ 2)).card + 1 := Finset.card_insert_le _ _
    _ ≤ padicValNat 2 n + 2 := by omega

theorem main : H1 → H2 → type_of% @Erdos1052.erdos_1052 := by
  intro h1 h2
  obtain ⟨A, hA⟩ := h2
  refine (((Set.finite_Iic (A + 2)).biUnion fun k _ => finite_card_primeFactors k).union
    (((Set.finite_singleton 87360).insert 60).insert 6)).subset ?_
  intro n hn
  by_cases hsq : Squarefree (n / 2 ^ padicValNat 2 n)
  · refine Or.inr ?_
    rcases h1 n hn hsq with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Set.mem_biUnion (x := n.primeFactors.card)
      (Set.mem_Iic.mpr ((card_primeFactors_le hn).trans
        (Nat.add_le_add_right (hA n hn hsq) 2))) ⟨hn, rfl⟩)

end OMA.R_Erdos1052_erdos_1052_R1
