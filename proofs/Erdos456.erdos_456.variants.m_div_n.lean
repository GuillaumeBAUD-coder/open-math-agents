import FormalConjectures.ErdosProblems.«456»

-- Problem: Erdős Problem 456 — m div n
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/456.lean:161 (declaration Erdos456.erdos_456.variants.m_div_n)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: Erdős, Some unconventional problems in number theory (1979), where it is called easy.

/-!
# For almost all n, the least m with n dividing the totient of m is much larger than n

If `m n < C * n` then `C * n` bounds some `k` with `n ∣ φ k`, so `n` is `φ k / t` with `t < C`.
Hence the bad `n` below `N` are at most `C` times the number of totient values of `k < C * N`.
Those are few: either `k` has a prime factor in each of `M` disjoint blocks of odd primes, and then
`2 ^ M ∣ φ k`, or `k` avoids a whole block, which happens for a proportion at most
`∏ (1 - 1 / p)` of integers. Blocks with small products exist because the prime reciprocals diverge.
A diagonal choice of thresholds then gives a density one set on which `m n / n → ∞`.
-/

open Nat Filter Finset

namespace OMAErdos456

open Erdos456 (m)


lemma prod_one_sub_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ Real.exp (-(∑ p ∈ S, 1 / (p : ℝ))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
    linarith
  · intro p hp
    have := Real.add_one_le_exp (-(1 / (p : ℝ)))
    linarith

lemma exists_primes_prod_small (L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ L < p) ∧ ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ δ := by
  by_contra! H
  apply Nat.Primes.not_summable_one_div
  refine summable_of_sum_le (c := (L + 1 : ℝ) + (- Real.log δ)) (fun p => by positivity) ?_
  intro u
  classical
  let S : Finset ℕ := (u.image (fun p : Nat.Primes => (p : ℕ))).filter (fun p => L < p)
  have hS : ∀ p ∈ S, p.Prime ∧ L < p := by
    intro p hp
    simp only [S, mem_filter, mem_image] at hp
    obtain ⟨⟨q, hq, rfl⟩, h⟩ := hp
    exact ⟨q.2, h⟩
  have h1 := H S hS
  have h2 := prod_one_sub_le_exp S (fun p hp => (hS p hp).1.pos)
  have h3 : ∑ p ∈ S, 1 / (p : ℝ) < - Real.log δ := by
    have := lt_of_lt_of_le h1 h2
    have := Real.log_lt_log hδ this
    rw [Real.log_exp] at this
    linarith
  have hsplit : ∑ x ∈ u, 1 / ((x : ℕ) : ℝ) =
      ∑ x ∈ u.filter (fun p : Nat.Primes => L < (p : ℕ)), 1 / ((x : ℕ) : ℝ) +
      ∑ x ∈ u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ)), 1 / ((x : ℕ) : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hA : ∑ x ∈ u.filter (fun p : Nat.Primes => L < (p : ℕ)), 1 / ((x : ℕ) : ℝ) =
      ∑ p ∈ S, 1 / (p : ℝ) := by
    simp only [S]
    rw [Finset.filter_image]
    rw [Finset.sum_image]
    intro a _ b _ h
    exact Subtype.ext h
  have hB : ∑ x ∈ u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ)), 1 / ((x : ℕ) : ℝ) ≤ L + 1 := by
    calc ∑ x ∈ u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ)), 1 / ((x : ℕ) : ℝ)
        ≤ ∑ x ∈ u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ)), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          have : (1 : ℝ) ≤ ((x : ℕ) : ℝ) := by exact_mod_cast x.2.one_lt.le
          rw [div_le_one (by linarith)]; exact this
      _ = (u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ))).card := by simp
      _ ≤ ((range (L + 1)).card : ℝ) := by
          have : (u.filter (fun p : Nat.Primes => ¬ L < (p : ℕ))).card ≤ (range (L + 1)).card := by
            refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ)) ?_ ?_
            · intro x hx
              simp only [coe_filter, Set.mem_setOf_eq] at hx
              simp only [coe_range, Set.mem_Iio]
              omega
            · intro a _ b _ h; exact Subtype.ext h
          exact_mod_cast this
      _ = L + 1 := by simp
  rw [hsplit, hA]
  linarith


lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    φ (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hpa : a.Prime := hS a (mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hpa (hs p hp)).2 (by rintro rfl; exact ha hp)
    rw [Nat.totient_mul hcop, Nat.totient_prime hpa, ih hs]

lemma totient_div_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (φ (∏ p ∈ S, p) : ℝ) = (∏ p ∈ S, (p : ℝ)) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  rw [totient_prod_primes S hS, ← Finset.prod_mul_distrib]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (hS p hp).one_lt.le
  have : (p : ℝ) ≠ 0 := by have := (hS p hp).pos; positivity
  rw [Nat.cast_sub hp1]
  field_simp
  push_cast; ring

lemma card_coprime_range_mul (P q : ℕ) :
    #{x ∈ range (P * q) | P.Coprime x} = q * φ P := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : range (P * (q + 1)) = range (P * q) ∪ Ico (P * q) (P * q + P) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega)
        (by omega)]
      rw [Nat.mul_succ]
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [ih, Nat.filter_coprime_Ico_eq_totient]; ring
    · apply Finset.disjoint_filter_filter
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive _ _ _

lemma card_coprime_range_le (P X : ℕ) (hP : 0 < P) :
    #{x ∈ range X | P.Coprime x} ≤ (X / P + 1) * φ P := by
  rw [← card_coprime_range_mul]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [mem_range] at hx ⊢
  have := Nat.lt_div_mul_add hP (a := X)
  nlinarith [Nat.div_add_mod X P, Nat.mod_lt X hP]

lemma card_coprime_range_le_real (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (X : ℕ) :
    (#{x ∈ range X | (∏ p ∈ S, p).Coprime x} : ℝ) ≤
      X * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + ∏ p ∈ S, (p : ℝ) := by
  set P := ∏ p ∈ S, p with hPdef
  have hP : 0 < P := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have h1 := card_coprime_range_le P X hP
  have h2 : (φ P : ℝ) = (P : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    rw [totient_div_prod_primes S hS, hPdef]; push_cast; ring
  have hprod_nonneg : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg; intro p hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
    linarith
  have hprod_le : ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      have : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
      linarith
    · intro p hp; have : (0:ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith
  have hPr : (P : ℝ) = ∏ p ∈ S, (p : ℝ) := by rw [hPdef]; push_cast; rfl
  have h3 : ((X / P : ℕ) : ℝ) * P ≤ X := by
    exact_mod_cast Nat.div_mul_le_self X P
  calc (#{x ∈ range X | P.Coprime x} : ℝ) ≤ ((X / P + 1) * φ P : ℕ) := by exact_mod_cast h1
    _ = ((X / P : ℕ) : ℝ) * P * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + P * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
        push_cast; rw [h2]; ring
    _ ≤ X * ∏ p ∈ S, (1 - 1 / (p : ℝ)) + P * 1 := by
        gcongr
    _ = _ := by rw [hPr]; ring


lemma two_pow_dvd_totient (k M : ℕ) (S : ℕ → Finset ℕ)
    (hodd : ∀ i < M, ∀ p ∈ S i, p.Prime ∧ 2 < p)
    (hdisj : ∀ i < M, ∀ j < M, i ≠ j → Disjoint (S i) (S j))
    (hrich : ∀ i < M, ∃ p ∈ S i, p ∣ k) : 2 ^ M ∣ φ k := by
  classical
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  choose! f hfS hfk using hrich
  have hinj : Set.InjOn f (range M : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    have := hdisj i hi j hj hne
    exact Finset.disjoint_left.mp this (hfS i hi) (hij ▸ hfS j hj)
  have hT : (range M).image f ⊆ k.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    rw [mem_range] at hi
    exact Nat.mem_primeFactors.mpr ⟨(hodd i hi _ (hfS i hi)).1, hfk i hi, hk⟩
  have h1 : 2 ^ M ∣ ∏ i ∈ range M, (f i - 1) := by
    rw [show 2 ^ M = ∏ i ∈ range M, 2 by simp]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    rw [mem_range] at hi
    obtain ⟨hp, h2⟩ := hodd i hi _ (hfS i hi)
    have hodd' : Odd (f i) := hp.odd_of_ne_two (by omega)
    obtain ⟨r, hr⟩ := hodd'
    exact ⟨r, by omega⟩
  have h2 : ∏ i ∈ range M, (f i - 1) = ∏ p ∈ (range M).image f, (p - 1) := by
    rw [Finset.prod_image]
    intro a ha b hb h; exact hinj ha hb h
  have h3 : ∏ p ∈ (range M).image f, (p - 1) ∣ ∏ p ∈ k.primeFactors, (p - 1) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hT
  have h4 : ∏ p ∈ k.primeFactors, (p - 1) ∣ φ k := by
    rw [Nat.totient_eq_prod_factorization hk, Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_dvd_prod_of_dvd
    intro p _
    exact Dvd.intro_left _ rfl
  rw [h2] at h1
  exact h1.trans (h3.trans h4)

lemma card_multiples_le (d X : ℕ) (hd : 0 < d) : #{v ∈ range X | d ∣ v} ≤ X / d + 1 := by
  calc #{v ∈ range X | d ∣ v} ≤ #(range (X / d + 1)) := by
        refine Finset.card_le_card_of_injOn (fun v => v / d) ?_ ?_
        · intro v hv
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hv
          simp only [coe_range, Set.mem_Iio]
          have := Nat.div_le_div_right (c := d) hv.1.le
          omega
        · intro a ha b hb h
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
          simp only at h
          rw [← Nat.div_mul_cancel ha.2, ← Nat.div_mul_cancel hb.2, h]
    _ = X / d + 1 := by simp

lemma card_image_totient_le (X M : ℕ) (S : ℕ → Finset ℕ)
    (hodd : ∀ i < M, ∀ p ∈ S i, p.Prime ∧ 2 < p)
    (hdisj : ∀ i < M, ∀ j < M, i ≠ j → Disjoint (S i) (S j)) :
    #((range X).image φ) ≤ #{v ∈ range X | 2 ^ M ∣ v} +
      ∑ i ∈ range M, #{x ∈ range X | (∏ p ∈ S i, p).Coprime x} := by
  classical
  have hsub : (range X).image φ ⊆ {v ∈ range X | 2 ^ M ∣ v} ∪
      (range M).biUnion (fun i => ({x ∈ range X | (∏ p ∈ S i, p).Coprime x}).image φ) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
    rw [mem_range] at hk
    by_cases hr : ∀ i < M, ∃ p ∈ S i, p ∣ k
    · apply mem_union_left
      simp only [mem_filter, mem_range]
      exact ⟨lt_of_le_of_lt (Nat.totient_le k) hk, two_pow_dvd_totient k M S hodd hdisj hr⟩
    · push_neg at hr
      obtain ⟨i, hi, hnd⟩ := hr
      apply mem_union_right
      simp only [mem_biUnion, mem_range, mem_image, mem_filter]
      refine ⟨i, hi, k, ⟨hk, ?_⟩, rfl⟩
      apply Nat.Coprime.prod_left
      intro p hp
      exact (Nat.Prime.coprime_iff_not_dvd (hodd i hi p hp).1).2 (hnd p hp)
  calc #((range X).image φ) ≤ #({v ∈ range X | 2 ^ M ∣ v} ∪
      (range M).biUnion (fun i => ({x ∈ range X | (∏ p ∈ S i, p).Coprime x}).image φ)) :=
        Finset.card_le_card hsub
    _ ≤ #{v ∈ range X | 2 ^ M ∣ v} +
      #((range M).biUnion (fun i => ({x ∈ range X | (∏ p ∈ S i, p).Coprime x}).image φ)) :=
        Finset.card_union_le _ _
    _ ≤ _ := by
        gcongr
        refine (Finset.card_biUnion_le).trans ?_
        apply Finset.sum_le_sum
        intro i _
        exact Finset.card_image_le


lemma exists_blocks {η : ℝ} (hη : 0 < η) : ∀ M : ℕ, ∃ S : ℕ → Finset ℕ, ∃ L : ℕ,
    (∀ i < M, ∀ p ∈ S i, p.Prime ∧ 2 < p ∧ p ≤ L) ∧
    (∀ i < M, ∀ j < M, i ≠ j → Disjoint (S i) (S j)) ∧
    (∀ i < M, ∏ p ∈ S i, (1 - 1 / (p : ℝ)) ≤ η) := by
  intro M
  induction M with
  | zero => exact ⟨fun _ => ∅, 0, by simp, by simp, by simp⟩
  | succ M ih =>
    obtain ⟨S, L, h1, h2, h3⟩ := ih
    obtain ⟨T, hT, hTprod⟩ := exists_primes_prod_small (max L 2) hη
    refine ⟨fun i => if i < M then S i else T, max (max L 2) (T.sup id), ?_, ?_, ?_⟩
    · intro i hi p hp
      by_cases him : i < M
      · simp only [him, if_true] at hp
        obtain ⟨a, b, c⟩ := h1 i him p hp
        exact ⟨a, b, le_trans c (le_trans (le_max_left _ _) (le_max_left _ _))⟩
      · simp only [him, if_false] at hp
        obtain ⟨a, b⟩ := hT p hp
        refine ⟨a, lt_of_le_of_lt (le_max_right _ _) b, ?_⟩
        exact le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)
    · intro i hi j hj hij
      by_cases him : i < M <;> by_cases hjm : j < M
      · simp only [him, hjm, if_true]; exact h2 i him j hjm hij
      · simp only [him, hjm, if_true, if_false]
        rw [Finset.disjoint_left]
        intro p hpS hpT
        have := (h1 i him p hpS).2.2
        have := (hT p hpT).2
        have := le_max_left L 2
        omega
      · simp only [him, hjm, if_true, if_false]
        rw [Finset.disjoint_left]
        intro p hpT hpS
        have := (h1 j hjm p hpS).2.2
        have := (hT p hpT).2
        have := le_max_left L 2
        omega
      · exfalso; omega
    · intro i hi
      by_cases him : i < M
      · simp only [him, if_true]; exact h3 i him
      · simp only [him, if_false]; exact hTprod

lemma card_image_totient_small {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ X : ℕ, (#((range X).image φ) : ℝ) ≤ 2 * η * X + K := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / η < 2 ^ M := pow_unbounded_of_one_lt _ (by norm_num)
  have hM' : (1 : ℝ) / 2 ^ M ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hM
    linarith
  have hδ : 0 < η / (M + 1) := by positivity
  obtain ⟨S, L, h1, h2, h3⟩ := exists_blocks hδ M
  refine ⟨1 + ∑ i ∈ range M, ∏ p ∈ S i, (p : ℝ), fun X => ?_⟩
  have hodd : ∀ i < M, ∀ p ∈ S i, p.Prime ∧ 2 < p := fun i hi p hp =>
    ⟨(h1 i hi p hp).1, (h1 i hi p hp).2.1⟩
  have hE := card_image_totient_le X M S hodd h2
  have hmul := card_multiples_le (2 ^ M) X (by positivity)
  have hmul' : (#{v ∈ range X | 2 ^ M ∣ v} : ℝ) ≤ η * X + 1 := by
    have : ((X / 2 ^ M : ℕ) : ℝ) ≤ (X : ℝ) / 2 ^ M := by
      have := Nat.cast_div_le (α := ℝ) (m := X) (n := 2 ^ M)
      simpa using this
    have h' : (X : ℝ) / 2 ^ M ≤ η * X := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hM' (by positivity)
    calc (#{v ∈ range X | 2 ^ M ∣ v} : ℝ) ≤ ((X / 2 ^ M + 1 : ℕ) : ℝ) := by exact_mod_cast hmul
      _ ≤ η * X + 1 := by push_cast; linarith
  have hsum : (∑ i ∈ range M, (#{x ∈ range X | (∏ p ∈ S i, p).Coprime x} : ℝ)) ≤
      ∑ i ∈ range M, (X * (η / (M + 1)) + ∏ p ∈ S i, (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [mem_range] at hi
    have := card_coprime_range_le_real (S i) (fun p hp => (h1 i hi p hp).1) X
    have := h3 i hi
    nlinarith [this, (show (0 : ℝ) ≤ X by positivity)]
  rw [Finset.sum_add_distrib, Finset.sum_const, card_range] at hsum
  have hMη : M • ((X : ℝ) * (η / (M + 1))) ≤ η * X := by
    rw [nsmul_eq_mul]
    have : (M : ℝ) / (M + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc (M : ℝ) * ((X : ℝ) * (η / (M + 1))) = (M / (M + 1)) * (η * X) := by ring
      _ ≤ 1 * (η * X) := by gcongr
      _ = η * X := by ring
  have hE' : (#((range X).image φ) : ℝ) ≤ (#{v ∈ range X | 2 ^ M ∣ v} : ℝ) +
      ∑ i ∈ range M, (#{x ∈ range X | (∏ p ∈ S i, p).Coprime x} : ℝ) := by
    exact_mod_cast hE
  linarith



lemma dvd_totient_mul_self (n : ℕ) (hn : 0 < n) : n ∣ φ (n * n) := by
  have h := Nat.totient_gcd_mul_totient_mul n n
  rw [Nat.gcd_self] at h
  have hpos : 0 < φ n := Nat.totient_pos.mpr hn
  have : φ (n * n) = φ n * n := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h]; ring
  rw [this]; exact Dvd.intro_left _ rfl

lemma m_spec (n : ℕ) (hn : 0 < n) : 0 < m n ∧ n ∣ φ (m n) := by
  unfold m
  exact Nat.sInf_mem (s := { k | 0 < k ∧ n ∣ totient k }) ⟨n * n, by positivity, dvd_totient_mul_self n hn⟩

lemma bad_count (C N : ℕ) :
    #{n ∈ range N | 0 < n ∧ m n < C * n} ≤ C * #((range (C * N)).image φ) := by
  classical
  have hsub : {n ∈ range N | 0 < n ∧ m n < C * n} ⊆
      (range C).biUnion (fun t => ((range (C * N)).image φ).image (· / t)) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    obtain ⟨hnN, hn0, hmC⟩ := hn
    obtain ⟨hk0, hdvd⟩ := m_spec n hn0
    obtain ⟨t, ht⟩ := hdvd
    have hphipos : 0 < φ (m n) := Nat.totient_pos.mpr hk0
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, mul_zero] at ht; omega
      · exact h
    have htC : t < C := by
      have h1 : n * t < n * C := by
        rw [← ht]
        calc φ (m n) ≤ m n := Nat.totient_le _
          _ < C * n := hmC
          _ = n * C := by ring
      exact Nat.lt_of_mul_lt_mul_left h1
    simp only [mem_biUnion, mem_range, mem_image]
    refine ⟨t, htC, φ (m n), ⟨m n, ?_, rfl⟩, ?_⟩
    · calc m n < C * n := hmC
        _ ≤ C * N := Nat.mul_le_mul_left _ hnN.le
    · rw [ht, Nat.mul_div_cancel _ htpos]
  calc #{n ∈ range N | 0 < n ∧ m n < C * n}
      ≤ #((range C).biUnion (fun t => ((range (C * N)).image φ).image (· / t))) :=
        Finset.card_le_card hsub
    _ ≤ ∑ t ∈ range C, #(((range (C * N)).image φ).image (· / t)) := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ range C, #((range (C * N)).image φ) := by
        apply Finset.sum_le_sum; intro t _; exact Finset.card_image_le
    _ = C * #((range (C * N)).image φ) := by simp

lemma bad_small (C : ℕ) : ∃ N0 : ℕ, ∀ N ≥ N0,
    (#{n ∈ range N | 0 < n ∧ m n < C * n} : ℝ) ≤ N / (C + 1) := by
  have hC : (0 : ℝ) < C + 1 := by positivity
  set η : ℝ := 1 / (4 * (C + 1) ^ 3) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨K, hK⟩ := card_image_totient_small hη
  refine ⟨⌈2 * (C + 1) * C * max K 0⌉₊, fun N hN => ?_⟩
  have hN' : 2 * (C + 1) * C * max K 0 ≤ N := by
    have := Nat.le_ceil (2 * (C + 1) * C * max K 0)
    exact this.trans (by exact_mod_cast hN)
  have h1 : (#{n ∈ range N | 0 < n ∧ m n < C * n} : ℝ) ≤ C * #((range (C * N)).image φ) := by
    exact_mod_cast bad_count C N
  have h2 := hK (C * N)
  push_cast at h2
  have hCle : (C : ℝ) ≤ C + 1 := by linarith
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hKle : K ≤ max K 0 := le_max_left _ _
  have key1 : (C : ℝ) * (2 * η * (C * N)) ≤ N / (2 * (C + 1)) := by
    have : (C : ℝ) * (2 * η * (C * N)) = (C * C) / (2 * (C + 1) ^ 3) * N := by
      rw [hη_def]; field_simp; ring
    rw [this]
    have hcc : (C : ℝ) * C ≤ (C + 1) ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (C : ℝ) * C * N * (2 * (C + 1)) ≤ (C + 1) ^ 2 * N * (2 * (C + 1)) := by
      have : 0 ≤ (N : ℝ) * (2 * (C + 1)) := by positivity
      nlinarith
    nlinarith
  have key2 : (C : ℝ) * K ≤ N / (2 * (C + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have : (C : ℝ) * K ≤ C * max K 0 := mul_le_mul_of_nonneg_left hKle hC0
    nlinarith
  calc (#{n ∈ range N | 0 < n ∧ m n < C * n} : ℝ) ≤ C * #((range (C * N)).image φ) := h1
    _ ≤ C * (2 * η * (C * N) + K) := mul_le_mul_of_nonneg_left h2 hC0
    _ = C * (2 * η * (C * N)) + C * K := by ring
    _ ≤ N / (2 * (C + 1)) + N / (2 * (C + 1)) := add_le_add key1 key2
    _ = N / (C + 1) := by field_simp; ring

open scoped Classical in
theorem main : ∃ A : Set ℕ, Tendsto (fun N ↦ (count (· ∈ A) N : ℝ) / N) atTop (nhds 1) ∧
      Tendsto (fun n ↦ (m n : ℝ) / (n : ℝ)) (atTop ⊓ Filter.principal A) atTop := by
  choose N0 hN0 using bad_small
  set N' : ℕ → ℕ := fun C => ∑ j ∈ range (C + 1), N0 j + C with hN'
  have hN'0 : ∀ C, N0 C ≤ N' C := by
    intro C
    have : N0 C ≤ ∑ j ∈ range (C + 1), N0 j :=
      Finset.single_le_sum (f := N0) (fun _ _ => Nat.zero_le _) (by simp)
    simp only [hN']; omega
  have hN'C : ∀ C, C ≤ N' C := by intro C; simp only [hN']; omega
  set A : Set ℕ := {n | ∀ C, N' C ≤ n → ¬ (0 < n ∧ m n < C * n)} with hA
  refine ⟨A, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨C0, hC0⟩ := exists_nat_one_div_lt hε
    refine ⟨max (N' C0) 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNC0 : N' C0 ≤ N := le_of_max_le_left hN
    set c := Nat.findGreatest (fun C => N' C ≤ N) N with hc
    have h0 : N' 0 ≤ N' C0 := by
      simp only [hN']
      have := Finset.sum_le_sum_of_subset (f := N0)
        (Finset.range_subset_range.2 (by omega : 0 + 1 ≤ C0 + 1))
      omega
    have hcspec : N' c ≤ N :=
      Nat.findGreatest_spec (P := fun C => N' C ≤ N) (Nat.zero_le N) (h0.trans hNC0)
    have hcC0 : C0 ≤ c := Nat.le_findGreatest (le_trans (hN'C C0) hNC0) hNC0
    have hcomp : #{n ∈ range N | n ∉ A} ≤ #{n ∈ range N | 0 < n ∧ m n < c * n} := by
      apply Finset.card_le_card
      intro n hn
      simp only [mem_filter, mem_range, hA, Set.mem_setOf_eq] at hn ⊢
      obtain ⟨hnN, hnA⟩ := hn
      push_neg at hnA
      obtain ⟨C, hCn, hpos, hlt⟩ := hnA
      have hCc : C ≤ c := Nat.le_findGreatest (by have := hN'C C; omega) (by omega)
      refine ⟨hnN, hpos, lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hCc)⟩
    have hbound := hN0 c N (le_trans (hN'0 c) hcspec)
    have hsplit : count (· ∈ A) N + #{n ∈ range N | n ∉ A} = N := by
      rw [Nat.count_eq_card_filter_range]
      have := Finset.card_filter_add_card_filter_not (s := range N) (fun n => n ∈ A)
      simpa using this
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hcomp' : (#{n ∈ range N | n ∉ A} : ℝ) ≤ N / (C0 + 1) := by
      have h1 : (#{n ∈ range N | n ∉ A} : ℝ) ≤ N / (c + 1) :=
        le_trans (by exact_mod_cast hcomp) hbound
      have h2 : (N : ℝ) / (c + 1) ≤ N / (C0 + 1) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : (C0 : ℝ) ≤ c := by exact_mod_cast hcC0
        linarith
      linarith
    have hcount : (count (· ∈ A) N : ℝ) = N - #{n ∈ range N | n ∉ A} := by
      have : ((count (· ∈ A) N + #{n ∈ range N | n ∉ A} : ℕ) : ℝ) = N := by
        exact_mod_cast hsplit
      push_cast at this; linarith
    rw [Real.dist_eq, hcount]
    have : ((N : ℝ) - #{n ∈ range N | n ∉ A}) / N - 1 = -(#{n ∈ range N | n ∉ A} / N) := by
      field_simp; ring
    rw [this, abs_neg, abs_of_nonneg (by positivity)]
    rw [div_lt_iff₀ hNpos]
    calc (#{n ∈ range N | n ∉ A} : ℝ) ≤ N / (C0 + 1) := hcomp'
      _ = 1 / (C0 + 1) * N := by ring
      _ < ε * N := by gcongr
  · rw [tendsto_atTop]
    intro b
    rw [eventually_inf_principal]
    set C := ⌈b⌉₊
    filter_upwards [eventually_ge_atTop (max (N' C) 1)] with n hn hnA
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnC : N' C ≤ n := le_of_max_le_left hn
    have h := hnA C hnC
    have hge : C * n ≤ m n := by
      by_contra hlt; push_neg at hlt; exact h ⟨hn1, hlt⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [le_div_iff₀ hnpos]
    calc b * n ≤ C * n := by gcongr; exact Nat.le_ceil b
      _ ≤ m n := by exact_mod_cast hge

end OMAErdos456

open scoped Classical in
theorem OMA.solution : type_of% @Erdos456.erdos_456.variants.m_div_n := by
  exact OMAErdos456.main
