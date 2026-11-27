import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1

open Filter Topology

namespace OMAPerf

lemma sdiv_of_mem {n : ℕ} (h : ∑ d ∈ n.properDivisors, d = n) :
    ∑ d ∈ n.divisors, d = 2 * n := by
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, h]; ring

lemma geom_two (j : ℕ) : ∑ i ∈ Finset.range j, 2 ^ i + 1 = 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma geom_parity (p : ℕ) (hp : p % 2 = 1) (j : ℕ) :
    (∑ i ∈ Finset.range j, p ^ i) % 2 = j % 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, Nat.one_pow]
    omega

lemma sigma_split (n q : ℕ) (hn : n ≠ 0) (hq : q.Prime) :
    ∑ d ∈ n.divisors, d = (∑ d ∈ (q ^ n.factorization q).divisors, d) *
      ∑ d ∈ (n / q ^ n.factorization q).divisors, d := by
  have hcop : Nat.Coprime (q ^ n.factorization q) (n / q ^ n.factorization q) :=
    (Nat.coprime_ordCompl hq hn).pow_left _
  rw [← Nat.Coprime.sum_divisors_mul hcop, Nat.ordProj_mul_ordCompl_eq_self]

lemma even_sigma_pow {p v : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hv : v % 2 = 1) :
    2 ∣ ∑ d ∈ (p ^ v).divisors, d := by
  rw [Nat.sum_divisors_prime_pow hp]
  have := geom_parity p hp2 (v + 1)
  omega

/-- For odd `n`, a prime with odd exponent makes the divisor sum even, with the cofactor split. -/
lemma two_dvd_sigma {n q : ℕ} (hn : n ≠ 0) (hodd : n % 2 = 1) (hq : q.Prime)
    (hv : n.factorization q % 2 = 1) :
    2 ∣ ∑ d ∈ (q ^ n.factorization q).divisors, d := by
  apply even_sigma_pow hq _ hv
  have hqn : q ∣ n := by
    apply Nat.dvd_of_factorization_pos
    omega
  rcases Nat.even_or_odd q with he | ho
  · exfalso
    have : 2 ∣ n := dvd_trans (even_iff_two_dvd.1 he) hqn
    omega
  · exact Nat.odd_iff.1 ho

lemma exists_odd_exp {n : ℕ} (hn : n ≠ 0) (hsq : ¬ IsSquare n) :
    ∃ p, p.Prime ∧ n.factorization p % 2 = 1 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hsq
    exact ⟨b, by rw [← hab]; ring⟩
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  refine ⟨p, hp, ?_⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have h1 : a.factorization p = 1 := by
    have hle := ha.natFactorization_le_one p
    have hpos := hp.factorization_pos_of_dvd ha0 hpa
    omega
  rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0, Nat.factorization_pow]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega

lemma odd_perfect_form {n : ℕ} (hn : 0 < n) (hodd : n % 2 = 1)
    (hs : ∑ d ∈ n.divisors, d = 2 * n) :
    ∃ m p k : ℕ, p.Prime ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (m + 1)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hm; omega
      · exact h
    refine ⟨m, p, 0, hp, Nat.not_dvd_of_pos_of_lt hm0 (by omega), ?_⟩
    rw [hm]; ring
  · obtain ⟨p, hp, hv⟩ := exists_odd_exp hn.ne' hsq
    have hsplit := sigma_split n p hn.ne' hp
    have h2 := two_dvd_sigma hn.ne' hodd hp hv
    have hnr : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hpr : ¬ p ∣ n / p ^ n.factorization p := Nat.not_dvd_ordCompl hp hn.ne'
    generalize hr : n / p ^ n.factorization p = r at hsplit hnr hpr
    generalize hvv : n.factorization p = v at hsplit hnr h2 hv
    have hr0 : r ≠ 0 := by rintro rfl; simp at hnr; omega
    have hrodd : r % 2 = 1 := by
      rcases Nat.even_or_odd r with he | ho
      · exfalso
        have : 2 ∣ n := by
          rw [← hnr]; exact dvd_mul_of_dvd_right (even_iff_two_dvd.1 he) _
        omega
      · exact Nat.odd_iff.1 ho
    have hrsq : IsSquare r := by
      by_contra hrs
      obtain ⟨q, hq, hw⟩ := exists_odd_exp hr0 hrs
      have hsplit2 := sigma_split r q hr0 hq
      have h2' := two_dvd_sigma hr0 hrodd hq hw
      obtain ⟨x, hx⟩ := h2
      obtain ⟨y, hy⟩ := h2'
      rw [hsplit2, hx, hy] at hsplit
      rw [hs] at hsplit
      have : 2 ∣ n := ⟨x * y * ∑ d ∈ (r / q ^ r.factorization q).divisors, d, by
        have : 2 * n = 2 * (2 * (x * y * ∑ d ∈ (r / q ^ r.factorization q).divisors, d)) := by
          rw [hsplit]; ring
        omega⟩
      omega
    obtain ⟨m, hm⟩ := hrsq
    refine ⟨m, p, v, hp, ?_, ?_⟩
    · intro hpm
      apply hpr
      rw [hm]; exact dvd_mul_of_dvd_left hpm _
    · rw [← hnr, hm]; ring

lemma coprime_pow_sigma {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.Coprime (p ^ k) (∑ d ∈ (p ^ k).divisors, d) := by
  cases k with
  | zero => simp
  | succ k =>
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
    intro h
    have h1 : p ∣ ∑ i ∈ Finset.range (k + 1), p ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self p (by omega)
    have h2 : p ∣ p ^ 0 := (Nat.dvd_add_right h1).1 h
    rw [pow_zero] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

lemma hornfeck {p q k l m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m)
    (hm : 0 < m)
    (h1 : ∑ d ∈ (p ^ k * m ^ 2).divisors, d = 2 * (p ^ k * m ^ 2))
    (h2 : ∑ d ∈ (q ^ l * m ^ 2).divisors, d = 2 * (q ^ l * m ^ 2)) : p ^ k = q ^ l := by
  have hc1 : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hc2 : Nat.Coprime (q ^ l) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm)
  rw [Nat.Coprime.sum_divisors_mul hc1] at h1
  rw [Nat.Coprime.sum_divisors_mul hc2] at h2
  have hCpos : 0 < ∑ d ∈ (m ^ 2).divisors, d := by
    apply Finset.sum_pos
    · intro d hd
      exact Nat.pos_of_mem_divisors hd
    · exact ⟨1, Nat.one_mem_divisors.2 (by positivity)⟩
  have hcA := coprime_pow_sigma hp k
  have hcB := coprime_pow_sigma hq l
  generalize (∑ d ∈ (p ^ k).divisors, d) = A at h1 hcA
  generalize (∑ d ∈ (q ^ l).divisors, d) = B at h2 hcB
  generalize (∑ d ∈ (m ^ 2).divisors, d) = C at h1 h2 hCpos
  have key : A * q ^ l = B * p ^ k := by
    have : A * q ^ l * C = B * p ^ k * C := by
      calc A * q ^ l * C = (A * C) * q ^ l := by ring
        _ = 2 * (p ^ k * m ^ 2) * q ^ l := by rw [h1]
        _ = (2 * (q ^ l * m ^ 2)) * p ^ k := by ring
        _ = (B * C) * p ^ k := by rw [h2]
        _ = B * p ^ k * C := by ring
    exact Nat.eq_of_mul_eq_mul_right hCpos this
  have d1 : p ^ k ∣ q ^ l := by
    have : p ^ k ∣ A * q ^ l := ⟨B, by rw [key]; ring⟩
    exact hcA.dvd_of_dvd_mul_left this
  have d2 : q ^ l ∣ p ^ k := by
    have : q ^ l ∣ B * p ^ k := ⟨A, by rw [← key]; ring⟩
    exact hcB.dvd_of_dvd_mul_left this
  exact Nat.dvd_antisymm d1 d2

lemma even_perfect_form {n : ℕ} (hn : 0 < n) (h2 : 2 ∣ n)
    (hs : ∑ d ∈ n.divisors, d = 2 * n) :
    n = 2 ^ (n.factorization 2) * (2 ^ (n.factorization 2 + 1) - 1) := by
  have hnm : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  have hsplit := sigma_split n 2 hn.ne' Nat.prime_two
  have hkpos : 1 ≤ n.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn.ne' h2
  generalize n.factorization 2 = k at hnm hsplit hkpos ⊢
  generalize n / 2 ^ k = m at hnm hsplit
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, hs] at hsplit
  have hg := geom_two (k + 1)
  generalize (∑ i ∈ Finset.range (k + 1), 2 ^ i) = M at hsplit hg
  have h4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM3 : 3 ≤ M := by omega
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hnm; omega
    · exact h
  have h1 : M * (∑ d ∈ m.divisors, d) = (M + 1) * m := by
    rw [← hsplit, ← hnm, hg, pow_succ]; ring
  have hMm : M ∣ m := by
    have h : M ∣ (M + 1) * m := ⟨_, h1.symm⟩
    have hc : Nat.Coprime M (M + 1) := by simp
    exact hc.dvd_of_dvd_mul_left h
  obtain ⟨j, hj⟩ := hMm
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hj; omega
    · exact h
  have hS : ∑ d ∈ m.divisors, d = (M + 1) * j := by
    have : M * (∑ d ∈ m.divisors, d) = M * ((M + 1) * j) := by rw [h1, hj]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hj1 : j = 1 := by
    by_contra hne
    have hsub : ({1, j, m} : Finset ℕ) ⊆ m.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Nat.one_mem_divisors.2 hm0.ne'
      · exact Nat.mem_divisors.2 ⟨⟨M, by rw [hj]; ring⟩, hm0.ne'⟩
      · exact Nat.mem_divisors_self _ hm0.ne'
    have hle := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
    have hjm : j < m := by rw [hj]; nlinarith
    have hsum : ∑ d ∈ ({1, j, m} : Finset ℕ), d = 1 + j + m := by
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · ring
      · simp; omega
      · simp; omega
    rw [hsum, hS] at hle
    have : (M + 1) * j = m + j := by rw [hj]; ring
    omega
  subst hj1
  rw [← hnm, hj]
  have : M = 2 ^ (k + 1) - 1 := by omega
  rw [this]; ring

/-- The set of perfect numbers, as in the target. -/
lemma count_le (b : ℕ) :
    (({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.univ) ∩ Set.Iio b).ncard
      ≤ 2 * (Nat.sqrt b + 1) := by
  have H : ∀ n : ℕ, ∃ m : ℕ, (0 < n → n % 2 = 1 → ∑ d ∈ n.divisors, d = 2 * n →
      ∃ p k : ℕ, p.Prime ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2) := by
    intro n
    by_cases h : 0 < n ∧ n % 2 = 1 ∧ ∑ d ∈ n.divisors, d = 2 * n
    · obtain ⟨m, p, k, hp, hpm, hn⟩ := odd_perfect_form h.1 h.2.1 h.2.2
      exact ⟨m, fun _ _ _ => ⟨p, k, hp, hpm, hn⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose g hg using H
  set E : Set ℕ := {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n ∧ n < b ∧ 2 ∣ n} with hE
  set O : Set ℕ := {n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n ∧ n < b ∧ n % 2 = 1} with hO
  have hsub : (({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.univ) ∩ Set.Iio b) ⊆ E ∪ O := by
    intro n hn
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true, Set.mem_Iio] at hn
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · left; exact ⟨hn.1.1, hn.1.2, hn.2, Nat.dvd_of_mod_eq_zero h⟩
    · right; exact ⟨hn.1.1, hn.1.2, hn.2, h⟩
  have hT : ((Finset.range (Nat.sqrt b + 1) : Finset ℕ) : Set ℕ).ncard = Nat.sqrt b + 1 := by
    rw [Set.ncard_coe_finset, Finset.card_range]
  have hEc : E.ncard ≤ Nat.sqrt b + 1 := by
    rw [← hT]
    apply Set.ncard_le_ncard_of_injOn (fun n => 2 ^ n.factorization 2)
    · intro n hn
      obtain ⟨hn0, hnp, hnb, hn2⟩ := hn
      have hform := even_perfect_form hn0 hn2 (sdiv_of_mem hnp)
      simp only [Finset.coe_range, Set.mem_Iio]
      have h1 : 2 ^ n.factorization 2 ≤ Nat.sqrt n := by
        rw [Nat.le_sqrt']
        have : 2 ^ n.factorization 2 ≤ 2 ^ (n.factorization 2 + 1) - 1 := by
          rw [pow_succ]
          have := Nat.one_le_two_pow (n := n.factorization 2)
          omega
        calc (2 ^ n.factorization 2) ^ 2 = 2 ^ n.factorization 2 * 2 ^ n.factorization 2 := by ring
          _ ≤ 2 ^ n.factorization 2 * (2 ^ (n.factorization 2 + 1) - 1) :=
            Nat.mul_le_mul_left _ this
          _ = n := hform.symm
      have h2 : Nat.sqrt n ≤ Nat.sqrt b := Nat.sqrt_le_sqrt hnb.le
      omega
    · intro n hn n' hn' heq
      obtain ⟨hn0, hnp, hnb, hn2⟩ := hn
      obtain ⟨hn0', hnp', hnb', hn2'⟩ := hn'
      have hform := even_perfect_form hn0 hn2 (sdiv_of_mem hnp)
      have hform' := even_perfect_form hn0' hn2' (sdiv_of_mem hnp')
      simp only at heq
      have hk : n.factorization 2 = n'.factorization 2 := Nat.pow_right_injective le_rfl heq
      rw [hform, hform', hk]
  have hOc : O.ncard ≤ Nat.sqrt b + 1 := by
    rw [← hT]
    apply Set.ncard_le_ncard_of_injOn g
    · intro n hn
      obtain ⟨hn0, hnp, hnb, hn2⟩ := hn
      obtain ⟨p, k, hp, hpm, hform⟩ := hg n hn0 hn2 (sdiv_of_mem hnp)
      simp only [Finset.coe_range, Set.mem_Iio]
      have h1 : g n ≤ Nat.sqrt n := by
        rw [Nat.le_sqrt']
        calc (g n) ^ 2 = 1 * (g n) ^ 2 := by ring
          _ ≤ p ^ k * (g n) ^ 2 := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)
          _ = n := hform.symm
      have h2 : Nat.sqrt n ≤ Nat.sqrt b := Nat.sqrt_le_sqrt hnb.le
      omega
    · intro n hn n' hn' heq
      obtain ⟨hn0, hnp, hnb, hn2⟩ := hn
      obtain ⟨hn0', hnp', hnb', hn2'⟩ := hn'
      obtain ⟨p, k, hp, hpm, hform⟩ := hg n hn0 hn2 (sdiv_of_mem hnp)
      obtain ⟨q, l, hq, hqm, hform'⟩ := hg n' hn0' hn2' (sdiv_of_mem hnp')
      have hs1 := sdiv_of_mem hnp
      have hs2 := sdiv_of_mem hnp'
      rw [← heq] at hqm hform'
      have hm0 : 0 < g n := by
        rcases Nat.eq_zero_or_pos (g n) with h | h
        · rw [h] at hform; simp at hform; omega
        · exact h
      have hpq : p ^ k = q ^ l := by
        apply hornfeck hp hq hpm hqm hm0
        · rw [← hform]; exact hs1
        · rw [← hform']; exact hs2
      rw [hform, hform', hpq]
  calc (({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.univ) ∩ Set.Iio b).ncard
      ≤ (E ∪ O).ncard := by
        refine Set.ncard_le_ncard hsub (Set.Finite.subset (Set.finite_Iio b) ?_)
        intro n hn
        rcases hn with hn | hn
        · exact hn.2.2.1
        · exact hn.2.2.1
    _ ≤ E.ncard + O.ncard := Set.ncard_union_le E O
    _ ≤ 2 * (Nat.sqrt b + 1) := by omega

end OMAPerf

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H3 := by
  unfold OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H3 Set.HasDensity
  have hlim : Tendsto (fun b : ℕ => (4 : ℝ) / Real.sqrt (b : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (4 : ℝ))).div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun b => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with b hb
  have hden : (Set.univ ∩ Set.Iio b : Set ℕ).ncard = b := by
    rw [Set.univ_inter, ← Finset.coe_Iio, Set.ncard_coe_finset, Nat.card_Iio]
  have hnum := OMAPerf.count_le b
  simp only [Set.partialDensity]
  rw [hden]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hsq1 : (1 : ℝ) ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hb1
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt (by positivity)
  have hns : (Nat.sqrt b : ℝ) ≤ Real.sqrt b := Real.nat_sqrt_le_real_sqrt
  have hnum' : ((({n : ℕ | 0 < n ∧ ∑ d ∈ n.properDivisors, d = n} ∩ Set.univ) ∩
      Set.Iio b).ncard : ℝ) ≤ 2 * ((Nat.sqrt b : ℝ) + 1) := by exact_mod_cast hnum
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith
