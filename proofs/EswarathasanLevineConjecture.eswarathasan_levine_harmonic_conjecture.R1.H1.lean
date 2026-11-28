import OMAReductions.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1

/-!
# Proof of `EswarathasanLevineConjecture.eswarathasan_levine_harmonic_conjecture.R1.H1`

Proves that `EswarathasanLevineConjecture.harmonicNumDivisibleSet p` is finite for every prime
`p < 7` (i.e., `p ∈ {2, 3, 5}`).

Key `p`-adic recurrence: for any prime `p`, `m ≥ 1`, and `r < p`,
`harmonic (p * m + r) = (1 / p) * harmonic m + S`, where `S = ∑_{k ∈ Icc 1 (p*m+r), ¬ p ∣ k} 1 / k`
has denominator coprime to `p`. If `¬ (p : ℤ) ∣ (harmonic m).num`, then writing
`harmonic m = a / b` in lowest terms (so `p ∤ a`) and `S = c / d` (with `p ∤ d`) yields
`harmonic (p * m + r) = (a * d + p * b * c) / (p * b * d)`, whose numerator is congruent to
`a * d ≢ 0 (mod p)`, so `¬ (p : ℤ) ∣ (harmonic (p * m + r)).num`.

By strong induction on `n` and kernel verification of the finitely many base cases (`n = 1` for
`p = 2`; `n ∈ {1, 6, 8, 21, 23, 66, 67, 68}` for `p = 3`;
`n ∈ {1, 2, 3, 21, 22, 23, 100..104, 120..124}` for `p = 5`), we obtain:
- `J_2 = ∅`,
- `J_3 ⊆ {2, 7, 22}`,
- `J_5 ⊆ {4, 20, 24}`,
each of which is finite.
-/

namespace EswarathasanLevineR1H1Proof

open Finset

private lemma harmonic_eq_sum_Icc (n : ℕ) :
    harmonic n = ∑ k ∈ Icc 1 n, ((k : ℚ))⁻¹ := by
  unfold harmonic
  refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]; omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]; omega
  · intro i _; omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro i _
    simp [Nat.cast_add, Nat.cast_one]

private lemma harmonic_split (p m r : ℕ) (hp : 0 < p) (hr : r < p) :
    harmonic (p * m + r) =
      ((p : ℚ))⁻¹ * harmonic m +
      ∑ k ∈ (Icc 1 (p * m + r)).filter (fun k => ¬ p ∣ k), ((k : ℚ))⁻¹ := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 (p * m + r)) (fun k => p ∣ k)]
  congr 1
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun j => p * j) (fun k => k / p) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right p j⟩
    · nlinarith
    · nlinarith
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Finset.mem_Icc]
    obtain ⟨j, rfl⟩ := hk.2
    rw [Nat.mul_div_cancel_left j hp]
    constructor
    · by_contra h0; have : j = 0 := by omega
      subst this; omega
    · by_contra hgt
      have hge : m + 1 ≤ j := by omega
      have : p * (m + 1) ≤ p * j := Nat.mul_le_mul_left p hge
      rw [Nat.mul_add, mul_one] at this
      omega
  · intro j _
    exact Nat.mul_div_cancel_left j hp
  · intro k hk
    rw [Finset.mem_filter] at hk
    exact Nat.mul_div_cancel' hk.2
  · intro j _
    rw [Nat.cast_mul, mul_inv]

private lemma not_dvd_den_sum_coprime {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 0 < k ∧ ¬ p ∣ k) :
    ∃ (c : ℤ) (d : ℕ), 0 < d ∧ ¬ p ∣ d ∧
      (∑ k ∈ s, ((k : ℚ))⁻¹) = (c : ℚ) / (d : ℚ) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 1, by decide, ?_, by simp⟩
    intro hd; have := Nat.le_of_dvd (by decide) hd; have := hp.two_le; omega
  | insert a t hat ih =>
    have ha := hs a (Finset.mem_insert_self a t)
    obtain ⟨c, d, hdpos, hdndvd, hsum⟩ := ih fun k hk => hs k (Finset.mem_insert_of_mem hk)
    refine ⟨(d : ℤ) + (a : ℤ) * c, a * d, Nat.mul_pos ha.1 hdpos, ?_, ?_⟩
    · intro hdiv
      rcases hp.dvd_mul.mp hdiv with h1 | h2
      · exact ha.2 h1
      · exact hdndvd h2
    · rw [Finset.sum_insert hat, hsum]
      have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.1.ne'
      have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
      push_cast
      field_simp [haq, hdq]

private lemma not_dvd_num_of_rat_eq {p : ℕ} (hp : p.Prime) {q : ℚ} {num : ℤ} {den : ℕ}
    (hden : 0 < den) (heq : q = (num : ℚ) / (den : ℚ))
    (hnum : ¬ (p : ℤ) ∣ num) : ¬ (p : ℤ) ∣ q.num := by
  intro hdvd
  have hqden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hdenq : (den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hden.ne'
  have hmulQ : (q.num : ℚ) * (den : ℚ) = (num : ℚ) * (q.den : ℚ) := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (num : ℚ) / (den : ℚ) := q.num_div_den.trans heq
    field_simp [hqden, hdenq] at h1
    exact h1.trans (mul_comm _ _)
  have hmulZ : q.num * (den : ℤ) = num * (q.den : ℤ) := by exact_mod_cast hmulQ
  have hprimeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd_rhs : (p : ℤ) ∣ num * (q.den : ℤ) := by
    rw [← hmulZ]
    exact dvd_mul_of_dvd_left hdvd _
  rcases hprimeZ.dvd_or_dvd hdvd_rhs with h1 | h2
  · exact hnum h1
  · have hp_den : p ∣ q.den := Int.ofNat_dvd.mp h2
    have hp_num_abs : p ∣ q.num.natAbs := Int.ofNat_dvd_left.mp hdvd
    have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
    have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hp_num_abs hp_den
    have := Nat.le_of_dvd (by decide) hp1
    have := hp.two_le
    omega

private lemma not_dvd_num_harmonic_child {p m r : ℕ} (hp : p.Prime) (hr : r < p)
    (hnot : ¬ (p : ℤ) ∣ (harmonic m).num) :
    ¬ (p : ℤ) ∣ (harmonic (p * m + r)).num := by
  rw [harmonic_split p m r hp.pos hr]
  obtain ⟨c, d, hdpos, hdndvd, hS⟩ := not_dvd_den_sum_coprime hp
    ((Icc 1 (p * m + r)).filter (fun k => ¬ p ∣ k))
    (fun k hk => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      exact ⟨by omega, hk.2⟩)
  rw [hS]
  set q := harmonic m
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
  have hcomb : ((p : ℚ))⁻¹ * q + (c : ℚ) / (d : ℚ) =
      (((q.num * (d : ℤ) + (p : ℤ) * (q.den : ℤ) * c : ℤ) : ℚ)) /
        (((p * q.den * d : ℕ) : ℚ)) := by
    conv_lhs => rw [hq]
    have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hqdq : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    push_cast
    field_simp [hpq, hqdq, hdq]
  have hden_pos : 0 < p * q.den * d := Nat.mul_pos (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero q.den_nz)) hdpos
  apply not_dvd_num_of_rat_eq hp hden_pos hcomb
  intro hdvd_sum
  have hprimeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd_p : (p : ℤ) ∣ (p : ℤ) * (q.den : ℤ) * c := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hdvd_ad : (p : ℤ) ∣ q.num * (d : ℤ) := (dvd_add_left hdvd_p).mp hdvd_sum
  rcases hprimeZ.dvd_or_dvd hdvd_ad with h1 | h2
  · exact hnot h1
  · exact hdndvd (Int.ofNat_dvd.mp h2)

-- Fast computable harmonic number in ℚ for kernel verification of the 25 small base cases
private def harmRec : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmRec n + ((n + 1 : ℚ))⁻¹

private lemma harmRec_eq (n : ℕ) : harmRec n = harmonic n := by
  induction n with
  | zero => simp [harmRec, harmonic]
  | succ n ih =>
    rw [harmRec, ih, harmonic_succ]
    simp [Nat.cast_add, Nat.cast_one]

private lemma base_p2 : ¬ ((2 : ℤ) ∣ (harmRec 1).num) := by decide +kernel

private lemma base_p3 :
    ∀ n ∈ ([1, 6, 8, 21, 23, 66, 67, 68] : List ℕ), ¬ ((3 : ℤ) ∣ (harmRec n).num) := by
  decide +kernel

private lemma base_p5 :
    ∀ n ∈ ([1, 2, 3, 21, 22, 23, 100, 101, 102, 103, 104, 120, 121, 122, 123, 124] : List ℕ),
      ¬ ((5 : ℤ) ∣ (harmRec n).num) := by
  decide +kernel

private lemma p2_all (n : ℕ) (hn : 1 ≤ n) : ¬ (2 : ℤ) ∣ (harmonic n).num := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1; rw [← harmRec_eq]; exact base_p2
    · have hm : 1 ≤ n / 2 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have heq : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
      rw [← heq]
      exact not_dvd_num_harmonic_child Nat.prime_two (Nat.mod_lt n (by decide)) (ih (n / 2) hlt hm)

private lemma p3_subset (n : ℕ) (hn : 1 ≤ n) (hnot : n ∉ ({2, 7, 22} : Finset ℕ)) :
    ¬ (3 : ℤ) ∣ (harmonic n).num := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hbase : ∀ k ∈ ([1, 6, 8, 21, 23, 66, 67, 68] : List ℕ), ¬ (3 : ℤ) ∣ (harmonic k).num := by
      intro k hk; rw [← harmRec_eq]; exact base_p3 k hk
    by_cases hmem : n ∈ ([1, 6, 8, 21, 23, 66, 67, 68] : List ℕ)
    · exact hbase n hmem
    · set m := n / 3
      set r := n % 3
      have hr : r < 3 := Nat.mod_lt n (by decide)
      have heq : 3 * m + r = n := Nat.div_add_mod n 3
      have hm1 : 1 ≤ m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
        omega
      have hmlt : m < n := Nat.div_lt_self (by omega) (by decide)
      have hm_not : m ∉ ({2, 7, 22} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
        omega
      rw [← heq]
      exact not_dvd_num_harmonic_child Nat.prime_three hr (ih m hmlt hm1 hm_not)

private lemma p5_subset (n : ℕ) (hn : 1 ≤ n) (hnot : n ∉ ({4, 20, 24} : Finset ℕ)) :
    ¬ (5 : ℤ) ∣ (harmonic n).num := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hbase : ∀ k ∈ ([1, 2, 3, 21, 22, 23, 100, 101, 102, 103, 104, 120, 121, 122, 123, 124] : List ℕ),
        ¬ (5 : ℤ) ∣ (harmonic k).num := by
      intro k hk; rw [← harmRec_eq]; exact base_p5 k hk
    by_cases hmem : n ∈ ([1, 2, 3, 21, 22, 23, 100, 101, 102, 103, 104, 120, 121, 122, 123, 124] : List ℕ)
    · exact hbase n hmem
    · set m := n / 5
      set r := n % 5
      have hr : r < 5 := Nat.mod_lt n (by decide)
      have heq : 5 * m + r = n := Nat.div_add_mod n 5
      have hm1 : 1 ≤ m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
        omega
      have hmlt : m < n := Nat.div_lt_self (by omega) (by decide)
      have hm_not : m ∉ ({4, 20, 24} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hmem
        omega
      rw [← heq]
      exact not_dvd_num_harmonic_child (by decide : Nat.Prime 5) hr (ih m hmlt hm1 hm_not)

end EswarathasanLevineR1H1Proof

theorem OMA.solution : OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1.H1 := by
  intro p hp hlt
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
    have := hp.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by decide)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hp (by decide)
  rcases hcases with rfl | rfl | rfl
  · refine Set.finite_empty.subset ?_
    rintro n ⟨hn, hdvd⟩
    exact absurd hdvd (EswarathasanLevineR1H1Proof.p2_all n hn)
  · refine (({2, 7, 22} : Finset ℕ).finite_toSet).subset ?_
    rintro n ⟨hn, hdvd⟩
    by_contra hnot
    exact EswarathasanLevineR1H1Proof.p3_subset n hn hnot hdvd
  · refine (({4, 20, 24} : Finset ℕ).finite_toSet).subset ?_
    rintro n ⟨hn, hdvd⟩
    by_contra hnot
    exact EswarathasanLevineR1H1Proof.p5_subset n hn hnot hdvd
