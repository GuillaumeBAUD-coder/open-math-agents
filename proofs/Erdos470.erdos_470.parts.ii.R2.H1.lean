import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

-- Divisor-sum and maximal-proper-divisor lemmas adapted from @biondadave's
-- proof of Erdos470.erdos_470.variants.prime_gap_imp_inf_prim_weird.
namespace OMA.WeirdCriterion

open Finset

-- The divisors of 2^k sum to 2^(k+1) - 1.
lemma sum_divisors_two_pow (k : ℕ) : ∑ d ∈ (2 ^ k).divisors, d + 1 = 2 ^ (k + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

lemma coprime_two_pow_of_prime {k r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : Nat.Coprime (2 ^ k) r :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))

-- sigma(2^k * r) for an odd prime r.
lemma sum_divisors_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∑ d ∈ (2 ^ k * r).divisors, d + (r + 1) = 2 ^ (k + 1) * (r + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (coprime_two_pow_of_prime hr hr2), Nat.Prime.sum_divisors hr]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- sigma(2^k * p * q) for distinct odd primes p, q.
lemma sum_divisors_two_pow_mul_mul (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d + (p + 1) * (q + 1) = 2 ^ (k + 1) * ((p + 1) * (q + 1)) := by
  have hcop1 : Nat.Coprime (2 ^ k) (p * q) :=
    Nat.Coprime.mul_right (coprime_two_pow_of_prime hp hp2) (coprime_two_pow_of_prime hq hq2)
  have hcop2 : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [mul_assoc, Nat.Coprime.sum_divisors_mul hcop1, Nat.Coprime.sum_divisors_mul hcop2,
    Nat.Prime.sum_divisors hp, Nat.Prime.sum_divisors hq]
  have h := sum_divisors_two_pow k
  rw [← h]
  ring

-- 2^k * r is not abundant when r is an odd prime with 2^(k+1) <= r + 1.
lemma not_abundant_two_pow_mul_prime (k r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hbig : 2 ^ (k + 1) ≤ r + 1) : ¬ (2 ^ k * r).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_prime k r hr hr2
  have h2 : 2 * (2 ^ k * r) = 2 ^ (k + 1) * r := by ring
  rw [h2]
  nlinarith

-- 2^j * p * q is not abundant when p, q are distinct odd primes, both at least 2^(j+2).
lemma not_abundant_two_pow_mul_mul (j p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (hpbig : 2 ^ (j + 2) ≤ p) (hqbig : 2 ^ (j + 2) ≤ q) :
    ¬ (2 ^ j * p * q).Abundant := by
  rw [Nat.abundant_iff_sum_divisors, not_lt]
  have h := sum_divisors_two_pow_mul_mul j p q hp hq hp2 hq2 hpq
  set m := 2 ^ (j + 1) with hm
  have h2 : 2 * (2 ^ j * p * q) = m * (p * q) := by rw [hm]; ring
  have h4 : 2 ^ (j + 2) = 2 * m := by rw [hm]; ring
  rw [h2]
  obtain ⟨u, rfl⟩ : ∃ u, p = 2 * m + u := ⟨p - 2 * m, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, q = 2 * m + v := ⟨q - 2 * m, by omega⟩
  nlinarith [Nat.zero_le (u * v), Nat.zero_le (m * u), Nat.zero_le (m * v), Nat.zero_le m]

-- A proper divisor of 2^k * p * q divides one of the three maximal proper divisors.
lemma dvd_cases (k p q d : ℕ) (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hd : d ∈ (2 ^ k * p * q).properDivisors) :
    d ∣ 2 ^ (k - 1) * p * q ∨ d ∣ 2 ^ k * q ∨ d ∣ 2 ^ k * p := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨⟨e, he⟩, hlt⟩ := hd
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at he
    omega
  have hen : e ∣ 2 ^ k * p * q := ⟨d, by rw [he]; ring⟩
  have hr := Nat.minFac_prime he1
  have hrn : e.minFac ∣ 2 ^ k * p * q := (Nat.minFac_dvd e).trans hen
  have hre := Nat.minFac_dvd e
  generalize e.minFac = r at hr hrn hre
  obtain ⟨e', rfl⟩ := hre
  rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      left
      refine ⟨e', ?_⟩
      have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2, hk'] at he
      have : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * e') := by rw [← mul_assoc, ← mul_assoc, he]; ring
      omega
    · have h2 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      right; left
      refine ⟨e', ?_⟩
      rw [h2] at he
      have : p * (2 ^ k * q) = p * (d * e') := by linarith [he]
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
  · have h2 := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
    right; right
    refine ⟨e', ?_⟩
    rw [h2] at he
    have : q * (2 ^ k * p) = q * (d * e') := by linarith [he]
    exact Nat.eq_of_mul_eq_mul_left hq.pos this

end OMA.WeirdCriterion

open OMA.WeirdCriterion

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := by
  intro k p q hp hq hpM hqM hpq hpos hsmall hmod
  set M := 2 ^ (k + 1) with hM
  have hM2 : 2 ≤ M := Nat.le_self_pow (by omega) 2
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hk : 1 ≤ k := by
    by_contra! h
    have hk0 : k = 0 := by omega
    have hm : M = 2 := by simp [hM, hk0]
    rw [hm] at hpos
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (show 3 ≤ p by omega)
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (show 3 ≤ q by omega)
    rw [ha, hb] at hpos
    norm_num at hpos
    nlinarith
  set n := 2 ^ k * p * q with hn
  set S := (M - 1) * (p + 1) * (q + 1) with hS
  have hdbl : 2 * n = M * p * q := by rw [hn, hM]; ring
  have hσ : ∑ d ∈ n.divisors, d = S := by
    have h := sum_divisors_two_pow_mul_mul k p q hp hq hp2 hq2 hpq
    have hs : M - 1 + 1 = M := by omega
    apply Nat.add_right_cancel (m := (p + 1) * (q + 1))
    calc
      _ = M * ((p + 1) * (q + 1)) := h
      _ = S + (p + 1) * (q + 1) := by
        dsimp only [S]
        conv_lhs => rw [← hs]
        ring
  refine ⟨⟨Nat.abundant_iff_sum_divisors.mpr (by omega), ?_⟩, ?_⟩
  · rintro ⟨-, s, hs, hsum⟩
    let t := n.properDivisors \ s
    have hsd := Finset.sum_sdiff hs (f := fun x => x)
    have hpd := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
    have hT : ∑ d ∈ t, d = S - M * p * q := by dsimp [t]; omega
    have hTq : ∑ d ∈ t, d < q := by omega
    have sub : t.filter (fun d => ¬ p ∣ d) ⊆ (2 ^ k).divisors := by
      intro d hd
      obtain ⟨hdt, hnp⟩ := Finset.mem_filter.mp hd
      have hdn := Nat.properDivisors_subset_divisors (Finset.sdiff_subset hdt)
      have hdpos := Nat.pos_of_mem_divisors hdn
      have hle := Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hdt
      have hnq : ¬ q ∣ d := fun h => (by omega : d < q).not_ge (Nat.le_of_dvd hdpos h)
      have cp := ((hp.coprime_iff_not_dvd).mpr hnp).symm
      have cq := ((hq.coprime_iff_not_dvd).mpr hnq).symm
      exact Nat.mem_divisors.mpr
        ⟨cp.dvd_of_dvd_mul_right (cq.dvd_of_dvd_mul_right (Nat.dvd_of_mem_divisors hdn)), by positivity⟩
    have bound := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) sub
    have binary := sum_divisors_two_pow k
    have hdiv : p ∣ ∑ d ∈ t.filter (fun d => p ∣ d), d :=
      Finset.dvd_sum fun _ hd => (Finset.mem_filter.mp hd).2
    have hsplit := Finset.sum_filter_add_sum_filter_not t (fun d => p ∣ d) (fun d => d)
    rw [← hT, ← hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  · -- primitive: every proper divisor is non-abundant
    intro d hd hw
    have hab := hw.1
    rcases dvd_cases k p q d hk hp hq hd with h | h | h
    · have hk' : k - 1 + 2 = k + 1 := by omega
      have hnot := not_abundant_two_pow_mul_mul (k - 1) p q hp hq hp2 hq2 hpq
        (by rw [hk', ← hM]; omega) (by rw [hk', ← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h
        (Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) hp.ne_zero) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k q hq hq2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hq.ne_zero))
    · have hnot := not_abundant_two_pow_mul_prime k p hp hp2 (by rw [← hM]; omega)
      exact hnot (Nat.Abundant.of_dvd hab h (Nat.mul_ne_zero (by positivity) hp.ne_zero))

