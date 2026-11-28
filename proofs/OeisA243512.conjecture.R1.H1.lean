import OMAReductions.R_OeisA243512_conjecture_R1

/-!
# Proof of `OeisA243512.conjecture.R1.H1`

Proves that for every prime `p`, `OeisA243512.a (p + 1) ≠ 0`, and if `5 ≤ p` then
`OeisA243512.a ((p + 3) / 2) ≠ 0`.

- For `i = p ^ 2`, `σ(p ^ 2) = 1 + p + p ^ 2` is coprime to `p ^ 2`, giving
  `abundancyDiff (p ^ 2) = p + 1`.
- For `i = 2 * p` with `p ≥ 5` prime, `σ(2 * p) = 3 * (p + 1)` and `p + 1` is even, so
  `σ(2 * p) / (2 * p) = (3 * ((p + 1) / 2)) / p` in lowest terms, giving
  `abundancyDiff (2 * p) = (p + 3) / 2`.
- In either case, the set `{i | 0 < i ∧ abundancyDiff i = n}` is nonempty, so its infimum
  `OeisA243512.a n` lies in the set and is therefore strictly positive.
-/

namespace OeisA243512R1H1Proof

private lemma a_ne_zero_of_witness {n i : ℕ} (hi : 0 < i) (h : OeisA243512.abundancyDiff i = n) :
    OeisA243512.a n ≠ 0 := by
  have hne : ({j : ℕ | 0 < j ∧ OeisA243512.abundancyDiff j = n}).Nonempty := ⟨i, hi, h⟩
  have hmem := Nat.sInf_mem hne
  exact Nat.ne_of_gt hmem.1

private lemma rat_num_den_of_eq_div {r : ℚ} {a b : ℕ} (hb : 0 < b) (hcop : a.Coprime b)
    (hr : r = (a : ℚ) / (b : ℚ)) : r.num = (a : ℤ) ∧ r.den = b := by
  have hden_pos : 0 < r.den := r.pos
  have hq : (r.num : ℚ) / (r.den : ℚ) = (a : ℚ) / (b : ℚ) := by
    rw [Rat.num_div_den, hr]
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  have hd0 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hden_pos)
  have hmul_q : (r.num : ℚ) * (b : ℚ) = (a : ℚ) * (r.den : ℚ) := by
    field_simp [hb0, hd0] at hq
    linarith
  have hmul_z : r.num * (b : ℤ) = (a : ℤ) * (r.den : ℤ) := by
    exact_mod_cast hmul_q
  have hnum_nonneg : 0 ≤ r.num := by
    have hprod_nonneg : 0 ≤ r.num * (b : ℤ) := by
      rw [hmul_z]
      positivity
    have hb_z : (0 : ℤ) < (b : ℤ) := Int.natCast_pos.mpr hb
    nlinarith
  have hmul_n : r.num.natAbs * b = a * r.den := by
    have h2 : ((r.num.natAbs * b : ℕ) : ℤ) = ((a * r.den : ℕ) : ℤ) := by
      push_cast
      rw [abs_of_nonneg hnum_nonneg]
      exact hmul_z
    exact_mod_cast h2
  have hcop_r : r.num.natAbs.Coprime r.den := r.reduced
  have hd_dvd_b : r.den ∣ b :=
    hcop_r.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
  have hb_dvd_d : b ∣ r.den :=
    hcop.symm.dvd_of_dvd_mul_left ⟨r.num.natAbs, by linarith⟩
  have hden_eq : r.den = b := Nat.dvd_antisymm hd_dvd_b hb_dvd_d
  have hnum_abs_eq : r.num.natAbs = a := by
    rw [hden_eq] at hmul_n
    exact Nat.eq_of_mul_eq_mul_right hb hmul_n
  refine ⟨?_, hden_eq⟩
  have h1 : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hnum_nonneg
  rw [← h1, hnum_abs_eq]

private lemma sum_divisors_prime_sq {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ (p ^ 2).divisors, d = 1 + p + p ^ 2 := by
  have hdiv : (p ^ 2).divisors = {1, p, p ^ 2} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    constructor
    · rintro ⟨hdvd, _⟩
      rw [Nat.dvd_prime_pow hp] at hdvd
      rcases hdvd with ⟨k, hk, rfl⟩
      interval_cases k
      · left; simp
      · right; left; simp
      · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨one_dvd _, hp2⟩
      · exact ⟨⟨d, by ring⟩, hp2⟩
      · exact ⟨dvd_refl _, hp2⟩
  rw [hdiv]
  have h1p : (1 : ℕ) ≠ p := Nat.ne_of_lt hp.one_lt
  have h1p2 : (1 : ℕ) ≠ p ^ 2 := by nlinarith [hp.one_lt]
  have hpp2 : p ≠ p ^ 2 := by nlinarith [hp.one_lt]
  rw [Finset.sum_insert (by simp [h1p, h1p2]), Finset.sum_insert (by simp [hpp2]),
    Finset.sum_singleton]
  ring

private lemma sum_divisors_two_mul_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ d ∈ (2 * p).divisors, d = 3 * (p + 1) := by
  have hdiv : (2 * p).divisors = {1, 2, p, 2 * p} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    have h2p : 2 * p ≠ 0 := by omega
    constructor
    · rintro ⟨hdvd, _⟩
      by_cases h2 : 2 ∣ d
      · obtain ⟨k, rfl⟩ := h2
        have hkp : k ∣ p := (mul_dvd_mul_iff_left (by omega : (2 : ℕ) ≠ 0)).mp hdvd
        rcases hp.eq_one_or_self_of_dvd k hkp with rfl | rfl
        · right; left; rfl
        · right; right; right; rfl
      · have hcop : Nat.Coprime d 2 :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2 |>.symm
        have hdp : d ∣ p := hcop.dvd_of_dvd_mul_left hdvd
        rcases hp.eq_one_or_self_of_dvd d hdp with rfl | rfl
        · left; rfl
        · right; right; left; rfl
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨one_dvd _, h2p⟩
      · exact ⟨⟨p, rfl⟩, h2p⟩
      · exact ⟨⟨2, by ring⟩, h2p⟩
      · exact ⟨dvd_refl _, h2p⟩
  rw [hdiv]
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  ring

private lemma abundancyDiff_prime_sq {p : ℕ} (hp : p.Prime) :
    OeisA243512.abundancyDiff (p ^ 2) = p + 1 := by
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hp2_ne : p ^ 2 ≠ 0 := Nat.ne_of_gt hp2_pos
  unfold OeisA243512.abundancyDiff
  rw [if_neg hp2_ne]
  have hsum_z : (∑ d ∈ (p ^ 2).divisors, (d : ℤ)) = ((1 + p + p ^ 2 : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, sum_divisors_prime_sq hp]
  dsimp only
  rw [hsum_z]
  have hcop_p : (1 + p + p ^ 2).Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have h1 : p ∣ 1 := by
      have : p ∣ p + p ^ 2 := ⟨1 + p, by ring⟩
      have hsub := Nat.dvd_sub hdvd this
      simpa [show 1 + p + p ^ 2 - (p + p ^ 2) = 1 by omega] using hsub
    exact hp.not_dvd_one h1
  have hcop : (1 + p + p ^ 2).Coprime (p ^ 2) := hcop_p.pow_right 2
  set r : ℚ := mkRat ((1 + p + p ^ 2 : ℕ) : ℤ) (p ^ 2)
  have hr : r = ((1 + p + p ^ 2 : ℕ) : ℚ) / ((p ^ 2 : ℕ) : ℚ) := by
    simp [r, Rat.mkRat_eq_div]
  obtain ⟨hnum, hden⟩ := rat_num_den_of_eq_div hp2_pos hcop hr
  rw [hnum, hden]
  have hdiff : ((1 + p + p ^ 2 : ℕ) : ℤ) - ((p ^ 2 : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [hdiff, Int.toNat_natCast]

private lemma abundancyDiff_two_mul_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    OeisA243512.abundancyDiff (2 * p) = (p + 3) / 2 := by
  have h2p_ne : 2 * p ≠ 0 := by omega
  unfold OeisA243512.abundancyDiff
  rw [if_neg h2p_ne]
  have hsum_z : (∑ d ∈ (2 * p).divisors, (d : ℤ)) = ((3 * (p + 1) : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, sum_divisors_two_mul_prime hp h5]
  dsimp only
  rw [hsum_z]
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  set k := (p + 1) / 2
  have hk_eq : 2 * k = p + 1 := by omega
  have hcop3 : (3 : ℕ).Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcopk : k.Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcop : (3 * k).Coprime p := hcop3.mul_left hcopk
  set r : ℚ := mkRat ((3 * (p + 1) : ℕ) : ℤ) (2 * p)
  have hr : r = ((3 * k : ℕ) : ℚ) / (p : ℚ) := by
    simp only [r, Rat.mkRat_eq_div]
    have hq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hke : (2 : ℚ) * (k : ℚ) = (p : ℚ) + 1 := by exact_mod_cast hk_eq
    push_cast
    field_simp [hq]
    linarith
  obtain ⟨hnum, hden⟩ := rat_num_den_of_eq_div hp.pos hcop hr
  rw [hnum, hden]
  have hdiff : ((3 * k : ℕ) : ℤ) - (p : ℤ) = (((p + 3) / 2 : ℕ) : ℤ) := by
    have hnat : 3 * k = p + (p + 3) / 2 := by omega
    have hcast : ((3 * k : ℕ) : ℤ) = (p : ℤ) + (((p + 3) / 2 : ℕ) : ℤ) := by exact_mod_cast hnat
    linarith
  rw [hdiff, Int.toNat_natCast]

end OeisA243512R1H1Proof

theorem OMA.solution : OMA.R_OeisA243512_conjecture_R1.H1 := by
  intro p hp
  refine ⟨?_, ?_⟩
  · exact OeisA243512R1H1Proof.a_ne_zero_of_witness (pow_pos hp.pos 2)
      (OeisA243512R1H1Proof.abundancyDiff_prime_sq hp)
  · intro h5
    exact OeisA243512R1H1Proof.a_ne_zero_of_witness (by omega)
      (OeisA243512R1H1Proof.abundancyDiff_two_mul_prime hp h5)
