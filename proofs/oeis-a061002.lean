import OMAStatements.S_oeis_a061002

/-!
# A061002: `denominator(H(p)/H(p-1)) = p^3 * numerator(H(p-1)/p^2)` for primes `p > 3`

Write `H m = ∑_{k=1}^{m} 1/k` and `H(p-1) = A/B` in lowest terms.

* `H p = H (p-1) + 1/p`, so `H p / H (p-1) = 1 + B/(pA) = (pA + B)/(pA)`.
* `p ∤ B` (a divisor of `B` dividing `p` would divide `A` too, but `A, B` are coprime),
  `p ∣ A`, and `A, B` are coprime, so `gcd(pA + B, pA) = 1`: the fraction is reduced and
  `denominator(H p / H (p-1)) = pA`.
* Wolstenholme's theorem (`p^2 ∣ A` for `p ≥ 5`) is what makes `H(p-1)/p^2 = (A/p^2)/B`
  reduced, with numerator `A/p^2`.  Hence the right side is `p^3 · A/p^2 = pA`.

The Wolstenholme input (`isPDvd_two_harmonic_sub_one`, `p ^ 2 ∣ H(p-1).num`) is reused from
the merged proof `proofs/EswarathasanLevineConjecture.eswarathasan_levine_three_elements_subset.lean`
by @TheWaler; its `IsPDvd` machinery is copied verbatim below.
-/

-- The section below, up to `end EswarathasanLevineProof`, is copied from @TheWaler's merged proof of
-- EswarathasanLevineConjecture.eswarathasan_levine_three_elements_subset.

namespace EswarathasanLevineProof

private def IsPDvd (p k : ℕ) (q : ℚ) : Prop :=
  ∃ N D : ℕ, ¬ p ∣ D ∧ p ^ k ∣ N ∧ q = (N : ℚ) / (D : ℚ)

private lemma isPDvd_zero {p k : ℕ} (hp : p.Prime) : IsPDvd p k 0 :=
  ⟨0, 1, hp.not_dvd_one, dvd_zero _, by simp⟩

private lemma isPDvd_add {p k : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvd p k q1) (h2 : IsPDvd p k q2) : IsPDvd p k (q1 + q2) := by
  rcases h1 with ⟨N1, D1, hD1, hN1, rfl⟩
  rcases h2 with ⟨N2, D2, hD2, hN2, rfl⟩
  have hD1_ne : (D1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hD1 (h ▸ dvd_zero p))
  have hD2_ne : (D2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hD2 (h ▸ dvd_zero p))
  refine ⟨N1 * D2 + N2 * D1, D1 * D2, fun h => (hp.dvd_mul.mp h).elim hD1 hD2,
    dvd_add (dvd_mul_of_dvd_left hN1 D2) (dvd_mul_of_dvd_left hN2 D1), ?_⟩
  push_cast
  field_simp

private lemma isPDvd_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsPDvd p k (f i)) : IsPDvd p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isPDvd_zero hp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPDvd_add hp (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isPDvd_one_of_two {p : ℕ} {q : ℚ} (h : IsPDvd p 2 q) : IsPDvd p 1 q := by
  rcases h with ⟨N, D, hD, hN, hq⟩
  exact ⟨N, D, hD, dvd_trans (by simp [pow_two]) hN, hq⟩

private lemma isPDvd_div_p {p : ℕ} (hp : p.Prime) {q : ℚ} (h : IsPDvd p 2 q) :
    IsPDvd p 1 (q / (p : ℚ)) := by
  rcases h with ⟨N, D, hD, ⟨M, rfl⟩, rfl⟩
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨p * M, D, hD, by simp [pow_one], ?_⟩
  push_cast
  field_simp

private lemma isPDvd_dvd_num {p : ℕ} (hp : p.Prime) {q : ℚ} (h : IsPDvd p 1 q) :
    (p : ℤ) ∣ q.num := by
  rcases h with ⟨N, D, hD, hN, hq⟩
  have hD_ne : D ≠ 0 := fun h0 => hD (h0 ▸ dvd_zero p)
  have hq_eq : (q.num : ℚ) / (q.den : ℚ) = (N : ℚ) / (D : ℚ) := by
    rw [q.num_div_den, hq]
  have hmul_q : (q.num : ℚ) * (D : ℚ) = (N : ℚ) * (q.den : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr q.den_nz) (Nat.cast_ne_zero.mpr hD_ne)).mp hq_eq
  have hmul_z : q.num * (D : ℤ) = (N : ℤ) * (q.den : ℤ) := by
    exact_mod_cast hmul_q
  have hpN : (p : ℤ) ∣ (N : ℤ) := Int.ofNat_dvd.mpr (by simpa using hN)
  have hp_mul : (p : ℤ) ∣ q.num * (D : ℤ) := by
    rw [hmul_z]
    exact dvd_mul_of_dvd_left hpN (q.den : ℤ)
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hp_int.dvd_or_dvd hp_mul with h1 | h2
  · exact h1
  · exact absurd (Int.ofNat_dvd.mp h2) hD

private lemma rat_inv_sum_eq_div {ι : Type*} [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (s : Finset ι) (b : ι → ℕ) (hb : ∀ i ∈ s, ¬ p ∣ b i) :
    ∃ N D : ℕ, ¬ p ∣ D ∧
      (∑ i ∈ s, ((b i : ℕ) : ℚ)⁻¹) = (N : ℚ) / (D : ℚ) ∧
      (N : ZMod p) = (D : ZMod p) * ∑ i ∈ s, ((b i : ℕ) : ZMod p)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨∑ i ∈ s, ∏ j ∈ s.erase i, b j, ∏ i ∈ s, b i, ?_, ?_, ?_⟩
  · intro h
    rcases (hp.prime.dvd_finsetProd_iff _).mp h with ⟨i, hi, hbi⟩
    exact hb i hi hbi
  · have hD_ne : (∏ i ∈ s, b i : ℕ) ≠ 0 := by
      intro h0
      rcases Finset.prod_eq_zero_iff.mp h0 with ⟨i, hi, hbi⟩
      exact hb i hi (hbi ▸ dvd_zero p)
    rw [eq_div_iff (Nat.cast_ne_zero.mpr hD_ne), Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbi_ne : (b i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hb i hi (h0 ▸ dvd_zero p))
    rw [← Finset.mul_prod_erase s (fun j => (b j : ℚ)) hi, inv_mul_cancel_left₀ hbi_ne]
  · rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hbi_ne : ((b i : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      exact hb i hi ((ZMod.natCast_eq_zero_iff (b i) p).mp h0)
    rw [← Finset.mul_prod_erase s (fun j => ((b j : ℕ) : ZMod p)) hi, mul_comm ((b i : ℕ) : ZMod p),
      mul_assoc, mul_inv_cancel₀ hbi_ne, mul_one]

private lemma sum_Ico_zmod_eq_univ {p : ℕ} [Fact p.Prime] (f : ZMod p → ZMod p) (hf0 : f 0 = 0) :
    ∑ r ∈ Finset.Ico 1 p, f (r : ZMod p) = ∑ x : ZMod p, f x := by
  have hp : p.Prime := Fact.out
  have hrange : ∑ r ∈ Finset.range p, f (r : ZMod p) = ∑ x : ZMod p, f x := by
    refine Finset.sum_nbij (fun r : ℕ => (r : ZMod p)) ?_ ?_ ?_ ?_
    · intro r _
      exact Finset.mem_univ _
    · intro r1 hr1 r2 hr2 heq
      have h1 : r1 < p := Finset.mem_range.mp hr1
      have h2 : r2 < p := Finset.mem_range.mp hr2
      have hval := congr_arg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _
      rfl
  rw [← hrange, ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hp.pos]
  simp [hf0]

private lemma zmod_sum_inv_eq_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hneg : ∑ x : ZMod p, (-x)⁻¹ = ∑ x : ZMod p, x⁻¹ :=
    Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x⁻¹)
  have hneg2 : ∑ x : ZMod p, (-x)⁻¹ = -∑ x : ZMod p, x⁻¹ := by
    simp [inv_neg, Finset.sum_neg_distrib]
  have hsum_zero : (2 : ZMod p) * ∑ x : ZMod p, x⁻¹ = 0 := by
    have hEq : -∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x⁻¹ := hneg2.symm.trans hneg
    calc
      (2 : ZMod p) * ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x⁻¹ + ∑ x : ZMod p, x⁻¹ := by ring
      _ = ∑ x : ZMod p, x⁻¹ + -∑ x : ZMod p, x⁻¹ := by rw [hEq]
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hsum_zero).resolve_left h2

private lemma zmod_sum_sq_inv_eq_zero {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, (x ^ 2)⁻¹ = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h0)
    have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsq : ∑ x : ZMod p, x ^ 2 = 0 := by
    have hbij : ∑ x : ZMod p, ((2 : ZMod p) * x) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
      Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2) (fun x => x ^ 2)
    have h4 : ∑ x : ZMod p, ((2 : ZMod p) * x) ^ 2 = (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      norm_num
    have hmul : (3 : ZMod p) * ∑ x : ZMod p, x ^ 2 = 0 := by
      have hEq : (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 = ∑ x : ZMod p, x ^ 2 := h4.symm.trans hbij
      calc
        (3 : ZMod p) * ∑ x : ZMod p, x ^ 2 =
            (4 : ZMod p) * ∑ x : ZMod p, x ^ 2 - ∑ x : ZMod p, x ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr hEq
    exact (mul_eq_zero.mp hmul).resolve_left h3
  have hinv_eq : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    simp [inv_pow]
  rw [hinv_eq]
  have hinv_bij : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 2)
  rw [hinv_bij, hsq]

private def blockSum (p j : ℕ) : ℚ :=
  ∑ r ∈ Finset.Ico 1 p, ((j * p + r : ℕ) : ℚ)⁻¹

private lemma isPDvd_blockSum {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
    IsPDvd p 1 (blockSum p j) := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : ∀ r ∈ Finset.Ico 1 p, ¬ p ∣ (j * p + r) := by
    intro r hr h
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrp : r < p := (Finset.mem_Ico.mp hr).2
    have hpr : p ∣ r := (Nat.dvd_add_right (dvd_mul_left p j)).mp h
    exact absurd (Nat.le_of_dvd (by omega) hpr) (by omega)
  rcases rat_inv_sum_eq_div hp (Finset.Ico 1 p) (fun r => j * p + r) hb with ⟨N, D, hD, hEq, hZ⟩
  have hsum_z : ∑ r ∈ Finset.Ico 1 p, ((j * p + r : ℕ) : ZMod p)⁻¹ = 0 := by
    have hsimp : ∑ r ∈ Finset.Ico 1 p, ((j * p + r : ℕ) : ZMod p)⁻¹ =
        ∑ r ∈ Finset.Ico 1 p, ((r : ℕ) : ZMod p)⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro r _
      simp
    rw [hsimp, sum_Ico_zmod_eq_univ (fun x : ZMod p => x⁻¹) inv_zero]
    exact zmod_sum_inv_eq_zero hp5
  rw [hsum_z, mul_zero] at hZ
  have hpN : p ∣ N := (ZMod.natCast_eq_zero_iff N p).mp hZ
  exact ⟨N, D, hD, by simpa using hpN, hEq⟩

private lemma harmonic_add_eq (a b : ℕ) :
    harmonic (a + b) = harmonic a + ∑ r ∈ Finset.Ico 1 (b + 1), ((a + r : ℕ) : ℚ)⁻¹ := by
  induction b with
  | zero =>
    simp
  | succ b ih =>
    have htop := Finset.sum_Ico_succ_top (a := 1) (b := b + 1) (by omega)
      (f := fun r => ((a + r : ℕ) : ℚ)⁻¹)
    rw [← Nat.add_assoc, harmonic_succ, ih, htop]
    push_cast
    ring

private lemma harmonic_sub_one_eq_blockSum_zero {p : ℕ} (hp : p.Prime) :
    harmonic (p - 1) = blockSum p 0 := by
  have h := harmonic_add_eq 0 (p - 1)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  simpa [harmonic, blockSum, hp1] using h

private lemma isPDvd_two_harmonic_sub_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsPDvd p 2 (harmonic (p - 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hrev : ∑ r ∈ Finset.Ico 1 p, ((p - r : ℕ) : ℚ)⁻¹ = ∑ r ∈ Finset.Ico 1 p, (r : ℚ)⁻¹ := by
    refine Finset.sum_nbij (fun r => p - r) ?_ ?_ ?_ ?_
    · intro r hr
      rcases Finset.mem_Ico.mp hr with ⟨h1, h2⟩
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro r1 hr1 r2 hr2 heq
      dsimp only at heq
      rcases Finset.mem_Ico.mp hr1 with ⟨_, h1⟩
      rcases Finset.mem_Ico.mp hr2 with ⟨_, h2⟩
      omega
    · intro r hr
      rcases Finset.mem_Ico.mp hr with ⟨h1, h2⟩
      refine ⟨p - r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      dsimp only
      omega
    · intro _ _
      rfl
  have hpair : (2 : ℚ) * harmonic (p - 1) =
      (p : ℚ) * ∑ r ∈ Finset.Ico 1 p, ((r * (p - r) : ℕ) : ℚ)⁻¹ := by
    rw [harmonic_sub_one_eq_blockSum_zero hp]
    unfold blockSum
    simp only [zero_mul, zero_add]
    have h2 : (2 : ℚ) * ∑ r ∈ Finset.Ico 1 p, (r : ℚ)⁻¹ =
        ∑ r ∈ Finset.Ico 1 p, ((r : ℚ)⁻¹ + ((p - r : ℕ) : ℚ)⁻¹) := by
      rw [Finset.sum_add_distrib, hrev]
      ring
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rcases Finset.mem_Ico.mp hr with ⟨h1, h2⟩
    have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpr_ne : ((p - r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hadd : (r : ℚ) + ((p - r : ℕ) : ℚ) = (p : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le (by omega : r ≤ p)
    rw [Nat.cast_mul]
    field_simp
    linarith
  have hb : ∀ r ∈ Finset.Ico 1 p, ¬ p ∣ r * (p - r) := by
    intro r hr h
    rcases Finset.mem_Ico.mp hr with ⟨h1, h2⟩
    rcases hp.dvd_mul.mp h with hr1 | hr2
    · exact absurd (Nat.le_of_dvd (by omega) hr1) (by omega)
    · exact absurd (Nat.le_of_dvd (by omega) hr2) (by omega)
  rcases rat_inv_sum_eq_div hp (Finset.Ico 1 p) (fun r => r * (p - r)) hb with ⟨N, D, hD, hEq, hZ⟩
  have hsum_z : ∑ r ∈ Finset.Ico 1 p, ((r * (p - r) : ℕ) : ZMod p)⁻¹ = 0 := by
    have hsimp : ∑ r ∈ Finset.Ico 1 p, ((r * (p - r) : ℕ) : ZMod p)⁻¹ =
        -∑ r ∈ Finset.Ico 1 p, (((r : ℕ) : ZMod p) ^ 2)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro r hr
      rcases Finset.mem_Ico.mp hr with ⟨_, h2⟩
      have hcast : ((r * (p - r) : ℕ) : ZMod p) = -(((r : ℕ) : ZMod p) ^ 2) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : r ≤ p), ZMod.natCast_self]
        ring
      rw [hcast, inv_neg]
    rw [hsimp, sum_Ico_zmod_eq_univ (fun x : ZMod p => (x ^ 2)⁻¹) (by simp),
      zmod_sum_sq_inv_eq_zero hp5, neg_zero]
  rw [hsum_z, mul_zero] at hZ
  have hpN : p ∣ N := (ZMod.natCast_eq_zero_iff N p).mp hZ
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  refine ⟨p * N, 2 * D, fun h => (hp.dvd_mul.mp h).elim hp2 hD, ?_, ?_⟩
  · rcases hpN with ⟨M, rfl⟩
    exact ⟨M, by ring⟩
  · have hEq' : (2 : ℚ) * harmonic (p - 1) = (p : ℚ) * ((N : ℚ) / (D : ℚ)) := by
      rw [hpair, hEq]
    push_cast
    linarith [show ((p : ℚ) * (N : ℚ)) / ((2 : ℚ) * (D : ℚ)) =
        ((p : ℚ) * ((N : ℚ) / (D : ℚ))) / 2 by ring,
      show harmonic (p - 1) = ((2 : ℚ) * harmonic (p - 1)) / 2 by ring]

private lemma harmonic_mul_p {p : ℕ} (hp : p.Prime) (m : ℕ) :
    harmonic (m * p) = harmonic m / (p : ℚ) + ∑ j ∈ Finset.range m, blockSum p j := by
  induction m with
  | zero =>
    simp [harmonic]
  | succ m ih =>
    rw [add_mul, one_mul, harmonic_add_eq, ih, Finset.sum_Ico_succ_top hp.pos,
      Finset.sum_range_succ, harmonic_succ, add_div]
    change harmonic m / (p : ℚ) + ∑ j ∈ Finset.range m, blockSum p j +
        (blockSum p m + ((m * p + p : ℕ) : ℚ)⁻¹) =
      harmonic m / (p : ℚ) + ((m + 1 : ℕ) : ℚ)⁻¹ / (p : ℚ) +
        (∑ j ∈ Finset.range m, blockSum p j + blockSum p m)
    have hterm : ((m * p + p : ℕ) : ℚ)⁻¹ = ((m + 1 : ℕ) : ℚ)⁻¹ / (p : ℚ) := by
      have hnat : m * p + p = (m + 1) * p := by ring
      rw [hnat, Nat.cast_mul, mul_inv, div_eq_mul_inv]
    rw [hterm]
    ring

end EswarathasanLevineProof
namespace OMA.S_oeis_a061002

open EswarathasanLevineProof

/-- `H` is Mathlib's harmonic number. -/
lemma H_eq_harmonic (m : ℕ) : H m = harmonic m := by
  simp [H, harmonic_eq_sum_Icc]

private lemma ipdvd_dvd_num {p k : ℕ} (hp : p.Prime) {qq : ℚ} (h : IsPDvd p k qq) :
    (p : ℤ) ^ k ∣ qq.num := by
  rcases h with ⟨N, D, hD, hN, hq⟩
  have hD_ne : D ≠ 0 := fun h0 => hD (h0 ▸ dvd_zero p)
  have hq_eq : (qq.num : ℚ) / (qq.den : ℚ) = (N : ℚ) / (D : ℚ) := by
    rw [qq.num_div_den, hq]
  have hmul_q : (qq.num : ℚ) * (D : ℚ) = (N : ℚ) * (qq.den : ℚ) :=
    (div_eq_div_iff (Nat.cast_ne_zero.mpr qq.den_nz) (Nat.cast_ne_zero.mpr hD_ne)).mp hq_eq
  have hmul_z : qq.num * (D : ℤ) = (N : ℤ) * (qq.den : ℤ) := by exact_mod_cast hmul_q
  have hpN : (p : ℤ) ^ k ∣ (N : ℤ) := by
    have h1 : ((p ^ k : ℕ) : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN
    simpa using h1
  have hdvd : (p : ℤ) ^ k ∣ qq.num * (D : ℤ) := by
    rw [hmul_z]; exact dvd_mul_of_dvd_left hpN _
  have hcop_nat : Nat.Coprime (p ^ k) D := ((hp.coprime_iff_not_dvd).mpr hD).pow_left k
  have hcop : IsCoprime ((p : ℤ) ^ k) (D : ℤ) := by
    have h2 : IsCoprime (((p ^ k : ℕ) : ℤ)) ((D : ℤ)) := hcop_nat.isCoprime
    simpa using h2
  exact hcop.dvd_of_dvd_mul_right hdvd

private lemma rat_eq_mkRat (N : ℤ) (D : ℕ) : ((N : ℚ) / (D : ℚ)) = mkRat N D := by
  have h1 : ((D : ℚ)) = (((D : ℤ)) : ℚ) := by push_cast; ring
  rw [h1, ← Rat.divInt_eq_div N (D : ℤ)]
  rfl

private lemma den_div_of_coprime {N : ℤ} {D : ℕ} (hD : D ≠ 0) (h : N.natAbs.Coprime D) :
    ((((N : ℚ) / (D : ℚ))).den) = D := by
  rw [rat_eq_mkRat, Rat.den_mkRat]
  simp [hD, h.symm.gcd_eq_one]

private lemma num_div_of_coprime {N : ℤ} {D : ℕ} (hD : D ≠ 0) (h : N.natAbs.Coprime D) :
    ((((N : ℚ) / (D : ℚ))).num) = N := by
  rw [rat_eq_mkRat, Rat.num_mkRat]
  simp [hD, h.symm.gcd_eq_one]

theorem key : ∀ p : ℕ, p.Prime → 3 < p →
    ((H p / H (p - 1)).den : ℤ) = (p : ℤ) ^ 3 * (H (p - 1) / (p : ℚ) ^ 2).num := by
  intro p hp hp3
  have hp5 : 5 ≤ p := by
    have hne : p ≠ 4 := by
      intro h4; rw [h4] at hp; norm_num at hp
    omega
  rw [H_eq_harmonic, H_eq_harmonic]
  set q := harmonic (p - 1) with hq
  set A : ℤ := q.num with hA
  set B : ℕ := q.den with hB
  have hqpos : 0 < q := by rw [hq]; exact harmonic_pos (by omega : p - 1 ≠ 0)
  have hB0 : B ≠ 0 := by rw [hB]; exact q.den_nz
  have hred : A.natAbs.Coprime B := by rw [hA, hB]; exact q.reduced
  have hqA : q = (A : ℚ) / (B : ℚ) := by
    rw [hA, hB]; exact (Rat.num_div_den q).symm
  have hApos : 0 < A := by
    have h1 : (A : ℚ) = q * (B : ℚ) := by rw [hqA]; field_simp
    have h2 : (0 : ℚ) < (A : ℚ) := by rw [h1]; positivity
    exact_mod_cast h2
  have hwol : IsPDvd p 2 q := by rw [hq]; exact isPDvd_two_harmonic_sub_one hp hp5
  have hA2 : (p : ℤ) ^ 2 ∣ A := by rw [hA]; exact ipdvd_dvd_num hp hwol
  obtain ⟨Ap, hAp⟩ := hA2
  have hpA : (p : ℤ) ∣ A := ⟨(p : ℤ) * Ap, by rw [hAp]; ring⟩
  have hpAn : p ∣ A.natAbs := by
    have h1 : (p : ℤ) ∣ (A.natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg hApos.le]; exact hpA
    exact Int.ofNat_dvd.mp h1
  have hpB : ¬ p ∣ B := by
    intro h
    have h1 : p ∣ Nat.gcd A.natAbs B := Nat.dvd_gcd hpAn h
    rw [hred.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  -- `H p = q + 1/p`
  have hHp : harmonic p = q + (p : ℚ)⁻¹ := by
    have h1 := harmonic_succ (p - 1)
    rw [Nat.sub_add_cancel hp.pos] at h1
    exact h1
  have hpApos : (0 : ℤ) < p * A := by
    have h1 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
    positivity
  -- coprimality of `p * A + B` and `p * A`
  have hnat : Nat.Coprime (p * A.natAbs + B) (p * A.natAbs) := by
    have hP : Nat.Coprime (p * A.natAbs + B) p :=
      (Nat.coprime_mul_left_add_left B p A.natAbs).mpr ((hp.coprime_iff_not_dvd).mpr hpB).symm
    have ha : Nat.Coprime (p * A.natAbs + B) A.natAbs := by
      have h' : Nat.Coprime (B + A.natAbs * p) A.natAbs :=
        (Nat.coprime_add_mul_left_left B A.natAbs p).mpr hred.symm
      rwa [mul_comm A.natAbs p, add_comm] at h'
    exact hP.mul_right ha
  have hAcast : A = ((A.natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hApos.le).symm
  have hpAcast : p * A = ((p * A.natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_mul, hAcast, Int.natAbs_natCast]
  have hNcast : p * A + (B : ℤ) = ((p * A.natAbs + B : ℕ) : ℤ) := by
    rw [Int.natCast_add, hpAcast]
  have htoNat : (p * A).toNat = p * A.natAbs := by
    rw [hpAcast, Int.toNat_natCast]
  have hcopPA : (p * A + (B : ℤ)).natAbs.Coprime ((p * A).toNat) := by
    rw [hNcast, htoNat, Int.natAbs_natCast]
    exact hnat
  have hPA : (((p * A).toNat : ℕ) : ℚ) = (p : ℚ) * (A : ℚ) := by
    have h1 : (((p * A).toNat : ℕ) : ℤ) = p * A := Int.toNat_of_nonneg hpApos.le
    calc (((p * A).toNat : ℕ) : ℚ) = ((((p * A).toNat : ℕ) : ℤ) : ℚ) := by push_cast; ring
      _ = ((p * A : ℤ) : ℚ) := by rw [h1]
      _ = (p : ℚ) * (A : ℚ) := by push_cast; ring
  have hr : harmonic p / q = ((p * A + (B : ℤ) : ℤ) : ℚ) / (((p * A).toNat : ℕ) : ℚ) := by
    rw [hHp, hqA, hPA]
    have hAq : (A : ℚ) ≠ 0 := by positivity
    have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB0
    have hpq : (p : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hPA0 : (p * A).toNat ≠ 0 := by
    intro h0
    have h1 : (((p * A).toNat : ℕ) : ℤ) = 0 := by rw [h0]; simp
    rw [Int.toNat_of_nonneg hpApos.le] at h1
    exact hpApos.ne' h1
  have hden : (harmonic p / q).den = (p * A).toNat := by
    rw [hr]
    exact den_div_of_coprime hPA0 hcopPA
  -- the numerator on the right
  have hnd : A.natAbs = p ^ 2 * Ap.natAbs := by
    rw [hAp, Int.natAbs_mul]
    simp
  have hdvdA : Ap.natAbs ∣ A.natAbs := ⟨p ^ 2, by rw [hnd, mul_comm]⟩
  have hcopAp : Ap.natAbs.Coprime B := hred.coprime_dvd_left hdvdA
  have hqdiv : q / (p : ℚ) ^ 2 = ((Ap : ℤ) : ℚ) / (B : ℚ) := by
    rw [hqA, hAp]
    have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB0
    have hpq : (p : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hnumR : (q / (p : ℚ) ^ 2).num = Ap := by
    rw [hqdiv]
    exact num_div_of_coprime hB0 hcopAp
  rw [hden, hnumR]
  have hcast : (((p * A).toNat : ℕ) : ℤ) = p * A := Int.toNat_of_nonneg hpApos.le
  rw [hcast]
  have hpA3 : p * A = (p : ℤ) ^ 3 * Ap := by rw [hAp]; ring
  rw [hpA3]

end OMA.S_oeis_a061002

theorem OMA.solution : type_of% @OMA.S_oeis_a061002.main := by
  intro p hp hp3
  exact OMA.S_oeis_a061002.key p hp hp3
