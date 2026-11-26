import FormalConjectures.Wikipedia.EswarathasanLevineConjecture

/-!
# Proof of the Eswarathasan–Levine three-element inclusion theorem

For any prime `p ≥ 5`, we prove `{p - 1, p ^ 2 - p, p ^ 2 - 1} ⊆ harmonicNumDivisibleSet p`:
1. Every block `B(p, j) = ∑_{r=1}^{p-1} 1 / (j * p + r)` has reduced numerator divisible by `p`
   and denominator coprime to `p`, because `∑_{x : ZMod p} x⁻¹ = 0`.
2. Pairing `r` with `p - r` in `H_{p-1}` gives `2 * H_{p-1} = p * ∑_{r=1}^{p-1} 1 / (r * (p - r))`,
   and the remaining sum vanishes mod `p` since `∑_{x : ZMod p} x ^ 2 = 0` for `p ≥ 5`, proving
   Wolstenholme's theorem `p ^ 2 ∣ H_{p-1}.num`.
3. Decomposing `H_{p^2 - p} = H_{p-1} / p + ∑_{j=0}^{p-2} B(p, j)` and
   `H_{p^2 - 1} = H_{p^2 - p} + B(p, p - 1)` yields divisibility by `p` for all three indices.
-/

-- Problem: Eswarathasan–Levine conjectures on harmonic numerators — eswarathasan levine three elements subset
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/EswarathasanLevineConjecture.lean:84 (declaration EswarathasanLevineConjecture.eswarathasan_levine_three_elements_subset)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

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

open EswarathasanLevineConjecture EswarathasanLevineProof

theorem OMA.solution : type_of% @EswarathasanLevineConjecture.eswarathasan_levine_three_elements_subset := by
  intro p hp hp5 n hn
  have hwol : IsPDvd p 2 (harmonic (p - 1)) := isPDvd_two_harmonic_sub_one hp hp5
  have hp2_ge : p + 1 ≤ p ^ 2 := by nlinarith
  have hmul_id : (p - 1) * p = p ^ 2 - p := by
    have : 1 ≤ p := hp.pos
    zify [this, show p ≤ p ^ 2 by omega]
    ring
  have hp2p_dvd : IsPDvd p 1 (harmonic (p ^ 2 - p)) := by
    rw [← hmul_id, harmonic_mul_p hp (p - 1)]
    exact isPDvd_add hp (isPDvd_div_p hp hwol)
      (isPDvd_sum hp (Finset.range (p - 1)) (blockSum p) (fun j _ => isPDvd_blockSum hp hp5 j))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨by omega, isPDvd_dvd_num hp (isPDvd_one_of_two hwol)⟩
  · exact ⟨by omega, isPDvd_dvd_num hp hp2p_dvd⟩
  · refine ⟨by omega, ?_⟩
    have hsplit : p ^ 2 - 1 = (p ^ 2 - p) + (p - 1) := by omega
    have hharm : harmonic (p ^ 2 - 1) = harmonic (p ^ 2 - p) + blockSum p (p - 1) := by
      rw [hsplit, harmonic_add_eq]
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
      rw [hp1, ← hmul_id]
      rfl
    rw [hharm]
    exact isPDvd_dvd_num hp (isPDvd_add hp hp2p_dvd (isPDvd_blockSum hp hp5 (p - 1)))
