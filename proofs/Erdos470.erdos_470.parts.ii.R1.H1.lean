import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1
import Mathlib.Tactic

/-!
# Proof of H1 for Erdos Problem 470 part ii (Melfi 2015, Theorem 1)
-/

private lemma sum_divisors_two_pow (m : ℕ) :
    ∑ d ∈ (2 ^ m).divisors, d = 2 ^ (m + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq (by norm_num) (m + 1)]
  omega

private lemma odd_of_prime_gt_two {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) : p % 2 = 1 := by
  by_contra h
  have hdvd : 2 ∣ p := by omega
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2 <;> omega

private lemma coprime_two_pow_of_prime_gt_two (m : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (2 ^ m).Coprime p := by
  refine (Nat.prime_two.coprime_iff_not_dvd.mpr ?_).pow_left m
  intro hdvd
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2 <;> omega

private lemma melfi_sigma_identity {N a b r p q : ℕ}
    (hN1 : 1 ≤ N) (ha : a = b + 4 + 2 * r) (ha_le : a ≤ 2 * N)
    (hp : p = 2 * N - a) (hq : q = 2 * N + b) :
    (N - 1) * (p + 1) * (q + 1) =
      N * p * q + (N * (2 * r + 1) + (a - 1) * (b + 1)) := by
  have ha1 : 1 ≤ a := by omega
  rw [hp, hq]
  zify [hN1, ha1, ha_le]
  rw [show (a : ℤ) = (b : ℤ) + 4 + 2 * (r : ℤ) by exact_mod_cast ha]
  ring

private lemma delta_not_in_block {N a b r p q h : ℕ}
    (ha : a = b + 4 + 2 * r) (hsize : a * (a + b) < 2 * N)
    (hp : p + a = 2 * N) (hq : q = 2 * N + b)
    (hlow : h * p ≤ N * (2 * r + 1) + (a - 1) * (b + 1))
    (hhigh : N * (2 * r + 1) + (a - 1) * (b + 1) < h * q + N) : False := by
  rcases le_or_gt h r with hle | hgt
  · have h1 : N * (2 * h + 1) ≤ N * (2 * r + 1) :=
      Nat.mul_le_mul_left N (by omega)
    have hh_le_a1 : h ≤ a - 1 := by omega
    have h2 : h * b < (a - 1) * (b + 1) := by
      calc
        h * b ≤ (a - 1) * b := Nat.mul_le_mul_right b hh_le_a1
        _ < (a - 1) * b + (a - 1) := by omega
        _ = (a - 1) * (b + 1) := by ring
    have hhqN : h * q + N = N * (2 * h + 1) + h * b := by
      rw [hq]
      ring
    omega
  · have hr1_le : r + 1 ≤ h := by omega
    have hp_mono : (r + 1) * p ≤ h * p := Nat.mul_le_mul_right p hr1_le
    have hident : 2 * ((a - 1) * (b + 1) + (r + 1) * a) + 2 * (b + 1) = a * (a + b) := by
      have ha1_eq : a - 1 = b + 3 + 2 * r := by omega
      rw [ha1_eq, ha]
      ring
    have hsmall : (a - 1) * (b + 1) + (r + 1) * a < N := by omega
    have hr1_sum : (r + 1) * p + (r + 1) * a = N * (2 * r + 1) + N := by
      calc
        (r + 1) * p + (r + 1) * a = (r + 1) * (p + a) := by ring
        _ = (r + 1) * (2 * N) := by rw [hp]
        _ = N * (2 * r + 1) + N := by ring
    omega

private lemma sigma_m12_le {N x : ℕ} (hN : 1 ≤ N) (hx : N ≤ x) :
    (N - 1) * (x + 1) ≤ N * x := by
  zify [hN] at hx ⊢
  nlinarith

private lemma sigma_m3_le {K p q : ℕ} (hK : 5 ≤ K) (hp : 3 * K < p) (hq : 4 * K ≤ q) :
    (K - 1) * (p + 1) * (q + 1) ≤ K * p * q := by
  have hK1 : 1 ≤ K := by omega
  zify [hK1] at hK hp hq ⊢
  nlinarith

private lemma not_pseudoperfect_melfi {K N a b r p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q)
    (hK_pos : 0 < K) (hsum_K : ∑ d ∈ K.divisors, d = N - 1)
    (ha : a = b + 4 + 2 * r) (hsize : a * (a + b) < 2 * N)
    (hp_add : p + a = 2 * N) (hq_eq : q = 2 * N + b)
    (hprop_sum : ∑ d ∈ (K * p * q).properDivisors, d =
      K * p * q + (N * (2 * r + 1) + (a - 1) * (b + 1))) :
    ¬ (K * p * q).Pseudoperfect := by
  rintro ⟨_, s, hs_sub, hs_sum⟩
  let n : ℕ := K * p * q
  let Δ : ℕ := N * (2 * r + 1) + (a - 1) * (b + 1)
  let T : Finset ℕ := n.properDivisors \ s
  have hT_sum : ∑ d ∈ T, d = Δ := by
    have hsdiff := Finset.sum_sdiff hs_sub (f := fun d => d)
    change (∑ d ∈ T, d) + ∑ d ∈ s, d = ∑ d ∈ n.properDivisors, d at hsdiff
    rw [hs_sum] at hsdiff
    change (∑ d ∈ T, d) + n = ∑ d ∈ (K * p * q).properDivisors, d at hsdiff
    rw [hprop_sum] at hsdiff
    change (∑ d ∈ T, d) + n = n + Δ at hsdiff
    omega
  let Tp : Finset ℕ := T.filter (fun d => p ∣ d)
  let Tnp : Finset ℕ := T.filter (fun d => ¬ p ∣ d)
  let Tq : Finset ℕ := Tnp.filter (fun d => q ∣ d)
  let T0 : Finset ℕ := Tnp.filter (fun d => ¬ q ∣ d)
  have hsplit1 : ∑ d ∈ T, d = (∑ d ∈ Tp, d) + ∑ d ∈ Tnp, d :=
    (Finset.sum_filter_add_sum_filter_not T (fun d => p ∣ d) (fun d => d)).symm
  have hsplit2 : ∑ d ∈ Tnp, d = (∑ d ∈ Tq, d) + ∑ d ∈ T0, d :=
    (Finset.sum_filter_add_sum_filter_not Tnp (fun d => q ∣ d) (fun d => d)).symm
  let B : ℕ := ∑ d ∈ Tp, d / p
  let C : ℕ := ∑ d ∈ Tq, d / q
  let A0 : ℕ := ∑ d ∈ T0, d
  have hTp_eq : ∑ d ∈ Tp, d = p * B := by
    dsimp [B]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2).symm
  have hTq_eq : ∑ d ∈ Tq, d = q * C := by
    dsimp [C]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2).symm
  have hT0_sub : T0 ⊆ K.divisors := by
    intro d hd
    have hd_Tnp : d ∈ Tnp := (Finset.mem_filter.mp hd).1
    have hnq : ¬ q ∣ d := (Finset.mem_filter.mp hd).2
    have hd_T : d ∈ T := (Finset.mem_filter.mp hd_Tnp).1
    have hnp : ¬ p ∣ d := (Finset.mem_filter.mp hd_Tnp).2
    have hd_prop : d ∈ n.properDivisors := (Finset.mem_sdiff.mp hd_T).1
    have hd_dvd_n : d ∣ K * p * q := (Nat.mem_properDivisors.mp hd_prop).1
    have hd_cop_q : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hnq).symm
    have hd_cop_p : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hnp).symm
    have hd_dvd_Kp : d ∣ K * p := hd_cop_q.dvd_of_dvd_mul_right hd_dvd_n
    have hd_dvd_K : d ∣ K := hd_cop_p.dvd_of_dvd_mul_right hd_dvd_Kp
    exact Nat.mem_divisors.mpr ⟨hd_dvd_K, hK_pos.ne'⟩
  have hA0_le : A0 ≤ N - 1 :=
    (Finset.sum_le_sum_of_subset hT0_sub).trans_eq hsum_K
  have hN_pos : 1 ≤ N := by omega
  have hΔ_decomp : Δ = p * B + q * C + A0 := by
    calc
      Δ = ∑ d ∈ T, d := hT_sum.symm
      _ = (∑ d ∈ Tp, d) + ((∑ d ∈ Tq, d) + A0) := by rw [hsplit1, hsplit2]
      _ = p * B + q * C + A0 := by rw [hTp_eq, hTq_eq, add_assoc]
  have hh_low : (B + C) * p ≤ Δ := by
    have hpC : p * C ≤ q * C := Nat.mul_le_mul_right C hp_lt_q.le
    have hlin : (B + C) * p = p * B + p * C := by ring
    omega
  have hh_high : Δ < (B + C) * q + N := by
    have hpB : p * B ≤ q * B := Nat.mul_le_mul_right B hp_lt_q.le
    have hlin : (B + C) * q = q * B + q * C := by ring
    omega
  exact delta_not_in_block ha hsize hp_add hq_eq hh_low hh_high

theorem prove_Erdos470_R1_H1 :
    ∀ k a b : ℕ, b + 3 < a → a * (a + b) < 2 ^ (k + 2) → (2 ^ (k + 2) - a).Prime →
      (2 ^ (k + 2) + b).Prime →
      Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b)) := by
  intro k a b hab hsize hp hq
  let K : ℕ := 2 ^ k
  let N : ℕ := 2 ^ (k + 1)
  let X : ℕ := 2 ^ (k + 2)
  let p : ℕ := X - a
  let q : ℕ := X + b
  have hN_eq : N = 2 * K := by dsimp [N, K]; ring
  have hX_eq : X = 4 * K := by dsimp [X, K]; ring
  have hX_2N : X = 2 * N := by dsimp [X, N]; ring
  have ha4 : 4 ≤ a := by omega
  have hsize_X : a * (a + b) < X := hsize
  have ha_lt_K : a < K := by
    have h4a : 4 * a ≤ a * (a + b) := by nlinarith
    omega
  have hK5 : 5 ≤ K := by omega
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    have hK1 : K = 1 := by simp [K, hk_eq]
    omega
  have hp_def : p = X - a := rfl
  have hq_def : q = X + b := rfl
  have hp_add_2N : p + a = 2 * N := by omega
  have hq_eq_2N : q = 2 * N + b := by omega
  have hp_gt_3K : 3 * K < p := by omega
  have hq_ge_4K : 4 * K ≤ q := by omega
  have hp2 : 2 < p := by omega
  have hq2 : 2 < q := by omega
  have hp_lt_q : p < q := by omega
  have hN1 : 1 ≤ N := by omega
  -- Coprimality and divisor sums
  have hcop_Kp : K.Coprime p := coprime_two_pow_of_prime_gt_two k hp hp2
  have hcop_Kq : K.Coprime q := coprime_two_pow_of_prime_gt_two k hq hq2
  have hcop_pq : p.Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt_q)).symm
  have hcop_Kpq : (K * p).Coprime q := hcop_Kq.mul_left hcop_pq
  have hsum_K : ∑ d ∈ K.divisors, d = N - 1 := sum_divisors_two_pow k
  have hsum_p : ∑ d ∈ p.divisors, d = p + 1 := by rw [hp.sum_divisors, add_comm]
  have hsum_q : ∑ d ∈ q.divisors, d = q + 1 := by rw [hq.sum_divisors, add_comm]
  have hsum_n : ∑ d ∈ (K * p * q).divisors, d = (N - 1) * (p + 1) * (q + 1) := by
    rw [hcop_Kpq.sum_divisors_mul, hcop_Kp.sum_divisors_mul, hsum_K, hsum_p, hsum_q]
  -- Parity and abundance formula
  have hp_odd : p % 2 = 1 := odd_of_prime_gt_two hp hp2
  have hq_odd : q % 2 = 1 := odd_of_prime_gt_two hq hq2
  let r : ℕ := (a - b - 4) / 2
  have hr_def : r = (a - b - 4) / 2 := rfl
  have ha_even_gap : a = b + 4 + 2 * r := by omega
  have hsize_2N : a * (a + b) < 2 * N := by omega
  have h2n_eq : 2 * (K * p * q) = N * p * q := by rw [hN_eq]; ring
  have hsigma_eq : (N - 1) * (p + 1) * (q + 1) =
      2 * (K * p * q) + (N * (2 * r + 1) + (a - 1) * (b + 1)) := by
    rw [h2n_eq]
    exact melfi_sigma_identity hN1 ha_even_gap (by omega) (by omega) hq_eq_2N
  have hΔ_pos : 0 < N * (2 * r + 1) + (a - 1) * (b + 1) := by
    have h1 : 0 < (a - 1) * (b + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have habund_n : (K * p * q).Abundant := by
    rw [Nat.abundant_iff_sum_divisors, hsum_n, hsigma_eq]
    omega
  have hprop_sum : ∑ d ∈ (K * p * q).properDivisors, d =
      K * p * q + (N * (2 * r + 1) + (a - 1) * (b + 1)) := by
    have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := K * p * q)
    rw [hsum_n, hsigma_eq] at h
    omega
  have hnot_pseudo : ¬ (K * p * q).Pseudoperfect :=
    not_pseudoperfect_melfi hp hq hp_lt_q (by omega) hsum_K ha_even_gap hsize_2N
      hp_add_2N hq_eq_2N hprop_sum
  change Erdos470.PrimitiveWeird (K * p * q)
  refine ⟨⟨habund_n, hnot_pseudo⟩, ?_⟩
  intro d hd_prop hd_weird
  have hd_abund : d.Abundant := hd_weird.1
  obtain ⟨hd_dvd, hd_lt⟩ := Nat.mem_properDivisors.mp hd_prop
  by_cases hpd : p ∣ d
  · by_cases hqd : q ∣ d
    · have hpq_dvd : p * q ∣ d := hcop_pq.mul_dvd_of_dvd_of_dvd hpd hqd
      obtain ⟨u, rfl⟩ := hpq_dvd
      have hpq_pos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
      have hu_dvd : u ∣ 2 ^ k := by
        apply (mul_dvd_mul_iff_left hpq_pos.ne').mp
        calc
          p * q * u ∣ K * p * q := hd_dvd
          _ = p * q * 2 ^ k := by dsimp [K]; ring
      have hu_lt : u < 2 ^ k := by
        apply (Nat.mul_lt_mul_left hpq_pos).mp
        calc
          p * q * u < K * p * q := hd_lt
          _ = p * q * 2 ^ k := by dsimp [K]; ring
      obtain ⟨j, hjk, rfl⟩ :=
        (Nat.mem_properDivisors_prime_pow Nat.prime_two k).mp
          (Nat.mem_properDivisors.mpr ⟨hu_dvd, hu_lt⟩)
      let m3 : ℕ := 2 ^ (k - 1) * p * q
      have hd_dvd_m3 : p * q * 2 ^ j ∣ m3 := by
        have hj_dvd : 2 ^ j ∣ 2 ^ (k - 1) := Nat.pow_dvd_pow 2 (by omega)
        calc
          p * q * 2 ^ j ∣ p * q * 2 ^ (k - 1) := mul_dvd_mul_left (p * q) hj_dvd
          _ = m3 := by dsimp [m3]; ring
      have hm3_pos : 0 < m3 := Nat.mul_pos (Nat.mul_pos (by positivity) hp.pos) hq.pos
      have hm3_abund : m3.Abundant := hd_abund.of_dvd hd_dvd_m3 hm3_pos.ne'
      rw [Nat.abundant_iff_sum_divisors] at hm3_abund
      have hcop1p : (2 ^ (k - 1)).Coprime p := coprime_two_pow_of_prime_gt_two (k - 1) hp hp2
      have hcop1q : (2 ^ (k - 1)).Coprime q := coprime_two_pow_of_prime_gt_two (k - 1) hq hq2
      have hcop2 : (2 ^ (k - 1) * p).Coprime q := hcop1q.mul_left hcop_pq
      have hsum_2k1 : ∑ x ∈ (2 ^ (k - 1)).divisors, x = K - 1 := by
        rw [sum_divisors_two_pow (k - 1), show k - 1 + 1 = k by omega]
      have hsum_m3 : ∑ x ∈ m3.divisors, x = (K - 1) * (p + 1) * (q + 1) := by
        dsimp [m3]
        rw [hcop2.sum_divisors_mul, hcop1p.sum_divisors_mul, hsum_2k1, hsum_p, hsum_q]
      have h2m3 : 2 * m3 = K * p * q := by
        have h2pow : 2 * 2 ^ (k - 1) = K := by
          dsimp [K]
          rw [← pow_succ', show k - 1 + 1 = k by omega]
        calc
          2 * m3 = (2 * 2 ^ (k - 1)) * p * q := by dsimp [m3]; ring
          _ = K * p * q := by rw [h2pow]
      rw [hsum_m3, h2m3] at hm3_abund
      exact (not_le_of_gt hm3_abund) (sigma_m3_le hK5 hp_gt_3K hq_ge_4K)
    · have hd_cop_q : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hqd).symm
      have hd_dvd_m2 : d ∣ K * p := hd_cop_q.dvd_of_dvd_mul_right hd_dvd
      have hm2_pos : 0 < K * p := Nat.mul_pos (by omega) hp.pos
      have hm2_abund : (K * p).Abundant := hd_abund.of_dvd hd_dvd_m2 hm2_pos.ne'
      rw [Nat.abundant_iff_sum_divisors, hcop_Kp.sum_divisors_mul, hsum_K, hsum_p,
        show 2 * (K * p) = N * p by rw [hN_eq]; ring] at hm2_abund
      exact (not_le_of_gt hm2_abund) (sigma_m12_le hN1 (by omega))
  · have hd_cop_p : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    have hd_dvd_swap : d ∣ (K * q) * p := by
      calc
        d ∣ K * p * q := hd_dvd
        _ = (K * q) * p := by ring
    have hd_dvd_m1 : d ∣ K * q := hd_cop_p.dvd_of_dvd_mul_right hd_dvd_swap
    have hm1_pos : 0 < K * q := Nat.mul_pos (by omega) hq.pos
    have hm1_abund : (K * q).Abundant := hd_abund.of_dvd hd_dvd_m1 hm1_pos.ne'
    rw [Nat.abundant_iff_sum_divisors, hcop_Kq.sum_divisors_mul, hsum_K, hsum_q,
      show 2 * (K * q) = N * q by rw [hN_eq]; ring] at hm1_abund
    exact (not_le_of_gt hm1_abund) (sigma_m12_le hN1 (by omega))

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 :=
  prove_Erdos470_R1_H1
