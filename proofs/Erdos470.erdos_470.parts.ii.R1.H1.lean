import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

-- Step Erdos470.erdos_470.parts.ii.R1.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R1
-- Credit: @smurali12
-- H1 := ∀ k a b : ℕ, b + 3 < a → a * (a + b) < 2 ^ (k + 2) → (2 ^ (k + 2) - a).Prime →     (2 ^ (k + 2) + b).Prime →     Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b))  -- For infinitely many k there are primes 2^(k+2) - a and 2^(k+2) + b as in H1.

private lemma sum_divisors_two_pow (j : ℕ) :
    ∑ d ∈ (2 ^ j).divisors, d = 2 ^ (j + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction j with
  | zero => decide
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow (m + 1) 2 (by decide)
    rw [pow_succ]
    omega

private lemma sum_divisors_prime_eq {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ p.divisors, d = p + 1 := by
  rw [← pow_one p, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
  ring

private lemma melfi_sum_divisors_eq (K M p q a b : ℕ) (hK : 1 ≤ K) (hM : M = 2 * K)
    (hab : b + 3 < a) (ha : a ≤ 2 * M) (hp : p = 2 * M - a) (hq : q = 2 * M + b) :
    (M - 1) * (p + 1) * (q + 1) =
      2 * (K * p * q) + (M * (a - b - 3) + (a - 1) * (b + 1)) := by
  subst hp hq hM
  zify [show 1 ≤ 2 * K by omega, show a ≤ 2 * (2 * K) by omega,
    show 1 ≤ a by omega, show b ≤ a by omega, show 3 ≤ a - b by omega]
  ring

private lemma melfi_no_decomp (M p q a b Δ h₀ S₀ B C : ℕ)
    (hM_pos : 1 ≤ M) (hp_eq : p = 2 * M - a) (hq_eq : q = 2 * M + b)
    (hΔ_eq : Δ = M * (a - b - 3) + (a - 1) * (b + 1))
    (hab : b + 3 < a) (hsize : a * (a + b) < 2 * M) (ha_lt_M : 2 * a < M)
    (hh₀ : a - b - 3 = 2 * h₀ + 1)
    (hS₀_le : S₀ ≤ M - 1) (hΔ_decomp : Δ = S₀ + p * B + q * C) : False := by
  have ha_le : a ≤ 2 * M := by omega
  have ha1 : 1 ≤ a := by omega
  have hba : b ≤ a := by omega
  have h3 : 3 ≤ a - b := by omega
  have hS₀_nonneg : (0 : ℤ) ≤ (S₀ : ℤ) := Nat.cast_nonneg S₀
  have hB_nonneg : (0 : ℤ) ≤ (B : ℤ) := Nat.cast_nonneg B
  have hC_nonneg : (0 : ℤ) ≤ (C : ℤ) := Nat.cast_nonneg C
  have hb_nonneg : (0 : ℤ) ≤ (b : ℤ) := Nat.cast_nonneg b
  have hh₀_nonneg : (0 : ℤ) ≤ (h₀ : ℤ) := Nat.cast_nonneg h₀
  zify [hM_pos, ha_le, ha1, hba, h3] at hM_pos hp_eq hq_eq hΔ_eq hab hsize ha_lt_M hh₀ hS₀_le hΔ_decomp
  have hpq : (p : ℤ) < (q : ℤ) := by linarith
  have hΔ_val : (Δ : ℤ) = (M : ℤ) * (2 * (h₀ : ℤ) + 1) + ((a : ℤ) - 1) * ((b : ℤ) + 1) := by
    rw [hΔ_eq, ← hh₀]
  by_cases hh : (B : ℤ) + (C : ℤ) ≤ (h₀ : ℤ)
  · have h1 : (p : ℤ) * (B : ℤ) + (q : ℤ) * (C : ℤ) ≤ (q : ℤ) * ((B : ℤ) + (C : ℤ)) := by nlinarith
    have h2 : (q : ℤ) * ((B : ℤ) + (C : ℤ)) ≤ (q : ℤ) * (h₀ : ℤ) := by nlinarith
    have hid1 : (Δ : ℤ) - ((M : ℤ) - 1 + (q : ℤ) * (h₀ : ℤ)) =
        1 + ((a : ℤ) - 1) + ((a : ℤ) - 1 - (h₀ : ℤ)) * (b : ℤ) := by
      rw [hΔ_val, hq_eq]
      ring
    have h3' : 0 ≤ ((a : ℤ) - 1 - (h₀ : ℤ)) * (b : ℤ) := by nlinarith
    linarith
  · have hh_ge : (h₀ : ℤ) + 1 ≤ (B : ℤ) + (C : ℤ) := by
      have : (h₀ : ℤ) < (B : ℤ) + (C : ℤ) := not_le.mp hh
      omega
    have h1 : (p : ℤ) * ((h₀ : ℤ) + 1) ≤ (p : ℤ) * ((B : ℤ) + (C : ℤ)) := by nlinarith
    have h2 : (p : ℤ) * ((B : ℤ) + (C : ℤ)) ≤ (p : ℤ) * (B : ℤ) + (q : ℤ) * (C : ℤ) := by nlinarith
    have hid2 : 2 * ((p : ℤ) * ((h₀ : ℤ) + 1) - (Δ : ℤ)) =
        2 * (M : ℤ) - (a : ℤ) * ((a : ℤ) + (b : ℤ)) + 2 * (b : ℤ) + 2 := by
      rw [hp_eq, hΔ_val]
      have h2h : (2 : ℤ) * (h₀ : ℤ) = (a : ℤ) - (b : ℤ) - 4 := by linarith
      linear_combination -(a : ℤ) * h2h
    linarith

private lemma melfi_not_pseudoperfect (k K M p q n a b Δ h₀ : ℕ)
    (hK : K = 2 ^ k) (hM : M = 2 * K) (hp_eq : p = 2 * M - a) (hq_eq : q = 2 * M + b)
    (hn_eq : n = K * p * q) (hΔ_eq : Δ = M * (a - b - 3) + (a - 1) * (b + 1))
    (hab : b + 3 < a) (hsize : a * (a + b) < 2 * M) (ha_lt_M : 2 * a < M)
    (hp_prime : p.Prime) (hq_prime : q.Prime) (hcop_pq : p.Coprime q)
    (hh₀ : a - b - 3 = 2 * h₀ + 1)
    (hsum_n : ∑ d ∈ n.divisors, d = 2 * n + Δ) (hn_pos : 0 < n) :
    ¬ n.Pseudoperfect := by
  have hM_pos : 1 ≤ M := by omega
  have hΔ_lt_pq : Δ < p * q := by
    have hp_gt : M < p := by omega
    have hq_ge : 2 * M ≤ q := by omega
    have h1 : 2 * (M * M) ≤ p * q := by nlinarith
    have h2 : Δ ≤ M * a + a * (b + 1) := by
      rw [hΔ_eq]
      gcongr <;> omega
    have h3 : M * a < M * M := by nlinarith
    have h4 : a * (b + 1) ≤ a * (a + b) := Nat.mul_le_mul_left a (by omega)
    have h5 : 2 * M ≤ M * M := by
      have : 2 ≤ M := by omega
      nlinarith
    omega
  rintro ⟨_, S, hS_sub, hS_sum⟩
  let T := n.properDivisors \ S
  have hT_sum : ∑ d ∈ T, d = Δ := by
    have h1 : ∑ d ∈ T, d + ∑ d ∈ S, d = ∑ d ∈ n.properDivisors, d := Finset.sum_sdiff hS_sub
    have h2 : ∑ d ∈ n.divisors, d = ∑ d ∈ n.properDivisors, d + n :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self
    omega
  have hno_pq : ∀ d ∈ T, ¬ (p * q ∣ d) := by
    intro d hd hdvd
    have hd_pos : 0 < d :=
      Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp (Finset.mem_sdiff.mp hd).1).1 hn_pos
    have hle_sum : d ≤ ∑ x ∈ T, x :=
      Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hd
    have hpq_le_d : p * q ≤ d := Nat.le_of_dvd hd_pos hdvd
    omega
  let T₀ := T.filter (fun d => ¬ p ∣ d ∧ ¬ q ∣ d)
  let T₁ := T.filter (fun d => p ∣ d)
  let T₂ := T.filter (fun d => q ∣ d)
  have hdisj01 : Disjoint T₀ T₁ := by
    rw [Finset.disjoint_left]
    intro d hd0 hd1
    exact (Finset.mem_filter.mp hd0).2.1 (Finset.mem_filter.mp hd1).2
  have hdisj02 : Disjoint T₀ T₂ := by
    rw [Finset.disjoint_left]
    intro d hd0 hd2
    exact (Finset.mem_filter.mp hd0).2.2 (Finset.mem_filter.mp hd2).2
  have hdisj12 : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    exact hno_pq d (Finset.mem_filter.mp hd1).1
      (hcop_pq.mul_dvd_of_dvd_of_dvd (Finset.mem_filter.mp hd1).2 (Finset.mem_filter.mp hd2).2)
  have hT_eq : T = T₀ ∪ (T₁ ∪ T₂) := by
    ext d
    simp only [T₀, T₁, T₂, Finset.mem_union, Finset.mem_filter]
    tauto
  have hT_split : ∑ d ∈ T, d = (∑ d ∈ T₀, d) + (∑ d ∈ T₁, d) + (∑ d ∈ T₂, d) := by
    rw [hT_eq, Finset.sum_union (Finset.disjoint_union_right.mpr ⟨hdisj01, hdisj02⟩),
      Finset.sum_union hdisj12]
    ring
  have hT₀_le : ∑ d ∈ T₀, d ≤ M - 1 := by
    have hsub : T₀ ⊆ K.divisors := by
      intro d hd
      have hdT := (Finset.mem_filter.mp hd).1
      have hnp := (Finset.mem_filter.mp hd).2.1
      have hnq := (Finset.mem_filter.mp hd).2.2
      have hd_prop := (Finset.mem_sdiff.mp hdT).1
      have hd_dvd : d ∣ K * p * q := by rw [← hn_eq]; exact (Nat.mem_properDivisors.mp hd_prop).1
      have hd_cop_q : d.Coprime q := (hq_prime.coprime_iff_not_dvd.mpr hnq).symm
      have hd_cop_p : d.Coprime p := (hp_prime.coprime_iff_not_dvd.mpr hnp).symm
      have hd_dvd_Kp : d ∣ K * p := hd_cop_q.dvd_of_dvd_mul_right hd_dvd
      have hd_dvd_K : d ∣ K := hd_cop_p.dvd_of_dvd_mul_right hd_dvd_Kp
      exact Nat.mem_divisors.mpr ⟨hd_dvd_K, by omega⟩
    have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
    rw [hK, sum_divisors_two_pow k, pow_succ', ← hK, ← hM] at hle
    exact hle
  let B := ∑ d ∈ T₁, d / p
  let C := ∑ d ∈ T₂, d / q
  have hT₁_eq : ∑ d ∈ T₁, d = p * B := by
    dsimp [B]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2).symm
  have hT₂_eq : ∑ d ∈ T₂, d = q * C := by
    dsimp [C]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    exact (Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2).symm
  have hΔ_decomp : Δ = (∑ d ∈ T₀, d) + p * B + q * C := by
    rw [← hT_sum, hT_split, hT₁_eq, hT₂_eq]
  exact melfi_no_decomp M p q a b Δ h₀ (∑ d ∈ T₀, d) B C hM_pos hp_eq hq_eq hΔ_eq hab
    hsize ha_lt_M hh₀ hT₀_le hΔ_decomp

private lemma melfi_m1_not_abundant (K K1 p q a b : ℕ) (_hK1 : 1 ≤ K1) (hK : K = 2 * K1)
    (hp_eq : p = 4 * K - a) (hq_eq : q = 4 * K + b)
    (ha_lt : a < 2 * K) (_hb_lt : b < 2 * K) (ha1 : 1 ≤ a) (hK8 : 8 ≤ K) :
    (K - 1) * (p + 1) * (q + 1) ≤ 2 * (K1 * p * q) := by
  zify [show 1 ≤ K by omega, show a ≤ 4 * K by omega, ha1] at hp_eq hq_eq hK ⊢
  have h1 : (2 : ℤ) * (K1 : ℤ) = (K : ℤ) := by linarith
  have h2 : (2 : ℤ) * ((K1 : ℤ) * (p : ℤ) * (q : ℤ)) = (K : ℤ) * (p : ℤ) * (q : ℤ) := by
    rw [← h1]
    ring
  rw [h2, hp_eq, hq_eq]
  nlinarith

private lemma melfi_m23_not_abundant (K M x : ℕ) (hM : M = 2 * K) (hM1 : 1 ≤ M) (hx : M < x) :
    (M - 1) * (x + 1) ≤ 2 * (K * x) := by
  zify [hM1] at hM hx ⊢
  rw [hM] at hx ⊢
  linarith [show ((2 : ℤ) * (K : ℤ) - 1) * ((x : ℤ) + 1) - 2 * ((K : ℤ) * (x : ℤ)) =
      2 * (K : ℤ) - (x : ℤ) - 1 by ring]

set_option maxHeartbeats 400000 in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := by
  intro k a b hab hsize hp hq
  let X := 2 ^ (k + 2)
  let M := 2 ^ (k + 1)
  let K := 2 ^ k
  let p := X - a
  let q := X + b
  let n := K * p * q
  have hX_eq : X = 2 * M := by dsimp [X, M]; rw [pow_succ']
  have hM_eq : M = 2 * K := by dsimp [M, K]; rw [pow_succ']
  have hK_pos : 1 ≤ K := Nat.one_le_pow k 2 (by decide)
  have hM_pos : 1 ≤ M := by omega
  have ha4 : 4 ≤ a := by omega
  have ha_sq : a * a < X := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (by omega)) hsize
  have ha_lt_M : 2 * a < M := by nlinarith
  have hk_ge : 3 ≤ k := by
    by_contra hk_lt
    have hk_le : k ≤ 2 := by omega
    have hX_le : X ≤ 16 := by
      dsimp [X]
      calc 2 ^ (k + 2) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 16 := by decide
    nlinarith
  have hp_def : p = 2 * M - a := by dsimp [p]; omega
  have hq_def : q = 2 * M + b := by dsimp [q]; omega
  have hp_gt_M : M < p := by omega
  have hq_ge_X : X ≤ q := by omega
  have hpq_lt : p < q := by omega
  have hp_odd : p % 2 = 1 := by
    have hne2 : p ≠ 2 := by omega
    exact Nat.mod_two_ne_zero.mp fun h => hne2 ((Nat.Prime.even_iff hp).mp (Nat.even_iff.mpr h))
  have hq_odd : q % 2 = 1 := by
    have hne2 : q ≠ 2 := by omega
    exact Nat.mod_two_ne_zero.mp fun h => hne2 ((Nat.Prime.even_iff hq).mp (Nat.even_iff.mpr h))
  have hX_even : X % 2 = 0 := by omega
  have ha_odd : a % 2 = 1 := by dsimp [p] at hp_odd; omega
  have hb_odd : b % 2 = 1 := by dsimp [q] at hq_odd; omega
  let h₀ := (a - b - 4) / 2
  have hh₀ : a - b - 3 = 2 * h₀ + 1 := by omega
  have hcop2p : K.Coprime p :=
    Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
  have hcop2q : K.Coprime q :=
    Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
  have hcop_pq : p.Coprime q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hcop2pq : (K * p).Coprime q := hcop2q.mul_left hcop_pq
  have hsum_n : ∑ d ∈ n.divisors, d = (M - 1) * (p + 1) * (q + 1) := by
    dsimp [n]
    rw [hcop2pq.sum_divisors_mul, hcop2p.sum_divisors_mul,
      sum_divisors_prime_eq hp, sum_divisors_prime_eq hq]
    dsimp [K, M]
    rw [sum_divisors_two_pow k]
  let Δ := M * (a - b - 3) + (a - 1) * (b + 1)
  have hsum_eq : ∑ d ∈ n.divisors, d = 2 * n + Δ := by
    rw [hsum_n]
    exact melfi_sum_divisors_eq K M p q a b hK_pos hM_eq hab (by omega) hp_def hq_def
  have hΔ_pos : 1 ≤ Δ := by
    have : 1 ≤ M * (a - b - 3) := Nat.mul_pos hM_pos (by omega)
    omega
  have habund : n.Abundant := by
    rw [Nat.abundant_iff_sum_divisors, hsum_eq]
    omega
  have hn_pos : 0 < n := Nat.mul_pos (Nat.mul_pos hK_pos hp.pos) hq.pos
  have hnot_pseudo : ¬ n.Pseudoperfect :=
    melfi_not_pseudoperfect k K M p q n a b Δ h₀ rfl hM_eq hp_def hq_def rfl rfl
      hab (by omega) ha_lt_M hp hq hcop_pq hh₀ hsum_eq hn_pos
  refine ⟨⟨habund, hnot_pseudo⟩, ?_⟩
  intro d hd ⟨hd_ab, _⟩
  let m₁ := 2 ^ (k - 1) * p * q
  let m₂ := K * q
  let m₃ := K * p
  have hm₁_pos : m₁ ≠ 0 := by
    dsimp [m₁]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by decide)) hp.ne_zero) hq.ne_zero
  have hm₂_pos : m₂ ≠ 0 := by
    dsimp [m₂, K]
    exact Nat.mul_ne_zero (pow_ne_zero _ (by decide)) hq.ne_zero
  have hm₃_pos : m₃ ≠ 0 := by
    dsimp [m₃, K]
    exact Nat.mul_ne_zero (pow_ne_zero _ (by decide)) hp.ne_zero
  have hd_dvd : d ∣ n := (Nat.mem_properDivisors.mp hd).1
  have hd_lt : d < n := (Nat.mem_properDivisors.mp hd).2
  have hm₁_not : ¬ m₁.Abundant := by
    rw [Nat.abundant_iff_sum_divisors, not_lt]
    have hcop1p : (2 ^ (k - 1)).Coprime p :=
      Nat.Coprime.pow_left (k - 1) (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    have hcop1q : (2 ^ (k - 1)).Coprime q :=
      Nat.Coprime.pow_left (k - 1) (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    have hcop1pq : (2 ^ (k - 1) * p).Coprime q := hcop1q.mul_left hcop_pq
    dsimp [m₁]
    rw [hcop1pq.sum_divisors_mul, hcop1p.sum_divisors_mul,
      sum_divisors_two_pow (k - 1), sum_divisors_prime_eq hp, sum_divisors_prime_eq hq,
      show k - 1 + 1 = k by omega]
    have hK_eq2 : K = 2 * 2 ^ (k - 1) := by
      dsimp [K]
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    have hK8 : 8 ≤ K := by
      dsimp [K]
      calc 8 = 2 ^ 3 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk_ge
    exact melfi_m1_not_abundant K (2 ^ (k - 1)) p q a b (Nat.one_le_pow _ 2 (by decide)) hK_eq2
      (by omega) (by omega) (by omega) (by omega) (by omega) hK8
  have hm₂_not : ¬ m₂.Abundant := by
    rw [Nat.abundant_iff_sum_divisors, not_lt]
    have hsum : ∑ d ∈ m₂.divisors, d = (M - 1) * (q + 1) := by
      dsimp [m₂]
      rw [hcop2q.sum_divisors_mul, sum_divisors_prime_eq hq]
      dsimp [K, M]
      rw [sum_divisors_two_pow k]
    rw [hsum]
    dsimp [m₂]
    exact melfi_m23_not_abundant K M q hM_eq hM_pos (by omega)
  have hm₃_not : ¬ m₃.Abundant := by
    rw [Nat.abundant_iff_sum_divisors, not_lt]
    have hsum : ∑ d ∈ m₃.divisors, d = (M - 1) * (p + 1) := by
      dsimp [m₃]
      rw [hcop2p.sum_divisors_mul, sum_divisors_prime_eq hp]
      dsimp [K, M]
      rw [sum_divisors_two_pow k]
    rw [hsum]
    dsimp [m₃]
    exact melfi_m23_not_abundant K M p hM_eq hM_pos hp_gt_M
  by_cases hp_d : p ∣ d
  · by_cases hq_d : q ∣ d
    · have hpq_d : p * q ∣ d := hcop_pq.mul_dvd_of_dvd_of_dvd hp_d hq_d
      obtain ⟨r, hr⟩ := hpq_d
      have hr_dvd : r ∣ K := by
        have h1 : r * (p * q) ∣ K * (p * q) := by
          rw [mul_comm r (p * q), ← hr, show K * (p * q) = K * p * q by ring]
          exact hd_dvd
        exact (Nat.mul_dvd_mul_iff_right (Nat.mul_pos hp.pos hq.pos)).mp h1
      have hr_lt : r < K := by
        have hmul : p * q * r < p * q * K := by
          rw [← hr, show p * q * K = K * p * q by ring]
          exact hd_lt
        exact Nat.lt_of_mul_lt_mul_left hmul
      obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hr_dvd
      have hj_lt : j < k := by
        by_contra hj
        have hle : K ≤ 2 ^ j := by
          dsimp [K]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hr_dvd' : 2 ^ j ∣ 2 ^ (k - 1) := Nat.pow_dvd_pow 2 (by omega)
      have hd_m₁ : d ∣ m₁ := by
        rw [hr, mul_comm (p * q) (2 ^ j)]
        show 2 ^ j * (p * q) ∣ 2 ^ (k - 1) * p * q
        rw [mul_assoc (2 ^ (k - 1)) p q]
        exact mul_dvd_mul_right hr_dvd' (p * q)
      exact hm₁_not (hd_ab.of_dvd hd_m₁ hm₁_pos)
    · have hd_cop_q : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hq_d).symm
      have hd_m₃ : d ∣ m₃ := hd_cop_q.dvd_of_dvd_mul_right hd_dvd
      exact hm₃_not (hd_ab.of_dvd hd_m₃ hm₃_pos)
  · have hd_cop_p : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hp_d).symm
    have hd_m₂ : d ∣ m₂ := by
      have hd_dvd' : d ∣ (K * q) * p := by
        rw [show (K * q) * p = K * p * q by ring]
        exact hd_dvd
      exact hd_cop_p.dvd_of_dvd_mul_right hd_dvd'
    exact hm₂_not (hd_ab.of_dvd hd_m₂ hm₂_pos)
