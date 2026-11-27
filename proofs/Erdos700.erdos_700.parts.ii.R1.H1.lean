import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1

-- Step Erdos700.erdos_700.parts.ii.R1.H1: hypothesis H1 of reduction Erdos700.erdos_700.parts.ii.R1
-- Credit: @michielkosters
-- H1 := ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r → q - p < r - q →     2 * (r - p) ^ 2 < p → Erdos700.f (p * q * r) ^ 2 > p * q * r  /-- There are arbitrarily large prime triples `p < q < r` with increasing gaps and `2 (r - p)^2 < p`. -/

private lemma not_dvd_choose_div_of_dvd {u n k : ℕ} (hu : u.Prime) (hun : u ∣ n)
    (h : ¬ u ∣ n.choose k) : u ∣ k ∧ ¬ u ∣ (n / u).choose (k / u) := by
  have hk : u ∣ k := Erdos700.prime_dvd_of_not_dvd_choose u n k hu hun h
  refine ⟨hk, fun hd => h ?_⟩
  have := Fact.mk hu
  have hmod : n.choose k ≡ (n % u).choose (k % u) * (n / u).choose (k / u) [MOD u] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  rw [Nat.mod_eq_zero_of_dvd hun, Nat.mod_eq_zero_of_dvd hk,
    Nat.choose_zero_right, one_mul] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hd))

private lemma mod_le_and_not_dvd_div_of_not_dvd_choose {u a b : ℕ} (hu : u.Prime)
    (h : ¬ u ∣ a.choose b) : b % u ≤ a % u ∧ ¬ u ∣ (a / u).choose (b / u) := by
  have := Fact.mk hu
  have hmod : a.choose b ≡ (a % u).choose (b % u) * (a / u).choose (b / u) [MOD u] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  constructor
  · by_contra! hlt
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul] at hmod
    exact h (Nat.modEq_zero_iff_dvd.mp hmod)
  · intro hd
    have h0 : (a % u).choose (b % u) * (a / u).choose (b / u) ≡ 0 [MOD u] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_right hd _
    exact h (Nat.modEq_zero_iff_dvd.mp (hmod.trans h0))

private lemma mod_eq_of_mul_add {u Q R : ℕ} (hR : R < u) : (u * Q + R) % u = R := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hR]

private lemma div_eq_of_mul_add {u Q R : ℕ} (hu : 0 < u) (hR : R < u) : (u * Q + R) / u = Q := by
  rw [Nat.mul_add_div hu, Nat.div_eq_of_lt hR, add_zero]

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 := by
  intro p q r hp hq hr hpq hqr hgap hsmall
  set d1 := q - p
  set d2 := r - q
  set D := r - p
  have hd1_pos : 0 < d1 := by omega
  have hd2_gt : d1 < d2 := hgap
  have hD_eq : D = d1 + d2 := by omega
  have hD_ge : 3 ≤ D := by omega
  have hD2_lt_p : 2 * D ^ 2 < p := hsmall
  have hD_sq_lt_p : D ^ 2 < p := by omega
  have hD_lt_p : 6 * D < p := by
    calc 6 * D = 2 * (3 * D) := by ring
      _ ≤ 2 * (D * D) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right D hD_ge)
      _ = 2 * D ^ 2 := by ring
      _ < p := hD2_lt_p
  have hp_ge : 19 ≤ p := by omega
  have hq_ge : 19 ≤ q := by omega
  have hr_ge : 19 ≤ r := by omega
  have hq_eq : q = p + d1 := by omega
  have hr_eq : r = p + D := by omega
  have hr_q_eq : r = q + d2 := by omega
  have hr_lt_2p : r < 2 * p := by omega
  have hr_lt_2q : r < 2 * q := by omega
  have hpqr_pos : 0 < p * q * r := Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hne_mem : 2 ≤ p * q * r / 2 := by
    have h4 : 4 ≤ p * q * r := by
      calc 4 ≤ 19 * 19 * 19 := by decide
        _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hp_ge hq_ge) hr_ge
    omega
  have hne : (Erdos700.fSet (p * q * r)).Nonempty :=
    ⟨_, Erdos700.f_mem (p * q * r) 2 (by decide) hne_mem⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  rw [Erdos700.f_eq, hkeq]
  set g := Nat.gcd (p * q * r) ((p * q * r).choose k)
  by_contra! hg_le
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hpqr_pos
  have h2k : 2 * k ≤ p * q * r := by omega
  have hcases : (¬ p ∣ (p * q * r).choose k ∧ ¬ q ∣ (p * q * r).choose k) ∨
      (¬ p ∣ (p * q * r).choose k ∧ ¬ r ∣ (p * q * r).choose k) ∨
      (¬ q ∣ (p * q * r).choose k ∧ ¬ r ∣ (p * q * r).choose k) := by
    by_cases hpC : p ∣ (p * q * r).choose k <;>
    by_cases hqC : q ∣ (p * q * r).choose k <;>
    by_cases hrC : r ∣ (p * q * r).choose k
    · exfalso
      have hpg : p ∣ g := Nat.dvd_gcd ⟨q * r, by ring⟩ hpC
      have hqg : q ∣ g := Nat.dvd_gcd ⟨p * r, by ring⟩ hqC
      have hpqg : p * q ∣ g := (Nat.coprime_primes hp hq).mpr hpq.ne |>.mul_dvd_of_dvd_of_dvd hpg hqg
      have hle : p * q ≤ g := Nat.le_of_dvd hgpos hpqg
      have hrpq : r < p * q := by
        calc r < 2 * p := hr_lt_2p
          _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
          _ = p * q := mul_comm q p
      have hlt : p * q * r < g ^ 2 := by
        calc p * q * r < p * q * (p * q) := Nat.mul_lt_mul_of_pos_left hrpq (Nat.mul_pos hp.pos hq.pos)
          _ = (p * q) ^ 2 := (sq _).symm
          _ ≤ g ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · exfalso
      have hpg : p ∣ g := Nat.dvd_gcd ⟨q * r, by ring⟩ hpC
      have hqg : q ∣ g := Nat.dvd_gcd ⟨p * r, by ring⟩ hqC
      have hpqg : p * q ∣ g := (Nat.coprime_primes hp hq).mpr hpq.ne |>.mul_dvd_of_dvd_of_dvd hpg hqg
      have hle : p * q ≤ g := Nat.le_of_dvd hgpos hpqg
      have hrpq : r < p * q := by
        calc r < 2 * p := hr_lt_2p
          _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
          _ = p * q := mul_comm q p
      have hlt : p * q * r < g ^ 2 := by
        calc p * q * r < p * q * (p * q) := Nat.mul_lt_mul_of_pos_left hrpq (Nat.mul_pos hp.pos hq.pos)
          _ = (p * q) ^ 2 := (sq _).symm
          _ ≤ g ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · exfalso
      have hpg : p ∣ g := Nat.dvd_gcd ⟨q * r, by ring⟩ hpC
      have hrg : r ∣ g := Nat.dvd_gcd ⟨p * q, by ring⟩ hrC
      have hprg : p * r ∣ g := (Nat.coprime_primes hp hr).mpr (by omega) |>.mul_dvd_of_dvd_of_dvd hpg hrg
      have hle : p * r ≤ g := Nat.le_of_dvd hgpos hprg
      have hqpr : q < p * r := by
        calc q < r := hqr
          _ = 1 * r := (one_mul r).symm
          _ ≤ p * r := Nat.mul_le_mul_right r (by omega)
      have hlt : p * q * r < g ^ 2 := by
        calc p * q * r = p * r * q := by ring
          _ < p * r * (p * r) := Nat.mul_lt_mul_of_pos_left hqpr (Nat.mul_pos hp.pos hr.pos)
          _ = (p * r) ^ 2 := (sq _).symm
          _ ≤ g ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · exact Or.inr (Or.inr ⟨hqC, hrC⟩)
    · exfalso
      have hqg : q ∣ g := Nat.dvd_gcd ⟨p * r, by ring⟩ hqC
      have hrg : r ∣ g := Nat.dvd_gcd ⟨p * q, by ring⟩ hrC
      have hqrg : q * r ∣ g := (Nat.coprime_primes hq hr).mpr hqr.ne |>.mul_dvd_of_dvd_of_dvd hqg hrg
      have hle : q * r ≤ g := Nat.le_of_dvd hgpos hqrg
      have hpqr : p < q * r := by
        calc p < q := hpq
          _ = q * 1 := (mul_one q).symm
          _ ≤ q * r := Nat.mul_le_mul_left q hr.pos
      have hlt : p * q * r < g ^ 2 := by
        calc p * q * r = q * r * p := by ring
          _ < q * r * (q * r) := Nat.mul_lt_mul_of_pos_left hpqr (Nat.mul_pos hq.pos hr.pos)
          _ = (q * r) ^ 2 := (sq _).symm
          _ ≤ g ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · exact Or.inr (Or.inl ⟨hpC, hrC⟩)
    · exact Or.inl ⟨hpC, hqC⟩
    · exact Or.inl ⟨hpC, hqC⟩
  have hD_lt_q : D < q := by
    calc D < 6 * D := by omega
      _ < p := hD_lt_p
      _ < q := hpq
  have hd2_m_lt_q : d2 - d1 - 1 < q := by
    calc d2 - d1 - 1 ≤ d2 := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
      _ ≤ D := by omega
      _ < q := hD_lt_q
  rcases hcases with ⟨hpC, hqC⟩ | ⟨hpC, hrC⟩ | ⟨hqC, hrC⟩
  · have hpk : p ∣ k := Erdos700.prime_dvd_of_not_dvd_choose p (p * q * r) k hp ⟨q * r, by ring⟩ hpC
    obtain ⟨hqk, hq_sub⟩ := not_dvd_choose_div_of_dvd hq ⟨p * r, by ring⟩ hqC
    have hpqk : p * q ∣ k := (Nat.coprime_primes hp hq).mpr hpq.ne |>.mul_dvd_of_dvd_of_dvd hpk hqk
    obtain ⟨m, hm_eq⟩ := hpqk
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp at hm_eq; omega
      · exact hm0
    have h2m_r : 2 * m ≤ r := by
      have hmul : (p * q) * (2 * m) ≤ (p * q) * r := by
        calc (p * q) * (2 * m) = 2 * (p * q * m) := by ring
          _ = 2 * k := by rw [hm_eq]
          _ ≤ p * q * r := h2k
      exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hp.pos hq.pos)
    have hm_lt_q : m < q := by omega
    have hk_div_q : k / q = p * m := by
      rw [hm_eq, show p * q * m = q * (p * m) by ring, Nat.mul_div_right _ hq.pos]
    have hn_div_q : p * q * r / q = p * r := by
      rw [show p * q * r = q * (p * r) by ring, Nat.mul_div_right _ hq.pos]
    rw [hn_div_q, hk_div_q] at hq_sub
    have hd1d2_lt_q : d1 * d2 < q := by
      calc d1 * d2 ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
        _ < q := hpq
    have hpr_decomp : p * r = q * (q + (d2 - d1 - 1)) + (q - d1 * d2) := by
      zify [hd1d2_lt_q.le]
      have hp_z : (p : ℤ) = (q : ℤ) - d1 := by omega
      have hr_z : (r : ℤ) = (q : ℤ) + d2 := by omega
      have hsub_z : ((d2 - d1 - 1 : ℕ) : ℤ) = (d2 : ℤ) - d1 - 1 := by omega
      rw [hp_z, hr_z, hsub_z]
      ring
    have hpr_mod : (p * r) % q = q - d1 * d2 := by
      rw [hpr_decomp]
      exact mod_eq_of_mul_add (Nat.sub_lt hq.pos (Nat.mul_pos hd1_pos (by omega)))
    have hpr_div : (p * r) / q = q + (d2 - d1 - 1) := by
      rw [hpr_decomp]
      exact div_eq_of_mul_add hq.pos (Nat.sub_lt hq.pos (Nat.mul_pos hd1_pos (by omega)))
    have hpr_div_mod : ((p * r) / q) % q = d2 - d1 - 1 := by
      rw [hpr_div, show q + (d2 - d1 - 1) = q * 1 + (d2 - d1 - 1) by ring]
      exact mod_eq_of_mul_add hd2_m_lt_q
    obtain ⟨hmod_le, hdiv_nd⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hq hq_sub
    obtain ⟨hdiv_mod_le, _⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hq hdiv_nd
    have hpm_lt_q2 : p * m < q * q := by
      calc p * m < q * m := Nat.mul_lt_mul_of_pos_right hpq hm_pos
        _ < q * q := Nat.mul_lt_mul_of_pos_left hm_lt_q hq.pos
    have hpm_div_lt_q : (p * m) / q < q := by
      rw [Nat.div_lt_iff_lt_mul hq.pos]
      exact hpm_lt_q2
    have hpm_div_mod : ((p * m) / q) % q = (p * m) / q := Nat.mod_eq_of_lt hpm_div_lt_q
    rw [hpm_div_mod, hpr_div_mod] at hdiv_mod_le
    have hm_le : m ≤ d2 - 1 := by
      by_cases hmd1 : m ≤ d1
      · omega
      · have hm_gt : d1 < m := by omega
        have hmul : (m - d1) * q < p * m := by
          have h1 : (m - d1) * q + d1 * m < (m - d1) * q + d1 * q := by gcongr
          have h2 : (m - d1) * q + d1 * q = p * m + d1 * m := by
            calc (m - d1) * q + d1 * q = (m - d1 + d1) * q := by ring
              _ = m * q := by rw [Nat.sub_add_cancel hm_gt.le]
              _ = m * (p + d1) := by rw [hq_eq]
              _ = p * m + d1 * m := by ring
          omega
        have hle_div : m - d1 ≤ (p * m) / q := by
          rw [Nat.le_div_iff_mul_le hq.pos]
          exact hmul.le
        omega
    have hd1m_pos : 0 < d1 * m := Nat.mul_pos hd1_pos hm_pos
    have hd1m_lt_q : d1 * m < q := by
      calc d1 * m ≤ d1 * d2 := Nat.mul_le_mul_left d1 (by omega)
        _ < q := hd1d2_lt_q
    have hpm_decomp : p * m = q * (m - 1) + (q - d1 * m) := by
      zify [hm_pos, hd1m_lt_q.le]
      have hp_z : (p : ℤ) = (q : ℤ) - d1 := by omega
      rw [hp_z]
      ring
    have hpm_mod : (p * m) % q = q - d1 * m := by
      rw [hpm_decomp]
      exact mod_eq_of_mul_add (Nat.sub_lt hq.pos hd1m_pos)
    rw [hpm_mod, hpr_mod] at hmod_le
    have : d1 * d2 ≤ d1 * m := by omega
    have : d2 ≤ m := Nat.le_of_mul_le_mul_left this hd1_pos
    omega
  · obtain ⟨hpk, hp_sub⟩ := not_dvd_choose_div_of_dvd hp ⟨q * r, by ring⟩ hpC
    obtain ⟨hrk, hr_sub⟩ := not_dvd_choose_div_of_dvd hr ⟨p * q, by ring⟩ hrC
    have hprk : p * r ∣ k := (Nat.coprime_primes hp hr).mpr (by omega) |>.mul_dvd_of_dvd_of_dvd hpk hrk
    obtain ⟨m, hm_eq⟩ := hprk
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp at hm_eq; omega
      · exact hm0
    have h2m_q : 2 * m ≤ q := by
      have hmul : (p * r) * (2 * m) ≤ (p * r) * q := by
        calc (p * r) * (2 * m) = 2 * (p * r * m) := by ring
          _ = 2 * k := by rw [hm_eq]
          _ ≤ p * q * r := h2k
          _ = (p * r) * q := by ring
      exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hp.pos hr.pos)
    have hn_div_p : p * q * r / p = q * r := by
      rw [show p * q * r = p * (q * r) by ring, Nat.mul_div_right _ hp.pos]
    have hk_div_p : k / p = r * m := by
      rw [hm_eq, show p * r * m = p * (r * m) by ring, Nat.mul_div_right _ hp.pos]
    rw [hn_div_p, hk_div_p] at hp_sub
    have hn_div_r : p * q * r / r = p * q := by
      rw [show p * q * r = r * (p * q) by ring, Nat.mul_div_right _ hr.pos]
    have hk_div_r : k / r = p * m := by
      rw [hm_eq, show p * r * m = r * (p * m) by ring, Nat.mul_div_right _ hr.pos]
    rw [hn_div_r, hk_div_r] at hr_sub
    have hd1D_lt_p : d1 * D < p := by
      calc d1 * D ≤ D * D := Nat.mul_le_mul_right D (by omega)
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
    have hqr_decomp : q * r = p * (p + (d1 + D)) + d1 * D := by
      rw [hq_eq, hr_eq]; ring
    have hqr_mod : (q * r) % p = d1 * D := by
      rw [hqr_decomp]
      exact mod_eq_of_mul_add hd1D_lt_p
    have hqr_div : (q * r) / p = p + (d1 + D) := by
      rw [hqr_decomp]
      exact div_eq_of_mul_add hp.pos hd1D_lt_p
    have hqr_div_mod : ((q * r) / p) % p = d1 + D := by
      rw [hqr_div, show p + (d1 + D) = p * 1 + (d1 + D) by ring]
      exact mod_eq_of_mul_add (by omega)
    set t := (D * m) / p
    set s := (D * m) % p
    have hs_lt : s < p := Nat.mod_lt _ hp.pos
    have hDm_eq : D * m = p * t + s := (Nat.div_add_mod (D * m) p).symm
    have hrm_decomp : r * m = p * (m + t) + s := by
      calc r * m = (p + D) * m := by rw [hr_eq]
        _ = p * m + D * m := by ring
        _ = p * m + (p * t + s) := by rw [hDm_eq]
        _ = p * (m + t) + s := by ring
    have hmt_lt_p : m + t < p := by
      have ht_le : p * t ≤ D * m := Nat.mul_div_le (D * m) p
      have h1 : 2 * p * (m + t) ≤ (p + D) * q := by
        calc 2 * p * (m + t) = 2 * p * m + 2 * (p * t) := by ring
          _ ≤ 2 * p * m + 2 * (D * m) := by gcongr
          _ = (p + D) * (2 * m) := by ring
          _ ≤ (p + D) * q := Nat.mul_le_mul_left _ h2m_q
      have h2 : (p + D) * q < 2 * p * p := by
        have hq2 : q < p + D := by omega
        calc (p + D) * q ≤ (p + D) * (p + D) := Nat.mul_le_mul_left _ hq2.le
          _ = p * p + D * (2 * p + D) := by ring
          _ ≤ p * p + D * (3 * p) := by gcongr; omega
          _ = p * p + (3 * D) * p := by ring
          _ < p * p + p * p := by gcongr; omega
          _ = 2 * p * p := by ring
      exact Nat.lt_of_mul_lt_mul_left (h1.trans_lt h2)
    have hrm_mod : (r * m) % p = s := by
      rw [hrm_decomp]
      exact mod_eq_of_mul_add hs_lt
    have hrm_div : (r * m) / p = m + t := by
      rw [hrm_decomp]
      exact div_eq_of_mul_add hp.pos hs_lt
    have hrm_div_mod : ((r * m) / p) % p = m + t := by
      rw [hrm_div]
      exact Nat.mod_eq_of_lt hmt_lt_p
    obtain ⟨hp_mod_le, hp_div_nd⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hp hp_sub
    obtain ⟨hp_div_mod_le, _⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hp hp_div_nd
    rw [hrm_div_mod, hqr_div_mod] at hp_div_mod_le
    have hm_lt_2D : m < 2 * D := by
      calc m ≤ m + t := Nat.le_add_right _ _
        _ ≤ d1 + D := hp_div_mod_le
        _ < D + D := by omega
        _ = 2 * D := by ring
    have hDm_lt_p : D * m < p := by
      calc D * m ≤ D * (2 * D) := Nat.mul_le_mul_left D hm_lt_2D.le
        _ = 2 * D ^ 2 := by ring
        _ < p := hD2_lt_p
    have hs_eq : s = D * m := Nat.mod_eq_of_lt hDm_lt_p
    rw [hrm_mod, hqr_mod, hs_eq] at hp_mod_le
    rw [mul_comm d1 D] at hp_mod_le
    have hm_le_d1 : m ≤ d1 := Nat.le_of_mul_le_mul_left hp_mod_le (by omega)
    have hDd2_lt_r : D * d2 < r := by
      calc D * d2 ≤ D * D := Nat.mul_le_mul_left D (by omega)
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
        _ < r := hpq.trans hqr
    have hpq_decomp : p * q = r * (r - D - d2) + D * d2 := by
      zify
      have hp_z : (p : ℤ) = (r : ℤ) - D := by omega
      have hq_z : (q : ℤ) = (r : ℤ) - d2 := by omega
      have hsub_z : ((r - D - d2 : ℕ) : ℤ) = (r : ℤ) - D - d2 := by omega
      rw [hp_z, hq_z, hsub_z]
      ring
    have hpq_mod : (p * q) % r = D * d2 := by
      rw [hpq_decomp]
      exact mod_eq_of_mul_add hDd2_lt_r
    have hDm_pos : 0 < D * m := Nat.mul_pos (by omega) hm_pos
    have hDm_lt_r : D * m < r := by
      calc D * m ≤ D * d1 := Nat.mul_le_mul_left D hm_le_d1
        _ = d1 * D := mul_comm D d1
        _ < p := hd1D_lt_p
        _ < r := hpq.trans hqr
    have hpm_decomp : p * m = r * (m - 1) + (r - D * m) := by
      zify [hm_pos, hDm_lt_r.le]
      have hp_z : (p : ℤ) = (r : ℤ) - D := by omega
      rw [hp_z]
      ring
    have hpm_mod : (p * m) % r = r - D * m := by
      rw [hpm_decomp]
      exact mod_eq_of_mul_add (Nat.sub_lt hr.pos hDm_pos)
    obtain ⟨hr_mod_le, _⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hr hr_sub
    rw [hpm_mod, hpq_mod] at hr_mod_le
    have hsum : D * m + D * d2 < r := by
      calc D * m + D * d2 ≤ D * d1 + D * d2 := by gcongr
        _ = D * (d1 + d2) := by ring
        _ = D ^ 2 := by rw [← hD_eq, sq]
        _ < p := hD_sq_lt_p
        _ < r := by omega
    omega
  · obtain ⟨hqk, hq_sub⟩ := not_dvd_choose_div_of_dvd hq ⟨p * r, by ring⟩ hqC
    obtain ⟨hrk, hr_sub⟩ := not_dvd_choose_div_of_dvd hr ⟨p * q, by ring⟩ hrC
    have hqrk : q * r ∣ k := (Nat.coprime_primes hq hr).mpr hqr.ne |>.mul_dvd_of_dvd_of_dvd hqk hrk
    obtain ⟨m, hm_eq⟩ := hqrk
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp at hm_eq; omega
      · exact hm0
    have h2m_p : 2 * m ≤ p := by
      have hmul : (q * r) * (2 * m) ≤ (q * r) * p := by
        calc (q * r) * (2 * m) = 2 * (q * r * m) := by ring
          _ = 2 * k := by rw [hm_eq]
          _ ≤ p * q * r := h2k
          _ = (q * r) * p := by ring
      exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hq.pos hr.pos)
    have hn_div_q : p * q * r / q = p * r := by
      rw [show p * q * r = q * (p * r) by ring, Nat.mul_div_right _ hq.pos]
    have hk_div_q : k / q = r * m := by
      rw [hm_eq, show q * r * m = q * (r * m) by ring, Nat.mul_div_right _ hq.pos]
    rw [hn_div_q, hk_div_q] at hq_sub
    have hn_div_r : p * q * r / r = p * q := by
      rw [show p * q * r = r * (p * q) by ring, Nat.mul_div_right _ hr.pos]
    have hk_div_r : k / r = q * m := by
      rw [hm_eq, show q * r * m = r * (q * m) by ring, Nat.mul_div_right _ hr.pos]
    rw [hn_div_r, hk_div_r] at hr_sub
    have hd1d2_lt_q : d1 * d2 < q := by
      calc d1 * d2 ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
        _ < q := hpq
    have hpr_decomp : p * r = q * (q + (d2 - d1 - 1)) + (q - d1 * d2) := by
      zify [hd1d2_lt_q.le]
      have hp_z : (p : ℤ) = (q : ℤ) - d1 := by omega
      have hr_z : (r : ℤ) = (q : ℤ) + d2 := by omega
      have hsub_z : ((d2 - d1 - 1 : ℕ) : ℤ) = (d2 : ℤ) - d1 - 1 := by omega
      rw [hp_z, hr_z, hsub_z]
      ring
    have hpr_div : (p * r) / q = q + (d2 - d1 - 1) := by
      rw [hpr_decomp]
      exact div_eq_of_mul_add hq.pos (Nat.sub_lt hq.pos (Nat.mul_pos hd1_pos (by omega)))
    have hpr_div_mod : ((p * r) / q) % q = d2 - d1 - 1 := by
      rw [hpr_div, show q + (d2 - d1 - 1) = q * 1 + (d2 - d1 - 1) by ring]
      exact mod_eq_of_mul_add hd2_m_lt_q
    set t := (d2 * m) / q
    set s := (d2 * m) % q
    have hs_lt : s < q := Nat.mod_lt _ hq.pos
    have hd2m_eq : d2 * m = q * t + s := (Nat.div_add_mod (d2 * m) q).symm
    have hrm_decomp : r * m = q * (m + t) + s := by
      calc r * m = (q + d2) * m := by rw [hr_q_eq]
        _ = q * m + d2 * m := by ring
        _ = q * m + (q * t + s) := by rw [hd2m_eq]
        _ = q * (m + t) + s := by ring
    have hmt_lt_q : m + t < q := by
      have ht_le : q * t ≤ d2 * m := Nat.mul_div_le (d2 * m) q
      have h1 : 2 * q * (m + t) ≤ (q + d2) * p := by
        calc 2 * q * (m + t) = 2 * q * m + 2 * (q * t) := by ring
          _ ≤ 2 * q * m + 2 * (d2 * m) := by gcongr
          _ = (q + d2) * (2 * m) := by ring
          _ ≤ (q + d2) * p := Nat.mul_le_mul_left _ h2m_p
      have h2 : (q + d2) * p < 2 * q * q := by
        calc (q + d2) * p ≤ (2 * q) * p := Nat.mul_le_mul_right p (by omega)
          _ < (2 * q) * q := Nat.mul_lt_mul_of_pos_left hpq (by omega)
      exact Nat.lt_of_mul_lt_mul_left (h1.trans_lt h2)
    have hrm_div : (r * m) / q = m + t := by
      rw [hrm_decomp]
      exact div_eq_of_mul_add hq.pos hs_lt
    have hrm_div_mod : ((r * m) / q) % q = m + t := by
      rw [hrm_div]
      exact Nat.mod_eq_of_lt hmt_lt_q
    obtain ⟨_, hq_div_nd⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hq hq_sub
    obtain ⟨hq_div_mod_le, _⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hq hq_div_nd
    rw [hrm_div_mod, hpr_div_mod] at hq_div_mod_le
    have hm_lt_D : m < D := by
      calc m ≤ m + t := Nat.le_add_right _ _
        _ ≤ d2 - d1 - 1 := hq_div_mod_le
        _ < D := by omega
    have hDd2_lt_r : D * d2 < r := by
      calc D * d2 ≤ D * D := Nat.mul_le_mul_left D (by omega)
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
        _ < r := by omega
    have hpq_decomp : p * q = r * (r - D - d2) + D * d2 := by
      zify
      have hp_z : (p : ℤ) = (r : ℤ) - D := by omega
      have hq_z : (q : ℤ) = (r : ℤ) - d2 := by omega
      have hsub_z : ((r - D - d2 : ℕ) : ℤ) = (r : ℤ) - D - d2 := by omega
      rw [hp_z, hq_z, hsub_z]
      ring
    have hpq_mod : (p * q) % r = D * d2 := by
      rw [hpq_decomp]
      exact mod_eq_of_mul_add hDd2_lt_r
    have hd2m_pos : 0 < d2 * m := Nat.mul_pos (by omega) hm_pos
    have hd2m_lt_r : d2 * m < r := by
      calc d2 * m ≤ D * D := Nat.mul_le_mul (by omega) hm_lt_D.le
        _ = D ^ 2 := (sq D).symm
        _ < p := hD_sq_lt_p
        _ < r := by omega
    have hqm_decomp : q * m = r * (m - 1) + (r - d2 * m) := by
      zify [hm_pos, hd2m_lt_r.le]
      have hq_z : (q : ℤ) = (r : ℤ) - d2 := by omega
      rw [hq_z]
      ring
    have hqm_mod : (q * m) % r = r - d2 * m := by
      rw [hqm_decomp]
      exact mod_eq_of_mul_add (Nat.sub_lt hr.pos hd2m_pos)
    obtain ⟨hr_mod_le, _⟩ := mod_le_and_not_dvd_div_of_not_dvd_choose hr hr_sub
    rw [hqm_mod, hpq_mod] at hr_mod_le
    have hsum : d2 * m + D * d2 < r := by
      calc d2 * m + D * d2 ≤ D * D + D * D := by
            gcongr <;> omega
        _ = 2 * D ^ 2 := by ring
        _ < p := hD2_lt_p
        _ < r := by omega
    omega
