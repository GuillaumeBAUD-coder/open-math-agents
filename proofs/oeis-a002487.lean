import OMAStatements.S_oeis_a002487

namespace OMA.S_oeis_a002487_Proof

open OMA.S_oeis_a002487

private lemma a_zero : a 0 = 0 := by unfold a; rfl
private lemma a_one : a 1 = 1 := by unfold a; rfl

private lemma a_two_mul (k : ℕ) : a (2 * k) = a k := by
  cases k with
  | zero => simp [a_zero]
  | succ j =>
    have h : 2 * (j + 1) = (2 * j) + 2 := by omega
    rw [h]
    conv_lhs => unfold a
    have hmod : (2 * j + 2) % 2 = 0 := by omega
    have hdiv : (2 * j + 2) / 2 = j + 1 := by omega
    rw [if_pos hmod, hdiv]

private lemma a_two : a 2 = 1 := by
  rw [show (2 : ℕ) = 2 * 1 by rfl, a_two_mul, a_one]

private lemma a_two_mul_add_one (k : ℕ) : a (2 * k + 1) = a k + a (k + 1) := by
  cases k with
  | zero => simp [a_zero, a_one]
  | succ j =>
    have h : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
    rw [h]
    conv_lhs => unfold a
    have hmod : (2 * j + 1 + 2) % 2 ≠ 0 := by omega
    have hdiv : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    rw [if_neg hmod, hdiv]

private lemma a_pos : ∀ k : ℕ, 1 ≤ k → 1 ≤ a k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases eq_or_lt_of_le hk with rfl | hgt
    · simp [a_one]
    · by_cases hev : k % 2 = 0
      · have hk_eq : k = 2 * (k / 2) := by omega
        rw [hk_eq, a_two_mul]
        exact ih (k / 2) (by omega) (by omega)
      · have hk_eq : k = 2 * (k / 2) + 1 := by omega
        rw [hk_eq, a_two_mul_add_one]
        have h1 := ih (k / 2) (by omega) (by omega)
        omega

private lemma a_coprime : ∀ k : ℕ, Nat.Coprime (a k) (a (k + 1)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k'
    · simp [a_zero, a_one]
    · simp [a_one, a_two]
    · by_cases hev : (k' + 2) % 2 = 0
      · have hk_eq : k' + 2 = 2 * ((k' + 2) / 2) := by omega
        rw [hk_eq, a_two_mul, a_two_mul_add_one]
        exact Nat.coprime_self_add_right.mpr (ih ((k' + 2) / 2) (by omega))
      · have hk_eq : k' + 2 = 2 * ((k' + 2) / 2) + 1 := by omega
        have hk1_eq : 2 * ((k' + 2) / 2) + 1 + 1 = 2 * ((k' + 2) / 2 + 1) := by omega
        rw [hk_eq, hk1_eq, a_two_mul_add_one, a_two_mul]
        exact Nat.coprime_add_self_left.mpr (ih ((k' + 2) / 2) (by omega))

private lemma a_two_pow_mul (t k : ℕ) : a (2 ^ t * k) = a k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_assoc, a_two_mul, ih]

private lemma a_two_pow_mul_add_one (t k : ℕ) : a (2 ^ t * k + 1) = t * a k + a (k + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_assoc, a_two_mul_add_one, a_two_pow_mul, ih]
    ring

private def idx (u v : ℕ) : ℕ :=
  if u = 0 ∨ v = 0 then 0
  else if u = v then 1
  else if u < v then 2 * idx u (v - u)
  else 2 * idx (u - v) v + 1
termination_by u + v
decreasing_by all_goals omega

private lemma idx_spec :
    ∀ s u v : ℕ, u + v = s → 1 ≤ u → 1 ≤ v →
      1 ≤ idx u v ∧ idx u v < 2 ^ (u + v - 1) ∧
      (Nat.Coprime u v → a (idx u v) = u ∧ a (idx u v + 1) = v) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro u v hs hu hv
    unfold idx
    have h0 : ¬ (u = 0 ∨ v = 0) := by omega
    rw [if_neg h0]
    split_ifs with heq hlt
    · refine ⟨le_refl 1, ?_, ?_⟩
      · have h1 : 1 ≤ u + v - 1 := by omega
        have h2 : 2 ^ 1 ≤ 2 ^ (u + v - 1) := Nat.pow_le_pow_right (by omega) h1
        omega
      · intro hcop
        rw [heq] at hcop
        have hv1 : v = 1 := by simpa [Nat.Coprime] using hcop
        subst hv1
        subst heq
        simp [a_one, a_two]
    · obtain ⟨hpos, hlt_pow, ha_eq⟩ := ih (u + (v - u)) (by omega) u (v - u) rfl hu (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · have hle : u + (v - u) - 1 + 1 ≤ u + v - 1 := by omega
        calc 2 * idx u (v - u) < 2 * 2 ^ (u + (v - u) - 1) := by omega
          _ = 2 ^ (u + (v - u) - 1 + 1) := by rw [pow_succ]; ring
          _ ≤ 2 ^ (u + v - 1) := Nat.pow_le_pow_right (by omega) hle
      · intro hcop
        have hcop' : Nat.Coprime u (v - u) := by
          have hv_eq : u + (v - u) = v := by omega
          rw [← hv_eq] at hcop
          exact Nat.coprime_self_add_right.mp hcop
        obtain ⟨ha1, ha2⟩ := ha_eq hcop'
        rw [a_two_mul, a_two_mul_add_one, ha1, ha2]
        exact ⟨rfl, by omega⟩
    · obtain ⟨hpos, hlt_pow, ha_eq⟩ := ih ((u - v) + v) (by omega) (u - v) v rfl (by omega) hv
      refine ⟨by omega, ?_, ?_⟩
      · have hle : (u - v) + v - 1 + 1 ≤ u + v - 1 := by omega
        calc 2 * idx (u - v) v + 1 < 2 * 2 ^ ((u - v) + v - 1) := by omega
          _ = 2 ^ ((u - v) + v - 1 + 1) := by rw [pow_succ]; ring
          _ ≤ 2 ^ (u + v - 1) := Nat.pow_le_pow_right (by omega) hle
      · intro hcop
        have hcop' : Nat.Coprime (u - v) v := by
          have hu_eq : (u - v) + v = u := by omega
          rw [← hu_eq] at hcop
          exact Nat.coprime_add_self_left.mp hcop
        obtain ⟨ha1, ha2⟩ := ha_eq hcop'
        have h1 : 2 * idx (u - v) v + 1 + 1 = 2 * (idx (u - v) v + 1) := by omega
        rw [h1, a_two_mul_add_one, a_two_mul, ha1, ha2]
        exact ⟨by omega, rfl⟩

private lemma idx_a : ∀ k : ℕ, 1 ≤ k → idx (a k) (a (k + 1)) = k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases eq_or_lt_of_le hk with rfl | hgt
    · rw [a_one, a_two]
      unfold idx
      simp
    · by_cases hev : k % 2 = 0
      · have hk_eq : k = 2 * (k / 2) := by omega
        have hj1 : 1 ≤ k / 2 := by omega
        have hjpos : 1 ≤ a (k / 2) := a_pos _ hj1
        have hj1pos : 1 ≤ a (k / 2 + 1) := a_pos _ (by omega)
        conv_lhs => rw [hk_eq]
        rw [a_two_mul, a_two_mul_add_one]
        unfold idx
        have h0 : ¬ (a (k / 2) = 0 ∨ a (k / 2) + a (k / 2 + 1) = 0) := by omega
        have hne : a (k / 2) ≠ a (k / 2) + a (k / 2 + 1) := by omega
        have hlt : a (k / 2) < a (k / 2) + a (k / 2 + 1) := by omega
        rw [if_neg h0, if_neg hne, if_pos hlt]
        have hsub : a (k / 2) + a (k / 2 + 1) - a (k / 2) = a (k / 2 + 1) := by omega
        rw [hsub, ih (k / 2) (by omega) hj1]
        omega
      · have hk_eq : k = 2 * (k / 2) + 1 := by omega
        have hk1_eq : 2 * (k / 2) + 1 + 1 = 2 * (k / 2 + 1) := by omega
        have hj1 : 1 ≤ k / 2 := by omega
        have hjpos : 1 ≤ a (k / 2) := a_pos _ hj1
        have hj1pos : 1 ≤ a (k / 2 + 1) := a_pos _ (by omega)
        conv_lhs => rw [hk_eq, hk1_eq]
        rw [a_two_mul_add_one, a_two_mul]
        unfold idx
        have h0 : ¬ (a (k / 2) + a (k / 2 + 1) = 0 ∨ a (k / 2 + 1) = 0) := by omega
        have hne : a (k / 2) + a (k / 2 + 1) ≠ a (k / 2 + 1) := by omega
        have hlt : ¬ (a (k / 2) + a (k / 2 + 1) < a (k / 2 + 1)) := by omega
        rw [if_neg h0, if_neg hne, if_neg hlt]
        have hsub : a (k / 2) + a (k / 2 + 1) - a (k / 2 + 1) = a (k / 2) := by omega
        rw [hsub, ih (k / 2) (by omega) hj1]
        omega

private lemma idx_lt_two_pow_left {n v : ℕ} (hv : 1 ≤ v) (hvn : v < n) :
    idx n v < 2 ^ n := by
  unfold idx
  have h0 : ¬ (n = 0 ∨ v = 0) := by omega
  have hne : n ≠ v := by omega
  have hlt : ¬ (n < v) := by omega
  rw [if_neg h0, if_neg hne, if_neg hlt]
  have hspec := (idx_spec ((n - v) + v) (n - v) v rfl (by omega) hv).2.1
  have hsum : (n - v) + v - 1 = n - 1 := by omega
  rw [hsum] at hspec
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have hn1 : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn1, pow_succ]
    ring
  omega

private lemma a_eq_one_iff_pow_two : ∀ k : ℕ, 1 ≤ k → (a k = 1 ↔ ∃ t : ℕ, k = 2 ^ t) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    constructor
    · intro ha1
      rcases eq_or_lt_of_le hk with rfl | hgt
      · exact ⟨0, rfl⟩
      · by_cases hev : k % 2 = 0
        · have hk_eq : k = 2 * (k / 2) := by omega
          rw [hk_eq, a_two_mul] at ha1
          obtain ⟨t, ht⟩ := (ih (k / 2) (by omega) (by omega)).mp ha1
          exact ⟨t + 1, by rw [hk_eq, ht, pow_succ']⟩
        · have hk_eq : k = 2 * (k / 2) + 1 := by omega
          rw [hk_eq, a_two_mul_add_one] at ha1
          have h1 := a_pos (k / 2) (by omega)
          have h2 := a_pos (k / 2 + 1) (by omega)
          omega
    · rintro ⟨t, rfl⟩
      have h : 2 ^ t = 2 ^ t * 1 := by ring
      rw [h, a_two_pow_mul, a_one]

private lemma factor_two_pow_odd : ∀ k : ℕ, 1 ≤ k → ∃ t k₀ : ℕ, k₀ % 2 = 1 ∧ k = 2 ^ t * k₀ := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases hev : k % 2 = 0
    · obtain ⟨t, k₀, hodd, hEq⟩ := ih (k / 2) (by omega) (by omega)
      refine ⟨t + 1, k₀, hodd, ?_⟩
      rw [pow_succ', mul_assoc, ← hEq]
      omega
    · exact ⟨0, k, by omega, by simp⟩

private lemma pow_two_unique_exp {a b c d : ℕ} (ha : 2 ^ a ≤ b) (hb : b < 2 ^ (a + 1))
    (hc : 2 ^ c ≤ 2 ^ d * b) (hd : 2 ^ d * b < 2 ^ (c + 1)) : d + a = c := by
  have h1 : 2 ^ (d + a) < 2 ^ (c + 1) := by
    calc 2 ^ (d + a) = 2 ^ d * 2 ^ a := pow_add 2 d a
      _ ≤ 2 ^ d * b := Nat.mul_le_mul_left _ ha
      _ < 2 ^ (c + 1) := hd
  have h2 : 2 ^ c < 2 ^ (d + a + 1) := by
    calc 2 ^ c ≤ 2 ^ d * b := hc
      _ < 2 ^ d * 2 ^ (a + 1) := Nat.mul_lt_mul_of_pos_left hb (by positivity)
      _ = 2 ^ (d + (a + 1)) := (pow_add 2 d (a + 1)).symm
      _ = 2 ^ (d + a + 1) := by ring_nf
  have h1' : d + a < c + 1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h1
  have h2' : c < d + a + 1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp h2
  omega

theorem main_proof :
    ∀ m n : ℕ, 1 ≤ n → n ≤ m →
      ((Finset.Icc (2 ^ (m - 1)) (2 ^ m - 1)).filter fun k => a k = n).card = Nat.totient n := by
  intro m n hn hnm
  rcases eq_or_lt_of_le hn with rfl | hn2
  · -- Case n = 1
    have hset : ((Finset.Icc (2 ^ (m - 1)) (2 ^ m - 1)).filter fun k => a k = 1) =
        {2 ^ (m - 1)} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hle, hge⟩, ha1⟩
        have hk1 : 1 ≤ k := le_trans (Nat.one_le_pow _ _ (by omega)) hle
        obtain ⟨t, rfl⟩ := (a_eq_one_iff_pow_two k hk1).mp ha1
        have hlt : 2 ^ t < 2 ^ m := by
          have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by omega)
          omega
        have ht1 : m - 1 ≤ t := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle
        have ht2 : t < m := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
        have ht_eq : t = m - 1 := by omega
        rw [ht_eq]
      · rintro rfl
        have hpow_le : 2 ^ (m - 1) ≤ 2 ^ m - 1 := by
          have hm_eq : m = (m - 1) + 1 := by omega
          have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
          conv_rhs => rw [hm_eq, pow_succ]
          omega
        refine ⟨⟨le_refl _, hpow_le⟩, ?_⟩
        exact (a_eq_one_iff_pow_two _ (Nat.one_le_pow _ _ (by omega))).mpr ⟨m - 1, rfl⟩
    rw [hset, Finset.card_singleton, Nat.totient_one]
  · -- Case n ≥ 2
    rw [Nat.totient_eq_card_coprime]
    symm
    refine Finset.card_bij
      (fun v _ => 2 ^ (m - 1 - Nat.log 2 (idx n v)) * idx n v)
      ?_ ?_ ?_
    · -- Maps into the filtered interval
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_range] at hv
      obtain ⟨hvn, hcop⟩ := hv
      have hv1 : 1 ≤ v := by
        by_contra h0
        have hv0 : v = 0 := by omega
        rw [hv0, Nat.coprime_zero_right] at hcop
        omega
      have hspec := idx_spec (n + v) n v rfl (by omega) hv1
      have hk0_pos : 1 ≤ idx n v := hspec.1
      obtain ⟨hak0, hak0_1⟩ := hspec.2.2 hcop
      have hk0_lt : idx n v < 2 ^ n := idx_lt_two_pow_left hv1 hvn
      have hk0_lt_m : idx n v < 2 ^ m := lt_of_lt_of_le hk0_lt (Nat.pow_le_pow_right (by omega) hnm)
      have hlog_lt : Nat.log 2 (idx n v) < m := Nat.log_lt_of_lt_pow (by omega) hk0_lt_m
      have hd_le : 2 ^ Nat.log 2 (idx n v) ≤ idx n v := Nat.pow_log_le_self 2 (by omega)
      have hd_lt : idx n v < 2 ^ (Nat.log 2 (idx n v) + 1) :=
        Nat.lt_pow_succ_log_self (by omega) (idx n v)
      have hexp1 : m - 1 - Nat.log 2 (idx n v) + Nat.log 2 (idx n v) = m - 1 := by omega
      have hexp2 : m - 1 - Nat.log 2 (idx n v) + (Nat.log 2 (idx n v) + 1) = m := by omega
      have hlo : 2 ^ (m - 1) ≤ 2 ^ (m - 1 - Nat.log 2 (idx n v)) * idx n v := by
        calc 2 ^ (m - 1) = 2 ^ (m - 1 - Nat.log 2 (idx n v) + Nat.log 2 (idx n v)) := by rw [hexp1]
          _ = 2 ^ (m - 1 - Nat.log 2 (idx n v)) * 2 ^ Nat.log 2 (idx n v) := pow_add _ _ _
          _ ≤ 2 ^ (m - 1 - Nat.log 2 (idx n v)) * idx n v := Nat.mul_le_mul_left _ hd_le
      have hhi : 2 ^ (m - 1 - Nat.log 2 (idx n v)) * idx n v < 2 ^ m := by
        calc 2 ^ (m - 1 - Nat.log 2 (idx n v)) * idx n v
            < 2 ^ (m - 1 - Nat.log 2 (idx n v)) * 2 ^ (Nat.log 2 (idx n v) + 1) :=
              Nat.mul_lt_mul_of_pos_left hd_lt (by positivity)
          _ = 2 ^ (m - 1 - Nat.log 2 (idx n v) + (Nat.log 2 (idx n v) + 1)) := (pow_add _ _ _).symm
          _ = 2 ^ m := by rw [hexp2]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hlo, by omega⟩, ?_⟩
      rw [a_two_pow_mul, hak0]
    · -- Injective
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hv₁ hv₂
      have hv1_pos : 1 ≤ v₁ := by
        by_contra h0
        have hv0 : v₁ = 0 := by omega
        have hcop0 := hv₁.2
        rw [hv0, Nat.coprime_zero_right] at hcop0
        omega
      have hv2_pos : 1 ≤ v₂ := by
        by_contra h0
        have hv0 : v₂ = 0 := by omega
        have hcop0 := hv₂.2
        rw [hv0, Nat.coprime_zero_right] at hcop0
        omega
      obtain ⟨ha1, ha1'⟩ := (idx_spec (n + v₁) n v₁ rfl (by omega) hv1_pos).2.2 hv₁.2
      obtain ⟨ha2, ha2'⟩ := (idx_spec (n + v₂) n v₂ rfl (by omega) hv2_pos).2.2 hv₂.2
      have hmod := congrArg (fun k => a (k + 1) % n) heq
      rw [a_two_pow_mul_add_one, a_two_pow_mul_add_one, ha1, ha1', ha2, ha2'] at hmod
      rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
          Nat.mod_eq_of_lt hv₁.1, Nat.mod_eq_of_lt hv₂.1] at hmod
      exact hmod
    · -- Surjective
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hlo, hhi⟩, hak⟩ := hk
      have hk1 : 1 ≤ k := le_trans (Nat.one_le_pow _ _ (by omega)) hlo
      obtain ⟨t, k₀, hodd, hk_eq⟩ := factor_two_pow_odd k hk1
      have hk0_pos : 1 ≤ k₀ := by omega
      have hak0 : a k₀ = n := by rw [hk_eq, a_two_pow_mul] at hak; exact hak
      have hk0_gt1 : 1 < k₀ := by
        by_contra hle1
        have hk0_1 : k₀ = 1 := by omega
        rw [hk0_1, a_one] at hak0
        omega
      have hk0_odd_eq : k₀ = 2 * (k₀ / 2) + 1 := by omega
      have hj1 : 1 ≤ k₀ / 2 := by omega
      have hk0_succ_eq : k₀ + 1 = 2 * (k₀ / 2 + 1) := by omega
      let v := a (k₀ + 1)
      have hv_lt : v < n := by
        dsimp only [v]
        rw [hk0_succ_eq, a_two_mul, ← hak0]
        conv_rhs => rw [hk0_odd_eq]
        rw [a_two_mul_add_one]
        have hpos := a_pos (k₀ / 2) hj1
        omega
      have hcop : Nat.Coprime n v := by
        rw [← hak0]
        exact a_coprime k₀
      refine ⟨v, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hv_lt, hcop⟩
      · have hidx : idx n v = k₀ := by
          rw [← hak0]
          exact idx_a k₀ hk0_pos
        rw [hidx]
        have hd_le : 2 ^ Nat.log 2 k₀ ≤ k₀ := Nat.pow_log_le_self 2 (by omega)
        have hd_lt : k₀ < 2 ^ (Nat.log 2 k₀ + 1) := Nat.lt_pow_succ_log_self (by omega) k₀
        have hk_lt : 2 ^ t * k₀ < 2 ^ (m - 1 + 1) := by
          have hm1 : m - 1 + 1 = m := by omega
          rw [hm1, ← hk_eq]
          have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by omega)
          omega
        have hk_ge : 2 ^ (m - 1) ≤ 2 ^ t * k₀ := by rw [← hk_eq]; exact hlo
        have hsum := pow_two_unique_exp hd_le hd_lt hk_ge hk_lt
        have ht_eq : m - 1 - Nat.log 2 k₀ = t := by omega
        rw [ht_eq, ← hk_eq]

end OMA.S_oeis_a002487_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a002487.main :=
  OMA.S_oeis_a002487_Proof.main_proof
