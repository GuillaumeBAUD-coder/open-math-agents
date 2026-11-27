import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

-- Step Erdos317.erdos_317.variants.claim2.R1.H1: hypothesis H1 of reduction Erdos317.erdos_317.variants.claim2.R1
-- Credit: @volskew90
-- H1 := ∀ n : ℕ, 1 ≤ n → ∃ u : ℕ, n < u ∧ IsPrimePow u ∧ (Icc 1 n).lcm id = (Icc 1 (u - 1)).lcm id

theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  intro n hn
  obtain ⟨q, hnq, hq⟩ := Nat.exists_infinite_primes (n + 1)
  have hne : {u : ℕ | n < u ∧ IsPrimePow u}.Nonempty :=
    ⟨q, by omega, q, 1, Nat.prime_iff.mp hq, Nat.one_pos, pow_one q⟩
  set u := Nat.find hne with hu_def
  have hu : n < u ∧ IsPrimePow u := Nat.find_spec hne
  obtain ⟨hnu, hppu⟩ := hu
  have hmin : ∀ m, n < m → m < u → ¬ IsPrimePow m := by
    intro m h1 h2 h3
    have hle := Nat.find_min' hne (show m ∈ {u : ℕ | n < u ∧ IsPrimePow u} from ⟨h1, h3⟩)
    omega
  have key : ∀ m, n ≤ m → m ≤ u - 1 →
      (Finset.Icc 1 m).lcm id = (Finset.Icc 1 n).lcm id := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro _; rfl
    | succ m hnm ih =>
      intro hmu
      have hL := ih (by omega : m ≤ u - 1)
      have h2v : 2 ≤ m + 1 := by omega
      have hnp : ¬ IsPrimePow (m + 1) := hmin (m + 1) (by omega) (by omega)
      set p := (m + 1).minFac with hp_def
      have hpp : p.Prime := Nat.minFac_prime (by omega : m + 1 ≠ 1)
      have hpP : Prime p := Nat.prime_iff.mp hpp
      have he : 0 < (m + 1).factorization p := by
        by_contra hz
        push_neg at hz
        have hz0 : (m + 1).factorization p = 0 := by omega
        rw [Nat.factorization_eq_zero_iff] at hz0
        rcases hz0 with h | h | h
        · exact h hpp
        · exact h (Nat.minFac_dvd _)
        · omega
      set a := p ^ ((m + 1).factorization p) with ha_def
      have ha_dvd : a ∣ m + 1 :=
        (Nat.Prime.pow_dvd_iff_le_factorization hpp (by omega : m + 1 ≠ 0)).mpr le_rfl
      set b := (m + 1) / a with hb_def
      have hab : a * b = m + 1 := Nat.mul_div_cancel' ha_dvd
      have ha1 : 1 < a := by
        have h1 : p ^ 1 ≤ a := Nat.pow_le_pow_right hpp.pos he
        rw [pow_one] at h1
        have := hpp.two_le
        omega
      have hb1 : 1 < b := by
        by_contra hbc
        push_neg at hbc
        have hb1' : b = 1 := by
          rcases Nat.eq_zero_or_pos b with h0 | hpos
          · rw [h0, mul_zero] at hab; omega
          · omega
        rw [hb1', mul_one] at hab
        exact hnp ⟨p, (m + 1).factorization p, hpP, he, ha_def ▸ hab⟩
      have hpb : ¬ p ∣ b := by
        intro hpb
        have h1 : a * p ∣ a * b := Nat.mul_dvd_mul_left a hpb
        rw [hab] at h1
        have e1 : p ^ ((m + 1).factorization p + 1) = a * p := by rw [pow_succ, ha_def]
        rw [← e1] at h1
        have hle := (Nat.Prime.pow_dvd_iff_le_factorization hpp (by omega : m + 1 ≠ 0)).mp h1
        omega
      have hco : Nat.Coprime a b := by
        rw [ha_def, Nat.coprime_pow_left_iff he, Nat.Prime.coprime_iff_not_dvd hpp]
        exact hpb
      have h2a : 2 * a ≤ m + 1 := by nlinarith [hab, hb1, ha1]
      have h2b : 2 * b ≤ m + 1 := by nlinarith [hab, hb1, ha1]
      have ham : a ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hbm : b ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hadvd : a ∣ (Finset.Icc 1 m).lcm id := Finset.dvd_lcm ham
      have hbdvd : b ∣ (Finset.Icc 1 m).lcm id := Finset.dvd_lcm hbm
      have hvdvd : m + 1 ∣ (Finset.Icc 1 m).lcm id :=
        hab ▸ hco.mul_dvd_of_dvd_of_dvd hadvd hbdvd
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.lcm_insert, id_eq, ← hL]
      exact Nat.dvd_antisymm
        (lcm_dvd_iff.mpr ⟨hL ▸ hvdvd, dvd_refl _⟩) (dvd_lcm_right _ _)
  exact ⟨u, hnu, hppu, (key (u - 1) (by omega) le_rfl).symm⟩
