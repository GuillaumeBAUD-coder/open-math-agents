import OMAStatements.S_oeis_a129654

namespace OMA.S_oeis_a129654

open PowerSeries

lemma coeff_inv_one_sub (t : ℕ) (ht : 0 < t) (i : ℕ) :
    PowerSeries.coeff i ((1 - X ^ t : ℚ⟦X⟧)⁻¹) = if t ∣ i then 1 else 0 := by
  have h : (1 - X ^ t : ℚ⟦X⟧) * (PowerSeries.mk (fun i => if t ∣ i then (1:ℚ) else 0)) = 1 := by
    ext i
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, mul_comm, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_one]
    by_cases hi : t ≤ i
    · simp only [hi, if_true, PowerSeries.coeff_mk]
      by_cases h1 : t ∣ i
      · have h2 : t ∣ i - t := Nat.dvd_sub h1 (dvd_refl t)
        have : i ≠ 0 := by
          rintro rfl; omega
        simp [h1, h2, this]
      · have h2 : ¬ t ∣ i - t := fun h2 => h1 (by
          have := Nat.dvd_add h2 (dvd_refl t); rwa [Nat.sub_add_cancel hi] at this)
        have : i ≠ 0 := by rintro rfl; exact h1 (dvd_zero _)
        simp [h1, h2, this]
    · simp only [hi, if_false]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp
      · have : ¬ t ∣ i := fun hd => hi (Nat.le_of_dvd h0 hd)
        simp [h0.ne', this]
  have : (1 - X ^ t : ℚ⟦X⟧)⁻¹ = PowerSeries.mk (fun i => if t ∣ i then (1:ℚ) else 0) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one]
    · rw [mul_comm]; exact h
    · simp [zero_pow ht.ne']
  rw [this, PowerSeries.coeff_mk]

lemma tri_two (k : ℕ) : k * (k + 1) = 2 * (k * (k + 1) / 2) := by
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self k
  omega

lemma tri_pos (k : ℕ) (hk : 1 ≤ k) : 0 < k * (k + 1) / 2 := by
  have := tri_two k
  have : 0 < k * (k + 1) := Nat.mul_pos (by omega) (by omega)
  omega

lemma polygonal_eq (j k : ℕ) :
    polygonal (j + 2) (k + 1) = ((j * (k * (k + 1) / 2) + k + 1 : ℕ) : ℤ) := by
  have h := tri_two k
  generalize k * (k + 1) / 2 = T at h ⊢
  unfold polygonal
  have e : ((k + 1 : ℕ) : ℤ) * ((((j + 2 : ℕ) : ℤ) - 2) * ((k + 1 : ℕ) : ℤ) - (((j + 2 : ℕ) : ℤ) - 4))
      = 2 * ((j * T + k + 1 : ℕ) : ℤ) := by
    have h' : (k : ℤ) * (k + 1) = 2 * T := by exact_mod_cast h
    push_cast
    linear_combination (j : ℤ) * h'
  rw [e]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

end OMA.S_oeis_a129654

open PowerSeries OMA.S_oeis_a129654 in
theorem OMA.solution : type_of% @OMA.S_oeis_a129654.main := by
  intro n hn
  have hcoef : PowerSeries.coeff n
      (∑ k ∈ Finset.Icc 1 n, (X : ℚ⟦X⟧) * X ^ k * (1 - X ^ (k * (k + 1) / 2))⁻¹)
      = ((Finset.filter (fun k => k * (k + 1) / 2 ∣ n - 1 - k) (Finset.Ico 1 n)).card : ℚ) := by
    rw [map_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 n, PowerSeries.coeff n
        ((X : ℚ⟦X⟧) * X ^ k * (1 - X ^ (k * (k + 1) / 2))⁻¹)
        = if (1 ≤ k ∧ k < n) ∧ k * (k + 1) / 2 ∣ n - 1 - k then 1 else 0 := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
      have hpos := tri_pos k hk1
      rw [← pow_succ', PowerSeries.coeff_X_pow_mul', coeff_inv_one_sub _ hpos]
      have e : n - (k + 1) = n - 1 - k := by omega
      rw [e]
      by_cases h1 : k + 1 ≤ n
      · by_cases h2 : k * (k + 1) / 2 ∣ n - 1 - k
        · simp [h1, h2, hk1, Nat.lt_of_succ_le h1]
        · simp [h1, h2]
      · have : ¬ (1 ≤ k ∧ k < n) := by omega
        simp [h1, this]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    congr 2
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · intro h
      exact ⟨⟨h.2.1.1, h.2.1.2⟩, h.2.2⟩
    · intro h
      exact ⟨⟨h.1.1, by omega⟩, ⟨h.1, h.2⟩⟩
  rw [hcoef]
  unfold a
  have hset : {p : ℕ × ℕ | 1 < p.1 ∧ 1 < p.2 ∧ polygonal p.1 p.2 = n} =
      (fun k => ((n - 1 - k) / (k * (k + 1) / 2) + 2, k + 1)) ''
        ((Finset.filter (fun k => k * (k + 1) / 2 ∣ n - 1 - k) (Finset.Ico 1 n) : Finset ℕ) : Set ℕ) := by
    ext ⟨m, r⟩
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨hm, hr, hp⟩
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      rw [polygonal_eq] at hp
      have hp' : j * (k * (k + 1) / 2) + k + 1 = n := by exact_mod_cast hp
      have hpos := tri_pos k (by omega)
      have hd : n - 1 - k = (k * (k + 1) / 2) * j := by rw [mul_comm]; omega
      refine ⟨k, ⟨⟨by omega, ?_⟩, ?_⟩, ?_, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; have := tri_two k; simp at hp'; nlinarith
        · nlinarith [Nat.mul_le_mul_left (k * (k + 1) / 2) h0]
      · rw [hd]; exact dvd_mul_right _ _
      · rw [hd, Nat.mul_div_cancel_left _ hpos]
    · rintro ⟨k, ⟨⟨k1, k2⟩, k3⟩, h1, h2⟩
      obtain ⟨c, hc⟩ := k3
      have hpos := tri_pos k k1
      rw [hc, Nat.mul_div_cancel_left _ hpos] at h1
      subst h2
      refine ⟨by omega, by omega, ?_⟩
      rw [← h1, polygonal_eq]
      have : c * (k * (k + 1) / 2) + k + 1 = n := by
        rw [mul_comm]; omega
      rw [this]
  rw [hset, Set.ncard_image_of_injOn, Set.ncard_coe_finset]
  intro x _ y _ hxy
  simp only [Prod.mk.injEq] at hxy
  omega

