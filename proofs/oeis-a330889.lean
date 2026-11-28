import OMAStatements.S_oeis_a330889
import Mathlib

namespace OMA.S_oeis_a330889

lemma parts_sum (m k : ℕ) : 2 * (parts m k).sum + 3 * k = 2 * k * m + 3 * k * k := by
  induction k with
  | zero => simp [parts]
  | succ k ih =>
    have : parts m (k+1) = parts m k ++ [m + 3 * k] := by
      simp [parts, List.range_succ]
    rw [this, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    nlinarith [ih]

lemma e_two (k : ℕ) : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := by
  apply Nat.mul_div_cancel'
  apply even_iff_two_dvd.mp
  rcases Nat.even_or_odd k with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · obtain ⟨j, hj⟩ := h
    exact Nat.even_mul.mpr (Or.inr ⟨3 * j + 1, by omega⟩)

lemma inv_coeff (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    PowerSeries.coeff j ((1 - PowerSeries.X ^ k : PowerSeries ℚ)⁻¹) = if k ∣ j then 1 else 0 := by
  have h : (1 - PowerSeries.X ^ k : PowerSeries ℚ)⁻¹ =
      PowerSeries.mk (fun i => if k ∣ i then (1:ℚ) else 0) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]; simp)]
    ext j
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, mul_comm, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
    by_cases hj : j < k
    · have : ¬ k ≤ j := by omega
      simp only [this, if_false, sub_zero]
      by_cases h0 : j = 0
      · subst h0; simp
      · have : ¬ k ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
        simp [this, h0]
    · have hk' : k ≤ j := by omega
      have hj0 : j ≠ 0 := by omega
      simp only [hk', if_true, hj0, if_false, PowerSeries.coeff_mk]
      by_cases hd : k ∣ j
      · have : k ∣ j - k := Nat.dvd_sub hd dvd_rfl
        simp [hd, this]
      · have : ¬ k ∣ j - k := fun h2 => hd (by have := Nat.dvd_add h2 (dvd_refl k); rwa [Nat.sub_add_cancel hk'] at this)
        simp [hd, this]
  rw [h, PowerSeries.coeff_mk]

lemma e_fact (k : ℕ) (hk : 1 ≤ k) : 2 * (k * (3 * k - 1) / 2) + k = 3 * k * k := by
  rw [e_two]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have : 3 * (j + 1) - 1 = 3 * j + 2 := by omega
  rw [this]; ring

lemma key (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (parts m k).sum = n ↔ (k * (3 * k - 1) / 2 ≤ n ∧ n - k * (3 * k - 1) / 2 = k * (m - 1)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 := parts_sum (m'+1) k
  have h2 := e_fact k hk
  have h3 : (parts (m'+1) k).sum = k * m' + k * (3 * k - 1) / 2 := by nlinarith
  simp only [Nat.add_sub_cancel]
  rw [h3]
  generalize k * m' = t
  generalize k * (3 * k - 1) / 2 = e
  omega

lemma inner (n k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Icc 1 n, (if (parts m k).sum = n then k else 0) =
      if (k * (3 * k - 1) / 2 ≤ n ∧ k ∣ n - k * (3 * k - 1) / 2) then k else 0 := by
  have h2 := e_fact k hk
  have he1 : 1 ≤ k * (3 * k - 1) / 2 := by nlinarith
  split_ifs with hc
  · obtain ⟨hle, q, hq⟩ := hc
    have hqn : q + 1 ≤ n := by
      have : q ≤ k * q := Nat.le_mul_of_pos_left q (by omega)
      omega
    rw [Finset.sum_eq_single (q + 1)]
    · rw [if_pos]
      rw [key n k (q+1) hk (by omega)]
      refine ⟨hle, ?_⟩
      simpa using hq
    · intro m hm hne
      rw [if_neg]
      intro h
      rw [key n k m hk (Finset.mem_Icc.mp hm).1] at h
      obtain ⟨_, h4⟩ := h
      have : k * (m - 1) = k * q := by omega
      have := Nat.eq_of_mul_eq_mul_left (by omega) this
      have := (Finset.mem_Icc.mp hm).1
      omega
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, hqn⟩) h
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    rw [key n k m hk (Finset.mem_Icc.mp hm).1] at h
    exact hc ⟨h.1, ⟨m - 1, h.2⟩⟩

lemma coeff_term (n k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.coeff n ((k : PowerSeries ℚ) * PowerSeries.X ^ (k * (3 * k - 1) / 2)
        * (1 - PowerSeries.X ^ k)⁻¹) =
      if (k * (3 * k - 1) / 2 ≤ n ∧ k ∣ n - k * (3 * k - 1) / 2) then (k : ℚ) else 0 := by
  have hc : (k : PowerSeries ℚ) = PowerSeries.C (k : ℚ) := by simp
  rw [hc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases h : k * (3 * k - 1) / 2 ≤ n
  · rw [if_pos h, inv_coeff k hk]
    by_cases hd : k ∣ n - k * (3 * k - 1) / 2 <;> simp [h, hd]
  · simp [h]

theorem main_aux : type_of% @OMA.S_oeis_a330889.main := by
  intro n N hnN
  unfold a
  rw [map_sum]
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hnN
  rw [← Finset.sum_subset hsub]
  · push_cast
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    rw [coeff_term n k hk1]
    have h' := congrArg (Nat.cast : ℕ → ℚ) (inner n k hk1)
    push_cast at h'
    rw [h']
  · intro k hk hk'
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkn : n < k := by
      by_contra h; exact hk' (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
    rw [coeff_term n k hk1, if_neg]
    have h2 := e_fact k hk1
    rintro ⟨h, _⟩
    nlinarith

end OMA.S_oeis_a330889

theorem OMA.solution : type_of% @OMA.S_oeis_a330889.main := OMA.S_oeis_a330889.main_aux
