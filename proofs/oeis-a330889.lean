import OMAStatements.S_oeis_a330889
import Mathlib

namespace A330889Proof

open OMA.S_oeis_a330889

theorem two_e (k : ℕ) : 2 * (k * (3 * k - 1) / 2) + k = 3 * k * k := by
  have hd : 2 ∣ k * (3 * k - 1) := by
    rcases Nat.even_or_odd k with h | h
    · exact Dvd.dvd.mul_right h.two_dvd _
    · obtain ⟨j, rfl⟩ := h
      exact Dvd.dvd.mul_left ⟨3 * j + 1, by omega⟩ _
  rw [Nat.mul_div_cancel' hd]
  rcases k with _ | k
  · simp
  · have : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
    rw [this]; ring

theorem parts_sum (m k : ℕ) : 2 * (parts m k).sum + 3 * k = 2 * k * m + 3 * k * k := by
  induction k with
  | zero => simp [parts]
  | succ k ih =>
    have h : (parts m (k + 1)).sum = (parts m k).sum + (m + 3 * k) := by
      simp [parts, List.range_succ]
    rw [h]
    nlinarith [ih]

theorem inner (n k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.Icc 1 n, (if (parts m k).sum = n then k else 0)) =
      if k * (3 * k - 1) / 2 ≤ n ∧ k ∣ n - k * (3 * k - 1) / 2 then k else 0 := by
  have he := two_e k
  generalize k * (3 * k - 1) / 2 = e at he
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have key : ∀ m, (parts m k).sum = n ↔ k * m + e = n + k := by
    intro m
    have := parts_sum m k
    constructor
    · intro h; rw [h] at this; nlinarith
    · intro h; nlinarith
  simp only [key]
  split_ifs with hc
  · obtain ⟨he', j, hj⟩ := hc
    have hn : n = e + k * j := by omega
    have hjn : j + 1 ≤ n := by nlinarith
    rw [Finset.sum_eq_single (j + 1)]
    · rw [if_pos]; rw [hn]; ring
    · intro m _ hm
      rw [if_neg]
      intro h
      apply hm
      have : k * m = k * (j + 1) := by rw [hn] at h; linarith
      exact Nat.eq_of_mul_eq_mul_left hk this
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨by omega, hjn⟩) h
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    apply hc
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have h2 : k * i + e = n := by linarith
    exact ⟨by omega, ⟨i, by omega⟩⟩

theorem inv_eq (k : ℕ) (hk : 1 ≤ k) :
    (1 - PowerSeries.X ^ k : PowerSeries ℚ)⁻¹ =
      PowerSeries.mk (fun j => if k ∣ j then (1 : ℚ) else 0) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · ext n
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_one]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn, PowerSeries.coeff_mk]
      have h1 : k ∣ n - k ↔ k ∣ n := by
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c + 1, by rw [Nat.mul_succ]; omega⟩
        · intro h
          first
            | exact Nat.dvd_sub h dvd_rfl
            | exact Nat.dvd_sub' h dvd_rfl
      have h0 : n ≠ 0 := by omega
      rw [if_neg h0]
      by_cases hd : k ∣ n
      · rw [if_pos hd, if_pos (h1.mpr hd)]; ring
      · rw [if_neg hd, if_neg (fun h => hd (h1.mp h))]; ring
    · rw [if_neg hkn]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg h0, if_neg, sub_zero]
        intro hd
        exact hkn (Nat.le_of_dvd (by omega) hd)
  · have hk0 : k ≠ 0 := by omega
    simp [hk0]

theorem term (n k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.coeff n ((k : PowerSeries ℚ) * PowerSeries.X ^ (k * (3 * k - 1) / 2)
        * (1 - PowerSeries.X ^ k)⁻¹) =
      (((if k * (3 * k - 1) / 2 ≤ n ∧ k ∣ n - k * (3 * k - 1) / 2 then k else 0 : ℕ)) : ℚ) := by
  rw [inv_eq k hk, ← map_natCast (PowerSeries.C (R := ℚ)) k, mul_assoc, PowerSeries.coeff_C_mul,
    mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_mul_X_pow']
  by_cases h1 : k * (3 * k - 1) / 2 ≤ n
  · rw [if_pos h1, PowerSeries.coeff_mk]
    by_cases h2 : k ∣ n - k * (3 * k - 1) / 2
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]; simp
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]; simp
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]; simp

theorem main_proof : ∀ n N : ℕ, n ≤ N →
    (a n : ℚ) = PowerSeries.coeff n (∑ k ∈ Finset.Icc 1 N,
      (k : PowerSeries ℚ) * PowerSeries.X ^ (k * (3 * k - 1) / 2)
        * (1 - PowerSeries.X ^ k)⁻¹) := by
  intro n N hnN
  rw [map_sum, Finset.sum_congr rfl (fun k hk => term n k (Finset.mem_Icc.mp hk).1),
    ← Nat.cast_sum]
  congr 1
  unfold a
  rw [Finset.sum_congr rfl (fun k hk => inner n k (Finset.mem_Icc.mp hk).1)]
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk hkn
    rw [Finset.mem_Icc] at hk hkn
    rw [if_neg]
    rintro ⟨h, -⟩
    have he := two_e k
    have hkk : k ≤ k * k := Nat.le_mul_self k
    have : k ≤ k * (3 * k - 1) / 2 := by nlinarith
    omega

end A330889Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a330889.main := A330889Proof.main_proof
