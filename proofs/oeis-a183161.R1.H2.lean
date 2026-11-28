import OMAReductions.R_oeis_a183161_R1
import Mathlib

theorem OMA.a183161_split (a : ℕ → ℤ) (h0 : a 0 = 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1 + 1), a k * a (m + 1 - k) =
      2 * a (m + 1) + ∑ k ∈ Finset.range m, a (k + 1) * a (m - k) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.sub_self, h0, Nat.add_sub_add_right]
  ring

theorem OMA.solution : OMA.R_oeis_a183161_R1.H2 := by
  intro a b ha hb h n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha, hb]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hd := (h (m + 1)).dvd
    rw [OMA.a183161_split a ha, OMA.a183161_split b hb] at hd
    have hu : ∀ k, k < m + 1 → a k = b k + 4 * ((a k - b k) / 4) := by
      intro k hk
      have := Int.mul_ediv_cancel' (ih k hk)
      omega
    have hmid : ∑ k ∈ Finset.range m, a (k + 1) * a (m - k) =
        ∑ k ∈ Finset.range m, b (k + 1) * b (m - k)
        + 4 * ∑ k ∈ Finset.range m, ((a (k + 1) - b (k + 1)) / 4) * b (m - k)
        + 4 * ∑ k ∈ Finset.range m, b (k + 1) * ((a (m - k) - b (m - k)) / 4)
        + 16 * ∑ k ∈ Finset.range m, ((a (k + 1) - b (k + 1)) / 4) * ((a (m - k) - b (m - k)) / 4) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 := hu (k + 1) (by omega)
      have h2 := hu (m - k) (by omega)
      generalize (a (k + 1) - b (k + 1)) / 4 = x at h1 ⊢
      generalize (a (m - k) - b (m - k)) / 4 = y at h2 ⊢
      rw [h1, h2]
      ring
    have hrefl : ∑ k ∈ Finset.range m, b (k + 1) * ((a (m - k) - b (m - k)) / 4) =
        ∑ k ∈ Finset.range m, ((a (k + 1) - b (k + 1)) / 4) * b (m - k) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show m - 1 - k + 1 = m - k by omega, show m - (m - 1 - k) = k + 1 by omega]
      ring
    rw [hmid, hrefl] at hd
    obtain ⟨c, hc⟩ := hd
    omega
