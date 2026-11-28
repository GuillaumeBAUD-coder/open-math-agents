import OMAReductions.R_oeis_a373444_R1

namespace OMA.Sol_oeis_a373444

open OMA.S_oeis_a373444

/-- If the divisors of `p` up to `m` sum to less than `m`, then `m` is not a sum of distinct
divisors of `p`, so `p` is not practical. -/
theorem not_practical_of {p m : ℕ} (hm : m ≤ p)
    (h : ∑ i ∈ (Finset.range (m + 1)).filter (· ∣ p), i < m) : ¬ IsPractical p := by
  rintro ⟨_, hall⟩
  obtain ⟨s, hs, hsum⟩ := hall m hm
  have hsub : s ⊆ (Finset.range (m + 1)).filter (· ∣ p) := by
    intro x hx
    have hxle : x ≤ m := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) hx
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.dvd_of_mem_divisors (hs hx)⟩
  have := Finset.sum_le_sum_of_subset (f := fun i : ℕ => i) hsub
  rw [hsum] at this
  omega

/-- Witnesses `m`, one for each `k` with a polygonal number not above 79445. -/
def W : List ℕ := [2, 8, 4, 2, 2, 4, 8, 2, 2, 16, 4, 2, 2, 4, 256, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 379, 4, 2, 2, 4, 91, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 16, 4, 2, 2, 4, 32, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 32, 4, 2, 2, 4, 16, 2, 2, 43, 4, 2, 2, 4, 218, 2, 2, 16, 4, 2, 2, 4, 64, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 256, 4, 2, 2, 4, 16, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 91, 4, 2, 2, 4, 187, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 32, 4, 2, 2, 4, 16, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 16, 4, 2, 2, 4, 128, 2, 2, 218, 4, 2, 2, 4, 43, 2, 2, 64, 4, 2, 2, 4, 16, 2, 2, 8, 4, 2, 2, 4, 8, 2, 2, 16, 4, 2, 2, 4, 32, 2, 2, 8, 4]

theorem table : ∀ k < 179, polygonal k ≤ 79445 →
    W.getD k 0 ≤ 79445 - polygonal k ∧
    ∑ i ∈ (Finset.range (W.getD k 0 + 1)).filter (· ∣ (79445 - polygonal k)), i < W.getD k 0 := by
  decide +kernel

end OMA.Sol_oeis_a373444

open OMA.S_oeis_a373444 OMA.Sol_oeis_a373444 in
theorem OMA.solution : OMA.R_oeis_a373444_R1.H1 := by
  rintro ⟨p, k, hp, he⟩
  have hpk : polygonal k ≤ 79445 := by omega
  have hk : k < 179 := by
    by_contra hk'
    have hk := Nat.le_of_not_lt hk'
    have h1 : 2 * polygonal k + 1 ≥ k * (5 * k - 3) := by unfold polygonal; omega
    have h2 : 5 * k - 3 ≥ 892 := by omega
    have h3 : 179 * 892 ≤ k * (5 * k - 3) := Nat.mul_le_mul hk h2
    omega
  obtain ⟨hm, hs⟩ := table k hk hpk
  have hpe : p = 79445 - polygonal k := by omega
  subst hpe
  exact not_practical_of hm hs hp
