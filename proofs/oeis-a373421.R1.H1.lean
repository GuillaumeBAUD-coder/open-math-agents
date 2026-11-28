import OMAReductions.R_oeis_a373421_R1

namespace OMA.Sol_oeis_a373421

open OMA.S_oeis_a373421

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

/-- Witnesses `m`, one for each `k` with a polygonal number not above 2671. -/
def W : List ℕ := [2, 73, 4, 2, 2, 8, 43, 2, 2, 4, 13, 2, 2, 61, 32, 2, 2, 4, 4, 2, 2, 43, 29, 2, 2, 40, 4, 2, 2, 32, 16, 2, 2, 4, 40, 2, 2, 29, 8, 2, 2, 4, 4]

theorem table : ∀ k < 43, polygonal k ≤ 2671 →
    W.getD k 0 ≤ 2671 - polygonal k ∧
    ∑ i ∈ (Finset.range (W.getD k 0 + 1)).filter (· ∣ (2671 - polygonal k)), i < W.getD k 0 := by
  decide +kernel

end OMA.Sol_oeis_a373421

open OMA.S_oeis_a373421 OMA.Sol_oeis_a373421 in
theorem OMA.solution : OMA.R_oeis_a373421_R1.H1 := by
  rintro ⟨p, k, hp, he⟩
  have hpk : polygonal k ≤ 2671 := by omega
  have hk : k < 43 := by
    by_contra hk'
    have hk := Nat.le_of_not_lt hk'
    have h1 : 2 * polygonal k + 1 ≥ k * (3 * k - 1) := by unfold polygonal; omega
    have h2 : 3 * k - 1 ≥ 128 := by omega
    have h3 : 43 * 128 ≤ k * (3 * k - 1) := Nat.mul_le_mul hk h2
    omega
  obtain ⟨hm, hs⟩ := table k hk hpk
  have hpe : p = 2671 - polygonal k := by omega
  subst hpe
  exact not_practical_of hm hs hp
