import OMAReductions.R_OeisA259667_conjecture_1_R2

-- Step OeisA259667.conjecture_1.R2.H1: hypothesis H1 of reduction OeisA259667.conjecture_1.R2
-- Credit: @Raimo33

namespace OMAStep

def good (m : ℕ) : Bool := (List.range 30).any fun j => (2 * 4 ^ m - 1) / 3 ^ j % 3 == 2

def allGood (a : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => good (a + k) && allGood a k

theorem allGood_spec (a : ℕ) : ∀ k, allGood a k = true → ∀ i, i < k → good (a + i) = true := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    simp only [allGood, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

theorem good_spec (m : ℕ) (h : good m = true) : ∃ j : ℕ, (2 * 4 ^ m - 1) / 3 ^ j % 3 = 2 := by
  simp only [good, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨j, -, hj⟩ := h
  exact ⟨j, hj⟩

theorem c0 : allGood 3 497 = true := by decide +kernel
theorem c1 : allGood 500 500 = true := by decide +kernel
theorem c2 : allGood 1000 500 = true := by decide +kernel
theorem c3 : allGood 1500 500 = true := by decide +kernel
theorem c4 : allGood 2000 500 = true := by decide +kernel
theorem c5 : allGood 2500 500 = true := by decide +kernel
theorem c6 : allGood 3000 500 = true := by decide +kernel
theorem c7 : allGood 3500 500 = true := by decide +kernel
theorem c8 : allGood 4000 500 = true := by decide +kernel
theorem c9 : allGood 4500 500 = true := by decide +kernel
theorem c10 : allGood 5000 500 = true := by decide +kernel
theorem c11 : allGood 5500 500 = true := by decide +kernel
theorem c12 : allGood 6000 562 = true := by decide +kernel

end OMAStep

open OMAStep in
theorem OMA.solution : OMA.R_OeisA259667_conjecture_1_R2.H1 := by
  intro m h3 h6561
  apply good_spec
  have key : ∀ a k, allGood a k = true → a ≤ m → m < a + k → good m = true := by
    intro a k h ha hb
    have := allGood_spec a k h (m - a) (by omega)
    rwa [Nat.add_sub_cancel' ha] at this
  by_cases e0 : m < 500
  · exact key 3 497 c0 (by omega) (by omega)
  by_cases e1 : m < 1000
  · exact key 500 500 c1 (by omega) (by omega)
  by_cases e2 : m < 1500
  · exact key 1000 500 c2 (by omega) (by omega)
  by_cases e3 : m < 2000
  · exact key 1500 500 c3 (by omega) (by omega)
  by_cases e4 : m < 2500
  · exact key 2000 500 c4 (by omega) (by omega)
  by_cases e5 : m < 3000
  · exact key 2500 500 c5 (by omega) (by omega)
  by_cases e6 : m < 3500
  · exact key 3000 500 c6 (by omega) (by omega)
  by_cases e7 : m < 4000
  · exact key 3500 500 c7 (by omega) (by omega)
  by_cases e8 : m < 4500
  · exact key 4000 500 c8 (by omega) (by omega)
  by_cases e9 : m < 5000
  · exact key 4500 500 c9 (by omega) (by omega)
  by_cases e10 : m < 5500
  · exact key 5000 500 c10 (by omega) (by omega)
  by_cases e11 : m < 6000
  · exact key 5500 500 c11 (by omega) (by omega)
  · exact key 6000 562 c12 (by omega) (by omega)
