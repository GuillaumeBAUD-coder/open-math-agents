import OMAReductions.R_OeisA259667_conjecture_1_R2

-- Step OeisA259667.conjecture_1.R2.H1: hypothesis H1 of reduction OeisA259667.conjecture_1.R2
-- Credit: @t-roscommon
-- H1 := ∀ m : ℕ, 3 ≤ m → m ≤ 6561 → ∃ j : ℕ, (2 * 4 ^ m - 1) / 3 ^ j % 3 = 2

/-!
The lowest 30 ternary digits of `N` only depend on `N % 3 ^ 30`, and
`2 * 4 ^ (m + 1) - 1 = 4 * (2 * 4 ^ m - 1) + 3`. So the kernel scans the residues
`(2 * 4 ^ m - 1) % 3 ^ 30`, which stay below `3 ^ 30`, and finds a digit `2` among the
lowest 30 digits for every `m` in range (the first one is always at position 28 or lower).
-/

namespace A259667Step

/-- The modulus `3 ^ 30`. -/
def M : ℕ := 205891132094649

theorem M_eq : (3 : ℕ) ^ 30 = M := by norm_num [M]

/-- Some digit among the lowest `f` ternary digits of `x` equals `2`. -/
def hasTwo : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, x => x % 3 == 2 || hasTwo f (x / 3)

theorem hasTwo_spec : ∀ f x, hasTwo f x = true → ∃ j, j < f ∧ x / 3 ^ j % 3 = 2 := by
  intro f
  induction f with
  | zero => intro x h; simp [hasTwo] at h
  | succ f ih =>
    intro x h
    simp only [hasTwo, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨j, hj, h⟩ := ih _ h
      refine ⟨j + 1, by omega, ?_⟩
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      exact h

/-- Digits below position 30 are unchanged by reducing modulo `3 ^ 30`. -/
theorem digit_mod (N j : ℕ) (hj : j < 30) : N % M / 3 ^ j % 3 = N / 3 ^ j % 3 := by
  have hd : 3 ^ j * 3 ∣ M := by
    rw [← M_eq, ← pow_succ]
    exact pow_dvd_pow 3 (by omega)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd]

theorem step (m : ℕ) : (2 * 4 ^ (m + 1) - 1) % M = (4 * ((2 * 4 ^ m - 1) % M) + 3) % M := by
  have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [pow_succ']
  have h3 : 2 * 4 ^ (m + 1) - 1 = 4 * (2 * 4 ^ m - 1) + 3 := by omega
  rw [h3]
  unfold M
  omega

/-- Check `n` consecutive residues, starting from `x`. -/
def scan : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, x => hasTwo 30 x && scan n ((4 * x + 3) % M)

theorem scan_spec : ∀ n m, scan n ((2 * 4 ^ m - 1) % M) = true →
    ∀ i, i < n → hasTwo 30 ((2 * 4 ^ (m + i) - 1) % M) = true := by
  intro n
  induction n with
  | zero => intro m _ i hi; omega
  | succ n ih =>
    intro m h i hi
    simp only [scan, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have h' := ih (m + 1) (by rw [step]; exact h.2) i (by omega)
      rwa [show m + 1 + i = m + (i + 1) by omega] at h'

set_option maxRecDepth 20000 in
theorem c0 : scan 1000 ((2 * 4 ^ (3 + 1000 * 0) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c1 : scan 1000 ((2 * 4 ^ (3 + 1000 * 1) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c2 : scan 1000 ((2 * 4 ^ (3 + 1000 * 2) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c3 : scan 1000 ((2 * 4 ^ (3 + 1000 * 3) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c4 : scan 1000 ((2 * 4 ^ (3 + 1000 * 4) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c5 : scan 1000 ((2 * 4 ^ (3 + 1000 * 5) - 1) % M) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem c6 : scan 1000 ((2 * 4 ^ (3 + 1000 * 6) - 1) % M) = true := by decide +kernel

theorem key (m : ℕ) (h3 : 3 ≤ m) (h6561 : m ≤ 6561) :
    hasTwo 30 ((2 * 4 ^ m - 1) % M) = true := by
  have hc : (m - 3) / 1000 ≤ 6 := by omega
  have hi : (m - 3) % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
  have hm : m = 3 + 1000 * ((m - 3) / 1000) + (m - 3) % 1000 := by omega
  generalize (m - 3) / 1000 = c at hc hm
  generalize (m - 3) % 1000 = i at hi hm
  subst hm
  interval_cases c
  · exact scan_spec _ _ c0 i hi
  · exact scan_spec _ _ c1 i hi
  · exact scan_spec _ _ c2 i hi
  · exact scan_spec _ _ c3 i hi
  · exact scan_spec _ _ c4 i hi
  · exact scan_spec _ _ c5 i hi
  · exact scan_spec _ _ c6 i hi

end A259667Step

open A259667Step in
theorem OMA.solution : OMA.R_OeisA259667_conjecture_1_R2.H1 := by
  intro m h3 h6561
  obtain ⟨j, hj, h⟩ := hasTwo_spec 30 _ (key m h3 h6561)
  exact ⟨j, by rw [← digit_mod _ _ hj]; exact h⟩
