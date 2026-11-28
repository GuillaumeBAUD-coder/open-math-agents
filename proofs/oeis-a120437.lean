import OMAStatements.S_oeis_a120437
import Mathlib

namespace OMA.P120437

open OMA.S_oeis_a120437

lemma b_zero : b 0 = 0 := by simp [b]

lemma b_step (q d : ℕ) (hd : d < 3) : b (3 * q + d) = 9 * b q + d := by
  unfold b
  rcases Nat.eq_zero_or_pos (3 * q + d) with h | h
  · have hq : q = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hq
    subst hd0
    simp
  · have e : 3 * q + d = d + 3 * q := by ring
    rw [e, Nat.digits_add 3 (by norm_num) d q hd (by omega), Nat.ofDigits_cons]
    push_cast
    ring

lemma b_one : b 1 = 1 := by
  have h := b_step 0 1 (by norm_num)
  simpa [b_zero] using h

lemma b_two : b 2 = 2 := by
  have h := b_step 0 2 (by norm_num)
  simpa [b_zero] using h

/-- Shifting by j base-3 digits. -/
lemma b_add (j : ℕ) : ∀ m r : ℕ, r < 3 ^ j → b (m * 3 ^ j + r) = 9 ^ j * b m + b r := by
  induction j with
  | zero =>
    intro m r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp [b_zero]
  | succ j ih =>
    intro m r hr
    have hr' : r / 3 < 3 ^ j := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [pow_succ] at hr
      exact hr
    have hd : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have e2 : r = 3 * (r / 3) + r % 3 := (Nat.div_add_mod r 3).symm
    have e1 : m * 3 ^ (j + 1) + r = 3 * (m * 3 ^ j + r / 3) + r % 3 := by
      rw [pow_succ]
      linarith
    have hbr : b r = 9 * b (r / 3) + r % 3 := by
      conv_lhs => rw [e2]
      exact b_step _ _ hd
    rw [e1, b_step _ _ hd, ih m (r / 3) hr', hbr, pow_succ]
    ring

lemma b_pow (j : ℕ) : b (3 ^ j) = 9 ^ j := by
  have h := b_add j 1 0 (by positivity)
  simpa [b_one, b_zero] using h

lemma c_succ (j : ℕ) : b (3 ^ (j + 1) - 1) = 9 * b (3 ^ j - 1) + 2 := by
  have hp : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have h : 3 ^ (j + 1) - 1 = 3 * (3 ^ j - 1) + 2 := by
    rw [pow_succ]
    omega
  rw [h, b_step _ 2 (by norm_num)]

lemma key (j : ℕ) : ∀ t r : ℕ, r < 3 ^ j → 1 ≤ t → t < 3 → 3 ^ j < t * 3 ^ j + r →
    a (t * 3 ^ j + r) = a (t * 3 ^ j + r - 3 ^ j) := by
  intro t r hr ht1 ht2 hlt
  have hp : 0 < 3 ^ j := by positivity
  interval_cases t
  · have hr0 : 1 ≤ r := by omega
    unfold a
    have e1 : 1 * 3 ^ j + r - 1 = 1 * 3 ^ j + (r - 1) := by omega
    have e2 : 1 * 3 ^ j + r - 3 ^ j = 0 * 3 ^ j + r := by omega
    have e3 : 0 * 3 ^ j + r - 1 = 0 * 3 ^ j + (r - 1) := by omega
    rw [e1, e2, e3, b_add j 1 r hr, b_add j 1 (r - 1) (by omega), b_add j 0 r hr,
      b_add j 0 (r - 1) (by omega)]
    push_cast
    ring
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · unfold a
      have e1 : 2 * 3 ^ j + 0 - 1 = 1 * 3 ^ j + (3 ^ j - 1) := by omega
      have e2 : 2 * 3 ^ j + 0 - 3 ^ j = 1 * 3 ^ j + 0 := by omega
      have e3 : 1 * 3 ^ j + 0 - 1 = 0 * 3 ^ j + (3 ^ j - 1) := by omega
      rw [e1, e2, e3, b_add j 2 0 hp, b_add j 1 (3 ^ j - 1) (by omega), b_add j 1 0 hp,
        b_add j 0 (3 ^ j - 1) (by omega)]
      simp only [b_zero, b_one, b_two]
      push_cast
      ring
    · unfold a
      have e1 : 2 * 3 ^ j + r - 1 = 2 * 3 ^ j + (r - 1) := by omega
      have e2 : 2 * 3 ^ j + r - 3 ^ j = 1 * 3 ^ j + r := by omega
      have e3 : 1 * 3 ^ j + r - 1 = 1 * 3 ^ j + (r - 1) := by omega
      rw [e1, e2, e3, b_add j 2 r hr, b_add j 2 (r - 1) (by omega), b_add j 1 r hr,
        b_add j 1 (r - 1) (by omega)]
      push_cast
      ring

end OMA.P120437

theorem OMA.solution : type_of% @OMA.S_oeis_a120437.main := by
  refine ⟨?_, ?_, ?_⟩
  · unfold OMA.S_oeis_a120437.a
    simp [OMA.P120437.b_one, OMA.P120437.b_zero]
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e : j + 1 - 1 = j := by omega
    rw [e]
    unfold OMA.S_oeis_a120437.a
    rw [OMA.P120437.b_pow, OMA.P120437.b_pow, OMA.P120437.c_succ]
    push_cast
    ring
  · intro k n hk h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e : j + 1 - 1 = j := by omega
    rw [e] at h1 ⊢
    have hp : 0 < 3 ^ j := by positivity
    have hn : n = n / 3 ^ j * 3 ^ j + n % 3 ^ j := (Nat.div_add_mod' n (3 ^ j)).symm
    have hr : n % 3 ^ j < 3 ^ j := Nat.mod_lt _ hp
    have ht1 : 1 ≤ n / 3 ^ j := (Nat.one_le_div_iff hp).mpr h1.le
    have ht2 : n / 3 ^ j < 3 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      rw [pow_succ] at h2
      linarith
    have h := OMA.P120437.key j (n / 3 ^ j) (n % 3 ^ j) hr ht1 ht2 (by rw [← hn]; exact h1)
    rw [← hn] at h
    exact h
