import OMAStatements.S_oeis_a103621
import Mathlib

-- Credit: @LordMike. Shortened from the proof by @caa1982.
open OMA.S_oeis_a103621 Finset

namespace P

theorem st (m k n e d : ℕ) (h : orbit m = n)
    (H : k = m + 1 ∧ e = n + d ∧ 64 ≤ n ∧ n < 2 ^ 37 - 37 ∧ (n % 64 = 9 ∧ d = 2 ∨ n % 64 = 11 ∧ d = 2 ∨ n % 64 = 13 ∧ d = 10 ∨ n % 64 = 23 ∧ d = 2 ∨ n % 64 = 25 ∧ d = 2 ∨ n % 64 = 27 ∧ d = 34 ∨ n % 64 = 61 ∧ d = 10 ∨ n % 64 = 7 ∧ d = 2)) :
    orbit k = e := by
  obtain ⟨rfl, rfl, h6, hn, hS⟩ := H
  show sloping _ = _
  rw [h]
  unfold sloping
  congr 1
  have hL : 6 ≤ n.log2 := by
    have := (Nat.log2_lt (show n ≠ 0 by omega) (k := 6)).not.mpr (by omega)
    omega
  rw [← sum_subset (range_subset_range.mpr (show 6 ≤ n.log2 + 1 by omega))]
  · rcases hS with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
      simp (disch := omega) [sum_range_succ, if_pos, if_neg]
  intro i hi hni
  simp only [mem_range] at hi hni
  refine if_neg fun h0 => ?_
  have h64 : 64 ∣ n + (i + 1) := (pow_dvd_pow 2 (show 6 ≤ i + 1 by omega) : 2 ^ 6 ∣ _).trans (Nat.dvd_of_mod_eq_zero h0)
  have := Nat.log2_self_le (show n ≠ 0 by omega)
  have h2 : 2 ^ i ≤ n := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans this
  have : i < 37 := by
    by_contra
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 37 ≤ i by omega)
    omega
  obtain rfl : i = 36 := by omega
  have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h0)
  norm_num at hn this
  omega

theorem ch (t : ℕ) (h1 : 1 ≤ t) (hb : 64 * t + 25 < 137438953435) (h : orbit (8 * t + 1) = 9 + 64 * t) :
    orbit (8 * t + 6) = 27 + 64 * t ∧ (64 * t + 71 < 137438953435 → orbit (8 * t + 7) = 61 + 64 * t ∧ orbit (8 * (t + 1) + 1) = 9 + 64 * (t + 1)) := by
  have B : (2 : ℕ) ^ 37 - 37 = 137438953435 := by norm_num
  have e2 := st _ (8 * t + 2) _ (11 + 64 * t) 2 h (by omega)
  have e3 := st _ (8 * t + 3) _ (13 + 64 * t) 2 e2 (by omega)
  have e4 := st _ (8 * t + 4) _ (23 + 64 * t) 10 e3 (by omega)
  have e5 := st _ (8 * t + 5) _ (25 + 64 * t) 2 e4 (by omega)
  have e6 := st _ (8 * t + 6) _ (27 + 64 * t) 2 e5 (by omega)
  refine ⟨e6, fun hb => ?_⟩
  have e7 := st _ (8 * t + 7) _ (61 + 64 * t) 34 e6 (by omega)
  have e8 := st _ (8 * t + 8) _ (71 + 64 * t) 10 e7 (by omega)
  exact ⟨e7, st _ _ _ _ 2 e8 (by omega)⟩

theorem per : ∀ t, 1 ≤ t → t ≤ 2147483647 → orbit (8 * t + 1) = 9 + 64 * t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _; decide
  | succ t ht ih => exact fun _ => (ch t ht (by omega) (ih (by omega))).2 (by omega) |>.2

theorem slx : sloping 137438953435 = 137438953435 + 34 + 2 ^ 37 := by
  unfold sloping
  rw [show Nat.log2 137438953435 = 36 by rw [Nat.log2_eq_iff (by norm_num)]; norm_num, sum_range_succ,
    ← sum_subset (range_subset_range.mpr (show 6 ≤ 36 by omega))]
  · simp [sum_range_succ]
  intro i hi hni
  simp only [mem_range] at hi hni
  refine if_neg fun h0 => ?_
  have := (pow_dvd_pow 2 (show 6 ≤ i + 1 by omega) : 2 ^ 6 ∣ _).trans (Nat.dvd_of_mod_eq_zero h0)
  omega

end P

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103621.main) := by
  intro h
  have h1 := h.1 17179869184 (by norm_num)
  have c1 := P.ch 2147483646 (by norm_num) (by norm_num) (P.per 2147483646 (by norm_num) (by norm_num))
  have b6 := (P.ch 2147483647 (by norm_num) (by norm_num) (P.per 2147483647 (by norm_num) (by norm_num))).1
  obtain ⟨a6, a7, -⟩ := c1.1, (c1.2 (by norm_num))
  norm_num at a6 a7 b6
  have b7 : orbit 17179869183 = 137438953435 + 34 + 2 ^ 37 := by
    show sloping (orbit 17179869182) = _
    rw [b6, P.slx]
  rw [show a 17179869184 = orbit 17179869183 from rfl, show a (17179869184 - 9) = orbit 17179869174 from rfl,
    show a (17179869184 - 1) = orbit 17179869182 from rfl, show a (17179869184 - 8) = orbit 17179869175 from rfl, b7, b6, a6, a7] at h1
  norm_num at h1
