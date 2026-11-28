import OMAReductions.R_erdos_634_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

namespace OMA.W

def L : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
  89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
  191, 193, 197, 199]

def S : List ℕ := [5, 9, 15, 16, 20, 25, 27, 32, 36, 40, 45, 48, 50, 54, 64, 72, 75, 80, 81, 90,
  96, 100, 108, 120, 125, 128, 135, 144, 150, 160, 162, 180, 192, 200, 3, 4, 6, 8, 10, 12, 18, 24,
  30, 60]

theorem key : ∀ n ∈ List.range 201, 3 ≤ n → n ∈ S ∨ ∃ l ∈ L, n % l = 0 := by
  decide +kernel

theorem Lprime : ∀ l ∈ L, l.Prime ∧ 5 < l := by
  intro l hl
  simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end OMA.W

open OMA.W in
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro n h3 h200 hs
  rcases key n (List.mem_range.mpr (by omega)) h3 with h | ⟨l, hl, hd⟩
  · simp only [S, List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  · have := Lprime l hl
    have := hs l this.1 (Nat.dvd_of_mod_eq_zero hd)
    omega
