import OMAStatements.S_oeis_a107928
import Mathlib

/-!
Starting from a(3) = 12, a(4) = 24, a(5) = 16, one step of the recursion from
a(3m+3), a(3m+4), a(3m+5) = 12x, 24x, 16x (x = 8^m) gives the harmonic-mean values
96x/5, 192x/7 and 128x, whose numerators are 96x, 192x and 128x since 8^m is coprime to 5 and 7.
So a(3m+3) = 12 * 8^m, a(3m+4) = 24 * 8^m, a(3m+5) = 16 * 8^m for every m, by induction on m.
-/

namespace R107928
open OMA.S_oeis_a107928

theorem num_nat_div (N D : ℕ) (hD : 0 < D) (hc : Nat.Coprime N D) :
    ((N : ℚ) / (D : ℚ)).num = N := by
  have h1 : (((N : ℤ) : ℚ) / ((D : ℤ) : ℚ)).num = (N : ℤ) :=
    Rat.num_div_eq_of_coprime (by exact_mod_cast hD)
      (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hc)
  rw [Int.cast_natCast, Int.cast_natCast] at h1
  exact h1

theorem step (k : ℕ) (u v r : ℤ) (N D : ℕ) (hu : a (k + 1) = u) (hv : a (k + 2) = v)
    (hD : 0 < D) (hc : Nat.Coprime N D) (hden : (u : ℚ) + v ≠ 0)
    (he : 2 * (v : ℚ) * u * D = N * ((u : ℚ) + v)) (hr : (N : ℤ) = r) : a (k + 3) = r := by
  have h : a (k + 3) = ((2 * a (k + 2) * a (k + 1) : ℚ) / ((a (k + 1) : ℚ) + a (k + 2))).num :=
    rfl
  have hq : (2 * (v : ℚ) * u) / ((u : ℚ) + v) = (N : ℚ) / (D : ℚ) := by
    rw [div_eq_div_iff hden (Nat.cast_pos.mpr hD).ne']
    linear_combination he
  rw [h, hu, hv, hq, num_nat_div N D hD hc, hr]

theorem key (m : ℕ) :
    a (3 * m + 3) = 12 * 8 ^ m ∧ a (3 * m + 4) = 24 * 8 ^ m ∧ a (3 * m + 5) = 16 * 8 ^ m := by
  induction m with
  | zero =>
    have h1 : a 1 = 2 := rfl
    have h2 : a 2 = 3 := rfl
    have h3 : a 3 = 12 :=
      step 0 2 3 12 12 5 h1 h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    have h4 : a 4 = 24 :=
      step 1 3 12 24 24 5 h2 h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    have h5 : a 5 = 16 :=
      step 2 12 24 16 16 1 h3 h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    refine ⟨?_, ?_, ?_⟩ <;> norm_num [h3, h4, h5]
  | succ m ih =>
    obtain ⟨hA, hB, hC⟩ := ih
    have hA' : a (3 * m + 6) = 12 * 8 ^ (m + 1) :=
      step (3 * m + 3) (24 * 8 ^ m) (16 * 8 ^ m) (12 * 8 ^ (m + 1)) (96 * 8 ^ m) 5 hB hC
        (by norm_num) (Nat.Coprime.mul_left (by norm_num) (Nat.Coprime.pow_left m (by norm_num)))
        (by push_cast; positivity) (by push_cast; ring) (by push_cast; ring)
    have hB' : a (3 * m + 7) = 24 * 8 ^ (m + 1) :=
      step (3 * m + 4) (16 * 8 ^ m) (12 * 8 ^ (m + 1)) (24 * 8 ^ (m + 1)) (192 * 8 ^ m) 7 hC hA'
        (by norm_num) (Nat.Coprime.mul_left (by norm_num) (Nat.Coprime.pow_left m (by norm_num)))
        (by push_cast; positivity) (by push_cast; ring) (by push_cast; ring)
    have hC' : a (3 * m + 8) = 16 * 8 ^ (m + 1) :=
      step (3 * m + 5) (12 * 8 ^ (m + 1)) (24 * 8 ^ (m + 1)) (16 * 8 ^ (m + 1)) (128 * 8 ^ m) 1
        hA' hB' (by norm_num) (Nat.coprime_one_right _) (by push_cast; positivity)
        (by push_cast; ring) (by push_cast; ring)
    rw [show 3 * (m + 1) + 3 = 3 * m + 6 by ring, show 3 * (m + 1) + 4 = 3 * m + 7 by ring,
      show 3 * (m + 1) + 5 = 3 * m + 8 by ring]
    exact ⟨hA', hB', hC'⟩

end R107928

theorem OMA.solution : type_of% @OMA.S_oeis_a107928.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hA, hB, hC⟩ := R107928.key m
  refine ⟨?_, ?_, ?_⟩
  · rw [show 3 * (m + 1) = 3 * m + 3 by ring, hA]
    push_cast
    ring
  · rw [show 3 * (m + 1) + 1 = 3 * m + 4 by ring, hB]
    ring
  · rw [show 3 * (m + 1) + 2 = 3 * m + 5 by ring, hC]
    ring
