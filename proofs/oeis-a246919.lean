import OMAStatements.S_oeis_a246919
import Mathlib

open OMA.S_oeis_a246919
open PowerSeries

namespace P246919

/-- Any solution gives `t = |2x - n|` with `t^2 + 3 n^2 = 4 y^2`, and `y <= (3 n^2 + 1) / 4`. -/
theorem sol_bound (n y : ℕ) (hn : 0 < n) (x : ℤ)
    (h : x ^ 2 - (y : ℤ) ^ 2 - n * x + (n : ℤ) ^ 2 = 0) :
    y ≤ (3 * n ^ 2 + 1) / 4 ∧ ∃ t : ℕ, t ≤ 2 * y ∧ t ^ 2 + 3 * n ^ 2 = 4 * y ^ 2 := by
  have key : ((2 * x - n).natAbs : ℤ) ^ 2 + 3 * (n : ℤ) ^ 2 = 4 * (y : ℤ) ^ 2 := by
    rw [Int.natAbs_sq]; linear_combination 4 * h
  have key' : (2 * x - n).natAbs ^ 2 + 3 * n ^ 2 = 4 * y ^ 2 := by exact_mod_cast key
  set t := (2 * x - n).natAbs
  have ht : t < 2 * y := by
    by_contra hc
    have hc := not_lt.mp hc
    have : (2 * y) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hc 2
    have : 0 < 3 * n ^ 2 := by positivity
    nlinarith
  refine ⟨?_, t, ht.le, key'⟩
  have h1 : t + 1 ≤ 2 * y := ht
  have h2 : 4 * y ≤ 3 * n ^ 2 + 1 := by
    rcases Nat.eq_zero_or_pos y with hy | hy
    · omega
    · have hle : t ≤ 2 * y - 1 := by omega
      have hsq : t ^ 2 ≤ (2 * y - 1) ^ 2 := Nat.pow_le_pow_left hle 2
      obtain ⟨z, hz⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
      subst hz
      have e : 2 * (z + 1) - 1 = 2 * z + 1 := by omega
      rw [e] at hsq
      nlinarith
  omega

theorem upper (n v : ℕ) (hn : 0 < n)
    (hdec : ∀ y < (3 * n ^ 2 + 1) / 4 + 1, ∀ t < 2 * y + 1, t ^ 2 + 3 * n ^ 2 = 4 * y ^ 2 →
      y = n ∨ y ≤ v) :
    ∀ y ∈ cevians n, y ≤ v := by
  rintro y ⟨hy, x, hx⟩
  obtain ⟨hb, t, ht, he⟩ := sol_bound n y hn x hx
  rcases hdec y (by omega) t (by omega) he with h | h
  · exact absurd h hy
  · exact h

theorem a_eq (n v : ℕ) (hn : 0 < n) (hv : v ∈ cevians n)
    (hdec : ∀ y < (3 * n ^ 2 + 1) / 4 + 1, ∀ t < 2 * y + 1, t ^ 2 + 3 * n ^ 2 = 4 * y ^ 2 →
      y = n ∨ y ≤ v) : a n = v :=
  IsGreatest.csSup_eq ⟨hv, upper n v hn hdec⟩

theorem a4 : a 4 = 0 := by
  have hE : cevians 4 = ∅ := by
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have := upper 4 0 (by norm_num) (by decide) y hy
    obtain ⟨hy4, x, hx⟩ := hy
    obtain rfl : y = 0 := by omega
    push_cast at hx
    nlinarith [sq_nonneg (x - 2)]
  rw [a, hE, csSup_empty]; rfl

theorem a8 : a 8 = 13 :=
  a_eq 8 13 (by norm_num) ⟨by norm_num, 15, by norm_num⟩ (by decide +kernel)

theorem a12 : a 12 = 28 :=
  a_eq 12 28 (by norm_num) ⟨by norm_num, 32, by norm_num⟩ (by decide +kernel)

theorem a16 : a 16 = 49 :=
  a_eq 16 49 (by norm_num) ⟨by norm_num, 55, by norm_num⟩ (by decide +kernel)

end P246919

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a246919.main) := by
  rintro ⟨h, -⟩
  have h16 := h 16 (by norm_num)
  norm_num [P246919.a16, P246919.a12, P246919.a8, P246919.a4] at h16
