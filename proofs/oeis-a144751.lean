import OMAStatements.S_oeis_a144751
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: every term is odd (odd + 1 + odd prime), so the least odd prime factor is Nat.minFac.
-- Computing the terms with norm_num (Nat.minFac evaluation) gives a(43) = 229401, while
-- 5 a(37) - 4 a(31) = 458727, so the recurrence of the g.f. fails at n = 43 (no search needed).

namespace OMA.P_oeis_a144751
open OMA.S_oeis_a144751

theorem lopf_of_odd {m : ℕ} (h : Odd m) : lopf m = Nat.minFac m := by
  have h2 : ¬ 2 ∣ m := by
    rintro ⟨k, rfl⟩
    exact (Nat.not_even_iff_odd.mpr h) ⟨k, by ring⟩
  simp [lopf, Nat.factorization_eq_zero_of_not_dvd h2]

theorem b_odd : ∀ n, Odd (b n) := by
  intro n
  induction n with
  | zero => exact ⟨1, rfl⟩
  | succ n ih =>
    have hm : Odd (Nat.minFac (b n)) := by
      by_cases hb : b n = 1
      · rw [hb, Nat.minFac_one]; exact ⟨0, rfl⟩
      rcases (Nat.minFac_prime hb).eq_two_or_odd' with h | h
      · exfalso
        have : 2 ∣ b n := h ▸ Nat.minFac_dvd (b n)
        exact (Nat.not_even_iff_odd.mpr ih) (even_iff_two_dvd.mpr this)
      · exact h
    show Odd (1 + b n + lopf (b n))
    rw [lopf_of_odd ih]
    rcases ih with ⟨x, hx⟩
    rcases hm with ⟨y, hy⟩
    exact ⟨x + y + 1, by omega⟩

theorem b_succ (n : ℕ) : b (n + 1) = 1 + b n + Nat.minFac (b n) := by
  show 1 + b n + lopf (b n) = _
  rw [lopf_of_odd (b_odd n)]

theorem b0 : b 0 = 3 := rfl
theorem b1 : b 1 = 7 := by rw [b_succ, b0]; norm_num
theorem b2 : b 2 = 15 := by rw [b_succ, b1]; norm_num
theorem b3 : b 3 = 19 := by rw [b_succ, b2]; norm_num
theorem b4 : b 4 = 39 := by rw [b_succ, b3]; norm_num
theorem b5 : b 5 = 43 := by rw [b_succ, b4]; norm_num
theorem b6 : b 6 = 87 := by rw [b_succ, b5]; norm_num
theorem b7 : b 7 = 91 := by rw [b_succ, b6]; norm_num
theorem b8 : b 8 = 99 := by rw [b_succ, b7]; norm_num
theorem b9 : b 9 = 103 := by rw [b_succ, b8]; norm_num
theorem b10 : b 10 = 207 := by rw [b_succ, b9]; norm_num
theorem b11 : b 11 = 211 := by rw [b_succ, b10]; norm_num
theorem b12 : b 12 = 423 := by rw [b_succ, b11]; norm_num
theorem b13 : b 13 = 427 := by rw [b_succ, b12]; norm_num
theorem b14 : b 14 = 435 := by rw [b_succ, b13]; norm_num
theorem b15 : b 15 = 439 := by rw [b_succ, b14]; norm_num
theorem b16 : b 16 = 879 := by rw [b_succ, b15]; norm_num
theorem b17 : b 17 = 883 := by rw [b_succ, b16]; norm_num
theorem b18 : b 18 = 1767 := by rw [b_succ, b17]; norm_num
theorem b19 : b 19 = 1771 := by rw [b_succ, b18]; norm_num
theorem b20 : b 20 = 1779 := by rw [b_succ, b19]; norm_num
theorem b21 : b 21 = 1783 := by rw [b_succ, b20]; norm_num
theorem b22 : b 22 = 3567 := by rw [b_succ, b21]; norm_num
theorem b23 : b 23 = 3571 := by rw [b_succ, b22]; norm_num
theorem b24 : b 24 = 7143 := by rw [b_succ, b23]; norm_num
theorem b25 : b 25 = 7147 := by rw [b_succ, b24]; norm_num
theorem b26 : b 26 = 7155 := by rw [b_succ, b25]; norm_num
theorem b27 : b 27 = 7159 := by rw [b_succ, b26]; norm_num
theorem b28 : b 28 = 14319 := by rw [b_succ, b27]; norm_num
theorem b29 : b 29 = 14323 := by rw [b_succ, b28]; norm_num
theorem b30 : b 30 = 28647 := by rw [b_succ, b29]; norm_num
theorem b31 : b 31 = 28651 := by rw [b_succ, b30]; norm_num
theorem b32 : b 32 = 28659 := by rw [b_succ, b31]; norm_num
theorem b33 : b 33 = 28663 := by rw [b_succ, b32]; norm_num
theorem b34 : b 34 = 57327 := by rw [b_succ, b33]; norm_num
theorem b35 : b 35 = 57331 := by rw [b_succ, b34]; norm_num
theorem b36 : b 36 = 114663 := by rw [b_succ, b35]; norm_num
theorem b37 : b 37 = 114667 := by rw [b_succ, b36]; norm_num
theorem b38 : b 38 = 114675 := by rw [b_succ, b37]; norm_num
theorem b39 : b 39 = 114679 := by rw [b_succ, b38]; norm_num
theorem b40 : b 40 = 229359 := by rw [b_succ, b39]; norm_num
theorem b41 : b 41 = 229363 := by rw [b_succ, b40]; norm_num
theorem b42 : b 42 = 229401 := by rw [b_succ, b41]; norm_num

theorem disproof : ¬ ∀ n : ℕ, 13 ≤ n → (a n : ℤ) = 5 * a (n - 6) - 4 * a (n - 12) := by
  intro h
  have h43 := h 43 (by norm_num)
  simp only [a, show 43 - 1 = 42 from rfl, show 43 - 6 - 1 = 36 from rfl,
    show 43 - 12 - 1 = 30 from rfl, b42, b36, b30] at h43
  norm_num at h43

end OMA.P_oeis_a144751

theorem OMA.solution : type_of% @OMA.S_oeis_a144751.main := OMA.P_oeis_a144751.disproof
