import OMAStatements.S_oeis_a107928
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: induction on blocks of three with t = 8^n: the harmonic means are 96t/5, 192t/7 and 128t,
-- already in lowest terms (powers of 2 times 3 are coprime to 5 and 7), giving 12*8^n, 24*8^n, 16*8^n.
-- No computer search.

namespace OMA.A107928Proof

open OMA.S_oeis_a107928

theorem step (n : ℕ) : a (n + 3) = ((2 * a (n + 2) * a (n + 1) : ℚ) / ((a (n + 1) : ℚ) + a (n + 2))).num := by
  rw [a]

theorem cop (c d n : ℕ) (hc : Nat.Coprime c d) (h2 : Nat.Coprime 2 d) :
    Nat.Coprime (((c : ℤ) * 8 ^ n).natAbs) d := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  simp only [Int.natAbs_natCast]
  refine Nat.Coprime.mul_left hc (Nat.Coprime.pow_left _ ?_)
  rw [show Int.natAbs 8 = 2 ^ 3 by norm_num]
  exact Nat.Coprime.pow_left _ h2

theorem key (n : ℕ) : a (3 * n + 3) = 12 * 8 ^ n ∧ a (3 * n + 4) = 24 * 8 ^ n ∧ a (3 * n + 5) = 16 * 8 ^ n := by
  induction n with
  | zero =>
    have a1 : a 1 = 2 := by rw [a]
    have a2 : a 2 = 3 := by rw [a]
    have a3 : a 3 = 12 := by
      rw [show 3 = 0 + 3 by rfl, step, a1, a2]
      rw [show ((2 * ((3 : ℤ) : ℚ) * ((2 : ℤ) : ℚ)) / (((2 : ℤ) : ℚ) + ((3 : ℤ) : ℚ))) = ((12 : ℤ) : ℚ) / ((5 : ℤ) : ℚ) by norm_num]
      exact Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)
    have a4 : a 4 = 24 := by
      rw [show 4 = 1 + 3 by rfl, step, show 1 + 2 = 3 by rfl, a3, a2]
      rw [show ((2 * ((12 : ℤ) : ℚ) * ((3 : ℤ) : ℚ)) / (((3 : ℤ) : ℚ) + ((12 : ℤ) : ℚ))) = ((24 : ℤ) : ℚ) / ((5 : ℤ) : ℚ) by norm_num]
      exact Rat.num_div_eq_of_coprime (by norm_num) (by norm_num)
    have a5 : a 5 = 16 := by
      rw [show 5 = 2 + 3 by rfl, step, show 2 + 2 = 4 by rfl, show 2 + 1 = 3 by rfl, a4, a3]
      rw [show ((2 * ((24 : ℤ) : ℚ) * ((12 : ℤ) : ℚ)) / (((12 : ℤ) : ℚ) + ((24 : ℤ) : ℚ))) = ((16 : ℤ) : ℚ) by norm_num]
      exact Rat.num_intCast 16
    exact ⟨by simpa using a3, by simpa using a4, by simpa using a5⟩
  | succ n ih =>
    obtain ⟨h3, h4, h5⟩ := ih
    have ht : (0 : ℚ) < 8 ^ n := by positivity
    have e6 : a (3 * (n + 1) + 3) = 12 * 8 ^ (n + 1) := by
      rw [show 3 * (n + 1) + 3 = (3 * n + 3) + 3 by ring, step, show 3 * n + 3 + 2 = 3 * n + 5 by ring,
        show 3 * n + 3 + 1 = 3 * n + 4 by ring, h4, h5]
      have : ((2 * ((16 * 8 ^ n : ℤ) : ℚ) * ((24 * 8 ^ n : ℤ) : ℚ)) / (((24 * 8 ^ n : ℤ) : ℚ) + ((16 * 8 ^ n : ℤ) : ℚ)))
          = (((96 : ℕ) : ℤ) * 8 ^ n : ℤ) / ((5 : ℤ) : ℚ) := by
        push_cast; field_simp; ring
      rw [this, Rat.num_div_eq_of_coprime (by norm_num) (cop 96 5 n (by norm_num) (by norm_num))]
      push_cast; ring
    have e7 : a (3 * (n + 1) + 4) = 24 * 8 ^ (n + 1) := by
      rw [show 3 * (n + 1) + 4 = (3 * n + 4) + 3 by ring, step, show 3 * n + 4 + 2 = 3 * (n + 1) + 3 by ring,
        show 3 * n + 4 + 1 = 3 * n + 5 by ring, h5, e6]
      have : ((2 * ((12 * 8 ^ (n + 1) : ℤ) : ℚ) * ((16 * 8 ^ n : ℤ) : ℚ)) / (((16 * 8 ^ n : ℤ) : ℚ) + ((12 * 8 ^ (n + 1) : ℤ) : ℚ)))
          = (((192 : ℕ) : ℤ) * 8 ^ n : ℤ) / ((7 : ℤ) : ℚ) := by
        push_cast; field_simp; ring
      rw [this, Rat.num_div_eq_of_coprime (by norm_num) (cop 192 7 n (by norm_num) (by norm_num))]
      push_cast; ring
    have e8 : a (3 * (n + 1) + 5) = 16 * 8 ^ (n + 1) := by
      rw [show 3 * (n + 1) + 5 = (3 * n + 5) + 3 by ring, step, show 3 * n + 5 + 2 = 3 * (n + 1) + 4 by ring,
        show 3 * n + 5 + 1 = 3 * (n + 1) + 3 by ring, e6, e7]
      have : ((2 * ((24 * 8 ^ (n + 1) : ℤ) : ℚ) * ((12 * 8 ^ (n + 1) : ℤ) : ℚ)) / (((12 * 8 ^ (n + 1) : ℤ) : ℚ) + ((24 * 8 ^ (n + 1) : ℤ) : ℚ)))
          = ((16 * 8 ^ (n + 1) : ℤ) : ℚ) := by
        push_cast; field_simp; ring
      rw [this, Rat.num_intCast]
    exact ⟨e6, e7, e8⟩

theorem mainP :
    ∀ n : ℕ, 0 < n →
      (a (3 * n) : ℚ) = 3 / 2 * 8 ^ n ∧ a (3 * n + 1) = 3 * 8 ^ n ∧
        a (3 * n + 2) = 2 * 8 ^ n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h3, h4, h5⟩ := key m
  rw [show 3 * (m + 1) = 3 * m + 3 by ring, show 3 * m + 3 + 1 = 3 * m + 4 by ring,
    show 3 * m + 3 + 2 = 3 * m + 5 by ring, h3, h4, h5]
  refine ⟨?_, ?_, ?_⟩
  · push_cast; ring
  · ring
  · ring

end OMA.A107928Proof

open OMA.A107928Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a107928.main := mainP
