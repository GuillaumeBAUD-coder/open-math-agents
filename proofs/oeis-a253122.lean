import OMAStatements.S_oeis_a253122
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: by induction, completions (2m) x y parity is P_m or Q_m with P+Q=4^m, P-Q=2^m; closed forms and a 3-term recurrence follow; series by coefficient comparison.

namespace OMA.P_oeis_a253122
open OMA.S_oeis_a253122 PowerSeries

theorem key (m : ℕ) : ∃ P Q : ℕ, P + Q = 4 ^ m ∧ P = Q + 2 ^ m ∧
    (∀ x y, completions (2 * m) x y false = P) ∧ (∀ x y, completions (2 * m) x y true = Q) := by
  induction m with
  | zero => exact ⟨1, 0, by norm_num, by norm_num, fun x y => rfl, fun x y => rfl⟩
  | succ m ih =>
    obtain ⟨P, Q, hs, hd, h1, h2⟩ := ih
    refine ⟨3 * P + Q, P + 3 * Q, ?_, ?_, ?_, ?_⟩
    · rw [pow_succ]; omega
    · rw [pow_succ]; omega
    · intro x y
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
      cases x <;> cases y <;> simp [completions, median, h1, h2] <;> omega
    · intro x y
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
      cases x <;> cases y <;> simp [completions, median, h1, h2] <;> omega

theorem cw_even (m : ℕ) : countedWords (2 * m) = 2 * 2 ^ m + 2 * 4 ^ m := by
  obtain ⟨P, Q, hs, hd, h1, h2⟩ := key m
  simp only [countedWords, h1]
  omega

theorem cw_odd (m : ℕ) : countedWords (2 * m + 1) = 4 * 4 ^ m := by
  obtain ⟨P, Q, hs, hd, h1, h2⟩ := key m
  simp [countedWords, completions, median, h1, h2]
  omega

theorem cw3 (k : ℕ) :
    countedWords (k + 3) + 4 * countedWords k =
      2 * countedWords (k + 2) + 2 * countedWords (k + 1) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
  · rw [show 2 * m + 3 = 2 * (m + 1) + 1 by ring, show 2 * m + 2 = 2 * (m + 1) by ring,
      cw_odd, cw_odd, cw_even, cw_even, pow_succ, pow_succ]
    omega
  · rw [show 2 * m + 1 + 3 = 2 * (m + 2) by ring, show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
      cw_odd, cw_odd, cw_even, cw_even, pow_succ, pow_succ, pow_succ, pow_succ]
    omega

theorem a_rec (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 3) : ℤ) = 2 * a (n + 2) + 2 * a (n + 1) - 4 * a n := by
  have := cw3 n
  simp only [a, show n + 3 ≠ 0 by omega, show n + 2 ≠ 0 by omega, show n + 1 ≠ 0 by omega,
    show n ≠ 0 by omega, if_false]
  omega

theorem cmul (n : ℕ) (f : ℤ⟦X⟧) (c : ℤ) : coeff n (C c * f) = c * coeff n f := coeff_C_mul n f c

theorem cXp (n k : ℕ) (f : ℤ⟦X⟧) :
    coeff n (X ^ k * f) = if k ≤ n then coeff (n - k) f else 0 := coeff_X_pow_mul' f k n

theorem ps :
    (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      4 * X * (1 + X - 4 * X ^ 2) := by
  have e2 : (2 : ℤ⟦X⟧) = C 2 := (map_ofNat (C (R := ℤ)) 2).symm
  have e4 : (4 : ℤ⟦X⟧) = C 4 := (map_ofNat (C (R := ℤ)) 4).symm
  have eL : (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      PowerSeries.mk (fun n => (a n : ℤ)) - C 2 * (X ^ 1 * PowerSeries.mk (fun n => (a n : ℤ)))
        - C 2 * (X ^ 2 * PowerSeries.mk (fun n => (a n : ℤ)))
        + C 2 * (C 2 * (X ^ 3 * PowerSeries.mk (fun n => (a n : ℤ)))) := by
    rw [← e2]; ring
  have eR : (4 : ℤ⟦X⟧) * X * (1 + X - 4 * X ^ 2) =
      C 4 * (X ^ 1 * 1) + C 4 * (X ^ 2 * 1) - C 4 * (C 4 * (X ^ 3 * 1)) := by
    rw [← e4]; ring
  rw [eL, eR]
  ext n
  simp only [map_add, map_sub, cmul, cXp, coeff_mk, coeff_one]
  rcases n with _ | _ | _ | n
  · simp [a]
  · simp [a, countedWords, completions, median]
  · simp [a, countedWords, completions, median]
  · rcases n with _ | n
    · simp [a, countedWords, completions, median]
    · have := a_rec (n + 1) (by omega)
      simp only [show 1 ≤ n + 1 + 3 by omega, show 2 ≤ n + 1 + 3 by omega,
        show 3 ≤ n + 1 + 3 by omega, if_true, show n + 1 + 3 - 1 = n + 1 + 2 by omega,
        show n + 1 + 3 - 2 = n + 1 + 1 by omega, show n + 1 + 3 - 3 = n + 1 by omega,
        show n + 1 + 2 ≠ 0 by omega,
        show n + 1 + 1 ≠ 0 by omega, show n + 1 ≠ 0 by omega, if_false]
      simp only [mul_zero, sub_zero, add_zero]
      linarith

theorem solve : type_of% @OMA.S_oeis_a253122.main := by
  refine ⟨ps, ?_, ?_⟩
  · intro n hn he
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hm : 2 * m / 2 = m := by omega
    rw [hm]
    simp only [a, show 2 * m ≠ 0 by omega, if_false]
    rw [cw_even, pow_succ, pow_succ, pow_mul]
    norm_num
    ring
  · intro n hn ho
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    simp only [a, show 2 * m + 1 ≠ 0 by omega, if_false]
    rw [cw_odd, pow_succ, pow_succ, pow_mul]
    norm_num
    ring

end OMA.P_oeis_a253122

theorem OMA.solution : type_of% @OMA.S_oeis_a253122.main := OMA.P_oeis_a253122.solve
