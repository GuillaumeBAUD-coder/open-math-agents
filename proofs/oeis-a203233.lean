import OMAStatements.S_oeis_a203233
import Mathlib

-- Problem: oeis-a203233
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P203233
open OMA.S_oeis_a203233 PowerSeries

lemma ps (n : ℕ) : products (n + 1) = ((products n).1 * digit n,
    (products n).2 * digit n + (products n).1) := rfl

lemma d0 (j : ℕ) : digit (2 * j) = 3 := by simp [digit]
lemma d1 (j : ℕ) : digit (2 * j + 1) = 2 := by simp [digit, Nat.add_mod]

lemma two (j : ℕ) : products (2 * j + 2) = ((products (2 * j)).1 * 6,
    ((products (2 * j)).2 * 3 + (products (2 * j)).1) * 2 + (products (2 * j)).1 * 3) := by
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, ps, ps, d0, d1]; ext <;> simp <;> ring

lemma two' (j : ℕ) : products (2 * j + 3) = ((products (2 * j + 1)).1 * 6,
    ((products (2 * j + 1)).2 * 2 + (products (2 * j + 1)).1) * 3 + (products (2 * j + 1)).1 * 2) := by
  rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, ps, show 2 * j + 2 = (2 * j + 1) + 1 by ring, ps, d1,
    show 2 * j + 1 + 1 = 2 * (j + 1) by ring, d0]; ext <;> simp <;> ring

lemma rec4 (m : ℕ) : a (m + 4) = 12 * a (m + 2) - 36 * a m := by
  unfold a
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j + 4 = 2 * (j + 1) + 2 by ring, two, show j + j + 2 = 2 * j + 2 by ring, two,
      show 2 * (j + 1) = 2 * j + 2 by ring, two, show j + j = 2 * j by ring]
    simp only
    ring
  · have h5 := two' (j + 1)
    have h3 := two' j
    rw [show 2 * (j + 1) + 3 = 2 * j + 1 + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at h5
    rw [show 2 * j + 1 + 2 = 2 * j + 3 by ring, h5, h3]
    simp only
    ring

lemma cX (f : ℕ → ℤ) (k n : ℕ) : coeff n (mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow']; simp

theorem sol : type_of% @OMA.S_oeis_a203233.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 2 = (m + 1) + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 = (m + 1) + 4 by omega, rec4]
  · have l : (1 - C 6 * X ^ 2 : PowerSeries ℤ) ^ 2 * mk a =
        mk a * X ^ 0 - C (12 : ℤ) * (mk a * X ^ 2) + C (36 : ℤ) * (mk a * X ^ 4) := by
      simp only [map_ofNat]; ring
    rw [l]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, cX, coeff_X_pow]
    rcases n with _ | _ | _ | _ | n
    · decide
    · decide
    · decide
    · decide
    · simp only [show ¬ (n + 1 + 1 + 1 + 1 = 1) by omega, show ¬ (n + 1 + 1 + 1 + 1 = 2) by omega,
        show ¬ (n + 1 + 1 + 1 + 1 = 3) by omega, if_false, show 2 ≤ n + 1 + 1 + 1 + 1 by omega,
        show 4 ≤ n + 1 + 1 + 1 + 1 by omega, show 0 ≤ n + 1 + 1 + 1 + 1 by omega, if_true,
        show n + 1 + 1 + 1 + 1 - 0 = n + 4 by omega, show n + 1 + 1 + 1 + 1 - 2 = n + 2 by omega,
        show n + 1 + 1 + 1 + 1 - 4 = n by omega, rec4]
      ring

end OMA.P203233

theorem OMA.solution : type_of% @OMA.S_oeis_a203233.main := OMA.P203233.sol
