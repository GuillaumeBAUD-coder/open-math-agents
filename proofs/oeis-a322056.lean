import OMAStatements.S_oeis_a322056
import Mathlib


namespace MSLOeisContradiction
open PowerSeries

noncomputable def q : PowerSeries ℤ :=
  C 1 + C 8 * X + C 32 * X ^ 2 + C 32 * X ^ 3 + C 70 * X ^ 4 +
  C 24 * X ^ 5 + C 72 * X ^ 6 + C 49 * X ^ 8 - C 8 * X ^ 10 +
  C 16 * X ^ 11 - C 8 * X ^ 12

noncomputable def d : PowerSeries ℤ := (1-X)^2 * (1+X)^2 * (1+X^2)^2

private lemma den_poly : d = 1 - 2*X^4 + X^8 := by
  dsimp [d]
  ring

private lemma num10 : (coeff 10) q = -8 := by
  rw [q]
  simp only [map_add, map_sub, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X]
  norm_num

private lemma den_coeff10 (a : ℕ → ℤ) :
    (coeff 10) (mk a * d) = a 10 - 2*a 6 + a 2 := by
  rw [den_poly]
  rw [mul_comm (mk a)]
  rw [show (2 : ℤ⟦X⟧) = C (2:ℤ) by norm_num]
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add,
             mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_mk]
  norm_num

/-- Exact A322056 source conjunction is impossible: its recurrence is claimed
    for n>8, although the GF numerator has a nonzero coefficient at n=10. -/
theorem a322056_incompatible (a : ℕ → ℤ)
    (hrec : ∀ n : ℕ, 8 < n → a n = 2 * a (n - 4) - a (n - 8))
    (hgf : mk a * d = q) : False := by
  have h10 := hrec 10 (by norm_num)
  have hcoeff := congrArg (coeff 10) hgf
  rw [den_coeff10, num10] at hcoeff
  linarith


noncomputable def dParent : PowerSeries ℤ :=
  (1-X)^3 * (1+X)^2 * (1+X^2)^2

private lemma denParent_poly :
    dParent = 1-X-2*X^4+2*X^5+X^8-X^9 := by
  dsimp [dParent]
  ring

private lemma denParent_coeff10 (a : ℕ → ℤ) :
    (coeff 10) (mk a * dParent) =
      a 10 - a 9 - 2*a 6 + 2*a 5 + a 2 - a 1 := by
  rw [denParent_poly]
  rw [mul_comm (mk a)]
  rw [show (2 : ℤ⟦X⟧) = C (2:ℤ) by norm_num]
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add,
             mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_mk]
  norm_num

/-- The exact OEIS A322055 published recurrence (n>8) and rational
    generating function cannot simultaneously hold, because the numerator
    still has coefficient -8 at n=10. This is independent of the automaton. -/
theorem a322055_incompatible (a : ℕ → ℤ)
    (hrec : ∀ n : ℕ, 8 < n →
      a n = a (n-1) + 2*a (n-4) - 2*a (n-5) - a (n-8) + a (n-9))
    (hgf : mk a * dParent = q) : False := by
  have h10 := hrec 10 (by norm_num)
  have hcoeff := congrArg (coeff 10) hgf
  rw [denParent_coeff10, num10] at hcoeff
  linarith

end MSLOeisContradiction

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a322056.main) := by
  rintro ⟨hrec,hgf⟩
  exact MSLOeisContradiction.a322056_incompatible
    (a:=fun n => (OMA.S_oeis_a322056.a n : ℤ))
    (by simpa using hrec)
    (by simpa [MSLOeisContradiction.d,
               MSLOeisContradiction.q] using hgf)

