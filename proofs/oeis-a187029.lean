import OMAStatements.S_oeis_a187029
import Mathlib

/-!
# OEIS A187029: generating function and recurrence

Every admissible 4-point tour has bounding-box spans `w, h ≤ 6` (checked by the kernel over all
`16^3` move triples), so for `n ≥ 6` each summand `(n - w) * (n - h)` is a quadratic polynomial in
`n` and has vanishing third difference. This gives the recurrence for `n > 8`; the generating
function follows coefficientwise, with the coefficients up to `x^8` evaluated directly.
-/

namespace OMA.A187029Proof

open OMA.S_oeis_a187029 PowerSeries

theorem bound : ∀ i j k : Fin 16,
    (spans i j k).all (fun wh => decide (wh.1 ≤ 6 ∧ wh.2 ≤ 6)) = true := by
  decide +kernel

theorem place_rec (s : Option (ℕ × ℕ))
    (hs : s.all (fun wh => decide (wh.1 ≤ 6 ∧ wh.2 ≤ 6)) = true) (m : ℕ) :
    (placements (m + 9) s : ℤ) =
      3 * placements (m + 8) s - 3 * placements (m + 7) s + placements (m + 6) s := by
  rcases s with _ | ⟨w, h⟩
  · simp [placements]
  · simp only [Option.all, decide_eq_true_eq] at hs
    obtain ⟨hw, hh⟩ := hs
    simp only [placements]
    push_cast [Nat.cast_sub (show w ≤ m + 9 by omega), Nat.cast_sub (show h ≤ m + 9 by omega),
      Nat.cast_sub (show w ≤ m + 8 by omega), Nat.cast_sub (show h ≤ m + 8 by omega),
      Nat.cast_sub (show w ≤ m + 7 by omega), Nat.cast_sub (show h ≤ m + 7 by omega),
      Nat.cast_sub (show w ≤ m + 6 by omega), Nat.cast_sub (show h ≤ m + 6 by omega)]
    ring

theorem term_rec (m : ℕ) :
    (term (m + 9) : ℤ) = 3 * term (m + 8) - 3 * term (m + 7) + term (m + 6) := by
  have h : ∀ i j k : Fin 16, (placements (m + 9) (spans i j k) : ℤ) =
      3 * placements (m + 8) (spans i j k) - 3 * placements (m + 7) (spans i j k) +
        placements (m + 6) (spans i j k) := fun i j k => place_rec _ (bound i j k) m
  simp only [term, Nat.cast_sum, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]

theorem t2 : term 2 = 24 := by decide +kernel
theorem t3 : term 3 = 1344 := by decide +kernel
theorem t4 : term 4 = 7056 := by decide +kernel
theorem t5 : term 5 = 19568 := by decide +kernel
theorem t6 : term 6 = 39348 := by decide +kernel
theorem t7 : term 7 = 66360 := by decide +kernel
theorem t8 : term 8 = 100380 := by decide +kernel
theorem t1 : term 1 = 0 := by decide +kernel
theorem t0 : term 0 = 0 := by decide +kernel

theorem gf : PowerSeries.mk (fun n => (term n : ℤ)) * (1 - X) ^ 3 =
    4 * X ^ 2 * (6 + 318 * X + 774 * X ^ 2 + 602 * X ^ 3 + 117 * X ^ 4 - 9 * X ^ 5 -
      56 * X ^ 6) := by
  set f := PowerSeries.mk (fun n => (term n : ℤ)) with hf
  have lhs : f * (1 - X) ^ 3 = f - C 3 * (f * X ^ 1) + C 3 * (f * X ^ 2) - f * X ^ 3 := by
    simp only [map_ofNat]; ring
  have rhs : (4 * X ^ 2 * (6 + 318 * X + 774 * X ^ 2 + 602 * X ^ 3 + 117 * X ^ 4 - 9 * X ^ 5 -
      56 * X ^ 6) : ℤ⟦X⟧) = C 24 * X ^ 2 + C 1272 * X ^ 3 + C 3096 * X ^ 4 + C 2408 * X ^ 5 +
        C 468 * X ^ 6 - C 36 * X ^ 7 - C 224 * X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [lhs, rhs]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hf, coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [t0, t1, t2, t3, t4, t5, t6, t7, t8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have := term_rec m
    rw [if_pos (show 1 ≤ m + 9 by omega), if_pos (show 2 ≤ m + 9 by omega),
      if_pos (show 3 ≤ m + 9 by omega), show m + 9 - 1 = m + 8 by omega,
      show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega]
    generalize (term (m + 9) : ℤ) = a at this ⊢
    generalize (term (m + 8) : ℤ) = b at this ⊢
    generalize (term (m + 7) : ℤ) = c at this ⊢
    generalize (term (m + 6) : ℤ) = d at this ⊢
    simp
    linarith

end OMA.A187029Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a187029.main := by
  refine ⟨OMA.A187029Proof.gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
    show m + 9 - 3 = m + 6 by omega]
  exact OMA.A187029Proof.term_rec m
