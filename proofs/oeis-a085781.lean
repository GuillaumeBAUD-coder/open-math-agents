import OMAStatements.S_oeis_a085781

-- Credit: @yuka30240
open OMA.S_oeis_a085781 Nat

theorem OMA.solution : type_of% @OMA.S_oeis_a085781.main := by
  let b (k : ℕ) := (2 * k + 1).choose (k + 1)
  -- Pascal's identity and symmetry give the ratio of consecutive odd-row coefficients.
  have step (k : ℕ) : b (k + 1) * (k + 2) = (2 * k + 3) * (b k + b k) := by
    unfold b
    rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by omega, ← add_one_mul_choose_eq,
      choose_succ_succ' (2 * k + 1) k, choose_symm_half]
  rintro (_ | _ | _ | k) hk <;> try omega
  have h₀ := step k
  have h₁ := step (k + 1)
  have h₂ := step (k + 2)
  zify at h₀ h₁ h₂
  simp [a, pow_succ]
  -- The weights 1, -4, 4 from @dreamzzz-dev's desk note also cancel the powers of two.
  linear_combination 2 * h₂ - 8 * h₁ + 8 * h₀
