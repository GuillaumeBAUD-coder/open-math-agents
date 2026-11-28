import OMAStatements.S_oeis_a131607

-- Problem: A131607: Pell companion numbers A001333 without last digit.
-- Upstream: formal-conjectures statements/oeis-a131607.lean:0 (declaration OMA.S_oeis_a131607.main)
-- Credit: @biondadave (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A131607Proof

open OMA.S_oeis_a131607 PowerSeries

lemma P_succ_succ (n : ℕ) : P (n + 2) = 2 * P (n + 1) + P n := rfl

/-- The last digit of `P` has period 12. -/
lemma P_mod_period (n : ℕ) : P (n + 12) % 10 = P n % 10 := by
  have key : ∀ n, P (n + 12) % 10 = P n % 10 ∧ P (n + 13) % 10 = P (n + 1) % 10 := by
    intro n
    induction n with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : P (k + 1 + 13) = 2 * P (k + 13) + P (k + 12) := P_succ_succ (k + 12)
      have h2 : P (k + 1 + 1) = 2 * P (k + 1) + P k := P_succ_succ k
      rw [h1, h2]
      omega
  exact (key n).1

/-- The digit combination killed by the recurrence operator. -/
lemma digits_rec (n : ℕ) :
    ((P (n + 9) % 10 : ℕ) : ℤ) - 3 * (P (n + 8) % 10 : ℕ) + (P (n + 7) % 10 : ℕ) +
      (P (n + 6) % 10 : ℕ) + (P (n + 3) % 10 : ℕ) - 3 * (P (n + 2) % 10 : ℕ) +
      (P (n + 1) % 10 : ℕ) + (P n % 10 : ℕ) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 12
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have := ih m (by omega)
      have e : ∀ j, P (m + 12 + j) % 10 = P (m + j) % 10 := fun j => by
        rw [show m + 12 + j = (m + j) + 12 by ring]; exact P_mod_period _
      have e0 : P (m + 12) % 10 = P m % 10 := P_mod_period m
      rw [e 9, e 8, e 7, e 6, e 3, e 2, e 1, e0]
      exact this

/-- The recurrence operator kills `P` exactly. -/
lemma P_rec (n : ℕ) :
    (P (n + 9) : ℤ) - 3 * P (n + 8) + P (n + 7) + P (n + 6) + P (n + 3) - 3 * P (n + 2) +
      P (n + 1) + P n = 0 := by
  have h : ∀ k, (P (n + k + 2) : ℤ) = 2 * P (n + k + 1) + P (n + k) := fun k => by
    exact_mod_cast P_succ_succ (n + k)
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [add_zero, add_assoc] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  linarith

lemma ten_a (k : ℕ) : (10 * a k : ℤ) + (P k % 10 : ℕ) = P k := by
  exact_mod_cast Nat.div_add_mod (P k) 10

/-- The recurrence holds from `n = 9` on (stronger than the stated `n > 12`). -/
lemma a_rec (n : ℕ) :
    (a (n + 9) : ℤ) = 3 * a (n + 8) - a (n + 7) - a (n + 6) - a (n + 3) + 3 * a (n + 2) -
      a (n + 1) - a n := by
  have := P_rec n
  have := digits_rec n
  have := ten_a (n + 9); have := ten_a (n + 8); have := ten_a (n + 7); have := ten_a (n + 6)
  have := ten_a (n + 3); have := ten_a (n + 2); have := ten_a (n + 1); have := ten_a n
  omega

lemma coeff_mk_mul_X_pow (f : ℕ → ℤ) (j n : ℕ) :
    coeff n (mk f * X ^ j) = if j ≤ n then f (n - j) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) * (1 + X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - X ^ 2 + X ^ 4) : PowerSeries ℤ) =
      X ^ 4 * (1 + X - 2 * X ^ 2 + X ^ 3 + X ^ 4) := by
  set f : ℕ → ℤ := fun n => (a n : ℤ) with hf
  have hL : mk f * ((1 - X) * (1 + X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - X ^ 2 + X ^ 4) :
        PowerSeries ℤ) =
      mk f * X ^ 0 - mk f * X ^ 1 - mk f * X ^ 1 - mk f * X ^ 1 + mk f * X ^ 2 + mk f * X ^ 3 +
        mk f * X ^ 6 - mk f * X ^ 7 - mk f * X ^ 7 - mk f * X ^ 7 + mk f * X ^ 8 +
        mk f * X ^ 9 := by
    ring
  have hR : (X ^ 4 * (1 + X - 2 * X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      X ^ 4 + X ^ 5 - X ^ 6 - X ^ 6 + X ^ 7 + X ^ 8 := by
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_mk_mul_X_pow, coeff_X_pow]
  rcases lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [hf, a] <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have h := a_rec m
    simp only [if_true,
      show 0 ≤ m + 9 from by omega, show 1 ≤ m + 9 from by omega, show 2 ≤ m + 9 from by omega,
      show 3 ≤ m + 9 from by omega, show 6 ≤ m + 9 from by omega, show 7 ≤ m + 9 from by omega,
      show 8 ≤ m + 9 from by omega, show 9 ≤ m + 9 from by omega,
      show m + 9 ≠ 4 from by omega, show m + 9 ≠ 5 from by omega, show m + 9 ≠ 6 from by omega,
      show m + 9 ≠ 7 from by omega, show m + 9 ≠ 8 from by omega, if_false, hf,
      show m + 9 - 0 = m + 9 from rfl, show m + 9 - 1 = m + 8 from rfl,
      show m + 9 - 2 = m + 7 from rfl, show m + 9 - 3 = m + 6 from rfl,
      show m + 9 - 6 = m + 3 from rfl, show m + 9 - 7 = m + 2 from rfl,
      show m + 9 - 8 = m + 1 from rfl, show m + 9 - 9 = m from rfl]
    linarith

end OMA.A131607Proof

open OMA.A131607Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a131607.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have h := a_rec m
  simp only [show m + 9 - 1 = m + 8 from rfl, show m + 9 - 2 = m + 7 from rfl,
    show m + 9 - 3 = m + 6 from rfl, show m + 9 - 6 = m + 3 from rfl,
    show m + 9 - 7 = m + 2 from rfl, show m + 9 - 8 = m + 1 from rfl,
    show m + 9 - 9 = m from rfl]
  exact h
