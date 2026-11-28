import OMAStatements.S_oeis_a316357
import Mathlib

open OMA.S_oeis_a316357 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a316357.main := by
  have e (n : ℕ) : shell (n+6) - shell (n+5) + shell (n+4) - 2*shell (n+3) + shell (n+2)
      - shell (n+1) + shell n = 0 := by
    induction n using Nat.strong_induction_on with | _ n ih =>
    obtain h | h := lt_or_ge n 12
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      have := ih m (by omega)
      simp [shell, add_assoc] at this ⊢
      linarith
  refine ⟨fun n => by simp [total]; linarith [e n], ?_⟩
  simp only [← map_ofNat (C (R := ℤ))]
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;>
  simp [-eq_intCast, pow_succ, sub_mul, add_mul, mul_assoc, total, shell, coeff_X, coeff_one]
  linarith [e n]
