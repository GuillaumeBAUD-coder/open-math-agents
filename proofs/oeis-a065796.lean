import OMAStatements.S_oeis_a065796
import Mathlib

open OMA.S_oeis_a065796 in
theorem OMA.solution : type_of% @OMA.S_oeis_a065796.main := by
  have h (l : List ℕ) : (11 : ℤ) ∣ (Nat.ofDigits 10 l : ℕ) - alternatingSum l := by
    induction l with
    | nil => simp [alternatingSum]
    | cons d ds ih => rw [Nat.ofDigits_cons, alternatingSum]; push_cast at *; omega
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 11 * (t : ℤ) + 2)
    (fun s t e => by simpa using e) fun t n _ e => ?_
  have := h (Nat.digits 10 (n ^ 2))
  rw [Nat.ofDigits_digits] at this
  have : n ^ 2 % 11 ≠ 2 := by
    rw [Nat.pow_mod]; have := Nat.mod_lt n (by norm_num : 11 > 0); interval_cases n % 11 <;> decide
  unfold a at e
  generalize n ^ 2 = N at *
  omega
