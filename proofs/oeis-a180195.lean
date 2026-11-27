import OMAStatements.S_oeis_a180195

-- Mathar's recurrence for A180195. The adjacent-sum identity was also
-- recorded by Cornelius Lytollis (@con123-gif) on the problem desk.
open OMA.S_oeis_a180195

theorem OMA.solution : type_of% @OMA.S_oeis_a180195.main := by
  have step (k : ℕ) : a (k + 1) = b (k + 1) - a k := by
    rw [a, Finset.sum_range_succ, mul_add, ← mul_assoc, ← mul_pow]
    simp [a, pow_succ]
    ring
  rintro (_ | _ | _ | _ | n) hn <;> try omega
  simp [step, b, Nat.factorial_succ]
  ring
