import OMAStatements.S_oeis_a080958

-- Problem: A080958: a(n) = n!*(2/1 - 3/2 + 4/3 - ... + s*(n+1)/n), where s = (-1)^(n+1).
-- Upstream: formal-conjectures statements/oeis-a080958.lean:0 (declaration OMA.S_oeis_a080958.main)
-- Credit: @weizj99 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a080958

lemma a_succ_step (k : ℕ) :
    a (k + 1) = ((k : ℚ) + 1) * a k +
      (-1 : ℚ) ^ (k + 2) * (k.factorial : ℚ) * ((k : ℚ) + 2) := by
  have hi : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hf : k + 1 ∉ Finset.Icc 1 k := by simp
  have hd : (k : ℚ) + 1 ≠ 0 := by positivity
  unfold a
  rw [hi, Finset.sum_insert hf, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hd]
  ring

end OMA.S_oeis_a080958

open OMA.S_oeis_a080958

theorem OMA.solution : type_of% @OMA.S_oeis_a080958.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    change -(((k + 1 : ℕ) : ℚ) + 1) * a ((k + 1) + 1) + a (k + 1) +
      ((k + 1 : ℕ) : ℚ) ^ 2 * (((k + 1 : ℕ) : ℚ) + 2) * a k = 0
    rw [a_succ_step (k + 1), a_succ_step k]
    have hs : (-1 : ℚ) ^ ((k + 1) + 2) = (-1 : ℚ) ^ (k + 2) * (-1) :=
      pow_succ _ _
    rw [hs, Nat.factorial_succ]
    push_cast
    ring
