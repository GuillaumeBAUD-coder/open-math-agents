import OMAStatements.S_oeis_a393833
import Mathlib.NumberTheory.PrimesCongruentOne

namespace A393833Proof

open OMA.S_oeis_a393833

/-- The exponent fixes the number of divisors, and every divisor is 1 modulo the modulus. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ k.divisors.card = 2 * n + 2 ∧
    residues n k = (residues n k).reverse := by
  intro n hn
  obtain ⟨p, hp, _, hpmod⟩ := Nat.exists_prime_gt_modEq_one (k := n) 0 (by omega)
  let e := 2 * n + 1
  refine ⟨p ^ e, pow_pos hp.pos _, ?_, ?_⟩
  · simp [Nat.divisors_prime_pow hp, e]
  · have hconstant : ∀ r ∈ residues n (p ^ e), r = 1 % n := by
      intro r hr
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      have hd' : d ∈ (p ^ e).properDivisors := by simpa using hd
      obtain ⟨j, _, rfl⟩ := (Nat.mem_properDivisors_prime_pow hp e).mp hd'
      simpa [Nat.ModEq] using hpmod.pow j
    have hrepl := List.eq_replicate_of_mem hconstant
    exact hrepl.trans (by simpa using (congrArg List.reverse hrepl).symm)

end A393833Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a393833.main := A393833Proof.main
