import OMAStatements.S_oeis_a218981

/-! OEIS A218981: infinitely many `n` split as `w + x + y + z` with
`σ n = σ w + σ x + σ y + σ z`.

Take `p = 10 t + 1`, which is prime to `2` and `5`, and `n = 5 p = p + p + p + 2 p`. Since `σ` is
multiplicative, `σ (5 p) = 6 σ p` and `σ (2 p) = 3 σ p`, so `σ n = 3 σ p + σ (2 p)`. The map
`t ↦ 5 (10 t + 1)` is injective, hence the set of terms is infinite. -/

namespace OpenMath.A218981

open OMA.S_oeis_a218981

private theorem isTerm (t : ℕ) : IsTerm (5 * (10 * t + 1)) := by
  generalize hp : 10 * t + 1 = p
  have h5 : Nat.Coprime 5 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 (by omega)
  have h2 : Nat.Coprime 2 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have s5 : ArithmeticFunction.sigma 1 5 = 6 := by
    rw [ArithmeticFunction.sigma_one_apply]
    decide
  have s2 : ArithmeticFunction.sigma 1 2 = 3 := by
    rw [ArithmeticFunction.sigma_one_apply]
    decide
  refine ⟨p, p, p, 2 * p, by omega, by omega, by omega, by omega, by omega, ?_⟩
  show ArithmeticFunction.sigma 1 (5 * p) = ArithmeticFunction.sigma 1 p +
    ArithmeticFunction.sigma 1 p + ArithmeticFunction.sigma 1 p + ArithmeticFunction.sigma 1 (2 * p)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h5,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h2, s5, s2]
  omega

theorem main : Set.Infinite {n : ℕ | IsTerm n} := by
  refine Set.infinite_of_injective_forall_mem (f := fun t => 5 * (10 * t + 1)) ?_ isTerm
  intro a b h
  have h' : 5 * (10 * a + 1) = 5 * (10 * b + 1) := h
  omega

end OpenMath.A218981

theorem OMA.solution : type_of% @OMA.S_oeis_a218981.main := OpenMath.A218981.main
