import OMAStatements.S_oeis_a005867

namespace OMA.S_oeis_a005867

private theorem nthPositive (k : ℕ) : Nat.nth (fun m : ℕ => 0 < m) k = k + 1 := by
  have infinite : (Set.ofPred fun m : ℕ => 0 < m).Infinite :=
    Set.infinite_of_injective_forall_mem Nat.succ_injective Nat.succ_pos
  have h := Nat.nth_comp_of_strictMono (p := fun m : ℕ => 0 < m) (n := k)
    (f := Nat.succ) (fun _ _ lt => Nat.succ_lt_succ lt)
    (fun m hm => ⟨m - 1, by omega⟩)
    (fun hf => (infinite hf).elim)
  simpa only [Nat.zero_lt_succ, Nat.nth_true] using h.symm

end OMA.S_oeis_a005867

open OMA.S_oeis_a005867 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005867.main) := by
  intro claim
  obtain ⟨P, _, symmetric, identity⟩ := claim 0
  have periodZero : period 0 = 1 := by simp [period]
  rw [periodZero, pow_one] at identity
  have hcoeff (j : ℕ) : PowerSeries.coeff j (roughSeries 0) = (j : ℤ) + 1 := by
    simp [roughSeries, primePrefix, nthPositive]
  have hconstant : PowerSeries.constantCoeff (roughSeries 0) = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hcoeff 0
  have zeroCoeff : P.coeff 0 = 1 := by
    simpa [hconstant, Polynomial.constantCoeff_coe] using
      (congrArg PowerSeries.constantCoeff identity).symm
  have oneCoeff : P.coeff 1 = 0 := by
    simpa [PowerSeries.coeff_one_mul, PowerSeries.coeff_X, PowerSeries.coeff_one,
      hconstant, hcoeff, Polynomial.coeff_coe] using
      (congrArg (PowerSeries.coeff 1) identity).symm
  have hsym := symmetric 0 (by omega)
  rw [periodZero, Nat.sub_zero, zeroCoeff, oneCoeff] at hsym
  omega
