import OMAStatements.S_oeis_a025527

-- Problem: A025527: a(n) = n!/lcm{1,2,...,n} = (n-1)!/lcm{C(n-1,0), C(n-1,1), ..., C(n-1,n-1)}.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a025527.main)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The identity holds for every `m`, not only `m = p - 1`: `m!` and `lcm(1, …, m)` have the
same prime factors (the primes `≤ m`), so `φ(m!) / φ(L) = m! / L`. -/

namespace OMA.A025527

open OMA.S_oeis_a025527

lemma L_dvd (m : ℕ) : L m ∣ m.factorial :=
  Finset.lcm_dvd fun i hi => Nat.dvd_factorial (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2

lemma L_pos (m : ℕ) : 0 < L m :=
  Nat.pos_of_ne_zero fun h => (Nat.factorial_pos m).ne' (Nat.eq_zero_of_zero_dvd (h ▸ L_dvd m))

lemma primeFactors_eq (m : ℕ) : (L m).primeFactors = m.factorial.primeFactors := by
  apply le_antisymm
  · exact Nat.primeFactors_mono (L_dvd m) (Nat.factorial_pos m).ne'
  · intro q hq
    rw [Nat.mem_primeFactors] at hq ⊢
    obtain ⟨hqp, hqd, -⟩ := hq
    refine ⟨hqp, ?_, (L_pos m).ne'⟩
    have hle : q ≤ m := (Nat.Prime.dvd_factorial hqp).1 hqd
    exact Finset.dvd_lcm (s := Finset.Icc 1 m) (f := id) (Finset.mem_Icc.2 ⟨hqp.one_le, hle⟩)

/-- If `a ∣ b` and both have the same prime factors, then `φ b = (b / a) * φ a`. -/
lemma totient_of_same (a b : ℕ) (ha : 0 < a) (hab : a ∣ b)
    (hpf : a.primeFactors = b.primeFactors) : Nat.totient b = b / a * Nat.totient a := by
  obtain ⟨k, rfl⟩ := hab
  have hP : (∏ p ∈ a.primeFactors, p) ∣ a := Nat.prod_primeFactors_dvd a
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.totient_eq_div_primeFactors_mul, ← hpf,
    Nat.mul_div_cancel_left _ ha, Nat.mul_comm a k, Nat.mul_div_assoc _ hP, Nat.mul_assoc]

theorem main_all (m : ℕ) :
    m.factorial / L m = Nat.totient m.factorial / Nat.totient (L m) := by
  rw [totient_of_same (L m) m.factorial (L_pos m) (L_dvd m) (primeFactors_eq m),
    Nat.mul_div_cancel _ (Nat.totient_pos.2 (L_pos m))]

end OMA.A025527

theorem OMA.solution : type_of% @OMA.S_oeis_a025527.main := by
  intro p _
  exact OMA.A025527.main_all (p - 1)
