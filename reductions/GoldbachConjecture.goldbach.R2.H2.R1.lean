import OMAReductions.R_GoldbachConjecture_goldbach_R2

-- Reduction GoldbachConjecture.goldbach.R2.H2.R1 of step GoldbachConjecture.goldbach.R2.H2
-- Credit: @nisbenz

/-!
# Main-term / Bombieri–Vinogradov split of the short-divisor Goldbach bound

Decomposes the short-divisor sum `S_D(n)` at cutoff `D = ⌊√(n / ⌊√√n⌋)⌋ ≈ n^{3/8}` into its
exact Euler-totient main term `n * M_D(n)` and the weighted arithmetic-progression error
`∑_{d ≤ D, (d,n)=1} μ(d) log d * (θ(n; d, n) - n / φ(d))`:

* `H1` (elementary truncated singular series): for every even `n > 50000`,
  `M_D(n) = -∑_{d ≤ D, (d,n)=1} μ(d) log(d) / φ(d) > 1`.
  (Numerically `≥ 1.1729` on `[50002, 100000]` and asymptotically `≥ 2 C_2 ≈ 1.3203`.)
* `H2` (Bombieri–Vinogradov weighted L¹ error at `D ≈ n^{3/8}`): for every even `n > 50000`,
  `∑_{d ≤ D, (d,n)=1} |μ(d)| log(d) |θ(n; d, n) - n / φ(d)| ≤ n / 5`.
  (Numerically `≤ 0.096 n` on `[50002, 60000]` and asymptotically `O_A(n / log^A n)`.)
-/

namespace OMA.R_GoldbachConjecture_goldbach_R2_H2_R1

/-- Elementary truncated singular-series lower bound `M_D(n) > 1` for even `n > 50000`. -/
def H1 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    (1 : ℝ) <
      -(∑ d ∈ (Finset.Icc 1 (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)))).filter (fun d => Nat.Coprime d n),
        (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) / (Nat.totient d : ℝ))

/-- Bombieri–Vinogradov weighted L¹ prime-in-AP error bound at cutoff `D ≈ n^{3/8}`. -/
def H2 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    (∑ d ∈ (Finset.Icc 1 (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)))).filter (fun d => Nat.Coprime d n),
      |(ArithmeticFunction.moebius d : ℝ)| * Real.log (d : ℝ) *
        |(∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ d ∣ (n - x)),
            Real.log (x : ℝ)) - (n : ℝ) / (Nat.totient d : ℝ)|) ≤ (1 : ℝ) / 5 * n

theorem main : H1 → H2 → OMA.R_GoldbachConjecture_goldbach_R2.H2 := by
  intro h1 h2 n hn heven
  let D : ℕ := Nat.sqrt (n / Nat.sqrt (Nat.sqrt n))
  let S : Finset ℕ := (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n)
  let θ : ℕ → ℝ := fun d =>
    ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ d ∣ (n - x)),
      Real.log (x : ℝ)
  have hM : (1 : ℝ) <
      -(∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) / (Nat.totient d : ℝ)) :=
    h1 n hn heven
  have hE : (∑ d ∈ S, |(ArithmeticFunction.moebius d : ℝ)| * Real.log (d : ℝ) *
      |θ d - (n : ℝ) / (Nat.totient d : ℝ)|) ≤ (1 : ℝ) / 5 * n :=
    h2 n hn heven
  have hdecomp :
      -(∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) * θ d) =
      (n : ℝ) * (-(∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) / (Nat.totient d : ℝ))) -
      (∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        (θ d - (n : ℝ) / (Nat.totient d : ℝ))) := by
    rw [mul_neg, Finset.mul_sum]
    have hadd :
        (∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) * θ d) =
        (∑ d ∈ S, (n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) / (Nat.totient d : ℝ))) +
        (∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          (θ d - (n : ℝ) / (Nat.totient d : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    linarith
  have herr_le :
      (∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        (θ d - (n : ℝ) / (Nat.totient d : ℝ))) ≤
      (∑ d ∈ S, |(ArithmeticFunction.moebius d : ℝ)| * Real.log (d : ℝ) *
        |θ d - (n : ℝ) / (Nat.totient d : ℝ)|) := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      exact_mod_cast this
    have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
    have h1' : (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        (θ d - (n : ℝ) / (Nat.totient d : ℝ)) ≤
        |(ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
          (θ d - (n : ℝ) / (Nat.totient d : ℝ))| := le_abs_self _
    rwa [abs_mul, abs_mul, abs_of_nonneg hlog] at h1'
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmain_gt : (n : ℝ) <
      (n : ℝ) * (-(∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) / (Nat.totient d : ℝ))) := by
    have := mul_lt_mul_of_pos_left hM hn_pos
    simpa only [mul_one] using this
  change (4 : ℝ) / 5 * n < -(∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) * θ d)
  linarith

end OMA.R_GoldbachConjecture_goldbach_R2_H2_R1
