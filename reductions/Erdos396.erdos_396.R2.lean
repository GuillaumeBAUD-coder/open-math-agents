import FormalConjectures.ErdosProblems.«396»

-- Reduction Erdos396.erdos_396.R2 of Erdős problem 396
-- Credit: @MBimrose

/-!
# Erdős 396: the cases `k ≤ 16` by explicit witnesses, and the open rest

The problem asks whether for every `k` there is an `n` such that `n (n - 1) ⋯ (n - k)` divides
the central binomial coefficient `C(2n, n)`.

* `H1`: this holds for `k ≤ 16`, with explicit witnesses `n = 1, 2, 2480, 8178, 45153, 3648841,
  7979090, 101130029, 339949252, 1019547844, 17609764994, 1070858041585, 5048891644646,
  18253129921842, 359503904702190, 2394789405254721, 20021368432952099` (the least witnesses,
  OEIS A375077). The divisibility is *not* checked by evaluating `C(2n, n)` — for `k = 5` that
  number already has millions of digits. Instead Kummer's theorem is used: the exponent of a prime
  `p` in `C(2n, n)` is the number of carries in `n + n` base `p`
  (`Nat.factorization_choose`), so every prime power that must divide `C(2n, n)` is verified by a
  small computation. The certificate is dischargeable by `decide`, so `H1` is a theorem
  (step `Erdos396.erdos_396.R2.H1`); the reduction below only isolates it.
* `H2`: it holds for every `k ≥ 17`. This is what remains open (witnesses are known for a few
  further `k` only, and no construction for all `k` is known).
-/

namespace OMA.R_Erdos396_erdos_396_R2

/-- The cases `k ≤ 16`, with explicit witnesses (proved separately as step `R2.H1`). -/
def H1 : Prop :=
  ∀ k : ℕ, k ≤ 16 → ∃ n : ℕ, Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

/-- The open part: all `k ≥ 17`. -/
def H2 : Prop :=
  ∀ k : ℕ, 17 ≤ k → ∃ n : ℕ, Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  intro h1 h2 k
  by_cases h : k ≤ 16
  · exact h1 k h
  · exact h2 k (by omega)

end OMA.R_Erdos396_erdos_396_R2
