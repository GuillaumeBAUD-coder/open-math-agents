import Mathlib

namespace OMA.S_oeis_a228885

/-- The `n × n` matrix with `(i, j)`-entry `1` if `gcd((i + 1) + (j + 1), n) = 1` and `0` otherwise
(for `0 ≤ i, j < n`, corresponding to `1 ≤ i, j ≤ n`). -/
def coprimeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if Nat.Coprime ((i.val + 1) + (j.val + 1)) n then 1 else 0

/-- OEIS A228885 Conjectures (Zhi-Wei Sun & Ridouane Oudra):
1. For all `n ≥ 1`, `det(coprimeMatrix n) = (-1)^(n / 2) * ∏_{k=1}^n φ(gcd(n, k))` if `n` is
   squarefree, and `0` otherwise.
2. In particular, if `n ≥ 1` is squarefree, then `(-1)^(n * (n - 1) / 2) * det(coprimeMatrix n) > 0`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (coprimeMatrix n).det =
        (-1 : ℤ) ^ (n / 2) *
          (if Squarefree n then ∏ k ∈ Finset.Icc 1 n, (Nat.totient (Nat.gcd n k) : ℤ) else 0) ∧
      (Squarefree n → 0 < (-1 : ℤ) ^ (n * (n - 1) / 2) * (coprimeMatrix n).det) := by
  sorry

end OMA.S_oeis_a228885
