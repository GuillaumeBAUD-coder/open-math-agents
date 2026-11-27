import FormalConjectures.ErdosProblems.«470»

-- Reduction Erdos470.erdos_470.parts.ii.R3 of Erdős Problem 470 — ii
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primitive weird numbers `2^k p q`: the exact criterion and the existence question

Write `M = 2^(k+1)` and let `p ≠ q` be primes larger than `M`. The proper divisors of
`n = 2^k p q` are `2^i`, `2^i p`, `2^i q` (`i ≤ k`) and `2^i p q` (`i < k`); sums of distinct
`2^i` are exactly `0, …, M - 1`. With the excess `e = σ(n) - 2n = (M-1)(p+1)(q+1) - M p q`,
`n` is pseudoperfect iff `e` is a sum of distinct proper divisors, and since `e < p q` this means
`e = a + b p + c q` with `a, b, c < M`. Every proper divisor of `n` is deficient (as `p, q > M`).

* `H1` (elementary): if `n` is abundant and `e` avoids every block `[b p + c q, b p + c q + M)`
  with `b, c < M`, then `n` is primitive weird. Checked by brute force for all
  `n ≤ 1.5·10^6` of this shape: the criterion is exact there.
* `H2` (the open core): for infinitely many `k` such primes exist.

`H2` is implied by `R1.H2` (Melfi's configuration `2^(k+2) - a, 2^(k+2) + b`) and by `R2.H2`
(`e < q`, `e mod p ≥ M`), so it is the most permissive existence statement for this family.
Equivalently, with `s = p - M + 1` and `C = (M - 1)(p + 1)` one has `e = C - s q`, and the block
condition is a condition on `C mod q` together with finitely many side conditions; for fixed `p`
the admissible `q` are isolated integers of the shape `⌊(C - u) / t⌋` with `t ≥ s`.
-/

namespace OMA.R_Erdos470_erdos_470_parts_ii_R3

/-- The exact (sufficient) criterion for `2^k p q` to be primitive weird. -/
def H1 : Prop :=
  ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
    (∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →
      ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1))) →
    Erdos470.PrimitiveWeird (2 ^ k * p * q)

/-- For infinitely many `k` there are primes `p ≠ q > 2^(k+1)` meeting the criterion. -/
def H2 : Prop :=
  ∀ K : ℕ, ∃ k p q : ℕ, K ≤ k ∧ p.Prime ∧ q.Prime ∧ 2 ^ (k + 1) < p ∧ 2 ^ (k + 1) < q ∧ p ≠ q ∧
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) ∧
    (∀ b c : ℕ, b < 2 ^ (k + 1) → c < 2 ^ (k + 1) →
      ¬ (b * p + c * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q ∧
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q < b * p + c * q + 2 ^ (k + 1)))

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.parts.ii := by
  intro h1 h2
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, p, q, hk, hp, hq, hpM, hqM, hpq, hab, hrep⟩ := h2 (B + 1)
  have hmem : 2 ^ k * p * q ≤ B := hB (h1 k p q hp hq hpM hqM hpq hab hrep)
  have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hle : 2 ^ k ≤ 2 ^ k * p * q := by
    calc 2 ^ k = 2 ^ k * 1 * 1 := by ring
      _ ≤ 2 ^ k * p * q := by gcongr <;> [exact hp.one_lt.le; exact hq.one_lt.le]
  omega

end OMA.R_Erdos470_erdos_470_parts_ii_R3
