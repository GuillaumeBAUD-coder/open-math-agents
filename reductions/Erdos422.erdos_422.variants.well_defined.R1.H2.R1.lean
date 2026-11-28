import OMAReductions.R_Erdos422_erdos_422_variants_well_defined_R1

-- Reduction Erdos422.erdos_422.variants.well_defined.R1.H2.R1
-- of step Erdos422.erdos_422.variants.well_defined.R1.H2
-- Credit: @marcusbuffett

/-!
# Hofstadter's Q-sequence: a verified range, and the open tail

The parent step says that a function `q` with `q 1 = q 2 = 1` satisfying the guarded recurrence
`q n = q (n - q (n - 1)) + q (n - q (n - 2))` (with value `0` when a reference would leave the
positive terms already computed) has `q n ≤ n` for all `n ≥ 512`. With the prefix checked by its
sibling step this is the statement that Hofstadter's Q-sequence (OEIS A005185) is well defined,
which is open.

* `H1` (a range, by computation): `q n ≤ n` for `512 ≤ n ≤ 30000`. The recurrence determines the
  values one after another, so this is a finite check of the first 30000 terms.
* `H2`: `q n ≤ n` for all `n > 30000`. This is the open problem and stays open.
-/

namespace OMA.R_Erdos422_erdos_422_variants_well_defined_R1_H2_R1

/-- The bound in the range `512 ≤ n ≤ 30000`. -/
def H1 : Prop :=
  ∀ q : ℕ → ℕ, q 1 = 1 → q 2 = 1 →
    (∀ n : ℕ, 2 < n → q n =
      if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
        q (n - q (n - 1)) + q (n - q (n - 2)) else 0) →
    ∀ n : ℕ, 512 ≤ n → n ≤ 30000 → q n ≤ n

/-- The open tail: the bound for every `n > 30000`. -/
def H2 : Prop :=
  ∀ q : ℕ → ℕ, q 1 = 1 → q 2 = 1 →
    (∀ n : ℕ, 2 < n → q n =
      if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
        q (n - q (n - 1)) + q (n - q (n - 2)) else 0) →
    ∀ n : ℕ, 30000 < n → q n ≤ n

theorem main : H1 → H2 → OMA.R_Erdos422_erdos_422_variants_well_defined_R1.H2 := by
  intro h1 h2 q q1 q2 hrec n hn
  by_cases hle : n ≤ 30000
  · exact h1 q q1 q2 hrec n hn hle
  · exact h2 q q1 q2 hrec n (by omega)

end OMA.R_Erdos422_erdos_422_variants_well_defined_R1_H2_R1
