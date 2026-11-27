import Mathlib

/-!
# Alexa's Conjecture on Primality

Source: https://www.openproblemgarden.org/op/alexas_conjecture_on_primality
Credit: @Hyvok

Definition (from the source): for a natural number `p` and each `i`, let `r_i` be the unique integer
with `(2i+1)^(p-1) ≡ r_i (mod p)` and `0 ≤ r_i < p`.

Conjecture (Alexa, posted 2012): a natural number `p ≥ 8` is prime if and only if
`∑_{i=1}^{⌊∛p / 2⌋} r_i = ⌊∛p / 2⌋`.

Formalization notes:
* `r p i = (2i+1)^(p-1) % p` is exactly the least nonnegative residue described in the source.
* `⌊∛p / 2⌋` is the floor of the real number `p^(1/3) / 2`.
* The source remarks that the statement is obviously true when `p` is prime (then every `r_i = 1`,
  since `2i + 1 ≤ ∛p < p` is coprime to `p`), so the content is the converse for composite `p`.
  Comments on the source report computational verification up to `10^8`.
-/

namespace OMA.S_opg_alexas_conjecture_on_primality

/-- `r p i`: the least nonnegative residue of `(2i+1)^(p-1)` modulo `p`. -/
def r (p i : ℕ) : ℕ := (2 * i + 1) ^ (p - 1) % p

/-- The upper limit `⌊∛p / 2⌋` of the sum. -/
noncomputable def bound (p : ℕ) : ℕ := ⌊(p : ℝ) ^ ((1 : ℝ) / 3) / 2⌋₊

/-- Alexa's conjecture: for `p ≥ 8`, `p` is prime iff `∑_{i=1}^{⌊∛p/2⌋} r_i = ⌊∛p/2⌋`. -/
theorem main :
    ∀ p : ℕ, 8 ≤ p → (p.Prime ↔ ∑ i ∈ Finset.Icc 1 (bound p), r p i = bound p) := by
  sorry

end OMA.S_opg_alexas_conjecture_on_primality
