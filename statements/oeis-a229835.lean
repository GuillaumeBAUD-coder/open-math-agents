import Mathlib

/-!
# A229835: Number of ways to write n = (p - 1)/6 + q, where p is a prime, and q is a term of the sequence A000009.

Source: https://oeis.org/A229835
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 2*10^8): a(n) > 0 for all n > 1.
Also, any integer n > 1 can be written as (p + 1)/6 + q, where p is a prime and q is a term of
A000009.

Formalization notes:
* A000009(k) is the number of partitions of k into distinct parts (k ≥ 0), defined below.
* (p - 1)/6 must be an integer for the representation, so p ≡ 1 (mod 6) is required (and
  p ≡ 5 (mod 6) for (p + 1)/6); both are stated with divisibility.
* Controls (computed): both claims hold for 1 < n < 3000.
-/

namespace OMA.S_oeis_a229835

/-- A000009(k): the number of partitions of `k` into distinct parts. -/
noncomputable def q (k : ℕ) : ℕ := Fintype.card {π : Nat.Partition k // π.parts.Nodup}

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ 6 ∣ p - 1 ∧ (p - 1) / 6 + q k = n) ∧
      ∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ 6 ∣ p + 1 ∧ (p + 1) / 6 + q k = n := by
  sorry

end OMA.S_oeis_a229835
