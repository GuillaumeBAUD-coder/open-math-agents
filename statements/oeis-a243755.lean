import Mathlib

/-!
# A243755: Primes p such that p is a primitive root modulo the next prime p' and also p' is a primitive root modulo p.

Source: https://oeis.org/A243755
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): The sequence contains infinitely many primes. Moreover, there are
infinitely many primes p such that both p and -p are primitive roots modulo the next prime p'
and both p' and -p' are primitive roots modulo p.

Translation notes.
* The primes are enumerated as Nat.nth Nat.Prime i (i = 0, 1, 2, ...), so the next prime
  after Nat.nth Nat.Prime i is Nat.nth Nat.Prime (i + 1).
* g is a primitive root modulo a prime q when its residue has multiplicative order q - 1,
  i.e. IsPrimitiveRoot (g : ZMod q) (q - 1). Modulo 2 every odd residue (order 1) qualifies,
  which matches the listed term 2 (2 is a primitive root mod 3, and 3 is one mod 2).
* -p is taken as the residue -(p : ZMod q).
* This reading reproduces the listed data: 2, 3, 5, 11, 59, 61, 83, 101, 131, 151, 179, 181,
  197, 251, 257, ...; the stronger condition holds for 797, 1709, 1889 among the first 300
  primes (checked by computer).
-/

namespace OMA.S_oeis_a243755

/-- The i-th prime, 0-indexed. -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- g is a primitive root modulo q. -/
def IsPrimRoot (q : ℕ) (g : ZMod q) : Prop := IsPrimitiveRoot g (q - 1)

theorem main :
    {p : ℕ | ∃ i : ℕ, p = P i ∧
      IsPrimRoot (P (i + 1)) (P i) ∧ IsPrimRoot (P i) (P (i + 1))}.Infinite ∧
    {p : ℕ | ∃ i : ℕ, p = P i ∧
      IsPrimRoot (P (i + 1)) (P i) ∧ IsPrimRoot (P (i + 1)) (-(P i : ZMod (P (i + 1)))) ∧
      IsPrimRoot (P i) (P (i + 1)) ∧ IsPrimRoot (P i) (-(P (i + 1) : ZMod (P i)))}.Infinite := by
  sorry

end OMA.S_oeis_a243755
