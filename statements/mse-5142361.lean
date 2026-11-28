import Mathlib

/-!
# Finitely many primes `p` with some `k ∈ [1, p]`, `ord_p(k) = q`, `k^(p-1) ≡ 1 (mod p²)`?

Source: https://math.stackexchange.com/questions/5142361
(it continues https://mathoverflow.net/questions/512630, "Conjecture A" with `n = 1`)

The source states the conjecture: "For a fixed prime `q` and sufficiently large primes `p`, there
exists no `k ∈ [1, p]` such that `ord_p(k) = q` and `k^(p-1) ≡ 1 (mod p²)`." The title asks
whether only finitely many such primes `p` exist.

Reading choices (for the reviewer):
* "For all sufficiently large `p` there is no such `k`" is stated in the title's equivalent form:
  for each prime `q`, the set of primes `p` having such a `k` is finite.
* `ord_p(k)` is Mathlib's `orderOf ((k : ℕ) : ZMod p)`. The source's side condition `q ∣ p - 1`
  follows from `ord_p(k) = q` and is not repeated. `k = p` never qualifies, because its order
  is `orderOf 0 = 0`.
* `k^(p-1) ≡ 1 (mod p²)` is `Nat.ModEq (p ^ 2) (k ^ (p - 1)) 1`.
* The source's Conjecture A (the equality `v_p(∏_{k=1}^p Φ_q(k)) = q - 1`) is equivalent by the
  reduction on the page. Only the reduced form is stated here.
* Status: open. The source gives computations (none for `q = 3` up to `10^11`; for `q = 11`, the
  exceptions `p = 400263469` and `p = 9544876463` up to `10^12`). In the comments, Greg Martin
  suspects that there are infinitely many, so the conjecture may be false.

Numeric sanity checks: the `example`s below show that `p = 11, k = 3` is an exception for
`q = 5` (`3^5 = 243 ≡ 1 mod 11` and `3^10 = 59049 ≡ 1 mod 121`). Outside the file, Python
confirmed both of the source's `q = 11` witnesses: `k^11 ≡ 1 (mod p)` with `k ≢ 1`, and
`k^(p-1) ≡ 1 (mod p²)`. A search over primes `p < 3000` found exceptions only for `q = 5`:
`(p, k) = (11, 3), (11, 9), (131, 58)`. There were none for `q = 2, 3, 7`, which matches the
source's `q = 3` report.
-/

namespace OMA.S_mse_5142361

/-- `p` is an exception for `q`: some `k ∈ [1, p]` has order `q` mod `p` and
`k^(p-1) ≡ 1 (mod p²)`. -/
def Exception (q p : ℕ) : Prop :=
  ∃ k ∈ Finset.Icc 1 p, orderOf ((k : ℕ) : ZMod p) = q ∧ Nat.ModEq (p ^ 2) (k ^ (p - 1)) 1

example : orderOf ((3 : ℕ) : ZMod 11) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

example : Nat.ModEq (11 ^ 2) (3 ^ (11 - 1)) 1 := by decide

example : Exception 5 11 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨3, by decide, orderOf_eq_prime (by decide) (by decide), by decide⟩

theorem main :
    ∀ q : ℕ, q.Prime → {p : ℕ | p.Prime ∧ Exception q p}.Finite := by
  sorry

end OMA.S_mse_5142361
