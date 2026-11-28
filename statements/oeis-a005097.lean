import Mathlib

/-!
# A005097: (Odd primes - 1)/2.

Source: https://oeis.org/A005097
Credit: @tczyzycki

The entry records two conjectures, stated here as a conjunction in the order given:

1. Horak and AlBdaiwi, Diameter Perfect Lee Codes, IEEE Trans. Inform. Theory 58 (2012),
   5490-5499 (arXiv:1109.3475), cited in the OEIS comment by Jonathan Vos Post (Sep 19 2011):
   when `2 * n + 1` is prime, there is a unique perfect 1-error-correcting Lee code of word
   length `n` over `ℤ` up to equivalence (isometries of `ℤ^n` under the Lee metric, i.e.,
   signed permutations of coordinates composed with translations). Note that the OEIS comment
   briefly paraphrases Horak-AlBdaiwi's abstract, where the actual conjecture is uniqueness
   (existence for all `n` being classical via the Golomb-Welch linear code); we formalize the
   exact conjecture from the cited source (existence and uniqueness up to Lee isometry).

2. Lear Young (May 20 2014): the set of pairwise sums of terms of A005097 is the set of
   integers greater than 1 (equivalent to Goldbach's conjecture that every even integer >= 6
   is the sum of two odd primes).
-/

namespace OMA.S_oeis_a005097

/-- Membership in A005097: numbers `k` such that `2 * k + 1` is prime
    (equivalently `(p - 1) / 2` for an odd prime `p`). -/
def InA005097 (k : ℕ) : Prop :=
  Nat.Prime (2 * k + 1)

/-- The Lee (`ℓ¹`) distance between two integer vectors of length `n`. -/
def leeDist {n : ℕ} (x y : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, (x i - y i).natAbs

/-- A perfect 1-error-correcting Lee code of word length `n` over `ℤ` (a tiling of `ℤ^n`
    by radius-1 Lee spheres / `n`-crosses): every point of `ℤ^n` lies within Lee distance `1`
    of a unique codeword. -/
def IsPerfectLeeCode {n : ℕ} (C : Set (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, ∃! c, c ∈ C ∧ leeDist x c ≤ 1

/-- Equivalence (congruence) of Lee codes over `ℤ^n` under the isometry group of `(ℤ^n, leeDist)`:
    coordinate permutations, coordinate sign flips, and translations. -/
def LeeEquiv {n : ℕ} (C₁ C₂ : Set (Fin n → ℤ)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤ) (v : Fin n → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) ∧
    (fun x : Fin n → ℤ => fun i => s i * x (σ i) + v i) '' C₁ = C₂

theorem main :
    -- Conjecture 1 (Horak-AlBdaiwi / Jonathan Vos Post): whenever 2n + 1 is prime,
    -- there is a unique perfect 1-error-correcting Lee code of word length n over ℤ
    -- up to Lee isometry.
    (∀ n : ℕ, InA005097 n →
      ∃ C : Set (Fin n → ℤ),
        IsPerfectLeeCode C ∧
        ∀ C' : Set (Fin n → ℤ), IsPerfectLeeCode C' → LeeEquiv C C') ∧
    -- Conjecture 2 (Lear Young): the set of pairwise sums of terms of A005097
    -- is the set of integers greater than 1.
    (∀ m : ℕ, 1 < m →
      ∃ x y : ℕ, InA005097 x ∧ InA005097 y ∧ x + y = m) := by
  sorry

end OMA.S_oeis_a005097
