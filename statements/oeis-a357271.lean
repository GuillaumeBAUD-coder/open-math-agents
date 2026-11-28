import Mathlib

/-!
# OEIS A357271: maximum number of stable matchings in the stable marriage problem

Source: https://oeis.org/A357271 (lower bounds from Appendix C of Thurber, 2002).
In the stable marriage problem of order `n` (Gale and Shapley), `n` men and `n` women each rank
all members of the other side strictly. A matching is stable when no man and woman both prefer
each other to their assigned partners. A357271 lists the best known lower bounds, obtained by
composing smaller instances, for the maximum number of stable matchings of an instance of
order `n`: 1, 2, 3, 10, 16, 48, 71, 268, 330, 1000, 1231, 6472, ..., a(16) = 195472.

The bounds are known to be exact for `n ≤ 5`. The OEIS entry records the conjecture that
a(6), a(8), a(10), a(12) and a(16) are also exact. That conjecture is stated here.

Encoding: `I.1 m w` is the rank that man `m` gives woman `w`, `I.2 w m` is the rank that woman
`w` gives man `m`; a smaller rank means more preferred. Strict complete rankings are exactly
permutations of `Fin n`. A matching is a permutation `μ`, man `m` being matched to woman `μ m`.

-- Credit: @Alegonca (agent: Claude Code)
-/

namespace OMA.S_oeis_a357271

/-- An instance of the stable marriage problem of order `n`: the men's and the women's
rankings, each a permutation of `Fin n` (smaller rank = more preferred). -/
abbrev Instance (n : ℕ) : Type :=
  (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))

/-- `μ` is stable for `I`: there is no blocking pair, i.e. no man `m` and woman `w` such that
`m` strictly prefers `w` to his partner `μ m` and `w` strictly prefers `m` to her partner. -/
def IsStable {n : ℕ} (I : Instance n) (μ : Equiv.Perm (Fin n)) : Prop :=
  ∀ m w : Fin n, ¬ (I.1 m w < I.1 m (μ m) ∧ I.2 w m < I.2 w (μ.symm w))

/-- The number of stable matchings of the instance `I`. -/
noncomputable def numStable {n : ℕ} (I : Instance n) : ℕ :=
  Nat.card {μ : Equiv.Perm (Fin n) // IsStable I μ}

/-- `IsMaxStable n k`: the maximum number of stable matchings over all instances of order `n`
is exactly `k`. -/
def IsMaxStable (n k : ℕ) : Prop :=
  IsGreatest (Set.range fun I : Instance n => numStable I) k

theorem main :
    IsMaxStable 6 48 ∧ IsMaxStable 8 268 ∧ IsMaxStable 10 1000 ∧ IsMaxStable 12 6472 ∧
      IsMaxStable 16 195472 := by
  sorry

end OMA.S_oeis_a357271
