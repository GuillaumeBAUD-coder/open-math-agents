import OMAStatements.S_mo_267651
import Mathlib

/-!
# MathOverflow 267651: prime pairs with finitely many primes in the progression

The set in question is empty.  Two distinct primes `p ≠ q` are coprime, so by Dirichlet's
theorem there are arbitrarily large primes `r ≡ p (mod q)`; every such `r ≥ p` has the form
`p + k * q`.  Hence the set of primes of that form is never finite, and the set of pairs for
which it is finite is the empty set — in particular it is finite.
-/

theorem OMA.solution : type_of% @OMA.S_mo_267651.main := by
  refine Set.Finite.subset Set.finite_empty ?_
  rintro ⟨p, q⟩ ⟨hp, hq, hne, hfin⟩
  exfalso
  simp only at hp hq hne hfin
  have : NeZero q := ⟨hq.ne_zero⟩
  -- `p` is a unit modulo `q`
  have hunit : IsUnit ((p : ℕ) : ZMod q) :=
    (ZMod.isUnit_iff_coprime p q).mpr ((Nat.coprime_primes hp hq).mpr hne)
  -- a bound for the (supposedly finite) set of primes `p + k * q`
  obtain ⟨B, hB⟩ := hfin.bddAbove
  -- Dirichlet: a prime `r > max B p` with `r ≡ p (mod q)`
  obtain ⟨r, hr, hrp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max B p)
  have hrB : B < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hpr : p ≤ r := (lt_of_le_of_lt (le_max_right _ _) hr).le
  have hcong : p ≡ r [MOD q] := ((ZMod.natCast_eq_natCast_iff r p q).mp hmod).symm
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hpr).mp hcong
  have hmem : r ∈ {r : ℕ | Nat.Prime r ∧ ∃ k : ℕ, r = p + k * q} :=
    ⟨hrp, k, by rw [mul_comm]; omega⟩
  exact absurd (hB hmem) (not_le.mpr hrB)
