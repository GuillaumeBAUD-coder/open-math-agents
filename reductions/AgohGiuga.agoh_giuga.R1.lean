import FormalConjectures.Wikipedia.AgohGiuga

-- Reduction AgohGiuga.agoh_giuga.R1 of Agoh-Giuga conjecture — agoh giuga
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
# Agoh's form of the Agoh-Giuga conjecture: Kellner's bridge + no strong Giuga number

Agoh's congruence `n B_{n-1} ≡ -1 (mod n)` is a statement about Bernoulli numbers;
Giuga's congruence `∑_{i=1}^{n-1} i^{n-1} ≡ -1 (mod n)` is elementary. Kellner
(B. C. Kellner, *The equivalence of Giuga's and Agoh's conjectures*, 2004) proved the two
congruences are equivalent for each `n ≥ 2`, via von Staudt-Clausen and Faulhaber's
formula. This separates the Bernoulli-number content from the arithmetic core.

* `H1` (known, Kellner 2004): for each `n ≥ 2`, Agoh's congruence holds iff Giuga's does.
* `H2` (open core, Giuga's conjecture): there is no strong Giuga number, i.e. no composite
  `n` with `n ∣ 1 + ∑_{i=1}^{n-1} i^{n-1}`. This core is itself split further in the
  reduction `AgohGiuga.agoh_giuga.variants.giuga.R1` (Carmichael + Giuga conditions).

`main` proves the prime direction by Fermat's little theorem and assembles the rest.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_R1

open AgohGiuga

/-- Kellner (2004): Agoh's Bernoulli congruence and Giuga's power-sum congruence agree for
every `n ≥ 2`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ((∃ k : ℤ, let B := bernoulli' (n - 1); n * B.num + B.den = k * n ^ 2) ↔
      n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ))

/-- Giuga's conjecture in its Giuga-number form: no strong Giuga number exists. -/
def H2 : Prop :=
  ∀ n : ℕ, ¬ IsStrongGiuga n

-- Fermat's little theorem gives Giuga's congruence at primes (same argument as in the
-- reduction AgohGiuga.agoh_giuga.variants.giuga.R1).
lemma prime_dvd_sum_pow (p : ℕ) (hp : p.Prime) :
    p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1 : ℕ) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hsum : ∑ i ∈ Finset.Ioo 0 p, ((i ^ (p - 1 : ℕ) : ℕ) : ZMod p) =
      ∑ _i ∈ Finset.Ioo 0 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow]
    rw [Finset.mem_Ioo] at hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hi.1 h) (not_le_of_gt hi.2)
    exact ZMod.pow_card_sub_one_eq_one hi0
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioo, Nat.sub_zero]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hp.one_le, ZMod.natCast_self]

theorem main : H1 → H2 → type_of% @AgohGiuga.agoh_giuga := by
  intro h1 h2
  change AgohGiugaCongr
  intro p hp2
  refine Iff.trans ?_ (h1 p hp2).symm
  constructor
  · exact prime_dvd_sum_pow p
  · intro hdvd
    by_contra hnp
    have hcomp : p.Composite := by
      dsimp [Nat.Composite]
      exact ⟨by omega, hnp⟩
    exact h2 p ⟨hcomp, hdvd⟩

end OMA.R_AgohGiuga_agoh_giuga_R1
