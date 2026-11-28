import FormalConjectures.ErdosProblems.«985»

-- Reduction Erdos985.erdos_985.variants.two_three_five_primitive_root.R3 of Erdős Problem 985 — two three five primitive root
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 985: the three smallest primes versus all larger ones

Heath-Brown proves that at least one of `2`, `3`, `5` is a primitive root modulo infinitely many
primes `p`. This file splits that statement along the **modulus**, not along the base.

* `H1` is the region `p ∈ {2, 3, 5}`. It is the region where the disjunction is polluted by
  vanishing bases: `2 ≡ 0 (mod 2)`, `3 ≡ 0 (mod 3)`, `5 ≡ 0 (mod 5)`, so the base equal to the
  modulus has order `0`, not `p - 1`. All three small primes still qualify, but each through a
  different base: `3 ≡ 5 ≡ 1 (mod 2)` has order `1 = 2 - 1`, `2 ≡ -1 (mod 3)` has order
  `2 = 3 - 1`, and `2` has order `4 = 5 - 1` modulo `5`. This is an elementary finite check,
  decidable in three cases.
* `H2` is the region `p > 5`. There `2`, `3`, `5` are three *distinct non-zero* residues, i.e.
  three distinct units of `(ZMod p)ˣ`, and the question is genuinely about their orders. This is
  the core region.

The axis is different from the two merged reductions of this parent, which split by *which base*
occurs infinitely often (`….R1`, a three-way disjunction) and by *proof architecture*
(`….R2`: Heath-Brown's sieve input versus the elementary three-generator counting lemma). The
value of the modulus split is that in `H2` no base degenerates, so any step that divides by `p`,
by `p - 1 = |(ZMod p)ˣ|`, or that needs `2`, `3`, `5` to be distinct units applies without the
finitely many exceptional primes `p ≤ 5` that pollute the disjunction; conversely `H2` follows from
each single-base hypothesis of `….R1` (delete the primes `≤ 5` from one infinite set), hence also
from `….R2`. So this is a further reduction of the same target, not a competing one.

Source: <https://www.erdosproblems.com/985>; D. R. Heath-Brown, *Artin's conjecture for primitive
roots*, Quart. J. Math. Oxford 37 (1986), 27–38.
-/

namespace OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R3

/-- The three smallest primes, each through a base that does not vanish. -/
def H1 : Prop :=
  (2 : ℕ).Prime ∧
    (orderOf (2 : ZMod 2) = 2 - 1 ∨ orderOf (3 : ZMod 2) = 2 - 1 ∨
      orderOf (5 : ZMod 2) = 2 - 1) ∧
  (3 : ℕ).Prime ∧
    (orderOf (2 : ZMod 3) = 3 - 1 ∨ orderOf (3 : ZMod 3) = 3 - 1 ∨
      orderOf (5 : ZMod 3) = 3 - 1) ∧
  (5 : ℕ).Prime ∧
    (orderOf (2 : ZMod 5) = 5 - 1 ∨ orderOf (3 : ZMod 5) = 5 - 1 ∨
      orderOf (5 : ZMod 5) = 5 - 1)

/-- Every prime above `5`, where `2`, `3`, `5` are three distinct units: the core region. -/
def H2 : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧
    (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
      orderOf (5 : ZMod p) = p - 1) ∧ 5 < p}

theorem main : H1 → H2 → type_of% @Erdos985.erdos_985.variants.two_three_five_primitive_root := by
  intro h1 hcore
  obtain ⟨h2p, h2o, h3p, h3o, h5p, h5o⟩ := h1
  have hcore' : Set.Infinite {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
        orderOf (5 : ZMod p) = p - 1) ∧ 5 < p} := hcore
  have hsub : {p : ℕ | p.Prime ∧
        (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
          orderOf (5 : ZMod p) = p - 1) ∧ 5 < p} ⊆
      {2, 3, 5} ∪ ({p : ℕ | p.Prime ∧
        (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
          orderOf (5 : ZMod p) = p - 1)} \ {2, 3, 5}) := by
    rintro p ⟨hpp, ho, hp5⟩
    refine Or.inr ⟨⟨hpp, ho⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hInf := hcore'.mono hsub
  have hEq : ({2, 3, 5} : Set ℕ) ∪ ({p : ℕ | p.Prime ∧
        (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
          orderOf (5 : ZMod p) = p - 1)} \ {2, 3, 5}) =
      {p : ℕ | p.Prime ∧
        (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
          orderOf (5 : ZMod p) = p - 1)} := by
    ext p
    constructor
    · rintro (hp | ⟨hp, -⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨h2p, h2o⟩
        · exact ⟨h3p, h3o⟩
        · exact ⟨h5p, h5o⟩
      · exact hp
    · intro hp
      by_cases h : p ∈ ({2, 3, 5} : Set ℕ)
      · exact Or.inl h
      · exact Or.inr ⟨hp, h⟩
  rw [hEq] at hInf
  exact hInf

end OMA.R_Erdos985_erdos_985_variants_two_three_five_primitive_root_R3
