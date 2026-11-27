import FormalConjectures.ErdosProblems.«687»

/-!
# A two-band sieve reduction of the Maier–Pomerance bound

This reduction has been withdrawn. The upper-band hypothesis H2 is false.
For a small fixed positive theta, prescribe zero at the primes between
x^theta and the square root of x and at the upper-band primes. Suitable
choices below x^theta make the upper band hit more than half of the
small-prime survivors. The implication below remains valid.

The initial sieve uses primes up to the square root of the prime cutoff.
The primes above that cutoff are split at the integer part of `x^(3/4)`.
Each hypothesis bounds the fraction of the initial survivors hit in one band,
uniformly in the initial residue classes and in the classes for that band.
A cover of the interval would have to hit every survivor in one of the bands.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2

open Asymptotics Filter Finset

private theorem survivors_card_le_band_cards_of_cover {x y z w : ℕ} {a : ℕ → ℕ}
    (ha : ∀ m ∈ Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]) :
    let survivors := (Icc 1 y).filter fun m =>
      ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
    let hits := fun p => survivors.filter fun m => m ≡ a p [MOD p]
    survivors.card ≤ (((Ioc z w).filter Nat.Prime).biUnion hits).card +
      (((Ioc w x).filter Nat.Prime).biUnion hits).card := by
  let survivors := (Icc 1 y).filter fun m =>
    ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
  let hits := fun p => survivors.filter fun m => m ≡ a p [MOD p]
  let lower := ((Ioc z w).filter Nat.Prime).biUnion hits
  let upper := ((Ioc w x).filter Nat.Prime).biUnion hits
  change survivors.card ≤ lower.card + upper.card
  have hsubset : survivors ⊆ lower ∪ upper := by
    intro m hm
    obtain ⟨hmInterval, hmAvoid⟩ := mem_filter.mp hm
    obtain ⟨p, hpUpper, hpPrime, hmCongruent⟩ := ha m hmInterval
    have hpLower : z < p := lt_of_not_ge fun hpLe => hmAvoid p hpLe hpPrime hmCongruent
    have hmHits : m ∈ hits p := mem_filter.mpr ⟨hm, hmCongruent⟩
    apply mem_union.mpr
    by_cases hp : p ≤ w
    · exact Or.inl (mem_biUnion.mpr
        ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpLower, hp⟩, hpPrime⟩, hmHits⟩)
    · exact Or.inr (mem_biUnion.mpr
        ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge hp, hpUpper⟩, hpPrime⟩, hmHits⟩)
  exact (card_le_card hsubset).trans (card_union_le lower upper)

private theorem Y_le_of_not_coverable_succ {x y : ℕ}
    (h : ¬ Green46.IsCoveredByResidues x (y + 1)) : Erdos687.Y x ≤ y := by
  rw [Erdos687.Y]
  refine csSup_le ⟨0, ⟨fun _ => 0, by simp⟩⟩ ?_
  rintro k ⟨a, ha⟩
  by_contra hk
  have hle : y + 1 ≤ k := by omega
  exact h ⟨a, fun m hm => ha m <| mem_Icc.mpr
    ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hle⟩⟩

/-- The classes assigned to primes in the lower band hit fewer than half
of the positions surviving the initial sieve. A position hit by several
primes contributes once to the cardinality of the union. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop, ∀ a b : ℕ → ℕ,
      let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
      let w := (x ^ 3).sqrt.sqrt
      let survivors := (Icc 1 y).filter fun m =>
        ∀ p ≤ x.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])
      2 * (((Ioc x.sqrt w).filter Nat.Prime).biUnion fun p =>
        survivors.filter fun m => m ≡ b p [MOD p]).card < survivors.card

/-- The classes assigned to primes in the upper band hit fewer than half
of the positions surviving the same initial sieve. The assignment `b`
is arbitrary and independent of the classes `a` used in the initial sieve. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop, ∀ a b : ℕ → ℕ,
      let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
      let w := (x ^ 3).sqrt.sqrt
      let survivors := (Icc 1 y).filter fun m =>
        ∀ p ≤ x.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])
      2 * (((Ioc w x).filter Nat.Prime).biUnion fun p =>
        survivors.filter fun m => m ≡ b p [MOD p]).card < survivors.card

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.maier_pomerance := by
  intro hLower hUpper ε hε
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [hLower ε hε, hUpper ε hε] with x hLowerX hUpperX
  let scale : ℝ := (x : ℝ) * Real.log x ^ (2 + ε)
  have hscale : 0 ≤ scale :=
    mul_nonneg (Nat.cast_nonneg x) (Real.rpow_nonneg (Real.log_natCast_nonneg x) _)
  have hY : Erdos687.Y x ≤ ⌊scale⌋₊ := by
    apply Y_le_of_not_coverable_succ
    rintro ⟨a, ha⟩
    have hCovered := survivors_card_le_band_cards_of_cover (z := x.sqrt)
      (w := (x ^ 3).sqrt.sqrt) ha
    have hLowerBound := hLowerX a a
    have hUpperBound := hUpperX a a
    dsimp only [scale] at hCovered hLowerBound hUpperBound
    omega
  have hYReal : (Erdos687.Y x : ℝ) ≤ scale :=
    (Nat.cast_le.mpr hY).trans (Nat.floor_le hscale)
  change ‖(Erdos687.Y x : ℝ)‖ ≤ 1 * ‖scale‖
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hscale, one_mul]

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2
