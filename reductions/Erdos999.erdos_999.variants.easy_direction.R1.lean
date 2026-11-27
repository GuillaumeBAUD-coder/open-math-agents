import FormalConjectures.ErdosProblems.«999»

-- Credit: @steveDOTdigital
namespace OMA.R_Erdos999_erdos_999_variants_easy_direction_R1

open MeasureTheory

-- Count the intervals centered at reduced fractions that meet the unit interval.
def H1 : Prop :=
  ∀ (f : ℕ → ℝ), (∀ q, 0 ≤ f q) → ∀ q : ℕ,
    (volume.restrict (Set.Icc (0 : ℝ) 1))
      {x : ℝ | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q} ≤
      ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q))

-- First Borel–Cantelli for a sequence on the unit interval, stated with a real majorant.
def H2 : Prop :=
  ∀ (s : ℕ → Set ℝ) (g : ℕ → ℝ), Summable g →
    (∀ q, (volume.restrict (Set.Icc (0 : ℝ) 1)) (s q) ≤ ENNReal.ofReal (g q)) →
    ¬ (∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1), {q : ℕ | x ∈ s q}.Infinite)

theorem main : H1 → H2 → type_of% @Erdos999.erdos_999.variants.easy_direction := by
  intro hcount hBC f hf happ hsum
  let s (q : ℕ) : Set ℝ :=
    {x | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}
  apply hBC s (fun q => 6 * ((Nat.totient q : ℝ) * f q / q))
    (hsum.mul_left 6) (hcount f hf)
  exact ae_restrict_of_ae happ

end OMA.R_Erdos999_erdos_999_variants_easy_direction_R1
