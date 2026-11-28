import OMAStatements.S_mo_198378

-- Reduction mo-198378.R1 of mo-198378: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_mo_198378_R1

open OMA.S_mo_198378
open Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ (m n t : ℕ) (P : Fin n → Finset (Fin m)) (ε K : ℝ), 0<ε → 0<K →
      (∀ j, K ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ (2*n+1)^t ∧
        ∀ r p, source r p → missed p P S ε ≤ (2:ℝ)^r *
          (((2*n+1:ℕ):ℝ)*Real.exp (-2*ε^2*K))^(t+1))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ (m n s : ℕ) (P : Fin n → Finset (Fin m)), 0<s → 20000 ≤ Real.log n →
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ s ∧
        ∀ r p, source r p → missed p P S (1/100) ≤ (2:ℝ)^r/s)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ (m n r : ℕ) (P : Fin n → Finset (Fin m)), 20000 ≤ Real.log n →
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ 100*2^r ∧
        ∀ p, source r p → missed p P S (1/100) ≤ 1/100)

/-- Step H4 of the reduction. -/
def H4 : Prop := (∃ C : ℕ, ∀ (m n r : ℕ) (P : Fin n → Finset (Fin m)),
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ C*2^r ∧
        ∀ p, source r p → missed p P S (1/100) ≤ 1/100)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_198378.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_mo_198378_R1
