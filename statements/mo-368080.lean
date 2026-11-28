import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

namespace OMA.S_mo_368080

/-- Integer points in the real half-open interval `(a,b]`. -/
noncomputable def interval (a b : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊a⌋ ⌊b⌋

noncomputable def count (S : Set ℤ) (m : ℕ) (r : ℤ) (a b : ℝ) : ℕ := by
  classical
  exact ((interval a b).filter fun x => x ∈ S ∧ (m : ℤ) ∣ x-r).card

/-- The class of functions `g` in the question. -/
def Admissible (g : ℕ → ℝ) : Prop :=
  g 1 = 1 ∧
    (∀ m n : ℕ, m.Coprime n → g (m*n) = g m * g n) ∧
    ∃ κ : ℝ, ∀ (p k : ℕ), p.Prime → 0 < k →
      g (p^k) = (p : ℝ)^k * (1 - κ/(p : ℝ))

def WellDistributed (S : Set ℤ) : Prop :=
  ∃ g : ℕ → ℝ, Admissible g ∧ ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 0 < m → ∀ r : ℤ,
      (∃ B : ℕ, ∀ a b : ℝ, 1 ≤ b-a → count S m r a b ≤ B) ∨
      (∀ a b : ℝ, 1 ≤ b-a →
        |(count S m r a b : ℝ) - (b-a)/g m| ≤ C*(b-a)^ε)

def SparseComplement (S : Set ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ b-a →
    (count Sᶜ 1 0 a b : ℝ) ≤ C*(b-a)^ε

def powersOfTwo : Set ℤ :=
  {x | ∃ j : ℕ, x = (2 : ℤ)^j}

/-- The sets in the question are precisely finite sets and sets with
uniformly subpolynomial complement counts. The complement of the
positive powers of two gives a co-infinite example. -/
theorem main :
    (∀ S : Set ℤ, WellDistributed S ↔ S.Finite ∨ SparseComplement S) ∧
      WellDistributed powersOfTwoᶜ := by
  sorry

end OMA.S_mo_368080
