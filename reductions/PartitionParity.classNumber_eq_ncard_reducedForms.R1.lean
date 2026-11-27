import FormalConjectures.Paper.PartitionParity

-- Reduction PartitionParity.classNumber_eq_ncard_reducedForms.R1 of Parities of partition numbers
-- Credit: @Halldon

/-!
The form–ideal correspondence identifies the class number with the number of
proper equivalence classes. Gauss reduction then gives exactly one reduced
representative per class. Both steps use the action by integral changes of
variables of determinant one.
-/

namespace OMA.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1

open Polynomial

/-- The form–ideal correspondence, for the fundamental discriminant `-D`. -/
def H1 : Prop :=
  ∀ (D : ℕ) [Fact (Irreducible (X ^ 2 + C (D : ℚ)))], Squarefree D → D % 4 = 3 →
    let Form := {f : ℤ × ℤ × ℤ // 0 < f.1 ∧ f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -(D : ℤ) ∧
      Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1}
    let evaluate (f : Form) (x y : ℤ) := f.val.1 * x ^ 2 + f.val.2.1 * x * y + f.val.2.2 * y ^ 2
    let proper (f g : Form) := ∃ u v w z : ℤ, u * z - v * w = 1 ∧
      ∀ x y : ℤ, evaluate f x y = evaluate g (u * x + v * y) (w * x + z * y)
    NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) = Nat.card (Quot proper)

/-- Gauss reduction of primitive positive-definite forms, with the stated tie convention. -/
def H2 : Prop :=
  ∀ (D : ℕ), 0 < D →
    let Form := {f : ℤ × ℤ × ℤ // 0 < f.1 ∧ f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -(D : ℤ) ∧
      Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1}
    let evaluate (f : Form) (x y : ℤ) := f.val.1 * x ^ 2 + f.val.2.1 * x * y + f.val.2.2 * y ^ 2
    let proper (f g : Form) := ∃ u v w z : ℤ, u * z - v * w = 1 ∧
      ∀ x y : ℤ, evaluate f x y = evaluate g (u * x + v * y) (w * x + z * y)
    Nonempty (Quot proper ≃ {f : ℤ × ℤ × ℤ // PartitionParity.IsReducedForm D f.1 f.2.1 f.2.2})

theorem main : H1 → H2 → type_of% @PartitionParity.classNumber_eq_ncard_reducedForms := by
  intro hClass hReduce D hSquarefree hMod
  have hPositive : 0 < D := by omega
  letI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
    ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 hPositive)⟩
  obtain ⟨e⟩ := hReduce D hPositive
  exact (hClass D hSquarefree hMod).trans (Nat.card_congr e)

end OMA.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1
