import FormalConjectures.Paper.PartitionParity

namespace OMA.R_PartitionParity_ono_swaminathan_quadratic_R1

open Nat PartitionParity

-- Section 4.1 of Ono and Swaminathan: an odd value.
def H1 : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ m : ℕ, m.Coprime 6 ∧ Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

-- Section 4.2: an even value.
def H2 : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ m : ℕ, m.Coprime 6 ∧ Even (partitionNumber ((D * m ^ 2 + 1) / 24))

-- The infinitude implications of Theorem 8, without its first-occurrence bounds.
def H3 : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∀ P : ℕ → Prop, (P = Even ∨ P = Odd) →
      (∃ m : ℕ, m.Coprime 6 ∧ P (partitionNumber ((D * m ^ 2 + 1) / 24))) →
      {m : ℕ | m.Coprime 6 ∧ P (partitionNumber ((D * m ^ 2 + 1) / 24))}.Infinite

theorem main : H1 → H2 → H3 → type_of% @PartitionParity.ono_swaminathan.quadratic := by
  intro oddWitness evenWitness propagate D hD hsq h23
  constructor
  · exact propagate D hD hsq h23 Even (Or.inl rfl) (evenWitness D hD hsq h23)
  · exact propagate D hD hsq h23 Odd (Or.inr rfl) (oddWitness D hD hsq h23)

end OMA.R_PartitionParity_ono_swaminathan_quadratic_R1
