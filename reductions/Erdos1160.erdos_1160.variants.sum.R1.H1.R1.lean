import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1

open Filter CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1

/-- Abelian groups at all smaller orders use at most half the available count of smaller 2-groups. -/
def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    2 * (∑ n ∈ Finset.Ico 1 (2 ^ m),
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ ∀ a b : G, a * b = b * a}).ncard)
      ≤ ∑ k ∈ Finset.range m, g (2 ^ k)

/-- It remains enough to bound the nonabelian contribution by three halves of that count. -/
def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop,
    2 * ((∑ n ∈ Finset.Ico 1 (2 ^ m), g n) -
      (∑ n ∈ Finset.Ico 1 (2 ^ m),
        (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
          {G : FiniteGrp.{0} | Nat.card G = n ∧ ∀ a b : G, a * b = b * a}).ncard))
      ≤ 3 * (∑ k ∈ Finset.range m, g (2 ^ k))

lemma add_contributions (a s p : ℕ) (ha : 2 * a ≤ p) (hn : 2 * (s - a) ≤ 3 * p) :
    s ≤ 2 * p := by omega

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1.H1 := by
  intro abelian nonabelian
  unfold H1 at abelian
  unfold H2 at nonabelian
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1.H1
  filter_upwards [abelian, nonabelian] with m ha hn
  exact add_contributions _ _ _ ha hn

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1
