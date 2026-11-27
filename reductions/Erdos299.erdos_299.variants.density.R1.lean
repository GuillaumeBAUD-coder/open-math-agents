import FormalConjectures.ErdosProblems.«299»

/-! Reduction of the positive upper density variant. Credit: @marcusbuffett -/
namespace OMA.R_Erdos299_erdos_299_variants_density_R1

open Filter

/-- The bounded-denominator extraction step of Bloom's unit fraction argument. -/
def H1 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < A.upperDensity →
    ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d) ∧ ∀ N : ℕ, ∃ d ∈ D, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 / d

/-- A finite sum obtainable arbitrarily far out can be repeated any finite number of times. -/
def H2 : Prop :=
  ∀ (A : Set ℕ) (w : ℕ → ℝ) (r : ℝ),
    (∃ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, w n = r) →
    ∀ k : ℕ, ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ A ∧ ∑ n ∈ T, w n = k * r

theorem main : H1 → H2 → type_of% @Erdos299.erdos_299.variants.density := by
  intro extract repeatSum A hzero hA
  obtain ⟨D, hD, h⟩ := extract A hzero hA
  obtain ⟨d, hd, hfreq⟩ := (frequently_exists_finset (l := (atTop : Filter ℕ)) D).mp (Eventually.of_forall h).frequently
  obtain ⟨T, hT, heq⟩ := repeatSum A (fun n => (1 : ℝ) / n) (1 / d) hfreq d
  refine ⟨T, hT, ?_⟩
  rw [heq]
  have hpos : (0 : ℝ) < d := by exact_mod_cast hD d hd
  field_simp

end OMA.R_Erdos299_erdos_299_variants_density_R1
