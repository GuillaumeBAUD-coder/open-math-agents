import FormalConjectures.ErdosProblems.«298»

/-!
# Reduction of the natural-density variant of Erdős Problem 298

The literal natural-density reading of Erdős Problem 298 splits into Bloom's two
analytic steps (bounded-denominator extraction and repetition, cf. the merged reduction of
the upper-density variant in `Erdos299`) plus the elementary fact that positive natural
density implies positive upper density.
-/

namespace OMA.R_Erdos298_erdos_298_variants_natural_density_R1

open Filter

/-- Bounded-denominator extraction step of Bloom's unit fraction argument (arXiv:2112.03726),
in rational form. -/
def H1 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < A.upperDensity →
    ∃ D : Finset ℕ, (∀ d ∈ D, 0 < d) ∧ ∀ N : ℕ, ∃ d ∈ D, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, (1 / n : ℚ) = 1 / d

/-- A finite rational sum obtainable arbitrarily far out can be repeated any finite
number of times. -/
def H2 : Prop :=
  ∀ (A : Set ℕ) (w : ℕ → ℚ) (r : ℚ),
    (∃ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (↑S : Set ℕ) ⊆ A ∩ Set.Ici N ∧ ∑ n ∈ S, w n = r) →
    ∀ k : ℕ, ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ A ∧ ∑ n ∈ T, w n = k * r

/-- A set of positive natural density has positive upper density. -/
def H3 : Prop := ∀ (A : Set ℕ), A.HasPosDensity → 0 < A.upperDensity

theorem main : H1 → H2 → H3 → type_of% @Erdos298.erdos_298.variants.natural_density := by
  intro extract repeatSum hdens A hzero hpos
  obtain ⟨D, hD, h⟩ := extract A hzero (hdens A hpos)
  obtain ⟨d, hd, hfreq⟩ :=
    (frequently_exists_finset (l := (atTop : Filter ℕ)) D).mp (Eventually.of_forall h).frequently
  obtain ⟨T, hT, heq⟩ := repeatSum A (fun n => (1 / n : ℚ)) (1 / d) hfreq d
  refine ⟨T, hT, ?_⟩
  rw [heq]
  have hpos : (0 : ℚ) < d := by exact_mod_cast hD d hd
  field_simp

end OMA.R_Erdos298_erdos_298_variants_natural_density_R1
