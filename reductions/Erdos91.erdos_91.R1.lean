import FormalConjectures.ErdosProblems.«91»

/-!
# Erdos 91: two optimal families separated by a similarity invariant

The target `Erdos91.erdos_91` asks that for all large `n` there are two non-similar `n`-point sets
minimising the number of distinct distances.  The two expected extremal families for this problem
are patches of the triangular lattice (which contain many equilateral triangles, i.e. triples of
points whose three mutual distances are equal) and patches of the square lattice (which contain no
equilateral triangle at all, a classical irrationality fact).

This reduction splits the target into the two existence statements for those families.  The glue is
a genuine geometric fact: the presence of an equilateral triple is invariant under a dilation
equivalence, because such an equivalence multiplies every distance by one fixed positive ratio.
Hence two optimal sets, one with and one without an equilateral triple, can never be similar, and
`UniqueMinimizer n` fails for every such `n`.
-/

open EuclideanGeometry Erdos91 Filter

namespace OMA.R_Erdos91_erdos_91_R1

/-- Triangular-lattice type: for all large `n` some optimal `n`-point set contains an equilateral
triple (three pairwise distinct points whose three mutual distances are equal). -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℝ², IsOptimal A n ∧
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ dist a b = dist b c ∧ dist b c = dist c a

/-- Square-lattice type: for all large `n` some optimal `n`-point set contains no equilateral
triple. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ B : Finset ℝ², IsOptimal B n ∧
    ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B,
      a ≠ b → b ≠ c → a ≠ c → ¬(dist a b = dist b c ∧ dist b c = dist c a)

/-- A dilation equivalence multiplies all distances by the same positive ratio, so it carries an
equilateral triple to an equilateral triple. -/
lemma equilateralTriple_of_similar {A B : Finset ℝ²} (h : DilationEquivSimilar A B)
    (hA : ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ dist a b = dist b c ∧ dist b c = dist c a) :
    ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ dist a b = dist b c ∧ dist b c = dist c a := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, h1, h2⟩ := hA
  have hmem : ∀ x ∈ A, f x ∈ B := by
    intro x hx
    have hx' : f x ∈ f '' (A : Set ℝ²) := ⟨x, by simpa using hx, rfl⟩
    rw [hf] at hx'
    simpa using hx'
  refine ⟨f a, hmem a ha, f b, hmem b hb, f c, hmem c hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hab (f.injective h)
  · exact fun h => hbc (f.injective h)
  · exact fun h => hac (f.injective h)
  · rw [Dilation.dist_eq, Dilation.dist_eq, h1]
  · rw [Dilation.dist_eq, Dilation.dist_eq, h2]

/-- Two optimal families of different lattice type force two non-similar optimal sets. -/
theorem main : H1 → H2 → type_of% @Erdos91.erdos_91 := by
  intro h1 h2
  filter_upwards [h1, h2] with n hn1 hn2
  obtain ⟨A, hA, htri⟩ := hn1
  obtain ⟨B, hB, hno⟩ := hn2
  intro huniq
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, e1, e2⟩ :=
    equilateralTriple_of_similar (huniq A B hA hB) htri
  exact hno a ha b hb c hc hab hbc hac ⟨e1, e2⟩

end OMA.R_Erdos91_erdos_91_R1
