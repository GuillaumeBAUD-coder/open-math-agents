import OMAReductions.R_Erdos667_erdos_667_variants_ramsey_bounds_R1

/-! # A finite Ramsey graph criterion and its parameters -/
-- Credit: @steveDOTdigital
namespace OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1
open Erdos667 Filter

-- B is the reciprocal probability of a red edge. The first estimate controls red p-cliques
-- touching any given edge. The second makes blue m-cliques sufficiently rare.
def H1 : Prop := ∀ p n B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) →
  ∃ G : SimpleGraph (Fin n), LocallyDense p 1 G ∧ G.CliqueFree (m+1)

-- A strict exponent gap permits integer powers for n, B and m.
def H2 : Prop := ∀ p : ℕ, 3 ≤ p → ∀ b : ℝ, 2/((p : ℝ)+1) < b →
  ∃ᶠ n : ℕ in atTop, ∃ B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) ∧ (m : ℝ) ≤ (n : ℝ)^b

theorem main : H1 → H2 → OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1.H2 := by
  intro graph parameters p hp b hb
  apply (parameters p hp b hb).mono
  rintro n ⟨B,m,fit,cap⟩
  obtain ⟨G,dense,free⟩ := graph p n B m fit
  exact ⟨m,G,cap,dense,free⟩

end OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1
