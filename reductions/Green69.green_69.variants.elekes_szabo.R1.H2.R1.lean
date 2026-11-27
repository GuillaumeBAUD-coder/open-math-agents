import OMAReductions.R_Green69_green_69_variants_elekes_szabo_R1

-- Reduction Green69.green_69.variants.elekes_szabo.R1.H2.R1 of step Green69.green_69.variants.elekes_szabo.R1.H2
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

/-!
The step is the Elekes–Szabó conjecture for point sets in general position. This file splits
it by the density c of triple lines, at c = 4/25. A set of n points with no four collinear has
at most n (n - 1) / 6 triple lines, so only 0 < c < 1/6 matters.

H1 is the dense range: n points, no four collinear, at least 4 n^2 / 25 triple lines. It is
true, by the following argument, which needs Euler's formula for line arrangements and so is
left as a step. Pass to the dual arrangement of n lines in the real projective plane, with t2
double points and t3 triple points, t2 + 3 t3 = n (n - 1) / 2. Euler's formula gives
1 + t2 + 2 t3 faces and shows that the sum over the faces of (number of sides - 3) is t2 - 3
(this is the proof of Melchior's inequality). Call a triple point good if its six faces are
triangles and its six neighbours along its three lines are triple points. A triple point on a
face with at least four sides is not good, and there are at most 4 (t2 - 3) of these; one next
to a double point is not good, and there are at most 4 t2 of these. So if t3 >= 8 t2, that is
if 25 t3 >= 4 n (n - 1), there is a good triple point. Its six neighbours and the nine lines
through them are, back in the plane, nine points and six triple lines forming a three by
three grid. The grid lies on two different cubics (three rows, three columns), so with any
tenth point it lies on a cubic of the pencil. This is the local step of Green and Tao, On
sets defining few ordinary lines, used there when t2 = O(n).

H2 is the range 0 < c < 4/25 of the step, unchanged otherwise. It is open. Below this
density no local argument is known: three by three grids are not forced in abstract linear
triple systems of positive density (Gishboliner and Shapira), and Solymosi's theorem that
they are forced for mutually avoiding sets (arXiv:2206.00889) uses an ordering that general
sets do not have.

The split loses nothing: the step implies H2, and H1 is a theorem.
-/

namespace OMA.R_Green69_green_69_variants_elekes_szabo_R1_H2_R1

open scoped Finset
open Green69

-- Dense range: at least 4 n^2 / 25 triple lines and no four collinear points.
def H1 : Prop :=
  ∃ n₀ : ℕ, ∀ A : Finset (ℝ × ℝ), n₀ < #A → AtMostOnLine 3 A →
    4 / 25 * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard → ∃ S ⊆ A, #S = 10 ∧ OnCubic S

-- The general position case for densities below 4/25.
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → c < 4 / 25 → ∃ d : ℕ, ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ, ∃ n₀ : ℕ,
    ∀ A : Finset (ℝ × ℝ), n₀ < #A →
    AtMostOnLine 3 A →
    (∀ T ⊆ A, #T = 7 → ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ 2 →
      ∃ a ∈ T, MvPolynomial.eval ![a.1, a.2] F ≠ 0) →
    (∀ T ⊆ A, #T = 9 → ∀ F G : MvPolynomial (Fin 2) ℝ, F.totalDegree ≤ 3 → G.totalDegree ≤ 3 →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] F = 0) →
      (∀ a ∈ T, MvPolynomial.eval ![a.1, a.2] G = 0) →
      ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • F + b • G = 0) →
    (∀ B ⊆ A, m ≤ #B →
      (∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        ∀ a ∈ B, MvPolynomial.eval ![a.1, a.2] F = 0) →
      ((tripleLines B).ncard : ℝ) < c' * (#B : ℝ) ^ 2) →
    c * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard →
    (∀ p ∈ A, c * (#A : ℝ) ≤
      ({L ∈ tripleLines A | p ∈ L} : Set (AffineSubspace ℝ (ℝ × ℝ))).ncard) →
    ∃ S ⊆ A, #S = 10 ∧ OnCubic S

theorem main : H1 → H2 → OMA.R_Green69_green_69_variants_elekes_szabo_R1.H2 := by
  intro k1 k2 c hc
  by_cases hcc : c < 4 / 25
  · exact k2 c hc hcc
  · push Not at hcc
    obtain ⟨n₀, h⟩ := k1
    refine ⟨0, 1, one_pos, fun m => ⟨n₀, fun A hA hL _ _ _ hden _ => h A hA hL ?_⟩⟩
    have h1 : (4 / 25 : ℝ) * (#A : ℝ) ^ 2 ≤ c * (#A : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcc (sq_nonneg _)
    exact h1.trans hden

end OMA.R_Green69_green_69_variants_elekes_szabo_R1_H2_R1
