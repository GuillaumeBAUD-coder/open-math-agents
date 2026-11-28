import FormalConjectures.Wikipedia.Singmaster

-- Reduction Singmaster.singmaster.R1 of Singmaster's conjecture
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch. Split the solutions (n, k) of C(n, k) = t, 1 <= k < n, by the position of k.
-- Write L(n) = exp((log n)^(3/4)).
-- * H1 (elementary): for every t > 1 the solution set is finite (1 <= k < n forces n <= C(n, k)).
-- * H2 (known theorem, not in Mathlib): solutions in the interior region L(n) <= k <= n - L(n)
--   have a uniformly bounded count. This follows from Matomaki, Radziwill, Shao, Tao and
--   Teravainen, Singmaster's conjecture in the interior of Pascal's triangle (arXiv 2106.03335,
--   Q. J. Math. 2022), which bounds the solutions with exp(log^(2/3+eps) n) <= k <= n -
--   exp(log^(2/3+eps) n) for all large t (here eps = 1/12), the finitely many small t being
--   handled by finiteness.
-- * H3 (open core): solutions near the edges (k < L(n) or n - k < L(n)) have a uniformly
--   bounded count.
-- main: the solution set is the union of the two regions; Set.ncard_union_le.

namespace OMA.R_Singmaster_singmaster_R1

/-- Every value `t > 1` has only finitely many representations `C(n, k) = t`, `1 ≤ k < n`. -/
def H1 : Prop :=
  ∀ t : ℕ, 1 < t → (Singmaster.solutions t).Finite

/-- Interior region (Matomäki–Radziwiłł–Shao–Tao–Teräväinen): bounded number of solutions with
`exp((log n)^(3/4)) ≤ k ≤ n - exp((log n)^(3/4))`. -/
def H2 : Prop :=
  ∃ C : ℕ, ∀ t : ℕ, 1 < t →
    {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧
      Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.2 : ℝ) ∧
      (p.2 : ℝ) + Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.1 : ℝ)}.ncard ≤ C

/-- Edge region (open core): bounded number of solutions with `k < exp((log n)^(3/4))` or
`n - k < exp((log n)^(3/4))`. -/
def H3 : Prop :=
  ∃ C : ℕ, ∀ t : ℕ, 1 < t →
    {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧
      ¬ (Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.2 : ℝ) ∧
      (p.2 : ℝ) + Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.1 : ℝ))}.ncard ≤ C

theorem main : H1 → H2 → H3 → type_of% @Singmaster.singmaster := by
  intro h1 h2 h3
  obtain ⟨C2, hC2⟩ := h2
  obtain ⟨C3, hC3⟩ := h3
  refine ⟨C2 + C3, fun t ht => ⟨h1 t ht, ?_⟩⟩
  set P : ℕ × ℕ → Prop := fun p =>
    Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.2 : ℝ) ∧
      (p.2 : ℝ) + Real.exp (Real.log (p.1 : ℝ) ^ ((3 : ℝ) / 4)) ≤ (p.1 : ℝ) with hP
  have hsplit : Singmaster.solutions t =
      {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧ P p} ∪
        {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧ ¬ P p} := by
    ext p
    by_cases hp : P p <;> simp [hp]
  rw [hsplit]
  calc _ ≤ {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧ P p}.ncard +
        {p : ℕ × ℕ | p ∈ Singmaster.solutions t ∧ ¬ P p}.ncard := Set.ncard_union_le _ _
    _ ≤ C2 + C3 := Nat.add_le_add (hC2 t ht) (hC3 t ht)

end OMA.R_Singmaster_singmaster_R1
