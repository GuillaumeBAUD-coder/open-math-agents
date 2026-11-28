import FormalConjectures.ErdosProblems.«1178»

-- Reduction Erdos1178.erdos_1178.R1 of Erdős Problem 1178
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: the target d_r(e) = (r-2)e+3 says that the infimum of the vertex counts v with
-- f_r(n, v, e) = o(n^2) (f_r = configurationExtremalNumber: no v vertices carry e edges)
-- is exactly (r-2)e+3. We split it into
--   H1: the lower bound, for all r, e ≥ 3: f_r(n, v, e) is not o(n^2) when v ≤ (r-2)e+2
--       (Brown-Erdős-Sós 1973 construction, together with monotonicity in v; known),
--   H2: the upper bound for e = 3: f_r(n, 3r-3, 3) = o(n^2) for all r ≥ 3
--       (Ruzsa-Szemerédi 1978 for r = 3, Erdős-Frankl-Rödl 1986 for all r; known),
--   H3: the upper bound for e ≥ 4: the Brown-Erdős-Sós conjecture (open).
-- main: le_antisymm on the infimum. No computer search was used.

namespace OMA.R_Erdos1178_erdos_1178_R1

open Filter Asymptotics

/-- Lower bound (Brown-Erdős-Sós 1973): below (r-2)e+3 vertices the extremal number is not
`o(n^2)`. -/
def H1 : Prop :=
  ∀ r e : ℕ, 3 ≤ r → 3 ≤ e → ∀ v : ℕ, v ≤ (r - 2) * e + 2 →
    ¬ (fun n ↦ (Hypergraph.configurationExtremalNumber n r v e : ℝ))
      =o[atTop] (fun n ↦ (n : ℝ) ^ 2)

/-- Upper bound for e = 3, i.e. 3r-3 vertices (Ruzsa-Szemerédi, Erdős-Frankl-Rödl). -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    (fun n ↦ (Hypergraph.configurationExtremalNumber n r ((r - 2) * 3 + 3) 3 : ℝ))
      =o[atTop] (fun n ↦ (n : ℝ) ^ 2)

/-- Upper bound for e ≥ 4 (the open Brown-Erdős-Sós conjecture). -/
def H3 : Prop :=
  ∀ r e : ℕ, 3 ≤ r → 4 ≤ e →
    (fun n ↦ (Hypergraph.configurationExtremalNumber n r ((r - 2) * e + 3) e : ℝ))
      =o[atTop] (fun n ↦ (n : ℝ) ^ 2)

theorem main : H1 → H2 → H3 → type_of% @Erdos1178.erdos_1178 := by
  intro h1 h2 h3 r e hr he
  unfold Hypergraph.sparseConfigurationThreshold
  apply le_antisymm
  · have hv : (fun n ↦ (Hypergraph.configurationExtremalNumber n r ((r - 2) * e + 3) e : ℝ))
        =o[atTop] (fun n ↦ (n : ℝ) ^ 2) := by
      rcases (by omega : e = 3 ∨ 4 ≤ e) with rfl | h
      · exact h2 r hr
      · exact h3 r e hr h
    exact iInf₂_le (f := fun (v : ℕ) (_ : (fun n ↦ (Hypergraph.configurationExtremalNumber n r v e : ℝ))
      =o[atTop] (fun n ↦ (n : ℝ) ^ 2)) => (v : ℕ∞)) ((r - 2) * e + 3) hv
  · refine le_iInf₂ fun v hv => ?_
    have hlt : (r - 2) * e + 2 < v := by
      by_contra hc
      exact h1 r e hr he v (by omega) hv
    exact_mod_cast (by omega : (r - 2) * e + 3 ≤ v)

end OMA.R_Erdos1178_erdos_1178_R1
