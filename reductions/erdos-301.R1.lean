import OMAStatements.S_erdos_301

-- Reduction erdos-301.R1 of Erdős Problem 301
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: `f N / N → 1/2` splits into the two one-sided bounds.
-- H1 is the known lower bound `f N ≥ N/2`, witnessed by the block `A = (N/2, N]`
-- (for distinct `b, b'` in it, `1/b + 1/b' ≥ 2/N > 1/a`, and `k ≤ 1` never works);
-- it is elementary and will be proved as a separate step.
-- H2 is the open upper bound `f N ≤ (1/2 + ε) N` for large `N`
-- (best known is van Doorn's `(25/28 + o(1)) N`, see erdosproblems.com/301).
-- `main` combines them with `tendsto_order`.

namespace OMA.R_erdos_301_R1

open Filter Topology

/-- The known lower bound: `f N ≥ N / 2` for every `N`. -/
def H1 : Prop := ∀ N : ℕ, N ≤ 2 * OMA.S_erdos_301.f N

/-- The open upper bound: for every `ε > 0`, eventually `f N ≤ (1/2 + ε) N`. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ N : ℕ in atTop, (OMA.S_erdos_301.f N : ℝ) ≤ (1 / 2 + ε) * N

theorem main : H1 → H2 → type_of% @OMA.S_erdos_301.main := by
  intro h1 h2
  show Tendsto (fun N : ℕ => (OMA.S_erdos_301.f N : ℝ) / N) atTop (𝓝 (1 / 2))
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h := h1 N
    have h' : (N : ℝ) ≤ 2 * (OMA.S_erdos_301.f N : ℝ) := by exact_mod_cast h
    rw [lt_div_iff₀ hN']
    nlinarith
  · have hε : 0 < (b - 1 / 2) / 2 := by linarith
    filter_upwards [h2 _ hε, eventually_ge_atTop 1] with N hf hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN']
    nlinarith
end OMA.R_erdos_301_R1
