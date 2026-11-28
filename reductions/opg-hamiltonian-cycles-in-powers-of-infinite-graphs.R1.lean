import OMAStatements.S_opg_hamiltonian_cycles_in_powers_of_infinite_graphs

-- Reduction opg-hamiltonian-cycles-in-powers-of-infinite-graphs.R1 of opg-hamiltonian-cycles-in-powers-of-infinite-graphs: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_opg_hamiltonian_cycles_in_powers_of_infinite_graphs_R1

open OMA.S_opg_hamiltonian_cycles_in_powers_of_infinite_graphs

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (V : Type) [Countable V] [LinearOrder V] (G : SimpleGraph V),
      Nonempty (Fin 3 ↪ V) → (G.Connected → HasHamiltonCircle (graphPower G 3))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (V : Type) [Countable V] [LinearOrder V] (G : SimpleGraph V),
      Nonempty (Fin 3 ↪ V) → (IsTwoConnected G → HasHamiltonCircle (graphPower G 2))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_opg_hamiltonian_cycles_in_powers_of_infinite_graphs.main := by
  intro h1 h2 x1 x2 x3 x4 x5
  exact ⟨h1 x1 x4 x5, h2 x1 x4 x5⟩

end OMA.R_opg_hamiltonian_cycles_in_powers_of_infinite_graphs_R1
