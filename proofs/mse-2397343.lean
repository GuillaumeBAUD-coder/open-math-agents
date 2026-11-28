import OMAStatements.S_mse_2397343
import Mathlib

-- Problem: mse-2397343, is a 2-in-3-SAT instance satisfiable exactly when the linear system
-- (each clause sums to 2 modulo 3) is solvable?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Variables s, t, p, q, w, x, y, a = 0, ..., 7 with the clauses
--   {s,t,p}, {s,t,q}, {p,q,w}, {p,q,x}, {p,q,y}, {x,y,a}.
-- Boolean: the first two clauses give p = q, the third then forces p = q = 1, the next two
-- force x = y = 0, and the last clause would need a = 2. Linear over Z/3: s = 1, t = 0,
-- p = q = 1, w = x = y = 0, a = 2 is a solution.

namespace MSE2397343

def clauses : Finset (Finset (Fin 8)) :=
  {{0, 1, 2}, {0, 1, 3}, {2, 3, 4}, {2, 3, 5}, {2, 3, 6}, {5, 6, 7}}

theorem card3 : ∀ c ∈ clauses, c.card = 3 := by
  decide +kernel

theorem linear : ∃ v : Fin 8 → ZMod 3, ∀ c ∈ clauses, ∑ i ∈ c, v i = 2 :=
  ⟨![1, 0, 1, 1, 0, 0, 0, 2], by decide +kernel⟩

theorem not_boolean : ¬ ∃ v : Fin 8 → Fin 2, ∀ c ∈ clauses, ∑ i ∈ c, (v i).val = 2 := by
  decide +kernel

end MSE2397343

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2397343.main) := by
  intro h
  exact MSE2397343.not_boolean
    ((h 8 MSE2397343.clauses MSE2397343.card3).mpr MSE2397343.linear)
