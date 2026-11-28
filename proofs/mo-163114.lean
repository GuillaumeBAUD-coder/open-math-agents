import OMAStatements.S_mo_163114

-- Problem mo-163114: the statement claims that in every BCL algebra (A, op, z) the relation
-- x <= y :<-> op x y = z is reflexive, antisymmetric and transitive.
-- Upstream: statements/mo-163114.lean (declaration OMA.S_mo_163114.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: transitivity fails. On the three-element set {0, 1, 2} with z = 0 take the operation
--   op 0 . = (0, 0, 1),   op 1 . = (1, 0, 0),   op 2 . = (1, 2, 0).
-- The three BCL axioms hold (checked over all 3, 9 and 27 cases), and op 0 1 = 0, op 1 2 = 0, but op 0 2 = 1.
-- The model was found by exhaustive search over all three-element operations.

open OMA.S_mo_163114

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_163114.main) := by
  intro h
  have hb : IsBCL (fun x y : Fin 3 =>
      (![![0, 0, 1], ![1, 0, 0], ![1, 2, 0]] : Fin 3 → Fin 3 → Fin 3) x y) 0 := by
    unfold IsBCL
    decide
  have ht := (h (Fin 3) _ 0 hb).2.2 0 1 2 (by decide) (by decide)
  revert ht
  decide
