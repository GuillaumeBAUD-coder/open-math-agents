import OMAStatements.S_mo_349784
import Mathlib

-- Problem mo-349784: the statement claims that for distinct nonempty subsets X_1, ..., X_n of a finite set and
-- positive weights f, the matrix with entries f(X_i meet X_j) (the total weight of the intersection) is positive
-- definite.
-- Upstream: statements/mo-349784.lean (declaration OMA.S_mo_349784.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take the two-point set {0, 1} with weights 1 and the three sets {0}, {1}, {0, 1}. The matrix is
-- (1 0 1; 0 1 1; 1 1 2), whose third row is the sum of the first two, so its determinant is 0, while a positive
-- definite matrix has positive determinant.

-- Evaluate the intersection Gram determinant directly; the original counterexample is unchanged.
open OMA.S_mo_349784

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_349784.main) := by
  intro h
  have hinj : Function.Injective (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) := by decide
  have hne : ∀ i, ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) i).Nonempty := by decide
  have hpd := h (Fin 2) 3 (fun _ => (1 : ℝ)) (fun _ => one_pos) ![{0}, {1}, {0, 1}] hinj hne
  have hdet := hpd.det_pos
  norm_num [Matrix.det_fin_three, gram, Matrix.cons_val_two] at hdet
