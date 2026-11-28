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

open OMA.S_mo_349784

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_349784.main) := by
  intro h
  have hinj : Function.Injective (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) := by decide
  have hne : ∀ i, ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) i).Nonempty := by decide
  have hpd := h (Fin 2) 3 (fun _ => (1 : ℝ)) (fun _ => one_pos) ![{0}, {1}, {0, 1}] hinj hne
  have hdet := hpd.det_pos
  have hval : ∀ i j : Fin 3,
      gram (fun _ : Fin 2 => (1 : ℝ)) (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) i j =
        ((((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) i ∩
          (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) j).card : ℕ) : ℝ) := by
    intro i j
    simp [gram]
  have e00 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0).card = 1 := by decide
  have e01 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1).card = 0 := by decide
  have e02 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2).card = 1 := by decide
  have e10 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0).card = 0 := by decide
  have e11 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1).card = 1 := by decide
  have e12 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2).card = 1 := by decide
  have e20 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 0).card = 1 := by decide
  have e21 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 1).card = 1 := by decide
  have e22 : ((![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2 ∩ (![{0}, {1}, {0, 1}] : Fin 3 → Finset (Fin 2)) 2).card = 2 := by decide
  rw [Matrix.det_fin_three] at hdet
  simp only [hval, e00, e01, e02, e10, e11, e12, e20, e21, e22] at hdet
  norm_num at hdet
