import OMAStatements.S_mse_4804070
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases

/-!
A five-node metric counterexample to the amended special-node conjecture.
The base counterexample appears in the November 2023 Reddit discussion linked
from MSE4804070; adding 20 to each off-diagonal entry makes it metric without
changing edge orderings or relative Hamiltonian-cycle costs. The identity
tour has length 141, and every tour with a special vertex has length > 141.
The finite enumeration is checked by ordinary kernel reduction, with a proof
that every genuine permutation occurs in the list being checked.
-/

namespace TspCertificate

def weight : Fin 5 → Fin 5 → ℕ :=
  ![![0, 28, 26, 23, 32],
    ![28, 0, 33, 30, 40],
    ![26, 33, 0, 21, 31],
    ![23, 30, 21, 0, 27],
    ![32, 40, 31, 27, 0]]

def rawLength (p : Fin 5 → Fin 5) : ℕ :=
  ∑ i : Fin 5, weight (p i) (p (finRotate 5 i))

def rawSpecial (p : Fin 5 → Fin 5) (i : Fin 5) : Prop :=
  ∀ w : Fin 5, w ≠ p i →
    w ≠ p ((finRotate 5).symm i) → w ≠ p (finRotate 5 i) →
    weight (p i) (p ((finRotate 5).symm i)) ≤ weight (p i) w ∧
    weight (p i) (p (finRotate 5 i)) ≤ weight (p i) w

instance (p : Fin 5 → Fin 5) (i : Fin 5) : Decidable (rawSpecial p i) := by
  unfold rawSpecial
  infer_instance

def listFn (l : List (Fin 5)) (i : Fin 5) : Fin 5 := l[i.val]!

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem list_certificate : ∀ l ∈ (List.finRange 5).permutations',
    ∀ i : Fin 5, rawSpecial (listFn l) i → 141 < rawLength (listFn l) := by
  decide

theorem ofFn_mem (p : Equiv.Perm (Fin 5)) :
    List.ofFn p ∈ (List.finRange 5).permutations' := by
  rw [List.mem_permutations', List.ofFn_eq_map]
  exact p.map_finRange_perm

theorem listFn_ofFn (p : Fin 5 → Fin 5) : listFn (List.ofFn p) = p := by
  funext i
  fin_cases i <;> rfl

theorem raw_special_length_gt (p : Equiv.Perm (Fin 5)) (i : Fin 5)
    (h : rawSpecial p i) : 141 < rawLength p := by
  have h' := list_certificate (List.ofFn p) (ofFn_mem p) i
  simp only [listFn_ofFn] at h'
  exact h' h

def natLength (p : Equiv.Perm (Fin 5)) : ℕ := rawLength p

def natIsSpecial (p : Equiv.Perm (Fin 5)) (i : Fin 5) : Prop := rawSpecial p i

theorem special_length_gt (p : Equiv.Perm (Fin 5)) (i : Fin 5)
    (h : natIsSpecial p i) : 141 < natLength p := raw_special_length_gt p i h

def cheapTour : Equiv.Perm (Fin 5) := Equiv.refl _

theorem cheapTour_length : natLength cheapTour = 141 := by decide

theorem weight_diag : ∀ i, weight i i = 0 := by decide

theorem weight_symm : ∀ i j, weight i j = weight j i := by decide

theorem weight_positive : ∀ i j, i ≠ j → 0 < weight i j := by decide

theorem weight_triangle : ∀ i j k, weight i k ≤ weight i j + weight j k := by decide

theorem weight_distinct : ∀ i j k l : Fin 5,
    i < j → k < l → weight i j = weight k l → i = k ∧ j = l := by decide

theorem weight_distinct_unordered : ∀ i j k l : Fin 5,
    i ≠ j → k ≠ l → weight i j = weight k l →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

end TspCertificate

namespace OMA.S_mse_4804070

theorem tourLength_cast {n : ℕ} (w : Fin n → Fin n → ℕ)
    (p : Equiv.Perm (Fin n)) :
    tourLength (fun i j => (w i j : ℝ)) p =
      ((∑ i : Fin n, w (p i) (p (finRotate n i))) : ℕ) := by
  simp only [tourLength, Nat.cast_sum]

theorem isSpecial_cast {n : ℕ} (w : Fin n → Fin n → ℕ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    IsSpecial (fun i j => (w i j : ℝ)) p i ↔
      ∀ v : Fin n, v ≠ p i →
        v ≠ p ((finRotate n).symm i) → v ≠ p (finRotate n i) →
        w (p i) (p ((finRotate n).symm i)) ≤ w (p i) v ∧
        w (p i) (p (finRotate n i)) ≤ w (p i) v := by
  simp only [IsSpecial, Nat.cast_le]

end OMA.S_mse_4804070

open OMA.S_mse_4804070 TspCertificate in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4804070.main) := by
  intro h
  obtain ⟨p, hp, i, hi⟩ := h 5 (by decide) (fun i j => (weight i j : ℝ))
    (by intro i; simp only [weight_diag, Nat.cast_zero])
    (by intro i j; exact congrArg (fun x : ℕ => (x : ℝ)) (weight_symm i j))
    (by intro i j; exact Nat.cast_nonneg _)
    (by
      intro i j k l hij hkl heq
      apply weight_distinct_unordered i j k l hij hkl
      simpa only [Nat.cast_inj] using heq)
  have hbound := hp cheapTour
  rw [tourLength_cast, tourLength_cast] at hbound
  have hnat : natLength p ≤ natLength cheapTour := by
    simpa only [Nat.cast_le, natLength, rawLength] using hbound
  rw [cheapTour_length] at hnat
  exact (Nat.not_lt_of_ge hnat)
    (special_length_gt p i ((isSpecial_cast weight p i).mp hi))
