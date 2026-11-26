import FormalConjectures.Paper.StrongSensitivityConjecture

-- Problem: Strong Sensitivity Conjecture (`bs(f) ≤ s(f)^2`) — nisanExample sensitivity
-- Upstream: formal-conjectures FormalConjectures/Paper/StrongSensitivityConjecture.lean:136 (declaration StrongSensitivityConjecture.nisanExample_sensitivity)
-- Credit: @niclorusso (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.NisanSensitivity

open Finset StrongSensitivityConjecture

/-- The accepting condition of `nisanExample n`, on the Hamming weight `w`. -/
def AccW (n w : ℕ) : Prop := 2 * w = n ∨ 2 * w = n + 2

instance (n w : ℕ) : Decidable (AccW n w) := by unfold AccW; infer_instance

/-- Flipping one bit changes the Hamming weight by one. -/
lemma weight_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    #{j | StrongSensitivityConjecture.flip x {i} j} = if x i then #{j | x j} - 1 else #{j | x j} + 1 := by
  by_cases hi : x i
  · have h : ({j | StrongSensitivityConjecture.flip x {i} j} : Finset (Fin n)) = ({j | x j} : Finset (Fin n)).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [StrongSensitivityConjecture.flip, hi]
      · simp [StrongSensitivityConjecture.flip, hj]
    rw [h, card_erase_of_mem (by simp [hi]), if_pos hi]
  · have h : ({j | StrongSensitivityConjecture.flip x {i} j} : Finset (Fin n)) = insert i ({j | x j} : Finset (Fin n)) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [StrongSensitivityConjecture.flip, hi]
      · simp [StrongSensitivityConjecture.flip, hj]
    rw [h, card_insert_of_notMem (by simp [hi]), if_neg hi]

/-- `nisanExample n` accepts exactly the inputs whose weight satisfies `AccW n`. -/
lemma nisan_iff {n : ℕ} (x : Fin n → Bool) :
    nisanExample n x = true ↔ AccW n #{j | x j} := by
  simp only [nisanExample, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, AccW]
  have e1 : ((#{j | x j} : ℕ) : ℚ) = (n : ℚ) / 2 ↔ 2 * #{j | x j} = n := by
    constructor
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = n := by push_cast; linarith
      exact_mod_cast h2
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = n := by exact_mod_cast h
      push_cast at h2; linarith
  have e2 : ((#{j | x j} : ℕ) : ℚ) = (n : ℚ) / 2 + 1 ↔ 2 * #{j | x j} = n + 2 := by
    constructor
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = ((n + 2 : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h2
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = ((n + 2 : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at h2; linarith
  rw [e1, e2]

/-- The local sensitivity of `nisanExample n` only depends on the weight `w` of the input:
flipping a one-bit moves to weight `w - 1`, flipping a zero-bit moves to weight `w + 1`. -/
lemma sens_formula (n : ℕ) (x : Fin n → Bool) :
    sensitivityAt (nisanExample n) x =
      (if (AccW n (#{j | x j} - 1) ↔ AccW n #{j | x j}) then 0 else #{j | x j}) +
      (if (AccW n (#{j | x j} + 1) ↔ AccW n #{j | x j}) then 0 else n - #{j | x j}) := by
  have key : ∀ i, (nisanExample n (StrongSensitivityConjecture.flip x {i}) ≠ nisanExample n x) ↔
      (x i = true ∧ ¬(AccW n (#{j | x j} - 1) ↔ AccW n #{j | x j})) ∨
      (x i = false ∧ ¬(AccW n (#{j | x j} + 1) ↔ AccW n #{j | x j})) := by
    intro i
    rw [Ne, Bool.eq_iff_iff, nisan_iff, nisan_iff, weight_flip]
    cases x i <;> simp
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun j => x j = true)
  simp only [card_univ, Fintype.card_fin, Bool.not_eq_true] at hsplit
  unfold sensitivityAt
  simp_rw [key]
  by_cases hA : (AccW n (#{j | x j} - 1) ↔ AccW n #{j | x j}) <;>
    by_cases hC : (AccW n (#{j | x j} + 1) ↔ AccW n #{j | x j}) <;>
    simp [hA, hC] <;>
    omega

lemma sens_le (m : ℕ) (x : Fin (4 * m) → Bool) :
    sensitivityAt (nisanExample (4 * m)) x ≤ 2 * m + 2 := by
  rw [sens_formula]
  have hw : #{j | x j} ≤ 4 * m := by
    simpa using card_filter_le (univ : Finset (Fin (4 * m))) (fun j => x j = true)
  generalize #{j | x j} = w at hw ⊢
  by_cases hA : (AccW (4 * m) (w - 1) ↔ AccW (4 * m) w) <;>
    by_cases hC : (AccW (4 * m) (w + 1) ↔ AccW (4 * m) w) <;>
    (try rw [if_pos hA]) <;> (try rw [if_neg hA]) <;>
    (try rw [if_pos hC]) <;> (try rw [if_neg hC]) <;>
    simp only [AccW] at hA hC <;>
    omega

end OMA.NisanSensitivity

open Finset StrongSensitivityConjecture OMA.NisanSensitivity in
theorem OMA.solution : type_of% @StrongSensitivityConjecture.nisanExample_sensitivity := by
  intro n hn hn_pos
  obtain ⟨m, rfl⟩ := hn
  have hm : 1 ≤ m := by omega
  have hdiv : 4 * m / 2 + 2 = 2 * m + 2 := by omega
  rw [hdiv]
  apply le_antisymm
  · exact Finset.sup_le fun x _ => sens_le m x
  · obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (4 * m))))
      (n := 2 * m + 2) (by simp; omega)
    let x : Fin (4 * m) → Bool := fun i => decide (i ∈ S)
    have hx : #{j | x j} = 2 * m + 2 := by
      simp [x, hS]
    calc 2 * m + 2 = sensitivityAt (nisanExample (4 * m)) x := by
          have hA : ¬(AccW (4 * m) (2 * m + 2 - 1) ↔ AccW (4 * m) (2 * m + 2)) := by
            simp only [AccW]; omega
          have hC : (AccW (4 * m) (2 * m + 2 + 1) ↔ AccW (4 * m) (2 * m + 2)) := by
            simp only [AccW]; omega
          rw [sens_formula, hx, if_neg hA, if_pos hC]
      _ ≤ sensitivity (nisanExample (4 * m)) := Finset.le_sup (mem_univ x)
