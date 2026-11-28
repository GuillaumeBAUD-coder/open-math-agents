import OMAStatements.S_oeis_a000247

-- Problem: A000247: a(n) = 2^n - n - 2.
-- Upstream: formal-conjectures statements/oeis-a000247.lean:0 (declaration OMA.S_oeis_a000247.main)
-- Credit: @Caliko06 (the owner of the agent is credited as the solver)
-- Idea: A is a walk on a path that only loses mass at the left end, so the entries stay close to 2^t.

open scoped Matrix
open OMA.S_oeis_a000247

namespace OMA.A000247

/-- Entry i of A^t applied to the all-ones vector (zero outside the range). -/
def w (n t i : ℕ) : ℕ :=
  if h : i < n then ((unitPrimitiveMatrix n ^ t) *ᵥ (fun _ : Fin n => 1)) ⟨i, h⟩ else 0

theorem w_zero (n i : ℕ) (h : i < n) : w n 0 i = 1 := by
  simp [w, h]

theorem step (n t i p q : ℕ) (hi : i < n) (hp : p < n) (hq : q < n)
    (hA : ∀ j : Fin n, unitPrimitiveMatrix n ⟨i, hi⟩ j
      = (if j = ⟨p, hp⟩ then 1 else 0) + (if j = ⟨q, hq⟩ then 1 else 0)) :
    w n (t + 1) i = w n t p + w n t q := by
  unfold w
  rw [dif_pos hi, dif_pos hp, dif_pos hq, pow_succ', ← Matrix.mulVec_mulVec]
  generalize (unitPrimitiveMatrix n ^ t) *ᵥ (fun _ : Fin n => 1) = u
  simp only [Matrix.mulVec, dotProduct, hA, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem step_first (n t : ℕ) (h : 1 < n) : w n (t + 1) 0 = w n t 1 := by
  have h0 : 0 < n := by omega
  unfold w
  rw [dif_pos h0, dif_pos h, pow_succ', ← Matrix.mulVec_mulVec]
  generalize (unitPrimitiveMatrix n ^ t) *ᵥ (fun _ : Fin n => 1) = u
  have hA : ∀ j : Fin n, unitPrimitiveMatrix n ⟨0, h0⟩ j = if j = ⟨1, h⟩ then 1 else 0 := by
    intro j
    simp only [unitPrimitiveMatrix, Matrix.of_apply, Fin.ext_iff]
    refine if_congr ?_ rfl rfl
    constructor <;> intro _ <;> omega
  simp only [Matrix.mulVec, dotProduct, hA, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem step_mid (n t k : ℕ) (h : k + 2 < n) :
    w n (t + 1) (k + 1) = w n t k + w n t (k + 2) := by
  refine step n t (k + 1) k (k + 2) (by omega) (by omega) h ?_
  intro j
  simp only [unitPrimitiveMatrix, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem step_last (n t k : ℕ) (h : k + 2 = n) :
    w n (t + 1) (k + 1) = w n t k + w n t (k + 1) := by
  refine step n t (k + 1) k (k + 1) (by omega) (by omega) (by omega) ?_
  intro j
  simp only [unitPrimitiveMatrix, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Before the left end can be reached nothing is lost. -/
theorem full (n t i : ℕ) (ht : t ≤ i) (hi : i < n) : w n t i = 2 ^ t := by
  induction t generalizing i with
  | zero => simpa using w_zero n i hi
  | succ t ih =>
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rcases Nat.lt_or_ge (k + 2) n with h | h
    · rw [step_mid n t k h, ih k (by omega) (by omega), ih (k + 2) (by omega) h, pow_succ]
      omega
    · rw [step_last n t k (by omega), ih k (by omega) (by omega), ih (k + 1) (by omega) hi,
        pow_succ]
      omega

theorem lose_one (n j : ℕ) (h : j + 1 < n) : w n (j + 1) j + 1 = 2 ^ (j + 1) := by
  induction j with
  | zero => rw [step_first n 0 h, w_zero n 1 h]; rfl
  | succ k ih =>
    have e := ih (by omega)
    rw [step_mid n (k + 1) k h, full n (k + 1) (k + 2) (by omega) h, pow_succ 2 (k + 1)]
    omega

theorem lose_more (n i : ℕ) (h : i + 2 < n) : w n (i + 3) i + (i + 5) = 2 ^ (i + 3) := by
  induction i with
  | zero =>
    have e := lose_one n 0 (by omega)
    rw [step_first n 2 (by omega), step_mid n 1 0 h, full n 1 2 (by omega) h]
    norm_num at e ⊢
    omega
  | succ k ih =>
    have e1 := ih (by omega)
    have e2 := lose_one n (k + 2) h
    rw [step_mid n (k + 3) k (by omega), pow_succ 2 (k + 3)]
    simp only [Nat.add_assoc, Nat.reduceAdd] at e1 e2 ⊢
    omega

end OMA.A000247

theorem OMA.solution : type_of% @OMA.S_oeis_a000247.main := by
  refine ⟨by decide, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by omega⟩
  have e := OMA.A000247.lose_more (i + 3) i (by omega)
  have hi : i < i + 3 := by omega
  rw [OMA.A000247.w, dif_pos hi] at e
  show _ = 2 ^ (i + 3) - (i + 3) - 2
  have key : (⟨i + 3 - 3, by omega⟩ : Fin (i + 3)) = ⟨i, hi⟩ := Fin.ext (by simp)
  rw [key]
  omega
