import OMAStatements.S_oeis_a250878
import Mathlib

namespace OMA.S_oeis_a250878

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

def Rel : (Fin 2 → Fin 4) → (Fin 2 → Fin 4) → Prop := fun u v => Blk (u 0) (v 0) (u 1) (v 1)

instance : DecidableRel Rel := fun u v => by unfold Rel Blk; infer_instance

theorem a_eq (n : ℕ) : a n = ∑ s, V Rel n s := by
  unfold a
  have e : {x : Fin 2 → Fin (n + 1) → Fin 4 // Good n x} ≃ Chain Rel n :=
    Equiv.subtypeEquiv (Equiv.piComm _) (by
      intro x
      constructor
      · intro h j
        exact h 0 j
      · intro h i j
        have : i = 0 := Fin.ext (by have := i.2; omega)
        subst this
        exact h j)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(-1 : ℤ), 4, -6, 4, -1].getD j 0

theorem hrec (n : ℕ) : (a (n + 4) : ℤ) = 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1) - a n := by
  have h := rec_total Rel 4 cc (by decide +kernel) n
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 4 := rfl
  have e2 : cc 2 = -6 := rfl
  have e3 : cc 3 = 4 := rfl
  have e4 : cc 4 = -1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, Nat.add_zero] at h
  simp only [a_eq]
  push_cast
  linarith

theorem a_poly (n : ℕ) : 3 * (a n : ℤ) = 34 * (n : ℤ) ^ 3 + 84 * n ^ 2 + 104 * n + 48 := by
  have key : ∀ n : ℕ, 3 * (a n : ℤ) = 34 * (n : ℤ) ^ 3 + 84 * n ^ 2 + 104 * n + 48 ∧
      3 * (a (n + 1) : ℤ) = 34 * ((n + 1 : ℕ) : ℤ) ^ 3 + 84 * ((n + 1 : ℕ) : ℤ) ^ 2 + 104 * ((n + 1 : ℕ) : ℤ) + 48 ∧
      3 * (a (n + 2) : ℤ) = 34 * ((n + 2 : ℕ) : ℤ) ^ 3 + 84 * ((n + 2 : ℕ) : ℤ) ^ 2 + 104 * ((n + 2 : ℕ) : ℤ) + 48 ∧
      3 * (a (n + 3) : ℤ) = 34 * ((n + 3 : ℕ) : ℤ) ^ 3 + 84 * ((n + 3 : ℕ) : ℤ) ^ 2 + 104 * ((n + 3 : ℕ) : ℤ) + 48 := by
    intro n
    induction n with
    | zero =>
      have h0 : a 0 = 16 := by rw [a_eq]; decide +kernel
      have h1 : a 1 = 90 := by rw [a_eq]; decide +kernel
      have h2 : a 2 = 288 := by rw [a_eq]; decide +kernel
      have h3 : a 3 = 678 := by rw [a_eq]; decide +kernel
      simp [h0, h1, h2, h3]
    | succ n ih =>
      obtain ⟨h0, h1, h2, h3⟩ := ih
      refine ⟨h1, h2, h3, ?_⟩
      have r := hrec n
      push_cast at *
      linear_combination 3 * r + 4 * h3 - 6 * h2 + 4 * h1 - h0
  exact (key n).1

end OMA.S_oeis_a250878

theorem OMA.solution : type_of% @OMA.S_oeis_a250878.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OMA.S_oeis_a250878.a_eq]; decide +kernel
  · rw [OMA.S_oeis_a250878.a_eq]; decide +kernel
  · rw [OMA.S_oeis_a250878.a_eq]; decide +kernel
  · rw [OMA.S_oeis_a250878.a_eq]; decide +kernel
  · intro n _
    exact OMA.S_oeis_a250878.hrec n
  · intro n _
    exact OMA.S_oeis_a250878.a_poly n
