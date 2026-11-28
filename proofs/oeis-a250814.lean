import OMAStatements.S_oeis_a250814
import Mathlib

namespace OMA.S_oeis_a250814

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

def Rel : (Fin 3 → Fin 3) → (Fin 3 → Fin 3) → Prop :=
  fun u v => ∀ i : Fin 2, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

instance : DecidableRel Rel := fun u v => by unfold Rel Blk; infer_instance

theorem a_eq (n : ℕ) : a n = ∑ s, V Rel n s := by
  unfold a
  have e : {x : Fin 3 → Fin (n + 1) → Fin 3 // Good n x} ≃ Chain Rel n :=
    Equiv.subtypeEquiv (Equiv.piComm _) (by
      intro x
      constructor
      · intro h j i
        exact h i j
      · intro h i j
        exact h j i)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cardChain]

def cc : ℕ → ℤ := fun j => [(-1 : ℤ), (5 : ℤ), (-10 : ℤ), (10 : ℤ), (-5 : ℤ), (1 : ℤ)].getD j 0

theorem hrec (k : ℕ) : (a (k + 5) : ℤ) = (1 : ℤ) * a (k + 0) + (-5 : ℤ) * a (k + 1) + (10 : ℤ) * a (k + 2) + (-10 : ℤ) * a (k + 3) + (5 : ℤ) * a (k + 4) := by
  have h := rec_total Rel 5 cc (by decide +kernel) k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 5 := rfl
  have e2 : cc 2 = -10 := rfl
  have e3 : cc 3 = 10 := rfl
  have e4 : cc 4 = -5 := rfl
  have e5 : cc 5 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 129 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 379 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 873 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 1731 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 3097 := by rw [a_eq]; decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (n : ℚ) ^ 4 + 10 * (n : ℚ) ^ 3 + 37 * (n : ℚ) ^ 2 + 54 * (n : ℚ) + 27 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 5
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have r : (a (k + 5) : ℚ) = (1 : ℚ) * a (k + 0) + (-5 : ℚ) * a (k + 1) + (10 : ℚ) * a (k + 2) + (-10 : ℚ) * a (k + 3) + (5 : ℚ) * a (k + 4) := by exact_mod_cast hrec k
      have i0 := ih (k + 0) (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      rw [r, i0, i1, i2, i3, i4]
      push_cast
      ring

end OMA.S_oeis_a250814

theorem OMA.solution : type_of% @OMA.S_oeis_a250814.main := by
  refine ⟨OMA.S_oeis_a250814.v1, OMA.S_oeis_a250814.v2, OMA.S_oeis_a250814.v3, OMA.S_oeis_a250814.v4, OMA.S_oeis_a250814.v5, ?_, ?_⟩
  · intro n hn
    have : ((OMA.S_oeis_a250814.a (n + 5) : ℤ) : ℚ) = (((5 : ℤ) * (OMA.S_oeis_a250814.a (n + 4) : ℤ) + (-10 : ℤ) * (OMA.S_oeis_a250814.a (n + 3) : ℤ) + (10 : ℤ) * (OMA.S_oeis_a250814.a (n + 2) : ℤ) + (-5 : ℤ) * (OMA.S_oeis_a250814.a (n + 1) : ℤ) + (1 : ℤ) * (OMA.S_oeis_a250814.a n : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [OMA.S_oeis_a250814.closed (n + 5) (by omega), OMA.S_oeis_a250814.closed (n + 4) (by omega), OMA.S_oeis_a250814.closed (n + 3) (by omega), OMA.S_oeis_a250814.closed (n + 2) (by omega), OMA.S_oeis_a250814.closed (n + 1) (by omega), OMA.S_oeis_a250814.closed n (by omega)]
      push_cast
      ring
    have h2 := (Int.cast_inj (α := ℚ)).mp this
    linarith [h2]
  · intro n hn
    have h := OMA.S_oeis_a250814.closed n hn
    have : ((1 * (OMA.S_oeis_a250814.a n : ℤ) : ℤ) : ℚ) = ((((n : ℤ) ^ 4 + 10 * (n : ℤ) ^ 3 + 37 * (n : ℤ) ^ 2 + 54 * (n : ℤ) + 27) : ℤ) : ℚ) := by
      push_cast
      rw [h]
      ring
    have h2 := (Int.cast_inj (α := ℚ)).mp this
    linarith [h2]
