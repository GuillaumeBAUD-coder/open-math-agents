import OMAStatements.S_oeis_a126475
import Mathlib

namespace A126475Aux

lemma card_cons (n : ℕ) (P : (Fin (n + 1) → Fin 7) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ d : Fin 7, (Finset.univ.filter (fun x : Fin n → Fin 7 => P (Fin.cons d x))).card := by
  simp only [Finset.card_filter]
  exact ((Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 7))
    (fun p => if P (Fin.cons p.1 p.2) then 1 else 0) (fun w => if P w then 1 else 0)
    (fun p => rfl)).symm).trans (Fintype.sum_prod_type _)

lemma valid_cons (m : ℕ) (d : Fin 7) (x : Fin (m + 1) → Fin 7) :
    (∀ i j : Fin (m + 2), (j : ℕ) = (i : ℕ) + 1 →
        OMA.S_oeis_a126475.close ((Fin.cons d x : Fin (m + 2) → Fin 7) i) ((Fin.cons d x : Fin (m + 2) → Fin 7) j))
      ↔ OMA.S_oeis_a126475.close d (x 0) ∧ ∀ i j : Fin (m + 1), (j : ℕ) = (i : ℕ) + 1 → OMA.S_oeis_a126475.close (x i) (x j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h01 := h 0 (Fin.succ 0) (by rw [Fin.val_succ, Fin.val_zero, Fin.val_zero])
      rw [Fin.cons_zero, Fin.cons_succ] at h01
      exact h01
    · intro i j hij
      have h2 := h i.succ j.succ (by rw [Fin.val_succ, Fin.val_succ, hij])
      rw [Fin.cons_succ, Fin.cons_succ] at h2
      exact h2
  · rintro ⟨h0, h1⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero =>
        exfalso
        rw [Fin.val_zero] at hij
        omega
      | succ j =>
        rw [Fin.cons_zero, Fin.cons_succ]
        have hj : j = 0 := by
          apply Fin.ext
          rw [Fin.val_succ, Fin.val_zero] at hij
          rw [Fin.val_zero]
          omega
        rw [hj]
        exact h0
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        exfalso
        rw [Fin.val_succ, Fin.val_zero] at hij
        omega
      | succ j =>
        rw [Fin.cons_succ, Fin.cons_succ]
        apply h1
        rw [Fin.val_succ, Fin.val_succ] at hij
        omega

def H (n : ℕ) (d : Fin 7) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 7 =>
    ∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 →
      OMA.S_oeis_a126475.close ((Fin.cons d x : Fin (n + 1) → Fin 7) i) ((Fin.cons d x : Fin (n + 1) → Fin 7) j))).card

lemma a_succ (n : ℕ) : OMA.S_oeis_a126475.a (n + 1) = ∑ d : Fin 7, H n d := by
  unfold OMA.S_oeis_a126475.a H
  exact card_cons n _

lemma H_succ (n : ℕ) (d : Fin 7) :
    H (n + 1) d = ∑ e : Fin 7, if OMA.S_oeis_a126475.close d e then H n e else 0 := by
  have h1 : H (n + 1) d = ∑ e : Fin 7, (Finset.univ.filter (fun y : Fin n → Fin 7 =>
      ∀ i j : Fin (n + 1 + 1), (j : ℕ) = (i : ℕ) + 1 →
        OMA.S_oeis_a126475.close ((Fin.cons d (Fin.cons e y : Fin (n + 1) → Fin 7) : Fin (n + 1 + 1) → Fin 7) i)
          ((Fin.cons d (Fin.cons e y : Fin (n + 1) → Fin 7) : Fin (n + 1 + 1) → Fin 7) j))).card := by
    unfold H
    exact card_cons n _
  rw [h1]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hde : OMA.S_oeis_a126475.close d e
  · rw [if_pos hde]
    unfold H
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro y _
    exact (valid_cons n d (Fin.cons e y)).trans
      ⟨fun h => h.2, fun h => ⟨by rw [Fin.cons_zero]; exact hde, h⟩⟩
  · rw [if_neg hde, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ h
    have h' := (valid_cons n d (Fin.cons e y)).mp h
    rw [Fin.cons_zero] at h'
    exact hde h'.1

lemma H_zero (d : Fin 7) : H 0 d = 1 := by
  unfold H
  rw [Finset.filter_true_of_mem]
  · simp
  · intro x _ i j hij
    exfalso
    have hi := i.isLt
    have hj := j.isLt
    omega

lemma a_zero : OMA.S_oeis_a126475.a 0 = 1 := by
  unfold OMA.S_oeis_a126475.a
  rw [Finset.filter_true_of_mem]
  · simp
  · intro x _ i
    exact i.elim0

lemma hs_0 (m : ℕ) : H (m + 1) 0 = H m 0 + H m 1 + H m 2 + H m 3 + 0 + 0 + 0 := by
  have c0 : OMA.S_oeis_a126475.close (0 : Fin 7) (0 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : OMA.S_oeis_a126475.close (0 : Fin 7) (1 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (0 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (0 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : ¬ (OMA.S_oeis_a126475.close (0 : Fin 7) (4 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : ¬ (OMA.S_oeis_a126475.close (0 : Fin 7) (5 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : ¬ (OMA.S_oeis_a126475.close (0 : Fin 7) (6 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_neg c4, if_neg c5, if_neg c6]

lemma hs_1 (m : ℕ) : H (m + 1) 1 = H m 0 + H m 1 + H m 2 + H m 3 + H m 4 + 0 + 0 := by
  have c0 : OMA.S_oeis_a126475.close (1 : Fin 7) (0 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : OMA.S_oeis_a126475.close (1 : Fin 7) (1 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (1 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (1 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (1 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : ¬ (OMA.S_oeis_a126475.close (1 : Fin 7) (5 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : ¬ (OMA.S_oeis_a126475.close (1 : Fin 7) (6 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_neg c5, if_neg c6]

lemma hs_2 (m : ℕ) : H (m + 1) 2 = H m 0 + H m 1 + H m 2 + H m 3 + H m 4 + H m 5 + 0 := by
  have c0 : OMA.S_oeis_a126475.close (2 : Fin 7) (0 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : OMA.S_oeis_a126475.close (2 : Fin 7) (1 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (2 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (2 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (2 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : OMA.S_oeis_a126475.close (2 : Fin 7) (5 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : ¬ (OMA.S_oeis_a126475.close (2 : Fin 7) (6 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_neg c6]

lemma hs_3 (m : ℕ) : H (m + 1) 3 = H m 0 + H m 1 + H m 2 + H m 3 + H m 4 + H m 5 + H m 6 := by
  have c0 : OMA.S_oeis_a126475.close (3 : Fin 7) (0 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : OMA.S_oeis_a126475.close (3 : Fin 7) (1 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (3 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (3 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (3 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : OMA.S_oeis_a126475.close (3 : Fin 7) (5 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : OMA.S_oeis_a126475.close (3 : Fin 7) (6 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6]

lemma hs_4 (m : ℕ) : H (m + 1) 4 = 0 + H m 1 + H m 2 + H m 3 + H m 4 + H m 5 + H m 6 := by
  have c0 : ¬ (OMA.S_oeis_a126475.close (4 : Fin 7) (0 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : OMA.S_oeis_a126475.close (4 : Fin 7) (1 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (4 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (4 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (4 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : OMA.S_oeis_a126475.close (4 : Fin 7) (5 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : OMA.S_oeis_a126475.close (4 : Fin 7) (6 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_neg c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6]

lemma hs_5 (m : ℕ) : H (m + 1) 5 = 0 + 0 + H m 2 + H m 3 + H m 4 + H m 5 + H m 6 := by
  have c0 : ¬ (OMA.S_oeis_a126475.close (5 : Fin 7) (0 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : ¬ (OMA.S_oeis_a126475.close (5 : Fin 7) (1 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : OMA.S_oeis_a126475.close (5 : Fin 7) (2 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (5 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (5 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : OMA.S_oeis_a126475.close (5 : Fin 7) (5 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : OMA.S_oeis_a126475.close (5 : Fin 7) (6 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_neg c0, if_neg c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6]

lemma hs_6 (m : ℕ) : H (m + 1) 6 = 0 + 0 + 0 + H m 3 + H m 4 + H m 5 + H m 6 := by
  have c0 : ¬ (OMA.S_oeis_a126475.close (6 : Fin 7) (0 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c1 : ¬ (OMA.S_oeis_a126475.close (6 : Fin 7) (1 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c2 : ¬ (OMA.S_oeis_a126475.close (6 : Fin 7) (2 : Fin 7)) := by unfold OMA.S_oeis_a126475.close; decide
  have c3 : OMA.S_oeis_a126475.close (6 : Fin 7) (3 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c4 : OMA.S_oeis_a126475.close (6 : Fin 7) (4 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c5 : OMA.S_oeis_a126475.close (6 : Fin 7) (5 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  have c6 : OMA.S_oeis_a126475.close (6 : Fin 7) (6 : Fin 7) := by unfold OMA.S_oeis_a126475.close; decide
  rw [H_succ, Fin.sum_univ_seven, if_neg c0, if_neg c1, if_neg c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6]

lemma a_sum (m : ℕ) : OMA.S_oeis_a126475.a (m + 1) = H m 0 + H m 1 + H m 2 + H m 3 + H m 4 + H m 5 + H m 6 := by
  rw [a_succ, Fin.sum_univ_seven]

lemma R0 (m : ℕ) : OMA.S_oeis_a126475.a (m + 1) = H m 0 + H m 1 + H m 2 + H m 3 + H m 4 + H m 5 + H m 6 := by
  exact a_sum m

lemma R1 (m : ℕ) : OMA.S_oeis_a126475.a (m + 2) = 4 * H m 0 + 5 * H m 1 + 6 * H m 2 + 7 * H m 3 + 6 * H m 4 + 5 * H m 5 + 4 * H m 6 := by
  have h : OMA.S_oeis_a126475.a (m + 2) = H (m + 1) 0 + H (m + 1) 1 + H (m + 1) 2 + H (m + 1) 3 + H (m + 1) 4 + H (m + 1) 5 + H (m + 1) 6 := R0 (m + 1)
  rw [h, hs_0 m, hs_1 m, hs_2 m, hs_3 m, hs_4 m, hs_5 m, hs_6 m]
  ring

lemma R2 (m : ℕ) : OMA.S_oeis_a126475.a (m + 3) = 22 * H m 0 + 28 * H m 1 + 33 * H m 2 + 37 * H m 3 + 33 * H m 4 + 28 * H m 5 + 22 * H m 6 := by
  have h : OMA.S_oeis_a126475.a (m + 3) = 4 * H (m + 1) 0 + 5 * H (m + 1) 1 + 6 * H (m + 1) 2 + 7 * H (m + 1) 3 + 6 * H (m + 1) 4 + 5 * H (m + 1) 5 + 4 * H (m + 1) 6 := R1 (m + 1)
  rw [h, hs_0 m, hs_1 m, hs_2 m, hs_3 m, hs_4 m, hs_5 m, hs_6 m]
  ring

lemma R3 (m : ℕ) : OMA.S_oeis_a126475.a (m + 4) = 120 * H m 0 + 153 * H m 1 + 181 * H m 2 + 203 * H m 3 + 181 * H m 4 + 153 * H m 5 + 120 * H m 6 := by
  have h : OMA.S_oeis_a126475.a (m + 4) = 22 * H (m + 1) 0 + 28 * H (m + 1) 1 + 33 * H (m + 1) 2 + 37 * H (m + 1) 3 + 33 * H (m + 1) 4 + 28 * H (m + 1) 5 + 22 * H (m + 1) 6 := R2 (m + 1)
  rw [h, hs_0 m, hs_1 m, hs_2 m, hs_3 m, hs_4 m, hs_5 m, hs_6 m]
  ring

lemma R4 (m : ℕ) : OMA.S_oeis_a126475.a (m + 5) = 657 * H m 0 + 838 * H m 1 + 991 * H m 2 + 1111 * H m 3 + 991 * H m 4 + 838 * H m 5 + 657 * H m 6 := by
  have h : OMA.S_oeis_a126475.a (m + 5) = 120 * H (m + 1) 0 + 153 * H (m + 1) 1 + 181 * H (m + 1) 2 + 203 * H (m + 1) 3 + 181 * H (m + 1) 4 + 153 * H (m + 1) 5 + 120 * H (m + 1) 6 := R3 (m + 1)
  rw [h, hs_0 m, hs_1 m, hs_2 m, hs_3 m, hs_4 m, hs_5 m, hs_6 m]
  ring

lemma rec_succ (k : ℕ) : (OMA.S_oeis_a126475.a (k + 5) : ℤ)
    = 5 * OMA.S_oeis_a126475.a (k + 4) + 3 * OMA.S_oeis_a126475.a (k + 3) - 2 * OMA.S_oeis_a126475.a (k + 2) - OMA.S_oeis_a126475.a (k + 1) := by
  rw [R4 k, R3 k, R2 k, R1 k, R0 k]
  push_cast
  ring

lemma small : OMA.S_oeis_a126475.a 0 = 1 ∧ OMA.S_oeis_a126475.a 1 = 7 ∧ OMA.S_oeis_a126475.a 2 = 37 ∧ OMA.S_oeis_a126475.a 3 = 203 ∧ OMA.S_oeis_a126475.a 4 = 1111 := by
  have r0 := R0 0
  simp only [H_zero] at r0
  have r1 := R1 0
  simp only [H_zero] at r1
  have r2 := R2 0
  simp only [H_zero] at r2
  have r3 := R3 0
  simp only [H_zero] at r3
  exact ⟨a_zero, r0, r1, r2, r3⟩

lemma rec0 : (OMA.S_oeis_a126475.a 4 : ℤ) = 5 * OMA.S_oeis_a126475.a 3 + 3 * OMA.S_oeis_a126475.a 2 - 2 * OMA.S_oeis_a126475.a 1 - OMA.S_oeis_a126475.a 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := small
  rw [h4, h3, h2, h1, h0]
  norm_num

lemma rec_all (m : ℕ) : (OMA.S_oeis_a126475.a (m + 4) : ℤ)
    = 5 * OMA.S_oeis_a126475.a (m + 3) + 3 * OMA.S_oeis_a126475.a (m + 2) - 2 * OMA.S_oeis_a126475.a (m + 1) - OMA.S_oeis_a126475.a m := by
  rcases m with _ | k
  · exact rec0
  · exact rec_succ k

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A126475Aux

set_option maxHeartbeats 1600000 in
open A126475Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a126475.main := by
  refine ⟨?_, ?_⟩
  · have hD : ((1 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3
        + PowerSeries.X ^ 4 : PowerSeries ℚ)) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 +
        PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 +
        PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : ((1 + 2 * PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries ℚ)) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 +
        PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    by_cases h4 : 4 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hz := rec_all m
      have hq : (OMA.S_oeis_a126475.a (m + 4) : ℚ) = 5 * OMA.S_oeis_a126475.a (m + 3) + 3 * OMA.S_oeis_a126475.a (m + 2) - 2 * OMA.S_oeis_a126475.a (m + 1) - OMA.S_oeis_a126475.a m := by
        exact_mod_cast hz
      have c0 : (0 : ℕ) ≤ m + 4 := by omega
      have c1 : (1 : ℕ) ≤ m + 4 := by omega
      have c2 : (2 : ℕ) ≤ m + 4 := by omega
      have c3 : (3 : ℕ) ≤ m + 4 := by omega
      have c4 : (4 : ℕ) ≤ m + 4 := by omega
      have n0 : ¬ (m + 4 = 0) := by omega
      have n1 : ¬ (m + 4 = 1) := by omega
      have n2 : ¬ (m + 4 = 2) := by omega
      have n3 : ¬ (m + 4 = 3) := by omega
      have d0 : m + 4 - 0 = m + 4 := by omega
      have d1 : m + 4 - 1 = m + 3 := by omega
      have d2 : m + 4 - 2 = m + 2 := by omega
      have d3 : m + 4 - 3 = m + 1 := by omega
      have d4 : m + 4 - 4 = m := by omega
      rw [if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_neg n0, if_neg n1, if_neg n2,
        if_neg n3, d0, d1, d2, d3, d4]
      linarith
    · obtain ⟨h0, h1, h2, h3, _⟩ := small
      have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn with rfl | rfl | rfl | rfl
      · norm_num [h0]
      · norm_num [h0, h1]
      · norm_num [h0, h1, h2]
      · norm_num [h0, h1, h2, h3]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have d1 : m + 4 - 1 = m + 3 := by omega
    have d2 : m + 4 - 2 = m + 2 := by omega
    have d3 : m + 4 - 3 = m + 1 := by omega
    have d4 : m + 4 - 4 = m := by omega
    rw [d1, d2, d3, d4]
    exact rec_all m
