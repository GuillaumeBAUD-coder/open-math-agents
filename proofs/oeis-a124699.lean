import OMAStatements.S_oeis_a124699

-- Problem: A124699: Number of base 6 circular n-digit numbers with adjacent digits differing by 1 or less.
-- Upstream: statements/oeis-a124699.lean (declaration OMA.S_oeis_a124699.main)
-- Credit: @minimumnz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Circ

variable {k : ℕ}

def W (A : Matrix (Fin k) (Fin k) ℤ) : (m : ℕ) → Fin k → (Fin m → Fin k) → Fin k → ℤ
  | 0, x, _, y => A x y
  | m + 1, x, t, y => A x (t 0) * W A m (t 0) (Fin.tail t) y

theorem W_sum (A : Matrix (Fin k) (Fin k) ℤ) : ∀ (m : ℕ) (x y : Fin k),
    ∑ t : Fin m → Fin k, W A m x t y = (A ^ (m + 1)) x y := by
  intro m
  induction m with
  | zero => intro x y; simp [W]
  | succ m ih =>
    intro x y
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type,
      pow_succ' A (m + 1), Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← ih z y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [W, Fin.consEquiv]

theorem cyc_prod (A : Matrix (Fin k) (Fin k) ℤ) : ∀ (m : ℕ) (s : Fin (m + 1) → Fin k) (y : Fin k),
    ∏ i : Fin (m + 1), A (s i) (if h : i.val + 1 < m + 1 then s ⟨i.val + 1, h⟩ else y)
      = W A m (s 0) (Fin.tail s) y := by
  intro m
  induction m with
  | zero => intro s y; simp [W]
  | succ m ih =>
    intro s y
    rw [Fin.prod_univ_succ, W, ← ih (Fin.tail s) y]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i.val + 1 < m + 1
    · have h' : (i.succ).val + 1 < m + 1 + 1 := by simp; omega
      rw [dif_pos h, dif_pos h']
      rfl
    · have h' : ¬ (i.succ).val + 1 < m + 1 + 1 := by simp; omega
      rw [dif_neg h, dif_neg h']
      rfl

theorem card_eq_trace (A : Matrix (Fin k) (Fin k) ℤ) (R : Fin k → Fin k → Prop) [DecidableRel R]
    (hA : ∀ x y, A x y = if R x y then 1 else 0) (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 1) → Fin k)).filter (fun s =>
      ∀ i : Fin (m + 1), R (s i)
        (s ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))).card : ℤ)
      = Matrix.trace (A ^ (m + 1)) := by
  rw [Finset.card_filter]
  push_cast
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [← W_sum A m]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
  have key := cyc_prod A m (Fin.cons x t) x
  simp only [Fin.cons_zero, Fin.tail_cons] at key
  rw [← key]
  simp only [hA]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Fin.consEquiv, Equiv.coe_fn_mk]
  refine if_congr ?_ rfl rfl
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, forall_true_left]
  by_cases h : i.val + 1 < m + 1
  · rw [dif_pos h]
    have : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt h
    simp only [this]
  · rw [dif_neg h]
    have : (i.val + 1) % (m + 1) = 0 := by
      have : i.val + 1 = m + 1 := by omega
      rw [this]; exact Nat.mod_self _
    simp only [this]
    rfl

end OMA.Circ

namespace OMA.P124699
open OMA.S_oeis_a124699

def R (x y : Fin 6) : Prop := Int.natAbs (((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)) ≤ 1

instance (x y : Fin 6) : Decidable (R x y) := inferInstanceAs (Decidable (_ ≤ _))

def A : Matrix (Fin 6) (Fin 6) ℤ := fun x y => if R x y then 1 else 0

theorem a_eq (m : ℕ) : a (m + 1) = Matrix.trace (A ^ (m + 1)) := by
  rw [← OMA.Circ.card_eq_trace A R (fun _ _ => rfl) m]
  simp only [a, decide_eq_true_eq, R]
  congr

theorem a0 : a 0 = 1 := by decide

set_option maxRecDepth 100000 in
theorem Arec : A ^ 7 = (6 : ℤ) • A ^ 6 - (10 : ℤ) • A ^ 5 + (9 : ℤ) • A ^ 3 - (2 : ℤ) • A ^ 2 - A := by
  decide

set_option maxRecDepth 100000 in
theorem tr1 : Matrix.trace (A ^ 1) = 6 ∧ Matrix.trace (A ^ 2) = 16 ∧ Matrix.trace (A ^ 3) = 36 ∧
    Matrix.trace (A ^ 4) = 92 ∧ Matrix.trace (A ^ 5) = 236 ∧ Matrix.trace (A ^ 6) = 622 := by
  decide

theorem a1 : a 1 = 6 := (a_eq 0).trans tr1.1
theorem a2 : a 2 = 16 := (a_eq 1).trans tr1.2.1
theorem a3 : a 3 = 36 := (a_eq 2).trans tr1.2.2.1
theorem a4 : a 4 = 92 := (a_eq 3).trans tr1.2.2.2.1
theorem a5 : a 5 = 236 := (a_eq 4).trans tr1.2.2.2.2.1
theorem a6 : a 6 = 622 := (a_eq 5).trans tr1.2.2.2.2.2

theorem rec (m : ℕ) : a (m + 7) = 6 * a (m + 6) - 10 * a (m + 5) + 9 * a (m + 3)
    - 2 * a (m + 2) - a (m + 1) := by
  rw [a_eq (m + 6), a_eq (m + 5), a_eq (m + 4), a_eq (m + 2), a_eq (m + 1), a_eq m]
  have h : A ^ (m + 6 + 1) = (6 : ℤ) • A ^ (m + 5 + 1) - (10 : ℤ) • A ^ (m + 4 + 1)
      + (9 : ℤ) • A ^ (m + 2 + 1) - (2 : ℤ) • A ^ (m + 1 + 1) - A ^ (m + 1) := by
    have e1 : A ^ (m + 6 + 1) = A ^ m * A ^ 7 := by rw [← pow_add]
    have e2 : A ^ (m + 5 + 1) = A ^ m * A ^ 6 := by rw [← pow_add]
    have e3 : A ^ (m + 4 + 1) = A ^ m * A ^ 5 := by rw [← pow_add]
    have e4 : A ^ (m + 2 + 1) = A ^ m * A ^ 3 := by rw [← pow_add]
    have e5 : A ^ (m + 1 + 1) = A ^ m * A ^ 2 := by rw [← pow_add]
    have e6 : A ^ (m + 1) = A ^ m * A := by rw [pow_succ]
    rw [e1, e2, e3, e4, e5, e6, Arec]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul]
  rw [h]
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

end OMA.P124699

theorem OMA.solution : type_of% @OMA.S_oeis_a124699.main := by
  have hr : ∀ m : ℕ, (OMA.S_oeis_a124699.a (m + 7) : ℚ)
      = 6 * OMA.S_oeis_a124699.a (m + 6) - 10 * OMA.S_oeis_a124699.a (m + 5)
        + 9 * OMA.S_oeis_a124699.a (m + 3) - 2 * OMA.S_oeis_a124699.a (m + 2)
        - OMA.S_oeis_a124699.a (m + 1) := by
    intro m; exact_mod_cast OMA.P124699.rec m
  refine ⟨?_, ?_⟩
  · have hD : ((1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
        (1 - 4 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) : PowerSeries ℚ)
        = 1 - PowerSeries.C (6 : ℚ) * PowerSeries.X + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 2
          - PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 5
          + PowerSeries.X ^ 6 := by
      simp only [map_ofNat]; ring
    have hN : (1 - 10 * PowerSeries.X ^ 2 + 27 * PowerSeries.X ^ 4 - 8 * PowerSeries.X ^ 5
        - 5 * PowerSeries.X ^ 6 : PowerSeries ℚ)
        = 1 - PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (27 : ℚ) * PowerSeries.X ^ 4
          - PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 6 := by
      simp only [map_ofNat]
    rw [hD, hN]
    have hE : PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) *
        (1 - PowerSeries.C (6 : ℚ) * PowerSeries.X + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 2
          - PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 5
          + PowerSeries.X ^ 6)
        = PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ))
          - PowerSeries.C (6 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.C (10 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) * PowerSeries.X ^ 2)
          - PowerSeries.C (9 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) * PowerSeries.X ^ 4)
          + PowerSeries.C (2 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) * PowerSeries.X ^ 5)
          + PowerSeries.mk (fun n => (OMA.S_oeis_a124699.a n : ℚ)) * PowerSeries.X ^ 6 := by
      ring
    rw [hE]
    ext n
    rcases n with _ | _ | _ | _ | _ | _ | _ | m
    · simp [OMA.P124699.a0, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
    · simp [OMA.P124699.a0, OMA.P124699.a1, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
    · simp [OMA.P124699.a0, OMA.P124699.a1, OMA.P124699.a2, PowerSeries.coeff_X_pow,
        PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [OMA.P124699.a0, OMA.P124699.a1, OMA.P124699.a2, OMA.P124699.a3,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [OMA.P124699.a0, OMA.P124699.a1, OMA.P124699.a2, OMA.P124699.a3, OMA.P124699.a4,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [OMA.P124699.a0, OMA.P124699.a1, OMA.P124699.a2, OMA.P124699.a3, OMA.P124699.a4,
        OMA.P124699.a5, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [OMA.P124699.a0, OMA.P124699.a1, OMA.P124699.a2, OMA.P124699.a3, OMA.P124699.a4,
        OMA.P124699.a5, OMA.P124699.a6, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow']
      norm_num
    · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_X_pow', hr m]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    exact hr m
