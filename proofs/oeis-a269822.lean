import OMAStatements.S_oeis_a269822
import Mathlib

open Finset

namespace A269822

theorem h1 : ∀ v : Fin 5, (univ.filter (fun y : Fin 5 => (y : ℕ) + (v : ℕ) = 4)).card = 1 := by decide

theorem h4 : ∀ v : Fin 5, (univ.filter (fun y : Fin 5 => ¬ ((y : ℕ) + (v : ℕ) = 4))).card = 4 := by
  decide

theorem hsum (v : Fin 5) (a b : ℕ) :
    (∑ y : Fin 5, if (y : ℕ) + (v : ℕ) = 4 then a else b) = a + 4 * b := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1 v, h4 v]
  simp

theorem pairs_cons (m : ℕ) (y : Fin 5) (x : Fin (m + 1) → Fin 5) :
    OMA.S_oeis_a269822.pairsTotallingFour (m + 1) (Fin.cons y x : Fin (m + 1 + 1) → Fin 5)
      = (if (y : ℕ) + (x 0 : ℕ) = 4 then 1 else 0) + OMA.S_oeis_a269822.pairsTotallingFour m x := by
  unfold OMA.S_oeis_a269822.pairsTotallingFour
  rw [Fin.card_filter_univ_succ']
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

/-- words of length `m + 1` with exactly `k` adjacent pairs totalling four -/
def W (m k : ℕ) : ℕ :=
  (univ.filter (fun x : Fin (m + 1) → Fin 5 => OMA.S_oeis_a269822.pairsTotallingFour m x = k)).card

theorem W_step (m k : ℕ) :
    W (m + 1) k
      = (univ.filter (fun x : Fin (m + 1) → Fin 5 =>
            1 + OMA.S_oeis_a269822.pairsTotallingFour m x = k)).card + 4 * W m k := by
  unfold W
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin 5)).sum_comp, Fintype.sum_prod_type_right,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : ∀ y : Fin 5,
      (if OMA.S_oeis_a269822.pairsTotallingFour (m + 1)
          ((Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin 5)) (y, x)) = k then 1 else 0)
      = if (y : ℕ) + (x 0 : ℕ) = 4
          then (if 1 + OMA.S_oeis_a269822.pairsTotallingFour m x = k then 1 else 0)
          else (if OMA.S_oeis_a269822.pairsTotallingFour m x = k then 1 else 0) := by
    intro y
    have he : (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin 5)) (y, x)
        = (Fin.cons y x : Fin (m + 1 + 1) → Fin 5) := rfl
    rw [he, pairs_cons m y x]
    by_cases c : (y : ℕ) + (x 0 : ℕ) = 4
    · simp [c]
    · simp [c]
  rw [Finset.sum_congr rfl (fun y _ => hx y), hsum]

theorem W_zero_zero : W 0 0 = 5 := by decide

theorem W_zero_succ (k : ℕ) : W 0 (k + 1) = 0 := by
  unfold W OMA.S_oeis_a269822.pairsTotallingFour
  simp

theorem W_k0 (m : ℕ) : W m 0 = 5 * 4 ^ m := by
  induction m with
  | zero => simpa using W_zero_zero
  | succ m ih =>
    rw [W_step, ih]
    have : (univ.filter (fun x : Fin (m + 1) → Fin 5 =>
            1 + OMA.S_oeis_a269822.pairsTotallingFour m x = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      omega
    rw [this]
    ring

theorem W_k1 (m : ℕ) : W m 1 = 5 * m * 4 ^ (m - 1) := by
  induction m with
  | zero => simpa using W_zero_succ 0
  | succ m ih =>
    rw [W_step, ih]
    have : (univ.filter (fun x : Fin (m + 1) → Fin 5 =>
            1 + OMA.S_oeis_a269822.pairsTotallingFour m x = 1)).card = W m 0 := by
      unfold W
      congr 1
      ext x
      simp
    rw [this, W_k0]
    cases m with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel]
      ring

theorem a_eq (m : ℕ) : OMA.S_oeis_a269822.a (m + 1) = 5 * m * 4 ^ (m - 1) := W_k1 m

end A269822

theorem OMA.solution : type_of% @OMA.S_oeis_a269822.main := by
  have hc : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a269822.a n = 5 * 4 ^ (n - 2) * (n - 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [A269822.a_eq]
    cases m with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel]
      have : j + 1 + 1 - 2 = j := by omega
      rw [this]
      ring
  have hrec : ∀ n : ℕ, 3 ≤ n → (OMA.S_oeis_a269822.a n : ℤ)
      = 8 * OMA.S_oeis_a269822.a (n - 1) - 16 * OMA.S_oeis_a269822.a (n - 2) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
    have e1 : j + 3 - 1 = j + 2 := by omega
    have e2 : j + 3 - 2 = j + 1 := by omega
    rw [e1, e2, A269822.a_eq (j + 2), A269822.a_eq (j + 1), A269822.a_eq j]
    cases j with
    | zero => norm_num
    | succ i =>
      simp only [Nat.add_sub_cancel]
      have e3 : i + 1 + 2 - 1 = i + 2 := by omega
      rw [e3]
      push_cast
      ring
  refine ⟨hrec, ?_, hc⟩
  have a0 : OMA.S_oeis_a269822.a 0 = 0 := rfl
  have a1 : OMA.S_oeis_a269822.a 1 = 0 := by rw [A269822.a_eq 0]; simp
  have a2 : OMA.S_oeis_a269822.a 2 = 5 := by rw [A269822.a_eq 1]; simp
  have key : ∀ n : ℕ, (OMA.S_oeis_a269822.a n : ℚ)
      - 8 * (if 1 ≤ n then (OMA.S_oeis_a269822.a (n - 1) : ℚ) else 0)
      + 16 * (if 2 ≤ n then (OMA.S_oeis_a269822.a (n - 2) : ℚ) else 0)
      = 5 * (if n = 2 then 1 else 0) := by
    intro n
    rcases n with _ | _ | _ | j
    · simp [a0]
    · simp [a0, a1]
    · simp [a0, a1, a2]
    · have h := hrec (j + 1 + 1 + 1) (by omega)
      have e3 : j + 1 + 1 + 1 - 1 = j + 2 := by omega
      have e4 : j + 1 + 1 + 1 - 2 = j + 1 := by omega
      rw [e3, e4] at h
      have hq : (OMA.S_oeis_a269822.a (j + 1 + 1 + 1) : ℚ)
          = 8 * OMA.S_oeis_a269822.a (j + 2) - 16 * OMA.S_oeis_a269822.a (j + 1) := by
        exact_mod_cast h
      have c1 : 1 ≤ j + 1 + 1 + 1 := by omega
      have c2 : 2 ≤ j + 1 + 1 + 1 := by omega
      have c3 : ¬ (j + 1 + 1 + 1 = 2) := by omega
      rw [if_pos c1, if_pos c2, if_neg c3, e3, e4, hq]
      ring
  have h8 : (PowerSeries.C (8 : ℚ)) = 8 := map_ofNat _ 8
  have h16 : (PowerSeries.C (16 : ℚ)) = 16 := map_ofNat _ 16
  have h5 : (PowerSeries.C (5 : ℚ)) = 5 := map_ofNat _ 5
  have e : PowerSeries.mk (fun n => (OMA.S_oeis_a269822.a n : ℚ)) * (1 - 4 * PowerSeries.X) ^ 2
      = PowerSeries.mk (fun n => (OMA.S_oeis_a269822.a n : ℚ))
        - PowerSeries.C (8 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a269822.a n : ℚ)) * PowerSeries.X ^ 1)
        + PowerSeries.C (16 : ℚ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a269822.a n : ℚ)) * PowerSeries.X ^ 2) := by
    rw [h8, h16]
    ring
  rw [e, ← h5]
  ext n
  conv_rhs => rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  exact key n
