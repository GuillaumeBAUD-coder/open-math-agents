import OMAStatements.S_oeis_a126529
import Mathlib

namespace OMA.A126529Proof

open OMA.S_oeis_a126529
open PowerSeries

def cnt (n : ℕ) (v : Fin 8) : ℕ :=
  (Finset.univ.filter fun g : Fin n → Fin 8 => (v :: List.ofFn g).IsChain near).card

def V : ℕ → Fin 8 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun v => ∑ w, if near v w then V n w else 0

theorem ofFn_cons' (n : ℕ) (x : Fin 8) (g : Fin n → Fin 8) :
    List.ofFn (Fin.cons x g : Fin (n + 1) → Fin 8) = x :: List.ofFn g := by
  rw [List.ofFn_succ]
  simp

theorem sum_cons (n : ℕ) (F : (Fin (n + 1) → Fin 8) → ℕ) :
    ∑ f, F f = ∑ x, ∑ g : Fin n → Fin 8, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 8)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem a_succ (n : ℕ) : a (n + 1) = ∑ v, cnt n v := by
  unfold a cnt
  simp only [Finset.card_filter]
  rw [sum_cons n]
  simp only [ofFn_cons']

theorem cnt_succ (n : ℕ) (v : Fin 8) :
    cnt (n + 1) v = ∑ w, if near v w then cnt n w else 0 := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [sum_cons n]
  simp only [ofFn_cons', List.isChain_cons_cons]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : near v w <;> simp [h]

theorem cnt_zero (v : Fin 8) : cnt 0 v = 1 := by
  simp [cnt]

theorem cnt_eq (n : ℕ) : ∀ v, (cnt n v : ℤ) = V n v := by
  induction n with
  | zero => intro v; simp [cnt_zero, V]
  | succ n ih =>
    intro v
    rw [cnt_succ, V]
    push_cast
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp [ih]

theorem V_base : ∀ v, V 3 v = 7 * V 2 v + 3 * V 1 v - 4 * V 0 v := by
  decide

theorem V_rec (n : ℕ) : ∀ v, V (n + 3) v = 7 * V (n + 2) v + 3 * V (n + 1) v - 4 * V n v := by
  induction n with
  | zero => exact V_base
  | succ n ih =>
    intro v
    have e : ∀ w, (if near v w then V (n + 3) w else 0) =
        7 * (if near v w then V (n + 2) w else 0) + 3 * (if near v w then V (n + 1) w else 0)
          - 4 * (if near v w then V n w else 0) := by
      intro w
      split_ifs
      · exact ih w
      · ring
    show (∑ w, if near v w then V (n + 3) w else 0) =
      7 * (∑ w, if near v w then V (n + 2) w else 0) + 3 * (∑ w, if near v w then V (n + 1) w else 0)
        - 4 * (∑ w, if near v w then V n w else 0)
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem aV (n : ℕ) : (a (n + 1) : ℤ) = ∑ v, V n v := by
  rw [a_succ]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => cnt_eq n v)

theorem a0 : a 0 = 1 := by
  simp [a]

theorem vals : (a 1 : ℤ) = 8 ∧ (a 2 : ℤ) = 58 ∧ (a 3 : ℤ) = 426 := by
  rw [aV, aV, aV]
  decide

theorem recZ (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 7 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) := by
  rcases (show n = 3 ∨ 4 ≤ n by omega) with h | h
  · subst h
    obtain ⟨v1, v2, v3⟩ := vals
    simp only [show 3 - 1 = 2 from rfl, show 3 - 2 = 1 from rfl, show 3 - 3 = 0 from rfl,
      v1, v2, v3, a0]
    norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    rw [show j + 4 - 1 = j + 2 + 1 by omega, show j + 4 - 2 = j + 1 + 1 by omega,
      show j + 4 - 3 = j + 1 by omega, show j + 4 = j + 3 + 1 by omega, aV, aV, aV, aV]
    simp only [V_rec j, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

end OMA.A126529Proof

open OMA.S_oeis_a126529 OMA.A126529Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a126529.main := by
  refine ⟨?_, recZ⟩
  ext k
  have e1 : ∀ A : PowerSeries ℚ, A * (1 - 7 * X - 3 * X ^ 2 + 4 * X ^ 3) =
      A - C (7 : ℚ) * (A * X ^ 1) - C (3 : ℚ) * (A * X ^ 2) + C (4 : ℚ) * (A * X ^ 3) := by
    intro A
    rw [show (C (7 : ℚ) : PowerSeries ℚ) = 7 from map_ofNat C 7,
      show (C (3 : ℚ) : PowerSeries ℚ) = 3 from map_ofNat C 3,
      show (C (4 : ℚ) : PowerSeries ℚ) = 4 from map_ofNat C 4]
    ring
  have e2 : (1 + X - X ^ 2 : PowerSeries ℚ) = C (1 : ℚ) + C (1 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 := by
    rw [map_one]
    ring
  rw [e1, e2]
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, coeff_mk]
  obtain ⟨v1, v2, v3⟩ := vals
  have q1 : (a 1 : ℚ) = 8 := by exact_mod_cast v1
  have q2 : (a 2 : ℚ) = 58 := by exact_mod_cast v2
  rcases (show k ≤ 2 ∨ 3 ≤ k by omega) with hk | hk
  · interval_cases k <;> simp [a0, q1, q2] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hr := recZ (j + 3) (by omega)
    simp only [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
      show j + 3 - 3 = j by omega] at hr
    have hq : ((a (j + 3) : ℤ) : ℚ) = ((7 * a (j + 2) + 3 * a (j + 1) - 4 * a j : ℤ) : ℚ) := by rw [hr]
    push_cast at hq
    simp only [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
      show j + 3 - 3 = j by omega,
      if_pos (show 1 ≤ j + 3 by omega), if_pos (show 2 ≤ j + 3 by omega),
      if_pos (show 3 ≤ j + 3 by omega), if_neg (show j + 3 ≠ 0 by omega),
      if_neg (show j + 2 ≠ 0 by omega), if_neg (show j + 1 ≠ 0 by omega)]
    rw [hq]
    ring
