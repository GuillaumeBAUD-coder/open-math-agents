import OMAStatements.S_oeis_a126395
import Mathlib

namespace A126395Aux

open OMA.S_oeis_a126395 in
def V (n : ℕ) (x : Fin n → Fin 8) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j)

open OMA.S_oeis_a126395 in
lemma V_cons (n : ℕ) (d e : Fin 8) (y : Fin n → Fin 8) :
    V (n + 1 + 1) (Fin.cons (α := fun _ => Fin 8) d (Fin.cons (α := fun _ => Fin 8) e y)) ↔
      close d e ∧ V (n + 1) (Fin.cons (α := fun _ => Fin 8) e y) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h01 := h 0 1 rfl
      simpa using h01
    · intro i j hij
      have h2 := h i.succ j.succ (by rw [Fin.val_succ, Fin.val_succ, hij])
      simpa using h2
  · rintro ⟨hde, hv⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j' =>
        have h0 : ((0 : Fin (n + 1 + 1)) : ℕ) = 0 := rfl
        rw [Fin.val_succ, h0] at hij
        have hv0 : (j' : ℕ) = 0 := by omega
        have hj : j' = 0 := Fin.ext hv0
        subst hj
        simpa using hde
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j' =>
        have h2 := hv i' j' (by rw [Fin.val_succ, Fin.val_succ] at hij; omega)
        simpa using h2

lemma V_one (x : Fin 1 → Fin 8) : V 1 x := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma V_zero (x : Fin 0 → Fin 8) : V 0 x := fun i => i.elim0

noncomputable def N (n : ℕ) (d : Fin 8) : ℕ :=
  ∑ y : Fin n → Fin 8,
    @ite ℕ (V (n + 1) (Fin.cons (α := fun _ => Fin 8) d y)) (Classical.propDecidable _) 1 0

noncomputable def S (n : ℕ) : ℕ :=
  ∑ x : Fin n → Fin 8, @ite ℕ (V n x) (Classical.propDecidable _) 1 0

lemma sum_cons_split (n : ℕ) (g : (Fin (n + 1) → Fin 8) → ℕ) :
    ∑ x, g x = ∑ d : Fin 8, ∑ y : Fin n → Fin 8, g (Fin.cons (α := fun _ => Fin 8) d y) := by
  calc ∑ x, g x
      = ∑ p : Fin 8 × (Fin n → Fin 8), g (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 8) p) :=
        (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 8)) g).symm
    _ = ∑ d : Fin 8, ∑ y : Fin n → Fin 8, g (Fin.cons (α := fun _ => Fin 8) d y) :=
        Fintype.sum_prod_type _

lemma N_zero (d : Fin 8) : N 0 d = 1 := by
  unfold N
  rw [Fintype.sum_unique]
  exact if_pos (V_one _)

lemma S_zero : S 0 = 1 := by
  unfold S
  rw [Fintype.sum_unique]
  exact if_pos (V_zero _)

lemma S_succ (n : ℕ) : S (n + 1) = ∑ d : Fin 8, N n d := by
  unfold S N
  rw [sum_cons_split]

open OMA.S_oeis_a126395 in
open Classical in
lemma N_succ (n : ℕ) (d : Fin 8) :
    N (n + 1) d = ∑ e : Fin 8, if close d e then N n e else 0 := by
  unfold N
  rw [sum_cons_split]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hde : close d e
  · rw [if_pos hde]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact if_congr ((V_cons n d e y).trans (and_iff_right hde)) rfl rfl
  · rw [if_neg hde]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    exact if_neg (fun h => hde ((V_cons n d e y).mp h).1)

open OMA.S_oeis_a126395 in
open Classical in
lemma a_eq_S (n : ℕ) : a n = S n := by
  unfold a S
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl (fun x _ => if_congr Iff.rfl rfl rfl)

open OMA.S_oeis_a126395 in
def cnt : ℕ → Fin 8 → ℕ
  | 0, _ => 1
  | h + 1, d => ∑ e : Fin 8, if close d e then cnt h e else 0

open OMA.S_oeis_a126395 in
lemma cnt_succ (h : ℕ) (d : Fin 8) :
    cnt (h + 1) d = ∑ e : Fin 8, if close d e then cnt h e else 0 := rfl

lemma N_eq (n : ℕ) : ∀ d : Fin 8, N n d = cnt n d := by
  induction n with
  | zero =>
    intro d
    exact N_zero d
  | succ n ih =>
    intro d
    rw [N_succ, cnt_succ]
    exact Finset.sum_congr rfl (fun e _ => if_congr Iff.rfl (ih e) rfl)

lemma vec_rec (h : ℕ) : ∀ d : Fin 8, cnt (h + 3) d + cnt (h + 1) d + 6 * cnt (h) d = 5 * cnt (h + 2) d := by
  induction h with
  | zero => decide +kernel
  | succ h ih =>
    intro d
    show cnt (h + 3 + 1) d + cnt (h + 1 + 1) d + 6 * cnt (h + 1) d = 5 * cnt (h + 2 + 1) d
    rw [cnt_succ (h + 3) d, cnt_succ (h + 1) d, cnt_succ (h) d, cnt_succ (h + 2) d]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have he := ih e
    split_ifs
    · exact he
    · rfl

open OMA.S_oeis_a126395 in
lemma a_succ (h : ℕ) : a (h + 1) = ∑ d : Fin 8, cnt h d := by
  rw [a_eq_S, S_succ]
  exact Finset.sum_congr rfl (fun d _ => N_eq h d)

open OMA.S_oeis_a126395 in
lemma a_zero : a 0 = 1 := by
  rw [a_eq_S, S_zero]

open OMA.S_oeis_a126395 in
lemma a_vals : a 1 = 8 ∧ a 2 = 34 ∧ a 3 = 150 :=
  ⟨(a_succ 0).trans (by decide +kernel), (a_succ 1).trans (by decide +kernel), (a_succ 2).trans (by decide +kernel)⟩

open OMA.S_oeis_a126395 in
lemma a_rec (h : ℕ) : a (h + 4) + a (h + 2) + 6 * a (h + 1) = 5 * a (h + 3) := by
  have e3 : a (h + 4) = ∑ d : Fin 8, cnt (h + 3) d := a_succ (h + 3)
  have e1 : a (h + 2) = ∑ d : Fin 8, cnt (h + 1) d := a_succ (h + 1)
  have e0 : a (h + 1) = ∑ d : Fin 8, cnt (h) d := a_succ (h)
  have e2 : a (h + 3) = ∑ d : Fin 8, cnt (h + 2) d := a_succ (h + 2)
  rw [e3, e1, e0, e2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => vec_rec h d)

end A126395Aux

open OMA.S_oeis_a126395 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a126395.main := by
  obtain ⟨v1, v2, v3⟩ := A126395Aux.a_vals
  refine ⟨?_, ?_⟩
  · have hD : (1 - 5 * X + X ^ 2 + 6 * X ^ 3 : PowerSeries ℚ)
        = C (1) * X ^ 0 + C (-5) * X ^ 1 + C (1) * X ^ 2 + C (6) * X ^ 3 := by
      simp only [map_neg, map_ofNat, map_one]; ring
    have hN : (1 + 3 * X - 5 * X ^ 2 - 6 * X ^ 3 : PowerSeries ℚ)
        = C (1) * X ^ 0 + C (3) * X ^ 1 + C (-5) * X ^ 2 + C (-6) * X ^ 3 := by
      simp only [map_neg, map_ofNat, map_one]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | n
    · norm_num [A126395Aux.a_zero, v1, v2, v3]
    · norm_num [A126395Aux.a_zero, v1, v2, v3]
    · norm_num [A126395Aux.a_zero, v1, v2, v3]
    · norm_num [A126395Aux.a_zero, v1, v2, v3]
    · have h := A126395Aux.a_rec n
      have hq : (a (n + 4) : ℚ) + (a (n + 2) : ℚ) + 6 * (a (n + 1) : ℚ) = 5 * (a (n + 3) : ℚ) := by
        exact_mod_cast h
      simp
      linarith
  · skip
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h := A126395Aux.a_rec m
    have hz : (a (m + 4) : ℤ) + (a (m + 2) : ℤ) + 6 * (a (m + 1) : ℤ) = 5 * (a (m + 3) : ℤ) := by
      exact_mod_cast h
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    linarith
