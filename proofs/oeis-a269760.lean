import OMAStatements.S_oeis_a269760
import Mathlib

/-
A269760: the number of words x_1 ... x_n over 0..5 with exactly one adjacent pair summing to 5
is 6 * 5^(n-2) * (n-1) for n >= 1; the recurrence and the generating function follow.

The count is done for an arbitrary alphabet 0..c and an abstract pair counter pr with
pr(cons b y) = [b + y_0 = c] + pr(y).
- cnt1, cnt0: for a fixed letter t exactly one letter b has b + t = c, and c letters do not.
- inner0, inner1: the number of b with [b + t = c] + p = 0 (or 1), as a function of p.
- step: splitting a word into its first letter and the rest gives
  N0(m+1) = c N0(m) and N1(m+1) = N0(m) + c N1(m), where Nj counts words with j such pairs.
- closed: N0(m) = (c+1) c^m and N1(m+1) = (c+1) c^m (m+1), by induction.
The three claims are then algebra; the generating function is checked coefficient by coefficient.
-/

namespace OMA.P269760

open Finset

lemma cnt1 (c : ℕ) (t : Fin (c + 1)) :
    (univ.filter (fun b : Fin (c + 1) => (b : ℕ) + (t : ℕ) = c)).card = 1 := by
  have e : univ.filter (fun b : Fin (c + 1) => (b : ℕ) + (t : ℕ) = c) = {Fin.rev t} := by
    ext b
    have h1 := t.isLt
    have h2 := b.isLt
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, Fin.val_rev]
    omega
  rw [e, card_singleton]

lemma cnt0 (c : ℕ) (t : Fin (c + 1)) :
    (univ.filter (fun b : Fin (c + 1) => ¬ ((b : ℕ) + (t : ℕ) = c))).card = c := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (c + 1))))
    (fun b : Fin (c + 1) => (b : ℕ) + (t : ℕ) = c)
  rw [cnt1, card_univ, Fintype.card_fin] at h
  omega

lemma inner0 (c : ℕ) (t : Fin (c + 1)) (p : ℕ) :
    ∑ b : Fin (c + 1), (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + p = 0 then 1 else 0) =
      if p = 0 then c else 0 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have e : ∀ b : Fin (c + 1),
        (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + 0 = 0 then 1 else 0) =
          if ¬ ((b : ℕ) + (t : ℕ) = c) then 1 else 0 := fun b => by split_ifs <;> simp_all
    rw [if_pos rfl]
    simp only [e]
    rw [← Finset.card_filter]
    exact cnt0 c t
  · have e : ∀ b : Fin (c + 1),
        (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + p = 0 then 1 else 0) = 0 :=
      fun b => by split_ifs <;> omega
    simp only [e, Finset.sum_const_zero]
    rw [if_neg (by omega)]

lemma inner1 (c : ℕ) (t : Fin (c + 1)) (p : ℕ) :
    ∑ b : Fin (c + 1), (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + p = 1 then 1 else 0) =
      (if p = 0 then 1 else 0) + (if p = 1 then c else 0) := by
  rcases p with _ | _ | p
  · have e : ∀ b : Fin (c + 1),
        (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + 0 = 1 then 1 else 0) =
          if (b : ℕ) + (t : ℕ) = c then 1 else 0 := fun b => by split_ifs <;> simp_all
    simp only [e]
    rw [← Finset.card_filter, cnt1]
    simp
  · have e : ∀ b : Fin (c + 1),
        (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + (0 + 1) = 1 then 1 else 0) =
          if ¬ ((b : ℕ) + (t : ℕ) = c) then 1 else 0 := fun b => by split_ifs <;> simp_all
    simp only [e]
    rw [← Finset.card_filter, cnt0]
    simp
  · have e : ∀ b : Fin (c + 1),
        (if (if (b : ℕ) + (t : ℕ) = c then 1 else 0) + (p + 1 + 1) = 1 then 1 else 0) = 0 :=
      fun b => by split_ifs <;> omega
    simp only [e, Finset.sum_const_zero]
    simp

lemma pr_cons (c m : ℕ) (b : Fin (c + 1)) (y : Fin (m + 1) → Fin (c + 1)) :
    (univ.filter (fun i : Fin (m + 1) =>
      ((Fin.cons b y : Fin (m + 1 + 1) → Fin (c + 1)) i.castSucc : ℕ) +
        ((Fin.cons b y : Fin (m + 1 + 1) → Fin (c + 1)) i.succ : ℕ) = c)).card =
      (if (b : ℕ) + (y 0 : ℕ) = c then 1 else 0) +
        (univ.filter (fun i : Fin m => (y i.castSucc : ℕ) + (y i.succ : ℕ) = c)).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

lemma step (c : ℕ) (pr : ∀ m, (Fin (m + 1) → Fin (c + 1)) → ℕ)
    (hprs : ∀ m (b : Fin (c + 1)) (y : Fin (m + 1) → Fin (c + 1)),
      pr (m + 1) (Fin.cons b y : Fin (m + 1 + 1) → Fin (c + 1)) =
        (if (b : ℕ) + (y 0 : ℕ) = c then 1 else 0) + pr m y) (m : ℕ) :
    (univ.filter (fun x : Fin (m + 1 + 1) → Fin (c + 1) => pr (m + 1) x = 0)).card =
        c * (univ.filter (fun y : Fin (m + 1) → Fin (c + 1) => pr m y = 0)).card ∧
    (univ.filter (fun x : Fin (m + 1 + 1) → Fin (c + 1) => pr (m + 1) x = 1)).card =
        (univ.filter (fun y : Fin (m + 1) → Fin (c + 1) => pr m y = 0)).card +
          c * (univ.filter (fun y : Fin (m + 1) → Fin (c + 1) => pr m y = 1)).card := by
  have reindex : ∀ F : (Fin (m + 1 + 1) → Fin (c + 1)) → ℕ,
      ∑ x, F x = ∑ y : Fin (m + 1) → Fin (c + 1), ∑ b : Fin (c + 1),
        F (Fin.cons b y : Fin (m + 1 + 1) → Fin (c + 1)) := by
    intro F
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin (c + 1))) F,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  constructor
  · rw [Finset.card_filter, reindex]
    simp only [hprs, inner0]
    rw [Finset.card_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  · rw [Finset.card_filter, reindex]
    simp only [hprs, inner1, Finset.sum_add_distrib]
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp

lemma closed (c : ℕ) (pr : ∀ m, (Fin (m + 1) → Fin (c + 1)) → ℕ)
    (hpr0 : ∀ x : Fin (0 + 1) → Fin (c + 1), pr 0 x = 0)
    (hprs : ∀ m (b : Fin (c + 1)) (y : Fin (m + 1) → Fin (c + 1)),
      pr (m + 1) (Fin.cons b y : Fin (m + 1 + 1) → Fin (c + 1)) =
        (if (b : ℕ) + (y 0 : ℕ) = c then 1 else 0) + pr m y) :
    (univ.filter (fun x : Fin (0 + 1) → Fin (c + 1) => pr 0 x = 1)).card = 0 ∧
    ∀ m, (univ.filter (fun x : Fin (m + 1) → Fin (c + 1) => pr m x = 0)).card = (c + 1) * c ^ m ∧
      (univ.filter (fun x : Fin (m + 1 + 1) → Fin (c + 1) => pr (m + 1) x = 1)).card =
        (c + 1) * c ^ m * (m + 1) := by
  have base1 : (univ.filter (fun x : Fin (0 + 1) → Fin (c + 1) => pr 0 x = 1)).card = 0 := by
    simp [hpr0]
  have base0 : (univ.filter (fun x : Fin (0 + 1) → Fin (c + 1) => pr 0 x = 0)).card = c + 1 := by
    simp [hpr0]
  refine ⟨base1, fun m => ?_⟩
  induction m with
  | zero =>
    refine ⟨by rw [base0]; ring, ?_⟩
    rw [(step c pr hprs 0).2, base1, base0]
    ring
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [(step c pr hprs m).1, h0]
      ring
    · rw [(step c pr hprs (m + 1)).2, (step c pr hprs m).1, h0, h1]
      ring

lemma main' (pr : ∀ m, (Fin (m + 1) → Fin 6) → ℕ)
    (hpr : ∀ m x, pr m x =
      (univ.filter (fun i : Fin m => (x i.castSucc : ℕ) + (x i.succ : ℕ) = 5)).card)
    (a : ℕ → ℕ) (ha0 : a 0 = 0)
    (has : ∀ m, a (m + 1) = (univ.filter (fun x : Fin (m + 1) → Fin 6 => pr m x = 1)).card) :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 10 * a (n - 1) - 25 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 5 * PowerSeries.X) ^ 2 =
      6 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 6 * 5 ^ (n - 2) * (n - 1)) := by
  have hpr0 : ∀ x : Fin (0 + 1) → Fin (5 + 1), pr 0 x = 0 := fun x => by
    rw [hpr]
    simp
  have hprs : ∀ m (b : Fin (5 + 1)) (y : Fin (m + 1) → Fin (5 + 1)),
      pr (m + 1) (Fin.cons b y : Fin (m + 1 + 1) → Fin (5 + 1)) =
        (if (b : ℕ) + (y 0 : ℕ) = 5 then 1 else 0) + pr m y := fun m b y => by
    rw [hpr, hpr]
    exact pr_cons 5 m b y
  obtain ⟨hb, hcl⟩ := closed 5 pr hpr0 hprs
  have hA1 : a 1 = 0 := (has 0).trans hb
  have hA : ∀ m, a (m + 2) = 6 * 5 ^ m * (m + 1) := fun m => (has (m + 1)).trans (hcl m).2
  have hB : ∀ k, 5 * a (k + 1) = 6 * 5 ^ k * k := by
    intro k
    rcases k with _ | j
    · rw [hA1]
      simp
    · rw [hA j]
      ring
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    have h3 : (a (k + 3) : ℤ) = 6 * 5 ^ (k + 1) * ((k : ℤ) + 2) := by
      have := hA (k + 1)
      rw [show k + 1 + 2 = k + 3 by ring] at this
      rw [this]
      push_cast
      ring
    have h2 : (a (k + 2) : ℤ) = 6 * 5 ^ k * ((k : ℤ) + 1) := by
      rw [hA k]
      push_cast
      ring
    have h1 : 5 * (a (k + 1) : ℤ) = 6 * 5 ^ k * (k : ℤ) := by
      exact_mod_cast hB k
    linear_combination h3 - 10 * h2 + 5 * h1
  · have e8 : (PowerSeries.C (10 : ℚ) : PowerSeries ℚ) = 10 := map_ofNat _ 10
    have e16 : (PowerSeries.C (25 : ℚ) : PowerSeries ℚ) = 25 := map_ofNat _ 25
    have e5 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
    have key : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 5 * PowerSeries.X) ^ 2 =
        PowerSeries.mk (fun n => (a n : ℚ)) -
          PowerSeries.C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1) +
          PowerSeries.C (25 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2) := by
      rw [e8, e16]
      ring
    rw [key, ← e5]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | k
    · simp [ha0]
    · simp [ha0, hA1]
    · have h := hA 0
      simp [ha0, hA1, h]
    · have h3 : (a (k + 1 + 1 + 1) : ℚ) = 6 * 5 ^ (k + 1) * ((k : ℚ) + 2) := by
        have := hA (k + 1)
        rw [show k + 1 + 2 = k + 1 + 1 + 1 from rfl] at this
        rw [this]
        push_cast
        ring
      have h2 : (a (k + 2) : ℚ) = 6 * 5 ^ k * ((k : ℚ) + 1) := by
        rw [hA k]
        push_cast
        ring
      have h1 : 5 * (a (k + 1) : ℚ) = 6 * 5 ^ k * (k : ℚ) := by
        exact_mod_cast hB k
      have c1 : 1 ≤ k + 1 + 1 + 1 := by omega
      have c2 : 2 ≤ k + 1 + 1 + 1 := by omega
      have c3 : ¬ (k + 1 = 0) := by omega
      have e1 : k + 1 + 1 + 1 - 1 = k + 2 := by omega
      have e2 : k + 1 + 1 + 1 - 2 = k + 1 := by omega
      simp only [if_pos c1, if_pos c2, if_neg c3, e1, e2]
      linear_combination h3 - 10 * h2 + 5 * h1
  · intro n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [hA1]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [hA m, show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega]

end OMA.P269760

theorem OMA.solution : type_of% @OMA.S_oeis_a269760.main :=
  OMA.P269760.main' OMA.S_oeis_a269760.pairsTotallingFive (fun _ _ => rfl) OMA.S_oeis_a269760.a rfl (fun _ => rfl)
