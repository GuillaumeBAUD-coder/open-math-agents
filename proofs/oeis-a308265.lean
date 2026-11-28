import OMAStatements.S_oeis_a308265

namespace OMA.S_oeis_a308265

open Finset PowerSeries






/-- The number of partitions of n into 3 parts. -/
def p (n : ℕ) : ℕ := (tri n).card

/-- floor((n + 2) / 2). -/
def q (n : ℕ) : ℕ := (n + 2) / 2

/-- The largest parts of the partitions of n + 3 with smallest part 1. -/
def S (n : ℕ) : ℕ := ∑ b ∈ Icc 1 (q n), (n + 2 - b)

/-- Adding 1 to each part. -/
def shiftE : ℕ × ℕ × ℕ ↪ ℕ × ℕ × ℕ :=
  ⟨fun t => (t.1 + 1, t.2.1 + 1, t.2.2 + 1), by
    intro t t' h
    obtain ⟨x, y, z⟩ := t
    obtain ⟨x', y', z'⟩ := t'
    simp only [Prod.mk.injEq] at h ⊢
    omega⟩

/-- The partitions (1, b, n + 2 - b). -/
def onesE (n : ℕ) : ℕ ↪ ℕ × ℕ × ℕ :=
  ⟨fun b => (1, b, n + 2 - b), by
    intro b b' h
    simp only [Prod.mk.injEq] at h
    exact h.2.1⟩

lemma mem_tri (n x y z : ℕ) : (x, y, z) ∈ tri n ↔ 1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n := by
  simp only [tri, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨⟨by omega, by omega, by omega⟩, h⟩

lemma shiftE_apply (t : ℕ × ℕ × ℕ) : shiftE t = (t.1 + 1, t.2.1 + 1, t.2.2 + 1) := rfl

lemma onesE_apply (n b : ℕ) : onesE n b = (1, b, n + 2 - b) := rfl

lemma tri_succ3 (n : ℕ) : tri (n + 3) = (tri n).map shiftE ∪ (Icc 1 (q n)).map (onesE n) := by
  ext ⟨x, y, z⟩
  rw [Finset.mem_union, Finset.mem_map, Finset.mem_map, mem_tri]
  constructor
  · intro h
    by_cases hx : x = 1
    · right
      refine ⟨y, Finset.mem_Icc.2 ⟨by omega, by unfold q; omega⟩, ?_⟩
      have e : y + z = n + 2 := by omega
      rw [onesE_apply, hx, show n + 2 - y = z by omega]
    · left
      refine ⟨(x - 1, y - 1, z - 1), (mem_tri _ _ _ _).2 ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      simp only [shiftE_apply, Prod.mk.injEq]
      omega
  · rintro (⟨⟨x', y', z'⟩, ht, he⟩ | ⟨b, hb, he⟩)
    · rw [mem_tri] at ht
      simp only [shiftE_apply, Prod.mk.injEq] at he
      omega
    · rw [Finset.mem_Icc] at hb
      simp only [onesE_apply, Prod.mk.injEq] at he
      unfold q at hb
      omega

lemma disj (n : ℕ) : Disjoint ((tri n).map shiftE) ((Icc 1 (q n)).map (onesE n)) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  rw [Finset.mem_map] at ht ht'
  obtain ⟨⟨x1, y1, z1⟩, h1, rfl⟩ := ht
  obtain ⟨b, _, h⟩ := ht'
  rw [mem_tri] at h1
  simp only [shiftE_apply, onesE_apply, Prod.mk.injEq] at h
  omega

lemma a_succ3 (n : ℕ) : a (n + 3) = a n + p n + S n := by
  unfold a p S
  rw [tri_succ3, Finset.sum_union (disj n), Finset.sum_map, Finset.sum_map]
  have e1 : ∑ x ∈ tri n, (shiftE x).2.2 = ∑ x ∈ tri n, (x.2.2 + 1) := rfl
  have e2 : ∑ x ∈ Icc 1 (q n), (onesE n x).2.2 = ∑ b ∈ Icc 1 (q n), (n + 2 - b) := rfl
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]

lemma p_succ3 (n : ℕ) : p (n + 3) = p n + q n := by
  unfold p
  rw [tri_succ3, Finset.card_union_of_disjoint (disj n), Finset.card_map, Finset.card_map,
    Nat.card_Icc]
  omega

lemma small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

lemma sum_Icc_id (U : ℕ) : ∑ x ∈ Icc 1 U, (x : ℚ) = (U : ℚ) * (U + 1) / 2 := by
  induction U with
  | zero => simp
  | succ U ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma S_q (n : ℕ) : (S n : ℚ) = (q n : ℚ) * (n + 2) - (q n : ℚ) * (q n + 1) / 2 := by
  unfold S
  rw [Nat.cast_sum]
  have : ∀ b ∈ Icc 1 (q n), ((n + 2 - b : ℕ) : ℚ) = (n + 2 : ℚ) - b := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    rw [Nat.cast_sub (by unfold q at hb; omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    sum_Icc_id, nsmul_eq_mul]
  push_cast
  ring

/-- S as a quasi-polynomial in n = 2j + k. -/
lemma S_eval (j k : ℕ) : (S (2 * j + k) : ℚ) =
    ((j + q k : ℕ) : ℚ) * (2 * j + k + 2) - ((j + q k : ℕ) : ℚ) * ((j + q k : ℕ) + 1) / 2 := by
  rw [S_q, show q (2 * j + k) = j + q k by unfold q; omega]
  push_cast
  ring

/-- The power series of p, q, S. -/
noncomputable def P : ℚ⟦X⟧ := PowerSeries.mk fun n => (p n : ℚ)

noncomputable def Q : ℚ⟦X⟧ := PowerSeries.mk fun n => (q n : ℚ)

noncomputable def Ss : ℚ⟦X⟧ := PowerSeries.mk fun n => (S n : ℚ)

lemma h1 : A * (1 - X ^ 3) = (P + Ss) * X ^ 3 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mul_X_pow']
  simp only [A, P, Ss, coeff_mk, map_add]
  obtain ⟨h0, h1, h2, _⟩ := small
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show 3 ≤ m + 3 by omega, if_true, show m + 3 - 3 = m by omega, a_succ3]
    push_cast
    ring

lemma h2 : P * (1 - X ^ 3) = Q * X ^ 3 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mul_X_pow']
  simp only [P, Q, coeff_mk]
  obtain ⟨_, _, _, h0, h1, h2⟩ := small
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show 3 ≤ m + 3 by omega, if_true, show m + 3 - 3 = m by omega, p_succ3]
    push_cast
    ring

lemma h3 : Q * ((1 - X) * (1 - X ^ 2)) = 1 := by
  have e : Q * ((1 - X) * (1 - X ^ 2)) = Q - Q * X ^ 1 - Q * X ^ 2 + Q * X ^ 3 := by ring
  rw [e]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_one, Q, coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num [q]
  · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, if_false]
    have e1 : q n + q (n - 3) = q (n - 1) + q (n - 2) := by unfold q; omega
    have e2 : ((q n + q (n - 3) : ℕ) : ℚ) = ((q (n - 1) + q (n - 2) : ℕ) : ℚ) := by rw [e1]
    push_cast at e2
    linarith

lemma h4 : Ss * ((1 - X) * (1 - X ^ 2) ^ 2) = 1 + X + X ^ 2 := by
  have e : Ss * ((1 - X) * (1 - X ^ 2) ^ 2) =
      Ss - Ss * X ^ 1 - C (2 : ℚ) * (Ss * X ^ 2) + C (2 : ℚ) * (Ss * X ^ 3) + Ss * X ^ 4 -
        Ss * X ^ 5 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e' : (1 + X + X ^ 2 : ℚ⟦X⟧) = 1 + X ^ 1 + X ^ 2 := by ring
  rw [e, e']
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, Ss,
    coeff_mk]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp only [S_q] <;> norm_num [q]
  · obtain ⟨j, k, hk, rfl⟩ : ∃ j k, k < 2 ∧ n = 2 * j + (k + 5) :=
      ⟨(n - 5) / 2, (n - 5) % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    simp only [show 1 ≤ 2 * j + (k + 5) by omega, show 2 ≤ 2 * j + (k + 5) by omega,
      show 3 ≤ 2 * j + (k + 5) by omega, show 4 ≤ 2 * j + (k + 5) by omega,
      show 5 ≤ 2 * j + (k + 5) by omega, if_true, show 2 * j + (k + 5) ≠ 0 by omega,
      show 2 * j + (k + 5) ≠ 1 by omega, show 2 * j + (k + 5) ≠ 2 by omega, if_false]
    rw [show 2 * j + (k + 5) - 1 = 2 * j + (k + 4) by omega,
      show 2 * j + (k + 5) - 2 = 2 * j + (k + 3) by omega,
      show 2 * j + (k + 5) - 3 = 2 * j + (k + 2) by omega,
      show 2 * j + (k + 5) - 4 = 2 * j + (k + 1) by omega,
      show 2 * j + (k + 5) - 5 = 2 * j + k by omega,
      S_eval, S_eval, S_eval, S_eval, S_eval, S_eval]
    interval_cases k <;> norm_num [q] <;> push_cast <;> ring

lemma mul_den : A * den = num := by
  have e : den = (1 - X ^ 3) * ((1 - X ^ 3) * (1 - X ^ 2) ^ 2) := by unfold den; ring
  rw [e]
  unfold num
  linear_combination ((1 - X ^ 3) * (1 - X ^ 2) ^ 2) * h1 + (X ^ 3 * (1 - X ^ 2) ^ 2) * h2 +
    (X ^ 6 * (1 + X)) * h3 + (X ^ 3 * (1 + X + X ^ 2)) * h4

/-- a and p computed by the recursion. -/
def ap : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | 2 => (0, 0)
  | n + 3 => ((ap n).1 + (ap n).2 + S n, (ap n).2 + q n)

lemma ap_eq (n : ℕ) : ap n = (a n, p n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := small
    rcases n with _ | _ | _ | n
    · simp [ap, h0, h3]
    · simp [ap, h1, h4]
    · simp [ap, h2, h5]
    · rw [show n + 1 + 1 + 1 = n + 3 from rfl, ap, ih n (by omega), a_succ3, p_succ3]

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - 4 * a (n - 5) - a (n - 6) +
      2 * a (n - 7) + 2 * a (n - 8) - a (n - 10) := by
  have h := congrArg (coeff n) mul_den
  have eD : den = 1 - X ^ 2 - X ^ 2 - X ^ 3 - X ^ 3 + X ^ 4 + X ^ 5 + X ^ 5 + X ^ 5 + X ^ 5 +
      X ^ 6 - X ^ 7 - X ^ 7 - X ^ 8 - X ^ 8 + X ^ 10 := by unfold den; ring
  have eN : num = X ^ 3 + X ^ 4 + X ^ 4 + X ^ 5 + X ^ 5 + X ^ 5 + X ^ 6 + X ^ 6 + X ^ 6 +
      X ^ 7 + X ^ 7 := by unfold num; ring
  rw [eD, eN] at h
  have e2 : A * (1 - X ^ 2 - X ^ 2 - X ^ 3 - X ^ 3 + X ^ 4 + X ^ 5 + X ^ 5 + X ^ 5 + X ^ 5 +
      X ^ 6 - X ^ 7 - X ^ 7 - X ^ 8 - X ^ 8 + X ^ 10) = A - A * X ^ 2 - A * X ^ 2 - A * X ^ 3 -
      A * X ^ 3 + A * X ^ 4 + A * X ^ 5 + A * X ^ 5 + A * X ^ 5 + A * X ^ 5 + A * X ^ 6 -
      A * X ^ 7 - A * X ^ 7 - A * X ^ 8 - A * X ^ 8 + A * X ^ 10 := by ring
  rw [e2] at h
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk,
    show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
    show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 10 ≤ n by omega,
    if_true, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
    show n ≠ 7 by omega, if_false] at h
  have hq : (a n : ℚ) = 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - 4 * a (n - 5) - a (n - 6) +
      2 * a (n - 7) + 2 * a (n - 8) - a (n - 10) := by linarith
  exact_mod_cast hq

/-- Controls: the entry's data a(1..21). -/
theorem controls : (List.range 21).map (fun i => a (i + 1)) =
    [0, 0, 1, 2, 5, 9, 15, 22, 34, 45, 62, 81, 104, 129, 163, 195, 237, 282, 333, 387, 454] := by
  rw [show (fun i => a (i + 1)) = (fun i => (ap (i + 1)).1) from
    funext (fun i => by rw [ap_eq])]
  decide

/-- Barker's two conjectures. -/
theorem conjecture : A = num * den⁻¹ ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - 4 * a (n - 5) - a (n - 6) +
        2 * a (n - 7) + 2 * a (n - 8) - a (n - 10) := by
  refine ⟨?_, recurrence⟩
  have h : constantCoeff den ≠ 0 := by unfold den; simp
  rw [← mul_den, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

end OMA.S_oeis_a308265

theorem OMA.solution : type_of% @OMA.S_oeis_a308265.main :=
  OMA.S_oeis_a308265.conjecture
