import OMAStatements.S_oeis_a026200

/-!
Proof of Barker's conjectures for A026200.

Step n of the A026166 process (n >= 2) targets position L = n - floor((n-1)/2) first and
R = n + floor((n-1)/2) otherwise. For n = 2k, L = k + 1 and R = 3k - 1; for n = 2k + 1,
L = k + 1 and R = 3k + 1. An invariant of the partial sequences (`A26Inv`) shows:
* a position p with p = 0 mod 3 receives 2p - 2 (from step 2(p-1), always at L);
* a position p = 3k + 1 receives 2k + 1 (from the odd step, which always goes to R);
* a position p = 2 mod 3 receives either 2p - 2, or 2j with p = 3j - 1 and j not 2 mod 3.
Hence A026166(p) = 1 mod 3 exactly when p = 0 mod 3 or p = 1 mod 9. The positions of these terms
are 9m + 1, 9m + 3, 9m + 6, 9m + 9, so a(4m+1) = 2m + 1, a(4m+2) = 6m + 2, a(4m+3) = 6m + 4 and
a(4m+4) = 6m + 6. The recurrence and the generating function follow (the denominator is
(1 - x^4)^2).
-/

namespace OMA.Helpers

open OMA.S_oeis_a026200

/-- The invariant of the placement process after the numbers `1, ..., n` are placed. -/
def A26Inv (n : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧
  (∀ p, 3 ≤ p → p % 3 = 0 → f p = if 2 * p - 2 ≤ n then 2 * p - 2 else 0) ∧
  (∀ p, 4 ≤ p → p % 3 = 1 → f p = if (2 * p + 1) / 3 ≤ n then (2 * p + 1) / 3 else 0) ∧
  (∀ p, p % 3 = 2 → f p ≠ 0 → (f p = 2 * p - 2 ∨ (3 * f p = 2 * p + 2 ∧ (p + 1) / 3 % 3 ≠ 2))) ∧
  (∀ p, 1 ≤ p → 2 * p - 2 ≤ n → f p ≠ 0)

theorem a26_step_even (j : ℕ) (f : ℕ → ℕ) :
    step (2 * j + 2) f = if f (j + 2) = 0 then Function.update f (j + 2) (2 * j + 2)
      else Function.update f (3 * j + 2) (2 * j + 2) := by
  unfold step
  have h1 : 2 * j + 2 - (2 * j + 2 - 1) / 2 = j + 2 := by omega
  have h2 : 2 * j + 2 + (2 * j + 2 - 1) / 2 = 3 * j + 2 := by omega
  rw [h1, h2]

theorem a26_step_odd (j : ℕ) (f : ℕ → ℕ) :
    step (2 * j + 3) f = if f (j + 2) = 0 then Function.update f (j + 2) (2 * j + 3)
      else Function.update f (3 * j + 4) (2 * j + 3) := by
  unfold step
  have h1 : 2 * j + 3 - (2 * j + 3 - 1) / 2 = j + 2 := by omega
  have h2 : 2 * j + 3 + (2 * j + 3 - 1) / 2 = 3 * j + 4 := by omega
  rw [h1, h2]

theorem a26_inv_init : A26Inv 1 init := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp _
    simp only [init, if_neg (show p ≠ 1 by omega)]
    rw [if_neg (by omega)]
  · intro p hp _
    simp only [init, if_neg (show p ≠ 1 by omega)]
    rw [if_neg (by omega)]
  · intro p hp hne
    simp only [init, if_neg (show p ≠ 1 by omega)] at hne
    exact absurd rfl hne
  · intro p hp hp2
    have : p = 1 := by omega
    subst this
    simp [init]

theorem a26_inv_even (j : ℕ) (f : ℕ → ℕ) (h : A26Inv (2 * j + 1) f) :
    A26Inv (2 * j + 2) (step (2 * j + 2) f) := by
  obtain ⟨h0, h1, hb, hc, hd, he⟩ := h
  rw [a26_step_even]
  by_cases hL : f (j + 2) = 0
  · rw [if_pos hL]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_apply, if_neg (by omega), h0]
    · rw [Function.update_apply, if_neg (by omega), h1]
    · intro p hp3 hp0
      rw [Function.update_apply]
      split_ifs with hpL
      · omega
      · omega
      · rw [hb p hp3 hp0]
        split_ifs <;> omega
      · rw [hb p hp3 hp0]
        split_ifs <;> omega
    · intro p hp4 hp1
      rw [Function.update_apply]
      split_ifs with hpL
      · subst hpL
        have := hc (j + 2) hp4 hp1
        rw [hL] at this
        split_ifs at this <;> omega
      · subst hpL
        have := hc (j + 2) hp4 hp1
        rw [hL] at this
        split_ifs at this <;> omega
      · rw [hc p hp4 hp1]
        split_ifs <;> omega
      · rw [hc p hp4 hp1]
        split_ifs <;> omega
    · intro p hp2 hne
      rw [Function.update_apply] at hne ⊢
      split_ifs with hpL
      · left
        omega
      · rw [if_neg hpL] at hne
        exact hd p hp2 hne
    · intro p hp1 hp2
      rw [Function.update_apply]
      split_ifs with hpL
      · omega
      · exact he p hp1 (by omega)
  · rw [if_neg hL]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_apply, if_neg (by omega), h0]
    · rw [Function.update_apply, if_neg (by omega), h1]
    · intro p hp3 hp0
      rw [Function.update_apply, if_neg (by omega)]
      by_cases hpL : p = j + 2
      · subst hpL
        have := hb (j + 2) hp3 hp0
        rw [if_neg (by omega)] at this
        exact absurd this hL
      · rw [hb p hp3 hp0]
        split_ifs <;> omega
    · intro p hp4 hp1
      rw [Function.update_apply, if_neg (by omega), hc p hp4 hp1]
      split_ifs <;> omega
    · intro p hp2 hne
      rw [Function.update_apply] at hne ⊢
      split_ifs with hpR
      · right
        refine ⟨by omega, ?_⟩
        intro hk
        have := hb (j + 2) (by omega) (by omega)
        rw [if_neg (by omega)] at this
        exact hL this
      · rw [if_neg hpR] at hne
        exact hd p hp2 hne
    · intro p hp1 hp2
      rw [Function.update_apply]
      split_ifs with hpR
      · omega
      · by_cases hpL : p = j + 2
        · subst hpL
          exact hL
        · exact he p hp1 (by omega)

theorem a26_inv_odd (j : ℕ) (f : ℕ → ℕ) (h : A26Inv (2 * j + 2) f) :
    A26Inv (2 * j + 3) (step (2 * j + 3) f) := by
  obtain ⟨h0, h1, hb, hc, hd, he⟩ := h
  have hL : f (j + 2) ≠ 0 := he (j + 2) (by omega) (by omega)
  rw [a26_step_odd, if_neg hL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_apply, if_neg (by omega), h0]
  · rw [Function.update_apply, if_neg (by omega), h1]
  · intro p hp3 hp0
    rw [Function.update_apply, if_neg (by omega), hb p hp3 hp0]
    split_ifs <;> omega
  · intro p hp4 hp1
    rw [Function.update_apply]
    split_ifs with hpR
    · omega
    · omega
    · rw [hc p hp4 hp1]
      split_ifs <;> omega
    · rw [hc p hp4 hp1]
      split_ifs <;> omega
  · intro p hp2 hne
    rw [Function.update_apply, if_neg (by omega)] at hne ⊢
    exact hd p hp2 hne
  · intro p hp1 hp2
    rw [Function.update_apply]
    split_ifs with hpR
    · omega
    · exact he p hp1 (by omega)

theorem a26_inv_state : ∀ n, 1 ≤ n → A26Inv n (state n)
  | 0, h => absurd h (by omega)
  | 1, _ => a26_inv_init
  | n + 2, _ => by
    have ih := a26_inv_state (n + 1) (by omega)
    show A26Inv (n + 2) (step (n + 2) (state (n + 1)))
    have key : ∀ f, A26Inv (n + 1) f → A26Inv (n + 2) (step (n + 2) f) := by
      intro f hf
      rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
      · have e1 : n + 1 = 2 * j + 1 := by omega
        have e2 : n + 2 = 2 * j + 2 := by omega
        rw [e1] at hf
        rw [e2]
        exact a26_inv_even j f hf
      · have e1 : n + 1 = 2 * j + 2 := by omega
        have e2 : n + 2 = 2 * j + 3 := by omega
        rw [e1] at hf
        rw [e2]
        exact a26_inv_odd j f hf
    exact key _ ih

theorem a26_val0 (p : ℕ) (hp : 3 ≤ p) (h0 : p % 3 = 0) : A026166 p = 2 * p - 2 := by
  have := (a26_inv_state (2 * p) (by omega)).2.2.1 p hp h0
  unfold A026166
  rw [this, if_pos (by omega)]

theorem a26_val1 (p : ℕ) (h1 : p % 3 = 1) : A026166 p = (2 * p + 1) / 3 := by
  have hI := a26_inv_state (2 * p) (by omega)
  unfold A026166
  by_cases hp : p = 1
  · subst hp
    rw [hI.2.1]
  · rw [hI.2.2.2.1 p (by omega) h1, if_pos (by omega)]

theorem a26_pred (p : ℕ) : (1 ≤ p ∧ A026166 p % 3 = 1) ↔ (1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)) := by
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨hp, ?_⟩
    have hI := a26_inv_state (2 * p) (by omega)
    have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · left
      exact hr
    · rw [a26_val1 p hr] at hm
      right
      omega
    · exfalso
      have hne := hI.2.2.2.2.2 p hp (by omega)
      have hd := hI.2.2.2.2.1 p hr hne
      unfold A026166 at hm
      omega
  · rintro ⟨hp, hm⟩
    refine ⟨hp, ?_⟩
    rcases hm with hm | hm
    · rw [a26_val0 p (by omega) hm]
      omega
    · rw [a26_val1 p (by omega)]
      omega

/-- The positions of the terms that are `1 mod 3`. -/
def A26Pos (p : ℕ) : Prop := 1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)

instance : DecidablePred A26Pos := fun p =>
  inferInstanceAs (Decidable (1 ≤ p ∧ (p % 3 = 0 ∨ p % 9 = 1)))

theorem a26_cnt (m : ℕ) : Nat.count A26Pos (9 * m + 1) = 4 * m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have e : 9 * (m + 1) + 1 = 9 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    rw [e]
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, Nat.count_succ, Nat.count_succ,
      Nat.count_succ, Nat.count_succ, Nat.count_succ, Nat.count_succ, ih]
    rw [if_pos (show A26Pos (9 * m + 1) by unfold A26Pos; omega),
      if_neg (show ¬ A26Pos (9 * m + 1 + 1) by unfold A26Pos; omega),
      if_pos (show A26Pos (9 * m + 1 + 1 + 1) by unfold A26Pos; omega),
      if_neg (show ¬ A26Pos (9 * m + 1 + 1 + 1 + 1) by unfold A26Pos; omega),
      if_neg (show ¬ A26Pos (9 * m + 1 + 1 + 1 + 1 + 1) by unfold A26Pos; omega),
      if_pos (show A26Pos (9 * m + 1 + 1 + 1 + 1 + 1 + 1) by unfold A26Pos; omega),
      if_neg (show ¬ A26Pos (9 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1) by unfold A26Pos; omega),
      if_neg (show ¬ A26Pos (9 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) by unfold A26Pos; omega),
      if_pos (show A26Pos (9 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) by unfold A26Pos; omega)]
    omega

theorem a26_nth (m : ℕ) :
    Nat.nth A26Pos (4 * m) = 9 * m + 1 ∧ Nat.nth A26Pos (4 * m + 1) = 9 * m + 3 ∧
    Nat.nth A26Pos (4 * m + 2) = 9 * m + 6 ∧ Nat.nth A26Pos (4 * m + 3) = 9 * m + 9 := by
  have c0 := a26_cnt m
  have p1 : A26Pos (9 * m + 1) := by unfold A26Pos; omega
  have n2 : ¬ A26Pos (9 * m + 2) := by unfold A26Pos; omega
  have p3 : A26Pos (9 * m + 3) := by unfold A26Pos; omega
  have n4 : ¬ A26Pos (9 * m + 4) := by unfold A26Pos; omega
  have n5 : ¬ A26Pos (9 * m + 5) := by unfold A26Pos; omega
  have p6 : A26Pos (9 * m + 6) := by unfold A26Pos; omega
  have n7 : ¬ A26Pos (9 * m + 7) := by unfold A26Pos; omega
  have n8 : ¬ A26Pos (9 * m + 8) := by unfold A26Pos; omega
  have p9 : A26Pos (9 * m + 9) := by unfold A26Pos; omega
  have c3 : Nat.count A26Pos (9 * m + 3) = 4 * m + 1 := by
    rw [show 9 * m + 3 = 9 * m + 2 + 1 by ring, Nat.count_succ, if_neg n2,
      show 9 * m + 2 = 9 * m + 1 + 1 by ring, Nat.count_succ, if_pos p1, c0]
  have c6 : Nat.count A26Pos (9 * m + 6) = 4 * m + 2 := by
    rw [show 9 * m + 6 = 9 * m + 5 + 1 by ring, Nat.count_succ, if_neg n5,
      show 9 * m + 5 = 9 * m + 4 + 1 by ring, Nat.count_succ, if_neg n4,
      show 9 * m + 4 = 9 * m + 3 + 1 by ring, Nat.count_succ, if_pos p3, c3]
  have c9 : Nat.count A26Pos (9 * m + 9) = 4 * m + 3 := by
    rw [show 9 * m + 9 = 9 * m + 8 + 1 by ring, Nat.count_succ, if_neg n8,
      show 9 * m + 8 = 9 * m + 7 + 1 by ring, Nat.count_succ, if_neg n7,
      show 9 * m + 7 = 9 * m + 6 + 1 by ring, Nat.count_succ, if_pos p6, c6]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← c0]; exact Nat.nth_count p1
  · rw [← c3]; exact Nat.nth_count p3
  · rw [← c6]; exact Nat.nth_count p6
  · rw [← c9]; exact Nat.nth_count p9

theorem a26_pred_eq : (fun p => 1 ≤ p ∧ A026166 p % 3 = 1) = A26Pos := by
  funext p
  exact propext (a26_pred p)

theorem a26_formula (m : ℕ) :
    a (4 * m + 1) = 2 * m + 1 ∧ a (4 * m + 2) = 6 * m + 2 ∧
    a (4 * m + 3) = 6 * m + 4 ∧ a (4 * m + 4) = 6 * m + 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := a26_nth m
  unfold a s
  rw [a26_pred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 4 * m + 1 - 1 = 4 * m by omega, h1, a26_val1 _ (by omega)]
    omega
  · rw [show 4 * m + 2 - 1 = 4 * m + 1 by omega, h2, a26_val0 _ (by omega) (by omega)]
    omega
  · rw [show 4 * m + 3 - 1 = 4 * m + 2 by omega, h3, a26_val0 _ (by omega) (by omega)]
    omega
  · rw [show 4 * m + 4 - 1 = 4 * m + 3 by omega, h4, a26_val0 _ (by omega) (by omega)]
    omega

theorem a26_rec (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 2 * a (n - 4) - a (n - 8) := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * (m + 2) + r + 1 :=
    ⟨(n - 1) / 4 - 2, (n - 1) % 4, by omega, by omega⟩
  have e1 : 4 * (m + 2) + r + 1 - 4 = 4 * (m + 1) + r + 1 := by omega
  have e2 : 4 * (m + 2) + r + 1 - 8 = 4 * m + r + 1 := by omega
  rw [e1, e2]
  obtain ⟨a1, a2, a3, a4⟩ := a26_formula (m + 2)
  obtain ⟨b1, b2, b3, b4⟩ := a26_formula (m + 1)
  obtain ⟨c1, c2, c3, c4⟩ := a26_formula m
  interval_cases r
  · rw [show 4 * (m + 2) + 0 + 1 = 4 * (m + 2) + 1 by ring, a1,
      show 4 * (m + 1) + 0 + 1 = 4 * (m + 1) + 1 by ring, b1,
      show 4 * m + 0 + 1 = 4 * m + 1 by ring, c1]
    push_cast
    ring
  · rw [show 4 * (m + 2) + 1 + 1 = 4 * (m + 2) + 2 by ring, a2,
      show 4 * (m + 1) + 1 + 1 = 4 * (m + 1) + 2 by ring, b2,
      show 4 * m + 1 + 1 = 4 * m + 2 by ring, c2]
    push_cast
    ring
  · rw [show 4 * (m + 2) + 2 + 1 = 4 * (m + 2) + 3 by ring, a3,
      show 4 * (m + 1) + 2 + 1 = 4 * (m + 1) + 3 by ring, b3,
      show 4 * m + 2 + 1 = 4 * m + 3 by ring, c3]
    push_cast
    ring
  · rw [show 4 * (m + 2) + 3 + 1 = 4 * (m + 2) + 4 by ring, a4,
      show 4 * (m + 1) + 3 + 1 = 4 * (m + 1) + 4 by ring, b4,
      show 4 * m + 3 + 1 = 4 * m + 4 by ring, c4]
    push_cast
    ring

theorem a26_recQ (n : ℕ) (hn : 8 < n) : (a n : ℚ) - 2 * a (n - 4) + a (n - 8) = 0 := by
  have h := a26_rec n hn
  have h' : ((a n : ℤ) : ℚ) = ((2 * (a (n - 4) : ℤ) - a (n - 8) : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  rw [h']
  ring

open PowerSeries in
theorem a26_gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 * (1 + PowerSeries.X ^ 2) ^ 2) =
      PowerSeries.X * (1 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hden : ((1 : ℚ⟦X⟧) - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2 = 1 - X ^ 4 - X ^ 4 + X ^ 8 := by
    ring
  have hrhs : (X : ℚ⟦X⟧) * (1 + 2 * X + 4 * X ^ 2 + 6 * X ^ 3 + X ^ 4 + 4 * X ^ 5 + 2 * X ^ 6) =
      C (1 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 +
        C (1 : ℚ) * X ^ 5 + C (4 : ℚ) * X ^ 6 + C (2 : ℚ) * X ^ 7 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hden, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  obtain ⟨a1, a2, a3, a4⟩ := a26_formula 0
  obtain ⟨b1, b2, b3, b4⟩ := a26_formula 1
  norm_num at a1 a2 a3 a4 b1 b2 b3 b4
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp
  · norm_num [a1]
  · norm_num [a2]
  · norm_num [a3]
  · norm_num [a4]
  · norm_num [a1, b1]
  · norm_num [a2, b2]
  · norm_num [a3, b3]
  · norm_num [a4, b4]
  · simp only [show ¬ (j + 9 = 0) by omega, show 4 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show ¬ (j + 9 - 4 = 0) by omega, show ¬ (j + 9 - 8 = 0) by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, if_true, if_false]
    have := a26_recQ (j + 9) (by omega)
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a026200.main :=
  ⟨OMA.Helpers.a26_gf, OMA.Helpers.a26_rec⟩
