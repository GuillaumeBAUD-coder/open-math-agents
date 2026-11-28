import OMAStatements.S_oeis_a269103

/-!
A269103 via a transfer argument on the first row. For an array with `m + 1` rows and first row
`r`, let `cnt269 m r k` count the arrays with exactly `k` adjacent pairs totalling three. Adding a
row on top adds `hr269 r` (the new horizontal pair) and `vr269 r s` (vertical pairs with the old
first row `s`). The counts for `k = 0, 1` depend only on whether `r` itself totals three, which
gives `a (m + 1) = 12 * 7^m + 12 * W0 m + 4 * W1 m` and the closed form
`7 * a (m + 2) = 60 * 7^m * (8m + 21)`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a269103

/-- A row of the array. -/
abbrev Row269 := Fin 2 → Fin 4

/-- 1 if the two entries of a row total three. -/
def hr269 (r : Row269) : ℕ := if (r 0 : ℕ) + (r 1 : ℕ) = 3 then 1 else 0

/-- The number of columns in which rows `r` and `s` total three. -/
def vr269 (r s : Row269) : ℕ :=
  (if (r 0 : ℕ) + (s 0 : ℕ) = 3 then 1 else 0) + (if (r 1 : ℕ) + (s 1 : ℕ) = 3 then 1 else 0)

theorem pairs269_cons (m : ℕ) (r : Row269) (y : Fin (m + 1) → Row269) :
    pairsTotallingThree (m + 1) (Fin.cons r y : Fin (m + 2) → Row269) =
      hr269 r + vr269 r (y 0) + pairsTotallingThree m y := by
  have hv : (∑ x : Fin (m + 1), ∑ j : Fin 2,
      (if (((Fin.cons r y : Fin (m + 2) → Row269) x.castSucc j : Fin 4) : ℕ) +
        (((Fin.cons r y : Fin (m + 2) → Row269) x.succ j : Fin 4) : ℕ) = 3 then 1 else 0)) =
      (∑ j : Fin 2, if (r j : ℕ) + (y 0 j : ℕ) = 3 then 1 else 0) +
        ∑ x : Fin m, ∑ j : Fin 2, if (y x.castSucc j : ℕ) + (y x.succ j : ℕ) = 3 then 1 else 0 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
  unfold pairsTotallingThree hr269 vr269
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hv, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_two]
  ring

/-- Arrays with `m + 1` rows, first row `r` and exactly `k` adjacent pairs totalling three. -/
def cnt269 (m : ℕ) (r : Row269) (k : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun y : Fin (m + 1) → Row269 => y 0 = r ∧ pairsTotallingThree m y = k)).card

theorem cnt269_succ (m : ℕ) (r : Row269) (k : ℕ) :
    cnt269 (m + 1) r k = ∑ s : Row269,
      if hr269 r + vr269 r s ≤ k then cnt269 m s (k - (hr269 r + vr269 r s)) else 0 := by
  unfold cnt269
  rw [Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row269).symm _
    (fun p => if (Fin.cons p.1 p.2 : Fin (m + 2) → Row269) 0 = r ∧
      pairsTotallingThree (m + 1) (Fin.cons p.1 p.2 : Fin (m + 2) → Row269) = k then 1 else 0)
    (fun x => by simp), Fintype.sum_prod_type]
  simp only [Fin.cons_zero, pairs269_cons]
  rw [Finset.sum_eq_single r]
  · have pt : ∀ y : Fin (m + 1) → Row269,
        (if r = r ∧ hr269 r + vr269 r (y 0) + pairsTotallingThree m y = k then 1 else 0) =
          ∑ s : Row269, if hr269 r + vr269 r s ≤ k then
            (if y 0 = s ∧ pairsTotallingThree m y = k - (hr269 r + vr269 r s) then 1 else 0)
            else 0 := by
      intro y
      rw [Finset.sum_eq_single (y 0)]
      · by_cases hc : hr269 r + vr269 r (y 0) ≤ k
        · rw [if_pos hc]
          by_cases hp : hr269 r + vr269 r (y 0) + pairsTotallingThree m y = k
          · rw [if_pos ⟨rfl, hp⟩, if_pos ⟨rfl, by omega⟩]
          · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp (by omega))]
        · rw [if_neg hc, if_neg (fun h => hc (by omega))]
      · intro s _ hs
        split_ifs with h1 h2
        · exact absurd h2.1.symm hs
        · rfl
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun y _ => pt y), Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hc
    · rw [Finset.card_filter]
    · exact Finset.sum_const_zero
  · intro b _ hb
    refine Finset.sum_eq_zero fun y _ => if_neg ?_
    rintro ⟨h, -⟩
    exact hb h
  · intro h
    exact absurd (Finset.mem_univ _) h


theorem cnt269_zero_zero : ∀ r : Row269, cnt269 0 r 0 = 1 - hr269 r := by
  decide +kernel

theorem cnt269_zero_one : ∀ r : Row269, cnt269 0 r 1 = hr269 r := by
  decide +kernel

theorem t269_a : ∀ r : Row269,
    (∑ s : Row269, if hr269 r + vr269 r s ≤ 0 then 1 - hr269 s else 0) = 7 * (1 - hr269 r) := by
  decide +kernel

theorem t269_b : ∀ r : Row269,
    (∑ s : Row269, if hr269 r + vr269 r s = 0 then 1 - hr269 s else 0) = 7 * (1 - hr269 r) := by
  decide +kernel

theorem t269_c : ∀ r : Row269,
    (∑ s : Row269, if hr269 r + vr269 r s = 0 then hr269 s else 0) = 2 * (1 - hr269 r) := by
  decide +kernel

theorem t269_d : ∀ r : Row269,
    (∑ s : Row269, if hr269 r + vr269 r s = 1 then 1 - hr269 s else 0) =
      4 * (1 - hr269 r) + 6 * hr269 r := by
  decide +kernel

theorem t269_e : (∑ r : Row269, (1 - hr269 r)) = 12 := by
  decide +kernel

theorem t269_f : (∑ r : Row269, hr269 r) = 4 := by
  decide +kernel

theorem hr269_le (r : Row269) : hr269 r ≤ 1 := by
  unfold hr269
  split_ifs <;> omega

/-- Arrays with exactly one pair totalling three, first row not totalling three. -/
def W1_269 : ℕ → ℕ
  | 0 => 1
  | m + 1 => 6 * 7 ^ m

/-- Arrays with exactly one pair totalling three, first row totalling three. -/
def W0_269 : ℕ → ℕ
  | 0 => 0
  | m + 1 => 7 * W0_269 m + 2 * W1_269 m + 4 * 7 ^ m

theorem cnt269_formula (m : ℕ) : ∀ r : Row269,
    cnt269 m r 0 = (1 - hr269 r) * 7 ^ m ∧
      cnt269 m r 1 = (1 - hr269 r) * W0_269 m + hr269 r * W1_269 m := by
  induction m with
  | zero =>
    intro r
    rw [cnt269_zero_zero, cnt269_zero_one]
    simp [W0_269, W1_269]
  | succ m ih =>
    intro r
    constructor
    · rw [cnt269_succ]
      have pt : ∀ s : Row269,
          (if hr269 r + vr269 r s ≤ 0 then cnt269 m s (0 - (hr269 r + vr269 r s)) else 0) =
            (if hr269 r + vr269 r s ≤ 0 then 1 - hr269 s else 0) * 7 ^ m := by
        intro s
        split_ifs with h
        · rw [show 0 - (hr269 r + vr269 r s) = 0 by omega, (ih s).1]
        · simp
      rw [Finset.sum_congr rfl (fun s _ => pt s), ← Finset.sum_mul, t269_a r]
      ring
    · rw [cnt269_succ]
      have pt : ∀ s : Row269,
          (if hr269 r + vr269 r s ≤ 1 then cnt269 m s (1 - (hr269 r + vr269 r s)) else 0) =
            (if hr269 r + vr269 r s = 0 then 1 - hr269 s else 0) * W0_269 m +
              (if hr269 r + vr269 r s = 0 then hr269 s else 0) * W1_269 m +
              (if hr269 r + vr269 r s = 1 then 1 - hr269 s else 0) * 7 ^ m := by
        intro s
        rcases Nat.lt_trichotomy (hr269 r + vr269 r s) 1 with hc | hc | hc
        · have hc0 : hr269 r + vr269 r s = 0 := by omega
          rw [if_pos (by omega), if_pos hc0, if_pos hc0, if_neg (by omega), hc0, (ih s).2]
          ring
        · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos hc, hc,
            (ih s).1]
          ring
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          ring
      rw [Finset.sum_congr rfl (fun s _ => pt s), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, t269_b r, t269_c r, t269_d r]
      simp only [W0_269, W1_269]
      ring

theorem a269_succ (m : ℕ) : a (m + 1) = ∑ r : Row269, (cnt269 m r 0 + cnt269 m r 1) := by
  simp only [a, cnt269, Finset.card_filter]
  have pt : ∀ x : Fin (m + 1) → Row269,
      (if pairsTotallingThree m x ≤ 1 then 1 else 0) =
        ∑ r : Row269, ((if x 0 = r ∧ pairsTotallingThree m x = 0 then 1 else 0) +
          (if x 0 = r ∧ pairsTotallingThree m x = 1 then 1 else 0)) := by
    intro x
    rw [Finset.sum_eq_single (x 0)]
    · rcases Nat.lt_trichotomy (pairsTotallingThree m x) 1 with h | h | h
      · rw [if_pos (by omega), if_pos ⟨rfl, by omega⟩, if_neg (fun h' => absurd h'.2 (by omega))]
      · rw [if_pos (by omega), if_neg (fun h' => absurd h'.2 (by omega)), if_pos ⟨rfl, h⟩]
      · rw [if_neg (by omega), if_neg (fun h' => absurd h'.2 (by omega)),
          if_neg (fun h' => absurd h'.2 (by omega))]
    · intro r _ hr
      rw [if_neg (fun h => hr h.1.symm), if_neg (fun h => hr h.1.symm)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun x _ => pt x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_add_distrib]

theorem a269_total (m : ℕ) : a (m + 1) = 12 * 7 ^ m + 12 * W0_269 m + 4 * W1_269 m := by
  have F := cnt269_formula m
  have h : ∀ r : Row269, cnt269 m r 0 + cnt269 m r 1 =
      (1 - hr269 r) * (7 ^ m + W0_269 m) + hr269 r * W1_269 m := by
    intro r
    rw [(F r).1, (F r).2]
    ring
  rw [a269_succ, Finset.sum_congr rfl (fun r _ => h r), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, t269_e, t269_f]
  ring

theorem W0_269_closed (m : ℕ) : (7 : ℤ) * W0_269 (m + 1) = 7 ^ m * (40 * m + 42) := by
  induction m with
  | zero => norm_num [W0_269, W1_269]
  | succ m ih =>
    have e : W0_269 (m + 1 + 1) = 7 * W0_269 (m + 1) + 2 * (6 * 7 ^ m) + 4 * 7 ^ (m + 1) := rfl
    rw [e]
    push_cast
    linear_combination 7 * ih

theorem a269_key (m : ℕ) : (7 : ℤ) * a (m + 2) = 60 * 7 ^ m * (8 * m + 21) := by
  rw [a269_total]
  have e : W1_269 (m + 1) = 6 * 7 ^ m := rfl
  rw [e]
  push_cast
  linear_combination 12 * W0_269_closed m

theorem a269_zero : a 0 = 0 := rfl

theorem a269_one : a 1 = 16 := by
  rw [a269_total]
  norm_num [W0_269, W1_269]

theorem a269_rec (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 14 * a (n - 1) - 49 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = (m + 1) + 2 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 = (m + 2) + 2 by omega]
  have k2 := a269_key (m + 2)
  have k1 := a269_key (m + 1)
  have k0 := a269_key m
  push_cast at k2 k1 k0
  have h7 : (7 : ℤ) * ((a (m + 2 + 2) : ℤ) - (14 * a (m + 1 + 2) - 49 * a (m + 2))) = 0 := by
    linear_combination k2 - 14 * k1 + 49 * k0
  have := mul_eq_zero.mp h7
  rcases this with h | h
  · norm_num at h
  · linarith

theorem a269_closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = 60 * 7 ^ ((n : ℤ) - 3) * (8 * n + 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have k := a269_key m
  have kq : (7 : ℚ) * a (m + 2) = 60 * 7 ^ m * (8 * m + 21) := by exact_mod_cast k
  have hz : ((m + 2 : ℕ) : ℤ) - 3 = (m : ℤ) - 1 := by push_cast; ring
  rw [hz, zpow_sub₀ (by norm_num : (7 : ℚ) ≠ 0), zpow_natCast, zpow_one]
  push_cast
  field_simp
  linear_combination kq

open PowerSeries in
theorem a269_gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X) ^ 2 =
    4 * X * (4 - 11 * X + X ^ 2) := by
  have key : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X) ^ 2 =
      C 1 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 0) -
        C 14 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) +
        C 49 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4 : ℚ⟦X⟧) * X * (4 - 11 * X + X ^ 2) =
      C 16 * X ^ 1 - C 44 * X ^ 2 + C 4 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have v2 : (a 2 : ℚ) = 180 := by
    have := a269_key 0
    norm_num at this
    exact_mod_cast (by omega : a 2 = 180)
  have v3 : (a 3 : ℚ) = 1740 := by
    have := a269_key 1
    norm_num at this
    exact_mod_cast (by omega : a 3 = 1740)
  by_cases hk : k < 4
  · interval_cases k <;> norm_num [a269_zero, a269_one, v2, v3]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have hr := a269_rec (j + 4) (by omega)
    have hq : (a (j + 4) : ℚ) = 14 * a (j + 4 - 1) - 49 * a (j + 4 - 2) := by exact_mod_cast hr
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show j + 4 - 0 = j + 4 by omega,
      show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
      if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a269103.main :=
  ⟨OMA.Helpers.a269_rec, OMA.Helpers.a269_gf, OMA.Helpers.a269_closed⟩
