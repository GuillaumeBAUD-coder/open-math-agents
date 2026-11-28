import OMAStatements.S_oeis_a235510
import Mathlib

/-!
Rows are `Fin 2 → Bool`; `OK r x` is the block condition for consecutive rows `r, x`. With the
transfer operator `T f r = ∑ x, [OK r x] f x` and `E m = T^m 1`, appending a row gives
`a (L + m) = S L (E m)`. A linear identity between the `E m` holds on every row
(`decide +kernel`), which gives the recurrence of `a`; the generating function follows by
coefficient shifting and the closed form by induction, using `√17 ^ 2 = 17`.
-/

namespace R235510
open OMA.S_oeis_a235510

abbrev Row := Fin 2 → Bool

abbrev C3 (p q x : Row) : Prop := blockMaxMin (p 0) (p 1) (q 0) (q 1) ≤ blockMaxMin (q 0) (q 1) (x 0) (x 1)

def vals : List Bool := [false, true]

theorem vals_sum (h : Bool → ℕ) : ∑ v : Bool, h v = (vals.map h).sum := by
  rw [Fintype.sum_bool]
  simp [vals, add_comm]

def rsum (g : Row → ℕ) : ℕ := (vals.map (fun a => (vals.map (fun b => g ![a, b])).sum)).sum

theorem rsum_eq (g : Row → ℕ) : ∑ x : Row, g x = rsum g := by
  have e : ∀ u v : Bool, (piFinTwoEquiv fun _ => Bool).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [e, vals_sum]
  rfl

def T (f : Row → Row → ℕ) (p q : Row) : ℕ := rsum (fun x => if C3 p q x then f q x else 0)

def E : ℕ → Row → Row → ℕ
  | 0 => fun _ _ => 1
  | m + 1 => T (E m)

def S (L : ℕ) (f : Row → Row → ℕ) : ℕ :=
  ∑ A : Fin (L + 1 + 1) → Row,
    if (∀ i : Fin L, C3 (A i.castSucc.castSucc) (A i.succ.castSucc) (A i.succ.succ))
    then f (A (Fin.last L).castSucc) (A (Fin.last (L + 1))) else 0

theorem valid_snoc {L : ℕ} (w : Fin (L + 1 + 1) → Row) (x : Row) :
    (∀ i : Fin (L + 1), C3 (Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ.succ)) ↔
      (∀ i : Fin L, C3 (w i.castSucc.castSucc) (w i.succ.castSucc) (w i.succ.succ)) ∧
        C3 (w (Fin.last L).castSucc) (w (Fin.last (L + 1))) x := by
  have h1 : ∀ j : Fin L, Fin.snoc (α := fun _ => Row) w x j.castSucc.castSucc.castSucc =
      w j.castSucc.castSucc := fun j => by rw [Fin.snoc_castSucc]
  have h2 : ∀ j : Fin L, Fin.snoc (α := fun _ => Row) w x j.castSucc.succ.castSucc =
      w j.succ.castSucc := fun j => by rw [Fin.snoc_castSucc, Fin.succ_castSucc]
  have h3 : ∀ j : Fin L, Fin.snoc (α := fun _ => Row) w x j.castSucc.succ.succ =
      w j.succ.succ := fun j => by rw [Fin.succ_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  have h4 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).castSucc.castSucc =
      w (Fin.last L).castSucc := by rw [Fin.snoc_castSucc]
  have h5 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ.castSucc =
      w (Fin.last (L + 1)) := by rw [Fin.snoc_castSucc, Fin.succ_last]
  have h6 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ.succ = x := by
    rw [Fin.succ_last, Fin.succ_last, Fin.snoc_last]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      rwa [h1, h2, h3] at hi
    · have hl := h (Fin.last L)
      rwa [h4, h5, h6] at hl
  · rintro ⟨hw, hx⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [h1, h2, h3]
      exact hw j
    · rw [h4, h5, h6]
      exact hx

theorem step_w {L : ℕ} (w : Fin (L + 1 + 1) → Row) (f : Row → Row → ℕ) :
    (∑ x : Row, if (∀ i : Fin (L + 1), C3 (Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ.succ))
      then f (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1)).castSucc)
        (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1 + 1))) else 0) =
    if (∀ i : Fin L, C3 (w i.castSucc.castSucc) (w i.succ.castSucc) (w i.succ.succ))
    then T f (w (Fin.last L).castSucc) (w (Fin.last (L + 1))) else 0 := by
  rw [T, ← rsum_eq]
  by_cases hw : ∀ i : Fin L, C3 (w i.castSucc.castSucc) (w i.succ.castSucc) (w i.succ.succ)
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : C3 (w (Fin.last L).castSucc) (w (Fin.last (L + 1))) x
    · rw [if_pos ((valid_snoc w x).2 ⟨hw, hx⟩), if_pos hx, Fin.snoc_last, Fin.snoc_castSucc]
    · rw [if_neg (fun h => hx ((valid_snoc w x).1 h).2), if_neg hx]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hw ((valid_snoc w x).1 h).1))

theorem pull (L : ℕ) (f : Row → Row → ℕ) : S (L + 1) f = S L (T f) := by
  have he : S (L + 1) f = ∑ p : Row × (Fin (L + 1 + 1) → Row),
      if (∀ i : Fin (L + 1), C3 (Fin.snoc (α := fun _ => Row) p.2 p.1 i.castSucc.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ.succ))
      then f (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1)).castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1 + 1))) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Row)
      (fun A : Fin (L + 1 + 1 + 1) → Row =>
        if (∀ i : Fin (L + 1), C3 (A i.castSucc.castSucc) (A i.succ.castSucc) (A i.succ.succ))
        then f (A (Fin.last (L + 1)).castSucc) (A (Fin.last (L + 1 + 1))) else 0)).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  unfold S
  exact Finset.sum_congr rfl (fun w _ => step_w w f)

theorem iter (m : ℕ) : ∀ L, S (L + m) (fun _ _ => 1) = S L (E m) := by
  induction m with
  | zero => intro L; rfl
  | succ m ih =>
    intro L
    rw [show L + (m + 1) = L + 1 + m by omega, ih (L + 1)]
    exact pull L (E m)

theorem S0 (f : Row → Row → ℕ) : S 0 f = rsum (fun p => rsum (fun q => f p q)) := by
  have e : ∀ u v : Row, (piFinTwoEquiv fun _ => Row).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  unfold S
  rw [← (piFinTwoEquiv fun _ => Row).symm.sum_comp, Fintype.sum_prod_type]
  simp only [e, ← rsum_eq]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  have h0 : ∀ i : Fin 0, C3 (![p, q] i.castSucc.castSucc) (![p, q] i.succ.castSucc)
      (![p, q] i.succ.succ) := fun i => Fin.elim0 i
  exact (if_pos h0).trans rfl

theorem card_eq (L : ℕ) : A235510 (L + 1) = S L (fun _ _ => 1) := by
  rw [A235510, Finset.card_filter, ← (Equiv.curry (Fin (L + 1 + 1)) (Fin 2) Bool).symm.sum_comp]
  unfold S
  exact Finset.sum_congr rfl (fun B _ => if_congr Iff.rfl rfl rfl)

theorem a_E (L m : ℕ) : A235510 (L + m + 1) = S L (E m) := (card_eq _).trans (iter m L)

theorem a_val (m : ℕ) : A235510 (m + 1) = rsum (fun p => rsum (fun q => E m p q)) := by
  have h := a_E 0 m
  rw [Nat.zero_add, S0] at h
  exact h

theorem ident (p q : Row) : E 5 p q + 6 * E 2 p q = 4 * E 4 p q + E 1 p q + 2 * E 0 p q := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : Bool, p = ![u, v] := ⟨p 0, p 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨u', v', rfl⟩ : ∃ u v : Bool, q = ![u, v] := ⟨q 0, q 1, by funext i; fin_cases i <;> rfl⟩
  revert u v u' v'
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 5) + 6 * S L (E 2) = 4 * S L (E 4) + S L (E 1) + 2 * S L (E 0) := by
  unfold S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, C3 (A i.castSucc.castSucc) (A i.succ.castSucc) (A i.succ.succ)
  · simp only [if_pos hA]
    exact ident _ _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem a_rec (L : ℕ) : A235510 (L + 6) + 6 * A235510 (L + 3) = 4 * A235510 (L + 5) + A235510 (L + 2) + 2 * A235510 (L + 1) := by
  have h := rec_S L
  rw [← a_E, ← a_E, ← a_E, ← a_E, ← a_E] at h
  exact h

theorem a1 : A235510 1 = 16 := (a_val 0).trans (by decide +kernel)

theorem a2 : A235510 2 = 58 := (a_val 1).trans (by decide +kernel)

theorem a3 : A235510 3 = 209 := (a_val 2).trans (by decide +kernel)

theorem a4 : A235510 4 = 746 := (a_val 3).trans (by decide +kernel)

theorem a5 : A235510 5 = 2660 := (a_val 4).trans (by decide +kernel)

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A235510 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A235510 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235510 n : ℤ)) =
      PowerSeries.X * (16 - 6 * PowerSeries.X - 23 * PowerSeries.X ^ 2 +
        6 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235510 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 16 + PowerSeries.X * Bs 2 := by rw [shiftB, a1]; norm_num
  have s2 : Bs 2 = 58 + PowerSeries.X * Bs 3 := by rw [shiftB, a2]; norm_num
  have s3 : Bs 3 = 209 + PowerSeries.X * Bs 4 := by rw [shiftB, a3]; norm_num
  have s4 : Bs 4 = 746 + PowerSeries.X * Bs 5 := by rw [shiftB, a4]; norm_num
  have s5 : Bs 5 = 2660 + PowerSeries.X * Bs 6 := by rw [shiftB, a5]; norm_num
  have R : Bs 6 + PowerSeries.C 6 * Bs 3 = PowerSeries.C 4 * Bs 5 + Bs 2 + PowerSeries.C 2 * Bs 1 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_zero]
    exact_mod_cast a_rec m
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - 4 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) * s1 + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 5) * s2 + (PowerSeries.X ^ 3 - 4 * PowerSeries.X ^ 4) * s3 + (PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 5) * s4 + (PowerSeries.X ^ 5) * s5 + (PowerSeries.X ^ 6) * R

theorem hD : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem key : ∀ n : ℕ, 1 ≤ n → (A235510 n : ℝ) = ((1 : ℝ) / 544) * (2⁻¹ : ℝ) ^ (n + 1) * ((3 - Real.sqrt 17) ^ n * (2533 - 611 * Real.sqrt 17) + (3 + Real.sqrt 17) ^ n * (2533 + 611 * Real.sqrt 17)) + -((221 : ℝ) / 544) + -((68 : ℝ) / 544) * (-1 : ℝ) ^ n + -((68 : ℝ) / 544) * (1 + ((n : ℕ) : ℝ))
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [a1]
    push_cast
    linear_combination (((-611 : ℝ) / 1088)) * hD
  | 2, _ => by
    rw [a2]
    push_cast
    linear_combination (((-6199 : ℝ) / 2176)) * hD
  | 3, _ => by
    rw [a3]
    push_cast
    linear_combination (((-49681 : ℝ) / 4352) + ((-611 : ℝ) / 4352) * Real.sqrt 17 ^ 2) * hD
  | 4, _ => by
    rw [a4]
    push_cast
    linear_combination (((-370475 : ℝ) / 8704) + ((-9865 : ℝ) / 8704) * Real.sqrt 17 ^ 2) * hD
  | 5, _ => by
    rw [a5]
    push_cast
    linear_combination (((-2688689 : ℝ) / 17408) + ((-25843 : ℝ) / 4352) * Real.sqrt 17 ^ 2 + ((-611 : ℝ) / 17408) * Real.sqrt 17 ^ 4) * hD
  | n + 6, _ => by
    have i1 := key (n + 5) (by omega)
    have i3 := key (n + 3) (by omega)
    have i4 := key (n + 2) (by omega)
    have i5 := key (n + 1) (by omega)
    have hr := a_rec n
    have hr' := congrArg (fun z : ℕ => (z : ℝ)) hr
    push_cast at hr'
    push_cast at *
    linear_combination (1) * hr' + (4) * i1 + (-6) * i3 + (1) * i4 + (2) * i5 + (-(((1 : ℝ) / 544) * (2⁻¹ : ℝ) ^ ((n + 1) + 1) * ((3 - Real.sqrt 17) ^ (n + 1) * (2533 - 611 * Real.sqrt 17) * (((5 : ℝ) / 32) + ((-11 : ℝ) / 32) * Real.sqrt 17 + ((7 : ℝ) / 32) * Real.sqrt 17 ^ 2 + ((-1 : ℝ) / 32) * Real.sqrt 17 ^ 3)) + ((1 : ℝ) / 544) * (2⁻¹ : ℝ) ^ ((n + 1) + 1) * ((3 + Real.sqrt 17) ^ (n + 1) * (2533 + 611 * Real.sqrt 17) * (((5 : ℝ) / 32) + ((11 : ℝ) / 32) * Real.sqrt 17 + ((7 : ℝ) / 32) * Real.sqrt 17 ^ 2 + ((1 : ℝ) / 32) * Real.sqrt 17 ^ 3)))) * hD

theorem hz (n : ℕ) : (2 : ℝ) ^ (-1 - (n : ℤ)) = (2⁻¹ : ℝ) ^ (n + 1) := by
  rw [show -1 - (n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (A235510 n : ℝ) =
      (1 / 544 : ℝ) *
        (-221 - 68 * (-1 : ℝ) ^ n +
         (2 : ℝ) ^ (-1 - (n : ℤ)) *
           ((2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
            (3 + Real.sqrt 17) ^ n * (2533 + 611 * Real.sqrt 17)) -
         68 * (1 + (n : ℝ))) := by
  rw [hz, key n hn]
  ring

end R235510

theorem OMA.solution : type_of% @OMA.S_oeis_a235510.main := ⟨R235510.ps, R235510.closed⟩
