import OMAStatements.S_oeis_a235895
import Mathlib

/-!
Rows are `Fin 2 → (Fin 3)`; `OK r x` is the block condition for consecutive rows `r, x`. With the
transfer operator `T f r = ∑ x, [OK r x] f x` and `E m = T^m 1`, appending a row gives
`a (L + m) = S L (E m)`. A linear identity between the `E m` holds on every row
(`decide +kernel`), which gives the recurrence of `a`; the generating function follows by
coefficient shifting and the closed form by induction, using `√17 ^ 2 = 17`.
-/

namespace R235895
open OMA.S_oeis_a235895

abbrev Row := Fin 2 → (Fin 3)

abbrev OK (r x : Row) : Prop := validBlock (r 0) (r 1) (x 0) (x 1)

def vals : List (Fin 3) := List.finRange 3

theorem vals_sum (h : (Fin 3) → ℕ) : ∑ v : (Fin 3), h v = (vals.map h).sum := by
  exact Fin.sum_univ_def h

def rsum (g : Row → ℕ) : ℕ := (vals.map (fun a => (vals.map (fun b => g ![a, b])).sum)).sum

theorem rsum_eq (g : Row → ℕ) : ∑ x : Row, g x = rsum g := by
  have e : ∀ u v : (Fin 3), (piFinTwoEquiv fun _ => (Fin 3)).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => (Fin 3)).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [e, vals_sum]
  rfl

def T (f : Row → ℕ) (r : Row) : ℕ := rsum (fun x => if OK r x then f x else 0)

def E : ℕ → Row → ℕ
  | 0 => fun _ => 1
  | m + 1 => T (E m)

def S (L : ℕ) (f : Row → ℕ) : ℕ :=
  ∑ A : Fin (L + 1) → Row,
    if (∀ i : Fin L, OK (A i.castSucc) (A i.succ)) then f (A (Fin.last L)) else 0

theorem valid_snoc {L : ℕ} (w : Fin (L + 1) → Row) (x : Row) :
    (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ)) ↔
      (∀ i : Fin L, OK (w i.castSucc) (w i.succ)) ∧ OK (w (Fin.last L)) x := by
  have h1 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc = w i.castSucc :=
    fun i => by rw [Fin.snoc_castSucc]
  have h2 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.succ = w i.succ :=
    fun i => by rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  have h3 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).castSucc = w (Fin.last L) := by
    rw [Fin.snoc_castSucc]
  have h4 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ = x := Fin.snoc_last ..
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      rwa [h1, h2] at hi
    · have hl := h (Fin.last L)
      rwa [h3, h4] at hl
  · rintro ⟨hw, hx⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [h1, h2]
      exact hw j
    · rw [h3, h4]
      exact hx

theorem step_w {L : ℕ} (w : Fin (L + 1) → Row) (f : Row → ℕ) :
    (∑ x : Row, if (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ))
      then f (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1))) else 0) =
    if (∀ i : Fin L, OK (w i.castSucc) (w i.succ)) then T f (w (Fin.last L)) else 0 := by
  rw [T, ← rsum_eq]
  by_cases hw : ∀ i : Fin L, OK (w i.castSucc) (w i.succ)
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : OK (w (Fin.last L)) x
    · rw [if_pos ((valid_snoc w x).2 ⟨hw, hx⟩), if_pos hx, Fin.snoc_last]
    · rw [if_neg (fun h => hx ((valid_snoc w x).1 h).2), if_neg hx]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hw ((valid_snoc w x).1 h).1))

theorem pull (L : ℕ) (f : Row → ℕ) : S (L + 1) f = S L (T f) := by
  have he : S (L + 1) f = ∑ p : Row × (Fin (L + 1) → Row),
      if (∀ i : Fin (L + 1), OK (Fin.snoc (α := fun _ => Row) p.2 p.1 i.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ))
      then f (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1))) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Row)
      (fun A : Fin (L + 1 + 1) → Row =>
        if (∀ i : Fin (L + 1), OK (A i.castSucc) (A i.succ))
        then f (A (Fin.last (L + 1))) else 0)).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  unfold S
  exact Finset.sum_congr rfl (fun w _ => step_w w f)

theorem iter (m : ℕ) : ∀ L, S (L + m) (fun _ => 1) = S L (E m) := by
  induction m with
  | zero => intro L; rfl
  | succ m ih =>
    intro L
    rw [show L + (m + 1) = L + 1 + m by omega, ih (L + 1)]
    exact pull L (E m)

theorem S0 (f : Row → ℕ) : S 0 f = ∑ r, f r := by
  rw [← (Equiv.funUnique (Fin 1) Row).sum_comp f]
  unfold S
  refine Fintype.sum_congr _ _ (fun A => ?_)
  have h0 : ∀ i : Fin 0, OK (A i.castSucc) (A i.succ) := fun i => Fin.elim0 i
  exact (if_pos h0).trans rfl

theorem card_eq (n : ℕ) : A235895 n = S n (fun _ => 1) := by
  rw [A235895, Finset.card_filter, ← (Equiv.curry (Fin (n + 1)) (Fin 2) (Fin 3)).symm.sum_comp]
  unfold S
  exact Finset.sum_congr rfl (fun B _ => if_congr Iff.rfl rfl rfl)

theorem a_E (L m : ℕ) : A235895 (L + m) = S L (E m) := (card_eq _).trans (iter m L)

theorem a_val (m : ℕ) : A235895 m = rsum (E m) := by
  have h := a_E 0 m
  rw [Nat.zero_add, S0, rsum_eq] at h
  exact h

theorem ident (r : Row) : E 3 r + 10 * E 1 r + 8 * E 0 r = 7 * E 2 r := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : (Fin 3), r = ![u, v] := ⟨r 0, r 1, by funext i; fin_cases i <;> rfl⟩
  revert u v
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 3) + 10 * S L (E 1) + 8 * S L (E 0) = 7 * S L (E 2) := by
  unfold S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, OK (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact ident _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem a_rec (L : ℕ) : A235895 (L + 4) + 10 * A235895 (L + 2) + 8 * A235895 (L + 1) = 7 * A235895 (L + 3) := by
  have h := rec_S (L + 1)
  rw [← a_E, ← a_E, ← a_E, ← a_E] at h
  exact h

theorem a1 : A235895 1 = 33 := by
  rw [a_val]
  decide +kernel

theorem a2 : A235895 2 = 125 := by
  rw [a_val]
  decide +kernel

theorem a3 : A235895 3 = 473 := by
  rw [a_val]
  decide +kernel

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A235895 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A235895 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - 4 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235895 n : ℤ)) =
      PowerSeries.X * (33 - 106 * PowerSeries.X - 72 * PowerSeries.X ^ 2) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235895 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 33 + PowerSeries.X * Bs 2 := by rw [shiftB, a1]; norm_num
  have s2 : Bs 2 = 125 + PowerSeries.X * Bs 3 := by rw [shiftB, a2]; norm_num
  have s3 : Bs 3 = 473 + PowerSeries.X * Bs 4 := by rw [shiftB, a3]; norm_num
  have R : Bs 4 + PowerSeries.C 10 * Bs 2 + PowerSeries.C 8 * Bs 1 = PowerSeries.C 7 * Bs 3 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_zero]
    exact_mod_cast a_rec m
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - 7 * PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3) * s1 + (PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3) * s2 + (PowerSeries.X ^ 3) * s3 + (PowerSeries.X ^ 4) * R

theorem hD : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem key : ∀ n : ℕ, 1 ≤ n → (A235895 n : ℝ) * Real.sqrt 17 = (2⁻¹ : ℝ) ^ (n + 1) * ((3 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) + (3 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17)) + (4 : ℝ) ^ (1 + n) * Real.sqrt 17
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [a1]
    push_cast
    ring
  | 2, _ => by
    rw [a2]
    push_cast
    linear_combination (((-5 : ℝ) / 4) * Real.sqrt 17) * hD
  | 3, _ => by
    rw [a3]
    push_cast
    linear_combination ((-8 : ℝ) * Real.sqrt 17) * hD
  | n + 4, _ => by
    have i1 := key (n + 3) (by omega)
    have i2 := key (n + 2) (by omega)
    have i3 := key (n + 1) (by omega)
    have hr := a_rec n
    have hr' := congrArg (fun z : ℕ => (z : ℝ)) hr
    push_cast at hr'
    linear_combination (Real.sqrt 17) * hr' + (7) * i1 + (-10) * i2 + (-8) * i3 + (-((2⁻¹ : ℝ) ^ ((n + 1) + 1) * ((3 - Real.sqrt 17) ^ (n + 1) * (-19 + 5 * Real.sqrt 17) * (((-5 : ℝ) / 8) + ((-1 : ℝ) / 8) * Real.sqrt 17)) + (2⁻¹ : ℝ) ^ ((n + 1) + 1) * ((3 + Real.sqrt 17) ^ (n + 1) * (19 + 5 * Real.sqrt 17) * (((-5 : ℝ) / 8) + ((1 : ℝ) / 8) * Real.sqrt 17)))) * hD

theorem hz (n : ℕ) : (2 : ℝ) ^ (-1 - (n : ℤ)) = (2⁻¹ : ℝ) ^ (n + 1) := by
  rw [show -1 - (n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, inv_pow]

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (A235895 n : ℝ) =
      (4 : ℝ) ^ (1 + n) +
        ((2 : ℝ) ^ (-1 - (n : ℤ)) *
          ((3 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
           (3 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17 := by
  have hs : Real.sqrt 17 ≠ 0 := by positivity
  rw [hz]
  apply mul_right_cancel₀ hs
  rw [key n hn, add_mul, div_mul_cancel₀ _ hs]
  ring

end R235895

theorem OMA.solution : type_of% @OMA.S_oeis_a235895.main := ⟨R235895.ps, R235895.closed⟩
