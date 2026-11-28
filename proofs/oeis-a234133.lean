import OMAStatements.S_oeis_a234133
import Mathlib

/-!
Rows are `Fin 2 → (Fin 4)`; `OK r x` is the block condition for consecutive rows `r, x`. With the
transfer operator `T f r = ∑ x, [OK r x] f x` and `E m = T^m 1`, appending a row gives
`a (L + m) = S L (E m)`. A linear identity between the `E m` holds on every row
(`decide +kernel`), which gives the recurrence of `a`; the generating function follows by
coefficient shifting and the closed form by induction, using `√ ^ 2 = `.
-/

namespace R234133
open OMA.S_oeis_a234133

abbrev Row := Fin 2 → (Fin 4)

abbrev OK (r x : Row) : Prop := validBlock (r 0) (r 1) (x 0) (x 1)

def vals : List (Fin 4) := List.finRange 4

theorem vals_sum (h : (Fin 4) → ℕ) : ∑ v : (Fin 4), h v = (vals.map h).sum := by
  exact Fin.sum_univ_def h

def rsum (g : Row → ℕ) : ℕ := (vals.map (fun a => (vals.map (fun b => g ![a, b])).sum)).sum

theorem rsum_eq (g : Row → ℕ) : ∑ x : Row, g x = rsum g := by
  have e : ∀ u v : (Fin 4), (piFinTwoEquiv fun _ => (Fin 4)).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => (Fin 4)).symm.sum_comp g, Fintype.sum_prod_type]
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

theorem card_eq (n : ℕ) : A234133 n = S n (fun _ => 1) := by
  rw [A234133, Finset.card_filter, ← (Equiv.curry (Fin (n + 1)) (Fin 2) (Fin 4)).symm.sum_comp]
  unfold S
  exact Finset.sum_congr rfl (fun B _ => if_congr Iff.rfl rfl rfl)

theorem a_E (L m : ℕ) : A234133 (L + m) = S L (E m) := (card_eq _).trans (iter m L)

theorem a_val (m : ℕ) : A234133 m = rsum (E m) := by
  have h := a_E 0 m
  rw [Nat.zero_add, S0, rsum_eq] at h
  exact h

theorem ident (r : Row) : E 4 r + 16 * E 1 r = 2 * E 3 r + 8 * E 2 r := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : (Fin 4), r = ![u, v] := ⟨r 0, r 1, by funext i; fin_cases i <;> rfl⟩
  revert u v
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 4) + 16 * S L (E 1) = 2 * S L (E 3) + 8 * S L (E 2) := by
  unfold S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, OK (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact ident _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem a_rec (L : ℕ) : A234133 (L + 4) + 16 * A234133 (L + 1) = 2 * A234133 (L + 3) + 8 * A234133 (L + 2) := by
  have h := rec_S L
  rw [← a_E, ← a_E, ← a_E, ← a_E] at h
  exact h

theorem a1 : A234133 1 = 32 := by
  rw [a_val]
  decide +kernel

theorem a2 : A234133 2 = 80 := by
  rw [a_val]
  decide +kernel

theorem a3 : A234133 3 = 192 := by
  rw [a_val]
  decide +kernel

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A234133 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A234133 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234133 n : ℤ)) =
      16 * PowerSeries.X * (2 + PowerSeries.X - 14 * PowerSeries.X ^ 2) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234133 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 32 + PowerSeries.X * Bs 2 := by rw [shiftB, a1]; norm_num
  have s2 : Bs 2 = 80 + PowerSeries.X * Bs 3 := by rw [shiftB, a2]; norm_num
  have s3 : Bs 3 = 192 + PowerSeries.X * Bs 4 := by rw [shiftB, a3]; norm_num
  have R : Bs 4 + PowerSeries.C 16 * Bs 1 = PowerSeries.C 2 * Bs 3 + PowerSeries.C 8 * Bs 2 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_zero]
    exact_mod_cast a_rec m
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - 2 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3) * s1 + (PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3) * s2 + (PowerSeries.X ^ 3) * s3 + (PowerSeries.X ^ 4) * R

def hc : ℕ → ℕ
  | 0 => 6
  | 1 => 16
  | n + 2 => 8 * hc n

theorem hc_even (q : ℕ) : hc (2 * q) = 6 * 8 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by ring, hc.eq_3 (2 * q), ih]
    ring

theorem hc_odd (q : ℕ) : hc (2 * q + 1) = 16 * 8 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 2 by ring, hc.eq_3 (2 * q + 1), ih]
    ring

theorem key : ∀ n : ℕ, 1 ≤ n → A234133 n = 2 ^ (3 + n) + hc n
  | 0, h => absurd h (by norm_num)
  | 1, _ => a1.trans (by decide)
  | 2, _ => a2.trans (by decide)
  | 3, _ => a3.trans (by decide)
  | n + 4, _ => by
    have i1 := key (n + 3) (by omega)
    have i2 := key (n + 2) (by omega)
    have i3 := key (n + 1) (by omega)
    have hr := a_rec n
    have e2 : hc (n + 2) = 8 * hc (n + 0) := by
      rw [show n + 2 = n + 0 + 2 by omega, hc.eq_3 (n + 0)]
    have e3 : hc (n + 3) = 8 * hc (n + 1) := by
      rw [show n + 3 = n + 1 + 2 by omega, hc.eq_3 (n + 1)]
    have e4 : hc (n + 4) = 8 * hc (n + 2) := by
      rw [show n + 4 = n + 2 + 2 by omega, hc.eq_3 (n + 2)]
    have p1 : 2 ^ (3 + (n + 1)) = 2 * 2 ^ (3 + n) := by ring
    have p2 : 2 ^ (3 + (n + 2)) = 4 * 2 ^ (3 + n) := by ring
    have p3 : 2 ^ (3 + (n + 3)) = 8 * 2 ^ (3 + n) := by ring
    have p4 : 2 ^ (3 + (n + 4)) = 16 * 2 ^ (3 + n) := by ring
    omega

theorem rp (k : ℕ) : (2 : ℝ) ^ ((k : ℝ) - 1 / 2) * Real.sqrt 2 = 2 ^ k := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, ← Real.sqrt_eq_rpow,
    div_mul_cancel₀ _ (by positivity)]

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (A234133 n : ℝ) =
      (2 : ℝ) ^ (3 + n) +
        (2 : ℝ) ^ (-(1 : ℝ) / 2 + (3 * (n : ℝ)) / 2) *
          (4 - 4 * (-1 : ℝ) ^ n + 3 * Real.sqrt 2 + 3 * (-1 : ℝ) ^ n * Real.sqrt 2) := by
  rw [key n hn]
  rcases Nat.even_or_odd n with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : -(1 : ℝ) / 2 + (3 * ((q + q : ℕ) : ℝ)) / 2 = ((3 * q : ℕ) : ℝ) - 1 / 2 := by
      push_cast
      ring
    have hm : (-1 : ℝ) ^ (q + q) = 1 := Even.neg_one_pow ⟨q, rfl⟩
    rw [hq, hm, show q + q = 2 * q by ring, hc_even]
    have h1 := rp (3 * q)
    have h8 : (2 : ℝ) ^ (3 * q) = 8 ^ q := by rw [pow_mul]; norm_num
    push_cast at h1 ⊢
    linear_combination (-6) * h1 + (-6) * h8
  · have hq : -(1 : ℝ) / 2 + (3 * ((2 * q + 1 : ℕ) : ℝ)) / 2 = ((3 * q + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have hm : (-1 : ℝ) ^ (2 * q + 1) = -1 := Odd.neg_one_pow ⟨q, rfl⟩
    rw [hq, Real.rpow_natCast, hm, hc_odd]
    have h8 : (2 : ℝ) ^ (3 * q + 1) = 2 * 8 ^ q := by rw [pow_succ, pow_mul]; ring
    push_cast
    linear_combination (-8) * h8

end R234133

theorem OMA.solution : type_of% @OMA.S_oeis_a234133.main := ⟨R234133.ps, R234133.closed⟩
