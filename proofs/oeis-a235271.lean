import OMAStatements.S_oeis_a235271
import Mathlib

/-!
Rows are `Fin 2 → (Fin 5)`; `OK r x` is the block condition for consecutive rows `r, x`. With the
transfer operator `T f r = ∑ x, [OK r x] f x` and `E m = T^m 1`, appending a row gives
`a (L + m) = S L (E m)`. A linear identity between the `E m` holds on every row
(`decide +kernel`), which gives the recurrence of `a`; the generating function follows by
coefficient shifting and the closed form by induction, using `√ ^ 2 = `.
-/

namespace R235271
open OMA.S_oeis_a235271

abbrev Row := Fin 2 → (Fin 5)

abbrev OK (r x : Row) : Prop := validBlock (r 0) (r 1) (x 0) (x 1)

def vals : List (Fin 5) := List.finRange 5

theorem vals_sum (h : (Fin 5) → ℕ) : ∑ v : (Fin 5), h v = (vals.map h).sum := by
  exact Fin.sum_univ_def h

def rsum (g : Row → ℕ) : ℕ := (vals.map (fun a => (vals.map (fun b => g ![a, b])).sum)).sum

theorem rsum_eq (g : Row → ℕ) : ∑ x : Row, g x = rsum g := by
  have e : ∀ u v : (Fin 5), (piFinTwoEquiv fun _ => (Fin 5)).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => (Fin 5)).symm.sum_comp g, Fintype.sum_prod_type]
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

theorem card_eq (n : ℕ) : A235271 n = S n (fun _ => 1) := by
  rw [A235271, Finset.card_filter, ← (Equiv.curry (Fin (n + 1)) (Fin 2) (Fin 5)).symm.sum_comp]
  unfold S
  exact Finset.sum_congr rfl (fun B _ => if_congr Iff.rfl rfl rfl)

theorem a_E (L m : ℕ) : A235271 (L + m) = S L (E m) := (card_eq _).trans (iter m L)

theorem a_val (m : ℕ) : A235271 m = rsum (E m) := by
  have h := a_E 0 m
  rw [Nat.zero_add, S0, rsum_eq] at h
  exact h

theorem ident (r : Row) : E 5 r + 24 * E 1 r = 10 * E 3 r := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : (Fin 5), r = ![u, v] := ⟨r 0, r 1, by funext i; fin_cases i <;> rfl⟩
  revert u v
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 5) + 24 * S L (E 1) = 10 * S L (E 3) := by
  unfold S
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, OK (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact ident _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem a_rec (L : ℕ) : A235271 (L + 5) + 24 * A235271 (L + 1) = 10 * A235271 (L + 3) := by
  have h := rec_S L
  rw [← a_E, ← a_E, ← a_E] at h
  exact h

theorem a1 : A235271 1 = 40 := by
  rw [a_val]
  decide +kernel

theorem a2 : A235271 2 = 100 := by
  rw [a_val]
  decide +kernel

theorem a3 : A235271 3 = 208 := by
  rw [a_val]
  decide +kernel

theorem a4 : A235271 4 = 520 := by
  rw [a_val]
  decide +kernel

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A235271 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A235271 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235271 n : ℤ)) =
      4 * PowerSeries.X * (2 + 5 * PowerSeries.X) * (5 - 24 * PowerSeries.X ^ 2) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235271 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 40 + PowerSeries.X * Bs 2 := by rw [shiftB, a1]; norm_num
  have s2 : Bs 2 = 100 + PowerSeries.X * Bs 3 := by rw [shiftB, a2]; norm_num
  have s3 : Bs 3 = 208 + PowerSeries.X * Bs 4 := by rw [shiftB, a3]; norm_num
  have s4 : Bs 4 = 520 + PowerSeries.X * Bs 5 := by rw [shiftB, a4]; norm_num
  have R : Bs 5 + PowerSeries.C 24 * Bs 1 = PowerSeries.C 10 * Bs 3 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, map_zero]
    exact_mod_cast a_rec m
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - 10 * PowerSeries.X ^ 3) * s1 + (PowerSeries.X ^ 2 - 10 * PowerSeries.X ^ 4) * s2 + (PowerSeries.X ^ 3) * s3 + (PowerSeries.X ^ 4) * s4 + (PowerSeries.X ^ 5) * R

def hc : ℕ → ℕ
  | 0 => 10
  | 1 => 24
  | n + 2 => 6 * hc n

theorem hc_even (q : ℕ) : hc (2 * q) = 10 * 6 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by ring, hc.eq_3 (2 * q), ih]
    ring

theorem hc_odd (q : ℕ) : hc (2 * q + 1) = 24 * 6 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 2 by ring, hc.eq_3 (2 * q + 1), ih]
    ring

theorem key : ∀ n : ℕ, 1 ≤ n → (A235271 n : ℤ) = (-2) ^ n + 9 * 2 ^ n + (hc n : ℤ)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [a1]
    norm_num [hc]
  | 2, _ => by
    rw [a2]
    norm_num [hc]
  | 3, _ => by
    rw [a3]
    norm_num [hc]
  | 4, _ => by
    rw [a4]
    norm_num [hc]
  | n + 5, _ => by
    have i2 := key (n + 3) (by omega)
    have i4 := key (n + 1) (by omega)
    have hr := a_rec n
    have e5 : hc (n + 5) = 6 * hc (n + 3) := by
      rw [show n + 5 = n + 3 + 2 by omega, hc.eq_3 (n + 3)]
    have e3 : hc (n + 3) = 6 * hc (n + 1) := by
      rw [show n + 3 = n + 1 + 2 by omega, hc.eq_3 (n + 1)]
    have q5 : (-2 : ℤ) ^ (n + 5) = -32 * (-2) ^ n := by ring
    have q3 : (-2 : ℤ) ^ (n + 3) = -8 * (-2) ^ n := by ring
    have q1 : (-2 : ℤ) ^ (n + 1) = -2 * (-2) ^ n := by ring
    have t5 : (2 : ℤ) ^ (n + 5) = 32 * 2 ^ n := by ring
    have t3 : (2 : ℤ) ^ (n + 3) = 8 * 2 ^ n := by ring
    have t1 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

theorem rp6 (k : ℕ) : (6 : ℝ) ^ ((k : ℝ) - 1 / 2) * Real.sqrt 6 = 6 ^ k := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 6), Real.rpow_natCast, ← Real.sqrt_eq_rpow,
    div_mul_cancel₀ _ (by positivity)]

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (A235271 n : ℝ) =
      (-2 : ℝ) ^ n + 9 * (2 : ℝ) ^ n +
        (6 : ℝ) ^ ((1 / 2 : ℝ) * (-1 + (n : ℝ))) *
          (12 - 12 * (-1 : ℝ) ^ n + 5 * Real.sqrt 6 + 5 * (-1 : ℝ) ^ n * Real.sqrt 6) := by
  have hk := congrArg (Int.cast : ℤ → ℝ) (key n hn)
  push_cast at hk
  rw [hk]
  rcases Nat.even_or_odd n with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : (1 / 2 : ℝ) * (-1 + ((q + q : ℕ) : ℝ)) = ((q : ℕ) : ℝ) - 1 / 2 := by
      push_cast
      ring
    have hm : (-1 : ℝ) ^ (q + q) = 1 := Even.neg_one_pow ⟨q, rfl⟩
    rw [hq, hm, show q + q = 2 * q by ring, hc_even]
    have h1 := rp6 q
    push_cast
    linear_combination (-10) * h1
  · have hq : (1 / 2 : ℝ) * (-1 + ((2 * q + 1 : ℕ) : ℝ)) = ((q : ℕ) : ℝ) := by
      push_cast
      ring
    have hm : (-1 : ℝ) ^ (2 * q + 1) = -1 := Odd.neg_one_pow ⟨q, rfl⟩
    rw [hq, Real.rpow_natCast, hm, hc_odd]
    push_cast
    ring

end R235271

theorem OMA.solution : type_of% @OMA.S_oeis_a235271.main := ⟨R235271.ps, R235271.closed⟩
