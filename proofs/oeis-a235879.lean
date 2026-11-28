import OMAStatements.S_oeis_a235879
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on the 81 rows (Fin 4 -> Fin 3); arrays counted row by row via Fin.init/Fin.snoc.
-- Dual vectors u1..u3 tabulated and checked by decide +kernel, with u3 + 11 u1 = 6 u2 + 6 u0 per row, so
-- a(k+3) = 6a(k+2) - 11a(k+1) + 6a(k); closed form by induction from a1..a3, g.f. by coefficients.

namespace OMA.S_oeis_a235879

open PowerSeries

open Finset

abbrev St := Fin 4 → Fin 3

def ok (r s : St) : Prop :=
  ∀ j j' : Fin 4, j'.val = j.val + 1 → medEq (r j).val (r j').val (s j).val (s j').val = true

instance (r s : St) : Decidable (ok r s) := by unfold ok; infer_instance

def Gd (n : ℕ) (f : Fin n → St) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd n) := fun f => by unfold Gd; infer_instance

def w : ℕ → St → ℕ
  | 0, _ => 1
  | k + 1, y => ∑ x, if ok x y then w k x else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if ok x y then u j y else 0

def cnt (k : ℕ) (y : St) : ℕ :=
  ((univ : Finset (Fin (k + 1) → St)).filter
    (fun f => Gd (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → St) :
    Gd (k + 2) f ↔ Gd (k + 1) (Fin.init f) ∧
      ok (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · intro h
    exact ⟨fun i j hij => h _ _ (by simp [hij]), h _ _ (by simp)⟩
  · rintro ⟨h1, h3⟩
    intro i j hij
    by_cases hj : j.val < k + 1
    · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
      simpa [Fin.init] using this
    · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
      have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
      subst hj' hi'; exact h3

lemma cnt_zero (y : St) : cnt 0 y = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => y, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
  · rintro rfl; exact ⟨fun i j hij => by omega, rfl⟩

lemma cnt_succ (k : ℕ) (y : St) :
    cnt (k + 1) y = ∑ x, if ok x y then cnt k x else 0 := by
  have e : cnt (k + 1) y = ((univ : Finset (Fin (k + 1) → St)).filter
      (fun g => Gd (k + 1) g ∧ ok (g (Fin.last k)) y)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hg, hl⟩ := hf
      rw [gd_succ] at hg
      refine ⟨hg.1, ?_⟩
      have := hg.2; rw [hl] at this; simpa [Fin.init] using this
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      refine ⟨?_, by simp⟩
      rw [gd_succ]
      refine ⟨by simpa using hg.1, ?_⟩
      simpa using hg.2
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.2]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hg, hx⟩
    · rintro ⟨hg, hx⟩; exact ⟨⟨hg, hx ▸ h⟩, hx⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨⟨-, ha⟩, hx⟩; exact h (hx ▸ ha)

lemma cnt_eq (k : ℕ) (y : St) : cnt k y = w k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma a_w (k : ℕ) : a k = ∑ y, w k y := by
  simp only [← cnt_eq]
  unfold cnt a
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]; rfl

lemma dual (j k : ℕ) : ∑ y, w (k + j) y = ∑ x, w k x * u j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

def tb (L : List ℕ) (x : St) : ℕ :=
  L.getD ((x 0).val * 27 + (x 1).val * 9 + (x 2).val * 3 + (x 3).val) 0

def T1 : List ℕ := [3, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def T2 : List ℕ := [9, 4, 4, 4, 4, 1, 4, 1, 4, 4, 4, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4, 4, 4, 1, 4, 4, 1, 1, 1, 1, 4, 4, 1, 4, 9, 4, 1, 4, 4, 1, 1, 1, 1, 4, 4, 1, 4, 4, 4, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4, 4, 4, 1, 4, 1, 4, 4, 4, 4, 9]
def T3 : List ℕ := [27, 8, 8, 8, 8, 1, 8, 1, 8, 8, 8, 1, 8, 8, 1, 1, 1, 1, 8, 1, 8, 1, 1, 1, 8, 1, 8, 8, 8, 1, 8, 8, 1, 1, 1, 1, 8, 8, 1, 8, 27, 8, 1, 8, 8, 1, 1, 1, 1, 8, 8, 1, 8, 8, 8, 1, 8, 1, 1, 1, 8, 1, 8, 1, 1, 1, 1, 8, 8, 1, 8, 8, 8, 1, 8, 1, 8, 8, 8, 8, 27]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y, if ok x y then tb T1 y else 0) = tb T2 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y, if ok x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu2 (x : St) : u 2 x = tb T2 x := by
  show (∑ y, if ok x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

lemma hu3 (x : St) : u 3 x = tb T3 x := by
  show (∑ y, if ok x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x, tb T3 x + 11 * tb T1 x = 6 * tb T2 x + 6 := by decide +kernel

lemma arec (k : ℕ) : (a (k + 3) : ℤ) = 6 * a (k + 2) - 11 * a (k + 1) + 6 * a k := by
  rw [a_w, a_w, a_w, a_w, dual 3 k, dual 2 k, dual 1 k]
  have key : ∑ x, w k x * u 3 x + 11 * ∑ x, w k x * u 1 x =
      6 * ∑ x, w k x * u 2 x + 6 * ∑ x, w k x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    have := hT x
    rw [hu1, hu2, hu3]
    calc w k x * tb T3 x + 11 * (w k x * tb T1 x)
        = w k x * (tb T3 x + 11 * tb T1 x) := by ring
      _ = w k x * (6 * tb T2 x + 6) := by rw [this]
      _ = 6 * (w k x * tb T2 x) + 6 * w k x := by ring
  zify at key
  push_cast
  linarith

lemma v1 : a 1 = 129 := by
  have hd := dual 1 0
  rw [zero_add] at hd
  rw [a_w, hd]
  simp only [hu1, w, one_mul]; decide +kernel
lemma v2 : a 2 = 231 := by
  have hd := dual 2 0
  rw [zero_add] at hd
  rw [a_w, hd]
  simp only [hu2, w, one_mul]; decide +kernel
lemma v3 : a 3 = 453 := by
  have hd := dual 3 0
  rw [zero_add] at hd
  rw [a_w, hd]
  simp only [hu3, w, one_mul]; decide +kernel

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

lemma closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (12 + 7 * 2 ^ (1 + n) + 3 ^ n) := by
  have key : ∀ m : ℕ, ∀ k ≤ m, (a (k + 1) : ℚ) = 3 * (12 + 7 * 2 ^ (1 + (k + 1)) + 3 ^ (k + 1)) := by
    intro m
    induction m with
    | zero =>
      intro k hk; obtain rfl : k = 0 := by omega
      rw [v1]; norm_num
    | succ m ih =>
      intro k hk
      rcases (show k ≤ m ∨ k = m + 1 by omega) with hk | rfl
      · exact ih k hk
      · rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
        · rw [v2]; norm_num
        · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
          have hq : (a (j + 1 + 3) : ℚ) = 6 * a (j + 1 + 2) - 11 * a (j + 1 + 1) + 6 * a (j + 1) := by
            exact_mod_cast arec (j + 1)
          rcases (show j = 0 ∨ 1 ≤ j by omega) with rfl | hj
          · rw [v3]; norm_num
          · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
            have i1 := ih (i + 1 + 1) le_rfl
            have i2 := ih (i + 1) (by omega)
            have i3 := ih i (by omega)
            have hq' := arec (i + 1)
            have hq2 : (a (i + 1 + 3) : ℚ) = 6 * a (i + 1 + 2) - 11 * a (i + 1 + 1) + 6 * a (i + 1) := by
              exact_mod_cast hq'
            rw [show i + 1 + 1 + 1 + 1 = i + 1 + 3 by omega, hq2,
              show i + 1 + 2 = i + 1 + 1 + 1 by omega, i1, i2, i3]
            ring
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact key k k le_rfl

theorem main_proof :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        3 * X * (43 - 181 * X + 162 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (12 + 7 * 2 ^ (1 + n) + 3 ^ n) := by
  refine ⟨?_, closed⟩
  rw [show ((1 - X) * (1 - 2 * X) * (1 - 3 * X) : PowerSeries ℚ) =
      1 - PowerSeries.C (6:ℚ) * X + PowerSeries.C (11:ℚ) * X ^ 2 - PowerSeries.C (6:ℚ) * X ^ 3 by
        simp only [map_ofNat]; ring,
    show (3 * X * (43 - 181 * X + 162 * X ^ 2) : PowerSeries ℚ) =
      PowerSeries.C (129:ℚ) * X - PowerSeries.C (543:ℚ) * X ^ 2 + PowerSeries.C (486:ℚ) * X ^ 3 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
  · interval_cases n <;> simp [v1, v2, v3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have hq : (a (m + 4) : ℚ) = 6 * a (m + 3) - 11 * a (m + 2) + 6 * a (m + 1) := by
      exact_mod_cast arec (m + 1)
    simp [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega,
      show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega]
    rw [hq]; ring

end OMA.S_oeis_a235879

theorem OMA.solution : type_of% @OMA.S_oeis_a235879.main := OMA.S_oeis_a235879.main_proof
