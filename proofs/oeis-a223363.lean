import OMAStatements.S_oeis_a223363
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix. a(k+1) = sum over end vertices of w k y, where w counts walks (bijection by
-- removing the last entry, Fin.init / Fin.snoc). With dual vectors u j (walks of j steps from x),
-- a(k+1+j) = sum_x w k x * u j x, and u3 + 4 u1 + 8 u0 = 6 u2 holds at all 21 vertices (decide +kernel).
-- This gives a(n+3) = 6a(n+2) - 4a(n+1) - 8a(n); the g.f. follows by comparing coefficients, and the
-- closed form (roots 2, 2-2*sqrt 2, 2+2*sqrt 2) by strong induction.

namespace OMA.P_oeis_a223363

open OMA.S_oeis_a223363
open PowerSeries Finset

def w : ℕ → Fin 21 → ℕ
  | 0, _ => 1
  | k + 1, y => ∑ x, if adj x y then w k x else 0

def u : ℕ → Fin 21 → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if adj x y then u j y else 0

def Gd (n : ℕ) (f : Fin n → Fin 21) : Prop := ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd n) := fun f => by unfold Gd; infer_instance

def cnt (k : ℕ) (y : Fin 21) : ℕ :=
  ((univ : Finset (Fin (k + 1) → Fin 21)).filter (fun f => Gd (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → Fin 21) :
    Gd (k + 2) f ↔ Gd (k + 1) (Fin.init f) ∧ adj (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · intro h
    refine ⟨fun i j hij => h _ _ (by simp [hij]), h _ _ (by simp)⟩
  · rintro ⟨h1, h2⟩ i j hij
    by_cases hj : j.val < k + 1
    · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
      simpa [Fin.init] using this
    · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
      have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
      subst hj' hi'; exact h2

lemma cnt_zero (y : Fin 21) : cnt 0 y = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => y, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
  · rintro rfl; exact ⟨fun i j hij => by omega, rfl⟩

lemma cnt_succ (k : ℕ) (y : Fin 21) : cnt (k + 1) y = ∑ x, if adj x y then cnt k x else 0 := by
  have e : cnt (k + 1) y = ((univ : Finset (Fin (k + 1) → Fin 21)).filter
      (fun g => Gd (k + 1) g ∧ adj (g (Fin.last k)) y)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
      obtain ⟨hg, hl⟩ := hf
      rw [gd_succ] at hg
      refine ⟨hg.1, ?_⟩
      have := hg.2; rw [hl] at this; simpa [Fin.init] using this
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
      refine ⟨?_, by simp⟩
      rw [gd_succ]
      refine ⟨by simpa using hg.1, ?_⟩
      simpa using hg.2
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      rw [← hf.2]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → Fin 21 => g (Fin.last k))
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

lemma cnt_eq (k : ℕ) (y : Fin 21) : cnt k y = w k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma a_succ (k : ℕ) : a (k + 1) = ∑ y, w k y := by
  simp only [← cnt_eq]
  unfold cnt a
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → Fin 21 => g (Fin.last k))
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
    have hs : adj x y ↔ adj y x := by unfold adj; tauto
    by_cases h : adj x y
    · have h' : adj y x := hs.mp h
      simp [h, h']
    · have h' : ¬ adj y x := fun h' => h (hs.mpr h')
      simp [h, h']

set_option maxRecDepth 100000 in
lemma hU : ∀ x : Fin 21, u 3 x + 4 * u 1 x + 8 * u 0 x = 6 * u 2 x := by decide +kernel

lemma arec (k : ℕ) : (a (k + 4) : ℤ) = 6 * a (k + 3) - 4 * a (k + 2) - 8 * a (k + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, show k + 3 = k + 3 by rfl]
  have d3 := dual 3 k
  have d2 := dual 2 k
  have d1 := dual 1 k
  have d0 := dual 0 k
  rw [show k + 0 = k by rfl] at d0
  have key : ∑ x, w k x * u 3 x + 4 * ∑ x, w k x * u 1 x + 8 * ∑ x, w k x * u 0 x
      = 6 * ∑ x, w k x * u 2 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    have := hU x
    calc w k x * u 3 x + 4 * (w k x * u 1 x) + 8 * (w k x * u 0 x)
        = w k x * (u 3 x + 4 * u 1 x + 8 * u 0 x) := by ring
      _ = w k x * (6 * u 2 x) := by rw [this]
      _ = 6 * (w k x * u 2 x) := by ring
  rw [show k + 3 = k + 3 by rfl] at d3
  rw [d3, d2, d1, d0]
  have : (∑ x, w k x * u 3 x : ℕ) + 4 * ∑ x, w k x * u 1 x + 8 * ∑ x, w k x * u 0 x
      = 6 * ∑ x, w k x * u 2 x := key
  zify at this
  push_cast
  linarith

lemma v1 : a 1 = 21 := by rw [a_succ]; decide
lemma v2 : a 2 = 90 := by rw [a_succ]; decide +kernel
lemma v3 : a 3 = 420 := by rw [a_succ]; decide +kernel

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2)) = 3 * X * (7 - 12 * X - 12 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (3 / 2) * (2 ^ n - (2 - 2 * Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
        (2 : ℝ) ^ ((1 : ℝ) / 2 + n) * (1 + Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n) := by
  refine ⟨?_, ?_⟩
  · rw [show ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2) : PowerSeries ℚ) =
        1 - PowerSeries.C (6:ℚ) * X + PowerSeries.C (4:ℚ) * X ^ 2 + PowerSeries.C (8:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring,
      show (3 * X * (7 - 12 * X - 12 * X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (21:ℚ) * X - PowerSeries.C (36:ℚ) * X ^ 2 - PowerSeries.C (36:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v1, v2, v3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hq : (a (m + 4) : ℚ) = 6 * a (m + 3) - 4 * a (m + 2) - 8 * a (m + 1) := by
        exact_mod_cast arec m
      simp [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        show m + 4 - 3 = m + 1 by omega,
        show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega]
      rw [hq]; ring
  · have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hr : ∀ n : ℕ, (2 : ℝ) ^ ((1 : ℝ) / 2 + n) = Real.sqrt 2 * 2 ^ n := by
      intro n
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]
    set s := Real.sqrt 2
    have key : ∀ m : ℕ, ∀ k ≤ m, (a (k + 1) : ℝ) =
        (3 / 2) * (2 ^ (k + 1) - (2 - 2 * s) ^ (k + 1) * (-1 + s) +
          (1 + s) * (2 * (1 + s)) ^ (k + 1)) := by
      intro m
      induction m with
      | zero =>
        intro k hk; obtain rfl : k = 0 := by omega
        rw [v1]; push_cast; linear_combination (-6 : ℝ) * hs
      | succ m ih =>
        intro k hk
        rcases (show k ≤ m ∨ k = m + 1 by omega) with hk | rfl
        · exact ih k hk
        · rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
          · rw [v2]; push_cast; linear_combination (-36 : ℝ) * hs
          · rw [v3]; push_cast; linear_combination (-24 * s ^ 2 - 192 : ℝ) * hs
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
            have hq : (a (j + 4) : ℝ) = 6 * a (j + 3) - 4 * a (j + 2) - 8 * a (j + 1) := by
              exact_mod_cast arec j
            have i1 := ih (j + 2) le_rfl
            have i2 := ih (j + 1) (by omega)
            have i3 := ih j (by omega)
            rw [show j + 2 + 1 = j + 3 by omega] at i1
            rw [show j + 1 + 1 = j + 2 by omega] at i2
            rw [show j + 2 + 1 + 1 = j + 4 by omega, hq, i1, i2, i3]
            have r1 : (2 - 2 * s) ^ 3 = 6 * (2 - 2 * s) ^ 2 - 4 * (2 - 2 * s) - 8 := by
              linear_combination (-8 * s) * hs
            have r2 : (2 * (1 + s)) ^ 3 = 6 * (2 * (1 + s)) ^ 2 - 4 * (2 * (1 + s)) - 8 := by
              linear_combination (8 * s) * hs
            have e1 : (2 - 2 * s) ^ (j + 4) = (2 - 2 * s) ^ (j + 1) * (2 - 2 * s) ^ 3 := by ring
            have e2 : (2 * (1 + s)) ^ (j + 4) = (2 * (1 + s)) ^ (j + 1) * (2 * (1 + s)) ^ 3 := by ring
            rw [e1, e2, r1, r2]; ring
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [key k k le_rfl]
    have h1 := hr (k + 1)
    push_cast at h1 ⊢
    rw [h1, mul_pow]
    ring

end OMA.P_oeis_a223363

theorem OMA.solution : type_of% @OMA.S_oeis_a223363.main := OMA.P_oeis_a223363.main_proof
