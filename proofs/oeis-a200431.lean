import OMAStatements.S_oeis_a200431
import Mathlib
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: fiber over (a,d) gives card = sum of (2n-|a+d|); induction on n gives 3 a(n) = 2n(n-1)(8n-1);
-- the recurrence and the g.f. coefficients then follow by a 4th-difference computation.
open OMA.S_oeis_a200431
namespace A200431Proof
open PowerSeries
lemma box_succ (n : ℕ) : Finset.Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ) =
    insert ((n:ℤ)+1) (insert (-((n:ℤ)+1)) (Finset.Icc (-(n:ℤ)) n)) := by
  ext y; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega

lemma sum_box_succ (n : ℕ) (f : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc (-((n+1 : ℕ) : ℤ)) ((n+1 : ℕ) : ℤ), f x =
      f ((n:ℤ)+1) + f (-((n:ℤ)+1)) + ∑ x ∈ Finset.Icc (-(n:ℤ)) n, f x := by
  rw [box_succ, Finset.sum_insert, Finset.sum_insert, add_assoc]
  · simp only [Finset.mem_Icc]; omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]; omega

lemma row0 (n : ℕ) (c e : ℤ) :
    ∑ w ∈ Finset.Icc (-(n:ℤ)) n, (if w ≠ 0 then c + e * w else 0) = 2 * n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_box_succ, ih, if_pos (by omega), if_pos (by omega)]
    push_cast; ring

lemma row (n : ℕ) (c e : ℤ) (f : ℤ → ℤ)
    (hf : ∀ w ∈ Finset.Icc (-(n:ℤ)) n, f w = if w ≠ 0 then c + e * w else 0) :
    ∑ w ∈ Finset.Icc (-(n:ℤ)) n, f w = 2 * n * c := by
  rw [Finset.sum_congr rfl hf, row0]

def cnd (x w : ℤ) : ℤ := if x ≠ 0 ∧ w ≠ 0 ∧ x + w ≠ 0 then 1 else 0

def g (n : ℕ) (x w : ℤ) : ℤ :=
  if x ≠ 0 ∧ w ≠ 0 ∧ x + w ≠ 0 then min (n:ℤ) (n-x-w) - max (-(n:ℤ)) (-n-x-w) else 0

lemma C_sum (n : ℕ) : ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, cnd x w
    = 4 * n^2 - 2 * n := by
  induction n with
  | zero => simp [cnd]
  | succ n ih =>
    simp only [sum_box_succ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ih]
    rw [row n 1 0 (fun w => cnd ((n:ℤ)+1) w) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold cnd; split_ifs <;> omega)]
    rw [row n 1 0 (fun w => cnd (-((n:ℤ)+1)) w) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold cnd; split_ifs <;> omega)]
    rw [row n 1 0 (fun w => cnd w ((n:ℤ)+1)) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold cnd; split_ifs <;> omega)]
    rw [row n 1 0 (fun w => cnd w (-((n:ℤ)+1))) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold cnd; split_ifs <;> omega)]
    have h1 : cnd ((n:ℤ)+1) ((n:ℤ)+1) = 1 := by unfold cnd; split_ifs <;> omega
    have h2 : cnd ((n:ℤ)+1) (-((n:ℤ)+1)) = 0 := by unfold cnd; split_ifs <;> omega
    have h3 : cnd (-((n:ℤ)+1)) ((n:ℤ)+1) = 0 := by unfold cnd; split_ifs <;> omega
    have h4 : cnd (-((n:ℤ)+1)) (-((n:ℤ)+1)) = 1 := by unfold cnd; split_ifs <;> omega
    rw [h1, h2, h3, h4]
    push_cast; ring

lemma D_sum (n : ℕ) : 3 * ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, g n x w
    = 2 * (n:ℤ) * (n - 1) * (8 * n - 1) := by
  induction n with
  | zero => simp [g]
  | succ n ih =>
    simp only [sum_box_succ]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have inner : ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, g (n+1) x w =
        ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, g n x w +
        2 * ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, cnd x w := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x hx
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro w hw
      simp only [Finset.mem_Icc] at hx hw
      unfold g cnd; push_cast; split_ifs <;> omega
    rw [inner, C_sum]
    rw [row n ((n:ℤ)+1) (-1) (fun w => g (n+1) ((n:ℤ)+1) w) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold g; push_cast; split_ifs <;> omega)]
    rw [row n ((n:ℤ)+1) 1 (fun w => g (n+1) (-((n:ℤ)+1)) w) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold g; push_cast; split_ifs <;> omega)]
    rw [row n ((n:ℤ)+1) (-1) (fun w => g (n+1) w ((n:ℤ)+1)) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold g; push_cast; split_ifs <;> omega)]
    rw [row n ((n:ℤ)+1) 1 (fun w => g (n+1) w (-((n:ℤ)+1))) (by intro w hw; simp only [Finset.mem_Icc] at hw; unfold g; push_cast; split_ifs <;> omega)]
    have h1 : g (n+1) ((n:ℤ)+1) ((n:ℤ)+1) = 0 := by unfold g; push_cast; split_ifs <;> omega
    have h2 : g (n+1) ((n:ℤ)+1) (-((n:ℤ)+1)) = 0 := by unfold g; push_cast; split_ifs <;> omega
    have h3 : g (n+1) (-((n:ℤ)+1)) ((n:ℤ)+1) = 0 := by unfold g; push_cast; split_ifs <;> omega
    have h4 : g (n+1) (-((n:ℤ)+1)) (-((n:ℤ)+1)) = 0 := by unfold g; push_cast; split_ifs <;> omega
    rw [h1, h2, h3, h4]
    push_cast
    ring_nf
    ring_nf at ih
    linarith

lemma fiber (n : ℕ) (x w : ℤ) (hx : x ≠ 0) (hw : w ≠ 0) (hxw : x + w ≠ 0)
    (hx1 : -(n:ℤ) ≤ x) (hx2 : x ≤ n) (hw1 : -(n:ℤ) ≤ w) (hw2 : w ≤ n) :
    (quadruples n).filter (fun q => (q.1, q.2.2.2) = (x, w)) =
      ((Finset.Icc (max (-(n:ℤ)) (-n-x-w)) (min (n:ℤ) (n-x-w))).erase (-x)).image
        (fun b => (x, b, -(x+b+w), w)) := by
  ext ⟨a, b, c, d⟩
  simp only [quadruples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨h, h2, h3⟩
    subst h2 h3
    refine ⟨b, ?_, ?_⟩ <;> omega
  · rintro ⟨b', h, h2⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
    omega

lemma fiber_card (n : ℕ) (x w : ℤ) (hx : x ≠ 0) (hw : w ≠ 0) (hxw : x + w ≠ 0)
    (hx1 : -(n:ℤ) ≤ x) (hx2 : x ≤ n) (hw1 : -(n:ℤ) ≤ w) (hw2 : w ≤ n) :
    (((quadruples n).filter (fun q => (q.1, q.2.2.2) = (x, w))).card : ℤ) =
      (min (n:ℤ) (n-x-w) - max (-(n:ℤ)) (-n-x-w)) := by
  rw [fiber n x w hx hw hxw hx1 hx2 hw1 hw2, Finset.card_image_of_injective]
  · rw [Finset.card_erase_of_mem (by simp only [Finset.mem_Icc]; omega), Int.card_Icc]
    omega
  · intro b1 b2 h
    simp only [Prod.mk.injEq] at h
    exact h.2.1

lemma fiber_empty (n : ℕ) (x w : ℤ) (h : ¬ (x ≠ 0 ∧ w ≠ 0 ∧ x + w ≠ 0)) :
    ((quadruples n).filter (fun q => (q.1, q.2.2.2) = (x, w))) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro ⟨a, b, c, d⟩ hq h2
  simp only [quadruples, Finset.mem_filter, Prod.mk.injEq] at hq h2
  obtain ⟨rfl, rfl⟩ := h2
  omega

lemma card_sum (n : ℕ) : ((quadruples n).card : ℤ) =
    ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n,
      (if x ≠ 0 ∧ w ≠ 0 ∧ x + w ≠ 0 then (min (n:ℤ) (n-x-w) - max (-(n:ℤ)) (-n-x-w)) else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => (q.1, q.2.2.2))
    (t := Finset.Icc (-(n:ℤ)) n ×ˢ Finset.Icc (-(n:ℤ)) n)]
  · push_cast
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Finset.mem_Icc] at hx hw
    split_ifs with h
    · exact fiber_card n x w h.1 h.2.1 h.2.2 hx.1 hx.2 hw.1 hw.2
    · rw [fiber_empty n x w h]; simp
  · rintro ⟨a, b, c, d⟩ hq
    simp only [Finset.mem_coe, quadruples, Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨hq.1.1, hq.1.2.2.2⟩

lemma card_formula (n : ℕ) : 3 * OMA.S_oeis_a200431.a n = 2 * (n:ℤ) * (n - 1) * (8 * n - 1) := by
  have h : ((quadruples n).card : ℤ) =
      ∑ x ∈ Finset.Icc (-(n:ℤ)) n, ∑ w ∈ Finset.Icc (-(n:ℤ)) n, g n x w := by
    rw [card_sum]; rfl
  show 3 * ((quadruples n).card : ℤ) = _
  rw [h]
  exact D_sum n

lemma coeff_mk_mul_X_pow (k j : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk OMA.S_oeis_a200431.a * PowerSeries.X ^ j) = if j ≤ k then OMA.S_oeis_a200431.a (k - j) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; split_ifs <;> simp

end A200431Proof

open A200431Proof in
open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a200431.main := by
  have key : ∀ k : ℕ, a (k+4) - 4 * a (k+3) + 6 * a (k+2) - 4 * a (k+1) + a k = 0 := by
    intro k
    have h0 := card_formula k
    have h1 := card_formula (k+1)
    have h2 := card_formula (k+2)
    have h3 := card_formula (k+3)
    have h4 := card_formula (k+4)
    push_cast at h0 h1 h2 h3 h4
    ring_nf at h0 h1 h2 h3 h4 ⊢
    linarith
  refine ⟨?_, ?_⟩
  · have e : (1 - X : PowerSeries ℤ)^4 = 1 - 4 * X + 6 * X^2 - 4 * X^3 + X^4 := by ring
    rw [e]
    ext k
    have r : (mk a * (1 - 4 * X + 6 * X^2 - 4 * X^3 + X^4) : PowerSeries ℤ)
        = mk a * X^0 - C 4 * (mk a * X^1) + C 6 * (mk a * X^2) - C 4 * (mk a * X^3) + mk a * X^4 := by
      simp only [map_ofNat]; ring
    have r2 : (4 * X^2 * (5 + 3 * X) : PowerSeries ℤ) = C 20 * X^2 + C 12 * X^3 := by
      simp only [map_ofNat]; ring
    rw [r, r2]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_mk_mul_X_pow, PowerSeries.coeff_X_pow]
    have a0 : a 0 = 0 := by decide
    have a1 : a 1 = 0 := by decide
    rcases k with _ | _ | _ | _ | k
    · simp [a0]
    · simp [a0, a1]
    · have a2 : a 2 = 20 := by have := card_formula 2; norm_num at this; linarith
      simp [a0, a1, a2]
    · have a2 : a 2 = 20 := by have := card_formula 2; norm_num at this; linarith
      have a3 : a 3 = 92 := by have := card_formula 3; norm_num at this; linarith
      simp [a0, a1, a2, a3]
    · have := key k
      simp
      exact this
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have := key k
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
    linarith
