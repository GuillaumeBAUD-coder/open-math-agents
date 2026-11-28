import OMAStatements.S_oeis_a202077
import Mathlib

/-! Proof for OEIS A202077: odd adjacent sums force alternating parity, and a zero sum rules out the pattern
odd-even-odd-even-odd, so the array is `(2y₀, 2z₁+1, 2y₂, 2z₃+1, 2y₄)`. Shifting gives a bijection with
pairs of tuples in boxes `[0, 2p]³ × [0, 2c-1]²` (`p = ⌊n/2⌋`, `c = ⌈n/2⌉`) with entry sum `3p + 2c - 1`,
counted as a coefficient of `(Σ_{i≤2p} x^i)³ (Σ_{i<2c} x^i)²` via `invOneSubPow`. This gives
`a(2p) = 115p⁴/12 + 23p³/2 + 53p²/12 + p/2` and
`a(2p+1) = 115p⁴/12 + 161p³/6 + 329p²/12 + 73p/6 + 2`; the g.f. follows coefficientwise by cases on
`n mod 2`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P202077
open Finset OMA.S_oeis_a202077

noncomputable abbrev arrN (m k : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ : Fin k => range (m + 1)

lemma odd_iff4 (v : Fin 5 → ℤ) : (∀ i : Fin 4, Odd (v i.castSucc + v i.succ)) ↔
    (v 0 + v 1) % 2 = 1 ∧ (v 1 + v 2) % 2 = 1 ∧ (v 2 + v 3) % 2 = 1 ∧ (v 3 + v 4) % 2 = 1 := by
  constructor
  · intro h; exact ⟨Int.odd_iff.1 (h 0), Int.odd_iff.1 (h 1), Int.odd_iff.1 (h 2), Int.odd_iff.1 (h 3)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    rw [Int.odd_iff]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3


lemma helpE (p c : ℕ) (hc1 : p ≤ c) (hc2 : c ≤ p + 1) (x : ℤ) (h1 : -((p : ℤ) + c) ≤ x) (h2 : x ≤ p + c)
    (hx : x % 2 = 0) : ((x + 2 * p) / 2).toNat < 2 * p + 1 ∧ 2 * ((((x + 2 * p) / 2).toNat : ℕ) : ℤ) - 2 * p = x := by
  omega

lemma helpO (p c : ℕ) (hc1 : p ≤ c) (hc2 : c ≤ p + 1) (x : ℤ) (h1 : -((p : ℤ) + c) ≤ x) (h2 : x ≤ p + c)
    (hx : x % 2 = 1) : ((x + (2 * c - 1)) / 2).toNat < 2 * c ∧
      2 * ((((x + (2 * c - 1)) / 2).toNat : ℕ) : ℤ) - (2 * c - 1) = x := by
  omega

lemma backE (p c : ℕ) (hc1 : p ≤ c) (u : ℕ) (hu : u < 2 * p + 1) :
    -((p : ℤ) + c) ≤ 2 * (u : ℤ) - 2 * p ∧ 2 * (u : ℤ) - 2 * p ≤ p + c ∧ (2 * (u : ℤ) - 2 * p) % 2 = 0 ∧
      ((2 * (u : ℤ) - 2 * p + 2 * p) / 2).toNat = u := by
  omega

lemma backO (p c : ℕ) (hc1 : p ≤ c) (hc2 : c ≤ p + 1) (hc0 : 1 ≤ c) (w : ℕ) (hw : w < 2 * c) :
    -((p : ℤ) + c) ≤ 2 * (w : ℤ) - (2 * c - 1) ∧ 2 * (w : ℤ) - (2 * c - 1) ≤ p + c ∧
      (2 * (w : ℤ) - (2 * c - 1)) % 2 = 1 ∧ ((2 * (w : ℤ) - (2 * c - 1) + (2 * c - 1)) / 2).toNat = w := by
  omega

lemma count_eq (p c s : ℕ) (hc1 : p ≤ c) (hc2 : c ≤ p + 1) (hc0 : 1 ≤ c) (hs : s + 1 = 3 * p + 2 * c) :
    a (p + c) = ((arrN (2 * p) 3 ×ˢ arrN (2 * c - 1) 2).filter (fun uw => ∑ i, uw.1 i + ∑ i, uw.2 i = s)).card := by
  unfold a
  have hm2 : ((2 * c - 1 : ℕ) : ℤ) = 2 * c - 1 := by omega
  apply card_nbij'
    (fun v : Fin 5 → ℤ => ((![((v 0 + 2 * p) / 2).toNat, ((v 2 + 2 * p) / 2).toNat, ((v 4 + 2 * p) / 2).toNat] : Fin 3 → ℕ),
      (![((v 1 + (2 * c - 1)) / 2).toNat, ((v 3 + (2 * c - 1)) / 2).toNat] : Fin 2 → ℕ)))
    (fun uw : (Fin 3 → ℕ) × (Fin 2 → ℕ) => (![2 * (uw.1 0 : ℤ) - 2 * p, 2 * (uw.2 0 : ℤ) - (2 * c - 1),
      2 * (uw.1 1 : ℤ) - 2 * p, 2 * (uw.2 1 : ℤ) - (2 * c - 1), 2 * (uw.1 2 : ℤ) - 2 * p] : Fin 5 → ℤ))
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_Icc, Fin.sum_univ_five,
      odd_iff4] at hv
    obtain ⟨hb, hs0, o0, o1, o2, o3⟩ := hv
    push_cast at hb
    have b0 := hb 0; have b1 := hb 1; have b2 := hb 2; have b3 := hb 3; have b4 := hb 4
    have pe : v 0 % 2 = 0 ∧ v 1 % 2 = 1 ∧ v 2 % 2 = 0 ∧ v 3 % 2 = 1 ∧ v 4 % 2 = 0 := by omega
    have e0 := helpE p c hc1 hc2 (v 0) b0.1 b0.2 pe.1
    have e2 := helpE p c hc1 hc2 (v 2) b2.1 b2.2 pe.2.2.1
    have e4 := helpE p c hc1 hc2 (v 4) b4.1 b4.2 pe.2.2.2.2
    have d1 := helpO p c hc1 hc2 (v 1) b1.1 b1.2 pe.2.1
    have d3 := helpO p c hc1 hc2 (v 3) b3.1 b3.2 pe.2.2.2.1
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, Fintype.mem_piFinset, mem_range,
      Fin.sum_univ_three, Fin.sum_univ_two]
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · fin_cases i
      · exact e0.1
      · exact e2.1
      · exact e4.1
    · fin_cases i
      · rw [show 2 * c - 1 + 1 = 2 * c by omega]; exact d1.1
      · rw [show 2 * c - 1 + 1 = 2 * c by omega]; exact d3.1
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      have f0 := e0.2; have f2 := e2.2; have f4 := e4.2; have f1 := d1.2; have f3 := d3.2
      generalize ((v 0 + 2 * p) / 2).toNat = A0 at *
      generalize ((v 2 + 2 * p) / 2).toNat = A1 at *
      generalize ((v 4 + 2 * p) / 2).toNat = A2 at *
      generalize ((v 1 + (2 * c - 1)) / 2).toNat = B0 at *
      generalize ((v 3 + (2 * c - 1)) / 2).toNat = B1 at *
      omega
  · rintro ⟨u, w⟩ huw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, Fintype.mem_piFinset, mem_range,
      Fin.sum_univ_three, Fin.sum_univ_two] at huw
    obtain ⟨⟨hu, hw⟩, hsum⟩ := huw
    have u0 := backE p c hc1 (u 0) (hu 0); have u1 := backE p c hc1 (u 1) (hu 1)
    have u2 := backE p c hc1 (u 2) (hu 2)
    have w0 := backO p c hc1 hc2 hc0 (w 0) (by have := hw 0; omega)
    have w1 := backO p c hc1 hc2 hc0 (w 1) (by have := hw 1; omega)
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_Icc, Fin.sum_univ_five,
      odd_iff4]
    push_cast
    refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · fin_cases i
      · exact ⟨u0.1, u0.2.1⟩
      · exact ⟨w0.1, w0.2.1⟩
      · exact ⟨u1.1, u1.2.1⟩
      · exact ⟨w1.1, w1.2.1⟩
      · exact ⟨u2.1, u2.2.1⟩
    all_goals try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_three, Matrix.cons_val_four]
    all_goals omega
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_Icc, Fin.sum_univ_five,
      odd_iff4] at hv
    obtain ⟨hb, hs0, o0, o1, o2, o3⟩ := hv
    push_cast at hb
    have b0 := hb 0; have b1 := hb 1; have b2 := hb 2; have b3 := hb 3; have b4 := hb 4
    have pe : v 0 % 2 = 0 ∧ v 1 % 2 = 1 ∧ v 2 % 2 = 0 ∧ v 3 % 2 = 1 ∧ v 4 % 2 = 0 := by omega
    have e0 := helpE p c hc1 hc2 (v 0) b0.1 b0.2 pe.1
    have e2 := helpE p c hc1 hc2 (v 2) b2.1 b2.2 pe.2.2.1
    have e4 := helpE p c hc1 hc2 (v 4) b4.1 b4.2 pe.2.2.2.2
    have d1 := helpO p c hc1 hc2 (v 1) b1.1 b1.2 pe.2.1
    have d3 := helpO p c hc1 hc2 (v 3) b3.1 b3.2 pe.2.2.2.1
    funext i
    fin_cases i
    · exact e0.2
    · exact d1.2
    · exact e2.2
    · exact d3.2
    · exact e4.2
  · rintro ⟨u, w⟩ huw
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, Fintype.mem_piFinset, mem_range] at huw
    obtain ⟨⟨hu, hw⟩, -⟩ := huw
    ext i
    · fin_cases i
      · exact (backE p c hc1 (u 0) (hu 0)).2.2.2
      · exact (backE p c hc1 (u 1) (hu 1)).2.2.2
      · exact (backE p c hc1 (u 2) (hu 2)).2.2.2
    · fin_cases i
      · exact (backO p c hc1 hc2 hc0 (w 0) (by have := hw 0; omega)).2.2.2
      · exact (backO p c hc1 hc2 hc0 (w 1) (by have := hw 1; omega)).2.2.2

noncomputable def PP (m : ℕ) : PowerSeries ℚ := ∑ i ∈ range (m + 1), PowerSeries.X ^ i

lemma coeff_PP (m i : ℕ) : PowerSeries.coeff i (PP m) = if i ≤ m then 1 else 0 := by
  unfold PP
  simp [map_sum, PowerSeries.coeff_X_pow, Nat.lt_succ_iff]

lemma cnt_coeff (m : ℕ) : ∀ (k s : ℕ),
    (((arrN m k).filter (fun a => ∑ i, a i = s)).card : ℚ) = PowerSeries.coeff s (PP m ^ k) := by
  intro k
  induction k with
  | zero =>
    intro s
    simp only [pow_zero, PowerSeries.coeff_one]
    by_cases hs : s = 0
    · subst hs; rw [filter_true_of_mem (fun a _ => by simp)]; simp
    · rw [if_neg hs]
      rw [show (arrN m 0).filter (fun a => ∑ i, a i = s) = ∅ by
        rw [filter_eq_empty_iff]; intro a _; simp [Ne.symm hs]]
      simp
  | succ k ih =>
    intro s
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have e : ((arrN m (k + 1)).filter (fun a => ∑ i, a i = s)).card =
        ∑ x ∈ range (s + 1), ((range (m + 1)).filter (fun y => y = x)).card *
          ((arrN m k).filter (fun a => ∑ i, a i = s - x)).card := by
      rw [card_eq_sum_card_fiberwise (f := fun a => a 0) (t := range (s + 1))]
      · apply sum_congr rfl; intro x hx
        simp only [mem_range] at hx
        rw [show ((range (m + 1)).filter (fun y => y = x)).card = if x ≤ m then 1 else 0 by
          split_ifs with h
          · rw [card_eq_one]; exact ⟨x, by ext y; simp only [mem_filter, mem_range, mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩⟩
          · rw [card_eq_zero, filter_eq_empty_iff]; intro y hy; simp at hy; omega]
        split_ifs with hxm
        · rw [one_mul]
          apply card_nbij' (fun a => Fin.tail a) (fun w => Fin.cons x w)
          · intro a ha
            simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq, mem_filter] at ha ⊢
            refine ⟨fun i => ha.1.1 _, ?_⟩
            have := ha.1.2; rw [Fin.sum_univ_succ] at this
            have h2 := ha.2
            show ∑ i : Fin k, a i.succ = s - x; omega
          · intro w hw
            simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq, mem_filter] at hw ⊢
            refine ⟨⟨fun i => ?_, ?_⟩, by simp⟩
            · refine Fin.cases ?_ (fun j => ?_) i
              · simp; omega
              · simpa using hw.1 j
            · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; omega
          · intro a ha
            simp only [coe_filter, mem_filter] at ha
            rw [← ha.2]; exact Fin.cons_self_tail a
          · intro w _; simp
        · rw [zero_mul, card_eq_zero, filter_eq_empty_iff]
          intro a ha h0
          simp only [mem_filter, Fintype.mem_piFinset, mem_range] at ha
          have := ha.1 0; omega
      · intro a ha
        simp only [mem_coe, mem_filter, Fintype.mem_piFinset] at ha
        simp only [mem_coe, mem_range]
        have := ha.2; rw [Fin.sum_univ_succ] at this; omega
    rw [e]; push_cast
    apply sum_congr rfl; intro x hx
    simp only [mem_range] at hx
    rw [ih, coeff_PP]
    split_ifs with h
    · rw [show ((range (m + 1)).filter (fun y => y = x)).card = 1 by
        rw [card_eq_one]; exact ⟨x, by ext y; simp only [mem_filter, mem_range, mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩⟩]; simp
    · rw [show ((range (m + 1)).filter (fun y => y = x)).card = 0 by
        rw [card_eq_zero, filter_eq_empty_iff]; intro y hy; simp at hy; omega]; simp


lemma pair2 (m1 m2 s : ℕ) :
    ((((arrN m1 3) ×ˢ (arrN m2 2)).filter (fun ab => ∑ i, ab.1 i + ∑ i, ab.2 i = s)).card : ℚ) =
      PowerSeries.coeff s (PP m1 ^ 3 * PP m2 ^ 2) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [card_eq_sum_card_fiberwise (f := fun ab => ∑ i, ab.1 i) (t := range (s + 1))]
  · push_cast
    apply sum_congr rfl; intro x hx
    simp only [mem_range] at hx
    rw [← cnt_coeff, ← cnt_coeff, ← Nat.cast_mul, ← card_product]
    congr 2; ext ⟨a, b⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, h⟩, rfl⟩; exact ⟨⟨ha, rfl⟩, hb, by omega⟩
    · rintro ⟨⟨ha, rfl⟩, hb, h⟩; exact ⟨⟨⟨ha, hb⟩, by omega⟩, rfl⟩
  · intro ab hab
    simp only [mem_coe, mem_filter] at hab
    simp only [mem_coe, mem_range]; omega

/-- `B4 t = C(t + 4, 4)` as a polynomial in `t`. -/
noncomputable def B4 (t : ℤ) : ℚ := ((t : ℚ) + 1) * (t + 2) * (t + 3) * (t + 4) / 24

lemma choose4 (x : ℕ) : ((x.choose 4 : ℕ) : ℚ) = (x : ℚ) * (x - 1) * (x - 2) * (x - 3) / 24 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [descPochhammer_succ_right, Polynomial.eval_mul, Nat.factorial] <;> ring

lemma choose_B4 (e s : ℕ) (h : e ≤ s) : (((4 + (s - e)).choose 4 : ℕ) : ℚ) = B4 ((s : ℤ) - e) := by
  obtain ⟨d, rfl⟩ : ∃ d, s = e + d := ⟨s - e, by omega⟩
  rw [Nat.add_sub_cancel_left, choose4, B4]
  push_cast; ring

lemma choose_B4' (e s : ℕ) : (if e ≤ s then (((4 + (s - e)).choose 4 : ℕ) : ℚ) else 0) =
    if e ≤ s then B4 ((s : ℤ) - e) else 0 := by
  split_ifs with h
  · exact choose_B4 e s h
  · rfl

lemma coeffPP (m1 m2 s : ℕ) : PowerSeries.coeff s (PP m1 ^ 3 * PP m2 ^ 2) =
    (1 : ℚ) * (if 0 * (m1 + 1) + 0 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (0 * (m1 + 1) + 0 * (m2 + 1) : ℕ) : ℤ) else 0) + (-2 : ℚ) * (if 0 * (m1 + 1) + 1 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (0 * (m1 + 1) + 1 * (m2 + 1) : ℕ) : ℤ) else 0) + (1 : ℚ) * (if 0 * (m1 + 1) + 2 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (0 * (m1 + 1) + 2 * (m2 + 1) : ℕ) : ℤ) else 0) + (-3 : ℚ) * (if 1 * (m1 + 1) + 0 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (1 * (m1 + 1) + 0 * (m2 + 1) : ℕ) : ℤ) else 0) + (6 : ℚ) * (if 1 * (m1 + 1) + 1 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (1 * (m1 + 1) + 1 * (m2 + 1) : ℕ) : ℤ) else 0) + (-3 : ℚ) * (if 1 * (m1 + 1) + 2 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (1 * (m1 + 1) + 2 * (m2 + 1) : ℕ) : ℤ) else 0) + (3 : ℚ) * (if 2 * (m1 + 1) + 0 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (2 * (m1 + 1) + 0 * (m2 + 1) : ℕ) : ℤ) else 0) + (-6 : ℚ) * (if 2 * (m1 + 1) + 1 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (2 * (m1 + 1) + 1 * (m2 + 1) : ℕ) : ℤ) else 0) + (3 : ℚ) * (if 2 * (m1 + 1) + 2 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (2 * (m1 + 1) + 2 * (m2 + 1) : ℕ) : ℤ) else 0) + (-1 : ℚ) * (if 3 * (m1 + 1) + 0 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (3 * (m1 + 1) + 0 * (m2 + 1) : ℕ) : ℤ) else 0) + (2 : ℚ) * (if 3 * (m1 + 1) + 1 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (3 * (m1 + 1) + 1 * (m2 + 1) : ℕ) : ℤ) else 0) + (-1 : ℚ) * (if 3 * (m1 + 1) + 2 * (m2 + 1) ≤ s then B4 ((s : ℕ) - (3 * (m1 + 1) + 2 * (m2 + 1) : ℕ) : ℤ) else 0) := by
  set G : PowerSeries ℚ := PowerSeries.mk fun j => ((4 + j).choose 4 : ℚ) with hG
  have hinv : (1 - PowerSeries.X) ^ 5 * G = 1 := by
    have := (PowerSeries.invOneSubPow ℚ 5).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at this
    simpa [hG, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] using this
  have hP : ∀ m, PP m * (1 - PowerSeries.X) = 1 - PowerSeries.X ^ (m + 1) := by
    intro m
    unfold PP; rw [mul_sub, mul_one, sum_mul]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, sum_range_succ (fun i => PowerSeries.X ^ i * PowerSeries.X)]
      calc _ = (∑ x ∈ range (m + 1), PowerSeries.X ^ x - ∑ i ∈ range (m + 1), PowerSeries.X ^ i * PowerSeries.X)
            + PowerSeries.X ^ (m + 1) - PowerSeries.X ^ (m + 1) * PowerSeries.X := by ring
        _ = _ := by rw [ih]; ring
  have e : PP m1 ^ 3 * PP m2 ^ 2 =
      (1 - PowerSeries.X ^ (m1 + 1)) ^ 3 * (1 - PowerSeries.X ^ (m2 + 1)) ^ 2 * G := by
    calc PP m1 ^ 3 * PP m2 ^ 2 = PP m1 ^ 3 * PP m2 ^ 2 * ((1 - PowerSeries.X) ^ 5 * G) := by rw [hinv, mul_one]
      _ = (PP m1 * (1 - PowerSeries.X)) ^ 3 * (PP m2 * (1 - PowerSeries.X)) ^ 2 * G := by ring
      _ = _ := by rw [hP, hP]
  rw [e]
  have expand : ((1 - PowerSeries.X ^ (m1 + 1)) ^ 3 * (1 - PowerSeries.X ^ (m2 + 1)) ^ 2 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ (0 * (m1 + 1) + 0 * (m2 + 1)) + PowerSeries.C (-2 : ℚ) * PowerSeries.X ^ (0 * (m1 + 1) + 1 * (m2 + 1)) + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ (0 * (m1 + 1) + 2 * (m2 + 1)) + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ (1 * (m1 + 1) + 0 * (m2 + 1)) + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ (1 * (m1 + 1) + 1 * (m2 + 1)) + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ (1 * (m1 + 1) + 2 * (m2 + 1)) + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ (2 * (m1 + 1) + 0 * (m2 + 1)) + PowerSeries.C (-6 : ℚ) * PowerSeries.X ^ (2 * (m1 + 1) + 1 * (m2 + 1)) + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ (2 * (m1 + 1) + 2 * (m2 + 1)) + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ (3 * (m1 + 1) + 0 * (m2 + 1)) + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ (3 * (m1 + 1) + 1 * (m2 + 1)) + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ (3 * (m1 + 1) + 2 * (m2 + 1)) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [expand]
  simp only [add_mul, map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', hG,
    PowerSeries.coeff_mk]
  simp only [choose_B4']

lemma a_zero : a 0 = 0 := by
  unfold a
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v hv h
  simp only [Fintype.mem_piFinset, mem_Icc] at hv
  rw [odd_iff4] at h
  have b0 := hv 0; have b1 := hv 1
  push_cast at b0 b1
  omega

lemma closedE (q : ℕ) : (a (2 * q + 2) : ℚ) = (26 : ℚ) * ((q : ℚ)) ^ 0 + (493/6 : ℚ) * ((q : ℚ)) ^ 1 + (1157/12 : ℚ) * ((q : ℚ)) ^ 2 + (299/6 : ℚ) * ((q : ℚ)) ^ 3 + (115/12 : ℚ) * ((q : ℚ)) ^ 4 := by
  have h := count_eq (q + 1) (q + 1) (5 * q + 4) (by omega) (by omega) (by omega) (by omega)
  simp only [show 2 * (q + 1) - 1 = 2 * q + 1 by omega] at h
  rw [show 2 * q + 2 = (q + 1) + (q + 1) by ring, h, pair2, coeffPP]
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> norm_num [B4]
  · simp only [if_pos (show 0 * (2 * (q + 1) + 1) + 0 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_pos (show 0 * (2 * (q + 1) + 1) + 1 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_pos (show 0 * (2 * (q + 1) + 1) + 2 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_pos (show 1 * (2 * (q + 1) + 1) + 0 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_pos (show 1 * (2 * (q + 1) + 1) + 1 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_neg (show ¬ (1 * (2 * (q + 1) + 1) + 2 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega), if_pos (show 2 * (2 * (q + 1) + 1) + 0 * (2 * q + 1 + 1) ≤ 5 * q + 4 by omega), if_neg (show ¬ (2 * (2 * (q + 1) + 1) + 1 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega), if_neg (show ¬ (2 * (2 * (q + 1) + 1) + 2 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega), if_neg (show ¬ (3 * (2 * (q + 1) + 1) + 0 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega), if_neg (show ¬ (3 * (2 * (q + 1) + 1) + 1 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega), if_neg (show ¬ (3 * (2 * (q + 1) + 1) + 2 * (2 * q + 1 + 1) ≤ 5 * q + 4) by omega)]
    unfold B4; push_cast; ring

lemma closedO (p : ℕ) : (a (2 * p + 1) : ℚ) = (2 : ℚ) * ((p : ℚ)) ^ 0 + (73/6 : ℚ) * ((p : ℚ)) ^ 1 + (329/12 : ℚ) * ((p : ℚ)) ^ 2 + (161/6 : ℚ) * ((p : ℚ)) ^ 3 + (115/12 : ℚ) * ((p : ℚ)) ^ 4 := by
  have h := count_eq p (p + 1) (5 * p + 1) (by omega) (by omega) (by omega) (by omega)
  simp only [show 2 * (p + 1) - 1 = 2 * p + 1 by omega] at h
  rw [show 2 * p + 1 = p + (p + 1) by ring, h, pair2, coeffPP]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · interval_cases p <;> norm_num [B4]
  · simp only [if_pos (show 0 * (2 * p + 1) + 0 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_pos (show 0 * (2 * p + 1) + 1 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_pos (show 0 * (2 * p + 1) + 2 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_pos (show 1 * (2 * p + 1) + 0 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_pos (show 1 * (2 * p + 1) + 1 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_neg (show ¬ (1 * (2 * p + 1) + 2 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega), if_pos (show 2 * (2 * p + 1) + 0 * (2 * p + 1 + 1) ≤ 5 * p + 1 by omega), if_neg (show ¬ (2 * (2 * p + 1) + 1 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega), if_neg (show ¬ (2 * (2 * p + 1) + 2 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega), if_neg (show ¬ (3 * (2 * p + 1) + 0 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega), if_neg (show ¬ (3 * (2 * p + 1) + 1 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega), if_neg (show ¬ (3 * (2 * p + 1) + 2 * (2 * p + 1 + 1) ≤ 5 * p + 1) by omega)]
    unfold B4; push_cast; ring

lemma hE (p : ℕ) : (a (2 * p) : ℚ) = (1/2 : ℚ) * ((p : ℚ)) ^ 1 + (53/12 : ℚ) * ((p : ℚ)) ^ 2 + (23/2 : ℚ) * ((p : ℚ)) ^ 3 + (115/12 : ℚ) * ((p : ℚ)) ^ 4 := by
  rcases p with _ | q
  · simp [a_zero]
  · rw [show 2 * (q + 1) = 2 * q + 2 by ring, closedE]; push_cast; ring

lemma hO (p : ℕ) : (a (2 * p + 1) : ℚ) = (2 : ℚ) * ((p : ℚ)) ^ 0 + (73/6 : ℚ) * ((p : ℚ)) ^ 1 + (329/12 : ℚ) * ((p : ℚ)) ^ 2 + (161/6 : ℚ) * ((p : ℚ)) ^ 3 + (115/12 : ℚ) * ((p : ℚ)) ^ 4 := closedO p

end OMA.P202077

namespace OMA.P202077
lemma t0 : (OMA.S_oeis_a202077.a 0 : ℚ) = 0 := by
  rw [show (0 : ℕ) = 2 * 0 from rfl, hE]; norm_num

lemma t1 : (OMA.S_oeis_a202077.a 1 : ℚ) = 2 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, hO]; norm_num

lemma t2 : (OMA.S_oeis_a202077.a 2 : ℚ) = 26 := by
  rw [show (2 : ℕ) = 2 * 1 from rfl, hE]; norm_num

lemma t3 : (OMA.S_oeis_a202077.a 3 : ℚ) = 78 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, hO]; norm_num

lemma t4 : (OMA.S_oeis_a202077.a 4 : ℚ) = 264 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, hE]; norm_num

lemma t5 : (OMA.S_oeis_a202077.a 5 : ℚ) = 504 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, hO]; norm_num

lemma t6 : (OMA.S_oeis_a202077.a 6 : ℚ) = 1128 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, hE]; norm_num

lemma t7 : (OMA.S_oeis_a202077.a 7 : ℚ) = 1786 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, hO]; norm_num

lemma t8 : (OMA.S_oeis_a202077.a 8 : ℚ) = 3262 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, hE]; norm_num

lemma t9 : (OMA.S_oeis_a202077.a 9 : ℚ) = 4660 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 from rfl, hO]; norm_num

lemma t10 : (OMA.S_oeis_a202077.a 10 : ℚ) = 7540 := by
  rw [show (10 : ℕ) = 2 * 5 from rfl, hE]; norm_num

lemma rec0 (q : ℕ) : (1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 5) + 1) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 5)) : ℚ) + (-4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 4) + 1) : ℚ) + (4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 4)) : ℚ) + (6 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 3) + 1) : ℚ) + (-6 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 3)) : ℚ) + (-4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 2) + 1) : ℚ) + (4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 2)) : ℚ) + (1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 1) + 1) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 1)) : ℚ) = 0 := by
  rw [OMA.P202077.hO (q + 5), OMA.P202077.hE (q + 5), OMA.P202077.hO (q + 4), OMA.P202077.hE (q + 4), OMA.P202077.hO (q + 3), OMA.P202077.hE (q + 3), OMA.P202077.hO (q + 2), OMA.P202077.hE (q + 2), OMA.P202077.hO (q + 1), OMA.P202077.hE (q + 1)]
  push_cast
  ring

lemma rec1 (q : ℕ) : (1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 6)) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 5) + 1) : ℚ) + (-4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 5)) : ℚ) + (4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 4) + 1) : ℚ) + (6 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 4)) : ℚ) + (-6 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 3) + 1) : ℚ) + (-4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 3)) : ℚ) + (4 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 2) + 1) : ℚ) + (1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 2)) : ℚ) + (-1 : ℚ) * (OMA.S_oeis_a202077.a (2 * (q + 1) + 1) : ℚ) = 0 := by
  rw [OMA.P202077.hE (q + 6), OMA.P202077.hO (q + 5), OMA.P202077.hE (q + 5), OMA.P202077.hO (q + 4), OMA.P202077.hE (q + 4), OMA.P202077.hO (q + 3), OMA.P202077.hE (q + 3), OMA.P202077.hO (q + 2), OMA.P202077.hE (q + 2), OMA.P202077.hO (q + 1)]
  push_cast
  ring

end OMA.P202077

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a202077.main := by
  ext m
  have hX : ((1 - X) ^ 5 * (1 + X) ^ 4 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-1 : ℚ) * X ^ 1 + C (-4 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 + C (-6 : ℚ) * X ^ 5 + C (-4 : ℚ) * X ^ 6 + C (4 : ℚ) * X ^ 7 + C (1 : ℚ) * X ^ 8 + C (-1 : ℚ) * X ^ 9 := by
    simp only [map_neg, map_one, map_ofNat, map_natCast]; ring
  rw [hX]
  have hN : (2 * X * (1 + 12 * X + 22 * X ^ 2 + 45 * X ^ 3 + 22 * X ^ 4 + 12 * X ^ 5 + X ^ 6) : PowerSeries ℚ) = X ^ 1 * C (2 : ℚ) + X ^ 2 * C (24 : ℚ) + X ^ 3 * C (44 : ℚ) + X ^ 4 * C (90 : ℚ) + X ^ 5 * C (44 : ℚ) + X ^ 6 * C (24 : ℚ) + X ^ 7 * C (2 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hN]
  simp only [mul_add, map_add, coeff_mk, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mul_C, coeff_X,
    Nat.zero_le, if_true, Nat.sub_zero]
  rcases Nat.lt_or_ge m 11 with hm | hm
  · interval_cases m <;> norm_num only [OMA.P202077.t0, OMA.P202077.t1, OMA.P202077.t2, OMA.P202077.t3, OMA.P202077.t4, OMA.P202077.t5, OMA.P202077.t6, OMA.P202077.t7, OMA.P202077.t8, OMA.P202077.t9, OMA.P202077.t10, if_true, if_false, ite_true, ite_false, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
  · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ m = 2 * q + r + 11 := ⟨(m - 11) / 2, (m - 11) % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    simp only [if_pos (show 1 ≤ 2 * q + r + 11 by omega), if_pos (show 2 ≤ 2 * q + r + 11 by omega), if_pos (show 3 ≤ 2 * q + r + 11 by omega), if_pos (show 4 ≤ 2 * q + r + 11 by omega), if_pos (show 5 ≤ 2 * q + r + 11 by omega), if_pos (show 6 ≤ 2 * q + r + 11 by omega), if_pos (show 7 ≤ 2 * q + r + 11 by omega), if_pos (show 8 ≤ 2 * q + r + 11 by omega), if_pos (show 9 ≤ 2 * q + r + 11 by omega)]
    try simp only [if_neg (show ¬ (2 * q + r + 11 = 0) by omega), if_neg (show ¬ (2 * q + r + 11 = 1) by omega), if_neg (show ¬ (2 * q + r + 11 = 2) by omega), if_neg (show ¬ (2 * q + r + 11 = 3) by omega), if_neg (show ¬ (2 * q + r + 11 = 4) by omega), if_neg (show ¬ (2 * q + r + 11 = 5) by omega), if_neg (show ¬ (2 * q + r + 11 = 6) by omega), if_neg (show ¬ (2 * q + r + 11 = 7) by omega)]
    try simp only [zero_add, add_zero, sub_zero, mul_zero]
    interval_cases r
    · rw [show 2 * q + 0 + 11 - 9 = 2 * (q + 1) by omega, show 2 * q + 0 + 11 - 8 = 2 * (q + 1) + 1 by omega, show 2 * q + 0 + 11 - 7 = 2 * (q + 2) by omega, show 2 * q + 0 + 11 - 6 = 2 * (q + 2) + 1 by omega, show 2 * q + 0 + 11 - 5 = 2 * (q + 3) by omega, show 2 * q + 0 + 11 - 4 = 2 * (q + 3) + 1 by omega, show 2 * q + 0 + 11 - 3 = 2 * (q + 4) by omega, show 2 * q + 0 + 11 - 2 = 2 * (q + 4) + 1 by omega, show 2 * q + 0 + 11 - 1 = 2 * (q + 5) by omega, show 2 * q + 0 + 11 = 2 * (q + 5) + 1 by ring]
      linear_combination OMA.P202077.rec0 q
    · rw [show 2 * q + 1 + 11 - 9 = 2 * (q + 1) + 1 by omega, show 2 * q + 1 + 11 - 8 = 2 * (q + 2) by omega, show 2 * q + 1 + 11 - 7 = 2 * (q + 2) + 1 by omega, show 2 * q + 1 + 11 - 6 = 2 * (q + 3) by omega, show 2 * q + 1 + 11 - 5 = 2 * (q + 3) + 1 by omega, show 2 * q + 1 + 11 - 4 = 2 * (q + 4) by omega, show 2 * q + 1 + 11 - 3 = 2 * (q + 4) + 1 by omega, show 2 * q + 1 + 11 - 2 = 2 * (q + 5) by omega, show 2 * q + 1 + 11 - 1 = 2 * (q + 5) + 1 by omega, show 2 * q + 1 + 11 = 2 * (q + 6) by ring]
      linear_combination OMA.P202077.rec1 q
