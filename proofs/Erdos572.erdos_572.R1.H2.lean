import OMAReductions.R_Erdos572_erdos_572_R1
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Step Erdos572.erdos_572.R1.H2: hypothesis H2 of reduction Erdos572.erdos_572.R1
-- Credit: @yhay81
-- uses note #158817
-- H2 := ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,     c * (n : ℝ) ^ (1 + 1 / (5 : ℝ)) ≤       (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 5)) : ℝ)

open Filter SimpleGraph

private abbrev WFive (p : ℕ) := Fin 5 → ZMod p

private abbrev WVert4 (p k : ℕ) := (WFive p ⊕ WFive p) ⊕ Fin k

private def wenger4Rel (p : ℕ) (P L : WFive p) : Prop :=
  ∀ j : Fin 4, P j.succ + L j.succ = P 0 ^ (j.val + 1) * L 0

private def paddedWenger4 (p k : ℕ) : SimpleGraph (WVert4 p k) where
  Adj u v :=
    match u, v with
    | Sum.inl (Sum.inl P), Sum.inl (Sum.inr L) => wenger4Rel p P L
    | Sum.inl (Sum.inr L), Sum.inl (Sum.inl P) => wenger4Rel p P L
    | _, _ => False
  symm := by
    constructor
    rintro ((P | L) | i) ((P' | L') | j) h <;> exact h
  loopless := by
    constructor
    rintro ((P | L) | i) h
    · exact h
    · exact h
    · exact h

private lemma wenger4_pt_eq_of_zero_eq {p : ℕ} {P P' L : WFive p}
    (h1 : wenger4Rel p P L) (h2 : wenger4Rel p P' L) (h0 : P 0 = P' 0) : P = P' := by
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  have hj1 := h1 j
  have hj2 := h2 j
  rw [h0] at hj1
  linear_combination hj1 - hj2

private lemma wenger4_line_eq_of_zero_eq {p : ℕ} {P L L' : WFive p}
    (h1 : wenger4Rel p P L) (h2 : wenger4Rel p P L') (h0 : L 0 = L' 0) : L = L' := by
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  have hj1 := h1 j
  have hj2 := h2 j
  rw [h0] at hj1
  linear_combination hj1 - hj2

private lemma five_vanish_elim {F : Type*} [Field F]
    {x0 x1 x2 x3 x4 c0 c1 c2 c3 c4 : F}
    (hc0 : c0 ≠ 0)
    (h0 : c0 + c1 + c2 + c3 + c4 = 0)
    (h1 : c0 * x0 + c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 = 0)
    (h2 : c0 * x0 ^ 2 + c1 * x1 ^ 2 + c2 * x2 ^ 2 + c3 * x3 ^ 2 + c4 * x4 ^ 2 = 0)
    (h3 : c0 * x0 ^ 3 + c1 * x1 ^ 3 + c2 * x2 ^ 3 + c3 * x3 ^ 3 + c4 * x4 ^ 3 = 0)
    (h4 : c0 * x0 ^ 4 + c1 * x1 ^ 4 + c2 * x2 ^ 4 + c3 * x3 ^ 4 + c4 * x4 ^ 4 = 0)
    (hx01 : x0 ≠ x1) (hx02 : x0 ≠ x2) (hx03 : x0 ≠ x3) (hx04 : x0 ≠ x4) : False := by
  have hprod : c0 * (x0 - x1) * (x0 - x2) * (x0 - x3) * (x0 - x4) = 0 := by
    linear_combination
      h4
      - (x1 + x2 + x3 + x4) * h3
      + (x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4 + x3 * x4) * h2
      - (x1 * x2 * x3 + x1 * x2 * x4 + x1 * x3 * x4 + x2 * x3 * x4) * h1
      + (x1 * x2 * x3 * x4) * h0
  simp only [mul_eq_zero, sub_eq_zero] at hprod
  tauto

private lemma wenger4_no_ten_cycle {p : ℕ} [Fact p.Prime]
    (P0 P1 P2 P3 P4 L0 L1 L2 L3 L4 : WFive p)
    (hP01 : P0 ≠ P1) (hP12 : P1 ≠ P2) (hP23 : P2 ≠ P3) (hP34 : P3 ≠ P4) (hP40 : P4 ≠ P0)
    (hL01 : L0 ≠ L1) (hL12 : L1 ≠ L2) (hL23 : L2 ≠ L3) (hL34 : L3 ≠ L4) (hL40 : L4 ≠ L0)
    (e0 : wenger4Rel p P0 L0) (e1 : wenger4Rel p P1 L0)
    (e2 : wenger4Rel p P1 L1) (e3 : wenger4Rel p P2 L1)
    (e4 : wenger4Rel p P2 L2) (e5 : wenger4Rel p P3 L2)
    (e6 : wenger4Rel p P3 L3) (e7 : wenger4Rel p P4 L3)
    (e8 : wenger4Rel p P4 L4) (e9 : wenger4Rel p P0 L4) : False := by
  let x0 : ZMod p := P0 0
  let x1 : ZMod p := P1 0
  let x2 : ZMod p := P2 0
  let x3 : ZMod p := P3 0
  let x4 : ZMod p := P4 0
  let c0 : ZMod p := L0 0 - L4 0
  let c1 : ZMod p := L1 0 - L0 0
  let c2 : ZMod p := L2 0 - L1 0
  let c3 : ZMod p := L3 0 - L2 0
  let c4 : ZMod p := L4 0 - L3 0
  have hx01 : x0 ≠ x1 := fun h => hP01 (wenger4_pt_eq_of_zero_eq e0 e1 h)
  have hx12 : x1 ≠ x2 := fun h => hP12 (wenger4_pt_eq_of_zero_eq e2 e3 h)
  have hx23 : x2 ≠ x3 := fun h => hP23 (wenger4_pt_eq_of_zero_eq e4 e5 h)
  have hx34 : x3 ≠ x4 := fun h => hP34 (wenger4_pt_eq_of_zero_eq e6 e7 h)
  have hx40 : x4 ≠ x0 := fun h => hP40 (wenger4_pt_eq_of_zero_eq e8 e9 h)
  have hc0 : c0 ≠ 0 := fun h => hL40 (wenger4_line_eq_of_zero_eq e9 e0 (sub_eq_zero.mp h).symm)
  have hc1 : c1 ≠ 0 := fun h => hL01 (wenger4_line_eq_of_zero_eq e1 e2 (sub_eq_zero.mp h).symm)
  have hc2 : c2 ≠ 0 := fun h => hL12 (wenger4_line_eq_of_zero_eq e3 e4 (sub_eq_zero.mp h).symm)
  have hc3 : c3 ≠ 0 := fun h => hL23 (wenger4_line_eq_of_zero_eq e5 e6 (sub_eq_zero.mp h).symm)
  have hc4 : c4 ≠ 0 := fun h => hL34 (wenger4_line_eq_of_zero_eq e7 e8 (sub_eq_zero.mp h).symm)
  have hS0 : c0 + c1 + c2 + c3 + c4 = 0 := by
    dsimp only [c0, c1, c2, c3, c4]
    ring
  have hSk : ∀ j : Fin 4,
      c0 * x0 ^ (j.val + 1) + c1 * x1 ^ (j.val + 1) + c2 * x2 ^ (j.val + 1) +
        c3 * x3 ^ (j.val + 1) + c4 * x4 ^ (j.val + 1) = 0 := by
    intro j
    dsimp only [x0, x1, x2, x3, x4, c0, c1, c2, c3, c4]
    linear_combination
      -(e0 j) + (e1 j) - (e2 j) + (e3 j) - (e4 j) + (e5 j) - (e6 j) + (e7 j) - (e8 j) + (e9 j)
  have hS1 : c0 * x0 + c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 = 0 := by
    simpa using hSk 0
  have hS2 : c0 * x0 ^ 2 + c1 * x1 ^ 2 + c2 * x2 ^ 2 + c3 * x3 ^ 2 + c4 * x4 ^ 2 = 0 := by
    simpa using hSk 1
  have hS3 : c0 * x0 ^ 3 + c1 * x1 ^ 3 + c2 * x2 ^ 3 + c3 * x3 ^ 3 + c4 * x4 ^ 3 = 0 := by
    simpa using hSk 2
  have hS4 : c0 * x0 ^ 4 + c1 * x1 ^ 4 + c2 * x2 ^ 4 + c3 * x3 ^ 4 + c4 * x4 ^ 4 = 0 := by
    simpa using hSk 3
  have h0eq : x0 = x2 ∨ x0 = x3 := by
    by_contra h
    push Not at h
    exact five_vanish_elim hc0 hS0 hS1 hS2 hS3 hS4 hx01 h.1 h.2 hx40.symm
  have h1eq : x1 = x3 ∨ x1 = x4 := by
    by_contra h
    push Not at h
    exact five_vanish_elim (x0 := x1) (x1 := x2) (x2 := x3) (x3 := x4) (x4 := x0)
      (c0 := c1) (c1 := c2) (c2 := c3) (c3 := c4) (c4 := c0)
      hc1 (by linear_combination hS0) (by linear_combination hS1)
      (by linear_combination hS2) (by linear_combination hS3) (by linear_combination hS4)
      hx12 h.1 h.2 hx01.symm
  have h2eq : x2 = x4 ∨ x2 = x0 := by
    by_contra h
    push Not at h
    exact five_vanish_elim (x0 := x2) (x1 := x3) (x2 := x4) (x3 := x0) (x4 := x1)
      (c0 := c2) (c1 := c3) (c2 := c4) (c3 := c0) (c4 := c1)
      hc2 (by linear_combination hS0) (by linear_combination hS1)
      (by linear_combination hS2) (by linear_combination hS3) (by linear_combination hS4)
      hx23 h.1 h.2 hx12.symm
  have h3eq : x3 = x0 ∨ x3 = x1 := by
    by_contra h
    push Not at h
    exact five_vanish_elim (x0 := x3) (x1 := x4) (x2 := x0) (x3 := x1) (x4 := x2)
      (c0 := c3) (c1 := c4) (c2 := c0) (c3 := c1) (c4 := c2)
      hc3 (by linear_combination hS0) (by linear_combination hS1)
      (by linear_combination hS2) (by linear_combination hS3) (by linear_combination hS4)
      hx34 h.1 h.2 hx23.symm
  have h4eq : x4 = x1 ∨ x4 = x2 := by
    by_contra h
    push Not at h
    exact five_vanish_elim (x0 := x4) (x1 := x0) (x2 := x1) (x3 := x2) (x4 := x3)
      (c0 := c4) (c1 := c0) (c2 := c1) (c3 := c2) (c4 := c3)
      hc4 (by linear_combination hS0) (by linear_combination hS1)
      (by linear_combination hS2) (by linear_combination hS3) (by linear_combination hS4)
      hx40 h.1 h.2 hx34.symm
  rcases h0eq with h02 | h03
  · rcases h1eq with h13 | h14
    · rcases h4eq with h41 | h42
      · exact hx34 (h13.symm.trans h41.symm)
      · exact hx40 (h42.trans h02.symm)
    · rcases h3eq with h30 | h31
      · exact hx23 (h02.symm.trans h30.symm)
      · exact hx34 (h31.trans h14)
  · rcases h1eq with h13 | h14
    · exact hx01 (h03.trans h13.symm)
    · rcases h2eq with h24 | h20
      · exact hx12 (h14.trans h24.symm)
      · exact hx23 (h20.trans h03)

private lemma adj_inl_inl {p k : ℕ} {P : WFive p} {v : WVert4 p k}
    (h : (paddedWenger4 p k).Adj (Sum.inl (Sum.inl P)) v) :
    ∃ L : WFive p, v = Sum.inl (Sum.inr L) ∧ wenger4Rel p P L := by
  rcases v with (P' | L) | i
  · exact False.elim h
  · exact ⟨L, rfl, h⟩
  · exact False.elim h

private lemma adj_inl_inr {p k : ℕ} {L : WFive p} {v : WVert4 p k}
    (h : (paddedWenger4 p k).Adj (Sum.inl (Sum.inr L)) v) :
    ∃ P : WFive p, v = Sum.inl (Sum.inl P) ∧ wenger4Rel p P L := by
  rcases v with (P | L') | i
  · exact ⟨P, rfl, h⟩
  · exact False.elim h
  · exact False.elim h

private lemma paddedWenger4_cycle10_free (p k : ℕ) [Fact p.Prime] :
    (SimpleGraph.cycleGraph (2 * 5)).Free (paddedWenger4 p k) := by
  rintro ⟨f⟩
  have a01 : (paddedWenger4 p k).Adj (f.toHom 0) (f.toHom 1) := f.toHom.map_rel (by decide)
  have a12 : (paddedWenger4 p k).Adj (f.toHom 1) (f.toHom 2) := f.toHom.map_rel (by decide)
  have a23 : (paddedWenger4 p k).Adj (f.toHom 2) (f.toHom 3) := f.toHom.map_rel (by decide)
  have a34 : (paddedWenger4 p k).Adj (f.toHom 3) (f.toHom 4) := f.toHom.map_rel (by decide)
  have a45 : (paddedWenger4 p k).Adj (f.toHom 4) (f.toHom 5) := f.toHom.map_rel (by decide)
  have a56 : (paddedWenger4 p k).Adj (f.toHom 5) (f.toHom 6) := f.toHom.map_rel (by decide)
  have a67 : (paddedWenger4 p k).Adj (f.toHom 6) (f.toHom 7) := f.toHom.map_rel (by decide)
  have a78 : (paddedWenger4 p k).Adj (f.toHom 7) (f.toHom 8) := f.toHom.map_rel (by decide)
  have a89 : (paddedWenger4 p k).Adj (f.toHom 8) (f.toHom 9) := f.toHom.map_rel (by decide)
  have a90 : (paddedWenger4 p k).Adj (f.toHom 9) (f.toHom 0) := f.toHom.map_rel (by decide)
  have hne : ∀ (i j : Fin (2 * 5)), i ≠ j → f.toHom i ≠ f.toHom j :=
    fun _ _ hij h => hij (f.injective' h)
  cases h0 : f.toHom 0 with
  | inr i =>
    rw [h0] at a01
    cases h1 : f.toHom 1 <;> rw [h1] at a01 <;> exact a01
  | inl u0 =>
    cases u0 with
    | inl P0 =>
      obtain ⟨L0, h1, e0⟩ := adj_inl_inl (h0 ▸ a01)
      obtain ⟨P1, h2, e1⟩ := adj_inl_inr (h1 ▸ a12)
      obtain ⟨L1, h3, e2⟩ := adj_inl_inl (h2 ▸ a23)
      obtain ⟨P2, h4, e3⟩ := adj_inl_inr (h3 ▸ a34)
      obtain ⟨L2, h5, e4⟩ := adj_inl_inl (h4 ▸ a45)
      obtain ⟨P3, h6, e5⟩ := adj_inl_inr (h5 ▸ a56)
      obtain ⟨L3, h7, e6⟩ := adj_inl_inl (h6 ▸ a67)
      obtain ⟨P4, h8, e7⟩ := adj_inl_inr (h7 ▸ a78)
      obtain ⟨L4, h9, e8⟩ := adj_inl_inl (h8 ▸ a89)
      have e9 : wenger4Rel p P0 L4 := by rw [h9, h0] at a90; exact a90
      exact wenger4_no_ten_cycle P0 P1 P2 P3 P4 L0 L1 L2 L3 L4
        (fun h => hne 0 2 (by decide) (by rw [h0, h2, h]))
        (fun h => hne 2 4 (by decide) (by rw [h2, h4, h]))
        (fun h => hne 4 6 (by decide) (by rw [h4, h6, h]))
        (fun h => hne 6 8 (by decide) (by rw [h6, h8, h]))
        (fun h => hne 8 0 (by decide) (by rw [h8, h0, h]))
        (fun h => hne 1 3 (by decide) (by rw [h1, h3, h]))
        (fun h => hne 3 5 (by decide) (by rw [h3, h5, h]))
        (fun h => hne 5 7 (by decide) (by rw [h5, h7, h]))
        (fun h => hne 7 9 (by decide) (by rw [h7, h9, h]))
        (fun h => hne 9 1 (by decide) (by rw [h9, h1, h]))
        e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    | inr L4 =>
      obtain ⟨P0, h1, e9⟩ := adj_inl_inr (h0 ▸ a01)
      obtain ⟨L0, h2, e0⟩ := adj_inl_inl (h1 ▸ a12)
      obtain ⟨P1, h3, e1⟩ := adj_inl_inr (h2 ▸ a23)
      obtain ⟨L1, h4, e2⟩ := adj_inl_inl (h3 ▸ a34)
      obtain ⟨P2, h5, e3⟩ := adj_inl_inr (h4 ▸ a45)
      obtain ⟨L2, h6, e4⟩ := adj_inl_inl (h5 ▸ a56)
      obtain ⟨P3, h7, e5⟩ := adj_inl_inr (h6 ▸ a67)
      obtain ⟨L3, h8, e6⟩ := adj_inl_inl (h7 ▸ a78)
      obtain ⟨P4, h9, e7⟩ := adj_inl_inr (h8 ▸ a89)
      have e8 : wenger4Rel p P4 L4 := by rw [h9, h0] at a90; exact a90
      exact wenger4_no_ten_cycle P0 P1 P2 P3 P4 L0 L1 L2 L3 L4
        (fun h => hne 1 3 (by decide) (by rw [h1, h3, h]))
        (fun h => hne 3 5 (by decide) (by rw [h3, h5, h]))
        (fun h => hne 5 7 (by decide) (by rw [h5, h7, h]))
        (fun h => hne 7 9 (by decide) (by rw [h7, h9, h]))
        (fun h => hne 9 1 (by decide) (by rw [h9, h1, h]))
        (fun h => hne 2 4 (by decide) (by rw [h2, h4, h]))
        (fun h => hne 4 6 (by decide) (by rw [h4, h6, h]))
        (fun h => hne 6 8 (by decide) (by rw [h6, h8, h]))
        (fun h => hne 8 0 (by decide) (by rw [h8, h0, h]))
        (fun h => hne 0 2 (by decide) (by rw [h0, h2, h]))
        e0 e1 e2 e3 e4 e5 e6 e7 e8 e9

private lemma paddedWenger4_card_edgeFinset_ge (p k : ℕ) [NeZero p] :
    haveI : DecidableRel (paddedWenger4 p k).Adj := Classical.decRel _
    p ^ 6 ≤ (paddedWenger4 p k).edgeFinset.card := by
  classical
  let mkL : WFive p → ZMod p → WFive p := fun P l0 =>
    Fin.cons l0 (fun j : Fin 4 => P 0 ^ (j.val + 1) * l0 - P j.succ)
  let edgeMap : WFive p × ZMod p → Sym2 (WVert4 p k) := fun ⟨P, l0⟩ =>
    s(Sum.inl (Sum.inl P), Sum.inl (Sum.inr (mkL P l0)))
  have hinj : Function.Injective edgeMap := by
    rintro ⟨P, l0⟩ ⟨P', l0'⟩ h
    simp only [edgeMap, Sym2.eq_iff] at h
    rcases h with ⟨hP, hL⟩ | ⟨hbad, _⟩
    · injection hP with hP1
      injection hP1 with hP2
      injection hL with hL1
      injection hL1 with hL2
      have hl0 : l0 = l0' := by
        have := congrFun hL2 0
        simpa [mkL] using this
      exact Prod.ext hP2 hl0
    · injection hbad with hbad1
      cases hbad1
  have hsub : Finset.univ.image edgeMap ⊆ (paddedWenger4 p k).edgeFinset := by
    intro e he
    obtain ⟨⟨P, l0⟩, _, rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset]
    change wenger4Rel p P (mkL P l0)
    intro j
    simp only [mkL, Fin.cons_succ, Fin.cons_zero]
    ring
  have hcard : (Finset.univ.image edgeMap).card = p ^ 6 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp [WFive, ZMod.card]
    ring
  rw [← hcard]
  exact Finset.card_le_card hsub

private lemma wvert4_card (p n : ℕ) [NeZero p] (h : 2 * p ^ 5 ≤ n) :
    Fintype.card (WVert4 p (n - 2 * p ^ 5)) = n := by
  simp only [WVert4, WFive, Fintype.card_sum, Fintype.card_pi, Fintype.card_fin, ZMod.card,
    Finset.prod_const, Finset.card_univ]
  have h5 : p ^ 5 + p ^ 5 = 2 * p ^ 5 := by ring
  omega

theorem OMA.solution : OMA.R_Erdos572_erdos_572_R1.H2 := by
  refine ⟨1 / 256, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨64, fun n hn => ?_⟩
  have hn64 : (1 : ℝ) ≤ (n : ℝ) / 64 := by
    have : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let y : ℝ := ((n : ℝ) / 64) ^ (1 / 5 : ℝ)
  have hy_ge_one : 1 ≤ y := Real.one_le_rpow hn64 (by positivity)
  let m : ℕ := Nat.floor y
  have hm_pos : 1 ≤ m := Nat.floor_pos.mpr hy_ge_one
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2p5 : 2 * p ^ 5 ≤ n := by
    have hm_le : (m : ℝ) ≤ y := Nat.floor_le (by positivity)
    have hm5 : (m : ℝ) ^ 5 ≤ (n : ℝ) / 64 := by
      calc (m : ℝ) ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le 5
        _ = (n : ℝ) / 64 := by
            dsimp only [y]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
    have h64m5 : 64 * m ^ 5 ≤ n := by
      have : (64 * (m : ℝ) ^ 5) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hp5 : p ^ 5 ≤ (2 * m) ^ 5 := Nat.pow_le_pow_left hp2m 5
    have h2 : 2 * (2 * m) ^ 5 = 64 * m ^ 5 := by ring
    omega
  have hp6_le_ex : p ^ 6 ≤ SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 5)) := by
    classical
    have h1 := paddedWenger4_card_edgeFinset_ge p (n - 2 * p ^ 5)
    have h2 := SimpleGraph.card_edgeFinset_le_extremalNumber
      (paddedWenger4_cycle10_free p (n - 2 * p ^ 5))
    rw [wvert4_card p n h2p5] at h2
    exact le_trans h1 h2
  have hy_lt_p : y < (p : ℝ) := by
    have h1 : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : (m : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hmp
    linarith
  have hn64_le_p5 : (n : ℝ) / 64 ≤ (p : ℝ) ^ 5 := by
    have h5 : y ^ 5 ≤ (p : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hy_lt_p.le 5
    have hy5 : y ^ 5 = (n : ℝ) / 64 := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have hmain : (1 / 256 : ℝ) * (n : ℝ) ^ (1 + 1 / (5 : ℝ)) ≤ (p : ℝ) ^ 6 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by positivity)
    have hlhs : ((1 / 256 : ℝ) * (n : ℝ) ^ (1 + 1 / (5 : ℝ))) ^ 5 =
        (1 / 256 ^ 5 : ℝ) * (n : ℝ) ^ 6 := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 + 1 / (5 : ℝ))) 5,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    have hrhs : ((p : ℝ) ^ 6) ^ 5 = ((p : ℝ) ^ 5) ^ 6 := by ring
    rw [hlhs, hrhs]
    have hpow6 : ((n : ℝ) / 64) ^ 6 ≤ ((p : ℝ) ^ 5) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hn64_le_p5 6
    have hdiv : ((n : ℝ) / 64) ^ 6 = (1 / 64 ^ 6 : ℝ) * (n : ℝ) ^ 6 := by ring
    rw [hdiv] at hpow6
    have hconst : (1 / 256 ^ 5 : ℝ) * (n : ℝ) ^ 6 ≤ (1 / 64 ^ 6 : ℝ) * (n : ℝ) ^ 6 := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
      nlinarith
    exact le_trans hconst hpow6
  have hp6_le_exR : (p : ℝ) ^ 6 ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 5)) : ℝ) := by
    exact_mod_cast hp6_le_ex
  exact le_trans hmain hp6_le_exR
