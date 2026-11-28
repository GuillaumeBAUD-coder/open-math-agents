import OMAReductions.R_Erdos572_erdos_572_R1
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Step Erdos572.erdos_572.R1.H1: hypothesis H1 of reduction Erdos572.erdos_572.R1
-- Credit: @yhay81
-- uses note #156918
-- H1 := ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,     c * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤       (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 3)) : ℝ)

open Filter SimpleGraph

private abbrev WTriple (p : ℕ) := ZMod p × ZMod p × ZMod p

private abbrev WVert (p k : ℕ) := (WTriple p ⊕ WTriple p) ⊕ Fin k

private def wengerRel (p : ℕ) (P L : WTriple p) : Prop :=
  P.2.1 + L.2.1 = P.1 * L.1 ∧ P.2.2 + L.2.2 = P.1 ^ 2 * L.1

private def paddedWenger (p k : ℕ) : SimpleGraph (WVert p k) where
  Adj u v :=
    match u, v with
    | Sum.inl (Sum.inl P), Sum.inl (Sum.inr L) => wengerRel p P L
    | Sum.inl (Sum.inr L), Sum.inl (Sum.inl P) => wengerRel p P L
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

private lemma wenger_pt_eq_of_fst_eq {p : ℕ} {P P' L : WTriple p}
    (h1 : wengerRel p P L) (h2 : wengerRel p P' L) (hfst : P.1 = P'.1) : P = P' := by
  rcases P with ⟨x, y, z⟩
  rcases P' with ⟨x', y', z'⟩
  rcases L with ⟨a, b, c⟩
  dsimp only [wengerRel] at h1 h2 hfst
  subst hfst
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · linear_combination h1.1 - h2.1
  · linear_combination h1.2 - h2.2

private lemma wenger_line_eq_of_fst_eq {p : ℕ} {P L L' : WTriple p}
    (h1 : wengerRel p P L) (h2 : wengerRel p P L') (hfst : L.1 = L'.1) : L = L' := by
  rcases P with ⟨x, y, z⟩
  rcases L with ⟨a, b, c⟩
  rcases L' with ⟨a', b', c'⟩
  dsimp only [wengerRel] at h1 h2 hfst
  subst hfst
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · linear_combination h1.1 - h2.1
  · linear_combination h1.2 - h2.2

private lemma wenger_no_six_cycle {p : ℕ} [Fact p.Prime]
    (P1 P2 P3 L1 L2 L3 : WTriple p)
    (hP23 : P2 ≠ P3) (hP31 : P3 ≠ P1) (hL23 : L2 ≠ L3)
    (e1 : wengerRel p P1 L1) (e2 : wengerRel p P2 L1)
    (e3 : wengerRel p P2 L2) (e4 : wengerRel p P3 L2)
    (e5 : wengerRel p P3 L3) (e6 : wengerRel p P1 L3) : False := by
  have hx23 : P2.1 ≠ P3.1 := fun h => hP23 (wenger_pt_eq_of_fst_eq e3 e4 h)
  have hx31 : P3.1 ≠ P1.1 := fun h => hP31 (wenger_pt_eq_of_fst_eq e5 e6 h)
  have ha23 : L2.1 ≠ L3.1 := fun h => hL23 (wenger_line_eq_of_fst_eq e4 e5 h)
  have hE1 : (P1.1 - P2.1) * L1.1 + (P2.1 - P3.1) * L2.1 + (P3.1 - P1.1) * L3.1 = 0 := by
    linear_combination -e1.1 + e2.1 - e3.1 + e4.1 - e5.1 + e6.1
  have hE2 : (P1.1 ^ 2 - P2.1 ^ 2) * L1.1 + (P2.1 ^ 2 - P3.1 ^ 2) * L2.1 +
      (P3.1 ^ 2 - P1.1 ^ 2) * L3.1 = 0 := by
    linear_combination -e1.2 + e2.2 - e3.2 + e4.2 - e5.2 + e6.2
  have hprod : (P2.1 - P3.1) * (P3.1 - P1.1) * (L2.1 - L3.1) = 0 := by
    linear_combination hE2 - (P1.1 + P2.1) * hE1
  rcases mul_eq_zero.mp hprod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact hx23 (sub_eq_zero.mp h1)
    · exact hx31 (sub_eq_zero.mp h2)
  · exact ha23 (sub_eq_zero.mp h3)

private lemma paddedWenger_cycle6_free (p k : ℕ) [Fact p.Prime] :
    (SimpleGraph.cycleGraph (2 * 3)).Free (paddedWenger p k) := by
  rintro ⟨f⟩
  have a01 : (paddedWenger p k).Adj (f.toHom 0) (f.toHom 1) := f.toHom.map_rel (by decide)
  have a12 : (paddedWenger p k).Adj (f.toHom 1) (f.toHom 2) := f.toHom.map_rel (by decide)
  have a23 : (paddedWenger p k).Adj (f.toHom 2) (f.toHom 3) := f.toHom.map_rel (by decide)
  have a34 : (paddedWenger p k).Adj (f.toHom 3) (f.toHom 4) := f.toHom.map_rel (by decide)
  have a45 : (paddedWenger p k).Adj (f.toHom 4) (f.toHom 5) := f.toHom.map_rel (by decide)
  have a50 : (paddedWenger p k).Adj (f.toHom 5) (f.toHom 0) := f.toHom.map_rel (by decide)
  have hne : ∀ (i j : Fin (2 * 3)), i ≠ j → f.toHom i ≠ f.toHom j :=
    fun _ _ hij h => hij (f.injective' h)
  cases h0 : f.toHom 0 with
  | inr i =>
    rw [h0] at a01
    cases h1 : f.toHom 1 <;> rw [h1] at a01 <;> exact a01
  | inl u0 =>
    cases u0 with
    | inl P1 =>
      cases h1 : f.toHom 1 with
      | inr i => rw [h0, h1] at a01; exact a01
      | inl u1 =>
        cases u1 with
        | inl Q => rw [h0, h1] at a01; exact a01
        | inr L1 =>
          cases h2 : f.toHom 2 with
          | inr i => rw [h1, h2] at a12; exact a12
          | inl u2 =>
            cases u2 with
            | inr Q => rw [h1, h2] at a12; exact a12
            | inl P2 =>
              cases h3 : f.toHom 3 with
              | inr i => rw [h2, h3] at a23; exact a23
              | inl u3 =>
                cases u3 with
                | inl Q => rw [h2, h3] at a23; exact a23
                | inr L2 =>
                  cases h4 : f.toHom 4 with
                  | inr i => rw [h3, h4] at a34; exact a34
                  | inl u4 =>
                    cases u4 with
                    | inr Q => rw [h3, h4] at a34; exact a34
                    | inl P3 =>
                      cases h5 : f.toHom 5 with
                      | inr i => rw [h4, h5] at a45; exact a45
                      | inl u5 =>
                        cases u5 with
                        | inl Q => rw [h4, h5] at a45; exact a45
                        | inr L3 =>
                          rw [h0, h1] at a01
                          rw [h1, h2] at a12
                          rw [h2, h3] at a23
                          rw [h3, h4] at a34
                          rw [h4, h5] at a45
                          rw [h5, h0] at a50
                          have hP23 : P2 ≠ P3 := fun h =>
                            hne 2 4 (by decide) (by rw [h2, h4, h])
                          have hP31 : P3 ≠ P1 := fun h =>
                            hne 4 0 (by decide) (by rw [h4, h0, h])
                          have hL23 : L2 ≠ L3 := fun h =>
                            hne 3 5 (by decide) (by rw [h3, h5, h])
                          exact wenger_no_six_cycle P1 P2 P3 L1 L2 L3 hP23 hP31 hL23
                            a01 a12 a23 a34 a45 a50
    | inr L3 =>
      cases h1 : f.toHom 1 with
      | inr i => rw [h0, h1] at a01; exact a01
      | inl u1 =>
        cases u1 with
        | inr Q => rw [h0, h1] at a01; exact a01
        | inl P1 =>
          cases h2 : f.toHom 2 with
          | inr i => rw [h1, h2] at a12; exact a12
          | inl u2 =>
            cases u2 with
            | inl Q => rw [h1, h2] at a12; exact a12
            | inr L1 =>
              cases h3 : f.toHom 3 with
              | inr i => rw [h2, h3] at a23; exact a23
              | inl u3 =>
                cases u3 with
                | inr Q => rw [h2, h3] at a23; exact a23
                | inl P2 =>
                  cases h4 : f.toHom 4 with
                  | inr i => rw [h3, h4] at a34; exact a34
                  | inl u4 =>
                    cases u4 with
                    | inl Q => rw [h3, h4] at a34; exact a34
                    | inr L2 =>
                      cases h5 : f.toHom 5 with
                      | inr i => rw [h4, h5] at a45; exact a45
                      | inl u5 =>
                        cases u5 with
                        | inr Q => rw [h4, h5] at a45; exact a45
                        | inl P3 =>
                          rw [h0, h1] at a01
                          rw [h1, h2] at a12
                          rw [h2, h3] at a23
                          rw [h3, h4] at a34
                          rw [h4, h5] at a45
                          rw [h5, h0] at a50
                          have hP23 : P2 ≠ P3 := fun h =>
                            hne 3 5 (by decide) (by rw [h3, h5, h])
                          have hP31 : P3 ≠ P1 := fun h =>
                            hne 5 1 (by decide) (by rw [h5, h1, h])
                          have hL23 : L2 ≠ L3 := fun h =>
                            hne 4 0 (by decide) (by rw [h4, h0, h])
                          exact wenger_no_six_cycle P1 P2 P3 L1 L2 L3 hP23 hP31 hL23
                            a12 a23 a34 a45 a50 a01

private lemma paddedWenger_card_edgeFinset_ge (p k : ℕ) [NeZero p] :
    haveI : DecidableRel (paddedWenger p k).Adj := Classical.decRel _
    p ^ 4 ≤ (paddedWenger p k).edgeFinset.card := by
  classical
  let edgeMap : WTriple p × ZMod p → Sym2 (WVert p k) := fun ⟨P, l1⟩ =>
    s(Sum.inl (Sum.inl P), Sum.inl (Sum.inr (l1, P.1 * l1 - P.2.1, P.1 ^ 2 * l1 - P.2.2)))
  have hinj : Function.Injective edgeMap := by
    rintro ⟨P, l1⟩ ⟨P', l1'⟩ h
    simp only [edgeMap, Sym2.eq_iff] at h
    rcases h with ⟨hP, hL⟩ | ⟨hbad, _⟩
    · injection hP with hP1
      injection hP1 with hP2
      injection hL with hL1
      injection hL1 with hL2
      exact Prod.ext hP2 (congrArg Prod.fst hL2)
    · injection hbad with hbad1
      cases hbad1
  have hsub : Finset.univ.image edgeMap ⊆ (paddedWenger p k).edgeFinset := by
    intro e he
    obtain ⟨⟨P, l1⟩, _, rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset]
    change wengerRel p P (l1, P.1 * l1 - P.2.1, P.1 ^ 2 * l1 - P.2.2)
    constructor <;> dsimp only <;> ring
  have hcard : (Finset.univ.image edgeMap).card = p ^ 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp [WTriple, ZMod.card]
    ring
  rw [← hcard]
  exact Finset.card_le_card hsub

private lemma wvert_card (p n : ℕ) [NeZero p] (h : 2 * p ^ 3 ≤ n) :
    Fintype.card (WVert p (n - 2 * p ^ 3)) = n := by
  simp only [WVert, WTriple, Fintype.card_sum, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  have h3 : p * (p * p) + p * (p * p) = 2 * p ^ 3 := by ring
  omega

theorem OMA.solution : OMA.R_Erdos572_erdos_572_R1.H1 := by
  refine ⟨1 / 64, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨16, fun n hn => ?_⟩
  have hn16 : (1 : ℝ) ≤ (n : ℝ) / 16 := by
    have : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let y : ℝ := ((n : ℝ) / 16) ^ (1 / 3 : ℝ)
  have hy_ge_one : 1 ≤ y := Real.one_le_rpow hn16 (by positivity)
  let m : ℕ := Nat.floor y
  have hm_pos : 1 ≤ m := Nat.floor_pos.mpr hy_ge_one
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2p3 : 2 * p ^ 3 ≤ n := by
    have hm_le : (m : ℝ) ≤ y := Nat.floor_le (by positivity)
    have hm3 : (m : ℝ) ^ 3 ≤ (n : ℝ) / 16 := by
      calc (m : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le 3
        _ = (n : ℝ) / 16 := by
            dsimp only [y]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
    have h16m3 : 16 * m ^ 3 ≤ n := by
      have : (16 * (m : ℝ) ^ 3) ≤ (n : ℝ) := by linarith
      exact_mod_cast this
    have hp3 : p ^ 3 ≤ (2 * m) ^ 3 := Nat.pow_le_pow_left hp2m 3
    have h2 : 2 * (2 * m) ^ 3 = 16 * m ^ 3 := by ring
    omega
  have hp4_le_ex : p ^ 4 ≤ SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 3)) := by
    classical
    have h1 := paddedWenger_card_edgeFinset_ge p (n - 2 * p ^ 3)
    have h2 := SimpleGraph.card_edgeFinset_le_extremalNumber
      (paddedWenger_cycle6_free p (n - 2 * p ^ 3))
    rw [wvert_card p n h2p3] at h2
    exact le_trans h1 h2
  have hy_lt_p : y < (p : ℝ) := by
    have h1 : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : (m : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hmp
    linarith
  have hn16_le_p3 : (n : ℝ) / 16 ≤ (p : ℝ) ^ 3 := by
    have h3 : y ^ 3 ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hy_lt_p.le 3
    have hy3 : y ^ 3 = (n : ℝ) / 16 := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have hmain : (1 / 64 : ℝ) * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤ (p : ℝ) ^ 4 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by positivity)
    have hlhs : ((1 / 64 : ℝ) * (n : ℝ) ^ (1 + 1 / (3 : ℝ))) ^ 3 =
        (1 / 64 ^ 3 : ℝ) * (n : ℝ) ^ 4 := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 + 1 / (3 : ℝ))) 3,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    have hrhs : ((p : ℝ) ^ 4) ^ 3 = ((p : ℝ) ^ 3) ^ 4 := by ring
    rw [hlhs, hrhs]
    have hpow4 : ((n : ℝ) / 16) ^ 4 ≤ ((p : ℝ) ^ 3) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hn16_le_p3 4
    have hdiv : ((n : ℝ) / 16) ^ 4 = (1 / 16 ^ 4 : ℝ) * (n : ℝ) ^ 4 := by ring
    rw [hdiv] at hpow4
    have hconst : (1 / 64 ^ 3 : ℝ) * (n : ℝ) ^ 4 ≤ (1 / 16 ^ 4 : ℝ) * (n : ℝ) ^ 4 := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
      nlinarith
    exact le_trans hconst hpow4
  have hp4_le_exR : (p : ℝ) ^ 4 ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 3)) : ℝ) := by
    exact_mod_cast hp4_le_ex
  exact le_trans hmain hp4_le_exR
