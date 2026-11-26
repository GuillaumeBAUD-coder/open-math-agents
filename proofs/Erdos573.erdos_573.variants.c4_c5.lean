import FormalConjectures.ErdosProblems.«573»
import Mathlib.Analysis.MeanInequalities
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The Erdős–Simonovits upper bound for forbidding four- and five-cycles. -/

open Finset SimpleGraph
open scoped BigOperators

private theorem cycle_four {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : cycleGraph 4 ⊑ G := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  apply (cycleGraph_isContained_iff (by decide : 2 < 4)).mpr
  refine ⟨a, p, ?_, rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, by simp [p]⟩
  simp [p, Walk.isPath_def, hab.ne, hbc.ne, hcd.ne, hda.ne, hac, hbd, ne_comm]

private theorem cycle_five {V : Type*} {G : SimpleGraph V} {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hea : G.Adj e a) (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d)
    (hbe : b ≠ e) (hce : c ≠ e) : cycleGraph 5 ⊑ G := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))))
  apply (cycleGraph_isContained_iff (by decide : 2 < 5)).mpr
  refine ⟨a, p, ?_, rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, by simp [p]⟩
  simp [p, Walk.isPath_def, hab.ne, hbc.ne, hcd.ne, hde.ne, hea.ne,
    hac, had, hbd, hbe, hce, ne_comm]

section Counts

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def common (u v : V) : Finset V :=
  (G.neighborFinset u).filter (G.Adj v)

omit [DecidableEq V] in private theorem mem_common {u v w : V} : w ∈ common G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [common]

omit [DecidableEq V] in private theorem common_symm (u v : V) : common G u v = common G v u := by
  ext w
  simp only [mem_common, and_comm]

private theorem card_common_le_one (h4 : (cycleGraph 4).Free G) {u v : V}
    (huv : u ≠ v) : (common G u v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨hua, hva⟩ := (mem_common G).mp ha
  obtain ⟨hub, hvb⟩ := (mem_common G).mp hb
  by_contra hab
  exact h4 (cycle_four hua hva.symm hvb hub.symm huv hab)

private def pairSlot (w : V) : V ↪ V × V :=
  ⟨Prod.mk w, fun _ _ h => congrArg Prod.snd h⟩

private def pairFibers (s : Finset V) (F : V → Finset V) : Finset (V × V) :=
  s.biUnion fun w => (F w).map (pairSlot w)

omit [Fintype V] in private theorem mem_pairFibers {s : Finset V} {F : V → Finset V} {p : V × V} :
    p ∈ pairFibers s F ↔ p.1 ∈ s ∧ p.2 ∈ F p.1 := by
  rcases p with ⟨a, b⟩
  simp only [pairFibers, mem_biUnion, mem_map]
  constructor
  · rintro ⟨w, hw, z, hz, heq⟩
    change (w, z) = (a, b) at heq
    cases heq
    exact ⟨hw, hz⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

omit [Fintype V] in private theorem card_pairFibers (s : Finset V) (F : V → Finset V) :
    (pairFibers s F).card = ∑ w ∈ s, (F w).card := by
  have hdisj : (s : Set V).PairwiseDisjoint (fun w => (F w).map (pairSlot w)) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun p ha hb => ?_
    obtain ⟨x, _, rfl⟩ := mem_map.mp ha
    obtain ⟨y, _, hy⟩ := mem_map.mp hb
    exact hab (congrArg Prod.fst hy).symm
  simp [pairFibers, Finset.card_biUnion hdisj]

private def extensions (v : V) : Finset (V × V) :=
  pairFibers (G.neighborFinset v) (fun w => G.neighborFinset w)

private def goodExtensions (u v : V) : Finset (V × V) :=
  (extensions G v).filter fun p => p.1 ≠ u ∧ p.2 ≠ v ∧ ¬ G.Adj u p.1

private theorem mem_goodExtensions {u v : V} {p : V × V} :
    p ∈ goodExtensions G u v ↔
      G.Adj v p.1 ∧ G.Adj p.1 p.2 ∧ p.1 ≠ u ∧ p.2 ≠ v ∧ ¬ G.Adj u p.1 := by
  simp only [goodExtensions, extensions, mem_filter, mem_pairFibers, mem_neighborFinset, and_assoc]

private theorem good_endpoint_injective (h4 : (cycleGraph 4).Free G) (u v : V) :
    (goodExtensions G u v : Set (V × V)).InjOn Prod.snd := by
  intro p hp q hq he
  obtain ⟨hvp, hpp, _, hpv, _⟩ := (mem_goodExtensions G).mp hp
  obtain ⟨hvq, hqq, _, _, _⟩ := (mem_goodExtensions G).mp hq
  apply Prod.ext _ he
  by_contra hne
  exact h4 (cycle_four hvp hpp (he.symm ▸ hqq.symm) hvq.symm hpv.symm hne)

private theorem good_endpoint_disjoint (h5 : (cycleGraph 5).Free G) {u v : V}
    (huv : G.Adj u v) :
    Disjoint ((goodExtensions G u v).image Prod.snd) ((goodExtensions G v u).image Prod.snd) := by
  refine Finset.disjoint_left.mpr fun x h₁ h₂ => ?_
  obtain ⟨⟨a, y⟩, hya, rfl⟩ := mem_image.mp h₁
  obtain ⟨⟨b, z⟩, hzb, hz⟩ := mem_image.mp h₂
  change z = y at hz
  subst z
  obtain ⟨hva, hay, hau, hyv, hno⟩ := (mem_goodExtensions G).mp hya
  obtain ⟨hub, hby, hbv, hyu, _⟩ := (mem_goodExtensions G).mp hzb
  have hab : a ≠ b := fun h => hno (h ▸ hub)
  exact h5 (cycle_five huv hva hay hby.symm hub.symm hau.symm hyu.symm hyv.symm hbv.symm hab)

private theorem card_good_pair_le (h4 : (cycleGraph 4).Free G) (h5 : (cycleGraph 5).Free G)
    {u v : V} (huv : G.Adj u v) :
    (goodExtensions G u v).card + (goodExtensions G v u).card ≤ Fintype.card V := by
  rw [← card_image_of_injOn (good_endpoint_injective G h4 u v),
    ← card_image_of_injOn (good_endpoint_injective G h4 v u),
    ← card_union_of_disjoint (good_endpoint_disjoint G h5 huv)]
  exact card_le_univ _

private theorem card_extensions_le (u v : V) :
    (extensions G v).card ≤ (goodExtensions G u v).card + G.degree u + G.degree v +
      ∑ w ∈ common G u v, G.degree w := by
  let backtrack := pairFibers {u} (fun w => G.neighborFinset w)
  let repeatedEnd := pairFibers (G.neighborFinset v) (fun _ => {v})
  let throughCommon := pairFibers (common G u v) (fun w => G.neighborFinset w)
  have hsubset : extensions G v ⊆ goodExtensions G u v ∪
      (backtrack ∪ (repeatedEnd ∪ throughCommon)) := by
    intro p hp
    simp only [extensions, mem_pairFibers, mem_neighborFinset] at hp
    simp only [mem_union, mem_goodExtensions, backtrack, repeatedEnd, throughCommon,
      mem_pairFibers, mem_neighborFinset, mem_common, mem_singleton]
    tauto
  have h₁ := card_le_card hsubset
  have h₂ := card_union_le (goodExtensions G u v) (backtrack ∪ (repeatedEnd ∪ throughCommon))
  have h₃ := card_union_le backtrack (repeatedEnd ∪ throughCommon)
  have h₄ := card_union_le repeatedEnd throughCommon
  have h₅ : backtrack.card = G.degree u := by simp [backtrack, card_pairFibers]
  have h₆ : repeatedEnd.card = G.degree v := by simp [repeatedEnd, card_pairFibers]
  have h₇ : throughCommon.card = ∑ w ∈ common G u v, G.degree w := by
    simp [throughCommon, card_pairFibers]
  omega

private theorem card_extension_pair_le (h4 : (cycleGraph 4).Free G) (h5 : (cycleGraph 5).Free G)
    {u v : V} (huv : G.Adj u v) :
    (extensions G v).card + (extensions G u).card ≤ Fintype.card V +
      2 * (G.degree u + G.degree v) + 2 * (∑ w ∈ common G u v, G.degree w) := by
  have h₁ := card_extensions_le G u v
  have h₂ := card_extensions_le G v u
  rw [common_symm G v u] at h₂
  have h₃ := card_good_pair_le G h4 h5 huv
  omega

omit [DecidableEq V] in private theorem sum_neighbors_comm {R : Type*} [AddCommMonoid R] (f : V → V → R) :
    (∑ u, ∑ v ∈ G.neighborFinset u, f u v) =
      ∑ v, ∑ u ∈ G.neighborFinset v, f u v := by
  simp_rw [neighborFinset_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : G.Adj u v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun e => h e.symm)]

private theorem card_extensions_eq_sum_common (u : V) :
    (extensions G u).card = ∑ v, (common G u v).card := by
  rw [extensions, card_pairFibers]
  calc
    (∑ w ∈ G.neighborFinset u, (G.neighborFinset w).card) =
        ∑ w ∈ G.neighborFinset u, ∑ v, if G.Adj w v then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro w _
      simp only [Finset.sum_boole, Nat.cast_id, neighborFinset_eq_filter]
    _ = ∑ v, ∑ w ∈ G.neighborFinset u, if G.Adj v w then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro w _
      by_cases h : G.Adj w v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun e => h e.symm)]
    _ = ∑ v, (common G u v).card := by simp [common]

private theorem sum_degree_sq_le (h4 : (cycleGraph 4).Free G) :
    (∑ u, G.degree u ^ 2) ≤ 2 * (Fintype.card V) ^ 2 := by
  let n := Fintype.card V
  have hsum : (∑ u, G.degree u) ≤ n * n := by
    calc
      _ ≤ ∑ _ : V, n := sum_le_sum fun u _ => (G.degree_lt_card_verts u).le
      _ = _ := by simp [n]
  have hsame (u : V) : common G u u = G.neighborFinset u := by
    ext v
    simp [mem_common]
  have hrow (u : V) : (extensions G u).card ≤ n + G.degree u := by
    rw [card_extensions_eq_sum_common]
    calc
      _ ≤ ∑ v : V, (1 + if v = u then G.degree u else 0) := by
        apply sum_le_sum
        intro v _
        by_cases h : v = u
        · subst v
          simp [hsame]
        · simpa only [if_neg h, add_zero] using card_common_le_one G h4 (Ne.symm h)
      _ = _ := by simp [Finset.sum_add_distrib, n]
  calc
    (∑ u, G.degree u ^ 2) = ∑ u, ∑ _ ∈ G.neighborFinset u, G.degree u := by
      simp [pow_two]
    _ = ∑ v, ∑ u ∈ G.neighborFinset v, G.degree u := sum_neighbors_comm G fun u _ => G.degree u
    _ = ∑ v, (extensions G v).card := by simp [extensions, card_pairFibers]
    _ ≤ ∑ u, (n + G.degree u) := sum_le_sum fun u _ => hrow u
    _ ≤ 2 * n ^ 2 := by
      rw [Finset.sum_add_distrib]
      have hconst : (∑ _ : V, n) = n * n := by simp [n]
      rw [hconst, pow_two]
      omega

private theorem sum_common_degrees_le (h4 : (cycleGraph 4).Free G) :
    (∑ u, ∑ v ∈ G.neighborFinset u, ∑ w ∈ common G u v, G.degree w) ≤
      ∑ w, G.degree w ^ 2 := by
  have hreorder (u : V) :
      (∑ v ∈ G.neighborFinset u, ∑ w ∈ common G u v, G.degree w) =
        ∑ w ∈ G.neighborFinset u, ∑ v ∈ common G u w, G.degree w := by
    simp_rw [common, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro w _
    apply sum_congr rfl
    intro v _
    by_cases h : G.Adj v w
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun e => h e.symm)]
  calc
    _ = ∑ u, ∑ w ∈ G.neighborFinset u, ∑ v ∈ common G u w, G.degree w :=
      sum_congr rfl (fun u _ => hreorder u)
    _ = ∑ w, ∑ u ∈ G.neighborFinset w, ∑ v ∈ common G u w, G.degree w :=
      sum_neighbors_comm G (fun u w => ∑ v ∈ common G u w, G.degree w)
    _ ≤ ∑ w, ∑ _ ∈ G.neighborFinset w, G.degree w := by
      apply sum_le_sum
      intro w _
      apply sum_le_sum
      intro u hu
      have hwu : w ≠ u := ((G.mem_neighborFinset _ _).mp hu).ne
      have hcard := card_common_le_one G h4 hwu.symm
      simpa [nsmul_eq_mul] using Nat.mul_le_mul_right (G.degree w) hcard
    _ = _ := by simp [pow_two]

private theorem three_walk_count_upper (h4 : (cycleGraph 4).Free G)
    (h5 : (cycleGraph 5).Free G) :
    (∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v) ≤
      G.edgeFinset.card * Fintype.card V + 6 * (Fintype.card V) ^ 2 := by
  let n := Fintype.card V
  let W := ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v
  let D := ∑ u, G.degree u ^ 2
  let A := ∑ u, ∑ v ∈ G.neighborFinset u, ∑ w ∈ common G u v, G.degree w
  have hstart : (∑ u, ∑ _ ∈ G.neighborFinset u, (extensions G u).card) = W := by
    simp [extensions, card_pairFibers, W, Finset.mul_sum]
  have hend : (∑ u, ∑ v ∈ G.neighborFinset u, (extensions G v).card) = W :=
    (sum_neighbors_comm G fun _ v => (extensions G v).card).trans hstart
  have hconst : (∑ u, ∑ _ ∈ G.neighborFinset u, n) = 2 * G.edgeFinset.card * n := by
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, card_neighborFinset_eq_degree,
      ← Finset.sum_mul, sum_degrees_eq_twice_card_edges]
  have hdegree_start : (∑ u, ∑ _ ∈ G.neighborFinset u, G.degree u) = D := by
    simp [D, pow_two]
  have hdegree_end : (∑ u, ∑ v ∈ G.neighborFinset u, G.degree v) = D :=
    (sum_neighbors_comm G fun _ v => G.degree v).trans hdegree_start
  have hpair :
      (∑ u, ∑ v ∈ G.neighborFinset u, ((extensions G v).card + (extensions G u).card)) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u,
          (n + 2 * (G.degree u + G.degree v) + 2 * (∑ w ∈ common G u v, G.degree w)) :=
    sum_le_sum fun u _ => sum_le_sum fun v hv =>
      card_extension_pair_le G h4 h5 ((G.mem_neighborFinset _ _).mp hv)
  have hleft :
      (∑ u, ∑ v ∈ G.neighborFinset u, ((extensions G v).card + (extensions G u).card)) =
        2 * W := by
    rw [two_mul]
    simp only [sum_add_distrib, hstart, hend]
  have hright :
      (∑ u, ∑ v ∈ G.neighborFinset u,
        (n + 2 * (G.degree u + G.degree v) + 2 * (∑ w ∈ common G u v, G.degree w))) =
        2 * G.edgeFinset.card * n + 4 * D + 2 * A := by
    simp_rw [mul_add, sum_add_distrib, ← Finset.mul_sum]
    rw [hconst, hdegree_start, hdegree_end]
    change 2 * G.edgeFinset.card * n + (2 * D + 2 * D) + 2 * A = _
    ring
  rw [hleft, hright, Nat.mul_assoc 2] at hpair
  clear hstart hend hconst hdegree_start hdegree_end hleft hright
  have hA : A ≤ D := sum_common_degrees_le G h4
  have hD : D ≤ 2 * n ^ 2 := sum_degree_sq_le G h4
  change W ≤ G.edgeFinset.card * n + 6 * n ^ 2
  omega

end Counts

lemma OMA.threeFactorCardCube {ι : Type*} (s : Finset ι) (f g h : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) (hh : ∀ i ∈ s, 0 < h i)
    (hone : ∀ i ∈ s, f i * g i * h i = 1) :
    (s.card : ℝ) ^ 3 ≤ (∑ i ∈ s, f i) * (∑ i ∈ s, g i) * (∑ i ∈ s, h i) := by
  by_cases hs : s.Nonempty
  · let F := ∑ i ∈ s, f i
    let G := ∑ i ∈ s, g i
    let H := ∑ i ∈ s, h i
    have hF : 0 < F := Finset.sum_pos hf hs
    have hG : 0 < G := Finset.sum_pos hg hs
    have hH : 0 < H := Finset.sum_pos hh hs
    let P := F * G * H
    have hP : 0 < P := by dsimp [P]; positivity
    let r := P ^ (1 / 3 : ℝ)
    have hr : 0 < r := Real.rpow_pos_of_pos hP _
    have hpoint (i : ι) (hi : i ∈ s) :
        r⁻¹ ≤ (1 / 3 : ℝ) * (f i / F) + (1 / 3 : ℝ) * (g i / G) +
          (1 / 3 : ℝ) * (h i / H) := by
      have hx : 0 ≤ f i / F := div_nonneg (hf i hi).le hF.le
      have hy : 0 ≤ g i / G := div_nonneg (hg i hi).le hG.le
      have hz : 0 ≤ h i / H := div_nonneg (hh i hi).le hH.le
      have hm : f i / F * (g i / G) * (h i / H) = P⁻¹ := by
        rw [div_mul_div_comm, div_mul_div_comm, hone i hi]
        simp [P, one_div]
      calc
        r⁻¹ = (P⁻¹) ^ (1 / 3 : ℝ) := (Real.inv_rpow hP.le _).symm
        _ = (f i / F) ^ (1 / 3 : ℝ) * (g i / G) ^ (1 / 3 : ℝ) *
            (h i / H) ^ (1 / 3 : ℝ) := by
          rw [← hm, Real.mul_rpow (mul_nonneg hx hy) hz, Real.mul_rpow hx hy]
        _ ≤ _ := Real.geom_mean_le_arith_mean3_weighted
          (by norm_num) (by norm_num) (by norm_num) hx hy hz (by norm_num)
    have hsf : (∑ i ∈ s, f i / F) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hF.ne'
    have hsg : (∑ i ∈ s, g i / G) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hG.ne'
    have hsh : (∑ i ∈ s, h i / H) = 1 := by
      rw [← Finset.sum_div]
      exact div_self hH.ne'
    have hsum := Finset.sum_le_sum hpoint
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hsf, hsg, hsh, mul_one] at hsum
    have hle : (s.card : ℝ) ≤ r := (div_le_one hr).mp (by
      rw [div_eq_mul_inv]
      linarith only [hsum])
    have hcub : r ^ 3 = P := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
      norm_num
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hle 3).trans_eq hcub
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

lemma OMA.cycleEdgeBound {n m W C : ℝ} (hn : 0 < n)
    (hlo : (2 * m) ^ 3 ≤ W * n ^ 2) (hhi : W ≤ m * n + C * n ^ 2) (hC : 0 ≤ C) :
    m ≤ (n / 2) ^ (3 / 2 : ℝ) + C * n := by
  let M := (n / 2) ^ (3 / 2 : ℝ)
  have hMsq : M ^ 2 = n ^ 3 / 8 := by
    dsimp [M]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    ring
  have hM : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  change m ≤ M + C * n
  by_cases hm : m ≤ M
  · exact hm.trans (le_add_of_nonneg_right (mul_nonneg hC hn.le))
  · have hnonneg : 0 ≤ m - M := sub_nonneg.mpr (le_of_not_ge hm)
    have h₂ : n ^ 3 ≤ 8 * m * (m + M) := by
      have hMm : M ≤ m := le_of_not_ge hm
      have hm0 : 0 ≤ m := hM.trans hMm
      have h₃ : M ^ 2 ≤ m * (m + M) := by
        rw [pow_two]
        exact mul_le_mul hMm (le_add_of_nonneg_left hm0) hM hm0
      linarith only [hMsq, h₃]
    have h₄ := mul_le_mul_of_nonneg_left h₂ hnonneg
    have h₅ := hlo.trans (mul_le_mul_of_nonneg_right hhi (sq_nonneg n))
    have h₆ : (m - M) * n ^ 3 ≤ (C * n) * n ^ 3 := by
      nlinarith only [h₄, h₅, congrArg (fun t : ℝ => 8 * m * t) hMsq]
    have h₇ := (mul_le_mul_iff_of_pos_right (pow_pos hn 3)).mp h₆
    linarith only [h₇]

lemma OMA.dartInverseDegreeSum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ d : G.Dart, (G.degree d.fst : ℝ)⁻¹) ≤ (Fintype.card V : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset G.Dart) (fun d => d.fst)
    (fun v => (G.degree v : ℝ)⁻¹)]
  calc
    _ ≤ ∑ _v : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      rw [Finset.sum_const, nsmul_eq_mul, G.dart_fst_fiber_card_eq_degree]
      by_cases hd : (G.degree v : ℝ) = 0 <;> simp [hd]
    _ = _ := by simp

lemma OMA.dartThreeWalkLower {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidablePred (· ∈ G.edgeSet)] :
    (2 * (G.edgeFinset.card : ℝ)) ^ 3 ≤
      (∑ d : G.Dart, (G.degree d.fst : ℝ) * (G.degree d.snd : ℝ)) *
        (Fintype.card V : ℝ) ^ 2 := by
  classical
  let a (d : G.Dart) : ℝ := G.degree d.fst
  let b (d : G.Dart) : ℝ := G.degree d.snd
  have ha (d : G.Dart) : 0 < a d := by
    change (0 : ℝ) < (G.degree d.fst : ℝ)
    exact_mod_cast d.adj.degree_pos_left
  have hb (d : G.Dart) : 0 < b d := by
    change (0 : ℝ) < (G.degree d.snd : ℝ)
    exact_mod_cast d.adj.symm.degree_pos_left
  have hlo := OMA.threeFactorCardCube (Finset.univ : Finset G.Dart)
    (fun d => a d * b d) (fun d => (a d)⁻¹) (fun d => (b d)⁻¹)
    (fun d _ => mul_pos (ha d) (hb d))
    (fun d _ => inv_pos.mpr (ha d)) (fun d _ => inv_pos.mpr (hb d))
    (fun d _ => by field_simp [(ha d).ne', (hb d).ne'])
  rw [Finset.card_univ, G.dart_card_eq_twice_card_edges, Nat.cast_mul, Nat.cast_ofNat] at hlo
  have hi : (∑ d, (a d)⁻¹) ≤ (Fintype.card V : ℝ) := OMA.dartInverseDegreeSum G
  have heq : (∑ d, (b d)⁻¹) = ∑ d, (a d)⁻¹ := by
    let e : G.Dart ≃ G.Dart := SimpleGraph.Dart.symm_involutive.toPerm
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [heq] at hlo
  calc
    _ ≤ _ := hlo
    _ ≤ (∑ d : G.Dart, a d * b d) * (Fintype.card V : ℝ) ^ 2 := by
      rw [pow_two, ← mul_assoc]
      gcongr

lemma OMA.dartThreeWalk_eq_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ d : G.Dart, (G.degree d.fst : ℝ) * (G.degree d.snd : ℝ)) =
      ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u : ℝ) * (G.degree v : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset G.Dart) (fun d => d.fst)
    (fun d => (G.degree d.fst : ℝ) * (G.degree d.snd : ℝ))]
  apply Finset.sum_congr rfl
  intro u _
  refine Finset.sum_bij'
    (fun d _ => d.snd)
    (fun v hv => (⟨(u, v), (G.mem_neighborFinset u v).mp hv⟩ : G.Dart)) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    apply (G.mem_neighborFinset u d.snd).mpr
    exact (Finset.mem_filter.mp hd).2 ▸ d.adj
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro d hd
    apply SimpleGraph.Dart.ext
    exact Prod.ext (Finset.mem_filter.mp hd).2.symm rfl
  · intro v hv
    rfl
  · intro d hd
    rw [(Finset.mem_filter.mp hd).2]

lemma OMA.adjThreeWalkLower {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidablePred (· ∈ G.edgeSet)] :
    (2 * (G.edgeFinset.card : ℝ)) ^ 3 ≤
      (∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u : ℝ) * (G.degree v : ℝ)) *
        (Fintype.card V : ℝ) ^ 2 := by
  rw [← OMA.dartThreeWalk_eq_adj G]
  exact OMA.dartThreeWalkLower G

open scoped Classical in
theorem OMA.solution : type_of% @Erdos573.erdos_573.variants.c4_c5 := by
  refine ⟨6, Filter.eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro n hn
  let admissible := Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    ∀ k ∈ ({4, 5} : Set ℕ), (cycleGraph k).Free G
  change ((admissible.sup (fun G => G.edgeFinset.card) : ℕ) : ℝ) ≤
    ((n : ℝ) / 2) ^ (3 / 2 : ℝ) + 6 * n
  by_cases hne : admissible.Nonempty
  · obtain ⟨G, hG, he⟩ := admissible.exists_mem_eq_sup hne (fun G => G.edgeFinset.card)
    have hfree := (Finset.mem_filter.mp hG).2
    have h4 := hfree 4 (by simp)
    have h5 := hfree 5 (by simp)
    have hupper :
        (∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v) ≤
          G.edgeFinset.card * n + 6 * n ^ 2 := by
      simpa only [Fintype.card_fin] using three_walk_count_upper G h4 h5
    have hupperReal :
        (∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u : ℝ) * G.degree v) ≤
          (G.edgeFinset.card : ℝ) * n + 6 * (n : ℝ) ^ 2 := by
      exact_mod_cast hupper
    have hlower := OMA.adjThreeWalkLower G
    rw [Fintype.card_fin] at hlower
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from hn)
    rw [he]
    exact OMA.cycleEdgeBound hnReal hlower hupperReal (by norm_num)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty, bot_eq_zero, Nat.cast_zero]
    positivity