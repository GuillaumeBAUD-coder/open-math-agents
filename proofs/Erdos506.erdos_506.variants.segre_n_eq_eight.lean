import FormalConjectures.ErdosProblems.«506»
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Sphere.Basic

-- Problem: Erdős Problem 506 — segre n eq eight
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/506.lean:110 (declaration Erdos506.erdos_506.variants.segre_n_eq_eight)
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Explicit 8-point counterexample for Segre's observation (`n = 8`):
7 points on the circle of radius 5 centered at the origin together with the origin itself. -/

namespace SegreEightProof

open EuclideanGeometry

noncomputable def q : ℝ² := !₂[0, 0]
noncomputable def p₁ : ℝ² := !₂[5, 0]
noncomputable def p₂ : ℝ² := !₂[-5, 0]
noncomputable def p₃ : ℝ² := !₂[0, 5]
noncomputable def p₄ : ℝ² := !₂[0, -5]
noncomputable def p₅ : ℝ² := !₂[3, 4]
noncomputable def p₆ : ℝ² := !₂[3, -4]
noncomputable def p₇ : ℝ² := !₂[-3, 4]

noncomputable def C7 : Finset ℝ² := {p₁, p₂, p₃, p₄, p₅, p₆, p₇}
noncomputable def P8 : Finset ℝ² := insert q C7

noncomputable def S₀ : Sphere ℝ² := ⟨q, 5⟩

lemma pt_ne_of_coord0 {a b : ℝ²} (h : a 0 ≠ b 0) : a ≠ b :=
  fun heq => h (congrArg (fun x => x 0) heq)

lemma pt_ne_of_coord1 {a b : ℝ²} (h : a 1 ≠ b 1) : a ≠ b :=
  fun heq => h (congrArg (fun x => x 1) heq)

lemma dist_sq_eq {x y : ℝ} (h : x ^ 2 + y ^ 2 = 25) : dist (!₂[x, y] : ℝ²) q = 5 := by
  rw [EuclideanSpace.dist_eq]
  simp only [q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, Fin.isValue, sub_zero, Real.dist_eq, sq_abs]
  norm_num [h]

lemma mem_S₀_C7 {p : ℝ²} (hp : p ∈ C7) : p ∈ S₀ := by
  rw [mem_sphere]
  simp only [C7, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dist_sq_eq (by norm_num [p₁])
  · exact dist_sq_eq (by norm_num [p₂])
  · exact dist_sq_eq (by norm_num [p₃])
  · exact dist_sq_eq (by norm_num [p₄])
  · exact dist_sq_eq (by norm_num [p₅])
  · exact dist_sq_eq (by norm_num [p₆])
  · exact dist_sq_eq (by norm_num [p₇])

lemma sphere_eq_of_three_mem {s₁ s₂ : Sphere ℝ²} {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha₁ : a ∈ s₁) (hb₁ : b ∈ s₁) (hc₁ : c ∈ s₁)
    (ha₂ : a ∈ s₂) (hb₂ : b ∈ s₂) (hc₂ : c ∈ s₂) : s₁ = s₂ := by
  by_contra hs
  have hfin : Module.finrank ℝ ℝ² = 2 := by simp
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two hfin hs hab
    ha₁ hb₁ hc₁ ha₂ hb₂ hc₂ with h | h
  · exact hac.symm h
  · exact hbc.symm h

lemma not_collinear_triple_of_mem_sphere {s : Sphere ℝ²} {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    ¬ Collinear ℝ ({a, b, c} : Set ℝ²) := by
  intro hcol
  have hind : AffineIndependent ℝ ![a, b, c] := by
    refine s.cospherical.affineIndependent ?_ ?_
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  rw [affineIndependent_iff_not_collinear] at hind
  apply hind
  have hrange : Set.range ![a, b, c] = ({a, b, c} : Set ℝ²) := by
    ext x
    simp
    tauto
  rwa [hrange]

lemma collinear_q_p1_p2 : Collinear ℝ ({q, p₁, p₂} : Set ℝ²) := by
  refine (collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair ℝ p₁ p₂)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨(1 / 2 : ℝ), ?_⟩
  ext i
  fin_cases i <;> norm_num [AffineMap.lineMap_apply, q, p₁, p₂]

lemma collinear_q_p3_p4 : Collinear ℝ ({q, p₃, p₄} : Set ℝ²) := by
  refine (collinear_insert_iff_of_mem_affineSpan ?_).2 (collinear_pair ℝ p₃ p₄)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨(1 / 2 : ℝ), ?_⟩
  ext i
  fin_cases i <;> norm_num [AffineMap.lineMap_apply, q, p₃, p₄]

lemma q_not_mem_C7 : q ∉ C7 := by
  intro h
  simp only [C7, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h
  · exact pt_ne_of_coord0 (by norm_num [q, p₁]) h
  · exact pt_ne_of_coord0 (by norm_num [q, p₂]) h
  · exact pt_ne_of_coord1 (by norm_num [q, p₃]) h
  · exact pt_ne_of_coord1 (by norm_num [q, p₄]) h
  · exact pt_ne_of_coord0 (by norm_num [q, p₅]) h
  · exact pt_ne_of_coord0 (by norm_num [q, p₆]) h
  · exact pt_ne_of_coord0 (by norm_num [q, p₇]) h

lemma C7_card : C7.card = 7 := by
  have h12 : p₁ ≠ p₂ := pt_ne_of_coord0 (by norm_num [p₁, p₂])
  have h13 : p₁ ≠ p₃ := pt_ne_of_coord0 (by norm_num [p₁, p₃])
  have h14 : p₁ ≠ p₄ := pt_ne_of_coord0 (by norm_num [p₁, p₄])
  have h15 : p₁ ≠ p₅ := pt_ne_of_coord0 (by norm_num [p₁, p₅])
  have h16 : p₁ ≠ p₆ := pt_ne_of_coord0 (by norm_num [p₁, p₆])
  have h17 : p₁ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₁, p₇])
  have h23 : p₂ ≠ p₃ := pt_ne_of_coord0 (by norm_num [p₂, p₃])
  have h24 : p₂ ≠ p₄ := pt_ne_of_coord0 (by norm_num [p₂, p₄])
  have h25 : p₂ ≠ p₅ := pt_ne_of_coord0 (by norm_num [p₂, p₅])
  have h26 : p₂ ≠ p₆ := pt_ne_of_coord0 (by norm_num [p₂, p₆])
  have h27 : p₂ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₂, p₇])
  have h34 : p₃ ≠ p₄ := pt_ne_of_coord1 (by norm_num [p₃, p₄])
  have h35 : p₃ ≠ p₅ := pt_ne_of_coord0 (by norm_num [p₃, p₅])
  have h36 : p₃ ≠ p₆ := pt_ne_of_coord0 (by norm_num [p₃, p₆])
  have h37 : p₃ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₃, p₇])
  have h45 : p₄ ≠ p₅ := pt_ne_of_coord0 (by norm_num [p₄, p₅])
  have h46 : p₄ ≠ p₆ := pt_ne_of_coord0 (by norm_num [p₄, p₆])
  have h47 : p₄ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₄, p₇])
  have h56 : p₅ ≠ p₆ := pt_ne_of_coord1 (by norm_num [p₅, p₆])
  have h57 : p₅ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₅, p₇])
  have h67 : p₆ ≠ p₇ := pt_ne_of_coord0 (by norm_num [p₆, p₇])
  simp [C7, h12, h13, h14, h15, h16, h17, h23, h24, h25, h26, h27,
    h34, h35, h36, h37, h45, h46, h47, h56, h57, h67]

end SegreEightProof

open EuclideanGeometry

theorem OMA.solution : type_of% @Erdos506.erdos_506.variants.segre_n_eq_eight := by
  classical
  refine ⟨SegreEightProof.P8, ?_, ?_, ?_, ?_⟩
  · -- P8.card = 8
    rw [SegreEightProof.P8, Finset.card_insert_of_notMem SegreEightProof.q_not_mem_C7,
      SegreEightProof.C7_card]
  · -- ¬ Collinear ℝ P8
    intro hcol
    have hsub : Collinear ℝ ({SegreEightProof.q, SegreEightProof.p₁, SegreEightProof.p₃} : Set ℝ²) := by
      refine hcol.subset ?_
      intro x hx
      simp only [SegreEightProof.P8, SegreEightProof.C7, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    have hq1 : SegreEightProof.q ≠ SegreEightProof.p₁ :=
      SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.q, SegreEightProof.p₁])
    have hm : SegreEightProof.p₃ ∈ line[ℝ, SegreEightProof.q, SegreEightProof.p₁] :=
      hsub.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hq1
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm
    have ht1 := congrArg (fun p : ℝ² => p 1) ht
    norm_num [AffineMap.lineMap_apply, SegreEightProof.q, SegreEightProof.p₁, SegreEightProof.p₃] at ht1
  · -- ¬ Cospherical P8
    intro hcosp
    obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.mp hcosp
    have h12 : SegreEightProof.p₁ ≠ SegreEightProof.p₂ :=
      SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₂])
    have h13 : SegreEightProof.p₁ ≠ SegreEightProof.p₃ :=
      SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₃])
    have h23 : SegreEightProof.p₂ ≠ SegreEightProof.p₃ :=
      SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₂, SegreEightProof.p₃])
    have hs_eq : s = SegreEightProof.S₀ := by
      refine SegreEightProof.sphere_eq_of_three_mem h12 h13 h23 ?_ ?_ ?_ ?_ ?_ ?_
      · exact hs (by simp [SegreEightProof.P8, SegreEightProof.C7])
      · exact hs (by simp [SegreEightProof.P8, SegreEightProof.C7])
      · exact hs (by simp [SegreEightProof.P8, SegreEightProof.C7])
      · exact SegreEightProof.mem_S₀_C7 (by simp [SegreEightProof.C7])
      · exact SegreEightProof.mem_S₀_C7 (by simp [SegreEightProof.C7])
      · exact SegreEightProof.mem_S₀_C7 (by simp [SegreEightProof.C7])
    have hq_mem : SegreEightProof.q ∈ SegreEightProof.S₀ := by
      rw [← hs_eq]
      exact hs (by simp [SegreEightProof.P8])
    rw [mem_sphere] at hq_mem
    simp [SegreEightProof.S₀] at hq_mem
  · -- numCircles P8 < (8 - 1).choose 2
    let pair12 : Finset ℝ² := {SegreEightProof.p₁, SegreEightProof.p₂}
    let pair34 : Finset ℝ² := {SegreEightProof.p₃, SegreEightProof.p₄}
    let Good : Finset (Finset ℝ²) := (SegreEightProof.C7.powersetCard 2) \ {pair12, pair34}
    have hGood_card : Good.card ≤ 19 := by
      have hp12_mem : pair12 ∈ SegreEightProof.C7.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨by intro x hx; simp [pair12, SegreEightProof.C7] at hx ⊢; tauto, ?_⟩
        have h12 : SegreEightProof.p₁ ≠ SegreEightProof.p₂ :=
          SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₂])
        simp [pair12, h12]
      have hp34_mem : pair34 ∈ SegreEightProof.C7.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨by intro x hx; simp [pair34, SegreEightProof.C7] at hx ⊢; tauto, ?_⟩
        have h34 : SegreEightProof.p₃ ≠ SegreEightProof.p₄ :=
          SegreEightProof.pt_ne_of_coord1 (by norm_num [SegreEightProof.p₃, SegreEightProof.p₄])
        simp [pair34, h34]
      have hne1234 : pair12 ≠ pair34 := by
        intro heq
        have hp1 : SegreEightProof.p₁ ∈ pair34 := heq ▸ (by simp [pair12])
        simp only [pair34, Finset.mem_insert, Finset.mem_singleton] at hp1
        rcases hp1 with h | h
        · exact SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₃]) h
        · exact SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₄]) h
      have hsub_card : ({pair12, pair34} : Finset (Finset ℝ²)).card = 2 := by
        simp [hne1234]
      have hsub_mem : ({pair12, pair34} : Finset (Finset ℝ²)) ⊆ SegreEightProof.C7.powersetCard 2 := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> assumption
      have hpc : (SegreEightProof.C7.powersetCard 2).card = 21 := by
        rw [Finset.card_powersetCard, SegreEightProof.C7_card]
        decide
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_mem, hpc, hsub_card]
    let goodSpheres : Finset (Sphere ℝ²) :=
      Good.biUnion fun t =>
        if h : ∃ s : Sphere ℝ², SegreEightProof.q ∈ s ∧ (t : Set ℝ²) ⊆ s
        then {Classical.choose h}
        else ∅
    have hgs_card : goodSpheres.card ≤ 19 := by
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ t ∈ Good, (if h : ∃ s : Sphere ℝ², SegreEightProof.q ∈ s ∧ (t : Set ℝ²) ⊆ s
            then ({Classical.choose h} : Finset (Sphere ℝ²)) else ∅).card
          ≤ ∑ _t ∈ Good, 1 := by
            refine Finset.sum_le_sum fun t _ => ?_
            split_ifs <;> simp
        _ = Good.card := by simp
        _ ≤ 19 := hGood_card
    let Cand : Finset (Sphere ℝ²) := insert SegreEightProof.S₀ goodSpheres
    have hCand_card : Cand.card ≤ 20 := by
      exact le_trans (Finset.card_insert_le _ _) (by omega)
    have hsubset :
        { s : Sphere ℝ² | 3 ≤ {p ∈ (SegreEightProof.P8 : Set ℝ²) | p ∈ s}.ncard } ⊆
          (Cand : Set (Sphere ℝ²)) := by
      intro s hs
      change 3 ≤ {p : ℝ² | p ∈ (SegreEightProof.P8 : Set ℝ²) ∧ p ∈ s}.ncard at hs
      have hset_eq : {p : ℝ² | p ∈ (SegreEightProof.P8 : Set ℝ²) ∧ p ∈ s} =
          ((SegreEightProof.P8.filter (· ∈ s)) : Set ℝ²) := by
        ext p
        simp
      rw [hset_eq, Set.ncard_coe_finset] at hs
      by_cases hq_s : SegreEightProof.q ∈ s
      · have hfilt_sub : SegreEightProof.P8.filter (· ∈ s) ⊆
            insert SegreEightProof.q (SegreEightProof.C7.filter (· ∈ s)) := by
          intro x hx
          simp only [Finset.mem_filter, SegreEightProof.P8, Finset.mem_insert] at hx ⊢
          rcases hx with ⟨rfl | hxC, hxs⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxC, hxs⟩
        have hC7s_ge2 : 2 ≤ (SegreEightProof.C7.filter (· ∈ s)).card := by
          have h1 := Finset.card_le_card hfilt_sub
          have h2 := Finset.card_insert_le SegreEightProof.q (SegreEightProof.C7.filter (· ∈ s))
          omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (SegreEightProof.C7.filter (· ∈ s)).card)
        simp only [Finset.mem_filter] at ha hb
        let t : Finset ℝ² := {a, b}
        have ht_pc : t ∈ SegreEightProof.C7.powersetCard 2 := by
          rw [Finset.mem_powersetCard]
          refine ⟨by intro x hx; simp only [t, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> [exact ha.1; exact hb.1], ?_⟩
          simp [t, hab]
        have hqa : SegreEightProof.q ≠ a := fun h => SegreEightProof.q_not_mem_C7 (h ▸ ha.1)
        have hqb : SegreEightProof.q ≠ b := fun h => SegreEightProof.q_not_mem_C7 (h ▸ hb.1)
        have ht_not_12 : t ≠ pair12 := by
          intro heq
          have hp1t : SegreEightProof.p₁ ∈ t := heq.symm ▸ (by simp [pair12])
          have hp2t : SegreEightProof.p₂ ∈ t := heq.symm ▸ (by simp [pair12])
          have hp1s : SegreEightProof.p₁ ∈ s := by
            simp only [t, Finset.mem_insert, Finset.mem_singleton] at hp1t
            rcases hp1t with rfl | rfl <;> [exact ha.2; exact hb.2]
          have hp2s : SegreEightProof.p₂ ∈ s := by
            simp only [t, Finset.mem_insert, Finset.mem_singleton] at hp2t
            rcases hp2t with rfl | rfl <;> [exact ha.2; exact hb.2]
          have hq1 : SegreEightProof.q ≠ SegreEightProof.p₁ :=
            SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.q, SegreEightProof.p₁])
          have hq2 : SegreEightProof.q ≠ SegreEightProof.p₂ :=
            SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.q, SegreEightProof.p₂])
          have h12 : SegreEightProof.p₁ ≠ SegreEightProof.p₂ :=
            SegreEightProof.pt_ne_of_coord0 (by norm_num [SegreEightProof.p₁, SegreEightProof.p₂])
          exact SegreEightProof.not_collinear_triple_of_mem_sphere hq1 hq2 h12 hq_s hp1s hp2s
            SegreEightProof.collinear_q_p1_p2
        have ht_not_34 : t ≠ pair34 := by
          intro heq
          have hp3t : SegreEightProof.p₃ ∈ t := heq.symm ▸ (by simp [pair34])
          have hp4t : SegreEightProof.p₄ ∈ t := heq.symm ▸ (by simp [pair34])
          have hp3s : SegreEightProof.p₃ ∈ s := by
            simp only [t, Finset.mem_insert, Finset.mem_singleton] at hp3t
            rcases hp3t with rfl | rfl <;> [exact ha.2; exact hb.2]
          have hp4s : SegreEightProof.p₄ ∈ s := by
            simp only [t, Finset.mem_insert, Finset.mem_singleton] at hp4t
            rcases hp4t with rfl | rfl <;> [exact ha.2; exact hb.2]
          have hq3 : SegreEightProof.q ≠ SegreEightProof.p₃ :=
            SegreEightProof.pt_ne_of_coord1 (by norm_num [SegreEightProof.q, SegreEightProof.p₃])
          have hq4 : SegreEightProof.q ≠ SegreEightProof.p₄ :=
            SegreEightProof.pt_ne_of_coord1 (by norm_num [SegreEightProof.q, SegreEightProof.p₄])
          have h34 : SegreEightProof.p₃ ≠ SegreEightProof.p₄ :=
            SegreEightProof.pt_ne_of_coord1 (by norm_num [SegreEightProof.p₃, SegreEightProof.p₄])
          exact SegreEightProof.not_collinear_triple_of_mem_sphere hq3 hq4 h34 hq_s hp3s hp4s
            SegreEightProof.collinear_q_p3_p4
        have ht_good : t ∈ Good := Finset.mem_sdiff.mpr ⟨ht_pc, by simp [ht_not_12, ht_not_34]⟩
        have hex : ∃ s' : Sphere ℝ², SegreEightProof.q ∈ s' ∧ (t : Set ℝ²) ⊆ s' := by
          refine ⟨s, hq_s, ?_⟩
          intro x hx
          simp only [t, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl <;> [exact ha.2; exact hb.2]
        have hs_eq : s = Classical.choose hex := by
          have hspec := Classical.choose_spec hex
          refine SegreEightProof.sphere_eq_of_three_mem hqa hqb hab hq_s ha.2 hb.2 hspec.1 ?_ ?_
          · exact hspec.2 (by simp [t])
          · exact hspec.2 (by simp [t])
        simp only [Finset.mem_coe, Cand, Finset.mem_insert, goodSpheres, Finset.mem_biUnion]
        refine Or.inr ⟨t, ht_good, ?_⟩
        rw [dif_pos hex]
        simp [hs_eq]
      · have hfilt_sub : SegreEightProof.P8.filter (· ∈ s) ⊆ SegreEightProof.C7.filter (· ∈ s) := by
          intro x hx
          simp only [Finset.mem_filter, SegreEightProof.P8, Finset.mem_insert] at hx ⊢
          rcases hx with ⟨rfl | hxC, hxs⟩
          · exact absurd hxs hq_s
          · exact ⟨hxC, hxs⟩
        have hC7s_ge3 : 3 ≤ (SegreEightProof.C7.filter (· ∈ s)).card :=
          le_trans hs (Finset.card_le_card hfilt_sub)
        obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hC7s_ge3
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht_card
        have ha : a ∈ SegreEightProof.C7.filter (· ∈ s) := ht_sub (by simp)
        have hb : b ∈ SegreEightProof.C7.filter (· ∈ s) := ht_sub (by simp)
        have hc : c ∈ SegreEightProof.C7.filter (· ∈ s) := ht_sub (by simp)
        simp only [Finset.mem_filter] at ha hb hc
        have hs_eq : s = SegreEightProof.S₀ :=
          SegreEightProof.sphere_eq_of_three_mem hab hac hbc ha.2 hb.2 hc.2
            (SegreEightProof.mem_S₀_C7 ha.1) (SegreEightProof.mem_S₀_C7 hb.1) (SegreEightProof.mem_S₀_C7 hc.1)
        simp [Cand, hs_eq]
    have hncard_le : Erdos506.numCircles (SegreEightProof.P8 : Set ℝ²) ≤ Cand.card := by
      rw [Erdos506.numCircles]
      exact (Set.ncard_le_ncard hsubset Cand.finite_toSet).trans_eq (Set.ncard_coe_finset Cand)
    have h20 : (20 : ℕ) < (8 - 1).choose 2 := by decide
    omega