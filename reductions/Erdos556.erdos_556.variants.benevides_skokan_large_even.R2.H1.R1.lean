import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
/-
Simultaneous regularity for the large even cycle Ramsey number.

A refinement for one graph gains at least ε⁵/4 of its energy and loses at most ε⁵/25
of the other graph's energy. Iterating the sum gives a common equipartition. Since
the three densities sum to one on disjoint nonempty sets, two regular colours
suffice for a common exceptional set and all three colours. In the EC2 alternative,
passing from unweighted cluster deficits to vertex deficits costs a factor of four.
Portions of the energy argument adapt Mathlib's Regularity/Chunk.lean, Increment.lean and
Lemma.lean. Copyright (c) 2021–2022 Yaël Dillies, Bhavik Mehta. Apache License 2.0.
-/

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1

section Energy
open Finpartition Finset Fintype Rel Nat SimpleGraph SzemerediRegularity Function
open scoped SzemerediRegularity.Positivity



variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  {hP : P.IsEquipartition} {G : SimpleGraph α} [DecidableRel G.Adj] {ε : ℝ}
  {U V : Finset α} {hU : U ∈ P.parts} {𝒜 : Finset (Finset α)} {s : Finset α}
private theorem lowerSize (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#𝒜 : ℝ) * #s * ((card α / stepBound #P.parts : ℕ) / ((card α / stepBound #P.parts : ℕ) + 1)) ≤ #(𝒜.sup id) := by
  rw [mul_div_assoc', div_le_iff₀ coe_m_add_one_pos, mul_right_comm]
  gcongr
  · rw [← (ofSubset _ h𝒜 rfl).sum_card_parts, ofSubset_parts, ← cast_mul, cast_le]
    exact card_nsmul_le_sum _ _ _ fun x hx => m_le_card_of_mem_chunk_parts <| h𝒜 hx
  · exact mod_cast card_le_m_add_one_of_mem_chunk_parts (h𝒜 hs)

private theorem sizeRatio [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    ↑1 - ε ^ 5 / ↑50 ≤ ((card α / stepBound #P.parts : ℕ) / ((card α / stepBound #P.parts : ℕ) + 1 : ℝ)) ^ 2 := by
  have : ((card α / stepBound #P.parts : ℕ) : ℝ) / ((card α / stepBound #P.parts : ℕ) + 1) = 1 - 1 / ((card α / stepBound #P.parts : ℕ) + 1) := by
    rw [one_sub_div coe_m_add_one_pos.ne', add_sub_cancel_right]
  rw [this, sub_sq, one_pow, mul_one]
  refine le_trans ?_ (le_add_of_nonneg_right <| sq_nonneg _)
  rw [sub_le_sub_iff_left, ← le_div_iff₀' (show (0 : ℝ) < 2 by simp), div_div,
    one_div_le coe_m_add_one_pos, one_div_div]
  · refine le_trans ?_ (le_add_of_nonneg_right zero_le_one)
    norm_num
    apply hundred_div_ε_pow_five_le_m hPα hPε
  sz_positivity


variable (H : SimpleGraph α) [DecidableRel H.Adj]
private theorem densityAverage [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) :
    (H.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / 50 ≤
    (∑ ab ∈ A.product B, (H.edgeDensity ab.1 ab.2 : ℝ)) / (#A * #B) := by
  have : ↑(H.edgeDensity (A.biUnion id) (B.biUnion id)) - ε ^ 5 / ↑50 ≤
      (↑1 - ε ^ 5 / 50) * H.edgeDensity (A.biUnion id) (B.biUnion id) := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast H.edgeDensity_le_one _ _
  refine this.trans ?_
  conv_rhs =>
    simp only [SimpleGraph.edgeDensity_def, sum_div, Rat.cast_div, div_div]
  conv_lhs =>
    rw [SimpleGraph.edgeDensity_def, SimpleGraph.interedges, ← sup_eq_biUnion, ← sup_eq_biUnion,
      Rel.card_interedges_finpartition _ (ofSubset _ hA rfl) (ofSubset _ hB rfl), ofSubset_parts,
      ofSubset_parts]
    simp only [cast_sum, sum_div, mul_sum, Rat.cast_sum, Rat.cast_div,
      mul_div_left_comm ((1 : ℝ) - _)]
  push_cast
  apply sum_le_sum
  simp only [and_imp, Prod.forall, mem_product]
  rintro x y hx hy
  rw [mul_mul_mul_comm, mul_comm (#x : ℝ), mul_comm (#y : ℝ), le_div_iff₀, mul_assoc]
  · refine mul_le_of_le_one_right (cast_nonneg _) ?_
    rw [div_mul_eq_mul_div, ← mul_assoc, mul_assoc]
    refine div_le_one_of_le₀ ?_ (by positivity)
    refine (mul_le_mul_of_nonneg_right (sizeRatio hPα hPε) ?_).trans ?_
    · exact_mod_cast _root_.zero_le
    rw [sq, mul_mul_mul_comm, mul_comm (((card α / stepBound #P.parts : ℕ) : ℝ) / _), mul_comm (((card α / stepBound #P.parts : ℕ) : ℝ) / _)]
    gcongr
    · apply lowerSize hA hx
    · apply lowerSize hB hy
  refine mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_) <;> rw [cast_pos, Finset.card_pos]
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]

private theorem squareAverage [Nonempty α] (hP)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    ((∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (H.edgeDensity ab.1 ab.2 : ℝ)) / ↑16 ^ #P.parts) ^ 2 := by
  obtain hGε | hGε := le_total (H.edgeDensity U V : ℝ) (ε ^ 5 / 50)
  · refine (sub_nonpos_of_le <| (sq_le ?_ ?_).trans <| hGε.trans ?_).trans (sq_nonneg _)
    · exact mod_cast H.edgeDensity_nonneg _ _
    · exact mod_cast H.edgeDensity_le_one _ _
    · exact div_le_div_of_nonneg_left (by sz_positivity) (by simp) (by norm_num)
  rw [← sub_nonneg] at hGε
  have : 0 ≤ ε := by sz_positivity
  calc
    _ = H.edgeDensity U V ^ 2 - 1 * ε ^ 5 / 25 + 0 ^ 10 / 2500 := by ring
    _ ≤ H.edgeDensity U V ^ 2 - H.edgeDensity U V * ε ^ 5 / 25 + ε ^ 10 / 2500 := by
      gcongr; exact mod_cast H.edgeDensity_le_one ..
    _ = (H.edgeDensity U V - ε ^ 5 / 50) ^ 2 := by ring
    _ ≤ _ := by
      gcongr
      have rflU := Subset.refl (chunk hP G ε hU).parts
      have rflV := Subset.refl (chunk hP G ε hV).parts
      refine (le_trans ?_ <| densityAverage H hPα hPε rflU rflV).trans ?_
      · rw [biUnion_parts, biUnion_parts]
      · rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ← cast_mul, ← mul_pow, cast_pow]
        norm_cast

theorem cross_chunk [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (H.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    (∑ ab ∈ (chunk hP G ε hU).parts.product (chunk hP G ε hV).parts,
      (H.edgeDensity ab.1 ab.2 : ℝ) ^ 2) / ↑16 ^ #P.parts := by
  apply (squareAverage H (G := G) (hP := hP) hPα hPε hU hV).trans
  have key : (16 : ℝ) ^ #P.parts = #((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts) := by
    rw [card_product, cast_mul, card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne', ←
      cast_mul, ← mul_pow]; norm_cast
  simp_rw [key]
  convert! sum_div_card_sq_le_sum_sq_div_card (α := ℝ)

private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (fun x : {x // x ∈ P.parts.offDiag} =>
        (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts) ⊆ (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint
      (fun x : {x // x ∈ P.parts.offDiag} =>
        (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts) := by
  simp +unfoldPartialApp only [Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  exact hst <| Subtype.ext <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb

/-- Refining for graph G costs at most ε⁵/25 of the energy of a second graph H. -/
theorem cross_energy [Nonempty α]
    (hPε : 100 ≤ 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPG : ¬P.IsUniform G ε) :
    (P.energy H : ℝ) - ε ^ 5 / 25 ≤ (increment hP G ε).energy H := by
  have hk := (nonempty_of_not_uniform hPG).card_pos
  have hk' : (0 : ℝ) < #P.parts := by exact_mod_cast hk
  have hε' := eps_pow_five_pos hPε
  have hn : (#P.parts.offDiag : ℝ) ≤ (#P.parts : ℝ)^2 := by
    exact_mod_cast (show #P.parts.offDiag ≤ #P.parts^2 by rw [offDiag_card, sq]; omega)
  calc
    _ = (∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ) ^ 2 -
          (#P.parts : ℝ) ^ 2 * (ε ^ 5 / 25)) / #P.parts ^ 2 := by
        rw [coe_energy, sub_div, mul_div_cancel_left₀]; positivity
    _ ≤ (∑ x ∈ P.parts.offDiag.attach, (∑ i ∈ ((chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts),
          H.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ #P.parts) / #P.parts ^ 2 := by
        gcongr
        calc
          _ ≤ (∑ x ∈ P.parts.offDiag, (H.edgeDensity x.1 x.2 : ℝ)^2) -
                #P.parts.offDiag * (ε^5/25) := by gcongr
          _ = ∑ x ∈ P.parts.offDiag.attach, ((H.edgeDensity x.val.1 x.val.2 : ℝ)^2 -
                ε^5/25) := by
                rw [sum_attach P.parts.offDiag (fun x => (H.edgeDensity x.1 x.2 : ℝ)^2 - ε^5/25),
                  sum_sub_distrib, sum_const, nsmul_eq_mul]
          _ ≤ _ := sum_le_sum fun x _ => cross_chunk H hPα hPε _ _
    _ = (∑ x ∈ P.parts.offDiag.attach, ∑ i ∈ ((chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts),
          H.edgeDensity i.1 i.2 ^ 2 : ℝ) / #(increment hP G ε).parts ^ 2 := by
        rw [card_increment hPα hPG, coe_stepBound, mul_pow, pow_right_comm,
          div_mul_eq_div_div_swap, ← sum_div]; norm_num
    _ ≤ _ := by
        rw [coe_energy]
        gcongr
        rw [← sum_biUnion pairwiseDisjoint_distinctPairs]
        exact sum_le_sum_of_subset_of_nonneg distinctPairs_increment fun i _ _ => sq_nonneg _


/-- One equipartition works simultaneously for two graphs, with a bound independent of the graphs. -/
theorem simultaneous_equipartition (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1) (l : ℕ) :
    ∃ M : ℕ, ∀ {X : Type*} [Fintype X] [DecidableEq X] (G H : SimpleGraph X)
      [DecidableRel G.Adj] [DecidableRel H.Adj], M ≤ Fintype.card X →
      ∃ P : Finpartition (Finset.univ : Finset X), P.IsEquipartition ∧
        l ≤ #P.parts ∧ #P.parts ≤ M ∧ P.IsUniform G η ∧ P.IsUniform H η := by
  let t := initialBound η l
  obtain ⟨r, hr⟩ := exists_nat_gt (10 / η^5)
  let K := stepBound^[r] t
  refine ⟨K * 16^K, ?_⟩
  intro X _ _ G H _ _ hX
  have hK : t ≤ K := by
    exact (monotone_iterate_of_id_le le_stepBound (Nat.zero_le r) t)
  have hKM : K ≤ K * 16^K := Nat.le_mul_of_pos_right _ (by positivity)
  have ht : 0 < t := initialBound_pos _ _
  have : Nonempty X := Fintype.card_pos_iff.mp (ht.trans_le (hK.trans (hKM.trans hX)))
  obtain ⟨start, heq, hnum⟩ := exists_equipartition_card_eq (univ : Finset X) ht.ne'
    (by simpa using hK.trans (hKM.trans hX))
  let goal := fun P : Finpartition (univ : Finset X) => P.IsUniform G η ∧ P.IsUniform H η
  have iter : ∀ i ≤ r, ∃ P : Finpartition (univ : Finset X), P.IsEquipartition ∧
      t ≤ #P.parts ∧ #P.parts ≤ stepBound^[i] t ∧
      (goal P ∨ η^5/5 * i ≤ (P.energy G : ℝ) + P.energy H) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨start, heq, hnum.ge, hnum.le, Or.inr ?_⟩
      simp only [Nat.cast_zero, mul_zero]
      exact add_nonneg (by exact_mod_cast start.energy_nonneg G) (by exact_mod_cast start.energy_nonneg H)
    | succ i ih =>
      intro hi
      obtain ⟨P, hp, hmin, hmax, hor⟩ := ih (by omega)
      by_cases done : goal P
      · exact ⟨P, hp, hmin, hmax.trans (monotone_iterate_of_id_le le_stepBound (Nat.le_succ i) t), Or.inl done⟩
      have he := hor.resolve_left done
      have hsize : #P.parts ≤ K := hmax.trans (monotone_iterate_of_id_le le_stepBound (by omega : i ≤ r) t)
      have hroom : #P.parts * 16 ^ #P.parts ≤ Fintype.card X :=
        (Nat.mul_le_mul hsize (Nat.pow_le_pow_right (by decide) hsize)).trans hX
      have hbig : (100 : ℝ) ≤ 4 ^ #P.parts * η^5 :=
        (hundred_lt_pow_initialBound_mul hη l).le.trans
          (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hmin) (by positivity))
      have hseven : 7 ≤ #P.parts := (seven_le_initialBound η l).trans hmin
      have bounds (J : SimpleGraph X) [DecidableRel J.Adj] (bad : ¬P.IsUniform J η) :
          t ≤ #(increment hp J η).parts ∧ #(increment hp J η).parts ≤ stepBound^[i+1] t := by
        rw [card_increment hroom bad, Function.iterate_succ_apply']
        exact ⟨hmin.trans (le_stepBound _), stepBound_mono hmax⟩
      have hpow := pow_pos hη 5
      by_cases hG : P.IsUniform G η
      · have hH : ¬P.IsUniform H η := fun h => done ⟨hG,h⟩
        obtain ⟨ha,hb⟩ := bounds H hH
        refine ⟨_, increment_isEquipartition hp H η, ha, hb, Or.inr ?_⟩
        have hgain := energy_increment hp hseven hbig hroom hH hη.le hη₁
        have hloss := cross_energy G (hP := hp) hbig hroom hH
        rw [Nat.cast_succ, mul_add, mul_one]
        linarith
      · obtain ⟨ha,hb⟩ := bounds G hG
        refine ⟨_, increment_isEquipartition hp G η, ha, hb, Or.inr ?_⟩
        have hgain := energy_increment hp hseven hbig hroom hG hη.le hη₁
        have hloss := cross_energy H (hP := hp) hbig hroom hG
        rw [Nat.cast_succ, mul_add, mul_one]
        linarith
  obtain ⟨P, hp, ha, hb, hor⟩ := iter r le_rfl
  refine ⟨P, hp, (le_initialBound η l).trans ha, hb.trans hKM, hor.resolve_right ?_⟩
  intro he
  have hg : (P.energy G : ℝ) ≤ 1 := by exact_mod_cast P.energy_le_one G
  have hh : (P.energy H : ℝ) ≤ 1 := by exact_mod_cast P.energy_le_one H
  have hr' := (div_lt_iff₀ (pow_pos hη 5)).mp hr
  linarith

end Energy

section Joint
open Finset SimpleGraph


variable {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V)
  [∀ i, DecidableRel (c i).Adj]

theorem density_sum (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {s t : Finset V} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : Disjoint s t) :
    (c 0).edgeDensity s t + (c 1).edgeDensity s t + (c 2).edgeDensity s t = 1 := by
  let E := fun i => (c i).interedges s t
  have hd {i j : Fin 3} (hij : i ≠ j) : Disjoint (E i) (E j) := by
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact SimpleGraph.disjoint_left.mp (hc.2 _ _ hij) _ _
      (((c i).mem_interedges_iff).mp hi).2.2 (((c j).mem_interedges_iff).mp hj).2.2
  have hu : E 0 ∪ E 1 ∪ E 2 = s ×ˢ t := by
    ext e
    simp only [E, Finset.mem_union, SimpleGraph.mem_interedges_iff, Finset.mem_product]
    constructor
    · rintro ((h | h) | h) <;> exact ⟨h.1, h.2.1⟩
    · rintro ⟨hs', ht'⟩
      have ha : (⊤ : SimpleGraph V).Adj e.1 e.2 := hst.forall_ne_finset hs' ht'
      rw [hc.1, SimpleGraph.iSup_adj] at ha
      obtain ⟨i, hi⟩ := ha
      fin_cases i
      · exact Or.inl (Or.inl ⟨hs', ht', hi⟩)
      · exact Or.inl (Or.inr ⟨hs', ht', hi⟩)
      · exact Or.inr ⟨hs', ht', hi⟩
  have hn := congrArg Finset.card hu
  have hd₂ : Disjoint (E 0 ∪ E 1) (E 2) := disjoint_sup_left.mpr ⟨hd (by decide), hd (by decide)⟩
  rw [Finset.card_union_of_disjoint hd₂,
    Finset.card_union_of_disjoint (hd (i := 0) (j := 1) (by decide)), Finset.card_product] at hn
  simp only [SimpleGraph.edgeDensity_def, ← add_div]
  apply (div_eq_one_iff_eq (mul_ne_zero (by exact_mod_cast hs.card_pos.ne')
    (by exact_mod_cast ht.card_pos.ne'))).mpr
  exact_mod_cast hn

theorem third_uniform (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {s t : Finset V} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : Disjoint s t) {ε : ℝ}
    (h₀ : (c 0).IsUniform ε s t) (h₁ : (c 1).IsUniform ε s t) :
    (c 2).IsUniform (2 * ε) s t := by
  intro a ha b hb hsa htb
  have hε := h₀.pos
  have hs₀ : (s.card : ℝ) * ε ≤ a.card := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) s.card) hε.le]
  have ht₀ : (t.card : ℝ) * ε ≤ b.card := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t.card) hε.le]
  have ha₀ : a.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos (by exact_mod_cast hs.card_pos) hε).trans_le hs₀)
  have hb₀ : b.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos (by exact_mod_cast ht.card_pos) hε).trans_le ht₀)
  have total (x y : Finset V) (hx : x.Nonempty) (hy : y.Nonempty) (hxy : Disjoint x y) :
      ((c 0).edgeDensity x y : ℝ) + (c 1).edgeDensity x y + (c 2).edgeDensity x y = 1 := by
    exact_mod_cast density_sum c hc hx hy hxy
  have ht₁ := total s t hs ht hst
  have ht₂ := total a b ha₀ hb₀ (hst.mono ha hb)
  obtain ⟨hl₀, hu₀⟩ := abs_lt.mp (h₀ ha hb hs₀ ht₀)
  obtain ⟨hl₁, hu₁⟩ := abs_lt.mp (h₁ ha hb hs₀ ht₀)
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Outside one exceptional set of at most 2ε of the ordered pairs of distinct clusters,
all three colours are 2ε-regular and some colour has density at least 1/3. -/
theorem joint_pairs (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) {A : Finset V} (P : Finpartition A) {ε : ℝ}
    (h₀ : P.IsUniform (c 0) ε) (h₁ : P.IsUniform (c 1) ε) :
    ∃ bad ⊆ P.parts.offDiag, (bad.card : ℝ) ≤ (P.parts.offDiag.card : ℝ) * (2 * ε) ∧
      ∀ x ∈ P.parts.offDiag, x ∉ bad →
        (∀ i, (c i).IsUniform (2 * ε) x.1 x.2) ∧
        ∃ i, (1 / 3 : ℚ) ≤ (c i).edgeDensity x.1 x.2 := by
  classical
  let bad := P.nonUniforms (c 0) ε ∪ P.nonUniforms (c 1) ε
  refine ⟨bad, Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..), ?_, ?_⟩
  · have hn : P.parts.offDiag.card = P.parts.card * (P.parts.card - 1) := by
      rw [Finset.offDiag_card, Nat.mul_sub_one]
    have hb : (bad.card : ℝ) ≤ (P.nonUniforms (c 0) ε).card + ((P.nonUniforms (c 1) ε).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (P.nonUniforms (c 0) ε) (P.nonUniforms (c 1) ε)
    rw [Finpartition.IsUniform, ← hn] at h₀ h₁
    linarith
  · intro x hx hgood
    obtain ⟨hx₀, hx₁, hne⟩ := Finset.mem_offDiag.mp hx
    have good (i : Fin 3) (hi : x ∉ P.nonUniforms (c i) ε) : (c i).IsUniform ε x.1 x.2 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨hx,h⟩)
    have g₀ := good 0 (fun h => hgood (Finset.mem_union_left _ h))
    have g₁ := good 1 (fun h => hgood (Finset.mem_union_right _ h))
    have hs := P.nonempty_of_mem_parts hx₀
    have ht := P.nonempty_of_mem_parts hx₁
    have hd := P.disjoint hx₀ hx₁ hne
    constructor
    · intro i
      fin_cases i
      · exact g₀.mono (by linarith [g₀.pos])
      · exact g₁.mono (by linarith [g₁.pos])
      · exact third_uniform c hc hs ht hd g₀ g₁
    · by_contra! h
      linarith [density_sum c hc hs ht hd, h 0, h 1, h 2]

end Joint

section Lift
open Finset SimpleGraph


variable {V : Type*} [DecidableEq V] {T : Finset V} (P : Finpartition T)

/-- A near-monochromatic unweighted block of clusters pulls back to a near-monochromatic
block of vertices. The factor four covers the difference of one between cluster sizes. -/
theorem lift_density (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset (Finset V)} (hA : A ⊆ P.parts) (hB : B ⊆ P.parts)
    {w : ℕ} (hw : ∀ X ∈ P.parts, w ≤ #X ∧ #X ≤ 2 * w)
    {α : ℝ} (hα : 0 ≤ α)
    (h : ∑ xy ∈ A ×ˢ B, (1 - (G.edgeDensity xy.1 xy.2 : ℝ)) ≤
      α / 4 * A.card * B.card) :
    (1 - α) * ((A.sup id).card : ℝ) * (B.sup id).card ≤
      ∑ x ∈ A.sup id, (((B.sup id).filter (G.Adj x)).card : ℝ) := by
  let X := A.sup id
  let Y := B.sup id
  let Q := P.ofSubset hA rfl
  let R := P.ofSubset hB rfl
  let miss := fun x y : V => ¬ G.Adj x y
  have loss (a b : Finset V) (ha : a ∈ P.parts) (hb : b ∈ P.parts) :
      ((Rel.interedges miss a b).card : ℝ) ≤ (1 - (G.edgeDensity a b : ℝ)) * (4 * (w:ℝ)^2) := by
    have hsum := Rel.card_interedges_add_card_interedges_compl G.Adj a b
    have hsum' : ((G.interedges a b).card : ℝ) + (Rel.interedges miss a b).card =
        (a.card : ℝ) * b.card := by exact_mod_cast hsum
    have hne : (a.card : ℝ) * b.card ≠ 0 := mul_ne_zero
      (by exact_mod_cast (P.nonempty_of_mem_parts ha).card_pos.ne')
      (by exact_mod_cast (P.nonempty_of_mem_parts hb).card_pos.ne')
    have he : (G.edgeDensity a b : ℝ) * (a.card * (b.card : ℝ)) = (G.interedges a b).card := by
      rw [edgeDensity_def]; push_cast; exact div_mul_cancel₀ _ hne
    have hsmall : (a.card : ℝ) * b.card ≤ (2 * (w:ℝ)) * (2 * w) := by
      gcongr
      · exact_mod_cast (hw a ha).2
      · exact_mod_cast (hw b hb).2
    calc
      _ = (1 - (G.edgeDensity a b : ℝ)) * (a.card * (b.card : ℝ)) := by linarith only [he, hsum']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [hsmall])
        (sub_nonneg.mpr (by exact_mod_cast G.edgeDensity_le_one a b))
  have count : (Rel.interedges miss X Y).card =
      ∑ xy ∈ A ×ˢ B, (Rel.interedges miss xy.1 xy.2).card := by
    exact Rel.card_interedges_finpartition miss Q R
  have lower (C : Finset (Finset V)) (hC : C ⊆ P.parts) :
      C.card * w ≤ (C.sup id).card := by
    rw [← (P.ofSubset hC rfl).sum_card_parts]
    simpa using (Finset.sum_le_sum (s := C) (f := fun _ => w) (g := Finset.card)
      fun a ha => (hw a (hC ha)).1)
  have size : ((A.card : ℝ) * w) * (B.card * (w : ℝ)) ≤ (X.card : ℝ) * Y.card := by
    gcongr
    · exact_mod_cast lower A hA
    · exact_mod_cast lower B hB
  have missing : ((Rel.interedges miss X Y).card : ℝ) ≤ α * X.card * Y.card := by
    rw [count, Nat.cast_sum]
    calc
      _ ≤ ∑ xy ∈ A ×ˢ B, (1 - (G.edgeDensity xy.1 xy.2 : ℝ)) * (4 * (w : ℝ)^2) :=
        sum_le_sum fun xy hxy => loss _ _ (hA (mem_product.mp hxy).1) (hB (mem_product.mp hxy).2)
      _ = _ := (Finset.sum_mul ..).symm
      _ ≤ (α / 4 * A.card * B.card) * (4 * (w : ℝ)^2) := by gcongr
      _ = α * ((A.card * (w : ℝ)) * (B.card * (w : ℝ))) := by ring
      _ ≤ _ := by rw [mul_assoc α]; exact mul_le_mul_of_nonneg_left size hα
  have full : ((Rel.interedges G.Adj X Y).card : ℝ) + (Rel.interedges miss X Y).card =
      (X.card : ℝ) * Y.card := by exact_mod_cast Rel.card_interedges_add_card_interedges_compl G.Adj X Y
  have rows : (Rel.interedges G.Adj X Y).card = ∑ x ∈ X, (Y.filter (G.Adj x)).card := by
    rw [Rel.interedges_eq_biUnion, card_biUnion]
    · simp
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro e he hf
      obtain ⟨z,_,rfl⟩ := mem_map.mp he
      obtain ⟨_,_,heq⟩ := mem_map.mp hf
      exact hxy (congrArg Prod.fst heq).symm
  change (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ)
  rw [← Nat.cast_sum, ← rows]
  linarith only [full, missing]

end Lift

open Filter SimpleGraph Finset

/-- Connected matching embedding, exactly as in Łuczak R1.H2 (already proved upstream). -/
def H1 : Prop :=
  ∀ (d δ : ℝ), 0 < d → 0 < δ → δ < 1 →
    ∃ η > (0 : ℝ), ∀ (t : ℕ), ∃ m₀ : ℕ,
      ∀ (N n m k : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
        Even n → 4 ≤ n → 1 ≤ k → m₀ ≤ m → (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) →
        Pairwise (fun i j => Disjoint (parts i) (parts j)) →
        (∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1) →
        (∀ u v : Fin t, R.Adj u v →
          G.IsUniform η (parts u) (parts v) ∧ (d : ℝ) ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) →
        M.IsMatching → 2 * k ≤ M.verts.ncard →
        (∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) →
        (cycleGraph n).IsContained G

/-- Residual stability on a common regular partition. The three alternatives are a
large connected matching on regular dense pairs of one colour, a cycle in the host
(allowing the other extremal configurations), and an EC2 partition of the clusters.
The density deficits for EC2 are unweighted sums over ordered pairs of clusters. -/
def H2 : Prop := ∀ α : ℝ, 0 < α → ∃ d δ ρ : ℝ, 0 < d ∧ 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
  ∀ η : ℝ, 0 < η → η ≤ ρ → ∃ l : ℕ, ∀ B : ℕ, ∀ᶠ m : ℕ in atTop,
  let V := Fin (4 * m)
  ∀ (c : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (c i).Adj]
    (P : Finpartition (univ : Finset V)), (⊤ : SimpleGraph V).IsEdgeColouring c →
    P.IsEquipartition → l ≤ #P.parts → #P.parts ≤ B →
    (∃ b ⊆ P.parts.offDiag, (b.card : ℝ) ≤ P.parts.offDiag.card * η ∧
      ∀ x ∈ P.parts.offDiag, x ∉ b → (∀ i, (c i).IsUniform η x.1 x.2) ∧
        ∃ i, (1 / 3 : ℚ) ≤ (c i).edgeDensity x.1 x.2) →
    let t := P.parts.card
    let w := (4 * m) / t
    (∃ (i : Fin 3) (k : ℕ) (e : Fin t ≃ P.parts) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
      let p := fun u => (e u).val
      1 ≤ k ∧ (2 * (m : ℝ)) ≤ (1 - δ) * (2 * k * w) ∧
      (∀ u v, R.Adj u v → (c i).IsUniform η (p u) (p v) ∧ d ≤ ((c i).edgeDensity (p u) (p v) : ℝ)) ∧
      M.IsMatching ∧ 2 * k ≤ M.verts.ncard ∧ ∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) ∨
    (∃ i, cycleGraph (2 * m) ⊑ c i) ∨
    ∃ (g : Finset V → Fin 4) (σ : Equiv.Perm (Fin 3)),
    let S := fun j : Fin 4 => P.parts.filter (fun X => g X = j)
    let dense := fun (i : Fin 3) (A B : Finset (Finset V)) =>
      ∑ xy ∈ A ×ˢ B, (1 - ((c (σ i)).edgeDensity xy.1 xy.2 : ℝ)) ≤ α / 4 * A.card * B.card
    (∀ j, (1 - α) * m ≤ ((S j).card : ℝ) * w) ∧
      dense 0 (S 0) (S 1) ∧ dense 1 (S 2) (S 0 ∪ S 1) ∧ dense 2 (S 3) (S 0 ∪ S 1)

theorem main : H1 → H2 → OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2.H1 := by
  intro embed stability α hα
  obtain ⟨d, δ, ρ, hd, hδ, hδ₁, hρ, hstab⟩ := stability α hα
  obtain ⟨η, hη, hEmbed⟩ := embed d δ hd hδ hδ₁
  choose cut hcut using hEmbed
  let ε := min 1 (min η ρ / 2)
  have hε : 0 < ε := lt_min (by norm_num) (half_pos (lt_min hη hρ))
  have hmin : 2 * ε ≤ min η ρ := by linarith [min_le_right (1 : ℝ) (min η ρ / 2)]
  have hη' := hmin.trans (min_le_left η ρ)
  obtain ⟨l, hst⟩ := hstab (2 * ε) (by positivity) (hmin.trans (min_le_right η ρ))
  obtain ⟨B, hb⟩ := simultaneous_equipartition.{0} ε hε (min_le_left ..) l
  let K := (range (B + 1)).sup cut
  filter_upwards [hst B, eventually_ge_atTop (max (max B 2) (K * B))] with m hm hm'
  intro c _ hc
  obtain ⟨P, hp, hlo, hhi, hr, hg⟩ := hb (c 0) (c 1) (by simp only [Fintype.card_fin]; omega)
  rcases hm c P hc hp hlo hhi (joint_pairs c hc P hr hg) with matchCase | done
  · obtain ⟨i,k,e,R,M,hk,hlen,hu,hM,hsize,hcon⟩ := matchCase
    let t := P.parts.card
    let w := (4 * m) / t
    let v₀ : Fin (4*m) := ⟨0, by omega⟩
    have ht : 0 < t := Finset.card_pos.mpr ⟨P.part v₀, P.part_mem.mpr (mem_univ _)⟩
    have hKt : cut t ≤ K := Finset.le_sup (f := cut) (mem_range.mpr (by omega : t < B+1))
    have hcutw : cut t ≤ w := (Nat.le_div_iff_mul_le ht).mpr
      ((Nat.mul_le_mul hKt hhi).trans (by omega))
    refine Or.inl ⟨i, hcut t _ _ w k (c i) (fun u => (e u).val) R M
      (even_two_mul m) (by omega) hk hcutw (by simpa using hlen) ?_ ?_ ?_ hM hsize hcon⟩
    · intro u v huv
      exact P.disjoint (e u).property (e v).property fun heq => huv (e.injective (Subtype.ext heq))
    · intro u
      exact ⟨by simpa [w, t] using hp.average_le_card_part (e u).property,
        by simpa [w, t] using hp.card_part_le_average_add_one (e u).property⟩
    · intro u v hadj
      obtain ⟨hunif,hdens⟩ := hu u v hadj
      exact ⟨hunif.mono hη', hdens⟩
  · rcases done with cyc | ⟨g,σ,hblocks⟩
    · exact Or.inl cyc
    let S := fun j : Fin 4 => P.parts.filter (fun X => g X = j)
    let w := (4 * m) / P.parts.card
    have sub (j : Fin 4) : S j ⊆ P.parts := filter_subset ..
    have subU : S 0 ∪ S 1 ⊆ P.parts := union_subset (sub 0) (sub 1)
    have partsize (X : Finset (Fin (4*m))) (hx : X ∈ P.parts) :
        w ≤ X.card ∧ X.card ≤ 2 * w := by
      have hpos : 0 < P.parts.card := (Finset.card_pos.mpr ⟨_, hx⟩)
      have hle : P.parts.card ≤ 4*m := by simpa using P.card_parts_le_card
      have hwpos : 0 < w := Nat.div_pos hle hpos
      have hlow : w ≤ X.card := by simpa [w] using hp.average_le_card_part hx
      have hhigh : X.card ≤ w + 1 := by simpa [w] using hp.card_part_le_average_add_one hx
      exact ⟨hlow, by omega⟩
    have fiber (j : Fin 4) : univ.filter (fun v => g (P.part v) = j) = (S j).sup id := by
      rw [sup_eq_biUnion]
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, S, id_eq]
      constructor
      · intro hv
        exact ⟨P.part v, ⟨P.part_mem.mpr (mem_univ _), hv⟩, P.mem_part (mem_univ _)⟩
      · rintro ⟨X, ⟨hx, hg'⟩, hv⟩
        rwa [P.part_eq_of_mem hx hv]
    obtain ⟨hs, h01, h2, h3⟩ := hblocks
    refine Or.inr ⟨fun v => g (P.part v), σ, ?_⟩
    dsimp only
    simp_rw [fiber]
    have hunion : (S 0).sup id ∪ (S 1).sup id = (S 0 ∪ S 1).sup id := (Finset.sup_union ..).symm
    rw [hunion]
    refine ⟨?_, lift_density P _ (sub 0) (sub 1) partsize hα.le h01,
      lift_density P _ (sub 2) subU partsize hα.le h2,
      lift_density P _ (sub 3) subU partsize hα.le h3⟩
    intro j
    apply (hs j).trans
    exact_mod_cast (show (S j).card * w ≤ ((S j).sup id).card by
      rw [← (P.ofSubset (sub j) rfl).sum_card_parts]
      simpa using (sum_le_sum (s := S j) (f := fun _ => w) (g := Finset.card)
        fun x hx => (partsize x (sub j hx)).1))

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1
