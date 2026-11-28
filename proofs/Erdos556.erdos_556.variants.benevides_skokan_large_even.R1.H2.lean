import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Logic.Equiv.Fin.Rotate

-- Step Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H2: hypothesis H2 of reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R1
-- Credit: @divmxnd0x (translation); the mathematics is reused from @steveDOTdigital (proof of R2.H2, PR 7465)
-- and @abduljaleel (reduction R2, PR 6107), with thanks.

/-!
# Step R1.H2 of Benevides-Skokan (EC2 colourings contain a monochromatic `C_n`)

R1.H2 asks for a monochromatic `C_n` in every 3-colouring of `K_{2n}` of type EC2: four blocks
`W 0, ..., W 3` of size at least `(1 - α) n / 2`, colour 0 dense between `W 0` and `W 1`, colour 1
dense between `W 0 ∪ W 1` and `W 2`, colour 2 dense between `W 0 ∪ W 1` and `W 3`.

This is exactly the configuration handled in the merged proof of step R2.H2 of the sibling reduction
R2 (its proof never uses the two extra `narrow` hypotheses). We reuse that argument verbatim:
* the alternating-cycle / Hall lemmas `cycle_rotate_val`, `cycle_of_alternating_representatives`,
  `hall_cycle_with_exceptions` (with `ec2_common_with_exceptions`, `cycle_from_dense_block`) are
  copied from `reductions/Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.lean`;
* the absorption lemmas of namespace `FourBlockAbsorption` and the final argument (`core`) are
  copied from `proofs/Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H2.lean`;
and only translate the hypotheses (`Nat.card` of subtypes of ordered pairs into sums over blocks,
`Fin (2 * n)` with `n = m + m` into `Fin (4 * m)`, and `α ≤ 10⁻⁹` into the fixed `α = 10⁻⁹`).
-/

open Filter SimpleGraph
open scoped Fin.NatCast

namespace OMA.P556R1H2

open Finset

theorem ec2_common_with_exceptions {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U C : Finset V) (m : ℕ) (α : ℝ)
    (hm : 0 < m) (hα : 0 ≤ α) (hα' : α ≤ 1 / 1000)
    (hU : 2 * (1 - α) * (m : ℝ) ≤ (U.card : ℝ))
    (hC : (1 + 11 / 4 * α) * (m : ℝ) ≤ (C.card : ℝ) ∨
      m ≤ (C.filter (fun x => 3 * U.card ≤ 5 * (U.filter (G.Adj x)).card)).card)
    (hC' : (C.card : ℝ) ≤ 4 * (m : ℝ))
    (hd : (1 - α) * (C.card : ℝ) * (U.card : ℝ) ≤
      ∑ x ∈ C, ((U.filter (G.Adj x)).card : ℝ)) :
    ∃ S ⊆ C, S.card = m ∧ ∃ P ⊆ S,
      (∀ x ∈ S, ∀ y ∈ S, 2 * P.card ≤ (U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ∉ P → y ∉ P → m ≤ (U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card) := by
  classical
  let nbr (x : V) := U.filter (G.Adj x)
  let miss (x : V) : ℝ := U.card - ((nbr x).card : ℝ)
  have hmiss (x : V) : 0 ≤ miss x := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))
  have htot : ∑ x ∈ C, miss x ≤ α * (C.card : ℝ) * (U.card : ℝ) := by
    simp only [miss, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    change (1 - α) * (C.card : ℝ) * (U.card : ℝ) ≤ ∑ x ∈ C, ((nbr x).card : ℝ) at hd
    linarith only [hd]
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hαm := mul_le_mul_of_nonneg_right hα' hmpos.le
  have hUpos : 0 < (U.card : ℝ) := by linarith only [hU, hαm, hmpos]
  have hmark (t : ℝ) (A : Finset V) (hA : A ⊆ C)
      (hcut : ∀ x ∈ A, t * (U.card : ℝ) ≤ 5 * miss x) :
      t * (A.card : ℝ) ≤ 5 * α * (C.card : ℝ) := by
    have hsum : ∑ x ∈ A, miss x ≤ ∑ x ∈ C, miss x :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun x _ _ => hmiss x)
    have hlow : (A.card : ℝ) * (t * (U.card : ℝ)) ≤ 5 * (∑ x ∈ A, miss x) := by
      calc (A.card : ℝ) * (t * (U.card : ℝ)) = ∑ _x ∈ A, (t * (U.card : ℝ)) := by
             simp [Finset.sum_const, nsmul_eq_mul]
           _ ≤ ∑ x ∈ A, 5 * miss x := Finset.sum_le_sum hcut
           _ = _ := (Finset.mul_sum ..).symm
    apply (mul_le_mul_iff_left₀ hUpos).mp
    linarith only [hlow, hsum, htot]
  let B := C.filter fun x => 2 * (U.card : ℝ) < 5 * miss x
  have hBC : B ⊆ C := Finset.filter_subset _ _
  have hgood : m ≤ (C \ B).card := by
    rcases hC with hC | hC
    · have hbad := hmark 2 B hBC (fun x hx => (Finset.mem_filter.mp hx).2.le)
      have hprod : 1 ≤ (1 - 5 / 2 * α) * (1 + 11 / 4 * α) := by
        nlinarith only [mul_nonneg hα (show 0 ≤ 1 / 4 - 55 / 8 * α by linarith only [hα'])]
      have hmore : (m : ℝ) ≤ (1 - 5 / 2 * α) * (C.card : ℝ) := by
        calc (m : ℝ) ≤ ((1 - 5 / 2 * α) * (1 + 11 / 4 * α)) * m := by
               simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod hmpos.le
             _ = (1 - 5 / 2 * α) * ((1 + 11 / 4 * α) * m) := mul_assoc _ _ _
             _ ≤ _ := mul_le_mul_of_nonneg_left hC (by linarith only [hα'])
      have hcard : (C \ B).card + B.card = C.card := Finset.card_sdiff_add_card_eq_card hBC
      have hcardR : ((C \ B).card : ℝ) + (B.card : ℝ) = C.card := by exact_mod_cast hcard
      exact_mod_cast (show (m : ℝ) ≤ ((C \ B).card : ℝ) by linarith only [hmore, hcardR, hbad])
    · apply hC.trans
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxC, hxdeg⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_sdiff.mpr
      refine ⟨hxC, ?_⟩
      intro hxB
      have hxmiss := (Finset.mem_filter.mp hxB).2
      have hxdegR : 3 * (U.card : ℝ) ≤ 5 * ((nbr x).card : ℝ) := by
        exact_mod_cast hxdeg
      change 2 * (U.card : ℝ) < 5 * ((U.card : ℝ) - ((nbr x).card : ℝ)) at hxmiss
      linarith only [hxdegR, hxmiss]
  obtain ⟨S, hS, hSm⟩ := Finset.exists_subset_card_eq hgood
  have hSC : S ⊆ C := fun x hx => (Finset.mem_sdiff.mp (hS hx)).1
  let P := S.filter fun x => (U.card : ℝ) < 5 * miss x
  have hPS : P ⊆ S := Finset.filter_subset _ _
  have hpoor := hmark 1 P (hPS.trans hSC) (by
    intro x hx
    rw [one_mul]
    exact (Finset.mem_filter.mp hx).2.le)
  have hαC' := mul_le_mul_of_nonneg_right hα' (Nat.cast_nonneg (α := ℝ) C.card)
  have hpU : 10 * (P.card : ℝ) ≤ U.card := by
    linarith only [hpoor, hαC', hC', hU, hαm, hmpos]
  have htyp {x : V} (hx : x ∈ S) : 5 * miss x ≤ 2 * (U.card : ℝ) := by
    obtain ⟨hxC, hxB⟩ := Finset.mem_sdiff.mp (hS hx)
    exact le_of_not_gt fun hb => hxB (Finset.mem_filter.mpr ⟨hxC, hb⟩)
  have hhigh {x : V} (hx : x ∈ S) (hxp : x ∉ P) : 5 * miss x ≤ U.card := by
    exact le_of_not_gt fun hb => hxp (Finset.mem_filter.mpr ⟨hx, hb⟩)
  have hcodeg (x y : V) :
      (U.card : ℝ) - miss x - miss y ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) := by
    have hu : (nbr x ∪ nbr y) ⊆ U :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hi := Finset.card_union_add_card_inter (nbr x) (nbr y)
    have hib : (nbr x).card + (nbr y).card ≤ U.card + (nbr x ∩ nbr y).card := by
      rw [← hi]
      exact Nat.add_le_add_right (Finset.card_le_card hu) _
    have heq : nbr x ∩ nbr y = U.filter (fun z => G.Adj x z ∧ G.Adj y z) := by
      ext z
      simp [nbr, and_assoc, and_left_comm, and_comm]
    rw [heq] at hib
    have hr : ((nbr x).card : ℝ) + ((nbr y).card : ℝ) ≤ U.card +
        ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) := by exact_mod_cast hib
    dsimp only [miss]
    linarith only [hr]
  refine ⟨S, hSC, hSm, P, hPS, ?_, ?_⟩
  · intro x hx y hy
    exact_mod_cast (show 2 * (P.card : ℝ) ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) by
      linarith only [hcodeg x y, htyp hx, htyp hy, hpU])
  · intro x hx y hy hxp hyp
    exact_mod_cast (show (m : ℝ) ≤ ((U.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) by
      linarith only [hcodeg x y, hhigh hx hxp, hhigh hy hyp, hU, hαm, hmpos])

open SimpleGraph

theorem cycle_rotate_val {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    (finRotate m i).val = (i.val + 1) % m := by
  haveI : NeZero m := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]

theorem cycle_of_alternating_representatives {V : Type*} (G : SimpleGraph V)
    {m : ℕ} (hm : 2 ≤ m) (U : Finset V) (x y : Fin m → V)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxu : ∀ i, x i ∉ U)
    (hmem : ∀ i, y i ∈ U ∧ G.Adj (x i) (y i) ∧ G.Adj (x (finRotate m i)) (y i)) :
    (cycleGraph (2 * m)).IsContained G := by
  have hxy (i j : Fin m) : x i ≠ y j := fun h => hxu i (by simpa only [h] using (hmem j).1)
  let half (a : Fin (2 * m)) : Fin m := ⟨a.val / 2, by have := a.isLt; omega⟩
  let f (a : Fin (2 * m)) := if a.val % 2 = 0 then x (half a) else y (half a)
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0
    · have he := congrArg Fin.val (hx (by simpa [f, ha, hb] using hab : x (half a) = x (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab : x (half a) = y (half b))).elim
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab.symm : x (half b) = y (half a))).elim
    · have he := congrArg Fin.val (hy (by simpa [f, ha, hb] using hab : y (half a) = y (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
  have step (a b : Fin (2 * m)) (hz : (b - a).val = 1) : G.Adj (f a) (f b) := by
    have hsize := a.isLt
    have hbsize := b.isLt
    rw [Fin.coe_sub] at hz
    have hab : b.val = a.val + 1 ∨ (a.val + 1 = 2 * m ∧ b.val = 0) := by
      by_cases hle : a.val ≤ b.val
      · rw [show 2 * m - a.val + b.val = 2 * m + (b.val - a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inr (by omega)
    rcases hab with h | ⟨haLast, hbZero⟩
    · by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 ≠ 0 := by omega
        have he : half a = half b := Fin.ext (by dsimp [half]; omega)
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.1
      · have hb : b.val % 2 = 0 := by omega
        have he : finRotate m (half a) = half b := by
          apply Fin.ext
          rw [cycle_rotate_val hm]
          dsimp [half]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
    · have ha : a.val % 2 ≠ 0 := by omega
      have he : finRotate m (half a) = half b := by
        apply Fin.ext
        rw [cycle_rotate_val hm]
        dsimp [half]
        simp [show a.val / 2 + 1 = m by omega, hbZero]
      have hb : b.val % 2 = 0 := by omega
      simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
  let hom : cycleGraph (2 * m) →g G := ⟨f, by
    intro a b hab
    rcases cycleGraph_adj'.mp hab with h | h
    · exact (step b a h).symm
    · exact step a b h⟩
  exact ⟨⟨hom, hinj⟩⟩

theorem hall_cycle_with_exceptions {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℕ} (hm : 2 ≤ m) (U S P : Finset V) (hSU : Disjoint S U)
    (hs : S.card = m)
    (hmin : ∀ a ∈ S, ∀ b ∈ S, 2 * P.card ≤ (U.filter fun z => G.Adj a z ∧ G.Adj b z).card)
    (hgood : ∀ a ∈ S, ∀ b ∈ S, a ∉ P → b ∉ P → m ≤ (U.filter fun z => G.Adj a z ∧ G.Adj b z).card) :
    (cycleGraph (2 * m)).IsContained G := by
  classical
  let e : S ≃ Fin m := Finset.equivFinOfCardEq hs
  let x (i : Fin m) : V := (e.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have hxS (i : Fin m) : x i ∈ S := (e.symm i).property
  let t (i : Fin m) := U.filter fun z => G.Adj (x i) z ∧ G.Adj (x (finRotate m i)) z
  let bad (g : Fin m → V) := Finset.univ.filter fun i => g i ∈ P
  have bad_card (g : Fin m → V) (hg : Function.Injective g) : (bad g).card ≤ P.card := by
    apply Finset.card_le_card_of_injOn g
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact hg.injOn
  have hHall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    have sub (j : Fin m) (hj : j ∈ s) : (t j).card ≤ (s.biUnion t).card :=
      Finset.card_le_card (fun v hv => Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
    by_cases hh : ∃ j ∈ s, x j ∉ P ∧ x (finRotate m j) ∉ P
    · obtain ⟨j, hj, hj₁, hj₂⟩ := hh
      have hs' : s.card ≤ m := by simpa using Finset.card_le_univ s
      exact hs'.trans ((hgood _ (hxS j) _ (hxS (finRotate m j)) hj₁ hj₂).trans (sub j hj))
    · have hsub : s ⊆ bad x ∪ bad (x ∘ finRotate m) := by
        intro j hj
        by_cases hp : x j ∈ P
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
        · have hnext : x (finRotate m j) ∈ P := by
            by_contra hn
            exact hh ⟨j, hj, hp, hn⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnext⟩)
      have hab := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h₁ := bad_card x hx
      have h₂ := bad_card (x ∘ finRotate m) (hx.comp (finRotate m).injective)
      have hs' : s.card ≤ 2 * P.card := by omega
      exact hs'.trans ((hmin _ (hxS i) _ (hxS (finRotate m i))).trans (sub i hi))
  obtain ⟨y, hy, hyt⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  apply cycle_of_alternating_representatives G hm U x y hx hy
  · exact fun i => Finset.disjoint_left.mp hSU (hxS i)
  · exact fun i => Finset.mem_filter.mp (hyt i)

theorem cycle_from_dense_block {m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (U C : Finset (Fin (4 * m))) (hCU : Disjoint C U) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1/1000)
    (hU : 2*(1-α)*(m : ℝ) ≤ U.card)
    (hC : (1+11/4*α)*(m : ℝ) ≤ C.card ∨
      m ≤ (C.filter (fun x => 3*U.card ≤ 5*(U.filter (G.Adj x)).card)).card)
    (hd : (1-α)*(C.card : ℝ)*U.card ≤ ∑ x ∈ C, ((U.filter (G.Adj x)).card : ℝ)) :
    cycleGraph (2*m) ⊑ G := by
  have hupp : C.card ≤ 4*m := by simpa using Finset.card_le_univ C
  obtain ⟨S,hSC,hs,P,_,hmin,hgood⟩ := ec2_common_with_exceptions G U C m α
    (by omega) hα.le hα' hU hC (by exact_mod_cast hupp) hd
  exact hall_cycle_with_exceptions G hm U S P (hCU.mono_left hSC) hs hmin hgood

end OMA.P556R1H2

open Finset SimpleGraph Filter
open OMA.P556R1H2

namespace FourBlockAbsorption
 
private def nb {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) := U.filter (G.Adj x)

private def holes {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) := U.filter (fun y => ¬ G.Adj x y)

private def both {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x y : V) := U.filter (fun z => G.Adj x z ∧ G.Adj y z)

private theorem part {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) : (nb G U x).card + (holes G U x).card = U.card :=
  card_filter_add_card_filter_not (G.Adj x)

private theorem common {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (a b : V) :
    (nb G U a).card ≤ (both G U a b).card + (holes G U b).card := by
  have sub : nb G U a ⊆ both G U a b ∪ holes G U b := by
    intro z hz
    obtain ⟨hu,ha⟩ := mem_filter.mp hz
    by_cases hb : G.Adj b z
    · exact mem_union_left _ (mem_filter.mpr ⟨hu,ha,hb⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hu,hb⟩)
  exact (card_le_card sub).trans (card_union_le ..)

private theorem nb_restrict {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R U : Finset V) (h : R ⊆ U) (x : V) :
    (nb G U x).card ≤ (nb G R x).card + (U.card-R.card) := by
  have sub : nb G U x ⊆ nb G R x ∪ (U \ R) := by
    intro z hz
    obtain ⟨hu,ha⟩ := mem_filter.mp hz
    by_cases hr : z ∈ R
    · exact mem_union_left _ (mem_filter.mpr ⟨hr,ha⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hu,hr⟩)
  simpa [card_sdiff_of_subset h] using (card_le_card sub).trans (card_union_le ..)

private theorem hole_mono {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {R U : Finset V} (h : R ⊆ U) (x : V) : (holes G R x).card ≤ (holes G U x).card :=
  card_le_card (filter_subset_filter _ h)

/-- Order a finite set with its exceptional entries in mutually nonconsecutive
cyclic slots. Extend the injection assigning those entries even positions. -/
private theorem separated_order {V : Type*} [DecidableEq V] {m : ℕ} (hm : 2 ≤ m)
    (S P : Finset V) (hP : P ⊆ S) (hs : S.card=m) (hp : 2*P.card ≤ m) :
    ∃ x : Fin m → V, Function.Injective x ∧ (∀ i,x i ∈ S) ∧
      ∀ i, x i ∉ P ∨ x (finRotate m i) ∉ P := by
  classical
  let e := S.equivFinOfCardEq hs
  let b (w : P) : Fin m := e ⟨w.val,hP w.property⟩
  let k := P.equivFin
  let pos (w : P) : Fin m := ⟨2*(k w).val,by have := (k w).isLt; omega⟩
  have hb : Function.Injective b := by
    intro v w eq; exact Subtype.ext (congrArg (fun z : S => z.val) (e.injective eq))
  have hpos : Function.Injective pos := by
    intro v w eq; apply k.injective; apply Fin.ext
    have eq' := congrArg Fin.val eq
    change 2*_ = 2*_ at eq'; omega
  obtain ⟨φ,hφ⟩ := Equiv.Perm.exists_extending_pair b pos hb hpos
  let x (i : Fin m) := (e.symm (φ.symm i)).val
  have ispos (i : Fin m) (hi : x i ∈ P) : i=pos ⟨x i,hi⟩ := by
    rw [←hφ]
    have he : b ⟨x i,hi⟩=φ.symm i := by
      apply e.symm.injective; apply Subtype.ext
      simp [b,x]
    rw [he,φ.apply_symm_apply]
  refine ⟨x,Subtype.val_injective.comp (e.symm.injective.comp φ.symm.injective),
    fun i => (e.symm (φ.symm i)).property,?_⟩
  intro i
  by_contra! outside
  obtain ⟨hi,hj⟩ := outside
  have ei := congrArg Fin.val (ispos i hi)
  have ej := congrArg Fin.val (ispos (finRotate m i) hj)
  rw [cycle_rotate_val hm] at ej
  change i.val=2*(k ⟨x i,hi⟩).val at ei
  change (i.val+1)%m=2*(k ⟨x (finRotate m i),hj⟩).val at ej
  have lt := (k ⟨x i,hi⟩).isLt
  rw [Nat.mod_eq_of_lt (by omega)] at ej
  omega

private theorem hall_cycle {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (hm : 2 ≤ m) (R : Finset V) (x : Fin m → V) (hx : Function.Injective x)
    (out : ∀ i,x i ∉ R)
    (hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion fun i => both G R (x i) (x (finRotate m i))).card)
    : cycleGraph (2*m) ⊑ G := by
  classical
  let t (i : Fin m) := both G R (x i) (x (finRotate m i))
  obtain ⟨y,hy,ht⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  exact cycle_of_alternating_representatives G hm R x y hx hy out (fun i => mem_filter.mp (ht i))

/-- Fill the gaps by Hall. A gap touching an exceptional center needs only
enough neighbors to cover the at most twice as many exceptional gaps. -/
private theorem absorb {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m) (R S P : Finset V) (sep : Disjoint S R) (hP : P ⊆ S)
    (hs : S.card=m) (hp : 2*P.card ≤ m)
    (one : ∀ a ∈ S, ∀ b ∈ S, a ∉ P ∨ b ∉ P → 2*P.card ≤ (both G R a b).card)
    (two : ∀ a ∈ S, ∀ b ∈ S, a ∉ P → b ∉ P → m ≤ (both G R a b).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  obtain ⟨x,hx,hxS,hpos⟩ := separated_order hm S P hP hs hp
  apply hall_cycle G hm R x hx (fun i => Finset.disjoint_left.mp sep (hxS i))
  intro s
  let t (i : Fin m) := both G R (x i) (x (finRotate m i))
  change s.card ≤ (s.biUnion t).card
  rcases s.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · simp
  have le (j : Fin m) (hj : j ∈ s) : (t j).card ≤ (s.biUnion t).card :=
    card_le_card (fun z hz => mem_biUnion.mpr ⟨j,hj,hz⟩)
  by_cases good : ∃ j ∈ s,x j ∉ P ∧ x (finRotate m j) ∉ P
  · obtain ⟨j,hj,h₁,h₂⟩ := good
    exact (show s.card ≤ m by simpa using card_le_univ s).trans
      ((two _ (hxS j) _ (hxS _) h₁ h₂).trans (le j hj))
  · let bad (g : Fin m → V) := univ.filter (fun j => g j ∈ P)
    have cardBad (g : Fin m → V) (hg : Function.Injective g) : (bad g).card ≤ P.card :=
      card_le_card_of_injOn g (fun _ h => (mem_filter.mp h).2) hg.injOn
    have sub : s ⊆ bad x ∪ bad (x ∘ finRotate m) := by
      intro j hj
      by_cases h : x j ∈ P
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,
          by by_contra hn; exact good ⟨j,hj,h,hn⟩⟩)
    have hs' := (card_le_card sub).trans (card_union_le ..)
    have left := cardBad x hx
    have right := cardBad _ (hx.comp (finRotate m).injective)
    have low := (one _ (hxS i) _ (hxS _) (hpos i)).trans (le i hi)
    omega

/-- Extend the excellent centers in C to m centers of moderate degree into
U. Fewer than 2d extra centers are needed, including any selected from U. -/
private theorem dense_join {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m d : ℕ} (hd : 0<d) (hm : 1000*d ≤ m)
    (U C : Finset V) (hCU : Disjoint C U) (hu : 2*m ≤ U.card+d)
    (hc : m ≤ C.card+d) (loss : ∑ x ∈ C, (holes G U x).card ≤ d*d)
    (enough : m ≤ (univ.filter fun x => 16*d ≤ (nb G U x).card).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let E := C.filter fun x => (holes G U x).card ≤ d
  let D := univ.filter fun x => 16*d ≤ (nb G U x).card
  have ec : E ⊆ C := filter_subset ..
  have cut : (C \ E).card*d ≤ ∑ x ∈ C, (holes G U x).card := by
    calc (C \ E).card*d = ∑ _x ∈ C \ E,d := by simp
         _ ≤ ∑ x ∈ C \ E,(holes G U x).card := sum_le_sum <| by
           intro x hx
           obtain ⟨hxC,hxE⟩ := mem_sdiff.mp hx
           by_contra! h
           exact hxE (mem_filter.mpr ⟨hxC,h.le⟩)
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (by intros; omega)
  have small : (C \ E).card ≤ d := Nat.le_of_mul_le_mul_right (cut.trans loss) hd
  have hec := card_sdiff_add_card_eq_card ec
  have ed : E ⊆ D := by
    intro x hx
    have hh := (mem_filter.mp hx).2
    change (holes G U x).card ≤ d at hh
    exact mem_filter.mpr ⟨mem_univ _,by have := part G U x; omega⟩
  obtain ⟨S₀,h₀,hsize₀⟩ := exists_subset_card_eq (min_le_right m E.card)
  obtain ⟨S,h₀S,hSD,hsize⟩ := exists_subsuperset_card_eq (h₀.trans ed)
    (hsize₀.trans_le (min_le_left ..)) enough
  let P := S \ S₀
  let R := U \ P
  have hP : P ⊆ S := sdiff_subset
  have pc : P.card ≤ 2*d := by
    have h := card_sdiff_add_card_eq_card h₀S
    change P.card+S₀.card=S.card at h
    omega
  have rem : U.card ≤ R.card+P.card := card_le_card_sdiff_add_card
  have sep : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    obtain ⟨hu',hp'⟩ := mem_sdiff.mp hr
    by_cases h : x ∈ S₀
    · exact Finset.disjoint_left.mp hCU (ec (h₀ h)) hu'
    · exact hp' (mem_sdiff.mpr ⟨hx,h⟩)
  have minDeg (x) (hx : x ∈ S) : 16*d ≤ (nb G R x).card+P.card := by
    have hs : 16*d ≤ (nb G U x).card := (mem_filter.mp (hSD hx)).2
    have h := nb_restrict G R U sdiff_subset x
    omega
  have maxLoss (x) (hx : x ∈ S) (hp : x ∉ P) : (holes G R x).card ≤ d := by
    have h : x ∈ S₀ := by by_contra he; exact hp (mem_sdiff.mpr ⟨hx,he⟩)
    exact (hole_mono G (show R ⊆ U from sdiff_subset) x).trans ((mem_filter.mp (h₀ h)).2)
  apply absorb G (by omega) R S P sep hP hsize (by omega)
  · intro a ha b hb h
    rcases h with good | good
    · have eq : both G R a b=both G R b a := by ext; simp [both,and_comm]
      rw [eq]
      have := common G R b a
      have := minDeg b hb
      have := maxLoss a ha good
      omega
    · have := common G R a b
      have := minDeg a ha
      have := maxLoss b hb good
      omega
  · intro a ha b hb h₁ h₂
    have := part G R a
    have := common G R a b
    have := maxLoss a ha h₁
    have := maxLoss b hb h₂
    omega

/-- If at least 2m vertices see almost all of U in red, use outside
vertices as centers whenever possible. When too few are outside, use
m inside vertices as connectors and count missing gaps in each column. -/
private theorem red_finish {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m d : ℕ} (hd : 0<d) (hm : 1000*d ≤ m)
    (U Z : Finset V) (hu : 2*m ≤ U.card+d) (hz : 2*m ≤ Z.card)
    (red : ∀ x ∈ Z,(holes G U x).card ≤ 33*d) : cycleGraph (2*m) ⊑ G := by
  classical
  by_cases outside : m ≤ 4*(Z \ U).card
  · obtain ⟨E,he,heC⟩ := exists_subset_card_eq (min_le_right m (Z \ U).card)
    obtain ⟨S,hES,hSZ,hS⟩ := exists_subsuperset_card_eq (he.trans sdiff_subset)
      (heC.trans_le (min_le_left ..)) (by omega : m ≤ Z.card)
    let R := U \ S
    have loss : (U∩S).card ≤ S.card-E.card := by
      rw [←card_sdiff_of_subset hES]
      apply card_le_card
      intro x hx
      obtain ⟨hxU,hxS⟩ := mem_inter.mp hx
      exact mem_sdiff.mpr ⟨hxS,fun hh => (mem_sdiff.mp (he hh)).2 hxU⟩
    have rsize : R.card+(U∩S).card=U.card := card_sdiff_add_card_inter ..
    have minRow (a) (ha:a ∈ S) (b) (hb:b ∈ S) : m ≤ (both G R a b).card := by
      have la := (hole_mono G (show R ⊆ U from sdiff_subset) a).trans (red a (hSZ ha))
      have lb := (hole_mono G (show R ⊆ U from sdiff_subset) b).trans (red b (hSZ hb))
      have := part G R a
      have := common G R a b
      omega
    apply hall_cycle_with_exceptions G (by omega) R S ∅ (Finset.disjoint_left.mpr
      (fun _ hs hr => (mem_sdiff.mp hr).2 hs)) hS
    · simp
    · intro a ha b hb _ _
      exact minRow a ha b hb
  · have inside := card_sdiff_add_card_inter Z U
    have enough : m ≤ (Z∩U).card := by omega
    obtain ⟨T,hT,tc⟩ := exists_subset_card_eq enough
    have tz : T ⊆ Z := hT.trans inter_subset_left
    have tu : T ⊆ U := hT.trans inter_subset_right
    have room := card_sdiff_add_card_eq_card tz
    obtain ⟨S,hS,sc⟩ := exists_subset_card_eq (show m ≤ (Z \ T).card by omega)
    let e := S.equivFinOfCardEq sc
    let x (i : Fin m) : V := (e.symm i).val
    have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
    have xZ (i : Fin m) : x i ∈ Z := (mem_sdiff.mp (hS (e.symm i).property)).1
    have xT (i : Fin m) : x i ∉ T := (mem_sdiff.mp (hS (e.symm i).property)).2
    apply hall_cycle G (by omega) T x hx xT
    intro s
    let t (i : Fin m) := both G T (x i) (x (finRotate m i))
    change s.card ≤ (s.biUnion t).card
    by_cases full : T ⊆ s.biUnion t
    · exact (show s.card ≤ m by simpa using card_le_univ s).trans (tc.symm.trans_le (card_le_card full))
    · obtain ⟨y,hy,miss⟩ := Finset.not_subset.mp full
      let B := (Z \ U) ∪ holes G U y
      have bsize := card_union_le (Z \ U) (holes G U y)
      have hred := red y (tz hy)
      have absent (i : Fin m) (h : ¬G.Adj (x i) y) : x i ∈ B := by
        by_cases hu' : x i ∈ U
        · exact mem_union_right _ (mem_filter.mpr ⟨hu',fun z => h z.symm⟩)
        · exact mem_union_left _ (mem_sdiff.mpr ⟨xZ i,hu'⟩)
      let bad (f : Fin m → V) := univ.filter fun i => f i ∈ B
      have badCard (f : Fin m → V) (hf : Function.Injective f) : (bad f).card ≤ B.card :=
        card_le_card_of_injOn f (fun _ h => (mem_filter.mp h).2) hf.injOn
      have subset : s ⊆ bad x ∪ bad (x ∘ finRotate m) := by
        intro i hi
        by_cases h : G.Adj (x i) y
        · have h' : ¬G.Adj (x (finRotate m i)) y :=
            fun h' => miss (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hy,h,h'⟩⟩)
          exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,absent _ h'⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,absent _ h⟩)
      have bound := (card_le_card subset).trans (card_union_le ..)
      have h₁ := badCard x hx
      have h₂ := badCard _ (hx.comp (finRotate m).injective)
      change B.card ≤ _ at bsize
      rcases s.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
      · simp
      have row := common G T (x i) (x (finRotate m i))
      have parts := part G T (x i)
      have h₃ := (hole_mono G tu _).trans (red _ (xZ i))
      have h₄ := (hole_mono G tu _).trans (red _ (xZ (finRotate m i)))
      have bound' : (t i).card ≤ (s.biUnion t).card :=
        card_le_card (fun z hz => mem_biUnion.mpr ⟨i,hi,hz⟩)
      change (both G T (x i) (x (finRotate m i))).card ≤ _ at bound'
      omega

end FourBlockAbsorption

open FourBlockAbsorption

namespace OMA.P556R1H2

open Classical in
/-- The EC2 argument of the merged proof of R2.H2, for `N = 4 m` vertices and `α = 10⁻⁹`. -/
theorem core (m : ℕ) (hlarge : 1000 ≤ m) (N : ℕ) (hN : N = 4 * m)
    (c : Fin 3 → SimpleGraph (Fin N))
    (colour : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) (f : Fin N → Fin 4)
    (σ : Equiv.Perm (Fin 3)) :
    let α : ℝ := 1 / 1000000000
    let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin N => f v = j)
    let U := W 0 ∪ W 1
    let dense := fun (i : Fin 3) (X Y : Finset (Fin N)) =>
      (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
    ((∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
      dense 0 (W 0) (W 1) ∧ dense 1 (W 2) U ∧ dense 2 (W 3) U) →
    ∃ i, cycleGraph (2 * m) ⊑ c i := by
  subst hN
  intro α W U dense data
  let d := m/1000
  have hd : 0<d := by dsimp [d]; omega
  have hm : 1000*d ≤ m := by dsimp [d]; omega
  have upper : m ≤ 2000*d := by dsimp [d]; omega
  have realUpper : (m:ℝ) ≤ 2000*(d:ℝ) := by exact_mod_cast upper
  have low (j : Fin 4) : (1-α)*(m:ℝ) ≤ (W j).card := data.1 j
  have dis {i j : Fin 4} (h:i≠j) : Disjoint (W i) (W j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact h ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
  have hU : 2*m ≤ U.card+d := by
    have cardU : U.card=(W 0).card+(W 1).card := card_union_of_disjoint (dis (by decide))
    rw [cardU]
    have h0 := low 0
    have h1 := low 1
    dsimp [α] at h0 h1
    exact_mod_cast (show 2*(m:ℝ) ≤ ((W 0).card:ℝ)+((W 1).card:ℝ)+d by linarith)
  let D (i : Fin 3) := univ.filter fun x => 16*d ≤ (nb (c (σ i)) U x).card
  by_contra no
  have few (i : Fin 3) (j : Fin 4) (h0 : j≠0) (h1 : j≠1)
      (density : (1-α)*((W j).card:ℝ)*U.card ≤ ∑ x ∈ W j,((nb (c (σ i)) U x).card:ℝ)) :
      (D i).card < m := by
    by_contra! plentiful
    let C := W j
    let G := c (σ i)
    have Csize : m ≤ C.card+d := by
      have lower := low j
      dsimp [α] at lower
      exact_mod_cast (show (m:ℝ) ≤ (C.card:ℝ)+d by change (m:ℝ) ≤ ((W j).card:ℝ)+d; linarith)
    have cup : C.card ≤ 4*m := by simpa using card_le_univ C
    have uup : U.card ≤ 4*m := by simpa using card_le_univ U
    have Ccap : (C.card:ℝ) ≤ 8000*(d:ℝ) := by exact_mod_cast (show C.card ≤ 8000*d by omega)
    have Ucap : (U.card:ℝ) ≤ 8000*(d:ℝ) := by exact_mod_cast (show U.card ≤ 8000*d by omega)
    have allPairs : (∑ x ∈ C,(holes G U x).card)+(∑ x ∈ C,(nb G U x).card)=C.card*U.card := by
      rw [←sum_add_distrib]
      calc (∑ x ∈ C,((holes G U x).card+(nb G U x).card)) = ∑ _x ∈ C,U.card :=
             sum_congr rfl (fun x _ => (Nat.add_comm ..).trans (part G U x))
           _ = _ := by simp
    have allReal := congrArg (fun n : ℕ => (n:ℝ)) allPairs
    push_cast at allReal
    change (1-α)*(C.card:ℝ)*U.card ≤ ∑ x ∈ C,((nb G U x).card:ℝ) at density
    have hLoss : (∑ x ∈ C,((holes G U x).card:ℝ)) ≤ α*(C.card:ℝ)*U.card := by
      linarith only [allReal,density]
    have loss : ∑ x ∈ C,(holes G U x).card ≤ d*d := by
      have cap : α*(C.card:ℝ)*U.card ≤ α*(8000*(d:ℝ))*(8000*(d:ℝ)) := by
        gcongr <;> first | exact Ccap | exact Ucap | positivity
      have num : α*(8000*(d:ℝ))*(8000*(d:ℝ)) ≤ (d:ℝ)*d := by dsimp [α]; nlinarith [sq_nonneg (d:ℝ)]
      exact_mod_cast hLoss.trans (cap.trans num)
    have hCU : Disjoint C U := disjoint_union_right.mpr ⟨dis h0,dis h1⟩
    exact no ⟨σ i,dense_join G hd hm U C hCU hU Csize loss plentiful⟩
  have h₁ := few 1 2 (by decide) (by decide) data.2.2.1
  have h₂ := few 2 3 (by decide) (by decide) data.2.2.2
  let Z := univ \ (D 1 ∪ D 2)
  have zsize : 2*m ≤ Z.card := by
    have sum := card_sdiff_add_card_eq_card (subset_univ (D 1 ∪ D 2))
    change Z.card+(D 1 ∪ D 2).card=_ at sum
    rw [card_univ,Fintype.card_fin] at sum
    have := card_union_le (D 1) (D 2)
    omega
  apply no
  refine ⟨σ 0,red_finish (c (σ 0)) hd hm U Z hU zsize ?_⟩
  intro x hx
  have hnot := (mem_sdiff.mp hx).2
  have gsmall : (nb (c (σ 1)) U x).card < 16*d := by
    by_contra! h; exact hnot (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩))
  have bsmall : (nb (c (σ 2)) U x).card < 16*d := by
    by_contra! h; exact hnot (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
  have cover : holes (c (σ 0)) U x ⊆ insert x (nb (c (σ 1)) U x ∪ nb (c (σ 2)) U x) := by
    intro y hy
    obtain ⟨hyU,hn⟩ := mem_filter.mp hy
    by_cases he : y=x
    · exact mem_insert.mpr (.inl he)
    apply mem_insert_of_mem
    have edge : (⊤ : SimpleGraph (Fin (4*m))).Adj x y := fun h => he h.symm
    rw [colour.1,SimpleGraph.iSup_adj] at edge
    obtain ⟨i,hi⟩ := edge
    obtain ⟨j,rfl⟩ := σ.surjective i
    fin_cases j
    · exact (hn hi).elim
    · exact mem_union_left _ (mem_filter.mpr ⟨hyU,hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hyU,hi⟩)
  have h := (card_le_card cover).trans (card_insert_le ..)
  have := card_union_le (nb (c (σ 1)) U x) (nb (c (σ 2)) U x)
  omega


end OMA.P556R1H2

namespace OMA.P556R1H2

open Finset

open Classical in
/-- Ordered pairs counted by their first coordinate. -/
theorem pairs_left {N : ℕ} (f : Fin N → Fin 4) (G : SimpleGraph (Fin N)) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ x ∈ univ.filter (fun v => f v ∈ S),
        ((univ.filter (fun v => f v ∈ T)).filter (G.Adj x)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, Fintype.sum_prod_type,
    sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : f x ∈ S
  · simp only [hx, true_and, if_true]
    rw [filter_filter, card_filter]
  · simp [hx]

open Classical in
/-- Ordered pairs counted by their second coordinate. -/
theorem pairs_right {N : ℕ} (f : Fin N → Fin 4) (G : SimpleGraph (Fin N)) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ y ∈ univ.filter (fun v => f v ∈ T),
        ((univ.filter (fun v => f v ∈ S)).filter (G.Adj y)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter, Fintype.sum_prod_type_right,
    sum_filter]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : f y ∈ T
  · simp only [hy, true_and, and_true, if_true]
    rw [filter_filter, card_filter]
    refine sum_congr rfl fun x _ => ?_
    rw [G.adj_comm]
  · simp [hy]

end OMA.P556R1H2

open Finset in
theorem OMA.solution : OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1.H2 := by
  classical
  refine ⟨1 / 1000000000, by norm_num, fun α hα hα' => ?_⟩
  filter_upwards [eventually_ge_atTop 2000] with n hn heven c hc f hsize hdens
  obtain ⟨m, rfl⟩ := heven
  have hm : 1000 ≤ m := by omega
  have key := OMA.P556R1H2.core m hm (2 * (m + m)) (by ring) c hc f (Equiv.refl _)
  simp only [Equiv.refl_apply] at key
  have hcard (S : Finset (Fin 4)) :
      (Nat.card {v // f v ∈ S} : ℝ) = ((univ.filter fun v => f v ∈ S).card : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hW (j : Fin 4) :
      (univ.filter fun v => f v ∈ ({j} : Finset (Fin 4))) = univ.filter fun v => f v = j := by
    ext v; simp
  have hU : (univ.filter fun v => f v ∈ ({0, 1} : Finset (Fin 4))) =
      (univ.filter fun v => f v = 0) ∪ (univ.filter fun v => f v = 1) := by
    ext v; simp
  have hmono : (1 - 1 / 1000000000 : ℝ) ≤ 1 - α := by linarith
  have size (j : Fin 4) :
      (1 - 1 / 1000000000 : ℝ) * m ≤ ((univ.filter fun v => f v = j).card : ℝ) := by
    have h := hsize j
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    push_cast at h
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmono hm0]
  have d0 : (1 - 1 / 1000000000 : ℝ) * ((univ.filter fun v => f v = 0).card : ℝ) *
        (univ.filter fun v => f v = 1).card ≤
      ∑ x ∈ univ.filter (fun v => f v = 0),
        (((univ.filter fun v => f v = 1).filter ((c 0).Adj x)).card : ℝ) := by
    have h := hdens 0 {0} {1} (by simp)
    rw [hcard, hcard, OMA.P556R1H2.pairs_left] at h
    push_cast at h
    rw [hW, hW] at h
    have hpos : (0 : ℝ) ≤ ((univ.filter fun v => f v = 0).card : ℝ) *
        (univ.filter fun v => f v = 1).card := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmono hpos]
  have dU (k : Fin 3) (j : Fin 4) (hk : (k, ({0, 1} : Finset (Fin 4)), ({j} : Finset (Fin 4))) ∈
      ([(0, {0}, {1}), (1, {0, 1}, {2}), (2, {0, 1}, {3})] :
        List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))) :
      (1 - 1 / 1000000000 : ℝ) * ((univ.filter fun v => f v = j).card : ℝ) *
        ((univ.filter fun v => f v = 0) ∪ (univ.filter fun v => f v = 1)).card ≤
      ∑ x ∈ univ.filter (fun v => f v = j),
        ((((univ.filter fun v => f v = 0) ∪ (univ.filter fun v => f v = 1)).filter
          ((c k).Adj x)).card : ℝ) := by
    have h := hdens k {0, 1} {j} hk
    rw [hcard, hcard, OMA.P556R1H2.pairs_right] at h
    push_cast at h
    rw [hU, hW] at h
    have hpos : (0 : ℝ) ≤ ((univ.filter fun v => f v = j).card : ℝ) *
        ((univ.filter fun v => f v = 0) ∪ (univ.filter fun v => f v = 1)).card := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hmono hpos]
  obtain ⟨i, hi⟩ := key ⟨size, d0, dU 1 2 (by simp), dU 2 3 (by simp)⟩
  exact ⟨i, by rwa [show 2 * m = m + m by ring] at hi⟩
