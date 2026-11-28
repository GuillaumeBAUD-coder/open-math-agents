import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1
import Mathlib

-- Step H2 of reduction Erdos875.erdos_875.variants.deshouillers_freiman.R1.H2.R1.H1.R1 (Erdos Problem 875): the number of sums of r distinct elements.
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Claim: a set B of naturals has at least r (|B| - r) + 1 sums of r distinct elements.
-- Proof: the lemma card_rSums_ge of the merged root reduction file, copied below (induction on the largest element).

namespace OMA.P_Erdos875_DF_RS

open Finset

-- The lemma below is copied from the merged reduction file
-- reductions/Erdos875.erdos_875.variants.deshouillers_freiman.R1.lean (lemma card_rSums_ge there).
lemma card_rSums_ge (A : Finset ℕ) :
    ∀ r ≤ A.card, r * (A.card - r) + 1 ≤ ((A.powersetCard r).image (fun T => ∑ x ∈ T, x)).card := by
  induction A using Finset.induction_on_max with
  | empty =>
    intro r hr
    have hr0 : r = 0 := Nat.le_zero.mp hr
    subst hr0
    simp
  | insert a A hmax ih =>
    intro r hr
    have ha : a ∉ A := fun h => (hmax a h).false
    have hcard : (insert a A).card = A.card + 1 := Finset.card_insert_of_notMem ha
    rw [hcard] at hr ⊢
    by_cases hr0 : r = 0
    · subst hr0; simp
    by_cases hrmax : r = A.card + 1
    · subst hrmax
      have hne : ((insert a A).powersetCard (A.card + 1)).Nonempty :=
        Finset.powersetCard_nonempty.mpr (by rw [hcard])
      have hpos := Finset.card_pos.mpr (hne.image (fun T => ∑ x ∈ T, x))
      simp only [Nat.sub_self, Nat.mul_zero, zero_add]
      exact hpos
    have hrA : r ≤ A.card := by omega
    set S := ((insert a A).powersetCard r).image (fun T => ∑ x ∈ T, x)
    set S0 := (A.powersetCard r).image (fun T => ∑ x ∈ T, x)
    have hS0_sub : S0 ⊆ S := by
      intro s hs
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hs
      rw [Finset.mem_powersetCard] at hT
      exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hT.1.trans (Finset.subset_insert a A), hT.2⟩, rfl⟩
    -- Build `r` elements of `S` strictly larger than `max S0` by taking a max-sum `r`-subset of `A`
    -- and replacing one of its elements by `a`.
    have hS0_ne : S0.Nonempty := (Finset.powersetCard_nonempty.mpr hrA).image _
    set m0 := S0.max' hS0_ne
    obtain ⟨T0, hT0_mem, hT0_sum⟩ := Finset.mem_image.mp (Finset.max'_mem S0 hS0_ne)
    change ∑ x ∈ T0, x = m0 at hT0_sum
    rw [Finset.mem_powersetCard] at hT0_mem
    let E := T0.image (fun b => a + (m0 - b))
    have hE_card : E.card = r := by
      rw [Finset.card_image_of_injOn]
      · exact hT0_mem.2
      · intro x hx y hy hxy
        dsimp only at hxy
        have hbx : x ≤ m0 := by
          rw [← hT0_sum]
          exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hx
        have hby : y ≤ m0 := by
          rw [← hT0_sum]
          exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hy
        omega
    have hE_sub : E ⊆ S := by
      intro s hs
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
      have hba : a ∉ T0.erase b := fun h => ha (hT0_mem.1 (Finset.mem_of_mem_erase h))
      refine Finset.mem_image.mpr ⟨insert a (T0.erase b), Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hT0_mem.1 (Finset.mem_of_mem_erase hz'))
      · rw [Finset.card_insert_of_notMem hba, Finset.card_erase_of_mem hb, hT0_mem.2]
        omega
      · rw [Finset.sum_insert hba]
        have hsum := Finset.add_sum_erase T0 (fun x => x) hb
        omega
    have hdisj : Disjoint S0 E := by
      refine Finset.disjoint_left.mpr fun s hs0 hsE => ?_
      have hle : s ≤ m0 := Finset.le_max' S0 s hs0
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hsE
      have hbA : b ∈ A := hT0_mem.1 hb
      have hlt : b < a := hmax b hbA
      have hbm : b ≤ m0 := by
        rw [← hT0_sum]
        exact Finset.single_le_sum (f := fun z => z) (fun _ _ => Nat.zero_le _) hb
      omega
    have hstep : S0.card + E.card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hS0_sub hE_sub)
    have hih : r * (A.card - r) + 1 ≤ S0.card := ih r hrA
    rw [hE_card] at hstep
    have hmul : r * (A.card + 1 - r) = r * (A.card - r) + r := by
      have : A.card + 1 - r = (A.card - r) + 1 := by omega
      rw [this, Nat.mul_add, Nat.mul_one]
    omega

end OMA.P_Erdos875_DF_RS

theorem OMA.solution : OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H2_R1_H1_R1.H2 :=
  fun B r hr => OMA.P_Erdos875_DF_RS.card_rSums_ge B r hr
