import FormalConjectures.ErdosProblems.«835»
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

open Finset
namespace OMA.R_Erdos835_erdos_835_R1

/- The fixed boundary comes from fifteen pairwise edge-disjoint starters
on the nonzero residues modulo 17. The rows encode edges (a,b) by 17*a+b.
X is the fixed set of 15 remaining points. D is the color-zero boundary,
including complementary blocks. Translating the cyclic coordinates by d
prescribes color d. This gives a constructive sufficient condition at
k = 16, the smallest parameter not excluded in the literature. -/

-- The prescribed color-zero boundary contains no adjacent distinct blocks.
def H1 : Prop :=
  let M : List (List Nat) := [[33,49,65,81,97,113,129,145],
    [19,56,77,114,133,152,183,202],
    [26,40,61,75,96,149,218,271],
    [20,39,80,115,127,168,184,203],
    [23,42,58,79,98,163,219,254],
    [21,47,59,100,116,128,181,220],
    [22,46,62,83,109,146,167,237],
    [27,50,66,82,91,132,148,164],
    [32,48,64,78,94,110,135,199],
    [25,41,55,101,117,166,182,201],
    [29,45,57,76,92,169,185,235],
    [24,37,84,99,112,151,165,200],
    [30,43,63,74,93,130,186,253],
    [28,38,67,95,111,134,150,217],
    [31,44,60,73,118,131,147,236]]
  let X := (Finset.univ : Finset (Fin 32)).filter (fun x => 17 ≤ x.val)
  let L := (insert 0 X) :: (M.zipIdx.flatMap (fun (r,j) =>
    r.map fun t => insert (Fin.ofNat 32 (t/17))
      (insert (Fin.ofNat 32 (t%17)) (X.erase (Fin.ofNat 32 (17+j))))))
  let D := L ++ L.map (fun B => Finset.univ \ B)
  ∀ A ∈ D, ∀ B ∈ D, A ≠ B → (A ∩ B).card ≠ 15

-- Complete the remaining blocks, requiring adjacency constraints on all
-- pairs except those within a prescribed class (covered by H1).
def H2 : Prop :=
  let M : List (List Nat) := [[33,49,65,81,97,113,129,145],
    [19,56,77,114,133,152,183,202],
    [26,40,61,75,96,149,218,271],
    [20,39,80,115,127,168,184,203],
    [23,42,58,79,98,163,219,254],
    [21,47,59,100,116,128,181,220],
    [22,46,62,83,109,146,167,237],
    [27,50,66,82,91,132,148,164],
    [32,48,64,78,94,110,135,199],
    [25,41,55,101,117,166,182,201],
    [29,45,57,76,92,169,185,235],
    [24,37,84,99,112,151,165,200],
    [30,43,63,74,93,130,186,253],
    [28,38,67,95,111,134,150,217],
    [31,44,60,73,118,131,147,236]]
  let X := (Finset.univ : Finset (Fin 32)).filter (fun x => 17 ≤ x.val)
  let L := (insert 0 X) :: (M.zipIdx.flatMap (fun (r,j) =>
    r.map fun t => insert (Fin.ofNat 32 (t/17))
      (insert (Fin.ofNat 32 (t%17)) (X.erase (Fin.ofNat 32 (17+j))))))
  let D := L ++ L.map (fun B => Finset.univ \ B)
  let shift := fun (d : Fin 17) (x : Fin 32) =>
    if x.val < 17 then Fin.ofNat 32 ((x.val+d.val)%17) else x
  ∃ c : Finset (Fin 32) → Fin 17,
    (∀ d : Fin 17, ∀ A ∈ D, c (A.image (shift d)) = d) ∧
    (∀ A B : Finset (Fin 32), A.card = 16 → B.card = 16 →
      A ≠ B → (A ∩ B).card = 15 → c A = c B →
      ∃ U ∈ D, ∃ V ∈ D,
        A = U.image (shift (c A)) ∧ B = V.image (shift (c A)))

private theorem shift_inj (d : Fin 17) : Function.Injective
    (fun (x : Fin 32) => if x.val < 17 then Fin.ofNat 32 ((x.val+d.val)%17) else x) := by
  intro x y h
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  have hd := d.isLt
  change (if x.val < 17 then Fin.ofNat 32 ((x.val+d.val)%17) else x) =
    (if y.val < 17 then Fin.ofNat 32 ((y.val+d.val)%17) else y) at h
  split at h <;> split at h <;> have hh := congrArg Fin.val h <;>
    (try simp at hh) <;> omega

theorem main : H1 → H2 → type_of% @Erdos835.erdos_835 := by
  classical
  intro h1 h2
  unfold H1 at h1
  unfold H2 at h2
  dsimp only at h1 h2
  obtain ⟨c,hboundary,hc⟩ := h2
  have hi (A B : Finset (Fin 32)) (hA : A.card = 16) (hB : B.card = 16)
      (hne : A ≠ B) (hab : (A ∩ B).card = 15) : c A ≠ c B := by
    intro h
    obtain ⟨U,hU,V,hV,hu,hv⟩ := hc A B hA hB hne hab h
    have hne' : U ≠ V := fun he => hne (hu.trans (by rw [he, ← hv]))
    have hs := shift_inj (c A)
    apply h1 U hU V hV hne'
    rw [hu,hv, ←Finset.image_inter U V hs, Finset.card_image_of_injective _ hs] at hab
    exact hab
  refine ⟨16, by decide, ?_⟩
  unfold Erdos835.Property
  refine ⟨fun s => c s.val, ?_⟩
  intro A hA
  change A.card = 17 at hA
  have hI : Set.InjOn c ↑(A.powersetCard 16) := by
    intro B hB D hD h
    by_contra hn
    obtain ⟨hBA,hBk⟩ := Finset.mem_powersetCard.mp hB
    obtain ⟨hDA,hDk⟩ := Finset.mem_powersetCard.mp hD
    have hU : (B ∪ D).card ≤ 17 := by
      rw [← hA]
      exact Finset.card_le_card (Finset.union_subset hBA hDA)
    have hC : (B ∩ D).card < 16 := by
      by_contra! hh
      have h₁ := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁:=B) (s₂:=D)) (by omega)
      have h₂ := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right (s₁:=B) (s₂:=D)) (by omega)
      exact hn (h₁.symm.trans h₂)
    have hsum := Finset.card_union_add_card_inter B D
    exact hi B D hBk hDk hn (by omega) h
  have hcard : ((A.powersetCard 16).image c).card = 17 := by
    rw [Finset.card_image_of_injOn hI, Finset.card_powersetCard, hA]
    decide
  have hf : (A.powersetCard 16).image c = univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hcard]
  apply Finset.eq_univ_of_forall
  intro a
  have hm : a ∈ (A.powersetCard 16).image c := by rw [hf]; simp
  obtain ⟨B,hB,hcB⟩ := Finset.mem_image.mp hm
  obtain ⟨hBA,hBk⟩ := Finset.mem_powersetCard.mp hB
  refine Finset.mem_image.mpr ⟨⟨B,hBk⟩, ?_, hcB⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.ssubset_iff_subset_ne.mpr
  exact ⟨hBA, fun e => by rw [e,hA] at hBk; omega⟩

end OMA.R_Erdos835_erdos_835_R1
