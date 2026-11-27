import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2
import Mathlib

/-!
A coloring with the minimum number of colors separates disjoint blocks.
Count supersets of a fixed set in two colors, then sum these counts modulo two
over the subsets of one block.
-/

open Finset

namespace OMA.JohnsonDisjoint

variable {α : Type*} [DecidableEq α] [Fintype α] {w : ℕ}

omit [Fintype α] in
private theorem insert_intersection {S : Finset α} {x y : α} (hxy : x ≠ y) :
    insert x S ∩ insert y S = S := by
  ext z
  simp only [mem_inter, mem_insert]
  grind

private theorem unique_extension (hα : Fintype.card α = 2*w+1)
    (c : Finset α → Fin (w+2))
    (hproper : ∀ A B : Finset α, A.card = w → B.card = w →
      (A ∩ B).card = w-1 → c A ≠ c B)
    {S : Finset α} (hS : S.card+1 = w) (i : Fin (w+2)) :
    ∃! x : α, x ∉ S ∧ c (insert x S) = i := by
  classical
  let f : (Sᶜ : Finset α) → Fin (w+2) := fun x => c (insert x.val S)
  have hInjective : Function.Injective f := by
    intro x y h
    by_contra hne
    have hx := mem_compl.mp x.property
    have hy := mem_compl.mp y.property
    apply hproper (insert x.val S) (insert y.val S)
      ((card_insert_of_notMem hx).trans hS) ((card_insert_of_notMem hy).trans hS) _ h
    rw [insert_intersection (fun he => hne (Subtype.ext he))]
    omega
  have hcard : Fintype.card (↥(Sᶜ : Finset α)) = Fintype.card (Fin (w+2)) := by
    rw [Fintype.card_coe, card_compl, Fintype.card_fin, hα]
    omega
  obtain ⟨x,hx⟩ := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hInjective,hcard⟩ |>.2 i
  refine ⟨x.val, ⟨mem_compl.mp x.property,hx⟩, fun y hy => ?_⟩
  exact congrArg Subtype.val (hInjective (a₁ := ⟨y,mem_compl.mpr hy.1⟩) (hy.2.trans hx.symm))

/-- Deletion counts the same flags in each color. -/
private theorem equal_small_counts (c : Finset α → Fin (w+2))
    (hExt : ∀ S : Finset α, S.card+1 = w → ∀ i,
      ∃! x : α, x ∉ S ∧ c (insert x S) = i)
    (U : Finset α) (hU : U.card < w) (i j : Fin (w+2)) :
    (((univ : Finset α).powersetCard w).filter (fun V => c V = i ∧ U ⊆ V)).card =
    (((univ : Finset α).powersetCard w).filter (fun V => c V = j ∧ U ⊆ V)).card := by
  classical
  let W (γ : Fin (w+2)) := ((univ : Finset α).powersetCard w).filter
    (fun V => c V = γ ∧ U ⊆ V)
  let T := ((univ : Finset α).powersetCard (w-1)).filter (fun S => U ⊆ S)
  let F (γ : Fin (w+2)) := (W γ).sigma (fun V => V \ U)
  have hFlags (γ : Fin (w+2)) : (F γ).card = T.card := by
    apply card_bij (fun q _ => q.1.erase q.2)
    · rintro ⟨V,x⟩ h
      obtain ⟨hV,hx⟩ := mem_sigma.mp h
      obtain ⟨hV,_,hUV⟩ := mem_filter.mp hV
      obtain ⟨hxV,hxU⟩ := mem_sdiff.mp hx
      exact mem_filter.mpr ⟨mem_powersetCard.mpr
        ⟨subset_univ _, by rw [card_erase_of_mem hxV,(mem_powersetCard.mp hV).2]⟩,
        fun y hy => mem_erase.mpr ⟨fun he => hxU (he ▸ hy),hUV hy⟩⟩
    · rintro ⟨V,x⟩ h ⟨V',x'⟩ h' he
      obtain ⟨hV,hx⟩ := mem_sigma.mp h
      obtain ⟨hV',hx'⟩ := mem_sigma.mp h'
      obtain ⟨hV,hc,_⟩ := mem_filter.mp hV
      obtain ⟨_,hc',_⟩ := mem_filter.mp hV'
      have hxV := (mem_sdiff.mp hx).1
      have hxV' := (mem_sdiff.mp hx').1
      have hS : (V.erase x).card+1 = w := by
        rw [card_erase_of_mem hxV,(mem_powersetCard.mp hV).2]
        omega
      obtain ⟨y,_,hy⟩ := hExt (V.erase x) hS γ
      have hxx' := (hy x ⟨notMem_erase _ _, by simpa [insert_erase hxV] using hc⟩).trans
        (hy x' ⟨he.symm ▸ notMem_erase _ _, by rw [he, insert_erase hxV']; exact hc'⟩).symm
      subst x'
      have hVV' := congrArg (insert x) he
      rw [insert_erase hxV,insert_erase hxV'] at hVV'
      change V = V' at hVV'
      subst V'
      rfl
    · intro S hS
      obtain ⟨hS,hUS⟩ := mem_filter.mp hS
      have hS' : S.card+1 = w := by
        have := (mem_powersetCard.mp hS).2
        omega
      obtain ⟨x,⟨hx,hc⟩,_⟩ := hExt S hS' γ
      refine ⟨⟨insert x S,x⟩,mem_sigma.mpr ⟨?_,?_⟩,erase_insert hx⟩
      · exact mem_filter.mpr ⟨mem_powersetCard.mpr
          ⟨subset_univ _,(card_insert_of_notMem hx).trans hS'⟩,hc,hUS.trans (subset_insert _ _)⟩
      · exact mem_sdiff.mpr ⟨mem_insert_self _ _, fun hu => hx (hUS hu)⟩
  have hFormula (γ : Fin (w+2)) : (F γ).card = (W γ).card * (w-U.card) := by
    rw [card_sigma]
    calc
      ∑ V ∈ W γ, (V \ U).card = ∑ _V ∈ W γ, (w-U.card) := by
        apply sum_congr rfl
        intro V hV
        obtain ⟨hV,_,hUV⟩ := mem_filter.mp hV
        rw [card_sdiff_of_subset hUV,(mem_powersetCard.mp hV).2]
      _ = _ := by simp
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < w-U.card)
  rw [← hFormula,← hFormula,hFlags,hFlags]

omit [Fintype α] in
/-- A block contributes one subset for each subset of its intersection with A.
Only disjoint blocks contribute an odd number. -/
private theorem count_disjoint_parity (A : Finset α) (W : Finset (Finset α)) :
    (∑ U ∈ A.powerset, (((W.filter (fun V => U ⊆ V)).card : ℕ) : ZMod 2)) =
      ((W.filter (Disjoint A)).card : ZMod 2) := by
  classical
  simp only [card_eq_sum_ones,Nat.cast_sum,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro V _
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← sum_filter]
  have hfilter : A.powerset.filter (fun U => U ⊆ V) = (A ∩ V).powerset := by
    ext U
    simp only [mem_filter,mem_powerset,subset_inter_iff]
  rw [hfilter]
  have hsum : (∑ _U ∈ (A∩V).powerset, (1 : ZMod 2)) =
      ((2 ^ (A∩V).card : ℕ) : ZMod 2) := by
    rw [sum_const, nsmul_eq_mul, mul_one, card_powerset]
  rw [hsum,Nat.cast_pow]
  by_cases hd : Disjoint A V
  · simp [hd,disjoint_iff_inter_eq_empty.mp hd]
  · have hpos : 0 < (A ∩ V).card := card_pos.mpr
      (nonempty_iff_ne_empty.mpr fun he => hd (disjoint_iff_inter_eq_empty.mpr he))
    rw [show ((2 : ℕ) : ZMod 2) = 0 by decide,zero_pow hpos.ne',if_neg hd]


theorem disjoint_colors (hα : Fintype.card α = 2*w+1) (hw : 0 < w)
    (c : Finset α → Fin (w+2))
    (hproper : ∀ A B : Finset α, A.card = w → B.card = w →
      (A ∩ B).card = w-1 → c A ≠ c B)
    (A B : Finset α) (hA : A.card = w) (hB : B.card = w)
    (hAB : Disjoint A B) : c A ≠ c B := by
  classical
  intro hSame
  have hAc : Aᶜ.card = w+1 := by rw [card_compl,hα,hA]; omega
  have hBA : B ⊆ Aᶜ := fun x hx => mem_compl.mpr fun h => disjoint_left.mp hAB h hx
  have hextra : ¬ Aᶜ ⊆ B := by
    intro h
    have := card_le_card h
    omega
  obtain ⟨y,hyA,hyB⟩ := not_subset.mp hextra
  obtain ⟨x,hx⟩ := card_pos.mp (hB.symm ▸ hw)
  let C := insert y (B.erase x)
  have hC : C.card = w := by
    rw [card_insert_of_notMem (fun h => hyB (erase_subset _ _ h)),card_erase_of_mem hx,hB]
    omega
  have hCA : C ⊆ Aᶜ := insert_subset hyA ((erase_subset _ _).trans hBA)
  have hAC : Disjoint A C :=
    disjoint_left.mpr fun z hz hzc => (mem_compl.mp (hCA hzc)) hz
  have hUnique {V W : Finset α} (hV : V.card = w) (hW : W.card = w)
      (hAV : Disjoint A V) (hAW : Disjoint A W) (hVW : V ≠ W) : c V ≠ c W := by
    have hUnion : V ∪ W ⊆ Aᶜ := by
      intro z hz
      apply mem_compl.mpr
      intro ha
      exact (mem_union.mp hz).elim (disjoint_left.mp hAV ha) (disjoint_left.mp hAW ha)
    have hle := card_le_card hUnion
    have heq := card_union_add_card_inter V W
    have hlt : (V ∩ W).card < V.card := by
      apply card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left,fun h => hVW
        (eq_of_subset_of_card_le (h ▸ inter_subset_right) (hW.trans hV.symm).le)⟩
    exact hproper V W hV hW (by omega)
  have hBC : B ≠ C := fun h => hyB (h ▸ mem_insert_self y (B.erase x))
  have hDiff : c A ≠ c C := hSame ▸ hUnique hB hC hAB hAC hBC
  let W (i : Fin (w+2)) :=
    ((univ : Finset α).powersetCard w).filter (fun V => c V = i)
  let n (i : Fin (w+2)) (U : Finset α) := ((W i).filter (fun V => U ⊆ V)).card
  have hCounts (i j : Fin (w+2)) (U : Finset α) (hU : U ⊂ A) : n i U = n j U := by
    simpa [n,W,filter_filter,and_comm] using
      equal_small_counts c (fun S hS i => unique_extension hα c hproper hS i) U
        (hA ▸ card_lt_card hU) i j
  have hTop (i : Fin (w+2)) :
      (W i).filter (fun V => A ⊆ V) = if c A = i then {A} else ∅ := by
    ext V
    simp only [W,mem_filter,mem_powersetCard,subset_univ,true_and]
    by_cases h : c A = i <;> simp only [h,if_true,if_false,mem_singleton,notMem_empty]
    · constructor
      · rintro ⟨⟨hV,_⟩,hAV⟩
        exact (eq_of_subset_of_card_le hAV (hV.trans hA.symm).le).symm
      · rintro rfl
        exact ⟨⟨hA,h⟩,Subset.rfl⟩
    · apply iff_false_intro
      rintro ⟨⟨hV,hc⟩,hAV⟩
      have he := eq_of_subset_of_card_le hAV (hV.trans hA.symm).le
      exact h (he ▸ hc)
  have hSingleton {V : Finset α} (hV : V.card = w) (hAV : Disjoint A V) :
      (W (c V)).filter (Disjoint A) = {V} := by
    ext Z
    simp only [W,mem_filter,mem_powersetCard,subset_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨⟨hZ,hColor⟩,hAZ⟩
      by_contra hn
      exact (hUnique hZ hV hAZ hAV hn) hColor
    · rintro rfl
      exact ⟨⟨hV,rfl⟩,hAV⟩
  have hSumB := count_disjoint_parity A (W (c A))
  have hSumC := count_disjoint_parity A (W (c C))
  rw [hSame,hSingleton hB hAB] at hSumB
  rw [hSingleton hC hAC] at hSumC
  have hEqual : (∑ U ∈ A.powerset, (n (c A) U : ZMod 2)) =
      ∑ U ∈ A.powerset, (n (c C) U : ZMod 2) := by
    simpa [n,hSame] using hSumB.trans hSumC.symm
  have hRest : (∑ U ∈ A.ssubsets, (n (c A) U : ZMod 2)) =
      ∑ U ∈ A.ssubsets, (n (c C) U : ZMod 2) :=
    sum_congr rfl (fun U hU => congrArg (fun v : ℕ => (v : ZMod 2))
      (hCounts _ _ U (mem_ssubsets.mp hU)))
  have hAs : A ∈ A.powerset := mem_powerset.mpr Subset.rfl
  rw [← sum_erase_add _ _ hAs, ← sum_erase_add _ _ hAs] at hEqual
  change (∑ U ∈ A.ssubsets, (n (c A) U : ZMod 2)) + (n (c A) A : ZMod 2) =
    (∑ U ∈ A.ssubsets, (n (c C) U : ZMod 2)) + (n (c C) A : ZMod 2) at hEqual
  have hOne : n (c A) A = 1 := by simp [n,hTop]
  have hZero : n (c C) A = 0 := by simp [n,hTop,hDiff]
  rw [hRest,hOne,hZero] at hEqual
  have h10 := add_left_cancel hEqual
  exact (one_ne_zero (α := ZMod 2)) (by simpa only [Nat.cast_one,Nat.cast_zero] using h10)

end OMA.JohnsonDisjoint

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H3 := by
  intro p _ hp c hproper A B hA hB hAB h
  let w := p - 2
  have hpw : p = w+2 := by omega
  let d (V : Finset (Fin (2*p-3))) := Fin.cast hpw (c V)
  have hSize : Fintype.card (Fin (2*p-3)) = 2*w+1 := by
    simp only [Fintype.card_fin]
    omega
  have hProper : ∀ V W : Finset (Fin (2*p-3)), V.card = w → W.card = w →
      (V ∩ W).card = w-1 → d V ≠ d W := by
    intro V W hv hw hi he
    have hvv := congrArg (fun x : Fin (w+2) => x.val) he
    exact hproper V W hv hw (by omega) (Fin.ext hvv)
  exact OMA.JohnsonDisjoint.disjoint_colors hSize (by omega) d hProper A B hA hB hAB
    (congrArg (Fin.cast hpw) h)
