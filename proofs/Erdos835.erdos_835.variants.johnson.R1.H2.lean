import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1

/-!
# Proof of Step H2 for `Erdos835.erdos_835.variants.johnson.R1`

Formalizes Mendelsohn's intersecting-block lemma (`https://doi.org/10.4153/CJM-1970-117-0`)
via fraction-free double counting and inclusion-exclusion over `ℤ`.
-/

open Finset SimpleGraph

section Mendelsohn

lemma double_count_step {α : Type*} [DecidableEq α]
    (U : Finset α) (r : ℕ) (ℱ : Finset (Finset α))
    (hℱ : ℱ ⊆ U.powersetCard r) (I : Finset α) :
    (r - #I) * #(ℱ.filter (I ⊆ ·)) =
      ∑ z ∈ U \ I, #(ℱ.filter (insert z I ⊆ ·)) := by
  have hrew : ∀ z ∈ U \ I,
      #(ℱ.filter (insert z I ⊆ ·)) = #((ℱ.filter (I ⊆ ·)).filter (z ∈ ·)) := by
    intro z _
    congr 1
    ext A
    simp only [mem_filter, insert_subset_iff]
    tauto
  rw [sum_congr rfl hrew]
  simp only [filter_filter, card_filter]
  rw [sum_comm]
  have hinner : ∀ x ∈ ℱ,
      (∑ y ∈ U \ I, if I ⊆ x ∧ y ∈ x then 1 else 0) =
        if I ⊆ x then r - #I else 0 := by
    intro A hA
    have hAU : A ⊆ U := (mem_powersetCard.mp (hℱ hA)).1
    have hAr : #A = r := (mem_powersetCard.mp (hℱ hA)).2
    by_cases hIA : I ⊆ A
    · simp only [hIA, true_and, if_true]
      rw [← card_filter]
      have hset : (U \ I).filter (· ∈ A) = A \ I := by
        ext z
        simp only [mem_filter, mem_sdiff]
        exact ⟨fun ⟨⟨_, hzI⟩, hzA⟩ => ⟨hzA, hzI⟩,
               fun ⟨hzA, hzI⟩ => ⟨⟨hAU hzA, hzI⟩, hzA⟩⟩
      rw [hset, card_sdiff_of_subset hIA, hAr]
    · simp [hIA]
  rw [sum_congr rfl hinner]
  have hmul : (∑ x ∈ ℱ, if I ⊆ x then r - #I else 0) =
      (∑ x ∈ ℱ, if I ⊆ x then 1 else 0) * (r - #I) := by
    rw [sum_mul]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [hmul, mul_comm]

lemma card_powersetCard_filter_subset {α : Type*} [DecidableEq α]
    (U I : Finset α) (r : ℕ) (hIU : I ⊆ U) (hIr : #I ≤ r) :
    #((U.powersetCard r).filter (I ⊆ ·)) = (#U - #I).choose (r - #I) := by
  have himg : (U.powersetCard r).filter (I ⊆ ·) =
      ((U \ I).powersetCard (r - #I)).image (I ∪ ·) := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hAU, hAr⟩, hIA⟩
      refine ⟨A \ I, ⟨?_, ?_⟩, union_sdiff_of_subset hIA⟩
      · exact sdiff_subset_sdiff hAU Subset.rfl
      · rw [card_sdiff_of_subset hIA, hAr]
    · rintro ⟨C, ⟨hCU, hCr⟩, rfl⟩
      have hdisj : Disjoint I C := disjoint_of_subset_right hCU disjoint_sdiff_self_right
      refine ⟨⟨union_subset hIU (hCU.trans sdiff_subset), ?_⟩, subset_union_left⟩
      rw [card_union_of_disjoint hdisj, hCr]
      omega
  rw [himg, card_image_of_injOn, card_powersetCard, card_sdiff_of_subset hIU]
  intro C₁ hC₁ C₂ hC₂ hEq
  dsimp only at hEq
  have hd₁ : Disjoint I C₁ :=
    disjoint_of_subset_right (mem_powersetCard.mp hC₁).1 disjoint_sdiff_self_right
  have hd₂ : Disjoint I C₂ :=
    disjoint_of_subset_right (mem_powersetCard.mp hC₂).1 disjoint_sdiff_self_right
  have h1 := union_sdiff_cancel_left hd₁
  have h2 := union_sdiff_cancel_left hd₂
  rw [← h1, ← h2, hEq]

lemma alternating_sum_powerset {α : Type*} [DecidableEq α] (S : Finset α) :
    (∑ I ∈ S.powerset, (-1 : ℤ) ^ #I) = if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hne : insert a s ≠ ∅ := insert_ne_empty a s
    rw [if_neg hne, powerset_insert, sum_union]
    · rw [sum_image]
      · have hneg : ∀ I ∈ s.powerset,
            (-1 : ℤ) ^ #(insert a I) = -((-1 : ℤ) ^ #I) := by
          intro I hI
          have haI : a ∉ I := fun h => ha (mem_powerset.mp hI h)
          rw [card_insert_of_notMem haI, pow_succ]
          ring
        rw [sum_congr rfl hneg, sum_neg_distrib, add_neg_cancel]
      · intro I₁ hI₁ I₂ hI₂ hEq
        have ha₁ : a ∉ I₁ := fun h => ha (mem_powerset.mp hI₁ h)
        have ha₂ : a ∉ I₂ := fun h => ha (mem_powerset.mp hI₂ h)
        have h1 := erase_insert ha₁
        have h2 := erase_insert ha₂
        rw [← h1, ← h2, hEq]
    · rw [Finset.disjoint_left]
      intro I hI₁ hI₂
      rcases mem_image.mp hI₂ with ⟨J, _, rfl⟩
      exact ha (mem_powerset.mp hI₁ (mem_insert_self a J))

lemma inclusion_exclusion_disjoint {α : Type*} [DecidableEq α]
    (ℱ : Finset (Finset α)) (B₀ : Finset α) :
    (∑ I ∈ B₀.powerset, (-1 : ℤ) ^ #I * (#(ℱ.filter (I ⊆ ·)) : ℤ)) =
      (#(ℱ.filter (Disjoint B₀ ·)) : ℤ) := by
  have hterm : ∀ I : Finset α,
      (-1 : ℤ) ^ #I * (#(ℱ.filter (I ⊆ ·)) : ℤ) =
        ∑ A ∈ ℱ, if I ⊆ A then (-1 : ℤ) ^ #I else 0 := by
    intro I
    rw [card_filter, Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun A _ => ?_
    split_ifs <;> simp
  simp_rw [hterm]
  rw [sum_comm]
  have hinner : ∀ A ∈ ℱ,
      (∑ I ∈ B₀.powerset, if I ⊆ A then (-1 : ℤ) ^ #I else 0) =
        if Disjoint B₀ A then 1 else 0 := by
    intro A _
    rw [← sum_filter]
    have hpow : B₀.powerset.filter (· ⊆ A) = (B₀ ∩ A).powerset := by
      ext I
      simp only [mem_filter, mem_powerset, subset_inter_iff]
    rw [hpow, alternating_sum_powerset]
    simp only [disjoint_iff_inter_eq_empty]
  rw [sum_congr rfl hinner, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun A _ => ?_
  split_ifs <;> simp

lemma steiner_proportionality
    (k : ℕ) (x : Fin (2 * k)) (hk : 3 ≤ k)
    (c : (J(2 * k, k).induce {v | x ∈ v.val}).Coloring (Fin (k + 1)))
    (γ : Fin (k + 1)) :
    let U : Finset (Fin (2 * k)) := univ.erase x
    let 𝒜 : Finset (Finset (Fin (2 * k))) := U.powersetCard (k - 1)
    let lift : ∀ A ∈ 𝒜, {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val} :=
      fun A hA => ⟨⟨insert x A, by
        have hx : x ∉ A := fun hxA => (mem_erase.mp ((mem_powersetCard.mp hA).1 hxA)).1 rfl
        rw [card_insert_of_notMem hx, (mem_powersetCard.mp hA).2]
        omega⟩, mem_insert_self x A⟩
    let 𝒟 : Finset (Finset (Fin (2 * k))) :=
      𝒜.filter (fun A => if hA : A ∈ 𝒜 then c (lift A hA) = γ else False)
    ∀ I, I ⊆ U → #I ≤ k - 2 →
      (k + 1) * #(𝒟.filter (I ⊆ ·)) = #(𝒜.filter (I ⊆ ·)) := by
  classical
  intro U 𝒜 lift 𝒟
  have hUcard : #U = 2 * k - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  have h𝒟sub : 𝒟 ⊆ 𝒜 := filter_subset _ _
  have hbase : ∀ T, T ⊆ U → #T = k - 2 → #(𝒟.filter (T ⊆ ·)) = 1 := by
    intro T hTU hTcard
    let S : Finset (Fin (2 * k)) := U \ T
    have hScard : #S = k + 1 := by
      rw [card_sdiff_of_subset hTU, hUcard, hTcard]
      omega
    have hxT : x ∉ T := fun hx => (mem_erase.mp (hTU hx)).1 rfl
    have memA : ∀ y : S, insert y.1 T ∈ 𝒜 := by
      intro y
      have hyU : y.1 ∈ U := (mem_sdiff.mp y.2).1
      have hyT : y.1 ∉ T := (mem_sdiff.mp y.2).2
      rw [mem_powersetCard]
      refine ⟨insert_subset_iff.mpr ⟨hyU, hTU⟩, ?_⟩
      rw [card_insert_of_notMem hyT, hTcard]
      omega
    let φ : S → Fin (k + 1) := fun y => c (lift (insert y.1 T) (memA y))
    have hφ_inj : Function.Injective φ := by
      intro y₁ y₂ hEq
      by_contra hne
      have hval_ne : y₁.1 ≠ y₂.1 := fun hv => hne (Subtype.ext hv)
      have hadj : #(insert x (insert y₁.1 T) ∩ insert x (insert y₂.1 T)) + 1 = k := by
        have hinter : insert x (insert y₁.1 T) ∩ insert x (insert y₂.1 T) = insert x T := by
          ext z
          simp only [mem_inter, mem_insert]
          by_cases hzx : z = x
          · simp [hzx]
          · by_cases hzT : z ∈ T
            · simp [hzT]
            · simp only [hzx, hzT, or_false, false_or, iff_false, not_and]
              exact fun h1 h2 => hval_ne (h1.symm.trans h2)
        rw [hinter, card_insert_of_notMem hxT, hTcard]
        omega
      exact c.valid (v := lift (insert y₁.1 T) (memA y₁))
        (w := lift (insert y₂.1 T) (memA y₂)) hadj hEq
    have hφ_bij : Function.Bijective φ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hφ_inj, ?_⟩
      rw [Fintype.card_coe, hScard, Fintype.card_fin]
    obtain ⟨y₀, hy₀, hy₀_uniq⟩ := hφ_bij.existsUnique γ
    have hsingleton : 𝒟.filter (T ⊆ ·) = {insert y₀.1 T} := by
      ext A
      simp only [mem_filter, mem_singleton, 𝒟]
      constructor
      · rintro ⟨⟨hA, hcol⟩, hTA⟩
        rw [dif_pos hA] at hcol
        have hdiff_card : #(A \ T) = 1 := by
          rw [card_sdiff_of_subset hTA, (mem_powersetCard.mp hA).2, hTcard]
          omega
        obtain ⟨z, hz⟩ := card_eq_one.mp hdiff_card
        have hz_mem : z ∈ A \ T := by rw [hz]; exact mem_singleton_self z
        have hzS : z ∈ S := mem_sdiff.mpr ⟨(mem_powersetCard.mp hA).1 (mem_sdiff.mp hz_mem).1,
          (mem_sdiff.mp hz_mem).2⟩
        have hAeq : insert z T = A := by
          have hu := sdiff_union_of_subset hTA
          rw [hz, singleton_union] at hu
          exact hu
        have hlift_eq : lift (insert z T) (memA ⟨z, hzS⟩) = lift A hA := by
          apply Subtype.ext
          apply Subtype.ext
          change insert x (insert z T) = insert x A
          rw [hAeq]
        have hφz : φ ⟨z, hzS⟩ = γ := by
          change c (lift (insert z T) (memA ⟨z, hzS⟩)) = γ
          rw [hlift_eq]
          exact hcol
        have hzy₀ : (⟨z, hzS⟩ : S) = y₀ := hy₀_uniq ⟨z, hzS⟩ hφz
        have hzeq : z = y₀.1 := congrArg Subtype.val hzy₀
        rw [← hAeq, hzeq]
      · rintro rfl
        refine ⟨⟨memA y₀, ?_⟩, subset_insert y₀.1 T⟩
        rw [dif_pos (memA y₀)]
        exact hy₀
    rw [hsingleton, card_singleton]
  have hind : ∀ d : ℕ, ∀ I, I ⊆ U → #I ≤ k - 2 → k - 2 - #I = d →
      (k + 1) * #(𝒟.filter (I ⊆ ·)) = #(𝒜.filter (I ⊆ ·)) := by
    intro d
    induction d with
    | zero =>
      intro I hIU hI1 hI2
      have hIcard : #I = k - 2 := by omega
      rw [hbase I hIU hIcard, mul_one,
          card_powersetCard_filter_subset U I (k - 1) hIU (by omega),
          hUcard, hIcard]
      have h1 : 2 * k - 1 - (k - 2) = k + 1 := by omega
      have h2 : k - 1 - (k - 2) = 1 := by omega
      rw [h1, h2, Nat.choose_one_right]
    | succ d ih =>
      intro I hIU hIle hId
      have hstepD := double_count_step U (k - 1) 𝒟 h𝒟sub I
      have hstepA := double_count_step U (k - 1) 𝒜 Subset.rfl I
      have hmul : (k - 1 - #I) * ((k + 1) * #(𝒟.filter (I ⊆ ·))) =
          (k - 1 - #I) * #(𝒜.filter (I ⊆ ·)) := by
        calc
          (k - 1 - #I) * ((k + 1) * #(𝒟.filter (I ⊆ ·)))
              = (k + 1) * ((k - 1 - #I) * #(𝒟.filter (I ⊆ ·))) := by ring
          _ = (k + 1) * ∑ z ∈ U \ I, #(𝒟.filter (insert z I ⊆ ·)) := by rw [hstepD]
          _ = ∑ z ∈ U \ I, (k + 1) * #(𝒟.filter (insert z I ⊆ ·)) := by rw [mul_sum]
          _ = ∑ z ∈ U \ I, #(𝒜.filter (insert z I ⊆ ·)) := by
              refine sum_congr rfl fun z hz => ?_
              have hzU : z ∈ U := (mem_sdiff.mp hz).1
              have hzI : z ∉ I := (mem_sdiff.mp hz).2
              have hinsU : insert z I ⊆ U := insert_subset_iff.mpr ⟨hzU, hIU⟩
              have hinsCard : #(insert z I) = #I + 1 := card_insert_of_notMem hzI
              exact ih (insert z I) hinsU (by omega) (by omega)
          _ = (k - 1 - #I) * #(𝒜.filter (I ⊆ ·)) := hstepA.symm
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  intro I hIU hIle
  exact hind (k - 2 - #I) I hIU hIle rfl

end Mendelsohn

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H2 := by
  classical
  intro k x hk heven c v w hvw hcol
  let γ : Fin (k + 1) := c w
  let U : Finset (Fin (2 * k)) := univ.erase x
  let 𝒜 : Finset (Finset (Fin (2 * k))) := U.powersetCard (k - 1)
  let lift : ∀ A ∈ 𝒜, {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val} :=
    fun A hA => ⟨⟨insert x A, by
      have hx : x ∉ A := fun hxA => (mem_erase.mp ((mem_powersetCard.mp hA).1 hxA)).1 rfl
      rw [card_insert_of_notMem hx, (mem_powersetCard.mp hA).2]
      omega⟩, mem_insert_self x A⟩
  let 𝒟 : Finset (Finset (Fin (2 * k))) :=
    𝒜.filter (fun A => if hA : A ∈ 𝒜 then c (lift A hA) = γ else False)
  have hprop := steiner_proportionality k x hk c γ
  change ∀ I, I ⊆ U → #I ≤ k - 2 →
    (k + 1) * #(𝒟.filter (I ⊆ ·)) = #(𝒜.filter (I ⊆ ·)) at hprop
  let A₀ : Finset (Fin (2 * k)) := v.val.val.erase x
  let B₀ : Finset (Fin (2 * k)) := w.val.val.erase x
  have hmemA : ∀ u : {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val},
      u.val.val.erase x ∈ 𝒜 := by
    intro u
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro z hz
      exact mem_erase.mpr ⟨(mem_erase.mp hz).1, mem_univ z⟩
    · rw [card_erase_of_mem u.property, u.val.property]
  have hlift_erase : ∀ (u : {v : {s : Finset (Fin (2 * k)) // s.card = k} // x ∈ v.val})
      (hu : u.val.val.erase x ∈ 𝒜), lift (u.val.val.erase x) hu = u := by
    intro u hu
    apply Subtype.ext
    apply Subtype.ext
    exact insert_erase u.property
  have hA₀D : A₀ ∈ 𝒟 := by
    simp only [𝒟, mem_filter]
    refine ⟨hmemA v, ?_⟩
    rw [dif_pos (hmemA v), hlift_erase v (hmemA v)]
    exact hcol
  have hB₀A : B₀ ∈ 𝒜 := hmemA w
  have hB₀D : B₀ ∈ 𝒟 := by
    simp only [𝒟, mem_filter]
    refine ⟨hB₀A, ?_⟩
    rw [dif_pos hB₀A, hlift_erase w hB₀A]
  have hdisjAB : Disjoint B₀ A₀ := by
    rw [Finset.disjoint_left]
    intro z hzB hzA
    have hzx : z ≠ x := (mem_erase.mp hzB).1
    have hzw : z ∈ w.val.val := (mem_erase.mp hzB).2
    have hzv : z ∈ v.val.val := (mem_erase.mp hzA).2
    have hzvw : z ∈ v.val.val ∩ w.val.val := mem_inter.mpr ⟨hzv, hzw⟩
    rw [hvw, mem_singleton] at hzvw
    exact hzx hzvw
  have hB₀U : B₀ ⊆ U := (mem_powersetCard.mp hB₀A).1
  have hB₀card : #B₀ = k - 1 := (mem_powersetCard.mp hB₀A).2
  have hUcard : #U = 2 * k - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  have htopD : 𝒟.filter (B₀ ⊆ ·) = {B₀} := by
    ext A
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hAD, hBA⟩
      have hAA : A ∈ 𝒜 := (mem_filter.mp hAD).1
      exact (eq_of_subset_of_card_le hBA (by rw [(mem_powersetCard.mp hAA).2, hB₀card])).symm
    · rintro rfl
      exact ⟨hB₀D, Subset.rfl⟩
  have htopA : 𝒜.filter (B₀ ⊆ ·) = {B₀} := by
    ext A
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hAA, hBA⟩
      exact (eq_of_subset_of_card_le hBA (by rw [(mem_powersetCard.mp hAA).2, hB₀card])).symm
    · rintro rfl
      exact ⟨hB₀A, Subset.rfl⟩
  have hdisjA_card : #(𝒜.filter (Disjoint B₀ ·)) = k := by
    have hset : 𝒜.filter (Disjoint B₀ ·) = (U \ B₀).powersetCard (k - 1) := by
      ext A
      simp only [mem_filter, mem_powersetCard, 𝒜]
      constructor
      · rintro ⟨⟨hAU, hAr⟩, hdisj⟩
        refine ⟨subset_sdiff.mpr ⟨hAU, hdisj.symm⟩, hAr⟩
      · rintro ⟨hAsdiff, hAr⟩
        refine ⟨⟨hAsdiff.trans sdiff_subset, hAr⟩,
          disjoint_of_subset_right hAsdiff disjoint_sdiff_self_right⟩
    rw [hset, card_powersetCard, card_sdiff_of_subset hB₀U, hUcard, hB₀card]
    have hsub : 2 * k - 1 - (k - 1) = k := by omega
    rw [hsub]
    obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
    simp
  have hieD := inclusion_exclusion_disjoint 𝒟 B₀
  have hieA := inclusion_exclusion_disjoint 𝒜 B₀
  have hpow_split : B₀.powerset = insert B₀ B₀.ssubsets := by
    ext I
    simp only [mem_powerset, mem_insert, mem_ssubsets]
    exact subset_iff_ssubset_or_eq.trans or_comm
  have hnotMem_ssub : B₀ ∉ B₀.ssubsets := by simp
  rw [hpow_split, sum_insert hnotMem_ssub, htopD, card_singleton] at hieD
  rw [hpow_split, sum_insert hnotMem_ssub, htopA, card_singleton, hdisjA_card] at hieA
  have hssub_eq :
      (∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * ((k + 1 : ℤ) * (#(𝒟.filter (I ⊆ ·)) : ℤ))) =
        ∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * (#(𝒜.filter (I ⊆ ·)) : ℤ) := by
    refine sum_congr rfl fun I hI => ?_
    have hIB : I ⊂ B₀ := mem_ssubsets.mp hI
    have hIU : I ⊆ U := hIB.subset.trans hB₀U
    have hIlt : #I < #B₀ := card_lt_card hIB
    have hIle : #I ≤ k - 2 := by omega
    have hp := hprop I hIU hIle
    have hpZ : ((k + 1 : ℤ) * (#(𝒟.filter (I ⊆ ·)) : ℤ)) = (#(𝒜.filter (I ⊆ ·)) : ℤ) := by
      exact_mod_cast hp
    rw [hpZ]
  have hodd_pow : (-1 : ℤ) ^ #B₀ = -1 := by
    rcases heven with ⟨m, hm⟩
    have hB₀m : #B₀ = 2 * (m - 1) + 1 := by omega
    rw [hB₀m]
    exact Odd.neg_one_pow ⟨m - 1, rfl⟩
  rw [hodd_pow] at hieD hieA
  have hmulD : (k + 1 : ℤ) * (#(𝒟.filter (Disjoint B₀ ·)) : ℤ) =
      (-1 : ℤ) * (k + 1 : ℤ) +
        ∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * ((k + 1 : ℤ) * (#(𝒟.filter (I ⊆ ·)) : ℤ)) := by
    calc
      (k + 1 : ℤ) * (#(𝒟.filter (Disjoint B₀ ·)) : ℤ)
          = (k + 1 : ℤ) * ((-1 : ℤ) * ((1 : ℕ) : ℤ) +
              ∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * (#(𝒟.filter (I ⊆ ·)) : ℤ)) := by rw [← hieD]
      _ = (-1 : ℤ) * (k + 1 : ℤ) +
            (k + 1 : ℤ) * ∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * (#(𝒟.filter (I ⊆ ·)) : ℤ) := by
          push_cast; ring
      _ = (-1 : ℤ) * (k + 1 : ℤ) +
            ∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * ((k + 1 : ℤ) * (#(𝒟.filter (I ⊆ ·)) : ℤ)) := by
          rw [mul_sum]
          refine congrArg ((-1 : ℤ) * (k + 1 : ℤ) + ·) (sum_congr rfl fun I _ => by ring)
  rw [hssub_eq] at hmulD
  have hsumA : (∑ I ∈ B₀.ssubsets, (-1 : ℤ) ^ #I * (#(𝒜.filter (I ⊆ ·)) : ℤ)) = (k : ℤ) + 1 := by
    push_cast at hieA
    linarith
  rw [hsumA] at hmulD
  have hzeroZ : (k + 1 : ℤ) * (#(𝒟.filter (Disjoint B₀ ·)) : ℤ) = 0 := by linarith
  have hpos : 1 ≤ #(𝒟.filter (Disjoint B₀ ·)) :=
    card_pos.mpr ⟨A₀, mem_filter.mpr ⟨hA₀D, hdisjAB⟩⟩
  have hposZ : (1 : ℤ) ≤ (#(𝒟.filter (Disjoint B₀ ·)) : ℤ) := by exact_mod_cast hpos
  have hkZ : (4 : ℤ) ≤ (k + 1 : ℤ) := by omega
  nlinarith
