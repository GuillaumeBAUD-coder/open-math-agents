import OMAReductions.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1
import Mathlib

-- Step Erdos651.erdos_651.variants.pohoata_zakharov.R1.H1: hypothesis H1 of reduction Erdos651.erdos_651.variants.pohoata_zakharov.R1
-- Credit: @stochastic-parrot-ftw

open Finset Filter Set Module
open scoped EuclideanGeometry BigOperators Classical Matrix

namespace PZ651

/- ### Part 1: Finite Hypergraph Ramsey Theorem -/

lemma finite_ramsey_sets {α : Type*} [DecidableEq α] (r n : ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
      ∃ Y ⊆ X, Y.card = n ∧ ∃ b : Bool, ∀ A ⊆ Y, A.card = r → c A = b := by
  induction r generalizing n with
  | zero =>
    refine ⟨n, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard⟩ := Finset.exists_subset_card_eq hX
    refine ⟨Y, hYX, hcard, c ∅, fun A _ hA => ?_⟩
    rw [Finset.card_eq_zero.mp hA]
  | succ r ih =>
    have stage (t : ℕ) : ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
        ∃ Y ⊆ X, Y.card = t ∧ ∃ labels : α → Bool,
          ∀ A ⊆ Y, A.card = r + 1 → ∃ a ∈ A, c A = labels a := by
      induction t with
      | zero =>
        refine ⟨0, fun X _ _ => ⟨∅, Finset.empty_subset X, rfl, fun _ => false, ?_⟩⟩
        intro A hA hcard
        rw [Finset.subset_empty.mp hA] at hcard
        simp at hcard
      | succ t it =>
        obtain ⟨M, hM⟩ := it
        obtain ⟨N, hN⟩ := ih M
        refine ⟨N + 1, fun X hX c => ?_⟩
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
        have herase : N ≤ (X.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
        obtain ⟨R, hR, hcardR, b, hb⟩ := hN (X.erase x) herase (fun A => c (insert x A))
        obtain ⟨Y, hY, hcard, labels, hlabels⟩ := hM R hcardR.ge c
        have hxY : x ∉ Y := fun h => (Finset.mem_erase.mp (hR (hY h))).1 rfl
        have hYX := hY.trans (hR.trans (Finset.erase_subset x X))
        refine ⟨insert x Y, Finset.insert_subset hx hYX, by simp [hxY, hcard],
          Function.update labels x b, ?_⟩
        intro A hA hcardA
        by_cases hxA : x ∈ A
        · have hAY : A.erase x ⊆ Y := by
            intro a ha
            obtain ⟨hne, haA⟩ := Finset.mem_erase.mp ha
            exact (Finset.mem_insert.mp (hA haA)).resolve_left hne
          have hac : (A.erase x).card = r := by rw [Finset.card_erase_of_mem hxA, hcardA]; simp
          refine ⟨x, hxA, ?_⟩
          simpa [Finset.insert_erase hxA] using hb _ (hAY.trans hY) hac
        · have hAY : A ⊆ Y := fun a ha =>
            (Finset.mem_insert.mp (hA ha)).resolve_left (fun he => hxA (he ▸ ha))
          obtain ⟨a, ha, hc⟩ := hlabels A hAY hcardA
          have hax : a ≠ x := fun h => hxA (h ▸ ha)
          exact ⟨a, ha, by rwa [Function.update_of_ne hax]⟩
    obtain ⟨N, hN⟩ := stage (2 * n)
    refine ⟨N, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard, labels, hlabels⟩ := hN X hX c
    let U := Y.filter fun a => labels a = true
    let V := Y.filter fun a => labels a ≠ true
    have hsum : U.card + V.card = 2 * n :=
      (Finset.card_filter_add_card_filter_not (s := Y) _).trans hcard
    by_cases hU : n ≤ U.card
    · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hU
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, true, fun A hA hcardA => ?_⟩
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      exact he.trans (Finset.mem_filter.mp (hZ (hA ha))).2
    · have hV : n ≤ V.card := by omega
      obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hV
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, false, fun A hA hcardA => ?_⟩
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      have ht := (Finset.mem_filter.mp (hZ (hA ha))).2
      exact he.trans (by cases h : labels a <;> simp_all)

/- ### Part 2: Dilworth's Theorem (Galvin's proof) and Consequences -/

def IsStrictPO {α : Type*} (lt : α → α → Prop) : Prop :=
  (∀ x, ¬ lt x x) ∧ (∀ x y z, lt x y → lt y z → lt x z)

def IsChain {α : Type*} (lt : α → α → Prop) (C : Finset α) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → lt x y ∨ lt y x

def IsAntichain {α : Type*} (lt : α → α → Prop) (A : Finset α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ¬ lt x y

lemma exists_maximal_of_strictPO {α : Type*} [DecidableEq α] {lt : α → α → Prop}
    (hpo : IsStrictPO lt) {S : Finset α} (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, ¬ lt a b := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    obtain ⟨x, hx⟩ := hS
    let U := S.filter fun b => lt x b
    by_cases hU : U.Nonempty
    · have hUsub : U ⊆ S.erase x := by
        intro b hb
        obtain ⟨hbS, hxb⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_erase.mpr ⟨fun he => hpo.1 x (he ▸ hxb), hbS⟩
      have hUlt : U.card < n := by
        have h1 := Finset.card_le_card hUsub
        have h2 := Finset.card_erase_lt_of_mem hx
        omega
      obtain ⟨a, haU, hmax⟩ := ih U.card hUlt hU rfl
      obtain ⟨haS, hxa⟩ := Finset.mem_filter.mp haU
      refine ⟨a, haS, fun b hbS hab => ?_⟩
      exact hmax b (Finset.mem_filter.mpr ⟨hbS, hpo.2 x a b hxa hab⟩) hab
    · refine ⟨x, hx, fun b hbS hxb => hU ⟨b, Finset.mem_filter.mpr ⟨hbS, hxb⟩⟩⟩

lemma dilworth_chains {α : Type*} [DecidableEq α] {lt : α → α → Prop}
    (hpo : IsStrictPO lt) (S : Finset α) (k : ℕ)
    (hanti : ∀ A ⊆ S, IsAntichain lt A → A.card ≤ k) :
    ∃ C : Finset (Finset α), C.card ≤ k ∧
      (∀ c ∈ C, c ⊆ S ∧ IsChain lt c) ∧
      (∀ c1 ∈ C, ∀ c2 ∈ C, c1 ≠ c2 → Disjoint c1 c2) ∧
      ∀ x ∈ S, ∃ c ∈ C, x ∈ c := by
  induction hn : S.card using Nat.strong_induction_on generalizing S k with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · exact ⟨∅, Nat.zero_le _, by simp, by simp, by simp⟩
    · have hkpos : 1 ≤ k := by
        obtain ⟨x, hx⟩ := hSne
        have h1 : ({x} : Finset α).card ≤ k := hanti {x} (Finset.singleton_subset_iff.mpr hx)
          (fun a ha b hb => by
            simp only [Finset.mem_singleton] at ha hb
            rcases ha with rfl; rcases hb with rfl; exact hpo.1 _)
        simpa using h1
      obtain ⟨a, haS, hamax⟩ := exists_maximal_of_strictPO hpo hSne
      let S' := S.erase a
      have hS'lt : S'.card < n := by rw [← hn]; exact Finset.card_erase_lt_of_mem haS
      let P (j : ℕ) : Prop := ∃ A ⊆ S', IsAntichain lt A ∧ A.card = j
      have hP0 : P 0 := ⟨∅, Finset.empty_subset _, fun _ h => by simp at h, rfl⟩
      let m := Nat.findGreatest P k
      have hm_le : m ≤ k := Nat.findGreatest_le k
      have hm_anti : ∀ A ⊆ S', IsAntichain lt A → A.card ≤ m := by
        intro A hAS' hA
        have hAk : A.card ≤ k := hanti A (hAS'.trans (Finset.erase_subset a S)) hA
        exact Nat.le_findGreatest hAk ⟨A, hAS', hA, rfl⟩
      obtain ⟨C, hCcard, hCprop, hCdisj, hCcov⟩ := ih S'.card hS'lt S' m hm_anti rfl
      by_cases hm_lt : m < k
      · refine ⟨insert {a} C, ?_, ?_, ?_, ?_⟩
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hcC
          · exact ⟨Finset.singleton_subset_iff.mpr haS, fun x hx y hy hne => by
              simp only [Finset.mem_singleton] at hx hy; exact absurd (hx.trans hy.symm) hne⟩
          · exact ⟨(hCprop c hcC).1.trans (Finset.erase_subset a S), (hCprop c hcC).2⟩
        · intro c1 hc1 c2 hc2 hne
          rcases Finset.mem_insert.mp hc1 with rfl | hc1' <;>
          rcases Finset.mem_insert.mp hc2 with rfl | hc2'
          · exact absurd rfl hne
          · rw [Finset.disjoint_singleton_left]
            intro ha'
            exact (Finset.mem_erase.mp ((hCprop c2 hc2').1 ha')).1 rfl
          · rw [Finset.disjoint_singleton_right]
            intro ha'
            exact (Finset.mem_erase.mp ((hCprop c1 hc1').1 ha')).1 rfl
          · exact hCdisj c1 hc1' c2 hc2' hne
        · intro x hx
          by_cases hxa : x = a
          · subst hxa; exact ⟨{x}, Finset.mem_insert_self _ _, Finset.mem_singleton_self _⟩
          · obtain ⟨c, hcC, hxc⟩ := hCcov x (Finset.mem_erase.mpr ⟨hxa, hx⟩)
            exact ⟨c, Finset.mem_insert_of_mem hcC, hxc⟩
      · have hmk : m = k := by omega
        have hPmk : P k := hmk ▸ Nat.findGreatest_spec (Nat.zero_le k) hP0
        have hchain_anti_le1 : ∀ c ∈ C, ∀ A ⊆ S', IsAntichain lt A → (A ∩ c).card ≤ 1 := by
          intro c hcC A _ hA
          refine Finset.card_le_one.mpr fun x hx y hy => ?_
          by_contra hne
          rcases (hCprop c hcC).2 x (Finset.mem_inter.mp hx).2 y (Finset.mem_inter.mp hy).2 hne with h | h
          · exact hA x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 h
          · exact hA y (Finset.mem_inter.mp hy).1 x (Finset.mem_inter.mp hx).1 h
        have hC_ge : k ≤ C.card := by
          obtain ⟨A, hAS', hA, hAcard⟩ := hPmk
          have hsub : A ⊆ C.biUnion fun c => A ∩ c := by
            intro x hx
            obtain ⟨c, hcC, hxc⟩ := hCcov x (hAS' hx)
            exact Finset.mem_biUnion.mpr ⟨c, hcC, Finset.mem_inter.mpr ⟨hx, hxc⟩⟩
          calc k = A.card := hAcard.symm
            _ ≤ (C.biUnion fun c => A ∩ c).card := Finset.card_le_card hsub
            _ ≤ ∑ c ∈ C, (A ∩ c).card := Finset.card_biUnion_le
            _ ≤ ∑ _c ∈ C, 1 := Finset.sum_le_sum fun c hc => hchain_anti_le1 c hc A hAS' hA
            _ = C.card := by simp
        have hCeq : C.card = k := le_antisymm (hCcard.trans hm_le) hC_ge
        have hmeets : ∀ c ∈ C, ∀ A ⊆ S', IsAntichain lt A → A.card = k → (A ∩ c).Nonempty := by
          intro c hcC A hAS' hA hAcard
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          have hsub : A ⊆ (C.erase c).biUnion fun c' => A ∩ c' := by
            intro x hx
            obtain ⟨c', hc'C, hxc'⟩ := hCcov x (hAS' hx)
            have hne : c' ≠ c := by
              rintro rfl
              have : x ∈ A ∩ c' := Finset.mem_inter.mpr ⟨hx, hxc'⟩
              rw [hemp] at this; exact Finset.notMem_empty _ this
            exact Finset.mem_biUnion.mpr ⟨c', Finset.mem_erase.mpr ⟨hne, hc'C⟩,
              Finset.mem_inter.mpr ⟨hx, hxc'⟩⟩
          have hle : k ≤ (C.erase c).card := calc
            k = A.card := hAcard.symm
            _ ≤ ((C.erase c).biUnion fun c' => A ∩ c').card := Finset.card_le_card hsub
            _ ≤ ∑ c' ∈ C.erase c, (A ∩ c').card := Finset.card_biUnion_le
            _ ≤ ∑ _c' ∈ C.erase c, 1 := Finset.sum_le_sum fun c' hc' =>
                hchain_anti_le1 c' (Finset.mem_of_mem_erase hc') A hAS' hA
            _ = (C.erase c).card := by simp
          have := Finset.card_erase_of_mem hcC
          omega
        let M (c : Finset α) : Finset α :=
          c.filter fun x => ∃ A ⊆ S', IsAntichain lt A ∧ A.card = k ∧ x ∈ A
        have hMne : ∀ c ∈ C, (M c).Nonempty := by
          intro c hcC
          obtain ⟨A, hAS', hA, hAcard⟩ := hPmk
          obtain ⟨x, hx⟩ := hmeets c hcC A hAS' hA hAcard
          exact ⟨x, Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hx).2, A, hAS', hA, hAcard,
            (Finset.mem_inter.mp hx).1⟩⟩
        have htop : ∀ c ∈ C, ∃ x ∈ M c, ∀ y ∈ M c, ¬ lt x y := fun c hc =>
          exists_maximal_of_strictPO hpo (hMne c hc)
        choose top htop_mem htop_max using htop
        have htop_ge : ∀ c (hc : c ∈ C), ∀ y ∈ M c, y = top c hc ∨ lt y (top c hc) := by
          intro c hc y hy
          by_cases heq : y = top c hc
          · exact Or.inl heq
          · rcases (hCprop c hc).2 y (Finset.mem_filter.mp hy).1
                (top c hc) (Finset.mem_filter.mp (htop_mem c hc)).1 heq with h | h
            · exact Or.inr h
            · exact absurd h (htop_max c hc y hy)
        have htop_anti : ∀ c1 (hc1 : c1 ∈ C) c2 (hc2 : c2 ∈ C), ¬ lt (top c1 hc1) (top c2 hc2) := by
          intro c1 hc1 c2 hc2 hlt
          obtain ⟨_, A, hAS', hA, hAcard, htop2A⟩ := Finset.mem_filter.mp (htop_mem c2 hc2)
          obtain ⟨y, hy⟩ := hmeets c1 hc1 A hAS' hA hAcard
          have hyA : y ∈ A := (Finset.mem_inter.mp hy).1
          have hyc1 : y ∈ c1 := (Finset.mem_inter.mp hy).2
          have hyM : y ∈ M c1 := Finset.mem_filter.mpr ⟨hyc1, A, hAS', hA, hAcard, hyA⟩
          rcases htop_ge c1 hc1 y hyM with rfl | hylt
          · exact hA _ hyA _ htop2A hlt
          · exact hA _ hyA _ htop2A (hpo.2 _ _ _ hylt hlt)
        by_cases hcomp : ∃ c, ∃ hc : c ∈ C, lt (top c hc) a
        · obtain ⟨c₀, hc₀, hlt_a⟩ := hcomp
          let K := insert a (c₀.filter fun y => y = top c₀ hc₀ ∨ lt y (top c₀ hc₀))
          have hKS : K ⊆ S := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact haS
            · exact Finset.erase_subset a S ((hCprop c₀ hc₀).1 (Finset.mem_filter.mp hx').1)
          have hKchain : IsChain lt K := by
            intro x hx y hy hne
            rcases Finset.mem_insert.mp hx with rfl | hx' <;>
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact absurd rfl hne
            · right
              rcases (Finset.mem_filter.mp hy').2 with rfl | hylt
              · exact hlt_a
              · exact hpo.2 _ _ _ hylt hlt_a
            · left
              rcases (Finset.mem_filter.mp hx').2 with rfl | hxlt
              · exact hlt_a
              · exact hpo.2 _ _ _ hxlt hlt_a
            · exact (hCprop c₀ hc₀).2 x (Finset.mem_filter.mp hx').1
                y (Finset.mem_filter.mp hy').1 hne
          have haK : a ∈ K := Finset.mem_insert_self _ _
          let R := S \ K
          have hRlt : R.card < n := by
            rw [← hn]
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.sdiff_subset, fun he => by
                have hmem : a ∈ R := by rw [he]; exact haS
                exact (Finset.mem_sdiff.mp hmem).2 haK⟩
          have hRanti : ∀ A ⊆ R, IsAntichain lt A → A.card ≤ k - 1 := by
            intro A hAR hA
            have hAS' : A ⊆ S' := fun x hx => by
              have hxR := Finset.mem_sdiff.mp (hAR hx)
              exact Finset.mem_erase.mpr ⟨fun h => hxR.2 (h ▸ haK), hxR.1⟩
            have hAle : A.card ≤ k := hmk ▸ hm_anti A hAS' hA
            by_contra! hge
            have hAeq : A.card = k := by omega
            obtain ⟨y, hy⟩ := hmeets c₀ hc₀ A hAS' hA hAeq
            have hyA : y ∈ A := (Finset.mem_inter.mp hy).1
            have hyc0 : y ∈ c₀ := (Finset.mem_inter.mp hy).2
            have hyM : y ∈ M c₀ := Finset.mem_filter.mpr ⟨hyc0, A, hAS', hA, hAeq, hyA⟩
            have hyK : y ∈ K := Finset.mem_insert_of_mem
              (Finset.mem_filter.mpr ⟨hyc0, htop_ge c₀ hc₀ y hyM⟩)
            exact (Finset.mem_sdiff.mp (hAR hyA)).2 hyK
          obtain ⟨C', hC'card, hC'prop, hC'disj, hC'cov⟩ := ih R.card hRlt R (k - 1) hRanti rfl
          refine ⟨insert K C', ?_, ?_, ?_, ?_⟩
          · exact (Finset.card_insert_le _ _).trans (by omega)
          · intro c hc
            rcases Finset.mem_insert.mp hc with rfl | hc'
            · exact ⟨hKS, hKchain⟩
            · exact ⟨(hC'prop c hc').1.trans Finset.sdiff_subset, (hC'prop c hc').2⟩
          · intro c1 hc1 c2 hc2 hne
            rcases Finset.mem_insert.mp hc1 with rfl | hc1' <;>
            rcases Finset.mem_insert.mp hc2 with rfl | hc2'
            · exact absurd rfl hne
            · rw [Finset.disjoint_left]
              intro x hxK hxc2
              exact (Finset.mem_sdiff.mp ((hC'prop c2 hc2').1 hxc2)).2 hxK
            · rw [Finset.disjoint_right]
              intro x hxK hxc1
              exact (Finset.mem_sdiff.mp ((hC'prop c1 hc1').1 hxc1)).2 hxK
            · exact hC'disj c1 hc1' c2 hc2' hne
          · intro x hx
            by_cases hxK : x ∈ K
            · exact ⟨K, Finset.mem_insert_self _ _, hxK⟩
            · obtain ⟨c, hc', hxc⟩ := hC'cov x (Finset.mem_sdiff.mpr ⟨hx, hxK⟩)
              exact ⟨c, Finset.mem_insert_of_mem hc', hxc⟩
        · exfalso
          let T := C.attach.image fun c => top c.1 c.2
          have hTinj : Function.Injective (fun c : {c // c ∈ C} => top c.1 c.2) := by
            intro c1 c2 heq
            by_contra hne
            have hne' : c1.1 ≠ c2.1 := fun h => hne (Subtype.ext h)
            dsimp only at heq
            have h1 : top c1.1 c1.2 ∈ c1.1 := (Finset.mem_filter.mp (htop_mem c1.1 c1.2)).1
            have h2 : top c1.1 c1.2 ∈ c2.1 := by
              rw [heq]; exact (Finset.mem_filter.mp (htop_mem c2.1 c2.2)).1
            exact Finset.disjoint_left.mp (hCdisj c1.1 c1.2 c2.1 c2.2 hne') h1 h2
          have hTcard : T.card = k := by
            rw [Finset.card_image_of_injective _ hTinj, Finset.card_attach, hCeq]
          have hTS' : T ⊆ S' := by
            intro x hx
            obtain ⟨⟨c, hc⟩, _, rfl⟩ := Finset.mem_image.mp hx
            exact (hCprop c hc).1 (Finset.mem_filter.mp (htop_mem c hc)).1
          have haT : a ∉ T := fun ha => (Finset.mem_erase.mp (hTS' ha)).1 rfl
          have hATsub : insert a T ⊆ S :=
            Finset.insert_subset haS (hTS'.trans (Finset.erase_subset a S))
          have hATanti : IsAntichain lt (insert a T) := by
            intro x hx y hy
            rcases Finset.mem_insert.mp hx with rfl | hxT <;>
            rcases Finset.mem_insert.mp hy with rfl | hyT
            · exact hpo.1 _
            · exact hamax y (Finset.erase_subset _ S (hTS' hyT))
            · obtain ⟨⟨c, hc⟩, _, rfl⟩ := Finset.mem_image.mp hxT
              intro hlt; exact hcomp ⟨c, hc, hlt⟩
            · obtain ⟨⟨c1, hc1⟩, _, rfl⟩ := Finset.mem_image.mp hxT
              obtain ⟨⟨c2, hc2⟩, _, rfl⟩ := Finset.mem_image.mp hyT
              exact htop_anti c1 hc1 c2 hc2
          have hcard_le := hanti (insert a T) hATsub hATanti
          rw [Finset.card_insert_of_notMem haT, hTcard] at hcard_le
          omega

lemma chain_or_antichain {α : Type*} [DecidableEq α] {lt : α → α → Prop}
    (hpo : IsStrictPO lt) (S : Finset α) (a b : ℕ) (hcard : a * b < S.card) :
    (∃ C ⊆ S, IsChain lt C ∧ a < C.card) ∨ (∃ A ⊆ S, IsAntichain lt A ∧ b < A.card) := by
  by_contra h
  push Not at h
  obtain ⟨hC, hA⟩ := h
  obtain ⟨Cs, hCscard, hCsprop, _, hCscov⟩ := dilworth_chains hpo S b hA
  have hsub : S ⊆ Cs.biUnion id := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hCscov x hx
    exact Finset.mem_biUnion.mpr ⟨c, hc, hxc⟩
  have hle : S.card ≤ a * b := calc
    S.card ≤ (Cs.biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ Cs, c.card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ Cs, a := Finset.sum_le_sum fun c hc => hC c (hCsprop c hc).1 (hCsprop c hc).2
    _ = Cs.card * a := by simp
    _ ≤ b * a := Nat.mul_le_mul_right a hCscard
    _ = a * b := Nat.mul_comm b a
  omega

lemma dilworth_three_orders {α : Type*} [DecidableEq α]
    {lt1 lt2 lt3 : α → α → Prop}
    (hpo1 : IsStrictPO lt1) (hpo2 : IsStrictPO lt2) (hpo3 : IsStrictPO lt3)
    (S : Finset α)
    (hincomp : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (¬ lt1 x y ∧ ¬ lt1 y x) ∨ (¬ lt2 x y ∧ ¬ lt2 y x) ∨ (¬ lt3 x y ∧ ¬ lt3 y x))
    (M : ℕ) (hcard : M ^ 3 < S.card) :
    (∃ A ⊆ S, IsAntichain lt1 A ∧ M < A.card) ∨
    (∃ A ⊆ S, IsAntichain lt2 A ∧ M < A.card) ∨
    (∃ A ⊆ S, IsAntichain lt3 A ∧ M < A.card) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨C1, hC1card, hC1prop, _, hC1cov⟩ := dilworth_chains hpo1 S M h1
  obtain ⟨C2, hC2card, hC2prop, _, hC2cov⟩ := dilworth_chains hpo2 S M h2
  obtain ⟨C3, hC3card, hC3prop, _, hC3cov⟩ := dilworth_chains hpo3 S M h3
  choose f1 hf1C hf1mem using hC1cov
  choose f2 hf2C hf2mem using hC2cov
  choose f3 hf3C hf3mem using hC3cov
  let φ : {x // x ∈ S} → (C1 ×ˢ (C2 ×ˢ C3)) := fun x =>
    ⟨(f1 x.1 x.2, (f2 x.1 x.2, f3 x.1 x.2)),
      Finset.mem_product.mpr ⟨hf1C x.1 x.2, Finset.mem_product.mpr ⟨hf2C x.1 x.2, hf3C x.1 x.2⟩⟩⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    by_contra hne
    have hne' : x.1 ≠ y.1 := fun he => hne (Subtype.ext he)
    have he1 : f1 x.1 x.2 = f1 y.1 y.2 := congrArg (fun p => p.1.1) hxy
    have he2 : f2 x.1 x.2 = f2 y.1 y.2 := congrArg (fun p => p.1.2.1) hxy
    have he3 : f3 x.1 x.2 = f3 y.1 y.2 := congrArg (fun p => p.1.2.2) hxy
    have hc1 := (hC1prop _ (hf1C x.1 x.2)).2 x.1 (hf1mem x.1 x.2) y.1 (he1 ▸ hf1mem y.1 y.2) hne'
    have hc2 := (hC2prop _ (hf2C x.1 x.2)).2 x.1 (hf2mem x.1 x.2) y.1 (he2 ▸ hf2mem y.1 y.2) hne'
    have hc3 := (hC3prop _ (hf3C x.1 x.2)).2 x.1 (hf3mem x.1 x.2) y.1 (he3 ▸ hf3mem y.1 y.2) hne'
    rcases hincomp x.1 x.2 y.1 y.2 hne' with ⟨n1, n2⟩ | ⟨n1, n2⟩ | ⟨n1, n2⟩
    · exact hc1.elim n1 n2
    · exact hc2.elim n1 n2
    · exact hc3.elim n1 n2
  have hle : S.card ≤ (C1 ×ˢ (C2 ×ˢ C3)).card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective φ hφinj
  have hprod : (C1 ×ˢ (C2 ×ˢ C3)).card ≤ M ^ 3 := by
    simp only [Finset.card_product, pow_succ, pow_zero, one_mul]
    calc C1.card * (C2.card * C3.card)
      _ ≤ M * (M * M) := Nat.mul_le_mul hC1card (Nat.mul_le_mul hC2card hC3card)
      _ = M * M * M := by ring
  omega

/- ### Part 3: 2D Erdős–Szekeres Cups-vs-Caps Theorem -/

noncomputable def slope2 (p q : ℝ × ℝ) : ℝ := (q.2 - p.2) / (q.1 - p.1)

def IsCap2 (C : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a.1 < b.1 → b.1 < c.1 → slope2 b c < slope2 a b

def IsCup2 (C : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a.1 < b.1 → b.1 < c.1 → slope2 a b < slope2 b c

lemma slope2_gt_between {a b c : ℝ × ℝ} (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (h : slope2 b c < slope2 a b) : slope2 a c < slope2 a b ∧ slope2 b c < slope2 a c := by
  have h1 : 0 < b.1 - a.1 := sub_pos.mpr hab
  have h2 : 0 < c.1 - b.1 := sub_pos.mpr hbc
  have h3 : 0 < c.1 - a.1 := sub_pos.mpr (hab.trans hbc)
  dsimp [slope2] at h ⊢
  rw [div_lt_div_iff₀ h2 h1] at h
  constructor
  · rw [div_lt_div_iff₀ h3 h1]; nlinarith
  · rw [div_lt_div_iff₀ h2 h3]; nlinarith

lemma slope2_lt_between {a b c : ℝ × ℝ} (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (h : slope2 a b < slope2 b c) : slope2 a b < slope2 a c ∧ slope2 a c < slope2 b c := by
  have h1 : 0 < b.1 - a.1 := sub_pos.mpr hab
  have h2 : 0 < c.1 - b.1 := sub_pos.mpr hbc
  have h3 : 0 < c.1 - a.1 := sub_pos.mpr (hab.trans hbc)
  dsimp [slope2] at h ⊢
  rw [div_lt_div_iff₀ h1 h2] at h
  constructor
  · rw [div_lt_div_iff₀ h1 h3]; nlinarith
  · rw [div_lt_div_iff₀ h3 h2]; nlinarith

lemma isCap2_of_card_le_two {C : Finset (ℝ × ℝ)} (hC : C.card ≤ 2) : IsCap2 C := by
  intro a ha b hb c hc hab hbc
  exfalso
  have hne1 : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hne2 : b ≠ c := fun h => hbc.ne (congrArg Prod.fst h)
  have hne3 : a ≠ c := fun h => (hab.trans hbc).ne (congrArg Prod.fst h)
  have hsub : ({a, b, c} : Finset (ℝ × ℝ)) ⊆ C := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset (ℝ × ℝ)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne2]
    · simp [hne1, hne3]
  have := Finset.card_le_card hsub
  omega

lemma isCup2_of_card_le_two {C : Finset (ℝ × ℝ)} (hC : C.card ≤ 2) : IsCup2 C := by
  intro a ha b hb c hc hab hbc
  exfalso
  have hne1 : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  have hne2 : b ≠ c := fun h => hbc.ne (congrArg Prod.fst h)
  have hne3 : a ≠ c := fun h => (hab.trans hbc).ne (congrArg Prod.fst h)
  have hsub : ({a, b, c} : Finset (ℝ × ℝ)) ⊆ C := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset (ℝ × ℝ)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne2]
    · simp [hne1, hne3]
  have := Finset.card_le_card hsub
  omega

lemma erdos_szekeres_cups_caps :
    ∀ s a b : ℕ, a + b = s → 2 ≤ a → 2 ≤ b →
    ∀ (X : Finset (ℝ × ℝ)),
      (∀ p ∈ X, ∀ q ∈ X, p.1 = q.1 → p = q) →
      (∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X, p.1 < q.1 → q.1 < r.1 → slope2 p q ≠ slope2 q r) →
      Nat.choose (a + b - 4) (a - 2) < X.card →
      (∃ C ⊆ X, IsCap2 C ∧ C.card = a) ∨ (∃ C ⊆ X, IsCup2 C ∧ C.card = b) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b hs ha hb X hxinj hgp hcard
    by_cases ha2 : a = 2
    · subst ha2
      have h2le : 2 ≤ X.card := by
        simp only [Nat.sub_self, Nat.choose_zero_right] at hcard; omega
      obtain ⟨C, hCX, hCcard⟩ := Finset.exists_subset_card_eq h2le
      exact Or.inl ⟨C, hCX, isCap2_of_card_le_two hCcard.le, hCcard⟩
    · by_cases hb2 : b = 2
      · subst hb2
        have h2le : 2 ≤ X.card := by
          have : Nat.choose (a + 2 - 4) (a - 2) = 1 := by
            rw [show a + 2 - 4 = a - 2 by omega, Nat.choose_self]
          omega
        obtain ⟨C, hCX, hCcard⟩ := Finset.exists_subset_card_eq h2le
        exact Or.inr ⟨C, hCX, isCup2_of_card_le_two hCcard.le, hCcard⟩
      · have ha3 : 3 ≤ a := by omega
        have hb3 : 3 ≤ b := by omega
        let L := X.filter fun p =>
          ∃ K ⊆ X, IsCap2 K ∧ K.card = a - 1 ∧ p ∈ K ∧ ∀ q ∈ K, q.1 ≤ p.1
        let R := X \ L
        have hLR : L.card + R.card = X.card := by
          change L.card + (X \ L).card = X.card
          have hsub : L ⊆ X := Finset.filter_subset _ _
          have := Finset.card_sdiff_add_card_eq_card hsub
          omega
        have hpascal : Nat.choose (a + b - 4) (a - 2) =
            Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) +
            Nat.choose (a + (b - 1) - 4) (a - 2) := by
          have h1 : a + b - 4 = (a + b - 5) + 1 := by omega
          have h2 : a - 2 = (a - 3) + 1 := by omega
          have h3 : (a - 1) + b - 4 = a + b - 5 := by omega
          have h4 : (a - 1) - 2 = a - 3 := by omega
          have h5 : a + (b - 1) - 4 = a + b - 5 := by omega
          rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ, add_comm]
        by_cases hR : Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) < R.card
        · have hRsub : R ⊆ X := Finset.sdiff_subset
          have hih := ih ((a - 1) + b) (by omega) (a - 1) b rfl (by omega) hb R
            (fun p hp q hq => hxinj p (hRsub hp) q (hRsub hq))
            (fun p hp q hq r hr => hgp p (hRsub hp) q (hRsub hq) r (hRsub hr)) hR
          rcases hih with ⟨K, hKR, hKcap, hKcard⟩ | ⟨U, hUR, hUcup, hUcard⟩
          · exfalso
            have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨p, hpK, hpmax⟩ := Finset.exists_max_image K Prod.fst hKne
            have hpL : p ∈ L := Finset.mem_filter.mpr
              ⟨hRsub (hKR hpK), K, hKR.trans hRsub, hKcap, hKcard, hpK, hpmax⟩
            exact (Finset.mem_sdiff.mp (hKR hpK)).2 hpL
          · exact Or.inr ⟨U, hUR.trans hRsub, hUcup, hUcard⟩
        · have hL : Nat.choose (a + (b - 1) - 4) (a - 2) < L.card := by omega
          have hLsub : L ⊆ X := Finset.filter_subset _ _
          have hih := ih (a + (b - 1)) (by omega) a (b - 1) rfl ha (by omega) L
            (fun p hp q hq => hxinj p (hLsub hp) q (hLsub hq))
            (fun p hp q hq r hr => hgp p (hLsub hp) q (hLsub hq) r (hLsub hr)) hL
          rcases hih with ⟨K, hKL, hKcap, hKcard⟩ | ⟨U, hUL, hUcup, hUcard⟩
          · exact Or.inl ⟨K, hKL.trans hLsub, hKcap, hKcard⟩
          · have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨p, hpU, hpmin⟩ := Finset.exists_min_image U Prod.fst hUne
            obtain ⟨hpX, K, hKX, hKcap, hKcard, hpK, hpmax⟩ := Finset.mem_filter.mp (hUL hpU)
            have hKerase_ne : (K.erase p).Nonempty := by
              rw [← Finset.card_pos, Finset.card_erase_of_mem hpK]; omega
            obtain ⟨q, hqKe, hqmax⟩ := Finset.exists_max_image (K.erase p) Prod.fst hKerase_ne
            have hqK : q ∈ K := Finset.mem_of_mem_erase hqKe
            have hqnep : q ≠ p := (Finset.mem_erase.mp hqKe).1
            have hqp : q.1 < p.1 :=
              lt_of_le_of_ne (hpmax q hqK) (fun h => hqnep (hxinj q (hKX hqK) p hpX h))
            have hUerase_ne : (U.erase p).Nonempty := by
              rw [← Finset.card_pos, Finset.card_erase_of_mem hpU]; omega
            obtain ⟨r, hrUe, hrmin⟩ := Finset.exists_min_image (U.erase p) Prod.fst hUerase_ne
            have hrU : r ∈ U := Finset.mem_of_mem_erase hrUe
            have hrnep : r ≠ p := (Finset.mem_erase.mp hrUe).1
            have hpr : p.1 < r.1 :=
              lt_of_le_of_ne (hpmin r hrU) (fun h => hrnep (hxinj r (hLsub (hUL hrU)) p hpX h.symm))
            have hne_slope := hgp q (hKX hqK) p hpX r (hLsub (hUL hrU)) hqp hpr
            rcases lt_or_gt_of_ne hne_slope with hlt | hgt
            · -- slope q p < slope p r ⇒ insert q U is a b-cup!
              have hqnotU : q ∉ U := fun hqU => by linarith [hpmin q hqU]
              refine Or.inr ⟨insert q U, Finset.insert_subset (hKX hqK) (hUL.trans hLsub), ?_, ?_⟩
              · intro u hu v hv w hw huv hvw
                rcases Finset.mem_insert.mp hu with rfl | huU
                · have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left
                    (fun h => huv.ne' (congrArg Prod.fst h))
                  have hwU : w ∈ U := (Finset.mem_insert.mp hw).resolve_left
                    (fun h => (huv.trans hvw).ne' (congrArg Prod.fst h))
                  by_cases hvp : v = p
                  · subst hvp
                    by_cases hwr : w = r
                    · subst hwr; exact hlt
                    · have hrv : r.1 < w.1 := lt_of_le_of_ne (hrmin w (Finset.mem_erase.mpr
                        ⟨fun h => hvw.ne (congrArg Prod.fst h.symm), hwU⟩))
                        (fun h => hwr (hxinj w (hLsub (hUL hwU)) r (hLsub (hUL hrU)) h.symm))
                      have h1 := hUcup v hpU r hrU w hwU hpr hrv
                      exact hlt.trans (slope2_lt_between hpr hrv h1).1
                  · have hpv : p.1 < v.1 := lt_of_le_of_ne (hpmin v hvU)
                      (fun h => hvp (hxinj v (hLsub (hUL hvU)) p hpX h.symm))
                    have h1 := hUcup p hpU v hvU w hwU hpv hvw
                    have h2 : slope2 p r ≤ slope2 p v := by
                      by_cases hvr : v = r
                      · subst hvr; exact le_rfl
                      · have hrv : r.1 < v.1 := lt_of_le_of_ne
                          (hrmin v (Finset.mem_erase.mpr ⟨hvp, hvU⟩))
                          (fun h => hvr (hxinj v (hLsub (hUL hvU)) r (hLsub (hUL hrU)) h.symm))
                        exact (slope2_lt_between hpr hrv (hUcup p hpU r hrU v hvU hpr hrv)).1.le
                    have hqp_lt_pv : slope2 u p < slope2 p v := lt_of_lt_of_le hlt h2
                    have hqv_lt_pv : slope2 u v < slope2 p v :=
                      (slope2_lt_between hqp hpv hqp_lt_pv).2
                    exact hqv_lt_pv.trans h1
                · have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left (fun h => by
                    have h1 : v.1 = q.1 := congrArg Prod.fst h; linarith [hpmin u huU])
                  have hwU : w ∈ U := (Finset.mem_insert.mp hw).resolve_left (fun h => by
                    have h1 : w.1 = q.1 := congrArg Prod.fst h; linarith [hpmin u huU])
                  exact hUcup u huU v hvU w hwU huv hvw
              · rw [Finset.card_insert_of_notMem hqnotU, hUcard]; omega
            · -- slope p r < slope q p ⇒ insert r K is an a-cap!
              have hrnotK : r ∉ K := fun hrK => by linarith [hpmax r hrK]
              refine Or.inl ⟨insert r K, Finset.insert_subset (hLsub (hUL hrU)) hKX, ?_, ?_⟩
              · intro u hu v hv w hw huv hvw
                rcases Finset.mem_insert.mp hw with rfl | hwK
                · have huK : u ∈ K := (Finset.mem_insert.mp hu).resolve_left
                    (fun h => (huv.trans hvw).ne (congrArg Prod.fst h))
                  have hvK : v ∈ K := (Finset.mem_insert.mp hv).resolve_left
                    (fun h => hvw.ne (congrArg Prod.fst h))
                  by_cases hvp : v = p
                  · subst hvp
                    by_cases huq : u = q
                    · subst huq; exact hgt
                    · have huq_lt : u.1 < q.1 := lt_of_le_of_ne
                        (hqmax u (Finset.mem_erase.mpr
                          ⟨fun h => huv.ne (congrArg Prod.fst h), huK⟩))
                        (fun h => huq (hxinj u (hKX huK) q (hKX hqK) h))
                      have h1 := hKcap u huK q hqK v hpK huq_lt hqp
                      exact hgt.trans (slope2_gt_between huq_lt hqp h1).2
                  · have hvp_lt : v.1 < p.1 := lt_of_le_of_ne (hpmax v hvK)
                      (fun h => hvp (hxinj v (hKX hvK) p hpX h))
                    have h1 := hKcap u huK v hvK p hpK huv hvp_lt
                    have h2 : slope2 q p ≤ slope2 v p := by
                      by_cases hvq : v = q
                      · subst hvq; exact le_rfl
                      · have hvq_lt : v.1 < q.1 := lt_of_le_of_ne
                          (hqmax v (Finset.mem_erase.mpr ⟨hvp, hvK⟩))
                          (fun h => hvq (hxinj v (hKX hvK) q (hKX hqK) h))
                        exact (slope2_gt_between hvq_lt hqp (hKcap v hvK q hqK p hpK hvq_lt hqp)).2.le
                    have hpr_lt_vp : slope2 p w < slope2 v p := lt_of_lt_of_le hgt h2
                    have hvr_lt_vp : slope2 v w < slope2 v p :=
                      (slope2_gt_between hvp_lt hpr hpr_lt_vp).1
                    exact hvr_lt_vp.trans h1
                · have huK : u ∈ K := (Finset.mem_insert.mp hu).resolve_left (fun h => by
                    have h1 : u.1 = r.1 := congrArg Prod.fst h; linarith [hpmax w hwK])
                  have hvK : v ∈ K := (Finset.mem_insert.mp hv).resolve_left (fun h => by
                    have h1 : v.1 = r.1 := congrArg Prod.fst h; linarith [hpmax w hwK])
                  exact hKcap u huK v hvK w hwK huv hvw
              · rw [Finset.card_insert_of_notMem hrnotK, hKcard]; omega

/- ### Part 4: Elementary Binomial Bound (no Stirling) -/

lemma choose_le_exp_mul_pow (N k : ℕ) {t : ℝ} (ht : 0 < t) :
    (Nat.choose N k : ℝ) ≤ Real.exp ((N : ℝ) / t) * t ^ k := by
  by_cases hk : k ≤ N
  · have hsum : (1 / t + 1) ^ N =
        ∑ m ∈ Finset.range (N + 1), (1 / t) ^ m * (1 : ℝ) ^ (N - m) * (Nat.choose N m : ℝ) :=
      add_pow (1 / t) 1 N
    have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    have hnonneg : ∀ m ∈ Finset.range (N + 1),
        0 ≤ (1 / t) ^ m * (1 : ℝ) ^ (N - m) * (Nat.choose N m : ℝ) := fun m _ => by positivity
    have hle := Finset.single_le_sum hnonneg hmem
    rw [← hsum, one_pow, mul_one] at hle
    have hpow : (1 / t + 1) ^ N ≤ Real.exp ((N : ℝ) / t) := by
      calc (1 / t + 1) ^ N
        _ ≤ (Real.exp (1 / t)) ^ N :=
            pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp (1 / t)) N
        _ = Real.exp ((N : ℝ) * (1 / t)) := (Real.exp_nat_mul (1 / t) N).symm
        _ = Real.exp ((N : ℝ) / t) := by ring_nf
    have hmul := mul_le_mul_of_nonneg_right (hle.trans hpow) (pow_nonneg ht.le k)
    have hcancel : (1 / t) ^ k * (Nat.choose N k : ℝ) * t ^ k = (Nat.choose N k : ℝ) := by
      rw [one_div, inv_pow]
      field_simp [pow_ne_zero k ht.ne']
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    positivity

lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  rw [← Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h1 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h2 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

lemma choose_le_rpow {N k t : ℕ} (ht : 2 ≤ t) :
    (Nat.choose N k : ℝ) ≤ (t : ℝ) ^ ((2 * (N : ℝ)) / (t : ℝ) + (k : ℝ)) := by
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hlog : (1 / 2 : ℝ) ≤ Real.log (t : ℝ) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) ht2)
  have h1 := choose_le_exp_mul_pow N k htpos
  have hexp : Real.exp ((N : ℝ) / (t : ℝ)) ≤ (t : ℝ) ^ ((2 * (N : ℝ)) / (t : ℝ)) := by
    rw [Real.rpow_def_of_pos htpos]
    apply Real.exp_le_exp.mpr
    have hnn : 0 ≤ (N : ℝ) / (t : ℝ) := by positivity
    calc (N : ℝ) / (t : ℝ)
      _ = (1 / 2 : ℝ) * ((2 * (N : ℝ)) / (t : ℝ)) := by ring
      _ ≤ Real.log (t : ℝ) * ((2 * (N : ℝ)) / (t : ℝ)) :=
          mul_le_mul_of_nonneg_right hlog (by positivity)
  calc (Nat.choose N k : ℝ)
    _ ≤ Real.exp ((N : ℝ) / (t : ℝ)) * (t : ℝ) ^ k := h1
    _ ≤ (t : ℝ) ^ ((2 * (N : ℝ)) / (t : ℝ)) * (t : ℝ) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_right hexp (pow_nonneg htpos.le k)
    _ = (t : ℝ) ^ ((2 * (N : ℝ)) / (t : ℝ) + (k : ℝ)) := (Real.rpow_add htpos _ _).symm

/- ### Part 5: Centerpoint Theorem (from Mathlib's Helly Theorem) -/

lemma centerpoint_exists {d : ℕ} (S : Finset (ℝ^d)) (hS : S.Nonempty) :
    ∃ c : ℝ^d, ∀ (f : (ℝ^d) →ₗ[ℝ] ℝ) (r : ℝ), r ≤ f c →
      S.card ≤ (d + 1) * (S.filter fun x => r ≤ f x).card := by
  let Fset := S.powerset.filter fun T => d * S.card < (d + 1) * T.card
  have hconv : ∀ T ∈ Fset, Convex ℝ (convexHull ℝ (T : Set (ℝ^d))) :=
    fun T _ => convex_convexHull ℝ _
  have hinter : ∀ I ⊆ Fset, I.card ≤ Module.finrank ℝ (ℝ^d) + 1 →
      (⋂ T ∈ I, convexHull ℝ (T : Set (ℝ^d))).Nonempty := by
    intro I hIF hIcard
    rw [finrank_euclideanSpace_fin] at hIcard
    rcases I.eq_empty_or_nonempty with rfl | hIne
    · obtain ⟨x, _⟩ := hS; exact ⟨x, by simp⟩
    · let bad := I.biUnion fun T => S \ T
      have hbad_sub : bad ⊆ S := Finset.biUnion_subset.mpr fun _ _ => Finset.sdiff_subset
      have hbad_lt : bad.card < S.card := by
        have hlt_each : ∀ T ∈ I, (d + 1) * (S \ T).card < S.card := by
          intro T hTI
          have hTF := Finset.mem_filter.mp (hIF hTI)
          have hTS : T ⊆ S := Finset.mem_powerset.mp hTF.1
          have hsd := Finset.card_sdiff_add_card_eq_card hTS
          have hbig := hTF.2
          nlinarith
        have hsum_lt : ∑ T ∈ I, (d + 1) * (S \ T).card < ∑ _T ∈ I, S.card :=
          Finset.sum_lt_sum_of_nonempty hIne hlt_each
        have h1 : (d + 1) * bad.card ≤ (d + 1) * ∑ T ∈ I, (S \ T).card :=
          Nat.mul_le_mul_left (d + 1) Finset.card_biUnion_le
        rw [Finset.mul_sum] at h1
        have h2 : ∑ _T ∈ I, S.card = I.card * S.card := by simp
        have h3 : I.card * S.card ≤ (d + 1) * S.card := Nat.mul_le_mul_right S.card hIcard
        nlinarith
      have hne_sdiff : (S \ bad).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_eq_card hbad_sub
        omega
      obtain ⟨x, hx⟩ := hne_sdiff
      obtain ⟨hxS, hxnotbad⟩ := Finset.mem_sdiff.mp hx
      refine ⟨x, Set.mem_iInter₂.mpr fun T hTI => subset_convexHull ℝ (T : Set (ℝ^d)) ?_⟩
      change x ∈ T
      by_contra hxT
      exact hxnotbad (Finset.mem_biUnion.mpr ⟨T, hTI, Finset.mem_sdiff.mpr ⟨hxS, hxT⟩⟩)
  obtain ⟨c, hc⟩ := Convex.helly_theorem' hconv hinter
  refine ⟨c, fun f r hfc => ?_⟩
  by_contra! hlt
  let T := S.filter fun x => f x < r
  have hpart : (S.filter fun x => r ≤ f x).card + T.card = S.card := by
    have : T = S.filter fun x => ¬ (r ≤ f x) := by ext x; simp [T]
    rw [this]
    exact Finset.card_filter_add_card_filter_not _
  have hTF : T ∈ Fset := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), by nlinarith⟩
  have hcT : c ∈ convexHull ℝ (T : Set (ℝ^d)) := Set.mem_iInter₂.mp hc T hTF
  have hsub : convexHull ℝ (T : Set (ℝ^d)) ⊆ {x : ℝ^d | f x < r} := by
    apply convexHull_min
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · exact convex_halfSpace_lt f.isLinear r
  have : f c < r := hsub hcT
  linarith

/- ### Part 6: Kirchberger's Theorem -/

lemma kirchberger {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A B : Finset E)
    (hne : (convexHull ℝ (A : Set E) ∩ convexHull ℝ (B : Set E)).Nonempty) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, A'.card + B'.card ≤ Module.finrank ℝ E + 2 ∧
      (convexHull ℝ (A' : Set E) ∩ convexHull ℝ (B' : Set E)).Nonempty := by
  induction hn : A.card + B.card using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    by_cases hle : A.card + B.card ≤ Module.finrank ℝ E + 2
    · exact ⟨A, Finset.Subset.rfl, B, Finset.Subset.rfl, hle, hne⟩
    · obtain ⟨p, hpA, hpB⟩ := hne
      rw [Finset.convexHull_eq] at hpA hpB
      obtain ⟨wA, hwA_nn, hwA_sum, hwA_cm⟩ := hpA
      obtain ⟨wB, hwB_nn, hwB_sum, hwB_cm⟩ := hpB
      rw [Finset.centerMass_eq_of_sum_1 _ _ hwA_sum] at hwA_cm
      rw [Finset.centerMass_eq_of_sum_1 _ _ hwB_sum] at hwB_cm
      simp only [id_eq] at hwA_cm hwB_cm
      by_cases hzeroA : ∃ a ∈ A, wA a = 0
      · obtain ⟨a, haA, hwa0⟩ := hzeroA
        have hlt : (A.erase a).card + B.card < n := by
          rw [← hn, Finset.card_erase_of_mem haA]; have := Finset.card_pos.mpr ⟨a, haA⟩; omega
        have hpA' : p ∈ convexHull ℝ ((A.erase a : Finset E) : Set E) := by
          rw [Finset.convexHull_eq]
          refine ⟨wA, fun x hx => hwA_nn x (Finset.mem_of_mem_erase hx), ?_, ?_⟩
          · rw [Finset.sum_erase_eq_sub haA, hwa0, sub_zero]; exact hwA_sum
          · have hsum1 : ∑ x ∈ A.erase a, wA x = 1 := by
              rw [Finset.sum_erase_eq_sub haA, hwa0, sub_zero]; exact hwA_sum
            rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
            simp only [id_eq]
            rw [Finset.sum_erase_eq_sub haA, hwa0, zero_smul, sub_zero]
            exact hwA_cm
        obtain ⟨A', hA', B', hB', hcard', hne'⟩ :=
          ih _ hlt (A.erase a) B ⟨p, hpA', by
            rw [Finset.convexHull_eq]
            exact ⟨wB, hwB_nn, hwB_sum, by
              rw [Finset.centerMass_eq_of_sum_1 _ _ hwB_sum]; simpa using hwB_cm⟩⟩ rfl
        exact ⟨A', hA'.trans (Finset.erase_subset a A), B', hB', hcard', hne'⟩
      · by_cases hzeroB : ∃ b ∈ B, wB b = 0
        · obtain ⟨b, hbB, hwb0⟩ := hzeroB
          have hlt : A.card + (B.erase b).card < n := by
            rw [← hn, Finset.card_erase_of_mem hbB]; have := Finset.card_pos.mpr ⟨b, hbB⟩; omega
          have hpB' : p ∈ convexHull ℝ ((B.erase b : Finset E) : Set E) := by
            rw [Finset.convexHull_eq]
            refine ⟨wB, fun x hx => hwB_nn x (Finset.mem_of_mem_erase hx), ?_, ?_⟩
            · rw [Finset.sum_erase_eq_sub hbB, hwb0, sub_zero]; exact hwB_sum
            · have hsum1 : ∑ x ∈ B.erase b, wB x = 1 := by
                rw [Finset.sum_erase_eq_sub hbB, hwb0, sub_zero]; exact hwB_sum
              rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
              simp only [id_eq]
              rw [Finset.sum_erase_eq_sub hbB, hwb0, zero_smul, sub_zero]
              exact hwB_cm
          obtain ⟨A', hA', B', hB', hcard', hne'⟩ :=
            ih _ hlt A (B.erase b) ⟨p, by
              rw [Finset.convexHull_eq]
              exact ⟨wA, hwA_nn, hwA_sum, by
                rw [Finset.centerMass_eq_of_sum_1 _ _ hwA_sum]; simpa using hwA_cm⟩, hpB'⟩ rfl
          exact ⟨A', hA', B', hB'.trans (Finset.erase_subset b B), hcard', hne'⟩
        · push Not at hzeroA hzeroB
          have hwA_pos : ∀ a ∈ A, 0 < wA a := fun a ha => lt_of_le_of_ne (hwA_nn a ha) (Ne.symm (hzeroA a ha))
          have hwB_pos : ∀ b ∈ B, 0 < wB b := fun b hb => lt_of_le_of_ne (hwB_nn b hb) (Ne.symm (hzeroB b hb))
          let Φ : ((A → ℝ) × (B → ℝ)) →ₗ[ℝ] (E × ℝ × ℝ) :=
            { toFun := fun uv =>
                (∑ a : A, uv.1 a • (a : E) - ∑ b : B, uv.2 b • (b : E),
                 ∑ a : A, uv.1 a,
                 ∑ b : B, uv.2 b)
              map_add' := fun x y => by
                ext <;> simp [add_smul, Finset.sum_add_distrib, sub_add_sub_comm]
              map_smul' := fun r x => by
                ext <;> simp [mul_smul, Finset.smul_sum, Finset.mul_sum, smul_sub] }
          have hfin_dom : Module.finrank ℝ ((A → ℝ) × (B → ℝ)) = A.card + B.card := by
            simp [Module.finrank_prod, Fintype.card_coe]
          have hfin_cod : Module.finrank ℝ (E × ℝ × ℝ) = Module.finrank ℝ E + 2 := by
            simp [Module.finrank_prod]
          have hker_ne : LinearMap.ker Φ ≠ ⊥ := by
            intro hbot
            have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.mp hbot
            have hle_rank := LinearMap.finrank_le_finrank_of_injective hinj
            omega
          obtain ⟨⟨u, v⟩, huv_ker, huv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
          have hker_eq : (∑ a : A, u a • (a : E) = ∑ b : B, v b • (b : E)) ∧
              (∑ a : A, u a = 0) ∧ (∑ b : B, v b = 0) := by
            have h0 := LinearMap.mem_ker.mp huv_ker
            have h1 : ∑ a : A, u a • (a : E) - ∑ b : B, v b • (b : E) = 0 := congrArg Prod.fst h0
            have h2 : ∑ a : A, u a = 0 := congrArg (fun p => p.2.1) h0
            have h3 : ∑ b : B, v b = 0 := congrArg (fun p => p.2.2) h0
            exact ⟨sub_eq_zero.mp h1, h2, h3⟩
          -- There exists at least one strictly positive entry in u or v
          have hex_pos : (∃ a : A, 0 < u a) ∨ (∃ b : B, 0 < v b) := by
            by_contra hnp
            push Not at hnp
            obtain ⟨hu_le, hv_le⟩ := hnp
            have hu0 : ∀ a : A, u a = 0 := fun a => by
              have hsum0 : ∑ x : A, (-u x) = 0 := by
                rw [Finset.sum_neg_distrib, hker_eq.2.1, neg_zero]
              have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => neg_nonneg.mpr (hu_le x))).mp hsum0 a (Finset.mem_univ a)
              linarith
            have hv0 : ∀ b : B, v b = 0 := fun b => by
              have hsum0 : ∑ x : B, (-v x) = 0 := by
                rw [Finset.sum_neg_distrib, hker_eq.2.2, neg_zero]
              have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => neg_nonneg.mpr (hv_le x))).mp hsum0 b (Finset.mem_univ b)
              linarith
            apply huv_ne
            ext x
            · exact hu0 x
            · exact hv0 x
          let ratiosA := (Finset.univ.filter fun a : A => 0 < u a).image fun a => wA a.1 / u a
          let ratiosB := (Finset.univ.filter fun b : B => 0 < v b).image fun b => wB b.1 / v b
          let ratios := ratiosA ∪ ratiosB
          have hratios_ne : ratios.Nonempty := by
            rcases hex_pos with ⟨a, ha⟩ | ⟨b, hb⟩
            · exact ⟨wA a.1 / u a, Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩, rfl⟩)⟩
            · exact ⟨wB b.1 / v b, Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩)⟩
          let t := ratios.min' hratios_ne
          have ht_le_A : ∀ a : A, 0 < u a → t ≤ wA a.1 / u a := fun a ha =>
            Finset.min'_le _ _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩, rfl⟩))
          have ht_le_B : ∀ b : B, 0 < v b → t ≤ wB b.1 / v b := fun b hb =>
            Finset.min'_le _ _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩))
          have ht_pos : 0 < t := by
            change 0 < ratios.min' hratios_ne
            have hmem := Finset.min'_mem ratios hratios_ne
            rcases Finset.mem_union.mp hmem with hA | hB
            · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hA
              rw [← heq]; exact div_pos (hwA_pos a.1 a.2) (Finset.mem_filter.mp ha).2
            · obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hB
              rw [← heq]; exact div_pos (hwB_pos b.1 b.2) (Finset.mem_filter.mp hb).2
          let wA' : E → ℝ := fun x => if hx : x ∈ A then wA x - t * u ⟨x, hx⟩ else 0
          let wB' : E → ℝ := fun x => if hx : x ∈ B then wB x - t * v ⟨x, hx⟩ else 0
          have hwA'_nn : ∀ a ∈ A, 0 ≤ wA' a := by
            intro a ha
            simp only [wA', dif_pos ha]
            by_cases hu : 0 < u ⟨a, ha⟩
            · have := (le_div_iff₀ hu).mp (ht_le_A ⟨a, ha⟩ hu); linarith
            · nlinarith [hwA_pos a ha]
          have hwB'_nn : ∀ b ∈ B, 0 ≤ wB' b := by
            intro b hb
            simp only [wB', dif_pos hb]
            by_cases hv : 0 < v ⟨b, hb⟩
            · have := (le_div_iff₀ hv).mp (ht_le_B ⟨b, hb⟩ hv); linarith
            · nlinarith [hwB_pos b hb]
          have hwA'_sum : ∑ a ∈ A, wA' a = 1 := by
            calc ∑ a ∈ A, wA' a
              _ = ∑ a : A, (wA a.1 - t * u a) := by
                  rw [← Finset.sum_coe_sort A]
                  exact Finset.sum_congr rfl fun a _ => dif_pos a.2
              _ = ∑ a : A, wA a.1 - t * ∑ a : A, u a := by
                  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              _ = ∑ a ∈ A, wA a - 0 := by rw [hker_eq.2.1, mul_zero, Finset.sum_coe_sort A wA]
              _ = 1 := by linarith
          have hwB'_sum : ∑ b ∈ B, wB' b = 1 := by
            calc ∑ b ∈ B, wB' b
              _ = ∑ b : B, (wB b.1 - t * v b) := by
                  rw [← Finset.sum_coe_sort B]
                  exact Finset.sum_congr rfl fun b _ => dif_pos b.2
              _ = ∑ b : B, wB b.1 - t * ∑ b : B, v b := by
                  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              _ = ∑ b ∈ B, wB b - 0 := by rw [hker_eq.2.2, mul_zero, Finset.sum_coe_sort B wB]
              _ = 1 := by linarith
          have hcm_eq : ∑ a ∈ A, wA' a • a = ∑ b ∈ B, wB' b • b := by
            have h1 : ∑ a ∈ A, wA' a • a = p - t • ∑ a : A, u a • (a : E) := by
              calc ∑ a ∈ A, wA' a • a
                _ = ∑ a : A, (wA a.1 - t * u a) • (a : E) := by
                    rw [← Finset.sum_coe_sort A (fun x => wA' x • x)]
                    exact Finset.sum_congr rfl fun a _ => by simp [wA', a.2]
                _ = ∑ a : A, wA a.1 • (a : E) - ∑ a : A, (t * u a) • (a : E) := by
                    simp only [sub_smul, Finset.sum_sub_distrib]
                _ = p - t • ∑ a : A, u a • (a : E) := by
                    rw [Finset.sum_coe_sort A (fun x => wA x • x), hwA_cm, Finset.smul_sum]
                    congr 1; exact Finset.sum_congr rfl fun a _ => mul_smul _ _ _
            have h2 : ∑ b ∈ B, wB' b • b = p - t • ∑ b : B, v b • (b : E) := by
              calc ∑ b ∈ B, wB' b • b
                _ = ∑ b : B, (wB b.1 - t * v b) • (b : E) := by
                    rw [← Finset.sum_coe_sort B (fun x => wB' x • x)]
                    exact Finset.sum_congr rfl fun b _ => by simp [wB', b.2]
                _ = ∑ b : B, wB b.1 • (b : E) - ∑ b : B, (t * v b) • (b : E) := by
                    simp only [sub_smul, Finset.sum_sub_distrib]
                _ = p - t • ∑ b : B, v b • (b : E) := by
                    rw [Finset.sum_coe_sort B (fun x => wB x • x), hwB_cm, Finset.smul_sum]
                    congr 1; exact Finset.sum_congr rfl fun b _ => mul_smul _ _ _
            rw [h1, h2, hker_eq.1]
          let p' := ∑ a ∈ A, wA' a • a
          have hmem := Finset.min'_mem ratios hratios_ne
          rcases Finset.mem_union.mp hmem with hA | hB
          · obtain ⟨a0, ha0f, heq⟩ := Finset.mem_image.mp hA
            have hu_pos : 0 < u a0 := (Finset.mem_filter.mp ha0f).2
            have hw0 : wA' a0.1 = 0 := by
              simp only [wA', dif_pos a0.2]
              have ht_eq : t = wA a0.1 / u a0 := heq.symm
              rw [ht_eq, div_mul_cancel₀ _ hu_pos.ne', sub_self]
            have hlt : (A.erase a0.1).card + B.card < n := by
              rw [← hn, Finset.card_erase_of_mem a0.2]
              have := Finset.card_pos.mpr ⟨a0.1, a0.2⟩; omega
            have hp'A : p' ∈ convexHull ℝ ((A.erase a0.1 : Finset E) : Set E) := by
              rw [Finset.convexHull_eq]
              have hsum1 : ∑ x ∈ A.erase a0.1, wA' x = 1 := by
                rw [Finset.sum_erase_eq_sub a0.2, hw0, sub_zero]; exact hwA'_sum
              refine ⟨wA', fun x hx => hwA'_nn x (Finset.mem_of_mem_erase hx), hsum1, ?_⟩
              rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
              simp only [id_eq]
              rw [Finset.sum_erase_eq_sub a0.2, hw0, zero_smul, sub_zero]
            have hp'B : p' ∈ convexHull ℝ (B : Set E) := by
              rw [Finset.convexHull_eq]
              refine ⟨wB', hwB'_nn, hwB'_sum, ?_⟩
              rw [Finset.centerMass_eq_of_sum_1 _ _ hwB'_sum]
              simpa [p'] using hcm_eq.symm
            obtain ⟨A', hA', B', hB', hcard', hne'⟩ :=
              ih _ hlt (A.erase a0.1) B ⟨p', hp'A, hp'B⟩ rfl
            exact ⟨A', hA'.trans (Finset.erase_subset a0.1 A), B', hB', hcard', hne'⟩
          · obtain ⟨b0, hb0f, heq⟩ := Finset.mem_image.mp hB
            have hv_pos : 0 < v b0 := (Finset.mem_filter.mp hb0f).2
            have hw0 : wB' b0.1 = 0 := by
              simp only [wB', dif_pos b0.2]
              have ht_eq : t = wB b0.1 / v b0 := heq.symm
              rw [ht_eq, div_mul_cancel₀ _ hv_pos.ne', sub_self]
            have hlt : A.card + (B.erase b0.1).card < n := by
              rw [← hn, Finset.card_erase_of_mem b0.2]
              have := Finset.card_pos.mpr ⟨b0.1, b0.2⟩; omega
            have hp'A : p' ∈ convexHull ℝ (A : Set E) := by
              rw [Finset.convexHull_eq]
              refine ⟨wA', hwA'_nn, hwA'_sum, ?_⟩
              rw [Finset.centerMass_eq_of_sum_1 _ _ hwA'_sum]; rfl
            have hp'B : p' ∈ convexHull ℝ ((B.erase b0.1 : Finset E) : Set E) := by
              rw [Finset.convexHull_eq]
              have hsum1 : ∑ x ∈ B.erase b0.1, wB' x = 1 := by
                rw [Finset.sum_erase_eq_sub b0.2, hw0, sub_zero]; exact hwB'_sum
              refine ⟨wB', fun x hx => hwB'_nn x (Finset.mem_of_mem_erase hx), hsum1, ?_⟩
              rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
              simp only [id_eq]
              rw [Finset.sum_erase_eq_sub b0.2, hw0, zero_smul, sub_zero]
              exact hcm_eq.symm
            obtain ⟨A', hA', B', hB', hcard', hne'⟩ :=
              ih _ hlt A (B.erase b0.1) ⟨p', hp'A, hp'B⟩ rfl
            exact ⟨A', hA', B', hB'.trans (Finset.erase_subset b0.1 B), hcard', hne'⟩

/- ### Part 7: 2D Discrete Ham Sandwich Theorem -/

noncomputable def projDir (θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.cos θ * p.1 + Real.sin θ * p.2

noncomputable def medianDir (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : r + 1 ≤ A.card) (θ : ℝ) : ℝ :=
  have hne : (A.powersetCard (r + 1)).Nonempty := by
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hA
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, hScard⟩⟩
  (A.powersetCard (r + 1)).inf' hne fun S =>
    if hS : S.Nonempty then S.sup' hS (fun a => projDir θ a) else 0

lemma medianDir_continuous (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : r + 1 ≤ A.card) :
    Continuous (medianDir A r hA) := by
  have hne : (A.powersetCard (r + 1)).Nonempty := by
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hA
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, hScard⟩⟩
  have heq : medianDir A r hA =
      (A.powersetCard (r + 1)).inf' hne fun S =>
        if hS : S.Nonempty then S.sup' hS (fun a θ => projDir θ a) else fun _ => 0 := by
    ext θ
    unfold medianDir
    simp only [Finset.inf'_apply]
    congr 1
    ext S
    split_ifs with hS
    · simp only [Finset.sup'_apply]
    · rfl
  rw [heq]
  apply Continuous.finset_inf'
  intro S _
  split_ifs with hS
  · apply Continuous.finset_sup'
    intro a _
    unfold projDir
    exact (Real.continuous_cos.mul continuous_const).add (Real.continuous_sin.mul continuous_const)
  · exact continuous_const

lemma medianDir_le_count (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : r + 1 ≤ A.card) (θ : ℝ) :
    r + 1 ≤ (A.filter fun a => projDir θ a ≤ medianDir A r hA θ).card := by
  have hne : (A.powersetCard (r + 1)).Nonempty := by
    obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hA
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, hScard⟩⟩
  let g : Finset (ℝ × ℝ) → ℝ := fun S =>
    if hS : S.Nonempty then S.sup' hS (fun a => projDir θ a) else 0
  obtain ⟨S, hSm, hSeq⟩ := Finset.exists_mem_eq_inf' hne g
  obtain ⟨hSA, hScard⟩ := Finset.mem_powersetCard.mp hSm
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsub : S ⊆ A.filter fun a => projDir θ a ≤ medianDir A r hA θ := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨hSA ha, ?_⟩
    change projDir θ a ≤ (A.powersetCard (r + 1)).inf' hne g
    rw [hSeq]
    dsimp [g]
    rw [dif_pos hSne]
    exact Finset.le_sup' (fun x => projDir θ x) ha
  exact hScard.symm.le.trans (Finset.card_le_card hsub)

lemma medianDir_lt_count (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : r + 1 ≤ A.card) (θ : ℝ) :
    (A.filter fun a => projDir θ a < medianDir A r hA θ).card ≤ r := by
  by_contra! hgt
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
    (show r + 1 ≤ (A.filter fun a => projDir θ a < medianDir A r hA θ).card by omega)
  have hSA : S ⊆ A := hSsub.trans (Finset.filter_subset _ _)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hle : medianDir A r hA θ ≤ S.sup' hSne (fun a => projDir θ a) := by
    unfold medianDir
    have hmem : S ∈ A.powersetCard (r + 1) := Finset.mem_powersetCard.mpr ⟨hSA, hScard⟩
    have h0 := Finset.inf'_le (f := fun T => if hT : T.Nonempty then T.sup' hT (fun a => projDir θ a) else 0) hmem
    rwa [dif_pos hSne] at h0
  obtain ⟨a, haS, haeq⟩ := Finset.exists_mem_eq_sup' hSne (fun a => projDir θ a)
  have halt : projDir θ a < medianDir A r hA θ := (Finset.mem_filter.mp (hSsub haS)).2
  linarith

lemma medianDir_ge_count (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : A.card = 2 * r + 1) (θ : ℝ) :
    r + 1 ≤ (A.filter fun a => medianDir A r (by omega) θ ≤ projDir θ a).card := by
  have hlt := medianDir_lt_count A r (by omega) θ
  have hpart : (A.filter fun a => projDir θ a < medianDir A r (by omega) θ).card +
      (A.filter fun a => medianDir A r (by omega) θ ≤ projDir θ a).card = A.card := by
    have : (A.filter fun a => medianDir A r (by omega) θ ≤ projDir θ a) =
        (A.filter fun a => ¬ (projDir θ a < medianDir A r (by omega) θ)) := by
      ext a; simp [not_lt]
    rw [this]; exact Finset.card_filter_add_card_filter_not _
  omega

lemma medianDir_add_pi (A : Finset (ℝ × ℝ)) (r : ℕ) (hA : A.card = 2 * r + 1) (θ : ℝ) :
    medianDir A r (by omega) (θ + Real.pi) = - medianDir A r (by omega) θ := by
  have hproj : ∀ p, projDir (θ + Real.pi) p = - projDir θ p := by
    intro p; unfold projDir
    rw [Real.cos_add_pi, Real.sin_add_pi]; ring
  set v := medianDir A r (by omega) θ
  set w := medianDir A r (by omega) (θ + Real.pi)
  have h1 : w ≤ -v := by
    have hge := medianDir_ge_count A r hA θ
    have hge' : r + 1 ≤ (A.filter fun a => projDir (θ + Real.pi) a ≤ -v).card := by
      convert hge using 2; ext a; simp [v, hproj]
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hge'
    have hSA : S ⊆ A := hSsub.trans (Finset.filter_subset _ _)
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hle : w ≤ S.sup' hSne (fun a => projDir (θ + Real.pi) a) := by
      dsimp only [w]; unfold medianDir
      have hmem : S ∈ A.powersetCard (r + 1) := Finset.mem_powersetCard.mpr ⟨hSA, hScard⟩
      have h0 := Finset.inf'_le (f := fun T => if hT : T.Nonempty then T.sup' hT (fun a => projDir (θ + Real.pi) a) else 0) hmem
      rwa [dif_pos hSne] at h0
    have hsup : S.sup' hSne (fun a => projDir (θ + Real.pi) a) ≤ -v :=
      Finset.sup'_le _ _ fun a ha => (Finset.mem_filter.mp (hSsub ha)).2
    exact hle.trans hsup
  have h2 : -v ≤ w := by
    by_contra! hlt
    let U := A.filter fun a => projDir θ a ≤ v
    let V := A.filter fun a => projDir (θ + Real.pi) a ≤ w
    have hU : r + 1 ≤ U.card := medianDir_le_count A r (by omega) θ
    have hV : r + 1 ≤ V.card := medianDir_le_count A r (by omega) (θ + Real.pi)
    have hdisj : Disjoint U V := by
      rw [Finset.disjoint_left]
      intro a haU haV
      have hUm := (Finset.mem_filter.mp haU).2
      have hVm := (Finset.mem_filter.mp haV).2
      rw [hproj] at hVm
      linarith
    have hcard : U.card + V.card ≤ A.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  exact le_antisymm h1 h2

lemma ham_sandwich_2d_odd (A B : Finset (ℝ × ℝ)) (r s : ℕ)
    (hA : A.card = 2 * r + 1) (hB : B.card = 2 * s + 1) :
    ∃ (θ c : ℝ),
      r + 1 ≤ (A.filter fun a => projDir θ a ≤ c).card ∧
      r + 1 ≤ (A.filter fun a => c ≤ projDir θ a).card ∧
      s + 1 ≤ (B.filter fun b => projDir θ b ≤ c).card ∧
      s + 1 ≤ (B.filter fun b => c ≤ projDir θ b).card := by
  let F : ℝ → ℝ := fun θ => medianDir B s (by omega) θ - medianDir A r (by omega) θ
  have hcont : Continuous F := (medianDir_continuous B s (by omega)).sub (medianDir_continuous A r (by omega))
  have hpi : F Real.pi = - F 0 := by
    dsimp [F]
    have h1 := medianDir_add_pi A r hA 0
    have h2 := medianDir_add_pi B s hB 0
    simp only [zero_add] at h1 h2
    linarith
  have hzero : ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, F θ = 0 := by
    by_cases h0 : 0 ≤ F 0
    · have hmem : (0 : ℝ) ∈ Set.Icc (F Real.pi) (F 0) := ⟨by linarith, h0⟩
      exact intermediate_value_Icc' Real.pi_pos.le hcont.continuousOn hmem
    · have hmem : (0 : ℝ) ∈ Set.Icc (F 0) (F Real.pi) := ⟨by linarith, by linarith⟩
      exact intermediate_value_Icc Real.pi_pos.le hcont.continuousOn hmem
  obtain ⟨θ, _, hFθ⟩ := hzero
  have heq : medianDir B s (by omega) θ = medianDir A r (by omega) θ := sub_eq_zero.mp hFθ
  refine ⟨θ, medianDir A r (by omega) θ,
    medianDir_le_count A r (by omega) θ,
    medianDir_ge_count A r hA θ, ?_, ?_⟩
  · rw [← heq]; exact medianDir_le_count B s (by omega) θ
  · rw [← heq]; exact medianDir_ge_count B s hB θ

lemma ham_sandwich_2d (A B : Finset (ℝ × ℝ)) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (θ c : ℝ),
      A.card / 2 ≤ (A.filter fun a => projDir θ a ≤ c).card ∧
      A.card / 2 ≤ (A.filter fun a => c ≤ projDir θ a).card ∧
      B.card / 2 ≤ (B.filter fun b => projDir θ b ≤ c).card ∧
      B.card / 2 ≤ (B.filter fun b => c ≤ projDir θ b).card := by
  have shrink (S : Finset (ℝ × ℝ)) (hS : S.Nonempty) :
      ∃ S' ⊆ S, ∃ r : ℕ, S'.card = 2 * r + 1 ∧ S.card / 2 ≤ r + 1 := by
    let r := (S.card - 1) / 2
    have hle : 2 * r + 1 ≤ S.card := by
      have := Finset.card_pos.mpr hS; omega
    obtain ⟨S', hS', hcard⟩ := Finset.exists_subset_card_eq hle
    exact ⟨S', hS', r, hcard, by omega⟩
  obtain ⟨A', hA', r, hA'card, hr⟩ := shrink A hA
  obtain ⟨B', hB', s, hB'card, hs⟩ := shrink B hB
  obtain ⟨θ, c, h1, h2, h3, h4⟩ := ham_sandwich_2d_odd A' B' r s hA'card hB'card
  refine ⟨θ, c,
    hr.trans (h1.trans (Finset.card_le_card (Finset.filter_subset_filter _ hA'))),
    hr.trans (h2.trans (Finset.card_le_card (Finset.filter_subset_filter _ hA'))),
    hs.trans (h3.trans (Finset.card_le_card (Finset.filter_subset_filter _ hB'))),
    hs.trans (h4.trans (Finset.card_le_card (Finset.filter_subset_filter _ hB')))⟩

/- ### Part 8: Generic Coordinate Change in ℝ^3 -/

def orient2 (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def NoThreeCollinear2 (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → orient2 a b c ≠ 0

lemma orient2_swap23 (a b c : ℝ × ℝ) : orient2 a c b = - orient2 a b c := by
  unfold orient2; ring

lemma orient2_swap12 (a b c : ℝ × ℝ) : orient2 b a c = - orient2 a b c := by
  unfold orient2; ring

lemma orient2_cyc (a b c : ℝ × ℝ) : orient2 b c a = orient2 a b c := by
  unfold orient2; ring

lemma orient2_cyc2 (a b c : ℝ × ℝ) : orient2 c a b = orient2 a b c := by
  unfold orient2; ring

lemma orient2_rev (a b c : ℝ × ℝ) : orient2 c b a = - orient2 a b c := by
  unfold orient2; ring

lemma orient2_self_right (a b : ℝ × ℝ) : orient2 a b b = 0 := by
  unfold orient2; ring

lemma projDir_add_pi (θ : ℝ) (p : ℝ × ℝ) : projDir (θ + Real.pi) p = - projDir θ p := by
  unfold projDir; rw [Real.cos_add_pi, Real.sin_add_pi]; ring

lemma affineIndependent_comp_linearMap {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {f : E →ₗ[ℝ] F} (hf : Function.Injective f)
    {p : ι → E} (hp : AffineIndependent ℝ p) : AffineIndependent ℝ (f ∘ p) := by
  rcases isEmpty_or_nonempty ι with h | hne
  · exact affineIndependent_of_subsingleton _ _
  · obtain ⟨i₀⟩ := hne
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ i₀] at hp ⊢
    have h1 := hp.map' f (LinearMap.ker_eq_bot.mpr hf)
    have heq : (f ∘ fun i : {i // i ≠ i₀} => p i.1 -ᵥ p i₀) =
        fun i : {i // i ≠ i₀} => (f ∘ p) i.1 -ᵥ (f ∘ p) i₀ := by
      ext i; simp only [Function.comp_apply, vsub_eq_sub, map_sub]
    rwa [heq] at h1

lemma orient2_eq_slope_diff {a b c : ℝ × ℝ} (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    orient2 a b c = (b.1 - a.1) * (c.1 - b.1) * (slope2 b c - slope2 a b) := by
  have h1 : b.1 - a.1 ≠ 0 := (sub_pos.mpr hab).ne'
  have h2 : c.1 - b.1 ≠ 0 := (sub_pos.mpr hbc).ne'
  unfold orient2 slope2
  field_simp [h1, h2]
  ring

lemma finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β) (X : Finset α) (Z : Finset β)
    (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

lemma convex_subset_lifts {k d n : ℕ} (L : (ℝ^d) →ₗ[ℝ] (ℝ^k)) (X : Finset (ℝ^d))
    (hL : Set.InjOn L (X : Set (ℝ^d))) (hX : Erdos651.HasConvexSubset n (X.image L)) :
    Erdos651.HasConvexSubset n X := by
  obtain ⟨Z, hZ, hZn, hconv⟩ := hX
  obtain ⟨Y, hYX, hYZ, hcard⟩ := finite_image_pullback L X Z hZ hL
  refine ⟨Y, hYX, hcard.trans hZn, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hconv ⊢
  intro y hy h
  have hLy : L y ∈ (Z : Set (ℝ^k)) := by
    rw [← hYZ]; exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  apply hconv (L y) hLy
  have himage : L '' ((Y : Set (ℝ^d)) \ {y}) ⊆ (Z : Set (ℝ^k)) \ {L y} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hYZ]; exact Finset.mem_image.mpr ⟨a, ha.1, rfl⟩
    · intro he; exact ha.2 (hL (hYX ha.1) (hYX hy) he)
  apply convexHull_mono himage
  rw [← L.image_convexHull]
  exact ⟨y, h, rfl⟩

lemma generic_projection_32 (X : Finset (ℝ^3)) (hX : Erdos651.IsInGeneralPosition X) :
    ∃ L : (ℝ^3) →ₗ[ℝ] (ℝ^2),
      Set.InjOn L (X : Set (ℝ^3)) ∧ Erdos651.IsInGeneralPosition (X.image L) ∧
      ∃ v₀ : ℝ^3, v₀ ≠ 0 ∧ LinearMap.ker L = ℝ ∙ v₀ := by
  let T := X.powerset.filter fun Y => Y.card ≤ 3
  let W (Y : T) : Submodule ℝ (ℝ^3) := vectorSpan ℝ (Y.val : Set (ℝ^3))
  have hW (Y : T) : W Y ≠ ⊤ := by
    have hsmall : Y.val.card ≤ 3 := (Finset.mem_filter.mp Y.prop).2
    have hdim : Module.finrank ℝ (W Y) ≤ 2 := by
      rcases Y.val.eq_empty_or_nonempty with hY | hY
      · change Module.finrank ℝ (vectorSpan ℝ (Y.val : Set (ℝ^3))) ≤ 2
        rw [hY, Finset.coe_empty, vectorSpan_empty, finrank_bot]; exact Nat.zero_le _
      · have hcard : Y.val.card = (Y.val.card - 1) + 1 := by
          have := Finset.card_pos.mpr hY; omega
        have h := finrank_vectorSpan_image_finset_le ℝ id Y.val hcard
        rw [Finset.image_id] at h
        have h' : Module.finrank ℝ (W Y) ≤ Y.val.card - 1 := h
        omega
    intro htop
    rw [htop, finrank_top, finrank_euclideanSpace_fin] at hdim
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  have hv₀ : v ≠ 0 := by
    let e : T := ⟨∅, by simp [T]⟩
    intro h; exact hv e (h.symm ▸ (W e).zero_mem)
  let U := ℝ ∙ v
  have hdim : Module.finrank ℝ ((ℝ^3) ⧸ U) = Module.finrank ℝ (ℝ^2) := by
    have h := U.finrank_quotient_add_finrank
    rw [show Module.finrank ℝ U = 1 from finrank_span_singleton hv₀,
      finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]; omega
  let e := LinearEquiv.ofFinrankEq _ _ hdim
  let L : (ℝ^3) →ₗ[ℝ] (ℝ^2) := e.toLinearMap.comp U.mkQ
  have hker_eq : LinearMap.ker L = U := by
    ext u
    simp only [LinearMap.mem_ker, L, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      EmbeddingLike.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hker (Y : Finset (ℝ^3)) (hYX : Y ⊆ X) (hY : Y.card ≤ 3) :
      Disjoint (vectorSpan ℝ (Y : Set (ℝ^3))) (LinearMap.ker L) := by
    let i : T := ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYX, hY⟩⟩
    rw [Submodule.disjoint_def]
    intro u hu hlu
    rw [hker_eq] at hlu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hlu
    by_cases ha₀ : a = 0
    · simpa [ha₀] using ha.symm
    · rw [← ha] at hu
      exact (hv i (((W i).smul_mem_iff ha₀).mp hu)).elim
  have hL : Set.InjOn L (X : Set (ℝ^3)) := by
    intro a ha b hb hab
    let Y : Finset (ℝ^3) := {a, b}
    have hYX : Y ⊆ X := by
      intro x hx; simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hY : Y.card ≤ 3 := Finset.card_le_two.trans (by omega)
    have hm : a - b ∈ vectorSpan ℝ (Y : Set (ℝ^3)) :=
      vsub_mem_vectorSpan ℝ (show a ∈ (Y : Set _) by simp [Y]) (show b ∈ (Y : Set _) by simp [Y])
    have hd : a - b ∈ LinearMap.ker L := LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp (hker Y hYX hY) _ hm hd)
  refine ⟨L, hL, fun Z hZ hcard => ?_, v, hv₀, hker_eq⟩
  obtain ⟨Y, hYX, hYZ, hcardY⟩ := finite_image_pullback L X Z hZ hL
  have hYcard : Y.card ≤ 3 := hcardY.trans_le hcard
  let p : ↥(Y : Set (ℝ^3)) → ℝ^3 := Subtype.val
  have hrange : Set.range (L ∘ p) = (Z : Set (ℝ^2)) := by
    rw [Set.range_comp, Subtype.range_coe, ← Finset.coe_image, hYZ]
  suffices h : AffineIndependent ℝ (L ∘ p) by rw [← hrange]; exact h.range
  rcases isEmpty_or_nonempty ↥(Y : Set (ℝ^3)) with hEmpty | hNonempty
  · let _ := hEmpty; exact affineIndependent_of_subsingleton _ (L ∘ p)
  · obtain ⟨y⟩ := hNonempty
    have hind : AffineIndependent ℝ p := hX Y hYX (by omega)
    have hd := (affineIndependent_iff_linearIndependent_vsub ℝ p y).mp hind
    apply (affineIndependent_iff_linearIndependent_vsub ℝ (L ∘ p) y).mpr
    have hs : Submodule.span ℝ (Set.range (fun i : {i // i ≠ y} => p i -ᵥ p y)) ≤
        vectorSpan ℝ (Y : Set (ℝ^3)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩; exact vsub_mem_vectorSpan ℝ i.val.prop y.prop
    have hm := hd.map ((hker Y hYX hYcard).mono_left hs)
    change LinearIndependent ℝ (fun i : {i // i ≠ y} => L (p i - p y)) at hm
    simpa only [Function.comp_apply, vsub_eq_sub, map_sub] using hm

lemma planar_coordinates (X : Finset (ℝ^2)) :
    ∃ x y : (ℝ^2) →ₗ[ℝ] ℝ, Set.InjOn x (X : Set (ℝ^2)) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  let bad := (X ×ˢ X).image fun uv : (ℝ^2) × (ℝ^2) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ^2) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext; intro i; fin_cases i
    · change p 0 = q 0; rw [hy] at hx; exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso; apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

def proj2 : (ℝ^3) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p 0, p 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma generic_coord_change (X : Finset (ℝ^3)) (hX : Erdos651.IsInGeneralPosition X) :
    ∃ Φ : (ℝ^3) ≃ₗ[ℝ] (ℝ^3),
      let X' := X.image Φ
      X'.card = X.card ∧
      Erdos651.IsInGeneralPosition X' ∧
      (∀ n, Erdos651.HasConvexSubset n X' → Erdos651.HasConvexSubset n X) ∧
      Set.InjOn proj2 (X' : Set (ℝ^3)) ∧
      Set.InjOn (fun p : ℝ^3 => p 0) (X' : Set (ℝ^3)) ∧
      NoThreeCollinear2 (X'.image proj2) := by
  obtain ⟨L, hLinj, hLgp, v₀, hv₀, hkerL⟩ := generic_projection_32 X hX
  obtain ⟨x, y, hxinj, hjoin⟩ := planar_coordinates (X.image L)
  let f0 : (ℝ^3) →ₗ[ℝ] ℝ := x.comp L
  let f1 : (ℝ^3) →ₗ[ℝ] ℝ := y.comp L
  let f2 : (ℝ^3) →ₗ[ℝ] ℝ := (innerSL ℝ v₀).toLinearMap
  have hf2v0 : f2 v₀ ≠ 0 := by
    change inner ℝ v₀ v₀ ≠ 0
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv₀)
  let Ψ : (ℝ^3) →ₗ[ℝ] (ℝ^3) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap.comp
      (LinearMap.pi ![f0, f1, f2])
  have hΨ0 : ∀ u, (Ψ u) 0 = f0 u := fun u => rfl
  have hΨ1 : ∀ u, (Ψ u) 1 = f1 u := fun u => rfl
  have hΨ2 : ∀ u, (Ψ u) 2 = f2 u := fun u => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : x (L u) = x 0 := by
      have := congrArg (fun p : ℝ^3 => p 0) hu
      simpa [hΨ0, f0] using this
    have h1 : y (L u) = y 0 := by
      have := congrArg (fun p : ℝ^3 => p 1) hu
      simpa [hΨ1, f1] using this
    have hLu : L u = 0 := hjoin (L u) 0 h0 h1
    have hu_ker : u ∈ ℝ ∙ v₀ := hkerL ▸ LinearMap.mem_ker.mpr hLu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu_ker
    have h2 : c * f2 v₀ = 0 := by
      have := congrArg (fun p : ℝ^3 => p 2) hu
      simpa [hΨ2, map_smul] using this
    rcases mul_eq_zero.mp h2 with rfl | hbad
    · simp
    · exact absurd hbad hf2v0
  let Φ : (ℝ^3) ≃ₗ[ℝ] (ℝ^3) :=
    LinearEquiv.ofBijective Ψ ⟨hΨinj, LinearMap.injective_iff_surjective.mp hΨinj⟩
  have hΦeq : ∀ u, Φ u = Ψ u := fun _ => rfl
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injective X Φ.injective
  · intro Z hZ hZcard
    obtain ⟨Y, hYX, hYZ, hYcard⟩ := finite_image_pullback Φ X Z hZ Φ.injective.injOn
    have hind : AffineIndependent ℝ (Subtype.val : ↥(Y : Set (ℝ^3)) → ℝ^3) :=
      hX Y hYX (by omega)
    have hrange : Set.range (Φ.toLinearMap ∘ (Subtype.val : ↥(Y : Set (ℝ^3)) → ℝ^3)) = (Z : Set (ℝ^3)) := by
      rw [Set.range_comp, Subtype.range_coe, ← Finset.coe_image]; exact congrArg _ hYZ
    rw [← hrange]
    exact (affineIndependent_comp_linearMap Φ.injective hind).range
  · intro n hn
    exact convex_subset_lifts Φ.toLinearMap X Φ.injective.injOn hn
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have h0 : x (L u) = x (L v) := congrArg Prod.fst hab
    have h1 : y (L u) = y (L v) := congrArg Prod.snd hab
    have hLuv : L u = L v := hjoin (L u) (L v) h0 h1
    rw [hLinj hu hv hLuv]
  · intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have h0 : x (L u) = x (L v) := hab
    have hLuv : L u = L v := hxinj (Finset.mem_image_of_mem L hu) (Finset.mem_image_of_mem L hv) h0
    rw [hLinj hu hv hLuv]
  · intro p hp q hq r hr hpq hqr hpr hori
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    have hne1 : L a ≠ L b := fun h => hpq (by
      change (x (L a), y (L a)) = (x (L b), y (L b)); rw [h])
    have hne2 : L b ≠ L c := fun h => hqr (by
      change (x (L b), y (L b)) = (x (L c), y (L c)); rw [h])
    have hne3 : L a ≠ L c := fun h => hpr (by
      change (x (L a), y (L a)) = (x (L c), y (L c)); rw [h])
    let Z : Finset (ℝ^2) := {L a, L b, L c}
    have hZsub : Z ⊆ X.image L := by
      intro w hw; simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> exact Finset.mem_image_of_mem L ‹_›
    have hZcard : Z.card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)
    have hZind : AffineIndependent ℝ (Subtype.val : ↥(Z : Set (ℝ^2)) → ℝ^2) :=
      hLgp Z hZsub hZcard
    let xy : (ℝ^2) →ₗ[ℝ] (ℝ × ℝ) := LinearMap.prod x y
    have hxy_inj : Function.Injective xy := fun u v huv =>
      hjoin u v (congrArg Prod.fst huv) (congrArg Prod.snd huv)
    let w : Fin 3 → ↥(Z : Set (ℝ^2)) :=
      ![⟨L a, by simp [Z]⟩, ⟨L b, by simp [Z]⟩, ⟨L c, by simp [Z]⟩]
    have hwinj : Function.Injective w := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [w]
    have hind3 : AffineIndependent ℝ (xy ∘ Subtype.val ∘ w) := by
      have h1 : AffineIndependent ℝ (Subtype.val ∘ w) := hZind.comp_embedding ⟨w, hwinj⟩
      exact affineIndependent_comp_linearMap hxy_inj h1
    have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ (xy ∘ Subtype.val ∘ w) 0).mp hind3
    let u1 : ℝ × ℝ := proj2 (Φ b) - proj2 (Φ a)
    let u2 : ℝ × ℝ := proj2 (Φ c) - proj2 (Φ a)
    have hu1_eq : (xy ∘ Subtype.val ∘ w) ⟨1, by decide⟩ -ᵥ (xy ∘ Subtype.val ∘ w) 0 = u1 := rfl
    have hu2_eq : (xy ∘ Subtype.val ∘ w) ⟨2, by decide⟩ -ᵥ (xy ∘ Subtype.val ∘ w) 0 = u2 := rfl
    have hdet : u1.1 * u2.2 - u1.2 * u2.1 = 0 := hori
    have hne_u1 : u1 ≠ 0 := by
      intro h0
      apply hpq
      exact (sub_eq_zero.mp h0).symm
    have hdep1 : u2.1 • u1 + (-u1.1) • u2 = 0 := by
      ext
      · simp; ring
      · simp; linarith [hdet]
    have hdep2 : u2.2 • u1 + (-u1.2) • u2 = 0 := by
      ext
      · simp; linarith [hdet]
      · simp; ring
    have hlin_zero (c1 c2 : ℝ) (heq : c1 • u1 + c2 • u2 = 0) : c1 = 0 ∧ c2 = 0 := by
      let g : {i : Fin 3 // i ≠ 0} → ℝ := fun i => if i.1 = 1 then c1 else c2
      have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • ((xy ∘ Subtype.val ∘ w) i.1 -ᵥ (xy ∘ Subtype.val ∘ w) 0) = 0 := by
        have huniv : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) =
            {⟨1, by decide⟩, ⟨2, by decide⟩} := by decide
        rw [huniv, Finset.sum_pair (by decide)]
        have hg1 : g ⟨1, by decide⟩ = c1 := rfl
        have hg2 : g ⟨2, by decide⟩ = c2 := rfl
        rw [hg1, hg2]
        change c1 • ((xy ∘ Subtype.val ∘ w) ⟨1, by decide⟩ -ᵥ (xy ∘ Subtype.val ∘ w) 0) +
          c2 • ((xy ∘ Subtype.val ∘ w) ⟨2, by decide⟩ -ᵥ (xy ∘ Subtype.val ∘ w) 0) = 0
        rw [hu1_eq, hu2_eq]
        exact heq
      have hall := Fintype.linearIndependent_iff.mp hlin g hsum
      exact ⟨by simpa [g] using hall ⟨1, by decide⟩, by simpa [g] using hall ⟨2, by decide⟩⟩
    have hc1 := hlin_zero u2.1 (-u1.1) hdep1
    have hc2 := hlin_zero u2.2 (-u1.2) hdep2
    apply hne_u1
    ext
    · change u1.1 = 0; linarith [hc1.2]
    · change u1.2 = 0; linarith [hc2.2]

/- ### Part 9: 2D Same-Type Lemma and Positive-Fraction Convex Clusters -/

lemma exists_median_1d {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.Nonempty) (f : α → ℝ) :
    ∃ m : ℝ, S.card / 2 ≤ (S.filter fun a => f a ≤ m).card ∧
      S.card / 2 ≤ (S.filter fun a => m ≤ f a).card := by
  let k := (S.card + 1) / 2
  have hkpos : 1 ≤ k := by have := Finset.card_pos.mpr hS; omega
  have hkle : k ≤ S.card := by omega
  have hne : (S.powersetCard k).Nonempty := by
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hkle
    exact ⟨T, Finset.mem_powersetCard.mpr ⟨hTS, hTcard⟩⟩
  let g : Finset α → ℝ := fun T => if hT : T.Nonempty then T.sup' hT f else 0
  let m := (S.powersetCard k).inf' hne g
  have hle : k ≤ (S.filter fun a => f a ≤ m).card := by
    obtain ⟨T, hTm, hTeq⟩ := Finset.exists_mem_eq_inf' hne g
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.mp hTm
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hsub : T ⊆ S.filter fun a => f a ≤ m := fun a ha => by
      refine Finset.mem_filter.mpr ⟨hTS ha, ?_⟩
      change f a ≤ (S.powersetCard k).inf' hne g
      rw [hTeq]; dsimp [g]; rw [dif_pos hTne]
      exact Finset.le_sup' f ha
    exact hTcard.symm.le.trans (Finset.card_le_card hsub)
  have hlt : (S.filter fun a => f a < m).card ≤ k - 1 := by
    by_contra! hgt
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (show k ≤ (S.filter fun a => f a < m).card by omega)
    have hTS : T ⊆ S := hTsub.trans (Finset.filter_subset _ _)
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have h0 := Finset.inf'_le (f := g) (Finset.mem_powersetCard.mpr ⟨hTS, hTcard⟩)
    dsimp [g] at h0; rw [dif_pos hTne] at h0
    obtain ⟨a, haT, haeq⟩ := Finset.exists_mem_eq_sup' hTne f
    have halt : f a < m := (Finset.mem_filter.mp (hTsub haT)).2
    linarith
  have hge : S.card - (k - 1) ≤ (S.filter fun a => m ≤ f a).card := by
    have hpart : (S.filter fun a => f a < m).card + (S.filter fun a => m ≤ f a).card = S.card := by
      have : (S.filter fun a => m ≤ f a) = (S.filter fun a => ¬ (f a < m)) := by ext a; simp [not_lt]
      rw [this]; exact Finset.card_filter_add_card_filter_not _
    omega
  exact ⟨m, by omega, by omega⟩

lemma card_on_line_le_two {S : Finset (ℝ × ℝ)} (hgp : NoThreeCollinear2 S)
    (a b c : ℝ) (hnonzero : a ≠ 0 ∨ b ≠ 0) :
    (S.filter fun p => a * p.1 + b * p.2 = c).card ≤ 2 := by
  by_contra! hgt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (S.filter fun p => a * p.1 + b * p.2 = c).card by omega)
  obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hp1]; omega : 0 < (T.erase p1).card)
  have hp2T : p2 ∈ T := Finset.mem_of_mem_erase hp2
  obtain ⟨p3, hp3⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hp2, Finset.card_erase_of_mem hp1]; omega : 0 < ((T.erase p1).erase p2).card)
  have h1T : p1 ∈ T := hp1
  have h2T : p2 ∈ T := hp2T
  have h3T : p3 ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp3)
  have hne12 : p1 ≠ p2 := (Finset.mem_erase.mp hp2).1.symm
  have hne23 : p2 ≠ p3 := (Finset.mem_erase.mp hp3).1.symm
  have hne13 : p1 ≠ p3 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hp3)).1.symm
  have hf1 := Finset.mem_filter.mp (hTsub h1T)
  have hf2 := Finset.mem_filter.mp (hTsub h2T)
  have hf3 := Finset.mem_filter.mp (hTsub h3T)
  have hori := hgp p1 hf1.1 p2 hf2.1 p3 hf3.1 hne12 hne23 hne13
  apply hori
  unfold orient2
  rcases hnonzero with ha | hb
  · apply mul_left_cancel₀ ha
    have h1 : a * (p2.1 - p1.1) = -b * (p2.2 - p1.2) := by linarith [hf1.2, hf2.2]
    have h2 : a * (p3.1 - p1.1) = -b * (p3.2 - p1.2) := by linarith [hf1.2, hf3.2]
    calc a * ((p2.1 - p1.1) * (p3.2 - p1.2) - (p2.2 - p1.2) * (p3.1 - p1.1))
      _ = (a * (p2.1 - p1.1)) * (p3.2 - p1.2) - (p2.2 - p1.2) * (a * (p3.1 - p1.1)) := by ring
      _ = (-b * (p2.2 - p1.2)) * (p3.2 - p1.2) - (p2.2 - p1.2) * (-b * (p3.2 - p1.2)) := by rw [h1, h2]
      _ = a * 0 := by ring
  · apply mul_left_cancel₀ hb
    have h1 : b * (p2.2 - p1.2) = -a * (p2.1 - p1.1) := by linarith [hf1.2, hf2.2]
    have h2 : b * (p3.2 - p1.2) = -a * (p3.1 - p1.1) := by linarith [hf1.2, hf3.2]
    calc b * ((p2.1 - p1.1) * (p3.2 - p1.2) - (p2.2 - p1.2) * (p3.1 - p1.1))
      _ = (p2.1 - p1.1) * (b * (p3.2 - p1.2)) - (b * (p2.2 - p1.2)) * (p3.1 - p1.1) := by ring
      _ = (p2.1 - p1.1) * (-a * (p3.1 - p1.1)) - (-a * (p2.1 - p1.1)) * (p3.1 - p1.1) := by rw [h1, h2]
      _ = b * 0 := by ring

lemma same_type_2d_triple (A B C : Finset (ℝ × ℝ))
    (hgp : NoThreeCollinear2 (A ∪ B ∪ C))
    (hA : 32 ≤ A.card) (hB : 32 ≤ B.card) (hC : 32 ≤ C.card) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, ∃ C' ⊆ C,
      A.card / 16 ≤ A'.card ∧ B.card / 16 ≤ B'.card ∧ C.card / 16 ≤ C'.card ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ a ∈ A', ∀ b ∈ B', ∀ c ∈ C', 0 < s * orient2 a b c := by
  have hgpA : NoThreeCollinear2 A := fun p hp q hq r hr =>
    hgp p (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
      q (Finset.mem_union_left _ (Finset.mem_union_left _ hq))
      r (Finset.mem_union_left _ (Finset.mem_union_left _ hr))
  have hgpB : NoThreeCollinear2 B := fun p hp q hq r hr =>
    hgp p (Finset.mem_union_left _ (Finset.mem_union_right _ hp))
      q (Finset.mem_union_left _ (Finset.mem_union_right _ hq))
      r (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
  have hgpC : NoThreeCollinear2 C := fun p hp q hq r hr =>
    hgp p (Finset.mem_union_right _ hp) q (Finset.mem_union_right _ hq) r (Finset.mem_union_right _ hr)
  -- Step 1: Ham Sandwich on (A, B), orient so ≥ half of C has ℓ1 ≥ 0
  obtain ⟨θ1_0, c1_0, hA1_le, hA1_ge, hB1_le, hB1_ge⟩ :=
    ham_sandwich_2d A B (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
  have hex1 : ∃ θ1 c1 : ℝ,
      A.card / 2 ≤ (A.filter fun p => projDir θ1 p ≤ c1).card ∧
      B.card / 2 ≤ (B.filter fun p => projDir θ1 p ≤ c1).card ∧
      C.card / 2 ≤ (C.filter fun p => c1 ≤ projDir θ1 p).card := by
    by_cases hC1 : C.card / 2 ≤ (C.filter fun p => c1_0 ≤ projDir θ1_0 p).card
    · exact ⟨θ1_0, c1_0, hA1_le, hB1_le, hC1⟩
    · refine ⟨θ1_0 + Real.pi, -c1_0, ?_, ?_, ?_⟩
      · convert hA1_ge using 2; ext p; simp [projDir_add_pi]
      · convert hB1_ge using 2; ext p; simp [projDir_add_pi]
      · have hpart : (C.filter fun p => c1_0 ≤ projDir θ1_0 p).card +
            (C.filter fun p => projDir θ1_0 p < c1_0).card = C.card := by
          have : (C.filter fun p => projDir θ1_0 p < c1_0) =
              (C.filter fun p => ¬ (c1_0 ≤ projDir θ1_0 p)) := by ext p; simp [not_le]
          rw [this]; exact Finset.card_filter_add_card_filter_not _
        have hsub : (C.filter fun p => projDir θ1_0 p < c1_0) ⊆
            (C.filter fun p => -c1_0 ≤ projDir (θ1_0 + Real.pi) p) := by
          intro p hp
          refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
          have := (Finset.mem_filter.mp hp).2
          rw [projDir_add_pi]; linarith
        have := Finset.card_le_card hsub
        omega
  obtain ⟨θ1, c1, hA1le, hB1le, hC1ge⟩ := hex1
  have hnz1 : Real.cos θ1 ≠ 0 ∨ Real.sin θ1 ≠ 0 := by
    by_contra h; push Not at h; have := Real.sin_sq_add_cos_sq θ1; nlinarith only [h, this]
  have strict_drop (S : Finset (ℝ × ℝ)) (hgpS : NoThreeCollinear2 S) (θ c : ℝ)
      (hnz : Real.cos θ ≠ 0 ∨ Real.sin θ ≠ 0) :
      (S.filter fun p => projDir θ p ≤ c).card - 2 ≤ (S.filter fun p => projDir θ p < c).card ∧
      (S.filter fun p => c ≤ projDir θ p).card - 2 ≤ (S.filter fun p => c < projDir θ p).card := by
    have heq2 : (S.filter fun p => projDir θ p = c).card ≤ 2 := card_on_line_le_two hgpS _ _ c hnz
    constructor
    · have hsub : (S.filter fun p => projDir θ p ≤ c) ⊆
          (S.filter fun p => projDir θ p < c) ∪ (S.filter fun p => projDir θ p = c) := by
        intro p hp; obtain ⟨hpS, hle⟩ := Finset.mem_filter.mp hp
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS, hlt⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS, heq⟩)
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    · have hsub : (S.filter fun p => c ≤ projDir θ p) ⊆
          (S.filter fun p => c < projDir θ p) ∪ (S.filter fun p => projDir θ p = c) := by
        intro p hp; obtain ⟨hpS, hle⟩ := Finset.mem_filter.mp hp
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS, hlt⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS, heq.symm⟩)
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
  let A1 := A.filter fun p => projDir θ1 p < c1
  let B1 := B.filter fun p => projDir θ1 p < c1
  let C1 := C.filter fun p => c1 < projDir θ1 p
  have hA1c : A.card / 2 - 2 ≤ A1.card := (Nat.sub_le_sub_right hA1le 2).trans (strict_drop A hgpA θ1 c1 hnz1).1
  have hB1c : B.card / 2 - 2 ≤ B1.card := (Nat.sub_le_sub_right hB1le 2).trans (strict_drop B hgpB θ1 c1 hnz1).1
  have hC1c : C.card / 2 - 2 ≤ C1.card := (Nat.sub_le_sub_right hC1ge 2).trans (strict_drop C hgpC θ1 c1 hnz1).2
  -- Step 2: Ham Sandwich on (A1, C1), orient so ≥ half of B1 has ℓ2 ≥ 0
  obtain ⟨θ2_0, c2_0, hA2_le, hA2_ge, hC2_le, hC2_ge⟩ :=
    ham_sandwich_2d A1 C1 (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
  have hex2 : ∃ θ2 c2 : ℝ,
      A1.card / 2 ≤ (A1.filter fun p => projDir θ2 p ≤ c2).card ∧
      B1.card / 2 ≤ (B1.filter fun p => c2 ≤ projDir θ2 p).card ∧
      C1.card / 2 ≤ (C1.filter fun p => projDir θ2 p ≤ c2).card ∧
      C1.card / 2 ≤ (C1.filter fun p => c2 ≤ projDir θ2 p).card := by
    by_cases hB2 : B1.card / 2 ≤ (B1.filter fun p => c2_0 ≤ projDir θ2_0 p).card
    · exact ⟨θ2_0, c2_0, hA2_le, hB2, hC2_le, hC2_ge⟩
    · refine ⟨θ2_0 + Real.pi, -c2_0, ?_, ?_, ?_, ?_⟩
      · convert hA2_ge using 2; ext p; simp [projDir_add_pi]
      · have hpart : (B1.filter fun p => c2_0 ≤ projDir θ2_0 p).card +
            (B1.filter fun p => projDir θ2_0 p < c2_0).card = B1.card := by
          have : (B1.filter fun p => projDir θ2_0 p < c2_0) =
              (B1.filter fun p => ¬ (c2_0 ≤ projDir θ2_0 p)) := by ext p; simp [not_le]
          rw [this]; exact Finset.card_filter_add_card_filter_not _
        have hsub : (B1.filter fun p => projDir θ2_0 p < c2_0) ⊆
            (B1.filter fun p => -c2_0 ≤ projDir (θ2_0 + Real.pi) p) := by
          intro p hp
          refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, ?_⟩
          have := (Finset.mem_filter.mp hp).2
          rw [projDir_add_pi]; linarith
        have := Finset.card_le_card hsub
        omega
      · convert hC2_ge using 2; ext p; simp [projDir_add_pi]
      · convert hC2_le using 2; ext p; simp [projDir_add_pi]
  obtain ⟨θ2, c2, hA2le, hB2ge, hC2le, hC2ge⟩ := hex2
  have hnz2 : Real.cos θ2 ≠ 0 ∨ Real.sin θ2 ≠ 0 := by
    by_contra h; push Not at h; have := Real.sin_sq_add_cos_sq θ2; nlinarith only [h, this]
  have hgpA1 : NoThreeCollinear2 A1 := fun p hp q hq r hr =>
    hgpA p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) r (Finset.filter_subset _ _ hr)
  have hgpB1 : NoThreeCollinear2 B1 := fun p hp q hq r hr =>
    hgpB p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) r (Finset.filter_subset _ _ hr)
  have hgpC1 : NoThreeCollinear2 C1 := fun p hp q hq r hr =>
    hgpC p (Finset.filter_subset _ _ hp) q (Finset.filter_subset _ _ hq) r (Finset.filter_subset _ _ hr)
  let A2 := A1.filter fun p => projDir θ2 p < c2
  let B2 := B1.filter fun p => c2 < projDir θ2 p
  let C2L := C1.filter fun p => projDir θ2 p < c2
  let C2R := C1.filter fun p => c2 < projDir θ2 p
  have hA2c : A1.card / 2 - 2 ≤ A2.card := (Nat.sub_le_sub_right hA2le 2).trans (strict_drop A1 hgpA1 θ2 c2 hnz2).1
  have hB2c : B1.card / 2 - 2 ≤ B2.card := (Nat.sub_le_sub_right hB2ge 2).trans (strict_drop B1 hgpB1 θ2 c2 hnz2).2
  have hC2Lc : C1.card / 2 - 2 ≤ C2L.card := (Nat.sub_le_sub_right hC2le 2).trans (strict_drop C1 hgpC1 θ2 c2 hnz2).1
  have hC2Rc : C1.card / 2 - 2 ≤ C2R.card := (Nat.sub_le_sub_right hC2ge 2).trans (strict_drop C1 hgpC1 θ2 c2 hnz2).2
  -- Define shifted coordinates x(p) = projDir θ2 p - c2, y(p) = projDir θ1 p - c1
  let xf : ℝ × ℝ → ℝ := fun p => projDir θ2 p - c2
  let yf : ℝ × ℝ → ℝ := fun p => projDir θ1 p - c1
  let D : ℝ := Real.cos θ2 * Real.sin θ1 - Real.sin θ2 * Real.cos θ1
  have hDne : D ≠ 0 := by
    intro hD0
    let sig : ℝ := Real.cos θ1 * Real.cos θ2 + Real.sin θ1 * Real.sin θ2
    have h1 := Real.sin_sq_add_cos_sq θ1
    have h2 := Real.sin_sq_add_cos_sq θ2
    have hsq : sig ^ 2 = 1 := by
      have hid : sig ^ 2 + D ^ 2 = (Real.sin θ1 ^ 2 + Real.cos θ1 ^ 2) * (Real.sin θ2 ^ 2 + Real.cos θ2 ^ 2) := by
        dsimp [sig, D]; ring
      rw [hD0, h1, h2] at hid; linarith
    have hc : Real.cos θ2 = sig * Real.cos θ1 := by
      have hid : Real.cos θ2 - sig * Real.cos θ1 =
          Real.cos θ2 * (1 - (Real.sin θ1 ^ 2 + Real.cos θ1 ^ 2)) + Real.sin θ1 * D := by
        dsimp [sig, D]; ring
      rw [hD0, h1] at hid; linarith
    have hs : Real.sin θ2 = sig * Real.sin θ1 := by
      have hid : Real.sin θ2 - sig * Real.sin θ1 =
          Real.sin θ2 * (1 - (Real.sin θ1 ^ 2 + Real.cos θ1 ^ 2)) - Real.cos θ1 * D := by
        dsimp [sig, D]; ring
      rw [hD0, h1] at hid; linarith
    have hproj_eq : ∀ p, projDir θ2 p = sig * projDir θ1 p := by
      intro p; unfold projDir; rw [hc, hs]; ring
    have hsig : sig = 1 ∨ sig = -1 := by
      have : (sig - 1) * (sig + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
    rcases hsig with h1s | h1s
    · obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < B2.card)
      obtain ⟨c, hc'⟩ := Finset.card_pos.mp (by omega : 0 < C2L.card)
      have hb1 : projDir θ1 b < c1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
      have hb2 : c2 < projDir θ2 b := (Finset.mem_filter.mp hb).2
      have hc1 : c1 < projDir θ1 c := (Finset.mem_filter.mp (Finset.mem_filter.mp hc').1).2
      have hc2 : projDir θ2 c < c2 := (Finset.mem_filter.mp hc').2
      have hpb := hproj_eq b; have hpc := hproj_eq c; rw [h1s, one_mul] at hpb hpc; linarith
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A2.card)
      obtain ⟨c, hc'⟩ := Finset.card_pos.mp (by omega : 0 < C2R.card)
      have ha1 : projDir θ1 a < c1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      have ha2 : projDir θ2 a < c2 := (Finset.mem_filter.mp ha).2
      have hc1 : c1 < projDir θ1 c := (Finset.mem_filter.mp (Finset.mem_filter.mp hc').1).2
      have hc2 : c2 < projDir θ2 c := (Finset.mem_filter.mp hc').2
      have hpa := hproj_eq a; have hpc := hproj_eq c; rw [h1s] at hpa hpc; linarith
  have hdet_id : ∀ a b c : ℝ × ℝ,
      (xf b - xf a) * (yf c - yf a) - (yf b - yf a) * (xf c - xf a) = D * orient2 a b c := by
    intro a b c; dsimp [xf, yf, D]; unfold projDir orient2; ring
  -- Step 3: Medians of yf on A2 and B2
  obtain ⟨mA, hA_le, hA_ge⟩ := exists_median_1d A2 (Finset.card_pos.mp (by omega)) yf
  obtain ⟨mB, hB_le, hB_ge⟩ := exists_median_1d B2 (Finset.card_pos.mp (by omega)) yf
  have hA2sub : A2 ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hB2sub : B2 ⊆ B := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hC2Lsub : C2L ⊆ C := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hC2Rsub : C2R ⊆ C := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  let sgn : ℝ := if 0 < D then 1 else -1
  have hsgn_pm : sgn = 1 ∨ sgn = -1 := by dsimp [sgn]; split_ifs <;> [left; right] <;> rfl
  have hD_pos_of : ∀ v : ℝ, 0 < D * v → 0 < sgn * v := by
    intro v hv; dsimp [sgn]
    split_ifs with hD
    · rw [one_mul]; exact pos_of_mul_pos_right hv hD.le
    · have hDneg : D < 0 := lt_of_le_of_ne (not_lt.mp hD) hDne
      have hvneg : v < 0 := by nlinarith only [hv, hDneg]
      linarith
  by_cases hm : mA ≤ mB
  · let A' := A2.filter fun p => yf p ≤ mA
    let B' := B2.filter fun p => mB ≤ yf p
    have hA'c : A2.card / 2 ≤ A'.card := hA_le
    have hB'c : B2.card / 2 ≤ B'.card := hB_ge
    refine ⟨A', (Finset.filter_subset _ _).trans hA2sub,
      B', (Finset.filter_subset _ _).trans hB2sub,
      C2L, hC2Lsub, by omega, by omega, by omega, sgn, hsgn_pm, ?_⟩
    intro a ha b hb c hc
    have hxa : xf a < 0 := sub_neg.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hxb : 0 < xf b := sub_pos.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hxc : xf c < 0 := sub_neg.mpr (Finset.mem_filter.mp hc).2
    have hya : yf a ≤ mA := (Finset.mem_filter.mp ha).2
    have hyb_ge : mB ≤ yf b := (Finset.mem_filter.mp hb).2
    have hyb : yf b < 0 := sub_neg.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).2
    have hyc : 0 < yf c := sub_pos.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    apply hD_pos_of
    rw [← hdet_id a b c]
    have hrewrite : (xf b - xf a) * (yf c - yf a) - (yf b - yf a) * (xf c - xf a) =
        (xf b - xf a) * (yf c - yf b) + (yf b - yf a) * (xf b - xf c) := by ring
    rw [hrewrite]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by linarith only [hxa, hxb]) (by linarith only [hyb, hyc]))
      (mul_nonneg (by linarith only [hya, hyb_ge, hm]) (by linarith only [hxb, hxc]))
  · let A' := A2.filter fun p => mA ≤ yf p
    let B' := B2.filter fun p => yf p ≤ mB
    have hA'c : A2.card / 2 ≤ A'.card := hA_ge
    have hB'c : B2.card / 2 ≤ B'.card := hB_le
    refine ⟨A', (Finset.filter_subset _ _).trans hA2sub,
      B', (Finset.filter_subset _ _).trans hB2sub,
      C2R, hC2Rsub, by omega, by omega, by omega, sgn, hsgn_pm, ?_⟩
    intro a ha b hb c hc
    have hxa : xf a < 0 := sub_neg.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hxb : 0 < xf b := sub_pos.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hxc : 0 < xf c := sub_pos.mpr (Finset.mem_filter.mp hc).2
    have hya_ge : mA ≤ yf a := (Finset.mem_filter.mp ha).2
    have hya : yf a < 0 := sub_neg.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).2
    have hyb : yf b ≤ mB := (Finset.mem_filter.mp hb).2
    have hyc : 0 < yf c := sub_pos.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    apply hD_pos_of
    rw [← hdet_id a b c]
    have hrewrite : (xf b - xf a) * (yf c - yf a) - (yf b - yf a) * (xf c - xf a) =
        (xf b - xf a) * (yf c - yf a) + (yf a - yf b) * (xf c - xf a) := by ring
    rw [hrewrite]
    exact add_pos
      (mul_pos (by linarith only [hxa, hxb]) (by linarith only [hya, hyc]))
      (mul_pos (by linarith only [hya_ge, hyb, hm]) (by linarith only [hxa, hxc]))

lemma partition_equal {α : Type*} [DecidableEq α] (m : ℕ) (S : Finset α) (q : ℕ)
    (hcard : m * q ≤ S.card) :
    ∃ U : Fin m → Finset α,
      (∀ i, U i ⊆ S) ∧ (∀ i, (U i).card = q) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  induction m generalizing S with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    have hq : q ≤ S.card := by nlinarith
    obtain ⟨U0, hU0S, hU0card⟩ := Finset.exists_subset_card_eq hq
    have hrem : m * q ≤ (S \ U0).card := by
      have := Finset.card_sdiff_add_card_eq_card hU0S
      nlinarith
    obtain ⟨U', hU'sub, hU'card, hU'disj⟩ := ih (S \ U0) hrem
    refine ⟨Fin.cons U0 U', ?_, ?_, ?_⟩
    · intro i; refine Fin.cases hU0S (fun j => (hU'sub j).trans Finset.sdiff_subset) i
    · intro i; refine Fin.cases hU0card hU'card i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j' =>
          rw [Fin.cons_zero, Fin.cons_succ, Finset.disjoint_right]
          intro x hx; exact (Finset.mem_sdiff.mp (hU'sub j' hx)).2
      | succ i' =>
        cases j using Fin.cases with
        | zero =>
          rw [Fin.cons_zero, Fin.cons_succ, Finset.disjoint_left]
          intro x hx; exact (Finset.mem_sdiff.mp (hU'sub i' hx)).2
        | succ j' =>
          rw [Fin.cons_succ, Fin.cons_succ]
          exact hU'disj i' j' (fun h => hij (congrArg Fin.succ h))

lemma orient2_any_triple {k : ℕ} {Y : Fin k → Finset (ℝ × ℝ)} {s : ℝ}
    (hori : ∀ i j l : Fin k, i < j → j < l →
      ∀ a ∈ Y i, ∀ b ∈ Y j, ∀ c ∈ Y l, 0 < s * orient2 a b c)
    {i j l : Fin k} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ∃ t : ℝ, ∀ a ∈ Y i, ∀ b ∈ Y j, ∀ c ∈ Y l, 0 < t * orient2 a b c := by
  rcases lt_or_gt_of_ne hij with h1 | h1 <;>
  rcases lt_or_gt_of_ne hjl with h2 | h2 <;>
  rcases lt_or_gt_of_ne hil with h3 | h3
  · exact ⟨s, fun a ha b hb c hc => hori i j l h1 h2 a ha b hb c hc⟩
  · exact absurd (h1.trans (h2.trans h3)) (lt_irrefl _)
  · exact ⟨-s, fun a ha b hb c hc => by
      have := hori i l j h3 h2 a ha c hc b hb; rw [orient2_swap23] at this; linarith⟩
  · exact ⟨s, fun a ha b hb c hc => by
      have := hori l i j h3 h1 c hc a ha b hb; rw [orient2_cyc2] at this; exact this⟩
  · exact ⟨-s, fun a ha b hb c hc => by
      have := hori j i l h1 h3 b hb a ha c hc; rw [orient2_swap12] at this; linarith⟩
  · exact ⟨s, fun a ha b hb c hc => by
      have := hori j l i h2 h3 b hb c hc a ha; rw [orient2_cyc] at this; exact this⟩
  · exact absurd (h2.trans (h1.trans h3)) (lt_irrefl _)
  · exact ⟨-s, fun a ha b hb c hc => by
      have := hori l j i h2 h1 c hc b hb a ha; rw [orient2_rev] at this; linarith⟩

lemma orient2_convex_position {k : ℕ} (hk : 3 ≤ k) (Y : Fin k → Finset (ℝ × ℝ))
    (hne : ∀ i, (Y i).Nonempty) (s : ℝ)
    (hori : ∀ i j l : Fin k, i < j → j < l →
      ∀ a ∈ Y i, ∀ b ∈ Y j, ∀ c ∈ Y l, 0 < s * orient2 a b c) :
    ∀ j : Fin k, Disjoint (convexHull ℝ (Y j : Set (ℝ × ℝ)))
      (convexHull ℝ ((Finset.univ.erase j).biUnion Y : Set (ℝ × ℝ))) := by
  have hpair_disj : ∀ i j : Fin k, i ≠ j →
      Disjoint (convexHull ℝ (Y i : Set (ℝ × ℝ))) (convexHull ℝ (Y j : Set (ℝ × ℝ))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro p hpi hpj
    have hex3 : ∃ r : Fin k, r ≠ i ∧ r ≠ j := by
      have hcard : ({i, j} : Finset (Fin k)).card ≤ 2 := Finset.card_le_two
      have hne_sdiff : (Finset.univ \ ({i, j} : Finset (Fin k))).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({i, j} : Finset (Fin k)))
        rw [Finset.card_univ, Fintype.card_fin] at this; omega
      obtain ⟨r, hr⟩ := hne_sdiff
      exact ⟨r, by simpa using (Finset.mem_sdiff.mp hr).2⟩
    obtain ⟨r, hri, hrj⟩ := hex3
    obtain ⟨z, hz⟩ := hne r
    obtain ⟨t, ht⟩ := orient2_any_triple hori hri hij hrj
    have h1 : ∀ b ∈ Y j, 0 < t * orient2 z p b := by
      intro b hb
      let f : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun a => t * ((a.1 * (b.2 - z.2) - a.2 * (b.1 - z.1)))
          map_add' := fun u v => by simp; ring
          map_smul' := fun c u => by simp; ring }
      let c0 : ℝ := t * (z.1 * (b.2 - z.2) - z.2 * (b.1 - z.1))
      have hf_eq : ∀ a, t * orient2 z a b = f a - c0 := by
        intro a; dsimp [f, c0]; unfold orient2; ring
      have hsub : convexHull ℝ (Y i : Set (ℝ × ℝ)) ⊆ {a | c0 < f a} := by
        apply convexHull_min
        · intro a ha; change c0 < f a; have := ht z hz a ha b hb; rw [hf_eq] at this; linarith
        · exact convex_halfSpace_gt f.isLinear c0
      have := hsub hpi; change c0 < f p at this; rw [hf_eq]; linarith
    let g : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun b => t * ((p.1 - z.1) * b.2 - (p.2 - z.2) * b.1)
        map_add' := fun u v => by simp; ring
        map_smul' := fun c u => by simp; ring }
    let d0 : ℝ := t * ((p.1 - z.1) * z.2 - (p.2 - z.2) * z.1)
    have hg_eq : ∀ b, t * orient2 z p b = g b - d0 := by
      intro b; dsimp [g, d0]; unfold orient2; ring
    have hsub2 : convexHull ℝ (Y j : Set (ℝ × ℝ)) ⊆ {b | d0 < g b} := by
      apply convexHull_min
      · intro b hb; change d0 < g b; have := h1 b hb; rw [hg_eq] at this; linarith
      · exact convex_halfSpace_gt g.isLinear d0
    have hpp := hsub2 hpj; change d0 < g p at hpp
    have h0 : t * orient2 z p p = 0 := by rw [orient2_self_right, mul_zero]
    rw [hg_eq] at h0; linarith
  have hseg_disj : ∀ j i1 i2 : Fin k, i1 ≠ j → i2 ≠ j →
      ∀ u1 ∈ Y i1, ∀ u2 ∈ Y i2,
      ∀ p ∈ convexHull ℝ (Y j : Set (ℝ × ℝ)),
      p ∉ convexHull ℝ ({u1, u2} : Set (ℝ × ℝ)) := by
    intro j i1 i2 hi1 hi2 u1 hu1 u2 hu2 p hpj hpseg
    by_cases heq : i1 = i2
    · subst heq
      have hsub : convexHull ℝ ({u1, u2} : Set (ℝ × ℝ)) ⊆ convexHull ℝ (Y i1 : Set (ℝ × ℝ)) :=
        convexHull_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl <;> assumption)
      exact Set.disjoint_left.mp (hpair_disj j i1 hi1.symm) hpj (hsub hpseg)
    · obtain ⟨t, ht⟩ := orient2_any_triple hori heq hi2 hi1
      let g : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun b => t * ((u2.1 - u1.1) * b.2 - (u2.2 - u1.2) * b.1)
          map_add' := fun u v => by simp; ring
          map_smul' := fun c u => by simp; ring }
      let d0 : ℝ := t * ((u2.1 - u1.1) * u1.2 - (u2.2 - u1.2) * u1.1)
      have hg_eq : ∀ b, t * orient2 u1 u2 b = g b - d0 := by
        intro b; dsimp [g, d0]; unfold orient2; ring
      have hsub1 : convexHull ℝ (Y j : Set (ℝ × ℝ)) ⊆ {b | d0 < g b} := by
        apply convexHull_min
        · intro b hb; change d0 < g b; have := ht u1 hu1 u2 hu2 b hb; rw [hg_eq] at this; linarith
        · exact convex_halfSpace_gt g.isLinear d0
      have hsub2 : convexHull ℝ ({u1, u2} : Set (ℝ × ℝ)) ⊆ {b | g b ≤ d0} := by
        apply convexHull_min
        · intro b hb; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          change g b ≤ d0
          rcases hb with h | h
          · rw [h]; have h0 : t * orient2 u1 u2 u1 = 0 := by unfold orient2; ring
            rw [hg_eq] at h0; linarith
          · rw [h]; have h0 : t * orient2 u1 u2 u2 = 0 := by unfold orient2; ring
            rw [hg_eq] at h0; linarith
        · exact convex_halfSpace_le g.isLinear d0
      have hgt : d0 < g p := hsub1 hpj
      have hle : g p ≤ d0 := hsub2 hpseg
      linarith
  intro j
  rw [Set.disjoint_left]
  intro p0 hp0j hp0rest
  have hne_inter : (convexHull ℝ (Y j : Set (ℝ × ℝ)) ∩
      convexHull ℝ (((Finset.univ.erase j).biUnion Y : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))).Nonempty :=
    ⟨p0, hp0j, by simpa using hp0rest⟩
  obtain ⟨A', hA'sub, B', hB'sub, hcard4, p, hpA', hpB'⟩ := kirchberger (Y j) ((Finset.univ.erase j).biUnion Y) hne_inter
  have hfin2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  rw [hfin2] at hcard4
  have hA'ne : A'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpA'; exact hpA'
  have hB'ne : B'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpB'; exact hpB'
  have hpYj : p ∈ convexHull ℝ (Y j : Set (ℝ × ℝ)) := convexHull_mono (Finset.coe_subset.mpr hA'sub) hpA'
  have hmem_other : ∀ u ∈ B', ∃ i : Fin k, i ≠ j ∧ u ∈ Y i := fun u hu => by
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp (hB'sub hu)
    exact ⟨i, (Finset.mem_erase.mp hi).1, hui⟩
  have hB'card : B'.card ≤ 3 := by have := Finset.card_pos.mpr hA'ne; omega
  rcases Nat.le_succ_iff.mp hB'card with hle2 | hB3
  · rcases Nat.le_succ_iff.mp hle2 with hle1 | hB2
    · have hB1 : B'.card = 1 := by have := Finset.card_pos.mpr hB'ne; omega
      obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hB1
      obtain ⟨i, hij, hui⟩ := hmem_other u (Finset.mem_singleton_self u)
      have hpYi : p ∈ convexHull ℝ (Y i : Set (ℝ × ℝ)) :=
        convexHull_mono (by simpa using hui) hpB'
      exact Set.disjoint_left.mp (hpair_disj j i hij.symm) hpYj hpYi
    · obtain ⟨u1, u2, _, rfl⟩ := Finset.card_eq_two.mp hB2
      obtain ⟨i1, hi1, hu1⟩ := hmem_other u1 (by simp)
      obtain ⟨i2, hi2, hu2⟩ := hmem_other u2 (by simp)
      exact hseg_disj j i1 i2 hi1 hi2 u1 hu1 u2 hu2 p hpYj (by simpa using hpB')
  · have hA1 : A'.card = 1 := by have := Finset.card_pos.mpr hA'ne; omega
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hA1
    have hbYj : b ∈ Y j := hA'sub (Finset.mem_singleton_self b)
    have hpb : p = b := by simpa [convexHull_singleton] using hpA'
    subst hpb
    obtain ⟨u1, u2, u3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hB3
    obtain ⟨i1, hi1, hu1⟩ := hmem_other u1 (by simp)
    obtain ⟨i2, hi2, hu2⟩ := hmem_other u2 (by simp)
    obtain ⟨i3, hi3, hu3⟩ := hmem_other u3 (by simp)
    have hpB'_orig := hpB'
    rw [Finset.convexHull_eq] at hpB'
    obtain ⟨w, hw_nn, hw_sum, hw_cm⟩ := hpB'
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw_sum] at hw_cm
    simp only [id_eq] at hw_cm
    have hsum3 : w u1 + w u2 + w u3 = 1 := by
      rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at hw_sum; linarith
    have hcm3 : w u1 • u1 + w u2 • u2 + w u3 • u3 = p := by
      rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at hw_cm
      simpa [add_assoc] using hw_cm
    have hw1 : 0 ≤ w u1 := hw_nn u1 (by simp)
    have hw2 : 0 ≤ w u2 := hw_nn u2 (by simp)
    have hw3 : 0 ≤ w u3 := hw_nn u3 (by simp)
    have hpos1 : 0 < w u1 := by
      rcases eq_or_lt_of_le hw1 with h0 | hpos
      · exfalso
        have hp23 : p ∈ convexHull ℝ ({u2, u3} : Set (ℝ × ℝ)) := by
          rw [← Finset.coe_pair, Finset.convexHull_eq]
          refine ⟨w, fun x hx => hw_nn x (by simp at hx ⊢; tauto), ?_, ?_⟩
          · rw [Finset.sum_pair h23]; linarith
          · rw [Finset.centerMass_eq_of_sum_1 _ _ (by rw [Finset.sum_pair h23]; linarith)]
            simp only [id_eq]; rw [Finset.sum_pair h23]
            have : (0 : ℝ) • u1 = 0 := zero_smul _ _
            rw [← h0, this, zero_add] at hcm3; exact hcm3
        exact hseg_disj j i2 i3 hi2 hi3 u2 hu2 u3 hu3 p (subset_convexHull ℝ _ hbYj) hp23
      · exact hpos
    have hpos2 : 0 < w u2 := by
      rcases eq_or_lt_of_le hw2 with h0 | hpos
      · exfalso
        have hp13 : p ∈ convexHull ℝ ({u1, u3} : Set (ℝ × ℝ)) := by
          rw [← Finset.coe_pair, Finset.convexHull_eq]
          refine ⟨w, fun x hx => hw_nn x (by simp at hx ⊢; tauto), ?_, ?_⟩
          · rw [Finset.sum_pair h13]; linarith
          · rw [Finset.centerMass_eq_of_sum_1 _ _ (by rw [Finset.sum_pair h13]; linarith)]
            simp only [id_eq]; rw [Finset.sum_pair h13]
            have : (0 : ℝ) • u2 = 0 := zero_smul _ _
            rw [← h0, this, add_zero] at hcm3; exact hcm3
        exact hseg_disj j i1 i3 hi1 hi3 u1 hu1 u3 hu3 p (subset_convexHull ℝ _ hbYj) hp13
      · exact hpos
    have hpos3 : 0 < w u3 := by
      rcases eq_or_lt_of_le hw3 with h0 | hpos
      · exfalso
        have hp12 : p ∈ convexHull ℝ ({u1, u2} : Set (ℝ × ℝ)) := by
          rw [← Finset.coe_pair, Finset.convexHull_eq]
          refine ⟨w, fun x hx => hw_nn x (by simp at hx ⊢; tauto), ?_, ?_⟩
          · rw [Finset.sum_pair h12]; linarith
          · rw [Finset.centerMass_eq_of_sum_1 _ _ (by rw [Finset.sum_pair h12]; linarith)]
            simp only [id_eq]; rw [Finset.sum_pair h12]
            have : (0 : ℝ) • u3 = 0 := zero_smul _ _
            rw [← h0, this, add_zero] at hcm3; exact hcm3
        exact hseg_disj j i1 i2 hi1 hi2 u1 hu1 u2 hu2 p (subset_convexHull ℝ _ hbYj) hp12
      · exact hpos
    have hp1 : p.1 = w u1 * u1.1 + w u2 * u2.1 + w u3 * u3.1 := by
      have := congrArg Prod.fst hcm3; simpa using this.symm
    have hp2 : p.2 = w u1 * u1.2 + w u2 * u2.2 + w u3 * u3.2 := by
      have := congrArg Prod.snd hcm3; simpa using this.symm
    have htwo_eq (a1 a2 a3 : ℝ × ℝ) (ia ic : Fin k) (hia : ia ≠ j) (hic : ic ≠ j) (hiac : ia ≠ ic)
        (ha1 : a1 ∈ Y ia) (ha2 : a2 ∈ Y ia) (ha3 : a3 ∈ Y ic)
        (l1 l2 l3 : ℝ) (hl1 : 0 < l1) (hl2 : 0 < l2) (hsum : l1 + l2 + l3 = 1)
        (hx : p.1 = l1 * a1.1 + l2 * a2.1 + l3 * a3.1)
        (hy : p.2 = l1 * a1.2 + l2 * a2.2 + l3 * a3.2) : False := by
      have hl3_eq : l3 = 1 - l1 - l2 := by linarith
      have heq1 : orient2 a1 p a3 = l2 * orient2 a1 a2 a3 := by
        unfold orient2; rw [hx, hy, hl3_eq]; ring
      have heq2 : orient2 a2 p a3 = - l1 * orient2 a1 a2 a3 := by
        unfold orient2; rw [hx, hy, hl3_eq]; ring
      obtain ⟨t, ht⟩ := orient2_any_triple hori hia hic.symm hiac
      have h1 := ht a1 ha1 p hbYj a3 ha3
      have h2 := ht a2 ha2 p hbYj a3 ha3
      rw [heq1] at h1; rw [heq2] at h2
      nlinarith only [h1, h2, hl1, hl2]
    have hthree_lt (a1 a2 a3 : ℝ × ℝ) (k1 k2 k3 : Fin k) (hk12 : k1 < k2) (hk23 : k2 < k3)
        (hk1j : k1 ≠ j) (hk2j : k2 ≠ j) (hk3j : k3 ≠ j)
        (ha1 : a1 ∈ Y k1) (ha2 : a2 ∈ Y k2) (ha3 : a3 ∈ Y k3)
        (l1 l2 l3 : ℝ) (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3) (hsum : l1 + l2 + l3 = 1)
        (hx : p.1 = l1 * a1.1 + l2 * a2.1 + l3 * a3.1)
        (hy : p.2 = l1 * a1.2 + l2 * a2.2 + l3 * a3.2) : False := by
      have h123 : 0 < s * orient2 a1 a2 a3 := hori k1 k2 k3 hk12 hk23 a1 ha1 a2 ha2 a3 ha3
      have hl3_eq : l3 = 1 - l1 - l2 := by linarith
      have h12p : orient2 a1 a2 p = l3 * orient2 a1 a2 a3 := by
        unfold orient2; rw [hx, hy, hl3_eq]; ring
      have h23p : orient2 a2 a3 p = l1 * orient2 a1 a2 a3 := by
        unfold orient2; rw [hx, hy, hl3_eq]; ring
      have h31p : orient2 a3 a1 p = l2 * orient2 a1 a2 a3 := by
        unfold orient2; rw [hx, hy, hl3_eq]; ring
      rcases lt_or_gt_of_ne hk1j with h1j | hj1
      · rcases lt_or_gt_of_ne hk2j with h2j | hj2
        · rcases lt_or_gt_of_ne hk3j with h3j | hj3
          · have h0 := hori k1 k3 j (hk12.trans hk23) h3j a1 ha1 a3 ha3 p hbYj
            rw [orient2_swap12, h31p] at h0; nlinarith only [h0, h123, hl2]
          · have h0 := hori k2 j k3 h2j hj3 a2 ha2 p hbYj a3 ha3
            rw [orient2_swap23, h23p] at h0; nlinarith only [h0, h123, hl1]
        · have h0 := hori k1 j k2 h1j hj2 a1 ha1 p hbYj a2 ha2
          rw [orient2_swap23, h12p] at h0; nlinarith only [h0, h123, hl3]
      · have h0 := hori j k1 k3 hj1 (hk12.trans hk23) p hbYj a1 ha1 a3 ha3
        have hcyc : orient2 p a1 a3 = - orient2 a3 a1 p := by unfold orient2; ring
        rw [hcyc, h31p] at h0; nlinarith only [h0, h123, hl2]
    by_cases h12e : i1 = i2
    · by_cases h23e : i2 = i3
      · subst h12e; subst h23e
        have hpYi : p ∈ convexHull ℝ (Y i1 : Set (ℝ × ℝ)) :=
          convexHull_mono (by intro x hx; simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> assumption) hpB'_orig
        exact Set.disjoint_left.mp (hpair_disj j i1 hi1.symm) hpYj hpYi
      · exact htwo_eq u1 u2 u3 i1 i3 hi1 hi3 (h12e ▸ h23e) hu1 (h12e ▸ hu2) hu3 (w u1) (w u2) (w u3) hpos1 hpos2 hsum3 hp1 hp2
    · by_cases h13e : i1 = i3
      · exact htwo_eq u1 u3 u2 i1 i2 hi1 hi2 h12e hu1 (h13e ▸ hu3) hu2 (w u1) (w u3) (w u2) hpos1 hpos3 (by linarith) (by linarith) (by linarith)
      · by_cases h23e : i2 = i3
        · exact htwo_eq u2 u3 u1 i2 i1 hi2 hi1 (Ne.symm h12e) hu2 (h23e ▸ hu3) hu1 (w u2) (w u3) (w u1) hpos2 hpos3 (by linarith) (by linarith) (by linarith)
        · rcases lt_or_gt_of_ne h12e with h12' | h21' <;>
          rcases lt_or_gt_of_ne h23e with h23' | h32' <;>
          rcases lt_or_gt_of_ne h13e with h13' | h31'
          · exact hthree_lt u1 u2 u3 i1 i2 i3 h12' h23' hi1 hi2 hi3 hu1 hu2 hu3 (w u1) (w u2) (w u3) hpos1 hpos2 hpos3 hsum3 hp1 hp2
          · exact absurd (h12'.trans (h23'.trans h31')) (lt_irrefl _)
          · exact hthree_lt u1 u3 u2 i1 i3 i2 h13' h32' hi1 hi3 hi2 hu1 hu3 hu2 (w u1) (w u3) (w u2) hpos1 hpos3 hpos2 (by linarith) (by linarith) (by linarith)
          · exact hthree_lt u3 u1 u2 i3 i1 i2 h31' h12' hi3 hi1 hi2 hu3 hu1 hu2 (w u3) (w u1) (w u2) hpos3 hpos1 hpos2 (by linarith) (by linarith) (by linarith)
          · exact hthree_lt u2 u1 u3 i2 i1 i3 h21' h13' hi2 hi1 hi3 hu2 hu1 hu3 (w u2) (w u1) (w u3) hpos2 hpos1 hpos3 (by linarith) (by linarith) (by linarith)
          · exact hthree_lt u2 u3 u1 i2 i3 i1 h23' h31' hi2 hi3 hi1 hu2 hu3 hu1 (w u2) (w u3) (w u1) hpos2 hpos3 hpos1 (by linarith) (by linarith) (by linarith)
          · exact absurd (h32'.trans (h21'.trans h13')) (lt_irrefl _)
          · exact hthree_lt u3 u2 u1 i3 i2 i1 h32' h21' hi3 hi2 hi1 hu3 hu2 hu1 (w u3) (w u2) (w u1) hpos3 hpos2 hpos1 (by linarith) (by linarith) (by linarith)

lemma positive_fraction_convex_2d (k₀ : ℕ) (hk₀ : 3 ≤ k₀) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ (Y : Finset (ℝ × ℝ)),
      (∀ p ∈ Y, ∀ q ∈ Y, p.1 = q.1 → p = q) →
      NoThreeCollinear2 Y →
      M ≤ Y.card →
      ∃ (C : Fin k₀ → Finset (ℝ × ℝ)) (s : ℝ),
        (s = 1 ∨ s = -1) ∧
        (∀ i, C i ⊆ Y) ∧
        (∀ i, Y.card / M ≤ (C i).card) ∧
        (∀ i, (C i).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
        (∀ i j l : Fin k₀, i < j → j < l →
          ∀ a ∈ C i, ∀ b ∈ C j, ∀ c ∈ C l, 0 < s * orient2 a b c) := by
  let m := Nat.choose (2 * k₀ - 4) (k₀ - 2) + 1
  have hm3 : 3 ≤ m := by
    have hge : ∀ r : ℕ, 1 ≤ r → 2 ≤ Nat.choose (2 * r) r := by
      intro r hr
      induction r, hr using Nat.le_induction with
      | base => decide
      | succ r hr ih =>
        rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, Nat.choose_succ_succ]
        have hpos : 1 ≤ Nat.choose (2 * r + 1) (r + 1) := Nat.choose_pos (by omega)
        have hpos2 : 1 ≤ Nat.choose (2 * r + 1) r := Nat.choose_pos (by omega)
        exact Nat.add_le_add hpos2 hpos
    have h2 : 2 ≤ Nat.choose (2 * k₀ - 4) (k₀ - 2) := by
      rw [show 2 * k₀ - 4 = 2 * (k₀ - 2) by omega]
      exact hge (k₀ - 2) (by omega)
    omega
  -- Define triples of Fin m with i < j < l
  let triples : Finset (Fin m × Fin m × Fin m) :=
    Finset.univ.filter fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2
  -- By induction on any subset T ⊆ triples, refine U to be same-type on all t ∈ T
  have refine_triples : ∀ (T : Finset (Fin m × Fin m × Fin m)), T ⊆ triples →
      ∀ (U : Fin m → Finset (ℝ × ℝ)),
        (∀ i, NoThreeCollinear2 (U i)) →
        (∀ i j l : Fin m, i < j → j < l → NoThreeCollinear2 (U i ∪ U j ∪ U l)) →
        (∀ i, 32 * 16 ^ T.card ≤ (U i).card) →
        ∃ V : Fin m → Finset (ℝ × ℝ),
          (∀ i, V i ⊆ U i) ∧
          (∀ i, (U i).card / 16 ^ T.card ≤ (V i).card) ∧
          (∀ t ∈ T, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            ∀ a ∈ V t.1, ∀ b ∈ V t.2.1, ∀ c ∈ V t.2.2, 0 < s * orient2 a b c) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ U _ _ _
      exact ⟨U, fun _ => Finset.Subset.rfl, fun i => by simp, fun _ h => absurd h (Finset.notMem_empty _)⟩
    | @insert t T' htT' ih =>
      intro hsub U hgpU hgp3 hcard
      have ht_mem : t ∈ triples := hsub (Finset.mem_insert_self _ _)
      have hlt : t.1 < t.2.1 ∧ t.2.1 < t.2.2 := (Finset.mem_filter.mp ht_mem).2
      have hne12 : t.1 ≠ t.2.1 := hlt.1.ne
      have hne23 : t.2.1 ≠ t.2.2 := hlt.2.ne
      have hne13 : t.1 ≠ t.2.2 := (hlt.1.trans hlt.2).ne
      have hT'sub : T' ⊆ triples := (Finset.subset_insert _ _).trans hsub
      have hcard_ins : (insert t T').card = T'.card + 1 := Finset.card_insert_of_notMem htT'
      have hcard' : ∀ i, 32 * 16 ^ T'.card ≤ (U i).card := fun i => by
        have h1 := hcard i; rw [hcard_ins, pow_succ] at h1
        have : 1 ≤ 16 ^ T'.card := Nat.one_le_pow _ _ (by omega)
        nlinarith
      obtain ⟨V', hV'sub, hV'card, hV'same⟩ := ih hT'sub U hgpU hgp3 hcard'
      have h32 : ∀ i, 32 ≤ (V' i).card := fun i => by
        have h1 := hcard i; rw [hcard_ins, pow_succ] at h1
        have h2 := hV'card i
        have hpos : 0 < 16 ^ T'.card := by positivity
        have h3 : 32 * 16 ≤ (U i).card / 16 ^ T'.card := by
          rw [Nat.le_div_iff_mul_le hpos]; nlinarith
        omega
      have hgpV' : NoThreeCollinear2 (V' t.1 ∪ V' t.2.1 ∪ V' t.2.2) := by
        intro p hp q hq r hr
        have hsub3 : V' t.1 ∪ V' t.2.1 ∪ V' t.2.2 ⊆ U t.1 ∪ U t.2.1 ∪ U t.2.2 :=
          Finset.union_subset_union (Finset.union_subset_union (hV'sub _) (hV'sub _)) (hV'sub _)
        exact hgp3 t.1 t.2.1 t.2.2 hlt.1 hlt.2 p (hsub3 hp) q (hsub3 hq) r (hsub3 hr)
      obtain ⟨A', hA'sub, B', hB'sub, C', hC'sub, hA'c, hB'c, hC'c, st, hst_pm, hst⟩ :=
        same_type_2d_triple (V' t.1) (V' t.2.1) (V' t.2.2) hgpV' (h32 t.1) (h32 t.2.1) (h32 t.2.2)
      let V : Fin m → Finset (ℝ × ℝ) := fun i =>
        if i = t.1 then A' else if i = t.2.1 then B' else if i = t.2.2 then C' else V' i
      have hV_sub_V' : ∀ i, V i ⊆ V' i := fun i => by
        dsimp [V]; split_ifs with h1 h2 h3
        · subst h1; exact hA'sub
        · subst h2; exact hB'sub
        · subst h3; exact hC'sub
        · exact Finset.Subset.rfl
      have hV_card_V' : ∀ i, (V' i).card / 16 ≤ (V i).card := fun i => by
        dsimp [V]; split_ifs with h1 h2 h3
        · subst h1; exact hA'c
        · subst h2; exact hB'c
        · subst h3; exact hC'c
        · exact Nat.div_le_self _ _
      refine ⟨V, fun i => (hV_sub_V' i).trans (hV'sub i), fun i => ?_, fun t' ht' => ?_⟩
      · rw [hcard_ins, pow_succ, ← Nat.div_div_eq_div_mul]
        exact (Nat.div_le_div_right (hV'card i)).trans (hV_card_V' i)
      · rcases Finset.mem_insert.mp ht' with rfl | ht'T'
        · refine ⟨st, hst_pm, fun a ha b hb c hc => ?_⟩
          have ha' : a ∈ A' := by simpa [V] using ha
          have hb' : b ∈ B' := by simpa [V, hne12.symm] using hb
          have hc' : c ∈ C' := by simpa [V, hne13.symm, hne23.symm] using hc
          exact hst a ha' b hb' c hc'
        · obtain ⟨s', hs'pm, hs'⟩ := hV'same t' ht'T'
          exact ⟨s', hs'pm, fun a ha b hb c hc => hs' a (hV_sub_V' _ ha) b (hV_sub_V' _ hb) c (hV_sub_V' _ hc)⟩
  let M : ℕ := 64 * m * 16 ^ triples.card
  have hM1 : 1 ≤ M := by
    have : 1 ≤ 16 ^ triples.card := Nat.one_le_pow _ _ (by omega)
    dsimp [M]; nlinarith
  refine ⟨M, hM1, fun Y hxinj hgpY hYcard => ?_⟩
  let q := Y.card / m
  have hmq : m * q ≤ Y.card := Nat.mul_div_le Y.card m
  obtain ⟨U, hUsub, hUcard, hUdisj⟩ := partition_equal m Y q hmq
  have hq_ge : 32 * 16 ^ triples.card ≤ q := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < m)]
    dsimp [M] at hYcard; nlinarith
  have hgpU : ∀ i, NoThreeCollinear2 (U i) := fun i p hp q hq r hr =>
    hgpY p (hUsub i hp) q (hUsub i hq) r (hUsub i hr)
  have hgp3 : ∀ i j l : Fin m, i < j → j < l → NoThreeCollinear2 (U i ∪ U j ∪ U l) := by
    intro i j l _ _ p hp q hq r hr
    have hsub3 : U i ∪ U j ∪ U l ⊆ Y := Finset.union_subset (Finset.union_subset (hUsub i) (hUsub j)) (hUsub l)
    exact hgpY p (hsub3 hp) q (hsub3 hq) r (hsub3 hr)
  obtain ⟨V, hVsub, hVcard, hVsame⟩ := refine_triples triples Finset.Subset.rfl U hgpU hgp3 (fun i => by rw [hUcard i]; exact hq_ge)
  have hVne : ∀ i, (V i).Nonempty := fun i => by
    rw [← Finset.card_pos]
    have h1 := hVcard i; rw [hUcard i] at h1
    have hpos : 0 < 16 ^ triples.card := by positivity
    have h2 : 32 ≤ q / 16 ^ triples.card := by rw [Nat.le_div_iff_mul_le hpos]; linarith
    omega
  choose y hyV using hVne
  have hyY : ∀ i, y i ∈ Y := fun i => hUsub i (hVsub i (hyV i))
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hUdisj i j hne) (hVsub i (hyV i)) (hij ▸ hVsub j (hyV j))
  let S : Finset (ℝ × ℝ) := Finset.univ.image y
  have hScard : S.card = m := by rw [Finset.card_image_of_injective _ hyinj, Finset.card_univ, Fintype.card_fin]
  have hSsub : S ⊆ Y := by
    intro p hp; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp; exact hyY i
  have hSgp : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p.1 < q.1 → q.1 < r.1 → slope2 p q ≠ slope2 q r := by
    intro p hp q hq r hr hpq hqr heq
    have hne1 : p ≠ q := fun h => hpq.ne (congrArg Prod.fst h)
    have hne2 : q ≠ r := fun h => hqr.ne (congrArg Prod.fst h)
    have hne3 : p ≠ r := fun h => (hpq.trans hqr).ne (congrArg Prod.fst h)
    apply hgpY p (hSsub hp) q (hSsub hq) r (hSsub hr) hne1 hne2 hne3
    rw [orient2_eq_slope_diff hpq hqr, heq, sub_self, mul_zero]
  have hSlt : Nat.choose (k₀ + k₀ - 4) (k₀ - 2) < S.card := by
    rw [hScard]; dsimp [m]; rw [show k₀ + k₀ - 4 = 2 * k₀ - 4 by omega]; omega
  have hes := erdos_szekeres_cups_caps (k₀ + k₀) k₀ k₀ rfl (by omega) (by omega) S
    (fun p hp q hq => hxinj p (hSsub hp) q (hSsub hq)) hSgp hSlt
  have hex_sorted : ∃ (idx : Fin k₀ → Fin m) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective idx ∧
      ∀ a b c : Fin k₀, a < b → b < c → 0 < s * orient2 (y (idx a)) (y (idx b)) (y (idx c)) := by
    have sort_set (K : Finset (ℝ × ℝ)) (hKS : K ⊆ S) (hKcard : K.card = k₀) :
        ∃ idx : Fin k₀ → Fin m, Function.Injective idx ∧
          (∀ a, y (idx a) ∈ K) ∧ ∀ a b : Fin k₀, a < b → (y (idx a)).1 < (y (idx b)).1 := by
      let Xvals : Finset ℝ := K.image Prod.fst
      have hXinj : Set.InjOn Prod.fst (K : Set (ℝ × ℝ)) := fun p hp q hq h =>
        hxinj p (hSsub (hKS hp)) q (hSsub (hKS hq)) h
      have hXcard : Xvals.card = k₀ := by rw [Finset.card_image_of_injOn hXinj, hKcard]
      let e : Fin k₀ ≃o Xvals := Xvals.orderIsoOfFin hXcard
      have hpull : ∀ a : Fin k₀, ∃ i : Fin m, y i ∈ K ∧ (y i).1 = (e a).1 := by
        intro a
        obtain ⟨p, hpK, hp1⟩ := Finset.mem_image.mp (e a).2
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hKS hpK)
        exact ⟨i, hpK, hp1⟩
      choose idx hidxK hidx1 using hpull
      have hmono : ∀ a b : Fin k₀, a < b → (y (idx a)).1 < (y (idx b)).1 := by
        intro a b hab; rw [hidx1 a, hidx1 b]; exact e.strictMono hab
      have hinj : Function.Injective idx := by
        intro a b hab
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact (hmono a b h).ne (by rw [hab])
        · exact (hmono b a h).ne (by rw [hab])
      exact ⟨idx, hinj, hidxK, hmono⟩
    rcases hes with ⟨K, hKS, hKcap, hKcard⟩ | ⟨K, hKS, hKcup, hKcard⟩
    · obtain ⟨idx, hidx_inj, hidxK, hmono⟩ := sort_set K hKS hKcard
      refine ⟨idx, -1, Or.inr rfl, hidx_inj, fun a b c hab hbc => ?_⟩
      have h1 := hmono a b hab
      have h2 := hmono b c hbc
      have hsl := hKcap _ (hidxK a) _ (hidxK b) _ (hidxK c) h1 h2
      rw [orient2_eq_slope_diff h1 h2]
      have hd1 : 0 < (y (idx b)).1 - (y (idx a)).1 := sub_pos.mpr h1
      have hd2 : 0 < (y (idx c)).1 - (y (idx b)).1 := sub_pos.mpr h2
      have hdiff : slope2 (y (idx b)) (y (idx c)) - slope2 (y (idx a)) (y (idx b)) < 0 := sub_neg.mpr hsl
      have hprod : ((y (idx b)).1 - (y (idx a)).1) * ((y (idx c)).1 - (y (idx b)).1) *
          (slope2 (y (idx b)) (y (idx c)) - slope2 (y (idx a)) (y (idx b))) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hd1 hd2) hdiff
      linarith
    · obtain ⟨idx, hidx_inj, hidxK, hmono⟩ := sort_set K hKS hKcard
      refine ⟨idx, 1, Or.inl rfl, hidx_inj, fun a b c hab hbc => ?_⟩
      have h1 := hmono a b hab
      have h2 := hmono b c hbc
      have hsl := hKcup _ (hidxK a) _ (hidxK b) _ (hidxK c) h1 h2
      rw [orient2_eq_slope_diff h1 h2, one_mul]
      have hd1 : 0 < (y (idx b)).1 - (y (idx a)).1 := sub_pos.mpr h1
      have hd2 : 0 < (y (idx c)).1 - (y (idx b)).1 := sub_pos.mpr h2
      exact mul_pos (mul_pos hd1 hd2) (sub_pos.mpr hsl)
  obtain ⟨idx, s, hspm, hidx_inj, hidx_ori⟩ := hex_sorted
  refine ⟨fun i => V (idx i), s, hspm,
    fun i => (hVsub (idx i)).trans (hUsub (idx i)),
    fun i => ?_,
    fun i => ⟨y (idx i), hyV (idx i)⟩,
    fun i j hij => (hUdisj (idx i) (idx j) (fun h => hij (hidx_inj h))).mono (hVsub _) (hVsub _),
    fun a b c hab hbc p hp q hq r hr => ?_⟩
  · have h1 := hVcard (idx i)
    rw [hUcard (idx i)] at h1
    have hpos_m : 0 < m * 16 ^ triples.card := Nat.mul_pos (by omega) (by positivity)
    have h2 : Y.card / M ≤ (Y.card / m) / 16 ^ triples.card := by
      rw [Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_left (by dsimp [M]; nlinarith) hpos_m
    exact h2.trans h1
  · have same_on_ordered (i1 i2 i3 : Fin m) (h12 : i1 < i2) (h23 : i2 < i3)
        (a1 a2 : ℝ × ℝ) (ha1 : a1 ∈ V i1) (ha2 : a2 ∈ V i1)
        (b1 b2 : ℝ × ℝ) (hb1 : b1 ∈ V i2) (hb2 : b2 ∈ V i2)
        (c1 c2 : ℝ × ℝ) (hc1 : c1 ∈ V i3) (hc2 : c2 ∈ V i3) :
        0 < orient2 a1 b1 c1 * orient2 a2 b2 c2 := by
      have ht : (i1, i2, i3) ∈ triples := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12, h23⟩
      obtain ⟨st, hst_pm, hst⟩ := hVsame (i1, i2, i3) ht
      have h1 := hst a1 ha1 b1 hb1 c1 hc1
      have h2 := hst a2 ha2 b2 hb2 c2 hc2
      have hst2 : st * st = 1 := by rcases hst_pm with rfl | rfl <;> norm_num
      have hprod : 0 < (st * orient2 a1 b1 c1) * (st * orient2 a2 b2 c2) := mul_pos h1 h2
      have : (st * orient2 a1 b1 c1) * (st * orient2 a2 b2 c2) =
          (st * st) * (orient2 a1 b1 c1 * orient2 a2 b2 c2) := by ring
      rw [this, hst2, one_mul] at hprod; exact hprod
    have hne12 : idx a ≠ idx b := fun h => hab.ne (hidx_inj h)
    have hne23 : idx b ≠ idx c := fun h => hbc.ne (hidx_inj h)
    have hne13 : idx a ≠ idx c := fun h => (hab.trans hbc).ne (hidx_inj h)
    have hprod_pos : 0 < orient2 (y (idx a)) (y (idx b)) (y (idx c)) * orient2 p q r := by
      rcases lt_or_gt_of_ne hne12 with h12 | h21 <;>
      rcases lt_or_gt_of_ne hne23 with h23 | h32 <;>
      rcases lt_or_gt_of_ne hne13 with h13 | h31
      · exact same_on_ordered _ _ _ h12 h23 _ _ (hyV _) hp _ _ (hyV _) hq _ _ (hyV _) hr
      · exact absurd (h12.trans (h23.trans h31)) (lt_irrefl _)
      · have h0 := same_on_ordered _ _ _ h13 h32 _ _ (hyV _) hp _ _ (hyV _) hr _ _ (hyV _) hq
        rw [orient2_swap23 (y (idx a)) (y (idx b)) (y (idx c)), orient2_swap23 p q r] at h0
        simpa [neg_mul_neg] using h0
      · have h0 := same_on_ordered _ _ _ h31 h12 _ _ (hyV _) hr _ _ (hyV _) hp _ _ (hyV _) hq
        rw [orient2_cyc2 (y (idx a)) (y (idx b)) (y (idx c)), orient2_cyc2 p q r] at h0
        exact h0
      · have h0 := same_on_ordered _ _ _ h21 h13 _ _ (hyV _) hq _ _ (hyV _) hp _ _ (hyV _) hr
        rw [orient2_swap12 (y (idx a)) (y (idx b)) (y (idx c)), orient2_swap12 p q r] at h0
        simpa [neg_mul_neg] using h0
      · have h0 := same_on_ordered _ _ _ h23 h31 _ _ (hyV _) hq _ _ (hyV _) hr _ _ (hyV _) hp
        rw [orient2_cyc (y (idx a)) (y (idx b)) (y (idx c)), orient2_cyc p q r] at h0
        exact h0
      · exact absurd (h32.trans (h21.trans h13)) (lt_irrefl _)
      · have h0 := same_on_ordered _ _ _ h32 h21 _ _ (hyV _) hr _ _ (hyV _) hq _ _ (hyV _) hp
        rw [orient2_rev (y (idx a)) (y (idx b)) (y (idx c)), orient2_rev p q r] at h0
        simpa [neg_mul_neg] using h0
    have href := hidx_ori a b c hab hbc
    have hs2 : s * s = 1 := by rcases hspm with rfl | rfl <;> norm_num
    nlinarith only [href, hprod_pos, hs2]

/- ### Part 10: 2-Separability in ℝ^3 via Centerpoints + Hahn-Banach -/

lemma card_on_hyperplane_le_three {U : Finset (ℝ^3)} (hU : Erdos651.IsInGeneralPosition U)
    (f : (ℝ^3) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (r : ℝ) :
    (U.filter fun x => f x = r).card ≤ 3 := by
  by_contra! hgt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (U.filter fun x => f x = r).card by omega)
  have hTU : T ⊆ U := hTsub.trans (Finset.filter_subset _ _)
  have hind : AffineIndependent ℝ (Subtype.val : ↥(T : Set (ℝ^3)) → ℝ^3) :=
    hU T hTU (by omega)
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let y₀ : ↥(T : Set (ℝ^3)) := ⟨x₀, hx₀⟩
  have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ (Subtype.val : ↥(T : Set (ℝ^3)) → ℝ^3) y₀).mp hind
  have hmem_ker : ∀ i : {i : ↥(T : Set (ℝ^3)) // i ≠ y₀}, (i.1.1 -ᵥ y₀.1) ∈ LinearMap.ker f := by
    intro i
    rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
    have h1 := (Finset.mem_filter.mp (hTsub i.1.2)).2
    have h2 := (Finset.mem_filter.mp (hTsub y₀.2)).2
    linarith
  let g : {i : ↥(T : Set (ℝ^3)) // i ≠ y₀} → LinearMap.ker f := fun i => ⟨i.1.1 -ᵥ y₀.1, hmem_ker i⟩
  have hlin_ker : LinearIndependent ℝ g := LinearIndependent.of_comp (LinearMap.ker f).subtype hlin
  have hcard_le : Fintype.card {i : ↥(T : Set (ℝ^3)) // i ≠ y₀} ≤ Module.finrank ℝ (LinearMap.ker f) :=
    hlin_ker.fintype_card_le_finrank
  have hcard_eq : Fintype.card {i : ↥(T : Set (ℝ^3)) // i ≠ y₀} = 3 := by
    have hTcoe : Fintype.card ↥(T : Set (ℝ^3)) = T.card := by simp
    rw [Fintype.card_subtype_compl, hTcoe, hTcard, Fintype.card_subtype_eq]
  have hker_ne_top : LinearMap.ker f ≠ ⊤ := by
    intro htop; apply hf; ext u
    have : u ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
    exact LinearMap.mem_ker.mp this
  have hlt : Module.finrank ℝ (LinearMap.ker f) < Module.finrank ℝ (ℝ^3) :=
    Submodule.finrank_lt hker_ne_top
  rw [finrank_euclideanSpace_fin] at hlt
  omega

lemma exists_nonzero_functional_on_four_coplanar (c1 c2 c3 c4 p : ℝ^3)
    (hp12 : p ∈ convexHull ℝ ({c1, c2} : Set (ℝ^3)))
    (hp34 : p ∈ convexHull ℝ ({c3, c4} : Set (ℝ^3))) :
    ∃ f : (ℝ^3) →ₗ[ℝ] ℝ, f ≠ 0 ∧ f c1 = f p ∧ f c2 = f p ∧ f c3 = f p ∧ f c4 = f p := by
  have pair_span (a b : ℝ^3) (hp : p ∈ convexHull ℝ ({a, b} : Set (ℝ^3))) :
      ∃ v : ℝ^3, a - p ∈ ℝ ∙ v ∧ b - p ∈ ℝ ∙ v := by
    rw [convexHull_pair] at hp
    obtain ⟨t, s, ht, hs, hts, heq⟩ := hp
    by_cases ht0 : t = 0
    · have hs1 : s = 1 := by linarith
      have hpb : p = b := by rw [ht0, hs1, zero_smul, one_smul, zero_add] at heq; exact heq.symm
      refine ⟨a - p, Submodule.mem_span_singleton_self _, ?_⟩
      rw [hpb, sub_self]; exact Submodule.zero_mem _
    · refine ⟨b - p, ?_, Submodule.mem_span_singleton_self _⟩
      have hlin : t • (a - p) + s • (b - p) = 0 := by
        calc t • (a - p) + s • (b - p)
          _ = (t • a + s • b) - (t + s) • p := by rw [smul_sub, smul_sub, add_smul]; abel
          _ = p - (1 : ℝ) • p := by rw [heq, hts]
          _ = 0 := by rw [one_smul, sub_self]
      have hap : a - p = (-s / t) • (b - p) := by
        have h1 : t • (a - p) = (-s) • (b - p) := by
          rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hlin
        calc a - p = t⁻¹ • (t • (a - p)) := by rw [inv_smul_smul₀ ht0]
          _ = t⁻¹ • ((-s) • (b - p)) := by rw [h1]
          _ = (-s / t) • (b - p) := by rw [smul_smul]; congr 1; ring
      rw [hap]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨v1, hc1, hc2⟩ := pair_span c1 c2 hp12
  obtain ⟨v2, hc3, hc4⟩ := pair_span c3 c4 hp34
  let K : Submodule ℝ (ℝ^3) := Submodule.span ℝ ({v1, v2} : Set (ℝ^3))
  have hKdim : Module.finrank ℝ K ≤ 2 := by
    have h1 := finrank_span_le_card (R := ℝ) ({v1, v2} : Set (ℝ^3))
    have h2 : ({v1, v2} : Set (ℝ^3)).toFinset.card ≤ 2 := by
      have : ({v1, v2} : Set (ℝ^3)).toFinset = ({v1, v2} : Finset (ℝ^3)) := by ext x; simp
      rw [this]; exact Finset.card_le_two
    exact h1.trans h2
  have hKorth_pos : 0 < Module.finrank ℝ Kᗮ := by
    have hadd := K.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at hadd
    omega
  have hKorth_ne : Kᗮ ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hKorth_pos; omega
  obtain ⟨n, hnK, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKorth_ne
  let f : (ℝ^3) →ₗ[ℝ] ℝ := (innerSL ℝ n).toLinearMap
  have hf_ne : f ≠ 0 := by
    intro h0
    have hnn : inner ℝ n n = 0 := by
      have := congrArg (fun g : (ℝ^3) →ₗ[ℝ] ℝ => g n) h0
      exact this
    rw [real_inner_self_eq_norm_sq] at hnn
    exact norm_ne_zero_iff.mpr hn0 (sq_eq_zero_iff.mp hnn)
  have hf_zero : ∀ u ∈ K, f u = 0 := fun u hu => by
    change inner ℝ n u = 0
    exact (Submodule.mem_orthogonal K n).mp hnK u hu |> fun h => by rw [real_inner_comm]; exact h
  have hsub1 : (ℝ ∙ v1) ≤ K := Submodule.span_mono (by simp)
  have hsub2 : (ℝ ∙ v2) ≤ K := Submodule.span_mono (by simp)
  have hfeq (c : ℝ^3) (hc : c - p ∈ K) : f c = f p := by
    have h0 := hf_zero (c - p) hc
    rw [map_sub] at h0; linarith
  exact ⟨f, hf_ne, hfeq c1 (hsub1 hc1), hfeq c2 (hsub1 hc2), hfeq c3 (hsub2 hc3), hfeq c4 (hsub2 hc4)⟩

lemma separate_four_3d (X1 X2 X3 X4 : Finset (ℝ^3))
    (hgp : Erdos651.IsInGeneralPosition (X1 ∪ X2 ∪ X3 ∪ X4))
    (h1 : 60 ≤ X1.card) (h2 : 60 ≤ X2.card) (h3 : 60 ≤ X3.card) (h4 : 60 ≤ X4.card) :
    ∃ (f : (ℝ^3) →ₗ[ℝ] ℝ) (r : ℝ),
      X1.card / 5 ≤ (X1.filter fun x => r < f x).card ∧
      X2.card / 5 ≤ (X2.filter fun x => r < f x).card ∧
      X3.card / 5 ≤ (X3.filter fun x => f x < r).card ∧
      X4.card / 5 ≤ (X4.filter fun x => f x < r).card := by
  obtain ⟨c1, hc1⟩ := centerpoint_exists X1 (Finset.card_pos.mp (by omega))
  obtain ⟨c2, hc2⟩ := centerpoint_exists X2 (Finset.card_pos.mp (by omega))
  obtain ⟨c3, hc3⟩ := centerpoint_exists X3 (Finset.card_pos.mp (by omega))
  obtain ⟨c4, hc4⟩ := centerpoint_exists X4 (Finset.card_pos.mp (by omega))
  have hex_fr : ∃ (f : (ℝ^3) →ₗ[ℝ] ℝ) (r : ℝ),
      f ≠ 0 ∧ r ≤ f c1 ∧ r ≤ f c2 ∧ f c3 ≤ r ∧ f c4 ≤ r := by
    by_cases hdisj : Disjoint (convexHull ℝ ({c1, c2} : Set (ℝ^3))) (convexHull ℝ ({c3, c4} : Set (ℝ^3)))
    · have hcomp1 : IsCompact (convexHull ℝ ({c1, c2} : Set (ℝ^3))) :=
        Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)
      have hcomp2 : IsCompact (convexHull ℝ ({c3, c4} : Set (ℝ^3))) :=
        Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)
      obtain ⟨g, u, v, hgu, huv, hgv⟩ :=
        geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hcomp1
          (convex_convexHull ℝ _) hcomp2.isClosed hdisj
      let f : (ℝ^3) →ₗ[ℝ] ℝ := -g.toLinearMap
      let r : ℝ := -(u + v) / 2
      have h1' : g c1 < u := hgu c1 (subset_convexHull ℝ _ (by simp))
      have h2' : g c2 < u := hgu c2 (subset_convexHull ℝ _ (by simp))
      have h3' : v < g c3 := hgv c3 (subset_convexHull ℝ _ (by simp))
      have h4' : v < g c4 := hgv c4 (subset_convexHull ℝ _ (by simp))
      have hfne : f ≠ 0 := by
        intro h0
        have hc10 : f c1 = 0 := congrArg (fun h : (ℝ^3) →ₗ[ℝ] ℝ => h c1) h0
        have hc30 : f c3 = 0 := congrArg (fun h : (ℝ^3) →ₗ[ℝ] ℝ => h c3) h0
        change -g c1 = 0 at hc10; change -g c3 = 0 at hc30; linarith
      refine ⟨f, r, hfne, ?_, ?_, ?_, ?_⟩ <;> (dsimp [f, r]; linarith)
    · rw [Set.not_disjoint_iff] at hdisj
      obtain ⟨p, hp12, hp34⟩ := hdisj
      obtain ⟨f, hfne, hf1, hf2, hf3, hf4⟩ := exists_nonzero_functional_on_four_coplanar c1 c2 c3 c4 p hp12 hp34
      exact ⟨f, f p, hfne, hf1.ge, hf2.ge, hf3.le, hf4.le⟩
  obtain ⟨f, r, hfne, hfc1, hfc2, hfc3, hfc4⟩ := hex_fr
  have hgp_sub (S : Finset (ℝ^3)) (hSU : S ⊆ X1 ∪ X2 ∪ X3 ∪ X4) : Erdos651.IsInGeneralPosition S :=
    fun Z hZS hZc => hgp Z (hZS.trans hSU) hZc
  have hdrop_gt (S : Finset (ℝ^3)) (hSU : S ⊆ X1 ∪ X2 ∪ X3 ∪ X4)
      (hS60 : 60 ≤ S.card) (hge : S.card ≤ 4 * (S.filter fun x => r ≤ f x).card) :
      S.card / 5 ≤ (S.filter fun x => r < f x).card := by
    have heq3 : (S.filter fun x => f x = r).card ≤ 3 :=
      card_on_hyperplane_le_three (hgp_sub S hSU) f hfne r
    have hsub : (S.filter fun x => r ≤ f x) ⊆
        (S.filter fun x => r < f x) ∪ (S.filter fun x => f x = r) := by
      intro x hx; obtain ⟨hxS, hle⟩ := Finset.mem_filter.mp hx
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, heq.symm⟩)
    have hcard_u := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hdrop_lt (S : Finset (ℝ^3)) (hSU : S ⊆ X1 ∪ X2 ∪ X3 ∪ X4)
      (hS60 : 60 ≤ S.card) (hle : S.card ≤ 4 * (S.filter fun x => f x ≤ r).card) :
      S.card / 5 ≤ (S.filter fun x => f x < r).card := by
    have heq3 : (S.filter fun x => f x = r).card ≤ 3 :=
      card_on_hyperplane_le_three (hgp_sub S hSU) f hfne r
    have hsub : (S.filter fun x => f x ≤ r) ⊆
        (S.filter fun x => f x < r) ∪ (S.filter fun x => f x = r) := by
      intro x hx; obtain ⟨hxS, hle'⟩ := Finset.mem_filter.mp hx
      rcases lt_or_eq_of_le hle' with hlt | heq
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, heq⟩)
    have hcard_u := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hc3' : X3.card ≤ 4 * (X3.filter fun x => f x ≤ r).card := by
    have h0 := hc3 (-f) (-r) (by simp; linarith)
    convert h0 using 3; ext x; simp
  have hc4' : X4.card ≤ 4 * (X4.filter fun x => f x ≤ r).card := by
    have h0 := hc4 (-f) (-r) (by simp; linarith)
    convert h0 using 3; ext x; simp
  refine ⟨f, r,
    hdrop_gt X1 (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))) h1 (hc1 f r hfc1),
    hdrop_gt X2 (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))) h2 (hc2 f r hfc2),
    hdrop_lt X3 (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)) h3 hc3',
    hdrop_lt X4 (fun x hx => Finset.mem_union_right _ hx) h4 hc4'⟩

lemma two_separable_3d (k₀ : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ (X : Fin k₀ → Finset (ℝ^3)),
      Erdos651.IsInGeneralPosition (Finset.univ.biUnion X) →
      (∀ i, 60 * M ≤ (X i).card) →
      ∃ Y : Fin k₀ → Finset (ℝ^3),
        (∀ i, Y i ⊆ X i) ∧
        (∀ i, (X i).card / M ≤ (Y i).card) ∧
        (∀ i j i' j' : Fin k₀, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
          Disjoint (convexHull ℝ ((Y i ∪ Y j : Finset (ℝ^3)) : Set (ℝ^3)))
            (convexHull ℝ ((Y i' ∪ Y j' : Finset (ℝ^3)) : Set (ℝ^3)))) := by
  let quads : Finset (Fin k₀ × Fin k₀ × Fin k₀ × Fin k₀) :=
    Finset.univ.filter fun q =>
      q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧ q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2
  have refine_quads : ∀ (T : Finset (Fin k₀ × Fin k₀ × Fin k₀ × Fin k₀)), T ⊆ quads →
      ∀ (X : Fin k₀ → Finset (ℝ^3)),
        Erdos651.IsInGeneralPosition (Finset.univ.biUnion X) →
        (∀ i, 60 * 5 ^ T.card ≤ (X i).card) →
        ∃ Y : Fin k₀ → Finset (ℝ^3),
          (∀ i, Y i ⊆ X i) ∧
          (∀ i, (X i).card / 5 ^ T.card ≤ (Y i).card) ∧
          (∀ q ∈ T, Disjoint (convexHull ℝ ((Y q.1 ∪ Y q.2.1 : Finset (ℝ^3)) : Set (ℝ^3)))
            (convexHull ℝ ((Y q.2.2.1 ∪ Y q.2.2.2 : Finset (ℝ^3)) : Set (ℝ^3)))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ X _ _
      exact ⟨X, fun _ => Finset.Subset.rfl, fun i => by simp, fun _ h => absurd h (Finset.notMem_empty _)⟩
    | @insert q T' hqT' ih =>
      intro hsub X hgp hcard
      have hq_mem : q ∈ quads := hsub (Finset.mem_insert_self _ _)
      have hdisj_idx := (Finset.mem_filter.mp hq_mem).2
      have hT'sub : T' ⊆ quads := (Finset.subset_insert _ _).trans hsub
      have hcard_ins : (insert q T').card = T'.card + 1 := Finset.card_insert_of_notMem hqT'
      have hcard' : ∀ i, 60 * 5 ^ T'.card ≤ (X i).card := fun i => by
        have h1 := hcard i; rw [hcard_ins, pow_succ] at h1
        have : 1 ≤ 5 ^ T'.card := Nat.one_le_pow _ _ (by omega)
        nlinarith
      obtain ⟨Y', hY'sub, hY'card, hY'sep⟩ := ih hT'sub X hgp hcard'
      have h60 : ∀ i, 60 ≤ (Y' i).card := fun i => by
        have h1 := hcard i; rw [hcard_ins, pow_succ] at h1
        have h2 := hY'card i
        have hpos : 0 < 5 ^ T'.card := by positivity
        have h3 : 60 * 5 ≤ (X i).card / 5 ^ T'.card := by
          rw [Nat.le_div_iff_mul_le hpos]; nlinarith
        omega
      have hgp4 : Erdos651.IsInGeneralPosition (Y' q.1 ∪ Y' q.2.1 ∪ Y' q.2.2.1 ∪ Y' q.2.2.2) := by
        intro Z hZ hZc
        have hsub4 : Y' q.1 ∪ Y' q.2.1 ∪ Y' q.2.2.1 ∪ Y' q.2.2.2 ⊆ Finset.univ.biUnion X := by
          intro x hx
          simp only [Finset.mem_union] at hx
          rcases hx with ((hx | hx) | hx) | hx <;>
            exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, hY'sub _ hx⟩
        exact hgp Z (hZ.trans hsub4) hZc
      obtain ⟨f, r, hf1, hf2, hf3, hf4⟩ :=
        separate_four_3d (Y' q.1) (Y' q.2.1) (Y' q.2.2.1) (Y' q.2.2.2) hgp4
          (h60 q.1) (h60 q.2.1) (h60 q.2.2.1) (h60 q.2.2.2)
      let Y : Fin k₀ → Finset (ℝ^3) := fun a =>
        if a = q.1 ∨ a = q.2.1 then (Y' a).filter fun x => r < f x
        else if a = q.2.2.1 ∨ a = q.2.2.2 then (Y' a).filter fun x => f x < r
        else Y' a
      have hY_sub_Y' : ∀ a, Y a ⊆ Y' a := fun a => by
        dsimp [Y]; split_ifs <;> [exact Finset.filter_subset _ _; exact Finset.filter_subset _ _; exact Finset.Subset.rfl]
      have hY_card_Y' : ∀ a, (Y' a).card / 5 ≤ (Y a).card := fun a => by
        dsimp [Y]; split_ifs with h12 h34
        · rcases h12 with rfl | rfl <;> assumption
        · rcases h34 with rfl | rfl <;> assumption
        · exact Nat.div_le_self _ _
      refine ⟨Y, fun a => (hY_sub_Y' a).trans (hY'sub a), fun a => ?_, fun q' hq' => ?_⟩
      · rw [hcard_ins, pow_succ, ← Nat.div_div_eq_div_mul]
        exact (Nat.div_le_div_right (hY'card a)).trans (hY_card_Y' a)
      · rcases Finset.mem_insert.mp hq' with rfl | hq'T'
        · have hleft : convexHull ℝ ((Y q'.1 ∪ Y q'.2.1 : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ {x | r < f x} := by
            apply convexHull_min _ (convex_halfSpace_gt f.isLinear r)
            intro x hx
            have hx' : x ∈ Y q'.1 ∨ x ∈ Y q'.2.1 := by simpa using hx
            rcases hx' with h1 | h2
            · have : Y q'.1 = (Y' q'.1).filter fun x => r < f x := by simp [Y]
              rw [this] at h1; exact (Finset.mem_filter.mp h1).2
            · have : Y q'.2.1 = (Y' q'.2.1).filter fun x => r < f x := by simp [Y]
              rw [this] at h2; exact (Finset.mem_filter.mp h2).2
          have hright : convexHull ℝ ((Y q'.2.2.1 ∪ Y q'.2.2.2 : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ {x | f x < r} := by
            apply convexHull_min _ (convex_halfSpace_lt f.isLinear r)
            intro x hx
            have hx' : x ∈ Y q'.2.2.1 ∨ x ∈ Y q'.2.2.2 := by simpa using hx
            rcases hx' with h3 | h4
            · have : Y q'.2.2.1 = (Y' q'.2.2.1).filter fun x => f x < r := by
                dsimp [Y]; rw [if_neg (by push Not; exact ⟨hdisj_idx.1.symm, hdisj_idx.2.2.1.symm⟩), if_pos (Or.inl rfl)]
              rw [this] at h3; exact (Finset.mem_filter.mp h3).2
            · have : Y q'.2.2.2 = (Y' q'.2.2.2).filter fun x => f x < r := by
                dsimp [Y]; rw [if_neg (by push Not; exact ⟨hdisj_idx.2.1.symm, hdisj_idx.2.2.2.symm⟩), if_pos (Or.inr rfl)]
              rw [this] at h4; exact (Finset.mem_filter.mp h4).2
          rw [Set.disjoint_left]
          intro p hp1 hp2
          have : r < f p := hleft hp1
          have : f p < r := hright hp2
          linarith
        · have hsub1 : convexHull ℝ ((Y q'.1 ∪ Y q'.2.1 : Finset (ℝ^3)) : Set (ℝ^3)) ⊆
              convexHull ℝ ((Y' q'.1 ∪ Y' q'.2.1 : Finset (ℝ^3)) : Set (ℝ^3)) :=
            convexHull_mono (Finset.coe_subset.mpr (Finset.union_subset_union (hY_sub_Y' _) (hY_sub_Y' _)))
          have hsub2 : convexHull ℝ ((Y q'.2.2.1 ∪ Y q'.2.2.2 : Finset (ℝ^3)) : Set (ℝ^3)) ⊆
              convexHull ℝ ((Y' q'.2.2.1 ∪ Y' q'.2.2.2 : Finset (ℝ^3)) : Set (ℝ^3)) :=
            convexHull_mono (Finset.coe_subset.mpr (Finset.union_subset_union (hY_sub_Y' _) (hY_sub_Y' _)))
          exact (hY'sep q' hq'T').mono hsub1 hsub2
  refine ⟨5 ^ quads.card, Nat.one_le_pow _ _ (by omega), fun X hgp hcard => ?_⟩
  obtain ⟨Y, hYsub, hYcard, hYsep⟩ := refine_quads quads Finset.Subset.rfl X hgp hcard
  exact ⟨Y, hYsub, hYcard, fun i j i' j' h1 h2 h3 h4 =>
    hYsep (i, j, i', j') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3, h4⟩)⟩

/- ### Part 11: Above/Below Ramsey (Cor cor_ab) and Separation Transfer (Prop lem_tub) -/

def crossDiff (s : ℝ) (p1 p2 p3 p4 : ℝ^3) : ℝ :=
  let d1 := s * orient2 (proj2 p1) (proj2 p2) (proj2 p3)
  let d2 := s * orient2 (proj2 p1) (proj2 p3) (proj2 p4)
  let d3 := s * orient2 (proj2 p2) (proj2 p3) (proj2 p4)
  let d4 := s * orient2 (proj2 p1) (proj2 p2) (proj2 p4)
  d3 * p1 2 + d4 * p3 2 - d2 * p2 2 - d1 * p4 2

lemma orient2_plucker (q1 q2 q3 q4 : ℝ × ℝ) :
    orient2 q1 q2 q3 + orient2 q1 q3 q4 = orient2 q2 q3 q4 + orient2 q1 q2 q4 ∧
    orient2 q2 q3 q4 * q1.1 + orient2 q1 q2 q4 * q3.1 = orient2 q1 q3 q4 * q2.1 + orient2 q1 q2 q3 * q4.1 ∧
    orient2 q2 q3 q4 * q1.2 + orient2 q1 q2 q4 * q3.2 = orient2 q1 q3 q4 * q2.2 + orient2 q1 q2 q3 * q4.2 := by
  unfold orient2; refine ⟨by ring, by ring, by ring⟩

lemma crossDiff_rot2 (s : ℝ) (p1 p2 p3 p4 : ℝ^3) :
    crossDiff s p3 p4 p1 p2 = crossDiff s p1 p2 p3 p4 := by
  unfold crossDiff orient2 proj2; dsimp; ring

lemma crossDiff_rot1 (s : ℝ) (p1 p2 p3 p4 : ℝ^3) :
    crossDiff s p2 p3 p4 p1 = - crossDiff s p1 p2 p3 p4 := by
  unfold crossDiff orient2 proj2; dsimp; ring

lemma mem_convexHull_triple {E : Type*} [AddCommGroup E] [Module ℝ E]
    {v1 v2 v3 p : E} (hp : p ∈ convexHull ℝ ({v1, v2, v3} : Set E)) :
    ∃ l1 l2 l3 : ℝ, 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ l1 + l2 + l3 = 1 ∧
      l1 • v1 + l2 • v2 + l3 • v3 = p := by
  rw [convexHull_insert (Set.insert_nonempty v2 {v3}), mem_convexJoin] at hp
  obtain ⟨x, hx, y, hy, a, b, ha, hb, hab, heq⟩ := hp
  rw [Set.mem_singleton_iff] at hx; subst hx
  rw [convexHull_pair] at hy
  obtain ⟨c, d, hc, hd, hcd, hy_eq⟩ := hy
  refine ⟨a, b * c, b * d, ha, mul_nonneg hb hc, mul_nonneg hb hd, ?_, ?_⟩
  · calc a + b * c + b * d = a + b * (c + d) := by ring
      _ = 1 := by rw [hcd, mul_one, hab]
  · rw [← heq, ← hy_eq, smul_add, smul_smul, smul_smul, add_assoc]

lemma set_triple_rot {α : Type*} (a b c : α) : ({a, b, c} : Set α) = {c, a, b} := by
  ext z; simp; tauto

lemma crossDiff_ne_zero {s : ℝ} {p1 p2 p3 p4 : ℝ^3}
    (hind : AffineIndependent ℝ ![p1, p2, p3, p4])
    (hd3 : s * orient2 (proj2 p2) (proj2 p3) (proj2 p4) ≠ 0) :
    crossDiff s p1 p2 p3 p4 ≠ 0 := by
  intro h0
  let d1 := s * orient2 (proj2 p1) (proj2 p2) (proj2 p3)
  let d2 := s * orient2 (proj2 p1) (proj2 p3) (proj2 p4)
  let d3 := s * orient2 (proj2 p2) (proj2 p3) (proj2 p4)
  let d4 := s * orient2 (proj2 p1) (proj2 p2) (proj2 p4)
  have hpl := orient2_plucker (proj2 p1) (proj2 p2) (proj2 p3) (proj2 p4)
  let w : Fin 4 → ℝ := ![d3, -d2, d4, -d1]
  have hwsum : ∑ i : Fin 4, w i = 0 := by
    rw [Fin.sum_univ_four]
    have hs := congrArg (s * ·) hpl.1
    dsimp [w, d1, d2, d3, d4]; linarith
  have hwvsub : Finset.univ.weightedVSub ![p1, p2, p3, p4] w = 0 := by
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hwsum, Fin.sum_univ_four]
    apply PiLp.ext; intro j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    fin_cases j
    · change d3 * (proj2 p1).1 + -d2 * (proj2 p2).1 + d4 * (proj2 p3).1 + -d1 * (proj2 p4).1 = 0
      have hs := congrArg (s * ·) hpl.2.1; dsimp [d1, d2, d3, d4]; linarith
    · change d3 * (proj2 p1).2 + -d2 * (proj2 p2).2 + d4 * (proj2 p3).2 + -d1 * (proj2 p4).2 = 0
      have hs := congrArg (s * ·) hpl.2.2; dsimp [d1, d2, d3, d4]; linarith
    · change d3 * p1 2 + -d2 * p2 2 + d4 * p3 2 + -d1 * p4 2 = 0
      unfold crossDiff at h0; dsimp [d1, d2, d3, d4] at h0 ⊢; linarith
  have hzero := hind Finset.univ w hwsum hwvsub 0 (Finset.mem_univ 0)
  exact hd3 hzero

lemma seg_tri_disjoint_of_above {s σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    {u1 u2 v1 v2 v3 : ℝ^3} (hu12 : proj2 u1 ≠ proj2 u2)
    (ho1 : 0 < s * orient2 (proj2 u1) (proj2 v1) (proj2 u2))
    (ho2 : 0 < s * orient2 (proj2 u1) (proj2 u2) (proj2 v2))
    (ho3 : 0 < s * orient2 (proj2 u1) (proj2 u2) (proj2 v3))
    (_ho12 : 0 < s * orient2 (proj2 v1) (proj2 u2) (proj2 v2))
    (_ho12' : 0 < s * orient2 (proj2 u1) (proj2 v1) (proj2 v2))
    (_ho13 : 0 < s * orient2 (proj2 v1) (proj2 u2) (proj2 v3))
    (_ho13' : 0 < s * orient2 (proj2 u1) (proj2 v1) (proj2 v3))
    (hcd2 : 0 < σ * crossDiff s u1 v1 u2 v2)
    (hcd3 : 0 < σ * crossDiff s u1 v1 u2 v3) :
    Disjoint (convexHull ℝ ({u1, u2} : Set (ℝ^3))) (convexHull ℝ ({v1, v2, v3} : Set (ℝ^3))) := by
  rw [Set.disjoint_left]
  intro p hpU hpV
  rw [convexHull_pair] at hpU
  obtain ⟨α1, α2, hα1, hα2, hαsum, hpU_eq⟩ := hpU
  obtain ⟨l1, l2, l3, hl1, hl2, hl3, hlsum, hlp⟩ := mem_convexHull_triple hpV
  let a1 := s * orient2 (proj2 u1) (proj2 v1) (proj2 u2)
  let a2 := s * orient2 (proj2 u1) (proj2 u2) (proj2 v2)
  let a3 := s * orient2 (proj2 u1) (proj2 u2) (proj2 v3)
  have ha1 : 0 < a1 := ho1
  have ha2 : 0 < a2 := ho2
  have ha3 : 0 < a3 := ho3
  have hfp_U : s * orient2 (proj2 u1) (proj2 u2) (proj2 p) = 0 := by
    have hproj : proj2 p = α1 • proj2 u1 + α2 • proj2 u2 := by
      rw [← hpU_eq, map_add, map_smul, map_smul]
    have hα2eq : α2 = 1 - α1 := by linarith
    have hp1 : (proj2 p).1 = α1 * (proj2 u1).1 + (1 - α1) * (proj2 u2).1 := by
      rw [hproj, hα2eq]; rfl
    have hp2 : (proj2 p).2 = α1 * (proj2 u1).2 + (1 - α1) * (proj2 u2).2 := by
      rw [hproj, hα2eq]; rfl
    unfold orient2; rw [hp1, hp2]; ring
  have hfp_V : s * orient2 (proj2 u1) (proj2 u2) (proj2 p) = -l1 * a1 + l2 * a2 + l3 * a3 := by
    have hproj : proj2 p = l1 • proj2 v1 + l2 • proj2 v2 + l3 • proj2 v3 := by
      rw [← hlp, map_add, map_add, map_smul, map_smul, map_smul]
    have hl3eq : l3 = 1 - l1 - l2 := by linarith
    have hp1 : (proj2 p).1 = l1 * (proj2 v1).1 + l2 * (proj2 v2).1 + (1 - l1 - l2) * (proj2 v3).1 := by
      rw [hproj, hl3eq]; rfl
    have hp2 : (proj2 p).2 = l1 * (proj2 v1).2 + l2 * (proj2 v2).2 + (1 - l1 - l2) * (proj2 v3).2 := by
      rw [hproj, hl3eq]; rfl
    dsimp [a1, a2, a3]; unfold orient2; rw [hp1, hp2, hl3eq]; ring
  have hbal : l1 * a1 = l2 * a2 + l3 * a3 := by
    rw [hfp_U] at hfp_V; linarith only [hfp_V]
  have hl1_pos : 0 < l1 := by
    by_contra h0
    have hl10 : l1 = 0 := le_antisymm (not_lt.mp h0) hl1
    have hsum23 : l2 * a2 + l3 * a3 = 0 := by rw [hl10, zero_mul] at hbal; linarith
    have hl20 : l2 = 0 := by nlinarith only [hl2, hl3, ha2, ha3, hsum23]
    have hl30 : l3 = 0 := by nlinarith only [hl2, hl3, ha2, ha3, hsum23]
    linarith
  let Δ2 := a1 + a2
  let Δ3 := a1 + a3
  have hΔ2 : 0 < Δ2 := add_pos ha1 ha2
  have hΔ3 : 0 < Δ3 := add_pos ha1 ha3
  let w2 : ℝ^3 := (a2 / Δ2) • v1 + (a1 / Δ2) • v2
  let w3 : ℝ^3 := (a3 / Δ3) • v1 + (a1 / Δ3) • v3
  let μ2 := l2 * Δ2 / a1
  let μ3 := l3 * Δ3 / a1
  have hμ2 : 0 ≤ μ2 := by dsimp [μ2]; positivity
  have hμ3 : 0 ≤ μ3 := by dsimp [μ3]; positivity
  have hμsum : μ2 + μ3 = 1 := by
    dsimp [μ2, μ3, Δ2, Δ3]
    field_simp [ha1.ne']
    calc l2 * (a1 + a2) + l3 * (a1 + a3)
      _ = (l2 + l3) * a1 + (l2 * a2 + l3 * a3) := by ring
      _ = (l2 + l3) * a1 + l1 * a1 := by rw [← hbal]
      _ = (l1 + l2 + l3) * a1 := by ring
      _ = a1 := by rw [hlsum, one_mul]
  have hp_w : μ2 • w2 + μ3 • w3 = p := by
    have h1 : μ2 * (a2 / Δ2) + μ3 * (a3 / Δ3) = l1 := by
      dsimp [μ2, μ3]; field_simp [ha1.ne', hΔ2.ne', hΔ3.ne']; linarith [hbal]
    have h2 : μ2 * (a1 / Δ2) = l2 := by
      dsimp [μ2]; field_simp [ha1.ne', hΔ2.ne']
    have h3 : μ3 * (a1 / Δ3) = l3 := by
      dsimp [μ3]; field_simp [ha1.ne', hΔ3.ne']
    rw [← hlp]; dsimp [w2, w3]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, h2, h3]
    calc (μ2 * (a2 / Δ2)) • v1 + l2 • v2 + ((μ3 * (a3 / Δ3)) • v1 + l3 • v3)
      _ = (μ2 * (a2 / Δ2) + μ3 * (a3 / Δ3)) • v1 + l2 • v2 + l3 • v3 := by rw [add_smul]; abel
      _ = l1 • v1 + l2 • v2 + l3 • v3 := by rw [h1]
  let d3_2 := s * orient2 (proj2 v1) (proj2 u2) (proj2 v2)
  let d4_2 := s * orient2 (proj2 u1) (proj2 v1) (proj2 v2)
  let d3_3 := s * orient2 (proj2 v1) (proj2 u2) (proj2 v3)
  let d4_3 := s * orient2 (proj2 u1) (proj2 v1) (proj2 v3)
  have hpl2 := orient2_plucker (proj2 u1) (proj2 v1) (proj2 u2) (proj2 v2)
  have hpl3 := orient2_plucker (proj2 u1) (proj2 v1) (proj2 u2) (proj2 v3)
  have hΔ2_eq : d3_2 + d4_2 = Δ2 := by
    have hs := congrArg (s * ·) hpl2.1; dsimp [d3_2, d4_2, Δ2, a1, a2]; linarith
  have hΔ3_eq : d3_3 + d4_3 = Δ3 := by
    have hs := congrArg (s * ·) hpl3.1; dsimp [d3_3, d4_3, Δ3, a1, a3]; linarith
  let u2' : ℝ^3 := (d3_2 / Δ2) • u1 + (d4_2 / Δ2) • u2
  let u3' : ℝ^3 := (d3_3 / Δ3) • u1 + (d4_3 / Δ3) • u2
  have hproj_u2' : proj2 u2' = proj2 w2 := by
    ext
    · change (d3_2 / Δ2) * (proj2 u1).1 + (d4_2 / Δ2) * (proj2 u2).1 =
        (a2 / Δ2) * (proj2 v1).1 + (a1 / Δ2) * (proj2 v2).1
      field_simp [hΔ2.ne']; have hs := congrArg (s * ·) hpl2.2.1; dsimp [d3_2, d4_2, a1, a2]; linarith
    · change (d3_2 / Δ2) * (proj2 u1).2 + (d4_2 / Δ2) * (proj2 u2).2 =
        (a2 / Δ2) * (proj2 v1).2 + (a1 / Δ2) * (proj2 v2).2
      field_simp [hΔ2.ne']; have hs := congrArg (s * ·) hpl2.2.2; dsimp [d3_2, d4_2, a1, a2]; linarith
  have hproj_u3' : proj2 u3' = proj2 w3 := by
    ext
    · change (d3_3 / Δ3) * (proj2 u1).1 + (d4_3 / Δ3) * (proj2 u2).1 =
        (a3 / Δ3) * (proj2 v1).1 + (a1 / Δ3) * (proj2 v3).1
      field_simp [hΔ3.ne']; have hs := congrArg (s * ·) hpl3.2.1; dsimp [d3_3, d4_3, a1, a3]; linarith
    · change (d3_3 / Δ3) * (proj2 u1).2 + (d4_3 / Δ3) * (proj2 u2).2 =
        (a3 / Δ3) * (proj2 v1).2 + (a1 / Δ3) * (proj2 v3).2
      field_simp [hΔ3.ne']; have hs := congrArg (s * ·) hpl3.2.2; dsimp [d3_3, d4_3, a1, a3]; linarith
  let u' : ℝ^3 := μ2 • u2' + μ3 • u3'
  have hproj_eq : proj2 u' = proj2 p := by
    rw [← hp_w]; dsimp [u']; rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul, hproj_u2', hproj_u3']
  let β1 := μ2 * (d3_2 / Δ2) + μ3 * (d3_3 / Δ3)
  let β2 := μ2 * (d4_2 / Δ2) + μ3 * (d4_3 / Δ3)
  have hβsum : β1 + β2 = 1 := by
    dsimp [β1, β2]
    calc μ2 * (d3_2 / Δ2) + μ3 * (d3_3 / Δ3) + (μ2 * (d4_2 / Δ2) + μ3 * (d4_3 / Δ3))
      _ = μ2 * ((d3_2 + d4_2) / Δ2) + μ3 * ((d3_3 + d4_3) / Δ3) := by ring
      _ = μ2 * 1 + μ3 * 1 := by rw [hΔ2_eq, hΔ3_eq, div_self hΔ2.ne', div_self hΔ3.ne']
      _ = 1 := by linarith
  have hu'_eq : u' = β1 • u1 + β2 • u2 := by
    dsimp [u', u2', u3', β1, β2]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, add_smul, add_smul]; abel
  have hαβ : β1 = α1 ∧ β2 = α2 := by
    have hdiff : (β1 - α1) • (proj2 u1 - proj2 u2) = 0 := by
      have h1 : β1 • proj2 u1 + β2 • proj2 u2 = α1 • proj2 u1 + α2 • proj2 u2 := by
        have := hproj_eq; rw [hu'_eq, ← hpU_eq, map_add, map_add, map_smul, map_smul, map_smul, map_smul] at this
        exact this
      have h2 : β2 - α2 = -(β1 - α1) := by linarith
      calc (β1 - α1) • (proj2 u1 - proj2 u2)
        _ = (β1 - α1) • proj2 u1 + (β2 - α2) • proj2 u2 := by rw [h2, smul_sub, neg_smul]; abel
        _ = (β1 • proj2 u1 + β2 • proj2 u2) - (α1 • proj2 u1 + α2 • proj2 u2) := by rw [sub_smul, sub_smul]; abel
        _ = 0 := by rw [h1, sub_self]
    have hne : proj2 u1 - proj2 u2 ≠ 0 := sub_ne_zero.mpr hu12
    have h0 : β1 - α1 = 0 := (smul_eq_zero.mp hdiff).resolve_right hne
    exact ⟨by linarith, by linarith⟩
  have hu'p : u' = p := by rw [hu'_eq, hαβ.1, hαβ.2, hpU_eq]
  have hz2 : 0 < σ * (u2' 2 - w2 2) := by
    have heq : σ * (u2' 2 - w2 2) = (σ * crossDiff s u1 v1 u2 v2) / Δ2 := by
      dsimp [u2', w2, d3_2, d4_2, a1, a2]; unfold crossDiff
      field_simp [hΔ2.ne']; ring
    rw [heq]; exact div_pos hcd2 hΔ2
  have hz3 : 0 < σ * (u3' 2 - w3 2) := by
    have heq : σ * (u3' 2 - w3 2) = (σ * crossDiff s u1 v1 u2 v3) / Δ3 := by
      dsimp [u3', w3, d3_3, d4_3, a1, a3]; unfold crossDiff
      field_simp [hΔ3.ne']; ring
    rw [heq]; exact div_pos hcd3 hΔ3
  have hzdiff : σ * (u' 2 - p 2) = μ2 * (σ * (u2' 2 - w2 2)) + μ3 * (σ * (u3' 2 - w3 2)) := by
    have hpz : p 2 = μ2 * w2 2 + μ3 * w3 2 := by rw [← hp_w]; rfl
    have huz : u' 2 = μ2 * u2' 2 + μ3 * u3' 2 := rfl
    rw [hpz, huz]; ring
  have hpos_sum : 0 < μ2 * (σ * (u2' 2 - w2 2)) + μ3 * (σ * (u3' 2 - w3 2)) := by
    by_cases hμ20 : μ2 = 0
    · have hμ31 : μ3 = 1 := by linarith
      rw [hμ20, hμ31, zero_mul, zero_add, one_mul]; exact hz3
    · have hμ2p : 0 < μ2 := lt_of_le_of_ne hμ2 (Ne.symm hμ20)
      exact add_pos_of_pos_of_nonneg (mul_pos hμ2p hz2) (mul_nonneg hμ3 hz3.le)
  rw [hu'p, sub_self, mul_zero] at hzdiff
  linarith

lemma cor_ab_of_consistent {k : ℕ} (hk : 4 ≤ k) (y : Fin k → ℝ^3) (s σ : ℝ)
    (hσpm : σ = 1 ∨ σ = -1)
    (hy_inj : Function.Injective y)
    (hy_gp : Erdos651.IsInGeneralPosition (Finset.univ.image y))
    (hy_ori : ∀ i j l : Fin k, i < j → j < l →
      0 < s * orient2 (proj2 (y i)) (proj2 (y j)) (proj2 (y l)))
    (hcd_all : ∀ i1 i2 i3 i4 : Fin k, i1 < i2 → i2 < i3 → i3 < i4 →
      0 < σ * crossDiff s (y i1) (y i2) (y i3) (y i4))
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (_hck : c ≤ k) :
    let I1 := (Finset.univ : Finset (Fin k)).filter fun i => i.1 < a ∨ (b ≤ i.1 ∧ i.1 < c)
    let I2 := (Finset.univ : Finset (Fin k)).filter fun i => (a ≤ i.1 ∧ i.1 < b) ∨ c ≤ i.1
    Disjoint (convexHull ℝ ((I1.image y : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ ((I2.image y : Finset (ℝ^3)) : Set (ℝ^3))) := by
  have hy_proj_inj : Function.Injective (proj2 ∘ y) := by
    intro i j hij
    by_contra hne
    have hex3 : ∃ l : Fin k, l ≠ i ∧ l ≠ j := by
      have hne_sd : (Finset.univ \ ({i, j} : Finset (Fin k))).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({i, j} : Finset (Fin k)))
        rw [Finset.card_univ, Fintype.card_fin] at this
        have := Finset.card_le_two (a := i) (b := j); omega
      obtain ⟨l, hl⟩ := hne_sd
      exact ⟨l, by simpa using (Finset.mem_sdiff.mp hl).2⟩
    obtain ⟨l, hli, hlj⟩ := hex3
    have hY_sing : ∀ i1 i2 i3 : Fin k, i1 < i2 → i2 < i3 →
        ∀ p ∈ ({proj2 (y i1)} : Finset _), ∀ q ∈ ({proj2 (y i2)} : Finset _), ∀ r ∈ ({proj2 (y i3)} : Finset _),
          0 < s * orient2 p q r := fun i1 i2 i3 h12 h23 p hp q hq r hr => by
      simp only [Finset.mem_singleton] at hp hq hr; subst hp; subst hq; subst hr
      exact hy_ori i1 i2 i3 h12 h23
    obtain ⟨t, ht⟩ := orient2_any_triple hY_sing hne hlj.symm hli.symm
    have hpos := ht (proj2 (y i)) (by simp) (proj2 (y j)) (by simp) (proj2 (y l)) (by simp)
    have heq : proj2 (y i) = proj2 (y j) := hij
    rw [heq] at hpos
    have h0 : orient2 (proj2 (y j)) (proj2 (y j)) (proj2 (y l)) = 0 := by unfold orient2; ring
    rw [h0, mul_zero] at hpos; exact lt_irrefl 0 hpos
  intro I1 I2
  rw [Set.disjoint_left]
  intro p0 hp01 hp02
  have hne : (convexHull ℝ ((I1.image y : Finset (ℝ^3)) : Set (ℝ^3)) ∩
      convexHull ℝ ((I2.image y : Finset (ℝ^3)) : Set (ℝ^3))).Nonempty := ⟨p0, hp01, hp02⟩
  obtain ⟨A', hA'sub, B', hB'sub, hcard5, p, hpA', hpB'⟩ := kirchberger (I1.image y) (I2.image y) hne
  rw [finrank_euclideanSpace_fin] at hcard5
  obtain ⟨JA, hJA1, hJAimg, hJAcard⟩ := finite_image_pullback y I1 A' hA'sub hy_inj.injOn
  obtain ⟨JB, hJB2, hJBimg, hJBcard⟩ := finite_image_pullback y I2 B' hB'sub hy_inj.injOn
  have hJdisj : Disjoint JA JB := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 := (Finset.mem_filter.mp (hJA1 hi1)).2
    have h2 := (Finset.mem_filter.mp (hJB2 hi2)).2
    omega
  have hA'ne : A'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpA'; exact hpA'
  have hB'ne : B'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpB'; exact hpB'
  have hsum5 : JA.card + JB.card = 5 := by
    by_contra hne5
    have hle4 : (JA ∪ JB).card ≤ 4 := by
      rw [Finset.card_union_of_disjoint hJdisj]; omega
    let Z := (JA ∪ JB).image y
    have hZsub : Z ⊆ Finset.univ.image y := Finset.image_subset_image (Finset.subset_univ _)
    have hZcard : Z.card ≤ 4 := (Finset.card_image_le).trans hle4
    have hZind : AffineIndependent ℝ (Subtype.val : ↥(Z : Set (ℝ^3)) → ℝ^3) := hy_gp Z hZsub hZcard
    have hA'Z : A' ⊆ Z := by rw [← hJAimg]; exact Finset.image_subset_image Finset.subset_union_left
    have hB'Z : B' ⊆ Z := by rw [← hJBimg]; exact Finset.image_subset_image Finset.subset_union_right
    have hABdisj : Disjoint A' B' := by
      rw [← hJAimg, ← hJBimg, Finset.disjoint_left]
      intro u hu1 hu2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu1
      obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hu2
      exact Finset.disjoint_left.mp hJdisj hi (hy_inj hij ▸ hj)
    rw [Finset.convexHull_eq] at hpA' hpB'
    obtain ⟨wA, hwA_nn, hwA_sum, hwA_cm⟩ := hpA'
    obtain ⟨wB, hwB_nn, hwB_sum, hwB_cm⟩ := hpB'
    rw [Finset.centerMass_eq_of_sum_1 _ _ hwA_sum] at hwA_cm
    rw [Finset.centerMass_eq_of_sum_1 _ _ hwB_sum] at hwB_cm
    simp only [id_eq] at hwA_cm hwB_cm
    let w : ↥(Z : Set (ℝ^3)) → ℝ := fun u =>
      (if u.1 ∈ A' then wA u.1 else 0) - (if u.1 ∈ B' then wB u.1 else 0)
    have hsum_coe {β : Type} [AddCommMonoid β] (f : ℝ^3 → β) :
        ∑ u : ↥(Z : Set (ℝ^3)), f u.1 = ∑ u ∈ Z, f u := by
      have heq := Fintype.sum_equiv (Equiv.subtypeEquivRight fun x => Finset.mem_coe (s := Z) (a := x))
        (fun u : ↥(Z : Set (ℝ^3)) => f u.1) (fun u : ↥Z => f u.1) (fun _ => rfl)
      exact heq.trans (Finset.sum_coe_sort Z f)
    have hwsum : ∑ u : ↥(Z : Set (ℝ^3)), w u = 0 := by
      have hA : ∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ A' then wA u.1 else 0) = 1 := by
        rw [hsum_coe (fun u => if u ∈ A' then wA u else 0),
          ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hA'Z, hwA_sum]
      have hB : ∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ B' then wB u.1 else 0) = 1 := by
        rw [hsum_coe (fun u => if u ∈ B' then wB u else 0),
          ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB'Z, hwB_sum]
      calc ∑ u : ↥(Z : Set (ℝ^3)), w u
        _ = (∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ A' then wA u.1 else 0)) -
            (∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ B' then wB u.1 else 0)) := Finset.sum_sub_distrib _ _
        _ = 1 - 1 := by rw [hA, hB]
        _ = 0 := sub_self 1
    have hwvsub : Finset.univ.weightedVSub (Subtype.val : ↥(Z : Set (ℝ^3)) → ℝ^3) w = 0 := by
      rw [Finset.weightedVSub_eq_linear_combination Finset.univ hwsum]
      simp only [w, sub_smul, Finset.sum_sub_distrib]
      have h1 : ∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ A' then wA u.1 else 0) • u.1 = p := by
        rw [hsum_coe (fun u => (if u ∈ A' then wA u else 0) • u)]
        have : ∀ u ∈ Z, (if u ∈ A' then wA u else 0) • u = if u ∈ A' then wA u • u else 0 :=
          fun u _ => by split_ifs <;> simp
        rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr hA'Z, hwA_cm]
      have h2 : ∑ u : ↥(Z : Set (ℝ^3)), (if u.1 ∈ B' then wB u.1 else 0) • u.1 = p := by
        rw [hsum_coe (fun u => (if u ∈ B' then wB u else 0) • u)]
        have : ∀ u ∈ Z, (if u ∈ B' then wB u else 0) • u = if u ∈ B' then wB u • u else 0 :=
          fun u _ => by split_ifs <;> simp
        rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr hB'Z, hwB_cm]
      rw [h1, h2, sub_self]
    have hall0 := hZind Finset.univ w hwsum hwvsub
    have hsumA0 : ∑ u ∈ A', wA u = 0 := by
      apply Finset.sum_eq_zero; intro u hu
      have h0 := hall0 ⟨u, hA'Z hu⟩ (Finset.mem_univ _)
      have huB : u ∉ B' := Finset.disjoint_left.mp hABdisj hu
      simpa [w, hu, huB] using h0
    linarith
  have h2d_cvx := orient2_convex_position (by omega) (fun i => ({proj2 (y i)} : Finset (ℝ × ℝ)))
    (fun i => Finset.singleton_nonempty _) s
    (fun i j l hij hjl p1 hp1 p2 hp2 p3 hp3 => by
      simp only [Finset.mem_singleton] at hp1 hp2 hp3; subst hp1; subst hp2; subst hp3
      exact hy_ori i j l hij hjl)
  have hno1 (J1 J2 : Finset (Fin k)) (hdisj12 : Disjoint J1 J2) (hJ1card : J1.card = 1)
      (hp1 : p ∈ convexHull ℝ ((J1.image y : Finset (ℝ^3)) : Set (ℝ^3)))
      (hp2 : p ∈ convexHull ℝ ((J2.image y : Finset (ℝ^3)) : Set (ℝ^3))) : False := by
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ1card
    have hp_j : proj2 p ∈ convexHull ℝ ((({proj2 (y j)} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) := by
      have : p = y j := by simpa [convexHull_singleton] using hp1
      rw [this]; exact subset_convexHull ℝ _ (by simp)
    have hp_rest : proj2 p ∈ convexHull ℝ
        (((Finset.univ.erase j).biUnion fun i => ({proj2 (y i)} : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      have h1 : proj2 p ∈ proj2 '' convexHull ℝ ((J2.image y : Finset (ℝ^3)) : Set (ℝ^3)) := ⟨p, hp2, rfl⟩
      rw [LinearMap.image_convexHull] at h1
      apply convexHull_mono _ h1
      rintro q ⟨u, hu, rfl⟩
      obtain ⟨i, hi2, rfl⟩ := Finset.mem_image.mp hu
      have hij : i ≠ j := fun h => Finset.disjoint_left.mp hdisj12 (by simp) (h ▸ hi2)
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩, by simp⟩)
    exact Set.disjoint_left.mp (h2d_cvx j) hp_j hp_rest
  have hJA_ge2 : 2 ≤ JA.card := by
    by_contra! hlt
    have hJA1 : JA.card = 1 := by have := Finset.card_pos.mpr hA'ne; omega
    exact hno1 JA JB hJdisj hJA1 (hJAimg.symm ▸ hpA') (hJBimg.symm ▸ hpB')
  have hJB_ge2 : 2 ≤ JB.card := by
    by_contra! hlt
    have hJB1 : JB.card = 1 := by have := Finset.card_pos.mpr hB'ne; omega
    exact hno1 JB JA hJdisj.symm hJB1 (hJBimg.symm ▸ hpB') (hJAimg.symm ▸ hpA')
  have hseg_sep (r1 r2 : Fin k) (hr12 : r1 < r2) (T : Finset (Fin k))
      (hTside : (∀ t ∈ T, r1 < t ∧ t < r2) ∨ (∀ t ∈ T, t < r1 ∨ r2 < t))
      (hpU : p ∈ convexHull ℝ ({y r1, y r2} : Set (ℝ^3)))
      (hpT : p ∈ convexHull ℝ ((T.image y : Finset (ℝ^3)) : Set (ℝ^3))) : False := by
    have hsign : ∃ sg : ℝ, ∀ t ∈ T, 0 < sg * orient2 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t)) := by
      rcases hTside with hin | hout
      · refine ⟨-s, fun t ht => ?_⟩
        have h0 := hy_ori r1 t r2 (hin t ht).1 (hin t ht).2
        rw [orient2_swap23 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t))] at h0; linarith
      · refine ⟨s, fun t ht => ?_⟩
        rcases hout t ht with hlt | hgt
        · have h0 := hy_ori t r1 r2 hlt hr12
          rw [orient2_cyc2 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t))] at h0; exact h0
        · exact hy_ori r1 r2 t hr12 hgt
    obtain ⟨sg, hsg⟩ := hsign
    let q1 := proj2 (y r1)
    let q2 := proj2 (y r2)
    let f : (ℝ^3) →ₗ[ℝ] ℝ :=
      { toFun := fun u => sg * ((q2.1 - q1.1) * (proj2 u).2 - (q2.2 - q1.2) * (proj2 u).1)
        map_add' := fun u v => by simp [proj2]; ring
        map_smul' := fun c u => by simp [proj2]; ring }
    let d0 : ℝ := sg * ((q2.1 - q1.1) * q1.2 - (q2.2 - q1.2) * q1.1)
    have hf_eq : ∀ u, sg * orient2 q1 q2 (proj2 u) = f u - d0 := fun u => by
      dsimp [f, d0, q1, q2]; unfold orient2; ring
    have hsubT : convexHull ℝ ((T.image y : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ {u | d0 < f u} := by
      apply convexHull_min _ (convex_halfSpace_gt f.isLinear d0)
      intro u hu; obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      change d0 < f (y t); have := hsg t ht; rw [hf_eq] at this; linarith
    have hsubU : convexHull ℝ ({y r1, y r2} : Set (ℝ^3)) ⊆ {u | f u ≤ d0} := by
      apply convexHull_min _ (convex_halfSpace_le f.isLinear d0)
      intro u hu; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      change f u ≤ d0
      rcases hu with rfl | rfl
      · have h0 : sg * orient2 q1 q2 q1 = 0 := by unfold orient2; ring
        rw [hf_eq] at h0; linarith
      · have h0 : sg * orient2 q1 q2 q2 = 0 := by unfold orient2; ring
        rw [hf_eq] at h0; linarith
    have hgt : d0 < f p := hsubT hpT
    have hle : f p ≤ d0 := hsubU hpU
    linarith
  have hcall (u1 u2 v1 v2 v3 : Fin k) (hu12 : u1 ≠ u2)
      (ho1 : 0 < s * orient2 (proj2 (y u1)) (proj2 (y v1)) (proj2 (y u2)))
      (ho2 : 0 < s * orient2 (proj2 (y u1)) (proj2 (y u2)) (proj2 (y v2)))
      (ho3 : 0 < s * orient2 (proj2 (y u1)) (proj2 (y u2)) (proj2 (y v3)))
      (ho12 : 0 < s * orient2 (proj2 (y v1)) (proj2 (y u2)) (proj2 (y v2)))
      (ho12' : 0 < s * orient2 (proj2 (y u1)) (proj2 (y v1)) (proj2 (y v2)))
      (ho13 : 0 < s * orient2 (proj2 (y v1)) (proj2 (y u2)) (proj2 (y v3)))
      (ho13' : 0 < s * orient2 (proj2 (y u1)) (proj2 (y v1)) (proj2 (y v3)))
      (σ' : ℝ) (hσ' : σ' = 1 ∨ σ' = -1)
      (hcd2 : 0 < σ' * crossDiff s (y u1) (y v1) (y u2) (y v2))
      (hcd3 : 0 < σ' * crossDiff s (y u1) (y v1) (y u2) (y v3))
      (hpu' : p ∈ convexHull ℝ ({y u1, y u2} : Set (ℝ^3)))
      (hpv' : p ∈ convexHull ℝ ({y v1, y v2, y v3} : Set (ℝ^3))) : False :=
    Set.disjoint_left.mp
      (seg_tri_disjoint_of_above hσ' (fun h => hu12 (hy_proj_inj h)) ho1 ho2 ho3 ho12 ho12' ho13 ho13' hcd2 hcd3)
      hpu' hpv'
  have hσ_neg : -σ = 1 ∨ -σ = -1 := by rcases hσpm with h | h <;> [right; left] <;> linarith
  have sort2 (S : Finset (Fin k)) (hS : S.card = 2) :
      ∃ r1 r2 : Fin k, r1 < r2 ∧ S = {r1, r2} := by
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨u, v, h, rfl⟩
    · exact ⟨v, u, h, Finset.pair_comm u v⟩
  have sort3 (S : Finset (Fin k)) (hS : S.card = 3) :
      ∃ t1 t2 t3 : Fin k, t1 < t2 ∧ t2 < t3 ∧ S = {t1, t2, t3} := by
    let e : Fin 3 ≃o S := S.orderIsoOfFin hS
    refine ⟨(e 0).1, (e 1).1, (e 2).1, e.strictMono (by decide), e.strictMono (by decide), ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      obtain ⟨r, hr⟩ : ∃ r : Fin 3, e r = ⟨z, hz⟩ := ⟨e.symm ⟨z, hz⟩, e.apply_symm_apply _⟩
      fin_cases r
      · left; exact congrArg Subtype.val hr.symm
      · right; left; exact congrArg Subtype.val hr.symm
      · right; right; exact congrArg Subtype.val hr.symm
    · rintro (rfl | rfl | rfl) <;> exact (e _).2
  have hJA_cases : JA.card = 2 ∧ JB.card = 3 ∨ JA.card = 3 ∧ JB.card = 2 := by omega
  rcases hJA_cases with ⟨hJA2c, hJB3c⟩ | ⟨hJA3c, hJB2c⟩
  · obtain ⟨r1, r2, hr12, hJAeq⟩ := sort2 JA hJA2c
    obtain ⟨t1, t2, t3, ht12, ht23, hJBeq⟩ := sort3 JB hJB3c
    have hr1I1 : r1.1 < a ∨ (b ≤ r1.1 ∧ r1.1 < c) := (Finset.mem_filter.mp (hJA1 (hJAeq ▸ by simp))).2
    have hr2I1 : r2.1 < a ∨ (b ≤ r2.1 ∧ r2.1 < c) := (Finset.mem_filter.mp (hJA1 (hJAeq ▸ by simp))).2
    have hpU : p ∈ convexHull ℝ ({y r1, y r2} : Set (ℝ^3)) := by
      have h1 : A' = {y r1, y r2} := by rw [← hJAimg, hJAeq]; simp
      rw [h1] at hpA'; simpa using hpA'
    have hpV_set : p ∈ convexHull ℝ ((JB.image y : Finset (ℝ^3)) : Set (ℝ^3)) := hJBimg.symm ▸ hpB'
    have hpV : p ∈ convexHull ℝ ({y t1, y t2, y t3} : Set (ℝ^3)) := by
      have h1 : B' = {y t1, y t2, y t3} := by rw [← hJBimg, hJBeq]; simp
      rw [h1] at hpB'; simpa using hpB'
    have hr1a : r1.1 < a := by
      rcases hr1I1 with h | h
      · exact h
      · exfalso
        have hr2bc : b ≤ r2.1 ∧ r2.1 < c := by
          rcases hr2I1 with h2 | h2
          · have : r1.1 < r2.1 := hr12; omega
          · exact h2
        apply hseg_sep r1 r2 hr12 JB (Or.inr fun t ht => ?_) hpU hpV_set
        have htI2 := (Finset.mem_filter.mp (hJB2 ht)).2
        rcases htI2 with ⟨_, htb⟩ | hct
        · left; change t.1 < r1.1; omega
        · right; change r2.1 < t.1; omega
    have hr2bc : b ≤ r2.1 ∧ r2.1 < c := by
      rcases hr2I1 with h | h
      · exfalso
        apply hseg_sep r1 r2 hr12 JB (Or.inr fun t ht => ?_) hpU hpV_set
        have htI2 := (Finset.mem_filter.mp (hJB2 ht)).2
        right; change r2.1 < t.1; omega
      · exact h
    have htI2 (t : Fin k) (ht : t ∈ JB) : (r1 < t ∧ t < r2) ∨ r2 < t := by
      have h0 := (Finset.mem_filter.mp (hJB2 ht)).2
      rcases h0 with ⟨h1, h2⟩ | h3
      · left; exact ⟨show r1.1 < t.1 by omega, show t.1 < r2.1 by omega⟩
      · right; exact show r2.1 < t.1 by omega
    have ht1_in : r1 < t1 ∧ t1 < r2 := by
      rcases htI2 t1 (hJBeq ▸ by simp) with h | h
      · exact h
      · exfalso
        apply hseg_sep r1 r2 hr12 JB (Or.inr fun t ht => ?_) hpU hpV_set
        rw [hJBeq] at ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inr h
        · exact Or.inr (h.trans ht12)
        · exact Or.inr (h.trans (ht12.trans ht23))
    have ht3_out : r2 < t3 := by
      rcases htI2 t3 (hJBeq ▸ by simp) with h | h
      · exfalso
        apply hseg_sep r1 r2 hr12 JB (Or.inl fun t ht => ?_) hpU hpV_set
        rw [hJBeq] at ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact ht1_in
        · exact ⟨ht1_in.1.trans ht12, ht23.trans h.2⟩
        · exact h
      · exact h
    rcases htI2 t2 (hJBeq ▸ by simp) with ⟨_, ht2_lt⟩ | ht2_gt
    · have hpU' : p ∈ convexHull ℝ ({y r2, y r1} : Set (ℝ^3)) := by rwa [Set.pair_comm]
      have hpV' : p ∈ convexHull ℝ ({y t3, y t1, y t2} : Set (ℝ^3)) := by rwa [← set_triple_rot]
      exact hcall r2 r1 t3 t1 t2 hr12.ne'
        (by rw [orient2_cyc (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t3))]; exact hy_ori r1 r2 t3 hr12 ht3_out)
        (by rw [orient2_swap12 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t1)),
               orient2_swap23 (proj2 (y r1)) (proj2 (y t1)) (proj2 (y r2)), neg_neg]
            exact hy_ori r1 t1 r2 ht1_in.1 ht1_in.2)
        (by rw [orient2_swap12 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t2)),
               orient2_swap23 (proj2 (y r1)) (proj2 (y t2)) (proj2 (y r2)), neg_neg]
            exact hy_ori r1 t2 r2 (ht1_in.1.trans ht12) ht2_lt)
        (by rw [orient2_cyc2 (proj2 (y r1)) (proj2 (y t1)) (proj2 (y t3))]
            exact hy_ori r1 t1 t3 ht1_in.1 (ht1_in.2.trans ht3_out))
        (by rw [orient2_cyc (proj2 (y t1)) (proj2 (y r2)) (proj2 (y t3))]
            exact hy_ori t1 r2 t3 ht1_in.2 ht3_out)
        (by rw [orient2_cyc2 (proj2 (y r1)) (proj2 (y t2)) (proj2 (y t3))]
            exact hy_ori r1 t2 t3 (ht1_in.1.trans ht12) (ht2_lt.trans ht3_out))
        (by rw [orient2_cyc (proj2 (y t2)) (proj2 (y r2)) (proj2 (y t3))]
            exact hy_ori t2 r2 t3 ht2_lt ht3_out)
        σ hσpm
        (by rw [crossDiff_rot2]; exact hcd_all r1 t1 r2 t3 ht1_in.1 ht1_in.2 ht3_out)
        (by rw [crossDiff_rot2]; exact hcd_all r1 t2 r2 t3 (ht1_in.1.trans ht12) ht2_lt ht3_out)
        hpU' hpV'
    · exact hcall r1 r2 t1 t2 t3 hr12.ne
        (hy_ori r1 t1 r2 ht1_in.1 ht1_in.2)
        (hy_ori r1 r2 t2 hr12 ht2_gt)
        (hy_ori r1 r2 t3 hr12 ht3_out)
        (hy_ori t1 r2 t2 ht1_in.2 ht2_gt)
        (hy_ori r1 t1 t2 ht1_in.1 (ht1_in.2.trans ht2_gt))
        (hy_ori t1 r2 t3 ht1_in.2 ht3_out)
        (hy_ori r1 t1 t3 ht1_in.1 (ht1_in.2.trans ht3_out))
        σ hσpm
        (hcd_all r1 t1 r2 t2 ht1_in.1 ht1_in.2 ht2_gt)
        (hcd_all r1 t1 r2 t3 ht1_in.1 ht1_in.2 ht3_out)
        hpU hpV
  · obtain ⟨r1, r2, hr12, hJBeq⟩ := sort2 JB hJB2c
    obtain ⟨t1, t2, t3, ht12, ht23, hJAeq⟩ := sort3 JA hJA3c
    have hr1I2 : (a ≤ r1.1 ∧ r1.1 < b) ∨ c ≤ r1.1 := (Finset.mem_filter.mp (hJB2 (hJBeq ▸ by simp))).2
    have hr2I2 : (a ≤ r2.1 ∧ r2.1 < b) ∨ c ≤ r2.1 := (Finset.mem_filter.mp (hJB2 (hJBeq ▸ by simp))).2
    have hpU : p ∈ convexHull ℝ ({y r1, y r2} : Set (ℝ^3)) := by
      have h1 : B' = {y r1, y r2} := by rw [← hJBimg, hJBeq]; simp
      rw [h1] at hpB'; simpa using hpB'
    have hpV_set : p ∈ convexHull ℝ ((JA.image y : Finset (ℝ^3)) : Set (ℝ^3)) := hJAimg.symm ▸ hpA'
    have hpV : p ∈ convexHull ℝ ({y t1, y t2, y t3} : Set (ℝ^3)) := by
      have h1 : A' = {y t1, y t2, y t3} := by rw [← hJAimg, hJAeq]; simp
      rw [h1] at hpA'; simpa using hpA'
    have hr1ab : a ≤ r1.1 ∧ r1.1 < b := by
      rcases hr1I2 with h | h
      · exact h
      · exfalso
        apply hseg_sep r1 r2 hr12 JA (Or.inr fun t ht => ?_) hpU hpV_set
        have htI1 := (Finset.mem_filter.mp (hJA1 ht)).2
        left; change t.1 < r1.1; omega
    have hr2c : c ≤ r2.1 := by
      rcases hr2I2 with h | h
      · exfalso
        apply hseg_sep r1 r2 hr12 JA (Or.inr fun t ht => ?_) hpU hpV_set
        have htI1 := (Finset.mem_filter.mp (hJA1 ht)).2
        rcases htI1 with hta | ⟨hbt, _⟩
        · left; change t.1 < r1.1; omega
        · right; change r2.1 < t.1; omega
      · exact h
    have htI1 (t : Fin k) (ht : t ∈ JA) : t < r1 ∨ (r1 < t ∧ t < r2) := by
      have h0 := (Finset.mem_filter.mp (hJA1 ht)).2
      rcases h0 with h1 | ⟨h2, h3⟩
      · left; exact show t.1 < r1.1 by omega
      · right; exact ⟨show r1.1 < t.1 by omega, show t.1 < r2.1 by omega⟩
    have ht1_lt : t1 < r1 := by
      rcases htI1 t1 (hJAeq ▸ by simp) with h | h
      · exact h
      · exfalso
        apply hseg_sep r1 r2 hr12 JA (Or.inl fun t ht => ?_) hpU hpV_set
        have ht_in := htI1 t ht
        rw [hJAeq] at ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact h
        · rcases ht_in with h2 | h2
          · exact absurd (h.1.trans (ht12.trans h2)) (lt_irrefl _)
          · exact h2
        · rcases ht_in with h3 | h3
          · exact absurd (h.1.trans ((ht12.trans ht23).trans h3)) (lt_irrefl _)
          · exact h3
    have ht3_in : r1 < t3 ∧ t3 < r2 := by
      rcases htI1 t3 (hJAeq ▸ by simp) with h | h
      · exfalso
        apply hseg_sep r1 r2 hr12 JA (Or.inr fun t ht => ?_) hpU hpV_set
        rw [hJAeq] at ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · exact Or.inl ht1_lt
        · exact Or.inl (ht23.trans h)
        · exact Or.inl h
      · exact h
    rcases htI1 t2 (hJAeq ▸ by simp) with ht2_lt | ⟨ht2_gt, ht2_r2⟩
    · have hpV' : p ∈ convexHull ℝ ({y t3, y t1, y t2} : Set (ℝ^3)) := by rwa [← set_triple_rot]
      exact hcall r1 r2 t3 t1 t2 hr12.ne
        (hy_ori r1 t3 r2 ht3_in.1 ht3_in.2)
        (by rw [orient2_cyc (proj2 (y t1)) (proj2 (y r1)) (proj2 (y r2))]; exact hy_ori t1 r1 r2 ht1_lt hr12)
        (by rw [orient2_cyc (proj2 (y t2)) (proj2 (y r1)) (proj2 (y r2))]; exact hy_ori t2 r1 r2 ht2_lt hr12)
        (by rw [orient2_cyc (proj2 (y t1)) (proj2 (y t3)) (proj2 (y r2))]; exact hy_ori t1 t3 r2 (ht1_lt.trans ht3_in.1) ht3_in.2)
        (by rw [orient2_cyc (proj2 (y t1)) (proj2 (y r1)) (proj2 (y t3))]; exact hy_ori t1 r1 t3 ht1_lt ht3_in.1)
        (by rw [orient2_cyc (proj2 (y t2)) (proj2 (y t3)) (proj2 (y r2))]; exact hy_ori t2 t3 r2 (ht2_lt.trans ht3_in.1) ht3_in.2)
        (by rw [orient2_cyc (proj2 (y t2)) (proj2 (y r1)) (proj2 (y t3))]; exact hy_ori t2 r1 t3 ht2_lt ht3_in.1)
        (-σ) hσ_neg
        (by rw [crossDiff_rot1]; have := hcd_all t1 r1 t3 r2 ht1_lt ht3_in.1 ht3_in.2; linarith)
        (by rw [crossDiff_rot1]; have := hcd_all t2 r1 t3 r2 ht2_lt ht3_in.1 ht3_in.2; linarith)
        hpU hpV'
    · have hpU' : p ∈ convexHull ℝ ({y r2, y r1} : Set (ℝ^3)) := by rwa [Set.pair_comm]
      exact hcall r2 r1 t1 t2 t3 hr12.ne'
        (by rw [orient2_cyc2 (proj2 (y t1)) (proj2 (y r1)) (proj2 (y r2))]; exact hy_ori t1 r1 r2 ht1_lt hr12)
        (by rw [orient2_swap12 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t2)),
               orient2_swap23 (proj2 (y r1)) (proj2 (y t2)) (proj2 (y r2)), neg_neg]
            exact hy_ori r1 t2 r2 ht2_gt ht2_r2)
        (by rw [orient2_swap12 (proj2 (y r1)) (proj2 (y r2)) (proj2 (y t3)),
               orient2_swap23 (proj2 (y r1)) (proj2 (y t3)) (proj2 (y r2)), neg_neg]
            exact hy_ori r1 t3 r2 ht3_in.1 ht3_in.2)
        (hy_ori t1 r1 t2 ht1_lt ht2_gt)
        (by rw [orient2_cyc2 (proj2 (y t1)) (proj2 (y t2)) (proj2 (y r2))]; exact hy_ori t1 t2 r2 (ht1_lt.trans ht2_gt) ht2_r2)
        (hy_ori t1 r1 t3 ht1_lt ht3_in.1)
        (by rw [orient2_cyc2 (proj2 (y t1)) (proj2 (y t3)) (proj2 (y r2))]; exact hy_ori t1 t3 r2 (ht1_lt.trans ht3_in.1) ht3_in.2)
        (-σ) hσ_neg
        (by have hrot : crossDiff s (y r2) (y t1) (y r1) (y t2) = - crossDiff s (y t1) (y r1) (y t2) (y r2) := by
              rw [← crossDiff_rot2, crossDiff_rot1]
            rw [hrot]; have := hcd_all t1 r1 t2 r2 ht1_lt ht2_gt ht2_r2; linarith)
        (by have hrot : crossDiff s (y r2) (y t1) (y r1) (y t3) = - crossDiff s (y t1) (y r1) (y t3) (y r2) := by
              rw [← crossDiff_rot2, crossDiff_rot1]
            rw [hrot]; have := hcd_all t1 r1 t3 r2 ht1_lt ht3_in.1 ht3_in.2; linarith)
        hpU' hpV

lemma above_below_ramsey (k : ℕ) (hk : 4 ≤ k) :
    ∃ k₀ : ℕ, 4 ≤ k₀ ∧ ∀ (x : Fin k₀ → ℝ^3) (s : ℝ),
      (s = 1 ∨ s = -1) →
      Function.Injective x →
      Erdos651.IsInGeneralPosition (Finset.univ.image x) →
      (∀ i j l : Fin k₀, i < j → j < l →
        0 < s * orient2 (proj2 (x i)) (proj2 (x j)) (proj2 (x l))) →
      ∃ idx : Fin k → Fin k₀, StrictMono idx ∧
        ∀ (a b c : ℕ), a ≤ b → b ≤ c → c ≤ k →
          let I1 := (Finset.univ : Finset (Fin k)).filter fun i => i.1 < a ∨ (b ≤ i.1 ∧ i.1 < c)
          let I2 := (Finset.univ : Finset (Fin k)).filter fun i => (a ≤ i.1 ∧ i.1 < b) ∨ c ≤ i.1
          Disjoint (convexHull ℝ ((I1.image (x ∘ idx) : Finset (ℝ^3)) : Set (ℝ^3)))
            (convexHull ℝ ((I2.image (x ∘ idx) : Finset (ℝ^3)) : Set (ℝ^3))) := by
  obtain ⟨N, hN⟩ := finite_ramsey_sets (α := ℕ) 4 k
  let k₀ := max N 4
  refine ⟨k₀, le_max_right _ _, fun x s hspm hxinj hgp hori => ?_⟩
  let col : Finset ℕ → Bool := fun A =>
    if hA : A.card = 4 ∧ A ⊆ Finset.range k₀ then
      let e : Fin 4 ≃o A := A.orderIsoOfFin hA.1
      let f : Fin 4 → Fin k₀ := fun r => ⟨(e r).1, Finset.mem_range.mp (hA.2 (e r).2)⟩
      decide (0 < crossDiff s (x (f 0)) (x (f 1)) (x (f 2)) (x (f 3)))
    else false
  obtain ⟨Y, hYsub, hYcard, colb, hmono⟩ := hN (Finset.range k₀) (by rw [Finset.card_range]; exact le_max_left _ _) col
  let eY : Fin k ≃o Y := Y.orderIsoOfFin hYcard
  let idx : Fin k → Fin k₀ := fun i => ⟨(eY i).1, Finset.mem_range.mp (hYsub (eY i).2)⟩
  have hidx_mono : StrictMono idx := fun i j hij => eY.strictMono hij
  let y : Fin k → ℝ^3 := x ∘ idx
  have hy_ori : ∀ i j l : Fin k, i < j → j < l →
      0 < s * orient2 (proj2 (y i)) (proj2 (y j)) (proj2 (y l)) :=
    fun i j l hij hjl => hori _ _ _ (hidx_mono hij) (hidx_mono hjl)
  have hy_inj : Function.Injective y := hxinj.comp hidx_mono.injective
  have hy_gp : Erdos651.IsInGeneralPosition (Finset.univ.image y) := by
    intro Z hZ hZc
    have hsub : Finset.univ.image y ⊆ Finset.univ.image x := by
      intro u hu; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_image.mpr ⟨idx i, Finset.mem_univ _, rfl⟩
    exact hgp Z (hZ.trans hsub) hZc
  let σ : ℝ := if colb then 1 else -1
  have hσpm : σ = 1 ∨ σ = -1 := by dsimp [σ]; cases colb <;> simp
  have hcd_all : ∀ i1 i2 i3 i4 : Fin k, i1 < i2 → i2 < i3 → i3 < i4 →
      0 < σ * crossDiff s (y i1) (y i2) (y i3) (y i4) := by
    intro i1 i2 i3 i4 h12 h23 h34
    let A : Finset ℕ := {(idx i1).1, (idx i2).1, (idx i3).1, (idx i4).1}
    have hlt12 : (idx i1).1 < (idx i2).1 := hidx_mono h12
    have hlt23 : (idx i2).1 < (idx i3).1 := hidx_mono h23
    have hlt34 : (idx i3).1 < (idx i4).1 := hidx_mono h34
    have hAsubY : A ⊆ Y := by
      intro z hz; simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact (eY _).2
    have hAsubR : A ⊆ Finset.range k₀ := hAsubY.trans hYsub
    have hAcard : A.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp; omega
      · simp; omega
      · simp; omega
    have hcolA : col A = colb := hmono A hAsubY hAcard
    dsimp only [col] at hcolA
    rw [dif_pos ⟨hAcard, hAsubR⟩] at hcolA
    let g : Fin 4 → A := ![⟨(idx i1).1, by simp [A]⟩, ⟨(idx i2).1, by simp [A]⟩,
      ⟨(idx i3).1, by simp [A]⟩, ⟨(idx i4).1, by simp [A]⟩]
    have hg_mono : StrictMono g := by
      intro a b hab
      change (g a).1 < (g b).1
      fin_cases a <;> fin_cases b <;> dsimp [g]
      all_goals first
        | exact hlt12
        | exact hlt23
        | exact hlt34
        | exact hlt12.trans hlt23
        | exact hlt23.trans hlt34
        | exact (hlt12.trans hlt23).trans hlt34
        | (exfalso; revert hab; decide)
    have hg_bij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_mono.injective, by rw [Fintype.card_fin, Fintype.card_coe, hAcard]⟩
    let eg : Fin 4 ≃o A := OrderIso.ofRelIsoLT ⟨Equiv.ofBijective g hg_bij, hg_mono.lt_iff_lt⟩
    have heq_iso : A.orderIsoOfFin hAcard = eg := by
      have h1 : (eg.trans (A.orderIsoOfFin hAcard).symm : Fin 4 ≃o Fin 4) = OrderIso.refl (Fin 4) :=
        Subsingleton.elim _ _
      ext r
      have h2 := congrArg (fun φ : Fin 4 ≃o Fin 4 => (A.orderIsoOfFin hAcard) (φ r)) h1
      change (A.orderIsoOfFin hAcard) ((A.orderIsoOfFin hAcard).symm (eg r)) = (A.orderIsoOfFin hAcard) r at h2
      rw [OrderIso.apply_symm_apply] at h2
      exact congrArg Subtype.val h2.symm
    have hf_eq (r : Fin 4) : (⟨((A.orderIsoOfFin hAcard) r).1, Finset.mem_range.mp (hAsubR ((A.orderIsoOfFin hAcard) r).2)⟩ : Fin k₀) =
        ![idx i1, idx i2, idx i3, idx i4] r := by
      ext; rw [heq_iso]; fin_cases r <;> rfl
    have hcd_eq : crossDiff s
        (x ⟨((A.orderIsoOfFin hAcard) 0).1, Finset.mem_range.mp (hAsubR ((A.orderIsoOfFin hAcard) 0).2)⟩)
        (x ⟨((A.orderIsoOfFin hAcard) 1).1, Finset.mem_range.mp (hAsubR ((A.orderIsoOfFin hAcard) 1).2)⟩)
        (x ⟨((A.orderIsoOfFin hAcard) 2).1, Finset.mem_range.mp (hAsubR ((A.orderIsoOfFin hAcard) 2).2)⟩)
        (x ⟨((A.orderIsoOfFin hAcard) 3).1, Finset.mem_range.mp (hAsubR ((A.orderIsoOfFin hAcard) 3).2)⟩) =
        crossDiff s (y i1) (y i2) (y i3) (y i4) := by
      rw [hf_eq 0, hf_eq 1, hf_eq 2, hf_eq 3]; rfl
    have hcd_ne : crossDiff s (y i1) (y i2) (y i3) (y i4) ≠ 0 := by
      let Z : Finset (ℝ^3) := {y i1, y i2, y i3, y i4}
      have hZsub : Z ⊆ Finset.univ.image x := by
        intro u hu; simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      have hZcard : Z.card ≤ 4 := by
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_two)))
      have hZind : AffineIndependent ℝ (Subtype.val : ↥(Z : Set (ℝ^3)) → ℝ^3) := hgp Z hZsub hZcard
      let w4 : Fin 4 → ↥(Z : Set (ℝ^3)) :=
        ![⟨y i1, by simp [Z]⟩, ⟨y i2, by simp [Z]⟩, ⟨y i3, by simp [Z]⟩, ⟨y i4, by simp [Z]⟩]
      have hw4_inj : Function.Injective w4 := by
        intro a b hab
        have hval := congrArg Subtype.val hab
        fin_cases a <;> fin_cases b <;> dsimp [w4] at hval
        all_goals first
          | rfl
          | (exfalso; have := hy_inj hval; exact absurd this (by omega))
      have hind4 : AffineIndependent ℝ ![y i1, y i2, y i3, y i4] := by
        have h1 := hZind.comp_embedding ⟨w4, hw4_inj⟩
        change AffineIndependent ℝ (Subtype.val ∘ w4) at h1
        have hcomp : (Subtype.val ∘ w4) = ![y i1, y i2, y i3, y i4] := by ext r; fin_cases r <;> rfl
        rwa [hcomp] at h1
      exact crossDiff_ne_zero hind4 (hy_ori i2 i3 i4 h23 h34).ne'
    dsimp [σ]
    cases hcb : colb
    · rw [hcb] at hcolA
      have hnot : ¬ (0 < crossDiff s (y i1) (y i2) (y i3) (y i4)) := by
        rw [← hcd_eq]; exact of_decide_eq_false hcolA
      have hlt : crossDiff s (y i1) (y i2) (y i3) (y i4) < 0 := lt_of_le_of_ne (not_lt.mp hnot) hcd_ne
      simp; linarith
    · rw [hcb] at hcolA
      have hpos : 0 < crossDiff s (y i1) (y i2) (y i3) (y i4) := by
        rw [← hcd_eq]; exact of_decide_eq_true hcolA
      simp; exact hpos
  exact ⟨idx, hidx_mono, fun a b c hab hbc hck => cor_ab_of_consistent hk y s σ hσpm hy_inj hy_gp hy_ori hcd_all a b c hab hbc hck⟩

lemma sep_transfer_3d {k : ℕ} (X : Fin k → Finset (ℝ^3))
    (x : Fin k → ℝ^3) (hx : ∀ i, x i ∈ X i)
    (hcvx : ∀ j : Fin k, Disjoint (convexHull ℝ (X j : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ.erase j).biUnion X : Finset (ℝ^3)) : Set (ℝ^3))))
    (h2sep : ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      Disjoint (convexHull ℝ ((X i ∪ X j : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((X i' ∪ X j' : Finset (ℝ^3)) : Set (ℝ^3))))
    (Spos : Finset (Fin k))
    (hrep_sep : Disjoint (convexHull ℝ ((Spos.image x : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ \ Spos).image x : Finset (ℝ^3)) : Set (ℝ^3)))) :
    Disjoint (convexHull ℝ ((Spos.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ \ Spos).biUnion X : Finset (ℝ^3)) : Set (ℝ^3))) := by
  let Sneg := Finset.univ \ Spos
  -- Core asymmetric helper: 2 points from one side cannot intersect 3 points from the other!
  have h23_contra (P Q : Finset (Fin k)) (hPQdisj : Disjoint P Q)
      (hPQrep : Disjoint (convexHull ℝ ((P.image x : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((Q.image x : Finset (ℝ^3)) : Set (ℝ^3))))
      (i1 i2 : Fin k) (hi1 : i1 ∈ P) (hi2 : i2 ∈ P)
      (j1 j2 j3 : Fin k) (hj1 : j1 ∈ Q) (hj2 : j2 ∈ Q) (hj3 : j3 ∈ Q)
      (y1 y2 y3 y4 y5 : ℝ^3)
      (hy1 : y1 ∈ X i1) (hy2 : y2 ∈ X i2) (hy3 : y3 ∈ X j1) (hy4 : y4 ∈ X j2) (hy5 : y5 ∈ X j3)
      (hinter : (convexHull ℝ ({y1, y2} : Set (ℝ^3)) ∩ convexHull ℝ ({y3, y4, y5} : Set (ℝ^3))).Nonempty) :
      False := by
    have hne_ij : ∀ i ∈ P, ∀ j ∈ Q, i ≠ j := fun i hi j hj heq =>
      Finset.disjoint_left.mp hPQdisj hi (heq ▸ hj)
    let w1 (t : ℝ) : ℝ^3 := (1 - t) • y1 + t • x i1
    let w2 (t : ℝ) : ℝ^3 := (1 - t) • y2 + t • x i2
    let w3 (t : ℝ) : ℝ^3 := (1 - t) • y3 + t • x j1
    let w4 (t : ℝ) : ℝ^3 := (1 - t) • y4 + t • x j2
    let w5 (t : ℝ) : ℝ^3 := (1 - t) • y5 + t • x j3
    have hw_mem (i : Fin k) (y : ℝ^3) (hy : y ∈ X i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        (1 - t) • y + t • x i ∈ convexHull ℝ (X i : Set (ℝ^3)) :=
      (convex_convexHull ℝ (X i : Set (ℝ^3))) (subset_convexHull ℝ _ hy) (subset_convexHull ℝ _ (hx i))
        (by linarith) ht0 (by linarith)
    let K : Set (ℝ × ℝ × ℝ × ℝ) :=
      {q | q.1 ∈ Set.Icc 0 1 ∧ q.2.1 ∈ Set.Icc 0 1 ∧ 0 ≤ q.2.2.1 ∧ 0 ≤ q.2.2.2 ∧
           q.2.2.1 + q.2.2.2 ≤ 1 ∧
           (1 - q.2.1) • w1 q.1 + q.2.1 • w2 q.1 =
             q.2.2.1 • w3 q.1 + q.2.2.2 • w4 q.1 + (1 - q.2.2.1 - q.2.2.2) • w5 q.1}
    -- Every point in K has strictly interior (α, β1, β2) and t < 1!
    have hinterior : ∀ q ∈ K, q.1 < 1 ∧ 0 < q.2.1 ∧ q.2.1 < 1 ∧
        0 < q.2.2.1 ∧ 0 < q.2.2.2 ∧ q.2.2.1 + q.2.2.2 < 1 := by
      rintro ⟨t, α, b1, b2⟩ ⟨⟨ht0, ht1⟩, ⟨hα0, hα1⟩, hb1, hb2, hb12, heq⟩
      have hw1m := hw_mem i1 y1 hy1 ht0 ht1
      have hw2m := hw_mem i2 y2 hy2 ht0 ht1
      have hw3m := hw_mem j1 y3 hy3 ht0 ht1
      have hw4m := hw_mem j2 y4 hy4 ht0 ht1
      have hw5m := hw_mem j3 y5 hy5 ht0 ht1
      set pt := (1 - α) • w1 t + α • w2 t
      have hpt_pair (a b : Fin k) (u v : ℝ^3)
          (hu : u ∈ convexHull ℝ (X a : Set (ℝ^3))) (hv : v ∈ convexHull ℝ (X b : Set (ℝ^3)))
          (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc : c1 + c2 = 1) :
          c1 • u + c2 • v ∈ convexHull ℝ ((X a ∪ X b : Finset (ℝ^3)) : Set (ℝ^3)) := by
        have hu' : u ∈ convexHull ℝ ((X a ∪ X b : Finset (ℝ^3)) : Set (ℝ^3)) :=
          convexHull_mono (Finset.coe_subset.mpr (Finset.subset_union_left (s₁ := X a) (s₂ := X b))) hu
        have hv' : v ∈ convexHull ℝ ((X a ∪ X b : Finset (ℝ^3)) : Set (ℝ^3)) :=
          convexHull_mono (Finset.coe_subset.mpr (Finset.subset_union_right (s₁ := X a) (s₂ := X b))) hv
        exact convex_convexHull ℝ _ hu' hv' hc1 hc2 hc
      have hpt_U : pt ∈ convexHull ℝ ((X i1 ∪ X i2 : Finset (ℝ^3)) : Set (ℝ^3)) :=
        hpt_pair i1 i2 (w1 t) (w2 t) hw1m hw2m (1 - α) α (by linarith) hα0 (by linarith)
      have hpt_Q : pt ∈ convexHull ℝ ((Q.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) := by
        have hsub3 (j : Fin k) (hj : j ∈ Q) : convexHull ℝ (X j : Set (ℝ^3)) ⊆
            convexHull ℝ ((Q.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) :=
          convexHull_mono (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem X hj))
        have h3 := hsub3 j1 hj1 hw3m
        have h4 := hsub3 j2 hj2 hw4m
        have h5 := hsub3 j3 hj3 hw5m
        rw [heq]
        by_cases h12z : b1 + b2 = 0
        · have hb10 : b1 = 0 := by linarith
          have hb20 : b2 = 0 := by linarith
          simpa [hb10, hb20] using h5
        · have h12p : 0 < b1 + b2 := lt_of_le_of_ne (by linarith) (Ne.symm h12z)
          let u34 := (b1 / (b1 + b2)) • w3 t + (b2 / (b1 + b2)) • w4 t
          have hu34 : u34 ∈ convexHull ℝ ((Q.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) :=
            convex_convexHull ℝ _ h3 h4 (div_nonneg hb1 h12p.le) (div_nonneg hb2 h12p.le)
              (by field_simp [h12p.ne'])
          have hrew : b1 • w3 t + b2 • w4 t + (1 - b1 - b2) • w5 t =
              (b1 + b2) • u34 + (1 - b1 - b2) • w5 t := by
            symm; dsimp [u34]
            rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h12p.ne', mul_div_cancel₀ _ h12p.ne']
          rw [hrew]
          exact convex_convexHull ℝ _ hu34 h5 h12p.le (by linarith) (by linarith)
      have ht_lt1 : t < 1 := by
        rcases lt_or_eq_of_le ht1 with h | rfl
        · exact h
        · exfalso
          have h1 : pt ∈ convexHull ℝ ((P.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
            have hx1 : w1 1 ∈ convexHull ℝ ((P.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
              have : w1 1 = x i1 := by simp [w1]
              rw [this]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem x hi1))
            have hx2 : w2 1 ∈ convexHull ℝ ((P.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
              have : w2 1 = x i2 := by simp [w2]
              rw [this]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem x hi2))
            exact convex_convexHull ℝ _ hx1 hx2 (by linarith) hα0 (by linarith)
          have h2 : pt ∈ convexHull ℝ ((Q.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
            have hx3 : w3 1 ∈ convexHull ℝ ((Q.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
              have : w3 1 = x j1 := by simp [w3]
              rw [this]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem x hj1))
            have hx4 : w4 1 ∈ convexHull ℝ ((Q.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
              have : w4 1 = x j2 := by simp [w4]
              rw [this]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem x hj2))
            have hx5 : w5 1 ∈ convexHull ℝ ((Q.image x : Finset (ℝ^3)) : Set (ℝ^3)) := by
              have : w5 1 = x j3 := by simp [w5]
              rw [this]; exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem x hj3))
            rw [heq]
            by_cases h12z : b1 + b2 = 0
            · have hb10 : b1 = 0 := by linarith
              have hb20 : b2 = 0 := by linarith
              simpa [hb10, hb20] using hx5
            · have h12p : 0 < b1 + b2 := lt_of_le_of_ne (by linarith) (Ne.symm h12z)
              let u34 := (b1 / (b1 + b2)) • w3 1 + (b2 / (b1 + b2)) • w4 1
              have hu34 := convex_convexHull ℝ _ hx3 hx4 (div_nonneg hb1 h12p.le) (div_nonneg hb2 h12p.le)
                (by field_simp [h12p.ne'])
              have hrew : b1 • w3 1 + b2 • w4 1 + (1 - b1 - b2) • w5 1 =
                  (b1 + b2) • u34 + (1 - b1 - b2) • w5 1 := by
                symm; dsimp [u34]
                rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h12p.ne', mul_div_cancel₀ _ h12p.ne']
              rw [hrew]; exact convex_convexHull ℝ _ hu34 hx5 h12p.le (by linarith) (by linarith)
          exact Set.disjoint_left.mp hPQrep h1 h2
      have hQ_sub (i : Fin k) (hi : i ∈ P) :
          convexHull ℝ ((Q.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) ⊆
          convexHull ℝ (((Finset.univ.erase i).biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) := by
        apply convexHull_mono; apply Finset.coe_subset.mpr; apply Finset.biUnion_subset_biUnion_of_subset_left
        intro j hj; exact Finset.mem_erase.mpr ⟨(hne_ij i hi j hj).symm, Finset.mem_univ j⟩
      have hα_pos : 0 < α := by
        rcases eq_or_lt_of_le hα0 with rfl | h
        · exfalso
          have : pt = w1 t := by simp [pt]
          exact Set.disjoint_left.mp (hcvx i1) (this ▸ hw1m) (hQ_sub i1 hi1 hpt_Q)
        · exact h
      have hα_lt1 : α < 1 := by
        rcases lt_or_eq_of_le hα1 with h | rfl
        · exact h
        · exfalso
          have : pt = w2 t := by simp [pt]
          exact Set.disjoint_left.mp (hcvx i2) (this ▸ hw2m) (hQ_sub i2 hi2 hpt_Q)
      have hb1_pos : 0 < b1 := by
        rcases eq_or_lt_of_le hb1 with rfl | h
        · exfalso
          have hpt2 : pt ∈ convexHull ℝ ((X j2 ∪ X j3 : Finset (ℝ^3)) : Set (ℝ^3)) := by
            rw [heq]; simp only [zero_smul, zero_add, sub_zero]
            exact hpt_pair j2 j3 (w4 t) (w5 t) hw4m hw5m b2 (1 - b2) hb2 (by linarith) (by linarith)
          exact Set.disjoint_left.mp
            (h2sep i1 i2 j2 j3 (hne_ij i1 hi1 j2 hj2) (hne_ij i1 hi1 j3 hj3)
              (hne_ij i2 hi2 j2 hj2) (hne_ij i2 hi2 j3 hj3)) hpt_U hpt2
        · exact h
      have hb2_pos : 0 < b2 := by
        rcases eq_or_lt_of_le hb2 with rfl | h
        · exfalso
          have hpt2 : pt ∈ convexHull ℝ ((X j1 ∪ X j3 : Finset (ℝ^3)) : Set (ℝ^3)) := by
            rw [heq]; simp only [zero_smul, add_zero, sub_zero]
            exact hpt_pair j1 j3 (w3 t) (w5 t) hw3m hw5m b1 (1 - b1) hb1 (by linarith) (by linarith)
          exact Set.disjoint_left.mp
            (h2sep i1 i2 j1 j3 (hne_ij i1 hi1 j1 hj1) (hne_ij i1 hi1 j3 hj3)
              (hne_ij i2 hi2 j1 hj1) (hne_ij i2 hi2 j3 hj3)) hpt_U hpt2
        · exact h
      have hb12_lt1 : b1 + b2 < 1 := by
        rcases lt_or_eq_of_le hb12 with h | h1
        · exact h
        · exfalso
          have hpt2 : pt ∈ convexHull ℝ ((X j1 ∪ X j2 : Finset (ℝ^3)) : Set (ℝ^3)) := by
            rw [heq, show 1 - b1 - b2 = 0 by linarith, zero_smul, add_zero]
            exact hpt_pair j1 j2 (w3 t) (w4 t) hw3m hw4m b1 b2 hb1 hb2 h1
          exact Set.disjoint_left.mp
            (h2sep i1 i2 j1 j2 (hne_ij i1 hi1 j1 hj1) (hne_ij i1 hi1 j2 hj2)
              (hne_ij i2 hi2 j1 hj1) (hne_ij i2 hi2 j2 hj2)) hpt_U hpt2
      exact ⟨ht_lt1, hα_pos, hα_lt1, hb1_pos, hb2_pos, hb12_lt1⟩
    -- K is nonempty (t = 0 from hinter)
    have hKne : K.Nonempty := by
      obtain ⟨p0, hp12, hp345⟩ := hinter
      rw [convexHull_pair] at hp12
      obtain ⟨a1, a2, ha1, ha2, ha12, hp12_eq⟩ := hp12
      obtain ⟨b1, b2, b3, hb1, hb2, hb3, hb123, hbp⟩ := mem_convexHull_triple hp345
      refine ⟨(0, a2, b1, b2), ⟨le_rfl, zero_le_one⟩, ⟨ha2, by linarith⟩, hb1, hb2, by linarith, ?_⟩
      simp only [w1, w2, w3, w4, w5, sub_zero, one_smul, zero_smul, add_zero]
      rw [show 1 - a2 = a1 by linarith, show 1 - b1 - b2 = b3 by linarith, hp12_eq, hbp]
    -- K is compact (closed subset of [0,1]^4)
    have hKcomp : IsCompact K := by
      let B : Set (ℝ × ℝ × ℝ × ℝ) := Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
      have hBcomp : IsCompact B :=
        isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
      have hKsub : K ⊆ B := by
        rintro ⟨t, α, b1, b2⟩ ⟨ht, hα, hb1, hb2, hb12, _⟩
        exact ⟨ht, hα, ⟨hb1, by linarith⟩, ⟨hb2, by linarith⟩⟩
      have hcw : ∀ u v : ℝ^3, Continuous (fun q : ℝ × ℝ × ℝ × ℝ => (1 - q.1) • u + q.1 • v) := fun u v =>
        ((continuous_const.sub continuous_fst).smul continuous_const).add (continuous_fst.smul continuous_const)
      have hcl_eq : IsClosed {q : ℝ × ℝ × ℝ × ℝ |
          (1 - q.2.1) • w1 q.1 + q.2.1 • w2 q.1 =
            q.2.2.1 • w3 q.1 + q.2.2.2 • w4 q.1 + (1 - q.2.2.1 - q.2.2.2) • w5 q.1} := by
        apply isClosed_eq
        · exact ((continuous_const.sub (continuous_fst.comp continuous_snd)).smul (hcw y1 (x i1))).add
            ((continuous_fst.comp continuous_snd).smul (hcw y2 (x i2)))
        · exact (((continuous_fst.comp (continuous_snd.comp continuous_snd)).smul (hcw y3 (x j1))).add
            ((continuous_snd.comp (continuous_snd.comp continuous_snd)).smul (hcw y4 (x j2)))).add
            (((continuous_const.sub (continuous_fst.comp (continuous_snd.comp continuous_snd))).sub
              (continuous_snd.comp (continuous_snd.comp continuous_snd))).smul (hcw y5 (x j3)))
      have hKclosed : IsClosed K := by
        have h1 : IsClosed {q : ℝ × ℝ × ℝ × ℝ | q.1 ∈ Set.Icc 0 1} := isClosed_Icc.preimage continuous_fst
        have h2 : IsClosed {q : ℝ × ℝ × ℝ × ℝ | q.2.1 ∈ Set.Icc 0 1} := isClosed_Icc.preimage (continuous_fst.comp continuous_snd)
        have h3 : IsClosed {q : ℝ × ℝ × ℝ × ℝ | 0 ≤ q.2.2.1} := isClosed_le continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd))
        have h4 : IsClosed {q : ℝ × ℝ × ℝ × ℝ | 0 ≤ q.2.2.2} := isClosed_le continuous_const (continuous_snd.comp (continuous_snd.comp continuous_snd))
        have h5 : IsClosed {q : ℝ × ℝ × ℝ × ℝ | q.2.2.1 + q.2.2.2 ≤ 1} :=
          isClosed_le ((continuous_fst.comp (continuous_snd.comp continuous_snd)).add (continuous_snd.comp (continuous_snd.comp continuous_snd))) continuous_const
        exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter hcl_eq))))
      exact hBcomp.of_isClosed_subset hKclosed hKsub
    -- Maximize t on K!
    obtain ⟨qmax, hqmaxK, hqmax⟩ := hKcomp.exists_isMaxOn hKne continuous_fst.continuousOn
    rcases qmax with ⟨t0, α0, b10, b20⟩
    obtain ⟨ht0_lt1, hα0_pos, hα0_lt1, hb10_pos, hb20_pos, hb120_lt1⟩ := hinterior _ hqmaxK
    -- Rewrite intersection equation as 3×3 matrix system M(t) *ᵥ v = rhs(t)
    let M (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
      Matrix.of fun r c => match c with
        | 0 => (w2 t - w1 t) r
        | 1 => (w5 t - w3 t) r
        | 2 => (w5 t - w4 t) r
    let rhs (t : ℝ) : Fin 3 → ℝ := fun r => (w5 t - w1 t) r
    have hsys_iff (t α b1 b2 : ℝ) :
        ((1 - α) • w1 t + α • w2 t = b1 • w3 t + b2 • w4 t + (1 - b1 - b2) • w5 t) ↔
        M t *ᵥ ![α, b1, b2] = rhs t := by
      constructor
      · intro h; ext r
        have hr := congrArg (fun u : ℝ^3 => u r) h
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hr
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, M, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, rhs, PiLp.sub_apply]
        linarith
      · intro h; apply PiLp.ext; intro r
        have hr := congrFun h r
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, M, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, rhs, PiLp.sub_apply] at hr
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        linarith
    have hv0_eq : M t0 *ᵥ ![α0, b10, b20] = rhs t0 := (hsys_iff t0 α0 b10 b20).mp hqmaxK.2.2.2.2.2
    by_cases hdet : (M t0).det = 0
    · -- Case B: det M(t0) = 0 ⇒ move along ker M(t0) until hitting a face!
      obtain ⟨d, hdne, hMd0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      let c5 : Fin 5 → ℝ := ![α0, 1 - α0, b10, b20, 1 - b10 - b20]
      let a5 : Fin 5 → ℝ := ![d 0, -d 0, d 1, d 2, -(d 1 + d 2)]
      have hc5_pos : ∀ r : Fin 5, 0 < c5 r := by
        intro r; fin_cases r <;> dsimp [c5] <;> linarith
      have hex_neg : ∃ r : Fin 5, a5 r < 0 := by
        by_contra hall
        push Not at hall
        have h0 := hall 0; have h1 := hall 1; have h2 := hall 2; have h3 := hall 3; have h4 := hall 4
        dsimp [a5] at h0 h1 h2 h3 h4
        apply hdne; ext i; fin_cases i <;> simp <;> linarith
      let negs : Finset (Fin 5) := Finset.univ.filter fun r => a5 r < 0
      have hnegs_ne : negs.Nonempty := by
        obtain ⟨r, hr⟩ := hex_neg; exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩⟩
      let ratios := negs.image fun r => c5 r / (-a5 r)
      have hrat_ne : ratios.Nonempty := hnegs_ne.image _
      let s0 := ratios.min' hrat_ne
      obtain ⟨r0, hr0_mem, hr0_eq⟩ := Finset.mem_image.mp (Finset.min'_mem ratios hrat_ne)
      have ha_r0 : a5 r0 < 0 := (Finset.mem_filter.mp hr0_mem).2
      have hs0_pos : 0 < s0 := by
        change 0 < ratios.min' hrat_ne; rw [← hr0_eq]
        exact div_pos (hc5_pos r0) (by linarith)
      have hnn5 : ∀ r : Fin 5, 0 ≤ c5 r + s0 * a5 r := by
        intro r
        by_cases hneg : a5 r < 0
        · have hle : s0 ≤ c5 r / (-a5 r) :=
            Finset.min'_le _ _ (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hneg⟩, rfl⟩)
          have hpos : 0 < -a5 r := by linarith
          have := (le_div_iff₀ hpos).mp hle
          linarith
        · have : 0 ≤ a5 r := not_lt.mp hneg
          nlinarith only [hc5_pos r, hs0_pos, this]
      have hzero_r0 : c5 r0 + s0 * a5 r0 = 0 := by
        have hs0_eq : s0 = c5 r0 / (-a5 r0) := hr0_eq.symm
        have hne : a5 r0 ≠ 0 := by linarith
        rw [hs0_eq, div_neg, neg_mul, div_mul_cancel₀ _ hne, add_neg_cancel]
      let α' := α0 + s0 * d 0
      let b1' := b10 + s0 * d 1
      let b2' := b20 + s0 * d 2
      have hM' : M t0 *ᵥ ![α', b1', b2'] = rhs t0 := by
        have hv_eq : ![α', b1', b2'] = ![α0, b10, b20] + s0 • d := by
          ext i; fin_cases i <;> simp [α', b1', b2']
        rw [hv_eq, Matrix.mulVec_add, Matrix.mulVec_smul, hv0_eq, hMd0, smul_zero, add_zero]
      have hq'K : (t0, α', b1', b2') ∈ K := by
        have h0 := hnn5 0; have h1 := hnn5 1; have h2 := hnn5 2; have h3 := hnn5 3; have h4 := hnn5 4
        dsimp [c5, a5] at h0 h1 h2 h3 h4
        refine ⟨hqmaxK.1, ⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith,
          (hsys_iff t0 α' b1' b2').mpr hM'⟩
      obtain ⟨_, ha'p, ha'1, hb1'p, hb2'p, hb12'1⟩ := hinterior _ hq'K
      fin_cases r0 <;> dsimp [c5, a5] at hzero_r0 <;> dsimp [α', b1', b2'] at ha'p ha'1 hb1'p hb2'p hb12'1 <;> linarith
    · -- Case A: det M(t0) ≠ 0 ⇒ Cramer's rule extends continuously to t0 + ε > t0!
      have hMcont : Continuous M := by
        refine continuous_matrix fun r c => ?_
        have hcw (u v : ℝ^3) : Continuous (fun t : ℝ => ((1 - t) • u + t • v) r) := by
          have : (fun t : ℝ => ((1 - t) • u + t • v) r) = fun t => (1 - t) * u r + t * v r := by
            ext t; simp
          rw [this]
          exact ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)
        fin_cases c <;>
          exact (hcw _ _).sub (hcw _ _)
      have hrhscont : Continuous rhs := by
        rw [continuous_pi_iff]; intro r
        have hcw (u v : ℝ^3) : Continuous (fun t : ℝ => ((1 - t) • u + t • v) r) := by
          have : (fun t : ℝ => ((1 - t) • u + t • v) r) = fun t => (1 - t) * u r + t * v r := by
            ext t; simp
          rw [this]
          exact ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)
        exact (hcw y5 (x j3)).sub (hcw y1 (x i1))
      let vfun (t : ℝ) : Fin 3 → ℝ := (M t).det⁻¹ • ((M t).adjugate *ᵥ rhs t)
      have hv_sol : ∀ t, (M t).det ≠ 0 → M t *ᵥ vfun t = rhs t := fun t hdt => by
        dsimp [vfun]
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
          Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hdt, one_smul]
      have hv_t0 : vfun t0 = ![α0, b10, b20] := by
        have h1 : (M t0).adjugate *ᵥ (M t0 *ᵥ ![α0, b10, b20]) = (M t0).det • ![α0, b10, b20] := by
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        dsimp [vfun]
        rw [← hv0_eq, h1, smul_smul, inv_mul_cancel₀ hdet, one_smul]
      have hdet_cont : Continuous (fun t => (M t).det) := hMcont.matrix_det
      have hv_contAt : ContinuousAt vfun t0 := by
        have hinv : ContinuousAt (fun t => (M t).det⁻¹) t0 := hdet_cont.continuousAt.inv₀ hdet
        have hadj : Continuous (fun t => (M t).adjugate *ᵥ rhs t) := by
          rw [continuous_pi_iff]; intro r
          simp only [Matrix.mulVec, dotProduct]
          exact continuous_finsetSum _ fun c _ =>
            (((continuous_apply c).comp ((continuous_apply r).comp hMcont.matrix_adjugate)).mul
              ((continuous_apply c).comp hrhscont))
        exact hinv.smul hadj.continuousAt
      have hev_det : ∀ᶠ t in nhds t0, (M t).det ≠ 0 :=
        hdet_cont.continuousAt.eventually_ne hdet
      have hev0 : ∀ᶠ t in nhds t0, 0 < vfun t 0 := by
        have : ContinuousAt (fun t => vfun t 0) t0 := (continuous_apply 0).continuousAt.comp hv_contAt
        exact this.eventually (Ioi_mem_nhds (by dsimp only; rw [hv_t0]; exact hα0_pos))
      have hev1 : ∀ᶠ t in nhds t0, vfun t 0 < 1 := by
        have : ContinuousAt (fun t => vfun t 0) t0 := (continuous_apply 0).continuousAt.comp hv_contAt
        exact this.eventually (Iio_mem_nhds (by dsimp only; rw [hv_t0]; exact hα0_lt1))
      have hev2 : ∀ᶠ t in nhds t0, 0 < vfun t 1 := by
        have : ContinuousAt (fun t => vfun t 1) t0 := (continuous_apply 1).continuousAt.comp hv_contAt
        exact this.eventually (Ioi_mem_nhds (by dsimp only; rw [hv_t0]; exact hb10_pos))
      have hev3 : ∀ᶠ t in nhds t0, 0 < vfun t 2 := by
        have : ContinuousAt (fun t => vfun t 2) t0 := (continuous_apply 2).continuousAt.comp hv_contAt
        exact this.eventually (Ioi_mem_nhds (by dsimp only; rw [hv_t0]; exact hb20_pos))
      have hev4 : ∀ᶠ t in nhds t0, vfun t 1 + vfun t 2 < 1 := by
        have : ContinuousAt (fun t => vfun t 1 + vfun t 2) t0 :=
          ((continuous_apply 1).continuousAt.comp hv_contAt).add ((continuous_apply 2).continuousAt.comp hv_contAt)
        exact this.eventually (Iio_mem_nhds (by dsimp only; rw [hv_t0]; exact hb120_lt1))
      have hall := hev_det.and (hev0.and (hev1.and (hev2.and (hev3.and hev4))))
      rw [Metric.eventually_nhds_iff] at hall
      obtain ⟨δ, hδpos, hδ⟩ := hall
      let t1 := t0 + min (δ / 2) ((1 - t0) / 2)
      have ht1_gt : t0 < t1 := by dsimp [t1]; linarith [lt_min (half_pos hδpos) (half_pos (sub_pos.mpr ht0_lt1))]
      have ht1_le1 : t1 ≤ 1 := by dsimp [t1]; linarith [min_le_right (δ / 2) ((1 - t0) / 2)]
      have ht1_dist : dist t1 t0 < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht1_gt)]
        dsimp [t1]; linarith [min_le_left (δ / 2) ((1 - t0) / 2)]
      obtain ⟨hdt1, h0, h1, h2, h3, h4⟩ := hδ ht1_dist
      have hv1_sol : M t1 *ᵥ ![vfun t1 0, vfun t1 1, vfun t1 2] = rhs t1 := by
        have : ![vfun t1 0, vfun t1 1, vfun t1 2] = vfun t1 := by ext i; fin_cases i <;> rfl
        rw [this]; exact hv_sol t1 hdt1
      have hq1K : (t1, vfun t1 0, vfun t1 1, vfun t1 2) ∈ K :=
        ⟨⟨hqmaxK.1.1.trans ht1_gt.le, ht1_le1⟩, ⟨h0.le, h1.le⟩, h2.le, h3.le, h4.le,
          (hsys_iff t1 (vfun t1 0) (vfun t1 1) (vfun t1 2)).mpr hv1_sol⟩
      have hle_max : t1 ≤ t0 := hqmax hq1K
      linarith
  -- Apply Kirchberger to Spos.biUnion X and Sneg.biUnion X!
  rw [Set.disjoint_left]
  intro p0 hp01 hp02
  have hne : (convexHull ℝ ((Spos.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)) ∩
      convexHull ℝ ((Sneg.biUnion X : Finset (ℝ^3)) : Set (ℝ^3))).Nonempty := ⟨p0, hp01, hp02⟩
  obtain ⟨A', hA'sub, B', hB'sub, hcard5, p, hpA', hpB'⟩ := kirchberger (Spos.biUnion X) (Sneg.biUnion X) hne
  rw [finrank_euclideanSpace_fin] at hcard5
  have hA'ne : A'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpA'; exact hpA'
  have hB'ne : B'.Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.coe_empty, convexHull_empty] at hpB'; exact hpB'
  have hdisj_pn : Disjoint Spos Sneg := Finset.disjoint_sdiff
  have hno1 (P Q : Finset (Fin k)) (hPQ : Disjoint P Q) (A B : Finset (ℝ^3))
      (hAP : A ⊆ P.biUnion X) (hBQ : B ⊆ Q.biUnion X) (hA1 : A.card = 1)
      (hpA : p ∈ convexHull ℝ (A : Set (ℝ^3))) (hpB : p ∈ convexHull ℝ (B : Set (ℝ^3))) : False := by
    obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hA1
    obtain ⟨i, hiP, hyXi⟩ := Finset.mem_biUnion.mp (hAP (Finset.mem_singleton_self y))
    have hpy : p = y := by simpa [convexHull_singleton] using hpA
    have hpXi : p ∈ convexHull ℝ (X i : Set (ℝ^3)) := subset_convexHull ℝ _ (hpy ▸ hyXi)
    have hBsub : B ⊆ (Finset.univ.erase i).biUnion X := by
      intro z hz; obtain ⟨j, hjQ, hzXj⟩ := Finset.mem_biUnion.mp (hBQ hz)
      have hji : j ≠ i := fun h => Finset.disjoint_left.mp hPQ hiP (h ▸ hjQ)
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hzXj⟩
    exact Set.disjoint_left.mp (hcvx i) hpXi (convexHull_mono (Finset.coe_subset.mpr hBsub) hpB)
  have hA'ge2 : 2 ≤ A'.card := by
    by_contra! hlt
    exact hno1 Spos Sneg hdisj_pn A' B' hA'sub hB'sub (by have := Finset.card_pos.mpr hA'ne; omega) hpA' hpB'
  have hB'ge2 : 2 ≤ B'.card := by
    by_contra! hlt
    exact hno1 Sneg Spos hdisj_pn.symm B' A' hB'sub hA'sub (by have := Finset.card_pos.mpr hB'ne; omega) hpB' hpA'
  have hno22 (hA2 : A'.card = 2) (hB2 : B'.card = 2) : False := by
    obtain ⟨y1, y2, _, rfl⟩ := Finset.card_eq_two.mp hA2
    obtain ⟨y3, y4, _, rfl⟩ := Finset.card_eq_two.mp hB2
    obtain ⟨i1, hi1, hy1⟩ := Finset.mem_biUnion.mp (hA'sub (show y1 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨i2, hi2, hy2⟩ := Finset.mem_biUnion.mp (hA'sub (show y2 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨j1, hj1, hy3⟩ := Finset.mem_biUnion.mp (hB'sub (show y3 ∈ ({y3, y4} : Finset (ℝ^3)) by simp))
    obtain ⟨j2, hj2, hy4⟩ := Finset.mem_biUnion.mp (hB'sub (show y4 ∈ ({y3, y4} : Finset (ℝ^3)) by simp))
    have hne : ∀ i ∈ Spos, ∀ j ∈ Sneg, i ≠ j := fun i hi j hj h =>
      Finset.disjoint_left.mp hdisj_pn hi (h ▸ hj)
    have hp1 : p ∈ convexHull ℝ ((X i1 ∪ X i2 : Finset (ℝ^3)) : Set (ℝ^3)) :=
      convexHull_mono (by intro z hz; simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]; rcases hz with rfl | rfl <;> [exact Or.inl hy1; exact Or.inr hy2]) hpA'
    have hp2 : p ∈ convexHull ℝ ((X j1 ∪ X j2 : Finset (ℝ^3)) : Set (ℝ^3)) :=
      convexHull_mono (by intro z hz; simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]; rcases hz with rfl | rfl <;> [exact Or.inl hy3; exact Or.inr hy4]) hpB'
    exact Set.disjoint_left.mp (h2sep i1 i2 j1 j2 (hne _ hi1 _ hj1) (hne _ hi1 _ hj2) (hne _ hi2 _ hj1) (hne _ hi2 _ hj2)) hp1 hp2
  have hcases : (A'.card = 2 ∧ B'.card = 3) ∨ (A'.card = 3 ∧ B'.card = 2) := by
    by_cases h22 : A'.card = 2 ∧ B'.card = 2
    · exact absurd (hno22 h22.1 h22.2) id
    · omega
  rcases hcases with ⟨hA2, hB3⟩ | ⟨hA3, hB2⟩
  · obtain ⟨y1, y2, _, rfl⟩ := Finset.card_eq_two.mp hA2
    obtain ⟨y3, y4, y5, _, _, _, rfl⟩ := Finset.card_eq_three.mp hB3
    obtain ⟨i1, hi1, hy1⟩ := Finset.mem_biUnion.mp (hA'sub (show y1 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨i2, hi2, hy2⟩ := Finset.mem_biUnion.mp (hA'sub (show y2 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨j1, hj1, hy3⟩ := Finset.mem_biUnion.mp (hB'sub (show y3 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    obtain ⟨j2, hj2, hy4⟩ := Finset.mem_biUnion.mp (hB'sub (show y4 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    obtain ⟨j3, hj3, hy5⟩ := Finset.mem_biUnion.mp (hB'sub (show y5 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    exact h23_contra Spos Sneg hdisj_pn hrep_sep i1 i2 hi1 hi2 j1 j2 j3 hj1 hj2 hj3 y1 y2 y3 y4 y5
      hy1 hy2 hy3 hy4 hy5 ⟨p, by simpa using hpA', by simpa using hpB'⟩
  · obtain ⟨y1, y2, _, rfl⟩ := Finset.card_eq_two.mp hB2
    obtain ⟨y3, y4, y5, _, _, _, rfl⟩ := Finset.card_eq_three.mp hA3
    obtain ⟨i1, hi1, hy1⟩ := Finset.mem_biUnion.mp (hB'sub (show y1 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨i2, hi2, hy2⟩ := Finset.mem_biUnion.mp (hB'sub (show y2 ∈ ({y1, y2} : Finset (ℝ^3)) by simp))
    obtain ⟨j1, hj1, hy3⟩ := Finset.mem_biUnion.mp (hA'sub (show y3 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    obtain ⟨j2, hj2, hy4⟩ := Finset.mem_biUnion.mp (hA'sub (show y4 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    obtain ⟨j3, hj3, hy5⟩ := Finset.mem_biUnion.mp (hA'sub (show y5 ∈ ({y3, y4, y5} : Finset (ℝ^3)) by simp))
    exact h23_contra Sneg Spos hdisj_pn.symm hrep_sep.symm i1 i2 hi1 hi2 j1 j2 j3 hj1 hj2 hj3 y1 y2 y3 y4 y5
      hy1 hy2 hy3 hy4 hy5 ⟨p, by simpa using hpB', by simpa using hpA'⟩

/- ### Part 12: Affine Perturbation and Wedge Separation (Prop 5_lem) -/

def evalAff (g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (u : ℝ^3) : ℝ := g.1 u + g.2

lemma evalAff_convex_comb (g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (a b : ℝ) (hab : a + b = 1) (u v : ℝ^3) :
    evalAff g (a • u + b • v) = a * evalAff g u + b * evalAff g v := by
  dsimp [evalAff]; rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc a * g.1 u + b * g.1 v + g.2
    _ = a * g.1 u + b * g.1 v + (a + b) * g.2 := by rw [hab, one_mul]
    _ = a * (g.1 u + g.2) + b * (g.1 v + g.2) := by ring

lemma perturb_functional (f : (ℝ^3) →ₗ[ℝ] ℝ) (c : ℝ) (A B V : Finset (ℝ^3))
    (hA : ∀ u ∈ A, f u + c < 0) (hB : ∀ u ∈ B, 0 < f u + c)
    (hV : ∀ v ∈ V, v ≠ 0) :
    ∃ f' : (ℝ^3) →ₗ[ℝ] ℝ,
      (∀ u ∈ A, f' u + c < 0) ∧ (∀ u ∈ B, 0 < f' u + c) ∧ (∀ v ∈ V, f' v ≠ 0) := by
  let W (v : V) : Submodule ℝ ((ℝ^3) →ₗ[ℝ] ℝ) :=
    LinearMap.ker (LinearMap.applyₗ (R := ℝ) (M := ℝ^3) (M₂ := ℝ) v.1)
  have hWne (v : V) : W v ≠ ⊤ := by
    intro htop
    have hmem : (innerSL ℝ v.1).toLinearMap ∈ W v := htop ▸ Submodule.mem_top
    have h0 : inner ℝ v.1 v.1 = 0 := LinearMap.mem_ker.mp hmem
    rw [real_inner_self_eq_norm_sq] at h0
    exact hV v.1 v.2 (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hWne
  have hℓv : ∀ v ∈ V, ℓ v ≠ 0 := fun v hv h0 =>
    hℓ ⟨v, hv⟩ (LinearMap.mem_ker.mpr h0)
  -- Find δ > 0 preserving all strict inequalities on A and B
  let margA := A.image fun u => -(f u + c) / (|ℓ u| + 1)
  let margB := B.image fun u => (f u + c) / (|ℓ u| + 1)
  let margs := insert (1 : ℝ) (margA ∪ margB)
  have hmargs_ne : margs.Nonempty := Finset.insert_nonempty _ _
  let δ := margs.min' hmargs_ne
  have hδpos : 0 < δ := by
    change 0 < margs.min' hmargs_ne
    have hmem := Finset.min'_mem margs hmargs_ne
    rcases Finset.mem_insert.mp hmem with h1 | hu
    · linarith
    · rcases Finset.mem_union.mp hu with hA' | hB'
      · obtain ⟨u, huA, heq⟩ := Finset.mem_image.mp hA'
        rw [← heq]; exact div_pos (by linarith [hA u huA]) (by positivity)
      · obtain ⟨u, huB, heq⟩ := Finset.mem_image.mp hB'
        rw [← heq]; exact div_pos (hB u huB) (by positivity)
  let bad : Finset ℝ := V.image fun v => -(f v) / (ℓ v)
  have hinf : (Set.Ioo (0 : ℝ) δ).Infinite := Set.Ioo_infinite hδpos
  obtain ⟨ε, hεIoo, hεnotbad⟩ := (hinf.sdiff bad.finite_toSet).nonempty
  refine ⟨f + ε • ℓ, ?_, ?_, ?_⟩
  · intro u hu
    have hle : δ ≤ -(f u + c) / (|ℓ u| + 1) :=
      Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)))
    have hpos : 0 < |ℓ u| + 1 := by positivity
    have h1 : ε * (|ℓ u| + 1) < -(f u + c) := by
      have h2 := (le_div_iff₀ hpos).mp hle
      have h3 : ε < δ := hεIoo.2
      nlinarith only [h2, h3, hpos]
    have h4 : ε * ℓ u ≤ ε * |ℓ u| := mul_le_mul_of_nonneg_left (le_abs_self _) hεIoo.1.le
    change (f u + ε * ℓ u) + c < 0
    nlinarith only [h1, h4, hεIoo.1]
  · intro u hu
    have hle : δ ≤ (f u + c) / (|ℓ u| + 1) :=
      Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)))
    have hpos : 0 < |ℓ u| + 1 := by positivity
    have h1 : ε * (|ℓ u| + 1) < f u + c := by
      have h2 := (le_div_iff₀ hpos).mp hle
      have h3 : ε < δ := hεIoo.2
      nlinarith only [h2, h3, hpos]
    have h4 : -(ε * |ℓ u|) ≤ ε * ℓ u := by
      have := neg_abs_le (ℓ u); nlinarith only [this, hεIoo.1]
    change 0 < (f u + ε * ℓ u) + c
    nlinarith only [h1, h4, hεIoo.1]
  · intro v hv h0
    change f v + ε * ℓ v = 0 at h0
    apply hεnotbad
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, ?_⟩)
    have hne : ℓ v ≠ 0 := hℓv v hv
    field_simp [hne]; linarith

lemma affine_comb_ne_zero_of_gp {S : Finset (ℝ^3)} (hS : Erdos651.IsInGeneralPosition S)
    {u v w : ℝ^3} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    {c1 c2 c3 : ℝ} (hsum : c1 + c2 + c3 = 0) (hc1 : c1 ≠ 0) :
    c1 • u + c2 • v + c3 • w ≠ 0 := by
  intro h0
  let Z : Finset (ℝ^3) := {u, v, w}
  have hZS : Z ⊆ S := by
    intro x hx; simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hZc : Z.card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_le_two.trans (by omega)))
  have hZind : AffineIndependent ℝ (Subtype.val : ↥(Z : Set (ℝ^3)) → ℝ^3) := hS Z hZS hZc
  let p3 : Fin 3 → ↥(Z : Set (ℝ^3)) := ![⟨u, by simp [Z]⟩, ⟨v, by simp [Z]⟩, ⟨w, by simp [Z]⟩]
  have hp3_inj : Function.Injective p3 := by
    intro a b hab
    have hval := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;> simp_all [p3]
  have hind3 : AffineIndependent ℝ ![u, v, w] := by
    have h1 := hZind.comp_embedding ⟨p3, hp3_inj⟩
    change AffineIndependent ℝ (Subtype.val ∘ p3) at h1
    have hcomp : Subtype.val ∘ p3 = ![u, v, w] := by ext r; fin_cases r <;> rfl
    rwa [hcomp] at h1
  let cw : Fin 3 → ℝ := ![c1, c2, c3]
  have hwsum : ∑ i : Fin 3, cw i = 0 := by rw [Fin.sum_univ_three]; exact hsum
  have hwvsub : Finset.univ.weightedVSub ![u, v, w] cw = 0 := by
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hwsum, Fin.sum_univ_three]
    simpa [cw, add_assoc] using h0
  exact hc1 (hind3 Finset.univ cw hwsum hwvsub 0 (Finset.mem_univ 0))

lemma hahn_banach_finset_sep (A B : Finset (ℝ^3))
    (hdisj : Disjoint (convexHull ℝ (A : Set (ℝ^3))) (convexHull ℝ (B : Set (ℝ^3)))) :
    ∃ g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ,
      (∀ u ∈ A, evalAff g u < 0) ∧ (∀ u ∈ B, 0 < evalAff g u) := by
  have hcompA : IsCompact (convexHull ℝ (A : Set (ℝ^3))) :=
    Set.Finite.isCompact_convexHull (𝕜 := ℝ) A.finite_toSet
  have hcompB : IsCompact (convexHull ℝ (B : Set (ℝ^3))) :=
    Set.Finite.isCompact_convexHull (𝕜 := ℝ) B.finite_toSet
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hcompA
      (convex_convexHull ℝ _) hcompB.isClosed hdisj
  refine ⟨(f.toLinearMap, -(u + v) / 2), ?_, ?_⟩
  · intro x hx; have := hfu x (subset_convexHull ℝ _ hx); dsimp [evalAff]; linarith
  · intro x hx; have := hfv x (subset_convexHull ℝ _ hx); dsimp [evalAff]; linarith

lemma wedge_separation {k : ℕ} (X : Fin k → Finset (ℝ^3))
    (hgp : Erdos651.IsInGeneralPosition (Finset.univ.biUnion X))
    (x : Fin k → ℝ^3) (hx : ∀ i, x i ∈ X i)
    (hcvx : ∀ j : Fin k, Disjoint (convexHull ℝ (X j : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ.erase j).biUnion X : Finset (ℝ^3)) : Set (ℝ^3))))
    (h2sep : ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      Disjoint (convexHull ℝ ((X i ∪ X j : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((X i' ∪ X j' : Finset (ℝ^3)) : Set (ℝ^3))))
    (hcor_ab : ∀ (a b c : ℕ), a ≤ b → b ≤ c → c ≤ k →
      let I1 := (Finset.univ : Finset (Fin k)).filter fun i => i.1 < a ∨ (b ≤ i.1 ∧ i.1 < c)
      let I2 := (Finset.univ : Finset (Fin k)).filter fun i => (a ≤ i.1 ∧ i.1 < b) ∨ c ≤ i.1
      Disjoint (convexHull ℝ ((I1.image x : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((I2.image x : Finset (ℝ^3)) : Set (ℝ^3))))
    (j1 j2 j3 : Fin k) (hj12 : j1 < j2) (hj23 : j2 < j3) :
    let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < j1 ∨ (j2 < j ∧ j ≤ j3)
    let S2 := (Finset.univ : Finset (Fin k)).filter fun j => (j1 ≤ j ∧ j < j2) ∨ j3 < j
    ∃ (f0 f1 f2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (ε : ℝ),
      0 < ε ∧
      (∀ u ∈ (Finset.univ.erase j2).biUnion X, evalAff f0 u ≤ -ε) ∧
      (∀ u ∈ X j2, 0 < evalAff f0 u) ∧
      (∀ u ∈ S1.biUnion X, ε ≤ evalAff f1 u) ∧
      (∀ u ∈ (insert j2 S2).biUnion X, evalAff f1 u ≤ -ε) ∧
      (∀ u ∈ (insert j2 S1).biUnion X, ε ≤ evalAff f2 u) ∧
      (∀ u ∈ S2.biUnion X, evalAff f2 u ≤ -ε) ∧
      Set.InjOn (evalAff f0) (X j2 : Set (ℝ^3)) ∧
      Set.InjOn (evalAff f1) (X j2 : Set (ℝ^3)) ∧
      Set.InjOn (evalAff f2) (X j2 : Set (ℝ^3)) ∧
      NoThreeCollinear2 ((X j2).image fun u => (evalAff f0 u, evalAff f1 u)) ∧
      NoThreeCollinear2 ((X j2).image fun u => (evalAff f0 u, evalAff f2 u)) ∧
      NoThreeCollinear2 ((X j2).image fun u => (evalAff f1 u, evalAff f2 u)) := by
  intro S1 S2
  have hgp_j2 : Erdos651.IsInGeneralPosition (X j2) :=
    fun Z hZ hZc => hgp Z (hZ.trans (Finset.subset_biUnion_of_mem X (Finset.mem_univ j2))) hZc
  -- Plane 0: separates (univ.erase j2).biUnion X (< 0) from X j2 (> 0)
  obtain ⟨f0_raw, hf0A, hf0B⟩ := hahn_banach_finset_sep ((Finset.univ.erase j2).biUnion X) (X j2) (hcvx j2).symm
  -- Plane 1: separates (insert j2 S2).biUnion X (< 0) from S1.biUnion X (> 0)
  have hsep1 : Disjoint (convexHull ℝ (((insert j2 S2).biUnion X : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ ((S1.biUnion X : Finset (ℝ^3)) : Set (ℝ^3))) := by
    have hI1eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.1 < j1.1 ∨ (j2.1 + 1 ≤ i.1 ∧ i.1 < j3.1 + 1)) = S1 := by
      ext j; simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]; omega
    have hI2eq : (Finset.univ : Finset (Fin k)).filter (fun i => (j1.1 ≤ i.1 ∧ i.1 < j2.1 + 1) ∨ j3.1 + 1 ≤ i.1) = insert j2 S2 := by
      ext j; simp only [S2, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def, Fin.ext_iff]; omega
    have hcomp1 : Finset.univ \ S1 = insert j2 S2 := by
      ext j; simp only [S1, S2, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, Finset.mem_insert, true_and, Fin.lt_def, Fin.le_def, Fin.ext_iff]; omega
    have hrep := hcor_ab j1.1 (j2.1 + 1) (j3.1 + 1) (by omega) (by omega) (by omega)
    dsimp only at hrep
    rw [hI1eq, hI2eq, ← hcomp1] at hrep
    have htr := sep_transfer_3d X x hx hcvx h2sep S1 hrep
    rw [hcomp1] at htr
    exact htr.symm
  obtain ⟨f1_raw, hf1A, hf1B⟩ := hahn_banach_finset_sep ((insert j2 S2).biUnion X) (S1.biUnion X) hsep1
  -- Plane 2: separates S2.biUnion X (< 0) from (insert j2 S1).biUnion X (> 0)
  have hsep2 : Disjoint (convexHull ℝ ((S2.biUnion X : Finset (ℝ^3)) : Set (ℝ^3)))
      (convexHull ℝ (((insert j2 S1).biUnion X : Finset (ℝ^3)) : Set (ℝ^3))) := by
    have hI1eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.1 < j1.1 ∨ (j2.1 ≤ i.1 ∧ i.1 < j3.1 + 1)) = insert j2 S1 := by
      ext j; simp only [S1, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def, Fin.ext_iff]; omega
    have hI2eq : (Finset.univ : Finset (Fin k)).filter (fun i => (j1.1 ≤ i.1 ∧ i.1 < j2.1) ∨ j3.1 + 1 ≤ i.1) = S2 := by
      ext j; simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]; omega
    have hcomp2 : Finset.univ \ insert j2 S1 = S2 := by
      ext j; simp only [S1, S2, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, Finset.mem_insert, true_and, Fin.lt_def, Fin.le_def, Fin.ext_iff]; omega
    have hrep := hcor_ab j1.1 j2.1 (j3.1 + 1) (by omega) (by omega) (by omega)
    dsimp only at hrep
    rw [hI1eq, hI2eq, ← hcomp2] at hrep
    have htr := sep_transfer_3d X x hx hcvx h2sep (insert j2 S1) hrep
    rw [hcomp2] at htr
    exact htr.symm
  obtain ⟨f2_raw, hf2A, hf2B⟩ := hahn_banach_finset_sep (S2.biUnion X) ((insert j2 S1).biUnion X) hsep2
  -- Perturb f0, f1, f2 sequentially so all three are injective and pairwise non-collinear on X j2!
  let diffs := ((X j2 ×ˢ X j2).filter fun p => p.1 ≠ p.2).image fun p => p.1 - p.2
  have hdiffs_nz : ∀ v ∈ diffs, v ≠ 0 := by
    intro v hv; obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hv
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hab).2
  obtain ⟨f0L, hf0LA, hf0LB, hf0V⟩ := perturb_functional f0_raw.1 f0_raw.2 _ _ diffs hf0A hf0B hdiffs_nz
  let f0 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f0L, f0_raw.2)
  have hf0_inj : Set.InjOn (evalAff f0) (X j2 : Set (ℝ^3)) := by
    intro u hu v hv heq
    by_contra hne
    have hmem : u - v ∈ diffs := Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne⟩, rfl⟩
    have h0 : f0L (u - v) = 0 := by rw [map_sub]; dsimp [evalAff, f0] at heq; linarith
    exact hf0V _ hmem h0
  let triVec (g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) : Finset (ℝ^3) :=
    ((X j2 ×ˢ (X j2 ×ˢ X j2)).filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2).image
      fun t => (evalAff g t.2.2 - evalAff g t.2.1) • t.1 +
        (evalAff g t.1 - evalAff g t.2.2) • t.2.1 +
        (evalAff g t.2.1 - evalAff g t.1) • t.2.2
  have htri_nz (g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (hg_inj : Set.InjOn (evalAff g) (X j2 : Set (ℝ^3))) :
      ∀ v ∈ triVec g, v ≠ 0 := by
    intro v hv
    obtain ⟨⟨u, a, b⟩, ht, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hmem, h1, h2, h3⟩ := Finset.mem_filter.mp ht
    obtain ⟨hu, hab⟩ := Finset.mem_product.mp hmem
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have hne : evalAff g b - evalAff g a ≠ 0 := sub_ne_zero.mpr (fun h => h2 (hg_inj hb ha h).symm)
    exact affine_comb_ne_zero_of_gp hgp_j2 hu ha hb h1 h2 h3 (by ring) hne
  have htri_nocol (ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (hgb : ∀ v ∈ triVec ga, gb.1 v ≠ 0) :
      NoThreeCollinear2 ((X j2).image fun u => (evalAff ga u, evalAff gb u)) := by
    intro p hp q hq r hr hpq hqr hpr hori
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    have h1 : u ≠ a := fun h => hpq (by rw [h])
    have h2 : a ≠ b := fun h => hqr (by rw [h])
    have h3 : u ≠ b := fun h => hpr (by rw [h])
    have hmem : (evalAff ga b - evalAff ga a) • u + (evalAff ga u - evalAff ga b) • a +
        (evalAff ga a - evalAff ga u) • b ∈ triVec ga :=
      Finset.mem_image.mpr ⟨(u, a, b), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hu, Finset.mem_product.mpr ⟨ha, hb⟩⟩, h1, h2, h3⟩, rfl⟩
    apply hgb _ hmem
    rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    calc (evalAff ga b - evalAff ga a) * gb.1 u + (evalAff ga u - evalAff ga b) * gb.1 a +
          (evalAff ga a - evalAff ga u) * gb.1 b
      _ = orient2 (evalAff ga u, evalAff gb u) (evalAff ga a, evalAff gb a) (evalAff ga b, evalAff gb b) := by
          unfold orient2 evalAff; ring
      _ = 0 := hori
  -- Perturb f1 avoiding diffs ∪ triVec f0
  obtain ⟨f1L, hf1LA, hf1LB, hf1V⟩ := perturb_functional f1_raw.1 f1_raw.2 _ _ (diffs ∪ triVec f0)
    hf1A hf1B (fun v hv => by rcases Finset.mem_union.mp hv with h | h; exact hdiffs_nz v h; exact htri_nz f0 hf0_inj v h)
  let f1 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f1L, f1_raw.2)
  have hf1_inj : Set.InjOn (evalAff f1) (X j2 : Set (ℝ^3)) := by
    intro u hu v hv heq; by_contra hne
    have hmem : u - v ∈ diffs ∪ triVec f0 := Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne⟩, rfl⟩)
    exact hf1V _ hmem (by rw [map_sub]; dsimp [evalAff, f1] at heq; linarith)
  -- Perturb f2 avoiding diffs ∪ triVec f0 ∪ triVec f1
  obtain ⟨f2L, hf2LA, hf2LB, hf2V⟩ := perturb_functional f2_raw.1 f2_raw.2 _ _ (diffs ∪ triVec f0 ∪ triVec f1)
    hf2A hf2B (fun v hv => by
      rcases Finset.mem_union.mp hv with h | h
      · rcases Finset.mem_union.mp h with h1 | h2
        · exact hdiffs_nz v h1
        · exact htri_nz f0 hf0_inj v h2
      · exact htri_nz f1 hf1_inj v h)
  let f2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f2L, f2_raw.2)
  have hf2_inj : Set.InjOn (evalAff f2) (X j2 : Set (ℝ^3)) := by
    intro u hu v hv heq; by_contra hne
    have hmem : u - v ∈ diffs ∪ triVec f0 ∪ triVec f1 := Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne⟩, rfl⟩))
    exact hf2V _ hmem (by rw [map_sub]; dsimp [evalAff, f2] at heq; linarith)
  -- Choose ε > 0 strictly smaller than all margins!
  let G0 := ((Finset.univ.erase j2).biUnion X).image fun u => -evalAff f0 u
  let G1a := (S1.biUnion X).image fun u => evalAff f1 u
  let G1b := ((insert j2 S2).biUnion X).image fun u => -evalAff f1 u
  let G2a := ((insert j2 S1).biUnion X).image fun u => evalAff f2 u
  let G2b := (S2.biUnion X).image fun u => -evalAff f2 u
  let allG := insert (1 : ℝ) (G0 ∪ G1a ∪ G1b ∪ G2a ∪ G2b)
  have hallG_ne : allG.Nonempty := Finset.insert_nonempty _ _
  let ε := allG.min' hallG_ne / 2
  have hmin_pos : 0 < allG.min' hallG_ne := by
    have hmem := Finset.min'_mem allG hallG_ne
    rcases Finset.mem_insert.mp hmem with h | h
    · linarith
    · simp only [Finset.mem_union, G0, G1a, G1b, G2a, G2b, Finset.mem_image] at h
      rcases h with ((((⟨u, hu, heq⟩ | ⟨u, hu, heq⟩) | ⟨u, hu, heq⟩) | ⟨u, hu, heq⟩) | ⟨u, hu, heq⟩)
      · rw [← heq]; dsimp [evalAff, f0]; linarith [hf0LA u hu]
      · rw [← heq]; exact hf1LB u hu
      · rw [← heq]; dsimp [evalAff, f1]; linarith [hf1LA u hu]
      · rw [← heq]; exact hf2LB u hu
      · rw [← heq]; dsimp [evalAff, f2]; linarith [hf2LA u hu]
  have hle_min (v : ℝ) (hv : v ∈ allG) : ε ≤ v := by
    have h1 := Finset.min'_le allG v hv; dsimp [ε]; linarith
  refine ⟨f0, f1, f2, ε, half_pos hmin_pos, ?_, hf0LB, ?_, ?_, ?_, ?_,
    hf0_inj, hf1_inj, hf2_inj,
    htri_nocol f0 f1 (fun v hv => hf1V v (Finset.mem_union_right _ hv)),
    htri_nocol f0 f2 (fun v hv => hf2V v (Finset.mem_union_left _ (Finset.mem_union_right _ hv))),
    htri_nocol f1 f2 (fun v hv => hf2V v (Finset.mem_union_right _ hv))⟩
  · intro u hu
    have hmem : -evalAff f0 u ∈ allG := Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)))))
    linarith [hle_min _ hmem]
  · intro u hu
    exact hle_min _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))))))
  · intro u hu
    have hmem : -evalAff f1 u ∈ allG := Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hu))))
    linarith [hle_min _ hmem]
  · intro u hu
    exact hle_min _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))))
  · intro u hu
    have hmem : -evalAff f2 u ∈ allG := Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu))
    linarith [hle_min _ hmem]

/- ### Part 13: 3-Halfspace Wedge Cups-vs-Caps (Prop lem_es) -/

def ltPair (ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) (u v : ℝ^3) : Prop :=
  evalAff ga u < evalAff ga v ∧
  ∃ q1 q2 : ℝ, q1 ≤ 0 ∧ q2 ≤ 0 ∧ ∃ l : ℝ, 0 < l ∧ l < 1 ∧
    evalAff ga u = (1 - l) * q1 + l * evalAff ga v ∧
    evalAff gb u = (1 - l) * q2 + l * evalAff gb v

lemma ltPair_strictPO (ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) : IsStrictPO (ltPair ga gb) := by
  refine ⟨fun u h => lt_irrefl _ h.1, fun u v w huv hvw => ?_⟩
  obtain ⟨h1, q1, q2, hq1, hq2, l, hl0, hl1, hga1, hgb1⟩ := huv
  obtain ⟨h2, r1, r2, hr1, hr2, m, hm0, hm1, hga2, hgb2⟩ := hvw
  have hlm0 : 0 < l * m := mul_pos hl0 hm0
  have hlm1 : l * m < 1 := by nlinarith only [hl0, hl1, hm0, hm1]
  have hden : 0 < 1 - l * m := sub_pos.mpr hlm1
  let s1 := ((1 - l) * q1 + l * (1 - m) * r1) / (1 - l * m)
  let s2 := ((1 - l) * q2 + l * (1 - m) * r2) / (1 - l * m)
  refine ⟨h1.trans h2, s1, s2, ?_, ?_, l * m, hlm0, hlm1, ?_, ?_⟩
  · exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) hq1)
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hl0.le (by linarith)) hr1)) hden.le
  · exact div_nonpos_of_nonpos_of_nonneg (add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) hq2)
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hl0.le (by linarith)) hr2)) hden.le
  · dsimp [s1]; rw [mul_div_cancel₀ _ hden.ne', hga1, hga2]; ring
  · dsimp [s2]; rw [mul_div_cancel₀ _ hden.ne', hgb1, hgb2]; ring

lemma ltPair_of_line_hit {ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ} {u v : ℝ^3}
    (hau : 0 < evalAff ga u) (hav : 0 < evalAff ga v)
    (ht : ∃ t : ℝ, evalAff ga ((1 - t) • u + t • v) ≤ 0 ∧ evalAff gb ((1 - t) • u + t • v) ≤ 0) :
    ltPair ga gb u v ∨ ltPair ga gb v u := by
  obtain ⟨t, hga, hgb⟩ := ht
  set q1 := evalAff ga ((1 - t) • u + t • v)
  set q2 := evalAff gb ((1 - t) • u + t • v)
  have hq1e : q1 = (1 - t) * evalAff ga u + t * evalAff ga v := evalAff_convex_comb ga (1 - t) t (by ring) u v
  have hq2e : q2 = (1 - t) * evalAff gb u + t * evalAff gb v := evalAff_convex_comb gb (1 - t) t (by ring) u v
  by_cases ht0 : t < 0
  · left
    have hden : 0 < 1 - t := by linarith
    let l := -t / (1 - t)
    have hl0 : 0 < l := div_pos (by linarith) hden
    have hl1 : l < 1 := (div_lt_one hden).mpr (by linarith)
    have hga_u : evalAff ga u = (1 - l) * q1 + l * evalAff ga v := by
      dsimp [l]; field_simp [hden.ne']; linarith [hq1e]
    have hgb_u : evalAff gb u = (1 - l) * q2 + l * evalAff gb v := by
      dsimp [l]; field_simp [hden.ne']; linarith [hq2e]
    refine ⟨?_, q1, q2, hga, hgb, l, hl0, hl1, hga_u, hgb_u⟩
    nlinarith only [hga_u, hga, hl0, hl1, hav]
  · have ht1 : 1 < t := by
      by_contra hle; push Not at hle
      have : 0 < (1 - t) * evalAff ga u + t * evalAff ga v := by
        have ht0' : 0 ≤ t := not_lt.mp ht0
        by_cases hz : t = 0
        · rw [hz]; linarith
        · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hau.le) (mul_pos (lt_of_le_of_ne ht0' (Ne.symm hz)) hav)
      linarith
    right
    have htpos : 0 < t := by linarith
    let l := (t - 1) / t
    have hl0 : 0 < l := div_pos (by linarith) htpos
    have hl1 : l < 1 := (div_lt_one htpos).mpr (by linarith)
    have hga_v : evalAff ga v = (1 - l) * q1 + l * evalAff ga u := by
      dsimp [l]; field_simp [htpos.ne']; linarith [hq1e]
    have hgb_v : evalAff gb v = (1 - l) * q2 + l * evalAff gb u := by
      dsimp [l]; field_simp [htpos.ne']; linarith [hq2e]
    refine ⟨?_, q1, q2, hga, hgb, l, hl0, hl1, hga_v, hgb_v⟩
    nlinarith only [hga_v, hga, hl0, hl1, hau]

lemma line_hit_of_ltPair {ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ} {u v : ℝ^3}
    (h : ltPair ga gb u v) :
    ∃ t : ℝ, evalAff ga ((1 - t) • u + t • v) ≤ 0 ∧ evalAff gb ((1 - t) • u + t • v) ≤ 0 := by
  obtain ⟨_, q1, q2, hq1, hq2, l, _, hl1, hga, hgb⟩ := h
  have hden : 0 < 1 - l := sub_pos.mpr hl1
  refine ⟨-l / (1 - l), ?_, ?_⟩
  · rw [evalAff_convex_comb ga _ _ (by ring)]
    have heq : (1 - -l / (1 - l)) * evalAff ga u + -l / (1 - l) * evalAff ga v = q1 := by
      field_simp [hden.ne']; linarith [hga]
    linarith
  · rw [evalAff_convex_comb gb _ _ (by ring)]
    have heq : (1 - -l / (1 - l)) * evalAff gb u + -l / (1 - l) * evalAff gb v = q2 := by
      field_simp [hden.ne']; linarith [hgb]
    linarith

lemma cup2_convex_independent (K : Finset (ℝ × ℝ))
    (hxinj : ∀ p ∈ K, ∀ q ∈ K, p.1 = q.1 → p = q) (hcup : IsCup2 K) :
    ConvexIndependent ℝ (Subtype.val : ↥(K : Set (ℝ × ℝ)) → ℝ × ℝ) := by
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro p hp hmem
  have hpK : p ∈ K := hp
  let L := K.filter fun q => q.1 < p.1
  let R := K.filter fun q => p.1 < q.1
  have hpart : ∀ q ∈ K, q ≠ p → q ∈ L ∨ q ∈ R := fun q hq hne => by
    rcases lt_or_gt_of_ne (fun h => hne (hxinj q hq p hpK h)) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hq, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hq, h⟩)
  -- Find a slope m strictly between all left slopes and all right slopes!
  have hex_m : ∃ m : ℝ, (∀ q ∈ L, slope2 q p < m) ∧ (∀ q ∈ R, m < slope2 p q) := by
    have hLR : ∀ a ∈ L, ∀ b ∈ R, slope2 a p < slope2 p b := fun a ha b hb =>
      hcup a (Finset.mem_filter.mp ha).1 p hpK b (Finset.mem_filter.mp hb).1
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    rcases L.eq_empty_or_nonempty with hL | hLne
    · rcases R.eq_empty_or_nonempty with hR | hRne
      · exact ⟨0, by simp [hL], by simp [hR]⟩
      · obtain ⟨b, hbR, hbmin⟩ := Finset.exists_min_image R (fun q => slope2 p q) hRne
        exact ⟨slope2 p b - 1, by simp [hL], fun q hq => by linarith [hbmin q hq]⟩
    · rcases R.eq_empty_or_nonempty with hR | hRne
      · obtain ⟨a, haL, hamax⟩ := Finset.exists_max_image L (fun q => slope2 q p) hLne
        exact ⟨slope2 a p + 1, fun q hq => by linarith [hamax q hq], by simp [hR]⟩
      · obtain ⟨a, haL, hamax⟩ := Finset.exists_max_image L (fun q => slope2 q p) hLne
        obtain ⟨b, hbR, hbmin⟩ := Finset.exists_min_image R (fun q => slope2 p q) hRne
        have hlt := hLR a haL b hbR
        exact ⟨(slope2 a p + slope2 p b) / 2,
          fun q hq => by linarith [hamax q hq], fun q hq => by linarith [hbmin q hq]⟩
  obtain ⟨m, hmL, hmR⟩ := hex_m
  let f : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun q => q.2 - m * q.1
      map_add' := fun u v => by simp; ring
      map_smul' := fun c u => by simp; ring }
  have hsub : convexHull ℝ ((K : Set (ℝ × ℝ)) \ {p}) ⊆ {q | f p < f q} := by
    apply convexHull_min _ (convex_halfSpace_gt f.isLinear (f p))
    rintro q ⟨hqK, hqne⟩
    change f p < f q
    dsimp [f]
    rcases hpart q hqK hqne with hqL | hqR
    · have hlt := (Finset.mem_filter.mp hqL).2
      have hsl := hmL q hqL
      unfold slope2 at hsl
      have hpos : 0 < p.1 - q.1 := sub_pos.mpr hlt
      have := (div_lt_iff₀ hpos).mp hsl
      linarith
    · have hlt := (Finset.mem_filter.mp hqR).2
      have hsl := hmR q hqR
      unfold slope2 at hsl
      have hpos : 0 < q.1 - p.1 := sub_pos.mpr hlt
      have := (lt_div_iff₀ hpos).mp hsl
      linarith
  have : f p < f p := hsub hmem
  exact lt_irrefl _ this

lemma antichain_cap_is_wedge_cap {ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ}
    {P : Set (ℝ^3)} (hP : ∀ u ∈ P, evalAff ga u ≤ 0 ∧ evalAff gb u ≤ 0)
    {X' : Finset (ℝ^3)} (hX'pos : ∀ u ∈ X', 0 < evalAff ga u)
    (hga_inj : Set.InjOn (evalAff ga) (X' : Set (ℝ^3)))
    (hgb_inj : Set.InjOn (evalAff gb) (X' : Set (ℝ^3)))
    (hanti : IsAntichain (ltPair ga gb) X')
    {K : Finset (ℝ^3)} (hKX' : K ⊆ X')
    (hcap : IsCap2 (K.image fun u => (evalAff ga u, evalAff gb u))) :
    ∀ y ∈ K, y ∉ convexHull ℝ (P ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))) := by
  let π (u : ℝ^3) : ℝ × ℝ := (evalAff ga u, evalAff gb u)
  -- Key antichain consequences: for u, v ∈ X' with x u < x v, y u > y v AND y-intercept > 0!
  have hanti_slope : ∀ u ∈ X', ∀ v ∈ X', (π u).1 < (π v).1 →
      (π v).2 < (π u).2 ∧ 0 < (π v).1 * (π u).2 - (π u).1 * (π v).2 := by
    intro u hu v hv hlt
    have hxu : 0 < (π u).1 := hX'pos u hu
    have hxv : 0 < (π v).1 := hX'pos v hv
    have hne : u ≠ v := fun h => hlt.ne (by rw [h])
    have hnot_hit : ∀ t : ℝ, ¬ (evalAff ga ((1 - t) • u + t • v) ≤ 0 ∧ evalAff gb ((1 - t) • u + t • v) ≤ 0) := by
      intro t ht
      rcases ltPair_of_line_hit hxu hxv ⟨t, ht⟩ with h | h
      · exact hanti u hu v hv h
      · exact hanti v hv u hu h
    have hy_gt : (π v).2 < (π u).2 := by
      rcases lt_or_gt_of_ne (fun h => hne (hgb_inj hu hv h)) with hylt | hygt
      · exfalso
        have hdx : 0 < (π v).1 - (π u).1 := sub_pos.mpr hlt
        have hdy : 0 < (π v).2 - (π u).2 := sub_pos.mpr hylt
        let t := min (-(π u).1 / ((π v).1 - (π u).1)) (-(π u).2 / ((π v).2 - (π u).2)) - 1
        apply hnot_hit t
        rw [evalAff_convex_comb ga _ _ (by ring), evalAff_convex_comb gb _ _ (by ring)]
        have ht1 : t ≤ -(π u).1 / ((π v).1 - (π u).1) := by dsimp [t]; linarith [min_le_left (-(π u).1 / ((π v).1 - (π u).1)) (-(π u).2 / ((π v).2 - (π u).2))]
        have ht2 : t ≤ -(π u).2 / ((π v).2 - (π u).2) := by dsimp [t]; linarith [min_le_right (-(π u).1 / ((π v).1 - (π u).1)) (-(π u).2 / ((π v).2 - (π u).2))]
        have h1 := (le_div_iff₀ hdx).mp ht1
        have h2 := (le_div_iff₀ hdy).mp ht2
        constructor <;> dsimp [π] at h1 h2 <;> nlinarith only [h1, h2]
      · exact hygt
    have hint_pos : 0 < (π v).1 * (π u).2 - (π u).1 * (π v).2 := by
      by_contra! hle
      have hdx : 0 < (π v).1 - (π u).1 := sub_pos.mpr hlt
      let t := -(π u).1 / ((π v).1 - (π u).1)
      apply hnot_hit t
      rw [evalAff_convex_comb ga _ _ (by ring), evalAff_convex_comb gb _ _ (by ring)]
      constructor
      · have heq : (1 - t) * (π u).1 + t * (π v).1 = 0 := by dsimp [t]; field_simp [hdx.ne']; ring
        dsimp [π] at heq; linarith
      · have heq : (1 - t) * (π u).2 + t * (π v).2 = ((π v).1 * (π u).2 - (π u).1 * (π v).2) / ((π v).1 - (π u).1) := by
          dsimp [t]; field_simp [hdx.ne']; ring
        dsimp [π] at heq; rw [heq]; exact div_nonpos_of_nonpos_of_nonneg hle hdx.le
    exact ⟨hy_gt, hint_pos⟩
  intro y hyK hmem
  have hyX' : y ∈ X' := hKX' hyK
  have hxy : 0 < (π y).1 := hX'pos y hyX'
  let L := K.filter fun u => (π u).1 < (π y).1
  let R := K.filter fun u => (π y).1 < (π u).1
  have hpart : ∀ u ∈ K, u ≠ y → u ∈ L ∨ u ∈ R := fun u hu hne => by
    rcases lt_or_gt_of_ne (fun h => hne (hga_inj (hKX' hu) hyX' h)) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hu, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hu, h⟩)
  -- Find slope m < 0 with: ∀ u ∈ L, m < slope2 (π u) (π y); ∀ u ∈ R, slope2 (π y) (π u) < m; AND 0 < (π y).2 - m * (π y).1!
  have hex_m : ∃ m : ℝ, m < 0 ∧ 0 < (π y).2 - m * (π y).1 ∧
      (∀ u ∈ L, m < slope2 (π u) (π y)) ∧ (∀ u ∈ R, slope2 (π y) (π u) < m) := by
    have hLR : ∀ a ∈ L, ∀ b ∈ R, slope2 (π y) (π b) < slope2 (π a) (π y) := fun a ha b hb =>
      hcap (π a) (Finset.mem_image_of_mem π (Finset.mem_filter.mp ha).1)
        (π y) (Finset.mem_image_of_mem π hyK)
        (π b) (Finset.mem_image_of_mem π (Finset.mem_filter.mp hb).1)
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hL_prop (a : ℝ^3) (ha : a ∈ L) : slope2 (π a) (π y) < 0 ∧ 0 < (π y).2 - slope2 (π a) (π y) * (π y).1 := by
      have haK := (Finset.mem_filter.mp ha).1
      have hlt := (Finset.mem_filter.mp ha).2
      obtain ⟨hy_gt, hint⟩ := hanti_slope a (hKX' haK) y hyX' hlt
      have hdx : 0 < (π y).1 - (π a).1 := sub_pos.mpr hlt
      constructor
      · unfold slope2; exact div_neg_of_neg_of_pos (sub_neg.mpr hy_gt) hdx
      · have heq : (π y).2 - slope2 (π a) (π y) * (π y).1 =
            ((π y).1 * (π a).2 - (π a).1 * (π y).2) / ((π y).1 - (π a).1) := by
          unfold slope2; field_simp [hdx.ne']; ring
        rw [heq]; exact div_pos hint hdx
    have hR_prop (b : ℝ^3) (hb : b ∈ R) : slope2 (π y) (π b) < 0 ∧ 0 < (π y).2 - slope2 (π y) (π b) * (π y).1 := by
      have hbK := (Finset.mem_filter.mp hb).1
      have hlt := (Finset.mem_filter.mp hb).2
      obtain ⟨hy_gt, hint⟩ := hanti_slope y hyX' b (hKX' hbK) hlt
      have hdx : 0 < (π b).1 - (π y).1 := sub_pos.mpr hlt
      constructor
      · unfold slope2; exact div_neg_of_neg_of_pos (sub_neg.mpr hy_gt) hdx
      · have heq : (π y).2 - slope2 (π y) (π b) * (π y).1 =
            ((π b).1 * (π y).2 - (π y).1 * (π b).2) / ((π b).1 - (π y).1) := by
          unfold slope2; field_simp [hdx.ne']; ring
        rw [heq]; exact div_pos hint hdx
    rcases L.eq_empty_or_nonempty with hL | hLne
    · rcases R.eq_empty_or_nonempty with hR | hRne
      · let m := min (-1) (((π y).2 - 1) / (π y).1)
        refine ⟨m, by dsimp [m]; linarith [min_le_left (-1 : ℝ) (((π y).2 - 1) / (π y).1)], ?_, by simp [hL], by simp [hR]⟩
        have hle : m ≤ ((π y).2 - 1) / (π y).1 := min_le_right _ _
        have := (le_div_iff₀ hxy).mp hle
        linarith
      · obtain ⟨b, hbR, hbmax⟩ := Finset.exists_max_image R (fun u => slope2 (π y) (π u)) hRne
        obtain ⟨hsneg, hint⟩ := hR_prop b hbR
        let δ := min (-slope2 (π y) (π b) / 2) (((π y).2 - slope2 (π y) (π b) * (π y).1) / (2 * (π y).1))
        have hδpos : 0 < δ := lt_min (by linarith) (div_pos hint (by linarith))
        let m := slope2 (π y) (π b) + δ
        refine ⟨m, ?_, ?_, by simp [hL], fun u hu => by linarith [hbmax u hu]⟩
        · dsimp [m]; linarith [min_le_left (-slope2 (π y) (π b) / 2) (((π y).2 - slope2 (π y) (π b) * (π y).1) / (2 * (π y).1))]
        · have hle : δ ≤ ((π y).2 - slope2 (π y) (π b) * (π y).1) / (2 * (π y).1) := min_le_right _ _
          have := (le_div_iff₀ (show 0 < 2 * (π y).1 by linarith)).mp hle
          dsimp [m]; nlinarith only [this, hint]
    · rcases R.eq_empty_or_nonempty with hR | hRne
      · obtain ⟨a, haL, hamin⟩ := Finset.exists_min_image L (fun u => slope2 (π u) (π y)) hLne
        obtain ⟨hsneg, hint⟩ := hL_prop a haL
        let m := slope2 (π a) (π y) - 1
        refine ⟨m, by dsimp [m]; linarith, by dsimp [m]; nlinarith only [hint, hxy],
          fun u hu => by dsimp [m]; linarith [hamin u hu], by simp [hR]⟩
      · obtain ⟨a, haL, hamin⟩ := Finset.exists_min_image L (fun u => slope2 (π u) (π y)) hLne
        obtain ⟨b, hbR, hbmax⟩ := Finset.exists_max_image R (fun u => slope2 (π y) (π u)) hRne
        obtain ⟨hsneg, hint⟩ := hL_prop a haL
        have hlt := hLR a haL b hbR
        let m := (slope2 (π a) (π y) + slope2 (π y) (π b)) / 2
        refine ⟨m, by dsimp [m]; linarith, by dsimp [m]; nlinarith only [hint, hlt, hxy],
          fun u hu => by dsimp [m]; linarith [hamin u hu],
          fun u hu => by dsimp [m]; linarith [hbmax u hu]⟩
  obtain ⟨m, hmneg, hmint, hmL, hmR⟩ := hex_m
  -- Affine functional h(u) = (-m) * ga u + gb u has h(y) > h(u) for ALL u ∈ P ∪ (K.erase y)!
  let hL : (ℝ^3) →ₗ[ℝ] ℝ := (-m) • ga.1 + gb.1
  let hC : ℝ := (-m) * ga.2 + gb.2
  have hval : ∀ u, hL u + hC = (-m) * (π u).1 + (π u).2 := fun u => by
    dsimp [hL, hC, π, evalAff]; ring
  have hsub : convexHull ℝ (P ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))) ⊆ {u | hL u < hL y} := by
    apply convexHull_min _ (convex_halfSpace_lt hL.isLinear (hL y))
    intro u hu
    change hL u < hL y
    suffices hsuff : hL u + hC < hL y + hC by linarith
    rw [hval u, hval y]
    rcases hu with huP | huK
    · obtain ⟨hga_le, hgb_le⟩ := hP u huP
      change (π u).1 ≤ 0 at hga_le; change (π u).2 ≤ 0 at hgb_le
      nlinarith only [hmneg, hmint, hga_le, hgb_le]
    · obtain ⟨hne, huK'⟩ := Finset.mem_erase.mp huK
      rcases hpart u huK' hne with huL | huR
      · have hlt := (Finset.mem_filter.mp huL).2
        have hsl := hmL u huL; unfold slope2 at hsl
        have hdx : 0 < (π y).1 - (π u).1 := sub_pos.mpr hlt
        have := (lt_div_iff₀ hdx).mp hsl
        linarith
      · have hlt := (Finset.mem_filter.mp huR).2
        have hsl := hmR u huR; unfold slope2 at hsl
        have hdx : 0 < (π u).1 - (π y).1 := sub_pos.mpr hlt
        have := (div_lt_iff₀ hdx).mp hsl
        linarith
  have : hL y < hL y := hsub hmem
  exact lt_irrefl _ this

lemma wedge_cups_vs_caps {g0 g1 g2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ}
    (Z : Finset (ℝ^3))
    (hg0pos : ∀ u ∈ Z, 0 < evalAff g0 u) (hg1pos : ∀ u ∈ Z, 0 < evalAff g1 u)
    (hg0inj : Set.InjOn (evalAff g0) (Z : Set (ℝ^3)))
    (hg1inj : Set.InjOn (evalAff g1) (Z : Set (ℝ^3)))
    (hg2inj : Set.InjOn (evalAff g2) (Z : Set (ℝ^3)))
    (hnc01 : NoThreeCollinear2 (Z.image fun u => (evalAff g0 u, evalAff g1 u)))
    (hnc02 : NoThreeCollinear2 (Z.image fun u => (evalAff g0 u, evalAff g2 u)))
    (hnc12 : NoThreeCollinear2 (Z.image fun u => (evalAff g1 u, evalAff g2 u)))
    (hPfree : ∀ u ∈ Z, ∀ v ∈ Z, u ≠ v → ∀ t : ℝ,
      ¬ (evalAff g0 ((1 - t) • u + t • v) ≤ 0 ∧
         evalAff g1 ((1 - t) • u + t • v) ≤ 0 ∧
         evalAff g2 ((1 - t) • u + t • v) ≤ 0))
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : (Nat.choose (a + b - 4) (a - 2)) ^ 3 < Z.card) :
    let P : Set (ℝ^3) := {u | evalAff g0 u ≤ 0 ∧ evalAff g1 u ≤ 0 ∧ evalAff g2 u ≤ 0}
    (∃ K ⊆ Z, K.card = a ∧ ∀ y ∈ K, y ∉ convexHull ℝ (P ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) ∨
    Erdos651.HasConvexSubset b Z := by
  intro P
  -- Step 1: By 1D Helly, any distinct u, v ∈ Z are incomparable in at least one of ltPair (g0,g1), (g0,g2), (g1,g2)
  have hincomp : ∀ u ∈ Z, ∀ v ∈ Z, u ≠ v →
      (¬ ltPair g0 g1 u v ∧ ¬ ltPair g0 g1 v u) ∨
      (¬ ltPair g0 g2 u v ∧ ¬ ltPair g0 g2 v u) ∨
      (¬ ltPair g1 g2 u v ∧ ¬ ltPair g1 g2 v u) := by
    intro u hu v hv hne
    by_contra h; push Not at h
    obtain ⟨h01, h02, h12⟩ := h
    have hhit01 : ∃ t : ℝ, evalAff g0 ((1 - t) • u + t • v) ≤ 0 ∧ evalAff g1 ((1 - t) • u + t • v) ≤ 0 := by
      by_cases hlt : ltPair g0 g1 u v
      · exact line_hit_of_ltPair hlt
      · obtain ⟨t, ht1, ht2⟩ := line_hit_of_ltPair (h01 hlt)
        exact ⟨1 - t, by simpa [sub_sub_cancel, add_comm] using ht1, by simpa [sub_sub_cancel, add_comm] using ht2⟩
    have hhit02 : ∃ t : ℝ, evalAff g0 ((1 - t) • u + t • v) ≤ 0 ∧ evalAff g2 ((1 - t) • u + t • v) ≤ 0 := by
      by_cases hlt : ltPair g0 g2 u v
      · exact line_hit_of_ltPair hlt
      · obtain ⟨t, ht1, ht2⟩ := line_hit_of_ltPair (h02 hlt)
        exact ⟨1 - t, by simpa [sub_sub_cancel, add_comm] using ht1, by simpa [sub_sub_cancel, add_comm] using ht2⟩
    have hhit12 : ∃ t : ℝ, evalAff g1 ((1 - t) • u + t • v) ≤ 0 ∧ evalAff g2 ((1 - t) • u + t • v) ≤ 0 := by
      by_cases hlt : ltPair g1 g2 u v
      · exact line_hit_of_ltPair hlt
      · obtain ⟨t, ht1, ht2⟩ := line_hit_of_ltPair (h12 hlt)
        exact ⟨1 - t, by simpa [sub_sub_cancel, add_comm] using ht1, by simpa [sub_sub_cancel, add_comm] using ht2⟩
    -- Apply Mathlib's Helly's theorem on ℝ (finrank ℝ ℝ + 1 = 2)!
    let gs : Fin 3 → ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := ![g0, g1, g2]
    let F (i : Fin 3) : Set ℝ := {t : ℝ | evalAff (gs i) ((1 - t) • u + t • v) ≤ 0}
    have hFconv : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Convex ℝ (F i) := fun i _ => by
      let L : ℝ →ₗ[ℝ] ℝ := (evalAff (gs i) v - evalAff (gs i) u) • LinearMap.id
      have hFeq : F i = {t : ℝ | L t ≤ -evalAff (gs i) u} := by
        ext t
        change evalAff (gs i) ((1 - t) • u + t • v) ≤ 0 ↔ L t ≤ -evalAff (gs i) u
        simp only [L, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
        rw [evalAff_convex_comb (gs i) _ _ (by ring)]; constructor <;> intro h <;> linarith
      rw [hFeq]; exact convex_halfSpace_le L.isLinear _
    have hFinter : ∀ I ⊆ (Finset.univ : Finset (Fin 3)), I.card ≤ Module.finrank ℝ ℝ + 1 →
        (⋂ i ∈ I, F i).Nonempty := by
      intro I _ hIc
      rw [Module.finrank_self] at hIc
      have hpair : ∀ i j : Fin 3, (F i ∩ F j).Nonempty := fun i j => by
        fin_cases i <;> fin_cases j
        · obtain ⟨t, h1, _⟩ := hhit01; exact ⟨t, h1, h1⟩
        · obtain ⟨t, h1, h2⟩ := hhit01; exact ⟨t, h1, h2⟩
        · obtain ⟨t, h1, h2⟩ := hhit02; exact ⟨t, h1, h2⟩
        · obtain ⟨t, h1, h2⟩ := hhit01; exact ⟨t, h2, h1⟩
        · obtain ⟨t, _, h2⟩ := hhit01; exact ⟨t, h2, h2⟩
        · obtain ⟨t, h1, h2⟩ := hhit12; exact ⟨t, h1, h2⟩
        · obtain ⟨t, h1, h2⟩ := hhit02; exact ⟨t, h2, h1⟩
        · obtain ⟨t, h1, h2⟩ := hhit12; exact ⟨t, h2, h1⟩
        · obtain ⟨t, _, h2⟩ := hhit02; exact ⟨t, h2, h2⟩
      rcases I.eq_empty_or_nonempty with rfl | hIne
      · exact ⟨0, by simp⟩
      · rcases Nat.le_succ_iff.mp hIc with hle1 | h2
        · have hI1 : I.card = 1 := by have := Finset.card_pos.mpr hIne; omega
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI1
          obtain ⟨t, ht, _⟩ := hpair i i; exact ⟨t, by simpa using ht⟩
        · obtain ⟨i, j, _, rfl⟩ := Finset.card_eq_two.mp h2
          obtain ⟨t, hi, hj⟩ := hpair i j
          refine ⟨t, Set.mem_iInter₂.mpr fun r hr => ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl <;> assumption
    obtain ⟨t, ht⟩ := Convex.helly_theorem' hFconv hFinter
    exact hPfree u hu v hv hne t
      ⟨Set.mem_iInter₂.mp ht 0 (Finset.mem_univ _),
       Set.mem_iInter₂.mp ht 1 (Finset.mem_univ _),
       Set.mem_iInter₂.mp ht 2 (Finset.mem_univ _)⟩
  -- Helper: finish from a large antichain for any single pair (ga, gb)!
  have finish_pair (ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ)
      (hPab : ∀ u ∈ P, evalAff ga u ≤ 0 ∧ evalAff gb u ≤ 0)
      (hapos : ∀ u ∈ Z, 0 < evalAff ga u)
      (hainj : Set.InjOn (evalAff ga) (Z : Set (ℝ^3)))
      (hbinj : Set.InjOn (evalAff gb) (Z : Set (ℝ^3)))
      (hnc : NoThreeCollinear2 (Z.image fun u => (evalAff ga u, evalAff gb u)))
      (X' : Finset (ℝ^3)) (hX'Z : X' ⊆ Z) (hanti : IsAntichain (ltPair ga gb) X')
      (hX'card : Nat.choose (a + b - 4) (a - 2) < X'.card) :
      (∃ K ⊆ Z, K.card = a ∧ ∀ y ∈ K, y ∉ convexHull ℝ (P ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) ∨
      Erdos651.HasConvexSubset b Z := by
    let π (u : ℝ^3) : ℝ × ℝ := (evalAff ga u, evalAff gb u)
    have hπinj : Set.InjOn π (X' : Set (ℝ^3)) := fun u hu v hv h =>
      hainj (hX'Z hu) (hX'Z hv) (congrArg Prod.fst h)
    let Y := X'.image π
    have hYcard : Y.card = X'.card := Finset.card_image_of_injOn hπinj
    have hYxinj : ∀ p ∈ Y, ∀ q ∈ Y, p.1 = q.1 → p = q := by
      intro p hp q hq heq
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      rw [hainj (hX'Z hu) (hX'Z hv) heq]
    have hYgp : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y, p.1 < q.1 → q.1 < r.1 → slope2 p q ≠ slope2 q r := by
      intro p hp q hq r hr hpq hqr heq
      have hYsub : Y ⊆ Z.image π := Finset.image_subset_image hX'Z
      have hne1 : p ≠ q := fun h => hpq.ne (congrArg Prod.fst h)
      have hne2 : q ≠ r := fun h => hqr.ne (congrArg Prod.fst h)
      have hne3 : p ≠ r := fun h => (hpq.trans hqr).ne (congrArg Prod.fst h)
      apply hnc p (hYsub hp) q (hYsub hq) r (hYsub hr) hne1 hne2 hne3
      rw [orient2_eq_slope_diff hpq hqr, heq, sub_self, mul_zero]
    rcases erdos_szekeres_cups_caps (a + b) a b rfl ha hb Y hYxinj hYgp (by omega) with
      ⟨K2, hK2Y, hK2cap, hK2card⟩ | ⟨U2, hU2Y, hU2cup, hU2card⟩
    · obtain ⟨K, hKX', hKimg, hKcard⟩ := finite_image_pullback π X' K2 hK2Y hπinj
      left
      refine ⟨K, hKX'.trans hX'Z, hKcard.trans hK2card, ?_⟩
      exact antichain_cap_is_wedge_cap hPab (fun u hu => hapos u (hX'Z hu))
        (hainj.mono hX'Z) (hbinj.mono hX'Z) hanti hKX' (hKimg.symm ▸ hK2cap)
    · right
      obtain ⟨U, hUX', hUimg, hUcard⟩ := finite_image_pullback π X' U2 hU2Y hπinj
      refine ⟨U, hUX'.trans hX'Z, hUcard.trans hU2card, ?_⟩
      have hU2cvx := cup2_convex_independent U2 (fun p hp q hq => hYxinj p (hU2Y hp) q (hU2Y hq)) hU2cup
      rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hU2cvx ⊢
      intro y hyU hyhull
      have hπy : π y ∈ (U2 : Set (ℝ × ℝ)) := by rw [← hUimg]; exact Finset.mem_image_of_mem π hyU
      apply hU2cvx (π y) hπy
      let L : (ℝ^3) →ₗ[ℝ] (ℝ × ℝ) := LinearMap.prod ga.1 gb.1
      let aff : (ℝ^3) →ᵃ[ℝ] (ℝ × ℝ) :=
        { toFun := π
          linear := L
          map_vadd' := fun p v => by
            ext <;> simp [π, evalAff, L, vadd_eq_add, map_add] <;> ring }
      have himg : aff '' ((U : Set (ℝ^3)) \ {y}) ⊆ (U2 : Set (ℝ × ℝ)) \ {π y} := by
        rintro _ ⟨u, ⟨huU, hune⟩, rfl⟩
        refine ⟨by rw [← hUimg]; exact Finset.mem_image_of_mem π huU,
          fun he => hune (hπinj (hUX' huU) (hUX' hyU) he)⟩
      apply convexHull_mono himg
      rw [← AffineMap.image_convexHull]
      exact ⟨y, hyhull, rfl⟩
  -- Apply dilworth_three_orders and dispatch!
  rcases dilworth_three_orders (ltPair_strictPO g0 g1) (ltPair_strictPO g0 g2) (ltPair_strictPO g1 g2)
      Z hincomp (Nat.choose (a + b - 4) (a - 2)) hcard with
    ⟨X', hX'Z, hanti, hX'c⟩ | ⟨X', hX'Z, hanti, hX'c⟩ | ⟨X', hX'Z, hanti, hX'c⟩
  · exact finish_pair g0 g1 (fun u hu => ⟨hu.1, hu.2.1⟩) hg0pos hg0inj hg1inj hnc01 X' hX'Z hanti hX'c
  · exact finish_pair g0 g2 (fun u hu => ⟨hu.1, hu.2.2⟩) hg0pos hg0inj hg2inj hnc02 X' hX'Z hanti hX'c
  · exact finish_pair g1 g2 (fun u hu => ⟨hu.2.1, hu.2.2⟩) hg1pos hg1inj hg2inj hnc12 X' hX'Z hanti hX'c

/- ### Part 14: Main Theorem (Pohoata–Zakharov 3D Subexponential Bound) -/

lemma no_line_meets_wedge1_wedge2_X {f0 f1 f2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ} {ε : ℝ} (hε : 0 < ε)
    {u v p1 p2 : ℝ^3}
    (hv0 : 0 < evalAff f0 v) (hv1 : evalAff f1 v ≤ -ε) (hv2 : ε ≤ evalAff f2 v)
    (hp1_0 : evalAff f0 p1 ≤ -ε) (hp1_1 : ε ≤ evalAff f1 p1) (hp1_2 : ε ≤ evalAff f2 p1)
    (hp2_0 : evalAff f0 p2 ≤ -ε) (hp2_1 : evalAff f1 p2 ≤ -ε) (hp2_2 : evalAff f2 p2 ≤ -ε)
    {l : ℝ} (hu_eq : u = (1 - l) • p1 + l • v)
    {t : ℝ} (hp2_eq : p2 = (1 - t) • u + t • v) : False := by
  let s := (1 - t) * (1 - l)
  have hp2_comb : p2 = s • p1 + (1 - s) • v := by
    rw [hp2_eq, hu_eq, smul_add, smul_smul, smul_smul]
    calc ((1 - t) * (1 - l)) • p1 + ((1 - t) * l) • v + t • v
      _ = ((1 - t) * (1 - l)) • p1 + ((1 - t) * l + t) • v := by rw [add_smul]; abel
      _ = s • p1 + (1 - s) • v := by congr 2; dsimp [s]; ring
  have h0 : evalAff f0 p2 = s * evalAff f0 p1 + (1 - s) * evalAff f0 v := by
    rw [hp2_comb, evalAff_convex_comb f0 s (1 - s) (by ring)]
  have h1 : evalAff f1 p2 = s * evalAff f1 p1 + (1 - s) * evalAff f1 v := by
    rw [hp2_comb, evalAff_convex_comb f1 s (1 - s) (by ring)]
  have h2 : evalAff f2 p2 = s * evalAff f2 p1 + (1 - s) * evalAff f2 v := by
    rw [hp2_comb, evalAff_convex_comb f2 s (1 - s) (by ring)]
  have hs_pos : 0 < s := by nlinarith only [h0, hv0, hp1_0, hp2_0, hε]
  have hs_gt1 : 1 < s := by nlinarith only [h2, hv2, hp1_2, hp2_2, hs_pos, hε]
  nlinarith only [h1, hv1, hp1_1, hp2_1, hs_pos, hs_gt1, hε]

lemma noThreeCollinear2_scale_shift {A S : Finset (ℝ^3)} (hAS : A ⊆ S)
    {fa fb ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ} {sa sb ca cb : ℝ} (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (hga : ∀ u, evalAff ga u = sa * evalAff fa u + ca)
    (hgb : ∀ u, evalAff gb u = sb * evalAff fb u + cb)
    (hnc : NoThreeCollinear2 (S.image fun u => (evalAff fa u, evalAff fb u))) :
    NoThreeCollinear2 (A.image fun u => (evalAff ga u, evalAff gb u)) := by
  intro p hp q hq r hr hpq hqr hpr hori
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hne : ∀ x y : ℝ^3, (evalAff ga x, evalAff gb x) ≠ (evalAff ga y, evalAff gb y) →
      (evalAff fa x, evalAff fb x) ≠ (evalAff fa y, evalAff fb y) := fun x y hxy heq => by
    have h1 : evalAff fa x = evalAff fa y := congrArg Prod.fst heq
    have h2 : evalAff fb x = evalAff fb y := congrArg Prod.snd heq
    exact hxy (Prod.ext (by rw [hga x, hga y, h1]) (by rw [hgb x, hgb y, h2]))
  apply hnc _ (Finset.mem_image_of_mem _ (hAS hu)) _ (Finset.mem_image_of_mem _ (hAS hv))
    _ (Finset.mem_image_of_mem _ (hAS hw)) (hne u v hpq) (hne v w hqr) (hne u w hpr)
  have hmul : sa * sb * orient2 (evalAff fa u, evalAff fb u) (evalAff fa v, evalAff fb v) (evalAff fa w, evalAff fb w) = 0 := by
    calc sa * sb * orient2 (evalAff fa u, evalAff fb u) (evalAff fa v, evalAff fb v) (evalAff fa w, evalAff fb w)
      _ = orient2 (evalAff ga u, evalAff gb u) (evalAff ga v, evalAff gb v) (evalAff ga w, evalAff gb w) := by
          unfold orient2; rw [hga u, hga v, hga w, hgb u, hgb v, hgb w]; ring
      _ = 0 := hori
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hsa hsb)

lemma noThreeCollinear2_scale_shift_swap {A S : Finset (ℝ^3)} (hAS : A ⊆ S)
    {fa fb ga gb : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ} {sa sb ca cb : ℝ} (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (hga : ∀ u, evalAff ga u = sb * evalAff fb u + cb)
    (hgb : ∀ u, evalAff gb u = sa * evalAff fa u + ca)
    (hnc : NoThreeCollinear2 (S.image fun u => (evalAff fa u, evalAff fb u))) :
    NoThreeCollinear2 (A.image fun u => (evalAff ga u, evalAff gb u)) := by
  intro p hp q hq r hr hpq hqr hpr hori
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hne : ∀ x y : ℝ^3, (evalAff ga x, evalAff gb x) ≠ (evalAff ga y, evalAff gb y) →
      (evalAff fa x, evalAff fb x) ≠ (evalAff fa y, evalAff fb y) := fun x y hxy heq => by
    have h1 : evalAff fa x = evalAff fa y := congrArg Prod.fst heq
    have h2 : evalAff fb x = evalAff fb y := congrArg Prod.snd heq
    exact hxy (Prod.ext (by rw [hga x, hga y, h2]) (by rw [hgb x, hgb y, h1]))
  apply hnc _ (Finset.mem_image_of_mem _ (hAS hu)) _ (Finset.mem_image_of_mem _ (hAS hv))
    _ (Finset.mem_image_of_mem _ (hAS hw)) (hne u v hpq) (hne v w hqr) (hne u w hpr)
  have hmul : -(sa * sb) * orient2 (evalAff fa u, evalAff fb u) (evalAff fa v, evalAff fb v) (evalAff fa w, evalAff fb w) = 0 := by
    calc -(sa * sb) * orient2 (evalAff fa u, evalAff fb u) (evalAff fa v, evalAff fb v) (evalAff fa w, evalAff fb w)
      _ = orient2 (evalAff ga u, evalAff gb u) (evalAff ga v, evalAff gb v) (evalAff ga w, evalAff gb w) := by
          unfold orient2; rw [hga u, hga v, hga w, hgb u, hgb v, hgb w]; ring
      _ = 0 := hori
  exact (mul_eq_zero.mp hmul).resolve_left (neg_ne_zero.mpr (mul_ne_zero hsa hsb))

lemma triple_wedge_cap {k a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n)
    (W : Fin k → Finset (ℝ^3)) (X' : Finset (ℝ^3))
    (hWsubX' : ∀ i : Fin k, W i ⊆ X')
    (hX'no_cvx : ¬ Erdos651.HasConvexSubset n X')
    (hWgp : Erdos651.IsInGeneralPosition (Finset.univ.biUnion W))
    (w_rep : Fin k → ℝ^3) (hw_rep : ∀ i : Fin k, w_rep i ∈ W i)
    (hWcvx : ∀ j : Fin k, Disjoint (convexHull ℝ (W j : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ.erase j).biUnion W : Finset (ℝ^3)) : Set (ℝ^3))))
    (hW2sep : ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      Disjoint (convexHull ℝ ((W i ∪ W j : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((W i' ∪ W j' : Finset (ℝ^3)) : Set (ℝ^3))))
    (hcor_ab : ∀ (p q r : ℕ), p ≤ q → q ≤ r → r ≤ k →
      let I1 := (Finset.univ : Finset (Fin k)).filter fun i => i.1 < p ∨ (q ≤ i.1 ∧ i.1 < r)
      let I2 := (Finset.univ : Finset (Fin k)).filter fun i => (p ≤ i.1 ∧ i.1 < q) ∨ r ≤ i.1
      Disjoint (convexHull ℝ ((I1.image w_rep : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((I2.image w_rep : Finset (ℝ^3)) : Set (ℝ^3))))
    (j1 j2 j3 : Fin k) (hj12 : j1 < j2) (hj23 : j2 < j3)
    (hWsize : ((Nat.choose (a + n - 4) (a - 2)) ^ 3) * ((Nat.choose (a + n - 4) (a - 2)) ^ 3) < (W j2).card) :
    let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < j1 ∨ (j2 < j ∧ j ≤ j3)
    let S2 := (Finset.univ : Finset (Fin k)).filter fun j => (j1 ≤ j ∧ j < j2) ∨ j3 < j
    (∃ K ⊆ W j2, K.card = a ∧
      ∀ y ∈ K, y ∉ convexHull ℝ (((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) ∨
    (∃ K ⊆ W j2, K.card = a ∧
      ∀ y ∈ K, y ∉ convexHull ℝ (((S2.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) := by
  intro S1 S2
  let M_cap : ℕ := (Nat.choose (a + n - 4) (a - 2)) ^ 3
  obtain ⟨f0, f1, f2, ε, hε, hf0A, hf0B, hf1B, hf1A, hf2B, hf2A,
    hf0i, hf1i, hf2i, hnc01, hnc02, hnc12⟩ :=
    wedge_separation W hWgp w_rep hw_rep hWcvx hW2sep hcor_ab j1 j2 j3 hj12 hj23
  let g0 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f0.1, f0.2 + ε)
  let g1 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (-f1.1, -f1.2 + ε)
  let g2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (-f2.1, -f2.2 + ε)
  let h0 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f0.1, f0.2 + ε)
  let h1 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f2.1, f2.2 + ε)
  let h2 : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ := (f1.1, f1.2 + ε)
  have hg0eq (u : ℝ^3) : evalAff g0 u = 1 * evalAff f0 u + ε := by dsimp [g0, evalAff]; ring
  have hg1eq (u : ℝ^3) : evalAff g1 u = (-1) * evalAff f1 u + ε := by dsimp [g1, evalAff]; ring
  have hg2eq (u : ℝ^3) : evalAff g2 u = (-1) * evalAff f2 u + ε := by dsimp [g2, evalAff]; ring
  have hh0eq (u : ℝ^3) : evalAff h0 u = 1 * evalAff f0 u + ε := by dsimp [h0, evalAff]; ring
  have hh1eq (u : ℝ^3) : evalAff h1 u = 1 * evalAff f2 u + ε := by dsimp [h1, evalAff]; ring
  have hh2eq (u : ℝ^3) : evalAff h2 u = 1 * evalAff f1 u + ε := by dsimp [h2, evalAff]; ring
  let P1 : Set (ℝ^3) := {u | evalAff g0 u ≤ 0 ∧ evalAff g1 u ≤ 0 ∧ evalAff g2 u ≤ 0}
  let P2 : Set (ℝ^3) := {u | evalAff h0 u ≤ 0 ∧ evalAff h1 u ≤ 0 ∧ evalAff h2 u ≤ 0}
  have hconv_aff (g : ((ℝ^3) →ₗ[ℝ] ℝ) × ℝ) : Convex ℝ {u | evalAff g u ≤ 0} := by
    have heq : {u : ℝ^3 | evalAff g u ≤ 0} = {u : ℝ^3 | g.1 u ≤ -g.2} := by
      ext u; change g.1 u + g.2 ≤ 0 ↔ g.1 u ≤ -g.2; constructor <;> intro h <;> linarith
    rw [heq]; exact convex_halfSpace_le g.1.isLinear (-g.2)
  have hP1conv : Convex ℝ P1 := (hconv_aff g0).inter ((hconv_aff g1).inter (hconv_aff g2))
  let ltJ (u v : ℝ^3) : Prop :=
    evalAff f0 u < evalAff f0 v ∧
    ∃ p1 ∈ P1, ∃ l : ℝ, 0 < l ∧ l < 1 ∧ u = (1 - l) • p1 + l • v
  have hltJ_po : IsStrictPO ltJ := by
    refine ⟨fun u h => lt_irrefl _ h.1, fun u v w huv hvw => ?_⟩
    obtain ⟨h1, p1, hp1, l, hl0, hl1, hu_eq⟩ := huv
    obtain ⟨h2, q1, hq1, m, hm0, hm1, hv_eq⟩ := hvw
    have hlm0 : 0 < l * m := mul_pos hl0 hm0
    have hlm1 : l * m < 1 := by nlinarith only [hl0, hl1, hm0, hm1]
    have hden : 0 < 1 - l * m := sub_pos.mpr hlm1
    let r1 := ((1 - l) / (1 - l * m)) • p1 + ((l * (1 - m)) / (1 - l * m)) • q1
    have hr1P1 : r1 ∈ P1 := hP1conv hp1 hq1 (div_nonneg (by linarith) hden.le)
      (div_nonneg (by nlinarith only [hl0, hm1]) hden.le) (by field_simp [hden.ne']; ring)
    refine ⟨h1.trans h2, r1, hr1P1, l * m, hlm0, hlm1, ?_⟩
    rw [hu_eq, hv_eq]; dsimp [r1]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_div_cancel₀ _ hden.ne', mul_div_cancel₀ _ hden.ne']
    abel
  have hS1P1 : ((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P1 := by
    intro u hu
    have hu' : u ∈ S1.biUnion W := hu
    obtain ⟨j, hjS1, huj⟩ := Finset.mem_biUnion.mp hu'
    have hjne : j ≠ j2 := by
      intro heq; subst heq
      have := (Finset.mem_filter.mp hjS1).2
      exact absurd this (by rintro (h | ⟨h, _⟩); exact (hj12.trans h).false; exact lt_irrefl _ h)
    have hu_er : u ∈ (Finset.univ.erase j2).biUnion W :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩, huj⟩
    have hu_i1 : u ∈ (insert j2 S1).biUnion W :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_insert_of_mem hjS1, huj⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hg0eq]; linarith [hf0A u hu_er]
    · rw [hg1eq]; linarith [hf1B u hu']
    · rw [hg2eq]; linarith [hf2B u hu_i1]
  have hS2P2 : ((S2.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ⊆ P2 := by
    intro u hu
    have hu' : u ∈ S2.biUnion W := hu
    obtain ⟨j, hjS2, huj⟩ := Finset.mem_biUnion.mp hu'
    have hjne : j ≠ j2 := by
      intro heq; subst heq
      have := (Finset.mem_filter.mp hjS2).2
      rcases this with ⟨_, h⟩ | h
      · exact lt_irrefl _ h
      · exact (hj23.trans h).false
    have hu_er : u ∈ (Finset.univ.erase j2).biUnion W :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩, huj⟩
    have hu_i2 : u ∈ (insert j2 S2).biUnion W :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_insert_of_mem hjS2, huj⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hh0eq]; linarith [hf0A u hu_er]
    · rw [hh1eq]; linarith [hf2A u hu']
    · rw [hh2eq]; linarith [hf1A u hu_i2]
  rcases chain_or_antichain hltJ_po (W j2) M_cap M_cap hWsize with
    ⟨C, hCW, hCchain, hCcard⟩ | ⟨A, hAW, hAanti, hAcard⟩
  · -- C is a chain of size > M_cap ⇒ C is P2-free!
    have hP2free : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ∀ t : ℝ,
        ¬ (evalAff h0 ((1 - t) • u + t • v) ≤ 0 ∧ evalAff h1 ((1 - t) • u + t • v) ≤ 0 ∧
           evalAff h2 ((1 - t) • u + t • v) ≤ 0) := by
      intro u hu v hv hne t ht
      set p2 := (1 - t) • u + t • v
      have hp2_0 : evalAff f0 p2 ≤ -ε := by have := ht.1; rw [hh0eq] at this; linarith
      have hp2_1 : evalAff f1 p2 ≤ -ε := by have := ht.2.2; rw [hh2eq] at this; linarith
      have hp2_2 : evalAff f2 p2 ≤ -ε := by have := ht.2.1; rw [hh1eq] at this; linarith
      have hmem_j2 (w : ℝ^3) (hw : w ∈ W j2) :
          0 < evalAff f0 w ∧ evalAff f1 w ≤ -ε ∧ ε ≤ evalAff f2 w :=
        ⟨hf0B w hw,
         hf1A w (Finset.mem_biUnion.mpr ⟨j2, Finset.mem_insert_self _ _, hw⟩),
         hf2B w (Finset.mem_biUnion.mpr ⟨j2, Finset.mem_insert_self _ _, hw⟩)⟩
      obtain ⟨hu0, hu1, hu2⟩ := hmem_j2 u (hCW hu)
      obtain ⟨hv0, hv1, hv2⟩ := hmem_j2 v (hCW hv)
      rcases hCchain u hu v hv hne with ⟨_, p1, hp1, l, _, _, hu_eq⟩ | ⟨_, p1, hp1, l, _, _, hv_eq⟩
      · have hp1_0 : evalAff f0 p1 ≤ -ε := by have := hp1.1; rw [hg0eq] at this; linarith
        have hp1_1 : ε ≤ evalAff f1 p1 := by have := hp1.2.1; rw [hg1eq] at this; linarith
        have hp1_2 : ε ≤ evalAff f2 p1 := by have := hp1.2.2; rw [hg2eq] at this; linarith
        exact no_line_meets_wedge1_wedge2_X hε hv0 hv1 hv2 hp1_0 hp1_1 hp1_2 hp2_0 hp2_1 hp2_2 hu_eq rfl
      · have hp1_0 : evalAff f0 p1 ≤ -ε := by have := hp1.1; rw [hg0eq] at this; linarith
        have hp1_1 : ε ≤ evalAff f1 p1 := by have := hp1.2.1; rw [hg1eq] at this; linarith
        have hp1_2 : ε ≤ evalAff f2 p1 := by have := hp1.2.2; rw [hg2eq] at this; linarith
        have hp2_swap : p2 = (1 - (1 - t)) • v + (1 - t) • u := by dsimp [p2]; rw [sub_sub_cancel, add_comm]
        exact no_line_meets_wedge1_wedge2_X hε hu0 hu1 hu2 hp1_0 hp1_1 hp1_2 hp2_0 hp2_1 hp2_2 hv_eq hp2_swap
    rcases wedge_cups_vs_caps (g0 := h0) (g1 := h1) (g2 := h2) C
        (fun u hu => by rw [hh0eq]; linarith [hf0B u (hCW hu)])
        (fun u hu => by rw [hh1eq]; linarith [hf2B u (Finset.mem_biUnion.mpr ⟨j2, Finset.mem_insert_self _ _, hCW hu⟩)])
        (fun u hu v hv h => hf0i (hCW hu) (hCW hv) (by rw [hh0eq, hh0eq] at h; linarith))
        (fun u hu v hv h => hf2i (hCW hu) (hCW hv) (by rw [hh1eq, hh1eq] at h; linarith))
        (fun u hu v hv h => hf1i (hCW hu) (hCW hv) (by rw [hh2eq, hh2eq] at h; linarith))
        (noThreeCollinear2_scale_shift hCW one_ne_zero one_ne_zero hh0eq hh1eq hnc02)
        (noThreeCollinear2_scale_shift hCW one_ne_zero one_ne_zero hh0eq hh2eq hnc01)
        (noThreeCollinear2_scale_shift_swap hCW one_ne_zero one_ne_zero hh1eq hh2eq hnc12)
        hP2free ha hn hCcard with
      ⟨K, hKC, hKcard, hKcap⟩ | hcvxC
    · right
      refine ⟨K, hKC.trans hCW, hKcard, fun y hy hmem => hKcap y hy (convexHull_mono (Set.union_subset_union_left _ hS2P2) hmem)⟩
    · exfalso
      obtain ⟨U, hUC, hUcard, hUind⟩ := hcvxC
      exact hX'no_cvx ⟨U, hUC.trans (hCW.trans (hWsubX' j2)), hUcard, hUind⟩
  · -- A is an antichain of size > M_cap ⇒ A is P1-free!
    have hP1free : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → ∀ t : ℝ,
        ¬ (evalAff g0 ((1 - t) • u + t • v) ≤ 0 ∧ evalAff g1 ((1 - t) • u + t • v) ≤ 0 ∧
           evalAff g2 ((1 - t) • u + t • v) ≤ 0) := by
      intro u hu v hv hne t ht
      set p1 := (1 - t) • u + t • v
      have hp1P1 : p1 ∈ P1 := ht
      have hf0u : 0 < evalAff f0 u := hf0B u (hAW hu)
      have hf0v : 0 < evalAff f0 v := hf0B v (hAW hv)
      have hf0p : evalAff f0 p1 < 0 := by have := ht.1; rw [hg0eq] at this; linarith
      have hf0comb : evalAff f0 p1 = (1 - t) * evalAff f0 u + t * evalAff f0 v :=
        evalAff_convex_comb f0 (1 - t) t (by ring) u v
      by_cases ht0 : t < 0
      · have hden : 0 < 1 - t := by linarith
        let l := -t / (1 - t)
        have hl0 : 0 < l := div_pos (by linarith) hden
        have hl1 : l < 1 := (div_lt_one hden).mpr (by linarith)
        have hu_eq : u = (1 - l) • p1 + l • v := by
          dsimp [p1, l]; rw [smul_add, smul_smul, smul_smul]
          have hc1 : (1 - -t / (1 - t)) * (1 - t) = 1 := by field_simp [hden.ne']; ring
          have hc2 : (1 - -t / (1 - t)) * t + -t / (1 - t) = 0 := by field_simp [hden.ne']; ring
          calc u = (1 : ℝ) • u + (0 : ℝ) • v := by simp
            _ = ((1 - -t / (1 - t)) * (1 - t)) • u + ((1 - -t / (1 - t)) * t + -t / (1 - t)) • v := by rw [hc1, hc2]
            _ = ((1 - -t / (1 - t)) * (1 - t)) • u + ((1 - -t / (1 - t)) * t) • v + (-t / (1 - t)) • v := by rw [add_smul]; abel
        have hlt0 : evalAff f0 u < evalAff f0 v := by
          have := evalAff_convex_comb f0 (1 - l) l (by ring) p1 v
          rw [← hu_eq] at this; nlinarith only [this, hf0p, hf0v, hl0, hl1]
        exact hAanti u hu v hv ⟨hlt0, p1, hp1P1, l, hl0, hl1, hu_eq⟩
      · have ht1 : 1 < t := by
          by_contra hle; push Not at hle
          have ht0' : 0 ≤ t := not_lt.mp ht0
          have : 0 < (1 - t) * evalAff f0 u + t * evalAff f0 v := by
            by_cases hz : t = 0
            · rw [hz]; linarith
            · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hf0u.le)
                (mul_pos (lt_of_le_of_ne ht0' (Ne.symm hz)) hf0v)
          linarith
        have htpos : 0 < t := by linarith
        let l := (t - 1) / t
        have hl0 : 0 < l := div_pos (by linarith) htpos
        have hl1 : l < 1 := (div_lt_one htpos).mpr (by linarith)
        have hv_eq : v = (1 - l) • p1 + l • u := by
          dsimp [p1, l]; rw [smul_add, smul_smul, smul_smul]
          have hc1 : (1 - (t - 1) / t) * (1 - t) + (t - 1) / t = 0 := by field_simp [htpos.ne']; ring
          have hc2 : (1 - (t - 1) / t) * t = 1 := by field_simp [htpos.ne']; ring
          calc v = (0 : ℝ) • u + (1 : ℝ) • v := by simp
            _ = ((1 - (t - 1) / t) * (1 - t) + (t - 1) / t) • u + ((1 - (t - 1) / t) * t) • v := by rw [hc1, hc2]
            _ = ((1 - (t - 1) / t) * (1 - t)) • u + ((1 - (t - 1) / t) * t) • v + ((t - 1) / t) • u := by rw [add_smul]; abel
        have hlt0 : evalAff f0 v < evalAff f0 u := by
          have := evalAff_convex_comb f0 (1 - l) l (by ring) p1 u
          rw [← hv_eq] at this; nlinarith only [this, hf0p, hf0u, hl0, hl1]
        exact hAanti v hv u hu ⟨hlt0, p1, hp1P1, l, hl0, hl1, hv_eq⟩
    rcases wedge_cups_vs_caps (g0 := g0) (g1 := g1) (g2 := g2) A
        (fun u hu => by rw [hg0eq]; linarith [hf0B u (hAW hu)])
        (fun u hu => by rw [hg1eq]; linarith [hf1A u (Finset.mem_biUnion.mpr ⟨j2, Finset.mem_insert_self _ _, hAW hu⟩)])
        (fun u hu v hv h => hf0i (hAW hu) (hAW hv) (by rw [hg0eq, hg0eq] at h; linarith))
        (fun u hu v hv h => hf1i (hAW hu) (hAW hv) (by rw [hg1eq, hg1eq] at h; linarith))
        (fun u hu v hv h => hf2i (hAW hu) (hAW hv) (by rw [hg2eq, hg2eq] at h; linarith))
        (noThreeCollinear2_scale_shift hAW one_ne_zero (by norm_num) hg0eq hg1eq hnc01)
        (noThreeCollinear2_scale_shift hAW one_ne_zero (by norm_num) hg0eq hg2eq hnc02)
        (noThreeCollinear2_scale_shift hAW (by norm_num) (by norm_num) hg1eq hg2eq hnc12)
        hP1free ha hn hAcard with
      ⟨K, hKA, hKcard, hKcap⟩ | hcvxA
    · left
      refine ⟨K, hKA.trans hAW, hKcard, fun y hy hmem => hKcap y hy (convexHull_mono (Set.union_subset_union_left _ hS1P1) hmem)⟩
    · exfalso
      obtain ⟨U, hUA, hUcard, hUind⟩ := hcvxA
      exact hX'no_cvx ⟨U, hUA.trans (hAW.trans (hWsubX' j2)), hUcard, hUind⟩

lemma assemble_convex_from_wedges {k t a n : ℕ} (ht : 2 ≤ t) (ha : a = n / t + 2)
    (W : Fin k → Finset (ℝ^3)) (X' : Finset (ℝ^3))
    (hWsubX' : ∀ i : Fin k, W i ⊆ X')
    (hWdisj : ∀ i j : Fin k, i ≠ j → Disjoint (W i) (W j))
    (hk_ram : ∀ c : Finset ℕ → Bool, ∃ Q ⊆ Finset.range k, Q.card = 2 * t + 2 ∧
      ∃ b : Bool, ∀ A ⊆ Q, A.card = 3 → c A = b)
    (htriple_wedge : ∀ j1 j2 j3 : Fin k, j1 < j2 → j2 < j3 →
      let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < j1 ∨ (j2 < j ∧ j ≤ j3)
      let S2 := (Finset.univ : Finset (Fin k)).filter fun j => (j1 ≤ j ∧ j < j2) ∨ j3 < j
      (∃ K ⊆ W j2, K.card = a ∧
        ∀ y ∈ K, y ∉ convexHull ℝ (((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) ∨
      (∃ K ⊆ W j2, K.card = a ∧
        ∀ y ∈ K, y ∉ convexHull ℝ (((S2.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))))) :
    Erdos651.HasConvexSubset n X' := by
  let col3 : Finset ℕ → Bool := fun T =>
    if hT : T.card = 3 ∧ T ⊆ Finset.range k then
      let e : Fin 3 ≃o T := T.orderIsoOfFin hT.1
      let j1 : Fin k := ⟨(e 0).1, Finset.mem_range.mp (hT.2 (e 0).2)⟩
      let j2 : Fin k := ⟨(e 1).1, Finset.mem_range.mp (hT.2 (e 1).2)⟩
      let j3 : Fin k := ⟨(e 2).1, Finset.mem_range.mp (hT.2 (e 2).2)⟩
      let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < j1 ∨ (j2 < j ∧ j ≤ j3)
      decide (∃ K ⊆ W j2, K.card = a ∧
        ∀ y ∈ K, y ∉ convexHull ℝ (((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))))
    else false
  obtain ⟨Q, hQsub, hQcard, colb, hQmono⟩ := hk_ram col3
  let eQ : Fin (2 * t + 2) ≃o Q := Q.orderIsoOfFin hQcard
  let q : Fin (2 * t + 2) → Fin k := fun i => ⟨(eQ i).1, Finset.mem_range.mp (hQsub (eQ i).2)⟩
  have hq_mono : StrictMono q := fun i j hij => eQ.strictMono hij
  have hcol_triple (u1 u2 u3 : Fin (2 * t + 2)) (h12 : u1 < u2) (h23 : u2 < u3) :
      let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < q u1 ∨ (q u2 < j ∧ j ≤ q u3)
      let S2 := (Finset.univ : Finset (Fin k)).filter fun j => (q u1 ≤ j ∧ j < q u2) ∨ q u3 < j
      if colb then
        ∃ K ⊆ W (q u2), K.card = a ∧
          ∀ y ∈ K, y ∉ convexHull ℝ (((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))
      else
        ∃ K ⊆ W (q u2), K.card = a ∧
          ∀ y ∈ K, y ∉ convexHull ℝ (((S2.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))) := by
    intro S1 S2
    let T : Finset ℕ := {(q u1).1, (q u2).1, (q u3).1}
    have hlt12 : (q u1).1 < (q u2).1 := hq_mono h12
    have hlt23 : (q u2).1 < (q u3).1 := hq_mono h23
    have hTsubQ : T ⊆ Q := by
      intro z hz; simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> exact (eQ _).2
    have hTsubR : T ⊆ Finset.range k := hTsubQ.trans hQsub
    have hTcard : T.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp; omega
      · simp; omega
    have hcolT : col3 T = colb := hQmono T hTsubQ hTcard
    dsimp only [col3] at hcolT
    rw [dif_pos ⟨hTcard, hTsubR⟩] at hcolT
    let g : Fin 3 → T := ![⟨(q u1).1, by simp [T]⟩, ⟨(q u2).1, by simp [T]⟩, ⟨(q u3).1, by simp [T]⟩]
    have hg_mono : StrictMono g := by
      intro i j hij
      change (g i).1 < (g j).1
      fin_cases i <;> fin_cases j <;> dsimp [g]
      all_goals first
        | exact hlt12
        | exact hlt23
        | exact hlt12.trans hlt23
        | (exfalso; revert hij; decide)
    have hg_bij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg_mono.injective, by rw [Fintype.card_fin, Fintype.card_coe, hTcard]⟩
    let eg : Fin 3 ≃o T := OrderIso.ofRelIsoLT ⟨Equiv.ofBijective g hg_bij, hg_mono.lt_iff_lt⟩
    have heq_iso : T.orderIsoOfFin hTcard = eg := by
      have h1 : (eg.trans (T.orderIsoOfFin hTcard).symm : Fin 3 ≃o Fin 3) = OrderIso.refl (Fin 3) := Subsingleton.elim _ _
      ext r
      have h2 := congrArg (fun φ : Fin 3 ≃o Fin 3 => (T.orderIsoOfFin hTcard) (φ r)) h1
      change (T.orderIsoOfFin hTcard) ((T.orderIsoOfFin hTcard).symm (eg r)) = (T.orderIsoOfFin hTcard) r at h2
      rw [OrderIso.apply_symm_apply] at h2
      exact congrArg Subtype.val h2.symm
    have hfeq (r : Fin 3) : (⟨((T.orderIsoOfFin hTcard) r).1, Finset.mem_range.mp (hTsubR ((T.orderIsoOfFin hTcard) r).2)⟩ : Fin k) =
        ![q u1, q u2, q u3] r := by
      ext; rw [heq_iso]; fin_cases r <;> rfl
    rw [hfeq 0, hfeq 1, hfeq 2] at hcolT
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hcolT
    cases hcb : colb
    · rw [hcb] at hcolT
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnot := of_decide_eq_false hcolT
      exact (htriple_wedge (q u1) (q u2) (q u3) (hq_mono h12) (hq_mono h23)).resolve_left hnot
    · rw [hcb] at hcolT
      simp only [↓reduceIte]
      exact of_decide_eq_true hcolT
  let oddIdx (r : Fin t) : Fin k := q ⟨2 * r.1 + 1, by omega⟩
  have hcaps : ∀ r : Fin t, ∃ K ⊆ W (oddIdx r), K.card = a ∧
      ∀ y ∈ K, y ∉ convexHull ℝ
        ((((Finset.univ.erase r).biUnion fun s => W (oddIdx s) : Finset (ℝ^3)) : Set (ℝ^3)) ∪
          ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3))) := by
    intro r
    cases hcb : colb
    · have h := hcol_triple ⟨0, by omega⟩ ⟨2 * r.1 + 1, by omega⟩ ⟨2 * r.1 + 2, by omega⟩
        (by change 0 < 2 * r.1 + 1; omega) (by change 2 * r.1 + 1 < 2 * r.1 + 2; omega)
      rw [hcb] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨K, hKW, hKc, hKcap⟩ := h
      refine ⟨K, hKW, hKc, fun y hy hmem => hKcap y hy (convexHull_mono (Set.union_subset_union_left _ ?_) hmem)⟩
      apply Finset.coe_subset.mpr; apply Finset.biUnion_subset.mpr
      intro s hs
      have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
      apply Finset.subset_biUnion_of_mem W
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases lt_or_gt_of_ne hsr with hlt | hgt
      · left
        exact ⟨hq_mono.monotone (show (⟨0, by omega⟩ : Fin (2 * t + 2)) ≤ ⟨2 * s.1 + 1, by omega⟩ by change 0 ≤ 2 * s.1 + 1; omega),
               hq_mono (show (⟨2 * s.1 + 1, by omega⟩ : Fin (2 * t + 2)) < ⟨2 * r.1 + 1, by omega⟩ by change 2 * s.1 + 1 < 2 * r.1 + 1; have : s.1 < r.1 := hlt; omega)⟩
      · right
        exact hq_mono (show (⟨2 * r.1 + 2, by omega⟩ : Fin (2 * t + 2)) < ⟨2 * s.1 + 1, by omega⟩ by change 2 * r.1 + 2 < 2 * s.1 + 1; have : r.1 < s.1 := hgt; omega)
    · have h := hcol_triple ⟨2 * r.1, by omega⟩ ⟨2 * r.1 + 1, by omega⟩ ⟨2 * t + 1, by omega⟩
        (by change 2 * r.1 < 2 * r.1 + 1; omega) (by change 2 * r.1 + 1 < 2 * t + 1; omega)
      rw [hcb] at h; simp only [↓reduceIte] at h
      obtain ⟨K, hKW, hKc, hKcap⟩ := h
      refine ⟨K, hKW, hKc, fun y hy hmem => hKcap y hy (convexHull_mono (Set.union_subset_union_left _ ?_) hmem)⟩
      apply Finset.coe_subset.mpr; apply Finset.biUnion_subset.mpr
      intro s hs
      have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
      apply Finset.subset_biUnion_of_mem W
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases lt_or_gt_of_ne hsr with hlt | hgt
      · left
        exact hq_mono (show (⟨2 * s.1 + 1, by omega⟩ : Fin (2 * t + 2)) < ⟨2 * r.1, by omega⟩ by change 2 * s.1 + 1 < 2 * r.1; have : s.1 < r.1 := hlt; omega)
      · right
        exact ⟨hq_mono (show (⟨2 * r.1 + 1, by omega⟩ : Fin (2 * t + 2)) < ⟨2 * s.1 + 1, by omega⟩ by change 2 * r.1 + 1 < 2 * s.1 + 1; have : r.1 < s.1 := hgt; omega),
               hq_mono.monotone (show (⟨2 * s.1 + 1, by omega⟩ : Fin (2 * t + 2)) ≤ ⟨2 * t + 1, by omega⟩ by change 2 * s.1 + 1 ≤ 2 * t + 1; omega)⟩
  choose K hKW hKcard hKcap using hcaps
  let Ktot : Finset (ℝ^3) := Finset.univ.biUnion K
  have hKdisj : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint K := by
    intro r _ s _ hrs
    have hodd_ne : oddIdx r ≠ oddIdx s := fun heq => by
      have := hq_mono.injective heq
      have h1 : 2 * r.1 + 1 = 2 * s.1 + 1 := congrArg Fin.val this
      exact hrs (Fin.ext (by omega))
    exact (hWdisj (oddIdx r) (oddIdx s) hodd_ne).mono (hKW r) (hKW s)
  have hKtot_card : n ≤ Ktot.card := by
    rw [Finset.card_biUnion (fun r hr s hs hrs => hKdisj hr hs hrs)]
    have hsum : ∑ r : Fin t, (K r).card = t * a := by simp [hKcard]
    rw [hsum, ha]
    have hdm : t * (n / t) + n % t = n := Nat.div_add_mod n t
    have hml : n % t < t := Nat.mod_lt n (by omega)
    nlinarith only [hdm, hml]
  have hKtot_sub : Ktot ⊆ X' := Finset.biUnion_subset.mpr fun r _ => (hKW r).trans (hWsubX' (oddIdx r))
  have hKtot_cvx : ConvexIndependent ℝ (Subtype.val : ↥(Ktot : Set (ℝ^3)) → ℝ^3) := by
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro y hy hmem
    obtain ⟨r, _, hyKr⟩ := Finset.mem_biUnion.mp hy
    apply hKcap r y hyKr
    apply convexHull_mono _ hmem
    rintro u ⟨huK, hune⟩
    obtain ⟨s, _, huKs⟩ := Finset.mem_biUnion.mp huK
    by_cases hsr : s = r
    · subst hsr; exact Or.inr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hune, huKs⟩))
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨s, Finset.mem_erase.mpr ⟨hsr, Finset.mem_univ s⟩, hKW s huKs⟩))
  obtain ⟨U, hUK, hUcard⟩ := Finset.exists_subset_card_eq hKtot_card
  refine ⟨U, hUK.trans hKtot_sub, hUcard, ?_⟩
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff] at hKtot_cvx ⊢
  intro y hyU hmem
  exact hKtot_cvx y (hUK hyU) (convexHull_mono (Set.sdiff_subset_sdiff_left (Finset.coe_subset.mpr hUK)) hmem)

theorem pohoata_zakharov_3d : OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1.H1 := by
  refine ⟨32, by norm_num, fun t ht => ?_⟩
  -- Constants depending only on t
  obtain ⟨k_ram, hk_ram⟩ := finite_ramsey_sets (α := ℕ) 3 (2 * t + 2)
  let k := max k_ram 4
  obtain ⟨k₀, hk₀4, hab_ram⟩ := above_below_ramsey k (le_max_right _ _)
  obtain ⟨M2, hM2pos, hpf2d⟩ := positive_fraction_convex_2d k₀ (by omega)
  obtain ⟨M3, hM3pos, h2sep3d⟩ := two_separable_3d k₀
  let Cconst : ℕ := 60 * M2 * M3 + 10
  let N₀ : ℕ := max (2 * t) (max 4 (t * Cconst))
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn X hX hno_cvx => ?_⟩
  by_contra! hbig
  -- Step 1: Generic coordinate change in ℝ^3
  obtain ⟨Φ, hX'card, hX'gp, hX'lift, hproj_inj, hx0_inj, hYnc⟩ := generic_coord_change X hX
  let X' := X.image Φ
  have hX'no_cvx : ¬ Erdos651.HasConvexSubset n X' := fun h => hno_cvx (hX'lift n h)
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  -- Lower bound on (t : ℝ) ^ (n / t)
  have hC_le_rpow : (Cconst : ℝ) ≤ (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) := by
    have hnt : (Cconst : ℝ) ≤ (n : ℝ) / (t : ℝ) := by
      rw [le_div_iff₀ htpos]
      have h1 : Cconst * t ≤ n := by
        have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn); nlinarith
      exact_mod_cast h1
    have hpow1 : (Cconst : ℝ) ≤ (2 : ℝ) ^ Cconst := by
      have : Cconst < 2 ^ Cconst := Nat.lt_two_pow_self
      exact_mod_cast this.le
    have hpow2 : (2 : ℝ) ^ Cconst ≤ (t : ℝ) ^ (Cconst : ℝ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow (by norm_num) ht2 (Nat.cast_nonneg _)
    have hpow3 : (t : ℝ) ^ (Cconst : ℝ) ≤ (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hnt
    exact hpow1.trans (hpow2.trans hpow3)
  have hX'big : (t : ℝ) ^ (32 * (n : ℝ) / (t : ℝ)) < (X'.card : ℝ) := by
    rw [hX'card]; exact hbig
  have hMtot_le : 60 * M2 * M3 ≤ X'.card := by
    have h1 : (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) ≤ (t : ℝ) ^ (32 * (n : ℝ) / (t : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by
        have h0 : 0 ≤ (n : ℝ) / (t : ℝ) := div_nonneg (Nat.cast_nonneg _) htpos.le
        rw [mul_div_assoc]; linarith)
    have h2 : (60 * M2 * M3 : ℝ) < (X'.card : ℝ) := by
      have : (60 * M2 * M3 : ℝ) ≤ (Cconst : ℝ) := by dsimp [Cconst]; push_cast; linarith
      linarith
    exact_mod_cast h2.le
  -- Step 2: Positive fraction 2D convex clusters
  let Y := X'.image proj2
  have hYcard : Y.card = X'.card := Finset.card_image_of_injOn hproj_inj
  have hYxinj : ∀ p ∈ Y, ∀ q ∈ Y, p.1 = q.1 → p = q := by
    intro p hp q hq heq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    rw [hx0_inj hu hv heq]
  have hM2leY : M2 ≤ Y.card := by rw [hYcard]; have : 1 ≤ M3 := hM3pos; nlinarith
  obtain ⟨C2d, s, hspm, hC2sub, hC2card, hC2ne, hC2disj, hC2ori⟩ := hpf2d Y hYxinj hYnc hM2leY
  -- Pull C2d back to X1 : Fin k₀ → Finset (ℝ^3)
  have hpull_each : ∀ i : Fin k₀, ∃ S ⊆ X', S.image proj2 = C2d i ∧ S.card = (C2d i).card :=
    fun i => finite_image_pullback proj2 X' (C2d i) (hC2sub i) hproj_inj
  choose X1 hX1sub hX1img hX1card using hpull_each
  have hX1gp : Erdos651.IsInGeneralPosition (Finset.univ.biUnion X1) := fun Z hZ hZc =>
    hX'gp Z (hZ.trans (Finset.biUnion_subset.mpr fun i _ => hX1sub i)) hZc
  have hX1_60 : ∀ i : Fin k₀, 60 * M3 ≤ (X1 i).card := fun i => by
    rw [hX1card i]
    have h1 := hC2card i; rw [hYcard] at h1
    have h2 : 60 * M3 ≤ X'.card / M2 := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < M2)]; nlinarith
    omega
  -- Step 3: 2-separable refinement X2 ⊆ X1
  obtain ⟨X2, hX2sub, hX2card, hX2sep⟩ := h2sep3d X1 hX1gp hX1_60
  have hX2_size : ∀ i : Fin k₀, X'.card / (M2 * M3) ≤ (X2 i).card := fun i => by
    have h1 := hX2card i
    have h2 : X'.card / (M2 * M3) ≤ (X1 i).card / M3 := by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right (by rw [hX1card i, ← hYcard]; exact hC2card i)
    exact h2.trans h1
  have hX2ne : ∀ i : Fin k₀, (X2 i).Nonempty := fun i => by
    rw [← Finset.card_pos]
    have h1 := hX2_size i
    have h2 : 1 ≤ X'.card / (M2 * M3) := by
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))]; nlinarith
    omega
  choose x_rep hx_rep using hX2ne
  -- Step 4: Above/below 4-uniform Ramsey on x_rep
  have hx_rep_inj : Function.Injective x_rep := by
    intro i j hij; by_contra hne
    have hi : proj2 (x_rep i) ∈ C2d i := by rw [← hX1img i]; exact Finset.mem_image_of_mem proj2 (hX2sub i (hx_rep i))
    have hj : proj2 (x_rep i) ∈ C2d j := by rw [hij, ← hX1img j]; exact Finset.mem_image_of_mem proj2 (hX2sub j (hx_rep j))
    exact Finset.disjoint_left.mp (hC2disj i j hne) hi hj
  have hx_rep_gp : Erdos651.IsInGeneralPosition (Finset.univ.image x_rep) := by
    intro Z hZ hZc
    have hsub : Finset.univ.image x_rep ⊆ X' := by
      intro u hu; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu; exact hX1sub i (hX2sub i (hx_rep i))
    exact hX'gp Z (hZ.trans hsub) hZc
  have hx_rep_ori : ∀ i j l : Fin k₀, i < j → j < l →
      0 < s * orient2 (proj2 (x_rep i)) (proj2 (x_rep j)) (proj2 (x_rep l)) := fun i j l hij hjl =>
    hC2ori i j l hij hjl
      (proj2 (x_rep i)) (by rw [← hX1img i]; exact Finset.mem_image_of_mem proj2 (hX2sub i (hx_rep i)))
      (proj2 (x_rep j)) (by rw [← hX1img j]; exact Finset.mem_image_of_mem proj2 (hX2sub j (hx_rep j)))
      (proj2 (x_rep l)) (by rw [← hX1img l]; exact Finset.mem_image_of_mem proj2 (hX2sub l (hx_rep l)))
  obtain ⟨idx, hidx_mono, hcor_ab⟩ := hab_ram x_rep s hspm hx_rep_inj hx_rep_gp hx_rep_ori
  let W : Fin k → Finset (ℝ^3) := fun i => X2 (idx i)
  let w_rep : Fin k → ℝ^3 := x_rep ∘ idx
  have hWsubX' : ∀ i : Fin k, W i ⊆ X' := fun i => (hX2sub (idx i)).trans (hX1sub (idx i))
  have hWgp : Erdos651.IsInGeneralPosition (Finset.univ.biUnion W) := fun Z hZ hZc =>
    hX'gp Z (hZ.trans (Finset.biUnion_subset.mpr fun i _ => hWsubX' i)) hZc
  have hW2sep : ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      Disjoint (convexHull ℝ ((W i ∪ W j : Finset (ℝ^3)) : Set (ℝ^3)))
        (convexHull ℝ ((W i' ∪ W j' : Finset (ℝ^3)) : Set (ℝ^3))) := fun i j i' j' h1 h2 h3 h4 =>
    hX2sep (idx i) (idx j) (idx i') (idx j')
      (fun h => h1 (hidx_mono.injective h)) (fun h => h2 (hidx_mono.injective h))
      (fun h => h3 (hidx_mono.injective h)) (fun h => h4 (hidx_mono.injective h))
  have hWcvx : ∀ j : Fin k, Disjoint (convexHull ℝ (W j : Set (ℝ^3)))
      (convexHull ℝ (((Finset.univ.erase j).biUnion W : Finset (ℝ^3)) : Set (ℝ^3))) := by
    have h2d := orient2_convex_position (by omega) C2d hC2ne s hC2ori
    intro j; rw [Set.disjoint_left]; intro p hp1 hp2
    have h1 : proj2 p ∈ convexHull ℝ (C2d (idx j) : Set (ℝ × ℝ)) := by
      have h1' : proj2 p ∈ proj2 '' convexHull ℝ (W j : Set (ℝ^3)) := ⟨p, hp1, rfl⟩
      rw [LinearMap.image_convexHull] at h1'
      refine convexHull_mono (fun q hq => ?_) h1'
      obtain ⟨u, hu, rfl⟩ := hq
      rw [Finset.mem_coe, ← hX1img (idx j)]
      exact Finset.mem_image_of_mem proj2 (hX2sub (idx j) hu)
    have h2 : proj2 p ∈ convexHull ℝ (((Finset.univ.erase (idx j)).biUnion C2d : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      have h2' : proj2 p ∈ proj2 '' convexHull ℝ (((Finset.univ.erase j).biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) := ⟨p, hp2, rfl⟩
      rw [LinearMap.image_convexHull] at h2'
      refine convexHull_mono (fun q hq => ?_) h2'
      obtain ⟨u, hu, rfl⟩ := hq
      obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
      have hij : idx i ≠ idx j := fun h => (Finset.mem_erase.mp hi).1 (hidx_mono.injective h)
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨idx i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩, ?_⟩)
      rw [← hX1img (idx i)]; exact Finset.mem_image_of_mem proj2 (hX2sub (idx i) hui)
    exact Set.disjoint_left.mp (h2d (idx j)) h1 h2
  -- Step 5: Compute cap size a = n / t + 2 and threshold M_cap = choose (a + n - 4) (a - 2) ^ 3
  let a : ℕ := n / t + 2
  let M_cap : ℕ := (Nat.choose (a + n - 4) (a - 2)) ^ 3
  have hMcap_sq_lt : ∀ i : Fin k, M_cap * M_cap < (W i).card := by
    intro i
    have ha_le : ((a - 2 : ℕ) : ℝ) ≤ (n : ℝ) / (t : ℝ) := by
      have h1 : (a - 2) * t ≤ n := by dsimp [a]; exact Nat.div_mul_le_self n t
      rw [le_div_iff₀ htpos]
      exact_mod_cast h1
    have hN_le : ((a + n - 4 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      have h1 : n / t ≤ n := Nat.div_le_self n t
      have h2 : a + n - 4 ≤ 2 * n := by dsimp [a]; omega
      exact_mod_cast h2
    have hch : (Nat.choose (a + n - 4) (a - 2) : ℝ) ≤ (t : ℝ) ^ (5 * (n : ℝ) / (t : ℝ)) := by
      have h1 := choose_le_rpow (N := a + n - 4) (k := a - 2) ht
      have hexp : 2 * ((a + n - 4 : ℕ) : ℝ) / (t : ℝ) + ((a - 2 : ℕ) : ℝ) ≤ 5 * (n : ℝ) / (t : ℝ) := by
        have h3 : 2 * ((a + n - 4 : ℕ) : ℝ) / (t : ℝ) ≤ 4 * (n : ℝ) / (t : ℝ) := by
          rw [div_le_div_iff_of_pos_right htpos]; linarith
        have h4 : 4 * (n : ℝ) / (t : ℝ) + (n : ℝ) / (t : ℝ) = 5 * (n : ℝ) / (t : ℝ) := by ring
        linarith
      exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp)
    have hMsq : ((M_cap * M_cap : ℕ) : ℝ) ≤ (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) := by
      have hcast : ((M_cap * M_cap : ℕ) : ℝ) = ((Nat.choose (a + n - 4) (a - 2) : ℝ)) ^ (6 : ℕ) := by
        dsimp [M_cap]; push_cast; ring
      rw [hcast]
      calc ((Nat.choose (a + n - 4) (a - 2) : ℝ)) ^ (6 : ℕ)
        _ ≤ ((t : ℝ) ^ (5 * (n : ℝ) / (t : ℝ))) ^ (6 : ℕ) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hch 6
        _ = (t : ℝ) ^ ((5 * (n : ℝ) / (t : ℝ)) * (6 : ℕ)) := (Real.rpow_natCast _ 6).symm ▸ (Real.rpow_mul htpos.le _ _).symm
        _ = (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) := by congr 1; push_cast; ring
    have hdiv_gt : (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) < ((W i).card : ℝ) := by
      have h1 : (X'.card / (M2 * M3) : ℕ) ≤ (W i).card := hX2_size (idx i)
      have h2 : (X'.card : ℝ) / ((M2 * M3 : ℕ) : ℝ) - 1 < ((X'.card / (M2 * M3) : ℕ) : ℝ) := by
        have hpos : (0 : ℝ) < ((M2 * M3 : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos (by omega) (by omega) : 0 < M2 * M3)
        have hlt : X'.card < (X'.card / (M2 * M3) + 1) * (M2 * M3) := by
          have := Nat.div_add_mod X'.card (M2 * M3)
          have := Nat.mod_lt X'.card (Nat.mul_pos (by omega) (by omega) : 0 < M2 * M3)
          nlinarith
        have hlt' : (X'.card : ℝ) < (((X'.card / (M2 * M3) : ℕ) : ℝ) + 1) * ((M2 * M3 : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hpos]; linarith
      have hM_le : ((M2 * M3 : ℕ) : ℝ) * 2 ≤ (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) := by
        have : ((M2 * M3 : ℕ) : ℝ) * 2 ≤ (Cconst : ℝ) := by dsimp [Cconst]; push_cast; nlinarith
        exact this.trans hC_le_rpow
      have hpow_ge : (2 : ℝ) ≤ (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) := by
        have : (2 : ℝ) ≤ (Cconst : ℝ) := by dsimp [Cconst]; push_cast; nlinarith
        exact this.trans hC_le_rpow
      have hprod : (t : ℝ) ^ (32 * (n : ℝ) / (t : ℝ)) =
          (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) * (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) := by
        rw [← Real.rpow_add htpos, ← Real.rpow_add htpos]; congr 1; ring
      have hposM : (0 : ℝ) < ((M2 * M3 : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos (by omega) (by omega) : 0 < M2 * M3)
      have h3 : (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) + 1 < (X'.card : ℝ) / ((M2 * M3 : ℕ) : ℝ) := by
        rw [lt_div_iff₀ hposM]
        have h30pos : 1 ≤ (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) :=
          Real.one_le_rpow (by linarith) (by positivity)
        have hmul1 : ((t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) + 1) * ((M2 * M3 : ℕ) : ℝ) ≤
            (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (((M2 * M3 : ℕ) : ℝ) * 2) := by nlinarith
        have hmul2 : (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (((M2 * M3 : ℕ) : ℝ) * 2) ≤
            (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) :=
          mul_le_mul_of_nonneg_left hM_le (by positivity)
        have hmul3 : (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) ≤
            (t : ℝ) ^ (32 * (n : ℝ) / (t : ℝ)) := by
          rw [hprod]
          have : 0 ≤ (t : ℝ) ^ (30 * (n : ℝ) / (t : ℝ)) * (t : ℝ) ^ ((n : ℝ) / (t : ℝ)) := by positivity
          nlinarith [hpow_ge]
        linarith
      have h1' : ((X'.card / (M2 * M3) : ℕ) : ℝ) ≤ ((W i).card : ℝ) := by exact_mod_cast h1
      linarith
    exact_mod_cast hMsq.trans_lt hdiv_gt
  -- Step 6: For every ordered triple j1 < j2 < j3, construct wedges and apply Dilworth!
  have htriple_wedge : ∀ j1 j2 j3 : Fin k, j1 < j2 → j2 < j3 →
      let S1 := (Finset.univ : Finset (Fin k)).filter fun j => j < j1 ∨ (j2 < j ∧ j ≤ j3)
      let S2 := (Finset.univ : Finset (Fin k)).filter fun j => (j1 ≤ j ∧ j < j2) ∨ j3 < j
      (∃ K ⊆ W j2, K.card = a ∧
        ∀ y ∈ K, y ∉ convexHull ℝ (((S1.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) ∨
      (∃ K ⊆ W j2, K.card = a ∧
        ∀ y ∈ K, y ∉ convexHull ℝ (((S2.biUnion W : Finset (ℝ^3)) : Set (ℝ^3)) ∪ ((K.erase y : Finset (ℝ^3)) : Set (ℝ^3)))) :=
    fun j1 j2 j3 hj12 hj23 =>
      triple_wedge_cap (Nat.le_add_left 2 (n / t))
        (by have : 4 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn); omega)
        W X' hWsubX' hX'no_cvx hWgp w_rep (fun i => hx_rep (idx i)) hWcvx hW2sep hcor_ab
        j1 j2 j3 hj12 hj23 (hMcap_sq_lt j2)
  -- Step 7-8: 3-uniform Ramsey and assemble t caps into a convex set of size n!
  have hWdisj : ∀ i j : Fin k, i ≠ j → Disjoint (W i) (W j) := fun i j hij => by
    rw [Finset.disjoint_left]; intro u hu1 hu2
    have h1 : proj2 u ∈ C2d (idx i) := by rw [← hX1img _]; exact Finset.mem_image_of_mem proj2 (hX2sub _ hu1)
    have h2 : proj2 u ∈ C2d (idx j) := by rw [← hX1img _]; exact Finset.mem_image_of_mem proj2 (hX2sub _ hu2)
    exact Finset.disjoint_left.mp (hC2disj _ _ (fun h => hij (hidx_mono.injective h))) h1 h2
  exact hX'no_cvx (assemble_convex_from_wedges ht rfl W X' hWsubX' hWdisj
    (fun c => hk_ram (Finset.range k) (by rw [Finset.card_range]; exact le_max_left _ _) c)
    htriple_wedge)

end PZ651

theorem OMA.solution : OMA.R_Erdos651_erdos_651_variants_pohoata_zakharov_R1.H1 :=
  PZ651.pohoata_zakharov_3d
