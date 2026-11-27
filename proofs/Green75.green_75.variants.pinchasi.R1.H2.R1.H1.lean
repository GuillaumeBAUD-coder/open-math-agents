import OMAReductions.R_Green75_green_75_variants_pinchasi_R1_H2_R1

namespace G75sweep
open Finset
open scoped Classical

abbrev Rel (n d : ℕ) (u v : List (Fin n)) : Prop :=
  ∃ pre block post : List (Fin n), 2 ≤ block.length ∧ block.Pairwise (· < ·) ∧
    d ≤ ((pre.length : ℤ) - (post.length : ℤ)).natAbs ∧
    u = pre ++ block ++ post ∧ v = pre ++ block.reverse ++ post

abbrev P {n : ℕ} (w : Fin n → Fin n → ℕ) (s : ℕ) (D : Finset (Fin n)) (a b : Fin n) : Prop :=
  (a < b ∧ (s < w a b ∨ (w a b = s ∧ a ∉ D))) ∨ (b < a ∧ (w b a < s ∨ (w b a = s ∧ b ∈ D)))

abbrev B (x y z : ℕ) : Prop := (x < y ∧ y < z) ∨ (z < y ∧ y < x) ∨ (x = y ∧ y = z)

theorem tw_all {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α), x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases hp : p a = true
    · rw [List.takeWhile_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hp
      · exact tw_all p l x h
    · rw [List.takeWhile_cons_of_neg hp] at h
      simp at h

theorem split {α : Type} (c : α → Prop) [DecidablePred c] :
    ∀ L : List α, (∀ i k z, [i, k, z].Sublist L → c i → c z → c k) →
    ∃ pre block post, L = pre ++ block ++ post ∧ (∀ x ∈ pre, ¬ c x) ∧ (∀ x ∈ block, c x) ∧
      (∀ x ∈ post, ¬ c x)
  | [], _ => ⟨[], [], [], rfl, by simp, by simp, by simp⟩
  | a :: L, h => by
    by_cases ha : c a
    · refine ⟨[], a :: L.takeWhile (fun x => decide (c x)), L.dropWhile (fun x => decide (c x)),
        by simp [List.takeWhile_append_dropWhile], by simp, fun x hx => ?_, fun x hx hcx => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact of_decide_eq_true (tw_all _ L x hx)
      · cases hM : L.dropWhile (fun x => decide (c x)) with
        | nil => rw [hM] at hx; simp at hx
        | cons k M =>
          have hk := List.head_dropWhile_not (fun x => decide (c x)) (l := L) (by simp [hM])
          simp only [hM, List.head_cons, decide_eq_false_iff_not] at hk
          rw [hM] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hk hcx
          · have s1 : [k, x].Sublist (k :: M) := (List.singleton_sublist.mpr hx).cons_cons k
            have s2 : [k, x].Sublist L := (hM ▸ s1).trans (List.dropWhile_sublist _)
            exact hk (h a k x (s2.cons_cons a) ha hcx)
    · obtain ⟨pre, block, post, e, h1, h2, h3⟩ :=
        split c L (fun i k z hs => h i k z (hs.cons a))
      refine ⟨a :: pre, block, post, by simp [e], fun x hx => ?_, h2, h3⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact h1 x hx

theorem pw_rev {α : Type} {Q Q' : α → α → Prop} {pre block post : List α} (c : α → Prop)
    (h : (pre ++ block ++ post).Pairwise Q)
    (hb : ∀ x ∈ block, c x) (hpre : ∀ x ∈ pre, ¬ c x) (hpost : ∀ x ∈ post, ¬ c x)
    (h1 : ∀ a b, Q a b → ¬ (c a ∧ c b) → Q' a b) (h2 : ∀ a b, c a → c b → Q a b → Q' b a) :
    (pre ++ block.reverse ++ post).Pairwise Q' := by
  simp only [List.pairwise_append, List.pairwise_reverse, List.mem_append, List.mem_reverse] at h ⊢
  obtain ⟨⟨hp, hbl, hpb⟩, hpo, hall⟩ := h
  refine ⟨⟨hp.imp_of_mem fun ha hb' hq => h1 _ _ hq fun hc => hpre _ ha hc.1,
    hbl.imp_of_mem fun ha hb' hq => h2 _ _ (hb _ ha) (hb _ hb') hq,
    fun a ha b hb' => h1 _ _ (hpb a ha b hb') fun hc => hpre _ ha hc.1⟩,
    hpo.imp_of_mem fun ha hb' hq => h1 _ _ hq fun hc => hpost _ ha hc.1,
    fun a ha b hb' => h1 _ _ (hall a ha b hb') fun hc => hpost _ hb' hc.2⟩

theorem tri {n : ℕ} {w : Fin n → Fin n → ℕ}
    (htri : ∀ i j k, i < j → j < k → B (w i j) (w i k) (w j k))
    (hsym : ∀ i j, w i j = w j i)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (a < b ∧ b < c ∧ B (w a b) (w a c) (w b c)) ∨ (a < c ∧ c < b ∧ B (w a c) (w a b) (w b c)) ∨
    (b < a ∧ a < c ∧ B (w a b) (w b c) (w a c)) ∨ (b < c ∧ c < a ∧ B (w b c) (w a b) (w a c)) ∨
    (c < a ∧ a < b ∧ B (w a c) (w b c) (w a b)) ∨ (c < b ∧ b < a ∧ B (w b c) (w a c) (w a b)) := by
  have e1 := hsym a b
  have e2 := hsym b c
  have e3 := hsym a c
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  · exact Or.inl ⟨h1, h2, htri a b c h1 h2⟩
  · exact absurd (h1.trans h2) (not_lt_of_gt h3)
  · exact Or.inr (Or.inl ⟨h3, h2, by rw [e2]; exact htri a c b h3 h2⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h1, by rw [e3, e2]; exact htri c a b h3 h1⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h3, by rw [e1]; exact htri b a c h1 h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3, by rw [e1, e3]; exact htri b c a h2 h3⟩)))
  · exact absurd (h2.trans h1) (not_lt_of_gt h3)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h1, by rw [e2, e3, e1]; exact htri c b a h2 h1⟩))))

theorem step {n d : ℕ} {w : Fin n → Fin n → ℕ}
    (hsym : ∀ i j, w i j = w j i)
    (htri : ∀ i j k, i < j → j < k → B (w i j) (w i k) (w j k))
    (hside : ∀ i j, i < j → ∀ T1 T2 : Finset (Fin n),
      (∀ k, k ∈ T1 ↔ (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)) →
      (∀ k, k ∈ T2 ↔ (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)) →
      d ≤ ((T1.card : ℤ) - (T2.card : ℤ)).natAbs)
    (s : ℕ) (D : Finset (Fin n)) (L : List (Fin n))
    (hperm : L.Perm (List.finRange n)) (hpw : L.Pairwise (P w s D))
    (hD : ∀ a b, a ∈ D → a ≠ b → w a b = s → b ∈ D)
    (x y : Fin n) (hxy : x < y) (hw : w x y = s) (hxD : x ∉ D) :
    ∃ (D' : Finset (Fin n)) (L' : List (Fin n)), Rel n d L L' ∧ L'.Perm (List.finRange n) ∧
      L'.Pairwise (P w s D') ∧ (∀ a b, a ∈ D' → a ≠ b → w a b = s → b ∈ D') ∧
      D ⊆ D' ∧ x ∈ D' := by
  obtain ⟨c, hc⟩ : ∃ c : Finset (Fin n), ∀ z, z ∈ c ↔ z = x ∨ w x z = s :=
    ⟨univ.filter fun z => z = x ∨ w x z = s, fun z => by simp⟩
  have F1 : ∀ a b, a ∈ c → b ∈ c → a ≠ b → w a b = s := by
    intro a b ha hb hab
    rcases (hc a).mp ha with rfl | ha'
    · exact ((hc b).mp hb).resolve_left (Ne.symm hab)
    rcases (hc b).mp hb with rfl | hb'
    · rw [hsym]; exact ha'
    by_cases hxa : x = a
    · rw [← hxa]; exact hb'
    by_cases hxb : x = b
    · rw [← hxb, hsym]; exact ha'
    have := tri htri hsym x a b hxa hab hxb
    omega
  have F2 : ∀ a b, a ∈ c → a ≠ b → w a b = s → b ∈ c := by
    intro a b ha hab hwab
    rw [hc]
    rcases (hc a).mp ha with rfl | ha'
    · exact Or.inr hwab
    by_cases hxb : b = x
    · exact Or.inl hxb
    by_cases hxa : x = a
    · rw [hxa]; exact Or.inr hwab
    have := tri htri hsym x a b hxa hab (Ne.symm hxb)
    omega
  have F3 : ∀ a, a ∈ c → a ∉ D := by
    intro a ha haD
    rcases (hc a).mp ha with rfl | ha'
    · exact hxD haD
    by_cases hxa : a = x
    · exact hxD (hxa ▸ haD)
    exact hxD (hD a x haD hxa (by rw [hsym]; exact ha'))
  have F4 : ∀ i k z, [i, k, z].Sublist L → i ∈ c → z ∈ c → k ∈ c := by
    intro i k z hs hi hz
    by_contra hk
    have hp := hpw.sublist hs
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true] at hp
    obtain ⟨⟨hik, hiz⟩, hkz⟩ := hp
    have hiz' : i ≠ z := by rintro rfl; simp [P] at hiz
    have hik' : i ≠ k := by rintro rfl; exact hk hi
    have hkz' : k ≠ z := by rintro rfl; exact hk hz
    have w1 := F1 i z hi hz hiz'
    have w2 : w i k ≠ s := fun h => hk (F2 i k hi hik' h)
    have w3 : w k z ≠ s := fun h => hk (F2 z k hz (Ne.symm hkz') (by rw [hsym]; exact h))
    have d1 := F3 i hi
    have d2 := F3 z hz
    have e1 := hsym i k
    have e2 := hsym k z
    have e3 := hsym i z
    have := tri htri hsym i k z hik' hkz' hiz'
    simp only [P, B, Fin.lt_def] at *
    omega
  obtain ⟨pre, block, post, rfl, hpre, hblock, hpost⟩ := split (· ∈ c) L F4
  have hmem : ∀ k : Fin n, k ∈ pre ++ block ++ post := fun k =>
    hperm.mem_iff.mpr (List.mem_finRange k)
  have hnd : (pre ++ block ++ post).Nodup := hperm.nodup_iff.mpr (List.nodup_finRange n)
  have hpw' := hpw
  simp only [List.pairwise_append, List.mem_append] at hpw'
  obtain ⟨⟨hp, hbl, hpb⟩, hpo, hall⟩ := hpw'
  have hyc : y ∈ c := (hc y).mpr (Or.inr hw)
  have hxc : x ∈ c := (hc x).mpr (Or.inl rfl)
  have inblock : ∀ z, z ∈ c → z ∈ block := by
    intro z hz
    have := hmem z
    simp only [List.mem_append] at this
    rcases this with (h | h) | h
    · exact absurd hz (hpre z h)
    · exact h
    · exact absurd hz (hpost z h)
  have hxb := inblock x hxc
  have hyb := inblock y hyc
  have key : ∀ a b, a ∈ c → b ∈ c → P w s D a b → a < b := by
    intro a b ha hb hq
    have hab : a ≠ b := by rintro rfl; simp [P] at hq
    have w1 := F1 a b ha hb hab
    have d2 := F3 b hb
    have e1 := hsym a b
    rcases hq with h | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact h.1
    · omega
    · exact absurd h3 d2
  refine ⟨D ∪ c, pre ++ block.reverse ++ post, ⟨pre, block, post, ?_, ?_, ?_, rfl, rfl⟩, ?_, ?_, ?_,
    Finset.subset_union_left, Finset.mem_union_right _ hxc⟩
  · have hne : x ≠ y := hxy.ne
    rcases block with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hxb
    · simp only [List.mem_singleton] at hxb hyb
      exact absurd (hxb.trans hyb.symm) hne
    · simp
  · exact hbl.imp_of_mem fun ha hb hq => key _ _ (hblock _ ha) (hblock _ hb) hq
  · have hndp : pre.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
    have hndq : post.Nodup := (List.nodup_append.mp hnd).2.1
    have nk : ∀ k, k ∉ c → w x k ≠ s := fun k hkc h => hkc ((hc k).mpr (Or.inr h))
    have h1 := hside x y hxy post.toFinset pre.toFinset ?_ ?_
    · rw [List.toFinset_card_of_nodup hndq, List.toFinset_card_of_nodup hndp, ← Int.natAbs_neg,
        neg_sub] at h1
      exact h1
    · intro k
      rw [List.mem_toFinset]
      have e := hsym k x
      constructor
      · intro hk
        have nk' := nk k (hpost k hk)
        rcases hall x (Or.inr hxb) k hk with ⟨h1, h2 | ⟨h2, -⟩⟩ | ⟨h1, h2 | ⟨h2, -⟩⟩
        · exact Or.inl ⟨h1, by omega⟩
        · exact absurd h2 nk'
        · exact Or.inr ⟨h1, by omega⟩
        · omega
      · intro hk
        have hkc : k ∉ c := by
          rw [hc]
          rintro (rfl | h)
          · omega
          · omega
        have := hmem k
        simp only [List.mem_append] at this
        rcases this with (h | h) | h
        · rcases hpb k h x hxb with ⟨h1, h2 | ⟨h2, -⟩⟩ | ⟨h1, h2 | ⟨h2, -⟩⟩ <;> omega
        · exact absurd (hblock k h) hkc
        · exact h
    · intro k
      rw [List.mem_toFinset]
      have e := hsym k x
      constructor
      · intro hk
        have nk' := nk k (hpre k hk)
        rcases hpb k hk x hxb with ⟨h1, h2 | ⟨h2, -⟩⟩ | ⟨h1, h2 | ⟨h2, -⟩⟩
        · exact Or.inr ⟨h1, by omega⟩
        · omega
        · exact Or.inl ⟨h1, by omega⟩
        · exact absurd h2 nk'
      · intro hk
        have hkc : k ∉ c := by
          rw [hc]
          rintro (rfl | h)
          · omega
          · omega
        have := hmem k
        simp only [List.mem_append] at this
        rcases this with (h | h) | h
        · exact h
        · exact absurd (hblock k h) hkc
        · rcases hall x (Or.inr hxb) k h with ⟨h1, h2 | ⟨h2, -⟩⟩ | ⟨h1, h2 | ⟨h2, -⟩⟩ <;> omega
  · exact (((List.reverse_perm block).append_left pre).append_right post).trans hperm
  · refine pw_rev (· ∈ c) hpw hblock hpre hpost ?_ ?_
    · intro a b hq hnc
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨h1, h2.imp_right fun h => ⟨h.1, ?_⟩⟩
        intro hm
        rcases Finset.mem_union.mp hm with hm | hm
        · exact h.2 hm
        · exact hnc ⟨hm, F2 a b hm h1.ne h.1⟩
      · exact Or.inr ⟨h1, h2.imp_right fun h => ⟨h.1, Finset.mem_union_left _ h.2⟩⟩
    · intro a b ha hb hq
      have hlt := key a b ha hb hq
      exact Or.inr ⟨hlt, Or.inr ⟨F1 a b ha hb hlt.ne, Finset.mem_union_right _ ha⟩⟩
  · intro a b ha hab hwab
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_left _ (hD a b ha hab hwab)
    · exact Finset.mem_union_right _ (F2 a b ha hab hwab)

theorem level {n d : ℕ} {w : Fin n → Fin n → ℕ}
    (hsym : ∀ i j, w i j = w j i)
    (htri : ∀ i j k, i < j → j < k → B (w i j) (w i k) (w j k))
    (hside : ∀ i j, i < j → ∀ T1 T2 : Finset (Fin n),
      (∀ k, k ∈ T1 ↔ (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)) →
      (∀ k, k ∈ T2 ↔ (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)) →
      d ≤ ((T1.card : ℤ) - (T2.card : ℤ)).natAbs)
    (s : ℕ) : ∀ (m : ℕ) (D : Finset (Fin n)) (L : List (Fin n)), (univ \ D).card ≤ m →
    L.Perm (List.finRange n) → L.Pairwise (P w s D) →
    (∀ a b, a ∈ D → a ≠ b → w a b = s → b ∈ D) →
    ∃ L' : List (Fin n), Relation.ReflTransGen (Rel n d) L L' ∧ L'.Perm (List.finRange n) ∧
      L'.Pairwise (P w (s + 1) ∅) := by
  intro m
  induction m with
  | zero =>
    intro D L hm hperm hpw hD
    refine ⟨L, Relation.ReflTransGen.refl, hperm, hpw.imp fun {a b} hq => ?_⟩
    have hall : ∀ z : Fin n, z ∈ D := by
      intro z
      by_contra hz
      have : z ∈ univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
      exact absurd (Finset.card_pos.mpr ⟨z, this⟩) (by omega)
    rcases hq with ⟨h1, h2 | ⟨h2, h3⟩⟩ | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact Or.inl ⟨h1, by
        rcases Nat.lt_or_ge (s + 1) (w a b) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, by simp⟩⟩
    · exact absurd (hall a) h3
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
  | succ m ih =>
    intro D L hm hperm hpw hD
    by_cases hex : ∃ x y, x < y ∧ w x y = s ∧ x ∉ D
    · obtain ⟨x, y, hxy, hw, hxD⟩ := hex
      obtain ⟨D', L', hrel, hperm', hpw', hD', hsub, hxD'⟩ :=
        step hsym htri hside s D L hperm hpw hD x y hxy hw hxD
      have hlt : (univ \ D').card < (univ \ D).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hsub, ?_⟩
        intro h
        have : x ∈ univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxD⟩
        rw [← h] at this
        exact (Finset.mem_sdiff.mp this).2 hxD'
      obtain ⟨L'', h1, h2, h3⟩ := ih D' L' (by omega) hperm' hpw' hD'
      exact ⟨L'', Relation.ReflTransGen.head hrel h1, h2, h3⟩
    · refine ⟨L, Relation.ReflTransGen.refl, hperm, hpw.imp fun {a b} hq => ?_⟩
      rcases hq with ⟨h1, h2 | ⟨h2, h3⟩⟩ | ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact Or.inl ⟨h1, by
          rcases Nat.lt_or_ge (s + 1) (w a b) with h | h
          · exact Or.inl h
          · exact Or.inr ⟨by omega, by simp⟩⟩
      · exact absurd ⟨a, b, h1, h2, h3⟩ hex
      · exact Or.inr ⟨h1, Or.inl (by omega)⟩
      · exact Or.inr ⟨h1, Or.inl (by omega)⟩

theorem sweep (n d : ℕ) (w : Fin n → Fin n → ℕ)
    (hsym : ∀ i j, w i j = w j i)
    (htri : ∀ i j k, i < j → j < k →
      (w i j < w i k ∧ w i k < w j k) ∨ (w j k < w i k ∧ w i k < w i j) ∨
      (w i j = w i k ∧ w i k = w j k))
    (hside : ∀ i j, i < j → d ≤ (((univ.filter fun k : Fin n =>
        (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)).card : ℤ) - ((univ.filter fun k : Fin n =>
        (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)).card : ℤ)).natAbs) :
    Relation.ReflTransGen (fun u v : List (Fin n) =>
      ∃ pre block post : List (Fin n), 2 ≤ block.length ∧ block.Pairwise (· < ·) ∧
        d ≤ ((pre.length : ℤ) - (post.length : ℤ)).natAbs ∧
        u = pre ++ block ++ post ∧ v = pre ++ block.reverse ++ post)
      (List.finRange n) (List.finRange n).reverse := by
  have hside' : ∀ i j, i < j → ∀ T1 T2 : Finset (Fin n),
      (∀ k, k ∈ T1 ↔ (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j)) →
      (∀ k, k ∈ T2 ↔ (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k)) →
      d ≤ ((T1.card : ℤ) - (T2.card : ℤ)).natAbs := by
    intro i j hij T1 T2 h1 h2
    have e1 : T1 = univ.filter fun k : Fin n =>
        (i < k ∧ w i j < w i k) ∨ (k < i ∧ w i k < w i j) := by
      ext k; simp [h1]
    have e2 : T2 = univ.filter fun k : Fin n =>
        (i < k ∧ w i k < w i j) ∨ (k < i ∧ w i j < w i k) := by
      ext k; simp [h2]
    rw [e1, e2]
    exact hside i j hij
  have all : ∀ s : ℕ, ∃ L : List (Fin n), Relation.ReflTransGen (Rel n d) (List.finRange n) L ∧
      L.Perm (List.finRange n) ∧ L.Pairwise (P w s ∅) := by
    intro s
    induction s with
    | zero =>
      refine ⟨_, Relation.ReflTransGen.refl, List.Perm.refl _,
        (List.pairwise_lt_finRange n).imp fun {a b} h => Or.inl ⟨h, ?_⟩⟩
      rcases Nat.eq_zero_or_pos (w a b) with h0 | h0
      · exact Or.inr ⟨h0, by simp⟩
      · exact Or.inl h0
    | succ s ih =>
      obtain ⟨L, h1, h2, h3⟩ := ih
      obtain ⟨L', g1, g2, g3⟩ := level hsym htri hside' s _ ∅ L le_rfl h2 h3 (by simp)
      exact ⟨L', h1.trans g1, g2, g3⟩
  obtain ⟨L, h1, h2, h3⟩ := all ((univ.sup fun a : Fin n => univ.sup fun b : Fin n => w a b) + 1)
  have hrev : L.Pairwise (fun a b => b < a) := by
    refine h3.imp fun {a b} hq => ?_
    have hle : ∀ a b : Fin n, w a b < (univ.sup fun a : Fin n => univ.sup fun b : Fin n => w a b) + 1 :=
      fun a b => Nat.lt_succ_of_le ((Finset.le_sup (f := fun b : Fin n => w a b) (Finset.mem_univ b)).trans
        (Finset.le_sup (f := fun a : Fin n => univ.sup fun b : Fin n => w a b) (Finset.mem_univ a)))
    rcases hq with ⟨h1, h2 | ⟨h2, -⟩⟩ | ⟨h1, -⟩
    · exact absurd (hle a b) (by omega)
    · exact absurd (hle a b) (by omega)
    · exact h1
  have hL : L = (List.finRange n).reverse :=
    List.Perm.eq_of_pairwise (le := fun a b : Fin n => b < a)
      (fun a b _ _ h1 h2 => absurd h1 (lt_asymm h2)) hrev
      (List.pairwise_reverse.mpr (List.pairwise_lt_finRange n))
      (h2.trans (List.reverse_perm _).symm)
  rw [← hL]
  exact h1
end G75sweep

theorem OMA.solution : OMA.R_Green75_green_75_variants_pinchasi_R1_H2_R1.H1 :=
  fun n d _ w hsym htri hside => G75sweep.sweep n d w hsym htri hside
