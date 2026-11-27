import OMAReductions.R_Erdos131_erdos_131_variants_elrss_R1

-- Step Erdos131.erdos_131.variants.elrss.R1.H2: hypothesis H2 of reduction Erdos131.erdos_131.variants.elrss.R1
-- Credit: @loremcdmx
-- H2 := ∀ (n : ℕ), 0 < n → ∀ (J : Finset ℕ) (S : ℕ → Finset (ZMod n)),     (∀ j ∈ J, (0 : ZMod n) ∈ S j) →     (∀ f : ℕ → ZMod n, (∀ j ∈ J, f j ∈ S j) →       (∑ j ∈ J, f j) = 0 → ∀ j ∈ J, f j = 0) →     (∑ j ∈ J, ((S j).card - 1)) + 1 ≤ n  set_option maxHeartbeats 2000000 in

open Finset
open scoped BigOperators Classical Pointwise

namespace OMA.Aux

theorem sk {n : ℕ} [NeZero n] : ∀ (k : ℕ) (A B : Finset (ZMod n)), B.card = k →
    (0 : ZMod n) ∈ A → (0 : ZMod n) ∈ B →
    (∀ a ∈ A, ∀ b ∈ B, a + b = 0 → a = 0 ∧ b = 0) →
    A.card + B.card ≤ (A + B).card + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A B hk hA hB huniq
  by_cases hall : ∀ b ∈ B, b = 0
  · have hBs : B = {0} := by
      ext x
      constructor
      · intro h; exact mem_singleton.2 (hall x h)
      · intro h; rw [mem_singleton.1 h]; exact hB
    subst hBs
    have : A ⊆ A + {0} := by
      intro a ha
      exact mem_add.2 ⟨a, ha, 0, mem_singleton_self _, add_zero a⟩
    have := card_le_card this
    simp only [card_singleton]
    omega
  · push_neg at hall
    obtain ⟨b, hbB, hb0⟩ := hall
    have hex : ∃ e ∈ A, ∃ b' ∈ B, e + b' ∉ A := by
      by_contra hno
      push_neg at hno
      have h1 : ∀ m : ℕ, m • b ∈ A := by
        intro m
        induction m with
        | zero => simpa using hA
        | succ m ih2 => rw [succ_nsmul]; exact hno _ ih2 b hbB
      have := huniq _ (h1 (n - 1)) b hbB (by
        rw [← succ_nsmul, Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n)), nsmul_eq_mul,
          ZMod.natCast_self, zero_mul])
      exact hb0 this.2
    obtain ⟨e, he, b', hb', hnot⟩ := hex
    set A' := A ∪ B.image (fun x => e + x) with hA'
    set B' := B.filter (fun x => e + x ∈ A) with hB'
    have hlt : B'.card < B.card :=
      card_lt_card (filter_ssubset.2 ⟨b', hb', hnot⟩)
    have hA'0 : (0 : ZMod n) ∈ A' := mem_union_left _ hA
    have hB'0 : (0 : ZMod n) ∈ B' := mem_filter.2 ⟨hB, by simpa using he⟩
    have hsub : A' + B' ⊆ A + B := by
      intro z hz
      obtain ⟨a', ha', y, hy, rfl⟩ := mem_add.1 hz
      rcases mem_union.1 ha' with h | h
      · exact mem_add.2 ⟨a', h, y, (mem_filter.1 hy).1, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
        exact mem_add.2 ⟨e + y, (mem_filter.1 hy).2, x, hx, by abel⟩
    have hint : A ∩ B.image (fun x => e + x) = B'.image (fun x => e + x) := by
      ext z
      constructor
      · intro h
        obtain ⟨hzA, hzim⟩ := mem_inter.1 h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hzim
        exact mem_image.2 ⟨x, mem_filter.2 ⟨hx, hzA⟩, rfl⟩
      · intro h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 h
        have := mem_filter.1 hx
        exact mem_inter.2 ⟨this.2, mem_image.2 ⟨x, this.1, rfl⟩⟩
    have hinj : Function.Injective (fun x : ZMod n => e + x) := fun x y h => add_left_cancel h
    have hcardeq : A'.card + B'.card = A.card + B.card := by
      have h1 := card_union_add_card_inter A (B.image (fun x => e + x))
      rw [hint, card_image_of_injective _ hinj, card_image_of_injective _ hinj] at h1
      rw [hA']
      omega
    have huniq' : ∀ a ∈ A', ∀ y ∈ B', a + y = 0 → a = 0 ∧ y = 0 := by
      intro a' ha' y hy h
      rcases mem_union.1 ha' with h' | h'
      · exact huniq a' h' y (mem_filter.1 hy).1 h
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 h'
        have h2 := huniq (e + y) (mem_filter.1 hy).2 x hx (by rw [← h]; abel)
        have h3 := huniq e he y (mem_filter.1 hy).1 h2.1
        refine ⟨?_, h3.2⟩
        rw [h3.1, h2.2, add_zero]
    have := ih B'.card (hk ▸ hlt) A' B' rfl hA'0 hB'0 huniq'
    have := card_le_card hsub
    omega

theorem main {n : ℕ} [NeZero n] : ∀ (J : Finset ℕ) (S : ℕ → Finset (ZMod n)),
    (∀ j ∈ J, (0 : ZMod n) ∈ S j) →
    (∀ f : ℕ → ZMod n, (∀ j ∈ J, f j ∈ S j) →
      (∑ j ∈ J, f j) = 0 → ∀ j ∈ J, f j = 0) →
    ∃ T : Finset (ZMod n), (0 : ZMod n) ∈ T ∧
      (∀ t ∈ T, ∃ f : ℕ → ZMod n, (∀ j ∈ J, f j ∈ S j) ∧ ∑ j ∈ J, f j = t) ∧
      (∑ j ∈ J, ((S j).card - 1)) + 1 ≤ T.card := by
  intro J S
  induction J using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨{0}, mem_singleton_self _, ?_, by simp⟩
    intro t ht
    refine ⟨fun _ => 0, by simp, ?_⟩
    rw [mem_singleton.1 ht]; simp
  | insert j J' hj ih =>
    intro h0 huniq
    have h0' : ∀ i ∈ J', (0 : ZMod n) ∈ S i := fun i hi => h0 i (mem_insert_of_mem hi)
    have hsw : ∀ (f : ℕ → ZMod n) (s : ZMod n),
        ∑ i ∈ insert j J', Function.update f j s i = s + ∑ i ∈ J', f i := by
      intro f s
      rw [sum_insert hj, Function.update_self]
      congr 1
      exact sum_congr rfl (fun i hi => Function.update_of_ne (fun h => hj (by rw [← h]; exact hi)) _ _)
    have hmem : ∀ (f : ℕ → ZMod n) (s : ZMod n), s ∈ S j → (∀ i ∈ J', f i ∈ S i) →
        ∀ i ∈ insert j J', Function.update f j s i ∈ S i := by
      intro f s hs hf i hi
      by_cases h : i = j
      · subst h; rw [Function.update_self]; exact hs
      · rw [Function.update_of_ne h]; exact hf i (mem_of_mem_insert_of_ne hi h)
    have huniq' : ∀ f : ℕ → ZMod n, (∀ i ∈ J', f i ∈ S i) →
        (∑ i ∈ J', f i) = 0 → ∀ i ∈ J', f i = 0 := by
      intro f hf hsum i hi
      have := huniq (Function.update f j 0) (hmem f 0 (h0 j (mem_insert_self _ _)) hf)
        (by rw [hsw, zero_add]; exact hsum) i (mem_insert_of_mem hi)
      rwa [Function.update_of_ne (fun h => hj (by rw [← h]; exact hi))] at this
    obtain ⟨T', h0T, hrep, hcard⟩ := ih h0' huniq'
    have hSj0 : (0 : ZMod n) ∈ S j := h0 j (mem_insert_self _ _)
    have hsk := sk _ T' (S j) rfl h0T hSj0 (by
      intro a ha b hb hab
      obtain ⟨f, hf, hfa⟩ := hrep a ha
      have hall := huniq (Function.update f j b) (hmem f b hb hf)
        (by rw [hsw, hfa, add_comm]; exact hab)
      have hbj := hall j (mem_insert_self _ _)
      rw [Function.update_self] at hbj
      refine ⟨?_, hbj⟩
      rw [← hfa]
      apply sum_eq_zero
      intro i hi
      have := hall i (mem_insert_of_mem hi)
      rwa [Function.update_of_ne (fun h => hj (by rw [← h]; exact hi))] at this)
    refine ⟨T' + S j, mem_add.2 ⟨0, h0T, 0, hSj0, add_zero 0⟩, ?_, ?_⟩
    · intro t ht
      obtain ⟨t', ht', s, hs, rfl⟩ := mem_add.1 ht
      obtain ⟨f, hf, hfs⟩ := hrep t' ht'
      refine ⟨Function.update f j s, hmem f s hs hf, ?_⟩
      rw [hsw, hfs, add_comm]
    · have hpos : 0 < (S j).card := card_pos.2 ⟨0, hSj0⟩
      rw [sum_insert hj]
      omega

end OMA.Aux

theorem OMA.solution : OMA.R_Erdos131_erdos_131_variants_elrss_R1.H2 := by
  intro n hn J S h0 huniq
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨T, _, _, hc⟩ := OMA.Aux.main J S h0 huniq
  have := card_le_univ T
  rw [ZMod.card] at this
  omega
