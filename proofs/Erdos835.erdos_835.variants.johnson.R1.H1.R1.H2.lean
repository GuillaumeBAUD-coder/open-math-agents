import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

-- Problem: https://lefttosolve.com/p/Erdos835.erdos_835.variants.johnson.R1.H1.R1.H2
-- Credit: @oliverboersma

-- ===== submission: auxiliary =====
theorem OMA_H2_even_used {α C : Type*} [LinearOrder α] [DecidableEq C] (Q : Finset α)
    (e : α → α → C) (hsym : ∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a)
    (hinj : ∀ a ∈ Q, ∀ b ∈ Q, ∀ d ∈ Q, b ≠ a → d ≠ a → b ≠ d → e a b ≠ e a d) (c : C) :
    Even (Q.filter (fun v => ∃ t ∈ Q, t ≠ v ∧ e v t = c)).card := by
  classical
  set P := (Q ×ˢ Q).filter (fun p => p.1 ≠ p.2 ∧ e p.1 p.2 = c) with hP
  have h1 : P.card = (Q.filter (fun v => ∃ t ∈ Q, t ≠ v ∧ e v t = c)).card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_filter]
      exact ⟨hp.1.1, p.2, hp.1.2, Ne.symm hp.2.1, hp.2.2⟩
    · intro p hp q hq hpq
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hp hq
      by_contra hne
      have h2 : p.2 ≠ q.2 := by
        intro h; exact hne (Prod.ext hpq h)
      apply hinj p.1 hp.1.1 p.2 hp.1.2 q.2 hq.1.2 (Ne.symm hp.2.1) (by rw [hpq]; exact Ne.symm hq.2.1) h2
      rw [hp.2.2, hpq, hq.2.2]
    · intro v hv
      simp only [Finset.mem_filter] at hv
      obtain ⟨hvQ, t, htQ, htv, hc⟩ := hv
      refine ⟨(v, t), ?_, rfl⟩
      simp only [hP, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hvQ, htQ⟩, Ne.symm htv, hc⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.1 < p.2)
  have h3 : (P.filter (fun p => p.1 < p.2)).card = (P.filter (fun p => ¬ p.1 < p.2)).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      refine ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, Ne.symm hp.1.2.1, ?_⟩, not_lt.mpr hp.2.le⟩
      rw [hsym _ hp.1.1.2 _ hp.1.1.1]; exact hp.1.2.2
    · intro p hp q hq hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 hpq.1
    · intro q hq
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [hP, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, Ne.symm hq.1.2.1, ?_⟩, ?_⟩
      · rw [hsym _ hq.1.1.2 _ hq.1.1.1]; exact hq.1.2.2
      · exact lt_of_le_of_ne (not_lt.mp hq.2) (Ne.symm hq.1.2.1)
  rw [← h1, ← h2, h3]
  exact ⟨_, rfl⟩

theorem OMA_H2_key {α C : Type*} [LinearOrder α] [Fintype C] [DecidableEq C] (Q : Finset α)
    (hodd : Odd Q.card) (hC : Fintype.card C = Q.card)
    (e : α → α → C) (hsym : ∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a)
    (hinj : ∀ a ∈ Q, ∀ b ∈ Q, ∀ d ∈ Q, b ≠ a → d ≠ a → b ≠ d → e a b ≠ e a d)
    (a : α) (ha : a ∈ Q) (b : α) (hb : b ∈ Q) (hab : a ≠ b) (i : C)
    (hia : ∀ t ∈ Q, t ≠ a → i ≠ e a t) (hib : ∀ t ∈ Q, t ≠ b → i ≠ e b t) : False := by
  classical
  let r : α → C → Prop := fun v c => ∀ t ∈ Q, t ≠ v → e v t ≠ c
  have habove : ∀ v ∈ Q, (Finset.univ.filter (fun c => r v c)).card = 1 := by
    intro v hv
    have heq : Finset.univ.filter (fun c => r v c) = Finset.univ \ (Q.erase v).image (e v) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_erase, r]
      constructor
      · rintro h ⟨t, ⟨htv, htQ⟩, hc⟩
        exact h t htQ htv hc
      · intro h t htQ htv hc
        exact h ⟨t, ⟨htv, htQ⟩, hc⟩
    have himg : ((Q.erase v).image (e v)).card = Q.card - 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hv]
      intro x hx y hy hxy
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
      by_contra hne
      exact hinj v hv x hx.1 y hy.1 hx.2 hy.2 hne hxy
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hC, himg]
    have : 1 ≤ Q.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have hbelow : ∀ c : C, 1 ≤ (Q.filter (fun v => r v c)).card := by
    intro c
    have hev := OMA_H2_even_used Q e hsym hinj c
    have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun v => r v c)
    have hneg : Q.filter (fun v => ¬ r v c) = Q.filter (fun v => ∃ t ∈ Q, t ≠ v ∧ e v t = c) := by
      apply Finset.filter_congr
      intro v _
      simp only [r, not_forall, not_not, exists_prop]
    rw [hneg] at hsplit
    rcases Nat.eq_zero_or_pos (Q.filter (fun v => r v c)).card with h0 | h0
    · rw [h0, zero_add] at hsplit
      rw [hsplit] at hev
      exact absurd hev (Nat.not_even_iff_odd.mpr hodd)
    · exact h0
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Q)
    (t := (Finset.univ : Finset C)) (r := r)
  have hL : ∑ v ∈ Q, (Finset.bipartiteAbove r Finset.univ v).card = Q.card := by
    rw [Finset.card_eq_sum_ones Q]
    apply Finset.sum_congr rfl
    intro v hv
    exact habove v hv
  have hlt : ∑ c ∈ (Finset.univ : Finset C), 1 <
      ∑ c ∈ (Finset.univ : Finset C), (Finset.bipartiteBelow r Q c).card := by
    apply Finset.sum_lt_sum
    · intro c _; exact hbelow c
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      have hsub : ({a, b} : Finset α) ⊆ Finset.bipartiteBelow r Q i := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        simp only [Finset.bipartiteBelow, Finset.mem_filter, r]
        rcases hv with rfl | rfl
        · exact ⟨ha, fun t ht htv h => hia t ht htv h.symm⟩
        · exact ⟨hb, fun t ht htv h => hib t ht htv h.symm⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hab] at this
      omega
  rw [← hdc, hL, Finset.sum_const, Finset.card_univ, hC, smul_eq_mul, mul_one] at hlt
  exact lt_irrefl _ hlt

-- ===== frozen statement + submitted proof =====
theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H2 :=
by
  intro k hk Q hQ e hsym hinj a ha b hb hab i j hi hj hij
  subst hij
  have hodd : Odd Q.card := by rw [hQ]; exact Even.add_one hk
  exact OMA_H2_key Q hodd (by rw [Fintype.card_fin, hQ]) e hsym hinj a ha b hb hab i hi hj
