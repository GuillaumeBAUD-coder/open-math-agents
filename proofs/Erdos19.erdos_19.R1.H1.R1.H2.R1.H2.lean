import OMAReductions.R_Erdos19_erdos_19_R1_H1_R1_H2_R1

/-! Lines of K keep their colors in {0, ..., n-t-1}. A line a not in K meets P, so it has two
points; the point p of a in P lies on b, and the other point x lies off b, because a meets b in
at most one point. Such a line gets the color n - t + (rank of p in P + rank of x off b) mod t,
a Latin-square coloring: two such lines that meet share p or x, and then differ in the other.
Colors of the two kinds lie in disjoint ranges. -/

open Finset in
theorem OMA.solution : OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1.H2 := by
  intro n t L b P ht hb hPb hPc hbc hL hP2 K hc
  obtain ⟨c, hc⟩ := hc
  have htn : t ≤ n := by
    rw [← hbc]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have two_in_b : ∀ a ∈ L, a ≠ b → ∀ p ∈ a, p ∈ b → ∀ x ∈ a, x ∈ b → p = x := by
    intro a haL hab p hpa hpb x hxa hxb
    exact card_le_one.1 (hL a haL b hb hab) p (mem_inter.2 ⟨hpa, hpb⟩) x (mem_inter.2 ⟨hxa, hxb⟩)
  have extra : ∀ a ∈ L, a ∉ K → ∃ p x, p ∈ P ∧ x ∉ b ∧ p ≠ x ∧ a = {p, x} := by
    intro a haL haK
    have hK : ¬ (a = b ∨ Disjoint a P) := fun h => haK (mem_filter.2 ⟨haL, h⟩)
    rw [not_or] at hK
    obtain ⟨p, hpa, hpP⟩ := not_disjoint_iff.1 hK.2
    have h2 := hP2 p hpP a haL hK.1 hpa
    obtain ⟨x, hxa, hxp⟩ := exists_mem_ne (show 1 < a.card by omega) p
    have hxb : x ∉ b := fun hxb => hxp (two_in_b a haL hK.1 p hpa (hPb hpP) x hxa hxb).symm
    refine ⟨p, x, hpP, hxb, hxp.symm, ?_⟩
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · simp [h2, card_pair hxp.symm]
  have rank_mono : ∀ (s : Finset (Fin n)) (z w : Fin n), z ∈ s → z < w →
      (s.filter (· < z)).card < (s.filter (· < w)).card := by
    intro s z w hz hlt
    apply card_lt_card
    refine (ssubset_iff_of_subset ?_).2 ⟨z, by simp [hz, hlt], by simp⟩
    intro y hy
    simp only [mem_filter] at hy ⊢
    exact ⟨hy.1, hy.2.trans hlt⟩
  have rank_inj : ∀ (s : Finset (Fin n)) (z w : Fin n), z ∈ s → w ∈ s →
      (s.filter (· < z)).card = (s.filter (· < w)).card → z = w := by
    intro s z w hz hw h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := rank_mono s z w hz hlt; omega
    · have := rank_mono s w z hw hlt; omega
  have rank_lt : ∀ (s : Finset (Fin n)) (z : Fin n), z ∈ s →
      (s.filter (· < z)).card < s.card := by
    intro s z hz
    apply card_lt_card
    exact (ssubset_iff_of_subset (filter_subset _ _)).2 ⟨z, hz, by simp⟩
  let f : Fin n → ℕ := fun z =>
    if z ∈ b then (P.filter (· < z)).card else ((univ \ b).filter (· < z)).card
  have hsum : ∀ p x, p ∈ P → x ∉ b → p ≠ x → ∑ z ∈ ({p, x} : Finset (Fin n)), f z =
      (P.filter (· < p)).card + ((univ \ b).filter (· < x)).card := by
    intro p x hp hx hpx
    rw [sum_pair hpx]
    simp only [f, if_pos (hPb hp), if_neg hx]
  have hcol : ∀ m : ℕ, n - t + m % t < n := by
    intro m
    have := Nat.mod_lt m ht
    omega
  refine ⟨fun a => if h : a.val ∈ K then Fin.castLE (Nat.sub_le n t) (c ⟨a.val, h⟩)
      else ⟨n - t + (∑ z ∈ a.val, f z) % t, hcol _⟩, ?_⟩
  intro a d had hint
  dsimp only
  by_cases ha : a.val ∈ K <;> by_cases hd : d.val ∈ K
  · rw [dif_pos ha, dif_pos hd]
    intro heq
    apply hc ⟨a.val, ha⟩ ⟨d.val, hd⟩ _ hint (Fin.castLE_injective _ heq)
    intro h
    apply had
    exact Subtype.ext (Subtype.mk.inj h)
  · rw [dif_pos ha, dif_neg hd]
    intro heq
    have h1 : (Fin.castLE (Nat.sub_le n t) (c ⟨a.val, ha⟩)).val =
        n - t + (∑ z ∈ d.val, f z) % t := congrArg Fin.val heq
    rw [Fin.val_castLE] at h1
    have := (c ⟨a.val, ha⟩).isLt
    generalize (∑ z ∈ d.val, f z) % t = X at h1
    omega
  · rw [dif_neg ha, dif_pos hd]
    intro heq
    have h1 : n - t + (∑ z ∈ a.val, f z) % t =
        (Fin.castLE (Nat.sub_le n t) (c ⟨d.val, hd⟩)).val := congrArg Fin.val heq
    rw [Fin.val_castLE] at h1
    have := (c ⟨d.val, hd⟩).isLt
    generalize (∑ z ∈ a.val, f z) % t = X at h1
    omega
  · rw [dif_neg ha, dif_neg hd]
    intro heq
    have h1 : n - t + (∑ z ∈ a.val, f z) % t = n - t + (∑ z ∈ d.val, f z) % t :=
      congrArg Fin.val heq
    have hmod := Nat.add_left_cancel h1
    obtain ⟨p, x, hpP, hxb, hpx, hae⟩ := extra a.val a.property ha
    obtain ⟨p', x', hpP', hxb', hpx', hde⟩ := extra d.val d.property hd
    rw [hae, hsum p x hpP hxb hpx, hde, hsum p' x' hpP' hxb' hpx'] at hmod
    obtain ⟨z, hz⟩ := hint
    rw [mem_inter] at hz
    have hab : a.val ≠ b := fun h => ha (mem_filter.2 ⟨a.property, Or.inl h⟩)
    have hdb : d.val ≠ b := fun h => hd (mem_filter.2 ⟨d.property, Or.inl h⟩)
    have hpa : p ∈ a.val := by rw [hae]; exact mem_insert_self _ _
    have hpd : p' ∈ d.val := by rw [hde]; exact mem_insert_self _ _
    have hxo : x ∈ univ \ b := by simp [hxb]
    have hxo' : x' ∈ univ \ b := by simp [hxb']
    have rPlt := rank_lt P p hpP
    have rPlt' := rank_lt P p' hpP'
    have rOlt := rank_lt (univ \ b) x hxo
    have rOlt' := rank_lt (univ \ b) x' hxo'
    rw [hPc] at rPlt rPlt'
    rw [hbc] at rOlt rOlt'
    by_cases hzb : z ∈ b
    · have e1 : p = z := two_in_b a.val a.property hab p hpa (hPb hpP) z hz.1 hzb
      have e2 : p' = z := two_in_b d.val d.property hdb p' hpd (hPb hpP') z hz.2 hzb
      have hxx : x ≠ x' := by
        intro hxx
        apply had
        apply Subtype.ext
        rw [hae, hde, e1, e2, hxx]
      apply hxx
      apply rank_inj (univ \ b) x x' hxo hxo'
      rw [e1, e2] at hmod
      have h3 := Nat.ModEq.add_left_cancel' _ hmod
      unfold Nat.ModEq at h3
      rwa [Nat.mod_eq_of_lt rOlt, Nat.mod_eq_of_lt rOlt'] at h3
    · have hza := hz.1
      have hzd := hz.2
      rw [hae, mem_insert, mem_singleton] at hza
      rw [hde, mem_insert, mem_singleton] at hzd
      have e1 : z = x := hza.resolve_left (fun h => hzb (by rw [h]; exact hPb hpP))
      have e2 : z = x' := hzd.resolve_left (fun h => hzb (by rw [h]; exact hPb hpP'))
      have hpp : p ≠ p' := by
        intro hpp
        apply had
        apply Subtype.ext
        rw [hae, hde, hpp, ← e1, ← e2]
      apply hpp
      apply rank_inj P p p' hpP hpP'
      rw [← e1, ← e2] at hmod
      have h3 := Nat.ModEq.add_right_cancel' _ hmod
      unfold Nat.ModEq at h3
      rwa [Nat.mod_eq_of_lt rPlt, Nat.mod_eq_of_lt rPlt'] at h3
