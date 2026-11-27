import FormalConjectures.WrittenOnTheWallII.GraphConjecture96

/-!
# Proof of Written on the Wall II - Conjecture 96

For every finite simple connected graph `G` on at least two vertices,
`α(G) ≤ 1 + min_v distEven(v) · (max_v l(v) - 1)`.
-/

namespace OMA.WOWII96

open SimpleGraph Finset

private lemma exists_max_indepSet {α : Type*} [Fintype α] (G : SimpleGraph α) :
    ∃ I : Finset α, G.IsIndepSet (I : Set α) ∧ I.card = G.indepNum := by
  classical
  have hne : {n : ℕ | ∃ S : Finset α, G.IsNIndepSet n S}.Nonempty :=
    ⟨0, ∅, ⟨by simp [SimpleGraph.IsIndepSet], rfl⟩⟩
  have hbdd : BddAbove {n : ℕ | ∃ S : Finset α, G.IsNIndepSet n S} :=
    ⟨Fintype.card α, fun n ⟨S, hS⟩ => hS.card_eq ▸ S.card_le_univ⟩
  obtain ⟨I, hI⟩ := Nat.sSup_mem hne hbdd
  exact ⟨I, hI.isIndepSet, hI.card_eq⟩

private lemma card_le_indepNeighborsCard {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (x : α) (S : Finset α)
    (hS_sub : ∀ w ∈ S, G.Adj x w) (hS_ind : G.IsIndepSet (S : Set α)) :
    S.card ≤ indepNeighborsCard G x := by
  classical
  unfold indepNeighborsCard
  let f : {w // w ∈ S} ↪ G.neighborSet x :=
    ⟨fun w => ⟨w.1, hS_sub w.1 w.2⟩, fun a b hab => by
      apply Subtype.ext
      exact congrArg (fun z : G.neighborSet x => z.1) hab⟩
  let T : Finset (G.neighborSet x) := S.attach.map f
  have hT_card : T.card = S.card := by
    simp [T]
  have hT_ind : (G.induce (G.neighborSet x)).IsIndepSet (T : Set (G.neighborSet x)) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, T, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : a ≠ b := by
      intro h
      apply huv
      apply Subtype.ext
      exact h
    exact hS_ind ha hb hab
  rw [← hT_card]
  unfold SimpleGraph.indepNum
  apply le_csSup
  · exact ⟨Fintype.card (G.neighborSet x), fun n ⟨U, hU⟩ => hU.card_eq ▸ U.card_le_univ⟩
  · exact ⟨T, hT_ind, rfl⟩

private lemma exists_pred_dist {α : Type*} (G : SimpleGraph α) (h : G.Connected)
    (v₀ u : α) (hne : u ≠ v₀) :
    ∃ y : α, G.Adj y u ∧ G.dist v₀ y + 1 = G.dist v₀ u := by
  have hreach : G.Reachable v₀ u := h v₀ u
  have hd_pos : 0 < G.dist v₀ u := hreach.pos_dist_of_ne hne.symm
  obtain ⟨p, hp⟩ := G.exists_walk_of_dist_ne_zero (Nat.ne_of_gt hd_pos)
  let k := p.length - 1
  have hk : k < p.length := by omega
  have hks : k + 1 = p.length := by omega
  let y := p.getVert k
  have hadj : G.Adj y u := by
    have h1 := p.adj_getVert_succ hk
    rw [hks, p.getVert_length] at h1
    exact h1
  have hle1 : G.dist v₀ y ≤ k := by
    calc G.dist v₀ y ≤ (p.take k).length := SimpleGraph.dist_le (p.take k)
      _ = k := by rw [Walk.take_length]; omega
  have hle2 : G.dist v₀ u ≤ G.dist v₀ y + 1 := by
    have hry : G.Reachable v₀ y := h v₀ y
    obtain ⟨q, hq⟩ := hry.exists_walk_length_eq_dist
    have hq' := SimpleGraph.dist_le (q.append (Walk.cons hadj Walk.nil))
    simp only [Walk.length_append, Walk.length_cons, Walk.length_nil, hq] at hq'
    exact hq'
  exact ⟨y, hadj, by omega⟩

private lemma dist_le_add_one_of_adj {α : Type*} (G : SimpleGraph α) (h : G.Connected)
    (v₀ x y : α) (hadj : G.Adj x y) : G.dist v₀ y ≤ G.dist v₀ x + 1 := by
  obtain ⟨q, hq⟩ := (h v₀ x).exists_walk_length_eq_dist
  have hq' := SimpleGraph.dist_le (q.append (Walk.cons hadj Walk.nil))
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil, hq] at hq'
  exact hq'

private lemma adj_of_indepNeighborsCard_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (h : G.Connected)
    (hL : ∀ v : α, indepNeighborsCard G v ≤ 1) {u w : α} (hne : u ≠ w) : G.Adj u w := by
  classical
  have hdist_le_one : G.dist u w ≤ 1 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨p, hp⟩ := (h u w).exists_walk_length_eq_dist
    have hp2 : 2 ≤ p.length := by omega
    let x₁ := p.getVert 1
    let x₂ := p.getVert 2
    have h01 : G.Adj u x₁ := by
      have h1 := p.adj_getVert_succ (show 0 < p.length by omega)
      simpa using h1
    have h12 : G.Adj x₁ x₂ := by
      have h2 := p.adj_getVert_succ (show 1 < p.length by omega)
      simpa using h2
    have hu_ne_x2 : u ≠ x₂ := by
      intro heq
      let hq : G.Walk u w := (p.drop 2).copy heq.symm rfl
      have hdist_le : G.dist u w ≤ hq.length := SimpleGraph.dist_le hq
      have hq_len : hq.length = p.length - 2 := by simp [hq]
      omega
    have h02 : G.Adj u x₂ := by
      by_contra hnot
      have h2le : ({u, x₂} : Finset α).card ≤ indepNeighborsCard G x₁ := by
        apply card_le_indepNeighborsCard G x₁ {u, x₂}
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact h01.symm
          · exact h12
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact absurd rfl hab
          · exact hnot
          · exact fun hba => hnot hba.symm
          · exact absurd rfl hab
      have hcard : ({u, x₂} : Finset α).card = 2 := Finset.card_pair hu_ne_x2
      have hle1 := hL x₁
      omega
    let q : G.Walk u w := Walk.cons h02 (p.drop 2)
    have hq_le : G.dist u w ≤ q.length := SimpleGraph.dist_le q
    have hq_len : q.length = p.length - 2 + 1 := by simp [q]
    omega
  have hd_pos : 0 < G.dist u w := (h u w).pos_dist_of_ne hne
  have hd_eq : G.dist u w = 1 := by omega
  exact SimpleGraph.dist_eq_one_iff_adj.mp hd_eq

end OMA.WOWII96

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  intro α _ _ _ G h
  classical
  dsimp only
  set minDistEven := (Finset.univ.image (SimpleGraph.distEven G)).min' (by simp)
  set maxL := (Finset.univ.image (fun v => SimpleGraph.indepNeighborsCard G v)).max' (by simp)
  have hv0_mem : minDistEven ∈ Finset.univ.image (SimpleGraph.distEven G) :=
    Finset.min'_mem _ _
  obtain ⟨v₀, -, hv₀⟩ := Finset.mem_image.mp hv0_mem
  have hL_ge : ∀ v : α, SimpleGraph.indepNeighborsCard G v ≤ maxL := fun v =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  have hL_pos : 1 ≤ maxL := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    obtain ⟨y, hy, -⟩ := OMA.WOWII96.exists_pred_dist G h a b hab.symm
    have h1 : ({y} : Finset α).card ≤ SimpleGraph.indepNeighborsCard G b := by
      apply OMA.WOWII96.card_le_indepNeighborsCard G b {y}
      · intro z hz
        simp only [Finset.mem_singleton] at hz
        subst hz
        exact hy.symm
      · intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_singleton] at hu hv
        exact absurd (hu.trans hv.symm) huv
    have h2 := hL_ge b
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨I, hI_ind, hI_card⟩ := OMA.WOWII96.exists_max_indepSet G
  have hnat : I.card ≤ 1 + minDistEven * (maxL - 1) := by
    by_cases hL1 : maxL = 1
    · have hcard_le1 : I.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro u hu w hw
        by_contra hne
        have hadj := OMA.WOWII96.adj_of_indepNeighborsCard_le_one G h
          (fun v => by have := hL_ge v; omega) hne
        exact hI_ind hu hw hne hadj
      omega
    · have hL2 : 2 ≤ maxL := by omega
      let E : Finset α := Finset.univ.filter fun w => Even (G.dist v₀ w)
      let O : Finset α := Finset.univ.filter fun w => ¬ Even (G.dist v₀ w)
      have hE_card : E.card = minDistEven := hv₀
      have hv0_in_E : v₀ ∈ E := by
        simp [E]
      have hIO_split : I.card = (I ∩ E).card + (I ∩ O).card := by
        have hdisj : Disjoint (I ∩ E) (I ∩ O) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_inter, Finset.mem_filter, E, O] at hw1 hw2
          exact hw2.2.2 hw1.2.2
        have hunion : (I ∩ E) ∪ (I ∩ O) = I := by
          ext w
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
            true_and, E, O]
          tauto
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      let pred : α → α := fun u =>
        if hu : u ≠ v₀ then (OMA.WOWII96.exists_pred_dist G h v₀ u hu).choose else v₀
      have hpred_adj : ∀ u, u ≠ v₀ → G.Adj (pred u) u := fun u hu => by
        simp only [pred, dif_pos hu]
        exact (OMA.WOWII96.exists_pred_dist G h v₀ u hu).choose_spec.1
      have hpred_dist : ∀ u, u ≠ v₀ → G.dist v₀ (pred u) + 1 = G.dist v₀ u := fun u hu => by
        simp only [pred, dif_pos hu]
        exact (OMA.WOWII96.exists_pred_dist G h v₀ u hu).choose_spec.2
      have hpred_maps : ∀ w ∈ I ∩ O, pred w ∈ E \ I := by
        intro w hw
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, O] at hw
        have hw_ne : w ≠ v₀ := by
          intro heq
          rw [heq] at hw
          exact hw.2 (by simp)
        have hadj := hpred_adj w hw_ne
        have hdist := hpred_dist w hw_ne
        have heven : Even (G.dist v₀ (pred w)) := by
          rw [Nat.even_iff] at *
          omega
        have hnotI : pred w ∉ I := by
          intro hmem
          exact hI_ind hmem hw.1 (G.ne_of_adj hadj) hadj
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, E]
        exact ⟨heven, hnotI⟩
      have hfiber_sum : (I ∩ O).card =
          ∑ x ∈ E \ I, ((I ∩ O).filter fun w => pred w = x).card := by
        exact Finset.card_eq_sum_card_fiberwise hpred_maps
      have hfiber_le_L : ∀ x ∈ E \ I, ((I ∩ O).filter fun w => pred w = x).card ≤ maxL := by
        intro x _
        let Fx := (I ∩ O).filter fun w => pred w = x
        have h1 : Fx.card ≤ SimpleGraph.indepNeighborsCard G x := by
          apply OMA.WOWII96.card_le_indepNeighborsCard G x Fx
          · intro w hw
            simp only [Fx, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, O] at hw
            have hw_ne : w ≠ v₀ := by
              intro heq
              rw [heq] at hw
              exact hw.1.2 (by simp)
            rw [← hw.2]
            exact hpred_adj w hw_ne
          · intro a ha b hb hab
            simp only [Fx, Finset.mem_coe, Finset.mem_filter, Finset.mem_inter] at ha hb
            exact hI_ind ha.1.1 hb.1.1 hab
        exact le_trans h1 (hL_ge x)
      have hfiber_le_L_sub : ∀ x ∈ E \ I, x ≠ v₀ →
          ((I ∩ O).filter fun w => pred w = x).card ≤ maxL - 1 := by
        intro x _ hx_ne
        let Fx := (I ∩ O).filter fun w => pred w = x
        let y := pred x
        have hyx : G.Adj y x := hpred_adj x hx_ne
        have hydist : G.dist v₀ y + 1 = G.dist v₀ x := hpred_dist x hx_ne
        have hy_notMem : y ∉ Fx := by
          intro hy
          simp only [Fx, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, O] at hy
          have hy_ne : y ≠ v₀ := by
            intro heq
            rw [heq] at hy
            exact hy.1.2 (by simp)
          have hdy := hpred_dist y hy_ne
          rw [hy.2] at hdy
          omega
        have hhy_nonadj : ∀ w ∈ Fx, ¬ G.Adj y w := by
          intro w hw hadj_yw
          simp only [Fx, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, O] at hw
          have hw_ne : w ≠ v₀ := by
            intro heq
            rw [heq] at hw
            exact hw.1.2 (by simp)
          have hdw := hpred_dist w hw_ne
          rw [hw.2] at hdw
          have htri := OMA.WOWII96.dist_le_add_one_of_adj G h v₀ y w hadj_yw
          omega
        have h1 : (insert y Fx).card ≤ SimpleGraph.indepNeighborsCard G x := by
          apply OMA.WOWII96.card_le_indepNeighborsCard G x (insert y Fx)
          · intro w hw
            simp only [Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact hyx.symm
            · simp only [Fx, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, O] at hw
              have hw_ne : w ≠ v₀ := by
                intro heq
                rw [heq] at hw
                exact hw.1.2 (by simp)
              rw [← hw.2]
              exact hpred_adj w hw_ne
          · intro a ha b hb hab
            simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · exact absurd rfl hab
            · exact hhy_nonadj b hb
            · exact fun hba => hhy_nonadj a ha hba.symm
            · simp only [Fx, Finset.mem_filter, Finset.mem_inter] at ha hb
              exact hI_ind ha.1.1 hb.1.1 hab
        rw [Finset.card_insert_of_notMem hy_notMem] at h1
        have h2 := hL_ge x
        change Fx.card ≤ maxL - 1
        omega
      have hE_split : (I ∩ E).card + (E \ I).card = E.card := by
        rw [Finset.inter_comm]
        exact Finset.card_inter_add_card_sdiff E I
      by_cases hv0I : v₀ ∈ I
      · have hIO_le : (I ∩ O).card ≤ (E \ I).card * (maxL - 1) := by
          rw [hfiber_sum]
          calc ∑ x ∈ E \ I, ((I ∩ O).filter fun w => pred w = x).card
              ≤ ∑ _x ∈ E \ I, (maxL - 1) := by
                apply Finset.sum_le_sum
                intro x hx
                have hx_ne : x ≠ v₀ := fun heq => (Finset.mem_sdiff.mp hx).2 (heq ▸ hv0I)
                exact hfiber_le_L_sub x hx hx_ne
            _ = (E \ I).card * (maxL - 1) := by simp
        have hIE_pos : 1 ≤ (I ∩ E).card :=
          Finset.card_pos.mpr ⟨v₀, Finset.mem_inter.mpr ⟨hv0I, hv0_in_E⟩⟩
        have hIE_le : (I ∩ E).card - 1 ≤ ((I ∩ E).card - 1) * (maxL - 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have hmul : ((I ∩ E).card - 1) * (maxL - 1) + (E \ I).card * (maxL - 1) ≤
            E.card * (maxL - 1) := by
          rw [← Nat.add_mul]
          apply Nat.mul_le_mul_right
          omega
        rw [hE_card] at hmul
        omega
      · have hv0_sdiff : v₀ ∈ E \ I := Finset.mem_sdiff.mpr ⟨hv0_in_E, hv0I⟩
        have hIO_le : (I ∩ O).card ≤ 1 + (E \ I).card * (maxL - 1) := by
          rw [hfiber_sum, ← Finset.add_sum_erase _ _ hv0_sdiff]
          have hrest : ∑ x ∈ (E \ I).erase v₀, ((I ∩ O).filter fun w => pred w = x).card ≤
              ((E \ I).erase v₀).card * (maxL - 1) := by
            calc ∑ x ∈ (E \ I).erase v₀, ((I ∩ O).filter fun w => pred w = x).card
                ≤ ∑ _x ∈ (E \ I).erase v₀, (maxL - 1) := by
                  apply Finset.sum_le_sum
                  intro x hx
                  have hx_ne : x ≠ v₀ := (Finset.mem_erase.mp hx).1
                  have hx_mem : x ∈ E \ I := (Finset.mem_erase.mp hx).2
                  exact hfiber_le_L_sub x hx_mem hx_ne
              _ = ((E \ I).erase v₀).card * (maxL - 1) := by simp
          have hv0_bound := hfiber_le_L v₀ hv0_sdiff
          have herase_card : ((E \ I).erase v₀).card = (E \ I).card - 1 :=
            Finset.card_erase_of_mem hv0_sdiff
          have hsdiff_pos : 1 ≤ (E \ I).card := Finset.card_pos.mpr ⟨v₀, hv0_sdiff⟩
          rw [herase_card] at hrest
          have hmul : 1 + (maxL - 1) + ((E \ I).card - 1) * (maxL - 1) =
              1 + (E \ I).card * (maxL - 1) := by
            have h1 : 1 + ((E \ I).card - 1) = (E \ I).card := by omega
            calc 1 + (maxL - 1) + ((E \ I).card - 1) * (maxL - 1)
                = 1 + (1 * (maxL - 1) + ((E \ I).card - 1) * (maxL - 1)) := by ring
              _ = 1 + (1 + ((E \ I).card - 1)) * (maxL - 1) := by rw [← Nat.add_mul]
              _ = 1 + (E \ I).card * (maxL - 1) := by rw [h1]
          omega
        have hIE_le : (I ∩ E).card ≤ (I ∩ E).card * (maxL - 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have hmul : (I ∩ E).card * (maxL - 1) + (E \ I).card * (maxL - 1) =
            E.card * (maxL - 1) := by
          rw [← Nat.add_mul, hE_split]
        rw [hE_card] at hmul
        omega
  rw [← hI_card]
  have hcast : ((I.card : ℕ) : ℝ) ≤ ((1 + minDistEven * (maxL - 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  push_cast [Nat.cast_sub hL_pos] at hcast
  exact hcast
