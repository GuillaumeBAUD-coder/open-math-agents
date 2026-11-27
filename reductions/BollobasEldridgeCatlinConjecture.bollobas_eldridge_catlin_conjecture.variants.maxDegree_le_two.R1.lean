import FormalConjectures.Paper.BollobasEldridgeCatlinConjecture

-- Reduction BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two.R1 of Maximum degree two (Aigner–Brandt 1993).
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- H1: triangle factors (Corradi-Hajnal case): a disjoint union of triangles and isolated vertices packs with G2
--     when 3 * (maxDegree G2 + 1) <= card V + 1. (Follows from the Hajnal-Szemeredi theorem.)
-- H2: the cycle-closing step of the induction on the number of edges of G1 (see its statement).
-- Everything else (Sauer-Spencer, leaf step, reduction to unions of cycles, relocation, Posa rotation) is proved below.

open SimpleGraph BollobasEldridgeCatlinConjecture

namespace OMA

variable {V : Type} [Fintype V] [DecidableEq V]

lemma mem_conf (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (σ : Equiv.Perm V) (x y : V) :
    (x, y) ∈ (Finset.univ.filter (fun p : V × V => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2))) ↔ G₁.Adj x y ∧ G₂.Adj (σ x) (σ y) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma step (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V)
    (σ : Equiv.Perm V) (u v : V) (h1 : G₁.Adj u v) (h2 : G₂.Adj (σ u) (σ v)) :
    ∃ τ : Equiv.Perm V, ((Finset.univ.filter (fun p : V × V => G₁.Adj p.1 p.2 ∧ G₂.Adj (τ p.1) (τ p.2)))).card < ((Finset.univ.filter (fun p : V × V => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2)))).card := by
  classical
  set B₁ : Finset V := (G₁.neighborFinset u).biUnion
    (fun u' => (G₂.neighborFinset (σ u')).image σ.symm) with hB₁
  set B₂ : Finset V := (G₂.neighborFinset (σ u)).biUnion
    (fun a => G₁.neighborFinset (σ.symm a)) with hB₂
  have hc1 : B₁.card ≤ G₁.maxDegree * G₂.maxDegree := by
    calc B₁.card ≤ ∑ u' ∈ G₁.neighborFinset u,
          ((G₂.neighborFinset (σ u')).image σ.symm).card := Finset.card_biUnion_le
      _ ≤ ∑ u' ∈ G₁.neighborFinset u, G₂.maxDegree := by
          apply Finset.sum_le_sum
          intro x _
          calc ((G₂.neighborFinset (σ x)).image σ.symm).card
              ≤ (G₂.neighborFinset (σ x)).card := Finset.card_image_le
            _ = G₂.degree (σ x) := G₂.card_neighborFinset_eq_degree _
            _ ≤ G₂.maxDegree := G₂.degree_le_maxDegree _
      _ = (G₁.neighborFinset u).card * G₂.maxDegree := by simp
      _ ≤ G₁.maxDegree * G₂.maxDegree := by
          apply Nat.mul_le_mul_right
          rw [G₁.card_neighborFinset_eq_degree]
          exact G₁.degree_le_maxDegree u
  have hc2 : B₂.card ≤ G₁.maxDegree * G₂.maxDegree := by
    calc B₂.card ≤ ∑ a ∈ G₂.neighborFinset (σ u),
          (G₁.neighborFinset (σ.symm a)).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ G₂.neighborFinset (σ u), G₁.maxDegree := by
          apply Finset.sum_le_sum
          intro x _
          rw [G₁.card_neighborFinset_eq_degree]
          exact G₁.degree_le_maxDegree _
      _ = (G₂.neighborFinset (σ u)).card * G₁.maxDegree := by simp
      _ ≤ G₂.maxDegree * G₁.maxDegree := by
          apply Nat.mul_le_mul_right
          rw [G₂.card_neighborFinset_eq_degree]
          exact G₂.degree_le_maxDegree _
      _ = G₁.maxDegree * G₂.maxDegree := Nat.mul_comm _ _
  have hu1 : u ∈ B₁ := by
    simp only [hB₁, Finset.mem_biUnion, Finset.mem_image, mem_neighborFinset]
    exact ⟨v, h1, σ u, h2.symm, by simp⟩
  have hu2 : u ∈ B₂ := by
    simp only [hB₂, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ v, h2, by simpa using h1.symm⟩
  have hcard : (insert v (B₁ ∪ B₂)).card < Fintype.card V := by
    have h3 : (B₁ ∪ B₂).card + (B₁ ∩ B₂).card = B₁.card + B₂.card :=
      Finset.card_union_add_card_inter _ _
    have h4 : 0 < (B₁ ∩ B₂).card :=
      Finset.card_pos.mpr ⟨u, Finset.mem_inter.mpr ⟨hu1, hu2⟩⟩
    have h5 : (insert v (B₁ ∪ B₂)).card ≤ (B₁ ∪ B₂).card + 1 := Finset.card_insert_le _ _
    have h6 : 2 * G₁.maxDegree * G₂.maxDegree
        = G₁.maxDegree * G₂.maxDegree + G₁.maxDegree * G₂.maxDegree := by ring
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ insert v (B₁ ∪ B₂) := by
    by_contra hcon
    have hcon : ∀ w, w ∈ insert v (B₁ ∪ B₂) := fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩
    have hall : insert v (B₁ ∪ B₂) = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [hall, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hw
  obtain ⟨hwv, hw1, hw2⟩ := hw
  have hwu : w ≠ u := fun e => hw1 (e ▸ hu1)
  have hw1' : ∀ y, G₁.Adj u y → ¬ G₂.Adj (σ y) (σ w) := by
    intro y hy hadj
    apply hw1
    simp only [hB₁, Finset.mem_biUnion, Finset.mem_image, mem_neighborFinset]
    exact ⟨y, hy, σ w, hadj, by simp⟩
  have hw2' : ∀ y, G₁.Adj w y → ¬ G₂.Adj (σ u) (σ y) := by
    intro y hy hadj
    apply hw2
    simp only [hB₂, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ y, hadj, by simpa using hy.symm⟩
  have hvu : v ≠ u := fun e => h1.ne e.symm
  have hvw : v ≠ w := fun e => hwv e.symm
  refine ⟨(Equiv.swap u w).trans σ, ?_⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(u, v), (mem_conf G₁ G₂ σ u v).2 ⟨h1, h2⟩, ?_⟩
    rw [mem_conf]
    rintro ⟨_, hadj⟩
    simp only [Equiv.trans_apply] at hadj
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hvu hvw] at hadj
    exact hw1' v h1 hadj.symm
  · intro p hp
    obtain ⟨x, y⟩ := p
    rw [mem_conf] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨hp1, ?_⟩
    simp only [Equiv.trans_apply] at hp2
    by_cases hxu : x = u
    · rw [hxu] at hp1 hp2 ⊢
      rw [Equiv.swap_apply_left] at hp2
      by_cases hyw : y = w
      · rw [hyw] at hp2 ⊢
        rw [Equiv.swap_apply_right] at hp2
        exact hp2.symm
      · have hyu : y ≠ u := fun e => hp1.ne e.symm
        rw [Equiv.swap_apply_of_ne_of_ne hyu hyw] at hp2
        exact absurd hp2.symm (hw1' y hp1)
    · by_cases hxw : x = w
      · rw [hxw] at hp1 hp2 ⊢
        rw [Equiv.swap_apply_right] at hp2
        by_cases hyu : y = u
        · rw [hyu] at hp2 ⊢
          rw [Equiv.swap_apply_left] at hp2
          exact hp2.symm
        · have hyw : y ≠ w := fun e => hp1.ne e.symm
          rw [Equiv.swap_apply_of_ne_of_ne hyu hyw] at hp2
          exact absurd hp2 (hw2' y hp1)
      · rw [Equiv.swap_apply_of_ne_of_ne hxu hxw] at hp2
        by_cases hyu : y = u
        · rw [hyu] at hp1 hp2
          rw [Equiv.swap_apply_left] at hp2
          exact absurd hp2 (hw1' x hp1.symm)
        · by_cases hyw : y = w
          · rw [hyw] at hp1 hp2
            rw [Equiv.swap_apply_right] at hp2
            exact absurd hp2.symm (hw2' x hp1.symm)
          · rw [Equiv.swap_apply_of_ne_of_ne hyu hyw] at hp2
            exact hp2

lemma sauer_spencer (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) : Packs G₁ G₂ := by
  have key : ∀ n : ℕ, ∀ σ : Equiv.Perm V, ((Finset.univ.filter (fun p : V × V => G₁.Adj p.1 p.2 ∧ G₂.Adj (σ p.1) (σ p.2)))).card = n → Packs G₁ G₂ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ hσ
      by_cases hex : ∃ u v, G₁.Adj u v ∧ G₂.Adj (σ u) (σ v)
      · obtain ⟨u, v, h1, h2⟩ := hex
        obtain ⟨τ, hτ⟩ := step G₁ G₂ h σ u v h1 h2
        exact ih _ (hσ ▸ hτ) τ rfl
      · exact ⟨σ, fun u v huv h2 => hex ⟨u, v, huv, h2⟩⟩
  exact key _ 1 rfl

/-- Adding a pendant edge: if `x` has `y` as its only neighbour in `G₁` and a placement is
conflict-free on all edges of `G₁` avoiding `x`, then `G₁` packs with `G₂`. -/
lemma leaf_step (G₁ G₂ : SimpleGraph V) [DecidableRel G₂.Adj]
    (hdeg : ∀ v a b c, G₁.Adj v a → G₁.Adj v b → G₁.Adj v c → a = b ∨ a = c ∨ b = c)
    (hn : 3 * G₂.maxDegree < Fintype.card V)
    (x y : V) (hxy : G₁.Adj x y) (hleaf : ∀ z, G₁.Adj x z → z = y)
    (σ : Equiv.Perm V)
    (hσ : ∀ u v, G₁.Adj u v → u ≠ x → v ≠ x → ¬ G₂.Adj (σ u) (σ v)) :
    Packs G₁ G₂ := by
  classical
  by_cases hc : G₂.Adj (σ x) (σ y)
  swap
  · refine ⟨σ, fun u v huv hadj => ?_⟩
    by_cases hux : u = x
    · rw [hux] at huv hadj
      have hvy : v = y := hleaf v huv
      rw [hvy] at hadj
      exact hc hadj
    · by_cases hvx : v = x
      · rw [hvx] at huv hadj
        have huy : u = y := hleaf u huv.symm
        rw [huy] at hadj
        exact hc hadj.symm
      · exact hσ u v huv hux hvx hadj
  have hdeg2 : ∀ b, (G₁.neighborFinset b).card ≤ 2 := by
    intro b
    by_contra hlt
    have hlt' : 2 < (G₁.neighborFinset b).card := by omega
    obtain ⟨a, ha, c, hc', d, hd, hac, had, hcd⟩ := Finset.two_lt_card.mp hlt'
    rw [mem_neighborFinset] at ha hc' hd
    rcases hdeg b a c d ha hc' hd with h | h | h
    · exact hac h
    · exact had h
    · exact hcd h
  set T : Finset V := (G₂.neighborFinset (σ y)).image σ.symm with hT
  set U : Finset V := (G₂.neighborFinset (σ x)).biUnion
    (fun a => G₁.neighborFinset (σ.symm a)) with hU
  have hcT : T.card ≤ G₂.maxDegree := by
    calc T.card ≤ (G₂.neighborFinset (σ y)).card := Finset.card_image_le
      _ = G₂.degree (σ y) := G₂.card_neighborFinset_eq_degree _
      _ ≤ G₂.maxDegree := G₂.degree_le_maxDegree _
  have hcU : U.card ≤ 2 * G₂.maxDegree := by
    calc U.card ≤ ∑ a ∈ G₂.neighborFinset (σ x), (G₁.neighborFinset (σ.symm a)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ a ∈ G₂.neighborFinset (σ x), 2 := Finset.sum_le_sum (fun a _ => hdeg2 _)
      _ = (G₂.neighborFinset (σ x)).card * 2 := by simp
      _ ≤ G₂.maxDegree * 2 := by
          apply Nat.mul_le_mul_right
          rw [G₂.card_neighborFinset_eq_degree]
          exact G₂.degree_le_maxDegree _
      _ = 2 * G₂.maxDegree := Nat.mul_comm _ _
  have hxT : x ∈ T := by
    simp only [hT, Finset.mem_image, mem_neighborFinset]
    exact ⟨σ x, hc.symm, by simp⟩
  have hxU : x ∈ U := by
    simp only [hU, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ y, hc, by simpa using hxy.symm⟩
  have hcard : (insert y (T ∪ U)).card < Fintype.card V := by
    have h3 : (T ∪ U).card + (T ∩ U).card = T.card + U.card :=
      Finset.card_union_add_card_inter _ _
    have h4 : 0 < (T ∩ U).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxT, hxU⟩⟩
    have h5 : (insert y (T ∪ U)).card ≤ (T ∪ U).card + 1 := Finset.card_insert_le _ _
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ insert y (T ∪ U) := by
    by_contra hcon
    have hcon' : ∀ w, w ∈ insert y (T ∪ U) := fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩
    have hall : insert y (T ∪ U) = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon'
    rw [hall, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hw
  obtain ⟨hwy, hwT, hwU⟩ := hw
  have hwx : w ≠ x := fun e => hwT (e ▸ hxT)
  have hT' : ¬ G₂.Adj (σ w) (σ y) := by
    intro hadj
    apply hwT
    simp only [hT, Finset.mem_image, mem_neighborFinset]
    exact ⟨σ w, hadj.symm, by simp⟩
  have hU' : ∀ b, G₁.Adj w b → ¬ G₂.Adj (σ x) (σ b) := by
    intro b hb hadj
    apply hwU
    simp only [hU, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ b, hadj, by simpa using hb.symm⟩
  have hyx : y ≠ x := fun e => hxy.ne e.symm
  have hyw : y ≠ w := fun e => hwy e.symm
  refine ⟨(Equiv.swap x w).trans σ, fun u v huv hadj => ?_⟩
  simp only [Equiv.trans_apply] at hadj
  by_cases hux : u = x
  · rw [hux] at huv hadj
    have hvy : v = y := hleaf v huv
    rw [hvy] at hadj
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyx hyw] at hadj
    exact hT' hadj
  · by_cases hvx : v = x
    · rw [hvx] at huv hadj
      have huy : u = y := hleaf u huv.symm
      rw [huy] at hadj
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyx hyw] at hadj
      exact hT' hadj.symm
    · by_cases huw : u = w
      · rw [huw] at huv hadj
        have hvw : v ≠ w := fun e => huv.ne e.symm
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hvx hvw] at hadj
        exact hU' v huv hadj
      · by_cases hvw : v = w
        · rw [hvw] at huv hadj
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hux huw] at hadj
          exact hU' u huv.symm hadj.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hux huw,
            Equiv.swap_apply_of_ne_of_ne hvx hvw] at hadj
          exact hσ u v huv hux hvx hadj

/-- Induction on the number of edges: pendant edges can always be added, so everything reduces
to graphs in which every non-isolated vertex has exactly two neighbours (unions of cycles). -/
lemma reduce_to_cycles (G₂ : SimpleGraph V) [DecidableRel G₂.Adj]
    (hn : 3 * G₂.maxDegree < Fintype.card V)
    (hcyc : ∀ G₁ : SimpleGraph V,
      (∀ v a b c, G₁.Adj v a → G₁.Adj v b → G₁.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ x y, G₁.Adj x y → ∃ z, z ≠ y ∧ G₁.Adj x z) →
      (∀ G' : SimpleGraph V,
        (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
        Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | G₁.Adj p.1 p.2} →
        Packs G' G₂) →
      Packs G₁ G₂) :
    ∀ m : ℕ, ∀ G₁ : SimpleGraph V,
      (∀ v a b c, G₁.Adj v a → G₁.Adj v b → G₁.Adj v c → a = b ∨ a = c ∨ b = c) →
      Set.ncard {p : V × V | G₁.Adj p.1 p.2} = m → Packs G₁ G₂ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G₁ hdeg hm
    by_cases hl : ∃ x y, G₁.Adj x y ∧ ∀ z, G₁.Adj x z → z = y
    · obtain ⟨x, y, hxy, hleaf⟩ := hl
      let G₁' : SimpleGraph V :=
        { Adj := fun a b => G₁.Adj a b ∧ a ≠ x ∧ b ≠ x
          symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
          loopless := ⟨fun a h => G₁.loopless.irrefl a h.1⟩ }
      have hdeg' : ∀ v a b c, G₁'.Adj v a → G₁'.Adj v b → G₁'.Adj v c →
          a = b ∨ a = c ∨ b = c :=
        fun v a b c ha hb hc => hdeg v a b c ha.1 hb.1 hc.1
      have hsub : {p : V × V | G₁'.Adj p.1 p.2} ⊆ {p : V × V | G₁.Adj p.1 p.2} :=
        fun p hp => hp.1
      have hss : {p : V × V | G₁'.Adj p.1 p.2} ⊂ {p : V × V | G₁.Adj p.1 p.2} :=
        (Set.ssubset_iff_of_subset hsub).2 ⟨(x, y), hxy, fun hp => hp.2.1 rfl⟩
      have hlt : Set.ncard {p : V × V | G₁'.Adj p.1 p.2} < m := by
        rw [← hm]
        exact Set.ncard_lt_ncard hss (Set.toFinite _)
      obtain ⟨σ, hσ⟩ := ih _ hlt G₁' hdeg' rfl
      exact leaf_step G₁ G₂ hdeg hn x y hxy hleaf σ
        (fun u v huv hux hvx => hσ u v ⟨huv, hux, hvx⟩)
    · refine hcyc G₁ hdeg ?_ ?_
      · intro x y hxy
        by_contra hno
        apply hl
        refine ⟨x, y, hxy, fun z hz => ?_⟩
        by_contra hzy
        exact hno ⟨z, hzy, hz⟩
      · intro G' hdeg' hlt
        exact ih _ (hm ▸ hlt) G' hdeg' rfl

/-- A placement whose only possible conflict is the edge `xy`, when that edge is fine. -/
lemma packs_of_almost (C G₂ : SimpleGraph V) (x y : V) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b))
    (hc : ¬ G₂.Adj (σ x) (σ y)) : Packs C G₂ := by
  refine ⟨σ, fun a b hab hadj => ?_⟩
  by_cases h1 : a = x ∧ b = y
  · rw [h1.1, h1.2] at hadj
    exact hc hadj
  · by_cases h2 : a = y ∧ b = x
    · rw [h2.1, h2.2] at hadj
      exact hc hadj.symm
    · exact hσ a b hab h1 h2 hadj

/-- Relocating the endpoint `x` of the conflicting edge `xy`: when `3 * maxDegree G₂ + 1 < card V`
there is always another vertex `w` such that exchanging `x` and `w` keeps every other edge
conflict-free. So either `C` packs, or the new position of `x` is again adjacent to that of `y`. -/
lemma relocate (C G₂ : SimpleGraph V) [DecidableRel G₂.Adj]
    (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hn : 3 * G₂.maxDegree + 1 < Fintype.card V)
    (x y : V) (hxy : C.Adj x y) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b))
    (hc : G₂.Adj (σ x) (σ y)) :
    Packs C G₂ ∨ ∃ w, w ≠ x ∧ w ≠ y ∧ G₂.Adj (σ w) (σ y) ∧
      ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G₂.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b)) := by
  classical
  have hdeg2 : ∀ b, (C.neighborFinset b).card ≤ 2 := by
    intro b
    by_contra hlt
    have hlt' : 2 < (C.neighborFinset b).card := by omega
    obtain ⟨a, ha, c, hc', d, hd, hac, had, hcd⟩ := Finset.two_lt_card.mp hlt'
    rw [mem_neighborFinset] at ha hc' hd
    rcases hC2 b a c d ha hc' hd with h | h | h
    · exact hac h
    · exact had h
    · exact hcd h
  set T : Finset V := ((C.neighborFinset x).erase y).biUnion
    (fun z => (G₂.neighborFinset (σ z)).image σ.symm) with hT
  set U : Finset V := (G₂.neighborFinset (σ x)).biUnion
    (fun a => C.neighborFinset (σ.symm a)) with hU
  have hcT : T.card ≤ G₂.maxDegree := by
    have h1 : ((C.neighborFinset x).erase y).card ≤ 1 := by
      have hy : y ∈ C.neighborFinset x := (C.mem_neighborFinset x y).2 hxy
      rw [Finset.card_erase_of_mem hy]
      have := hdeg2 x
      omega
    calc T.card ≤ ∑ z ∈ (C.neighborFinset x).erase y,
          ((G₂.neighborFinset (σ z)).image σ.symm).card := Finset.card_biUnion_le
      _ ≤ ∑ z ∈ (C.neighborFinset x).erase y, G₂.maxDegree := by
          apply Finset.sum_le_sum
          intro z _
          calc ((G₂.neighborFinset (σ z)).image σ.symm).card
              ≤ (G₂.neighborFinset (σ z)).card := Finset.card_image_le
            _ = G₂.degree (σ z) := G₂.card_neighborFinset_eq_degree _
            _ ≤ G₂.maxDegree := G₂.degree_le_maxDegree _
      _ = ((C.neighborFinset x).erase y).card * G₂.maxDegree := by simp
      _ ≤ 1 * G₂.maxDegree := Nat.mul_le_mul_right _ h1
      _ = G₂.maxDegree := Nat.one_mul _
  have hcU : U.card ≤ 2 * G₂.maxDegree := by
    calc U.card ≤ ∑ a ∈ G₂.neighborFinset (σ x), (C.neighborFinset (σ.symm a)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ a ∈ G₂.neighborFinset (σ x), 2 := Finset.sum_le_sum (fun a _ => hdeg2 _)
      _ = (G₂.neighborFinset (σ x)).card * 2 := by simp
      _ ≤ G₂.maxDegree * 2 := by
          apply Nat.mul_le_mul_right
          rw [G₂.card_neighborFinset_eq_degree]
          exact G₂.degree_le_maxDegree _
      _ = 2 * G₂.maxDegree := Nat.mul_comm _ _
  have hxU : x ∈ U := by
    simp only [hU, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ y, hc, by simpa using hxy.symm⟩
  have hcard : (insert y (T ∪ U)).card < Fintype.card V := by
    have h3 : (T ∪ U).card ≤ T.card + U.card := Finset.card_union_le _ _
    have h5 : (insert y (T ∪ U)).card ≤ (T ∪ U).card + 1 := Finset.card_insert_le _ _
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ insert y (T ∪ U) := by
    by_contra hcon
    have hcon' : ∀ w, w ∈ insert y (T ∪ U) := fun w => by
      by_contra hw
      exact hcon ⟨w, hw⟩
    have hall : insert y (T ∪ U) = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon'
    rw [hall, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  simp only [Finset.mem_insert, Finset.mem_union, not_or] at hw
  obtain ⟨hwy, hwT, hwU⟩ := hw
  have hwx : w ≠ x := fun e => hwU (e ▸ hxU)
  have hT' : ∀ z, C.Adj x z → z ≠ y → ¬ G₂.Adj (σ w) (σ z) := by
    intro z hz hzy hadj
    apply hwT
    simp only [hT, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_image, mem_neighborFinset]
    exact ⟨z, ⟨hzy, hz⟩, σ w, hadj.symm, by simp⟩
  have hU' : ∀ b, C.Adj w b → ¬ G₂.Adj (σ x) (σ b) := by
    intro b hb hadj
    apply hwU
    simp only [hU, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨σ b, hadj, by simpa using hb.symm⟩
  have hyx : y ≠ x := fun e => hxy.ne e.symm
  have hyw : y ≠ w := fun e => hwy e.symm
  have key : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
      ¬ G₂.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b)) := by
    intro a b hab h1 h2 hadj
    by_cases hax : a = x
    · have hby : b ≠ y := fun e => h1 ⟨hax, e⟩
      rw [hax] at hab hadj
      rw [Equiv.swap_apply_left] at hadj
      by_cases hbw : b = w
      · rw [hbw] at hab hadj
        rw [Equiv.swap_apply_right] at hadj
        exact hσ x w hab (fun e => hwy e.2) (fun e => hyx e.1.symm) hadj.symm
      · have hbx : b ≠ x := fun e => hab.ne e.symm
        rw [Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
        exact hT' b hab hby hadj
    · by_cases hbx : b = x
      · have hay : a ≠ y := fun e => h2 ⟨e, hbx⟩
        rw [hbx] at hab hadj
        rw [Equiv.swap_apply_left] at hadj
        by_cases haw : a = w
        · rw [haw] at hab hadj
          rw [Equiv.swap_apply_right] at hadj
          exact hσ x w hab.symm (fun e => hwy e.2) (fun e => hyx e.1.symm) hadj
        · rw [Equiv.swap_apply_of_ne_of_ne hax haw] at hadj
          exact hT' a hab.symm hay hadj.symm
      · by_cases haw : a = w
        · rw [haw] at hab hadj
          have hbw : b ≠ w := fun e => hab.ne e.symm
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
          exact hU' b hab hadj
        · by_cases hbw : b = w
          · rw [hbw] at hab hadj
            rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hax haw] at hadj
            exact hU' a hab.symm hadj.symm
          · rw [Equiv.swap_apply_of_ne_of_ne hax haw,
              Equiv.swap_apply_of_ne_of_ne hbx hbw] at hadj
            exact hσ a b hab h1 h2 hadj
  by_cases hres : G₂.Adj (σ w) (σ y)
  · exact Or.inr ⟨w, hwx, hwy, hres, key⟩
  · left
    refine packs_of_almost C G₂ x y ((Equiv.swap x w).trans σ) ?_ ?_
    · intro a b hab h1 h2
      simp only [Equiv.trans_apply]
      exact key a b hab h1 h2
    · simp only [Equiv.trans_apply]
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyx hyw]
      exact hres

/-- Double relocation: if `x` can be moved to `w` and `y` can be moved to `w'` (each keeping all
other edges conflict-free, each without repairing the edge `xy`), then either `C` packs or the
two new positions are again adjacent in `G₂`. -/
lemma double_relocate (C G₂ : SimpleGraph V) (x y w w' : V) (σ : Equiv.Perm V)
    (hxy : C.Adj x y) (hwx : w ≠ x) (hwy : w ≠ y) (hw'x : w' ≠ x) (hw'y : w' ≠ y) (hww' : w ≠ w')
    (hc : G₂.Adj (σ x) (σ y)) (hw' : G₂.Adj (σ w') (σ x))
    (h1 : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
      ¬ G₂.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b)))
    (h2 : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
      ¬ G₂.Adj (σ (Equiv.swap y w' a)) (σ (Equiv.swap y w' b)))
    (hno : ¬ G₂.Adj (σ w) (σ w')) : Packs C G₂ := by
  have hyx : y ≠ x := fun e => hxy.ne e.symm
  have hxy' : x ≠ y := fun e => hyx e.symm
  have hyw : y ≠ w := fun e => hwy e.symm
  have hxw' : x ≠ w' := fun e => hw'x e.symm
  have hw'w : w' ≠ w := fun e => hww' e.symm
  have E1 : C.Adj w y → False := fun h =>
    h1 w y h (fun e => hwx e.1) (fun e => hwy e.1)
      (by rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyx hyw]; exact hc)
  have E2 : C.Adj x w' → False := fun h =>
    h2 x w' h (fun e => hw'y e.2) (fun e => hyx e.1.symm)
      (by rw [Equiv.swap_apply_of_ne_of_ne hxy' hxw', Equiv.swap_apply_right]; exact hc)
  have E3 : C.Adj w w' → False := fun h =>
    h1 w w' h (fun e => hwx e.1) (fun e => hwy e.1)
      (by rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hw'x hw'w]; exact hw'.symm)
  have hfix : ∀ v, v ≠ x → v ≠ w →
      Equiv.swap x w (Equiv.swap y w' v) = Equiv.swap y w' v := by
    intro v hvx hvw
    by_cases hvy : v = y
    · rw [hvy, Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne hw'x hw'w
    · by_cases hvw' : v = w'
      · rw [hvw', Equiv.swap_apply_right]
        exact Equiv.swap_apply_of_ne_of_ne hyx hyw
      · rw [Equiv.swap_apply_of_ne_of_ne hvy hvw']
        exact Equiv.swap_apply_of_ne_of_ne hvx hvw
  refine packs_of_almost C G₂ x y (((Equiv.swap y w').trans (Equiv.swap x w)).trans σ) ?_ ?_
  · intro a b hab hn1 hn2 hadj
    simp only [Equiv.trans_apply] at hadj
    by_cases ha : a = y ∨ a = w'
    · by_cases hb : b = x ∨ b = w
      · rcases ha with ha1 | ha1
        · rcases hb with hb1 | hb1
          · exact hn2 ⟨ha1, hb1⟩
          · rw [ha1, hb1] at hab
            exact E1 hab.symm
        · rcases hb with hb1 | hb1
          · rw [ha1, hb1] at hab
            exact E2 hab.symm
          · rw [ha1, hb1] at hab
            exact E3 hab.symm
      · simp only [not_or] at hb
        have hax : a ≠ x := by
          rcases ha with h | h
          · rw [h]; exact hyx
          · rw [h]; exact hw'x
        have haw : a ≠ w := by
          rcases ha with h | h
          · rw [h]; exact hyw
          · rw [h]; exact hw'w
        rw [hfix a hax haw, hfix b hb.1 hb.2] at hadj
        exact h2 a b hab hn1 hn2 hadj
    · simp only [not_or] at ha
      by_cases hb : b = y ∨ b = w'
      · by_cases ha' : a = x ∨ a = w
        · rcases ha' with ha1 | ha1
          · rcases hb with hb1 | hb1
            · exact hn1 ⟨ha1, hb1⟩
            · rw [ha1, hb1] at hab
              exact E2 hab
          · rcases hb with hb1 | hb1
            · rw [ha1, hb1] at hab
              exact E1 hab
            · rw [ha1, hb1] at hab
              exact E3 hab
        · simp only [not_or] at ha'
          have hbx : b ≠ x := by
            rcases hb with h | h
            · rw [h]; exact hyx
            · rw [h]; exact hw'x
          have hbw : b ≠ w := by
            rcases hb with h | h
            · rw [h]; exact hyw
            · rw [h]; exact hw'w
          rw [hfix a ha'.1 ha'.2, hfix b hbx hbw] at hadj
          exact h2 a b hab hn1 hn2 hadj
      · simp only [not_or] at hb
        rw [Equiv.swap_apply_of_ne_of_ne ha.1 ha.2,
          Equiv.swap_apply_of_ne_of_ne hb.1 hb.2] at hadj
        exact h1 a b hab hn1 hn2 hadj
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hxy' hxw', Equiv.swap_apply_left, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hw'x hw'w]
    exact hno

/-- By the induction hypothesis, `C` minus one edge packs: a placement with at most one conflict. -/
lemma almost_packing (C G₂ : SimpleGraph V)
    (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hIH : ∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G₂)
    (x y : V) (hxy : C.Adj x y) :
    ∃ σ : Equiv.Perm V, ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
      ¬ G₂.Adj (σ a) (σ b) := by
  let G' : SimpleGraph V :=
    { Adj := fun a b => C.Adj a b ∧ ¬ (a = x ∧ b = y) ∧ ¬ (a = y ∧ b = x)
      symm := ⟨fun a b h => ⟨h.1.symm, fun e => h.2.2 ⟨e.2, e.1⟩, fun e => h.2.1 ⟨e.2, e.1⟩⟩⟩
      loopless := ⟨fun a h => C.loopless.irrefl a h.1⟩ }
  have hdeg' : ∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c :=
    fun v a b c ha hb hc => hC2 v a b c ha.1 hb.1 hc.1
  have hsub : {p : V × V | G'.Adj p.1 p.2} ⊆ {p : V × V | C.Adj p.1 p.2} := fun p hp => hp.1
  have hss : {p : V × V | G'.Adj p.1 p.2} ⊂ {p : V × V | C.Adj p.1 p.2} :=
    (Set.ssubset_iff_of_subset hsub).2 ⟨(x, y), hxy, fun hp => hp.2.1 ⟨rfl, rfl⟩⟩
  obtain ⟨σ, hσ⟩ := hIH G' hdeg' (Set.ncard_lt_ncard hss (Set.toFinite _))
  exact ⟨σ, fun a b hab h1 h2 => hσ a b ⟨hab, h1, h2⟩⟩

/-- Posa rotation: `p 0, ..., p L` lists the cycle through the conflicting edge `xy`, from `y` to
`x`. Reversing the segment `p (i+1), ..., p L` closes the cycle when `x ~ p i` and `y ~ p (i+1)`. -/
lemma rotate (C G₂ : SimpleGraph V) (x y : V) (σ : Equiv.Perm V) (p : ℕ → V) (L i : ℕ)
    (hinj : ∀ j k, j ≤ L → k ≤ L → p j = p k → j = k)
    (hp0 : p 0 = y) (hpL : p L = x)
    (hnb : ∀ j b, 1 ≤ j → j < L → C.Adj (p j) b → b = p (j - 1) ∨ b = p (j + 1))
    (hnbL : ∀ b, C.Adj x b → b = p (L - 1) ∨ b = y)
    (hpadj : ∀ j, j < L → C.Adj (p j) (p (j + 1)))
    (hi1 : 1 ≤ i) (hi2 : i + 2 ≤ L)
    (hσ : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b))
    (hx : ¬ G₂.Adj (σ x) (σ (p i))) (hy : ¬ G₂.Adj (σ y) (σ (p (i + 1)))) :
    Packs C G₂ := by
  classical
  let inS : V → Prop := fun v => ∃ j, i + 1 ≤ j ∧ j ≤ L ∧ p j = v
  let f : V → V := fun v => if h : inS v then p (L + i + 1 - Classical.choose h) else v
  have hf_seg : ∀ j, i + 1 ≤ j → j ≤ L → f (p j) = p (L + i + 1 - j) := by
    intro j hj1 hj2
    have h : inS (p j) := ⟨j, hj1, hj2, rfl⟩
    simp only [f, dif_pos h]
    obtain ⟨_, hc2, hc3⟩ := Classical.choose_spec h
    rw [hinj _ _ hc2 hj2 hc3]
  have hf_out : ∀ v, ¬ inS v → f v = v := by
    intro v hv
    simp only [f, dif_neg hv]
  have hinv : Function.Involutive f := by
    intro v
    by_cases hv : inS v
    · obtain ⟨j, hj1, hj2, rfl⟩ := hv
      rw [hf_seg j hj1 hj2, hf_seg (L + i + 1 - j) (by omega) (by omega)]
      congr 1
      omega
    · rw [hf_out v hv, hf_out v hv]
  have hne_x : ∀ m, m < L → p m ≠ x := fun m hm h => by
    have := hinj m L (by omega) le_rfl (h.trans hpL.symm)
    omega
  have hne_y : ∀ m, 1 ≤ m → m ≤ L → p m ≠ y := fun m hm1 hm2 h => by
    have := hinj m 0 hm2 (Nat.zero_le _) (h.trans hp0.symm)
    omega
  have hgood : ∀ m, 1 ≤ m → m < L → ¬ G₂.Adj (σ (p m)) (σ (p (m + 1))) := fun m h1 h2 =>
    hσ _ _ (hpadj m h2) (fun h => hne_x m h2 h.1) (fun h => hne_y m h1 (by omega) h.1)
  have hy_out : ¬ inS y := by
    rintro ⟨j, hj1, hj2, hj3⟩
    exact hne_y j (by omega) hj2 hj3
  have hpi_out : ¬ inS (p i) := by
    rintro ⟨j, hj1, hj2, hj3⟩
    have := hinj j i hj2 (by omega) hj3
    omega
  have hx_in : inS x := ⟨L, by omega, le_rfl, hpL⟩
  have hcase : ∀ a b, C.Adj a b → inS a → ¬ G₂.Adj (σ (f a)) (σ (f b)) := by
    intro a b hab ha
    obtain ⟨j, hj1, hj2, rfl⟩ := ha
    rcases Nat.lt_or_ge j L with hjL | hjL
    · rw [hf_seg j hj1 hj2]
      rcases hnb j b (by omega) hjL hab with hb | hb
      · rw [hb]
        by_cases hj' : i + 1 ≤ j - 1
        · rw [hf_seg (j - 1) hj' (by omega)]
          have e : L + i + 1 - (j - 1) = (L + i + 1 - j) + 1 := by omega
          rw [e]
          exact hgood _ (by omega) (by omega)
        · have e1 : j - 1 = i := by omega
          have e2 : L + i + 1 - j = L := by omega
          rw [e1, e2, hpL, hf_out _ hpi_out]
          exact hx
      · rw [hb, hf_seg (j + 1) (by omega) (by omega)]
        have e : L + i + 1 - j = (L + i + 1 - (j + 1)) + 1 := by omega
        rw [e]
        intro h
        exact hgood _ (by omega) (by omega) h.symm
    · have hj : j = L := le_antisymm hj2 hjL
      subst hj
      rw [hf_seg j hj1 hj2]
      have e0 : j + i + 1 - j = i + 1 := by omega
      rw [e0]
      rcases hnbL b (hpL ▸ hab) with hb | hb
      · rw [hb, hf_seg (j - 1) (by omega) (by omega)]
        have e : j + i + 1 - (j - 1) = (i + 1) + 1 := by omega
        rw [e]
        exact hgood _ (by omega) (by omega)
      · rw [hb, hf_out _ hy_out]
        intro h
        exact hy h.symm
  refine ⟨(Function.Involutive.toPerm f hinv).trans σ, fun a b hab => ?_⟩
  show ¬ G₂.Adj (σ (f a)) (σ (f b))
  by_cases ha : inS a
  · exact hcase a b hab ha
  · by_cases hb : inS b
    · intro h
      exact hcase b a hab.symm hb h.symm
    · rw [hf_out a ha, hf_out b hb]
      refine hσ a b hab ?_ ?_
      · rintro ⟨rfl, -⟩
        exact ha hx_in
      · rintro ⟨-, rfl⟩
        exact hb hx_in

/-- Choosing the rotation index by counting. -/
lemma find_index (G₂ : SimpleGraph V) [DecidableRel G₂.Adj] (x y : V) (σ : Equiv.Perm V)
    (p : ℕ → V) (L : ℕ)
    (hinj : ∀ j k, j ≤ L → k ≤ L → p j = p k → j = k)
    (hp0 : p 0 = y) (hpL : p L = x) (hc : G₂.Adj (σ x) (σ y))
    (hL : 2 * G₂.maxDegree + 1 ≤ L) :
    ∃ i, 1 ≤ i ∧ i + 2 ≤ L ∧ ¬ G₂.Adj (σ x) (σ (p i)) ∧ ¬ G₂.Adj (σ y) (σ (p (i + 1))) := by
  classical
  set I : Finset ℕ := Finset.Icc 1 (L - 2) with hI
  set A : Finset ℕ := I.filter (fun i => G₂.Adj (σ x) (σ (p i))) with hA
  set B : Finset ℕ := I.filter (fun i => G₂.Adj (σ y) (σ (p (i + 1)))) with hB
  have hdx : 1 ≤ G₂.degree (σ x) := by
    rw [← G₂.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨σ y, (G₂.mem_neighborFinset _ _).2 hc⟩
  have hΔ1 : 1 ≤ G₂.maxDegree := le_trans hdx (G₂.degree_le_maxDegree _)
  have hcA : A.card ≤ G₂.maxDegree - 1 := by
    have h1 : A.card ≤ ((G₂.neighborFinset (σ x)).erase (σ y)).card := by
      refine Finset.card_le_card_of_injOn (fun i => σ (p i)) ?_ ?_
      · intro i hi
        simp only [hA, hI, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, mem_neighborFinset,
          Set.mem_singleton_iff]
        refine ⟨hi.2, fun h => ?_⟩
        have h' : p i = p 0 := by rw [hp0]; exact σ.injective h
        have := hinj i 0 (by omega) (Nat.zero_le _) h'
        omega
      · intro i hi k hk hik
        simp only [hA, hI, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hi hk
        exact hinj i k (by omega) (by omega) (σ.injective hik)
    have h2 : ((G₂.neighborFinset (σ x)).erase (σ y)).card = G₂.degree (σ x) - 1 := by
      rw [Finset.card_erase_of_mem ((G₂.mem_neighborFinset _ _).2 hc),
        G₂.card_neighborFinset_eq_degree]
    have h3 := G₂.degree_le_maxDegree (σ x)
    omega
  have hcB : B.card ≤ G₂.maxDegree - 1 := by
    have hdy : 1 ≤ G₂.degree (σ y) := by
      rw [← G₂.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨σ x, (G₂.mem_neighborFinset _ _).2 hc.symm⟩
    have h1 : B.card ≤ ((G₂.neighborFinset (σ y)).erase (σ x)).card := by
      refine Finset.card_le_card_of_injOn (fun i => σ (p (i + 1))) ?_ ?_
      · intro i hi
        simp only [hB, hI, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hi
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, mem_neighborFinset,
          Set.mem_singleton_iff]
        refine ⟨hi.2, fun h => ?_⟩
        have h' : p (i + 1) = p L := by rw [hpL]; exact σ.injective h
        have := hinj (i + 1) L (by omega) le_rfl h'
        omega
      · intro i hi k hk hik
        simp only [hB, hI, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hi hk
        have := hinj (i + 1) (k + 1) (by omega) (by omega) (σ.injective hik)
        omega
    have h2 : ((G₂.neighborFinset (σ y)).erase (σ x)).card = G₂.degree (σ y) - 1 := by
      rw [Finset.card_erase_of_mem ((G₂.mem_neighborFinset _ _).2 hc.symm),
        G₂.card_neighborFinset_eq_degree]
    have h3 := G₂.degree_le_maxDegree (σ y)
    omega
  have hcI : I.card = L - 2 := by
    rw [hI, Nat.card_Icc]
    omega
  have hlt : (A ∪ B).card < I.card := by
    have := Finset.card_union_le A B
    omega
  obtain ⟨i, hiI, hiAB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hiI' := hiI
  simp only [hI, Finset.mem_Icc] at hiI'
  refine ⟨i, hiI'.1, by omega, fun h => hiAB ?_, fun h => hiAB ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hiI, h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hiI, h⟩)


/-- Handshake: a vertex of odd degree reaches some other vertex of odd degree. -/
lemma reach_of_odd (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (hy : Odd (G.degree y)) (hev : ∀ w, w ≠ x → w ≠ y → Even (G.degree w)) :
    G.Reachable y x := by
  classical
  by_contra hnr
  let K : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ G.Reachable y a
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.trans (SimpleGraph.Adj.reachable h.1)⟩⟩
      loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  letI hK : DecidableRel K.Adj := fun a b => Classical.propDecidable _
  have hKdeg : ∀ w, G.Reachable y w → K.degree w = G.degree w := by
    intro w hw
    rw [← K.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_neighborFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  have hKy : Odd (K.degree y) := by
    rw [hKdeg y (Reachable.refl _)]
    exact hy
  obtain ⟨w, hwy, hwodd⟩ := K.exists_ne_odd_degree_of_exists_odd_degree y hKy
  have hpos : 0 < (K.neighborFinset w).card := by
    rw [K.card_neighborFinset_eq_degree]
    exact hwodd.pos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  rw [mem_neighborFinset] at hb
  have hRw : G.Reachable y w := hb.2
  have hwx : w ≠ x := fun e => hnr (e ▸ hRw)
  rw [hKdeg w hRw] at hwodd
  exact (Nat.not_even_iff_odd.mpr hwodd) (hev w hwx hwy)

/-- In a union of cycles, deleting the edge `xy` leaves a path from `y` to `x` that runs through the
whole component of `y`. -/
lemma cycle_path (C : SimpleGraph V)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (x y : V) (hxy : C.Adj x y) :
    ∃ (p : ℕ → V) (L : ℕ), 2 ≤ L ∧ (∀ j k, j ≤ L → k ≤ L → p j = p k → j = k) ∧
      p 0 = y ∧ p L = x ∧ (∀ j, j < L → C.Adj (p j) (p (j + 1))) ∧
      (∀ u, C.Reachable y u → ∃ j, j ≤ L ∧ p j = u) ∧
      (∀ j b, 1 ≤ j → j < L → C.Adj (p j) b → b = p (j - 1) ∨ b = p (j + 1)) ∧
      (∀ b, C.Adj x b → b = p (L - 1) ∨ b = y) := by
  classical
  let C' : SimpleGraph V :=
    { Adj := fun a b => C.Adj a b ∧ ¬ (a = x ∧ b = y) ∧ ¬ (a = y ∧ b = x)
      symm := ⟨fun a b h => ⟨h.1.symm, fun e => h.2.2 ⟨e.2, e.1⟩, fun e => h.2.1 ⟨e.2, e.1⟩⟩⟩
      loopless := ⟨fun a h => C.loopless.irrefl a h.1⟩ }
  have hxy' : x ≠ y := hxy.ne
  have hdeg2 : ∀ v, (C.neighborFinset v).card ≤ 2 := by
    intro b
    by_contra hlt
    have hlt' : 2 < (C.neighborFinset b).card := by omega
    obtain ⟨a, ha, c, hc', d, hd, hac, had, hcd⟩ := Finset.two_lt_card.mp hlt'
    rw [mem_neighborFinset] at ha hc' hd
    rcases hdeg b a c d ha hc' hd with h | h | h
    · exact hac h
    · exact had h
    · exact hcd h
  have hreach : C'.Reachable y x := by
    obtain ⟨z, hzx, hyz⟩ := hnl y x hxy.symm
    refine reach_of_odd C' x y ?_ ?_
    · have hKy : C'.neighborFinset y = {z} := by
        ext b
        simp only [mem_neighborFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, _, h2⟩
          rcases hdeg y b x z hb hxy.symm hyz with h | h | h
          · exact absurd ⟨rfl, h⟩ h2
          · exact h
          · exact absurd h.symm hzx
        · rintro rfl
          exact ⟨hyz, fun h => hxy' h.1.symm, fun h => hzx h.2⟩
      rw [← C'.card_neighborFinset_eq_degree, hKy]
      simp
    · intro w hwx hwy
      have hKw : C'.neighborFinset w = C.neighborFinset w := by
        ext b
        simp only [mem_neighborFinset]
        constructor
        · exact fun h => h.1
        · intro h
          exact ⟨h, fun e => hwx e.1, fun e => hwy e.1⟩
      have hev : (C.neighborFinset w).card = 0 ∨ (C.neighborFinset w).card = 2 := by
        rcases Nat.eq_zero_or_pos (C.neighborFinset w).card with h | h
        · exact Or.inl h
        · right
          obtain ⟨b, hb⟩ := Finset.card_pos.mp h
          rw [mem_neighborFinset] at hb
          obtain ⟨c, hcb, hc⟩ := hnl w b hb
          have hsub : ({b, c} : Finset V) ⊆ C.neighborFinset w := by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact (C.mem_neighborFinset _ _).2 hb
            · exact (C.mem_neighborFinset _ _).2 hc
          have hcard : ({b, c} : Finset V).card = 2 := Finset.card_pair (Ne.symm hcb)
          have h2 : 2 ≤ (C.neighborFinset w).card := hcard ▸ Finset.card_le_card hsub
          have := hdeg2 w
          omega
      rw [← C'.card_neighborFinset_eq_degree, hKw]
      rcases hev with h | h <;> rw [h] <;> decide
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hL2 : 2 ≤ w.length := by
    by_contra hlt
    have h01 : w.length = 0 ∨ w.length = 1 := by omega
    rcases h01 with h | h
    · exact hxy' (Walk.eq_of_length_eq_zero h).symm
    · exact (Walk.adj_of_length_eq_one h).2.2 ⟨rfl, rfl⟩
  have hinj : ∀ j k, j ≤ w.length → k ≤ w.length → w.getVert j = w.getVert k → j = k :=
    fun j k hj hk hjk => hw.getVert_injOn hj hk hjk
  have hadj : ∀ j, j < w.length → C.Adj (w.getVert j) (w.getVert (j + 1)) :=
    fun j hj => (w.adj_getVert_succ hj).1
  have hnb : ∀ j b, 1 ≤ j → j < w.length → C.Adj (w.getVert j) b →
      b = w.getVert (j - 1) ∨ b = w.getVert (j + 1) := by
    intro j b hj1 hj2 hb
    have h1 : C.Adj (w.getVert j) (w.getVert (j - 1)) := by
      have := hadj (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      exact this.symm
    have h2 := hadj j hj2
    rcases hdeg _ b _ _ hb h1 h2 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := hinj _ _ (by omega) (by omega) h
      omega
  have hnbL : ∀ b, C.Adj x b → b = w.getVert (w.length - 1) ∨ b = y := by
    intro b hb
    have h1 : C.Adj x (w.getVert (w.length - 1)) := by
      have := hadj (w.length - 1) (by omega)
      rw [show w.length - 1 + 1 = w.length by omega, w.getVert_length] at this
      exact this.symm
    rcases hdeg x b _ y hb h1 hxy with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have h' : w.getVert (w.length - 1) = w.getVert 0 := by rw [w.getVert_zero]; exact h
      have := hinj _ _ (by omega) (by omega) h'
      omega
  have hnb0 : ∀ b, C.Adj y b → b = x ∨ b = w.getVert 1 := by
    intro b hb
    have h1 : C.Adj y (w.getVert 1) := by
      have := hadj 0 (by omega)
      rw [w.getVert_zero] at this
      exact this
    rcases hdeg y b x _ hb hxy.symm h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have h' : w.getVert w.length = w.getVert 1 := by rw [w.getVert_length]; exact h
      have := hinj _ _ le_rfl (by omega) h'
      omega
  have hcl : ∀ j b, j ≤ w.length → C.Adj (w.getVert j) b →
      ∃ k, k ≤ w.length ∧ w.getVert k = b := by
    intro j b hj hb
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [w.getVert_zero] at hb
      rcases hnb0 b hb with h | h
      · exact ⟨w.length, le_rfl, by rw [w.getVert_length, h]⟩
      · exact ⟨1, by omega, h.symm⟩
    · rcases Nat.lt_or_ge j w.length with hjL | hjL
      · rcases hnb j b h0 hjL hb with h | h
        · exact ⟨j - 1, by omega, h.symm⟩
        · exact ⟨j + 1, by omega, h.symm⟩
      · have hj' : j = w.length := le_antisymm hj hjL
        subst hj'
        rw [w.getVert_length] at hb
        rcases hnbL b hb with h | h
        · exact ⟨w.length - 1, by omega, h.symm⟩
        · exact ⟨0, Nat.zero_le _, by rw [w.getVert_zero, h]⟩
  refine ⟨fun j => w.getVert j, w.length, hL2, hinj, w.getVert_zero, w.getVert_length, hadj,
    ?_, hnb, hnbL⟩
  intro u hu
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu
  induction hu with
  | refl => exact ⟨0, Nat.zero_le _, w.getVert_zero⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk, hpk⟩ := ih
    have hpk' : w.getVert k = _ := hpk
    refine hcl k _ hk ?_
    rw [hpk']
    exact hbc

/-- Closing a long cycle: if the component of the conflicting edge has at least
`2 * maxDegree G₂ + 2` vertices, a rotation repairs the placement. -/
lemma long_cycle (C G₂ : SimpleGraph V) [DecidableRel G₂.Adj]
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (x y : V) (hxy : C.Adj x y) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b))
    (hlong : 2 * G₂.maxDegree + 2 ≤ Set.ncard {u | C.Reachable y u}) : Packs C G₂ := by
  classical
  by_cases hc : G₂.Adj (σ x) (σ y)
  swap
  · exact packs_of_almost C G₂ x y σ hσ hc
  obtain ⟨p, L, hL2, hinj, hp0, hpL, hpadj, hcov, hnb, hnbL⟩ := cycle_path C hdeg hnl x y hxy
  have hcard : Set.ncard {u | C.Reachable y u} ≤ L + 1 := by
    have hsub : {u | C.Reachable y u} ⊆ (((Finset.range (L + 1)).image p : Finset V) : Set V) := by
      intro u hu
      obtain ⟨j, hj, rfl⟩ := hcov u hu
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨j, by omega, rfl⟩
    calc Set.ncard {u | C.Reachable y u}
        ≤ Set.ncard (((Finset.range (L + 1)).image p : Finset V) : Set V) :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((Finset.range (L + 1)).image p).card := Set.ncard_coe_finset _
      _ ≤ (Finset.range (L + 1)).card := Finset.card_image_le
      _ = L + 1 := Finset.card_range _
  obtain ⟨i, hi1, hi2, hx, hy⟩ := find_index G₂ x y σ p L hinj hp0 hpL hc (by omega)
  exact rotate C G₂ x y σ p L i hinj hp0 hpL hnb hnbL hpadj hi1 hi2 hσ hx hy

/-- An isolated vertex `z` can take the place of the endpoint `x` of the conflicting edge `xy`. -/
lemma absorb (C G₂ : SimpleGraph V) (x y z : V) (σ : Equiv.Perm V) (hxy : C.Adj x y)
    (hz : ∀ b, ¬ C.Adj z b)
    (hσ : ∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b))
    (hzy : ¬ G₂.Adj (σ z) (σ y)) (hzb : ∀ b, C.Adj x b → b ≠ y → ¬ G₂.Adj (σ z) (σ b)) :
    Packs C G₂ := by
  have hx : ∀ b, C.Adj x b → ¬ G₂.Adj (σ z) (σ b) := by
    intro b hb
    by_cases hby : b = y
    · rw [hby]
      exact hzy
    · exact hzb b hb hby
  refine ⟨(Equiv.swap x z).trans σ, fun a b hab => ?_⟩
  simp only [Equiv.trans_apply]
  have haz : a ≠ z := fun e => hz b (e ▸ hab)
  have hbz : b ≠ z := fun e => hz a (e ▸ hab.symm)
  by_cases hax : a = x
  · rw [hax] at hab ⊢
    have hbx : b ≠ x := fun e => hab.ne e.symm
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbx hbz]
    exact hx b hab
  · by_cases hbx : b = x
    · rw [hbx] at hab ⊢
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hax haz]
      intro h
      exact hx a hab.symm h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hax haz, Equiv.swap_apply_of_ne_of_ne hbx hbz]
      exact hσ a b hab (fun h => hax h.1) (fun h => hbx h.2)

lemma tri_nbrs (C : SimpleGraph V)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (htri : ∀ x y, C.Adj x y → ∃ u, C.Adj x u ∧ C.Adj y u) (v a : V) (ha : C.Adj v a) :
    ∃ b, C.Adj v b ∧ C.Adj a b ∧ ∀ c, C.Adj v c ↔ c = a ∨ c = b := by
  obtain ⟨b, hvb, hab⟩ := htri v a ha
  refine ⟨b, hvb, hab, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · rcases hdeg v c a b hc ha hvb with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hab.ne
  · rcases hc with rfl | rfl
    · exact ha
    · exact hvb

lemma tri_eq_of_mem (C : SimpleGraph V) [DecidableRel C.Adj]
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (htri : ∀ x y, C.Adj x y → ∃ u, C.Adj x u ∧ C.Adj y u) (v w : V)
    (hw : w ∈ insert v (C.neighborFinset v)) :
    insert w (C.neighborFinset w) = insert v (C.neighborFinset v) := by
  rw [Finset.mem_insert, mem_neighborFinset] at hw
  rcases hw with rfl | hvw
  · rfl
  obtain ⟨b, hvb, hwb, hv⟩ := tri_nbrs C hdeg htri v w hvw
  obtain ⟨b', hwb', hvb', hw'⟩ := tri_nbrs C hdeg htri w v hvw.symm
  have hb' : b' = b := by
    rcases (hv b').1 hvb' with h | h
    · exact absurd h.symm hwb'.ne
    · exact h
  subst hb'
  ext x
  simp only [Finset.mem_insert, mem_neighborFinset, hv, hw']
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

lemma card_tri (C : SimpleGraph V) [DecidableRel C.Adj]
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (htri : ∀ x y, C.Adj x y → ∃ u, C.Adj x u ∧ C.Adj y u) (v a : V) (ha : C.Adj v a) :
    (insert v (C.neighborFinset v)).card = 3 := by
  obtain ⟨b, hvb, hab, hv⟩ := tri_nbrs C hdeg htri v a ha
  rw [Finset.card_eq_three]
  refine ⟨v, a, b, ha.ne, hvb.ne, hab.ne, ?_⟩
  ext x
  simp only [Finset.mem_insert, mem_neighborFinset, hv, Finset.mem_singleton]

lemma mem_NI_of_mem_tri (C : SimpleGraph V) [DecidableRel C.Adj] (v w : V) (hv : ∃ a, C.Adj v a)
    (hw : w ∈ insert v (C.neighborFinset v)) : ∃ a, C.Adj w a := by
  rw [Finset.mem_insert, mem_neighborFinset] at hw
  rcases hw with rfl | hvw
  · exact hv
  · exact ⟨v, hvw.symm⟩

/-- In an equitable colouring with the right number of colours, at least `n / 3` classes have at
least three vertices. -/
lemma big_classes (t : ℕ) (f : V → Fin t)
    (heq : ∀ c₁ c₂, (Finset.univ.filter (fun v => f v = c₁)).card ≤
      (Finset.univ.filter (fun v => f v = c₂)).card + 1)
    (ht : t = Fintype.card V / 3 ∨ Fintype.card V + 1 = 3 * t) :
    Fintype.card V / 3 ≤
      (Finset.univ.filter (fun c => 3 ≤ (Finset.univ.filter (fun v => f v = c)).card)).card := by
  classical
  set W : Fin t → Finset V := fun c => Finset.univ.filter (fun v => f v = c) with hW
  have hsum : Fintype.card V = ∑ c, (W c).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))
  set Big := Finset.univ.filter (fun c => 3 ≤ (W c).card) with hBig
  set Small := Finset.univ.filter (fun c => ¬ 3 ≤ (W c).card) with hSmall
  have hBS : Big.card + Small.card = t := by
    rw [hBig, hSmall, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  show Fintype.card V / 3 ≤ Big.card
  by_cases hs : Small.card = 0
  · rcases ht with ht | ht <;> omega
  · obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hs)
    have hc₀' : (W c₀).card ≤ 2 := by
      simp only [hSmall, Finset.mem_filter, Finset.mem_univ, true_and] at hc₀
      omega
    have hall : ∀ c, (W c).card ≤ 3 := fun c => by
      have h := heq c c₀
      change (W c).card ≤ (W c₀).card + 1 at h
      omega
    have hsplit : ∑ c, (W c).card = ∑ c ∈ Big, (W c).card + ∑ c ∈ Small, (W c).card :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have h1 : ∑ c ∈ Big, (W c).card ≤ Big.card * 3 :=
      Finset.sum_le_card_nsmul _ _ _ (fun c _ => hall c)
    have h2 : ∑ c ∈ Small, (W c).card ≤ Small.card * 2 := by
      refine Finset.sum_le_card_nsmul _ _ _ (fun c hc => ?_)
      simp only [hSmall, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      omega
    rcases ht with ht | ht <;> omega

end OMA

namespace OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1

open OMA

/-- H1 -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (C G₂ : SimpleGraph V) [DecidableRel G₂.Adj],
    3 * (G₂.maxDegree + 1) ≤ Fintype.card V + 1 →
    (∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c) →
    (∀ x y, C.Adj x y → ∃ u, C.Adj x u ∧ C.Adj y u) →
    Packs C G₂

/-- H2 -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (C G₂ : SimpleGraph V) [DecidableRel G₂.Adj],
    3 * (G₂.maxDegree + 1) ≤ Fintype.card V + 1 →
    Fintype.card V ≤ 4 * G₂.maxDegree →
    (∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c) →
    (∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) →
    (∀ v, Set.ncard {u | C.Reachable v u} ≤ 2 * G₂.maxDegree + 1) →
    (∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G₂) →
    ∀ x y : V, C.Adj x y →
    (∀ u, ¬ (C.Adj x u ∧ C.Adj y u)) →
    ∀ σ : Equiv.Perm V,
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → ¬ G₂.Adj (σ a) (σ b)) →
      G₂.Adj (σ x) (σ y) →
      (∀ z, (∀ b, ¬ C.Adj z b) → G₂.Adj (σ z) (σ y) ∨ ∃ b, C.Adj x b ∧ b ≠ y ∧ G₂.Adj (σ z) (σ b)) →
      (∀ z, (∀ b, ¬ C.Adj z b) → G₂.Adj (σ z) (σ x) ∨ ∃ b, C.Adj y b ∧ b ≠ x ∧ G₂.Adj (σ z) (σ b)) →
    ∀ w w' : V, w ≠ x → w ≠ y → w' ≠ x → w' ≠ y →
      G₂.Adj (σ w) (σ y) → G₂.Adj (σ w') (σ x) →
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G₂.Adj (σ (Equiv.swap x w a)) (σ (Equiv.swap x w b))) →
      (∀ a b, C.Adj a b → ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) →
        ¬ G₂.Adj (σ (Equiv.swap y w' a)) (σ (Equiv.swap y w' b))) →
      (w ≠ w' → G₂.Adj (σ w) (σ w')) →
      Packs C G₂

theorem solution_of_H (htf : H1) (hstep : H2)
    {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2)
    (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) : Packs G₁ G₂ := by
  by_cases h0 : G₁.maxDegree = 0
  · exact (bollobas_eldridge_catlin_conjecture.variants.edgeless G₂ G₁ h0).symm
  by_cases h1 : G₁.maxDegree = 1
  · apply sauer_spencer
    rw [h1] at h ⊢
    omega
  have h2 : G₁.maxDegree = 2 := by omega
  by_cases h3 : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V
  · exact sauer_spencer G₁ G₂ h3
  rw [h2] at h h3
  have hn : 3 * G₂.maxDegree < Fintype.card V := by omega
  have hdeg : ∀ v a b c, G₁.Adj v a → G₁.Adj v b → G₁.Adj v c → a = b ∨ a = c ∨ b = c := by
    intro v a b c ha hb hc
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hab, hac, hbc⟩ := hne
    have hlt : 2 < (G₁.neighborFinset v).card :=
      Finset.two_lt_card.mpr ⟨a, (G₁.mem_neighborFinset v a).2 ha, b,
        (G₁.mem_neighborFinset v b).2 hb, c, (G₁.mem_neighborFinset v c).2 hc, hab, hac, hbc⟩
    rw [G₁.card_neighborFinset_eq_degree] at hlt
    have := G₁.degree_le_maxDegree v
    omega
  refine reduce_to_cycles G₂ hn ?_ _ G₁ hdeg rfl
  intro C hC2 hCnoleaf hIH
  by_cases hlong : ∃ v, 2 * G₂.maxDegree + 2 ≤ Set.ncard {u | C.Reachable v u}
  · obtain ⟨v, hv⟩ := hlong
    obtain ⟨x, hxv⟩ : ∃ x, C.Adj x v := by
      by_contra hno
      have hsub : {u | C.Reachable v u} ⊆ {v} := by
        intro u hu
        obtain ⟨w⟩ := hu
        cases w with
        | nil => exact Set.mem_singleton _
        | cons h _ => exact absurd ⟨_, h.symm⟩ hno
      have h1 : Set.ncard {u | C.Reachable v u} ≤ 1 := by
        calc Set.ncard {u | C.Reachable v u} ≤ Set.ncard ({v} : Set V) :=
              Set.ncard_le_ncard hsub (Set.finite_singleton v)
          _ = 1 := Set.ncard_singleton v
      omega
    obtain ⟨σ, hσ⟩ := almost_packing C G₂ hC2 hIH x v hxv
    exact long_cycle C G₂ hC2 hCnoleaf x v hxv σ hσ hv
  have hsmall : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 2 * G₂.maxDegree + 1 := by
    intro v
    by_contra hv
    exact hlong ⟨v, by omega⟩
  by_cases hpure : ∀ a b, C.Adj a b → ∃ u, C.Adj a u ∧ C.Adj b u
  · exact htf C G₂ (by omega) hC2 hpure
  obtain ⟨x, y, hxy, hnt⟩ : ∃ x y, C.Adj x y ∧ ∀ u, ¬ (C.Adj x u ∧ C.Adj y u) := by
    by_contra hno
    apply hpure
    intro a b hab
    by_contra hnu
    exact hno ⟨a, b, hab, fun u hu => hnu ⟨u, hu⟩⟩
  obtain ⟨σ, hσ⟩ := almost_packing C G₂ hC2 hIH x y hxy
  by_cases hc : G₂.Adj (σ x) (σ y)
  swap
  · exact packs_of_almost C G₂ x y σ hσ hc
  by_contra hnp
  have hn' : 3 * G₂.maxDegree + 1 < Fintype.card V := by omega
  rcases relocate C G₂ hC2 hn' x y hxy σ hσ hc with hp | ⟨w, hwx, hwy, hwadj, hw1⟩
  · exact hnp hp
  rcases relocate C G₂ hC2 hn' y x hxy.symm σ (fun a b hab h1 h2 => hσ a b hab h2 h1)
    hc.symm with hp | ⟨w', hw'y, hw'x, hw'adj, hw2⟩
  · exact hnp hp
  have habx : ∀ z, (∀ b, ¬ C.Adj z b) →
      G₂.Adj (σ z) (σ y) ∨ ∃ b, C.Adj x b ∧ b ≠ y ∧ G₂.Adj (σ z) (σ b) := by
    intro z hz
    by_contra hno
    push_neg at hno
    exact hnp (absorb C G₂ x y z σ hxy hz hσ hno.1 hno.2)
  have haby : ∀ z, (∀ b, ¬ C.Adj z b) →
      G₂.Adj (σ z) (σ x) ∨ ∃ b, C.Adj y b ∧ b ≠ x ∧ G₂.Adj (σ z) (σ b) := by
    intro z hz
    by_contra hno
    push_neg at hno
    exact hnp (absorb C G₂ y x z σ hxy.symm hz (fun a b hab h1 h2 => hσ a b hab h2 h1)
      hno.1 hno.2)
  apply hnp
  refine hstep C G₂ (by omega) (by omega) hC2 hCnoleaf hsmall hIH x y hxy hnt σ hσ hc habx haby
    w w' hwx hwy hw'x hw'y hwadj hw'adj hw1 (fun a b hab h1 h2 => hw2 a b hab h2 h1) ?_
  intro hww'
  by_contra hno
  exact hnp (double_relocate C G₂ x y w w' σ hxy hwx hwy hw'x hw'y hww' hc hw'adj hw1
    (fun a b hab h1 h2 => hw2 a b hab h2 h1) hno)


theorem main : H1 → H2 → type_of% @BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two := by
  intro h1 h2 V _ _ G₁ G₂ _ _ hΔ h
  exact solution_of_H h1 h2 G₁ G₂ hΔ h

end OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1
