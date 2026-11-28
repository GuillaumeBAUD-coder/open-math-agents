import OMAReductions.R_Erdos626_erdos_626_parts_i_R1
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

-- Step Erdos626.erdos_626.parts.i.R1.H2: hypothesis H2 of reduction Erdos626.erdos_626.parts.i.R1
-- Credit: @yhay81
-- H2 := ∀ k : ℕ, 4 ≤ k → ∃ B : ℝ, ∀ i : ℕ, 0 < i →     (g k (2^i) : ℝ) ≤ B * i

open SimpleGraph Finset

private lemma walk_support_head_eq {V : Type*} {H : SimpleGraph V} {u v : V} (p : H.Walk u v) :
    p.support.head p.support_ne_nil = u := by
  cases p <;> rfl

private lemma cons_ne_cons_of_ne_mid {V : Type*} {H : SimpleGraph V} {u a₁ a₂ v : V}
    (h₁ : H.Adj u a₁) (q₁ : H.Walk a₁ v) (h₂ : H.Adj u a₂) (q₂ : H.Walk a₂ v)
    (hne : a₁ ≠ a₂) : Walk.cons h₁ q₁ ≠ Walk.cons h₂ q₂ := by
  intro heq
  have hs := congrArg (fun w => w.support.tail) heq
  simp only [Walk.support_cons, List.tail_cons] at hs
  have h1 := walk_support_head_eq q₁
  have h2 := walk_support_head_eq q₂
  have hh : q₁.support.head q₁.support_ne_nil = q₂.support.head q₂.support_ne_nil := by
    simp only [hs]
  rw [h1, h2] at hh
  exact hne hh

private lemma isPath_eq_nil {V : Type*} {H : SimpleGraph V} {u : V} (p : H.Walk u u)
    (hp : p.IsPath) : p = Walk.nil := by
  cases p with
  | nil => rfl
  | cons h q =>
    exfalso
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    exact hnd.1 q.end_mem_support

private lemma egirth_le_of_ne_paths_aux {V : Type*} [DecidableEq V] {H : SimpleGraph V} :
    ∀ (N : ℕ) {u v : V} (p₁ p₂ : H.Walk u v),
      p₁.length + p₂.length ≤ N → p₁.IsPath → p₂.IsPath → p₁ ≠ p₂ →
      H.egirth ≤ (p₁.length + p₂.length : ℕ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro u v p₁ p₂ hlen hp₁ hp₂ hne
    cases p₁ with
    | nil =>
      exact False.elim (hne (isPath_eq_nil p₂ hp₂).symm)
    | @cons _ a₁ _ h₁ q₁ =>
      cases p₂ with
      | nil =>
        exact False.elim (hne (isPath_eq_nil (Walk.cons h₁ q₁) hp₁))
      | @cons _ a₂ _ h₂ q₂ =>
        have hq₁ : q₁.IsPath := hp₁.of_cons
        have hq₂ : q₂.IsPath := hp₂.of_cons
        have hu₁ : u ∉ q₁.support := by
          have hnd := hp₁.support_nodup
          rw [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.1
        have hu₂ : u ∉ q₂.support := by
          have hnd := hp₂.support_nodup
          rw [Walk.support_cons, List.nodup_cons] at hnd
          exact hnd.1
        by_cases ha : a₁ = a₂
        · subst ha
          have hqne : q₁ ≠ q₂ := fun h => hne (by rw [h])
          have hsum_lt : q₁.length + q₂.length < N := by
            simp only [Walk.length_cons] at hlen
            omega
          have hrec := ih (q₁.length + q₂.length) hsum_lt q₁ q₂ le_rfl hq₁ hq₂ hqne
          have hle : (q₁.length + q₂.length : ℕ) ≤
              ((Walk.cons h₁ q₁).length + (Walk.cons h₂ q₂).length : ℕ) := by
            simp only [Walk.length_cons]
            omega
          exact hrec.trans (by exact_mod_cast hle)
        · by_cases hinter : ∃ z ∈ q₁.support, z ∈ q₂.support ∧ z ≠ v
          · obtain ⟨z, hz₁, hz₂, hzv⟩ := hinter
            let p₁' : H.Walk u z := Walk.cons h₁ (q₁.takeUntil z hz₁)
            let p₂' : H.Walk u z := Walk.cons h₂ (q₂.takeUntil z hz₂)
            have hzu : z ≠ u := fun h => hu₁ (h ▸ hz₁)
            have hp₁'_eq : p₁' = (Walk.cons h₁ q₁).takeUntil z (List.mem_cons_of_mem u hz₁) := by
              dsimp only [p₁']
              rw [Walk.takeUntil_cons (h := hzu.symm)]
            have hp₂'_eq : p₂' = (Walk.cons h₂ q₂).takeUntil z (List.mem_cons_of_mem u hz₂) := by
              dsimp only [p₂']
              rw [Walk.takeUntil_cons (h := hzu.symm)]
            have hp₁'_path : p₁'.IsPath := hp₁'_eq ▸ hp₁.takeUntil _
            have hp₂'_path : p₂'.IsPath := hp₂'_eq ▸ hp₂.takeUntil _
            have hp'_ne : p₁' ≠ p₂' := cons_ne_cons_of_ne_mid h₁ _ h₂ _ ha
            have hlt₁ : p₁'.length < (Walk.cons h₁ q₁).length := by
              have hspec := congrArg Walk.length (q₁.take_spec hz₁)
              rw [Walk.length_append] at hspec
              have hdrop_pos : 0 < (q₁.dropUntil z hz₁).length := by
                cases hd : q₁.dropUntil z hz₁ with
                | nil => exact False.elim (hzv rfl)
                | cons _ _ => simp
              dsimp only [p₁']
              simp only [Walk.length_cons]
              omega
            have hlt₂ : p₂'.length ≤ (Walk.cons h₂ q₂).length := by
              have hspec := congrArg Walk.length (q₂.take_spec hz₂)
              rw [Walk.length_append] at hspec
              dsimp only [p₂']
              simp only [Walk.length_cons]
              omega
            have hsum_lt : p₁'.length + p₂'.length < N := by omega
            have hrec := ih (p₁'.length + p₂'.length) hsum_lt p₁' p₂' le_rfl hp₁'_path hp₂'_path hp'_ne
            have hle : (p₁'.length + p₂'.length : ℕ) ≤
                ((Walk.cons h₁ q₁).length + (Walk.cons h₂ q₂).length : ℕ) := by omega
            exact hrec.trans (by exact_mod_cast hle)
          · push Not at hinter
            let w : H.Walk u u := (Walk.cons h₁ q₁).append (Walk.cons h₂ q₂).reverse
            have hw_ne : w ≠ Walk.nil := by
              dsimp only [w]
              simp
            have hw_nodup : w.edges.Nodup := by
              dsimp only [w]
              rw [Walk.edges_append, List.nodup_append]
              refine ⟨hp₁.isTrail.edges_nodup, hp₂.reverse.isTrail.edges_nodup, ?_⟩
              intro e he₁ e' he₂ heq
              subst heq
              rw [Walk.edges_reverse, List.mem_reverse] at he₂
              refine Sym2.ind (fun x y hx hy => ?_) e he₁ he₂
              have hxy_ne : x ≠ y := ((Walk.cons h₁ q₁).adj_of_mem_edges hx).ne
              have hx₁ : x ∈ (Walk.cons h₁ q₁).support := Walk.fst_mem_support_of_mem_edges _ hx
              have hy₁ : y ∈ (Walk.cons h₁ q₁).support := Walk.snd_mem_support_of_mem_edges _ hx
              have hx₂ : x ∈ (Walk.cons h₂ q₂).support := Walk.fst_mem_support_of_mem_edges _ hy
              have hy₂ : y ∈ (Walk.cons h₂ q₂).support := Walk.snd_mem_support_of_mem_edges _ hy
              have hmem_uv : ∀ z, z ∈ (Walk.cons h₁ q₁).support → z ∈ (Walk.cons h₂ q₂).support →
                  z = u ∨ z = v := by
                intro z h1 h2
                rw [Walk.support_cons, List.mem_cons] at h1 h2
                rcases h1 with rfl | hq1
                · exact Or.inl rfl
                · rcases h2 with rfl | hq2
                  · exact Or.inl rfl
                  · exact Or.inr (hinter z hq1 hq2)
              have hxe : s(x, y) = s(u, v) := by
                rcases hmem_uv x hx₁ hx₂ with rfl | rfl <;> rcases hmem_uv y hy₁ hy₂ with rfl | rfl
                · exact False.elim (hxy_ne rfl)
                · rfl
                · exact Sym2.eq_swap
                · exact False.elim (hxy_ne rfl)
              rw [hxe] at hx hy
              rw [Walk.edges_cons, List.mem_cons] at hx hy
              have hva₁ : v = a₁ := by
                rcases hx with heq | hmem
                · rw [Sym2.eq_iff] at heq
                  rcases heq with ⟨_, h⟩ | ⟨h, _⟩
                  · exact h
                  · exact False.elim (h₁.ne h)
                · exact False.elim (hu₁ (Walk.fst_mem_support_of_mem_edges _ hmem))
              have hva₂ : v = a₂ := by
                rcases hy with heq | hmem
                · rw [Sym2.eq_iff] at heq
                  rcases heq with ⟨_, h⟩ | ⟨h, _⟩
                  · exact h
                  · exact False.elim (h₂.ne h)
                · exact False.elim (hu₂ (Walk.fst_mem_support_of_mem_edges _ hmem))
              exact ha (hva₁.symm.trans hva₂)
            have hw_circ : w.IsCircuit := ⟨⟨hw_nodup⟩, hw_ne⟩
            have hle := hw_circ.egirth_le_length
            have hw_len : w.length = (Walk.cons h₁ q₁).length + (Walk.cons h₂ q₂).length := by
              simp only [w, Walk.length_append, Walk.length_reverse]
            rwa [hw_len] at hle

private lemma egirth_le_of_ne_paths {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {u v : V} (p₁ p₂ : H.Walk u v) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath) (hne : p₁ ≠ p₂) :
    H.egirth ≤ (p₁.length + p₂.length : ℕ) :=
  egirth_le_of_ne_paths_aux (p₁.length + p₂.length) p₁ p₂ le_rfl hp₁ hp₂ hne

private lemma not_mem_support_of_dist_ge {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {v₀ w u : V} (p : H.Walk v₀ w) (huw : u ≠ w) (hdist : p.length ≤ H.dist v₀ u) :
    u ∉ p.support := by
  intro hu
  have hspec := congrArg Walk.length (p.take_spec hu)
  rw [Walk.length_append] at hspec
  have hdrop_pos : 0 < (p.dropUntil u hu).length := by
    cases hd : p.dropUntil u hu with
    | nil => exact False.elim (huw rfl)
    | cons _ _ => simp
  have hle : H.dist v₀ u ≤ (p.takeUntil u hu).length := SimpleGraph.dist_le _
  omega

private lemma egirth_le_of_two_short_neighbors {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {v₀ u w₁ w₂ : V} {t : ℕ}
    (hw : w₁ ≠ w₂) (h₁ : H.Adj u w₁) (h₂ : H.Adj u w₂)
    (hr₁ : H.Reachable v₀ w₁) (hr₂ : H.Reachable v₀ w₂)
    (hd₁ : H.dist v₀ w₁ ≤ t) (hd₂ : H.dist v₀ w₂ ≤ t)
    (hu : t ≤ H.dist v₀ u) :
    H.egirth ≤ (2 * (t + 1) : ℕ) := by
  obtain ⟨p₁, hp₁len⟩ := hr₁.exists_walk_length_eq_dist
  obtain ⟨p₂, hp₂len⟩ := hr₂.exists_walk_length_eq_dist
  have hu₁ : u ∉ p₁.support := not_mem_support_of_dist_ge p₁ h₁.ne (by omega)
  have hu₂ : u ∉ p₂.support := not_mem_support_of_dist_ge p₂ h₂.ne (by omega)
  let q₁ : H.Walk u v₀ := Walk.cons h₁ p₁.toPath.1.reverse
  let q₂ : H.Walk u v₀ := Walk.cons h₂ p₂.toPath.1.reverse
  have hu₁' : u ∉ p₁.toPath.1.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    exact fun h => hu₁ (Walk.support_toPath_subset_support p₁ h)
  have hu₂' : u ∉ p₂.toPath.1.reverse.support := by
    rw [Walk.support_reverse, List.mem_reverse]
    exact fun h => hu₂ (Walk.support_toPath_subset_support p₂ h)
  have hq₁ : q₁.IsPath := p₁.toPath.2.reverse.cons hu₁'
  have hq₂ : q₂.IsPath := p₂.toPath.2.reverse.cons hu₂'
  have hqne : q₁ ≠ q₂ := cons_ne_cons_of_ne_mid h₁ _ h₂ _ hw
  have hle := egirth_le_of_ne_paths q₁ q₂ hq₁ hq₂ hqne
  have hlen₁ : q₁.length ≤ t + 1 := by
    dsimp only [q₁]
    simp only [Walk.length_cons, Walk.length_reverse]
    have : p₁.toPath.1.length ≤ p₁.length := Walk.length_bypass_le_length p₁
    omega
  have hlen₂ : q₂.length ≤ t + 1 := by
    dsimp only [q₂]
    simp only [Walk.length_cons, Walk.length_reverse]
    have : p₂.toPath.1.length ≤ p₂.length := Walk.length_bypass_le_length p₂
    omega
  have hsum : q₁.length + q₂.length ≤ 2 * (t + 1) := by omega
  exact hle.trans (by exact_mod_cast hsum)

private lemma moore_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (r : ℕ)
    (hdeg : ∀ v : V, 3 ≤ (H.neighborFinset v).card)
    (hgirth : (2 * r : ℕ∞) < H.egirth) :
    2 ^ r ≤ Fintype.card V := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let D (t : ℕ) : Finset V := Finset.univ.filter fun v => H.Reachable v₀ v ∧ H.dist v₀ v = t
  have hD_card : ∀ t ≤ r, 2 ^ t ≤ (D t).card := by
    intro t ht
    induction t with
    | zero =>
      have hv₀ : v₀ ∈ D 0 := by
        simp [D]
      have hpos : 0 < (D 0).card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
      omega
    | succ t ih =>
      have htr : t < r := by omega
      have h2t : 2 * (t + 1) ≤ 2 * r := by omega
      have hg : ¬ H.egirth ≤ (2 * (t + 1) : ℕ) := by
        intro hle
        have h1 : (2 * (t + 1) : ℕ∞) ≤ (2 * r : ℕ∞) := by exact_mod_cast h2t
        exact not_le_of_gt hgirth (hle.trans h1)
      let fwd (u : V) : Finset V := (H.neighborFinset u).filter fun w => w ∈ D (t + 1)
      have hdisj : Set.PairwiseDisjoint (↑(D t)) fwd := by
        intro u₁ hu₁ u₂ hu₂ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro w hw₁ hw₂
        have hu₁' := (Finset.mem_filter.mp hu₁).2
        have hu₂' := (Finset.mem_filter.mp hu₂).2
        have hw₁' := Finset.mem_filter.mp hw₁
        have hw₂' := Finset.mem_filter.mp hw₂
        have hdw := (Finset.mem_filter.mp hw₁'.2).2
        have hadj₁ : H.Adj w u₁ := ((SimpleGraph.mem_neighborFinset H u₁ w).mp hw₁'.1).symm
        have hadj₂ : H.Adj w u₂ := ((SimpleGraph.mem_neighborFinset H u₂ w).mp hw₂'.1).symm
        exact hg (egirth_le_of_two_short_neighbors hne hadj₁ hadj₂ hu₁'.1 hu₂'.1
          hu₁'.2.le hu₂'.2.le (by omega))
      have hsub : (D t).biUnion fwd ⊆ D (t + 1) := by
        intro w hw
        obtain ⟨u, _, hwu⟩ := Finset.mem_biUnion.mp hw
        exact (Finset.mem_filter.mp hwu).2
      have hfwd_ge : ∀ u ∈ D t, 2 ≤ (fwd u).card := by
        intro u hu
        have hu' := (Finset.mem_filter.mp hu).2
        let back : Finset V := (H.neighborFinset u).filter fun w => H.dist v₀ w ≤ t
        have hback_le : back.card ≤ 1 := by
          by_contra hgt
          push Not at hgt
          obtain ⟨w₁, hw₁, w₂, hw₂, hwne⟩ := Finset.one_lt_card.mp hgt
          have hw₁' := Finset.mem_filter.mp hw₁
          have hw₂' := Finset.mem_filter.mp hw₂
          have hadj₁ : H.Adj u w₁ := (SimpleGraph.mem_neighborFinset H u w₁).mp hw₁'.1
          have hadj₂ : H.Adj u w₂ := (SimpleGraph.mem_neighborFinset H u w₂).mp hw₂'.1
          have hr₁ : H.Reachable v₀ w₁ := hu'.1.trans hadj₁.reachable
          have hr₂ : H.Reachable v₀ w₂ := hu'.1.trans hadj₂.reachable
          exact hg (egirth_le_of_two_short_neighbors hwne hadj₁ hadj₂ hr₁ hr₂
            hw₁'.2 hw₂'.2 hu'.2.ge)
        have hpart : (H.neighborFinset u) \ back ⊆ fwd u := by
          intro w hw
          obtain ⟨hn, hnb⟩ := Finset.mem_sdiff.mp hw
          have hadj : H.Adj u w := (SimpleGraph.mem_neighborFinset H u w).mp hn
          have hgt : t < H.dist v₀ w := by
            by_contra hle
            exact hnb (Finset.mem_filter.mpr ⟨hn, by omega⟩)
          have hreach : H.Reachable v₀ w := hu'.1.trans hadj.reachable
          have hle : H.dist v₀ w ≤ t + 1 := by
            obtain ⟨p, hp⟩ := hu'.1.exists_walk_length_eq_dist
            have hle' : H.dist v₀ w ≤ (p.append (Walk.cons hadj Walk.nil)).length :=
              SimpleGraph.dist_le _
            simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hle'
            omega
          exact Finset.mem_filter.mpr ⟨hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach, by omega⟩⟩
        have hcard_sdiff : (H.neighborFinset u).card - back.card ≤ ((H.neighborFinset u) \ back).card := by
          rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
        have h3 := hdeg u
        have hle2 := Finset.card_le_card hpart
        omega
      have hbi : 2 * (D t).card ≤ ((D t).biUnion fwd).card := by
        rw [Finset.card_biUnion hdisj]
        calc 2 * (D t).card = ∑ _u ∈ D t, 2 := by simp [mul_comm]
          _ ≤ ∑ u ∈ D t, (fwd u).card := Finset.sum_le_sum hfwd_ge
      have hstep : 2 * (D t).card ≤ (D (t + 1)).card := hbi.trans (Finset.card_le_card hsub)
      have hih := ih (by omega)
      rw [pow_succ']
      omega
  exact (hD_card r le_rfl).trans (Finset.card_le_univ (D r))

private lemma exists_min_deg_three_induced {n : ℕ} (G : SimpleGraph (Fin n))
    (hnc : ¬ G.Colorable 3) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ v : S, 3 ≤ ((G.induce (S : Set (Fin n))).neighborSet v).ncard := by
  classical
  let bad : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S => ¬ (G.induce (S : Set (Fin n))).Colorable 3
  have huniv_bad : Finset.univ ∈ bad := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun hcol => hnc ?_⟩
    obtain ⟨c⟩ := hcol
    exact ⟨SimpleGraph.Coloring.mk (fun v => c ⟨v, Finset.mem_univ v⟩)
      fun hadj => c.valid hadj⟩
  obtain ⟨S, hSbad, hSmin⟩ := Finset.exists_min_image bad Finset.card ⟨Finset.univ, huniv_bad⟩
  have hSnc : ¬ (G.induce (S : Set (Fin n))).Colorable 3 := (Finset.mem_filter.mp hSbad).2
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    apply hSnc
    exact ⟨SimpleGraph.Coloring.mk (fun v => False.elim (Finset.notMem_empty v.1 v.2))
      (fun {v} _ => False.elim (Finset.notMem_empty v.1 v.2))⟩
  refine ⟨S, hSne, fun v => ?_⟩
  by_contra hlt
  push Not at hlt
  let S' : Finset (Fin n) := S.erase v.1
  have hS'card : S'.card < S.card := Finset.card_erase_lt_of_mem v.2
  have hS'col : (G.induce (S' : Set (Fin n))).Colorable 3 := by
    by_contra hbad'
    have hmem' : S' ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad'⟩
    have := hSmin S' hmem'
    omega
  obtain ⟨c⟩ := hS'col
  let Nv : Finset S := ((G.induce (S : Set (Fin n))).neighborSet v).toFinset
  have hNv_card : Nv.card < 3 := by
    rwa [← Set.ncard_eq_toFinset_card']
  let used : Finset (Fin 3) := Nv.image fun u =>
    if hu : u.1 ∈ S' then c ⟨u.1, hu⟩ else 0
  have hused_lt : used.card < Fintype.card (Fin 3) := by
    have h1 : used.card ≤ Nv.card := Finset.card_image_le
    simp only [Fintype.card_fin]
    omega
  have hex : ∃ col : Fin 3, col ∉ used := by
    by_contra hall
    push Not at hall
    have heq : used = Finset.univ := Finset.eq_univ_of_forall hall
    rw [heq, Finset.card_univ] at hused_lt
    exact lt_irrefl _ hused_lt
  obtain ⟨col, hcol⟩ := hex
  apply hSnc
  refine ⟨SimpleGraph.Coloring.mk (fun u => if hu : u.1 ∈ S' then c ⟨u.1, hu⟩ else col) ?_⟩
  intro x y hadj
  have hxy : x ≠ y := hadj.ne
  by_cases hx : x.1 ∈ S'
  · by_cases hy : y.1 ∈ S'
    · simp only [dif_pos hx, dif_pos hy]
      exact c.valid hadj
    · have hyv : y = v := by
        apply Subtype.ext
        by_contra hne
        exact hy (Finset.mem_erase.mpr ⟨hne, y.2⟩)
      subst hyv
      simp only [dif_pos hx, dif_neg hy]
      intro heq
      apply hcol
      refine Finset.mem_image.mpr ⟨x, ?_, ?_⟩
      · rw [Set.mem_toFinset]
        exact hadj.symm
      · simp only [dif_pos hx, heq]
  · have hxv : x = v := by
      apply Subtype.ext
      by_contra hne
      exact hx (Finset.mem_erase.mpr ⟨hne, x.2⟩)
    subst hxv
    have hy : y.1 ∈ S' := Finset.mem_erase.mpr ⟨fun h => hxy (Subtype.ext h.symm), y.2⟩
    simp only [dif_neg hx, dif_pos hy]
    intro heq
    apply hcol
    refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
    · rw [Set.mem_toFinset]
      exact hadj
    · simp only [dif_pos hy, heq.symm]

theorem OMA.solution : OMA.R_Erdos626_erdos_626_parts_i_R1.H2 := by
  intro k hk
  refine ⟨4, fun i hi => ?_⟩
  have hnat : Erdos626.g k (2 ^ i) ≤ 4 * i := by
    unfold Erdos626.g
    apply csSup_le'
    rintro m ⟨G, hGchi, hmg⟩
    have hnc : ¬ G.Colorable 3 := by
      intro hc
      have hle := hc.chromaticNumber_le
      rw [hGchi] at hle
      have : k ≤ 3 := by exact_mod_cast hle
      omega
    obtain ⟨S, hSne, hdeg⟩ := exists_min_deg_three_induced G hnc
    classical
    let H := G.induce (S : Set (Fin (2 ^ i)))
    have hSub : H ⊑ G := ⟨(SimpleGraph.Embedding.induce (S : Set (Fin (2 ^ i)))).toCopy⟩
    have hHgirth : (m : ℕ∞) < H.egirth := lt_of_lt_of_le hmg hSub.egirth_le
    have : Nonempty S := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
    let r : ℕ := m / 2
    have h2r : (2 * r : ℕ∞) < H.egirth :=
      lt_of_le_of_lt (by exact_mod_cast (show 2 * r ≤ m by omega)) hHgirth
    have hdeg' : ∀ v : S, 3 ≤ (H.neighborFinset v).card := by
      intro v
      have h1 := hdeg v
      rwa [Set.ncard_eq_toFinset_card'] at h1
    have hmoore := moore_bound H r hdeg' h2r
    have hcard_le : Fintype.card S ≤ 2 ^ i := by
      rw [Fintype.card_coe]
      simpa using S.card_le_univ
    have hpow : 2 ^ r ≤ 2 ^ i := hmoore.trans hcard_le
    have hri : r ≤ i := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
    omega
  exact_mod_cast hnat
