import OMAReductions.R_opg_seymours_r_graph_conjecture_R1

/-!
# Proof of opg-seymours-r-graph-conjecture.R1.H1

Proves Shannon's theorem (1949) for loopless multigraphs of maximum degree `d <= 3`:
every such multigraph has a proper edge coloring with `3 * d / 2` colors.

- `d = 0`: no edges exist.
- `d = 1`: no two distinct edges share a vertex, so 1 color suffices.
- `d = 2`: greedy induction on the edge set uses at most 3 colors.
- `d = 3`: induction on the edge set using 4 colors with a single Kempe chain swap and
  one neighbor recoloring.
-/

-- Proof of step opg-seymours-r-graph-conjecture.R1.H1
-- Credit: @mvanhorn

open Finset

section ShannonDegLe3

private lemma sym2_exists_eq {V : Type} (z : Sym2 V) : ∃ u v : V, z = s(u, v) := by
  induction z using Sym2.ind with
  | _ u v => exact ⟨u, v, rfl⟩

private def ProperOn {V E : Type} (ends : E → Sym2 V) {k : ℕ}
    (S : Finset E) (c : E → Fin k) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f

private def FreeAt {V E : Type} (ends : E → Sym2 V) {k : ℕ}
    (S : Finset E) (c : E → Fin k) (v : V) (κ : Fin k) : Prop :=
  ∀ e ∈ S, v ∈ ends e → c e ≠ κ

private lemma card_used_colors {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k)
    (hprop : ProperOn ends S c) (v : V) :
    ((S.filter fun e => v ∈ ends e).image c).card =
      (S.filter fun e => v ∈ ends e).card := by
  apply Finset.card_image_of_injOn
  intro e he f hf hcef
  by_contra hef
  exact hprop e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1 hef
    ⟨v, (Finset.mem_filter.mp he).2, (Finset.mem_filter.mp hf).2⟩ hcef

private lemma card_free_colors {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k)
    (hprop : ProperOn ends S c) (v : V) :
    ((Finset.univ : Finset (Fin k)) \ (S.filter fun e => v ∈ ends e).image c).card =
      k - (S.filter fun e => v ∈ ends e).card := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    card_used_colors ends S c hprop v]

private lemma mem_free_colors_iff {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k) (v : V) (κ : Fin k) :
    κ ∈ (Finset.univ : Finset (Fin k)) \ (S.filter fun e => v ∈ ends e).image c ↔
      FreeAt ends S c v κ := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
    not_exists, not_and, FreeAt]
  constructor
  · intro h e he hv hce; exact h e ⟨he, hv⟩ hce
  · intro h e ⟨he, hv⟩ hce; exact h e he hv hce

private lemma properOn_insert_update {V E : Type} [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k)
    (hprop : ProperOn ends S c) {e0 : E} {u v : V} (he0 : ends e0 = s(u, v))
    {κ : Fin k} (hu : FreeAt ends S c u κ) (hv : FreeAt ends S c v κ) :
    ProperOn ends (insert e0 S) (Function.update c e0 κ) := by
  intro e he f hf hef ⟨x, hxe, hxf⟩
  rcases Finset.mem_insert.mp he with rfl | heS <;>
    rcases Finset.mem_insert.mp hf with rfl | hfS
  · exact absurd rfl hef
  · rw [Function.update_self, Function.update_of_ne hef.symm]
    rw [he0, Sym2.mem_iff] at hxe
    rcases hxe with rfl | rfl
    · exact (hu f hfS hxf).symm
    · exact (hv f hfS hxf).symm
  · rw [Function.update_self, Function.update_of_ne hef]
    rw [he0, Sym2.mem_iff] at hxf
    rcases hxf with rfl | rfl
    · exact hu e heS hxe
    · exact hv e heS hxe
  · by_cases he0e : e = e0
    · subst he0e
      rw [Function.update_self, Function.update_of_ne hef.symm]
      rw [he0, Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · exact (hu f hfS hxf).symm
      · exact (hv f hfS hxf).symm
    · by_cases he0f : f = e0
      · subst he0f
        rw [Function.update_self, Function.update_of_ne hef]
        rw [he0, Sym2.mem_iff] at hxf
        rcases hxf with rfl | rfl
        · exact hu e heS hxe
        · exact hv e heS hxe
      · rw [Function.update_of_ne he0e, Function.update_of_ne he0f]
        exact hprop e heS f hfS hef ⟨x, hxe, hxf⟩

private lemma properOn_recolor {V E : Type} [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k)
    (hprop : ProperOn ends S c) {e1 : E} (he1 : e1 ∈ S) {u w : V} (he1_ends : ends e1 = s(u, w))
    {κ : Fin k} (hu : FreeAt ends S c u κ) (hw : FreeAt ends S c w κ) :
    ProperOn ends S (Function.update c e1 κ) ∧
    FreeAt ends S (Function.update c e1 κ) u (c e1) ∧
    (∀ v : V, v ≠ u → v ≠ w → ∀ γ : Fin k, FreeAt ends S c v γ →
      FreeAt ends S (Function.update c e1 κ) v γ) := by
  have hne_c : c e1 ≠ κ := hu e1 he1 (he1_ends ▸ by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro e he f hf hef ⟨x, hxe, hxf⟩
    by_cases he1e : e = e1
    · subst he1e
      rw [Function.update_self, Function.update_of_ne hef.symm]
      rw [he1_ends, Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · exact (hu f hf hxf).symm
      · exact (hw f hf hxf).symm
    · by_cases he1f : f = e1
      · subst he1f
        rw [Function.update_self, Function.update_of_ne hef]
        rw [he1_ends, Sym2.mem_iff] at hxf
        rcases hxf with rfl | rfl
        · exact hu e he hxe
        · exact hw e he hxe
      · rw [Function.update_of_ne he1e, Function.update_of_ne he1f]
        exact hprop e he f hf hef ⟨x, hxe, hxf⟩
  · intro e he hue
    by_cases he1e : e = e1
    · subst he1e; rw [Function.update_self]; exact hne_c.symm
    · rw [Function.update_of_ne he1e]
      exact hprop e he e1 he1 he1e ⟨u, hue, he1_ends ▸ by simp⟩
  · intro v hvu hvw γ hvγ e he hve
    have he1e : e ≠ e1 := by
      rintro rfl
      rw [he1_ends, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl <;> contradiction
    rw [Function.update_of_ne he1e]
    exact hvγ e he hve

-- Path uniqueness in graphs of maximum degree <= 2
private lemma internal_deg_ge_two {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y v : V}
    (p : G.Walk x y) (hp : p.IsPath) (hv : v ∈ p.support) (hvx : v ≠ x) (hvy : v ≠ y) :
    2 ≤ G.degree v := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    exact absurd hv hvx
  | @cons a b c hab p' ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hvp'
    · exact absurd rfl hvx
    · have hp' : p'.IsPath := hp.of_cons
      by_cases hvb : v = b
      · subst hvb
        cases p' with
        | nil => exact absurd rfl hvy
        | @cons _ d _ hbd p'' =>
          have had : a ≠ d := by
            intro h
            subst h
            have hnodup := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons] at hnodup
            exact hnodup.1 (Or.inr (SimpleGraph.Walk.start_mem_support p''))
          have hsub : ({a, d} : Finset V) ⊆ G.neighborFinset v := by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rw [SimpleGraph.mem_neighborFinset]
            rcases ht with rfl | rfl
            · exact hab.symm
            · exact hbd
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          calc 2 = ({a, d} : Finset V).card := (Finset.card_pair had).symm
            _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
      · exact ih hp' hvp' hvb hvy

private lemma deg_le_two_unique_other {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x p a b : V}
    (hdeg : G.degree x ≤ 2) (hxp : G.Adj x p) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hap : a ≠ p) (hbp : b ≠ p) : a = b := by
  by_contra hab
  have hsub : ({p, a, b} : Finset V) ⊆ G.neighborFinset x := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [SimpleGraph.mem_neighborFinset]
    rcases ht with rfl | rfl | rfl <;> assumption
  have hc3 : ({p, a, b} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hap.symm, hbp.symm]),
      Finset.card_pair hab]
  have hle : ({p, a, b} : Finset V).card ≤ G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  omega

private lemma unique_path_of_maxDeg_le_two {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hmax : ∀ z : V, G.degree z ≤ 2) :
    ∀ (n : ℕ) {x y z : V} (prev : Option V)
      (p : G.Walk x y) (q : G.Walk x z),
      p.length ≤ n → p.IsPath → q.IsPath →
      (∀ s ∈ p.support, prev ≠ some s) →
      (∀ s ∈ q.support, prev ≠ some s) →
      (∀ a b, G.Adj x a → G.Adj x b → prev ≠ some a → prev ≠ some b → a = b) →
      y ∈ q.support ∨ z ∈ p.support := by
  intro n
  induction n with
  | zero =>
    intro x y z _ p q hlen _ _ _ _ _
    cases p with
    | nil => exact Or.inl (SimpleGraph.Walk.start_mem_support q)
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro x y z prev p q hlen hp hq hpv hqv huniq
    cases p with
    | nil => exact Or.inl (SimpleGraph.Walk.start_mem_support q)
    | @cons _ a _ hxa p' =>
      cases q with
      | nil => exact Or.inr (SimpleGraph.Walk.start_mem_support _)
      | @cons _ b _ hxb q' =>
        have ha_mem : a ∈ (SimpleGraph.Walk.cons hxa p').support := by simp
        have hb_mem : b ∈ (SimpleGraph.Walk.cons hxb q').support := by simp
        have hab : a = b := huniq a b hxa hxb (hpv a ha_mem) (hqv b hb_mem)
        subst hab
        have hp' : p'.IsPath := hp.of_cons
        have hq' : q'.IsPath := hq.of_cons
        have hx_not_p' : x ∉ p'.support := by
          have := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at this
          exact this.1
        have hx_not_q' : x ∉ q'.support := by
          have := hq.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at this
          exact this.1
        have hlen' : p'.length ≤ n := by simp at hlen; omega
        have hres := ih (some x) p' q' hlen' hp' hq'
          (fun s hs he => hx_not_p' (Option.some.inj he ▸ hs))
          (fun s hs he => hx_not_q' (Option.some.inj he ▸ hs))
          (fun c d hac had hcx hdx =>
            deg_le_two_unique_other (hmax a) hxa.symm hac had
              (fun h => hcx (congrArg some h.symm))
              (fun h => hdx (congrArg some h.symm)))
        rcases hres with hy | hz
        · exact Or.inl (by simp [hy])
        · exact Or.inr (by simp [hz])

private lemma not_three_deg_le_one_in_component {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : ∀ x : V, G.degree x ≤ 2)
    (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hdu : G.degree u ≤ 1) (hdv : G.degree v ≤ 1) (hdw : G.degree w ≤ 1)
    (hruv : G.Reachable u v) (hruw : G.Reachable u w) : False := by
  let p := hruv.some.toPath
  let q := hruw.some.toPath
  have huniq : ∀ a b, G.Adj u a → G.Adj u b → (none : Option V) ≠ some a →
      (none : Option V) ≠ some b → a = b := by
    intro a b hua hub _ _
    have hcard : (G.neighborFinset u).card ≤ 1 := by
      rwa [SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_one.mp hcard a ((SimpleGraph.mem_neighborFinset G u a).mpr hua)
      b ((SimpleGraph.mem_neighborFinset G u b).mpr hub)
  rcases unique_path_of_maxDeg_le_two hmax p.1.length none p.1 q.1 le_rfl p.2 q.2
      (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) huniq with hvq | hwp
  · have h2 := internal_deg_ge_two q.1 q.2 hvq huv.symm hvw
    omega
  · have h2 := internal_deg_ge_two p.1 p.2 hwp huw.symm hvw.symm
    omega

-- Kempe swap on the (α, δ)-subgraph component of x0
private lemma kempe_swap {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (S : Finset E) (c : E → Fin 4) (hprop : ProperOn ends S c)
    (α δ : Fin 4) (hαδ : α ≠ δ) (x0 : V) (hx0 : FreeAt ends S c x0 α) :
    let K : SimpleGraph V :=
      { Adj := fun x y => x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = α ∨ c e = δ)
        symm := ⟨fun x y ⟨hne, e, he, hends, hc⟩ =>
          ⟨hne.symm, e, he, hends.trans Sym2.eq_swap, hc⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    ∃ c' : E → Fin 4,
      ProperOn ends S c' ∧
      FreeAt ends S c' x0 δ ∧
      (∀ e ∈ S, c e ≠ α → c e ≠ δ → c' e = c e) ∧
      (∀ y : V, ¬ K.Reachable x0 y → ∀ e ∈ S, y ∈ ends e → c' e = c e) := by
  classical
  intro K
  let c' : E → Fin 4 := fun e =>
    if (c e = α ∨ c e = δ) ∧ (∃ x, x ∈ ends e ∧ K.Reachable x0 x) then
      if c e = α then δ else α
    else c e
  have hcomp_iff : ∀ e ∈ S, c e = α ∨ c e = δ → ∀ x y : V, ends e = s(x, y) →
      (K.Reachable x0 x ↔ K.Reachable x0 y) := by
    intro e he hce x y hends
    have hxy : x ≠ y := by
      have hl := hloop e; rw [hends] at hl; simpa using hl
    have hadj : K.Adj x y := ⟨hxy, e, he, hends, hce⟩
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  have hmem_reach : ∀ e ∈ S, c e = α ∨ c e = δ → ∀ v : V, v ∈ ends e →
      ((∃ x, x ∈ ends e ∧ K.Reachable x0 x) ↔ K.Reachable x0 v) := by
    intro e he hce v hv
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    constructor
    · rintro ⟨x, hx, hrx⟩
      rw [hw, Sym2.mem_iff] at hx
      rcases hx with rfl | hxw
      · exact hrx
      · rw [hxw] at hrx
        exact (hcomp_iff e he hce v w hw).mpr hrx
    · intro hrv; exact ⟨v, hv, hrv⟩
  refine ⟨c', ?_, ?_, ?_, ?_⟩
  · -- ProperOn ends S c'
    intro e he f hf hef ⟨v, hve, hvf⟩
    have hce_ne : c e ≠ c f := hprop e he f hf hef ⟨v, hve, hvf⟩
    by_cases hrv : K.Reachable x0 v
    · dsimp only [c']
      by_cases hce : c e = α ∨ c e = δ <;> by_cases hcf : c f = α ∨ c f = δ
      · have he1 : ∃ x, x ∈ ends e ∧ K.Reachable x0 x := ⟨v, hve, hrv⟩
        have hf1 : ∃ x, x ∈ ends f ∧ K.Reachable x0 x := ⟨v, hvf, hrv⟩
        simp only [hce, he1, hcf, hf1, and_self, ↓reduceIte]
        rcases hce with h1 | h1 <;> rcases hcf with h2 | h2
        · exact absurd (h1.trans h2.symm) hce_ne
        · simp [h1, h2, hαδ.symm]
        · simp [h1, h2, hαδ.symm]; exact hαδ
        · exact absurd (h1.trans h2.symm) hce_ne
      · have he1 : ∃ x, x ∈ ends e ∧ K.Reachable x0 x := ⟨v, hve, hrv⟩
        simp only [hce, he1, hcf, and_self, false_and, ↓reduceIte]
        push Not at hcf
        split_ifs <;> [exact Ne.symm hcf.2; exact Ne.symm hcf.1]
      · have hf1 : ∃ x, x ∈ ends f ∧ K.Reachable x0 x := ⟨v, hvf, hrv⟩
        simp only [hce, hcf, hf1, and_self, false_and, ↓reduceIte]
        push Not at hce
        split_ifs <;> [exact hce.2; exact hce.1]
      · simp only [hce, hcf, false_and, ↓reduceIte]; exact hce_ne
    · have hne : ¬ ((c e = α ∨ c e = δ) ∧ (∃ x, x ∈ ends e ∧ K.Reachable x0 x)) := by
        rintro ⟨hce, hex⟩; exact hrv ((hmem_reach e he hce v hve).mp hex)
      have hnf : ¬ ((c f = α ∨ c f = δ) ∧ (∃ x, x ∈ ends f ∧ K.Reachable x0 x)) := by
        rintro ⟨hcf, hex⟩; exact hrv ((hmem_reach f hf hcf v hvf).mp hex)
      simp only [c', hne, hnf, ↓reduceIte]
      exact hce_ne
  · -- FreeAt ends S c' x0 δ
    intro e he hx0e
    dsimp only [c']
    by_cases hce : c e = α ∨ c e = δ
    · have hex : ∃ x, x ∈ ends e ∧ K.Reachable x0 x := ⟨x0, hx0e, SimpleGraph.Reachable.refl x0⟩
      simp only [hce, hex, and_self, ↓reduceIte]
      rcases hce with h1 | h1
      · exact absurd h1 (hx0 e he hx0e)
      · simp [h1, hαδ.symm, hαδ]
    · simp only [hce, false_and, ↓reduceIte]
      push Not at hce
      exact hce.2
  · -- Colors other than α, δ are unchanged
    intro e _ h1 h2
    have hnot : ¬ ((c e = α ∨ c e = δ) ∧ (∃ x, x ∈ ends e ∧ K.Reachable x0 x)) := by
      rintro ⟨h | h, _⟩ <;> contradiction
    simp only [c', hnot, ↓reduceIte]
  · -- Edges at vertices unreachable from x0 are unchanged
    intro y hy e he hye
    have hnot : ¬ ((c e = α ∨ c e = δ) ∧ (∃ x, x ∈ ends e ∧ K.Reachable x0 x)) := by
      rintro ⟨hce, hex⟩
      exact hy ((hmem_reach e he hce y hye).mp hex)
    simp only [c', hnot, ↓reduceIte]

private lemma kempe_graph_deg_bounds {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (S : Finset E) (c : E → Fin 4) (hprop : ProperOn ends S c)
    (α δ : Fin 4) (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : ∀ x y : V, K.Adj x y ↔ x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = α ∨ c e = δ)) :
    (∀ x : V, K.degree x ≤ 2) ∧
    (∀ x : V, (FreeAt ends S c x α ∨ FreeAt ends S c x δ) → K.degree x ≤ 1) := by
  have hdeg_le : ∀ x : V, ∀ T : Finset (Fin 4),
      (∀ y : V, K.Adj x y → ∃ e ∈ S, ends e = s(x, y) ∧ c e ∈ T) →
      K.degree x ≤ T.card := by
    intro x T hT
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let f : {y // y ∈ K.neighborFinset x} → Fin 4 := fun y =>
      c (hT y.1 ((SimpleGraph.mem_neighborFinset K x y.1).mp y.2)).choose
    have hf_mem : ∀ y, f y ∈ T := fun y =>
      (hT y.1 ((SimpleGraph.mem_neighborFinset K x y.1).mp y.2)).choose_spec.2.2
    have hf_inj : Function.Injective f := by
      intro y1 y2 heq
      set e1 := (hT y1.1 ((SimpleGraph.mem_neighborFinset K x y1.1).mp y1.2)).choose
      set e2 := (hT y2.1 ((SimpleGraph.mem_neighborFinset K x y2.1).mp y2.2)).choose
      have hs1 := (hT y1.1 ((SimpleGraph.mem_neighborFinset K x y1.1).mp y1.2)).choose_spec
      have hs2 := (hT y2.1 ((SimpleGraph.mem_neighborFinset K x y2.1).mp y2.2)).choose_spec
      have he12 : e1 = e2 := by
        by_contra hne
        exact hprop e1 hs1.1 e2 hs2.1 hne
          ⟨x, hs1.2.1 ▸ by simp, hs2.2.1 ▸ by simp⟩ heq
      have hsym : s(x, y1.1) = s(x, y2.1) :=
        hs1.2.1.symm.trans ((congrArg ends he12).trans hs2.2.1)
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hsym
      rcases hsym with ⟨_, h⟩ | ⟨h, _⟩
      · exact Subtype.ext h
      · exact absurd h ((SimpleGraph.mem_neighborFinset K x y2.1).mp y2.2).ne
    have hcard_le : Fintype.card {y // y ∈ K.neighborFinset x} ≤ T.card := by
      have hsub : (Finset.univ.image f) ⊆ T := by
        intro κ hκ
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hκ
        exact hf_mem y
      calc Fintype.card {y // y ∈ K.neighborFinset x}
          = (Finset.univ : Finset {y // y ∈ K.neighborFinset x}).card := (Finset.card_univ).symm
        _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
        _ ≤ T.card := Finset.card_le_card hsub
    rwa [Fintype.card_coe] at hcard_le
  constructor
  · intro x
    refine (hdeg_le x {α, δ} ?_).trans Finset.card_le_two
    intro y hy
    obtain ⟨_, e, he, hends, hc⟩ := (hK x y).mp hy
    exact ⟨e, he, hends, by simp [hc]⟩
  · intro x hfree
    rcases hfree with hα | hδ
    · exact (hdeg_le x {δ} (fun y hy => by
        obtain ⟨_, e, he, hends, hc⟩ := (hK x y).mp hy
        rcases hc with h1 | h1
        · exact absurd h1 (hα e he (hends ▸ by simp))
        · exact ⟨e, he, hends, by simp [h1]⟩)).trans (by simp)
    · exact (hdeg_le x {α} (fun y hy => by
        obtain ⟨_, e, he, hends, hc⟩ := (hK x y).mp hy
        rcases hc with h1 | h1
        · exact ⟨e, he, hends, by simp [h1]⟩
        · exact absurd h1 (hδ e he (hends ▸ by simp)))).trans (by simp)

private lemma shannon_deg3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hdeg : ∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ 3) :
    ∀ S : Finset E, ∃ c : E → Fin 4, ProperOn ends S c := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert e0 S he0S ih =>
    obtain ⟨c, hprop⟩ := ih
    obtain ⟨u, v, he0_ends⟩ := sym2_exists_eq (ends e0)
    have huv : u ≠ v := by
      have hl := hloop e0; rw [he0_ends] at hl; simpa using hl
    have hS_deg : ∀ x : V, (S.filter fun e => x ∈ ends e).card ≤ 3 := fun x =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans (hdeg x)
    have hS_deg_u : (S.filter fun e => u ∈ ends e).card ≤ 2 := by
      have hsub : insert e0 (S.filter fun e => u ∈ ends e) ⊆ Finset.univ.filter fun e => u ∈ ends e := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he0_ends ▸ by simp⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
      have hnot : e0 ∉ S.filter fun e => u ∈ ends e := fun h => he0S (Finset.mem_filter.mp h).1
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hc
      have := hdeg u; omega
    have hS_deg_v : (S.filter fun e => v ∈ ends e).card ≤ 2 := by
      have hsub : insert e0 (S.filter fun e => v ∈ ends e) ⊆ Finset.univ.filter fun e => v ∈ ends e := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he0_ends ▸ by simp⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
      have hnot : e0 ∉ S.filter fun e => v ∈ ends e := fun h => he0S (Finset.mem_filter.mp h).1
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hc
      have := hdeg v; omega
    let Fu := (Finset.univ : Finset (Fin 4)) \ (S.filter fun e => u ∈ ends e).image c
    let Fv := (Finset.univ : Finset (Fin 4)) \ (S.filter fun e => v ∈ ends e).image c
    have hFu_ge2 : 2 ≤ Fu.card := by
      rw [card_free_colors ends S c hprop u]; omega
    have hFv_ge2 : 2 ≤ Fv.card := by
      rw [card_free_colors ends S c hprop v]; omega
    by_cases hcomm : (Fu ∩ Fv).Nonempty
    · obtain ⟨κ, hκ⟩ := hcomm
      have huκ := (mem_free_colors_iff ends S c u κ).mp (Finset.mem_inter.mp hκ).1
      have hvκ := (mem_free_colors_iff ends S c v κ).mp (Finset.mem_inter.mp hκ).2
      exact ⟨Function.update c e0 κ, properOn_insert_update ends S c hprop he0_ends huκ hvκ⟩
    · -- Fu and Fv are disjoint subsets of Fin 4 of size >= 2, so both have size 2 and partition Fin 4!
      have hdisj : Disjoint Fu Fv := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hcomm)
      have hFu_eq2 : Fu.card = 2 := by
        have hu := Finset.card_union_of_disjoint hdisj
        have hle : (Fu ∪ Fv).card ≤ 4 := by
          calc (Fu ∪ Fv).card ≤ (Finset.univ : Finset (Fin 4)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = 4 := by decide
        omega
      have hFv_eq2 : Fv.card = 2 := by
        have hu := Finset.card_union_of_disjoint hdisj
        have hle : (Fu ∪ Fv).card ≤ 4 := by
          calc (Fu ∪ Fv).card ≤ (Finset.univ : Finset (Fin 4)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = 4 := by decide
        omega
      have hpart : Fu ∪ Fv = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        rw [Finset.card_union_of_disjoint hdisj, hFu_eq2, hFv_eq2, Finset.card_univ, Fintype.card_fin]
      obtain ⟨α, β, hαβ, hFu_pair⟩ := Finset.card_eq_two.mp hFu_eq2
      obtain ⟨γ, δ, hγδ, hFv_pair⟩ := Finset.card_eq_two.mp hFv_eq2
      have hα_Fu : α ∈ Fu := by rw [hFu_pair]; simp
      have hβ_Fu : β ∈ Fu := by rw [hFu_pair]; simp
      have hγ_Fv : γ ∈ Fv := by rw [hFv_pair]; simp
      have hδ_Fv : δ ∈ Fv := by rw [hFv_pair]; simp
      have hα_free_u : FreeAt ends S c u α := (mem_free_colors_iff ends S c u α).mp hα_Fu
      have hβ_free_u : FreeAt ends S c u β := (mem_free_colors_iff ends S c u β).mp hβ_Fu
      have hγ_free_v : FreeAt ends S c v γ := (mem_free_colors_iff ends S c v γ).mp hγ_Fv
      have hδ_free_v : FreeAt ends S c v δ := (mem_free_colors_iff ends S c v δ).mp hδ_Fv
      have hαγ : α ≠ γ := fun h => Finset.disjoint_left.mp hdisj hα_Fu (h ▸ hγ_Fv)
      have hαδ : α ≠ δ := fun h => Finset.disjoint_left.mp hdisj hα_Fu (h ▸ hδ_Fv)
      have hβγ : β ≠ γ := fun h => Finset.disjoint_left.mp hdisj hβ_Fu (h ▸ hγ_Fv)
      have hβδ : β ≠ δ := fun h => Finset.disjoint_left.mp hdisj hβ_Fu (h ▸ hδ_Fv)
      -- γ is NOT free at u, so there is an edge eγ ∈ S incident to u with color γ!
      have hγ_not_Fu : γ ∉ Fu := fun h => Finset.disjoint_left.mp hdisj h hγ_Fv
      have hγ_used_u : γ ∈ (S.filter fun e => u ∈ ends e).image c := by
        by_contra hnot
        exact hγ_not_Fu (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
      obtain ⟨eγ, heγ_f, hcγ⟩ := Finset.mem_image.mp hγ_used_u
      have heγ_S : eγ ∈ S := (Finset.mem_filter.mp heγ_f).1
      have hu_eγ : u ∈ ends eγ := (Finset.mem_filter.mp heγ_f).2
      obtain ⟨w, heγ_ends⟩ := Sym2.mem_iff_exists.mp hu_eγ
      have huw : u ≠ w := by
        have hl := hloop eγ; rw [heγ_ends] at hl; simpa using hl
      have hvw : v ≠ w := by
        rintro rfl
        exact hγ_free_v eγ heγ_S (heγ_ends ▸ by simp) hcγ
      -- w has degree <= 3, so at least 1 color κ ∈ Fin 4 is free at w!
      let Fw := (Finset.univ : Finset (Fin 4)) \ (S.filter fun e => w ∈ ends e).image c
      have hFw_pos : 0 < Fw.card := by
        rw [card_free_colors ends S c hprop w]; have := hS_deg w; omega
      obtain ⟨κ, hκ_Fw⟩ := Finset.card_pos.mp hFw_pos
      have hκ_free_w : FreeAt ends S c w κ := (mem_free_colors_iff ends S c w κ).mp hκ_Fw
      have hκγ : κ ≠ γ := fun h => hκ_free_w eγ heγ_S (heγ_ends ▸ by simp) (hcγ.trans h.symm)
      have hκ_mem : κ ∈ Fu ∪ Fv := by rw [hpart]; exact Finset.mem_univ _
      rw [hFu_pair, hFv_pair] at hκ_mem
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hκ_mem
      rcases hκ_mem with (hκα | hκβ) | (hκγ' | hκδ)
      · -- κ = α is free at both u and w: recolor eγ to α, then color e0 with γ!
        rw [hκα] at hκ_free_w
        obtain ⟨hprop1, huγ1, hv_pres⟩ :=
          properOn_recolor ends S c hprop heγ_S heγ_ends hα_free_u hκ_free_w
        rw [hcγ] at huγ1
        have hvγ1 := hv_pres v huv.symm hvw γ hγ_free_v
        exact ⟨Function.update (Function.update c eγ α) e0 γ,
          properOn_insert_update ends S _ hprop1 he0_ends huγ1 hvγ1⟩
      · -- κ = β is free at both u and w: recolor eγ to β, then color e0 with γ!
        rw [hκβ] at hκ_free_w
        obtain ⟨hprop1, huγ1, hv_pres⟩ :=
          properOn_recolor ends S c hprop heγ_S heγ_ends hβ_free_u hκ_free_w
        rw [hcγ] at huγ1
        have hvγ1 := hv_pres v huv.symm hvw γ hγ_free_v
        exact ⟨Function.update (Function.update c eγ β) e0 γ,
          properOn_insert_update ends S _ hprop1 he0_ends huγ1 hvγ1⟩
      · exact absurd hκγ' hκγ
      · -- κ = δ is free at w! Consider the (α, δ)-Kempe graph K!
        rw [hκδ] at hκ_free_w
        let K : SimpleGraph V :=
          { Adj := fun x y => x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = α ∨ c e = δ)
            symm := ⟨fun x y ⟨hne, e, he, hends, hc⟩ =>
              ⟨hne.symm, e, he, hends.trans Sym2.eq_swap, hc⟩⟩
            loopless := ⟨fun _ h => h.1 rfl⟩ }
        have hK_bounds := kempe_graph_deg_bounds ends S c hprop α δ K (fun _ _ => Iff.rfl)
        by_cases hruv : K.Reachable u v
        · -- Then w CANNOT be reachable from u (nor from v) in K!
          have hruw : ¬ K.Reachable u w := fun hruw =>
            not_three_deg_le_one_in_component K hK_bounds.1 u v w huv huw hvw
              (hK_bounds.2 u (Or.inl hα_free_u))
              (hK_bounds.2 v (Or.inr hδ_free_v))
              (hK_bounds.2 w (Or.inr hκ_free_w))
              hruv hruw
          have hrwu : ¬ K.Reachable w u := fun h => hruw h.symm
          have hrwv : ¬ K.Reachable w v := fun h => hruw (hruv.trans h.symm)
          -- Swap (α, δ) on the K-component of w!
          obtain ⟨c1, hprop1, hwα1, hother1, hunreach1⟩ :=
            kempe_swap ends hloop S c hprop δ α hαδ.symm w hκ_free_w
          -- Note: kempe_swap swaps δ <-> α, making α free at w, and leaves u, v, and eγ untouched!
          have hK_eq : (SimpleGraph.mk (Adj := fun x y => x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = δ ∨ c e = α))
              (symm := ⟨fun x y ⟨hne, e, he, hends, hc⟩ => ⟨hne.symm, e, he, hends.trans Sym2.eq_swap, hc⟩⟩)
              (loopless := ⟨fun _ h => h.1 rfl⟩)) = K := by
            ext x y; simp [K, or_comm]
          have hrwu' : ¬ (SimpleGraph.mk (Adj := fun x y => x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = δ ∨ c e = α))
              (symm := ⟨fun x y ⟨hne, e, he, hends, hc⟩ => ⟨hne.symm, e, he, hends.trans Sym2.eq_swap, hc⟩⟩)
              (loopless := ⟨fun _ h => h.1 rfl⟩)).Reachable w u := by rwa [hK_eq]
          have hrwv' : ¬ (SimpleGraph.mk (Adj := fun x y => x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = δ ∨ c e = α))
              (symm := ⟨fun x y ⟨hne, e, he, hends, hc⟩ => ⟨hne.symm, e, he, hends.trans Sym2.eq_swap, hc⟩⟩)
              (loopless := ⟨fun _ h => h.1 rfl⟩)).Reachable w v := by rwa [hK_eq]
          have huα1 : FreeAt ends S c1 u α := fun e he hue => by
            rw [hunreach1 u hrwu' e he hue]; exact hα_free_u e he hue
          have hvγ1 : FreeAt ends S c1 v γ := fun e he hve => by
            rw [hunreach1 v hrwv' e he hve]; exact hγ_free_v e he hve
          have hc1γ : c1 eγ = γ := by
            rw [hother1 eγ heγ_S (hcγ.symm ▸ hγδ) (hcγ.symm ▸ hαγ.symm), hcγ]
          obtain ⟨hprop2, huγ2, hv_pres2⟩ :=
            properOn_recolor ends S c1 hprop1 heγ_S heγ_ends huα1 hwα1
          rw [hc1γ] at huγ2
          have hvγ2 := hv_pres2 v huv.symm hvw γ hvγ1
          exact ⟨Function.update (Function.update c1 eγ α) e0 γ,
            properOn_insert_update ends S _ hprop2 he0_ends huγ2 hvγ2⟩
        · -- v is not reachable from u in K: swap (α, δ) on the K-component of u, then color e0 with δ!
          obtain ⟨c1, hprop1, huδ1, _, hunreach1⟩ :=
            kempe_swap ends hloop S c hprop α δ hαδ u hα_free_u
          have hvδ1 : FreeAt ends S c1 v δ := fun e he hve => by
            rw [hunreach1 v hruv e he hve]; exact hδ_free_v e he hve
          exact ⟨Function.update c1 e0 δ,
            properOn_insert_update ends S c1 hprop1 he0_ends huδ1 hvδ1⟩

private lemma shannon_deg2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → Sym2 V) (_hloop : ∀ e, ¬ (ends e).IsDiag)
    (hdeg : ∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ 2) :
    ∀ S : Finset E, ∃ c : E → Fin 3, ProperOn ends S c := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert e0 S he0S ih =>
    obtain ⟨c, hprop⟩ := ih
    obtain ⟨u, v, he0_ends⟩ := sym2_exists_eq (ends e0)
    have hS_deg_u : (S.filter fun e => u ∈ ends e).card ≤ 1 := by
      have hsub : insert e0 (S.filter fun e => u ∈ ends e) ⊆ Finset.univ.filter fun e => u ∈ ends e := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he0_ends ▸ by simp⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
      have hnot : e0 ∉ S.filter fun e => u ∈ ends e := fun h => he0S (Finset.mem_filter.mp h).1
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hc
      have := hdeg u; omega
    have hS_deg_v : (S.filter fun e => v ∈ ends e).card ≤ 1 := by
      have hsub : insert e0 (S.filter fun e => v ∈ ends e) ⊆ Finset.univ.filter fun e => v ∈ ends e := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he0_ends ▸ by simp⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
      have hnot : e0 ∉ S.filter fun e => v ∈ ends e := fun h => he0S (Finset.mem_filter.mp h).1
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hc
      have := hdeg v; omega
    let used := (S.filter fun e => u ∈ ends e).image c ∪ (S.filter fun e => v ∈ ends e).image c
    have hused_le2 : used.card ≤ 2 := by
      calc used.card ≤ ((S.filter fun e => u ∈ ends e).image c).card +
            ((S.filter fun e => v ∈ ends e).image c).card := Finset.card_union_le _ _
        _ ≤ (S.filter fun e => u ∈ ends e).card + (S.filter fun e => v ∈ ends e).card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ ≤ 2 := by omega
    have hfree_pos : 0 < ((Finset.univ : Finset (Fin 3)) \ used).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨κ, hκ⟩ := Finset.card_pos.mp hfree_pos
    have hκ_not : κ ∉ used := (Finset.mem_sdiff.mp hκ).2
    have huκ : FreeAt ends S c u κ := fun e he hue hce =>
      hκ_not (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hue⟩, hce⟩))
    have hvκ : FreeAt ends S c v κ := fun e he hve hce =>
      hκ_not (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, hce⟩))
    exact ⟨Function.update c e0 κ, properOn_insert_update ends S c hprop he0_ends huκ hvκ⟩

theorem OMA.solution : OMA.R_opg_seymours_r_graph_conjecture_R1.H1 := by
  intro V E _ _ _ ends hloop d hd hdeg
  classical
  interval_cases d
  · -- d = 0: E is empty
    have hempty : ∀ e : E, False := by
      intro e
      obtain ⟨u, _, hu⟩ := sym2_exists_eq (ends e)
      have hpos : 0 < (Finset.univ.filter fun f => u ∈ ends f).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu ▸ by simp⟩⟩
      have := hdeg u
      omega
    exact ⟨fun e => False.elim (hempty e), fun e _ _ _ => False.elim (hempty e)⟩
  · -- d = 1: no two distinct edges share a vertex
    refine ⟨fun _ => ⟨0, by decide⟩, fun e f hef ⟨v, hve, hvf⟩ _ => ?_⟩
    have h2 : 2 ≤ (Finset.univ.filter fun g => v ∈ ends g).card := by
      have hsub : ({e, f} : Finset E) ⊆ Finset.univ.filter fun g => v ∈ ends g := by
        intro g hg
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
      calc 2 = ({e, f} : Finset E).card := (Finset.card_pair hef).symm
        _ ≤ _ := Finset.card_le_card hsub
    have := hdeg v
    omega
  · -- d = 2: 3 colors
    obtain ⟨c, hc⟩ := shannon_deg2 ends hloop hdeg Finset.univ
    exact ⟨c, fun e f hef hv => hc e (Finset.mem_univ _) f (Finset.mem_univ _) hef hv⟩
  · -- d = 3: 4 colors
    obtain ⟨c, hc⟩ := shannon_deg3 ends hloop hdeg Finset.univ
    exact ⟨c, fun e f hef hv => hc e (Finset.mem_univ _) f (Finset.mem_univ _) hef hv⟩

end ShannonDegLe3
