import OMAReductions.R_opg_seymours_r_graph_conjecture_R1

-- Step opg-seymours-r-graph-conjecture.R1.H1: hypothesis H1 of reduction opg-seymours-r-graph-conjecture.R1
-- Credit: @hadijannat
-- H1 := ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (ends : E → Sym2 V),
--     (∀ e, ¬ (ends e).IsDiag) → ∀ d : ℕ, d ≤ 3 →
--       (∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ d) →
--       ∃ c : E → Fin (3 * d / 2), ∀ e f, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f

namespace ShannonH1

open SimpleGraph Finset

private def ProperOn {V E : Type} (ends : E → Sym2 V) {k : ℕ}
    (S : Finset E) (c : E → Fin k) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (∃ v, v ∈ ends e ∧ v ∈ ends f) → c e ≠ c f

private lemma sym2_eq_pair {V : Type} [DecidableEq V] {p : Sym2 V} (hp : ¬ p.IsDiag) :
    ∃ u v : V, u ≠ v ∧ p = s(u, v) := by
  induction p using Sym2.ind with
  | _ a b => exact ⟨a, b, by simpa using hp, rfl⟩

private lemma sym2_eq_of_ne_mem {V : Type} {a b : V} {p : Sym2 V}
    (hab : a ≠ b) (ha : a ∈ p) (hb : b ∈ p) : p = s(a, b) := by
  induction p using Sym2.ind with
  | _ x y =>
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hab rfl).elim

private def usedAt {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k) (x : V) : Finset (Fin k) :=
  (S.filter fun e => x ∈ ends e).image c

private lemma mem_usedAt_iff {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k) (x : V) (α : Fin k) :
    α ∈ usedAt ends S c x ↔ ∃ e ∈ S, x ∈ ends e ∧ c e = α := by
  simp only [usedAt, mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hx⟩, rfl⟩
    exact ⟨e, he, hx, rfl⟩
  · rintro ⟨e, he, hx, rfl⟩
    exact ⟨e, ⟨he, hx⟩, rfl⟩

private lemma card_usedAt_le {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} (S : Finset E) (c : E → Fin k) (x : V) :
    (usedAt ends S c x).card ≤ (S.filter fun e => x ∈ ends e).card :=
  Finset.card_image_le

private lemma unique_edge_of_color {V E : Type} (ends : E → Sym2 V) {k : ℕ}
    {S : Finset E} {c : E → Fin k} (hprop : ProperOn ends S c)
    {e₁ e₂ : E} (he₁ : e₁ ∈ S) (he₂ : e₂ ∈ S) {x : V}
    (hx₁ : x ∈ ends e₁) (hx₂ : x ∈ ends e₂) (hc : c e₁ = c e₂) : e₁ = e₂ := by
  by_contra hne
  exact hprop e₁ he₁ e₂ he₂ hne ⟨x, hx₁, hx₂⟩ hc

private lemma properOn_update_insert {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} {S : Finset E} {c : E → Fin k}
    (hprop : ProperOn ends S c) {e₀ : E} (he₀ : e₀ ∉ S) {u v : V}
    (huv : ends e₀ = s(u, v)) {α : Fin k}
    (hu : α ∉ usedAt ends S c u) (hv : α ∉ usedAt ends S c v) :
    ProperOn ends (insert e₀ S) (Function.update c e₀ α) := by
  intro e₁ he₁ e₂ he₂ hne ⟨x, hx₁, hx₂⟩ hceq
  rw [mem_insert] at he₁ he₂
  rcases he₁ with rfl | he₁S <;> rcases he₂ with rfl | he₂S
  · exact hne rfl
  · rw [Function.update_self, Function.update_of_ne hne.symm] at hceq
    rw [huv, Sym2.mem_iff] at hx₁
    rcases hx₁ with rfl | rfl
    · exact hu ((mem_usedAt_iff ends S c x α).mpr ⟨e₂, he₂S, hx₂, hceq.symm⟩)
    · exact hv ((mem_usedAt_iff ends S c x α).mpr ⟨e₂, he₂S, hx₂, hceq.symm⟩)
  · rw [Function.update_of_ne hne, Function.update_self] at hceq
    rw [huv, Sym2.mem_iff] at hx₂
    rcases hx₂ with rfl | rfl
    · exact hu ((mem_usedAt_iff ends S c x α).mpr ⟨e₁, he₁S, hx₁, hceq⟩)
    · exact hv ((mem_usedAt_iff ends S c x α).mpr ⟨e₁, he₁S, hx₁, hceq⟩)
  · have hne1 : e₁ ≠ e₀ := fun h => he₀ (h ▸ he₁S)
    have hne2 : e₂ ≠ e₀ := fun h => he₀ (h ▸ he₂S)
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2] at hceq
    exact hprop e₁ he₁S e₂ he₂S hne ⟨x, hx₁, hx₂⟩ hceq

private lemma properOn_recolor {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} {S : Finset E} {c : E → Fin k}
    (hprop : ProperOn ends S c) {f : E} (_hf : f ∈ S) {u w : V}
    (hfw : ends f = s(u, w)) {γ : Fin k}
    (hu : γ ∉ usedAt ends S c u) (hw : γ ∉ usedAt ends S c w) :
    ProperOn ends S (Function.update c f γ) := by
  intro e₁ he₁ e₂ he₂ hne ⟨x, hx₁, hx₂⟩ hceq
  by_cases h1 : e₁ = f
  · subst h1
    rw [Function.update_self, Function.update_of_ne hne.symm] at hceq
    rw [hfw, Sym2.mem_iff] at hx₁
    rcases hx₁ with rfl | rfl
    · exact hu ((mem_usedAt_iff ends S c x γ).mpr ⟨e₂, he₂, hx₂, hceq.symm⟩)
    · exact hw ((mem_usedAt_iff ends S c x γ).mpr ⟨e₂, he₂, hx₂, hceq.symm⟩)
  · by_cases h2 : e₂ = f
    · subst h2
      rw [Function.update_of_ne h1, Function.update_self] at hceq
      rw [hfw, Sym2.mem_iff] at hx₂
      rcases hx₂ with rfl | rfl
      · exact hu ((mem_usedAt_iff ends S c x γ).mpr ⟨e₁, he₁, hx₁, hceq⟩)
      · exact hw ((mem_usedAt_iff ends S c x γ).mpr ⟨e₁, he₁, hx₁, hceq⟩)
    · rw [Function.update_of_ne h1, Function.update_of_ne h2] at hceq
      exact hprop e₁ he₁ e₂ he₂ hne ⟨x, hx₁, hx₂⟩ hceq

private lemma not_mem_usedAt_recolor_old {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} {S : Finset E} {c : E → Fin k}
    (hprop : ProperOn ends S c) {f : E} (hf : f ∈ S) {x : V}
    (hx : x ∈ ends f) {γ : Fin k} (hγ : γ ≠ c f) :
    c f ∉ usedAt ends S (Function.update c f γ) x := by
  rw [mem_usedAt_iff]
  rintro ⟨e, he, hxe, hce⟩
  by_cases hef : e = f
  · subst hef
    rw [Function.update_self] at hce
    exact hγ hce
  · rw [Function.update_of_ne hef] at hce
    exact hef (unique_edge_of_color ends hprop he hf hxe hx hce)

private lemma not_mem_usedAt_recolor_of_not_mem {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {k : ℕ} {S : Finset E} {c : E → Fin k}
    {x : V} {α γ : Fin k} (hno : α ∉ usedAt ends S c x) (hαγ : α ≠ γ)
    (f : E) : α ∉ usedAt ends S (Function.update c f γ) x := by
  rw [mem_usedAt_iff] at hno ⊢
  rintro ⟨e, he, hxe, hce⟩
  by_cases hef : e = f
  · subst hef
    rw [Function.update_self] at hce
    exact hαγ hce.symm
  · rw [Function.update_of_ne hef] at hce
    exact hno ⟨e, he, hxe, hce⟩

private def kempeGraph {V E : Type} (ends : E → Sym2 V) (S : Finset E)
    (c : E → Fin 4) (α β : Fin 4) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = α ∨ c e = β)
  symm := ⟨fun _ _ ⟨hne, e, he, hends, hc⟩ =>
    ⟨hne.symm, e, he, by rw [Sym2.eq_swap]; exact hends, hc⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

@[simp]
private lemma kempeGraph_adj {V E : Type} (ends : E → Sym2 V) (S : Finset E)
    (c : E → Fin 4) (α β : Fin 4) (x y : V) :
    (kempeGraph ends S c α β).Adj x y ↔
      x ≠ y ∧ ∃ e ∈ S, ends e = s(x, y) ∧ (c e = α ∨ c e = β) := Iff.rfl

open Classical in
private lemma kempe_card_neighborFinset_le_pair {V E : Type} [Fintype V] [DecidableEq V]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4}
    (hprop : ProperOn ends S c) (α β : Fin 4) (x : V) :
    ∃ T : Finset (Fin 4), T ⊆ {α, β} ∧
      (∀ γ ∈ T, ∃ e ∈ S, x ∈ ends e ∧ c e = γ) ∧
      ((kempeGraph ends S c α β).neighborFinset x).card ≤ T.card := by
  classical
  let G := kempeGraph ends S c α β
  let T : Finset (Fin 4) := ({α, β} : Finset (Fin 4)).filter
    (fun γ => ∃ y ∈ G.neighborFinset x, ∃ e ∈ S, ends e = s(x, y) ∧ c e = γ)
  refine ⟨T, Finset.filter_subset _ _, ?_, ?_⟩
  · intro γ hγ
    dsimp only [T] at hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨_, _, e, heS, hexy, hce⟩ := hγ.2
    exact ⟨e, heS, by rw [hexy]; simp, hce⟩
  · let pickColor : V → Fin 4 := fun y =>
      if h : G.Adj x y then c ((kempeGraph_adj ends S c α β x y).mp h).2.choose else 0
    have himg : (G.neighborFinset x).image pickColor ⊆ T := by
      intro γ hγ
      rw [Finset.mem_image] at hγ
      obtain ⟨y, hy, rfl⟩ := hγ
      have hadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      dsimp only [pickColor]
      rw [dif_pos hadj]
      set e := ((kempeGraph_adj ends S c α β x y).mp hadj).2.choose
      obtain ⟨heS, hexy, hce⟩ := ((kempeGraph_adj ends S c α β x y).mp hadj).2.choose_spec
      dsimp only [T]
      rw [Finset.mem_filter]
      exact ⟨by rcases hce with h | h <;> simp [e, h], ⟨y, hy, e, heS, hexy, rfl⟩⟩
    have hinj : Set.InjOn pickColor (G.neighborFinset x : Set V) := by
      intro y₁ hy₁ y₂ hy₂ hceq
      have h1 : y₁ ∈ G.neighborFinset x := hy₁
      have h2 : y₂ ∈ G.neighborFinset x := hy₂
      have hadj₁ : G.Adj x y₁ := (G.mem_neighborFinset x y₁).mp h1
      have hadj₂ : G.Adj x y₂ := (G.mem_neighborFinset x y₂).mp h2
      dsimp only [pickColor] at hceq
      rw [dif_pos hadj₁, dif_pos hadj₂] at hceq
      set e₁ := ((kempeGraph_adj ends S c α β x y₁).mp hadj₁).2.choose
      set e₂ := ((kempeGraph_adj ends S c α β x y₂).mp hadj₂).2.choose
      obtain ⟨he1S, he1xy, _⟩ := ((kempeGraph_adj ends S c α β x y₁).mp hadj₁).2.choose_spec
      obtain ⟨he2S, he2xy, _⟩ := ((kempeGraph_adj ends S c α β x y₂).mp hadj₂).2.choose_spec
      have hx1 : x ∈ ends e₁ := by rw [he1xy]; simp
      have hx2 : x ∈ ends e₂ := by rw [he2xy]; simp
      have heeq : e₁ = e₂ :=
        unique_edge_of_color ends hprop he1S he2S hx1 hx2 hceq
      have hsym : s(x, y₁) = s(x, y₂) :=
        he1xy.symm.trans ((congrArg ends heeq).trans he2xy)
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨_, rfl⟩ | ⟨_, hy1x⟩
      · rfl
      · exact (((kempeGraph_adj ends S c α β x y₁).mp hadj₁).1 hy1x.symm).elim
    calc (G.neighborFinset x).card
        = ((G.neighborFinset x).image pickColor).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ T.card := Finset.card_le_card himg

open Classical in
private lemma kempe_deg_le_two {V E : Type} [Fintype V] [DecidableEq V]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4}
    (hprop : ProperOn ends S c) (α β : Fin 4) (x : V) :
    ((kempeGraph ends S c α β).neighborFinset x).card ≤ 2 := by
  classical
  obtain ⟨T, hTsub, _, hcard⟩ := kempe_card_neighborFinset_le_pair ends hprop α β x
  calc ((kempeGraph ends S c α β).neighborFinset x).card ≤ T.card := hcard
    _ ≤ ({α, β} : Finset (Fin 4)).card := Finset.card_le_card hTsub
    _ ≤ 2 := Finset.card_le_two

open Classical in
private lemma kempe_deg_le_one_of_not_mem {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4}
    (hprop : ProperOn ends S c) {α β : Fin 4} {x : V}
    (hno : α ∉ usedAt ends S c x) :
    ((kempeGraph ends S c α β).neighborFinset x).card ≤ 1 := by
  classical
  obtain ⟨T, hTsub, hmem, hcard⟩ := kempe_card_neighborFinset_le_pair ends hprop α β x
  have hsub : T ⊆ {β} := by
    intro γ hγ
    have hγ' : γ ∈ ({α, β} : Finset (Fin 4)) := hTsub hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ' ⊢
    rcases hγ' with rfl | rfl
    · exfalso
      obtain ⟨e, heS, hx, hce⟩ := hmem _ hγ
      exact hno ((mem_usedAt_iff ends S c x _).mpr ⟨e, heS, hx, hce⟩)
    · rfl
  have hle1 : T.card ≤ ({β} : Finset (Fin 4)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hle1
  omega

open Classical in
private lemma kempe_deg_le_one_of_not_mem_right {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4}
    (hprop : ProperOn ends S c) {α β : Fin 4} {x : V}
    (hno : β ∉ usedAt ends S c x) :
    ((kempeGraph ends S c α β).neighborFinset x).card ≤ 1 := by
  classical
  have hnb : (kempeGraph ends S c α β).neighborFinset x =
      (kempeGraph ends S c β α).neighborFinset x := by
    ext y
    simp only [mem_neighborFinset, kempeGraph_adj, or_comm]
  rw [hnb]
  exact kempe_deg_le_one_of_not_mem ends hprop (α := β) (β := α) hno

open Classical in
private lemma path_internal_deg_ge_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {prev a b m : V} (r : G.Walk a b) (hr : r.IsPath)
    (hadj : G.Adj prev a) (hprev : prev ∉ r.support)
    (hm : m ∈ r.support) (hmb : m ≠ b) :
    2 ≤ (G.neighborFinset m).card := by
  classical
  induction r generalizing prev with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hm
    exact (hmb hm).elim
  | @cons a next b hadj_next r' ih =>
    rw [Walk.cons_isPath_iff] at hr
    obtain ⟨hr', ha_r'⟩ := hr
    simp only [Walk.support_cons, List.mem_cons] at hm hprev
    rcases hm with rfl | hm'
    · have h1 : prev ∈ G.neighborFinset m := (G.mem_neighborFinset m prev).mpr hadj.symm
      have h2 : next ∈ G.neighborFinset m := (G.mem_neighborFinset m next).mpr hadj_next
      have hne : prev ≠ next := fun h => hprev (Or.inr (h ▸ r'.start_mem_support))
      have hsub : ({prev, next} : Finset V) ⊆ G.neighborFinset m := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard : ({prev, next} : Finset V).card = 2 := Finset.card_pair hne
      calc 2 = ({prev, next} : Finset V).card := hcard.symm
        _ ≤ (G.neighborFinset m).card := Finset.card_le_card hsub
    · exact ih hr' hadj_next ha_r' hm' hmb

open Classical in
private lemma paths_overlap_of_deg_le_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdeg2 : ∀ x, (G.neighborFinset x).card ≤ 2)
    {prev a b c : V} (p : G.Walk a b) (q : G.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hadj : G.Adj prev a) (hp_prev : prev ∉ p.support) (hq_prev : prev ∉ q.support) :
    b ∈ q.support ∨ c ∈ p.support := by
  classical
  induction p generalizing prev with
  | nil =>
    left
    exact q.start_mem_support
  | @cons a x b hadj_x p' ih =>
    cases q with
    | nil =>
      right
      exact (Walk.cons hadj_x p').start_mem_support
    | @cons _ y _ hadj_y q' =>
      rw [Walk.cons_isPath_iff] at hp hq
      obtain ⟨hp', ha_p'⟩ := hp
      obtain ⟨hq', ha_q'⟩ := hq
      simp only [Walk.support_cons, List.mem_cons, not_or] at hp_prev hq_prev
      have hpx : prev ≠ x := fun h => hp_prev.2 (h ▸ p'.start_mem_support)
      have hqy : prev ≠ y := fun h => hq_prev.2 (h ▸ q'.start_mem_support)
      have hxy : x = y := by
        by_contra hne
        have h1 : prev ∈ G.neighborFinset a := (G.mem_neighborFinset a prev).mpr hadj.symm
        have h2 : x ∈ G.neighborFinset a := (G.mem_neighborFinset a x).mpr hadj_x
        have h3 : y ∈ G.neighborFinset a := (G.mem_neighborFinset a y).mpr hadj_y
        have hsub : ({prev, x, y} : Finset V) ⊆ G.neighborFinset a := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have hcard3 : ({prev, x, y} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
          simp [hpx, hqy]
        have hle := Finset.card_le_card hsub
        have hdeg := hdeg2 a
        omega
      subst hxy
      rcases ih q' hp' hq' hadj_x ha_p' ha_q' with hb | hc
      · left; simp [hb]
      · right; simp [hc]

open Classical in
private lemma not_three_deg_one_reachable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdeg2 : ∀ x, (G.neighborFinset x).card ≤ 2)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hdu : (G.neighborFinset u).card ≤ 1)
    (hdv : (G.neighborFinset v).card ≤ 1)
    (hdw : (G.neighborFinset w).card ≤ 1)
    (hruv : G.Reachable u v) (hruw : G.Reachable u w) : False := by
  classical
  obtain ⟨p, hp⟩ := hruv.exists_isPath
  obtain ⟨q, hq⟩ := hruw.exists_isPath
  cases p with
  | nil => exact huv rfl
  | @cons _ x _ hadj_x p' =>
    cases q with
    | nil => exact huw rfl
    | @cons _ y _ hadj_y q' =>
      rw [Walk.cons_isPath_iff] at hp hq
      obtain ⟨hp', hu_p'⟩ := hp
      obtain ⟨hq', hu_q'⟩ := hq
      have hxy : x = y := Finset.card_le_one.mp hdu x
        ((G.mem_neighborFinset u x).mpr hadj_x) y
        ((G.mem_neighborFinset u y).mpr hadj_y)
      subst hxy
      rcases paths_overlap_of_deg_le_two G hdeg2 p' q' hp' hq' hadj_x hu_p' hu_q' with hv | hw
      · have h2 := path_internal_deg_ge_two G q' hq' hadj_x hu_q' hv hvw
        omega
      · have h2 := path_internal_deg_ge_two G p' hp' hadj_x hu_p' hw hvw.symm
        omega

private def swapColor (α β x : Fin 4) : Fin 4 :=
  if x = α then β else if x = β then α else x

private lemma swapColor_inj (α β : Fin 4) : Function.Injective (swapColor α β) := by
  intro x y h
  dsimp only [swapColor] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  all_goals omega

private lemma swapColor_mem_pair {α β x : Fin 4} (hx : x = α ∨ x = β) :
    swapColor α β x = α ∨ swapColor α β x = β := by
  dsimp only [swapColor]
  rcases hx with rfl | rfl
  · simp
  · split_ifs <;> simp

private lemma swapColor_eq_of_ne {α β x : Fin 4} (h1 : x ≠ α) (h2 : x ≠ β) :
    swapColor α β x = x := by
  simp [swapColor, h1, h2]

private lemma swapColor_eq_left_iff {α β x : Fin 4} (hαβ : α ≠ β) :
    swapColor α β x = α ↔ x = β := by
  dsimp only [swapColor]
  split_ifs with h1 h2
  · subst h1; exact ⟨fun h => (hαβ h.symm).elim, fun h => (hαβ h).elim⟩
  · subst h2; simp
  · exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩

private noncomputable def kempeSwap {V E : Type} (ends : E → Sym2 V) (S : Finset E)
    (c : E → Fin 4) (α β : Fin 4) (z : V) (e : E) : Fin 4 :=
  letI := Classical.propDecidable
  if (c e = α ∨ c e = β) ∧ ∃ x ∈ ends e, (kempeGraph ends S c α β).Reachable z x then
    swapColor α β (c e)
  else c e

private lemma kempeSwap_reachable_iff {V E : Type} (ends : E → Sym2 V) (S : Finset E)
    (c : E → Fin 4) (α β : Fin 4) (z : V) {e : E} (he : e ∈ S)
    (hce : c e = α ∨ c e = β) {v : V} (hv : v ∈ ends e) :
    (∃ x ∈ ends e, (kempeGraph ends S c α β).Reachable z x) ↔
      (kempeGraph ends S c α β).Reachable z v := by
  let G := kempeGraph ends S c α β
  constructor
  · rintro ⟨x, hx, hzx⟩
    refine hzx.trans ?_
    by_cases hxv : x = v
    · subst hxv; exact Reachable.refl x
    · exact SimpleGraph.Adj.reachable ((kempeGraph_adj ends S c α β x v).mpr ⟨hxv, e, he, sym2_eq_of_ne_mem hxv hx hv, hce⟩)
  · intro hzv
    exact ⟨v, hv, hzv⟩

private lemma properOn_kempeSwap {V E : Type} (ends : E → Sym2 V) {S : Finset E}
    {c : E → Fin 4} (hprop : ProperOn ends S c) (α β : Fin 4) (z : V) :
    ProperOn ends S (kempeSwap ends S c α β z) := by
  classical
  let G := kempeGraph ends S c α β
  intro e₁ he₁ e₂ he₂ hne ⟨v, hv₁, hv₂⟩ hceq
  have h1 := hprop e₁ he₁ e₂ he₂ hne ⟨v, hv₁, hv₂⟩
  dsimp only [kempeSwap] at hceq
  by_cases hc1 : c e₁ = α ∨ c e₁ = β <;> by_cases hc2 : c e₂ = α ∨ c e₂ = β
  · rw [kempeSwap_reachable_iff ends S c α β z he₁ hc1 hv₁,
        kempeSwap_reachable_iff ends S c α β z he₂ hc2 hv₂] at hceq
    by_cases hzv : G.Reachable z v
    · rw [if_pos ⟨hc1, hzv⟩, if_pos ⟨hc2, hzv⟩] at hceq
      exact h1 (swapColor_inj α β hceq)
    · rw [if_neg (fun h => hzv h.2), if_neg (fun h => hzv h.2)] at hceq
      exact h1 hceq
  · have hleft : kempeSwap ends S c α β z e₁ = α ∨ kempeSwap ends S c α β z e₁ = β := by
      dsimp only [kempeSwap]
      split_ifs with hp
      · exact swapColor_mem_pair hc1
      · exact hc1
    have hright : kempeSwap ends S c α β z e₂ = c e₂ := by
      dsimp only [kempeSwap]
      rw [if_neg (fun h => hc2 h.1)]
    have hceq' : kempeSwap ends S c α β z e₁ = kempeSwap ends S c α β z e₂ := hceq
    rw [hright] at hceq'
    rw [hceq'] at hleft
    exact hc2 hleft
  · have hright : kempeSwap ends S c α β z e₂ = α ∨ kempeSwap ends S c α β z e₂ = β := by
      dsimp only [kempeSwap]
      split_ifs with hp
      · exact swapColor_mem_pair hc2
      · exact hc2
    have hleft : kempeSwap ends S c α β z e₁ = c e₁ := by
      dsimp only [kempeSwap]
      rw [if_neg (fun h => hc1 h.1)]
    have hceq' : kempeSwap ends S c α β z e₁ = kempeSwap ends S c α β z e₂ := hceq
    rw [hleft] at hceq'
    rw [← hceq'] at hright
    exact hc1 hright
  · simp only [hc1, hc2, false_and, ↓reduceIte] at hceq
    exact h1 hceq

private lemma usedAt_kempeSwap_of_not_reachable {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4} {α β : Fin 4} {z x : V}
    (hnr : ¬ (kempeGraph ends S c α β).Reachable z x) :
    usedAt ends S (kempeSwap ends S c α β z) x = usedAt ends S c x := by
  ext γ
  simp only [mem_usedAt_iff]
  constructor
  · rintro ⟨e, heS, hxe, rfl⟩
    refine ⟨e, heS, hxe, ?_⟩
    dsimp only [kempeSwap]
    split_ifs with hcond
    · exfalso
      have := (kempeSwap_reachable_iff ends S c α β z heS hcond.1 hxe).mp hcond.2
      exact hnr this
    · rfl
  · rintro ⟨e, heS, hxe, rfl⟩
    refine ⟨e, heS, hxe, ?_⟩
    dsimp only [kempeSwap]
    split_ifs with hcond
    · exfalso
      have := (kempeSwap_reachable_iff ends S c α β z heS hcond.1 hxe).mp hcond.2
      exact hnr this
    · rfl

private lemma not_mem_usedAt_kempeSwap_self {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4} {α β : Fin 4}
    (hαβ : α ≠ β) {z : V} (hno : β ∉ usedAt ends S c z) :
    α ∉ usedAt ends S (kempeSwap ends S c α β z) z := by
  rw [mem_usedAt_iff] at hno ⊢
  rintro ⟨e, heS, hze, hce⟩
  dsimp only [kempeSwap] at hce
  split_ifs at hce with hcond
  · have hβ : c e = β := (swapColor_eq_left_iff hαβ).mp hce
    exact hno ⟨e, heS, hze, hβ⟩
  · have hreach : ∃ y ∈ ends e, (kempeGraph ends S c α β).Reachable z y :=
      ⟨z, hze, Reachable.refl z⟩
    have hnot : ¬ (c e = α ∨ c e = β) := fun hc => hcond ⟨hc, hreach⟩
    exact hnot (Or.inl hce)

private lemma kempeSwap_eq_of_ne {V E : Type} (ends : E → Sym2 V) (S : Finset E)
    (c : E → Fin 4) {α β : Fin 4} {z₀ : V} (f : E)
    (h1 : c f ≠ α) (h2 : c f ≠ β) :
    kempeSwap ends S c α β z₀ f = c f := by
  dsimp only [kempeSwap]
  rw [if_neg (fun h => h.1.elim h1 h2)]

private lemma usedAt_kempeSwap_ne_of_not_mem {V E : Type} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) {S : Finset E} {c : E → Fin 4} {α β γ : Fin 4}
    (hγα : γ ≠ α) (hγβ : γ ≠ β) {z x : V} (hno : γ ∉ usedAt ends S c x) :
    γ ∉ usedAt ends S (kempeSwap ends S c α β z) x := by
  rw [mem_usedAt_iff] at hno ⊢
  rintro ⟨e, heS, hxe, hce⟩
  dsimp only [kempeSwap] at hce
  split_ifs at hce with hcond
  · have hmem := swapColor_mem_pair hcond.1
    rw [hce] at hmem
    exact hmem.elim hγα hγβ
  · exact hno ⟨e, heS, hxe, hce⟩

open Classical in
private lemma color_three_step_reach_alpha {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    {S : Finset E} {c : E → Fin 4} (hprop : ProperOn ends S c)
    {u v w : V} {f : E} {α γ : Fin 4} (hf : f ∈ S) (hfuw : ends f = s(u, w)) (hcf : c f = γ)
    (_hαγ : α ≠ γ)
    (hno_u : α ∉ usedAt ends S c u) (hwv : w ≠ v) (huv : u ≠ v)
    (hreach : (kempeGraph ends S c α γ).Reachable v u) :
    α ∈ usedAt ends S c w := by
  classical
  let G := kempeGraph ends S c α γ
  obtain ⟨p, hp⟩ := hreach.symm.exists_isPath
  cases p with
  | nil => exact (huv rfl).elim
  | @cons _ x _ hadj_x p' =>
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨hp', hu_p'⟩ := hp
    rw [kempeGraph_adj] at hadj_x
    obtain ⟨_, e₁, he1S, he1ux, hc1⟩ := hadj_x
    have hc1γ : c e₁ = γ := by
      rcases hc1 with h | h
      · exfalso
        exact hno_u ((mem_usedAt_iff ends S c u α).mpr ⟨e₁, he1S, by rw [he1ux]; simp, h⟩)
      · exact h
    have he1f : e₁ = f := by
      apply unique_edge_of_color ends hprop he1S hf (x := u)
      · rw [he1ux]; simp
      · rw [hfuw]; simp
      · rw [hc1γ, hcf]
    have hxw : x = w := by
      have hsym : s(u, x) = s(u, w) := by rw [← he1ux, ← hfuw, he1f]
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨_, h⟩ | ⟨huw, _⟩
      · exact h
      · exfalso
        have : (ends f).IsDiag := by rw [hfuw, huw]; simp
        exact hloop f this
    subst x
    cases p' with
    | nil => exact (hwv rfl).elim
    | @cons _ y _ hadj_y p'' =>
      rw [kempeGraph_adj] at hadj_y
      obtain ⟨hwy, e₂, he2S, he2wy, hc2⟩ := hadj_y
      have hy_mem : y ∈ (Walk.cons hadj_y p'').support := by
        simp [Walk.support_cons, p''.start_mem_support]
      have hyu : y ≠ u := fun h => hu_p' (h ▸ hy_mem)
      have he2f : e₂ ≠ f := by
        intro heq
        have hsym : s(w, y) = s(u, w) := by rw [← he2wy, ← hfuw, heq]
        rw [Sym2.eq_iff] at hsym
        rcases hsym with ⟨h_wu, _⟩ | ⟨_, h_yu⟩
        · have : (ends f).IsDiag := by rw [hfuw, h_wu]; simp
          exact hloop f this
        · exact hyu h_yu
      have hw1 : w ∈ ends e₂ := by rw [he2wy]; simp
      have hw2 : w ∈ ends f := by rw [hfuw]; simp
      have hc2ne : c e₂ ≠ c f := hprop e₂ he2S f hf he2f ⟨w, hw1, hw2⟩
      rw [hcf] at hc2ne
      have hc2α : c e₂ = α := hc2.elim id (fun h => (hc2ne h).elim)
      exact (mem_usedAt_iff ends S c w α).mpr ⟨e₂, he2S, hw1, hc2α⟩

open Classical in
private lemma exists_coloring_three {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hdeg : ∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ 3) :
    ∀ S : Finset E, ∃ c : E → Fin 4, ProperOn ends S c := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, fun _ h => by simp at h⟩
  | @insert e₀ S he₀ ih =>
    obtain ⟨c, hprop⟩ := ih
    obtain ⟨u, v, huv, he0uv⟩ := sym2_eq_pair (hloop e₀)
    have hdeg_le_two : ∀ z ∈ ends e₀, (S.filter fun e => z ∈ ends e).card ≤ 2 := by
      intro z hz
      have hss : S.filter (fun e => z ∈ ends e) ⊂ Finset.univ.filter (fun e => z ∈ ends e) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, hz⟩, fun h => he₀ (Finset.mem_filter.mp h).1⟩
        · intro e he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, (Finset.mem_filter.mp he).2⟩
      have hlt := Finset.card_lt_card hss
      have hle := hdeg z
      omega
    have hu_in : u ∈ ends e₀ := by rw [he0uv]; simp
    have hv_in : v ∈ ends e₀ := by rw [he0uv]; simp
    have hu_card : (usedAt ends S c u).card ≤ 2 :=
      (card_usedAt_le ends S c u).trans (hdeg_le_two u hu_in)
    have hv_card : (usedAt ends S c v).card ≤ 2 :=
      (card_usedAt_le ends S c v).trans (hdeg_le_two v hv_in)
    by_cases hcommon : ∃ α : Fin 4, α ∉ usedAt ends S c u ∧ α ∉ usedAt ends S c v
    · obtain ⟨α, hαu, hαv⟩ := hcommon
      exact ⟨Function.update c e₀ α, properOn_update_insert ends hprop he₀ he0uv hαu hαv⟩
    · push Not at hcommon
      have hunion_univ : usedAt ends S c u ∪ usedAt ends S c v = Finset.univ := by
        ext α
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases h : α ∈ usedAt ends S c u
        · exact Or.inl h
        · exact Or.inr (hcommon α h)
      have hcu_inter := Finset.card_union_add_card_inter (usedAt ends S c u) (usedAt ends S c v)
      rw [hunion_univ, Finset.card_univ, Fintype.card_fin] at hcu_inter
      have hdisj : Disjoint (usedAt ends S c u) (usedAt ends S c v) := by
        rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
        omega
      have hu2 : (usedAt ends S c u).card = 2 := by omega
      have hv2 : (usedAt ends S c v).card = 2 := by omega
      obtain ⟨γ, δ, hγδ, hU_eq⟩ := Finset.card_eq_two.mp hu2
      obtain ⟨α, β, hαβ, hV_eq⟩ := Finset.card_eq_two.mp hv2
      have hγu : γ ∈ usedAt ends S c u := by rw [hU_eq]; simp
      have hδu : δ ∈ usedAt ends S c u := by rw [hU_eq]; simp
      have hαv : α ∈ usedAt ends S c v := by rw [hV_eq]; simp
      have hβv : β ∈ usedAt ends S c v := by rw [hV_eq]; simp
      have hαγ : α ≠ γ := fun h => Finset.disjoint_left.mp hdisj (h ▸ hγu) hαv
      have hαδ : α ≠ δ := fun h => Finset.disjoint_left.mp hdisj (h ▸ hδu) hαv
      have hβγ : β ≠ γ := fun h => Finset.disjoint_left.mp hdisj (h ▸ hγu) hβv
      have hβδ : β ≠ δ := fun h => Finset.disjoint_left.mp hdisj (h ▸ hδu) hβv
      have hno_αu : α ∉ usedAt ends S c u := fun h => Finset.disjoint_left.mp hdisj h hαv
      have hno_βu : β ∉ usedAt ends S c u := fun h => Finset.disjoint_left.mp hdisj h hβv
      have hno_γv : γ ∉ usedAt ends S c v := fun h => Finset.disjoint_right.mp hdisj h hγu
      have hno_δv : δ ∉ usedAt ends S c v := fun h => Finset.disjoint_right.mp hdisj h hδu
      let Gαγ := kempeGraph ends S c α γ
      by_cases hreach1 : Gαγ.Reachable v u
      · obtain ⟨f, hfS, hfu, hcf⟩ := (mem_usedAt_iff ends S c u γ).mp hγu
        obtain ⟨x₀, y₀, hx0y0, hfxy⟩ := sym2_eq_pair (hloop f)
        have hwf : ∃ w : V, w ≠ u ∧ ends f = s(u, w) := by
          have hu_f := hfu
          rw [hfxy, Sym2.mem_iff] at hu_f
          rcases hu_f with rfl | rfl
          · exact ⟨y₀, hx0y0.symm, hfxy⟩
          · exact ⟨x₀, hx0y0, by rw [hfxy, Sym2.eq_swap]⟩
        obtain ⟨w, hwu, hfuw⟩ := hwf
        have hwv : w ≠ v := by
          intro h
          subst h
          have : γ ∈ usedAt ends S c w := (mem_usedAt_iff ends S c w γ).mpr
            ⟨f, hfS, by rw [hfuw]; simp, hcf⟩
          exact hno_γv this
        have hαw : α ∈ usedAt ends S c w :=
          color_three_step_reach_alpha ends hloop hprop hfS hfuw hcf hαγ hno_αu hwv huv hreach1
        have hγw : γ ∈ usedAt ends S c w := (mem_usedAt_iff ends S c w γ).mpr
          ⟨f, hfS, by rw [hfuw]; simp, hcf⟩
        have hw_card : (usedAt ends S c w).card ≤ 3 :=
          (card_usedAt_le ends S c w).trans
            ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))).trans (hdeg w))
        by_cases hβw : β ∈ usedAt ends S c w
        · have hno_δw : δ ∉ usedAt ends S c w := by
            intro hδw
            have hsub : ({α, β, γ, δ} : Finset (Fin 4)) ⊆ usedAt ends S c w := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl | rfl <;> assumption
            have h4 : ({α, β, γ, δ} : Finset (Fin 4)).card = 4 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                  Finset.card_pair hγδ]
              · simp [hβγ, hβδ]
              · simp [hαβ, hαγ, hαδ]
            have hle := Finset.card_le_card hsub
            omega
          let Gαδ := kempeGraph ends S c α δ
          by_cases hreach2 : Gαδ.Reachable v u
          · have hdeg2 : ∀ x, (Gαδ.neighborFinset x).card ≤ 2 :=
              kempe_deg_le_two ends hprop α δ
            have hdu : (Gαδ.neighborFinset u).card ≤ 1 :=
              kempe_deg_le_one_of_not_mem ends hprop hno_αu
            have hdv : (Gαδ.neighborFinset v).card ≤ 1 :=
              kempe_deg_le_one_of_not_mem_right ends hprop hno_δv
            have hdw : (Gαδ.neighborFinset w).card ≤ 1 :=
              kempe_deg_le_one_of_not_mem_right ends hprop hno_δw
            have hnr_wu : ¬ Gαδ.Reachable w u := by
              intro hwu_r
              exact not_three_deg_one_reachable Gαδ hdeg2 huv hwu.symm hwv.symm hdu hdv hdw
                hreach2.symm hwu_r.symm
            have hnr_wv : ¬ Gαδ.Reachable w v := by
              intro hwv_r
              exact hnr_wu (hwv_r.trans hreach2)
            let c' := kempeSwap ends S c α δ w
            have hprop' : ProperOn ends S c' := properOn_kempeSwap ends hprop α δ w
            have hno_αu' : α ∉ usedAt ends S c' u := by
              rw [usedAt_kempeSwap_of_not_reachable ends hnr_wu]
              exact hno_αu
            have hno_αw' : α ∉ usedAt ends S c' w :=
              not_mem_usedAt_kempeSwap_self ends hαδ hno_δw
            have hcf' : c' f = γ :=
              (kempeSwap_eq_of_ne ends S c (z₀ := w) f (by rw [hcf]; exact hαγ.symm)
                (by rw [hcf]; exact hγδ)).trans hcf
            have hno_γv' : γ ∉ usedAt ends S c' v := by
              rw [usedAt_kempeSwap_of_not_reachable ends hnr_wv]
              exact hno_γv
            let c'' := Function.update c' f α
            have hprop'' : ProperOn ends S c'' := properOn_recolor ends hprop' hfS hfuw hno_αu' hno_αw'
            have hno_γu'' : γ ∉ usedAt ends S c'' u := by
              rw [← hcf']
              exact not_mem_usedAt_recolor_old ends hprop' hfS hfu (by rw [hcf']; exact hαγ)
            have hno_γv'' : γ ∉ usedAt ends S c'' v :=
              not_mem_usedAt_recolor_of_not_mem ends hno_γv' hαγ.symm f
            exact ⟨Function.update c'' e₀ γ,
              properOn_update_insert ends hprop'' he₀ he0uv hno_γu'' hno_γv''⟩
          · let c' := kempeSwap ends S c α δ v
            have hprop' : ProperOn ends S c' := properOn_kempeSwap ends hprop α δ v
            have hno_αu' : α ∉ usedAt ends S c' u := by
              rw [usedAt_kempeSwap_of_not_reachable ends hreach2]
              exact hno_αu
            have hno_αv' : α ∉ usedAt ends S c' v :=
              not_mem_usedAt_kempeSwap_self ends hαδ hno_δv
            exact ⟨Function.update c' e₀ α,
              properOn_update_insert ends hprop' he₀ he0uv hno_αu' hno_αv'⟩
        · let c' := Function.update c f β
          have hprop' : ProperOn ends S c' := properOn_recolor ends hprop hfS hfuw hno_βu hβw
          have hno_γu' : γ ∉ usedAt ends S c' u := by
            rw [← hcf]
            exact not_mem_usedAt_recolor_old ends hprop hfS hfu (by rw [hcf]; exact hβγ)
          have hno_γv' : γ ∉ usedAt ends S c' v :=
            not_mem_usedAt_recolor_of_not_mem ends hno_γv hβγ.symm f
          exact ⟨Function.update c' e₀ γ,
            properOn_update_insert ends hprop' he₀ he0uv hno_γu' hno_γv'⟩
      · let c' := kempeSwap ends S c α γ v
        have hprop' : ProperOn ends S c' := properOn_kempeSwap ends hprop α γ v
        have hno_αu' : α ∉ usedAt ends S c' u := by
          rw [usedAt_kempeSwap_of_not_reachable ends hreach1]
          exact hno_αu
        have hno_αv' : α ∉ usedAt ends S c' v :=
          not_mem_usedAt_kempeSwap_self ends hαγ hno_γv
        exact ⟨Function.update c' e₀ α,
          properOn_update_insert ends hprop' he₀ he0uv hno_αu' hno_αv'⟩

private lemma exists_coloring_two {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hdeg : ∀ v : V, (Finset.univ.filter fun e => v ∈ ends e).card ≤ 2) :
    ∀ S : Finset E, ∃ c : E → Fin 3, ProperOn ends S c := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ h => by simp at h⟩
  | @insert e₀ S he₀ ih =>
    obtain ⟨c, hprop⟩ := ih
    obtain ⟨u, v, _, he0uv⟩ := sym2_eq_pair (hloop e₀)
    have hdeg_le_one : ∀ z ∈ ends e₀, (S.filter fun e => z ∈ ends e).card ≤ 1 := by
      intro z hz
      have hss : S.filter (fun e => z ∈ ends e) ⊂ Finset.univ.filter (fun e => z ∈ ends e) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, hz⟩, fun h => he₀ (Finset.mem_filter.mp h).1⟩
        · intro e he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, (Finset.mem_filter.mp he).2⟩
      have hlt := Finset.card_lt_card hss
      have hle := hdeg z
      omega
    have hu_card : (usedAt ends S c u).card ≤ 1 :=
      (card_usedAt_le ends S c u).trans (hdeg_le_one u (by rw [he0uv]; simp))
    have hv_card : (usedAt ends S c v).card ≤ 1 :=
      (card_usedAt_le ends S c v).trans (hdeg_le_one v (by rw [he0uv]; simp))
    have hlt : (usedAt ends S c u ∪ usedAt ends S c v).card < (Finset.univ : Finset (Fin 3)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_union_le (usedAt ends S c u) (usedAt ends S c v)
      omega
    have hne : (Finset.univ \ (usedAt ends S c u ∪ usedAt ends S c v)).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; omega)
    obtain ⟨α, hα⟩ := hne
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hα
    exact ⟨Function.update c e₀ α,
      properOn_update_insert ends hprop he₀ he0uv hα.2.1 hα.2.2⟩

end ShannonH1

theorem OMA.solution : OMA.R_opg_seymours_r_graph_conjecture_R1.H1 := by
  classical
  intro V E _ _ _ ends hloop d hd hdeg
  have hcase : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · have hemp : IsEmpty E := ⟨fun e => by
      obtain ⟨u, _, _, heu⟩ := ShannonH1.sym2_eq_pair (hloop e)
      have hm : e ∈ Finset.univ.filter fun e' => u ∈ ends e' :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ e, by rw [heu]; simp⟩
      have hpos : 0 < (Finset.univ.filter fun e' => u ∈ ends e').card :=
        Finset.card_pos.mpr ⟨e, hm⟩
      have h0 := hdeg u
      omega⟩
    exact ⟨fun e => (hemp.false e).elim, fun e => (hemp.false e).elim⟩
  · refine ⟨fun _ => (0 : Fin (3 * 1 / 2)), ?_⟩
    intro e f hne ⟨v, hve, hvf⟩
    exfalso
    have hsub : ({e, f} : Finset E) ⊆ Finset.univ.filter fun e' => v ∈ ends e' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hve, hvf]
    have h2 : 2 = ({e, f} : Finset E).card := (Finset.card_pair hne).symm
    have hle := Finset.card_le_card hsub
    have h1 := hdeg v
    omega
  · obtain ⟨c, hc⟩ := ShannonH1.exists_coloring_two ends hloop hdeg Finset.univ
    refine ⟨c, fun e f hne hv => hc e (Finset.mem_univ e) f (Finset.mem_univ f) hne hv⟩
  · obtain ⟨c, hc⟩ := ShannonH1.exists_coloring_three ends hloop hdeg Finset.univ
    refine ⟨c, fun e f hne hv => hc e (Finset.mem_univ e) f (Finset.mem_univ f) hne hv⟩
