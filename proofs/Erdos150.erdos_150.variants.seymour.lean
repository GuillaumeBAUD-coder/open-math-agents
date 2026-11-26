import FormalConjectures.ErdosProblems.«150»

/-! A minimal cut chooses one internal vertex from each of the four-edge paths. -/

open SimpleGraph

abbrev OMA.seymour_vertices (m : ℕ) := Fin 2 ⊕ (Fin m × Fin 3)

abbrev OMA.seymour_pole (m : ℕ) (p : Fin 2) : OMA.seymour_vertices m := Sum.inl p

abbrev OMA.seymour_internal {m : ℕ} (i : Fin m) (j : Fin 3) : OMA.seymour_vertices m :=
  Sum.inr (i, j)

def OMA.seymour_graph (m : ℕ) : SimpleGraph (OMA.seymour_vertices m) where
  Adj a b := match a, b with
    | .inl _, .inl _ => False
    | .inl p, .inr x => x.2.val = 2 * p.val
    | .inr x, .inl p => x.2.val = 2 * p.val
    | .inr x, .inr y => x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)
  symm := ⟨by
    intro a b
    cases a <;> cases b
    · exact id
    · exact id
    · exact id
    · rintro ⟨hi, hj⟩
      exact ⟨hi.symm, hj.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

def OMA.seymour_cut {m : ℕ} (f : Fin m → Fin 3) : Set (OMA.seymour_vertices m) :=
  Set.range fun i => OMA.seymour_internal i (f i)

lemma OMA.seymour_internal_mem {m : ℕ} {f : Fin m → Fin 3} {i : Fin m} {j : Fin 3} :
    OMA.seymour_internal i j ∈ OMA.seymour_cut f ↔ j = f i := by
  constructor
  · rintro ⟨k, hk⟩
    have h := Prod.mk.inj (Sum.inr.inj hk)
    obtain ⟨rfl, h⟩ := h
    exact h.symm
  · rintro rfl
    exact ⟨i, rfl⟩

lemma OMA.seymour_pole_not_mem {m : ℕ} (f : Fin m → Fin 3) (p : Fin 2) :
    OMA.seymour_pole m p ∉ OMA.seymour_cut f := by
  rintro ⟨i, hi⟩
  cases hi

def OMA.seymour_left_side {m : ℕ} (f : Fin m → Fin 3) (p : OMA.seymour_vertices m) : Prop :=
  match p with
  | .inl s => s = 0
  | .inr x => x.2 < f x.1

lemma OMA.seymour_pole_side {m : ℕ} {f : Fin m → Fin 3} (p : Fin 2) (i : Fin m)
    (j : Fin 3) (hj : j.val = 2 * p.val) (hne : j ≠ f i) :
    p = 0 ↔ j < f i := by
  have hh : p = 0 ↔ p.val = 0 := by
    constructor
    · rintro rfl
      rfl
    · intro h
      exact Fin.ext h
  rw [hh]
  change p.val = 0 ↔ j.val < (f i).val
  have hp := p.isLt
  have hJ := j.isLt
  have hf := (f i).isLt
  have h' : j.val ≠ (f i).val := fun h => hne (Fin.ext h)
  omega

lemma OMA.seymour_side_adj {m : ℕ} {f : Fin m → Fin 3} {x y : OMA.seymour_vertices m}
    (hx : x ∉ OMA.seymour_cut f) (hy : y ∉ OMA.seymour_cut f)
    (hxy : (OMA.seymour_graph m).Adj x y) :
    OMA.seymour_left_side f x ↔ OMA.seymour_left_side f y := by
  cases x with
  | inl p =>
    cases y with
    | inl q => exact False.elim hxy
    | inr q =>
      obtain ⟨i, j⟩ := q
      exact OMA.seymour_pole_side p i j hxy (fun he => hy (OMA.seymour_internal_mem.mpr he))
  | inr p =>
    obtain ⟨i, j⟩ := p
    cases y with
    | inl q =>
      exact (OMA.seymour_pole_side q i j hxy (fun he => hx (OMA.seymour_internal_mem.mpr he))).symm
    | inr q =>
      obtain ⟨k, l⟩ := q
      have h : i = k ∧ (j.val + 1 = l.val ∨ l.val + 1 = j.val) := hxy
      obtain ⟨rfl, hstep⟩ := h
      have hj : j.val ≠ (f i).val := fun he => hx (OMA.seymour_internal_mem.mpr (Fin.ext he))
      have hl : l.val ≠ (f i).val := fun he => hy (OMA.seymour_internal_mem.mpr (Fin.ext he))
      change j.val < (f i).val ↔ l.val < (f i).val
      omega

lemma OMA.seymour_not_preconnected {m : ℕ} (f : Fin m → Fin 3) :
    ¬ ((OMA.seymour_graph m).induce (OMA.seymour_cut f)ᶜ).Preconnected := by
  intro h
  let G' := (OMA.seymour_graph m).induce (OMA.seymour_cut f)ᶜ
  let L : ↥((OMA.seymour_cut f)ᶜ) := ⟨OMA.seymour_pole m 0, OMA.seymour_pole_not_mem f 0⟩
  let R : ↥((OMA.seymour_cut f)ᶜ) := ⟨OMA.seymour_pole m 1, OMA.seymour_pole_not_mem f 1⟩
  have hwalk {x y : ↥((OMA.seymour_cut f)ᶜ)} (p : G'.Walk x y) :
      OMA.seymour_left_side f x.val → OMA.seymour_left_side f y.val := by
    induction p with
    | nil => exact id
    | @cons a b _ hadj _ ih =>
      intro hleft
      have ha : a.val ∉ OMA.seymour_cut f := (Set.mem_compl_iff _ _).mp a.property
      have hb : b.val ∉ OMA.seymour_cut f := (Set.mem_compl_iff _ _).mp b.property
      change (OMA.seymour_graph m).Adj a.val b.val at hadj
      exact ih ((OMA.seymour_side_adj ha hb hadj).mp hleft)
  obtain ⟨w⟩ := h L R
  have hL : OMA.seymour_left_side f L.val := by rfl
  have hR : OMA.seymour_left_side f R.val := hwalk w hL
  have impossible : (1 : Fin 2) = 0 := hR
  exact (by decide : (1 : Fin 2) ≠ 0) impossible

lemma OMA.seymour_reachable_adj {m : ℕ} (S : Set (OMA.seymour_vertices m))
    {x y : OMA.seymour_vertices m} (hx : x ∉ S) (hy : y ∉ S)
    (h : (OMA.seymour_graph m).Adj x y) :
    ((OMA.seymour_graph m).induce Sᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  (show ((OMA.seymour_graph m).induce Sᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from h).reachable

lemma OMA.seymour_from_left {m : ℕ} (S : Set (OMA.seymour_vertices m)) (i : Fin m) (j : Fin 3)
    (hL : OMA.seymour_pole m 0 ∉ S)
    (h : ∀ k : Fin 3, k ≤ j → OMA.seymour_internal i k ∉ S) :
    ((OMA.seymour_graph m).induce Sᶜ).Reachable
      ⟨OMA.seymour_pole m 0, hL⟩ ⟨OMA.seymour_internal i j, h j le_rfl⟩ := by
  have e0 (h0 : OMA.seymour_internal i 0 ∉ S) :=
    OMA.seymour_reachable_adj S hL h0 (by
      change (0 : Fin 3).val = 2 * (0 : Fin 2).val
      decide)
  have e1 (h0 : OMA.seymour_internal i 0 ∉ S) (h1 : OMA.seymour_internal i 1 ∉ S) :=
    OMA.seymour_reachable_adj S h0 h1 (by
      change i = i ∧ ((0 : Fin 3).val + 1 = (1 : Fin 3).val ∨ (1 : Fin 3).val + 1 = (0 : Fin 3).val)
      exact ⟨rfl, Or.inl rfl⟩)
  have e2 (h1 : OMA.seymour_internal i 1 ∉ S) (h2 : OMA.seymour_internal i 2 ∉ S) :=
    OMA.seymour_reachable_adj S h1 h2 (by
      change i = i ∧ ((1 : Fin 3).val + 1 = (2 : Fin 3).val ∨ (2 : Fin 3).val + 1 = (1 : Fin 3).val)
      exact ⟨rfl, Or.inl rfl⟩)
  fin_cases j
  · exact e0 (h 0 (by decide))
  · exact (e0 (h 0 (by decide))).trans (e1 (h 0 (by decide)) (h 1 (by decide)))
  · exact ((e0 (h 0 (by decide))).trans (e1 (h 0 (by decide)) (h 1 (by decide)))).trans
      (e2 (h 1 (by decide)) (h 2 (by decide)))

lemma OMA.seymour_from_right {m : ℕ} (S : Set (OMA.seymour_vertices m)) (i : Fin m) (j : Fin 3)
    (hR : OMA.seymour_pole m 1 ∉ S)
    (h : ∀ k : Fin 3, j ≤ k → OMA.seymour_internal i k ∉ S) :
    ((OMA.seymour_graph m).induce Sᶜ).Reachable
      ⟨OMA.seymour_pole m 1, hR⟩ ⟨OMA.seymour_internal i j, h j le_rfl⟩ := by
  have e2 (h2 : OMA.seymour_internal i 2 ∉ S) :=
    OMA.seymour_reachable_adj S hR h2 (by
      change (2 : Fin 3).val = 2 * (1 : Fin 2).val
      decide)
  have e1 (h2 : OMA.seymour_internal i 2 ∉ S) (h1 : OMA.seymour_internal i 1 ∉ S) :=
    OMA.seymour_reachable_adj S h2 h1 (by
      change i = i ∧ ((2 : Fin 3).val + 1 = (1 : Fin 3).val ∨ (1 : Fin 3).val + 1 = (2 : Fin 3).val)
      exact ⟨rfl, Or.inr rfl⟩)
  have e0 (h1 : OMA.seymour_internal i 1 ∉ S) (h0 : OMA.seymour_internal i 0 ∉ S) :=
    OMA.seymour_reachable_adj S h1 h0 (by
      change i = i ∧ ((1 : Fin 3).val + 1 = (0 : Fin 3).val ∨ (0 : Fin 3).val + 1 = (1 : Fin 3).val)
      exact ⟨rfl, Or.inr rfl⟩)
  fin_cases j
  · exact ((e2 (h 2 (by decide))).trans (e1 (h 2 (by decide)) (h 1 (by decide)))).trans
      (e0 (h 1 (by decide)) (h 0 (by decide)))
  · exact (e2 (h 2 (by decide))).trans (e1 (h 2 (by decide)) (h 1 (by decide)))
  · exact e2 (h 2 (by decide))

lemma OMA.seymour_proper_preconnected {m : ℕ} (f : Fin m → Fin 3) (S : Set (OMA.seymour_vertices m))
    (hS : S ⊂ OMA.seymour_cut f) : ((OMA.seymour_graph m).induce Sᶜ).Preconnected := by
  have hL : OMA.seymour_pole m 0 ∉ S := fun hp => OMA.seymour_pole_not_mem f 0 (hS.le hp)
  have hR : OMA.seymour_pole m 1 ∉ S := fun hp => OMA.seymour_pole_not_mem f 1 (hS.le hp)
  let A := (OMA.seymour_graph m).induce Sᶜ
  let L : ↥(Sᶜ) := ⟨OMA.seymour_pole m 0, hL⟩
  let R : ↥(Sᶜ) := ⟨OMA.seymour_pole m 1, hR⟩
  have hFree (i : Fin m) (k : Fin 3) (hk : k ≠ f i) : OMA.seymour_internal i k ∉ S :=
    fun hp => hk (OMA.seymour_internal_mem.mp (hS.le hp))
  have hWhole (i : Fin m) (hOmitted : OMA.seymour_internal i (f i) ∉ S) (k : Fin 3) :
      OMA.seymour_internal i k ∉ S := by
    by_cases he : k = f i
    · simpa only [he] using hOmitted
    · exact hFree i k he
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Set.exists_of_ssubset hS
  have hAcross : A.Reachable L R :=
    (OMA.seymour_from_left S i 2 hL (fun k _ => hWhole i hi k)).trans
      (OMA.seymour_from_right S i 2 hR (fun k _ => hWhole i hi k)).symm
  have hFromL (a : ↥(Sᶜ)) : A.Reachable L a := by
    obtain ⟨a, ha⟩ := a
    cases a with
    | inl p =>
      fin_cases p
      · exact Reachable.rfl
      · exact hAcross
    | inr q =>
      obtain ⟨k, j⟩ := q
      rcases lt_trichotomy j (f k) with hj | hj | hj
      · exact OMA.seymour_from_left S k j hL (fun r hr => hFree k r (lt_of_le_of_lt hr hj).ne)
      · have hh : OMA.seymour_internal k (f k) ∉ S := by
          have hJ : OMA.seymour_internal k j ∉ S := (Set.mem_compl_iff _ _).mp ha
          simpa only [hj] using hJ
        exact OMA.seymour_from_left S k j hL (fun r _ => hWhole k hh r)
      · exact hAcross.trans (OMA.seymour_from_right S k j hR
          (fun r hr => hFree k r (lt_of_lt_of_le hj hr).ne.symm))
  intro a b
  exact (hFromL a).symm.trans (hFromL b)

lemma OMA.seymour_preconnected_comap {V W : Type*} (e : V ≃ W) (G : SimpleGraph W) (T : Set W) :
    ((G.comap e).induce (e ⁻¹' T)ᶜ).Preconnected ↔ (G.induce Tᶜ).Preconnected := by
  let g := SimpleGraph.Iso.comap e G
  have hBij : Set.BijOn g (e ⁻¹' T)ᶜ Tᶜ := by
    refine ⟨fun _ h => h, e.injective.injOn, ?_⟩
    intro v hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change e (e.symm v) ∉ T
    simpa using hv
  exact (g.induce hBij).preconnected_iff

lemma OMA.seymour_cut_comap {V W : Type*} (e : V ≃ W) (G : SimpleGraph W) {T : Set W}
    (hT : Erdos150.IsMinimalCut G T) : Erdos150.IsMinimalCut (G.comap e) (e ⁻¹' T) := by
  refine ⟨fun h => hT.1 ((OMA.seymour_preconnected_comap e G T).mp h), ?_⟩
  intro S hS
  have hImage : e '' S ⊂ T := by
    have h := e.injective.image_strictMono hS
    rwa [e.image_preimage] at h
  have h := (OMA.seymour_preconnected_comap e G (e '' S)).mpr (hT.2 _ hImage)
  rwa [e.preimage_image] at h

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.seymour := by
  intro m
  classical
  let e : Fin (3 * m + 2) ≃ OMA.seymour_vertices m :=
    Fintype.equivOfCardEq (by simp [OMA.seymour_vertices, Fintype.card_sum, Fintype.card_prod,
      Nat.mul_comm, Nat.add_comm])
  let G := (OMA.seymour_graph m).comap e
  let cut (f : Fin m → Fin 3) : {T : Set (Fin (3 * m + 2)) | Erdos150.IsMinimalCut G T} :=
    ⟨e ⁻¹' OMA.seymour_cut f, OMA.seymour_cut_comap e (OMA.seymour_graph m)
      ⟨OMA.seymour_not_preconnected f, OMA.seymour_proper_preconnected f⟩⟩
  have hinj : Function.Injective cut := by
    intro f g h
    have h' : e ⁻¹' OMA.seymour_cut f = e ⁻¹' OMA.seymour_cut g := congrArg Subtype.val h
    have heq := e.surjective.preimage_injective h'
    funext i
    apply OMA.seymour_internal_mem.mp
    rw [← heq]
    exact OMA.seymour_internal_mem.mpr rfl
  have hcard : 3 ^ m ≤ {T : Set (Fin (3 * m + 2)) | Erdos150.IsMinimalCut G T}.ncard := by
    have h := Nat.card_le_card_of_injective cut hinj
    rwa [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
  let counts : Set ℕ := {k | ∃ G' : SimpleGraph (Fin (3 * m + 2)),
    {T : Set (Fin (3 * m + 2)) | Erdos150.IsMinimalCut G' T}.ncard = k}
  change 3 ^ m ≤ sSup counts
  have hBdd : BddAbove counts := by
    refine ⟨Nat.card (Set (Fin (3 * m + 2))), ?_⟩
    rintro n ⟨G', rfl⟩
    exact Set.ncard_le_card _
  have hmem : {T : Set (Fin (3 * m + 2)) | Erdos150.IsMinimalCut G T}.ncard ∈ counts := ⟨G, rfl⟩
  exact le_csSup_of_le hBdd hmem hcard