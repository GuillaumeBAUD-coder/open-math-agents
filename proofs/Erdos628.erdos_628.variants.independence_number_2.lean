import FormalConjectures.ErdosProblems.«628»

/-!
# Erdős Problem 628 — independence number 2

Proves the Erdős–Lovász–Tihany conjecture for graphs with independence number 2
(Balogh, Kostochka, Prince, and Stiebitz [BKPS09]) via reduction to vertex-critical
graphs, complement-graph matchings, Gallai's lemma, and component splitting.
-/

namespace Erdos628Proof

universe u

open SimpleGraph Classical

/- Section 1: Basic graph helpers -/

private lemma card_set_compl {W : Type u} [Fintype W] (S : Set W)
    [Fintype S] [Fintype (Sᶜ : Set W)] :
    Fintype.card (Sᶜ : Set W) = Fintype.card W - Fintype.card S := by
  have h1 : Fintype.card (Sᶜ : Set W) = Fintype.card {x // x ∉ S} :=
    Fintype.card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩,
      fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
  have h2 : Fintype.card S = Fintype.card {x // x ∈ S} :=
    Fintype.card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩,
      fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
  rw [h1, h2, Fintype.card_subtype_compl]

private lemma card_set_singleton {W : Type u} (v : W) [Fintype ({v} : Set W)] :
    Fintype.card ({v} : Set W) = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨⟨v, rfl⟩, fun x => Subtype.ext x.2⟩

private lemma indepNum_induce_le {V : Type u} [Fintype V] (G : SimpleGraph V) (s : Set V) :
    (G.induce s).indepNum ≤ G.indepNum := by
  obtain ⟨t, ht⟩ := (G.induce s).exists_isNIndepSet_indepNum
  have ht_indep : G.IsIndepSet ((t.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe,
      Subtype.exists] at hx hy
    obtain ⟨a, ha, hat, rfl⟩ := hx
    obtain ⟨b, hb, hbt, rfl⟩ := hy
    have hab : (⟨a, ha⟩ : s) ≠ ⟨b, hb⟩ := fun h => hxy (congrArg Subtype.val h)
    exact ((SimpleGraph.isIndepSet_iff _).mp ht.1) hat hbt hab
  have hle := ht_indep.card_le_indepNum
  rw [Finset.card_map, ht.2] at hle
  exact hle

private lemma compl_cliqueFree_three {V : Type u} [Fintype V] {G : SimpleGraph V}
    (h : G.indepNum ≤ 2) : Gᶜ.CliqueFree 3 := by
  intro t ht
  have hind : G.IsIndepSet (t : Set V) := G.isClique_compl.mp ht.1
  have hle : t.card ≤ G.indepNum := hind.card_le_indepNum
  have hcard : t.card = 3 := ht.2
  omega

private lemma compl_induce_eq {V : Type u} (G : SimpleGraph V) (s : Set V) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext x y
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/- Section 2: Matchings as involutions & coloring equivalence -/

private structure Matching {V : Type u} (H : SimpleGraph V) where
  mate : V → V
  invol : ∀ v, mate (mate v) = v
  adj_of_ne : ∀ v, mate v ≠ v → H.Adj v (mate v)

private def Matching.empty (H : SimpleGraph V) : Matching H where
  mate := id
  invol _ := rfl
  adj_of_ne _ h := (h rfl).elim

private noncomputable def Matching.fixedSet {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) : Finset V :=
  Finset.univ.filter (fun v => M.mate v = v)

private noncomputable def Matching.defic {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) : ℕ :=
  M.fixedSet.card

private lemma Matching.mem_fixedSet {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) (v : V) : v ∈ M.fixedSet ↔ M.mate v = v := by
  simp [Matching.fixedSet]

private def Matching.transport {V W : Type u} {H₁ : SimpleGraph V} {H₂ : SimpleGraph W}
    (φ : H₁ ≃g H₂) (M : Matching H₁) : Matching H₂ where
  mate w := φ (M.mate (φ.symm w))
  invol w := by simp [M.invol]
  adj_of_ne w hw := by
    have hne : M.mate (φ.symm w) ≠ φ.symm w := by
      intro heq
      apply hw
      rw [heq, φ.apply_symm_apply]
    have hadj := M.adj_of_ne (φ.symm w) hne
    have hadj2 : H₂.Adj (φ (φ.symm w)) (φ (M.mate (φ.symm w))) := φ.map_rel_iff.mpr hadj
    simpa using hadj2

private lemma Matching.defic_transport {V W : Type u} [Fintype V] [Fintype W]
    {H₁ : SimpleGraph V} {H₂ : SimpleGraph W} (φ : H₁ ≃g H₂) (M : Matching H₁) :
    (M.transport φ).defic = M.defic := by
  unfold Matching.defic
  refine Finset.card_bij (fun w _ => φ.symm w) ?_ ?_ ?_
  · intro w hw
    rw [Matching.mem_fixedSet] at hw ⊢
    exact φ.injective (by simpa [Matching.transport] using hw)
  · intro w₁ _ w₂ _ h
    exact φ.symm.injective h
  · intro v hv
    rw [Matching.mem_fixedSet] at hv
    refine ⟨φ v, (Matching.mem_fixedSet _ _).mpr ?_, φ.symm_apply_apply v⟩
    simp [Matching.transport, hv]

private lemma Matching.two_mul_pairCard_eq {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) :
    2 * (Finset.univ.image (fun v => s(v, M.mate v))).card = Fintype.card V + M.defic := by
  let f : V → Sym2 V := fun v => s(v, M.mate v)
  let E : Finset (Sym2 V) := Finset.univ.image f
  let E_diag : Finset (Sym2 V) := E.filter Sym2.IsDiag
  let E_nondiag : Finset (Sym2 V) := E.filter (fun e => ¬ e.IsDiag)
  let S_diag : Finset V := M.fixedSet
  let S_nondiag : Finset V := Finset.univ.filter (fun v => ¬ M.mate v = v)
  have hE_card : E_diag.card + E_nondiag.card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) Sym2.IsDiag
  have hS_card : S_diag.card + S_nondiag.card = Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun v => M.mate v = v)
  have hdiag : S_diag.card = E_diag.card := by
    refine Finset.card_bij (fun v _ => s(v, v)) ?_ ?_ ?_
    · intro v hv
      rw [Matching.mem_fixedSet] at hv
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, ?_⟩, by simp⟩
      change s(v, M.mate v) = s(v, v)
      rw [hv]
    · intro v₁ _ v₂ _ h
      exact (Sym2.eq_iff.mp h).elim (fun h1 => h1.1) (fun h2 => h2.1)
    · intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨he_im, hdiag_e⟩ := he
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he_im
      rw [Sym2.mk_isDiag_iff] at hdiag_e
      refine ⟨v, (Matching.mem_fixedSet M v).mpr hdiag_e.symm, ?_⟩
      dsimp only [f]
      rw [← hdiag_e]
  have hnondiag : S_nondiag.card = 2 * E_nondiag.card := by
    have hfib : S_nondiag.card = ∑ e ∈ E_nondiag, (S_nondiag.filter (fun v => f v = e)).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro v hv
      simp only [Finset.mem_coe, S_nondiag, E_nondiag, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      refine ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, ?_⟩
      rw [Sym2.mk_isDiag_iff]
      exact fun h => hv h.symm
    have hconst : ∀ e ∈ E_nondiag, (S_nondiag.filter (fun v => f v = e)).card = 2 := by
      intro e he
      simp only [E_nondiag, E, Finset.mem_filter] at he
      obtain ⟨he_im, hnd⟩ := he
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he_im
      have hne : M.mate v ≠ v := fun heq => hnd (Sym2.mk_isDiag_iff.mpr heq.symm)
      have hset : S_nondiag.filter (fun u => f u = s(v, M.mate v)) = {v, M.mate v} := by
        ext u
        simp only [S_nondiag, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, f, Sym2.eq_iff]
        constructor
        · rintro ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
          · refine ⟨?_, Or.inr ⟨rfl, M.invol v⟩⟩
            intro heq
            exact hne (by simpa [M.invol] using heq.symm)
      rw [hset, Finset.card_pair hne.symm]
    rw [hfib, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    omega
  have hE_eq : (Finset.univ.image (fun v => s(v, M.mate v))).card = E.card := rfl
  have hdefic : M.defic = S_diag.card := rfl
  omega

private lemma Matching.even_card_add_defic {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) : Even (Fintype.card V + M.defic) := by
  refine ⟨(Finset.univ.image (fun v => s(v, M.mate v))).card, ?_⟩
  have h := M.two_mul_pairCard_eq
  omega

private lemma colorable_iff_exists_matching {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.indepNum ≤ 2) (r : ℕ) :
    G.Colorable r ↔ ∃ M : Matching Gᶜ, Fintype.card V + M.defic ≤ 2 * r := by
  constructor
  · rintro ⟨C⟩
    let F : Fin r → Finset V := fun i => Finset.univ.filter (fun v => C v = i)
    have hF_card : ∀ i, (F i).card ≤ 2 := by
      intro i
      have hind : G.IsIndepSet ((F i : Finset V) : Set V) := by
        rw [SimpleGraph.isIndepSet_iff]
        intro u hu v hv _ hadj
        simp only [Finset.mem_coe, F, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        exact C.valid hadj (hu.trans hv.symm)
      exact hind.card_le_indepNum.trans hG
    let mate : V → V := fun v =>
      if h : ∃ w, w ≠ v ∧ C w = C v then Classical.choose h else v
    have hmate_eq : ∀ v w, w ≠ v → C w = C v → mate v = w := by
      intro v w hne hc
      have hex : ∃ u, u ≠ v ∧ C u = C v := ⟨w, hne, hc⟩
      have hspec := Classical.choose_spec hex
      have hmate_def : mate v = Classical.choose hex := dif_pos hex
      rw [hmate_def]
      by_contra hdiff
      let u := Classical.choose hex
      have hsub : ({v, w, u} : Finset V) ⊆ F (C v) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hz with rfl | rfl | rfl
        · rfl
        · exact hc
        · exact hspec.2
      have hne_vu : v ≠ u := hspec.1.symm
      have hcard3 : ({v, w, u} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hdiff)]
        simp [hne.symm, hne_vu]
      have hle := (Finset.card_le_card hsub).trans (hF_card (C v))
      omega
    have hmate_none : ∀ v, (∀ w, C w = C v → w = v) → mate v = v := by
      intro v h
      have hnex : ¬ ∃ w, w ≠ v ∧ C w = C v := fun ⟨w, hne, hc⟩ => hne (h w hc)
      simp [mate, hnex]
    let M : Matching Gᶜ :=
      { mate := mate
        invol := fun v => by
          by_cases h : ∃ w, w ≠ v ∧ C w = C v
          · obtain ⟨w, hne, hc⟩ := h
            rw [hmate_eq v w hne hc]
            exact hmate_eq w v hne.symm hc.symm
          · push Not at h
            rw [hmate_none v (fun w hc => by_contra fun hne => h w hne hc)]
            exact hmate_none v (fun w hc => by_contra fun hne => h w hne hc)
        adj_of_ne := fun v hne => by
          rw [SimpleGraph.compl_adj]
          refine ⟨hne.symm, ?_⟩
          have h : ∃ w, w ≠ v ∧ C w = C v := by
            by_contra hnex
            exact hne (by simp [mate, hnex])
          have hspec := Classical.choose_spec h
          have hcv : C (mate v) = C v := by
            simp only [mate, dif_pos h]
            exact hspec.2
          intro hadj
          exact C.valid hadj hcv.symm }
    refine ⟨M, ?_⟩
    have hV_sum : Fintype.card V = ∑ i : Fin r, (F i).card := by
      rw [← Finset.card_univ]
      have h := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset (Fin r)))
        (f := C) (fun _ _ => Finset.mem_univ _)
      simpa [F] using h
    have hdefic_sum : M.defic = ∑ i : Fin r, (if (F i).card = 1 then 1 else 0) := by
      unfold Matching.defic Matching.fixedSet
      rw [Finset.card_eq_sum_card_fiberwise (f := C) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmem : ∀ v, M.mate v = v ↔ F (C v) = {v} := by
        intro v
        constructor
        · intro hv
          ext w
          simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hc
            by_contra hne
            exact hne (hmate_eq v w hne hc ▸ hv)
          · rintro rfl; rfl
        · intro hv
          apply hmate_none v
          intro w hc
          have hw : w ∈ F (C v) := by simp [F, hc]
          rw [hv, Finset.mem_singleton] at hw
          exact hw
      by_cases h1 : (F i).card = 1
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
        have hcv : C v = i := by
          have : v ∈ F i := by rw [hv]; exact Finset.mem_singleton_self v
          simpa [F] using this
        have hfilt : (Finset.univ.filter fun a => M.mate a = a).filter (fun a => C a = i) = {v} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hc⟩
            have hw : w ∈ F i := by simp [F, hc]
            rw [hv, Finset.mem_singleton] at hw
            exact hw
          · intro hw_eq
            rw [hw_eq]
            exact ⟨(hmem v).mpr (by rw [hcv]; exact hv), hcv⟩
        simp [h1, hfilt]
      · have hfilt : (Finset.univ.filter fun a => M.mate a = a).filter (fun a => C a = i) = ∅ := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨hw, hc⟩
          have hfw := (hmem w).mp hw
          rw [hc] at hfw
          exact h1 (by rw [hfw, Finset.card_singleton])
        simp [h1, hfilt]
    rw [hV_sum, hdefic_sum, ← Finset.sum_add_distrib]
    calc ∑ i : Fin r, ((F i).card + if (F i).card = 1 then 1 else 0)
        ≤ ∑ _i : Fin r, 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hF_card i
          split_ifs <;> omega
      _ = 2 * r := by simp [mul_comm]
  · rintro ⟨M, hle⟩
    let E : Finset (Sym2 V) := Finset.univ.image (fun v => s(v, M.mate v))
    have hE2 : 2 * E.card = Fintype.card V + M.defic := M.two_mul_pairCard_eq
    have hEr : E.card ≤ r := by omega
    let e := Fintype.equivFinOfCardEq (Fintype.card_coe E)
    refine ⟨⟨fun v => Fin.castLE hEr (e ⟨s(v, M.mate v),
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩), ?_⟩⟩
    intro u v hadj heq
    have heq1 : e ⟨s(u, M.mate u), Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩⟩ =
        e ⟨s(v, M.mate v), Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩ :=
      Fin.ext (by simpa using congrArg Fin.val heq)
    have hs : s(u, M.mate u) = s(v, M.mate v) :=
      congrArg Subtype.val (e.injective heq1)
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨huv, _⟩ | ⟨huv_m, _⟩
    · exact hadj.ne huv
    · have hne : M.mate v ≠ v := by rw [← huv_m]; exact hadj.ne
      have hadj_c := M.adj_of_ne v hne
      rw [SimpleGraph.compl_adj, ← huv_m] at hadj_c
      exact hadj_c.2 hadj.symm

/- Section 3: Alternating paths & Gallai's Lemma -/

private def altStep {V : Type u} {H : SimpleGraph V} (M₁ M₂ : Matching H) (n : ℕ) (v : V) : V :=
  if Even n then M₂.mate v else M₁.mate v

private lemma altStep_invol {V : Type u} {H : SimpleGraph V} (M₁ M₂ : Matching H) (n : ℕ) (v : V) :
    altStep M₁ M₂ n (altStep M₁ M₂ n v) = v := by
  unfold altStep
  split_ifs <;> simp [M₁.invol, M₂.invol]

private def altSeq {V : Type u} {H : SimpleGraph V} (M₁ M₂ : Matching H) (u : V) : ℕ → V
  | 0 => u
  | n + 1 => altStep M₁ M₂ n (altSeq M₁ M₂ u n)

private lemma altSeq_inj_of_no_stop {V : Type u} {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (u : V) (hm₁ : M₁.mate u = u) (m : ℕ)
    (hno : ∀ k < m, altSeq M₁ M₂ u (k + 1) ≠ altSeq M₁ M₂ u k) :
    ∀ j ≤ m, ∀ i < j, altSeq M₁ M₂ u i ≠ altSeq M₁ M₂ u j := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hkm i hik heq
    have ih' := ih (by omega)
    cases i with
    | zero =>
      by_cases hk0 : k = 0
      · subst hk0
        exact hno 0 (by omega) heq.symm
      · by_cases heven : Even k
        · have h1k : (1 : ℕ) < k := by
            by_contra hle
            have : k = 1 := by omega
            subst this
            exact Nat.not_even_one heven
          have h1 : altSeq M₁ M₂ u 1 = M₂.mate (altSeq M₁ M₂ u 0) := by simp [altSeq, altStep]
          have hk1 : altSeq M₁ M₂ u (k + 1) = M₂.mate (altSeq M₁ M₂ u k) := by
            simp [altSeq, altStep, heven]
          have h_eq1 : altSeq M₁ M₂ u 1 = altSeq M₁ M₂ u k := by
            rw [h1, heq, hk1, M₂.invol]
          exact ih' 1 h1k h_eq1
        · have hk1 : altSeq M₁ M₂ u (k + 1) = M₁.mate (altSeq M₁ M₂ u k) := by
            simp [altSeq, altStep, heven]
          have h_eq0 : altSeq M₁ M₂ u 0 = altSeq M₁ M₂ u k := by
            have h0m : M₁.mate (altSeq M₁ M₂ u 0) = altSeq M₁ M₂ u 0 := hm₁
            have := congrArg M₁.mate heq
            rw [h0m, hk1, M₁.invol] at this
            exact this
          exact ih' 0 (by omega) h_eq0
    | succ i' =>
      by_cases hi'k : i' + 1 = k
      · subst hi'k
        exact hno (i' + 1) (by omega) heq.symm
      · have hik' : i' + 1 < k := by omega
        by_cases hpar : Even i' ↔ Even k
        · have hstep_eq : altStep M₁ M₂ i' = altStep M₁ M₂ k := by
            ext z; simp [altStep, hpar]
          have heq' : altStep M₁ M₂ i' (altSeq M₁ M₂ u i') = altStep M₁ M₂ i' (altSeq M₁ M₂ u k) := by
            calc altStep M₁ M₂ i' (altSeq M₁ M₂ u i')
                = altStep M₁ M₂ k (altSeq M₁ M₂ u k) := heq
              _ = altStep M₁ M₂ i' (altSeq M₁ M₂ u k) := by rw [hstep_eq]
          have heq'' := congrArg (altStep M₁ M₂ i') heq'
          rw [altStep_invol, altStep_invol] at heq''
          exact ih' i' (by omega) heq''
        · have hpar_succ : Even (i' + 1) ↔ Even k := by
            rw [Nat.even_add_one]
            tauto
          have hne_succ : i' + 2 ≠ k := by
            intro h
            have h1 : Even (i' + 2) ↔ ¬ Even (i' + 1) := by
              rw [show i' + 2 = (i' + 1) + 1 by rfl, Nat.even_add_one]
            have h2 : Even k ↔ ¬ Even k := by
              calc Even k ↔ Even (i' + 2) := by rw [h]
                _ ↔ ¬ Even (i' + 1) := h1
                _ ↔ ¬ Even k := not_congr hpar_succ
            exact (iff_not_self (a := Even k)) h2
          have hlt2 : i' + 2 < k := by omega
          have hstep_eq : altStep M₁ M₂ (i' + 1) = altStep M₁ M₂ k := by
            ext z; simp [altStep, hpar_succ]
          have h_eq2 : altSeq M₁ M₂ u (i' + 2) = altSeq M₁ M₂ u k := by
            change altStep M₁ M₂ (i' + 1) (altSeq M₁ M₂ u (i' + 1)) = altSeq M₁ M₂ u k
            rw [heq, hstep_eq]
            exact altStep_invol M₁ M₂ k (altSeq M₁ M₂ u k)
          exact ih' (i' + 2) hlt2 h_eq2

private lemma altSeq_exists_stop {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (u : V) (hm₁ : M₁.mate u = u) :
    ∃ L : ℕ, altSeq M₁ M₂ u (L + 1) = altSeq M₁ M₂ u L := by
  by_contra hnone
  push Not at hnone
  have hinj : Function.Injective (fun i : Fin (Fintype.card V + 1) => altSeq M₁ M₂ u i.1) := by
    intro a b hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact altSeq_inj_of_no_stop M₁ M₂ u hm₁ b.1 (fun k _ => hnone k) b.1 le_rfl a.1 hlt hab
    · exact altSeq_inj_of_no_stop M₁ M₂ u hm₁ a.1 (fun k _ => hnone k) a.1 le_rfl b.1 hgt hab.symm
  have hle := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at hle
  omega

private noncomputable def Matching.swap {V : Type u} {H : SimpleGraph V} (M₁ M₂ : Matching H)
    (P : Finset V)
    (h1 : ∀ v ∈ P, M₁.mate v ∈ P)
    (h2 : ∀ v ∈ P, M₂.mate v ∈ P) : Matching H where
  mate v := if v ∈ P then M₂.mate v else M₁.mate v
  invol v := by
    by_cases hv : v ∈ P
    · simp [hv, h2 v hv, M₂.invol]
    · have h1v : M₁.mate v ∉ P := by
        intro hmem
        have := h1 (M₁.mate v) hmem
        rw [M₁.invol] at this
        exact hv this
      simp [hv, h1v, M₁.invol]
  adj_of_ne v hne := by
    by_cases hv : v ∈ P
    · simp only [hv, ↓reduceIte] at hne ⊢
      exact M₂.adj_of_ne v hne
    · simp only [hv, ↓reduceIte] at hne ⊢
      exact M₁.adj_of_ne v hne

private lemma Matching.defic_swap {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (P : Finset V)
    (h1 : ∀ v ∈ P, M₁.mate v ∈ P) (h2 : ∀ v ∈ P, M₂.mate v ∈ P) :
    (M₁.swap M₂ P h1 h2).defic + (P ∩ M₁.fixedSet).card =
      M₁.defic + (P ∩ M₂.fixedSet).card := by
  let Pc := Finset.univ \ P
  have split : ∀ (S : Finset V), S.card = (P ∩ S).card + (Pc ∩ S).card := by
    intro S
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_inter, Pc, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_inter, Pc, Finset.mem_sdiff] at hv1 hv2
      exact hv2.1.2 hv1.1
  have hA : P ∩ (M₁.swap M₂ P h1 h2).fixedSet = P ∩ M₂.fixedSet := by
    ext v
    simp only [Finset.mem_inter, Matching.mem_fixedSet, Matching.swap]
    constructor
    · rintro ⟨hv, h⟩; rw [if_pos hv] at h; exact ⟨hv, h⟩
    · rintro ⟨hv, h⟩; rw [if_pos hv]; exact ⟨hv, h⟩
  have hB : Pc ∩ (M₁.swap M₂ P h1 h2).fixedSet = Pc ∩ M₁.fixedSet := by
    ext v
    simp only [Finset.mem_inter, Pc, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Matching.mem_fixedSet, Matching.swap]
    constructor
    · rintro ⟨hv, h⟩; rw [if_neg hv] at h; exact ⟨hv, h⟩
    · rintro ⟨hv, h⟩; rw [if_neg hv]; exact ⟨hv, h⟩
  unfold Matching.defic
  rw [split (M₁.swap M₂ P h1 h2).fixedSet, split M₁.fixedSet, hA, hB]
  omega

private lemma altSeq_path_props {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (u : V) (hm₁ : M₁.mate u = u) (L : ℕ)
    (hno : ∀ k < L, altSeq M₁ M₂ u (k + 1) ≠ altSeq M₁ M₂ u k)
    (hstop : altSeq M₁ M₂ u (L + 1) = altSeq M₁ M₂ u L) :
    let P := (Finset.range (L + 1)).image (altSeq M₁ M₂ u)
    (∀ v ∈ P, M₁.mate v ∈ P) ∧ (∀ v ∈ P, M₂.mate v ∈ P) ∧
    (1 ≤ L → Odd L →
      (P ∩ M₁.fixedSet).card = 2 ∧
      (P ∩ M₂.fixedSet).card = 0) ∧
    (1 ≤ L → Even L →
      (P ∩ M₁.fixedSet).card = 1 ∧
      (P ∩ M₂.fixedSet).card = 1) := by
  let P := (Finset.range (L + 1)).image (altSeq M₁ M₂ u)
  have hx_inj := altSeq_inj_of_no_stop M₁ M₂ u hm₁ L hno
  have hm₁_mem : ∀ k ≤ L, M₁.mate (altSeq M₁ M₂ u k) ∈ P := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      change M₁.mate u ∈ P
      rw [hm₁]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
    · by_cases heven : Even k
      · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hk'_odd : ¬ Even k' := by rw [Nat.even_add_one] at heven; exact heven
        have heq : M₁.mate (altSeq M₁ M₂ u (k' + 1)) = altSeq M₁ M₂ u k' := by
          change M₁.mate (altStep M₁ M₂ k' (altSeq M₁ M₂ u k')) = altSeq M₁ M₂ u k'
          simp [altStep, hk'_odd, M₁.invol]
        rw [heq]
        exact Finset.mem_image.mpr ⟨k', Finset.mem_range.mpr (by omega), rfl⟩
      · have h1 : altSeq M₁ M₂ u (k + 1) = M₁.mate (altSeq M₁ M₂ u k) := by
          simp [altSeq, altStep, heven]
        rw [← h1]
        by_cases hkL : k = L
        · subst hkL
          rw [hstop]
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
        · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hm₂_mem : ∀ k ≤ L, M₂.mate (altSeq M₁ M₂ u k) ∈ P := by
    intro k hk
    by_cases heven : Even k
    · have h1 : altSeq M₁ M₂ u (k + 1) = M₂.mate (altSeq M₁ M₂ u k) := by
        simp [altSeq, altStep, heven]
      rw [← h1]
      by_cases hkL : k = L
      · subst hkL
        rw [hstop]
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      · exact Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), rfl⟩
    · have hk0 : k ≠ 0 := fun h => heven (h ▸ ⟨0, rfl⟩)
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hk'_even : Even k' := by rw [Nat.even_add_one] at heven; tauto
      have heq : M₂.mate (altSeq M₁ M₂ u (k' + 1)) = altSeq M₁ M₂ u k' := by
        change M₂.mate (altStep M₁ M₂ k' (altSeq M₁ M₂ u k')) = altSeq M₁ M₂ u k'
        simp [altStep, hk'_even, M₂.invol]
      rw [heq]
      exact Finset.mem_image.mpr ⟨k', Finset.mem_range.mpr (by omega), rfl⟩
  have hclosed1 : ∀ v ∈ P, M₁.mate v ∈ P := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact hm₁_mem k (by simpa [Finset.mem_range] using hk)
  have hclosed2 : ∀ v ∈ P, M₂.mate v ∈ P := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact hm₂_mem k (by simpa [Finset.mem_range] using hk)
  have hm₁_fix_iff : ∀ k ≤ L, M₁.mate (altSeq M₁ M₂ u k) = altSeq M₁ M₂ u k ↔ k = 0 ∨ (k = L ∧ Odd L) := by
    intro k hk
    constructor
    · intro hfix
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · right
        by_cases heven : Even k
        · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have hk'_odd : ¬ Even k' := by rw [Nat.even_add_one] at heven; exact heven
          have heq : altSeq M₁ M₂ u (k' + 1) = M₁.mate (altSeq M₁ M₂ u k') := by
            simp [altSeq, altStep, hk'_odd]
          have heq2 : altSeq M₁ M₂ u k' = altSeq M₁ M₂ u (k' + 1) := by
            have := congrArg M₁.mate heq
            rw [M₁.invol] at this
            exact (hfix ▸ this).symm
          exact (hno k' (by omega) heq2.symm).elim
        · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
          by_cases hkL : k = L
          · exact ⟨hkL, hkL ▸ hodd⟩
          · have h1 : altSeq M₁ M₂ u (k + 1) = M₁.mate (altSeq M₁ M₂ u k) := by
              simp [altSeq, altStep, heven]
            rw [hfix] at h1
            exact (hno k (by omega) h1).elim
    · rintro (rfl | ⟨rfl, hoddL⟩)
      · exact hm₁
      · have hevenL : ¬ Even k := Nat.not_even_iff_odd.mpr hoddL
        have h1 : altSeq M₁ M₂ u (k + 1) = M₁.mate (altSeq M₁ M₂ u k) := by
          simp [altSeq, altStep, hevenL]
        rw [← h1, hstop]
  have hm₂_fix_iff : ∀ k ≤ L, M₂.mate (altSeq M₁ M₂ u k) = altSeq M₁ M₂ u k ↔ k = L ∧ Even L := by
    intro k hk
    constructor
    · intro hfix
      by_cases heven : Even k
      · by_cases hkL : k = L
        · exact ⟨hkL, hkL ▸ heven⟩
        · have h1 : altSeq M₁ M₂ u (k + 1) = M₂.mate (altSeq M₁ M₂ u k) := by
            simp [altSeq, altStep, heven]
          rw [hfix] at h1
          exact (hno k (by omega) h1).elim
      · have hk0 : k ≠ 0 := fun h => heven (h ▸ ⟨0, rfl⟩)
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hk'_even : Even k' := by rw [Nat.even_add_one] at heven; tauto
        have heq : altSeq M₁ M₂ u (k' + 1) = M₂.mate (altSeq M₁ M₂ u k') := by
          simp [altSeq, altStep, hk'_even]
        have heq2 : altSeq M₁ M₂ u k' = altSeq M₁ M₂ u (k' + 1) := by
          have := congrArg M₂.mate heq
          rw [M₂.invol] at this
          exact (hfix ▸ this).symm
        exact (hno k' (by omega) heq2.symm).elim
    · rintro ⟨rfl, hevenL⟩
      have h1 : altSeq M₁ M₂ u (k + 1) = M₂.mate (altSeq M₁ M₂ u k) := by
        simp [altSeq, altStep, hevenL]
      rw [← h1, hstop]
  refine ⟨hclosed1, hclosed2, ?_, ?_⟩
  · intro hL1 hoddL
    have hf1 : P ∩ M₁.fixedSet = {altSeq M₁ M₂ u 0, altSeq M₁ M₂ u L} := by
      ext v
      simp only [Finset.mem_inter, Matching.mem_fixedSet, Finset.mem_image, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton, P]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hfix⟩
        rcases (hm₁_fix_iff k (by omega)).mp hfix with rfl | ⟨rfl, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨⟨0, by omega, rfl⟩, hm₁⟩
        · exact ⟨⟨L, by omega, rfl⟩, (hm₁_fix_iff L le_rfl).mpr (Or.inr ⟨rfl, hoddL⟩)⟩
    have hf2 : P ∩ M₂.fixedSet = ∅ := by
      ext v
      simp only [Finset.mem_inter, Matching.mem_fixedSet, Finset.mem_image, Finset.mem_range,
        Finset.notMem_empty, iff_false, P]
      rintro ⟨⟨k, hk, rfl⟩, hfix⟩
      have ⟨_, hevenL⟩ := (hm₂_fix_iff k (by omega)).mp hfix
      exact Nat.not_even_iff_odd.mpr hoddL hevenL
    have hne : altSeq M₁ M₂ u 0 ≠ altSeq M₁ M₂ u L := hx_inj L le_rfl 0 (by omega)
    rw [hf1, hf2, Finset.card_pair hne, Finset.card_empty]
    exact ⟨rfl, rfl⟩
  · intro hL1 hevenL
    have hf1 : P ∩ M₁.fixedSet = {altSeq M₁ M₂ u 0} := by
      ext v
      simp only [Finset.mem_inter, Matching.mem_fixedSet, Finset.mem_image, Finset.mem_range,
        Finset.mem_singleton, P]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hfix⟩
        rcases (hm₁_fix_iff k (by omega)).mp hfix with rfl | ⟨rfl, hoddL⟩
        · rfl
        · exact (Nat.not_even_iff_odd.mpr hoddL hevenL).elim
      · rintro rfl
        exact ⟨⟨0, by omega, rfl⟩, hm₁⟩
    have hf2 : P ∩ M₂.fixedSet = {altSeq M₁ M₂ u L} := by
      ext v
      simp only [Finset.mem_inter, Matching.mem_fixedSet, Finset.mem_image, Finset.mem_range,
        Finset.mem_singleton, P]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hfix⟩
        have ⟨rfl, _⟩ := (hm₂_fix_iff k (by omega)).mp hfix
        rfl
      · rintro rfl
        exact ⟨⟨L, by omega, rfl⟩, (hm₂_fix_iff L le_rfl).mpr ⟨rfl, hevenL⟩⟩
    rw [hf1, hf2, Finset.card_singleton, Finset.card_singleton]
    exact ⟨rfl, rfl⟩

private lemma altSeq_even_and_swap {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (u : V)
    (hm₁_min : ∀ M : Matching H, M₁.defic ≤ M.defic)
    (hm₁_u : M₁.mate u = u) (hm₂_u : M₂.mate u ≠ u) :
    ∃ (L : ℕ) (P : Finset V) (h1 : ∀ v ∈ P, M₁.mate v ∈ P) (h2 : ∀ v ∈ P, M₂.mate v ∈ P),
      1 ≤ L ∧ Even L ∧
      P = (Finset.range (L + 1)).image (altSeq M₁ M₂ u) ∧
      (∀ k < L, altSeq M₁ M₂ u (k + 1) ≠ altSeq M₁ M₂ u k) ∧
      altSeq M₁ M₂ u (L + 1) = altSeq M₁ M₂ u L ∧
      (M₂.swap M₁ P h2 h1).defic = M₂.defic ∧
      (M₂.swap M₁ P h2 h1).mate u = u ∧
      (∀ z ∉ P, (M₂.swap M₁ P h2 h1).mate z = M₂.mate z) := by
  have hex := altSeq_exists_stop M₁ M₂ u hm₁_u
  let L := Nat.find hex
  have hstop : altSeq M₁ M₂ u (L + 1) = altSeq M₁ M₂ u L := Nat.find_spec hex
  have hno : ∀ k < L, altSeq M₁ M₂ u (k + 1) ≠ altSeq M₁ M₂ u k :=
    fun k hk => Nat.find_min hex hk
  have hL1 : 1 ≤ L := by
    by_contra h0
    have hL0 : L = 0 := by omega
    rw [hL0] at hstop
    simp only [altSeq, altStep] at hstop
    split_ifs at hstop with h0e
    · exact hm₂_u hstop
    · exact (h0e ⟨0, rfl⟩).elim
  let P := (Finset.range (L + 1)).image (altSeq M₁ M₂ u)
  obtain ⟨h1, h2, hodd, heven⟩ := altSeq_path_props M₁ M₂ u hm₁_u L hno hstop
  have hL_even : Even L := by
    by_contra hnot_even
    have hL_odd : Odd L := Nat.not_even_iff_odd.mp hnot_even
    obtain ⟨hc1, hc2⟩ := hodd hL1 hL_odd
    have hswap := M₁.defic_swap M₂ P h1 h2
    have hle := hm₁_min (M₁.swap M₂ P h1 h2)
    have hhc1 : (P ∩ M₁.fixedSet).card = 2 := hc1
    have hhc2 : (P ∩ M₂.fixedSet).card = 0 := hc2
    omega
  obtain ⟨hc1, hc2⟩ := heven hL1 hL_even
  have hswap2 := M₂.defic_swap M₁ P h2 h1
  have hhc1 : (P ∩ M₁.fixedSet).card = 1 := hc1
  have hhc2 : (P ∩ M₂.fixedSet).card = 1 := hc2
  have hdefic_eq : (M₂.swap M₁ P h2 h1).defic = M₂.defic := by omega
  have hu_P : u ∈ P := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hmate_u : (M₂.swap M₁ P h2 h1).mate u = u := by
    simp only [Matching.swap, hu_P, ↓reduceIte, hm₁_u]
  refine ⟨L, P, h1, h2, hL1, hL_even, rfl, hno, hstop, hdefic_eq, hmate_u, ?_⟩
  intro z hz
  simp only [Matching.swap, hz, ↓reduceIte]

private lemma altSeq_disjoint {V : Type u} {H : SimpleGraph V}
    (M₁ M₂ : Matching H) (u v : V) (huv : u ≠ v)
    (hm₁_u : M₁.mate u = u) (hm₁_v : M₁.mate v = v)
    (Lu Lv : ℕ) (hLu_even : Even Lu)
    (hno_u : ∀ k < Lu, altSeq M₁ M₂ u (k + 1) ≠ altSeq M₁ M₂ u k)
    (hstop_u : altSeq M₁ M₂ u (Lu + 1) = altSeq M₁ M₂ u Lu)
    (hno_v : ∀ k < Lv, altSeq M₁ M₂ v (k + 1) ≠ altSeq M₁ M₂ v k) :
    ∀ j ≤ Lv, ∀ i ≤ Lu, altSeq M₁ M₂ u i ≠ altSeq M₁ M₂ v j := by
  intro j
  induction j with
  | zero =>
    intro _ i hiLu heq
    cases i with
    | zero => exact huv heq
    | succ i' =>
      by_cases heven : Even i'
      · have hne : i' + 1 ≠ Lu := by
          intro h
          have : Even (i' + 1) := h ▸ hLu_even
          rw [Nat.even_add_one] at this
          exact this heven
        have hlt : i' + 1 < Lu := by omega
        have hstep : ¬ Even (i' + 1) := by rw [Nat.even_add_one]; tauto
        have h1 : altSeq M₁ M₂ u (i' + 2) = M₁.mate (altSeq M₁ M₂ u (i' + 1)) := by
          simp [altSeq, altStep, hstep]
        have h2 : M₁.mate (altSeq M₁ M₂ u (i' + 1)) = altSeq M₁ M₂ u (i' + 1) := by
          rw [heq]; exact hm₁_v
        exact hno_u (i' + 1) hlt (h1.trans h2)
      · have h1 : altSeq M₁ M₂ u (i' + 1) = M₁.mate (altSeq M₁ M₂ u i') := by
          simp [altSeq, altStep, heven]
        have h2 : M₁.mate (altSeq M₁ M₂ u (i' + 1)) = altSeq M₁ M₂ u (i' + 1) := by
          rw [heq]; exact hm₁_v
        have h3 : altSeq M₁ M₂ u i' = altSeq M₁ M₂ u (i' + 1) := by
          have := congrArg M₁.mate h1
          rw [M₁.invol] at this
          exact this.symm.trans h2
        exact hno_u i' (by omega) h3.symm
  | succ k ih =>
    intro hkLv i hiLu heq
    have ih' := ih (by omega)
    by_cases hpar : Even i ↔ Even k
    · have hstep_eq : altStep M₁ M₂ i = altStep M₁ M₂ k := by ext z; simp [altStep, hpar]
      have heq_step : altStep M₁ M₂ i (altSeq M₁ M₂ u i) = altSeq M₁ M₂ v k := by
        have : altStep M₁ M₂ k (altSeq M₁ M₂ v k) = altSeq M₁ M₂ u i := heq.symm
        have := congrArg (altStep M₁ M₂ k) this
        rw [altStep_invol, ← hstep_eq] at this
        exact this.symm
      by_cases hiLu_eq : i = Lu
      · subst i
        have hstep_Lu : altSeq M₁ M₂ u (Lu + 1) = altSeq M₁ M₂ v k := heq_step
        rw [hstop_u] at hstep_Lu
        have hcontra : altSeq M₁ M₂ v (k + 1) = altSeq M₁ M₂ v k := heq.symm.trans hstep_Lu
        exact hno_v k (by omega) hcontra
      · exact ih' (i + 1) (by omega) heq_step
    · cases i with
      | zero =>
        have hk_odd : ¬ Even k := fun he => hpar (iff_of_true ⟨0, rfl⟩ he)
        have h1 : altSeq M₁ M₂ v (k + 1) = M₁.mate (altSeq M₁ M₂ v k) := by
          simp [altSeq, altStep, hk_odd]
        have h2 : altSeq M₁ M₂ v k = u := by
          have := congrArg M₁.mate h1
          rw [M₁.invol, ← heq] at this
          exact this.symm.trans hm₁_u
        exact hno_v k (by omega) (heq.symm.trans h2.symm)
      | succ i' =>
        have hpar' : Even i' ↔ Even k := by
          rw [Nat.even_add_one] at hpar
          tauto
        have hstep_eq : altStep M₁ M₂ i' = altStep M₁ M₂ k := by ext z; simp [altStep, hpar']
        have h1 : altStep M₁ M₂ k (altSeq M₁ M₂ u i') = altStep M₁ M₂ k (altSeq M₁ M₂ v k) := by
          change altStep M₁ M₂ k (altSeq M₁ M₂ u i') = altSeq M₁ M₂ v (k + 1)
          rw [← hstep_eq]
          exact heq
        have h2 := congrArg (altStep M₁ M₂ k) h1
        rw [altStep_invol, altStep_invol] at h2
        exact ih' i' (by omega) h2

private lemma gallai_defic_eq_one {V : Type u} [Fintype V] [Nonempty V] {H : SimpleGraph V}
    (hconn : H.Connected) (d_min : ℕ)
    (hd_min : ∀ M : Matching H, d_min ≤ M.defic)
    (hmiss : ∀ x : V, ∃ M : Matching H, M.defic = d_min ∧ M.mate x = x) :
    d_min = 1 := by
  have hd1 : 1 ≤ d_min := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨M, hMd, hMv⟩ := hmiss v
    rw [← hMd]
    exact Finset.card_pos.mpr ⟨v, (M.mem_fixedSet v).mpr hMv⟩
  by_contra hne1
  have hd2 : 2 ≤ d_min := by omega
  have hex_pair : ∃ d : ℕ, ∃ (M : Matching H) (u v : V),
      M.defic = d_min ∧ M.mate u = u ∧ M.mate v = v ∧ u ≠ v ∧ H.dist u v = d := by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    obtain ⟨M₀, hM₀d, _⟩ := hmiss v₀
    have hcard_pos : 1 < M₀.fixedSet.card := by
      have : M₀.defic = d_min := hM₀d
      unfold Matching.defic at this
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard_pos
    rw [M₀.mem_fixedSet] at ha hb
    exact ⟨H.dist a b, M₀, a, b, hM₀d, ha, hb, hab, rfl⟩
  let d := Nat.find hex_pair
  obtain ⟨M, u, v, hMd, hMu, hMv, huv, hdist⟩ := Nat.find_spec hex_pair
  have hd_pos : 0 < d := by
    by_contra hd0
    have heq0 : H.dist u v = 0 := by omega
    have hne : H.dist u v ≠ 0 :=
      SimpleGraph.dist_ne_zero_iff_ne_and_reachable.mpr ⟨huv, hconn u v⟩
    exact hne heq0
  have hd_ne_one : d ≠ 1 := by
    intro hd1_eq
    have hadj : H.Adj u v := SimpleGraph.dist_eq_one_iff_adj.mp (hdist.trans hd1_eq)
    let M' : Matching H :=
      { mate := fun x => if x = u then v else if x = v then u else M.mate x
        invol := fun x => by
          by_cases hxu : x = u
          · subst hxu; simp [huv.symm]
          · by_cases hxv : x = v
            · subst hxv; simp
            · have hm_ne_u : M.mate x ≠ u := by
                intro h; apply hxu; rw [← M.invol x, h, hMu]
              have hm_ne_v : M.mate x ≠ v := by
                intro h; apply hxv; rw [← M.invol x, h, hMv]
              simp [hxu, hxv, hm_ne_u, hm_ne_v, M.invol]
        adj_of_ne := fun x hne => by
          by_cases hxu : x = u
          · subst hxu; simp only [↓reduceIte]; exact hadj
          · by_cases hxv : x = v
            · subst hxv; simp only [huv.symm, ↓reduceIte]; exact hadj.symm
            · simp only [hxu, ↓reduceIte, hxv] at hne ⊢
              exact M.adj_of_ne x hne }
    have hfilt : M'.fixedSet = (M.fixedSet.erase u).erase v := by
      ext x
      simp only [Matching.mem_fixedSet, Finset.mem_erase, M']
      by_cases hxu : x = u
      · subst hxu; simp [huv.symm]
      · by_cases hxv : x = v
        · subst hxv; simp [hxu, huv]
        · simp [hxu, hxv]
    have hv_in : v ∈ M.fixedSet.erase u :=
      Finset.mem_erase.mpr ⟨huv.symm, (M.mem_fixedSet v).mpr hMv⟩
    have hu_in : u ∈ M.fixedSet := (M.mem_fixedSet u).mpr hMu
    have hdef_lt : M'.defic + 2 = M.defic := by
      unfold Matching.defic
      rw [hfilt, Finset.card_erase_of_mem hv_in, Finset.card_erase_of_mem hu_in]
      have hc : 2 ≤ M.fixedSet.card := by
        have : M.defic = d_min := hMd
        unfold Matching.defic at this
        omega
      omega
    have hle := hd_min M'
    omega
  have hd_ge2 : 2 ≤ d := by omega
  obtain ⟨p, _, hp_len⟩ := hconn.exists_path_of_dist u v
  rw [hdist] at hp_len
  cases p with
  | nil => rw [SimpleGraph.Walk.length_nil] at hp_len; omega
  | @cons _ w _ h_uw q =>
    simp only [SimpleGraph.Walk.length_cons] at hp_len
    have huw : u ≠ w := h_uw.ne
    have hdist_uw : H.dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h_uw
    have hdist_wv : H.dist w v ≤ d - 1 := by
      have hle := H.dist_le q
      omega
    have hwv : w ≠ v := by
      intro heq
      subst heq
      rw [hdist_uw] at hdist
      omega
    obtain ⟨M', hM'd, hM'w⟩ := hmiss w
    have hM'u : M'.mate u ≠ u := by
      intro hfix
      have hmin := Nat.find_min hex_pair (m := 1) (by omega)
      exact hmin ⟨M', u, w, hM'd, hfix, hM'w, huw, hdist_uw⟩
    have hM'v : M'.mate v ≠ v := by
      intro hfix
      have hmin := Nat.find_min hex_pair (m := H.dist w v) (by omega)
      exact hmin ⟨M', w, v, hM'd, hM'w, hfix, hwv, rfl⟩
    obtain ⟨Lu, Pu, h1u, h2u, _, hLu_even, hPu_eq, hno_u, hstop_u, hdu_eq, hM'u_fix, hM'u_out⟩ :=
      altSeq_even_and_swap M M' u (fun N => hMd ▸ hd_min N) hMu hM'u
    obtain ⟨Lv, Pv, h1v, h2v, _, _, hPv_eq, hno_v, _, hdv_eq, hM'v_fix, hM'v_out⟩ :=
      altSeq_even_and_swap M M' v (fun N => hMd ▸ hd_min N) hMv hM'v
    have hdisj : ∀ j ≤ Lv, ∀ i ≤ Lu, altSeq M M' u i ≠ altSeq M M' v j :=
      altSeq_disjoint M M' u v huv hMu hMv Lu Lv hLu_even hno_u hstop_u hno_v
    by_cases hw_Pu : w ∈ Pu
    · have hw_nPv : w ∉ Pv := by
        rw [hPu_eq] at hw_Pu
        rw [hPv_eq]
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw_Pu
        intro hw_mem
        obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp hw_mem
        exact hdisj j (by simpa [Finset.mem_range] using hj)
          i (by simpa [Finset.mem_range] using hi) hij.symm
      let M'' := M'.swap M Pv h2v h1v
      have hM''w : M''.mate w = w := by rw [hM'v_out w hw_nPv]; exact hM'w
      have hmin := Nat.find_min hex_pair (m := H.dist w v) (by omega)
      exact hmin ⟨M'', w, v, hdv_eq.trans hM'd, hM''w, hM'v_fix, hwv, rfl⟩
    · let M'' := M'.swap M Pu h2u h1u
      have hM''w : M''.mate w = w := by rw [hM'u_out w hw_Pu]; exact hM'w
      have hmin := Nat.find_min hex_pair (m := 1) (by omega)
      exact hmin ⟨M'', u, w, hdu_eq.trans hM'd, hM'u_fix, hM''w, huw, hdist_uw⟩

/- Section 4: Connected-component decomposition -/

private def Matching.restrictToClosed {V : Type u} {H : SimpleGraph V}
    (M : Matching H) (S : Set V)
    (hS : ∀ u v, H.Adj u v → u ∈ S → v ∈ S) : Matching (H.induce S) where
  mate x := ⟨M.mate x.1, by
    by_cases hne : M.mate x.1 = x.1
    · rw [hne]; exact x.2
    · exact hS x.1 (M.mate x.1) (M.adj_of_ne x.1 hne) x.2⟩
  invol x := Subtype.ext (M.invol x.1)
  adj_of_ne x hne := by
    have hne1 : M.mate x.1 ≠ x.1 := fun h => hne (Subtype.ext h)
    exact M.adj_of_ne x.1 hne1

private def glueMate {V : Type u} {H : SimpleGraph V}
    (f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp)) (v : V) : V :=
  ((f (H.connectedComponentMk v)).mate ⟨v, rfl⟩).1

private lemma glueMate_congr {V : Type u} {H : SimpleGraph V}
    (f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp))
    {C₁ C₂ : H.ConnectedComponent} (h : C₁ = C₂) (x : C₁.supp) :
    ((f C₁).mate x).1 = ((f C₂).mate ⟨x.1, h ▸ x.2⟩).1 := by
  subst h; rfl

private lemma glueMate_apply_mem {V : Type u} {H : SimpleGraph V}
    (f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp))
    (C : H.ConnectedComponent) (x : C.supp) :
    glueMate f x.1 = ((f C).mate x).1 :=
  glueMate_congr f x.2 ⟨x.1, rfl⟩

private def Matching.glueComponents {V : Type u} {H : SimpleGraph V}
    (f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp)) : Matching H where
  mate := glueMate f
  invol v := by
    let C := H.connectedComponentMk v
    let x : C.supp := ⟨v, rfl⟩
    let y : C.supp := (f C).mate x
    have hy : glueMate f v = y.1 := rfl
    rw [hy, glueMate_apply_mem f C y]
    exact congrArg Subtype.val ((f C).invol x)
  adj_of_ne v hne := by
    let C := H.connectedComponentMk v
    let x : C.supp := ⟨v, rfl⟩
    have hne' : (f C).mate x ≠ x := fun h => hne (congrArg Subtype.val h)
    exact (f C).adj_of_ne x hne'

private lemma Matching.defic_glueComponents {V : Type u} [Fintype V] {H : SimpleGraph V}
    (f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp))
    [Fintype H.ConnectedComponent] :
    (Matching.glueComponents f).defic = ∑ C : H.ConnectedComponent, (f C).defic := by
  unfold Matching.defic
  rw [Finset.card_eq_sum_card_fiberwise (s := (Matching.glueComponents f).fixedSet)
    (f := H.connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun C _ => ?_
  refine Finset.card_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    have hfix := (Matching.mem_fixedSet _ v).mp hv.1
    refine (Matching.mem_fixedSet _ _).mpr (Subtype.ext ?_)
    rw [← glueMate_apply_mem f C ⟨v, hv.2⟩]
    exact hfix
  · intro _ _ _ _ h
    exact congrArg Subtype.val h
  · intro x hx
    rw [Matching.mem_fixedSet] at hx
    refine ⟨x.1, Finset.mem_filter.mpr ⟨(Matching.mem_fixedSet _ _).mpr ?_, x.2⟩, rfl⟩
    change glueMate f x.1 = x.1
    rw [glueMate_apply_mem f C x, hx]

private lemma Matching.defic_eq_sum_components {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) [Fintype H.ConnectedComponent] :
    M.defic = ∑ C : H.ConnectedComponent,
      (M.restrictToClosed C.supp (fun _ _ hadj hc => (C.mem_supp_congr_adj hadj).mp hc)).defic := by
  let f : ∀ C : H.ConnectedComponent, Matching (H.induce C.supp) :=
    fun C => M.restrictToClosed C.supp (fun _ _ hadj hc => (C.mem_supp_congr_adj hadj).mp hc)
  have hglue : Matching.glueComponents f = M := by
    cases M
    congr 1
  calc M.defic = (Matching.glueComponents f).defic := by rw [hglue]
    _ = ∑ C : H.ConnectedComponent, (f C).defic := Matching.defic_glueComponents f

private def Matching.restrictToInterComponent {V : Type u} {H : SimpleGraph V}
    (S : Set V) (M : Matching (H.induce S)) (C : H.ConnectedComponent) :
    Matching (H.induce (S ∩ C.supp)) where
  mate x := ⟨(M.mate ⟨x.1, x.2.1⟩).1, ⟨(M.mate ⟨x.1, x.2.1⟩).2, by
    by_cases hne : M.mate ⟨x.1, x.2.1⟩ = ⟨x.1, x.2.1⟩
    · rw [hne]; exact x.2.2
    · exact (C.mem_supp_congr_adj (M.adj_of_ne ⟨x.1, x.2.1⟩ hne)).mp x.2.2⟩⟩
  invol x := by
    apply Subtype.ext
    dsimp only
    have h1 : (⟨(M.mate ⟨x.1, x.2.1⟩).1, (M.mate ⟨x.1, x.2.1⟩).2⟩ : S) = M.mate ⟨x.1, x.2.1⟩ :=
      Subtype.coe_eta _ _
    rw [h1]
    exact congrArg Subtype.val (M.invol ⟨x.1, x.2.1⟩)
  adj_of_ne x hne := by
    have hne' : M.mate ⟨x.1, x.2.1⟩ ≠ ⟨x.1, x.2.1⟩ := fun h =>
      hne (Subtype.ext (congrArg (Subtype.val : S → V) h))
    exact M.adj_of_ne ⟨x.1, x.2.1⟩ hne'

private lemma Matching.card_add_defic_eq_sum_inter_components {V : Type u} [Fintype V]
    {H : SimpleGraph V} (S : Set V) (M : Matching (H.induce S))
    [Fintype H.ConnectedComponent] :
    Fintype.card S + M.defic =
      ∑ C : H.ConnectedComponent,
        (Fintype.card (S ∩ C.supp : Set V) + (M.restrictToInterComponent S C).defic) := by
  have hS_sum : Fintype.card S = ∑ C : H.ConnectedComponent, Fintype.card (S ∩ C.supp : Set V) := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun x : S => H.connectedComponentMk x.1) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro _ _ _ _ h; exact Subtype.ext (congrArg (Subtype.val : (S ∩ C.supp : Set V) → V) h)
    · intro y _
      refine ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2.2⟩, rfl⟩
  have hdefic_sum : M.defic =
      ∑ C : H.ConnectedComponent, (M.restrictToInterComponent S C).defic := by
    unfold Matching.defic
    rw [Finset.card_eq_sum_card_fiberwise (s := M.fixedSet)
      (f := fun x : S => H.connectedComponentMk x.1) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun C _ => ?_
    refine Finset.card_bij (fun x hx => ⟨x.1, x.2, (Finset.mem_filter.mp hx).2⟩) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hfix := (Matching.mem_fixedSet M x).mp hx.1
      exact (Matching.mem_fixedSet _ _).mpr
        (Subtype.ext (congrArg (Subtype.val : S → V) hfix))
    · intro _ _ _ _ h; exact Subtype.ext (congrArg (Subtype.val : (S ∩ C.supp : Set V) → V) h)
    · intro y hy
      rw [Matching.mem_fixedSet] at hy
      have hfix : M.mate ⟨y.1, y.2.1⟩ = ⟨y.1, y.2.1⟩ :=
        Subtype.ext (congrArg (Subtype.val : (S ∩ C.supp : Set V) → V) hy)
      refine ⟨⟨y.1, y.2.1⟩, Finset.mem_filter.mpr
        ⟨(Matching.mem_fixedSet M _).mpr hfix, y.2.2⟩, rfl⟩
  rw [hS_sum, hdefic_sum, Finset.sum_add_distrib]

/- Section 5: Component splitting and allocator -/

private lemma Matching.card_add_defic_transport {V₁ V₂ : Type u} [Fintype V₁] [Fintype V₂]
    {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂} (φ : H₁ ≃g H₂) (M : Matching H₁) :
    Fintype.card V₁ + M.defic = Fintype.card V₂ + (M.transport φ).defic := by
  rw [Fintype.card_congr φ.toEquiv, M.defic_transport φ]

private lemma Matching.card_add_defic_ge_of_odd {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) (x : ℕ) (hx : 1 ≤ x) (hcard : Fintype.card V = 2 * x - 1) :
    2 * x ≤ Fintype.card V + M.defic := by
  obtain ⟨t, ht⟩ := M.even_card_add_defic
  omega

private lemma Matching.card_add_defic_ge_of_fixed_even {V : Type u} [Fintype V] {H : SimpleGraph V}
    (M : Matching H) (w : V) (hw : M.mate w = w) (y : ℕ) (hy : 1 ≤ y)
    (hcard : Fintype.card V = 2 * y - 2) :
    2 * y ≤ Fintype.card V + M.defic := by
  have hd1 : 1 ≤ M.defic := Finset.card_pos.mpr ⟨w, (M.mem_fixedSet w).mpr hw⟩
  obtain ⟨t, ht⟩ := M.even_card_add_defic
  omega

private lemma Matching.card_add_defic_ge_of_transport {V₁ V₂ : Type u}
    [Fintype V₁] [Fintype V₂] {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂}
    (φ : H₁ ≃g H₂) (M : Matching H₁) (b : ℕ)
    (hb : ∀ N : Matching H₂, b ≤ Fintype.card V₂ + N.defic) :
    b ≤ Fintype.card V₁ + M.defic := by
  rw [Matching.card_add_defic_transport φ M]
  exact hb (M.transport φ)

private lemma split_odd_triangleFree_aux {W : Type u} [Fintype W] (H₀ : SimpleGraph W)
    (hconn : H₀.Connected) (htri : H₀.CliqueFree 3)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card W = 2 * m + 1)
    (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x + y = m + 2)
    (hm_le : m ≤ 2 * x - 1) :
    ∃ S : Set W,
      (∀ M : Matching (H₀.induce S), 2 * x ≤ Fintype.card S + M.defic) ∧
      (∀ M : Matching (H₀.induce Sᶜ), 2 * y ≤ Fintype.card (Sᶜ : Set W) + M.defic) := by
  have hedge : ∃ u v : W, H₀.Adj u v := by
    have hcard2 : 1 < (Finset.univ : Finset W).card := by rw [Finset.card_univ]; omega
    obtain ⟨u, _, v, _, huv⟩ := Finset.one_lt_card.mp hcard2
    obtain ⟨p⟩ := hconn u v
    cases p with
    | nil => exact (huv rfl).elim
    | @cons _ z _ h _ => exact ⟨u, z, h⟩
  obtain ⟨u, v, huv⟩ := hedge
  let Nu : Finset W := Finset.univ.filter (fun z => H₀.Adj u z)
  let Nv : Finset W := Finset.univ.filter (fun z => H₀.Adj v z)
  have hdisj : Disjoint Nu Nv := by
    rw [Finset.disjoint_left]
    intro z hzu hzv
    simp only [Nu, Nv, Finset.mem_filter, Finset.mem_univ, true_and] at hzu hzv
    have hne_uz : u ≠ z := hzu.ne
    have hne_vz : v ≠ z := hzv.ne
    have hcard3 : ({u, v, z} : Finset W).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne_vz]
      simp [huv.ne, hne_uz]
    have hclique : H₀.IsNClique 3 {u, v, z} := by
      refine ⟨?_, hcard3⟩
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      all_goals first | exact (hab rfl).elim | exact huv | exact huv.symm | exact hzu |
        exact hzu.symm | exact hzv | exact hzv.symm
    exact htri {u, v, z} hclique
  have hsum_le : Nu.card + Nv.card ≤ Fintype.card W := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have hw_ex : ∃ w : W, (Finset.univ.filter (fun z => H₀.Adj w z)).card ≤ m := by
    by_cases hNu : Nu.card ≤ m
    · exact ⟨u, hNu⟩
    · refine ⟨v, ?_⟩
      change Nv.card ≤ m
      omega
  obtain ⟨w, hNw_le⟩ := hw_ex
  let Nw : Finset W := Finset.univ.filter (fun z => H₀.Adj w z)
  have hNw_le' : Nw.card ≤ m := hNw_le
  have hNw_sub : Nw ⊆ Finset.univ.erase w := by
    intro z hz
    simp only [Nw, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact Finset.mem_erase.mpr ⟨hz.ne.symm, Finset.mem_univ z⟩
  let R := (Finset.univ.erase w) \ Nw
  have hR_card : R.card = 2 * m - Nw.card := by
    rw [Finset.card_sdiff_of_subset hNw_sub, Finset.card_erase_of_mem (Finset.mem_univ w),
      Finset.card_univ, hcard]
    omega
  have hB_need : 2 * x - 1 - Nw.card ≤ R.card := by omega
  obtain ⟨B, hB_sub, hB_card⟩ := Finset.exists_subset_card_eq hB_need
  let A := Nw ∪ B
  have hdisj_AB : Disjoint Nw B := by
    rw [Finset.disjoint_left]
    intro z hz hzb
    exact (Finset.mem_sdiff.mp (hB_sub hzb)).2 hz
  have hA_card : A.card = 2 * x - 1 := by
    rw [Finset.card_union_of_disjoint hdisj_AB, hB_card]
    omega
  have hw_not_A : w ∉ A := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hnw | hb
    · exact (Finset.mem_erase.mp (hNw_sub hnw)).1 rfl
    · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp (hB_sub hb)).1).1 rfl
  let S : Set W := (A : Set W)
  have hS_card : Fintype.card S = 2 * x - 1 := by
    have h1 : Fintype.card S = Fintype.card A :=
      Fintype.card_congr ⟨fun z => ⟨z.1, z.2⟩, fun z => ⟨z.1, z.2⟩,
        fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩
    rw [h1, Fintype.card_coe]; exact hA_card
  have hSc_card : Fintype.card (Sᶜ : Set W) = 2 * y - 2 := by
    rw [card_set_compl, hS_card, hcard]
    omega
  refine ⟨S, ?_, ?_⟩
  · intro M
    convert Matching.card_add_defic_ge_of_odd M x (by omega) (by convert hS_card)
  · intro M
    have hw_Sc : w ∈ Sᶜ := hw_not_A
    have hm_w : M.mate ⟨w, hw_Sc⟩ = ⟨w, hw_Sc⟩ := by
      by_contra hne
      have hadj : H₀.Adj w (M.mate ⟨w, hw_Sc⟩).1 := M.adj_of_ne ⟨w, hw_Sc⟩ hne
      have hmem_Nw : (M.mate ⟨w, hw_Sc⟩).1 ∈ Nw :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      have hmem_A : (M.mate ⟨w, hw_Sc⟩).1 ∈ S := Finset.mem_union_left B hmem_Nw
      exact (M.mate ⟨w, hw_Sc⟩).2 hmem_A
    convert Matching.card_add_defic_ge_of_fixed_even M ⟨w, hw_Sc⟩ hm_w y (by omega) (by convert hSc_card)

private lemma split_odd_triangleFree {W : Type u} [Fintype W] (H₀ : SimpleGraph W)
    (hconn : H₀.Connected) (htri : H₀.CliqueFree 3)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Fintype.card W = 2 * m + 1)
    (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x + y = m + 2) :
    ∃ S : Set W,
      (∀ M : Matching (H₀.induce S), 2 * x ≤ Fintype.card S + M.defic) ∧
      (∀ M : Matching (H₀.induce Sᶜ), 2 * y ≤ Fintype.card (Sᶜ : Set W) + M.defic) := by
  by_cases hm_le : m ≤ 2 * x - 1
  · exact split_odd_triangleFree_aux H₀ hconn htri m hm hcard x y hx hy hxy hm_le
  · have hm_le' : m ≤ 2 * y - 1 := by omega
    obtain ⟨T, hT1, hT2⟩ := split_odd_triangleFree_aux H₀ hconn htri m hm hcard y x hy hx (by omega) hm_le'
    refine ⟨Tᶜ, fun M => by convert hT2 M, ?_⟩
    intro M
    let φ : (H₀.induce (Tᶜ : Set W)ᶜ) ≃g (H₀.induce T) :=
      { toFun := fun v => ⟨v.1, by have hv := v.2; simp only [Set.mem_compl_iff, not_not] at hv; exact hv⟩
        invFun := fun v => ⟨v.1, by simp [v.2]⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl
        map_rel_iff' := Iff.rfl }
    convert Matching.card_add_defic_ge_of_transport φ M (2 * y) (fun N => by convert hT1 N)

private lemma alloc_components :
    ∀ (r : ℕ) (c : Fin r → ℕ) (a b : ℕ),
      (∀ i, 3 ≤ c i) → 2 ≤ a → 2 ≤ b → a + b = (∑ i, c i) + 1 →
      ∃ x y : Fin r → ℕ,
        a ≤ ∑ i, x i ∧ b ≤ ∑ i, y i ∧
        ∀ i, (x i = c i ∧ y i = 0) ∨ (x i = 0 ∧ y i = c i) ∨
             (2 ≤ x i ∧ 2 ≤ y i ∧ x i + y i = c i + 1) := by
  intro r
  induction r with
  | zero =>
    intro c a b _ ha hb hab
    simp at hab
    omega
  | succ r ih =>
    intro c a b hc ha hb hab
    cases r with
    | zero =>
      refine ⟨fun _ => a, fun _ => b, by simp, by simp, fun i => ?_⟩
      refine Or.inr (Or.inr ⟨ha, hb, ?_⟩)
      rw [Fin.eq_zero i]
      simpa using hab
    | succ r' =>
      let c' : Fin (r' + 1) → ℕ := fun i => c i.castSucc
      let c_last := c (Fin.last (r' + 1))
      have hc_last : 3 ≤ c_last := hc (Fin.last (r' + 1))
      let S := ∑ i : Fin (r' + 1), c' i
      have hS_ge : 3 ≤ S := by
        have h0 : c' 0 ≤ S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        dsimp only [c'] at h0
        have := hc (Fin.castSucc (0 : Fin (r' + 1)))
        omega
      have hab_S : a + b = S + c_last + 1 := by
        rw [Fin.sum_univ_castSucc] at hab
        exact hab
      by_cases ha_big : c_last + 2 ≤ a
      · obtain ⟨x', y', hx', hy', hspec'⟩ :=
          ih c' (a - c_last) b (fun i => hc i.castSucc) (by omega) hb (by omega)
        refine ⟨Fin.snoc x' c_last, Fin.snoc y' 0, ?_, ?_, fun i => ?_⟩
        · rw [Fin.sum_univ_castSucc]
          simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
        · rw [Fin.sum_univ_castSucc]
          simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
        · refine Fin.lastCases ?_ ?_ i
          · exact Or.inl ⟨by simp [Fin.snoc_last, c_last], by simp [Fin.snoc_last]⟩
          · intro j; simp [Fin.snoc_castSucc, c', hspec' j]
      · by_cases hb_big : c_last + 2 ≤ b
        · obtain ⟨x', y', hx', hy', hspec'⟩ :=
            ih c' a (b - c_last) (fun i => hc i.castSucc) ha (by omega) (by omega)
          refine ⟨Fin.snoc x' 0, Fin.snoc y' c_last, ?_, ?_, fun i => ?_⟩
          · rw [Fin.sum_univ_castSucc]
            simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
          · rw [Fin.sum_univ_castSucc]
            simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
          · refine Fin.lastCases ?_ ?_ i
            · exact Or.inr (Or.inl ⟨by simp [Fin.snoc_last], by simp [Fin.snoc_last, c_last]⟩)
            · intro j; simp [Fin.snoc_castSucc, c', hspec' j]
        · let t := max 4 a
          let a' := min (S - 1) (t - 2)
          let b' := S + 1 - a'
          let x_last := t - a'
          let y_last := c_last + 1 - x_last
          have ha'2 : 2 ≤ a' := by omega
          have hb'2 : 2 ≤ b' := by omega
          have hab' : a' + b' = S + 1 := by omega
          have hxl2 : 2 ≤ x_last := by omega
          have hyl2 : 2 ≤ y_last := by omega
          have hxyl : x_last + y_last = c_last + 1 := by omega
          obtain ⟨x', y', hx', hy', hspec'⟩ :=
            ih c' a' b' (fun i => hc i.castSucc) ha'2 hb'2 hab'
          refine ⟨Fin.snoc x' x_last, Fin.snoc y' y_last, ?_, ?_, fun i => ?_⟩
          · rw [Fin.sum_univ_castSucc]
            simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
          · rw [Fin.sum_univ_castSucc]
            simp [Fin.snoc_castSucc, Fin.snoc_last]; omega
          · refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last]; exact Or.inr (Or.inr ⟨hxl2, hyl2, hxyl⟩)
            · intro j; simp [Fin.snoc_castSucc, c', hspec' j]

/- Section 6: Universal vertex chromatic boost and main theorem -/

private lemma chromaticNumber_boost_universal {V : Type u} [Fintype V] (G : SimpleGraph V)
    (s : Set V) (v : V) (hvs : v ∈ s) (huniv : ∀ u, u ≠ v → G.Adj v u)
    (r : ℕ) (hsub : (r : ℕ∞) ≤ (G.induce (s \ {v} : Set V)).chromaticNumber) :
    ((r + 1 : ℕ) : ℕ∞) ≤ (G.induce s).chromaticNumber := by
  rw [SimpleGraph.le_chromaticNumber_iff_colorable] at hsub ⊢
  intro m ⟨C⟩
  have hm_pos : 1 ≤ m := Fin.pos (C ⟨v, hvs⟩)
  let cv := C ⟨v, hvs⟩
  let e : {c : Fin m // c ≠ cv} ≃ Fin (m - 1) :=
    Fintype.equivFinOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_fin]
      simp)
  have hcol_sub : (G.induce (s \ {v} : Set V)).Colorable (m - 1) := by
    refine ⟨⟨fun x => e ⟨C ⟨x.1, x.2.1⟩, ?_⟩, ?_⟩⟩
    · have hne : x.1 ≠ v := x.2.2
      have hadj : (G.induce s).Adj ⟨x.1, x.2.1⟩ ⟨v, hvs⟩ := (huniv x.1 hne).symm
      exact C.valid hadj
    · intro x y hadj heq
      have heq' : C ⟨x.1, x.2.1⟩ = C ⟨y.1, y.2.1⟩ :=
        congrArg Subtype.val (e.injective heq)
      exact C.valid (show (G.induce s).Adj ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ from hadj) heq'
  have hr := hsub (m - 1) hcol_sub
  omega

private lemma erdos628_no_singleton_components {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG_indep : G.indepNum ≤ 2)
    (k a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a + b = k + 1)
    [Fintype (Gᶜ).ConnectedComponent]
    (hcomp_odd : ∀ C : (Gᶜ).ConnectedComponent, Odd (Fintype.card C.supp))
    (hcomp_ne_three : ∀ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp ≠ 3)
    (hsingleton : ∀ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp ≠ 1)
    (hc_sum : ∑ C : (Gᶜ).ConnectedComponent, (Fintype.card C.supp + 1) / 2 = k) :
    ∃ (s : Set V),
      (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
      (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber := by
  let H := Gᶜ
  let c : H.ConnectedComponent → ℕ := fun C => (Fintype.card C.supp + 1) / 2
  have hall_ge5 : ∀ C : H.ConnectedComponent, ∃ m, 2 ≤ m ∧ Fintype.card C.supp = 2 * m + 1 := by
    intro C
    rcases hcomp_odd C with ⟨m, hm⟩
    have hne1 := hsingleton C
    have hne3 := hcomp_ne_three C
    refine ⟨m, by omega, by omega⟩
  let r := Fintype.card H.ConnectedComponent
  let e : Fin r ≃ H.ConnectedComponent := (Fintype.equivFin H.ConnectedComponent).symm
  have hc_ge3 : ∀ i : Fin r, 3 ≤ c (e i) := by
    intro i
    obtain ⟨m, _, hm_eq⟩ := hall_ge5 (e i)
    dsimp [c]; omega
  have hab_sum : a + b = (∑ i : Fin r, c (e i)) + 1 := by
    rw [Equiv.sum_comp e c]
    exact hab.trans (by rw [hc_sum])
  obtain ⟨x, y, hx_sum, hy_sum, hxy_spec⟩ :=
    alloc_components r (fun i => c (e i)) a b hc_ge3 ha hb hab_sum
  have hsplit_comp : ∀ i : Fin r, ∃ T : Set V, T ⊆ (e i).supp ∧
      (∀ M : Matching (H.induce T), 2 * x i ≤ Fintype.card T + M.defic) ∧
      (∀ M : Matching (H.induce ((e i).supp \ T : Set V)),
        2 * y i ≤ Fintype.card ((e i).supp \ T : Set V) + M.defic) := by
    intro i
    rcases hxy_spec i with ⟨hxi, hyi⟩ | ⟨hxi, hyi⟩ | ⟨hxi, hyi, hsumi⟩
    · refine ⟨(e i).supp, Set.Subset.rfl, ?_, ?_⟩
      · intro M
        have h2c : Fintype.card (e i).supp = 2 * x i - 1 := by
          obtain ⟨m, _, hm_eq⟩ := hall_ge5 (e i)
          have hc1 : c (e i) = m + 1 := by dsimp [c]; omega
          omega
        convert Matching.card_add_defic_ge_of_odd M (x i) (by have := hc_ge3 i; omega) (by convert h2c)
      · intro M; rw [hyi]; omega
    · refine ⟨∅, Set.empty_subset _, ?_, ?_⟩
      · intro M; rw [hxi]; omega
      · intro M
        let φ : (H.induce ((e i).supp \ ∅ : Set V)) ≃g (H.induce (e i).supp) :=
          { toFun := fun z => ⟨z.1, z.2.1⟩
            invFun := fun z => ⟨z.1, z.2, Set.notMem_empty _⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext rfl
            map_rel_iff' := Iff.rfl }
        have h2c : Fintype.card (e i).supp = 2 * y i - 1 := by
          obtain ⟨m, _, hm_eq⟩ := hall_ge5 (e i)
          have hc1 : c (e i) = m + 1 := by dsimp [c]; omega
          omega
        convert Matching.card_add_defic_ge_of_transport φ M (2 * y i) (fun N =>
          Matching.card_add_defic_ge_of_odd N (y i) (by have := hc_ge3 i; omega) (by convert h2c))
    · obtain ⟨m, hm2, hm_eq⟩ := hall_ge5 (e i)
      have htri_comp : (H.induce (e i).supp).CliqueFree 3 := by
        rw [SimpleGraph.cliqueFree_induce_iff]
        exact (compl_cliqueFree_three hG_indep).cliqueFreeOn
      have hc_eq : c (e i) = m + 1 := by dsimp [c]; omega
      obtain ⟨S₀, hS₀1, hS₀2⟩ := split_odd_triangleFree (H.induce (e i).supp)
        (e i).connected_toSimpleGraph htri_comp m hm2 hm_eq (x i) (y i) hxi hyi (by omega)
      let T : Set V := Subtype.val '' S₀
      refine ⟨T, Subtype.coe_image_subset (e i).supp S₀, ?_, ?_⟩
      · intro M
        let φ : (H.induce T) ≃g ((H.induce (e i).supp).induce S₀) :=
          { toFun := fun z => ⟨⟨z.1, Subtype.coe_image_subset _ _ z.2⟩, by
              obtain ⟨w, hw, hzw⟩ := z.2
              have hsub : w = ⟨z.1, Subtype.coe_image_subset _ _ z.2⟩ := Subtype.ext hzw
              rwa [← hsub]⟩
            invFun := fun z => ⟨z.1.1, ⟨z.1, z.2, rfl⟩⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
            map_rel_iff' := Iff.rfl }
        convert Matching.card_add_defic_ge_of_transport φ M (2 * x i) (fun N => by convert hS₀1 N)
      · intro M
        let φ : (H.induce ((e i).supp \ T : Set V)) ≃g ((H.induce (e i).supp).induce S₀ᶜ) :=
          { toFun := fun z => ⟨⟨z.1, z.2.1⟩, fun hw => z.2.2 ⟨⟨z.1, z.2.1⟩, hw, rfl⟩⟩
            invFun := fun z => ⟨z.1.1, ⟨z.1.2, by
              rintro ⟨w, hw, hzw⟩
              have hsub : w = z.1 := Subtype.ext hzw
              exact z.2 (hsub ▸ hw)⟩⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
            map_rel_iff' := Iff.rfl }
        convert Matching.card_add_defic_ge_of_transport φ M (2 * y i) (fun N => by convert hS₀2 N)
  choose T hT_sub hT_1 hT_2 using hsplit_comp
  let S : Set V := ⋃ i : Fin r, T i
  have hS_inter : ∀ i : Fin r, S ∩ (e i).supp = T i := by
    intro i
    ext z
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨j, hzj⟩, hzi⟩
      have hzj' : z ∈ (e j).supp := hT_sub j hzj
      have hij : j = i := e.injective (SimpleGraph.ConnectedComponent.eq_of_common_vertex hzj' hzi)
      subst hij; exact hzj
    · intro hzi
      exact ⟨⟨i, hzi⟩, hT_sub i hzi⟩
  have hSc_inter : ∀ i : Fin r, Sᶜ ∩ (e i).supp = (e i).supp \ T i := by
    intro i
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, S, Set.mem_iUnion, not_exists]
    constructor
    · rintro ⟨hzS, hzi⟩
      exact ⟨hzi, hzS i⟩
    · rintro ⟨hzi, hzn⟩
      refine ⟨fun j hzj => ?_, hzi⟩
      have hzj' : z ∈ (e j).supp := hT_sub j hzj
      have hij : j = i := e.injective (SimpleGraph.ConnectedComponent.eq_of_common_vertex hzj' hzi)
      subst hij; exact hzn hzj
  refine ⟨S, ?_, ?_⟩
  · rw [SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    obtain ⟨M, hM⟩ := (colorable_iff_exists_matching ((indepNum_induce_le G S).trans hG_indep) m).mp hm
    let ψ : (G.induce S)ᶜ ≃g (H.induce S) :=
      { toEquiv := Equiv.refl _
        map_rel_iff' := by intro x y; simp [H, SimpleGraph.compl_adj, Subtype.ext_iff] }
    rw [Matching.card_add_defic_transport ψ M] at hM
    let M' : Matching (H.induce S) := M.transport ψ
    have hsum := M'.card_add_defic_eq_sum_inter_components S
    have hcomp_lb : ∀ i : Fin r,
        2 * x i ≤ Fintype.card (S ∩ (e i).supp : Set V) + (M'.restrictToInterComponent S (e i)).defic := by
      intro i
      let φ : (H.induce (S ∩ (e i).supp : Set V)) ≃g (H.induce (T i)) :=
        { toFun := fun z => ⟨z.1, (hS_inter i) ▸ z.2⟩
          invFun := fun z => ⟨z.1, (hS_inter i).symm ▸ z.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_rel_iff' := Iff.rfl }
      exact Matching.card_add_defic_ge_of_transport φ (M'.restrictToInterComponent S (e i)) (2 * x i)
        (fun N => by convert hT_1 i N)
    have hsum_comp :
        ∑ i : Fin r, (Fintype.card (S ∩ (e i).supp : Set V) + (M'.restrictToInterComponent S (e i)).defic) =
        ∑ C : H.ConnectedComponent, (Fintype.card (S ∩ C.supp : Set V) + (M'.restrictToInterComponent S C).defic) :=
      Equiv.sum_comp e (fun C : H.ConnectedComponent =>
        Fintype.card (S ∩ C.supp : Set V) + (M'.restrictToInterComponent S C).defic)
    have htot : 2 * a ≤ Fintype.card S + M'.defic := by
      calc 2 * a ≤ 2 * ∑ i : Fin r, x i := by omega
        _ = ∑ i : Fin r, 2 * x i := Finset.mul_sum _ _ _
        _ ≤ ∑ i : Fin r,
              (Fintype.card (S ∩ (e i).supp : Set V) + (M'.restrictToInterComponent S (e i)).defic) :=
              Finset.sum_le_sum fun i _ => hcomp_lb i
        _ = ∑ C : H.ConnectedComponent,
              (Fintype.card (S ∩ C.supp : Set V) + (M'.restrictToInterComponent S C).defic) := hsum_comp
        _ = Fintype.card S + M'.defic := by convert hsum.symm
    have hM' : Fintype.card S + M'.defic ≤ 2 * m := hM
    omega
  · rw [SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    obtain ⟨M, hM⟩ := (colorable_iff_exists_matching ((indepNum_induce_le G Sᶜ).trans hG_indep) m).mp hm
    let ψ : (G.induce Sᶜ)ᶜ ≃g (H.induce Sᶜ) :=
      { toEquiv := Equiv.refl _
        map_rel_iff' := by intro x y; simp [H, SimpleGraph.compl_adj, Subtype.ext_iff] }
    rw [Matching.card_add_defic_transport ψ M] at hM
    let M' : Matching (H.induce Sᶜ) := M.transport ψ
    have hsum := M'.card_add_defic_eq_sum_inter_components Sᶜ
    have hcomp_lb : ∀ i : Fin r,
        2 * y i ≤ Fintype.card (Sᶜ ∩ (e i).supp : Set V) + (M'.restrictToInterComponent Sᶜ (e i)).defic := by
      intro i
      let φ : (H.induce (Sᶜ ∩ (e i).supp : Set V)) ≃g (H.induce ((e i).supp \ T i : Set V)) :=
        { toFun := fun z => ⟨z.1, (hSc_inter i) ▸ z.2⟩
          invFun := fun z => ⟨z.1, (hSc_inter i).symm ▸ z.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_rel_iff' := Iff.rfl }
      exact Matching.card_add_defic_ge_of_transport φ (M'.restrictToInterComponent Sᶜ (e i)) (2 * y i)
        (fun N => by convert hT_2 i N)
    have hsum_comp :
        ∑ i : Fin r, (Fintype.card (Sᶜ ∩ (e i).supp : Set V) + (M'.restrictToInterComponent Sᶜ (e i)).defic) =
        ∑ C : H.ConnectedComponent, (Fintype.card (Sᶜ ∩ C.supp : Set V) + (M'.restrictToInterComponent Sᶜ C).defic) :=
      Equiv.sum_comp e (fun C : H.ConnectedComponent =>
        Fintype.card (Sᶜ ∩ C.supp : Set V) + (M'.restrictToInterComponent Sᶜ C).defic)
    have htot : 2 * b ≤ Fintype.card (Sᶜ : Set V) + M'.defic := by
      calc 2 * b ≤ 2 * ∑ i : Fin r, y i := by omega
        _ = ∑ i : Fin r, 2 * y i := Finset.mul_sum _ _ _
        _ ≤ ∑ i : Fin r,
              (Fintype.card (Sᶜ ∩ (e i).supp : Set V) + (M'.restrictToInterComponent Sᶜ (e i)).defic) :=
              Finset.sum_le_sum fun i _ => hcomp_lb i
        _ = ∑ C : H.ConnectedComponent,
              (Fintype.card (Sᶜ ∩ C.supp : Set V) + (M'.restrictToInterComponent Sᶜ C).defic) := hsum_comp
        _ = Fintype.card (Sᶜ : Set V) + M'.defic := by convert hsum.symm
    have hM' : Fintype.card (Sᶜ : Set V) + M'.defic ≤ 2 * m := hM
    omega

private lemma gallai_components_summary {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG_indep : G.indepNum ≤ 2)
    (k n d : ℕ) (hcardV : Fintype.card V = n) (hnd_eq : n + d = 2 * k)
    (M₀ : Matching Gᶜ) (hM₀_d : M₀.defic = d)
    (hd_min : ∀ M : Matching Gᶜ, d ≤ M.defic)
    (hmiss : ∀ v : V, ∃ M : Matching Gᶜ, M.defic = d ∧ M.mate v = v)
    [Fintype (Gᶜ).ConnectedComponent] :
    (∀ C : (Gᶜ).ConnectedComponent, Odd (Fintype.card C.supp)) ∧
    (∀ (C : (Gᶜ).ConnectedComponent) (x : C.supp),
      ∃ M : Matching ((Gᶜ).induce C.supp), M.defic = 1 ∧ M.mate x = x) ∧
    (∀ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp ≠ 3) ∧
    (∑ C : (Gᶜ).ConnectedComponent, (Fintype.card C.supp + 1) / 2 = k) := by
  have hexC : ∀ C : (Gᶜ).ConnectedComponent,
      ∃ m, ∃ M : Matching ((Gᶜ).induce C.supp), M.defic = m :=
    fun C => ⟨(Matching.empty ((Gᶜ).induce C.supp)).defic, Matching.empty _, rfl⟩
  let dC : (Gᶜ).ConnectedComponent → ℕ := fun C => Nat.find (hexC C)
  have hdC_min : ∀ (C : (Gᶜ).ConnectedComponent) (M : Matching ((Gᶜ).induce C.supp)), dC C ≤ M.defic :=
    fun C M => Nat.find_min' (hexC C) ⟨M, rfl⟩
  have hdC_ex : ∀ C : (Gᶜ).ConnectedComponent, ∃ M : Matching ((Gᶜ).induce C.supp), M.defic = dC C :=
    fun C => Nat.find_spec (hexC C)
  have hd_sum_eq : d = ∑ C : (Gᶜ).ConnectedComponent, dC C := by
    apply le_antisymm
    · choose f hf using hdC_ex
      calc d ≤ (Matching.glueComponents f).defic := hd_min (Matching.glueComponents f)
        _ = ∑ C : (Gᶜ).ConnectedComponent, (f C).defic := by convert Matching.defic_glueComponents f
        _ = ∑ C : (Gᶜ).ConnectedComponent, dC C := Finset.sum_congr rfl fun C _ => by convert hf C
    · calc ∑ C : (Gᶜ).ConnectedComponent, dC C
          ≤ ∑ C : (Gᶜ).ConnectedComponent,
              (M₀.restrictToClosed C.supp (fun _ _ hadj hc => (C.mem_supp_congr_adj hadj).mp hc)).defic :=
              Finset.sum_le_sum fun C _ => by convert hdC_min C _
        _ = M₀.defic := by convert (Matching.defic_eq_sum_components M₀).symm
        _ = d := hM₀_d
  have hdC_eq_one : ∀ C : (Gᶜ).ConnectedComponent, dC C = 1 := by
    intro C
    have h_ne : Nonempty C.supp := ⟨C.out, C.out_eq⟩
    have hconnC : ((Gᶜ).induce C.supp).Connected := C.connected_toSimpleGraph
    refine gallai_defic_eq_one hconnC (dC C) (fun M => by convert hdC_min C M) ?_
    intro x
    obtain ⟨Mx, hMx_d, hMx_fix⟩ := hmiss x.1
    let MC := Mx.restrictToClosed C.supp (fun _ _ hadj hc => (C.mem_supp_congr_adj hadj).mp hc)
    have hMC_eq : MC.defic = dC C := by
      by_contra hne
      have hlt : dC C < MC.defic := Nat.lt_of_le_of_ne (hdC_min C MC) (Ne.symm hne)
      have hstrict : ∑ D : (Gᶜ).ConnectedComponent, dC D <
          ∑ D : (Gᶜ).ConnectedComponent,
            (Mx.restrictToClosed D.supp (fun _ _ hadj hc => (D.mem_supp_congr_adj hadj).mp hc)).defic :=
        Finset.sum_lt_sum (fun D _ => hdC_min D _) ⟨C, Finset.mem_univ C, hlt⟩
      have hsum_mx : ∑ D : (Gᶜ).ConnectedComponent,
          (Mx.restrictToClosed D.supp (fun _ _ hadj hc => (D.mem_supp_congr_adj hadj).mp hc)).defic = d := by
        calc _ = Mx.defic := by convert (Matching.defic_eq_sum_components Mx).symm
          _ = d := hMx_d
      omega
    exact ⟨MC, by convert hMC_eq, Subtype.ext hMx_fix⟩
  have hcomp_odd : ∀ C : (Gᶜ).ConnectedComponent, Odd (Fintype.card C.supp) := by
    intro C
    obtain ⟨MC, hMC⟩ := hdC_ex C
    have hev := MC.even_card_add_defic
    rw [hMC, hdC_eq_one C] at hev
    rcases hev with ⟨t, ht⟩
    exact ⟨t - 1, by omega⟩
  have hcomp_miss : ∀ (C : (Gᶜ).ConnectedComponent) (x : C.supp),
      ∃ M : Matching ((Gᶜ).induce C.supp), M.defic = 1 ∧ M.mate x = x := by
    intro C x
    obtain ⟨Mx, hMx_d, hMx_fix⟩ := hmiss x.1
    let MC := Mx.restrictToClosed C.supp (fun _ _ hadj hc => (C.mem_supp_congr_adj hadj).mp hc)
    have hMC_eq : MC.defic = 1 := by
      rw [← hdC_eq_one C]
      by_contra hne
      have hlt : dC C < MC.defic := Nat.lt_of_le_of_ne (hdC_min C MC) (Ne.symm hne)
      have hstrict : ∑ D : (Gᶜ).ConnectedComponent, dC D <
          ∑ D : (Gᶜ).ConnectedComponent,
            (Mx.restrictToClosed D.supp (fun _ _ hadj hc => (D.mem_supp_congr_adj hadj).mp hc)).defic :=
        Finset.sum_lt_sum (fun D _ => hdC_min D _) ⟨C, Finset.mem_univ C, hlt⟩
      have hsum_mx : ∑ D : (Gᶜ).ConnectedComponent,
          (Mx.restrictToClosed D.supp (fun _ _ hadj hc => (D.mem_supp_congr_adj hadj).mp hc)).defic = d := by
        calc _ = Mx.defic := by convert (Matching.defic_eq_sum_components Mx).symm
          _ = d := hMx_d
      omega
    exact ⟨MC, by convert hMC_eq, Subtype.ext hMx_fix⟩
  have hcomp_ne_three : ∀ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp ≠ 3 := by
    intro C hcard3
    have htri : Gᶜ.CliqueFree 3 := compl_cliqueFree_three hG_indep
    let S : Finset V := C.supp.toFinset
    have hS_card : S.card = 3 := by
      have h1 : S.card = Fintype.card C.supp := by
        dsimp only [S]
        rw [Set.toFinset_card]
      omega
    have hS_clique : Gᶜ.IsNClique 3 S := by
      refine ⟨?_, hS_card⟩
      intro u hu v hv huv
      simp only [S, Finset.mem_coe, Set.mem_toFinset] at hu hv
      have hsub : (S.erase u).erase v ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hcard1 : ((S.erase u).erase v).card = 1 := by
        have hv' : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, by simp [S, hv]⟩
        rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem (by simp [S, hu]), hS_card]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard1
      have hz_mem : z ∈ S := hsub (hz ▸ Finset.mem_singleton_self z)
      have hz_supp : z ∈ C.supp := by simpa [S] using hz_mem
      have hzu : z ≠ u := by
        intro heq
        have : z ∈ (S.erase u).erase v := hz ▸ Finset.mem_singleton_self z
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp this).2).1 heq
      obtain ⟨Mz, hMz_d, hMz_fix⟩ := hcomp_miss C ⟨z, hz_supp⟩
      let ux : C.supp := ⟨u, hu⟩
      let zx : C.supp := ⟨z, hz_supp⟩
      have hmate_u_ne_u : Mz.mate ux ≠ ux := by
        intro hfix
        have h2 : 2 ≤ Mz.defic := by
          have : ({ux, zx} : Finset C.supp) ⊆ Mz.fixedSet := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> rw [Mz.mem_fixedSet]
            · exact hfix
            · exact hMz_fix
          have hne_uz : ux ≠ zx := fun h => hzu (congrArg Subtype.val h).symm
          calc 2 = ({ux, zx} : Finset C.supp).card := (Finset.card_pair hne_uz).symm
            _ ≤ Mz.defic := Finset.card_le_card this
        omega
      have hmate_u_ne_z : Mz.mate ux ≠ zx := by
        intro h
        have : ux = zx := by rw [← Mz.invol ux, h, hMz_fix]
        exact hzu (congrArg Subtype.val this).symm
      have hmate_u_in : (Mz.mate ux).1 ∈ S := by simp [S]
      have hmate_u_eq : (Mz.mate ux).1 = v := by
        by_contra hne_v
        have hin : (Mz.mate ux).1 ∈ (S.erase u).erase v := by
          refine Finset.mem_erase.mpr ⟨hne_v, Finset.mem_erase.mpr ⟨?_, hmate_u_in⟩⟩
          intro h; exact hmate_u_ne_u (Subtype.ext h)
        rw [hz, Finset.mem_singleton] at hin
        exact hmate_u_ne_z (Subtype.ext hin)
      have hadj := Mz.adj_of_ne ux hmate_u_ne_u
      simpa [ux, hmate_u_eq] using hadj
    exact htri S hS_clique
  have hcard_sum : ∑ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp = n := by
    rw [← hcardV, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := (Gᶜ).connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
    · intro _ _ _ _ h; exact Subtype.ext h
    · intro v hv; exact ⟨⟨v, (Finset.mem_filter.mp hv).2⟩, Finset.mem_univ _, rfl⟩
  have hc_sum : ∑ C : (Gᶜ).ConnectedComponent, (Fintype.card C.supp + 1) / 2 = k := by
    have h2c : ∀ C : (Gᶜ).ConnectedComponent, 2 * ((Fintype.card C.supp + 1) / 2) = Fintype.card C.supp + 1 := by
      intro C
      rcases hcomp_odd C with ⟨m, hm⟩
      omega
    have h1_sum : ∑ _C : (Gᶜ).ConnectedComponent, 1 = d := by
      calc ∑ _C : (Gᶜ).ConnectedComponent, 1
          = ∑ C : (Gᶜ).ConnectedComponent, dC C :=
              Finset.sum_congr rfl fun C _ => (hdC_eq_one C).symm
        _ = d := hd_sum_eq.symm
    have hsum2 : 2 * ∑ C : (Gᶜ).ConnectedComponent, (Fintype.card C.supp + 1) / 2 = 2 * k := by
      rw [Finset.mul_sum]
      calc ∑ C : (Gᶜ).ConnectedComponent, 2 * ((Fintype.card C.supp + 1) / 2)
          = ∑ C : (Gᶜ).ConnectedComponent, (Fintype.card C.supp + 1) :=
              Finset.sum_congr rfl fun C _ => h2c C
        _ = (∑ C : (Gᶜ).ConnectedComponent, Fintype.card C.supp) + ∑ _C : (Gᶜ).ConnectedComponent, 1 :=
              Finset.sum_add_distrib
        _ = n + d := by rw [hcard_sum, h1_sum]
        _ = 2 * k := hnd_eq
    omega
  exact ⟨hcomp_odd, hcomp_miss, hcomp_ne_three, hc_sum⟩

private lemma erdos628_indep_le_two :
    ∀ (n : ℕ) {V : Type u} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n →
      G.indepNum ≤ 2 →
      ∀ (k a b : ℕ),
        G.chromaticNumber = (k : ℕ∞) →
        G.CliqueFree k →
        2 ≤ a → 2 ≤ b → a + b = k + 1 →
        ∃ (s : Set V),
          (a : ℕ∞) ≤ (G.induce s).chromaticNumber ∧
          (b : ℕ∞) ≤ (G.induce sᶜ).chromaticNumber := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro V _ G hcardV hG_indep k a b hG_chrom hG_clique ha hb hab
  have hk3 : 3 ≤ k := by omega
  have hG_col : G.Colorable k := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable, hG_chrom]
  have hG_ncol : ¬ G.Colorable (k - 1) := by
    intro hcol
    have hle := hcol.chromaticNumber_le
    rw [hG_chrom] at hle
    norm_cast at hle
    omega
  have hV_nonempty : Nonempty V := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have h0 : G.Colorable 0 := SimpleGraph.Colorable.of_isEmpty 0
    exact hG_ncol (h0.mono (Nat.zero_le _))
  by_cases hcrit : ∃ v : V, ¬ (G.induce ({v}ᶜ : Set V)).Colorable (k - 1)
  · obtain ⟨v, hnv⟩ := hcrit
    let V' := ({v}ᶜ : Set V)
    let G' := G.induce V'
    have hcard' : Fintype.card V' = n - 1 := by
      rw [card_set_compl, card_set_singleton v, hcardV]
    have hn_pos : 1 ≤ n := by rw [← hcardV]; exact Fintype.card_pos
    have hG'_col : G'.Colorable k := by
      rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
      calc G'.chromaticNumber ≤ G.chromaticNumber :=
            SimpleGraph.chromaticNumber_mono_of_hom ⟨Subtype.val, fun h => h⟩
        _ = (k : ℕ∞) := hG_chrom
    have hG'_chrom : G'.chromaticNumber = (k : ℕ∞) := by
      apply le_antisymm
      · exact hG'_col.chromaticNumber_le
      · rw [SimpleGraph.le_chromaticNumber_iff_colorable]
        intro m hm
        by_contra hlt
        exact hnv (hm.mono (by omega))
    have hG'_clique : G'.CliqueFree k := by
      rw [SimpleGraph.cliqueFree_induce_iff]
      exact hG_clique.cliqueFreeOn
    obtain ⟨s', hs'a, hs'b⟩ :=
      ih (n - 1) (by omega) G' hcard' ((indepNum_induce_le G V').trans hG_indep) k a b
        hG'_chrom hG'_clique ha hb hab
    let s : Set V := Subtype.val '' s'
    refine ⟨s, ?_, ?_⟩
    · refine hs'a.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
      exact ⟨fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩, fun h => h⟩
    · refine hs'b.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
      refine ⟨fun x => ⟨x.1.1, ?_⟩, fun h => h⟩
      rintro ⟨y, hy, hyx⟩
      exact x.2 (by rwa [← Subtype.ext hyx])
  · push Not at hcrit
    let H := Gᶜ
    have hex_d : ∃ d : ℕ, ∃ M : Matching H, M.defic = d :=
      ⟨(Matching.empty H).defic, Matching.empty H, rfl⟩
    let d := Nat.find hex_d
    obtain ⟨M₀, hM₀_d⟩ := Nat.find_spec hex_d
    have hd_min : ∀ M : Matching H, d ≤ M.defic := fun M =>
      Nat.find_min' hex_d ⟨M, rfl⟩
    have hnd_eq : n + d = 2 * k := by
      obtain ⟨Mk, hMk⟩ := (colorable_iff_exists_matching hG_indep k).mp hG_col
      have hdk : n + d ≤ 2 * k := by
        rw [← hcardV]
        exact le_trans (by have := hd_min Mk; omega) hMk
      have hnk1 : ¬ (n + d ≤ 2 * (k - 1)) := by
        intro hle
        exact hG_ncol ((colorable_iff_exists_matching hG_indep (k - 1)).mpr ⟨M₀, by omega⟩)
      have heven := M₀.even_card_add_defic
      rw [hcardV, hM₀_d] at heven
      rcases heven with ⟨t, ht⟩
      omega
    have hmiss : ∀ v : V, ∃ M : Matching H, M.defic = d ∧ M.mate v = v := by
      intro v
      obtain ⟨Mv, hMv_le⟩ :=
        (colorable_iff_exists_matching ((indepNum_induce_le G {v}ᶜ).trans hG_indep) (k - 1)).mp (hcrit v)
      have hcard_vc : Fintype.card ({v}ᶜ : Set V) = n - 1 := by
        rw [card_set_compl, card_set_singleton v, hcardV]
      rw [hcard_vc] at hMv_le
      have hMv_def : Mv.defic + 1 ≤ d := by omega
      let M_ext : Matching H :=
        { mate := fun x => if hx : x = v then v else (Mv.mate ⟨x, hx⟩).1
          invol := fun x => by
            by_cases hx : x = v
            · simp [hx]
            · simp only [hx, ↓reduceDIte]
              have hne : (Mv.mate ⟨x, hx⟩).1 ≠ v := (Mv.mate ⟨x, hx⟩).2
              simp only [hne, ↓reduceDIte]
              exact congrArg Subtype.val (Mv.invol ⟨x, hx⟩)
          adj_of_ne := fun x hne => by
            by_cases hx : x = v
            · subst hx; simp at hne
            · simp only [hx, ↓reduceDIte] at hne ⊢
              have hne' : Mv.mate ⟨x, hx⟩ ≠ ⟨x, hx⟩ := fun h =>
                hne (congrArg (Subtype.val : ({v}ᶜ : Set V) → V) h)
              rw [SimpleGraph.compl_adj]
              refine ⟨hne.symm, ?_⟩
              intro hadjG
              have hadj_ind : (G.induce ({v}ᶜ : Set V)).Adj ⟨x, hx⟩ (Mv.mate ⟨x, hx⟩) := hadjG
              have hadj_c := Mv.adj_of_ne ⟨x, hx⟩ hne'
              rw [SimpleGraph.compl_adj] at hadj_c
              exact hadj_c.2 hadj_ind }
      have hdef_ext : M_ext.defic = Mv.defic + 1 := by
        unfold Matching.defic
        have hv_in : v ∈ M_ext.fixedSet := (M_ext.mem_fixedSet v).mpr (by simp [M_ext])
        rw [← Finset.card_erase_add_one hv_in]
        congr 1
        refine Finset.card_bij (fun x hx => ⟨x, (Finset.mem_erase.mp hx).1⟩) ?_ ?_ ?_
        · intro x hx
          have hx' := Finset.mem_erase.mp hx
          have hfx := (M_ext.mem_fixedSet x).mp hx'.2
          simp only [M_ext, hx'.1, ↓reduceDIte] at hfx
          exact (Mv.mem_fixedSet _).mpr (Subtype.ext hfx)
        · intro x₁ _ x₂ _ h; exact congrArg Subtype.val h
        · intro y hy
          have hfy := (Mv.mem_fixedSet y).mp hy
          refine ⟨y.1, Finset.mem_erase.mpr ⟨y.2, (M_ext.mem_fixedSet y.1).mpr ?_⟩, rfl⟩
          have hm_eq : M_ext.mate y.1 = (Mv.mate ⟨y.1, y.2⟩).1 := dif_neg y.2
          rw [hm_eq, show (⟨y.1, y.2⟩ : ({v}ᶜ : Set V)) = y from Subtype.coe_eta y _]
          exact congrArg (Subtype.val : ({v}ᶜ : Set V) → V) hfy
      have hd_eq : M_ext.defic = d := le_antisymm (by omega) (hd_min M_ext)
      exact ⟨M_ext, hd_eq, by simp [M_ext]⟩
    obtain ⟨hcomp_odd, hcomp_miss, hcomp_ne_three, hc_sum⟩ :=
      gallai_components_summary G hG_indep k n d hcardV hnd_eq M₀ hM₀_d hd_min hmiss
    let c : H.ConnectedComponent → ℕ := fun C => (Fintype.card C.supp + 1) / 2
    have hcard_sum : ∑ C : H.ConnectedComponent, Fintype.card C.supp = n := by
      rw [← hcardV, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
        (f := H.connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro v hv; exact ⟨⟨v, (Finset.mem_filter.mp hv).2⟩, Finset.mem_univ _, rfl⟩
    by_cases hsingleton : ∃ C₀ : H.ConnectedComponent, Fintype.card C₀.supp = 1
    · obtain ⟨C₀, hC₀_card⟩ := hsingleton
      obtain ⟨v₀, hv₀⟩ := C₀.nonempty_supp
      have hv₀_univ : ∀ u : V, u ≠ v₀ → G.Adj v₀ u := by
        intro u huv
        by_contra hnot
        have hadjH : H.Adj v₀ u := by simp [H, SimpleGraph.compl_adj, huv.symm, hnot]
        have hu_mem : u ∈ C₀.supp := (C₀.mem_supp_congr_adj hadjH).mp hv₀
        have hle : ({⟨v₀, hv₀⟩, ⟨u, hu_mem⟩} : Finset C₀.supp).card ≤ Fintype.card C₀.supp :=
          Finset.card_le_univ _
        have hne_sub : (⟨v₀, hv₀⟩ : C₀.supp) ≠ ⟨u, hu_mem⟩ := fun h => huv.symm (congrArg Subtype.val h)
        rw [Finset.card_pair hne_sub, hC₀_card] at hle
        omega
      have hex_ge5 : ∃ C₁ : H.ConnectedComponent, 5 ≤ Fintype.card C₁.supp := by
        by_contra hnone
        push Not at hnone
        have hall1 : ∀ C : H.ConnectedComponent, Fintype.card C.supp = 1 := by
          intro C
          rcases hcomp_odd C with ⟨m, hm⟩
          have hne3 := hcomp_ne_three C
          have hlt := hnone C
          omega
        have hk_eq_n : k = n := by
          have hc1 : ∀ C : H.ConnectedComponent, c C = 1 := fun C => by
            dsimp only [c]; rw [hall1 C]
          have hsum_1 : ∑ C : H.ConnectedComponent, Fintype.card C.supp = ∑ _C : H.ConnectedComponent, 1 :=
            Finset.sum_congr rfl fun C _ => hall1 C
          rw [← hc_sum, Finset.sum_congr rfl (fun C _ => hc1 C), ← hsum_1, hcard_sum]
        have hH_bot : H = ⊥ := by
          ext u w
          simp only [SimpleGraph.bot_adj, iff_false]
          intro hadj
          let Cu := H.connectedComponentMk u
          have hw_mem : w ∈ Cu.supp := (Cu.mem_supp_congr_adj hadj).mp rfl
          have hne_uw : (⟨u, rfl⟩ : Cu.supp) ≠ ⟨w, hw_mem⟩ := fun h => hadj.ne (congrArg Subtype.val h)
          have hle : ({⟨u, rfl⟩, ⟨w, hw_mem⟩} : Finset Cu.supp).card ≤ Fintype.card Cu.supp :=
            Finset.card_le_univ _
          rw [Finset.card_pair hne_uw, hall1 Cu] at hle
          omega
        have hG_top : G.IsNClique k Finset.univ := by
          refine ⟨?_, by rw [Finset.card_univ, hcardV, hk_eq_n]⟩
          intro u _ w _ huw
          by_contra hnot
          have hadjH : H.Adj u w := by simp [H, SimpleGraph.compl_adj, huw, hnot]
          rw [hH_bot] at hadjH
          exact hadjH
        exact hG_clique Finset.univ hG_top
      obtain ⟨C₁, hC₁_ge5⟩ := hex_ge5
      have hC₀_ne_C₁ : C₀ ≠ C₁ := fun h => by rw [← h, hC₀_card] at hC₁_ge5; omega
      have hk4 : 4 ≤ k := by
        have hc₀ : c C₀ = 1 := by dsimp only [c]; rw [hC₀_card]
        have hc₁ : 3 ≤ c C₁ := by dsimp [c]; omega
        have hle : c C₀ + c C₁ ≤ ∑ C : H.ConnectedComponent, c C :=
          Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ C₀) (Finset.mem_univ C₁) hC₀_ne_C₁
        have hsum_k : ∑ C : H.ConnectedComponent, c C = k := by convert hc_sum
        omega
      let V' := ({v₀}ᶜ : Set V)
      let G' := G.induce V'
      have hcard' : Fintype.card V' = n - 1 := by
        rw [card_set_compl, card_set_singleton v₀, hcardV]
      have hn_pos : 1 ≤ n := by rw [← hcardV]; exact Fintype.card_pos
      have hG'_col : G'.Colorable (k - 1) := hcrit v₀
      have hG'_ncol : ¬ G'.Colorable (k - 2) := by
        rintro ⟨C'⟩
        apply hG_ncol
        refine ⟨⟨fun u => if hu : u = v₀ then ⟨k - 2, by omega⟩ else ⟨(C' ⟨u, hu⟩).1, by omega⟩, ?_⟩⟩
        intro u w hadj heq
        by_cases hu : u = v₀ <;> by_cases hw : w = v₀
        · subst hu hw; exact hadj.ne rfl
        · rw [dif_pos hu, dif_neg hw] at heq
          have hlt := (C' ⟨w, hw⟩).isLt
          have hval := congrArg Fin.val heq
          dsimp only at hval
          omega
        · rw [dif_neg hu, dif_pos hw] at heq
          have hlt := (C' ⟨u, hu⟩).isLt
          have hval := congrArg Fin.val heq
          dsimp only at hval
          omega
        · rw [dif_neg hu, dif_neg hw] at heq
          have hval : C' ⟨u, hu⟩ = C' ⟨w, hw⟩ :=
            Fin.ext (congrArg (Fin.val : Fin (k - 1) → ℕ) heq)
          exact C'.valid (show G'.Adj ⟨u, hu⟩ ⟨w, hw⟩ from hadj) hval
      have hG'_chrom : G'.chromaticNumber = ((k - 1 : ℕ) : ℕ∞) := by
        apply le_antisymm
        · exact hG'_col.chromaticNumber_le
        · rw [SimpleGraph.le_chromaticNumber_iff_colorable]
          intro m hm
          by_contra hlt
          exact hG'_ncol (hm.mono (by omega))
      have hG'_clique : G'.CliqueFree (k - 1) := by
        intro t ht
        let t' : Finset V := insert v₀ (t.map ⟨Subtype.val, Subtype.val_injective⟩)
        have hv₀_not : v₀ ∉ t.map ⟨Subtype.val, Subtype.val_injective⟩ := by
          by_contra hmem
          obtain ⟨⟨x, hx⟩, _, hxeq⟩ := Finset.mem_map.mp hmem
          exact hx hxeq
        have ht'_card : t'.card = k := by
          rw [Finset.card_insert_of_notMem hv₀_not, Finset.card_map, ht.2]
          omega
        have ht'_clique : G.IsNClique k t' := by
          refine ⟨?_, ht'_card⟩
          intro x hx y hy hxy
          simp only [t', Finset.coe_insert, Set.mem_insert_iff, Finset.coe_map,
            Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe, Subtype.exists] at hx hy
          rcases hx with rfl | ⟨a, ha, hat, rfl⟩ <;> rcases hy with rfl | ⟨b, hb, hbt, rfl⟩
          · exact (hxy rfl).elim
          · exact hv₀_univ b hxy.symm
          · exact (hv₀_univ a hxy).symm
          · exact ht.1 hat hbt (fun h => hxy (congrArg (Subtype.val : V' → V) h))
        exact hG_clique t' ht'_clique
      have hcases : 3 ≤ a ∨ 3 ≤ b := by omega
      rcases hcases with ha3 | hb3
      · obtain ⟨s', hs'a, hs'b⟩ :=
          ih (n - 1) (by omega) G' hcard' ((indepNum_induce_le G V').trans hG_indep) (k - 1) (a - 1) b
            hG'_chrom hG'_clique (by omega) hb (by omega)
        let s : Set V := insert v₀ (Subtype.val '' s')
        refine ⟨s, ?_, ?_⟩
        · have hsub_s : ((a - 1 : ℕ) : ℕ∞) ≤ (G.induce (s \ {v₀} : Set V)).chromaticNumber := by
            refine hs'a.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
            refine ⟨fun x => ⟨x.1.1, ?_⟩, fun h => h⟩
            exact ⟨Or.inr ⟨x.1, x.2, rfl⟩, x.1.2⟩
          have hboost := chromaticNumber_boost_universal G s v₀ (Set.mem_insert v₀ _) hv₀_univ (a - 1) hsub_s
          rwa [show (a - 1 + 1 : ℕ) = a by omega] at hboost
        · refine hs'b.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
          refine ⟨fun x => ⟨x.1.1, ?_⟩, fun h => h⟩
          rintro (heq | ⟨y, hy, hyx⟩)
          · exact x.1.2 heq
          · exact x.2 (by rwa [← Subtype.ext hyx])
      · obtain ⟨s', hs'a, hs'b⟩ :=
          ih (n - 1) (by omega) G' hcard' ((indepNum_induce_le G V').trans hG_indep) (k - 1) a (b - 1)
            hG'_chrom hG'_clique ha (by omega) (by omega)
        let s : Set V := Subtype.val '' s'
        refine ⟨s, ?_, ?_⟩
        · refine hs'a.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
          exact ⟨fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩, fun h => h⟩
        · have hv₀_sc : v₀ ∈ sᶜ := by
            rintro ⟨y, _, hy⟩; exact y.2 hy
          have hsub_sc : ((b - 1 : ℕ) : ℕ∞) ≤ (G.induce (sᶜ \ {v₀} : Set V)).chromaticNumber := by
            refine hs'b.trans (SimpleGraph.chromaticNumber_mono_of_hom ?_)
            refine ⟨fun x => ⟨x.1.1, ?_, x.1.2⟩, fun h => h⟩
            rintro ⟨y, hy, hyx⟩; exact x.2 (by rwa [← Subtype.ext hyx])
          have hboost := chromaticNumber_boost_universal G sᶜ v₀ hv₀_sc hv₀_univ (b - 1) hsub_sc
          rwa [show (b - 1 + 1 : ℕ) = b by omega] at hboost
    · push Not at hsingleton
      exact erdos628_no_singleton_components G hG_indep k a b ha hb hab
        hcomp_odd hcomp_ne_three hsingleton hc_sum

end Erdos628Proof

theorem OMA.solution : type_of% @Erdos628.erdos_628.variants.independence_number_2 := by
  intro V _ G _ hG_indep k hG_chrom hG_clique a b ha hb hab
  exact Erdos628Proof.erdos628_indep_le_two (Fintype.card V) G rfl hG_indep.le k a b
    hG_chrom hG_clique ha hb hab
