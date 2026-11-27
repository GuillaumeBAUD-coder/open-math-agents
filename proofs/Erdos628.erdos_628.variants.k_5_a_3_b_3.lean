import FormalConjectures.ErdosProblems.«628»

-- Problem: Erdős Problem 628 — k 5 a 3 b 3
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/628.lean:61 (declaration Erdos628.erdos_628.variants.k_5_a_3_b_3)
-- Credit: @divo12 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos628K5

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `s` admits a proper 2-colouring, phrased on the ambient vertex type. -/
def TwoCol (s : Set V) : Prop :=
  ∃ f : V → Fin 2, ∀ a b, a ∈ s → b ∈ s → G.Adj a b → f a ≠ f b

/-- `S` is an independent set. -/
def Ind (S : Set V) : Prop := ∀ a b, a ∈ S → b ∈ S → ¬ G.Adj a b

lemma twoCol_of_colorable {s : Set V} (h : (G.induce s).Colorable 2) : TwoCol G s := by
  classical
  obtain ⟨C⟩ := h
  refine ⟨fun a => if ha : a ∈ s then C ⟨a, ha⟩ else 0, ?_⟩
  intro a b ha hb hab
  simp only [dif_pos ha, dif_pos hb]
  exact C.valid (by simpa using hab)

lemma three_le_of_not_colorable {W : Type*} (H : SimpleGraph W) (h : ¬ H.Colorable 2) :
    (3 : ℕ∞) ≤ H.chromaticNumber := by
  by_contra hc
  apply h
  rw [← chromaticNumber_le_iff_colorable]
  exact Order.le_of_lt_add_one (not_le.mp hc)

lemma fin2_tri (p q r : Fin 2) (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r) : False := by
  revert p q r; decide

lemma fin2_cases (p : Fin 2) : p = 0 ∨ p = 1 := by
  revert p; decide

lemma cover4 (S0 S1 S2 S3 : Set V) (h0 : Ind G S0) (h1 : Ind G S1) (h2 : Ind G S2)
    (h3 : Ind G S3) (hc : ∀ a, a ∈ S0 ∨ a ∈ S1 ∨ a ∈ S2 ∨ a ∈ S3) : G.Colorable 4 := by
  let S : Fin 4 → Set V := ![S0, S1, S2, S3]
  have hS : ∀ i, Ind G (S i) := by
    intro i; fin_cases i <;> assumption
  have hcov : ∀ a, ∃ i, a ∈ S i := by
    intro a
    rcases hc a with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  refine ⟨Coloring.mk (fun a => Classical.choose (hcov a)) ?_⟩
  intro a b hab heq
  exact hS _ a b (Classical.choose_spec (hcov a)) (heq ▸ Classical.choose_spec (hcov b)) hab

lemma tri_not {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) {s : Set V}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : ¬ TwoCol G s := by
  rintro ⟨f, hf⟩
  exact fin2_tri _ _ _ (hf a b ha hb hab) (hf b c hb hc hbc) (hf a c ha hc hac)

/-- Lemma T: complete vertices of a triangle. -/
lemma complete_vertex (h4 : ¬ G.Colorable 4) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : G.Adj a c) (f : V → Fin 2)
    (hf : ∀ x y, x ∈ ({a, b, c} : Set V)ᶜ → y ∈ ({a, b, c} : Set V)ᶜ → G.Adj x y → f x ≠ f y)
    (i : Fin 2) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ f x = i ∧ G.Adj x a ∧ G.Adj x b ∧ G.Adj x c := by
  by_contra hne
  set T : Set V := {a, b, c} with hT
  have hmem : ∀ x, x ∉ T ↔ x ≠ a ∧ x ≠ b ∧ x ≠ c := by
    intro x; simp [hT]
  have key : ∀ t, Ind G {x | x = t ∨ (x ∉ T ∧ f x = i ∧ ¬ G.Adj x t)} := by
    rintro t x y (rfl | ⟨hx, hfx, hxt⟩) (rfl | ⟨hy, hfy, hyt⟩) hxy
    · exact hxy.ne rfl
    · exact hyt hxy.symm
    · exact hxt hxy
    · exact hf x y hx hy hxy (hfx.trans hfy.symm)
  apply h4
  refine cover4 G _ _ _ {x | x ∉ T ∧ f x ≠ i} (key a) (key b) (key c) ?_ ?_
  · rintro x y ⟨hx, hfx⟩ ⟨hy, hfy⟩ hxy
    have h1 := hf x y hx hy hxy
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases (f x) with h | h <;>
      rcases fin2_cases (f y) with h' | h' <;> simp_all
  · intro x
    by_cases hx : x ∈ T
    · rw [hT] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inl (Or.inl rfl)))
    · by_cases hfx : f x = i
      · obtain ⟨hxa, hxb, hxc⟩ := (hmem x).1 hx
        by_cases ha : G.Adj x a
        · by_cases hb : G.Adj x b
          · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hx, hfx, fun hc =>
              hne ⟨x, hxa, hxb, hxc, hfx, ha, hb, hc⟩⟩)))
          · exact Or.inr (Or.inl (Or.inr ⟨hx, hfx, hb⟩))
        · exact Or.inl (Or.inr ⟨hx, hfx, ha⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hx, hfx⟩))

lemma complete2 (h4 : ¬ G.Colorable 4) (H : ∀ s : Set V, TwoCol G s ∨ TwoCol G sᶜ)
    {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    ∃ x y, x ≠ y ∧ (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ G.Adj x a ∧ G.Adj x b ∧ G.Adj x c) ∧
      (y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ G.Adj y a ∧ G.Adj y b ∧ G.Adj y c) := by
  rcases H {a, b, c} with h | ⟨f, hf⟩
  · exact (tri_not G hab hbc hac (by simp) (by simp) (by simp) h).elim
  · obtain ⟨x, hx⟩ := complete_vertex G h4 hab hbc hac f hf 0
    obtain ⟨y, hy⟩ := complete_vertex G h4 hab hbc hac f hf 1
    refine ⟨x, y, ?_, ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2⟩, ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.2⟩⟩
    rintro rfl
    have := hx.2.2.2.1.symm.trans hy.2.2.2.1
    exact absurd this (by decide)

lemma five_clique [DecidableEq V] {a b c d e : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (had : G.Adj a d) (hae : G.Adj a e) (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hcd : G.Adj c d) (hce : G.Adj c e) (hde : G.Adj d e) : ¬ G.CliqueFree 5 := by
  intro h
  have h3 : G.IsNClique 3 {c, d, e} := is3Clique_triple_iff.mpr ⟨hcd, hce, hde⟩
  have h4 : G.IsNClique 4 (insert b {c, d, e}) :=
    h3.insert (by simp [hbc, hbd, hbe])
  have h5 : G.IsNClique 5 (insert a (insert b {c, d, e})) :=
    h4.insert (by simp [hab, hac, had, hae])
  exact h _ h5

lemma caseA (h4 : ¬ G.Colorable 4) (h5 : G.CliqueFree 5)
    (H : ∀ s : Set V, TwoCol G s ∨ TwoCol G sᶜ) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : G.Adj a c) : False := by
  classical
  obtain ⟨d, -, -, ⟨hda', hdb', hdc', hda, hdb, hdc⟩, -⟩ := complete2 G h4 H hab hbc hac
  -- a complete vertex `e ≠ a` of the triangle `{b, c, d}`
  have hE : ∃ e, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ G.Adj e b ∧ G.Adj e c ∧ G.Adj e d := by
    obtain ⟨x, y, hxy, ⟨hxb', hxc', hxd', hxb, hxc, hxd⟩, ⟨hyb', hyc', hyd', hyb, hyc, hyd⟩⟩ :=
      complete2 G h4 H hbc hdc.symm hdb.symm
    by_cases hxa : x = a
    · exact ⟨y, fun h => hxy (hxa.trans h.symm), hyb', hyc', hyd', hyb, hyc, hyd⟩
    · exact ⟨x, hxa, hxb', hxc', hxd', hxb, hxc, hxd⟩
  obtain ⟨e, hea', heb', hec', hed', heb, hec, hed⟩ := hE
  obtain ⟨g0, g1, hg, ⟨hg0c', hg0d', hg0e', hg0c, hg0d, hg0e⟩,
      ⟨hg1c', hg1d', hg1e', hg1c, hg1d, hg1e⟩⟩ :=
    complete2 G h4 H hdc.symm hed.symm hec.symm
  -- if some `g` avoids `{a, b}`, then `{d, e, g}` is a triangle disjoint from `{a, b, c}`
  have hdisj : ∀ g, g ≠ a → g ≠ b → g ≠ c → G.Adj g d → G.Adj g e → False := by
    intro g hga hgb hgc hgd hge
    rcases H {a, b, c} with h | h
    · exact tri_not G hab hbc hac (by simp) (by simp) (by simp) h
    · refine tri_not G hed.symm hge.symm hgd.symm ?_ ?_ ?_ h <;> simp [*]
  have h0 : g0 = a ∨ g0 = b := by
    by_contra hc
    push Not at hc
    exact hdisj g0 hc.1 hc.2 hg0c' hg0d hg0e
  have h1 : g1 = a ∨ g1 = b := by
    by_contra hc
    push Not at hc
    exact hdisj g1 hc.1 hc.2 hg1c' hg1d hg1e
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl
  · exact hg rfl
  · exact five_clique G hab hg0c hg0d hg0e hbc hdb.symm heb.symm hdc.symm hec.symm hed.symm h5
  · exact five_clique G hab hac hda.symm hg1e hg0c hg0d hg0e hdc.symm hec.symm hed.symm h5
  · exact hg rfl

lemma layer_edge (h4 : ¬ G.Colorable 4) :
    ∃ v y w, G.Adj y w ∧ G.Reachable v y ∧ G.dist v y = G.dist v w := by
  by_contra hne
  apply h4
  let r : V → V := fun u => Quot.out (G.connectedComponentMk u)
  have hr : ∀ u, G.Reachable (r u) u := fun u =>
    ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk u))
  have hrr : ∀ u w, G.Adj u w → r u = r w := by
    intro u w h
    simp only [r, ConnectedComponent.connectedComponentMk_eq_of_adj h]
  refine ⟨Coloring.mk (fun u => (⟨G.dist (r u) u % 2, by omega⟩ : Fin 4)) ?_⟩
  intro u w h heq
  have hv := congrArg Fin.val heq
  simp only at hv
  rw [hrr u w h] at hv
  have h1 := h.diff_dist_adj (u := r w)
  have h2 : G.dist (r w) u ≠ G.dist (r w) w := fun he =>
    hne ⟨r w, u, w, h, hrr u w h ▸ hr u, he⟩
  omega

lemma pred {v u : V} (hr : G.Reachable v u) {i : ℕ} (hd : G.dist v u = i + 1) :
    ∃ u', G.Adj u' u ∧ G.Reachable v u' ∧ G.dist v u' = i := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  cases hq : p.reverse with
  | nil =>
    have := congrArg Walk.length hq
    simp only [Walk.length_reverse, Walk.length_nil] at this
    omega
  | cons hadj q =>
    have hl := congrArg Walk.length hq
    simp only [Walk.length_reverse, Walk.length_cons] at hl
    refine ⟨_, hadj.symm, ⟨q.reverse⟩, ?_⟩
    have h1 := dist_le q.reverse
    have h2 := hadj.symm.diff_dist_adj (u := v)
    rw [Walk.length_reverse] at h1
    omega

lemma caseB (h4 : ¬ G.Colorable 4) (h3 : G.CliqueFree 3)
    (H : ∀ s : Set V, TwoCol G s ∨ TwoCol G sᶜ) : False := by
  classical
  obtain ⟨v0, y0, w0, hyw0, hr0, hd0⟩ := layer_edge G h4
  have hex : ∃ k, ∃ v y w, G.Adj y w ∧ G.Reachable v y ∧ G.dist v y = k ∧ G.dist v w = k :=
    ⟨_, v0, y0, w0, hyw0, hr0, rfl, hd0.symm⟩
  obtain ⟨v, y, w, hyw, hvy, hdy, hdw⟩ := Nat.find_spec hex
  have hmin : ∀ u u', G.Adj u u' → G.Reachable v u → G.dist v u = G.dist v u' →
      Nat.find hex ≤ G.dist v u :=
    fun u u' h hr hd => Nat.find_min' hex ⟨v, u, u', h, hr, rfl, hd.symm⟩
  generalize Nat.find hex = k at hdy hdw hmin
  have hvw : G.Reachable v w := hvy.trans hyw.reachable
  have hk : 1 ≤ k := by
    by_contra hk0
    have e1 : v = y := hvy.dist_eq_zero_iff.mp (by omega)
    have e2 : v = w := hvw.dist_eq_zero_iff.mp (by omega)
    exact hyw.ne (e1.symm.trans e2)
  have hadj : ∀ u u', G.Adj u u' → G.dist v u' ≤ G.dist v u + 1 := by
    intro u u' h
    have := h.diff_dist_adj (u := v)
    omega
  set B : Set V := {u | G.Reachable v u ∧ G.dist v u < k} with hB
  set Y : Set V := {u | u ∈ B ∨ u = y ∨ G.Adj y u} with hY
  have hBpar : ∀ u u', u ∈ B → u' ∈ B → G.Adj u u' →
      G.dist v u % 2 = G.dist v u' % 2 → False := by
    rintro u u' ⟨hu, hdu⟩ ⟨hu', hdu'⟩ h hp
    have h1 := hadj u u' h
    have h2 := hadj u' u h.symm
    have := hmin u u' h hu (by omega)
    omega
  rcases H Y with ⟨f, hf⟩ | ⟨f, hf⟩
  · -- `G[Y]` is not 2-colourable: parity along BFS layers
    have hind : ∀ i, i < k → ∀ u, G.Reachable v u → G.dist v u = i →
        (f u).val = ((f v).val + i) % 2 := by
      intro i
      induction i with
      | zero =>
        intro _ u hu hd
        obtain rfl := hu.dist_eq_zero_iff.mp hd
        have := (f v).isLt
        omega
      | succ i ih =>
        intro hi u hu hd
        obtain ⟨u', hu'u, hru', hdu'⟩ := pred G hu hd
        have e := ih (by omega) u' hru' hdu'
        have hne := hf u' u (Or.inl ⟨hru', by omega⟩) (Or.inl ⟨hu, by omega⟩) hu'u
        have hne' : (f u').val ≠ (f u).val := fun h => hne (Fin.ext h)
        have := (f u).isLt
        have := (f u').isLt
        omega
    obtain ⟨y', hy'y, hry', hdy'⟩ := pred G hvy (i := k - 1) (by omega)
    obtain ⟨w', hw'w, hrw', hdw'⟩ := pred G hvw (i := k - 1) (by omega)
    have ey := hind (k - 1) (by omega) y' hry' hdy'
    have ew := hind (k - 1) (by omega) w' hrw' hdw'
    have hyY : y ∈ Y := Or.inr (Or.inl rfl)
    have hwY : w ∈ Y := Or.inr (Or.inr hyw)
    have n1 := hf y' y (Or.inl ⟨hry', by omega⟩) hyY hy'y
    have n2 := hf w' w (Or.inl ⟨hrw', by omega⟩) hwY hw'w
    have n3 := hf y w hyY hwY hyw
    have n1' : (f y').val ≠ (f y).val := fun h => n1 (Fin.ext h)
    have n2' : (f w').val ≠ (f w).val := fun h => n2 (Fin.ext h)
    have n3' : (f y).val ≠ (f w).val := fun h => n3 (Fin.ext h)
    have := (f y).isLt
    have := (f w).isLt
    have := (f y').isLt
    have := (f w').isLt
    omega
  · -- `G[Yᶜ]` is not 2-colourable: otherwise `G` is 4-colourable
    have hBnbr : ∀ u x, u ∈ B → G.dist v u % 2 = k % 2 → G.Adj u x → x ∈ B := by
      rintro u x ⟨hu, hdu⟩ hp h
      have := hadj u x h
      exact ⟨hu.trans h.reachable, by omega⟩
    have hyY : ∀ x, G.Adj y x → x ∈ Y := fun x h => Or.inr (Or.inr h)
    have hBy : ∀ u, u ∈ B → G.dist v u % 2 = k % 2 → ¬ G.Adj u y := by
      rintro u ⟨hu, hdu⟩ hp h
      have := hadj u y h
      omega
    apply h4
    refine cover4 G {u | (u ∉ Y ∧ f u = 0) ∨ (u ∈ B ∧ G.dist v u % 2 = k % 2) ∨ u = y}
      {u | u ∉ Y ∧ f u = 1} {u | u ∈ B ∧ G.dist v u % 2 ≠ k % 2} {u | G.Adj y u ∧ u ∉ B}
      ?_ ?_ ?_ ?_ ?_
    · rintro a b (⟨ha, hfa⟩ | ⟨ha, hpa⟩ | ha) (⟨hb, hfb⟩ | ⟨hb, hpb⟩ | hb) hab
      · exact hf a b ha hb hab (hfa.trans hfb.symm)
      · exact ha (Or.inl (hBnbr b a hb hpb hab.symm))
      · rw [hb] at hab
        exact ha (hyY a hab.symm)
      · exact hb (Or.inl (hBnbr a b ha hpa hab))
      · exact hBpar a b ha hb hab (by omega)
      · rw [hb] at hab
        exact hBy a ha hpa hab
      · rw [ha] at hab
        exact hb (hyY b hab)
      · rw [ha] at hab
        exact hBy b hb hpb hab.symm
      · rw [ha, hb] at hab
        exact hab.ne rfl
    · rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩ hab
      exact hf a b ha hb hab (hfa.trans hfb.symm)
    · rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩ hab
      exact hBpar a b ha hb hab (by omega)
    · rintro a b ⟨ha, -⟩ ⟨hb, -⟩ hab
      exact h3 {y, a, b} (is3Clique_triple_iff.mpr ⟨ha, hb, hab⟩)
    · intro u
      by_cases hu : u ∈ Y
      · by_cases hb : u ∈ B
        · by_cases hp : G.dist v u % 2 = k % 2
          · exact Or.inl (Or.inr (Or.inl ⟨hb, hp⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hb, hp⟩))
        · rcases hu with hu | hu | hu
          · exact (hb hu).elim
          · exact Or.inl (Or.inr (Or.inr hu))
          · exact Or.inr (Or.inr (Or.inr ⟨hu, hb⟩))
      · rcases fin2_cases (f u) with h | h
        · exact Or.inl (Or.inl ⟨hu, h⟩)
        · exact Or.inr (Or.inl ⟨hu, h⟩)

lemma main (h4 : ¬ G.Colorable 4) (h5 : G.CliqueFree 5)
    (H : ∀ s : Set V, TwoCol G s ∨ TwoCol G sᶜ) : False := by
  classical
  by_cases h3 : G.CliqueFree 3
  · exact caseB G h4 h3 H
  · rw [CliqueFree] at h3
    push Not at h3
    obtain ⟨t, ht⟩ := h3
    rw [is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
    exact caseA G h4 h5 H hab hbc hac

end OMA.Erdos628K5

theorem OMA.solution : type_of% @Erdos628.erdos_628.variants.k_5_a_3_b_3 := by
  classical
  intro V _ G _ hχ hcf
  have h4 : ¬ G.Colorable 4 := by
    intro h
    have := h.chromaticNumber_le
    rw [hχ] at this
    exact absurd this (by decide)
  by_contra hne
  apply OMA.Erdos628K5.main G h4 hcf
  intro s
  by_cases h1 : (G.induce s).Colorable 2
  · exact Or.inl (OMA.Erdos628K5.twoCol_of_colorable G h1)
  · by_cases h2 : (G.induce sᶜ).Colorable 2
    · exact Or.inr (OMA.Erdos628K5.twoCol_of_colorable G h2)
    · exact (hne ⟨s, OMA.Erdos628K5.three_le_of_not_colorable _ h1,
        OMA.Erdos628K5.three_le_of_not_colorable _ h2⟩).elim
