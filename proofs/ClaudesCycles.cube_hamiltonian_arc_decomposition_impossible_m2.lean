import FormalConjectures.Paper.ClaudesCycles

/-!
# Impossibility of a Hamiltonian Arc Decomposition of the 3-Cube Digraph

We prove `¬ HasHamiltonianArcDecomposition 2` (Aubert–Schneider 1982).
Given three arc-disjoint directed Hamiltonian cycles on `(ZMod 2)³`, no cycle can traverse both
directions of an undirected edge (else it would contain a 2-cycle). Hence each undirected edge
misses a unique cycle, yielding a proper 3-edge-coloring `g` of the 3-cube. Any bichromatic
4-cycle face would force all four edges leaving that face to share the third color, trapping the
corresponding cycle inside the face. Finally, a direct case check shows that no proper
3-edge-coloring of the 3-cube avoids bichromatic faces.
-/

-- Problem: Claude's Cycles — cube hamiltonian arc decomposition impossible m2
-- Upstream: formal-conjectures FormalConjectures/Paper/ClaudesCycles.lean:129 (declaration ClaudesCycles.cube_hamiltonian_arc_decomposition_impossible_m2)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace ClaudesCyclesM2Proof

open ClaudesCycles

private lemma zmod2_add_one_add_one (x : ZMod 2) : x + 1 + 1 = x := by
  revert x
  decide

private lemma zmod2_add_one_ne (x : ZMod 2) : x + 1 ≠ x := by
  revert x
  decide

private lemma zmod2_eq_or_eq_add_one (x y : ZMod 2) : x = y ∨ x = y + 1 := by
  revert x y
  decide

private lemma bumpAt_invol (b : Fin 3) (v : Vertex 2) :
    bumpAt b (bumpAt b v) = v := by
  funext i
  by_cases h : i = b
  · subst h
    rw [bumpAt_apply_self, bumpAt_apply_self, zmod2_add_one_add_one]
  · rw [bumpAt_apply_of_ne (Ne.symm h), bumpAt_apply_of_ne (Ne.symm h)]

private lemma bumpAt_comm (a b : Fin 3) (v : Vertex 2) :
    bumpAt a (bumpAt b v) = bumpAt b (bumpAt a v) := by
  funext i
  by_cases ha : i = a
  · subst ha
    by_cases hb : i = b
    · subst hb; rfl
    · rw [bumpAt_apply_self, bumpAt_apply_of_ne (Ne.symm hb),
        bumpAt_apply_of_ne (Ne.symm hb), bumpAt_apply_self]
  · by_cases hb : i = b
    · subst hb
      rw [bumpAt_apply_of_ne (Ne.symm ha), bumpAt_apply_self,
        bumpAt_apply_self, bumpAt_apply_of_ne (Ne.symm ha)]
    · rw [bumpAt_apply_of_ne (Ne.symm ha), bumpAt_apply_of_ne (Ne.symm hb),
        bumpAt_apply_of_ne (Ne.symm hb), bumpAt_apply_of_ne (Ne.symm ha)]

private lemma bumpAt_ne_self (b : Fin 3) (v : Vertex 2) :
    bumpAt b v ≠ v := by
  intro h
  have hb := congrFun h b
  rw [bumpAt_apply_self] at hb
  exact zmod2_add_one_ne (v b) hb

private def third : Fin 3 → Fin 3 → Fin 3
  | 0, 1 => 2
  | 1, 0 => 2
  | 0, 2 => 1
  | 2, 0 => 1
  | 1, 2 => 0
  | 2, 1 => 0
  | a, _ => a

private lemma third_comm (a b : Fin 3) : third a b = third b a := by
  revert a b
  decide

private lemma third_ne_left {a b : Fin 3} (h : a ≠ b) : third a b ≠ a := by
  revert a b h
  decide

private lemma third_ne_right {a b : Fin 3} (h : a ≠ b) : third a b ≠ b := by
  revert a b h
  decide

private lemma eq_third_of_ne {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    c = third a b := by
  revert a b c hab hca hcb
  decide

private lemma fin3_mem_triple {a b : Fin 3} (hab : a ≠ b) (i : Fin 3) :
    i = a ∨ i = b ∨ i = third a b := by
  revert a b hab i
  decide

private lemma fin3_disjoint_pairs {x₀ x₁ y₀ y₁ : Fin 3}
    (h00 : x₀ ≠ y₀) (h01 : x₀ ≠ y₁) (h10 : x₁ ≠ y₀) (h11 : x₁ ≠ y₁) :
    x₀ = x₁ ∨ y₀ = y₁ := by
  revert x₀ x₁ y₀ y₁ h00 h01 h10 h11
  decide

private lemma perm_zpow_invariant {α : Type*} (σ : Equiv.Perm α) (P : α → Prop)
    (hstep : ∀ x, P x → P (σ x)) (hinv : ∀ x, P x → P (σ⁻¹ x))
    {x : α} (hx : P x) (k : ℤ) : P ((σ ^ k) x) := by
  induction k using Int.induction_on with
  | zero => simpa using hx
  | succ n ih =>
    have hpow : σ ^ ((n : ℤ) + 1) = σ * σ ^ (n : ℤ) := by
      rw [add_comm, zpow_add, zpow_one]
    rw [hpow, Equiv.Perm.mul_apply]
    exact hstep _ ih
  | pred n ih =>
    have hpow : σ ^ (-(n : ℤ) - 1) = σ⁻¹ * σ ^ (-(n : ℤ)) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
    rw [hpow, Equiv.Perm.mul_apply]
    exact hinv _ ih

private lemma no_edge_coloring_without_bichromatic_face
    (g : Vertex 2 → Fin 3 → Fin 3)
    (hsym : ∀ v b, g (bumpAt b v) b = g v b)
    (hinj : ∀ v, Function.Injective (g v))
    (hface : ∀ v a b, a ≠ b → ¬ (g v a = g (bumpAt b v) a ∧ g v b = g (bumpAt a v) b)) :
    False := by
  have face_contra : ∀ (v : Vertex 2) (a b : Fin 3), a ≠ b →
      g v a = g (bumpAt b v) a → False := by
    intro v a b hab heq
    let d : Fin 3 := third a b
    have hda : d ≠ a := third_ne_left hab
    have hdb : d ≠ b := third_ne_right hab
    let c₀ : Fin 3 := g v a
    let c₁ : Fin 3 := g v b
    let c₂ : Fin 3 := g (bumpAt a v) b
    have hc01 : c₀ ≠ c₁ := fun h => hab (hinj v h)
    have hc02 : c₀ ≠ c₂ := by
      intro h
      have h' : g (bumpAt a v) a = g (bumpAt a v) b := by
        rw [hsym]; exact h
      exact hab (hinj (bumpAt a v) h')
    have hc12 : c₁ ≠ c₂ := fun h => hface v a b hab ⟨heq, h⟩
    have hc0 : c₀ = third c₁ c₂ := eq_third_of_ne hc12 hc01 hc02
    have hc1 : c₁ = third c₀ c₂ := eq_third_of_ne hc02 hc01.symm hc12
    have hc2 : c₂ = third c₀ c₁ := eq_third_of_ne hc01 hc02.symm hc12.symm
    have h_v_d : g v d = c₂ := by
      rw [hc2]
      exact eq_third_of_ne hc01 (fun h => hda (hinj v h)) (fun h => hdb (hinj v h))
    have h_vb_d : g (bumpAt b v) d = c₂ := by
      rw [hc2]
      refine eq_third_of_ne hc01 ?_ ?_
      · intro h
        have h' : g (bumpAt b v) d = g (bumpAt b v) a := h.trans heq
        exact hda (hinj (bumpAt b v) h')
      · intro h
        have h' : g (bumpAt b v) d = g (bumpAt b v) b := h.trans (hsym v b).symm
        exact hdb (hinj (bumpAt b v) h')
    have h_va_d : g (bumpAt a v) d = c₁ := by
      rw [hc1]
      refine eq_third_of_ne hc02 ?_ ?_
      · intro h
        have h' : g (bumpAt a v) d = g (bumpAt a v) a := h.trans (hsym v a).symm
        exact hda (hinj (bumpAt a v) h')
      · intro h
        exact hdb (hinj (bumpAt a v) h)
    have h_vba_d : g (bumpAt b (bumpAt a v)) d = c₁ := by
      rw [hc1]
      refine eq_third_of_ne hc02 ?_ ?_
      · intro h
        have h' : g (bumpAt b (bumpAt a v)) d = g (bumpAt b (bumpAt a v)) a := by
          calc g (bumpAt b (bumpAt a v)) d
              = g (bumpAt b v) a := h.trans heq
            _ = g (bumpAt a (bumpAt b v)) a := (hsym (bumpAt b v) a).symm
            _ = g (bumpAt b (bumpAt a v)) a := by rw [bumpAt_comm a b v]
        exact hda (hinj (bumpAt b (bumpAt a v)) h')
      · intro h
        have h' : g (bumpAt b (bumpAt a v)) d = g (bumpAt b (bumpAt a v)) b := by
          rw [hsym (bumpAt a v) b]
          exact h
        exact hdb (hinj (bumpAt b (bumpAt a v)) h')
    have h_vd_b : g (bumpAt d v) b = c₀ := by
      rw [hc0]
      refine eq_third_of_ne hc12 ?_ ?_
      · intro h
        exact hface v d b hdb ⟨h_v_d.trans h_vb_d.symm, h.symm⟩
      · intro h
        have h' : g (bumpAt d v) b = g (bumpAt d v) d := by
          rw [hsym v d, h_v_d]
          exact h
        exact hdb.symm (hinj (bumpAt d v) h')
    have h_vda_b : g (bumpAt d (bumpAt a v)) b = c₀ := by
      rw [hc0]
      refine eq_third_of_ne hc12 ?_ ?_
      · intro h
        have h' : g (bumpAt d (bumpAt a v)) b = g (bumpAt d (bumpAt a v)) d := by
          rw [hsym (bumpAt a v) d, h_va_d]
          exact h
        exact hdb.symm (hinj (bumpAt d (bumpAt a v)) h')
      · intro h
        exact hface (bumpAt a v) d b hdb ⟨h_va_d.trans h_vba_d.symm, h.symm⟩
    let u : Vertex 2 := bumpAt d v
    have h_u_a : g u a = c₁ := by
      rw [hc1]
      refine eq_third_of_ne hc02 ?_ ?_
      · intro h
        have h' : g u a = g u b := h.trans h_vd_b.symm
        exact hab (hinj u h')
      · intro h
        have h' : g u a = g u d := by
          rw [hsym v d, h_v_d]
          exact h
        exact hda.symm (hinj u h')
    have h_ua_a : g (bumpAt a u) a = c₂ := by
      have hua : bumpAt a u = bumpAt d (bumpAt a v) := bumpAt_comm a d v
      rw [hc2]
      refine eq_third_of_ne hc01 ?_ ?_
      · intro h
        have h' : g (bumpAt a u) a = g (bumpAt a u) b := by
          calc g (bumpAt a u) a
              = c₀ := h
            _ = g (bumpAt d (bumpAt a v)) b := h_vda_b.symm
            _ = g (bumpAt a u) b := by rw [hua]
        exact hab (hinj (bumpAt a u) h')
      · intro h
        have h' : g (bumpAt a u) a = g (bumpAt a u) d := by
          calc g (bumpAt a u) a
              = c₁ := h
            _ = g (bumpAt a v) d := h_va_d.symm
            _ = g (bumpAt d (bumpAt a v)) d := (hsym (bumpAt a v) d).symm
            _ = g (bumpAt a u) d := by rw [hua]
        exact hda.symm (hinj (bumpAt a u) h')
    have h_eq12 : c₁ = c₂ := by
      rw [← h_u_a, ← hsym u a, h_ua_a]
    exact hc12 h_eq12
  let v0 : Vertex 2 := fun _ => 0
  have h00 : g v0 0 ≠ g v0 1 := fun h => by
    have := hinj v0 h
    exact absurd this (by decide)
  have h01 : g v0 0 ≠ g (bumpAt 0 v0) 1 := by
    intro h
    have h' : g (bumpAt 0 v0) 0 = g (bumpAt 0 v0) 1 := by
      rw [hsym]; exact h
    exact absurd (hinj (bumpAt 0 v0) h') (by decide)
  have h10 : g (bumpAt 1 v0) 0 ≠ g v0 1 := by
    intro h
    have h' : g (bumpAt 1 v0) 0 = g (bumpAt 1 v0) 1 := by
      rw [hsym]; exact h
    exact absurd (hinj (bumpAt 1 v0) h') (by decide)
  have h11 : g (bumpAt 1 v0) 0 ≠ g (bumpAt 0 v0) 1 := by
    intro h
    have h' : g (bumpAt 0 (bumpAt 1 v0)) 0 = g (bumpAt 0 (bumpAt 1 v0)) 1 := by
      rw [hsym (bumpAt 1 v0) 0, bumpAt_comm 0 1 v0, hsym (bumpAt 0 v0) 1]
      exact h
    exact absurd (hinj (bumpAt 0 (bumpAt 1 v0)) h') (by decide)
  rcases fin3_disjoint_pairs h00 h01 h10 h11 with h | h
  · exact face_contra v0 0 1 (by decide) h
  · exact face_contra v0 1 0 (by decide) h

private lemma vertex_on_face (v w : Vertex 2) {a b : Fin 3} (hab : a ≠ b)
    (hd : w (third a b) = v (third a b)) :
    w = v ∨ w = bumpAt a v ∨ w = bumpAt b v ∨ w = bumpAt a (bumpAt b v) := by
  have hda : third a b ≠ a := third_ne_left hab
  have hdb : third a b ≠ b := third_ne_right hab
  rcases zmod2_eq_or_eq_add_one (w a) (v a) with ha | ha <;>
    rcases zmod2_eq_or_eq_add_one (w b) (v b) with hb | hb
  · left
    funext i
    rcases fin3_mem_triple hab i with rfl | rfl | rfl <;> assumption
  · right; right; left
    funext i
    rcases fin3_mem_triple hab i with rfl | rfl | rfl
    · rw [bumpAt_apply_of_ne hab.symm]; exact ha
    · rw [bumpAt_apply_self]; exact hb
    · rw [bumpAt_apply_of_ne hdb.symm]; exact hd
  · right; left
    funext i
    rcases fin3_mem_triple hab i with rfl | rfl | rfl
    · rw [bumpAt_apply_self]; exact ha
    · rw [bumpAt_apply_of_ne hab]; exact hb
    · rw [bumpAt_apply_of_ne hda.symm]; exact hd
  · right; right; right
    funext i
    rcases fin3_mem_triple hab i with rfl | rfl | rfl
    · rw [bumpAt_apply_self, bumpAt_apply_of_ne hab.symm]; exact ha
    · rw [bumpAt_apply_of_ne hab, bumpAt_apply_self]; exact hb
    · rw [bumpAt_apply_of_ne hda.symm, bumpAt_apply_of_ne hdb.symm]; exact hd

end ClaudesCyclesM2Proof

theorem OMA.solution : type_of% @ClaudesCycles.cube_hamiltonian_arc_decomposition_impossible_m2 := by
  rintro ⟨σ, hcyc, hdecomp⟩
  let f : ClaudesCycles.Vertex 2 → Fin 3 → Fin 3 := fun v b => (hdecomp v b).choose
  have hf_eq : ∀ v b, σ (f v b) v = ClaudesCycles.bumpAt b v :=
    fun v b => (hdecomp v b).choose_spec.1
  have hf_uniq : ∀ v b c, σ c v = ClaudesCycles.bumpAt b v → c = f v b :=
    fun v b c h => (hdecomp v b).choose_spec.2 c h
  have hsame : ∀ c (u w : ClaudesCycles.Vertex 2), (σ c).SameCycle u w := by
    intro c u w
    have hu : σ c u ≠ u := by
      rw [← Equiv.Perm.mem_support, (hcyc c).2.2]
      exact Finset.mem_univ u
    have hw : σ c w ≠ w := by
      rw [← Equiv.Perm.mem_support, (hcyc c).2.2]
      exact Finset.mem_univ w
    exact (hcyc c).2.1.sameCycle hu hw
  have hne_rev : ∀ v b, f v b ≠ f (ClaudesCycles.bumpAt b v) b := by
    intro v b heq
    let c := f v b
    let u := ClaudesCycles.bumpAt b v
    have h1 : σ c v = u := hf_eq v b
    have h2 : σ c u = v := by
      have := hf_eq u b
      rw [← heq, ClaudesCyclesM2Proof.bumpAt_invol] at this
      exact this
    have h1_inv : (σ c)⁻¹ u = v := (Equiv.symm_apply_eq (σ c)).mpr h1.symm
    have h2_inv : (σ c)⁻¹ v = u := (Equiv.symm_apply_eq (σ c)).mpr h2.symm
    have hinv : ∀ k : ℤ, ((σ c) ^ k) v = v ∨ ((σ c) ^ k) v = u := by
      refine ClaudesCyclesM2Proof.perm_zpow_invariant (σ c) (fun x => x = v ∨ x = u) ?_ ?_ (Or.inl rfl)
      · rintro x (rfl | rfl)
        · exact Or.inr h1
        · exact Or.inl h2
      · rintro x (rfl | rfl)
        · exact Or.inr h2_inv
        · exact Or.inl h1_inv
    let b' : Fin 3 := if b = 0 then 1 else 0
    have hbb' : b ≠ b' := by
      fin_cases b <;> decide
    let w := ClaudesCycles.bumpAt b' v
    rcases hsame c v w with ⟨k, hk⟩
    rcases hinv k with hkv | hku
    · rw [hk] at hkv
      exact ClaudesCyclesM2Proof.bumpAt_ne_self b' v hkv
    · rw [hk] at hku
      have hcoord := congrFun hku b'
      dsimp only [w, u] at hcoord
      rw [ClaudesCycles.bumpAt_apply_self, ClaudesCycles.bumpAt_apply_of_ne hbb'] at hcoord
      exact ClaudesCyclesM2Proof.zmod2_add_one_ne (v b') hcoord
  let g : ClaudesCycles.Vertex 2 → Fin 3 → Fin 3 :=
    fun v b => ClaudesCyclesM2Proof.third (f v b) (f (ClaudesCycles.bumpAt b v) b)
  have hsym : ∀ v b, g (ClaudesCycles.bumpAt b v) b = g v b := by
    intro v b
    simp only [g, ClaudesCyclesM2Proof.bumpAt_invol, ClaudesCyclesM2Proof.third_comm]
  have hinj : ∀ v, Function.Injective (g v) := by
    intro v b1 b2 hgb
    let c := g v b1
    rcases (hcyc c).1 v with ⟨b_out, h_out⟩
    have hf_out : f v b_out = c := (hf_uniq v b_out c h_out.symm).symm
    rcases (hcyc c).1 ((σ c)⁻¹ v) with ⟨b_in, h_in⟩
    have h_in' : (σ c)⁻¹ v = ClaudesCycles.bumpAt b_in v := by
      have h' : ClaudesCycles.bumpAt b_in ((σ c)⁻¹ v) = v := by
        simpa using h_in
      calc (σ c)⁻¹ v
          = ClaudesCycles.bumpAt b_in (ClaudesCycles.bumpAt b_in ((σ c)⁻¹ v)) :=
              (ClaudesCyclesM2Proof.bumpAt_invol b_in _).symm
        _ = ClaudesCycles.bumpAt b_in v := by rw [h']
    have h_in_fwd : σ c (ClaudesCycles.bumpAt b_in v) = v := by
      rw [← h_in']
      simp
    have hf_in : f (ClaudesCycles.bumpAt b_in v) b_in = c := by
      have h' : σ c (ClaudesCycles.bumpAt b_in v) =
          ClaudesCycles.bumpAt b_in (ClaudesCycles.bumpAt b_in v) := by
        rw [ClaudesCyclesM2Proof.bumpAt_invol]
        exact h_in_fwd
      exact (hf_uniq (ClaudesCycles.bumpAt b_in v) b_in c h').symm
    have h_out_ne_in : b_out ≠ b_in := by
      intro h
      subst h
      exact hne_rev v b_out (hf_out.trans hf_in.symm)
    have h_eq_third : ∀ b, g v b = c → b = ClaudesCyclesM2Proof.third b_out b_in := by
      intro b hgc
      refine ClaudesCyclesM2Proof.eq_third_of_ne h_out_ne_in ?_ ?_
      · intro h
        rw [h] at hgc
        exact ClaudesCyclesM2Proof.third_ne_left (hne_rev v b_out) (hgc.trans hf_out.symm)
      · intro h
        rw [h] at hgc
        exact ClaudesCyclesM2Proof.third_ne_right (hne_rev v b_in) (hgc.trans hf_in.symm)
    exact (h_eq_third b1 rfl).trans (h_eq_third b2 hgb.symm).symm
  have hface : ∀ v a b, a ≠ b →
      ¬ (g v a = g (ClaudesCycles.bumpAt b v) a ∧ g v b = g (ClaudesCycles.bumpAt a v) b) := by
    intro v a b hab ⟨ha_eq, hb_eq⟩
    let d := ClaudesCyclesM2Proof.third a b
    have hda : d ≠ a := ClaudesCyclesM2Proof.third_ne_left hab
    have hdb : d ≠ b := ClaudesCyclesM2Proof.third_ne_right hab
    let c1 := g v a
    let c2 := g v b
    have hc12 : c1 ≠ c2 := fun h => hab (hinj v h)
    let c := g v d
    have hc_eq : c = ClaudesCyclesM2Proof.third c1 c2 :=
      ClaudesCyclesM2Proof.eq_third_of_ne hc12 (fun h => hda (hinj v h)) (fun h => hdb (hinj v h))
    have hg_face : ∀ w : ClaudesCycles.Vertex 2, w d = v d → g w d = c := by
      intro w hwd
      rcases ClaudesCyclesM2Proof.vertex_on_face v w hab hwd with rfl | rfl | rfl | rfl
      · rfl
      · rw [hc_eq]
        refine ClaudesCyclesM2Proof.eq_third_of_ne hc12 ?_ ?_
        · intro h
          have h' : g (ClaudesCycles.bumpAt a v) d = g (ClaudesCycles.bumpAt a v) a := by
            rw [hsym]; exact h
          exact hda (hinj (ClaudesCycles.bumpAt a v) h')
        · intro h
          have h' : g (ClaudesCycles.bumpAt a v) d = g (ClaudesCycles.bumpAt a v) b :=
            h.trans hb_eq
          exact hdb (hinj (ClaudesCycles.bumpAt a v) h')
      · rw [hc_eq]
        refine ClaudesCyclesM2Proof.eq_third_of_ne hc12 ?_ ?_
        · intro h
          have h' : g (ClaudesCycles.bumpAt b v) d = g (ClaudesCycles.bumpAt b v) a :=
            h.trans ha_eq
          exact hda (hinj (ClaudesCycles.bumpAt b v) h')
        · intro h
          have h' : g (ClaudesCycles.bumpAt b v) d = g (ClaudesCycles.bumpAt b v) b := by
            rw [hsym]; exact h
          exact hdb (hinj (ClaudesCycles.bumpAt b v) h')
      · rw [hc_eq]
        refine ClaudesCyclesM2Proof.eq_third_of_ne hc12 ?_ ?_
        · intro h
          have h' : g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) d =
              g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) a := by
            rw [hsym (ClaudesCycles.bumpAt b v) a]
            exact h.trans ha_eq
          exact hda (hinj (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) h')
        · intro h
          have h' : g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) d =
              g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) b := by
            calc g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) d
                = g (ClaudesCycles.bumpAt a v) b := h.trans hb_eq
              _ = g (ClaudesCycles.bumpAt b (ClaudesCycles.bumpAt a v)) b :=
                  (hsym (ClaudesCycles.bumpAt a v) b).symm
              _ = g (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) b := by
                  rw [ClaudesCyclesM2Proof.bumpAt_comm b a v]
          exact hdb (hinj (ClaudesCycles.bumpAt a (ClaudesCycles.bumpAt b v)) h')
    have hinv : ∀ k : ℤ, (((σ c) ^ k) v) d = v d := by
      refine ClaudesCyclesM2Proof.perm_zpow_invariant (σ c) (fun w => w d = v d) ?_ ?_ rfl
      · intro w hwd
        rcases (hcyc c).1 w with ⟨b', hb'⟩
        have hb'd : b' ≠ d := by
          intro h
          subst h
          have hfc : f w d = c := (hf_uniq w d c hb'.symm).symm
          have hne := ClaudesCyclesM2Proof.third_ne_left (hne_rev w d)
          exact hne ((hg_face w hwd).trans hfc.symm)
        rw [← hb', ClaudesCycles.bumpAt_apply_of_ne hb'd, hwd]
      · intro w hwd
        rcases (hcyc c).1 ((σ c)⁻¹ w) with ⟨b', hb'⟩
        have hprev : (σ c)⁻¹ w = ClaudesCycles.bumpAt b' w := by
          have h' : ClaudesCycles.bumpAt b' ((σ c)⁻¹ w) = w := by
            simpa using hb'
          calc (σ c)⁻¹ w
              = ClaudesCycles.bumpAt b' (ClaudesCycles.bumpAt b' ((σ c)⁻¹ w)) :=
                  (ClaudesCyclesM2Proof.bumpAt_invol b' _).symm
            _ = ClaudesCycles.bumpAt b' w := by rw [h']
        have hb'd : b' ≠ d := by
          intro h
          subst h
          have hfwd : σ c (ClaudesCycles.bumpAt d w) =
              ClaudesCycles.bumpAt d (ClaudesCycles.bumpAt d w) := by
            rw [ClaudesCyclesM2Proof.bumpAt_invol, ← hprev]
            simp
          have hfc : f (ClaudesCycles.bumpAt d w) d = c :=
            (hf_uniq (ClaudesCycles.bumpAt d w) d c hfwd).symm
          have hne := ClaudesCyclesM2Proof.third_ne_right (hne_rev w d)
          exact hne ((hg_face w hwd).trans hfc.symm)
        rw [hprev, ClaudesCycles.bumpAt_apply_of_ne hb'd, hwd]
    rcases hsame c v (ClaudesCycles.bumpAt d v) with ⟨k, hk⟩
    have hcoord := hinv k
    rw [hk, ClaudesCycles.bumpAt_apply_self] at hcoord
    exact ClaudesCyclesM2Proof.zmod2_add_one_ne (v d) hcoord
  exact ClaudesCyclesM2Proof.no_edge_coloring_without_bichromatic_face g hsym hinj hface
