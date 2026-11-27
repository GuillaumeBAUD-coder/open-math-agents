import FormalConjectures.ErdosProblems.«147»

/-! A bipartite minimum-degree reduction for Janzer's conjecture, Erdős problem 147. -/
-- Credit: @NicholasWierenga

namespace OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R1

open Filter Asymptotics SimpleGraph Finset
open scoped Classical

/-- A two-colouring retains at least half the edges between its colour classes. -/
lemma exists_bipartite_half {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧
      G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  let side (c : V → Bool) : Set V := {v | c v = true}
  let cut (c : V → Bool) := G.between (side c) (side c)ᶜ
  let w (c : V → Bool) (e : Sym2 V) : ℕ := if e ∈ (cut c).edgeFinset then 1 else 0
  have cutSum (c : V → Bool) : ∑ e ∈ G.edgeFinset, w c e = (cut c).edgeFinset.card := by
    have hsub : (cut c).edgeFinset ⊆ G.edgeFinset := edgeFinset_mono between_le
    exact (Finset.card_eq_sum_ite hsub).symm
  have cross (c : V → Bool) (a b : V) (hab : G.Adj a b) :
      s(a, b) ∈ (cut c).edgeFinset ↔ c a ≠ c b := by
    simp only [mem_edgeFinset, mem_edgeSet, cut, between_adj, side, Set.mem_compl_iff,
      Set.mem_ofPred_eq, hab, true_and]
    cases c a <;> cases c b <;> decide
  have pairSum (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (∑ c : V → Bool, (1 : ℕ)) = ∑ c : V → Bool, 2 * w c e := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      let flip (c : V → Bool) : V → Bool := fun x => if x = a then !(c x) else c x
      have hinv : Function.Involutive flip := by
        intro c
        funext x
        by_cases hx : x = a <;> simp [flip, hx]
      have swap : (∑ c, w (flip c) s(a, b)) = ∑ c, w c s(a, b) :=
        Fintype.sum_equiv hinv.toPerm _ _ (fun _ => rfl)
      calc
        _ = ∑ c : V → Bool, (w (flip c) s(a, b) + w c s(a, b)) := by
          apply Finset.sum_congr rfl
          intro c _
          simp only [w, cross _ _ _ hab]
          simp only [flip, if_pos rfl, if_neg hab.ne.symm]
          cases c a <;> cases c b <;> decide
        _ = _ := by rw [Finset.sum_add_distrib, swap, ← two_mul, Finset.mul_sum]
  have total : (∑ _c : V → Bool, G.edgeFinset.card) =
      ∑ c : V → Bool, 2 * (cut c).edgeFinset.card := by
    calc
      _ = ∑ _c : V → Bool, ∑ _e ∈ G.edgeFinset, (1 : ℕ) := by simp
      _ = ∑ e ∈ G.edgeFinset, ∑ _c : V → Bool, (1 : ℕ) := Finset.sum_comm
      _ = ∑ e ∈ G.edgeFinset, ∑ c : V → Bool, 2 * w c e :=
        Finset.sum_congr rfl pairSum
      _ = ∑ c : V → Bool, ∑ e ∈ G.edgeFinset, 2 * w c e := Finset.sum_comm
      _ = _ := by simp_rw [← Finset.mul_sum, cutSum]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty total.le
  exact ⟨cut c, between_le, between_isBipartite disjoint_compl_right, by convert! hc⟩

/-- Delete a low-degree vertex at each step. The degree bound may be real-valued. -/
lemma bipartite_free_edge_bound {W : Type} (H : SimpleGraph W) (n : ℕ) (D : ℝ)
    (sparse : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      Fintype.card V ≤ n → G.IsBipartite → H.Free G → ∃ v, (G.degree v : ℝ) ≤ D) :
    ∀ (m : ℕ), m ≤ n → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = m → G.IsBipartite → H.Free G → (G.edgeFinset.card : ℝ) ≤ m * D := by
  classical
  intro m
  induction m with
  | zero =>
    intro _ V _ G hV _ _
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hbot : G = ⊥ := Subsingleton.elim _ _
    simp [hbot]
  | succ m ih =>
    intro hmn V _ G hV hb hf
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, hv⟩ := sparse V G (by omega) hb hf
    let S : Set V := {v}ᶜ
    have hs : Fintype.card S = m := by
      dsimp only [S]
      rw [Fintype.card_compl_set, hV, @Fintype.card_unique ({v} : Set V), Nat.add_sub_cancel]
    have drop := Copy.induce G S
    have hsmall := ih (by omega) S (G.induce S) hs (Colorable.of_hom drop.toHom hb)
      (fun h => hf (h.trans ⟨drop⟩))
    have hedge : (G.induce S).edgeFinset.card + G.degree v = G.edgeFinset.card := by
      dsimp only [S]
      rw [card_edgeFinset_induce_compl_singleton,
        card_edgeFinset_deleteIncidenceSet, Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
    have hreal : ((G.induce S).edgeFinset.card : ℝ) + G.degree v = G.edgeFinset.card := by
      exact_mod_cast hedge
    rw [Nat.cast_succ, add_mul, one_mul, ← hreal]
    convert! add_le_add hsmall hv

/-- A minimum-degree embedding test on bipartite hosts gives the usual extremal upper bound. -/
lemma extremal_of_bipartite_min_degree {q : ℕ} (H : SimpleGraph (Fin q)) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (force : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), G.IsBipartite →
      (∀ v, C * (Fintype.card V : ℝ) ^ a < G.degree v) → H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (a + 1) := by
  classical
  rw [isBigO_iff]
  refine ⟨2 * C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have bound : (extremalNumber n H : ℝ) ≤ 2 * C * (n : ℝ) ^ (a + 1) := by
    have hnon : 0 ≤ 2 * C * (n : ℝ) ^ (a + 1) := by positivity
    nth_rw 1 [← Fintype.card_fin n]
    apply (extremalNumber_le_iff_of_nonneg (V := Fin n) H hnon).2
    intro G _ hf
    obtain ⟨B, hBG, hb, hedge⟩ := exists_bipartite_half G
    have hfree : H.Free B := fun h => hf (h.trans (.of_le hBG))
    have sparse (V : Type) [Fintype V] [Nonempty V] (F : SimpleGraph V)
        (hV : Fintype.card V ≤ n) (hbip : F.IsBipartite) (hF : H.Free F) :
        ∃ v, (F.degree v : ℝ) ≤ C * n ^ a := by
      by_contra! hd
      apply hF (force V F hbip ?_)
      intro v
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hV) ha) hC) (hd v)
    have hB := bipartite_free_edge_bound H n (C * n ^ a) sparse n le_rfl (Fin n) B
      (Fintype.card_fin n) hb hfree
    have hE : G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by convert! hedge
    calc
      (G.edgeFinset.card : ℝ) ≤ 2 * (B.edgeFinset.card : ℝ) := by exact_mod_cast hE
      _ ≤ 2 * (n * (C * (n : ℝ) ^ a)) := by
        convert! mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by rw [Real.rpow_add hn', Real.rpow_one]; ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (Real.rpow_nonneg hn'.le _)] using bound

/-- Janzer's even-degree case. -/
def H1 : Prop := ∀ (r : ℕ), 4 ≤ r → Even r → ∀ ε : ℝ, 0 < ε →
  ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree r ∧
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε)

/-- Janzer's cubic case. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε →
  ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree 3 ∧
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (4 / 3 + ε : ℝ)

/-- In the remaining degrees it suffices to embed one fixed witness in bipartite
hosts whose minimum degree exceeds a power of their order. -/
def H3 : Prop := ∀ (r : ℕ), 5 ≤ r → Odd r → ∀ ε : ℝ, 0 < ε →
  ε ≤ 2 / ((r : ℝ) * ((r : ℝ) + 1)) →
  ∃ (q : ℕ) (H : SimpleGraph (Fin q)) (C : ℝ), 0 < q ∧ H.IsRegularOfDegree r ∧ 0 ≤ C ∧
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), G.IsBipartite →
      (∀ v, C * (Fintype.card V : ℝ) ^ (1 - 2 / (r : ℝ) + ε) < G.degree v) → H ⊑ G

lemma regular_hall {V : Type*} [Fintype V] {G : SimpleGraph V} {d : ℕ}
    (hG : G.IsRegularOfDegree d) (hd : 0 < d) (S : Set V) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  classical
  let s := S.toFinset
  let t := s.biUnion (fun v ↦ G.neighborFinset v)
  have hs : (↑s : Set V) = S := Set.coe_toFinset S
  have ht : (↑t : Set V) = ⋃ x ∈ S, G.neighborSet x := by
    ext y
    simp [t, s]
  rw [← ht, ← hs, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hfilter (u : Finset V) (v : V) :
      u.filter (G.Adj v) ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).2 (Finset.mem_filter.1 hw).2
  have hrow (x : V) (hx : x ∈ s) :
      (∑ y ∈ t, if G.Adj x y then (1 : ℕ) else 0) = d := by
    have heq : t.filter (G.Adj x) = G.neighborFinset x := by
      refine subset_antisymm (hfilter t x) ?_
      intro y hy
      exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨x, hx, hy⟩,
        (G.mem_neighborFinset x y).1 hy⟩
    simp [Finset.sum_boole, heq, card_neighborFinset_eq_degree, hG.degree_eq]
  have hcol (y : V) :
      (∑ x ∈ s, if G.Adj x y then (1 : ℕ) else 0) ≤ d := by
    simp_rw [show ∀ x, G.Adj x y ↔ G.Adj y x from fun x ↦ ⟨Adj.symm, Adj.symm⟩,
      Finset.sum_boole]
    exact (Finset.card_le_card (hfilter s y)).trans_eq
      ((G.card_neighborFinset_eq_degree y).trans (hG.degree_eq y))
  apply Nat.le_of_mul_le_mul_right (a := s.card) (b := t.card) (c := d) _ hd
  calc
    s.card * d = ∑ x ∈ s, (∑ y ∈ t, if G.Adj x y then (1 : ℕ) else 0) := by
      rw [Finset.sum_congr rfl hrow]
      simp
    _ = ∑ y ∈ t, (∑ x ∈ s, if G.Adj x y then (1 : ℕ) else 0) := Finset.sum_comm
    _ ≤ ∑ _y ∈ t, d := Finset.sum_le_sum fun y _ ↦ hcol y
    _ = t.card * d := by simp

/-- A regular finite bipartite graph has a spanning subgraph of every smaller degree. -/
theorem exists_regular_spanning_subgraph {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hb : G.IsBipartite) {r d : ℕ} (hrd : r ≤ d) (hG : G.IsRegularOfDegree d) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧ H.IsRegularOfDegree r := by
  classical
  induction d generalizing G with
  | zero =>
      have hr : r = 0 := Nat.eq_zero_of_le_zero hrd
      exact ⟨G, le_rfl, hb, hr.symm ▸ hG⟩
  | succ d ih =>
      by_cases hr : r = d + 1
      · exact ⟨G, le_rfl, hb, hr.symm ▸ hG⟩
      have hrd' : r ≤ d := by omega
      obtain ⟨s, t, hst⟩ := hb.exists_isBipartiteWith
      obtain ⟨M, hM⟩ :=
        exists_isPerfectMatching_of_forall_ncard_le hst (regular_hall hG (Nat.succ_pos d))
      let G' := G \ M.spanningCoe
      have hG' : G' ≤ G := sdiff_le
      have hb' : G'.IsBipartite := Colorable.mono_left hG' hb
      let : DecidableRel G'.Adj := fun _ _ ↦ Classical.propDecidable _
      have hM' (v : V) : M.spanningCoe.degree v = 1 := by
        obtain ⟨w, hw, huniq⟩ := Subgraph.isPerfectMatching_iff.mp hM v
        rw [← card_neighborFinset_eq_degree, Finset.card_eq_one]
        refine ⟨w, ?_⟩
        ext z
        simp only [mem_neighborFinset, Finset.mem_singleton, Subgraph.spanningCoe_adj]
        refine ⟨huniq z, ?_⟩
        rintro rfl
        exact hw
      have hd' : G'.IsRegularOfDegree d := by
        intro v
        have hsub : M.spanningCoe.neighborFinset v ⊆ G.neighborFinset v := by
          intro w hw
          exact (G.mem_neighborFinset v w).2 (M.spanningCoe_le
            ((M.spanningCoe.mem_neighborFinset v w).1 hw))
        rw [← card_neighborFinset_eq_degree, neighborFinset_sdiff, Finset.card_sdiff_of_subset hsub,
          card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hG.degree_eq, hM']
        omega
      obtain ⟨H, hH, hbH, hdH⟩ := ih hb' hrd' hd'
      exact ⟨H, hH.trans hG', hbH, hdH⟩

/-- A power bound for a regular bipartite graph remains valid for a spanning regular subgraph. -/
theorem exists_regular_spanning_subgraph_asymptotic {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hb : G.IsBipartite) {r d : ℕ} (hrd : r ≤ d)
    (hG : G.IsRegularOfDegree d) {f : ℕ → ℝ}
    (hbound : (fun n : ℕ ↦ (extremalNumber n G : ℝ)) =O[Filter.atTop] f) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ ↦ (extremalNumber n H : ℝ)) =O[Filter.atTop] f := by
  classical
  obtain ⟨H, hH, hbH, hrH⟩ := exists_regular_spanning_subgraph hb hrd hG
  refine ⟨H, hH, hbH, hrH, ?_⟩
  apply IsBigO.trans _ hbound
  refine isBigO_of_le _ ?_
  intro n
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast (IsContained.of_le hH).extremalNumber_le (n := n)

/-- The even-degree bounds give the conjectured estimate for odd degrees when the
allowed error exceeds the exponent loss from reducing the degree by one. -/
theorem odd_degree_of_even_degree
    (evenBounds : H1)
    (r : ℕ) (hr : 3 ≤ r) (hOdd : Odd r) (ε : ℝ)
    (hε : 2 / ((r : ℝ) * ((r : ℝ) + 1)) < ε) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)), 0 < q ∧ H.IsBipartite ∧ H.IsRegularOfDegree r ∧
      (fun n : ℕ ↦ (extremalNumber n H : ℝ)) =O[Filter.atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε) := by
  have hEven : Even (r + 1) := by
    obtain ⟨k, hk⟩ := hOdd
    exact ⟨k + 1, by omega⟩
  let η := ε - 2 / ((r : ℝ) * ((r : ℝ) + 1))
  have hη : 0 < η := sub_pos.mpr hε
  obtain ⟨q, G, hq, hb, hG, hBound⟩ := evenBounds (r + 1) (by omega) hEven η hη
  obtain ⟨H, _, hbH, hH, hBoundH⟩ :=
    exists_regular_spanning_subgraph_asymptotic hb (Nat.le_succ r) hG hBound
  have hr₀ : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hr₁ : 0 < (r : ℝ) + 1 := by positivity
  have hgap : 2 / (r : ℝ) - 2 / ((r : ℝ) + 1) =
      2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
    field_simp [hr₀.ne', hr₁.ne']
    ring
  have hExp : 2 - 2 / ((r + 1 : ℕ) : ℝ) + η = 2 - 2 / (r : ℝ) + ε := by
    rw [Nat.cast_add, Nat.cast_one]
    dsimp [η]
    linarith only [hgap]
  exact ⟨q, H, hq, hbH, hH, by simpa only [hExp] using hBoundH⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos147.erdos_147.variants.janzer_conjecture := by
  intro evenCase cubicCase oddCase r hr ε hε
  by_cases he : Even r
  · have h4 : 4 ≤ r := by obtain ⟨k, hk⟩ := he; omega
    obtain ⟨q, H, hq, _, hreg, hbound⟩ := evenCase r h4 he ε hε
    exact ⟨q, H, hq, hreg, hbound⟩
  by_cases hc : r = 3
  · subst r
    obtain ⟨q, H, hq, _, hreg, hbound⟩ := cubicCase ε hε
    exact ⟨q, H, hq, hreg, by convert hbound using 1; norm_num⟩
  have ho : Odd r := Nat.not_even_iff_odd.mp he
  have h5 : 5 ≤ r := by obtain ⟨k, hk⟩ := ho; omega
  by_cases hsmall : ε ≤ 2 / ((r : ℝ) * ((r : ℝ) + 1))
  · obtain ⟨q, H, C, hq, hreg, hC, hforce⟩ := oddCase r h5 ho ε hε hsmall
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast (by omega : 2 ≤ r)
    have hdiv : 2 / (r : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hr'
    have hbound := extremal_of_bipartite_min_degree H
      (by linarith : 0 ≤ 1 - 2 / (r : ℝ) + ε) hC hforce
    have hexp : 1 - 2 / (r : ℝ) + ε + 1 = 2 - 2 / (r : ℝ) + ε := by ring
    exact ⟨q, H, hq, hreg, hexp ▸ hbound⟩
  · obtain ⟨q, H, hq, _, hreg, hbound⟩ :=
      odd_degree_of_even_degree evenCase r hr ho ε (lt_of_not_ge hsmall)
    exact ⟨q, H, hq, hreg, hbound⟩

end OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R1
