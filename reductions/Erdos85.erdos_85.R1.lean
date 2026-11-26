import FormalConjectures.ErdosProblems.«85»

/-!
# A deletion interval for Erdős problem 85

Credit: @desenyon.

In a graph without a four-cycle, the neighbors of any vertex induce a matching
and isolated vertices. Delete the vertex and a union of components of that
matching. Every surviving vertex loses at most one neighbor. A cut through one
matched pair is also possible when the surviving endpoint has a unit of slack.

This gives an interval of orders below a higher-degree witness. Theorem 6 of
L. Boza, arXiv:2409.12770v2, uses deletion of the full closed neighborhood.
Here selecting part of the neighborhood gives the intermediate orders and
identifies the regular, triangular obstruction to attaining an even deletion size.
-/

namespace OMA.R_Erdos85_erdos_85_R1

open SimpleGraph Filter Finset
open scoped Classical

private lemma unique_common {V : Type*} (G : SimpleGraph V) (hG : ¬ cycleGraph 4 ⊑ G)
    {v x a b : V} (hvx : v ≠ x) (hva : G.Adj v a) (hxa : G.Adj x a)
    (hvb : G.Adj v b) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  let p : Fin 4 → V := ![v, a, x, b]
  have hpair : ∀ i j : Fin 4, p i = p j → i = j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, hvx, hvx.symm, hab, Ne.symm hab,
      hva.ne, hva.ne.symm, hxa.ne, hxa.ne.symm, hvb.ne, hvb.ne.symm, hxb.ne, hxb.ne.symm]
  apply hG
  refine ⟨⟨⟨p, ?_⟩, fun {i j} => hpair i j⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact hva | exact hva.symm | exact hxa | exact hxa.symm
    | exact hvb | exact hvb.symm | exact hxb | exact hxb.symm
    | exact False.elim ((by decide : ¬ _) hij)

/-- A matching together with isolated vertices has a union of components of every
even size up to its order. -/
private lemma even_selection {V : Type*} (G : SimpleGraph V)
    (T : Finset V) (matching : ∀ x ∈ T, ∀ a ∈ T, ∀ b ∈ T,
      G.Adj x a → G.Adj x b → a = b)
    (r : ℕ) (hsize : 2 * r ≤ T.card) :
    ∃ S ⊆ T, S.card = 2 * r ∧ ∀ x ∈ T, x ∉ S → ∀ y ∈ S, ¬ G.Adj x y := by
  classical
  induction r generalizing T with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨a, ha, b, hb, hab, hclosed⟩ :
        ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧
          ∀ x ∈ T, x ≠ a → x ≠ b → ¬ G.Adj x a ∧ ¬ G.Adj x b := by
      by_cases hedge : ∃ a ∈ T, ∃ b ∈ T, G.Adj a b
      · obtain ⟨a, ha, b, hb, e⟩ := hedge
        exact ⟨a, ha, b, hb, e.ne, fun x hx hxa hxb =>
          ⟨fun h => hxb (matching a ha x hx b hb h.symm e),
           fun h => hxa (matching b hb x hx a ha h.symm e.symm)⟩⟩
      · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
        exact ⟨a, ha, b, hb, hab, fun x hx _ _ =>
          ⟨fun h => hedge ⟨x,hx,a,ha,h⟩, fun h => hedge ⟨x,hx,b,hb,h⟩⟩⟩
    let U := (T.erase a).erase b
    have hb' : b ∈ T.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
    have hcard : U.card + 2 = T.card := by
      dsimp [U]
      rw [card_erase_of_mem hb', card_erase_of_mem ha]
      omega
    have hUT : U ⊆ T := (erase_subset ..).trans (erase_subset ..)
    obtain ⟨S, hS, hc, hs⟩ := ih U
      (fun x hx a ha b hb => matching x (hUT hx) a (hUT ha) b (hUT hb)) (by omega)
    have haS : a ∉ S := by intro h; simpa [U] using hS h
    have hbS : b ∉ S := by intro h; simpa [U] using hS h
    refine ⟨insert a (insert b S), ?_, ?_, ?_⟩
    · exact insert_subset ha (insert_subset hb (hS.trans hUT))
    · simp [hab, haS, hbS, hc, Nat.mul_succ]
    · intro x hx hxout y hy
      simp only [mem_insert, not_or] at hxout
      obtain ⟨hxa, hxb, hxs⟩ := hxout
      have hxU : x ∈ U := by simp [U, hxa, hxb, hx]
      rcases mem_insert.mp hy with rfl | hy
      · exact (hclosed x hx hxa hxb).1
      rcases mem_insert.mp hy with rfl | hy
      · exact (hclosed x hx hxa hxb).2
      · exact hs x hxU hxs y hy

/-- To cut an odd number out of a matching, one distinguished vertex suffices
if its possible mate has a unit of degree to spare. -/
private lemma link_selection {V : Type*} (G : SimpleGraph V) (T : Finset V)
    (matching : ∀ x ∈ T, ∀ a ∈ T, ∀ b ∈ T, G.Adj x a → G.Adj x b → a = b)
    (spare : V → Prop) (k : ℕ) (hk : k ≤ T.card)
    (h : Even k ∨ ∃ a ∈ T, ∀ x ∈ T, G.Adj x a → spare x) :
    ∃ S ⊆ T, S.card = k ∧ ∀ x ∈ T, x ∉ S → ∀ y ∈ S, G.Adj x y → spare x := by
  classical
  by_cases he : Even k
  · obtain ⟨r, hr⟩ := he
    obtain ⟨S, hST, hc, hs⟩ := even_selection G T matching r (by omega)
    exact ⟨S, hST, by omega, fun x hx hxs y hy e => (hs x hx hxs y hy e).elim⟩
  · obtain ⟨a, ha, hsp⟩ := h.resolve_left he
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp he
    have hcT := card_erase_of_mem ha
    obtain ⟨S, hST, hc, hs⟩ := even_selection G (T.erase a)
      (fun x hx b hb c hc => matching x (mem_of_mem_erase hx) b
        (mem_of_mem_erase hb) c (mem_of_mem_erase hc)) r (by omega)
    have haS : a ∉ S := fun h => (ne_of_mem_erase (hST h)) rfl
    refine ⟨insert a S, insert_subset ha (hST.trans (erase_subset ..)), ?_, ?_⟩
    · rw [card_insert_of_notMem haS]; omega
    · intro x hx hxs y hy e
      rw [mem_insert, not_or] at hxs
      rcases mem_insert.mp hy with rfl | hy
      · exact hsp x hx e
      · exact (hs x (mem_erase.mpr ⟨hxs.1, hx⟩) hxs.2 y hy e).elim

lemma lt_threshold_iff {n d : ℕ} :
    d < Erdos85.f n ↔ ∃ G : SimpleGraph (Fin n), ¬ cycleGraph 4 ⊑ G ∧ d ≤ G.minDegree := by
  classical
  let P := {k : ℕ | ∀ G : SimpleGraph (Fin n), k ≤ G.minDegree → cycleGraph 4 ⊑ G}
  have hne : P.Nonempty := by
    refine ⟨n+1, fun G h => ?_⟩
    by_cases hz : n = 0
    · subst n; simp at h
    · have : NeZero n := ⟨hz⟩
      have := G.minDegree_lt_card
      simp only [Fintype.card_fin] at this
      omega
  change d < sInf P ↔ _
  constructor
  · intro h
    by_contra hnone
    have hd : d ∈ P := fun G hdeg => by
      by_contra hfree
      exact hnone ⟨G, hfree, hdeg⟩
    exact h.not_ge (Nat.sInf_le hd)
  · rintro ⟨G, hf, hg⟩
    by_contra! h
    exact hf ((Nat.sInf_mem hne : sInf P ∈ P) G (h.trans hg))

/-- Relabel the induced graph on the retained vertices and retain the degree
bound measured there. -/
private lemma realize_induced {M n d : ℕ} (G : SimpleGraph (Fin M))
    (hG : ¬ cycleGraph 4 ⊑ G) (R : Finset (Fin M)) (hn : 0 < n) (hc : R.card = n)
    (hd : ∀ x ∈ R, d ≤ ((G.neighborFinset x) ∩ R).card) : d < Erdos85.f n := by
  classical
  have hc' : Fintype.card R = n := by simpa using hc
  let e := (Fintype.equivFinOfCardEq hc').symm
  let I := G.induce (R : Set (Fin M))
  let H := I.comap e
  let iso : H ≃g I := SimpleGraph.Iso.comap e I
  let emb : I ↪g G := SimpleGraph.Embedding.comap (.subtype (· ∈ R)) G
  apply lt_threshold_iff.mpr
  refine ⟨H, fun h => hG ((h.trans ⟨iso.toCopy⟩).trans ⟨emb.toCopy⟩), ?_⟩
  have : NeZero n := ⟨by omega⟩
  apply H.le_minDegree_of_forall_le_degree
  intro x
  let U := G.neighborFinset (e x).1 ∩ R
  let liftNeighbor (z : U) : H.neighborSet x := by
    let w : R := ⟨z.1, (mem_inter.mp z.property).2⟩
    refine ⟨e.symm w, ?_⟩
    change G.Adj (e x).1 (e (e.symm w)).1
    rw [e.apply_symm_apply]
    exact (G.mem_neighborFinset _ _).mp (mem_inter.mp z.property).1
  have inj : Function.Injective liftNeighbor := by
    intro a b hab
    apply Subtype.ext
    simpa [liftNeighbor] using congrArg (fun w : H.neighborSet x => (e w.1).1) hab
  calc
    d ≤ U.card := hd (e x) (e x).property
    _ = Fintype.card U := (Fintype.card_coe U).symm
    _ ≤ Fintype.card (H.neighborSet x) := Fintype.card_le_of_injective liftNeighbor inj
    _ = H.degree x := H.card_neighborSet_eq_degree x

/-- Delete a vertex and a prescribed number of its neighbors. A surviving
non-neighbor loses at most one edge. A surviving neighbor can lose a second
edge only across the cut inside the link, where the selection requires slack. -/
private lemma prune_link {M n d k : ℕ} (G : SimpleGraph (Fin M))
    (hG : ¬ cycleGraph 4 ⊑ G) (hg : d + 1 ≤ G.minDegree)
    (hn : 0 < n) (hM : M = n + k + 1) (v : Fin M) (hk : k ≤ G.degree v)
    (hp : Even k ∨ ∃ a ∈ G.neighborFinset v, ∀ x ∈ G.neighborFinset v,
      G.Adj x a → d + 2 ≤ G.degree x) : d < Erdos85.f n := by
  classical
  have matching : ∀ x ∈ G.neighborFinset v, ∀ a ∈ G.neighborFinset v,
      ∀ b ∈ G.neighborFinset v, G.Adj x a → G.Adj x b → a = b := by
    intro x hx a ha b hb hxa hxb
    exact unique_common G hG ((G.mem_neighborFinset _ _).mp hx).ne
      ((G.mem_neighborFinset _ _).mp ha) hxa ((G.mem_neighborFinset _ _).mp hb) hxb
  obtain ⟨S, hS, hcard, hcut⟩ := link_selection G (G.neighborFinset v) matching
    (fun x => d + 2 ≤ G.degree x) k hk hp
  let D := insert v S
  let R := univ \ D
  have hvS : v ∉ S := fun hv => G.irrefl ((G.mem_neighborFinset _ _).mp (hS hv))
  have hD : D.card = k + 1 := by simp [D, hvS, hcard]
  have hR : R.card = n := by simp [R, Finset.card_sdiff_of_subset, hD, hM]
  refine realize_induced G hG R hn hR ?_
  intro x hx
  have hxD : x ∉ D := (mem_sdiff.mp hx).2
  have hxv : x ≠ v := fun h => hxD (h ▸ mem_insert_self ..)
  have hxS : x ∉ S := fun h => hxD (mem_insert_of_mem h)
  let A := G.neighborFinset x
  have hAS : (A ∩ S).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨hxa, hsa⟩ := mem_inter.mp ha
    obtain ⟨hxb, hsb⟩ := mem_inter.mp hb
    exact unique_common G hG hxv.symm ((G.mem_neighborFinset _ _).mp (hS hsa))
      ((G.mem_neighborFinset _ _).mp hxa) ((G.mem_neighborFinset _ _).mp (hS hsb))
      ((G.mem_neighborFinset _ _).mp hxb)
  have hsplit : A.card = (A ∩ R).card + (A ∩ D).card := by
    have eqR : A ∩ R = A \ D := by ext; simp [R]
    rw [eqR, card_sdiff_add_card_inter]
  have hmin : d + 1 ≤ A.card := hg.trans (G.minDegree_le_degree x)
  change d ≤ (A ∩ R).card
  by_cases hvA : v ∈ A
  · have hparts : A ∩ D = insert v (A ∩ S) := by ext; simp [D]; grind
    have hpartsCard : (A ∩ D).card = (A ∩ S).card + 1 := by
      rw [hparts, card_insert_of_notMem (by simp [hvS])]
    by_cases hempty : (A ∩ S).Nonempty
    · obtain ⟨y, hy⟩ := hempty
      have h := hcut x ((G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hvA).symm)
        hxS y (mem_inter.mp hy).2 ((G.mem_neighborFinset _ _).mp (mem_inter.mp hy).1)
      change d + 2 ≤ A.card at h
      omega
    · have := Finset.not_nonempty_iff_eq_empty.mp hempty
      rw [this, card_empty] at hpartsCard
      omega
  · have hparts : A ∩ D = A ∩ S := by ext; simp [D]; grind
    rw [hparts] at hsplit
    omega

/-- Failure to interpolate from a graph of one higher minimum degree forces
an even deletion size and a regular graph all of whose edges lie in triangles. -/
lemma obstruction {M n d : ℕ} (hn : 0 < n) (hlt : n < M)
    (hnear : M ≤ n + d + 2) (hmiss : Erdos85.f n ≤ d)
    (G : SimpleGraph (Fin M)) (hG : ¬ cycleGraph 4 ⊑ G) (hg : d + 1 ≤ G.minDegree) :
    Even (M - n) ∧ G.IsRegularOfDegree (d+1) ∧
      ∀ v a, G.Adj v a → ∃ x, G.Adj v x ∧ G.Adj x a := by
  classical
  let k := M - n - 1
  have hk : k ≤ d + 1 := by dsimp [k]; omega
  have heq : M = n + k + 1 := by dsimp [k]; omega
  have : NeZero M := ⟨by omega⟩
  have fail (v : Fin M) : ¬ (Even k ∨ ∃ a ∈ G.neighborFinset v,
      ∀ x ∈ G.neighborFinset v, G.Adj x a → d + 2 ≤ G.degree x) := by
    intro h
    exact hmiss.not_gt (prune_link G hG hg hn heq v
      (hk.trans (hg.trans (G.minDegree_le_degree v))) h)
  have oddk := Nat.not_even_iff_odd.mp (fun he => fail 0 (Or.inl he))
  have triangles (v a : Fin M) (hva : G.Adj v a) : ∃ x, G.Adj v x ∧ G.Adj x a := by
    by_contra hnone
    exact fail v (.inr ⟨a, (G.mem_neighborFinset _ _).mpr hva, fun x hx hxa =>
      (hnone ⟨x, (G.mem_neighborFinset _ _).mp hx, hxa⟩).elim⟩)
  refine ⟨?_, ?_, triangles⟩
  · obtain ⟨r, hr⟩ := oddk
    exact ⟨r+1, by omega⟩
  · intro x
    have hx := hg.trans (G.minDegree_le_degree x)
    by_contra hne
    have hspare : d + 2 ≤ G.degree x := by omega
    have hpos : 0 < (G.neighborFinset x).card := by
      rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨v, hv⟩ := card_pos.mp hpos
    have hvx := ((G.mem_neighborFinset _ _).mp hv).symm
    obtain ⟨a, hva, hax⟩ := triangles v x hvx
    apply fail v
    refine .inr ⟨a, (G.mem_neighborFinset _ _).mpr hva, ?_⟩
    intro y hy hya
    have hyx := unique_common G hG hva.ne ((G.mem_neighborFinset _ _).mp hy) hya.symm hvx hax
    rw [hyx]
    exact hspare

/-- In the exceptional graph the incident triangles partition every neighborhood
into pairs. In particular the exceptional regular degree is even. -/
private lemma even_degree_of_triangles {M : ℕ} (G : SimpleGraph (Fin M))
    (hG : ¬ cycleGraph 4 ⊑ G) (triangles : ∀ v a, G.Adj v a → ∃ x, G.Adj v x ∧ G.Adj x a)
    (v : Fin M) : Even (G.degree v) := by
  classical
  let L := G.induce (G.neighborSet v)
  have unit (a : G.neighborSet v) : L.degree a = 1 := by
    apply degree_eq_one_iff_existsUnique_adj.mpr
    obtain ⟨x, hvx, hxa⟩ := triangles v a a.property
    refine ⟨⟨x, hvx⟩, hxa.symm, ?_⟩
    intro y hy
    exact Subtype.ext (unique_common G hG (G.ne_of_adj a.property) y.property hy hvx hxa.symm)
  have hsum := L.sum_degrees_eq_twice_card_edges
  rw [← G.card_neighborSet_eq_degree v]
  exact ⟨L.edgeFinset.card, by simpa [unit, two_mul] using hsum⟩

/-- Fill an order below the deletion range of the next degree record.
Here the degree d has already been attained, and degree d+1 has never been
attained at any order through n+d+2. -/
def H1 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ,
    (∃ j < n, d < Erdos85.f j) →
    (∀ j ≤ n + d + 2, Erdos85.f j ≤ d + 1) →
    ∃ G : SimpleGraph (Fin n), ¬ cycleGraph 4 ⊑ G ∧ d ≤ G.minDegree

/-- The exceptional orders within the deletion range of the first witness of
degree d+1. The distance is even, and every such witness is regular with each
edge in a triangle. -/
def H2 : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ d M : ℕ,
    (∃ j < n, d < Erdos85.f j) →
    n < M → M ≤ n + d + 2 → Even (M - n) → Odd d →
    d + 1 < Erdos85.f M → (∀ j < M, Erdos85.f j ≤ d + 1) →
    (∀ G : SimpleGraph (Fin M), ¬ cycleGraph 4 ⊑ G → d + 1 ≤ G.minDegree →
      G.IsRegularOfDegree (d + 1) ∧ ∀ v a, G.Adj v a → ∃ x, G.Adj v x ∧ G.Adj x a) →
    ∃ G : SimpleGraph (Fin n), ¬ cycleGraph 4 ⊑ G ∧ d ≤ G.minDegree

theorem main : H1 → H2 → type_of% @Erdos85.erdos_85 := by
  classical
  rintro ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
  apply eventually_atTop.mpr
  refine ⟨max N₁ N₂, fun t ht => ?_⟩
  let n := t + 1
  have hn : 0 < n := Nat.succ_pos t
  have hN₁ : N₁ ≤ n := (le_max_left ..).trans (ht.trans (Nat.le_succ t))
  have hN₂ : N₂ ≤ n := (le_max_right ..).trans (ht.trans (Nat.le_succ t))
  let A := range n
  obtain ⟨j, hj, hrecord⟩ := A.exists_mem_eq_sup (by exact ⟨t, mem_range.mpr (Nat.lt_succ_self t)⟩) Erdos85.f
  have hmax (i : ℕ) (hi : i < n) : Erdos85.f i ≤ Erdos85.f j :=
    hrecord ▸ (Finset.le_sup (s := A) (f := Erdos85.f) (mem_range.mpr hi))
  change Erdos85.f t ≤ Erdos85.f n
  apply (hmax t (Nat.lt_succ_self t)).trans
  by_contra! hdrop
  let d := Erdos85.f j - 1
  have hd : Erdos85.f j = d + 1 := by dsimp [d]; omega
  have hmiss : Erdos85.f n ≤ d := by omega
  have hearlier : ∃ i < n, d < Erdos85.f i := ⟨j, mem_range.mp hj, by omega⟩
  by_cases hex : ∃ m, d + 1 < Erdos85.f m ∧ m ≤ n + d + 2
  · let M := Nat.find hex
    have ⟨hhigh, hnear⟩ := Nat.find_spec hex
    have hfirst (i : ℕ) (hi : i < M) : Erdos85.f i ≤ d + 1 := by
      by_contra! h
      exact Nat.find_min hex hi ⟨h, by change i < Nat.find hex at hi; omega⟩
    have hlt : n < M := by
      by_contra! h
      rcases lt_or_eq_of_le h with h | h
      · exact (not_lt_of_ge ((hmax M h).trans_eq hd)) hhigh
      · change d + 1 < Erdos85.f M at hhigh
        rw [h] at hhigh
        omega
    obtain ⟨G, hf, hg⟩ := lt_threshold_iff.mp hhigh
    obtain ⟨hpar, hreg, htri⟩ := obstruction hn hlt hnear hmiss G hf hg
    have : NeZero M := ⟨by omega⟩
    obtain ⟨r, hr⟩ := even_degree_of_triangles G hf htri 0
    rw [hreg 0] at hr
    have hodd : Odd d := ⟨r - 1, by omega⟩
    exact hmiss.not_gt (lt_threshold_iff.mpr (h₂ n hN₂ d M hearlier hlt hnear hpar hodd
      hhigh hfirst (fun K hK hdeg => (obstruction hn hlt hnear hmiss K hK hdeg).2)))
  · have hbound (i : ℕ) (hi : i ≤ n + d + 2) : Erdos85.f i ≤ d + 1 := by
      by_contra! h
      exact hex ⟨i, h, hi⟩
    exact hmiss.not_gt (lt_threshold_iff.mpr (h₁ n hN₁ d hearlier hbound))

end OMA.R_Erdos85_erdos_85_R1
