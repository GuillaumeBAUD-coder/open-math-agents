import FormalConjectures.WrittenOnTheWallII.GraphConjecture189

/-!
Two vertices at distance five cannot both have degree at least the second-smallest
degree. Along a five-edge geodesic, weighted counts of closed neighborhoods and
even-distance sets first locate a low-degree vertex, then exclude both middle positions.
A six-edge geodesic would produce two disjoint pairs needing a low-degree vertex.

The remaining cases also satisfy the neighborhood condition for independent sets.
When the condition fails, a complete bipartite spanning subgraph after removal of one
vertex provides an alternating Hamiltonian path. The diameter-at-most-two argument is
the degree-sum case of Easwar and Johari, arXiv:2609.11719.
-/

open SimpleGraph
open scoped BigOperators

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

-- In diameter three the only nonzero even distance is two.
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → G.diam = 3 →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 4 ≤ G.diam → G.diam ≤ 5 →
    (∀ a b, G.dist a b = 5 →
      G.degree a < G.secondSmallestDegree ∨ G.degree b < G.secondSmallestDegree) →
    G.minDegree + secondSmallestDegree G + 1 < Fintype.card V →
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    (∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))

lemma geodesic (hc : G.Connected) {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b)
    (i j : ℕ) (hle : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hseg := dist_le ((p.drop i).take (j-i))
  rw [Walk.take_length, Walk.drop_length, Walk.drop_getVert, Nat.add_sub_of_le hle] at hseg
  have hfirst := dist_le (p.take i)
  have hlast := dist_le (p.drop j)
  rw [Walk.take_length] at hfirst
  rw [Walk.drop_length] at hlast
  have ht1 := hc.dist_triangle (u := a) (v := p.getVert i) (w := p.getVert j)
  have ht2 := hc.dist_triangle (u := a) (v := p.getVert j) (w := b)
  omega

lemma order_bound [Nonempty V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) :
    Fintype.card V ≤ (G.minDegree + 1) * (G.secondSmallestDegree + 1) := by
  classical
  obtain ⟨r,hr⟩ := G.exists_minimal_degree_vertex
  let B := insert r (G.neighborFinset r)
  let E (x : V) := Finset.univ.filter (fun y => Even (G.dist x y))
  have hcover : Finset.univ ⊆ B.biUnion E := by
    intro x _
    apply Finset.mem_biUnion.mpr
    by_cases h : Even (G.dist r x)
    · exact ⟨r, Finset.mem_insert_self _ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist r x
      rw [Nat.even_iff] at h
      have hl : 1 ≤ p.length := by omega
      have ha := geodesic hc p hp 0 1 (by decide) hl
      rw [p.getVert_zero] at ha
      have hx := geodesic hc p hp 1 p.length hl (le_refl _)
      rw [p.getVert_length] at hx
      refine ⟨p.getVert 1, Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr
        (dist_eq_one_iff_adj.mp ha)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [Nat.even_iff]
      omega
  have hsize : B.card = G.minDegree + 1 := by
    simp only [B, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self _),
      card_neighborFinset_eq_degree, hr]
  calc
    Fintype.card V = (Finset.univ : Finset V).card := Finset.card_univ.symm
    _ ≤ (B.biUnion E).card := Finset.card_le_card hcover
    _ ≤ B.card * (G.secondSmallestDegree + 1) := Finset.card_biUnion_le_card_mul _ _ _ fun x _ =>
      by simpa only [E,distEven,Nat.add_comm 1] using hb x
    _ = _ := by rw [hsize]

private def closedIndicator (n : ℕ) : ℕ := if n ≤ 1 then 1 else 0

private def evenIndicator (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 0

lemma dist_le_one_count [DecidableRel G.Adj] (hc : G.Connected) (x : V) :
    (∑ y : V, (if G.dist x y ≤ 1 then 1 else 0 : ℕ)) = G.degree x + 1 := by
  classical
  rw [← Finset.card_filter]
  have he : Finset.univ.filter (fun y => G.dist x y ≤ 1) = insert x (G.neighborFinset x) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,mem_neighborFinset]
    constructor
    · intro hd
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with h | h
      · exact Or.inl ((hc.dist_eq_zero_iff.mp h).symm)
      · exact Or.inr (dist_eq_one_iff_adj.mp h)
    · rintro (rfl | h)
      · simp
      · exact (dist_eq_one_iff_adj.mpr h).le
  rw [he,Finset.card_insert_of_notMem (G.notMem_neighborFinset_self _), card_neighborFinset_eq_degree]

section Five
variable (hc : G.Connected) (v : ℕ → V)
variable (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i)

include hc hg in
lemma profile_bounds (y : V) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) :
    G.dist (v i) y ≤ G.dist (v j) y + (j-i) ∧
    G.dist (v j) y ≤ G.dist (v i) y + (j-i) ∧ j-i ≤ G.dist (v i) y + G.dist (v j) y := by
  have h₁ := hc.dist_triangle (u := v i) (v := v j) (w := y)
  have h₂ := hc.dist_triangle (u := v j) (v := v i) (w := y)
  have h₃ := hc.dist_triangle (u := v i) (v := y) (w := v j)
  rw [SimpleGraph.dist_comm (u := v j) (v := v i)] at h₂
  rw [SimpleGraph.dist_comm (u := y) (v := v j)] at h₃
  rw [hg i j hi hj] at h₁ h₂ h₃
  omega

private lemma sum_evenIndicator [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (x : V) :
    ∑ y : V, evenIndicator (G.dist x y) ≤ G.secondSmallestDegree + 1 := by
  classical
  simpa only [evenIndicator,distEven,Finset.card_filter,Nat.even_iff] using hb x

-- A vertex x near the left endpoint and at distance three from both middle vertices
-- has low degree. Its closed neighborhood and those of v₃ and v₅ require more total
-- incidences than the even-distance sets of v₀, v₁ and v₂ can supply.
include hc hg in
lemma low_bad_left [DecidableRel G.Adj]
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs3 : G.secondSmallestDegree ≤ G.degree (v 3))
    (hs5 : G.secondSmallestDegree ≤ G.degree (v 5))
    (x : V) (hx0 : G.dist (v 0) x ≤ 1)
    (hx2 : G.dist (v 2) x = 3) (hx3 : G.dist (v 3) x = 3) : G.degree x < G.secondSmallestDegree := by
  classical
  have h5x := profile_bounds hc v hg x 0 5 (by decide) (by decide)
  norm_num1 at h5x
  let B (a y : V) := closedIndicator (G.dist a y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  have hpoint (y : V) : B x y + B (v 3) y + B (v 5) y ≤ E 0 y + E 1 y + E 2 y := by
    have h01 := profile_bounds hc v hg y 0 1 (by decide) (by decide)
    have h12 := profile_bounds hc v hg y 1 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h01 h12 h03 h05 h23 h25 h35
    have h0 := hc.dist_triangle (u := v 0) (v := x) (w := y)
    have h2 := hc.dist_triangle (u := v 2) (v := y) (w := x)
    have h3 := hc.dist_triangle (u := v 3) (v := y) (w := x)
    have h5 := hc.dist_triangle (u := v 5) (v := y) (w := x)
    rw [SimpleGraph.dist_comm (u := y) (v := x)] at h2 h3 h5
    dsimp only [B,E,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have hstrict : B x (v 0) + B (v 3) (v 0) + B (v 5) (v 0) <
      E 0 (v 0) + E 1 (v 0) + E 2 (v 0) := by
    rw [SimpleGraph.dist_comm] at hx0
    have h1 := hg 0 1 (by decide) (by decide)
    have h2 := hg 0 2 (by decide) (by decide)
    have h3 := hg 0 3 (by decide) (by decide)
    have h5 := hg 0 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at h1 h2 h3 h5
    norm_num [B,E,closedIndicator,evenIndicator,hx0,h1,h2,h3,h5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B x y + B (v 3) y + B (v 5) y) (g := fun y => E 0 y + E 1 y + E 2 y)
    (fun y _ => hpoint y) ⟨v 0,Finset.mem_univ _,hstrict⟩
  have hB (a : V) : ∑ y : V, B a y = G.degree a + 1 := dist_le_one_count hc a
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  omega

include hc hg in
lemma exists_bad [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs0 : G.secondSmallestDegree ≤ G.degree (v 0)) (hs5 : G.secondSmallestDegree ≤ G.degree (v 5)) :
    ∃ x, (G.dist (v 0) x ≤ 1 ∨ G.dist (v 5) x ≤ 1) ∧
      G.dist (v 2) x = 3 ∧ G.dist (v 3) x = 3 := by
  classical
  let B (i : ℕ) (y : V) := closedIndicator (G.dist (v i) y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  by_contra hno
  have hpoint (y : V) : B 0 y + B 5 y ≤ E 2 y + E 3 y := by
    have hneg : ¬((G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1) ∧
        G.dist (v 2) y = 3 ∧ G.dist (v 3) y = 3) := fun h => hno ⟨y,h⟩
    have h02 := profile_bounds hc v hg y 0 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h02 h03 h05 h23 h25 h35
    dsimp only [B,E,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have hstrict : B 0 (v 2) + B 5 (v 2) < E 2 (v 2) + E 3 (v 2) := by
    have h0 := hg 0 2 (by decide) (by decide)
    have h3 := hg 2 3 (by decide) (by decide)
    have h5 := hg 2 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at h3 h5
    norm_num [B,E,closedIndicator,evenIndicator,h0,h3,h5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B 0 y + B 5 y) (g := fun y => E 2 y + E 3 y)
    (fun y _ => hpoint y) ⟨v 2,Finset.mem_univ _,hstrict⟩
  have hB (i : ℕ) : ∑ y : V, B i y = G.degree (v i) + 1 := dist_le_one_count hc (v i)
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he2 := he 2
  have he3 := he 3
  omega

-- With four high-degree path vertices, a closed endpoint neighborhood contains a
-- vertex at distance three from both middle vertices. Otherwise the two even-distance
-- sets at v₂ and v₃ cover both closed endpoint neighborhoods with strict excess.
include hc hg in
lemma five_low [DecidableRel G.Adj] (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1)
    (hs : ∀ i ∈ ([0,2,3,5] : List ℕ), G.secondSmallestDegree ≤ G.degree (v i)) :
    ∃ x, G.degree x < G.secondSmallestDegree ∧ G.dist (v 2) x = 3 ∧ G.dist (v 3) x = 3 := by
  obtain ⟨x,hnear,hx2,hx3⟩ := exists_bad hc v hg hb (hs 0 (by decide)) (hs 5 (by decide))
  refine ⟨x,?_,hx2,hx3⟩
  rcases hnear with hn | hn
  · exact low_bad_left hc v hg hb (hs 3 (by decide)) (hs 5 (by decide)) x hn hx2 hx3
  · let w (i : ℕ) := v (5-i)
    have hw (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
      dsimp only [w]
      rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
      omega
    exact low_bad_left hc w hw hb (hs 2 (by decide)) (hs 0 (by decide)) x hn hx3 hx2

end Five

-- Every geodesic of length five meets the unique low-degree vertex at an endpoint
-- or in one of its two middle positions. The strict excess at both middle vertices
-- cannot be offset by a single low-degree vertex elsewhere.
lemma five_hits_low [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (v : ℕ → V)
    (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i) :
    ∃ i ∈ ([0,2,3,5] : List ℕ), G.degree (v i) < G.secondSmallestDegree := by
  classical
  by_contra! hs
  obtain ⟨x,hx,_,_⟩ := five_low hc v hg hb hs
  have bad (y : V) (hn : G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1)
      (hy2 : G.dist (v 2) y = 3) (hy3 : G.dist (v 3) y = 3) : y = x := by
    have hy : G.degree y < G.secondSmallestDegree := by
      rcases hn with hn | hn
      · exact low_bad_left hc v hg hb (hs 3 (by decide)) (hs 5 (by decide)) y hn hy2 hy3
      · let w (i : ℕ) := v (5-i)
        have hw (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
          dsimp only [w]
          rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
          omega
        exact low_bad_left hc w hw hb (hs 2 (by decide)) (hs 0 (by decide)) y hn hy3 hy2
    by_contra h
    have h' := degree_pair (G := G) y x h
    omega
  let B (i : ℕ) (y : V) := closedIndicator (G.dist (v i) y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  let I (a y : V) : ℕ := if a = y then 1 else 0
  have hp (y : V) : B 0 y + B 5 y + I (v 2) y + I (v 3) y ≤ E 2 y + E 3 y + I x y := by
    have h02 := profile_bounds hc v hg y 0 2 (by decide) (by decide)
    have h03 := profile_bounds hc v hg y 0 3 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h25 := profile_bounds hc v hg y 2 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg y 3 5 (by decide) (by decide)
    norm_num1 at h02 h03 h05 h23 h25 h35
    by_cases hy2 : v 2 = y
    · have hdist : G.dist (v 2) y = 0 := by rw [hy2]; simp
      have hne : v 3 ≠ y := by
        intro h
        have h' : G.dist (v 3) y = 0 := by rw [h]; simp
        omega
      dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    by_cases hy3 : v 3 = y
    · have hdist : G.dist (v 3) y = 0 := by rw [hy3]; simp
      dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    by_cases hyx : x = y
    · dsimp only [B,E,I,closedIndicator,evenIndicator]
      split_ifs <;> omega
    have hno : ¬((G.dist (v 0) y ≤ 1 ∨ G.dist (v 5) y ≤ 1) ∧
        G.dist (v 2) y = 3 ∧ G.dist (v 3) y = 3) := by
      rintro ⟨hn,h2,h3⟩
      exact hyx (bad y hn h2 h3).symm
    dsimp only [B,E,I,closedIndicator,evenIndicator]
    split_ifs <;> omega
  have ht := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun y _ => hp y)
  have hB (i : ℕ) : ∑ y : V, B i y = G.degree (v i) + 1 := dist_le_one_count hc (v i)
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  have hI (a : V) : ∑ y : V, I a y = 1 := by simp [I]
  simp only [Finset.sum_add_distrib,hB,hI] at ht
  have he2 := he 2
  have he3 := he 3
  have hs0 := hs 0 (by decide)
  have hs5 := hs 5 (by decide)
  omega

section FiveEndpoint

variable [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (v : ℕ → V)
    (hg : ∀ i j : ℕ, i ≤ j → j ≤ 5 → G.dist (v i) (v j) = j-i)

include hc hb hg in
lemma no_triangle_at_low_middle (hs : G.degree (v 2) < G.secondSmallestDegree) (z : V) :
    ¬(G.dist (v 1) z = 1 ∧ G.dist (v 2) z = 1 ∧ G.dist (v 3) z = 1) := by
  rintro ⟨h1,h2,h3⟩
  let w (i : ℕ) := if i = 2 then z else v i
  have hz (i : ℕ) (hi : i ≤ 5) (hi2 : i ≠ 2) :
      G.dist (v i) z = if i ≤ 2 then 2-i else i-2 := by
    have h01 := profile_bounds hc v hg z 0 1 (by decide) (by decide)
    have h03 := profile_bounds hc v hg z 0 3 (by decide) (by decide)
    have h14 := profile_bounds hc v hg z 1 4 (by decide) (by decide)
    have h34 := profile_bounds hc v hg z 3 4 (by decide) (by decide)
    have h15 := profile_bounds hc v hg z 1 5 (by decide) (by decide)
    have h35 := profile_bounds hc v hg z 3 5 (by decide) (by decide)
    norm_num1 at h01 h03 h14 h34 h15 h35
    interval_cases i <;> norm_num1 <;> simp only [if_true,if_false] <;> omega
  have hw (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
    by_cases hi2 : i = 2
    · subst i
      by_cases hj2 : j = 2
      · subst j
        simp
      · have h := hz j hj hj2
        rw [SimpleGraph.dist_comm] at h
        simp only [w,if_pos rfl,if_neg hj2]
        rw [h,if_neg (by omega)]
    · by_cases hj2 : j = 2
      · subst j
        simpa only [w,if_pos rfl,if_neg hi2,if_pos hij] using hz i (by omega) hi2
      · simpa only [w,if_neg hi2,if_neg hj2] using hg i j hij hj
  obtain ⟨i,hi,hl⟩ := five_hits_low hc hb w hw
  have hne : v 2 ≠ w i := by
    by_cases hi2 : i = 2
    · subst i
      simp only [w,if_pos rfl]
      intro he
      rw [he,SimpleGraph.dist_self] at h2
      omega
    · have hi5 : i ≤ 5 := by simp at hi; omega
      simp only [w,if_neg hi2]
      intro he
      rcases lt_or_gt_of_ne hi2 with h | h
      · have hh := hg i 2 h.le (by decide)
        rw [he,SimpleGraph.dist_self] at hh
        omega
      · have hh := hg 2 i h.le hi5
        rw [he,SimpleGraph.dist_self] at hh
        omega
  have h := degree_pair (G := G) _ _ hne
  omega

private lemma right_cost (d0 d1 d2 d3 d4 d5 t : ℕ)
    (h01 : d0 ≤ d1+1 ∧ d1 ≤ d0+1) (h12 : d1 ≤ d2+1 ∧ d2 ≤ d1+1)
    (h23 : d2 ≤ d3+1 ∧ d3 ≤ d2+1) (h34 : d3 ≤ d4+1 ∧ d4 ≤ d3+1)
    (h45 : d4 ≤ d5+1 ∧ d5 ≤ d4+1) (h05 : 5 ≤ d0+d5)
    (ht : ¬(d1 = 1 ∧ d2 = 1 ∧ d3 = 1)) (h3 : 3 ≤ d3+t) (h5 : d5 ≤ t+1) :
    closedIndicator d0 + closedIndicator d1 + closedIndicator d3 + closedIndicator t ≤
      evenIndicator d2 + evenIndicator d3 + evenIndicator d4 + evenIndicator d5 := by
  unfold closedIndicator evenIndicator
  split_ifs <;> omega

include hc hg hb in
lemma bad_right_middle (hs2 : G.degree (v 2) < G.secondSmallestDegree)
    (hs : ∀ i ∈ ([0,1,3] : List ℕ), G.secondSmallestDegree ≤ G.degree (v i))
    (x : V) (hx5 : G.dist (v 5) x ≤ 1) (hx3 : G.dist (v 3) x = 3) :
    G.degree x < G.secondSmallestDegree := by
  classical
  let B (a y : V) := closedIndicator (G.dist a y)
  let E (i : ℕ) (y : V) := evenIndicator (G.dist (v i) y)
  have hp (y : V) : B (v 0) y + B (v 1) y + B (v 3) y + B x y ≤
      E 2 y + E 3 y + E 4 y + E 5 y := by
    have h01 := profile_bounds hc v hg y 0 1 (by decide) (by decide)
    have h12 := profile_bounds hc v hg y 1 2 (by decide) (by decide)
    have h23 := profile_bounds hc v hg y 2 3 (by decide) (by decide)
    have h34 := profile_bounds hc v hg y 3 4 (by decide) (by decide)
    have h45 := profile_bounds hc v hg y 4 5 (by decide) (by decide)
    have h05 := profile_bounds hc v hg y 0 5 (by decide) (by decide)
    norm_num1 at h01 h12 h23 h34 h45 h05
    have h3 := hc.dist_triangle (u := v 3) (v := y) (w := x)
    rw [SimpleGraph.dist_comm (u := y) (v := x)] at h3
    have h5 := hc.dist_triangle (u := v 5) (v := x) (w := y)
    exact right_cost _ _ _ _ _ _ _ ⟨h01.1,h01.2.1⟩ ⟨h12.1,h12.2.1⟩
      ⟨h23.1,h23.2.1⟩ ⟨h34.1,h34.2.1⟩ ⟨h45.1,h45.2.1⟩ h05.2.2
      (no_triangle_at_low_middle hc hb v hg hs2 y) (by omega) (by omega)
  have hstrict : B (v 0) (v 5) + B (v 1) (v 5) + B (v 3) (v 5) + B x (v 5) <
      E 2 (v 5) + E 3 (v 5) + E 4 (v 5) + E 5 (v 5) := by
    have h0 := hg 0 5 (by decide) (by decide)
    have h1 := hg 1 5 (by decide) (by decide)
    have h2 := hg 2 5 (by decide) (by decide)
    have h3 := hg 3 5 (by decide) (by decide)
    have h4 := hg 4 5 (by decide) (by decide)
    rw [SimpleGraph.dist_comm] at hx5
    norm_num [B,E,closedIndicator,evenIndicator,h0,h1,h2,h3,h4,hx5]
  have ht := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
    (f := fun y => B (v 0) y + B (v 1) y + B (v 3) y + B x y)
    (g := fun y => E 2 y + E 3 y + E 4 y + E 5 y)
    (fun y _ => hp y) ⟨v 5,Finset.mem_univ _,hstrict⟩
  have hB (a : V) : ∑ y : V, B a y = G.degree a + 1 := dist_le_one_count hc a
  have he (i : ℕ) : ∑ y : V, E i y ≤ G.secondSmallestDegree + 1 := sum_evenIndicator hb (v i)
  simp only [Finset.sum_add_distrib,hB] at ht
  have he2 := he 2
  have he3 := he 3
  have he4 := he 4
  have he5 := he 5
  have hs0 := hs 0 (by decide)
  have hs1 := hs 1 (by decide)
  have hs3 := hs 3 (by decide)
  omega

include hc hg hb in
lemma middle_cannot_be_low (hs2 : G.degree (v 2) < G.secondSmallestDegree) : False := by
  have hs (i : ℕ) (hi : i ≤ 5) (hi2 : i ≠ 2) : G.secondSmallestDegree ≤ G.degree (v i) := by
    have hne : v 2 ≠ v i := by
      intro he
      rcases lt_or_gt_of_ne hi2 with h | h
      · have hh := hg i 2 h.le (by decide)
        rw [he,SimpleGraph.dist_self] at hh
        omega
      · have hh := hg 2 i h.le hi
        rw [he,SimpleGraph.dist_self] at hh
        omega
    exact (degree_pair _ _ hne).resolve_left (by omega)
  obtain ⟨x,hn,h2,h3⟩ := exists_bad hc v hg hb (hs 0 (by decide) (by decide)) (hs 5 (by decide) (by decide))
  have hx : G.degree x < G.secondSmallestDegree := by
    rcases hn with h | h
    · exact low_bad_left hc v hg hb (hs 3 (by decide) (by decide)) (hs 5 (by decide) (by decide)) x h h2 h3
    · refine bad_right_middle hc hb v hg hs2 ?_ x h h3
      intro i hi
      simp at hi
      exact hs i (by omega) (by omega)
  have hne : v 2 ≠ x := by
    intro he
    rw [he,SimpleGraph.dist_self] at h2
    omega
  have h := degree_pair (G := G) _ _ hne
  omega

include hc hg hb in
lemma geodesic_five_endpoints :
    G.degree (v 0) < G.secondSmallestDegree ∨ G.degree (v 5) < G.secondSmallestDegree := by
  obtain ⟨i,hi,hl⟩ := five_hits_low hc hb v hg
  simp at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact Or.inl hl
  · exact (middle_cannot_be_low hc hb v hg hl).elim
  · let w (i : ℕ) := v (5-i)
    have hw (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) : G.dist (w i) (w j) = j-i := by
      dsimp only [w]
      rw [SimpleGraph.dist_comm, hg _ _ (by omega) (by omega)]
      omega
    exact (middle_cannot_be_low hc hb w hw hl).elim
  · exact Or.inr hl

end FiveEndpoint

lemma five_endpoints [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1) (a b : V) (hd : G.dist a b = 5) :
    G.degree a < G.secondSmallestDegree ∨ G.degree b < G.secondSmallestDegree := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  have hg (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 5) :
      G.dist (p.getVert i) (p.getVert j) = j-i := geodesic hc p hp _ _ hi (by omega)
  have h := geodesic_five_endpoints hc hb p.getVert hg
  rw [p.getVert_zero,p.getVert_of_length_le (by omega : p.length ≤ 5)] at h
  exact h

lemma diameter_le_five [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (hb : ∀ x, distEven G x ≤ 1 + G.secondSmallestDegree) : G.diam ≤ 5 := by
  have hb' : ∀ x, distEven G x ≤ G.secondSmallestDegree + 1 := by
    simpa only [Nat.add_comm 1] using hb
  by_contra! h
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  let v := p.getVert
  have hg (i j : ℕ) (hi : i ≤ j) (hj : j ≤ 6) :
      G.dist (v i) (v j) = j-i := geodesic hc p hp _ _ hi (by omega)
  have vne (i j : ℕ) (hi : i < j) (hj : j ≤ 6) : v i ≠ v j := by
    intro he
    have h := hg i j hi.le hj
    rw [he,SimpleGraph.dist_self] at h
    omega
  have h05 := five_endpoints hc hb' _ _ (hg 0 5 (by decide) (by decide))
  have h16 := five_endpoints hc hb' _ _ (hg 1 6 (by decide) (by decide))
  have h01 := degree_pair (G := G) _ _ (vne 0 1 (by decide) (by decide))
  have h06 := degree_pair (G := G) _ _ (vne 0 6 (by decide) (by decide))
  have h15 := degree_pair (G := G) _ _ (vne 1 5 (by decide) (by decide))
  have h56 := degree_pair (G := G) _ _ (vne 5 6 (by decide) (by decide))
  omega

lemma rot {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

-- The path rotation and crossing-chord argument below adapts the repository's
-- Dirac formalization by philipsaint to the degree-sum criterion for traceability.
lemma trace_of_sum [Nontrivial V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ x y, x ≠ y → Fintype.card V ≤ G.degree x + G.degree y + 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨v0⟩ := (inferInstance : Nonempty V)
  have hnn : 2 ≤ n := Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  set M := Nat.findGreatest PP n
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec (by omega) h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest (by omega) h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
    omega
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  have hfinish (he : m = n) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
    let p := Walk.ofSupport l hl_ne hlch
    have hp : p.IsPath := Walk.IsPath.mk' (by simpa [p, Walk.support_ofSupport] using hlnd)
    exact ⟨_, _, p, Walk.isHamiltonian_iff_isPath_and_length_eq.mpr
      ⟨hp, by simpa [p, Walk.length_ofSupport, ← hm, he, hn]⟩⟩
  by_cases hmn' : m = n
  · exact hfinish hmn'
  obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial v0
  have htwo : 2 ≤ m := by
    have hh := hmax [v0,y] (by simp [hy.ne]) (by simpa using hy)
    simpa [m,hlM] using hh
  have hneEnds : q0 ≠ z := by
    intro he
    have ieq : l[0]'(by omega) = l[m-1]'(by omega) := by
      rw [← List.getD_eq_getElem (d := q0), ← List.getD_eq_getElem (d := q0), hq0, hz]
      exact he
    have hh := hlnd.getElem_inj_iff.mp ieq
    omega
  -- The two index sets of possible crossing chords.
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hsum := hdeg q0 z hneEnds
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at this
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  -- every vertex lies on the path
  have hall : ∀ w, w ∈ l := by
    intro w
    by_contra hw
    obtain ⟨p⟩ := hconn q0 w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
    have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
    have hnd' : (d.snd :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (d.snd :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro y hy
      rw [hc'h] at hy
      simp at hy
      subst hy
      exact (d.adj).symm
    have := hmax _ hnd' hch'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hmn' : m = n := by
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hall w]
    have h2 := List.toFinset_card_of_nodup hlnd
    rw [h1, Finset.card_univ] at h2
    omega
  exact hfinish hmn'


lemma even_count_of_small_diameter [Nonempty V] (hc : G.Connected) (hd : G.diam ≤ 2) [DecidableRel G.Adj]
    (x : V) : distEven G x + G.degree x = Fintype.card V := by
  classical
  have hmem (y : V) : Even (G.dist x y) ↔ ¬ G.Adj x y := by
    have hb := G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := x) (v := y)
    rw [← dist_eq_one_iff_adj, Nat.even_iff]
    omega
  have hfilter : (Finset.univ.filter fun y => Even (G.dist x y)) = (G.neighborFinset x)ᶜ := by
    ext y
    simp [hmem,mem_neighborFinset]
  rw [distEven, hfilter, ← G.card_neighborFinset_eq_degree x, Finset.card_compl]
  have hh := (G.neighborFinset x).card_le_univ
  omega

lemma trace_small [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected) (hd : G.diam ≤ 2)
    (h : ∀ x, distEven G x ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply trace_of_sum hc
  intro x y hxy
  have hx := even_count_of_small_diameter hc hd x
  have hy := even_count_of_small_diameter hc hd y
  have hpx := h x
  have hpy := h y
  have hs := degree_pair (G := G) x y hxy
  omega

-- If one vertex sees s+1 members of an independent set, these exhaust the even-distance
-- vertices of each member. Connectivity then forces the set to dominate the graph.
lemma saturates (hc : G.Connected) (s : ℕ) (hb : ∀ x, distEven G x ≤ s+1)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) [DecidableRel G.Adj]
    (c : V) (hh : s+1 ≤ (I.filter (G.Adj c)).card) :
    (I.filter (G.Adj c)) = I ∧ I.card ≤ s+1 ∧ ∀ x, x ∈ I ∨ ∃ a ∈ I, G.Adj a x := by
  classical
  let Q := I.filter (G.Adj c)
  have hQ (q : V) (hq : q ∈ Q) : q ∈ I ∧ G.Adj c q := Finset.mem_filter.mp hq
  have hsat (q : V) (hq : q ∈ Q) :
      Finset.univ.filter (fun x => Even (G.dist q x)) = Q := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hqz : q = z
      · simp [hqz]
      · have hd := hc.one_lt_dist_of_ne_of_not_adj hqz (hI (hQ q hq).1 (hQ z hz).1 hqz)
        have htri := hc.dist_triangle (u := q) (v := c) (w := z)
        rw [dist_eq_one_iff_adj.mpr (hQ q hq).2.symm,dist_eq_one_iff_adj.mpr (hQ z hz).2] at htri
        rw [Nat.even_iff]
        omega
    · exact (hb q).trans hh
  obtain ⟨q,hq⟩ : Q.Nonempty := Finset.card_pos.mp (by change 0 < (I.filter _).card; omega)
  let T : Set V := {x | x ∈ Q ∨ ∃ a ∈ Q, G.Adj a x}
  have hall (x : V) : x ∈ T := by
    by_contra hx
    obtain ⟨p⟩ := hc q x
    obtain ⟨e,_,hf,ht⟩ := p.exists_boundary_dart T (Or.inl hq) hx
    apply ht
    rcases hf with hf | ⟨a,ha,hadj⟩
    · exact Or.inr ⟨e.fst,hf,e.adj⟩
    · by_cases hmem : e.snd ∈ Q
      · exact Or.inl hmem
      · have hn : ¬ Even (G.dist a e.snd) := by
          intro h
          apply hmem
          rw [← hsat a ha]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        have htri := hc.dist_triangle (u := a) (v := e.fst) (w := e.snd)
        rw [dist_eq_one_iff_adj.mpr hadj, dist_eq_one_iff_adj.mpr e.adj] at htri
        rw [Nat.even_iff] at hn
        exact Or.inr ⟨a,ha,dist_eq_one_iff_adj.mp (by omega)⟩
  have hEq : Q = I := by
    apply Finset.Subset.antisymm (Finset.filter_subset ..)
    intro x hx
    rcases hall x with h | ⟨a,ha,hax⟩
    · exact h
    · exact False.elim (hI (hQ a ha).1 hx hax.ne hax)
  have hbound := hb q
  unfold distEven at hbound
  rw [hsat q hq, hEq] at hbound
  refine ⟨hEq, hbound, ?_⟩
  intro x
  simpa [T,hEq] using hall x

lemma independent_hall_large [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (h : ∀ x, distEven G x ≤ secondSmallestDegree G + 1)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V))
    (hlarge : secondSmallestDegree G + 1 < I.card) :
    I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card := by
  classical
  let s := secondSmallestDegree G
  let N := Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)
  have hsub (a : V) (ha : a ∈ I) : G.neighborFinset a ⊆ N := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a,ha,(G.mem_neighborFinset a x).mp hx⟩
  have hsmall : ¬ I.card ≤ s+1 := by exact not_le.mpr hlarge
  have hnbr (x : V) : (I.filter (G.Adj x)).card ≤ s := by
    by_contra! hh
    exact hsmall (saturates hc s h I hI x hh).2.1
  obtain ⟨u,hu,hother⟩ : ∃ u ∈ I, ∀ y ∈ I.erase u, s ≤ G.degree y := by
    by_cases hall : ∀ u ∈ I, s ≤ G.degree u
    · obtain ⟨u,hu⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨u,hu,fun y hy => hall y (Finset.mem_of_mem_erase hy)⟩
    · push Not at hall
      obtain ⟨u,hu,hbad⟩ := hall
      exact ⟨u,hu,fun y hy => (degree_pair u y (Finset.ne_of_mem_erase hy).symm).resolve_left
        (by exact not_le.mpr hbad)⟩
  have hrow (a : V) (ha : a ∈ I) :
      G.degree a = ∑ x ∈ N, (if G.Adj a x then 1 else 0 : ℕ) := by
    rw [← Finset.card_filter, ← card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp only [Finset.mem_filter,mem_neighborFinset]
    exact ⟨fun hy => ⟨hsub a ha ((G.mem_neighborFinset a y).mpr hy),hy⟩, And.right⟩
  have hsum : ∑ a ∈ I, G.degree a ≤ N.card*s := by
    calc
      _ = ∑ a ∈ I, ∑ x ∈ N, (if G.Adj a x then 1 else 0 : ℕ) :=
        Finset.sum_congr rfl hrow
      _ = ∑ x ∈ N, (I.filter (G.Adj x)).card := by
        rw [Finset.sum_comm]
        simp only [Finset.card_filter,adj_comm]
      _ ≤ ∑ _ ∈ N, s := Finset.sum_le_sum fun x _ => hnbr x
      _ = N.card*s := by simp
  have hlo : (I.card-1)*s + G.degree u ≤ ∑ a ∈ I, G.degree a := by
    rw [← Finset.sum_erase_add _ _ hu]
    apply Nat.add_le_add_right
    calc
      _ = ∑ _ ∈ I.erase u,s := by simp [Finset.card_erase_of_mem hu]
      _ ≤ _ := Finset.sum_le_sum hother
  have hp := hc.preconnected.degree_pos_of_nontrivial u
  change I.card ≤ N.card
  by_contra! hgt
  have hmul : N.card*s ≤ (I.card-1)*s := Nat.mul_le_mul_right _ (by omega)
  omega



lemma alternating_chain [DecidableRel G.Adj] (L R : Finset V) (hsize : L.card = R.card)
    (hdis : Disjoint L R) (hc : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y) (a : V) (ha : a ∈ L) :
    ∃ l : List V, l.head? = some a ∧ l.Nodup ∧ l.IsChain G.Adj ∧ l.toFinset = L ∪ R := by
  classical
  induction R using Finset.strongInductionOn generalizing L a with
  | _ R ih =>
    obtain ⟨b,hb⟩ : R.Nonempty := Finset.card_pos.mp
      (by rw [← hsize]; exact Finset.card_pos.mpr ⟨a,ha⟩)
    have hab := hc a ha b hb
    let L' := L.erase a
    let R' := R.erase b
    have hlr : L'.card = R'.card := by simp [L',R',Finset.card_erase_of_mem,ha,hb,hsize]
    have hsplit : insert a (insert b (L' ∪ R')) = L ∪ R := by
      ext x
      simp [L',R']
      grind
    by_cases hem : L' = ∅
    · have hr' : R' = ∅ := Finset.card_eq_zero.mp (by simp [← hlr,hem])
      refine ⟨[a,b],rfl,by simp [hab.ne],by simpa using hab,?_⟩
      simpa [hem,hr'] using hsplit
    · obtain ⟨c,hc'⟩ := Finset.nonempty_iff_ne_empty.mpr hem
      have hrec := ih R' (Finset.erase_ssubset hb) L' hlr
        (hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
        (fun x hx y hy => hc x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) c hc'
      obtain ⟨l,hhead,hnd,hch,hset⟩ := hrec
      have habs : a ∉ l := by
        intro hh
        have : a ∈ L' ∪ R' := hset ▸ List.mem_toFinset.mpr hh
        rcases Finset.mem_union.mp this with hL | hR
        · exact Finset.notMem_erase a L hL
        · exact Finset.disjoint_left.mp hdis ha (Finset.mem_of_mem_erase hR)
      have hbbs : b ∉ l := by
        intro hh
        have : b ∈ L' ∪ R' := hset ▸ List.mem_toFinset.mpr hh
        rcases Finset.mem_union.mp this with hL | hR
        · exact Finset.disjoint_left.mp hdis (Finset.mem_of_mem_erase hL) hb
        · exact Finset.notMem_erase b R hR
      refine ⟨a::b::l,rfl, by simp [hab.ne,habs,hbbs,hnd], ?_,?_⟩
      · apply List.isChain_cons.mpr
        refine ⟨by simpa using hab, List.isChain_cons.mpr ⟨?_,hch⟩⟩
        intro y hy
        have he : y = c := by simpa [hhead,eq_comm] using hy
        subst y
        exact (hc c (Finset.mem_of_mem_erase hc') b hb).symm
      · simpa [hset] using hsplit

lemma trace_of_hall_deficit [Nontrivial V] [DecidableRel G.Adj] (hc : G.Connected)
    (h : ∀ x, distEven G x ≤ secondSmallestDegree G + 1)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V))
    (hviol : (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card < I.card) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let s := secondSmallestDegree G
  let N := Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)
  change N.card < I.card at hviol
  have hsub (a : V) (ha : a ∈ I) : G.neighborFinset a ⊆ N := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,(G.mem_neighborFinset a x).mp hx⟩
  have hsmall : I.card ≤ s+1 := by
    by_contra! hbig
    exact (not_le.mpr hviol) (independent_hall_large hc h I hI hbig)
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u,hu,hother⟩ : ∃ u ∈ I, ∀ y ∈ I.erase u, s ≤ G.degree y := by
    by_cases hall : ∀ u ∈ I, s ≤ G.degree u
    · obtain ⟨u,hu⟩ := hne
      exact ⟨u,hu,fun y hy => hall y (Finset.mem_of_mem_erase hy)⟩
    · push Not at hall
      obtain ⟨u,hu,hbad⟩ := hall
      exact ⟨u,hu,fun y hy => (degree_pair u y (Finset.ne_of_mem_erase hy).symm).resolve_left
        (by exact not_le.mpr hbad)⟩
  obtain ⟨b,hub⟩ := hc.preconnected.exists_adj_of_nontrivial u
  have hb : b ∈ N := hsub u hu ((G.mem_neighborFinset u b).mpr hub)
  have htwo : 1 < I.card := by
    have hn := Finset.card_pos.mpr (show N.Nonempty from ⟨b,hb⟩)
    omega
  obtain ⟨y,hy⟩ : (I.erase u).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hu];omega)
  have hl := Finset.card_le_card (hsub y (Finset.mem_of_mem_erase hy))
  rw [card_neighborFinset_eq_degree] at hl
  have hdy := hother y hy
  have hN : N.card = s := by omega
  have hIc : I.card = s+1 := by omega
  have hfull (a : V) (ha : a ∈ I.erase u) : G.neighborFinset a = N := by
    apply Finset.eq_of_subset_of_card_le (hsub a (Finset.mem_of_mem_erase ha))
    rw [card_neighborFinset_eq_degree,hN]
    exact hother a ha
  have hjoin (a : V) (ha : a ∈ I.erase u) (x : V) (hx : x ∈ N) : G.Adj a x :=
    (G.mem_neighborFinset a x).mp ((hfull a ha).symm ▸ hx)
  have hbc : I.filter (G.Adj b) = I := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    by_cases hau : a=u
    · simpa [hau] using hub.symm
    · exact (hjoin a (Finset.mem_erase.mpr ⟨hau,ha⟩) b hb).symm
  obtain ⟨_,_,hdom⟩ := saturates hc s h I hI b (by rw [hbc,hIc])
  have hdis : Disjoint I N := by
    apply Finset.disjoint_left.mpr
    intro a ha hNa
    obtain ⟨_,x,hx,hxa⟩ := Finset.mem_filter.mp hNa
    exact hI hx ha hxa.ne hxa
  obtain ⟨l,hhead,hnd,hchain,hset⟩ := alternating_chain N (I.erase u)
    (by rw [hN,Finset.card_erase_of_mem hu,hIc];omega)
    (hdis.symm.mono_right (Finset.erase_subset _ _)) (fun x hx a ha => (hjoin a ha x hx).symm) b hb
  have hnu : u ∉ l := by
    intro hh
    have : u ∈ N ∪ I.erase u := hset ▸ List.mem_toFinset.mpr hh
    rcases Finset.mem_union.mp this with hN | hI
    · exact Finset.disjoint_left.mp hdis hu hN
    · exact Finset.notMem_erase u I hI
  have hch : (u::l).IsChain G.Adj := List.isChain_cons.mpr ⟨by
    intro x hx
    have he : x = b := by simpa [hhead,eq_comm] using hx
    simpa [he] using hub,hchain⟩
  let p := Walk.ofSupport (u::l) (by simp) hch
  have hsup : p.support = u::l := Walk.support_ofSupport _ _
  have hp : p.IsPath := Walk.IsPath.mk' (by rw [hsup]; exact List.nodup_cons.mpr ⟨hnu,hnd⟩)
  refine ⟨_,_,p,hp.isHamiltonian_of_mem ?_⟩
  intro x
  rw [hsup,List.mem_cons]
  by_cases hxu : x=u
  · exact Or.inl hxu
  · apply Or.inr
    apply List.mem_toFinset.mp
    rw [hset]
    rcases hdom x with hx | ⟨a,ha,hax⟩
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxu,hx⟩)
    · exact Finset.mem_union_left _ (hsub a ha ((G.mem_neighborFinset a x).mpr hax))


lemma finite_case (h1 : H1) (h2 : H2) {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hb : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have h (v : V) : distEven G v ≤ 1 + secondSmallestDegree G :=
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))).trans hb
  by_cases hHall : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      I.card ≤ (Finset.univ.filter (fun x => ∃ a ∈ I, G.Adj a x)).card
  case neg =>
    push Not at hHall
    obtain ⟨I,hI,hviol⟩ := hHall
    exact trace_of_hall_deficit hc (by simpa [Nat.add_comm] using h) I hI hviol
  by_cases horder : G.minDegree + secondSmallestDegree G + 1 < Fintype.card V
  · by_cases hs : G.diam ≤ 2
    · exact trace_small hc hs h
    · have hdiam := diameter_le_five hc h
      by_cases he : G.diam = 3
      · exact h1 G hc he horder (order_bound hc h) h hHall
      · exact h2 G hc (by omega) hdiam
          (five_endpoints hc (by simpa only [Nat.add_comm 1] using h)) horder (order_bound hc h) h hHall
  · apply trace_of_sum hc
    intro x y hxy
    have hx := G.minDegree_le_degree x
    have hy := G.minDegree_le_degree y
    have hxy' := degree_pair (G := G) x y hxy
    omega


section Transfer

variable {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W}

lemma dist_iso (φ : G ≃g G') (hc : G.Connected) (x y : V) :
    G'.dist (φ x) (φ y) = G.dist x y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨q,hq⟩ := (φ.connected_iff.mp hc).exists_walk_length_eq_dist (φ x) (φ y)
  have h1 := dist_le (p.map φ.toHom)
  have h2 := dist_le (q.map φ.symm.toHom)
  simp only [Walk.length_map,hp] at h1
  simpa [Walk.length_map,hq] using le_antisymm h1 (by simpa [Walk.length_map,hq] using h2)

lemma even_iso (φ : G ≃g G') (hc : G.Connected) (x : V) :
    distEven G' (φ x) = distEven G x := by
  classical
  simp only [distEven, Finset.card_filter]
  rw [← φ.toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [show G'.dist (φ x) (φ.toEquiv y) = G.dist x y from dist_iso φ hc x y]

lemma second_iso [DecidableRel G.Adj] [DecidableRel G'.Adj] (φ : G ≃g G') :
    secondSmallestDegree G' = secondSmallestDegree G := by
  change ((Finset.univ.val.map (fun y : W => G'.degree y)).sort (· ≤ ·)).getD 1 0 =
    ((Finset.univ.val.map (fun x : V => G.degree x)).sort (· ≤ ·)).getD 1 0
  congr 2
  rw [← Finset.map_univ_equiv φ.toEquiv]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def]
  congr 1
  exact funext (φ.degree_eq ·)

end Transfer

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture189.conjecture189 := by
  intro h1 h2 V _ _ _ G _ hc hb
  classical
  let e := Fintype.equivFin V
  let φ := SimpleGraph.Iso.map e G
  have : Nontrivial (Fin (Fintype.card V)) := e.symm.nontrivial
  have hc' := φ.connected_iff.mp hc
  have h : ∀ y, distEven (G.map e) y ≤ 1 + secondSmallestDegree (G.map e) := by
    intro y
    obtain ⟨x,rfl⟩ := φ.surjective y
    rw [even_iso φ hc, second_iso φ]
    exact (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))).trans hb
  have hb' : (Finset.univ.image (distEven (G.map e))).max' (by simp) ≤
      1 + secondSmallestDegree (G.map e) := by
    apply Finset.max'_le
    intro n hn
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hn
    exact h y
  obtain ⟨a,b,q,hq⟩ := finite_case h1 h2 (G.map e) hc' hb'
  exact ⟨φ.symm a,φ.symm b,q.map φ.symm.toHom,hq.map _ φ.symm.bijective⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
