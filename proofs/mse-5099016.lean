import OMAStatements.S_mse_5099016
import Mathlib

-- mse-5099016: all vertices of a connected graph with an even-degree vertex can be removed by reductions
-- Credit: @Mapika

/-!
Removing all vertices of a graph by reductions (`mse-5099016`)

Target (`statements/mse-5099016.lean`): for a finite connected simple graph `G` with at least one
vertex of even degree, `Relation.ReflTransGen (ReductionStep G) Finset.univ ∅`, where one
reduction step from the vertex set `S` picks `v ∈ S` of even degree in `G[S]` and a set `U` of
neighbours of `v` in `S` that is either of odd size or the whole neighbourhood, and removes
`v` and `U`.

Status of the mathematics: NOT a new result. The statement was asked on Mathematics Stack
Exchange (question 5099016, September 2025) as an open problem. The asker posted a proof as an
answer in March 2026 (answer 5127263), and a comment of August 2026 under that answer says that
an automated prover formalised it in Lean and links a public repository. Nobody on this team has
opened that repository; this proof is independent of it. What was read: the question
and the answer text on the Stack Exchange page.

Method. Call a vertex set `S` good if no connected component of `G[S]` has all degrees odd
(such a component is called peculiar; it can never be touched by a reduction). The theorem
follows by induction on the size from the key step: a nonempty good set has a reduction to a good
set (`key`). For a connected good set the key step is the answer's proposition (a connected graph
with an even vertex is starry). The two easy lemmas of the answer are kept (`lemma1`, `lemma2`,
re-derived by the lead). The long case analysis of the answer (its Case 1 and Case 2, whose last
step is only asserted there) is NOT used: it is replaced by the lead's own structure lemma `core`
(complete proof in the docstrings of `core_a`, `core_b`) and by `star_a`, `star_b`.

Structure. `core_a`, `core_b` (structure lemma: hubs, and what hubs give), `oddpick`, `lemma2`,
`star_a`, `star_b` were proved separately against fixed statements by a team of agents (helper
names carry a two-letter tag) and assembled mechanically with the toolkit and the main argument.

Tests (python, exact brute force, kept outside this file): `brute.py` (the target itself: all labelled
connected graphs on at most 6 vertices, random graphs up to 12), `lem3.py` (first form of `core`),
`tests_bp.py` (`core`, `lemma1`, `lemma2`, `starcase`, `key` and the toolkit, mirrored literally
with an ambient graph and arbitrary subsets: all labelled graphs on at most 5 vertices, random
graphs on 6 to 8), `tests_core_split.py` (`core_a`, `core_b`: same exhaustive range, random on 6
to 9), `tests_split2.py` (`oddpick`, `star_a`: same exhaustive range, random on 6 to 10, and the
double star on 11 vertices). `star_b` is `starcase` with more hypotheses. No test failed.

Review. One independent adversarial reviewer (told to refute, with its own scripts, not shown the
lead's scripts or conclusions) attacked the first version of this blueprint, in which `core`,
`lemma2`, `starcase` and the toolkit were twelve statements still to be proved. Result: no statement refuted
(all labelled graphs on at most 5 vertices with all subsets, all graphs on 6 vertices with the
whole vertex set, 24000 random and structured graphs on 7 to 9 vertices, hub-and-star families
up to 12 vertices); Steps 1 to 6 of `core` and the proofs of `lemma2` and `starcase` found sound
line by line, and the intermediate claims that now form `Hub` (one peculiar component `P_u`,
`E \ {u} = N(u) ∩ P_u`, `S \ {u} ⊆ P_u`, Step 4, Step 6) held on about 756000 instances.
Strongest objection: cost and coverage of the two biggest contracts. The case of `core` in which
`C \ S` is not good, and the branch of `starcase` that consumes it, almost never occur on small
graphs (30 instances exhaustively up to 6 vertices; the peculiar-`W` branch only on hand-built
hub + star + triangle graphs), so the evidence for these statements is mostly random and targeted
graphs on 7 to 12 vertices, and `core`, `starcase` would run to 600 to 900 lines each; the
reviewer also asked for a covering lemma and noted that Case 1 of `lemma2` misused `tk_split`
and that Case 2 must route even vertices adjacent to `w` through `w`.
Disposition: accepted. After the review the lead (i) proved the whole toolkit, `good_univ`,
`pec_erase`, `lemma1` and `key` in Lean, (ii) added `tk_cover`, (iii) split `core` into `core_a`,
`core_b` and `starcase` into `star_a`, `star_b`, and factored `oddpick` out of `lemma2` and
`star_b`, (iv) rewrote the proof of `lemma2` with the case split on `(C.erase w) \ P` being good
and the routing through `w` made explicit. The statements of `core_a`, `core_b`, `oddpick`,
`star_a`, `star_b` are NEW after the review: they were tested by the lead's scripts only (see
Tests), not by the reviewer, although `Hub` consists of the intermediate claims the reviewer
checked. The coverage objection concerned the evidence before formalization; every statement is now
proved in this file and checked by the kernel.
-/

namespace OMA.Redux

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree of `v` into the vertex set `S` (the degree of `v` in `G[S]` when `v ∈ S`). -/
def dg (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

/-- An edge of `G[S]`. -/
def Lk (S : Finset V) (a b : V) : Prop := a ∈ S ∧ b ∈ S ∧ G.Adj a b

/-- Reachability inside `S`. Note that `Rch G S a a` holds for every `a`, also outside `S`. -/
def Rch (S : Finset V) (a b : V) : Prop := Relation.ReflTransGen (Lk G S) a b

/-- The connected component of `a` in `G[S]` is peculiar: every vertex of it has odd degree. -/
def Pec (S : Finset V) (a : V) : Prop := a ∈ S ∧ ∀ b, Rch G S a b → Odd (dg G S b)

/-- No connected component of `G[S]` is peculiar. -/
def Good (S : Finset V) : Prop := ∀ a, ¬ Pec G S a

/-- `G[S]` is connected (the empty set counts as connected). -/
def Conn (S : Finset V) : Prop := ∀ a ∈ S, ∀ b ∈ S, Rch G S a b

/-- `v, U` is a legal reduction of `S`: `v ∈ S` has even degree in `G[S]`, and `U` is a set of
neighbours of `v` in `S`, of odd size or the whole neighbourhood. -/
def Star (S : Finset V) (v : V) (U : Finset V) : Prop :=
  v ∈ S ∧ U ⊆ S.filter (G.Adj v) ∧ Even (dg G S v) ∧ (Odd U.card ∨ U = S.filter (G.Adj v))

/-- `D` is a union of connected components of `G[S]`. -/
def Closed (S D : Finset V) : Prop := D ⊆ S ∧ ∀ x ∈ D, ∀ y ∈ S, G.Adj x y → y ∈ D

-- ### Toolkit (proved)

/-- `S` is good iff every vertex of `S` reaches, inside `S`, a vertex of even degree. -/
lemma tk_good_iff (S : Finset V) :
    Good G S ↔ ∀ a ∈ S, ∃ b, Rch G S a b ∧ Even (dg G S b) := by
  unfold Good Pec
  constructor
  · intro h a ha
    by_contra hc
    refine h a ⟨ha, fun b hb => ?_⟩
    by_contra ho
    exact hc ⟨b, hb, Nat.not_odd_iff_even.mp ho⟩
  · intro h a ⟨ha, hp⟩
    obtain ⟨b, hb, he⟩ := h a ha
    exact Nat.not_odd_iff_even.mpr he (hp b hb)

/-- A connected graph with a vertex of even degree is good. -/
lemma good_univ (hc : G.Connected) (he : ∃ v : V, Even (G.degree v)) :
    Good G Finset.univ := by
  obtain ⟨v, hv⟩ := he
  have hr : ∀ a b : V, G.Reachable a b → Rch G Finset.univ a b := by
    intro a b ⟨w⟩
    induction w with
    | nil => exact Relation.ReflTransGen.refl
    | cons h _ ih =>
      exact Relation.ReflTransGen.head ⟨Finset.mem_univ _, Finset.mem_univ _, h⟩ ih
  have hd : dg G Finset.univ v = G.degree v := by
    unfold dg
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  intro a ⟨_, hp⟩
  have := hp v (hr a v (hc.preconnected a v))
  rw [hd] at this
  exact Nat.not_odd_iff_even.mpr hv this

/-- A vertex reachable inside `S` from a vertex of `S` is in `S`. -/
lemma rch_mem {S : Finset V} {a b : V} (h : Rch G S a b) (ha : a ∈ S) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ h2 _ => exact h2.2.1

/-- Reachability inside `S` is symmetric. (Transitivity is `Relation.ReflTransGen.trans`.) -/
lemma rch_symm {S : Finset V} {a b : V} (h : Rch G S a b) : Rch G S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact Relation.ReflTransGen.head ⟨h2.2.1, h2.1, h2.2.2.symm⟩ ih

/-- For a union of components `D` of `G[S]`: degrees, reachability from a vertex of `D`, and
peculiarity at a vertex of `D` are the same in `D` and in `S`. -/
lemma tk_closed (S D : Finset V) (h : Closed G S D) :
    (∀ x ∈ D, dg G D x = dg G S x) ∧ (∀ a ∈ D, ∀ b, Rch G S a b ↔ Rch G D a b) ∧
      (∀ a ∈ D, (Pec G S a ↔ Pec G D a)) := by
  obtain ⟨hDS, hcl⟩ := h
  have hdeg : ∀ x ∈ D, dg G D x = dg G S x := by
    intro x hx
    unfold dg
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hDS h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hcl x hx y h1 h2, h2⟩⟩
  have hr : ∀ a ∈ D, ∀ b, Rch G S a b → (Rch G D a b ∧ b ∈ D) := by
    intro a ha b hab
    induction hab with
    | refl => exact ⟨Relation.ReflTransGen.refl, ha⟩
    | tail _ h2 ih =>
      have hb := hcl _ ih.2 _ h2.2.1 h2.2.2
      exact ⟨Relation.ReflTransGen.tail ih.1 ⟨ih.2, hb, h2.2.2⟩, hb⟩
  have hr2 : ∀ a ∈ D, ∀ b, Rch G S a b ↔ Rch G D a b := by
    intro a ha b
    refine ⟨fun h => (hr a ha b h).1, fun h => ?_⟩
    have hmono : ∀ x y, Lk G D x y → Lk G S x y :=
      fun x y hxy => ⟨hDS hxy.1, hDS hxy.2.1, hxy.2.2⟩
    exact Relation.ReflTransGen.mono hmono a b h
  refine ⟨hdeg, hr2, ?_⟩
  intro a ha
  unfold Pec
  constructor
  · intro ⟨_, hp⟩
    refine ⟨ha, fun b hb => ?_⟩
    have hb' := (hr2 a ha b).mpr hb
    rw [hdeg b (hr a ha b hb').2]
    exact hp b hb'
  · intro ⟨_, hp⟩
    refine ⟨hDS ha, fun b hb => ?_⟩
    rw [← hdeg b (hr a ha b hb).2]
    exact hp b ((hr2 a ha b).mp hb)

/-- The complement of a union of components is a union of components, and `S` is good iff
both parts are. -/
lemma tk_split (S D : Finset V) (h : Closed G S D) :
    Closed G S (S \ D) ∧ (Good G S ↔ Good G D ∧ Good G (S \ D)) := by
  have hc2 : Closed G S (S \ D) := by
    refine ⟨Finset.sdiff_subset, fun x hx y hy hxy => ?_⟩
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hy, fun hyD => hx.2 (h.2 y hyD x hx.1 hxy.symm)⟩
  refine ⟨hc2, ?_⟩
  have h1 := (tk_closed G S D h).2.2
  have h2 := (tk_closed G S (S \ D) hc2).2.2
  unfold Good
  constructor
  · intro hg
    exact ⟨fun a hp => hg a ((h1 a hp.1).mpr hp), fun a hp => hg a ((h2 a hp.1).mpr hp)⟩
  · intro ⟨hg1, hg2⟩ a hp
    by_cases haD : a ∈ D
    · exact hg1 a ((h1 a haD).mp hp)
    · have : a ∈ S \ D := Finset.mem_sdiff.mpr ⟨hp.1, haD⟩
      exact hg2 a ((h2 a this).mp hp)

/-- Covering: if every vertex of `T` lies in a good union of components of `G[T]`, then `T` is
good. -/
lemma tk_cover (T : Finset V) (h : ∀ a ∈ T, ∃ D, a ∈ D ∧ Closed G T D ∧ Good G D) :
    Good G T := by
  intro a hp
  obtain ⟨D, haD, hcl, hg⟩ := h a hp.1
  exact hg a (((tk_closed G T D hcl).2.2 a haD).mp hp)

/-- The connected component of `a ∈ S` as a finset. -/
lemma tk_comp (S : Finset V) (a : V) (ha : a ∈ S) :
    ∃ K : Finset V, a ∈ K ∧ Closed G S K ∧ Conn G K ∧ ∀ b, b ∈ K ↔ Rch G S a b := by
  classical
  let K : Finset V := S.filter (fun b => Rch G S a b)
  have hmem : ∀ b, b ∈ K ↔ Rch G S a b := by
    intro b
    simp only [K, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨rch_mem G h ha, h⟩⟩
  have haK : a ∈ K := (hmem a).mpr Relation.ReflTransGen.refl
  have hcl : Closed G S K := by
    refine ⟨Finset.filter_subset _ _, fun x hx y hy hxy => ?_⟩
    rw [hmem] at hx ⊢
    exact Relation.ReflTransGen.tail hx ⟨rch_mem G hx ha, hy, hxy⟩
  refine ⟨K, haK, hcl, ?_, hmem⟩
  intro x hx y hy
  have hr := (tk_closed G S K hcl).2.1
  have hax : Rch G K a x := (hr a haK x).mp ((hmem x).mp hx)
  have hay : Rch G K a y := (hr a haK y).mp ((hmem y).mp hy)
  exact Relation.ReflTransGen.trans (rch_symm G hax) hay

lemma tk_parity_aux (S : Finset V) (n : ℕ) : ∀ T : Finset V, T.card = n → T ⊆ S → Odd T.card →
    ∃ a ∈ T, ∀ K : Finset V, (∀ b, b ∈ K ↔ Rch G S a b) → Odd (T ∩ K).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hT hodd
    have hne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hodd
    obtain ⟨a, haT⟩ := hne
    obtain ⟨K, haK, hcl, hconn, hmem⟩ := tk_comp G S a (hT haT)
    by_cases hp : Odd (T ∩ K).card
    · refine ⟨a, haT, fun K' hK' => ?_⟩
      have hKK : K' = K := Finset.ext fun b => by rw [hK', hmem]
      rw [hKK]
      exact hp
    · have hcard : (T \ K).card + (T ∩ K).card = T.card := Finset.card_sdiff_add_card_inter T K
      have hodd' : Odd (T \ K).card := by
        have he : Even (T ∩ K).card := Nat.not_odd_iff_even.mp hp
        rw [← hcard] at hodd
        exact (Nat.odd_add.mp hodd).mpr he
      have hlt : (T \ K).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, fun h => ?_⟩
        exact (Finset.mem_sdiff.mp (h haT)).2 haK
      obtain ⟨a', ha', h'⟩ := ih _ hlt (T \ K) rfl (Finset.sdiff_subset.trans hT) hodd'
      refine ⟨a', (Finset.mem_sdiff.mp ha').1, fun K' hK' => ?_⟩
      have h3 := h' K' hK'
      have heq : (T \ K) ∩ K' = T ∩ K' := by
        ext b
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · exact fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩
        · intro ⟨h1, h3⟩
          refine ⟨⟨h1, fun hbK => ?_⟩, h3⟩
          have h4 : Rch G S a a' :=
            Relation.ReflTransGen.trans ((hmem b).mp hbK) (rch_symm G ((hK' b).mp h3))
          exact (Finset.mem_sdiff.mp ha').2 ((hmem a').mpr h4)
      rw [heq] at h3
      exact h3

/-- A set `T ⊆ S` of odd size meets some connected component of `G[S]` in an odd number of
vertices. -/
lemma tk_parity (S T : Finset V) (hT : T ⊆ S) (hodd : Odd T.card) :
    ∃ a ∈ T, ∀ K : Finset V, (∀ b, b ∈ K ↔ Rch G S a b) → Odd (T ∩ K).card :=
  tk_parity_aux G S _ T rfl hT hodd

/-- Leaving through `v`: a path inside `C` from `a ≠ v` either avoids `v`, or passes a neighbour
`y` of `v` that is reachable from `a` inside `C - v`. With `b := v` only the second case is
possible, so in a connected `C` every component of `C - v` contains a neighbour of `v`. -/
lemma tk_exit (C : Finset V) (v : V) {a b : V} (h : Rch G C a b) (ha : a ∈ C.erase v) :
    Rch G (C.erase v) a b ∨ ∃ y, Rch G (C.erase v) a y ∧ y ∈ C.erase v ∧ G.Adj y v := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases ih with ih | ih
    · by_cases hc : c = v
      · right
        exact ⟨b, ih, rch_mem G ih ha, hc ▸ hbc.2.2⟩
      · left
        exact Relation.ReflTransGen.tail ih
          ⟨rch_mem G ih ha, Finset.mem_erase.mpr ⟨hc, hbc.2.1⟩, hbc.2.2⟩
    · exact Or.inr ih

/-- Removing a neighbour lowers the degree by one. -/
lemma dg_erase_adj (C : Finset V) (v y : V) (hv : v ∈ C) (hyv : G.Adj y v) :
    dg G (C.erase v) y + 1 = dg G C y := by
  unfold dg
  have hm : v ∈ C.filter (G.Adj y) := Finset.mem_filter.mpr ⟨hv, hyv⟩
  rw [Finset.filter_erase, Finset.card_erase_of_mem hm]
  have : 0 < (C.filter (G.Adj y)).card := Finset.card_pos.mpr ⟨v, hm⟩
  omega

/-- Removing a non-neighbour does not change the degree. -/
lemma dg_erase_not_adj (C : Finset V) (v y : V) (hyv : ¬ G.Adj y v) :
    dg G (C.erase v) y = dg G C y := by
  unfold dg
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  exact fun h => hyv (Finset.mem_filter.mp h).2

/-- A connected set all of whose degrees are odd stays good when one vertex is removed. -/
lemma pec_erase (C : Finset V) (hc : Conn G C) (hodd : ∀ x ∈ C, Odd (dg G C x)) (v : V)
    (hv : v ∈ C) : Good G (C.erase v) := by
  rw [tk_good_iff]
  intro a ha
  have haC := (Finset.mem_erase.mp ha).2
  rcases tk_exit G C v (hc a haC v hv) ha with h | ⟨y, hy, hyC, hyv⟩
  · exact absurd (rch_mem G h ha) (Finset.notMem_erase v C)
  · refine ⟨y, hy, ?_⟩
    have h1 := hodd y (Finset.mem_erase.mp hyC).2
    rw [← dg_erase_adj G C v y hv hyv] at h1
    exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h1)

-- ### The structure lemma

/-- The structure around `u ∈ S` used in `core`: `P` is the union of the peculiar components of
`C - u` (in fact a single component), it contains every other vertex of even degree of `C` and
every other vertex of `S`, the vertices of even degree are adjacent to `u`, and `S` has a second
vertex. -/
def Hub (C S : Finset V) (u : V) (P : Finset V) : Prop :=
  Closed G (C.erase u) P ∧ (∀ x ∈ P, Odd (dg G (C.erase u) x)) ∧
    (∀ a, Pec G (C.erase u) a → a ∈ P) ∧
    (∀ e ∈ C, e ≠ u → Even (dg G C e) → e ∈ P ∧ G.Adj u e) ∧
    (∀ s ∈ S, s ≠ u → s ∈ P) ∧ ∃ s ∈ S, s ≠ u

-- core_a
section CA

/-- (a) In a connected `C`, every vertex of `C - w` reaches inside `C - w` a neighbour of `w`. -/
lemma CA_exit (C : Finset V) (hc : Conn G C) (w : V) (hw : w ∈ C) (a : V)
    (ha : a ∈ C.erase w) :
    ∃ y, Rch G (C.erase w) a y ∧ y ∈ C.erase w ∧ G.Adj y w := by
  have haC := (Finset.mem_erase.mp ha).2
  rcases tk_exit G C w (hc a haC w hw) ha with h | h
  · exact absurd (rch_mem G h ha) (Finset.notMem_erase w C)
  · exact h

/-- (b) A vertex of odd degree in `C - w` has even degree in `C` iff it is adjacent to `w`. -/
lemma CA_par (C : Finset V) (w : V) (hw : w ∈ C) (x : V)
    (hodd : Odd (dg G (C.erase w) x)) : Even (dg G C x) ↔ G.Adj x w := by
  by_cases h : G.Adj x w
  · have h1 := dg_erase_adj G C w x hw h
    refine ⟨fun _ => h, fun _ => ?_⟩
    rw [← h1]
    exact hodd.add_one
  · have h1 := dg_erase_not_adj G C w x h
    rw [h1] at hodd
    exact ⟨fun he => absurd he (Nat.not_even_iff_odd.mpr hodd), fun hadj => absurd hadj h⟩

/-- A path inside `T` from `x` stays inside `T - s` if `s` is not reachable from `x`. -/
lemma CA_rch_erase (T : Finset V) (s : V) {x y : V} (h : Rch G T x y)
    (hs : ∀ z, Rch G T x z → z ≠ s) : Rch G (T.erase s) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.tail ih
      ⟨Finset.mem_erase.mpr ⟨hs _ hab, hbc.1⟩,
        Finset.mem_erase.mpr ⟨hs _ (Relation.ReflTransGen.tail hab hbc), hbc.2.1⟩, hbc.2.2⟩

/-- Reachability is monotone in the vertex set. -/
lemma CA_mono {T T' : Finset V} (hT : T ⊆ T') {x y : V} (h : Rch G T x y) : Rch G T' x y :=
  Relation.ReflTransGen.mono (fun _ _ hxy => ⟨hT hxy.1, hT hxy.2.1, hxy.2.2⟩) x y h

/-- A set that is not good has a peculiar base point. -/
lemma CA_bad (T : Finset V) (h : ¬ Good G T) : ∃ a, Pec G T a := by
  by_contra hne
  exact h (fun a ha => hne ⟨a, ha⟩)

/-- Step 1: if `s` lies in a peculiar component of `C - u`, then every peculiar component of
`C - s` contains `u`. -/
lemma CA_step1 (C : Finset V) (hc : Conn G C) (u s a a' : V) (hu : u ∈ C) (hsC : s ∈ C)
    (hsu : s ≠ u) (ha : Pec G (C.erase u) a) (has : Rch G (C.erase u) a s)
    (ha' : Pec G (C.erase s) a') : Rch G (C.erase s) a' u := by
  obtain ⟨y, hy, hyC, hys⟩ := CA_exit G C hc s hsC a' ha'.1
  have hye : Even (dg G C y) := (CA_par G C s hsC y (ha'.2 y hy)).mpr hys
  have huE : u ∈ C.erase s := Finset.mem_erase.mpr ⟨fun h => hsu h.symm, hu⟩
  by_cases hyu : y = u
  · rw [← hyu]
    exact hy
  · have hyCu : y ∈ C.erase u := Finset.mem_erase.mpr ⟨hyu, (Finset.mem_erase.mp hyC).2⟩
    have hsCu : s ∈ C.erase u := Finset.mem_erase.mpr ⟨hsu, hsC⟩
    have hay : Rch G (C.erase u) a y := Relation.ReflTransGen.tail has ⟨hsCu, hyCu, hys.symm⟩
    have hyu' : G.Adj y u := (CA_par G C u hu y (ha.2 y hay)).mp hye
    exact Relation.ReflTransGen.tail hy ⟨hyC, huE, hyu'⟩

/-- Step 2: for `u ∈ S`, every vertex `e ≠ u` of even degree in `C` lies in every peculiar
component of `C - u` and is adjacent to `u`. -/
lemma CA_step2 (C S : Finset V) (hc : Conn G C) (hS : S ⊆ C)
    (h2 : ∀ u ∈ S, ¬ Good G (C.erase u))
    (h3 : ∀ w ∈ C, ∀ a, Pec G (C.erase w) a → ∃ s ∈ S, Rch G (C.erase w) a s)
    (u : V) (hu : u ∈ S) (a : V) (ha : Pec G (C.erase u) a) (e : V) (heC : e ∈ C)
    (heu : e ≠ u) (hee : Even (dg G C e)) : Rch G (C.erase u) a e ∧ G.Adj u e := by
  have huC := hS hu
  obtain ⟨s, hsS, has⟩ := h3 u huC a ha
  have hsCu : s ∈ C.erase u := rch_mem G has ha.1
  have hsu : s ≠ u := (Finset.mem_erase.mp hsCu).1
  have hsC : s ∈ C := (Finset.mem_erase.mp hsCu).2
  obtain ⟨a', ha'⟩ := CA_bad G _ (h2 s hsS)
  have ha'u : Rch G (C.erase s) a' u := CA_step1 G C hc u s a a' huC hsC hsu ha has ha'
  have huEs : u ∈ C.erase s := Finset.mem_erase.mpr ⟨fun h => hsu h.symm, huC⟩
  have heCu : e ∈ C.erase u := Finset.mem_erase.mpr ⟨heu, heC⟩
  have hkey : Rch G (C.erase u) a e := by
    by_contra hne
    have havoid : ∀ z, Rch G (C.erase u) e z → z ≠ s := by
      intro z hz hzs
      rw [hzs] at hz
      exact hne (Relation.ReflTransGen.trans has (rch_symm G hz))
    rcases tk_exit G C u (hc e heC u huC) heCu with h | ⟨y, hy, hyC, hyu⟩
    · exact absurd (rch_mem G h heCu) (Finset.notMem_erase u C)
    · have h1 : Rch G ((C.erase u).erase s) e y := CA_rch_erase G _ s hy havoid
      have h2' : Rch G (C.erase s) e y :=
        CA_mono G (Finset.erase_subset_erase s (Finset.erase_subset u C)) h1
      have hys : y ≠ s := havoid y hy
      have h3' : Rch G (C.erase s) e u :=
        Relation.ReflTransGen.tail h2'
          ⟨Finset.mem_erase.mpr ⟨hys, (Finset.mem_erase.mp hyC).2⟩, huEs, hyu⟩
      have h4 : Rch G (C.erase s) a' e := Relation.ReflTransGen.trans ha'u (rch_symm G h3')
      have hnadj : ¬ G.Adj e s := fun hadj =>
        hne (Relation.ReflTransGen.tail has ⟨hsCu, heCu, hadj.symm⟩)
      exact hnadj ((CA_par G C s hsC e (ha'.2 e h4)).mp hee)
  exact ⟨hkey, ((CA_par G C u huC e (ha.2 e hkey)).mp hee).symm⟩

/-- LEMMA `core_a` (TAG `CA`): every `u ∈ S` has a hub. -/
lemma core_a (C S : Finset V) (hc : Conn G C) (hS : S ⊆ C)
    (h2 : ∀ u ∈ S, ¬ Good G (C.erase u))
    (h3 : ∀ w ∈ C, ∀ a, Pec G (C.erase w) a → ∃ s ∈ S, Rch G (C.erase w) a s)
    (u : V) (hu : u ∈ S) : ∃ P : Finset V, Hub G C S u P := by
  have huC := hS hu
  obtain ⟨a, ha⟩ := CA_bad G _ (h2 u hu)
  obtain ⟨K, -, hcl, -, hmem⟩ := tk_comp G (C.erase u) a ha.1
  obtain ⟨s0, hs0S, has0⟩ := h3 u huC a ha
  have hs0u : s0 ≠ u := (Finset.mem_erase.mp (rch_mem G has0 ha.1)).1
  refine ⟨K, hcl, fun x hx => ha.2 x ((hmem x).mp hx), ?_, ?_, ?_, ⟨s0, hs0S, hs0u⟩⟩
  · intro b hb
    obtain ⟨y, hy, hyC, hyu⟩ := CA_exit G C hc u huC b hb.1
    have hye : Even (dg G C y) := (CA_par G C u huC y (hb.2 y hy)).mpr hyu
    have h1 := (CA_step2 G C S hc hS h2 h3 u hu a ha y (Finset.mem_erase.mp hyC).2
      (Finset.mem_erase.mp hyC).1 hye).1
    exact (hmem b).mpr (Relation.ReflTransGen.trans h1 (rch_symm G hy))
  · intro e heC heu hee
    have h1 := CA_step2 G C S hc hS h2 h3 u hu a ha e heC heu hee
    exact ⟨(hmem e).mpr h1.1, h1.2⟩
  · intro s' hs' hs'u
    rw [hmem]
    by_cases hex : ∃ e ∈ C, e ≠ u ∧ e ≠ s' ∧ Even (dg G C e)
    · obtain ⟨e, heC, heu, hes, hee⟩ := hex
      have h1 := (CA_step2 G C S hc hS h2 h3 u hu a ha e heC heu hee).1
      obtain ⟨b, hb⟩ := CA_bad G _ (h2 s' hs')
      have h4 := (CA_step2 G C S hc hS h2 h3 s' hs' b hb e heC hes hee).2
      exact Relation.ReflTransGen.tail h1
        ⟨rch_mem G h1 ha.1, Finset.mem_erase.mpr ⟨hs'u, hS hs'⟩, h4.symm⟩
    · obtain ⟨y, hy, hyC, hyu⟩ := CA_exit G C hc u huC a ha.1
      have hye : Even (dg G C y) := (CA_par G C u huC y (ha.2 y hy)).mpr hyu
      have hys : y = s' := by
        by_contra hne
        exact hex ⟨y, (Finset.mem_erase.mp hyC).2, (Finset.mem_erase.mp hyC).1, hne, hye⟩
      rw [← hys]
      exact hy

end CA

-- core_b
section CB

/-- Leaving through `S`: a path inside `C` from `a ∈ C \ S` either avoids `S`, or passes a vertex
`y` reachable from `a` inside `C \ S` that has a neighbour in `S`. -/
lemma CB_exit (C S : Finset V) {a b : V} (h : Rch G C a b) (ha : a ∈ C \ S) :
    Rch G (C \ S) a b ∨ ∃ y, Rch G (C \ S) a y ∧ y ∈ C \ S ∧ ∃ s ∈ S, G.Adj y s := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases ih with ih | ih
    · by_cases hcS : c ∈ S
      · right
        exact ⟨b, ih, rch_mem G ih ha, c, hcS, hbc.2.2⟩
      · left
        exact Relation.ReflTransGen.tail ih
          ⟨rch_mem G ih ha, Finset.mem_sdiff.mpr ⟨hbc.2.1, hcS⟩, hbc.2.2⟩
    · exact Or.inr ih

omit [Fintype V] in
/-- The degree into `C` is the degree into `C \ S` plus the number of neighbours in `S`. -/
lemma CB_dg_split (C S : Finset V) (hS : S ⊆ C) (x : V) :
    dg G C x = dg G (C \ S) x + (S.filter (G.Adj x)).card := by
  unfold dg
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro ⟨h1, h2⟩
      by_cases hy : y ∈ S
      · exact Or.inr ⟨hy, h2⟩
      · exact Or.inl ⟨⟨h1, hy⟩, h2⟩
    · rintro (⟨⟨h1, -⟩, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨hS h1, h2⟩
  · rw [Finset.disjoint_left]
    intro y hy1 hy2
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy1).1).2 (Finset.mem_filter.mp hy2).1

/-- Step 4, first half: a vertex of odd degree outside `S` has at most one neighbour in `S`. -/
lemma CB_two (C S : Finset V) (hS : S ⊆ C)
    (hP : ∀ u ∈ S, ∃ P : Finset V, Hub G C S u P) (x : V) (hxC : x ∈ C) (hxS : x ∉ S)
    (hodd : Odd (dg G C x)) (s1 : V) (hs1 : s1 ∈ S) (s2 : V) (hs2 : s2 ∈ S) (hne : s1 ≠ s2)
    (h1 : G.Adj x s1) (h2 : G.Adj x s2) : False := by
  obtain ⟨P, hcl, hPodd, -, -, hP5, -⟩ := hP s1 hs1
  have hx1 : x ≠ s1 := fun h => hxS (h ▸ hs1)
  have hxP : x ∈ P :=
    hcl.2 s2 (hP5 s2 hs2 hne.symm) x (Finset.mem_erase.mpr ⟨hx1, hxC⟩) h2.symm
  have h3 := hPodd x hxP
  have h4 := dg_erase_adj G C s1 x (hS hs1) h1
  rw [Nat.odd_iff] at h3 hodd
  omega

/-- Step 6: after removing the even vertex `u ∉ S` and any `w ∈ S`, every peculiar component
meets `S`. -/
lemma CB_step6 (C S : Finset V) (hc : Conn G C) (hS : S ⊆ C)
    (hP : ∀ u ∈ S, ∃ P : Finset V, Hub G C S u P) (u : V) (huC : u ∈ C) (huS : u ∉ S)
    (hue : Even (dg G C u)) (w : V) (hw : w ∈ S) (a : V)
    (hpec : Pec G ((C.erase u).erase w) a) :
    ∃ s ∈ S, Rch G ((C.erase u).erase w) a s := by
  by_contra hno'
  have hno : ∀ s ∈ S, ¬ Rch G ((C.erase u).erase w) a s := fun s hs h => hno' ⟨s, hs, h⟩
  obtain ⟨haT, hodd⟩ := hpec
  obtain ⟨P, hcl, hPodd, -, hP4, -, s, hs, hsw⟩ := hP w hw
  have hwC : w ∈ C := hS hw
  have huw : u ≠ w := fun h => huS (h ▸ hw)
  have hwCu : w ∈ C.erase u := Finset.mem_erase.mpr ⟨huw.symm, hwC⟩
  obtain ⟨huP, -⟩ := hP4 u huC huw hue
  have hsT : s ∈ (C.erase u).erase w :=
    Finset.mem_erase.mpr ⟨hsw, Finset.mem_erase.mpr ⟨fun h => huS (h ▸ hs), hS hs⟩⟩
  have key : ∀ b, Rch G ((C.erase u).erase w) a b → ¬ G.Adj b u ∧ ¬ G.Adj b w := by
    intro b hb
    have hbT := rch_mem G hb haT
    have hbw : b ≠ w := (Finset.mem_erase.mp hbT).1
    have hbCu : b ∈ C.erase u := (Finset.mem_erase.mp hbT).2
    have hbC : b ∈ C := (Finset.mem_erase.mp hbCu).2
    have hbodd : Odd (dg G C b) := by
      by_contra hne
      have hev := Nat.not_odd_iff_even.mp hne
      obtain ⟨Ps, -, -, -, hPs4, -, -⟩ := hP s hs
      have hbs : b ≠ s := fun h => hno s hs (h ▸ hb)
      have hsb := (hPs4 b hbC hbs hev).2
      exact hno s hs (Relation.ReflTransGen.tail hb ⟨hbT, hsT, hsb.symm⟩)
    have hT := hodd b hb
    rw [Nat.odd_iff] at hT hbodd
    by_cases hbu' : G.Adj b u <;> by_cases hbw' : G.Adj b w
    · exfalso
      have hbP : b ∈ P := hcl.2 u huP b (Finset.mem_erase.mpr ⟨hbw, hbC⟩) hbu'.symm
      have h1 := hPodd b hbP
      have h2 := dg_erase_adj G C w b hwC hbw'
      rw [Nat.odd_iff] at h1
      omega
    · exfalso
      have h1 := dg_erase_adj G C u b huC hbu'
      have h2 := dg_erase_not_adj G (C.erase u) w b hbw'
      omega
    · exfalso
      have h1 := dg_erase_not_adj G C u b hbu'
      have h2 := dg_erase_adj G (C.erase u) w b hwCu hbw'
      omega
    · exact ⟨hbu', hbw'⟩
  have haCu : a ∈ C.erase u := (Finset.mem_erase.mp haT).2
  have haC : a ∈ C := (Finset.mem_erase.mp haCu).2
  rcases tk_exit G C u (hc a haC u huC) haCu with h | ⟨y, hy, -, hyu⟩
  · exact absurd (rch_mem G h haCu) (Finset.notMem_erase u C)
  · rcases tk_exit G (C.erase u) w hy haT with h | ⟨z, hz, -, hzw⟩
    · exact (key y h).1 hyu
    · exact (key z hz).2 hzw

/-- LEMMA `core_b` (TAG `CB`). Let `C` be connected, `S ⊆ C` nonempty, and suppose every
`u ∈ S` has a hub `P_u`. If `C \ S` has a peculiar component, then `|S|` is odd and there is a
vertex `u ∈ C \ S` of even degree in `C`, adjacent to every `w ∈ S`, such that for every `w ∈ S`
every peculiar component of `C - u - w` meets `S`.

Proof (the lead's). `E` is the set of vertices of even degree in `C`.
Step 4. A vertex `x ∈ C \ S` of odd degree in `C` has at most one neighbour in `S`: if `x ~ s1`,
`x ~ s2` with `s1 ≠ s2` in `S`, then `x ∉ P_{s1}` (else `dg (C - s1) x = dg C x - 1` would be
odd), but `s2 ∈ P_{s1}` and `x ~ s2`, `x ≠ s1` give `x ∈ P_{s1}` (closedness). A vertex
`x ∈ E \ S` is adjacent to every vertex of `S` (fourth property of the hubs).
Step 5. Let `Q` be a peculiar component of `C \ S` (base point from `hbad`). Some `x ∈ Q` has a
neighbour in `S` (`C` connected, `S` nonempty: walk from the base point to a vertex of `S` and
stop before the first vertex of `S`; prove the analogue of `tk_exit` for removing the set `S`).
`dg (C \ S) x + |S ∩ N(x)| = dg C x`, and `dg (C \ S) x` is odd. If `x ∉ E` then `|S ∩ N(x)| = 1`
by Step 4 and the left side is even: impossible. So `x ∈ E \ S`, `S ∩ N(x) = S`, and `|S|` is
odd. Take `u := x`.
Step 6. Let `w ∈ S`; `u ~ w` by Step 4. There is `s ∈ S`, `s ≠ w` (last property of the hub of
`w`). Suppose `D` is a peculiar component of `C - u - w` not meeting `S`. No `e ∈ E` is in `D`:
such an `e` is not in `S` and differs from `u`, so `e ~ s` (Step 4) and `s ∈ D`. So all vertices
of `D` have odd degree in `C`, and every `x ∈ D` is adjacent to both or neither of `u`, `w` (its
degree in `C - u - w` is `dg C x - [x ~ u] - [x ~ w]`, odd). Both is impossible: `x ∉ E`,
`x ~ w` give `x ∉ P_w`, while `u ∈ E`, `u ≠ w` give `u ∈ P_w`, and `x ~ u`, `x ≠ w` give
`x ∈ P_w`. Neither for all `x ∈ D` is impossible: `C` is connected, so a path from a vertex of
`D` to `u` inside `C` must leave `D` through `u` or `w` (`tk_exit` twice).
Estimate: 400 lines. Tests: `tests_core_split.py`: same ranges; 455 cases with a peculiar
component of `C \ S`, conclusion never violated; `tests_bp.py` (`t_core`) for the combination.
Depends on: toolkit. -/
lemma core_b (C S : Finset V) (hc : Conn G C) (hS : S ⊆ C) (hne : S.Nonempty)
    (hP : ∀ u ∈ S, ∃ P : Finset V, Hub G C S u P) (hbad : ¬ Good G (C \ S)) :
    Odd S.card ∧ ∃ u ∈ C \ S, Even (dg G C u) ∧ ∀ w ∈ S, G.Adj u w ∧
      ∀ a, Pec G ((C.erase u).erase w) a → ∃ s ∈ S, Rch G ((C.erase u).erase w) a s := by
  have hbad' : ∃ a, Pec G (C \ S) a := by
    by_contra h
    exact hbad fun a ha => h ⟨a, ha⟩
  obtain ⟨a, haCS, hpec⟩ := hbad'
  obtain ⟨s0, hs0⟩ := hne
  have haC : a ∈ C := (Finset.mem_sdiff.mp haCS).1
  obtain ⟨x, hax, hxCS, s1, hs1, hxs1⟩ :
      ∃ x, Rch G (C \ S) a x ∧ x ∈ C \ S ∧ ∃ s ∈ S, G.Adj x s := by
    rcases CB_exit G C S (hc a haC s0 (hS hs0)) haCS with h | h
    · exact absurd hs0 (Finset.mem_sdiff.mp (rch_mem G h haCS)).2
    · exact h
  have hxC : x ∈ C := (Finset.mem_sdiff.mp hxCS).1
  have hxS : x ∉ S := (Finset.mem_sdiff.mp hxCS).2
  have hxodd : Odd (dg G (C \ S) x) := hpec x hax
  have hsplit := CB_dg_split G C S hS x
  have hxe : Even (dg G C x) := by
    by_contra hne'
    have hodd : Odd (dg G C x) := Nat.not_even_iff_odd.mp hne'
    have hle : (S.filter (G.Adj x)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro p hp q hq
      by_contra hpq
      rw [Finset.mem_filter] at hp hq
      exact CB_two G C S hS hP x hxC hxS hodd p hp.1 q hq.1 hpq hp.2 hq.2
    have hpos : 0 < (S.filter (G.Adj x)).card :=
      Finset.card_pos.mpr ⟨s1, Finset.mem_filter.mpr ⟨hs1, hxs1⟩⟩
    rw [Nat.odd_iff] at hodd hxodd
    omega
  have hall : ∀ w ∈ S, G.Adj x w := by
    intro w hw
    obtain ⟨P, -, -, -, hP4, -, -⟩ := hP w hw
    exact (hP4 x hxC (fun h => hxS (h ▸ hw)) hxe).2.symm
  have hfil : S.filter (G.Adj x) = S := Finset.filter_true_of_mem hall
  rw [hfil] at hsplit
  refine ⟨?_, x, hxCS, hxe, fun w hw => ⟨hall w hw, ?_⟩⟩
  · rw [Nat.odd_iff] at hxodd ⊢
    rw [Nat.even_iff] at hxe
    omega
  · exact fun a' ha' => CB_step6 G C S hc hS hP x hxC hxS hxe w hw a' ha'

end CB

/-- The structure lemma: `core_a` and `core_b` combined. -/
lemma core (C S : Finset V) (hc : Conn G C) (hS : S ⊆ C) (hne : S.Nonempty)
    (h2 : ∀ u ∈ S, ¬ Good G (C.erase u))
    (h3 : ∀ w ∈ C, ∀ a, Pec G (C.erase w) a → ∃ s ∈ S, Rch G (C.erase w) a s)
    (hbad : ¬ Good G (C \ S)) :
    Odd S.card ∧ ∃ u ∈ C \ S, Even (dg G C u) ∧ ∀ w ∈ S, G.Adj u w ∧
      ∀ a, Pec G ((C.erase u).erase w) a → ∃ s ∈ S, Rch G ((C.erase u).erase w) a s :=
  core_b G C S hc hS hne (fun u hu => core_a G C S hc hS h2 h3 u hu) hbad

/-- If `C` is connected, has a vertex of even degree, and removing any vertex of even degree
leaves a peculiar component, then removing all vertices of even degree leaves a good set
(Lemma 1 of the Stack Exchange answer, here a corollary of `core`). -/
lemma lemma1 (C : Finset V) (hc : Conn G C) (hne : ∃ u ∈ C, Even (dg G C u))
    (h2 : ∀ u ∈ C, Even (dg G C u) → ¬ Good G (C.erase u)) :
    Good G (C.filter (fun x => ¬ Even (dg G C x))) := by
  by_contra hbad
  rw [Finset.filter_not] at hbad
  obtain ⟨u0, hu0, hu0e⟩ := hne
  have hS : C.filter (fun x => Even (dg G C x)) ⊆ C := Finset.filter_subset _ _
  have hne' : (C.filter (fun x => Even (dg G C x))).Nonempty :=
    ⟨u0, Finset.mem_filter.mpr ⟨hu0, hu0e⟩⟩
  have h2' : ∀ u ∈ C.filter (fun x => Even (dg G C x)), ¬ Good G (C.erase u) := by
    intro u hu
    exact h2 u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
  have h3 : ∀ w ∈ C, ∀ a, Pec G (C.erase w) a →
      ∃ s ∈ C.filter (fun x => Even (dg G C x)), Rch G (C.erase w) a s := by
    intro w hw a ⟨ha, hp⟩
    have haC := (Finset.mem_erase.mp ha).2
    rcases tk_exit G C w (hc a haC w hw) ha with h | ⟨y, hy, hyC, hyw⟩
    · exact absurd (rch_mem G h ha) (Finset.notMem_erase w C)
    · refine ⟨y, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hyC).2, ?_⟩, hy⟩
      rw [← dg_erase_adj G C w y hw hyw]
      exact (hp y hy).add_one
  obtain ⟨-, u, hu, hue, -⟩ := core G C _ hc hS hne' h2' h3 hbad
  rw [Finset.mem_sdiff] at hu
  exact hu.2 (Finset.mem_filter.mpr ⟨hu.1, hue⟩)

-- ### The two reductions

-- oddpick
section OP

/-- Gluing: removing from a good `X` a subset `U` of a union of components `K` keeps `X` good
when `K \ U` is good. -/
lemma OP_glue (X K U : Finset V) (hcl : Closed G X K) (hg : Good G X) (hUK : U ⊆ K)
    (hgK : Good G (K \ U)) : Good G (X \ U) := by
  have hD : Closed G (X \ U) (K \ U) := by
    constructor
    · intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨hcl.1 hx.1, hx.2⟩
    · intro x hx y hy hxy
      rw [Finset.mem_sdiff] at hx hy ⊢
      exact ⟨hcl.2 x hx.1 y hy.1 hxy, hy.2⟩
  have hrest : (X \ U) \ (K \ U) = X \ K := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun hxK => h3 ⟨hxK, h2⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun hxU => h2 (hUK hxU)⟩, fun h3 => h2 h3.1⟩
  have h1 := (tk_split G X K hcl).2.mp hg
  have h2 := (tk_split G _ _ hD).2
  rw [hrest] at h2
  exact h2.mpr ⟨hgK, h1.2⟩

lemma oddpick (X : Finset V) (hg : Good G X)
    (hodd : Odd (X.filter (fun x => Even (dg G X x))).card) :
    ∃ U, U ⊆ X.filter (fun x => Even (dg G X x)) ∧ Odd U.card ∧ Good G (X \ U) := by
  set N := X.filter (fun x => Even (dg G X x)) with hN
  by_cases ha : ∃ u ∈ N, ∃ K : Finset V, u ∈ K ∧ Closed G X K ∧ Good G (K.erase u)
  · obtain ⟨u, huN, K, huK, hcl, hgK⟩ := ha
    refine ⟨{u}, Finset.singleton_subset_iff.mpr huN, by simp, ?_⟩
    refine OP_glue G X K {u} hcl hg (Finset.singleton_subset_iff.mpr huK) ?_
    rw [Finset.sdiff_singleton_eq_erase]
    exact hgK
  · push Not at ha
    obtain ⟨a, haN, hpar⟩ := tk_parity G X N (Finset.filter_subset _ _) hodd
    have haX : a ∈ X := (Finset.mem_filter.mp haN).1
    obtain ⟨K, haK, hcl, hconn, hmem⟩ := tk_comp G X a haX
    have hdeg := (tk_closed G X K hcl).1
    have hKodd := hpar K hmem
    have hevK : ∀ x ∈ K, (Even (dg G K x) ↔ x ∈ N ∩ K) := by
      intro x hx
      rw [hdeg x hx, Finset.mem_inter, hN, Finset.mem_filter]
      exact ⟨fun h => ⟨⟨hcl.1 hx, h⟩, hx⟩, fun h => h.1.2⟩
    have hgood := lemma1 G K hconn
      ⟨a, haK, (hevK a haK).mpr (Finset.mem_inter.mpr ⟨haN, haK⟩)⟩
      (fun u hu hue => by
        have huNK := (hevK u hu).mp hue
        exact ha u (Finset.mem_inter.mp huNK).1 K hu hcl)
    have heq : K.filter (fun x => ¬ Even (dg G K x)) = K \ (N ∩ K) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hx, hne⟩
        exact ⟨hx, fun h => hne ((hevK x hx).mpr h)⟩
      · rintro ⟨hx, hne⟩
        exact ⟨hx, fun h => hne ((hevK x hx).mp h)⟩
    rw [heq] at hgood
    exact ⟨N ∩ K, Finset.inter_subset_left, hKodd,
      OP_glue G X K (N ∩ K) hcl hg Finset.inter_subset_right hgood⟩

end OP

-- lemma2
section LB

/-- A peculiar component of `C - w` (`C` connected) contains a neighbour of `w`, and that
neighbour has odd degree in `C - w`. -/
lemma LB_exit (C : Finset V) (hc : Conn G C) (w : V) (hw : w ∈ C) (a : V)
    (hp : Pec G (C.erase w) a) :
    ∃ y, Rch G (C.erase w) a y ∧ y ∈ C.erase w ∧ G.Adj y w ∧ Odd (dg G (C.erase w) y) := by
  obtain ⟨ha, hp⟩ := hp
  have haC := (Finset.mem_erase.mp ha).2
  rcases tk_exit G C w (hc a haC w hw) ha with h | ⟨y, hy, hyC, hyw⟩
  · exact absurd (rch_mem G h ha) (Finset.notMem_erase w C)
  · exact ⟨y, hy, hyC, hyw, hp y hy⟩

/-- The peculiar component `P` of `C - w` and a neighbour `v ∈ P` of `w`. -/
lemma LB_setup (C : Finset V) (hc : Conn G C) (w : V) (hw : w ∈ C)
    (hbad : ¬ Good G (C.erase w)) :
    ∃ (P : Finset V) (v : V), Closed G (C.erase w) P ∧ Conn G P ∧
      (∀ x ∈ P, Odd (dg G P x)) ∧ v ∈ P ∧ G.Adj v w := by
  unfold Good at hbad
  rw [not_forall] at hbad
  obtain ⟨a, ha⟩ := hbad
  have hpec : Pec G (C.erase w) a := not_not.mp ha
  obtain ⟨P, haP, hcl, hconn, hmem⟩ := tk_comp G (C.erase w) a hpec.1
  obtain ⟨hdeg, -, -⟩ := tk_closed G (C.erase w) P hcl
  obtain ⟨y, hy, -, hyw, -⟩ := LB_exit G C hc w hw a hpec
  refine ⟨P, y, hcl, hconn, fun x hx => ?_, (hmem y).mpr hy, hyw⟩
  rw [hdeg x hx]
  exact hpec.2 x ((hmem x).mp hx)

/-- Case 1: the rest of `C - w` is good; remove `v` and `w`. -/
lemma LB_case1 (C : Finset V) (w : V) (P : Finset V) (v : V)
    (hcl : Closed G (C.erase w) P) (hvP : v ∈ P) (hX : Good G (P.erase v))
    (hR : Good G ((C.erase w) \ P)) : Good G ((C.erase v) \ {w}) := by
  apply tk_cover
  intro a ha
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton] at ha
  obtain ⟨⟨hav, haC⟩, haw⟩ := ha
  by_cases haP : a ∈ P
  · refine ⟨P.erase v, Finset.mem_erase.mpr ⟨hav, haP⟩, ⟨?_, ?_⟩, hX⟩
    · intro x hx
      obtain ⟨hxv, hxP⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxw, hxC⟩ := Finset.mem_erase.mp (hcl.1 hxP)
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      exact ⟨⟨hxv, hxC⟩, hxw⟩
    · intro x hx y hy hxy
      obtain ⟨hxv, hxP⟩ := Finset.mem_erase.mp hx
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton] at hy
      obtain ⟨⟨hyv, hyC⟩, hyw⟩ := hy
      exact Finset.mem_erase.mpr
        ⟨hyv, hcl.2 x hxP y (Finset.mem_erase.mpr ⟨hyw, hyC⟩) hxy⟩
  · refine ⟨(C.erase w) \ P,
      Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨haw, haC⟩, haP⟩, ⟨?_, ?_⟩, hR⟩
    · intro x hx
      obtain ⟨hx1, hxP⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hxw, hxC⟩ := Finset.mem_erase.mp hx1
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
      exact ⟨⟨fun h => hxP (h ▸ hvP), hxC⟩, hxw⟩
    · intro x hx y hy hxy
      obtain ⟨hx1, hxP⟩ := Finset.mem_sdiff.mp hx
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton] at hy
      obtain ⟨⟨hyv, hyC⟩, hyw⟩ := hy
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hyw, hyC⟩,
        fun hyP => hxP (hcl.2 y hyP x hx1 hxy.symm)⟩

/-- Case 2: there is a vertex `y'` outside `P`, adjacent to `w`, of even degree in `C`; remove
`v` and a set `U` of vertices of `P - v` such that `(P - v) \ U` is good. -/
lemma LB_case2 (C : Finset V) (hc : Conn G C) (w : V) (hw : w ∈ C) (P : Finset V) (v : V)
    (hcl : Closed G (C.erase w) P) (hvP : v ∈ P) (U : Finset V) (hU : U ⊆ P.erase v)
    (hg : Good G ((P.erase v) \ U)) (y' : V) (hy' : y' ∈ (C.erase w) \ P)
    (hy'w : G.Adj y' w) (hy'e : Even (dg G C y')) : Good G ((C.erase v) \ U) := by
  rw [tk_good_iff]
  have hPC : ∀ x ∈ P, x ∈ C ∧ x ≠ w := fun x hx =>
    ⟨(Finset.mem_erase.mp (hcl.1 hx)).2, (Finset.mem_erase.mp (hcl.1 hx)).1⟩
  have hmemT : ∀ x, x ∈ (C.erase v) \ U ↔ x ∈ C ∧ x ≠ v ∧ x ∉ U := by
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    tauto
  have hmemX : ∀ x, x ∈ (P.erase v) \ U ↔ x ∈ P ∧ x ≠ v ∧ x ∉ U := by
    intro x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    tauto
  have hUP : ∀ x ∈ U, x ∈ P := fun x hx => (Finset.mem_erase.mp (hU hx)).2
  have hXT : ∀ x ∈ (P.erase v) \ U, x ∈ (C.erase v) \ U := by
    intro x hx
    rw [hmemX] at hx
    rw [hmemT]
    exact ⟨(hPC x hx.1).1, hx.2⟩
  have hwT : w ∈ (C.erase v) \ U :=
    (hmemT w).mpr ⟨hw, fun h => (hPC v hvP).2 h.symm, fun h => (hPC w (hUP w h)).2 rfl⟩
  obtain ⟨hy'1, hy'P⟩ := Finset.mem_sdiff.mp hy'
  obtain ⟨hy'nw, hy'C⟩ := Finset.mem_erase.mp hy'1
  have hy'T : y' ∈ (C.erase v) \ U :=
    (hmemT y').mpr ⟨hy'C, fun h => hy'P (h ▸ hvP), fun h => hy'P (hUP y' h)⟩
  have hy'deg : dg G ((C.erase v) \ U) y' = dg G C y' := by
    unfold dg
    congr 1
    ext z
    simp only [Finset.mem_filter, hmemT]
    constructor
    · exact fun ⟨h1, h2⟩ => ⟨h1.1, h2⟩
    · intro ⟨h1, h2⟩
      have hzP : z ∉ P := fun hz => hy'P (hcl.2 z hz y' hy'1 h2.symm)
      exact ⟨⟨h1, fun h => hzP (h ▸ hvP), fun h => hzP (hUP z h)⟩, h2⟩
  have hfromw : ∀ a, Rch G ((C.erase v) \ U) a w →
      ∃ b, Rch G ((C.erase v) \ U) a b ∧ Even (dg G ((C.erase v) \ U) b) := by
    intro a ha
    refine ⟨y', Relation.ReflTransGen.tail ha ⟨hwT, hy'T, hy'w.symm⟩, ?_⟩
    rw [hy'deg]
    exact hy'e
  intro a ha
  by_cases haw : a = w
  · rw [haw]
    exact hfromw w Relation.ReflTransGen.refl
  have haT := (hmemT a).mp ha
  by_cases haP : a ∈ P
  · have haX : a ∈ (P.erase v) \ U := (hmemX a).mpr ⟨haP, haT.2⟩
    obtain ⟨b, hab, hbe⟩ := (tk_good_iff G _).mp hg a haX
    have hbX := rch_mem G hab haX
    have hsub : ∀ x y, Lk G ((P.erase v) \ U) x y → Lk G ((C.erase v) \ U) x y :=
      fun x y hxy => ⟨hXT x hxy.1, hXT y hxy.2.1, hxy.2.2⟩
    have hab' : Rch G ((C.erase v) \ U) a b := Relation.ReflTransGen.mono hsub a b hab
    by_cases hbw : G.Adj b w
    · exact hfromw a (Relation.ReflTransGen.tail hab' ⟨hXT b hbX, hwT, hbw⟩)
    · refine ⟨b, hab', ?_⟩
      have hbP : b ∈ P := ((hmemX b).mp hbX).1
      have hdeg : dg G ((C.erase v) \ U) b = dg G ((P.erase v) \ U) b := by
        unfold dg
        congr 1
        ext z
        simp only [Finset.mem_filter, hmemT, hmemX]
        constructor
        · intro ⟨h1, h2⟩
          have hzw : z ≠ w := fun h => hbw (h ▸ h2)
          exact ⟨⟨hcl.2 b hbP z (Finset.mem_erase.mpr ⟨hzw, h1.1⟩) h2, h1.2⟩, h2⟩
        · exact fun ⟨h1, h2⟩ => ⟨⟨(hPC z h1.1).1, h1.2⟩, h2⟩
      rw [hdeg]
      exact hbe
  · have haCw : a ∈ C.erase w := Finset.mem_erase.mpr ⟨haw, haT.1⟩
    rcases tk_exit G C w (hc a haT.1 w hw) haCw with h | ⟨y, hy, hyC, hyw⟩
    · exact absurd (rch_mem G h haCw) (Finset.notMem_erase w C)
    · have hR := (tk_split G (C.erase w) P hcl).1
      have haR : a ∈ (C.erase w) \ P := Finset.mem_sdiff.mpr ⟨haCw, haP⟩
      have hy2 := ((tk_closed G _ _ hR).2.1 a haR y).mp hy
      have hyR := rch_mem G hy2 haR
      have hRT : ∀ x ∈ (C.erase w) \ P, x ∈ (C.erase v) \ U := by
        intro x hx
        obtain ⟨hx1, hxP⟩ := Finset.mem_sdiff.mp hx
        exact (hmemT x).mpr
          ⟨(Finset.mem_erase.mp hx1).2, fun h => hxP (h ▸ hvP), fun h => hxP (hUP x h)⟩
      have hsub : ∀ x y, Lk G ((C.erase w) \ P) x y → Lk G ((C.erase v) \ U) x y :=
        fun x y hxy => ⟨hRT x hxy.1, hRT y hxy.2.1, hxy.2.2⟩
      have hy3 : Rch G ((C.erase v) \ U) a y := Relation.ReflTransGen.mono hsub a y hy2
      exact hfromw a (Relation.ReflTransGen.tail hy3 ⟨hRT y hyR, hwT, hyw⟩)

/-- LEMMA `lemma2`. If `C` is connected and `C - w` is not good for some `w ∈ C`, then `C` has a
reduction to a good set. -/
lemma lemma2 (C : Finset V) (hc : Conn G C) (w : V) (hw : w ∈ C)
    (hbad : ¬ Good G (C.erase w)) :
    ∃ v U, Star G C v U ∧ Good G ((C.erase v) \ U) := by
  obtain ⟨P, v, hcl, hconn, hoddP, hvP, hvw⟩ := LB_setup G C hc w hw hbad
  have hvC : v ∈ C := (Finset.mem_erase.mp (hcl.1 hvP)).2
  obtain ⟨hdegP, -, -⟩ := tk_closed G (C.erase w) P hcl
  have hev : Even (dg G C v) := by
    rw [← dg_erase_adj G C w v hw hvw, ← hdegP v hvP]
    exact (hoddP v hvP).add_one
  have hX : Good G (P.erase v) := pec_erase G P hconn hoddP v hvP
  by_cases hR : Good G ((C.erase w) \ P)
  · refine ⟨v, {w}, ⟨hvC, ?_, hev, Or.inl (by simp)⟩, LB_case1 G C w P v hcl hvP hX hR⟩
    exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hw, hvw⟩)
  · -- a second peculiar component, with a neighbour `y'` of `w`
    obtain ⟨hRcl, -⟩ := tk_split G (C.erase w) P hcl
    unfold Good at hR
    rw [not_forall] at hR
    obtain ⟨a', ha'⟩ := hR
    have hpec' : Pec G ((C.erase w) \ P) a' := not_not.mp ha'
    have ha'R : a' ∈ (C.erase w) \ P := hpec'.1
    obtain ⟨-, hrch, hpeq⟩ := tk_closed G (C.erase w) ((C.erase w) \ P) hRcl
    have hpec : Pec G (C.erase w) a' := (hpeq a' ha'R).mpr hpec'
    obtain ⟨y', hy'r, hy'Cw, hy'w, hy'o⟩ := LB_exit G C hc w hw a' hpec
    have hy'R : y' ∈ (C.erase w) \ P := rch_mem G ((hrch a' ha'R y').mp hy'r) ha'R
    have hy'e : Even (dg G C y') := by
      rw [← dg_erase_adj G C w y' hw hy'w]
      exact hy'o.add_one
    -- the vertices of even degree of `P - v` are the neighbours of `v` in `P`
    have hfilt : (P.erase v).filter (fun x => Even (dg G (P.erase v) x)) =
        P.filter (G.Adj v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · intro ⟨⟨_, hxP⟩, he⟩
        refine ⟨hxP, ?_⟩
        by_contra hadj
        have h1 := dg_erase_not_adj G P v x (fun h => hadj h.symm)
        rw [h1] at he
        exact Nat.not_odd_iff_even.mpr he (hoddP x hxP)
      · intro ⟨hxP, hadj⟩
        refine ⟨⟨fun h => G.ne_of_adj hadj h.symm, hxP⟩, ?_⟩
        have h1 := hoddP x hxP
        rw [← dg_erase_adj G P v x hvP hadj.symm] at h1
        exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h1)
    have hcount : Odd ((P.erase v).filter (fun x => Even (dg G (P.erase v) x))).card := by
      rw [hfilt]
      exact hoddP v hvP
    obtain ⟨U, hUsub, hUodd, hUgood⟩ := oddpick G (P.erase v) hX hcount
    have hUX : U ⊆ P.erase v := hUsub.trans (Finset.filter_subset _ _)
    rw [hfilt] at hUsub
    refine ⟨v, U, ⟨hvC, ?_, hev, Or.inl hUodd⟩,
      LB_case2 G C hc w hw P v hcl hvP U hUX hUgood y' hy'R hy'w hy'e⟩
    intro u hu
    obtain ⟨huP, huadj⟩ := Finset.mem_filter.mp (hUsub hu)
    exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hcl.1 huP)).2, huadj⟩

end LB

/-- The outcome of `star_a`: a component `K` of `C - v` with an odd number of neighbours of `v`,
and a vertex `u ∈ K` of even degree, not adjacent to `v`, adjacent to all neighbours of `v` in
`K`, such that after removing `u` and any such neighbour `w` every peculiar component of the rest
of `K` contains a neighbour of `v`. -/
def Spoke (C : Finset V) (v : V) (K : Finset V) (u : V) : Prop :=
  Closed G (C.erase v) K ∧ Conn G K ∧ Odd (K.filter (G.Adj v)).card ∧ u ∈ K ∧ ¬ G.Adj v u ∧
    Even (dg G K u) ∧ ∀ w ∈ K.filter (G.Adj v), G.Adj u w ∧
      ∀ a, Pec G ((K.erase u).erase w) a →
        ∃ s ∈ K.filter (G.Adj v), Rch G ((K.erase u).erase w) a s

-- star_a
section SA

/-- LEMMA `star_a` (TAG `SA`). Let `C` be connected with `C - w` good for every `w`, and `v ∈ C`
such that no `C - v - u` with `u` a neighbour of `v` is good. Then either removing `v` with all
its neighbours leaves a good set, or there is a spoke. -/
lemma star_a (C : Finset V) (hc : Conn G C) (hstar : ∀ w ∈ C, Good G (C.erase w)) (v : V)
    (hv : v ∈ C) (hno : ∀ u ∈ C.filter (G.Adj v), ¬ Good G ((C.erase v).erase u)) :
    Good G ((C.erase v) \ C.filter (G.Adj v)) ∨ ∃ K u, Spoke G C v K u := by
  by_cases hg : Good G ((C.erase v) \ C.filter (G.Adj v))
  · exact Or.inl hg
  right
  have hg' := hg
  simp only [Good, not_forall, not_not] at hg'
  obtain ⟨a, hpa⟩ := hg'
  have haCv : a ∈ C.erase v := (Finset.mem_sdiff.mp hpa.1).1
  have hav : ¬ G.Adj v a := fun h => (Finset.mem_sdiff.mp hpa.1).2
    (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp haCv).2, h⟩)
  obtain ⟨K, haK, hKcl, hKconn, hKmem⟩ := tk_comp G (C.erase v) a haCv
  have hKC : K ⊆ C := hKcl.1.trans (Finset.erase_subset v C)
  -- `K \ S` is not good
  have hKS : ¬ Good G (K \ K.filter (G.Adj v)) := by
    have hcl : Closed G ((C.erase v) \ C.filter (G.Adj v)) (K \ K.filter (G.Adj v)) := by
      constructor
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hx ⊢
        exact ⟨hKcl.1 hx.1, fun _ => hx.2 hx.1⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hx hy ⊢
        exact ⟨hKcl.2 x hx.1 y hy.1 hxy, fun _ => hy.2 (Finset.mem_erase.mp hy.1).2⟩
    have haKS : a ∈ K \ K.filter (G.Adj v) := by
      simp only [Finset.mem_sdiff, Finset.mem_filter, not_and]
      exact ⟨haK, fun _ => hav⟩
    intro hgood
    exact hgood a (((tk_closed G _ _ hcl).2.2 a haKS).mp hpa)
  -- `S` is nonempty
  have hne : (K.filter (G.Adj v)).Nonempty := by
    rcases tk_exit G C v (hc a (hKC haK) v hv) haCv with h | ⟨y, hy, -, hyv⟩
    · exact absurd (rch_mem G h haCv) (Finset.notMem_erase v C)
    · exact ⟨y, Finset.mem_filter.mpr ⟨(hKmem y).mpr hy, hyv.symm⟩⟩
  -- (h2)
  have hCvK : Good G ((C.erase v) \ K) := ((tk_split G _ K hKcl).2.mp (hstar v hv)).2
  have h2 : ∀ u ∈ K.filter (G.Adj v), ¬ Good G (K.erase u) := by
    intro u hu hgood
    obtain ⟨huK, hvu⟩ := Finset.mem_filter.mp hu
    apply hno u (Finset.mem_filter.mpr ⟨hKC huK, hvu⟩)
    have hcl : Closed G ((C.erase v).erase u) (K.erase u) := by
      constructor
      · exact Finset.erase_subset_erase u hKcl.1
      · intro x hx y hy hxy
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,
          hKcl.2 x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2 hxy⟩
    have hrest : ((C.erase v).erase u) \ (K.erase u) = (C.erase v) \ K := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · intro h
        exact ⟨⟨h.1.2.1, h.1.2.2⟩, fun hk => h.2 ⟨h.1.1, hk⟩⟩
      · intro h
        exact ⟨⟨fun hxu => h.2 (hxu ▸ huK), h.1.1, h.1.2⟩, fun h' => h.2 h'.2⟩
    have hsp := (tk_split G _ _ hcl).2
    rw [hrest] at hsp
    exact hsp.mpr ⟨hgood, hCvK⟩
  -- (h3)
  have h3 : ∀ w ∈ K, ∀ a', Pec G (K.erase w) a' →
      ∃ s ∈ K.filter (G.Adj v), Rch G (K.erase w) a' s := by
    intro w hw a' hpa'
    by_contra hns
    push Not at hns
    obtain ⟨D, haD, hDcl, -, hDmem⟩ := tk_comp G (K.erase w) a' hpa'.1
    have hDC : Closed G (C.erase w) D := by
      constructor
      · exact hDcl.1.trans (Finset.erase_subset_erase w hKC)
      · intro x hx y hy hxy
        have hxr := (hDmem x).mp hx
        have hxKw := hDcl.1 hx
        by_cases hyv : y = v
        · rw [hyv] at hxy
          exact absurd hxr
            (hns x (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hxKw).2, hxy.symm⟩))
        · have hyK : y ∈ K := hKcl.2 x (Finset.mem_erase.mp hxKw).2 y
            (Finset.mem_erase.mpr ⟨hyv, (Finset.mem_erase.mp hy).2⟩) hxy
          exact hDcl.2 x hx y (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, hyK⟩) hxy
    have hpD : Pec G D a' := ((tk_closed G _ _ hDcl).2.2 a' haD).mp hpa'
    exact hstar w (hKC hw) a' (((tk_closed G _ _ hDC).2.2 a' haD).mpr hpD)
  obtain ⟨hodd, u, huKS, hue, hrest⟩ :=
    core G K (K.filter (G.Adj v)) hKconn (Finset.filter_subset _ _) hne h2 h3 hKS
  obtain ⟨huK, huS⟩ := Finset.mem_sdiff.mp huKS
  exact ⟨K, u, hKcl, hKconn, hodd, huK, fun h => huS (Finset.mem_filter.mpr ⟨huK, h⟩), hue,
    hrest⟩

end SA

-- star_b
section SB

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reachability is monotone in the vertex set. -/
lemma SB_rch_mono {S T : Finset V} (h : S ⊆ T) {a b : V} (hab : Rch G S a b) : Rch G T a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy => ⟨h hxy.1, h hxy.2.1, hxy.2.2⟩) a b hab

/-- The second reduction of `star_b`: if `K` is a union of components of `C - v` with an odd
number of neighbours of `v`, and all vertices of `C - v` outside `K` have odd degree in `C`, then
some reduction at `v` removing an odd set of neighbours outside `K` leaves a good set. -/
lemma SB_second (C : Finset V) (v : V) (hv : v ∈ C) (hev : Even (dg G C v))
    (hgood : Good G (C.erase v)) (K : Finset V) (hcl : Closed G (C.erase v) K)
    (hS : Odd (K.filter (G.Adj v)).card)
    (hX : ∀ x ∈ (C.erase v) \ K, Odd (dg G C x)) :
    ∃ U, Star G C v U ∧ Good G ((C.erase v) \ U) := by
  obtain ⟨hXcl, hsplit⟩ := tk_split G (C.erase v) K hcl
  obtain ⟨hgK, hgX⟩ := hsplit.mp hgood
  have hdegX := (tk_closed G (C.erase v) _ hXcl).1
  -- the vertices of even degree of `X` are the neighbours of `v` in `X`
  have hfil : ((C.erase v) \ K).filter (fun x => Even (dg G ((C.erase v) \ K) x)) =
      ((C.erase v) \ K).filter (G.Adj v) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨hx, ?_⟩
      by_contra hna
      have h1 := dg_erase_not_adj G C v x (fun h => hna h.symm)
      rw [hdegX x hx, h1] at he
      exact Nat.not_odd_iff_even.mpr he (hX x hx)
    · rintro ⟨hx, ha⟩
      refine ⟨hx, ?_⟩
      have h1 := dg_erase_adj G C v x hv ha.symm
      have h2 := hX x hx
      rw [← h1] at h2
      rw [hdegX x hx]
      exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp h2)
  -- their number is odd
  have hcard : Odd (((C.erase v) \ K).filter (G.Adj v)).card := by
    have hsub : K.filter (G.Adj v) ⊆ C.filter (G.Adj v) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_erase.mp (hcl.1 hx.1)).2, hx.2⟩
    have heq : ((C.erase v) \ K).filter (G.Adj v) = C.filter (G.Adj v) \ K.filter (G.Adj v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩
        exact ⟨⟨h2, h4⟩, fun h => h3 h.1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun hxv => ?_, h1⟩, fun hxK => h3 ⟨hxK, h2⟩⟩, h2⟩
        rw [hxv] at h2
        exact G.irrefl h2
    have hadd := Finset.card_sdiff_add_card_eq_card hsub
    rw [heq]
    have hev' : Even (C.filter (G.Adj v)).card := hev
    rw [← hadd] at hev'
    obtain ⟨k, hk⟩ := hS
    obtain ⟨m, hm⟩ := hev'
    exact ⟨m - k - 1, by omega⟩
  obtain ⟨U, hU, hUodd, hUgood⟩ := oddpick G _ hgX (by rw [hfil]; exact hcard)
  rw [hfil] at hU
  have hUX : ∀ x ∈ U, x ∈ C.erase v ∧ x ∉ K ∧ G.Adj v x := by
    intro x hx
    have h1 := Finset.mem_filter.mp (hU hx)
    have h2 := Finset.mem_sdiff.mp h1.1
    exact ⟨h2.1, h2.2, h1.2⟩
  refine ⟨U, ⟨hv, ?_, hev, Or.inl hUodd⟩, ?_⟩
  · intro x hx
    obtain ⟨h1, -, h3⟩ := hUX x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp h1).2, h3⟩
  · have hD : Closed G ((C.erase v) \ U) K := by
      constructor
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hcl.1 hx, fun hxU => (hUX x hxU).2.1 hx⟩
      · intro x hx y hy hxy
        exact hcl.2 x hx y (Finset.mem_sdiff.mp hy).1 hxy
    have hrest : ((C.erase v) \ U) \ K = ((C.erase v) \ K) \ U := by
      ext x
      simp only [Finset.mem_sdiff]
      tauto
    have h2 := (tk_split G _ _ hD).2
    rw [hrest] at h2
    exact h2.mpr ⟨hgK, hUgood⟩

/-- If the first reduction `u`, `{w}` of `star_b` leaves a peculiar component, then every vertex
of `C - v` outside `K` has odd degree in `C`. -/
lemma SB_odd (C : Finset V) (hc : Conn G C) (v : V) (hv : v ∈ C) (K : Finset V) (u w : V)
    (hcl : Closed G (C.erase v) K) (huK : u ∈ K) (hwK : w ∈ K)
    (hsp : ∀ a, Pec G ((K.erase u).erase w) a →
      ∃ s ∈ K.filter (G.Adj v), Rch G ((K.erase u).erase w) a s)
    (a : V) (ha : Pec G ((C.erase u).erase w) a) :
    ∀ x ∈ (C.erase v) \ K, Odd (dg G C x) := by
  obtain ⟨haT, hpec⟩ := ha
  have hKC : ∀ x ∈ K, x ∈ C ∧ x ≠ v := fun x hx =>
    ⟨(Finset.mem_erase.mp (hcl.1 hx)).2, (Finset.mem_erase.mp (hcl.1 hx)).1⟩
  have hvu : v ≠ u := fun h => (hKC u huK).2 h.symm
  have hvw : v ≠ w := fun h => (hKC w hwK).2 h.symm
  have hvT : v ∈ (C.erase u).erase w :=
    Finset.mem_erase.mpr ⟨hvw, Finset.mem_erase.mpr ⟨hvu, hv⟩⟩
  have hXcl := (tk_split G (C.erase v) K hcl).1
  have hXT : (C.erase v) \ K ⊆ (C.erase u).erase w := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    refine Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ hwK), Finset.mem_erase.mpr
      ⟨fun h => hx.2 (h ▸ huK), (Finset.mem_erase.mp hx.1).2⟩⟩
  have hKT : (K.erase u).erase w ⊆ (C.erase u).erase w := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hx.2.1, (hKC x hx.2.2).1⟩
  -- every vertex outside `K` reaches `v`
  have hXv : ∀ x ∈ (C.erase v) \ K, Rch G ((C.erase u).erase w) x v := by
    intro x hx
    have hxCv := (Finset.mem_sdiff.mp hx).1
    rcases tk_exit G C v (hc x (Finset.mem_erase.mp hxCv).2 v hv) hxCv with h | ⟨y, hy, -, hyv⟩
    · exact absurd (rch_mem G h hxCv) (Finset.notMem_erase v C)
    · have hy' := ((tk_closed G (C.erase v) _ hXcl).2.1 x hx y).mp hy
      have hyX := rch_mem G hy' hx
      exact Relation.ReflTransGen.tail (SB_rch_mono G hXT hy') ⟨hXT hyX, hvT, hyv⟩
  -- the base point reaches `v`
  have hav : Rch G ((C.erase u).erase w) a v := by
    by_cases hav0 : a = v
    · rw [hav0]
      exact Relation.ReflTransGen.refl
    have haC : a ∈ C.erase v :=
      Finset.mem_erase.mpr ⟨hav0, (Finset.mem_erase.mp (Finset.mem_erase.mp haT).2).2⟩
    by_cases haK : a ∈ K
    · by_contra hnr
      have haK' : a ∈ (K.erase u).erase w :=
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp haT).1, Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp haT).2).1, haK⟩⟩
      have hp : Pec G ((K.erase u).erase w) a := by
        refine ⟨haK', fun b hb => ?_⟩
        have hbK' := rch_mem G hb haK'
        have hbK : b ∈ K := (Finset.mem_erase.mp (Finset.mem_erase.mp hbK').2).2
        have hbT := SB_rch_mono G hKT hb
        have hdeg : dg G ((K.erase u).erase w) b = dg G ((C.erase u).erase w) b := by
          unfold dg
          congr 1
          ext y
          simp only [Finset.mem_filter]
          constructor
          · exact fun ⟨h1, h2⟩ => ⟨hKT h1, h2⟩
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h2⟩
            have hyv : y ≠ v := by
              rintro rfl
              exact hnr (Relation.ReflTransGen.tail hbT ⟨hKT hbK', h1, h2⟩)
            rw [Finset.mem_erase, Finset.mem_erase] at h1 ⊢
            exact ⟨h1.1, h1.2.1,
              hcl.2 b hbK y (Finset.mem_erase.mpr ⟨hyv, h1.2.2⟩) h2⟩
        rw [hdeg]
        exact hpec b hbT
      obtain ⟨s, hs, has⟩ := hsp a hp
      have hsK' := rch_mem G has haK'
      exact hnr (Relation.ReflTransGen.tail (SB_rch_mono G hKT has)
        ⟨hKT hsK', hvT, (Finset.mem_filter.mp hs).2.symm⟩)
    · exact hXv a (Finset.mem_sdiff.mpr ⟨haC, haK⟩)
  intro x hx
  have hxT : Rch G ((C.erase u).erase w) a x :=
    Relation.ReflTransGen.trans hav (rch_symm G (hXv x hx))
  have hodd := hpec x hxT
  have hx' := Finset.mem_sdiff.mp hx
  have hxw : ¬ G.Adj x w := fun h => hx'.2 (hcl.2 w hwK x hx'.1 h.symm)
  have hxu : ¬ G.Adj x u := fun h => hx'.2 (hcl.2 u huK x hx'.1 h.symm)
  rw [dg_erase_not_adj G (C.erase u) w x hxw, dg_erase_not_adj G C u x hxu] at hodd
  exact hodd

/-- LEMMA `star_b`. -/
lemma star_b (C : Finset V) (hc : Conn G C) (hstar : ∀ w ∈ C, Good G (C.erase w)) (v : V)
    (hv : v ∈ C) (hev : Even (dg G C v))
    (hno : ∀ u ∈ C.filter (G.Adj v), ¬ Good G ((C.erase v).erase u))
    (K : Finset V) (u : V) (hK : Spoke G C v K u) :
    ∃ v' U, Star G C v' U ∧ Good G ((C.erase v') \ U) := by
  have _ := hno
  obtain ⟨hcl, -, hS, huK, hvu, hue, hsp⟩ := hK
  have hne : (K.filter (G.Adj v)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hS
    simp at hS
  obtain ⟨w, hw⟩ := hne
  obtain ⟨huw, hspw⟩ := hsp w hw
  have hwK : w ∈ K := (Finset.mem_filter.mp hw).1
  have huC : u ∈ C := (Finset.mem_erase.mp (hcl.1 huK)).2
  have hwC : w ∈ C := (Finset.mem_erase.mp (hcl.1 hwK)).2
  by_cases hT : Good G ((C.erase u).erase w)
  · have hueC : Even (dg G C u) := by
      rw [← dg_erase_not_adj G C v u (fun h => hvu h.symm), ← (tk_closed G _ K hcl).1 u huK]
      exact hue
    refine ⟨u, {w}, ⟨huC, ?_, hueC, Or.inl (by simp)⟩, ?_⟩
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hwC, huw⟩)
    · rw [Finset.sdiff_singleton_eq_erase]
      exact hT
  · obtain ⟨a, ha⟩ := not_forall.mp hT
    have hX := SB_odd G C hc v hv K u w hcl huK hwK hspw a (not_not.mp ha)
    obtain ⟨U, hU, hUg⟩ := SB_second G C v hv hev (hstar v hv) K hcl hS hX
    exact ⟨v, U, hU, hUg⟩

end SB

/-- If `C` is connected, `C - w` is good for every `w ∈ C`, and `v ∈ C` has even degree in `C`,
then `C` has a reduction to a good set. -/
lemma starcase (C : Finset V) (hc : Conn G C) (hstar : ∀ w ∈ C, Good G (C.erase w)) (v : V)
    (hv : v ∈ C) (hev : Even (dg G C v)) :
    ∃ v' U, Star G C v' U ∧ Good G ((C.erase v') \ U) := by
  by_cases hno : ∀ u ∈ C.filter (G.Adj v), ¬ Good G ((C.erase v).erase u)
  · rcases star_a G C hc hstar v hv hno with hfull | ⟨K, u, hK⟩
    · exact ⟨v, C.filter (G.Adj v), ⟨hv, Finset.Subset.refl _, hev, Or.inr rfl⟩, hfull⟩
    · exact star_b G C hc hstar v hv hev hno K u hK
  · obtain ⟨u, hu⟩ := not_forall.mp hno
    obtain ⟨huN, hgood⟩ := Classical.not_imp.mp hu
    refine ⟨v, {u}, ⟨hv, Finset.singleton_subset_iff.mpr huN, hev, Or.inl (by simp)⟩, ?_⟩
    rw [Finset.sdiff_singleton_eq_erase]
    exact not_not.mp hgood

/-- A connected set with a vertex of even degree has a reduction to a good set (the proposition
of the Stack Exchange answer: a connected graph is starry iff it is not peculiar). -/
lemma key_conn (C : Finset V) (hc : Conn G C) (he : ∃ v ∈ C, Even (dg G C v)) :
    ∃ v U, Star G C v U ∧ Good G ((C.erase v) \ U) := by
  by_cases h : ∀ w ∈ C, Good G (C.erase w)
  · obtain ⟨v, hv, hev⟩ := he
    exact starcase G C hc h v hv hev
  · obtain ⟨w, hw⟩ := not_forall.mp h
    obtain ⟨hwC, hbad⟩ := Classical.not_imp.mp hw
    exact lemma2 G C hc w hwC hbad

/-- A nonempty good set has a reduction to a good set. -/
lemma key (S : Finset V) (hg : Good G S) (hne : S.Nonempty) :
    ∃ v U, Star G S v U ∧ Good G ((S.erase v) \ U) := by
  obtain ⟨a, haS⟩ := hne
  obtain ⟨K, haK, hcl, hconn, hmem⟩ := tk_comp G S a haS
  obtain ⟨hdeg, -, -⟩ := tk_closed G S K hcl
  obtain ⟨b, hab, hbe⟩ := (tk_good_iff G S).mp hg a haS
  have hbK : b ∈ K := (hmem b).mpr hab
  have hbe' : Even (dg G K b) := by
    rw [hdeg b hbK]
    exact hbe
  obtain ⟨v, U, ⟨hvK, hU, hev, hodd⟩, hgood⟩ := key_conn G K hconn ⟨b, hbK, hbe'⟩
  have hfilt : K.filter (G.Adj v) = S.filter (G.Adj v) := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hcl.1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hcl.2 v hvK y h1 h2, h2⟩⟩
  have hUK : U ⊆ K := hU.trans (Finset.filter_subset _ _)
  refine ⟨v, U, ⟨hcl.1 hvK, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hfilt]
    exact hU
  · rw [← hdeg v hvK]
    exact hev
  · rw [← hfilt]
    exact hodd
  · have hD : Closed G ((S.erase v) \ U) ((K.erase v) \ U) := by
      constructor
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_erase] at hx ⊢
        exact ⟨⟨hx.1.1, hcl.1 hx.1.2⟩, hx.2⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_sdiff, Finset.mem_erase] at hx hy ⊢
        exact ⟨⟨hy.1.1, hcl.2 x hx.1.2 y hy.1.2 hxy⟩, hy.2⟩
    have hrest : ((S.erase v) \ U) \ ((K.erase v) \ U) = S \ K := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · intro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨h2, fun hxK => h4 ⟨⟨h1, hxK⟩, h3⟩⟩
      · intro ⟨h1, h2⟩
        refine ⟨⟨⟨fun hxv => h2 (hxv ▸ hvK), h1⟩, fun hxU => h2 (hUK hxU)⟩, fun h4 => h2 h4.1.2⟩
    have h1 := (tk_split G S K hcl).2.mp hg
    have h2 := (tk_split G _ _ hD).2
    rw [hrest] at h2
    exact h2.mpr ⟨hgood, h1.2⟩

/-- Every good set can be removed completely. -/
theorem reduce_all (n : ℕ) : ∀ S : Finset V, S.card = n → Good G S →
    Relation.ReflTransGen (OMA.S_mse_5099016.ReductionStep G) S ∅ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hg
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact Relation.ReflTransGen.refl
    · obtain ⟨v, U, ⟨hv, hU, hev, hodd⟩, hT⟩ := key G S hg hne
      have hstep : OMA.S_mse_5099016.ReductionStep G S ((S.erase v) \ U) := by
        refine ⟨v, hv, U, ?_, ?_, hev, hodd, rfl⟩
        · exact hU.trans (Finset.filter_subset _ _)
        · intro u hu
          exact (Finset.mem_filter.mp (hU hu)).2
      have hlt : ((S.erase v) \ U).card < n := by
        rw [← hcard]
        exact Finset.card_lt_card
          (Finset.ssubset_of_subset_of_ssubset Finset.sdiff_subset (Finset.erase_ssubset hv))
      exact Relation.ReflTransGen.head hstep (ih _ hlt _ rfl hT)

end OMA.Redux

theorem OMA.solution : type_of% @OMA.S_mse_5099016.main := by
  intro V _ _ G _ hc he
  exact OMA.Redux.reduce_all G _ Finset.univ rfl (OMA.Redux.good_univ G hc he)
