import OMAStatements.S_mo_442518
import Mathlib

/-!
Disproof for mo-442518 at d = 3, on an explicit digraph with 12 vertices.

Vertices: 0 = s, 1 = t, 2 and 3 are the two connector vertices, 4..7 and 8..11 are two
bidirected 4-cliques. Arcs besides the cliques: s, t, 2, 3 are pairwise joined in both directions
except that 2 and 3 are not joined; 2 <-> 4 and 3 <-> 8; t -> 5 -> s and t -> 9 -> s.

Every s-t path has at most 2 arcs: a longer one starts s -> 2 (or s -> 3), then must enter the
clique 4..7 (or 8..11), and a clique can only be left towards s or towards its connector, both
already used.
-/

namespace OMA.S_mo_442518.Cex

/-- Out-neighbour lists of the counterexample. -/
def nbrs (v : Fin 12) : List (Fin 12) :=
  ([[1, 2, 3], [0, 2, 3, 5, 9], [0, 1, 4], [0, 1, 8], [5, 6, 7, 2], [4, 6, 7, 0], [4, 5, 7],
    [4, 5, 6], [9, 10, 11, 3], [8, 10, 11, 0], [8, 9, 11], [8, 9, 10]] :
      List (List (Fin 12))).getD v.val []

/-- The counterexample digraph. -/
def G : Digraph (Fin 12) where
  Adj u w := w ∈ nbrs u

instance decAdj : DecidableRel G.Adj := fun u w => inferInstanceAs (Decidable (w ∈ nbrs u))

lemma noLoops : ∀ v : Fin 12, ¬ G.Adj v v := by decide

set_option maxRecDepth 100000 in
lemma degrees : ∀ v : Fin 12, 3 ≤ outdegree G v ∧ 3 ≤ indegree G v := by decide

/-! Strong connectivity certificates.

The index `c : Fin 13` encodes the deleted vertex (`c = 12`: nothing deleted). `root c` is a
surviving vertex, `rkOut c` is the distance from the root and `rkIn c` the distance to the root
in the digraph with `c` deleted. -/

def root (c : Fin 13) : Fin 12 := if c.val = 0 then 1 else 0

def rkOut (c : Fin 13) (u : Fin 12) : ℕ :=
  (([[0, 0, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2], [0, 0, 1, 1, 2, 3, 3, 3, 2, 3, 3, 3],
     [0, 1, 0, 1, 3, 2, 3, 3, 2, 2, 3, 3], [0, 1, 1, 0, 2, 2, 3, 3, 3, 2, 3, 3],
     [0, 1, 1, 1, 0, 2, 3, 3, 2, 2, 3, 3], [0, 1, 1, 1, 2, 0, 3, 3, 2, 2, 3, 3],
     [0, 1, 1, 1, 2, 2, 0, 3, 2, 2, 3, 3], [0, 1, 1, 1, 2, 2, 3, 0, 2, 2, 3, 3],
     [0, 1, 1, 1, 2, 2, 3, 3, 0, 2, 3, 3], [0, 1, 1, 1, 2, 2, 3, 3, 2, 0, 3, 3],
     [0, 1, 1, 1, 2, 2, 3, 3, 2, 2, 0, 3], [0, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 0],
     [0, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3]] : List (List ℕ)).getD c.val []).getD u.val 0

def rkIn (c : Fin 13) (u : Fin 12) : ℕ :=
  (([[0, 0, 1, 1, 2, 3, 3, 3, 2, 3, 3, 3], [0, 0, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2],
     [0, 1, 0, 1, 2, 1, 2, 2, 2, 1, 2, 2], [0, 1, 1, 0, 2, 1, 2, 2, 2, 1, 2, 2],
     [0, 1, 1, 1, 0, 1, 2, 2, 2, 1, 2, 2], [0, 1, 1, 1, 2, 0, 3, 3, 2, 1, 2, 2],
     [0, 1, 1, 1, 2, 1, 0, 2, 2, 1, 2, 2], [0, 1, 1, 1, 2, 1, 2, 0, 2, 1, 2, 2],
     [0, 1, 1, 1, 2, 1, 2, 2, 0, 1, 2, 2], [0, 1, 1, 1, 2, 1, 2, 2, 2, 0, 3, 3],
     [0, 1, 1, 1, 2, 1, 2, 2, 2, 1, 0, 2], [0, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 0],
     [0, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2]] : List (List ℕ)).getD c.val []).getD u.val 0

set_option maxRecDepth 100000 in
lemma certOut : ∀ c : Fin 13, ∀ u : Fin 12, u.val ≠ c.val →
    u = root c ∨ ∃ p : Fin 12, p.val ≠ c.val ∧ G.Adj p u ∧ rkOut c p < rkOut c u := by decide

set_option maxRecDepth 100000 in
lemma certIn : ∀ c : Fin 13, ∀ u : Fin 12, u.val ≠ c.val →
    u = root c ∨ ∃ p : Fin 12, p.val ≠ c.val ∧ G.Adj u p ∧ rkIn c p < rkIn c u := by decide

/-- If every vertex of `X` other than `r` has an `R`-predecessor in `X` of smaller rank, then
`r` reaches every vertex of `X`. -/
lemma reach_from {V : Type} (R : V → V → Prop) (X : V → Prop) (r : V) (rk : V → ℕ)
    (h : ∀ u, X u → u = r ∨ ∃ p, X p ∧ R p u ∧ rk p < rk u) :
    ∀ n u, rk u = n → X u → Relation.ReflTransGen R r u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hu
    rcases h u hu with h1 | ⟨p, hp, hR, hlt⟩
    · rw [h1]
    · exact (ih (rk p) (hn ▸ hlt) p rfl hp).tail hR

/-- If every vertex of `X` other than `r` has an `R`-successor in `X` of smaller rank, then
every vertex of `X` reaches `r`. -/
lemma reach_to {V : Type} (R : V → V → Prop) (X : V → Prop) (r : V) (rk : V → ℕ)
    (h : ∀ u, X u → u = r ∨ ∃ p, X p ∧ R u p ∧ rk p < rk u) :
    ∀ n u, rk u = n → X u → Relation.ReflTransGen R u r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hu
    rcases h u hu with h1 | ⟨p, hp, hR, hlt⟩
    · rw [h1]
    · exact Relation.ReflTransGen.head hR (ih (rk p) (hn ▸ hlt) p rfl hp)

/-- The digraph with the vertex encoded by `c` deleted is strongly connected. -/
lemma strongC (c : Fin 13) : ∀ u w : Fin 12, u.val ≠ c.val → w.val ≠ c.val →
    Relation.ReflTransGen
      (fun a b : Fin 12 => G.Adj a b ∧ a.val ≠ c.val ∧ b.val ≠ c.val) u w := by
  intro u w hu hw
  have h1 : Relation.ReflTransGen
      (fun a b : Fin 12 => G.Adj a b ∧ a.val ≠ c.val ∧ b.val ≠ c.val) u (root c) := by
    refine reach_to _ (fun x : Fin 12 => x.val ≠ c.val) (root c) (rkIn c) ?_ _ u rfl hu
    intro x hx
    rcases certIn c x hx with h | ⟨p, hp, hA, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, ⟨hA, hx, hp⟩, hlt⟩
  have h2 : Relation.ReflTransGen
      (fun a b : Fin 12 => G.Adj a b ∧ a.val ≠ c.val ∧ b.val ≠ c.val) (root c) w := by
    refine reach_from _ (fun x : Fin 12 => x.val ≠ c.val) (root c) (rkOut c) ?_ _ w rfl hw
    intro x hx
    rcases certOut c x hx with h | ⟨p, hp, hA, hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, ⟨hA, hp, hx⟩, hlt⟩
  exact h1.trans h2

lemma twoStrong : IsKStrong G 2 := by
  refine ⟨by simp, ?_⟩
  intro S hS u w hu hw
  have hS' : S.card = 0 ∨ S.card = 1 := by omega
  rcases hS' with h0 | h1
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
    subst hS0
    have key := strongC (Fin.last 12) u w (Nat.ne_of_lt u.isLt) (Nat.ne_of_lt w.isLt)
    clear hw
    induction key with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      exact ih.tail ⟨hab.1, Finset.notMem_empty _, Finset.notMem_empty _⟩
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
    have hx : x.val < 13 := by have := x.isLt; omega
    have hux : u.val ≠ x.val := fun h => hu (Finset.mem_singleton.mpr (Fin.ext h))
    have hwx : w.val ≠ x.val := fun h => hw (Finset.mem_singleton.mpr (Fin.ext h))
    have key := strongC ⟨x.val, hx⟩ u w hux hwx
    clear hw hwx
    induction key with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      exact ih.tail ⟨hab.1, fun ha => hab.2.1 (congrArg Fin.val (Finset.mem_singleton.mp ha)),
        fun hb => hab.2.2 (congrArg Fin.val (Finset.mem_singleton.mp hb))⟩

/-! No path from 0 to 1 with three or more arcs. -/

/-- The clique attached to the connector `b` (4..7 for `b = 2`, 8..11 otherwise). -/
def trap (b x : Fin 12) : Bool :=
  if b.val = 2 then (decide (4 ≤ x.val) && decide (x.val ≤ 7)) else decide (8 ≤ x.val)

lemma out_s : ∀ y : Fin 12, G.Adj 0 y → y = 1 ∨ y = 2 ∨ y = 3 := by decide

lemma out_b : ∀ b y : Fin 12, (b = 2 ∨ b = 3) → G.Adj b y → y = 0 ∨ y = 1 ∨ trap b y = true := by
  decide

set_option maxRecDepth 100000 in
lemma trap_step : ∀ b x y : Fin 12, (b = 2 ∨ b = 3) → trap b x = true → G.Adj x y →
    trap b y = true ∨ y = 0 ∨ y = b := by decide

lemma trap_t : ∀ b : Fin 12, (b = 2 ∨ b = 3) → trap b 1 = false := by decide

lemma noLongPath : ¬ HasPathOfLengthAtLeast G 0 1 3 := by
  rintro ⟨ℓ, hℓ, p, hinj, h0, hlast, hadj⟩
  have adj : ∀ i (h : i < ℓ), G.Adj (p ⟨i, by omega⟩) (p ⟨i + 1, by omega⟩) :=
    fun i h => hadj ⟨i, h⟩
  have inj : ∀ i j (hi : i < ℓ + 1) (hj : j < ℓ + 1), p ⟨i, hi⟩ = p ⟨j, hj⟩ → i = j :=
    fun i j hi hj h => congrArg Fin.val (hinj h)
  have h0' : p ⟨0, by omega⟩ = 0 := h0
  have hl' : p ⟨ℓ, by omega⟩ = 1 := hlast
  -- the second vertex is a connector
  have a01 : G.Adj 0 (p ⟨1, by omega⟩) := by
    have h := adj 0 (by omega)
    rw [h0'] at h
    exact h
  obtain ⟨b, hb, hp1⟩ : ∃ b : Fin 12, (b = 2 ∨ b = 3) ∧ p ⟨1, by omega⟩ = b := by
    rcases out_s _ a01 with h | h | h
    · exfalso
      have := inj 1 ℓ (by omega) (by omega) (h.trans hl'.symm)
      omega
    · exact ⟨2, Or.inl rfl, h⟩
    · exact ⟨3, Or.inr rfl, h⟩
  -- the third vertex lies in the clique of that connector
  have a12 : G.Adj b (p ⟨2, by omega⟩) := by
    have h := adj 1 (by omega)
    rw [hp1] at h
    exact h
  have h2 : trap b (p ⟨2, by omega⟩) = true := by
    rcases out_b b _ hb a12 with h | h | h
    · exfalso
      have := inj 2 0 (by omega) (by omega) (h.trans h0'.symm)
      omega
    · exfalso
      have := inj 2 ℓ (by omega) (by omega) (h.trans hl'.symm)
      omega
    · exact h
  -- and the path never leaves the clique afterwards
  have key : ∀ i (hi : i < ℓ + 1), 2 ≤ i → trap b (p ⟨i, hi⟩) = true := by
    intro i
    induction i with
    | zero => intro hi h; omega
    | succ n ih =>
      intro hi h2n
      rcases Nat.lt_or_ge n 2 with hn | hn
      · have hn1 : n = 1 := by omega
        subst hn1
        exact h2
      · have hT := ih (by omega) hn
        have hA := adj n (by omega)
        rcases trap_step b _ _ hb hT hA with h | h | h
        · exact h
        · exfalso
          have := inj (n + 1) 0 hi (by omega) (h.trans h0'.symm)
          omega
        · exfalso
          have := inj (n + 1) 1 hi (by omega) (h.trans hp1.symm)
          omega
  have hfin := key ℓ (by omega) (by omega)
  rw [hl', trap_t b hb] at hfin
  exact Bool.false_ne_true hfin

end OMA.S_mo_442518.Cex

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_442518.main) := by
  intro h
  exact OMA.S_mo_442518.Cex.noLongPath
    (h (Fin 12) OMA.S_mo_442518.Cex.G 3 OMA.S_mo_442518.Cex.noLoops
      OMA.S_mo_442518.Cex.twoStrong OMA.S_mo_442518.Cex.degrees 0 1 (by decide))
