import OMAReductions.R_Erdos64_erdos_64_R2
import Mathlib

/-!
# Structural reduction of the triangle-containing critical branch of Erdős Problem 64

Step `H2` of `Erdos64.erdos_64.R2` concerns finite graphs `G` on `Fin n` of minimum degree
at least `3` obtained from a vertex- and edge-critical counterexample that contains at least
one triangle, has no `4`-cycle (`|(N(a) ∩ N(b))| ≤ 1` for `a ≠ b`), has no cycle with private
triangular detours on every edge, satisfies critical cubic-cut concentration, and satisfies
the cubic density bound `2 * n ≤ 3 * |V_3|`.

This reduction proves four unconditional structural theorems in Lean 4 and splits `R2.H2`
along the sharp `2 / 3` cubic-density threshold into the extremal `{3, 4}`-biregular
matching-triangle graphs (`H1`, where `2 * n = 3 * |V_3|`) and the strict cubic-excess
branch (`H2`, where `2 * n < 3 * |V_3|`, matching the strict regime of Bisch, 2026):

1. **Connectedness from cubic-cut concentration**: any graph of minimum degree at least `3`
   satisfying the cubic-closed cut witness property is connected.
2. **Minimum order `9 ≤ n` around a triangle**: in any `C4`-free graph of minimum degree at
   least `3` containing a triangle `(a, b, c)`, choosing external neighbors `a', b', c'` yields
   a `6`-vertex set `F = {a, b, c, a', b', c'}` such that `N(a') \ F` and `N(b') \ F` each have
   cardinality at least `2` and intersect in at most `1` vertex, forcing `9 ≤ n`.
3. **Isolated cubic-edge apex theorem (Bisch 2026, Proposition 2.3)**: whenever two adjacent
   cubic vertices `a` and `b` have no other cubic neighbors, `{a, b}` is cubic-closed and proper,
   so critical cut concentration produces a vertex `v` of degree **exactly `4`** adjacent to
   both `a` and `b`.
4. **Complete characterization and `15 ≤ n` bound for the extremal case `2 * n = 3 * |V_3|`**:
   when `2 * n = 3 * |V_3|`, double counting cross-edges forces every non-cubic vertex to have
   degree `4`, every cubic vertex to have degree `1` in `G[V_3]` (so `G[V_3]` is a `1`-regular
   matching), every cubic vertex to lie in a triangle with a degree-`4` apex, `3 ∣ n`, and
   ordered-pair counting across `V_4` forces `4 * |V_4| ≤ |V_4| * (|V_4| - 1)`, hence
   `5 ≤ |V_4|` and `15 ≤ n`.
-/

namespace OMA.R_Erdos64_erdos_64_R2_H2_R1

open SimpleGraph Finset
open scoped Classical

/-- Extremal `{3, 4}`-biregular critical triangle graphs at `2 * n = 3 * |V_3|`: connected,
order `n ≥ 15` divisible by `3`, no `C4` or `C8`, every vertex has degree `3` or `4`, degree-`4`
vertices are independent, `G[V_3]` is `1`-regular, and every cubic vertex lies in a triangle
with a degree-`4` apex. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected →
    15 ≤ n →
    3 ∣ n →
    2 * n = 3 * (univ.filter (fun x => G.degree x = 3)).card →
    (∀ x, G.degree x = 3 ∨ G.degree x = 4) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ y, G.degree y = 3 → ((G.neighborFinset y).filter (fun z => G.degree z = 3)).card = 1) →
    (∀ a, G.degree a = 3 →
      ∃ b v, G.degree b = 3 ∧ G.degree v = 4 ∧ G.Adj a b ∧ G.Adj v a ∧ G.Adj v b) →
    (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
    ¬ cycleGraph 8 ⊑ G →
    (∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) →
    (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ e : Fin (2 * m) ↪ Fin n,
      (∀ i, G.Adj (e i) (e (i + 1))) →
      ¬ (∀ i : Fin m, G.Adj (e ⟨2 * i.val, by omega⟩)
        (e ⟨2 * (i + 1).val, by have := (i + 1).isLt; omega⟩))) →
    ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Strict cubic-excess critical triangle graphs (`2 * n < 3 * |V_3|`): connected, `9 ≤ n`,
no `C4` or `C8`, containing a triangle, and satisfying the isolated cubic-edge degree-`4`
apex theorem. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected →
    9 ≤ n →
    3 ≤ G.minDegree →
    2 * n < 3 * (univ.filter (fun x => G.degree x = 3)).card →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
    (∀ a b, G.Adj a b → G.degree a = 3 → G.degree b = 3 →
      (∀ z, G.Adj a z → z ≠ b → G.degree z ≠ 3) →
      (∀ z, G.Adj b z → z ≠ a → G.degree z ≠ 3) →
      ∃ v, G.degree v = 4 ∧ G.Adj v a ∧ G.Adj v b) →
    (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
    ¬ cycleGraph 8 ⊑ G →
    (∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
    (∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) →
    (∀ (m : ℕ) [NeZero m], 3 ≤ m → ∀ e : Fin (2 * m) ↪ Fin n,
      (∀ i, G.Adj (e i) (e (i + 1))) →
      ¬ (∀ i : Fin m, G.Adj (e ⟨2 * i.val, by omega⟩)
        (e ⟨2 * (i + 1).val, by have := (i + 1).isLt; omega⟩))) →
    ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

section Helpers

private lemma pos_of_minDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hz := G.minDegree_of_subsingleton
    omega
  · exact hpos

private lemma common_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    {a b x y : Fin n} (hab : a ≠ b)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hby : G.Adj b y) : x = y := by
  by_contra hxy
  have hx : x ∈ (G.neighborFinset a) ∩ G.neighborFinset b :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a x).mpr hax, (G.mem_neighborFinset b x).mpr hbx⟩
  have hy : y ∈ (G.neighborFinset a) ∩ G.neighborFinset b :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a y).mpr hay, (G.mem_neighborFinset b y).mpr hby⟩
  have htwo : 2 ≤ ((G.neighborFinset a) ∩ G.neighborFinset b).card := by
    have hsub : ({x, y} : Finset (Fin n)) ⊆ (G.neighborFinset a) ∩ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    simpa [hxy] using hc
  have hle := pair a b hab
  omega

/-- Part 1: Cubic-cut concentration forces connectedness. -/
private lemma connected_of_cut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree)
    (cut : ∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) :
    G.Connected := by
  have hn : 0 < n := pos_of_minDegree G hmin
  let v0 : Fin n := ⟨0, hn⟩
  have : Nonempty (Fin n) := ⟨v0⟩
  let K : G.ConnectedComponent := G.connectedComponentMk v0
  let C : Finset (Fin n) := K.supp.toFinset
  have hmem : ∀ z : Fin n, z ∈ C ↔ G.Reachable z v0 := by
    intro z
    simp [C, K, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  have hCne : C.Nonempty := ⟨v0, (hmem v0).mpr Reachable.rfl⟩
  have hclosed : ∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C := by
    intro a b ha hab _
    exact (hmem b).mpr (hab.symm.reachable.trans ((hmem a).mp ha))
  have hall : ∀ x : Fin n, x ∈ C := by
    by_contra hnot
    push Not at hnot
    obtain ⟨v, hvC, hv4, hcard⟩ := cut C hCne hnot hclosed
    have hpos : 0 < ((G.neighborFinset v) ∩ C).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    obtain ⟨hvu, huC⟩ := Finset.mem_inter.mp hu
    have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hvu
    exact hvC ((hmem v).mpr (hadj.reachable.trans ((hmem u).mp huC)))
  exact ⟨fun x y => ((hmem x).mp (hall x)).trans ((hmem y).mp (hall y)).symm⟩

/-- Helper: picking a third neighbor of a triangle vertex outside the triangle. -/
private lemma exists_third_nbr {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree) (u x y : Fin n) :
    ∃ u' : Fin n, G.Adj u u' ∧ u' ≠ x ∧ u' ≠ y := by
  have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset u) {x, y}
  have hinter : ((G.neighborFinset u) ∩ {x, y}).card ≤ ({x, y} : Finset (Fin n)).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpair : ({x, y} : Finset (Fin n)).card ≤ 2 := Finset.card_insert_le _ _
  rw [G.card_neighborFinset_eq_degree] at hsplit
  have hdeg := hmin.trans (G.minDegree_le_degree u)
  obtain ⟨u', hu'⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset u \ {x, y}).card by omega)
  obtain ⟨hu'N, hu'not⟩ := Finset.mem_sdiff.mp hu'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu'not
  exact ⟨u', (G.mem_neighborFinset u u').mp hu'N, hu'not.1, hu'not.2⟩

/-- Part 2: Every `C4`-free graph of minimum degree `≥ 3` with a triangle has order `≥ 9`. -/
private lemma order_ge_nine_of_triangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    (htri : ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) :
    9 ≤ n := by
  obtain ⟨a, b, c, hab, hbc, hca⟩ := htri
  obtain ⟨a', haa', ha'b, ha'c⟩ := exists_third_nbr hmin a b c
  obtain ⟨b', hbb', hb'a, hb'c⟩ := exists_third_nbr hmin b a c
  obtain ⟨c', hcc', hc'a, hc'b⟩ := exists_third_nbr hmin c a b
  have ha'a : a' ≠ a := haa'.ne.symm
  have hb'b : b' ≠ b := hbb'.ne.symm
  have hc'c : c' ≠ c := hcc'.ne.symm
  have ha'b' : a' ≠ b' := by
    intro h
    have hb_a' : G.Adj b a' := h ▸ hbb'
    exact ha'c (common_unique pair hab.ne hca.symm hbc haa' hb_a').symm
  have ha'c' : a' ≠ c' := by
    intro h
    have hc_a' : G.Adj c a' := h ▸ hcc'
    exact ha'b (common_unique pair hca.ne.symm hab hbc.symm haa' hc_a').symm
  have hb'c' : b' ≠ c' := by
    intro h
    have hc_b' : G.Adj c b' := h ▸ hcc'
    exact hb'a (common_unique pair hbc.ne hab.symm hca hbb' hc_b').symm
  let F : Finset (Fin n) := {a, b, c, a', b', c'}
  have hF_iff : ∀ z, z ∈ F ↔ z = a ∨ z = b ∨ z = c ∨ z = a' ∨ z = b' ∨ z = c' := fun z => by
    simp only [F, Finset.mem_insert, Finset.mem_singleton]
  have hF_card : F.card = 6 := by
    have hnd : ([a, b, c, a', b', c'] : List (Fin n)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
        not_false_eq_true, List.nodup_nil, and_true]
      exact ⟨⟨hab.ne, hca.ne.symm, ha'a.symm, hb'a.symm, hc'a.symm⟩,
        ⟨hbc.ne, ha'b.symm, hb'b.symm, hc'b.symm⟩,
        ⟨ha'c.symm, hb'c.symm, hc'c.symm⟩,
        ⟨ha'b', ha'c'⟩, hb'c'⟩
    have hFeq : F = ([a, b, c, a', b', c'] : List (Fin n)).toFinset := by
      ext z
      simp only [hF_iff, List.mem_toFinset, List.mem_cons, List.mem_nil_iff, or_false]
    rw [hFeq, List.toFinset_card_of_nodup hnd]
    rfl
  have hcap_le_one : ∀ u u' v w v' w' : Fin n,
      G.Adj u v → G.Adj v w → G.Adj w u →
      G.Adj u u' → u' ≠ v → u' ≠ w →
      G.Adj v v' → v' ≠ u → G.Adj w w' → w' ≠ u →
      (∀ z ∈ F, z = u ∨ z = v ∨ z = w ∨ z = u' ∨ z = v' ∨ z = w') →
      2 ≤ (G.neighborFinset u' \ F).card := by
    intro u u' v w v' w' huv hvw hwu huu' hu'v hu'w hvv' hv'u hww' hw'u hFmem
    have hsub : (G.neighborFinset u') ∩ F ⊆ {u} := by
      intro z hz
      obtain ⟨hzN, hzF⟩ := Finset.mem_inter.mp hz
      have hadj : G.Adj u' z := (G.mem_neighborFinset u' z).mp hzN
      rcases hFmem z hzF with h | h | h | h | h | h
      · exact Finset.mem_singleton.mpr h
      · exfalso
        rw [h] at hadj
        exact hu'w (common_unique pair huv.ne hwu.symm hvw huu' hadj.symm).symm
      · exfalso
        rw [h] at hadj
        exact hu'v (common_unique pair hwu.ne.symm huv hvw.symm huu' hadj.symm).symm
      · exfalso
        rw [h] at hadj
        exact hadj.ne rfl
      · exfalso
        rw [h] at hadj
        exact hu'v (common_unique pair hv'u.symm huv hvv'.symm huu' hadj.symm).symm
      · exfalso
        rw [h] at hadj
        exact hu'w (common_unique pair hw'u.symm hwu.symm hww'.symm huu' hadj.symm).symm
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset u') F
    have hinter : ((G.neighborFinset u') ∩ F).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    rw [G.card_neighborFinset_eq_degree] at hsplit
    have hdeg := hmin.trans (G.minDegree_le_degree u')
    omega
  have hSa : 2 ≤ (G.neighborFinset a' \ F).card :=
    hcap_le_one a a' b c b' c' hab hbc hca haa' ha'b ha'c hbb' hb'a hcc' hc'a
      (fun z hz => (hF_iff z).mp hz)
  have hSb : 2 ≤ (G.neighborFinset b' \ F).card :=
    hcap_le_one b b' a c a' c' hab.symm hca.symm hbc.symm hbb' hb'a hb'c haa' ha'b hcc' hc'b
      (fun z hz => by
        rcases (hF_iff z).mp hz with h | h | h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  let Sa := G.neighborFinset a' \ F
  let Sb := G.neighborFinset b' \ F
  have hSab_inter : (Sa ∩ Sb).card ≤ 1 := by
    have hsub : Sa ∩ Sb ⊆ (G.neighborFinset a') ∩ G.neighborFinset b' :=
      Finset.inter_subset_inter Finset.sdiff_subset Finset.sdiff_subset
    exact (Finset.card_le_card hsub).trans (pair a' b' ha'b')
  have hSab_union : 3 ≤ (Sa ∪ Sb).card := by
    have hu := Finset.card_union_add_card_inter Sa Sb
    change 2 ≤ Sa.card at hSa
    change 2 ≤ Sb.card at hSb
    omega
  have hdisj : Disjoint F (Sa ∪ Sb) :=
    Finset.disjoint_union_right.mpr ⟨Finset.disjoint_sdiff, Finset.disjoint_sdiff⟩
  have hcard_all : (F ∪ (Sa ∪ Sb)).card ≤ n := by
    simpa using Finset.card_le_univ (F ∪ (Sa ∪ Sb))
  rw [Finset.card_union_of_disjoint hdisj, hF_card] at hcard_all
  omega

/-- Part 3 (Bisch 2026, Prop. 2.3): Every isolated edge of `G[V_3]` forms a triangle with a
vertex of degree **exactly `4`**. -/
private lemma local_cubic_edge_apex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn3 : 3 ≤ n)
    (cut : ∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card)
    (a b : Fin n) (hab : G.Adj a b) (_ha3 : G.degree a = 3) (_hb3 : G.degree b = 3)
    (ha_iso : ∀ z, G.Adj a z → z ≠ b → G.degree z ≠ 3)
    (hb_iso : ∀ z, G.Adj b z → z ≠ a → G.degree z ≠ 3) :
    ∃ v, G.degree v = 4 ∧ G.Adj v a ∧ G.Adj v b := by
  let C : Finset (Fin n) := {a, b}
  have hC_card : C.card = 2 := Finset.card_pair hab.ne
  have hCne : C.Nonempty := ⟨a, by simp [C]⟩
  have hout : ∃ x, x ∉ C := by
    by_contra hall
    push Not at hall
    have hsub : (univ : Finset (Fin n)) ⊆ C := fun x _ => hall x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, hC_card] at hle
    omega
  have hclosed : ∀ ⦃u w⦄, u ∈ C → G.Adj u w → G.degree w = 3 → w ∈ C := by
    intro u w hu huw hw3
    have hu' : u = a ∨ u = b := by simpa [C] using hu
    rcases hu' with h | h
    · rw [h] at huw
      by_cases hwb : w = b
      · simp [C, hwb]
      · exact (ha_iso w huw hwb hw3).elim
    · rw [h] at huw
      by_cases hwa : w = a
      · simp [C, hwa]
      · exact (hb_iso w huw hwa hw3).elim
  obtain ⟨v, _, hv4, hcard⟩ := cut C hCne hout hclosed
  have hinter_le : ((G.neighborFinset v) ∩ C).card ≤ C.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hv_deg : G.degree v = 4 := by omega
  have heq_C : (G.neighborFinset v) ∩ C = C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have ha_in : a ∈ (G.neighborFinset v) ∩ C := by rw [heq_C]; simp [C]
  have hb_in : b ∈ (G.neighborFinset v) ∩ C := by rw [heq_C]; simp [C]
  exact ⟨v, hv_deg,
    (G.mem_neighborFinset v a).mp (Finset.mem_inter.mp ha_in).1,
    (G.mem_neighborFinset v b).mp (Finset.mem_inter.mp hb_in).1⟩

/-- Part 4: Complete structural characterization and `15 ≤ n` bound for `2 * n = 3 * |V_3|`. -/
private lemma equality_structure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn9 : 9 ≤ n)
    (hmin : 3 ≤ G.minDegree)
    (edge : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3)
    (nbr : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    (cut : ∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card)
    (heq : 2 * n = 3 * (univ.filter (fun x => G.degree x = 3)).card) :
    15 ≤ n ∧
    3 ∣ n ∧
    (∀ x, G.degree x = 3 ∨ G.degree x = 4) ∧
    (∀ y, G.degree y = 3 → ((G.neighborFinset y).filter (fun z => G.degree z = 3)).card = 1) ∧
    (∀ a, G.degree a = 3 →
      ∃ b v, G.degree b = 3 ∧ G.degree v = 4 ∧ G.Adj a b ∧ G.Adj v a ∧ G.Adj v b) := by
  let L := univ.filter fun x => G.degree x = 3
  let H := univ.filter fun x => G.degree x ≠ 3
  let cross (y : Fin n) := (G.neighborFinset y).filter (· ∈ H)
  let inside (y : Fin n) := (G.neighborFinset y).filter (fun z => G.degree z = 3)
  have parts : L.card + H.card = n := by
    have h := (univ : Finset (Fin n)).card_filter_add_card_filter_not (fun x => G.degree x = 3)
    change L.card + H.card = (univ : Finset (Fin n)).card at h
    simpa using h
  change 2 * n = 3 * L.card at heq
  have hL_2H : L.card = 2 * H.card := by omega
  have hn_3H : n = 3 * H.card := by omega
  have hdvd3 : 3 ∣ n := ⟨H.card, hn_3H⟩
  have hH_ge3 : 3 ≤ H.card := by omega
  -- Double count cross edges between H and L
  have sums : (∑ x ∈ H, G.degree x) = ∑ y ∈ L, (cross y).card := by
    calc
      _ = ∑ x ∈ H, ∑ y ∈ L, if G.Adj x y then 1 else 0 := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hn3 : G.degree x ≠ 3 := (Finset.mem_filter.mp hx).2
        have same : L.filter (G.Adj x) = G.neighborFinset x := by
          ext y
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, G.mem_neighborFinset]
          exact ⟨And.right, fun h => ⟨(edge h).resolve_left hn3, h⟩⟩
        rw [Finset.sum_boole, same, G.card_neighborFinset_eq_degree]
        rfl
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        have same : H.filter (fun x => G.Adj x y) = cross y := by
          ext x
          simp [cross, G.adj_comm, and_comm]
        rw [Finset.sum_boole, same]
        rfl
  have hH_ge4 : ∀ x ∈ H, 4 ≤ G.degree x := by
    intro x hx
    have h1 := hmin.trans (G.minDegree_le_degree x)
    have h2 := (Finset.mem_filter.mp hx).2
    omega
  have hcross_le2 : ∀ y ∈ L, (cross y).card ≤ 2 := by
    intro y hy
    obtain ⟨t, ht, hdt⟩ := nbr y
    have hc : cross y ⊆ (G.neighborFinset y).erase t := by
      intro x hx
      obtain ⟨hyx, hxH⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_filter.mp hxH).2 (he ▸ hdt), hyx⟩
    have hb := Finset.card_le_card hc
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y t).mpr ht),
      G.card_neighborFinset_eq_degree, (Finset.mem_filter.mp hy).2] at hb
    exact hb
  have hlower : 4 * H.card ≤ ∑ x ∈ H, G.degree x := by
    calc 4 * H.card = ∑ _x ∈ H, 4 := by simp [mul_comm]
      _ ≤ ∑ x ∈ H, G.degree x := Finset.sum_le_sum hH_ge4
  have hupper : ∑ y ∈ L, (cross y).card ≤ 2 * L.card := by
    calc ∑ y ∈ L, (cross y).card ≤ ∑ _y ∈ L, 2 := Finset.sum_le_sum hcross_le2
      _ = 2 * L.card := by simp [mul_comm]
  -- Equality forces deg x = 4 on H and |cross y| = 2 on L
  have hdegH_eq4 : ∀ x ∈ H, G.degree x = 4 := by
    have hsum_diff : (∑ x ∈ H, (G.degree x - 4)) + 4 * H.card = ∑ x ∈ H, G.degree x := by
      have h4 : 4 * H.card = ∑ _x ∈ H, 4 := by simp [mul_comm]
      rw [h4, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      have := hH_ge4 x hx
      omega
    have hzero : ∑ x ∈ H, (G.degree x - 4) = 0 := by omega
    intro x hx
    have hle0 : G.degree x - 4 ≤ 0 := by
      rw [← hzero]
      exact Finset.single_le_sum (f := fun z => G.degree z - 4) (fun _ _ => Nat.zero_le _) hx
    have := hH_ge4 x hx
    omega
  have hdeg34 : ∀ x, G.degree x = 3 ∨ G.degree x = 4 := by
    intro x
    by_cases hx3 : G.degree x = 3
    · exact Or.inl hx3
    · exact Or.inr (hdegH_eq4 x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx3⟩))
  have hcross_eq2 : ∀ y ∈ L, (cross y).card = 2 := by
    have hsum_diff : (∑ y ∈ L, (2 - (cross y).card)) + ∑ y ∈ L, (cross y).card = 2 * L.card := by
      rw [← Finset.sum_add_distrib]
      calc ∑ y ∈ L, ((2 - (cross y).card) + (cross y).card) = ∑ _y ∈ L, 2 := by
            refine Finset.sum_congr rfl fun y hy => ?_
            have := hcross_le2 y hy
            omega
        _ = 2 * L.card := by simp [mul_comm]
    have hzero : ∑ y ∈ L, (2 - (cross y).card) = 0 := by omega
    intro y hy
    have hle0 : 2 - (cross y).card ≤ 0 := by
      rw [← hzero]
      exact Finset.single_le_sum (f := fun z => 2 - (cross z).card) (fun _ _ => Nat.zero_le _) hy
    have := hcross_le2 y hy
    omega
  have hinside_eq1 : ∀ y, G.degree y = 3 → (inside y).card = 1 := by
    intro y hy3
    have hyL : y ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy3⟩
    have htot : (inside y).card + (cross y).card = 3 := by
      have h := (G.neighborFinset y).card_filter_add_card_filter_not (fun z => G.degree z = 3)
      have hcr : (G.neighborFinset y).filter (fun z => ¬ G.degree z = 3) = cross y := by
        ext z; simp [cross, H]
      rw [hcr, G.card_neighborFinset_eq_degree, hy3] at h
      exact h
    have := hcross_eq2 y hyL
    omega
  have hapex : ∀ a, G.degree a = 3 →
      ∃ b v, G.degree b = 3 ∧ G.degree v = 4 ∧ G.Adj a b ∧ G.Adj v a ∧ G.Adj v b := by
    intro a ha3
    obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp (hinside_eq1 a ha3)
    have hb_mem : b ∈ inside a := by rw [hb_eq]; simp
    obtain ⟨habN, hb3⟩ := Finset.mem_filter.mp hb_mem
    have hab : G.Adj a b := (G.mem_neighborFinset a b).mp habN
    have ha_iso : ∀ z, G.Adj a z → z ≠ b → G.degree z ≠ 3 := by
      intro z haz hzb hz3
      have hz_in : z ∈ inside a := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset a z).mpr haz, hz3⟩
      rw [hb_eq] at hz_in
      exact hzb (Finset.mem_singleton.mp hz_in)
    have hb_iso : ∀ z, G.Adj b z → z ≠ a → G.degree z ≠ 3 := by
      intro z hbz hza hz3
      obtain ⟨b', hb'_eq⟩ := Finset.card_eq_one.mp (hinside_eq1 b hb3)
      have ha_in : a ∈ inside b := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset b a).mpr hab.symm, ha3⟩
      have hz_in : z ∈ inside b := Finset.mem_filter.mpr ⟨(G.mem_neighborFinset b z).mpr hbz, hz3⟩
      rw [hb'_eq] at ha_in hz_in
      exact hza ((Finset.mem_singleton.mp hz_in).trans (Finset.mem_singleton.mp ha_in).symm)
    obtain ⟨v, hv4, hva, hvb⟩ := local_cubic_edge_apex G (by omega) cut a b hab ha3 hb3 ha_iso hb_iso
    exact ⟨b, v, hb3, hv4, hab, hva, hvb⟩
  -- Ordered-pair double count across H to force 5 ≤ H.card, hence 15 ≤ n
  let f : Fin n → Fin n → Fin n → ℕ :=
    fun x x' y => if x ≠ x' ∧ G.Adj x y ∧ G.Adj x' y then 1 else 0
  have hf_lb : 2 * L.card ≤ ∑ y ∈ L, ∑ x ∈ H, ∑ x' ∈ H, f x x' y := by
    calc 2 * L.card = ∑ _y ∈ L, 2 := by simp [mul_comm]
      _ ≤ ∑ y ∈ L, ∑ x ∈ H, ∑ x' ∈ H, f x x' y := by
        refine Finset.sum_le_sum fun y hy => ?_
        obtain ⟨w1, w2, hw12, hcy⟩ := Finset.card_eq_two.mp (hcross_eq2 y hy)
        have hw1_in : w1 ∈ cross y := by rw [hcy]; simp
        have hw2_in : w2 ∈ cross y := by rw [hcy]; simp
        obtain ⟨hyw1N, hw1H⟩ := Finset.mem_filter.mp hw1_in
        obtain ⟨hyw2N, hw2H⟩ := Finset.mem_filter.mp hw2_in
        have hyw1 : G.Adj w1 y := ((G.mem_neighborFinset y w1).mp hyw1N).symm
        have hyw2 : G.Adj w2 y := ((G.mem_neighborFinset y w2).mp hyw2N).symm
        have hsubH : ({w1, w2} : Finset (Fin n)) ⊆ H := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have h2 : (∑ x ∈ ({w1, w2} : Finset (Fin n)), ∑ x' ∈ ({w1, w2} : Finset (Fin n)), f x x' y) = 2 := by
          rw [Finset.sum_pair hw12, Finset.sum_pair hw12, Finset.sum_pair hw12]
          simp [f, hw12, hw12.symm, hyw1, hyw2]
        rw [← h2]
        refine (Finset.sum_le_sum_of_subset hsubH).trans ?_
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset hsubH
  have hf_swap : (∑ y ∈ L, ∑ x ∈ H, ∑ x' ∈ H, f x x' y) =
      ∑ x ∈ H, ∑ x' ∈ H, ∑ y ∈ L, f x x' y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  have hf_ub : (∑ x ∈ H, ∑ x' ∈ H, ∑ y ∈ L, f x x' y) ≤ H.card * (H.card - 1) := by
    calc (∑ x ∈ H, ∑ x' ∈ H, ∑ y ∈ L, f x x' y)
        ≤ ∑ x ∈ H, ∑ x' ∈ H, if x ≠ x' then 1 else 0 := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
          by_cases hxx' : x = x'
          · simp [f, hxx']
          · rw [if_pos hxx']
            have heq_f : (∑ y ∈ L, f x x' y) = ∑ y ∈ L, if G.Adj x y ∧ G.Adj x' y then 1 else 0 :=
              Finset.sum_congr rfl fun y _ => by simp [f, hxx']
            have hsub_inter : L.filter (fun y => G.Adj x y ∧ G.Adj x' y) ⊆
                (G.neighborFinset x) ∩ G.neighborFinset x' := by
              intro y hy
              obtain ⟨_, hxy, hx'y⟩ := Finset.mem_filter.mp hy
              exact Finset.mem_inter.mpr
                ⟨(G.mem_neighborFinset x y).mpr hxy, (G.mem_neighborFinset x' y).mpr hx'y⟩
            rw [heq_f, Finset.sum_boole]
            exact_mod_cast (Finset.card_le_card hsub_inter).trans (pair x x' hxx')
      _ = ∑ x ∈ H, (H.card - 1) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have heq_er : H.filter (fun x' => x ≠ x') = H.erase x := by
            ext x'
            simp [eq_comm, and_comm]
          rw [Finset.sum_boole, heq_er, Finset.card_erase_of_mem hx]
          rfl
      _ = H.card * (H.card - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
  have h4H : 4 * H.card ≤ H.card * (H.card - 1) := by omega
  have hH_ge5 : 5 ≤ H.card := by
    by_contra hlt5
    have h34 : H.card = 3 ∨ H.card = 4 := by omega
    rcases h34 with h3 | h4
    · rw [h3] at h4H; omega
    · rw [h4] at h4H; omega
  exact ⟨by omega, hdvd3, hdeg34, hinside_eq1, hapex⟩

end Helpers

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R2.H2 := by
  intro hEq hStrict n G _ hmin hedge hnbr hpair hcut htri hring hbound
  by_cases hc8 : cycleGraph 8 ⊑ G
  · obtain ⟨v, c, hc, hlen⟩ := (cycleGraph_isContained_iff (by decide : 3 ≤ 8)).mp hc8
    exact ⟨3, v, c, by decide, hc, hlen⟩
  have hconn : G.Connected := connected_of_cut G hmin hcut
  have hn9 : 9 ≤ n := order_ge_nine_of_triangle G hmin hpair htri
  by_cases heq : 2 * n = 3 * (univ.filter (fun x => G.degree x = 3)).card
  · obtain ⟨hn15, hdvd3, hdeg34, hinside1, hapex⟩ :=
      equality_structure G hn9 hmin hedge hnbr hpair hcut heq
    exact hEq n G hconn hn15 hdvd3 heq hdeg34 hedge hinside1 hapex hpair hc8 hcut hring
  · have hlt : 2 * n < 3 * (univ.filter (fun x => G.degree x = 3)).card := by omega
    have hlocal : ∀ a b, G.Adj a b → G.degree a = 3 → G.degree b = 3 →
        (∀ z, G.Adj a z → z ≠ b → G.degree z ≠ 3) →
        (∀ z, G.Adj b z → z ≠ a → G.degree z ≠ 3) →
        ∃ v, G.degree v = 4 ∧ G.Adj v a ∧ G.Adj v b :=
      local_cubic_edge_apex G (by omega) hcut
    exact hStrict n G hconn hn9 hmin hlt hedge hnbr hlocal hpair hc8 htri hcut hring

end OMA.R_Erdos64_erdos_64_R2_H2_R1
