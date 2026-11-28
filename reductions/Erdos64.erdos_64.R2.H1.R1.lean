import OMAReductions.R_Erdos64_erdos_64_R2
import Mathlib

/-!
# Structural reduction of the triangle-free critical branch of Erdős Problem 64

Step `H1` of `Erdos64.erdos_64.R2` concerns finite graphs `G` on `Fin n` of minimum degree
at least `3` and girth at least `5` (triangle-free and `C4`-free via at-most-one common
neighbor) obtained from a vertex- and edge-critical counterexample: vertices of degree at
least `4` form an independent set, every vertex has a cubic neighbor, every nonempty proper
cubic-closed subset `C` has an external vertex `v` of degree `d ≥ 4` sending at least `d - 2`
edges into `C`, every connected component of the cubic subgraph has at least `4` vertices,
and `8 * n ≤ 11 * |V_3|`.

This reduction proves five unconditional structural theorems in Lean 4 and splits the
remaining triangle-free graphs into the pure cubic branch (`H1`) and the mixed-degree
branch (`H2`):

1. **Connectedness from cubic-cut concentration**: any graph of minimum degree at least `3`
   satisfying the cubic-closed cut witness property is connected.
2. **Radius at least `3` (eliminating diameter `2` of Carr, arXiv:2508.19302, and all
   eccentricity-`2` centers)**: in a finite graph of minimum degree at least `3` and girth
   at least `5`, if some vertex `x` reaches every vertex in at most `2` steps, then `G`
   contains a simple `8`-cycle (`2^3`). Consequently, in any `C8`-free instance every vertex
   has a vertex at distance at least `3`.
3. **Second-neighborhood degree-sum bound**: for every vertex `x`, combining disjointness of
   `{u' ∈ N(u) | u' ≠ x}` across `u ∈ N(x)` with a vertex at distance at least `3` from `x`
   yields `2 + ∑ u ∈ G.neighborFinset x, G.degree u ≤ n`, hence `3 * G.degree x + 2 ≤ n`.
   This immediately eliminates order `10` (including the Petersen graph) without case
   enumeration and forces `14 ≤ n` whenever a vertex of degree at least `4` exists.
4. **Elimination of `12`-vertex cubic girth-`≥ 5` graphs**: parity of the degree sum forces
   even `n` in the cubic case, and analyzing the `2` vertices outside `{x} ∪ N(x) ∪ N_2(x)`
   at `n = 12` exhibits an explicit `8`-cycle in every case, forcing `Even n` and `14 ≤ n`.
5. **Boundary divisibility in the mixed branch**: if `8 * n = 11 * |V_3|`, coprimality of `8`
   and `11` forces `11 ∣ n`, which combined with `14 ≤ n` yields `22 ≤ n`.
-/

namespace OMA.R_Erdos64_erdos_64_R2_H1_R1

open SimpleGraph Finset
open scoped Classical

/-- Connected cubic graphs of even order `n ≥ 14`, girth at least `5`, no `8`-cycle,
and radius at least `3` (every vertex has eccentricity at least `3`). -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected →
    (∀ v, G.degree v = 3) →
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
    ¬ cycleGraph 8 ⊑ G →
    (∀ x : Fin n, ∃ y : Fin n, y ≠ x ∧ ¬ G.Adj x y ∧ ∀ b, ¬ (G.Adj x b ∧ G.Adj b y)) →
    Even n →
    14 ≤ n →
    ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Connected non-cubic graphs of order `n ≥ 14` and girth at least `5` with no `8`-cycle,
radius at least `3`, second-neighborhood degree-sum bound `2 + ∑_{u ∈ N(x)} deg(u) ≤ n`,
critical cubic-cut concentration, cubic component size `≥ 4`, `8 * n ≤ 11 * |V_3|`, and
`22 ≤ n` in the boundary equality case `8 * n = 11 * |V_3|`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected →
    3 ≤ G.minDegree →
    (∃ v, 4 ≤ G.degree v) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    (∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) →
    ¬ cycleGraph 8 ⊑ G →
    (∀ x : Fin n, ∃ y : Fin n, y ≠ x ∧ ¬ G.Adj x y ∧ ∀ b, ¬ (G.Adj x b ∧ G.Adj b y)) →
    (∀ x : Fin n, 2 + ∑ u ∈ G.neighborFinset x, G.degree u ≤ n) →
    (∀ C : Finset (Fin n), C.Nonempty → (∃ x, x ∉ C) →
      (∀ ⦃a b⦄, a ∈ C → G.Adj a b → G.degree b = 3 → b ∈ C) →
      ∃ v ∉ C, 4 ≤ G.degree v ∧ G.degree v - 2 ≤ ((G.neighborFinset v) ∩ C).card) →
    (∀ C : (G.induce {x : Fin n | G.degree x = 3}).ConnectedComponent, 4 ≤ C.supp.ncard) →
    8 * n ≤ 11 * (univ.filter (fun x => G.degree x = 3)).card →
    (8 * n = 11 * (univ.filter (fun x => G.degree x = 3)).card → 22 ≤ n) →
    14 ≤ n →
    ∃ (k : ℕ) (v : Fin n) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

section Helpers

private lemma pos_of_minDegree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hz := G.minDegree_of_subsingleton
    omega
  · exact hpos

private lemma nodup_eight {X : Type*} {v0 v1 v2 v3 v4 v5 v6 v7 : X}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h03 : v0 ≠ v3) (h04 : v0 ≠ v4)
    (h05 : v0 ≠ v5) (h06 : v0 ≠ v6) (h07 : v0 ≠ v7)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h14 : v1 ≠ v4) (h15 : v1 ≠ v5)
    (h16 : v1 ≠ v6) (h17 : v1 ≠ v7)
    (h23 : v2 ≠ v3) (h24 : v2 ≠ v4) (h25 : v2 ≠ v5) (h26 : v2 ≠ v6) (h27 : v2 ≠ v7)
    (h34 : v3 ≠ v4) (h35 : v3 ≠ v5) (h36 : v3 ≠ v6) (h37 : v3 ≠ v7)
    (h45 : v4 ≠ v5) (h46 : v4 ≠ v6) (h47 : v4 ≠ v7)
    (h56 : v5 ≠ v6) (h57 : v5 ≠ v7)
    (h67 : v6 ≠ v7) :
    ([v0, v1, v2, v3, v4, v5, v6, v7] : List X).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩,
    ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩,
    ⟨h34, h35, h36, h37⟩,
    ⟨h45, h46, h47⟩,
    ⟨h56, h57⟩,
    h67⟩

private lemma copy_of_periodic {X : Type*} (K : SimpleGraph X) (N : ℕ) (d : ℕ → X)
    (hper : ∀ m, d (m + N) = d m) (hadj : ∀ m, K.Adj (d m) (d (m + 1)))
    (hinj : ∀ a b, a < N → b < N → d a = d b → a = b) : cycleGraph N ⊑ K := by
  have step : ∀ t t' : Fin N, (t' - t).val = 1 → K.Adj (d t.val) (d t'.val) := by
    intro t t' h
    rw [Fin.val_sub] at h
    have ht := t.isLt
    have ht' := t'.isLt
    by_cases hs : N - t.val + t'.val < N
    · rw [Nat.mod_eq_of_lt hs] at h
      have h0 : t'.val = 0 := by omega
      have h1 : t.val + 1 = N := by omega
      have e : d t'.val = d (t.val + 1) := by rw [h0, h1, ← hper 0, Nat.zero_add]
      rw [e]
      exact hadj _
    · have hs2 : N - t.val + t'.val - N < N := by omega
      rw [Nat.mod_eq_sub_mod (show N - t.val + t'.val ≥ N by omega), Nat.mod_eq_of_lt hs2] at h
      have h1 : t'.val = t.val + 1 := by omega
      rw [h1]
      exact hadj _
  refine ⟨⟨⟨fun t => d t.val, ?_⟩, ?_⟩⟩
  · intro t t' h
    rw [cycleGraph_adj'] at h
    rcases h with h | h
    · exact (step t' t h).symm
    · exact step t t' h
  · intro t t' h
    change d t.val = d t'.val at h
    exact Fin.ext (hinj _ _ t.isLt t'.isLt h)

private lemma copy_eight {X : Type*} (K : SimpleGraph X)
    (v0 v1 v2 v3 v4 v5 v6 v7 : X)
    (h01 : K.Adj v0 v1) (h12 : K.Adj v1 v2) (h23 : K.Adj v2 v3) (h34 : K.Adj v3 v4)
    (h45 : K.Adj v4 v5) (h56 : K.Adj v5 v6) (h67 : K.Adj v6 v7) (h70 : K.Adj v7 v0)
    (hnodup : ([v0, v1, v2, v3, v4, v5, v6, v7] : List X).Nodup) :
    cycleGraph 8 ⊑ K := by
  let v : Fin 8 → X := ![v0, v1, v2, v3, v4, v5, v6, v7]
  have hget : ∀ i : Fin 8, ([v0, v1, v2, v3, v4, v5, v6, v7] : List X)[i.val]'(by simp) = v i := by
    intro i; fin_cases i <;> rfl
  have hinj : Function.Injective v := by
    intro i j hij
    have h' : ([v0, v1, v2, v3, v4, v5, v6, v7] : List X)[i.val]'(by simp) =
        ([v0, v1, v2, v3, v4, v5, v6, v7] : List X)[j.val]'(by simp) := by
      rw [hget i, hget j]; exact hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h')
  apply copy_of_periodic K 8 (fun m => v ⟨m % 8, Nat.mod_lt _ (by omega)⟩)
  · intro m; simp [Nat.add_mod_right]
  · intro m
    have hr : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨
        m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by omega
    have hnext : (m + 1) % 8 = (m % 8 + 1) % 8 := by omega
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;>
      simp [v, hnext, hr, h01, h12, h23, h34, h45, h56, h67, h70]
  · intro a b ha hb hab
    have := hinj hab
    simp [Fin.ext_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this

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
  refine ⟨fun x y => ((hmem x).mp (hall x)).trans ((hmem y).mp (hall y)).symm⟩

/-- Part 2: Radius at most `2` in a girth-`≥ 5` graph of minimum degree `≥ 3` forces `C8`. -/
private lemma no_eccentricity_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    (no8 : ¬ cycleGraph 8 ⊑ G)
    (x : Fin n) :
    ∃ y : Fin n, y ≠ x ∧ ¬ G.Adj x y ∧ ∀ b, ¬ (G.Adj x b ∧ G.Adj b y) := by
  by_contra hecc
  push Not at hecc
  have deg_ge : ∀ v, 3 ≤ G.degree v := fun v => hmin.trans (G.minDegree_le_degree v)
  let B : Finset (Fin n) := G.neighborFinset x
  let T : Finset (Fin n) := univ.filter (fun y => y ≠ x ∧ ¬ G.Adj x y)
  have memB : ∀ y, y ∈ B ↔ G.Adj x y := fun y => G.mem_neighborFinset x y
  have memT : ∀ y, y ∈ T ↔ y ≠ x ∧ ¬ G.Adj x y := by intro y; simp [T]
  have disjBT : ∀ y, y ∈ B → y ∈ T → False := by
    intro y hyB hyT
    exact ((memT y).mp hyT).2 ((memB y).mp hyB)
  have x_not_B : x ∉ B := by simp [memB]
  have x_not_T : x ∉ T := by simp [memT]
  have ne_xB : ∀ b ∈ B, x ≠ b := fun b hb h => x_not_B (h ▸ hb)
  have ne_xT : ∀ t ∈ T, x ≠ t := fun t ht h => x_not_T (h ▸ ht)
  have ne_BT : ∀ b ∈ B, ∀ t ∈ T, b ≠ t := fun b hb t ht h => disjBT b hb (h ▸ ht)
  have hTne : T.Nonempty := by
    have hBx : 3 ≤ B.card := by rw [G.card_neighborFinset_eq_degree]; exact deg_ge x
    obtain ⟨b0, hb0⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    have hxb0 : G.Adj x b0 := (memB b0).mp hb0
    have hsub : (G.neighborFinset b0).erase x ⊆ T := by
      intro w hw
      obtain ⟨hwx, hwb0⟩ := Finset.mem_erase.mp hw
      have hb0w : G.Adj b0 w := (G.mem_neighborFinset b0 w).mp hwb0
      exact (memT w).mpr ⟨hwx, fun hxw => tri x b0 w hxb0 hb0w hxw.symm⟩
    have hc : 2 ≤ ((G.neighborFinset b0).erase x).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset b0 x).mpr hxb0.symm),
        G.card_neighborFinset_eq_degree]
      have := deg_ge b0
      omega
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) (hc.trans (Finset.card_le_card hsub)))
  have hexB : ∀ t ∈ T, ∃ b ∈ B, G.Adj b t := by
    intro t ht
    obtain ⟨htx, hntx⟩ := (memT t).mp ht
    obtain ⟨b, hxb, hbt⟩ := hecc t htx hntx
    exact ⟨b, (memB b).mpr hxb, hbt⟩
  let p : Fin n → Fin n := fun t => if ht : t ∈ T then (hexB t ht).choose else x
  have hp_mem : ∀ t (ht : t ∈ T), p t ∈ B := by
    intro t ht; simp only [p, dif_pos ht]; exact (hexB t ht).choose_spec.1
  have hp_adj : ∀ t (ht : t ∈ T), G.Adj (p t) t := by
    intro t ht; simp only [p, dif_pos ht]; exact (hexB t ht).choose_spec.2
  have hp_x : ∀ t (ht : t ∈ T), G.Adj x (p t) := by
    intro t ht; exact (memB (p t)).mp (hp_mem t ht)
  have hp_unique : ∀ t (ht : t ∈ T) b, b ∈ B → G.Adj b t → b = p t := by
    intro t ht b hbB hbt
    exact common_unique pair ((memT t).mp ht).1 hbt.symm ((memB b).mp hbB)
      (hp_adj t ht).symm (hp_x t ht)
  have hTdeg : ∀ t ∈ T, 2 ≤ (T.filter (G.Adj t)).card := by
    intro t ht
    have hsub : G.neighborFinset t ⊆ insert (p t) (T.filter (G.Adj t)) := by
      intro w hw
      have htw : G.Adj t w := (G.mem_neighborFinset t w).mp hw
      by_cases hwx : w = x
      · subst hwx; exact (((memT t).mp ht).2 htw.symm).elim
      · by_cases hwB : G.Adj x w
        · have heq := hp_unique t ht w ((memB w).mpr hwB) htw.symm
          exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨(memT w).mpr ⟨hwx, hwB⟩, htw⟩))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [G.card_neighborFinset_eq_degree] at hc
    have := deg_ge t
    omega
  have step1 : ∀ a b, a ∈ T → b ∈ T → G.Adj a b → p a ≠ p b := by
    intro a b ha hb hab heq
    have hpa := hp_adj a ha
    have hpb : G.Adj (p a) b := heq ▸ hp_adj b hb
    exact tri (p a) a b hpa hab hpb.symm
  have step2 : ∀ a b c, a ∈ T → b ∈ T → c ∈ T → a ≠ c → G.Adj a b → G.Adj b c → p a ≠ p c := by
    intro a b c ha hb hc hac hab hbc heq
    have hpa := hp_adj a ha
    have hpc : G.Adj (p a) c := heq ▸ hp_adj c hc
    have heq_b : p a = b := common_unique pair hac hpa.symm hpc.symm hab hbc.symm
    exact disjBT (p a) (hp_mem a ha) (heq_b ▸ hb)
  have step4 : ∀ a0 a1 a2 a3 a4,
      a0 ∈ T → a1 ∈ T → a2 ∈ T → a3 ∈ T → a4 ∈ T →
      ([a0, a1, a2, a3, a4] : List (Fin n)).Nodup →
      G.Adj a0 a1 → G.Adj a1 a2 → G.Adj a2 a3 → G.Adj a3 a4 →
      p a0 = p a4 := by
    intro a0 a1 a2 a3 a4 h0 h1 h2 h3 h4 hnd e01 e12 e23 e34
    by_contra hpne
    apply no8
    apply copy_eight G x (p a0) a0 a1 a2 a3 a4 (p a4)
      (hp_x a0 h0) (hp_adj a0 h0) e01 e12 e23 e34 (hp_adj a4 h4).symm (hp_x a4 h4).symm
    have hB0 := hp_mem a0 h0
    have hB4 := hp_mem a4 h4
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    exact nodup_eight
      (ne_xB _ hB0) (ne_xT _ h0) (ne_xT _ h1) (ne_xT _ h2) (ne_xT _ h3) (ne_xT _ h4) (ne_xB _ hB4)
      (ne_BT _ hB0 _ h0) (ne_BT _ hB0 _ h1) (ne_BT _ hB0 _ h2) (ne_BT _ hB0 _ h3) (ne_BT _ hB0 _ h4) hpne
      hnd.1.1 hnd.1.2.1 hnd.1.2.2.1 hnd.1.2.2.2 (ne_BT _ hB4 _ h0).symm
      hnd.2.1.1 hnd.2.1.2.1 hnd.2.1.2.2 (ne_BT _ hB4 _ h1).symm
      hnd.2.2.1.1 hnd.2.2.1.2 (ne_BT _ hB4 _ h2).symm
      hnd.2.2.2 (ne_BT _ hB4 _ h3).symm
      (ne_BT _ hB4 _ h4).symm
  let PathT : List (Fin n) → Prop := fun L =>
    L ≠ [] ∧ L.Nodup ∧ (∀ z ∈ L, z ∈ T) ∧
      ∀ i (hi : i + 1 < L.length), G.Adj (L[i]'(by omega)) L[i + 1]
  have hbdd : ∀ L, PathT L → L.length ≤ n := by
    intro L hL
    have hsub : L.toFinset.card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [List.toFinset_card_of_nodup hL.2.1, Fintype.card_fin] at hsub
    exact hsub
  have hmax_ex : ∃ m, ∀ L, PathT L → L.length ≤ m := ⟨n, hbdd⟩
  let m := Nat.find hmax_ex
  have hm_ub : ∀ L, PathT L → L.length ≤ m := Nat.find_spec hmax_ex
  have hm_att : ∃ L, PathT L ∧ L.length = m := by
    by_contra hno
    push Not at hno
    obtain ⟨t0, ht0⟩ := hTne
    have hm_pos : 0 < m := by
      have h1 := hm_ub [t0] ⟨by simp, by simp, by simp [ht0], fun i hi => by simp at hi⟩
      simp at h1; omega
    have hle : ∀ L, PathT L → L.length ≤ m - 1 := fun L hL => by
      have := hm_ub L hL; have := hno L hL; omega
    exact Nat.find_min hmax_ex (show m - 1 < m by omega) hle
  obtain ⟨L, hPL, hLlen⟩ := hm_att
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hPL.1
  let v0 : Fin n := L[0]'hLpos
  have hv0T : v0 ∈ T := hPL.2.2.1 v0 (List.getElem_mem hLpos)
  have hnhd_in_L : ∀ w ∈ T.filter (G.Adj v0), w ∈ L := by
    intro w hw
    by_contra hnot
    obtain ⟨hwT, hadj⟩ := Finset.mem_filter.mp hw
    have hP' : PathT (w :: L) := by
      refine ⟨by simp, List.nodup_cons.mpr ⟨hnot, hPL.2.1⟩, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hzL
        · exact hwT
        · exact hPL.2.2.1 z hzL
      · intro i hi
        cases i with
        | zero => exact hadj.symm
        | succ j => exact hPL.2.2.2 j (by simp at hi; omega)
    have hle := hm_ub (w :: L) hP'
    simp [hLlen] at hle
  obtain ⟨w1, w2, hw1, hw2, hw12⟩ :=
    Finset.one_lt_card_iff.mp (lt_of_lt_of_le (by decide : 1 < 2) (hTdeg v0 hv0T))
  obtain ⟨i1, hi1, rfl⟩ := List.getElem_of_mem (hnhd_in_L w1 hw1)
  obtain ⟨i2, hi2, rfl⟩ := List.getElem_of_mem (hnhd_in_L w2 hw2)
  have hadj1 : G.Adj L[0] L[i1] := (Finset.mem_filter.mp hw1).2
  have hadj2 : G.Adj L[0] L[i2] := (Finset.mem_filter.mp hw2).2
  have hi1_pos : 0 < i1 := by
    by_contra h0; have : i1 = 0 := by omega
    subst this; exact hadj1.ne rfl
  have hi2_pos : 0 < i2 := by
    by_contra h0; have : i2 = 0 := by omega
    subst this; exact hadj2.ne rfl
  have hi12_ne : i1 ≠ i2 := fun h => hw12 (by subst h; rfl)
  obtain ⟨r, hr_lt, hr_ge2, hadjr⟩ : ∃ (r : ℕ) (hr : r < L.length), 2 ≤ r ∧ G.Adj L[0] L[r] := by
    rcases lt_trichotomy i1 i2 with hlt | rfl | hgt
    · exact ⟨i2, hi2, by omega, hadj2⟩
    · exact (hi12_ne rfl).elim
    · exact ⟨i1, hi1, by omega, hadj1⟩
  have hmemL : ∀ k (hk : k < L.length), L[k] ∈ T := fun k hk => hPL.2.2.1 L[k] (List.getElem_mem hk)
  have hneL : ∀ a b (ha : a < L.length) (hb : b < L.length), a ≠ b → L[a] ≠ L[b] := by
    intro a b ha hb hab heq
    exact hab ((List.Nodup.getElem_inj_iff hPL.2.1).mp heq)
  have nodup5 : ∀ a b c d e (ha : a < L.length) (hb : b < L.length) (hc : c < L.length)
      (hd : d < L.length) (he : e < L.length),
      ([a, b, c, d, e] : List ℕ).Nodup → ([L[a], L[b], L[c], L[d], L[e]] : List (Fin n)).Nodup := by
    intro a b c d e ha hb hc hd he hnd
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at hnd ⊢
    exact ⟨⟨hneL a b ha hb hnd.1.1, hneL a c ha hc hnd.1.2.1,
        hneL a d ha hd hnd.1.2.2.1, hneL a e ha he hnd.1.2.2.2⟩,
      ⟨hneL b c hb hc hnd.2.1.1, hneL b d hb hd hnd.2.1.2.1, hneL b e hb he hnd.2.1.2.2⟩,
      ⟨hneL c d hc hd hnd.2.2.1.1, hneL c e hc he hnd.2.2.1.2⟩,
      hneL d e hd he hnd.2.2.2⟩
  have hr_ne2 : r ≠ 2 := by
    rintro rfl
    exact tri L[0] L[1] L[2] (hPL.2.2.2 0 (by omega)) (hPL.2.2.2 1 (by omega)) hadjr.symm
  have hr_ne3 : r ≠ 3 := by
    rintro rfl
    have heq := common_unique pair (hneL 0 2 (by omega) (by omega) (by omega))
      (hPL.2.2.2 0 (by omega)) (hPL.2.2.2 1 (by omega)).symm hadjr (hPL.2.2.2 2 (by omega))
    exact hneL 1 3 (by omega) (by omega) (by omega) heq
  have hr_ge4 : 4 ≤ r := by omega
  by_cases hr4 : r = 4
  · subst hr4
    have hp10 := step4 L[1] L[2] L[3] L[4] L[0]
      (hmemL 1 (by omega)) (hmemL 2 (by omega)) (hmemL 3 (by omega))
      (hmemL 4 (by omega)) (hmemL 0 (by omega))
      (nodup5 1 2 3 4 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by decide))
      (hPL.2.2.2 1 (by omega)) (hPL.2.2.2 2 (by omega)) (hPL.2.2.2 3 (by omega)) hadjr.symm
    exact step1 L[0] L[1] (hmemL 0 (by omega)) (hmemL 1 (by omega)) (hPL.2.2.2 0 (by omega)) hp10.symm
  · by_cases hr5 : r = 5
    · subst hr5
      have hp04 := step4 L[0] L[1] L[2] L[3] L[4]
        (hmemL 0 (by omega)) (hmemL 1 (by omega)) (hmemL 2 (by omega))
        (hmemL 3 (by omega)) (hmemL 4 (by omega))
        (nodup5 0 1 2 3 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by decide))
        (hPL.2.2.2 0 (by omega)) (hPL.2.2.2 1 (by omega))
        (hPL.2.2.2 2 (by omega)) (hPL.2.2.2 3 (by omega))
      exact step2 L[0] L[5] L[4] (hmemL 0 (by omega)) (hmemL 5 (by omega)) (hmemL 4 (by omega))
        (hneL 0 4 (by omega) (by omega) (by omega)) hadjr (hPL.2.2.2 4 (by omega)).symm hp04
    · have hr6 : 6 ≤ r := by omega
      have h0 : 0 < L.length := by omega
      have h1 : 1 < L.length := by omega
      have h2 : 2 < L.length := by omega
      have h3 : 3 < L.length := by omega
      have h4 : 4 < L.length := by omega
      have h5 : 5 < L.length := by omega
      have h6 : 6 < L.length := by omega
      have hp04 := step4 L[0] L[1] L[2] L[3] L[4]
        (hmemL 0 h0) (hmemL 1 h1) (hmemL 2 h2) (hmemL 3 h3) (hmemL 4 h4)
        (nodup5 0 1 2 3 4 h0 h1 h2 h3 h4 (by decide))
        (hPL.2.2.2 0 (by omega)) (hPL.2.2.2 1 (by omega))
        (hPL.2.2.2 2 (by omega)) (hPL.2.2.2 3 (by omega))
      have hp26 := step4 L[2] L[3] L[4] L[5] L[6]
        (hmemL 2 h2) (hmemL 3 h3) (hmemL 4 h4) (hmemL 5 h5) (hmemL 6 h6)
        (nodup5 2 3 4 5 6 h2 h3 h4 h5 h6 (by decide))
        (hPL.2.2.2 2 (by omega)) (hPL.2.2.2 3 (by omega))
        (hPL.2.2.2 4 (by omega)) (hPL.2.2.2 5 (by omega))
      have hp02 := step2 L[0] L[1] L[2] (hmemL 0 h0) (hmemL 1 h1) (hmemL 2 h2)
        (hneL 0 2 h0 h2 (by decide)) (hPL.2.2.2 0 (by omega)) (hPL.2.2.2 1 (by omega))
      apply no8
      apply copy_eight G (p L[0]) L[0] L[1] L[2] (p L[2]) L[6] L[5] L[4]
        (hp_adj L[0] (hmemL 0 h0))
        (hPL.2.2.2 0 (by omega))
        (hPL.2.2.2 1 (by omega))
        (hp_adj L[2] (hmemL 2 h2)).symm
        (hp26 ▸ hp_adj L[6] (hmemL 6 h6))
        (hPL.2.2.2 5 (by omega)).symm
        (hPL.2.2.2 4 (by omega)).symm
        (hp04.symm ▸ (hp_adj L[4] (hmemL 4 h4)).symm)
      have hB0 := hp_mem L[0] (hmemL 0 h0)
      have hB2 := hp_mem L[2] (hmemL 2 h2)
      exact nodup_eight
        (ne_BT _ hB0 _ (hmemL 0 h0)) (ne_BT _ hB0 _ (hmemL 1 h1)) (ne_BT _ hB0 _ (hmemL 2 h2))
        hp02 (ne_BT _ hB0 _ (hmemL 6 h6)) (ne_BT _ hB0 _ (hmemL 5 h5)) (ne_BT _ hB0 _ (hmemL 4 h4))
        (hneL 0 1 h0 h1 (by decide)) (hneL 0 2 h0 h2 (by decide)) (ne_BT _ hB2 _ (hmemL 0 h0)).symm
        (hneL 0 6 h0 h6 (by decide)) (hneL 0 5 h0 h5 (by decide)) (hneL 0 4 h0 h4 (by decide))
        (hneL 1 2 h1 h2 (by decide)) (ne_BT _ hB2 _ (hmemL 1 h1)).symm
        (hneL 1 6 h1 h6 (by decide)) (hneL 1 5 h1 h5 (by decide)) (hneL 1 4 h1 h4 (by decide))
        (ne_BT _ hB2 _ (hmemL 2 h2)).symm (hneL 2 6 h2 h6 (by decide))
        (hneL 2 5 h2 h5 (by decide)) (hneL 2 4 h2 h4 (by decide))
        (ne_BT _ hB2 _ (hmemL 6 h6)) (ne_BT _ hB2 _ (hmemL 5 h5)) (ne_BT _ hB2 _ (hmemL 4 h4))
        (hneL 6 5 h6 h5 (by decide)) (hneL 6 4 h6 h4 (by decide))
        (hneL 5 4 h5 h4 (by decide))

/-- Part 3: Second-neighborhood degree-sum bound from girth `≥ 5` and eccentricity `≥ 3`. -/
private lemma second_neighborhood_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    (ecc : ∀ x : Fin n, ∃ y : Fin n, y ≠ x ∧ ¬ G.Adj x y ∧ ∀ b, ¬ (G.Adj x b ∧ G.Adj b y))
    (x : Fin n) :
    2 + ∑ u ∈ G.neighborFinset x, G.degree u ≤ n := by
  obtain ⟨y, hyx, hnxy, hdist2⟩ := ecc x
  let B := G.neighborFinset x
  let S : Fin n → Finset (Fin n) := fun u => (G.neighborFinset u).erase x
  let S2 : Finset (Fin n) := B.biUnion S
  have hS_disj : (B : Set (Fin n)).PairwiseDisjoint S := by
    intro u1 hu1 u2 hu2 hne
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    obtain ⟨hwx, hwu1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨_, hwu2⟩ := Finset.mem_erase.mp hw2
    have heq := common_unique pair hne
      ((G.mem_neighborFinset x u1).mp hu1).symm ((G.mem_neighborFinset x u2).mp hu2).symm
      ((G.mem_neighborFinset u1 w).mp hwu1) ((G.mem_neighborFinset u2 w).mp hwu2)
    exact hwx heq.symm
  have hS2_card : S2.card = ∑ u ∈ B, (G.degree u - 1) := by
    rw [Finset.card_biUnion hS_disj]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hux : G.Adj u x := ((G.mem_neighborFinset x u).mp hu).symm
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u x).mpr hux), G.card_neighborFinset_eq_degree]
  have hdisj1 : Disjoint ({x, y} : Finset (Fin n)) B := by
    refine Finset.disjoint_left.mpr fun z hz hzB => ?_
    have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hzB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxz.ne rfl
    · exact hnxy hxz
  have hdisj2 : Disjoint (({x, y} : Finset (Fin n)) ∪ B) S2 := by
    refine Finset.disjoint_left.mpr fun z hz hzS2 => ?_
    obtain ⟨u, huB, hzu⟩ := Finset.mem_biUnion.mp hzS2
    obtain ⟨hzx, huz⟩ := Finset.mem_erase.mp hzu
    have hxu : G.Adj x u := (G.mem_neighborFinset x u).mp huB
    have hadj_uz : G.Adj u z := (G.mem_neighborFinset u z).mp huz
    rcases Finset.mem_union.mp hz with hzxy | hzB
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hzxy
      rcases hzxy with rfl | rfl
      · exact hzx rfl
      · exact hdist2 u ⟨hxu, hadj_uz⟩
    · exact tri x u z hxu hadj_uz ((G.mem_neighborFinset x z).mp hzB).symm
  have hcard_all : (({x, y} : Finset (Fin n)) ∪ B ∪ S2).card ≤ n := by
    simpa using Finset.card_le_univ (({x, y} : Finset (Fin n)) ∪ B ∪ S2)
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_pair hyx.symm, hS2_card] at hcard_all
  have hsum_eq : B.card + ∑ u ∈ B, (G.degree u - 1) = ∑ u ∈ B, G.degree u := by
    have hB1 : B.card = ∑ _u ∈ B, 1 := by simp
    rw [hB1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have := hmin.trans (G.minDegree_le_degree u)
    omega
  change 2 + ∑ u ∈ B, G.degree u ≤ n
  omega

/-- Part 4: Helper for Case 2 of the `n = 12` cubic girth-`≥ 5` elimination. -/
private lemma twelve_adj_case {G : SimpleGraph (Fin 12)} [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1)
    (x u1 u2 u3 y1 y2 a1 b1 a2 : Fin 12)
    (hxu1 : G.Adj x u1) (hxu2 : G.Adj x u2) (hxu3 : G.Adj x u3)
    (hu12 : u1 ≠ u2) (hu13 : u1 ≠ u3) (hu23 : u2 ≠ u3)
    (hy12 : G.Adj y1 y2)
    (hy1_not : y1 ∉ ({x, u1, u2, u3} : Finset (Fin 12)) ∪
      ((G.neighborFinset u1).erase x ∪ (G.neighborFinset u2).erase x ∪ (G.neighborFinset u3).erase x))
    (hy2_not : y2 ∉ ({x, u1, u2, u3} : Finset (Fin 12)) ∪
      ((G.neighborFinset u1).erase x ∪ (G.neighborFinset u2).erase x ∪ (G.neighborFinset u3).erase x))
    (huniv : ∀ z : Fin 12, z ∈ ({x, u1, u2, u3} : Finset (Fin 12)) ∪
      ((G.neighborFinset u1).erase x ∪ (G.neighborFinset u2).erase x ∪ (G.neighborFinset u3).erase x) ∨
      z = y1 ∨ z = y2)
    (ha1 : a1 ∈ (G.neighborFinset u1).erase x) (hya1 : G.Adj y1 a1)
    (hb1 : b1 ∈ (G.neighborFinset u1).erase x) (hyb1 : G.Adj y2 b1)
    (ha2 : a2 ∈ (G.neighborFinset u2).erase x) (hya2 : G.Adj y1 a2)
    (hy1_only : ∀ z, G.Adj y1 z → z = y2 ∨ z = a1 ∨ z = a2) :
    cycleGraph 8 ⊑ G := by
  let B' : Finset (Fin 12) := {x, u1, u2, u3}
  let S1 := (G.neighborFinset u1).erase x
  let S2 := (G.neighborFinset u2).erase x
  let S3 := (G.neighborFinset u3).erase x
  have hab1_ne : a1 ≠ b1 := fun h => tri y1 y2 a1 hy12 (h ▸ hyb1) hya1.symm
  have hS_disj12 : Disjoint S1 S2 := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    obtain ⟨hwx, hwu1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨_, hwu2⟩ := Finset.mem_erase.mp hw2
    exact hwx (common_unique pair hu12 hxu1.symm hxu2.symm
      ((G.mem_neighborFinset u1 w).mp hwu1) ((G.mem_neighborFinset u2 w).mp hwu2)).symm
  have hS_disj13 : Disjoint S1 S3 := by
    refine Finset.disjoint_left.mpr fun w hw1 hw3 => ?_
    obtain ⟨hwx, hwu1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨_, hwu3⟩ := Finset.mem_erase.mp hw3
    exact hwx (common_unique pair hu13 hxu1.symm hxu3.symm
      ((G.mem_neighborFinset u1 w).mp hwu1) ((G.mem_neighborFinset u3 w).mp hwu3)).symm
  have hS_disj23 : Disjoint S2 S3 := by
    refine Finset.disjoint_left.mpr fun w hw2 hw3 => ?_
    obtain ⟨hwx, hwu2⟩ := Finset.mem_erase.mp hw2
    obtain ⟨_, hwu3⟩ := Finset.mem_erase.mp hw3
    exact hwx (common_unique pair hu23 hxu2.symm hxu3.symm
      ((G.mem_neighborFinset u2 w).mp hwu2) ((G.mem_neighborFinset u3 w).mp hwu3)).symm
  have hB_eq : G.neighborFinset x = {u1, u2, u3} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h
      · rw [h]; exact (G.mem_neighborFinset x u1).mpr hxu1
      · rw [h]; exact (G.mem_neighborFinset x u2).mpr hxu2
      · rw [h]; exact (G.mem_neighborFinset x u3).mpr hxu3
    · rw [G.card_neighborFinset_eq_degree x, hdeg x]
      simp [hu12, hu13, hu23]
  have hSi_not_xB : ∀ w, w ∈ S1 ∪ S2 ∪ S3 → w ∉ B' := by
    intro w hw hB
    have hwx : w ≠ x := by
      rcases Finset.mem_union.mp hw with hw12 | hw3
      · rcases Finset.mem_union.mp hw12 with hw1 | hw2
        · exact (Finset.mem_erase.mp hw1).1
        · exact (Finset.mem_erase.mp hw2).1
      · exact (Finset.mem_erase.mp hw3).1
    have hwB : G.Adj x w := by
      simp only [B', Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl | rfl | rfl
      · exact (hwx rfl).elim
      · exact hxu1
      · exact hxu2
      · exact hxu3
    rcases Finset.mem_union.mp hw with hw12 | hw3
    · rcases Finset.mem_union.mp hw12 with hw1 | hw2
      · exact tri x u1 w hxu1 ((G.mem_neighborFinset u1 w).mp (Finset.mem_erase.mp hw1).2) hwB.symm
      · exact tri x u2 w hxu2 ((G.mem_neighborFinset u2 w).mp (Finset.mem_erase.mp hw2).2) hwB.symm
    · exact tri x u3 w hxu3 ((G.mem_neighborFinset u3 w).mp (Finset.mem_erase.mp hw3).2) hwB.symm
  have inS1 : ∀ z ∈ S1, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  have inS2 : ∀ z ∈ S2, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  have inS3 : ∀ z ∈ S3, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inr h)
  have ne_B_S : ∀ u ∈ B', ∀ z ∈ S1 ∪ S2 ∪ S3, u ≠ z := fun u hu z hz h => hSi_not_xB z hz (h ▸ hu)
  have ne_12 : ∀ a ∈ S1, ∀ b ∈ S2, a ≠ b := fun a ha b hb h => Finset.disjoint_left.mp hS_disj12 ha (h ▸ hb)
  have ne_13 : ∀ a ∈ S1, ∀ b ∈ S3, a ≠ b := fun a ha b hb h => Finset.disjoint_left.mp hS_disj13 ha (h ▸ hb)
  have ne_23 : ∀ a ∈ S2, ∀ b ∈ S3, a ≠ b := fun a ha b hb h => Finset.disjoint_left.mp hS_disj23 ha (h ▸ hb)
  have ne_y1_B : ∀ u ∈ B', y1 ≠ u := fun u hu h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inl hu))
  have ne_y2_B : ∀ u ∈ B', y2 ≠ u := fun u hu h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inl hu))
  have ne_y1_S : ∀ z ∈ S1 ∪ S2 ∪ S3, y1 ≠ z := fun z hz h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inr hz))
  have ne_y2_S : ∀ z ∈ S1 ∪ S2 ∪ S3, y2 ≠ z := fun z hz h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inr hz))
  have hxB : x ∈ B' := by simp [B']
  have hu1B : u1 ∈ B' := by simp [B']
  have hu2B : u2 ∈ B' := by simp [B']
  have hu3B : u3 ∈ B' := by simp [B']
  have hy_not_xB : ∀ y, (y = y1 ∨ y = y2) → ∀ z ∈ B', ¬ G.Adj y z := by
    intro y hy z hz hyz
    have hy_out : y ∉ B' ∪ (S1 ∪ S2 ∪ S3) := by
      rcases hy with rfl | rfl <;> assumption
    have hz' : z = x ∨ z = u1 ∨ z = u2 ∨ z = u3 := by simpa [B'] using hz
    rcases hz' with h | h | h | h
    · rw [h] at hyz
      have hyB : y ∈ ({u1, u2, u3} : Finset (Fin 12)) := hB_eq ▸ (G.mem_neighborFinset x y).mpr hyz.symm
      have hyB' : y = u1 ∨ y = u2 ∨ y = u3 := by simpa using hyB
      rcases hyB' with h' | h' | h'
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu1B)))
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu2B)))
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu3B)))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS1 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u1 y).mpr hyz.symm⟩))))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS2 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u2 y).mpr hyz.symm⟩))))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS3 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u3 y).mpr hyz.symm⟩))))
  have hy2_third : ∃ w ∈ S2 ∪ S3, G.Adj y2 w := by
    have hsub2 : G.neighborFinset y2 \ {y1, b1} ⊆ S2 ∪ S3 := by
      intro z hz
      obtain ⟨hzN, hz_not⟩ := Finset.mem_sdiff.mp hz
      have hy2z : G.Adj y2 z := (G.mem_neighborFinset y2 z).mp hzN
      rcases huniv z with hzU | rfl | rfl
      · rcases Finset.mem_union.mp hzU with hzB | hzS
        · exact (hy_not_xB y2 (Or.inr rfl) z hzB hy2z).elim
        · rcases Finset.mem_union.mp hzS with hz12 | hz3
          · rcases Finset.mem_union.mp hz12 with hz1 | hz2
            · have hzb1 : z = b1 := common_unique pair (ne_y2_B u1 hu1B).symm
                ((G.mem_neighborFinset u1 z).mp (Finset.mem_erase.mp hz1).2) hy2z
                ((G.mem_neighborFinset u1 b1).mp (Finset.mem_erase.mp hb1).2) hyb1
              exact (hz_not (by simp [hzb1])).elim
            · exact Finset.mem_union.mpr (Or.inl hz2)
          · exact Finset.mem_union.mpr (Or.inr hz3)
      · exact (hz_not (by simp)).elim
      · exact (hy2z.ne rfl).elim
    have hc : 1 ≤ (G.neighborFinset y2 \ {y1, b1}).card := by
      have h1 := Finset.card_sdiff_add_card_inter (G.neighborFinset y2) {y1, b1}
      have h2 : ((G.neighborFinset y2) ∩ {y1, b1}).card ≤ ({y1, b1} : Finset (Fin 12)).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h3 : ({y1, b1} : Finset (Fin 12)).card ≤ 2 := Finset.card_insert_le _ _
      rw [G.card_neighborFinset_eq_degree y2, hdeg y2] at h1
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 1) hc)
    exact ⟨w, hsub2 hw, (G.mem_neighborFinset y2 w).mp (Finset.mem_sdiff.mp hw).1⟩
  obtain ⟨w, hw23, hy2w⟩ := hy2_third
  rcases Finset.mem_union.mp hw23 with hw2 | hw3
  · -- Subcase B1: w ∈ S2
    have ha2w : a2 ≠ w := fun h => tri y1 y2 a2 hy12 (h ▸ hy2w) hya2.symm
    apply copy_eight G u1 a1 y1 a2 u2 w y2 b1
      ((G.mem_neighborFinset u1 a1).mp (Finset.mem_erase.mp ha1).2)
      hya1.symm hya2
      ((G.mem_neighborFinset u2 a2).mp (Finset.mem_erase.mp ha2).2).symm
      ((G.mem_neighborFinset u2 w).mp (Finset.mem_erase.mp hw2).2)
      hy2w.symm hyb1
      ((G.mem_neighborFinset u1 b1).mp (Finset.mem_erase.mp hb1).2).symm
    exact nodup_eight
      (ne_B_S u1 hu1B a1 (inS1 a1 ha1)) (ne_y1_B u1 hu1B).symm (ne_B_S u1 hu1B a2 (inS2 a2 ha2))
      hu12 (ne_B_S u1 hu1B w (inS2 w hw2)) (ne_y2_B u1 hu1B).symm (ne_B_S u1 hu1B b1 (inS1 b1 hb1))
      (ne_y1_S a1 (inS1 a1 ha1)).symm (ne_12 a1 ha1 a2 ha2) (ne_B_S u2 hu2B a1 (inS1 a1 ha1)).symm
      (ne_12 a1 ha1 w hw2) (ne_y2_S a1 (inS1 a1 ha1)).symm hab1_ne
      (ne_y1_S a2 (inS2 a2 ha2)) (ne_y1_B u2 hu2B) (ne_y1_S w (inS2 w hw2))
      hy12.ne (ne_y1_S b1 (inS1 b1 hb1))
      (ne_B_S u2 hu2B a2 (inS2 a2 ha2)).symm ha2w (ne_y2_S a2 (inS2 a2 ha2)).symm (ne_12 b1 hb1 a2 ha2).symm
      (ne_B_S u2 hu2B w (inS2 w hw2)) (ne_y2_B u2 hu2B).symm (ne_B_S u2 hu2B b1 (inS1 b1 hb1))
      (ne_y2_S w (inS2 w hw2)).symm (ne_12 b1 hb1 w hw2).symm
      (ne_y2_S b1 (inS1 b1 hb1))
  · -- Subcase B2: w ∈ S3 (call b3 := w). Pick c2 ∈ S2 \ {a2}.
    let b3 := w
    have hS2_card : S2.card = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u2 x).mpr hxu2.symm),
        G.card_neighborFinset_eq_degree u2, hdeg u2]
    obtain ⟨c2, hc2_mem⟩ : ∃ c2, c2 ∈ S2.erase a2 := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha2, hS2_card]
      decide
    obtain ⟨hc2_ne_a2, hc2⟩ := Finset.mem_erase.mp hc2_mem
    have hc2_not_y1 : ¬ G.Adj c2 y1 := by
      intro h
      rcases hy1_only c2 h.symm with hc | hc | hc
      · exact ne_y2_S c2 (inS2 c2 hc2) hc.symm
      · exact ne_12 a1 ha1 c2 hc2 hc.symm
      · exact hc2_ne_a2 hc
    have hy2_set : G.neighborFinset y2 = {y1, b1, b3} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with h | h | h
        · rw [h]; exact (G.mem_neighborFinset y2 y1).mpr hy12.symm
        · rw [h]; exact (G.mem_neighborFinset y2 b1).mpr hyb1
        · rw [h]; exact (G.mem_neighborFinset y2 b3).mpr hy2w
      · rw [G.card_neighborFinset_eq_degree y2, hdeg y2]
        have hy1_b1 : y1 ≠ b1 := ne_y1_S b1 (inS1 b1 hb1)
        have hy1_b3 : y1 ≠ b3 := ne_y1_S b3 (inS3 b3 hw3)
        have hb1_b3 : b1 ≠ b3 := ne_13 b1 hb1 b3 hw3
        simp [hy1_b1, hy1_b3, hb1_b3]
    have hc2_not_y2' : ¬ G.Adj c2 y2 := by
      intro h
      have hm : c2 ∈ G.neighborFinset y2 := (G.mem_neighborFinset y2 c2).mpr h.symm
      rw [hy2_set] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hc | hc | hc
      · exact ne_y1_S c2 (inS2 c2 hc2) hc.symm
      · exact ne_12 b1 hb1 c2 hc2 hc.symm
      · exact ne_23 c2 hc2 b3 hw3 hc
    have hc2_sub : (G.neighborFinset c2).erase u2 ⊆ S1 ∪ S3 := by
      intro z hz
      obtain ⟨hzu2, hzc2⟩ := Finset.mem_erase.mp hz
      have hc2z : G.Adj c2 z := (G.mem_neighborFinset c2 z).mp hzc2
      rcases huniv z with hzU | rfl | rfl
      · rcases Finset.mem_union.mp hzU with hzB | hzS
        · exfalso
          have hz' : z = x ∨ z = u1 ∨ z = u2 ∨ z = u3 := by simpa [B'] using hzB
          rcases hz' with h | h | h | h
          · rw [h] at hc2z
            exact tri x u2 c2 hxu2 ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2) hc2z
          · rw [h] at hc2z
            have hx_eq := common_unique pair hu12 hxu1.symm hxu2.symm hc2z.symm
              ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2)
            exact (Finset.mem_erase.mp hc2).1 hx_eq.symm
          · exact hzu2 h
          · rw [h] at hc2z
            have hx_eq := common_unique pair hu23 hxu2.symm hxu3.symm
              ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2) hc2z.symm
            exact (Finset.mem_erase.mp hc2).1 hx_eq.symm
        · rcases Finset.mem_union.mp hzS with hz12 | hz3
          · rcases Finset.mem_union.mp hz12 with hz1 | hz2
            · exact Finset.mem_union.mpr (Or.inl hz1)
            · exfalso
              exact tri u2 c2 z ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2)
                hc2z ((G.mem_neighborFinset u2 z).mp (Finset.mem_erase.mp hz2).2).symm
          · exact Finset.mem_union.mpr (Or.inr hz3)
      · exact (hc2_not_y1 hc2z).elim
      · exact (hc2_not_y2' hc2z).elim
    have hc2_S1_le : ((G.neighborFinset c2) ∩ S1).card ≤ 1 := by
      have hsub : (G.neighborFinset c2) ∩ S1 ⊆ (G.neighborFinset c2) ∩ G.neighborFinset u1 :=
        Finset.inter_subset_inter_left (Finset.erase_subset _ _)
      exact (Finset.card_le_card hsub).trans (pair c2 u1 (ne_B_S u1 hu1B c2 (inS2 c2 hc2)).symm)
    have hc2_S3 : ∃ z3 ∈ S3, G.Adj c2 z3 := by
      have hsub3 : ((G.neighborFinset c2).erase u2) \ S1 ⊆ S3 := by
        intro z hz
        obtain ⟨hz1, hznot1⟩ := Finset.mem_sdiff.mp hz
        exact (Finset.mem_union.mp (hc2_sub hz1)).resolve_left hznot1
      have hc_er : ((G.neighborFinset c2).erase u2).card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset c2 u2).mpr
          ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2).symm),
          G.card_neighborFinset_eq_degree c2, hdeg c2]
      have hsplit := Finset.card_sdiff_add_card_inter ((G.neighborFinset c2).erase u2) S1
      have hinter : (((G.neighborFinset c2).erase u2) ∩ S1).card ≤ ((G.neighborFinset c2) ∩ S1).card :=
        Finset.card_le_card (Finset.inter_subset_inter_right (Finset.erase_subset _ _))
      have hpos : 0 < (((G.neighborFinset c2).erase u2) \ S1).card := by omega
      obtain ⟨z3, hz3⟩ := Finset.card_pos.mp hpos
      exact ⟨z3, hsub3 hz3, (G.mem_neighborFinset c2 z3).mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hz3).1).2⟩
    obtain ⟨z3, hz3, hc2z3⟩ := hc2_S3
    by_cases hzb3 : z3 = b3
    · -- z3 = b3: [x, u2, c2, b3, y2, y1, a1, u1] is a C8
      subst hzb3
      apply copy_eight G x u2 c2 b3 y2 y1 a1 u1
        hxu2
        ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2)
        hc2z3 hy2w.symm hy12.symm hya1
        ((G.mem_neighborFinset u1 a1).mp (Finset.mem_erase.mp ha1).2).symm
        hxu1.symm
      exact nodup_eight
        hxu2.ne (ne_B_S x hxB c2 (inS2 c2 hc2)) (ne_B_S x hxB b3 (inS3 b3 hw3))
        (ne_y2_B x hxB).symm (ne_y1_B x hxB).symm (ne_B_S x hxB a1 (inS1 a1 ha1)) hxu1.ne
        (ne_B_S u2 hu2B c2 (inS2 c2 hc2)) (ne_B_S u2 hu2B b3 (inS3 b3 hw3))
        (ne_y2_B u2 hu2B).symm (ne_y1_B u2 hu2B).symm (ne_B_S u2 hu2B a1 (inS1 a1 ha1)) hu12.symm
        (ne_23 c2 hc2 b3 hw3) (ne_y2_S c2 (inS2 c2 hc2)).symm (ne_y1_S c2 (inS2 c2 hc2)).symm
        (ne_12 a1 ha1 c2 hc2).symm (ne_B_S u1 hu1B c2 (inS2 c2 hc2)).symm
        (ne_y2_S b3 (inS3 b3 hw3)).symm (ne_y1_S b3 (inS3 b3 hw3)).symm
        (ne_13 a1 ha1 b3 hw3).symm (ne_B_S u1 hu1B b3 (inS3 b3 hw3)).symm
        hy12.ne.symm (ne_y2_S a1 (inS1 a1 ha1)) (ne_y2_B u1 hu1B)
        (ne_y1_S a1 (inS1 a1 ha1)) (ne_y1_B u1 hu1B)
        (ne_B_S u1 hu1B a1 (inS1 a1 ha1)).symm
    · -- z3 ≠ b3: [u3, b3, y2, y1, a2, u2, c2, z3] is a C8
      apply copy_eight G u3 b3 y2 y1 a2 u2 c2 z3
        ((G.mem_neighborFinset u3 b3).mp (Finset.mem_erase.mp hw3).2)
        hy2w.symm hy12.symm hya2
        ((G.mem_neighborFinset u2 a2).mp (Finset.mem_erase.mp ha2).2).symm
        ((G.mem_neighborFinset u2 c2).mp (Finset.mem_erase.mp hc2).2)
        hc2z3
        ((G.mem_neighborFinset u3 z3).mp (Finset.mem_erase.mp hz3).2).symm
      exact nodup_eight
        (ne_B_S u3 hu3B b3 (inS3 b3 hw3)) (ne_y2_B u3 hu3B).symm (ne_y1_B u3 hu3B).symm
        (ne_B_S u3 hu3B a2 (inS2 a2 ha2)) hu23.symm (ne_B_S u3 hu3B c2 (inS2 c2 hc2))
        (ne_B_S u3 hu3B z3 (inS3 z3 hz3))
        (ne_y2_S b3 (inS3 b3 hw3)).symm (ne_y1_S b3 (inS3 b3 hw3)).symm
        (ne_23 a2 ha2 b3 hw3).symm (ne_B_S u2 hu2B b3 (inS3 b3 hw3)).symm
        (ne_23 c2 hc2 b3 hw3).symm (Ne.symm hzb3)
        hy12.ne.symm (ne_y2_S a2 (inS2 a2 ha2)) (ne_y2_B u2 hu2B)
        (ne_y2_S c2 (inS2 c2 hc2)) (ne_y2_S z3 (inS3 z3 hz3))
        (ne_y1_S a2 (inS2 a2 ha2)) (ne_y1_B u2 hu2B)
        (ne_y1_S c2 (inS2 c2 hc2)) (ne_y1_S z3 (inS3 z3 hz3))
        (ne_B_S u2 hu2B a2 (inS2 a2 ha2)).symm hc2_ne_a2.symm (ne_23 a2 ha2 z3 hz3)
        (ne_B_S u2 hu2B c2 (inS2 c2 hc2)) (ne_B_S u2 hu2B z3 (inS3 z3 hz3))
        (ne_23 c2 hc2 z3 hz3)

/-- Part 4b: Every `12`-vertex cubic graph of girth `≥ 5` contains `C8`. -/
private lemma cubic_twelve_has_c8 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (pair : ∀ a b, a ≠ b → ((G.neighborFinset a) ∩ G.neighborFinset b).card ≤ 1) :
    cycleGraph 8 ⊑ G := by
  let x : Fin 12 := 0
  have hBx_card : (G.neighborFinset x).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg x]
  obtain ⟨u1, u2, u3, hu12, hu13, hu23, hBx⟩ := Finset.card_eq_three.mp hBx_card
  have hxu1 : G.Adj x u1 := (G.mem_neighborFinset x u1).mp (by rw [hBx]; simp)
  have hxu2 : G.Adj x u2 := (G.mem_neighborFinset x u2).mp (by rw [hBx]; simp)
  have hxu3 : G.Adj x u3 := (G.mem_neighborFinset x u3).mp (by rw [hBx]; simp)
  let B' : Finset (Fin 12) := {x, u1, u2, u3}
  let S1 := (G.neighborFinset u1).erase x
  let S2 := (G.neighborFinset u2).erase x
  let S3 := (G.neighborFinset u3).erase x
  have hxB : x ∈ B' := by simp [B']
  have hu1B : u1 ∈ B' := by simp [B']
  have hu2B : u2 ∈ B' := by simp [B']
  have hu3B : u3 ∈ B' := by simp [B']
  have inS1 : ∀ z ∈ S1, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
  have inS2 : ∀ z ∈ S2, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
  have inS3 : ∀ z ∈ S3, z ∈ S1 ∪ S2 ∪ S3 := fun _ h =>
    Finset.mem_union.mpr (Or.inr h)
  have hS1_card : S1.card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u1 x).mpr hxu1.symm),
      G.card_neighborFinset_eq_degree, hdeg u1]
  have hS2_card : S2.card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u2 x).mpr hxu2.symm),
      G.card_neighborFinset_eq_degree, hdeg u2]
  have hS3_card : S3.card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u3 x).mpr hxu3.symm),
      G.card_neighborFinset_eq_degree, hdeg u3]
  have hS_disj12 : Disjoint S1 S2 := by
    refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
    obtain ⟨hwx, hwu1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨_, hwu2⟩ := Finset.mem_erase.mp hw2
    exact hwx (common_unique pair hu12 hxu1.symm hxu2.symm
      ((G.mem_neighborFinset u1 w).mp hwu1) ((G.mem_neighborFinset u2 w).mp hwu2)).symm
  have hS_disj13 : Disjoint S1 S3 := by
    refine Finset.disjoint_left.mpr fun w hw1 hw3 => ?_
    obtain ⟨hwx, hwu1⟩ := Finset.mem_erase.mp hw1
    obtain ⟨_, hwu3⟩ := Finset.mem_erase.mp hw3
    exact hwx (common_unique pair hu13 hxu1.symm hxu3.symm
      ((G.mem_neighborFinset u1 w).mp hwu1) ((G.mem_neighborFinset u3 w).mp hwu3)).symm
  have hS_disj23 : Disjoint S2 S3 := by
    refine Finset.disjoint_left.mpr fun w hw2 hw3 => ?_
    obtain ⟨hwx, hwu2⟩ := Finset.mem_erase.mp hw2
    obtain ⟨_, hwu3⟩ := Finset.mem_erase.mp hw3
    exact hwx (common_unique pair hu23 hxu2.symm hxu3.symm
      ((G.mem_neighborFinset u2 w).mp hwu2) ((G.mem_neighborFinset u3 w).mp hwu3)).symm
  let U := B' ∪ (S1 ∪ S2 ∪ S3)
  have hdisj_B_S : Disjoint B' (S1 ∪ S2 ∪ S3) := by
    refine Finset.disjoint_left.mpr fun z hzB hzS => ?_
    have hzx : z ≠ x := by
      rcases Finset.mem_union.mp hzS with hz12 | hz3
      · rcases Finset.mem_union.mp hz12 with hz1 | hz2
        · exact (Finset.mem_erase.mp hz1).1
        · exact (Finset.mem_erase.mp hz2).1
      · exact (Finset.mem_erase.mp hz3).1
    have hxz : G.Adj x z := by
      simp only [B', Finset.mem_insert, Finset.mem_singleton] at hzB
      rcases hzB with rfl | rfl | rfl | rfl
      · exact (hzx rfl).elim
      · exact hxu1
      · exact hxu2
      · exact hxu3
    rcases Finset.mem_union.mp hzS with hz12 | hz3
    · rcases Finset.mem_union.mp hz12 with hz1 | hz2
      · exact tri x u1 z hxu1 ((G.mem_neighborFinset u1 z).mp (Finset.mem_erase.mp hz1).2) hxz.symm
      · exact tri x u2 z hxu2 ((G.mem_neighborFinset u2 z).mp (Finset.mem_erase.mp hz2).2) hxz.symm
    · exact tri x u3 z hxu3 ((G.mem_neighborFinset u3 z).mp (Finset.mem_erase.mp hz3).2) hxz.symm
  have hU_card : U.card = 10 := by
    have hB4 : B'.card = 4 := by
      simp [B', hxu1.ne, hxu2.ne, hxu3.ne, hu12, hu13, hu23]
    have hS123 : (S1 ∪ S2 ∪ S3).card = 6 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hS_disj13, hS_disj23⟩),
        Finset.card_union_of_disjoint hS_disj12, hS1_card, hS2_card, hS3_card]
    rw [Finset.card_union_of_disjoint hdisj_B_S, hB4, hS123]
  have hR_card : (univ \ U).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hU_card]
  obtain ⟨y1, y2, hy12_ne, hR_eq⟩ := Finset.card_eq_two.mp hR_card
  have hy1_not : y1 ∉ U := (Finset.mem_sdiff.mp (by rw [hR_eq]; simp)).2
  have hy2_not : y2 ∉ U := (Finset.mem_sdiff.mp (by rw [hR_eq]; simp)).2
  have huniv : ∀ z : Fin 12, z ∈ U ∨ z = y1 ∨ z = y2 := by
    intro z
    by_cases hz : z ∈ U
    · exact Or.inl hz
    · have hzR : z ∈ univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
      rw [hR_eq] at hzR
      exact Or.inr (by simpa using hzR)
  have hy_not_xB : ∀ y, (y = y1 ∨ y = y2) → ∀ z ∈ B', ¬ G.Adj y z := by
    intro y hy z hz hyz
    have hy_out : y ∉ U := by rcases hy with rfl | rfl <;> assumption
    have hz' : z = x ∨ z = u1 ∨ z = u2 ∨ z = u3 := by simpa [B'] using hz
    rcases hz' with h | h | h | h
    · rw [h] at hyz
      have hyB : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hyz.symm
      rw [hBx] at hyB
      have hyB' : y = u1 ∨ y = u2 ∨ y = u3 := by simpa using hyB
      rcases hyB' with h' | h' | h'
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu1B)))
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu2B)))
      · exact hy_out (Finset.mem_union.mpr (Or.inl (h' ▸ hu3B)))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS1 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u1 y).mpr hyz.symm⟩))))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS2 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u2 y).mpr hyz.symm⟩))))
    · rw [h] at hyz
      have hyx_ne : y ≠ x := fun hx => hy_out (Finset.mem_union.mpr (Or.inl (hx ▸ hxB)))
      exact hy_out (Finset.mem_union.mpr (Or.inr (inS3 y (Finset.mem_erase.mpr ⟨hyx_ne, (G.mem_neighborFinset u3 y).mpr hyz.symm⟩))))
  have hy_Si_le : ∀ y, (y = y1 ∨ y = y2) →
      ((G.neighborFinset y) ∩ S1).card ≤ 1 ∧
      ((G.neighborFinset y) ∩ S2).card ≤ 1 ∧
      ((G.neighborFinset y) ∩ S3).card ≤ 1 := by
    intro y hy
    have hy_out : y ∉ U := by rcases hy with rfl | rfl <;> assumption
    refine ⟨?_, ?_, ?_⟩
    · exact (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))).trans
        (pair y u1 (fun h => hy_out (Finset.mem_union.mpr (Or.inl (h ▸ hu1B)))))
    · exact (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))).trans
        (pair y u2 (fun h => hy_out (Finset.mem_union.mpr (Or.inl (h ▸ hu2B)))))
    · exact (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset _ _))).trans
        (pair y u3 (fun h => hy_out (Finset.mem_union.mpr (Or.inl (h ▸ hu3B)))))
  by_cases hy12 : G.Adj y1 y2
  · -- Adjacent case
    have hy1_S : (G.neighborFinset y1).erase y2 ⊆ S1 ∪ S2 ∪ S3 := by
      intro z hz
      obtain ⟨hzy2, hzy1⟩ := Finset.mem_erase.mp hz
      have hadj := (G.mem_neighborFinset y1 z).mp hzy1
      rcases huniv z with hzU | rfl | rfl
      · exact (Finset.mem_union.mp hzU).resolve_left fun hzB => hy_not_xB y1 (Or.inl rfl) z hzB hadj
      · exact (hadj.ne rfl).elim
      · exact (hzy2 rfl).elim
    have hy2_S : (G.neighborFinset y2).erase y1 ⊆ S1 ∪ S2 ∪ S3 := by
      intro z hz
      obtain ⟨hzy1, hzy2⟩ := Finset.mem_erase.mp hz
      have hadj := (G.mem_neighborFinset y2 z).mp hzy2
      rcases huniv z with hzU | rfl | rfl
      · exact (Finset.mem_union.mp hzU).resolve_left fun hzB => hy_not_xB y2 (Or.inr rfl) z hzB hadj
      · exact (hzy1 rfl).elim
      · exact (hadj.ne rfl).elim
    have hc1 : ((G.neighborFinset y1).erase y2).card = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y1 y2).mpr hy12),
        G.card_neighborFinset_eq_degree, hdeg y1]
    have hc2 : ((G.neighborFinset y2).erase y1).card = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y2 y1).mpr hy12.symm),
        G.card_neighborFinset_eq_degree, hdeg y2]
    have hle1 := hy_Si_le y1 (Or.inl rfl)
    have hle2 := hy_Si_le y2 (Or.inr rfl)
    have hsum1 : ((G.neighborFinset y1) ∩ S1).card + ((G.neighborFinset y1) ∩ S2).card +
        ((G.neighborFinset y1) ∩ S3).card = 2 := by
      have heq : (G.neighborFinset y1).erase y2 =
          ((G.neighborFinset y1) ∩ S1) ∪ ((G.neighborFinset y1) ∩ S2) ∪ ((G.neighborFinset y1) ∩ S3) := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hz
          rcases Finset.mem_union.mp (hy1_S (Finset.mem_erase.mpr hz)) with h12 | h3
          · rcases Finset.mem_union.mp h12 with h1 | h2
            · exact Or.inl (Or.inl ⟨hz.2, h1⟩)
            · exact Or.inl (Or.inr ⟨hz.2, h2⟩)
          · exact Or.inr ⟨hz.2, h3⟩
        · rintro ((⟨hzN, hz1⟩ | ⟨hzN, hz2⟩) | ⟨hzN, hz3⟩)
          · exact ⟨fun h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inr (inS1 z hz1))), hzN⟩
          · exact ⟨fun h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inr (inS2 z hz2))), hzN⟩
          · exact ⟨fun h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inr (inS3 z hz3))), hzN⟩
      have hd12 : Disjoint ((G.neighborFinset y1) ∩ S1) ((G.neighborFinset y1) ∩ S2) :=
        hS_disj12.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd13 : Disjoint ((G.neighborFinset y1) ∩ S1) ((G.neighborFinset y1) ∩ S3) :=
        hS_disj13.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd23 : Disjoint ((G.neighborFinset y1) ∩ S2) ((G.neighborFinset y1) ∩ S3) :=
        hS_disj23.mono Finset.inter_subset_right Finset.inter_subset_right
      rw [← hc1, heq, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12]
    have hsum2 : ((G.neighborFinset y2) ∩ S1).card + ((G.neighborFinset y2) ∩ S2).card +
        ((G.neighborFinset y2) ∩ S3).card = 2 := by
      have heq : (G.neighborFinset y2).erase y1 =
          ((G.neighborFinset y2) ∩ S1) ∪ ((G.neighborFinset y2) ∩ S2) ∪ ((G.neighborFinset y2) ∩ S3) := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hz
          rcases Finset.mem_union.mp (hy2_S (Finset.mem_erase.mpr hz)) with h12 | h3
          · rcases Finset.mem_union.mp h12 with h1 | h2
            · exact Or.inl (Or.inl ⟨hz.2, h1⟩)
            · exact Or.inl (Or.inr ⟨hz.2, h2⟩)
          · exact Or.inr ⟨hz.2, h3⟩
        · rintro ((⟨hzN, hz1⟩ | ⟨hzN, hz2⟩) | ⟨hzN, hz3⟩)
          · exact ⟨fun h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inr (inS1 z hz1))), hzN⟩
          · exact ⟨fun h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inr (inS2 z hz2))), hzN⟩
          · exact ⟨fun h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inr (inS3 z hz3))), hzN⟩
      have hd12 : Disjoint ((G.neighborFinset y2) ∩ S1) ((G.neighborFinset y2) ∩ S2) :=
        hS_disj12.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd13 : Disjoint ((G.neighborFinset y2) ∩ S1) ((G.neighborFinset y2) ∩ S3) :=
        hS_disj13.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd23 : Disjoint ((G.neighborFinset y2) ∩ S2) ((G.neighborFinset y2) ∩ S3) :=
        hS_disj23.mono Finset.inter_subset_right Finset.inter_subset_right
      rw [← hc2, heq, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12]
    have apply_perm : ∀ v1 v2 v3 : Fin 12,
        G.Adj x v1 → G.Adj x v2 → G.Adj x v3 → v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
        ({v1, v2, v3} : Finset (Fin 12)) = {u1, u2, u3} →
        (G.neighborFinset v1).erase x ∪ (G.neighborFinset v2).erase x ∪ (G.neighborFinset v3).erase x =
          S1 ∪ S2 ∪ S3 →
        ((G.neighborFinset y1) ∩ (G.neighborFinset v1).erase x).card = 1 →
        ((G.neighborFinset y2) ∩ (G.neighborFinset v1).erase x).card = 1 →
        ((G.neighborFinset y1) ∩ (G.neighborFinset v2).erase x).card = 1 →
        cycleGraph 8 ⊑ G := by
      intro v1 v2 v3 hv1 hv2 hv3 h12' h13' h23' hset hS_perm ha1c hb1c ha2c
      have hU_eq : ({x, v1, v2, v3} : Finset (Fin 12)) ∪
          ((G.neighborFinset v1).erase x ∪ (G.neighborFinset v2).erase x ∪ (G.neighborFinset v3).erase x) = U := by
        have hB_perm : ({x, v1, v2, v3} : Finset (Fin 12)) = B' := by
          change insert x ({v1, v2, v3} : Finset (Fin 12)) = insert x ({u1, u2, u3} : Finset (Fin 12))
          rw [hset]
        dsimp only [U]
        rw [hB_perm, hS_perm]
      obtain ⟨a1, ha1_inter⟩ := Finset.card_eq_one.mp ha1c
      obtain ⟨b1, hb1_inter⟩ := Finset.card_eq_one.mp hb1c
      obtain ⟨a2, ha2_inter⟩ := Finset.card_eq_one.mp ha2c
      have ha1_mem : a1 ∈ (G.neighborFinset y1) ∩ (G.neighborFinset v1).erase x := by rw [ha1_inter]; simp
      have hb1_mem : b1 ∈ (G.neighborFinset y2) ∩ (G.neighborFinset v1).erase x := by rw [hb1_inter]; simp
      have ha2_mem : a2 ∈ (G.neighborFinset y1) ∩ (G.neighborFinset v2).erase x := by rw [ha2_inter]; simp
      obtain ⟨hya1, ha1S⟩ := Finset.mem_inter.mp ha1_mem
      obtain ⟨hyb1, hb1S⟩ := Finset.mem_inter.mp hb1_mem
      obtain ⟨hya2, ha2S⟩ := Finset.mem_inter.mp ha2_mem
      have ha1_ne_a2 : a1 ≠ a2 := by
        intro h
        subst h
        have hux := common_unique pair h12' hv1.symm hv2.symm
          ((G.mem_neighborFinset v1 a1).mp (Finset.mem_erase.mp ha1S).2)
          ((G.mem_neighborFinset v2 a1).mp (Finset.mem_erase.mp ha2S).2)
        exact (Finset.mem_erase.mp ha1S).1 hux.symm
      have hy1_set : G.neighborFinset y1 = {y2, a1, a2} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with h | h | h
          · rw [h]; exact (G.mem_neighborFinset y1 y2).mpr hy12
          · rw [h]; exact hya1
          · rw [h]; exact hya2
        · rw [G.card_neighborFinset_eq_degree y1, hdeg y1]
          have hy2_a1 : y2 ≠ a1 := fun h => hy2_not (hU_eq ▸ h ▸ Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ha1S))))))
          have hy2_a2 : y2 ≠ a2 := fun h => hy2_not (hU_eq ▸ h ▸ Finset.mem_union.mpr (Or.inr
            (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ha2S))))))
          simp [hy2_a1, hy2_a2, ha1_ne_a2]
      exact twelve_adj_case hdeg tri pair x v1 v2 v3 y1 y2 a1 b1 a2 hv1 hv2 hv3 h12' h13' h23' hy12
        (by rwa [hU_eq]) (by rwa [hU_eq]) (by intro z; rw [hU_eq]; exact huniv z)
        ha1S ((G.mem_neighborFinset y1 a1).mp hya1)
        hb1S ((G.mem_neighborFinset y2 b1).mp hyb1)
        ha2S ((G.mem_neighborFinset y1 a2).mp hya2)
        (fun z hz => by
          have hm : z ∈ G.neighborFinset y1 := (G.mem_neighborFinset y1 z).mpr hz
          rw [hy1_set] at hm; simpa using hm)
    have hcases :
        (((G.neighborFinset y1) ∩ S1).card = 1 ∧ ((G.neighborFinset y2) ∩ S1).card = 1 ∧ ((G.neighborFinset y1) ∩ S2).card = 1) ∨
        (((G.neighborFinset y1) ∩ S1).card = 1 ∧ ((G.neighborFinset y2) ∩ S1).card = 1 ∧ ((G.neighborFinset y1) ∩ S3).card = 1) ∨
        (((G.neighborFinset y1) ∩ S2).card = 1 ∧ ((G.neighborFinset y2) ∩ S2).card = 1 ∧ ((G.neighborFinset y1) ∩ S1).card = 1) ∨
        (((G.neighborFinset y1) ∩ S2).card = 1 ∧ ((G.neighborFinset y2) ∩ S2).card = 1 ∧ ((G.neighborFinset y1) ∩ S3).card = 1) ∨
        (((G.neighborFinset y1) ∩ S3).card = 1 ∧ ((G.neighborFinset y2) ∩ S3).card = 1 ∧ ((G.neighborFinset y1) ∩ S1).card = 1) ∨
        (((G.neighborFinset y1) ∩ S3).card = 1 ∧ ((G.neighborFinset y2) ∩ S3).card = 1 ∧ ((G.neighborFinset y1) ∩ S2).card = 1) := by
      omega
    rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact apply_perm u1 u2 u3 hxu1 hxu2 hxu3 hu12 hu13 hu23 rfl rfl h1 h2 h3
    · exact apply_perm u1 u3 u2 hxu1 hxu3 hxu2 hu13 hu12 hu23.symm
        (congrArg (insert u1) (Finset.pair_comm u3 u2))
        (by change S1 ∪ S3 ∪ S2 = S1 ∪ S2 ∪ S3; rw [Finset.union_assoc, Finset.union_comm S3 S2, ← Finset.union_assoc])
        h1 h2 h3
    · exact apply_perm u2 u1 u3 hxu2 hxu1 hxu3 hu12.symm hu23 hu13
        (Finset.insert_comm u2 u1 {u3})
        (by change S2 ∪ S1 ∪ S3 = S1 ∪ S2 ∪ S3; rw [Finset.union_comm S2 S1])
        h1 h2 h3
    · exact apply_perm u2 u3 u1 hxu2 hxu3 hxu1 hu23 hu12.symm hu13.symm
        ((congrArg (insert u2) (Finset.pair_comm u3 u1)).trans (Finset.insert_comm u2 u1 {u3}))
        (by change S2 ∪ S3 ∪ S1 = S1 ∪ S2 ∪ S3; rw [Finset.union_comm (S2 ∪ S3) S1, ← Finset.union_assoc])
        h1 h2 h3
    · exact apply_perm u3 u1 u2 hxu3 hxu1 hxu2 hu13.symm hu23.symm hu12
        ((Finset.insert_comm u3 u1 {u2}).trans (congrArg (insert u1) (Finset.pair_comm u3 u2)))
        (by change S3 ∪ S1 ∪ S2 = S1 ∪ S2 ∪ S3; rw [Finset.union_assoc, Finset.union_comm S3 (S1 ∪ S2)])
        h1 h2 h3
    · exact apply_perm u3 u2 u1 hxu3 hxu2 hxu1 hu23.symm hu13.symm hu12.symm
        ((Finset.insert_comm u3 u2 {u1}).trans ((congrArg (insert u2) (Finset.pair_comm u3 u1)).trans (Finset.insert_comm u2 u1 {u3})))
        (by change S3 ∪ S2 ∪ S1 = S1 ∪ S2 ∪ S3; rw [Finset.union_comm S3 S2, Finset.union_comm (S2 ∪ S3) S1, ← Finset.union_assoc])
        h1 h2 h3
  · -- Non-adjacent case: ¬ G.Adj y1 y2
    have hy_allS : ∀ y, (y = y1 ∨ y = y2) → G.neighborFinset y ⊆ S1 ∪ S2 ∪ S3 := by
      intro y hy z hz
      have hadj := (G.mem_neighborFinset y z).mp hz
      rcases huniv z with hzU | rfl | rfl
      · exact (Finset.mem_union.mp hzU).resolve_left fun hzB => hy_not_xB y hy z hzB hadj
      · rcases hy with rfl | rfl
        · exact (hadj.ne rfl).elim
        · exact (hy12 hadj.symm).elim
      · rcases hy with rfl | rfl
        · exact (hy12 hadj).elim
        · exact (hadj.ne rfl).elim
    have hy_one_each : ∀ y, (y = y1 ∨ y = y2) →
        ((G.neighborFinset y) ∩ S1).card = 1 ∧
        ((G.neighborFinset y) ∩ S2).card = 1 ∧
        ((G.neighborFinset y) ∩ S3).card = 1 := by
      intro y hy
      have hle := hy_Si_le y hy
      have hsub := hy_allS y hy
      have heq : G.neighborFinset y =
          ((G.neighborFinset y) ∩ S1) ∪ ((G.neighborFinset y) ∩ S2) ∪ ((G.neighborFinset y) ∩ S3) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hz
          rcases Finset.mem_union.mp (hsub hz) with h12 | h3
          · rcases Finset.mem_union.mp h12 with h1 | h2
            · exact Or.inl (Or.inl ⟨hz, h1⟩)
            · exact Or.inl (Or.inr ⟨hz, h2⟩)
          · exact Or.inr ⟨hz, h3⟩
        · rintro ((⟨hz, _⟩ | ⟨hz, _⟩) | ⟨hz, _⟩) <;> exact hz
      have hd12 : Disjoint ((G.neighborFinset y) ∩ S1) ((G.neighborFinset y) ∩ S2) :=
        hS_disj12.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd13 : Disjoint ((G.neighborFinset y) ∩ S1) ((G.neighborFinset y) ∩ S3) :=
        hS_disj13.mono Finset.inter_subset_right Finset.inter_subset_right
      have hd23 : Disjoint ((G.neighborFinset y) ∩ S2) ((G.neighborFinset y) ∩ S3) :=
        hS_disj23.mono Finset.inter_subset_right Finset.inter_subset_right
      have hc := congrArg Finset.card heq
      rw [G.card_neighborFinset_eq_degree, hdeg y,
        Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12] at hc
      omega
    obtain ⟨c11, c12, c13⟩ := hy_one_each y1 (Or.inl rfl)
    obtain ⟨c21, c22, c23⟩ := hy_one_each y2 (Or.inr rfl)
    obtain ⟨a1, ha1_eq⟩ := Finset.card_eq_one.mp c11
    obtain ⟨a2, ha2_eq⟩ := Finset.card_eq_one.mp c12
    obtain ⟨a3, ha3_eq⟩ := Finset.card_eq_one.mp c13
    obtain ⟨b1, hb1_eq⟩ := Finset.card_eq_one.mp c21
    obtain ⟨b2, hb2_eq⟩ := Finset.card_eq_one.mp c22
    obtain ⟨b3, hb3_eq⟩ := Finset.card_eq_one.mp c23
    have ha1_m : a1 ∈ (G.neighborFinset y1) ∩ S1 := by rw [ha1_eq]; simp
    have ha2_m : a2 ∈ (G.neighborFinset y1) ∩ S2 := by rw [ha2_eq]; simp
    have ha3_m : a3 ∈ (G.neighborFinset y1) ∩ S3 := by rw [ha3_eq]; simp
    have hb1_m : b1 ∈ (G.neighborFinset y2) ∩ S1 := by rw [hb1_eq]; simp
    have hb2_m : b2 ∈ (G.neighborFinset y2) ∩ S2 := by rw [hb2_eq]; simp
    have hb3_m : b3 ∈ (G.neighborFinset y2) ∩ S3 := by rw [hb3_eq]; simp
    have hnot_two_eq : (a1 ≠ b1 ∧ a2 ≠ b2) ∨ (a1 ≠ b1 ∧ a3 ≠ b3) ∨ (a2 ≠ b2 ∧ a3 ≠ b3) := by
      by_contra hbad
      push Not at hbad
      by_cases h1 : a1 = b1
      · by_cases h2 : a2 = b2
        · have hne12 : a1 ≠ a2 := fun h => Finset.disjoint_left.mp hS_disj12 (Finset.mem_inter.mp ha1_m).2 (h ▸ (Finset.mem_inter.mp ha2_m).2)
          have eq := common_unique pair hy12_ne
            ((G.mem_neighborFinset y1 a1).mp (Finset.mem_inter.mp ha1_m).1)
            (h1 ▸ (G.mem_neighborFinset y2 b1).mp (Finset.mem_inter.mp hb1_m).1)
            ((G.mem_neighborFinset y1 a2).mp (Finset.mem_inter.mp ha2_m).1)
            (h2 ▸ (G.mem_neighborFinset y2 b2).mp (Finset.mem_inter.mp hb2_m).1)
          exact hne12 eq
        · have h3 : a3 = b3 := hbad.2.2 h2
          have hne13 : a1 ≠ a3 := fun h => Finset.disjoint_left.mp hS_disj13 (Finset.mem_inter.mp ha1_m).2 (h ▸ (Finset.mem_inter.mp ha3_m).2)
          have eq := common_unique pair hy12_ne
            ((G.mem_neighborFinset y1 a1).mp (Finset.mem_inter.mp ha1_m).1)
            (h1 ▸ (G.mem_neighborFinset y2 b1).mp (Finset.mem_inter.mp hb1_m).1)
            ((G.mem_neighborFinset y1 a3).mp (Finset.mem_inter.mp ha3_m).1)
            (h3 ▸ (G.mem_neighborFinset y2 b3).mp (Finset.mem_inter.mp hb3_m).1)
          exact hne13 eq
      · have h2 : a2 = b2 := hbad.1 h1
        have h3 : a3 = b3 := hbad.2.1 h1
        have hne23 : a2 ≠ a3 := fun h => Finset.disjoint_left.mp hS_disj23 (Finset.mem_inter.mp ha2_m).2 (h ▸ (Finset.mem_inter.mp ha3_m).2)
        have eq := common_unique pair hy12_ne
          ((G.mem_neighborFinset y1 a2).mp (Finset.mem_inter.mp ha2_m).1)
          (h2 ▸ (G.mem_neighborFinset y2 b2).mp (Finset.mem_inter.mp hb2_m).1)
          ((G.mem_neighborFinset y1 a3).mp (Finset.mem_inter.mp ha3_m).1)
          (h3 ▸ (G.mem_neighborFinset y2 b3).mp (Finset.mem_inter.mp hb3_m).1)
        exact hne23 eq
    have make8 : ∀ vi vj ai bi aj bj : Fin 12,
        vi ∈ ({u1, u2, u3} : Finset (Fin 12)) → vj ∈ ({u1, u2, u3} : Finset (Fin 12)) → vi ≠ vj →
        ai ∈ (G.neighborFinset vi).erase x → bi ∈ (G.neighborFinset vi).erase x → ai ≠ bi →
        aj ∈ (G.neighborFinset vj).erase x → bj ∈ (G.neighborFinset vj).erase x → aj ≠ bj →
        ai ∈ S1 ∪ S2 ∪ S3 → bi ∈ S1 ∪ S2 ∪ S3 → aj ∈ S1 ∪ S2 ∪ S3 → bj ∈ S1 ∪ S2 ∪ S3 →
        Disjoint ((G.neighborFinset vi).erase x) ((G.neighborFinset vj).erase x) →
        G.Adj y1 ai → G.Adj y1 aj → G.Adj y2 bi → G.Adj y2 bj →
        cycleGraph 8 ⊑ G := by
      intro vi vj ai bi aj bj hvi hvj hvivj hai hbi haibi haj hbj hajbj haiS hbiS hajS hbjS hdisj hy1ai hy1aj hy2bi hy2bj
      apply copy_eight G vi ai y1 aj vj bj y2 bi
        ((G.mem_neighborFinset vi ai).mp (Finset.mem_erase.mp hai).2)
        hy1ai.symm hy1aj
        ((G.mem_neighborFinset vj aj).mp (Finset.mem_erase.mp haj).2).symm
        ((G.mem_neighborFinset vj bj).mp (Finset.mem_erase.mp hbj).2)
        hy2bj.symm hy2bi
        ((G.mem_neighborFinset vi bi).mp (Finset.mem_erase.mp hbi).2).symm
      have hviU : vi ∈ B' := Finset.mem_insert_of_mem hvi
      have hvjU : vj ∈ B' := Finset.mem_insert_of_mem hvj
      have ne_BS : ∀ u ∈ B', ∀ s ∈ S1 ∪ S2 ∪ S3, u ≠ s := fun u hu s hs h =>
        Finset.disjoint_left.mp hdisj_B_S hu (h ▸ hs)
      have ne_ij : ∀ a ∈ (G.neighborFinset vi).erase x, ∀ b ∈ (G.neighborFinset vj).erase x, a ≠ b :=
        fun a ha b hb h => Finset.disjoint_left.mp hdisj ha (h ▸ hb)
      have ne_y1B : ∀ u ∈ B', y1 ≠ u := fun u hu h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inl hu))
      have ne_y2B : ∀ u ∈ B', y2 ≠ u := fun u hu h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inl hu))
      have ne_y1S : ∀ s ∈ S1 ∪ S2 ∪ S3, y1 ≠ s := fun s hs h => hy1_not (h ▸ Finset.mem_union.mpr (Or.inr hs))
      have ne_y2S : ∀ s ∈ S1 ∪ S2 ∪ S3, y2 ≠ s := fun s hs h => hy2_not (h ▸ Finset.mem_union.mpr (Or.inr hs))
      exact nodup_eight
        (ne_BS vi hviU ai haiS) (ne_y1B vi hviU).symm (ne_BS vi hviU aj hajS) hvivj
        (ne_BS vi hviU bj hbjS) (ne_y2B vi hviU).symm (ne_BS vi hviU bi hbiS)
        (ne_y1S ai haiS).symm (ne_ij ai hai aj haj) (ne_BS vj hvjU ai haiS).symm
        (ne_ij ai hai bj hbj) (ne_y2S ai haiS).symm haibi
        (ne_y1S aj hajS) (ne_y1B vj hvjU) (ne_y1S bj hbjS) hy12_ne (ne_y1S bi hbiS)
        (ne_BS vj hvjU aj hajS).symm hajbj (ne_y2S aj hajS).symm (ne_ij bi hbi aj haj).symm
        (ne_BS vj hvjU bj hbjS) (ne_y2B vj hvjU).symm (ne_BS vj hvjU bi hbiS)
        (ne_y2S bj hbjS).symm (ne_ij bi hbi bj hbj).symm
        (ne_y2S bi hbiS)
    rcases hnot_two_eq with ⟨hn1, hn2⟩ | ⟨hn1, hn3⟩ | ⟨hn2, hn3⟩
    · exact make8 u1 u2 a1 b1 a2 b2 (by simp) (by simp) hu12
        (Finset.mem_inter.mp ha1_m).2 (Finset.mem_inter.mp hb1_m).2 hn1
        (Finset.mem_inter.mp ha2_m).2 (Finset.mem_inter.mp hb2_m).2 hn2
        (inS1 a1 (Finset.mem_inter.mp ha1_m).2) (inS1 b1 (Finset.mem_inter.mp hb1_m).2)
        (inS2 a2 (Finset.mem_inter.mp ha2_m).2) (inS2 b2 (Finset.mem_inter.mp hb2_m).2)
        hS_disj12
        ((G.mem_neighborFinset y1 a1).mp (Finset.mem_inter.mp ha1_m).1)
        ((G.mem_neighborFinset y1 a2).mp (Finset.mem_inter.mp ha2_m).1)
        ((G.mem_neighborFinset y2 b1).mp (Finset.mem_inter.mp hb1_m).1)
        ((G.mem_neighborFinset y2 b2).mp (Finset.mem_inter.mp hb2_m).1)
    · exact make8 u1 u3 a1 b1 a3 b3 (by simp) (by simp) hu13
        (Finset.mem_inter.mp ha1_m).2 (Finset.mem_inter.mp hb1_m).2 hn1
        (Finset.mem_inter.mp ha3_m).2 (Finset.mem_inter.mp hb3_m).2 hn3
        (inS1 a1 (Finset.mem_inter.mp ha1_m).2) (inS1 b1 (Finset.mem_inter.mp hb1_m).2)
        (inS3 a3 (Finset.mem_inter.mp ha3_m).2) (inS3 b3 (Finset.mem_inter.mp hb3_m).2)
        hS_disj13
        ((G.mem_neighborFinset y1 a1).mp (Finset.mem_inter.mp ha1_m).1)
        ((G.mem_neighborFinset y1 a3).mp (Finset.mem_inter.mp ha3_m).1)
        ((G.mem_neighborFinset y2 b1).mp (Finset.mem_inter.mp hb1_m).1)
        ((G.mem_neighborFinset y2 b3).mp (Finset.mem_inter.mp hb3_m).1)
    · exact make8 u2 u3 a2 b2 a3 b3 (by simp) (by simp) hu23
        (Finset.mem_inter.mp ha2_m).2 (Finset.mem_inter.mp hb2_m).2 hn2
        (Finset.mem_inter.mp ha3_m).2 (Finset.mem_inter.mp hb3_m).2 hn3
        (inS2 a2 (Finset.mem_inter.mp ha2_m).2) (inS2 b2 (Finset.mem_inter.mp hb2_m).2)
        (inS3 a3 (Finset.mem_inter.mp ha3_m).2) (inS3 b3 (Finset.mem_inter.mp hb3_m).2)
        hS_disj23
        ((G.mem_neighborFinset y1 a2).mp (Finset.mem_inter.mp ha2_m).1)
        ((G.mem_neighborFinset y1 a3).mp (Finset.mem_inter.mp ha3_m).1)
        ((G.mem_neighborFinset y2 b2).mp (Finset.mem_inter.mp hb2_m).1)
        ((G.mem_neighborFinset y2 b3).mp (Finset.mem_inter.mp hb3_m).1)

end Helpers

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R2.H1 := by
  intro hCubic hMixed n G _ hmin hedge hnbr hpair hcut htri hcomp hdvd8
  by_cases hc8 : cycleGraph 8 ⊑ G
  · obtain ⟨v, c, hc, hlen⟩ := (cycleGraph_isContained_iff (by decide : 3 ≤ 8)).mp hc8
    exact ⟨3, v, c, by decide, hc, hlen⟩
  have hconn : G.Connected := connected_of_cut G hmin hcut
  have hecc : ∀ x : Fin n, ∃ y : Fin n, y ≠ x ∧ ¬ G.Adj x y ∧ ∀ b, ¬ (G.Adj x b ∧ G.Adj b y) :=
    no_eccentricity_two G hmin htri hpair hc8
  have hsum : ∀ x : Fin n, 2 + ∑ u ∈ G.neighborFinset x, G.degree u ≤ n :=
    second_neighborhood_bound G hmin htri hpair hecc
  have hdeg_lb : ∀ x : Fin n, 3 * G.degree x + 2 ≤ n := by
    intro x
    have hlow : 3 * G.degree x ≤ ∑ u ∈ G.neighborFinset x, G.degree u := by
      calc 3 * G.degree x = ∑ _u ∈ G.neighborFinset x, 3 := by
            rw [Finset.sum_const, G.card_neighborFinset_eq_degree, smul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ G.neighborFinset x, G.degree u :=
            Finset.sum_le_sum fun u _ => hmin.trans (G.minDegree_le_degree u)
    have hx := hsum x
    omega
  by_cases hcub : ∀ v, G.degree v = 3
  · -- Cubic branch
    have hn_pos : 0 < n := pos_of_minDegree G hmin
    have h11 : 11 ≤ n := by
      have := hdeg_lb ⟨0, hn_pos⟩
      rw [hcub] at this
      omega
    have heven : Even n := by
      have hhs := G.sum_degrees_eq_twice_card_edges
      have h3n : (∑ v : Fin n, G.degree v) = 3 * n := by
        calc (∑ v : Fin n, G.degree v) = ∑ _v : Fin n, 3 := Finset.sum_congr rfl fun v _ => hcub v
          _ = 3 * n := by simp [mul_comm]
      rw [h3n] at hhs
      obtain ⟨k, hk⟩ : Even (3 * n) := ⟨G.edgeFinset.card, by omega⟩
      rcases Nat.even_or_odd n with hn_ev | ⟨m, rfl⟩
      · exact hn_ev
      · omega
    have hne12 : n ≠ 12 := by
      rintro rfl
      exact hc8 (cubic_twelve_has_c8 G hcub htri hpair)
    have h14 : 14 ≤ n := by
      obtain ⟨k, rfl⟩ := heven
      omega
    exact hCubic n G hconn hcub htri hpair hc8 hecc heven h14
  · -- Non-cubic branch
    push Not at hcub
    obtain ⟨v0, hv0_ne⟩ := hcub
    have hv0_ge3 := hmin.trans (G.minDegree_le_degree v0)
    have hv0_ge4 : 4 ≤ G.degree v0 := by omega
    have h14 : 14 ≤ n := by
      have := hdeg_lb v0
      omega
    have h22 : 8 * n = 11 * (univ.filter (fun x => G.degree x = 3)).card → 22 ≤ n := by
      intro heq
      have hdvd : 11 ∣ 8 * n := ⟨(univ.filter (fun x => G.degree x = 3)).card, heq⟩
      have hdvd_n : 11 ∣ n := (by decide : Nat.Coprime 11 8).dvd_of_dvd_mul_left hdvd
      obtain ⟨m, rfl⟩ := hdvd_n
      omega
    exact hMixed n G hconn hmin ⟨v0, hv0_ge4⟩ hedge hnbr htri hpair hc8 hecc hsum hcut hcomp
      hdvd8 h22 h14

end OMA.R_Erdos64_erdos_64_R2_H1_R1
