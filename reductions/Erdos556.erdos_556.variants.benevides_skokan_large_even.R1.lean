import FormalConjectures.ErdosProblems.«556»
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.Pigeonhole

/-! A four-block lower bound and cycle-embedding lemmas for large even cycles. -/

open SimpleGraph Filter

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1

-- Below 2n vertices, use three exceptional vertices and four equal blocks.
-- The two low bits distinguish the four blocks. After removing the exceptional
-- vertex of a colour, ordinary edges of that colour stay in pairs of blocks.
def H1 : Prop :=
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if (x / 2) % 2 = (y / 2) % 2 then 1 else 2
  ∀ n : ℕ, 4 ≤ n → Even n → ∀ f : Fin n → ℕ, Function.Injective f →
    (∀ u, f u < 2 * n - 1) → ∀ i : Fin 3,
      ∃ u v, (cycleGraph n).Adj u v ∧ colour (f u) (f v) ≠ i

-- The forcing direction is a statement about a single host size for each n.
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, Even n →
    ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)),
      (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∃ i, (cycleGraph n).IsContained (c i)


-- Deleting a single index from a cyclic order leaves the other indices
-- in path order. Rotate so that the omitted index is immediately before it.
lemma lowerColouringAvoidsCycle : H1 := by
  classical
  intro n hn he f hf hsize i
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if x / 2 % 2 = y / 2 % 2 then 1 else 2
  change ∃ u v, (cycleGraph n).Adj u v ∧ colour (f u) (f v) ≠ i
  by_contra! hmono
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  obtain ⟨k, hk⟩ := he
  obtain ⟨a, ha⟩ : ∃ a : Fin (m + 4), ∀ u, f u = i.val → u = a := by
    by_cases hit : ∃ u, f u = i.val
    · obtain ⟨a, ha⟩ := hit
      exact ⟨a, fun _ hu => hf (hu.trans ha.symm)⟩
    · exact ⟨0, fun u hu => (hit ⟨u, hu⟩).elim⟩
  let pos (j : Fin (m + 3)) : Fin (m + 4) := a + j.succ
  have pos_inj : Function.Injective pos := by
    intro u v h
    exact Fin.succ_inj.mp (add_left_cancel (show a + u.succ = a + v.succ from h))
  let g (j : Fin (m + 3)) := f (pos j)
  have avoid (j) : g j ≠ i.val := by
    intro h
    have hpos := ha (pos j) h
    exact Fin.succ_ne_zero j (add_left_cancel
      (show a + j.succ = a + 0 from hpos.trans (add_zero a).symm))
  have edge (j : Fin (m + 2)) : colour (g j.castSucc) (g j.succ) = i := by
    apply hmono
    apply cycleGraph_adj.mpr
    right
    apply sub_eq_iff_eq_add.mpr
    change a + j.succ.succ = 1 + (a + j.castSucc.succ)
    rw [← Fin.coeSucc_eq_succ (a := j.succ), Fin.castSucc_succ]
    ac_rfl
  -- Within one colour, fixing the component leaves two ordinary
  -- residues per group of four. The second coordinate selects one of them.
  let key (c : Fin 3) (x : ℕ) : ℕ :=
    if c = 0 then x % 2 else if c = 1 then x / 2 % 2
    else if x % 2 = x / 2 % 2 then 0 else 1
  let bit (c : Fin 3) (x : ℕ) := if c = 0 then x / 2 % 2 else x % 2
  have pair {x y : ℕ} (hx : x ≠ i.val) (hy : y ≠ i.val)
      (hc : colour x y = i) : 3 ≤ x ∧ 3 ≤ y ∧ key i x = key i y := by
    by_cases hs : min x y < 3
    · have hv := congrArg Fin.val hc
      simp only [colour, if_pos hs, Nat.mod_eq_of_lt hs] at hv
      rw [min_def] at hv
      split at hv <;> contradiction
    · have hx3 : 3 ≤ x := le_trans (Nat.le_of_not_lt hs) (min_le_left _ _)
      have hy3 : 3 ≤ y := le_trans (Nat.le_of_not_lt hs) (min_le_right _ _)
      refine ⟨hx3, hy3, ?_⟩
      by_cases hp : x % 2 = y % 2
      · have hi : (0 : Fin 3) = i := by simpa only [colour, if_neg hs, if_pos hp] using hc
        simpa [← hi, key] using hp
      · by_cases hb : x / 2 % 2 = y / 2 % 2
        · have hi : (1 : Fin 3) = i := by simpa only [colour, if_neg hs, if_neg hp, if_pos hb] using hc
          simpa [← hi, key] using hb
        · have hi : (2 : Fin 3) = i := by simpa only [colour, if_neg hs, if_neg hp, if_neg hb] using hc
          rw [← hi]
          simp only [key, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
          split_ifs <;> omega
  have links (j : Fin (m + 2)) := pair (avoid j.castSucc) (avoid j.succ) (edge j)
  have same (j : Fin (m + 3)) : 3 ≤ g j ∧ key i (g j) = key i (g 0) := by
    induction j using Fin.induction with
    | zero => exact ⟨(links 0).1, rfl⟩
    | succ j ih => exact ⟨(links j).2.1, (links j).2.2.symm.trans ih.2⟩
  let code (j : Fin (m + 3)) : Fin (m + 2) :=
    ⟨2 * ((g j - 3) / 4) + bit i (g j), by
      have := hsize (pos j)
      change g j < 2 * (m + 4) - 1 at this
      have := (same j).1
      dsimp [bit]
      split <;> omega⟩
  have inj : Function.Injective code := by
    intro u v huv
    apply pos_inj
    apply hf
    change g u = g v
    have hc := congrArg Fin.val huv
    change 2 * ((g u - 3) / 4) + bit i (g u) = 2 * ((g v - 3) / 4) + bit i (g v) at hc
    have heq := (same u).2.trans (same v).2.symm
    have hu := (same u).1
    have hv := (same v).1
    have bit_lt (x : ℕ) : bit i x < 2 := by dsimp [bit]; split <;> omega
    have bu := bit_lt (g u)
    have bv := bit_lt (g v)
    have row : (g u - 3) / 4 = (g v - 3) / 4 := by omega
    have lastBit : bit i (g u) = bit i (g v) := by omega
    have digits (x : ℕ) : x % 4 = x % 2 + 2 * (x / 2 % 2) := by
      have hd : x / 2 / 2 = x / 4 := Nat.div_div_eq_div_mul _ _ _
      omega
    have low : g u % 4 = g v % 4 := by
      rw [digits (g u), digits (g v)]
      fin_cases i <;> simp [key, bit] at heq lastBit <;> (try split_ifs at heq) <;> omega
    have xu := Nat.mod_add_div (g u) 4
    have xv := Nat.mod_add_div (g v) 4
    omega
  have impossible := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_fin] at impossible
  omega

-- A sufficient embedding condition for an even cycle in one colour:
-- alternate two disjoint sets of k vertices across a complete bipartite pair.
lemma cycle_of_complete_pair {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin k ↪ V) (apart : ∀ a b, left a ≠ right b)
    (cross : ∀ a b, G.Adj (left a) (right b)) :
    (cycleGraph (2 * k)).IsContained G := by
  let half (u : Fin (2 * k)) : Fin k := ⟨u.val / 2, by have := u.isLt; omega⟩
  let place (u : Fin (2 * k)) := if u.val % 2 = 0 then left (half u) else right (half u)
  have opposite {a b : Fin (2 * k)} (h : (a - b).val = 1) : a.val % 2 ≠ b.val % 2 := by
    by_cases hle : b ≤ a
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      have := b.isLt
      omega
  refine ⟨⟨⟨place, ?_⟩, ?_⟩⟩
  · intro a b hab
    have hop : a.val % 2 ≠ b.val % 2 := by
      rcases cycleGraph_adj'.mp hab with h | h
      · exact opposite h
      · exact Ne.symm (opposite h)
    dsimp only [place]
    split_ifs <;> first | exact cross _ _ | exact (cross _ _).symm | exfalso; omega
  · intro a b h
    change place a = place b at h
    dsimp only [place] at h
    split_ifs at h
    · have hh := congrArg Fin.val (left.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · have hh := congrArg Fin.val (right.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)

-- The right vertices are candidates for the gaps between successive left
-- vertices. Half-degree on both sides of this auxiliary graph gives Hall.
lemma matching_of_half_degrees {k : ℕ} (cand : Fin k → Finset (Fin k))
    (rows : ∀ j, k ≤ 2 * (cand j).card)
    (cols : ∀ v, k ≤ 2 * (Finset.univ.filter (fun j => v ∈ cand j)).card) :
    ∃ pick : Fin k → Fin k, Function.Injective pick ∧ ∀ j, pick j ∈ cand j := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' cand).mp
  intro s
  by_cases small : 2 * s.card ≤ k
  · by_cases hs : s.Nonempty
    · obtain ⟨j, hj⟩ := hs
      have hsub : cand j ⊆ s.biUnion cand :=
        fun v hv => Finset.mem_biUnion.mpr ⟨j, hj, hv⟩
      have := Finset.card_le_card hsub
      have := rows j
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  · have hall : s.biUnion cand = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_contra hv
      have hsub : Finset.univ.filter (fun j => v ∈ cand j) ⊆ sᶜ := by
        intro j hj
        apply Finset.mem_compl.mpr
        intro hjs
        exact hv (Finset.mem_biUnion.mpr ⟨j, hjs, (Finset.mem_filter.mp hj).2⟩)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin] at hcard
      have := cols v
      have hsk : s.card ≤ k := by simpa using Finset.card_le_univ s
      omega
    rw [hall]
    exact Finset.card_le_univ s

-- A candidate for an odd cycle position must join each of its two even
-- neighbours. The relation allows unrelated cross-edges to be absent.
lemma cycle_from_gap_matching {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin k ↪ V) (apart : ∀ a b, left a ≠ right b)
    (pick : Fin k → Fin k) (hinj : Function.Injective pick)
    (fits : ∀ (a b : Fin (2 * k)) (u v : Fin k),
      a.val % 2 = 0 → b.val % 2 ≠ 0 → (cycleGraph (2 * k)).Adj a b →
      u.val = a.val / 2 → v.val = b.val / 2 → G.Adj (left u) (right (pick v))) :
    (cycleGraph (2 * k)).IsContained G := by
  let half (u : Fin (2 * k)) : Fin k := ⟨u.val / 2, by have := u.isLt; omega⟩
  let place (u : Fin (2 * k)) :=
    if u.val % 2 = 0 then left (half u) else right (pick (half u))
  have flip {a b : Fin (2 * k)} (h : (a - b).val = 1) : a.val % 2 ≠ b.val % 2 := by
    by_cases hle : b ≤ a
    · rw [Fin.sub_val_of_le hle] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      have := b.isLt
      omega
  refine ⟨⟨⟨place, ?_⟩, ?_⟩⟩
  · intro a b hab
    have hop : a.val % 2 ≠ b.val % 2 :=
      (cycleGraph_adj'.mp hab).elim flip (fun h => Ne.symm (flip h))
    dsimp only [place]
    by_cases ha : a.val % 2 = 0
    · have hb : b.val % 2 ≠ 0 := by omega
      rw [if_pos ha, if_neg hb]
      exact fits a b (half a) (half b) ha hb hab rfl rfl
    · have hb : b.val % 2 = 0 := by omega
      rw [if_neg ha, if_pos hb]
      exact (fits b a (half b) (half a) hb ha hab.symm rfl rfl).symm
  · intro a b h
    change place a = place b at h
    dsimp only [place] at h
    split_ifs at h
    · have hh := congrArg Fin.val (left.injective h)
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)
    · exact (apart _ _ h).elim
    · exact (apart _ _ h.symm).elim
    · have hh := congrArg Fin.val (hinj (right.injective h))
      change a.val / 2 = b.val / 2 at hh
      exact Fin.ext (by omega)

-- Consecutive rows with at least three quarters of the opposite vertices
-- in each neighbourhood have at least half in common. Applying the same
-- count to each column verifies the other side of Hall's condition.
lemma consecutive_common_representatives {k : ℕ} (next : Equiv.Perm (Fin k))
    (nb : Fin k → Finset (Fin k))
    (rows : ∀ j, 3 * k ≤ 4 * (nb j).card)
    (cols : ∀ v, 3 * k ≤ 4 * (Finset.univ.filter (fun j => v ∈ nb j)).card) :
    ∃ pick : Fin k → Fin k, Function.Injective pick ∧
      ∀ j, pick j ∈ nb j ∧ pick j ∈ nb (next j) := by
  classical
  have half {s t : Finset (Fin k)} (hs : 3 * k ≤ 4 * s.card) (ht : 3 * k ≤ 4 * t.card) :
      k ≤ 2 * (s ∩ t).card := by
    have h := Finset.card_union_add_card_inter s t
    have hmax : (s ∪ t).card ≤ k := by simpa using Finset.card_le_univ (s ∪ t)
    omega
  let cand (j : Fin k) := nb j ∩ nb (next j)
  have col (v : Fin k) : k ≤ 2 * (Finset.univ.filter (fun j => v ∈ cand j)).card := by
    let s := Finset.univ.filter (fun j => v ∈ nb j)
    let t := s.map next.symm.toEmbedding
    have ht (j : Fin k) : j ∈ t ↔ v ∈ nb (next j) := by
      change j ∈ s.map next.symm.toEmbedding ↔ _
      constructor
      · intro hj
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hj
        simpa [s] using hx
      · intro hj
        exact Finset.mem_map.mpr ⟨next j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩,
          next.symm_apply_apply j⟩
    have heq : Finset.univ.filter (fun j => v ∈ cand j) = s ∩ t := by
      ext j
      simp [s, cand, ht]
    rw [heq]
    apply half (cols v)
    simpa [t] using cols v
  obtain ⟨p, hp, hmem⟩ := matching_of_half_degrees cand
    (fun j => half (rows j) (rows (next j))) col
  exact ⟨p, hp, fun j => Finset.mem_inter.mp (hmem j)⟩

-- With at most one quarter of the cross-edges missing at each vertex,
-- use distinct common neighbours to close the prescribed cyclic left order.
lemma cycle_of_three_quarter_pair {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (left right : Fin (k + 1) ↪ V) (apart : ∀ a b, left a ≠ right b)
    (nb : Fin (k + 1) → Finset (Fin (k + 1)))
    (sound : ∀ a b, b ∈ nb a → G.Adj (left a) (right b))
    (rows : ∀ j, 3 * (k + 1) ≤ 4 * (nb j).card)
    (cols : ∀ v, 3 * (k + 1) ≤ 4 * (Finset.univ.filter (fun j => v ∈ nb j)).card) :
    (cycleGraph (2 * (k + 1))).IsContained G := by
  let next := Equiv.addRight (1 : Fin (k + 1))
  obtain ⟨pick, hinj, sides⟩ := consecutive_common_representatives next nb rows cols
  apply cycle_from_gap_matching G (k + 1) left right apart pick hinj
  intro a b u v ha hb hab hu hv
  have adjacent : u = v ∨ u = next v := by
    have ha' := a.isLt
    have hb' := b.isLt
    have hv' := v.isLt
    have hn : (next v).val = if v.val = k then 0 else v.val + 1 := by
      change (v + 1).val = _
      rw [Fin.val_add_one]
      simp only [Fin.ext_iff, Fin.val_last]
    simp only [Fin.ext_iff]
    rw [hn]
    rcases cycleGraph_adj'.mp hab with h | h
    · by_cases hle : b ≤ a
      · rw [Fin.sub_val_of_le hle] at h
        split_ifs <;> omega
      · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
        split_ifs <;> omega
    · by_cases hle : a ≤ b
      · rw [Fin.sub_val_of_le hle] at h
        split_ifs <;> omega
      · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
        split_ifs <;> omega
  rcases adjacent with h | h
  · rw [h]; exact sound _ _ (sides v).1
  · rw [h]; exact sound _ _ (sides v).2

-- From a budget of missing cross-edges, choose q rows each with at most
-- t missing edges. This can be applied on the two sides independently.
lemma select_low_defect (q r t : ℕ) (defect : Fin (q + r) → ℕ)
    (budget : ∑ x, defect x < (r + 1) * (t + 1)) :
    ∃ e : Fin q ↪ Fin (q + r), ∀ a, defect (e a) ≤ t := by
  classical
  let bad := Finset.univ.filter fun x => t < defect x
  have total : bad.card * (t + 1) ≤ ∑ x, defect x := by
    calc
      bad.card * (t + 1) = ∑ _x ∈ bad, (t + 1) := by simp
      _ ≤ ∑ x ∈ bad, defect x := Finset.sum_le_sum fun x hx =>
        Nat.succ_le_of_lt (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x, defect x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have few : bad.card ≤ r := by
    by_contra! hr
    have hmul : (r + 1) * (t + 1) ≤ bad.card * (t + 1) := Nat.mul_le_mul_right _ hr
    exact (not_lt_of_ge (hmul.trans total)) budget
  have hc : q ≤ Fintype.card ↥(badᶜ : Finset (Fin (q+r))) := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨f⟩ : Nonempty (Fin q ↪ ↥(badᶜ : Finset (Fin (q+r)))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  refine ⟨⟨fun a => (f a).val, Subtype.val_injective.comp f.injective⟩, ?_⟩
  intro a
  have ha := (f a).property
  simpa [bad] using ha

-- Each missing cross-edge contributes once to the row total and once to
-- the column total. With r spare vertices on either side, discard rows
-- and columns of excessive defect, then apply the three-quarter lemma.
lemma cycle_of_sparse_missing_edges {V : Type*} (G : SimpleGraph V) (k r : ℕ)
    (left right : Fin (k + 1 + r) ↪ V) (apart : ∀ a b, left a ≠ right b)
    (miss : Fin (k + 1 + r) → Finset (Fin (k + 1 + r)))
    (sound : ∀ a b, b ∉ miss a → G.Adj (left a) (right b))
    (budget : ∑ a, (miss a).card < (r + 1) * ((k + 1) / 4 + 1)) :
    (cycleGraph (2 * (k + 1))).IsContained G := by
  classical
  let col (b : Fin (k + 1 + r)) := Finset.univ.filter fun a => b ∈ miss a
  have eqtotal : ∑ b, (col b).card = ∑ a, (miss a).card := by
    calc
      _ = ∑ b, ∑ a : Fin (k + 1 + r), if b ∈ miss a then 1 else 0 := by
        simp [col, Finset.sum_boole]
      _ = ∑ a, ∑ b : Fin (k + 1 + r), if b ∈ miss a then 1 else 0 := Finset.sum_comm
      _ = _ := by simp
  obtain ⟨L, hL⟩ := select_low_defect (k + 1) r ((k + 1) / 4) (fun a => (miss a).card) budget
  obtain ⟨R, hR⟩ := select_low_defect (k + 1) r ((k + 1) / 4) (fun b => (col b).card)
    (by rw [eqtotal]; exact budget)
  let nb (a : Fin (k + 1)) := Finset.univ.filter fun b : Fin (k + 1) => R b ∉ miss (L a)
  apply cycle_of_three_quarter_pair G k (L.trans left) (R.trans right)
    (fun a b => apart (L a) (R b)) nb
  · intro a b hb
    exact sound _ _ (Finset.mem_filter.mp hb).2
  · intro a
    have sub : ((nb a)ᶜ).card ≤ (miss (L a)).card := by
      apply Finset.card_le_card_of_injOn R _ R.injective.injOn
      intro b hb
      simpa [nb] using hb
    rw [Finset.card_compl, Fintype.card_fin] at sub
    have := hL a
    omega
  · intro b
    let neighbours := Finset.univ.filter (fun a => b ∈ nb a)
    have sub : (neighboursᶜ).card ≤ (col (R b)).card := by
      apply Finset.card_le_card_of_injOn L _ L.injective.injOn
      intro a ha
      simpa [col, neighbours, nb] using ha
    rw [Finset.card_compl, Fintype.card_fin] at sub
    have := hR b
    change 3 * (k + 1) ≤ 4 * neighbours.card
    omega

-- An unconditional, coarse host bound. Group the right vertices by
-- their entire colour pattern towards 3q left vertices. Two applications
-- of pigeonhole yield a monochromatic complete q-by-q bipartite graph.
lemma constant_subsequence {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B) (q : ℕ) (hsize : Fintype.card B * q ≤ Fintype.card A) :
    ∃ b : B, ∃ e : Fin q ↪ A, ∀ j, f (e j) = b := by
  classical
  obtain ⟨b, hb⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f hsize
  let s := Finset.univ.filter fun a => f a = b
  obtain ⟨e⟩ : Nonempty (Fin q ↪ ↥s) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, Fintype.card_coe]; exact hb)
  exact ⟨b, ⟨fun j => (e j).val, Subtype.val_injective.comp e.injective⟩,
    fun j => (Finset.mem_filter.mp (e j).property).2⟩

lemma even_cycle_forcing_host (q : ℕ) :
    ∀ c : Fin 3 → SimpleGraph (Fin (3 * q + 3 ^ (3 * q) * q)),
      (⊤ : SimpleGraph _).IsEdgeColouring c → ∃ i, (cycleGraph (2 * q)).IsContained (c i) := by
  classical
  let l := 3 * q
  let r := 3 ^ l * q
  intro c hc
  let L : Fin l ↪ Fin (l + r) :=
    ⟨fun a => ⟨a.val, by have := a.isLt; omega⟩,
      fun a b h => Fin.ext (congrArg (fun z : Fin (l + r) => z.val) h)⟩
  let R : Fin r ↪ Fin (l + r) :=
    ⟨fun b => ⟨l + b.val, by have := b.isLt; omega⟩, by
      intro a b h
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val h)⟩
  have apart (a : Fin l) (b : Fin r) : L a ≠ R b := by
    intro h
    have heq := congrArg Fin.val h
    change a.val = l + b.val at heq
    have := a.isLt
    omega
  have covered (b : Fin r) (a : Fin l) : ∃ i, (c i).Adj (L a) (R b) := by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj _ _).mpr (apart _ _)
  let pattern (b : Fin r) (a : Fin l) : Fin 3 := (covered b a).choose
  obtain ⟨word, cols, hcols⟩ := constant_subsequence pattern q
    (by simp [r])
  obtain ⟨i, rows, hrows⟩ := constant_subsequence word q (by simp [l])
  refine ⟨i, cycle_of_complete_pair (c i) q (rows.trans L) (cols.trans R)
    (fun a b => apart _ _) ?_⟩
  intro a b
  have he := (covered (cols b) (rows a)).choose_spec
  change (c (pattern (cols b) (rows a))).Adj (L (rows a)) (R (cols b)) at he
  rw [hcols b, hrows a] at he
  exact he

lemma even_cycle_global_upper (q : ℕ) :
    multicolourRamsey (cycleGraph (2 * q)) 3 ≤ 3 * q + 3 ^ (3 * q) * q := by
  apply Nat.sInf_le
  exact even_cycle_forcing_host q

lemma even_cycle_lower_bound (n : ℕ) (hfour : 4 ≤ n) (heven : Even n) :
    2 * n ≤ multicolourRamsey (cycleGraph n) 3 := by
  classical
  have hbad := lowerColouringAvoidsCycle
  let S : Set ℕ := {N | ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c → ∃ i, (cycleGraph n).IsContained (c i)}
  change 2 * n ≤ sInf S
  have hne : S.Nonempty := by
    obtain ⟨q, hq⟩ := heven
    have h : n = 2 * q := by omega
    refine ⟨3 * q + 3 ^ (3 * q) * q, ?_⟩
    dsimp only [S, Set.mem_setOf_eq]
    rw [h]
    exact even_cycle_forcing_host q
  refine le_csInf hne ?_
  intro N hN
  by_contra! hsmall
  let colour (x y : ℕ) : Fin 3 :=
    if min x y < 3 then ⟨min x y % 3, Nat.mod_lt _ (by decide)⟩
    else if x % 2 = y % 2 then 0
    else if (x / 2) % 2 = (y / 2) % 2 then 1 else 2
  have sym (x y : ℕ) : colour x y = colour y x := by
    unfold colour
    rw [min_comm y x]
    by_cases hp : x % 2 = y % 2
    · simp only [if_pos hp, if_pos hp.symm]
    · by_cases hb : x / 2 % 2 = y / 2 % 2
      · simp only [if_neg hp, if_neg (Ne.symm hp), if_pos hb, if_pos hb.symm]
      · simp only [if_neg hp, if_neg (Ne.symm hp), if_neg hb, if_neg (Ne.symm hb)]
  let c (i : Fin 3) : SimpleGraph (Fin N) :=
    { Adj := fun x y => x ≠ y ∧ colour x.val y.val = i
      symm := ⟨fun x y h => ⟨h.1.symm, (sym x.val y.val).symm.trans h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c := by
    constructor
    · ext x y
      rw [top_adj, iSup_adj]
      exact ⟨fun h => ⟨colour x.val y.val, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩
    · intro i j hij
      apply disjoint_iff_inf_le.mpr
      intro x y h
      exact (hij (h.1.2.symm.trans h.2.2)).elim
  obtain ⟨i, ⟨copy⟩⟩ := hN c hc
  obtain ⟨u, v, huv, hdiff⟩ := hbad n hfour heven (fun u => (copy u).val)
    (Fin.val_injective.comp copy.injective) (fun u => by have := (copy u).isLt; omega) i
  exact hdiff (copy.toHom.map_adj huv).2

section RegularPairs

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {S T : Finset V} {ε : ℚ}

/-- In any two sufficiently large subclusters of a regular pair, one can choose
a vertex in the first with the expected number of neighbours in the second. -/
lemma regular_pair_choose {A B : Finset V} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hA : A ⊆ S) (hB : B ⊆ T)
    (hsizeA : (S.card : ℚ) * ε ≤ A.card) (hsizeB : (T.card : ℚ) * ε ≤ B.card) :
    ∃ a ∈ A, (G.edgeDensity S T - ε) * B.card < ((B.filter (G.Adj a)).card : ℚ) := by
  classical
  by_contra! hall
  have hu : -ε < G.edgeDensity A B - G.edgeDensity S T := by
    simpa using (abs_lt.mp (hreg hA hB hsizeA hsizeB)).1
  have hsum : ((G.interedges A B).card : ℚ) ≤
      (A.card : ℚ) * ((G.edgeDensity S T - ε) * B.card) := by
    calc
      ((G.interedges A B).card : ℚ) ≤ ∑ a ∈ A, ((B.filter (G.Adj a)).card : ℚ) := by
        change ((Rel.interedges G.Adj A B).card : ℚ) ≤ _
        rw [Rel.interedges_eq_biUnion]
        exact_mod_cast (show _ ≤ ∑ a ∈ A, (B.filter (G.Adj a)).card from
          (card_biUnion_le).trans_eq (by simp))
      _ ≤ _ := by simpa using (sum_le_sum hall)
  have hden : G.edgeDensity A B ≤ G.edgeDensity S T - ε := by
    rw [edgeDensity_def]
    apply div_le_of_le_mul₀ (by positivity) (sub_nonneg.mpr hd)
    linarith only [hsum, show (A.card : ℚ) * ((G.edgeDensity S T - ε) * B.card) =
        (G.edgeDensity S T - ε) * (A.card * B.card) by ring]
  linarith

/-- A regular pair joins any two eligible subclusters by an edge. -/
lemma regular_pair_edge {A B : Finset V} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hA : A ⊆ S) (hB : B ⊆ T)
    (hsizeA : (S.card : ℚ) * ε ≤ A.card) (hsizeB : (T.card : ℚ) * ε ≤ B.card) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  obtain ⟨a, ha, h⟩ := regular_pair_choose G hreg hd hA hB hsizeA hsizeB
  have hpos : (0 : ℚ) < (B.filter (G.Adj a)).card :=
    lt_of_le_of_lt (mul_nonneg (sub_nonneg.mpr hd) (Nat.cast_nonneg _)) h
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (B.filter (G.Adj a)).card by exact_mod_cast hpos)
  exact ⟨a, ha, b, (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩

end RegularPairs

section RegularPaths

open Finset

/-- Grow a path two vertices at a time in a regular pair, leaving a set of
neighbours of the far endpoint untouched for the closing edge. The internal
vertices stay in the supplied pools, so vertices of an existing embedding
can be excluded in advance. -/
lemma regular_pair_odd_path {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    {R : Finset V} {y : V} (hR : R ⊆ S) (hrsize : k ≤ R.card) (hy : y ∈ T)
    (hRy : ∀ z ∈ R, G.Adj z y)
    (r : ℕ) (A B : Finset V) (x : V) (ha : A ⊆ S) (hb : B ⊆ T)
    (har : Disjoint A R) (hx : x ∈ S) (hxa : x ∉ A) (hxr : x ∉ R) (hyb : y ∉ B)
    (hA : m + r ≤ A.card) (hB : m + r ≤ B.card)
    (hxB : k ≤ (B.filter (G.Adj x)).card) :
    ∃ l : List V, l.length = 2 * r + 2 ∧
      (x :: (l ++ [y])).Nodup ∧ (x :: (l ++ [y])).IsChain G.Adj ∧
      ∀ z ∈ l, z ∈ A ∨ z ∈ B ∨ z ∈ R := by
  classical
  have separate : ∀ {u v}, u ∈ S → v ∈ T → u ≠ v := by
    rintro u v hu hv rfl
    exact Finset.disjoint_left.mp hst hu hv
  induction r generalizing A B x with
  | zero =>
    obtain ⟨a, haR, b, hbN, hab⟩ := regular_pair_edge G hreg hd hR
      ((filter_subset _ _).trans hb) (hs.trans (by exact_mod_cast hrsize))
      (ht.trans (by exact_mod_cast hxB))
    obtain ⟨hbin, hxb⟩ := mem_filter.mp hbN
    have hxb' := separate hx (hb hbin)
    have hxy := separate hx hy
    have hab' := separate (hR haR) (hb hbin)
    have hay := separate (hR haR) hy
    have hxa' : x ≠ a := fun e => hxr (e ▸ haR)
    have hby : b ≠ y := fun e => hyb (e ▸ hbin)
    refine ⟨[b, a], by simp, ?_, ?_, ?_⟩
    · simp [hxb', hxa', hxy, hab'.symm, hby, hay]
    · simp [List.isChain_cons_cons, hxb, hab.symm, hRy a haR]
    · intro z hz
      simp at hz
      rcases hz with rfl | rfl <;> tauto
  | succ r ih =>
    have size {U : Finset V} (hu : m ≤ U.card) :
        (k : ℚ) ≤ (G.edgeDensity S T - ε) * U.card :=
      hdegree.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (sub_nonneg.mpr hd))
    have hswap : ε ≤ G.edgeDensity T S := by rwa [G.edgeDensity_comm T S]
    obtain ⟨b, hbN, hbn⟩ := regular_pair_choose G hreg.symm hswap
      ((filter_subset _ _).trans hb) ha (ht.trans (by exact_mod_cast hxB))
      (hs.trans (by exact_mod_cast (show k ≤ A.card by omega)))
    obtain ⟨hbin, hxb⟩ := mem_filter.mp hbN
    rw [G.edgeDensity_comm T S] at hbn
    have hbA : (k : ℚ) ≤ (A.filter (G.Adj b)).card :=
      (size (by omega : m ≤ A.card)).trans hbn.le
    have hBerase : m + r ≤ (B.erase b).card := by rw [card_erase_of_mem hbin]; omega
    obtain ⟨a, haN, han⟩ := regular_pair_choose G hreg hd
      ((filter_subset _ _).trans ha) ((erase_subset _ _).trans hb)
      (hs.trans hbA) (ht.trans (by exact_mod_cast (show k ≤ (B.erase b).card by omega)))
    obtain ⟨hain, hba⟩ := mem_filter.mp haN
    have hax : k ≤ ((B.erase b).filter (G.Adj a)).card := by
      exact_mod_cast (size (by omega : m ≤ (B.erase b).card)).trans han.le
    have hAerase : m + r ≤ (A.erase a).card := by rw [card_erase_of_mem hain]; omega
    have haR := Finset.disjoint_left.mp har hain
    obtain ⟨l, hl, hsimple, hchain, hpool⟩ := ih (A.erase a) (B.erase b) a
      ((erase_subset _ _).trans ha) ((erase_subset _ _).trans hb)
      (har.mono_left (erase_subset _ _)) (ha hain) (notMem_erase _ _) haR
      (fun h => hyb (erase_subset _ _ h)) hAerase hBerase hax
    have hxl : x ∉ l := by
      intro h
      rcases hpool x h with h | h | h
      · exact hxa (erase_subset _ _ h)
      · exact separate hx (hb (erase_subset _ _ h)) rfl
      · exact hxr h
    have hbl : b ∉ l := by
      intro h
      rcases hpool b h with h | h | h
      · exact separate (ha (erase_subset _ _ h)) (hb hbin) rfl
      · exact notMem_erase _ _ h
      · exact separate (hR h) (hb hbin) rfl
    have hxa' : x ≠ a := fun e => hxa (e ▸ hain)
    have hby : b ≠ y := fun e => hyb (e ▸ hbin)
    have hxb' := separate hx (hb hbin)
    have hba' := (separate (ha hain) (hb hbin)).symm
    have hxy := separate hx hy
    refine ⟨b :: a :: l, by simp [hl]; omega, ?_, ?_, ?_⟩
    · change (x :: b :: a :: (l ++ [y])).Nodup
      exact List.nodup_cons.mpr ⟨by simp [hxb', hxa', hxl, hxy],
        List.nodup_cons.mpr ⟨by simp [hba', hbl, hby], hsimple⟩⟩
    · exact List.isChain_cons_cons.mpr ⟨hxb, List.isChain_cons_cons.mpr ⟨hba, hchain⟩⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inl hbin)
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl hain
      rcases hpool z hz with h | h | h
      · exact Or.inl (erase_subset _ _ h)
      · exact Or.inr (Or.inl (erase_subset _ _ h))
      · exact Or.inr (Or.inr h)

end RegularPaths

/-- Close an embedded simple path with an edge between its endpoints. -/
lemma cycle_of_closed_chain {V : Type*} (G : SimpleGraph V) {x y : V} {l : List V}
    (hlen : 0 < l.length) (hpath : (x :: (l ++ [y])).Nodup)
    (hchain : (x :: (l ++ [y])).IsChain G.Adj) (hclose : G.Adj y x) :
    (cycleGraph (l.length + 2)).IsContained G := by
  let L := (x :: l) ++ [y]
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn hchain
  have hlast : L.getLast hn = y := by simp [L]
  have hedge : G.Adj (L.getLast hn) (L.head hn) := hlast ▸ hclose
  have hp : p.IsPath := Walk.IsPath.mk' ((Walk.support_ofSupport hn hchain).symm ▸ (show L.Nodup from hpath))
  have hlen' : p.length = l.length + 1 := by
    calc
      p.length = L.length - 1 := Walk.length_ofSupport hn hchain
      _ = _ := by simp [L]
  apply (cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, Walk.cons hedge p, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa using hp
  · rw [Walk.length_cons, hlen']; omega
  · rw [Walk.length_cons, hlen']


/-- The endpoint form of the regular-pair path lemma. Either endpoint may be
prescribed, even when the endpoints have no edge between them. -/
lemma regular_pair_path_between {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m r : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    (hA : m + r + k + 1 ≤ S.card) (hB : m + r + 1 ≤ T.card)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (hxdeg : k < (T.filter (G.Adj x)).card) (hycard : k < (S.filter (G.Adj y)).card) :
    ∃ l : List V, l.length = 2 * r + 2 ∧ (x :: (l ++ [y])).Nodup ∧
      (x :: (l ++ [y])).IsChain G.Adj ∧ ∀ z ∈ l, z ∈ S ∨ z ∈ T := by
  classical
  have herase : k ≤ ((S.filter (G.Adj y)).erase x).card := by
    exact (show k ≤ (S.filter (G.Adj y)).card - 1 by omega).trans Finset.pred_card_le_card_erase
  obtain ⟨R, hR, hRcard⟩ := Finset.exists_subset_card_eq herase
  have hRS : R ⊆ S := hR.trans ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
  have hxR : x ∉ R := fun h => Finset.notMem_erase _ _ (hR h)
  have hRy : ∀ z ∈ R, G.Adj z y := fun z hz =>
    (Finset.mem_filter.mp (Finset.erase_subset _ _ (hR hz))).2.symm
  let A := (S.erase x) \ R
  let B := T.erase y
  have hAsub : A ⊆ S.erase x := Finset.sdiff_subset
  have hAsize : m + r ≤ A.card := by
    have h := Finset.le_card_sdiff R (S.erase x)
    rw [Finset.card_erase_of_mem hx, hRcard] at h
    change m + r ≤ ((S.erase x) \ R).card
    omega
  have hBsize : m + r ≤ B.card := by
    dsimp [B]; rw [Finset.card_erase_of_mem hy]; omega
  have hNB : k ≤ (B.filter (G.Adj x)).card := by
    have heq : B.filter (G.Adj x) = (T.filter (G.Adj x)).erase y := by
      ext z; simp [B, and_assoc]
    rw [heq]
    exact (show k ≤ (T.filter (G.Adj x)).card - 1 by omega).trans Finset.pred_card_le_card_erase
  obtain ⟨l, hl, hsimple, hchain, hpool⟩ := regular_pair_odd_path G hreg hd hst k m hs ht hkm hdegree
    hRS hRcard.ge hy hRy r A B x (hAsub.trans (Finset.erase_subset _ _)) (Finset.erase_subset _ _)
    (Finset.disjoint_left.mpr (fun _ ha hr => (Finset.mem_sdiff.mp ha).2 hr))
    hx (fun h => Finset.notMem_erase _ _ (hAsub h)) hxR (Finset.notMem_erase _ _) hAsize hBsize hNB
  refine ⟨l, hl, hsimple, hchain, ?_⟩
  intro z hz
  rcases hpool z hz with h | h | h
  · exact Or.inl (Finset.erase_subset _ _ (hAsub h))
  · exact Or.inr (Finset.erase_subset _ _ h)
  · exact Or.inl (hRS h)

/-- A single regular dense pair contains every even cycle length allowed by
the unused-vertex budget. Both endpoints and the reserved neighbourhood are
chosen inside the pair. -/
lemma cycle_of_regular_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε : ℚ}
    (hreg : G.IsUniform ε S T) (hd : ε ≤ G.edgeDensity S T) (hst : Disjoint S T)
    (k m r : ℕ) (hs : (S.card : ℚ) * ε ≤ k) (ht : (T.card : ℚ) * ε ≤ k)
    (hkm : k ≤ m) (hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m)
    (hA : m + r + k + 1 ≤ S.card) (hB : m + r + 1 ≤ T.card) :
    (cycleGraph (2 * r + 4)).IsContained G := by
  classical
  have size {U : Finset V} (hu : m ≤ U.card) :
      (k : ℚ) ≤ (G.edgeDensity S T - ε) * U.card :=
    hdegree.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (sub_nonneg.mpr hd))
  obtain ⟨x, hx, hxN⟩ := regular_pair_choose G hreg hd (Finset.Subset.refl S) (Finset.Subset.refl T)
    (hs.trans (by exact_mod_cast (show k ≤ S.card by omega)))
    (ht.trans (by exact_mod_cast (show k ≤ T.card by omega)))
  have hxdeg : k < (T.filter (G.Adj x)).card := by
    exact_mod_cast (size (by omega : m ≤ T.card)).trans_lt hxN
  have hswap : ε ≤ G.edgeDensity T S := by rwa [G.edgeDensity_comm T S]
  obtain ⟨y, hyN, hydeg⟩ := regular_pair_choose G hreg.symm hswap
    (Finset.filter_subset _ _) (Finset.Subset.refl S) (ht.trans (by exact_mod_cast hxdeg.le))
    (hs.trans (by exact_mod_cast (show k ≤ S.card by omega)))
  rw [G.edgeDensity_comm T S] at hydeg
  obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hyN
  have hycard : k < (S.filter (G.Adj y)).card := by
    exact_mod_cast (size (by omega : m ≤ S.card)).trans_lt hydeg
  obtain ⟨l, hl, hsimple, hchain, _⟩ := regular_pair_path_between G hreg hd hst k m r hs ht hkm hdegree
    hA hB hx hy hxdeg hycard
  rw [← (show l.length + 2 = 2 * r + 4 by omega)]
  exact cycle_of_closed_chain G (by omega : 0 < l.length) hsimple hchain hxy.symm

/-- Quantitative fixed-endpoint path embedding (Benevides, thesis, Lemma 3.3,
in the small-density range used for the reduced graph). The largeness
condition is explicit. Here length counts edges. -/
lemma regular_pair_path_length_range {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} {ε α : ℚ} {n l : ℕ}
    (hS : S.card = n) (hT : T.card = n) (hst : Disjoint S T)
    (hreg : G.IsUniform ε S T) (hd : α / 4 ≤ G.edgeDensity S T)
    (ha : 0 < α) (ha' : α ≤ 1/2) (he : 0 < ε) (he' : ε ≤ α / 100)
    (hlarge : 100 ≤ (n : ℚ) * ε)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T)
    (hxdeg : α * n / 5 ≤ ((T.filter (G.Adj x)).card : ℚ))
    (hydeg : α * n / 5 ≤ ((S.filter (G.Adj y)).card : ℚ))
    (hl : 1 ≤ l) (hrange : (l : ℚ) + 5 * ((n : ℚ) * ε / α) ≤ n) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = 2 * l + 1 ∧
      ∀ z ∈ p.support, z ∈ S ∨ z ∈ T := by
  let t : ℚ := n * ε / α
  let k : ℕ := ⌈(n : ℚ) * ε⌉₊
  let m : ℕ := ⌈43 / 10 * t⌉₊
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (Nat.cast_nonneg _) he.le) ha.le
  have ht : t * α = n * ε := div_mul_cancel₀ _ ha.ne'
  have hhalf : t * α ≤ t / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') ht0]
  have htlarge : 100 ≤ t := by linarith
  have hklo : n * ε ≤ (k : ℚ) := Nat.le_ceil _
  have hkhi : (k : ℚ) < n * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmlo : 43 / 10 * t ≤ (m : ℚ) := Nat.le_ceil _
  have hmhi : (m : ℚ) < 43 / 10 * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkm : k ≤ m := by exact_mod_cast (show (k : ℚ) ≤ m by linarith)
  have hd' : ε ≤ G.edgeDensity S T := by linarith
  have hdegree : (k : ℚ) ≤ (G.edgeDensity S T - ε) * m := by
    have hd0 : 6 / 25 * α ≤ G.edgeDensity S T - ε := by linarith
    have hmul := mul_le_mul hd0 hmlo (show 0 ≤ 43 / 10 * t by positivity)
      (by linarith : 0 ≤ G.edgeDensity S T - ε)
    nlinarith [hmul]
  have hbudget : k + m + l ≤ n := by
    exact_mod_cast (show (k : ℚ) + m + l ≤ n by change (l : ℚ) + 5 * t ≤ n at hrange; linarith)
  have hend : (k : ℚ) < α * n / 5 := by
    nlinarith [mul_le_mul_of_nonneg_left he' (show 0 ≤ (n : ℚ) by positivity)]
  let r := l - 1
  have hrl : r + 1 = l := by dsimp [r]; omega
  obtain ⟨L, hlen, hnodup, hchain, hpool⟩ := regular_pair_path_between G hreg hd' hst k m r
    (hS ▸ hklo) (hT ▸ hklo) hkm hdegree (by omega) (by omega) hx hy
    (by exact_mod_cast hend.trans_le hxdeg) (by exact_mod_cast hend.trans_le hydeg)
  let W := (x :: L) ++ [y]
  have hn : W ≠ [] := by simp [W]
  let w := Walk.ofSupport W hn hchain
  have hw : w.support = W := Walk.support_ofSupport hn hchain
  have hwlen : w.length = W.length - 1 := Walk.length_ofSupport hn hchain
  have hend' : W.getLast hn = y := by simp [W]
  have hstart : W.head hn = x := rfl
  refine ⟨w.copy hstart hend', ?_, ?_, ?_⟩
  · apply Walk.IsPath.mk'
    rw [Walk.support_copy, hw]
    exact hnodup
  · rw [Walk.length_copy, hwlen]
    simp [W, hlen]; omega
  · rw [Walk.support_copy, hw]
    intro z hz
    simp [W] at hz
    rcases hz with rfl | h | rfl
    · exact Or.inl hx
    · exact hpool _ h
    · exact Or.inr hy

/-- Benevides, Proposition 3.2, with an arbitrary eligible target subset.
The forbidden set may therefore be recomputed after vertices have been used. -/
lemma regular_pair_few_bad {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T B : Finset V} {ε : ℚ} (hreg : G.IsUniform ε S T)
    (hd : ε ≤ G.edgeDensity S T) (hB : B ⊆ T) (hsize : (T.card : ℚ) * ε ≤ B.card) :
    ((S.filter fun x => ((B.filter (G.Adj x)).card : ℚ) ≤
      (G.edgeDensity S T - ε) * B.card).card : ℚ) < S.card * ε := by
  by_contra! h
  obtain ⟨a, ha, hdeg⟩ := regular_pair_choose G hreg hd (Finset.filter_subset _ _) hB h hsize
  exact (not_lt_of_ge (Finset.mem_filter.mp ha).2) hdeg

/-- Choose a single attachment vertex typical toward two different clusters
in the same colour. The candidate pool may already exclude used vertices. -/
lemma regular_pair_two_targets {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T U B C X : Finset V} {ε : ℚ}
    (ht : G.IsUniform ε S T) (hu : G.IsUniform ε S U)
    (hdt : ε ≤ G.edgeDensity S T) (hdu : ε ≤ G.edgeDensity S U)
    (hB : B ⊆ T) (hC : C ⊆ U) (hsizeB : (T.card : ℚ) * ε ≤ B.card)
    (hsizeC : (U.card : ℚ) * ε ≤ C.card) (hX : X ⊆ S) (hsizeX : 2 * S.card * ε ≤ X.card) :
    ∃ x ∈ X, (G.edgeDensity S T - ε) * B.card < ((B.filter (G.Adj x)).card : ℚ) ∧
      (G.edgeDensity S U - ε) * C.card < ((C.filter (G.Adj x)).card : ℚ) := by
  classical
  let badT := S.filter fun x => ((B.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S T - ε) * B.card
  let badU := S.filter fun x => ((C.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S U - ε) * C.card
  have ht' : (badT.card : ℚ) < S.card * ε := regular_pair_few_bad G ht hdt hB hsizeB
  have hu' : (badU.card : ℚ) < S.card * ε := regular_pair_few_bad G hu hdu hC hsizeC
  by_contra! hnone
  have hsub : X ⊆ badT ∪ badU := by
    intro x hx
    by_cases h : ((B.filter (G.Adj x)).card : ℚ) ≤ (G.edgeDensity S T - ε) * B.card
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hX hx, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hX hx, hnone x hx (lt_of_not_ge h)⟩)
  have htot : (X.card : ℚ) ≤ badT.card + badU.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

/-- Lift a finite walk through regular pairs to a simple path. The same cluster
may occur several times. Each step deletes its chosen vertex from all future
pools, and the output records the pool used at every position. -/
lemma lift_regular_chain {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (r : ℕ) (C P : ℕ → Finset V) (A : Finset V)
    (hA : A ⊆ C 0) (hstart : k ≤ A.card)
    (hthreshold : ∀ i ≤ r, ((C i).card : ℚ) * ε ≤ k)
    (hpools : ∀ i < r, P i ⊆ C (i+1) ∧ m + r ≤ (P i).card)
    (hpairs : ∀ i < r, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1))) :
    ∃ x ∈ A, ∃ L : List V, L.length = r ∧ (x :: L).Nodup ∧ (x :: L).IsChain G.Adj ∧
      ∀ i (hi : i < L.length), L[i] ∈ P i := by
  classical
  induction r generalizing C P A with
  | zero =>
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (hk.trans_le hstart)
    exact ⟨x, hx, [], rfl, by simp, .singleton _, fun i hi => by simp at hi⟩
  | succ r ih =>
    obtain ⟨hreg, hden⟩ := hpairs 0 (by omega)
    obtain ⟨hsub, hcard⟩ := hpools 0 (by omega)
    obtain ⟨x, hx, hdeg⟩ := regular_pair_choose G hreg (hd.trans hden) hA hsub
      ((hthreshold 0 (by omega)).trans (by exact_mod_cast hstart))
      ((hthreshold 1 (by omega)).trans (by exact_mod_cast (show k ≤ (P 0).card by omega)))
    let A' := (P 0).filter (G.Adj x)
    have hA' : k ≤ A'.card := by
      have low : (k : ℚ) ≤ (G.edgeDensity (C 0) (C 1) - ε) * (P 0).card :=
        hdegree.trans (mul_le_mul (sub_le_sub_right hden ε)
          (by exact_mod_cast (show m ≤ (P 0).card by omega)) (Nat.cast_nonneg _) (by linarith))
      exact_mod_cast low.trans hdeg.le
    let P' (i : ℕ) := (P (i+1)).erase x
    have hpools' (i) (hi : i < r) : P' i ⊆ C (i+1+1) ∧ m + r ≤ (P' i).card := by
      obtain ⟨hsi, hci⟩ := hpools (i+1) (by omega)
      refine ⟨(Finset.erase_subset _ _).trans hsi, ?_⟩
      have h : (P (i+1)).card - 1 ≤ (P' i).card := Finset.pred_card_le_card_erase
      omega
    obtain ⟨y, hy, L, hlen, hs, hc, hpos⟩ := ih (fun i => C (i+1)) P' A'
      ((Finset.filter_subset _ _).trans hsub) hA' (fun i hi => hthreshold _ (by omega)) hpools'
      (fun i hi => hpairs _ (by omega))
    obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
    have hxL : x ∉ L := by
      intro hit
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hit
      have h := hpos i hi
      rw [hix] at h
      exact Finset.notMem_erase _ _ h
    refine ⟨x, hx, y :: L, by simp [hlen], ?_, List.isChain_cons_cons.mpr ⟨hxy,hc⟩, ?_⟩
    · exact List.nodup_cons.mpr ⟨by simp [hxy.ne, hxL], hs⟩
    · intro i hi
      cases i with
      | zero => exact hyP
      | succ j =>
        exact Finset.erase_subset _ _ (hpos j (by simpa using hi))

/-- Close a lifted chain at a vertex reserved outside its pools. The first
and last pools lie in the neighbourhood of that vertex. Intermediate
clusters may repeat along the reduced walk. -/
lemma lift_regular_circuit {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (r : ℕ) (C P : ℕ → Finset V) (A : Finset V)
    (hA : A ⊆ C 0) (hstart : k ≤ A.card)
    (hthreshold : ∀ i ≤ r + 1, ((C i).card : ℚ) * ε ≤ k)
    (hpools : ∀ i < r + 1, P i ⊆ C (i+1) ∧ m + (r+1) ≤ (P i).card)
    (hpairs : ∀ i < r + 1, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1)))
    (a : V) (havoid : ∀ i < r + 1, a ∉ P i)
    (hfirst : ∀ x ∈ A, G.Adj a x) (hlast : ∀ y ∈ P r, G.Adj y a) :
    (cycleGraph (r+3)).IsContained G := by
  obtain ⟨x, hx, L, hlen, hs, hc, hpos⟩ := lift_regular_chain G hd k m hk hkm hdegree (r+1)
    C P A hA hstart hthreshold hpools hpairs
  have hax := hfirst x hx
  have haL : a ∉ L := by
    intro ha
    obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
    have h := hpos i hi
    rw [hia] at h
    exact havoid _ (by omega) h
  have hne : L ≠ [] := by intro e; simp [e] at hlen
  obtain ⟨L', y, heq⟩ : ∃ L' y, L = L' ++ [y] :=
    ⟨L.dropLast, L.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  subst L
  have hlen' : L'.length = r := by simpa using hlen
  have hlastmem := hpos L'.length (by simp)
  have hy : y ∈ P r := by simpa [hlen'] using hlastmem
  have hsimple : (a :: x :: (L' ++ [y])).Nodup :=
    List.nodup_cons.mpr ⟨by simp only [List.mem_cons, not_or]; exact ⟨hax.ne,haL⟩,hs⟩
  have hchain : (a :: x :: (L' ++ [y])).IsChain G.Adj := List.isChain_cons_cons.mpr ⟨hax,hc⟩
  have hcopy := cycle_of_closed_chain (l := x :: L') G (by simp) hsimple hchain (hlast y hy)
  rw [← (show (x :: L').length + 2 = r + 3 by simp; omega)]
  exact hcopy

/-- Every sufficiently well populated closed walk through dense regular
pairs lifts to a cycle of the same length in the original colour. No
distinctness of the cluster visits is required. -/
lemma cycle_of_regular_closed_walk {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℚ} (hd : ε ≤ d) (k m r : ℕ) (hk : 0 < k) (hkm : k ≤ m)
    (hdegree : (k : ℚ) ≤ (d - ε) * m) (C : ℕ → Finset V)
    (hthreshold : ∀ i ≤ r+2, ((C i).card : ℚ) * ε ≤ k)
    (hroot : 2*k ≤ (C 0).card)
    (hsize : ∀ i ≤ r+2, m+r+2 ≤ (C i).card)
    (hattach : ∀ i ≤ r+2, ((m+r+1 : ℕ) : ℚ) ≤ (d-ε) * (C i).card)
    (hpairs : ∀ i < r+2, G.IsUniform ε (C i) (C (i+1)) ∧ d ≤ G.edgeDensity (C i) (C (i+1)))
    (hclose : G.IsUniform ε (C 0) (C (r+2)) ∧ d ≤ G.edgeDensity (C 0) (C (r+2))) :
    (cycleGraph (r+3)).IsContained G := by
  classical
  obtain ⟨hreg, hden⟩ := hpairs 0 (by omega)
  have hth (i) (hi : i ≤ r+2) : ((C i).card : ℚ) * ε ≤ (C i).card :=
    (hthreshold i hi).trans (by exact_mod_cast (show k ≤ (C i).card by have := hsize i hi; omega))
  have h0 : 2 * ((C 0).card : ℚ) * ε ≤ (C 0).card := by
    have h := hthreshold 0 (by omega)
    have h' : (2 : ℚ) * k ≤ (C 0).card := by exact_mod_cast hroot
    linarith
  obtain ⟨a, _, hn1, hn2⟩ := regular_pair_two_targets G hreg hclose.1 (hd.trans hden) (hd.trans hclose.2)
    (Finset.Subset.refl _) (Finset.Subset.refl _) (hth 1 (by omega)) (hth _ le_rfl)
    (Finset.Subset.refl _) h0
  have degree {T : Finset V} (h : d ≤ G.edgeDensity (C 0) T)
      (hlo : ((m+r+1 : ℕ) : ℚ) ≤ (d-ε) * T.card)
      (hn : (G.edgeDensity (C 0) T - ε) * T.card < ((T.filter (G.Adj a)).card : ℚ)) :
      m+r+1 ≤ (T.filter (G.Adj a)).card := by
    exact_mod_cast (hlo.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right h ε) (Nat.cast_nonneg _))).trans hn.le
  have h1 := degree hden (hattach 1 (by omega)) hn1
  have h2 := degree hclose.2 (hattach _ le_rfl) hn2
  let P (i : ℕ) := if i = r then (C (r+2)).filter (G.Adj a) else (C (i+2)).erase a
  apply lift_regular_circuit G hd k m hk hkm hdegree r (fun i => C (i+1)) P
    ((C 1).filter (G.Adj a)) (Finset.filter_subset _ _) (by omega) (fun i hi => hthreshold _ (by omega))
    _ (fun i hi => hpairs _ (by omega)) a
  · intro i hi
    by_cases eq : i = r
    · subst i
      exact ⟨by simpa [P] using (Finset.filter_subset (G.Adj a) (C (r+2))),
        by simpa [P, Nat.add_assoc] using h2⟩
    · have hb := hsize (i+2) (by omega)
      have hc : (C (i+2)).card - 1 ≤ ((C (i+2)).erase a).card := Finset.pred_card_le_card_erase
      simp only [P, if_neg eq]
      exact ⟨Finset.erase_subset _ _, by omega⟩
  · intro i hi
    by_cases eq : i = r <;> simp [P, eq]
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro y hy
    have hy' : y ∈ (C (r+2)).filter (G.Adj a) := by simpa [P] using hy
    exact (Finset.mem_filter.mp hy').2.symm

/-- Concatenate path segments lying in disjoint vertex pools, with one
connecting edge between successive segments. The order is exactly the sum
of the segment orders. -/
lemma join_disjoint_path_segments {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b : ℕ → V) (pool : ℕ → Finset V) (len : ℕ → ℕ) (t : ℕ)
    (hseg : ∀ i ≤ t, ∃ l : List V, l.length = len i ∧
      (a i :: (l ++ [b i])).Nodup ∧ (a i :: (l ++ [b i])).IsChain G.Adj ∧
      ∀ z ∈ a i :: (l ++ [b i]), z ∈ pool i)
    (hlinks : ∀ i < t, G.Adj (b i) (a (i+1)))
    (hdis : ∀ i j, i < j → j ≤ t → Disjoint (pool i) (pool j)) :
    ∃ L : List V, L.length + 2 = ∑ i ∈ Finset.range (t+1), (len i + 2) ∧
      (a 0 :: (L ++ [b t])).Nodup ∧ (a 0 :: (L ++ [b t])).IsChain G.Adj ∧
      ∀ z ∈ a 0 :: (L ++ [b t]), ∃ i ≤ t, z ∈ pool i := by
  induction t with
  | zero =>
    obtain ⟨l, hl, hs, hc, hp⟩ := hseg 0 le_rfl
    exact ⟨l, by simp [hl], hs, hc, fun z hz => ⟨0, le_rfl, hp z hz⟩⟩
  | succ t ih =>
    obtain ⟨l, hl, hs, hc, hp⟩ := ih (fun i hi => hseg i (by omega))
      (fun i hi => hlinks i (by omega)) (fun i j hij hj => hdis i j hij (by omega))
    obtain ⟨l', hl', hs', hc', hp'⟩ := hseg (t+1) le_rfl
    let X := a 0 :: (l ++ [b t])
    let Y := a (t+1) :: (l' ++ [b (t+1)])
    have hsep : X.Disjoint Y := by
      intro z hz hz'
      obtain ⟨i, hi, h⟩ := hp z hz
      exact Finset.disjoint_left.mp (hdis i (t+1) (by omega) le_rfl) h (hp' z hz')
    have hsimple : (X ++ Y).Nodup := List.nodup_append'.mpr ⟨hs,hs',hsep⟩
    have hchain : (X ++ Y).IsChain G.Adj := by
      apply hc.append hc'
      intro u hu v hv
      have hu' : b t = u := by simpa [← List.cons_append] using hu
      have hv' : a (t+1) = v := by simpa using hv
      exact hu' ▸ hv' ▸ hlinks t (by omega)
    let L := l ++ [b t, a (t+1)] ++ l'
    have heq : a 0 :: (L ++ [b (t+1)]) = X ++ Y := by simp [L,X,Y,List.append_assoc]
    refine ⟨L, ?_, heq ▸ hsimple, heq ▸ hchain, ?_⟩
    · rw [Finset.sum_range_succ, ← hl]
      simp [L,hl']; omega
    · rw [heq]
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · obtain ⟨i, hi, h⟩ := hp z h
        exact ⟨i, by omega, h⟩
      · exact ⟨_, le_rfl, hp' z h⟩

/-- Distribute any requested even increment among the matched pairs, up to
their combined capacity. -/
lemma allocate_cycle_length (t : ℕ) (cap : ℕ → ℕ) (q : ℕ)
    (h : q ≤ ∑ i ∈ Finset.range t, cap i) :
    ∃ use : ℕ → ℕ, (∀ i < t, use i ≤ cap i) ∧ ∑ i ∈ Finset.range t, use i = q := by
  induction t generalizing q with
  | zero =>
    simp at h
    exact ⟨fun _ => 0, by simp, by simp [h]⟩
  | succ t ih =>
    rw [Finset.sum_range_succ] at h
    obtain ⟨f, hf, hsum⟩ := ih (q - cap t) (by omega)
    let use (i : ℕ) := if i = t then min q (cap t) else f i
    refine ⟨use, ?_, ?_⟩
    · intro i hi
      by_cases e : i = t
      · simp [use,e]
      · simpa [use,e] using hf i (by omega)
    · have hold : ∑ i ∈ Finset.range t, use i = ∑ i ∈ Finset.range t, f i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [use, (Finset.mem_range.mp hi).ne]
      rw [Finset.sum_range_succ, hold, hsum]
      simp [use]; omega

/-- In a cyclic arrangement of disjoint path segments, independently
extensible segments realize every admissible total order of the correct
parity. Segments of zero capacity serve as fixed connectors. -/
lemma cycle_of_flexible_segments {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (a b : ℕ → V) (pool : ℕ → Finset V) (base cap : ℕ → ℕ)
    (hseg : ∀ i ≤ t, ∀ j ≤ cap i, ∃ l : List V, l.length = base i + 2*j ∧
      (a i :: (l ++ [b i])).Nodup ∧ (a i :: (l ++ [b i])).IsChain G.Adj ∧
      ∀ z ∈ a i :: (l ++ [b i]), z ∈ pool i)
    (hlinks : ∀ i < t, G.Adj (b i) (a (i+1))) (hclose : G.Adj (b t) (a 0))
    (hdis : ∀ i j, i < j → j ≤ t → Disjoint (pool i) (pool j))
    (n q : ℕ) (hn : 3 ≤ n) (hcap : q ≤ ∑ i ∈ Finset.range (t+1), cap i)
    (horder : n = (∑ i ∈ Finset.range (t+1), (base i + 2)) + 2*q) :
    (cycleGraph n).IsContained G := by
  obtain ⟨f,hf,hsum⟩ := allocate_cycle_length (t+1) cap q hcap
  obtain ⟨L,hL,hs,hc,_⟩ := join_disjoint_path_segments G a b pool (fun i => base i + 2*f i) t
    (fun i hi => hseg i hi (f i) (hf i (by omega))) hlinks hdis
  have hlen : L.length + 2 = n := by
    rw [hL, horder, ← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    omega
  rw [← hlen]
  exact cycle_of_closed_chain G (by omega) hs hc hclose

section ReducedColours

open Finset

variable {V : Type*} [DecidableEq V] (c : Fin 3 → SimpleGraph V)
  [∀ i, DecidableRel (c i).Adj] (hc : (⊤ : SimpleGraph V).IsEdgeColouring c)

include hc

/-- The three densities of a cluster pair in a complete edge-colouring sum to one. -/
lemma cluster_colour_densities {S T : Finset V} (hst : Disjoint S T)
    (hs : S.Nonempty) (ht : T.Nonempty) : ∑ i, (c i).edgeDensity S T = 1 := by
  classical
  let E (i : Fin 3) := (c i).interedges S T
  have cover : (univ.biUnion E) = S ×ˢ T := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
      exact mem_product.mpr ⟨(((c i).mem_interedges_iff).mp hi).1, (((c i).mem_interedges_iff).mp hi).2.1⟩
    · intro hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      have hne : p.1 ≠ p.2 := fun h => Finset.disjoint_left.mp hst (h ▸ ha) hb
      have hed : (⨆ i, c i).Adj p.1 p.2 := by rw [← hc.1]; exact (top_adj _ _).mpr hne
      obtain ⟨i, hi⟩ := iSup_adj.mp hed
      exact mem_biUnion.mpr ⟨i, mem_univ _, ((c i).mem_interedges_iff).mpr ⟨ha, hb, hi⟩⟩
  have hcount : ∑ i, (E i).card = S.card * T.card := by
    rw [← card_product, ← cover, card_biUnion]
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hi hj
    exact (disjoint_iff_inf_le.mp (hc.2 i j hij) (show (c i ⊓ c j).Adj p.1 p.2 from
      ⟨(((c i).mem_interedges_iff).mp hi).2.2, (((c j).mem_interedges_iff).mp hj).2.2⟩)).elim
  simp_rw [edgeDensity_def]
  rw [← Finset.sum_div, div_eq_one_iff_eq]
  · exact_mod_cast hcount
  · exact (mul_pos (by exact_mod_cast hs.card_pos) (by exact_mod_cast ht.card_pos)).ne'

/-- Use every sufficiently dense colour of a simultaneously regular pair.
A uniquely labelled pair is almost monochromatic in the original graph. -/
lemma reduced_colour_graphs {I : Type*} (C : I → Finset V)
    (hne : ∀ u, (C u).Nonempty) (hdis : ∀ u v, u ≠ v → Disjoint (C u) (C v))
    (ε δ : ℚ) (hδ : δ ≤ 1/3) :
    ∃ red : Fin 3 → SimpleGraph I,
      (∀ i u v, (red i).Adj u v ↔ u ≠ v ∧
        (∀ j, (c j).IsUniform ε (C u) (C v)) ∧ δ ≤ (c i).edgeDensity (C u) (C v)) ∧
      (∀ u v, u ≠ v → (∀ j, (c j).IsUniform ε (C u) (C v)) → ∃ i, (red i).Adj u v) ∧
      ∀ i u v, (red i).Adj u v → (∀ j, j ≠ i → ¬ (red j).Adj u v) →
        1 - 2 * δ < (c i).edgeDensity (C u) (C v) := by
  classical
  let red (i : Fin 3) : SimpleGraph I :=
    { Adj := fun u v => u ≠ v ∧ (∀ j, (c j).IsUniform ε (C u) (C v)) ∧
          δ ≤ (c i).edgeDensity (C u) (C v)
      symm := ⟨fun u v h => ⟨h.1.symm, fun j => (h.2.1 j).symm,
        ((c i).edgeDensity_comm (C u) (C v)) ▸ h.2.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨red, fun _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro u v huv hreg
    have htotal := cluster_colour_densities c hc (hdis u v huv) (hne u) (hne v)
    rw [Fin.sum_univ_three] at htotal
    by_contra! h
    have small (i : Fin 3) : (c i).edgeDensity (C u) (C v) < δ :=
      lt_of_not_ge fun hi => h i ⟨huv, hreg, hi⟩
    linarith [small 0, small 1, small 2]
  · intro i u v hi honly
    obtain ⟨huv, hreg, _⟩ := hi
    have htotal := cluster_colour_densities c hc (hdis u v huv) (hne u) (hne v)
    rw [Fin.sum_univ_three] at htotal
    have small (j : Fin 3) (hj : j ≠ i) : (c j).edgeDensity (C u) (C v) < δ :=
      lt_of_not_ge fun hd => honly j hj ⟨huv, hreg, hd⟩
    fin_cases i
    · change 1 - 2 * δ < (c 0).edgeDensity (C u) (C v)
      linarith [small 1 (by decide), small 2 (by decide)]
    · change 1 - 2 * δ < (c 1).edgeDensity (C u) (C v)
      linarith [small 0 (by decide), small 2 (by decide)]
    · change 1 - 2 * δ < (c 2).edgeDensity (C u) (C v)
      linarith [small 0 (by decide), small 1 (by decide)]

end ReducedColours

/-- The pairs discarded by simultaneous three-colour regularity occupy at
most three times the one-colour error budget. Pairs are counted in both orders. -/
lemma simultaneously_irregular_count {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (c : Fin 3 → SimpleGraph V)
    [∀ i, DecidableRel (c i).Adj] (ε : ℚ) (h : ∀ i, P.IsUniform (c i) ε) :
    ∃ bad : Finset (Finset V × Finset V),
      (∀ S T, (S,T) ∈ bad ↔ S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T ∧
          ¬ ∀ i, (c i).IsUniform ε S T) ∧
      (bad.card : ℚ) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * (3 * ε) := by
  classical
  let bad := Finset.univ.biUnion (fun i => P.nonUniforms (c i) ε)
  refine ⟨bad, ?_, ?_⟩
  · intro S T
    simp only [bad, Finset.mem_biUnion, Finset.mem_univ, true_and, Finpartition.mk_mem_nonUniforms]
    push Not
    aesop
  · calc
      (bad.card : ℚ) ≤ ∑ i : Fin 3, ((P.nonUniforms (c i) ε).card : ℚ) := by
        exact_mod_cast (Finset.card_biUnion_le : bad.card ≤ ∑ i : Fin 3, (P.nonUniforms (c i) ε).card)
      _ ≤ _ := by
        rw [Fin.sum_univ_three]
        have h' (i : Fin 3) : ((P.nonUniforms (c i) ε).card : ℚ) ≤
            ((P.parts.card * (P.parts.card - 1) : ℕ) : ℚ) * ε := h i
        linarith [h' 0, h' 1, h' 2]

/-- Delete high-defect clusters before the stability argument (the counting
step in Benevides, Lemma 4.4). Within the remaining cluster set every row
has at most k missing ordered pairs. -/
lemma clean_reduced_pairs {I : Type*} [DecidableEq I] (U : Finset I)
    (bad : Finset (I × I)) (hoff : bad ⊆ U.offDiag)
    (b k : ℕ) (hbudget : bad.card < (b + 1) * (k + 1)) :
    ∃ good ⊆ U, U.card ≤ good.card + b ∧
      ∀ x ∈ good, (good.filter fun y => (x,y) ∈ bad).card ≤ k := by
  classical
  let deg (x : I) := (bad.filter (fun p => p.1 = x)).card
  let high := U.filter fun x => k < deg x
  have hsum : bad.card = ∑ x ∈ U, deg x :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun p hp => (Finset.mem_offDiag.mp (hoff hp)).1)
  have hcount : high.card * (k + 1) ≤ bad.card := by
    calc
      _ = ∑ _x ∈ high, (k + 1) := by simp
      _ ≤ ∑ x ∈ high, deg x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ U, deg x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := hsum.symm
  have hfew : high.card ≤ b := by
    by_contra! h
    exact (not_le_of_gt hbudget) ((Nat.mul_le_mul_right (k+1) h).trans hcount)
  let good := U \ high
  have hhigh : high ⊆ U := Finset.filter_subset _ _
  refine ⟨good, Finset.sdiff_subset, ?_, ?_⟩
  · have h : good.card + high.card = U.card := Finset.card_sdiff_add_card_eq_card hhigh
    omega
  · intro x hx
    obtain ⟨hxU, hxH⟩ := Finset.mem_sdiff.mp hx
    have hd : deg x ≤ k := le_of_not_gt (fun h => hxH (Finset.mem_filter.mpr ⟨hxU,h⟩))
    apply le_trans _ hd
    apply Finset.card_le_card_of_injOn (fun y => (x,y))
    · intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).2,rfl⟩
    · intro y _ z _ h
      exact congrArg Prod.snd h

section Stability

open Finset

/-- The common-neighbour step of Benevides's thesis, Lemma 4.5. Every
left vertex is in one component as soon as twice the missing-degree bound
is smaller than the right side. -/
lemma dense_pair_left_reachable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hmiss : ∀ x ∈ A, B.card ≤ (B.filter (G.Adj x)).card + k) (hB : 2 * k < B.card)
    {x z : V} (hx : x ∈ A) (hz : z ∈ A) : G.Reachable x z := by
  let X := B.filter (G.Adj x)
  let Z := B.filter (G.Adj z)
  have hU : X ∪ Z ⊆ B := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_le_card hU
  have hsum := card_union_add_card_inter X Z
  have hx' : B.card ≤ X.card + k := hmiss x hx
  have hz' : B.card ≤ Z.card + k := hmiss z hz
  obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < (X ∩ Z).card)
  obtain ⟨hbX, hbZ⟩ := mem_inter.mp hb
  exact (mem_filter.mp hbX).2.reachable.trans (mem_filter.mp hbZ).2.symm.reachable

/-- The connected matching conclusion of Lemma 4.5. A and B can have
different sizes. The edges indexed by D have distinct endpoints on each
side and every vertex in the pair belongs to their component. -/
lemma dense_pair_connected_matching {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hab : Disjoint A B) (hsize : A.card ≤ B.card) (hA : k < A.card) (hB : 2 * k < B.card)
    (hl : ∀ x ∈ A, B.card ≤ (B.filter (G.Adj x)).card + k)
    (hr : ∀ y ∈ B, A.card ≤ (A.filter (G.Adj y)).card + k) :
    ∃ a ∈ A, (∀ v ∈ A ∪ B, G.Reachable a v) ∧
      ∃ D ⊆ A, D.card = A.card - k ∧ ∃ f : D ↪ V,
        (∀ x, f x ∈ B ∧ G.Adj x.val (f x)) ∧ Disjoint D (univ.image f) := by
  classical
  obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < A.card)
  refine ⟨a, ha, ?_, ?_⟩
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact dense_pair_left_reachable G A B k hl hB ha hv
    · have hd := hr v hv
      obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (A.filter (G.Adj v)).card)
      obtain ⟨huA, hvu⟩ := mem_filter.mp hu
      exact (dense_pair_left_reachable G A B k hl hB ha huA).trans hvu.symm.reachable
  · obtain ⟨D, hD, hcard⟩ := exists_subset_card_eq (Nat.sub_le A.card k)
    let cand (x : D) := B.filter (G.Adj x.val)
    obtain ⟨f, hfinj, hf⟩ : ∃ f : D → V, Function.Injective f ∧ ∀ x, f x ∈ cand x := by
      apply (all_card_le_biUnion_card_iff_existsInjective' cand).mp
      intro s
      by_cases h : s.Nonempty
      · obtain ⟨x, hx⟩ := h
        have hsub : cand x ⊆ s.biUnion cand := fun z hz => mem_biUnion.mpr ⟨x, hx, hz⟩
        have hc := card_le_card hsub
        have hs : s.card ≤ D.card := by simpa using card_le_univ s
        have hv : B.card ≤ (cand x).card + k := hl _ (hD x.property)
        omega
      · simp [not_nonempty_iff_eq_empty.mp h]
    let emb : D ↪ V := ⟨f, hfinj⟩
    refine ⟨D, hD, hcard, emb, fun x => mem_filter.mp (hf x), ?_⟩
    exact hab.mono hD (by
      intro z hz
      obtain ⟨x, _, rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp (hf x)).1)

end Stability

/-- Benevides, Lemma 4.8. If each vertex misses at most k pairs in a
two-coloured graph on U, a monochromatic component covers all but 2k
vertices. The large component can be chosen to contain a prescribed root. -/
lemma two_colour_large_component {V : Type*} [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    [DecidableRel G.Reachable] [DecidableRel H.Reachable]
    (U : Finset V) (k : ℕ) (hm : ∀ x ∈ U,
      (U.filter fun y => y ≠ x ∧ ¬ G.Adj x y ∧ ¬ H.Adj x y).card ≤ k)
    (a : V) (ha : a ∈ U) :
    U.card ≤ (U.filter (G.Reachable a)).card + 2 * k ∨
    U.card ≤ (U.filter (H.Reachable a)).card + k := by
  classical
  let A := U.filter (G.Reachable a)
  let B := U \ A
  have hAU : A ⊆ U := Finset.filter_subset _ _
  have hBU : B ⊆ U := Finset.sdiff_subset
  have haA : a ∈ A := Finset.mem_filter.mpr ⟨ha, Reachable.refl _⟩
  have hAB : Disjoint A B := Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx
  have hcount : B.card + A.card = U.card := Finset.card_sdiff_add_card_eq_card hAU
  by_cases hB : B.card ≤ 2 * k
  · left; change U.card ≤ A.card + 2 * k; omega
  right
  have blue (x) (hx : x ∈ A) : B.card ≤ (B.filter (H.Adj x)).card + k := by
    have hsub : B.filter (fun y => ¬ H.Adj x y) ⊆
        U.filter (fun y => y ≠ x ∧ ¬ G.Adj x y ∧ ¬ H.Adj x y) := by
      intro y hy
      obtain ⟨hyB, hxy⟩ := Finset.mem_filter.mp hy
      have hyU := hBU hyB
      have hyA := (Finset.mem_sdiff.mp hyB).2
      refine Finset.mem_filter.mpr ⟨hyU, (fun e => hyA (e ▸ hx)), ?_, hxy⟩
      intro hg
      exact hyA (Finset.mem_filter.mpr ⟨hyU, (Finset.mem_filter.mp hx).2.trans hg.reachable⟩)
    have small := (Finset.card_le_card hsub).trans (hm x (hAU hx))
    have add := Finset.card_filter_add_card_filter_not (s := B) (H.Adj x)
    omega
  have hleft (x) (hx : x ∈ A) := dense_pair_left_reachable H A B k blue (by omega) haA hx
  let D := B.filter (H.Adj a)
  have hdB : D ⊆ B := Finset.filter_subset _ _
  have sub : A ∪ D ⊆ U.filter (H.Reachable a) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_filter.mpr ⟨hAU h, hleft x h⟩
    · exact Finset.mem_filter.mpr ⟨hBU (hdB h), (Finset.mem_filter.mp h).2.reachable⟩
  have hc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint (hAB.mono_right hdB)] at hc
  have hD : B.card ≤ D.card + k := blue _ haA
  omega

/-- Splitting both sides of a pair increases its size-weighted mean square
density by exactly the variance of the subpair densities. In particular a
refinement chosen to repair one colour cannot cost energy in another. -/
lemma cluster_refinement_variance {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (P : Finpartition S) (Q : Finpartition T) :
    let blocks := P.parts ×ˢ Q.parts
    let weight := fun z : Finset V × Finset V => (z.1.card : ℚ) * z.2.card
    let d := fun z : Finset V × Finset V => G.edgeDensity z.1 z.2
    (∑ z ∈ blocks, weight z * (d z)^2) =
      (S.card : ℚ) * T.card * (G.edgeDensity S T)^2 +
      ∑ z ∈ blocks, weight z * (d z - G.edgeDensity S T)^2 := by
  classical
  let blocks := P.parts ×ˢ Q.parts
  let w (z : Finset V × Finset V) : ℚ := z.1.card * z.2.card
  let f (z : Finset V × Finset V) := G.edgeDensity z.1 z.2
  let D := G.edgeDensity S T
  change (∑ z ∈ blocks, w z * (f z)^2) =
    (S.card : ℚ) * T.card * D^2 + ∑ z ∈ blocks, w z * (f z-D)^2
  have hweight : ∑ z ∈ blocks, w z = (S.card : ℚ) * T.card := by
    change (∑ z ∈ P.parts ×ˢ Q.parts, (z.1.card : ℚ) * z.2.card) = _
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    exact_mod_cast congrArg₂ (· * ·) P.sum_card_parts Q.sum_card_parts
  have hmass {A B : Finset V} (ha : A.Nonempty) (hb : B.Nonempty) :
      ((A.card : ℚ) * B.card) * G.edgeDensity A B = (G.interedges A B).card := by
    rw [G.edgeDensity_def]
    field_simp [show (A.card : ℚ) ≠ 0 by exact_mod_cast ha.card_pos.ne',
      show (B.card : ℚ) ≠ 0 by exact_mod_cast hb.card_pos.ne']
  have hmean : ∑ z ∈ blocks, w z * f z = ((S.card : ℚ) * T.card) * D := by
    rw [show (S.card : ℚ) * T.card * D = (G.interedges S T).card from hmass hS hT]
    calc
      _ = ∑ z ∈ blocks, ((G.interedges z.1 z.2).card : ℚ) := by
        apply Finset.sum_congr rfl
        intro z hz
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hz
        exact hmass (P.nonempty_of_mem_parts ha) (Q.nonempty_of_mem_parts hb)
      _ = _ := by exact_mod_cast (Rel.card_interedges_finpartition G.Adj P Q).symm
  have expand (z) : w z * (f z - D)^2 = w z * (f z)^2 - (w z * f z) * (2*D) + w z * D^2 := by ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hmean, hweight]
  ring

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.benevides_skokan_large_even := by
  intro _ hforce
  unfold H2 at hforce
  filter_upwards [hforce, eventually_ge_atTop 4] with n hn hfour
  intro heven
  refine le_antisymm ?_ (even_cycle_lower_bound n hfour heven)
  apply Nat.sInf_le
  exact hn heven

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1
