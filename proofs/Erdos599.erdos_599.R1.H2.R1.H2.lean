import OMAReductions.R_Erdos599_erdos_599_R1_H2_R1
import Mathlib

/-! Finite-path transport for the nested Erdős 599 linkability reduction. -/

open SimpleGraph

namespace Erdos599Transport

/-- Last occurrence of a set among the positions up to a prescribed bound. -/
theorem exists_last_index_le_of_mem {V : Type} {G : SimpleGraph V}
    {a b : V} (q : G.Walk a b) (S : Set V) {j : ℕ}
    (h : ∃ n ≤ j, q.getVert n ∈ S) :
    ∃ n ≤ j, q.getVert n ∈ S ∧
      ∀ m ≤ j, n < m → q.getVert m ∉ S := by
  classical
  let indices : Finset ℕ :=
    (Finset.range (j + 1)).filter fun n => q.getVert n ∈ S
  have hindices : indices.Nonempty := by
    rcases h with ⟨n, hnj, hnS⟩
    refine ⟨n, ?_⟩
    simp only [indices, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hnS⟩
  let n := indices.max' hindices
  have hnmem : n ∈ indices := indices.max'_mem hindices
  have hnj : n ≤ j := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hnmem).1
    omega
  refine ⟨n, hnj, (Finset.mem_filter.mp hnmem).2, ?_⟩
  intro m hmj hnm hmS
  have hmMem : m ∈ indices := by
    simp only [indices, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmS⟩
  exact (not_lt_of_ge (indices.le_max' m hmMem)) hnm

/-- Vertices of an indexed walk segment are precisely the vertices at shifted
indices in the original walk. -/
theorem mem_segment_support_iff {V : Type} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (n j : ℕ) (hj : j ≤ p.length) {x : V} :
    x ∈ ((p.drop n).take (j - n)).support ↔
      ∃ k ≤ j - n, p.getVert (n + k) = x := by
  constructor
  · intro hx
    rcases Walk.mem_support_iff_exists_getVert.mp hx with ⟨k, hk, hklen⟩
    have hlen : ((p.drop n).take (j - n)).length = j - n := by
      rw [Walk.take_length, Walk.drop_length]
      exact min_eq_left (Nat.sub_le_sub_right hj n)
    have hkJN : k ≤ j - n := by simpa [hlen] using hklen
    refine ⟨k, hkJN, ?_⟩
    calc p.getVert (n + k) = (p.drop n).getVert k := by rw [Walk.drop_getVert]
      _ = (p.drop n).getVert ((j - n) ⊓ k) := by rw [min_eq_right hkJN]
      _ = ((p.drop n).take (j - n)).getVert k := (Walk.take_getVert ..).symm
      _ = x := hk
  · rintro ⟨k, hk, rfl⟩
    have hqv : ((p.drop n).take (j - n)).getVert k = p.getVert (n + k) := by
      rw [Walk.take_getVert, min_eq_right hk, Walk.drop_getVert]
    rw [← hqv]
    exact ((p.drop n).take (j - n)).getVert_mem_support k

theorem ne_start_of_mem_tail_of_isPath {V : Type} {G : SimpleGraph V}
    {u v x : V} {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support.tail) : x ≠ u := by
  have hrel := hp.support_nodup.rel_head_tail hx
  rw [Walk.head_support] at hrel
  exact fun hxu ↦ hrel hxu.symm

theorem ne_end_of_mem_dropLast_of_isPath {V : Type} {G : SimpleGraph V}
    {u v x : V} {p : G.Walk u v} (hp : p.IsPath)
    (hx : x ∈ p.support.dropLast) : x ≠ v := by
  have hrel := hp.support_nodup.rel_dropLast_getLast hx
  rwa [Walk.getLast_support] at hrel

end Erdos599Transport

open Erdos599Transport

theorem OMA.solution : OMA.R_Erdos599_erdos_599_R1_H2_R1.H2 := by
  classical
  intro V G A B hmax ι a b p S ha hb hp hdisjoint hsub hunique hsep
  -- Index every separator vertex by the unique orthogonal path containing it.
  have hmemS (t : S) : ∃ i, t.1 ∈ (p i).support := hsub t.2
  let idx : S → ι := fun t ↦ (hmemS t).choose
  have hidxmem (t : S) : t.1 ∈ (p (idx t)).support := (hmemS t).choose_spec
  have hunique_on_path (i : ι) {u v : V} (huS : u ∈ S) (hvS : v ∈ S)
      (hu : u ∈ (p i).support) (hv : v ∈ (p i).support) : u = v := by
    obtain ⟨w, hw, huniq⟩ := hunique i
    exact (huniq u ⟨huS, hu⟩).trans (huniq v ⟨hvS, hv⟩).symm
  have hidxinj : Function.Injective idx := by
    intro t u htu
    apply Subtype.ext
    exact hunique_on_path (idx t) t.2 u.2 (hidxmem t) (htu.symm ▸ hidxmem u)
  let w : (t : S) → G.Walk (a (idx t)) (b (idx t)) := fun t ↦ p (idx t)

  -- Choose the position of the separator vertex, then the last source vertex
  -- weakly before it.
  have hpos (t : S) : ∃ n, (w t).getVert n = t.1 ∧ n ≤ (w t).length := by
    exact Walk.mem_support_iff_exists_getVert.mp (hidxmem t)
  let j : S → ℕ := fun t ↦ (hpos t).choose
  have hj_eq (t : S) : (w t).getVert (j t) = t.1 := ((hpos t).choose_spec).1
  have hj_le (t : S) : j t ≤ (w t).length := ((hpos t).choose_spec).2
  have hA0 (t : S) : ∃ n ≤ j t, (w t).getVert n ∈ A := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [(w t).getVert_zero]
    exact ha (idx t)
  have hlast (t : S) : ∃ n ≤ j t, (w t).getVert n ∈ A ∧
      ∀ m ≤ j t, n < m → (w t).getVert m ∉ A :=
    exists_last_index_le_of_mem (w t) A (hA0 t)
  let n : S → ℕ := fun t ↦ (hlast t).choose
  have hn_spec (t : S) : n t ≤ j t ∧ (w t).getVert (n t) ∈ A ∧
      ∀ m ≤ j t, n t < m → (w t).getVert m ∉ A :=
    (hlast t).choose_spec
  let b0 : S → V := fun t ↦ (w t).getVert (n t)

  -- The wave path ending at `t` is the segment from that last source vertex.
  have hseg_end (t : S) :
      ((w t).drop (n t)).getVert (j t - n t) = t.1 := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le (hn_spec t).1, hj_eq t]
  let q0 : ∀ t : S, G.Walk (b0 t) t.1 := fun t ↦
    (((w t).drop (n t)).take (j t - n t)).copy rfl (hseg_end t)
  have hq0path (t : S) : (q0 t).IsPath := by
    dsimp [q0]
    rw [Walk.isPath_copy]
    exact ((hp (idx t)).drop (n t)).take (j t - n t)
  have hq0subset (t : S) : (q0 t).support ⊆ (p (idx t)).support := by
    intro x hx
    have hxseg : x ∈ (((w t).drop (n t)).take (j t - n t)).support := by
      simpa [q0, Walk.support_copy] using hx
    have hsubwalk : (((w t).drop (n t)).take (j t - n t)).IsSubwalk (w t) :=
      (((w t).drop (n t)).isSubwalk_take (j t - n t)).trans
        ((w t).isSubwalk_drop (n t))
    exact hsubwalk.support_subset hxseg
  have hb0A : ∀ t, b0 t ∈ A := fun t ↦ (hn_spec t).2.1

  -- No source vertex occurs after the chosen last source vertex on a wave path.
  have hq0A (t : S) : ∀ x ∈ (q0 t).support.tail, x ∉ A := by
    intro x hxtail hxA
    simp only [q0, Walk.support_copy] at hxtail
    have hxseg : x ∈ (((w t).drop (n t)).take (j t - n t)).support :=
      List.mem_of_mem_tail hxtail
    obtain ⟨k, hk, hkx⟩ :=
      (mem_segment_support_iff (w t) (n t) (j t) (hj_le t)).mp hxseg
    have hqsegpath : (((w t).drop (n t)).take (j t - n t)).IsPath :=
      ((hp (idx t)).drop (n t)).take (j t - n t)
    have hxne : x ≠ (w t).getVert (n t) :=
      ne_start_of_mem_tail_of_isPath hqsegpath hxtail
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hxne
      calc x = (w t).getVert (n t + k) := hkx.symm
        _ = (w t).getVert (n t) := by rw [hk0, add_zero]
    have hlej : n t + k ≤ j t := by
      have hle : n t + k ≤ n t + (j t - n t) := Nat.add_le_add_left hk _
      rwa [Nat.add_sub_of_le (hn_spec t).1] at hle
    have hnoA := (hn_spec t).2.2 (n t + k) hlej
      (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk0))
    have hxA' : (w t).getVert (n t + k) ∈ A := by
      rwa [hkx]
    exact hnoA hxA'

  -- No target vertex occurs strictly before the separator vertex. Otherwise
  -- the prefix to that target vertex would be an `A`--`B` path missing `S`.
  have hq0B (t : S) : ∀ x ∈ (q0 t).support.dropLast, x ∉ B := by
    intro x hxdrop hxB
    simp only [q0, Walk.support_copy] at hxdrop
    have hxseg : x ∈ (((w t).drop (n t)).take (j t - n t)).support :=
      List.mem_of_mem_dropLast hxdrop
    obtain ⟨k, hk, hkx⟩ :=
      (mem_segment_support_iff (w t) (n t) (j t) (hj_le t)).mp hxseg
    have hqsegpath : (((w t).drop (n t)).take (j t - n t)).IsPath :=
      ((hp (idx t)).drop (n t)).take (j t - n t)
    have hxne_end := ne_end_of_mem_dropLast_of_isPath hqsegpath hxdrop
    rw [hseg_end t] at hxne_end
    have hklt : k < j t - n t := by
      refine lt_of_le_of_ne hk ?_
      intro hkeq
      apply hxne_end
      calc x = (w t).getVert (n t + k) := hkx.symm
        _ = (w t).getVert (j t) := by
          congr 1
          have hnj : n t ≤ j t := (hn_spec t).1
          omega
        _ = t.1 := hj_eq t
    have hm_lt_j : n t + k < j t := by
      have hlt : n t + k < n t + (j t - n t) := Nat.add_lt_add_left hklt _
      rwa [Nat.add_sub_of_le (hn_spec t).1] at hlt
    let pre0 := (w t).take (n t + k)
    let pre : G.Walk (a (idx t)) x := pre0.copy rfl hkx
    have hprepath : pre.IsPath := by
      dsimp [pre, pre0]
      rw [Walk.isPath_copy]
      exact (hp (idx t)).take (n t + k)
    obtain ⟨s, hs_pre, hsS⟩ :=
      hsep (a (idx t)) (ha (idx t)) x hxB pre hprepath
    have hs_pre0 : s ∈ pre0.support := by
      simpa [pre, pre0, Walk.support_copy] using hs_pre
    obtain ⟨l, hsl, hlle⟩ := Walk.mem_support_iff_exists_getVert.mp hs_pre0
    have hlm : l ≤ n t + k := by
      have hlmin : l ≤ (n t + k) ⊓ (w t).length := by
        simpa [pre0, Walk.take_length] using hlle
      exact le_trans hlmin (min_le_left _ _)
    have hsl_w : (w t).getVert l = s := by
      calc (w t).getVert l = (w t).getVert ((n t + k) ⊓ l) := by
            rw [min_eq_right hlm]
        _ = ((w t).take (n t + k)).getVert l := (Walk.take_getVert ..).symm
        _ = s := hsl
    have hs_w : s ∈ (w t).support :=
      ((w t).isSubwalk_take (n t + k)).support_subset hs_pre0
    have hst : s = t.1 :=
      hunique_on_path (idx t) hsS t.2 hs_w (hidxmem t)
    have hl_eq_t : (w t).getVert l = (w t).getVert (j t) := by
      calc (w t).getVert l = s := hsl_w
        _ = t.1 := hst
        _ = (w t).getVert (j t) := (hj_eq t).symm
    have hl_len : l ≤ (w t).length :=
      le_trans hlm (le_trans hm_lt_j.le (hj_le t))
    have hl_eq_j : l = j t :=
      (hp (idx t)).getVert_injOn hl_len (hj_le t) hl_eq_t
    have hl_lt_j : l < j t :=
      lt_of_le_of_lt hlm hm_lt_j
    exact (Nat.ne_of_lt hl_lt_j) hl_eq_j

  have hq0hits (t : S) :
      (∀ x ∈ (q0 t).support.tail, x ∉ A) ∧
        (∀ x ∈ (q0 t).support.dropLast, x ∉ B) :=
    ⟨hq0A t, hq0B t⟩
  have hq0disjoint :
      Pairwise fun t u ↦ Disjoint {v | v ∈ (q0 t).support} {v | v ∈ (q0 u).support} := by
    intro t u htu
    have hidxne : idx t ≠ idx u := fun h ↦ htu (hidxinj h)
    refine Set.disjoint_left.2 ?_
    intro x hxt hxu
    exact Set.disjoint_left.1 (hdisjoint hidxne)
      (hq0subset t hxt) (hq0subset u hxu)

  -- Unhinderedness forces the trimmed wave to start at every source vertex.
  have hcover : ∀ x ∈ A, ∃ t, b0 t = x :=
    hmax S b0 q0 hb0A hq0path hq0hits hq0disjoint hsep
  let tOf : A → S := fun x ↦ (hcover x.1 x.2).choose
  have htOf (x : A) : b0 (tOf x) = x.1 := (hcover x.1 x.2).choose_spec
  let bOut : A → V := fun x ↦ b (idx (tOf x))
  let pOut : ∀ x : A, G.Walk x.1 (bOut x) := fun x ↦
    ((w (tOf x)).drop (n (tOf x))).copy (htOf x) rfl
  refine ⟨bOut, pOut, fun x ↦ hb (idx (tOf x)), ?_⟩
  intro x y hxy
  have htxy : tOf x ≠ tOf y := by
    intro ht
    apply hxy
    apply Subtype.ext
    calc x.1 = b0 (tOf x) := (htOf x).symm
      _ = b0 (tOf y) := by rw [ht]
      _ = y.1 := htOf y
  have hidxne : idx (tOf x) ≠ idx (tOf y) := fun h ↦ htxy (hidxinj h)
  refine Set.disjoint_left.2 ?_
  intro v hvx hvy
  have hvxs : v ∈ ((w (tOf x)).drop (n (tOf x))).support := by
    change v ∈ ((((w (tOf x)).drop (n (tOf x))).copy (htOf x) rfl).support) at hvx
    rwa [Walk.support_copy] at hvx
  have hvys : v ∈ ((w (tOf y)).drop (n (tOf y))).support := by
    change v ∈ ((((w (tOf y)).drop (n (tOf y))).copy (htOf y) rfl).support) at hvy
    rwa [Walk.support_copy] at hvy
  have hvxt : v ∈ (p (idx (tOf x))).support :=
    ((w (tOf x)).isSubwalk_drop (n (tOf x))).support_subset hvxs
  have hvyt : v ∈ (p (idx (tOf y))).support :=
    ((w (tOf y)).isSubwalk_drop (n (tOf y))).support_subset hvys
  exact Set.disjoint_left.1 (hdisjoint hidxne) hvxt hvyt
