import FormalConjectures.ErdosProblems.«128»

-- Reduction Erdos128.erdos_128.R1 of Erdős Problem 128
-- Credit: @ashnewmanjones
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Erdős 128 is equivalent to: every triangle-free graph on n vertices has a set of at least
-- (n - 1) / 2 vertices spanning at most n^2 / 50 edges (a sparse half). We split by the edge
-- count e of G:
--   * e ≤ 2 n^2 / 25: PROVED below (sparse_case), by deleting a vertex of maximum degree until
--     n / 2 vertices remain, which keeps at most a (n/2)(n/2 - 1) / (n (n - 1)) ≤ 1/4 fraction
--     of the edges.
--   * e ≥ n^2 / 5 (average degree ≥ 2n/5): H1, a known theorem (Keevash and Sudakov, Sparse
--     halves in triangle-free graphs, JCTB 2006; see also Norin and Yepremyan, Sparse halves in
--     dense triangle-free graphs, JCTB 2015).
--   * 2 n^2 / 25 < e < n^2 / 5: H2, the open core of the problem.

namespace OMA.R_Erdos128_erdos_128_R1

open Finset

-- Dense case (known): a triangle-free graph with at least n^2 / 5 edges has a sparse half.
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    Fintype.card V ^ 2 ≤ 5 * G.edgeSet.ncard →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- Middle range (open): a triangle-free graph with between 2 n^2 / 25 and n^2 / 5 edges has a
-- sparse half.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    2 * Fintype.card V ^ 2 < 25 * G.edgeSet.ncard →
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

-- Twice the number of edges of the induced graph on S is the sum of degrees inside S.
lemma two_mul_induce (S : Finset V) :
    2 * (G.induce (S : Set V)).edgeSet.ncard = ∑ v ∈ S, (S.filter (G.Adj v)).card := by
  classical
  set H := G.induce (S : Set V)
  rw [← H.coe_edgeFinset, Set.ncard_coe_finset, ← H.sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort S]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun v => ?_
  simp only [Equiv.refl_apply]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _ => (w : V)) ?_ ?_ ?_
  · intro w hw
    simp only [SimpleGraph.mem_neighborFinset, H, SimpleGraph.comap_adj,
      Function.Embedding.coe_subtype] at hw
    exact mem_filter.mpr ⟨by simp, hw⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro w hw
    obtain ⟨hwS, hadj⟩ := mem_filter.mp hw
    refine ⟨⟨w, by simp [hwS]⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj


-- Deleting a vertex v from S removes 2 deg_S(v) from the degree sum.
lemma deg_sum_erase (S : Finset V) {v : V} (hv : v ∈ S) :
    ∑ u ∈ S, (S.filter (G.Adj u)).card =
      ∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card + 2 * (S.filter (G.Adj v)).card := by
  rw [← Finset.add_sum_erase S _ hv]
  have h1 : ∀ u ∈ S.erase v, (S.filter (G.Adj u)).card =
      ((S.erase v).filter (G.Adj u)).card + if G.Adj u v then 1 else 0 := by
    intro u _
    conv_lhs => rw [← Finset.insert_erase hv]
    rw [Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_boole]
  have h2 : ((S.erase v).filter (fun u => G.Adj u v)).card = (S.filter (G.Adj v)).card := by
    congr 1
    ext u
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hu⟩, h⟩
      exact ⟨hu, h.symm⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨fun e => G.ne_of_adj h e.symm, hu⟩, h.symm⟩
  simp only [Nat.cast_id] at h2 ⊢
  rw [h2]
  ring

lemma deg_sum_erase_total (S : Finset V) :
    ∑ v ∈ S, ∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card +
      2 * ∑ u ∈ S, (S.filter (G.Adj u)).card = S.card * ∑ u ∈ S, (S.filter (G.Adj u)).card := by
  have h : ∀ v ∈ S, ∑ u ∈ S, (S.filter (G.Adj u)).card =
      ∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card + 2 * (S.filter (G.Adj v)).card :=
    fun v hv => deg_sum_erase G S hv
  calc ∑ v ∈ S, ∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card +
        2 * ∑ u ∈ S, (S.filter (G.Adj u)).card
      = ∑ v ∈ S, (∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card +
          2 * (S.filter (G.Adj v)).card) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ _v ∈ S, ∑ u ∈ S, (S.filter (G.Adj u)).card := Finset.sum_congr rfl fun v hv => (h v hv).symm
    _ = S.card * ∑ u ∈ S, (S.filter (G.Adj u)).card := by rw [Finset.sum_const, smul_eq_mul]

-- Some vertex can be deleted losing at least a 2/|S| fraction of the degree sum.
lemma exists_good_vertex (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, S.card * ∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card +
      2 * ∑ u ∈ S, (S.filter (G.Adj u)).card ≤ S.card * ∑ u ∈ S, (S.filter (G.Adj u)).card := by
  apply Finset.exists_le_of_sum_le hS
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul]
  have := deg_sum_erase_total G S
  nlinarith [this]

-- Repeated deletion: a set of size n - d whose degree sum is at most the
-- (n - d)(n - d - 1) / (n (n - 1)) fraction of the whole degree sum.
lemma descend : ∀ d, d ≤ Fintype.card V → ∃ S : Finset V, S.card = Fintype.card V - d ∧
    (∑ u ∈ S, (S.filter (G.Adj u)).card) * (Fintype.card V * (Fintype.card V - 1)) ≤
      (Fintype.card V - d) * (Fintype.card V - d - 1) *
        ∑ u ∈ (univ : Finset V), ((univ : Finset V).filter (G.Adj u)).card := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨univ, by simp, by simp; exact le_of_eq (by ring)⟩
  | succ d ih =>
    intro hd
    obtain ⟨S, hS, hb⟩ := ih (by omega)
    have hpos : 0 < S.card := by rw [hS]; omega
    obtain ⟨v, hv, hgood⟩ := exists_good_vertex G S (Finset.card_pos.mp hpos)
    have hcard : (S.erase v).card = Fintype.card V - (d + 1) := by
      rw [Finset.card_erase_of_mem hv, hS]; omega
    refine ⟨S.erase v, hcard, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    have e1 : Fintype.card V - d = m + 1 := by omega
    have e2 : Fintype.card V - d - 1 = m := by omega
    have e3 : Fintype.card V - (d + 1) = m := by omega
    rw [e2, e1] at hb
    rw [e3]
    rw [hm] at hgood
    generalize (∑ u ∈ S.erase v, ((S.erase v).filter (G.Adj u)).card) = a at hgood ⊢
    generalize (∑ u ∈ S, (S.filter (G.Adj u)).card) = b at hgood hb
    generalize (∑ u ∈ (univ : Finset V), ((univ : Finset V).filter (G.Adj u)).card) = c at hb ⊢
    generalize (Fintype.card V * (Fintype.card V - 1)) = N at hb ⊢
    rcases m with _ | m
    · have ha : a = 0 := by simp at hgood; omega
      simp [ha]
    · have h1 : (m + 1 + 1) * a ≤ m * b := by nlinarith [hgood]
      have h3 : (m + 1 + 1) * (a * N) ≤ (m + 1 + 1) * ((m + 1) * m * c) := by
        calc (m + 1 + 1) * (a * N) = ((m + 1 + 1) * a) * N := by ring
          _ ≤ (m * b) * N := Nat.mul_le_mul_right _ h1
          _ = m * (b * N) := by ring
          _ ≤ m * ((m + 1 + 1) * (m + 1) * c) := Nat.mul_le_mul_left _ hb
          _ = (m + 1 + 1) * ((m + 1) * m * c) := by ring
      simp only [Nat.add_sub_cancel]
      exact Nat.le_of_mul_le_mul_left h3 (by omega)

-- The degree sum of the whole graph is twice its number of edges.
lemma deg_sum_univ :
    ∑ u ∈ (univ : Finset V), ((univ : Finset V).filter (G.Adj u)).card = 2 * G.edgeSet.ncard := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset, ← G.sum_degrees_eq_twice_card_edges]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

lemma four_mul_le (n k : ℕ) (h : 2 * (k + 1) ≤ n) : 4 * ((k + 1) * k) ≤ n * (n - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith

-- The sparse case: at most 2n²/25 edges forces a half spanning at most n²/50 edges.
lemma sparse_case (h : 25 * G.edgeSet.ncard ≤ 2 * Fintype.card V ^ 2) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  set n := Fintype.card V with hn
  obtain ⟨S, hS, hb⟩ := descend G (n - n / 2) (by omega)
  have hk : n - (n - n / 2) = n / 2 := by omega
  rw [hk] at hS hb
  refine ⟨(S : Set V), ?_, ?_⟩
  · rw [Set.ncard_coe_finset, hS]; omega
  · have h2 := two_mul_induce G S
    rw [deg_sum_univ] at hb
    set a := ∑ u ∈ S, (S.filter (G.Adj u)).card
    set E := (G.induce (S : Set V)).edgeSet.ncard
    set e := G.edgeSet.ncard
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n ≤ 1: the half is empty
      have hS0 : S = ∅ := by
        rw [← Finset.card_eq_zero, hS]; omega
      have ha : a = 0 := by simp [a, hS0]
      omega
    · obtain ⟨k, hk⟩ : ∃ k, n / 2 = k + 1 := ⟨n / 2 - 1, by omega⟩
      rw [hk] at hb
      simp only [Nat.add_sub_cancel] at hb
      have h2k : 2 * (k + 1) ≤ n := by omega
      have hkk : 4 * ((k + 1) * k) ≤ n * (n - 1) := four_mul_le n k h2k
      have hN : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
      have key : (25 * a) * (n * (n - 1)) ≤ n ^ 2 * (n * (n - 1)) := by
        calc (25 * a) * (n * (n - 1)) = 25 * (a * (n * (n - 1))) := by ring
          _ ≤ 25 * ((k + 1) * k * (2 * e)) := Nat.mul_le_mul_left _ hb
          _ = ((k + 1) * k) * (2 * (25 * e)) := by ring
          _ ≤ ((k + 1) * k) * (2 * (2 * n ^ 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
          _ = (4 * ((k + 1) * k)) * n ^ 2 := by ring
          _ ≤ (n * (n - 1)) * n ^ 2 := Nat.mul_le_mul_right _ hkk
          _ = n ^ 2 * (n * (n - 1)) := by ring
      have := Nat.le_of_mul_le_mul_right key hN
      omega

theorem main : H1 → H2 → type_of% @Erdos128.erdos_128 := by
  intro h1 h2 V _ G hG hcf
  classical
  have contra : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 → False :=
    fun V' ha hb => absurd (hG V' ha) (not_lt.mpr hb)
  rcases le_or_gt (Fintype.card V ^ 2) (5 * G.edgeSet.ncard) with hd | hd
  · obtain ⟨V', ha, hb⟩ := h1 V G hcf hd
    exact contra V' ha hb
  · rcases le_or_gt (25 * G.edgeSet.ncard) (2 * Fintype.card V ^ 2) with hs | hs
    · obtain ⟨V', ha, hb⟩ := sparse_case G hs
      exact contra V' ha hb
    · obtain ⟨V', ha, hb⟩ := h2 V G hcf hs hd
      exact contra V' ha hb

end OMA.R_Erdos128_erdos_128_R1
