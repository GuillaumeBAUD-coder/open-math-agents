import OMAStatements.S_opg_linial_berge_path_partition_duality
import Mathlib

-- Reduction opg-linial-berge-path-partition-duality.R3 of Linial-Berge path partition duality
-- Credit: @MBimrose
--
-- The target is Linial's path partition conjecture (the "weak" form of Berge's conjecture): for every finite
-- loopless digraph D and every k >= 1 there is a path partition P and a set S inducing a k-colourable
-- subgraph with  sum_{p in P} min(|p|,k) <= |S|.
--
-- This reduction sharpens the open core as far as elementary arguments reach. It has only TWO hypotheses:
--
--   H1  the k = 1 instance (Gallai-Milgram 1960: min number of paths <= max stable set). Known theorem.
--   H2  the open core, with every provable class removed: 2 <= k < |V|, D ORIENTED (no pair carries arcs in
--       both directions), D has NO directed Hamiltonian path, and the underlying undirected graph of D is NOT
--       k-colourable. This is where the conjecture actually lives (by the literature it is open: the known
--       cases are k = 1, acyclic D, k = 2, and k >= lambda - 3 for lambda the longest-path order; the case
--       k >= lambda is trivial and is discharged here, see below).
--
-- The bridge `main` proves the three classes that are NOT part of H2, with explicit constructions:
--   (a) k >= |V|: S = V with an injective colouring (|V| <= k), partition into singletons, k-norm |V|.
--   (b) the underlying graph is k-colourable: S = V with that colouring; the singleton partition has
--       k-norm at most |V| = |S|. (This covers, by Gallai-Roy-Vitaver, every D whose longest directed path
--       has at most k vertices - the `k >= lambda` case - and every bipartite-underlying D for k = 2.)
--   (c) D has a directed Hamiltonian path: the single path has k-norm min(|V|,k) = k, and its first k
--       vertices are k-colourable by an injective colouring (positions on the path).
--   (d) 2-cycles: any loopless D can be replaced by an ORIENTATION D' of the same underlying graph with
--       D' subset D (keep one arc of every pair, chosen by a linear order on V). Every directed path of D'
--       is one of D, and `IsProperOn` only sees the underlying graph, so a solution for D' is one for D.
-- So `main` handles k = 1 by H1, then orients D and dispatches (a), (b), (c) with constructions and leaves
-- exactly the non-k-colourable, Hamiltonian-path-free, intermediate-k case to H2.
--
-- Audit (no vacuous or false hypothesis, each used, non-redundant):
--   * H1: domain inhabited (one vertex, k = 1); Gallai-Milgram is a theorem, so H1 is true.
--   * H2: domain inhabited - two disjoint directed odd cycles (5-cycle and 3-cycle, k = 2) are oriented, have
--     no Hamiltonian path, and their underlying graph is not 2-colourable, with 2 <= 2 < 8.
--   * Both are restrictions of the target instance to a subclass, so the target implies each of them.
--   * main uses H1 in the k = 1 branch and H2 only in the last branch of an exhaustive split
--     (k >= |V|, then k-colourable, then Hamiltonian path, else H2); neither is used twice or vacuously.

namespace OMA.R_opg_linial_berge_path_partition_duality_R3

open OMA.S_opg_linial_berge_path_partition_duality

/-- The `k = 1` instance for arbitrary loopless digraphs: Gallai-Milgram. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) → ∀ k : ℕ, k = 1 →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card

/-- The open core: `2 <= k < |V|`, oriented, no directed Hamiltonian path, and the underlying undirected
graph is not k-colourable. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (D : Digraph V), (∀ v, ¬ D.Adj v v) →
    (∀ u v, D.Adj u v → ¬ D.Adj v u) → ∀ k : ℕ, 2 ≤ k → k < Fintype.card V →
      (¬ ∃ (l : ℕ) (q : Fin (l + 1) → V), IsDirectedPath D q ∧ l + 1 = Fintype.card V) →
        (¬ ∃ c : V → Fin k, ∀ u v, (D.Adj u v ∨ D.Adj v u) → c u ≠ c v) →
          ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
            (∀ j, IsDirectedPath D (p j)) ∧
              (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
                ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
                  ∑ j, min (len j + 1) k ≤ S.card

/-- `k >= |V|`: singletons, `S = univ`, injective colouring. -/
lemma large_k_solution (V : Type) [Fintype V] (D : Digraph V) (hloop : ∀ v, ¬ D.Adj v v)
    (k : ℕ) (hcard : Fintype.card V ≤ k) :
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨Fintype.card V, fun _ => 0, fun j _ => e.symm j, ?_, ?_, Finset.univ,
    fun v => Fin.castLE hcard (e v), ?_, ?_⟩
  · intro j
    refine ⟨?_, fun i => Fin.elim0 i⟩
    intro a b _
    have ha : a.val = 0 := Nat.lt_one_iff.mp (show a.val < 1 from a.isLt)
    have hb : b.val = 0 := Nat.lt_one_iff.mp (show b.val < 1 from b.isLt)
    exact Fin.ext (by rw [ha, hb])
  · intro v
    refine ⟨⟨e v, 0⟩, e.symm_apply_apply v, ?_⟩
    intro y hy
    obtain ⟨j, w⟩ := y
    dsimp only at hy
    have hj : j = e v := by
      have h : e (e.symm j) = e v := by rw [hy]
      rwa [Equiv.apply_symm_apply] at h
    subst hj
    have hw : w = 0 := by
      apply Fin.ext
      show w.val = 0
      exact Nat.lt_one_iff.mp (show w.val < 1 from w.isLt)
    exact congrArg (fun w => Sigma.mk (e v) w) hw
  · intro u _ v _ huv hc
    have hne : u ≠ v := fun h => hloop u (h ▸ huv)
    have hc' : Fin.castLE hcard (e u) = Fin.castLE hcard (e v) := hc
    have hval : (Fin.castLE hcard (e u)).val = (Fin.castLE hcard (e v)).val := congrArg Fin.val hc'
    exact hne (e.injective (Fin.ext (by simpa using hval)))
  · calc ∑ j : Fin (Fintype.card V), min (0 + 1) k
        ≤ ∑ j : Fin (Fintype.card V), 1 := Finset.sum_le_sum (fun j _ => Nat.min_le_left 1 k)
      _ = Fintype.card V := by simp
      _ = (Finset.univ : Finset V).card := by simp

/-- The underlying undirected graph is k-colourable: singletons, `S = univ`, the given colouring. -/
lemma kcolourable_solution (V : Type) [Fintype V] (D : Digraph V)
    (k : ℕ) (c : V → Fin k) (hc : ∀ u v, D.Adj u v → c u ≠ c v) :
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c' : V → Fin k), IsProperOn D S c' ∧
            ∑ j, min (len j + 1) k ≤ S.card := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨Fintype.card V, fun _ => 0, fun j _ => e.symm j, ?_, ?_, Finset.univ, c, ?_, ?_⟩
  · intro j
    refine ⟨?_, fun i => Fin.elim0 i⟩
    intro a b _
    have ha : a.val = 0 := Nat.lt_one_iff.mp (show a.val < 1 from a.isLt)
    have hb : b.val = 0 := Nat.lt_one_iff.mp (show b.val < 1 from b.isLt)
    exact Fin.ext (by rw [ha, hb])
  · intro v
    refine ⟨⟨e v, 0⟩, e.symm_apply_apply v, ?_⟩
    intro y hy
    obtain ⟨j, w⟩ := y
    dsimp only at hy
    have hj : j = e v := by
      have h : e (e.symm j) = e v := by rw [hy]
      rwa [Equiv.apply_symm_apply] at h
    subst hj
    have hw : w = 0 := by
      apply Fin.ext
      show w.val = 0
      exact Nat.lt_one_iff.mp (show w.val < 1 from w.isLt)
    exact congrArg (fun w => Sigma.mk (e v) w) hw
  · intro u _ v _ huv
    exact hc u v huv
  · calc ∑ j : Fin (Fintype.card V), min (0 + 1) k
        ≤ ∑ j : Fin (Fintype.card V), 1 := Finset.sum_le_sum (fun j _ => Nat.min_le_left 1 k)
      _ = Fintype.card V := by simp
      _ = (Finset.univ : Finset V).card := by simp

/-- A directed Hamiltonian path: the path is the partition, its first `k` vertices are the set `S`. -/
lemma ham_solution (V : Type) [Fintype V] (D : Digraph V) (hloop : ∀ v, ¬ D.Adj v v)
    (k : ℕ) (hk2 : 2 ≤ k) (hlt : k < Fintype.card V) (l : ℕ) (q : Fin (l + 1) → V)
    (hq : IsDirectedPath D q) (hcard : l + 1 = Fintype.card V) :
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card := by
  classical
  have hq_inj : Function.Injective q := hq.1
  have hkl : k ≤ l + 1 := by omega
  let f : Fin k → V := fun i => q (Fin.castLE hkl i)
  have hf_inj : Function.Injective f := hq_inj.comp (Fin.castLE_injective hkl)
  let pos : V → Fin k := fun v =>
    if h : ∃ i : Fin k, f i = v then Classical.choose h else ⟨0, by omega⟩
  have hpos : ∀ i : Fin k, pos (f i) = i := by
    intro i
    have hex : ∃ j : Fin k, f j = f i := ⟨i, rfl⟩
    have hval : pos (f i) = Classical.choose hex := dif_pos hex
    rw [hval]
    exact hf_inj (Classical.choose_spec hex)
  have hsurj : Function.Surjective q :=
    (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivFinOfCardEq hcard.symm).symm).mp hq_inj
  refine ⟨1, fun _ => l, fun _ => q, ?_, ?_, Finset.univ.image f, pos, ?_, ?_⟩
  · intro j
    exact hq
  · intro v
    obtain ⟨i, hi⟩ := hsurj v
    refine ⟨⟨0, i⟩, hi, ?_⟩
    rintro ⟨j, w⟩ hw
    dsimp only at hw
    have hwi : w = i := hq_inj (by rw [hw, hi])
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    subst hwi
    rfl
  · intro u hu v hv huv hc
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hv
    rw [← hi, ← hj] at huv
    have hne : i ≠ j := by
      rintro rfl
      exact hloop (f i) huv
    apply hne
    rw [← hi, ← hj] at hc
    rw [hpos i, hpos j] at hc
    exact hc
  · have hcardS : (Finset.univ.image f).card = k := by
      rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
    rw [Fin.sum_univ_one, hcardS, Nat.min_eq_right hkl]

/-- The two hypotheses imply the target: `k = 1`, then the orientation of `D`, then the three provable
classes, and finally the open core. -/
theorem main : H1 → H2 →
    type_of% @OMA.S_opg_linial_berge_path_partition_duality.main := by
  intro h1 h2 V instV D hloop k hk
  by_cases hk1 : k = 1
  · exact h1 V D hloop k hk1
  have hk2 : 2 ≤ k := by omega
  -- replace `D` by an orientation `D'` of the same underlying graph, with `D'` a sub-digraph of `D`
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let D' : Digraph V :=
    ⟨fun v w => (D.Adj v w ∧ ¬ D.Adj w v) ∨ (D.Adj v w ∧ D.Adj w v ∧ e v < e w)⟩
  have hsub : ∀ v w, D'.Adj v w → D.Adj v w := by
    intro v w h
    rcases h with h' | h'
    · exact h'.1
    · exact h'.1
  have hloop' : ∀ v, ¬ D'.Adj v v := fun v h => hloop v (hsub v v h)
  have hor : ∀ v w, D'.Adj v w → ¬ D'.Adj w v := by
    intro v w h h'
    have hv : D.Adj v w := hsub v w h
    have hw : D.Adj w v := hsub w v h'
    rcases h with ⟨_, hn⟩ | ⟨_, _, hlt⟩
    · exact hn hw
    · rcases h' with ⟨_, hn⟩ | ⟨_, _, hlt'⟩
      · exact hn hv
      · exact absurd hlt' (not_lt.mpr (le_of_lt hlt))
  have hunder : ∀ v w, v ≠ w → ((D'.Adj v w ∨ D'.Adj w v) ↔ (D.Adj v w ∨ D.Adj w v)) := by
    intro v w hne
    have hlt : e v < e w ∨ e w < e v := lt_or_gt_of_ne (fun he => hne (e.injective he))
    constructor
    · rintro (h | h)
      · exact Or.inl (hsub v w h)
      · exact Or.inr (hsub w v h)
    · rintro (h | h)
      · by_cases hb : D.Adj w v
        · rcases hlt with hl | hl
          · exact Or.inl (Or.inr ⟨h, hb, hl⟩)
          · exact Or.inr (Or.inr ⟨hb, h, hl⟩)
        · exact Or.inl (Or.inl ⟨h, hb⟩)
      · by_cases ha : D.Adj v w
        · rcases hlt with hl | hl
          · exact Or.inl (Or.inr ⟨ha, h, hl⟩)
          · exact Or.inr (Or.inr ⟨h, ha, hl⟩)
        · exact Or.inr (Or.inl ⟨h, ha⟩)
  -- a solution for the orientation is a solution for `D`
  have transfer : (∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D' (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D' S c ∧
            ∑ j, min (len j + 1) k ≤ S.card) →
    ∃ (N : ℕ) (len : Fin N → ℕ) (p : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (p j)) ∧
        (∀ v, ∃! x : (Σ j, Fin (len j + 1)), p x.1 x.2 = v) ∧
          ∃ (S : Finset V) (c : V → Fin k), IsProperOn D S c ∧
            ∑ j, min (len j + 1) k ≤ S.card := by
    rintro ⟨N, len, p, hpath, hcover, S, c, hprop, hsum⟩
    refine ⟨N, len, p, fun j => ⟨(hpath j).1, fun i => hsub _ _ ((hpath j).2 i)⟩, hcover, S, c, ?_, hsum⟩
    intro u hu v hv huv
    have hne : u ≠ v := fun h => hloop u (h ▸ huv)
    rcases (hunder u v hne).mpr (Or.inl huv) with h | h
    · exact hprop u hu v hv h
    · exact fun hc => hprop v hv u hu h hc.symm
  apply transfer
  by_cases hbig : Fintype.card V ≤ k
  · exact large_k_solution V D' hloop' k hbig
  · by_cases hcol : ∃ c : V → Fin k, ∀ u v, (D.Adj u v ∨ D.Adj v u) → c u ≠ c v
    · obtain ⟨c, hc⟩ := hcol
      refine kcolourable_solution V D' k c (fun u v huv => ?_)
      have hne : u ≠ v := fun h => hloop' u (h ▸ huv)
      exact hc u v ((hunder u v hne).mp (Or.inl huv))
    · have hlt : k < Fintype.card V := not_le.mp hbig
      by_cases hham : ∃ (l : ℕ) (q : Fin (l + 1) → V), IsDirectedPath D' q ∧ l + 1 = Fintype.card V
      · obtain ⟨l, q, hq, hcard⟩ := hham
        exact ham_solution V D' hloop' k hk2 hlt l q hq hcard
      · refine h2 V D' hloop' hor k hk2 hlt hham ?_
        rintro ⟨c, hc⟩
        apply hcol
        refine ⟨c, fun u v huv => ?_⟩
        by_cases huv' : u = v
        · subst huv'
          rcases huv with h | h
          · exact absurd h (hloop u)
          · exact absurd h (hloop u)
        · rcases (hunder u v huv').mpr huv with h | h
          · exact hc u v (Or.inl h)
          · exact fun hh => hc v u (Or.inl h) hh.symm

end OMA.R_opg_linial_berge_path_partition_duality_R3
