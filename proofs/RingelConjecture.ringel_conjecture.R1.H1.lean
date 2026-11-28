import OMAReductions.R_RingelConjecture_ringel_conjecture_R1
import Mathlib

-- Step RingelConjecture.ringel_conjecture.R1.H1: Ringel's conjecture for paths (Rosa 1967).
-- The path v_0, ..., v_n gets the zigzag labels 0, n, 1, n - 1, 2, ... (label k / 2 at even k,
-- n - k / 2 at odd k); the edge v_k v_(k+1) then has length n - k, so all lengths 1, ..., n
-- occur once, and the cyclic shifts of this labelling decompose K_(2n+1).
-- The cyclic-shift lemma (rosa_kotzig_cyclic with its three helpers) and the Hamiltonian path
-- lemma for trees of maximum degree 2 (walk_exists_boundary_edge,
-- tree_maxDeg_le_two_hamiltonian) are adapted from the merged open-math-agents reduction
-- Arxiv.2001.02665.kotzig_conjecture_large.R1 (PR 6354), credit: @ItsNotTheGabs.
-- The zigzag labelling, its rainbow property and the assembly are original.

namespace OMA.RingelPaths

open SimpleGraph

private lemma fin_odd_add_self_inj {n : ℕ} {i j : Fin (2 * n + 1)}
    (h : i + i = j + j) : i = j := by
  have hval := congrArg Fin.val h
  simp only [Fin.val_add] at hval
  have hi := i.isLt
  have hj := j.isLt
  ext
  by_cases h1 : i.val + i.val < 2 * n + 1 <;> by_cases h2 : j.val + j.val < 2 * n + 1
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at hval
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    omega

private lemma fin_sub_val_add_symm {n : ℕ} {x y : Fin (2 * n + 1)} (hne : x ≠ y) :
    (x - y).val + (y - x).val = 2 * n + 1 := by
  have h1 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h2 : y - x ≠ 0 := sub_ne_zero.mpr hne.symm
  have h1' : 0 < (x - y).val := Nat.pos_of_ne_zero (fun h => h1 (Fin.ext h))
  have h2' : 0 < (y - x).val := Nat.pos_of_ne_zero (fun h => h2 (Fin.ext h))
  have hsum : (x - y) + (y - x) = 0 := by abel
  have hval := congrArg Fin.val hsum
  simp only [Fin.val_add, Fin.val_zero] at hval
  have hlt1 := (x - y).isLt
  have hlt2 := (y - x).isLt
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hval
  have hk1 : k = 1 := by nlinarith
  rw [hk1, mul_one] at hk
  exact hk

private lemma fin_nd_eq_iff {n : ℕ} {x₁ y₁ x₂ y₂ : Fin (2 * n + 1)}
    (h1 : x₁ ≠ y₁) (h2 : x₂ ≠ y₂)
    (hmin : min (x₁ - y₁).val (y₁ - x₁).val = min (x₂ - y₂).val (y₂ - x₂).val) :
    x₁ - y₁ = x₂ - y₂ ∨ x₁ - y₁ = y₂ - x₂ := by
  have hs1 := fin_sub_val_add_symm h1
  have hs2 := fin_sub_val_add_symm h2
  by_cases ha : (x₁ - y₁).val ≤ (y₁ - x₁).val <;> by_cases hb : (x₂ - y₂).val ≤ (y₂ - x₂).val
  · left; ext; simp only [min_eq_left ha, min_eq_left hb] at hmin; exact hmin
  · right; ext; simp only [min_eq_left ha, min_eq_right (le_of_not_ge hb)] at hmin; exact hmin
  · right; ext; simp only [min_eq_right (le_of_not_ge ha), min_eq_left hb] at hmin; omega
  · left; ext
    simp only [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb)] at hmin
    omega

private lemma rosa_kotzig_cyclic {n : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hcard : T.edgeSet.ncard = n)
    (g : V ↪ Fin (2 * n + 1))
    (hrain : ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
      (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
      s(u₁, v₁) = s(u₂, v₂)) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  let f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)) :=
    fun i => g.trans ⟨(· + i), add_left_injective i⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i v
    simp [f]
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hi hj
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet, SimpleGraph.map_adj] at hi hj
      obtain ⟨u₁, v₁, hT1, hx1, hy1⟩ := hi
      obtain ⟨u₂, v₂, hT2, hx2, hy2⟩ := hj
      simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk] at hx1 hy1 hx2 hy2
      have hdiff : g u₁ - g v₁ = g u₂ - g v₂ := by
        calc g u₁ - g v₁ = (g u₁ + i) - (g v₁ + i) := by abel
          _ = x - y := by rw [hx1, hy1]
          _ = (g u₂ + j) - (g v₂ + j) := by rw [hx2, hy2]
          _ = g u₂ - g v₂ := by abel
      have hsym := hrain u₁ v₁ u₂ v₂ hT1 hT2 (Or.inl hdiff)
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : g u₁ + i = g u₁ + j := hx1.trans hx2.symm
        exact hij (add_left_cancel this)
      · have h1 : g u₁ + i = g v₁ + j := hx1.trans hx2.symm
        have h2 : g v₁ + i = g u₁ + j := hy1.trans hy2.symm
        have hadd : (g u₁ + g v₁) + (i + i) = (g u₁ + g v₁) + (j + j) := by
          calc (g u₁ + g v₁) + (i + i) = (g u₁ + i) + (g v₁ + i) := by abel
            _ = (g v₁ + j) + (g u₁ + j) := by rw [h1, h2]
            _ = (g u₁ + g v₁) + (j + j) := by abel
        exact hij (fin_odd_add_self_inj (add_left_cancel hadd))
  · apply le_antisymm le_top
    intro x y htop
    have hxy : x ≠ y := htop
    rw [SimpleGraph.iSup_adj]
    let col : Sym2 V → ℕ :=
      Sym2.lift ⟨fun u v => min (g u - g v).val (g v - g u).val, fun u v => min_comm _ _⟩
    have hsub : T.edgeFinset.image col ⊆ Finset.Icc 1 n := by
      intro c hc
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_edgeFinset, mem_edgeSet] at he
        have hne : g u ≠ g v := fun h => he.ne (g.injective h)
        have hsum := fin_sub_val_add_symm hne
        have h1 : 0 < (g u - g v).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hne (Fin.ext h))
        have h2 : 0 < (g v - g u).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hne.symm (Fin.ext h))
        simp only [col, Sym2.lift_mk, Finset.mem_Icc]
        omega
    have hinj : Set.InjOn col (T.edgeFinset : Set (Sym2 V)) := by
      intro e₁ he₁ e₂ he₂ hceq
      induction e₁ using Sym2.ind with
      | _ u₁ v₁ =>
        induction e₂ using Sym2.ind with
        | _ u₂ v₂ =>
          simp only [Finset.mem_coe, mem_edgeFinset, mem_edgeSet] at he₁ he₂
          simp only [col, Sym2.lift_mk] at hceq
          have h1 : g u₁ ≠ g v₁ := fun h => he₁.ne (g.injective h)
          have h2 : g u₂ ≠ g v₂ := fun h => he₂.ne (g.injective h)
          exact hrain u₁ v₁ u₂ v₂ he₁ he₂ (fin_nd_eq_iff h1 h2 hceq)
    have hcard_fin : T.edgeFinset.card = n := by
      rw [← Set.ncard_coe_finset, coe_edgeFinset]
      exact hcard
    have himg : T.edgeFinset.image col = Finset.Icc 1 n := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_image_of_injOn hinj, hcard_fin, Nat.card_Icc]
      omega
    have hmem : min (x - y).val (y - x).val ∈ T.edgeFinset.image col := by
      rw [himg, Finset.mem_Icc]
      have hsum := fin_sub_val_add_symm hxy
      have h1 : 0 < (x - y).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hxy (Fin.ext h))
      have h2 : 0 < (y - x).val := Nat.pos_of_ne_zero (fun h => sub_ne_zero.mpr hxy.symm (Fin.ext h))
      omega
    obtain ⟨e, he, hcol⟩ := Finset.mem_image.mp hmem
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      simp only [col, Sym2.lift_mk] at hcol
      have hguv : g u ≠ g v := fun h => he.ne (g.injective h)
      rcases fin_nd_eq_iff hguv hxy hcol with hd | hd
      · refine ⟨x - g u, ?_⟩
        rw [SimpleGraph.map_adj]
        refine ⟨u, v, he, ?_, ?_⟩
        · simp [f]
        · simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
          have : g v + (x - g u) = x - (g u - g v) := by abel
          rw [this, hd]; abel
      · refine ⟨x - g v, ?_⟩
        rw [SimpleGraph.map_adj]
        refine ⟨v, u, he.symm, ?_, ?_⟩
        · simp [f]
        · simp only [f, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
          have : g u + (x - g v) = x + (g u - g v) := by abel
          rw [this, hd]; abel

-- ============================================================================
-- SECTION 2: Longest-Path Characterization of Degree-≤-2 Trees
-- ============================================================================

private lemma walk_exists_boundary_edge {U : Type*} {G : SimpleGraph U} {s : Set U}
    {x y : U} (q : G.Walk x y) (hx : x ∉ s) (hy : y ∈ s) :
    ∃ a b : U, G.Adj a b ∧ a ∉ s ∧ b ∈ s := by
  induction q with
  | nil => exact absurd hy hx
  | @cons u v w hadj tail ih =>
    by_cases hv : v ∈ s
    · exact ⟨u, v, hadj, hx, hv⟩
    · exact ih hv hy

private lemma tree_maxDeg_le_two_hamiltonian {U : Type*} [Fintype U] [DecidableEq U]
    (C : SimpleGraph U) [DecidableRel C.Adj] (hC : C.IsTree) (hdeg : ∀ x, C.degree x ≤ 2) :
    ∃ f : Fin (Fintype.card U) → U,
      Function.Injective f ∧
      ∀ (i : ℕ) (hi : i + 1 < Fintype.card U),
        C.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
  have : Nonempty U := hC.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length C
  have hcov : ∀ w : U, w ∈ p.support := by
    intro w
    by_contra hw
    obtain ⟨q⟩ := hC.connected w u
    obtain ⟨a, b, hab, ha, hb⟩ :=
      walk_exists_boundary_edge (s := {z | z ∈ p.support}) q hw p.start_mem_support
    have hmem : b ∈ p.support := hb
    obtain ⟨i, hi_len, hi_eq⟩ := List.mem_iff_getElem.mp hmem
    have hlen_supp : p.support.length = p.length + 1 := p.length_support
    have hi_le : i ≤ p.length := by omega
    have hget : p.getVert i = b := by
      rw [Walk.getVert_eq_support_getElem p hi_le]
      exact hi_eq
    by_cases hi0 : i = 0
    · subst hi0
      have hbu : b = u := by simpa using hget.symm
      subst hbu
      have hp' : (Walk.cons hab p).IsPath := Walk.IsPath.cons hp ha
      have hle := hmax a v (Walk.cons hab p) hp'
      simp only [Walk.length_cons] at hle
      omega
    · by_cases hil : i = p.length
      · subst hil
        have hbv : b = v := by simpa [Walk.getVert_length] using hget.symm
        subst hbv
        have hp' : (p.concat hab.symm).IsPath := hp.concat ha hab.symm
        have hle := hmax u a (p.concat hab.symm) hp'
        simp only [Walk.length_concat] at hle
        omega
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
        have hi_lt : i < p.length := lt_of_le_of_ne hi_le hil
        let x₁ := p.getVert (i - 1)
        let x₂ := p.getVert (i + 1)
        have hadj1 : C.Adj b x₁ := by
          have h := p.adj_getVert_succ (by omega : i - 1 < p.length)
          have hidx : i - 1 + 1 = i := by omega
          rw [hidx, hget] at h
          exact h.symm
        have hadj2 : C.Adj b x₂ := by
          have h := p.adj_getVert_succ hi_lt
          rw [hget] at h
          exact h
        have hx1_mem : x₁ ∈ p.support := p.getVert_mem_support (i - 1)
        have hx2_mem : x₂ ∈ p.support := p.getVert_mem_support (i + 1)
        have ha1 : a ≠ x₁ := fun h => ha (h ▸ hx1_mem)
        have ha2 : a ≠ x₂ := fun h => ha (h ▸ hx2_mem)
        have h12 : x₁ ≠ x₂ := by
          intro heq
          have h1 : x₁ = p.support[i - 1]'(by omega) := p.getVert_eq_support_getElem (by omega)
          have h2 : x₂ = p.support[i + 1]'(by omega) := p.getVert_eq_support_getElem (by omega)
          rw [h1, h2] at heq
          have := (List.Nodup.getElem_inj_iff hp.support_nodup).mp heq
          omega
        have hsub : ({a, x₁, x₂} : Finset U) ⊆ C.neighborFinset b := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [mem_neighborFinset]
          rcases hz with rfl | rfl | rfl
          · exact hab.symm
          · exact hadj1
          · exact hadj2
        have hcard3 : ({a, x₁, x₂} : Finset U).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [h12]
          · simp [ha1, ha2]
        have hle2 := hdeg b
        rw [← card_neighborFinset_eq_degree] at hle2
        have := Finset.card_le_card hsub
        omega
  have htoFinset : p.support.toFinset = Finset.univ := by
    ext w
    simp [hcov w]
  have hcard_eq : p.length + 1 = Fintype.card U := by
    calc p.length + 1 = p.support.length := p.length_support.symm
      _ = p.support.toFinset.card := (List.toFinset_card_of_nodup hp.support_nodup).symm
      _ = Fintype.card U := by rw [htoFinset, Finset.card_univ]
  have hsupp_len : p.support.length = Fintype.card U := by
    rw [p.length_support, hcard_eq]
  refine ⟨fun j => p.getVert j.val, ?_, ?_⟩
  · intro j₁ j₂ hj
    dsimp only at hj
    have h1 : p.getVert j₁.val = p.support[j₁.val]'(by omega) :=
      p.getVert_eq_support_getElem (by omega)
    have h2 : p.getVert j₂.val = p.support[j₂.val]'(by omega) :=
      p.getVert_eq_support_getElem (by omega)
    rw [h1, h2] at hj
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp.support_nodup).mp hj)
  · intro i hi
    dsimp only
    exact p.adj_getVert_succ (by omega)
-- ============================================================================
-- The zigzag labelling of a path
-- ============================================================================

/-- The value of a difference of two labels at most `n` in `Fin (2 * n + 1)`. -/
lemma sub_val_cases {n : ℕ} (x y : Fin (2 * n + 1)) :
    (y ≤ x ∧ (x - y).val = x.val - y.val) ∨ (x < y ∧ (x - y).val = 2 * n + 1 + x.val - y.val) := by
  rcases le_or_gt y x with h | h
  · exact Or.inl ⟨h, Fin.coe_sub_iff_le.mpr h⟩
  · exact Or.inr ⟨h, Fin.coe_sub_iff_lt.mpr h⟩

/-- Two label pairs at most `n` whose differences agree up to sign have the same length. -/
lemma len_eq {n : ℕ} (x₁ y₁ x₂ y₂ : Fin (2 * n + 1))
    (hx₁ : x₁.val ≤ n) (hy₁ : y₁.val ≤ n) (hx₂ : x₂.val ≤ n) (hy₂ : y₂.val ≤ n)
    (h : x₁ - y₁ = x₂ - y₂ ∨ x₁ - y₁ = y₂ - x₂) :
    max x₁.val y₁.val - min x₁.val y₁.val = max x₂.val y₂.val - min x₂.val y₂.val := by
  have c1 := sub_val_cases x₁ y₁
  have c2 := sub_val_cases x₂ y₂
  have c3 := sub_val_cases y₂ x₂
  have l1 : y₁ ≤ x₁ ↔ y₁.val ≤ x₁.val := Fin.le_def
  have l2 : y₂ ≤ x₂ ↔ y₂.val ≤ x₂.val := Fin.le_def
  have l3 : x₁ < y₁ ↔ x₁.val < y₁.val := Fin.lt_def
  have l4 : x₂ < y₂ ↔ x₂.val < y₂.val := Fin.lt_def
  have l5 : x₂ ≤ y₂ ↔ x₂.val ≤ y₂.val := Fin.le_def
  have l6 : y₂ < x₂ ↔ y₂.val < x₂.val := Fin.lt_def
  rcases h with h | h <;> have hv := congrArg Fin.val h <;>
    rcases c1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases c2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
    rcases c3 with ⟨a3, b3⟩ | ⟨a3, b3⟩ <;> omega

/-- The zigzag label of the `k`-th vertex of a path with `n` edges. -/
lemma zig_spec (n k : ℕ) (hk : k < n) :
    max (if k % 2 = 0 then k / 2 else n - k / 2) (if (k + 1) % 2 = 0 then (k + 1) / 2 else n - (k + 1) / 2)
      - min (if k % 2 = 0 then k / 2 else n - k / 2)
          (if (k + 1) % 2 = 0 then (k + 1) / 2 else n - (k + 1) / 2) = n - k := by
  split_ifs <;> omega

theorem path_kotzig : ∀ {V : Type} [Finite V] (T : SimpleGraph V), T.IsTree →
    (∀ v, (T.neighborSet v).ncard ≤ 2) →
    ∀ (n : ℕ), T.edgeSet.ncard = n →
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      (∀ i v, f i v = f 0 v + i) ∧
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  intro V _ T hT hdeg n hn
  classical
  have : Fintype V := Fintype.ofFinite V
  have hcard_fin : T.edgeFinset.card = n := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
    exact hn
  have hVcard : Fintype.card V = n + 1 := by
    have := hT.card_edgeFinset
    omega
  have hdeg' : ∀ x, T.degree x ≤ 2 := by
    intro x
    have h := hdeg x
    rw [← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, coe_neighborFinset]
    exact h
  obtain ⟨f, hfinj, hfadj⟩ := tree_maxDeg_le_two_hamiltonian T hT hdeg'
  let F : Fin (n + 1) → V := fun k => f (Fin.cast hVcard.symm k)
  have hFinj : Function.Injective F := hfinj.comp (Fin.cast_injective _)
  have hFadj : ∀ k : Fin n, T.Adj (F k.castSucc) (F k.succ) := by
    intro k
    exact hfadj k.val (by omega)
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).2 ⟨hFinj, by simp [hVcard]⟩
  let e : Fin (n + 1) ≃ V := Equiv.ofBijective F hFbij
  have he : ∀ k, e.symm (F k) = k := fun k => (Equiv.ofBijective F hFbij).symm_apply_apply k
  let z : ℕ → ℕ := fun k => if k % 2 = 0 then k / 2 else n - k / 2
  have hz_le : ∀ k, k < n + 1 → z k ≤ n := by
    intro k hk
    simp only [z]
    split_ifs <;> omega
  have hz_inj : ∀ a b, a < n + 1 → b < n + 1 → z a = z b → a = b := by
    intro a b ha hb h
    simp only [z] at h
    split_ifs at h <;> omega
  let g : V ↪ Fin (2 * n + 1) :=
    ⟨fun v => ⟨z (e.symm v).val, by have := hz_le _ (e.symm v).isLt; omega⟩, by
      intro u v h
      simp only [Fin.mk.injEq] at h
      exact e.symm.injective (Fin.ext (hz_inj _ _ (e.symm u).isLt (e.symm v).isLt h))⟩
  have hgF : ∀ k, (g (F k)).val = z k.val := by
    intro k
    show z (e.symm (F k)).val = z k.val
    rw [he]
  -- the edges of `T` are exactly the path edges
  let P : Finset (Sym2 V) := Finset.univ.image (fun k : Fin n => s(F k.castSucc, F k.succ))
  have hPsub : P ⊆ T.edgeFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_edgeFinset, mem_edgeSet]
    exact hFadj k
  have hPcard : P.card = n := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro a b hab
    simp only at hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact Fin.castSucc_injective _ (hFinj h1)
    · have h1' := congrArg Fin.val (hFinj h1)
      have h2' := congrArg Fin.val (hFinj h2)
      simp only [Fin.val_castSucc, Fin.val_succ] at h1' h2'
      omega
  have hPeq : P = T.edgeFinset := Finset.eq_of_subset_of_card_le hPsub (by rw [hPcard, hcard_fin])
  have hedge : ∀ u v, T.Adj u v → ∃ k : Fin n, s(u, v) = s(F k.castSucc, F k.succ) := by
    intro u v huv
    have hmem : s(u, v) ∈ P := by
      rw [hPeq, mem_edgeFinset, mem_edgeSet]
      exact huv
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    exact ⟨k, hk.symm⟩
  -- the length of an edge determines it
  have hlen : ∀ u v, T.Adj u v → ∃ k : Fin n, s(u, v) = s(F k.castSucc, F k.succ) ∧
      max (g u).val (g v).val - min (g u).val (g v).val = n - k.val := by
    intro u v huv
    obtain ⟨k, hk⟩ := hedge u v huv
    refine ⟨k, hk, ?_⟩
    have hs := zig_spec n k.val k.isLt
    rw [Sym2.eq_iff] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hgF, hgF]
      simpa [z] using hs
    · rw [hgF, hgF, max_comm, min_comm]
      simpa [z] using hs
  have hrain : ∀ u₁ v₁ u₂ v₂, T.Adj u₁ v₁ → T.Adj u₂ v₂ →
      (g u₁ - g v₁ = g u₂ - g v₂ ∨ g u₁ - g v₁ = g v₂ - g u₂) →
      s(u₁, v₁) = s(u₂, v₂) := by
    intro u₁ v₁ u₂ v₂ h1 h2 hd
    obtain ⟨k₁, hk₁, hl₁⟩ := hlen u₁ v₁ h1
    obtain ⟨k₂, hk₂, hl₂⟩ := hlen u₂ v₂ h2
    have hb : ∀ w, (g w).val ≤ n := fun w => hz_le _ (e.symm w).isLt
    have hL := len_eq (g u₁) (g v₁) (g u₂) (g v₂) (hb _) (hb _) (hb _) (hb _) hd
    have hkk : k₁ = k₂ := by
      have := k₁.isLt
      have := k₂.isLt
      ext
      omega
    rw [hk₁, hk₂, hkk]
  exact rosa_kotzig_cyclic T hn g hrain

/-- Ringel for paths: forget that the decomposition is cyclic. -/
theorem path_ringel : OMA.R_RingelConjecture_ringel_conjecture_R1.H1 := by
  intro V _ T hT hdeg n hn
  obtain ⟨f, -, h2, h3⟩ := path_kotzig T hT hdeg n hn
  exact ⟨f, h2, h3⟩

end OMA.RingelPaths

theorem OMA.solution : OMA.R_RingelConjecture_ringel_conjecture_R1.H1 :=
  OMA.RingelPaths.path_ringel
