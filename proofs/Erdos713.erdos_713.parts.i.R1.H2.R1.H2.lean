import OMAReductions.R_Erdos713_erdos_713_parts_i_R1_H2_R1

/-!
# Proof of `Erdos713.erdos_713.parts.i.R1.H2.R1.H2`

Here `G` is a disconnected star forest (acyclic, no isolated vertices, every edge has an
endpoint of degree `≤ 1`, and some vertex has degree `≥ 3`).
Decomposing `G` into its `s ≥ 2` star components `K_{1, d_0} ⊔ ... ⊔ K_{1, d_{s-1}}` sorted
with `d_0 ≥ d_1 ≥ ... ≥ d_{s-1} ≥ 1`, let
`M^* = max_{0 ≤ k < s} (k + (d_k - 1) / 2)`.

We prove unconditionally:
1. **Upper bound**: `extremalNumber n G ≤ M^* * n + 8 * s * q^3` (split vertices of degree `≥ 2q`
   into at most `s - 1` hubs `B`, greedily bound medium-degree vertices outside `B`, and sum
   remaining degrees `≤ d_k - 1`).
2. **Lower bound**: for all large `m`, `K_k + Circulant(m - k, d_k - 1)` is `G`-free (by a
   pigeonhole argument on the `k + 1` largest stars) and has at least `M^* * m - (k + 1)^2` edges.

Together these show `extremalNumber n G / n → M^*`, immediately yielding the goal.
-/

-- Credit: @skhakim

open SimpleGraph Finset
open scoped Classical

private lemma sort_finset_by_deg {q : ℕ} (G : SimpleGraph (Fin q)) :
    ∀ (s : ℕ) (C : Finset (Fin q)), C.card = s →
      ∃ c : Fin s → Fin q, Function.Injective c ∧
        (∀ i, c i ∈ C) ∧ (∀ x ∈ C, ∃ i, c i = x) ∧
        (∀ i j : Fin s, i ≤ j → G.degree (c j) ≤ G.degree (c i)) := by
  intro s
  induction s with
  | zero =>
    intro C hC
    have hCe : C = ∅ := Finset.card_eq_zero.mp hC
    subst hCe
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun _ hx ↦ by simp at hx,
      fun i ↦ i.elim0⟩
  | succ k ih =>
    intro C hC
    have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v₀, hv₀C, hv₀max⟩ := Finset.exists_max_image C (fun v ↦ G.degree v) hCne
    let C' := C.erase v₀
    have hC'card : C'.card = k := by rw [Finset.card_erase_of_mem hv₀C, hC]; omega
    obtain ⟨c', hc'_inj, hc'_mem, hc'_surj, hc'_mono⟩ := ih C' hC'card
    let c : Fin (k + 1) → Fin q := Fin.cons v₀ c'
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · intro i j heq
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j' =>
          simp only [c, Fin.cons_zero, Fin.cons_succ] at heq
          exfalso
          have hmem := hc'_mem j'
          rw [← heq] at hmem
          exact (Finset.mem_erase.mp hmem).1 rfl
      | succ i' =>
        cases j using Fin.cases with
        | zero =>
          simp only [c, Fin.cons_zero, Fin.cons_succ] at heq
          exfalso
          have hmem := hc'_mem i'
          rw [heq] at hmem
          exact (Finset.mem_erase.mp hmem).1 rfl
        | succ j' =>
          simp only [c, Fin.cons_succ] at heq
          exact congr_arg Fin.succ (hc'_inj heq)
    · intro i
      cases i using Fin.cases with
      | zero => exact hv₀C
      | succ i' => exact (Finset.mem_erase.mp (hc'_mem i')).2
    · intro x hx
      by_cases hxv : x = v₀
      · subst hxv; exact ⟨0, rfl⟩
      · obtain ⟨i', hi'⟩ := hc'_surj x (Finset.mem_erase.mpr ⟨hxv, hx⟩)
        exact ⟨i'.succ, hi'⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact le_refl _
        | succ j' =>
          simp only [c]
          exact hv₀max (c' j') (Finset.mem_erase.mp (hc'_mem j')).2
      | succ i' =>
        cases j using Fin.cases with
        | zero => exact absurd hij (by simp)
        | succ j' =>
          simp only [c]
          exact hc'_mono i' j' (Fin.succ_le_succ_iff.mp hij)

private lemma star_forest_decomp {q : ℕ} {G : SimpleGraph (Fin q)}
    (hnoiso : ∀ v, ¬ G.IsIsolated v)
    (hstar : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) :
    ∃ (C : Finset (Fin q)),
      (∀ u ∈ C, ∀ w ∈ C, ¬ G.Adj u w) ∧
      (∀ u ∉ C, ∃! w, w ∈ C ∧ G.Adj u w) ∧
      (∀ u ∉ C, ∀ w ∉ C, ¬ G.Adj u w) := by
  let C : Finset (Fin q) := Finset.univ.filter fun v ↦
    2 ≤ G.degree v ∨ (G.degree v = 1 ∧ ∃ w, G.Adj v w ∧ G.degree w = 1 ∧ v < w)
  have hdeg_pos : ∀ v, 1 ≤ G.degree v := by
    intro v
    have hne : (G.neighborFinset v).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hnoiso v
      intro w hvw
      have : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).mpr hvw
      rw [hempty] at this
      exact Finset.notMem_empty w this
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr hne
  have hdeg1_uniq : ∀ v, G.degree v = 1 → ∃! w, G.Adj v w := by
    intro v hv
    have hcard : (G.neighborFinset v).card = 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hv
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
    refine ⟨w, (SimpleGraph.mem_neighborFinset G v w).mp (by rw [hw]; simp), fun u hu ↦ ?_⟩
    have hu' : u ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v u).mpr hu
    rw [hw, Finset.mem_singleton] at hu'
    exact hu'
  have hC_indep : ∀ u ∈ C, ∀ w ∈ C, ¬ G.Adj u w := by
    intro u hu w hw hadj
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
    rcases hu with hu2 | ⟨hu1, x, hux, _, hux_lt⟩
    · rcases hw with hw2 | ⟨hw1, y, hwy, hy1, _⟩
      · rcases hstar u w hadj with h | h <;> omega
      · obtain ⟨z, _, hz_uniq⟩ := hdeg1_uniq w hw1
        have h1 : u = z := hz_uniq u hadj.symm
        have h2 : y = z := hz_uniq y hwy
        rw [h1, ← h2] at hu2
        omega
    · rcases hw with hw2 | ⟨hw1, y, hwy, _, hwy_lt⟩
      · obtain ⟨z, _, hz_uniq⟩ := hdeg1_uniq u hu1
        have h1 : w = z := hz_uniq w hadj
        have h2 : x = z := hz_uniq x hux
        rw [h1, ← h2] at hw2
        omega
      · obtain ⟨z₁, _, hz₁⟩ := hdeg1_uniq u hu1
        obtain ⟨z₂, _, hz₂⟩ := hdeg1_uniq w hw1
        have hx : x = w := (hz₁ x hux).trans (hz₁ w hadj).symm
        have hy : y = u := (hz₂ y hwy).trans (hz₂ u hadj.symm).symm
        subst hx; subst hy
        exact lt_asymm hux_lt hwy_lt
  have hnotC_deg1 : ∀ u ∉ C, G.degree u = 1 := by
    intro u hu
    have hpos := hdeg_pos u
    by_contra hne
    apply hu
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    left; omega
  have hnotC_uniq : ∀ u ∉ C, ∃! w, w ∈ C ∧ G.Adj u w := by
    intro u hu
    have hu1 := hnotC_deg1 u hu
    obtain ⟨w, huw, hw_uniq⟩ := hdeg1_uniq u hu1
    have hwC : w ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hw2 : 2 ≤ G.degree w
      · exact Or.inl hw2
      · right
        have hw1 : G.degree w = 1 := by have := hdeg_pos w; omega
        refine ⟨hw1, u, huw.symm, hu1, ?_⟩
        rcases lt_trichotomy w u with hlt | heq | hgt
        · exact hlt
        · exact absurd heq huw.ne.symm
        · exfalso
          apply hu
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨hu1, w, huw, hw1, hgt⟩
    refine ⟨w, ⟨hwC, huw⟩, fun y ⟨_, huy⟩ ↦ hw_uniq y huy⟩
  have hnotC_indep : ∀ u ∉ C, ∀ w ∉ C, ¬ G.Adj u w := by
    intro u hu w hw hadj
    obtain ⟨z, ⟨hzC, huz⟩, hz_uniq⟩ := hnotC_uniq u hu
    have hu1 := hnotC_deg1 u hu
    obtain ⟨z', _, hz'_uniq⟩ := hdeg1_uniq u hu1
    have h1 : w = z := (hz'_uniq w hadj).trans (hz'_uniq z huz).symm
    subst h1
    exact hw hzC
  exact ⟨C, hC_indep, hnotC_uniq, hnotC_indep⟩

private lemma embed_star_forest {q s n : ℕ} {G : SimpleGraph (Fin q)} {H : SimpleGraph (Fin n)}
    {C : Finset (Fin q)} {c : Fin s → Fin q}
    (hc_inj : Function.Injective c)
    (hc_mem : ∀ i, c i ∈ C) (hc_surj : ∀ x ∈ C, ∃ i, c i = x)
    (hC_indep : ∀ u ∈ C, ∀ w ∈ C, ¬ G.Adj u w)
    (hnotC_uniq : ∀ u ∉ C, ∃! w, w ∈ C ∧ G.Adj u w)
    (hnotC_indep : ∀ u ∉ C, ∀ w ∉ C, ¬ G.Adj u w)
    (x : Fin s → Fin n) (hx_inj : Function.Injective x)
    (W : Fin s → Finset (Fin n))
    (hW_card : ∀ i, (W i).card = G.degree (c i))
    (hW_disj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hW_adj : ∀ i, ∀ y ∈ W i, H.Adj (x i) y)
    (hW_notx : ∀ i j, x j ∉ W i) :
    G ⊑ H := by
  have hequiv : ∀ i : Fin s, Nonempty ((G.neighborFinset (c i)) ≃ W i) := by
    intro i
    refine ⟨Fintype.equivOfCardEq ?_⟩
    rw [Fintype.card_coe, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree, hW_card i]
  let eqv : ∀ i : Fin s, (G.neighborFinset (c i)) ≃ W i := fun i ↦ Classical.choice (hequiv i)
  -- Every u ∉ C has a unique center index idx u : Fin s
  have hidx_ex : ∀ u : Fin q, u ∉ C → ∃ i : Fin s, G.Adj u (c i) := by
    intro u hu
    obtain ⟨w, ⟨hwC, huw⟩, _⟩ := hnotC_uniq u hu
    obtain ⟨i, rfl⟩ := hc_surj w hwC
    exact ⟨i, huw⟩
  let f : Fin q → Fin n := fun u ↦
    if hu : u ∈ C then x (Classical.choose (hc_surj u hu))
    else
      let i := Classical.choose (hidx_ex u hu)
      have hadj : G.Adj (c i) u := (Classical.choose_spec (hidx_ex u hu)).symm
      (eqv i ⟨u, (SimpleGraph.mem_neighborFinset G (c i) u).mpr hadj⟩).1
  have hf_center : ∀ i : Fin s, f (c i) = x i := by
    intro i
    have hmem := hc_mem i
    simp only [f, hmem, ↓reduceDIte]
    have hch := Classical.choose_spec (hc_surj (c i) hmem)
    rw [hc_inj hch]
  have hf_leaf : ∀ (i : Fin s) (u : Fin q), G.Adj (c i) u →
      u ∉ C ∧ f u ∈ W i ∧ ∀ j : Fin s, G.Adj (c j) u → j = i := by
    intro i u hiu
    have hu_notC : u ∉ C := fun huC ↦ hC_indep (c i) (hc_mem i) u huC hiu
    have huniq : ∀ j : Fin s, G.Adj (c j) u → j = i := by
      intro j hju
      obtain ⟨w, _, hw_uniq⟩ := hnotC_uniq u hu_notC
      have h1 : c j = w := hw_uniq (c j) ⟨hc_mem j, hju.symm⟩
      have h2 : c i = w := hw_uniq (c i) ⟨hc_mem i, hiu.symm⟩
      exact hc_inj (h1.trans h2.symm)
    refine ⟨hu_notC, ?_, huniq⟩
    simp only [f, hu_notC, ↓reduceDIte]
    have hi_eq : Classical.choose (hidx_ex u hu_notC) = i :=
      huniq _ (Classical.choose_spec (hidx_ex u hu_notC)).symm
    have hmemW := (eqv (Classical.choose (hidx_ex u hu_notC))
      ⟨u, (SimpleGraph.mem_neighborFinset G _ u).mpr
        (Classical.choose_spec (hidx_ex u hu_notC)).symm⟩).2
    rw [← hi_eq]
    exact hmemW
  have hf_inj : Function.Injective f := by
    intro u v huv
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C
    · obtain ⟨i, rfl⟩ := hc_surj u hu
      obtain ⟨j, rfl⟩ := hc_surj v hv
      rw [hf_center i, hf_center j] at huv
      rw [hx_inj huv]
    · obtain ⟨i, rfl⟩ := hc_surj u hu
      obtain ⟨j, hju⟩ := hidx_ex v hv
      have hfv := (hf_leaf j v hju.symm).2.1
      rw [hf_center i] at huv
      exact absurd (huv ▸ hfv) (hW_notx j i)
    · obtain ⟨j, rfl⟩ := hc_surj v hv
      obtain ⟨i, hiu⟩ := hidx_ex u hu
      have hfu := (hf_leaf i u hiu.symm).2.1
      rw [hf_center j] at huv
      exact absurd (huv.symm ▸ hfu) (hW_notx i j)
    · obtain ⟨i, hiu⟩ := hidx_ex u hu
      obtain ⟨j, hjv⟩ := hidx_ex v hv
      have hfu := (hf_leaf i u hiu.symm).2.1
      have hfv := (hf_leaf j v hjv.symm).2.1
      have hij : i = j := by
        by_contra hne
        exact Finset.disjoint_left.mp (hW_disj i j hne) hfu (huv ▸ hfv)
      subst hij
      have hci : Classical.choose (hidx_ex u hu) = i :=
        (hf_leaf i u hiu.symm).2.2 _ (Classical.choose_spec (hidx_ex u hu)).symm
      have hcj : Classical.choose (hidx_ex v hv) = i :=
        (hf_leaf i v hjv.symm).2.2 _ (Classical.choose_spec (hidx_ex v hv)).symm
      simp only [f, hu, hv, ↓reduceDIte] at huv
      have hmove : ∀ (j₁ j₂ : Fin s) (_h : j₁ = j₂) (z : Fin q)
          (hz1 : z ∈ G.neighborFinset (c j₁)) (hz2 : z ∈ G.neighborFinset (c j₂)),
          (eqv j₁ ⟨z, hz1⟩).1 = (eqv j₂ ⟨z, hz2⟩).1 := by
        rintro j₁ _ rfl z hz1 hz2; rfl
      have hu_nb : u ∈ G.neighborFinset (c i) := (SimpleGraph.mem_neighborFinset G _ _).mpr hiu.symm
      have hv_nb : v ∈ G.neighborFinset (c i) := (SimpleGraph.mem_neighborFinset G _ _).mpr hjv.symm
      have huv' : (eqv i ⟨u, hu_nb⟩).1 = (eqv i ⟨v, hv_nb⟩).1 := by
        rw [← hmove _ i hci u _ hu_nb, ← hmove _ i hcj v _ hv_nb]
        exact huv
      have heq_sub : eqv i ⟨u, hu_nb⟩ = eqv i ⟨v, hv_nb⟩ := Subtype.ext huv'
      exact congr_arg Subtype.val ((eqv i).injective heq_sub)
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro u v huv
  by_cases hu : u ∈ C
  · obtain ⟨i, rfl⟩ := hc_surj u hu
    rw [hf_center i]
    exact hW_adj i (f v) (hf_leaf i v huv).2.1
  · by_cases hv : v ∈ C
    · obtain ⟨i, rfl⟩ := hc_surj v hv
      rw [hf_center i]
      exact (hW_adj i (f u) (hf_leaf i u huv.symm).2.1).symm
    · exact absurd huv (hnotC_indep u hu v hv)

private lemma greedy_star_leaves {n k : ℕ} (H : SimpleGraph (Fin n))
    (x : Fin k → Fin n) (d : Fin k → ℕ) (U : Finset (Fin n))
    (hdeg : ∀ i : Fin k, U.card + (∑ j : Fin k, d j) ≤ (H.neighborFinset (x i)).card) :
    ∃ W : Fin k → Finset (Fin n),
      (∀ i, (W i).card = d i) ∧
      (∀ i, Disjoint (W i) U) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      (∀ i, ∀ y ∈ W i, H.Adj (x i) y) := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ m ih =>
    let x' : Fin m → Fin n := fun i ↦ x i.castSucc
    let d' : Fin m → ℕ := fun i ↦ d i.castSucc
    have hdeg' : ∀ i : Fin m, U.card + (∑ j : Fin m, d' j) ≤ (H.neighborFinset (x' i)).card := by
      intro i
      have hsum : (∑ j : Fin m, d' j) ≤ ∑ j : Fin (m + 1), d j := by
        rw [Fin.sum_univ_castSucc]
        exact Nat.le_add_right _ _
      exact (Nat.add_le_add_left hsum U.card).trans (hdeg i.castSucc)
    obtain ⟨W', hW'c, hW'U, hW'd, hW'a⟩ := ih x' d' hdeg'
    let used : Finset (Fin n) := U ∪ Finset.univ.biUnion W'
    have hused_le : used.card ≤ U.card + ∑ j : Fin m, d' j := by
      calc used.card ≤ U.card + (Finset.univ.biUnion W').card := Finset.card_union_le _ _
        _ ≤ U.card + ∑ j : Fin m, (W' j).card := Nat.add_le_add_left Finset.card_biUnion_le _
        _ = U.card + ∑ j : Fin m, d' j := by simp [hW'c]
    have havail : d (Fin.last m) ≤ ((H.neighborFinset (x (Fin.last m))) \ used).card := by
      have h1 := Finset.card_sdiff_add_card_inter (H.neighborFinset (x (Fin.last m))) used
      have h2 : (H.neighborFinset (x (Fin.last m)) ∩ used).card ≤ used.card :=
        Finset.card_le_card Finset.inter_subset_right
      have h3 := hdeg (Fin.last m)
      rw [Fin.sum_univ_castSucc] at h3
      have hd'_sum : ∑ j : Fin m, d' j = ∑ j : Fin m, d j.castSucc := rfl
      omega
    obtain ⟨Wlast, hWlast_sub, hWlast_card⟩ := Finset.exists_subset_card_eq havail
    let W : Fin (m + 1) → Finset (Fin n) := Fin.snoc W' Wlast
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [W] using hWlast_card
      | cast i' => simpa [W] using hW'c i'
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [W, Fin.snoc_last]
        exact (Finset.disjoint_sdiff.symm.mono_left hWlast_sub).mono_right Finset.subset_union_left
      | cast i' => simpa [W] using hW'U i'
    · intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j' =>
          simp only [W, Fin.snoc_last, Fin.snoc_castSucc]
          exact (Finset.disjoint_sdiff.symm.mono_left hWlast_sub).mono_right
            ((Finset.subset_biUnion_of_mem W' (Finset.mem_univ j')).trans Finset.subset_union_right)
      | cast i' =>
        cases j using Fin.lastCases with
        | last =>
          simp only [W, Fin.snoc_last, Fin.snoc_castSucc]
          exact ((Finset.disjoint_sdiff.symm.mono_left hWlast_sub).mono_right
            ((Finset.subset_biUnion_of_mem W' (Finset.mem_univ i')).trans Finset.subset_union_right)).symm
        | cast j' =>
          simp only [W, Fin.snoc_castSucc]
          exact hW'd i' j' (fun h ↦ hij (congr_arg Fin.castSucc h))
    · intro i y hy
      cases i using Fin.lastCases with
      | last =>
        simp only [W, Fin.snoc_last] at hy
        exact (SimpleGraph.mem_neighborFinset H _ y).mp (Finset.sdiff_subset (hWlast_sub hy))
      | cast i' =>
        simp only [W, Fin.snoc_castSucc] at hy
        exact hW'a i' y hy

private lemma greedy_disjoint_closed_nbhds {n m D : ℕ} (H : SimpleGraph (Fin n))
    (V' C' : Finset (Fin n)) (hCV : C' ⊆ V')
    (hmaxdeg : ∀ u ∈ V', (V'.filter (H.Adj u)).card ≤ D)
    (hC'big : m * (1 + D + D * D) < C'.card) :
    ∃ y : Fin m → Fin n, Function.Injective y ∧ (∀ i, y i ∈ C') ∧
      ∀ i j : Fin m, i ≠ j →
        Disjoint (insert (y i) (V'.filter (H.Adj (y i))))
                 (insert (y j) (V'.filter (H.Adj (y j)))) := by
  induction m with
  | zero =>
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ k ih =>
    have hlt : k * (1 + D + D * D) < C'.card := by
      calc k * (1 + D + D * D) ≤ (k + 1) * (1 + D + D * D) :=
            Nat.mul_le_mul_right _ (Nat.le_succ k)
        _ < C'.card := hC'big
    obtain ⟨y', hy'_inj, hy'_mem, hy'_disj⟩ := ih hlt
    let ball2 : Fin n → Finset (Fin n) := fun u ↦
      let N1 := V'.filter (H.Adj u)
      insert u (N1 ∪ N1.biUnion (fun z ↦ V'.filter (H.Adj z)))
    have hball2_card : ∀ u ∈ V', (ball2 u).card ≤ 1 + D + D * D := by
      intro u hu
      dsimp [ball2]
      let N1 := V'.filter (H.Adj u)
      have hN1 : N1.card ≤ D := hmaxdeg u hu
      have hN2 : (N1.biUnion (fun z ↦ V'.filter (H.Adj z))).card ≤ D * D := by
        calc (N1.biUnion (fun z ↦ V'.filter (H.Adj z))).card
            ≤ ∑ z ∈ N1, (V'.filter (H.Adj z)).card := Finset.card_biUnion_le
          _ ≤ ∑ _z ∈ N1, D := Finset.sum_le_sum fun z hz ↦ hmaxdeg z (Finset.mem_filter.mp hz).1
          _ = N1.card * D := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ D * D := Nat.mul_le_mul_right D hN1
      calc (insert u (N1 ∪ N1.biUnion (fun z ↦ V'.filter (H.Adj z)))).card
          ≤ 1 + (N1 ∪ N1.biUnion (fun z ↦ V'.filter (H.Adj z))).card := by
              have := Finset.card_insert_le u (N1 ∪ N1.biUnion (fun z ↦ V'.filter (H.Adj z)))
              omega
        _ ≤ 1 + (N1.card + (N1.biUnion (fun z ↦ V'.filter (H.Adj z))).card) :=
              Nat.add_le_add_left (Finset.card_union_le _ _) 1
        _ ≤ 1 + D + D * D := by omega
    let forb : Finset (Fin n) := Finset.univ.biUnion (fun i : Fin k ↦ ball2 (y' i))
    have hforb_lt : forb.card < C'.card := by
      have h1 : forb.card ≤ ∑ i : Fin k, (ball2 (y' i)).card := Finset.card_biUnion_le
      have h2 : ∑ i : Fin k, (ball2 (y' i)).card ≤ k * (1 + D + D * D) := by
        calc ∑ i : Fin k, (ball2 (y' i)).card
            ≤ ∑ _i : Fin k, (1 + D + D * D) :=
              Finset.sum_le_sum fun i _ ↦ hball2_card (y' i) (hCV (hy'_mem i))
          _ = k * (1 + D + D * D) := by simp
      have h3 : k * (1 + D + D * D) < C'.card := hlt
      omega
    obtain ⟨ylast, hylast_C', hylast_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hforb_lt
    have hdisj_last : ∀ i : Fin k,
        Disjoint (insert ylast (V'.filter (H.Adj ylast)))
                 (insert (y' i) (V'.filter (H.Adj (y' i)))) := by
      intro i
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      apply hylast_not
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp only [ball2, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_filter] at hz1 hz2 ⊢
      rcases hz1 with rfl | ⟨hzV, hyl_z⟩
      · rcases hz2 with rfl | ⟨_, hyi_z⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hCV hylast_C', hyi_z⟩)
      · rcases hz2 with rfl | ⟨_, hyi_z⟩
        · exact Or.inr (Or.inl ⟨hCV hylast_C', hyl_z.symm⟩)
        · exact Or.inr (Or.inr ⟨z, ⟨hzV, hyi_z⟩, hCV hylast_C', hyl_z.symm⟩)
    let y : Fin (k + 1) → Fin n := Fin.snoc y' ylast
    refine ⟨y, ?_, ?_, ?_⟩
    · intro i j heq
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j' =>
          simp only [y, Fin.snoc_last, Fin.snoc_castSucc] at heq
          exfalso
          exact Finset.disjoint_left.mp (hdisj_last j') (Finset.mem_insert_self _ _)
            (heq ▸ Finset.mem_insert_self _ _)
      | cast i' =>
        cases j using Fin.lastCases with
        | last =>
          simp only [y, Fin.snoc_last, Fin.snoc_castSucc] at heq
          exfalso
          exact Finset.disjoint_left.mp (hdisj_last i') (Finset.mem_insert_self _ _)
            (heq.symm ▸ Finset.mem_insert_self _ _)
        | cast j' =>
          simp only [y, Fin.snoc_castSucc] at heq
          exact congr_arg Fin.castSucc (hy'_inj heq)
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [y] using hylast_C'
      | cast i' => simpa [y] using hy'_mem i'
    · intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j' => simpa [y] using hdisj_last j'
      | cast i' =>
        cases j using Fin.lastCases with
        | last => simpa [y] using (hdisj_last i').symm
        | cast j' => simpa [y] using hy'_disj i' j' (fun h ↦ hij (congr_arg Fin.castSucc h))

private lemma circulant_exists_deg_le (m' r : ℕ) (hm' : r + 2 ≤ m') :
    ∃ R : SimpleGraph (Fin m'),
      (∀ v : Fin m', R.degree v ≤ r) ∧
      r * m' - 1 ≤ 2 * #R.edgeFinset := by
  let h : ℕ := r / 2
  let half : ℕ := m' / 2
  let adjCirc : Fin m' → Fin m' → Prop := fun a b ↦
    let d := (a.val + m' - b.val) % m'
    (1 ≤ d ∧ d ≤ h) ∨ (m' - h ≤ d ∧ d ≤ m' - 1) ∨
    (r % 2 = 1 ∧ ((a.val < half ∧ b.val = a.val + half) ∨
                  (b.val < half ∧ a.val = b.val + half)))
  have hsymm : ∀ a b, adjCirc a b → adjCirc b a := by
    intro a b hab
    dsimp only [adjCirc] at hab ⊢
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hodd, hmatch⟩
    · right; left
      have hba : (b.val + m' - a.val) % m' = m' - ((a.val + m' - b.val) % m') := by
        by_cases hlt : a.val < b.val
        · have h1' : (a.val + m' - b.val) % m' = a.val + m' - b.val :=
            Nat.mod_eq_of_lt (by omega)
          have h2' : (b.val + m' - a.val) % m' = b.val - a.val := by
            have : b.val + m' - a.val = (b.val - a.val) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · have hne : a.val ≠ b.val := by
            intro heq; rw [heq] at h1
            have : (b.val + m' - b.val) % m' = 0 := by
              have : b.val + m' - b.val = m' := by omega
              rw [this, Nat.mod_self]
            omega
          have h1' : (a.val + m' - b.val) % m' = a.val - b.val := by
            have : a.val + m' - b.val = (a.val - b.val) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have h2' : (b.val + m' - a.val) % m' = b.val + m' - a.val :=
            Nat.mod_eq_of_lt (by omega)
          omega
      omega
    · left
      have hba : (b.val + m' - a.val) % m' = m' - ((a.val + m' - b.val) % m') := by
        by_cases hlt : a.val < b.val
        · have h1' : (a.val + m' - b.val) % m' = a.val + m' - b.val :=
            Nat.mod_eq_of_lt (by omega)
          have h2' : (b.val + m' - a.val) % m' = b.val - a.val := by
            have : b.val + m' - a.val = (b.val - a.val) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · have hne : a.val ≠ b.val := by
            intro heq; rw [heq] at h1
            have : (b.val + m' - b.val) % m' = 0 := by
              have : b.val + m' - b.val = m' := by omega
              rw [this, Nat.mod_self]
            omega
          have h1' : (a.val + m' - b.val) % m' = a.val - b.val := by
            have : a.val + m' - b.val = (a.val - b.val) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have h2' : (b.val + m' - a.val) % m' = b.val + m' - a.val :=
            Nat.mod_eq_of_lt (by omega)
          omega
      omega
    · right; right; exact ⟨hodd, hmatch.symm⟩
  have hloopless : ∀ a, ¬ adjCirc a a := by
    intro a ha
    dsimp only [adjCirc] at ha
    have h0 : (a.val + m' - a.val) % m' = 0 := by
      have : a.val + m' - a.val = m' := by omega
      rw [this, Nat.mod_self]
    rw [h0] at ha
    rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, ⟨_, h2⟩ | ⟨_, h2⟩⟩ <;> omega
  let R : SimpleGraph (Fin m') := ⟨adjCirc, ⟨hsymm⟩, ⟨hloopless⟩⟩
  have hm'_pos : 0 < m' := by omega
  have hhalf_gt : h < half := by omega
  have hdeg_exact : ∀ a : Fin m',
      R.degree a = 2 * h + (if r % 2 = 1 ∧ a.val < 2 * half then 1 else 0) := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let S1 : Finset (Fin m') := (Finset.Icc 1 h).attach.image fun j ↦
      ⟨(a.val + m' - j.1) % m', Nat.mod_lt _ hm'_pos⟩
    let S2 : Finset (Fin m') := (Finset.Icc 1 h).attach.image fun j ↦
      ⟨(a.val + j.1) % m', Nat.mod_lt _ hm'_pos⟩
    let S3 : Finset (Fin m') :=
      if hcond : r % 2 = 1 ∧ a.val < 2 * half then
        if hlt : a.val < half then {⟨a.val + half, by omega⟩}
        else {⟨a.val - half, by omega⟩}
      else ∅
    have hS1_card : S1.card = h := by
      have hinj : Function.Injective (fun j : {x // x ∈ Finset.Icc 1 h} ↦
          (⟨(a.val + m' - j.1) % m', Nat.mod_lt _ hm'_pos⟩ : Fin m')) := by
        intro j₁ j₂ heq
        have h1 := Finset.mem_Icc.mp j₁.2
        have h2 := Finset.mem_Icc.mp j₂.2
        have hv : (a.val + m' - j₁.1) % m' = (a.val + m' - j₂.1) % m' := congr_arg Fin.val heq
        have hdiff : ∀ x : ℕ, 1 ≤ x → x ≤ h →
            (a.val + m' - x) % m' = if x ≤ a.val then a.val - x else a.val + m' - x := by
          intro x hx1 hx2
          split_ifs with hxa
          · have : a.val + m' - x = (a.val - x) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · exact Nat.mod_eq_of_lt (by omega)
        rw [hdiff j₁.1 h1.1 h1.2, hdiff j₂.1 h2.1 h2.2] at hv
        split_ifs at hv <;> exact Subtype.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
      simp
    have hS2_card : S2.card = h := by
      have hinj : Function.Injective (fun j : {x // x ∈ Finset.Icc 1 h} ↦
          (⟨(a.val + j.1) % m', Nat.mod_lt _ hm'_pos⟩ : Fin m')) := by
        intro j₁ j₂ heq
        have h1 := Finset.mem_Icc.mp j₁.2
        have h2 := Finset.mem_Icc.mp j₂.2
        have hv : (a.val + j₁.1) % m' = (a.val + j₂.1) % m' := congr_arg Fin.val heq
        have hsum : ∀ x : ℕ, 1 ≤ x → x ≤ h →
            (a.val + x) % m' = if a.val + x < m' then a.val + x else a.val + x - m' := by
          intro x hx1 hx2
          split_ifs with hlt
          · exact Nat.mod_eq_of_lt hlt
          · have ha_lt := a.isLt
            have hh_le : h < m' := by dsimp only [h]; omega
            have hadd : a.val + x = (a.val + x - m') + m' := by omega
            conv_lhs => rw [hadd]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hsum j₁.1 h1.1 h1.2, hsum j₂.1 h2.1 h2.2] at hv
        split_ifs at hv <;> exact Subtype.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
      simp
    have hS3_card : S3.card = if r % 2 = 1 ∧ a.val < 2 * half then 1 else 0 := by
      dsimp [S3]
      split_ifs <;> simp
    have hdist_S1 : ∀ b ∈ S1, 1 ≤ (a.val + m' - b.val) % m' ∧ (a.val + m' - b.val) % m' ≤ h := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨⟨j, hj⟩, _, rfl⟩ := hb
      rw [Finset.mem_Icc] at hj
      have heq : (a.val + m' - (a.val + m' - j) % m') % m' = j := by
        by_cases hja : j ≤ a.val
        · have h1 : (a.val + m' - j) % m' = a.val - j := by
            have : a.val + m' - j = (a.val - j) + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have : a.val + m' - (a.val - j) = j + m' := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · have h1 : (a.val + m' - j) % m' = a.val + m' - j := Nat.mod_eq_of_lt (by omega)
          rw [h1]
          have : a.val + m' - (a.val + m' - j) = j := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [heq]; exact hj
    have hdist_S2 : ∀ b ∈ S2, m' - h ≤ (a.val + m' - b.val) % m' ∧ (a.val + m' - b.val) % m' ≤ m' - 1 := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨⟨j, hj⟩, _, rfl⟩ := hb
      rw [Finset.mem_Icc] at hj
      have heq : (a.val + m' - (a.val + j) % m') % m' = m' - j := by
        by_cases hlt : a.val + j < m'
        · rw [Nat.mod_eq_of_lt hlt]
          have : a.val + m' - (a.val + j) = m' - j := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        · have h1 : (a.val + j) % m' = a.val + j - m' := by
            have ha_lt := a.isLt
            have hh_le : h < m' := by dsimp only [h]; omega
            have hadd : a.val + j = (a.val + j - m') + m' := by omega
            conv_lhs => rw [hadd]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have : a.val + m' - (a.val + j - m') = (m' - j) + m' := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [heq]; omega
    have hdist_S3 : ∀ b ∈ S3, (a.val + m' - b.val) % m' = half ∨ (a.val + m' - b.val) % m' = m' - half := by
      intro b hb
      dsimp [S3] at hb
      split_ifs at hb with hcond hlt
      · rw [Finset.mem_singleton] at hb; subst hb
        right
        have : a.val + m' - (a.val + half) = m' - half := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      · rw [Finset.mem_singleton] at hb; subst hb
        left
        have : a.val + m' - (a.val - half) = half + m' := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact absurd hb (Finset.notMem_empty b)
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro b h1 h2
      have d1 := hdist_S1 b h1; have d2 := hdist_S2 b h2; omega
    have hd13 : Disjoint S1 S3 := by
      rw [Finset.disjoint_left]; intro b h1 h3
      have d1 := hdist_S1 b h1; have d3 := hdist_S3 b h3; omega
    have hd23 : Disjoint S2 S3 := by
      rw [Finset.disjoint_left]; intro b h2 h3
      have d2 := hdist_S2 b h2; have d3 := hdist_S3 b h3; omega
    have hnb_eq : R.neighborFinset a = (S1 ∪ S2) ∪ S3 := by
      ext b
      rw [SimpleGraph.mem_neighborFinset]
      simp only [R, adjCirc, Finset.mem_union]
      constructor
      · intro hab
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hodd, hmatch⟩
        · left; left
          rw [Finset.mem_image]
          let j := (a.val + m' - b.val) % m'
          refine ⟨⟨j, Finset.mem_Icc.mpr ⟨h1, h2⟩⟩, Finset.mem_attach _ _, Fin.ext ?_⟩
          dsimp only
          by_cases hlt : a.val < b.val
          · have hj : j = a.val + m' - b.val := Nat.mod_eq_of_lt (by omega)
            have : a.val + m' - j = b.val := by omega
            rw [this, Nat.mod_eq_of_lt b.isLt]
          · have hj : j = a.val - b.val := by
              have : a.val + m' - b.val = (a.val - b.val) + m' := by omega
              dsimp [j]; rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have : a.val + m' - j = b.val + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
        · left; right
          rw [Finset.mem_image]
          let j := m' - (a.val + m' - b.val) % m'
          refine ⟨⟨j, Finset.mem_Icc.mpr (by omega)⟩, Finset.mem_attach _ _, Fin.ext ?_⟩
          dsimp only
          by_cases hlt : a.val < b.val
          · have hj : j = b.val - a.val := by
              have : (a.val + m' - b.val) % m' = a.val + m' - b.val := Nat.mod_eq_of_lt (by omega)
              omega
            have : a.val + j = b.val := by omega
            rw [this, Nat.mod_eq_of_lt b.isLt]
          · have hj : j = m' - (a.val - b.val) := by
              have : (a.val + m' - b.val) % m' = a.val - b.val := by
                have : a.val + m' - b.val = (a.val - b.val) + m' := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              omega
            have : a.val + j = b.val + m' := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]
        · right
          dsimp only [S3]
          rcases hmatch with ⟨ha_lt, hb_eq⟩ | ⟨hb_lt, ha_eq⟩
          · have hcond : r % 2 = 1 ∧ a.val < 2 * half := ⟨hodd, by omega⟩
            rw [dif_pos hcond, dif_pos ha_lt, Finset.mem_singleton]
            exact Fin.ext hb_eq
          · have hcond : r % 2 = 1 ∧ a.val < 2 * half := ⟨hodd, by omega⟩
            have ha_not : ¬ a.val < half := by omega
            rw [dif_pos hcond, dif_neg ha_not, Finset.mem_singleton]
            exact Fin.ext (by dsimp only; omega)
      · rintro ((hb1 | hb2) | hb3)
        · exact Or.inl (hdist_S1 b hb1)
        · exact Or.inr (Or.inl (hdist_S2 b hb2))
        · right; right
          dsimp only [S3] at hb3
          split_ifs at hb3 with hcond hlt
          · rw [Finset.mem_singleton] at hb3; subst hb3
            exact ⟨hcond.1, Or.inl ⟨hlt, rfl⟩⟩
          · rw [Finset.mem_singleton] at hb3; subst hb3
            exact ⟨hcond.1, Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩⟩
          · exact absurd hb3 (Finset.notMem_empty b)
    rw [hnb_eq, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
      Finset.card_union_of_disjoint hd12, hS1_card, hS2_card, hS3_card]
    omega
  have hdeg_le : ∀ v : Fin m', R.degree v ≤ r := by
    intro v
    rw [hdeg_exact v]
    split_ifs <;> omega
  have hedge_ge : r * m' - 1 ≤ 2 * #R.edgeFinset := by
    have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges R
    rw [← hhand]
    simp_rw [hdeg_exact]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    by_cases hodd : r % 2 = 1
    · have hsum_ind : ∑ v : Fin m', (if r % 2 = 1 ∧ v.val < 2 * half then 1 else 0) = 2 * half := by
        have hfilt : (Finset.univ.filter (fun v : Fin m' ↦ r % 2 = 1 ∧ v.val < 2 * half)).card = 2 * half := by
          rw [← Finset.card_range (2 * half)]
          refine Finset.card_bij (fun (v : Fin m') _ ↦ v.val) ?_ ?_ ?_
          · intro v hv; simp at hv; exact Finset.mem_range.mpr hv.2
          · intro v₁ _ v₂ _ h; exact Fin.ext h
          · intro x hx
            rw [Finset.mem_range] at hx
            exact ⟨⟨x, by omega⟩, by simp [hodd, hx], rfl⟩
        rw [← Finset.card_filter, hfilt]
      rw [hsum_ind]
      have hr : r = 2 * h + 1 := by omega
      have hm2 : m' - 1 ≤ 2 * half := by omega
      have : r * m' = m' * (2 * h) + m' := by rw [hr]; ring
      omega
    · have hr : r = 2 * h := by omega
      have : r * m' = m' * (2 * h) := by rw [hr]; ring
      omega
  refine ⟨R, fun v ↦ ?_, ?_⟩
  · convert hdeg_le v
  · convert hedge_ge

theorem OMA.solution : OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1.H2 := by
  intro q G _ _ _ hnoiso hnotconn _ hex3 hstar a b hab hlim
  obtain ⟨v₃, hv₃⟩ := hex3
  have hq_pos : 0 < q := Fin.pos v₃
  -- Re-prove C.Nonempty cleanly using hq_pos (avoiding sorry in helper!)
  obtain ⟨C, hC_indep, hnotC_uniq, hnotC_indep⟩ := star_forest_decomp hnoiso hstar
  have hCne : C.Nonempty := by
    by_cases hv : v₃ ∈ C
    · exact ⟨v₃, hv⟩
    · obtain ⟨w, ⟨hwC, _⟩, _⟩ := hnotC_uniq v₃ hv
      exact ⟨w, hwC⟩
  let s := C.card
  have hs_pos : 0 < s := Finset.card_pos.mpr hCne
  obtain ⟨c, hc_inj, hc_mem, hc_surj, hc_mono⟩ := sort_finset_by_deg G s C rfl
  let d : Fin s → ℕ := fun i ↦ G.degree (c i)
  have hd_pos : ∀ i : Fin s, 1 ≤ d i := by
    intro i
    have hne : (G.neighborFinset (c i)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hnoiso (c i)
      intro w hw
      have := (SimpleGraph.mem_neighborFinset G (c i) w).mpr hw
      rw [hempty] at this
      exact Finset.notMem_empty w this
    dsimp only [d]
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr hne
  have hsum_d_le : s + ∑ i : Fin s, d i ≤ q := by
    have hdisj_all : ∀ i j : Fin s, i ≠ j →
        Disjoint (G.neighborFinset (c i)) (G.neighborFinset (c j)) := by
      intro i j hij
      rw [Finset.disjoint_left]
      intro u hui huj
      have h1 := (SimpleGraph.mem_neighborFinset G (c i) u).mp hui
      have h2 := (SimpleGraph.mem_neighborFinset G (c j) u).mp huj
      have hu_notC : u ∉ C := fun huC ↦ hC_indep (c i) (hc_mem i) u huC h1
      obtain ⟨w, _, hw_uniq⟩ := hnotC_uniq u hu_notC
      have e1 : c i = w := hw_uniq (c i) ⟨hc_mem i, h1.symm⟩
      have e2 : c j = w := hw_uniq (c j) ⟨hc_mem j, h2.symm⟩
      exact hij (hc_inj (e1.trans e2.symm))
    have hdisj_C : Disjoint C (Finset.univ.biUnion (fun i : Fin s ↦ G.neighborFinset (c i))) := by
      rw [Finset.disjoint_left]
      intro u huC huN
      rw [Finset.mem_biUnion] at huN
      obtain ⟨i, _, hui⟩ := huN
      exact hC_indep (c i) (hc_mem i) u huC ((SimpleGraph.mem_neighborFinset G (c i) u).mp hui)
    have hcard_union := Finset.card_union_of_disjoint hdisj_C
    have hcard_bi : (Finset.univ.biUnion (fun i : Fin s ↦ G.neighborFinset (c i))).card =
        ∑ i : Fin s, d i := by
      rw [Finset.card_biUnion (fun i _ j _ hij ↦ hdisj_all i j hij)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact SimpleGraph.card_neighborFinset_eq_degree G (c i)
    have hle : (C ∪ Finset.univ.biUnion (fun i : Fin s ↦ G.neighborFinset (c i))).card ≤ q :=
      (Finset.card_le_univ _).trans (by simp)
    omega
  let val : Fin s → ℚ := fun k ↦ (k.val : ℚ) + ((d k - 1 : ℕ) : ℚ) / 2
  have huniv_ne : (Finset.univ : Finset (Fin s)).Nonempty :=
    ⟨⟨0, hs_pos⟩, Finset.mem_univ _⟩
  obtain ⟨k₀, _, hk₀_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin s)) val huniv_ne
  let Mstar : ℚ := val k₀
  -- Step 1: Upper bound on extremalNumber n G
  have hupper : ∀ n : ℕ, (extremalNumber n G : ℚ) ≤ Mstar * (n : ℚ) + (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ) := by
    intro n
    have hnat : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], G.Free H →
        (#H.edgeFinset : ℚ) ≤ Mstar * (n : ℚ) + (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ) := by
      intro H _ hGfree
      let B : Finset (Fin n) := Finset.univ.filter (fun u ↦ 2 * q ≤ H.degree u)
      have hB_lt : B.card < s := by
        by_contra hge
        push Not at hge
        obtain ⟨B0, hB0_sub, hB0_card⟩ := Finset.exists_subset_card_eq hge
        let eB0 : Fin s ≃ B0 := Fintype.equivOfCardEq (by simp [hB0_card])
        let x : Fin s → Fin n := fun i ↦ (eB0 i).1
        have hx_inj : Function.Injective x := fun i j h ↦ eB0.injective (Subtype.ext h)
        have hdeg_x : ∀ i : Fin s, B0.card + (∑ j : Fin s, d j) ≤ (H.neighborFinset (x i)).card := by
          intro i
          rw [SimpleGraph.card_neighborFinset_eq_degree, hB0_card]
          have hxB := hB0_sub (eB0 i).2
          rw [Finset.mem_filter] at hxB
          dsimp only [x]
          omega
        obtain ⟨W, hWc, hWU, hWd, hWa⟩ :=
          greedy_star_leaves H x d B0 (fun i ↦ (hdeg_x i).trans_eq (congr_arg Finset.card (by ext w; simp)))
        apply hGfree
        exact embed_star_forest hc_inj hc_mem hc_surj hC_indep hnotC_uniq hnotC_indep
          x hx_inj W hWc hWd hWa (fun i j hmem ↦ Finset.disjoint_left.mp (hWU i) hmem (eB0 j).2)
      let k : ℕ := B.card
      let kfin : Fin s := ⟨k, hB_lt⟩
      let r : ℕ := d kfin
      let V' : Finset (Fin n) := Finset.univ \ B
      let C' : Finset (Fin n) := V'.filter (fun u ↦ r ≤ (V'.filter (H.Adj u)).card)
      have hV'_maxdeg : ∀ u ∈ V', (V'.filter (H.Adj u)).card ≤ 2 * q := by
        intro u hu
        have hu_notB : u ∉ B := (Finset.mem_sdiff.mp hu).2
        have hdeg_lt : H.degree u < 2 * q := by
          by_contra hge; push Not at hge
          exact hu_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hge⟩)
        have hsub : V'.filter (H.Adj u) ⊆ H.neighborFinset u := by
          intro w hw
          exact (SimpleGraph.mem_neighborFinset H u w).mpr (Finset.mem_filter.mp hw).2
        have hle := (Finset.card_le_card hsub).trans (le_of_eq (SimpleGraph.card_neighborFinset_eq_degree H u))
        omega
      have hC'_le : C'.card ≤ (s - k) * (1 + 2 * q + 2 * q * (2 * q)) := by
        by_contra hgt
        push Not at hgt
        obtain ⟨y, hy_inj, hy_mem, hy_disj⟩ :=
          greedy_disjoint_closed_nbhds H V' C' (Finset.filter_subset _ _)
            (fun u hu ↦ le_trans (le_of_eq (congr_arg Finset.card (by ext w; simp))) (hV'_maxdeg u hu)) hgt
        -- For j < s - k, pick d (k + j) neighbors of y j inside V'
        have hW_tail_ex : ∀ j : Fin (s - k),
            ∃ T ⊆ V'.filter (H.Adj (y j)), T.card = d ⟨k + j.val, by omega⟩ := by
          intro j
          have hyC' := hy_mem j
          rw [Finset.mem_filter] at hyC'
          have hd_le : d ⟨k + j.val, by omega⟩ ≤ r := hc_mono kfin ⟨k + j.val, by omega⟩ (by show k ≤ k + j.val; omega)
          exact Finset.exists_subset_card_eq (hd_le.trans hyC'.2)
        choose Wtail hWtail_sub hWtail_card using hW_tail_ex
        let U : Finset (Fin n) := B ∪ Finset.univ.biUnion (fun j : Fin (s - k) ↦ insert (y j) (Wtail j))
        have hU_card : U.card ≤ k + (s - k) + ∑ j : Fin (s - k), d ⟨k + j.val, by omega⟩ := by
          have h1 : U.card ≤ B.card + (Finset.univ.biUnion (fun j : Fin (s - k) ↦ insert (y j) (Wtail j))).card :=
            Finset.card_union_le _ _
          have h2 : (Finset.univ.biUnion (fun j : Fin (s - k) ↦ insert (y j) (Wtail j))).card ≤
              ∑ j : Fin (s - k), (insert (y j) (Wtail j)).card := Finset.card_biUnion_le
          have h3 : ∑ j : Fin (s - k), (insert (y j) (Wtail j)).card ≤
              (s - k) + ∑ j : Fin (s - k), d ⟨k + j.val, by omega⟩ := by
            calc ∑ j : Fin (s - k), (insert (y j) (Wtail j)).card
                ≤ ∑ j : Fin (s - k), (1 + (Wtail j).card) := by
                    refine Finset.sum_le_sum fun j _ ↦ ?_
                    have := Finset.card_insert_le (y j) (Wtail j); omega
              _ = (s - k) + ∑ j : Fin (s - k), d ⟨k + j.val, by omega⟩ := by
                    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                      smul_eq_mul, mul_one]
                    simp [hWtail_card]
          omega
        let eB : Fin k ≃ B := Fintype.equivOfCardEq (by simp [k])
        let xhead : Fin k → Fin n := fun i ↦ (eB i).1
        let dhead : Fin k → ℕ := fun i ↦ d ⟨i.val, by omega⟩
        have hsum_split : (∑ i : Fin k, dhead i) + (∑ j : Fin (s - k), d ⟨k + j.val, by omega⟩) =
            ∑ i : Fin s, d i := by
          let fsum : Fin s ≃ Fin k ⊕ Fin (s - k) :=
            (finCongr (by omega : s = k + (s - k))).trans finSumFinEquiv.symm
          rw [← Equiv.sum_comp fsum.symm]
          rw [Fintype.sum_sum_type]
          refine congr_arg₂ (· + ·) ?_ ?_
          · refine Finset.sum_congr rfl fun i _ ↦ ?_
            dsimp [fsum, dhead]; congr 1
          · refine Finset.sum_congr rfl fun j _ ↦ ?_
            dsimp [fsum]; congr 1
        have hdeg_head : ∀ i : Fin k, U.card + ∑ j : Fin k, dhead j ≤ (H.neighborFinset (xhead i)).card := by
          intro i
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          have hxB := (eB i).2
          rw [Finset.mem_filter] at hxB
          dsimp only [xhead]
          omega
        obtain ⟨Whead, hWhead_c, hWhead_U, hWhead_d, hWhead_a⟩ :=
          greedy_star_leaves H xhead dhead U (fun i ↦ (hdeg_head i).trans_eq (congr_arg Finset.card (by ext w; simp)))
        let x : Fin s → Fin n := fun i ↦
          if h : i.val < k then xhead ⟨i.val, h⟩ else y ⟨i.val - k, by omega⟩
        let W : Fin s → Finset (Fin n) := fun i ↦
          if h : i.val < k then Whead ⟨i.val, h⟩ else Wtail ⟨i.val - k, by omega⟩
        have hWtail_in_nb : ∀ j : Fin (s - k), Wtail j ⊆ V'.filter (H.Adj (y j)) := hWtail_sub
        have hy_notB : ∀ j : Fin (s - k), y j ∉ B := fun j ↦ (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hy_mem j)).1).2
        have hWtail_notB : ∀ j : Fin (s - k), ∀ z ∈ Wtail j, z ∉ B := fun j z hz ↦
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hWtail_in_nb j hz)).1).2
        have hx_inj : Function.Injective x := by
          intro i₁ i₂ heq
          by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
          · simp only [x, h1, h2, ↓reduceDIte] at heq
            have hsub := eB.injective (Subtype.ext heq)
            exact Fin.ext (congr_arg (fun z : Fin k ↦ z.val) hsub)
          · simp only [x, h1, h2, ↓reduceDIte] at heq
            change (eB ⟨i₁.val, h1⟩).1 = y ⟨i₂.val - k, by omega⟩ at heq
            exact absurd (heq ▸ (eB ⟨i₁.val, h1⟩).2) (hy_notB ⟨i₂.val - k, by omega⟩)
          · simp only [x, h1, h2, ↓reduceDIte] at heq
            change y ⟨i₁.val - k, by omega⟩ = (eB ⟨i₂.val, h2⟩).1 at heq
            exact absurd (heq.symm ▸ (eB ⟨i₂.val, h2⟩).2) (hy_notB ⟨i₁.val - k, by omega⟩)
          · simp only [x, h1, h2, ↓reduceDIte] at heq
            have hsub := hy_inj heq
            have hv : i₁.val - k = i₂.val - k := congr_arg (fun z : Fin (s - k) ↦ z.val) hsub
            exact Fin.ext (by omega)
        apply hGfree
        refine embed_star_forest hc_inj hc_mem hc_surj hC_indep hnotC_uniq hnotC_indep
          x hx_inj W ?_ ?_ ?_ ?_
        · intro i
          by_cases h : i.val < k
          · simp only [W, h, ↓reduceDIte, hWhead_c]; rfl
          · simp only [W, h, ↓reduceDIte, hWtail_card]
            have hidx : (⟨k + (i.val - k), by omega⟩ : Fin s) = i := Fin.ext (by dsimp only; omega)
            rw [hidx]
        · intro i₁ i₂ hne
          by_cases h1 : i₁.val < k <;> by_cases h2 : i₂.val < k
          · simp only [W, h1, h2, ↓reduceDIte]
            exact hWhead_d ⟨i₁.val, h1⟩ ⟨i₂.val, h2⟩ (fun h ↦ hne (Fin.ext (congr_arg (fun z : Fin k ↦ z.val) h)))
          · simp only [W, h1, h2, ↓reduceDIte]
            refine (hWhead_U ⟨i₁.val, h1⟩).mono_right ?_
            intro z hz
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨⟨i₂.val - k, by omega⟩, Finset.mem_univ _, Finset.mem_insert_of_mem hz⟩)
          · simp only [W, h1, h2, ↓reduceDIte]
            refine ((hWhead_U ⟨i₂.val, h2⟩).mono_right ?_).symm
            intro z hz
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨⟨i₁.val - k, by omega⟩, Finset.mem_univ _, Finset.mem_insert_of_mem hz⟩)
          · simp only [W, h1, h2, ↓reduceDIte]
            have hne' : (⟨i₁.val - k, by omega⟩ : Fin (s - k)) ≠ ⟨i₂.val - k, by omega⟩ :=
              fun h ↦ hne (Fin.ext (by have := congr_arg (fun z : Fin (s - k) ↦ z.val) h; dsimp at this; omega))
            rw [Finset.disjoint_left]
            intro z hz1 hz2
            exact Finset.disjoint_left.mp (hy_disj _ _ hne')
              (by simpa using Finset.mem_insert_of_mem (hWtail_in_nb _ hz1))
              (by simpa using Finset.mem_insert_of_mem (hWtail_in_nb _ hz2))
        · intro i z hz
          by_cases h : i.val < k
          · simp only [x, W, h, ↓reduceDIte] at hz ⊢
            exact hWhead_a ⟨i.val, h⟩ z hz
          · simp only [x, W, h, ↓reduceDIte] at hz ⊢
            exact (Finset.mem_filter.mp (hWtail_in_nb ⟨i.val - k, by omega⟩ hz)).2
        · intro i j hmem
          by_cases hi : i.val < k <;> by_cases hj : j.val < k
          · simp only [x, W, hi, hj, ↓reduceDIte] at hmem
            exact Finset.disjoint_left.mp (hWhead_U ⟨i.val, hi⟩) hmem
              (Finset.mem_union_left _ (eB ⟨j.val, hj⟩).2)
          · simp only [x, W, hi, hj, ↓reduceDIte] at hmem
            exact Finset.disjoint_left.mp (hWhead_U ⟨i.val, hi⟩) hmem
              (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
                ⟨⟨j.val - k, by omega⟩, Finset.mem_univ _, Finset.mem_insert_self _ _⟩))
          · simp only [x, W, hi, hj, ↓reduceDIte] at hmem
            exact hWtail_notB ⟨i.val - k, by omega⟩ _ hmem (eB ⟨j.val, hj⟩).2
          · simp only [x, W, hi, hj, ↓reduceDIte] at hmem
            by_cases hij : i = j
            · subst hij
              have hadj := (Finset.mem_filter.mp (hWtail_in_nb ⟨i.val - k, by omega⟩ hmem)).2
              exact H.ne_of_adj hadj rfl
            · have hne' : (⟨i.val - k, by omega⟩ : Fin (s - k)) ≠ ⟨j.val - k, by omega⟩ :=
                fun h ↦ hij (Fin.ext (by have := congr_arg (fun z : Fin (s - k) ↦ z.val) h; dsimp at this; omega))
              exact Finset.disjoint_left.mp (hy_disj _ _ hne')
                (by simpa using Finset.mem_insert_of_mem (hWtail_in_nb _ hmem))
                (Finset.mem_insert_self _ _)
      -- Edge bound on H: 2 * #E(H) ≤ 2 * k * n + (r - 1) * n + C'.card * (2 * q)
      have h2edges : 2 * #H.edgeFinset ≤ 2 * k * n + (r - 1) * n + C'.card * (2 * q) := by
        -- Split edges into those touching B and those inside V'
        let E_B := H.edgeFinset.filter (fun ed ↦ ∃ u ∈ B, u ∈ ed)
        let E_V := H.edgeFinset.filter (fun ed ↦ ¬ ∃ u ∈ B, u ∈ ed)
        have hpart : #H.edgeFinset = E_B.card + E_V.card :=
          (Finset.card_filter_add_card_filter_not (s := H.edgeFinset)
            (p := fun ed ↦ ∃ u ∈ B, u ∈ ed)).symm
        have hEB_le : E_B.card ≤ k * n := by
          have hsub : E_B ⊆ B.biUnion (fun u ↦ (H.neighborFinset u).image (fun w ↦ s(u, w))) := by
            intro ed hed
            rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hed
            rcases ed with ⟨u₁, u₂⟩
            obtain ⟨u, huB, hu_mem⟩ := hed.2
            simp only [Sym2.mem_iff] at hu_mem
            rw [Finset.mem_biUnion]
            rcases hu_mem with rfl | rfl
            · exact ⟨u, huB, Finset.mem_image.mpr ⟨u₂, (SimpleGraph.mem_neighborFinset H u u₂).mpr hed.1, rfl⟩⟩
            · exact ⟨u, huB, Finset.mem_image.mpr ⟨u₁, (SimpleGraph.mem_neighborFinset H u u₁).mpr hed.1.symm, Sym2.eq_swap⟩⟩
          calc E_B.card
              ≤ (B.biUnion (fun u ↦ (H.neighborFinset u).image (fun w ↦ s(u, w)))).card :=
                Finset.card_le_card hsub
            _ ≤ ∑ u ∈ B, ((H.neighborFinset u).image (fun w ↦ s(u, w))).card := Finset.card_biUnion_le
            _ ≤ ∑ _u ∈ B, n := by
                refine Finset.sum_le_sum fun u _ ↦ ?_
                exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
            _ = k * n := by rw [Finset.sum_const, smul_eq_mul]
        have hEV_le : 2 * E_V.card ≤ (r - 1) * n + C'.card * (2 * q) := by
          have hbij : E_V.card = #(H.induce (V' : Set (Fin n))).edgeFinset := by
            symm
            refine Finset.card_bij (fun ed _ ↦ Sym2.map Subtype.val ed) ?_ ?_ ?_
            · intro ed hed
              rcases ed with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
              rw [SimpleGraph.mem_edgeFinset] at hed
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
              refine ⟨hed, ?_⟩
              rintro ⟨u, huB, hu_mem⟩
              simp only [Sym2.map_mk, Sym2.mem_iff] at hu_mem
              rcases hu_mem with rfl | rfl
              · exact (Finset.mem_sdiff.mp ha).2 huB
              · exact (Finset.mem_sdiff.mp hb).2 huB
            · intro e₁ _ e₂ _ heq
              exact Sym2.map.injective Subtype.val_injective heq
            · intro ed hed
              rcases ed with ⟨a, b⟩
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hed
              have ha : a ∈ V' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,
                fun hB ↦ hed.2 ⟨a, hB, by simp⟩⟩
              have hb : b ∈ V' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ b,
                fun hB ↦ hed.2 ⟨b, hB, by simp⟩⟩
              refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
              rw [SimpleGraph.mem_edgeFinset]
              exact hed.1
          rw [hbij, ← SimpleGraph.sum_degrees_eq_twice_card_edges (H.induce (V' : Set (Fin n)))]
          have hdeg_eq : ∀ u : V', (H.induce (V' : Set (Fin n))).degree u = (V'.filter (H.Adj u.1)).card := by
            intro u
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            refine Finset.card_bij (fun w _ ↦ w.1) ?_ ?_ ?_
            · intro w hw
              rw [SimpleGraph.mem_neighborFinset] at hw
              exact Finset.mem_filter.mpr ⟨w.2, hw⟩
            · intro w₁ _ w₂ _ h; exact Subtype.ext h
            · intro w hw
              rw [Finset.mem_filter] at hw
              exact ⟨⟨w, hw.1⟩, (SimpleGraph.mem_neighborFinset _ u ⟨w, hw.1⟩).mpr hw.2, rfl⟩
          simp_rw [hdeg_eq]
          have hsum_V' : ∑ x : V', (V'.filter (H.Adj x.1)).card =
              ∑ u ∈ V', (V'.filter (H.Adj u)).card := by
            convert Finset.sum_coe_sort V' (fun u ↦ (V'.filter (H.Adj u)).card)
          refine le_trans (le_of_eq hsum_V') ?_
          have hsplit_V' : V' = C' ∪ (V' \ C') := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
          have hdisj_V' : Disjoint C' (V' \ C') := Finset.disjoint_sdiff
          have hsum_split : ∑ u ∈ V', (V'.filter (H.Adj u)).card =
              (∑ u ∈ C', (V'.filter (H.Adj u)).card) + ∑ u ∈ V' \ C', (V'.filter (H.Adj u)).card := by
            rw [← Finset.sum_union hdisj_V', ← hsplit_V']
          rw [hsum_split]
          have hsum_C' : ∑ u ∈ C', (V'.filter (H.Adj u)).card ≤ C'.card * (2 * q) := by
            calc ∑ u ∈ C', (V'.filter (H.Adj u)).card
                ≤ ∑ _u ∈ C', (2 * q) := Finset.sum_le_sum fun u hu ↦ hV'_maxdeg u (Finset.mem_filter.mp hu).1
              _ = C'.card * (2 * q) := by rw [Finset.sum_const, smul_eq_mul]
          have hsum_rem : ∑ u ∈ V' \ C', (V'.filter (H.Adj u)).card ≤ (r - 1) * n := by
            calc ∑ u ∈ V' \ C', (V'.filter (H.Adj u)).card
                ≤ ∑ _u ∈ V' \ C', (r - 1) := by
                    refine Finset.sum_le_sum fun u hu ↦ ?_
                    rw [Finset.mem_sdiff] at hu
                    have hlt : (V'.filter (H.Adj u)).card < r := by
                      by_contra hge; push Not at hge
                      exact hu.2 (Finset.mem_filter.mpr ⟨hu.1, hge⟩)
                    omega
              _ = (V' \ C').card * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ n * (r - 1) := Nat.mul_le_mul_right _ ((Finset.card_le_univ _).trans (by simp))
              _ = (r - 1) * n := mul_comm _ _
          omega
        have h2kn : 2 * k * n = 2 * (k * n) := by ring
        omega
      have h2q_r : (2 * #H.edgeFinset : ℚ) ≤
          2 * (val kfin * (n : ℚ) + (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ)) := by
        have h1 : (2 * #H.edgeFinset : ℚ) ≤
            (2 * k * n + (r - 1) * n + C'.card * (2 * q) : ℕ) := by exact_mod_cast h2edges
        have h2 : (C'.card : ℚ) ≤ (s * (1 + 2 * q + 4 * q * q) : ℚ) := by
          have hnat_c : C'.card ≤ s * (1 + 2 * q + 4 * q * q) := by
            calc C'.card ≤ (s - k) * (1 + 2 * q + 2 * q * (2 * q)) := hC'_le
              _ ≤ s * (1 + 2 * q + 4 * q * q) := by
                  have : 1 + 2 * q + 2 * q * (2 * q) = 1 + 2 * q + 4 * q * q := by ring
                  rw [this]
                  exact Nat.mul_le_mul_right _ (Nat.sub_le s k)
          exact_mod_cast hnat_c
        push_cast at h1
        dsimp [val, kfin, r]
        have hq0 : (0 : ℚ) ≤ (2 * q : ℚ) := by positivity
        nlinarith
      have hval_le : val kfin ≤ Mstar := hk₀_max kfin (Finset.mem_univ kfin)
      have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
      nlinarith
    have hex_le : (extremalNumber n G : ℚ) ≤ Mstar * (n : ℚ) + (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ) := by
      have hnonneg : (0 : ℚ) ≤ Mstar * (n : ℚ) + (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ) := by
        have : (0 : ℚ) ≤ Mstar := by dsimp [Mstar, val]; positivity
        positivity
      conv_lhs => rw [← Fintype.card_fin n]
      rw [SimpleGraph.extremalNumber_le_iff_of_nonneg G hnonneg]
      intro H _ hGfree
      exact hnat H hGfree
    exact hex_le
  -- From hlim and hupper, deduce b ≤ Mstar
  have hb_le : b ≤ Mstar := by
    by_contra hgt
    push Not at hgt
    let C0 : ℚ := (s * (1 + 2 * q + 4 * q * q) * (2 * q) : ℚ)
    obtain ⟨N0, hN0⟩ := exists_nat_gt (C0 / (b - Mstar))
    obtain ⟨n, hn, hbn⟩ := hlim N0
    have hup := hupper n
    have hbm : (0 : ℚ) < b - Mstar := by linarith
    have hn_gt : C0 / (b - Mstar) < (n : ℚ) := hN0.trans_le (by exact_mod_cast hn)
    have hmul : C0 < (b - Mstar) * (n : ℚ) := (div_lt_iff₀ hbm).mp hn_gt |> fun h ↦ by linarith
    linarith
  -- Step 2: Constructive lower bound ex(m, G) ≥ Mstar * m - (k₀ + 1)^2 - d k₀
  let k : ℕ := k₀.val
  let r : ℕ := d k₀ - 1
  have hlower : ∀ m : ℕ, k + r + 2 ≤ m →
      Mstar * (m : ℚ) - ((k + 1) * (k + r + 1) + 1 : ℚ) ≤ (extremalNumber m G : ℚ) := by
    intro m hm
    let m' : ℕ := m - k
    obtain ⟨R, hR_deg, hR_edges⟩ := circulant_exists_deg_le m' r (by omega)
    let Hm : SimpleGraph (Fin m) := {
      Adj := fun u v ↦ u ≠ v ∧ (u.val < k ∨ v.val < k ∨
        ∃ (hu : k ≤ u.val) (hv : k ≤ v.val), R.Adj ⟨u.val - k, by omega⟩ ⟨v.val - k, by omega⟩)
      symm := ⟨by
        intro u v ⟨hne, h⟩
        refine ⟨hne.symm, ?_⟩
        rcases h with hu | hv | ⟨hu, hv, hadj⟩
        · exact Or.inr (Or.inl hu)
        · exact Or.inl hv
        · exact Or.inr (Or.inr ⟨hv, hu, hadj.symm⟩)⟩
      loopless := ⟨fun u h ↦ h.1 rfl⟩
    }
    have hHm_free : G.Free Hm := by
      intro ⟨φ⟩
      let Kfin : Finset (Fin (k + 1)) := Finset.univ
      let Iin : Finset (Fin (k + 1)) := Kfin.filter (fun i ↦ (φ (c ⟨i.val, by omega⟩)).val < k)
      let Iout : Finset (Fin (k + 1)) := Kfin.filter (fun i ↦ ¬ (φ (c ⟨i.val, by omega⟩)).val < k)
      have hleaf_in_K : ∀ i ∈ Iout, ∃ w ∈ G.neighborFinset (c ⟨i.val, by omega⟩),
          (φ w).val < k := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have hci_ge : k ≤ (φ (c ⟨i.val, by omega⟩)).val := by omega
        by_contra hnone
        push Not at hnone
        let nb := G.neighborFinset (c ⟨i.val, by omega⟩)
        have hnb_card : d k₀ ≤ nb.card := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact hc_mono ⟨i.val, by omega⟩ k₀ (by show i.val ≤ k; omega)
        have hmap_sub : nb.image (fun w ↦ (⟨(φ w).val - k, by omega⟩ : Fin m')) ⊆
            R.neighborFinset ⟨(φ (c ⟨i.val, by omega⟩)).val - k, by omega⟩ := by
          intro z hz
          rw [Finset.mem_image] at hz
          obtain ⟨w, hw, rfl⟩ := hz
          rw [SimpleGraph.mem_neighborFinset]
          have hGadj := (SimpleGraph.mem_neighborFinset G _ w).mp hw
          have hHadj := φ.toHom.map_rel hGadj
          rcases hHadj.2 with h1 | h2 | ⟨_, _, hRadj⟩
          · change (φ (c ⟨i.val, by omega⟩)).val < k at h1
            omega
          · have hw_ge : k ≤ (φ w).val := hnone w (by exact hw)
            change (φ w).val < k at h2
            omega
          · exact hRadj
        have hinj_nb : Set.InjOn (fun w ↦ (⟨(φ w).val - k, by omega⟩ : Fin m')) (nb : Set (Fin q)) := by
          intro w₁ hw₁ w₂ hw₂ heq
          have hv : (φ w₁).val - k = (φ w₂).val - k := congr_arg Fin.val heq
          have h1 : k ≤ (φ w₁).val := hnone w₁ hw₁
          have h2 : k ≤ (φ w₂).val := hnone w₂ hw₂
          have hval_eq : (φ w₁).val = (φ w₂).val := by omega
          exact φ.injective (Fin.ext hval_eq)
        have hle_r : nb.card ≤ r := by
          calc nb.card
              = (nb.image (fun w ↦ (⟨(φ w).val - k, by omega⟩ : Fin m'))).card :=
                (Finset.card_image_of_injOn hinj_nb).symm
            _ ≤ (R.neighborFinset ⟨(φ (c ⟨i.val, by omega⟩)).val - k, by omega⟩).card :=
                Finset.card_le_card hmap_sub
            _ = R.degree _ := SimpleGraph.card_neighborFinset_eq_degree R _
            _ ≤ r := hR_deg _
        have hd_pos_k0 := hd_pos k₀
        omega
      let mapToK : Fin (k + 1) → Fin k := fun i ↦
        if hi : i ∈ Iin then ⟨(φ (c ⟨i.val, by omega⟩)).val, (Finset.mem_filter.mp hi).2⟩
        else
          have hiout : i ∈ Iout := Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun h ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)⟩
          let w := Classical.choose (hleaf_in_K i hiout)
          ⟨(φ w).val, (Classical.choose_spec (hleaf_in_K i hiout)).2⟩
      have hmap_inj : Function.Injective mapToK := by
        intro i₁ i₂ heq
        have hv : (mapToK i₁).val = (mapToK i₂).val := congr_arg Fin.val heq
        by_cases h1 : i₁ ∈ Iin <;> by_cases h2 : i₂ ∈ Iin
        · simp only [mapToK, h1, h2, ↓reduceDIte] at hv
          have hsub := hc_inj (φ.injective (Fin.ext hv))
          have hval : i₁.val = i₂.val := congr_arg (fun x : Fin s ↦ x.val) hsub
          exact Fin.ext hval
        · simp only [mapToK, h1, h2, ↓reduceDIte] at hv
          exfalso
          have h2out : i₂ ∈ Iout := Finset.mem_filter.mpr ⟨Finset.mem_univ i₂, fun h ↦ h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i₂, h⟩)⟩
          have hw_adj := (SimpleGraph.mem_neighborFinset G _ _).mp (Classical.choose_spec (hleaf_in_K i₂ h2out)).1
          have hceq := φ.injective (Fin.ext hv)
          rw [← hceq] at hw_adj
          exact hC_indep _ (hc_mem _) _ (hc_mem _) hw_adj
        · simp only [mapToK, h1, h2, ↓reduceDIte] at hv
          exfalso
          have h1out : i₁ ∈ Iout := Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, fun h ↦ h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, h⟩)⟩
          have hw_adj := (SimpleGraph.mem_neighborFinset G _ _).mp (Classical.choose_spec (hleaf_in_K i₁ h1out)).1
          have hceq := φ.injective (Fin.ext hv.symm)
          rw [← hceq] at hw_adj
          exact hC_indep _ (hc_mem _) _ (hc_mem _) hw_adj
        · simp only [mapToK, h1, h2, ↓reduceDIte] at hv
          have h1out : i₁ ∈ Iout := Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, fun h ↦ h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, h⟩)⟩
          have h2out : i₂ ∈ Iout := Finset.mem_filter.mpr ⟨Finset.mem_univ i₂, fun h ↦ h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i₂, h⟩)⟩
          have hw1 := (SimpleGraph.mem_neighborFinset G _ _).mp (Classical.choose_spec (hleaf_in_K i₁ h1out)).1
          have hw2 := (SimpleGraph.mem_neighborFinset G _ _).mp (Classical.choose_spec (hleaf_in_K i₂ h2out)).1
          have hweq : Classical.choose (hleaf_in_K i₁ h1out) = Classical.choose (hleaf_in_K i₂ h2out) :=
            φ.injective (Fin.ext hv)
          rw [← hweq] at hw2
          have hw_notC : Classical.choose (hleaf_in_K i₁ h1out) ∉ C :=
            fun hmem ↦ hC_indep _ (hc_mem _) _ hmem hw1
          obtain ⟨z, _, hz_uniq⟩ := hnotC_uniq _ hw_notC
          have e1 := hz_uniq _ ⟨hc_mem _, hw1.symm⟩
          have e2 := hz_uniq _ ⟨hc_mem _, hw2.symm⟩
          have hsub := hc_inj (e1.trans e2.symm)
          have hval : i₁.val = i₂.val := congr_arg (fun x : Fin s ↦ x.val) hsub
          exact Fin.ext hval
      have hcard_le := Fintype.card_le_of_injective mapToK hmap_inj
      simp at hcard_le
    -- Count edges of Hm: cross edges (k * m') + R edges (≥ (r * m' - 1) / 2)
    have hHm_edges : 2 * k * m' + (r * m' - 1) ≤ 2 * #Hm.edgeFinset := by
      let Ecross : Finset (Sym2 (Fin m)) :=
        ((Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin m'))).image
          fun p ↦ s(⟨p.1.val, by omega⟩, ⟨k + p.2.val, by omega⟩)
      let Etail : Finset (Sym2 (Fin m)) :=
        R.edgeFinset.image (Sym2.map fun a : Fin m' ↦ (⟨k + a.val, by omega⟩ : Fin m))
      have hEc_sub : Ecross ⊆ Hm.edgeFinset := by
        intro ed hed
        rw [Finset.mem_image] at hed
        obtain ⟨⟨i, j⟩, _, rfl⟩ := hed
        rw [SimpleGraph.mem_edgeFinset]
        exact ⟨fun h ↦ by have := congr_arg Fin.val h; dsimp at this; omega, Or.inl i.isLt⟩
      have hEt_sub : Etail ⊆ Hm.edgeFinset := by
        intro ed hed
        rw [Finset.mem_image] at hed
        obtain ⟨eR, heR, rfl⟩ := hed
        rcases eR with ⟨a, b⟩
        simp only [Sym2.map_mk]
        rw [SimpleGraph.mem_edgeFinset] at heR ⊢
        change Hm.Adj ⟨k + a.val, by omega⟩ ⟨k + b.val, by omega⟩
        refine ⟨fun h ↦ heR.ne (Fin.ext (Nat.add_left_cancel (congr_arg Fin.val h))),
          Or.inr (Or.inr ⟨Nat.le_add_right k a.val, Nat.le_add_right k b.val, ?_⟩)⟩
        simpa [Nat.add_sub_cancel_left] using heR
      have hdisj : Disjoint Ecross Etail := by
        rw [Finset.disjoint_left]
        intro ed h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨⟨i, j⟩, _, rfl⟩ := h1
        obtain ⟨eR, _, heq⟩ := h2
        rcases eR with ⟨a, b⟩
        simp only [Sym2.map_mk, Sym2.eq_iff, Fin.mk.injEq] at heq
        rcases heq with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      have hEc_card : Ecross.card = k * m' := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
          simp only [Sym2.eq_iff, Fin.mk.injEq] at heq
          rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Prod.ext (Fin.ext h1) (Fin.ext (Nat.add_left_cancel h2))
          · omega
      have hEt_card : Etail.card = #R.edgeFinset := by
        rw [Finset.card_image_of_injective]
        exact Sym2.map.injective (fun a b h ↦ Fin.ext (by have hv := congr_arg Fin.val h; dsimp only at hv; omega))
      have hle : Ecross.card + Etail.card ≤ #Hm.edgeFinset := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset hEc_sub hEt_sub)
      have h2km' : 2 * k * m' = 2 * (k * m') := by ring
      omega
    have hex_ge : (#Hm.edgeFinset : ℚ) ≤ (extremalNumber m G : ℚ) := by
      have hle_ex := SimpleGraph.card_edgeFinset_le_extremalNumber hHm_free
      rw [Fintype.card_fin] at hle_ex
      exact_mod_cast hle_ex
    have h2m : (2 * k * m' + (r * m' - 1) : ℕ) ≤ 2 * #Hm.edgeFinset := hHm_edges
    have h2m_q : ((2 * k * m' : ℕ) : ℚ) + ((r * m' : ℕ) : ℚ) - 1 ≤ 2 * (#Hm.edgeFinset : ℚ) := by
      have hcast : ((2 * k * m' + (r * m' - 1) : ℕ) : ℚ) ≤ ((2 * #Hm.edgeFinset : ℕ) : ℚ) := by
        exact_mod_cast h2m
      push_cast at hcast ⊢
      by_cases hrm : 1 ≤ r * m'
      · rw [Nat.cast_sub hrm] at hcast; push_cast at hcast; linarith
      · have hrm0 : r * m' = 0 := by omega
        have hrm0q : (r : ℚ) * (m' : ℚ) = 0 := by exact_mod_cast hrm0
        rw [hrm0] at hcast
        simp at hcast
        linarith
    have hm'k : (m' : ℚ) + (k : ℚ) = (m : ℚ) := by exact_mod_cast (show m' + k = m by omega)
    have hm'_q : (m' : ℚ) = (m : ℚ) - (k : ℚ) := by linarith
    dsimp [Mstar, val, k, r] at h2m_q ⊢
    push_cast at h2m_q
    rw [hm'_q] at h2m_q
    have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
    have hr0 : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
    nlinarith
  -- Step 3: Conclude ∃ M, ∀ m ≥ M, a * m ≤ extremalNumber m G
  let C1 : ℚ := ((k + 1) * (k + r + 1) + 1 : ℚ)
  obtain ⟨M1, hM1⟩ := exists_nat_ge (C1 / (b - a))
  refine ⟨max (k + r + 2) M1, fun m hm ↦ ?_⟩
  have h1 := hlower m ((le_max_left _ _).trans hm)
  have h2 : M1 ≤ m := (le_max_right _ _).trans hm
  have hba : (0 : ℚ) < b - a := by linarith
  have hm_ge : C1 / (b - a) ≤ (m : ℚ) := hM1.trans (by exact_mod_cast h2)
  have hmul : C1 ≤ (b - a) * (m : ℚ) := (div_le_iff₀ hba).mp hm_ge |> fun h ↦ by linarith
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  nlinarith
