import OMAReductions.R_Erdos719_erdos_719_R1

/-!
# Proof of `Erdos719.erdos_719.R1.H1` (Erdős–Goodman–Pósa, 1966)

Every 2-uniform hypergraph `H` on `n` vertices admits an edge-disjoint decomposition `D` into
edges and triangles (`|S| ∈ {2, 3}`) with `D.card ≤ Hypergraph.cliqueExtremalNumber n 2 3`.

1. **Extremal lower bound (`n ^ 2 / 4 ≤ cliqueExtremalNumber n 2 3`)**: the balanced complete
   bipartite graph on `{i : Fin n | i.1 < n / 2}` and `{i : Fin n | n / 2 ≤ i.1}` is triangle-free
   and has `(n / 2) * (n - n / 2) = n ^ 2 / 4` edges.
2. **Erdős–Goodman–Pósa decomposition (`D.card ≤ m ^ 2 / 4`)**: by induction on `V.card = m`:
   choose a minimum-degree vertex `v ∈ V` (degree `d = |A|` where `A = N(v)`) and a maximum
   matching `M` of size `m₀` inside the induced subgraph on `A`. Every unmatched vertex `x ∈ A \ V(M)`
   has all its neighbors in `A` inside `V(M)`, so `2 * m₀ ≥ |N(x) ∩ A| ≥ d - (m + 1 - d) = 2 * d - (m + 1)`,
   yielding `d - m₀ ≤ (m + 1) / 2` in all cases. Combining the IH decomposition of `(H - v) \ M`
   (at most `m ^ 2 / 4` cliques) with the `m₀` triangles `insert v e` (`e ∈ M`) and `d - 2 * m₀`
   edges `{v, u}` (`u ∈ A \ V(M)`) gives an edge-disjoint decomposition of size at most
   `m ^ 2 / 4 + (d - m₀) ≤ m ^ 2 / 4 + (m + 1) / 2 = (m + 1) ^ 2 / 4`.
-/

namespace OMA.P_Erdos719_H1

open Finset

private lemma half_mul_sub_half (n : ℕ) : (n / 2) * (n - n / 2) = n ^ 2 / 4 := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  set q := n / 2
  have hn : n = 2 * q + n % 2 := (Nat.div_add_mod n 2).symm
  rcases hmod with h0 | h1
  · have hnq : n = 2 * q := by omega
    rw [hnq]
    have h1' : (2 * q) ^ 2 = 4 * (q * q) := by ring
    rw [h1', Nat.mul_div_right _ (by norm_num)]
    have h2' : 2 * q - q = q := by omega
    rw [h2']
  · have hnq : n = 2 * q + 1 := by omega
    rw [hnq]
    have h1' : (2 * q + 1) ^ 2 = 4 * (q * (q + 1)) + 1 := by ring
    rw [h1', Nat.mul_add_div (by norm_num : 0 < 4)]
    have h2' : 2 * q + 1 - q = q + 1 := by omega
    rw [h2']
    simp

private lemma turan_step (m : ℕ) : m ^ 2 / 4 + (m + 1) / 2 = (m + 1) ^ 2 / 4 := by
  have hmod : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  set q := m / 2
  have hm : m = 2 * q + m % 2 := (Nat.div_add_mod m 2).symm
  rcases hmod with h0 | h1
  · have hmq : m = 2 * q := by omega
    rw [hmq]
    have h1' : (2 * q) ^ 2 = 4 * (q * q) := by ring
    have h2' : (2 * q + 1) ^ 2 = 4 * (q * q + q) + 1 := by ring
    have h3' : (2 * q + 1) / 2 = q := by omega
    rw [h1', h2', h3', Nat.mul_div_right _ (by norm_num), Nat.mul_add_div (by norm_num : 0 < 4)]
    simp
  · have hmq : m = 2 * q + 1 := by omega
    rw [hmq]
    have h1' : (2 * q + 1) ^ 2 = 4 * (q * q + q) + 1 := by ring
    have h2' : (2 * q + 1 + 1) ^ 2 = 4 * (q * q + 2 * q + 1) := by ring
    have h3' : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    rw [h1', h2', h3', Nat.mul_div_right _ (by norm_num), Nat.mul_add_div (by norm_num : 0 < 4)]
    omega

private lemma quarter_le_cliqueExtremalNumber (n : ℕ) :
    n ^ 2 / 4 ≤ Hypergraph.cliqueExtremalNumber n 2 (2 + 1) := by
  classical
  set k := n / 2
  let A : Finset (Fin n) := Finset.univ.filter fun i => i.1 < k
  let B : Finset (Fin n) := Finset.univ.filter fun i => k ≤ i.1
  let K : Finset (Finset (Fin n)) := (A ×ˢ B).image fun p => ({p.1, p.2} : Finset (Fin n))
  have hAcard : A.card = k := by
    have hbij : A = Finset.univ.image (fun j : Fin k => (⟨j.1, by omega⟩ : Fin n)) := by
      ext i
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        exact ⟨⟨i.1, hi⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.2
    rw [hbij, Finset.card_image_of_injective]
    · simp
    · intro x y hxy
      exact Fin.ext (by simpa using congrArg Fin.val hxy)
  have hBcard : B.card = n - k := by
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
      omega
    have hunion : A ∪ B = Finset.univ := by
      ext i
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    have hsum : A.card + B.card = n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  have hKsub : K ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro e he
    simp only [K, Finset.mem_image, Finset.mem_product, A, B, Finset.mem_filter,
      Finset.mem_univ, true_and] at he
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := he
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, Finset.card_pair ?_⟩
    intro hab
    dsimp only at ha hb hab
    subst hab
    omega
  have hKinj : Set.InjOn (fun p : Fin n × Fin n => ({p.1, p.2} : Finset (Fin n))) ((A ×ˢ B : Finset _) : Set _) := by
    rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 heq
    dsimp only at heq
    simp only [Finset.mem_coe, Finset.mem_product, A, B, Finset.mem_filter,
      Finset.mem_univ, true_and] at h1 h2
    have ha1 : a1 ∈ ({a2, b2} : Finset (Fin n)) := heq ▸ Finset.mem_insert_self a1 {b1}
    have hb1 : b1 ∈ ({a2, b2} : Finset (Fin n)) := heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 hb1
    have ha : a1 = a2 := by
      rcases ha1 with h | h
      · exact h
      · subst h; omega
    have hb : b1 = b2 := by
      rcases hb1 with h | h
      · subst h; omega
      · exact h
    exact Prod.ext ha hb
  have hKcard : K.card = n ^ 2 / 4 := by
    rw [Finset.card_image_of_injOn hKinj, Finset.card_product, hAcard, hBcard]
    exact half_mul_sub_half n
  have hKfree : ¬ K.ContainsCompleteHypergraph 2 (2 + 1) := by
    rintro ⟨S, hScard, hSsub⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hScard
    have hpair : ∀ u v : Fin n, u ∈ ({x, y, z} : Finset (Fin n)) →
        v ∈ ({x, y, z} : Finset (Fin n)) → u ≠ v →
        (u.1 < k ∧ k ≤ v.1) ∨ (v.1 < k ∧ k ≤ u.1) := by
      intro u v hu hv huv
      have he : ({u, v} : Finset (Fin n)) ∈ ({x, y, z} : Finset (Fin n)).powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair huv⟩
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have heK := hSsub he
      simp only [K, Finset.mem_image, Finset.mem_product, A, B, Finset.mem_filter,
        Finset.mem_univ, true_and] at heK
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := heK
      have hu' : u ∈ ({a, b} : Finset (Fin n)) := hab.symm ▸ Finset.mem_insert_self u {v}
      have hv' : v ∈ ({a, b} : Finset (Fin n)) := hab.symm ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu' hv'
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact False.elim (huv rfl)
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact False.elim (huv rfl)
    have h1 := hpair x y (by simp) (by simp) hxy
    have h2 := hpair x z (by simp) (by simp) hxz
    have h3 := hpair y z (by simp) (by simp) hyz
    omega
  rw [← hKcard]
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply Finset.le_sup (f := Finset.card)
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hKsub, hKfree⟩

private lemma pair_eq_iff {α : Type*} [DecidableEq α] {u v x y : α}
    (h : ({u, v} : Finset α) = {x, y}) : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hu : u ∈ ({x, y} : Finset α) := h ▸ Finset.mem_insert_self u {v}
  have hv : v ∈ ({x, y} : Finset α) := h ▸ (by simp)
  have hx : x ∈ ({u, v} : Finset α) := h.symm ▸ Finset.mem_insert_self x {y}
  have hy : y ∈ ({u, v} : Finset α) := h.symm ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hx hy
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

private lemma egp_finset {α : Type*} [DecidableEq α] :
    ∀ m : ℕ, ∀ (V : Finset α) (H : Finset (Finset α)),
      V.card = m → H.IsUniform 2 → (∀ e ∈ H, e ⊆ V) →
      ∃ D : Finset (Finset α),
        H.IsCompleteHypergraphDecomposition 2 D ∧ D.card ≤ m ^ 2 / 4 := by
  intro m
  induction m with
  | zero =>
    intro V H hV hU hsub
    have hV0 : V = ∅ := Finset.card_eq_zero.mp hV
    have hH0 : H = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have hcard := hU e he
      have hsub0 : e ⊆ ∅ := hV0 ▸ hsub e he
      have he0 : e = ∅ := Finset.subset_empty.mp hsub0
      rw [he0] at hcard
      simp at hcard
    subst hH0
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, by simp⟩
  | succ m ih =>
    intro V H hV hU hsub
    have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
    let N : α → Finset α := fun u => V.filter fun w => ({u, w} : Finset α) ∈ H
    have hN_sub : ∀ u, N u ⊆ V := fun u => Finset.filter_subset _ _
    have hN_not_self : ∀ u, u ∉ N u := by
      intro u hu
      simp only [N, Finset.mem_filter] at hu
      have hcard := hU _ hu.2
      simp at hcard
    have hN_mem : ∀ {u w : α}, u ∈ V → (w ∈ N u ↔ ({u, w} : Finset α) ∈ H) := by
      intro u w _
      simp only [N, Finset.mem_filter, and_iff_right_iff_imp]
      intro he
      exact hsub _ he (by simp)
    obtain ⟨v, hvV, hvmin⟩ := Finset.exists_min_image V (fun u => (N u).card) hVne
    let A : Finset α := N v
    set d : ℕ := A.card
    have hv_not_A : v ∉ A := hN_not_self v
    have hA_sub_erase : A ⊆ V.erase v := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun hxv => hv_not_A (hxv ▸ hx), hN_sub v hx⟩
    have hd_le_m : d ≤ m := by
      have h1 : A.card ≤ (V.erase v).card := Finset.card_le_card hA_sub_erase
      rw [Finset.card_erase_of_mem hvV, hV] at h1
      omega
    let HA : Finset (Finset α) := H.filter fun e => e ⊆ A
    let Matchings : Finset (Finset (Finset α)) :=
      HA.powerset.filter fun M => (M : Set (Finset α)).Pairwise Disjoint
    have hMne : Matchings.Nonempty :=
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩⟩
    obtain ⟨M, hMmem, hMmax⟩ := Finset.exists_max_image Matchings Finset.card hMne
    have hMsubHA : M ⊆ HA := Finset.mem_powerset.mp (Finset.mem_filter.mp hMmem).1
    have hMdisj : (M : Set (Finset α)).Pairwise Disjoint := (Finset.mem_filter.mp hMmem).2
    have hMsubH : M ⊆ H := fun e he => (Finset.mem_filter.mp (hMsubHA he)).1
    have hMsubA : ∀ e ∈ M, e ⊆ A := fun e he => (Finset.mem_filter.mp (hMsubHA he)).2
    let VM : Finset α := M.biUnion id
    have hVM_sub_A : VM ⊆ A := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, heM, hxe⟩ := hx
      exact hMsubA e heM hxe
    have hVM_card : VM.card = 2 * M.card := by
      change (M.biUnion id).card = 2 * M.card
      rw [Finset.card_biUnion (t := id) (fun e he f hf hne => hMdisj he hf hne)]
      have h2 : ∀ e ∈ M, (id e).card = 2 := fun e he => hU e (hMsubH he)
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
    have h2M_le_d : 2 * M.card ≤ d := by
      rw [← hVM_card]
      exact Finset.card_le_card hVM_sub_A
    let U : Finset α := A \ VM
    have hU_card : U.card = d - 2 * M.card := by
      rw [Finset.card_sdiff_of_subset hVM_sub_A, hVM_card]
    have hd_sub_M_le : d - M.card ≤ (m + 1) / 2 := by
      by_cases hU0 : U = ∅
      · have hcard0 : d - 2 * M.card = 0 := by rw [← hU_card, hU0]; simp
        omega
      · obtain ⟨x, hxU⟩ := Finset.nonempty_iff_ne_empty.mpr hU0
        have hxA : x ∈ A := (Finset.mem_sdiff.mp hxU).1
        have hxNotVM : x ∉ VM := (Finset.mem_sdiff.mp hxU).2
        have hxV : x ∈ V := hN_sub v hxA
        have hNxA_sub_VM : N x ∩ A ⊆ VM := by
          intro y hy
          have hyNx : y ∈ N x := (Finset.mem_inter.mp hy).1
          have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
          by_contra hyNotVM
          have hxyH : ({x, y} : Finset α) ∈ H := (hN_mem hxV).mp hyNx
          have hxyHA : ({x, y} : Finset α) ∈ HA := by
            rw [Finset.mem_filter]
            refine ⟨hxyH, ?_⟩
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have hxy_disj_M : ∀ e ∈ M, Disjoint ({x, y} : Finset α) e := by
            intro e heM
            rw [Finset.disjoint_left]
            intro w hw hwe
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact hxNotVM (Finset.mem_biUnion.mpr ⟨e, heM, hwe⟩)
            · exact hyNotVM (Finset.mem_biUnion.mpr ⟨e, heM, hwe⟩)
          have hxy_not_M : ({x, y} : Finset α) ∉ M := by
            intro hmem
            have hd := hxy_disj_M _ hmem
            exact Finset.disjoint_left.mp hd (Finset.mem_insert_self x {y}) (Finset.mem_insert_self x {y})
          have hM'_mem : insert ({x, y} : Finset α) M ∈ Matchings := by
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨Finset.insert_subset hxyHA hMsubHA, ?_⟩
            rw [Finset.coe_insert, Set.pairwise_insert]
            exact ⟨hMdisj, fun e he _ => ⟨hxy_disj_M e he, (hxy_disj_M e he).symm⟩⟩
          have hle := hMmax _ hM'_mem
          rw [Finset.card_insert_of_notMem hxy_not_M] at hle
          omega
        have hNx_sub : N x ⊆ (N x ∩ A) ∪ (V \ A) := by
          intro y hy
          by_cases hyA : y ∈ A
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hy, hyA⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hN_sub x hy, hyA⟩)
        have hdeg_le : (N x).card ≤ (N x ∩ A).card + (V \ A).card :=
          le_trans (Finset.card_le_card hNx_sub) (Finset.card_union_le _ _)
        have hNxA_le : (N x ∩ A).card ≤ 2 * M.card := by
          rw [← hVM_card]
          exact Finset.card_le_card hNxA_sub_VM
        have hVA_card : (V \ A).card = m + 1 - d := by
          rw [Finset.card_sdiff_of_subset (hN_sub v), hV]
        have hd_le_Nx : d ≤ (N x).card := hvmin x hxV
        omega
    let V' : Finset α := V.erase v
    let H' : Finset (Finset α) := (H.filter fun e => v ∉ e) \ M
    have hV'_card : V'.card = m := by
      rw [Finset.card_erase_of_mem hvV, hV]
      omega
    have hH'_U : H'.IsUniform 2 := fun e he => hU e (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).1
    have hH'_sub : ∀ e ∈ H', e ⊆ V' := by
      intro e he x hx
      have he1 := Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1
      rw [Finset.mem_erase]
      exact ⟨fun hxv => he1.2 (hxv ▸ hx), hsub e he1.1 hx⟩
    obtain ⟨D', ⟨hD'card_mem, hD'union, hD'disj⟩, hD'le⟩ := ih V' H' hV'_card hH'_U hH'_sub
    let Dtri : Finset (Finset α) := M.image fun e => insert v e
    let Dedge : Finset (Finset α) := U.image fun u => ({v, u} : Finset α)
    let D : Finset (Finset α) := D' ∪ Dtri ∪ Dedge
    have hS_H' : ∀ S ∈ D', S.powersetCard 2 ⊆ H' := by
      intro S hS e he
      rw [hD'union]
      exact Finset.mem_biUnion.mpr ⟨S, hS, he⟩
    have hDtri_sub_H : ∀ e ∈ M, (insert v e).powersetCard 2 ⊆ H := by
      intro e heM f hf
      rw [Finset.mem_powersetCard] at hf
      obtain ⟨hfsub, hfcard⟩ := hf
      have hecard : e.card = 2 := hU e (hMsubH heM)
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
      have hxA : x ∈ A := hMsubA _ heM (Finset.mem_insert_self x {y})
      have hyA : y ∈ A := hMsubA _ heM (by simp)
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hfcard
      have hp : p ∈ ({v, x, y} : Finset α) := hfsub (Finset.mem_insert_self p {q})
      have hq : q ∈ ({v, x, y} : Finset α) := hfsub (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
      · exact False.elim (hpq rfl)
      · exact (hN_mem hvV).mp hxA
      · exact (hN_mem hvV).mp hyA
      · rw [Finset.pair_comm]; exact (hN_mem hvV).mp hxA
      · exact False.elim (hpq rfl)
      · exact hMsubH heM
      · rw [Finset.pair_comm]; exact (hN_mem hvV).mp hyA
      · rw [Finset.pair_comm]; exact hMsubH heM
      · exact False.elim (hpq rfl)
    have hDedge_sub_H : ∀ u ∈ U, ({v, u} : Finset α).powersetCard 2 ⊆ H := by
      intro u huU f hf
      rw [Finset.mem_powersetCard] at hf
      have huA : u ∈ A := (Finset.mem_sdiff.mp huU).1
      have huv : v ≠ u := fun h => hv_not_A (h ▸ huA)
      have hcard2 : ({v, u} : Finset α).card = 2 := Finset.card_pair huv
      have hfeq : f = {v, u} := Finset.eq_of_subset_of_card_le hf.1 (by rw [hf.2, hcard2])
      rw [hfeq]
      exact (hN_mem hvV).mp huA
    have hD_card_mem : ∀ S ∈ D, S.card = 2 ∨ S.card = 3 := by
      intro S hS
      simp only [D, Finset.mem_union] at hS
      rcases hS with (hS | hS) | hS
      · exact hD'card_mem S hS
      · simp only [Dtri, Finset.mem_image] at hS
        obtain ⟨e, heM, rfl⟩ := hS
        have hvne : v ∉ e := fun hve => hv_not_A (hMsubA e heM hve)
        right
        rw [Finset.card_insert_of_notMem hvne, hU e (hMsubH heM)]
      · simp only [Dedge, Finset.mem_image] at hS
        obtain ⟨u, huU, rfl⟩ := hS
        have huv : v ≠ u := fun h => hv_not_A (h ▸ (Finset.mem_sdiff.mp huU).1)
        left
        exact Finset.card_pair huv
    have hD_union : H = D.biUnion (fun S => S.powersetCard 2) := by
      ext e
      rw [Finset.mem_biUnion]
      constructor
      · intro heH
        by_cases hve : v ∈ e
        · obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp (hU e heH)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hve
          have hpair_u : ∃ u ∈ A, ({x, y} : Finset α) = {v, u} := by
            rcases hve with hxv | hyv
            · exact ⟨y, (hN_mem hvV).mpr (hxv ▸ heH), by rw [hxv]⟩
            · exact ⟨x, (hN_mem hvV).mpr (by rw [Finset.pair_comm]; exact hyv ▸ heH),
                by rw [hyv, Finset.pair_comm]⟩
          obtain ⟨u, huA, hxy_eq⟩ := hpair_u
          rw [hxy_eq]
          by_cases huVM : u ∈ VM
          · rw [Finset.mem_biUnion] at huVM
            obtain ⟨e0, he0M, hue0⟩ := huVM
            refine ⟨insert v e0, Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ he0M)), ?_⟩
            rw [Finset.mem_powersetCard]
            refine ⟨?_, Finset.card_pair (fun h => hv_not_A (h ▸ huA))⟩
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_insert_self _ e0
            · exact Finset.mem_insert_of_mem hue0
          · have huU : u ∈ U := Finset.mem_sdiff.mpr ⟨huA, huVM⟩
            refine ⟨{v, u}, Finset.mem_union_right _ (Finset.mem_image_of_mem _ huU), ?_⟩
            rw [Finset.mem_powersetCard]
            exact ⟨Finset.Subset.refl _, Finset.card_pair (fun h => hv_not_A (h ▸ huA))⟩
        · by_cases heM : e ∈ M
          · refine ⟨insert v e, Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ heM)), ?_⟩
            rw [Finset.mem_powersetCard]
            exact ⟨Finset.subset_insert v e, hU e heH⟩
          · have heH' : e ∈ H' := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨heH, hve⟩, heM⟩
            rw [hD'union, Finset.mem_biUnion] at heH'
            obtain ⟨S, hSD', heS⟩ := heH'
            exact ⟨S, Finset.mem_union_left _ (Finset.mem_union_left _ hSD'), heS⟩
      · rintro ⟨S, hSD, heS⟩
        simp only [D, Finset.mem_union] at hSD
        rcases hSD with (hS | hS) | hS
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hS_H' S hS heS)).1).1
        · simp only [Dtri, Finset.mem_image] at hS
          obtain ⟨e0, he0M, rfl⟩ := hS
          exact hDtri_sub_H e0 he0M heS
        · simp only [Dedge, Finset.mem_image] at hS
          obtain ⟨u, huU, rfl⟩ := hS
          exact hDedge_sub_H u huU heS
    have hD_uniq : ∀ S ∈ D, ∀ T ∈ D, ∀ e, e ∈ S.powersetCard 2 → e ∈ T.powersetCard 2 → S = T := by
      have haux : ∀ S ∈ D, ∀ e, e ∈ S.powersetCard 2 →
          ((v ∉ e ∧ e ∉ M) → S ∈ D') ∧
          ((e ∈ M) → S = insert v e) ∧
          (∀ u ∈ A, e = {v, u} →
            (u ∈ U → S = {v, u}) ∧
            (∀ e0 ∈ M, u ∈ e0 → S = insert v e0)) := by
        intro S hSD e heS
        have hesub : e ⊆ S := (Finset.mem_powersetCard.mp heS).1
        have hecard : e.card = 2 := (Finset.mem_powersetCard.mp heS).2
        simp only [D, Finset.mem_union] at hSD
        refine ⟨?_, ?_, ?_⟩
        · rintro ⟨hvne, henotM⟩
          rcases hSD with (hS | hS) | hS
          · exact hS
          · simp only [Dtri, Finset.mem_image] at hS
            obtain ⟨e0, he0M, rfl⟩ := hS
            have hesub0 : e ⊆ e0 := fun w hw => by
              have := hesub hw
              rw [Finset.mem_insert] at this
              rcases this with rfl | h
              · exact False.elim (hvne hw)
              · exact h
            have heeq : e = e0 := Finset.eq_of_subset_of_card_le hesub0 (by rw [hecard, hU e0 (hMsubH he0M)])
            exact False.elim (henotM (heeq ▸ he0M))
          · simp only [Dedge, Finset.mem_image] at hS
            obtain ⟨u, huU, rfl⟩ := hS
            have huv : v ≠ u := fun h => hv_not_A (h ▸ (Finset.mem_sdiff.mp huU).1)
            have heeq : e = {v, u} := Finset.eq_of_subset_of_card_le hesub (by rw [hecard, Finset.card_pair huv])
            exact False.elim (hvne (heeq ▸ Finset.mem_insert_self v {u}))
        · intro heM
          have hvne : v ∉ e := fun hve => hv_not_A (hMsubA e heM hve)
          rcases hSD with (hS | hS) | hS
          · exact False.elim ((Finset.mem_sdiff.mp (hS_H' S hS heS)).2 heM)
          · simp only [Dtri, Finset.mem_image] at hS
            obtain ⟨e0, he0M, rfl⟩ := hS
            have hesub0 : e ⊆ e0 := fun w hw => by
              have := hesub hw
              rw [Finset.mem_insert] at this
              rcases this with rfl | h
              · exact False.elim (hvne hw)
              · exact h
            have heeq : e = e0 := Finset.eq_of_subset_of_card_le hesub0 (by rw [hecard, hU e0 (hMsubH he0M)])
            rw [heeq]
          · simp only [Dedge, Finset.mem_image] at hS
            obtain ⟨u, huU, rfl⟩ := hS
            have huv : v ≠ u := fun h => hv_not_A (h ▸ (Finset.mem_sdiff.mp huU).1)
            have heeq : e = {v, u} := Finset.eq_of_subset_of_card_le hesub (by rw [hecard, Finset.card_pair huv])
            exact False.elim (hvne (heeq ▸ Finset.mem_insert_self v {u}))
        · intro u huA heeq
          subst heeq
          have hv_in : v ∈ ({v, u} : Finset α) := Finset.mem_insert_self v {u}
          have huv : v ≠ u := fun h => hv_not_A (h ▸ huA)
          refine ⟨?_, ?_⟩
          · intro huU
            have huNotVM : u ∉ VM := (Finset.mem_sdiff.mp huU).2
            rcases hSD with (hS | hS) | hS
            · exact False.elim ((Finset.mem_filter.mp (Finset.mem_sdiff.mp (hS_H' S hS heS)).1).2 hv_in)
            · simp only [Dtri, Finset.mem_image] at hS
              obtain ⟨e0, he0M, rfl⟩ := hS
              have hu_in : u ∈ insert v e0 := hesub (by simp)
              rw [Finset.mem_insert] at hu_in
              rcases hu_in with h | h
              · exact False.elim (huv h.symm)
              · exact False.elim (huNotVM (Finset.mem_biUnion.mpr ⟨e0, he0M, h⟩))
            · simp only [Dedge, Finset.mem_image] at hS
              obtain ⟨u', hu'U, rfl⟩ := hS
              have huv' : v ≠ u' := fun h => hv_not_A (h ▸ (Finset.mem_sdiff.mp hu'U).1)
              exact (Finset.eq_of_subset_of_card_le hesub (by rw [hecard, Finset.card_pair huv'])).symm
          · intro e0 he0M hue0
            have huVM : u ∈ VM := Finset.mem_biUnion.mpr ⟨e0, he0M, hue0⟩
            rcases hSD with (hS | hS) | hS
            · exact False.elim ((Finset.mem_filter.mp (Finset.mem_sdiff.mp (hS_H' S hS heS)).1).2 hv_in)
            · simp only [Dtri, Finset.mem_image] at hS
              obtain ⟨e1, he1M, rfl⟩ := hS
              have hu_in : u ∈ insert v e1 := hesub (by simp)
              rw [Finset.mem_insert] at hu_in
              rcases hu_in with h | h
              · exact False.elim (huv h.symm)
              · have heq : e1 = e0 := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hMdisj he1M he0M hne) h hue0
                rw [heq]
            · simp only [Dedge, Finset.mem_image] at hS
              obtain ⟨u', hu'U, rfl⟩ := hS
              have huv' : v ≠ u' := fun h => hv_not_A (h ▸ (Finset.mem_sdiff.mp hu'U).1)
              have heq := Finset.eq_of_subset_of_card_le hesub (by rw [hecard, Finset.card_pair huv'])
              have hpair := pair_eq_iff heq
              rcases hpair with ⟨_, rfl⟩ | ⟨h1, _⟩
              · exact False.elim ((Finset.mem_sdiff.mp hu'U).2 huVM)
              · exact False.elim (huv' h1)
      intro S hSD T hTD e heS heT
      have heH : e ∈ H := by
        rw [hD_union, Finset.mem_biUnion]
        exact ⟨S, hSD, heS⟩
      by_cases hve : v ∈ e
      · obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp (hU e heH)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hve
        have hpair_u : ∃ u ∈ A, ({x, y} : Finset α) = {v, u} := by
          rcases hve with hxv | hyv
          · exact ⟨y, (hN_mem hvV).mpr (hxv ▸ heH), by rw [hxv]⟩
          · exact ⟨x, (hN_mem hvV).mpr (by rw [Finset.pair_comm]; exact hyv ▸ heH),
              by rw [hyv, Finset.pair_comm]⟩
        obtain ⟨u, huA, hxy_eq⟩ := hpair_u
        by_cases huVM : u ∈ VM
        · rw [Finset.mem_biUnion] at huVM
          obtain ⟨e0, he0M, hue0⟩ := huVM
          have hS := ((haux S hSD _ heS).2.2 u huA hxy_eq).2 e0 he0M hue0
          have hT := ((haux T hTD _ heT).2.2 u huA hxy_eq).2 e0 he0M hue0
          rw [hS, hT]
        · have huU : u ∈ U := Finset.mem_sdiff.mpr ⟨huA, huVM⟩
          have hS := ((haux S hSD _ heS).2.2 u huA hxy_eq).1 huU
          have hT := ((haux T hTD _ heT).2.2 u huA hxy_eq).1 huU
          rw [hS, hT]
      · by_cases heM : e ∈ M
        · rw [(haux S hSD e heS).2.1 heM, (haux T hTD e heT).2.1 heM]
        · have hSD' := (haux S hSD e heS).1 ⟨hve, heM⟩
          have hTD' := (haux T hTD e heT).1 ⟨hve, heM⟩
          by_contra hne
          exact Finset.disjoint_left.mp (hD'disj hSD' hTD' hne) heS heT
    have hD_disj : (D : Set (Finset α)).Pairwise fun S T => Disjoint (S.powersetCard 2) (T.powersetCard 2) := by
      intro S hSD T hTD hne
      rw [Finset.disjoint_left]
      intro e heS heT
      exact hne (hD_uniq S hSD T hTD e heS heT)
    have hD_card : D.card ≤ (m + 1) ^ 2 / 4 := by
      have h1 : D.card ≤ D'.card + Dtri.card + Dedge.card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have htri : Dtri.card ≤ M.card := Finset.card_image_le
      have hedge : Dedge.card ≤ d - 2 * M.card := by
        rw [← hU_card]
        exact Finset.card_image_le
      have hstep := turan_step m
      omega
    exact ⟨D, ⟨hD_card_mem, hD_union, hD_disj⟩, hD_card⟩

theorem h1_proof : OMA.R_Erdos719_erdos_719_R1.H1 := by
  intro n H hU
  obtain ⟨D, hD, hcard⟩ := egp_finset n (Finset.univ : Finset (Fin n)) H
    (by simp) hU (fun _ _ => Finset.subset_univ _)
  exact ⟨D, hD, le_trans hcard (quarter_le_cliqueExtremalNumber n)⟩

end OMA.P_Erdos719_H1

theorem OMA.solution : OMA.R_Erdos719_erdos_719_R1.H1 :=
  OMA.P_Erdos719_H1.h1_proof
