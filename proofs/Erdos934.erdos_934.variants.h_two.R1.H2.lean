import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1

/-!
# Erdős 934, the upper bound for distance two

Formalizes the upper bound of Fan R. K. Chung, András Gyárfás, Zsolt Tuza, and
William T. Trotter, *The maximum number of edges in 2K₂-free graphs of bounded degree*,
Discrete Mathematics 81 (1990), 129–135. The proof uses their clique-size cases and
dominating-clique argument with the uniform bound `4 * |E| ≤ 5 * D ^ 2`.
-/

open Erdos934 SimpleGraph Finset
open scoped Classical

namespace Research934

noncomputable section

variable {V : Type} [Fintype V] {G : SimpleGraph V}

private def Near (G : SimpleGraph V) (x y : V) : Prop := G.Adj x y ∨ x = y

private def NoFar (G : SimpleGraph V) : Prop :=
  ∀ {a b c d}, G.Adj a b → G.Adj c d →
    Near G a c ∨ Near G a d ∨ Near G b c ∨ Near G b d

private theorem noFar_of_not_hasFar (h : ¬ HasFarEdges G 2) : NoFar G := by
  intro a b c d hab hcd
  by_contra! hn
  apply h
  refine ⟨a, b, c, d, hab, hcd, ?_⟩
  intro x hx y hy
  have aux (u v : V) (huv : ¬ Near G u v) : (2 : ℕ∞) ≤ G.edist u v := by
    rw [← not_lt, ENat.lt_two_iff, edist_le_one_iff_adj_or_eq]
    exact huv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact aux _ _ hn.1
  · exact aux _ _ hn.2.1
  · exact aux _ _ hn.2.2.1
  · exact aux _ _ hn.2.2.2

private def nbr (G : SimpleGraph V) (S : Finset V) (x : V) : Finset V :=
  S.filter (G.Adj x)

private theorem mem_nbr {S : Finset V} {x y : V} :
    y ∈ nbr G S x ↔ y ∈ S ∧ G.Adj x y :=
  mem_filter

private theorem nbr_mono {S T : Finset V} (h : S ⊆ T) (x : V) :
    nbr G S x ⊆ nbr G T x := filter_subset_filter _ h

private theorem nbr_subset (S : Finset V) (x : V) : nbr G S x ⊆ S :=
  filter_subset _ _

private theorem card_nbr_univ (x : V) : (nbr G univ x).card = G.degree x := by
  congr 1
  ext y
  simp [mem_nbr, mem_neighborFinset]

private theorem card_nbr_le_degree (S : Finset V) (x : V) : (nbr G S x).card ≤ G.degree x := by
  rw [← card_nbr_univ]
  exact card_le_card (nbr_mono (subset_univ S) x)

private theorem nbr_union (S T : Finset V) (x : V) :
    nbr G (S ∪ T) x = nbr G S x ∪ nbr G T x := by
  ext y
  simp only [mem_nbr, mem_union]
  tauto

private theorem card_nbr_add (S T : Finset V) (hd : Disjoint S T) (x : V) :
    (nbr G (S ∪ T) x).card = (nbr G S x).card + (nbr G T x).card := by
  rw [nbr_union, card_union_of_disjoint]
  exact hd.mono (nbr_subset S x) (nbr_subset T x)

private theorem sum_nbr_comm (S T : Finset V) :
    ∑ x ∈ S, (nbr G T x).card = ∑ y ∈ T, (nbr G S y).card := by
  simp only [nbr, card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [adj_comm]

private theorem sum_nbr_weight (S : Finset V) (f : V → ℕ) :
    (∑ x ∈ S, ∑ y ∈ nbr G S x, (f x + f y)) =
      2 * ∑ x ∈ S, f x * (nbr G S x).card := by
  have hcomm : (∑ x ∈ S, ∑ y ∈ nbr G S x, f y) =
      ∑ x ∈ S, f x * (nbr G S x).card := by
    simp only [nbr, sum_filter, card_filter, Finset.mul_sum]
    rw [Finset.sum_comm (s := S) (t := S)]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [adj_comm]
    split <;> simp_all
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, add_comm, hcomm, two_mul,
    mul_comm, Nat.cast_id]

private theorem card_nbr_clique {K : Finset V} (hK : G.IsClique (K : Set V))
    {x : V} (hx : x ∈ K) : (nbr G K x).card = K.card - 1 := by
  have h : nbr G K x = K.erase x := by
    ext y
    simp only [mem_nbr, mem_erase]
    refine ⟨fun ⟨hy, he⟩ => ⟨he.ne.symm, hy⟩, fun ⟨he, hy⟩ => ⟨hy, ?_⟩⟩
    exact hK hx hy he.symm
  rw [h, card_erase_of_mem hx]

private theorem exists_hitting_vertex (hF : NoFar G) (A B : Finset V)
    (hd : Disjoint A B) (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (hB : B.Nonempty) :
    ∃ x ∈ B, ∀ p ∈ A, ∀ q ∈ B, G.Adj p q → G.Adj x p ∨ G.Adj x q := by
  obtain ⟨x, hx, hmax⟩ := exists_max_image B (fun z => (nbr G A z).card) hB
  refine ⟨x, hx, fun p hp q hq hpq => ?_⟩
  by_contra! hn
  have hsub : nbr G A x ⊆ nbr G A q := by
    intro t ht
    obtain ⟨htA, hxt⟩ := mem_nbr.mp ht
    refine mem_nbr.mpr ⟨htA, ?_⟩
    rcases hF hxt hpq with ⟨h | h⟩ | ⟨h | h⟩ | htp | htq
    · exact (hn.1 h).elim
    · exact (disjoint_left.1 hd hp (h ▸ hx)).elim
    · exact (hn.2 h).elim
    · exact (hn.1 (h ▸ hpq.symm)).elim
    · rcases htp with h | rfl
      · exact (hA t htA p hp h).elim
      · exact (hn.1 hxt).elim
    · rcases htq with h | rfl
      · exact h.symm
      · exact (disjoint_left.1 hd htA hq).elim
  have hstrict := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => by
    have hp' : p ∈ nbr G A q := mem_nbr.mpr ⟨hp, hpq.symm⟩
    exact hn.1 ((mem_nbr.mp (he.symm ▸ hp' : p ∈ nbr G A x)).2)⟩)
  exact (not_lt_of_ge (hmax q hq)) hstrict

private def dom (G : SimpleGraph V) (K : Finset V) : Finset V :=
  univ.filter fun v => v ∈ K ∨ ∃ u ∈ K, G.Adj u v

private theorem mem_dom {K : Finset V} {v : V} :
    v ∈ dom G K ↔ v ∈ K ∨ ∃ u ∈ K, G.Adj u v := by
  simp [dom]

private theorem clique_outside_exists_nonadj {K : Finset V} (hK : G.IsMaximumClique K)
    {y : V} (hy : y ∉ K) : ∃ x ∈ K, ¬ G.Adj y x := by
  by_contra! hn
  have hcl : G.IsClique ((insert y K : Finset V) : Set V) := by
    rw [coe_insert]
    exact hK.isClique.insert (fun b hb _ => hn b hb)
  have h := hK.maximum _ hcl
  rw [card_insert_of_notMem hy] at h
  exact (Nat.not_succ_le_self _) h

private theorem clique_nonadj_pair (hF : NoFar G) {K : Finset V} {y z : V}
    (hK : G.IsClique (K : Set V)) (hy : y ∉ K) (hz : z ∉ K)
    (hyz : G.Adj y z) :
    (K.filter (fun x => ¬ G.Adj y x ∧ ¬ G.Adj z x)).card ≤ 1 := by
  rw [card_le_one]
  intro x hx a ha
  obtain ⟨hxK, hxy, hxz⟩ := mem_filter.mp hx
  obtain ⟨haK, hay, haz⟩ := mem_filter.mp ha
  by_contra hne
  have hxa : G.Adj x a := hK hxK haK hne
  have hxy' : ¬ Near G y x := fun h => h.elim hxy (fun h => hy (h.symm ▸ hxK))
  have hay' : ¬ Near G y a := fun h => h.elim hay (fun h => hy (h.symm ▸ haK))
  have hxz' : ¬ Near G z x := fun h => h.elim hxz (fun h => hz (h.symm ▸ hxK))
  have haz' : ¬ Near G z a := fun h => h.elim haz (fun h => hz (h.symm ▸ haK))
  exact (hF hyz hxa).elim hxy' (fun h => h.elim hay' (fun h => h.elim hxz' haz'))

private theorem exists_dominating_maximum_clique (hF : NoFar G) (h3 : 3 ≤ G.cliqueNum) :
    ∃ K : Finset V, G.IsMaximumClique K ∧
      ∀ z, (∃ y, G.Adj z y) → z ∈ dom G K := by
  obtain ⟨K0, hK0⟩ := G.maximumClique_exists
  let M : Finset (Finset V) := univ.filter fun K => G.IsMaximumClique K
  have hM : M.Nonempty := ⟨K0, by simp [M, hK0]⟩
  obtain ⟨K, hKM, hmax⟩ := exists_max_image M (fun K => (dom G K).card) hM
  have hK : G.IsMaximumClique K := (mem_filter.mp hKM).2
  have hK3 : 3 ≤ K.card := G.maximumClique_card_eq_cliqueNum _ hK ▸ h3
  refine ⟨K, hK, ?_⟩
  rintro z ⟨y, hzy⟩
  by_contra hz
  have nzK : z ∉ K := fun h => hz (mem_dom.mpr (.inl h))
  have nz (v : V) (hv : v ∈ K) : ¬ G.Adj z v :=
    fun h => hz (mem_dom.mpr (.inr ⟨v, hv, h.symm⟩))
  have nyK : y ∉ K := fun h => nz y h hzy
  obtain ⟨x, hx, hyx⟩ := clique_outside_exists_nonadj hK nyK
  have hq (q : V) (hq : q ∈ K.erase x) : G.Adj y q := by
    have hKq := (mem_erase.mp hq).2
    by_contra hyq
    have h := clique_nonadj_pair hF hK.isClique nyK nzK hzy.symm
    rw [card_le_one] at h
    exact (mem_erase.mp hq).1
      (h q (mem_filter.mpr ⟨hKq, hyq, nz q hKq⟩) x
        (mem_filter.mpr ⟨hx, hyx, nz x hx⟩))
  let K' := insert y (K.erase x)
  have hK' : G.IsClique (K' : Set V) := by
    dsimp [K']
    rw [coe_insert]
    exact (hK.isClique.subset (show ((K.erase x : Finset V) : Set V) ⊆ K from
      fun _ h => (mem_erase.mp h).2)).insert (fun q h _ => hq q h)
  have hK'card : K'.card = K.card := by
    rw [show K' = insert y (K.erase x) from rfl, card_insert_of_notMem, card_erase_of_mem hx]
    · omega
    · exact fun h => nyK (mem_erase.mp h).2
  have hKM' : K' ∈ M := by
    simp only [M, mem_filter, mem_univ, true_and]
    exact ⟨hK', fun t ht => hK'card ▸ hK.maximum t ht⟩
  have htwo : 1 < (K.erase x).card := by rw [card_erase_of_mem hx]; omega
  obtain ⟨q, hqK', r, hrK', hqr⟩ := one_lt_card.mp htwo
  have qK := (mem_erase.mp hqK').2
  have rK := (mem_erase.mp hrK').2
  have qK' : q ∈ K' := mem_insert_of_mem hqK'
  have rK' : r ∈ K' := mem_insert_of_mem hrK'
  have xD' : x ∈ dom G K' :=
    mem_dom.mpr (.inr ⟨q, qK', hK.isClique qK hx (mem_erase.mp hqK').1⟩)
  have zD' : z ∈ dom G K' := mem_dom.mpr (.inr ⟨y, mem_insert_self _ _, hzy.symm⟩)
  have hsub : dom G K ⊆ dom G K' := by
    intro v hv
    by_contra hv'
    have nvK' : v ∉ K' := fun h => hv' (mem_dom.mpr (.inl h))
    have nv' (w : V) (hw : w ∈ K') : ¬ G.Adj w v :=
      fun h => hv' (mem_dom.mpr (.inr ⟨w, hw, h⟩))
    have nvK : v ∉ K := by
      intro hvK
      by_cases h : v = x
      · exact hv' (h.symm ▸ xD')
      · exact nvK' (mem_insert_of_mem (mem_erase.mpr ⟨h, hvK⟩))
    obtain ⟨w, hwK, hwv⟩ := (mem_dom.mp hv).resolve_left nvK
    have hwx : w = x := by
      by_contra h
      exact nv' w (mem_insert_of_mem (mem_erase.mpr ⟨h, hwK⟩)) hwv
    subst w
    have hzv : G.Adj z v := by
      rcases hF hzy hwv with h | h | h | h
      · exact (h.elim (nz x hx) (fun hz'x => nzK (hz'x.symm ▸ hx))).elim
      · exact h.elim id (fun h => (hz (h.symm ▸ hv)).elim)
      · exact (h.elim hyx (fun hy'x => nyK (hy'x.symm ▸ hx))).elim
      · exact (h.elim (nv' y (mem_insert_self _ _))
          (fun hy'v => nvK' (hy'v ▸ mem_insert_self _ _))).elim
    have fnear (u : V) (hu : u ∈ K) : ¬ Near G z u :=
      fun h => h.elim (nz u hu) (fun h => nzK (h.symm ▸ hu))
    have fnear' (u : V) (hu : u ∈ K) (hu' : u ∈ K') : ¬ Near G v u :=
      fun h => h.elim (fun h => nv' u hu' h.symm) (fun h => nvK (h.symm ▸ hu))
    rcases hF hzv (hK.isClique qK rK hqr) with h | h | h | h
    · exact fnear q qK h
    · exact fnear r rK h
    · exact fnear' q qK qK' h
    · exact fnear' r rK rK' h
  have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨hsub, fun h => hz (h.symm ▸ zD')⟩)
  exact (not_lt_of_ge (hmax K' hKM')) hlt

private def activeOutside (G : SimpleGraph V) (K : Finset V) : Finset V :=
  univ.filter fun v => v ∉ K ∧ ∃ w, G.Adj v w

private theorem mem_activeOutside {K : Finset V} {v : V} :
    v ∈ activeOutside G K ↔ v ∉ K ∧ ∃ w, G.Adj v w := by
  simp [activeOutside]

private theorem disjoint_activeOutside (K : Finset V) : Disjoint K (activeOutside G K) :=
  disjoint_left.mpr (fun _ hx hy => (mem_activeOutside.mp hy).1 hx)

private theorem degree_eq_nbr_add (K : Finset V) (x : V) :
    G.degree x = (nbr G K x).card + (nbr G (activeOutside G K) x).card := by
  rw [← card_nbr_univ, ← card_nbr_add _ _ (disjoint_activeOutside K)]
  congr 1
  ext y
  simp only [mem_nbr, mem_univ, true_and, mem_union, mem_activeOutside]
  constructor
  · intro h
    by_cases hy : y ∈ K
    · exact ⟨.inl hy, h⟩
    · exact ⟨.inr ⟨hy, x, h.symm⟩, h⟩
  · exact And.right

private theorem double_edges_parts {K : Finset V} (hK : G.IsClique (K : Set V)) :
    2 * G.edgeFinset.card =
      K.card * (K.card - 1) +
      2 * (∑ x ∈ K, (nbr G (activeOutside G K) x).card) +
      (∑ y ∈ activeOutside G K, (nbr G (activeOutside G K) y).card) := by
  let Y := activeOutside G K
  have hdegree (x : V) : G.degree x = (nbr G K x).card + (nbr G Y x).card :=
    degree_eq_nbr_add K x
  have hunion : ∑ x ∈ K ∪ Y, G.degree x = ∑ x : V, G.degree x := by
    apply sum_subset (subset_univ _)
    intro x _ hx
    simp only [mem_union, mem_activeOutside, Y, not_or] at hx
    exact (G.degree_eq_zero x).mpr (fun y hxy => hx.2 ⟨hx.1, y, hxy⟩)
  rw [← G.sum_degrees_eq_twice_card_edges, ← hunion, sum_union (disjoint_activeOutside K)]
  simp only [hdegree, sum_add_distrib]
  have hk : (∑ x ∈ K, (nbr G K x).card) = K.card * (K.card - 1) := by
    calc
      _ = ∑ _x ∈ K, (K.card - 1) := sum_congr rfl fun _ hx => card_nbr_clique hK hx
      _ = _ := by simp [nsmul_eq_mul]
  rw [hk, sum_nbr_comm (G := G) Y K, two_mul]
  simp only [Y, add_assoc]

private theorem cross_count_le {K : Finset V} (hK : G.IsClique (K : Set V))
    (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    (∑ x ∈ K, (nbr G (activeOutside G K) x).card) ≤ K.card * (D - (K.card - 1)) := by
  calc
    _ ≤ ∑ _x ∈ K, (D - (K.card - 1)) := by
      apply sum_le_sum
      intro x hx
      have h := hd x
      rw [degree_eq_nbr_add K, card_nbr_clique hK hx] at h
      omega
    _ = _ := by simp [nsmul_eq_mul]

private theorem clique_weight_lower (hF : NoFar G) {K : Finset V}
    (hK : G.IsClique (K : Set V)) {y z : V} (hy : y ∉ K) (hz : z ∉ K) (hyz : G.Adj y z) :
    K.card - 1 ≤ (nbr G K y).card + (nbr G K z).card := by
  let I := K.filter fun x => ¬ G.Adj y x ∧ ¬ G.Adj z x
  have hI : I.card ≤ 1 := clique_nonadj_pair hF hK hy hz hyz
  have h : K ⊆ (nbr G K y ∪ nbr G K z) ∪ I := by
    intro x hx
    simp only [mem_union, mem_nbr, I, mem_filter]
    tauto
  have hc := card_le_card h
  have hu := card_union_le (nbr G K y ∪ nbr G K z) I
  have hv := card_union_le (nbr G K y) (nbr G K z)
  omega

private theorem weight_upper (K : Finset V) (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    (∑ y ∈ activeOutside G K, (nbr G K y).card * (nbr G (activeOutside G K) y).card)
      ≤ (D - 1) * ∑ x ∈ K, (nbr G (activeOutside G K) x).card := by
  rw [sum_nbr_comm (G := G) K (activeOutside G K), Finset.mul_sum]
  apply sum_le_sum
  intro y _
  by_cases h : (nbr G K y).card = 0
  · simp [h]
  · rw [mul_comm (D - 1)]
    apply Nat.mul_le_mul_left
    have hy := hd y
    rw [degree_eq_nbr_add K] at hy
    omega

private theorem large_clique_bound (hF : NoFar G) {K : Finset V}
    (hK : G.IsClique (K : Set V)) (h5 : 5 ≤ K.card) (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    4 * G.edgeFinset.card ≤ 5 * D ^ 2 := by
  let Y := activeOutside G K
  let c := ∑ x ∈ K, (nbr G Y x).card
  let l := ∑ y ∈ Y, (nbr G Y y).card
  let k := K.card
  let w := ∑ y ∈ Y, (nbr G K y).card * (nbr G Y y).card
  have hE : 2 * G.edgeFinset.card = k * (k - 1) + 2 * c + l := double_edges_parts hK
  have hC : c ≤ k * (D - (k - 1)) := cross_count_le hK D hd
  have hW : w ≤ (D - 1) * c := weight_upper K D hd
  have hl : (k - 1) * l ≤ 2 * w := by
    rw [Finset.mul_sum, ← sum_nbr_weight Y (fun y => (nbr G K y).card)]
    apply sum_le_sum
    intro y hy
    have hconst : (k - 1) * (nbr G Y y).card = ∑ _z ∈ nbr G Y y, (k - 1) := by simp [mul_comm]
    rw [hconst]
    apply sum_le_sum
    intro z hz
    obtain ⟨hz, hyz⟩ := mem_nbr.mp hz
    exact clique_weight_lower hF hK (mem_activeOutside.mp hy).1 (mem_activeOutside.mp hz).1 hyz
  have hk : k - 1 ≤ D := by
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < K.card)
    exact (card_nbr_clique hK hx) ▸ (card_nbr_le_degree K x).trans (hd x)
  have hkn : 5 ≤ k := h5
  have hDn : 4 ≤ D := by omega
  -- Multiplying by the positive `k-1` avoids any division.
  let q := k - 1
  have hq : k = q + 1 := by dsimp [q]; omega
  have hqD : q ≤ D := hk
  have hq4 : 4 ≤ q := by dsimp [q]; omega
  change q * l ≤ 2 * w at hl
  have hC' : c ≤ k * (D - q) := hC
  have hW' : w ≤ (D - 1) * c := hW
  have hD1 : D - 1 + 1 = D := by omega
  have hDq : D - q + q = D := by omega
  have ha : 2 * q * G.edgeFinset.card = k * q * q + 2 * q * c + q * l := by
    change 2 * G.edgeFinset.card = k * q + 2 * c + l at hE
    calc
      _ = q * (2 * G.edgeFinset.card) := by ring
      _ = q * (k * q + 2 * c + l) := by rw [hE]
      _ = _ := by ring
  have hb := calc
    2 * q * G.edgeFinset.card ≤ k * q * q + 2 * q * c + 2 * w := by omega
    _ ≤ k * q * q + 2 * q * c + 2 * ((D - 1) * c) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hW') _
    _ = k * q * q + 2 * (q + (D - 1)) * c := by ring
    _ ≤ k * q * q + 2 * (q + (D - 1)) * (k * (D - q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hC') _
  have hc : k * q * q + 2 * (q + (D - 1)) * (k * (D - q))
      ≤ 2 * k * D ^ 2 := by
    have hm : q + (D - 1) ≤ q + D := Nat.add_le_add_left (Nat.sub_le D 1) q
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (k * (D - q)) (Nat.mul_le_mul_left 2 hm)) _)
    have he : k * q * q + 2 * (q + D) * (k * (D - q)) + k * q * q = 2 * k * D ^ 2 := by
      generalize (D - q) = r at hDq ⊢
      rw [← hDq]
      ring
    omega
  have hqk : 4 * k ≤ 5 * q := by omega
  have hf : (4 * G.edgeFinset.card) * q ≤ (5 * D ^ 2) * q := by
    have he := Nat.mul_le_mul_right (D ^ 2) hqk
    calc
      _ = 2 * (2 * q * G.edgeFinset.card) := by ring
      _ ≤ 2 * (2 * k * D ^ 2) := Nat.mul_le_mul_left _ (hb.trans hc)
      _ = (4 * k) * D ^ 2 := by ring
      _ ≤ (5 * q) * D ^ 2 := he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hf (by omega)

private theorem sum_degrees_of_cover (S : Finset V)
    (hs : ∀ x y, G.Adj x y → x ∈ S) :
    (∑ x ∈ S, G.degree x) = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  apply sum_subset (subset_univ _)
  intro x _ hx
  exact (G.degree_eq_zero x).mpr (fun y h => hx (hs x y h))

private theorem degree_eq_nbr_of_all {S : Finset V} {x : V}
    (hs : ∀ y, G.Adj x y → y ∈ S) : G.degree x = (nbr G S x).card := by
  rw [← card_nbr_univ]
  congr 1
  ext y
  simp only [mem_nbr, mem_univ, true_and]
  exact ⟨fun h => ⟨hs y h, h⟩, And.right⟩

private theorem bipartition_bound (hF : NoFar G) (D : ℕ) (hd : ∀ v, G.degree v ≤ D)
    (A B : Finset V) (hdj : Disjoint A B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hcover : ∀ x y, G.Adj x y → x ∈ A ∪ B) (hactive : ∀ x ∈ A, ∃ y, G.Adj x y)
    (hne : B.Nonempty) :
    G.edgeFinset.card ≤ D ^ 2 := by
  have hab (x : V) (hx : x ∈ A) : G.degree x = (nbr G B x).card :=
    degree_eq_nbr_of_all fun y hxy =>
      (mem_union.mp (hcover y x hxy.symm)).resolve_left (fun hy => hA x hx y hy hxy)
  have hba (x : V) (hx : x ∈ B) : G.degree x = (nbr G A x).card :=
    degree_eq_nbr_of_all fun y hxy =>
      (mem_union.mp (hcover y x hxy.symm)).resolve_right (fun hy => hB x hx y hy hxy)
  obtain ⟨b, hb, hhit⟩ := exists_hitting_vertex hF A B hdj hA hne
  have hincl : A ⊆ G.neighborFinset b := by
    intro x hx
    obtain ⟨y, hxy⟩ := hactive x hx
    have hy := (mem_union.mp (hcover y x hxy.symm)).resolve_left
      (fun hy => hA x hx y hy hxy)
    rw [mem_neighborFinset]
    exact (hhit x hx y hy hxy).resolve_right (hB b hb y hy)
  have hcard : A.card ≤ D := (card_le_card hincl).trans (hd b)
  have hsum : (∑ x ∈ A, G.degree x) = G.edgeFinset.card := by
    have hall := sum_degrees_of_cover (A ∪ B) hcover
    rw [sum_union hdj, sum_congr rfl hab, sum_congr rfl hba, sum_nbr_comm B A] at hall
    rw [sum_congr rfl hab]
    omega
  have hs : (∑ x ∈ A, G.degree x) ≤ A.card * D :=
    (sum_le_sum (fun x _ => hd x)).trans_eq (by simp [nsmul_eq_mul])
  rw [← hsum, pow_two]
  exact hs.trans (Nat.mul_le_mul_right _ hcard)

private theorem noTriangle {a b c : V} (hT : G.CliqueFree 3)
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c := by
  intro hbc
  exact hT {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

private def cycleAdj (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i

private instance (i j : Fin 5) : Decidable (cycleAdj i j) :=
  inferInstanceAs (Decidable (i + 1 = j ∨ j + 1 = i))

private def FiveCycle (G : SimpleGraph V) : Prop :=
  ∃ c : Fin 5 → V, Function.Injective c ∧ ∀ i j, G.Adj (c i) (c j) ↔ cycleAdj i j

private theorem triangleFree_without_fiveCycle (hF : NoFar G) (hT : G.CliqueFree 3)
    (hc : ¬ FiveCycle G) (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    G.edgeFinset.card ≤ D ^ 2 := by
  by_cases h : ∃ u v, G.Adj u v
  · obtain ⟨u, v, huv⟩ := h
    let Z := univ.filter fun z => ¬ G.Adj u z ∧ ¬ G.Adj v z
    let X := univ.filter fun z => z ∈ Z ∧ ∃ b, G.Adj v b ∧ G.Adj b z
    let Y := univ.filter fun z => z ∈ Z ∧ ∃ a, G.Adj u a ∧ G.Adj a z
    let A := G.neighborFinset u ∪ X
    let B := G.neighborFinset v ∪ Y
    have mz (z : V) : z ∈ Z ↔ ¬ G.Adj u z ∧ ¬ G.Adj v z := by simp [Z]
    have mx (z : V) : z ∈ X ↔ z ∈ Z ∧ ∃ b, G.Adj v b ∧ G.Adj b z := by simp [X]
    have my (z : V) : z ∈ Y ↔ z ∈ Z ∧ ∃ a, G.Adj u a ∧ G.Adj a z := by simp [Y]
    have zstable (z w : V) (hz : z ∈ Z) (hw : w ∈ Z) : ¬ G.Adj z w := by
      intro hzw
      have nz : z ≠ u := fun h => (mz z |>.mp hz).2 (h.symm ▸ huv.symm)
      have nz' : z ≠ v := fun h => (mz z |>.mp hz).1 (h.symm ▸ huv)
      have nw : w ≠ u := fun h => (mz w |>.mp hw).2 (h.symm ▸ huv.symm)
      have nw' : w ≠ v := fun h => (mz w |>.mp hw).1 (h.symm ▸ huv)
      rcases hF hzw huv with h | h | h | h
      · exact h.elim (fun e => (mz z |>.mp hz).1 e.symm) nz
      · exact h.elim (fun e => (mz z |>.mp hz).2 e.symm) nz'
      · exact h.elim (fun e => (mz w |>.mp hw).1 e.symm) nw
      · exact h.elim (fun e => (mz w |>.mp hw).2 e.symm) nw'
    have exclusive (z : V) (hz : z ∈ Z)
        (ax : ∃ a, G.Adj u a ∧ G.Adj a z) (bx : ∃ b, G.Adj v b ∧ G.Adj b z) : False := by
      obtain ⟨a, hua, haz⟩ := ax
      obtain ⟨b, hvb, hbz⟩ := bx
      obtain ⟨huz, hvz⟩ := (mz z).mp hz
      have hva := noTriangle hT huv hua
      have hab := noTriangle hT haz.symm hbz.symm
      have huv' := huv.ne
      have hun' := hua.ne
      have hvb' := hvb.ne
      have haz' := haz.ne
      have hbz' := hbz.ne
      apply hc
      let c : Fin 5 → V := ![u, v, b, z, a]
      have hub' : ¬ G.Adj u b := fun h => (noTriangle hT huv h hvb)
      have hzu : z ≠ u := fun h => hvz (h.symm ▸ huv.symm)
      have hzv : z ≠ v := fun h => huz (h.symm ▸ huv)
      have hbu : b ≠ u := fun h => huz (h ▸ hbz)
      have hav : a ≠ v := fun h => hvz (h ▸ haz)
      have hab' : a ≠ b := fun h => hva (h.symm ▸ hvb)
      have ch : ∀ i j, G.Adj (c i) (c j) ↔ cycleAdj i j := by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [c, cycleAdj, huv, huv.symm, hua, hua.symm, hvb, hvb.symm,
            haz, haz.symm, hbz, hbz.symm, hub', hva, huz, hvz, hab, adj_comm]
      refine ⟨c, ?_, ch⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [c, ne_comm]
    have hdn : ∀ x, ¬ (G.Adj u x ∧ G.Adj v x) :=
      fun x ⟨hux, hvx⟩ => noTriangle hT huv hux hvx
    have am (x : V) : x ∈ A ↔ G.Adj u x ∨ x ∈ X := by simp [A]
    have bm (x : V) : x ∈ B ↔ G.Adj v x ∨ x ∈ Y := by simp [B]
    have xa (x : V) (hx : x ∈ X) (y : V) (hy : G.Adj u y) : ¬ G.Adj y x := by
      obtain ⟨hxZ, hh⟩ := (mx x).mp hx
      exact fun e => exclusive x hxZ ⟨y, hy, e⟩ hh
    have yb (x : V) (hx : x ∈ Y) (y : V) (hy : G.Adj v y) : ¬ G.Adj y x := by
      obtain ⟨hxZ, hh⟩ := (my x).mp hx
      exact fun e => exclusive x hxZ hh ⟨y, hy, e⟩
    have hdj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x ha hb
      rcases (am x).mp ha with hu | hx <;> rcases (bm x).mp hb with hv | hy
      · exact hdn x ⟨hu, hv⟩
      · exact ((mz x).mp ((my x).mp hy).1).1 hu
      · exact ((mz x).mp ((mx x).mp hx).1).2 hv
      · exact exclusive x ((mx x).mp hx).1 ((my x).mp hy).2 ((mx x).mp hx).2
    refine bipartition_bound hF D hd A B hdj ?_ ?_ ?_ ?_ ⟨u, (bm u).mpr (.inl huv.symm)⟩
    · intro x hx y hy
      rcases (am x).mp hx with hu | hx' <;> rcases (am y).mp hy with hu' | hy'
      · exact noTriangle hT hu hu'
      · exact xa y hy' x hu
      · exact fun h => xa x hx' y hu' h.symm
      · exact zstable x y ((mx x).mp hx').1 ((mx y).mp hy').1
    · intro x hx y hy
      rcases (bm x).mp hx with hv | hx' <;> rcases (bm y).mp hy with hv' | hy'
      · exact noTriangle hT hv hv'
      · exact yb y hy' x hv
      · exact fun h => yb x hx' y hv' h.symm
      · exact zstable x y ((my x).mp hx').1 ((my y).mp hy').1
    · intro x y hxy
      rw [mem_union, am, bm]
      by_cases hu : G.Adj u x
      · exact .inl (.inl hu)
      by_cases hv : G.Adj v x
      · exact .inr (.inl hv)
      have hz : x ∈ Z := (mz x).mpr ⟨hu, hv⟩
      by_cases hyu : G.Adj u y
      · exact .inr (.inr ((my x).mpr ⟨hz, y, hyu, hxy.symm⟩))
      by_cases hyv : G.Adj v y
      · exact .inl (.inr ((mx x).mpr ⟨hz, y, hyv, hxy.symm⟩))
      exact (zstable x y hz ((mz y).mpr ⟨hyu, hyv⟩) hxy).elim
    · intro x hx
      rcases (am x).mp hx with hu | hx
      · exact ⟨u, hu.symm⟩
      · obtain ⟨_, y, _, hxy⟩ := (mx x).mp hx
        exact ⟨y, hxy.symm⟩
  · have hz (x : V) : G.degree x = 0 :=
      (G.degree_eq_zero x).mpr (fun y hxy => h ⟨x, y, hxy⟩)
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hz, Finset.sum_const_zero] at hsum
    omega

private theorem fiveCycle_bound (hF : NoFar G) (hT : G.CliqueFree 3)
    (hc : FiveCycle G) (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    4 * G.edgeFinset.card ≤ 5 * D ^ 2 := by
  obtain ⟨c, hinj, hc⟩ := hc
  have next (i : Fin 5) : G.Adj (c i) (c (i+1)) := (hc _ _).2 (.inl rfl)
  have opp (i : Fin 5) : G.Adj (c (i+2)) (c (i+3)) := by
    apply (hc _ _).2
    left
    fin_cases i <;> decide
  have hnon (i : Fin 5) : ¬ cycleAdj i (i+2) ∧ ¬ cycleAdj i (i+3) := by
    fin_cases i <;> decide
  have far (i : Fin 5) : ¬ Near G (c i) (c (i+2)) ∧ ¬ Near G (c i) (c (i+3)) := by
    have hne (j : Fin 5) (h : i ≠ j) (hn : ¬ cycleAdj i j) : ¬ Near G (c i) (c j) :=
      fun h' => h'.elim (fun h' => hn ((hc _ _).1 h')) (fun h' => h (hinj h'))
    exact ⟨hne _ (by fin_cases i <;> decide) (hnon i).1,
      hne _ (by fin_cases i <;> decide) (hnon i).2⟩
  have hfinite₀ :
      ∀ f : Fin 5 → Bool,
        (∀ i, ¬ (f i = true ∧ f (i+1) = true)) →
        ¬ (∀ i, f i = true ∨ f (i+1) = true) := by decide +kernel
  have hfinite₁ :
      ∀ f : Fin 5 → Bool,
        (∃ i, f i = true) →
        (∀ i, ¬ (f i = true ∧ f (i+1) = true)) →
        (∀ i, f i = true → f (i+2) = true ∨ f (i+3) = true) →
        ∃ j, ∀ k, f k = true ↔ cycleAdj j k := by decide +kernel
  have hdifferent : ∀ i j : Fin 5, (∀ k, cycleAdj i k ↔ cycleAdj j k) → i = j := by decide +kernel
  let A (i : Fin 5) := univ.filter fun x => ∀ k, G.Adj x (c k) ↔ cycleAdj i k
  have hA (x : V) (i : Fin 5) :
      x ∈ A i ↔ ∀ k, G.Adj x (c k) ↔ cycleAdj i k := by simp [A]
  have hinder (w : V) (i : Fin 5) : ¬ (G.Adj w (c i) ∧ G.Adj w (c (i+1))) :=
    fun ⟨h, h'⟩ => noTriangle hT h h' (next i)
  have covered (x y : V) (hxy : G.Adj x y) : ∃ i, x ∈ A i := by
    have hadj : ∃ i, G.Adj x (c i) := by
      by_contra! hn
      have neq (i : Fin 5) : x ≠ c i := fun h => hn (i+1) (h ▸ next i)
      have neq' (i : Fin 5) : y ≠ c i := fun h => hn i (h ▸ hxy)
      have each (i : Fin 5) : G.Adj y (c i) ∨ G.Adj y (c (i+1)) := by
        rcases hF hxy (next i) with h | h | h | h
        · exact (h.elim (hn i) (neq i)).elim
        · exact (h.elim (hn (i+1)) (neq (i+1))).elim
        · exact .inl (h.elim id (fun he => (neq' i he).elim))
        · exact .inr (h.elim id (fun he => (neq' (i+1) he).elim))
      apply hfinite₀ (fun i => decide (G.Adj y (c i)))
      · simpa only [decide_eq_true_eq] using hinder y
      · simpa only [decide_eq_true_eq] using each
    have prefer (i : Fin 5) (hxi : G.Adj x (c i)) : G.Adj x (c (i+2)) ∨ G.Adj x (c (i+3)) := by
      rcases hF hxi (opp i) with h | h | h | h
      · exact .inl (h.elim id (fun he => ((far i).1 (.inl (he ▸ hxi).symm)).elim))
      · exact .inr (h.elim id (fun he => ((far i).2 (.inl (he ▸ hxi).symm)).elim))
      · exact ((far i).1 h).elim
      · exact ((far i).2 h).elim
    obtain ⟨i, hi⟩ := hfinite₁ (fun i => decide (G.Adj x (c i)))
      (by simpa only [decide_eq_true_eq] using hadj)
      (by simpa only [decide_eq_true_eq] using hinder x)
      (by simpa only [decide_eq_true_eq] using prefer)
    exact ⟨i, (hA x i).2 (by simpa only [decide_eq_true_eq] using hi)⟩
  have disj {i j : Fin 5} (hij : i ≠ j) : Disjoint (A i) (A j) := by
    rw [Finset.disjoint_left]
    intro x hi hj
    exact hij (hdifferent i j fun k => ((hA x i).1 hi k).symm.trans ((hA x j).1 hj k))
  let S := (univ : Finset (Fin 5)).biUnion A
  have Scover (x y : V) (h : G.Adj x y) : x ∈ S := by
    obtain ⟨i, hi⟩ := covered x y h
    exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  have Scard : S.card = ∑ i : Fin 5, (A i).card :=
    card_biUnion fun i _ j _ hij => disj hij
  have bound (i : Fin 5) : (A i).card + (A (i+2)).card ≤ D := by
    have hsub : A i ∪ A (i+2) ⊆ G.neighborFinset (c (i+1)) := by
      intro z hz
      rw [mem_neighborFinset]
      rcases mem_union.mp hz with hz | hz
      · exact ((hA z i).1 hz (i+1) |>.2 (.inl rfl)).symm
      · exact ((hA z (i+2)).1 hz (i+1) |>.2 (.inr (by fin_cases i <;> decide))).symm
    rw [← card_union_of_disjoint (disj (show i ≠ i+2 by fin_cases i <;> decide))]
    exact (card_le_card hsub).trans (hd (c (i+1)))
  have hsum : 2 * S.card ≤ 5 * D := by
    calc
      2 * S.card = ∑ i : Fin 5, ((A i).card + (A (i+2)).card) := by
        rw [Scard, sum_add_distrib, two_mul]
        congr 1
        let p : Fin 5 ≃ Fin 5 :=
          ⟨fun i => i + 2, fun i => i + 3, by intro i; fin_cases i <;> decide,
            by intro i; fin_cases i <;> decide⟩
        exact (Equiv.sum_comp p (fun i => (A i).card)).symm
      _ ≤ ∑ _i : Fin 5, D := sum_le_sum fun i _ => bound i
      _ = _ := by simp
  have hedge : 2 * G.edgeFinset.card ≤ S.card * D := by
    rw [← sum_degrees_of_cover S Scover]
    calc
      _ ≤ ∑ _x ∈ S, D := sum_le_sum fun x _ => hd x
      _ = _ := by simp
  calc
    4 * G.edgeFinset.card = 2 * (2 * G.edgeFinset.card) := by ring
    _ ≤ 2 * (S.card * D) := Nat.mul_le_mul_left _ hedge
    _ = (2 * S.card) * D := by ring
    _ ≤ (5 * D) * D := Nat.mul_le_mul_right _ hsum
    _ = _ := by ring

private theorem card_nbr_pos_of_dom {K : Finset V}
    (hdom : ∀ y, (∃ z, G.Adj y z) → y ∈ dom G K) {y : V} (hy : y ∈ activeOutside G K) :
    0 < (nbr G K y).card := by
  obtain ⟨hyK, hex⟩ := mem_activeOutside.mp hy
  obtain ⟨x, hxK, hxy⟩ := (mem_dom.mp (hdom y hex)).resolve_left hyK
  exact card_pos.mpr ⟨x, mem_nbr.mpr ⟨hxK, hxy.symm⟩⟩

private theorem sum_nbr_indicator {Y A B : Finset V} (hA : A ⊆ Y) (hB : B ⊆ Y) :
    (∑ x ∈ Y, ∑ y ∈ nbr G Y x, if x ∈ A ∧ y ∈ B then (1 : ℕ) else 0) =
      ∑ x ∈ A, (nbr G B x).card := by
  have hre (x : V) : (∑ y ∈ nbr G Y x, if x ∈ A ∧ y ∈ B then (1 : ℕ) else 0) =
      if x ∈ A then (nbr G B x).card else 0 := by
    by_cases hx : x ∈ A
    · simp only [hx, true_and, if_true, ← card_filter]
      congr 1
      ext y
      simp only [mem_filter, mem_nbr]
      exact ⟨fun ⟨⟨_, h⟩, hy⟩ => ⟨hy, h⟩, fun ⟨hy, h⟩ => ⟨⟨hB hy, h⟩, hy⟩⟩
    · simp [hx]
  simp_rw [hre, ← sum_filter]
  congr 1
  ext x
  simp only [mem_filter]
  exact ⟨And.right, fun hx => ⟨hA hx, hx⟩⟩

private theorem cut_count_of_hit {A B : Finset V} {x : V}
    (hhit : ∀ p ∈ A, ∀ q ∈ B, G.Adj p q → G.Adj x p ∨ G.Adj x q) :
    (∑ p ∈ A, (nbr G B p).card) ≤
      (∑ p ∈ nbr G A x, (nbr G B p).card) +
      (∑ q ∈ nbr G B x, (nbr G A q).card) := by
  let S := A.filter fun p => ¬ G.Adj x p
  have hsplit : (∑ p ∈ A, (nbr G B p).card) =
      (∑ p ∈ nbr G A x, (nbr G B p).card) + (∑ p ∈ S, (nbr G B p).card) := by
    exact (Finset.sum_filter_add_sum_filter_not A (G.Adj x) _).symm
  rw [hsplit]
  apply Nat.add_le_add_left
  have hres (p : V) (hp : p ∈ S) : nbr G B p = nbr G (nbr G B x) p := by
    ext q
    simp only [mem_nbr]
    obtain ⟨hpA, hxp⟩ := mem_filter.mp hp
    exact ⟨fun ⟨hq, hpq⟩ => ⟨⟨hq, (hhit p hpA q hq hpq).resolve_left hxp⟩, hpq⟩,
      fun ⟨⟨hq, _⟩, hpq⟩ => ⟨hq, hpq⟩⟩
  rw [sum_congr rfl (fun p hp => congrArg Finset.card (hres p hp)), sum_nbr_comm (G := G)]
  apply sum_le_sum
  intro q _
  exact card_le_card (nbr_mono (filter_subset _ _) q)

private theorem four_clique_bound (hF : NoFar G) {K : Finset V}
    (hK : G.IsClique (K : Set V)) (h4 : K.card = 4)
    (hdom : ∀ y, (∃ z, G.Adj y z) → y ∈ dom G K)
    (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    4 * G.edgeFinset.card ≤ 5 * D ^ 2 := by
  let Y := activeOutside G K
  let f (x : V) := (nbr G K x).card
  let A := Y.filter fun x => f x = 1
  let B := Y.filter fun x => f x = 2
  let c := ∑ x ∈ K, (nbr G Y x).card
  let l := ∑ y ∈ Y, (nbr G Y y).card
  let w := ∑ y ∈ Y, f y * (nbr G Y y).card
  let e3 := ∑ y ∈ A, (nbr G B y).card
  have hE : 2 * G.edgeFinset.card = 12 + 2 * c + l := by
    simpa only [h4] using (double_edges_parts hK)
  have hC : c ≤ 4 * (D - 3) := by simpa only [h4] using (cross_count_le hK D hd)
  have hW : w ≤ (D - 1) * c := weight_upper K D hd
  have subA : A ⊆ Y := filter_subset _ _
  have subB : B ⊆ Y := filter_subset _ _
  have memA {x : V} : x ∈ A ↔ x ∈ Y ∧ f x = 1 := mem_filter
  have memB {x : V} : x ∈ B ↔ x ∈ Y ∧ f x = 2 := mem_filter
  have disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have ha := (memA.mp hx).2
    have hb := (memB.mp hy).2
    omega
  have Wlower {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) (hyz : G.Adj y z) : 3 ≤ f y + f z := by
    simpa only [h4] using
      clique_weight_lower hF hK (mem_activeOutside.mp hy).1 (mem_activeOutside.mp hz).1 hyz
  have hstable (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ A) : ¬ G.Adj x y := by
    intro h
    have h' := Wlower (subA hx) (subA hy) h
    rw [(memA.mp hx).2, (memA.mp hy).2] at h'
    omega
  have hkD : 3 ≤ D := by
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < K.card)
    have hxcard := card_nbr_clique hK hx
    have h' := (card_nbr_le_degree K x).trans (hd x)
    omega
  have compare (y : V) (hy : y ∈ Y) (z : V) (hz : z ∈ nbr G Y y) :
      4 ≤ f y + f z + (if y ∈ A ∧ z ∈ B then 1 else 0) +
        (if y ∈ B ∧ z ∈ A then 1 else 0) := by
    obtain ⟨hzY, hyz⟩ := mem_nbr.mp hz
    have h := Wlower hy hzY hyz
    by_cases he : f y + f z = 3
    · have hy' : 0 < f y := card_nbr_pos_of_dom hdom hy
      have hz' : 0 < f z := card_nbr_pos_of_dom hdom hzY
      have hcases : (f y = 1 ∧ f z = 2) ∨ (f y = 2 ∧ f z = 1) := by omega
      rcases hcases with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> simp [memA, memB, hy, hzY, hu, hv]
    · have hab : 4 ≤ f y + f z := by omega
      omega
  have hl : 4 * l ≤ 2 * w + 2 * e3 := by
    have hcompare : 4 * l ≤ ∑ y ∈ Y, ∑ z ∈ nbr G Y y,
        (f y + f z + (if y ∈ A ∧ z ∈ B then 1 else 0) + (if y ∈ B ∧ z ∈ A then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro y hy
      have hn : 4 * (nbr G Y y).card = ∑ _z ∈ nbr G Y y, (4 : ℕ) := by simp [mul_comm]
      rw [hn]
      exact sum_le_sum (compare y hy)
    simp only [sum_add_distrib] at hcompare
    have hw := sum_nbr_weight (G := G) Y f
    simp only [sum_add_distrib] at hw
    rw [hw, sum_nbr_indicator subA subB] at hcompare
    rw [sum_nbr_indicator subB subA, sum_nbr_comm (G := G) B A] at hcompare
    change 4 * l ≤ 2 * w + e3 + e3 at hcompare
    omega
  have he3 : e3 ≤ (D - 2) * (D - 1) := by
    by_cases hB : B.Nonempty
    · obtain ⟨x, hx, hhit⟩ := exists_hitting_vertex hF A B disj hstable hB
      have total : (nbr G A x).card + (nbr G B x).card ≤ D - 2 := by
        rw [← card_nbr_add A B disj]
        have hle := card_le_card (nbr_mono (G := G) (union_subset subA subB) x)
        have hdx := hd x
        rw [degree_eq_nbr_add K] at hdx
        change f x + (nbr G Y x).card ≤ D at hdx
        rw [(memB.mp hx).2] at hdx
        omega
      have low (T : Finset V) (hT : T ⊆ Y) {y : V} (hy : y ∈ Y) : (nbr G T y).card ≤ D - 1 := by
        have hle := card_le_card (nbr_mono (G := G) hT y)
        have hdy := hd y
        have hpos := card_nbr_pos_of_dom hdom hy
        rw [degree_eq_nbr_add K] at hdy
        change (nbr G K y).card + (nbr G Y y).card ≤ D at hdy
        omega
      calc
        e3 ≤ (∑ p ∈ nbr G A x, (nbr G B p).card) +
            (∑ q ∈ nbr G B x, (nbr G A q).card) := cut_count_of_hit hhit
        _ ≤ (∑ _p ∈ nbr G A x, (D - 1)) + (∑ _q ∈ nbr G B x, (D - 1)) :=
          Nat.add_le_add (sum_le_sum (fun p hp => low B subB (subA (mem_nbr.mp hp).1)))
            (sum_le_sum (fun q hq => low A subA (subB (mem_nbr.mp hq).1)))
        _ = ((nbr G A x).card + (nbr G B x).card) * (D - 1) := by simp [Nat.add_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ total
    · have hz := not_nonempty_iff_eq_empty.mp hB
      simp [e3, hz, nbr]
  have hD1 : D - 1 + 1 = D := by omega
  have hD2 : D - 2 + 2 = D := by omega
  have hD3 : D - 3 + 3 = D := by omega
  have hwC := hW.trans (Nat.mul_le_mul_left (D - 1) hC)
  have leading := calc
    8 * G.edgeFinset.card ≤ 48 + 8 * c + 2 * w + 2 * e3 := by omega
    _ ≤ 48 + 8 * (4 * (D - 3)) + 2 * ((D - 1) * (4 * (D - 3))) +
        2 * ((D - 2) * (D - 1)) := by gcongr
  have hcalc : 48 + 8 * (4 * (D - 3)) + 2 * ((D - 1) * (4 * (D - 3))) +
      2 * ((D - 2) * (D - 1)) ≤ 10 * D ^ 2 := by
    zify at hD1 hD2 hD3 ⊢
    have h1 : ((D - 1 : ℕ) : ℤ) = (D : ℤ) - 1 := by linarith
    have h2 : ((D - 2 : ℕ) : ℤ) = (D : ℤ) - 2 := by linarith
    have h3 : ((D - 3 : ℕ) : ℤ) = (D : ℤ) - 3 := by linarith
    rw [h1, h2, h3]
    nlinarith only [show 0 ≤ (D : ℤ) by positivity]
  omega

private def Joined (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, G.Adj x y

private def FullTo (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ x ∈ A, ∀ y ∈ B, G.Adj x y

private theorem joined_symm {A B : Finset V} (h : Joined G A B) : Joined G B A := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  exact ⟨y, hy, x, hx, h.symm⟩

private theorem fullTo_or_isolated (hF : NoFar G) (A B : Finset V)
    (hdj : Disjoint A B) (hAst : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (hBst : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y) (hA : A.Nonempty) :
    FullTo G A B ∨ ∃ y ∈ B, ∀ x ∈ A, ¬ G.Adj y x := by
  obtain ⟨x, hx, hhit⟩ := exists_hitting_vertex hF B A hdj.symm hBst hA
  by_cases h : ∀ y ∈ B, G.Adj x y
  · exact .inl ⟨x, hx, h⟩
  push Not at h
  obtain ⟨y, hy, hxy⟩ := h
  exact .inr ⟨y, hy, fun z hz hyz => (hhit y hy z hz hyz).elim hxy (hAst x hx z hz)⟩

private theorem three_large_parts_linked (hF : NoFar G) (D : ℕ)
    (hd : ∀ v, G.degree v ≤ D) (A : Fin 3 → Finset V)
    (hdisj : ∀ {i j}, i ≠ j → Disjoint (A i) (A j))
    (hstable : ∀ i x, x ∈ A i → ∀ y ∈ A i, ¬ G.Adj x y)
    (hlarge : ∀ i, D < 2 * (A i).card)
    (force : ∀ {i j k}, i ≠ j → i ≠ k → j ≠ k → ∀ {x y z},
      x ∈ A i → y ∈ A j → z ∈ A k → G.Adj x y → G.Adj x z ∨ G.Adj y z)
    (hex : ∃ i j : Fin 3, i ≠ j ∧ Joined G (A i) (A j)) :
    ∃ i j : Fin 3, i ≠ j ∧ FullTo G (A i) (A j) ∧ FullTo G (A j) (A i) := by
  have ane (i : Fin 3) : (A i).Nonempty := card_pos.mp (by have := hlarge i; omega)
  have avoid {i j} (hij : i ≠ j) (z : V) :
      ¬ ((∀ x ∈ A i, G.Adj z x) ∧ ∀ y ∈ A j, G.Adj z y) := by
    rintro ⟨hi, hj⟩
    have hsub : A i ∪ A j ⊆ G.neighborFinset z := by
      intro w hw
      rw [mem_neighborFinset]
      exact (mem_union.mp hw).elim (hi w) (hj w)
    have bound := (card_le_card hsub).trans (hd z)
    rw [card_union_of_disjoint (hdisj hij)] at bound
    have hi' := hlarge i
    have hj' := hlarge j
    omega
  have transfer {i j k} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hEdge : Joined G (A i) (A k)) : Joined G (A i) (A j) := by
    by_contra h
    have none (x : V) (hx : x ∈ A i) (y : V) (hy : y ∈ A j) : ¬ G.Adj x y :=
      fun hxy => h ⟨x, hx, y, hy, hxy⟩
    obtain ⟨x, hx, z, hz, hxz⟩ := hEdge
    have hyz (y : V) (hy : y ∈ A j) : G.Adj z y :=
      (force hik hij hjk.symm hx hz hy hxz).resolve_left (none x hx y hy)
    obtain ⟨y, hy⟩ := ane j
    have hzx (x' : V) (hx' : x' ∈ A i) : G.Adj z x' :=
      (force hjk.symm hik.symm hij.symm hz hy hx' (hyz y hy)).resolve_right
        (fun hyx => none x' hx' y hy hyx.symm)
    exact avoid hij z ⟨hzx, hyz⟩
  have all (i j : Fin 3) (hij : i ≠ j) : Joined G (A i) (A j) := by
    obtain ⟨p, q, hpq, h⟩ := hex
    obtain ⟨r, hpr, hqr⟩ : ∃ r : Fin 3, p ≠ r ∧ q ≠ r := by
      have finite : ∀ p q : Fin 3, p ≠ q → ∃ r : Fin 3, p ≠ r ∧ q ≠ r := by decide +kernel
      exact finite p q hpq
    have hprE := transfer hpr hpq hqr.symm h
    have hqrE := transfer hqr hpq.symm hpr.symm (joined_symm h)
    have cover (z : Fin 3) : z = p ∨ z = q ∨ z = r := by
      have finite : ∀ p q r z : Fin 3, p ≠ q → p ≠ r → q ≠ r → z = p ∨ z = q ∨ z = r := by
        decide +kernel
      exact finite p q r z hpq hpr hqr
    rcases cover i with rfl | rfl | rfl <;> rcases cover j with rfl | rfl | rfl
    all_goals
      first | contradiction | assumption | apply joined_symm; assumption
  have helper {i j k} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hy0 : ∃ y ∈ A j, ∀ x ∈ A i, ¬ G.Adj y x) :
      FullTo G (A i) (A k) ∧ FullTo G (A k) (A i) := by
    obtain ⟨y₀, hy₀, hy₀x⟩ := hy0
    obtain ⟨x₀, hx₀, z₀, hz₀, hx₀z₀⟩ := all i k hik
    have hz₀y₀ : G.Adj z₀ y₀ :=
      (force hik hij hjk.symm hx₀ hz₀ hy₀ hx₀z₀).resolve_left (fun h => hy₀x x₀ hx₀ h.symm)
    have hz₀x (x : V) (hx : x ∈ A i) : G.Adj z₀ x :=
      (force hjk.symm hik.symm hij.symm hz₀ hy₀ hx hz₀y₀).resolve_right (hy₀x x hx)
    obtain ⟨y₁, hy₁, hz₀y₁⟩ : ∃ y ∈ A j, ¬ G.Adj z₀ y := by
      by_contra! h
      exact avoid hij z₀ ⟨hz₀x, h⟩
    have hy₁x (x : V) (hx : x ∈ A i) : G.Adj y₁ x := by
      exact ((force hik hij hjk.symm hx hz₀ hy₁ (hz₀x x hx).symm).resolve_right hz₀y₁).symm
    refine ⟨?_, ⟨z₀, hz₀, hz₀x⟩⟩
    rcases fullTo_or_isolated hF (A i) (A k) (hdisj hik) (hstable i) (hstable k) (ane i)
      with h | ⟨z₁, hz₁, hz₁x⟩
    · exact h
    · have hy₁z₁ := (force hij hik hjk hx₀ hy₁ hz₁ (hy₁x x₀ hx₀).symm).resolve_left
        (fun h => hz₁x x₀ hx₀ h.symm)
      have friendly (a b : V) (h : ¬ G.Adj a b) (hne : a ≠ b) : ¬ Near G a b :=
        fun hr => hr.elim h hne
      have hy₀y₁ : y₀ ≠ y₁ := fun h => hz₀y₁ (h ▸ hz₀y₀)
      have hz₀z₁ : z₀ ≠ z₁ := fun h => hz₁x x₀ hx₀ (h ▸ hz₀x x₀ hx₀)
      have z₀y₁ : z₀ ≠ y₁ := fun h => Finset.disjoint_left.mp (hdisj hjk.symm) hz₀ (h.symm ▸ hy₁)
      have y₀z₁ : y₀ ≠ z₁ := fun h => Finset.disjoint_left.mp (hdisj hjk) hy₀ (h.symm ▸ hz₁)
      have hlast : G.Adj y₀ z₁ := by
        rcases hF hz₀y₀ hy₁z₁ with h | h | h | h
        · exact (friendly _ _ hz₀y₁ z₀y₁ h).elim
        · exact (friendly _ _ (hstable k _ hz₀ _ hz₁) hz₀z₁ h).elim
        · exact (friendly _ _ (hstable j _ hy₀ _ hy₁) hy₀y₁ h).elim
        · exact h.elim id (fun he => (y₀z₁ he).elim)
      have final := force hjk hij.symm hik.symm hy₀ hz₁ hx₀ hlast
      exact (final.elim (hy₀x x₀ hx₀) (hz₁x x₀ hx₀)).elim
  let a : Fin 3 := 0
  let b : Fin 3 := 1
  let c : Fin 3 := 2
  have ab : a ≠ b := by decide
  have ac : a ≠ c := by decide
  have bc : b ≠ c := by decide
  rcases fullTo_or_isolated hF (A a) (A b) (hdisj ab) (hstable a) (hstable b) (ane a)
    with hab | hab
  · rcases fullTo_or_isolated hF (A b) (A a) (hdisj ab.symm) (hstable b) (hstable a) (ane b)
      with hba | hba
    · exact ⟨a, b, ab, hab, hba⟩
    · exact ⟨b, c, bc, helper ab.symm bc ac hba⟩
  · exact ⟨a, c, ac, helper ab ac bc hab⟩

private theorem ordered_edges_of_cover {Y B : Finset V} (hB : B ⊆ Y)
    (hcover : ∀ y ∈ Y, ∀ z ∈ Y, G.Adj y z → y ∈ B ∨ z ∈ B) :
    (∑ y ∈ Y, (nbr G Y y).card) ≤ 2 * ∑ y ∈ B, (nbr G Y y).card := by
  calc
    _ ≤ ∑ y ∈ Y, ∑ z ∈ nbr G Y y,
        ((if y ∈ B ∧ z ∈ Y then (1 : ℕ) else 0) + (if y ∈ Y ∧ z ∈ B then 1 else 0)) := by
      apply sum_le_sum
      intro y hy
      rw [card_eq_sum_ones]
      apply sum_le_sum
      intro z hz
      obtain ⟨hzY, hyz⟩ := mem_nbr.mp hz
      rcases hcover y hy z hzY hyz with hb | hb
      · simp [hb, hzY]
      · simp [hb, hy]
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_nbr_indicator hB (Subset.rfl), sum_nbr_indicator (Subset.rfl) hB,
        sum_nbr_comm (G := G) Y B, two_mul]

private theorem triangle_clique_bound (hF : NoFar G) {K : Finset V}
    (hK : G.IsMaximumClique K) (h3 : K.card = 3)
    (hdom : ∀ y, (∃ z, G.Adj y z) → y ∈ dom G K)
    (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    4 * G.edgeFinset.card ≤ 5 * D ^ 2 := by
  by_contra! hcontra
  let Y := activeOutside G K
  let f (y : V) := (nbr G K y).card
  let e := (K.equivFinOfCardEq h3).symm
  let x (i : Fin 3) : V := (e i).1
  have xmem (i : Fin 3) : x i ∈ K := (e i).2
  have xinj : Function.Injective x := fun _ _ h => e.injective (Subtype.ext h)
  have xsur {u : V} (hu : u ∈ K) : ∃ i, x i = u := by
    obtain ⟨i, hi⟩ := e.surjective ⟨u, hu⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  let A (i : Fin 3) := Y.filter fun y => nbr G K y = {x i}
  let B := Y.filter fun y => f y = 2
  let c := ∑ u ∈ K, (nbr G Y u).card
  let l := ∑ y ∈ Y, (nbr G Y y).card
  have hE : 2 * G.edgeFinset.card = 6 + 2 * c + l := by
    simpa only [h3] using (double_edges_parts hK.isClique)
  have hC : c ≤ 3 * (D - 2) := by simpa only [h3] using (cross_count_le hK.isClique D hd)
  have hD : 2 ≤ D := by
    have h := (card_nbr_le_degree K (x 0)).trans (hd (x 0))
    rw [card_nbr_clique hK.isClique (xmem 0), h3] at h
    exact h
  have hD1 : D - 1 + 1 = D := by omega
  have hD2 : D - 2 + 2 = D := by omega
  have dc (y : V) : G.degree y = f y + (nbr G Y y).card := degree_eq_nbr_add K y
  have pos (y : V) (hy : y ∈ Y) : 0 < f y := card_nbr_pos_of_dom hdom hy
  have upper (y : V) (hy : y ∈ Y) : f y ≤ 2 := by
    obtain ⟨u, hu, he⟩ := clique_outside_exists_nonadj hK (mem_activeOutside.mp hy).1
    have hsub : nbr G K y ⊆ K.erase u := by
      intro z hz
      obtain ⟨hz, hyz⟩ := mem_nbr.mp hz
      exact mem_erase.mpr ⟨fun h => he (h ▸ hyz), hz⟩
    have h := card_le_card hsub
    rw [card_erase_of_mem hu, h3] at h
    exact h
  have a_mem {i : Fin 3} {y : V} :
      y ∈ A i ↔ y ∈ Y ∧ nbr G K y = {x i} := mem_filter
  have b_mem {y : V} : y ∈ B ↔ y ∈ Y ∧ f y = 2 := mem_filter
  have a_adj {i : Fin 3} {y : V} (hy : y ∈ A i) : G.Adj y (x i) :=
    (mem_nbr.mp ((a_mem.mp hy).2.symm ▸ mem_singleton_self (x i))).2
  have a_nonadj {i j : Fin 3} {y : V} (hij : i ≠ j) (hy : y ∈ A i) :
      ¬ Near G y (x j) := by
    rintro (h | h)
    · have hj : x j ∈ nbr G K y := mem_nbr.mpr ⟨xmem j, h⟩
      rw [(a_mem.mp hy).2, mem_singleton] at hj
      exact hij (xinj hj).symm
    · exact (mem_activeOutside.mp (a_mem.mp hy).1).1 (h.symm ▸ xmem j)
  have a_stable (i : Fin 3) (y : V) (hy : y ∈ A i) (z : V) (hz : z ∈ A i) :
      ¬ G.Adj y z := by
    intro hyz
    obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      have finite : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide +kernel
      exact finite i
    have hjk' := hK.isClique (xmem j) (xmem k) (fun h => hjk (xinj h))
    rcases hF hyz hjk' with h | h | h | h
    · exact a_nonadj hij hy h
    · exact a_nonadj hik hy h
    · exact a_nonadj hij hz h
    · exact a_nonadj hik hz h
  have a_disj {i j : Fin 3} (hij : i ≠ j) : Disjoint (A i) (A j) := by
    rw [Finset.disjoint_left]
    exact fun _ hy hz => a_nonadj hij hy (.inl (a_adj hz))
  have classify (y : V) (hy : y ∈ Y) : y ∈ B ∨ ∃ i, y ∈ A i := by
    by_cases h : f y = 2
    · exact .inl (b_mem.mpr ⟨hy, h⟩)
    have h1 : (nbr G K y).card = 1 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (lt_of_le_of_ne (upper y hy) h)) (pos y hy)
    obtain ⟨u, hu⟩ := card_eq_one.mp h1
    have huK := (mem_nbr.mp (hu.symm ▸ mem_singleton_self u : u ∈ nbr G K y)).1
    obtain ⟨i, hi⟩ := xsur huK
    exact .inr ⟨i, a_mem.mpr ⟨hy, by rwa [hi]⟩⟩
  have dY (y : V) (hy : y ∈ Y) : (nbr G Y y).card ≤ D - 1 := by
    have h := hd y
    rw [dc y] at h
    have hpos := pos y hy
    omega
  have yLarge : 5 * D < 2 * Y.card + 8 := by
    by_contra! hsmall
    have hL : l ≤ Y.card * (D - 1) := calc
      _ ≤ ∑ _y ∈ Y, (D - 1) := sum_le_sum dY
      _ = _ := by simp
    have hMult := Nat.mul_le_mul_right (D - 1) hsmall
    have aux : 2 * l + 8 * (D - 1) ≤ (5 * D) * (D - 1) := by
      calc
        _ ≤ 2 * (Y.card * (D - 1)) + 8 * (D - 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 hL) _
        _ = (2 * Y.card + 8) * (D - 1) := by ring
        _ ≤ _ := hMult
    have ar : 12 + 4 * (3 * (D - 2)) + (5 * D) * (D - 1) ≤ 5 * D ^ 2 + 8 * (D - 1) := by
      zify at hD1 hD2 ⊢
      have h1 : ((D - 1 : ℕ) : ℤ) = (D : ℤ) - 1 := by linarith
      have h2 : ((D - 2 : ℕ) : ℤ) = (D : ℤ) - 2 := by linarith
      rw [h1, h2]
      nlinarith only [show 0 ≤ (D : ℤ) by positivity]
    omega
  have aLarge (i : Fin 3) : D < 2 * (A i).card := by
    obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      have finite : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide +kernel
      exact finite i
    have hsub : Y ⊆ A i ∪ (nbr G Y (x j) ∪ nbr G Y (x k)) := by
      intro y hy
      by_cases hj : G.Adj y (x j)
      · exact mem_union_right _ (mem_union_left _ (mem_nbr.mpr ⟨hy, hj.symm⟩))
      by_cases hk : G.Adj y (x k)
      · exact mem_union_right _ (mem_union_right _ (mem_nbr.mpr ⟨hy, hk.symm⟩))
      have hs : nbr G K y ⊆ {x i} := by
        intro u hu
        obtain ⟨huK, hyu⟩ := mem_nbr.mp hu
        obtain ⟨a, rfl⟩ := xsur huK
        have finite : ∀ i j k a : Fin 3, i ≠ j → i ≠ k → j ≠ k → a = i ∨ a = j ∨ a = k := by
          decide +kernel
        rcases finite i j k a hij hik hjk with rfl | rfl | rfl
        · exact mem_singleton_self _
        · exact (hj hyu).elim
        · exact (hk hyu).elim
      have he : nbr G K y = {x i} := by
        obtain ⟨u, hu⟩ := card_pos.mp (pos y hy)
        have hu' := mem_singleton.mp (hs hu)
        exact Subset.antisymm hs (singleton_subset_iff.mpr (hu' ▸ hu))
      exact mem_union_left _ (a_mem.mpr ⟨hy, he⟩)
    have hbound := card_le_card hsub
    have hu := card_union_le (A i) (nbr G Y (x j) ∪ nbr G Y (x k))
    have hv := card_union_le (nbr G Y (x j)) (nbr G Y (x k))
    have hD' (a : Fin 3) : (nbr G Y (x a)).card ≤ D - 2 := by
      have h := hd (x a)
      rw [degree_eq_nbr_add K, card_nbr_clique hK.isClique (xmem a), h3] at h
      change 2 + (nbr G Y (x a)).card ≤ D at h
      omega
    have hj := hD' j
    have hk := hD' k
    omega
  have bSmall : 2 * B.card + 4 < D := by
    have hbound : (Y.card + B.card) ≤ c := by
      have hsum : (∑ y ∈ Y, f y) = c := sum_nbr_comm (G := G) Y K
      rw [← hsum]
      have hBcard : B.card = ∑ y ∈ Y, (if y ∈ B then 1 else 0 : ℕ) := by
        rw [← card_filter]
        congr 1
        ext y
        exact ⟨fun h => mem_filter.mpr ⟨(b_mem.mp h).1, h⟩, fun h => (mem_filter.mp h).2⟩
      rw [hBcard, Finset.card_eq_sum_ones Y, ← sum_add_distrib]
      apply sum_le_sum
      intro y hy
      by_cases h : y ∈ B
      · simp [h, (b_mem.mp h).2]
      · have hpos := pos y hy
        simp [h]
        omega
    omega
  have joined : ∃ i j : Fin 3, i ≠ j ∧ Joined G (A i) (A j) := by
    by_contra! hn
    have cover (y : V) (hy : y ∈ Y) (z : V) (hz : z ∈ Y) (hyz : G.Adj y z) : y ∈ B ∨ z ∈ B := by
      rcases classify y hy with h | ⟨i, hi⟩
      · exact .inl h
      rcases classify z hz with h | ⟨j, hj⟩
      · exact .inr h
      by_cases hij : i = j
      · subst j
        exact (a_stable i y hi z hj hyz).elim
      · exact (hn i j hij ⟨y, hi, z, hj, hyz⟩).elim
    have hL' : l ≤ 2 * B.card * (D - 2) := by
      have hcover := ordered_edges_of_cover (G := G) (filter_subset (fun y => f y = 2) Y) cover
      have hsum : (∑ y ∈ B, (nbr G Y y).card) ≤ B.card * (D - 2) := calc
        _ ≤ ∑ _y ∈ B, (D - 2) := by
          apply sum_le_sum
          intro y hy
          have h := hd y
          rw [dc y, (b_mem.mp hy).2] at h
          omega
        _ = _ := by simp
      rw [mul_assoc]
      exact hcover.trans (Nat.mul_le_mul_left 2 hsum)
    have hb : 2 * B.card ≤ D := by omega
    have hL := hL'.trans (Nat.mul_le_mul_right (D - 2) hb)
    have ar : 12 + 4 * (3 * (D - 2)) + 2 * (D * (D - 2)) ≤ 5 * D ^ 2 := by
      zify at hD2 ⊢
      have h2 : ((D - 2 : ℕ) : ℤ) = (D : ℤ) - 2 := by linarith
      rw [h2]
      nlinarith only [sq_nonneg ((D : ℤ) - 2), show 0 ≤ (D : ℤ) by positivity]
    omega
  have force {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {u v w : V}
      (hu : u ∈ A i) (hv : v ∈ A j) (hw : w ∈ A k) (huv : G.Adj u v) :
      G.Adj u w ∨ G.Adj v w := by
    rcases hF huv (a_adj hw).symm with h | h | h | h
    · exact (a_nonadj hik hu h).elim
    · refine .inl (h.elim id (fun he => ?_))
      exact (Finset.disjoint_left.mp (a_disj hik) hu (he.symm ▸ hw)).elim
    · exact (a_nonadj hjk hv h).elim
    · refine .inr (h.elim id (fun he => ?_))
      exact (Finset.disjoint_left.mp (a_disj hjk) hv (he.symm ▸ hw)).elim
  obtain ⟨i, j, hij, ⟨a, ha, haall⟩, ⟨b, hb, hball⟩⟩ :=
    three_large_parts_linked hF D hd A a_disj a_stable aLarge force joined
  have hsub : Y ⊆ nbr G Y a ∪ (nbr G Y b ∪ B) := by
    intro y hy
    rcases classify y hy with hyB | ⟨k, hk⟩
    · exact mem_union_right _ (mem_union_right _ hyB)
    by_cases hik : i = k
    · exact mem_union_right _ (mem_union_left _ (mem_nbr.mpr ⟨hy, hball y (hik.symm ▸ hk)⟩))
    by_cases hjk : j = k
    · exact mem_union_left _ (mem_nbr.mpr ⟨hy, haall y (hjk.symm ▸ hk)⟩)
    exact (force hij hik hjk ha hb hk (haall b hb)).elim
      (fun h => mem_union_left _ (mem_nbr.mpr ⟨hy, h⟩))
      (fun h => mem_union_right _ (mem_union_left _ (mem_nbr.mpr ⟨hy, h⟩)))
  have hbound := card_le_card hsub
  have hbc := card_union_le (nbr G Y b) B
  have habc := card_union_le (nbr G Y a) (nbr G Y b ∪ B)
  have hda := dY a (a_mem.mp ha).1
  have hdb := dY b (a_mem.mp hb).1
  omega

private theorem edges_bound (hF : NoFar G) (D : ℕ) (hd : ∀ v, G.degree v ≤ D) :
    4 * G.edgeFinset.card ≤ 5 * D ^ 2 := by
  by_cases h3 : 3 ≤ G.cliqueNum
  · obtain ⟨K, hK, hdom⟩ := exists_dominating_maximum_clique hF h3
    have h := G.maximumClique_card_eq_cliqueNum K hK
    by_cases hK3 : K.card = 3
    · exact triangle_clique_bound hF hK hK3 hdom D hd
    by_cases hK4 : K.card = 4
    · exact four_clique_bound hF hK.isClique hK4 hdom D hd
    exact large_clique_bound hF hK.isClique (by omega) D hd
  · have hT : G.CliqueFree 3 := by
      intro s hs
      have hge := hs.isClique.card_le_cliqueNum
      rw [hs.card_eq] at hge
      omega
    by_cases hC : FiveCycle G
    · exact fiveCycle_bound hF hT hC D hd
    · have h := triangleFree_without_fiveCycle hF hT hC D hd
      omega

end

end Research934

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H2 := by
  intro D n G hd he
  by_contra hn
  have hd' (v : Fin n) : G.degree v ≤ D := by
    simpa only [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
      using hd v
  have he' : (5 * D ^ 2 + 4) / 4 ≤ G.edgeFinset.card := by
    simpa only [← G.coe_edgeFinset, Set.ncard_coe_finset] using he
  have upper := Research934.edges_bound (Research934.noFar_of_not_hasFar hn) D hd'
  omega
