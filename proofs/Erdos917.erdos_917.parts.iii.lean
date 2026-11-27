import FormalConjectures.ErdosProblems.«917»

/-!
Disproof of the general asymptotic question in Erdos Problem 917 (part iii).

At `k = 7`, `conjecturedValue 7 n = n ^ 2 / 4`. Joining Toft's 4-critical graph on `16 * s + 4`
vertices (built from two odd cycles of length `4 * s + 1` and two matched independent sets with a
complete bipartite join between them) and an odd cycle of length `14 * s + 3` produces a
7-critical graph on `n = 30 * s + 7` vertices with `240 * s ^ 2 + 138 * s + 20` edges, giving
asymptotic edge density `4 / 15 > 1 / 4`.
-/

namespace OMA.Erdos917PartIII

open Finset SimpleGraph Filter Asymptotics

/- Cycle adjacency and local colourings on `0, ..., m - 1` -/

def cyc (m p q : ℕ) : Prop :=
  p ≠ q ∧ (q = p + 1 ∨ p = q + 1 ∨ (p = 0 ∧ q + 1 = m) ∨ (q = 0 ∧ p + 1 = m))

instance instDecidableCyc (m p q : ℕ) : Decidable (cyc m p q) := by
  unfold cyc; infer_instance

lemma cyc_symm {m p q : ℕ} (h : cyc m p q) : cyc m q p := by
  unfold cyc at h ⊢; omega

lemma cyc_irrefl {m p : ℕ} (h : cyc m p p) : False :=
  h.1 rfl

def nxt (m p : ℕ) : ℕ := if p + 1 = m then 0 else p + 1

lemma nxt_lt {m p : ℕ} (hm : 3 ≤ m) (_hp : p < m) : nxt m p < m := by
  unfold nxt; split_ifs <;> omega

lemma cyc_nxt {m p : ℕ} (hm : 3 ≤ m) (_hp : p < m) : cyc m p (nxt m p) := by
  unfold cyc nxt; split_ifs <;> omega

def rel (m s p : ℕ) : ℕ := if s ≤ p then p - s else p + m - s

def col3 (m p : ℕ) : ℕ := if p + 1 = m then 2 else p % 2

def brk (m s p : ℕ) : ℕ := rel m s p % 2

def spc0 (m u p : ℕ) : ℕ := if p = u then 0 else 1 + rel m (nxt m u) p % 2

lemma col3_lt (m p : ℕ) : col3 m p < 3 := by
  unfold col3; split_ifs <;> omega

lemma col3_cyc {m p q : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) (hp : p < m) (hq : q < m)
    (h : cyc m p q) : col3 m p ≠ col3 m q := by
  unfold col3 cyc at *; split_ifs <;> omega

lemma brk_lt (m s p : ℕ) : brk m s p < 2 := by
  unfold brk; omega

lemma brk_cyc {m s j p q : ℕ} (_hm : 3 ≤ m) (_hp : p < m) (_hq : q < m) (hs : s < m)
    (hjs : s = j + 1 ∨ (s = 0 ∧ j + 1 = m)) (h : cyc m p q)
    (hnot : ¬ ((p = j ∧ q = s) ∨ (p = s ∧ q = j))) : brk m s p ≠ brk m s q := by
  unfold brk rel cyc at *; split_ifs <;> omega

lemma spc0_lt (m u p : ℕ) : spc0 m u p < 3 := by
  unfold spc0; split_ifs <;> omega

lemma spc0_cyc {m u p q : ℕ} (hm : 3 ≤ m) (hu : u < m) (hp : p < m) (hq : q < m)
    (h : cyc m p q) : spc0 m u p ≠ spc0 m u q := by
  unfold spc0 rel nxt cyc at *; split_ifs <;> omega

lemma no_two_col_cyc {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1)
    (f : ℕ → ℕ) (hproper : ∀ p q, p < m → q < m → cyc m p q → f p ≠ f q)
    {a b : ℕ} (forall_ab : ∀ p, p < m → f p = a ∨ f p = b) : False := by
  have h0 : 0 < m := by omega
  by_cases hf0 : f 0 = a
  · have claim : ∀ j, j < m → f j = if j % 2 = 0 then a else b := by
      intro j
      induction j with
      | zero => intro _; simp [hf0]
      | succ j ih =>
        intro hj1
        have hj : j < m := by omega
        have hne := hproper j (j + 1) hj hj1 ⟨by omega, Or.inl rfl⟩
        rw [ih hj] at hne
        by_cases hev : j % 2 = 0
        · have hev1 : ¬ (j + 1) % 2 = 0 := by omega
          simp only [hev, hev1, ↓reduceIte] at hne ⊢
          rcases forall_ab (j + 1) hj1 with hja | hjb
          · exact absurd hja.symm hne
          · exact hjb
        · have hev1 : (j + 1) % 2 = 0 := by omega
          simp only [hev, hev1, ↓reduceIte] at hne ⊢
          rcases forall_ab (j + 1) hj1 with hja | hjb
          · exact hja
          · exact absurd hjb.symm hne
    have hlast : m - 1 < m := by omega
    have e1 := claim (m - 1) hlast
    rw [if_pos (by omega : (m - 1) % 2 = 0)] at e1
    exact hproper (m - 1) 0 hlast h0 ⟨by omega, Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))⟩
      (e1.trans hf0.symm)
  · have hf0b : f 0 = b := (forall_ab 0 h0).resolve_left hf0
    have claim : ∀ j, j < m → f j = if j % 2 = 0 then b else a := by
      intro j
      induction j with
      | zero => intro _; simp [hf0b]
      | succ j ih =>
        intro hj1
        have hj : j < m := by omega
        have hne := hproper j (j + 1) hj hj1 ⟨by omega, Or.inl rfl⟩
        rw [ih hj] at hne
        by_cases hev : j % 2 = 0
        · have hev1 : ¬ (j + 1) % 2 = 0 := by omega
          simp only [hev, hev1, ↓reduceIte] at hne ⊢
          rcases forall_ab (j + 1) hj1 with hja | hjb
          · exact hja
          · exact absurd hjb.symm hne
        · have hev1 : (j + 1) % 2 = 0 := by omega
          simp only [hev, hev1, ↓reduceIte] at hne ⊢
          rcases forall_ab (j + 1) hj1 with hja | hjb
          · exact absurd hja.symm hne
          · exact hjb
    have hlast : m - 1 < m := by omega
    have e1 := claim (m - 1) hlast
    rw [if_pos (by omega : (m - 1) % 2 = 0)] at e1
    exact hproper (m - 1) 0 hlast h0 ⟨by omega, Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))⟩
      (e1.trans hf0b.symm)

lemma no_avoid_one_of_three {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1)
    (f : ℕ → Fin 3) (hproper : ∀ p q, p < m → q < m → cyc m p q → f p ≠ f q)
    (bad : Fin 3) (havoid : ∀ p, p < m → f p ≠ bad) : False := by
  have hex : ∃ a b : Fin 3, ∀ x : Fin 3, x ≠ bad → x = a ∨ x = b := by
    fin_cases bad
    · exact ⟨1, 2, by decide⟩
    · exact ⟨0, 2, by decide⟩
    · exact ⟨0, 1, by decide⟩
  obtain ⟨a, b, hab⟩ := hex
  refine no_two_col_cyc hm hodd (fun p => (f p).val)
    (fun p q hp hq hc heq => hproper p q hp hq hc (Fin.ext heq)) (a := a.val) (b := b.val) ?_
  intro p hp
  rcases hab (f p) (havoid p hp) with h | h
  · exact Or.inl (congrArg Fin.val h)
  · exact Or.inr (congrArg Fin.val h)

/- General criticality criterion from edge criticality and minimum degree >= 1 -/

lemma colorable_of {V : Type*} (H : SimpleGraph V) (K : ℕ) (col : V → ℕ)
    (hb : ∀ x, col x < K) (hp : ∀ x y, H.Adj x y → col x ≠ col y) : H.Colorable K :=
  ⟨Coloring.mk (fun x => ⟨col x, hb x⟩) (fun {x y} h heq => hp x y h (congrArg Fin.val heq))⟩

lemma isKCritical_of_edge_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical G k := by
  have hle_chi : (k : ℕ∞) ≤ G.chromaticNumber := by
    rw [le_chromaticNumber_iff_not_colorable (by omega)]
    exact hnot
  have hchi : G.chromaticNumber = (k : ℕ∞) :=
    le_antisymm hcol.chromaticNumber_le hle_chi
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    obtain ⟨w, hvw⟩ := hdeg v
    obtain ⟨C⟩ := hedge v w hvw
    have hdel : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun a => C a.val) ?_⟩
      intro a b hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
      obtain ⟨_, ha, _, hb, hab⟩ := hab
      rw [Subgraph.top_adj] at hab
      apply C.valid
      rw [deleteEdges_adj]
      refine ⟨hab, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact ha (Set.mem_singleton_iff.mpr h1)
      · exact hb (Set.mem_singleton_iff.mpr h2)
    have htop_le : (k : ℕ∞) ≤ (⊤ : G.Subgraph).coe.chromaticNumber := by
      rw [le_chromaticNumber_iff_not_colorable (by omega)]
      rintro ⟨C'⟩
      exact hnot ⟨Coloring.mk (fun x => C' ⟨x, trivial⟩) (fun h => C'.valid (by simpa using h))⟩
    exact lt_of_le_of_lt hdel.chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) htop_le)
  · intro e he
    unfold IsCriticalEdge IsCriticalEdges
    revert he
    refine Sym2.ind (fun u w huw => ?_) e
    rw [mem_edgeSet] at huw
    exact lt_of_le_of_lt (hedge u w huw).chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) hle_chi)

lemma isKCritical_transport {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical (G.map e.toEmbedding) k := by
  refine isKCritical_of_edge_critical _ hk ?_ ?_ ?_ ?_
  · obtain ⟨C⟩ := hcol
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    simpa using C.valid huv
  · rintro ⟨C⟩
    exact hnot ⟨Coloring.mk (fun v => C (e v)) fun {u v} huv =>
      C.valid (by rw [map_adj]; exact ⟨u, v, huv, rfl, rfl⟩)⟩
  · intro w
    obtain ⟨u, hu⟩ := hdeg (e.symm w)
    refine ⟨e u, ?_⟩
    rw [map_adj]
    exact ⟨e.symm w, u, hu, e.apply_symm_apply w, rfl⟩
  · intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    obtain ⟨C⟩ := hedge u v huv
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro a b hab
    rw [deleteEdges_adj, map_adj] at hab
    obtain ⟨⟨u', v', huv', rfl, rfl⟩, hne⟩ := hab
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨huv', ?_⟩
    intro heq
    apply hne
    rw [Set.mem_singleton_iff] at heq ⊢
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

lemma ncard_edgeSet_map {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ W)
    [DecidableRel (G.map e.toEmbedding).Adj] :
    (G.map e.toEmbedding).edgeSet.ncard = G.edgeSet.ncard := by
  rw [← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg : ∀ v : V, (G.map e.toEmbedding).degree (e v) = G.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    refine card_bij (fun w _ => e.symm w) ?_ ?_ ?_
    · intro w hw
      rw [mem_filter] at hw ⊢
      refine ⟨mem_univ _, ?_⟩
      have hwadj := hw.2
      rw [map_adj] at hwadj
      obtain ⟨a, b, hab, ha, hb⟩ := hwadj
      have h1 : a = v := e.injective ha
      have h2 : b = e.symm w := by
        apply e.injective
        simpa using hb
      rwa [← h1, ← h2]
    · intro w₁ _ w₂ _ h
      exact e.symm.injective h
    · intro u hu
      rw [mem_filter] at hu
      refine ⟨e u, ?_, e.symm_apply_apply u⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [map_adj]
      exact ⟨v, u, hu.2, rfl, rfl⟩
  have hsum1 := sum_degrees_eq_twice_card_edges (G.map e.toEmbedding)
  have hsum2 := sum_degrees_eq_twice_card_edges G
  have hsum_eq : ∑ w : W, (G.map e.toEmbedding).degree w = ∑ v : V, G.degree v := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun v _ => hdeg v
  omega

/- Odd cycle on `Fin m` -/

def oddCycle (m : ℕ) : SimpleGraph (Fin m) where
  Adj x y := cyc m x.val y.val
  symm := ⟨fun _ _ h => cyc_symm h⟩
  loopless := ⟨fun _ h => cyc_irrefl h⟩

instance instDecidableOddCycle (m : ℕ) : DecidableRel (oddCycle m).Adj :=
  fun x y => instDecidableCyc m x.val y.val

lemma oddCycle_critical {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    Erdos917.IsKCritical (oddCycle m) 3 := by
  refine isKCritical_of_edge_critical (oddCycle m) (by omega) ?_ ?_ ?_ ?_
  · exact colorable_of _ 3 (fun x => col3 m x.val) (fun x => col3_lt m x.val)
      (fun x y h => col3_cyc hm hodd x.isLt y.isLt h)
  · rintro ⟨C⟩
    exact no_two_col_cyc hm hodd (fun p => if hp : p < m then (C ⟨p, hp⟩).val else 0)
      (fun p q hp hq hc heq => by
        simp only [hp, hq, ↓reduceDIte] at heq
        exact C.valid (show (oddCycle m).Adj ⟨p, hp⟩ ⟨q, hq⟩ from hc) (Fin.ext heq))
      (a := 0) (b := 1)
      (fun p hp => by
        simp only [hp, ↓reduceDIte]
        have := (C ⟨p, hp⟩).isLt
        omega)
  · intro v
    exact ⟨⟨nxt m v.val, nxt_lt hm v.isLt⟩, cyc_nxt hm v.isLt⟩
  · intro u w huw
    by_cases hdir : w.val = nxt m u.val
    · have hjs : w.val = u.val + 1 ∨ (w.val = 0 ∧ u.val + 1 = m) := by
        unfold nxt at hdir; split_ifs at hdir <;> omega
      refine colorable_of _ 2 (fun x => brk m w.val x.val) (fun x => brk_lt m w.val x.val) ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      refine brk_cyc hm a.isLt b.isLt w.isLt hjs hab.1 ?_
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hab.2 (by rw [Fin.ext h1, Fin.ext h2]; exact Set.mem_singleton _)
      · exact hab.2 (by rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]; exact Set.mem_singleton _)
    · have hjs : u.val = w.val + 1 ∨ (u.val = 0 ∧ w.val + 1 = m) := by
        unfold nxt at hdir
        have hcyc : cyc m u.val w.val := huw
        have hu := u.isLt
        have hw := w.isLt
        unfold cyc at hcyc
        split_ifs at hdir <;> omega
      refine colorable_of _ 2 (fun x => brk m u.val x.val) (fun x => brk_lt m u.val x.val) ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      refine brk_cyc hm a.isLt b.isLt u.isLt hjs hab.1 ?_
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hab.2 (by rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]; exact Set.mem_singleton _)
      · exact hab.2 (by rw [Fin.ext h1, Fin.ext h2]; exact Set.mem_singleton _)

lemma oddCycle_degree {m : ℕ} (hm : 3 ≤ m) (x : Fin m) : (oddCycle m).degree x = 2 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  let p1 : Fin m := ⟨nxt m x.val, nxt_lt hm x.isLt⟩
  let p2 : Fin m := ⟨if x.val = 0 then m - 1 else x.val - 1, by split_ifs <;> omega⟩
  have hset : univ.filter (fun y : Fin m => (oddCycle m).Adj x y) = {p1, p2} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rcases y with ⟨yv, hy⟩
    rcases x with ⟨xv, hx⟩
    simp only [oddCycle, cyc, Fin.ext_iff]
    dsimp only [p1, p2, nxt]
    split_ifs <;> constructor <;> intro h <;> omega
  rw [hset, card_pair]
  intro heq
  have hval := congrArg Fin.val heq
  dsimp only [p1, p2, nxt] at hval
  have := x.isLt
  split_ifs at hval <;> omega

lemma oddCycle_ncard_edges {m : ℕ} (hm : 3 ≤ m) : (oddCycle m).edgeSet.ncard = m := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have h := sum_degrees_eq_twice_card_edges (oddCycle m)
  simp only [oddCycle_degree hm, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/- Toft's 4-critical graph -/

inductive ToftV (m₁ m₂ : ℕ) : Type
  | A : Fin m₁ → ToftV m₁ m₂
  | B : Fin m₁ → ToftV m₁ m₂
  | C : Fin m₂ → ToftV m₁ m₂
  | D : Fin m₂ → ToftV m₁ m₂
  deriving DecidableEq

def toftEquiv (m₁ m₂ : ℕ) : ToftV m₁ m₂ ≃ Fin (2 * m₁ + 2 * m₂) where
  toFun
    | .A i => ⟨i.val, by omega⟩
    | .B i => ⟨m₁ + i.val, by omega⟩
    | .C j => ⟨2 * m₁ + j.val, by omega⟩
    | .D j => ⟨2 * m₁ + m₂ + j.val, by omega⟩
  invFun x :=
    if h1 : x.val < m₁ then .A ⟨x.val, h1⟩
    else if h2 : x.val < 2 * m₁ then .B ⟨x.val - m₁, by omega⟩
    else if h3 : x.val < 2 * m₁ + m₂ then .C ⟨x.val - 2 * m₁, by omega⟩
    else .D ⟨x.val - (2 * m₁ + m₂), by omega⟩
  left_inv v := by
    cases v with
    | A i => simp [i.isLt]
    | B i =>
      have h1 : ¬ m₁ + i.val < m₁ := by omega
      have h2 : m₁ + i.val < 2 * m₁ := by omega
      simp [h1, h2]
    | C j =>
      have h1 : ¬ 2 * m₁ + j.val < m₁ := by omega
      have h2 : ¬ 2 * m₁ + j.val < 2 * m₁ := by omega
      have h3 : 2 * m₁ + j.val < 2 * m₁ + m₂ := by omega
      simp [h1, h2, h3]
    | D j =>
      have h1 : ¬ 2 * m₁ + m₂ + j.val < m₁ := by omega
      have h2 : ¬ 2 * m₁ + m₂ + j.val < 2 * m₁ := by omega
      have h3 : ¬ 2 * m₁ + m₂ + j.val < 2 * m₁ + m₂ := by omega
      simp [h1, h2, h3]
  right_inv x := by
    simp only
    split_ifs with h1 h2 h3 <;> ext <;> simp <;> omega

instance instFintypeToftV (m₁ m₂ : ℕ) : Fintype (ToftV m₁ m₂) :=
  Fintype.ofEquiv (Fin (2 * m₁ + 2 * m₂)) (toftEquiv m₁ m₂).symm

def toftAdj {m₁ m₂ : ℕ} : ToftV m₁ m₂ → ToftV m₁ m₂ → Prop
  | .A i, .A j => cyc m₁ i.val j.val
  | .A i, .B j => i = j
  | .B i, .A j => i = j
  | .B _, .C _ => True
  | .C _, .B _ => True
  | .C i, .D j => i = j
  | .D i, .C j => i = j
  | .D i, .D j => cyc m₂ i.val j.val
  | _, _ => False

instance instDecidableToftAdj (m₁ m₂ : ℕ) : DecidableRel (@toftAdj m₁ m₂) := by
  intro u v
  cases u <;> cases v <;> unfold toftAdj <;> infer_instance

def toftRaw (m₁ m₂ : ℕ) : SimpleGraph (ToftV m₁ m₂) where
  Adj := toftAdj
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only [toftAdj] at h ⊢
    all_goals first | exact cyc_symm h | exact h.symm⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only [toftAdj] at h
    all_goals exact cyc_irrefl h⟩

instance instDecidableToftRaw (m₁ m₂ : ℕ) : DecidableRel (toftRaw m₁ m₂).Adj :=
  instDecidableToftAdj m₁ m₂

lemma spcShift_lt (m u p : ℕ) : (spc0 m u p + 1) % 3 < 3 := Nat.mod_lt _ (by omega)

lemma spcShift_cyc {m u p q : ℕ} (hm : 3 ≤ m) (hu : u < m) (hp : p < m) (hq : q < m)
    (h : cyc m p q) : (spc0 m u p + 1) % 3 ≠ (spc0 m u q + 1) % 3 := by
  have hne := spc0_cyc hm hu hp hq h
  have h1 := spc0_lt m u p
  have h2 := spc0_lt m u q
  omega

lemma spcShift_vs_two_one {m : ℕ} (u p : ℕ) :
    (spc0 m u p + 1) % 3 ≠ (if p = u then 2 else 1) := by
  unfold spc0; split_ifs <;> omega

lemma spc0_vs_two_zero {m : ℕ} (u p : ℕ) :
    spc0 m u p ≠ (if p = u then 2 else 0) := by
  unfold spc0; split_ifs <;> omega

lemma toftRaw_colorable4 {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (ho₁ : m₁ % 2 = 1)
    (hm₂ : 3 ≤ m₂) (ho₂ : m₂ % 2 = 1) : (toftRaw m₁ m₂).Colorable 4 := by
  refine colorable_of _ 4
    (fun v => match v with
      | .A i => col3 m₁ i.val
      | .B _ => 3
      | .C _ => 0
      | .D j => if col3 m₂ j.val = 0 then 3 else col3 m₂ j.val)
    (fun v => by
      cases v with
      | A i => dsimp only; have := col3_lt m₁ i.val; omega
      | B _ => dsimp only; omega
      | C _ => dsimp only; omega
      | D j => dsimp only; have := col3_lt m₂ j.val; split_ifs <;> omega)
    ?_
  intro u v huv
  rcases u with i | i | i | i <;> rcases v with j | j | j | j <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at huv
  · exact col3_cyc hm₁ ho₁ i.isLt j.isLt huv
  · have := col3_lt m₁ i.val; omega
  · have := col3_lt m₁ j.val; omega
  · omega
  · omega
  · split_ifs <;> have := col3_lt m₂ j.val <;> omega
  · split_ifs <;> have := col3_lt m₂ i.val <;> omega
  · have hne := col3_cyc hm₂ ho₂ i.isLt j.isLt huv
    have hi := col3_lt m₂ i.val
    have hj := col3_lt m₂ j.val
    split_ifs <;> omega

lemma fin3_unique_rem :
    ∀ b₀ b₁ x : Fin 3, b₀ ≠ b₁ → x ≠ b₀ → x ≠ b₁ →
      ∀ y : Fin 3, y ≠ b₀ → y ≠ b₁ → x = y := by
  decide

lemma toftRaw_not_colorable3 {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (ho₁ : m₁ % 2 = 1)
    (hm₂ : 3 ≤ m₂) (ho₂ : m₂ % 2 = 1) : ¬ (toftRaw m₁ m₂).Colorable 3 := by
  rintro ⟨C⟩
  let z₁ : Fin m₁ := ⟨0, by omega⟩
  let z₂ : Fin m₂ := ⟨0, by omega⟩
  set b₀ : Fin 3 := C (.B z₁)
  set c₀ : Fin 3 := C (.C z₂)
  by_cases hB : ∀ i : Fin m₁, C (.B i) = b₀
  · refine no_avoid_one_of_three hm₁ ho₁
      (fun p => if hp : p < m₁ then C (.A ⟨p, hp⟩) else 0)
      (fun p q hp hq hc => by
        simp only [hp, hq, ↓reduceDIte]
        exact C.valid (show (toftRaw m₁ m₂).Adj (.A ⟨p, hp⟩) (.A ⟨q, hq⟩) from hc))
      b₀ ?_
    intro p hp
    simp only [hp, ↓reduceDIte]
    rw [← hB ⟨p, hp⟩]
    exact C.valid (show (toftRaw m₁ m₂).Adj (.A ⟨p, hp⟩) (.B ⟨p, hp⟩) from rfl)
  · push Not at hB
    obtain ⟨i₁, hi₁⟩ := hB
    set b₁ : Fin 3 := C (.B i₁)
    have hb01 : b₀ ≠ b₁ := hi₁.symm
    have hC_all : ∀ j : Fin m₂, C (.C j) = c₀ := by
      intro j
      refine fin3_unique_rem b₀ b₁ (C (.C j)) hb01 ?_ ?_ c₀ ?_ ?_
      · exact C.valid (show (toftRaw m₁ m₂).Adj (.C j) (.B z₁) from trivial)
      · exact C.valid (show (toftRaw m₁ m₂).Adj (.C j) (.B i₁) from trivial)
      · exact C.valid (show (toftRaw m₁ m₂).Adj (.C z₂) (.B z₁) from trivial)
      · exact C.valid (show (toftRaw m₁ m₂).Adj (.C z₂) (.B i₁) from trivial)
    refine no_avoid_one_of_three hm₂ ho₂
      (fun p => if hp : p < m₂ then C (.D ⟨p, hp⟩) else 0)
      (fun p q hp hq hc => by
        simp only [hp, hq, ↓reduceDIte]
        exact C.valid (show (toftRaw m₁ m₂).Adj (.D ⟨p, hp⟩) (.D ⟨q, hq⟩) from hc))
      c₀ ?_
    intro p hp
    simp only [hp, ↓reduceDIte]
    rw [← hC_all ⟨p, hp⟩]
    exact C.valid (show (toftRaw m₁ m₂).Adj (.D ⟨p, hp⟩) (.C ⟨p, hp⟩) from rfl)

lemma toftRaw_del_A {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂)
    (i j : Fin m₁) (hij : cyc m₁ i.val j.val) :
    ((toftRaw m₁ m₂).deleteEdges {s(.A i, .A j)}).Colorable 3 := by
  obtain ⟨u, w, hpair, hs_lt, hjs⟩ : ∃ u w : Fin m₁,
      s(.A u, .A w) = s(ToftV.A (m₂ := m₂) i, .A j) ∧ w.val < m₁ ∧
      (w.val = u.val + 1 ∨ (w.val = 0 ∧ u.val + 1 = m₁)) := by
    by_cases hdir : j.val = nxt m₁ i.val
    · refine ⟨i, j, rfl, j.isLt, ?_⟩
      unfold nxt at hdir; split_ifs at hdir <;> omega
    · refine ⟨j, i, Sym2.eq_swap, i.isLt, ?_⟩
      unfold nxt at hdir
      have hcyc := hij; have hi := i.isLt; have hj := j.isLt; unfold cyc at hcyc
      split_ifs at hdir <;> omega
  rw [← hpair]
  refine colorable_of _ 3
    (fun v => match v with
      | .A p => 1 + brk m₁ w.val p.val
      | .B _ => 0
      | .C q => if q.val = 0 then 2 else 1
      | .D q => (spc0 m₂ 0 q.val + 1) % 3)
    (fun v => by
      cases v with
      | A p => dsimp only; have := brk_lt m₁ w.val p.val; omega
      | B _ => dsimp only; omega
      | C _ => dsimp only; split_ifs <;> omega
      | D q => dsimp only; exact spcShift_lt m₂ 0 q.val)
    ?_
  intro x y hxy
  rw [deleteEdges_adj] at hxy
  obtain ⟨hadj, hne⟩ := hxy
  rcases x with p | p | p | p <;> rcases y with q | q | q | q <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at hadj
  · have hneq := brk_cyc hm₁ p.isLt q.isLt hs_lt hjs hadj (by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hne (by rw [Fin.ext h1, Fin.ext h2]; exact Set.mem_singleton _)
      · exact hne (by rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]; exact Set.mem_singleton _))
    omega
  · omega
  · omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · subst hadj; exact (spcShift_vs_two_one 0 p.val).symm
  · subst hadj; exact spcShift_vs_two_one 0 p.val
  · exact spcShift_cyc hm₂ (by omega) p.isLt q.isLt hadj

lemma toftRaw_del_D {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂)
    (i j : Fin m₂) (hij : cyc m₂ i.val j.val) :
    ((toftRaw m₁ m₂).deleteEdges {s(.D i, .D j)}).Colorable 3 := by
  obtain ⟨u, w, hpair, hs_lt, hjs⟩ : ∃ u w : Fin m₂,
      s(.D u, .D w) = s(ToftV.D (m₁ := m₁) i, .D j) ∧ w.val < m₂ ∧
      (w.val = u.val + 1 ∨ (w.val = 0 ∧ u.val + 1 = m₂)) := by
    by_cases hdir : j.val = nxt m₂ i.val
    · refine ⟨i, j, rfl, j.isLt, ?_⟩
      unfold nxt at hdir; split_ifs at hdir <;> omega
    · refine ⟨j, i, Sym2.eq_swap, i.isLt, ?_⟩
      unfold nxt at hdir
      have hcyc := hij; have hi := i.isLt; have hj := j.isLt; unfold cyc at hcyc
      split_ifs at hdir <;> omega
  rw [← hpair]
  refine colorable_of _ 3
    (fun v => match v with
      | .A p => (spc0 m₁ 0 p.val + 1) % 3
      | .B p => if p.val = 0 then 2 else 1
      | .C _ => 0
      | .D q => 1 + brk m₂ w.val q.val)
    (fun v => by
      cases v with
      | A p => dsimp only; exact spcShift_lt m₁ 0 p.val
      | B _ => dsimp only; split_ifs <;> omega
      | C _ => dsimp only; omega
      | D q => dsimp only; have := brk_lt m₂ w.val q.val; omega)
    ?_
  intro x y hxy
  rw [deleteEdges_adj] at hxy
  obtain ⟨hadj, hne⟩ := hxy
  rcases x with p | p | p | p <;> rcases y with q | q | q | q <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at hadj
  · exact spcShift_cyc hm₁ (by omega) p.isLt q.isLt hadj
  · subst hadj; exact spcShift_vs_two_one 0 p.val
  · subst hadj; exact (spcShift_vs_two_one 0 p.val).symm
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega
  · omega
  · have hneq := brk_cyc hm₂ p.isLt q.isLt hs_lt hjs hadj (by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hne (by rw [Fin.ext h1, Fin.ext h2]; exact Set.mem_singleton _)
      · exact hne (by rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]; exact Set.mem_singleton _))
    omega

lemma toftRaw_del_AB {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) (i₀ : Fin m₁) :
    ((toftRaw m₁ m₂).deleteEdges {s(.A i₀, .B i₀)}).Colorable 3 := by
  refine colorable_of _ 3
    (fun v => match v with
      | .A p => spc0 m₁ i₀.val p.val
      | .B _ => 0
      | .C q => if q.val = 0 then 2 else 1
      | .D q => (spc0 m₂ 0 q.val + 1) % 3)
    (fun v => by
      cases v with
      | A p => dsimp only; exact spc0_lt m₁ i₀.val p.val
      | B _ => dsimp only; omega
      | C _ => dsimp only; split_ifs <;> omega
      | D q => dsimp only; exact spcShift_lt m₂ 0 q.val)
    ?_
  intro x y hxy
  rw [deleteEdges_adj] at hxy
  obtain ⟨hadj, hne⟩ := hxy
  rcases x with p | p | p | p <;> rcases y with q | q | q | q <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at hadj
  · exact spc0_cyc hm₁ i₀.isLt p.isLt q.isLt hadj
  · subst hadj
    have hpi : p.val ≠ i₀.val := by
      intro heq
      exact hne (by rw [Fin.ext heq]; exact Set.mem_singleton _)
    unfold spc0; rw [if_neg hpi]; omega
  · subst hadj
    have hpi : p.val ≠ i₀.val := by
      intro heq
      exact hne (by rw [Fin.ext heq, Sym2.eq_swap]; exact Set.mem_singleton _)
    unfold spc0; rw [if_neg hpi]; omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · subst hadj; exact (spcShift_vs_two_one 0 p.val).symm
  · subst hadj; exact spcShift_vs_two_one 0 p.val
  · exact spcShift_cyc hm₂ (by omega) p.isLt q.isLt hadj

lemma toftRaw_del_CD {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) (j₀ : Fin m₂) :
    ((toftRaw m₁ m₂).deleteEdges {s(.C j₀, .D j₀)}).Colorable 3 := by
  refine colorable_of _ 3
    (fun v => match v with
      | .A p => (spc0 m₁ 0 p.val + 1) % 3
      | .B p => if p.val = 0 then 2 else 1
      | .C _ => 0
      | .D q => spc0 m₂ j₀.val q.val)
    (fun v => by
      cases v with
      | A p => dsimp only; exact spcShift_lt m₁ 0 p.val
      | B _ => dsimp only; split_ifs <;> omega
      | C _ => dsimp only; omega
      | D q => dsimp only; exact spc0_lt m₂ j₀.val q.val)
    ?_
  intro x y hxy
  rw [deleteEdges_adj] at hxy
  obtain ⟨hadj, hne⟩ := hxy
  rcases x with p | p | p | p <;> rcases y with q | q | q | q <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at hadj
  · exact spcShift_cyc hm₁ (by omega) p.isLt q.isLt hadj
  · subst hadj; exact spcShift_vs_two_one 0 p.val
  · subst hadj; exact (spcShift_vs_two_one 0 p.val).symm
  · split_ifs <;> omega
  · split_ifs <;> omega
  · subst hadj
    have hpj : p.val ≠ j₀.val := by
      intro heq
      exact hne (by rw [Fin.ext heq]; exact Set.mem_singleton _)
    unfold spc0; rw [if_neg hpj]; omega
  · subst hadj
    have hpj : p.val ≠ j₀.val := by
      intro heq
      exact hne (by rw [Fin.ext heq, Sym2.eq_swap]; exact Set.mem_singleton _)
    unfold spc0; rw [if_neg hpj]; omega
  · exact spc0_cyc hm₂ j₀.isLt p.isLt q.isLt hadj

lemma toftRaw_del_BC {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) (i₀ : Fin m₁) (j₀ : Fin m₂) :
    ((toftRaw m₁ m₂).deleteEdges {s(.B i₀, .C j₀)}).Colorable 3 := by
  refine colorable_of _ 3
    (fun v => match v with
      | .A p => spc0 m₁ i₀.val p.val
      | .B p => if p.val = i₀.val then 2 else 0
      | .C q => if q.val = j₀.val then 2 else 1
      | .D q => (spc0 m₂ j₀.val q.val + 1) % 3)
    (fun v => by
      cases v with
      | A p => dsimp only; exact spc0_lt m₁ i₀.val p.val
      | B _ => dsimp only; split_ifs <;> omega
      | C _ => dsimp only; split_ifs <;> omega
      | D q => dsimp only; exact spcShift_lt m₂ j₀.val q.val)
    ?_
  intro x y hxy
  rw [deleteEdges_adj] at hxy
  obtain ⟨hadj, hne⟩ := hxy
  rcases x with p | p | p | p <;> rcases y with q | q | q | q <;>
    dsimp only <;> simp only [toftRaw, toftAdj] at hadj
  · exact spc0_cyc hm₁ i₀.isLt p.isLt q.isLt hadj
  · subst hadj; exact spc0_vs_two_zero i₀.val p.val
  · subst hadj; exact (spc0_vs_two_zero i₀.val p.val).symm
  · by_cases hp : p.val = i₀.val
    · by_cases hq : q.val = j₀.val
      · exfalso
        exact hne (by rw [Fin.ext hp, Fin.ext hq]; exact Set.mem_singleton _)
      · simp [hp, hq]
    · rw [if_neg hp]; split_ifs <;> omega
  · by_cases hp : q.val = i₀.val
    · by_cases hq : p.val = j₀.val
      · exfalso
        exact hne (by rw [Fin.ext hp, Fin.ext hq, Sym2.eq_swap]; exact Set.mem_singleton _)
      · simp [hp, hq]
    · rw [if_neg hp]; split_ifs <;> omega
  · subst hadj; exact (spcShift_vs_two_one j₀.val p.val).symm
  · subst hadj; exact spcShift_vs_two_one j₀.val p.val
  · exact spcShift_cyc hm₂ j₀.isLt p.isLt q.isLt hadj

def toftGraph (m₁ m₂ : ℕ) : SimpleGraph (Fin (2 * m₁ + 2 * m₂)) :=
  (toftRaw m₁ m₂).map (toftEquiv m₁ m₂).toEmbedding

noncomputable instance instDecidableToftGraph (m₁ m₂ : ℕ) : DecidableRel (toftGraph m₁ m₂).Adj :=
  Classical.decRel _

lemma toftGraph_critical {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (ho₁ : m₁ % 2 = 1)
    (hm₂ : 3 ≤ m₂) (ho₂ : m₂ % 2 = 1) :
    Erdos917.IsKCritical (toftGraph m₁ m₂) 4 := by
  refine isKCritical_transport (toftRaw m₁ m₂) (toftEquiv m₁ m₂) (by omega)
    (toftRaw_colorable4 hm₁ ho₁ hm₂ ho₂)
    (toftRaw_not_colorable3 hm₁ ho₁ hm₂ ho₂)
    (fun v => by
      cases v with
      | A i => exact ⟨.B i, rfl⟩
      | B i => exact ⟨.A i, rfl⟩
      | C j => exact ⟨.D j, rfl⟩
      | D j => exact ⟨.C j, rfl⟩)
    ?_
  intro u w huw
  cases u <;> cases w <;> simp only [toftRaw, toftAdj] at huw
  · exact toftRaw_del_A hm₁ hm₂ _ _ huw
  · subst huw; exact toftRaw_del_AB hm₁ hm₂ _
  · subst huw; rw [Sym2.eq_swap]; exact toftRaw_del_AB hm₁ hm₂ _
  · exact toftRaw_del_BC hm₁ hm₂ _ _
  · rw [Sym2.eq_swap]; exact toftRaw_del_BC hm₁ hm₂ _ _
  · subst huw; exact toftRaw_del_CD hm₁ hm₂ _
  · subst huw; rw [Sym2.eq_swap]; exact toftRaw_del_CD hm₁ hm₂ _
  · exact toftRaw_del_D hm₁ hm₂ _ _ huw

lemma toftRaw_degree {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) (v : ToftV m₁ m₂) :
    (toftRaw m₁ m₂).degree v =
      match v with
      | .A _ => 3
      | .B _ => 1 + m₂
      | .C _ => m₁ + 1
      | .D _ => 3 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  cases v with
  | A i =>
    let p1 : Fin m₁ := ⟨nxt m₁ i.val, nxt_lt hm₁ i.isLt⟩
    let p2 : Fin m₁ := ⟨if i.val = 0 then m₁ - 1 else i.val - 1, by split_ifs <;> omega⟩
    have hset : univ.filter (fun y : ToftV m₁ m₂ => (toftRaw m₁ m₂).Adj (.A i) y) =
        {.A p1, .A p2, .B i} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rcases y with q | q | q | q
      · rcases i with ⟨iv, hi⟩
        rcases q with ⟨qv, hq⟩
        simp only [toftRaw, toftAdj, cyc, ToftV.A.injEq, reduceCtorEq, or_false, Fin.ext_iff]
        dsimp only [p1, p2, nxt]
        split_ifs <;> constructor <;> intro h <;> omega
      · simp [toftRaw, toftAdj, eq_comm]
      · simp [toftRaw, toftAdj]
      · simp [toftRaw, toftAdj]
    rw [hset, card_insert_of_notMem, card_pair]
    · intro h; cases h
    · intro hm
      rcases mem_insert.mp hm with h | h
      · have hval := congrArg Fin.val (ToftV.A.inj h)
        dsimp only [p1, p2, nxt] at hval
        have := i.isLt
        split_ifs at hval <;> omega
      · rw [mem_singleton] at h; cases h
  | B i =>
    dsimp only
    have hset : univ.filter (fun y : ToftV m₁ m₂ => (toftRaw m₁ m₂).Adj (.B i) y) =
        insert (.A i) (univ.image ToftV.C) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
      cases y <;> simp [toftRaw, toftAdj, eq_comm]
    rw [hset, card_insert_of_notMem (by intro hm; obtain ⟨_, _, h⟩ := mem_image.mp hm; cases h),
      card_image_of_injective _ (fun _ _ h => ToftV.C.inj h), card_univ, Fintype.card_fin]
    omega
  | C j =>
    dsimp only
    have hset : univ.filter (fun y : ToftV m₁ m₂ => (toftRaw m₁ m₂).Adj (.C j) y) =
        insert (.D j) (univ.image ToftV.B) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
      cases y <;> simp [toftRaw, toftAdj, eq_comm]
    rw [hset, card_insert_of_notMem (by intro hm; obtain ⟨_, _, h⟩ := mem_image.mp hm; cases h),
      card_image_of_injective _ (fun _ _ h => ToftV.B.inj h), card_univ, Fintype.card_fin]
  | D j =>
    let p1 : Fin m₂ := ⟨nxt m₂ j.val, nxt_lt hm₂ j.isLt⟩
    let p2 : Fin m₂ := ⟨if j.val = 0 then m₂ - 1 else j.val - 1, by split_ifs <;> omega⟩
    have hset : univ.filter (fun y : ToftV m₁ m₂ => (toftRaw m₁ m₂).Adj (.D j) y) =
        {.D p1, .D p2, .C j} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rcases y with q | q | q | q
      · simp [toftRaw, toftAdj]
      · simp [toftRaw, toftAdj]
      · simp [toftRaw, toftAdj, eq_comm]
      · rcases j with ⟨jv, hj⟩
        rcases q with ⟨qv, hq⟩
        simp only [toftRaw, toftAdj, cyc, ToftV.D.injEq, reduceCtorEq, or_false, Fin.ext_iff]
        dsimp only [p1, p2, nxt]
        split_ifs <;> constructor <;> intro h <;> omega
    rw [hset, card_insert_of_notMem, card_pair]
    · intro h; cases h
    · intro hm
      rcases mem_insert.mp hm with h | h
      · have hval := congrArg Fin.val (ToftV.D.inj h)
        dsimp only [p1, p2, nxt] at hval
        have := j.isLt
        split_ifs at hval <;> omega
      · rw [mem_singleton] at h; cases h

lemma toftGraph_ncard_edges {m₁ m₂ : ℕ} (hm₁ : 3 ≤ m₁) (hm₂ : 3 ≤ m₂) :
    (toftGraph m₁ m₂).edgeSet.ncard = m₁ * m₂ + 2 * m₁ + 2 * m₂ := by
  classical
  unfold toftGraph
  rw [ncard_edgeSet_map, ← coe_edgeFinset, Set.ncard_coe_finset]
  have h := sum_degrees_eq_twice_card_edges (toftRaw m₁ m₂)
  have hsum : ∑ v : ToftV m₁ m₂, (toftRaw m₁ m₂).degree v =
      (∑ _ : Fin m₁, 3) + (∑ _ : Fin m₁, (1 + m₂)) +
        ((∑ _ : Fin m₂, (m₁ + 1)) + (∑ _ : Fin m₂, 3)) := by
    have huniv : (univ : Finset (ToftV m₁ m₂)) =
        ((univ.image ToftV.A) ∪ (univ.image ToftV.B)) ∪
          ((univ.image ToftV.C) ∪ (univ.image ToftV.D)) := by
      ext v; cases v <;> simp
    rw [huniv, sum_union, sum_union, sum_union]
    · simp only [sum_image (fun _ _ _ _ h => ToftV.A.inj h),
        sum_image (fun _ _ _ _ h => ToftV.B.inj h),
        sum_image (fun _ _ _ _ h => ToftV.C.inj h),
        sum_image (fun _ _ _ _ h => ToftV.D.inj h), toftRaw_degree hm₁ hm₂]
    · rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨_, _, rfl⟩ := mem_image.mp hx
      obtain ⟨_, _, h'⟩ := mem_image.mp hy
      cases h'
    · rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨_, _, rfl⟩ := mem_image.mp hx
      obtain ⟨_, _, h'⟩ := mem_image.mp hy
      cases h'
    · rw [Finset.disjoint_left]
      rintro x hx hy
      simp only [mem_union, mem_image, mem_univ, true_and] at hx hy
      rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rcases hy with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [hsum] at h
  have halg : m₁ * 3 + m₁ * (1 + m₂) + (m₂ * (m₁ + 1) + m₂ * 3) =
      2 * (m₁ * m₂ + 2 * m₁ + 2 * m₂) := by
    ring
  omega

/- Join of two critical graphs on `Fin n₁` and `Fin n₂` -/

def joinSum {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph (V₁ ⊕ V₂) where
  Adj
    | .inl x, .inl y => G₁.Adj x y
    | .inr x, .inr y => G₂.Adj x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only at h ⊢
    · exact h.symm
    · exact h.symm⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only at h
    · exact G₁.ne_of_adj h rfl
    · exact G₂.ne_of_adj h rfl⟩

lemma isKCritical_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos917.IsKCritical G k) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp hG.1.1.le

lemma isKCritical_not_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : ¬ G.Colorable (k - 1) := by
  intro hc
  have hlt : (k - 1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
  exact not_le_of_gt hlt (hG.1.1.symm.trans_le hc.chromaticNumber_le)

lemma isKCritical_nonempty {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : Nonempty V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  exact isKCritical_not_colorable hk hG
    ⟨Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {v} => (IsEmpty.false v).elim)⟩

lemma isKCritical_del_edge_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) {u w : V} (huw : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).Colorable (k - 1) := by
  have he : s(u, w) ∈ G.edgeSet := huw
  have hlt := hG.2 _ he
  unfold IsCriticalEdge IsCriticalEdges at hlt
  rw [hG.1.1] at hlt
  by_contra hnc
  exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt

lemma isKCritical_del_vert_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) (v : V) :
    ∃ col : V → ℕ, (∀ x, x ≠ v → col x < k - 1) ∧
      ∀ x y, x ≠ v → y ≠ v → G.Adj x y → col x ≠ col y := by
  classical
  have hlt := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at hlt
  have htop_le : (⊤ : G.Subgraph).coe.chromaticNumber ≤ G.chromaticNumber := by
    obtain ⟨C⟩ := isKCritical_colorable hG
    rw [hG.1.1]
    exact (Colorable.chromaticNumber_le
      ⟨Coloring.mk (fun x => C x.val) (fun {a b} h => C.valid (by simpa using h))⟩)
  have hlt' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (k : ℕ∞) :=
    lt_of_lt_of_le hlt (htop_le.trans_eq hG.1.1)
  have hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
    by_contra hnc
    exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt'
  obtain ⟨C⟩ := hcol
  refine ⟨fun x => if hx : x ≠ v then (C ⟨x, by simp [hx]⟩).val else 0, ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [dif_pos hx]
    exact (C _).isLt
  · intro x y hx hy hadj heq
    dsimp only at heq
    rw [dif_pos hx, dif_pos hy] at heq
    have hadj' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Adj ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ := by
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
      exact ⟨trivial, by simp [hx], trivial, by simp [hy], hadj⟩
    exact C.valid hadj' (Fin.ext heq)

def joinGraph {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    SimpleGraph (Fin (n₁ + n₂)) :=
  (joinSum G₁ G₂).map finSumFinEquiv.toEmbedding

lemma joinGraph_critical {n₁ n₂ k₁ k₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : Erdos917.IsKCritical G₁ k₁) (h₂ : Erdos917.IsKCritical G₂ k₂) :
    Erdos917.IsKCritical (joinGraph G₁ G₂) (k₁ + k₂) := by
  classical
  obtain ⟨v₁₀⟩ := isKCritical_nonempty hk₁ h₁
  obtain ⟨v₂₀⟩ := isKCritical_nonempty hk₂ h₂
  refine isKCritical_transport (joinSum G₁ G₂) finSumFinEquiv (by omega) ?_ ?_ ?_ ?_
  · obtain ⟨C₁⟩ := isKCritical_colorable h₁
    obtain ⟨C₂⟩ := isKCritical_colorable h₂
    refine colorable_of _ (k₁ + k₂)
      (Sum.elim (fun x => (C₁ x).val) (fun y => k₁ + (C₂ y).val))
      (fun u => by
        cases u with
        | inl x => simp only [Sum.elim_inl]; have := (C₁ x).isLt; omega
        | inr y => simp only [Sum.elim_inr]; have := (C₂ y).isLt; omega)
      ?_
    intro u v huv
    rcases u with x | x <;> rcases v with y | y <;>
      simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at huv ⊢
    · intro heq; exact C₁.valid huv (Fin.ext heq)
    · have := (C₁ x).isLt; omega
    · have := (C₁ y).isLt; omega
    · intro heq; exact C₂.valid huv (Fin.ext (by omega))
  · rintro ⟨C⟩
    let S₁ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun x : Fin n₁ => C (.inl x))
    let S₂ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun y : Fin n₂ => C (.inr y))
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      obtain ⟨x, _, rfl⟩ := mem_image.mp hc₁
      obtain ⟨y, _, hy⟩ := mem_image.mp hc₂
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl x) (.inr y) from trivial) hy.symm
    have hcard : S₁.card + S₂.card ≤ k₁ + k₂ - 1 := by
      rw [← card_union_of_disjoint hdisj]
      exact (card_le_univ _).trans_eq (Fintype.card_fin _)
    by_cases hle₁ : S₁.card ≤ k₁ - 1
    · apply isKCritical_not_colorable hk₁ h₁
      let eqv := S₁.equivFin
      refine ⟨Coloring.mk (fun x => (eqv ⟨C (.inl x), mem_image_of_mem _ (mem_univ x)⟩).castLE hle₁) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₁ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl a) (.inl b) from hab) (congrArg Subtype.val hsub)
    · have hle₂ : S₂.card ≤ k₂ - 1 := by omega
      apply isKCritical_not_colorable hk₂ h₂
      let eqv := S₂.equivFin
      refine ⟨Coloring.mk (fun y => (eqv ⟨C (.inr y), mem_image_of_mem _ (mem_univ y)⟩).castLE hle₂) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₂ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inr a) (.inr b) from hab) (congrArg Subtype.val hsub)
  · intro v
    cases v with
    | inl _ => exact ⟨.inr v₂₀, trivial⟩
    | inr _ => exact ⟨.inl v₁₀, trivial⟩
  · intro u w huw
    cases u <;> cases w <;> simp only [joinSum] at huw
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_del_edge_colorable hk₁ h₁ huw
      obtain ⟨C₂⟩ := isKCritical_colorable h₂
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => (k₁ - 1) + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq
        have hadj' : (G₁.deleteEdges {s(x, y)}).Adj a₁ b₁ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₁.valid hadj' (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq; exact C₂.valid hadj (Fin.ext (by omega))
    · rename_i x y
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i y x
      rw [Sym2.eq_swap]
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_colorable h₁
      obtain ⟨C₂⟩ := isKCritical_del_edge_colorable hk₂ h₂ huw
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => k₁ + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq; exact C₁.valid hadj (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq
        have hadj' : (G₂.deleteEdges {s(x, y)}).Adj a₂ b₂ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₂.valid hadj' (Fin.ext (by omega))

lemma joinGraph_ncard_edges {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (joinGraph G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ * n₂ := by
  classical
  unfold joinGraph
  rw [ncard_edgeSet_map, ← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset,
    Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg_inl : ∀ x : Fin n₁, (joinSum G₁ G₂).degree (.inl x) = G₁.degree x + n₂ := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inl x) z) =
        ((univ.filter (fun y : Fin n₁ => G₁.Adj x y)).image Sum.inl) ∪ (univ.image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have hdeg_inr : ∀ y : Fin n₂, (joinSum G₁ G₂).degree (.inr y) = n₁ + G₂.degree y := by
    intro y
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inr y) z) =
        (univ.image Sum.inl) ∪ ((univ.filter (fun w : Fin n₂ => G₂.Adj y w)).image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have h1 := sum_degrees_eq_twice_card_edges (joinSum G₁ G₂)
  have h2 := sum_degrees_eq_twice_card_edges G₁
  have h3 := sum_degrees_eq_twice_card_edges G₂
  have hsum : ∑ z : Fin n₁ ⊕ Fin n₂, (joinSum G₁ G₂).degree z =
      (∑ x : Fin n₁, (G₁.degree x + n₂)) + (∑ y : Fin n₂, (n₁ + G₂.degree y)) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact sum_congr rfl fun x _ => hdeg_inl x
    · exact sum_congr rfl fun y _ => hdeg_inr y
  rw [sum_add_distrib, sum_add_distrib] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  omega

lemma conjecturedValue_seven (n : ℕ) :
    Erdos917.conjecturedValue 7 n = (n : ℝ) ^ 2 / 4 := by
  have h : ((7 / 3 : ℕ) : ℝ) = 2 := by norm_num
  rw [Erdos917.conjecturedValue, h]
  ring

end OMA.Erdos917PartIII

open OMA.Erdos917PartIII in
theorem OMA.solution : type_of% @Erdos917.erdos_917.parts.iii := by
  intro hall
  have h7 := hall 7 (by omega)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h7.isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 30))
  let s : ℕ := N₀ + 1
  let m₁ : ℕ := 4 * s + 1
  let y : ℕ := 14 * s + 3
  let n : ℕ := (2 * m₁ + 2 * m₁) + y
  have hm₁ : 3 ≤ m₁ := by omega
  have ho₁ : m₁ % 2 = 1 := by omega
  have hy : 3 ≤ y := by omega
  have hoy : y % 2 = 1 := by omega
  let J : SimpleGraph (Fin n) := joinGraph (toftGraph m₁ m₁) (oddCycle y)
  have hcrit : Erdos917.IsKCritical J 7 :=
    joinGraph_critical (k₁ := 4) (k₂ := 3) (by omega) (by omega)
      (toftGraph_critical hm₁ ho₁ hm₁ ho₁) (oddCycle_critical hy hoy)
  have hle_f : J.edgeSet.ncard ≤ Erdos917.f 7 n := Erdos917.edgeSet_ncard_le_f hcrit
  have hcard : J.edgeSet.ncard =
      (m₁ * m₁ + 2 * m₁ + 2 * m₁) + y + (2 * m₁ + 2 * m₁) * y := by
    dsimp [J]
    rw [joinGraph_ncard_edges, toftGraph_ncard_edges hm₁ hm₁, oddCycle_ncard_edges hy]
  have hle_real : ((J.edgeSet.ncard : ℕ) : ℝ) ≤ (Erdos917.f 7 n : ℝ) := by
    exact_mod_cast hle_f
  have hbound := hN₀ n (by omega)
  rw [Pi.sub_apply, conjecturedValue_seven, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 2 / 4)] at hbound
  have hdiff : (Erdos917.f 7 n : ℝ) - (n : ℝ) ^ 2 / 4 ≤
      |(Erdos917.f 7 n : ℝ) - (n : ℝ) ^ 2 / 4| := le_abs_self _
  have hupper : (Erdos917.f 7 n : ℝ) ≤ (31 / 120 : ℝ) * (n : ℝ) ^ 2 := by
    linarith
  have hlower : (240 : ℝ) * (s : ℝ) ^ 2 + 138 * (s : ℝ) + 20 ≤ (Erdos917.f 7 n : ℝ) := by
    refine le_trans ?_ hle_real
    rw [hcard]
    dsimp [m₁, y]
    push_cast
    ring_nf
    linarith
  have hn_eq : (n : ℝ) = 30 * (s : ℝ) + 7 := by
    dsimp [n, m₁, y]
    push_cast
    ring
  rw [hn_eq] at hupper
  have hs_pos : (1 : ℝ) ≤ (s : ℝ) := by
    dsimp [s]; exact_mod_cast (Nat.le_add_left 1 N₀)
  nlinarith

