import OMAReductions.R_Erdos743_erdos_743_variants_almost_linear_degree_R2

/-!
Leaf-rich packing, split at the beginning of MatchLeaves (Algorithm 3 in
Allen et al., arXiv:1906.11558). H1 uses the preparation for uniformly leaf-rich guests in Definition 12, Lemmas 18 and 19 and Claim 21. H3 supplies that uniform family and is proved below. H2 isolates the matching
argument of Lemma 20 and Claims 22–24. The guest lists A may exclude padded
vertices as well as the core. D u is the set of out-neighbors at parent u.
The weight w u k counts guest k's omitted leaves at u. The final three
bounds control cross-round collisions as in the proof of Claim 24.
The residual density p is chosen after μ, and the weight cap d after p.
The local degree and distinct-guest codegree targets are μm and μ²m.
The weight cap controls exceptional pairs belonging to a single guest.
-/
namespace OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R2_H1_R1

open SimpleGraph Filter Finset
open scoped Classical

/-- Prepare the cores, orientation, and local estimates for the matching phase. -/
def H1 : Prop :=
  ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ∀ q > (0 : ℝ), ∃ p ∈ Set.Ioo 0 q,
  ∀ d > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ (T : (k : ℕ) → SimpleGraph (Fin k)) (J : Finset ℕ),
    (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * n / Real.log n) →
    J ⊆ Icc ((n + 3) / 4) (n / 2) →
    J.card = n/8000000 →
    (∀ k ∈ J, n/8000000 ≤ (univ.filter (fun x => (T k).degree x = 1)).card) →
    let S := Set.Icc 2 n
    ∃ (C : (k : S) → Set (Fin k)) (par : (k : S) → {v : Fin k // v ∉ C k} → C k)
      (f : (k : S) → C k ↪ Fin n) (D : Fin n → Finset (Fin n)) (A : S → Finset (Fin n)),
    let G (k : S) := ((T k).induce (C k)).map (f k)
    let w (u : Fin n) (k : S) := Nat.card {x : {v : Fin k // v ∉ C k} // f k (par k x) = u}
    (∀ k x y, (T (k : S)).Adj x.val y → y = (par k x).val) ∧
    (∀ k l : S, k.val < l.val → Disjoint (G k).edgeSet (G l).edgeSet) ∧
    (∀ u v, v ∈ D u → u ∉ D v) ∧ (∀ k u v, v ∈ D u → ¬ (G k).Adj u v) ∧
    (∀ k y, f k y ∉ A k) ∧
    let m := p * n / 2
    let near (x y : ℝ) := |x - y| ≤ p * y
    (∀ u, ∑ k, w u k = (D u).card) ∧
    (∀ u, near (D u).card m) ∧
    (∀ u k, (w u k : ℝ) ≤ d * n / Real.log n) ∧
    (∀ u k, 0 < w u k → near ((D u ∩ A k).card) (μ * m)) ∧
    (∀ u, ∀ y ∈ D u, near (∑ k, if y ∈ A k then (w u k : ℝ) else 0) (μ * m)) ∧
    (∀ u k l, k ≠ l → 0 < w u k → 0 < w u l →
      near ((D u ∩ A k ∩ A l).card) (μ ^ 2 * m)) ∧
    (∀ u v, u ≠ v → ((D u ∩ D v).card : ℝ) ≤ 2 * p ^ 2 * n) ∧
    (∀ k, (∑ u, (w u k : ℝ)) ≤ p * n / μ) ∧
    (∀ k, ∀ y ∈ A k, (∑ u, if y ∈ D u then (w u k : ℝ) else 0) ≤ 10 * p ^ 2 * n / μ)

/-- A matching problem with guest colors. The distinct destinations for each
guest implement the cross-round update. Each host pair is used at most once. -/
def H2 : Prop :=
  ∀ μ : ℝ, 0 < μ → μ ≤ 1 → ∃ q > (0 : ℝ), ∀ p ∈ Set.Ioo 0 q,
  ∃ d > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  let S := Set.Icc 2 n
  ∀ (C : (k : S) → Set (Fin k)) (host : (k : S) → {v : Fin k // v ∉ C k} → Fin n)
    (D : Fin n → Finset (Fin n)) (A : S → Finset (Fin n)),
    let w (u : Fin n) (k : S) := Nat.card {x : {v : Fin k // v ∉ C k} // host k x = u}
    (let m := p * n / 2
     let near (x y : ℝ) := |x - y| ≤ p * y
     (∀ u, ∑ k, w u k = (D u).card) ∧
     (∀ u, near (D u).card m) ∧
     (∀ u k, (w u k : ℝ) ≤ d * n / Real.log n) ∧
     (∀ u k, 0 < w u k → near ((D u ∩ A k).card) (μ * m)) ∧
     (∀ u, ∀ y ∈ D u, near (∑ k, if y ∈ A k then (w u k : ℝ) else 0) (μ * m)) ∧
     (∀ u k l, k ≠ l → 0 < w u k → 0 < w u l →
       near ((D u ∩ A k ∩ A l).card) (μ ^ 2 * m)) ∧
     (∀ u v, u ≠ v → ((D u ∩ D v).card : ℝ) ≤ 2 * p ^ 2 * n) ∧
     (∀ k, (∑ u, (w u k : ℝ)) ≤ p * n / μ) ∧
     (∀ k, ∀ y ∈ A k, (∑ u, if y ∈ D u then (w u k : ℝ) else 0) ≤ 10 * p ^ 2 * n / μ)) →
    ∃ g : (k : S) → {v : Fin k // v ∉ C k} ↪ Fin n,
      (∀ k x, g k x ∈ D (host k x) ∩ A k) ∧
      ∀ k l x y, host k x = host l y → g k x = g l y → k = l

/-- Extract a uniform family of leaf-rich guests from an aggregate bound. -/
def H3 : Prop := ∀ (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)) (J : Finset ℕ),
  J ⊆ Icc ((n+3)/4) (n/2) →
  n^2 ≤ 4000000 * ∑ k ∈ J, (univ.filter fun x => (T k).degree x = 1).card →
  ∃ B ⊆ J, B.card = n/8000000 ∧
    ∀ k ∈ B, n/8000000 ≤ (univ.filter fun x => (T k).degree x = 1).card

theorem select_leaf_reserves (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k))
    (J : Finset ℕ) (medium : J ⊆ Icc ((n+3)/4) (n/2))
    (mass : n^2 ≤ 4000000 * ∑ k ∈ J, (univ.filter fun x => (T k).degree x = 1).card)
    (a b : ℕ) (ha : a ≤ n/8000000) (hb : b ≤ n/8000000) :
    ∃ B ⊆ J, B.card = a ∧ ∀ k ∈ B, ∃ R : Finset (Fin k),
      R.card = b ∧ ∀ x ∈ R, (T k).degree x = 1 := by
  classical
  let leaves k := univ.filter fun x => (T k).degree x = 1
  let rich := J.filter fun k => b ≤ (leaves k).card
  by_cases h : n = 0
  · have az : a = 0 := by omega
    exact ⟨∅,empty_subset _,by simp [az],by simp⟩
  have hJ : J.card ≤ n := by
    have hsize := card_le_card medium
    rw [Nat.card_Icc] at hsize
    omega
  have cap (k) (hk : k ∈ J) : (leaves k).card ≤ n :=
    (card_filter_le ..).trans ((card_univ.trans (Fintype.card_fin k)).le.trans (by
      have := (mem_Icc.mp (medium hk)).2
      omega))
  have enough : a ≤ rich.card := by
    by_contra! few
    have estimate (k) (hk : k ∈ J) :
        (leaves k).card ≤ b + (if b ≤ (leaves k).card then n else 0) := by
      split <;> first | exact (cap k hk).trans (Nat.le_add_left ..) | omega
    have upper := sum_le_sum estimate
    simp only [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, ← sum_filter] at upper
    change ∑ k ∈ J, (leaves k).card ≤ J.card*b + rich.card*n at upper
    change n^2 ≤ 4000000 * ∑ k ∈ J, (leaves k).card at mass
    have hp : 8000000*b ≤ n := by omega
    have hq : 8000000*rich.card < n := by omega
    have pos : 0 < n := by omega
    have e1 := Nat.mul_le_mul_right n hp
    have e2 := Nat.mul_lt_mul_of_pos_right hq pos
    have u := upper.trans (Nat.add_le_add_right (Nat.mul_le_mul_right b hJ) _)
    nlinarith only [mass,u,e1,e2]
  obtain ⟨B,sub,count⟩ := exists_subset_card_eq enough
  refine ⟨B,sub.trans (filter_subset ..),count,?_⟩
  intro k hk
  obtain ⟨R,subR,countR⟩ := exists_subset_card_eq (mem_filter.mp (sub hk)).2
  exact ⟨R,countR,fun x hx => (mem_filter.mp (subR hx)).2⟩

theorem uniform_family_exists : H3 := by
  intro n T J orders mass
  obtain ⟨B,sub,size,chooseLeaves⟩ := select_leaf_reserves n T J orders mass
    (n/8000000) (n/8000000) le_rfl le_rfl
  refine ⟨B,sub,size,?_⟩
  intro k hk
  obtain ⟨R,card,leaves⟩ := chooseLeaves k hk
  rw [←card]
  exact card_le_card (fun x hx => mem_filter.mpr ⟨mem_univ _,leaves x hx⟩)

/-- The deterministic completion step for a leaf packing. At each host parent,
the matching uses distinct outgoing edges. Freshness and injectivity of the
leaf destinations within each guest preserve vertex injectivity. -/
theorem packing_of_leaf_assignments {n : ℕ} {S : Set ℕ}
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (C : (k : S) → Set (Fin k))
    (parent : (k : S) → {v : Fin k // v ∉ C k} → C k)
    (neighbor : ∀ (k : S) (x : {v : Fin k // v ∉ C k}) y, (T k).Adj x.val y → y = (parent k x).val)
    (core : (k : S) → C k ↪ Fin n)
    (packed : ∀ k l : S, k.val < l.val →
      Disjoint (((T k).induce (C k)).map (core k)).edgeSet
               (((T l).induce (C l)).map (core l)).edgeSet)
    (dest : (k : S) → {v : Fin k // v ∉ C k} ↪ Fin n)
    (fresh : ∀ (k : S) (x : {v : Fin k // v ∉ C k}) (y : C k), dest k x ≠ core k y)
    (R : Fin n → Fin n → Prop)
    (asymm : ∀ u v, R u v → ¬ R v u)
    (unused : ∀ (k : S) u v, R u v → ¬ (((T k).induce (C k)).map (core k)).Adj u v)
    (allowed : ∀ k x, R (core k (parent k x)) (dest k x))
    (matching : ∀ (k l : S) (x : {v : Fin k // v ∉ C k}) (y : {v : Fin l // v ∉ C l}),
      core k (parent k x) = core l (parent l y) → dest k x = dest l y → k = l) :
    Erdos743.IsPacking n S T := by
  classical
  let f (k : S) (x : Fin k) : Fin n :=
    if h : x ∈ C k then core k ⟨x, h⟩ else dest k ⟨x, h⟩
  have fc (k : S) (x : C k) : f k x.val = core k x := by simp [f, x.property]
  have fl (k : S) (x : {v : Fin k // v ∉ C k}) : f k x.val = dest k x := by
    have hx : x.val ∉ C k := x.property
    simp [f, hx]
  have inj (k : S) : Function.Injective (f k) := by
    intro x y he
    by_cases hx : x ∈ C k <;> by_cases hy : y ∈ C k
    · simpa [f, hx, hy] using he
    · exact False.elim (fresh k ⟨y, hy⟩ ⟨x, hx⟩ (by simpa [f, hx, hy] using he.symm))
    · exact False.elim (fresh k ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [f, hx, hy] using he))
    · simpa [f, hx, hy] using he
  let old (k : S) := (((T k).induce (C k)).map (core k)).edgeSet
  let extra (k : S) (x : {v : Fin k // v ∉ C k}) := s(core k (parent k x), dest k x)
  have leaf_edge (k : S) (x : {v : Fin k // v ∉ C k}) {y : Fin k} (h : (T k).Adj x.val y) :
      s(f k x.val, f k y) = extra k x := by
    rw [neighbor k x y h, fl, fc]
    exact Sym2.eq_swap
  have classify (k : S) (e : Sym2 (Fin n)) (he : e ∈ ((T k).map (f k)).edgeSet) :
      e ∈ old k ∨ ∃ x, e = extra k x := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨_, x, y, hxy, rfl, rfl⟩ := (map_adj' _ _ _ _).mp he
      by_cases hx : x ∈ C k
      · by_cases hy : y ∈ C k
        · left
          exact (map_adj _ _ _ _).mpr ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, (fc _ _).symm, (fc _ _).symm⟩
        · exact Or.inr ⟨⟨y, hy⟩, Sym2.eq_swap.trans (leaf_edge k ⟨y, hy⟩ hxy.symm)⟩
      · exact Or.inr ⟨⟨x, hx⟩, leaf_edge k ⟨x, hx⟩ hxy⟩
  have avoid (k l : S) (x : {v : Fin l // v ∉ C l}) : extra l x ∉ old k :=
    unused k _ _ (allowed l x)
  refine ⟨f, inj, fun k l hkl => Set.disjoint_left.mpr ?_⟩
  intro e hek hel
  rcases classify k e hek with hk | ⟨x, rfl⟩
  · rcases classify l e hel with hl | ⟨y, rfl⟩
    · exact Set.disjoint_left.mp (packed k l hkl) hk hl
    · exact avoid k l y hk
  · rcases classify l _ hel with hl | ⟨y, equal⟩
    · exact avoid l k x hl
    · rcases Sym2.eq_iff.mp equal with ⟨hp, hd⟩ | ⟨hp, hd⟩
      · exact (ne_of_lt hkl) (congrArg Subtype.val (matching k l x y hp hd))
      · have reversed := allowed k x
        rw [hp, hd] at reversed
        exact asymm _ _ (allowed l y) reversed

theorem main : H1 → H2 → H3 → OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R2.H1 := by
  rintro ⟨μ, hμ, μle, prepare⟩ matchLeaves extract
  obtain ⟨q, hq, matchAt⟩ := matchLeaves μ hμ μle
  obtain ⟨p, hp, coreAt⟩ := prepare q hq
  obtain ⟨d, hd, complete⟩ := matchAt p hp
  obtain ⟨c, hc, build⟩ := coreAt d hd
  refine ⟨c, hc, ?_⟩
  filter_upwards [build, complete] with n buildN completeN
  intro T J trees orders leaves
  obtain ⟨B,subB,countB,richB⟩ := extract n T J orders leaves
  obtain ⟨C, par, f, D, A, neighbor, packed, oriented, unused, fresh, estimates⟩ :=
    buildN T B trees (subB.trans orders) countB richB
  obtain ⟨g, permitted, unique⟩ := completeN C (fun k x => f k (par k x)) D A estimates
  apply packing_of_leaf_assignments T C par neighbor f packed g _ (fun u v => v ∈ D u)
    oriented unused (fun k x => (mem_inter.mp (permitted k x)).1) unique
  intro k x y he
  exact fresh k y (he ▸ (mem_inter.mp (permitted k x)).2)

end OMA.R_Erdos743_erdos_743_variants_almost_linear_degree_R2_H1_R1
