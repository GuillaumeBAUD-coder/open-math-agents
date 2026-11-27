import FormalConjectures.ErdosProblems.«615»

/-!
# Erdős Problem 615 — Sudakov's theorem

If `f n / sqrt (log n) → ∞`, then every `K₄`-free graph on `n` vertices whose independence
number is at most `n * exp (-f n)` has `o(n²)` edges. The proof is Sudakov's dependent random
choice argument, carried out with finite sums only (no measure theory).
-/

open Filter SimpleGraph

/- ## Combinatorics: common neighbourhoods -/

/-- In a `K₄`-free graph, the common neighbourhood of an edge is an independent set. -/
lemma isIndepSet_common {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hK4 : G.CliqueFree 4) {x y : Fin m} (hxy : G.Adj x y) :
    G.IsIndepSet ((G.neighborFinset x ∩ G.neighborFinset y : Finset (Fin m)) : Set (Fin m)) := by
  intro z hz w hw _ hzw
  simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_neighborFinset] at hz hw
  obtain ⟨hxz, hyz⟩ := hz
  obtain ⟨hxw, hyw⟩ := hw
  refine hK4 ({x, y, z, w} : Finset (Fin m)) ?_
  have h1 : G.IsNClique 1 ({w} : Finset (Fin m)) := isNClique_one.2 ⟨w, rfl⟩
  have h2 : G.IsNClique 2 ({z, w} : Finset (Fin m)) := h1.insert (by simp [hzw])
  have h3 : G.IsNClique 3 ({y, z, w} : Finset (Fin m)) := h2.insert (by simp [hyz, hyw])
  exact h3.insert (by simp [hxz, hxw, hxy])

/-- Deleting one vertex per ordered adjacent pair turns a finite vertex set into an independent
set: there is an independent `I ⊆ S` with `|I| ≥ |S| - #{ordered adjacent pairs in S}`. -/
lemma exists_indep_subset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ S : Finset V, ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet (I : Set V) ∧
      S.card ≤ I.card + ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card := by
  intro S
  refine Finset.strongInductionOn S (fun S ih => ?_)
  by_cases hS : G.IsIndepSet (S : Set V)
  · exact ⟨S, Finset.Subset.refl S, hS, by simp⟩
  · obtain ⟨x, hxS, y, hyS, hne, hxy⟩ : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ G.Adj x y := by
      by_contra hcon
      apply hS
      intro a ha b hb hab hadj
      exact hcon ⟨a, ha, b, hb, hab, hadj⟩
    obtain ⟨I, hIS, hIind, hIcard⟩ := ih (S.erase x) (Finset.erase_ssubset hxS)
    refine ⟨I, hIS.trans (Finset.erase_subset x S), hIind, ?_⟩
    have hsub : ((S.erase x) ×ˢ (S.erase x)).filter (fun p => G.Adj p.1 p.2)
        ⊆ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨Finset.mem_of_mem_erase hp.1.1, Finset.mem_of_mem_erase hp.1.2⟩, hp.2⟩
    have hmemA : (x, y) ∈ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
      simp [hxS, hyS, hxy]
    have hnot : (x, y) ∉ ((S.erase x) ×ˢ (S.erase x)).filter (fun p => G.Adj p.1 p.2) := by
      simp
    have hins : insert (x, y) (((S.erase x) ×ˢ (S.erase x)).filter (fun p => G.Adj p.1 p.2))
        ⊆ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hmemA
      · exact hsub hp
    have hcard : (((S.erase x) ×ˢ (S.erase x)).filter (fun p => G.Adj p.1 p.2)).card + 1
        ≤ ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card := by
      have heq : (insert (x, y) (((S.erase x) ×ˢ (S.erase x)).filter
          (fun p => G.Adj p.1 p.2))).card
          = (((S.erase x) ×ˢ (S.erase x)).filter (fun p => G.Adj p.1 p.2)).card + 1 := by
        rw [Finset.card_insert_of_notMem hnot]
      rw [← heq]
      exact Finset.card_le_card hins
    have herase : (S.erase x).card + 1 = S.card := by
      rw [Finset.card_erase_of_mem hxS]
      have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, hxS⟩
      omega
    omega

/- ## Counting tuples -/

section Counting

variable {n : ℕ}

/-- The set of common neighbours of a tuple of vertices. -/
noncomputable def sudakovCmn (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ)
    (T : Fin t → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => ∀ i, G.Adj u (T i))

/-- The number of ordered adjacent pairs inside `sudakovCmn G t T`. -/
noncomputable def sudakovApr (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ)
    (T : Fin t → Fin n) : ℕ :=
  ((sudakovCmn G t T ×ˢ sudakovCmn G t T).filter (fun p => G.Adj p.1 p.2)).card

/-- The number of `t`-tuples all of whose entries are neighbours of `u` is `deg u ^ t`. -/
lemma card_filter_tuple (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) (u : Fin n) :
    (Finset.univ.filter (fun T : Fin t → Fin n => ∀ i, G.Adj u (T i))).card = G.degree u ^ t := by
  have hcard : (Finset.univ.filter (fun T : Fin t → Fin n => ∀ i, G.Adj u (T i))).card
      = Fintype.card {T : Fin t → Fin n // ∀ i, G.Adj u (T i)} :=
    (Fintype.card_ofFinset (s := Finset.univ.filter (fun T : Fin t → Fin n => ∀ i, G.Adj u (T i)))
      (p := {T : Fin t → Fin n | ∀ i, G.Adj u (T i)}) (by simp)).symm
  rw [hcard, Fintype.card_congr
    (Equiv.subtypePiEquivPi (β := fun _ => Fin n) (p := fun (_ : Fin t) (v : Fin n) => G.Adj u v))]
  rw [Fintype.card_fun, Fintype.card_fin]
  have hdeg : Fintype.card {v : Fin n // G.Adj u v} = G.degree u := by
    have e : {v : Fin n // G.Adj u v} ≃ {v : Fin n // v ∈ G.neighborFinset u} :=
      Equiv.subtypeEquivRight (fun v => by simp [SimpleGraph.mem_neighborFinset])
    rw [Fintype.card_congr e, Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
  rw [hdeg]

/-- The total size of the common neighbourhoods of all `t`-tuples is the sum of the `t`-th powers
of the degrees. -/
lemma sum_sudakovCmn (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) :
    ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card : ℝ) = ∑ u : Fin n, (G.degree u : ℝ) ^ t := by
  have h1 : ∀ T : Fin t → Fin n,
      ((sudakovCmn G t T).card : ℝ)
        = ∑ u : Fin n, (if (∀ i, G.Adj u (T i)) then (1 : ℝ) else 0) := by
    intro T
    rw [sudakovCmn, Finset.natCast_card_filter]
  have h2 : ∀ u : Fin n,
      (∑ T : Fin t → Fin n, (if (∀ i, G.Adj u (T i)) then (1 : ℝ) else 0))
        = (G.degree u : ℝ) ^ t := by
    intro u
    rw [Finset.sum_boole, card_filter_tuple, Nat.cast_pow]
  calc ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card : ℝ)
      = ∑ T : Fin t → Fin n, ∑ u : Fin n, (if (∀ i, G.Adj u (T i)) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun T _ => h1 T)
    _ = ∑ u : Fin n, ∑ T : Fin t → Fin n, (if (∀ i, G.Adj u (T i)) then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ u : Fin n, (G.degree u : ℝ) ^ t := Finset.sum_congr rfl (fun u _ => h2 u)

/-- The number of ordered adjacent pairs inside a common neighbourhood, written as a double sum. -/
lemma apr_cast (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) (T : Fin t → Fin n) :
    ((sudakovApr G t T : ℕ) : ℝ) = ∑ x : Fin n, ∑ y : Fin n,
      (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0) := by
  rw [sudakovApr, sudakovCmn, Finset.natCast_card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : (∀ i, G.Adj x (T i))
  · rw [if_pos hx]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : (∀ i, G.Adj y (T i))
    · rw [if_pos hy]
      by_cases hxy : G.Adj x y <;> simp [hx, hy, hxy]
    · rw [if_neg hy]
      simp [hx, hy]
  · rw [if_neg hx]
    simp [hx]

/-- The number of `t`-tuples sitting in the common neighbourhood of two vertices `x`, `y`
is `|N x ∩ N y| ^ t`. -/
lemma card_filter_tuple_pair (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) (x y : Fin n) :
    (Finset.univ.filter (fun T : Fin t → Fin n =>
        (∀ i, G.Adj x (T i)) ∧ (∀ i, G.Adj y (T i)))).card
      = (G.neighborFinset x ∩ G.neighborFinset y).card ^ t := by
  have hpred : (Finset.univ.filter (fun T : Fin t → Fin n =>
      (∀ i, G.Adj x (T i)) ∧ (∀ i, G.Adj y (T i))))
      = (Finset.univ.filter (fun T : Fin t → Fin n =>
          ∀ i, (G.Adj x (T i) ∧ G.Adj y (T i)))) := by
    refine Finset.filter_congr (fun T _ => ?_)
    exact forall_and.symm
  rw [hpred]
  have hcard : (Finset.univ.filter (fun T : Fin t → Fin n =>
      ∀ i, (G.Adj x (T i) ∧ G.Adj y (T i)))).card
      = Fintype.card {T : Fin t → Fin n // ∀ i, (G.Adj x (T i) ∧ G.Adj y (T i))} :=
    (Fintype.card_ofFinset
      (s := Finset.univ.filter (fun T : Fin t → Fin n => ∀ i, (G.Adj x (T i) ∧ G.Adj y (T i))))
      (p := {T : Fin t → Fin n | ∀ i, (G.Adj x (T i) ∧ G.Adj y (T i))}) (by simp)).symm
  rw [hcard, Fintype.card_congr
    (Equiv.subtypePiEquivPi (β := fun _ => Fin n)
      (p := fun (_ : Fin t) (v : Fin n) => G.Adj x v ∧ G.Adj y v))]
  rw [Fintype.card_fun, Fintype.card_fin]
  have hmem : (G.neighborFinset x ∩ G.neighborFinset y)
      = (Finset.univ.filter (fun v : Fin n => G.Adj x v ∧ G.Adj y v)) := by
    ext v
    simp [Finset.mem_inter, mem_neighborFinset]
  have hd : Fintype.card {v : Fin n // G.Adj x v ∧ G.Adj y v}
      = (G.neighborFinset x ∩ G.neighborFinset y).card := by
    rw [hmem]
    exact Fintype.card_ofFinset (Finset.univ.filter (fun v : Fin n => G.Adj x v ∧ G.Adj y v))
      (p := {v : Fin n | G.Adj x v ∧ G.Adj y v}) (by simp)
  rw [hd]

/-- The total number of ordered adjacent pairs inside the common neighbourhoods, summed over all
`t`-tuples, as a triple sum. -/
lemma sum_apr (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) :
    ∑ T : Fin t → Fin n, ((sudakovApr G t T : ℕ) : ℝ)
      = ∑ x : Fin n, ∑ y : Fin n, ∑ T : Fin t → Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0) := by
  calc ∑ T : Fin t → Fin n, ((sudakovApr G t T : ℕ) : ℝ)
      = ∑ T : Fin t → Fin n, ∑ x : Fin n, ∑ y : Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun T _ => apr_cast G t T)
    _ = ∑ x : Fin n, ∑ T : Fin t → Fin n, ∑ y : Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ x : Fin n, ∑ y : Fin n, ∑ T : Fin t → Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

/-- Bound on the total number of ordered adjacent pairs inside common neighbourhoods. -/
lemma sum_apr_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hK4 : G.CliqueFree 4) (t : ℕ)
    {α : ℝ} (hα : (G.indepNum : ℝ) ≤ α) :
    ∑ T : Fin t → Fin n, ((sudakovApr G t T : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 * α ^ t := by
  classical
  have hα0 : (0 : ℝ) ≤ α := le_trans (Nat.cast_nonneg _) hα
  have hterm : ∀ x y : Fin n, (∑ T : Fin t → Fin n,
      (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0)) ≤ α ^ t := by
    intro x y
    by_cases hxy : G.Adj x y
    · have hf : (Finset.univ.filter (fun T : Fin t → Fin n =>
          (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y)))
          = (Finset.univ.filter (fun T : Fin t → Fin n =>
              (∀ i, G.Adj x (T i)) ∧ (∀ i, G.Adj y (T i)))) := by
        refine Finset.filter_congr (fun T _ => ?_)
        simp [sudakovCmn, hxy]
      have hsum : (∑ T : Fin t → Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0))
          = ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) ^ t := by
        rw [Finset.sum_boole, hf, card_filter_tuple_pair, Nat.cast_pow]
      have hind : ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) ≤ α := by
        have hI := SimpleGraph.IsIndepSet.card_le_indepNum (G := G)
          (isIndepSet_common G hK4 hxy)
        have hcast : ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) ≤ (G.indepNum : ℝ) := by
          exact_mod_cast hI
        linarith
      rw [hsum]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hind t
    · have hzero : (∑ T : Fin t → Fin n,
          (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0)) = 0 := by
        simp [hxy]
      rw [hzero]
      exact pow_nonneg hα0 t
  rw [sum_apr]
  calc ∑ x : Fin n, ∑ y : Fin n, ∑ T : Fin t → Fin n,
        (if (x ∈ sudakovCmn G t T ∧ y ∈ sudakovCmn G t T ∧ G.Adj x y) then (1 : ℝ) else 0)
      ≤ ∑ x : Fin n, ∑ y : Fin n, α ^ t :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hterm x y))
    _ = (n : ℝ) * ((n : ℝ) * α ^ t) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ = (n : ℝ) ^ 2 * α ^ t := by ring

end Counting

/- ## The main theorem -/

/-- Sudakov's theorem: `rt(n; 4, n e^{-f(n)}) = o(n²)` when `f(n)/sqrt(log n) → ∞`. -/
theorem OMA.solution : type_of% @Erdos615.erdos_615.variants.sudakov := by
  intro f hf ε hε
  classical
  -- truncate `ε` so that `2 δ ≤ 1`
  set δ : ℝ := min ε (1 / 4) with hδdef
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδle : δ ≤ ε := min_le_left _ _
  have hδq : δ ≤ 1 / 4 := min_le_right _ _
  have h2δpos : (0 : ℝ) < 2 * δ := by linarith
  have h2δle : 2 * δ ≤ 1 / 2 := by linarith
  set L : ℝ := Real.log (1 / (2 * δ)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    rw [lt_div_iff₀ h2δpos]
    linarith
  set M : ℝ := Real.sqrt (200 * L) + 12 * L + 8 with hMdef
  have hMsq0 : 0 ≤ Real.sqrt (200 * L) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  have hM8 : 8 ≤ M := by rw [hMdef]; linarith
  have hM12 : 12 * L ≤ M := by rw [hMdef]; linarith
  have hMsq : Real.sqrt (200 * L) ≤ M := by rw [hMdef]; linarith
  -- the threshold in `n`
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n := by
    have h : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h.eventually (eventually_ge_atTop 1)
  have hev2 : ∀ᶠ n : ℕ in atTop, M ≤ f n / Real.sqrt (Real.log n) :=
    hf.eventually (eventually_ge_atTop M)
  rw [Filter.eventually_atTop] at hev1 hev2 ⊢
  obtain ⟨N1, hN1⟩ := hev1
  obtain ⟨N2, hN2⟩ := hev2
  refine ⟨max N1 (max N2 2), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hpos : (0 : ℕ) < n := by omega
    exact_mod_cast hpos
  have hlog : (1 : ℝ) ≤ Real.log n := hN1 n (by omega)
  have hlogpos : (0 : ℝ) < Real.log n := by linarith
  have hfdiv : M ≤ f n / Real.sqrt (Real.log n) := hN2 n (by omega)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (Real.log n) := by
    rw [Real.one_le_sqrt]
    exact hlog
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Real.log n) := by linarith
  have hsplit : f n = (f n / Real.sqrt (Real.log n)) * Real.sqrt (Real.log n) := by
    field_simp
  have hfM : M ≤ f n := by
    rw [hsplit]
    calc M = M * 1 := (mul_one M).symm
      _ ≤ (f n / Real.sqrt (Real.log n)) * Real.sqrt (Real.log n) :=
          mul_le_mul hfdiv hsqrt1 (by norm_num) (le_trans hM0 hfdiv)
  have hf8 : 8 ≤ f n := le_trans hM8 hfM
  have hf2 : 2 ≤ f n := by linarith
  have hfpos : 0 < f n := by linarith
  have hf12 : 12 * L ≤ f n := le_trans hM12 hfM
  have hfsq : 200 * L * Real.log n ≤ (f n) ^ 2 := by
    have hstep : Real.sqrt (200 * L) * Real.sqrt (Real.log n) ≤ f n := by
      calc Real.sqrt (200 * L) * Real.sqrt (Real.log n)
          ≤ M * Real.sqrt (Real.log n) :=
            mul_le_mul_of_nonneg_right hMsq (le_of_lt hsqrtpos)
        _ ≤ f n := by
            rw [hsplit]
            exact mul_le_mul_of_nonneg_right hfdiv (le_of_lt hsqrtpos)
    have h2 : (Real.sqrt (200 * L) * Real.sqrt (Real.log n)) ^ 2 ≤ (f n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hstep 2
    have h3 : (Real.sqrt (200 * L) * Real.sqrt (Real.log n)) ^ 2 = 200 * L * Real.log n := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    linarith [h2, h3]
  -- the tuple length
  set t : ℕ := Nat.ceil (2 * Real.log n / f n) + 2 with htdef
  have ht2 : 2 ≤ t := by
    have h0 : 0 ≤ Nat.ceil (2 * Real.log n / f n) := Nat.zero_le _
    omega
  have ht1 : 1 ≤ t := by omega
  have hxt : 2 * Real.log n / f n + 2 ≤ (t : ℝ) := by
    have h := Nat.le_ceil (2 * Real.log n / f n)
    rw [htdef]
    push_cast
    linarith
  have hxt2 : (t : ℝ) < 2 * Real.log n / f n + 3 := by
    have h := Nat.ceil_lt_add_one (a := 2 * Real.log n / f n)
      (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.log n / f n))
    rw [htdef]
    push_cast at h ⊢
    linarith
  have htf : 2 * Real.log n + 2 * f n ≤ (t : ℝ) * f n := by
    have h := mul_le_mul_of_nonneg_right hxt (le_of_lt hfpos)
    have heq : (2 * Real.log n / f n + 2) * f n = 2 * Real.log n + 2 * f n := by
      field_simp
    linarith [h, heq]
  have htL : (t : ℝ) * L < f n / 2 := by
    have h1 : (t : ℝ) * L < (2 * Real.log n / f n + 3) * L :=
      mul_lt_mul_of_pos_right hxt2 hLpos
    have h2 : (2 * Real.log n / f n + 3) * L = 2 * L * Real.log n / f n + 3 * L := by
      field_simp
    have h3 : 2 * L * Real.log n / f n ≤ f n / 100 := by
      rw [div_le_iff₀ hfpos]
      nlinarith [hfsq]
    have h4 : 3 * L ≤ f n / 4 := by linarith
    linarith [h1, h2, h3, h4]
  -- the two sides of the inequality
  set α : ℝ := (n : ℝ) * Real.exp (-(f n)) with hαdef
  have hαn : α / (n : ℝ) = Real.exp (-(f n)) := by
    rw [hαdef]
    field_simp
  have hlog2δ : Real.log (2 * δ) = -L := by
    rw [hLdef, one_div, Real.log_inv, neg_neg]
  have hexp2δ : (2 * δ) ^ t = Real.exp (-((t : ℝ) * L)) := by
    have h0 : (2 * δ) ^ t = Real.exp (Real.log (2 * δ)) ^ t := by rw [Real.exp_log h2δpos]
    rw [h0, ← Real.exp_nat_mul, hlog2δ]
    congr 1
    ring
  have hexptr : (Real.exp (-(f n))) ^ t = Real.exp (-((t : ℝ) * f n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hB : (n : ℝ) ^ 2 * (α / (n : ℝ)) ^ t ≤ α := by
    rw [hαn, hexptr]
    have h1 : Real.exp (-((t : ℝ) * f n)) ≤ Real.exp (-(2 * Real.log n + 2 * f n)) := by
      apply Real.exp_le_exp.2
      linarith [htf]
    have h2 : (n : ℝ) ^ 2 * Real.exp (-(2 * Real.log n + 2 * f n)) = Real.exp (-(2 * f n)) := by
      have hsp : -(2 * Real.log n + 2 * f n) = -(2 * Real.log n) + -(2 * f n) := by ring
      rw [hsp, Real.exp_add]
      have h3 : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
        have hl : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
          rw [Real.log_pow]
          push_cast
          ring
        rw [← hl, Real.exp_neg, Real.exp_log (by positivity)]
      rw [h3]
      field_simp
    calc (n : ℝ) ^ 2 * Real.exp (-((t : ℝ) * f n))
        ≤ (n : ℝ) ^ 2 * Real.exp (-(2 * Real.log n + 2 * f n)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp (-(2 * f n)) := h2
      _ ≤ Real.exp (-(f n)) := Real.exp_le_exp.2 (by linarith)
      _ ≤ (n : ℝ) * Real.exp (-(f n)) := by
          have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          calc Real.exp (-(f n)) = 1 * Real.exp (-(f n)) := (one_mul _).symm
            _ ≤ (n : ℝ) * Real.exp (-(f n)) :=
                mul_le_mul_of_nonneg_right hn1' (le_of_lt (Real.exp_pos _))
  have hA : 2 * α < (n : ℝ) * (2 * δ) ^ t := by
    rw [hexp2δ, hαdef]
    have hexp2 : 2 * Real.exp (-(f n)) ≤ Real.exp (-(f n / 2)) := by
      have hsp : -(f n / 2) = -(f n) + f n / 2 := by ring
      rw [hsp, Real.exp_add]
      have h2le : 2 ≤ Real.exp (f n / 2) := by
        rw [← Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
        have hlog2 : Real.log 2 ≤ 1 := by
          have hlog2' := Real.log_two_lt_d9
          linarith
        linarith
      calc 2 * Real.exp (-(f n)) = Real.exp (-(f n)) * 2 := by ring
        _ ≤ Real.exp (-(f n)) * Real.exp (f n / 2) :=
            mul_le_mul_of_nonneg_left h2le (le_of_lt (Real.exp_pos _))
    have hexp3 : Real.exp (-(f n / 2)) < Real.exp (-((t : ℝ) * L)) := by
      apply Real.exp_lt_exp.2
      linarith [htL]
    calc 2 * ((n : ℝ) * Real.exp (-(f n))) = (n : ℝ) * (2 * Real.exp (-(f n))) := by ring
      _ ≤ (n : ℝ) * Real.exp (-(f n / 2)) :=
          mul_le_mul_of_nonneg_left hexp2 (le_of_lt hnR)
      _ < (n : ℝ) * Real.exp (-((t : ℝ) * L)) := mul_lt_mul_of_pos_left hexp3 hnR
  have hdiv : α + (n : ℝ) ^ 2 * (α / (n : ℝ)) ^ t < (n : ℝ) * (2 * δ) ^ t := by
    linarith [hA, hB]
  -- counting
  intro G hK4 hα
  by_contra hcon
  have hcon' : ε * (n : ℝ) ^ 2 < (G.edgeFinset.card : ℝ) := not_le.1 hcon
  have hm : δ * (n : ℝ) ^ 2 < (G.edgeFinset.card : ℝ) := by
    have h1 : δ * (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hδle (by positivity)
    linarith
  have hD : ∑ u : Fin n, (G.degree u : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have hdeg := G.sum_degrees_eq_twice_card_edges
    have h' : ((∑ u : Fin n, G.degree u : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
      rw [hdeg]
    push_cast at h'
    linarith [h']
  have hntpos : (0 : ℝ) < (n : ℝ) ^ t := by positivity
  have hNt : ((Finset.univ : Finset (Fin t → Fin n)).card : ℝ) = (n : ℝ) ^ t := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  have hsumA : (n : ℝ) ^ (t + 1) * (2 * δ) ^ t
      ≤ ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card : ℝ) := by
    rw [sum_sudakovCmn]
    have hDge : 2 * δ * (n : ℝ) ^ 2 ≤ ∑ u : Fin n, (G.degree u : ℝ) := by linarith
    have hJ := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
      (f := fun u : Fin n => (G.degree u : ℝ)) (fun i _ => Nat.cast_nonneg _) (t - 1)
    rw [Finset.card_univ, Fintype.card_fin, Nat.sub_add_cancel ht1] at hJ
    have hkey : (2 * δ) ^ t * (n : ℝ) ^ (2 * t)
        ≤ (∑ u : Fin n, (G.degree u : ℝ)) ^ t := by
      rw [show (2 * δ) ^ t * (n : ℝ) ^ (2 * t) = (2 * δ * (n : ℝ) ^ 2) ^ t by
        conv_rhs => rw [mul_pow]
        rw [← pow_mul]]
      exact pow_le_pow_left₀ (by positivity) hDge t
    have hnsub : (0 : ℝ) < (n : ℝ) ^ (t - 1) := by positivity
    have hstep : (2 * δ) ^ t * (n : ℝ) ^ (2 * t) ≤ (∑ u : Fin n, (G.degree u : ℝ) ^ t)
        * (n : ℝ) ^ (t - 1) := by
      calc (2 * δ) ^ t * (n : ℝ) ^ (2 * t)
          ≤ (∑ u : Fin n, (G.degree u : ℝ)) ^ t := hkey
        _ ≤ (n : ℝ) ^ (t - 1) * (∑ u : Fin n, (G.degree u : ℝ) ^ t) := hJ
        _ = (∑ u : Fin n, (G.degree u : ℝ) ^ t) * (n : ℝ) ^ (t - 1) := by ring
    have hfin : (2 * δ) ^ t * (n : ℝ) ^ (t + 1) ≤ ∑ u : Fin n, (G.degree u : ℝ) ^ t := by
      have h1 : (2 * δ) ^ t * (n : ℝ) ^ (2 * t) / (n : ℝ) ^ (t - 1)
          ≤ ∑ u : Fin n, (G.degree u : ℝ) ^ t := by
        rw [div_le_iff₀ hnsub]
        linarith [hstep]
      have h2 : (2 * δ) ^ t * (n : ℝ) ^ (2 * t) / (n : ℝ) ^ (t - 1)
          = (2 * δ) ^ t * (n : ℝ) ^ (t + 1) := by
        rw [div_eq_mul_inv, mul_assoc,
          ← pow_sub₀ (n : ℝ) (ne_of_gt hnR) (by omega : t - 1 ≤ 2 * t),
          show 2 * t - (t - 1) = t + 1 by omega]
      linarith [h1, h2]
    have hfin' : (n : ℝ) ^ (t + 1) * (2 * δ) ^ t ≤ ∑ u : Fin n, (G.degree u : ℝ) ^ t := by
      rw [mul_comm]
      exact hfin
    linarith [hfin']
  have hsumP : ∑ T : Fin t → Fin n, ((sudakovApr G t T : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 * α ^ t :=
    sum_apr_le G hK4 t hα
  have hpowdiv : (n : ℝ) ^ t * ((n : ℝ) ^ 2 * (α / (n : ℝ)) ^ t) = (n : ℝ) ^ 2 * α ^ t := by
    have hnt : (n : ℝ) ^ t ≠ 0 := ne_of_gt hntpos
    rw [div_pow]
    field_simp
  have hmul : (n : ℝ) ^ t * (α + (n : ℝ) ^ 2 * (α / (n : ℝ)) ^ t)
      < (n : ℝ) ^ t * ((n : ℝ) * (2 * δ) ^ t) :=
    mul_lt_mul_of_pos_left hdiv hntpos
  have hexp : (n : ℝ) ^ t * (α + (n : ℝ) ^ 2 * (α / (n : ℝ)) ^ t)
      = (n : ℝ) ^ t * α + (n : ℝ) ^ 2 * α ^ t := by
    rw [mul_add, hpowdiv]
  have hexp2 : (n : ℝ) ^ t * ((n : ℝ) * (2 * δ) ^ t) = (n : ℝ) ^ (t + 1) * (2 * δ) ^ t := by
    rw [pow_succ]
    ring
  obtain ⟨T, hT⟩ : ∃ T : Fin t → Fin n, α < (sudakovCmn G t T).card - (sudakovApr G t T : ℝ) := by
    by_contra hc
    push Not at hc
    have hsub : ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card - (sudakovApr G t T : ℝ))
        = ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card : ℝ)
          - ∑ T : Fin t → Fin n, ((sudakovApr G t T : ℕ) : ℝ) := by
      simp only [Finset.sum_sub_distrib]
    have hle : ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card - (sudakovApr G t T : ℝ)) ≤ (n : ℝ) ^ t * α := by
      have h1 : ∑ T : Fin t → Fin n, ((sudakovCmn G t T).card - (sudakovApr G t T : ℝ))
          ≤ ∑ _T : Fin t → Fin n, α := Finset.sum_le_sum (fun T _ => hc T)
      rw [Finset.sum_const, nsmul_eq_mul, hNt] at h1
      exact h1
    rw [hsub] at hle
    linarith [hle, hsumA, hsumP, hmul, hexp, hexp2]
  obtain ⟨I, hIsub, hIind, hIcard⟩ := exists_indep_subset G (sudakovCmn G t T)
  have hindep : (I.card : ℝ) ≤ (G.indepNum : ℝ) := by
    have h := SimpleGraph.IsIndepSet.card_le_indepNum (G := G) hIind
    exact_mod_cast h
  have hcast : ((sudakovCmn G t T).card : ℝ) ≤ (I.card : ℝ) + ((sudakovApr G t T : ℕ) : ℝ) := by
    exact_mod_cast hIcard
  rw [hαdef] at hα
  linarith [hT, hindep, hcast, hα]
