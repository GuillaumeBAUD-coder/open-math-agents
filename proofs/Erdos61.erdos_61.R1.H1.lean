import OMAReductions.R_Erdos61_erdos_61_R1

-- Step Erdos61.erdos_61.R1.H1: hypothesis H1 of reduction Erdos61.erdos_61.R1
-- Credit: @yhay81
-- uses note #154121
-- H1 := ∀ m : ℕ,     (∃ c > (0 : ℝ), IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin m)) (fun n : ℕ => (n : ℝ) ^ c)) ∧     (∃ c > (0 : ℝ), IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin m)) (fun n : ℕ => (n : ℝ) ^ c))

open SimpleGraph Filter

private lemma greedy_indep_of_deg_lt {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ (t d : ℕ) (T : Finset V), 1 ≤ d → t * d ≤ T.card →
      (∀ v ∈ T, (T.filter (G.Adj v)).card < d) →
      ∃ I : Finset V, I ⊆ T ∧ G.IsNIndepSet t I
  | 0, _, _, _, _, _ => ⟨∅, Finset.empty_subset _, by simp [SimpleGraph.isNIndepSet_iff]⟩
  | t + 1, d, T, hd, hcard, hdeg => by
    have hpos : 0 < T.card := lt_of_lt_of_le (by nlinarith) hcard
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    let T' : Finset V := T.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
    have hsub : T' ⊆ T := Finset.filter_subset _ T
    have hdiff_sub : T \ T' ⊆ insert v (T.filter (G.Adj v)) := by
      intro u hu
      rw [Finset.mem_sdiff] at hu
      rcases hu with ⟨huT, huT'⟩
      rw [Finset.mem_insert, Finset.mem_filter]
      by_cases huv : u = v
      · exact Or.inl huv
      · refine Or.inr ⟨huT, ?_⟩
        by_contra hna
        exact huT' (Finset.mem_filter.mpr ⟨huT, huv, hna⟩)
    have hdiff_le : (T \ T').card ≤ d := by
      have h1 : (T \ T').card ≤ (insert v (T.filter (G.Adj v))).card :=
        Finset.card_le_card hdiff_sub
      have h2 : (insert v (T.filter (G.Adj v))).card ≤ (T.filter (G.Adj v)).card + 1 :=
        Finset.card_insert_le _ _
      have h3 : (T.filter (G.Adj v)).card < d := hdeg v hv
      omega
    have hT'_card : t * d ≤ T'.card := by
      have hpart : T'.card + (T \ T').card = T.card := by
        rw [Finset.card_sdiff_of_subset hsub]
        have := Finset.card_le_card hsub
        omega
      have : (t + 1) * d = t * d + d := by ring
      omega
    have hT'_deg : ∀ w ∈ T', (T'.filter (G.Adj w)).card < d := by
      intro w hw
      have hfilt : T'.filter (G.Adj w) ⊆ T.filter (G.Adj w) :=
        Finset.filter_subset_filter _ hsub
      exact lt_of_le_of_lt (Finset.card_le_card hfilt) (hdeg w (hsub hw))
    obtain ⟨I, hIT', hI⟩ := greedy_indep_of_deg_lt G t d T' hd hT'_card hT'_deg
    refine ⟨insert v I, Finset.insert_subset hv (hIT'.trans hsub), ?_⟩
    rw [SimpleGraph.isNIndepSet_iff] at hI ⊢
    have hvI : v ∉ I := fun hvI => (Finset.mem_filter.mp (hIT' hvI)).2.1 rfl
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy hadj
      rw [Finset.mem_coe, Finset.mem_insert] at hx hy
      rcases hx with rfl | hxI
      · rcases hy with rfl | hyI
        · exact hxy rfl
        · exact (Finset.mem_filter.mp (hIT' hyI)).2.2 hadj
      · rcases hy with rfl | hyI
        · exact (Finset.mem_filter.mp (hIT' hxI)).2.2 hadj.symm
        · exact hI.1 hxI hyI hxy hadj
    · rw [Finset.card_insert_of_notMem hvI, hI.2]

private lemma ramsey_clique_or_indep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ (m k : ℕ) (S : Finset V), 1 ≤ k → k ^ m ≤ S.card →
      (∃ C : Finset V, C ⊆ S ∧ G.IsNClique (m + 1) C) ∨
      (∃ I : Finset V, I ⊆ S ∧ G.IsNIndepSet k I)
  | 0, _, S, _, hcard => by
    have hpos : 0 < S.card := lt_of_lt_of_le (by simp) hcard
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact Or.inl ⟨{v}, Finset.singleton_subset_iff.mpr hv, SimpleGraph.isNClique_singleton.mpr rfl⟩
  | m + 1, k, S, hk, hcard => by
    by_cases hhigh : ∃ v ∈ S, k ^ m ≤ (S.filter (G.Adj v)).card
    · obtain ⟨v, hv, hdeg⟩ := hhigh
      let S' := S.filter (G.Adj v)
      have hsub : S' ⊆ S := Finset.filter_subset _ S
      rcases ramsey_clique_or_indep G m k S' hk hdeg with ⟨C, hCS', hC⟩ | ⟨I, hIS', hI⟩
      · refine Or.inl ⟨insert v C, Finset.insert_subset hv (hCS'.trans hsub), ?_⟩
        exact hC.insert (fun u hu => (Finset.mem_filter.mp (hCS' hu)).2)
      · exact Or.inr ⟨I, hIS'.trans hsub, hI⟩
    · push Not at hhigh
      have hd : 1 ≤ k ^ m := Nat.one_le_pow m k (by omega)
      have hmul : k * k ^ m ≤ S.card := by
        simpa [pow_succ'] using hcard
      exact Or.inr (greedy_indep_of_deg_lt G k (k ^ m) S hd hmul hhigh)

private lemma exists_comap_top_of_isNClique {n m : ℕ} {G : SimpleGraph (Fin n)} {C : Finset (Fin n)}
    (hC : G.IsNClique m C) :
    ∃ g : Fin m ↪ Fin n, (⊤ : SimpleGraph (Fin m)) = G.comap g := by
  have hcard : Fintype.card C = m := by
    rw [Fintype.card_coe, hC.card_eq]
  let e : Fin m ≃ C := (Fintype.equivFinOfCardEq hcard).symm
  let g : Fin m ↪ Fin n := e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨g, ?_⟩
  ext a b
  simp only [SimpleGraph.top_adj, SimpleGraph.comap_adj, g, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, Function.Embedding.coe_subtype]
  constructor
  · intro hab
    have hne : (e a : Fin n) ≠ (e b : Fin n) := fun h => hab (e.injective (Subtype.ext h))
    exact hC.isClique (e a).prop (e b).prop hne
  · intro hadj hab
    rw [hab] at hadj
    exact hadj.ne rfl

private lemma le_indepNum_of_isNIndepSet {n k : ℕ} {G : SimpleGraph (Fin n)} {I : Finset (Fin n)}
    (hI : G.IsNIndepSet k I) : k ≤ G.indepNum := by
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro t ⟨s, hs⟩
    rw [← hs.card_eq]
    simpa using s.card_le_univ
  · exact ⟨I, hI⟩

private lemma isErdosHajnal_top (m : ℕ) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin m))
      (fun n : ℕ => (n : ℝ) ^ c) := by
  rcases m with _ | r
  · refine ⟨1, zero_lt_one, Filter.Eventually.of_forall fun n G hno => ?_⟩
    exfalso
    refine hno ⟨Function.Embedding.ofIsEmpty, ?_⟩
    ext a
    exact Fin.elim0 a
  · rcases r with _ | r'
    · refine ⟨1, zero_lt_one, ?_⟩
      unfold Erdos61.IsErdosHajnalLowerBound
      rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn G hno => ?_⟩
      exfalso
      have h0 : 0 < n := by omega
      let g : Fin (0 + 1) ↪ Fin n := ⟨fun _ => ⟨0, h0⟩, fun a b _ => Fin.ext (by omega)⟩
      refine hno ⟨g, ?_⟩
      ext a b
      have hab : a = b := Fin.ext (by omega)
      subst hab
      simp
    · let d : ℕ := r' + 1
      have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
      let c : ℝ := 1 / (2 * (d : ℝ))
      have hc_pos : 0 < c := by positivity
      refine ⟨c, hc_pos, ?_⟩
      unfold Erdos61.IsErdosHajnalLowerBound
      rw [Filter.eventually_atTop]
      refine ⟨2 ^ (2 * d), fun n hn G hno => ?_⟩
      classical
      let x : ℝ := (n : ℝ) ^ c
      have hx_ge_two : (2 : ℝ) ≤ x := by
        have h1 : ((2 ^ (2 * d) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h2 : ((2 ^ (2 * d) : ℕ) : ℝ) ^ c ≤ x :=
          Real.rpow_le_rpow (by positivity) h1 hc_pos.le
        have h3 : ((2 ^ (2 * d) : ℕ) : ℝ) ^ c = 2 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) (2 * d),
            ← Real.rpow_mul (by positivity)]
          have hexp : ((2 * d : ℕ) : ℝ) * c = 1 := by
            dsimp only [c]
            push_cast
            field_simp
          rw [hexp, Real.rpow_one]
        linarith
      have hx_sq : x ^ 2 = (n : ℝ) ^ (1 / (d : ℝ)) := by
        dsimp only [x, c]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        push_cast
        field_simp
      have hx_add_le : x + 1 ≤ x ^ 2 := by nlinarith
      let k : ℕ := Nat.floor (x ^ 2)
      have hx_lt_k : x < (k : ℝ) := by
        have hlt : x ^ 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (x ^ 2)
        linarith
      have hk_ge_one : 1 ≤ k := by
        have h1 : (1 : ℝ) < (k : ℝ) := by linarith
        exact_mod_cast h1.le
      have hk_pow_le : k ^ d ≤ n := by
        have hk_le : (k : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) := by
          rw [← hx_sq]
          exact Nat.floor_le (by positivity)
        have hpow_le : ((k : ℝ)) ^ d ≤ ((n : ℝ) ^ (1 / (d : ℝ))) ^ d :=
          pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le d
        have hrhs : ((n : ℝ) ^ (1 / (d : ℝ))) ^ d = (n : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
          have hexp : (1 / (d : ℝ)) * (d : ℝ) = 1 := by field_simp
          rw [hexp, Real.rpow_one]
        rw [hrhs] at hpow_le
        exact_mod_cast hpow_le
      have huniv : k ^ d ≤ (Finset.univ : Finset (Fin n)).card := by
        simpa using hk_pow_le
      rcases ramsey_clique_or_indep G d k Finset.univ hk_ge_one huniv with
        ⟨C, _, hC⟩ | ⟨I, _, hI⟩
      · exfalso
        exact hno (exists_comap_top_of_isNClique hC)
      · left
        have hle : k ≤ G.indepNum := le_indepNum_of_isNIndepSet hI
        have hleR : (k : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast hle
        exact le_trans hx_lt_k.le hleR

private lemma indepNum_compl_eq_cliqueNum {V : Type*} (G : SimpleGraph V) :
    Gᶜ.indepNum = G.cliqueNum := by
  unfold SimpleGraph.indepNum SimpleGraph.cliqueNum
  congr 1
  ext k
  simp

private lemma cliqueNum_compl_eq_indepNum {V : Type*} (G : SimpleGraph V) :
    Gᶜ.cliqueNum = G.indepNum := by
  unfold SimpleGraph.indepNum SimpleGraph.cliqueNum
  congr 1
  ext k
  simp

private lemma isErdosHajnal_bot_of_top {m : ℕ} {f : ℕ → ℝ}
    (htop : Erdos61.IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin m)) f) :
    Erdos61.IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin m)) f := by
  unfold Erdos61.IsErdosHajnalLowerBound at htop ⊢
  filter_upwards [htop] with n hn G hG
  have hGc : ¬ ∃ g : Fin m ↪ Fin n, (⊤ : SimpleGraph (Fin m)) = Gᶜ.comap g := by
    rintro ⟨g, hg⟩
    refine hG ⟨g, ?_⟩
    ext a b
    simp only [SimpleGraph.bot_adj, SimpleGraph.comap_adj, false_iff]
    intro hadj
    have hab : a ≠ b := by
      intro heq
      rw [heq] at hadj
      exact hadj.ne rfl
    have htop_adj : (⊤ : SimpleGraph (Fin m)).Adj a b := hab
    rw [hg, SimpleGraph.comap_adj, SimpleGraph.compl_adj] at htop_adj
    exact htop_adj.2 hadj
  rcases hn Gᶜ hGc with hind | hcl
  · rw [indepNum_compl_eq_cliqueNum] at hind
    exact Or.inr hind
  · rw [cliqueNum_compl_eq_indepNum] at hcl
    exact Or.inl hcl

theorem OMA.solution : OMA.R_Erdos61_erdos_61_R1.H1 := by
  intro m
  obtain ⟨c, hc, htop⟩ := isErdosHajnal_top m
  exact ⟨⟨c, hc, htop⟩, ⟨c, hc, isErdosHajnal_bot_of_top htop⟩⟩
