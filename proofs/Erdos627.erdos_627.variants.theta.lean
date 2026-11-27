import FormalConjectures.ErdosProblems.«627»

/-! # Erdős 627: order of the maximum chromatic-to-clique ratio

The lower estimate is @Halldon's first-moment proof from this project's merged PR #964
(commit 6a9ea34d011c01c9825ef112db808c9d31f96da4), included here because a submission is
checked as a single file. For the upper estimate, apply the off-diagonal Ramsey bound
in each remaining induced subgraph and color one independent set at a time. -/

open Filter SimpleGraph
open scoped Asymptotics

open Filter SimpleGraph

namespace Erdos627Lower

/- The Boolean edge-labelling construction and union bound are from @TheWaler's
   proof of Erdős 78 in this repository (PR #299, commit 1dba85f).
   We retain only the finite graph counting argument. -/
private abbrev Pair (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

private def toGraph {n : ℕ} (c : Pair n → Bool) : SimpleGraph (Fin n) where
  Adj u v :=
    if h : u < v then c ⟨(u, v), h⟩ = true
    else if h' : v < u then c ⟨(v, u), h'⟩ = true
    else False
  symm := ⟨by
    intro u v huv
    by_cases h1 : u < v
    · have h2 : ¬ v < u := not_lt_of_gt h1
      simp only [h1, h2, ↓reduceDIte] at huv ⊢
      exact huv
    · by_cases h2 : v < u
      · simp only [h1, h2, ↓reduceDIte] at huv ⊢
        exact huv
      · simp only [h1, h2, ↓reduceDIte] at huv⟩
  loopless := ⟨by
    intro u
    simp⟩

private lemma toGraph_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c).Adj u v ↔ c ⟨(u, v), h⟩ = true := by
  simp [toGraph, h]

private lemma toGraph_compl_adj_of_lt {n : ℕ} (c : Pair n → Bool) {u v : Fin n} (h : u < v) :
    (toGraph c)ᶜ.Adj u v ↔ c ⟨(u, v), h⟩ = false := by
  simp [SimpleGraph.compl_adj, ne_of_lt h, toGraph, h]

private def pairsIn {n : ℕ} (s : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter (fun p => p.1.1 ∈ s ∧ p.1.2 ∈ s)

private lemma pairsIn_card {n : ℕ} (s : Finset (Fin n)) :
    (pairsIn s).card = s.card * (s.card - 1) / 2 := by
  let L : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 < p.2)
  let G : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.2 < p.1)
  let D : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun p => p.1 = p.2)
  have hPL : (pairsIn s).card = L.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [L, Finset.mem_filter, Finset.mem_product]
      exact ⟨hp, p.2⟩
    · intro p₁ _ p₂ _ h
      exact Subtype.ext h
    · intro q hq
      simp only [L, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨⟨q, hq.2⟩, by simp [pairsIn, hq.1], rfl⟩
  have hLG : L.card = G.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [L, Finset.mem_filter, Finset.mem_product] at hp
      simp only [G, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      cases p₁; cases p₂
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      simp only [G, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨(q.2, q.1), by simp [L, hq.1.1, hq.1.2, hq.2], by simp⟩
  have hDs : D.card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [D, Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
      exact Prod.ext h (hp₁.2.symm.trans (h.trans hp₂.2))
    · intro x hx
      exact ⟨(x, x), by simp [D, hx], rfl⟩
  have hdisj1 : Disjoint L G := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, Finset.mem_filter] at hp1 hp2
    exact lt_asymm hp1.2 hp2.2
  have hdisj2 : Disjoint (L ∪ G) D := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with h1 | h1
    · exact ne_of_lt h1.2 hp2.2
    · exact ne_of_gt h1.2 hp2.2
  have hunion : (L ∪ G) ∪ D = s ×ˢ s := by
    ext ⟨u, v⟩
    simp only [L, G, D, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · intro h
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨h, hlt⟩)
      · exact Or.inr ⟨h, heq⟩
      · exact Or.inl (Or.inr ⟨h, hgt⟩)
  have htotal : 2 * (pairsIn s).card + s.card = s.card * s.card := by
    have hc : ((L ∪ G) ∪ D).card = (s ×ˢ s).card := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_product, ← hLG, ← hPL, hDs] at hc
    omega
  cases hk : s.card with
  | zero =>
    rw [hk] at htotal
    omega
  | succ m =>
    rw [hk] at htotal
    have hmul : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
    rw [hmul] at htotal
    have h2 : 2 * (pairsIn s).card = (m + 1) * m := by omega
    simp only [Nat.add_sub_cancel]
    omega

private def monoGraphs {n : ℕ} (s : Finset (Fin n)) (b : Bool) : Finset (Pair n → Bool) :=
  Finset.univ.filter (fun c => ∀ p ∈ pairsIn s, c p = b)

private lemma monoGraphs_card_mul {n : ℕ} (s : Finset (Fin n)) (b : Bool) :
    (monoGraphs s b).card * 2 ^ (pairsIn s).card ≤ 2 ^ Fintype.card (Pair n) := by
  let res : (Pair n → Bool) → ({p : Pair n // p ∉ pairsIn s} → Bool) :=
    fun c p => c p.1
  have hinj : Set.InjOn res (monoGraphs s b) := by
    intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_coe, monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    funext p
    by_cases hp : p ∈ pairsIn s
    · rw [hc₁ p hp, hc₂ p hp]
    · exact congrFun heq ⟨p, hp⟩
  have hle : (monoGraphs s b).card ≤ Fintype.card ({p : Pair n // p ∉ pairsIn s} → Bool) := by
    have h := Finset.card_le_card_of_injOn res (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ] using h
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe] at hle
  have hsub : (pairsIn s).card ≤ Fintype.card (Pair n) := Finset.card_le_univ (pairsIn s)
  have hmul := Nat.mul_le_mul_right (2 ^ (pairsIn s).card) hle
  rwa [← pow_add, Nat.sub_add_cancel hsub] at hmul

private lemma exists_ramsey_counterexample {n k : ℕ}
    (hlt : 2 * n.choose k < 2 ^ (k * (k - 1) / 2)) :
    ∃ C : SimpleGraph (Fin n),
      ¬ (completeGraph (Fin k)).IsContained C ∧ ¬ (completeGraph (Fin k)).IsContained Cᶜ := by
  let Bad : Finset (Pair n → Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion
      (fun s => monoGraphs s true ∪ monoGraphs s false)
  have hbad_mul : Bad.card * 2 ^ (k * (k - 1) / 2) ≤
      (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
    have h1 : Bad.card ≤
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          (monoGraphs s true ∪ monoGraphs s false).card :=
      Finset.card_biUnion_le
    calc Bad.card * 2 ^ (k * (k - 1) / 2)
        ≤ (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card) * 2 ^ (k * (k - 1) / 2) :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (k * (k - 1) / 2) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            (2 * 2 ^ Fintype.card (Pair n)) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
          have hpcard : (pairsIn s).card = k * (k - 1) / 2 := by
            rw [pairsIn_card, hscard]
          rw [← hpcard]
          have hu := Finset.card_union_le (monoGraphs s true) (monoGraphs s false)
          calc (monoGraphs s true ∪ monoGraphs s false).card * 2 ^ (pairsIn s).card
              ≤ ((monoGraphs s true).card + (monoGraphs s false).card) * 2 ^ (pairsIn s).card :=
                Nat.mul_le_mul_right _ hu
            _ = (monoGraphs s true).card * 2 ^ (pairsIn s).card +
                (monoGraphs s false).card * 2 ^ (pairsIn s).card :=
                Nat.add_mul _ _ _
            _ ≤ 2 ^ Fintype.card (Pair n) + 2 ^ Fintype.card (Pair n) :=
                Nat.add_le_add (monoGraphs_card_mul s true) (monoGraphs_card_mul s false)
            _ = 2 * 2 ^ Fintype.card (Pair n) := by ring
      _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card *
            (2 * 2 ^ Fintype.card (Pair n)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * n.choose k) * 2 ^ Fintype.card (Pair n) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          ring
  have hbad_lt_mul : Bad.card * 2 ^ (k * (k - 1) / 2) <
      2 ^ (k * (k - 1) / 2) * 2 ^ Fintype.card (Pair n) :=
    lt_of_le_of_lt hbad_mul (Nat.mul_lt_mul_of_pos_right hlt (by positivity))
  have hbad_lt : Bad.card < (Finset.univ : Finset (Pair n → Bool)).card := by
    have hlt' : Bad.card < 2 ^ Fintype.card (Pair n) := by
      rw [mul_comm (2 ^ (k * (k - 1) / 2))] at hbad_lt_mul
      exact Nat.lt_of_mul_lt_mul_right hbad_lt_mul
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] using hlt'
  have hex : ∃ c : Pair n → Bool, c ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Pair n → Bool)) ⊆ Bad := fun c _ => hall c
    exact not_le_of_gt hbad_lt (Finset.card_le_card hsub)
  obtain ⟨c, hc⟩ := hex
  refine ⟨toGraph c, ?_, ?_⟩
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s true := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c).Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_left _ hc_mono⟩)
  · intro hf
    rcases (hf : Nonempty _) with ⟨f⟩
    let s : Finset (Fin n) := Finset.univ.image f
    have hscard : s.card = k := by
      dsimp only [s]
      rw [← SimpleGraph.Copy.coe_toHom, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    have hs_mem : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hscard⟩
    have hc_mono : c ∈ monoGraphs s false := by
      simp only [monoGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp
      simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp.1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp.2
      have hij : i ≠ j := by
        intro h
        subst h
        exact ne_of_lt p.2 (hi.symm.trans hj)
      have hadj : (toGraph c)ᶜ.Adj p.1.1 p.1.2 := by
        rw [← hi, ← hj]
        exact f.toHom.map_rel' hij
      exact (toGraph_compl_adj_of_lt c p.2).mp hadj
    exact hc (Finset.mem_biUnion.mpr ⟨s, hs_mem, Finset.mem_union_right _ hc_mono⟩)


private lemma four_pow_le_factorial (k : ℕ) (hk : 9 ≤ k) : 4 ^ k ≤ k.factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ, Nat.factorial_succ, mul_comm (k + 1)]
    exact Nat.mul_le_mul ih (by omega)

/-- Keeping the factorial in the binomial coefficient allows us to use
    twice the *floor* of the binary logarithm as the forbidden clique size. -/
private lemma ramsey_threshold (n t : ℕ) (ht : 5 ≤ t) (hn : n ≤ 2 ^ (t + 1)) :
    2 * n.choose (2 * t) < 2 ^ ((2 * t) * (2 * t - 1) / 2) := by
  let k := 2 * t
  change 2 * n.choose k < 2 ^ (k * (k - 1) / 2)
  have hk : 9 ≤ k := by dsimp [k]; omega
  have hchoose : 4 ^ k * n.choose k ≤ n ^ k := calc
    _ ≤ k.factorial * n.choose k := Nat.mul_le_mul_right _ (four_pow_le_factorial k hk)
    _ = n.descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose n k).symm
    _ ≤ _ := Nat.descFactorial_le_pow n k
  have hexp : 1 + (t + 1) * k < 2 * k + k * (k - 1) / 2 := by
    have h : k * (k - 1) / 2 = t * (2*t - 1) := by
      rw [show k = 2*t by rfl, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [h]
    have hsub : 2*t - 1 + 1 = 2*t := by omega
    have hmul := congrArg (t * ·) hsub
    dsimp [k] at *
    nlinarith
  apply Nat.lt_of_mul_lt_mul_left (a := 4 ^ k)
  calc
    4 ^ k * (2 * n.choose k) = 2 * (4 ^ k * n.choose k) := by ring
    _ ≤ 2 * n ^ k := Nat.mul_le_mul_left _ hchoose
    _ ≤ 2 * (2 ^ (t + 1)) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    _ = 2 ^ (1 + (t + 1) * k) := by
      rw [pow_add 2 1 ((t + 1) * k), pow_one, pow_mul 2 (t + 1) k]
    _ < 2 ^ (2 * k + k * (k - 1) / 2) := Nat.pow_lt_pow_right (by decide) hexp
    _ = 4 ^ k * 2 ^ (k * (k - 1) / 2) := by rw [pow_add, pow_mul]; norm_num

private lemma clique_le_of_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (h : ¬ (completeGraph (Fin k)).IsContained G) : G.cliqueNum ≤ k := by
  by_contra! hlt
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hfree : G.CliqueFree k := by
    by_contra hf
    exact h ((G.not_cliqueFree_iff_top_isContained k).1 hf)
  exact hs.not_cliqueFree (CliqueFree.mono hlt.le hfree)

private lemma ratio_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (G : SimpleGraph (Fin n)) (hc : G.cliqueNum ≤ k) (hi : G.indepNum ≤ k) :
    (n : ℝ) / (k : ℝ) ^ 2 ≤ Erdos627.maxChromaticCliqueRatio n := by
  classical
  have one_le (H : SimpleGraph (Fin n)) : 1 ≤ H.cliqueNum := by
    let v : Fin n := ⟨0, hn⟩
    have h : H.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
    simpa using h.card_le_cliqueNum
  have hpω : 0 < (G.cliqueNum : ℝ) := by exact_mod_cast one_le G
  have hα : 0 < G.indepNum := (by decide : 0 < 1).trans_le (by simpa using one_le Gᶜ)
  have hχ : G.chromaticNumber ≠ ⊤ :=
    chromaticNumber_ne_top_iff_exists.mpr ⟨_, G.colorable_of_fintype⟩
  have hcolor := card_div_indepNum_le_chromaticNumber (G := G)
  rw [← ENat.natCast_toNat hχ] at hcolor
  have hceil : ⌈((n : ℚ≥0) / G.indepNum)⌉₊ ≤ G.chromaticNumber.toNat := by
    simpa [Nat.card_eq_fintype_card] using hcolor
  have hnn := (div_le_iff₀ (show 0 < (G.indepNum : ℚ≥0) by exact_mod_cast hα)).mp
    (Nat.ceil_le.mp hceil)
  have hnc : n ≤ G.chromaticNumber.toNat * G.indepNum := by exact_mod_cast hnn
  have hnk : (n : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) * k := by
    exact_mod_cast hnc.trans (Nat.mul_le_mul_left _ hi)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : (n : ℝ) / (k : ℝ)^2 ≤ (G.chromaticNumber.toNat : ℝ) / G.cliqueNum := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hk') hpω]
    calc
      (n : ℝ) * G.cliqueNum ≤ (n : ℝ) * k := by gcongr
      _ ≤ ((G.chromaticNumber.toNat : ℝ) * k) * k := by gcongr
      _ = _ := by ring
  exact le_ciSup_of_le (Set.finite_range _).bddAbove G hratio

end Erdos627Lower

private theorem erdos627_lower_estimate :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (1 / 4 - ε) * ((n : ℝ) / Real.logb 2 n ^ 2) ≤ Erdos627.maxChromaticCliqueRatio n := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 32] with n hn
  let t := Nat.log 2 n
  have ht : 5 ≤ t := (Nat.le_log_iff_pow_le (by decide) (by omega)).2 (by simpa using hn)
  have htt := Erdos627Lower.ramsey_threshold n t ht (Nat.lt_pow_succ_log_self (by decide) n).le
  obtain ⟨G, hG, hG'⟩ := Erdos627Lower.exists_ramsey_counterexample htt
  have hc := Erdos627Lower.clique_le_of_free G hG
  have hi : G.indepNum ≤ 2 * t := by
    simpa using Erdos627Lower.clique_le_of_free Gᶜ hG'
  have hmax := Erdos627Lower.ratio_bound (by omega) (by omega) G hc hi
  have htl : (t : ℝ) ≤ Real.logb 2 n := by simpa [t, Nat.log2_eq_log_two] using Real.log2_le_logb n
  have ht' : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hL := ht'.trans_le htl
  calc
    _ ≤ (1 / 4 : ℝ) * ((n : ℝ) / Real.logb 2 n ^ 2) := by gcongr; linarith
    _ = (n : ℝ) / (2 * Real.logb 2 n) ^ 2 := by ring
    _ ≤ (n : ℝ) / ((2 * t : ℕ) : ℝ) ^ 2 := by
      push_cast
      gcongr
    _ ≤ _ := hmax

namespace OMA.E627

theorem choose_le_exp_sqrt (a b : ℕ) :
    ((a + b).choose a : ℝ) ≤ Real.exp (2 * Real.sqrt ((a : ℝ) * b)) := by
  obtain rfl | ha := Nat.eq_zero_or_pos a
  · simp
  obtain rfl | hb := Nat.eq_zero_or_pos b
  · simp
  let x := Real.sqrt (a : ℝ)
  let y := Real.sqrt (b : ℝ)
  have hx : 0 < x := Real.sqrt_pos.2 (by exact_mod_cast ha)
  have hy : 0 < y := Real.sqrt_pos.2 (by exact_mod_cast hb)
  have hx2 : x^2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hy2 : y^2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have hterm : x^a * y^b * ((a+b).choose a : ℝ) ≤ (x+y)^(a+b) := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (f := fun i : ℕ => x^i * y^(a+b-i) * ((a+b).choose i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (show a < a+b+1 by omega))
    simpa using h
  have expand (u v : ℝ) (hu : 0 < u) : u + v ≤ u * Real.exp (v/u) := by
    calc u + v = u * (v/u + 1) := by field_simp; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hu.le
  have hsum : (a : ℝ)*(y/x) + (b : ℝ)*(x/y) = 2 * Real.sqrt ((a : ℝ)*b) := by
    rw [Real.sqrt_mul (by positivity)]
    change (a : ℝ)*(y/x) + (b : ℝ)*(x/y) = 2 * (x*y)
    calc (a : ℝ)*(y/x) + (b : ℝ)*(x/y) = x^2*(y/x) + y^2*(x/y) := by rw [hx2, hy2]
         _ = _ := by field_simp; ring
  refine le_of_mul_le_mul_left (a := x^a * y^b) ?_ (by positivity)
  calc x^a * y^b * ((a+b).choose a : ℝ) ≤ (x+y)^(a+b) := hterm
       _ = (x+y)^a * (x+y)^b := pow_add _ _ _
       _ ≤ (x * Real.exp (y/x))^a * (y * Real.exp (x/y))^b := by
         gcongr
         · exact expand x y hx
         · rw [add_comm]
           exact expand y x hy
       _ = x^a * y^b * (Real.exp (y/x)^a * Real.exp (x/y)^b) := by rw [mul_pow, mul_pow]; ring
       _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, hsum]

end OMA.E627

lemma greedyColor627 {n m t : ℕ} (G : SimpleGraph (Fin n)) (ht : 1 ≤ t)
    (hlarge : ∀ S : Finset (Fin n), m ≤ S.card →
      ∃ T : Finset (Fin n), T ⊆ S ∧ t ≤ T.card ∧ G.IsIndepSet (T : Set (Fin n))) :
    G.chromaticNumber.toNat ≤ n / t + m := by
  classical
  let rec color (S : Finset (Fin n)) :
      (G.induce (S : Set (Fin n))).Colorable (S.card / t + m) := by
    by_cases hS : m ≤ S.card
    · obtain ⟨T, hTS, htT, hI⟩ := hlarge S hS
      let R := S \ T
      have hRT : R.card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
      have hlt : R.card < S.card := by omega
      obtain ⟨c⟩ := color R
      let f (x : (S : Set (Fin n))) : Fin ((R.card / t + m) + 1) :=
        if hx : x.val ∈ T then Fin.last _ else
          (c ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩).castSucc
      have hdiv : R.card / t + 1 ≤ S.card / t := by
        apply (Nat.le_div_iff_mul_le ht).mpr
        rw [Nat.add_mul, Nat.one_mul]
        have := Nat.div_mul_le_self R.card t
        omega
      apply Colorable.mono (show R.card / t + m + 1 ≤ S.card / t + m by omega)
      refine ⟨Coloring.mk f ?_⟩
      intro x y hxy
      have hxy' : G.Adj x.val y.val := hxy
      by_cases hx : x.val ∈ T <;> by_cases hy : y.val ∈ T
      · exact ((hI hx hy hxy'.ne) hxy').elim
      · simp only [f, dif_pos hx, dif_neg hy]
        exact (Fin.castSucc_ne_last _).symm
      · simp [f, hx, hy, Fin.castSucc_ne_last]
      · simp only [f, dif_neg hx, dif_neg hy]
        apply (Fin.castSucc_injective _).ne
        exact c.valid (show (G.induce (R : Set (Fin n))).Adj
          ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩
          ⟨y.val, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩ from hxy')
    · apply Colorable.mono _ (G.induce (S : Set (Fin n))).colorable_of_fintype
      simpa using (Nat.le_of_lt (Nat.lt_of_not_ge hS)).trans (Nat.le_add_left m (S.card / t))
  termination_by S.card
  let U : Finset (Fin n) := Finset.univ
  let inclusion : G →g G.induce (U : Set (Fin n)) :=
    { toFun := fun x => ⟨x, Finset.mem_univ x⟩, map_rel' := fun h => h }
  have h := (color U).of_hom inclusion
  apply ENat.toNat_le_of_le_natCast
  simpa [U] using h.chromaticNumber_le

namespace Erdos627Upper

open Combinatorics.Diagonal

private theorem ramsey_choose_succ (s t : ℕ) :
    HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero =>
    rw [Nat.choose_zero_right]
    exact hasRamseyProperty_one_left (t + 1)
  | succ s ihs =>
    induction t with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self]
      exact hasRamseyProperty_one_right (s + 2)
    | succ t iht =>
      have hs : HasRamseyProperty ((s + (t + 1)).choose s) (s + 1) (t + 2) := ihs (t + 1)
      have hpos : 1 ≤ (s + (t + 1)).choose s := Nat.choose_pos (by omega)
      have hp : ((s + 1) + (t + 1)).choose (s + 1) =
          (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega, Nat.choose_succ_succ]
        rw [show s + (t + 1) = (s + 1) + t by omega]
      rw [hp]
      intro m c V hV
      exact HasRamseyProperty.step hs iht hpos c V hV

theorem indep_of_exp_le
    (binomialBound : ∀ a b : ℕ, ((a + b).choose a : ℝ) ≤
      Real.exp (2 * Real.sqrt ((a : ℝ) * b)))
    {n s t : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hclique : G.cliqueNum ≤ s)
    (hcard : Real.exp (2 * Real.sqrt ((s : ℝ) * t)) ≤ S.card) :
    ∃ T ⊆ S, T.card = t + 1 ∧ G.IsIndepSet (T : Set (Fin n)) := by
  classical
  have hn : (s + t).choose s ≤ S.card := by exact_mod_cast (binomialBound s t).trans hcard
  let c (e : Finset (Fin n)) : Bool := decide (¬ G.IsClique (e : Set (Fin n)))
  obtain ⟨T, _, hT, hmono⟩ | ⟨T, hTS, hT, hmono⟩ := ramsey_choose_succ s t c S hn
  · have hTc : G.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using h
    have hle := hTc.card_le_cliqueNum
    omega
  · refine ⟨T, hTS, hT, ?_⟩
    intro x hx y hy hxy
    have h := hmono {x, y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (by simp [hxy])
    simpa [c, SimpleGraph.isClique_pair, hxy] using h

end Erdos627Upper

namespace Erdos627Upper

/-- Eventually the cost of coloring the final square-root-sized remainder is negligible. -/
lemma log_sq_eventually_le_sqrt : ∀ᶠ n : ℕ in atTop,
    (Real.log n)^2 ≤ Real.sqrt n := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 (s := (1/2 : ℝ)) (by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with n hn
  change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ 1 * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ at hn
  rw [Real.rpow_two, ← Real.sqrt_eq_rpow, one_mul, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hn
  exact hn

/-- Use the Ramsey threshold at sqrt(n), then divide the number of colors by the clique size. -/
lemma ratio_of_threshold {n w colors : ℕ} (hn : 2 ≤ n) (hw : 0 < w)
    (hlog : (Real.log n)^2 ≤ Real.sqrt n)
    (hc : ∀ t m : ℕ, Real.exp (2 * Real.sqrt ((w : ℝ) * t)) ≤ m →
      colors ≤ n / (t + 1) + m) :
    (colors : ℝ) / w ≤ 18 * ((n : ℝ) / (Real.log n)^2) := by
  let L := Real.log n
  let u := L^2 / (16 * w)
  let t := ⌊u⌋₊
  let m := ⌈Real.sqrt n⌉₊
  have hn' : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hL : 0 < L := Real.log_pos hn'
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hwt : (w : ℝ) * t ≤ L^2 / 16 := by
    have h := (le_div_iff₀ (show 0 < 16 * (w : ℝ) by positivity)).mp (Nat.floor_le hu)
    dsimp [t, u] at *
    linarith only [h]
  have htroot : Real.sqrt ((w : ℝ) * t) ≤ L / 4 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hwt]⟩
  have hm : Real.exp (2 * Real.sqrt ((w : ℝ) * t)) ≤ m := calc
    _ ≤ Real.exp (L/2) := Real.exp_le_exp.mpr (by linarith only [htroot])
    _ = Real.sqrt n := by
      rw [← Real.log_sqrt (Nat.cast_nonneg n), Real.exp_log (Real.sqrt_pos.mpr (by positivity))]
    _ ≤ _ := Nat.le_ceil _
  have hcap := hc t m hm
  have hcolor : (colors : ℝ) ≤ (n : ℝ) / (t + 1) + m := by
    calc
      _ ≤ ((n / (t + 1) + m : ℕ) : ℝ) := by exact_mod_cast hcap
      _ ≤ _ := by push_cast; gcongr; exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := n) (n := t + 1))
  have hunit : L^2 ≤ 16 * w * ((t : ℝ) + 1) := by
    have h := (div_lt_iff₀ (show 0 < (16 : ℝ) * w by positivity)).mp (Nat.lt_floor_add_one u)
    dsimp [t, u] at *
    linarith only [h]
  have htpos : 0 < (t : ℝ) + 1 := by positivity
  have hmain : ((n : ℝ) / ((t : ℝ) + 1)) * L^2 ≤ 16 * n * w := by
    rw [div_mul_eq_mul_div, div_le_iff₀ htpos]
    calc
      _ ≤ (n : ℝ) * (16 * w * ((t : ℝ) + 1)) := by gcongr
      _ = _ := by ring
  have hnsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hs1 : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'.le
  have hm2 : (m : ℝ) ≤ 2 * Real.sqrt n := by
    have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))
    dsimp [m]
    linarith
  have htail : (m : ℝ) * L^2 ≤ 2 * n * w := calc
    _ ≤ (2 * Real.sqrt n) * Real.sqrt n :=
      mul_le_mul hm2 hlog (sq_nonneg _) (by positivity)
    _ = 2 * n := by nlinarith only [hnsq]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hw1
  have hscaled := mul_le_mul_of_nonneg_right hcolor (sq_nonneg L)
  change (colors : ℝ) / w ≤ 18 * ((n : ℝ) / L^2)
  rw [div_le_iff₀ hw', ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hL)]
  linarith only [hscaled, hmain, htail]

end Erdos627Upper

private lemma erdos627_upper :
    (fun n : ℕ => Erdos627.maxChromaticCliqueRatio n) =O[atTop]
      fun n : ℕ => (n : ℝ) / Real.logb 2 n ^ 2 := by
  classical
  refine Asymptotics.isBigO_iff.mpr ⟨18 / (Real.log 2)^2, ?_⟩
  filter_upwards [eventually_ge_atTop 2, Erdos627Upper.log_sq_eventually_le_sqrt] with n hn hlog
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hbase := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hsup : Erdos627.maxChromaticCliqueRatio n ≤ 18 * ((n : ℝ) / (Real.log n)^2) := by
    apply ciSup_le
    intro G
    have hw : 0 < G.cliqueNum := by
      let v : Fin n := ⟨0, by omega⟩
      have hv : G.IsClique (({v} : Finset (Fin n)) : Set (Fin n)) := by simp
      change 1 ≤ G.cliqueNum
      simpa using hv.card_le_cliqueNum
    apply Erdos627Upper.ratio_of_threshold hn hw hlog
    intro t m hm
    apply greedyColor627 G (by omega : 1 ≤ t + 1)
    intro S hs
    obtain ⟨I, hI, hcard, hind⟩ :=
      Erdos627Upper.indep_of_exp_le OMA.E627.choose_le_exp_sqrt G S le_rfl
        (hm.trans (by exact_mod_cast hs))
    exact ⟨I, hI, hcard.ge, hind⟩
  have hpos : 0 ≤ Erdos627.maxChromaticCliqueRatio n := by
    apply le_ciSup_of_le (Set.finite_range _).bddAbove (⊥ : SimpleGraph (Fin n))
    positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg (div_nonneg hn'.le (sq_nonneg _))]
  calc
    _ ≤ _ := hsup
    _ = _ := by rw [Real.logb]; field_simp

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.theta := by
  refine ⟨erdos627_upper, Asymptotics.isBigO_iff.mpr ⟨8, ?_⟩⟩
  filter_upwards [erdos627_lower_estimate (1 / 8) (by norm_num)] with n hn
  have hx : 0 ≤ (n : ℝ) / Real.logb 2 n ^ 2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hy : 0 ≤ Erdos627.maxChromaticCliqueRatio n := (mul_nonneg (by norm_num) hx).trans hn
  simp only [Real.norm_of_nonneg hx, Real.norm_of_nonneg hy]
  linarith only [hn]
