import FormalConjectures.ErdosProblems.«1037»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Sym.Sym2

/-!
# Cambie-Chan-Hunter construction for Erdos Problem 1037

Proves `Erdos1037.erdos_1037.variants.cambie_chan_hunter` via a finite counting
argument for sparse Ramsey graphs and the Cambie-Chan-Hunter degree-shifting
construction.
-/

open Filter Finset

namespace Erdos1037Proof

private abbrev Edge (M : ℕ) := {e : Sym2 (Fin M) // ¬ e.IsDiag}

private abbrev Sample (M : ℕ) := Edge M → Fin 8

private def graphOf {M : ℕ} (ω : Sample M) : SimpleGraph (Fin M) where
  Adj u v := ∃ h : u ≠ v, ω ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩ = 0
  symm := ⟨fun u v ⟨h, hω⟩ => ⟨h.symm, by simpa only [Sym2.eq_swap] using hω⟩⟩
  loopless := ⟨fun u ⟨h, _⟩ => h rfl⟩

private instance {M : ℕ} (ω : Sample M) : DecidableRel (graphOf ω).Adj :=
  fun u v => inferInstanceAs (Decidable (∃ h : u ≠ v, ω ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩ = 0))

private def incEdges (M : ℕ) (v : Fin M) : Finset (Edge M) :=
  Finset.univ.filter (fun e => v ∈ e.1)

private lemma incEdges_card (M : ℕ) (v : Fin M) : (incEdges M v).card = M - 1 := by
  have hbij : (Finset.univ.erase v).card = (incEdges M v).card := by
    refine Finset.card_bij (fun u hu => ⟨s(v, u), by
      have huv : u ≠ v := (Finset.mem_erase.mp hu).1
      simpa [Sym2.mk_isDiag_iff] using huv.symm⟩) ?_ ?_ ?_
    · intro u _
      simp [incEdges]
    · intro u₁ hu₁ u₂ hu₂ h
      have h2ne : u₂ ≠ v := (Finset.mem_erase.mp hu₂).1
      have heq : s(v, u₁) = s(v, u₂) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · exact absurd h2.symm h2ne
    · intro e he
      have hv : v ∈ e.1 := (Finset.mem_filter.mp he).2
      rcases hv with ⟨u, hu⟩
      refine ⟨u, Finset.mem_erase.mpr ⟨fun huv => e.2 ?_, Finset.mem_univ u⟩, ?_⟩
      · rw [hu, huv]
        exact Sym2.mk_isDiag_iff.mpr rfl
      · ext1
        exact hu.symm
  rw [← hbij, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_fin]

private lemma degree_graphOf {M : ℕ} (ω : Sample M) (v : Fin M) :
    (graphOf ω).degree v = ∑ e ∈ incEdges M v, if ω e = 0 then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.sum_boole, Nat.cast_id]
  refine Finset.card_bij (fun u hu => ⟨s(v, u), by
    have hadj : (graphOf ω).Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    simpa [Sym2.mk_isDiag_iff] using hadj.1⟩) ?_ ?_ ?_
  · intro u hu
    have hadj : (graphOf ω).Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    rw [Finset.mem_filter]
    refine ⟨?_, hadj.2⟩
    simp [incEdges]
  · intro u₁ _ u₂ hu₂ h
    have hadj₂ : (graphOf ω).Adj v u₂ := (SimpleGraph.mem_neighborFinset _ _ _).mp hu₂
    have heq : s(v, u₁) = s(v, u₂) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd h1 hadj₂.1
  · intro e he
    rw [Finset.mem_filter] at he
    have hv : v ∈ e.1 := (Finset.mem_filter.mp he.1).2
    rcases hv with ⟨u, hu⟩
    have huv : v ≠ u := fun h => e.2 (by rw [hu, h]; exact Sym2.mk_isDiag_iff.mpr rfl)
    refine ⟨u, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      refine ⟨huv, ?_⟩
      convert he.2 using 2
      ext1
      exact hu.symm
    · ext1
      exact hu.symm

private lemma sum_two_pow_degree (M : ℕ) (v : Fin M) :
    ∑ ω : Sample M, (2 : ℝ) ^ ((graphOf ω).degree v) =
      (9 : ℝ) ^ (M - 1) * (8 : ℝ) ^ (Fintype.card (Edge M) - (M - 1)) := by
  have hterm : ∀ ω : Sample M, (2 : ℝ) ^ ((graphOf ω).degree v) =
      ∏ e : Edge M, (if v ∈ e.1 then (if ω e = 0 then (2 : ℝ) else 1) else 1) := by
    intro ω
    rw [degree_graphOf]
    have hprod : ∏ e : Edge M, (if v ∈ e.1 then (if ω e = 0 then (2 : ℝ) else 1) else 1) =
        ∏ e ∈ incEdges M v, (if ω e = 0 then (2 : ℝ) else 1) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : Edge M => v ∈ e.1)]
      have h1 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => v ∈ e.1),
          (if v ∈ e.1 then (if ω e = 0 then (2 : ℝ) else 1) else 1) =
          ∏ e ∈ incEdges M v, (if ω e = 0 then (2 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun e he => ?_
        rw [if_pos (Finset.mem_filter.mp he).2]
      have h2 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => ¬ v ∈ e.1),
          (if v ∈ e.1 then (if ω e = 0 then (2 : ℝ) else 1) else 1) = 1 := by
        refine Finset.prod_eq_one fun e he => ?_
        rw [if_neg (Finset.mem_filter.mp he).2]
      rw [h1, h2, mul_one]
    rw [hprod]
    have hpow : ∏ e ∈ incEdges M v, (if ω e = 0 then (2 : ℝ) else 1) =
        ∏ e ∈ incEdges M v, (2 : ℝ) ^ (if ω e = 0 then 1 else 0) := by
      refine Finset.prod_congr rfl fun e _ => ?_
      split_ifs <;> norm_num
    rw [hpow, Finset.prod_pow_eq_pow_sum]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (e : Edge M) (c : Fin 8) =>
    if v ∈ e.1 then (if c = 0 then (2 : ℝ) else 1) else 1)]
  have hinner : ∀ e : Edge M,
      (∑ c : Fin 8, if v ∈ e.1 then (if c = 0 then (2 : ℝ) else 1) else 1) =
        if v ∈ e.1 then (9 : ℝ) else 8 := by
    intro e
    split_ifs
    · simp [Fin.sum_univ_eight]; norm_num
    · simp
  simp_rw [hinner]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : Edge M => v ∈ e.1)]
  have h1 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => v ∈ e.1),
      (if v ∈ e.1 then (9 : ℝ) else 8) = (9 : ℝ) ^ (M - 1) := by
    rw [Finset.prod_congr rfl (fun e he => if_pos (Finset.mem_filter.mp he).2)]
    rw [Finset.prod_const, ← incEdges, incEdges_card]
  have h2 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => ¬ v ∈ e.1),
      (if v ∈ e.1 then (9 : ℝ) else 8) = (8 : ℝ) ^ (Fintype.card (Edge M) - (M - 1)) := by
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.mp he).2)]
    rw [Finset.prod_const]
    congr 1
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Edge M))) (fun e => v ∈ e.1)
    rw [Finset.card_univ] at hsum
    change (incEdges M v).card + _ = _ at hsum
    rw [incEdges_card] at hsum
    omega
  rw [h1, h2]

private def cliqueEdges {M : ℕ} (S : Finset (Fin M)) : Finset (Edge M) :=
  Finset.univ.filter (fun e => ∀ x ∈ e.1, x ∈ S)

private lemma cliqueEdges_card {M : ℕ} (S : Finset (Fin M)) :
    (cliqueEdges S).card = S.card * (S.card - 1) / 2 := by
  have hhalf : (S.offDiag.filter (fun p => p.1 < p.2)).card = S.card * (S.card - 1) / 2 := by
    have hswap : (S.offDiag.filter (fun p => p.1 < p.2)).card =
        (S.offDiag.filter (fun p => p.2 < p.1)).card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
        exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        ext <;> simp_all
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_offDiag] at hp
        refine ⟨(p.2, p.1), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
    have hunion : (S.offDiag.filter (fun p => p.1 < p.2)).card +
        (S.offDiag.filter (fun p => p.2 < p.1)).card = S.offDiag.card := by
      have hdisj : Disjoint (S.offDiag.filter (fun p => p.1 < p.2))
          (S.offDiag.filter (fun p => p.2 < p.1)) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [Finset.mem_filter] at hp1 hp2
        exact lt_asymm hp1.2 hp2.2
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
        · exact Or.inl ⟨h, hlt⟩
        · exact absurd heq h.2.2
        · exact Or.inr ⟨h, hgt⟩
    rw [← hswap, Finset.offDiag_card, ← Nat.mul_sub_one] at hunion
    omega
  rw [← hhalf]
  symm
  refine Finset.card_bij (fun p hp => ⟨s(p.1, p.2), by
    rw [Finset.mem_filter, Finset.mem_offDiag] at hp
    simpa [Sym2.mk_isDiag_iff] using hp.1.2.2⟩) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_offDiag] at hp
    rw [cliqueEdges, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hp.1.1
    · exact hp.1.2.1
  · intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_filter] at hp₁ hp₂
    have heq : s(p₁.1, p₁.2) = s(p₂.1, p₂.2) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · have hlt : p₁.1 < p₁.1 := by
        calc p₁.1 < p₁.2 := hp₁.2
          _ = p₂.1 := h2
          _ < p₂.2 := hp₂.2
          _ = p₁.1 := h1.symm
      exact absurd hlt (lt_irrefl _)
  · intro e he
    rw [cliqueEdges, Finset.mem_filter] at he
    rcases e with ⟨e, he_diag⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he_diag
      have hu : u ∈ S := he.2 u (Sym2.mem_iff.mpr (Or.inl rfl))
      have hv : v ∈ S := he.2 v (Sym2.mem_iff.mpr (Or.inr rfl))
      rcases lt_or_gt_of_ne huv with hlt | hgt
      · refine ⟨(u, v), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨hu, hv, huv⟩, hlt⟩
      · refine ⟨(v, u), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_offDiag]
          exact ⟨⟨hv, hu, huv.symm⟩, hgt⟩
        · ext1
          exact Sym2.eq_swap

private lemma card_sample_eq (M : ℕ) :
    (Fintype.card (Sample M) : ℝ) = (8 : ℝ) ^ (Fintype.card (Edge M)) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rfl

private lemma count_clique_samples {M : ℕ} (S : Finset (Fin M)) :
    ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e = 0)).card : ℝ) ≤
      (7 / 8 : ℝ) ^ (cliqueEdges S).card * (Fintype.card (Sample M) : ℝ) := by
  have hcount : ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e = 0)).card : ℝ) =
      (8 : ℝ) ^ (Fintype.card (Edge M) - (cliqueEdges S).card) := by
    have hsum : ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e = 0)).card : ℝ) =
        ∑ ω : Sample M, ∏ e : Edge M, (if e ∈ cliqueEdges S then (if ω e = 0 then (1 : ℝ) else 0) else 1) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      split_ifs with h
      · refine (Finset.prod_eq_one fun e _ => ?_).symm
        by_cases he : e ∈ cliqueEdges S
        · simp [he, h e he]
        · simp [he]
      · push Not at h
        rcases h with ⟨e, he, hne⟩
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
        simp [he, hne]
    rw [hsum, ← Fintype.prod_sum (fun (e : Edge M) (c : Fin 8) =>
      if e ∈ cliqueEdges S then (if c = 0 then (1 : ℝ) else 0) else 1)]
    have hinner : ∀ e : Edge M,
        (∑ c : Fin 8, if e ∈ cliqueEdges S then (if c = 0 then (1 : ℝ) else 0) else 1) =
          if e ∈ cliqueEdges S then (1 : ℝ) else 8 := by
      intro e
      split_ifs <;> simp
    simp_rw [hinner]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : Edge M => e ∈ cliqueEdges S)]
    have h1 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => e ∈ cliqueEdges S),
        (if e ∈ cliqueEdges S then (1 : ℝ) else 8) = 1 :=
      Finset.prod_eq_one fun e he => by rw [if_pos (Finset.mem_filter.mp he).2]
    have h2 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => e ∉ cliqueEdges S),
        (if e ∈ cliqueEdges S then (1 : ℝ) else 8) =
        (8 : ℝ) ^ (Fintype.card (Edge M) - (cliqueEdges S).card) := by
      rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.mp he).2), Finset.prod_const]
      congr 1
      have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Edge M))) (fun e => e ∈ cliqueEdges S)
      rw [Finset.card_univ, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
      omega
    rw [h1, h2, one_mul]
  rw [hcount, card_sample_eq]
  have hle : (cliqueEdges S).card ≤ Fintype.card (Edge M) := by
    simpa [Finset.card_univ] using Finset.card_le_univ (cliqueEdges S)
  have h8 : (8 : ℝ) ^ (Fintype.card (Edge M) - (cliqueEdges S).card) =
      (1 / 8 : ℝ) ^ (cliqueEdges S).card * (8 : ℝ) ^ (Fintype.card (Edge M)) := by
    rw [one_div, inv_pow, ← div_eq_inv_mul, eq_div_iff (by positivity)]
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h8]
  gcongr
  norm_num

private lemma count_indep_samples {M : ℕ} (S : Finset (Fin M)) :
    ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e ≠ 0)).card : ℝ) ≤
      (7 / 8 : ℝ) ^ (cliqueEdges S).card * (Fintype.card (Sample M) : ℝ) := by
  have hcount : ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e ≠ 0)).card : ℝ) =
      (7 : ℝ) ^ (cliqueEdges S).card * (8 : ℝ) ^ (Fintype.card (Edge M) - (cliqueEdges S).card) := by
    have hsum : ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e ≠ 0)).card : ℝ) =
        ∑ ω : Sample M, ∏ e : Edge M, (if e ∈ cliqueEdges S then (if ω e ≠ 0 then (1 : ℝ) else 0) else 1) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      split_ifs with h
      · refine (Finset.prod_eq_one fun e _ => ?_).symm
        by_cases he : e ∈ cliqueEdges S
        · simp [he, h e he]
        · simp [he]
      · push Not at h
        rcases h with ⟨e, he, heq⟩
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
        simp [he, heq]
    rw [hsum, ← Fintype.prod_sum (fun (e : Edge M) (c : Fin 8) =>
      if e ∈ cliqueEdges S then (if c ≠ 0 then (1 : ℝ) else 0) else 1)]
    have hinner : ∀ e : Edge M,
        (∑ c : Fin 8, if e ∈ cliqueEdges S then (if c ≠ 0 then (1 : ℝ) else 0) else 1) =
          if e ∈ cliqueEdges S then (7 : ℝ) else 8 := by
      intro e
      split_ifs
      · simp [Fin.sum_univ_eight]; norm_num
      · simp
    simp_rw [hinner]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : Edge M => e ∈ cliqueEdges S)]
    have h1 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => e ∈ cliqueEdges S),
        (if e ∈ cliqueEdges S then (7 : ℝ) else 8) = (7 : ℝ) ^ (cliqueEdges S).card := by
      rw [Finset.prod_congr rfl (fun e he => if_pos (Finset.mem_filter.mp he).2), Finset.prod_const]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∏ e ∈ Finset.univ.filter (fun e : Edge M => e ∉ cliqueEdges S),
        (if e ∈ cliqueEdges S then (7 : ℝ) else 8) =
        (8 : ℝ) ^ (Fintype.card (Edge M) - (cliqueEdges S).card) := by
      rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.mp he).2), Finset.prod_const]
      congr 1
      have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Edge M))) (fun e => e ∈ cliqueEdges S)
      rw [Finset.card_univ, Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
      omega
    rw [h1, h2]
  rw [hcount, card_sample_eq]
  have hle : (cliqueEdges S).card ≤ Fintype.card (Edge M) := by
    simpa [Finset.card_univ] using Finset.card_le_univ (cliqueEdges S)
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

private lemma badDeg_bound (M : ℕ) :
    ((Finset.univ.filter (fun ω : Sample M => ∃ v : Fin M, M ≤ 5 * (graphOf ω).degree v)).card : ℝ) ≤
      (M : ℝ) * ((9 / 8 : ℝ) ^ (M - 1) / (2 : ℝ) ^ ((M : ℝ) / 5)) * (Fintype.card (Sample M) : ℝ) := by
  have hsub : Finset.univ.filter (fun ω : Sample M => ∃ v : Fin M, M ≤ 5 * (graphOf ω).degree v) ⊆
      Finset.univ.biUnion (fun v : Fin M => Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rcases hω.2 with ⟨v, hv⟩
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hv⟩⟩
  calc ((Finset.univ.filter (fun ω : Sample M => ∃ v : Fin M, M ≤ 5 * (graphOf ω).degree v)).card : ℝ)
      ≤ ((Finset.univ.biUnion (fun v : Fin M => Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v))).card : ℝ) := by
        gcongr
    _ ≤ ∑ v : Fin M, ((Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin M, ((9 / 8 : ℝ) ^ (M - 1) / (2 : ℝ) ^ ((M : ℝ) / 5)) * (Fintype.card (Sample M) : ℝ) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hmarkov : ((Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v)).card : ℝ) *
            (2 : ℝ) ^ ((M : ℝ) / 5) ≤ (9 : ℝ) ^ (M - 1) * (8 : ℝ) ^ (Fintype.card (Edge M) - (M - 1)) := by
          calc ((Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v)).card : ℝ) *
                (2 : ℝ) ^ ((M : ℝ) / 5)
              = ∑ _ω ∈ Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v), (2 : ℝ) ^ ((M : ℝ) / 5) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Sample M => M ≤ 5 * (graphOf ω).degree v),
                (2 : ℝ) ^ ((graphOf ω).degree v) := by
                refine Finset.sum_le_sum fun ω hω => ?_
                have hdeg : (M : ℝ) / 5 ≤ ((graphOf ω).degree v : ℝ) := by
                  have hnat : M ≤ 5 * (graphOf ω).degree v := (Finset.mem_filter.mp hω).2
                  have : (M : ℝ) ≤ 5 * ((graphOf ω).degree v : ℝ) := by exact_mod_cast hnat
                  linarith
                rw [← Real.rpow_natCast (2 : ℝ) ((graphOf ω).degree v)]
                exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hdeg
            _ ≤ ∑ ω : Sample M, (2 : ℝ) ^ ((graphOf ω).degree v) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
            _ = (9 : ℝ) ^ (M - 1) * (8 : ℝ) ^ (Fintype.card (Edge M) - (M - 1)) := sum_two_pow_degree M v
        have hle : M - 1 ≤ Fintype.card (Edge M) := by
          rw [← incEdges_card M v]
          simpa [Finset.card_univ] using Finset.card_le_univ (incEdges M v)
        have h98 : (9 : ℝ) ^ (M - 1) * (8 : ℝ) ^ (Fintype.card (Edge M) - (M - 1)) =
            (9 / 8 : ℝ) ^ (M - 1) * (Fintype.card (Sample M) : ℝ) := by
          rw [card_sample_eq, div_pow, div_mul_eq_mul_div, eq_div_iff (by positivity)]
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
        rw [h98] at hmarkov
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith [hmarkov]
    _ = (M : ℝ) * ((9 / 8 : ℝ) ^ (M - 1) / (2 : ℝ) ^ ((M : ℝ) / 5)) * (Fintype.card (Sample M) : ℝ) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_assoc]

private lemma eventually_deg_prob_lt :
    ∀ᶠ M : ℕ in atTop,
      (M : ℝ) * ((9 / 8 : ℝ) ^ (M - 1) / (2 : ℝ) ^ ((M : ℝ) / 5)) < 1 / 3 := by
  let r : ℝ := (9 / 8 : ℝ) / (2 : ℝ) ^ (1 / 5 : ℝ)
  have hr_pos : 0 < r := by positivity
  have hr_lt : r < 1 := by
    have hr5 : r ^ 5 < 1 := by
      rw [div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) (by simpa using hr5)
  let δ : ℝ := r⁻¹ - 1
  have hδ_pos : 0 < δ := sub_pos.mpr (one_lt_inv₀ hr_pos |>.mpr hr_lt)
  have hr_inv : 1 + δ = r⁻¹ := by simp [δ]
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 / (δ ^ 2 * (3 / 8)) + 2))] with M hM
  have hM2 : 2 ≤ M := by
    have hpos : 0 < 2 / (δ ^ 2 * (3 / 8)) + 2 := by positivity
    have : (2 : ℝ) ≤ M := by
      calc (2 : ℝ) ≤ 2 / (δ ^ 2 * (3 / 8)) + 2 := by linarith [show 0 ≤ 2 / (δ ^ 2 * (3 / 8)) by positivity]
        _ ≤ Nat.ceil (2 / (δ ^ 2 * (3 / 8)) + 2) := Nat.le_ceil _
        _ ≤ M := by exact_mod_cast hM
    exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hM_sub : 2 / (δ ^ 2 * (3 / 8)) < (M : ℝ) - 1 := by
    have : 2 / (δ ^ 2 * (3 / 8)) + 2 ≤ M := by
      calc 2 / (δ ^ 2 * (3 / 8)) + 2 ≤ Nat.ceil (2 / (δ ^ 2 * (3 / 8)) + 2) := Nat.le_ceil _
        _ ≤ M := by exact_mod_cast hM
    linarith
  have hbin : (M * (M - 1) / 2 : ℝ) * δ ^ 2 ≤ (1 + δ) ^ M := by
    have hchoose : δ ^ 2 * 1 ^ (M - 2) * (Nat.choose M 2 : ℝ) ≤ (δ + 1) ^ M := by
      rw [add_pow]
      exact Finset.single_le_sum (f := fun k => δ ^ k * 1 ^ (M - k) * (Nat.choose M k : ℝ))
        (fun k _ => by positivity) (Finset.mem_range.mpr (by omega))
    rw [add_comm δ 1] at hchoose
    simp only [one_pow, mul_one] at hchoose
    have hch2 : (Nat.choose M 2 : ℝ) = (M : ℝ) * ((M : ℝ) - 1) / 2 := by
      rw [Nat.choose_two_right]
      have hdvd : 2 ∣ M * (M - 1) := Nat.even_mul_pred_self M |>.two_dvd
      rw [Nat.cast_div hdvd (by norm_num)]
      push_cast [show 1 ≤ M by omega]
      ring
    linarith [hch2 ▸ hchoose]
  have hrM : (M : ℝ) * r ^ M < 3 / 8 := by
    have h1 : r ^ M = ((1 + δ) ^ M)⁻¹ := by rw [hr_inv, inv_pow, inv_inv]
    have hpos : 0 < (1 + δ) ^ M := by positivity
    rw [h1, ← div_eq_mul_inv, div_lt_iff₀ hpos]
    have h2 : (M : ℝ) < (3 / 8) * ((M * (M - 1) / 2 : ℝ) * δ ^ 2) := by
      have hM0 : (0 : ℝ) < M := by positivity
      have : 1 < (3 / 8) * (((M : ℝ) - 1) / 2 * δ ^ 2) := by
        calc 1 = (3 / 8) * ((2 / (δ ^ 2 * (3 / 8))) / 2 * δ ^ 2) := by field_simp
          _ < (3 / 8) * (((M : ℝ) - 1) / 2 * δ ^ 2) := by gcongr
      nlinarith
    calc (M : ℝ) < (3 / 8) * ((M * (M - 1) / 2 : ℝ) * δ ^ 2) := h2
      _ ≤ (3 / 8) * (1 + δ) ^ M := by gcongr
  have hrewrite : (9 / 8 : ℝ) ^ (M - 1) / (2 : ℝ) ^ ((M : ℝ) / 5) = (8 / 9 : ℝ) * r ^ M := by
    have hpow : (9 / 8 : ℝ) ^ (M - 1) = (8 / 9 : ℝ) * (9 / 8 : ℝ) ^ M := by
      have : M = (M - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ']
      ring
    have h2pow : (2 : ℝ) ^ ((M : ℝ) / 5) = ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ M := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 5 : ℝ)) M, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    dsimp only [r]
    rw [hpow, h2pow]
    simp only [div_eq_mul_inv, mul_pow, inv_pow]
    ring
  rw [hrewrite]
  calc (M : ℝ) * ((8 / 9 : ℝ) * r ^ M) = (8 / 9 : ℝ) * ((M : ℝ) * r ^ M) := by ring
    _ < (8 / 9 : ℝ) * (3 / 8) := by gcongr
    _ = 1 / 3 := by norm_num

private lemma ramsey_prob_lt (M : ℕ) (hM : 3 ≤ M) :
    let k := Nat.ceil (30 * Real.log M)
    (M : ℝ) ^ k * (7 / 8 : ℝ) ^ (k * (k - 1) / 2) < 1 / 3 := by
  intro k
  have hlog1 : 1 < Real.log (M : ℝ) := by
    have h3 : (Real.exp 1 : ℝ) < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hM3 : (Real.exp 1 : ℝ) < M := lt_of_lt_of_le h3 (by exact_mod_cast hM)
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hM3
  have hk_ge : 30 * Real.log (M : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hk30 : (30 : ℝ) ≤ (k : ℝ) := by linarith
  have hk_nat : 30 ≤ k := by exact_mod_cast hk30
  have h78 : (7 / 8 : ℝ) ≤ Real.exp (-1 / 8) := by
    linarith [Real.add_one_le_exp (-1 / 8 : ℝ)]
  have hchoose : ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    have hdvd : 2 ∣ k * (k - 1) := Nat.even_mul_pred_self k |>.two_dvd
    rw [Nat.cast_div hdvd (by norm_num)]
    push_cast [show 1 ≤ k by omega]
    ring
  have hM_eq : (M : ℝ) = Real.exp (Real.log M) := (Real.exp_log (by positivity)).symm
  calc (M : ℝ) ^ k * (7 / 8 : ℝ) ^ (k * (k - 1) / 2)
      ≤ (Real.exp (Real.log M)) ^ k * (Real.exp (-1 / 8)) ^ (k * (k - 1) / 2) := by
        rw [← hM_eq]
        gcongr
    _ = Real.exp ((k : ℝ) * Real.log M) * Real.exp (-1 / 8 * ((k * (k - 1) / 2 : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 2
        ring
    _ = Real.exp ((k : ℝ) * (Real.log M - ((k : ℝ) - 1) / 16)) := by
        rw [← Real.exp_add, hchoose]
        congr 1
        ring
    _ ≤ Real.exp (-2) := by
        rw [Real.exp_le_exp]
        have hdiff : Real.log (M : ℝ) - ((k : ℝ) - 1) / 16 ≤ -13 / 16 := by linarith
        nlinarith
    _ < 1 / 3 := by
        rw [Real.exp_neg]
        have h2 : (3 : ℝ) < Real.exp 2 := by
          have : (1 + 2 + 2 ^ 2 / 2 : ℝ) ≤ Real.exp 2 := by
            have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 3
            simpa [Finset.sum_range_succ, Nat.factorial] using this
          linarith
        exact inv_lt_of_inv_lt₀ (by norm_num) (by linarith)

private lemma exists_sparse_ramsey_graph :
    ∀ᶠ M : ℕ in atTop, ∃ H : SimpleGraph (Fin M), ∃ _ : DecidableRel H.Adj,
      (∀ v : Fin M, 5 * H.degree v < M) ∧
      (∀ s : Set (Fin M), H.IsClique s → s.ncard < Nat.ceil (30 * Real.log M)) ∧
      (∀ s : Set (Fin M), H.IsIndepSet s → s.ncard < Nat.ceil (30 * Real.log M)) := by
  filter_upwards [eventually_deg_prob_lt, Filter.eventually_ge_atTop 3] with M hdeg hM3
  let k := Nat.ceil (30 * Real.log M)
  let badDeg := Finset.univ.filter (fun ω : Sample M => ∃ v : Fin M, M ≤ 5 * (graphOf ω).degree v)
  let badClique := (Finset.univ.powersetCard k).biUnion
    (fun S => Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e = 0))
  let badIndep := (Finset.univ.powersetCard k).biUnion
    (fun S => Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e ≠ 0))
  have hbadC : (badClique.card : ℝ) < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by
    calc (badClique.card : ℝ)
        ≤ ∑ S ∈ Finset.univ.powersetCard k,
            ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e = 0)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Finset.univ.powersetCard k,
            (7 / 8 : ℝ) ^ (k * (k - 1) / 2) * (Fintype.card (Sample M) : ℝ) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
          have hce : (cliqueEdges S).card = k * (k - 1) / 2 := by rw [cliqueEdges_card, hScard]
          simpa [hce] using count_clique_samples S
      _ = ((Nat.choose M k : ℝ) * (7 / 8 : ℝ) ^ (k * (k - 1) / 2)) * (Fintype.card (Sample M) : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ ≤ ((M : ℝ) ^ k * (7 / 8 : ℝ) ^ (k * (k - 1) / 2)) * (Fintype.card (Sample M) : ℝ) := by
          gcongr
          exact_mod_cast Nat.choose_le_pow M k
      _ < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by
          have hΩpos : (0 : ℝ) < Fintype.card (Sample M) := by positivity
          exact mul_lt_mul_of_pos_right (ramsey_prob_lt M hM3) hΩpos
  have hbadI : (badIndep.card : ℝ) < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by
    calc (badIndep.card : ℝ)
        ≤ ∑ S ∈ Finset.univ.powersetCard k,
            ((Finset.univ.filter (fun ω : Sample M => ∀ e ∈ cliqueEdges S, ω e ≠ 0)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Finset.univ.powersetCard k,
            (7 / 8 : ℝ) ^ (k * (k - 1) / 2) * (Fintype.card (Sample M) : ℝ) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
          have hce : (cliqueEdges S).card = k * (k - 1) / 2 := by rw [cliqueEdges_card, hScard]
          simpa [hce] using count_indep_samples S
      _ = ((Nat.choose M k : ℝ) * (7 / 8 : ℝ) ^ (k * (k - 1) / 2)) * (Fintype.card (Sample M) : ℝ) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ ≤ ((M : ℝ) ^ k * (7 / 8 : ℝ) ^ (k * (k - 1) / 2)) * (Fintype.card (Sample M) : ℝ) := by
          gcongr
          exact_mod_cast Nat.choose_le_pow M k
      _ < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by
          have hΩpos : (0 : ℝ) < Fintype.card (Sample M) := by positivity
          exact mul_lt_mul_of_pos_right (ramsey_prob_lt M hM3) hΩpos
  have hbadD : (badDeg.card : ℝ) < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by
    have hΩpos : (0 : ℝ) < Fintype.card (Sample M) := by positivity
    exact lt_of_le_of_lt (badDeg_bound M) (mul_lt_mul_of_pos_right hdeg hΩpos)
  have hunion : (badDeg ∪ badClique ∪ badIndep).card < Fintype.card (Sample M) := by
    have hreal : ((badDeg ∪ badClique ∪ badIndep).card : ℝ) < (Fintype.card (Sample M) : ℝ) := by
      calc ((badDeg ∪ badClique ∪ badIndep).card : ℝ)
          ≤ (badDeg.card : ℝ) + (badClique.card : ℝ) + (badIndep.card : ℝ) := by
            have h1 : (badDeg ∪ badClique ∪ badIndep).card ≤ badDeg.card + badClique.card + badIndep.card := by
              calc (badDeg ∪ badClique ∪ badIndep).card
                  ≤ (badDeg ∪ badClique).card + badIndep.card := Finset.card_union_le _ _
                _ ≤ badDeg.card + badClique.card + badIndep.card := by gcongr; exact Finset.card_union_le _ _
            exact_mod_cast h1
        _ < (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) +
            (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) +
            (1 / 3 : ℝ) * (Fintype.card (Sample M) : ℝ) := by linarith
        _ = (Fintype.card (Sample M) : ℝ) := by ring
    exact_mod_cast hreal
  have hne : (Finset.univ \ (badDeg ∪ badClique ∪ badIndep)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have hcard : (Finset.univ \ (badDeg ∪ badClique ∪ badIndep)).card = 0 := by rw [h, Finset.card_empty]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hcard
    omega
  rcases hne with ⟨ω, hω⟩
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hω
  have hnotD : ω ∉ badDeg := fun h => hω.2 (Or.inl (Or.inl h))
  have hnotC : ω ∉ badClique := fun h => hω.2 (Or.inl (Or.inr h))
  have hnotI : ω ∉ badIndep := fun h => hω.2 (Or.inr h)
  refine ⟨graphOf ω, inferInstance, ?_, ?_, ?_⟩
  · intro v
    by_contra hle
    push Not at hle
    exact hnotD (Finset.mem_filter.mpr ⟨Finset.mem_univ ω, ⟨v, hle⟩⟩)
  · intro s hs
    by_contra hle
    push Not at hle
    classical
    have hfin : (Finset.univ.filter (· ∈ s)).card ≥ k := by
      have hcard : (Finset.univ.filter (· ∈ s)).card = s.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext x
        simp
      omega
    rcases Finset.exists_subset_card_eq hfin with ⟨S, hSs, hScard⟩
    apply hnotC
    dsimp only [badClique]
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, fun e he => ?_⟩⟩
    rcases e with ⟨e, he_diag⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huS : u ∈ S := (Finset.mem_filter.mp he).2 u (Sym2.mem_iff.mpr (Or.inl rfl))
      have hvS : v ∈ S := (Finset.mem_filter.mp he).2 v (Sym2.mem_iff.mpr (Or.inr rfl))
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he_diag
      have hus : u ∈ s := (Finset.mem_filter.mp (hSs huS)).2
      have hvs : v ∈ s := (Finset.mem_filter.mp (hSs hvS)).2
      exact (hs hus hvs huv).2
  · intro s hs
    by_contra hle
    push Not at hle
    classical
    have hfin : (Finset.univ.filter (· ∈ s)).card ≥ k := by
      have hcard : (Finset.univ.filter (· ∈ s)).card = s.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext x
        simp
      omega
    rcases Finset.exists_subset_card_eq hfin with ⟨S, hSs, hScard⟩
    apply hnotI
    dsimp only [badIndep]
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, fun e he h0 => ?_⟩⟩
    rcases e with ⟨e, he_diag⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huS : u ∈ S := (Finset.mem_filter.mp he).2 u (Sym2.mem_iff.mpr (Or.inl rfl))
      have hvS : v ∈ S := (Finset.mem_filter.mp he).2 v (Sym2.mem_iff.mpr (Or.inr rfl))
      have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using he_diag
      have hus : u ∈ s := (Finset.mem_filter.mp (hSs huS)).2
      have hvs : v ∈ s := (Finset.mem_filter.mp (hSs hvS)).2
      exact hs hus hvs huv ⟨huv, h0⟩

private lemma degree_compl_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] (v : V) :
    Gᶜ.degree v + G.degree v = Fintype.card V - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (Gᶜ.neighborFinset v) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rw [SimpleGraph.mem_neighborFinset] at hu1 hu2
    exact hu1.2 hu2
  rw [← Finset.card_union_of_disjoint hdisj]
  have hunion : Gᶜ.neighborFinset v ∪ G.neighborFinset v = Finset.univ.erase v := by
    ext u
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h.symm
      · exact (G.ne_of_adj h).symm
    · intro h
      by_cases hadj : G.Adj v u
      · exact Or.inr hadj
      · exact Or.inl ⟨h.symm, hadj⟩
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

private lemma degree_comap_perm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (v : V) :
    (G.comap σ).degree v = G.degree (σ v) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun u _ => σ u) ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  · intro u₁ _ u₂ _ h
    exact σ.injective h
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
    rw [SimpleGraph.mem_neighborFinset]
    simpa using hw

private lemma degree_comap_le {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {ι : U → V} (hι : Function.Injective ι) (u : U) :
    (G.comap ι).degree u ≤ G.degree (ι u) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn ι ?_ ?_
  · intro x hx
    simpa only [Finset.mem_coe, SimpleGraph.mem_neighborFinset, SimpleGraph.comap_adj] using hx
  · intro x _ y _ h
    exact hι h

private lemma ncard_neighborSet_comap_equiv {U V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : U ≃ V) (u : U) :
    ((G.comap e).neighborSet u).ncard = G.degree (e u) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
  refine Set.ncard_congr (fun x _ => e x) ?_ ?_ ?_
  · intro x hx; exact hx
  · intro x _ y _ h; exact e.injective h
  · intro y hy; exact ⟨e.symm y, by simpa using hy, e.apply_symm_apply y⟩

private def Gsum {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M)) :
    SimpleGraph (Fin m ⊕ Fin M) where
  Adj u v := match u, v with
    | Sum.inl i₁, Sum.inl i₂ => HA.Adj i₁ i₂
    | Sum.inr j₁, Sum.inr j₂ => HB.Adj j₁ j₂
    | Sum.inl i, Sum.inr j => m ≤ i.1 + j.1 + (if M = m then 1 else 0)
    | Sum.inr j, Sum.inl i => m ≤ i.1 + j.1 + (if M = m then 1 else 0)
  symm := ⟨fun u v h => by
    cases u <;> cases v
    · exact HA.adj_comm _ _ |>.mp h
    · exact h
    · exact h
    · exact HB.adj_comm _ _ |>.mp h⟩
  loopless := ⟨fun u h => by
    cases u
    · exact HA.loopless.irrefl _ h
    · exact HB.loopless.irrefl _ h⟩

private lemma Gsum_adj_inl_inl {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    (i₁ i₂ : Fin m) : (Gsum HA HB).Adj (Sum.inl i₁) (Sum.inl i₂) ↔ HA.Adj i₁ i₂ := Iff.rfl

private lemma Gsum_adj_inr_inr {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    (j₁ j₂ : Fin M) : (Gsum HA HB).Adj (Sum.inr j₁) (Sum.inr j₂) ↔ HB.Adj j₁ j₂ := Iff.rfl

private lemma Gsum_adj_inl_inr {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    (i : Fin m) (j : Fin M) :
    (Gsum HA HB).Adj (Sum.inl i) (Sum.inr j) ↔ m ≤ i.1 + j.1 + (if M = m then 1 else 0) := Iff.rfl

private lemma Gsum_adj_inr_inl {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    (j : Fin M) (i : Fin m) :
    (Gsum HA HB).Adj (Sum.inr j) (Sum.inl i) ↔ m ≤ i.1 + j.1 + (if M = m then 1 else 0) := Iff.rfl

private instance {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] : DecidableRel (Gsum HA HB).Adj :=
  fun u v => match u, v with
    | Sum.inl i₁, Sum.inl i₂ => inferInstanceAs (Decidable (HA.Adj i₁ i₂))
    | Sum.inr j₁, Sum.inr j₂ => inferInstanceAs (Decidable (HB.Adj j₁ j₂))
    | Sum.inl i, Sum.inr j => inferInstanceAs (Decidable (m ≤ i.1 + j.1 + (if M = m then 1 else 0)))
    | Sum.inr j, Sum.inl i => inferInstanceAs (Decidable (m ≤ i.1 + j.1 + (if M = m then 1 else 0)))

private lemma Gsum_degree_inl {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (hM : M = m ∨ M = m + 1) (i : Fin m) :
    (Gsum HA HB).degree (Sum.inl i) = HA.degree i + i.1 + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  let A : Finset (Fin m ⊕ Fin M) := (HA.neighborFinset i).image Sum.inl
  let B : Finset (Fin m ⊕ Fin M) :=
    (Finset.univ.filter (fun j : Fin M => m ≤ i.1 + j.1 + (if M = m then 1 else 0))).image Sum.inr
  have hunion : (Gsum HA HB).neighborFinset (Sum.inl i) = A ∪ B := by
    ext v
    cases v with
    | inl i₂ =>
      simp [A, B, SimpleGraph.mem_neighborFinset, Gsum_adj_inl_inl]
    | inr j =>
      simp [A, B, SimpleGraph.mem_neighborFinset, Gsum_adj_inl_inr]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [A, B, Finset.mem_image] at hv1 hv2
    rcases hv1 with ⟨_, _, rfl⟩
    rcases hv2 with ⟨_, _, h⟩
    cases h
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hA : A.card = (HA.neighborFinset i).card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have hB : B.card = i.1 + 1 := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    have hbij : (Finset.univ.filter (fun j : Fin M => m ≤ i.1 + j.1 + (if M = m then 1 else 0))).card =
        (Finset.Ico (M - 1 - i.1) M).card := by
      refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_Ico]
        refine ⟨?_, j.2⟩
        rcases hM with rfl | rfl <;> simp_all <;> omega
      · intro j₁ _ j₂ _ h
        exact Fin.ext h
      · intro k hk
        rw [Finset.mem_Ico] at hk
        refine ⟨⟨k, hk.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        rcases hM with rfl | rfl <;> simp_all <;> omega
    rw [hbij, Nat.card_Ico]
    omega
  rw [hA, hB]
  omega

private lemma Gsum_degree_inr {m M : ℕ} (HA : SimpleGraph (Fin m)) (HB : SimpleGraph (Fin M))
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (hM : M = m ∨ M = m + 1) (j : Fin M) :
    (Gsum HA HB).degree (Sum.inr j) = HB.degree j + (if M = m then j.1 + 1 else j.1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  let A : Finset (Fin m ⊕ Fin M) :=
    (Finset.univ.filter (fun i : Fin m => m ≤ i.1 + j.1 + (if M = m then 1 else 0))).image Sum.inl
  let B : Finset (Fin m ⊕ Fin M) := (HB.neighborFinset j).image Sum.inr
  have hunion : (Gsum HA HB).neighborFinset (Sum.inr j) = A ∪ B := by
    ext v
    cases v with
    | inl i =>
      simp [A, B, SimpleGraph.mem_neighborFinset, Gsum_adj_inr_inl]
    | inr j₂ =>
      simp [A, B, SimpleGraph.mem_neighborFinset, Gsum_adj_inr_inr]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [A, B, Finset.mem_image] at hv1 hv2
    rcases hv1 with ⟨_, _, rfl⟩
    rcases hv2 with ⟨_, _, h⟩
    cases h
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hB : B.card = (HB.neighborFinset j).card :=
    Finset.card_image_of_injective _ Sum.inr_injective
  have hA : A.card = if M = m then j.1 + 1 else j.1 := by
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    have hbij : (Finset.univ.filter (fun i : Fin m => m ≤ i.1 + j.1 + (if M = m then 1 else 0))).card =
        (Finset.Ico (m - (if M = m then j.1 + 1 else j.1)) m).card := by
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_Ico]
        refine ⟨?_, i.2⟩
        rcases hM with rfl | rfl
        · simp at hi ⊢; omega
        · simp at hi ⊢; omega
      · intro i₁ _ i₂ _ h
        exact Fin.ext h
      · intro k hk
        rw [Finset.mem_Ico] at hk
        refine ⟨⟨k, hk.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        rcases hM with rfl | rfl
        · simp at hk ⊢; omega
        · simp at hk ⊢; omega
    rw [hbij, Nat.card_Ico]
    rcases hM with rfl | rfl
    · simp; omega
    · simp; omega
  rw [hA, hB]
  omega

end Erdos1037Proof

theorem OMA.solution : type_of% @Erdos1037.erdos_1037.variants.cambie_chan_hunter := by
  refine ⟨70, ?_⟩
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp Erdos1037Proof.exists_sparse_ramsey_graph
  filter_upwards [Filter.eventually_ge_atTop (2 * M₀ + 100)] with n hn
  let m := n / 2
  let M := n - m
  have hmM : m + M = n := by omega
  have hM_cases : M = m ∨ M = m + 1 := by omega
  have hM_ge : M₀ ≤ M := by omega
  have hM50 : 50 ≤ M := by omega
  have hm50 : 50 ≤ m := by omega
  obtain ⟨H, instH, hHdeg, hHclique, hHindep⟩ := hM₀ M hM_ge
  let _ := instH
  let ι : Fin m → Fin M := fun i => ⟨i.1, by omega⟩
  have hι : Function.Injective ι := fun i₁ i₂ h => Fin.ext (congrArg (Fin.val : Fin M → ℕ) h)
  let HA : SimpleGraph (Fin m) := H.comap ι
  let HB : SimpleGraph (Fin M) := Hᶜ
  let σA : Equiv.Perm (Fin m) := Tuple.sort (fun i : Fin m => HA.degree i)
  let σB : Equiv.Perm (Fin M) := Tuple.sort (fun j : Fin M => HB.degree j)
  let HA' : SimpleGraph (Fin m) := HA.comap σA
  let HB' : SimpleGraph (Fin M) := HB.comap σB
  let G0 : SimpleGraph (Fin m ⊕ Fin M) := Erdos1037Proof.Gsum HA' HB'
  let e : Fin n ≃ Fin m ⊕ Fin M :=
    (Equiv.cast (congrArg Fin hmM.symm)).trans finSumFinEquiv.symm
  let G : SimpleGraph (Fin n) := G0.comap e
  have hdeg_eq : ∀ v : Fin n, ((G0.comap e).neighborSet v).ncard = G0.degree (e v) :=
    fun v => Erdos1037Proof.ncard_neighborSet_comap_equiv G0 e v
  have hmonoA : Monotone (fun i => HA'.degree i) := by
    intro i₁ i₂ hle
    simp only [HA']
    rw [Erdos1037Proof.degree_comap_perm, Erdos1037Proof.degree_comap_perm]
    exact Tuple.monotone_sort (fun i : Fin m => HA.degree i) hle
  have hmonoB : Monotone (fun j => HB'.degree j) := by
    intro j₁ j₂ hle
    simp only [HB']
    rw [Erdos1037Proof.degree_comap_perm, Erdos1037Proof.degree_comap_perm]
    exact Tuple.monotone_sort (fun j : Fin M => HB.degree j) hle
  have hinjA : Function.Injective (fun i : Fin m => G0.degree (Sum.inl i)) := by
    intro i₁ i₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := Erdos1037Proof.Gsum_degree_inl HA' HB' hM_cases i₁
      have h2 := Erdos1037Proof.Gsum_degree_inl HA' HB' hM_cases i₂
      have hm := hmonoA (le_of_lt hlt)
      dsimp only at heq hm
      rw [h1, h2] at heq
      have hlt' : i₁.1 < i₂.1 := hlt
      omega
    · have h1 := Erdos1037Proof.Gsum_degree_inl HA' HB' hM_cases i₁
      have h2 := Erdos1037Proof.Gsum_degree_inl HA' HB' hM_cases i₂
      have hm := hmonoA (le_of_lt hlt)
      dsimp only at heq hm
      rw [h1, h2] at heq
      have hlt' : i₂.1 < i₁.1 := hlt
      omega
  have hinjB : Function.Injective (fun j : Fin M => G0.degree (Sum.inr j)) := by
    intro j₁ j₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := Erdos1037Proof.Gsum_degree_inr HA' HB' hM_cases j₁
      have h2 := Erdos1037Proof.Gsum_degree_inr HA' HB' hM_cases j₂
      have hm := hmonoB (le_of_lt hlt)
      dsimp only at heq hm
      rw [h1, h2] at heq
      have hlt' : j₁.1 < j₂.1 := hlt
      rcases hM_cases with hMm | hMm
      · simp [hMm] at heq; omega
      · have hne_m : M ≠ m := by omega
        simp [hne_m] at heq; omega
    · have h1 := Erdos1037Proof.Gsum_degree_inr HA' HB' hM_cases j₁
      have h2 := Erdos1037Proof.Gsum_degree_inr HA' HB' hM_cases j₂
      have hm := hmonoB (le_of_lt hlt)
      dsimp only at heq hm
      rw [h1, h2] at heq
      have hlt' : j₂.1 < j₁.1 := hlt
      rcases hM_cases with hMm | hMm
      · simp [hMm] at heq; omega
      · have hne_m : M ≠ m := by omega
        simp [hne_m] at heq; omega
  refine ⟨G, ?_, ?_, ?_⟩
  · intro d
    have hsub : {v : Fin n | (G.neighborSet v).ncard = d} ⊆
        (e.symm ∘ Sum.inl) '' {i : Fin m | G0.degree (Sum.inl i) = d} ∪
        (e.symm ∘ Sum.inr) '' {j : Fin M | G0.degree (Sum.inr j) = d} := by
      intro v hv
      change (G.neighborSet v).ncard = d at hv
      rw [hdeg_eq v] at hv
      cases h : e v with
      | inl i =>
        left
        refine ⟨i, ?_, ?_⟩
        · rw [Set.mem_ofPred_eq]; rw [h] at hv; exact hv
        · simp [← h]
      | inr j =>
        right
        refine ⟨j, ?_, ?_⟩
        · rw [Set.mem_ofPred_eq]; rw [h] at hv; exact hv
        · simp [← h]
    have hcardA : ((e.symm ∘ Sum.inl) '' {i : Fin m | G0.degree (Sum.inl i) = d}).ncard ≤ 1 := by
      rw [Set.ncard_image_of_injective _ (e.symm.injective.comp Sum.inl_injective)]
      have hsubA : ({i : Fin m | G0.degree (Sum.inl i) = d} : Set (Fin m)).Subsingleton :=
        fun i₁ h1 i₂ h2 => hinjA (h1.trans h2.symm)
      rcases hsubA.eq_empty_or_singleton with h | ⟨x, h⟩ <;> simp [h]
    have hcardB : ((e.symm ∘ Sum.inr) '' {j : Fin M | G0.degree (Sum.inr j) = d}).ncard ≤ 1 := by
      rw [Set.ncard_image_of_injective _ (e.symm.injective.comp Sum.inr_injective)]
      have hsubB : ({j : Fin M | G0.degree (Sum.inr j) = d} : Set (Fin M)).Subsingleton :=
        fun j₁ h1 j₂ h2 => hinjB (h1.trans h2.symm)
      rcases hsubB.eq_empty_or_singleton with h | ⟨x, h⟩ <;> simp [h]
    calc {v : Fin n | (G.neighborSet v).ncard = d}.ncard
        ≤ ((e.symm ∘ Sum.inl) '' {i : Fin m | G0.degree (Sum.inl i) = d} ∪
           (e.symm ∘ Sum.inr) '' {j : Fin M | G0.degree (Sum.inr j) = d}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ((e.symm ∘ Sum.inl) '' {i : Fin m | G0.degree (Sum.inl i) = d}).ncard +
          ((e.symm ∘ Sum.inr) '' {j : Fin M | G0.degree (Sum.inr j) = d}).ncard :=
          Set.ncard_union_le _ _
      _ ≤ 1 + 1 := add_le_add hcardA hcardB
      _ = 2 := rfl
  · have hdegA_ub : ∀ i : Fin m, G0.degree (Sum.inl i) ≤ (M - 1) / 5 + m := by
      intro i
      rw [Erdos1037Proof.Gsum_degree_inl HA' HB' hM_cases i]
      have h1 : HA'.degree i = HA.degree (σA i) := Erdos1037Proof.degree_comap_perm HA σA i
      have h2 : HA.degree (σA i) ≤ H.degree (ι (σA i)) := Erdos1037Proof.degree_comap_le H hι (σA i)
      have h3 : 5 * H.degree (ι (σA i)) < M := hHdeg (ι (σA i))
      have hi : i.1 < m := i.2
      omega
    have hdegB_lb : ∀ j : Fin M, 9 * M / 20 + 2 ≤ j.1 → (M - 1) / 5 + m < G0.degree (Sum.inr j) := by
      intro j hj
      rw [Erdos1037Proof.Gsum_degree_inr HA' HB' hM_cases j]
      have h1 : HB'.degree j = HB.degree (σB j) := Erdos1037Proof.degree_comap_perm HB σB j
      have h2 : HB.degree (σB j) + H.degree (σB j) = M - 1 := by
        simpa [HB] using Erdos1037Proof.degree_compl_add H (σB j)
      have h3 : 5 * H.degree (σB j) < M := hHdeg (σB j)
      rw [h1]
      rcases hM_cases with hMm | hMm
      · simp [hMm]; omega
      · have hne : M ≠ m := by omega
        simp [hne]; omega
    let S₁ : Set ℕ := Set.range (fun i : Fin m => G0.degree (Sum.inl i))
    let S₂ : Set ℕ := (fun j : Fin M => G0.degree (Sum.inr j)) '' {j : Fin M | 9 * M / 20 + 2 ≤ j.1}
    have hdisj : Disjoint S₁ S₂ := by
      rw [Set.disjoint_left]
      rintro d ⟨i, rfl⟩ ⟨j, hj, heq⟩
      have h1 := hdegA_ub i
      have h2 := hdegB_lb j hj
      dsimp only at heq
      omega
    have hsub : S₁ ∪ S₂ ⊆ Set.range (fun v : Fin n => (G.neighborSet v).ncard) := by
      rintro d (⟨i, rfl⟩ | ⟨j, _, rfl⟩)
      · refine ⟨e.symm (Sum.inl i), ?_⟩
        dsimp only
        change ((G0.comap e).neighborSet (e.symm (Sum.inl i))).ncard = G0.degree (Sum.inl i)
        rw [hdeg_eq, e.apply_symm_apply]
      · refine ⟨e.symm (Sum.inr j), ?_⟩
        dsimp only
        change ((G0.comap e).neighborSet (e.symm (Sum.inr j))).ncard = G0.degree (Sum.inr j)
        rw [hdeg_eq, e.apply_symm_apply]
    have hcardS₁ : S₁.ncard = m := by
      rw [Set.ncard_range_of_injective hinjA, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hcardS₂ : S₂.ncard = M - (9 * M / 20 + 2) := by
      rw [Set.ncard_image_of_injective _ hinjB]
      have hfin : {j : Fin M | 9 * M / 20 + 2 ≤ j.1} =
          ((Finset.univ.filter (fun j : Fin M => 9 * M / 20 + 2 ≤ j.1)) : Set (Fin M)) := by
        ext j; simp
      rw [hfin, Set.ncard_coe_finset]
      have hbij : (Finset.univ.filter (fun j : Fin M => 9 * M / 20 + 2 ≤ j.1)).card =
          (Finset.Ico (9 * M / 20 + 2) M).card := by
        refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
        · intro j hj
          exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2, j.2⟩
        · intro j₁ _ j₂ _ h
          exact Fin.ext h
        · intro k hk
          rw [Finset.mem_Ico] at hk
          exact ⟨⟨k, hk.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.1⟩, rfl⟩
      rw [hbij, Nat.card_Ico]
    have hncard : 3 * n ≤ 4 * (Set.range (fun v : Fin n => (G.neighborSet v).ncard)).ncard := by
      have h1 : S₁.ncard + S₂.ncard ≤ (Set.range (fun v : Fin n => (G.neighborSet v).ncard)).ncard := by
        rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    have hreal : (3 : ℝ) * n ≤ 4 * ((Set.range (fun v : Fin n => (G.neighborSet v).ncard)).ncard : ℝ) := by
      exact_mod_cast hncard
    linarith
  · intro s hs
    let sA : Set (Fin m) := (e.symm ∘ Sum.inl) ⁻¹' s
    let sB : Set (Fin M) := (e.symm ∘ Sum.inr) ⁻¹' s
    have hsA : H.IsClique ((ι ∘ σA) '' sA) ∨ H.IsIndepSet ((ι ∘ σA) '' sA) := by
      rcases hs with hcl | hind
      · left
        rintro _ ⟨i₁, hi₁, rfl⟩ _ ⟨i₂, hi₂, rfl⟩ hne
        have hne' : e.symm (Sum.inl i₁) ≠ e.symm (Sum.inl i₂) :=
          fun h => hne (congrArg (ι ∘ σA) (Sum.inl.inj (e.symm.injective h)))
        have hadj := hcl hi₁ hi₂ hne'
        simpa [G, G0, HA', HA, Erdos1037Proof.Gsum_adj_inl_inl] using hadj
      · right
        rintro _ ⟨i₁, hi₁, rfl⟩ _ ⟨i₂, hi₂, rfl⟩ hne
        have hne' : e.symm (Sum.inl i₁) ≠ e.symm (Sum.inl i₂) :=
          fun h => hne (congrArg (ι ∘ σA) (Sum.inl.inj (e.symm.injective h)))
        have hadj := hind hi₁ hi₂ hne'
        simpa [G, G0, HA', HA, Erdos1037Proof.Gsum_adj_inl_inl] using hadj
    have hsB : HB.IsClique (σB '' sB) ∨ HB.IsIndepSet (σB '' sB) := by
      rcases hs with hcl | hind
      · left
        rintro _ ⟨j₁, hj₁, rfl⟩ _ ⟨j₂, hj₂, rfl⟩ hne
        have hne' : e.symm (Sum.inr j₁) ≠ e.symm (Sum.inr j₂) :=
          fun h => hne (congrArg σB (Sum.inr.inj (e.symm.injective h)))
        have hadj := hcl hj₁ hj₂ hne'
        simpa [G, G0, HB', Erdos1037Proof.Gsum_adj_inr_inr] using hadj
      · right
        rintro _ ⟨j₁, hj₁, rfl⟩ _ ⟨j₂, hj₂, rfl⟩ hne
        have hne' : e.symm (Sum.inr j₁) ≠ e.symm (Sum.inr j₂) :=
          fun h => hne (congrArg σB (Sum.inr.inj (e.symm.injective h)))
        have hadj := hind hj₁ hj₂ hne'
        simpa [G, G0, HB', Erdos1037Proof.Gsum_adj_inr_inr] using hadj
    have hcardA : sA.ncard < Nat.ceil (30 * Real.log M) := by
      have hinj : Function.Injective (ι ∘ σA) := hι.comp σA.injective
      rw [← Set.ncard_image_of_injective sA hinj]
      rcases hsA with hcl | hind
      · exact hHclique _ hcl
      · exact hHindep _ hind
    have hcardB : sB.ncard < Nat.ceil (30 * Real.log M) := by
      rw [← Set.ncard_image_of_injective sB σB.injective]
      have hhom : H.IsHomogeneous (σB '' sB) := SimpleGraph.isHomogeneous_compl.mp hsB
      rcases hhom with hcl | hind
      · exact hHclique _ hcl
      · exact hHindep _ hind
    have hsub : s ⊆ (e.symm ∘ Sum.inl) '' sA ∪ (e.symm ∘ Sum.inr) '' sB := by
      intro v hv
      cases h : e v with
      | inl i =>
        left
        refine ⟨i, ?_, ?_⟩
        · simpa [sA, ← h] using hv
        · simp [← h]
      | inr j =>
        right
        refine ⟨j, ?_, ?_⟩
        · simpa [sB, ← h] using hv
        · simp [← h]
    have hncard_s : s.ncard ≤ sA.ncard + sB.ncard := by
      calc s.ncard
          ≤ ((e.symm ∘ Sum.inl) '' sA ∪ (e.symm ∘ Sum.inr) '' sB).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ((e.symm ∘ Sum.inl) '' sA).ncard + ((e.symm ∘ Sum.inr) '' sB).ncard :=
            Set.ncard_union_le _ _
        _ = sA.ncard + sB.ncard := by
            rw [Set.ncard_image_of_injective _ (e.symm.injective.comp Sum.inl_injective),
                Set.ncard_image_of_injective _ (e.symm.injective.comp Sum.inr_injective)]
    have hlogM : (M : ℝ) ≤ n := by exact_mod_cast (by omega : M ≤ n)
    have hlog_le : Real.log M ≤ Real.log n := Real.log_le_log (by positivity) hlogM
    have hlog1 : 1 < Real.log (M : ℝ) := by
      have h3 : (Real.exp 1 : ℝ) < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hM3 : (Real.exp 1 : ℝ) < M := lt_of_lt_of_le h3 (by exact_mod_cast (by omega : 3 ≤ M))
      simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) hM3
    have hceil : (Nat.ceil (30 * Real.log M) : ℝ) < 30 * Real.log M + 1 := Nat.ceil_lt_add_one (by positivity)
    have hs_nat : s.ncard + 2 ≤ 2 * Nat.ceil (30 * Real.log M) := by omega
    have hs_real : (s.ncard : ℝ) + 2 ≤ 2 * (Nat.ceil (30 * Real.log M) : ℝ) := by exact_mod_cast hs_nat
    linarith
