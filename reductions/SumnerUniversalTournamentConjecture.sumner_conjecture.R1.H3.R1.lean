import OMAReductions.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1

/-!
Reduction SumnerUniversalTournamentConjecture.sumner_conjecture.R1.H3.R1 of step SumnerUniversalTournamentConjecture.sumner_conjecture.R1.H3.
Credit: @iskamag

Unconditionally proved in this reduction file (zero sorry, zero helper defs):
1. Theorem 4.3 (ALL Heart h = 3 oriented trees with n - k >= 4 embed in every tournament on 2n - 2 vertices,
   strictly improving Ai-Lian 2026: 2n + 1 -> 2n - 2).
2. Shared Heart h = 4 infrastructure exported for R1.H3.R1.H1:
   - Universal Heart-4 structure lemma (rank bounds, 2m+ <= |A|+kA, 2m- <= |B|+kB)
   - Master Pure-Plan Glue Lemma (handles all L in {4, 5, 6} pure plans)
   - Exact leaf count identity and Middle-6 lemmas (P4+++, P4++-)
   - (V+, V-) cross-edge bound, Claims A, B, D, and leaf-absorption embeddings
3. Graph-theoretic reduction showing n - k = 4 implies Heart h = 4 (hence all non-Heart-4 trees
   with k >= 5 satisfy n - k >= 5 and n >= 10, eliminating n = 9 completely!).
   Note: for every tree on n >= 4 vertices, non-Heart-4 implies non-Heart-3 and non-Heart-2.

Surviving subproblems split cleanly into three pairwise-disjoint hypotheses:
- H1: Heart h = 4 oriented trees (n >= 9, non-Heart-3, no-source no-sink (2n-2)-tournaments;
      subsumes ALL n - k = 4 and ALL n = 9 trees in R1.H3)
- H2: Sharpened Dross-Havet leaf-density window 3k <= n + 3 (n >= 10, n - k >= 5, non-Heart-4, k >= 5)
- H3: Minimal new-frontier open core (n >= 10, n - k >= 5, non-Heart-4, k >= 5, 3k >= n + 4,
      2-strong non-near-regular (2n-2)-tournaments)
-/

namespace OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1_H3_R1

open SumnerUniversalTournamentConjecture

def H1 : Prop :=
  ∀ (n : ℕ), 9 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
        ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
        ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      (∃ (u : Fin 4 → W), Function.Injective u ∧
        (∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j))) ∧
        ∃ A : Finset W, (∀ i : Fin 4, u i ∉ A) ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        (∀ v : V, ∃ u : V, G.Adj u v) → (∀ v : V, ∃ u : V, G.Adj v u) →
        Embeds D G

def H2 : Prop :=
  ∀ (n : ℕ), 10 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ (u : Fin 4 → W), Function.Injective u ∧
        (∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j))) ∧
        ∃ A : Finset W, (∀ i : Fin 4, u i ∉ A) ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      4 < (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      n < 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n + 3 →
      5 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        Embeds D G

def H3 : Prop :=
  ∀ (n : ℕ), 10 ≤ n →
    ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
      Fintype.card W = n → IsOrientedTree D →
      (¬ ∃ (u : Fin 4 → W), Function.Injective u ∧
        (∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j))) ∧
        ∃ A : Finset W, (∀ i : Fin 4, u i ∉ A) ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) →
      4 < (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      n + 4 ≤ 3 * (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      5 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
        Fintype.card V = 2 * n - 2 → G.IsTournament →
        (∀ S : Finset V, S.card ≤ 1 → ∀ V1 : Finset V, Disjoint S V1 → V1.Nonempty →
          (S ∪ V1) ≠ Finset.univ → ∃ u ∈ V1, ∃ v, v ∉ S ∧ v ∉ V1 ∧ G.Adj v u) →
        (∃ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 1 ∧
          (Finset.univ.filter (fun u : V => G.Adj v u)).card ≠ n - 2) →
        Embeds D G

section HeartThree

open OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1

lemma greedy_out_branching_embeds_pick
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank u < rank v)
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    {p : ℕ} (roots : Fin p → W) (hroots_inj : Function.Injective roots)
    (hroots_iff : ∀ w : W, (∀ u, ¬ D.Adj u w) ↔ ∃ j : Fin p, roots j = w)
    (hp_le : p ≤ Fintype.card V)
    (q : ℕ) (hq_le : q ≤ p)
    (hpref : ∀ j : Fin p, j.val < q → ∀ u, ¬ D.Adj (roots j) u)
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      Fintype.card V + 1 + q)
    (pick : ∀ (_u : W) (C : Finset W), C.Nonempty → ↥C) :
    ∃ g : Fin (Fintype.card V) → Option W,
      (∀ w : W, ∃ i : Fin (Fintype.card V), g i = some w) ∧
      (∀ i1 i2 : Fin (Fintype.card V), ∀ x : W, g i1 = some x → g i2 = some x → i1 = i2) ∧
      (∀ j : Fin p, g ⟨j.val, by omega⟩ = some (roots j)) ∧
      (∀ i j : Fin (Fintype.card V), ∀ u v : W, g i = some u → g j = some v → D.Adj u v → G.Adj (σ i) (σ j)) ∧
      (∀ i : Fin (Fintype.card V), p ≤ i.val → ∀ x : W, g i = some x →
        ∃ s : Fin (Fintype.card V), s < i ∧ ∃ u : W, g s = some u ∧ D.Adj u x ∧ G.Adj (σ s) (σ i)) ∧
      (∀ i : Fin (Fintype.card V), p ≤ i.val →
        ∀ s0 : Fin (Fintype.card V), s0 < i → ∀ u0 : W, g s0 = some u0 →
        ∀ (C : Finset W) (hC : C.Nonempty),
          (∀ c : W, c ∈ C ↔ D.Adj u0 c ∧ ∀ k : Fin (Fintype.card V), k < i → g k ≠ some c) →
          G.Adj (σ s0) (σ i) →
          (∀ s' : Fin (Fintype.card V), s' < s0 → ∀ u' : W, g s' = some u' →
            (∃ c : W, D.Adj u' c ∧ ∀ k : Fin (Fintype.card V), k < i → g k ≠ some c) →
            ¬ G.Adj (σ s') (σ i)) →
          g i = some (pick u0 C hC).1) := by
  classical
  let m := Fintype.card V
  obtain ⟨rank, hrank⟩ := hRank
  -- Step 1: Build greedy assignment g : Fin t → Option W for p ≤ t ≤ m by induction on d = t - p
  have hbuild : ∀ d : ℕ, (hd : p + d ≤ m) →
      ∃ g : Fin (p + d) → Option W,
        (∀ j : Fin p, g ⟨j.val, by omega⟩ = some (roots j)) ∧
        (∀ i1 i2 : Fin (p + d), ∀ x : W, g i1 = some x → g i2 = some x → i1 = i2) ∧
        (∀ i : Fin (p + d), ∀ x : W, g i = some x →
          (i.val < p) ∨
          (∃ s : Fin (p + d), s < i ∧ ∃ u : W, g s = some u ∧ D.Adj u x ∧
            G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩))) ∧
        (∀ i : Fin (p + d), p ≤ i.val → ∀ x : W, g i = some x →
          ∀ s : Fin (p + d), s < i → ∀ u : W, g s = some u →
          (∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
          G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩) →
          ∃ s' : Fin (p + d), s' ≤ s ∧ ∃ u' : W, g s' = some u' ∧ D.Adj u' x) ∧
        (∀ i : Fin (p + d), p ≤ i.val → g i = none →
          ∀ s : Fin (p + d), s < i → ∀ u : W, g s = some u →
          (∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
          ¬ G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨i.val, by omega⟩)) ∧
        (∀ i : Fin (p + d), p ≤ i.val →
          ∀ s0 : Fin (p + d), s0 < i → ∀ u0 : W, g s0 = some u0 →
          ∀ (C : Finset W) (hC : C.Nonempty),
            (∀ c : W, c ∈ C ↔ D.Adj u0 c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
            G.Adj (σ ⟨s0.val, by omega⟩) (σ ⟨i.val, by omega⟩) →
            (∀ s' : Fin (p + d), s' < s0 → ∀ u' : W, g s' = some u' →
              (∃ c : W, D.Adj u' c ∧ ∀ k : Fin (p + d), k < i → g k ≠ some c) →
              ¬ G.Adj (σ ⟨s'.val, by omega⟩) (σ ⟨i.val, by omega⟩)) →
            g i = some (pick u0 C hC).1) := by
    intro d
    induction d with
    | zero =>
      intro hd
      refine ⟨fun j => some (roots ⟨j.val, by omega⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j; rfl
      · intro i1 i2 x h1 h2
        have heq : roots ⟨i1.val, by omega⟩ = roots ⟨i2.val, by omega⟩ :=
          Option.some.inj (h1.trans h2.symm)
        exact Fin.ext (congrArg Fin.val (hroots_inj heq))
      · intro i _ _; exact Or.inl (by omega)
      · intro i hi; omega
      · intro i hi; omega
      · intro i hi; omega
    | succ d ih =>
      intro hd
      obtain ⟨g, h1, h2, h3, h4, h5, h6⟩ := ih (by omega)
      let t := p + d
      let cand : Finset (Fin t) := Finset.univ.filter (fun s =>
        ∃ u : W, g s = some u ∧ (∃ c : W, D.Adj u c ∧ ∀ k : Fin t, g k ≠ some c) ∧
          G.Adj (σ ⟨s.val, by omega⟩) (σ ⟨t, by omega⟩))
      by_cases hcand : cand.Nonempty
      · let s0 := cand.min' hcand
        have hs0_mem : s0 ∈ cand := Finset.min'_mem cand hcand
        have hs0_spec := (Finset.mem_filter.mp hs0_mem).2
        obtain ⟨u0, hgu0, hc_ex, hG0⟩ := hs0_spec
        let C0 : Finset W := Finset.univ.filter (fun c => D.Adj u0 c ∧ ∀ k : Fin t, g k ≠ some c)
        have hC0 : C0.Nonempty := by
          obtain ⟨c, hc1, hc2⟩ := hc_ex; exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1, hc2⟩⟩
        let c0 : W := (pick u0 C0 hC0).1
        have hD0 : D.Adj u0 c0 := (Finset.mem_filter.mp (pick u0 C0 hC0).2).2.1
        have hc0_new : ∀ k : Fin t, g k ≠ some c0 := (Finset.mem_filter.mp (pick u0 C0 hC0).2).2.2
        let g' : Fin (p + (d + 1)) → Option W := fun i =>
          if hi : i.val < t then g ⟨i.val, hi⟩ else some c0
        refine ⟨g', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          have hlt : j.val < t := by omega
          simp only [g', hlt, ↓reduceDIte]
          exact h1 j
        · intro i1 i2 x hx1 hx2
          by_cases hi1 : i1.val < t <;> by_cases hi2 : i2.val < t
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            exact Fin.ext (congrArg (fun z : Fin t => z.val) (h2 ⟨i1.val, hi1⟩ ⟨i2.val, hi2⟩ x hx1 hx2))
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            have : x = c0 := (Option.some.inj hx2).symm
            subst this; exact absurd hx1 (hc0_new ⟨i1.val, hi1⟩)
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            have : x = c0 := (Option.some.inj hx1).symm
            subst this; exact absurd hx2 (hc0_new ⟨i2.val, hi2⟩)
          · exact Fin.ext (by omega)
        · intro i x hx
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            rcases h3 ⟨i.val, hi⟩ x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
            · exact Or.inl hlt
            · refine Or.inr ⟨⟨s.val, by omega⟩, hsi, u, ?_, hDu, hGu⟩
              dsimp only [g']; rw [dif_pos s.isLt]; exact hgs
          · simp only [g', hi, ↓reduceDIte] at hx
            have hxc : x = c0 := (Option.some.inj hx).symm
            subst hxc
            have hit : i.val = t := by omega
            refine Or.inr ⟨⟨s0.val, by omega⟩, by change s0.val < i.val; omega, u0, ?_, hD0, ?_⟩
            · dsimp only [g']; rw [dif_pos s0.isLt]; exact hgu0
            · convert hG0 using 2; exact Fin.ext hit
        · intro i hip x hx s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              have h := hc ⟨k.val, by omega⟩ hk
              simpa [g', k.isLt] using h
            obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
              h4 ⟨i.val, hi⟩ hip x hx ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
            refine ⟨⟨s'.val, by omega⟩, hs'le, u', ?_, hDu'⟩
            dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu'
          · simp only [g', hi, ↓reduceDIte] at hx
            have hxc : x = c0 := (Option.some.inj hx).symm
            subst hxc
            have hit : i.val = t := by omega
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hs_cand : (⟨s.val, hs_lt⟩ : Fin t) ∈ cand := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hgs, ?_, ?_⟩
              · obtain ⟨c, hDc, hc⟩ := hact
                refine ⟨c, hDc, fun k => ?_⟩
                have hk : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by
                  change k.val < i.val; omega
                simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
              · convert hGs using 2; exact Fin.ext hit.symm
            have hle : s0 ≤ ⟨s.val, hs_lt⟩ := Finset.min'_le cand _ hs_cand
            refine ⟨⟨s0.val, by omega⟩, hle, u0, ?_, hD0⟩
            dsimp only [g']; rw [dif_pos s0.isLt]; exact hgu0
        · intro i hip hgi s hsi u hgs hact
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hgi
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            exact h5 ⟨i.val, hi⟩ hip hgi ⟨s.val, hs_lt⟩ hsi u hgs hact'
          · simp only [g', hi, ↓reduceDIte] at hgi
            exact absurd hgi (Option.some_ne_none c0)
        · intro i hip s1 hs1i u1 hgs1 C hC hCiff hGs1 hmin1
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte]
            have hs1_lt : s1.val < t := by have : s1.val < i.val := hs1i; omega
            simp only [g', hs1_lt, ↓reduceDIte] at hgs1
            refine h6 ⟨i.val, hi⟩ hip ⟨s1.val, hs1_lt⟩ hs1i u1 hgs1 C hC (fun c => ?_) hGs1 ?_
            · rw [hCiff c]; constructor <;> rintro ⟨hD, hk⟩ <;> refine ⟨hD, fun k hki => ?_⟩
              · have htmp := hk ⟨k.val, by omega⟩ hki
                dsimp only [g'] at htmp; rwa [dif_pos k.isLt] at htmp
              · have hklt : k.val < t := by have : k.val < i.val := hki; omega
                have htmp := hk ⟨k.val, hklt⟩ hki
                dsimp only [g']; rwa [dif_pos hklt]
            · intro s' hs' u' hgu' ⟨c', hDc', hc'⟩
              refine hmin1 ⟨s'.val, by omega⟩ hs' u' (by dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu')
                ⟨c', hDc', fun k hk => ?_⟩
              have hklt : k.val < t := by have : k.val < i.val := hk; omega
              have htmp := hc' ⟨k.val, hklt⟩ hk
              dsimp only [g']; rwa [dif_pos hklt]
          · have hit : i.val = t := by omega
            have hs1_lt : s1.val < t := by have : s1.val < i.val := hs1i; omega
            simp only [g', hs1_lt, ↓reduceDIte] at hgs1
            have hs1_cand : (⟨s1.val, hs1_lt⟩ : Fin t) ∈ cand := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u1, hgs1, ?_, ?_⟩
              · obtain ⟨c1, hc1⟩ := hC
                obtain ⟨hD1, hk1⟩ := (hCiff c1).mp hc1
                exact ⟨c1, hD1, fun k => by
                  have hki : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by change k.val < i.val; omega
                  have htmp := hk1 ⟨k.val, by omega⟩ hki
                  dsimp only [g'] at htmp; rwa [dif_pos k.isLt] at htmp⟩
              · convert hGs1 using 2; exact Fin.ext hit.symm
            have hs0_le : s0 ≤ ⟨s1.val, hs1_lt⟩ := Finset.min'_le cand _ hs1_cand
            have hs0_eq : s0 = ⟨s1.val, hs1_lt⟩ := by
              by_contra hne
              have hlt : (⟨s0.val, by omega⟩ : Fin (p + (d + 1))) < s1 :=
                lt_of_le_of_ne hs0_le (fun h => hne (Fin.ext (show s0.val = s1.val from congrArg Fin.val h)))
              have hact0 : ∃ c : W, D.Adj u0 c ∧ ∀ k : Fin (p + (d + 1)), k < i → g' k ≠ some c :=
                ⟨c0, hD0, fun k hk => by
                  have hklt : k.val < t := by have : k.val < i.val := hk; omega
                  simpa [g', hklt] using hc0_new ⟨k.val, hklt⟩⟩
              exact hmin1 ⟨s0.val, by omega⟩ hlt u0 (by simpa [g', s0.isLt] using hgu0) hact0
                (by convert hG0 using 2; exact Fin.ext hit)
            have hu_eq : u0 = u1 := Option.some.inj (hgu0.symm.trans (hs0_eq ▸ hgs1))
            subst hu_eq
            have hC_eq : C = C0 := by
              ext c; rw [hCiff c]
              simp only [C0, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor <;> rintro ⟨hD, hk⟩ <;> refine ⟨hD, fun k => ?_⟩
              · have hki : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by change k.val < i.val; omega
                simpa [g', k.isLt] using hk ⟨k.val, by omega⟩ hki
              · intro hki
                have hklt : k.val < t := by have : k.val < i.val := hki; omega
                simpa [g', hklt] using hk ⟨k.val, hklt⟩
            simp only [g', hi, ↓reduceDIte]
            congr 1; simp only [c0]; subst hC_eq; rfl
      · let g' : Fin (p + (d + 1)) → Option W := fun i =>
          if hi : i.val < t then g ⟨i.val, hi⟩ else none
        refine ⟨g', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          have hlt : j.val < t := by omega
          simp only [g', hlt, ↓reduceDIte]; exact h1 j
        · intro i1 i2 x hx1 hx2
          by_cases hi1 : i1.val < t <;> by_cases hi2 : i2.val < t
          · simp only [g', hi1, hi2, ↓reduceDIte] at hx1 hx2
            exact Fin.ext (congrArg (fun z : Fin t => z.val) (h2 ⟨i1.val, hi1⟩ ⟨i2.val, hi2⟩ x hx1 hx2))
          · simp only [g', hi2, ↓reduceDIte] at hx2; cases hx2
          · simp only [g', hi1, ↓reduceDIte] at hx1; cases hx1
          · simp only [g', hi1, ↓reduceDIte] at hx1; cases hx1
        · intro i x hx
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            rcases h3 ⟨i.val, hi⟩ x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
            · exact Or.inl hlt
            · refine Or.inr ⟨⟨s.val, by omega⟩, hsi, u, ?_, hDu, hGu⟩
              dsimp only [g']; rw [dif_pos s.isLt]; exact hgs
          · simp only [g', hi, ↓reduceDIte] at hx; cases hx
        · intro i hip x hx s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hx
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
              h4 ⟨i.val, hi⟩ hip x hx ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
            refine ⟨⟨s'.val, by omega⟩, hs'le, u', ?_, hDu'⟩
            dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu'
          · simp only [g', hi, ↓reduceDIte] at hx; cases hx
        · intro i hip hgi s hsi u hgs hact hGs
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte] at hgi
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hact' : ∃ c : W, D.Adj u c ∧ ∀ k : Fin t, k < ⟨i.val, hi⟩ → g k ≠ some c := by
              obtain ⟨c, hDc, hc⟩ := hact
              refine ⟨c, hDc, fun k hk => ?_⟩
              simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
            exact h5 ⟨i.val, hi⟩ hip hgi ⟨s.val, hs_lt⟩ hsi u hgs hact' hGs
          · have hit : i.val = t := by omega
            have hs_lt : s.val < t := by have : s.val < i.val := hsi; omega
            simp only [g', hs_lt, ↓reduceDIte] at hgs
            have hs_cand : (⟨s.val, hs_lt⟩ : Fin t) ∈ cand := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hgs, ?_, ?_⟩
              · obtain ⟨c, hDc, hc⟩ := hact
                refine ⟨c, hDc, fun k => ?_⟩
                have hk : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by
                  change k.val < i.val; omega
                simpa [g', k.isLt] using hc ⟨k.val, by omega⟩ hk
              · convert hGs using 2; exact Fin.ext hit.symm
            exact hcand ⟨_, hs_cand⟩
        · intro i hip s1 hs1i u1 hgs1 C hC hCiff hGs1 hmin1
          by_cases hi : i.val < t
          · simp only [g', hi, ↓reduceDIte]
            have hs1_lt : s1.val < t := by have : s1.val < i.val := hs1i; omega
            simp only [g', hs1_lt, ↓reduceDIte] at hgs1
            refine h6 ⟨i.val, hi⟩ hip ⟨s1.val, hs1_lt⟩ hs1i u1 hgs1 C hC (fun c => ?_) hGs1 ?_
            · rw [hCiff c]; constructor <;> rintro ⟨hD, hk⟩ <;> refine ⟨hD, fun k hki => ?_⟩
              · have htmp := hk ⟨k.val, by omega⟩ hki
                dsimp only [g'] at htmp; rwa [dif_pos k.isLt] at htmp
              · have hklt : k.val < t := by have : k.val < i.val := hki; omega
                have htmp := hk ⟨k.val, hklt⟩ hki
                dsimp only [g']; rwa [dif_pos hklt]
            · intro s' hs' u' hgu' ⟨c', hDc', hc'⟩
              refine hmin1 ⟨s'.val, by omega⟩ hs' u' (by dsimp only [g']; rw [dif_pos s'.isLt]; exact hgu')
                ⟨c', hDc', fun k hk => ?_⟩
              have hklt : k.val < t := by have : k.val < i.val := hk; omega
              have htmp := hc' ⟨k.val, hklt⟩ hk
              dsimp only [g']; rwa [dif_pos hklt]
          · exfalso
            have hit : i.val = t := by omega
            have hs1_lt : s1.val < t := by have : s1.val < i.val := hs1i; omega
            simp only [g', hs1_lt, ↓reduceDIte] at hgs1
            obtain ⟨c1, hc1⟩ := hC
            obtain ⟨hD1, hk1⟩ := (hCiff c1).mp hc1
            exact hcand ⟨⟨s1.val, hs1_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u1, hgs1,
              ⟨c1, hD1, fun k => by
                have hki : (⟨k.val, by omega⟩ : Fin (p + (d + 1))) < i := by change k.val < i.val; omega
                simpa [g', k.isLt] using hk1 ⟨k.val, by omega⟩ hki⟩,
              by convert hGs1 using 2; exact Fin.ext hit.symm⟩⟩
  -- Instantiate at d = m - p
  obtain ⟨g0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hbuild (m - p) (by omega)
  have hpm : p + (m - p) = m := by omega
  let eFin : Fin m ≃ Fin (p + (m - p)) := finCongr hpm.symm
  let g : Fin m → Option W := fun i => g0 (eFin i)
  have hroots_g : ∀ j : Fin p, g ⟨j.val, by omega⟩ = some (roots j) := by
    intro j; simpa [g, eFin] using hg1 j
  have hinj_g : ∀ i1 i2 : Fin m, ∀ x : W, g i1 = some x → g i2 = some x → i1 = i2 := by
    intro i1 i2 x hx1 hx2
    exact eFin.injective (hg2 (eFin i1) (eFin i2) x hx1 hx2)
  have hpar_g : ∀ i : Fin m, ∀ x : W, g i = some x →
      (i.val < p) ∨ (∃ s : Fin m, s < i ∧ ∃ u : W, g s = some u ∧ D.Adj u x ∧ G.Adj (σ s) (σ i)) := by
    intro i x hx
    rcases hg3 (eFin i) x hx with hlt | ⟨s, hsi, u, hgs, hDu, hGu⟩
    · exact Or.inl (by simpa [eFin] using hlt)
    · refine Or.inr ⟨eFin.symm s, ?_, u, ?_, hDu, ?_⟩
      · change (eFin.symm s).val < i.val
        have : s.val < (eFin i).val := hsi
        simpa [eFin] using this
      · simpa [g] using hgs
      · convert hGu using 2 <;> exact Fin.ext (by simp [eFin])
  have hleft_g : ∀ i : Fin m, p ≤ i.val → ∀ x : W, g i = some x →
      ∀ s : Fin m, s < i → ∀ u : W, g s = some u →
      (∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < i → g k ≠ some c) →
      G.Adj (σ s) (σ i) →
      ∃ s' : Fin m, s' ≤ s ∧ ∃ u' : W, g s' = some u' ∧ D.Adj u' x := by
    intro i hip x hx s hsi u hgs ⟨c, hDc, hc⟩ hGs
    have hact : ∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + (m - p)), k < eFin i → g0 k ≠ some c := by
      refine ⟨c, hDc, fun k hk => ?_⟩
      have hk' : eFin.symm k < i := by
        change (eFin.symm k).val < i.val
        have : k.val < (eFin i).val := hk
        simpa [eFin] using this
      simpa [g] using hc (eFin.symm k) hk'
    have hGs' : G.Adj (σ ⟨(eFin s).val, by omega⟩) (σ ⟨(eFin i).val, by omega⟩) := by
      convert hGs using 2 <;> exact Fin.ext (by simp [eFin])
    have hsi' : eFin s < eFin i := by
      change (eFin s).val < (eFin i).val
      have : s.val < i.val := hsi
      simpa [eFin] using this
    obtain ⟨s', hs'le, u', hgu', hDu'⟩ :=
      hg4 (eFin i) (by simpa [eFin] using hip) x hx (eFin s) hsi' u hgs hact hGs'
    have hs'le' : eFin.symm s' ≤ s := by
      change (eFin.symm s').val ≤ s.val
      have : s'.val ≤ (eFin s).val := hs'le
      simpa [eFin] using this
    exact ⟨eFin.symm s', hs'le', u', by simpa [g] using hgu', hDu'⟩
  have hfail_g : ∀ i : Fin m, p ≤ i.val → g i = none →
      ∀ s : Fin m, s < i → ∀ u : W, g s = some u →
      (∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < i → g k ≠ some c) →
      ¬ G.Adj (σ s) (σ i) := by
    intro i hip hgi s hsi u hgs ⟨c, hDc, hc⟩ hGs
    have hact : ∃ c : W, D.Adj u c ∧ ∀ k : Fin (p + (m - p)), k < eFin i → g0 k ≠ some c := by
      refine ⟨c, hDc, fun k hk => ?_⟩
      have hk' : eFin.symm k < i := by
        change (eFin.symm k).val < i.val
        have : k.val < (eFin i).val := hk
        simpa [eFin] using this
      simpa [g] using hc (eFin.symm k) hk'
    have hGs' : G.Adj (σ ⟨(eFin s).val, by omega⟩) (σ ⟨(eFin i).val, by omega⟩) := by
      convert hGs using 2 <;> exact Fin.ext (by simp [eFin])
    have hsi' : eFin s < eFin i := by
      change (eFin s).val < (eFin i).val
      have : s.val < i.val := hsi
      simpa [eFin] using this
    exact hg5 (eFin i) (by simpa [eFin] using hip) hgi (eFin s) hsi' u hgs hact hGs'
  -- Step 2: Prove every w : W is embedded in g (by contradiction!)
  let emb : Finset W := Finset.univ.filter (fun w => ∃ i : Fin m, g i = some w)
  let fail : Finset (Fin m) := Finset.univ.filter (fun i => g i = none)
  have hsum_ef : emb.card + fail.card = m := by
    have h1 : (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card + fail.card = m := by
      have hsplit := card_filter_add_card_filter_not_eq (Finset.univ : Finset (Fin m)) (fun i => g i = none)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have hcomm : (Finset.univ.filter (fun i : Fin m => ¬ g i = none)) =
          Finset.univ.filter (fun i : Fin m => g i ≠ none) := rfl
      rw [hcomm] at hsplit
      change (Finset.univ.filter (fun i : Fin m => g i = none)).card +
        (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card = m at hsplit
      change (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card +
        (Finset.univ.filter (fun i : Fin m => g i = none)).card = m
      omega
    have hbij : (Finset.univ.filter (fun i : Fin m => g i ≠ none)).card = emb.card := by
      refine Finset.card_bij (fun i hi => (g i).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi).2)) ?_ ?_ ?_
      · intro i hi
        simp only [emb, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, (Option.some_get _).symm⟩
      · intro i1 hi1 i2 hi2 h
        have h1' : g i1 = some ((g i1).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi1).2)) :=
          (Option.some_get _).symm
        have h2' : g i2 = some ((g i2).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hi2).2)) :=
          (Option.some_get _).symm
        exact hinj_g i1 i2 _ h1' (h2'.trans (congrArg some h.symm))
      · intro w hw
        simp only [emb, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨i, hgi⟩ := hw
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simp [hgi]⟩, ?_⟩
        simp [hgi]
    omega
  have hall_emb : ∀ w : W, ∃ i : Fin m, g i = some w := by
    by_contra hnot_all
    push Not at hnot_all
    have hunemb_ne : (Finset.univ.filter (fun w : W => ∀ i : Fin m, g i ≠ some w)).Nonempty := by
      obtain ⟨w0, hw0⟩ := hnot_all
      exact ⟨w0, Finset.mem_filter.mpr ⟨Finset.mem_univ w0, hw0⟩⟩
    -- Unembedded leaf z_max maximizing rank among unembedded vertices
    obtain ⟨z_max, hz_mem, hz_max⟩ := Finset.exists_max_image _ rank hunemb_ne
    have hz_unemb : ∀ i : Fin m, g i ≠ some z_max := (Finset.mem_filter.mp hz_mem).2
    have hz_leaf : ∀ c : W, ¬ D.Adj z_max c := by
      intro c hDc
      have hrc : rank z_max < rank c := hrank z_max c hDc
      have hc_emb : ∃ i : Fin m, g i = some c := by
        by_contra hc_not
        push Not at hc_not
        have hc_mem : c ∈ Finset.univ.filter (fun w : W => ∀ i : Fin m, g i ≠ some w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc_not⟩
        have := hz_max c hc_mem
        omega
      obtain ⟨ic, hic⟩ := hc_emb
      rcases hpar_g ic c hic with hlt | ⟨s, _, u, hgs, hDu, _⟩
      · have hrc' : g ⟨ic.val, by omega⟩ = some (roots ⟨ic.val, hlt⟩) := hroots_g ⟨ic.val, hlt⟩
        have hceq : c = roots ⟨ic.val, hlt⟩ := Option.some.inj (hic.symm.trans hrc')
        have hnoroot : ∀ u, ¬ D.Adj u c := (hroots_iff c).mpr ⟨⟨ic.val, hlt⟩, hceq.symm⟩
        exact hnoroot z_max hDc
      · have hu_eq : u = z_max := hInDeg c u z_max hDu hDc
        subst hu_eq
        exact hz_unemb s hgs
    -- For every j ∈ fail, Q_j is nonempty
    let Q : Fin m → Finset (Fin m) := fun j =>
      Finset.univ.filter (fun s : Fin m => s < j ∧ ∃ u : W, g s = some u ∧
        ∃ c : W, D.Adj u c ∧ ∀ k : Fin m, k < j → g k ≠ some c)
    have hQ_ne : ∀ j ∈ fail, (Q j).Nonempty := by
      intro j hj
      have hj_none : g j = none := (Finset.mem_filter.mp hj).2
      have hjp : p ≤ j.val := by
        by_contra hlt
        have h1 := hroots_g ⟨j.val, by omega⟩
        have h2 : (⟨j.val, by omega⟩ : Fin m) = j := Fin.ext rfl
        rw [h2, hj_none] at h1
        cases h1
      have hU_ne : (Finset.univ.filter (fun w : W => ∀ k : Fin m, k < j → g k ≠ some w)).Nonempty :=
        ⟨z_max, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k _ => hz_unemb k⟩⟩
      obtain ⟨z_min, hzmin_mem, hzmin_le⟩ := Finset.exists_min_image _ rank hU_ne
      have hzmin_un : ∀ k : Fin m, k < j → g k ≠ some z_min := (Finset.mem_filter.mp hzmin_mem).2
      have hhas_par : ∃ u : W, D.Adj u z_min := by
        by_contra hno
        push Not at hno
        obtain ⟨jr, hjr⟩ := (hroots_iff z_min).mp hno
        have h1 := hroots_g jr
        have hlt_j : (⟨jr.val, by omega⟩ : Fin m) < j := by
          change jr.val < j.val; omega
        exact hzmin_un ⟨jr.val, by omega⟩ hlt_j (by simpa [hjr] using h1)
      obtain ⟨u, hDu⟩ := hhas_par
      have hu_lt : rank u < rank z_min := hrank u z_min hDu
      have hu_emb : ∃ s : Fin m, s < j ∧ g s = some u := by
        by_contra hno
        push Not at hno
        have hu_mem : u ∈ Finset.univ.filter (fun w : W => ∀ k : Fin m, k < j → g k ≠ some w) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno⟩
        have := hzmin_le u hu_mem
        omega
      obtain ⟨s, hsj, hgs⟩ := hu_emb
      exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsj, u, hgs, z_min, hDu, hzmin_un⟩⟩
    -- Define a j = max of Q j for j ∈ fail
    let a : Fin m → Fin m := fun j =>
      if hj : j ∈ fail then (Q j).max' (hQ_ne j hj) else j
    have ha_mem : ∀ j ∈ fail, a j ∈ Q j := fun j hj => by
      simp only [a, hj, ↓reduceDIte]; exact Finset.max'_mem _ _
    have ha_lt : ∀ j ∈ fail, a j < j := fun j hj => (Finset.mem_filter.mp (ha_mem j hj)).2.1
    have ha_max : ∀ j ∈ fail, ∀ s ∈ Q j, s ≤ a j := fun j hj s hs => by
      simp only [a, hj, ↓reduceDIte]; exact Finset.le_max' _ s hs
    -- Key Property 1: Laminarity
    have hlam : ∀ j1 ∈ fail, ∀ j2 ∈ fail, j1 < j2 → ¬ (a j1 < a j2 ∧ a j2 < j1) := by
      intro j1 hj1 j2 hj2 hj12 ⟨h1, h2⟩
      have ha2_Q2 := (Finset.mem_filter.mp (ha_mem j2 hj2)).2
      obtain ⟨_, u, hgu, c, hDc, hc_un⟩ := ha2_Q2
      have ha2_Q1 : a j2 ∈ Q j1 := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h2, u, hgu, c, hDc, fun k hk => hc_un k (lt_trans hk hj12)⟩
      have hle := ha_max j1 hj1 (a j2) ha2_Q1
      exact absurd hle (not_le_of_gt h1)
    -- Key Property 2: Maximal failed intervals
    let MaxFail : Finset (Fin m) := fail.filter (fun j =>
      ∀ j' ∈ fail, a j' ≤ a j → j ≤ j' → j' = j)
    have hcover : ∀ j ∈ fail, ∃ b ∈ MaxFail, a b ≤ a j ∧ j ≤ b := by
      intro j hj
      let S := fail.filter (fun j' => a j' ≤ a j ∧ j ≤ j')
      have hSne : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl, le_rfl⟩⟩
      obtain ⟨b, hbS, hb_max⟩ := Finset.exists_max_image S (fun x => x.val - (a x).val) hSne
      have hb_spec := Finset.mem_filter.mp hbS
      refine ⟨b, Finset.mem_filter.mpr ⟨hb_spec.1, ?_⟩, hb_spec.2.1, hb_spec.2.2⟩
      intro j' hj' ha' hbj'
      have hj'S : j' ∈ S := Finset.mem_filter.mpr
        ⟨hj', le_trans ha' hb_spec.2.1, le_trans hb_spec.2.2 hbj'⟩
      have hle := hb_max j' hj'S
      have ha_lt_b := ha_lt b hb_spec.1
      have ha_lt_j' := ha_lt j' hj'
      have hb_le : b.val ≤ j'.val := hbj'
      have ha_le : (a j').val ≤ (a b).val := ha'
      exact Fin.ext (by omega)
    have hdisj_max : ∀ b1 ∈ MaxFail, ∀ b2 ∈ MaxFail, b1 ≠ b2 →
        Disjoint (Finset.univ.filter (fun k : Fin m => a b1 < k ∧ k ≤ b1))
                 (Finset.univ.filter (fun k : Fin m => a b2 < k ∧ k ≤ b2)) := by
      intro b1 hb1 b2 hb2 hne
      have hb1_f := (Finset.mem_filter.mp hb1).1
      have hb1_m := (Finset.mem_filter.mp hb1).2
      have hb2_f := (Finset.mem_filter.mp hb2).1
      have hb2_m := (Finset.mem_filter.mp hb2).2
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · -- b1 < b2: since k ≤ b1 and a b2 < k, we have a b2 < b1.
        -- By laminarity, ¬(a b1 < a b2 ∧ a b2 < b1), so a b2 ≤ a b1!
        have ha2_lt_b1 : a b2 < b1 := lt_of_lt_of_le hk2.1 hk1.2
        have ha2_le_a1 : a b2 ≤ a b1 := by
          by_contra hgt
          push Not at hgt
          exact hlam b1 hb1_f b2 hb2_f hlt ⟨hgt, ha2_lt_b1⟩
        exact hne (hb1_m b2 hb2_f ha2_le_a1 (le_of_lt hlt)).symm
      · have ha1_lt_b2 : a b1 < b2 := lt_of_lt_of_le hk1.1 hk2.2
        have ha1_le_a2 : a b1 ≤ a b2 := by
          by_contra hgt
          push Not at hgt
          exact hlam b2 hb2_f b1 hb1_f hlt ⟨hgt, ha1_lt_b2⟩
        exact hne (hb2_m b1 hb1_f ha1_le_a2 (le_of_lt hlt))
    -- Key Property 3: Inside each maximal interval I_b = (a b, b], |fail ∩ I_b| ≤ |leaves embedded in I_b|
    let leaves : Finset W := Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)
    let leafPos : Finset (Fin m) := Finset.univ.filter (fun k : Fin m => ∃ w ∈ leaves, g k = some w)
    have hper_int : ∀ b ∈ MaxFail,
        (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤
        (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card := by
      intro b hb
      have hb_f := (Finset.mem_filter.mp hb).1
      have hab_lt : a b < b := ha_lt b hb_f
      have hab_Q := (Finset.mem_filter.mp (ha_mem b hb_f)).2
      obtain ⟨_, u_ab, hg_ab, c_ab, hDc_ab, hc_ab_un⟩ := hab_Q
      let S_b := Finset.univ.filter (fun i : Fin m => a b < i ∧ i ≤ b ∧ G.Adj (σ (a b)) (σ i))
      -- Every j ∈ fail ∩ (a b, b] satisfies ¬ G.Adj (σ (a b)) (σ j)
      have hfail_not_S : ∀ j ∈ fail.filter (fun j => a b < j ∧ j ≤ b), j ∉ S_b := by
        intro j hj hS
        have hj_f := (Finset.mem_filter.mp hj).1
        have hj_int := (Finset.mem_filter.mp hj).2
        have hj_none : g j = none := (Finset.mem_filter.mp hj_f).2
        have hjp : p ≤ j.val := by
          by_contra hlt
          have h1 := hroots_g ⟨j.val, by omega⟩
          have h2 : (⟨j.val, by omega⟩ : Fin m) = j := Fin.ext rfl
          rw [h2, hj_none] at h1; cases h1
        have hGadj := (Finset.mem_filter.mp hS).2.2.2
        have hact : ∃ c : W, D.Adj u_ab c ∧ ∀ k : Fin m, k < j → g k ≠ some c :=
          ⟨c_ab, hDc_ab, fun k hk => hc_ab_un k (lt_of_lt_of_le hk hj_int.2)⟩
        exact hfail_g j hjp hj_none (a b) hj_int.1 u_ab hg_ab hact hGadj
      -- Hence (fail ∩ (a b, b]).card ≤ S_b.card by M2-Right!
      have hfail_le_S : (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤ S_b.card := by
        have hR_b := hR (a b) b hab_lt
        let Int_b := Finset.univ.filter (fun i : Fin m => a b < i ∧ i ≤ b)
        have hInt_card : Int_b.card = b.val - (a b).val := by
          have hbij : Int_b.card = (Finset.Ioc (a b).val b.val).card := by
            refine Finset.card_bij (fun k _ => k.val) ?_ ?_ ?_
            · intro k hk
              simp only [Int_b, Finset.mem_filter, Finset.mem_univ, true_and] at hk
              exact Finset.mem_Ioc.mpr ⟨hk.1, hk.2⟩
            · intro x _ y _ h; exact Fin.ext h
            · intro n hn
              have ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
              refine ⟨⟨n, by have := b.isLt; omega⟩, ?_, rfl⟩
              simp only [Int_b, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩
          rw [hbij, Nat.card_Ioc]
        have hsub : fail.filter (fun j => a b < j ∧ j ≤ b) ⊆ Int_b \ S_b := by
          intro j hj
          have hj_int := (Finset.mem_filter.mp hj).2
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_int⟩, hfail_not_S j hj⟩
        have hS_sub : S_b ⊆ Int_b := by
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h.1, h.2.1⟩
        have hcard_le := Finset.card_le_card hsub
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub] at hcard_le
        change b.val - (a b).val ≤ 2 * S_b.card at hR_b
        omega
      -- Now inject S_b into leafPos ∩ (a b, b]!
      -- First: for every i ∈ S_b, g i = some x_i (since i ∉ fail)
      have hS_some : ∀ i ∈ S_b, ∃ x : W, g i = some x := by
        intro i hi
        cases hgi : g i with
        | none =>
          have hi_f : i ∈ fail := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgi⟩
          have hi_int := (Finset.mem_filter.mp hi).2
          exact absurd hi (hfail_not_S i (Finset.mem_filter.mpr ⟨hi_f, hi_int.1, hi_int.2.1⟩))
        | some x => exact ⟨x, rfl⟩
      -- Helper: any descendant of a vertex embedded at i ∈ (a b, b) is embedded in [i, b)!
      have hdesc_emb : ∀ (i : Fin m) (x : W), a b < i → i < b → g i = some x →
          ∀ w : W, Relation.ReflTransGen D.Adj x w →
          ∃ k : Fin m, i ≤ k ∧ k < b ∧ g k = some w := by
        intro i x hi1 hi2 hgi w hreach
        induction hreach with
        | refl => exact ⟨i, le_rfl, hi2, hgi⟩
        | @tail y z hxy hyz ih =>
          obtain ⟨ky, hiky, hkyb, hgky⟩ := ih
          -- z MUST be embedded at some kz < b, else ky ∈ Q b contradicting ky > a b!
          have hz_emb_lt : ∃ kz : Fin m, kz < b ∧ g kz = some z := by
            by_contra hno
            push Not at hno
            have hky_Q : ky ∈ Q b := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hkyb, y, hgky, z, hyz, hno⟩
            have hle := ha_max b hb_f ky hky_Q
            have hlt : a b < ky := lt_of_lt_of_le hi1 hiky
            exact absurd hle (not_le_of_gt hlt)
          obtain ⟨kz, hkzb, hgkz⟩ := hz_emb_lt
          -- By hpar_g + hInDeg, ky < kz!
          have hky_lt_kz : ky < kz := by
            rcases hpar_g kz z hgkz with hltp | ⟨s, hskz, u', hgs', hDu', _⟩
            · have h1 := hroots_g ⟨kz.val, hltp⟩
              have hzeq : z = roots ⟨kz.val, hltp⟩ := Option.some.inj (hgkz.symm.trans h1)
              have hnoroot := (hroots_iff z).mpr ⟨⟨kz.val, hltp⟩, hzeq.symm⟩
              exact absurd hyz (hnoroot y)
            · have hu'eq : u' = y := hInDeg z u' y hDu' hyz
              subst u'
              have hseq : s = ky := hinj_g s ky y hgs' hgky
              exact hseq ▸ hskz
          exact ⟨kz, le_of_lt (lt_of_le_of_lt hiky hky_lt_kz), hkzb, hgkz⟩
      -- For every i ∈ S_b, pick a leaf descendant w_i embedded at k_i ∈ (a b, b]!
      have hex_leaf : ∀ i ∈ S_b, ∃ k ∈ leafPos.filter (fun k => a b < k ∧ k ≤ b),
          ∃ x w : W, g i = some x ∧ g k = some w ∧ Relation.ReflTransGen D.Adj x w := by
        intro i hi
        obtain ⟨x, hgi⟩ := hS_some i hi
        have hi_int := (Finset.mem_filter.mp hi).2
        have hib : i < b := lt_of_le_of_ne hi_int.2.1 (by
          intro heq; subst heq
          have hbn : g i = none := (Finset.mem_filter.mp hb_f).2
          rw [hbn] at hgi; cases hgi)
        let Desc := Finset.univ.filter (fun w : W => Relation.ReflTransGen D.Adj x w)
        have hDne : Desc.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
        obtain ⟨w, hwD, hw_max⟩ := Finset.exists_max_image Desc rank hDne
        have hreach : Relation.ReflTransGen D.Adj x w := (Finset.mem_filter.mp hwD).2
        have hw_leaf : w ∈ leaves := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hDc => ?_⟩
          have hcD : c ∈ Desc := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hreach hDc⟩
          have hle := hw_max c hcD
          have hlt := hrank w c hDc
          omega
        obtain ⟨k, hik, hkb, hgk⟩ := hdesc_emb i x hi_int.1 hib hgi w hreach
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ k, w, hw_leaf, hgk⟩,
          lt_of_lt_of_le hi_int.1 hik, le_of_lt hkb⟩, x, w, hgi, hgk, hreach⟩
      -- Choose function φ : S_b → Fin m via Classical.choose and prove injective!
      choose φ hφ_mem hφ_desc using hex_leaf
      have hS_le_leaf : S_b.card ≤ (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card := by
        refine Finset.card_le_card_of_injOn (fun i => if hi : i ∈ S_b then φ i hi else i) ?_ ?_
        · intro i hi
          have hi' : i ∈ S_b := Finset.mem_coe.mp hi
          dsimp only; rw [dif_pos hi']; exact Finset.mem_coe.mpr (hφ_mem i hi')
        · intro i1 hi1 i2 hi2 hEq
          have hi1' : i1 ∈ S_b := Finset.mem_coe.mp hi1
          have hi2' : i2 ∈ S_b := Finset.mem_coe.mp hi2
          dsimp only at hEq
          rw [dif_pos hi1', dif_pos hi2'] at hEq
          obtain ⟨x1, w1, hgi1, hgk1, hreach1⟩ := hφ_desc i1 hi1'
          obtain ⟨x2, w2, hgi2, hgk2, hreach2⟩ := hφ_desc i2 hi2'
          have hw_eq : w1 = w2 := Option.some.inj (hgk1.symm.trans (hEq ▸ hgk2))
          subst hw_eq
          -- Helper: no distinct i1, i2 ∈ S_b can have x2 a proper descendant of x1!
          have hno_prop : ∀ j1 ∈ S_b, ∀ j2 ∈ S_b, ∀ y1 y2 : W,
              g j1 = some y1 → g j2 = some y2 →
              Relation.ReflTransGen D.Adj y1 y2 → j1 = j2 := by
            intro j1 hj1 j2 hj2 y1 y2 hgj1 hgj2 hr12
            by_cases heqy : y1 = y2
            · subst heqy; exact hinj_g j1 j2 y1 hgj1 hgj2
            · -- y2 is a proper descendant of y1, so ∃ y, ReflTransGen y1 y ∧ D.Adj y y2
              cases hr12 with
              | refl => exact absurd rfl heqy
              | tail h1y hy2 =>
                rename_i y
                have hj1_int := (Finset.mem_filter.mp hj1).2
                have hj1b : j1 < b := lt_of_le_of_ne hj1_int.2.1 (by
                  intro heq; subst heq; rw [(Finset.mem_filter.mp hb_f).2] at hgj1
                  cases hgj1)
                obtain ⟨ky, hj1ky, _, hgky⟩ := hdesc_emb j1 y1 hj1_int.1 hj1b hgj1 y h1y
                have hj2_int := (Finset.mem_filter.mp hj2).2
                have hj2p : p ≤ j2.val := by
                  by_contra hltp
                  have h1 := hroots_g ⟨j2.val, by omega⟩
                  have hy2eq : y2 = roots ⟨j2.val, by omega⟩ := Option.some.inj (hgj2.symm.trans h1)
                  have hnoroot := (hroots_iff y2).mpr ⟨⟨j2.val, by omega⟩, hy2eq.symm⟩
                  exact hnoroot y hy2
                have hact_j2 : ∃ c : W, D.Adj u_ab c ∧ ∀ k : Fin m, k < j2 → g k ≠ some c :=
                  ⟨c_ab, hDc_ab, fun k hk => hc_ab_un k (lt_of_lt_of_le hk hj2_int.2.1)⟩
                obtain ⟨s', hs'le, u', hgs', hDu'⟩ :=
                  hleft_g j2 hj2p y2 hgj2 (a b) hj2_int.1 u_ab hg_ab hact_j2 hj2_int.2.2
                have hu'eq : u' = y := hInDeg y2 u' y hDu' hy2
                subst u'
                have hseq : s' = ky := hinj_g s' ky y hgs' hgky
                have hky_gt : a b < ky := lt_of_lt_of_le hj1_int.1 hj1ky
                exact absurd (hseq ▸ hs'le) (not_le_of_gt hky_gt)
          rcases branching_ancestors_comparable hInDeg hreach1 hreach2 with h12 | h21
          · exact hno_prop i1 hi1 i2 hi2 x1 x2 hgi1 hgi2 h12
          · exact (hno_prop i2 hi2 i1 hi1 x2 x1 hgi2 hgi1 h21).symm
      exact le_trans hfail_le_S hS_le_leaf
    -- Key Property 4: Sum over MaxFail, exclude prefix q and unembedded leaf z_max!
    have hfail_le_sum : fail.card ≤ ∑ b ∈ MaxFail, (fail.filter (fun j => a b < j ∧ j ≤ b)).card := by
      have hsub : fail ⊆ MaxFail.biUnion (fun b => fail.filter (fun j => a b < j ∧ j ≤ b)) := by
        intro j hj
        obtain ⟨b, hb, hab, hjb⟩ := hcover j hj
        refine Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hj, lt_of_le_of_lt hab (ha_lt j hj), hjb⟩⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have hsum_le_leaves : ∑ b ∈ MaxFail, (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card ≤
        (leafPos.filter (fun k => q ≤ k.val)).card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_le_card ?_
        intro k hk
        obtain ⟨b, hb, hkb⟩ := Finset.mem_biUnion.mp hk
        have hkl := (Finset.mem_filter.mp hkb).1
        have hkint := (Finset.mem_filter.mp hkb).2
        -- a b ≥ q because a b ∈ Q b has an unembedded child!
        have hab_ge_q : q ≤ (a b).val := by
          by_contra hltq
          have hb_f := (Finset.mem_filter.mp hb).1
          obtain ⟨_, u, hgu, c, hDc, _⟩ := (Finset.mem_filter.mp (ha_mem b hb_f)).2
          have h1 := hroots_g ⟨(a b).val, by omega⟩
          have hueq : u = roots ⟨(a b).val, by omega⟩ := Option.some.inj (hgu.symm.trans h1)
          subst hueq
          exact hpref ⟨(a b).val, by omega⟩ (by simpa using hltq) c hDc
        refine Finset.mem_filter.mpr ⟨hkl, ?_⟩
        have : (a b).val < k.val := hkint.1
        omega
      · intro b1 hb1 b2 hb2 hne
        exact (hdisj_max b1 hb1 b2 hb2 hne).mono
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩)
          (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩)
    -- Bound (leafPos.filter (q ≤ k.val)).card ≤ leaves.card - 1 - q!
    have hleaf_bound : (leafPos.filter (fun k => q ≤ k.val)).card + q + 1 ≤ leaves.card := by
      -- Map each k ∈ leafPos to its vertex in leaves, plus the q prefix roots, plus z_max!
      let L_used : Finset W := (leafPos.filter (fun k => q ≤ k.val)).image
        (fun k => if h : ∃ w ∈ leaves, g k = some w then Classical.choose h else z_max)
      let L_pref : Finset W := (Finset.univ : Finset (Fin q)).image (fun j => roots ⟨j.val, by omega⟩)
      have hcard_used : L_used.card = (leafPos.filter (fun k => q ≤ k.val)).card := by
        refine Finset.card_image_of_injOn ?_
        intro k1 hk1 k2 hk2 hEq
        have h1 : ∃ w ∈ leaves, g k1 = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk1).1).2
        have h2 : ∃ w ∈ leaves, g k2 = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk2).1).2
        simp only [h1, h2, ↓reduceDIte] at hEq
        have hg1' := (Classical.choose_spec h1).2
        have hg2' := (Classical.choose_spec h2).2
        exact hinj_g k1 k2 _ hg1' (hEq ▸ hg2')
      have hcard_pref : L_pref.card = q := by
        rw [Finset.card_image_of_injective]
        · exact Fintype.card_fin q
        · intro j1 j2 h
          exact Fin.ext (congrArg (fun z : Fin p => z.val) (hroots_inj h))
      have hdisj_up : Disjoint L_used L_pref := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw1
        obtain ⟨j, _, hjw⟩ := Finset.mem_image.mp hw2
        have h1 : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
        simp only [h1, ↓reduceDIte] at hjw
        have hgk := (Classical.choose_spec h1).2
        have hgj := hroots_g ⟨j.val, by omega⟩
        have hkj := hinj_g k ⟨j.val, by omega⟩ _ hgk (hjw.symm ▸ hgj)
        have hkq : q ≤ k.val := (Finset.mem_filter.mp hk).2
        have hjlt : j.val < q := j.isLt
        have : k.val = j.val := congrArg Fin.val hkj
        omega
      have hz_notin : z_max ∉ L_used ∪ L_pref := by
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h2
        · obtain ⟨k, hk, hkw⟩ := Finset.mem_image.mp h1
          have hex : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
          simp only [hex, ↓reduceDIte] at hkw
          exact hz_unemb k (hkw ▸ (Classical.choose_spec hex).2)
        · obtain ⟨j, _, hjw⟩ := Finset.mem_image.mp h2
          exact hz_unemb ⟨j.val, by omega⟩ (hjw ▸ hroots_g ⟨j.val, by omega⟩)
      have hsub_L : insert z_max (L_used ∪ L_pref) ⊆ leaves := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz_leaf⟩
        · rcases Finset.mem_union.mp hw' with h1 | h2
          · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h1
            have hex : ∃ w ∈ leaves, g k = some w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
            simp only [hex, ↓reduceDIte]
            exact (Classical.choose_spec hex).1
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref ⟨j.val, by omega⟩ j.isLt⟩
      have hc := Finset.card_le_card hsub_L
      rw [Finset.card_insert_of_notMem hz_notin, Finset.card_union_of_disjoint hdisj_up,
        hcard_used, hcard_pref] at hc
      omega
    have hfail_bound : fail.card + q + 1 ≤ leaves.card := by
      have hsum_step : ∑ b ∈ MaxFail, (fail.filter (fun j => a b < j ∧ j ≤ b)).card ≤
          ∑ b ∈ MaxFail, (leafPos.filter (fun k => a b < k ∧ k ≤ b)).card :=
        Finset.sum_le_sum hper_int
      omega
    have hemb_lt : emb.card < Fintype.card W := by
      have hsub : emb ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun h => by
        have : z_max ∈ emb := h ▸ Finset.mem_univ z_max
        obtain ⟨i, hi⟩ := (Finset.mem_filter.mp this).2
        exact hz_unemb i hi)
      simpa using Finset.card_lt_card hsub
    change Fintype.card W + leaves.card ≤ m + 1 + q at hm
    omega
  -- Step 3: Return g with all verified properties!
  refine ⟨g, hall_emb, hinj_g, hroots_g, ?_, ?_, ?_⟩
  · intro i j u v hgi hgj hDuv
    rcases hpar_g j v hgj with hltp | ⟨s, _, u', hgs', hDu', hGu'⟩
    · have h1 := hroots_g ⟨j.val, hltp⟩
      have hveq : v = roots ⟨j.val, hltp⟩ := Option.some.inj (hgj.symm.trans h1)
      exact absurd hDuv ((hroots_iff v).mpr ⟨⟨j.val, hltp⟩, hveq.symm⟩ u)
    · have hueq : u' = u := hInDeg v u' u hDu' hDuv
      subst u'
      have hseq : s = i := hinj_g s i u hgs' hgi
      exact hseq ▸ hGu'
  · intro i hip x hx
    rcases hpar_g i x hx with hlt | h
    · omega
    · exact h
  · intro i hip s0 hs0 u0 hgu0 C hC hCiff hGs0 hmin0
    have hsi' : eFin s0 < eFin i := by
      change (eFin s0).val < (eFin i).val; have : s0.val < i.val := hs0; simpa [eFin] using this
    have hGs0' : G.Adj (σ ⟨(eFin s0).val, by omega⟩) (σ ⟨(eFin i).val, by omega⟩) := by
      convert hGs0 using 2 <;> exact Fin.ext (by simp [eFin])
    refine hg6 (eFin i) (by simpa [eFin] using hip) (eFin s0) hsi' u0 hgu0 C hC (fun c => ?_) hGs0' ?_
    · rw [hCiff c]; constructor <;> rintro ⟨hD, hk⟩ <;> refine ⟨hD, fun k hki => ?_⟩
      · have hk' : eFin.symm k < i := by
          change (eFin.symm k).val < i.val; have : k.val < (eFin i).val := hki; simpa [eFin] using this
        simpa [g] using hk (eFin.symm k) hk'
      · have hk' : eFin k < eFin i := by
          change (eFin k).val < (eFin i).val; have : k.val < i.val := hki; simpa [eFin] using this
        exact hk (eFin k) hk'
    · intro s' hs' u' hgu' ⟨c', hDc', hc'⟩ hGs'
      have hs'lt : eFin.symm s' < s0 := by
        change (eFin.symm s').val < s0.val; have : s'.val < (eFin s0).val := hs'; simpa [eFin] using this
      have hGs'' : G.Adj (σ (eFin.symm s')) (σ i) := by
        convert hGs' using 2 <;> exact Fin.ext (by simp [eFin])
      refine hmin0 (eFin.symm s') hs'lt u' (by simpa [g] using hgu') ⟨c', hDc', fun k hk => ?_⟩ hGs''
      have hk' : eFin k < eFin i := by
        change (eFin k).val < (eFin i).val; have : k.val < i.val := hk; simpa [eFin] using this
      exact hc' (eFin k) hk'



-- Right-interval single-root out-arborescence with skip at lo + 2:
-- When u2, u3 are distinct out-leaf children of root u1 and ¬ G.Adj (σ lo) (σ (lo + 2)),
-- embeds D in [lo, lo + len) mapping u1 -> lo, u2 -> lo + 1, u3 -> lo + 3, leaving lo + 2 UNHIT!
lemma greedy_right_interval_skip2
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hRank : ∃ rank : W → ℕ, ∀ u v, D.Adj u v → rank u < rank v)
    (hInDeg : ∀ w u1 u2 : W, D.Adj u1 w → D.Adj u2 w → u1 = u2)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (lo len : ℕ) (hlen : lo + len ≤ Fintype.card V) (hlen4 : 4 ≤ len)
    (u1 u2 u3 : W) (hroot : ∀ w : W, (∀ u, ¬ D.Adj u w) ↔ w = u1)
    (h12 : D.Adj u1 u2) (h13 : D.Adj u1 u3) (h23 : u2 ≠ u3)
    (h2leaf : ∀ x : W, ¬ D.Adj u2 x) (h3leaf : ∀ x : W, ¬ D.Adj u3 x)
    (hnot02 : ¬ G.Adj (σ ⟨lo, by omega⟩) (σ ⟨lo + 2, by omega⟩))
    (hm : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      len + 1) :
    ∃ f : W → Fin (Fintype.card V),
      Function.Injective f ∧
      (∀ w : W, lo ≤ (f w).val ∧ (f w).val < lo + len) ∧
      (∀ u v : W, D.Adj u v → G.Adj (σ (f u)) (σ (f v))) ∧
      f u1 = ⟨lo, by omega⟩ ∧
      f u2 = ⟨lo + 1, by omega⟩ ∧
      (∀ w : W, f w ≠ ⟨lo + 2, by omega⟩) ∧
      f u3 = ⟨lo + 3, by omega⟩ := by
  classical
  let Gsub : Digraph (Fin len) := ⟨fun a b => G.Adj (σ ⟨lo + a.val, by omega⟩) (σ ⟨lo + b.val, by omega⟩)⟩
  let σsub : Fin (Fintype.card (Fin len)) ≃ Fin len := finCongr (Fintype.card_fin len)
  have hRsub : ∀ i j : Fin (Fintype.card (Fin len)), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
    intro i j hij
    let i' : Fin (Fintype.card V) := ⟨lo + i.val, by have := i.isLt; simp only [Fintype.card_fin] at this; omega⟩
    let j' : Fin (Fintype.card V) := ⟨lo + j.val, by have := j.isLt; simp only [Fintype.card_fin] at this; omega⟩
    have hij' : i' < j' := by change lo + i.val < lo + j.val; have : i.val < j.val := hij; omega
    have h := hR i' j' hij'
    have hdiff : j'.val - i'.val = j.val - i.val := by change (lo + j.val) - (lo + i.val) = j.val - i.val; omega
    have hcard : (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i' < k ∧ k ≤ j' ∧ G.Adj (σ i') (σ k))).card =
      (Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i < k ∧ k ≤ j ∧ Gsub.Adj (σsub i) (σsub k))).card := by
      refine Finset.card_bij (fun k hk => ⟨k.val - lo, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have h2 : k.val ≤ lo + j.val := hk.2.1
        have hjlt : j.val < len := by simpa using j.isLt
        rw [Fintype.card_fin]; omega⟩) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        have h1 : lo + i.val < k.val := hk.1
        have h2 : k.val ≤ lo + j.val := hk.2.1
        refine ⟨by change i.val < k.val - lo; omega, by change k.val - lo ≤ j.val; omega, ?_⟩
        dsimp only [Gsub, σsub, finCongr_apply, Fin.val_cast]
        have heq1 : (⟨lo + i.val, by omega⟩ : Fin (Fintype.card V)) = i' := rfl
        have heq2 : (⟨lo + (k.val - lo), by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext (by dsimp only; omega)
        simpa [heq1, heq2] using hk.2.2
      · intro k1 hk1 k2 hk2 hEq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
        have h1 : lo + i.val < k1.val := hk1.1
        have h2 : lo + i.val < k2.val := hk2.1
        have hv : k1.val - lo = k2.val - lo := congrArg Fin.val hEq
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        have hklt : k.val < len := by simpa using k.isLt
        refine ⟨⟨lo + k.val, by omega⟩, ?_, Fin.ext (by simp)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : i.val < k.val := hk.1
        have h2 : k.val ≤ j.val := hk.2.1
        refine ⟨by change lo + i.val < lo + k.val; omega,
          by change lo + k.val ≤ lo + j.val; omega, ?_⟩
        simpa [Gsub, σsub, i'] using hk.2.2
    rw [hdiff, hcard] at h
    exact h
  let pick : ∀ (_u : W) (C : Finset W), C.Nonempty → ↥C := fun _ C hC =>
    if h2 : u2 ∈ C then ⟨u2, h2⟩
    else if h3 : u3 ∈ C then ⟨u3, h3⟩
    else ⟨Classical.choose hC, Classical.choose_spec hC⟩
  have hm' : Fintype.card W + (Finset.univ.filter (fun w : W => ∀ u, ¬ D.Adj w u)).card ≤
      Fintype.card (Fin len) + 1 + 0 := by simpa using hm
  obtain ⟨g, hall, hinj, hroots, hadj, hpar, hdet⟩ := greedy_out_branching_embeds_pick D hRank hInDeg
    Gsub hRsub (fun (_ : Fin 1) => u1) (fun a b _ => Subsingleton.elim a b)
    (fun w => (hroot w).trans ⟨fun h => ⟨0, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩)
    (by simp; omega) 0 (by omega) (fun _ h => by omega) hm' pick
  have hcard_len : Fintype.card (Fin len) = len := Fintype.card_fin len
  let i0 : Fin (Fintype.card (Fin len)) := ⟨0, by omega⟩
  let i1 : Fin (Fintype.card (Fin len)) := ⟨1, by omega⟩
  let i2 : Fin (Fintype.card (Fin len)) := ⟨2, by omega⟩
  let i3 : Fin (Fintype.card (Fin len)) := ⟨3, by omega⟩
  have hg0 : g i0 = some u1 := hroots 0
  have hu1_ne2 : u1 ≠ u2 := by
    obtain ⟨rk, hrk⟩ := hRank; intro h; subst h; exact lt_irrefl _ (hrk u1 u1 h12)
  have hu1_ne3 : u1 ≠ u3 := by
    obtain ⟨rk, hrk⟩ := hRank; intro h; subst h; exact lt_irrefl _ (hrk u1 u1 h13)
  have hG01 : Gsub.Adj (σsub i0) (σsub i1) :=
    median_adj_succ hRsub i0 (by change (0 : ℕ) + 1 < Fintype.card (Fin len); omega)
  have hnotG02 : ¬ Gsub.Adj (σsub i0) (σsub i2) := by
    simpa [Gsub, σsub, i0, i2] using hnot02
  have hG03 : Gsub.Adj (σsub i0) (σsub i3) := by
    have hR03 := hRsub i0 i3 (by change (0 : ℕ) < 3; omega)
    have hdiff : i3.val - i0.val = 3 := rfl
    rw [hdiff] at hR03
    by_contra hnot03
    have hsub : Finset.univ.filter (fun k : Fin (Fintype.card (Fin len)) =>
        i0 < k ∧ k ≤ i3 ∧ Gsub.Adj (σsub i0) (σsub k)) ⊆ {i1} := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hk1 : 0 < k.val := hk.1
      have hk3 : k.val ≤ 3 := hk.2.1
      rcases (by omega : k.val = 1 ∨ k.val = 2 ∨ k.val = 3) with h1 | h2 | h3
      · exact Finset.mem_singleton.mpr (Fin.ext h1)
      · have hkeq : k = i2 := Fin.ext h2
        exact absurd (hkeq ▸ hk.2.2) hnotG02
      · have hkeq : k = i3 := Fin.ext h3
        exact absurd (hkeq ▸ hk.2.2) hnot03
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hc
    omega
  -- Trace g at i1, i2, i3!
  have hg1 : g i1 = some u2 := by
    let C1 := Finset.univ.filter (fun c : W => D.Adj u1 c ∧ ∀ k : Fin (Fintype.card (Fin len)), k < i1 → g k ≠ some c)
    have hu2C1 : u2 ∈ C1 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12, fun k hk hgk => ?_⟩
      have hk0 : k = i0 := Fin.ext (by change k.val < 1 at hk; change k.val = 0; omega)
      rw [hk0, hg0] at hgk; exact hu1_ne2 (Option.some.inj hgk)
    have hstep := hdet i1 (by change 1 ≤ 1; omega) i0 (by change (0 : ℕ) < 1; omega) u1 hg0
      C1 ⟨u2, hu2C1⟩ (fun c => by simp [C1]) hG01 (fun s' hs' => by have : s'.val < 0 := hs'; omega)
    have hpick1 : (pick u1 C1 ⟨u2, hu2C1⟩).1 = u2 := by simp [pick, hu2C1]
    rw [hpick1] at hstep; exact hstep
  have hg2 : g i2 = none := by
    cases h2 : g i2 with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨s, hsi2, u, hgs, hDux, hGsu⟩ := hpar i2 (by change 1 ≤ 2; omega) x h2
      have hslt : s.val < 2 := hsi2
      rcases (by omega : s.val = 0 ∨ s.val = 1) with hs0 | hs1
      · have hseq : s = i0 := Fin.ext hs0; subst hseq
        exact hnotG02 hGsu
      · have hseq : s = i1 := Fin.ext hs1; subst hseq
        rw [hg1] at hgs
        have hu2 : u = u2 := (Option.some.inj hgs).symm
        exact h2leaf x (hu2 ▸ hDux)
  have hg3 : g i3 = some u3 := by
    let C3 := Finset.univ.filter (fun c : W => D.Adj u1 c ∧ ∀ k : Fin (Fintype.card (Fin len)), k < i3 → g k ≠ some c)
    have hu2_notC3 : u2 ∉ C3 := fun h => (Finset.mem_filter.mp h).2.2 i1 (by change (1 : ℕ) < 3; omega) hg1
    have hu3C3 : u3 ∈ C3 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h13, fun k hk hgk => ?_⟩
      have hklt : k.val < 3 := hk
      rcases (by omega : k.val = 0 ∨ k.val = 1 ∨ k.val = 2) with h0 | h1 | h2
      · have hkeq : k = i0 := Fin.ext h0; rw [hkeq, hg0] at hgk; exact hu1_ne3 (Option.some.inj hgk)
      · have hkeq : k = i1 := Fin.ext h1; rw [hkeq, hg1] at hgk; exact h23 (Option.some.inj hgk)
      · have hkeq : k = i2 := Fin.ext h2; rw [hkeq, hg2] at hgk; cases hgk
    have hstep := hdet i3 (by change 1 ≤ 3; omega) i0 (by change (0 : ℕ) < 3; omega) u1 hg0
      C3 ⟨u3, hu3C3⟩ (fun c => by simp [C3]) hG03 (fun s' hs' => by have : s'.val < 0 := hs'; omega)
    have hpick3 : (pick u1 C3 ⟨u3, hu3C3⟩).1 = u3 := by simp [pick, hu2_notC3, hu3C3]
    rw [hpick3] at hstep; exact hstep
  -- Extract f : W → Fin (Fintype.card V)!
  choose idx hidx using hall
  refine ⟨fun w => ⟨lo + (idx w).val, by have := (idx w).isLt; omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w1 w2 h
    have hv : (idx w1).val = (idx w2).val := by have := congrArg Fin.val h; dsimp only at this; omega
    have hi : idx w1 = idx w2 := Fin.ext hv
    exact Option.some.inj ((hidx w1).symm.trans (hi ▸ hidx w2))
  · intro w; dsimp only; have := (idx w).isLt; exact ⟨by omega, by omega⟩
  · intro u v huv
    have hG := hadj (idx u) (idx v) u v (hidx u) (hidx v) huv
    simpa [Gsub, σsub] using hG
  · apply Fin.ext; dsimp only
    have := hinj (idx u1) i0 u1 (hidx u1) hg0
    have : (idx u1).val = 0 := congrArg Fin.val this; omega
  · apply Fin.ext; dsimp only
    have := hinj (idx u2) i1 u2 (hidx u2) hg1
    have : (idx u2).val = 1 := congrArg Fin.val this; omega
  · intro w hEq
    have hv : (idx w).val = 2 := by have := congrArg Fin.val hEq; dsimp only at this; omega
    have hi : idx w = i2 := Fin.ext hv
    have hw := hidx w; rw [hi, hg2] at hw; cases hw
  · apply Fin.ext; dsimp only
    have := hinj (idx u3) i3 u3 (hidx u3) hg3
    have : (idx u3).val = 3 := congrArg Fin.val this; omega

-- General connected-gate subtree lemma: if H ⊆ S is connected in T[H] and no edge crosses
-- between S \ H and Sᶜ, then T[S] is a tree!
lemma isTree_induce_of_connected_gate {W : Type*} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) {H S : Finset W} (hHS : H ⊆ S)
    {r : W} (hr : r ∈ H)
    (hH_conn : ∀ w (hw : w ∈ H), (T.induce (S : Set W)).Reachable ⟨r, hHS hr⟩ ⟨w, hHS hw⟩)
    (hgate : ∀ x ∈ S, x ∉ H → ∀ y ∉ S, ¬ T.Adj x y) :
    (T.induce (S : Set W)).IsTree := by
  classical
  refine ⟨?_, hT.isAcyclic.induce _⟩
  have : Nonempty S := ⟨⟨r, hHS hr⟩⟩
  refine SimpleGraph.Connected.mk (fun a b => ?_)
  have hreach_r : ∀ x : S, (T.induce (S : Set W)).Reachable ⟨r, hHS hr⟩ x := by
    intro x
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath r x.1
    -- Pick h ∈ H ∩ p.support minimizing (p.dropUntil h _).length!
    let Hsupp := H.filter (fun h => h ∈ p.support)
    have hHne : Hsupp.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hr, p.start_mem_support⟩⟩
    obtain ⟨h0, hh0_mem, hh0_min⟩ := Finset.exists_min_image Hsupp
      (fun h => if hm : h ∈ p.support then (p.dropUntil h hm).length else 0) hHne
    have hh0H : h0 ∈ H := (Finset.mem_filter.mp hh0_mem).1
    have hh0p : h0 ∈ p.support := (Finset.mem_filter.mp hh0_mem).2
    let q := p.dropUntil h0 hh0p
    have hqp : q.IsPath := hp.dropUntil hh0p
    -- Only vertex of q.support in H is h0!
    have hq_only_h0 : ∀ w ∈ q.support, w ∈ H → w = h0 := by
      intro w hwq hwH
      have hwp : w ∈ p.support := SimpleGraph.Walk.support_dropUntil_subset_support p hh0p hwq
      have hwHs : w ∈ Hsupp := Finset.mem_filter.mpr ⟨hwH, hwp⟩
      have hmin := hh0_min w hwHs
      simp only [hh0p, hwp, ↓reduceDIte] at hmin
      -- q.dropUntil w hwq has length <= q.length, with equality iff w = h0!
      have hdrop_eq : p.dropUntil w hwp = q.dropUntil w hwq := by
        have h1 : (p.dropUntil w hwp).IsPath := hp.dropUntil hwp
        have h2 : (q.dropUntil w hwq).IsPath := hqp.dropUntil hwq
        exact congrArg Subtype.val ((hT.isAcyclic.subsingleton_path w x.1).elim ⟨_, h1⟩ ⟨_, h2⟩)
      have hcat := SimpleGraph.Walk.take_spec q hwq
      have hlen_sum : (q.takeUntil w hwq).length + (q.dropUntil w hwq).length = q.length := by
        rw [← SimpleGraph.Walk.length_append, hcat]
      have hmin' : q.length ≤ (q.dropUntil w hwq).length := by rw [← hdrop_eq]; exact hmin
      have htake0 : (q.takeUntil w hwq).length = 0 := by omega
      exact (SimpleGraph.Walk.eq_of_length_eq_zero htake0).symm
    -- Every vertex on q lies in S!
    have hback : ∀ (a0 c0 : W) (q0 : T.Walk a0 c0), q0.IsPath → c0 ∈ S →
        (∀ w ∈ q0.support, w ∈ H → w = a0) → ∀ w ∈ q0.support, w ∈ S := by
      intro a0 c0 q0 hq0 hc0 hstart
      induction q0 with
      | nil =>
        intro w hw; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        exact hw ▸ hc0
      | @cons a1 b1 c1 hab q' ih =>
        have hq'p : q'.IsPath := hq0.of_cons
        have hnd : a1 ∉ q'.support := by
          have h := hq0.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at h
          exact h.1
        have hq'_noH : ∀ w ∈ q'.support, w ∉ H := fun w hw hwH =>
          hnd (hstart w (List.mem_cons_of_mem a1 hw) hwH ▸ hw)
        have hq'_S : ∀ w ∈ q'.support, w ∈ S :=
          ih hq'p hc0 (fun w hw hwH => absurd hwH (hq'_noH w hw))
        intro w hw
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
        rcases hw with hwa | hw'
        · rw [hwa]
          by_cases haH : a1 ∈ H
          · exact hHS haH
          · by_contra ha_notS
            exact hgate b1 (hq'_S b1 q'.start_mem_support) (hq'_noH b1 q'.start_mem_support) a1 ha_notS hab.symm
        · exact hq'_S w hw'
    have hqS : ∀ w ∈ q.support, w ∈ S := hback h0 x.1 q hqp x.2 hq_only_h0
    have hlift : ∀ (a1 c1 : W) (q0 : T.Walk a1 c1), (ha1 : a1 ∈ S) → (hc1 : c1 ∈ S) →
        (∀ w ∈ q0.support, w ∈ S) → (T.induce (S : Set W)).Reachable ⟨a1, ha1⟩ ⟨c1, hc1⟩ := by
      intro a1 c1 q0 ha1 hc1 hq0S
      induction q0 with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a2 b2 c2 hab q' ih =>
        have hbS : b2 ∈ S := hq0S b2 (List.mem_cons_of_mem a2 q'.start_mem_support)
        have hstep : (T.induce (S : Set W)).Adj ⟨a2, ha1⟩ ⟨b2, hbS⟩ := hab
        exact hstep.reachable.trans (ih hbS hc1 (fun w hw => hq0S w (List.mem_cons_of_mem a2 hw)))
    exact (hH_conn h0 hh0H).trans (hlift h0 x.1 q (hHS hh0H) x.2 hqS)
  exact (hreach_r a).symm.trans (hreach_r b)

-- Structural lemma for Heart h = 3 (covers both P_3^+: u1 -> u2 -> u3 and S_3^+: u1 -> u2, u1 -> u3)!
lemma heart_three_structure
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u1 u2 u3 : W) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3)
    (hH_adj : (D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3))
    (A : Finset W) (hu1A : u1 ∉ A) (hu2A : u2 ∉ A) (hu3A : u3 ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x) :
    let H : Finset W := {u1, u2, u3}
    let B : Finset W := Finset.univ \ (H ∪ A)
    -- (1) No arcs from A to H
    (∀ x ∈ A, ∀ h ∈ H, ¬ D.Adj x h) ∧
    -- (2) No arcs from H to B
    (∀ h ∈ H, ∀ y ∈ B, ¬ D.Adj h y) ∧
    -- (3) Acyclic rank on H ∪ A (for BOTH T^+ and F^+)
    (∃ rkP : ↥(H ∪ A) → ℕ, ∀ x y : ↥(H ∪ A), D.Adj x.1 y.1 → rkP x < rkP y) ∧
    -- (4) Acyclic reverse rank on H ∪ B (for F^-, i.e., arcs with tail in B)
    (∃ rkM : ↥(H ∪ B) → ℕ, ∀ x y : ↥(H ∪ B), x.1 ∈ B → D.Adj x.1 y.1 → rkM y < rkM x) ∧
    -- (5) Leaf count bound: |A_leaves| + |B_leaves| <= |Leaves(D)|
    (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
    (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤
    (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
  classical
  intro H B
  have hu1H : u1 ∈ H := by simp [H]
  have hu2H : u2 ∈ H := by simp [H]
  have hu3H : u3 ∈ H := by simp [H]
  have hSplus_tree : (T.induce ((H ∪ A : Finset W) : Set W)).IsTree := by
    refine isTree_induce_of_connected_gate hT Finset.subset_union_left hu1H ?_ ?_
    · intro h hh
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hH_adj with ⟨h12a, h23a⟩ | ⟨h12a, h13a⟩
      · have hr12 : (T.induce ((H ∪ A : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u2, Finset.mem_union_left _ hu2H⟩ := hO.1 u1 u2 h12a
        have hr23 : (T.induce ((H ∪ A : Finset W) : Set W)).Adj ⟨u2, Finset.mem_union_left _ hu2H⟩ ⟨u3, Finset.mem_union_left _ hu3H⟩ := hO.1 u2 u3 h23a
        rcases hh with rfl | rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact hr12.reachable
        · exact hr12.reachable.trans hr23.reachable
      · have hr12 : (T.induce ((H ∪ A : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u2, Finset.mem_union_left _ hu2H⟩ := hO.1 u1 u2 h12a
        have hr13 : (T.induce ((H ∪ A : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u3, Finset.mem_union_left _ hu3H⟩ := hO.1 u1 u3 h13a
        rcases hh with rfl | rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact hr12.reachable
        · exact hr13.reachable
    · intro x hx hxH y hyS hTxy
      have hxA : x ∈ A := (Finset.mem_union.mp hx).resolve_left hxH
      have hy1 : y ≠ u1 := fun h => hyS (Finset.mem_union_left _ (h ▸ hu1H))
      have hy2 : y ≠ u2 := fun h => hyS (Finset.mem_union_left _ (h ▸ hu2H))
      have hy3 : y ≠ u3 := fun h => hyS (Finset.mem_union_left _ (h ▸ hu3H))
      have hyA : y ∉ A := fun h => hyS (Finset.mem_union_right _ h)
      rcases adj_or_rev_of_isOrientation hO hTxy with h | h
      · exact (hno_AB x hxA y hy1 hy2 hy3 hyA).1 h
      · exact (hno_AB x hxA y hy1 hy2 hy3 hyA).2 h
  have hSminus_tree : (T.induce ((H ∪ B : Finset W) : Set W)).IsTree := by
    refine isTree_induce_of_connected_gate hT Finset.subset_union_left hu1H ?_ ?_
    · intro h hh
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hH_adj with ⟨h12a, h23a⟩ | ⟨h12a, h13a⟩
      · have hr12 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u2, Finset.mem_union_left _ hu2H⟩ := hO.1 u1 u2 h12a
        have hr23 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj ⟨u2, Finset.mem_union_left _ hu2H⟩ ⟨u3, Finset.mem_union_left _ hu3H⟩ := hO.1 u2 u3 h23a
        rcases hh with rfl | rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact hr12.reachable
        · exact hr12.reachable.trans hr23.reachable
      · have hr12 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u2, Finset.mem_union_left _ hu2H⟩ := hO.1 u1 u2 h12a
        have hr13 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj ⟨u1, Finset.mem_union_left _ hu1H⟩ ⟨u3, Finset.mem_union_left _ hu3H⟩ := hO.1 u1 u3 h13a
        rcases hh with rfl | rfl | rfl
        · exact SimpleGraph.Reachable.refl _
        · exact hr12.reachable
        · exact hr13.reachable
    · intro y hy hyH x hxS hTyx
      have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left hyH
      have hy_notHA : y ∉ H ∪ A := (Finset.mem_sdiff.mp hyB).2
      have hy1 : y ≠ u1 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu1H))
      have hy2 : y ≠ u2 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu2H))
      have hy3 : y ≠ u3 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu3H))
      have hyA : y ∉ A := fun h => hy_notHA (Finset.mem_union_right _ h)
      have hxA : x ∈ A := by
        by_contra hxnotA
        have hxH : x ∉ H := fun h => hxS (Finset.mem_union_left _ h)
        exact hxS (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
          (Finset.mem_union.mp h).elim hxH hxnotA⟩))
      rcases adj_or_rev_of_isOrientation hO hTyx with h | h
      · exact (hno_AB x hxA y hy1 hy2 hy3 hyA).2 h
      · exact (hno_AB x hxA y hy1 hy2 hy3 hyA).1 h
  -- Step 1: Analyze Dplus on H ∪ A via sum_indeg_eq_card_sub_one + out_arborescence_rank_and_root!
  let Dp : Digraph ↥(H ∪ A) := ⟨fun x y => D.Adj x.1 y.1⟩
  have hOp : Dp.IsOrientation (T.induce ((H ∪ A : Finset W) : Set W)) :=
    ⟨fun x y h => hO.1 x.1 y.1 h, fun x y h => hO.2 x.1 y.1 h⟩
  have hsum_p := sum_indeg_eq_card_sub_one hSplus_tree hOp
  have hA_in_p : ∀ x : ↥(H ∪ A), x.1 ∈ A → (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z x)).card = 1 := by
    intro x hxA
    have hbij : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z x)).card =
        (Finset.univ.filter (fun z : W => D.Adj z x.1)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDzx := (Finset.mem_filter.mp hz).2
        have hzHA : z ∈ H ∪ A := by
          by_contra hznot
          have hz1 : z ≠ u1 := fun h => hznot (Finset.mem_union_left _ (h ▸ hu1H))
          have hz2 : z ≠ u2 := fun h => hznot (Finset.mem_union_left _ (h ▸ hu2H))
          have hz3 : z ≠ u3 := fun h => hznot (Finset.mem_union_left _ (h ▸ hu3H))
          have hzA : z ∉ A := fun h => hznot (Finset.mem_union_right _ h)
          exact (hno_AB x.1 hxA z hz1 hz2 hz3 hzA).2 hDzx
        exact ⟨⟨z, hzHA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDzx⟩, rfl⟩
    rw [hbij]; exact hA_in x.1 hxA
  -- Both u2 and u3 have in-degree >= 1 in Dp!
  let u1p : ↥(H ∪ A) := ⟨u1, Finset.mem_union_left _ hu1H⟩
  let u2p : ↥(H ∪ A) := ⟨u2, Finset.mem_union_left _ hu2H⟩
  let u3p : ↥(H ∪ A) := ⟨u3, Finset.mem_union_left _ hu3H⟩
  have hu2_in_ge1 : 1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u2p)).card := by
    rcases hH_adj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact Finset.one_le_card.mpr ⟨u1p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have hu3_in_ge1 : 1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u3p)).card := by
    rcases hH_adj with ⟨_, h⟩ | ⟨_, h⟩
    · exact Finset.one_le_card.mpr ⟨u2p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    · exact Finset.one_le_card.mpr ⟨u1p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  -- Since sum over all w != u1p is >= Fintype.card - 1 = sum over all w, EVERY w != u1p has in-degree = 1 in Dp!
  have hall_in_p : ∀ w : ↥(H ∪ A), w ≠ u1p → (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card = 1 := by
    have hge1 : ∀ w ∈ (Finset.univ : Finset ↥(H ∪ A)).erase u1p,
        1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card := by
      intro w hw
      have hne1 : w ≠ u1p := (Finset.mem_erase.mp hw).1
      rcases Finset.mem_union.mp w.2 with hwH | hwA
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
        rcases hwH with h | h | h
        · exact absurd (Subtype.ext h) hne1
        · have : w = u2p := Subtype.ext h; exact this ▸ hu2_in_ge1
        · have : w = u3p := Subtype.ext h; exact this ▸ hu3_in_ge1
      · rw [hA_in_p w hwA]
    have hsum_er : ∑ w ∈ (Finset.univ : Finset ↥(H ∪ A)).erase u1p,
        (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card ≤ Fintype.card ↥(H ∪ A) - 1 := by
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset ↥(H ∪ A))
        (fun w => (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card) (Finset.mem_univ u1p)
      have hle : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u1p)).card +
          ∑ w ∈ (Finset.univ : Finset ↥(H ∪ A)).erase u1p,
            (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card = Fintype.card ↥(H ∪ A) - 1 :=
        hsplit.trans hsum_p
      omega
    have hcard_er : ((Finset.univ : Finset ↥(H ∪ A)).erase u1p).card = Fintype.card ↥(H ∪ A) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u1p), Finset.card_univ]
    intro w hwne
    have hw_er : w ∈ (Finset.univ : Finset ↥(H ∪ A)).erase u1p := Finset.mem_erase.mpr ⟨hwne, Finset.mem_univ _⟩
    have h1 := hge1 w hw_er
    have hrest : ((Finset.univ : Finset ↥(H ∪ A)).erase u1p).card - 1 ≤
        ∑ w' ∈ ((Finset.univ : Finset ↥(H ∪ A)).erase u1p).erase w,
          (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w')).card := by
      calc _ = (((Finset.univ : Finset ↥(H ∪ A)).erase u1p).erase w).card := (Finset.card_erase_of_mem hw_er).symm
        _ = ∑ _w' ∈ ((Finset.univ : Finset ↥(H ∪ A)).erase u1p).erase w, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun w' hw' => hge1 w' (Finset.mem_erase.mp hw').2)
    rw [← Finset.add_sum_erase _ _ hw_er] at hsum_er
    omega
  obtain ⟨hu1p_noin, hDp_uniq, hDp_rank⟩ := out_arborescence_rank_and_root hSplus_tree hOp u1p hall_in_p
  -- Consequence (1): NO arc from A to H!
  have hno_AH : ∀ x ∈ A, ∀ h ∈ H, ¬ D.Adj x h := by
    intro x hxA h hh hDxh
    have hxp : x ∈ H ∪ A := Finset.mem_union_right _ hxA
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · subst hh; exact hu1p_noin ⟨x, hxp⟩ hDxh
    · subst hh
      rcases hH_adj with ⟨h12a, _⟩ | ⟨h12a, _⟩
      · have hxeq : x = u1 := congrArg Subtype.val (hDp_uniq u2p ⟨x, hxp⟩ u1p hDxh h12a)
        exact hu1A (hxeq ▸ hxA)
      · have hxeq : x = u1 := congrArg Subtype.val (hDp_uniq u2p ⟨x, hxp⟩ u1p hDxh h12a)
        exact hu1A (hxeq ▸ hxA)
    · subst hh
      rcases hH_adj with ⟨_, h23a⟩ | ⟨_, h13a⟩
      · have hxeq : x = u2 := congrArg Subtype.val (hDp_uniq u3p ⟨x, hxp⟩ u2p hDxh h23a)
        exact hu2A (hxeq ▸ hxA)
      · have hxeq : x = u1 := congrArg Subtype.val (hDp_uniq u3p ⟨x, hxp⟩ u1p hDxh h13a)
        exact hu1A (hxeq ▸ hxA)
  -- Step 2: Analyze H ∪ B by re-orienting ONLY the 2 edges of H to point into u1!
  let u1m : ↥(H ∪ B) := ⟨u1, Finset.mem_union_left _ hu1H⟩
  let u2m : ↥(H ∪ B) := ⟨u2, Finset.mem_union_left _ hu2H⟩
  let u3m : ↥(H ∪ B) := ⟨u3, Finset.mem_union_left _ hu3H⟩
  let Dm_tmp : Digraph ↥(H ∪ B) := ⟨fun x y =>
    if x.1 ∈ H ∧ y.1 ∈ H then
      (T.Adj x.1 y.1) ∧ (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m y <
        (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m x
    else D.Adj x.1 y.1⟩
  let Dm_rev : Digraph ↥(H ∪ B) := ⟨fun x y => Dm_tmp.Adj y x⟩
  have hOm_rev : Dm_rev.IsOrientation (T.induce ((H ∪ B : Finset W) : Set W)) := by
    refine ⟨fun x y h => ?_, fun x y hTxy => ?_⟩
    · dsimp only [Dm_rev, Dm_tmp] at h
      split_ifs at h
      · exact h.1.symm
      · exact (hO.1 y.1 x.1 h).symm
    · dsimp only [Dm_rev, Dm_tmp]
      by_cases hxyH : y.1 ∈ H ∧ x.1 ∈ H
      · have hyxH : x.1 ∈ H ∧ y.1 ∈ H := ⟨hxyH.2, hxyH.1⟩
        rw [if_pos hxyH, if_pos hyxH]
        have hdist := hSminus_tree.dist_eq_dist_add_one_of_adj u1m hTxy
        constructor
        · intro h1 h2; have := h1.2; have := h2.2; omega
        · intro h1; refine ⟨hTxy.symm, ?_⟩
          rcases hdist with hd | hd
          · exact absurd ⟨hTxy, by omega⟩ h1
          · omega
      · have hyxH : ¬ (x.1 ∈ H ∧ y.1 ∈ H) := fun h => hxyH ⟨h.2, h.1⟩
        rw [if_neg hxyH, if_neg hyxH]
        exact hO.2 y.1 x.1 hTxy.symm
  have hsum_m := sum_indeg_eq_card_sub_one hSminus_tree hOm_rev
  have hB_in_m : ∀ y : ↥(H ∪ B), y.1 ∈ B → (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z y)).card = 1 := by
    intro y hyB
    have hy_notHA := (Finset.mem_sdiff.mp hyB).2
    have hy1 : y.1 ≠ u1 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu1H))
    have hy2 : y.1 ≠ u2 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu2H))
    have hy3 : y.1 ≠ u3 := fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu3H))
    have hyA : y.1 ∉ A := fun h => hy_notHA (Finset.mem_union_right _ h)
    have hy_notH : y.1 ∉ H := fun h => hy_notHA (Finset.mem_union_left _ h)
    have hbij : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z y)).card =
        (Finset.univ.filter (fun z : W => D.Adj y.1 z)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz
        have h := (Finset.mem_filter.mp hz).2
        simp only [Dm_rev, Dm_tmp, hy_notH, false_and, ↓reduceIte] at h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDyz := (Finset.mem_filter.mp hz).2
        have hzHB : z ∈ H ∪ B := by
          by_contra hznot
          have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
          have hzA : z ∈ A := by
            by_contra hnotA
            exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
              (Finset.mem_union.mp h).elim hzH hnotA⟩))
          exact (hno_AB z hzA y.1 hy1 hy2 hy3 hyA).2 hDyz
        refine ⟨⟨z, hzHB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        simp only [Dm_rev, Dm_tmp, hy_notH, false_and, ↓reduceIte]; exact hDyz
    rw [hbij]; exact hB_out y.1 hy1 hy2 hy3 hyA
  have h12m : Dm_rev.Adj u1m u2m := by
    have hT12 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj u1m u2m := by
      rcases hH_adj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact hO.1 u1 u2 h
    dsimp only [Dm_rev, Dm_tmp]
    rw [if_pos ⟨hu2H, hu1H⟩]
    have h0 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u1m = 0 := SimpleGraph.dist_self
    have hd := hSminus_tree.dist_eq_dist_add_one_of_adj u1m hT12
    exact ⟨hT12.symm, by rcases hd with h | h <;> omega⟩
  have h3in_m : ∃ z : ↥(H ∪ B), z.1 ∈ H ∧ Dm_rev.Adj z u3m := by
    rcases hH_adj with ⟨h12a, h23a⟩ | ⟨_, h13a⟩
    · have hT12 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj u1m u2m := hO.1 u1 u2 h12a
      have hT23 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj u2m u3m := hO.1 u2 u3 h23a
      have hd12 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u2m = 1 := by
        have h0 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u1m = 0 := SimpleGraph.dist_self
        rcases hSminus_tree.dist_eq_dist_add_one_of_adj u1m hT12 with h | h <;> omega
      have hd13 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u3m = 2 := by
        rcases hSminus_tree.dist_eq_dist_add_one_of_adj u1m hT23 with h | h
        · exfalso
          have h0 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u3m = 0 := by omega
          have heq : u1m = u3m := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
            (not_not.mpr (hSminus_tree.connected u1m u3m))
          exact h13 (congrArg Subtype.val heq)
        · omega
      refine ⟨u2m, hu2H, ?_⟩
      dsimp only [Dm_rev, Dm_tmp]; rw [if_pos ⟨hu3H, hu2H⟩]
      exact ⟨hT23.symm, by omega⟩
    · have hT13 : (T.induce ((H ∪ B : Finset W) : Set W)).Adj u1m u3m := hO.1 u1 u3 h13a
      refine ⟨u1m, hu1H, ?_⟩
      dsimp only [Dm_rev, Dm_tmp]; rw [if_pos ⟨hu3H, hu1H⟩]
      have h0 : (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m u1m = 0 := SimpleGraph.dist_self
      rcases hSminus_tree.dist_eq_dist_add_one_of_adj u1m hT13 with h | h <;> exact ⟨hT13.symm, by omega⟩
  have hu2m_ge1 : 1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z u2m)).card :=
    Finset.one_le_card.mpr ⟨u1m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12m⟩⟩
  have hu3m_ge1 : 1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z u3m)).card := by
    obtain ⟨z, _, hzm⟩ := h3in_m
    exact Finset.one_le_card.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzm⟩⟩
  have hall_in_m : ∀ w : ↥(H ∪ B), w ≠ u1m → (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w)).card = 1 := by
    have hge1 : ∀ w ∈ (Finset.univ : Finset ↥(H ∪ B)).erase u1m,
        1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w)).card := by
      intro w hw
      have hne1 : w ≠ u1m := (Finset.mem_erase.mp hw).1
      rcases Finset.mem_union.mp w.2 with hwH | hwB
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
        rcases hwH with h | h | h
        · exact absurd (Subtype.ext h) hne1
        · have : w = u2m := Subtype.ext h; exact this ▸ hu2m_ge1
        · have : w = u3m := Subtype.ext h; exact this ▸ hu3m_ge1
      · rw [hB_in_m w hwB]
    have hsum_er : ∑ w ∈ (Finset.univ : Finset ↥(H ∪ B)).erase u1m,
        (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w)).card ≤ Fintype.card ↥(H ∪ B) - 1 := by
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset ↥(H ∪ B))
        (fun w => (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w)).card) (Finset.mem_univ u1m)
      have hle : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z u1m)).card +
          ∑ w ∈ (Finset.univ : Finset ↥(H ∪ B)).erase u1m,
            (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w)).card = Fintype.card ↥(H ∪ B) - 1 :=
        hsplit.trans hsum_m
      omega
    have hcard_er : ((Finset.univ : Finset ↥(H ∪ B)).erase u1m).card = Fintype.card ↥(H ∪ B) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u1m), Finset.card_univ]
    intro w hwne
    have hw_er : w ∈ (Finset.univ : Finset ↥(H ∪ B)).erase u1m := Finset.mem_erase.mpr ⟨hwne, Finset.mem_univ _⟩
    have h1 := hge1 w hw_er
    have hrest : ((Finset.univ : Finset ↥(H ∪ B)).erase u1m).card - 1 ≤
        ∑ w' ∈ ((Finset.univ : Finset ↥(H ∪ B)).erase u1m).erase w,
          (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm_rev.Adj z w')).card := by
      calc _ = (((Finset.univ : Finset ↥(H ∪ B)).erase u1m).erase w).card := (Finset.card_erase_of_mem hw_er).symm
        _ = ∑ _w' ∈ ((Finset.univ : Finset ↥(H ∪ B)).erase u1m).erase w, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun w' hw' => hge1 w' (Finset.mem_erase.mp hw').2)
    rw [← Finset.add_sum_erase _ _ hw_er] at hsum_er
    omega
  obtain ⟨hu1m_noin, hDm_uniq, hDm_rank⟩ := out_arborescence_rank_and_root hSminus_tree hOm_rev u1m hall_in_m
  -- Consequence (2): NO arc from H to B!
  have hno_HB : ∀ h ∈ H, ∀ y ∈ B, ¬ D.Adj h y := by
    intro h hh y hyB hDhy
    have hy_notH : y ∉ H := fun hyH => (Finset.mem_sdiff.mp hyB).2 (Finset.mem_union_left _ hyH)
    have hhm : h ∈ H ∪ B := Finset.mem_union_left _ hh
    have hym : y ∈ H ∪ B := Finset.mem_union_right _ hyB
    have hDm : Dm_rev.Adj ⟨y, hym⟩ ⟨h, hhm⟩ := by
      simp only [Dm_rev, Dm_tmp, hy_notH, and_false, ↓reduceIte]; exact hDhy
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · subst hh; exact hu1m_noin ⟨y, hym⟩ hDm
    · subst hh
      have hyeq : y = u1 := congrArg Subtype.val (hDm_uniq u2m ⟨y, hym⟩ u1m hDm h12m)
      exact hy_notH (hyeq ▸ hu1H)
    · subst hh
      obtain ⟨z, hzH, hzm⟩ := h3in_m
      have hyeq : y = z.1 := congrArg Subtype.val (hDm_uniq u3m ⟨y, hym⟩ z hDm hzm)
      exact hy_notH (hyeq ▸ hzH)
  -- Consequence (5): Leaf count bound!
  have hleaves_le : (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
      (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤
      (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
    have hdisj_AB : Disjoint (A.filter (fun x => ∀ z : W, ¬ D.Adj x z))
        (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)) :=
      Finset.disjoint_left.mpr (fun w hw1 hw2 =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw2).1).2 (Finset.mem_union_right _ (Finset.mem_filter.mp hw1).1))
    rw [← Finset.card_union_of_disjoint hdisj_AB]
    refine Finset.card_le_card (fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    rcases Finset.mem_union.mp hw with hwA | hwB
    · have hwA' := Finset.mem_filter.mp hwA
      have hfeq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj z w) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_left (hwA'.2 z), fun h => Or.inr h⟩
      rw [hfeq]; exact hA_in w hwA'.1
    · have hwB' := Finset.mem_filter.mp hwB
      have hy_notHA := (Finset.mem_sdiff.mp hwB'.1).2
      have hfeq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj w z) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_right (hwB'.2 z), fun h => Or.inl h⟩
      rw [hfeq]
      exact hB_out w (fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
        (fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
        (fun h => hy_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
        (fun h => hy_notHA (Finset.mem_union_right _ h))
  refine ⟨hno_AH, hno_HB,
    ⟨fun x => (T.induce ((H ∪ A : Finset W) : Set W)).dist u1p x, hDp_rank⟩,
    ⟨fun x => (T.induce ((H ∪ B : Finset W) : Set W)).dist u1m x, fun x y hxB hDxy => ?_⟩,
    hleaves_le⟩
  have hx_notH : x.1 ∉ H := fun h => (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_left _ h)
  exact hDm_rank y x (by simp only [Dm_rev, Dm_tmp, hx_notH, false_and, ↓reduceIte]; exact hDxy)

-- Heart h = 3, Topology 1: H = P_3^+ (u1 -> u2 -> u3)!
lemma embeds_heart_three_P3plus {n : ℕ} (hn : 4 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hInt4 : 4 ≤ n - (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card)
    (u1 u2 u3 : W) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3)
    (hD12 : D.Adj u1 u2) (hD23 : D.Adj u2 u3)
    (A : Finset W) (hu1A : u1 ∉ A) (hu2A : u2 ∉ A) (hu3A : u3 ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hTree
  let H : Finset W := {u1, u2, u3}
  let B : Finset W := Finset.univ \ (H ∪ A)
  have hu1H : u1 ∈ H := by simp [H]
  have hu2H : u2 ∈ H := by simp [H]
  have hu3H : u3 ∈ H := by simp [H]
  obtain ⟨hno_AH, hno_HB, ⟨rkP, hrkP⟩, ⟨rkM, hrkM⟩, hleaves_le⟩ :=
    heart_three_structure D hT hO u1 u2 u3 h12 h13 h23 (Or.inl ⟨hD12, hD23⟩) A hu1A hu2A hu3A hA_in hB_out hno_AB
  -- Tree acyclicity: no edge between u1 and u3!
  have hno_13 : ¬ D.Adj u1 u3 ∧ ¬ D.Adj u3 u1 := by
    have hnoT : ¬ T.Adj u1 u3 := by
      intro hT13
      let p1 : T.Walk u1 u3 := SimpleGraph.Walk.cons hT13 SimpleGraph.Walk.nil
      let p2 : T.Walk u1 u3 := SimpleGraph.Walk.cons (hO.1 u1 u2 hD12)
        (SimpleGraph.Walk.cons (hO.1 u2 u3 hD23) SimpleGraph.Walk.nil)
      have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h13])
      have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.cons
        (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h23])) (by simp [h12, h13])
      have heq := congrArg (fun p : T.Walk u1 u3 => p.length)
        (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u1 u3).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
      simp [p1, p2] at heq
    exact ⟨fun h => hnoT (hO.1 u1 u3 h), fun h => hnoT (hO.1 u3 u1 h).symm⟩
  -- If u1 has no child in A, u1 merges into B -> Heart h = 2 ({u2, u3}, A)!
  by_cases hu1_out : ∃ x ∈ A, D.Adj u1 x
  · -- If u3 has no in-neighbor in B, u3 merges into A -> Heart h = 2 ({u1, u2}, insert u3 A)!
    by_cases hu3_in : ∃ y ∈ B, D.Adj y u3
    · -- Genuine P_3^+ with n_1^+ >= 1 and n_3^- >= 1!
      obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
      let Sp := H ∪ A
      let Sm := H ∪ B
      have hH_card : H.card = 3 := by
        simp only [H, Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
          h12, h13, h23, or_self, not_false_eq_true, Finset.card_singleton]
      have hdisj_HA : Disjoint H A := Finset.disjoint_left.mpr (fun w hwH hwA => by
        simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
        rcases hwH with rfl | rfl | rfl <;> contradiction)
      have hdisj_HB : Disjoint H B := Finset.disjoint_left.mpr (fun w hwH hwB =>
        (Finset.mem_sdiff.mp hwB).2 (Finset.mem_union_left _ hwH))
      have hSp_card : Sp.card = 3 + A.card := by rw [Finset.card_union_of_disjoint hdisj_HA, hH_card]
      have hSm_card : Sm.card = 3 + B.card := by rw [Finset.card_union_of_disjoint hdisj_HB, hH_card]
      have hAB_sum : 3 + A.card + B.card = n := by
        have h1 : B.card + Sp.card = n := by
          have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (H ∪ A))
          rw [Finset.card_univ, hW] at this; exact this
        omega
      let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
      let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
      have hkAB_le : kA + kB ≤ (Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := hleaves_le
      -- 3-root out-branching Fp on Sp (keep only arcs into A)!
      let Fp : Digraph ↥Sp := ⟨fun x y => y.1 ∈ A ∧ D.Adj x.1 y.1⟩
      let u1p : ↥Sp := ⟨u1, Finset.mem_union_left _ hu1H⟩
      let u2p : ↥Sp := ⟨u2, Finset.mem_union_left _ hu2H⟩
      let u3p : ↥Sp := ⟨u3, Finset.mem_union_left _ hu3H⟩
      let rootsP : Fin 3 → ↥Sp := fun j => match j.val with | 0 => u1p | 1 => u2p | _ => u3p
      have hFp_indeg : ∀ w x1 x2 : ↥Sp, Fp.Adj x1 w → Fp.Adj x2 w → x1 = x2 := by
        intro w x1 x2 h1 h2
        have hcard1 := hA_in w.1 h1.1
        exact Subtype.ext (Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj z w.1)).card ≤ 1)
          x1.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2⟩)
          x2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2⟩))
      have hFp_roots : ∀ w : ↥Sp, (∀ u : ↥Sp, ¬ Fp.Adj u w) ↔ ∃ j : Fin 3, rootsP j = w := by
        intro w; constructor
        · intro hno
          rcases Finset.mem_union.mp w.2 with hwH | hwA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
            rcases hwH with h | h | h
            · exact ⟨⟨0, by decide⟩, by dsimp only [rootsP, u1p]; exact Subtype.ext h.symm⟩
            · exact ⟨⟨1, by decide⟩, by dsimp only [rootsP, u2p]; exact Subtype.ext h.symm⟩
            · exact ⟨⟨2, by decide⟩, by dsimp only [rootsP, u3p]; exact Subtype.ext h.symm⟩
          · exfalso
            obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [hA_in w.1 hwA]; omega :
              0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card)
            have hDzw := (Finset.mem_filter.mp hz).2
            have hzSp : z ∈ Sp := by
              by_contra hznot
              exact (hno_AB w.1 hwA z (fun h => hznot (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hznot (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hznot (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hznot (Finset.mem_union_right _ h))).2 hDzw
            exact hno ⟨z, hzSp⟩ ⟨hwA, hDzw⟩
        · rintro ⟨j, rfl⟩ u hu
          have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
          rcases hj with h | h | h <;> simp only [rootsP, h] at hu
          · exact hu1A hu.1
          · exact hu2A hu.1
          · exact hu3A hu.1
      have hFp_leaves : (Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp.Adj x y)).card ≤ kA + 2 := by
        let Lsub : Finset ↥Sp := (Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)) ∪ {u2p, u3p}
        have hsub : Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp.Adj x y) ⊆ Lsub := by
          intro x hx
          have hno := (Finset.mem_filter.mp hx).2
          rcases Finset.mem_union.mp x.2 with hxH | hxA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h | h | h
            · exfalso; obtain ⟨a, haA, hDa⟩ := hu1_out
              exact hno ⟨a, Finset.mem_union_right _ haA⟩ ⟨haA, h ▸ hDa⟩
            · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
            · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, fun z hDxz => ?_⟩)
            have hzA : z ∈ A := by
              by_contra hznotA
              by_cases hzH : z ∈ H
              · exact hno_AH x.1 hxA z hzH hDxz
              · exact (hno_AB x.1 hxA z (fun h => hzH (h ▸ hu1H)) (fun h => hzH (h ▸ hu2H))
                  (fun h => hzH (h ▸ hu3H)) hznotA).1 hDxz
            exact hno ⟨z, Finset.mem_union_right _ hzA⟩ ⟨hzA, hDxz⟩
        have hcardA : (Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)).card = kA := by
          refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
          · intro x hx; exact Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro w hw; have hw' := Finset.mem_filter.mp hw
            exact ⟨⟨w, Finset.mem_union_right _ hw'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'⟩, rfl⟩
        have hc1 : (Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp.Adj x y)).card ≤
            ((Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)) ∪ ({u2p, u3p} : Finset ↥Sp)).card :=
          Finset.card_le_card hsub
        have hc2 := Finset.card_union_le (Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)) ({u2p, u3p} : Finset ↥Sp)
        have hc3 : ({u2p, u3p} : Finset ↥Sp).card ≤ 2 := Finset.card_le_two
        omega
      -- 3-root in-branching Fm on Sm (keep only arcs from B)!
      let Fm : Digraph ↥Sm := ⟨fun x y => x.1 ∈ B ∧ D.Adj x.1 y.1⟩
      let u1m : ↥Sm := ⟨u1, Finset.mem_union_left _ hu1H⟩
      let u2m : ↥Sm := ⟨u2, Finset.mem_union_left _ hu2H⟩
      let u3m : ↥Sm := ⟨u3, Finset.mem_union_left _ hu3H⟩
      let rootsM : Fin 3 → ↥Sm := fun j => match j.val with | 0 => u3m | 1 => u2m | _ => u1m
      have hFm_outdeg : ∀ w y1 y2 : ↥Sm, Fm.Adj w y1 → Fm.Adj w y2 → y1 = y2 := by
        intro w y1 y2 h1 h2
        have hw_notHA := (Finset.mem_sdiff.mp h1.1).2
        have hcard1 := hB_out w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hw_notHA (Finset.mem_union_right _ h))
        exact Subtype.ext (Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj w.1 z)).card ≤ 1)
          y1.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2⟩)
          y2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2⟩))
      have hFm_roots : ∀ w : ↥Sm, (∀ u : ↥Sm, ¬ Fm.Adj w u) ↔ ∃ j : Fin 3, rootsM j = w := by
        intro w; constructor
        · intro hno
          rcases Finset.mem_union.mp w.2 with hwH | hwB
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
            rcases hwH with h | h | h
            · exact ⟨⟨2, by decide⟩, by dsimp only [rootsM, u1m]; exact Subtype.ext h.symm⟩
            · exact ⟨⟨1, by decide⟩, by dsimp only [rootsM, u2m]; exact Subtype.ext h.symm⟩
            · exact ⟨⟨0, by decide⟩, by dsimp only [rootsM, u3m]; exact Subtype.ext h.symm⟩
          · exfalso
            have hw_notHA := (Finset.mem_sdiff.mp hwB).2
            have hcard1 := hB_out w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hw_notHA (Finset.mem_union_right _ h))
            obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => D.Adj w.1 z)).card)
            have hDwz := (Finset.mem_filter.mp hz).2
            have hzSm : z ∈ Sm := by
              by_contra hznot
              have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
              have hzA : z ∈ A := by
                by_contra hnotA
                exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
                  (Finset.mem_union.mp h).elim hzH hnotA⟩))
              exact (hno_AB z hzA w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hw_notHA (Finset.mem_union_right _ h))).2 hDwz
            exact hno ⟨z, hzSm⟩ ⟨hwB, hDwz⟩
        · rintro ⟨j, rfl⟩ u hu
          have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
          rcases hj with h | h | h <;> simp only [rootsM, h] at hu
          · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu3H)
          · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu2H)
          · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu1H)
      have hFm_leaves : (Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x)).card ≤ kB + 2 := by
        let Lsub : Finset ↥Sm := (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ∪ {u1m, u2m}
        have hsub : Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x) ⊆ Lsub := by
          intro x hx
          have hno := (Finset.mem_filter.mp hx).2
          rcases Finset.mem_union.mp x.2 with hxH | hxB
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h | h | h
            · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
            · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
            · exfalso; obtain ⟨b, hbB, hDb⟩ := hu3_in
              exact hno ⟨b, Finset.mem_union_right _ hbB⟩ ⟨hbB, h ▸ hDb⟩
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxB, fun z hDzx => ?_⟩)
            have hzB : z ∈ B := by
              by_contra hznotB
              by_cases hzH : z ∈ H
              · exact hno_HB z hzH x.1 hxB hDzx
              · have hzA : z ∈ A := by
                  by_contra hnotA; exact hznotB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩)
                have hx_notHA := (Finset.mem_sdiff.mp hxB).2
                exact (hno_AB z hzA x.1 (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                  (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                  (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                  (fun h => hx_notHA (Finset.mem_union_right _ h))).1 hDzx
            exact hno ⟨z, Finset.mem_union_right _ hzB⟩ ⟨hzB, hDzx⟩
        have hcardB : (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)).card = kB := by
          refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
          · intro x hx; exact Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro w hw; have hw' := Finset.mem_filter.mp hw
            exact ⟨⟨w, Finset.mem_union_right _ hw'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'⟩, rfl⟩
        have hc1 : (Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x)).card ≤
            ((Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ∪ ({u1m, u2m} : Finset ↥Sm)).card :=
          Finset.card_le_card hsub
        have hc2 := Finset.card_union_le (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ({u1m, u2m} : Finset ↥Sm)
        have hc3 : ({u1m, u2m} : Finset ↥Sm).card ≤ 2 := Finset.card_le_two
        omega
      -- Embed Fp on [r, r + lenR) and Fm on [0, r + 2]!
      let lenL := 4 + B.card + kB
      let lenR := 4 + A.card + kA
      let r := 1 + B.card + kB
      have htot_le : r + lenR ≤ Fintype.card V := by omega
      have hFp_roots_inj : Function.Injective rootsP := by
        intro j1 j2 h
        have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 := by omega
        have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 := by omega
        rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
          simp only [rootsP, h1, h2] at h
        · exact Fin.ext (by omega)
        · exact absurd (congrArg Subtype.val h) h12
        · exact absurd (congrArg Subtype.val h) h13
        · exact absurd (congrArg Subtype.val h).symm h12
        · exact Fin.ext (by omega)
        · exact absurd (congrArg Subtype.val h) h23
        · exact absurd (congrArg Subtype.val h).symm h13
        · exact absurd (congrArg Subtype.val h).symm h23
        · exact Fin.ext (by omega)
      have hFm_roots_inj : Function.Injective rootsM := by
        intro j1 j2 h
        have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 := by omega
        have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 := by omega
        rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
          simp only [rootsM, h1, h2] at h
        · exact Fin.ext (by omega)
        · exact absurd (congrArg Subtype.val h).symm h23
        · exact absurd (congrArg Subtype.val h).symm h13
        · exact absurd (congrArg Subtype.val h) h23
        · exact Fin.ext (by omega)
        · exact absurd (congrArg Subtype.val h).symm h12
        · exact absurd (congrArg Subtype.val h) h13
        · exact absurd (congrArg Subtype.val h) h12
        · exact Fin.ext (by omega)
      obtain ⟨fR, hfR_inj, hfR_rng, hfR_adj, hfR_rt⟩ := greedy_right_interval Fp
        ⟨rkP, fun x y h => hrkP x y h.2⟩ hFp_indeg G hR r lenR htot_le
        rootsP hFp_roots_inj hFp_roots (by omega) 0 (by omega) (fun _ h => by omega)
        (by rw [Fintype.card_coe, hSp_card]; omega)
      obtain ⟨fL, hfL_inj, hfL_rng, hfL_adj, hfL_rt⟩ := greedy_left_interval Fm
        ⟨rkM, fun x y h => hrkM x y h.1 h.2⟩ hFm_outdeg G hL (r + 2) lenL (by omega) (by omega)
        rootsM hFm_roots_inj hFm_roots (by omega) 0 (by omega) (fun _ h => by omega)
        (by rw [Fintype.card_coe, hSm_card]; omega)
      have hfRu1 : fR u1p = ⟨r, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨0, by omega⟩
      have hfRu2 : fR u2p = ⟨r + 1, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨1, by omega⟩
      have hfRu3 : fR u3p = ⟨r + 2, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨2, by omega⟩
      have hfLu3 : fL u3m = ⟨r + 2, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨0, by omega⟩
      have hfLu2 : fL u2m = ⟨r + 1, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨1, by omega⟩
      have hfLu1 : fL u1m = ⟨r, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨2, by omega⟩
      -- Glue fR (on Sp) and fL (on B)!
      let idx : W → Fin (Fintype.card V) := fun w =>
        if hw : w ∈ Sp then fR ⟨w, hw⟩ else fL ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)⟩
      have hidx_Sm : ∀ w (hw : w ∈ Sm), idx w = fL ⟨w, hw⟩ := by
        intro w hw
        by_cases hwSp : w ∈ Sp
        · simp only [idx, hwSp, ↓reduceDIte]
          have hwH : w ∈ H := by
            rcases Finset.mem_union.mp hw with h | hB
            · exact h
            · exact absurd hwSp (Finset.mem_sdiff.mp hB).2
          simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
          rcases hwH with rfl | rfl | rfl
          · exact hfRu1.trans hfLu1.symm
          · exact hfRu2.trans hfLu2.symm
          · exact hfRu3.trans hfLu3.symm
        · simp only [idx, hwSp, ↓reduceDIte]
      have hG_r01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
        median_adj_succ hR ⟨r, by omega⟩ (by change r + 1 < Fintype.card V; omega)
      have hG_r12 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 2, by omega⟩) :=
        median_adj_succ hR ⟨r + 1, by omega⟩ (by change (r + 1) + 1 < Fintype.card V; omega)
      refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
      · intro x y hDxy
        by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
        · simp only [idx, hxSp, hySp, ↓reduceDIte]
          by_cases hyA : y ∈ A
          · exact hfR_adj ⟨x, hxSp⟩ ⟨y, hySp⟩ ⟨hyA, hDxy⟩
          · have hyH : y ∈ H := (Finset.mem_union.mp hySp).resolve_right hyA
            have hxH : x ∈ H := by
              rcases Finset.mem_union.mp hxSp with h | hxA
              · exact h
              · exact absurd hDxy (hno_AH x hxA y hyH)
            simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH hyH
            rcases hxH with rfl | rfl | rfl <;> rcases hyH with rfl | rfl | rfl
            · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
            · rw [hfRu1, hfRu2]; exact hG_r01
            · exact absurd hDxy hno_13.1
            · exact absurd hDxy (not_adj_rev_of_isOrientation hO hD12)
            · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
            · rw [hfRu2, hfRu3]; exact hG_r12
            · exact absurd hDxy hno_13.2
            · exact absurd hDxy (not_adj_rev_of_isOrientation hO hD23)
            · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
        · exfalso
          have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
          rcases Finset.mem_union.mp hxSp with hxH | hxA
          · exact hno_HB x hxH y hyB hDxy
          · exact (hno_AB x hxA y (fun h => hySp (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hySp (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hySp (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hySp (Finset.mem_union_right _ h))).1 hDxy
        · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
          have hyH : y ∈ H := by
            rcases Finset.mem_union.mp hySp with h | hyA
            · exact h
            · exact absurd hDxy (hno_AB y hyA x (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hxSp (Finset.mem_union_right _ h))).2
          rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_left _ hyH)]
          exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_left _ hyH⟩ ⟨hxB, hDxy⟩
        · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
          have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
          rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_right _ hyB)]
          exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_right _ hyB⟩ ⟨hxB, hDxy⟩
      · intro x y hEq
        have hi := σ.injective hEq
        by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
        · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
          exact congrArg Subtype.val (hfR_inj hi)
        · exfalso
          have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
          simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
          have h1 := (hfR_rng ⟨x, hxSp⟩).1
          have h2 := (hfL_rng ⟨y, Finset.mem_union_right _ hyB⟩).2
          have hv : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = (fR ⟨x, hxSp⟩).val := congrArg Fin.val hi.symm
          rcases (by omega : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r ∨
              (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 1 ∨
              (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 2) with h | h | h
          · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
            have hy1 : y = u1 := congrArg Subtype.val (hfL_inj heq)
            exact hySp (Finset.mem_union_left _ (hy1 ▸ hu1H))
          · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u2m := Fin.ext (by rw [hfLu2]; exact h)
            have hy2 : y = u2 := congrArg Subtype.val (hfL_inj heq)
            exact hySp (Finset.mem_union_left _ (hy2 ▸ hu2H))
          · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u3m := Fin.ext (by rw [hfLu3]; exact h)
            have hy3 : y = u3 := congrArg Subtype.val (hfL_inj heq)
            exact hySp (Finset.mem_union_left _ (hy3 ▸ hu3H))
        · exfalso
          have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
          simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
          have h1 := (hfR_rng ⟨y, hySp⟩).1
          have h2 := (hfL_rng ⟨x, Finset.mem_union_right _ hxB⟩).2
          have hv : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = (fR ⟨y, hySp⟩).val := congrArg Fin.val hi
          rcases (by omega : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r ∨
              (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 1 ∨
              (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 2) with h | h | h
          · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
            have hx1 : x = u1 := congrArg Subtype.val (hfL_inj heq)
            exact hxSp (Finset.mem_union_left _ (hx1 ▸ hu1H))
          · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u2m := Fin.ext (by rw [hfLu2]; exact h)
            have hx2 : x = u2 := congrArg Subtype.val (hfL_inj heq)
            exact hxSp (Finset.mem_union_left _ (hx2 ▸ hu2H))
          · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u3m := Fin.ext (by rw [hfLu3]; exact h)
            have hx3 : x = u3 := congrArg Subtype.val (hfL_inj heq)
            exact hxSp (Finset.mem_union_left _ (hx3 ▸ hu3H))
        · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
          exact congrArg Subtype.val (hfL_inj hi)
    · -- hu3_in is false: u3 merges into A -> embeds_heart_two on (u1, u2, insert u3 A)!
      push Not at hu3_in
      refine embeds_heart_two (by omega) D hW ⟨T, hT, hO⟩ G hV hG
        ⟨u1, u2, hD12, insert u3 A, fun h => by simp [h13, hu1A] at h, fun h => by simp [h23, hu2A] at h,
          ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx3 | hxA
        · rw [hx3]
          have hfeq : Finset.univ.filter (fun z : W => D.Adj z u3) = {u2} := by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hDzu3
              by_cases hzA : z ∈ A
              · exact absurd hDzu3 (hno_AH z hzA u3 hu3H)
              · by_cases hzH : z ∈ H
                · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hzH
                  rcases hzH with rfl | rfl | rfl
                  · exact absurd hDzu3 hno_13.1
                  · rfl
                  · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDzu3))
                · exact absurd hDzu3 (hu3_in z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hzA⟩))
            · rintro rfl; exact hD23
          rw [hfeq, Finset.card_singleton]
        · exact hA_in x hxA
      · intro y hy1 hy2 hyA'
        have hy3 : y ≠ u3 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
        have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
        exact hB_out y hy1 hy2 hy3 hyA
      · intro x hx y hy1 hy2 hyA'
        have hy3 : y ≠ u3 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
        have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
        have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
          (Finset.mem_union.mp h).elim (fun hh => by simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with rfl | rfl | rfl <;> contradiction) hyA⟩
        rcases Finset.mem_insert.mp hx with hx3 | hxA
        · rw [hx3]; exact ⟨hno_HB u3 hu3H y hyB, hu3_in y hyB⟩
        · exact hno_AB x hxA y hy1 hy2 hy3 hyA
  · -- hu1_out is false: u1 merges into B -> embeds_heart_two on (u2, u3, A)!
    push Not at hu1_out
    refine embeds_heart_two (by omega) D hW ⟨T, hT, hO⟩ G hV hG ⟨u2, u3, hD23, A, hu2A, hu3A, hA_in, ?_, ?_⟩
    · intro y hy2 hy3 hyA
      by_cases hy1 : y = u1
      · subst y
        have hfeq : Finset.univ.filter (fun z : W => D.Adj u1 z) = {u2} := by
          ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hDu1z
            by_cases hzA : z ∈ A
            · exact absurd hDu1z (hu1_out z hzA)
            · by_cases hzH : z ∈ H
              · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hzH
                rcases hzH with rfl | rfl | rfl
                · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDu1z))
                · rfl
                · exact absurd hDu1z hno_13.1
              · exact absurd hDu1z (hno_HB u1 hu1H z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hzA⟩))
          · rintro rfl; exact hD12
        rw [hfeq, Finset.card_singleton]
      · exact hB_out y hy1 hy2 hy3 hyA
    · intro x hxA y hy2 hy3 hyA
      by_cases hy1 : y = u1
      · subst y; exact ⟨hno_AH x hxA u1 hu1H, hu1_out x hxA⟩
      · exact hno_AB x hxA y hy1 hy2 hy3 hyA

-- Heart h = 3, Topology 2: H = S_3^+ (u1 -> u2 and u1 -> u3)!
-- Extracted helper for Heart h = 3, S_3^+ Subcase 2a (non-adjacent r -> r+2)!
lemma embeds_heart_three_S3plus_2a_skip2
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (u1 u2 u3 : W) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3)
    (hD12 : D.Adj u1 u2) (hD13 : D.Adj u1 u3) (hno_23 : ¬ D.Adj u2 u3 ∧ ¬ D.Adj u3 u2)
    (A : Finset W) (hu1A : u1 ∉ A) (hu2A : u2 ∉ A) (hu3A : u3 ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ h ∈ ({u1, u2, u3} : Finset W), ¬ D.Adj x h)
    (hno_HB : ∀ h ∈ ({u1, u2, u3} : Finset W), ∀ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), ¬ D.Adj h y)
    (rkP : ↥({u1, u2, u3} ∪ A) → ℕ)
    (hrkP : ∀ x y : ↥({u1, u2, u3} ∪ A), D.Adj x.1 y.1 → rkP x < rkP y)
    (rkM : ↥({u1, u2, u3} ∪ (Finset.univ \ ({u1, u2, u3} ∪ A))) → ℕ)
    (hrkM : ∀ x y : ↥({u1, u2, u3} ∪ (Finset.univ \ ({u1, u2, u3} ∪ A))),
      x.1 ∈ Finset.univ \ ({u1, u2, u3} ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (σ : Fin (Fintype.card V) ≃ V)
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) => i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) => i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (hu2_in : ∃ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), D.Adj y u2)
    (hu3_in : ∃ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), D.Adj y u3)
    (v2 v3 : W) (hswap : v2 = u2 ∧ v3 = u3 ∨ v2 = u3 ∧ v3 = u2)
    (c2 : W) (hc2A : c2 ∈ A) (hDv2c2 : D.Adj v2 c2)
    (r : ℕ)
    (hr_ge : (Finset.univ \ ({u1, u2, u3} ∪ A)).card +
      ((Finset.univ \ ({u1, u2, u3} ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card + 1 ≤ r)
    (htot4 : r + (4 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card) ≤ Fintype.card V)
    (hG02 : ¬ G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩)) :
    Embeds D G := by
  classical
  let H : Finset W := {u1, u2, u3}
  let B : Finset W := Finset.univ \ (H ∪ A)
  let Sp := H ∪ A
  let Sm := H ∪ B
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  have hu1H : u1 ∈ H := by simp [H]
  have hu2H : u2 ∈ H := by simp [H]
  have hu3H : u3 ∈ H := by simp [H]
  have hH_card : H.card = 3 := by
    simp only [H, Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      h12, h13, h23, or_self, not_false_eq_true, Finset.card_singleton]
  have hdisj_HA : Disjoint H A := Finset.disjoint_left.mpr (fun w hwH hwA => by
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
    rcases hwH with rfl | rfl | rfl <;> contradiction)
  have hdisj_HB : Disjoint H B := Finset.disjoint_left.mpr (fun w hwH hwB =>
    (Finset.mem_sdiff.mp hwB).2 (Finset.mem_union_left _ hwH))
  have hSp_card : Sp.card = 3 + A.card := by rw [Finset.card_union_of_disjoint hdisj_HA, hH_card]
  have hSm_card : Sm.card = 3 + B.card := by rw [Finset.card_union_of_disjoint hdisj_HB, hH_card]
  have hB_out_uniq : ∀ y ∈ B, ∀ z1 z2 : W, D.Adj y z1 → D.Adj y z2 → z1 = z2 := by
    intro y hyB z1 z2 h1 h2
    have hnot := (Finset.mem_sdiff.mp hyB).2
    have hc := hB_out y (fun h => hnot (Finset.mem_union_left _ (h ▸ hu1H)))
      (fun h => hnot (Finset.mem_union_left _ (h ▸ hu2H)))
      (fun h => hnot (Finset.mem_union_left _ (h ▸ hu3H)))
      (fun h => hnot (Finset.mem_union_right _ h))
    exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj y z)).card ≤ 1)
      z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  have hA_in_uniq : ∀ x ∈ A, ∀ z1 z2 : W, D.Adj z1 x → D.Adj z2 x → z1 = z2 := by
    intro x hxA z1 z2 h1 h2
    have hc := hA_in x hxA
    exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj z x)).card ≤ 1)
      z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  have hG03 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 3, by omega⟩) := by
    let ir : Fin (Fintype.card V) := ⟨r, by omega⟩
    let ir3 : Fin (Fintype.card V) := ⟨r + 3, by omega⟩
    have hR03 := hR ir ir3 (by change r < r + 3; omega)
    have hdiff : ir3.val - ir.val = 3 := by change (r + 3) - r = 3; omega
    rw [hdiff] at hR03
    by_contra hnot03
    have hsub : Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        ir < k ∧ k ≤ ir3 ∧ G.Adj (σ ir) (σ k)) ⊆ {⟨r + 1, by omega⟩} := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hk1 : r < k.val := hk.1; have hk3 : k.val ≤ r + 3 := hk.2.1
      rcases (by omega : k.val = r + 1 ∨ k.val = r + 2 ∨ k.val = r + 3) with h1 | h2 | h3
      · exact Finset.mem_singleton.mpr (Fin.ext h1)
      · have hkeq : k = ⟨r + 2, by omega⟩ := Fin.ext h2
        rw [hkeq] at hk; exact absurd hk.2.2 hG02
      · have hkeq : k = ir3 := Fin.ext h3
        rw [hkeq] at hk; exact absurd hk.2.2 hnot03
    have hc := Finset.card_le_card hsub; rw [Finset.card_singleton] at hc; omega
  have h1v2 : u1 ≠ v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have h1v3 : u1 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv23 : v2 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact h23; exact h23.symm
  have hv2H : v2 ∈ H := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv3H : v3 ∈ H := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv2A : v2 ∉ A := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv3A : v3 ∉ A := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv2_in : ∃ y ∈ B, D.Adj y v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hv3_in : ∃ y ∈ B, D.Adj y v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hno_v23 : ¬ D.Adj v2 v3 ∧ ¬ D.Adj v3 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hno_23; exact ⟨hno_23.2, hno_23.1⟩
  have hDv12 : D.Adj u1 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hDv13 : D.Adj u1 v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hc2_notH : c2 ∉ H := fun h => Finset.disjoint_left.mp hdisj_HA h hc2A
  have hH_iff : ∀ w, w ∈ H ↔ w = u1 ∨ w = v2 ∨ w = v3 := fun w => by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [H, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  -- Right: 4-root out-branching Fp4 = Fp \ {v2 -> c2} on Sp, roots [u1, v2, c2, v3]!
  let Fp4 : Digraph ↥Sp := ⟨fun x y => y.1 ∈ A ∧ y.1 ≠ c2 ∧ D.Adj x.1 y.1⟩
  let u1p : ↥Sp := ⟨u1, Finset.mem_union_left _ hu1H⟩
  let v2p : ↥Sp := ⟨v2, Finset.mem_union_left _ hv2H⟩
  let c2p : ↥Sp := ⟨c2, Finset.mem_union_right _ hc2A⟩
  let v3p : ↥Sp := ⟨v3, Finset.mem_union_left _ hv3H⟩
  let rootsP4 : Fin 4 → ↥Sp := fun j => match j.val with | 0 => u1p | 1 => v2p | 2 => c2p | _ => v3p
  let qP4 : ℕ := if ∃ x ∈ A, D.Adj u1 x then 0 else 1
  have hFp4_inj : Function.Injective rootsP4 := by
    intro j1 j2 h
    have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 ∨ j1.val = 3 := by omega
    have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 ∨ j2.val = 3 := by omega
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> simp only [rootsP4, h1, h2] at h
    · exact Fin.ext (by omega)
    · exact absurd (congrArg Subtype.val h) h1v2
    · have hv : u1 = c2 := congrArg Subtype.val h; exact absurd (hv ▸ hu1H) hc2_notH
    · exact absurd (congrArg Subtype.val h) h1v3
    · exact absurd (congrArg Subtype.val h).symm h1v2
    · exact Fin.ext (by omega)
    · have hv : v2 = c2 := congrArg Subtype.val h; exact absurd (hv ▸ hv2H) hc2_notH
    · exact absurd (congrArg Subtype.val h) hv23
    · have hv : u1 = c2 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hu1H) hc2_notH
    · have hv : v2 = c2 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hv2H) hc2_notH
    · exact Fin.ext (by omega)
    · have hv : v3 = c2 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hv3H) hc2_notH
    · exact absurd (congrArg Subtype.val h).symm h1v3
    · exact absurd (congrArg Subtype.val h).symm hv23
    · have hv : v3 = c2 := congrArg Subtype.val h; exact absurd (hv ▸ hv3H) hc2_notH
    · exact Fin.ext (by omega)
  have hFp4_iff : ∀ w : ↥Sp, (∀ u : ↥Sp, ¬ Fp4.Adj u w) ↔ ∃ j : Fin 4, rootsP4 j = w := by
    intro w; constructor
    · intro hno
      by_cases hwc2 : w.1 = c2
      · exact ⟨⟨2, by decide⟩, by dsimp only [rootsP4, c2p]; exact Subtype.ext hwc2.symm⟩
      · rcases Finset.mem_union.mp w.2 with hwH | hwA
        · rcases (hH_iff w.1).mp hwH with h | h | h
          · exact ⟨⟨0, by decide⟩, by dsimp only [rootsP4, u1p]; exact Subtype.ext h.symm⟩
          · exact ⟨⟨1, by decide⟩, by dsimp only [rootsP4, v2p]; exact Subtype.ext h.symm⟩
          · exact ⟨⟨3, by decide⟩, by dsimp only [rootsP4, v3p]; exact Subtype.ext h.symm⟩
        · exfalso
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [hA_in w.1 hwA]; omega :
            0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card)
          have hDzw := (Finset.mem_filter.mp hz).2
          have hzSp : z ∈ Sp := by
            by_contra hznot
            exact (hno_AB w.1 hwA z (fun h => hznot (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hznot (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hznot (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hznot (Finset.mem_union_right _ h))).2 hDzw
          exact hno ⟨z, hzSp⟩ ⟨hwA, hwc2, hDzw⟩
    · rintro ⟨j, rfl⟩ u hu
      have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases hj with h | h | h | h <;> simp only [rootsP4, h] at hu
      · exact hu1A hu.1
      · exact hv2A hu.1
      · exact hu.2.1 rfl
      · exact hv3A hu.1
  have hFp4_leaves : (Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp4.Adj x y)).card ≤ kA + 2 + qP4 := by
    let LA := Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)
    let LH := (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p}) ∪ ({v2p, v3p} : Finset ↥Sp)
    have hsub : Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp4.Adj x y) ⊆ LA ∪ LH := by
      intro x hx
      have hno := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_union.mp x.2 with hxH | hxA
      · refine Finset.mem_union_right _ ?_
        rcases (hH_iff x.1).mp hxH with h | h | h
        · have hxq : x = u1p := Subtype.ext h; subst hxq
          have hno1 : ¬ ∃ a ∈ A, D.Adj u1 a := by
            rintro ⟨a, haA, hDa⟩
            have hac2 : a ≠ c2 := fun heq => h1v2 (hA_in_uniq c2 hc2A u1 v2 (heq ▸ hDa) hDv2c2)
            exact hno ⟨a, Finset.mem_union_right _ haA⟩ ⟨haA, hac2, hDa⟩
          exact Finset.mem_union_left _ (by simp [hno1])
        · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
        · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, fun z hDxz => ?_⟩)
        have hzA : z ∈ A := by
          by_contra hznotA
          by_cases hzH : z ∈ H
          · exact hno_AH x.1 hxA z hzH hDxz
          · exact (hno_AB x.1 hxA z (fun h => hzH (h ▸ hu1H)) (fun h => hzH (h ▸ hu2H))
              (fun h => hzH (h ▸ hu3H)) hznotA).1 hDxz
        have hzc2 : z ≠ c2 := fun heq => hv2A ((hA_in_uniq c2 hc2A x.1 v2 (heq ▸ hDxz) hDv2c2) ▸ hxA)
        exact hno ⟨z, Finset.mem_union_right _ hzA⟩ ⟨hzA, hzc2, hDxz⟩
    have hLA_eq : LA.card = kA := by
      refine Finset.card_bij (fun x _ => x.1) (fun x hx => Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2)
        (fun _ _ _ _ h => Subtype.ext h) (fun w hw => ⟨⟨w, Finset.mem_union_right _ (Finset.mem_filter.mp hw).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩, rfl⟩)
    have hc1 := Finset.card_le_card hsub; have hc2 := Finset.card_union_le LA LH
    have hc3 := Finset.card_union_le (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p}) ({v2p, v3p} : Finset ↥Sp)
    have c1 : (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p}).card = qP4 := by dsimp only [qP4]; split_ifs <;> simp
    have c2 : ({v2p, v3p} : Finset ↥Sp).card ≤ 2 := Finset.card_le_two
    have hLH_le : LH.card ≤ qP4 + 2 := by
      have : LH.card ≤ (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p}).card + ({v2p, v3p} : Finset ↥Sp).card := hc3
      omega
    rw [hLA_eq] at hc2; omega
  obtain ⟨fR, hfR_inj, hfR_rng, hfR_adj, hfR_rt⟩ := greedy_right_interval Fp4
    ⟨rkP, fun x y h => hrkP x y h.2.2⟩ (fun w x1 x2 h1 h2 => Subtype.ext (hA_in_uniq w.1 h1.1 x1.1 x2.1 h1.2.2 h2.2.2))
    G hR r (4 + A.card + kA) htot4 rootsP4 hFp4_inj hFp4_iff (by omega) qP4 (by dsimp only [qP4]; split_ifs <;> omega)
    (fun j hj u hu => by
      have hj0 : j.val = 0 := by dsimp only [qP4] at hj; split_ifs at hj <;> omega
      have hno1 : ¬ ∃ x ∈ A, D.Adj u1 x := by dsimp only [qP4] at hj; split_ifs at hj with h; omega; exact h
      simp only [rootsP4, hj0] at hu; exact hno1 ⟨u.1, hu.1, hu.2.2⟩)
    (by rw [Fintype.card_coe, hSp_card]; omega)
  -- Left: 4-root in-branching Fm4 on ↥Sm ⊕ Unit with roots [inl v3, inr (), inl v2, inl u1]!
  let Fm4 : Digraph (↥Sm ⊕ Unit) := ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => a.1 ∈ B ∧ D.Adj a.1 b.1
    | _, _ => False⟩
  let u1m : ↥Sm ⊕ Unit := Sum.inl ⟨u1, Finset.mem_union_left _ hu1H⟩
  let v2m : ↥Sm ⊕ Unit := Sum.inl ⟨v2, Finset.mem_union_left _ hv2H⟩
  let v3m : ↥Sm ⊕ Unit := Sum.inl ⟨v3, Finset.mem_union_left _ hv3H⟩
  let dumm : ↥Sm ⊕ Unit := Sum.inr ()
  let rootsM4 : Fin 4 → (↥Sm ⊕ Unit) := fun j => match j.val with | 0 => v3m | 1 => dumm | 2 => v2m | _ => u1m
  have hFm4_inj : Function.Injective rootsM4 := by
    intro j1 j2 h
    have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 ∨ j1.val = 3 := by omega
    have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 ∨ j2.val = 3 := by omega
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
      simp only [rootsM4, u1m, v2m, v3m, dumm, h1, h2] at h
    · exact Fin.ext (by omega)
    · cases h
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)).symm hv23
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)).symm h1v3
    · cases h
    · exact Fin.ext (by omega)
    · cases h
    · cases h
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)) hv23
    · cases h
    · exact Fin.ext (by omega)
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)).symm h1v2
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)) h1v3
    · cases h
    · exact absurd (congrArg Subtype.val (Sum.inl.inj h)) h1v2
    · exact Fin.ext (by omega)
  have hFm4_iff : ∀ w : ↥Sm ⊕ Unit, (∀ u : ↥Sm ⊕ Unit, ¬ Fm4.Adj w u) ↔ ∃ j : Fin 4, rootsM4 j = w := by
    intro w; constructor
    · intro hno
      cases w with
      | inr _ => exact ⟨⟨1, by omega⟩, rfl⟩
      | inl w0 =>
        rcases Finset.mem_union.mp w0.2 with hwH | hwB
        · rcases (hH_iff w0.1).mp hwH with h | h | h
          · exact ⟨⟨3, by omega⟩, by dsimp only [rootsM4, u1m]; exact congrArg Sum.inl (Subtype.ext h.symm)⟩
          · exact ⟨⟨2, by omega⟩, by dsimp only [rootsM4, v2m]; exact congrArg Sum.inl (Subtype.ext h.symm)⟩
          · exact ⟨⟨0, by omega⟩, by dsimp only [rootsM4, v3m]; exact congrArg Sum.inl (Subtype.ext h.symm)⟩
        · exfalso
          have hw_notHA := (Finset.mem_sdiff.mp hwB).2
          have hc := hB_out w0.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
            (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
            (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
            (fun h => hw_notHA (Finset.mem_union_right _ h))
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => D.Adj w0.1 z)).card)
          have hDwz := (Finset.mem_filter.mp hz).2
          have hzSm : z ∈ Sm := by
            by_contra hznot
            have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
            have hzA : z ∈ A := by
              by_contra hnotA; exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩))
            exact (hno_AB z hzA w0.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hw_notHA (Finset.mem_union_right _ h))).2 hDwz
          exact hno (Sum.inl ⟨z, hzSm⟩) ⟨hwB, hDwz⟩
    · rintro ⟨j, rfl⟩ u hu
      have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases hj with h | h | h | h <;> simp only [rootsM4, h] at hu <;> cases u
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hv3H)
      · exact hu
      · exact hu
      · exact hu
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hv2H)
      · exact hu
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu1H)
      · exact hu
  have hFm4_leaves : (Finset.univ.filter (fun x : ↥Sm ⊕ Unit => ∀ y : ↥Sm ⊕ Unit, ¬ Fm4.Adj y x)).card ≤ kB + 2 := by
    let LB := Finset.univ.filter (fun x : ↥Sm ⊕ Unit => match x with
      | Sum.inl a => a.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z a.1
      | Sum.inr _ => False)
    have hsub : Finset.univ.filter (fun x : ↥Sm ⊕ Unit => ∀ y : ↥Sm ⊕ Unit, ¬ Fm4.Adj y x) ⊆ LB ∪ {u1m, dumm} := by
      intro x hx
      have hno := (Finset.mem_filter.mp hx).2
      cases x with
      | inr _ => exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      | inl x0 =>
        rcases Finset.mem_union.mp x0.2 with hxH | hxB
        · rcases (hH_iff x0.1).mp hxH with h | h | h
          · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl (Subtype.ext h))))
          · exfalso; obtain ⟨b, hbB, hDb⟩ := hv2_in; exact hno (Sum.inl ⟨b, Finset.mem_union_right _ hbB⟩) ⟨hbB, h ▸ hDb⟩
          · exfalso; obtain ⟨b, hbB, hDb⟩ := hv3_in; exact hno (Sum.inl ⟨b, Finset.mem_union_right _ hbB⟩) ⟨hbB, h ▸ hDb⟩
        · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxB, fun z hDzx => ?_⟩)
          have hzB : z ∈ B := by
            by_contra hznotB
            by_cases hzH : z ∈ H
            · exact hno_HB z hzH x0.1 hxB hDzx
            · have hzA : z ∈ A := by
                by_contra hnotA; exact hznotB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩)
              have hx_notHA := (Finset.mem_sdiff.mp hxB).2
              exact (hno_AB z hzA x0.1 (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hx_notHA (Finset.mem_union_right _ h))).1 hDzx
          exact hno (Sum.inl ⟨z, Finset.mem_union_right _ hzB⟩) ⟨hzB, hDzx⟩
    have hLB_eq : LB.card = kB := by
      refine Finset.card_bij (fun x _ => Sum.elim (fun a : ↥Sm => a.1) (fun _ => u1) x) ?_ ?_ ?_
      · intro x hx; cases x with
        | inr _ => exact False.elim (Finset.mem_filter.mp hx).2
        | inl a => exact Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2
      · intro x1 hx1 x2 hx2 h; cases x1 with
        | inr _ => exact False.elim (Finset.mem_filter.mp hx1).2
        | inl a1 => cases x2 with
          | inr _ => exact False.elim (Finset.mem_filter.mp hx2).2
          | inl a2 => exact congrArg Sum.inl (Subtype.ext h)
      · intro w hw; have hw' := Finset.mem_filter.mp hw
        exact ⟨Sum.inl ⟨w, Finset.mem_union_right _ hw'.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'⟩, rfl⟩
    have hc1 := Finset.card_le_card hsub; have hc2 := Finset.card_union_le LB {u1m, dumm}
    have hc3 : ({u1m, dumm} : Finset (↥Sm ⊕ Unit)).card ≤ 2 := Finset.card_le_two
    rw [hLB_eq] at hc2; omega
  have hr_ge' : B.card + kB + 1 ≤ r := hr_ge
  obtain ⟨fL, hfL_inj, hfL_rng, hfL_adj, hfL_rt⟩ := greedy_left_interval Fm4
    ⟨fun x => match x with | Sum.inl a => rkM a | Sum.inr _ => 0,
      fun x y h => by cases x <;> cases y; exact hrkM _ _ h.1 h.2; exact False.elim h; exact False.elim h; exact False.elim h⟩
    (fun w y1 y2 h1 h2 => by
      cases w <;> cases y1 <;> cases y2
      · exact congrArg Sum.inl (Subtype.ext (hB_out_uniq _ h1.1 _ _ h1.2 h2.2))
      all_goals first | exact False.elim h1 | exact False.elim h2)
    G hL (r + 3) (r + 4) (by omega) (by omega)
    rootsM4 hFm4_inj hFm4_iff (by omega) 0 (by omega) (fun _ h => by omega)
    (by rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_punit, hSm_card]; omega)
  have hfRu1 : fR u1p = ⟨r, by omega⟩ := by simpa [rootsP4] using hfR_rt ⟨0, by omega⟩
  have hfRv2 : fR v2p = ⟨r + 1, by omega⟩ := by simpa [rootsP4] using hfR_rt ⟨1, by omega⟩
  have hfRc2 : fR c2p = ⟨r + 2, by omega⟩ := by simpa [rootsP4] using hfR_rt ⟨2, by omega⟩
  have hfRv3 : fR v3p = ⟨r + 3, by omega⟩ := by simpa [rootsP4] using hfR_rt ⟨3, by omega⟩
  have hfLv3 : fL v3m = ⟨r + 3, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨0, by omega⟩
  have hfLdum : fL dumm = ⟨r + 2, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨1, by omega⟩
  have hfLv2 : fL v2m = ⟨r + 1, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨2, by omega⟩
  have hfLu1 : fL u1m = ⟨r, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨3, by omega⟩
  let idx : W → Fin (Fintype.card V) := fun w =>
    if hw : w ∈ Sp then fR ⟨w, hw⟩ else fL (Sum.inl ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)⟩)
  have hidx_Sm : ∀ w (hw : w ∈ Sm), idx w = fL (Sum.inl ⟨w, hw⟩) := by
    intro w hw
    by_cases hwSp : w ∈ Sp
    · simp only [idx, hwSp, ↓reduceDIte]
      have hwH : w ∈ H := (Finset.mem_union.mp hw).elim id (fun hB => absurd hwSp (Finset.mem_sdiff.mp hB).2)
      rcases (hH_iff w).mp hwH with rfl | rfl | rfl
      · exact hfRu1.trans hfLu1.symm
      · exact hfRv2.trans hfLv2.symm
      · exact hfRv3.trans hfLv3.symm
    · simp only [idx, hwSp, ↓reduceDIte]
  have hG01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
    median_adj_succ hR ⟨r, by omega⟩ (by change r + 1 < Fintype.card V; omega)
  have hG12 : G.Adj (σ ⟨r + 1, by omega⟩) (σ ⟨r + 2, by omega⟩) :=
    median_adj_succ hR ⟨r + 1, by omega⟩ (by change (r + 1) + 1 < Fintype.card V; omega)
  refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
  · intro x y hDxy
    by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
    · simp only [idx, hxSp, hySp, ↓reduceDIte]
      by_cases hyA : y ∈ A
      · by_cases hyc2 : y = c2
        · subst y
          have hxv2 : x = v2 := hA_in_uniq c2 hc2A x v2 hDxy hDv2c2
          subst x; rw [hfRv2, hfRc2]; exact hG12
        · exact hfR_adj ⟨x, hxSp⟩ ⟨y, hySp⟩ ⟨hyA, hyc2, hDxy⟩
      · have hyH : y ∈ H := (Finset.mem_union.mp hySp).resolve_right hyA
        have hxH : x ∈ H := (Finset.mem_union.mp hxSp).elim id (fun hxA => absurd hDxy (hno_AH x hxA y hyH))
        rcases (hH_iff x).mp hxH with rfl | rfl | rfl <;> rcases (hH_iff y).mp hyH with rfl | rfl | rfl
        · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
        · rw [hfRu1, hfRv2]; exact hG01
        · rw [hfRu1, hfRv3]; exact hG03
        · exact absurd hDxy (not_adj_rev_of_isOrientation hO hDv12)
        · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
        · exact absurd hDxy hno_v23.1
        · exact absurd hDxy (not_adj_rev_of_isOrientation hO hDv13)
        · exact absurd hDxy hno_v23.2
        · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
    · exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      rcases Finset.mem_union.mp hxSp with hxH | hxA
      · exact hno_HB x hxH y hyB hDxy
      · exact (hno_AB x hxA y (fun h => hySp (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hySp (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hySp (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hySp (Finset.mem_union_right _ h))).1 hDxy
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      have hyH : y ∈ H := (Finset.mem_union.mp hySp).elim id (fun hyA =>
        absurd hDxy (hno_AB y hyA x (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hxSp (Finset.mem_union_right _ h))).2)
      rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_left _ hyH)]
      exact hfL_adj (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) (Sum.inl ⟨y, Finset.mem_union_left _ hyH⟩) ⟨hxB, hDxy⟩
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_right _ hyB)]
      exact hfL_adj (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) ⟨hxB, hDxy⟩
  · intro x y hEq
    have hi := σ.injective hEq
    by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
    · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi; exact congrArg Subtype.val (hfR_inj hi)
    · exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
      have h1 := (hfR_rng ⟨x, hxSp⟩).1; have h2 := (hfL_rng (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).2
      have hv : (fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val = (fR ⟨x, hxSp⟩).val := congrArg Fin.val hi.symm
      rcases (by omega : (fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val = r ∨
          (fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val = r + 1 ∨
          (fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val = r + 2 ∨
          (fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val = r + 3) with h | h | h | h
      · have heq : fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
        have hy1 : y = u1 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hySp (Finset.mem_union_left _ (hy1 ▸ hu1H))
      · have heq : fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) = fL v2m := Fin.ext (by rw [hfLv2]; exact h)
        have hy2 : y = v2 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hySp (Finset.mem_union_left _ (hy2 ▸ hv2H))
      · have heq : fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) = fL dumm := Fin.ext (by rw [hfLdum]; exact h)
        have hcon : dumm = Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩ := (hfL_inj heq).symm
        dsimp only [dumm] at hcon; cases hcon
      · have heq : fL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) = fL v3m := Fin.ext (by rw [hfLv3]; exact h)
        have hy3 : y = v3 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hySp (Finset.mem_union_left _ (hy3 ▸ hv3H))
    · exfalso
      have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
      have h1 := (hfR_rng ⟨y, hySp⟩).1; have h2 := (hfL_rng (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).2
      have hv : (fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = (fR ⟨y, hySp⟩).val := congrArg Fin.val hi
      rcases (by omega : (fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = r ∨
          (fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = r + 1 ∨
          (fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = r + 2 ∨
          (fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = r + 3) with h | h | h | h
      · have heq : fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
        have hx1 : x = u1 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hxSp (Finset.mem_union_left _ (hx1 ▸ hu1H))
      · have heq : fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = fL v2m := Fin.ext (by rw [hfLv2]; exact h)
        have hx2 : x = v2 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hxSp (Finset.mem_union_left _ (hx2 ▸ hv2H))
      · have heq : fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = fL dumm := Fin.ext (by rw [hfLdum]; exact h)
        have hcon : dumm = Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩ := (hfL_inj heq).symm
        dsimp only [dumm] at hcon; cases hcon
      · have heq : fL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = fL v3m := Fin.ext (by rw [hfLv3]; exact h)
        have hx3 : x = v3 := congrArg Subtype.val (Sum.inl.inj (hfL_inj heq))
        exact hxSp (Finset.mem_union_left _ (hx3 ▸ hv3H))
    · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
      exact congrArg Subtype.val (Sum.inl.inj (hfL_inj hi))

-- Extracted helper for Heart h = 3, S_3^+ Subcase 2b (non-adjacent r -> r+2)!
lemma embeds_heart_three_S3plus_2b_skip2
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hO : D.IsOrientation T)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (u1 u2 u3 : W) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3)
    (hD12 : D.Adj u1 u2) (hD13 : D.Adj u1 u3) (hno_23 : ¬ D.Adj u2 u3 ∧ ¬ D.Adj u3 u2)
    (A : Finset W) (hu1A : u1 ∉ A) (hu2A : u2 ∉ A) (hu3A : u3 ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ h ∈ ({u1, u2, u3} : Finset W), ¬ D.Adj x h)
    (hno_HB : ∀ h ∈ ({u1, u2, u3} : Finset W), ∀ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), ¬ D.Adj h y)
    (rkP : ↥({u1, u2, u3} ∪ A) → ℕ)
    (hrkP : ∀ x y : ↥({u1, u2, u3} ∪ A), D.Adj x.1 y.1 → rkP x < rkP y)
    (rkM : ↥({u1, u2, u3} ∪ (Finset.univ \ ({u1, u2, u3} ∪ A))) → ℕ)
    (hrkM : ∀ x y : ↥({u1, u2, u3} ∪ (Finset.univ \ ({u1, u2, u3} ∪ A))),
      x.1 ∈ Finset.univ \ ({u1, u2, u3} ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    (σ : Fin (Fintype.card V) ≃ V)
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) => i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) => i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (hu2_in : ∃ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), D.Adj y u2)
    (hu3_in : ∃ y ∈ Finset.univ \ ({u1, u2, u3} ∪ A), D.Adj y u3)
    (hu2_out : ∀ x ∈ A, ¬ D.Adj u2 x) (hu3_out : ∀ x ∈ A, ¬ D.Adj u3 x)
    (r : ℕ)
    (hr_ge : (Finset.univ \ ({u1, u2, u3} ∪ A)).card +
      ((Finset.univ \ ({u1, u2, u3} ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤ r)
    (htot4 : r + (4 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card) ≤ Fintype.card V)
    (hG02 : ¬ G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩)) :
    Embeds D G := by
  classical
  let H : Finset W := {u1, u2, u3}
  let B : Finset W := Finset.univ \ (H ∪ A)
  let Sp := H ∪ A
  let Sm := H ∪ B
  let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
  let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
  have hu1H : u1 ∈ H := by simp [H]
  have hu2H : u2 ∈ H := by simp [H]
  have hu3H : u3 ∈ H := by simp [H]
  have hH_card : H.card = 3 := by
    simp only [H, Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      h12, h13, h23, or_self, not_false_eq_true, Finset.card_singleton]
  have hdisj_HA : Disjoint H A := Finset.disjoint_left.mpr (fun w hwH hwA => by
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
    rcases hwH with rfl | rfl | rfl <;> contradiction)
  have hdisj_HB : Disjoint H B := Finset.disjoint_left.mpr (fun w hwH hwB =>
    (Finset.mem_sdiff.mp hwB).2 (Finset.mem_union_left _ hwH))
  have hSp_card : Sp.card = 3 + A.card := by rw [Finset.card_union_of_disjoint hdisj_HA, hH_card]
  have hSm_card : Sm.card = 3 + B.card := by rw [Finset.card_union_of_disjoint hdisj_HB, hH_card]
  have hB_out_uniq : ∀ y ∈ B, ∀ z1 z2 : W, D.Adj y z1 → D.Adj y z2 → z1 = z2 := by
    intro y hyB z1 z2 h1 h2
    have hnot := (Finset.mem_sdiff.mp hyB).2
    have hc := hB_out y (fun h => hnot (Finset.mem_union_left _ (h ▸ hu1H)))
      (fun h => hnot (Finset.mem_union_left _ (h ▸ hu2H)))
      (fun h => hnot (Finset.mem_union_left _ (h ▸ hu3H)))
      (fun h => hnot (Finset.mem_union_right _ h))
    exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj y z)).card ≤ 1)
      z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  have hA_in_uniq : ∀ x ∈ A, ∀ z1 z2 : W, D.Adj z1 x → D.Adj z2 x → z1 = z2 := by
    intro x hxA z1 z2 h1 h2
    have hc := hA_in x hxA
    exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj z x)).card ≤ 1)
      z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  -- and greedy_left_interval on F^- \ {c3 -> u3} (placing c3 at r + 2)!
  obtain ⟨c3, hc3B, hDc3u3⟩ := hu3_in
  let Tp : Digraph ↥Sp := ⟨fun x y => D.Adj x.1 y.1⟩
  let u1p : ↥Sp := ⟨u1, Finset.mem_union_left _ hu1H⟩
  let u2p : ↥Sp := ⟨u2, Finset.mem_union_left _ hu2H⟩
  let u3p : ↥Sp := ⟨u3, Finset.mem_union_left _ hu3H⟩
  have hTp_indeg : ∀ w x1 x2 : ↥Sp, Tp.Adj x1 w → Tp.Adj x2 w → x1 = x2 := by
    intro w x1 x2 h1 h2
    rcases Finset.mem_union.mp w.2 with hwH | hwA
    · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
      rcases hwH with h | h | h
      · exfalso
        rcases Finset.mem_union.mp x1.2 with hxH | hxA
        · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
          rcases hxH with h' | h' | h'
          · exact T.ne_of_adj (hO.1 _ _ h1) (h'.trans h.symm)
          · exact not_adj_rev_of_isOrientation hO hD12 (h' ▸ h ▸ h1)
          · exact not_adj_rev_of_isOrientation hO hD13 (h' ▸ h ▸ h1)
        · exact hno_AH x1.1 hxA u1 hu1H (h ▸ h1)
      · have hx1u1 : x1.1 = u1 := by
          rcases Finset.mem_union.mp x1.2 with hxH | hxA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h' | h' | h'
            · exact h'
            · exact absurd (h'.trans h.symm) (T.ne_of_adj (hO.1 _ _ h1))
            · exact absurd (h' ▸ h ▸ h1) hno_23.2
          · exact absurd (h ▸ h1) (hno_AH x1.1 hxA u2 hu2H)
        have hx2u1 : x2.1 = u1 := by
          rcases Finset.mem_union.mp x2.2 with hxH | hxA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h' | h' | h'
            · exact h'
            · exact absurd (h'.trans h.symm) (T.ne_of_adj (hO.1 _ _ h2))
            · exact absurd (h' ▸ h ▸ h2) hno_23.2
          · exact absurd (h ▸ h2) (hno_AH x2.1 hxA u2 hu2H)
        exact Subtype.ext (hx1u1.trans hx2u1.symm)
      · have hx1u1 : x1.1 = u1 := by
          rcases Finset.mem_union.mp x1.2 with hxH | hxA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h' | h' | h'
            · exact h'
            · exact absurd (h' ▸ h ▸ h1) hno_23.1
            · exact absurd (h'.trans h.symm) (T.ne_of_adj (hO.1 _ _ h1))
          · exact absurd (h ▸ h1) (hno_AH x1.1 hxA u3 hu3H)
        have hx2u1 : x2.1 = u1 := by
          rcases Finset.mem_union.mp x2.2 with hxH | hxA
          · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
            rcases hxH with h' | h' | h'
            · exact h'
            · exact absurd (h' ▸ h ▸ h2) hno_23.1
            · exact absurd (h'.trans h.symm) (T.ne_of_adj (hO.1 _ _ h2))
          · exact absurd (h ▸ h2) (hno_AH x2.1 hxA u3 hu3H)
        exact Subtype.ext (hx1u1.trans hx2u1.symm)
    · exact Subtype.ext (hA_in_uniq w.1 hwA x1.1 x2.1 h1 h2)
  have hTp_root : ∀ w : ↥Sp, (∀ u : ↥Sp, ¬ Tp.Adj u w) ↔ w = u1p := by
    intro w; constructor
    · intro hno
      rcases Finset.mem_union.mp w.2 with hwH | hwA
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
        rcases hwH with h | h | h
        · exact Subtype.ext h
        · exact absurd (by dsimp only [Tp, u1p]; rw [h]; exact hD12) (hno u1p)
        · exact absurd (by dsimp only [Tp, u1p]; rw [h]; exact hD13) (hno u1p)
      · exfalso
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [hA_in w.1 hwA]; omega :
          0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card)
        have hDzw := (Finset.mem_filter.mp hz).2
        have hzSp : z ∈ Sp := by
          by_contra hznot
          exact (hno_AB w.1 hwA z (fun h => hznot (Finset.mem_union_left _ (h ▸ hu1H)))
            (fun h => hznot (Finset.mem_union_left _ (h ▸ hu2H)))
            (fun h => hznot (Finset.mem_union_left _ (h ▸ hu3H)))
            (fun h => hznot (Finset.mem_union_right _ h))).2 hDzw
        exact hno ⟨z, hzSp⟩ hDzw
    · rintro rfl u hu
      rcases Finset.mem_union.mp u.2 with huH | huA
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at huH
        rcases huH with h | h | h
        · exact T.ne_of_adj (hO.1 _ _ hu) h
        · exact not_adj_rev_of_isOrientation hO hD12 (h ▸ hu)
        · exact not_adj_rev_of_isOrientation hO hD13 (h ▸ hu)
      · exact hno_AH u.1 huA u1 hu1H hu
  have hu2p_leaf : ∀ x : ↥Sp, ¬ Tp.Adj u2p x := by
    intro x hx
    rcases Finset.mem_union.mp x.2 with hxH | hxA
    · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
      rcases hxH with h | h | h
      · exact not_adj_rev_of_isOrientation hO hD12 (h ▸ hx)
      · exact T.ne_of_adj (hO.1 _ _ hx) h.symm
      · exact hno_23.1 (h ▸ hx)
    · exact hu2_out x.1 hxA hx
  have hu3p_leaf : ∀ x : ↥Sp, ¬ Tp.Adj u3p x := by
    intro x hx
    rcases Finset.mem_union.mp x.2 with hxH | hxA
    · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
      rcases hxH with h | h | h
      · exact not_adj_rev_of_isOrientation hO hD13 (h ▸ hx)
      · exact hno_23.2 (h ▸ hx)
      · exact T.ne_of_adj (hO.1 _ _ hx) h.symm
    · exact hu3_out x.1 hxA hx
  have hTp_leaves : (Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Tp.Adj x y)).card ≤ kA + 2 := by
    let LA := Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)
    have hsub : Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Tp.Adj x y) ⊆ LA ∪ {u2p, u3p} := by
      intro x hx
      have hno := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_union.mp x.2 with hxH | hxA
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
        rcases hxH with h | h | h
        · exact absurd (by dsimp only [Tp, u2p]; rw [h]; exact hD12) (hno u2p)
        · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
        · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, fun z hDxz => ?_⟩)
        have hzA : z ∈ A := by
          by_contra hznotA
          by_cases hzH : z ∈ H
          · exact hno_AH x.1 hxA z hzH hDxz
          · exact (hno_AB x.1 hxA z (fun h => hzH (h ▸ hu1H)) (fun h => hzH (h ▸ hu2H))
              (fun h => hzH (h ▸ hu3H)) hznotA).1 hDxz
        exact hno ⟨z, Finset.mem_union_right _ hzA⟩ hDxz
    have hLA_eq : LA.card = kA := by
      refine Finset.card_bij (fun x _ => x.1) (fun x hx => Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2)
        (fun _ _ _ _ h => Subtype.ext h) (fun w hw => ⟨⟨w, Finset.mem_union_right _ (Finset.mem_filter.mp hw).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩, rfl⟩)
    have hc1 := Finset.card_le_card hsub; have hc2 := Finset.card_union_le LA {u2p, u3p}
    have hc3 : ({u2p, u3p} : Finset ↥Sp).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨fR, hfR_inj, hfR_rng, hfR_adj, hfRu1, hfRu2, hfR_no2, hfRu3⟩ :=
    greedy_right_interval_skip2 Tp ⟨rkP, hrkP⟩ hTp_indeg G hR r (4 + A.card + kA) htot4 (by omega)
      u1p u2p u3p hTp_root hD12 hD13 (fun h => h23 (congrArg Subtype.val h)) hu2p_leaf hu3p_leaf hG02
      (by rw [Fintype.card_coe, hSp_card]; omega)
  -- Left: 4-root in-branching Fm4 = Fm \ {c3 -> u3} on Sm with roots [u3, c3, u2, u1]!
  let Fm4 : Digraph ↥Sm := ⟨fun x y => x.1 ∈ B ∧ x.1 ≠ c3 ∧ D.Adj x.1 y.1⟩
  let u1m : ↥Sm := ⟨u1, Finset.mem_union_left _ hu1H⟩
  let u2m : ↥Sm := ⟨u2, Finset.mem_union_left _ hu2H⟩
  let u3m : ↥Sm := ⟨u3, Finset.mem_union_left _ hu3H⟩
  let c3m : ↥Sm := ⟨c3, Finset.mem_union_right _ hc3B⟩
  let rootsM4 : Fin 4 → ↥Sm := fun j => match j.val with | 0 => u3m | 1 => c3m | 2 => u2m | _ => u1m
  let qM4 : ℕ := if ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 then 0 else 1
  have hc3_notH : c3 ∉ H := fun h => (Finset.mem_sdiff.mp hc3B).2 (Finset.mem_union_left _ h)
  have hFm4_inj : Function.Injective rootsM4 := by
    intro j1 j2 h
    have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 ∨ j1.val = 3 := by omega
    have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 ∨ j2.val = 3 := by omega
    rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> simp only [rootsM4, h1, h2] at h
    · exact Fin.ext (by omega)
    · have hv : u3 = c3 := congrArg Subtype.val h; exact absurd (hv ▸ hu3H) hc3_notH
    · exact absurd (congrArg Subtype.val h).symm h23
    · exact absurd (congrArg Subtype.val h).symm h13
    · have hv : u3 = c3 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hu3H) hc3_notH
    · exact Fin.ext (by omega)
    · have hv : u2 = c3 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hu2H) hc3_notH
    · have hv : u1 = c3 := (congrArg Subtype.val h).symm; exact absurd (hv ▸ hu1H) hc3_notH
    · exact absurd (congrArg Subtype.val h) h23
    · have hv : u2 = c3 := congrArg Subtype.val h; exact absurd (hv ▸ hu2H) hc3_notH
    · exact Fin.ext (by omega)
    · exact absurd (congrArg Subtype.val h).symm h12
    · exact absurd (congrArg Subtype.val h) h13
    · have hv : u1 = c3 := congrArg Subtype.val h; exact absurd (hv ▸ hu1H) hc3_notH
    · exact absurd (congrArg Subtype.val h) h12
    · exact Fin.ext (by omega)
  have hFm4_iff : ∀ w : ↥Sm, (∀ u : ↥Sm, ¬ Fm4.Adj w u) ↔ ∃ j : Fin 4, rootsM4 j = w := by
    intro w; constructor
    · intro hno
      by_cases hwc3 : w.1 = c3
      · exact ⟨⟨1, by decide⟩, by dsimp only [rootsM4, c3m]; exact Subtype.ext hwc3.symm⟩
      · rcases Finset.mem_union.mp w.2 with hwH | hwB
        · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
          rcases hwH with h | h | h
          · exact ⟨⟨3, by decide⟩, by dsimp only [rootsM4, u1m]; exact Subtype.ext h.symm⟩
          · exact ⟨⟨2, by decide⟩, by dsimp only [rootsM4, u2m]; exact Subtype.ext h.symm⟩
          · exact ⟨⟨0, by decide⟩, by dsimp only [rootsM4, u3m]; exact Subtype.ext h.symm⟩
        · exfalso
          have hw_notHA := (Finset.mem_sdiff.mp hwB).2
          have hc := hB_out w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
            (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
            (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
            (fun h => hw_notHA (Finset.mem_union_right _ h))
          obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => D.Adj w.1 z)).card)
          have hDwz := (Finset.mem_filter.mp hz).2
          have hzSm : z ∈ Sm := by
            by_contra hznot
            have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
            have hzA : z ∈ A := by
              by_contra hnotA; exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩))
            exact (hno_AB z hzA w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hw_notHA (Finset.mem_union_right _ h))).2 hDwz
          exact hno ⟨z, hzSm⟩ ⟨hwB, hwc3, hDwz⟩
    · rintro ⟨j, rfl⟩ u hu
      have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases hj with h | h | h | h <;> simp only [rootsM4, h] at hu
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu3H)
      · exact hu.2.1 rfl
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu2H)
      · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu1H)
  have hFm4_leaves : (Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm4.Adj y x)).card ≤ kB + 1 + qM4 := by
    let LB := Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)
    let LH := (if ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 then (∅ : Finset ↥Sm) else {u3m}) ∪ {u1m}
    have hsub : Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm4.Adj y x) ⊆ LB ∪ LH := by
      intro x hx
      have hno := (Finset.mem_filter.mp hx).2
      rcases Finset.mem_union.mp x.2 with hxH | hxB
      · refine Finset.mem_union_right _ ?_
        simp only [H, Finset.mem_insert, Finset.mem_singleton] at hxH
        rcases hxH with h | h | h
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (Subtype.ext h))
        · exfalso; obtain ⟨y2, hy2B, hDy2⟩ := hu2_in
          have hy2c3 : y2 ≠ c3 := fun heq => h23 (hB_out_uniq c3 hc3B u2 u3 (heq ▸ hDy2) hDc3u3)
          exact hno ⟨y2, Finset.mem_union_right _ hy2B⟩ ⟨hy2B, hy2c3, h ▸ hDy2⟩
        · have hxq : x = u3m := Subtype.ext h; subst hxq
          have hno3 : ¬ ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 := fun ⟨y, hyB, hyne, hDy⟩ =>
            hno ⟨y, Finset.mem_union_right _ hyB⟩ ⟨hyB, hyne, hDy⟩
          exact Finset.mem_union_left _ (by simp [hno3])
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxB, fun z hDzx => ?_⟩)
        have hzB : z ∈ B := by
          by_contra hznotB
          by_cases hzH : z ∈ H
          · exact hno_HB z hzH x.1 hxB hDzx
          · have hzA : z ∈ A := by
              by_contra hnotA; exact hznotB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩)
            have hx_notHA := (Finset.mem_sdiff.mp hxB).2
            exact (hno_AB z hzA x.1 (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
              (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
              (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
              (fun h => hx_notHA (Finset.mem_union_right _ h))).1 hDzx
        have hzc3 : z ≠ c3 := fun heq =>
          (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_left _ ((hB_out_uniq c3 hc3B x.1 u3 (heq ▸ hDzx) hDc3u3).symm ▸ hu3H))
        exact hno ⟨z, Finset.mem_union_right _ hzB⟩ ⟨hzB, hzc3, hDzx⟩
    have hLB_eq : LB.card = kB := by
      refine Finset.card_bij (fun x _ => x.1) (fun x hx => Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2)
        (fun _ _ _ _ h => Subtype.ext h) (fun w hw => ⟨⟨w, Finset.mem_union_right _ (Finset.mem_filter.mp hw).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩, rfl⟩)
    have hc1 := Finset.card_le_card hsub; have hc2 := Finset.card_union_le LB LH
    have hc3 := Finset.card_union_le (if ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 then (∅ : Finset ↥Sm) else {u3m}) {u1m}
    have c1 : (if ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 then (∅ : Finset ↥Sm) else {u3m}).card = qM4 := by dsimp only [qM4]; split_ifs <;> simp
    have hLH_le : LH.card ≤ qM4 + 1 := by
      have : LH.card ≤ (if ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 then (∅ : Finset ↥Sm) else {u3m}).card + ({u1m} : Finset ↥Sm).card := hc3
      rw [c1, Finset.card_singleton] at this; exact this
    rw [hLB_eq] at hc2; omega
  have hr_ge' : B.card + kB ≤ r := hr_ge
  obtain ⟨fL, hfL_inj, hfL_rng, hfL_adj, hfL_rt⟩ := greedy_left_interval Fm4
    ⟨rkM, fun x y h => hrkM x y h.1 h.2.2⟩ (fun w y1 y2 h1 h2 => Subtype.ext (hB_out_uniq w.1 h1.1 y1.1 y2.1 h1.2.2 h2.2.2))
    G hL (r + 3) (r + 4) (by omega) (by omega)
    rootsM4 hFm4_inj hFm4_iff (by omega) qM4 (by dsimp only [qM4]; split_ifs <;> omega)
    (fun j hj u hu => by
      have hj0 : j.val = 0 := by dsimp only [qM4] at hj; split_ifs at hj <;> omega
      have hno3 : ¬ ∃ y ∈ B, y ≠ c3 ∧ D.Adj y u3 := by dsimp only [qM4] at hj; split_ifs at hj with h; omega; exact h
      simp only [rootsM4, hj0] at hu; exact hno3 ⟨u.1, hu.1, hu.2.1, hu.2.2⟩)
    (by rw [Fintype.card_coe, hSm_card]; omega)
  have hfLu3 : fL u3m = ⟨r + 3, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨0, by omega⟩
  have hfLc3 : fL c3m = ⟨r + 2, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨1, by omega⟩
  have hfLu2 : fL u2m = ⟨r + 1, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨2, by omega⟩
  have hfLu1 : fL u1m = ⟨r, by omega⟩ := by simpa [rootsM4] using hfL_rt ⟨3, by omega⟩
  let idx : W → Fin (Fintype.card V) := fun w =>
    if hw : w ∈ Sp then fR ⟨w, hw⟩ else fL ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)⟩
  have hidx_Sm : ∀ w (hw : w ∈ Sm), idx w = fL ⟨w, hw⟩ := by
    intro w hw
    by_cases hwSp : w ∈ Sp
    · simp only [idx, hwSp, ↓reduceDIte]
      have hwH : w ∈ H := (Finset.mem_union.mp hw).elim id (fun hB => absurd hwSp (Finset.mem_sdiff.mp hB).2)
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
      rcases hwH with rfl | rfl | rfl
      · exact hfRu1.trans hfLu1.symm
      · exact hfRu2.trans hfLu2.symm
      · exact hfRu3.trans hfLu3.symm
    · simp only [idx, hwSp, ↓reduceDIte]
  have hG23 : G.Adj (σ ⟨r + 2, by omega⟩) (σ ⟨r + 3, by omega⟩) :=
    median_adj_succ hR ⟨r + 2, by omega⟩ (by change (r + 2) + 1 < Fintype.card V; omega)
  refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
  · intro x y hDxy
    by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
    · simp only [idx, hxSp, hySp, ↓reduceDIte]; exact hfR_adj ⟨x, hxSp⟩ ⟨y, hySp⟩ hDxy
    · exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      rcases Finset.mem_union.mp hxSp with hxH | hxA
      · exact hno_HB x hxH y hyB hDxy
      · exact (hno_AB x hxA y (fun h => hySp (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hySp (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hySp (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hySp (Finset.mem_union_right _ h))).1 hDxy
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      have hyH : y ∈ H := (Finset.mem_union.mp hySp).elim id (fun hyA =>
        absurd hDxy (hno_AB y hyA x (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hxSp (Finset.mem_union_right _ h))).2)
      rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_left _ hyH)]
      by_cases hxc3 : x = c3
      · subst x
        have hyu3 : y = u3 := hB_out_uniq c3 hc3B y u3 hDxy hDc3u3
        subst y; rw [hfLc3, hfLu3]; exact hG23
      · exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_left _ hyH⟩ ⟨hxB, hxc3, hDxy⟩
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      have hxc3 : x ≠ c3 := fun heq =>
        (Finset.mem_sdiff.mp hyB).2 (Finset.mem_union_left _ ((hB_out_uniq c3 hc3B y u3 (heq ▸ hDxy) hDc3u3).symm ▸ hu3H))
      rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_right _ hyB)]
      exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_right _ hyB⟩ ⟨hxB, hxc3, hDxy⟩
  · intro x y hEq
    have hi := σ.injective hEq
    by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
    · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi; exact congrArg Subtype.val (hfR_inj hi)
    · exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
      simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
      have h1 := (hfR_rng ⟨x, hxSp⟩).1; have h2 := (hfL_rng ⟨y, Finset.mem_union_right _ hyB⟩).2
      have hv : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = (fR ⟨x, hxSp⟩).val := congrArg Fin.val hi.symm
      rcases (by omega : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r ∨
          (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 1 ∨
          (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 2 ∨
          (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 3) with h | h | h | h
      · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
        have hy1 : y = u1 := congrArg Subtype.val (hfL_inj heq)
        exact hySp (Finset.mem_union_left _ (hy1 ▸ hu1H))
      · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u2m := Fin.ext (by rw [hfLu2]; exact h)
        have hy2 : y = u2 := congrArg Subtype.val (hfL_inj heq)
        exact hySp (Finset.mem_union_left _ (hy2 ▸ hu2H))
      · exact hfR_no2 ⟨x, hxSp⟩ (Fin.ext (by change (fR ⟨x, hxSp⟩).val = r + 2; omega))
      · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u3m := Fin.ext (by rw [hfLu3]; exact h)
        have hy3 : y = u3 := congrArg Subtype.val (hfL_inj heq)
        exact hySp (Finset.mem_union_left _ (hy3 ▸ hu3H))
    · exfalso
      have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
      simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
      have h1 := (hfR_rng ⟨y, hySp⟩).1; have h2 := (hfL_rng ⟨x, Finset.mem_union_right _ hxB⟩).2
      have hv : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = (fR ⟨y, hySp⟩).val := congrArg Fin.val hi
      rcases (by omega : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r ∨
          (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 1 ∨
          (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 2 ∨
          (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 3) with h | h | h | h
      · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
        have hx1 : x = u1 := congrArg Subtype.val (hfL_inj heq)
        exact hxSp (Finset.mem_union_left _ (hx1 ▸ hu1H))
      · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u2m := Fin.ext (by rw [hfLu2]; exact h)
        have hx2 : x = u2 := congrArg Subtype.val (hfL_inj heq)
        exact hxSp (Finset.mem_union_left _ (hx2 ▸ hu2H))
      · exact hfR_no2 ⟨y, hySp⟩ (Fin.ext (by change (fR ⟨y, hySp⟩).val = r + 2; omega))
      · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u3m := Fin.ext (by rw [hfLu3]; exact h)
        have hx3 : x = u3 := congrArg Subtype.val (hfL_inj heq)
        exact hxSp (Finset.mem_union_left _ (hx3 ▸ hu3H))
    · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi; exact congrArg Subtype.val (hfL_inj hi)

lemma embeds_heart_three_S3plus {n : ℕ} (hn : 4 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hInt4 : 4 ≤ n - (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card)
    (u1 u2 u3 : W) (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3)
    (hD12 : D.Adj u1 u2) (hD13 : D.Adj u1 u3)
    (A : Finset W) (hu1A : u1 ∉ A) (hu2A : u2 ∉ A) (hu3A : u3 ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x) :
    Embeds D G := by
  classical
  obtain ⟨T, hT, hO⟩ := hTree
  let H : Finset W := {u1, u2, u3}
  let B : Finset W := Finset.univ \ (H ∪ A)
  have hu1H : u1 ∈ H := by simp [H]
  have hu2H : u2 ∈ H := by simp [H]
  have hu3H : u3 ∈ H := by simp [H]
  obtain ⟨hno_AH, hno_HB, ⟨rkP, hrkP⟩, ⟨rkM, hrkM⟩, hleaves_le⟩ :=
    heart_three_structure D hT hO u1 u2 u3 h12 h13 h23 (Or.inr ⟨hD12, hD13⟩) A hu1A hu2A hu3A hA_in hB_out hno_AB
  have hno_23 : ¬ D.Adj u2 u3 ∧ ¬ D.Adj u3 u2 := by
    have hnoT : ¬ T.Adj u2 u3 := by
      intro hT23
      let p1 : T.Walk u2 u3 := SimpleGraph.Walk.cons hT23 SimpleGraph.Walk.nil
      let p2 : T.Walk u2 u3 := SimpleGraph.Walk.cons (hO.1 u1 u2 hD12).symm
        (SimpleGraph.Walk.cons (hO.1 u1 u3 hD13) SimpleGraph.Walk.nil)
      have hp1 : p1.IsPath := SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h23])
      have hp2 : p2.IsPath := SimpleGraph.Walk.IsPath.cons
        (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [h13])) (by simp [h12.symm, h23])
      have heq := congrArg (fun p : T.Walk u2 u3 => p.length)
        (congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u2 u3).elim ⟨p1, hp1⟩ ⟨p2, hp2⟩))
      simp [p1, p2] at heq
    exact ⟨fun h => hnoT (hO.1 u2 u3 h), fun h => hnoT (hO.1 u3 u2 h).symm⟩
  -- Helper: if some leaf b ∈ {u2, u3} has no in-neighbor in B, reduces to embeds_heart_two!
  have hred_h2 : ∀ (v2 v3 : W), (v2 = u2 ∧ v3 = u3 ∨ v2 = u3 ∧ v3 = u2) →
      (∀ y ∈ B, ¬ D.Adj y v2) → Embeds D G := by
    intro v2 v3 hswap hv2_noB
    have h1v2 : u1 ≠ v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have h1v3 : u1 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hv23 : v2 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact h23; exact h23.symm
    have hDv2 : D.Adj u1 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hDv3 : D.Adj u1 v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hno_v23 : ¬ D.Adj v3 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hno_23.2; exact hno_23.1
    have hv2H : v2 ∈ H := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hv3A : v3 ∉ A := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hHeq : ∀ w, w ∈ H ↔ w = u1 ∨ w = v2 ∨ w = v3 := fun w => by
      rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [H, Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    refine embeds_heart_two (by omega) D hW ⟨T, hT, hO⟩ G hV hG
      ⟨u1, v3, hDv3, insert v2 A, fun h => by simp [h1v2, hu1A] at h, fun h => by simp [hv23.symm, hv3A] at h,
        ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxv2 | hxA
      · rw [hxv2]
        have hfeq : Finset.univ.filter (fun z : W => D.Adj z v2) = {u1} := by
          ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hDz
            by_cases hzA : z ∈ A
            · exact absurd hDz (hno_AH z hzA v2 hv2H)
            · by_cases hzH : z ∈ H
              · rcases (hHeq z).mp hzH with rfl | rfl | rfl
                · rfl
                · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDz))
                · exact absurd hDz hno_v23
              · exact absurd hDz (hv2_noB z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hzA⟩))
          · rintro rfl; exact hDv2
        rw [hfeq, Finset.card_singleton]
      · exact hA_in x hxA
    · intro y hy1 hyv3 hyA'
      have hyv2 : y ≠ v2 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
      have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
      have hy23 : y ≠ u2 ∧ y ≠ u3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩
      exact hB_out y hy1 hy23.1 hy23.2 hyA
    · intro x hx y hy1 hyv3 hyA'
      have hyv2 : y ≠ v2 := fun h => hyA' (Finset.mem_insert.mpr (Or.inl h))
      have hyA : y ∉ A := fun h => hyA' (Finset.mem_insert.mpr (Or.inr h))
      have hy23 : y ≠ u2 ∧ y ≠ u3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨‹_›, ‹_›⟩
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
        (Finset.mem_union.mp h).elim (fun hh => by rcases (hHeq y).mp hh with rfl | rfl | rfl <;> contradiction) hyA⟩
      rcases Finset.mem_insert.mp hx with hxv2 | hxA
      · rw [hxv2]; exact ⟨hno_HB v2 hv2H y hyB, hv2_noB y hyB⟩
      · exact hno_AB x hxA y hy1 hy23.1 hy23.2 hyA
  by_cases hu2_in : ∃ y ∈ B, D.Adj y u2
  · by_cases hu3_in : ∃ y ∈ B, D.Adj y u3
    · -- Both u2 and u3 have in-neighbors in B!
      obtain ⟨σ, hR, hL⟩ := exists_median_order G hG
      let Sp := H ∪ A
      let Sm := H ∪ B
      have hH_card : H.card = 3 := by
        simp only [H, Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
          h12, h13, h23, or_self, not_false_eq_true, Finset.card_singleton]
      have hdisj_HA : Disjoint H A := Finset.disjoint_left.mpr (fun w hwH hwA => by
        simp only [H, Finset.mem_insert, Finset.mem_singleton] at hwH
        rcases hwH with rfl | rfl | rfl <;> contradiction)
      have hdisj_HB : Disjoint H B := Finset.disjoint_left.mpr (fun w hwH hwB =>
        (Finset.mem_sdiff.mp hwB).2 (Finset.mem_union_left _ hwH))
      have hSp_card : Sp.card = 3 + A.card := by rw [Finset.card_union_of_disjoint hdisj_HA, hH_card]
      have hSm_card : Sm.card = 3 + B.card := by rw [Finset.card_union_of_disjoint hdisj_HB, hH_card]
      have hAB_sum : 3 + A.card + B.card = n := by
        have h1 : B.card + Sp.card = n := by
          have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (H ∪ A))
          rw [Finset.card_univ, hW] at this; exact this
        omega
      let kA := (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card
      let kB := (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card
      have hkAB_le : kA + kB ≤ (Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := hleaves_le
      -- Note |B| >= 2 because y2 -> u2 and y3 -> u3 have y2 != y3 (out-degree 1 in B)!
      have hB_ge2 : 2 ≤ B.card := by
        obtain ⟨y2, hy2B, hDy2⟩ := hu2_in
        obtain ⟨y3, hy3B, hDy3⟩ := hu3_in
        have hy23 : y2 ≠ y3 := by
          rintro rfl
          have hnot := (Finset.mem_sdiff.mp hy2B).2
          have h1 := hB_out y2 (fun h => hnot (Finset.mem_union_left _ (h ▸ hu1H)))
            (fun h => hnot (Finset.mem_union_left _ (h ▸ hu2H)))
            (fun h => hnot (Finset.mem_union_left _ (h ▸ hu3H)))
            (fun h => hnot (Finset.mem_union_right _ h))
          exact h23 (Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj y2 z)).card ≤ 1)
            u2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDy2⟩)
            u3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDy3⟩))
        have hsub : ({y2, y3} : Finset W) ⊆ B := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        have := Finset.card_le_card hsub; rw [Finset.card_pair hy23] at this; exact this
      -- Shared Fp and Fm helpers for any ordering (v2, v3) of {u2, u3}!
      have hB_out_uniq : ∀ y ∈ B, ∀ z1 z2 : W, D.Adj y z1 → D.Adj y z2 → z1 = z2 := by
        intro y hyB z1 z2 h1 h2
        have hnot := (Finset.mem_sdiff.mp hyB).2
        have hc := hB_out y (fun h => hnot (Finset.mem_union_left _ (h ▸ hu1H)))
          (fun h => hnot (Finset.mem_union_left _ (h ▸ hu2H)))
          (fun h => hnot (Finset.mem_union_left _ (h ▸ hu3H)))
          (fun h => hnot (Finset.mem_union_right _ h))
        exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj y z)).card ≤ 1)
          z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      have hA_in_uniq : ∀ x ∈ A, ∀ z1 z2 : W, D.Adj z1 x → D.Adj z2 x → z1 = z2 := by
        intro x hxA z1 z2 h1 h2
        have hc := hA_in x hxA
        exact Finset.card_le_one.mp (by omega : (Finset.univ.filter (fun z : W => D.Adj z x)).card ≤ 1)
          z1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          z2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      -- Helper for the easy G.Adj (σ r) (σ (r + 2)) glue (used in BOTH Subcase 2a and Subcase 2b!)
      have hglue_02 : ∀ (v2 v3 : W), (v2 = u2 ∧ v3 = u3 ∨ v2 = u3 ∧ v3 = u2) →
          ∀ (r lenR : ℕ) (_hr_ge : B.card + kB ≤ r) (htot : r + lenR ≤ Fintype.card V) (hlenR3 : 3 ≤ lenR),
          3 + A.card + kA + (if ∃ x ∈ A, D.Adj v2 x then 0 else 1) + (if ∃ x ∈ A, D.Adj v3 x then 0 else 1) ≤ lenR + 1 →
          G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩) → Embeds D G := by
        intro v2 v3 hswap r lenR hr_ge htot hlenR3 hlenR_ok hG02
        have h1v2 : u1 ≠ v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have h1v3 : u1 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv23 : v2 ≠ v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact h23; exact h23.symm
        have hv2H : v2 ∈ H := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv3H : v3 ∈ H := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv2A : v2 ∉ A := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv3A : v3 ∉ A := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv2_in : ∃ y ∈ B, D.Adj y v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hv3_in : ∃ y ∈ B, D.Adj y v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hno_v23 : ¬ D.Adj v2 v3 ∧ ¬ D.Adj v3 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hno_23; exact ⟨hno_23.2, hno_23.1⟩
        have hDv12 : D.Adj u1 v2 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hDv13 : D.Adj u1 v3 := by rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hH_iff : ∀ w, w ∈ H ↔ w = u1 ∨ w = v2 ∨ w = v3 := fun w => by
          rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [H, Finset.mem_insert, Finset.mem_singleton]
          constructor <;> rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
        let Fp : Digraph ↥Sp := ⟨fun x y => y.1 ∈ A ∧ D.Adj x.1 y.1⟩
        let u1p : ↥Sp := ⟨u1, Finset.mem_union_left _ hu1H⟩
        let v2p : ↥Sp := ⟨v2, Finset.mem_union_left _ hv2H⟩
        let v3p : ↥Sp := ⟨v3, Finset.mem_union_left _ hv3H⟩
        let rootsP : Fin 3 → ↥Sp := fun j => match j.val with | 0 => u1p | 1 => v2p | _ => v3p
        let qP : ℕ := if ∃ x ∈ A, D.Adj u1 x then 0 else 1
        have hFp_leaves : (Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp.Adj x y)).card ≤
            kA + qP + (if ∃ x ∈ A, D.Adj v2 x then 0 else 1) + (if ∃ x ∈ A, D.Adj v3 x then 0 else 1) := by
          let LA := Finset.univ.filter (fun x : ↥Sp => x.1 ∈ A ∧ ∀ z : W, ¬ D.Adj x.1 z)
          let LH := Finset.univ.filter (fun x : ↥Sp => x.1 ∈ H ∧ ∀ y : ↥Sp, ¬ Fp.Adj x y)
          have hsub : Finset.univ.filter (fun x : ↥Sp => ∀ y : ↥Sp, ¬ Fp.Adj x y) ⊆ LA ∪ LH := by
            intro x hx
            have hno := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_union.mp x.2 with hxH | hxA
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxH, hno⟩)
            · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxA, fun z hDxz => ?_⟩)
              have hzA : z ∈ A := by
                by_contra hznotA
                by_cases hzH : z ∈ H
                · exact hno_AH x.1 hxA z hzH hDxz
                · exact (hno_AB x.1 hxA z (fun h => hzH (h ▸ hu1H)) (fun h => hzH (h ▸ hu2H))
                    (fun h => hzH (h ▸ hu3H)) hznotA).1 hDxz
              exact hno ⟨z, Finset.mem_union_right _ hzA⟩ ⟨hzA, hDxz⟩
          have hLA_eq : LA.card = kA := by
            refine Finset.card_bij (fun x _ => x.1) (fun x hx => Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2)
              (fun _ _ _ _ h => Subtype.ext h) (fun w hw => ⟨⟨w, Finset.mem_union_right _ (Finset.mem_filter.mp hw).1⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩, rfl⟩)
          have hLH_le : LH.card ≤ qP + (if ∃ x ∈ A, D.Adj v2 x then 0 else 1) + (if ∃ x ∈ A, D.Adj v3 x then 0 else 1) := by
            have hsub3 : LH ⊆ (if ∃ x ∈ A, D.Adj u1 x then ∅ else {u1p}) ∪
                ((if ∃ x ∈ A, D.Adj v2 x then ∅ else {v2p}) ∪ (if ∃ x ∈ A, D.Adj v3 x then ∅ else {v3p})) := by
              intro x hx
              have hx' := (Finset.mem_filter.mp hx).2
              rcases (hH_iff x.1).mp hx'.1 with h | h | h
              · have hxq : x = u1p := Subtype.ext h; subst hxq
                have hno1 : ¬ ∃ a ∈ A, D.Adj u1 a := fun ⟨a, haA, hDa⟩ => hx'.2 ⟨a, Finset.mem_union_right _ haA⟩ ⟨haA, hDa⟩
                exact Finset.mem_union_left _ (by simp [hno1])
              · have hxq : x = v2p := Subtype.ext h; subst hxq
                have hno2 : ¬ ∃ a ∈ A, D.Adj v2 a := fun ⟨a, haA, hDa⟩ => hx'.2 ⟨a, Finset.mem_union_right _ haA⟩ ⟨haA, hDa⟩
                exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simp [hno2]))
              · have hxq : x = v3p := Subtype.ext h; subst hxq
                have hno3 : ¬ ∃ a ∈ A, D.Adj v3 a := fun ⟨a, haA, hDa⟩ => hx'.2 ⟨a, Finset.mem_union_right _ haA⟩ ⟨haA, hDa⟩
                exact Finset.mem_union_right _ (Finset.mem_union_right _ (by simp [hno3]))
            have hc1 := Finset.card_le_card hsub3
            have hc2 := Finset.card_union_le (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p})
              ((if ∃ x ∈ A, D.Adj v2 x then (∅ : Finset ↥Sp) else {v2p}) ∪ (if ∃ x ∈ A, D.Adj v3 x then (∅ : Finset ↥Sp) else {v3p}))
            have hc3 := Finset.card_union_le (if ∃ x ∈ A, D.Adj v2 x then (∅ : Finset ↥Sp) else {v2p})
              (if ∃ x ∈ A, D.Adj v3 x then (∅ : Finset ↥Sp) else {v3p})
            have c1 : (if ∃ x ∈ A, D.Adj u1 x then (∅ : Finset ↥Sp) else {u1p}).card = qP := by dsimp only [qP]; split_ifs <;> simp
            have c2 : (if ∃ x ∈ A, D.Adj v2 x then (∅ : Finset ↥Sp) else {v2p}).card = (if ∃ x ∈ A, D.Adj v2 x then 0 else 1) := by split_ifs <;> simp
            have c3 : (if ∃ x ∈ A, D.Adj v3 x then (∅ : Finset ↥Sp) else {v3p}).card = (if ∃ x ∈ A, D.Adj v3 x then 0 else 1) := by split_ifs <;> simp
            omega
          have hc1 := Finset.card_le_card hsub; have hc2 := Finset.card_union_le LA LH; omega
        have hFp_roots_inj : Function.Injective rootsP := by
          intro j1 j2 h
          have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 := by omega
          have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 := by omega
          rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp only [rootsP, h1, h2] at h
          · exact Fin.ext (by omega)
          · exact absurd (congrArg Subtype.val h) h1v2
          · exact absurd (congrArg Subtype.val h) h1v3
          · exact absurd (congrArg Subtype.val h).symm h1v2
          · exact Fin.ext (by omega)
          · exact absurd (congrArg Subtype.val h) hv23
          · exact absurd (congrArg Subtype.val h).symm h1v3
          · exact absurd (congrArg Subtype.val h).symm hv23
          · exact Fin.ext (by omega)
        have hFp_roots_iff : ∀ w : ↥Sp, (∀ u : ↥Sp, ¬ Fp.Adj u w) ↔ ∃ j : Fin 3, rootsP j = w := by
          intro w; constructor
          · intro hno
            rcases Finset.mem_union.mp w.2 with hwH | hwA
            · rcases (hH_iff w.1).mp hwH with h | h | h
              · exact ⟨⟨0, by decide⟩, by dsimp only [rootsP, u1p]; exact Subtype.ext h.symm⟩
              · exact ⟨⟨1, by decide⟩, by dsimp only [rootsP, v2p]; exact Subtype.ext h.symm⟩
              · exact ⟨⟨2, by decide⟩, by dsimp only [rootsP, v3p]; exact Subtype.ext h.symm⟩
            · exfalso
              obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [hA_in w.1 hwA]; omega :
                0 < (Finset.univ.filter (fun z : W => D.Adj z w.1)).card)
              have hDzw := (Finset.mem_filter.mp hz).2
              have hzSp : z ∈ Sp := by
                by_contra hznot
                exact (hno_AB w.1 hwA z (fun h => hznot (Finset.mem_union_left _ (h ▸ hu1H)))
                  (fun h => hznot (Finset.mem_union_left _ (h ▸ hu2H)))
                  (fun h => hznot (Finset.mem_union_left _ (h ▸ hu3H)))
                  (fun h => hznot (Finset.mem_union_right _ h))).2 hDzw
              exact hno ⟨z, hzSp⟩ ⟨hwA, hDzw⟩
          · rintro ⟨j, rfl⟩ u hu
            have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
            rcases hj with h | h | h <;> simp only [rootsP, h] at hu
            · exact hu1A hu.1
            · exact hv2A hu.1
            · exact hv3A hu.1
        obtain ⟨fR, hfR_inj, hfR_rng, hfR_adj, hfR_rt⟩ := greedy_right_interval Fp
          ⟨rkP, fun x y h => hrkP x y h.2⟩ (fun w x1 x2 h1 h2 => Subtype.ext (hA_in_uniq w.1 h1.1 x1.1 x2.1 h1.2 h2.2))
          G hR r lenR htot rootsP hFp_roots_inj hFp_roots_iff hlenR3 qP (by dsimp only [qP]; split_ifs <;> omega)
          (fun j hj u hu => by
            have hj0 : j.val = 0 := by dsimp only [qP] at hj; split_ifs at hj <;> omega
            have hno1 : ¬ ∃ x ∈ A, D.Adj u1 x := by dsimp only [qP] at hj; split_ifs at hj with h; omega; exact h
            simp only [rootsP, hj0] at hu; exact hno1 ⟨u.1, hu.1, hu.2⟩)
          (by rw [Fintype.card_coe, hSp_card]; omega)
        -- Left side: Fm on Sm with roots [v3, v2, u1], lenL = r + 3!
        let Fm : Digraph ↥Sm := ⟨fun x y => x.1 ∈ B ∧ D.Adj x.1 y.1⟩
        let u1m : ↥Sm := ⟨u1, Finset.mem_union_left _ hu1H⟩
        let v2m : ↥Sm := ⟨v2, Finset.mem_union_left _ hv2H⟩
        let v3m : ↥Sm := ⟨v3, Finset.mem_union_left _ hv3H⟩
        let rootsM : Fin 3 → ↥Sm := fun j => match j.val with | 0 => v3m | 1 => v2m | _ => u1m
        have hFm_roots_inj : Function.Injective rootsM := by
          intro j1 j2 h
          have h1 : j1.val = 0 ∨ j1.val = 1 ∨ j1.val = 2 := by omega
          have h2 : j2.val = 0 ∨ j2.val = 1 ∨ j2.val = 2 := by omega
          rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp only [rootsM, h1, h2] at h
          · exact Fin.ext (by omega)
          · exact absurd (congrArg Subtype.val h).symm hv23
          · exact absurd (congrArg Subtype.val h).symm h1v3
          · exact absurd (congrArg Subtype.val h) hv23
          · exact Fin.ext (by omega)
          · exact absurd (congrArg Subtype.val h).symm h1v2
          · exact absurd (congrArg Subtype.val h) h1v3
          · exact absurd (congrArg Subtype.val h) h1v2
          · exact Fin.ext (by omega)
        have hFm_roots_iff : ∀ w : ↥Sm, (∀ u : ↥Sm, ¬ Fm.Adj w u) ↔ ∃ j : Fin 3, rootsM j = w := by
          intro w; constructor
          · intro hno
            rcases Finset.mem_union.mp w.2 with hwH | hwB
            · rcases (hH_iff w.1).mp hwH with h | h | h
              · exact ⟨⟨2, by decide⟩, by dsimp only [rootsM, u1m]; exact Subtype.ext h.symm⟩
              · exact ⟨⟨1, by decide⟩, by dsimp only [rootsM, v2m]; exact Subtype.ext h.symm⟩
              · exact ⟨⟨0, by decide⟩, by dsimp only [rootsM, v3m]; exact Subtype.ext h.symm⟩
            · exfalso
              have hw_notHA := (Finset.mem_sdiff.mp hwB).2
              have hc := hB_out w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hw_notHA (Finset.mem_union_right _ h))
              obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun z : W => D.Adj w.1 z)).card)
              have hDwz := (Finset.mem_filter.mp hz).2
              have hzSm : z ∈ Sm := by
                by_contra hznot
                have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
                have hzA : z ∈ A := by
                  by_contra hnotA; exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩))
                exact (hno_AB z hzA w.1 (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                  (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                  (fun h => hw_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                  (fun h => hw_notHA (Finset.mem_union_right _ h))).2 hDwz
              exact hno ⟨z, hzSm⟩ ⟨hwB, hDwz⟩
          · rintro ⟨j, rfl⟩ u hu
            have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
            rcases hj with h | h | h <;> simp only [rootsM, h] at hu
            · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hv3H)
            · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hv2H)
            · exact (Finset.mem_sdiff.mp hu.1).2 (Finset.mem_union_left _ hu1H)
        have hFm_leaves : (Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x)).card ≤ kB + 1 := by
          let Lsub : Finset ↥Sm := (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ∪ {u1m}
          have hsub : Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x) ⊆ Lsub := by
            intro x hx
            have hno := (Finset.mem_filter.mp hx).2
            rcases Finset.mem_union.mp x.2 with hxH | hxB
            · rcases (hH_iff x.1).mp hxH with h | h | h
              · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (Subtype.ext h))
              · exfalso; obtain ⟨b, hbB, hDb⟩ := hv2_in; exact hno ⟨b, Finset.mem_union_right _ hbB⟩ ⟨hbB, h ▸ hDb⟩
              · exfalso; obtain ⟨b, hbB, hDb⟩ := hv3_in; exact hno ⟨b, Finset.mem_union_right _ hbB⟩ ⟨hbB, h ▸ hDb⟩
            · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxB, fun z hDzx => ?_⟩)
              have hzB : z ∈ B := by
                by_contra hznotB
                by_cases hzH : z ∈ H
                · exact hno_HB z hzH x.1 hxB hDzx
                · have hzA : z ∈ A := by
                    by_contra hnotA; exact hznotB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hzH hnotA⟩)
                  have hx_notHA := (Finset.mem_sdiff.mp hxB).2
                  exact (hno_AB z hzA x.1 (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu1H)))
                    (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu2H)))
                    (fun h => hx_notHA (Finset.mem_union_left _ (h ▸ hu3H)))
                    (fun h => hx_notHA (Finset.mem_union_right _ h))).1 hDzx
              exact hno ⟨z, Finset.mem_union_right _ hzB⟩ ⟨hzB, hDzx⟩
          have hcardB : (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)).card = kB := by
            refine Finset.card_bij (fun x _ => x.1) (fun x hx => Finset.mem_filter.mpr (Finset.mem_filter.mp hx).2)
              (fun _ _ _ _ h => Subtype.ext h) (fun w hw => ⟨⟨w, Finset.mem_union_right _ (Finset.mem_filter.mp hw).1⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩, rfl⟩)
          have hc1 : (Finset.univ.filter (fun x : ↥Sm => ∀ y : ↥Sm, ¬ Fm.Adj y x)).card ≤
              ((Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ∪ ({u1m} : Finset ↥Sm)).card :=
            Finset.card_le_card hsub
          have hc2 := Finset.card_union_le (Finset.univ.filter (fun x : ↥Sm => x.1 ∈ B ∧ ∀ z : W, ¬ D.Adj z x.1)) ({u1m} : Finset ↥Sm)
          rw [hcardB, Finset.card_singleton] at hc2; omega
        obtain ⟨fL, hfL_inj, hfL_rng, hfL_adj, hfL_rt⟩ := greedy_left_interval Fm
          ⟨rkM, fun x y h => hrkM x y h.1 h.2⟩ (fun w y1 y2 h1 h2 => Subtype.ext (hB_out_uniq w.1 h1.1 y1.1 y2.1 h1.2 h2.2))
          G hL (r + 2) (r + 3) (by omega) (by omega)
          rootsM hFm_roots_inj hFm_roots_iff (by omega) 0 (by omega) (fun _ h => by omega)
          (by rw [Fintype.card_coe, hSm_card]; omega)
        have hfRu1 : fR u1p = ⟨r, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨0, by omega⟩
        have hfRv2 : fR v2p = ⟨r + 1, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨1, by omega⟩
        have hfRv3 : fR v3p = ⟨r + 2, by omega⟩ := by simpa [rootsP] using hfR_rt ⟨2, by omega⟩
        have hfLv3 : fL v3m = ⟨r + 2, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨0, by omega⟩
        have hfLv2 : fL v2m = ⟨r + 1, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨1, by omega⟩
        have hfLu1 : fL u1m = ⟨r, by omega⟩ := by simpa [rootsM] using hfL_rt ⟨2, by omega⟩
        let idx : W → Fin (Fintype.card V) := fun w =>
          if hw : w ∈ Sp then fR ⟨w, hw⟩ else fL ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩)⟩
        have hidx_Sm : ∀ w (hw : w ∈ Sm), idx w = fL ⟨w, hw⟩ := by
          intro w hw
          by_cases hwSp : w ∈ Sp
          · simp only [idx, hwSp, ↓reduceDIte]
            have hwH : w ∈ H := (Finset.mem_union.mp hw).elim id (fun hB => absurd hwSp (Finset.mem_sdiff.mp hB).2)
            rcases (hH_iff w).mp hwH with rfl | rfl | rfl
            · exact hfRu1.trans hfLu1.symm
            · exact hfRv2.trans hfLv2.symm
            · exact hfRv3.trans hfLv3.symm
          · simp only [idx, hwSp, ↓reduceDIte]
        have hG01 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 1, by omega⟩) :=
          median_adj_succ hR ⟨r, by omega⟩ (by change r + 1 < Fintype.card V; omega)
        refine ⟨⟨fun w => σ (idx w), ?_⟩, ?_⟩
        · intro x y hDxy
          by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
          · simp only [idx, hxSp, hySp, ↓reduceDIte]
            by_cases hyA : y ∈ A
            · exact hfR_adj ⟨x, hxSp⟩ ⟨y, hySp⟩ ⟨hyA, hDxy⟩
            · have hyH : y ∈ H := (Finset.mem_union.mp hySp).resolve_right hyA
              have hxH : x ∈ H := (Finset.mem_union.mp hxSp).elim id (fun hxA => absurd hDxy (hno_AH x hxA y hyH))
              rcases (hH_iff x).mp hxH with rfl | rfl | rfl <;> rcases (hH_iff y).mp hyH with rfl | rfl | rfl
              · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
              · rw [hfRu1, hfRv2]; exact hG01
              · rw [hfRu1, hfRv3]; exact hG02
              · exact absurd hDxy (not_adj_rev_of_isOrientation hO hDv12)
              · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
              · exact absurd hDxy hno_v23.1
              · exact absurd hDxy (not_adj_rev_of_isOrientation hO hDv13)
              · exact absurd hDxy hno_v23.2
              · exact absurd rfl (T.ne_of_adj (hO.1 _ _ hDxy))
          · exfalso
            have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
            rcases Finset.mem_union.mp hxSp with hxH | hxA
            · exact hno_HB x hxH y hyB hDxy
            · exact (hno_AB x hxA y (fun h => hySp (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hySp (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hySp (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hySp (Finset.mem_union_right _ h))).1 hDxy
          · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
            have hyH : y ∈ H := (Finset.mem_union.mp hySp).elim id (fun hyA =>
              absurd hDxy (hno_AB y hyA x (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu1H)))
                (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu2H)))
                (fun h => hxSp (Finset.mem_union_left _ (h ▸ hu3H)))
                (fun h => hxSp (Finset.mem_union_right _ h))).2)
            rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_left _ hyH)]
            exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_left _ hyH⟩ ⟨hxB, hDxy⟩
          · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
            have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
            rw [hidx_Sm x (Finset.mem_union_right _ hxB), hidx_Sm y (Finset.mem_union_right _ hyB)]
            exact hfL_adj ⟨x, Finset.mem_union_right _ hxB⟩ ⟨y, Finset.mem_union_right _ hyB⟩ ⟨hxB, hDxy⟩
        · intro x y hEq
          have hi := σ.injective hEq
          by_cases hxSp : x ∈ Sp <;> by_cases hySp : y ∈ Sp
          · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi; exact congrArg Subtype.val (hfR_inj hi)
          · exfalso
            have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hySp⟩
            simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
            have h1 := (hfR_rng ⟨x, hxSp⟩).1; have h2 := (hfL_rng ⟨y, Finset.mem_union_right _ hyB⟩).2
            have hv : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = (fR ⟨x, hxSp⟩).val := congrArg Fin.val hi.symm
            rcases (by omega : (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r ∨
                (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 1 ∨
                (fL ⟨y, Finset.mem_union_right _ hyB⟩).val = r + 2) with h | h | h
            · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
              have hy1 : y = u1 := congrArg Subtype.val (hfL_inj heq)
              exact hySp (Finset.mem_union_left _ (hy1 ▸ hu1H))
            · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL v2m := Fin.ext (by rw [hfLv2]; exact h)
              have hy2 : y = v2 := congrArg Subtype.val (hfL_inj heq)
              exact hySp (Finset.mem_union_left _ (hy2 ▸ hv2H))
            · have heq : fL ⟨y, Finset.mem_union_right _ hyB⟩ = fL v3m := Fin.ext (by rw [hfLv3]; exact h)
              have hy3 : y = v3 := congrArg Subtype.val (hfL_inj heq)
              exact hySp (Finset.mem_union_left _ (hy3 ▸ hv3H))
          · exfalso
            have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxSp⟩
            simp only [idx, hxSp, hySp, ↓reduceDIte] at hi
            have h1 := (hfR_rng ⟨y, hySp⟩).1; have h2 := (hfL_rng ⟨x, Finset.mem_union_right _ hxB⟩).2
            have hv : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = (fR ⟨y, hySp⟩).val := congrArg Fin.val hi
            rcases (by omega : (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r ∨
                (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 1 ∨
                (fL ⟨x, Finset.mem_union_right _ hxB⟩).val = r + 2) with h | h | h
            · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL u1m := Fin.ext (by rw [hfLu1]; exact h)
              have hx1 : x = u1 := congrArg Subtype.val (hfL_inj heq)
              exact hxSp (Finset.mem_union_left _ (hx1 ▸ hu1H))
            · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL v2m := Fin.ext (by rw [hfLv2]; exact h)
              have hx2 : x = v2 := congrArg Subtype.val (hfL_inj heq)
              exact hxSp (Finset.mem_union_left _ (hx2 ▸ hv2H))
            · have heq : fL ⟨x, Finset.mem_union_right _ hxB⟩ = fL v3m := Fin.ext (by rw [hfLv3]; exact h)
              have hx3 : x = v3 := congrArg Subtype.val (hfL_inj heq)
              exact hxSp (Finset.mem_union_left _ (hx3 ▸ hv3H))
          · simp only [idx, hxSp, hySp, ↓reduceDIte] at hi; exact congrArg Subtype.val (hfL_inj hi)
      -- Subcase 2a helper: given (v2, v3) with ∃ c2 ∈ A, D.Adj v2 c2!
      have hsub2a : ∀ (v2 v3 : W), (v2 = u2 ∧ v3 = u3 ∨ v2 = u3 ∧ v3 = u2) →
          (∃ c2 ∈ A, D.Adj v2 c2) → Embeds D G := by
        intro v2 v3 hswap ⟨c2, hc2A, hDv2c2⟩
        let r := B.card + kB + 1
        have htot4 : r + (4 + A.card + kA) ≤ Fintype.card V := by omega
        by_cases hG02 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩)
        · refine hglue_02 v2 v3 hswap r (3 + A.card + kA) (by omega) (by omega) (by omega) ?_ hG02
          have hpos : (if ∃ x ∈ A, D.Adj v2 x then 0 else 1) = 0 := if_pos ⟨c2, hc2A, hDv2c2⟩
          rw [hpos]; split_ifs <;> omega
        · exact embeds_heart_three_S3plus_2a_skip2 D hO G u1 u2 u3 h12 h13 h23 hD12 hD13 hno_23
            A hu1A hu2A hu3A hA_in hB_out hno_AB hno_AH hno_HB rkP hrkP rkM hrkM σ hR hL
            hu2_in hu3_in v2 v3 hswap c2 hc2A hDv2c2 r (show B.card + kB + 1 ≤ r from le_rfl) htot4 hG02
      -- Split into Subcase 2a (u2 or u3 has a child in A) vs Subcase 2b (neither has a child in A)!
      by_cases hu2_out : ∃ x ∈ A, D.Adj u2 x
      · exact hsub2a u2 u3 (Or.inl ⟨rfl, rfl⟩) hu2_out
      · by_cases hu3_out : ∃ x ∈ A, D.Adj u3 x
        · exact hsub2a u3 u2 (Or.inr ⟨rfl, rfl⟩) hu3_out
        · -- Subcase 2b: neither u2 nor u3 has any child in A!
          push Not at hu2_out hu3_out
          let r := B.card + kB
          have htot4 : r + (4 + A.card + kA) ≤ Fintype.card V := by omega
          by_cases hG02 : G.Adj (σ ⟨r, by omega⟩) (σ ⟨r + 2, by omega⟩)
          · refine hglue_02 u2 u3 (Or.inl ⟨rfl, rfl⟩) r (4 + A.card + kA) (by omega) htot4 (by omega) ?_ hG02
            split_ifs <;> omega
          · exact embeds_heart_three_S3plus_2b_skip2 D hO G u1 u2 u3 h12 h13 h23 hD12 hD13 hno_23
              A hu1A hu2A hu3A hA_in hB_out hno_AB hno_AH hno_HB rkP hrkP rkM hrkM σ hR hL
              hu2_in hu3_in hu2_out hu3_out r (show B.card + kB ≤ r from le_rfl) htot4 hG02
    · push Not at hu3_in; exact hred_h2 u3 u2 (Or.inr ⟨rfl, rfl⟩) hu3_in
  · push Not at hu2_in; exact hred_h2 u2 u3 (Or.inl ⟨rfl, rfl⟩) hu2_in

-- MAIN THEOREM (Theorem 4.3): Every oriented tree with Heart order h = 3 (P_3^+, S_3^+, or S_3^-)
-- and n - k >= 4 internal vertices embeds in every tournament on 2n - 2 vertices!
-- (Combined with embeds_internal_le_three for n - k <= 3 and embeds_heart_two for h <= 2,
--  completely proves ALL Heart h <= 3 trees — strictly beating Ai & Lian Aug 2026: 2n + 1 -> 2n - 2!)
theorem embeds_heart_three {n : ℕ} (hn : 4 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hTree : IsOrientedTree D)
    {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hInt4 : 4 ≤ n - (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card)
    (hH3 : ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)) :
    Embeds D G := by
  classical
  obtain ⟨u1, u2, u3, h12, h13, h23, htop, A, hu1A, hu2A, hu3A, hA_in, hB_out, hno_AB⟩ := hH3
  rcases htop with ⟨hD12, hD23⟩ | ⟨hD12, hD13⟩ | ⟨hD21, hD31⟩
  · exact embeds_heart_three_P3plus hn D hW hTree G hV hG hInt4 u1 u2 u3 h12 h13 h23 hD12 hD23
      A hu1A hu2A hu3A hA_in hB_out hno_AB
  · exact embeds_heart_three_S3plus hn D hW hTree G hV hG hInt4 u1 u2 u3 h12 h13 h23 hD12 hD13
      A hu1A hu2A hu3A hA_in hB_out hno_AB
  · -- S_3^-: exact arc-reversal dual of S_3^+ (swapping A and B = univ \ ({u1, u2, u3} ∪ A))!
    obtain ⟨T, hT, hO⟩ := hTree
    let Drev : Digraph W := ⟨fun x y => D.Adj y x⟩
    let Grev : Digraph V := ⟨fun u v => G.Adj v u⟩
    have hOrev : Drev.IsOrientation T :=
      ⟨fun x y h => (hO.1 y x h).symm, fun x y h => hO.2 y x h.symm⟩
    have hGrev : Grev.IsTournament := ⟨fun v => hG.1 v, fun u v hne => hG.2 v u hne.symm⟩
    have hInt4_rev : 4 ≤ n - (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)).card = 1)).card := by
      have heq : Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w)).card = 1) =
        Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1) := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have : Finset.univ.filter (fun z : W => Drev.Adj w z ∨ Drev.Adj z w) =
            Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) := by
          ext z; simp only [Drev, Finset.mem_filter, Finset.mem_univ, true_and]; exact or_comm
        rw [this]
      rw [heq]; exact hInt4
    let B : Finset W := Finset.univ \ ({u1, u2, u3} ∪ A)
    have hB_mem : ∀ y : W, y ∈ B ↔ y ≠ u1 ∧ y ≠ u2 ∧ y ≠ u3 ∧ y ∉ A := by
      intro y; simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, hA⟩; exact ⟨h1, h2, h3, hA⟩
      · rintro ⟨h1, h2, h3, hA⟩; exact ⟨⟨h1, h2, h3⟩, hA⟩
    obtain ⟨⟨fn, hfn⟩, hfinj⟩ := embeds_heart_three_S3plus hn Drev hW ⟨T, hT, hOrev⟩ Grev hV hGrev hInt4_rev
      u1 u2 u3 h12 h13 h23 hD21 hD31 B
      (fun h => ((hB_mem u1).mp h).1 rfl) (fun h => ((hB_mem u2).mp h).2.1 rfl) (fun h => ((hB_mem u3).mp h).2.2.1 rfl)
      (fun x hxB => by
        obtain ⟨h1, h2, h3, hA⟩ := (hB_mem x).mp hxB
        simpa [Drev] using hB_out x h1 h2 h3 hA)
      (fun y hy1 hy2 hy3 hyB => by
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB ((hB_mem y).mpr ⟨hy1, hy2, hy3, hnotA⟩)
        simpa [Drev] using hA_in y hyA)
      (fun x hxB y hy1 hy2 hy3 hyB => by
        obtain ⟨h1, h2, h3, hA⟩ := (hB_mem x).mp hxB
        have hyA : y ∈ A := by
          by_contra hnotA; exact hyB ((hB_mem y).mpr ⟨hy1, hy2, hy3, hnotA⟩)
        have h := hno_AB y hyA x h1 h2 h3 hA
        exact ⟨h.1, h.2⟩)
    exact ⟨⟨fn, fun hxy => hfn hxy⟩, hfinj⟩


end HeartThree

section HeartFourShared

open SimpleGraph Digraph OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1

lemma heart_four_structure
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hT : T.IsTree) (hO : D.IsOrientation T)
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ T.Adj (u j) (u i))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x) :
    let H : Finset W := Finset.univ.image u
    let B : Finset W := Finset.univ \ (H ∪ A)
    -- (1) No arcs from A to H
    (∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i)) ∧
    -- (2) No arcs from H to B
    (∀ i : Fin 4, ∀ y ∈ B, ¬ D.Adj (u i) y) ∧
    -- (3) Acyclic rank on H ∪ A for F^+ (all arcs with head in A)
    (∃ rkP : ↥(H ∪ A) → ℕ, ∀ x y : ↥(H ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y) ∧
    -- (4) Acyclic reverse rank on H ∪ B for F^- (all arcs with tail in B)
    (∃ rkM : ↥(H ∪ B) → ℕ, ∀ x y : ↥(H ∪ B), x.1 ∈ B → D.Adj x.1 y.1 → rkM y < rkM x) ∧
    -- (5) Leaf count bound: kA + kB <= k
    (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
    (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤
    (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ∧
    -- (6) Branch-count lower bounds: 2 * |maskP| <= |A| + kA and 2 * |maskM| <= |B| + kB
    2 * (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ∧
    2 * (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card ≤
      B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ∧
    -- (7) Card identity: 4 + |A| + |B| = |W|
    4 + A.card + B.card = Fintype.card W := by
  classical
  intro H B
  have hH_card : H.card = 4 := by
    rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Fintype.card_fin]
  have hHA_disj' : Disjoint H A := by
    rw [Finset.disjoint_left]
    intro x hxH hxA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
    exact hHA_disj i hxA
  have hcard_id : 4 + A.card + B.card = Fintype.card W := by
    have h1 : (H ∪ A).card = 4 + A.card := by
      rw [Finset.card_union_of_disjoint hHA_disj', hH_card]
    have h2 : B.card = Fintype.card W - (H ∪ A).card := by
      simp only [B, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have h3 : (H ∪ A).card ≤ Fintype.card W := Finset.card_le_univ _
    omega
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hH_reach : ∀ (S : Finset W) (hHS : H ⊆ S) (i : Fin 4),
      (T.induce (S : Set W)).Reachable ⟨u ⟨0, by decide⟩, hHS (hu_memH ⟨0, by decide⟩)⟩
        ⟨u i, hHS (hu_memH i)⟩ := by
    intro S hHS
    have hrec : ∀ m : ℕ, ∀ i : Fin 4, i.val = m →
        (T.induce (S : Set W)).Reachable ⟨u ⟨0, by decide⟩, hHS (hu_memH ⟨0, by decide⟩)⟩
          ⟨u i, hHS (hu_memH i)⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi
        by_cases h0 : i.val = 0
        · have hieq : i = ⟨0, by decide⟩ := Fin.ext h0
          subst hieq; exact SimpleGraph.Reachable.refl _
        · obtain ⟨j, hjlt, hjadj⟩ := hH_parent i h0
          have hrj := ih j.val (by omega) j rfl
          have hstep : (T.induce (S : Set W)).Adj ⟨u j, hHS (hu_memH j)⟩ ⟨u i, hHS (hu_memH i)⟩ := hjadj
          exact hrj.trans hstep.reachable
    exact fun i => hrec i.val i rfl
  have hSplus_tree : (T.induce ((H ∪ A : Finset W) : Set W)).IsTree := by
    refine isTree_induce_of_connected_gate hT Finset.subset_union_left (hu_memH ⟨0, by decide⟩) ?_ ?_
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact hH_reach (H ∪ A) Finset.subset_union_left i
    · intro x hx hxH y hyS hTxy
      have hxA : x ∈ A := (Finset.mem_union.mp hx).resolve_left hxH
      have hyH : ∀ i : Fin 4, y ≠ u i := fun i h => hyS (Finset.mem_union_left _ (h ▸ hu_memH i))
      have hyA : y ∉ A := fun h => hyS (Finset.mem_union_right _ h)
      rcases adj_or_rev_of_isOrientation hO hTxy with h | h
      · exact (hno_AB x hxA y hyH hyA).1 h
      · exact (hno_AB x hxA y hyH hyA).2 h
  have hSminus_tree : (T.induce ((H ∪ B : Finset W) : Set W)).IsTree := by
    refine isTree_induce_of_connected_gate hT Finset.subset_union_left (hu_memH ⟨0, by decide⟩) ?_ ?_
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact hH_reach (H ∪ B) Finset.subset_union_left i
    · intro y hy hyH x hxS hTyx
      have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left hyH
      have hy_notHA : y ∉ H ∪ A := (Finset.mem_sdiff.mp hyB).2
      have hyH' : ∀ i : Fin 4, y ≠ u i := fun i h => hy_notHA (Finset.mem_union_left _ (h ▸ hu_memH i))
      have hyA : y ∉ A := fun h => hy_notHA (Finset.mem_union_right _ h)
      have hxA : x ∈ A := by
        by_contra hxnotA
        have hxH : x ∉ H := fun h => hxS (Finset.mem_union_left _ h)
        exact hxS (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
          (Finset.mem_union.mp h).elim hxH hxnotA⟩))
      rcases adj_or_rev_of_isOrientation hO hTyx with h | h
      · exact (hno_AB x hxA y hyH' hyA).2 h
      · exact (hno_AB x hxA y hyH' hyA).1 h
  -- Step 1: Re-orient ONLY H-edges away from u 0 on H ∪ A
  let Dp : Digraph ↥(H ∪ A) := ⟨fun x y =>
    if x.1 ∈ H ∧ y.1 ∈ H then
      ∃ i j : Fin 4, u i = x.1 ∧ u j = y.1 ∧ i.val < j.val ∧ T.Adj x.1 y.1
    else D.Adj x.1 y.1⟩
  have hOp : Dp.IsOrientation (T.induce ((H ∪ A : Finset W) : Set W)) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      dsimp only [Dp] at hxy
      split_ifs at hxy with hHH
      · rcases hxy with ⟨_, _, _, _, _, hTxy⟩; exact hTxy
      · exact hO.1 x.1 y.1 hxy
    · intro x y hTxy
      dsimp only [Dp]
      by_cases hHH : x.1 ∈ H ∧ y.1 ∈ H
      · have hHH' : y.1 ∈ H ∧ x.1 ∈ H := ⟨hHH.2, hHH.1⟩
        rw [if_pos hHH, if_pos hHH']
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hHH.1
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hHH.2
        have hij : i ≠ j := fun h => T.ne_of_adj hTxy (hi.symm.trans (h ▸ hj))
        constructor
        · rintro ⟨i1, j1, hi1, hj1, hlt1, _⟩ ⟨i2, j2, hi2, hj2, hlt2, _⟩
          have : i1 = j2 := hu_inj (hi1.trans hj2.symm)
          have : j1 = i2 := hu_inj (hj1.trans hi2.symm)
          omega
        · intro hnot
          have hij_lt : i.val < j.val := by
            by_contra hge
            exact hnot ⟨j, i, hj, hi, by omega, hTxy.symm⟩
          exact ⟨i, j, hi, hj, hij_lt, hTxy⟩
      · have hHH' : ¬ (y.1 ∈ H ∧ x.1 ∈ H) := fun h => hHH ⟨h.2, h.1⟩
        rw [if_neg hHH, if_neg hHH']
        exact hO.2 x.1 y.1 hTxy
  have hsum_p : ∑ w : ↥(H ∪ A), (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card =
      Fintype.card ↥(H ∪ A) - 1 := by
    have h0 := sum_indeg_eq_card_sub_one hSplus_tree hOp
    have hcard_eq : Fintype.card ↥((H ∪ A : Finset W) : Set W) = Fintype.card ↥(H ∪ A) :=
      Fintype.card_congr (Equiv.refl _)
    rw [← hcard_eq, ← h0]
    refine Finset.sum_equiv (Equiv.refl _) (fun _ => by simp) (fun w _ => ?_)
    refine Finset.card_bij (fun z _ => z)
      (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩)
      (fun _ _ _ _ h => h)
      (fun z hz => ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩, rfl⟩)
  have hA_in_p : ∀ x : ↥(H ∪ A), x.1 ∈ A →
      (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z x)).card = 1 := by
    intro x hxA
    have hxnotH : x.1 ∉ H := Finset.disjoint_right.mp hHA_disj' hxA
    have hbij : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z x)).card =
        (Finset.univ.filter (fun z : W => D.Adj z x.1)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz
        have hDzx := (Finset.mem_filter.mp hz).2
        dsimp only [Dp] at hDzx
        have hnotHH : ¬ (z.1 ∈ H ∧ x.1 ∈ H) := fun h => hxnotH h.2
        simp only [hnotHH, ↓reduceIte] at hDzx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDzx⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDzx := (Finset.mem_filter.mp hz).2
        have hzHA : z ∈ H ∪ A := by
          by_contra hznot
          have hzH : ∀ i : Fin 4, z ≠ u i := fun i h => hznot (Finset.mem_union_left _ (h ▸ hu_memH i))
          have hzA : z ∉ A := fun h => hznot (Finset.mem_union_right _ h)
          exact (hno_AB x.1 hxA z hzH hzA).2 hDzx
        refine ⟨⟨z, hzHA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        dsimp only [Dp]
        have hnotHH : ¬ (z ∈ H ∧ x.1 ∈ H) := fun h => hxnotH h.2
        simp only [hnotHH, ↓reduceIte]
        exact hDzx
    rw [hbij]; exact hA_in x.1 hxA
  let u0p : ↥(H ∪ A) := ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH ⟨0, by decide⟩)⟩
  have hne0_ge1 : ∀ w : ↥(H ∪ A), w ≠ u0p →
      1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card := by
    intro w hw
    by_cases hwA : w.1 ∈ A
    · rw [hA_in_p w hwA]
    · have hwH : w.1 ∈ H := (Finset.mem_union.mp w.2).resolve_right hwA
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
      have hi0 : i.val ≠ 0 := by
        intro h0
        apply hw; apply Subtype.ext
        exact hi.symm.trans (congrArg u (Fin.ext h0))
      obtain ⟨j, hjlt, hjadj⟩ := hH_parent i hi0
      refine Finset.one_le_card.mpr ⟨⟨u j, Finset.mem_union_left _ (hu_memH j)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      dsimp only [Dp]
      rw [if_pos ⟨hu_memH j, hwH⟩]
      exact ⟨j, i, rfl, hi, hjlt, hi ▸ hjadj⟩
  have hall_in_p : ∀ w : ↥(H ∪ A), w ≠ u0p →
      (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card = 1 := by
    have hge : Fintype.card ↥(H ∪ A) - 1 ≤
        ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card := by
      calc Fintype.card ↥(H ∪ A) - 1
          = (Finset.univ.erase u0p).card := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        _ = ∑ _w ∈ Finset.univ.erase u0p, 1 := by simp
        _ ≤ ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card :=
            Finset.sum_le_sum (fun w hw => hne0_ge1 w (Finset.mem_erase.mp hw).1)
    have hsplit : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u0p)).card +
        ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card =
        Fintype.card ↥(H ∪ A) - 1 := by
      have hs := Finset.add_sum_erase Finset.univ
        (fun w : ↥(H ∪ A) => (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card)
        (Finset.mem_univ u0p)
      exact hs.trans hsum_p
    have hsum_eq : ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card =
        ∑ _w ∈ Finset.univ.erase u0p, 1 := by
      have hc : (Finset.univ.erase u0p).card = Fintype.card ↥(H ∪ A) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hc]; omega
    intro w hw
    have hle := Finset.sum_eq_sum_iff_of_le (s := Finset.univ.erase u0p)
      (fun x hx => hne0_ge1 x (Finset.mem_erase.mp hx).1)
    exact (hle.mp hsum_eq.symm w (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)).symm
  have hu0_in_0 : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u0p)).card = 0 := by
    have hsplit : (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u0p)).card +
        ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card =
        Fintype.card ↥(H ∪ A) - 1 := by
      have hs := Finset.add_sum_erase Finset.univ
        (fun w : ↥(H ∪ A) => (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card)
        (Finset.mem_univ u0p)
      exact hs.trans hsum_p
    have hsum_eq : ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card =
        Fintype.card ↥(H ∪ A) - 1 := by
      calc ∑ w ∈ Finset.univ.erase u0p, (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card
          = ∑ _w ∈ Finset.univ.erase u0p, 1 :=
            Finset.sum_congr rfl (fun w hw => hall_in_p w (Finset.mem_erase.mp hw).1)
        _ = (Finset.univ.erase u0p).card := by simp
        _ = Fintype.card ↥(H ∪ A) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i) := by
    intro x hxA i hDxu
    have hxnotH : x ∉ H := Finset.disjoint_right.mp hHA_disj' hxA
    let xp : ↥(H ∪ A) := ⟨x, Finset.mem_union_right _ hxA⟩
    let uip : ↥(H ∪ A) := ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩
    have hDpxu : Dp.Adj xp uip := by
      dsimp only [Dp, xp, uip]
      have : ¬ (x ∈ H ∧ u i ∈ H) := fun h => hxnotH h.1
      simp only [this, ↓reduceIte]; exact hDxu
    by_cases hi0 : i.val = 0
    · have huip_eq : uip = u0p := Subtype.ext (congrArg u (Fin.ext hi0))
      have hpos : 0 < (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z u0p)).card :=
        Finset.card_pos.mpr ⟨xp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huip_eq ▸ hDpxu⟩⟩
      omega
    · obtain ⟨j, hjlt, hjadj⟩ := hH_parent i hi0
      let ujp : ↥(H ∪ A) := ⟨u j, Finset.mem_union_left _ (hu_memH j)⟩
      have hDpju : Dp.Adj ujp uip := by
        dsimp only [Dp, ujp, uip]
        rw [if_pos ⟨hu_memH j, hu_memH i⟩]
        exact ⟨j, i, rfl, rfl, hjlt, hjadj⟩
      have hne : xp ≠ ujp := fun h => hxnotH (by
        have heq : x = u j := congrArg Subtype.val h
        exact heq ▸ hu_memH j)
      have hne0 : uip ≠ u0p := fun h => hi0 (congrArg Fin.val (hu_inj (congrArg Subtype.val h)))
      have hcard1 := hall_in_p uip hne0
      have htwo : 2 ≤ (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z uip)).card := by
        have hsub : ({xp, ujp} : Finset ↥(H ∪ A)) ⊆ Finset.univ.filter (fun z => Dp.Adj z uip) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDpxu⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDpju⟩
        calc 2 = ({xp, ujp} : Finset ↥(H ∪ A)).card := (Finset.card_pair hne).symm
          _ ≤ (Finset.univ.filter (fun z => Dp.Adj z uip)).card := Finset.card_le_card hsub
      omega
  obtain ⟨_, _, hrkP_all⟩ := out_arborescence_rank_and_root hSplus_tree hOp u0p (fun w hw => by
    have hcard_eq : (Finset.univ.filter (fun z : ↥((H ∪ A : Finset W) : Set W) => Dp.Adj z w)).card =
        (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card := by
      refine Finset.card_bij (fun z _ => z) (fun z hz => by simpa using hz) (fun _ _ _ _ h => h)
        (fun z hz => ⟨z, by simpa using hz, rfl⟩)
    rw [hcard_eq]
    exact hall_in_p w hw)
  let rkP : ↥(H ∪ A) → ℕ := fun x => (T.induce ((H ∪ A : Finset W) : Set W)).dist u0p x
  have hrkP : ∀ x y : ↥(H ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y := by
    intro x y hyA hxy
    apply hrkP_all x y
    dsimp only [Dp]
    have : ¬ (x.1 ∈ H ∧ y.1 ∈ H) := fun h => Finset.disjoint_right.mp hHA_disj' hyA h.2
    simp only [this, ↓reduceIte]; exact hxy
  -- Step 2: Dually on H ∪ B (reverse B-arcs + orient H-edges away from u 0)
  let Dm : Digraph ↥(H ∪ B) := ⟨fun x y =>
    if x.1 ∈ H ∧ y.1 ∈ H then
      ∃ i j : Fin 4, u i = x.1 ∧ u j = y.1 ∧ i.val < j.val ∧ T.Adj x.1 y.1
    else D.Adj y.1 x.1⟩
  have hOm : Dm.IsOrientation (T.induce ((H ∪ B : Finset W) : Set W)) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      dsimp only [Dm] at hxy
      split_ifs at hxy with hHH
      · rcases hxy with ⟨_, _, _, _, _, hTxy⟩; exact hTxy
      · exact (hO.1 y.1 x.1 hxy).symm
    · intro x y hTxy
      dsimp only [Dm]
      by_cases hHH : x.1 ∈ H ∧ y.1 ∈ H
      · have hHH' : y.1 ∈ H ∧ x.1 ∈ H := ⟨hHH.2, hHH.1⟩
        rw [if_pos hHH, if_pos hHH']
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hHH.1
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hHH.2
        have hij : i ≠ j := fun h => T.ne_of_adj hTxy (hi.symm.trans (h ▸ hj))
        constructor
        · rintro ⟨i1, j1, hi1, hj1, hlt1, _⟩ ⟨i2, j2, hi2, hj2, hlt2, _⟩
          have : i1 = j2 := hu_inj (hi1.trans hj2.symm)
          have : j1 = i2 := hu_inj (hj1.trans hi2.symm)
          omega
        · intro hnot
          have hij_lt : i.val < j.val := by
            by_contra hge
            exact hnot ⟨j, i, hj, hi, by omega, hTxy.symm⟩
          exact ⟨i, j, hi, hj, hij_lt, hTxy⟩
      · have hHH' : ¬ (y.1 ∈ H ∧ x.1 ∈ H) := fun h => hHH ⟨h.2, h.1⟩
        rw [if_neg hHH, if_neg hHH']
        exact hO.2 y.1 x.1 hTxy.symm
  have hsum_m : ∑ w : ↥(H ∪ B), (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card =
      Fintype.card ↥(H ∪ B) - 1 := by
    have h0 := sum_indeg_eq_card_sub_one hSminus_tree hOm
    have hcard_eq : Fintype.card ↥((H ∪ B : Finset W) : Set W) = Fintype.card ↥(H ∪ B) :=
      Fintype.card_congr (Equiv.refl _)
    rw [← hcard_eq, ← h0]
    refine Finset.sum_equiv (Equiv.refl _) (fun _ => by simp) (fun w _ => ?_)
    refine Finset.card_bij (fun z _ => z)
      (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩)
      (fun _ _ _ _ h => h)
      (fun z hz => ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩, rfl⟩)
  have hHB_disj' : Disjoint H B := Finset.disjoint_left.mpr (fun x hxH hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_left _ hxH))
  have hB_in_m : ∀ y : ↥(H ∪ B), y.1 ∈ B →
      (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z y)).card = 1 := by
    intro y hyB
    have hynotH : y.1 ∉ H := Finset.disjoint_right.mp hHB_disj' hyB
    have hynotHA : y.1 ∉ H ∪ A := (Finset.mem_sdiff.mp hyB).2
    have hyH : ∀ i : Fin 4, y.1 ≠ u i := fun i h => hynotHA (Finset.mem_union_left _ (h ▸ hu_memH i))
    have hyA : y.1 ∉ A := fun h => hynotHA (Finset.mem_union_right _ h)
    have hbij : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z y)).card =
        (Finset.univ.filter (fun z : W => D.Adj y.1 z)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz
        have hDzy := (Finset.mem_filter.mp hz).2
        dsimp only [Dm] at hDzy
        have : ¬ (z.1 ∈ H ∧ y.1 ∈ H) := fun h => hynotH h.2
        simp only [this, ↓reduceIte] at hDzy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDzy⟩
      · intro z1 _ z2 _ h; exact Subtype.ext h
      · intro z hz
        have hDyz := (Finset.mem_filter.mp hz).2
        have hzHB : z ∈ H ∪ B := by
          by_contra hznot
          have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
          have hzA : z ∈ A := by
            by_contra hznotA
            exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
              (Finset.mem_union.mp h).elim hzH hznotA⟩))
          exact (hno_AB z hzA y.1 hyH hyA).2 hDyz
        refine ⟨⟨z, hzHB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        dsimp only [Dm]
        have : ¬ (z ∈ H ∧ y.1 ∈ H) := fun h => hynotH h.2
        simp only [this, ↓reduceIte]; exact hDyz
    rw [hbij]; exact hB_out y.1 hyH hyA
  let u0m : ↥(H ∪ B) := ⟨u ⟨0, by decide⟩, Finset.mem_union_left _ (hu_memH ⟨0, by decide⟩)⟩
  have hne0_ge1_m : ∀ w : ↥(H ∪ B), w ≠ u0m →
      1 ≤ (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card := by
    intro w hw
    by_cases hwB : w.1 ∈ B
    · rw [hB_in_m w hwB]
    · have hwH : w.1 ∈ H := (Finset.mem_union.mp w.2).resolve_right hwB
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
      have hi0 : i.val ≠ 0 := by
        intro h0; apply hw; apply Subtype.ext
        exact hi.symm.trans (congrArg u (Fin.ext h0))
      obtain ⟨j, hjlt, hjadj⟩ := hH_parent i hi0
      refine Finset.one_le_card.mpr ⟨⟨u j, Finset.mem_union_left _ (hu_memH j)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      dsimp only [Dm]
      rw [if_pos ⟨hu_memH j, hwH⟩]
      exact ⟨j, i, rfl, hi, hjlt, hi ▸ hjadj⟩
  have hall_in_m : ∀ w : ↥(H ∪ B), w ≠ u0m →
      (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card = 1 := by
    have hge : Fintype.card ↥(H ∪ B) - 1 ≤
        ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card := by
      calc Fintype.card ↥(H ∪ B) - 1
          = (Finset.univ.erase u0m).card := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        _ = ∑ _w ∈ Finset.univ.erase u0m, 1 := by simp
        _ ≤ ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card :=
            Finset.sum_le_sum (fun w hw => hne0_ge1_m w (Finset.mem_erase.mp hw).1)
    have hsplit : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z u0m)).card +
        ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card =
        Fintype.card ↥(H ∪ B) - 1 := by
      have hs := Finset.add_sum_erase Finset.univ
        (fun w : ↥(H ∪ B) => (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card)
        (Finset.mem_univ u0m)
      exact hs.trans hsum_m
    have hsum_eq : ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card =
        ∑ _w ∈ Finset.univ.erase u0m, 1 := by
      have hc : (Finset.univ.erase u0m).card = Fintype.card ↥(H ∪ B) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hc]; omega
    intro w hw
    have hle := Finset.sum_eq_sum_iff_of_le (s := Finset.univ.erase u0m)
      (fun x hx => hne0_ge1_m x (Finset.mem_erase.mp hx).1)
    exact (hle.mp hsum_eq.symm w (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩)).symm
  have hu0_in_0_m : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z u0m)).card = 0 := by
    have hsplit : (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z u0m)).card +
        ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card =
        Fintype.card ↥(H ∪ B) - 1 := by
      have hs := Finset.add_sum_erase Finset.univ
        (fun w : ↥(H ∪ B) => (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card)
        (Finset.mem_univ u0m)
      exact hs.trans hsum_m
    have hsum_eq : ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card =
        Fintype.card ↥(H ∪ B) - 1 := by
      calc ∑ w ∈ Finset.univ.erase u0m, (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card
          = ∑ _w ∈ Finset.univ.erase u0m, 1 :=
            Finset.sum_congr rfl (fun w hw => hall_in_m w (Finset.mem_erase.mp hw).1)
        _ = (Finset.univ.erase u0m).card := by simp
        _ = Fintype.card ↥(H ∪ B) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have hno_HB : ∀ i : Fin 4, ∀ y ∈ B, ¬ D.Adj (u i) y := by
    intro i y hyB hDuy
    have hynotH : y ∉ H := Finset.disjoint_right.mp hHB_disj' hyB
    let ym : ↥(H ∪ B) := ⟨y, Finset.mem_union_right _ hyB⟩
    let uim : ↥(H ∪ B) := ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩
    have hDmyu : Dm.Adj ym uim := by
      dsimp only [Dm, ym, uim]
      have : ¬ (y ∈ H ∧ u i ∈ H) := fun h => hynotH h.1
      simp only [this, ↓reduceIte]; exact hDuy
    by_cases hi0 : i.val = 0
    · have huim_eq : uim = u0m := Subtype.ext (congrArg u (Fin.ext hi0))
      have hpos : 0 < (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z u0m)).card :=
        Finset.card_pos.mpr ⟨ym, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huim_eq ▸ hDmyu⟩⟩
      omega
    · obtain ⟨j, hjlt, hjadj⟩ := hH_parent i hi0
      let ujm : ↥(H ∪ B) := ⟨u j, Finset.mem_union_left _ (hu_memH j)⟩
      have hDmju : Dm.Adj ujm uim := by
        dsimp only [Dm, ujm, uim]
        rw [if_pos ⟨hu_memH j, hu_memH i⟩]
        exact ⟨j, i, rfl, rfl, hjlt, hjadj⟩
      have hne : ym ≠ ujm := fun h => hynotH (by
        have heq : y = u j := congrArg Subtype.val h
        exact heq ▸ hu_memH j)
      have hne0 : uim ≠ u0m := fun h => hi0 (congrArg Fin.val (hu_inj (congrArg Subtype.val h)))
      have hcard1 := hall_in_m uim hne0
      have htwo : 2 ≤ (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z uim)).card := by
        have hsub : ({ym, ujm} : Finset ↥(H ∪ B)) ⊆ Finset.univ.filter (fun z => Dm.Adj z uim) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDmyu⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDmju⟩
        calc 2 = ({ym, ujm} : Finset ↥(H ∪ B)).card := (Finset.card_pair hne).symm
          _ ≤ (Finset.univ.filter (fun z => Dm.Adj z uim)).card := Finset.card_le_card hsub
      omega
  obtain ⟨_, _, hrkM_all⟩ := out_arborescence_rank_and_root hSminus_tree hOm u0m (fun w hw => by
    have hcard_eq : (Finset.univ.filter (fun z : ↥((H ∪ B : Finset W) : Set W) => Dm.Adj z w)).card =
        (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card := by
      refine Finset.card_bij (fun z _ => z) (fun z hz => by simpa using hz) (fun _ _ _ _ h => h)
        (fun z hz => ⟨z, by simpa using hz, rfl⟩)
    rw [hcard_eq]
    exact hall_in_m w hw)
  let rkM : ↥(H ∪ B) → ℕ := fun x => (T.induce ((H ∪ B : Finset W) : Set W)).dist u0m x
  have hrkM : ∀ x y : ↥(H ∪ B), x.1 ∈ B → D.Adj x.1 y.1 → rkM y < rkM x := by
    intro x y hxB hxy
    apply hrkM_all y x
    dsimp only [Dm]
    have : ¬ (y.1 ∈ H ∧ x.1 ∈ H) := fun h => Finset.disjoint_right.mp hHB_disj' hxB h.2
    simp only [this, ↓reduceIte]; exact hxy
  -- Step 3: Leaf bound kA + kB <= k
  have hleaves_le : (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
      (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤
      (Finset.univ.filter (fun w : W =>
        (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
    have hdisj : Disjoint (A.filter (fun x => ∀ z : W, ¬ D.Adj x z))
        (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)) :=
      Finset.disjoint_left.mpr (fun w hwA hwB =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwB).1).2
          (Finset.mem_union_right _ (Finset.mem_filter.mp hwA).1))
    rw [← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_le_card (fun w hw => ?_)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hw with hwA | hwB
    · obtain ⟨hxA, hnoOut⟩ := Finset.mem_filter.mp hwA
      have heq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj z w) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_left (hnoOut z), Or.inr⟩
      rw [heq]; exact hA_in w hxA
    · obtain ⟨hyB, hnoIn⟩ := Finset.mem_filter.mp hwB
      have hynotHA := (Finset.mem_sdiff.mp hyB).2
      have heq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj w z) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_right (hnoIn z), Or.inl⟩
      rw [heq]
      exact hB_out w (fun i h => hynotHA (Finset.mem_union_left _ (h ▸ hu_memH i)))
        (fun h => hynotHA (Finset.mem_union_right _ h))
  -- Step 4: Disjoint-branch lower bounds 2*|maskP| <= |A| + kA and 2*|maskM| <= |B| + kB
  have hrootP_ex : ∃ rP : ↥(H ∪ A) → Fin 4,
      (∀ i : Fin 4, rP ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = i) ∧
      (∀ x y : ↥(H ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rP y = rP x) := by
    have hbuild : ∀ m : ℕ, ∃ f : ↥(H ∪ A) → Fin 4,
        (∀ i : Fin 4, f ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = i) ∧
        (∀ x y : ↥(H ∪ A), rkP y < m → y.1 ∈ A → D.Adj x.1 y.1 → f y = f x) := by
      intro m
      induction m with
      | zero =>
        refine ⟨fun w => if hw : w.1 ∈ H then Classical.choose (Finset.mem_image.mp hw) else ⟨0, by decide⟩,
          fun i => ?_, fun _ _ h => by omega⟩
        simp only [hu_memH i, ↓reduceDIte]
        exact hu_inj (Classical.choose_spec (Finset.mem_image.mp (hu_memH i))).2
      | succ m ih =>
        obtain ⟨f, hfH, hfstep⟩ := ih
        refine ⟨fun w => if hwA : w.1 ∈ A ∧ rkP w = m then
            f (Classical.choose (Finset.card_pos.mp (by rw [hA_in_p w hwA.1]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z w)).card)))
          else f w, ?_, ?_⟩
        · intro i
          have hnot : ¬ (u i ∈ A ∧ rkP ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = m) :=
            fun h => hHA_disj i h.1
          simp only [hnot, ↓reduceDIte]
          exact hfH i
        · intro x y hylt hyA hDxy
          have hxr : rkP x < rkP y := hrkP x y hyA hDxy
          have hxnot : ¬ (x.1 ∈ A ∧ rkP x = m) := fun h => by omega
          simp only [hxnot, ↓reduceDIte]
          by_cases hym : rkP y = m
          · have hyc : y.1 ∈ A ∧ rkP y = m := ⟨hyA, hym⟩
            rw [dif_pos hyc]
            let p := Classical.choose (Finset.card_pos.mp (by rw [hA_in_p y hyA]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z y)).card))
            have hp_mem := Classical.choose_spec (Finset.card_pos.mp (by rw [hA_in_p y hyA]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ A) => Dp.Adj z y)).card))
            have hDpy : Dp.Adj p y := (Finset.mem_filter.mp hp_mem).2
            have hDxy_p : Dp.Adj x y := by
              dsimp only [Dp]
              have : ¬ (x.1 ∈ H ∧ y.1 ∈ H) := fun h => Finset.disjoint_right.mp hHA_disj' hyA h.2
              simp only [this, ↓reduceIte]; exact hDxy
            have hpx : p = x := by
              have hcard1 := hA_in_p y hyA
              obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
              have hp0 : p = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDpy⟩)
              have hx0 : x = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy_p⟩)
              exact hp0.trans hx0.symm
            exact congrArg f hpx
          · have hnoty : ¬ (y.1 ∈ A ∧ rkP y = m) := fun h => hym h.2
            simp only [hnoty, ↓reduceDIte]
            exact hfstep x y (by omega) hyA hDxy
    have hneP : (Finset.univ.image rkP).Nonempty := ⟨rkP u0p, Finset.mem_image.mpr ⟨u0p, Finset.mem_univ _, rfl⟩⟩
    let M := (Finset.univ.image rkP).max' hneP + 1
    obtain ⟨f, hfH, hfstep⟩ := hbuild M
    refine ⟨f, hfH, fun x y hyA hxy => hfstep x y ?_ hyA hxy⟩
    have hle := Finset.le_max' (Finset.univ.image rkP) (rkP y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
    omega
  have hmaskP_bound : 2 * (Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)).card ≤
      A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
    obtain ⟨rP, hrPH, hrPstep⟩ := hrootP_ex
    let MP := Finset.univ.filter (fun i : Fin 4 => ∃ x ∈ A, D.Adj (u i) x)
    have hle_kA : MP.card ≤ (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
      let AL := A.filter (fun x => ∀ z : W, ¬ D.Adj x z)
      have hsub : MP ⊆ AL.image (fun x => if hx : x ∈ A then rP ⟨x, Finset.mem_union_right _ hx⟩ else ⟨0, by decide⟩) := by
        intro i hi
        obtain ⟨c, hcA, hDuc⟩ := (Finset.mem_filter.mp hi).2
        let Ai := (Finset.univ : Finset ↥(H ∪ A)).filter (fun x => x.1 ∈ A ∧ rP x = i)
        have hAine : Ai.Nonempty := by
          refine ⟨⟨c, Finset.mem_union_right _ hcA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcA, ?_⟩⟩
          rw [hrPstep ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ ⟨c, Finset.mem_union_right _ hcA⟩ hcA hDuc, hrPH i]
        obtain ⟨xm, hxm_mem, hxm_max⟩ := Finset.exists_max_image Ai rkP hAine
        obtain ⟨_, hxmA, hxm_r⟩ := Finset.mem_filter.mp hxm_mem
        have hxm_leaf : ∀ z : W, ¬ D.Adj xm.1 z := by
          intro z hDxz
          by_cases hzA : z ∈ A
          · let zp : ↥(H ∪ A) := ⟨z, Finset.mem_union_right _ hzA⟩
            have hzr : rP zp = i := (hrPstep xm zp hzA hDxz).trans hxm_r
            have hle := hxm_max zp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzA, hzr⟩)
            have hlt := hrkP xm zp hzA hDxz
            omega
          · by_cases hzH : z ∈ H
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH
              exact hno_AH xm.1 hxmA j hDxz
            · exact (hno_AB xm.1 hxmA z (fun j hj => hzH (hj ▸ hu_memH j)) hzA).1 hDxz
        refine Finset.mem_image.mpr ⟨xm.1, Finset.mem_filter.mpr ⟨hxmA, hxm_leaf⟩, ?_⟩
        simp only [hxmA, ↓reduceDIte]; exact hxm_r
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hle_A : (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card ≤ A.card := Finset.card_filter_le _ _
    dsimp only [MP] at hle_kA; omega
  -- Dually for maskM:
  have hrootM_ex : ∃ rM : ↥(H ∪ B) → Fin 4,
      (∀ i : Fin 4, rM ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = i) ∧
      (∀ x y : ↥(H ∪ B), x.1 ∈ B → D.Adj x.1 y.1 → rM x = rM y) := by
    have hbuild : ∀ m : ℕ, ∃ f : ↥(H ∪ B) → Fin 4,
        (∀ i : Fin 4, f ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = i) ∧
        (∀ x y : ↥(H ∪ B), rkM x < m → x.1 ∈ B → D.Adj x.1 y.1 → f x = f y) := by
      intro m
      induction m with
      | zero =>
        refine ⟨fun w => if hw : w.1 ∈ H then Classical.choose (Finset.mem_image.mp hw) else ⟨0, by decide⟩,
          fun i => ?_, fun _ _ h => by omega⟩
        simp only [hu_memH i, ↓reduceDIte]
        exact hu_inj (Classical.choose_spec (Finset.mem_image.mp (hu_memH i))).2
      | succ m ih =>
        obtain ⟨f, hfH, hfstep⟩ := ih
        refine ⟨fun w => if hwB : w.1 ∈ B ∧ rkM w = m then
            f (Classical.choose (Finset.card_pos.mp (by rw [hB_in_m w hwB.1]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z w)).card)))
          else f w, ?_, ?_⟩
        · intro i
          have hnot : ¬ (u i ∈ B ∧ rkM ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ = m) :=
            fun h => Finset.disjoint_left.mp hHB_disj' (hu_memH i) h.1
          simp only [hnot, ↓reduceDIte]
          exact hfH i
        · intro x y hxlt hxB hDxy
          have hyr : rkM y < rkM x := hrkM x y hxB hDxy
          have hynot : ¬ (y.1 ∈ B ∧ rkM y = m) := fun h => by omega
          simp only [hynot, ↓reduceDIte]
          by_cases hxm : rkM x = m
          · have hxc : x.1 ∈ B ∧ rkM x = m := ⟨hxB, hxm⟩
            rw [dif_pos hxc]
            let p := Classical.choose (Finset.card_pos.mp (by rw [hB_in_m x hxB]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z x)).card))
            have hp_mem := Classical.choose_spec (Finset.card_pos.mp (by rw [hB_in_m x hxB]; omega :
              0 < (Finset.univ.filter (fun z : ↥(H ∪ B) => Dm.Adj z x)).card))
            have hDmx : Dm.Adj p x := (Finset.mem_filter.mp hp_mem).2
            have hDyx_m : Dm.Adj y x := by
              dsimp only [Dm]
              have : ¬ (y.1 ∈ H ∧ x.1 ∈ H) := fun h => Finset.disjoint_right.mp hHB_disj' hxB h.2
              simp only [this, ↓reduceIte]; exact hDxy
            have hpy : p = y := by
              have hcard1 := hB_in_m x hxB
              obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
              have hp0 : p = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDmx⟩)
              have hy0 : y = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDyx_m⟩)
              exact hp0.trans hy0.symm
            exact congrArg f hpy
          · have hnotx : ¬ (x.1 ∈ B ∧ rkM x = m) := fun h => hxm h.2
            simp only [hnotx, ↓reduceDIte]
            exact hfstep x y (by omega) hxB hDxy
    have hneM : (Finset.univ.image rkM).Nonempty := ⟨rkM u0m, Finset.mem_image.mpr ⟨u0m, Finset.mem_univ _, rfl⟩⟩
    let M := (Finset.univ.image rkM).max' hneM + 1
    obtain ⟨f, hfH, hfstep⟩ := hbuild M
    refine ⟨f, hfH, fun x y hxB hxy => hfstep x y ?_ hxB hxy⟩
    have hle := Finset.le_max' (Finset.univ.image rkM) (rkM x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    omega
  have hmaskM_bound : 2 * (Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))).card ≤
      B.card + (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by
    obtain ⟨rM, hrMH, hrMstep⟩ := hrootM_ex
    let MM := Finset.univ.filter (fun i : Fin 4 => ∃ y ∈ B, D.Adj y (u i))
    have hle_kB : MM.card ≤ (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by
      let BL := B.filter (fun y => ∀ z : W, ¬ D.Adj z y)
      have hsub : MM ⊆ BL.image (fun y => if hy : y ∈ B then rM ⟨y, Finset.mem_union_right _ hy⟩ else ⟨0, by decide⟩) := by
        intro i hi
        obtain ⟨c, hcB, hDcu⟩ := (Finset.mem_filter.mp hi).2
        let Bi := (Finset.univ : Finset ↥(H ∪ B)).filter (fun y => y.1 ∈ B ∧ rM y = i)
        have hBine : Bi.Nonempty := by
          refine ⟨⟨c, Finset.mem_union_right _ hcB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcB, ?_⟩⟩
          rw [hrMstep ⟨c, Finset.mem_union_right _ hcB⟩ ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ hcB hDcu, hrMH i]
        obtain ⟨ym, hym_mem, hym_max⟩ := Finset.exists_max_image Bi rkM hBine
        obtain ⟨_, hymB, hym_r⟩ := Finset.mem_filter.mp hym_mem
        have hym_leaf : ∀ z : W, ¬ D.Adj z ym.1 := by
          intro z hDzy
          by_cases hzB : z ∈ B
          · let zm : ↥(H ∪ B) := ⟨z, Finset.mem_union_right _ hzB⟩
            have hzr : rM zm = i := (hrMstep zm ym hzB hDzy).trans hym_r
            have hle := hym_max zm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzB, hzr⟩)
            have hlt := hrkM zm ym hzB hDzy
            omega
          · by_cases hzH : z ∈ H
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH
              exact hno_HB j ym.1 hymB hDzy
            · have hzA : z ∈ A := by
                by_contra hznotA
                exact hzB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
                  (Finset.mem_union.mp h).elim hzH hznotA⟩)
              have hym_notHA := (Finset.mem_sdiff.mp hymB).2
              exact (hno_AB z hzA ym.1 (fun j hj => hym_notHA (Finset.mem_union_left _ (hj ▸ hu_memH j)))
                (fun h => hym_notHA (Finset.mem_union_right _ h))).1 hDzy
        refine Finset.mem_image.mpr ⟨ym.1, Finset.mem_filter.mpr ⟨hymB, hym_leaf⟩, ?_⟩
        simp only [hymB, ↓reduceDIte]; exact hym_r
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    have hle_B : (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card ≤ B.card := Finset.card_filter_le _ _
    dsimp only [MM] at hle_kB; omega
  exact ⟨hno_AH, hno_HB, ⟨rkP, hrkP⟩, ⟨rkM, hrkM⟩, hleaves_le, hmaskP_bound, hmaskM_bound, hcard_id⟩

-- ============================================================================
-- MODULE 2: Master Pure-Plan Glue Lemma (handles ALL L in {4,5,6} pure plans!)
-- ============================================================================

lemma embeds_heart_four_of_pure_plan
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_AH : ∀ x ∈ A, ∀ i : Fin 4, ¬ D.Adj x (u i))
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hRkP : ∃ rkP : ↥(Finset.univ.image u ∪ A) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ A), y.1 ∈ A → D.Adj x.1 y.1 → rkP x < rkP y)
    (hRkM : ∃ rkM : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → ℕ,
      ∀ x y : ↥(Finset.univ.image u ∪ (Finset.univ \ (Finset.univ.image u ∪ A))),
        x.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A) → D.Adj x.1 y.1 → rkM y < rkM x)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (lo hi : ℕ) (hlohi : lo ≤ hi) (hhi : hi < 2 * n - 2)
    (pos : Fin 4 → Fin (hi - lo + 1)) (hpos_inj : Function.Injective pos)
    (hpos_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      G.Adj (σ ⟨lo + (pos i).val, by omega⟩) (σ ⟨lo + (pos j).val, by omega⟩))
    (fR fL : Fin (hi - lo + 1) → Option (Fin 4))
    (hfree_disj : ∀ t : Fin (hi - lo + 1), (∀ i : Fin 4, pos i ≠ t) → fR t = none ∨ fL t = none)
    (hfR_inj : ∀ t1 t2 : Fin (hi - lo + 1), (∀ i, pos i ≠ t1) → (∀ i, pos i ≠ t2) →
      ∀ h : Fin 4, fR t1 = some h → fR t2 = some h → t1 = t2)
    (hfR_valid : ∀ t : Fin (hi - lo + 1), (∀ i, pos i ≠ t) → ∀ h : Fin 4, fR t = some h →
      (pos h).val < t.val ∧
      G.Adj (σ ⟨lo + (pos h).val, by omega⟩) (σ ⟨lo + t.val, by omega⟩) ∧
      ∃ c ∈ A, D.Adj (u h) c)
    (hfL_inj : ∀ t1 t2 : Fin (hi - lo + 1), (∀ i, pos i ≠ t1) → (∀ i, pos i ≠ t2) →
      ∀ h : Fin 4, fL t1 = some h → fL t2 = some h → t1 = t2)
    (hfL_valid : ∀ t : Fin (hi - lo + 1), (∀ i, pos i ≠ t) → ∀ h : Fin 4, fL t = some h →
      t.val < (pos h).val ∧
      G.Adj (σ ⟨lo + t.val, by omega⟩) (σ ⟨lo + (pos h).val, by omega⟩) ∧
      ∃ c ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj c (u h))
    (hBoundR : ∀ exhR : Finset (Fin 4),
      (∀ i ∈ exhR, ∃ t : Fin (hi - lo + 1), (∀ j, pos j ≠ t) ∧ fR t = some i) →
      ∃ qR : ℕ, qR ≤ hi - lo + 1 ∧
        (∀ t : Fin (hi - lo + 1), t.val < qR →
          (∀ i : Fin 4, pos i = t → (∀ x ∈ A, ¬ D.Adj (u i) x) ∨ i ∈ exhR) ∧
          ((∀ i : Fin 4, pos i ≠ t) → fR t = none)) ∧
        4 + A.card + (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
          2 * (Finset.univ.filter (fun t : Fin (hi - lo + 1) => (∀ i, pos i ≠ t) ∧ fR t = none)).card +
          (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card + exhR.card
          ≤ (2 * n - 2 - lo) + 1 + qR)
    (hBoundL : ∀ exhL : Finset (Fin 4),
      (∀ i ∈ exhL, ∃ t : Fin (hi - lo + 1), (∀ j, pos j ≠ t) ∧ fL t = some i) →
      ∃ qL : ℕ, qL ≤ hi - lo + 1 ∧
        (∀ t : Fin (hi - lo + 1), hi - lo - t.val < qL →
          (∀ i : Fin 4, pos i = t →
            (∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i)) ∨ i ∈ exhL) ∧
          ((∀ i : Fin 4, pos i ≠ t) → fL t = none)) ∧
        4 + (Finset.univ \ (Finset.univ.image u ∪ A)).card +
          ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card +
          2 * (Finset.univ.filter (fun t : Fin (hi - lo + 1) => (∀ i, pos i ≠ t) ∧ fL t = none)).card +
          (Finset.univ.filter (fun i : Fin 4 =>
            ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))).card + exhL.card
          ≤ (hi + 1) + 1 + qL) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let L : ℕ := hi - lo + 1
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hH_card : H.card = 4 := by
    rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Fintype.card_fin]
  have hHA_disj' : Disjoint H A := Finset.disjoint_left.mpr (fun x hxH hxA => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH; exact hHA_disj i hxA)
  have hHB_disj' : Disjoint H B := Finset.disjoint_left.mpr (fun x hxH hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_left _ hxH))
  -- ==================== RIGHT SIDE: greedy_right_interval ====================
  let DumR : Finset (Fin L) := Finset.univ.filter (fun t : Fin L => (∀ i, pos i ≠ t) ∧ fR t = none)
  let cutChildR : ∀ t : Fin L, (∀ i, pos i ≠ t) → ∀ h : Fin 4, fR t = some h → W :=
    fun t ht h hft => Classical.choose (hfR_valid t ht h hft).2.2
  have hcutR_spec : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fR t = some h),
      cutChildR t ht h hft ∈ A ∧ D.Adj (u h) (cutChildR t ht h hft) :=
    fun t ht h hft => Classical.choose_spec (hfR_valid t ht h hft).2.2
  -- Set of cut children in A (at most one per h in Fin 4)
  let isCutR : W → Prop := fun x => ∃ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fR t = some h),
    cutChildR t ht h hft = x
  have hcutR_inj_val : ∀ (t1 : Fin L) (ht1 : ∀ i, pos i ≠ t1) (h1 : Fin 4) (hf1 : fR t1 = some h1)
      (t2 : Fin L) (ht2 : ∀ i, pos i ≠ t2) (h2 : Fin 4) (hf2 : fR t2 = some h2),
      cutChildR t1 ht1 h1 hf1 = cutChildR t2 ht2 h2 hf2 → t1 = t2 := by
    intro t1 ht1 h1 hf1 t2 ht2 h2 hf2 heq
    have hc1 := hcutR_spec t1 ht1 h1 hf1
    have hc2 := hcutR_spec t2 ht2 h2 hf2
    have hcard1 := hA_in (cutChildR t1 ht1 h1 hf1) hc1.1
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have h1eq : u h1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1.2⟩)
    have h2eq : u h2 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc2.2⟩)
    have hh : h1 = h2 := hu_inj (h1eq.trans h2eq.symm)
    exact hfR_inj t1 t2 ht1 ht2 h1 hf1 (hh ▸ hf2)
  let WR := ↥(H ∪ A) ⊕ ↥DumR
  let Fp : Digraph WR := ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => b.1 ∈ A ∧ ¬ isCutR b.1 ∧ D.Adj a.1 b.1
    | _, _ => False⟩
  have hFp_rank : ∃ rk : WR → ℕ, ∀ x y, Fp.Adj x y → rk x < rk y := by
    obtain ⟨rkP, hrkP⟩ := hRkP
    refine ⟨Sum.elim rkP (fun _ => 0), fun x y hxy => ?_⟩
    cases x <;> cases y <;> simp only [Fp] at hxy
    exact hrkP _ _ hxy.1 hxy.2.2
  have hFp_in : ∀ w u1 u2 : WR, Fp.Adj u1 w → Fp.Adj u2 w → u1 = u2 := by
    intro w u1 u2 h1 h2
    cases w <;> cases u1 <;> cases u2 <;> simp only [Fp] at h1 h2
    rename_i w' a1 a2
    have hcard1 := hA_in w'.1 h1.1
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have e1 : a1.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2.2⟩)
    have e2 : a2.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2.2⟩)
    exact congrArg Sum.inl (Subtype.ext (e1.trans e2.symm))
  let rootsR : Fin L → WR := fun t =>
    if hi_ex : ∃ i : Fin 4, pos i = t then
      Sum.inl ⟨u (Classical.choose hi_ex), Finset.mem_union_left _ (hu_memH _)⟩
    else match hft : fR t with
    | none => Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi_ex ⟨i, hi⟩, hft⟩⟩
    | some h =>
      let ht : ∀ i, pos i ≠ t := fun i hi => hi_ex ⟨i, hi⟩
      Sum.inl ⟨cutChildR t ht h hft, Finset.mem_union_right _ (hcutR_spec t ht h hft).1⟩
  have hrootsR_pos : ∀ i : Fin 4, rootsR (pos i) = Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := by
    intro i
    have hex : ∃ j : Fin 4, pos j = pos i := ⟨i, rfl⟩
    simp only [rootsR, hex, ↓reduceDIte]
    have hch : Classical.choose hex = i := hpos_inj (Classical.choose_spec hex)
    rw [hch]
  have hrootsR_free_none : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (hft : fR t = none),
      rootsR t = Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hft⟩⟩ := by
    intro t ht hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsR]; rw [dif_neg hnot]; split
    · rfl
    · rename_i _ heq; rw [hft] at heq; cases heq
  have hrootsR_free_some : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fR t = some h),
      rootsR t = Sum.inl ⟨cutChildR t ht h hft, Finset.mem_union_right _ (hcutR_spec t ht h hft).1⟩ := by
    intro t ht h hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsR]; rw [dif_neg hnot]; split
    · rename_i heq; rw [hft] at heq; cases heq
    · rename_i h' heq
      have hh : h' = h := Option.some.inj (heq.symm.trans hft)
      subst hh; rfl
  have hrootsR_inj : Function.Injective rootsR := by
    intro t1 t2 heq
    by_cases h1 : ∃ i, pos i = t1 <;> by_cases h2 : ∃ i, pos i = t2
    · obtain ⟨i1, rfl⟩ := h1; obtain ⟨i2, rfl⟩ := h2
      rw [hrootsR_pos i1, hrootsR_pos i2] at heq
      have hu12 : u i1 = u i2 := congrArg Subtype.val (Sum.inl.inj heq)
      exact congrArg pos (hu_inj hu12)
    · obtain ⟨i1, rfl⟩ := h1
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      rw [hrootsR_pos i1] at heq
      cases hf2 : fR t2 with
      | none => rw [hrootsR_free_none t2 ht2 hf2] at heq; exact absurd heq (by simp)
      | some h =>
        rw [hrootsR_free_some t2 ht2 h hf2] at heq
        have hmem := (hcutR_spec t2 ht2 h hf2).1
        have heqW : u i1 = cutChildR t2 ht2 h hf2 := congrArg Subtype.val (Sum.inl.inj heq)
        exact absurd (heqW ▸ hmem) (hHA_disj i1)
    · obtain ⟨i2, rfl⟩ := h2
      have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      rw [hrootsR_pos i2] at heq
      cases hf1 : fR t1 with
      | none => rw [hrootsR_free_none t1 ht1 hf1] at heq; exact absurd heq (by simp)
      | some h =>
        rw [hrootsR_free_some t1 ht1 h hf1] at heq
        have hmem := (hcutR_spec t1 ht1 h hf1).1
        have heqW : cutChildR t1 ht1 h hf1 = u i2 := congrArg Subtype.val (Sum.inl.inj heq)
        exact absurd (heqW ▸ hmem) (hHA_disj i2)
    · have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      cases hf1 : fR t1 with
      | none =>
        rw [hrootsR_free_none t1 ht1 hf1] at heq
        cases hf2 : fR t2 with
        | none =>
          rw [hrootsR_free_none t2 ht2 hf2] at heq
          exact congrArg Subtype.val (Sum.inr.inj heq)
        | some h2' =>
          rw [hrootsR_free_some t2 ht2 h2' hf2] at heq; exact absurd heq (by simp)
      | some h1' =>
        rw [hrootsR_free_some t1 ht1 h1' hf1] at heq
        cases hf2 : fR t2 with
        | none =>
          rw [hrootsR_free_none t2 ht2 hf2] at heq; exact absurd heq (by simp)
        | some h2' =>
          rw [hrootsR_free_some t2 ht2 h2' hf2] at heq
          exact hcutR_inj_val t1 ht1 h1' hf1 t2 ht2 h2' hf2 (congrArg Subtype.val (Sum.inl.inj heq))
  have hrootsR_iff : ∀ w : WR, (∀ z, ¬ Fp.Adj z w) ↔ ∃ t : Fin L, rootsR t = w := by
    intro w
    constructor
    · intro hno
      cases w with
      | inr d =>
        have hd := Finset.mem_filter.mp d.2
        exact ⟨d.1, by rw [hrootsR_free_none d.1 hd.2.1 hd.2.2]⟩
      | inl a =>
        by_cases haH : a.1 ∈ H
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp haH
          exact ⟨pos i, by rw [hrootsR_pos i]; exact congrArg Sum.inl (Subtype.ext hi)⟩
        · have haA : a.1 ∈ A := (Finset.mem_union.mp a.2).resolve_left haH
          by_cases hcut : isCutR a.1
          · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
            exact ⟨t, by rw [hrootsR_free_some t ht h hft]; exact congrArg Sum.inl (Subtype.ext heqc)⟩
          · exfalso
            have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z a.1)).card := by
              rw [hA_in a.1 haA]; omega
            obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
            have hDza := (Finset.mem_filter.mp hz).2
            have hzHA : z ∈ H ∪ A := by
              by_contra hznot
              exact (hno_AB a.1 haA z (fun i hi => hznot (Finset.mem_union_left _ (hi ▸ hu_memH i)))
                (fun h => hznot (Finset.mem_union_right _ h))).2 hDza
            exact hno (Sum.inl ⟨z, hzHA⟩) ⟨haA, hcut, hDza⟩
    · rintro ⟨t, rfl⟩ z hFp
      by_cases h1 : ∃ i, pos i = t
      · obtain ⟨i, rfl⟩ := h1
        rw [hrootsR_pos i] at hFp
        cases z <;> simp only [Fp] at hFp
        exact hHA_disj i hFp.1
      · have ht : ∀ i, pos i ≠ t := fun i hi => h1 ⟨i, hi⟩
        cases hft : fR t with
        | none =>
          rw [hrootsR_free_none t ht hft] at hFp
          cases z <;> simp only [Fp] at hFp
        | some h =>
          rw [hrootsR_free_some t ht h hft] at hFp
          cases z <;> simp only [Fp] at hFp
          exact hFp.2.1 ⟨t, ht, h, hft, rfl⟩
  -- Exhausted right-cut heart vertices: i in Fin 4 such that u i has an A-child in D, yet NO out-edge in Fp!
  let exhR : Finset (Fin 4) := Finset.univ.filter (fun i : Fin 4 =>
    (∃ x ∈ A, D.Adj (u i) x) ∧ ∀ y : WR, ¬ Fp.Adj (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) y)
  have hexhR_cut : ∀ i ∈ exhR, ∃ t : Fin L, (∀ j, pos j ≠ t) ∧ fR t = some i := by
    intro i hi
    obtain ⟨⟨x, hxA, hDux⟩, hnoFp⟩ := (Finset.mem_filter.mp hi).2
    have hcutx : isCutR x := by
      by_contra hnc
      exact hnoFp (Sum.inl ⟨x, Finset.mem_union_right _ hxA⟩) ⟨hxA, hnc, hDux⟩
    obtain ⟨t, ht, h, hft, heqc⟩ := hcutx
    have hc := hcutR_spec t ht h hft
    have hcard1 := hA_in x hxA
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have e1 : u i = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDux⟩)
    have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
    have hhi : h = i := hu_inj (e2.trans e1.symm)
    exact ⟨t, ht, hhi ▸ hft⟩
  obtain ⟨qR, hqR_le, hqR_pref, hqR_card⟩ := hBoundR exhR hexhR_cut
  have hFp_cardW : Fintype.card WR = 4 + A.card + DumR.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
      Finset.card_union_of_disjoint hHA_disj', hH_card]
  have hFp_leaves : (Finset.univ.filter (fun w : WR => ∀ z, ¬ Fp.Adj w z)).card ≤
      (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card + DumR.card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card + exhR.card := by
    let LFp := Finset.univ.filter (fun w : WR => ∀ z, ¬ Fp.Adj w z)
    let S1 := LFp.filter (fun w => match w with | Sum.inl a => a.1 ∈ A | Sum.inr _ => False)
    let S2 := LFp.filter (fun w => match w with | Sum.inl _ => False | Sum.inr _ => True)
    let S3 := LFp.filter (fun w => match w with | Sum.inl a => a.1 ∈ H | Sum.inr _ => False)
    have hcov : LFp ⊆ S1 ∪ S2 ∪ S3 := by
      intro w hw
      cases w with
      | inr d => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, trivial⟩))
      | inl a =>
        rcases Finset.mem_union.mp a.2 with haH | haA
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, haH⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, haA⟩))
    have hS1 : S1.card ≤ (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card := by
      have hle : S1.card ≤ (S1.image (Sum.elim (fun a => a.1) (fun _ => u ⟨0, by decide⟩))).card := by
        rw [Finset.card_image_of_injOn]
        intro w1 hw1 w2 hw2 heq
        have h1 := (Finset.mem_filter.mp hw1).2
        have h2 := (Finset.mem_filter.mp hw2).2
        cases w1 <;> cases w2 <;> simp only at h1 h2 heq
        exact congrArg Sum.inl (Subtype.ext heq)
      refine hle.trans (Finset.card_le_card (fun x hx => ?_))
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hwL, hwA⟩ := Finset.mem_filter.mp hw
      cases w with
      | inr _ => exact absurd hwA id
      | inl a =>
        dsimp only [Sum.elim] at hwA ⊢
        refine Finset.mem_filter.mpr ⟨hwA, fun z hDaz => ?_⟩
        by_cases hzA : z ∈ A
        · have hnoFp := (Finset.mem_filter.mp hwL).2 (Sum.inl ⟨z, Finset.mem_union_right _ hzA⟩)
          have hcutz : isCutR z := by
            by_contra hnc; exact hnoFp ⟨hzA, hnc, hDaz⟩
          obtain ⟨t, ht, h, hft, heqc⟩ := hcutz
          have hc := hcutR_spec t ht h hft
          have hcard1 := hA_in z hzA
          obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
          have e1 : a.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDaz⟩)
          have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
          exact hHA_disj h (e2.trans e1.symm ▸ hwA)
        · by_cases hzH : z ∈ H
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH
            exact hno_AH a.1 hwA j hDaz
          · exact (hno_AB a.1 hwA z (fun j hj => hzH (hj ▸ hu_memH j)) hzA).1 hDaz
    have hS2 : S2.card ≤ DumR.card := by
      have hle : S2.card ≤ (Finset.univ : Finset ↥DumR).card := by
        have himg : S2 ⊆ (Finset.univ : Finset ↥DumR).image Sum.inr := by
          intro w hw
          cases w with
          | inl _ => exact absurd (Finset.mem_filter.mp hw).2 id
          | inr d => exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
        exact (Finset.card_le_card himg).trans Finset.card_image_le
      simpa using hle
    have hS3 : S3.card ≤ (Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)).card + exhR.card := by
      let Z0 := Finset.univ.filter (fun i : Fin 4 => ∀ x ∈ A, ¬ D.Adj (u i) x)
      have himg : S3 ⊆ (Z0 ∪ exhR).image (fun i => Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) := by
        intro w hw
        obtain ⟨hwL, hwH⟩ := Finset.mem_filter.mp hw
        cases w with
        | inr _ => exact absurd hwH id
        | inl a =>
          dsimp only at hwH
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
          refine Finset.mem_image.mpr ⟨i, ?_, congrArg Sum.inl (Subtype.ext hi)⟩
          by_cases hex : ∃ x ∈ A, D.Adj (u i) x
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex, ?_⟩)
            have hnoFp := (Finset.mem_filter.mp hwL).2
            have haeq : a = ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := Subtype.ext hi.symm
            exact haeq ▸ hnoFp
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx hD => hex ⟨x, hx, hD⟩⟩)
      exact ((Finset.card_le_card himg).trans Finset.card_image_le).trans (Finset.card_union_le _ _)
    calc LFp.card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hcov
      _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
      _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := by omega
  have hFp_pref : ∀ t : Fin L, t.val < qR → ∀ z : WR, ¬ Fp.Adj (rootsR t) z := by
    intro t htq z hFp
    have hp := hqR_pref t htq
    by_cases h1 : ∃ i, pos i = t
    · obtain ⟨i, hi⟩ := h1
      have hr : rootsR t = Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := by
        rw [← hi, hrootsR_pos i]
      rw [hr] at hFp
      rcases hp.1 i hi with hnoA | hi_exh
      · cases z <;> simp only [Fp] at hFp
        exact hnoA _ hFp.1 hFp.2.2
      · exact (Finset.mem_filter.mp hi_exh).2.2 z hFp
    · have ht : ∀ i, pos i ≠ t := fun i hi => h1 ⟨i, hi⟩
      have hnone : fR t = none := hp.2 ht
      rw [hrootsR_free_none t ht hnone] at hFp
      cases z <;> simp only [Fp] at hFp
  obtain ⟨gR, hgR_inj, hgR_range, hgR_adj, hgR_roots⟩ := greedy_right_interval Fp hFp_rank hFp_in G hR
    lo (2 * n - 2 - lo) (by omega) rootsR hrootsR_inj hrootsR_iff (by omega) qR hqR_le hFp_pref
    (by rw [hFp_cardW]; dsimp only [DumR, L] at hFp_leaves ⊢; omega)
  -- ==================== LEFT SIDE: greedy_left_interval ====================
  let DumL : Finset (Fin L) := Finset.univ.filter (fun t : Fin L => (∀ i, pos i ≠ t) ∧ fL t = none)
  let cutChildL : ∀ t : Fin L, (∀ i, pos i ≠ t) → ∀ h : Fin 4, fL t = some h → W :=
    fun t ht h hft => Classical.choose (hfL_valid t ht h hft).2.2
  have hcutL_spec : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
      cutChildL t ht h hft ∈ B ∧ D.Adj (cutChildL t ht h hft) (u h) :=
    fun t ht h hft => Classical.choose_spec (hfL_valid t ht h hft).2.2
  let isCutL : W → Prop := fun y => ∃ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
    cutChildL t ht h hft = y
  have hcutL_inj_val : ∀ (t1 : Fin L) (ht1 : ∀ i, pos i ≠ t1) (h1 : Fin 4) (hf1 : fL t1 = some h1)
      (t2 : Fin L) (ht2 : ∀ i, pos i ≠ t2) (h2 : Fin 4) (hf2 : fL t2 = some h2),
      cutChildL t1 ht1 h1 hf1 = cutChildL t2 ht2 h2 hf2 → t1 = t2 := by
    intro t1 ht1 h1 hf1 t2 ht2 h2 hf2 heq
    have hc1 := hcutL_spec t1 ht1 h1 hf1
    have hc2 := hcutL_spec t2 ht2 h2 hf2
    have hnotHA := (Finset.mem_sdiff.mp hc1.1).2
    have hcard1 := hB_out (cutChildL t1 ht1 h1 hf1)
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
      (fun h => hnotHA (Finset.mem_union_right _ h))
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have h1eq : u h1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1.2⟩)
    have h2eq : u h2 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc2.2⟩)
    have hh : h1 = h2 := hu_inj (h1eq.trans h2eq.symm)
    exact hfL_inj t1 t2 ht1 ht2 h1 hf1 (hh ▸ hf2)
  let WL := ↥(H ∪ B) ⊕ ↥DumL
  let Fm : Digraph WL := ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => a.1 ∈ B ∧ ¬ isCutL a.1 ∧ D.Adj a.1 b.1
    | _, _ => False⟩
  have hFm_rank : ∃ rk : WL → ℕ, ∀ x y, Fm.Adj x y → rk y < rk x := by
    obtain ⟨rkM, hrkM⟩ := hRkM
    refine ⟨Sum.elim rkM (fun _ => 0), fun x y hxy => ?_⟩
    cases x <;> cases y <;> simp only [Fm] at hxy
    exact hrkM _ _ hxy.1 hxy.2.2
  have hFm_out : ∀ w u1 u2 : WL, Fm.Adj w u1 → Fm.Adj w u2 → u1 = u2 := by
    intro w u1 u2 h1 h2
    cases w <;> cases u1 <;> cases u2 <;> simp only [Fm] at h1 h2
    rename_i w' b1 b2
    have hnotHA := (Finset.mem_sdiff.mp h1.1).2
    have hcard1 := hB_out w'.1
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
      (fun h => hnotHA (Finset.mem_union_right _ h))
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have e1 : b1.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2.2⟩)
    have e2 : b2.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2.2⟩)
    exact congrArg Sum.inl (Subtype.ext (e1.trans e2.symm))
  -- Left roots indexed by j : Fin L placed at hi - j.val = lo + (L - 1 - j.val)
  let revL : Fin L → Fin L := fun j => ⟨hi - lo - j.val, by omega⟩
  have hrevL_inv : ∀ j : Fin L, revL (revL j) = j := fun j => Fin.ext (by dsimp only [revL]; omega)
  have hrevL_inj : Function.Injective revL := fun j1 j2 h => by
    have := congrArg revL h; rwa [hrevL_inv, hrevL_inv] at this
  let rootsL : Fin L → WL := fun j =>
    let t := revL j
    if hi_ex : ∃ i : Fin 4, pos i = t then
      Sum.inl ⟨u (Classical.choose hi_ex), Finset.mem_union_left _ (hu_memH _)⟩
    else match hft : fL t with
    | none => Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi_ex ⟨i, hi⟩, hft⟩⟩
    | some h =>
      let ht : ∀ i, pos i ≠ t := fun i hi => hi_ex ⟨i, hi⟩
      Sum.inl ⟨cutChildL t ht h hft, Finset.mem_union_right _ (hcutL_spec t ht h hft).1⟩
  have hrootsL_pos : ∀ i : Fin 4, rootsL (revL (pos i)) = Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := by
    intro i
    have hex : ∃ k : Fin 4, pos k = pos i := ⟨i, rfl⟩
    simp only [rootsL, hrevL_inv, hex, ↓reduceDIte]
    have hch : Classical.choose hex = i := hpos_inj (Classical.choose_spec hex)
    exact congrArg Sum.inl (Subtype.ext (congrArg u hch))
  have hrootsL_free_none : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (hft : fL t = none),
      rootsL (revL t) = Sum.inr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hft⟩⟩ := by
    intro t ht hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsL]; rw [hrevL_inv, dif_neg hnot]; split
    · rfl
    · rename_i _ heq; rw [hft] at heq; cases heq
  have hrootsL_free_some : ∀ (t : Fin L) (ht : ∀ i, pos i ≠ t) (h : Fin 4) (hft : fL t = some h),
      rootsL (revL t) = Sum.inl ⟨cutChildL t ht h hft, Finset.mem_union_right _ (hcutL_spec t ht h hft).1⟩ := by
    intro t ht h hft
    have hnot : ¬ ∃ i : Fin 4, pos i = t := fun ⟨i, hi⟩ => ht i hi
    dsimp only [rootsL]; rw [hrevL_inv, dif_neg hnot]; split
    · rename_i heq; rw [hft] at heq; cases heq
    · rename_i h' heq
      have hh : h' = h := Option.some.inj (heq.symm.trans hft)
      subst hh; rfl
  have hrootsL_inj : Function.Injective rootsL := by
    intro j1 j2 heq
    apply hrevL_inj
    set t1 := revL j1
    set t2 := revL j2
    have heq' : rootsL (revL t1) = rootsL (revL t2) := by rwa [hrevL_inv, hrevL_inv]
    by_cases h1 : ∃ i, pos i = t1 <;> by_cases h2 : ∃ i, pos i = t2
    · obtain ⟨i1, hi1⟩ := h1; obtain ⟨i2, hi2⟩ := h2
      rw [← hi1, ← hi2, hrootsL_pos i1, hrootsL_pos i2] at heq'
      have hu12 : u i1 = u i2 := congrArg Subtype.val (Sum.inl.inj heq')
      rw [← hi1, ← hi2, hu_inj hu12]
    · obtain ⟨i1, hi1⟩ := h1
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      rw [← hi1, hrootsL_pos i1] at heq'
      cases hf2 : fL t2 with
      | none => rw [hrootsL_free_none t2 ht2 hf2] at heq'; exact absurd heq' (by simp)
      | some h =>
        rw [hrootsL_free_some t2 ht2 h hf2] at heq'
        have hmem := (hcutL_spec t2 ht2 h hf2).1
        have heqW : u i1 = cutChildL t2 ht2 h hf2 := congrArg Subtype.val (Sum.inl.inj heq')
        exact absurd (heqW ▸ hmem) (Finset.disjoint_left.mp hHB_disj' (hu_memH i1))
    · obtain ⟨i2, hi2⟩ := h2
      have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      rw [← hi2, hrootsL_pos i2] at heq'
      cases hf1 : fL t1 with
      | none => rw [hrootsL_free_none t1 ht1 hf1] at heq'; exact absurd heq' (by simp)
      | some h =>
        rw [hrootsL_free_some t1 ht1 h hf1] at heq'
        have hmem := (hcutL_spec t1 ht1 h hf1).1
        have heqW : cutChildL t1 ht1 h hf1 = u i2 := congrArg Subtype.val (Sum.inl.inj heq')
        exact absurd (heqW ▸ hmem) (Finset.disjoint_left.mp hHB_disj' (hu_memH i2))
    · have ht1 : ∀ i, pos i ≠ t1 := fun i hi => h1 ⟨i, hi⟩
      have ht2 : ∀ i, pos i ≠ t2 := fun i hi => h2 ⟨i, hi⟩
      cases hf1 : fL t1 with
      | none =>
        rw [hrootsL_free_none t1 ht1 hf1] at heq'
        cases hf2 : fL t2 with
        | none =>
          rw [hrootsL_free_none t2 ht2 hf2] at heq'
          exact congrArg Subtype.val (Sum.inr.inj heq')
        | some h2' => rw [hrootsL_free_some t2 ht2 h2' hf2] at heq'; exact absurd heq' (by simp)
      | some h1' =>
        rw [hrootsL_free_some t1 ht1 h1' hf1] at heq'
        cases hf2 : fL t2 with
        | none => rw [hrootsL_free_none t2 ht2 hf2] at heq'; exact absurd heq' (by simp)
        | some h2' =>
          rw [hrootsL_free_some t2 ht2 h2' hf2] at heq'
          exact hcutL_inj_val t1 ht1 h1' hf1 t2 ht2 h2' hf2 (congrArg Subtype.val (Sum.inl.inj heq'))
  have hrootsL_iff : ∀ w : WL, (∀ z, ¬ Fm.Adj w z) ↔ ∃ j : Fin L, rootsL j = w := by
    intro w
    constructor
    · intro hno
      cases w with
      | inr d =>
        have hd := Finset.mem_filter.mp d.2
        exact ⟨revL d.1, by rw [hrootsL_free_none d.1 hd.2.1 hd.2.2]⟩
      | inl a =>
        by_cases haH : a.1 ∈ H
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp haH
          exact ⟨revL (pos i), by rw [hrootsL_pos i]; exact congrArg Sum.inl (Subtype.ext hi)⟩
        · have haB : a.1 ∈ B := (Finset.mem_union.mp a.2).resolve_left haH
          by_cases hcut : isCutL a.1
          · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
            exact ⟨revL t, by rw [hrootsL_free_some t ht h hft]; exact congrArg Sum.inl (Subtype.ext heqc)⟩
          · exfalso
            have hnotHA := (Finset.mem_sdiff.mp haB).2
            have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj a.1 z)).card := by
              rw [hB_out a.1 (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
                (fun h => hnotHA (Finset.mem_union_right _ h))]; omega
            obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
            have hDaz := (Finset.mem_filter.mp hz).2
            have hzHB : z ∈ H ∪ B := by
              by_contra hznot
              have hzH : z ∉ H := fun h => hznot (Finset.mem_union_left _ h)
              have hzA : z ∈ A := by
                by_contra hznotA
                exact hznot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
                  (Finset.mem_union.mp h).elim hzH hznotA⟩))
              exact (hno_AB z hzA a.1 (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
                (fun h => hnotHA (Finset.mem_union_right _ h))).2 hDaz
            exact hno (Sum.inl ⟨z, hzHB⟩) ⟨haB, hcut, hDaz⟩
    · rintro ⟨j, rfl⟩ z hFm
      set t := revL j
      have hrj : rootsL j = rootsL (revL t) := by rw [hrevL_inv]
      rw [hrj] at hFm
      by_cases h1 : ∃ i, pos i = t
      · obtain ⟨i, hi⟩ := h1
        rw [← hi, hrootsL_pos i] at hFm
        cases z <;> simp only [Fm] at hFm
        exact Finset.disjoint_left.mp hHB_disj' (hu_memH i) hFm.1
      · have ht : ∀ i, pos i ≠ t := fun i hi => h1 ⟨i, hi⟩
        cases hft : fL t with
        | none =>
          rw [hrootsL_free_none t ht hft] at hFm
          cases z <;> simp only [Fm] at hFm
        | some h =>
          rw [hrootsL_free_some t ht h hft] at hFm
          cases z <;> simp only [Fm] at hFm
          exact hFm.2.1 ⟨t, ht, h, hft, rfl⟩
  let exhL : Finset (Fin 4) := Finset.univ.filter (fun i : Fin 4 =>
    (∃ y ∈ B, D.Adj y (u i)) ∧ ∀ z : WL, ¬ Fm.Adj z (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩))
  have hexhL_cut : ∀ i ∈ exhL, ∃ t : Fin L, (∀ j, pos j ≠ t) ∧ fL t = some i := by
    intro i hi
    obtain ⟨⟨y, hyB, hDyu⟩, hnoFm⟩ := (Finset.mem_filter.mp hi).2
    have hcuty : isCutL y := by
      by_contra hnc
      exact hnoFm (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) ⟨hyB, hnc, hDyu⟩
    obtain ⟨t, ht, h, hft, heqc⟩ := hcuty
    have hc := hcutL_spec t ht h hft
    have hnotHA := (Finset.mem_sdiff.mp hyB).2
    have hcard1 := hB_out y (fun k hk => hnotHA (Finset.mem_union_left _ (hk ▸ hu_memH k)))
      (fun h' => hnotHA (Finset.mem_union_right _ h'))
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
    have e1 : u i = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDyu⟩)
    have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
    have hhi : h = i := hu_inj (e2.trans e1.symm)
    exact ⟨t, ht, hhi ▸ hft⟩
  obtain ⟨qL, hqL_le, hqL_pref, hqL_card⟩ := hBoundL exhL hexhL_cut
  have hFm_cardW : Fintype.card WL = 4 + B.card + DumL.card := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
      Finset.card_union_of_disjoint hHB_disj', hH_card]
  have hFm_leaves : (Finset.univ.filter (fun w : WL => ∀ z, ¬ Fm.Adj z w)).card ≤
      (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card + DumL.card +
      (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card + exhL.card := by
    let LFm := Finset.univ.filter (fun w : WL => ∀ z, ¬ Fm.Adj z w)
    let S1 := LFm.filter (fun w => match w with | Sum.inl a => a.1 ∈ B | Sum.inr _ => False)
    let S2 := LFm.filter (fun w => match w with | Sum.inl _ => False | Sum.inr _ => True)
    let S3 := LFm.filter (fun w => match w with | Sum.inl a => a.1 ∈ H | Sum.inr _ => False)
    have hcov : LFm ⊆ S1 ∪ S2 ∪ S3 := by
      intro w hw
      cases w with
      | inr d => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, trivial⟩))
      | inl a =>
        rcases Finset.mem_union.mp a.2 with haH | haB
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, haH⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, haB⟩))
    have hS1 : S1.card ≤ (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card := by
      have hle : S1.card ≤ (S1.image (Sum.elim (fun a => a.1) (fun _ => u ⟨0, by decide⟩))).card := by
        rw [Finset.card_image_of_injOn]
        intro w1 hw1 w2 hw2 heq
        have h1 := (Finset.mem_filter.mp hw1).2
        have h2 := (Finset.mem_filter.mp hw2).2
        cases w1 <;> cases w2 <;> simp only at h1 h2 heq
        exact congrArg Sum.inl (Subtype.ext heq)
      refine hle.trans (Finset.card_le_card (fun y hy => ?_))
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hwL, hwB⟩ := Finset.mem_filter.mp hw
      cases w with
      | inr _ => exact absurd hwB id
      | inl a =>
        dsimp only [Sum.elim] at hwB ⊢
        refine Finset.mem_filter.mpr ⟨hwB, fun z hDza => ?_⟩
        by_cases hzB : z ∈ B
        · have hnoFm := (Finset.mem_filter.mp hwL).2 (Sum.inl ⟨z, Finset.mem_union_right _ hzB⟩)
          have hcutz : isCutL z := by
            by_contra hnc; exact hnoFm ⟨hzB, hnc, hDza⟩
          obtain ⟨t, ht, h, hft, heqc⟩ := hcutz
          have hc := hcutL_spec t ht h hft
          have hnotHA := (Finset.mem_sdiff.mp hzB).2
          have hcard1 := hB_out z (fun k hk => hnotHA (Finset.mem_union_left _ (hk ▸ hu_memH k)))
            (fun h' => hnotHA (Finset.mem_union_right _ h'))
          obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
          have e1 : a.1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDza⟩)
          have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
          exact Finset.disjoint_left.mp hHB_disj' (hu_memH h) (e2.trans e1.symm ▸ hwB)
        · by_cases hzH : z ∈ H
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hzH
            exact hno_HB j a.1 hwB hDza
          · have hzA : z ∈ A := by
              by_contra hznotA
              exact hzB (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
                (Finset.mem_union.mp h).elim hzH hznotA⟩)
            have hanotHA := (Finset.mem_sdiff.mp hwB).2
            exact (hno_AB z hzA a.1 (fun j hj => hanotHA (Finset.mem_union_left _ (hj ▸ hu_memH j)))
              (fun h => hanotHA (Finset.mem_union_right _ h))).1 hDza
    have hS2 : S2.card ≤ DumL.card := by
      have hle : S2.card ≤ (Finset.univ : Finset ↥DumL).card := by
        have himg : S2 ⊆ (Finset.univ : Finset ↥DumL).image Sum.inr := by
          intro w hw
          cases w with
          | inl _ => exact absurd (Finset.mem_filter.mp hw).2 id
          | inr d => exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
        exact (Finset.card_le_card himg).trans Finset.card_image_le
      simpa using hle
    have hS3 : S3.card ≤ (Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))).card + exhL.card := by
      let Z0 := Finset.univ.filter (fun i : Fin 4 => ∀ y ∈ B, ¬ D.Adj y (u i))
      have himg : S3 ⊆ (Z0 ∪ exhL).image (fun i => Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) := by
        intro w hw
        obtain ⟨hwL, hwH⟩ := Finset.mem_filter.mp hw
        cases w with
        | inr _ => exact absurd hwH id
        | inl a =>
          dsimp only at hwH
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwH
          refine Finset.mem_image.mpr ⟨i, ?_, congrArg Sum.inl (Subtype.ext hi)⟩
          by_cases hex : ∃ y ∈ B, D.Adj y (u i)
          · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex, ?_⟩)
            have hnoFm := (Finset.mem_filter.mp hwL).2
            have haeq : a = ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩ := Subtype.ext hi.symm
            exact haeq ▸ hnoFm
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y hy hD => hex ⟨y, hy, hD⟩⟩)
      exact ((Finset.card_le_card himg).trans Finset.card_image_le).trans (Finset.card_union_le _ _)
    calc LFm.card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hcov
      _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
      _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := by omega
  have hFm_pref : ∀ j : Fin L, j.val < qL → ∀ z : WL, ¬ Fm.Adj z (rootsL j) := by
    intro j hjq z hFm
    set t := revL j
    have htq : hi - lo - t.val < qL := by dsimp only [t, revL]; omega
    have hp := hqL_pref t htq
    have hrj : rootsL j = rootsL (revL t) := by rw [hrevL_inv]
    rw [hrj] at hFm
    by_cases h1 : ∃ i, pos i = t
    · obtain ⟨i, hi_eq⟩ := h1
      rw [← hi_eq, hrootsL_pos i] at hFm
      rcases hp.1 i hi_eq with hnoB | hi_exh
      · cases z <;> simp only [Fm] at hFm
        exact hnoB _ hFm.1 hFm.2.2
      · exact (Finset.mem_filter.mp hi_exh).2.2 z hFm
    · have ht : ∀ i, pos i ≠ t := fun i hi_eq => h1 ⟨i, hi_eq⟩
      have hnone : fL t = none := hp.2 ht
      rw [hrootsL_free_none t ht hnone] at hFm
      cases z <;> simp only [Fm] at hFm
  obtain ⟨gL, hgL_inj, hgL_range, hgL_adj, hgL_roots⟩ := greedy_left_interval Fm hFm_rank hFm_out G hL
    hi (hi + 1) (le_refl _) (by omega) rootsL hrootsL_inj hrootsL_iff (by omega) qL hqL_le hFm_pref
    (by rw [hFm_cardW]; dsimp only [B, H, DumL, L] at hFm_leaves ⊢; omega)
  -- ==================== GLUE gR (on H ∪ A) AND gL (on H ∪ B) ====================
  have hgR_u : ∀ i : Fin 4, gR (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) =
      ⟨lo + (pos i).val, by omega⟩ := by
    intro i; rw [← hrootsR_pos i]; exact hgR_roots (pos i)
  have hgL_u : ∀ i : Fin 4, gL (Sum.inl ⟨u i, Finset.mem_union_left _ (hu_memH i)⟩) =
      ⟨lo + (pos i).val, by omega⟩ := by
    intro i
    rw [← hrootsL_pos i, hgL_roots (revL (pos i))]
    apply Fin.ext; dsimp only [revL]; omega
  let φ : W → Fin (Fintype.card V) := fun w =>
    if hwHA : w ∈ H ∪ A then gR (Sum.inl ⟨w, hwHA⟩)
    else gL (Sum.inl ⟨w, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwHA⟩)⟩)
  have hφ_on_HB : ∀ w (hw : w ∈ H ∪ B), φ w = gL (Sum.inl ⟨w, hw⟩) := by
    intro w hw
    by_cases hwH : w ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH
      have hwHA : u i ∈ H ∪ A := Finset.mem_union_left _ (hu_memH i)
      simp only [φ, hwHA, ↓reduceDIte]
      rw [hgR_u i, hgL_u i]
    · have hwB : w ∈ B := (Finset.mem_union.mp hw).resolve_left hwH
      have hwnotHA : w ∉ H ∪ A := (Finset.mem_sdiff.mp hwB).2
      simp only [φ, hwnotHA, ↓reduceDIte]
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    by_cases hx : x ∈ H ∪ A <;> by_cases hy : y ∈ H ∪ A
    · simp only [φ, hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (Sum.inl.inj (hgR_inj hxy))
    · -- x ∈ H ∪ A, y ∈ B: must collide inside [lo, hi]
      exfalso
      have hyB : y ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
      simp only [φ, hx, hy, ↓reduceDIte] at hxy
      have hrx := hgR_range (Sum.inl ⟨x, hx⟩)
      have hry := hgL_range (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)
      have hval : lo ≤ (gR (Sum.inl ⟨x, hx⟩)).val ∧ (gR (Sum.inl ⟨x, hx⟩)).val ≤ hi := by
        have h1 : (gR (Sum.inl ⟨x, hx⟩)).val = (gL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩)).val :=
          congrArg Fin.val hxy
        omega
      let t : Fin L := ⟨(gR (Sum.inl ⟨x, hx⟩)).val - lo, by omega⟩
      have hRt : gR (rootsR t) = gR (Sum.inl ⟨x, hx⟩) := by
        rw [hgR_roots t]; apply Fin.ext; dsimp only [t]; omega
      have hLt : gL (rootsL (revL t)) = gL (Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩) := by
        rw [hgL_roots (revL t), ← hxy]; apply Fin.ext; dsimp only [revL, t]; omega
      have hrx_eq : rootsR t = Sum.inl ⟨x, hx⟩ := hgR_inj hRt
      have hry_eq : rootsL (revL t) = Sum.inl ⟨y, Finset.mem_union_right _ hyB⟩ := hgL_inj hLt
      -- t cannot be in range pos (otherwise y = u i ∈ H, contradicting y ∈ B!)
      have ht_free : ∀ i : Fin 4, pos i ≠ t := by
        intro i hi
        rw [← hi, hrootsL_pos i] at hry_eq
        have heq : u i = y := congrArg Subtype.val (Sum.inl.inj hry_eq)
        exact Finset.disjoint_left.mp hHB_disj' (hu_memH i) (heq ▸ hyB)
      -- By collision-freeness, fR t = none or fL t = none -> impossible since both roots are Sum.inl!
      rcases hfree_disj t ht_free with hRnone | hLnone
      · rw [hrootsR_free_none t ht_free hRnone] at hrx_eq; exact absurd hrx_eq (by simp)
      · rw [hrootsL_free_none t ht_free hLnone] at hry_eq; exact absurd hry_eq (by simp)
    · -- Symmetric: x ∈ B, y ∈ H ∪ A
      exfalso
      have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      simp only [φ, hx, hy, ↓reduceDIte] at hxy
      have hry := hgR_range (Sum.inl ⟨y, hy⟩)
      have hrx := hgL_range (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)
      have hval : lo ≤ (gR (Sum.inl ⟨y, hy⟩)).val ∧ (gR (Sum.inl ⟨y, hy⟩)).val ≤ hi := by
        have h1 : (gL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩)).val = (gR (Sum.inl ⟨y, hy⟩)).val :=
          congrArg Fin.val hxy
        omega
      let t : Fin L := ⟨(gR (Sum.inl ⟨y, hy⟩)).val - lo, by omega⟩
      have hRt : gR (rootsR t) = gR (Sum.inl ⟨y, hy⟩) := by
        rw [hgR_roots t]; apply Fin.ext; dsimp only [t]; omega
      have hLt : gL (rootsL (revL t)) = gL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) := by
        rw [hgL_roots (revL t), hxy]; apply Fin.ext; dsimp only [revL, t]; omega
      have hry_eq : rootsR t = Sum.inl ⟨y, hy⟩ := hgR_inj hRt
      have hrx_eq : rootsL (revL t) = Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩ := hgL_inj hLt
      have ht_free : ∀ i : Fin 4, pos i ≠ t := by
        intro i hi
        rw [← hi, hrootsL_pos i] at hrx_eq
        have heq : u i = x := congrArg Subtype.val (Sum.inl.inj hrx_eq)
        exact Finset.disjoint_left.mp hHB_disj' (hu_memH i) (heq ▸ hxB)
      rcases hfree_disj t ht_free with hRnone | hLnone
      · rw [hrootsR_free_none t ht_free hRnone] at hry_eq; exact absurd hry_eq (by simp)
      · rw [hrootsL_free_none t ht_free hLnone] at hrx_eq; exact absurd hrx_eq (by simp)
    · simp only [φ, hx, hy, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (Sum.inl.inj (hgL_inj hxy))
  have hφ_adj : ∀ x y : W, D.Adj x y → G.Adj (σ (φ x)) (σ (φ y)) := by
    intro x y hDxy
    by_cases hxH : x ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
      by_cases hyH : y ∈ H
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
        have hxHA : u i ∈ H ∪ A := Finset.mem_union_left _ (hu_memH i)
        have hyHA : u j ∈ H ∪ A := Finset.mem_union_left _ (hu_memH j)
        simp only [φ, hxHA, hyHA, ↓reduceDIte]
        rw [hgR_u i, hgR_u j]
        exact hpos_adj i j hDxy
      · by_cases hyA : y ∈ A
        · have hxHA : u i ∈ H ∪ A := Finset.mem_union_left _ (hu_memH i)
          have hyHA : y ∈ H ∪ A := Finset.mem_union_right _ hyA
          simp only [φ, hxHA, hyHA, ↓reduceDIte]
          by_cases hcut : isCutR y
          · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
            have hc := hcutR_spec t ht h hft
            have hcard1 := hA_in y hyA
            obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
            have e1 : u i = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩)
            have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
            have hhi : h = i := hu_inj (e2.trans e1.symm)
            have hgy : gR (Sum.inl ⟨y, hyHA⟩) = ⟨lo + t.val, by omega⟩ := by
              have hr := hrootsR_free_some t ht h hft
              have hy_eq : (Sum.inl ⟨y, hyHA⟩ : WR) = rootsR t := by
                rw [hr]; exact congrArg Sum.inl (Subtype.ext heqc.symm)
              rw [hy_eq, hgR_roots t]
            rw [hgR_u i, hgy]
            exact hhi ▸ (hfR_valid t ht h hft).2.1
          · exact hgR_adj _ _ ⟨hyA, hcut, hDxy⟩
        · exfalso
          exact hno_HB i y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
            (Finset.mem_union.mp h).elim hyH hyA⟩) hDxy
    · by_cases hxA : x ∈ A
      · by_cases hyH : y ∈ H
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
          exact absurd hDxy (hno_AH x hxA j)
        · by_cases hyA : y ∈ A
          · have hxHA : x ∈ H ∪ A := Finset.mem_union_right _ hxA
            have hyHA : y ∈ H ∪ A := Finset.mem_union_right _ hyA
            simp only [φ, hxHA, hyHA, ↓reduceDIte]
            have hnotcut : ¬ isCutR y := by
              rintro ⟨t, ht, h, hft, heqc⟩
              have hc := hcutR_spec t ht h hft
              have hcard1 := hA_in y hyA
              obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
              have e1 : x = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩)
              have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
              exact hHA_disj h (e2.trans e1.symm ▸ hxA)
            exact hgR_adj _ _ ⟨hyA, hnotcut, hDxy⟩
          · exfalso
            exact (hno_AB x hxA y (fun j hj => hyH (hj ▸ hu_memH j)) hyA).1 hDxy
      · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
          (Finset.mem_union.mp h).elim hxH hxA⟩
        have hyHB : y ∈ H ∪ B := by
          by_contra hynot
          have hyH : y ∉ H := fun h => hynot (Finset.mem_union_left _ h)
          have hyA : y ∈ A := by
            by_contra hynotA
            exact hynot (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
              (Finset.mem_union.mp h).elim hyH hynotA⟩))
          exact (hno_AB y hyA x (fun i hi => hxH (hi ▸ hu_memH i)) hxA).2 hDxy
        rw [hφ_on_HB x (Finset.mem_union_right _ hxB), hφ_on_HB y hyHB]
        by_cases hcut : isCutL x
        · obtain ⟨t, ht, h, hft, heqc⟩ := hcut
          have hc := hcutL_spec t ht h hft
          have hcard1 := hB_out x (fun i hi => hxH (hi ▸ hu_memH i)) hxA
          obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hcard1
          have e1 : y = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩)
          have e2 : u h = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, heqc ▸ hc.2⟩)
          have hyu : y = u h := e1.trans e2.symm
          have hgx : gL (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩) = ⟨lo + t.val, by omega⟩ := by
            have hr := hrootsL_free_some t ht h hft
            have hx_eq : (Sum.inl ⟨x, Finset.mem_union_right _ hxB⟩ : WL) = rootsL (revL t) := by
              rw [hr]; exact congrArg Sum.inl (Subtype.ext heqc.symm)
            rw [hx_eq, hgL_roots (revL t)]
            apply Fin.ext; dsimp only [revL]; omega
          have hgy : gL (Sum.inl ⟨y, hyHB⟩) = ⟨lo + (pos h).val, by omega⟩ := by
            have hy_eq : (Sum.inl ⟨y, hyHB⟩ : WL) = Sum.inl ⟨u h, Finset.mem_union_left _ (hu_memH h)⟩ :=
              congrArg Sum.inl (Subtype.ext hyu)
            rw [hy_eq, hgL_u h]
          rw [hgx, hgy]
          exact (hfL_valid t ht h hft).2.1
        · exact hgL_adj _ _ ⟨hxB, hcut, hDxy⟩
  exact ⟨⟨fun w => σ (φ w), fun h => hφ_adj _ _ h⟩, fun x y h => hφ_inj (σ.injective h)⟩

-- ============================================================================

-- MODULE 4: Exact Leaf Count (n - k = 4, n - k = 5) & Middle-6 Lemma
-- ============================================================================

lemma no_H_leaf_implies_k_eq
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (A : Finset W)
    (_hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hH_deg : ∀ i : Fin 4, (Finset.univ.filter (fun z : W => D.Adj (u i) z ∨ D.Adj z (u i))).card ≠ 1)
    (hO : ∃ T : SimpleGraph W, D.IsOrientation T) :
    let H : Finset W := Finset.univ.image u
    let B : Finset W := Finset.univ \ (H ∪ A)
    (A.filter (fun x => ∀ z : W, ¬ D.Adj x z)).card +
    (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)).card =
    (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
  classical
  obtain ⟨T, hO'⟩ := hO
  intro H B
  have hdisj : Disjoint (A.filter (fun x => ∀ z : W, ¬ D.Adj x z))
      (B.filter (fun y => ∀ z : W, ¬ D.Adj z y)) :=
    Finset.disjoint_left.mpr (fun w hwA hwB =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwB).1).2
        (Finset.mem_union_right _ (Finset.mem_filter.mp hwA).1))
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1; ext w
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hwA, hnoOut⟩ | ⟨hwB, hnoIn⟩)
    · have heq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj z w) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_left (hnoOut z), Or.inr⟩
      rw [heq]; exact hA_in w hwA
    · have hnotHA := (Finset.mem_sdiff.mp hwB).2
      have heq : Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w) =
          Finset.univ.filter (fun z : W => D.Adj w z) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.resolve_right (hnoIn z), Or.inl⟩
      rw [heq]
      exact hB_out w (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
        (fun h => hnotHA (Finset.mem_union_right _ h))
  · intro hdeg1
    by_cases hwH : w ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwH
      exact absurd hdeg1 (hH_deg i)
    · by_cases hwA : w ∈ A
      · left; refine ⟨hwA, fun z hDwz => ?_⟩
        have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z w)).card := by rw [hA_in w hwA]; omega
        obtain ⟨z0, hz0⟩ := Finset.card_pos.mp hpos
        have hDz0w := (Finset.mem_filter.mp hz0).2
        have hne : z ≠ z0 := fun h => not_adj_rev_of_isOrientation hO' hDwz (h ▸ hDz0w)
        have hsub : ({z, z0} : Finset W) ⊆ Finset.univ.filter (fun x : W => D.Adj w x ∨ D.Adj x w) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hDwz⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hDz0w⟩
        have h2 : 2 ≤ (Finset.univ.filter (fun x : W => D.Adj w x ∨ D.Adj x w)).card :=
          (Finset.card_pair hne).symm.trans_le (Finset.card_le_card hsub)
        omega
      · right
        have hwB : w ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hwH hwA⟩
        refine ⟨hwB, fun z hDzw => ?_⟩
        have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj w z)).card := by
          rw [hB_out w (fun i hi => hwH (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)) hwA]; omega
        obtain ⟨z0, hz0⟩ := Finset.card_pos.mp hpos
        have hDwz0 := (Finset.mem_filter.mp hz0).2
        have hne : z ≠ z0 := fun h => not_adj_rev_of_isOrientation hO' hDzw (h ▸ hDwz0)
        have hsub : ({z, z0} : Finset W) ⊆ Finset.univ.filter (fun x : W => D.Adj w x ∨ D.Adj x w) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hDzw⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hDwz0⟩
        have h2 : 2 ≤ (Finset.univ.filter (fun x : W => D.Adj w x ∨ D.Adj x w)).card :=
          (Finset.card_pair hne).symm.trans_le (Finset.card_le_card hsub)
        omega

-- Helper: general 4-core + direct-leaves embedding (used by Middle-6 AND Claims A/B!)
lemma embeds_of_core4_direct_leaves
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (_hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hA_all_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z)
    (hB_all_leaf : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ∀ z : W, ¬ D.Adj z y)
    (_hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (_hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (t : Fin 4 → V) (ht_inj : Function.Injective t)
    (ht_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → G.Adj (t i) (t j))
    (g : ↥(A ∪ (Finset.univ \ (Finset.univ.image u ∪ A))) → V)
    (hg_inj : Function.Injective g)
    (hg_notH : ∀ w, ∀ i : Fin 4, g w ≠ t i)
    (hg_A : ∀ w (_hwA : w.1 ∈ A) (i : Fin 4), D.Adj (u i) w.1 → G.Adj (t i) (g w))
    (hg_B : ∀ w (_hwB : w.1 ∈ Finset.univ \ (Finset.univ.image u ∪ A)) (i : Fin 4),
      D.Adj w.1 (u i) → G.Adj (g w) (t i)) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let φ : W → V := fun w =>
    if hwH : w ∈ H then t (Classical.choose (Finset.mem_image.mp hwH))
    else g ⟨w, by
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_left _ hwA
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hwH hwA⟩)⟩
  have hφ_u : ∀ i : Fin 4, φ (u i) = t i := by
    intro i; simp only [φ, hu_memH i, ↓reduceDIte]
    have hch := Classical.choose_spec (Finset.mem_image.mp (hu_memH i))
    rw [hu_inj hch.2]
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    by_cases hxH : x ∈ H <;> by_cases hyH : y ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
      rw [hφ_u i, hφ_u j] at hxy; rw [ht_inj hxy]
    · exfalso
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
      rw [hφ_u i] at hxy; simp only [φ, hyH, ↓reduceDIte] at hxy
      exact hg_notH _ i hxy.symm
    · exfalso
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
      rw [hφ_u j] at hxy; simp only [φ, hxH, ↓reduceDIte] at hxy
      exact hg_notH _ j hxy
    · simp only [φ, hxH, hyH, ↓reduceDIte] at hxy
      exact congrArg Subtype.val (hg_inj hxy)
  have hφ_adj : ∀ x y : W, D.Adj x y → G.Adj (φ x) (φ y) := by
    intro x y hDxy
    by_cases hxH : x ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH
      rw [hφ_u i]
      by_cases hyH : y ∈ H
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
        rw [hφ_u j]; exact ht_adj i j hDxy
      · by_cases hyA : y ∈ A
        · simp only [φ, hyH, ↓reduceDIte]; exact hg_A _ hyA i hDxy
        · exfalso
          exact hno_HB i y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hyH hyA⟩) hDxy
    · by_cases hxA : x ∈ A
      · exact absurd hDxy (hA_all_leaf x hxA y)
      · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hxH hxA⟩
        by_cases hyH : y ∈ H
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
          rw [hφ_u j]; simp only [φ, hxH, ↓reduceDIte]; exact hg_B _ hxB j hDxy
        · by_cases hyA : y ∈ A
          · exact absurd hDxy (hno_AB y hyA x (fun i hi => hxH (hi ▸ hu_memH i)) hxA).2
          · exact absurd hDxy (hB_all_leaf y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
              (Finset.mem_union.mp h).elim hyH hyA⟩) x)
  exact ⟨⟨φ, fun h => hφ_adj _ _ h⟩, hφ_inj⟩

-- Helper: M2-Left lower bound on in-neighbors of t in [0, cut - 1]
lemma median_in_lt_cut_ge {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card)
    (t : Fin (Fintype.card V)) (cut : ℕ) (_hcut : cut ≤ t.val) :
    (t.val + 1) / 2 - (t.val - cut) ≤
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < cut ∧ G.Adj (σ k) (σ t))).card := by
  classical
  have h1 := median_card_in_lt_ge hL t
  let Sall := Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < t.val ∧ G.Adj (σ k) (σ t))
  let Slow := Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < cut ∧ G.Adj (σ k) (σ t))
  let Smid := Finset.univ.filter (fun k : Fin (Fintype.card V) => cut ≤ k.val ∧ k.val < t.val)
  have hsub : Sall ⊆ Slow ∪ Smid := fun k hk => by
    have hk' := (Finset.mem_filter.mp hk).2
    by_cases hlt : k.val < cut
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hk'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hk'.1⟩)
  have hSmid : Smid.card ≤ t.val - cut := by
    have hbij : Smid.card = (Finset.Ico cut t.val).card := by
      refine Finset.card_bij (fun k _ => k.val) ?_ (fun _ _ _ _ h => Fin.ext h) ?_
      · intro k hk; have hk' := (Finset.mem_filter.mp hk).2; exact Finset.mem_Ico.mpr hk'
      · intro m hm; have ⟨h1', h2'⟩ := Finset.mem_Ico.mp hm
        exact ⟨⟨m, by have := t.isLt; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1', h2'⟩, rfl⟩
    rw [hbij, Nat.card_Ico]
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le Slow Smid)
  dsimp only [Sall, Slow] at hu; omega

-- Helper: M2-Right lower bound on out-neighbors of t in [cut, m - 1]
lemma median_out_ge_cut_ge {V : Type} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (t : Fin (Fintype.card V)) (cut : ℕ) (hcut : t.val < cut) :
    (Fintype.card V - t.val) / 2 - (cut - 1 - t.val) ≤
      (Finset.univ.filter (fun k : Fin (Fintype.card V) => cut ≤ k.val ∧ G.Adj (σ t) (σ k))).card := by
  classical
  have h1 := median_card_out_gt_ge hR t
  let Sall := Finset.univ.filter (fun k : Fin (Fintype.card V) => t.val < k.val ∧ G.Adj (σ t) (σ k))
  let Shi := Finset.univ.filter (fun k : Fin (Fintype.card V) => cut ≤ k.val ∧ G.Adj (σ t) (σ k))
  let Smid := Finset.univ.filter (fun k : Fin (Fintype.card V) => t.val < k.val ∧ k.val < cut)
  have hsub : Sall ⊆ Shi ∪ Smid := fun k hk => by
    have hk' := (Finset.mem_filter.mp hk).2
    by_cases hge : cut ≤ k.val
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge, hk'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'.1, by omega⟩)
  have hSmid : Smid.card ≤ cut - 1 - t.val := by
    have hbij : Smid.card ≤ (Finset.Ioo t.val cut).card := by
      have himg : Smid.image Fin.val ⊆ Finset.Ioo t.val cut := fun m hm => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hk).2
      rw [← Finset.card_image_of_injective Smid Fin.val_injective]
      exact Finset.card_le_card himg
    rw [Nat.card_Ioo] at hbij; omega
  have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le Shi Smid)
  have htlt := t.isLt
  dsimp only [Sall, Shi] at hu; omega

-- Middle-6 Case 1: P4+++ (0->1->2->3) at n-k = 4, maskP = {0}, maskM = {x, 3} (x in {0, 1})
lemma embeds_middle_six_P4ppp
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → i.val + 1 = j.val)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hcard_id : 4 + A.card + (Finset.univ \ (Finset.univ.image u ∪ A)).card = n)
    (hA_all_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z)
    (hB_all_leaf : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ∀ z : W, ¬ D.Adj z y)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hmaskP : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (ix : Fin 4) (hix : ix = ⟨0, by decide⟩ ∨ ix = ⟨1, by decide⟩)
    (hmaskM : ∀ i : Fin 4, i ≠ ix → i ≠ ⟨3, by decide⟩ →
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    (hix_ex : ∃ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), D.Adj y (u ix))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (_hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let a := A.card; let b := B.card
  have h2n : 2 * n - 2 = 2 * a + 2 * b + 6 := by dsimp only [a, b, B, H]; omega
  let pos4 : Fin 4 → Fin (Fintype.card V) := fun i => ⟨2 * b + i.val, by omega⟩
  have hpos4_inj : Function.Injective pos4 := fun i j h => Fin.ext (by have := congrArg Fin.val h; dsimp only [pos4] at this; omega)
  have ht_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → G.Adj (σ (pos4 i)) (σ (pos4 j)) := by
    intro i j hDij
    have hsucc := hH_adj i j hDij
    have hmed := median_adj_succ hR ⟨2 * b + i.val, by omega⟩ (by dsimp only; omega)
    convert hmed using 2; apply Fin.ext; dsimp only [pos4]; omega
  -- Split B into B3 (in-leaves of u 3) and Bx (in-leaves of u ix)
  let B3 := B.filter (fun y => D.Adj y (u ⟨3, by decide⟩))
  let Bx := B.filter (fun y => D.Adj y (u ix))
  have hdisj_B3x : Disjoint B3 Bx := Finset.disjoint_left.mpr (fun y h1 h2 => by
    have hnotHA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out y
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
      (fun h => hnotHA (Finset.mem_union_right _ h)))
    have e1 : u ⟨3, by decide⟩ = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h1).2⟩)
    have e2 : u ix = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h2).2⟩)
    have : ix = ⟨3, by decide⟩ := hu_inj (e2.trans e1.symm)
    rcases hix with h | h <;> simp [h] at this)
  have hB_cov : B3 ∪ Bx = B := by
    ext y; simp only [B3, Bx, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hyB
      have hnotHA := (Finset.mem_sdiff.mp hyB).2
      have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj y z)).card := by
        rw [hB_out y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnotHA (Finset.mem_union_right _ h))]; omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hDyz := (Finset.mem_filter.mp hz).2
      have hzH : z ∈ H := by
        by_contra hznotH
        by_cases hzA : z ∈ A
        · exact (hno_AB z hzA y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
            (fun h => hnotHA (Finset.mem_union_right _ h))).2 hDyz
        · exact hB_all_leaf z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hznotH hzA⟩) y hDyz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
      by_cases h3 : i = ⟨3, by decide⟩
      · exact Or.inl ⟨hyB, h3 ▸ hDyz⟩
      · by_cases hx : i = ix
        · exact Or.inr ⟨hyB, hx ▸ hDyz⟩
        · exact absurd hDyz (hmaskM i hx h3 y hyB)
  have hBx_pos : 1 ≤ Bx.card := by
    obtain ⟨y, hyB, hyx⟩ := hix_ex
    exact Finset.one_le_card.mpr ⟨y, Finset.mem_filter.mpr ⟨hyB, hyx⟩⟩
  have hB_sum : B3.card + Bx.card = b := by rw [← Finset.card_union_of_disjoint hdisj_B3x, hB_cov]
  -- Left pools in [0, 2b - 1], Right pool in [2b + 4, 2a + 2b + 5]
  let P0 := (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * b ∧ G.Adj (σ k) (σ (pos4 ⟨3, by decide⟩)))).image σ
  let P1 := (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * b ∧ G.Adj (σ k) (σ (pos4 ix)))).image σ
  let P2 := (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * b + 4 ≤ k.val ∧ G.Adj (σ (pos4 ⟨0, by decide⟩)) (σ k))).image σ
  have hP0_card : b - 1 ≤ P0.card := by
    dsimp only [P0]; rw [Finset.card_image_of_injective _ σ.injective]
    have h := median_in_lt_cut_ge hL (pos4 ⟨3, by decide⟩) (2 * b) (by dsimp only [pos4]; omega)
    dsimp only [pos4] at h ⊢; omega
  have hP1_card : b ≤ P1.card := by
    dsimp only [P1]; rw [Finset.card_image_of_injective _ σ.injective]
    have h := median_in_lt_cut_ge hL (pos4 ix) (2 * b) (by dsimp only [pos4]; omega)
    rcases hix with rfl | rfl <;> (dsimp only [pos4] at h ⊢; omega)
  have hP2_card : a ≤ P2.card := by
    dsimp only [P2]; rw [Finset.card_image_of_injective _ σ.injective]
    have h := median_out_ge_cut_ge hR (pos4 ⟨0, by decide⟩) (2 * b + 4) (by dsimp only [pos4]; omega)
    dsimp only [pos4] at h ⊢; omega
  -- Allocate B3 in P0, Bx in P1 \ img(B3), and A independently in P2 (disjoint from P0 ∪ P1!)
  obtain ⟨gL_AB, hgL_inj, hgL_B3, hgL_Bx, _⟩ := alloc_three_buckets hdisj_B3x (Finset.disjoint_empty_right B3)
    (Finset.disjoint_empty_right Bx) (P0 := P0) (P1 := P1) (P2 := P1)
    (by omega) (by omega) (by simp; omega)
  obtain ⟨PA, hPA_sub, hPA_card⟩ := Finset.exists_subset_card_eq hP2_card
  let eA : A ≃ PA := Fintype.equivOfCardEq (by simp [a, hPA_card])
  have hAB_disj : Disjoint A B := Finset.disjoint_left.mpr (fun x hxA hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_right _ hxA))
  let g : ↥(A ∪ B) → V := fun w =>
    if hwA : w.1 ∈ A then (eA ⟨w.1, hwA⟩).1
    else gL_AB ⟨w.1, Finset.mem_union_left _ (hB_cov.symm ▸ (Finset.mem_union.mp w.2).resolve_left hwA)⟩
  have hL_lt : ∀ w (hwB : w ∈ B), (σ.symm (gL_AB ⟨w, Finset.mem_union_left _ (hB_cov.symm ▸ hwB)⟩)).val < 2 * b := by
    intro w hwB
    have hwB' : w ∈ B3 ∪ Bx := hB_cov.symm ▸ hwB
    rcases Finset.mem_union.mp hwB' with h3 | hx
    · have hm := hgL_B3 ⟨w, Finset.mem_union_left _ hwB'⟩ h3
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      have : σ.symm (gL_AB ⟨w, Finset.mem_union_left _ hwB'⟩) = k := by rw [← heq, σ.symm_apply_apply]
      rw [this]; exact (Finset.mem_filter.mp hk).2.1
    · have hm := hgL_Bx ⟨w, Finset.mem_union_left _ hwB'⟩ hx
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      have : σ.symm (gL_AB ⟨w, Finset.mem_union_left _ hwB'⟩) = k := by rw [← heq, σ.symm_apply_apply]
      rw [this]; exact (Finset.mem_filter.mp hk).2.1
  have hR_ge : ∀ (x : W) (hxA : x ∈ A), 2 * b + 4 ≤ (σ.symm (eA ⟨x, hxA⟩).1).val := by
    intro x hxA
    have hm := hPA_sub (eA ⟨x, hxA⟩).2
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
    have : σ.symm (eA ⟨x, hxA⟩).1 = k := by rw [← heq, σ.symm_apply_apply]
    rw [this]; exact (Finset.mem_filter.mp hk).2.1
  refine embeds_of_core4_direct_leaves u hu_inj A hHA_disj hA_all_leaf hB_all_leaf hA_in hB_out hno_AB hno_HB
    (fun i => σ (pos4 i)) (fun i j h => hpos4_inj (σ.injective h)) ht_adj g ?_ ?_ ?_ ?_
  · intro x y hxy
    by_cases hxA : x.1 ∈ A <;> by_cases hyA : y.1 ∈ A
    · simp only [g, hxA, hyA, ↓reduceDIte] at hxy
      exact Subtype.ext (congrArg (fun z : A => z.1) (eA.injective (Subtype.ext hxy)))
    · exfalso
      have hyB : y.1 ∈ B := (Finset.mem_union.mp y.2).resolve_left hyA
      simp only [g, hxA, hyA, ↓reduceDIte] at hxy
      have h1 := hR_ge x.1 hxA; have h2 := hL_lt y.1 hyB
      rw [hxy] at h1; omega
    · exfalso
      have hxB : x.1 ∈ B := (Finset.mem_union.mp x.2).resolve_left hxA
      simp only [g, hxA, hyA, ↓reduceDIte] at hxy
      have h1 := hR_ge y.1 hyA; have h2 := hL_lt x.1 hxB
      rw [← hxy] at h1; omega
    · simp only [g, hxA, hyA, ↓reduceDIte] at hxy
      exact Subtype.ext (congrArg (fun z : ↥(B3 ∪ Bx ∪ ∅) => z.1) (hgL_inj hxy))
  · intro w i heq
    have hval := congrArg (fun v => (σ.symm v).val) heq
    rw [σ.symm_apply_apply] at hval
    by_cases hwA : w.1 ∈ A
    · simp only [g, hwA, ↓reduceDIte] at hval
      have := hR_ge w.1 hwA; dsimp only [pos4] at hval; omega
    · have hwB : w.1 ∈ B := (Finset.mem_union.mp w.2).resolve_left hwA
      simp only [g, hwA, ↓reduceDIte] at hval
      have := hL_lt w.1 hwB; dsimp only [pos4] at hval; omega
  · intro w hwA i hDui
    have hi0 : i = ⟨0, by decide⟩ := by by_contra h; exact hmaskP i h w.1 hwA hDui
    subst hi0
    simp only [g, hwA, ↓reduceDIte]
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hPA_sub (eA ⟨w.1, hwA⟩).2)
    rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
  · intro w hwB i hDwi
    have hwnotA : w.1 ∉ A := Finset.disjoint_right.mp hAB_disj hwB
    simp only [g, hwnotA, ↓reduceDIte]
    have hwB' : w.1 ∈ B3 ∪ Bx := hB_cov.symm ▸ hwB
    by_cases h3 : i = ⟨3, by decide⟩
    · subst h3
      have hm := hgL_B3 ⟨w.1, Finset.mem_union_left _ hwB'⟩ (Finset.mem_filter.mpr ⟨hwB, hDwi⟩)
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
    · have hxi : i = ix := by by_contra h; exact hmaskM i h h3 w.1 hwB hDwi
      subst hxi
      have hm := hgL_Bx ⟨w.1, Finset.mem_union_left _ hwB'⟩ (Finset.mem_filter.mpr ⟨hwB, hDwi⟩)
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hm
      rw [← heq]; exact (Finset.mem_filter.mp hk).2.2

-- Middle-6 Case 2: P4++- (0->1->2<-3) at n-k = 4, maskP = {0, 3}, maskM = {2}
lemma embeds_middle_six_P4ppm
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) →
      (i = ⟨0, by decide⟩ ∧ j = ⟨1, by decide⟩) ∨
      (i = ⟨1, by decide⟩ ∧ j = ⟨2, by decide⟩) ∨
      (i = ⟨3, by decide⟩ ∧ j = ⟨2, by decide⟩))
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hcard_id : 4 + A.card + (Finset.univ \ (Finset.univ.image u ∪ A)).card = n)
    (hA_all_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z)
    (hB_all_leaf : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ∀ z : W, ¬ D.Adj z y)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hmaskP : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → i ≠ ⟨3, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (h3_ex : ∃ x ∈ A, D.Adj (u ⟨3, by decide⟩) x)
    (hmaskM : ∀ i : Fin 4, i ≠ ⟨2, by decide⟩ →
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    {σ : Fin (Fintype.card V) ≃ V}
    (hR : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i < k ∧ k ≤ j ∧ G.Adj (σ i) (σ k))).card)
    (hL : ∀ i j : Fin (Fintype.card V), i < j →
      j.val - i.val ≤ 2 * (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
        i ≤ k ∧ k < j ∧ G.Adj (σ k) (σ j))).card) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let a := A.card; let b := B.card
  have h2n : 2 * n - 2 = 2 * a + 2 * b + 6 := by dsimp only [a, b, B, H]; omega
  let A0 := A.filter (fun x => D.Adj (u ⟨0, by decide⟩) x)
  let A3 := A.filter (fun x => D.Adj (u ⟨3, by decide⟩) x)
  have hdisj_A03 : Disjoint A0 A3 := Finset.disjoint_left.mpr (fun x h1 h2 => by
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hA_in x (Finset.mem_filter.mp h1).1)
    have e1 : u ⟨0, by decide⟩ = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h1).2⟩)
    have e2 : u ⟨3, by decide⟩ = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h2).2⟩)
    have := hu_inj (e1.trans e2.symm); simp at this)
  have hA_cov : A0 ∪ A3 = A := by
    ext x; simp only [A0, A3, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hxA
      have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z x)).card := by rw [hA_in x hxA]; omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hDzx := (Finset.mem_filter.mp hz).2
      have hzH : z ∈ H := by
        by_contra hznotH
        by_cases hzA : z ∈ A
        · exact hA_all_leaf z hzA x hDzx
        · exact (hno_AB x hxA z (fun i hi => hznotH (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)) hzA).2 hDzx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
      by_cases h0 : i = ⟨0, by decide⟩
      · exact Or.inl ⟨hxA, h0 ▸ hDzx⟩
      · by_cases h3 : i = ⟨3, by decide⟩
        · exact Or.inr ⟨hxA, h3 ▸ hDzx⟩
        · exact absurd hDzx (hmaskP i h0 h3 x hxA)
  have hA3_pos : 1 ≤ A3.card := by obtain ⟨x, hxA, hx3⟩ := h3_ex; exact Finset.one_le_card.mpr ⟨x, Finset.mem_filter.mpr ⟨hxA, hx3⟩⟩
  have hA_sum : A0.card + A3.card = a := by rw [← Finset.card_union_of_disjoint hdisj_A03, hA_cov]
  have hAB_disj : Disjoint A B := Finset.disjoint_left.mpr (fun x hxA hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_right _ hxA))
  -- Case split on G.Adj (2b + 3) (2b + 5) vs (2b + 5) -> (2b + 3)!
  by_cases h35 : G.Adj (σ ⟨2 * b + 3, by omega⟩) (σ ⟨2 * b + 5, by omega⟩)
  · -- Subcase 3 -> 5: pos = (2, 3, 5, 4) in M
    let pos4 : Fin 4 → Fin (Fintype.card V) := fun i =>
      match i.val with
      | 0 => ⟨2 * b + 2, by omega⟩
      | 1 => ⟨2 * b + 3, by omega⟩
      | 2 => ⟨2 * b + 5, by omega⟩
      | _ => ⟨2 * b + 4, by omega⟩
    have hpos4_inj : Function.Injective pos4 := by
      intro i j h; have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp only [pos4] at hv <;> first | rfl | omega
    have ht_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → G.Adj (σ (pos4 i)) (σ (pos4 j)) := by
      intro i j hDij
      rcases hH_adj i j hDij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact median_adj_succ hR ⟨2 * b + 2, by omega⟩ (by dsimp only; omega)
      · exact h35
      · exact median_adj_succ hR ⟨2 * b + 4, by omega⟩ (by dsimp only; omega)
    let PL := (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * b + 2 ∧ G.Adj (σ k) (σ (pos4 ⟨2, by decide⟩)))).image σ
    let PR0 := (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * b + 6 ≤ k.val ∧ G.Adj (σ (pos4 ⟨0, by decide⟩)) (σ k))).image σ
    let PR3 := (Finset.univ.filter (fun k : Fin (Fintype.card V) => 2 * b + 6 ≤ k.val ∧ G.Adj (σ (pos4 ⟨3, by decide⟩)) (σ k))).image σ
    have hPL_card : b ≤ PL.card := by
      dsimp only [PL]; rw [Finset.card_image_of_injective _ σ.injective]
      have h := median_in_lt_cut_ge hL (pos4 ⟨2, by decide⟩) (2 * b + 2) (by simp only [pos4]; omega)
      simp only [pos4] at h ⊢; omega
    have hPR0_card : a - 1 ≤ PR0.card := by
      dsimp only [PR0]; rw [Finset.card_image_of_injective _ σ.injective]
      have h := median_out_ge_cut_ge hR (pos4 ⟨0, by decide⟩) (2 * b + 6) (by simp only [pos4]; omega)
      simp only [pos4] at h ⊢; omega
    have hPR3_card : a ≤ PR3.card := by
      dsimp only [PR3]; rw [Finset.card_image_of_injective _ σ.injective]
      have h := median_out_ge_cut_ge hR (pos4 ⟨3, by decide⟩) (2 * b + 6) (by simp only [pos4]; omega)
      simp only [pos4] at h ⊢; omega
    obtain ⟨gR_A, hgR_inj, hgR_A0, hgR_A3, _⟩ := alloc_three_buckets hdisj_A03 (Finset.disjoint_empty_right A0)
      (Finset.disjoint_empty_right A3) (P0 := PR0) (P1 := PR3) (P2 := PR3)
      (by omega) (by omega) (by simp; omega)
    obtain ⟨PB, hPB_sub, hPB_card⟩ := Finset.exists_subset_card_eq hPL_card
    let eB : B ≃ PB := Fintype.equivOfCardEq (by simp [b, hPB_card])
    let g : ↥(A ∪ B) → V := fun w =>
      if hwA : w.1 ∈ A then gR_A ⟨w.1, Finset.mem_union_left _ (hA_cov.symm ▸ hwA)⟩
      else (eB ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hwA⟩).1
    have hR_ge : ∀ w (hwA : w ∈ A), 2 * b + 6 ≤ (σ.symm (gR_A ⟨w, Finset.mem_union_left _ (hA_cov.symm ▸ hwA)⟩)).val := by
      intro w hwA
      have hwA' : w ∈ A0 ∪ A3 := hA_cov.symm ▸ hwA
      rcases Finset.mem_union.mp hwA' with h0 | h3
      · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A0 ⟨w, Finset.mem_union_left _ hwA'⟩ h0)
        rw [show σ.symm (gR_A ⟨w, Finset.mem_union_left _ hwA'⟩) = k by rw [← heq, σ.symm_apply_apply]]
        exact (Finset.mem_filter.mp hk).2.1
      · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A3 ⟨w, Finset.mem_union_left _ hwA'⟩ h3)
        rw [show σ.symm (gR_A ⟨w, Finset.mem_union_left _ hwA'⟩) = k by rw [← heq, σ.symm_apply_apply]]
        exact (Finset.mem_filter.mp hk).2.1
    have hL_lt : ∀ y (hyB : y ∈ B), (σ.symm (eB ⟨y, hyB⟩).1).val < 2 * b + 2 := by
      intro y hyB
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hPB_sub (eB ⟨y, hyB⟩).2)
      rw [show σ.symm (eB ⟨y, hyB⟩).1 = k by rw [← heq, σ.symm_apply_apply]]
      exact (Finset.mem_filter.mp hk).2.1
    refine embeds_of_core4_direct_leaves u hu_inj A hHA_disj hA_all_leaf hB_all_leaf hA_in hB_out hno_AB hno_HB
      (fun i => σ (pos4 i)) (fun i j h => hpos4_inj (σ.injective h)) ht_adj g ?_ ?_ ?_ ?_
    · intro x y hxy
      by_cases hxA : x.1 ∈ A <;> by_cases hyA : y.1 ∈ A
      · simp only [g, hxA, hyA, ↓reduceDIte] at hxy; exact Subtype.ext (congrArg (fun z : ↥(A0 ∪ A3 ∪ ∅) => z.1) (hgR_inj hxy))
      · exfalso; have hyB := (Finset.mem_union.mp y.2).resolve_left hyA
        simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        have h1 := hR_ge x.1 hxA; have h2 := hL_lt y.1 hyB; rw [hxy] at h1; omega
      · exfalso; have hxB := (Finset.mem_union.mp x.2).resolve_left hxA
        simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        have h1 := hR_ge y.1 hyA; have h2 := hL_lt x.1 hxB; rw [← hxy] at h1; omega
      · simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        exact Subtype.ext (congrArg (fun z : B => z.1) (eB.injective (Subtype.ext hxy)))
    · intro w i heq
      have hval := congrArg (fun v => (σ.symm v).val) heq; rw [σ.symm_apply_apply] at hval
      by_cases hwA : w.1 ∈ A
      · simp only [g, hwA, ↓reduceDIte] at hval; have := hR_ge w.1 hwA; fin_cases i <;> simp only [pos4] at hval <;> omega
      · have hwB := (Finset.mem_union.mp w.2).resolve_left hwA
        simp only [g, hwA, ↓reduceDIte] at hval; have := hL_lt w.1 hwB; fin_cases i <;> simp only [pos4] at hval <;> omega
    · intro w hwA i hDui
      simp only [g, hwA, ↓reduceDIte]
      have hwA' : w.1 ∈ A0 ∪ A3 := hA_cov.symm ▸ hwA
      by_cases h0 : i = ⟨0, by decide⟩
      · subst h0
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A0 ⟨w.1, Finset.mem_union_left _ hwA'⟩ (Finset.mem_filter.mpr ⟨hwA, hDui⟩))
        rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
      · have h3 : i = ⟨3, by decide⟩ := by by_contra h; exact hmaskP i h0 h w.1 hwA hDui
        subst h3
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A3 ⟨w.1, Finset.mem_union_left _ hwA'⟩ (Finset.mem_filter.mpr ⟨hwA, hDui⟩))
        rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
    · intro w hwB i hDwi
      have h2 : i = ⟨2, by decide⟩ := by by_contra h; exact hmaskM i h w.1 hwB hDwi
      subst h2
      have hwnotA : w.1 ∉ A := Finset.disjoint_right.mp hAB_disj hwB
      simp only [g, hwnotA, ↓reduceDIte]
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hPB_sub (eB ⟨w.1, hwB⟩).2)
      rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
  · -- Subcase 5 -> 3: pos = (1, 2, 3, 5) in M
    have h53 : G.Adj (σ ⟨2 * b + 5, by omega⟩) (σ ⟨2 * b + 3, by omega⟩) :=
      (adj_or_rev_of_isTournament hG (fun h => by have := congrArg Fin.val (σ.injective h); dsimp only at this; omega)).resolve_left h35
    let pos4 : Fin 4 → Fin (Fintype.card V) := fun i =>
      match i.val with
      | 0 => ⟨2 * b + 1, by omega⟩
      | 1 => ⟨2 * b + 2, by omega⟩
      | 2 => ⟨2 * b + 3, by omega⟩
      | _ => ⟨2 * b + 5, by omega⟩
    have hpos4_inj : Function.Injective pos4 := by
      intro i j h; have hv := congrArg Fin.val h; fin_cases i <;> fin_cases j <;> simp only [pos4] at hv <;> first | rfl | omega
    have ht_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → G.Adj (σ (pos4 i)) (σ (pos4 j)) := by
      intro i j hDij
      rcases hH_adj i j hDij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact median_adj_succ hR ⟨2 * b + 1, by omega⟩ (by dsimp only; omega)
      · exact median_adj_succ hR ⟨2 * b + 2, by omega⟩ (by dsimp only; omega)
      · exact h53
    let PL := (Finset.univ.filter (fun k : Fin (Fintype.card V) => k.val < 2 * b + 1 ∧ G.Adj (σ k) (σ (pos4 ⟨2, by decide⟩)))).image σ
    let PR0 := (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      (k.val = 2 * b + 4 ∨ 2 * b + 6 ≤ k.val) ∧ G.Adj (σ (pos4 ⟨0, by decide⟩)) (σ k))).image σ
    let PR3 := (Finset.univ.filter (fun k : Fin (Fintype.card V) =>
      2 * b + 6 ≤ k.val ∧ G.Adj (σ (pos4 ⟨3, by decide⟩)) (σ k))).image σ
    have hPL_card : b ≤ PL.card := by
      dsimp only [PL]; rw [Finset.card_image_of_injective _ σ.injective]
      have h := median_in_lt_cut_ge hL (pos4 ⟨2, by decide⟩) (2 * b + 1) (by simp only [pos4]; omega)
      simp only [pos4] at h ⊢; omega
    have hPR0_card : a - 1 ≤ PR0.card := by
      dsimp only [PR0]; rw [Finset.card_image_of_injective _ σ.injective]
      have h1 := median_card_out_gt_ge hR (pos4 ⟨0, by decide⟩)
      let Sall := Finset.univ.filter (fun k : Fin (Fintype.card V) => (pos4 ⟨0, by decide⟩).val < k.val ∧ G.Adj (σ (pos4 ⟨0, by decide⟩)) (σ k))
      let Sgood := Finset.univ.filter (fun k : Fin (Fintype.card V) => (k.val = 2 * b + 4 ∨ 2 * b + 6 ≤ k.val) ∧ G.Adj (σ (pos4 ⟨0, by decide⟩)) (σ k))
      let Sbad : Finset (Fin (Fintype.card V)) := {⟨2 * b + 2, by omega⟩, ⟨2 * b + 3, by omega⟩, ⟨2 * b + 5, by omega⟩}
      have hsub : Sall ⊆ Sgood ∪ Sbad := fun k hk => by
        have hk' := (Finset.mem_filter.mp hk).2
        simp only [pos4] at hk'
        by_cases hgood : k.val = 2 * b + 4 ∨ 2 * b + 6 ≤ k.val
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood, hk'.2⟩)
        · refine Finset.mem_union_right _ ?_
          simp only [Sbad, Finset.mem_insert, Finset.mem_singleton]
          have : k.val = 2 * b + 2 ∨ k.val = 2 * b + 3 ∨ k.val = 2 * b + 5 := by omega
          rcases this with h | h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
          · exact Or.inr (Or.inr (Fin.ext h))
      have hSbad : Sbad.card ≤ 3 := Finset.card_le_three
      have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le Sgood Sbad)
      simp only [Sall, Sgood, pos4] at h1 hu ⊢; omega
    have hPR3_card : a ≤ PR3.card := by
      dsimp only [PR3]; rw [Finset.card_image_of_injective _ σ.injective]
      have h := median_out_ge_cut_ge hR (pos4 ⟨3, by decide⟩) (2 * b + 6) (by simp only [pos4]; omega)
      simp only [pos4] at h ⊢; omega
    obtain ⟨gR_A, hgR_inj, hgR_A0, hgR_A3, _⟩ := alloc_three_buckets hdisj_A03 (Finset.disjoint_empty_right A0)
      (Finset.disjoint_empty_right A3) (P0 := PR0) (P1 := PR3) (P2 := PR3)
      (by omega) (by omega) (by simp; omega)
    obtain ⟨PB, hPB_sub, hPB_card⟩ := Finset.exists_subset_card_eq hPL_card
    let eB : B ≃ PB := Fintype.equivOfCardEq (by simp [b, hPB_card])
    let g : ↥(A ∪ B) → V := fun w =>
      if hwA : w.1 ∈ A then gR_A ⟨w.1, Finset.mem_union_left _ (hA_cov.symm ▸ hwA)⟩
      else (eB ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hwA⟩).1
    have hR_pos : ∀ w (hwA : w ∈ A),
        let k := (σ.symm (gR_A ⟨w, Finset.mem_union_left _ (hA_cov.symm ▸ hwA)⟩)).val
        k = 2 * b + 4 ∨ 2 * b + 6 ≤ k := by
      intro w hwA
      have hwA' : w ∈ A0 ∪ A3 := hA_cov.symm ▸ hwA
      rcases Finset.mem_union.mp hwA' with h0 | h3
      · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A0 ⟨w, Finset.mem_union_left _ hwA'⟩ h0)
        dsimp only; rw [show σ.symm (gR_A ⟨w, Finset.mem_union_left _ hwA'⟩) = k by rw [← heq, σ.symm_apply_apply]]
        exact (Finset.mem_filter.mp hk).2.1
      · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A3 ⟨w, Finset.mem_union_left _ hwA'⟩ h3)
        dsimp only; rw [show σ.symm (gR_A ⟨w, Finset.mem_union_left _ hwA'⟩) = k by rw [← heq, σ.symm_apply_apply]]
        exact Or.inr (Finset.mem_filter.mp hk).2.1
    have hL_lt : ∀ y (hyB : y ∈ B), (σ.symm (eB ⟨y, hyB⟩).1).val < 2 * b + 1 := by
      intro y hyB
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hPB_sub (eB ⟨y, hyB⟩).2)
      rw [show σ.symm (eB ⟨y, hyB⟩).1 = k by rw [← heq, σ.symm_apply_apply]]
      exact (Finset.mem_filter.mp hk).2.1
    refine embeds_of_core4_direct_leaves u hu_inj A hHA_disj hA_all_leaf hB_all_leaf hA_in hB_out hno_AB hno_HB
      (fun i => σ (pos4 i)) (fun i j h => hpos4_inj (σ.injective h)) ht_adj g ?_ ?_ ?_ ?_
    · intro x y hxy
      by_cases hxA : x.1 ∈ A <;> by_cases hyA : y.1 ∈ A
      · simp only [g, hxA, hyA, ↓reduceDIte] at hxy; exact Subtype.ext (congrArg (fun z : ↥(A0 ∪ A3 ∪ ∅) => z.1) (hgR_inj hxy))
      · exfalso; have hyB := (Finset.mem_union.mp y.2).resolve_left hyA
        simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        have h1 := hR_pos x.1 hxA; have h2 := hL_lt y.1 hyB; dsimp only at h1; rw [hxy] at h1; omega
      · exfalso; have hxB := (Finset.mem_union.mp x.2).resolve_left hxA
        simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        have h1 := hR_pos y.1 hyA; have h2 := hL_lt x.1 hxB; dsimp only at h1; rw [← hxy] at h1; omega
      · simp only [g, hxA, hyA, ↓reduceDIte] at hxy
        exact Subtype.ext (congrArg (fun z : B => z.1) (eB.injective (Subtype.ext hxy)))
    · intro w i heq
      have hval := congrArg (fun v => (σ.symm v).val) heq; rw [σ.symm_apply_apply] at hval
      by_cases hwA : w.1 ∈ A
      · simp only [g, hwA, ↓reduceDIte] at hval; have h1 := hR_pos w.1 hwA; dsimp only at h1
        fin_cases i <;> simp only [pos4] at hval <;> omega
      · have hwB := (Finset.mem_union.mp w.2).resolve_left hwA
        simp only [g, hwA, ↓reduceDIte] at hval; have := hL_lt w.1 hwB
        fin_cases i <;> simp only [pos4] at hval <;> omega
    · intro w hwA i hDui
      simp only [g, hwA, ↓reduceDIte]
      have hwA' : w.1 ∈ A0 ∪ A3 := hA_cov.symm ▸ hwA
      by_cases h0 : i = ⟨0, by decide⟩
      · subst h0
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A0 ⟨w.1, Finset.mem_union_left _ hwA'⟩ (Finset.mem_filter.mpr ⟨hwA, hDui⟩))
        rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
      · have h3 : i = ⟨3, by decide⟩ := by by_contra h; exact hmaskP i h0 h w.1 hwA hDui
        subst h3
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hgR_A3 ⟨w.1, Finset.mem_union_left _ hwA'⟩ (Finset.mem_filter.mpr ⟨hwA, hDui⟩))
        rw [← heq]; exact (Finset.mem_filter.mp hk).2.2
    · intro w hwB i hDwi
      have h2 : i = ⟨2, by decide⟩ := by by_contra h; exact hmaskM i h w.1 hwB hDwi
      subst h2
      have hwnotA : w.1 ∉ A := Finset.disjoint_right.mp hAB_disj hwB
      simp only [g, hwnotA, ↓reduceDIte]
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hPB_sub (eB ⟨w.1, hwB⟩).2)
      rw [← heq]; exact (Finset.mem_filter.mp hk).2.2

-- ============================================================================
-- MODULE 5: (V+, V-) Cross-Edge Bound, Claims A, B, D & Leaf Absorption
-- ============================================================================

lemma cross_edges_Vp_Vm {n : ℕ} (hn : 6 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v)
    (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
    let Vm := Vpᶜ
    (∀ v : V, (Finset.univ.filter (fun u : V => G.Adj v u)).card +
              (Finset.univ.filter (fun u : V => G.Adj u v)).card = 2 * n - 3) ∧
    (∀ v ∈ Vm, n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card) ∧
    Vp.card + Vm.card = 2 * n - 2 ∧
    2 ≤ Vp.card ∧ 2 ≤ Vm.card ∧
    Vp.card * Vm.card + max Vp.card Vm.card ≤
      2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card ∧
    Vp.card + 2 < ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
  classical
  intro Vp Vm
  have hdeg_sum : ∀ v : V,
      (Finset.univ.filter (fun u : V => G.Adj v u)).card +
      (Finset.univ.filter (fun u : V => G.Adj u v)).card = 2 * n - 3 := by
    intro v
    have hdisj : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
        (Finset.univ.filter (fun u : V => G.Adj u v)) :=
      Finset.disjoint_left.mpr (fun u h1 h2 =>
        not_adj_rev_of_tournament hG (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2)
    have hunion : Finset.univ.filter (fun u : V => G.Adj v u) ∪
        Finset.univ.filter (fun u : V => G.Adj u v) = Finset.univ.erase v := by
      ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · rintro (h | h)
        · exact (ne_of_adj_tournament hG h).symm
        · exact ne_of_adj_tournament hG h
      · intro hne
        rcases adj_or_rev_of_isTournament hG hne.symm with h | h
        · exact Or.inl h
        · exact Or.inr h
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
    omega
  have hVm_deg : ∀ v ∈ Vm, n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
    intro v hv
    have hnotVp : v ∉ Vp := Finset.mem_compl.mp hv
    have hlt : (Finset.univ.filter (fun u : V => G.Adj v u)).card < n - 1 := by
      by_contra hge; exact hnotVp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
    have := hdeg_sum v; omega
  have hpq_sum : Vp.card + Vm.card = 2 * n - 2 := by
    rw [Finset.card_compl, hV]; have : Vp.card ≤ 2 * n - 2 := hV ▸ Finset.card_le_univ _; omega
  -- Cross-edge identity from Vp: sum_{v in Vp} d+(v) = e(Vp, Vp) + e(Vp, Vm)
  have he_from_Vp : Vp.card * Vm.card + Vp.card ≤ 2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hsum_ge : Vp.card * (n - 1) ≤ ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card := by
      calc Vp.card * (n - 1) = ∑ _v ∈ Vp, (n - 1) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    have hsplit : ∑ v ∈ Vp, (Finset.univ.filter (fun u : V => G.Adj v u)).card =
        ((Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2)).card +
        ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      have hbi1 : ∑ v ∈ Vp, (Vp.filter (fun u => G.Adj v u)).card =
          ((Vp ×ˢ Vp).filter (fun p => G.Adj p.1 p.2)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
      have hbi2 : ∑ v ∈ Vp, (Vm.filter (fun u => G.Adj v u)).card =
          ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
      rw [← hbi1, ← hbi2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 =>
        Finset.mem_compl.mp (Finset.mem_filter.mp h2).1 (Finset.mem_filter.mp h1).1))]
      congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]; tauto
    have hint := tournament_two_mul_internal_arcs hG Vp
    have h2 : 2 * (Vp.card * (n - 1)) ≤ (Vp.card * Vp.card - Vp.card) + 2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      omega
    have h3 : Vp.card ≤ Vp.card * Vp.card := Nat.le_mul_self Vp.card
    have h4 : Vp.card * Vp.card + Vp.card * Vm.card = Vp.card * (2 * n - 2) := by
      rw [← Nat.mul_add, hpq_sum]
    have h5 : 2 * (Vp.card * (n - 1)) = Vp.card * (2 * n - 2) := by
      have : 2 * (n - 1) = 2 * n - 2 := by omega
      rw [← this]; ring
    omega
  have he_from_Vm : Vp.card * Vm.card + Vm.card ≤ 2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hsum_ge : Vm.card * (n - 1) ≤ ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card := by
      calc Vm.card * (n - 1) = ∑ _v ∈ Vm, (n - 1) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun v hv => hVm_deg v hv)
    have hsplit : ∑ v ∈ Vm, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
        ((Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card +
        ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      have hbi1 : ∑ v ∈ Vm, (Vm.filter (fun u => G.Adj u v)).card =
          ((Vm ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
        rw [Finset.card_filter, Finset.sum_product_right]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
      have hbi2 : ∑ v ∈ Vm, (Vp.filter (fun u => G.Adj u v)).card =
          ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
        rw [Finset.card_filter, Finset.sum_product_right]
        refine Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
      rw [← hbi1, ← hbi2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 =>
        Finset.mem_compl.mp (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1))]
      congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]; tauto
    have hint := tournament_two_mul_internal_arcs hG Vm
    have h2 : 2 * (Vm.card * (n - 1)) ≤ (Vm.card * Vm.card - Vm.card) + 2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      omega
    have h3 : Vm.card ≤ Vm.card * Vm.card := Nat.le_mul_self Vm.card
    have h4 : Vp.card * Vm.card + Vm.card * Vm.card = Vm.card * (2 * n - 2) := by
      rw [Nat.mul_comm Vp.card Vm.card, ← Nat.mul_add, hpq_sum]
    have h5 : 2 * (Vm.card * (n - 1)) = Vm.card * (2 * n - 2) := by
      have : 2 * (n - 1) = 2 * n - 2 := by omega
      rw [← this]; ring
    omega
  have he_max : Vp.card * Vm.card + max Vp.card Vm.card ≤ 2 * ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    rcases le_total Vp.card Vm.card with h | h
    · rw [max_eq_right h]; exact he_from_Vm
    · rw [max_eq_left h]; exact he_from_Vp
  have hp_ge2 : 2 ≤ Vp.card := by
    by_contra hlt
    have hcases : Vp.card = 0 ∨ Vp.card = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0] at he_from_Vm hpq_sum
      have hcard0 : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card = 0 := by
        rw [Finset.card_eq_zero.mp h0, Finset.empty_product]; simp
      omega
    · obtain ⟨u0, hu0⟩ := Finset.card_eq_one.mp h1
      have hsub : (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) ⊆
          (Finset.univ.filter (fun y : V => G.Adj u0 y)).image (fun y => (u0, y)) := by
        intro p hp
        obtain ⟨hpprod, hadj⟩ := Finset.mem_filter.mp hp
        have hp1 : p.1 = u0 := Finset.mem_singleton.mp (hu0 ▸ (Finset.mem_product.mp hpprod).1)
        exact Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1 ▸ hadj⟩, Prod.ext hp1.symm rfl⟩
      have hle : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card ≤
          (Finset.univ.filter (fun y : V => G.Adj u0 y)).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      obtain ⟨w, hwu0⟩ := hNoSrc u0
      have hin_pos : 1 ≤ (Finset.univ.filter (fun y : V => G.Adj y u0)).card :=
        Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwu0⟩⟩
      have hsum := hdeg_sum u0
      rw [h1] at he_from_Vm hpq_sum
      omega
  have hq_ge2 : 2 ≤ Vm.card := by
    by_contra hlt
    have hcases : Vm.card = 0 ∨ Vm.card = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0] at he_from_Vp hpq_sum
      have hcard0 : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card = 0 := by
        rw [Finset.card_eq_zero.mp h0, Finset.product_empty]; simp
      omega
    · obtain ⟨v0, hv0⟩ := Finset.card_eq_one.mp h1
      have hsub : (Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2) ⊆
          (Finset.univ.filter (fun x : V => G.Adj x v0)).image (fun x => (x, v0)) := by
        intro p hp
        obtain ⟨hpprod, hadj⟩ := Finset.mem_filter.mp hp
        have hp2 : p.2 = v0 := Finset.mem_singleton.mp (hv0 ▸ (Finset.mem_product.mp hpprod).2)
        exact Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2 ▸ hadj⟩, Prod.ext rfl hp2.symm⟩
      have hle : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card ≤
          (Finset.univ.filter (fun x : V => G.Adj x v0)).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      obtain ⟨w, hv0w⟩ := hNoSnk v0
      have hout_pos : 1 ≤ (Finset.univ.filter (fun x : V => G.Adj v0 x)).card :=
        Finset.one_le_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv0w⟩⟩
      have hsum := hdeg_sum v0
      rw [h1] at he_from_Vp hpq_sum
      omega
  have he_gt : Vp.card + 2 < ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
    have hstrict : 2 * Vp.card + 4 < Vp.card * Vm.card + max Vp.card Vm.card := by
      by_cases hq2 : Vm.card = 2
      · have hp8 : 8 ≤ Vp.card := by omega
        have hmx : Vp.card ≤ max Vp.card Vm.card := le_max_left _ _
        rw [hq2]; omega
      · by_cases hq3 : Vm.card = 3
        · have hp7 : 7 ≤ Vp.card := by omega
          have hmx : Vp.card ≤ max Vp.card Vm.card := le_max_left _ _
          rw [hq3]; omega
        · have hq4 : 4 ≤ Vm.card := by omega
          by_cases hp2 : Vp.card = 2
          · have hq8 : 8 ≤ Vm.card := by omega
            have hmx : Vm.card ≤ max Vp.card Vm.card := le_max_right _ _
            rw [hp2]; omega
          · have hp3 : 3 ≤ Vp.card := by omega
            have hmul : 4 * Vp.card ≤ Vp.card * Vm.card := by
              rw [Nat.mul_comm 4 Vp.card]; exact Nat.mul_le_mul_left Vp.card hq4
            have hmx : 4 ≤ max Vp.card Vm.card := le_trans hq4 (le_max_right _ _)
            omega
    omega
  exact ⟨hdeg_sum, hVm_deg, hpq_sum, hp_ge2, hq_ge2, he_max, he_gt⟩

-- Helper: any tournament subset S where every vertex has out-degree <= 1 in S has |S| <= 3
lemma card_le_three_of_outdeg_le_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : Digraph V} [DecidableRel G.Adj] (hG : G.IsTournament) (S : Finset V)
    (hdeg : ∀ v ∈ S, (S.filter (fun u => G.Adj v u)).card ≤ 1) : S.card ≤ 3 := by
  classical
  have hint := tournament_two_mul_internal_arcs hG S
  have hsum : ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card ≤ S.card := by
    have heq : ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card =
        ∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun v _ => by rw [Finset.card_filter])
    rw [heq]
    calc ∑ v ∈ S, (S.filter (fun u => G.Adj v u)).card ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum hdeg
      _ = S.card := by simp
  by_contra hgt
  have h4 : 4 ≤ S.card := by omega
  have hmul : 4 * S.card ≤ S.card * S.card := Nat.mul_le_mul_right S.card h4
  omega

-- Claim (A): w0 -> w1 -> w2 -> w3 distinct, w0 in V+, w2, w3 in V-
lemma claim_A {n : ℕ} (hn : 6 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    ∃ w0 w1 w2 w3 : V,
      w0 ≠ w1 ∧ w0 ≠ w2 ∧ w0 ≠ w3 ∧ w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3 ∧
      G.Adj w0 w1 ∧ G.Adj w1 w2 ∧ G.Adj w2 w3 ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj w0 u)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u w2)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u w3)).card := by
  classical
  let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
  let Vm := Vpᶜ
  obtain ⟨_, hVm_deg, _, _, _, _, he_gt⟩ := cross_edges_Vp_Vm hn hV hG hNoSrc hNoSnk
  let S := Vm.filter (fun y => ∃ z ∈ Vm, G.Adj y z)
  let TA := Finset.univ.filter (fun v : V => ∃ y ∈ S, G.Adj v y)
  have hVmS_le1 : (Vm \ S).card ≤ 1 := by
    by_contra hgt
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Vm \ S).card)
    have ha' := Finset.mem_sdiff.mp ha; have hb' := Finset.mem_sdiff.mp hb
    rcases adj_or_rev_of_isTournament hG hab with h | h
    · exact ha'.2 (Finset.mem_filter.mpr ⟨ha'.1, b, hb'.1, h⟩)
    · exact hb'.2 (Finset.mem_filter.mpr ⟨hb'.1, a, ha'.1, h⟩)
  have hex_arc : ∃ w0 ∈ Vp, ∃ w1 ∈ TA, G.Adj w0 w1 := by
    by_contra hno
    push Not at hno
    have hTAVp_le1 : (TA ∩ Vp).card ≤ 1 := by
      by_contra hgt
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (TA ∩ Vp).card)
      have ha' := Finset.mem_inter.mp ha; have hb' := Finset.mem_inter.mp hb
      rcases adj_or_rev_of_isTournament hG hab with h | h
      · exact hno a ha'.2 b hb'.1 h
      · exact hno b hb'.2 a ha'.1 h
    have hVmTA_le3 : (Vm \ TA).card ≤ 3 := by
      refine card_le_three_of_outdeg_le_one hG (Vm \ TA) (fun y hy => ?_)
      have hy' := Finset.mem_sdiff.mp hy
      have hsub : (Vm \ TA).filter (fun z => G.Adj y z) ⊆ Vm \ S := fun z hz => by
        obtain ⟨hz1, hyz⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz1).1, fun hzS =>
          hy'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hzS, hyz⟩)⟩
      exact (Finset.card_le_card hsub).trans hVmS_le1
    have hsum_e : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card =
        ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun u _ => by rw [Finset.card_filter])
    have hbound : ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card ≤ Vp.card + 2 := by
      have hsplit : ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card =
          ∑ u ∈ Vp \ TA, (Vm.filter (fun y => G.Adj u y)).card +
          ∑ u ∈ TA ∩ Vp, (Vm.filter (fun y => G.Adj u y)).card := by
        rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun u h1 h2 =>
          (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1))]
        congr 1; ext u; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
      have h1 : ∑ u ∈ Vp \ TA, (Vm.filter (fun y => G.Adj u y)).card ≤ (Vp \ TA).card := by
        calc _ ≤ ∑ _u ∈ Vp \ TA, 1 := Finset.sum_le_sum (fun u hu => by
              have hnotTA := (Finset.mem_sdiff.mp hu).2
              have hsub : Vm.filter (fun y => G.Adj u y) ⊆ Vm \ S := fun y hy => by
                obtain ⟨hyVm, huy⟩ := Finset.mem_filter.mp hy
                exact Finset.mem_sdiff.mpr ⟨hyVm, fun hyS => hnotTA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyS, huy⟩)⟩
              exact (Finset.card_le_card hsub).trans hVmS_le1)
          _ = (Vp \ TA).card := by simp
      have h2 : ∑ u ∈ TA ∩ Vp, (Vm.filter (fun y => G.Adj u y)).card ≤ 3 * (TA ∩ Vp).card := by
        calc _ ≤ ∑ _u ∈ TA ∩ Vp, 3 := Finset.sum_le_sum (fun u hu => by
              have huVp := (Finset.mem_inter.mp hu).2
              have hsub : Vm.filter (fun y => G.Adj u y) ⊆ Vm \ TA := fun y hy => by
                obtain ⟨hyVm, huy⟩ := Finset.mem_filter.mp hy
                exact Finset.mem_sdiff.mpr ⟨hyVm, fun hyTA => hno u huVp y hyTA huy⟩
              exact (Finset.card_le_card hsub).trans hVmTA_le3)
          _ = 3 * (TA ∩ Vp).card := by simp [Nat.mul_comm]
      have hcard_split : (Vp \ TA).card + (TA ∩ Vp).card = Vp.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 =>
          (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1))]
        congr 1; ext u; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
      omega
    dsimp only [Vp, Vm] at he_gt hsum_e hbound; omega
  obtain ⟨w0, hw0Vp, w1, hw1TA, h01⟩ := hex_arc
  obtain ⟨w2, hw2S, h12⟩ := (Finset.mem_filter.mp hw1TA).2
  obtain ⟨hw2Vm, w3, hw3Vm, h23⟩ := Finset.mem_filter.mp hw2S
  have hne01 : w0 ≠ w1 := ne_of_adj_tournament hG h01
  have hne12 : w1 ≠ w2 := ne_of_adj_tournament hG h12
  have hne23 : w2 ≠ w3 := ne_of_adj_tournament hG h23
  have hne02 : w0 ≠ w2 := fun h => Finset.mem_compl.mp hw2Vm (h ▸ hw0Vp)
  have hne03 : w0 ≠ w3 := fun h => Finset.mem_compl.mp hw3Vm (h ▸ hw0Vp)
  have hne13 : w1 ≠ w3 := fun h => not_adj_rev_of_tournament hG h12 (h ▸ h23)
  exact ⟨w0, w1, w2, w3, hne01, hne02, hne03, hne12, hne13, hne23, h01, h12, h23,
    (Finset.mem_filter.mp hw0Vp).2, hVm_deg w2 hw2Vm, hVm_deg w3 hw3Vm⟩

-- Claim (B): w3 -> w0, w0 -> w1, w0 -> w2 distinct, w3 in V+, w1, w2 in V-
lemma claim_B {n : ℕ} (hn : 6 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    ∃ w0 w1 w2 w3 : V,
      w0 ≠ w1 ∧ w0 ≠ w2 ∧ w0 ≠ w3 ∧ w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3 ∧
      G.Adj w3 w0 ∧ G.Adj w0 w1 ∧ G.Adj w0 w2 ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj w3 u)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u w1)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u w2)).card := by
  classical
  let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
  let Vm := Vpᶜ
  obtain ⟨_, hVm_deg, _, _, _, _, he_gt⟩ := cross_edges_Vp_Vm hn hV hG hNoSrc hNoSnk
  let TB := Finset.univ.filter (fun v : V => 2 ≤ (Vm.filter (fun y => G.Adj v y)).card)
  have hex_arc : ∃ w3 ∈ Vp, ∃ w0 ∈ TB, G.Adj w3 w0 := by
    by_contra hno; push Not at hno
    have hTBVp_le1 : (TB ∩ Vp).card ≤ 1 := by
      by_contra hgt
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (TB ∩ Vp).card)
      have ha' := Finset.mem_inter.mp ha; have hb' := Finset.mem_inter.mp hb
      rcases adj_or_rev_of_isTournament hG hab with h | h
      · exact hno a ha'.2 b hb'.1 h
      · exact hno b hb'.2 a ha'.1 h
    have hVmTB_le3 : (Vm \ TB).card ≤ 3 := by
      refine card_le_three_of_outdeg_le_one hG (Vm \ TB) (fun y hy => ?_)
      have hnotTB := (Finset.mem_sdiff.mp hy).2
      have hle1 : (Vm.filter (fun z => G.Adj y z)).card ≤ 1 := by
        by_contra hge; exact hnotTB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      exact (Finset.card_le_card (fun z hz => by
        obtain ⟨hz1, hyz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz1).1, hyz⟩)).trans hle1
    have hsum_e : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card =
        ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun u _ => by rw [Finset.card_filter])
    have hbound : ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card ≤ Vp.card + 2 := by
      have hsplit : ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card =
          ∑ u ∈ Vp \ TB, (Vm.filter (fun y => G.Adj u y)).card +
          ∑ u ∈ TB ∩ Vp, (Vm.filter (fun y => G.Adj u y)).card := by
        rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun u h1 h2 =>
          (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1))]
        congr 1; ext u; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
      have h1 : ∑ u ∈ Vp \ TB, (Vm.filter (fun y => G.Adj u y)).card ≤ (Vp \ TB).card := by
        calc _ ≤ ∑ _u ∈ Vp \ TB, 1 := Finset.sum_le_sum (fun u hu => by
              have hnotTB := (Finset.mem_sdiff.mp hu).2
              by_contra hge; exact hnotTB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
          _ = (Vp \ TB).card := by simp
      have h2 : ∑ u ∈ TB ∩ Vp, (Vm.filter (fun y => G.Adj u y)).card ≤ 3 * (TB ∩ Vp).card := by
        calc _ ≤ ∑ _u ∈ TB ∩ Vp, 3 := Finset.sum_le_sum (fun u hu => by
              have huVp := (Finset.mem_inter.mp hu).2
              have hsub : Vm.filter (fun y => G.Adj u y) ⊆ Vm \ TB := fun y hy => by
                obtain ⟨hyVm, huy⟩ := Finset.mem_filter.mp hy
                exact Finset.mem_sdiff.mpr ⟨hyVm, fun hyTB => hno u huVp y hyTB huy⟩
              exact (Finset.card_le_card hsub).trans hVmTB_le3)
          _ = 3 * (TB ∩ Vp).card := by simp [Nat.mul_comm]
      have hcard_split : (Vp \ TB).card + (TB ∩ Vp).card = Vp.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun u h1 h2 =>
          (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1))]
        congr 1; ext u; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
      omega
    dsimp only [Vp, Vm] at he_gt hsum_e hbound; omega
  obtain ⟨w3, hw3Vp, w0, hw0TB, h30⟩ := hex_arc
  obtain ⟨w1, hw1, w2, hw2, h12⟩ := Finset.one_lt_card.mp
    (by have := (Finset.mem_filter.mp hw0TB).2; omega : 1 < (Vm.filter (fun y => G.Adj w0 y)).card)
  obtain ⟨hw1Vm, h01⟩ := Finset.mem_filter.mp hw1
  obtain ⟨hw2Vm, h02⟩ := Finset.mem_filter.mp hw2
  exact ⟨w0, w1, w2, w3, ne_of_adj_tournament hG h01, ne_of_adj_tournament hG h02,
    (ne_of_adj_tournament hG h30).symm, h12,
    fun h => Finset.mem_compl.mp hw1Vm (h ▸ hw3Vp),
    fun h => Finset.mem_compl.mp hw2Vm (h ▸ hw3Vp),
    h30, h01, h02, (Finset.mem_filter.mp hw3Vp).2, hVm_deg w1 hw1Vm, hVm_deg w2 hw2Vm⟩

-- Claim (D): w0 -> w1 -> w2 -> w3 <- ws distinct, w0 in V+, w3, ws in V-
lemma claim_D {n : ℕ} (hn : 6 ≤ n)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    ∃ w0 w1 w2 w3 ws : V,
      w0 ≠ w1 ∧ w0 ≠ w2 ∧ w0 ≠ w3 ∧ w0 ≠ ws ∧
      w1 ≠ w2 ∧ w1 ≠ w3 ∧ w1 ≠ ws ∧ w2 ≠ w3 ∧ w2 ≠ ws ∧ w3 ≠ ws ∧
      G.Adj w0 w1 ∧ G.Adj w1 w2 ∧ G.Adj w2 w3 ∧ G.Adj ws w3 ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj w0 u)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u w3)).card ∧
      n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj u ws)).card := by
  classical
  let Vp := Finset.univ.filter (fun v : V => n - 1 ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card)
  let Vm := Vpᶜ
  obtain ⟨hdeg_sum, hVm_deg, hpq_sum, hp_ge2, hq_ge2, he_max, _⟩ := cross_edges_Vp_Vm hn hV hG hNoSrc hNoSnk
  by_cases hq6 : 6 ≤ Vm.card
  · -- Case 1: q >= 6 => some w0 in V+ beats >= 4 vertices of V-
    have hgt3p : 3 * Vp.card < ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card := by
      have hmul : 6 * Vp.card ≤ Vp.card * Vm.card := by
        rw [Nat.mul_comm 6 Vp.card]; exact Nat.mul_le_mul_left Vp.card hq6
      have hmx : 6 ≤ max Vp.card Vm.card := le_trans hq6 (le_max_right _ _)
      dsimp only [Vp, Vm] at he_max hmul hmx ⊢; omega
    have hex_w0 : ∃ w0 ∈ Vp, 4 ≤ (Vm.filter (fun y => G.Adj w0 y)).card := by
      by_contra hno; push Not at hno
      have hsum : ((Vp ×ˢ Vm).filter (fun p => G.Adj p.1 p.2)).card =
          ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        exact Finset.sum_congr rfl (fun u _ => by rw [Finset.card_filter])
      have hle : ∑ u ∈ Vp, (Vm.filter (fun y => G.Adj u y)).card ≤ 3 * Vp.card := by
        calc _ ≤ ∑ _u ∈ Vp, 3 := Finset.sum_le_sum (fun u hu => by have := hno u hu; omega)
          _ = 3 * Vp.card := by simp [Nat.mul_comm]
      omega
    obtain ⟨w0, hw0Vp, hge4⟩ := hex_w0
    obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hge4
    let GU : Digraph U := ⟨fun a b => G.Adj a.1 b.1⟩
    have hGU : GU.IsTournament := isTournament_induce hG U
    obtain ⟨σU, hRU, _⟩ := exists_median_order GU hGU
    have hcardU : Fintype.card U = 4 := by rw [Fintype.card_coe, hUcard]
    let y0 := (σU ⟨0, by omega⟩).1; let y1 := (σU ⟨1, by omega⟩).1
    let y2 := (σU ⟨2, by omega⟩).1; let y3 := (σU ⟨3, by omega⟩).1
    have hy_in : ∀ k : Fin 4, (σU ⟨k.val, by omega⟩).1 ∈ Vm ∧ G.Adj w0 (σU ⟨k.val, by omega⟩).1 := fun k =>
      Finset.mem_filter.mp (hUsub (σU ⟨k.val, by omega⟩).2)
    have hy_inj : ∀ i j : Fin 4, (σU ⟨i.val, by omega⟩).1 = (σU ⟨j.val, by omega⟩).1 → i = j := fun i j h =>
      Fin.ext (by have := congrArg Fin.val (σU.injective (Subtype.ext h)); simpa using this)
    have ha01 : G.Adj y0 y1 := median_adj_succ hRU ⟨0, by omega⟩ (by dsimp only; omega)
    have ha12 : G.Adj y1 y2 := median_adj_succ hRU ⟨1, by omega⟩ (by dsimp only; omega)
    have ha23 : G.Adj y2 y3 := median_adj_succ hRU ⟨2, by omega⟩ (by dsimp only; omega)
    -- Extract (w1 -> w2 -> w3 <- ws) from 4-tournament {y0, y1, y2, y3}
    have hex4 : ∃ i1 i2 i3 is : Fin 4, i1 ≠ i2 ∧ i1 ≠ i3 ∧ i1 ≠ is ∧ i2 ≠ i3 ∧ i2 ≠ is ∧ i3 ≠ is ∧
        G.Adj (σU ⟨i1.val, by omega⟩).1 (σU ⟨i2.val, by omega⟩).1 ∧
        G.Adj (σU ⟨i2.val, by omega⟩).1 (σU ⟨i3.val, by omega⟩).1 ∧
        G.Adj (σU ⟨is.val, by omega⟩).1 (σU ⟨i3.val, by omega⟩).1 := by
      by_cases h03 : G.Adj y0 y3
      · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩,
          by decide, by decide, by decide, by decide, by decide, by decide, ha12, ha23, h03⟩
      · have h30 : G.Adj y3 y0 := (adj_or_rev_of_isTournament hG (fun h => by have := hy_inj ⟨0, by decide⟩ ⟨3, by decide⟩ h; simp at this)).resolve_left h03
        by_cases h31 : G.Adj y3 y1
        · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
            by decide, by decide, by decide, by decide, by decide, by decide, ha23, h31, ha01⟩
        · have h13 : G.Adj y1 y3 := (adj_or_rev_of_isTournament hG (fun h => by have := hy_inj ⟨3, by decide⟩ ⟨1, by decide⟩ h; simp at this)).resolve_left h31
          by_cases h02 : G.Adj y0 y2
          · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩,
              by decide, by decide, by decide, by decide, by decide, by decide, h02, ha23, h13⟩
          · have h20 : G.Adj y2 y0 := (adj_or_rev_of_isTournament hG (fun h => by have := hy_inj ⟨0, by decide⟩ ⟨2, by decide⟩ h; simp at this)).resolve_left h02
            exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩,
              by decide, by decide, by decide, by decide, by decide, by decide, ha12, h20, h30⟩
    obtain ⟨i1, i2, i3, is, d12, d13, d1s, d23, d2s, d3s, e12, e23, es3⟩ := hex4
    exact ⟨w0, (σU ⟨i1.val, by omega⟩).1, (σU ⟨i2.val, by omega⟩).1, (σU ⟨i3.val, by omega⟩).1, (σU ⟨is.val, by omega⟩).1,
      fun h => Finset.mem_compl.mp (hy_in i1).1 (h ▸ hw0Vp),
      fun h => Finset.mem_compl.mp (hy_in i2).1 (h ▸ hw0Vp),
      fun h => Finset.mem_compl.mp (hy_in i3).1 (h ▸ hw0Vp),
      fun h => Finset.mem_compl.mp (hy_in is).1 (h ▸ hw0Vp),
      fun h => d12 (hy_inj _ _ h), fun h => d13 (hy_inj _ _ h), fun h => d1s (hy_inj _ _ h),
      fun h => d23 (hy_inj _ _ h), fun h => d2s (hy_inj _ _ h), fun h => d3s (hy_inj _ _ h),
      (hy_in i1).2, e12, e23, es3,
      (Finset.mem_filter.mp hw0Vp).2, hVm_deg _ (hy_in i3).1, hVm_deg _ (hy_in is).1⟩
  · -- Case 2: q <= 5 => pick arc ws -> w3 in Vm, analyze X = N^-(w3) \ {ws}
    obtain ⟨a0, ha0, b0, hb0, hab0⟩ := Finset.one_lt_card.mp (by dsimp only [Vp, Vm] at hq_ge2 ⊢; omega : 1 < Vm.card)
    have hex_arcVm : ∃ ws ∈ Vm, ∃ w3 ∈ Vm, G.Adj ws w3 := by
      rcases adj_or_rev_of_isTournament hG hab0 with h | h
      · exact ⟨a0, ha0, b0, hb0, h⟩
      · exact ⟨b0, hb0, a0, ha0, h⟩
    obtain ⟨ws, hwsVm, w3, hw3Vm, hws3⟩ := hex_arcVm
    let X := (Finset.univ.filter (fun u : V => G.Adj u w3)).erase ws
    have hX_card : n - 2 ≤ X.card := by
      have h1 := hVm_deg w3 hw3Vm
      have h2 := Finset.card_erase_of_mem (s := Finset.univ.filter (fun u : V => G.Adj u w3))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hws3⟩)
      dsimp only [X]; omega
    by_cases hXVp3 : 3 ≤ (X ∩ Vp).card
    · -- Subcase 2a: directed P3 inside X ∩ Vp
      obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq hXVp3
      let GU : Digraph U := ⟨fun a b => G.Adj a.1 b.1⟩
      have hGU : GU.IsTournament := isTournament_induce hG U
      obtain ⟨σU, hRU, _⟩ := exists_median_order GU hGU
      have hcardU : Fintype.card U = 3 := by rw [Fintype.card_coe, hUcard]
      let w0 := (σU ⟨0, by omega⟩).1; let w1 := (σU ⟨1, by omega⟩).1; let w2 := (σU ⟨2, by omega⟩).1
      have hw_mem : ∀ k : Fin 3, (σU ⟨k.val, by omega⟩).1 ∈ X ∧ (σU ⟨k.val, by omega⟩).1 ∈ Vp := fun k =>
        Finset.mem_inter.mp (hUsub (σU ⟨k.val, by omega⟩).2)
      have h01 : G.Adj w0 w1 := median_adj_succ hRU ⟨0, by omega⟩ (by dsimp only; omega)
      have h12 : G.Adj w1 w2 := median_adj_succ hRU ⟨1, by omega⟩ (by dsimp only; omega)
      have h23 : G.Adj w2 w3 := (Finset.mem_filter.mp (Finset.mem_erase.mp (hw_mem ⟨2, by decide⟩).1).2).2
      have hne01 : w0 ≠ w1 := ne_of_adj_tournament hG h01
      have hne12 : w1 ≠ w2 := ne_of_adj_tournament hG h12
      have hne02 : w0 ≠ w2 := fun h => by
        have := congrArg Fin.val (σU.injective (Subtype.ext h)); simp at this
      exact ⟨w0, w1, w2, w3, ws, hne01, hne02,
        fun h => Finset.mem_compl.mp hw3Vm (h ▸ (hw_mem ⟨0, by decide⟩).2),
        fun h => Finset.mem_compl.mp hwsVm (h ▸ (hw_mem ⟨0, by decide⟩).2),
        hne12,
        fun h => Finset.mem_compl.mp hw3Vm (h ▸ (hw_mem ⟨1, by decide⟩).2),
        fun h => Finset.mem_compl.mp hwsVm (h ▸ (hw_mem ⟨1, by decide⟩).2),
        ne_of_adj_tournament hG h23,
        (Finset.mem_erase.mp (hw_mem ⟨2, by decide⟩).1).1,
        (ne_of_adj_tournament hG hws3).symm,
        h01, h12, h23, hws3,
        (Finset.mem_filter.mp (hw_mem ⟨0, by decide⟩).2).2, hVm_deg w3 hw3Vm, hVm_deg ws hwsVm⟩
    · -- Subcase 2b: |X ∩ Vp| <= 2 => X_good = {v in X : d+_X(v) >= 1} has |X_good| >= 3
      let Xgood := X.filter (fun v => ∃ z ∈ X, G.Adj v z)
      have hXXg_le1 : (X \ Xgood).card ≤ 1 := by
        by_contra hgt
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (X \ Xgood).card)
        have ha' := Finset.mem_sdiff.mp ha; have hb' := Finset.mem_sdiff.mp hb
        rcases adj_or_rev_of_isTournament hG hab with h | h
        · exact ha'.2 (Finset.mem_filter.mpr ⟨ha'.1, b, hb'.1, h⟩)
        · exact hb'.2 (Finset.mem_filter.mpr ⟨hb'.1, a, ha'.1, h⟩)
      have hXg_ge3 : 3 ≤ Xgood.card := by
        have hsub : Xgood ⊆ X := Finset.filter_subset _ _
        have hs := Finset.card_sdiff_add_card_eq_card hsub
        omega
      have hex_arcXg : ∃ w0 ∈ Vp, ∃ w1 ∈ Xgood, G.Adj w0 w1 := by
        by_contra hno; push Not at hno
        -- Pick v in Xgood \ Vp (nonempty since |Xgood| >= 3 > 2 >= |X ∩ Vp|)!
        have hdiff_pos : 0 < (Xgood \ Vp).card := by
          have hsub : Xgood ∩ Vp ⊆ X ∩ Vp := Finset.inter_subset_inter_right (Finset.filter_subset _ _)
          have hle := Finset.card_le_card hsub
          have hs := Finset.card_sdiff_add_card_inter Xgood Vp
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hdiff_pos
        have hvXg : v ∈ Xgood := (Finset.mem_sdiff.mp hv).1
        have hvnotVp : v ∉ Vp := (Finset.mem_sdiff.mp hv).2
        have hvVm : v ∈ Vm := Finset.mem_compl.mpr hvnotVp
        have hVp_sub : Vp ⊆ Finset.univ.filter (fun u : V => G.Adj v u) := fun u hu => by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hne : u ≠ v := fun h => hvnotVp (h ▸ hu)
          exact (adj_or_rev_of_isTournament hG hne).resolve_left (hno u hu v hvXg)
        have hp_le : Vp.card ≤ (Finset.univ.filter (fun u : V => G.Adj v u)).card := Finset.card_le_card hVp_sub
        have hv_in := hVm_deg v hvVm
        have hv_sum := hdeg_sum v
        dsimp only [Vp, Vm] at hpq_sum hp_le hq6; omega
      obtain ⟨w0, hw0Vp, w1, hw1Xg, h01⟩ := hex_arcXg
      obtain ⟨hw1X, w2, hw2X, h12⟩ := Finset.mem_filter.mp hw1Xg
      have h23 : G.Adj w2 w3 := (Finset.mem_filter.mp (Finset.mem_erase.mp hw2X).2).2
      have h13 : G.Adj w1 w3 := (Finset.mem_filter.mp (Finset.mem_erase.mp hw1X).2).2
      exact ⟨w0, w1, w2, w3, ws,
        ne_of_adj_tournament hG h01,
        fun h => not_adj_rev_of_tournament hG h01 (h ▸ h12),
        fun h => Finset.mem_compl.mp hw3Vm (h ▸ hw0Vp),
        fun h => Finset.mem_compl.mp hwsVm (h ▸ hw0Vp),
        ne_of_adj_tournament hG h12,
        ne_of_adj_tournament hG h13,
        (Finset.mem_erase.mp hw1X).1,
        ne_of_adj_tournament hG h23,
        (Finset.mem_erase.mp hw2X).1,
        (ne_of_adj_tournament hG hws3).symm,
        h01, h12, h23, hws3,
        (Finset.mem_filter.mp hw0Vp).2, hVm_deg w3 hw3Vm, hVm_deg ws hwsVm⟩

-- Greedy leaf absorption for Claims A and B (1 out-hub in V+, 2 in-hubs in V-, n-k = 4)
lemma embeds_of_Vp_Vm_core4
    {n : ℕ}
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (A : Finset W) (hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hcard_id : 4 + A.card + (Finset.univ \ (Finset.univ.image u ∪ A)).card = n)
    (hA_all_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z)
    (hB_all_leaf : ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ∀ z : W, ¬ D.Adj z y)
    (hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (ip im1 im2 : Fin 4) (hm12 : im1 ≠ im2)
    (hmaskP : ∀ i : Fin 4, i ≠ ip → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (hmaskM : ∀ i : Fin 4, i ≠ im1 → i ≠ im2 → ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hG : G.IsTournament)
    (t : Fin 4 → V) (ht_inj : Function.Injective t)
    (ht_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → G.Adj (t i) (t j))
    (hdP : n - 1 ≤ (Finset.univ.filter (fun v : V => G.Adj (t ip) v)).card)
    (hdM1 : n - 1 ≤ (Finset.univ.filter (fun v : V => G.Adj v (t im1))).card)
    (hdM2 : n - 1 ≤ (Finset.univ.filter (fun v : V => G.Adj v (t im2))).card) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let B1 := B.filter (fun y => D.Adj y (u im1))
  let B2 := B.filter (fun y => D.Adj y (u im2))
  have hdisj_B12 : Disjoint B1 B2 := Finset.disjoint_left.mpr (fun y h1 h2 => by
    have hnotHA := (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out y
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
      (fun h => hnotHA (Finset.mem_union_right _ h)))
    have e1 : u im1 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h1).2⟩)
    have e2 : u im2 = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h2).2⟩)
    exact hm12 (hu_inj (e1.trans e2.symm)))
  have hB_cov : B1 ∪ B2 = B := by
    ext y; simp only [B1, B2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hyB
      have hnotHA := (Finset.mem_sdiff.mp hyB).2
      have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj y z)).card := by
        rw [hB_out y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          (fun h => hnotHA (Finset.mem_union_right _ h))]; omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hDyz := (Finset.mem_filter.mp hz).2
      have hzH : z ∈ H := by
        by_contra hznotH
        by_cases hzA : z ∈ A
        · exact (hno_AB z hzA y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
            (fun h => hnotHA (Finset.mem_union_right _ h))).2 hDyz
        · exact hB_all_leaf z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hznotH hzA⟩) y hDyz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
      by_cases h1 : i = im1
      · exact Or.inl ⟨hyB, h1 ▸ hDyz⟩
      · by_cases h2 : i = im2
        · exact Or.inr ⟨hyB, h2 ▸ hDyz⟩
        · exact absurd hDyz (hmaskM i h1 h2 y hyB)
  have hB_sum : B1.card + B2.card = B.card := by rw [← Finset.card_union_of_disjoint hdisj_B12, hB_cov]
  have hAB_disj : Disjoint A B := Finset.disjoint_left.mpr (fun x hxA hxB =>
    (Finset.mem_sdiff.mp hxB).2 (Finset.mem_union_right _ hxA))
  have hd02 : Disjoint B1 A := Finset.disjoint_left.mpr (fun w h1 h2 => Finset.disjoint_right.mp hAB_disj (Finset.mem_filter.mp h1).1 h2)
  have hd12 : Disjoint B2 A := Finset.disjoint_left.mpr (fun w h1 h2 => Finset.disjoint_right.mp hAB_disj (Finset.mem_filter.mp h1).1 h2)
  let tH : Finset V := Finset.univ.image t
  have htH_card : tH.card = 4 := by rw [Finset.card_image_of_injective _ ht_inj, Finset.card_univ, Fintype.card_fin]
  let P0 := (Finset.univ.filter (fun v : V => G.Adj v (t im1))) \ tH
  let P1 := (Finset.univ.filter (fun v : V => G.Adj v (t im2))) \ tH
  let P2 := (Finset.univ.filter (fun v : V => G.Adj (t ip) v)) \ tH
  have hP0_card : n - 4 ≤ P0.card := by
    have hnot : t im1 ∉ Finset.univ.filter (fun v : V => G.Adj v (t im1)) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj v (t im1))) ∩ tH ⊆ tH.erase (t im1) := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj v (t im1))) ∩ tH).card ≤ 3 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨im1, Finset.mem_univ _, rfl⟩), htH_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj v (t im1))) tH
    dsimp only [P0]; omega
  have hP1_card : n - 4 ≤ P1.card := by
    have hnot : t im2 ∉ Finset.univ.filter (fun v : V => G.Adj v (t im2)) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj v (t im2))) ∩ tH ⊆ tH.erase (t im2) := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj v (t im2))) ∩ tH).card ≤ 3 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨im2, Finset.mem_univ _, rfl⟩), htH_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj v (t im2))) tH
    dsimp only [P1]; omega
  have hP2_card : n - 4 ≤ P2.card := by
    have hnot : t ip ∉ Finset.univ.filter (fun v : V => G.Adj (t ip) v) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj (t ip) v)) ∩ tH ⊆ tH.erase (t ip) := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj (t ip) v)) ∩ tH).card ≤ 3 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (Finset.mem_image.mpr ⟨ip, Finset.mem_univ _, rfl⟩), htH_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj (t ip) v)) tH
    dsimp only [P2]; omega
  obtain ⟨g0, hg0_inj, hg0_B1, hg0_B2, hg0_A⟩ := alloc_three_buckets hdisj_B12 hd02 hd12
    (P0 := P0) (P1 := P1) (P2 := P2)
    (by dsimp only [B, H] at hB_sum; omega) (by dsimp only [B, H] at hB_sum; omega) (by dsimp only [B, H] at hB_sum; omega)
  have hset_eq : A ∪ B = B1 ∪ B2 ∪ A := by rw [← hB_cov, Finset.union_comm]
  let g : ↥(A ∪ B) → V := fun w => g0 ⟨w.1, hset_eq ▸ w.2⟩
  refine embeds_of_core4_direct_leaves u hu_inj A hHA_disj hA_all_leaf hB_all_leaf hA_in hB_out hno_AB hno_HB
    t ht_inj ht_adj g (fun x y h => Subtype.ext (congrArg (fun z : ↥(B1 ∪ B2 ∪ A) => z.1) (hg0_inj h))) ?_ ?_ ?_
  · intro w i heq
    have hti : t i ∈ tH := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hw' : w.1 ∈ B1 ∪ B2 ∪ A := hset_eq ▸ w.2
    have heq' : g0 ⟨w.1, hw'⟩ = t i := heq
    rcases Finset.mem_union.mp hw' with h12 | hA
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact (Finset.mem_sdiff.mp (hg0_B1 ⟨w.1, hw'⟩ h1)).2 (heq' ▸ hti)
      · exact (Finset.mem_sdiff.mp (hg0_B2 ⟨w.1, hw'⟩ h2)).2 (heq' ▸ hti)
    · exact (Finset.mem_sdiff.mp (hg0_A ⟨w.1, hw'⟩ hA)).2 (heq' ▸ hti)
  · intro w hwA i hDui
    have hip : i = ip := by by_contra h; exact hmaskP i h w.1 hwA hDui
    subst hip
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_A ⟨w.1, hset_eq ▸ w.2⟩ hwA)).1).2
  · intro w hwB i hDwi
    by_cases h1 : i = im1
    · subst h1
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_B1 ⟨w.1, hset_eq ▸ w.2⟩ (Finset.mem_filter.mpr ⟨hwB, hDwi⟩))).1).2
    · have h2 : i = im2 := by by_contra h; exact hmaskM i h1 h w.1 hwB hDwi
      subst h2
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_B2 ⟨w.1, hset_eq ▸ w.2⟩ (Finset.mem_filter.mpr ⟨hwB, hDwi⟩))).1).2

-- Greedy leaf absorption for Claim D (P4+++ bare path at n-k = 5: |A| = kA, |B| = kB + 1 with single internal xs in B)
lemma embeds_of_claim_D
    {n : ℕ} (hn : 6 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] {D : Digraph W} [DecidableRel D.Adj]
    (u : Fin 4 → W) (hu_inj : Function.Injective u)
    (hH_adj : ∀ i j : Fin 4, D.Adj (u i) (u j) → i.val + 1 = j.val)
    (A : Finset W) (_hHA_disj : ∀ i : Fin 4, u i ∉ A)
    (hcard_id : 4 + A.card + (Finset.univ \ (Finset.univ.image u ∪ A)).card = n)
    (hA_all_leaf : ∀ x ∈ A, ∀ z : W, ¬ D.Adj x z)
    (hB_one_int : (Finset.univ \ (Finset.univ.image u ∪ A)).card =
      ((Finset.univ \ (Finset.univ.image u ∪ A)).filter (fun y => ∀ z : W, ¬ D.Adj z y)).card + 1)
    (_hA_in : ∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
    (hB_out : ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
      (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1)
    (hno_AB : ∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    (hno_HB : ∀ i : Fin 4, ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj (u i) y)
    (hmaskP : ∀ i : Fin 4, i ≠ ⟨0, by decide⟩ → ∀ x ∈ A, ¬ D.Adj (u i) x)
    (hmaskM : ∀ i : Fin 4, i ≠ ⟨3, by decide⟩ →
      ∀ y ∈ Finset.univ \ (Finset.univ.image u ∪ A), ¬ D.Adj y (u i))
    (hIrrefl : ∀ w : W, ¬ D.Adj w w)
    {V : Type} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 2 * n - 2) (hG : G.IsTournament)
    (hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v) (hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u) :
    Embeds D G := by
  classical
  let H : Finset W := Finset.univ.image u
  let B : Finset W := Finset.univ \ (H ∪ A)
  let BL := B.filter (fun y => ∀ z : W, ¬ D.Adj z y)
  have hu_memH : ∀ i : Fin 4, u i ∈ H := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hBint_card : (B \ BL).card = 1 := by
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun y => ∀ z : W, ¬ D.Adj z y) B)
    dsimp only [B, H, BL] at hs ⊢; omega
  obtain ⟨xs, hxs_eq⟩ := Finset.card_eq_one.mp hBint_card
  have hxs_mem : xs ∈ B \ BL := hxs_eq ▸ Finset.mem_singleton_self xs
  have hxsB : xs ∈ B := (Finset.mem_sdiff.mp hxs_mem).1
  have hxs_notHA : xs ∉ H ∪ A := (Finset.mem_sdiff.mp hxsB).2
  have hB_other_leaf : ∀ y ∈ B, y ≠ xs → ∀ z : W, ¬ D.Adj z y := by
    intro y hyB hyne
    have hyBL : y ∈ BL := by
      by_contra hnot
      have : y ∈ B \ BL := Finset.mem_sdiff.mpr ⟨hyB, hnot⟩
      rw [hxs_eq] at this; exact hyne (Finset.mem_singleton.mp this)
    exact (Finset.mem_filter.mp hyBL).2
  have hxs_adj_u3 : D.Adj xs (u ⟨3, by decide⟩) := by
    have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj xs z)).card := by
      rw [hB_out xs (fun i hi => hxs_notHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
        (fun h => hxs_notHA (Finset.mem_union_right _ h))]; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hDxsz := (Finset.mem_filter.mp hz).2
    have hzH : z ∈ H := by
      by_contra hznotH
      by_cases hzA : z ∈ A
      · exact (hno_AB z hzA xs (fun i hi => hxs_notHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
          (fun h => hxs_notHA (Finset.mem_union_right _ h))).2 hDxsz
      · have hzB : z ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hznotH hzA⟩
        by_cases hzx : z = xs
        · exact hIrrefl xs (hzx ▸ hDxsz)
        · exact hB_other_leaf z hzB hzx xs hDxsz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
    have hi3 : i = ⟨3, by decide⟩ := by by_contra h; exact hmaskM i h xs hxsB hDxsz
    exact hi3 ▸ hDxsz
  -- Split B \ {xs} into B1 (in-leaves of xs) and B2 (in-leaves of u 3)
  let B' := B.erase xs
  let B1 := B'.filter (fun y => D.Adj y xs)
  let B2 := B'.filter (fun y => D.Adj y (u ⟨3, by decide⟩))
  have hdisj_B12 : Disjoint B1 B2 := Finset.disjoint_left.mpr (fun y h1 h2 => by
    have hyB : y ∈ B := (Finset.mem_erase.mp (Finset.mem_filter.mp h1).1).2
    have hnotHA := (Finset.mem_sdiff.mp hyB).2
    obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out y
      (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
      (fun h => hnotHA (Finset.mem_union_right _ h)))
    have e1 : xs = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h1).2⟩)
    have e2 : u ⟨3, by decide⟩ = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h2).2⟩)
    exact hxs_notHA (Finset.mem_union_left _ (e1.trans e2.symm ▸ hu_memH ⟨3, by decide⟩)))
  have hB'_cov : B1 ∪ B2 = B' := by
    ext y; simp only [B1, B2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hyB'
      have hyB : y ∈ B := (Finset.mem_erase.mp hyB').2
      have hnotHA := (Finset.mem_sdiff.mp hyB).2
      have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj y z)).card := by
        rw [hB_out y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
          (fun h => hnotHA (Finset.mem_union_right _ h))]; omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      have hDyz := (Finset.mem_filter.mp hz).2
      by_cases hzx : z = xs
      · exact Or.inl ⟨hyB', hzx ▸ hDyz⟩
      · have hzH : z ∈ H := by
          by_contra hznotH
          by_cases hzA : z ∈ A
          · exact (hno_AB z hzA y (fun i hi => hnotHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
              (fun h => hnotHA (Finset.mem_union_right _ h))).2 hDyz
          · exact hB_other_leaf z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hznotH hzA⟩) hzx y hDyz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzH
        have hi3 : i = ⟨3, by decide⟩ := by by_contra h; exact hmaskM i h y hyB hDyz
        exact Or.inr ⟨hyB', hi3 ▸ hDyz⟩
  have hB'_card : B'.card = B.card - 1 := Finset.card_erase_of_mem hxsB
  have hB'_sum : B1.card + B2.card = B.card - 1 := by rw [← Finset.card_union_of_disjoint hdisj_B12, hB'_cov, hB'_card]
  have hAB'_disj : Disjoint B' A := Finset.disjoint_left.mpr (fun y hyB' hyA =>
    (Finset.mem_sdiff.mp (Finset.mem_erase.mp hyB').2).2 (Finset.mem_union_right _ hyA))
  have hd02 : Disjoint B1 A := Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hAB'_disj
  have hd12 : Disjoint B2 A := Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hAB'_disj
  -- Apply Claim D!
  obtain ⟨w0, w1, w2, w3, ws, d01, d02, d03, d0s, d12, d13, d1s, d23, d2s, d3s,
    a01, a12, a23, as3, hd0, hd3, hds⟩ := claim_D hn hV hG hNoSrc hNoSnk
  let core : Finset V := {w0, w1, w2, w3, ws}
  have hcore_card : core.card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [d01, d02, d03, d0s]),
      Finset.card_insert_of_notMem (by simp [d12, d13, d1s]),
      Finset.card_insert_of_notMem (by simp [d23, d2s]),
      Finset.card_insert_of_notMem (by simp [d3s]), Finset.card_singleton]
  let P0 := (Finset.univ.filter (fun v : V => G.Adj v ws)) \ core
  let P1 := (Finset.univ.filter (fun v : V => G.Adj v w3)) \ core
  let P2 := (Finset.univ.filter (fun v : V => G.Adj w0 v)) \ core
  have hP0_card : n - 5 ≤ P0.card := by
    have hnot : ws ∉ Finset.univ.filter (fun v : V => G.Adj v ws) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj v ws)) ∩ core ⊆ core.erase ws := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv; exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj v ws)) ∩ core).card ≤ 4 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (by simp [core]), hcore_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj v ws)) core
    dsimp only [P0]; omega
  have hP1_card : n - 5 ≤ P1.card := by
    have hnot : w3 ∉ Finset.univ.filter (fun v : V => G.Adj v w3) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj v w3)) ∩ core ⊆ core.erase w3 := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv; exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj v w3)) ∩ core).card ≤ 4 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (by simp [core]), hcore_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj v w3)) core
    dsimp only [P1]; omega
  have hP2_card : n - 5 ≤ P2.card := by
    have hnot : w0 ∉ Finset.univ.filter (fun v : V => G.Adj w0 v) := fun h => hG.1 _ (Finset.mem_filter.mp h).2
    have hsub : (Finset.univ.filter (fun v : V => G.Adj w0 v)) ∩ core ⊆ core.erase w0 := fun v hv => by
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv; exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ h1), h2⟩
    have hle : ((Finset.univ.filter (fun v : V => G.Adj w0 v)) ∩ core).card ≤ 4 :=
      (Finset.card_le_card hsub).trans (by rw [Finset.card_erase_of_mem (by simp [core]), hcore_card])
    have hs := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun v : V => G.Adj w0 v)) core
    dsimp only [P2]; omega
  have hB_pos : 1 ≤ B.card := Finset.one_le_card.mpr ⟨xs, hxsB⟩
  obtain ⟨g0, hg0_inj, hg0_B1, hg0_B2, hg0_A⟩ := alloc_three_buckets hdisj_B12 hd02 hd12
    (P0 := P0) (P1 := P1) (P2 := P2)
    (by dsimp only [B, H] at hB'_sum hB_pos; omega) (by dsimp only [B, H] at hB'_sum hB_pos; omega)
    (by dsimp only [B, H] at hB'_sum hB_pos; omega)
  let t4 : Fin 4 → V := fun i => match i.val with | 0 => w0 | 1 => w1 | 2 => w2 | _ => w3
  have ht4_inj : Function.Injective t4 := by
    intro i j h; fin_cases i <;> fin_cases j <;> dsimp only [t4] at h <;>
      first | rfl | exact absurd h d01 | exact absurd h d02 | exact absurd h d03 |
        exact absurd h d01.symm | exact absurd h d12 | exact absurd h d13 |
        exact absurd h d02.symm | exact absurd h d12.symm | exact absurd h d23 |
        exact absurd h d03.symm | exact absurd h d13.symm | exact absurd h d23.symm
  have ht4_mem : ∀ i : Fin 4, t4 i ∈ core := fun i => by fin_cases i <;> simp [t4, core]
  have ht4_ne_ws : ∀ i : Fin 4, t4 i ≠ ws := fun i => by fin_cases i <;> dsimp only [t4] <;> assumption
  let φ : W → V := fun w =>
    if hwH : w ∈ H then t4 (Classical.choose (Finset.mem_image.mp hwH))
    else if hwxs : w = xs then ws
    else g0 ⟨w, by
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_right _ hwA
      · refine Finset.mem_union_left _ ?_
        rw [hB'_cov]
        exact Finset.mem_erase.mpr ⟨hwxs, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hwH hwA⟩⟩⟩
  have hφ_u : ∀ i : Fin 4, φ (u i) = t4 i := by
    intro i; simp only [φ, hu_memH i, ↓reduceDIte]
    rw [hu_inj (Classical.choose_spec (Finset.mem_image.mp (hu_memH i))).2]
  have hφ_xs : φ xs = ws := by
    have hnotH : xs ∉ H := fun h => hxs_notHA (Finset.mem_union_left _ h)
    simp only [φ, hnotH, ↓reduceDIte]
  have hg0_not_core : ∀ w : ↥(B1 ∪ B2 ∪ A), g0 w ∉ core := fun w => by
    rcases Finset.mem_union.mp w.2 with h12 | hA
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · exact (Finset.mem_sdiff.mp (hg0_B1 w h1)).2
      · exact (Finset.mem_sdiff.mp (hg0_B2 w h2)).2
    · exact (Finset.mem_sdiff.mp (hg0_A w hA)).2
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    by_cases hxH : x ∈ H <;> by_cases hyH : y ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
      rw [hφ_u i, hφ_u j] at hxy; rw [ht4_inj hxy]
    · exfalso; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH; rw [hφ_u i] at hxy
      by_cases hyx : y = xs
      · rw [hyx, hφ_xs] at hxy; exact ht4_ne_ws i hxy
      · simp only [φ, hyH, hyx, ↓reduceDIte] at hxy; exact hg0_not_core _ (hxy ▸ ht4_mem i)
    · exfalso; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH; rw [hφ_u j] at hxy
      by_cases hxx : x = xs
      · rw [hxx, hφ_xs] at hxy; exact ht4_ne_ws j hxy.symm
      · simp only [φ, hxH, hxx, ↓reduceDIte] at hxy; exact hg0_not_core _ (hxy.symm ▸ ht4_mem j)
    · by_cases hxx : x = xs <;> by_cases hyx : y = xs
      · exact hxx.trans hyx.symm
      · exfalso; rw [hxx, hφ_xs] at hxy; simp only [φ, hyH, hyx, ↓reduceDIte] at hxy
        have hws_core : ws ∈ core := by simp [core]
        exact hg0_not_core _ (hxy ▸ hws_core)
      · exfalso; rw [hyx, hφ_xs] at hxy; simp only [φ, hxH, hxx, ↓reduceDIte] at hxy
        have hws_core : ws ∈ core := by simp [core]
        exact hg0_not_core _ (hxy.symm ▸ hws_core)
      · simp only [φ, hxH, hyH, hxx, hyx, ↓reduceDIte] at hxy
        exact congrArg Subtype.val (hg0_inj hxy)
  have hφ_adj : ∀ x y : W, D.Adj x y → G.Adj (φ x) (φ y) := by
    intro x y hDxy
    by_cases hxH : x ∈ H
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxH; rw [hφ_u i]
      by_cases hyH : y ∈ H
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH; rw [hφ_u j]
        have hstep := hH_adj i j hDxy
        fin_cases i <;> fin_cases j <;> dsimp only [t4] <;> simp at hstep <;> assumption
      · by_cases hyA : y ∈ A
        · have hi0 : i = ⟨0, by decide⟩ := by by_contra h; exact hmaskP i h y hyA hDxy
          subst hi0
          have hyne : y ≠ xs := fun h => hxs_notHA (Finset.mem_union_right _ (h ▸ hyA))
          simp only [φ, hyH, hyne, ↓reduceDIte, t4]
          exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_A _ hyA)).1).2
        · exfalso; exact hno_HB i y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hyH hyA⟩) hDxy
    · by_cases hxA : x ∈ A
      · exact absurd hDxy (hA_all_leaf x hxA y)
      · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hxH hxA⟩
        by_cases hxx : x = xs
        · subst x; rw [hφ_xs]
          have hy_u3 : y = u ⟨3, by decide⟩ := by
            obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp (hB_out xs
              (fun i hi => hxs_notHA (Finset.mem_union_left _ (hi ▸ hu_memH i)))
              (fun h => hxs_notHA (Finset.mem_union_right _ h)))
            have e1 : y = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDxy⟩)
            have e2 : u ⟨3, by decide⟩ = z0 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs_adj_u3⟩)
            exact e1.trans e2.symm
          rw [hy_u3, hφ_u ⟨3, by decide⟩]; exact as3
        · have hxB' : x ∈ B' := Finset.mem_erase.mpr ⟨hxx, hxB⟩
          by_cases hyx : y = xs
          · subst y; rw [hφ_xs]
            simp only [φ, hxH, hxx, ↓reduceDIte]
            exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_B1 _ (Finset.mem_filter.mpr ⟨hxB', hDxy⟩))).1).2
          · have hyH : y ∈ H := by
              by_contra hynotH
              by_cases hyA : y ∈ A
              · exact (hno_AB y hyA x (fun i hi => hxH (hi ▸ hu_memH i)) hxA).2 hDxy
              · exact hB_other_leaf y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hynotH hyA⟩) hyx x hDxy
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyH
            have hj3 : j = ⟨3, by decide⟩ := by by_contra h; exact hmaskM j h x hxB hDxy
            subst hj3; rw [hφ_u ⟨3, by decide⟩]; simp only [φ, hxH, hxx, ↓reduceDIte, t4]
            exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hg0_B2 _ (Finset.mem_filter.mpr ⟨hxB', hDxy⟩))).1).2
  exact ⟨⟨φ, fun h => hφ_adj _ _ h⟩, hφ_inj⟩

-- ============================================================================

-- Graph-theoretic bridge: every oriented tree on n >= 6 vertices with n - k = 4 has Heart order h = 4!
lemma hasHeart4_of_internal_eq_four {n : ℕ} (hn6 : 6 ≤ n)
    {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    (hW : Fintype.card W = n) (hD : IsOrientedTree D)
    (hm4 : n - (Finset.univ.filter (fun w : W =>
      (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card = 4) :
    ∃ (u : Fin 4 → W), Function.Injective u ∧
      (∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j))) ∧
      ∃ A : Finset W, (∀ i : Fin 4, u i ∉ A) ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x) := by
  classical
  let L := Finset.univ.filter (fun w : W =>
    (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)
  let H : Finset W := Lᶜ
  have hH_card : H.card = 4 := by
    have h1 := Finset.card_add_card_compl L
    change L.card + H.card = Fintype.card W at h1
    rw [hW] at h1
    dsimp only [L] at h1
    omega
  obtain ⟨T, hT, hO⟩ := hD
  have hdeg_eq : ∀ w : W, (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card =
      (Finset.univ.filter (fun z : W => T.Adj w z)).card := fun w => by
    congr 1; ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.elim (hO.1 w z) (fun h' => (hO.1 z w h').symm), adj_or_rev_of_isOrientation hO⟩
  -- Every internal vertex of any path between two vertices of H lies in H (degree >= 2)!
  have hpath_in_H : ∀ x y : W, x ∈ H → y ∈ H → ∀ (p : T.Walk x y), p.IsPath → ∀ z ∈ p.support, z ∈ H := by
    intro x y hxH hyH p hp z hz
    by_cases hzx : z = x
    · exact hzx ▸ hxH
    · by_cases hzy : z = y
      · exact hzy ▸ hyH
      · -- z is strictly interior on p => takeUntil z and dropUntil z give two distinct neighbors of z!
        have hp1 := (hp.takeUntil hz)
        have hp2 := (hp.dropUntil hz)
        have hl1 : (p.takeUntil z hz).length ≠ 0 := fun h => hzx (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
        have hl2 : (p.dropUntil z hz).length ≠ 0 := fun h => hzy (SimpleGraph.Walk.eq_of_length_eq_zero h)
        let p1r := (p.takeUntil z hz).reverse
        have hp1r : p1r.IsPath := hp1.reverse
        have hl1r : p1r.length ≠ 0 := by simpa [p1r] using hl1
        cases h1 : p1r with
        | nil => exact absurd (by simp [h1]) hl1r
        | @cons _ w1 _ hzw1 q1 =>
          cases h2 : p.dropUntil z hz with
          | nil => exact absurd (by simp [h2]) hl2
          | @cons _ w2 _ hzw2 q2 =>
            have hw1_ne_w2 : w1 ≠ w2 := by
              intro heq; subst heq
              have hcat := SimpleGraph.Walk.take_spec p hz
              have hnd : p.support.Nodup := hp.support_nodup
              have hmem1 : w1 ∈ (p.takeUntil z hz).support := by
                have hrev : p1r.support = (p.takeUntil z hz).support.reverse := SimpleGraph.Walk.support_reverse _
                rw [h1] at hrev
                have hmem_rev : w1 ∈ (p.takeUntil z hz).support.reverse := by
                  rw [← hrev]; exact List.mem_cons_of_mem _ q1.start_mem_support
                exact List.mem_reverse.mp hmem_rev
              have hmem2 : w1 ∈ (p.dropUntil z hz).support.tail := by
                rw [h2]; simp only [SimpleGraph.Walk.support_cons, List.tail_cons]; exact q2.start_mem_support
              have hsup_eq : p.support = (p.takeUntil z hz).support ++ (p.dropUntil z hz).support.tail := by
                have h1' : ((p.takeUntil z hz).append (p.dropUntil z hz)).support = p.support :=
                  congrArg SimpleGraph.Walk.support hcat
                rw [← h1', SimpleGraph.Walk.support_append]
              rw [hsup_eq, List.nodup_append] at hnd
              exact hnd.2.2 w1 hmem1 w1 hmem2 rfl
            have hdeg2 : 2 ≤ (Finset.univ.filter (fun w : W => T.Adj z w)).card :=
              (Finset.card_pair hw1_ne_w2).symm.trans_le (Finset.card_le_card (fun w hw => by
                rcases Finset.mem_insert.mp hw with rfl | hw'
                · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzw1⟩
                · rw [Finset.mem_singleton.mp hw']; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzw2⟩))
            refine Finset.mem_compl.mpr (fun hzL => ?_)
            have h1' := (Finset.mem_filter.mp hzL).2; rw [hdeg_eq] at h1'; omega
  -- Step-growth helper: for any nonempty proper subset S ⊂ H, some w ∈ H \ S is T-adjacent to S!
  have hex_step : ∀ S : Finset W, S.Nonempty → S ⊆ H → (H \ S).Nonempty →
      ∃ w ∈ H \ S, ∃ s ∈ S, T.Adj s w := by
    intro S ⟨s0, hs0⟩ hSH ⟨t0, ht0⟩
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath s0 t0
    have hpH : ∀ z ∈ p.support, z ∈ H := hpath_in_H s0 t0 (hSH hs0) (Finset.mem_sdiff.mp ht0).1 p hp
    -- Induction on p: find first step leaving S
    have hwalk : ∀ (a b : W) (q : T.Walk a b), a ∈ S → b ∉ S → (∀ z ∈ q.support, z ∈ H) →
        ∃ w ∈ H \ S, ∃ s ∈ S, T.Adj s w := by
      intro a b q
      induction q with
      | nil => intro ha hnb _; exact absurd ha hnb
      | @cons a1 b1 c1 hab q' ih =>
        intro ha1 hnc1 hqH
        by_cases hb1S : b1 ∈ S
        · exact ih hb1S hnc1 (fun z hz => hqH z (List.mem_cons_of_mem a1 hz))
        · exact ⟨b1, Finset.mem_sdiff.mpr ⟨hqH b1 (List.mem_cons_of_mem a1 q'.start_mem_support), hb1S⟩, a1, ha1, hab⟩
    exact hwalk s0 t0 p hs0 (Finset.mem_sdiff.mp ht0).2 hpH
  -- Grow u0, u1, u2, u3 in H with parent property!
  obtain ⟨u0, hu0H⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  have hs1_ne : (H \ {u0}).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu0H), Finset.card_singleton, hH_card]; omega)
  obtain ⟨u1, hu1, s1, hs1, h01⟩ := hex_step {u0} (Finset.singleton_nonempty u0) (Finset.singleton_subset_iff.mpr hu0H) hs1_ne
  have hs1_eq : s1 = u0 := Finset.mem_singleton.mp hs1; subst s1
  have hu1H : u1 ∈ H := (Finset.mem_sdiff.mp hu1).1
  have hne01 : u0 ≠ u1 := fun h => (Finset.mem_sdiff.mp hu1).2 (Finset.mem_singleton.mpr h.symm)
  have hS2_sub : ({u0, u1} : Finset W) ⊆ H := Finset.insert_subset hu0H (Finset.singleton_subset_iff.mpr hu1H)
  have hs2_ne : (H \ {u0, u1}).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hS2_sub, Finset.card_pair hne01, hH_card]; omega)
  obtain ⟨u2, hu2, s2, hs2, hs2u2⟩ := hex_step {u0, u1} ⟨u0, Finset.mem_insert_self _ _⟩ hS2_sub hs2_ne
  have hu2H : u2 ∈ H := (Finset.mem_sdiff.mp hu2).1
  have hne02 : u0 ≠ u2 := fun h => (Finset.mem_sdiff.mp hu2).2 (by rw [← h]; exact Finset.mem_insert_self _ _)
  have hne12 : u1 ≠ u2 := fun h => (Finset.mem_sdiff.mp hu2).2 (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hS3_sub : ({u0, u1, u2} : Finset W) ⊆ H := Finset.insert_subset hu0H (Finset.insert_subset hu1H (Finset.singleton_subset_iff.mpr hu2H))
  have hS3_card : ({u0, u1, u2} : Finset W).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]), Finset.card_pair hne12]
  have hs3_ne : (H \ {u0, u1, u2}).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hS3_sub, hS3_card, hH_card]; omega)
  obtain ⟨u3, hu3, s3, hs3, hs3u3⟩ := hex_step {u0, u1, u2} ⟨u0, Finset.mem_insert_self _ _⟩ hS3_sub hs3_ne
  have hu3H : u3 ∈ H := (Finset.mem_sdiff.mp hu3).1
  have hne03 : u0 ≠ u3 := fun h => (Finset.mem_sdiff.mp hu3).2 (by rw [← h]; exact Finset.mem_insert_self _ _)
  have hne13 : u1 ≠ u3 := fun h => (Finset.mem_sdiff.mp hu3).2 (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hne23 : u2 ≠ u3 := fun h => (Finset.mem_sdiff.mp hu3).2 (by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  let u : Fin 4 → W := fun i => match i.val with | 0 => u0 | 1 => u1 | 2 => u2 | _ => u3
  have hu_inj : Function.Injective u := fun i j h => by
    fin_cases i <;> fin_cases j <;> dsimp only [u] at h <;>
      first | rfl | exact absurd h hne01 | exact absurd h hne02 | exact absurd h hne03 |
        exact absurd h hne01.symm | exact absurd h hne12 | exact absurd h hne13 |
        exact absurd h hne02.symm | exact absurd h hne12.symm | exact absurd h hne23 |
        exact absurd h hne03.symm | exact absurd h hne13.symm | exact absurd h hne23.symm
  have hH_eq : Finset.univ.image u = H := by
    refine Finset.eq_of_subset_of_card_le (fun w hw => ?_) (by rw [Finset.card_image_of_injective _ hu_inj, Finset.card_univ, Fintype.card_fin, hH_card])
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    fin_cases i <;> dsimp only [u] <;> assumption
  have hH_parent : ∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j)) := by
    intro i hi; fin_cases i
    · exact absurd rfl hi
    · exact ⟨⟨0, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO h01⟩
    · rcases Finset.mem_insert.mp hs2 with rfl | hs2'
      · exact ⟨⟨0, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO hs2u2⟩
      · rw [Finset.mem_singleton.mp hs2'] at hs2u2
        exact ⟨⟨1, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO hs2u2⟩
    · rcases Finset.mem_insert.mp hs3 with rfl | hs3'
      · exact ⟨⟨0, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO hs3u3⟩
      · rcases Finset.mem_insert.mp hs3' with rfl | hs3''
        · exact ⟨⟨1, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO hs3u3⟩
        · rw [Finset.mem_singleton.mp hs3''] at hs3u3
          exact ⟨⟨2, by decide⟩, by decide, by dsimp only [u]; exact adj_or_rev_of_isOrientation hO hs3u3⟩
  -- No two leaves are adjacent in a tree on n >= 6 >= 3 vertices!
  have hno_LL : ∀ x ∈ L, ∀ y ∈ L, ¬ T.Adj x y := by
    intro x hx y hy hTxy
    have hxy : x ≠ y := T.ne_of_adj hTxy
    have hdx : (Finset.univ.filter (fun z : W => T.Adj x z)).card = 1 := by rw [← hdeg_eq]; exact (Finset.mem_filter.mp hx).2
    have hdy : (Finset.univ.filter (fun z : W => T.Adj y z)).card = 1 := by rw [← hdeg_eq]; exact (Finset.mem_filter.mp hy).2
    have hx_eq : Finset.univ.filter (fun z : W => T.Adj x z) = {y} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy⟩, fun z hz => by
        obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hdx
        have e1 := Finset.mem_singleton.mp (hz0 ▸ hz)
        have e2 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy⟩)
        exact e1.trans e2.symm⟩
    have hy_eq : Finset.univ.filter (fun z : W => T.Adj y z) = {x} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy.symm⟩, fun z hz => by
        obtain ⟨z0, hz0⟩ := Finset.card_eq_one.mp hdy
        have e1 := Finset.mem_singleton.mp (hz0 ▸ hz)
        have e2 := Finset.mem_singleton.mp (hz0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTxy.symm⟩)
        exact e1.trans e2.symm⟩
    have hsub : (Finset.univ : Finset W) ⊆ {x, y} := by
      intro w _
      obtain ⟨p, hp⟩ := hT.connected.exists_isPath x w
      cases p with
      | nil => exact Finset.mem_insert_self _ _
      | @cons _ b _ hxb q =>
        have hb : b = y := Finset.mem_singleton.mp (hx_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb⟩)
        subst hb
        cases q with
        | nil => exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        | @cons _ c _ hyc q' =>
          have hc : c = x := Finset.mem_singleton.mp (hy_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyc⟩)
          subst hc
          have hnd := hp.support_nodup
          simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons] at hnd
          exact absurd (Or.inr q'.start_mem_support) hnd.1
    have hle2 : n ≤ 2 := by
      rw [← hW, ← Finset.card_univ]
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  let A : Finset W := L.filter (fun x => (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1)
  refine ⟨u, hu_inj, hH_parent, A, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have huH : u i ∈ H := hH_eq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact Finset.mem_compl.mp huH (Finset.mem_filter.mp hi).1
  · intro x hxA; exact (Finset.mem_filter.mp hxA).2
  · intro y hyu hyA
    have hyL : y ∈ L := by
      by_contra hnotL
      have hyH : y ∈ H := Finset.mem_compl.mpr hnotL
      rw [← hH_eq] at hyH; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hyH; exact hyu i hi.symm
    have hdy1 : (Finset.univ.filter (fun z : W => D.Adj y z ∨ D.Adj z y)).card = 1 := (Finset.mem_filter.mp hyL).2
    have hin0 : (Finset.univ.filter (fun z : W => D.Adj z y)).card = 0 := by
      have hle : (Finset.univ.filter (fun z : W => D.Adj z y)).card ≤ 1 :=
        (Finset.card_le_card (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hz).2⟩)).trans hdy1.le
      have hne1 : (Finset.univ.filter (fun z : W => D.Adj z y)).card ≠ 1 := fun h1 => hyA (Finset.mem_filter.mpr ⟨hyL, h1⟩)
      omega
    have heq : Finset.univ.filter (fun z : W => D.Adj y z) = Finset.univ.filter (fun z : W => D.Adj y z ∨ D.Adj z y) := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Or.inl, fun h => h.resolve_right (fun hzy => by
        have hpos : 0 < (Finset.univ.filter (fun z : W => D.Adj z y)).card :=
          Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy⟩⟩
        omega)⟩
    rw [heq, hdy1]
  · intro x hxA y hyu _
    have hyL : y ∈ L := by
      by_contra hnotL
      have hyH : y ∈ H := Finset.mem_compl.mpr hnotL
      rw [← hH_eq] at hyH; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hyH; exact hyu i hi.symm
    have hnotT := hno_LL x (Finset.mem_filter.mp hxA).1 y hyL
    exact ⟨fun h => hnotT (hO.1 _ _ h), fun h => hnotT (hO.1 _ _ h).symm⟩

end HeartFourShared

theorem main : H1 → H2 → H3 → OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1.H3 := by
  intro h1 h2 h3 n hn9 W _ _ D _ hW hTree _hNotH2 hk5 h3k_gt hInt4 V _ _ G _ hV hG h2S hNonNR
  have hNoSrc : ∀ v : V, ∃ u : V, G.Adj u v := by
    intro v
    have hne : (∅ ∪ ({v} : Finset V)) ≠ Finset.univ := by
      intro heq
      have hc := congrArg Finset.card heq
      rw [Finset.empty_union, Finset.card_singleton, Finset.card_univ, hV] at hc; omega
    obtain ⟨u, hu, x, _, _, hxu⟩ := h2S ∅ (by simp) {v} (Finset.disjoint_empty_left _) (Finset.singleton_nonempty v) hne
    rw [Finset.mem_singleton.mp hu] at hxu; exact ⟨x, hxu⟩
  have hNoSnk : ∀ v : V, ∃ u : V, G.Adj v u := by
    intro v
    have hV1_ne : (Finset.univ.erase v : Finset V).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro heq
      have hc := congrArg Finset.card heq
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV, Finset.card_empty] at hc; omega
    have hne : (∅ ∪ (Finset.univ.erase v : Finset V)) ≠ Finset.univ := by
      intro heq
      have hv : v ∈ (∅ ∪ (Finset.univ.erase v : Finset V)) := by rw [heq]; exact Finset.mem_univ v
      rw [Finset.empty_union] at hv; exact (Finset.mem_erase.mp hv).1 rfl
    obtain ⟨u, hu, x, _, hxnot, hxu⟩ := h2S ∅ (by simp) (Finset.univ.erase v) (Finset.disjoint_empty_left _) hV1_ne hne
    have hxv : x = v := by by_contra hne'; exact hxnot (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ x⟩)
    exact ⟨u, hxv ▸ hxu⟩
  by_cases hH3 : ∃ u1 u2 u3 : W, u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
      ((D.Adj u1 u2 ∧ D.Adj u2 u3) ∨ (D.Adj u1 u2 ∧ D.Adj u1 u3) ∨ (D.Adj u2 u1 ∧ D.Adj u3 u1)) ∧
      ∃ A : Finset W, u1 ∉ A ∧ u2 ∉ A ∧ u3 ∉ A ∧
        (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
        (∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A →
          (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
        (∀ x ∈ A, ∀ y : W, y ≠ u1 → y ≠ u2 → y ≠ u3 → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
  · exact embeds_heart_three (by omega) D hW hTree G hV hG hInt4 hH3
  · by_cases hH4 : ∃ (u : Fin 4 → W), Function.Injective u ∧
        (∀ i : Fin 4, i.val ≠ 0 → ∃ j : Fin 4, j.val < i.val ∧ (D.Adj (u j) (u i) ∨ D.Adj (u i) (u j))) ∧
        ∃ A : Finset W, (∀ i : Fin 4, u i ∉ A) ∧
          (∀ x ∈ A, (Finset.univ.filter (fun z : W => D.Adj z x)).card = 1) ∧
          (∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A →
            (Finset.univ.filter (fun z : W => D.Adj y z)).card = 1) ∧
          (∀ x ∈ A, ∀ y : W, (∀ i : Fin 4, y ≠ u i) → y ∉ A → ¬ D.Adj x y ∧ ¬ D.Adj y x)
    · exact h1 n hn9 D hW hTree hH3 hH4 G hV hG hNoSrc hNoSnk
    · have hInt5 : 5 ≤ n - (Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card := by
        by_contra hlt
        exact hH4 (hasHeart4_of_internal_eq_four (by omega) D hW hTree (by omega))
      have hn10 : 10 ≤ n := by omega
      by_cases h3k : 3 * (Finset.univ.filter (fun w : W =>
          (Finset.univ.filter (fun z : W => D.Adj w z ∨ D.Adj z w)).card = 1)).card ≤ n + 3
      · exact h2 n hn10 D hW hTree hH4 hk5 h3k_gt h3k hInt5 G hV hG
      · exact h3 n hn10 D hW hTree hH4 hk5 (by omega) hInt5 G hV hG h2S hNonNR

end OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_R1_H3_R1
