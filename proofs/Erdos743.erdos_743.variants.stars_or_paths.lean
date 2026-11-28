import FormalConjectures.ErdosProblems.«743»

/-!
# Proof of Erdős Problem 743 (stars or paths variant)

We formalize the Gyárfás–Lehel / Zaks–Liu packing of stars and paths of orders
`2, 3, ..., n` into the complete graph `K_n`.

The edge set of `K_n` on `Fin n` is split by endpoint sum into two disjoint triangular
regions:
- `u + v ≤ 2 * (n / 2) - 1`, which packs all even-order trees (odd edge counts `1, 3, ...`),
- `u + v ≥ 2 * (n / 2)` (the `Fin.rev`-image of `u + v ≤ 2 * ((n - 1) / 2)`), which packs
  all odd-order trees (even edge counts `2, 4, ...`).

Within a triangular region `EdgeInRegion s M` (edges `{u, v}` with `s ≤ u, v` and
`(u - s) + (v - s) ≤ M`), peeling the largest tree of size `M + 1`:
- if it is a star, places its center at `s` and recurses on `EdgeInRegion (s + 1) (M - 2)`;
- if it is a path, places it along the outer anti-diagonals `(u - s) + (v - s) ∈ {M - 1, M}`
  and recurses on `EdgeInRegion s (M - 2)`.
-/

namespace OMA_Erdos743_StarsOrPaths

open SimpleGraph

private def EdgeInRegion {n : ℕ} (s M : ℕ) (u v : Fin n) : Prop :=
  s ≤ u.val ∧ s ≤ v.val ∧ (u.val - s) + (v.val - s) ≤ M

private def StrideSet (M : ℕ) : Set ℕ :=
  { k : ℕ | 2 ≤ k ∧ k ≤ M + 1 ∧ k % 2 = (M + 1) % 2 }

private def starEmbed (n s M : ℕ) (hsM : s + M < n) (c : Fin (M + 1)) (x : Fin (M + 1)) : Fin n :=
  if x = c then ⟨s, by omega⟩
  else if hxc : x.val < c.val then ⟨s + x.val + 1, by omega⟩
  else ⟨s + x.val, by omega⟩

private lemma starEmbed_injective (n s M : ℕ) (hsM : s + M < n) (c : Fin (M + 1)) :
    Function.Injective (starEmbed n s M hsM c) := by
  intro x y h
  simp only [starEmbed] at h
  split_ifs at h with hx hy hxy hxc hyc
  · exact hx.trans hy.symm
  all_goals exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)

private lemma starEmbed_adj {n s M : ℕ} (hsM : s + M < n) (c : Fin (M + 1))
    {u v : Fin n} (h : ((starGraph c).map (starEmbed n s M hsM c)).Adj u v) :
    EdgeInRegion s M u v ∧ (u.val = s ∨ v.val = s) := by
  rcases h with ⟨huv, a, b, hab, rfl, rfl⟩
  have hab' : a ≠ b ∧ (a = c ∨ b = c) := by
    simpa [starGraph, SimpleGraph.fromRel_adj] using hab
  rcases hab' with ⟨hne, rfl | rfl⟩
  · simp only [starEmbed, ite_true, hne.symm, ite_false, EdgeInRegion]
    split_ifs <;> refine ⟨⟨by omega, by dsimp; omega, by dsimp; omega⟩, Or.inl trivial⟩
  · simp only [starEmbed, ite_true, hne, ite_false, EdgeInRegion]
    split_ifs <;> refine ⟨⟨by dsimp; omega, by omega, by dsimp; omega⟩, Or.inr trivial⟩

private def pathEmbed (n s M : ℕ) (hsM : s + M < n) (t : Fin (M + 1)) : Fin n :=
  if t.val % 2 = 0 then ⟨s + (M - t.val / 2), by omega⟩
  else ⟨s + t.val / 2, by omega⟩

private lemma pathEmbed_injective (n s M : ℕ) (hsM : s + M < n) :
    Function.Injective (pathEmbed n s M hsM) := by
  intro x y h
  simp only [pathEmbed] at h
  split_ifs at h <;> exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)

private lemma fin_covBy_iff {k : ℕ} {a b : Fin k} : a ⋖ b ↔ a.val + 1 = b.val := by
  constructor
  · rintro ⟨hab, hno⟩
    have hab' : a.val < b.val := hab
    by_contra hne
    have hlt : a.val + 1 < b.val := by omega
    exact hno (c := ⟨a.val + 1, by omega⟩) (show a.val < a.val + 1 by omega) hlt
  · intro h
    refine ⟨show a.val < b.val by omega, fun c hac hcb => ?_⟩
    have hac' : a.val < c.val := hac
    have hcb' : c.val < b.val := hcb
    omega

private lemma pathGraph_adj_iff {k : ℕ} {a b : Fin k} :
    (pathGraph k).Adj a b ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val := by
  simp only [pathGraph, SimpleGraph.hasse_adj, fin_covBy_iff]

private lemma pathEmbed_adj {n s M : ℕ} (hsM : s + M < n)
    {u v : Fin n} (h : ((pathGraph (M + 1)).map (pathEmbed n s M hsM)).Adj u v) :
    EdgeInRegion s M u v ∧ M - 1 ≤ (u.val - s) + (v.val - s) := by
  rcases h with ⟨huv, a, b, hab, rfl, rfl⟩
  rw [pathGraph_adj_iff] at hab
  rcases hab with h1 | h1 <;> simp only [pathEmbed, EdgeInRegion] <;> split_ifs <;>
    first | omega | exact ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩, by dsimp; omega⟩

private lemma disjoint_edgeSet_of_adj {V : Type*} {G₁ G₂ : SimpleGraph V}
    (h : ∀ u v : V, G₁.Adj u v → ¬ G₂.Adj u v) :
    Disjoint G₁.edgeSet G₂.edgeSet := by
  rw [Set.disjoint_left]
  intro e he1 he2
  induction e using Sym2.ind with
  | _ u v =>
    exact h u v he1 he2

private lemma map_iso_adj {V W U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (g : W → U) (u v : U) :
    (G.map (g ∘ e)).Adj u v ↔ (H.map g).Adj u v := by
  constructor
  · rintro ⟨huv, a, b, hab, rfl, rfl⟩
    exact ⟨huv, e a, e b, e.map_rel_iff.mpr hab, rfl, rfl⟩
  · rintro ⟨huv, a, b, hab, rfl, rfl⟩
    refine ⟨huv, e.symm a, e.symm b, e.symm.map_rel_iff.mpr hab, ?_, ?_⟩ <;> simp

private lemma packStride (n : ℕ) (T : (k : ℕ) → SimpleGraph (Fin k)) :
    ∀ M s : ℕ, s + M < n →
      (∀ k ∈ StrideSet M, (∃ c : Fin k, T k = starGraph c) ∨ Nonempty (T k ≃g pathGraph k)) →
      ∃ f : (k : StrideSet M) → Fin k → Fin n,
        (∀ k : StrideSet M, Function.Injective (f k)) ∧
        (∀ k : StrideSet M, ∀ u v : Fin n, ((T k).map (f k)).Adj u v → EdgeInRegion s M u v) ∧
        (∀ k l : StrideSet M, (k : ℕ) < (l : ℕ) →
          Disjoint ((T k).map (f k)).edgeSet ((T l).map (f l)).edgeSet) := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro s hsM hT
    by_cases hM0 : M = 0
    · subst hM0
      refine ⟨fun k => False.elim (by rcases k.2 with ⟨h1, h2, _⟩; omega), ?_, ?_, ?_⟩ <;>
        intro k <;> exfalso <;> rcases k.2 with ⟨h1, h2, _⟩ <;> omega
    · have hM1 : 1 ≤ M := by omega
      have htop_mem : M + 1 ∈ StrideSet M := ⟨by omega, le_refl _, rfl⟩
      have hsub : ∀ k ∈ StrideSet (M - 2), k ∈ StrideSet M := by
        intro k hk
        rcases hk with ⟨h1, h2, h3⟩
        refine ⟨h1, by omega, by omega⟩
      have hprev_mem : ∀ k : StrideSet M, (k : ℕ) ≠ M + 1 → (k : ℕ) ∈ StrideSet (M - 2) := by
        intro k hk
        rcases k.2 with ⟨h1, h2, h3⟩
        refine ⟨h1, by omega, by omega⟩
      rcases hT (M + 1) htop_mem with ⟨c, hstar⟩ | hiso
      · -- Top tree T (M + 1) is a star
        have hsM' : (s + 1) + (M - 2) < n := by omega
        obtain ⟨f', hf'_inj, hf'_reg, hf'_disj⟩ :=
          ih (M - 2) (by omega) (s + 1) hsM' (fun k hk => hT k (hsub k hk))
        let f : (k : StrideSet M) → Fin k → Fin n := fun k =>
          if hk : (k : ℕ) = M + 1 then
            fun x => starEmbed n s M hsM c (x.cast hk)
          else
            f' ⟨k.1, hprev_mem k hk⟩
        have hf_top : ∀ (k : StrideSet M) (hk : (k : ℕ) = M + 1) (u v : Fin n),
            ((T k).map (f k)).Adj u v → EdgeInRegion s M u v ∧ (u.val = s ∨ v.val = s) := by
          intro k hk u v hadj
          rcases k with ⟨kv, hkm⟩
          dsimp only at hk
          subst hk
          have hfk : f ⟨M + 1, hkm⟩ = starEmbed n s M hsM c := by
            funext x
            simp [f]
          rw [hfk, hstar] at hadj
          exact starEmbed_adj hsM c hadj
        have hf_rest : ∀ (k : StrideSet M) (hk : (k : ℕ) ≠ M + 1) (u v : Fin n),
            ((T k).map (f k)).Adj u v → EdgeInRegion (s + 1) (M - 2) u v := by
          intro k hk u v hadj
          have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by
            simp [f, hk]
          rw [hfk] at hadj
          exact hf'_reg ⟨k.1, hprev_mem k hk⟩ u v hadj
        refine ⟨f, ?_, ?_, ?_⟩
        · intro k
          by_cases hk : (k : ℕ) = M + 1
          · rcases k with ⟨kv, hkm⟩
            dsimp only at hk
            subst hk
            have hfk : f ⟨M + 1, hkm⟩ = starEmbed n s M hsM c := by
              funext x
              simp [f]
            rw [hfk]
            exact starEmbed_injective n s M hsM c
          · have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by simp [f, hk]
            rw [hfk]
            exact hf'_inj ⟨k.1, hprev_mem k hk⟩
        · intro k u v hadj
          by_cases hk : (k : ℕ) = M + 1
          · exact (hf_top k hk u v hadj).1
          · have hM2 : 2 ≤ M := by
              rcases hprev_mem k hk with ⟨h1, h2, _⟩
              omega
            have hreg := hf_rest k hk u v hadj
            rcases hreg with ⟨hu, hv, hsum⟩
            exact ⟨by omega, by omega, by omega⟩
        · intro k l hkl
          by_cases hl : (l : ℕ) = M + 1
          · have hk : (k : ℕ) ≠ M + 1 := by omega
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            have h1 := hf_rest k hk u v hadjk
            have h2 := (hf_top l hl u v hadjl).2
            rcases h1 with ⟨hu, hv, _⟩
            omega
          · have hk : (k : ℕ) ≠ M + 1 := by
              rcases l.2 with ⟨_, hl2, _⟩
              omega
            have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by simp [f, hk]
            have hfl : f l = f' ⟨l.1, hprev_mem l hl⟩ := by simp [f, hl]
            rw [hfk, hfl]
            exact hf'_disj ⟨k.1, hprev_mem k hk⟩ ⟨l.1, hprev_mem l hl⟩ hkl
      · -- Top tree T (M + 1) is a path
        obtain ⟨iso⟩ := hiso
        have hsM' : s + (M - 2) < n := by omega
        obtain ⟨f', hf'_inj, hf'_reg, hf'_disj⟩ :=
          ih (M - 2) (by omega) s hsM' (fun k hk => hT k (hsub k hk))
        let f : (k : StrideSet M) → Fin k → Fin n := fun k =>
          if hk : (k : ℕ) = M + 1 then
            fun x => pathEmbed n s M hsM (iso (x.cast hk))
          else
            f' ⟨k.1, hprev_mem k hk⟩
        have hf_top : ∀ (k : StrideSet M) (hk : (k : ℕ) = M + 1) (u v : Fin n),
            ((T k).map (f k)).Adj u v → EdgeInRegion s M u v ∧ M - 1 ≤ (u.val - s) + (v.val - s) := by
          intro k hk u v hadj
          rcases k with ⟨kv, hkm⟩
          dsimp only at hk
          subst hk
          have hfk : f ⟨M + 1, hkm⟩ = pathEmbed n s M hsM ∘ iso := by
            funext x
            simp [f]
          rw [hfk, map_iso_adj] at hadj
          exact pathEmbed_adj hsM hadj
        have hf_rest : ∀ (k : StrideSet M) (hk : (k : ℕ) ≠ M + 1) (u v : Fin n),
            ((T k).map (f k)).Adj u v → EdgeInRegion s (M - 2) u v := by
          intro k hk u v hadj
          have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by simp [f, hk]
          rw [hfk] at hadj
          exact hf'_reg ⟨k.1, hprev_mem k hk⟩ u v hadj
        refine ⟨f, ?_, ?_, ?_⟩
        · intro k
          by_cases hk : (k : ℕ) = M + 1
          · rcases k with ⟨kv, hkm⟩
            dsimp only at hk
            subst hk
            have hfk : f ⟨M + 1, hkm⟩ = pathEmbed n s M hsM ∘ iso := by
              funext x
              simp [f]
            rw [hfk]
            exact (pathEmbed_injective n s M hsM).comp iso.injective
          · have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by simp [f, hk]
            rw [hfk]
            exact hf'_inj ⟨k.1, hprev_mem k hk⟩
        · intro k u v hadj
          by_cases hk : (k : ℕ) = M + 1
          · exact (hf_top k hk u v hadj).1
          · have hreg := hf_rest k hk u v hadj
            rcases hreg with ⟨hu, hv, hsum⟩
            exact ⟨hu, hv, by omega⟩
        · intro k l hkl
          by_cases hl : (l : ℕ) = M + 1
          · have hk : (k : ℕ) ≠ M + 1 := by omega
            have hM2 : 2 ≤ M := by
              have hkm := hprev_mem k hk
              rcases hkm with ⟨h1, h2, _⟩
              omega
            apply disjoint_edgeSet_of_adj
            intro u v hadjk hadjl
            have h1 := hf_rest k hk u v hadjk
            have h2 := (hf_top l hl u v hadjl).2
            rcases h1 with ⟨_, _, hsum⟩
            omega
          · have hk : (k : ℕ) ≠ M + 1 := by
              rcases l.2 with ⟨_, hl2, _⟩
              omega
            have hfk : f k = f' ⟨k.1, hprev_mem k hk⟩ := by simp [f, hk]
            have hfl : f l = f' ⟨l.1, hprev_mem l hl⟩ := by simp [f, hl]
            rw [hfk, hfl]
            exact hf'_disj ⟨k.1, hprev_mem k hk⟩ ⟨l.1, hprev_mem l hl⟩ hkl

private lemma map_comp_adj {V W U : Type*} {G : SimpleGraph V} {f : V → W} {g : W → U}
    (hg : Function.Injective g) (u v : U) :
    (G.map (g ∘ f)).Adj u v ↔ ∃ u' v', (G.map f).Adj u' v' ∧ g u' = u ∧ g v' = v := by
  constructor
  · rintro ⟨huv, a, b, hab, rfl, rfl⟩
    refine ⟨f a, f b, ⟨fun h => huv (congrArg g h), a, b, hab, rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨u', v', ⟨huv', a, b, hab, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨fun h => huv' (hg h), a, b, hab, rfl, rfl⟩

end OMA_Erdos743_StarsOrPaths

theorem OMA.solution : type_of% @Erdos743.erdos_743.variants.stars_or_paths := by
  intro n T hT
  by_cases hn : n < 2
  · refine ⟨fun k => False.elim (by rcases k.2 with ⟨h1, h2⟩; omega), ?_, ?_⟩ <;>
      intro k <;> exfalso <;> rcases k.2 with ⟨h1, h2⟩ <;> omega
  · have hn : 2 ≤ n := Nat.le_of_not_lt hn
    let Meven := 2 * (n / 2) - 1
    let Modd := 2 * ((n - 1) / 2)
    have hMeven : 0 + Meven < n := by omega
    have hModd : 0 + Modd < n := by omega
    have hTeven : ∀ k ∈ OMA_Erdos743_StarsOrPaths.StrideSet Meven,
        (∃ c : Fin k, T k = SimpleGraph.starGraph c) ∨ Nonempty (T k ≃g SimpleGraph.pathGraph k) := by
      intro k hk
      rcases hk with ⟨h1, h2, _⟩
      exact (hT k ⟨h1, by omega⟩).2
    have hTodd : ∀ k ∈ OMA_Erdos743_StarsOrPaths.StrideSet Modd,
        (∃ c : Fin k, T k = SimpleGraph.starGraph c) ∨ Nonempty (T k ≃g SimpleGraph.pathGraph k) := by
      intro k hk
      rcases hk with ⟨h1, h2, _⟩
      exact (hT k ⟨h1, by omega⟩).2
    obtain ⟨fe, hfe_inj, hfe_reg, hfe_disj⟩ :=
      OMA_Erdos743_StarsOrPaths.packStride n T Meven 0 hMeven hTeven
    obtain ⟨fo, hfo_inj, hfo_reg, hfo_disj⟩ :=
      OMA_Erdos743_StarsOrPaths.packStride n T Modd 0 hModd hTodd
    have hmem_even : ∀ k : Set.Icc 2 n, (k : ℕ) % 2 = 0 →
        (k : ℕ) ∈ OMA_Erdos743_StarsOrPaths.StrideSet Meven := by
      intro k hk
      rcases k.2 with ⟨h1, h2⟩
      exact ⟨h1, by omega, by omega⟩
    have hmem_odd : ∀ k : Set.Icc 2 n, (k : ℕ) % 2 ≠ 0 →
        (k : ℕ) ∈ OMA_Erdos743_StarsOrPaths.StrideSet Modd := by
      intro k hk
      rcases k.2 with ⟨h1, h2⟩
      exact ⟨h1, by omega, by omega⟩
    let f : (k : Set.Icc 2 n) → Fin k → Fin n := fun k =>
      if hk : (k : ℕ) % 2 = 0 then
        fe ⟨k.1, hmem_even k hk⟩
      else
        Fin.rev ∘ fo ⟨k.1, hmem_odd k hk⟩
    refine ⟨f, ?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) % 2 = 0
      · simp only [f, hk, dif_pos]
        exact hfe_inj ⟨k.1, hmem_even k hk⟩
      · simp only [f, hk, dif_neg, not_false_eq_true]
        exact Fin.rev_injective.comp (hfo_inj ⟨k.1, hmem_odd k hk⟩)
    · intro k l hkl
      by_cases hk : (k : ℕ) % 2 = 0 <;> by_cases hl : (l : ℕ) % 2 = 0
      · simp only [f, hk, hl, dif_pos]
        exact hfe_disj ⟨k.1, hmem_even k hk⟩ ⟨l.1, hmem_even l hl⟩ hkl
      · simp only [f, hk, hl, dif_pos, dif_neg, not_false_eq_true]
        apply OMA_Erdos743_StarsOrPaths.disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        have h1 := hfe_reg ⟨k.1, hmem_even k hk⟩ u v hadjk
        rw [OMA_Erdos743_StarsOrPaths.map_comp_adj Fin.rev_injective] at hadjl
        rcases hadjl with ⟨u', v', hadj', rfl, rfl⟩
        have h2 := hfo_reg ⟨l.1, hmem_odd l hl⟩ u' v' hadj'
        rcases h1 with ⟨_, _, hsum1⟩
        rcases h2 with ⟨_, _, hsum2⟩
        simp only [Fin.val_rev] at hsum1
        omega
      · simp only [f, hk, hl, dif_pos, dif_neg, not_false_eq_true]
        apply OMA_Erdos743_StarsOrPaths.disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        have h1 := hfe_reg ⟨l.1, hmem_even l hl⟩ u v hadjl
        rw [OMA_Erdos743_StarsOrPaths.map_comp_adj Fin.rev_injective] at hadjk
        rcases hadjk with ⟨u', v', hadj', rfl, rfl⟩
        have h2 := hfo_reg ⟨k.1, hmem_odd k hk⟩ u' v' hadj'
        rcases h1 with ⟨_, _, hsum1⟩
        rcases h2 with ⟨_, _, hsum2⟩
        simp only [Fin.val_rev] at hsum1
        omega
      · simp only [f, hk, hl, dif_neg, not_false_eq_true]
        apply OMA_Erdos743_StarsOrPaths.disjoint_edgeSet_of_adj
        intro u v hadjk hadjl
        rw [OMA_Erdos743_StarsOrPaths.map_comp_adj Fin.rev_injective] at hadjk hadjl
        rcases hadjk with ⟨u₁, v₁, h1, hu1, hv1⟩
        rcases hadjl with ⟨u₂, v₂, h2, hu2, hv2⟩
        have hu : u₁ = u₂ := Fin.rev_injective (hu1.trans hu2.symm)
        have hv : v₁ = v₂ := Fin.rev_injective (hv1.trans hv2.symm)
        subst hu; subst hv
        have hdisj := hfo_disj ⟨k.1, hmem_odd k hk⟩ ⟨l.1, hmem_odd l hl⟩ hkl
        exact Set.disjoint_left.mp hdisj (show s(u₁, v₁) ∈ _ from h1) (show s(u₁, v₁) ∈ _ from h2)
