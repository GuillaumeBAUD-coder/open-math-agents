import OMAReductions.R_Erdos147_erdos_147_variants_janzer_conjecture_R2

/-!
# Proof of `Erdos147.erdos_147.variants.janzer_conjecture.R2.H1`

We prove Oliver Janzer's theorem (IMRN 2023, arXiv:2109.06110): for every `ε > 0`, there exists a
3-regular graph `H` on `q > 0` vertices with `ex(n, H) = O(n^(4/3 + ε))`.

Proof outline:
1. **Janzer's 3-regular graph `janzerGraph k ℓ`** on `Fin (4 * k) × Fin (2 * ℓ)`:
   Every vertex `(i, j)` has 3 distinct neighbors `(pairMate i, j)`, `(crossMate i, j + 1)`, and
   `(crossMate i, j - 1)`. Two layers `y, z : Fin (4 * k) → V` whose `interleave y z` (or
   `interleave z y`) forms an `8k`-cycle in `G` supply all edges between layers `y` and `z`.
2. **`β`-good → `β`-nice → `janzerGraph k ℓ ⊑ G`**:
   Iterated deletion of sparse `(8k - 2)`-fibers extracts a nonempty `β`-nice subset from any
   nonempty `β`-good collection of `8k`-cycles. Applying `conflict_free_cycle_of_ratio` from
   `OMAReductions.R_Erdos147_erdos_147_variants_janzer_conjecture_R2` to the auxiliary graph on
   `4k`-tuples yields a copy of `janzerGraph k ℓ`.
3. **Deterministic regularization & `C_4`-balanced spanning subgraph**:
   Taking a minimum-order induced subgraph with `e(H) ≥ C |V(H)|^(1 + α)` and discarding vertices
   of degree `> K d` yields an arbitrarily large subgraph with average degree `d ≥ m^(1/3 + ε)`
   and maximum degree `≤ 2 K d`. Repeatedly deleting edges belonging to an oversized fraction of
   ordered 4-cycles gives a spanning subgraph `F` with `e(F) ≥ e/2` and uniform `C_4`-load.
4. **Elementary matrix/walk bounds**:
   Using Cauchy–Schwarz and the trace log-convexity/prefix-walk machinery exported by
   `OMAReductions.R_Erdos147_erdos_147_variants_janzer_conjecture_R2`, we prove Sidorenko's lower
   bound for even cycles, the bipartite lower bound `hom(C_{2r}, G) ≥ s^r t^r`, the vertex-conflict
   upper bound, and the high-codegree two-step upper bound.
5. **Few `C_4`s vs. Many `C_4`s**:
   - Few `C_4`s: direct removal of vertex-repeating and high-codegree `8k`-cycles yields an
     `m^(-ε/2)`-good family of `8k`-cycles.
   - Many `C_4`s: dyadic bucketing around a heavy center `v` produces a symmetric triple family
     `𝒟 ⊆ N(v) × V × N(v)`; bipartite dyadic regularization + conflict-free cycle counting on the
     auxiliary graph on `N(v)` produces an `m^(-ε/2)`-good family of `8k`-cycles.
-/

-- Credit: @skhakim

namespace OMA.P_Erdos147_erdos_147_variants_janzer_conjecture_R2_H1

open Filter Asymptotics SimpleGraph Finset
open OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2
open scoped BigOperators Classical

/- ### Section 1: Janzer's 3-regular graph `H_{k, ℓ}` and `8k`-cycle interleaving -/

private lemma fin_val_one_of_gt {m : ℕ} [NeZero m] (h : 1 < m) : (1 : Fin m).val = 1 := by
  change 1 % m = 1
  exact Nat.mod_eq_of_lt h

private lemma fin_val_ofNat {m : ℕ} [NeZero m] (a : ℕ) : (Fin.ofNat m a).val = a % m := rfl

private lemma fin_ofNat_add {m : ℕ} [NeZero m] (a b : ℕ) :
    Fin.ofNat m (a + b) = Fin.ofNat m a + Fin.ofNat m b := by
  ext
  change (a + b) % m = (a % m + b % m) % m
  exact Nat.add_mod a b m

private def pairMate {k : ℕ} (i : Fin (4 * k)) : Fin (4 * k) :=
  if h : i.1 % 2 = 0 then ⟨i.1 + 1, by omega⟩ else ⟨i.1 - 1, by omega⟩

private lemma pairMate_involutive {k : ℕ} (i : Fin (4 * k)) : pairMate (pairMate i) = i := by
  ext
  unfold pairMate
  by_cases h : i.1 % 2 = 0
  · have h1 : (i.1 + 1) % 2 ≠ 0 := by omega
    simp only [dif_pos h, dif_neg h1]; omega
  · have h1 : (i.1 - 1) % 2 = 0 := by omega
    simp only [dif_neg h, dif_pos h1]; omega

private lemma pairMate_ne {k : ℕ} (i : Fin (4 * k)) : pairMate i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold pairMate at hv
  by_cases h0 : i.1 % 2 = 0
  · simp only [dif_pos h0] at hv; omega
  · simp only [dif_neg h0] at hv; omega

private def crossMate {k : ℕ} (i : Fin (4 * k)) : Fin (4 * k) :=
  if h0 : i.1 = 0 then i
  else if h1 : i.1 = 4 * k - 1 then i
  else if h2 : i.1 % 2 = 1 then ⟨i.1 + 1, by omega⟩
  else ⟨i.1 - 1, by omega⟩

private lemma crossMate_involutive {k : ℕ} (i : Fin (4 * k)) : crossMate (crossMate i) = i := by
  ext
  unfold crossMate
  by_cases h0 : i.1 = 0
  · simp only [dif_pos h0]
  · by_cases h1 : i.1 = 4 * k - 1
    · simp only [dif_neg h0, dif_pos h1]
    · by_cases h2 : i.1 % 2 = 1
      · have ha : i.1 + 1 ≠ 0 := by omega
        have hb : i.1 + 1 ≠ 4 * k - 1 := by omega
        have hc : (i.1 + 1) % 2 ≠ 1 := by omega
        simp only [dif_neg h0, dif_neg h1, dif_pos h2, dif_neg ha, dif_neg hb, dif_neg hc]; omega
      · have ha : i.1 - 1 ≠ 0 := by omega
        have hb : i.1 - 1 ≠ 4 * k - 1 := by omega
        have hc : (i.1 - 1) % 2 = 1 := by omega
        simp only [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg ha, dif_neg hb, dif_pos hc]; omega

/-- Janzer's 3-regular graph `H_{k, ℓ}` on `Fin (4 * k) × Fin (2 * ℓ)`. -/
private def janzerGraph (k ℓ : ℕ) [NeZero ℓ] (_hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) :
    SimpleGraph (Fin (4 * k) × Fin (2 * ℓ)) where
  Adj u v :=
    (u.2 = v.2 ∧ v.1 = pairMate u.1) ∨
    ((v.2 = u.2 + 1 ∨ u.2 = v.2 + 1) ∧ v.1 = crossMate u.1)
  symm := ⟨by
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ (⟨hj, hi⟩ | ⟨hj, hi⟩)
    · exact Or.inl ⟨hj.symm, by rw [hi, pairMate_involutive]⟩
    · exact Or.inr ⟨hj.symm, by rw [hi, crossMate_involutive]⟩⟩
  loopless := ⟨by
    rintro ⟨i, j⟩ (⟨_, hi⟩ | ⟨hj, _⟩)
    · exact pairMate_ne i hi.symm
    · rcases hj with h | h
      · have h1 : (1 : Fin (2 * ℓ)) = 0 := by
          have := congrArg (· - j) h
          simpa using this.symm
        have hv := congrArg Fin.val h1
        rw [fin_val_one_of_gt (by omega : 1 < 2 * ℓ), Fin.val_zero] at hv
        omega
      · have h1 : (1 : Fin (2 * ℓ)) = 0 := by
          have := congrArg (· - j) h
          simpa using this.symm
        have hv := congrArg Fin.val h1
        rw [fin_val_one_of_gt (by omega : 1 < 2 * ℓ), Fin.val_zero] at hv
        omega⟩

private lemma fin_three_distinct {m : ℕ} [NeZero m] (hm : 4 ≤ m) (j : Fin m) :
    j ≠ j + 1 ∧ j ≠ j - 1 ∧ j + 1 ≠ j - 1 := by
  have h10 : (1 : Fin m) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [fin_val_one_of_gt (by omega : 1 < m), Fin.val_zero] at hv
    omega
  have h20 : (2 : Fin m) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    have h2 : (2 : Fin m).val = 2 := by change 2 % m = 2; exact Nat.mod_eq_of_lt (by omega)
    rw [h2, Fin.val_zero] at hv
    omega
  refine ⟨fun h => h10 (by have := congrArg (· - j) h; simpa using this.symm),
    fun h => h10 (by have := congrArg (j - ·) h; simpa using this.symm),
    fun h => h20 (by
      have := congrArg (· - (j - 1)) h
      have hl : j + 1 - (j - 1) = (2 : Fin m) := by
        calc j + 1 - (j - 1) = (1 : Fin m) + 1 := by abel
          _ = (2 : Fin m) := by
            ext
            rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < m)]
            rfl
      simpa [hl] using this)⟩

private lemma janzerGraph_isRegular (k ℓ : ℕ) [NeZero ℓ] (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) :
    (janzerGraph k ℓ hk hℓ).IsRegularOfDegree 3 := by
  intro v
  rcases v with ⟨i, j⟩
  have hdist := fin_three_distinct (by omega : 4 ≤ 2 * ℓ) j
  have hnf : (janzerGraph k ℓ hk hℓ).neighborFinset (i, j) =
      {(pairMate i, j), (crossMate i, j + 1), (crossMate i, j - 1)} := by
    ext ⟨i', j'⟩
    rw [mem_neighborFinset]
    simp only [janzerGraph, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro (⟨hj, hi⟩ | ⟨hj | hj, hi⟩)
      · exact Or.inl ⟨hi, hj.symm⟩
      · exact Or.inr (Or.inl ⟨hi, hj⟩)
      · exact Or.inr (Or.inr ⟨hi, by rw [hj]; abel⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl rfl, rfl⟩
      · exact Or.inr ⟨Or.inr (by abel), rfl⟩
  rw [← card_neighborFinset_eq_degree, hnf]
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [hdist.2.2]
  · simp [hdist.1, hdist.2.1]

/-- Interleave two `4k`-tuples `y, z` into an `8k`-tuple tracing the `8k`-cycle between them. -/
private def interleave {V : Type} {k : ℕ} (y z : Fin (4 * k) → V) (t : Fin (8 * k)) : V :=
  if h : t.1 < 4 * k then
    let idx : Fin (4 * k) := ⟨t.1, h⟩
    if (t.1 / 2) % 2 = 0 then y idx else z idx
  else
    let idx : Fin (4 * k) := ⟨8 * k - 1 - t.1, by omega⟩
    if (idx.1 / 2) % 2 = 0 then z idx else y idx

/-- Position of `y i` inside `interleave y z`. -/
private def yPos {k : ℕ} (i : Fin (4 * k)) : Fin (8 * k) :=
  if (i.1 / 2) % 2 = 0 then ⟨i.1, by omega⟩ else ⟨8 * k - 1 - i.1, by omega⟩

/-- Position of `z i` inside `interleave y z`. -/
private def zPos {k : ℕ} (i : Fin (4 * k)) : Fin (8 * k) :=
  if (i.1 / 2) % 2 = 1 then ⟨i.1, by omega⟩ else ⟨8 * k - 1 - i.1, by omega⟩

private lemma interleave_yPos {V : Type} {k : ℕ} (y z : Fin (4 * k) → V) (i : Fin (4 * k)) :
    interleave y z (yPos i) = y i := by
  unfold interleave yPos
  by_cases h : (i.1 / 2) % 2 = 0
  · simp only [if_pos h, dif_pos i.2, Fin.eta]
  · have hge : ¬ (8 * k - 1 - i.1 < 4 * k) := by omega
    have hsub : 8 * k - 1 - (8 * k - 1 - i.1) = i.1 := by omega
    simp only [if_neg h, dif_neg hge]
    simp only [hsub, if_neg h, Fin.eta]

private lemma interleave_zPos {V : Type} {k : ℕ} (y z : Fin (4 * k) → V) (i : Fin (4 * k)) :
    interleave y z (zPos i) = z i := by
  unfold interleave zPos
  by_cases h : (i.1 / 2) % 2 = 1
  · have h0 : (i.1 / 2) % 2 ≠ 0 := by omega
    simp only [if_pos h, dif_pos i.2, if_neg h0, Fin.eta]
  · have h0 : (i.1 / 2) % 2 = 0 := by omega
    have hge : ¬ (8 * k - 1 - i.1 < 4 * k) := by omega
    have hsub : 8 * k - 1 - (8 * k - 1 - i.1) = i.1 := by omega
    simp only [if_neg h, dif_neg hge]
    simp only [hsub, if_pos h0, Fin.eta]

private lemma yPos_injective {k : ℕ} : Function.Injective (@yPos k) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold yPos at hv
  ext
  by_cases ha : (a.1 / 2) % 2 = 0 <;> by_cases hb : (b.1 / 2) % 2 = 0
  · simp only [if_pos ha, if_pos hb] at hv; exact hv
  · simp only [if_pos ha, if_neg hb] at hv; omega
  · simp only [if_neg ha, if_pos hb] at hv; omega
  · simp only [if_neg ha, if_neg hb] at hv; omega

private lemma zPos_injective {k : ℕ} : Function.Injective (@zPos k) := by
  intro a b h
  have hv := congrArg Fin.val h
  unfold zPos at hv
  ext
  by_cases ha : (a.1 / 2) % 2 = 1 <;> by_cases hb : (b.1 / 2) % 2 = 1
  · simp only [if_pos ha, if_pos hb] at hv; exact hv
  · simp only [if_pos ha, if_neg hb] at hv; omega
  · simp only [if_neg ha, if_pos hb] at hv; omega
  · simp only [if_neg ha, if_neg hb] at hv; omega

private lemma yPos_ne_zPos {k : ℕ} (a b : Fin (4 * k)) : yPos a ≠ zPos b := by
  intro h
  have hv := congrArg Fin.val h
  unfold yPos zPos at hv
  by_cases ha : (a.1 / 2) % 2 = 0 <;> by_cases hb : (b.1 / 2) % 2 = 1
  · simp only [if_pos ha, if_pos hb] at hv; omega
  · simp only [if_pos ha, if_neg hb] at hv; omega
  · simp only [if_neg ha, if_pos hb] at hv; omega
  · simp only [if_neg ha, if_neg hb] at hv; omega

private lemma interleave_inj_of_y {V : Type} {k : ℕ} {y z₁ z₂ : Fin (4 * k) → V}
    (h : interleave y z₁ = interleave y z₂) : z₁ = z₂ := by
  funext i
  have := congrFun h (zPos i)
  rwa [interleave_zPos, interleave_zPos] at this

private lemma interleave_inj_of_z {V : Type} {k : ℕ} {y₁ y₂ z : Fin (4 * k) → V}
    (h : interleave y₁ z = interleave y₂ z) : y₁ = y₂ := by
  funext i
  have := congrFun h (yPos i)
  rwa [interleave_yPos, interleave_yPos] at this

/-- If `interleave y z` is a homomorphic `8k`-cycle in `G`, then all within-layer and cross-layer
edges of `janzerGraph` hold between `y` and `z`. -/
private lemma interleave_edges {V : Type} {k : ℕ} [NeZero k] (hk : 1 ≤ k) (G : SimpleGraph V)
    {y z : Fin (4 * k) → V}
    (hcyc : ∀ t : Fin (8 * k), G.Adj (interleave y z t) (interleave y z (t + 1))) :
    (∀ i : Fin (4 * k), G.Adj (y i) (y (pairMate i))) ∧
    (∀ i : Fin (4 * k), G.Adj (z i) (z (pairMate i))) ∧
    (∀ i : Fin (4 * k), G.Adj (y i) (z (crossMate i))) := by
  have hadj_val : ∀ a b : Fin (8 * k), (b.1 = (a.1 + 1) % (8 * k) ∨ a.1 = (b.1 + 1) % (8 * k)) →
      G.Adj (interleave y z a) (interleave y z b) := by
    intro a b hab
    rcases hab with hb | ha
    · have hba : b = a + 1 := by
        ext
        rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]
        exact hb
      rw [hba]; exact hcyc a
    · have hab' : a = b + 1 := by
        ext
        rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]
        exact ha
      rw [hab']; exact (hcyc b).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← interleave_yPos y z i, ← interleave_yPos y z (pairMate i)]
    apply hadj_val
    unfold yPos pairMate
    by_cases h1 : i.1 % 2 = 0
    · have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by omega
      by_cases h2 : (i.1 / 2) % 2 = 0
      · left; simp only [dif_pos h1, if_pos h2, hdiv]; exact (Nat.mod_eq_of_lt (by omega)).symm
      · right; simp only [dif_pos h1, if_neg h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have hdiv : (i.1 - 1) / 2 = i.1 / 2 := by omega
      by_cases h2 : (i.1 / 2) % 2 = 0
      · right; simp only [dif_neg h1, if_pos h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · left; simp only [dif_neg h1, if_neg h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro i
    rw [← interleave_zPos y z i, ← interleave_zPos y z (pairMate i)]
    apply hadj_val
    unfold zPos pairMate
    by_cases h1 : i.1 % 2 = 0
    · have hdiv : (i.1 + 1) / 2 = i.1 / 2 := by omega
      by_cases h2 : (i.1 / 2) % 2 = 1
      · left; simp only [dif_pos h1, if_pos h2, hdiv]; exact (Nat.mod_eq_of_lt (by omega)).symm
      · right; simp only [dif_pos h1, if_neg h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have hdiv : (i.1 - 1) / 2 = i.1 / 2 := by omega
      by_cases h2 : (i.1 / 2) % 2 = 1
      · right; simp only [dif_neg h1, if_pos h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · left; simp only [dif_neg h1, if_neg h2, hdiv]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro i
    rw [← interleave_yPos y z i, ← interleave_zPos y z (crossMate i)]
    apply hadj_val
    unfold yPos zPos crossMate
    by_cases h0 : i.1 = 0
    · right
      simp only [dif_pos h0]
      simp only [h0, Nat.zero_div, Nat.zero_mod, ↓reduceIte, zero_ne_one, Fin.val_mk]
      have h8k : (8 * k - 1 - 0 + 1) % (8 * k) = 0 := by
        have : 8 * k - 1 - 0 + 1 = 8 * k := by omega
        rw [this, Nat.mod_self]
      exact h8k.symm
    · by_cases h1 : i.1 = 4 * k - 1
      · right
        have hodd : ((4 * k - 1) / 2) % 2 = 1 := by omega
        have hne0 : ((4 * k - 1) / 2) % 2 ≠ 0 := by omega
        simp only [dif_neg h0, dif_pos h1]
        simp only [h1, if_neg hne0, if_pos hodd, Fin.val_mk]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · by_cases h2 : i.1 % 2 = 1
        · by_cases h3 : (i.1 / 2) % 2 = 0
          · left
            have h4 : ((i.1 + 1) / 2) % 2 = 1 := by omega
            simp only [dif_neg h0, dif_neg h1, dif_pos h2, if_pos h3, if_pos h4]
            exact (Nat.mod_eq_of_lt (by omega)).symm
          · right
            have h4 : ((i.1 + 1) / 2) % 2 ≠ 1 := by omega
            simp only [dif_neg h0, dif_neg h1, dif_pos h2, if_neg h3, if_neg h4]
            rw [Nat.mod_eq_of_lt (by omega)]; omega
        · by_cases h3 : (i.1 / 2) % 2 = 0
          · right
            have h4 : ((i.1 - 1) / 2) % 2 = 1 := by omega
            simp only [dif_neg h0, dif_neg h1, dif_neg h2, if_pos h3, if_pos h4]
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          · left
            have h4 : ((i.1 - 1) / 2) % 2 ≠ 1 := by omega
            simp only [dif_neg h0, dif_neg h1, dif_neg h2, if_neg h3, if_neg h4]
            rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- For each pair `r : Fin (2 * k)`, the two positions `{zPos (2r), zPos (2r + 1)}` are
consecutive in `Fin (8 * k)` (namely `{pos + 1, pos + 2}` for some `pos : Fin (8 * k)`). -/
private lemma zPos_pair_consecutive {k : ℕ} [NeZero k] (hk : 1 ≤ k) (r : Fin (2 * k)) :
    ∃ p : Fin (8 * k),
      ({zPos ⟨2 * r.1, by omega⟩, zPos ⟨2 * r.1 + 1, by omega⟩} : Set (Fin (8 * k))) =
        {p + 1, p + 2} := by
  have h2v : (2 : Fin (8 * k)).val = 2 := by change 2 % (8 * k) = 2; exact Nat.mod_eq_of_lt (by omega)
  by_cases hr : r.1 % 2 = 1
  · refine ⟨⟨2 * r.1 - 1, by omega⟩, ?_⟩
    have h1 : zPos (k := k) ⟨2 * r.1, by omega⟩ = (⟨2 * r.1 - 1, by omega⟩ : Fin (8 * k)) + 1 := by
      unfold zPos
      have hdiv : (2 * r.1 / 2) % 2 = 1 := by omega
      simp only [if_pos hdiv]
      ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have h2 : zPos (k := k) ⟨2 * r.1 + 1, by omega⟩ = (⟨2 * r.1 - 1, by omega⟩ : Fin (8 * k)) + 2 := by
      unfold zPos
      have hdiv : ((2 * r.1 + 1) / 2) % 2 = 1 := by omega
      simp only [if_pos hdiv]
      ext; rw [Fin.val_add, h2v]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2]
  · refine ⟨⟨8 * k - 3 - 2 * r.1, by omega⟩, ?_⟩
    have h1 : zPos (k := k) ⟨2 * r.1 + 1, by omega⟩ = (⟨8 * k - 3 - 2 * r.1, by omega⟩ : Fin (8 * k)) + 1 := by
      unfold zPos
      have hdiv : ((2 * r.1 + 1) / 2) % 2 ≠ 1 := by omega
      simp only [if_neg hdiv]
      ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have h2 : zPos (k := k) ⟨2 * r.1, by omega⟩ = (⟨8 * k - 3 - 2 * r.1, by omega⟩ : Fin (8 * k)) + 2 := by
      unfold zPos
      have hdiv : (2 * r.1 / 2) % 2 ≠ 1 := by omega
      simp only [if_neg hdiv]
      ext; rw [Fin.val_add, h2v]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2, Set.pair_comm]

private lemma yPos_pair_consecutive {k : ℕ} [NeZero k] (hk : 1 ≤ k) (r : Fin (2 * k)) :
    ∃ p : Fin (8 * k),
      ({yPos ⟨2 * r.1, by omega⟩, yPos ⟨2 * r.1 + 1, by omega⟩} : Set (Fin (8 * k))) =
        {p + 1, p + 2} := by
  have h2v : (2 : Fin (8 * k)).val = 2 := by change 2 % (8 * k) = 2; exact Nat.mod_eq_of_lt (by omega)
  by_cases hr : r.1 % 2 = 0
  · let p : Fin (8 * k) := if h0 : r.1 = 0 then ⟨8 * k - 1, by omega⟩ else ⟨2 * r.1 - 1, by omega⟩
    refine ⟨p, ?_⟩
    have h1 : yPos (k := k) ⟨2 * r.1, by omega⟩ = p + 1 := by
      unfold yPos
      have hdiv : (2 * r.1 / 2) % 2 = 0 := by omega
      simp only [if_pos hdiv, p]
      by_cases h0 : r.1 = 0
      · simp only [dif_pos h0]; ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp only
        have : 8 * k - 1 + 1 = 8 * k := by omega
        rw [this, Nat.mod_self]; omega
      · simp only [dif_neg h0]; ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    have h2 : yPos (k := k) ⟨2 * r.1 + 1, by omega⟩ = p + 2 := by
      unfold yPos
      have hdiv : ((2 * r.1 + 1) / 2) % 2 = 0 := by omega
      simp only [if_pos hdiv, p]
      by_cases h0 : r.1 = 0
      · simp only [dif_pos h0]; ext; rw [Fin.val_add, h2v]; dsimp only
        have : (8 * k - 1 + 2) % (8 * k) = 1 := by
          have : 8 * k - 1 + 2 = 8 * k + 1 := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [this]; omega
      · simp only [dif_neg h0]; ext; rw [Fin.val_add, h2v]; dsimp only
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2]
  · refine ⟨⟨8 * k - 3 - 2 * r.1, by omega⟩, ?_⟩
    have h1 : yPos (k := k) ⟨2 * r.1 + 1, by omega⟩ = (⟨8 * k - 3 - 2 * r.1, by omega⟩ : Fin (8 * k)) + 1 := by
      unfold yPos
      have hdiv : ((2 * r.1 + 1) / 2) % 2 ≠ 0 := by omega
      simp only [if_neg hdiv]
      ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have h2 : yPos (k := k) ⟨2 * r.1, by omega⟩ = (⟨8 * k - 3 - 2 * r.1, by omega⟩ : Fin (8 * k)) + 2 := by
      unfold yPos
      have hdiv : (2 * r.1 / 2) % 2 ≠ 0 := by omega
      simp only [if_neg hdiv]
      ext; rw [Fin.val_add, h2v]; dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2, Set.pair_comm]

/- ### Section 2: `β`-good and `β`-nice collections of `8k`-cycles (Lemmas 2.15 & 2.16) -/

/-- Projection of an `8k`-tuple forgetting positions `p + 1` and `p + 2` (modulo `8k`). -/
private def dropTwo {V : Type} {k : ℕ} [NeZero k] (p : Fin (8 * k)) (x : Fin (8 * k) → V) :
    {j : Fin (8 * k) // j ≠ p + 1 ∧ j ≠ p + 2} → V :=
  fun j => x j.1

private def IsBetaGood {V : Type} {k : ℕ} [NeZero k] (G : SimpleGraph V) (β : ℝ)
    (C : Finset (Fin (8 * k) → V)) : Prop :=
  ∃ s : ℝ, 0 < s ∧
    (∀ x ∈ C, Function.Injective x ∧ ∀ t : Fin (8 * k), G.Adj (x t) (x (t + 1))) ∧
    (∀ y ∈ C, ∀ i : Fin (8 * k),
      ((C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).card : ℝ) ≤ s) ∧
    (∀ p : Fin (8 * k),
      ((C.image (dropTwo p)).card : ℝ) ≤ β * (C.card : ℝ) / (16 * (k : ℝ) * s))

private def IsBetaNice {V : Type} {k : ℕ} [NeZero k] (G : SimpleGraph V) (β : ℝ)
    (C : Finset (Fin (8 * k) → V)) : Prop :=
  (∀ x ∈ C, Function.Injective x ∧ ∀ t : Fin (8 * k), G.Adj (x t) (x (t + 1))) ∧
  ∀ (p : Fin (8 * k)) (y : Fin (8 * k) → V) (u : V),
    let fib := C.filter fun x => ∀ j : Fin (8 * k), j ≠ p + 1 → j ≠ p + 2 → x j = y j
    ((fib.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card : ℝ) ≤ β * (fib.card : ℝ)

/-- Lemma 2.15: Every nonempty `β`-good collection of `8k`-cycles contains a nonempty `β`-nice
subcollection. -/
private theorem exists_betaNice_of_betaGood {V : Type} {k : ℕ} [NeZero k] (hk : 1 ≤ k)
    (G : SimpleGraph V) {β : ℝ} (hβ : 0 < β)
    (C₀ : Finset (Fin (8 * k) → V)) (hC₀_ne : C₀.Nonempty) (hgood : IsBetaGood G β C₀) :
    ∃ C : Finset (Fin (8 * k) → V), C.Nonempty ∧ IsBetaNice G β C := by
  obtain ⟨s, hs, hcyc₀, hsingle, hproj⟩ := hgood
  have h16ks : (0 : ℝ) < 16 * (k : ℝ) * s := by positivity
  -- Strong induction over `(C, D)` where `C ⊆ C₀` and `D` records deleted `(p, proj)` pairs.
  let PType := Σ p : Fin (8 * k), {j : Fin (8 * k) // j ≠ p + 1 ∧ j ≠ p + 2} → V
  let allProj : Finset PType :=
    Finset.univ.sigma fun p : Fin (8 * k) => C₀.image (dropTwo p)
  have hallProj_card : (allProj.card : ℝ) ≤ β * (C₀.card : ℝ) / (2 * s) := by
    rw [Finset.card_sigma, Nat.cast_sum]
    calc (∑ p : Fin (8 * k), ((C₀.image (dropTwo p)).card : ℝ))
        ≤ ∑ _p : Fin (8 * k), (β * (C₀.card : ℝ) / (16 * (k : ℝ) * s)) :=
          Finset.sum_le_sum fun p _ => hproj p
      _ = (8 * k : ℕ) * (β * (C₀.card : ℝ) / (16 * (k : ℝ) * s)) := by simp
      _ = β * (C₀.card : ℝ) / (2 * s) := by
          push_cast
          have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
          field_simp [hkR, hs.ne']
          ring
  have hrec : ∀ (n : ℕ) (C : Finset (Fin (8 * k) → V)) (D : Finset PType),
      C.card = n → C ⊆ C₀ → D ⊆ allProj →
      (∀ d ∈ D, ∀ x ∈ C, dropTwo d.1 x ≠ d.2) →
      ((C₀.card : ℝ) - (C.card : ℝ) ≤ (D.card : ℝ) * (2 * s / β)) →
      (D.Nonempty → (C₀.card : ℝ) - (C.card : ℝ) < (D.card : ℝ) * (2 * s / β)) →
      ∃ C' : Finset (Fin (8 * k) → V), C'.Nonempty ∧ IsBetaNice G β C' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C D hCn hCsub hDsub hDdisj hloss hloss_strict
      have hC_ne : C.Nonempty := by
        by_contra hEmp
        rw [Finset.not_nonempty_iff_eq_empty] at hEmp
        subst hEmp
        have hC0pos : (0 : ℝ) < (C₀.card : ℝ) := by exact_mod_cast hC₀_ne.card_pos
        by_cases hDne : D.Nonempty
        · have h1 := hloss_strict hDne
          have h2 : (D.card : ℝ) ≤ β * (C₀.card : ℝ) / (2 * s) :=
            (Nat.cast_le.mpr (Finset.card_le_card hDsub)).trans hallProj_card
          have h3 : (D.card : ℝ) * (2 * s / β) ≤ (C₀.card : ℝ) := by
            calc (D.card : ℝ) * (2 * s / β)
                ≤ (β * (C₀.card : ℝ) / (2 * s)) * (2 * s / β) :=
                  mul_le_mul_of_nonneg_right h2 (by positivity)
              _ = (C₀.card : ℝ) := by field_simp [hs.ne', hβ.ne']
          simp only [Finset.card_empty, Nat.cast_zero, sub_zero] at h1
          linarith
        · rw [Finset.not_nonempty_iff_eq_empty] at hDne
          subst hDne
          simp only [Finset.card_empty, Nat.cast_zero, sub_zero, zero_mul] at hloss
          linarith
      by_cases hex : ∃ (p : Fin (8 * k)) (y : Fin (8 * k) → V), y ∈ C ∧
          ((C.filter fun x => dropTwo p x = dropTwo p y).card : ℝ) < 2 * s / β
      · obtain ⟨p, y, hyC, hsmall⟩ := hex
        let fib := C.filter fun x => dropTwo p x = dropTwo p y
        have hfib_ne : fib.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨hyC, rfl⟩⟩
        have hfib_sub : fib ⊆ C := Finset.filter_subset _ _
        let d0 : PType := ⟨p, dropTwo p y⟩
        have hd0_mem : d0 ∈ allProj :=
          Finset.mem_sigma.mpr ⟨Finset.mem_univ p, Finset.mem_image.mpr ⟨y, hCsub hyC, rfl⟩⟩
        have hd0_not : d0 ∉ D := fun hmem => hDdisj d0 hmem y hyC rfl
        let C' := C \ fib
        let D' := insert d0 D
        have hC'_lt : C'.card < n := by
          rw [← hCn, Finset.card_sdiff_of_subset hfib_sub]
          have hpos := hfib_ne.card_pos
          have hle := Finset.card_le_card hfib_sub
          omega
        have hC'_sub : C' ⊆ C₀ := Finset.sdiff_subset.trans hCsub
        have hD'_sub : D' ⊆ allProj := Finset.insert_subset hd0_mem hDsub
        have hD'_disj : ∀ d ∈ D', ∀ x ∈ C', dropTwo d.1 x ≠ d.2 := by
          intro d hd x hx
          rcases Finset.mem_insert.mp hd with rfl | hdD
          · intro heq
            exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, heq⟩)
          · exact hDdisj d hdD x (Finset.mem_sdiff.mp hx).1
        have hcardC' : (C'.card : ℝ) = (C.card : ℝ) - (fib.card : ℝ) := by
          rw [Finset.card_sdiff_of_subset hfib_sub, Nat.cast_sub (Finset.card_le_card hfib_sub)]
        have hcardD' : (D'.card : ℝ) = (D.card : ℝ) + 1 := by
          rw [Finset.card_insert_of_notMem hd0_not, Nat.cast_add, Nat.cast_one]
        have hloss' : (C₀.card : ℝ) - (C'.card : ℝ) < (D'.card : ℝ) * (2 * s / β) := by
          rw [hcardC', hcardD']
          linarith
        exact ih C'.card hC'_lt C' D' rfl hC'_sub hD'_sub hD'_disj hloss'.le (fun _ => hloss')
      · push Not at hex
        refine ⟨C, hC_ne, fun x hx => hcyc₀ x (hCsub hx), fun p y u => ?_⟩
        let fib := C.filter fun x => ∀ j : Fin (8 * k), j ≠ p + 1 → j ≠ p + 2 → x j = y j
        by_cases hfib_ne : fib.Nonempty
        · obtain ⟨y₀, hy₀⟩ := hfib_ne
          have hy₀C : y₀ ∈ C := (Finset.mem_filter.mp hy₀).1
          have hfib_eq : fib = C.filter fun x => dropTwo p x = dropTwo p y₀ := by
            ext x
            simp only [fib, Finset.mem_filter, dropTwo, funext_iff, Subtype.forall]
            constructor
            · rintro ⟨hxC, hxy⟩
              exact ⟨hxC, fun j hj => (hxy j hj.1 hj.2).trans ((Finset.mem_filter.mp hy₀).2 j hj.1 hj.2).symm⟩
            · rintro ⟨hxC, hxy₀⟩
              exact ⟨hxC, fun j h1 h2 => (hxy₀ j ⟨h1, h2⟩).trans ((Finset.mem_filter.mp hy₀).2 j h1 h2)⟩
          have hge : 2 * s / β ≤ (fib.card : ℝ) := by
            rw [hfib_eq]
            exact hex p y₀ hy₀C
          have hhit1 : ((fib.filter fun x => x (p + 1) = u).card : ℝ) ≤ s := by
            by_cases h1 : (fib.filter fun x => x (p + 1) = u).Nonempty
            · obtain ⟨w, hw⟩ := h1
              have hwC : w ∈ C := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
              have hsub : (fib.filter fun x => x (p + 1) = u) ⊆
                  C₀.filter fun x => ∀ j : Fin (8 * k), j ≠ p + 2 → x j = w j := by
                intro x hx
                have hx1 := (Finset.mem_filter.mp hx).1
                have hxu := (Finset.mem_filter.mp hx).2
                refine Finset.mem_filter.mpr ⟨hCsub (Finset.mem_filter.mp hx1).1, fun j hj2 => ?_⟩
                by_cases hj1 : j = p + 1
                · subst hj1; exact hxu.trans (Finset.mem_filter.mp hw).2.symm
                · exact ((Finset.mem_filter.mp hx1).2 j hj1 hj2).trans
                    ((Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2 j hj1 hj2).symm
              exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hsingle w (hCsub hwC) (p + 2))
            · rw [Finset.not_nonempty_iff_eq_empty.mp h1, Finset.card_empty, Nat.cast_zero]
              exact hs.le
          have hhit2 : ((fib.filter fun x => x (p + 2) = u).card : ℝ) ≤ s := by
            by_cases h2 : (fib.filter fun x => x (p + 2) = u).Nonempty
            · obtain ⟨w, hw⟩ := h2
              have hwC : w ∈ C := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
              have hsub : (fib.filter fun x => x (p + 2) = u) ⊆
                  C₀.filter fun x => ∀ j : Fin (8 * k), j ≠ p + 1 → x j = w j := by
                intro x hx
                have hx1 := (Finset.mem_filter.mp hx).1
                have hxu := (Finset.mem_filter.mp hx).2
                refine Finset.mem_filter.mpr ⟨hCsub (Finset.mem_filter.mp hx1).1, fun j hj1 => ?_⟩
                by_cases hj2 : j = p + 2
                · subst hj2; exact hxu.trans (Finset.mem_filter.mp hw).2.symm
                · exact ((Finset.mem_filter.mp hx1).2 j hj1 hj2).trans
                    ((Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2 j hj1 hj2).symm
              exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hsingle w (hCsub hwC) (p + 1))
            · rw [Finset.not_nonempty_iff_eq_empty.mp h2, Finset.card_empty, Nat.cast_zero]
              exact hs.le
          have hunion : (fib.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card ≤
              (fib.filter fun x => x (p + 1) = u).card + (fib.filter fun x => x (p + 2) = u).card := by
            calc (fib.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card
                ≤ ((fib.filter fun x => x (p + 1) = u) ∪ (fib.filter fun x => x (p + 2) = u)).card := by
                  apply Finset.card_le_card
                  intro x hx
                  rw [Finset.mem_union]
                  rcases Finset.mem_filter.mp hx with ⟨hxf, h1 | h2⟩
                  · exact Or.inl (Finset.mem_filter.mpr ⟨hxf, h1⟩)
                  · exact Or.inr (Finset.mem_filter.mpr ⟨hxf, h2⟩)
              _ ≤ _ := Finset.card_union_le _ _
          have h2s : 2 * s ≤ β * (fib.card : ℝ) := by
            have := mul_le_mul_of_nonneg_left hge hβ.le
            have heq : β * (2 * s / β) = 2 * s := by field_simp [hβ.ne']
            linarith
          have hunionR : ((fib.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card : ℝ) ≤
              ((fib.filter fun x => x (p + 1) = u).card : ℝ) +
              ((fib.filter fun x => x (p + 2) = u).card : ℝ) := by
            exact_mod_cast hunion
          linarith
        · dsimp only
          have hfib_emp : fib = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfib_ne
          change ((fib.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card : ℝ) ≤ β * (fib.card : ℝ)
          rw [hfib_emp]; simp
  exact hrec C₀.card C₀ ∅ rfl Subset.rfl (Finset.empty_subset _) (by simp)
    (by simp) (by simp)

/-- Generic fiber-partition inequality: if every nonempty `proj`-fiber of `S_C` agrees with the
corresponding `proj`-fiber of `C` and satisfies `|fiber ∩ hit| ≤ c * |fiber|`, then
`|S_C ∩ hit| ≤ c * |S_C|`. -/
private lemma card_filter_le_of_fiber_bound {α β : Type} (S_C C : Finset α)
    (proj : α → β) (hit : α → Prop) (c : ℝ)
    (hfib : ∀ q ∈ S_C.image proj, S_C.filter (fun x => proj x = q) = C.filter (fun x => proj x = q))
    (hbound : ∀ x₀ ∈ S_C,
      (((C.filter fun x => proj x = proj x₀).filter hit).card : ℝ) ≤
        c * ((C.filter fun x => proj x = proj x₀).card : ℝ)) :
    ((S_C.filter hit).card : ℝ) ≤ c * (S_C.card : ℝ) := by
  let P_set := S_C.image proj
  have hpart_hit : ((S_C.filter hit).card : ℝ) =
      ∑ q ∈ P_set, (((S_C.filter fun x => proj x = q).filter hit).card : ℝ) := by
    rw [← Nat.cast_sum]; congr 1; rw [← Finset.card_biUnion]
    · congr 1; ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, P_set, Finset.mem_image]
      exact ⟨fun ⟨hx, hxu⟩ => ⟨proj x, ⟨x, hx, rfl⟩, ⟨hx, rfl⟩, hxu⟩,
        fun ⟨_, _, ⟨hx, _⟩, hxu⟩ => ⟨hx, hxu⟩⟩
    · intro q₁ _ q₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hne (((Finset.mem_filter.mp (Finset.mem_filter.mp hx₁).1).2).symm.trans
        (Finset.mem_filter.mp (Finset.mem_filter.mp hx₂).1).2)
  have hpart_all : (S_C.card : ℝ) = ∑ q ∈ P_set, ((S_C.filter fun x => proj x = q).card : ℝ) := by
    rw [← Nat.cast_sum]; congr 1; rw [← Finset.card_biUnion]
    · congr 1; ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter, P_set, Finset.mem_image]
      exact ⟨fun hx => ⟨proj x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
    · intro q₁ _ q₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hne (((Finset.mem_filter.mp hx₁).2).symm.trans (Finset.mem_filter.mp hx₂).2)
  rw [hpart_hit, hpart_all, Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [hfib q hq]
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hq
  exact hbound x₀ hx₀

/-- Helper for Lemma 2.16: right-interleaving branch bound from `IsBetaNice`. -/
private lemma interleave_branch_right {V : Type} [Fintype V]
    {k : ℕ} [NeZero k] (hk : 1 ≤ k) (G : SimpleGraph V) {β : ℝ}
    (C : Finset (Fin (8 * k) → V)) (hnice : IsBetaNice G β C)
    (y : Fin (4 * k) → V) (r : Fin (2 * k)) (u : V) :
    (((Finset.univ.filter fun z : Fin (4 * k) → V => interleave y z ∈ C ∧
        (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ)) ≤
      β * ((Finset.univ.filter fun z : Fin (4 * k) → V => interleave y z ∈ C).card : ℝ) := by
  have hprop := hnice.2
  obtain ⟨p, hp⟩ := zPos_pair_consecutive hk r
  let S := Finset.univ.filter fun z : Fin (4 * k) → V => interleave y z ∈ C
  let S_C := S.image fun z => interleave y z
  have hS_inj : Set.InjOn (fun z : Fin (4 * k) → V => interleave y z) (S : Set _) :=
    fun _ _ _ _ h => interleave_inj_of_y h
  have hS_card : S_C.card = S.card := Finset.card_image_of_injOn hS_inj
  have hfib_eq : ∀ q ∈ S_C.image (dropTwo p),
      S_C.filter (fun x => dropTwo p x = q) = C.filter (fun x => dropTwo p x = q) := by
    intro q hq
    obtain ⟨z₀, hz₀S, hqz₀⟩ := Finset.mem_image.mp hq
    obtain ⟨z₀W, _, rfl⟩ := Finset.mem_image.mp hz₀S
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxSC, hxq⟩
      obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hxSC
      exact ⟨(Finset.mem_filter.mp hzS).2, hxq⟩
    · rintro ⟨hxC, hxq⟩
      refine ⟨?_, hxq⟩
      let z : Fin (4 * k) → V := fun i => x (zPos i)
      have hxy : interleave y z = x := by
        funext t
        by_cases ht : t = p + 1 ∨ t = p + 2
        · have hmem : t ∈ ({p + 1, p + 2} : Set (Fin (8 * k))) := ht
          rw [← hp] at hmem
          rcases hmem with rfl | rfl <;> rw [interleave_zPos]
        · push Not at ht
          have hxt : x t = interleave y z₀W t := congrFun (hxq.trans hqz₀.symm) ⟨t, ht⟩
          have hzt : ∀ i : Fin (4 * k), t = zPos i → z i = z₀W i := fun i hi => by
            dsimp [z]; rw [← hi, hxt, hi, interleave_zPos]
          unfold interleave at hxt ⊢
          by_cases h1 : t.1 < 4 * k
          · simp only [dif_pos h1] at hxt ⊢
            by_cases h2 : (t.1 / 2) % 2 = 0
            · simp only [if_pos h2] at hxt ⊢; exact hxt.symm
            · simp only [if_neg h2] at hxt ⊢
              have hodd : (t.1 / 2) % 2 = 1 := by omega
              have hpos : t = zPos (k := k) ⟨t.1, h1⟩ := by
                unfold zPos; simp only [if_pos hodd]
              exact (hzt ⟨t.1, h1⟩ hpos).trans hxt.symm
          · simp only [dif_neg h1] at hxt ⊢
            by_cases h2 : ((8 * k - 1 - t.1) / 2) % 2 = 0
            · simp only [if_pos h2] at hxt ⊢
              have hne1 : ((8 * k - 1 - t.1) / 2) % 2 ≠ 1 := by omega
              have hpos : t = zPos (k := k) ⟨8 * k - 1 - t.1, by omega⟩ := by
                unfold zPos; simp only [if_neg hne1]; ext; dsimp only; omega
              exact (hzt ⟨8 * k - 1 - t.1, by omega⟩ hpos).trans hxt.symm
            · simp only [if_neg h2] at hxt ⊢; exact hxt.symm
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm ▸ hxC⟩, hxy⟩
  have hhit_sub : (Finset.univ.filter fun z : Fin (4 * k) → V => interleave y z ∈ C ∧
        (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card ≤
      (S_C.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card := by
    have hinj : Function.Injective (fun z : Fin (4 * k) → V => interleave y z) :=
      fun _ _ h => interleave_inj_of_y h
    rw [← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hzC, hzu⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzC⟩, rfl⟩, ?_⟩
    have hset : ∀ a : Fin (8 * k), a ∈ ({zPos ⟨2 * r.1, by omega⟩, zPos ⟨2 * r.1 + 1, by omega⟩} : Set (Fin (8 * k))) →
        a = p + 1 ∨ a = p + 2 := by rw [hp]; intro a ha; exact ha
    rcases hzu with h1 | h2
    · rcases hset (zPos ⟨2 * r.1, by omega⟩) (Or.inl rfl) with heq | heq
      · left; rw [← heq, interleave_zPos]; exact h1
      · right; rw [← heq, interleave_zPos]; exact h1
    · rcases hset (zPos ⟨2 * r.1 + 1, by omega⟩) (Or.inr rfl) with heq | heq
      · left; rw [← heq, interleave_zPos]; exact h2
      · right; rw [← heq, interleave_zPos]; exact h2
  have hfib_le := card_filter_le_of_fiber_bound S_C C (dropTwo p) (fun x => x (p + 1) = u ∨ x (p + 2) = u) β
    (by convert hfib_eq)
    (fun x₀ _ => by
      have h1 := hprop p x₀ u
      dsimp only at h1
      refine le_trans (le_of_eq ?_) (h1.trans_eq ?_)
      · congr 1; congr 1; ext x
        simp only [Finset.mem_filter, dropTwo, funext_iff, Subtype.forall]
        exact and_congr_left fun _ => and_congr_right fun _ =>
          ⟨fun h j h1 h2 => h j ⟨h1, h2⟩, fun h j hj => h j hj.1 hj.2⟩
      · congr 1; congr 1; congr 1; ext x
        simp only [Finset.mem_filter, dropTwo, funext_iff, Subtype.forall]
        exact and_congr_right fun _ =>
          ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩)
  change _ ≤ β * (S.card : ℝ)
  refine (Nat.cast_le.mpr hhit_sub).trans (le_trans (le_of_eq ?_) (hfib_le.trans_eq (by rw [hS_card])))
  congr 1; congr 1; ext x; simp only [Finset.mem_filter]

/-- Helper for Lemma 2.16: left-interleaving branch bound from `IsBetaNice`. -/
private lemma interleave_branch_left {V : Type} [Fintype V]
    {k : ℕ} [NeZero k] (hk : 1 ≤ k) (G : SimpleGraph V) {β : ℝ}
    (C : Finset (Fin (8 * k) → V)) (hnice : IsBetaNice G β C)
    (y : Fin (4 * k) → V) (r : Fin (2 * k)) (u : V) :
    (((Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y ∈ C ∧
        (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ)) ≤
      β * ((Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y ∈ C).card : ℝ) := by
  have hprop := hnice.2
  obtain ⟨p, hp⟩ := yPos_pair_consecutive hk r
  let S := Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y ∈ C
  let S_C := S.image fun z => interleave z y
  have hS_inj : Set.InjOn (fun z : Fin (4 * k) → V => interleave z y) (S : Set _) :=
    fun _ _ _ _ h => interleave_inj_of_z h
  have hS_card : S_C.card = S.card := Finset.card_image_of_injOn hS_inj
  have hfib_eq : ∀ q ∈ S_C.image (dropTwo p),
      S_C.filter (fun x => dropTwo p x = q) = C.filter (fun x => dropTwo p x = q) := by
    intro q hq
    obtain ⟨z₀, hz₀S, hqz₀⟩ := Finset.mem_image.mp hq
    obtain ⟨z₀W, _, rfl⟩ := Finset.mem_image.mp hz₀S
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxSC, hxq⟩
      obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hxSC
      exact ⟨(Finset.mem_filter.mp hzS).2, hxq⟩
    · rintro ⟨hxC, hxq⟩
      refine ⟨?_, hxq⟩
      let z : Fin (4 * k) → V := fun i => x (yPos i)
      have hxy : interleave z y = x := by
        funext t
        by_cases ht : t = p + 1 ∨ t = p + 2
        · have hmem : t ∈ ({p + 1, p + 2} : Set (Fin (8 * k))) := ht
          rw [← hp] at hmem
          rcases hmem with rfl | rfl <;> rw [interleave_yPos]
        · push Not at ht
          have hxt : x t = interleave z₀W y t := congrFun (hxq.trans hqz₀.symm) ⟨t, ht⟩
          have hzt : ∀ i : Fin (4 * k), t = yPos i → z i = z₀W i := fun i hi => by
            dsimp [z]; rw [← hi, hxt, hi, interleave_yPos]
          unfold interleave at hxt ⊢
          by_cases h1 : t.1 < 4 * k
          · simp only [dif_pos h1] at hxt ⊢
            by_cases h2 : (t.1 / 2) % 2 = 0
            · simp only [if_pos h2] at hxt ⊢
              have hpos : t = yPos (k := k) ⟨t.1, h1⟩ := by
                unfold yPos; simp only [if_pos h2]
              exact (hzt ⟨t.1, h1⟩ hpos).trans hxt.symm
            · simp only [if_neg h2] at hxt ⊢; exact hxt.symm
          · simp only [dif_neg h1] at hxt ⊢
            by_cases h2 : ((8 * k - 1 - t.1) / 2) % 2 = 0
            · simp only [if_pos h2] at hxt ⊢; exact hxt.symm
            · simp only [if_neg h2] at hxt ⊢
              have hpos : t = yPos (k := k) ⟨8 * k - 1 - t.1, by omega⟩ := by
                unfold yPos; simp only [if_neg h2]; ext; dsimp only; omega
              exact (hzt ⟨8 * k - 1 - t.1, by omega⟩ hpos).trans hxt.symm
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm ▸ hxC⟩, hxy⟩
  have hhit_sub : (Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y ∈ C ∧
        (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card ≤
      (S_C.filter fun x => x (p + 1) = u ∨ x (p + 2) = u).card := by
    have hinj : Function.Injective (fun z : Fin (4 * k) → V => interleave z y) :=
      fun _ _ h => interleave_inj_of_z h
    rw [← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hzC, hzu⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzC⟩, rfl⟩, ?_⟩
    have hset : ∀ a : Fin (8 * k), a ∈ ({yPos ⟨2 * r.1, by omega⟩, yPos ⟨2 * r.1 + 1, by omega⟩} : Set (Fin (8 * k))) →
        a = p + 1 ∨ a = p + 2 := by rw [hp]; intro a ha; exact ha
    rcases hzu with h1 | h2
    · rcases hset (yPos ⟨2 * r.1, by omega⟩) (Or.inl rfl) with heq | heq
      · left; rw [← heq, interleave_yPos]; exact h1
      · right; rw [← heq, interleave_yPos]; exact h1
    · rcases hset (yPos ⟨2 * r.1 + 1, by omega⟩) (Or.inr rfl) with heq | heq
      · left; rw [← heq, interleave_yPos]; exact h2
      · right; rw [← heq, interleave_yPos]; exact h2
  have hfib_le := card_filter_le_of_fiber_bound S_C C (dropTwo p) (fun x => x (p + 1) = u ∨ x (p + 2) = u) β
    (by convert hfib_eq)
    (fun x₀ _ => by
      have h1 := hprop p x₀ u
      dsimp only at h1
      refine le_trans (le_of_eq ?_) (h1.trans_eq ?_)
      · congr 1; congr 1; ext x
        simp only [Finset.mem_filter, dropTwo, funext_iff, Subtype.forall]
        exact and_congr_left fun _ => and_congr_right fun _ =>
          ⟨fun h j h1 h2 => h j ⟨h1, h2⟩, fun h j hj => h j hj.1 hj.2⟩
      · congr 1; congr 1; congr 1; ext x
        simp only [Finset.mem_filter, dropTwo, funext_iff, Subtype.forall]
        exact and_congr_right fun _ =>
          ⟨fun h j hj => h j hj.1 hj.2, fun h j h1 h2 => h j ⟨h1, h2⟩⟩)
  change _ ≤ β * (S.card : ℝ)
  refine (Nat.cast_le.mpr hhit_sub).trans (le_trans (le_of_eq ?_) (hfib_le.trans_eq (by rw [hS_card])))
  congr 1; congr 1; ext x; simp only [Finset.mem_filter]

/-- Lemma 2.16: A nonempty `β`-nice collection of `8k`-cycles with small enough `β` forces a copy
of `janzerGraph k ℓ` in `G`. -/
private theorem janzerGraph_copy_of_betaNice {V : Type} [Fintype V]
    {k ℓ : ℕ} [NeZero k] [NeZero ℓ] (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) (G : SimpleGraph V) {β : ℝ} (hβ : 0 ≤ β)
    (C : Finset (Fin (8 * k) → V)) (hC_ne : C.Nonempty) (hnice : IsBetaNice G β C)
    (hsmall : ((Fintype.card V : ℝ) ^ (4 * k)) *
      (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2 * β)) ^ ℓ < 1) :
    janzerGraph k ℓ hk hℓ ⊑ G := by
  have hcyc := hnice.1
  -- Auxiliary graph on active `4k`-tuples `W`.
  let adjRaw (y z : Fin (4 * k) → V) : Prop := interleave y z ∈ C ∨ interleave z y ∈ C
  let W := {y : Fin (4 * k) → V // ∃ z, adjRaw y z}
  have hW_ne : Nonempty W := by
    obtain ⟨x, hxC⟩ := hC_ne
    let y : Fin (4 * k) → V := fun i => x (yPos i)
    let z : Fin (4 * k) → V := fun i => x (zPos i)
    have hint : interleave y z = x := by
      funext t
      unfold interleave y z yPos zPos
      by_cases h1 : t.1 < 4 * k
      · simp only [dif_pos h1]
        by_cases h2 : (t.1 / 2) % 2 = 0
        · simp only [if_pos h2]
        · have h2' : (t.1 / 2) % 2 = 1 := by omega
          simp only [if_neg h2, if_pos h2']
      · simp only [dif_neg h1]
        let idx : Fin (4 * k) := ⟨8 * k - 1 - t.1, by omega⟩
        have hsub : 8 * k - 1 - idx.1 = t.1 := by dsimp [idx]; omega
        by_cases h2 : (idx.1 / 2) % 2 = 0
        · have h2' : (idx.1 / 2) % 2 ≠ 1 := by omega
          simp only [if_pos h2, if_neg h2', idx]
          congr 1; ext; exact hsub
        · simp only [if_neg h2, idx]
          congr 1; ext; exact hsub
    exact ⟨⟨y, z, Or.inl (hint.symm ▸ hxC)⟩⟩
  let 𝒢 : SimpleGraph W :=
    { Adj := fun y z => adjRaw y.1 z.1
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨by
        rintro ⟨y, _⟩ (h | h)
        · have hinj := (hcyc _ h).1
          have h0 : interleave y y (yPos ⟨0, by omega⟩) = interleave y y (zPos ⟨0, by omega⟩) := by
            rw [interleave_yPos, interleave_zPos]
          exact yPos_ne_zPos ⟨0, by omega⟩ ⟨0, by omega⟩ (hinj h0)
        · have hinj := (hcyc _ h).1
          have h0 : interleave y y (yPos ⟨0, by omega⟩) = interleave y y (zPos ⟨0, by omega⟩) := by
            rw [interleave_yPos, interleave_zPos]
          exact yPos_ne_zPos ⟨0, by omega⟩ ⟨0, by omega⟩ (hinj h0)⟩ }
  have hdeg_pos : ∀ y : W, 0 < 𝒢.degree y := by
    rintro ⟨y, z, hyz⟩
    have hzW : ∃ w, adjRaw z w := ⟨y, hyz.symm⟩
    exact Finset.card_pos.mpr ⟨⟨z, hzW⟩, (mem_neighborFinset 𝒢 _ _).mpr hyz⟩
  have hbranch1 : ∀ (y : W) (r : Fin (2 * k)) (u : V),
      (((Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C ∧
          (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ)) ≤
        β * ((Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C).card : ℝ) := by
    intro y r u
    have h1 : (Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C ∧
        (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card =
        (Finset.univ.filter fun z : Fin (4 * k) → V => interleave y.1 z ∈ C ∧
          (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z hz; obtain ⟨hC, hu⟩ := (Finset.mem_filter.mp hz).2
        exact ⟨⟨z, y.1, Or.inr hC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, hu⟩, rfl⟩
    have h2 : (Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C).card =
        (Finset.univ.filter fun z : Fin (4 * k) → V => interleave y.1 z ∈ C).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z hz; have hC := (Finset.mem_filter.mp hz).2
        exact ⟨⟨z, y.1, Or.inr hC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩, rfl⟩
    rw [h1, h2]
    exact interleave_branch_right hk G C hnice y.1 r u
  have hbranch2 : ∀ (y : W) (r : Fin (2 * k)) (u : V),
      (((Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C ∧
          (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ)) ≤
        β * ((Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C).card : ℝ) := by
    intro y r u
    have h1 : (Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C ∧
        (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card =
        (Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y.1 ∈ C ∧
          (z ⟨2 * r.1, by omega⟩ = u ∨ z ⟨2 * r.1 + 1, by omega⟩ = u)).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z hz; obtain ⟨hC, hu⟩ := (Finset.mem_filter.mp hz).2
        exact ⟨⟨z, y.1, Or.inl hC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, hu⟩, rfl⟩
    have h2 : (Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C).card =
        (Finset.univ.filter fun z : Fin (4 * k) → V => interleave z y.1 ∈ C).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_
      · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
      · intro z hz; have hC := (Finset.mem_filter.mp hz).2
        exact ⟨⟨z, y.1, Or.inl hC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩, rfl⟩
    rw [h1, h2]
    exact interleave_branch_left hk G C hnice y.1 r u
  -- Local conflict ratio bound:
  let conflict (x z : W) : Prop := ∃ i j : Fin (4 * k), x.1 i = z.1 j
  have hloc : ∀ x y : W,
      (((𝒢.neighborFinset y).filter (conflict x)).card : ℝ) ≤
        (16 * (k : ℝ) ^ 2 * β) * (𝒢.degree y : ℝ) := by
    intro x y
    have hhit_u : ∀ u : V,
        (((𝒢.neighborFinset y).filter fun z => ∃ i : Fin (4 * k), z.1 i = u).card : ℝ) ≤
          (4 * (k : ℝ) * β) * (𝒢.degree y : ℝ) := by
      intro u
      have hsub : (𝒢.neighborFinset y).filter (fun z => ∃ i : Fin (4 * k), z.1 i = u) ⊆
          (Finset.univ : Finset (Fin (2 * k))).biUnion fun r =>
            (Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C ∧
              (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)) ∪
            (Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C ∧
              (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)) := by
        intro z hz
        obtain ⟨hzN, i, hi⟩ := Finset.mem_filter.mp hz
        have hadj : interleave y.1 z.1 ∈ C ∨ interleave z.1 y.1 ∈ C := (mem_neighborFinset 𝒢 _ _).mp hzN
        let r : Fin (2 * k) := ⟨i.1 / 2, by omega⟩
        have hpair : z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u := by
          by_cases hpar : i.1 % 2 = 0
          · left; convert hi using 2; ext; dsimp [r]; omega
          · right; convert hi using 2; ext; dsimp [r]; omega
        refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, ?_⟩
        rw [Finset.mem_union]
        rcases hadj with h1 | h2
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h1, hpair⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h2, hpair⟩)
      have hb1_le : ((Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C).card : ℝ) ≤
          (𝒢.degree y : ℝ) := by
        rw [← card_neighborFinset_eq_degree]
        exact_mod_cast Finset.card_le_card fun z hz =>
          (mem_neighborFinset 𝒢 _ _).mpr (Or.inl (Finset.mem_filter.mp hz).2)
      have hb2_le : ((Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C).card : ℝ) ≤
          (𝒢.degree y : ℝ) := by
        rw [← card_neighborFinset_eq_degree]
        exact_mod_cast Finset.card_le_card fun z hz =>
          (mem_neighborFinset 𝒢 _ _).mpr (Or.inr (Finset.mem_filter.mp hz).2)
      have hcard_le : ((𝒢.neighborFinset y).filter (fun z => ∃ i : Fin (4 * k), z.1 i = u)).card ≤
          ∑ r : Fin (2 * k),
            ((Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C ∧
                (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card +
             (Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C ∧
                (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card) :=
        (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans
          (Finset.sum_le_sum fun r _ => Finset.card_union_le _ _))
      calc (((𝒢.neighborFinset y).filter fun z => ∃ i : Fin (4 * k), z.1 i = u).card : ℝ)
          ≤ ∑ r : Fin (2 * k),
              (((Finset.univ.filter fun z : W => interleave y.1 z.1 ∈ C ∧
                  (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ) +
               ((Finset.univ.filter fun z : W => interleave z.1 y.1 ∈ C ∧
                  (z.1 ⟨2 * r.1, by omega⟩ = u ∨ z.1 ⟨2 * r.1 + 1, by omega⟩ = u)).card : ℝ)) := by
            exact_mod_cast hcard_le
        _ ≤ ∑ _r : Fin (2 * k), (β * (𝒢.degree y : ℝ) + β * (𝒢.degree y : ℝ)) := by
            apply Finset.sum_le_sum
            intro r _
            exact add_le_add
              ((hbranch1 y r u).trans (mul_le_mul_of_nonneg_left hb1_le hβ))
              ((hbranch2 y r u).trans (mul_le_mul_of_nonneg_left hb2_le hβ))
        _ = (4 * (k : ℝ) * β) * (𝒢.degree y : ℝ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
    have hsubX : (𝒢.neighborFinset y).filter (conflict x) ⊆
        (Finset.univ : Finset (Fin (4 * k))).biUnion fun j =>
          (𝒢.neighborFinset y).filter fun z => ∃ i : Fin (4 * k), z.1 i = x.1 j := by
      intro z hz
      obtain ⟨hzN, j, i, hij⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
        Finset.mem_filter.mpr ⟨hzN, i, hij.symm⟩⟩
    calc (((𝒢.neighborFinset y).filter (conflict x)).card : ℝ)
        ≤ ∑ j : Fin (4 * k),
            (((𝒢.neighborFinset y).filter fun z => ∃ i : Fin (4 * k), z.1 i = x.1 j).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hsubX).trans Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin (4 * k), (4 * (k : ℝ) * β) * (𝒢.degree y : ℝ) :=
          Finset.sum_le_sum fun j _ => hhit_u (x.1 j)
      _ = (16 * (k : ℝ) ^ 2 * β) * (𝒢.degree y : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- Apply `conflict_free_cycle_of_ratio` from `R2`!
  let n_c := ℓ - 2
  have hn_c : n_c + 2 = ℓ := by omega
  have hL : ((n_c + 1) + (n_c + 1)) + 2 = 2 * ℓ := by omega
  have hW_card : (Fintype.card W : ℝ) ≤ (Fintype.card V : ℝ) ^ (4 * k) := by
    have h1 : Fintype.card W ≤ Fintype.card (Fin (4 * k) → V) := Fintype.card_subtype_le _
    rw [Fintype.card_fun, Fintype.card_fin] at h1
    exact_mod_cast h1
  have hsmallW : (Fintype.card W : ℝ) *
      (4 * ((n_c + 2 : ℕ) : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2 * β)) ^ (n_c + 2) < 1 := by
    rw [hn_c]
    exact (mul_le_mul_of_nonneg_right hW_card (by positivity)).trans_lt hsmall
  obtain ⟨f0, hf0_cf⟩ := conflict_free_cycle_of_ratio 𝒢 (fun y => by convert hdeg_pos y) conflict
    (fun _ _ ⟨i, j, hij⟩ => ⟨j, i, hij.symm⟩) (16 * (k : ℝ) ^ 2 * β) (by positivity)
    (fun x y => by convert hloc x y) n_c hsmallW
  -- Reindex `cycleGraph (((n_c + 1) + (n_c + 1)) + 2)` to `Fin (2 * ℓ)`:
  let eL : Fin (2 * ℓ) ≃ Fin (((n_c + 1) + (n_c + 1)) + 2) := finCongr hL.symm
  let xLayer (j : Fin (2 * ℓ)) : W := f0 (eL j)
  have hxLayer_adj : ∀ j : Fin (2 * ℓ), 𝒢.Adj (xLayer j) (xLayer (j + 1)) := by
    intro j
    apply f0.map_rel
    rw [cycleGraph_adj]
    right
    ext
    have h1 : (eL (j + 1)).1 = (j.1 + 1) % (2 * ℓ) := by
      simp [eL, Fin.val_add]
    have h2 : (eL j).1 = j.1 := rfl
    have hmod : (((n_c + 1) + (n_c + 1)) + 2) = 2 * ℓ := hL
    rw [Fin.val_sub, fin_val_one_of_gt (by omega : 1 < ((n_c + 1) + (n_c + 1)) + 2)]
    simp only [hmod, h1, h2]
    by_cases hj : j.1 + 1 < 2 * ℓ
    · rw [Nat.mod_eq_of_lt hj]
      have : 2 * ℓ - j.1 + (j.1 + 1) = 1 + 2 * ℓ := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hjEq : j.1 + 1 = 2 * ℓ := by omega
      rw [hjEq, Nat.mod_self, add_zero]
      have : 2 * ℓ - j.1 = 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  -- Embed `janzerGraph k ℓ hk hℓ` into `G`:
  refine ⟨⟨⟨fun u => (xLayer u.2).1 u.1, ?_⟩, ?_⟩⟩
  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ (⟨hj, hi⟩ | ⟨hj | hj, hi⟩)
    · dsimp only at hj hi; subst hj; subst hi
      rcases hxLayer_adj j₁ with h1 | h2
      · exact (interleave_edges hk G (hcyc _ h1).2).1 i₁
      · exact (interleave_edges hk G (hcyc _ h2).2).2.1 i₁
    · dsimp only at hj hi; subst hj; subst hi
      rcases hxLayer_adj j₁ with h1 | h2
      · exact (interleave_edges hk G (hcyc _ h1).2).2.2 i₁
      · have hrev := (interleave_edges hk G (hcyc _ h2).2).2.2 (crossMate i₁)
        rw [crossMate_involutive] at hrev
        exact hrev.symm
    · dsimp only at hj hi; subst hj; subst hi
      rcases hxLayer_adj j₂ with h1 | h2
      · have hrev := (interleave_edges hk G (hcyc _ h1).2).2.2 (crossMate i₁)
        rw [crossMate_involutive] at hrev
        exact hrev.symm
      · exact (interleave_edges hk G (hcyc _ h2).2).2.2 i₁
  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hEq
    by_cases hj : j₁ = j₂
    · subst hj
      have hadj := hxLayer_adj j₁
      have hinj : Function.Injective (xLayer j₁).1 := by
        intro a b hab
        rcases hadj with h1 | h2
        · have hI := (hcyc _ h1).1
          have hpos : yPos a = yPos b := hI (by rwa [interleave_yPos, interleave_yPos])
          exact yPos_injective hpos
        · have hI := (hcyc _ h2).1
          have hpos : zPos a = zPos b := hI (by rwa [interleave_zPos, interleave_zPos])
          exact zPos_injective hpos
      exact Prod.ext (hinj hEq) rfl
    · exfalso
      exact hf0_cf (eL j₁) (eL j₂) (fun h => hj (eL.injective h)) ⟨i₁, i₂, hEq⟩

/- ### Section 3: Deterministic Regularization and `C_4`-Balanced Spanning Subgraph -/

/-- Edges of `G` with both endpoints in `S`. -/
private noncomputable def inducedEdgeCount {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).edgeFinset.card

private lemma two_mul_inducedEdgeCount {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    2 * inducedEdgeCount G S = ∑ v ∈ S, (S.filter (G.Adj v)).card := by
  unfold inducedEdgeCount
  have hsum := (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges
  rw [← hsum]
  rw [← Finset.sum_coe_sort S (fun v => (S.filter (G.Adj v)).card)]
  apply Finset.sum_congr rfl
  rintro ⟨v, hv⟩ _
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_filter.mpr ⟨w.2, (mem_neighborFinset (G.induce (S : Set V)) _ _).mp hw⟩
  · intro w₁ _ w₂ _ h; exact Subtype.ext h
  · intro u hu
    obtain ⟨huS, huv⟩ := Finset.mem_filter.mp hu
    exact ⟨⟨u, huS⟩, (mem_neighborFinset _ _ _).mpr huv, rfl⟩

private lemma inducedEdgeCount_le_sq_div_two {V : Type} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    2 * inducedEdgeCount G S ≤ S.card * S.card := by
  rw [two_mul_inducedEdgeCount]
  calc ∑ v ∈ S, (S.filter (G.Adj v)).card
      ≤ ∑ _v ∈ S, S.card := Finset.sum_le_sum fun v _ => Finset.card_filter_le S _
    _ = S.card * S.card := by simp

/-- Helper for regularization: every `Finset` `S` has an `a`-subset achieving at least the
average weight of `f : V → ℕ`. -/
private lemma exists_heavy_subset_card_eq {V : Type}
    (S : Finset V) (a : ℕ) (ha_pos : 0 < a) (ha_le : a ≤ S.card) (f : V → ℕ) :
    ∃ W ⊆ S, W.card = a ∧ a * (∑ v ∈ S, f v) ≤ S.card * (∑ v ∈ W, f v) := by
  let P_a := S.powersetCard a
  have hPa_ne : P_a.Nonempty := by
    obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq ha_le
    exact ⟨W, Finset.mem_powersetCard.mpr ⟨hW, hWc⟩⟩
  have hdouble : ∑ W ∈ P_a, (∑ v ∈ W, f v) = (S.card - 1).choose (a - 1) * (∑ v ∈ S, f v) := by
    have h1 : ∑ W ∈ P_a, (∑ v ∈ W, f v) = ∑ v ∈ S, ((P_a.filter fun W => v ∈ W).card * f v) := by
      calc ∑ W ∈ P_a, (∑ v ∈ W, f v)
          = ∑ W ∈ P_a, ∑ v ∈ S, (if v ∈ W then f v else 0) := by
            apply Finset.sum_congr rfl; intro W hW
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
              Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hW).1]
        _ = ∑ v ∈ S, ∑ W ∈ P_a, (if v ∈ W then f v else 0) := Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro v _
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hcnt : ∀ v ∈ S, (P_a.filter fun W => v ∈ W).card = (S.card - 1).choose (a - 1) := by
      intro v hv
      have heq : P_a.filter (fun W => v ∈ W) = ((S.erase v).powersetCard (a - 1)).image (insert v) := by
        ext W
        simp only [Finset.mem_filter, P_a, Finset.mem_powersetCard, Finset.mem_image]
        constructor
        · rintro ⟨⟨hWsub, hWc⟩, hvW⟩
          refine ⟨W.erase v, ⟨Finset.erase_subset_erase v hWsub, ?_⟩, Finset.insert_erase hvW⟩
          rw [Finset.card_erase_of_mem hvW, hWc]
        · rintro ⟨U, ⟨hUsub, hUc⟩, rfl⟩
          have hvU : v ∉ U := fun h => (Finset.mem_erase.mp (hUsub h)).1 rfl
          refine ⟨⟨Finset.insert_subset hv (hUsub.trans (Finset.erase_subset _ _)), ?_⟩,
            Finset.mem_insert_self v U⟩
          rw [Finset.card_insert_of_notMem hvU, hUc]; omega
      rw [heq, Finset.card_image_of_injOn, Finset.card_powersetCard, Finset.card_erase_of_mem hv]
      intro U₁ hU₁ U₂ hU₂ hEq
      have hv1 : v ∉ U₁ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hU₁).1 h)).1 rfl
      have hv2 : v ∉ U₂ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hU₂).1 h)).1 rfl
      have := congrArg (fun X => X.erase v) hEq
      simpa [Finset.erase_insert hv1, Finset.erase_insert hv2] using this
    rw [h1]
    calc ∑ v ∈ S, (P_a.filter fun W => v ∈ W).card * f v
        = ∑ v ∈ S, (S.card - 1).choose (a - 1) * f v := Finset.sum_congr rfl fun v hv => by rw [hcnt v hv]
      _ = (S.card - 1).choose (a - 1) * ∑ v ∈ S, f v := by rw [← Finset.mul_sum]
  obtain ⟨W, hWP, hWmax⟩ := Finset.exists_max_image P_a (fun W => ∑ v ∈ W, f v) hPa_ne
  have hsum_le : ∑ W' ∈ P_a, (∑ v ∈ W', f v) ≤ P_a.card * (∑ v ∈ W, f v) := by
    calc ∑ W' ∈ P_a, (∑ v ∈ W', f v)
        ≤ ∑ _W' ∈ P_a, (∑ v ∈ W, f v) := Finset.sum_le_sum hWmax
      _ = _ := by simp
  rw [hdouble, Finset.card_powersetCard] at hsum_le
  have hcho : S.card * (S.card - 1).choose (a - 1) = a * S.card.choose a := by
    have hstep : ∀ n k : ℕ, (n + 1) * n.choose k = (k + 1) * (n + 1).choose (k + 1) := by
      intro n
      induction n with
      | zero =>
        intro k
        cases k with
        | zero => simp
        | succ k => simp [Nat.choose_eq_zero_of_lt]
      | succ n ih =>
        intro k
        cases k with
        | zero => simp
        | succ k =>
          have h3 := Nat.choose_succ_succ n k
          rw [Nat.choose_succ_succ (n + 1) (k + 1)]
          have h1 := ih (k + 1)
          have h2 := ih k
          nlinarith
    have h1 := hstep (S.card - 1) (a - 1)
    have hvs : S.card - 1 + 1 = S.card := by omega
    have ha1 : a - 1 + 1 = a := by omega
    rwa [hvs, ha1] at h1
  have hcho_pos : 0 < S.card.choose a := Nat.choose_pos ha_le
  have hmul : S.card.choose a * (a * ∑ v ∈ S, f v) ≤ S.card.choose a * (S.card * ∑ v ∈ W, f v) := by
    calc S.card.choose a * (a * ∑ v ∈ S, f v)
        = (a * S.card.choose a) * ∑ v ∈ S, f v := by ring
      _ = S.card * ((S.card - 1).choose (a - 1) * ∑ v ∈ S, f v) := by rw [← hcho]; ring
      _ ≤ S.card * (S.card.choose a * ∑ v ∈ W, f v) := Nat.mul_le_mul_left _ hsum_le
      _ = _ := by ring
  exact ⟨W, (Finset.mem_powersetCard.mp hWP).1, (Finset.mem_powersetCard.mp hWP).2,
    Nat.le_of_mul_le_mul_left hmul hcho_pos⟩

/-- Deterministic minimal-subgraph regularization: from `e(G) ≥ C * |V|^(1 + α)` (`0 < α < 1`),
we extract a nonempty induced subgraph `H` on `m` vertices with `m ≥ (1/2) * (2C)^(1/(1-α))`,
average degree `d ≥ C * m^α`, and maximum degree `≤ 2 K₀ * d`. -/
private theorem exists_regularized_subgraph {V : Type} [Fintype V]
    (G : SimpleGraph V) {α C : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hC : 1 ≤ C)
    (hG : C * (Fintype.card V : ℝ) ^ (1 + α) ≤ (G.edgeFinset.card : ℝ)) (hV_ne : Nonempty V) :
    let K₀ : ℕ := ⌈(32 : ℝ) ^ (1 / α)⌉₊ + 3
    ∃ S : Finset V, S.Nonempty ∧
      (2 * C) ^ (1 / (1 - α)) ≤ 2 * (S.card : ℝ) ∧
      let H := G.induce (S : Set V)
      let d : ℝ := 2 * (H.edgeFinset.card : ℝ) / (S.card : ℝ)
      C * (S.card : ℝ) ^ α ≤ d ∧
      ∀ v : (S : Set V), (H.degree v : ℝ) ≤ (2 * (K₀ : ℝ)) * d := by
  let K₀ : ℕ := ⌈(32 : ℝ) ^ (1 / α)⌉₊ + 3
  have hK₀_ge3 : 3 ≤ K₀ := by omega
  have hK₀_pow : (32 : ℝ) ≤ (K₀ : ℝ) ^ α := by
    have h1 : (32 : ℝ) ^ (1 / α) ≤ (K₀ : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(32 : ℝ) ^ (1 / α)⌉₊ ≤ K₀ by omega))
    have h2 := Real.rpow_le_rpow (by positivity) h1 hα0.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32), one_div_mul_cancel hα0.ne', Real.rpow_one] at h2
    exact h2
  -- Choose `S₀ ⊆ univ` nonempty with `C * |S₀|^(1+α) ≤ e(G[S₀])` of MINIMUM cardinality!
  let P (n : ℕ) : Prop := ∃ S : Finset V, S.card = n ∧ S.Nonempty ∧
    C * (S.card : ℝ) ^ (1 + α) ≤ (inducedEdgeCount G S : ℝ)
  have hP_ex : ∃ n, P n := by
    refine ⟨Fintype.card V, Finset.univ, Finset.card_univ, Finset.univ_nonempty, ?_⟩
    have heq : inducedEdgeCount G Finset.univ = G.edgeFinset.card := by
      have h2 := two_mul_inducedEdgeCount G Finset.univ
      have hG2 := G.sum_degrees_eq_twice_card_edges
      have hsum : ∑ v ∈ (Finset.univ : Finset V), (Finset.univ.filter (G.Adj v)).card =
          ∑ v : V, G.degree v := by
        apply Finset.sum_congr rfl; intro v _
        rw [← card_neighborFinset_eq_degree]; congr 1; ext w; simp
      omega
    rw [heq, Finset.card_univ]; exact hG
  let m := Nat.find hP_ex
  obtain ⟨S, hSm, hSne, hSe⟩ := Nat.find_spec hP_ex
  have hmin : ∀ T : Finset V, T.Nonempty → T.card < m →
      (inducedEdgeCount G T : ℝ) < C * (T.card : ℝ) ^ (1 + α) := by
    intro T hTne hTlt
    by_contra hge
    push Not at hge
    exact Nat.find_min hP_ex hTlt ⟨T, rfl, hTne, hge⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (hSm ▸ hSne.card_pos)
  have hSe' : C * (m : ℝ) ^ (1 + α) ≤ (inducedEdgeCount G S : ℝ) := by rwa [hSm] at hSe
  -- Lower bound on `m`: `2 C ≤ m^(1 - α)`.
  have hm_lb : (2 * C) ^ (1 / (1 - α)) ≤ (m : ℝ) := by
    have hsq : 2 * (inducedEdgeCount G S : ℝ) ≤ (m : ℝ) * (m : ℝ) := by
      have := inducedEdgeCount_le_sq_div_two G S
      rw [hSm] at this; exact_mod_cast this
    have h1 : 2 * C * (m : ℝ) ^ (1 + α) ≤ (m : ℝ) ^ (2 : ℝ) := by
      calc 2 * C * (m : ℝ) ^ (1 + α) ≤ 2 * (inducedEdgeCount G S : ℝ) := by linarith
        _ ≤ (m : ℝ) * (m : ℝ) := hsq
        _ = (m : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
    have h2 : 2 * C ≤ (m : ℝ) ^ (1 - α) := by
      have hpos : (0 : ℝ) < (m : ℝ) ^ (1 + α) := Real.rpow_pos_of_pos hm_pos _
      have hadd : (1 - α) + (1 + α) = (2 : ℝ) := by ring
      have hmul : (m : ℝ) ^ (1 - α) * (m : ℝ) ^ (1 + α) = (m : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hm_pos, hadd]
      exact le_of_mul_le_mul_right (h1.trans_eq hmul.symm) hpos
    have h3 := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ 1 / (1 - α))
    rw [← Real.rpow_mul hm_pos.le, mul_one_div_cancel (by linarith : 1 - α ≠ 0), Real.rpow_one] at h3
    exact h3
  -- Split `S` into `V_big` (`deg_S(v) > K₀ * d_S`) and `V_small = S \ V_big`.
  let dS : ℝ := 2 * (inducedEdgeCount G S : ℝ) / (m : ℝ)
  have hdS_pos : 0 < dS := by
    dsimp [dS]
    have : 0 < C * (m : ℝ) ^ (1 + α) := mul_pos (by linarith) (Real.rpow_pos_of_pos hm_pos _)
    exact div_pos (by linarith) hm_pos
  let V_big := S.filter fun v => (K₀ : ℝ) * dS < ((S.filter (G.Adj v)).card : ℝ)
  let V_small := S \ V_big
  let a := V_big.card
  have ha_lt : (a : ℝ) * (K₀ : ℝ) < (m : ℝ) := by
    have hsum1 : (a : ℝ) * ((K₀ : ℝ) * dS) ≤
        ∑ v ∈ V_big, ((S.filter (G.Adj v)).card : ℝ) := by
      calc (a : ℝ) * ((K₀ : ℝ) * dS)
          = ∑ _v ∈ V_big, (K₀ : ℝ) * dS := by simp [a]
        _ ≤ ∑ v ∈ V_big, ((S.filter (G.Adj v)).card : ℝ) :=
            Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2.le
    have hsum2 : ∑ v ∈ V_big, ((S.filter (G.Adj v)).card : ℝ) ≤ (m : ℝ) * dS := by
      have h1 : ∑ v ∈ V_big, (S.filter (G.Adj v)).card ≤ ∑ v ∈ S, (S.filter (G.Adj v)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h2 : (∑ v ∈ S, ((S.filter (G.Adj v)).card : ℝ)) = 2 * (inducedEdgeCount G S : ℝ) := by
        exact_mod_cast (two_mul_inducedEdgeCount G S).symm
      have h3 : 2 * (inducedEdgeCount G S : ℝ) = (m : ℝ) * dS := by
        dsimp [dS]; field_simp [hm_pos.ne']
      exact (by exact_mod_cast h1 : _ ≤ _).trans (h2.trans h3).le
    by_cases ha0 : a = 0
    · simp [ha0, hm_pos]
    · have hstrict : (a : ℝ) * ((K₀ : ℝ) * dS) < ∑ v ∈ V_big, ((S.filter (G.Adj v)).card : ℝ) := by
        have hne : V_big.Nonempty := Finset.card_pos.mp (by omega)
        calc (a : ℝ) * ((K₀ : ℝ) * dS)
            = ∑ _v ∈ V_big, (K₀ : ℝ) * dS := by simp [a]
          _ < ∑ v ∈ V_big, ((S.filter (G.Adj v)).card : ℝ) :=
              Finset.sum_lt_sum_of_nonempty hne fun v hv => (Finset.mem_filter.mp hv).2
      have hlt := hstrict.trans_le hsum2
      have : ((a : ℝ) * (K₀ : ℝ)) * dS < (m : ℝ) * dS := by linarith
      exact lt_of_mul_lt_mul_right this hdS_pos.le
  have ha_nat_lt : a * K₀ < m := by exact_mod_cast ha_lt
  have h2a_lt : 2 * a < m := by nlinarith
  have hVsmall_card : V_small.card = m - a := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hSm]
  -- Count edges inside `V_big` and between `V_big` and `V_small`:
  let crossCount := ∑ v ∈ V_small, (V_big.filter (G.Adj v)).card
  have hedge_decomp : 2 * inducedEdgeCount G S =
      2 * inducedEdgeCount G V_big + 2 * crossCount + 2 * inducedEdgeCount G V_small := by
    rw [two_mul_inducedEdgeCount, two_mul_inducedEdgeCount, two_mul_inducedEdgeCount]
    have hsplit : ∀ v : V, (S.filter (G.Adj v)).card =
        (V_big.filter (G.Adj v)).card + (V_small.filter (G.Adj v)).card := by
      intro v
      have hu : S = V_big ∪ V_small := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
      have hd : Disjoint V_big V_small := Finset.disjoint_sdiff
      rw [hu, Finset.filter_union, Finset.card_union_of_disjoint
        (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hSsplit : ∑ v ∈ S, (S.filter (G.Adj v)).card =
        (∑ v ∈ V_big, (S.filter (G.Adj v)).card) + ∑ v ∈ V_small, (S.filter (G.Adj v)).card := by
      have hu : S = V_big ∪ V_small := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
      rw [hu, Finset.sum_union Finset.disjoint_sdiff]
    have hsym : ∑ v ∈ V_big, (V_small.filter (G.Adj v)).card = crossCount := by
      dsimp [crossCount]
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        by_cases h : G.Adj v u
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [hSsplit]
    simp only [hsplit, Finset.sum_add_distrib, hsym]
    ring
  -- Claim 1: `e(V_big) < (1/4) * e(S)`.
  have hbig_lt : (inducedEdgeCount G V_big : ℝ) < (inducedEdgeCount G S : ℝ) / 4 := by
    by_cases ha0 : a = 0
    · have hEmp : V_big = ∅ := Finset.card_eq_zero.mp ha0
      have h0 : inducedEdgeCount G V_big = 0 := by
        rw [hEmp]; have := two_mul_inducedEdgeCount G ∅; simp at this; exact this
      rw [h0, Nat.cast_zero]
      have : 0 < C * (m : ℝ) ^ (1 + α) := mul_pos (by linarith) (Real.rpow_pos_of_pos hm_pos _)
      linarith
    · have hne : V_big.Nonempty := Finset.card_pos.mp (by omega)
      have hlt := hmin V_big hne (by omega)
      have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
      have hK_ge4 : (4 : ℝ) ≤ (K₀ : ℝ) ^ (1 + α) := by
        calc (4 : ℝ) ≤ 32 := by norm_num
          _ ≤ (K₀ : ℝ) ^ α := hK₀_pow
          _ ≤ (K₀ : ℝ) ^ (1 + α) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ K₀ by omega)) (by linarith)
      have hKm : ((K₀ : ℝ) * (a : ℝ)) ^ (1 + α) ≤ (m : ℝ) ^ (1 + α) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      rw [Real.mul_rpow (by positivity) ha_pos.le] at hKm
      have h1 : 4 * C * (a : ℝ) ^ (1 + α) ≤ C * (m : ℝ) ^ (1 + α) := by
        calc 4 * C * (a : ℝ) ^ (1 + α)
            ≤ C * ((K₀ : ℝ) ^ (1 + α) * (a : ℝ) ^ (1 + α)) := by nlinarith [Real.rpow_nonneg ha_pos.le (1 + α)]
          _ ≤ C * (m : ℝ) ^ (1 + α) := mul_le_mul_of_nonneg_left hKm (by linarith)
      linarith
  -- Claim 2: `crossCount < (1/4) * e(S)`.
  have hcross_lt : (crossCount : ℝ) < (inducedEdgeCount G S : ℝ) / 4 := by
    by_cases ha0 : a = 0
    · have hEmp : V_big = ∅ := Finset.card_eq_zero.mp ha0
      have hc0 : crossCount = 0 := by simp [crossCount, hEmp]
      rw [hc0, Nat.cast_zero]
      have : 0 < C * (m : ℝ) ^ (1 + α) := mul_pos (by linarith) (Real.rpow_pos_of_pos hm_pos _)
      linarith
    · by_contra hge
      push Not at hge
      have ha_pos : 0 < a := by omega
      have ha_le_small : a ≤ V_small.card := by omega
      -- Choose `W ⊆ V_small` of size `a` maximizing `∑ v ∈ W, deg(v, V_big)`.
      let degB (v : V) : ℕ := (V_big.filter (G.Adj v)).card
      obtain ⟨W, hWsub, hWc, hWavg⟩ := exists_heavy_subset_card_eq V_small a ha_pos ha_le_small degB
      let T := V_big ∪ W
      have hdisj : Disjoint V_big W := Finset.disjoint_sdiff.mono_right hWsub
      have hTcard : T.card = 2 * a := by
        rw [Finset.card_union_of_disjoint hdisj, hWc]; dsimp [a]; omega
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hTe_ge : ∑ v ∈ W, degB v ≤ inducedEdgeCount G T := by
        have h2 := two_mul_inducedEdgeCount G T
        have hsplit : ∑ v ∈ T, (T.filter (G.Adj v)).card =
            (∑ v ∈ V_big, (T.filter (G.Adj v)).card) + ∑ v ∈ W, (T.filter (G.Adj v)).card :=
          Finset.sum_union hdisj
        have h1 : ∑ v ∈ W, degB v ≤ ∑ v ∈ W, (T.filter (G.Adj v)).card :=
          Finset.sum_le_sum fun v _ => Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
        have h2' : ∑ v ∈ W, degB v ≤ ∑ v ∈ V_big, (T.filter (G.Adj v)).card := by
          have hsym : ∑ v ∈ W, degB v = ∑ u ∈ V_big, (W.filter (G.Adj u)).card := by
            simp only [degB, Finset.card_filter]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
              by_cases h : G.Adj v u
              · rw [if_pos h, if_pos h.symm]
              · rw [if_neg h, if_neg (fun h' => h h'.symm)]
          rw [hsym]
          exact Finset.sum_le_sum fun u _ =>
            Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
        omega
      -- Now contradict minimality of `m`:
      have hltT := hmin T hTne (by omega)
      have ha_posR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
      have hVsmall_le : (V_small.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show V_small.card ≤ m by omega)
      have hWavgR : (a : ℝ) * (crossCount : ℝ) ≤ (m : ℝ) * (inducedEdgeCount G T : ℝ) := by
        have h1 : (a : ℝ) * (crossCount : ℝ) ≤ (V_small.card : ℝ) * ((∑ v ∈ W, degB v : ℕ) : ℝ) := by
          exact_mod_cast hWavg
        have h2 : ((∑ v ∈ W, degB v : ℕ) : ℝ) ≤ (inducedEdgeCount G T : ℝ) := by exact_mod_cast hTe_ge
        calc (a : ℝ) * (crossCount : ℝ)
            ≤ (V_small.card : ℝ) * ((∑ v ∈ W, degB v : ℕ) : ℝ) := h1
          _ ≤ (m : ℝ) * (inducedEdgeCount G T : ℝ) :=
              mul_le_mul hVsmall_le h2 (Nat.cast_nonneg _) hm_pos.le
      have h2pow : (2 : ℝ) ^ (1 + α) ≤ 4 := by
        calc (2 : ℝ) ^ (1 + α) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hKm : (K₀ : ℝ) ^ α * (a : ℝ) ^ α ≤ (m : ℝ) ^ α := by
        rw [← Real.mul_rpow (by positivity) ha_posR.le]
        exact Real.rpow_le_rpow (by positivity) (by linarith) hα0.le
      have hCT : C * ((2 * a : ℕ) : ℝ) ^ (1 + α) ≤ (inducedEdgeCount G T : ℝ) := by
        have hLHS : (m : ℝ) * (C * ((2 * a : ℕ) : ℝ) ^ (1 + α)) ≤ (a : ℝ) * (crossCount : ℝ) := by
          have h2a : ((2 * a : ℕ) : ℝ) ^ (1 + α) = (2 : ℝ) ^ (1 + α) * (a : ℝ) ^ (1 + α) := by
            push_cast; rw [Real.mul_rpow (by norm_num) ha_posR.le]
          have hpowA : (a : ℝ) ^ (1 + α) = (a : ℝ) * (a : ℝ) ^ α := by
            rw [Real.rpow_add ha_posR, Real.rpow_one]
          have hpowM : (m : ℝ) ^ (1 + α) = (m : ℝ) * (m : ℝ) ^ α := by
            rw [Real.rpow_add hm_pos, Real.rpow_one]
          have h16 : (16 : ℝ) * (a : ℝ) ^ α ≤ (m : ℝ) ^ α := by
            calc (16 : ℝ) * (a : ℝ) ^ α ≤ 32 * (a : ℝ) ^ α := by
                  nlinarith [Real.rpow_nonneg ha_posR.le α]
              _ ≤ (K₀ : ℝ) ^ α * (a : ℝ) ^ α :=
                  mul_le_mul_of_nonneg_right hK₀_pow (Real.rpow_nonneg ha_posR.le α)
              _ ≤ (m : ℝ) ^ α := hKm
          rw [h2a, hpowA]
          calc (m : ℝ) * (C * ((2 : ℝ) ^ (1 + α) * ((a : ℝ) * (a : ℝ) ^ α)))
              ≤ (m : ℝ) * (C * (4 * ((a : ℝ) * (a : ℝ) ^ α))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right h2pow (mul_nonneg ha_posR.le (Real.rpow_nonneg ha_posR.le α)))
                  (by linarith)) hm_pos.le
            _ = (a : ℝ) * (C * (m : ℝ) * (16 * (a : ℝ) ^ α) / 4) := by ring
            _ ≤ (a : ℝ) * (C * (m : ℝ) * (m : ℝ) ^ α / 4) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h16 (mul_nonneg (by linarith) hm_pos.le)) (by norm_num)) ha_posR.le
            _ = (a : ℝ) * (C * (m : ℝ) ^ (1 + α) / 4) := by rw [hpowM]; ring
            _ ≤ (a : ℝ) * ((inducedEdgeCount G S : ℝ) / 4) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSe' (by norm_num)) ha_posR.le
            _ ≤ (a : ℝ) * (crossCount : ℝ) := mul_le_mul_of_nonneg_left hge ha_posR.le
        have : (m : ℝ) * (C * ((2 * a : ℕ) : ℝ) ^ (1 + α)) ≤ (m : ℝ) * (inducedEdgeCount G T : ℝ) :=
          hLHS.trans hWavgR
        exact le_of_mul_le_mul_left this hm_pos
      rw [hTcard] at hltT
      linarith
  -- Therefore `e(V_small) > (1/2) * e(S)`!
  have hsmall_gt : (inducedEdgeCount G S : ℝ) / 2 < (inducedEdgeCount G V_small : ℝ) := by
    have hdecR : 2 * (inducedEdgeCount G S : ℝ) =
        2 * (inducedEdgeCount G V_big : ℝ) + 2 * (crossCount : ℝ) + 2 * (inducedEdgeCount G V_small : ℝ) := by
      exact_mod_cast hedge_decomp
    linarith
  have hVsmall_ne : V_small.Nonempty := Finset.card_pos.mp (by omega)
  have hm'_pos : (0 : ℝ) < (V_small.card : ℝ) := by exact_mod_cast hVsmall_ne.card_pos
  have h2m' : (m : ℝ) ≤ 2 * (V_small.card : ℝ) := by
    have : m ≤ 2 * V_small.card := by omega
    exact_mod_cast this
  refine ⟨V_small, hVsmall_ne, hm_lb.trans h2m', ?_, ?_⟩
  · -- Average degree `d' ≥ C * (V_small.card)^α`:
    have hm'_le : (V_small.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show V_small.card ≤ m by omega)
    have hpowM : (m : ℝ) ^ (1 + α) = (m : ℝ) * (m : ℝ) ^ α := by
      rw [Real.rpow_add hm_pos, Real.rpow_one]
    have hpow_le : (V_small.card : ℝ) ^ α ≤ (m : ℝ) ^ α :=
      Real.rpow_le_rpow hm'_pos.le hm'_le hα0.le
    rw [le_div_iff₀ hm'_pos]
    calc C * (V_small.card : ℝ) ^ α * (V_small.card : ℝ)
        ≤ C * (m : ℝ) ^ α * (m : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow_le (by linarith)) hm'_le hm'_pos.le
            (mul_nonneg (by linarith) (Real.rpow_nonneg hm_pos.le α))
      _ = C * (m : ℝ) ^ (1 + α) := by rw [hpowM]; ring
      _ ≤ (inducedEdgeCount G S : ℝ) := hSe'
      _ ≤ 2 * (inducedEdgeCount G V_small : ℝ) := by linarith
  · -- Maximum degree `≤ 2 K₀ * d'`:
    rintro ⟨v, hv⟩
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
    have hvNotBig : v ∉ V_big := (Finset.mem_sdiff.mp hv).2
    have hdeg_le_S : ((G.induce (V_small : Set V)).degree ⟨v, hv⟩ : ℝ) ≤
        ((S.filter (G.Adj v)).card : ℝ) := by
      rw [← card_neighborFinset_eq_degree]
      have hsub : ((G.induce (V_small : Set V)).neighborFinset ⟨v, hv⟩).image Subtype.val ⊆
          S.filter (G.Adj v) := by
        intro u hu
        obtain ⟨⟨w, hw⟩, hwN, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw).1,
          (mem_neighborFinset (G.induce (V_small : Set V)) _ _).mp hwN⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
      exact_mod_cast hcard
    have hnotgt : ((S.filter (G.Adj v)).card : ℝ) ≤ (K₀ : ℝ) * dS := by
      by_contra hgt
      push Not at hgt
      exact hvNotBig (Finset.mem_filter.mpr ⟨hvS, hgt⟩)
    have hdS_le : dS ≤ 2 * (2 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ)) := by
      dsimp [dS]
      have hm'_le : (V_small.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show V_small.card ≤ m by omega)
      rw [div_le_iff₀ hm_pos]
      have h1 : 2 * (inducedEdgeCount G S : ℝ) ≤ 4 * (inducedEdgeCount G V_small : ℝ) := by linarith
      have hnn_e : (0 : ℝ) ≤ 4 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hm'_pos.le
      calc 2 * (inducedEdgeCount G S : ℝ)
          ≤ 4 * (inducedEdgeCount G V_small : ℝ) := h1
        _ = (4 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ)) * (V_small.card : ℝ) := by
            field_simp [hm'_pos.ne']
        _ ≤ (4 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ)) * (m : ℝ) :=
            mul_le_mul_of_nonneg_left hm'_le hnn_e
        _ = 2 * (2 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ)) * (m : ℝ) := by ring
    calc ((G.induce (V_small : Set V)).degree ⟨v, hv⟩ : ℝ)
        ≤ ((S.filter (G.Adj v)).card : ℝ) := hdeg_le_S
      _ ≤ (K₀ : ℝ) * dS := hnotgt
      _ ≤ (K₀ : ℝ) * (2 * (2 * (inducedEdgeCount G V_small : ℝ) / (V_small.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hdS_le (Nat.cast_nonneg K₀)
      _ = 2 * (K₀ : ℝ) * (2 * ((G.induce (V_small : Set V)).edgeFinset.card : ℝ) / (V_small.card : ℝ)) := by
          dsimp [inducedEdgeCount]; ring

/-- Ordered 4-cycles `(a, b, c, d)` in `G` (four pairwise distinct vertices with `a~b~c~d~a`). -/
private noncomputable def orderedC4 {V : Type} [Fintype V] (G : SimpleGraph V) :
    Finset (V × V × V × V) :=
  (Finset.univ : Finset (V × V × V × V)).filter fun t =>
    let a := t.1; let b := t.2.1; let c := t.2.2.1; let d := t.2.2.2
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

private def c4HasEdge {V : Type} (e : Sym2 V) (t : V × V × V × V) : Prop :=
  e = s(t.1, t.2.1) ∨ e = s(t.2.1, t.2.2.1) ∨ e = s(t.2.2.1, t.2.2.2) ∨ e = s(t.2.2.2, t.1)

/-- Lemma 2.10: Every graph `G` on `m ≥ 2` vertices with `e(G) ≥ 4` has a spanning subgraph `F ≤ G`
with `e(F) ≥ e(G) / 2` in which every edge lies in at most `(20 * log m / e(F)) * |orderedC4 F|`
ordered 4-cycles. -/
private theorem exists_balanced_c4_spanning {V : Type} [Fintype V]
    (G : SimpleGraph V) (hm : 2 ≤ Fintype.card V) (he : 4 ≤ G.edgeFinset.card) :
    ∃ F : SimpleGraph V, F ≤ G ∧
      G.edgeFinset.card ≤ 2 * F.edgeFinset.card ∧
      ∀ e ∈ F.edgeFinset,
        (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
          (20 * Real.log (Fintype.card V : ℝ) / (F.edgeFinset.card : ℝ)) * ((orderedC4 F).card : ℝ) := by
  let m := Fintype.card V
  let e0 := G.edgeFinset.card
  let τ : ℝ := 20 * Real.log (m : ℝ) / (e0 : ℝ)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have he0_pos : (0 : ℝ) < (e0 : ℝ) := by exact_mod_cast (show 0 < e0 by omega)
  have hτ_pos : 0 < τ := div_pos (by positivity) he0_pos
  have hq0_le : ((orderedC4 G).card : ℝ) ≤ (m : ℝ) ^ (4 : ℕ) := by
    have h1 : (orderedC4 G).card ≤ Fintype.card (V × V × V × V) := Finset.card_le_univ _
    simp only [Fintype.card_prod] at h1
    have h2 : (orderedC4 G).card ≤ m ^ 4 := by
      calc (orderedC4 G).card ≤ m * (m * (m * m)) := h1
        _ = m ^ 4 := by ring
    exact_mod_cast h2
  -- Inductive deletion with the step-count invariant `4 * (e0 - r) ≤ e0 + 3` (`e0 ≤ 2 * r` for `e0 ≥ 4`):
  have hrec : ∀ (r : ℕ) (H : SimpleGraph V), H.edgeFinset.card = r → H ≤ G →
      4 * (e0 - r) ≤ e0 + 3 →
      ((orderedC4 H).card : ℝ) ≤ ((orderedC4 G).card : ℝ) * Real.exp (-τ * ((e0 - r : ℕ) : ℝ)) →
      ∃ F : SimpleGraph V, F ≤ G ∧
        e0 ≤ 2 * F.edgeFinset.card ∧
        ∀ e ∈ F.edgeFinset,
          (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
            (20 * Real.log (m : ℝ) / (F.edgeFinset.card : ℝ)) * ((orderedC4 F).card : ℝ) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro H hHr hHG hdiff hqbound
      have hr_le : r ≤ e0 := hHr ▸ Finset.card_le_card (edgeFinset_mono hHG)
      have he0_le2r : e0 ≤ 2 * r := by omega
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      by_cases hgood : ∀ e ∈ H.edgeFinset,
          (((orderedC4 H).filter (c4HasEdge e)).card : ℝ) ≤ τ * ((orderedC4 H).card : ℝ)
      · refine ⟨H, hHG, hHr ▸ he0_le2r, fun e heH => (hgood e heH).trans ?_⟩
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        dsimp [τ]
        rw [hHr]
        exact div_le_div_of_nonneg_left (by positivity) hr_pos (by exact_mod_cast hr_le)
      · push Not at hgood
        obtain ⟨e, heH, hhit⟩ := hgood
        -- Note `orderedC4 H` must be nonempty since `hhit` gives `> τ * card ≥ 0`!
        have hqH_pos : 0 < (orderedC4 H).card := by
          by_contra h0
          have h0' : (orderedC4 H).card = 0 := by omega
          have hsub : ((orderedC4 H).filter (c4HasEdge e)).card ≤ (orderedC4 H).card :=
            Finset.card_filter_le _ _
          have hf0 : ((orderedC4 H).filter (c4HasEdge e)).card = 0 := by omega
          rw [h0', hf0, Nat.cast_zero, mul_zero] at hhit
          exact lt_irrefl _ hhit
        -- Also `4 * (e0 - r) < e0` because otherwise `(e0 - r) ≥ e0 / 4`, giving `qH < 1`!
        have hdiff_lt : 4 * (e0 - r) < e0 := by
          by_contra hge
          push Not at hge
          have hgeR : (e0 : ℝ) ≤ 4 * ((e0 - r : ℕ) : ℝ) := by exact_mod_cast hge
          have hexp : -τ * ((e0 - r : ℕ) : ℝ) ≤ -5 * Real.log (m : ℝ) := by
            dsimp [τ]
            have hmul : 20 * Real.log (m : ℝ) / (e0 : ℝ) * ((e0 - r : ℕ) : ℝ) ≥ 5 * Real.log (m : ℝ) := by
              rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ he0_pos]
              nlinarith
            linarith
          have hq1 : ((orderedC4 H).card : ℝ) < 1 := by
            calc ((orderedC4 H).card : ℝ)
                ≤ ((orderedC4 G).card : ℝ) * Real.exp (-τ * ((e0 - r : ℕ) : ℝ)) := hqbound
              _ ≤ (m : ℝ) ^ (4 : ℕ) * Real.exp (-5 * Real.log (m : ℝ)) :=
                  mul_le_mul hq0_le (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
              _ = (m : ℝ) ^ (4 : ℕ) * ((m : ℝ) ^ (5 : ℕ))⁻¹ := by
                  rw [neg_mul, Real.exp_neg, show (5 : ℝ) * Real.log (m : ℝ) = ((5 : ℕ) : ℝ) * Real.log (m : ℝ) by norm_num,
                    Real.exp_nat_mul, Real.exp_log hm_pos]
              _ = (m : ℝ)⁻¹ := by
                  field_simp [hm_pos.ne']
              _ < 1 := by
                  rw [inv_lt_one_iff₀]; right; exact_mod_cast (show 1 < m by omega)
          have hq1' : (1 : ℝ) ≤ ((orderedC4 H).card : ℝ) := by exact_mod_cast hqH_pos
          linarith
        -- Delete edge `e` from `H` to get `H'`:
        let H' : SimpleGraph V := H.deleteEdges {e}
        have hH'_le : H' ≤ H := SimpleGraph.deleteEdges_le _
        have hH'_edges : H'.edgeFinset = H.edgeFinset.erase e := by
          ext e'
          simp only [H', mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_erase, and_comm]
        have hH'_card : H'.edgeFinset.card = r - 1 := by
          rw [hH'_edges, Finset.card_erase_of_mem heH, hHr]
        have hC4_sub : orderedC4 H' ⊆ (orderedC4 H) \ ((orderedC4 H).filter (c4HasEdge e)) := by
          intro t ht
          have ht' : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
              t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2 ∧
              H'.Adj t.1 t.2.1 ∧ H'.Adj t.2.1 t.2.2.1 ∧ H'.Adj t.2.2.1 t.2.2.2 ∧ H'.Adj t.2.2.2 t.1 := by
            simpa only [orderedC4, Finset.mem_filter, Finset.mem_univ, true_and] using ht
          have htH : t ∈ orderedC4 H :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1,
              ht'.2.2.2.2.1, ht'.2.2.2.2.2.1,
              hH'_le ht'.2.2.2.2.2.2.1, hH'_le ht'.2.2.2.2.2.2.2.1,
              hH'_le ht'.2.2.2.2.2.2.2.2.1, hH'_le ht'.2.2.2.2.2.2.2.2.2⟩
          refine Finset.mem_sdiff.mpr ⟨htH, fun hmem => ?_⟩
          have heT := (Finset.mem_filter.mp hmem).2
          have hnot : ∀ u v, H'.Adj u v → s(u, v) ≠ e := fun u v huv =>
            (SimpleGraph.deleteEdges_adj.mp huv).2
          rcases heT with h1 | h2 | h3 | h4
          · exact hnot _ _ ht'.2.2.2.2.2.2.1 h1.symm
          · exact hnot _ _ ht'.2.2.2.2.2.2.2.1 h2.symm
          · exact hnot _ _ ht'.2.2.2.2.2.2.2.2.1 h3.symm
          · exact hnot _ _ ht'.2.2.2.2.2.2.2.2.2 h4.symm
        have hqH'_le : ((orderedC4 H').card : ℝ) ≤ (1 - τ) * ((orderedC4 H).card : ℝ) := by
          have hc1 : (orderedC4 H').card ≤
              (orderedC4 H).card - ((orderedC4 H).filter (c4HasEdge e)).card := by
            simpa only [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] using
              Finset.card_le_card hC4_sub
          have hc2 : ((orderedC4 H').card : ℝ) ≤
              ((orderedC4 H).card : ℝ) - (((orderedC4 H).filter (c4HasEdge e)).card : ℝ) := by
            have := Nat.cast_le (α := ℝ).mpr hc1
            rwa [Nat.cast_sub (Finset.card_filter_le _ _)] at this
          linarith
        have hqH'_exp : ((orderedC4 H').card : ℝ) ≤
            ((orderedC4 G).card : ℝ) * Real.exp (-τ * ((e0 - (r - 1) : ℕ) : ℝ)) := by
          have hstep_sub : ((e0 - (r - 1) : ℕ) : ℝ) = ((e0 - r : ℕ) : ℝ) + 1 := by
            have hr1 : 1 ≤ r := by omega
            have : e0 - (r - 1) = (e0 - r) + 1 := by omega
            rw [this, Nat.cast_add, Nat.cast_one]
          rw [hstep_sub]
          have h1e : 1 - τ ≤ Real.exp (-τ) := by
            simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-τ)
          calc ((orderedC4 H').card : ℝ)
              ≤ (1 - τ) * ((orderedC4 H).card : ℝ) := hqH'_le
            _ ≤ Real.exp (-τ) * ((orderedC4 H).card : ℝ) :=
                mul_le_mul_of_nonneg_right h1e (Nat.cast_nonneg _)
            _ ≤ Real.exp (-τ) * (((orderedC4 G).card : ℝ) * Real.exp (-τ * ((e0 - r : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left hqbound (Real.exp_pos _).le
            _ = ((orderedC4 G).card : ℝ) * Real.exp (-τ * (((e0 - r : ℕ) : ℝ) + 1)) := by
                rw [mul_add, mul_one, Real.exp_add]; ring
        exact ih (r - 1) (by omega) H' (by convert hH'_card) (hH'_le.trans hHG) (by omega) (by convert hqH'_exp)
  exact hrec e0 G rfl le_rfl (by omega) (by simp)

/- ### Section 4: Adjacency Matrix Walk and Cycle Bounds -/

private noncomputable def adjMat {V : Type} (G : SimpleGraph V) : Matrix V V ℝ :=
  fun u v => if G.Adj u v then 1 else 0

private lemma adjMat_nonneg {V : Type} (G : SimpleGraph V) (u v : V) : 0 ≤ adjMat G u v := by
  unfold adjMat; split_ifs <;> norm_num

private lemma adjMat_symm {V : Type} (G : SimpleGraph V) (u v : V) : adjMat G u v = adjMat G v u := by
  unfold adjMat
  by_cases h : G.Adj u v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

private lemma adjMat_row_sum {V : Type} [Fintype V] (G : SimpleGraph V) (u : V) :
    ∑ v : V, adjMat G u v = (G.degree u : ℝ) := by
  rw [← card_neighborFinset_eq_degree]
  simp only [adjMat, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext v
  simp [mem_neighborFinset]

private lemma adjMat_pow_symm {V : Type} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u v : V) :
    (adjMat G ^ r) u v = (adjMat G ^ r) v u := by
  have h := pow_detailedBalance (adjMat G) (fun _ => (1 : ℝ))
    (fun a b => by simp [adjMat_symm G a b]) r u v
  simp at h
  exact h

/-- General nonnegative log-convex interpolation: `(T j)^r ≤ (T 0)^(r - j) * (T r)^j` for `j ≤ r`. -/
private lemma logConvex_nonneg_interp (T : ℕ → ℝ) (hnn : ∀ i, 0 ≤ T i)
    (hcv : ∀ i, (T (i + 1)) ^ 2 ≤ T i * T (i + 2)) :
    ∀ (r j : ℕ), j ≤ r → (T j) ^ r ≤ (T 0) ^ (r - j) * (T r) ^ j := by
  have hstep : ∀ n : ℕ, (T n) ^ (n + 1) ≤ T 0 * (T (n + 1)) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      by_cases h0 : T (n + 1) = 0
      · rw [h0, zero_pow (by omega)]; exact mul_nonneg (hnn 0) (pow_nonneg (hnn _) _)
      · have hpos : 0 < (T (n + 1)) ^ n := pow_pos (lt_of_le_of_ne (hnn _) (Ne.symm h0)) n
        have h1 : ((T (n + 1)) ^ 2) ^ (n + 1) ≤ (T n * T (n + 2)) ^ (n + 1) :=
          pow_le_pow_left₀ (sq_nonneg _) (hcv n) (n + 1)
        have h2 : (T (n + 1)) ^ (n + 2) * (T (n + 1)) ^ n ≤
            (T 0 * (T (n + 2)) ^ (n + 1)) * (T (n + 1)) ^ n := by
          calc (T (n + 1)) ^ (n + 2) * (T (n + 1)) ^ n
              = ((T (n + 1)) ^ 2) ^ (n + 1) := by rw [← pow_add, ← pow_mul]; congr 1; omega
            _ ≤ (T n) ^ (n + 1) * (T (n + 2)) ^ (n + 1) := by rwa [mul_pow] at h1
            _ ≤ (T 0 * (T (n + 1)) ^ n) * (T (n + 2)) ^ (n + 1) :=
                mul_le_mul_of_nonneg_right ih (pow_nonneg (hnn _) _)
            _ = (T 0 * (T (n + 2)) ^ (n + 1)) * (T (n + 1)) ^ n := by ring
        exact le_of_mul_le_mul_right h2 hpos
  intro r
  induction r with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp
  | succ r ih =>
    intro j hj
    by_cases hje : j = r + 1
    · subst hje; simp
    · have hjr : j ≤ r := by omega
      cases r with
      | zero =>
        have hj0 : j = 0 := by omega
        subst hj0
        simp
      | succ r' =>
        have hih := ih j hjr
        have hpow : ((T j) ^ (r' + 2)) ^ (r' + 1) ≤
            ((T 0) ^ (r' + 2 - j) * (T (r' + 2)) ^ j) ^ (r' + 1) := by
          have hexp : (r' + 1 - j) * (r' + 2) + j = (r' + 2 - j) * (r' + 1) := by
            zify [hjr, show j ≤ r' + 2 by omega]; ring
          calc ((T j) ^ (r' + 2)) ^ (r' + 1)
              = ((T j) ^ (r' + 1)) ^ (r' + 2) := by rw [← pow_mul, ← pow_mul, mul_comm]
            _ ≤ ((T 0) ^ (r' + 1 - j) * (T (r' + 1)) ^ j) ^ (r' + 2) :=
                pow_le_pow_left₀ (pow_nonneg (hnn _) _) hih _
            _ = (T 0) ^ ((r' + 1 - j) * (r' + 2)) * ((T (r' + 1)) ^ (r' + 2)) ^ j := by
                rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm j (r' + 2)]
            _ ≤ (T 0) ^ ((r' + 1 - j) * (r' + 2)) * (T 0 * (T (r' + 2)) ^ (r' + 1)) ^ j :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg (hnn _) _) (hstep (r' + 1)) j)
                  (pow_nonneg (hnn 0) _)
            _ = (T 0) ^ ((r' + 1 - j) * (r' + 2) + j) * ((T (r' + 2)) ^ j) ^ (r' + 1) := by
                rw [mul_pow, ← mul_assoc, ← pow_add, ← pow_mul, ← pow_mul, mul_comm (r' + 1) j]
            _ = ((T 0) ^ (r' + 2 - j) * (T (r' + 2)) ^ j) ^ (r' + 1) := by
                rw [mul_pow, ← pow_mul, ← pow_mul, hexp]
        exact le_of_pow_le_pow_left₀ (by omega : r' + 1 ≠ 0)
          (mul_nonneg (pow_nonneg (hnn 0) _) (pow_nonneg (hnn _) _)) hpow

/-- Closed walks of length `L ≥ 2` equal `Tr(A^L)`. -/
private lemma hom_cycle_card_eq_trace {V : Type} [Fintype V]
    (G : SimpleGraph V) (L : ℕ) [NeZero L] (hL : 2 ≤ L) :
    ((Finset.univ.filter fun x : Fin L → V => ∀ i : Fin L, G.Adj (x i) (x (i + 1))).card : ℝ) =
      Matrix.trace (adjMat G ^ L) := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have hsum : ∑ x : Fin (m + 2) → V, (Classical.choose closedWeight_spec) (adjMat G) x =
      Matrix.trace (adjMat G ^ (m + 2)) := by
    let e : (Fin (m + 2) → V) ≃ V × (Fin (m + 1) → V) :=
      { toFun := fun x => (x 0, Fin.tail x)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun x => Fin.cons_self_tail x
        right_inv := fun ⟨a, w⟩ => Prod.ext rfl (by funext i; rfl) }
    calc ∑ x : Fin (m + 2) → V, (Classical.choose closedWeight_spec) (adjMat G) x
        = ∑ p : V × (Fin (m + 1) → V), (Classical.choose pathWeight_spec) (adjMat G) (m + 1) p.1 p.2 p.1 := by
          refine Fintype.sum_equiv e _ _ fun x => ?_
          rw [cw_eq]; rfl
      _ = ∑ a : V, ∑ w : Fin (m + 1) → V, (Classical.choose pathWeight_spec) (adjMat G) (m + 1) a w a :=
          Fintype.sum_prod_type _
      _ = ∑ a : V, (adjMat G ^ (m + 2)) a a := by
          exact Finset.sum_congr rfl fun a _ => sum_pathWeight_eq_pow (adjMat G) (m + 1) a a
      _ = Matrix.trace (adjMat G ^ (m + 2)) := rfl
  rw [← hsum, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [closedWeight_eq_prod]
  by_cases hx : ∀ i : Fin (m + 2), G.Adj (x i) (x (i + 1))
  · rw [if_pos hx, Nat.cast_one]
    exact (Finset.prod_eq_one fun i _ => if_pos (hx i)).symm
  · rw [if_neg hx, Nat.cast_zero]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- Trace log-convexity interpolation: `t_j ^ r ≤ |V| ^ (r - j) * t_r ^ j` for `j ≤ r`. -/
private lemma trace_even_interp {V : Type} [Fintype V]
    (G : SimpleGraph V) {j r : ℕ} (hjr : j ≤ r) :
    (Matrix.trace (adjMat G ^ (j + j))) ^ r ≤
      (Fintype.card V : ℝ) ^ (r - j) * (Matrix.trace (adjMat G ^ (r + r))) ^ j := by
  let t (i : ℕ) : ℝ := Matrix.trace (adjMat G ^ (i + i))
  have ht_nonneg : ∀ i, 0 ≤ t i := fun i => by
    dsimp [t]
    rw [trace_pow_split, Fintype.sum_prod_type]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    exact mul_nonneg (Matrix.pow_apply_nonneg (adjMat_nonneg G) _ _ _)
      (Matrix.pow_apply_nonneg (adjMat_nonneg G) _ _ _)
  have hconv : ∀ i, t (i + 1) ^ 2 ≤ t i * t (i + 2) := fun i =>
    even_trace_logConvex (adjMat G) (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
      (fun a b => by simp [adjMat_symm G a b]) i
  have h0 : t 0 = (Fintype.card V : ℝ) := by
    simp [t, Matrix.trace, Matrix.diag]
  have hint := logConvex_nonneg_interp t ht_nonneg hconv r j hjr
  simpa [t, h0] using hint

/-- Sidorenko's lower bound for even cycles (Lemma 2.6): `Tr(A^(2r)) ≥ (2 e(G) / |V|)^(2r)`. -/
private lemma trace_even_ge_avg_deg_pow {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (r : ℕ) :
    ((2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ (2 * r)) ≤
      Matrix.trace (adjMat G ^ (r + r)) := by
  let A := adjMat G
  have hAsym : ∀ a b : V, A a b = A b a := adjMat_symm G
  have hApow_sym : ∀ k (a b : V), (A ^ k) a b = (A ^ k) b a := adjMat_pow_symm G
  let n : ℝ := Fintype.card V
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let v (k : ℕ) (w : V) : ℝ := ∑ u : V, (A ^ k) u w
  let S (k : ℕ) : ℝ := ∑ w : V, (v k w) ^ 2
  have hS_nonneg : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun w _ => sq_nonneg _
  have hv_step : ∀ k w, v (k + 1) w = ∑ u : V, A w u * v k u := by
    intro k w
    dsimp [v]
    calc ∑ z : V, (A ^ (k + 1)) z w
        = ∑ z : V, ∑ u : V, (A ^ k) z u * A u w := by
          apply Finset.sum_congr rfl; intro z _
          rw [pow_succ, Matrix.mul_apply]
      _ = ∑ u : V, ∑ z : V, A w u * (A ^ k) z u := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun z _ => by
            rw [hAsym u w, mul_comm]
      _ = ∑ u : V, A w u * ∑ z : V, (A ^ k) z u := by
          exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
  have hS_conv : ∀ k : ℕ, (S (k + 1)) ^ 2 ≤ S k * S (k + 2) := by
    intro k
    have hinner : S (k + 1) = ∑ u : V, v k u * v (k + 2) u := by
      calc S (k + 1)
          = ∑ w : V, v (k + 1) w * v (k + 1) w := by
            exact Finset.sum_congr rfl fun w _ => sq _
        _ = ∑ w : V, (∑ u : V, A w u * v k u) * v (k + 1) w := by
            exact Finset.sum_congr rfl fun w _ => by rw [hv_step k w]
        _ = ∑ u : V, v k u * (∑ w : V, A u w * v (k + 1) w) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => by
              rw [hAsym w u]; ring
        _ = ∑ u : V, v k u * v (k + 2) u := by
            exact Finset.sum_congr rfl fun u _ => by rw [← hv_step (k + 1) u]
    rw [hinner]
    simpa [S] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) (v k) (v (k + 2))
  have hS0 : S 0 = n := by
    have hv0 : ∀ w : V, v 0 w = 1 := fun w => by
      simp [v, pow_zero, Matrix.one_apply]
    simp [S, hv0, n]
  have hS1 : (2 * (G.edgeFinset.card : ℝ)) ^ 2 ≤ n * S 1 := by
    have hv1 : ∀ w : V, v 1 w = (G.degree w : ℝ) := fun w => by
      dsimp [v]; rw [pow_one]
      calc ∑ u : V, A u w = ∑ u : V, A w u := Finset.sum_congr rfl fun u _ => hAsym u w
        _ = (G.degree w : ℝ) := adjMat_row_sum G w
    have hsumdeg : ∑ w : V, v 1 w = 2 * (G.edgeFinset.card : ℝ) := by
      simp only [hv1]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [← hsumdeg]
    simpa [S, n] using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := v 1)
  have hSr_le_trace : S r ≤ n * Matrix.trace (A ^ (r + r)) := by
    rw [trace_pow_split, Fintype.sum_prod_type]
    calc S r
        = ∑ w : V, (∑ u : V, (A ^ r) u w) ^ 2 := rfl
      _ ≤ ∑ w : V, n * ∑ u : V, ((A ^ r) u w) ^ 2 := by
          apply Finset.sum_le_sum; intro w _
          simpa [n] using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := fun u => (A ^ r) u w)
      _ = n * ∑ w : V, ∑ u : V, (A ^ r) u w * (A ^ r) w u := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => by
            rw [sq, hApow_sym r u w]
      _ = n * ∑ u : V, ∑ w : V, (A ^ r) u w * (A ^ r) w u := by rw [Finset.sum_comm]
  -- By log-convexity of `S`: for `r ≥ 1`, `S 1 ^ r ≤ S 0 ^ (r - 1) * S r`!
  cases r with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Matrix.trace, Matrix.diag]
    simpa using (Nat.cast_le (α := ℝ).mpr (show 1 ≤ Fintype.card V from Fintype.card_pos))
  | succ r' =>
    have hint := logConvex_nonneg_interp S hS_nonneg hS_conv (r' + 1) 1 (by omega)
    rw [pow_one, hS0] at hint
    have hpow1 : ((2 * (G.edgeFinset.card : ℝ)) ^ 2) ^ (r' + 1) ≤ (n * S 1) ^ (r' + 1) :=
      pow_le_pow_left₀ (sq_nonneg _) hS1 _
    rw [← pow_mul] at hpow1
    conv_rhs at hpow1 => rw [mul_pow]
    have hchain : (2 * (G.edgeFinset.card : ℝ)) ^ (2 * (r' + 1)) ≤
        n ^ (2 * (r' + 1)) * Matrix.trace (A ^ ((r' + 1) + (r' + 1))) := by
      calc (2 * (G.edgeFinset.card : ℝ)) ^ (2 * (r' + 1))
          ≤ n ^ (r' + 1) * S 1 ^ (r' + 1) := hpow1
        _ ≤ n ^ (r' + 1) * (n ^ (r' + 1 - 1) * S (r' + 1)) :=
            mul_le_mul_of_nonneg_left hint (pow_nonneg hn.le _)
        _ ≤ n ^ (r' + 1) * (n ^ r' * (n * Matrix.trace (A ^ ((r' + 1) + (r' + 1))))) := by
            have : r' + 1 - 1 = r' := by omega
            rw [this]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSr_le_trace (pow_nonneg hn.le _))
              (pow_nonneg hn.le _)
        _ = n ^ (2 * (r' + 1)) * Matrix.trace (A ^ ((r' + 1) + (r' + 1))) := by
            rw [show 2 * (r' + 1) = (r' + 1) + r' + 1 by omega, pow_add, pow_add, pow_one]; ring
    rw [div_pow, div_le_iff₀ (pow_pos hn _)]
    linarith

/-- Bipartite even-cycle lower bound (Lemma 2.4): if `X₁, X₂ ⊆ V` with `X₁.Nonempty`, every
`x ∈ X₁` has `≥ s` neighbors in `X₂`, and every `y ∈ X₂` has `≥ t` neighbors in `X₁`, then
`Tr(A^(2r)) ≥ s^r * t^r`. -/
private lemma bipartite_trace_even_ge {V : Type} [Fintype V]
    (G : SimpleGraph V) (X₁ X₂ : Finset V) (hX₁ : X₁.Nonempty) (s t : ℕ)
    (hs : ∀ x ∈ X₁, s ≤ (X₂.filter (G.Adj x)).card)
    (ht : ∀ y ∈ X₂, t ≤ (X₁.filter (G.Adj y)).card) (r : ℕ) :
    (s : ℝ) ^ r * (t : ℝ) ^ r ≤ Matrix.trace (adjMat G ^ (r + r)) := by
  let A := adjMat G
  have hApow_sym : ∀ k (a b : V), (A ^ k) a b = (A ^ k) b a := adjMat_pow_symm G
  -- Count walks of length `2r` starting in `X₁` and alternating `X₁ ↔ X₂`:
  have hwalk : ∀ m : ℕ,
      (∀ x ∈ X₁, (s : ℝ) ^ m * (t : ℝ) ^ m ≤ ∑ z ∈ X₁, (A ^ (m + m)) x z) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp only [pow_zero, mul_one, add_zero, Matrix.one_apply]
      rw [Finset.sum_ite_eq X₁ x (fun _ => (1 : ℝ)), if_pos hx]
    | succ m ih =>
      intro x hx
      have h1 : (s : ℝ) * ((t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m)) ≤
          ∑ y ∈ X₂, A x y * ∑ u ∈ X₁, A y u * ∑ z ∈ X₁, (A ^ (m + m)) u z := by
        calc (s : ℝ) * ((t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m))
            ≤ ((X₂.filter (G.Adj x)).card : ℝ) * ((t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m)) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hs x hx) (by positivity)
          _ = ∑ y ∈ X₂, A x y * ((t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m)) := by
              rw [← Finset.sum_mul]; congr 1
              rw [Finset.card_filter, Nat.cast_sum]
              exact Finset.sum_congr rfl fun y _ => by unfold A adjMat; split_ifs <;> simp
          _ ≤ ∑ y ∈ X₂, A x y * (∑ u ∈ X₁, A y u * ((s : ℝ) ^ m * (t : ℝ) ^ m)) := by
              apply Finset.sum_le_sum; intro y hy
              apply mul_le_mul_of_nonneg_left _ (adjMat_nonneg G x y)
              calc (t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m)
                  ≤ ((X₁.filter (G.Adj y)).card : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m) :=
                    mul_le_mul_of_nonneg_right (by exact_mod_cast ht y hy) (by positivity)
                _ = ∑ u ∈ X₁, A y u * ((s : ℝ) ^ m * (t : ℝ) ^ m) := by
                    rw [← Finset.sum_mul]; congr 1
                    rw [Finset.card_filter, Nat.cast_sum]
                    exact Finset.sum_congr rfl fun u _ => by unfold A adjMat; split_ifs <;> simp
          _ ≤ ∑ y ∈ X₂, A x y * ∑ u ∈ X₁, A y u * ∑ z ∈ X₁, (A ^ (m + m)) u z := by
              apply Finset.sum_le_sum; intro y _
              apply mul_le_mul_of_nonneg_left _ (adjMat_nonneg G x y)
              exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (ih u hu) (adjMat_nonneg G y u)
      have h2 : ∑ y ∈ X₂, A x y * ∑ u ∈ X₁, A y u * ∑ z ∈ X₁, (A ^ (m + m)) u z ≤
          ∑ z ∈ X₁, (A ^ ((m + 1) + (m + 1))) x z := by
        have hstep1 : ∀ y u z : V, 0 ≤ A x y * (A y u * (A ^ (m + m)) u z) := fun y u z =>
          mul_nonneg (adjMat_nonneg G x y) (mul_nonneg (adjMat_nonneg G y u)
            (Matrix.pow_apply_nonneg (adjMat_nonneg G) _ u z))
        calc ∑ y ∈ X₂, A x y * ∑ u ∈ X₁, A y u * ∑ z ∈ X₁, (A ^ (m + m)) u z
            = ∑ y ∈ X₂, ∑ u ∈ X₁, ∑ z ∈ X₁, A x y * (A y u * (A ^ (m + m)) u z) := by
              exact Finset.sum_congr rfl fun y _ => by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum, Finset.mul_sum]
          _ ≤ ∑ y : V, ∑ u : V, ∑ z ∈ X₁, A x y * (A y u * (A ^ (m + m)) u z) := by
              refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X₂)
                fun _ _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hstep1 _ _ _).trans ?_
              exact Finset.sum_le_sum fun y _ =>
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X₁)
                  fun _ _ _ => Finset.sum_nonneg fun _ _ => hstep1 _ _ _
          _ = ∑ z ∈ X₁, ∑ y : V, ∑ u : V, A x y * (A y u * (A ^ (m + m)) u z) := by
              rw [Finset.sum_comm]
              trans ∑ u : V, ∑ z ∈ X₁, ∑ y : V, A x y * (A y u * (A ^ (m + m)) u z)
              · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
              · rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
          _ = ∑ z ∈ X₁, (A ^ ((m + 1) + (m + 1))) x z := by
              apply Finset.sum_congr rfl; intro z _
              have hexp : (m + 1) + (m + 1) = 1 + (1 + (m + m)) := by omega
              rw [hexp, pow_add A 1 (1 + (m + m)), pow_add A 1 (m + m), pow_one, Matrix.mul_apply]
              apply Finset.sum_congr rfl; intro y _
              rw [Matrix.mul_apply, Finset.mul_sum]
      calc (s : ℝ) ^ (m + 1) * (t : ℝ) ^ (m + 1)
          = (s : ℝ) * ((t : ℝ) * ((s : ℝ) ^ m * (t : ℝ) ^ m)) := by rw [pow_succ, pow_succ]; ring
        _ ≤ _ := h1.trans h2
  -- Sum over `x ∈ X₁` and apply Cauchy–Schwarz!
  have hsum_lo : (X₁.card : ℝ) * ((s : ℝ) ^ r * (t : ℝ) ^ r) ≤
      ∑ x ∈ X₁, ∑ z ∈ X₁, (A ^ (r + r)) x z := by
    calc (X₁.card : ℝ) * ((s : ℝ) ^ r * (t : ℝ) ^ r)
        = ∑ _x ∈ X₁, ((s : ℝ) ^ r * (t : ℝ) ^ r) := by simp
      _ ≤ ∑ x ∈ X₁, ∑ z ∈ X₁, (A ^ (r + r)) x z := Finset.sum_le_sum (hwalk r)
  have hsum_hi : ∑ x ∈ X₁, ∑ z ∈ X₁, (A ^ (r + r)) x z ≤
      (X₁.card : ℝ) * Matrix.trace (A ^ (r + r)) := by
    calc ∑ x ∈ X₁, ∑ z ∈ X₁, (A ^ (r + r)) x z
        = ∑ w : V, (∑ x ∈ X₁, (A ^ r) x w) ^ 2 := by
          simp_rw [pow_add, Matrix.mul_apply]
          calc ∑ x ∈ X₁, ∑ z ∈ X₁, ∑ w : V, (A ^ r) x w * (A ^ r) w z
              = ∑ x ∈ X₁, ∑ w : V, ∑ z ∈ X₁, (A ^ r) x w * (A ^ r) z w := by
                exact Finset.sum_congr rfl fun x _ => by
                  rw [Finset.sum_comm]
                  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => by
                    rw [hApow_sym r w z]
            _ = ∑ w : V, ∑ x ∈ X₁, ∑ z ∈ X₁, (A ^ r) x w * (A ^ r) z w := Finset.sum_comm
            _ = ∑ w : V, (∑ x ∈ X₁, (A ^ r) x w) ^ 2 := by
                apply Finset.sum_congr rfl; intro w _
                rw [sq, Finset.sum_mul]
                exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ w : V, (X₁.card : ℝ) * ∑ x ∈ X₁, ((A ^ r) x w) ^ 2 := by
          apply Finset.sum_le_sum; intro w _
          exact sq_sum_le_card_mul_sum_sq
      _ = (X₁.card : ℝ) * ∑ x ∈ X₁, ∑ w : V, (A ^ r) x w * (A ^ r) w x := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by
            rw [sq, hApow_sym r x w]
      _ ≤ (X₁.card : ℝ) * ∑ x : V, ∑ w : V, (A ^ r) x w * (A ^ r) w x := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X₁) fun x _ _ =>
            Finset.sum_nonneg fun w _ => mul_nonneg
              (Matrix.pow_apply_nonneg (adjMat_nonneg G) _ _ _)
              (Matrix.pow_apply_nonneg (adjMat_nonneg G) _ _ _)
      _ = (X₁.card : ℝ) * Matrix.trace (A ^ (r + r)) := by rw [trace_pow_split, Fintype.sum_prod_type]
  have hX₁_pos : (0 : ℝ) < (X₁.card : ℝ) := by exact_mod_cast hX₁.card_pos
  exact le_of_mul_le_mul_left (hsum_lo.trans hsum_hi) hX₁_pos

/-- Vertex-conflict cycle upper bound (Lemma 2.2 specialized to `u = v`, reusing `R2`'s
`sum_badClosed_le_prefix`, `sum_badPrefixWeight_row`, `sum_mass_ratio_square`, and
`trace_even_interp`): for `r ≥ 2` and `Δ = max deg`, the number of non-injective homomorphic
`2r`-cycles is at most `2 * r^(3/2) * Δ^(1/2) * |V|^(1/(2r)) * Tr(A^(2r))^(1 - 1/(2r))`. -/
private theorem bad_vertex_cycles_le {V : Type} [Fintype V]
    (G : SimpleGraph V) (Δ : ℝ) (hΔ : ∀ v : V, (G.degree v : ℝ) ≤ Δ) (hΔ0 : 0 ≤ Δ)
    (r : ℕ) [NeZero r] (hr : 2 ≤ r) :
    let L := 2 * r
    ((Finset.univ.filter fun x : Fin L → V =>
        (∀ i : Fin L, G.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x).card : ℝ) ^ (2 * r) ≤
      (4 * (r : ℝ) ^ 3 * Δ) ^ r * (Fintype.card V : ℝ) *
        (Matrix.trace (adjMat G ^ (r + r))) ^ (2 * r - 1) := by
  let A := adjMat G
  let n := r - 2
  have hn : n + 2 = r := by omega
  have hL : ((n + 1) + (n + 1)) + 2 = 2 * r := by omega
  have hA := adjMat_nonneg G
  have hloc : ∀ u v : V, ∑ a : V, (if a = u then A v a else 0) ≤ 1 := fun u v => by
    rw [Finset.sum_ite_eq' Finset.univ u (fun a => A v a), if_pos (Finset.mem_univ u)]
    unfold A adjMat; split_ifs <;> norm_num
  -- Bound the bad closed weight for `L' = ((n+1)+(n+1))+2`:
  let U (a b c : V) : ℝ :=
    ∑ x_b : Fin (n + 1) → V,
      if ∃ i_b : Fin (n + 2), a = Fin.cons (α := fun _ => V) b x_b i_b
      then (Classical.choose pathWeight_spec) A (n + 1) b x_b c else 0
  let A₂ (a c : V) := (A ^ (n + 1)) a c
  let B₂ (a c : V) := (A ^ (n + 2)) a c
  let T (p : V × V × V) := A p.1 p.2.1 * U p.1 p.2.1 p.2.2 * A₂ p.2.2 p.1
  let X (p : V × V × V) := A₂ p.1 p.2.2
  let Y (p : V × V × V) := B₂ p.2.1 p.2.2
  have hU_nn : ∀ a b c, 0 ≤ U a b c := fun a b c => badPrefixWeight_nonneg A hA Eq n a b c
  have hUB : ∀ a b c, U a b c ≤ B₂ b c := fun a b c => badPrefixWeight_le_pow A hA Eq n a b c
  have hA2_nn : ∀ a c, 0 ≤ A₂ a c := fun a c => Matrix.pow_apply_nonneg hA _ a c
  have hB2_nn : ∀ a c, 0 ≤ B₂ a c := fun a c => Matrix.pow_apply_nonneg hA _ a c
  have hT_nn : ∀ p, 0 ≤ T p := fun p => mul_nonneg (mul_nonneg (hA _ _) (hU_nn _ _ _)) (hA2_nn _ _)
  have hT_sq : (∑ p : V × V × V, T p) ^ 2 ≤
      (Δ * Matrix.trace (A ^ ((n + 1) + (n + 1)))) *
      (((n + 2 : ℕ) : ℝ) * Matrix.trace (A ^ ((n + 2) + (n + 2)))) := by
    have hs : ∀ p : V × V × V, T p ≠ 0 → X p ≠ 0 ∧ Y p ≠ 0 := by
      rintro ⟨a, b, c⟩ hp
      change A a b * U a b c * A₂ c a ≠ 0 at hp
      refine ⟨fun hx => hp (by
        have : A₂ c a = 0 := by dsimp [A₂, A] at hx ⊢; rw [adjMat_pow_symm G (n + 1) c a]; exact hx
        simp [this]),
        (lt_of_lt_of_le (lt_of_le_of_ne (hU_nn a b c) fun h => hp (by simp [← h])) (hUB a b c)).ne'⟩
    have hsm := sum_mass_ratio_square T X Y hT_nn (fun p => hA2_nn p.1 p.2.2)
      (fun p => hB2_nn p.2.1 p.2.2) hs
    have h1 : (∑ p : V × V × V, T p * (X p / Y p)) ≤ Δ * Matrix.trace (A ^ ((n + 1) + (n + 1))) := by
      calc (∑ p : V × V × V, T p * (X p / Y p))
          ≤ ∑ a : V, ∑ b : V, ∑ c : V, A a b * (A₂ a c * A₂ c a) := by
            simp only [Fintype.sum_prod_type]
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => ?_
            have hu : U a b c * (A₂ a c / B₂ b c) ≤ A₂ a c := by
              by_cases h0 : B₂ b c = 0
              · simpa [h0] using hA2_nn a c
              · calc U a b c * (A₂ a c / B₂ b c)
                    ≤ B₂ b c * (A₂ a c / B₂ b c) :=
                      mul_le_mul_of_nonneg_right (hUB a b c) (div_nonneg (hA2_nn a c) (hB2_nn b c))
                  _ = A₂ a c := by field_simp
            dsimp [T, X, Y]
            calc A a b * U a b c * A₂ c a * (A₂ a c / B₂ b c)
                = A a b * (U a b c * (A₂ a c / B₂ b c)) * A₂ c a := by ring
              _ ≤ A a b * A₂ a c * A₂ c a :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (hA a b)) (hA2_nn c a)
              _ = A a b * (A₂ a c * A₂ c a) := by ring
        _ = ∑ a : V, (∑ b : V, A a b) * ∑ c : V, A₂ a c * A₂ c a := by
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ a : V, Δ * ∑ c : V, A₂ a c * A₂ c a := by
            apply Finset.sum_le_sum; intro a _
            apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun c _ => mul_nonneg (hA2_nn _ _) (hA2_nn _ _))
            rw [adjMat_row_sum G a]; exact hΔ a
        _ = Δ * Matrix.trace (A ^ ((n + 1) + (n + 1))) := by
            rw [← Finset.mul_sum, trace_pow_split, Fintype.sum_prod_type]
    have h2 : (∑ p : V × V × V, T p * (Y p / X p)) ≤
        ((n + 2 : ℕ) : ℝ) * Matrix.trace (A ^ ((n + 2) + (n + 2))) := by
      calc (∑ p : V × V × V, T p * (Y p / X p))
          ≤ ∑ a : V, ∑ b : V, ∑ c : V, B₂ c b * (A b a * U a b c) := by
            simp only [Fintype.sum_prod_type]
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => ?_
            by_cases hx : A₂ a c = 0
            · simpa [T, X, Y, hx] using mul_nonneg (hB2_nn c b) (mul_nonneg (hA b a) (hU_nn a b c))
            · apply le_of_eq
              have ha : A₂ c a = A₂ a c := adjMat_pow_symm G (n + 1) c a
              have hb : B₂ b c = B₂ c b := adjMat_pow_symm G (n + 2) b c
              have hba : A a b = A b a := adjMat_symm G a b
              dsimp [T, X, Y]
              rw [ha, hb, hba]; field_simp
        _ = ∑ b : V, ∑ c : V, B₂ c b * (∑ a : V, A b a * U a b c) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b _
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ b : V, ∑ c : V, B₂ c b * (((n + 2 : ℕ) : ℝ) * 1 * B₂ b c) := by
            refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
              mul_le_mul_of_nonneg_left (sum_badPrefixWeight_row A hA Eq 1 hloc n b c) (hB2_nn c b)
        _ = ((n + 2 : ℕ) : ℝ) * Matrix.trace (A ^ ((n + 2) + (n + 2))) := by
            rw [trace_pow_split, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_comm]
            apply Finset.sum_congr rfl; intro c _
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
    exact hsm.trans (mul_le_mul h1 h2
      (Finset.sum_nonneg fun p _ => mul_nonneg (hT_nn p) (div_nonneg (hB2_nn _ _) (hA2_nn _ _)))
      (mul_nonneg hΔ0 (by
        rw [trace_pow_split, Fintype.sum_prod_type]
        exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (hA2_nn _ _) (hA2_nn _ _))))
  -- Connect bad cycles on `Fin (2 * r)` to `sum_badClosed_le_prefix`:
  let L' := ((n + 1) + (n + 1)) + 2
  have hbad_eq : ((Finset.univ.filter fun x : Fin (2 * r) → V =>
      (∀ i : Fin (2 * r), G.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x).card : ℝ) =
      ∑ z : Fin L' → V,
        if ∃ i j : Fin L', i ≠ j ∧ z i = z j
        then (Classical.choose closedWeight_spec) A z else 0 := by
    let eL : Fin (2 * r) ≃ Fin L' := finCongr hL.symm
    let eFun : (Fin (2 * r) → V) ≃ (Fin L' → V) := Equiv.arrowCongr eL (Equiv.refl V)
    rw [Finset.card_filter, Nat.cast_sum]
    refine Fintype.sum_equiv eFun _ _ fun x => ?_
    have hcyc_iff : (∀ i : Fin (2 * r), G.Adj (x i) (x (i + 1))) ↔
        ∀ i : Fin L', G.Adj (eFun x i) (eFun x (i + 1)) := by
      have hsucc : ∀ i : Fin (2 * r), eL (i + 1) = eL i + 1 := fun i => by
        ext
        simp only [eL, finCongr_apply, Fin.val_cast, Fin.val_add,
          fin_val_one_of_gt (by omega : 1 < 2 * r)]
        rw [fin_val_one_of_gt (by omega : 1 < L')]
        change (i.1 + 1) % (2 * r) = (i.1 + 1) % (((n + 1) + (n + 1)) + 2)
        rw [hL]
      constructor
      · intro hx i
        have h1 : eFun x i = x (eL.symm i) := rfl
        have h2 : eFun x (i + 1) = x (eL.symm i + 1) := by
          change x (eL.symm (i + 1)) = x (eL.symm i + 1)
          congr 1; apply eL.injective; rw [eL.apply_symm_apply, hsucc, eL.apply_symm_apply]
        rw [h1, h2]; exact hx (eL.symm i)
      · intro hx i
        have h1 : x i = eFun x (eL i) := by change x i = x (eL.symm (eL i)); simp
        have h2 : x (i + 1) = eFun x (eL i + 1) := by
          rw [← hsucc]; change x (i + 1) = x (eL.symm (eL (i + 1))); simp
        rw [h1, h2]; exact hx (eL i)
    have hinj_iff : (¬ Function.Injective x) ↔ ∃ i j : Fin L', i ≠ j ∧ eFun x i = eFun x j := by
      simp only [Function.Injective, not_forall, exists_prop]
      constructor
      · rintro ⟨a, b, hab, hne⟩
        exact ⟨eL a, eL b, fun h => hne (eL.injective h), by simpa [eFun] using hab⟩
      · rintro ⟨a, b, hne, hab⟩
        exact ⟨eL.symm a, eL.symm b, hab, fun h => hne (eL.symm.injective h)⟩
    have hcw : (Classical.choose closedWeight_spec) A (eFun x) =
        if ∀ i : Fin L', G.Adj (eFun x i) (eFun x (i + 1)) then 1 else 0 := by
      rw [closedWeight_eq_prod]
      by_cases h : ∀ i : Fin L', G.Adj (eFun x i) (eFun x (i + 1))
      · rw [if_pos h]; exact Finset.prod_eq_one fun i _ => if_pos (h i)
      · rw [if_neg h]; push Not at h; obtain ⟨i, hi⟩ := h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [hcw]
    by_cases h1 : ∀ i : Fin (2 * r), G.Adj (x i) (x (i + 1))
    · by_cases h2 : Function.Injective x
      · have hni : ¬ ∃ i j : Fin L', i ≠ j ∧ eFun x i = eFun x j := fun h => (hinj_iff.mpr h) h2
        rw [if_neg (fun hh => hh.2 h2), if_neg hni, Nat.cast_zero]
      · rw [if_pos ⟨h1, h2⟩, if_pos (hinj_iff.mp h2), if_pos (hcyc_iff.mp h1), Nat.cast_one]
    · have hnc : ¬ ∀ i : Fin L', G.Adj (eFun x i) (eFun x (i + 1)) := fun h => h1 (hcyc_iff.mpr h)
      rw [if_neg (fun hh => h1 hh.1), if_neg hnc, Nat.cast_zero]; split_ifs <;> rfl
  have hprefix := sum_badClosed_le_prefix A hA Eq (fun _ _ h => h.symm) n
  have hsumT_eq : (∑ a : V, ∑ b : V, ∑ c : V,
      A a b * (∑ x_b : Fin (n + 1) → V,
        if ∃ i_b : Fin (n + 2), a = Fin.cons (α := fun _ => V) b x_b i_b
        then (Classical.choose pathWeight_spec) A (n + 1) b x_b c else 0) *
      (A ^ (n + 1)) c a) = ∑ p : V × V × V, T p := by
    simp [Fintype.sum_prod_type, T, U, A₂]
  rw [hsumT_eq] at hprefix
  let bad := ((Finset.univ.filter fun x : Fin (2 * r) → V =>
      (∀ i : Fin (2 * r), G.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x).card : ℝ)
  have hbad_nn : 0 ≤ bad := Nat.cast_nonneg _
  have hbad_le : bad ≤ (2 * r : ℝ) * ∑ p : V × V × V, T p := by
    have hL'R : (L' : ℝ) = 2 * (r : ℝ) := by exact_mod_cast hL
    dsimp [bad]; rw [hbad_eq, ← hL'R]; exact hprefix
  have hbad_sq : bad ^ 2 ≤ (4 * (r : ℝ) ^ 3 * Δ) *
      Matrix.trace (A ^ ((r - 1) + (r - 1))) * Matrix.trace (A ^ (r + r)) := by
    have hn1 : n + 1 = r - 1 := by omega
    have hn2 : n + 2 = r := by omega
    calc bad ^ 2
        ≤ ((2 * (r : ℝ)) * ∑ p : V × V × V, T p) ^ 2 :=
          pow_le_pow_left₀ hbad_nn hbad_le 2
      _ = (4 * (r : ℝ) ^ 2) * (∑ p : V × V × V, T p) ^ 2 := by ring
      _ ≤ (4 * (r : ℝ) ^ 2) * ((Δ * Matrix.trace (A ^ ((n + 1) + (n + 1)))) *
          (((n + 2 : ℕ) : ℝ) * Matrix.trace (A ^ ((n + 2) + (n + 2))))) :=
          mul_le_mul_of_nonneg_left hT_sq (by positivity)
      _ = (4 * (r : ℝ) ^ 3 * Δ) *
          Matrix.trace (A ^ ((r - 1) + (r - 1))) * Matrix.trace (A ^ (r + r)) := by
          rw [hn1, hn2]; ring
  have htr_nn : 0 ≤ Matrix.trace (A ^ (r + r)) := by
    rw [trace_pow_split, Fintype.sum_prod_type]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Matrix.pow_apply_nonneg hA _ _ _)
  have htr_interp := trace_even_interp G (j := r - 1) (r := r) (by omega)
  have hsub1 : r - (r - 1) = 1 := by omega
  rw [hsub1, pow_one] at htr_interp
  calc bad ^ (2 * r)
      = (bad ^ 2) ^ r := by rw [← pow_mul]
    _ ≤ ((4 * (r : ℝ) ^ 3 * Δ) *
        Matrix.trace (A ^ ((r - 1) + (r - 1))) * Matrix.trace (A ^ (r + r))) ^ r :=
        pow_le_pow_left₀ (sq_nonneg _) hbad_sq r
    _ = (4 * (r : ℝ) ^ 3 * Δ) ^ r *
        (Matrix.trace (A ^ ((r - 1) + (r - 1)))) ^ r * (Matrix.trace (A ^ (r + r))) ^ r := by
        rw [mul_pow, mul_pow]
    _ ≤ (4 * (r : ℝ) ^ 3 * Δ) ^ r *
        ((Fintype.card V : ℝ) * (Matrix.trace (A ^ (r + r))) ^ (r - 1)) *
        (Matrix.trace (A ^ (r + r))) ^ r := by
        gcongr
    _ = (4 * (r : ℝ) ^ 3 * Δ) ^ r * (Fintype.card V : ℝ) *
        (Matrix.trace (A ^ (r + r))) ^ (2 * r - 1) := by
        have hexp : (r - 1) + r = 2 * r - 1 := by omega
        rw [← hexp, pow_add]; ring

/-- Helper for `bad_codeg_at_zero_eq`: decompose a `2r`-cycle adjacency predicate into steps
`0→1`, `1→2`, `2→r`, and `r→0`. -/
private lemma bad_codeg_cyc_iff {V : Type} (G : SimpleGraph V) (r : ℕ) [NeZero r] (hr : 3 ≤ r)
    (x : Fin (2 * r) → V) :
    let L := 2 * r
    let m1 := r - 3
    let m2 := r - 1
    (∀ i : Fin L, G.Adj (x i) (x (i + 1))) ↔
      G.Adj (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) ∧
      G.Adj (x ⟨1, by omega⟩) (x ⟨2, by omega⟩) ∧
      (∀ j : Fin (m1 + 1), G.Adj
        (Fin.cons (α := fun _ => V) (x ⟨2, by omega⟩) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) j)
        (Fin.snoc (α := fun _ => V) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) (x ⟨r, by omega⟩) j)) ∧
      (∀ j : Fin (m2 + 1), G.Adj
        (Fin.cons (α := fun _ => V) (x ⟨r, by omega⟩) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) j)
        (Fin.snoc (α := fun _ => V) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) (x ⟨0, by omega⟩) j)) := by
  dsimp only
  let L := 2 * r
  let m1 := r - 3
  let m2 := r - 1
  have hnext : ∀ i : Fin L, (i + 1).1 = (i.1 + 1) % L := fun i => by
    rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < L)]
  have hval_adj : ∀ (a b : ℕ) (ha : a < L) (hb : b < L), b = (a + 1) % L →
      (∀ i : Fin L, G.Adj (x i) (x (i + 1))) → G.Adj (x ⟨a, ha⟩) (x ⟨b, hb⟩) := by
    intro a b ha hb hba hx
    have hEq : (⟨b, hb⟩ : Fin L) = ⟨a, ha⟩ + 1 := by ext; rw [hnext]; exact hba
    rw [hEq]; exact hx ⟨a, ha⟩
  constructor
  · intro hx
    refine ⟨hval_adj 0 1 (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]) hx,
      hval_adj 1 2 (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]) hx, ?_, ?_⟩
    · intro j
      have hL1 : Fin.cons (α := fun _ => V) (x ⟨2, by omega⟩) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) j =
          x ⟨j.1 + 2, by omega⟩ := by
        refine Fin.cases ?_ ?_ j
        · simp
        · intro j'; rfl
      have hR1 : Fin.snoc (α := fun _ => V) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) (x ⟨r, by omega⟩) j =
          x ⟨j.1 + 3, by omega⟩ := by
        unfold Fin.snoc
        split_ifs with hj
        · simp only [cast_eq]; congr 1
        · simp only [cast_eq]; congr 1; ext; change r = j.1 + 3; omega
      rw [hL1, hR1]
      exact hval_adj (j.1 + 2) (j.1 + 3) (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]) hx
    · intro j
      have hL2 : Fin.cons (α := fun _ => V) (x ⟨r, by omega⟩) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) j =
          x ⟨j.1 + r, by omega⟩ := by
        refine Fin.cases ?_ ?_ j
        · simp
        · intro j'; simp only [Fin.cons_succ]; congr 1; ext; change j'.1 + r + 1 = j'.1 + 1 + r; omega
      have hR2 : Fin.snoc (α := fun _ => V) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) (x ⟨0, by omega⟩) j =
          x ⟨(j.1 + r + 1) % L, Nat.mod_lt _ (by omega)⟩ := by
        unfold Fin.snoc
        split_ifs with hj
        · simp only [cast_eq]; congr 1; ext; change j.1 + r + 1 = (j.1 + r + 1) % L; rw [Nat.mod_eq_of_lt (by omega)]
        · simp only [cast_eq]; congr 1; ext; change 0 = (j.1 + r + 1) % L
          have : j.1 + r + 1 = L := by omega
          rw [this, Nat.mod_self]
      rw [hL2, hR2]
      exact hval_adj (j.1 + r) ((j.1 + r + 1) % L) (by omega) (Nat.mod_lt _ (by omega)) rfl hx
  · rintro ⟨h01, h12, hw1, hw2⟩ i
    have hstep : ∀ (a b : ℕ) (ha : a < L) (hb : b < L) (u v : Fin L),
        (⟨a, ha⟩ : Fin L) = u → (⟨b, hb⟩ : Fin L) = v →
        G.Adj (x ⟨a, ha⟩) (x ⟨b, hb⟩) → G.Adj (x u) (x v) := by
      rintro _ _ _ _ _ _ rfl rfl h; exact h
    by_cases hi0 : i.1 = 0
    · exact hstep 0 1 (by omega) (by omega) i (i + 1) (by ext; exact hi0.symm)
        (by ext; rw [hnext, hi0, zero_add, Nat.mod_eq_of_lt (by omega)]) h01
    · by_cases hi1 : i.1 = 1
      · exact hstep 1 2 (by omega) (by omega) i (i + 1) (by ext; exact hi1.symm)
          (by ext; rw [hnext, hi1, Nat.mod_eq_of_lt (by omega)]) h12
      · by_cases hir : i.1 < r
        · let j : Fin (m1 + 1) := ⟨i.1 - 2, by omega⟩
          have hj := hw1 j
          have hL1 : Fin.cons (α := fun _ => V) (x ⟨2, by omega⟩) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) j = x i := by
            have hgen : ∀ k : Fin (m1 + 1), k.1 = i.1 - 2 →
                Fin.cons (α := fun _ => V) (x ⟨2, by omega⟩) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) k = x i := by
              intro k hk; refine Fin.cases ?_ ?_ k hk
              · intro h0j; simp only [Fin.cons_zero]; congr 1; ext; change 2 = i.1; simp at h0j; omega
              · intro j' hEq; simp only [Fin.cons_succ]; congr 1; ext; change j'.1 + 3 = i.1; simp at hEq; omega
            exact hgen j rfl
          have hR1 : Fin.snoc (α := fun _ => V) (fun t : Fin m1 => x ⟨t.1 + 3, by omega⟩) (x ⟨r, by omega⟩) j = x (i + 1) := by
            unfold Fin.snoc
            split_ifs with hlt
            · simp only [cast_eq]; congr 1; ext; rw [hnext, Nat.mod_eq_of_lt (by omega)]; change j.1 + 3 = i.1 + 1; dsimp [j]; omega
            · simp only [cast_eq]; congr 1; ext; rw [hnext, Nat.mod_eq_of_lt (by omega)]; change r = i.1 + 1; dsimp [j] at hlt; omega
          rwa [hL1, hR1] at hj
        · let j : Fin (m2 + 1) := ⟨i.1 - r, by omega⟩
          have hj := hw2 j
          have hL2 : Fin.cons (α := fun _ => V) (x ⟨r, by omega⟩) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) j = x i := by
            have hgen : ∀ k : Fin (m2 + 1), k.1 = i.1 - r →
                Fin.cons (α := fun _ => V) (x ⟨r, by omega⟩) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) k = x i := by
              intro k hk; refine Fin.cases ?_ ?_ k hk
              · intro h0j; simp only [Fin.cons_zero]; congr 1; ext; change r = i.1; simp at h0j; omega
              · intro j' hEq; simp only [Fin.cons_succ]; congr 1; ext; change j'.1 + r + 1 = i.1; simp at hEq; omega
            exact hgen j rfl
          have hR2 : Fin.snoc (α := fun _ => V) (fun t : Fin m2 => x ⟨t.1 + r + 1, by omega⟩) (x ⟨0, by omega⟩) j = x (i + 1) := by
            unfold Fin.snoc
            split_ifs with hlt
            · dsimp [j, m2] at hlt
              simp only [cast_eq]; congr 1; ext; rw [hnext, Nat.mod_eq_of_lt (by omega)]; change j.1 + r + 1 = i.1 + 1; dsimp [j]; omega
            · dsimp [j, m2] at hlt
              simp only [cast_eq]; congr 1; ext; rw [hnext]; change 0 = (i.1 + 1) % L
              have : i.1 + 1 = L := by omega
              rw [this, Nat.mod_self]
          rwa [hL2, hR2] at hj

/-- Helper for `bad_codeg_cycles_le`: express the count of `2r`-cycles with high codegree at
position `0` as a matrix sum over `(x0, x1, xr)`. -/
private lemma bad_codeg_at_zero_eq {V : Type} [Fintype V]
    (G : SimpleGraph V) (s_codeg : ℕ) (r : ℕ) [NeZero r] (hr : 3 ≤ r) :
    let L := 2 * r
    let A := adjMat G
    let isBad2 (u z : V) : Prop := s_codeg < ((G.neighborFinset u) ∩ (G.neighborFinset z)).card
    let P (x0 x1 xr : V) : ℝ :=
      ∑ x2 : V, if isBad2 x0 x2 then A x1 x2 * (A ^ (r - 2)) x2 xr else 0
    ((Finset.univ.filter fun x : Fin L → V =>
        (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
        s_codeg < ((G.neighborFinset (x ⟨0, by omega⟩)) ∩
          (G.neighborFinset (x (⟨0, by omega⟩ + 2)))).card).card : ℝ) =
      ∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0 := by
  dsimp only
  let L := 2 * r
  let A := adjMat G
  let isBad2 (u z : V) : Prop := s_codeg < ((G.neighborFinset u) ∩ (G.neighborFinset z)).card
  let P (x0 x1 xr : V) : ℝ :=
    ∑ x2 : V, if isBad2 x0 x2 then A x1 x2 * (A ^ (r - 2)) x2 xr else 0
  have hpow_sum : ∀ (m : ℕ) (u v : V), (A ^ (m + 1)) u v =
      ∑ w : Fin m → V, (Classical.choose pathWeight_spec) A m u w v := fun m u v =>
    (sum_pathWeight_eq_pow A m u v).symm
  have hpw_ite : ∀ (m : ℕ) (u v : V) (w : Fin m → V),
      (Classical.choose pathWeight_spec) A m u w v =
        if (∀ j : Fin (m + 1), G.Adj (Fin.cons (α := fun _ => V) u w j) (Fin.snoc (α := fun _ => V) w v j))
        then 1 else 0 := by
    intro m u v w
    rw [pathWeight_eq_prod]
    have hcast : ∀ j : Fin (m + 1),
        Fin.cons (α := fun _ => V) u (Fin.snoc (α := fun _ => V) w v) j.castSucc =
          Fin.cons (α := fun _ => V) u w j := by
      intro j; refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · simp [Fin.snoc]
    have hsucc : ∀ j : Fin (m + 1),
        Fin.cons (α := fun _ => V) u (Fin.snoc (α := fun _ => V) w v) j.succ =
          Fin.snoc (α := fun _ => V) w v j := fun j => rfl
    by_cases h : ∀ j : Fin (m + 1), G.Adj (Fin.cons (α := fun _ => V) u w j) (Fin.snoc (α := fun _ => V) w v j)
    · rw [if_pos h]
      refine Finset.prod_eq_one fun j _ => ?_
      rw [hcast j, hsucc j]; exact if_pos (h j)
    · rw [if_neg h]
      push Not at h; obtain ⟨j, hj⟩ := h
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [hcast j, hsucc j]; exact if_neg hj
  let m1 := r - 3
  let m2 := r - 1
  have hm1 : m1 + 1 = r - 2 := by omega
  have hm2 : m2 + 1 = r := by omega
  have hRHS : (∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0) =
      ∑ x0 : V, ∑ x1 : V, ∑ x2 : V, ∑ xr : V,
        ∑ w1 : Fin m1 → V, ∑ w2 : Fin m2 → V,
          (if isBad2 x0 x2 then
            A x0 x1 * A x1 x2 *
            (Classical.choose pathWeight_spec) A m1 x2 w1 xr *
            (Classical.choose pathWeight_spec) A m2 xr w2 x0
          else 0) := by
    have h1 : ∀ x0 x1 xr : V,
        A x0 x1 * P x0 x1 xr * (A ^ r) xr x0 =
        ∑ x2 : V, ∑ w1 : Fin m1 → V, ∑ w2 : Fin m2 → V,
          (if isBad2 x0 x2 then
            A x0 x1 * A x1 x2 *
            (Classical.choose pathWeight_spec) A m1 x2 w1 xr *
            (Classical.choose pathWeight_spec) A m2 xr w2 x0
          else 0) := by
      intro x0 x1 xr
      dsimp [P]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x2 _
      by_cases hb : isBad2 x0 x2
      · simp only [if_pos hb]
        rw [← hm1, hpow_sum m1 x2 xr, ← hm2, hpow_sum m2 xr x0]
        calc A x0 x1 * (A x1 x2 * ∑ w1 : Fin m1 → V, (Classical.choose pathWeight_spec) A m1 x2 w1 xr) *
              ∑ w2 : Fin m2 → V, (Classical.choose pathWeight_spec) A m2 xr w2 x0
            = (∑ w1 : Fin m1 → V, A x0 x1 * A x1 x2 * (Classical.choose pathWeight_spec) A m1 x2 w1 xr) *
              ∑ w2 : Fin m2 → V, (Classical.choose pathWeight_spec) A m2 xr w2 x0 := by
                congr 1; rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun w1 _ => by ring
          _ = ∑ w1 : Fin m1 → V, ∑ w2 : Fin m2 → V,
                A x0 x1 * A x1 x2 * (Classical.choose pathWeight_spec) A m1 x2 w1 xr *
                  (Classical.choose pathWeight_spec) A m2 xr w2 x0 := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun w1 _ => Finset.mul_sum _ _ _
      · simp [if_neg hb]
    simp_rw [h1]
    apply Finset.sum_congr rfl; intro x0 _
    apply Finset.sum_congr rfl; intro x1 _
    exact Finset.sum_comm
  rw [hRHS, Finset.card_filter, Nat.cast_sum]
  let toTuple (x : Fin L → V) : V × V × V × V × (Fin m1 → V) × (Fin m2 → V) :=
    (x ⟨0, by omega⟩, x ⟨1, by omega⟩, x ⟨2, by omega⟩, x ⟨r, by omega⟩,
     fun j => x ⟨j.1 + 3, by omega⟩, fun j => x ⟨j.1 + r + 1, by omega⟩)
  let fromTuple (t : V × V × V × V × (Fin m1 → V) × (Fin m2 → V)) (i : Fin L) : V :=
    if h0 : i.1 = 0 then t.1
    else if h1 : i.1 = 1 then t.2.1
    else if h2 : i.1 = 2 then t.2.2.1
    else if h3 : i.1 < r then t.2.2.2.2.1 ⟨i.1 - 3, by omega⟩
    else if h4 : i.1 = r then t.2.2.2.1
    else t.2.2.2.2.2 ⟨i.1 - r - 1, by omega⟩
  let eSplit : (Fin L → V) ≃ (V × V × V × V × (Fin m1 → V) × (Fin m2 → V)) :=
    { toFun := toTuple
      invFun := fromTuple
      left_inv := fun x => by
        funext i
        dsimp [toTuple, fromTuple]
        split_ifs with h0 h1 h2 h3 h4
        · congr 1; ext; exact h0.symm
        · congr 1; ext; exact h1.symm
        · congr 1; ext; exact h2.symm
        · congr 1; ext; change i.1 - 3 + 3 = i.1; omega
        · congr 1; ext; exact h4.symm
        · congr 1; ext; change i.1 - r - 1 + r + 1 = i.1; omega
      right_inv := fun ⟨x0, x1, x2, xr, w1, w2⟩ => by
        dsimp [toTuple, fromTuple]
        refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ ?_))))
        · have h1 : r ≠ 0 := by omega
          have h2 : r ≠ 1 := by omega
          have h3 : r ≠ 2 := by omega
          simp [h1, h2, h3]
        · funext j
          dsimp only
          split_ifs <;> first | omega | rfl
        · funext j
          dsimp only
          split_ifs <;> try omega
          congr 1; ext; dsimp only; omega }
  have hsum_prod : (∑ x0 : V, ∑ x1 : V, ∑ x2 : V, ∑ xr : V,
      ∑ w1 : Fin m1 → V, ∑ w2 : Fin m2 → V,
        (if isBad2 x0 x2 then
          A x0 x1 * A x1 x2 *
          (Classical.choose pathWeight_spec) A m1 x2 w1 xr *
          (Classical.choose pathWeight_spec) A m2 xr w2 x0
        else 0)) =
      ∑ t : V × V × V × V × (Fin m1 → V) × (Fin m2 → V),
        (if isBad2 t.1 t.2.2.1 then
          A t.1 t.2.1 * A t.2.1 t.2.2.1 *
          (Classical.choose pathWeight_spec) A m1 t.2.2.1 t.2.2.2.2.1 t.2.2.2.1 *
          (Classical.choose pathWeight_spec) A m2 t.2.2.2.1 t.2.2.2.2.2 t.1
        else 0) := by
    simp only [Fintype.sum_prod_type]
  rw [hsum_prod]
  refine Fintype.sum_equiv eSplit _ _ fun x => ?_
  have h0_eq : (0 : Fin L) = ⟨0, by omega⟩ := rfl
  have h02 : (⟨0, by omega⟩ : Fin L) + 2 = ⟨2, by omega⟩ := by
    ext; have h2v : (2 : Fin L).val = 2 := by change 2 % L = 2; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, h2v]; dsimp only; rw [zero_add, Nat.mod_eq_of_lt (by omega)]
  have hbad_iff : (s_codeg < ((G.neighborFinset (x 0)) ∩ (G.neighborFinset (x (0 + 2)))).card) ↔
      isBad2 (x ⟨0, by omega⟩) (x ⟨2, by omega⟩) := by
    change (s_codeg < ((G.neighborFinset (x 0)) ∩ (G.neighborFinset (x (0 + 2)))).card) ↔
      (s_codeg < ((G.neighborFinset (x ⟨0, by omega⟩)) ∩ (G.neighborFinset (x ⟨2, by omega⟩))).card)
    have hce : ((G.neighborFinset (x 0)) ∩ (G.neighborFinset (x (0 + 2)))).card =
        ((G.neighborFinset (x ⟨0, by omega⟩)) ∩ (G.neighborFinset (x ⟨2, by omega⟩))).card := by
      congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, h0_eq, h02]
    rw [hce]
  have heS : eSplit x = toTuple x := rfl
  rw [heS]
  dsimp only [toTuple]
  rw [hpw_ite m1, hpw_ite m2]
  have hcyc_iff := bad_codeg_cyc_iff G r hr x
  dsimp only at hcyc_iff
  by_cases hb : isBad2 (x ⟨0, by omega⟩) (x ⟨2, by omega⟩)
  · by_cases hc : ∀ i : Fin L, G.Adj (x i) (x (i + 1))
    · obtain ⟨h1, h2, h3, h4⟩ := hcyc_iff.mp hc
      rw [if_pos ⟨hc, hbad_iff.mpr hb⟩, if_pos hb, if_pos h3, if_pos h4, Nat.cast_one]
      unfold A adjMat
      rw [if_pos h1, if_pos h2]
      ring
    · rw [if_neg (fun h => hc h.1), if_pos hb, Nat.cast_zero]
      by_contra hne
      apply hc
      rw [hcyc_iff]
      unfold A adjMat at hne
      split_ifs at hne with h1 h2 h3 h4 <;> simp at hne
      exact ⟨h1, h2, h3, h4⟩
  · rw [if_neg (fun h => hb (hbad_iff.mp h.2)), if_neg hb, Nat.cast_zero]

/-- High-codegree two-step cycle upper bound (replacing Lemma 2.1 in Lemma 2.17):
if for every edge `u ~ w`, at most `s` neighbors `z` of `w` satisfy `codeg(u, z) > s_codeg`,
then for `r ≥ 3` the number of homomorphic `2r`-cycles with some `codeg(x i, x (i + 2)) > s_codeg`
satisfies `bad^(2r) ≤ (4 r^2 s Δ^3)^r * |V|^2 * Tr(A^(2r))^(2r - 2)`. -/
private theorem bad_codeg_cycles_le {V : Type} [Fintype V]
    (G : SimpleGraph V) (Δ s : ℝ) (s_codeg : ℕ)
    (hΔ : ∀ v : V, (G.degree v : ℝ) ≤ Δ) (hΔ0 : 0 ≤ Δ) (hs0 : 0 ≤ s)
    (hs : ∀ u w : V, G.Adj u w →
      (((G.neighborFinset w).filter fun z =>
          s_codeg < ((G.neighborFinset u) ∩ (G.neighborFinset z)).card).card : ℝ) ≤ s)
    (r : ℕ) [NeZero r] (hr : 3 ≤ r) :
    let L := 2 * r
    ((Finset.univ.filter fun x : Fin L → V =>
        (∀ i : Fin L, G.Adj (x i) (x (i + 1))) ∧
        ∃ i : Fin L, s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card).card : ℝ) ^ (2 * r) ≤
      (4 * (r : ℝ) ^ 2 * s * Δ ^ 3) ^ r * (Fintype.card V : ℝ) ^ 2 *
        (Matrix.trace (adjMat G ^ (r + r))) ^ (2 * r - 2) := by
  let L := 2 * r
  let A := adjMat G
  have hA := adjMat_nonneg G
  let badAt (i : Fin L) : Finset (Fin L → V) :=
    Finset.univ.filter fun x =>
      (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
      s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card
  have hrot : ∀ i : Fin L, (badAt i).card = (badAt ⟨0, by omega⟩).card := by
    intro i
    refine Finset.card_bij (fun x _ t => x (t + i)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hcyc, hbad⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_, ?_⟩
      · dsimp only
        have heq : t + 1 + i = (t + i) + 1 := by abel
        rw [heq]; exact hcyc (t + i)
      · dsimp only
        have h0 : (⟨0, by omega⟩ : Fin L) + i = i := by simp
        have h2 : (⟨0, by omega⟩ : Fin L) + 2 + i = i + 2 := by
          have : (⟨0, by omega⟩ : Fin L) = 0 := rfl
          rw [this, zero_add, add_comm]
        have hce : ((G.neighborFinset (x (⟨0, by omega⟩ + i))) ∩
            (G.neighborFinset (x (⟨0, by omega⟩ + 2 + i)))).card =
            ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card := by
          congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, h0, h2]
        rwa [hce]
    · intro x₁ _ x₂ _ hEq
      funext t
      have := congrFun hEq (t - i)
      simpa using this
    · intro y hy
      obtain ⟨hcyc, hbad⟩ := (Finset.mem_filter.mp hy).2
      refine ⟨fun t => y (t - i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => ?_, ?_⟩, ?_⟩
      · dsimp only
        have heq : t + 1 - i = (t - i) + 1 := by abel
        rw [heq]; exact hcyc (t - i)
      · dsimp only
        have h0 : i - i = (⟨0, by omega⟩ : Fin L) := by
          change i - i = 0; exact sub_self i
        have h2 : i + 2 - i = (⟨0, by omega⟩ : Fin L) + 2 := by
          change i + 2 - i = 0 + 2; abel
        have hce : ((G.neighborFinset (y (i - i))) ∩ (G.neighborFinset (y (i + 2 - i)))).card =
            ((G.neighborFinset (y ⟨0, by omega⟩)) ∩ (G.neighborFinset (y (⟨0, by omega⟩ + 2)))).card := by
          congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, h0, h2]
        rwa [hce]
      · funext t; simp
  have hunion : ((Finset.univ.filter fun x : Fin L → V =>
      (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
      ∃ i : Fin L, s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card).card : ℝ) ≤
      (2 * (r : ℝ)) * ((badAt ⟨0, by omega⟩).card : ℝ) := by
    have hsub : (Finset.univ.filter fun x : Fin L → V =>
        (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
        ∃ i : Fin L, s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card) ⊆
        Finset.univ.biUnion badAt := by
      intro x hx
      obtain ⟨hcyc, i, hi⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcyc, hi⟩⟩
    have hc : (Finset.univ.filter fun x : Fin L → V =>
        (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
        ∃ i : Fin L, s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card).card ≤
        (2 * r) * (badAt ⟨0, by omega⟩).card := by
      calc _ ≤ (Finset.univ.biUnion badAt).card := Finset.card_le_card hsub
        _ ≤ ∑ i : Fin L, (badAt i).card := Finset.card_biUnion_le
        _ = ∑ _i : Fin L, (badAt ⟨0, by omega⟩).card := Finset.sum_congr rfl fun i _ => hrot i
        _ = (2 * r) * (badAt ⟨0, by omega⟩).card := by simp [L]
    exact_mod_cast hc
  -- Express `(badAt 0).card` in terms of `A`:
  let isBad2 (u z : V) : Prop := s_codeg < ((G.neighborFinset u) ∩ (G.neighborFinset z)).card
  let P (x0 x1 xr : V) : ℝ :=
    ∑ x2 : V, if isBad2 x0 x2 then A x1 x2 * (A ^ (r - 2)) x2 xr else 0
  have hbad0_eq : ((badAt ⟨0, by omega⟩).card : ℝ) =
      ∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0 :=
    bad_codeg_at_zero_eq G s_codeg r hr
  -- Apply Cauchy–Schwarz to `badAt 0`:
  have hbad0_sq : ((badAt ⟨0, by omega⟩).card : ℝ) ^ 2 ≤
      (s * Δ ^ 3) * Matrix.trace (A ^ ((r - 2) + (r - 2))) * Matrix.trace (A ^ (r + r)) := by
    rw [hbad0_eq]
    have hcs : (∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0) ^ 2 ≤
        (∑ p : V × V × V, (A p.1 p.2.1 * P p.1 p.2.1 p.2.2) ^ 2) *
        (∑ p : V × V × V, (A p.1 p.2.1 * (A ^ r) p.2.2 p.1) ^ 2) := by
      have hrew : (∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0) =
          ∑ p : V × V × V, (A p.1 p.2.1 * P p.1 p.2.1 p.2.2) * (A p.1 p.2.1 * (A ^ r) p.2.2 p.1) := by
        simp only [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun xr _ => ?_
        unfold A adjMat; split_ifs <;> ring
      rw [hrew]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    have hfac2 : (∑ p : V × V × V, (A p.1 p.2.1 * (A ^ r) p.2.2 p.1) ^ 2) ≤
        Δ * Matrix.trace (A ^ (r + r)) := by
      simp only [Fintype.sum_prod_type]
      calc ∑ x0 : V, ∑ x1 : V, ∑ xr : V, (A x0 x1 * (A ^ r) xr x0) ^ 2
          = ∑ x0 : V, (∑ x1 : V, A x0 x1) * ∑ xr : V, (A ^ r) x0 xr * (A ^ r) xr x0 := by
            apply Finset.sum_congr rfl; intro x0 _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro x1 _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro xr _
            rw [adjMat_pow_symm G r x0 xr]
            unfold A adjMat; split_ifs <;> ring
        _ ≤ ∑ x0 : V, Δ * ∑ xr : V, (A ^ r) x0 xr * (A ^ r) xr x0 := by
            apply Finset.sum_le_sum; intro x0 _
            apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun xr _ =>
              mul_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Matrix.pow_apply_nonneg hA _ _ _))
            rw [adjMat_row_sum G x0]; exact hΔ x0
        _ = Δ * Matrix.trace (A ^ (r + r)) := by rw [← Finset.mul_sum, trace_pow_split, Fintype.sum_prod_type]
    have hfac1 : (∑ p : V × V × V, (A p.1 p.2.1 * P p.1 p.2.1 p.2.2) ^ 2) ≤
        s * Δ ^ 2 * Matrix.trace (A ^ ((r - 2) + (r - 2))) := by
      simp only [Fintype.sum_prod_type]
      have hPsq : ∀ x0 x1 xr : V, (A x0 x1 * P x0 x1 xr) ^ 2 ≤
          s * A x0 x1 * ∑ x2 : V, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 := by
        intro x0 x1 xr
        by_cases h01 : G.Adj x0 x1
        · have hA01 : A x0 x1 = 1 := if_pos h01
          rw [hA01, one_mul, mul_one]
          let S2 := (G.neighborFinset x1).filter (isBad2 x0)
          have hPeq : P x0 x1 xr = ∑ x2 ∈ S2, (A ^ (r - 2)) x2 xr := by
            dsimp [P, S2]
            rw [Finset.sum_filter]
            refine (Finset.sum_subset (Finset.subset_univ (G.neighborFinset x1)) (fun x2 _ hx2 => ?_)).symm.trans ?_
            · have hnot : ¬ G.Adj x1 x2 := fun h => hx2 ((mem_neighborFinset _ _ _).mpr h)
              simp [A, adjMat, hnot]
            · apply Finset.sum_congr rfl; intro x2 hx2
              have h12 : G.Adj x1 x2 := (mem_neighborFinset G x1 x2).mp hx2
              have hA12 : A x1 x2 = 1 := if_pos h12
              dsimp [isBad2]; rw [hA12, one_mul]
          rw [hPeq]
          calc (∑ x2 ∈ S2, (A ^ (r - 2)) x2 xr) ^ 2
              ≤ (S2.card : ℝ) * ∑ x2 ∈ S2, ((A ^ (r - 2)) x2 xr) ^ 2 := sq_sum_le_card_mul_sum_sq
            _ ≤ s * ∑ x2 ∈ S2, ((A ^ (r - 2)) x2 xr) ^ 2 :=
                mul_le_mul_of_nonneg_right (hs x0 x1 h01) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            _ ≤ s * ∑ x2 : V, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 := by
                apply mul_le_mul_of_nonneg_left _ hs0
                calc ∑ x2 ∈ S2, ((A ^ (r - 2)) x2 xr) ^ 2
                    = ∑ x2 ∈ S2, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 := by
                      apply Finset.sum_congr rfl; intro x2 hx2
                      have h12 : G.Adj x1 x2 := (mem_neighborFinset _ _ _).mp (Finset.mem_filter.mp hx2).1
                      simp [A, adjMat, h12]
                  _ ≤ ∑ x2 : V, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
                        mul_nonneg (hA _ _) (sq_nonneg _)
        · have hA01 : A x0 x1 = 0 := if_neg h01
          simp [hA01]
      calc ∑ x0 : V, ∑ x1 : V, ∑ xr : V, (A x0 x1 * P x0 x1 xr) ^ 2
          ≤ ∑ x0 : V, ∑ x1 : V, ∑ xr : V,
              s * A x0 x1 * ∑ x2 : V, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 :=
            Finset.sum_le_sum fun x0 _ => Finset.sum_le_sum fun x1 _ => Finset.sum_le_sum fun xr _ => hPsq x0 x1 xr
        _ = s * ∑ x2 : V, (∑ x1 : V, A x2 x1 * (∑ x0 : V, A x1 x0)) *
              (∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2) := by
            rw [Finset.mul_sum]
            -- Swap sums cleanly:
            have hsw : ∀ x0 x1 : V,
                ∑ xr : V, s * A x0 x1 * ∑ x2 : V, A x1 x2 * ((A ^ (r - 2)) x2 xr) ^ 2 =
                ∑ x2 : V, s * (A x2 x1 * A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2 := by
              intro x0 x1
              have hAsym : ∀ a b : V, A a b = A b a := adjMat_symm G
              have hApow_sym : ∀ a b : V, (A ^ (r - 2)) a b = (A ^ (r - 2)) b a := adjMat_pow_symm G (r - 2)
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro x2 _
              apply Finset.sum_congr rfl; intro xr _
              rw [hAsym x0 x1, hAsym x1 x2, sq, hApow_sym xr x2]; ring
            simp_rw [hsw]
            calc ∑ x0 : V, ∑ x1 : V, ∑ x2 : V,
                    s * (A x2 x1 * A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2
                = ∑ x2 : V, ∑ x1 : V, ∑ x0 : V,
                    s * (A x2 x1 * A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2 := by
                  rw [Finset.sum_comm]
                  trans ∑ x1 : V, ∑ x2 : V, ∑ x0 : V,
                      s * (A x2 x1 * A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2
                  · exact Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
                  · exact Finset.sum_comm
              _ = ∑ x2 : V, s * ((∑ x1 : V, A x2 x1 * ∑ x0 : V, A x1 x0) *
                    ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2) := by
                  apply Finset.sum_congr rfl; intro x2 _
                  rw [Finset.sum_mul, Finset.mul_sum]
                  apply Finset.sum_congr rfl; intro x1 _
                  calc ∑ x0 : V, s * (A x2 x1 * A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2
                      = (∑ x0 : V, s * (A x2 x1 * A x1 x0)) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2 :=
                        (Finset.sum_mul _ _ _).symm
                    _ = s * (A x2 x1 * (∑ x0 : V, A x1 x0) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2) := by
                        have hfactor : ∑ x0 : V, s * (A x2 x1 * A x1 x0) = s * (A x2 x1 * ∑ x0 : V, A x1 x0) := by
                          rw [Finset.mul_sum, Finset.mul_sum]
                        rw [hfactor]; ring
        _ ≤ s * ∑ x2 : V, (Δ * Δ) * ∑ xr : V, (A ^ (r - 2)) x2 xr * (A ^ (r - 2)) xr x2 := by
            apply mul_le_mul_of_nonneg_left _ hs0
            apply Finset.sum_le_sum; intro x2 _
            apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun xr _ =>
              mul_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Matrix.pow_apply_nonneg hA _ _ _))
            calc ∑ x1 : V, A x2 x1 * ∑ x0 : V, A x1 x0
                ≤ ∑ x1 : V, A x2 x1 * Δ :=
                  Finset.sum_le_sum fun x1 _ => mul_le_mul_of_nonneg_left
                    (by rw [adjMat_row_sum G x1]; exact hΔ x1) (hA x2 x1)
              _ = (∑ x1 : V, A x2 x1) * Δ := (Finset.sum_mul _ _ _).symm
              _ ≤ Δ * Δ := mul_le_mul_of_nonneg_right (by rw [adjMat_row_sum G x2]; exact hΔ x2) hΔ0
        _ = s * Δ ^ 2 * Matrix.trace (A ^ ((r - 2) + (r - 2))) := by
            rw [← Finset.mul_sum, trace_pow_split, Fintype.sum_prod_type]; ring
    calc (∑ x0 : V, ∑ x1 : V, ∑ xr : V, A x0 x1 * P x0 x1 xr * (A ^ r) xr x0) ^ 2
        ≤ (s * Δ ^ 2 * Matrix.trace (A ^ ((r - 2) + (r - 2)))) * (Δ * Matrix.trace (A ^ (r + r))) :=
          hcs.trans (mul_le_mul hfac1 hfac2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (mul_nonneg (mul_nonneg hs0 (sq_nonneg _)) (by
              rw [trace_pow_split, Fintype.sum_prod_type]
              exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
                mul_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Matrix.pow_apply_nonneg hA _ _ _))))
      _ = (s * Δ ^ 3) * Matrix.trace (A ^ ((r - 2) + (r - 2))) * Matrix.trace (A ^ (r + r)) := by ring
  -- Combine `hunion`, `hbad0_sq`, and `trace_even_interp (j := r - 2)`:
  have htr_nn : 0 ≤ Matrix.trace (A ^ (r + r)) := by
    rw [trace_pow_split, Fintype.sum_prod_type]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Matrix.pow_apply_nonneg hA _ _ _)
  have htr_interp := trace_even_interp G (j := r - 2) (r := r) (by omega)
  have hsub2 : r - (r - 2) = 2 := by omega
  rw [hsub2] at htr_interp
  let bad := ((Finset.univ.filter fun x : Fin L → V =>
      (∀ t : Fin L, G.Adj (x t) (x (t + 1))) ∧
      ∃ i : Fin L, s_codeg < ((G.neighborFinset (x i)) ∩ (G.neighborFinset (x (i + 2)))).card).card : ℝ)
  have hbad_sq : bad ^ 2 ≤ (4 * (r : ℝ) ^ 2 * s * Δ ^ 3) *
      Matrix.trace (A ^ ((r - 2) + (r - 2))) * Matrix.trace (A ^ (r + r)) := by
    calc bad ^ 2
        ≤ ((2 * (r : ℝ)) * ((badAt ⟨0, by omega⟩).card : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hunion 2
      _ = (4 * (r : ℝ) ^ 2) * ((badAt ⟨0, by omega⟩).card : ℝ) ^ 2 := by ring
      _ ≤ (4 * (r : ℝ) ^ 2) * ((s * Δ ^ 3) *
          Matrix.trace (A ^ ((r - 2) + (r - 2))) * Matrix.trace (A ^ (r + r))) :=
          mul_le_mul_of_nonneg_left hbad0_sq (by positivity)
      _ = _ := by ring
  calc bad ^ (2 * r)
      = (bad ^ 2) ^ r := by rw [← pow_mul]
    _ ≤ ((4 * (r : ℝ) ^ 2 * s * Δ ^ 3) *
        Matrix.trace (A ^ ((r - 2) + (r - 2))) * Matrix.trace (A ^ (r + r))) ^ r :=
        pow_le_pow_left₀ (sq_nonneg _) hbad_sq r
    _ = (4 * (r : ℝ) ^ 2 * s * Δ ^ 3) ^ r *
        (Matrix.trace (A ^ ((r - 2) + (r - 2)))) ^ r * (Matrix.trace (A ^ (r + r))) ^ r := by
        rw [mul_pow, mul_pow]
    _ ≤ (4 * (r : ℝ) ^ 2 * s * Δ ^ 3) ^ r *
        ((Fintype.card V : ℝ) ^ 2 * (Matrix.trace (A ^ (r + r))) ^ (r - 2)) *
        (Matrix.trace (A ^ (r + r))) ^ r := by gcongr
    _ = (4 * (r : ℝ) ^ 2 * s * Δ ^ 3) ^ r * (Fintype.card V : ℝ) ^ 2 *
        (Matrix.trace (A ^ (r + r))) ^ (2 * r - 2) := by
        have hexp : (r - 2) + r = 2 * r - 2 := by omega
        rw [← hexp, pow_add]; ring

/- ### Section 5: Few 4-cycles (Lemma 2.13) -/

/-- Bound on `(8k - 2)`-projections of cycles in a graph of max degree `≤ Δ`. -/
private lemma card_dropTwo_walks_le {V : Type} [Fintype V]
    {k : ℕ} [NeZero k] (hk : 1 ≤ k) (G : SimpleGraph V) (Δ : ℝ) (hΔ : ∀ v : V, (G.degree v : ℝ) ≤ Δ) (hΔ0 : 0 ≤ Δ)
    (C : Finset (Fin (8 * k) → V))
    (hC : ∀ x ∈ C, ∀ t : Fin (8 * k), G.Adj (x t) (x (t + 1))) (p : Fin (8 * k)) :
    ((C.image (dropTwo p)).card : ℝ) ≤ (Fintype.card V : ℝ) * Δ ^ (8 * k - 3) := by
  -- Order the remaining `8k - 2` coordinates as a walk `p + 3, p + 4, ..., p + 8k (= p)` of length `8k - 3`:
  let walkLen := 8 * k - 3
  let W (t : ℕ) : Finset (Fin (t + 1) → V) :=
    Finset.univ.filter fun f => ∀ j : Fin t, G.Adj (f ⟨j.1, by omega⟩) (f ⟨j.1 + 1, by omega⟩)
  have hW_card : ∀ t : ℕ, ((W t).card : ℝ) ≤ (Fintype.card V : ℝ) * Δ ^ t := by
    intro t
    induction t with
    | zero =>
      have h1 : (W 0).card ≤ Fintype.card (Fin 1 → V) := Finset.card_le_univ _
      rw [Fintype.card_fun, Fintype.card_fin, pow_one] at h1
      simpa using (Nat.cast_le (α := ℝ).mpr h1)
    | succ t ih =>
      -- Fiber over the prefix `Fin (t + 1) → V`:
      let pref (f : Fin (t + 2) → V) : Fin (t + 1) → V := fun j => f ⟨j.1, by omega⟩
      have hsub : W (t + 1) ⊆ (W t).biUnion fun g =>
          (G.neighborFinset (g ⟨t, by omega⟩)).image fun v =>
            Fin.snoc (α := fun _ => V) g v := by
        intro f hf
        have hfw := (Finset.mem_filter.mp hf).2
        have hgp : pref f ∈ W t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hfw ⟨j.1, by omega⟩⟩
        have hadj : G.Adj (pref f ⟨t, by omega⟩) (f ⟨t + 1, by omega⟩) := hfw ⟨t, by omega⟩
        refine Finset.mem_biUnion.mpr ⟨pref f, hgp, Finset.mem_image.mpr
          ⟨f ⟨t + 1, by omega⟩, (mem_neighborFinset _ _ _).mpr hadj, ?_⟩⟩
        funext j
        unfold Fin.snoc
        split_ifs with hj
        · simp [pref]
        · simp only [cast_eq]; congr 1; ext; dsimp only; omega
      have hcard : (W (t + 1)).card ≤ ∑ g ∈ W t, G.degree (g ⟨t, by omega⟩) := by
        calc (W (t + 1)).card
            ≤ ∑ g ∈ W t, ((G.neighborFinset (g ⟨t, by omega⟩)).image fun v =>
                Fin.snoc (α := fun _ => V) g v).card :=
              (Finset.card_le_card hsub).trans Finset.card_biUnion_le
          _ ≤ ∑ g ∈ W t, (G.neighborFinset (g ⟨t, by omega⟩)).card :=
              Finset.sum_le_sum fun g _ => Finset.card_image_le
          _ = ∑ g ∈ W t, G.degree (g ⟨t, by omega⟩) :=
              Finset.sum_congr rfl fun g _ => card_neighborFinset_eq_degree _ _
      calc ((W (t + 1)).card : ℝ)
          ≤ ∑ g ∈ W t, (G.degree (g ⟨t, by omega⟩) : ℝ) := by exact_mod_cast hcard
        _ ≤ ∑ _g ∈ W t, Δ := Finset.sum_le_sum fun g _ => hΔ _
        _ = ((W t).card : ℝ) * Δ := by simp
        _ ≤ ((Fintype.card V : ℝ) * Δ ^ t) * Δ := mul_le_mul_of_nonneg_right ih hΔ0
        _ = (Fintype.card V : ℝ) * Δ ^ (t + 1) := by rw [pow_succ]; ring
  -- Inject `C.image (dropTwo p)` into `W walkLen` via `q ↦ fun j => q (p + (j + 3))`:
  have h1_val : (1 : Fin (8 * k)).val = 1 := fin_val_one_of_gt (by omega)
  have h2_val : (2 : Fin (8 * k)).val = 2 := by change 2 % (8 * k) = 2; exact Nat.mod_eq_of_lt (by omega)
  have hnot12' : ∀ j : Fin (walkLen + 1),
      p + Fin.ofNat (8 * k) (j.1 + 3) ≠ p + 1 ∧
      p + Fin.ofNat (8 * k) (j.1 + 3) ≠ p + 2 := by
    intro j
    constructor
    · intro h
      have h0 := congrArg (· - p) h
      simp only [add_sub_cancel_left] at h0
      have hv := congrArg Fin.val h0
      rw [h1_val] at hv
      change (j.1 + 3) % (8 * k) = 1 at hv
      by_cases hlt : j.1 + 3 < 8 * k
      · rw [Nat.mod_eq_of_lt hlt] at hv; omega
      · have heq : j.1 + 3 = 8 * k := by omega
        rw [heq, Nat.mod_self] at hv; omega
    · intro h
      have h0 := congrArg (· - p) h
      simp only [add_sub_cancel_left] at h0
      have hv := congrArg Fin.val h0
      rw [h2_val] at hv
      change (j.1 + 3) % (8 * k) = 2 at hv
      by_cases hlt : j.1 + 3 < 8 * k
      · rw [Nat.mod_eq_of_lt hlt] at hv; omega
      · have heq : j.1 + 3 = 8 * k := by omega
        rw [heq, Nat.mod_self] at hv; omega
  let toWalk' (q : {j : Fin (8 * k) // j ≠ p + 1 ∧ j ≠ p + 2} → V) : Fin (walkLen + 1) → V :=
    fun j => q ⟨p + Fin.ofNat (8 * k) (j.1 + 3), hnot12' j⟩
  have hinj' : Function.Injective toWalk' := by
    intro q₁ q₂ hEq
    funext ⟨i, hi1, hi2⟩
    let d := (i - p).1
    have hd_ne1 : d ≠ 1 := fun h => hi1 (by
      have : i - p = 1 := by ext; rw [h1_val]; exact h
      exact eq_add_of_sub_eq' this)
    have hd_ne2 : d ≠ 2 := fun h => hi2 (by
      have : i - p = 2 := by ext; rw [h2_val]; exact h
      exact eq_add_of_sub_eq' this)
    let jval := if d = 0 then walkLen else d - 3
    have hjlt : jval < walkLen + 1 := by dsimp [jval, walkLen]; split_ifs <;> omega
    have hpos : p + Fin.ofNat (8 * k) (jval + 3) = i := by
      have hdiff : Fin.ofNat (8 * k) (jval + 3) = i - p := by
        ext; change (jval + 3) % (8 * k) = d
        dsimp [jval, walkLen]
        split_ifs with h0
        · have : 8 * k - 3 + 3 = 8 * k := by omega
          rw [this, Nat.mod_self]; exact h0.symm
        · have hge3 : 3 ≤ d := by omega
          have : d - 3 + 3 = d := by omega
          rw [this, Nat.mod_eq_of_lt (i - p).2]
      rw [hdiff, add_sub_cancel]
    have hstep := congrFun hEq ⟨jval, hjlt⟩
    dsimp [toWalk'] at hstep
    convert hstep using 2 <;> exact Subtype.ext hpos.symm
  have hmaps : (C.image (dropTwo p)).image toWalk' ⊆ W walkLen := by
    intro f hf
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
    dsimp [toWalk', dropTwo]
    have : NeZero (8 * k) := ⟨by omega⟩
    change G.Adj (x (p + Fin.ofNat (8 * k) (j.1 + 3))) (x (p + Fin.ofNat (8 * k) (j.1 + 1 + 3)))
    have hsucc : p + Fin.ofNat (8 * k) (j.1 + 1 + 3) = (p + Fin.ofNat (8 * k) (j.1 + 3)) + 1 := by
      rw [show j.1 + 1 + 3 = (j.1 + 3) + 1 by omega, fin_ofNat_add, ← add_assoc]; rfl
    rw [hsucc]
    exact hC x hxC _
  have hcard : (C.image (dropTwo p)).card ≤ (W walkLen).card := by
    rw [← Finset.card_image_of_injective _ hinj']
    exact Finset.card_le_card hmaps
  exact (Nat.cast_le (α := ℝ).mpr hcard).trans (hW_card walkLen)

/-- Helper for Lemma 2.13: upper bound on non-injective `8k`-walks in `F`. -/
private lemma few_c4_badV_bound {V : Type} [Fintype V] (F : SimpleGraph V)
    {ε K_F : ℝ} (hε0 : 0 < ε) (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hm_ge2 : 2 ≤ Fintype.card V)
    (hm2 : (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * (Fintype.card V : ℝ) ^ (1 - (4 * (k : ℝ)) / 3) ≤
      ((1 : ℝ) / 4) ^ (8 * k))
    (hdF : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤ 2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hΔF : ∀ v : V, (F.degree v : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) :
    let r := 4 * k
    ((Finset.univ.filter fun x : Fin (8 * k) → V =>
        (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x).card : ℝ) ≤
      Matrix.trace (adjMat F ^ (r + r)) / 4 := by
  dsimp only
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let m : ℝ := Fintype.card V
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let r := 4 * k
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hm_ge1 : 1 ≤ m := Nat.one_le_cast.mpr (by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have : NeZero r := ⟨by omega⟩
  have : NeZero (2 * r) := ⟨by omega⟩
  have : NeZero (8 * k) := ⟨by omega⟩
  have htr_ge : dF ^ (8 * k) ≤ Matrix.trace (adjMat F ^ (r + r)) := by
    have h := trace_even_ge_avg_deg_pow F r
    simpa [r, dF, m, show 2 * (4 * k) = 8 * k by omega] using h
  have htr_pos : 0 < Matrix.trace (adjMat F ^ (r + r)) := lt_of_lt_of_le (pow_pos hdF_pos _) htr_ge
  let badV := Finset.univ.filter fun x : Fin (8 * k) → V =>
    (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x
  have hbv := bad_vertex_cycles_le F (K_F * dF) hΔF (by positivity) r (by omega)
  have h2r : 2 * r = 8 * k := by omega
  have hbadV_eq : badV.card = (Finset.univ.filter fun x : Fin (2 * r) → V =>
      (∀ i : Fin (2 * r), F.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x).card := by
    let eL : Fin (8 * k) ≃ Fin (2 * r) := finCongr h2r.symm
    have heL1 : ∀ i : Fin (8 * k), eL (i + 1) = eL i + 1 := fun i => by
      ext; simp only [eL, finCongr_apply, Fin.val_cast, Fin.val_add,
        fin_val_one_of_gt (by omega : 1 < 8 * k), fin_val_one_of_gt (by omega : 1 < 2 * r), h2r]
    refine Finset.card_bij (fun x _ i => x (eL.symm i)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hc, hni⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, fun hi => hni fun a b hab => ?_⟩
      · dsimp only
        have hsucc : eL.symm (i + 1) = eL.symm i + 1 := by
          apply eL.injective; rw [eL.apply_symm_apply, heL1, eL.apply_symm_apply]
        rw [hsucc]; exact hc _
      · have hEq : eL a = eL b := hi (by simpa using hab)
        exact eL.injective hEq
    · intro x₁ _ x₂ _ hEq; funext i; simpa using congrFun hEq (eL i)
    · intro y hy
      obtain ⟨hc, hni⟩ := (Finset.mem_filter.mp hy).2
      refine ⟨fun i => y (eL i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, fun hi => hni fun a b hab => ?_⟩, ?_⟩
      · dsimp only; rw [heL1]; exact hc _
      · have hEq : eL.symm a = eL.symm b := hi (by simpa using hab)
        exact eL.symm.injective hEq
      · funext i; simp
  have hpow : (badV.card : ℝ) ^ (8 * k) ≤ (Matrix.trace (adjMat F ^ (r + r)) / 4) ^ (8 * k) := by
    have h1 : (badV.card : ℝ) ^ (8 * k) ≤
        (256 * (k : ℝ) ^ 3 * K_F * dF) ^ (4 * k) * m * (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 1) := by
      have hcoef : 4 * (r : ℝ) ^ 3 * (K_F * dF) = 256 * (k : ℝ) ^ 3 * K_F * dF := by
        dsimp [r]; push_cast; ring
      rw [hbadV_eq, ← h2r, ← hcoef]
      exact hbv
    have hdF_m : m ^ ((4 * (k : ℝ)) / 3) ≤ dF ^ (4 * k) := by
      have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm_pos _).le hdF (by positivity : (0 : ℝ) ≤ (4 * k : ℕ))
      rw [← Real.rpow_mul hm_pos.le, Real.rpow_natCast] at h
      refine le_trans ?_ h
      exact Real.rpow_le_rpow_of_exponent_le hm_ge1 (by push_cast; nlinarith)
    rw [div_pow, show (4 : ℝ) ^ (8 * k) = ((1 / 4 : ℝ) ^ (8 * k))⁻¹ by rw [one_div, inv_pow, inv_inv],
      div_eq_mul_inv, inv_inv]
    have hgoal : (256 * (k : ℝ) ^ 3 * K_F * dF) ^ (4 * k) * m ≤
        ((1 : ℝ) / 4) ^ (8 * k) * Matrix.trace (adjMat F ^ (r + r)) := by
      calc (256 * (k : ℝ) ^ 3 * K_F * dF) ^ (4 * k) * m
          = (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * m * dF ^ (4 * k) := by rw [mul_pow]; ring
        _ = (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * (m ^ (1 - (4 * (k : ℝ)) / 3) * m ^ ((4 * (k : ℝ)) / 3)) *
            dF ^ (4 * k) := by rw [← Real.rpow_add hm_pos, sub_add_cancel, Real.rpow_one]
        _ ≤ (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * m ^ (1 - (4 * (k : ℝ)) / 3) * dF ^ (4 * k) * dF ^ (4 * k) := by
            have hnn : 0 ≤ (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * m ^ (1 - (4 * (k : ℝ)) / 3) := by positivity
            have := mul_le_mul_of_nonneg_left hdF_m hnn
            have := mul_le_mul_of_nonneg_right this (pow_nonneg hdF_pos.le (4 * k))
            linarith
        _ = ((256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * m ^ (1 - (4 * (k : ℝ)) / 3)) * dF ^ (8 * k) := by
            rw [show 8 * k = 4 * k + 4 * k by omega, pow_add]; ring
        _ ≤ ((1 : ℝ) / 4) ^ (8 * k) * dF ^ (8 * k) :=
            mul_le_mul_of_nonneg_right hm2 (pow_nonneg hdF_pos.le _)
        _ ≤ ((1 : ℝ) / 4) ^ (8 * k) * Matrix.trace (adjMat F ^ (r + r)) :=
            mul_le_mul_of_nonneg_left htr_ge (by positivity)
    calc (badV.card : ℝ) ^ (8 * k)
        ≤ ((256 * (k : ℝ) ^ 3 * K_F * dF) ^ (4 * k) * m) * (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 1) := h1
      _ ≤ (((1 : ℝ) / 4) ^ (8 * k) * Matrix.trace (adjMat F ^ (r + r))) *
            (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 1) :=
          mul_le_mul_of_nonneg_right hgoal (pow_nonneg htr_pos.le _)
      _ = (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k) * ((1 : ℝ) / 4) ^ (8 * k) := by
          rw [mul_assoc, ← pow_succ', show (8 * k - 1) + 1 = 8 * k by omega]; ring
  exact le_of_pow_le_pow_left₀ (by omega : 8 * k ≠ 0) (by positivity) hpow

/-- Helper for Lemma 2.13: upper bound on high-codegree `8k`-walks in `F`. -/
private lemma few_c4_badE_bound {V : Type} [Fintype V] (F : SimpleGraph V)
    {ε K_F : ℝ} (_hε0 : 0 < ε) (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hm_ge2 : 2 ≤ Fintype.card V)
    (hm3 : (192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k) * (Fintype.card V : ℝ) ^ (2 - 2 * (k : ℝ) * ε) ≤
      ((1 : ℝ) / 4) ^ (8 * k))
    (hdF : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤ 2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hΔF : ∀ v : V, (F.degree v : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))
    (s_codeg : ℕ)
    (hsEdge_bound : ∀ u w : V, F.Adj u w →
      (((F.neighborFinset w).filter fun z =>
        s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).card : ℝ) ≤
        3 * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) / (Fintype.card V : ℝ) ^ (ε / 2)) :
    let r := 4 * k
    ((Finset.univ.filter fun x : Fin (8 * k) → V =>
        (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧
        ∃ i : Fin (8 * k), s_codeg < ((F.neighborFinset (x i)) ∩ (F.neighborFinset (x (i + 2)))).card).card : ℝ) ≤
      Matrix.trace (adjMat F ^ (r + r)) / 4 := by
  dsimp only
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let m : ℝ := Fintype.card V
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let sEdge : ℝ := 3 * dF / m ^ (ε / 2)
  let r := 4 * k
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have : NeZero r := ⟨by omega⟩
  have : NeZero (2 * r) := ⟨by omega⟩
  have : NeZero (8 * k) := ⟨by omega⟩
  have htr_ge : dF ^ (8 * k) ≤ Matrix.trace (adjMat F ^ (r + r)) := by
    have h := trace_even_ge_avg_deg_pow F r
    simpa [r, dF, m, show 2 * (4 * k) = 8 * k by omega] using h
  have htr_pos : 0 < Matrix.trace (adjMat F ^ (r + r)) := lt_of_lt_of_le (pow_pos hdF_pos _) htr_ge
  let badE := Finset.univ.filter fun x : Fin (8 * k) → V =>
    (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧
    ∃ i : Fin (8 * k), s_codeg < ((F.neighborFinset (x i)) ∩ (F.neighborFinset (x (i + 2)))).card
  have hbe := bad_codeg_cycles_le F (K_F * dF) sEdge s_codeg hΔF (by positivity) (by positivity)
    hsEdge_bound r (by omega)
  have h2r : 2 * r = 8 * k := by omega
  have hbadE_eq : badE.card = (Finset.univ.filter fun x : Fin (2 * r) → V =>
      (∀ i : Fin (2 * r), F.Adj (x i) (x (i + 1))) ∧
      ∃ i : Fin (2 * r), s_codeg < ((F.neighborFinset (x i)) ∩ (F.neighborFinset (x (i + 2)))).card).card := by
    let eL : Fin (8 * k) ≃ Fin (2 * r) := finCongr h2r.symm
    have heL1 : ∀ i : Fin (8 * k), eL (i + 1) = eL i + 1 := fun i => by
      ext; simp only [eL, finCongr_apply, Fin.val_cast, Fin.val_add,
        fin_val_one_of_gt (by omega : 1 < 8 * k), fin_val_one_of_gt (by omega : 1 < 2 * r), h2r]
    have heL2 : ∀ i : Fin (8 * k), eL (i + 2) = eL i + 2 := fun i => by
      have h2a : (2 : Fin (8 * k)).val = 2 := by change 2 % (8 * k) = 2; exact Nat.mod_eq_of_lt (by omega)
      have h2b : (2 : Fin (2 * r)).val = 2 := by change 2 % (2 * r) = 2; exact Nat.mod_eq_of_lt (by omega)
      ext; simp only [eL, finCongr_apply, Fin.val_cast, Fin.val_add, h2a, h2b, h2r]
    refine Finset.card_bij (fun x _ i => x (eL.symm i)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hc, i0, hi0⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, eL i0, ?_⟩
      · dsimp only
        have hsucc : eL.symm (i + 1) = eL.symm i + 1 := by
          apply eL.injective; rw [eL.apply_symm_apply, heL1, eL.apply_symm_apply]
        rw [hsucc]; exact hc _
      · dsimp only
        have h2s : eL.symm (eL i0 + 2) = i0 + 2 := by
          apply eL.injective; rw [eL.apply_symm_apply, heL2]
        have hce : ((F.neighborFinset (x (eL.symm (eL i0)))) ∩
            (F.neighborFinset (x (eL.symm (eL i0 + 2))))).card =
            ((F.neighborFinset (x i0)) ∩ (F.neighborFinset (x (i0 + 2)))).card := by
          congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, Equiv.symm_apply_apply, h2s]
        rwa [hce]
    · intro x₁ _ x₂ _ hEq; funext i; simpa using congrFun hEq (eL i)
    · intro y hy
      obtain ⟨hc, i0, hi0⟩ := (Finset.mem_filter.mp hy).2
      refine ⟨fun i => y (eL i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, eL.symm i0, ?_⟩, ?_⟩
      · dsimp only; rw [heL1]; exact hc _
      · dsimp only
        have hce : ((F.neighborFinset (y (eL (eL.symm i0)))) ∩
            (F.neighborFinset (y (eL (eL.symm i0 + 2))))).card =
            ((F.neighborFinset (y i0)) ∩ (F.neighborFinset (y (i0 + 2)))).card := by
          congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, heL2, Equiv.apply_symm_apply]
        rwa [hce]
      · funext i; simp
  have hpow : (badE.card : ℝ) ^ (8 * k) ≤ (Matrix.trace (adjMat F ^ (r + r)) / 4) ^ (8 * k) := by
    have h1 : (badE.card : ℝ) ^ (8 * k) ≤
        (192 * (k : ℝ) ^ 2 * K_F ^ 3 * dF ^ 4 / m ^ (ε / 2)) ^ (4 * k) * m ^ 2 *
          (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 2) := by
      have hcoef : 4 * (r : ℝ) ^ 2 * sEdge * (K_F * dF) ^ 3 =
          192 * (k : ℝ) ^ 2 * K_F ^ 3 * dF ^ 4 / m ^ (ε / 2) := by
        dsimp [r, sEdge]; push_cast; ring
      rw [hbadE_eq, ← h2r, ← hcoef]
      exact hbe
    have hgoal : (192 * (k : ℝ) ^ 2 * K_F ^ 3 * dF ^ 4 / m ^ (ε / 2)) ^ (4 * k) * m ^ 2 ≤
        ((1 : ℝ) / 4) ^ (8 * k) * (Matrix.trace (adjMat F ^ (r + r))) ^ 2 := by
      have hmpow : (m ^ (ε / 2)) ^ (4 * k) = m ^ (2 * (k : ℝ) * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le]; congr 1; push_cast; ring
      have hdiv_m : m ^ 2 / m ^ (2 * (k : ℝ) * ε) = m ^ (2 - 2 * (k : ℝ) * ε) := by
        rw [Real.rpow_sub hm_pos, Real.rpow_two]
      calc (192 * (k : ℝ) ^ 2 * K_F ^ 3 * dF ^ 4 / m ^ (ε / 2)) ^ (4 * k) * m ^ 2
          = ((192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k) * (m ^ 2 / m ^ (2 * (k : ℝ) * ε))) *
              (dF ^ (8 * k)) ^ 2 := by
            rw [div_pow, mul_pow, hmpow, ← pow_mul, ← pow_mul, show 4 * (4 * k) = 8 * k * 2 by omega,
              pow_mul]
            ring
        _ = ((192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k) * m ^ (2 - 2 * (k : ℝ) * ε)) *
              (dF ^ (8 * k)) ^ 2 := by rw [hdiv_m]
        _ ≤ ((1 : ℝ) / 4) ^ (8 * k) * (dF ^ (8 * k)) ^ 2 :=
            mul_le_mul_of_nonneg_right hm3 (sq_nonneg _)
        _ ≤ ((1 : ℝ) / 4) ^ (8 * k) * (Matrix.trace (adjMat F ^ (r + r))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hdF_pos.le _) htr_ge 2) (by positivity)
    rw [div_pow, show (4 : ℝ) ^ (8 * k) = ((1 / 4 : ℝ) ^ (8 * k))⁻¹ by rw [one_div, inv_pow, inv_inv],
      div_eq_mul_inv, inv_inv]
    calc (badE.card : ℝ) ^ (8 * k)
        ≤ ((192 * (k : ℝ) ^ 2 * K_F ^ 3 * dF ^ 4 / m ^ (ε / 2)) ^ (4 * k) * m ^ 2) *
            (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 2) := h1
      _ ≤ (((1 : ℝ) / 4) ^ (8 * k) * (Matrix.trace (adjMat F ^ (r + r))) ^ 2) *
            (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k - 2) :=
          mul_le_mul_of_nonneg_right hgoal (pow_nonneg htr_pos.le _)
      _ = (Matrix.trace (adjMat F ^ (r + r))) ^ (8 * k) * ((1 : ℝ) / 4) ^ (8 * k) := by
          rw [mul_assoc, ← pow_add, show 2 + (8 * k - 2) = 8 * k by omega]; ring
  exact le_of_pow_le_pow_left₀ (by omega : 8 * k ≠ 0) (by positivity) hpow

/-- Helper for Lemma 2.13: bound high-codegree neighbors per edge `u ~ w` from the `C_4` load. -/
private lemma few_c4_sEdge_bound {V : Type} [Fintype V] (F : SimpleGraph V)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 12) (hm_ge2 : 2 ≤ Fintype.card V)
    (hm1 : (4 : ℝ) ≤ (Fintype.card V : ℝ) ^ (2 * ε))
    (hdF : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤ 2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hc4 : ∀ e ∈ F.edgeFinset, (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
      (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ (4 : ℕ) /
        (Fintype.card V : ℝ) ^ (1 + 3 * ε / 2)) :
    let m : ℝ := Fintype.card V
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    let s_codeg : ℕ := ⌊dF ^ (3 : ℕ) / m ^ (1 + ε)⌋₊
    ∀ u w : V, F.Adj u w →
      (((F.neighborFinset w).filter fun z =>
          s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).card : ℝ) ≤
        3 * dF / m ^ (ε / 2) := by
  dsimp only
  let m : ℝ := Fintype.card V
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hm_ge1 : 1 ≤ m := Nat.one_le_cast.mpr (by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have hdF_cubed : m ^ (1 + 3 * ε) ≤ dF ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm_pos _).le hdF (by norm_num : (0 : ℝ) ≤ (3 : ℕ))
    rw [← Real.rpow_mul hm_pos.le, Real.rpow_natCast] at h
    have hex : ((1 : ℝ) / 3 + ε) * ((3 : ℕ) : ℝ) = 1 + 3 * ε := by push_cast; ring
    rwa [hex] at h
  let sReal : ℝ := dF ^ (3 : ℕ) / m ^ (1 + ε)
  have hsReal_ge : m ^ (2 * ε) ≤ sReal := by
    dsimp [sReal]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hm_pos _), ← Real.rpow_add hm_pos]
    have : 2 * ε + (1 + ε) = 1 + 3 * ε := by ring
    rwa [this]
  have hsReal_ge4 : 4 ≤ sReal := hm1.trans hsReal_ge
  let s_codeg : ℕ := ⌊sReal⌋₊
  have hs_ge_half : sReal / 2 ≤ (s_codeg : ℝ) := by
    have hlt := Nat.lt_floor_add_one sReal; linarith
  have hs_pos : 0 < (s_codeg : ℝ) := by linarith
  intro u w huw
  let Z := ((F.neighborFinset w).filter fun z =>
      s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).erase u
  have hZ_cnt : (Z.card : ℝ) * (s_codeg : ℝ) ≤
      (((orderedC4 F).filter (c4HasEdge s(u, w))).card : ℝ) := by
    let pairs := Z.sigma fun z => ((F.neighborFinset u) ∩ (F.neighborFinset z)).erase w
    have hpinj : Set.InjOn (fun p : Σ _ : V, V => (u, w, p.1, p.2)) (pairs : Set (Σ _ : V, V)) := by
      rintro ⟨z₁, y₁⟩ _ ⟨z₂, y₂⟩ _ hEq
      simp only [Prod.mk.injEq] at hEq
      exact Sigma.ext hEq.2.2.1 (heq_of_eq hEq.2.2.2)
    have hpmaps : pairs.image (fun p : Σ _ : V, V => (u, w, p.1, p.2)) ⊆
        (orderedC4 F).filter (c4HasEdge s(u, w)) := by
      intro q hq
      obtain ⟨⟨z, y⟩, hzy, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hzZ, hyN⟩ := Finset.mem_sigma.mp hzy
      have hzu : z ≠ u := (Finset.mem_erase.mp hzZ).1
      have hzw : F.Adj w z := (mem_neighborFinset _ _ _).mp (Finset.mem_filter.mp (Finset.mem_erase.mp hzZ).2).1
      have hyw : y ≠ w := (Finset.mem_erase.mp hyN).1
      have hyu : F.Adj u y := (mem_neighborFinset _ _ _).mp (Finset.mem_inter.mp (Finset.mem_erase.mp hyN).2).1
      have hyz : F.Adj z y := (mem_neighborFinset _ _ _).mp (Finset.mem_inter.mp (Finset.mem_erase.mp hyN).2).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        huw.ne, hzu.symm, hyu.ne, hzw.ne, hyw.symm, hyz.ne, huw, hzw, hyz, hyu.symm⟩, Or.inl rfl⟩
    have hcard_p : Z.card * s_codeg ≤ pairs.card := by
      rw [Finset.card_sigma]
      calc Z.card * s_codeg = ∑ _z ∈ Z, s_codeg := by simp
        _ ≤ ∑ z ∈ Z, (((F.neighborFinset u) ∩ (F.neighborFinset z)).erase w).card := by
            apply Finset.sum_le_sum; intro z hz
            have hgt := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
            by_cases hw : w ∈ (F.neighborFinset u) ∩ (F.neighborFinset z)
            · rw [Finset.card_erase_of_mem hw]; omega
            · rw [Finset.erase_eq_of_notMem hw]; omega
    have hle : Z.card * s_codeg ≤ ((orderedC4 F).filter (c4HasEdge s(u, w))).card :=
      hcard_p.trans (by rw [← Finset.card_image_of_injOn hpinj]; exact Finset.card_le_card hpmaps)
    exact_mod_cast hle
  have hZ_le : (Z.card : ℝ) ≤ 2 * dF / m ^ (ε / 2) := by
    have he_mem : s(u, w) ∈ F.edgeFinset := mem_edgeFinset.mpr huw
    have h1 := hZ_cnt.trans (hc4 s(u, w) he_mem)
    rw [← le_div_iff₀ hs_pos] at h1
    calc (Z.card : ℝ) ≤ (dF ^ (4 : ℕ) / m ^ (1 + 3 * ε / 2)) / (s_codeg : ℝ) := h1
      _ ≤ (dF ^ (4 : ℕ) / m ^ (1 + 3 * ε / 2)) / (sReal / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hs_ge_half
      _ = 2 * dF / m ^ (ε / 2) := by
          dsimp [sReal]
          have hpow : m ^ (1 + 3 * ε / 2) = m ^ (1 + ε) * m ^ (ε / 2) := by
            rw [← Real.rpow_add hm_pos]; congr 1; ring
          rw [hpow]
          have h1p : m ^ (1 + ε) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
          have h2p : m ^ (ε / 2) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
          field_simp [hdF_pos.ne', h1p, h2p]
  have hadd1 : (((F.neighborFinset w).filter fun z =>
      s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).card : ℝ) ≤ (Z.card : ℝ) + 1 := by
    have hnat : ((F.neighborFinset w).filter fun z =>
        s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).card ≤ Z.card + 1 := by
      dsimp [Z]
      by_cases hu : u ∈ (F.neighborFinset w).filter fun z =>
          s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card
      · rw [Finset.card_erase_of_mem hu]; have := Finset.card_pos.mpr ⟨u, hu⟩; omega
      · rw [Finset.erase_eq_of_notMem hu]; omega
    exact_mod_cast hnat
  have h1_le : (1 : ℝ) ≤ dF / m ^ (ε / 2) := by
    rw [one_le_div (Real.rpow_pos_of_pos hm_pos _)]
    exact (Real.rpow_le_rpow_of_exponent_le hm_ge1 (by linarith)).trans hdF
  have hsum_s : 2 * dF / m ^ (ε / 2) + dF / m ^ (ε / 2) = 3 * dF / m ^ (ε / 2) := by ring
  linarith

/-- Lemma 2.13 (Few 4-cycles): under `d_F ≥ m^(1/3 + ε)`, `Δ ≤ K_F d_F`, and every edge in at most
`d_F^4 / m^(1 + 3ε/2)` ordered 4-cycles, `F` admits a nonempty `m^(-ε/2)`-good set of `8k`-cycles. -/
private theorem few_c4_betaGood {ε K_F : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 12) (hKF : 1 ≤ K_F)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hkε : 2 / ε ≤ (k : ℝ)) :
    ∃ M₀ : ℕ, ∀ (V : Type) [Fintype V] (F : SimpleGraph V),
      M₀ ≤ Fintype.card V →
      let m : ℝ := Fintype.card V
      let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
      m ^ ((1 : ℝ) / 3 + ε) ≤ dF →
      (∀ v : V, (F.degree v : ℝ) ≤ K_F * dF) →
      (∀ e ∈ F.edgeFinset, (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
        dF ^ (4 : ℕ) / m ^ (1 + 3 * ε / 2)) →
      ∃ C : Finset (Fin (8 * k) → V), C.Nonempty ∧ IsBetaGood F (m ^ (-ε / 2)) C := by
  -- Choose `M₀` large enough for the 4 asymptotic inequalities in `m`:
  have h1 : ∀ᶠ m : ℕ in atTop, (4 : ℝ) ≤ (m : ℝ) ^ (2 * ε) := by
    have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ (2 * ε)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 4
  have h2 : ∀ᶠ m : ℕ in atTop,
      (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) * (m : ℝ) ^ (1 - (4 * (k : ℝ)) / 3) ≤
        ((1 : ℝ) / 4) ^ (8 * k) := by
    have hexp : 1 - (4 * (k : ℝ)) / 3 < 0 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have ht : Tendsto (fun m : ℕ => (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k) *
        (m : ℝ) ^ (1 - (4 * (k : ℝ)) / 3)) atTop (nhds 0) := by
      have hrp : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 - (4 * (k : ℝ)) / 3)) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < -(1 - (4 * (k : ℝ)) / 3))).comp
          tendsto_natCast_atTop_atTop).congr fun m => by
            dsimp only [Function.comp_apply]; congr 1; ring
      simpa using (tendsto_const_nhds (x := (256 * (k : ℝ) ^ 3 * K_F) ^ (4 * k))).mul hrp
    exact ht.eventually (ge_mem_nhds (by positivity))
  have h3 : ∀ᶠ m : ℕ in atTop,
      (192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k) * (m : ℝ) ^ (2 - 2 * (k : ℝ) * ε) ≤
        ((1 : ℝ) / 4) ^ (8 * k) := by
    have hexp : 2 - 2 * (k : ℝ) * ε < 0 := by
      have h2k : 2 ≤ (k : ℝ) * ε := (div_le_iff₀ hε0).mp hkε
      linarith
    have ht : Tendsto (fun m : ℕ => (192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k) *
        (m : ℝ) ^ (2 - 2 * (k : ℝ) * ε)) atTop (nhds 0) := by
      have hrp : Tendsto (fun m : ℕ => (m : ℝ) ^ (2 - 2 * (k : ℝ) * ε)) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < -(2 - 2 * (k : ℝ) * ε))).comp
          tendsto_natCast_atTop_atTop).congr fun m => by
            dsimp only [Function.comp_apply]; congr 1; ring
      simpa using (tendsto_const_nhds (x := (192 * (k : ℝ) ^ 2 * K_F ^ 3) ^ (4 * k))).mul hrp
    exact ht.eventually (ge_mem_nhds (by positivity))
  have h4 : ∀ᶠ m : ℕ in atTop,
      (32 * (k : ℝ) * K_F ^ (8 * k - 3)) * (m : ℝ) ^ (-ε / 2) ≤ 1 := by
    have ht : Tendsto (fun m : ℕ => (32 * (k : ℝ) * K_F ^ (8 * k - 3)) *
        (m : ℝ) ^ (-ε / 2)) atTop (nhds 0) := by
      have hrp : Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε / 2)) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (by positivity : 0 < ε / 2)).comp
          tendsto_natCast_atTop_atTop).congr fun m => by
            dsimp only [Function.comp_apply]; congr 1; ring
      simpa using (tendsto_const_nhds (x := 32 * (k : ℝ) * K_F ^ (8 * k - 3))).mul hrp
    exact ht.eventually (ge_mem_nhds zero_lt_one)
  have hall := (h1.and (h2.and (h3.and (h4.and (eventually_ge_atTop (2 : ℕ))))))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hall
  refine ⟨M₀, fun V _ F hVm => ?_⟩
  obtain ⟨hm1, hm2, hm3, hm4, hm_ge2⟩ := hM₀ (Fintype.card V) hVm
  dsimp only
  intro hdF hΔF hc4
  have hV_ne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let m : ℝ := Fintype.card V
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have hdF_cubed : m ^ (1 + 3 * ε) ≤ dF ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm_pos _).le hdF (by norm_num : (0 : ℝ) ≤ (3 : ℕ))
    rw [← Real.rpow_mul hm_pos.le, Real.rpow_natCast] at h
    have hex : ((1 : ℝ) / 3 + ε) * ((3 : ℕ) : ℝ) = 1 + 3 * ε := by push_cast; ring
    rwa [hex] at h
  -- Set `s_codeg := ⌊dF^3 / m^(1 + ε)⌋₊`:
  let sReal : ℝ := dF ^ (3 : ℕ) / m ^ (1 + ε)
  have hsReal_ge : m ^ (2 * ε) ≤ sReal := by
    dsimp [sReal]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hm_pos _), ← Real.rpow_add hm_pos]
    have : 2 * ε + (1 + ε) = 1 + 3 * ε := by ring
    rwa [this]
  have hsReal_ge4 : 4 ≤ sReal := hm1.trans hsReal_ge
  let s_codeg : ℕ := ⌊sReal⌋₊
  have hs_le : (s_codeg : ℝ) ≤ sReal := Nat.floor_le (by linarith)
  have hs_ge_half : sReal / 2 ≤ (s_codeg : ℝ) := by
    have hlt := Nat.lt_floor_add_one sReal
    linarith
  have hs_pos : 0 < (s_codeg : ℝ) := by linarith
  have hsEdge_bound : ∀ u w : V, F.Adj u w →
      (((F.neighborFinset w).filter fun z =>
          s_codeg < ((F.neighborFinset u) ∩ (F.neighborFinset z)).card).card : ℝ) ≤
        3 * dF / m ^ (ε / 2) :=
    few_c4_sEdge_bound F hε0 hε1 hm_ge2 hm1 hdF hc4
  -- Count all homomorphic `8k`-cycles and remove vertex-bad and codeg-bad ones:
  let r := 4 * k
  have hr3 : 3 ≤ r := by omega
  let A := adjMat F
  have htr_ge : dF ^ (8 * k) ≤ Matrix.trace (A ^ (r + r)) := by
    have h := trace_even_ge_avg_deg_pow F r
    simpa [r, dF, m, show 2 * (4 * k) = 8 * k by omega] using h
  have htr_pos : 0 < Matrix.trace (A ^ (r + r)) := lt_of_lt_of_le (pow_pos hdF_pos _) htr_ge
  let allCyc := Finset.univ.filter fun x : Fin (8 * k) → V => ∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))
  let badV := Finset.univ.filter fun x : Fin (8 * k) → V =>
    (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧ ¬ Function.Injective x
  let badE := Finset.univ.filter fun x : Fin (8 * k) → V =>
    (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧
    ∃ i : Fin (8 * k), s_codeg < ((F.neighborFinset (x i)) ∩ (F.neighborFinset (x (i + 2)))).card
  have hall_eq : (allCyc.card : ℝ) = Matrix.trace (A ^ (r + r)) := by
    have := hom_cycle_card_eq_trace F (8 * k) (by omega)
    simpa [allCyc, r, show 4 * k + 4 * k = 8 * k by omega] using this
  have hbadV_le : (badV.card : ℝ) ≤ Matrix.trace (A ^ (r + r)) / 4 :=
    few_c4_badV_bound F hε0 hKF hk hm_ge2 hm2 hdF hΔF
  have hbadE_le : (badE.card : ℝ) ≤ Matrix.trace (A ^ (r + r)) / 4 :=
    few_c4_badE_bound F hε0 hKF hk hm_ge2 hm3 hdF hΔF s_codeg hsEdge_bound
  -- Good set `C := allCyc \ (badV ∪ badE)`:
  let C := allCyc \ (badV ∪ badE)
  have hC_card : Matrix.trace (A ^ (r + r)) / 2 ≤ (C.card : ℝ) := by
    have hnat : allCyc.card ≤ C.card + (badV.card + badE.card) := by
      have h1 : allCyc ⊆ C ∪ (badV ∪ badE) := fun x hx => by
        by_cases h : x ∈ badV ∪ badE
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
      exact (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hR : (allCyc.card : ℝ) ≤ (C.card : ℝ) + ((badV.card : ℝ) + (badE.card : ℝ)) := by exact_mod_cast hnat
    linarith
  have hC_ne : C.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < (C.card : ℝ) := by linarith
    exact_mod_cast this)
  have hC_mem : ∀ x ∈ C, (∀ i : Fin (8 * k), F.Adj (x i) (x (i + 1))) ∧ Function.Injective x ∧
      ∀ i : Fin (8 * k), ((F.neighborFinset (x i)) ∩ (F.neighborFinset (x (i + 2)))).card ≤ s_codeg := by
    intro x hx
    obtain ⟨hxA, hxNot⟩ := Finset.mem_sdiff.mp hx
    have hcyc := (Finset.mem_filter.mp hxA).2
    have hnotV : x ∉ badV := fun h => hxNot (Finset.mem_union_left _ h)
    have hnotE : x ∉ badE := fun h => hxNot (Finset.mem_union_right _ h)
    refine ⟨hcyc, ?_, ?_⟩
    · by_contra hni; exact hnotV (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcyc, hni⟩)
    · intro i; by_contra hgt; push Not at hgt
      exact hnotE (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hcyc, i, hgt⟩)
  refine ⟨C, hC_ne, (s_codeg : ℝ), hs_pos, fun x hx => ⟨(hC_mem x hx).2.1, (hC_mem x hx).1⟩, ?_, ?_⟩
  · -- Condition 2: fixing all `j ≠ i` fixes `x (i - 1)` and `x (i + 1)`, leaving `≤ s_codeg` choices:
    intro y hy i
    have hsub : (C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).image (fun x => x i) ⊆
        (F.neighborFinset (y (i - 1))) ∩ (F.neighborFinset (y (i + 1))) := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hxC, hxy⟩ := Finset.mem_filter.mp hx
      have hne1 : i - 1 ≠ i := by
        intro h; have := congrArg (· - i) h; simp at this
      have hne2 : i + 1 ≠ i := by
        intro h; have := congrArg (· - i) h; simp at this
      have hprev : F.Adj (y (i - 1)) (x i) := by
        rw [← hxy (i - 1) hne1]; simpa using (hC_mem x hxC).1 (i - 1)
      have hnext : F.Adj (y (i + 1)) (x i) := by
        rw [← hxy (i + 1) hne2]; exact ((hC_mem x hxC).1 i).symm
      exact Finset.mem_inter.mpr ⟨(mem_neighborFinset F _ _).mpr hprev, (mem_neighborFinset F _ _).mpr hnext⟩
    have hinj : Set.InjOn (fun x : Fin (8 * k) → V => x i)
        ((C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j) : Set (Fin (8 * k) → V)) := by
      intro x₁ hx₁ x₂ hx₂ hEq
      funext j
      by_cases hj : j = i
      · subst hj; exact hEq
      · exact ((Finset.mem_filter.mp hx₁).2 j hj).trans ((Finset.mem_filter.mp hx₂).2 j hj).symm
    have hcard : (C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).card ≤ s_codeg := by
      rw [← Finset.card_image_of_injOn hinj]
      refine (Finset.card_le_card hsub).trans ?_
      have h2 : (i - 1) + 2 = i + 1 := by
        have h2eq : (2 : Fin (8 * k)) = 1 + 1 := by
          ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; rfl
        rw [h2eq]; abel
      have hce : ((F.neighborFinset (y (i - 1))) ∩ (F.neighborFinset (y (i + 1)))).card =
          ((F.neighborFinset (y (i - 1))) ∩ (F.neighborFinset (y ((i - 1) + 2)))).card := by
        congr 1; ext w; simp only [Finset.mem_inter, mem_neighborFinset, h2]
      rw [hce]
      exact (hC_mem y hy).2.2 (i - 1)
    exact_mod_cast hcard
  · -- Condition 3: at most `m * (K_F dF)^(8k - 3) ≤ m^(-ε/2) * |C| / (16 k s_codeg)`!
    intro p
    have hproj := card_dropTwo_walks_le (by omega : 1 ≤ k) F (K_F * dF) hΔF
      (mul_nonneg (by linarith) hdF_pos.le) C (fun x hx => (hC_mem x hx).1) p
    refine hproj.trans ?_
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hk_pos) hs_pos)]
    have hC_ge : dF ^ (8 * k) / 2 ≤ (C.card : ℝ) := (div_le_div_of_nonneg_right htr_ge (by norm_num)).trans hC_card
    have hm_s : m * (s_codeg : ℝ) ≤ dF ^ (3 : ℕ) * m ^ (-ε) := by
      have h1 : m * (s_codeg : ℝ) ≤ m * (dF ^ (3 : ℕ) / m ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left hs_le hm_pos.le
      have h2 : m * (dF ^ (3 : ℕ) / m ^ (1 + ε)) = dF ^ (3 : ℕ) * m ^ (-ε) := by
        rw [Real.rpow_add hm_pos, Real.rpow_one, Real.rpow_neg hm_pos.le]
        have hme : m ^ ε ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
        field_simp [hm_pos.ne', hme]
      exact h1.trans_eq h2
    have hpow_split : dF ^ (8 * k - 3) * dF ^ (3 : ℕ) = dF ^ (8 * k) := by
      rw [← pow_add, show (8 * k - 3) + 3 = 8 * k by omega]
    have hnn1 : 0 ≤ (16 * (k : ℝ) * K_F ^ (8 * k - 3)) * dF ^ (8 * k - 3) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk_pos.le) (pow_nonneg (by linarith) _))
        (pow_nonneg hdF_pos.le _)
    have hnn2 : 0 ≤ m ^ (-ε / 2) * (dF ^ (8 * k) / 2) :=
      mul_nonneg (Real.rpow_pos_of_pos hm_pos _).le (div_nonneg (pow_nonneg hdF_pos.le _) (by norm_num))
    calc m * (K_F * dF) ^ (8 * k - 3) * (16 * (k : ℝ) * (s_codeg : ℝ))
        = (16 * (k : ℝ) * K_F ^ (8 * k - 3)) * dF ^ (8 * k - 3) * (m * (s_codeg : ℝ)) := by
          rw [mul_pow]; ring
      _ ≤ (16 * (k : ℝ) * K_F ^ (8 * k - 3)) * dF ^ (8 * k - 3) * (dF ^ (3 : ℕ) * m ^ (-ε)) :=
          mul_le_mul_of_nonneg_left hm_s hnn1
      _ = ((32 * (k : ℝ) * K_F ^ (8 * k - 3)) * m ^ (-ε / 2)) * (m ^ (-ε / 2) * (dF ^ (8 * k) / 2)) := by
          have hadd : m ^ (-ε / 2) * m ^ (-ε / 2) = m ^ (-ε) := by
            rw [← Real.rpow_add hm_pos]; congr 1; ring
          rw [← hpow_split, ← hadd]; ring
      _ ≤ 1 * (m ^ (-ε / 2) * (dF ^ (8 * k) / 2)) :=
          mul_le_mul_of_nonneg_right hm4 hnn2
      _ ≤ m ^ (-ε / 2) * (C.card : ℝ) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hC_ge (Real.rpow_pos_of_pos hm_pos _).le

/- ### Section 6: Bipartite Dyadic Regularization (Lemma 2.3) and Many 4-Cycles (Lemma 2.14) -/

/-- Standard bipartite cut: every graph `G` has disjoint sets `U₁, U₂` whose crossing subgraph has
at least `e(G) / 2` edges. -/
private lemma exists_bipartite_cut {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ U₁ U₂ : Finset V, Disjoint U₁ U₂ ∧
      G.edgeFinset.card ≤ 2 * (∑ u ∈ U₁, (U₂.filter (G.Adj u)).card) := by
  -- Average over all `c : V → Bool`: each undirected edge crosses in half of all 2-colorings.
  let cross (c : V → Bool) : ℕ :=
    ∑ u ∈ (Finset.univ.filter fun x => c x = true),
      ((Finset.univ.filter fun y => c y = false).filter (G.Adj u)).card
  have hcross_eq : ∀ c : V → Bool, 2 * cross c =
      ∑ u : V, ∑ v : V, if G.Adj u v ∧ c u ≠ c v then 1 else 0 := by
    intro c
    dsimp [cross]
    have h1 : ∑ u ∈ (Finset.univ.filter fun x => c x = true),
        ((Finset.univ.filter fun y => c y = false).filter (G.Adj u)).card =
        ∑ u : V, ∑ v : V, if G.Adj u v ∧ c u = true ∧ c v = false then 1 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro u _
      by_cases hu : c u = true
      · rw [if_pos hu, Finset.card_filter, Finset.sum_filter]
        exact Finset.sum_congr rfl fun v _ => by
          by_cases hv : c v = false <;> by_cases huv : G.Adj u v <;> simp [hu, hv, huv]
      · simp only [if_neg hu]
        exact (Finset.sum_eq_zero fun v _ => by simp [hu]).symm
    have h2 : ∑ u : V, ∑ v : V, (if G.Adj u v ∧ c u = false ∧ c v = true then 1 else 0) =
        ∑ u : V, ∑ v : V, (if G.Adj u v ∧ c u = true ∧ c v = false then 1 else 0) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        by_cases huv : G.Adj u v
        · simp [huv, huv.symm, and_comm]
        · have hvu : ¬ G.Adj v u := fun h => huv h.symm
          simp [huv, hvu]
    rw [h1, two_mul]
    conv_lhs => arg 1; rw [← h2]
    conv_rhs =>
      arg 2; ext u; arg 2; ext v
      rw [show (if G.Adj u v ∧ c u ≠ c v then (1 : ℕ) else 0) =
        (if G.Adj u v ∧ c u = false ∧ c v = true then 1 else 0) +
        (if G.Adj u v ∧ c u = true ∧ c v = false then 1 else 0) by
        cases c u <;> cases c v <;> by_cases huv : G.Adj u v <;> simp [huv]]
    simp only [Finset.sum_add_distrib]
  have hsum_all : ∑ c : V → Bool, (2 * cross c) =
      (Fintype.card (V → Bool)) * G.edgeFinset.card := by
    have hpair : ∀ u v : V, G.Adj u v →
        2 * (∑ c : V → Bool, if G.Adj u v ∧ c u ≠ c v then 1 else 0) =
        Fintype.card (V → Bool) := by
      intro u v huv
      let flip (c : V → Bool) : V → Bool := fun x => if x = u then !c x else c x
      have hinv : Function.Involutive flip := fun c => by
        funext x; by_cases hx : x = u <;> simp [flip, hx]
      have hswap : (∑ c : V → Bool, if G.Adj u v ∧ flip c u ≠ flip c v then (1 : ℕ) else 0) =
          ∑ c : V → Bool, if G.Adj u v ∧ c u ≠ c v then 1 else 0 :=
        Fintype.sum_equiv hinv.toPerm _ _ (fun _ => rfl)
      calc 2 * (∑ c : V → Bool, if G.Adj u v ∧ c u ≠ c v then 1 else 0)
          = (∑ c : V → Bool, if G.Adj u v ∧ flip c u ≠ flip c v then 1 else 0) +
            (∑ c : V → Bool, if G.Adj u v ∧ c u ≠ c v then 1 else 0) := by rw [two_mul, hswap]
        _ = ∑ c : V → Bool, ((if G.Adj u v ∧ flip c u ≠ flip c v then 1 else 0) +
            (if G.Adj u v ∧ c u ≠ c v then 1 else 0)) := (Finset.sum_add_distrib).symm
        _ = ∑ _c : V → Bool, 1 := by
            apply Finset.sum_congr rfl; intro c _
            simp only [flip, if_pos rfl, if_neg huv.ne.symm, huv, true_and]
            cases c u <;> cases c v <;> decide
        _ = Fintype.card (V → Bool) := by simp
    have hdouble : 2 * ∑ c : V → Bool, (2 * cross c) =
        2 * ((Fintype.card (V → Bool)) * G.edgeFinset.card) := by
      simp_rw [hcross_eq]
      calc 2 * ∑ c : V → Bool, ∑ u : V, ∑ v : V, (if G.Adj u v ∧ c u ≠ c v then 1 else 0)
          = ∑ c : V → Bool, ∑ u : V, ∑ v : V, 2 * (if G.Adj u v ∧ c u ≠ c v then 1 else 0) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun u _ => Finset.mul_sum _ _ _
        _ = ∑ u : V, ∑ v : V, 2 * ∑ c : V → Bool, (if G.Adj u v ∧ c u ≠ c v then 1 else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro u _
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
        _ = ∑ u : V, ∑ v : V, (if G.Adj u v then Fintype.card (V → Bool) else 0) := by
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
            by_cases huv : G.Adj u v
            · rw [if_pos huv]; exact hpair u v huv
            · simp [huv]
        _ = Fintype.card (V → Bool) * ∑ u : V, G.degree u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u _
            rw [← card_neighborFinset_eq_degree, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
            congr 1; congr 1; ext v; simp [mem_neighborFinset]
        _ = 2 * ((Fintype.card (V → Bool)) * G.edgeFinset.card) := by
            rw [G.sum_degrees_eq_twice_card_edges]; ring
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble
  obtain ⟨c, _, hcmax⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool)) cross Finset.univ_nonempty
  have hle : Fintype.card (V → Bool) * G.edgeFinset.card ≤ Fintype.card (V → Bool) * (2 * cross c) := by
    rw [← hsum_all]
    calc ∑ c' : V → Bool, 2 * cross c'
        ≤ ∑ _c' : V → Bool, 2 * cross c := Finset.sum_le_sum fun c' _ => Nat.mul_le_mul_left 2 (hcmax c' (Finset.mem_univ _))
      _ = Fintype.card (V → Bool) * (2 * cross c) := by simp
  have hge := Nat.le_of_mul_le_mul_left hle Fintype.card_pos
  refine ⟨Finset.univ.filter fun x => c x = true, Finset.univ.filter fun y => c y = false, ?_, hge⟩
  rw [Finset.disjoint_left]
  intro x h1 h2
  have ht := (Finset.mem_filter.mp h1).2
  have hf := (Finset.mem_filter.mp h2).2
  rw [ht] at hf; exact Bool.noConfusion hf

/-- Lemma 2.3 (Bipartite dyadic regularization): any graph `G` on `N ≥ 2` vertices with
`e(G) > 0` (`d = 2 e(G) / N`) contains a nonempty bipartite subgraph `G' ≤ G` with disjoint
parts `X₁, X₂` and parameters `D₁, D₂ ≥ d / 5` such that `D₁ / (8 L^2) ≤ deg_{G'}(x) ≤ D₁` on
`X₁` and `D₂ / (8 L^2) ≤ deg_{G'}(y) ≤ D₂` on `X₂`, where `L = Nat.log 2 N + 2`. -/
private theorem bipartite_dyadic_reg {V : Type} [Fintype V]
    (G : SimpleGraph V) (hN : 2 ≤ Fintype.card V) (he : 0 < G.edgeFinset.card) :
    let N := Fintype.card V
    let L : ℕ := Nat.log 2 N + 2
    let d : ℝ := 2 * (G.edgeFinset.card : ℝ) / (N : ℝ)
    ∃ (G' : SimpleGraph V) (X₁ X₂ : Finset V) (D₁ D₂ : ℕ),
      G' ≤ G ∧ Disjoint X₁ X₂ ∧ X₁.Nonempty ∧ X₂.Nonempty ∧
      d / 5 ≤ (D₁ : ℝ) ∧ d / 5 ≤ (D₂ : ℝ) ∧
      (∀ u v, G'.Adj u v → (u ∈ X₁ ∧ v ∈ X₂) ∨ (u ∈ X₂ ∧ v ∈ X₁)) ∧
      (∀ x ∈ X₁, (D₁ : ℝ) / (8 * (L : ℝ) ^ 2) ≤ ((X₂.filter (G'.Adj x)).card : ℝ) ∧
        (G'.degree x : ℝ) ≤ (D₁ : ℝ)) ∧
      (∀ y ∈ X₂, (D₂ : ℝ) / (8 * (L : ℝ) ^ 2) ≤ ((X₁.filter (G'.Adj y)).card : ℝ) ∧
        (G'.degree y : ℝ) ≤ (D₂ : ℝ)) ∧
      (∀ v : V, (G'.degree v : ℝ) ≤ max (D₁ : ℝ) (D₂ : ℝ)) := by
  let N := Fintype.card V
  let L : ℕ := Nat.log 2 N + 2
  let d : ℝ := 2 * (G.edgeFinset.card : ℝ) / (N : ℝ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < L := by omega
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have heR : (0 : ℝ) < (G.edgeFinset.card : ℝ) := by exact_mod_cast he
  -- Step 1: Bipartite cut `U₁, U₂` with `2 * e_cut ≥ e(G)`:
  obtain ⟨U₁, U₂, hUdisj, hUcut⟩ := exists_bipartite_cut G
  let Rcut (u v : V) : Prop := G.Adj u v ∧ ((u ∈ U₁ ∧ v ∈ U₂) ∨ (u ∈ U₂ ∧ v ∈ U₁))
  have hRcut_sym : ∀ ⦃u v⦄, Rcut u v → Rcut v u := by
    rintro u v ⟨huv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨huv.symm, Or.inr ⟨h2, h1⟩⟩
    · exact ⟨huv.symm, Or.inl ⟨h2, h1⟩⟩
  have hRcut_irr : ∀ u, ¬ Rcut u u := fun u h => G.irrefl h.1
  have hsum_cut : ∑ u ∈ (U₁ ∪ U₂), (((U₁ ∪ U₂).filter (Rcut u)).card : ℝ) =
      2 * ((∑ u ∈ U₁, (U₂.filter (G.Adj u)).card : ℕ) : ℝ) := by
    rw [Finset.sum_union hUdisj]
    have h1 : ∀ u ∈ U₁, ((U₁ ∪ U₂).filter (Rcut u)).card = (U₂.filter (G.Adj u)).card := by
      intro u hu
      congr 1; ext v
      simp only [Finset.mem_filter, Finset.mem_union, Rcut]
      have hu2 : u ∉ U₂ := Finset.disjoint_left.mp hUdisj hu
      constructor
      · rintro ⟨_, huv, ⟨_, hv2⟩ | ⟨hu2', _⟩⟩
        · exact ⟨hv2, huv⟩
        · exact (hu2 hu2').elim
      · rintro ⟨hv2, huv⟩
        exact ⟨Or.inr hv2, huv, Or.inl ⟨hu, hv2⟩⟩
    have h2 : ∀ v ∈ U₂, ((U₁ ∪ U₂).filter (Rcut v)).card = (U₁.filter (G.Adj v)).card := by
      intro v hv
      congr 1; ext u
      simp only [Finset.mem_filter, Finset.mem_union, Rcut]
      have hv1 : v ∉ U₁ := Finset.disjoint_right.mp hUdisj hv
      constructor
      · rintro ⟨_, hvu, ⟨hv1', _⟩ | ⟨_, hu1⟩⟩
        · exact (hv1 hv1').elim
        · exact ⟨hu1, hvu⟩
      · rintro ⟨hu1, hvu⟩
        exact ⟨Or.inl hu1, hvu, Or.inr ⟨hv, hu1⟩⟩
    have hsym : ∑ v ∈ U₂, (U₁.filter (G.Adj v)).card = ∑ u ∈ U₁, (U₂.filter (G.Adj u)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        by_cases h : G.Adj u v
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    have hs1 : ∑ u ∈ U₁, (((U₁ ∪ U₂).filter (Rcut u)).card : ℝ) = ∑ u ∈ U₁, ((U₂.filter (G.Adj u)).card : ℝ) :=
      Finset.sum_congr rfl fun u hu => by rw [h1 u hu]
    have hs2 : ∑ v ∈ U₂, (((U₁ ∪ U₂).filter (Rcut v)).card : ℝ) = ∑ v ∈ U₂, ((U₁.filter (G.Adj v)).card : ℝ) :=
      Finset.sum_congr rfl fun v hv => by rw [h2 v hv]
    rw [hs1, hs2, ← Nat.cast_sum, ← Nat.cast_sum, hsym, two_mul]
  -- Step 2: Core with minimum degree `≥ d / 5` using `exists_degree_core` from `R2`!
  have hdense1 : 2 * ∑ _u ∈ (U₁ ∪ U₂), (d / 5) <
      ∑ u ∈ (U₁ ∪ U₂), (((U₁ ∪ U₂).filter (Rcut u)).card : ℝ) := by
    rw [hsum_cut]
    have hUcard : ((U₁ ∪ U₂).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast Finset.card_le_univ (U₁ ∪ U₂)
    have hUcutR : (G.edgeFinset.card : ℝ) ≤ 2 * ((∑ u ∈ U₁, (U₂.filter (G.Adj u)).card : ℕ) : ℝ) := by
      exact_mod_cast hUcut
    have h1 : 2 * ∑ _u ∈ (U₁ ∪ U₂), (d / 5) ≤ (4 / 5 : ℝ) * (G.edgeFinset.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc 2 * (((U₁ ∪ U₂).card : ℝ) * (d / 5))
          ≤ 2 * ((N : ℝ) * (d / 5)) := by gcongr
        _ = (4 / 5 : ℝ) * (G.edgeFinset.card : ℝ) := by dsimp [d]; field_simp [hNpos.ne']; ring
    linarith
  obtain ⟨T, hTsub, hTne, hTdeg⟩ := exists_degree_core (U₁ ∪ U₂) Rcut (fun _ => d / 5)
    hRcut_sym hRcut_irr (by convert hdense1)
  let T₁ := T ∩ U₁
  let T₂ := T ∩ U₂
  have hTdisj : Disjoint T₁ T₂ := hUdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hTunion : T₁ ∪ T₂ = T := by
    ext x; simp only [T₁, T₂, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx; rcases Finset.mem_union.mp (hTsub hx) with h1 | h2
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, h2⟩
  have hdegT₁ : ∀ x ∈ T₁, (T.filter (Rcut x)).card = (T₂.filter (G.Adj x)).card := by
    intro x hx
    have hxT := (Finset.mem_inter.mp hx).1
    have hx1 := (Finset.mem_inter.mp hx).2
    have hx2 : x ∉ U₂ := Finset.disjoint_left.mp hUdisj hx1
    congr 1; ext y
    simp only [Finset.mem_filter, T₂, Finset.mem_inter, Rcut]
    constructor
    · rintro ⟨hyT, hxy, ⟨_, hy2⟩ | ⟨hx2', _⟩⟩
      · exact ⟨⟨hyT, hy2⟩, hxy⟩
      · exact (hx2 hx2').elim
    · rintro ⟨⟨hyT, hy2⟩, hxy⟩
      exact ⟨hyT, hxy, Or.inl ⟨hx1, hy2⟩⟩
  have hdegT₂ : ∀ y ∈ T₂, (T.filter (Rcut y)).card = (T₁.filter (G.Adj y)).card := by
    intro y hy
    have hyT := (Finset.mem_inter.mp hy).1
    have hy2 := (Finset.mem_inter.mp hy).2
    have hy1 : y ∉ U₁ := Finset.disjoint_right.mp hUdisj hy2
    congr 1; ext x
    simp only [Finset.mem_filter, T₁, Finset.mem_inter, Rcut]
    constructor
    · rintro ⟨hxT, hyx, ⟨hy1', _⟩ | ⟨_, hx1⟩⟩
      · exact (hy1 hy1').elim
      · exact ⟨⟨hxT, hx1⟩, hyx⟩
    · rintro ⟨⟨hxT, hx1⟩, hyx⟩
      exact ⟨hxT, hyx, Or.inr ⟨hy2, hx1⟩⟩
  -- Every vertex in `T₁` and `T₂` has `≥ d / 5 > 0` neighbors in the opposite part:
  have hdpos : 0 < d / 5 := by dsimp [d]; positivity
  have hdegT₁_ge : ∀ x ∈ T₁, d / 5 ≤ ((T₂.filter (G.Adj x)).card : ℝ) := fun x hx => by
    have h1 : d / 5 ≤ ((T.filter (Rcut x)).card : ℝ) := by
      convert hTdeg x (Finset.mem_inter.mp hx).1
    rwa [hdegT₁ x hx] at h1
  have hdegT₂_ge : ∀ y ∈ T₂, d / 5 ≤ ((T₁.filter (G.Adj y)).card : ℝ) := fun y hy => by
    have h1 : d / 5 ≤ ((T.filter (Rcut y)).card : ℝ) := by
      convert hTdeg y (Finset.mem_inter.mp hy).1
    rwa [hdegT₂ y hy] at h1
  have hdegT₁_pos : ∀ x ∈ T₁, 1 ≤ (T₂.filter (G.Adj x)).card := fun x hx => by
    have : (0 : ℝ) < ((T₂.filter (G.Adj x)).card : ℝ) := lt_of_lt_of_le hdpos (hdegT₁_ge x hx)
    exact_mod_cast this
  have hdegT₂_pos : ∀ y ∈ T₂, 1 ≤ (T₁.filter (G.Adj y)).card := fun y hy => by
    have : (0 : ℝ) < ((T₁.filter (G.Adj y)).card : ℝ) := lt_of_lt_of_le hdpos (hdegT₂_ge y hy)
    exact_mod_cast this
  -- Step 3: Dyadic buckets `A i` (`i ∈ range L`) and `B j` (`j ∈ range L`):
  let A (i : ℕ) : Finset V := T₁.filter fun x => Nat.log 2 (T₂.filter (G.Adj x)).card = i
  let B (j : ℕ) : Finset V := T₂.filter fun y => Nat.log 2 (T₁.filter (G.Adj y)).card = j
  have hlog_lt : ∀ k : ℕ, k ≤ N → Nat.log 2 k < L := fun k hk => by
    have h1 : Nat.log 2 k ≤ Nat.log 2 N := Nat.log_mono_right hk
    omega
  have hA_cov : ∀ x ∈ T₁, ∃ i ∈ Finset.range L, x ∈ A i := fun x hx =>
    ⟨Nat.log 2 (T₂.filter (G.Adj x)).card, Finset.mem_range.mpr (hlog_lt _ (Finset.card_le_univ _)),
      Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hB_cov : ∀ y ∈ T₂, ∃ j ∈ Finset.range L, y ∈ B j := fun y hy =>
    ⟨Nat.log 2 (T₁.filter (G.Adj y)).card, Finset.mem_range.mpr (hlog_lt _ (Finset.card_le_univ _)),
      Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
  let eAB (i j : ℕ) : ℕ := ∑ x ∈ A i, (B j |>.filter (G.Adj x)).card
  let eT : ℕ := ∑ x ∈ T₁, (T₂.filter (G.Adj x)).card
  have heT_pos : 0 < eT := by
    obtain ⟨z, hzT⟩ := hTne
    rw [← hTunion] at hzT
    rcases Finset.mem_union.mp hzT with h1 | h2
    · exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨z, h1, hdegT₁_pos z h1⟩
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp (hdegT₂_pos z h2)
      have hx1 := (Finset.mem_filter.mp hx).1
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨x, hx1, hdegT₁_pos x hx1⟩
  have heT_sym : eT = ∑ y ∈ T₂, (T₁.filter (G.Adj y)).card := by
    dsimp [eT]; simp only [Finset.card_filter]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by
      by_cases h : G.Adj x y
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hsum_eAB : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, eAB i j = eT := by
    have hdisjA : (Finset.range L : Set ℕ).PairwiseDisjoint A := fun i _ j _ hne => by
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hdisjB : (Finset.range L : Set ℕ).PairwiseDisjoint B := fun i _ j _ hne => by
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro y h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hunionA : (Finset.range L).biUnion A = T₁ := by
      ext x; simp only [Finset.mem_biUnion]
      exact ⟨fun ⟨_, _, hx⟩ => (Finset.mem_filter.mp hx).1, hA_cov x⟩
    have hunionB : (Finset.range L).biUnion B = T₂ := by
      ext y; simp only [Finset.mem_biUnion]
      exact ⟨fun ⟨_, _, hy⟩ => (Finset.mem_filter.mp hy).1, hB_cov y⟩
    dsimp [eAB, eT]
    have h1 : ∀ i, ∑ j ∈ Finset.range L, ∑ x ∈ A i, ((B j).filter (G.Adj x)).card =
        ∑ x ∈ A i, (T₂.filter (G.Adj x)).card := by
      intro i
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.card_biUnion (fun j₁ h1 j₂ h2 hne =>
        (hdisjB h1 h2 hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      congr 1; rw [← hunionB, Finset.filter_biUnion]
    simp_rw [h1]
    rw [← Finset.sum_biUnion hdisjA, hunionA]
  have hsumA_le : ∑ i ∈ Finset.range L, ((A i).card : ℝ) * (2 : ℝ) ^ i ≤ (eT : ℝ) := by
    have hnat : ∑ i ∈ Finset.range L, (A i).card * 2 ^ i ≤ eT := by
      have hdisjA : (Finset.range L : Set ℕ).PairwiseDisjoint A := fun i _ j _ hne => by
        dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hunionA : (Finset.range L).biUnion A = T₁ := by
        ext x; simp only [Finset.mem_biUnion]
        exact ⟨fun ⟨_, _, hx⟩ => (Finset.mem_filter.mp hx).1, hA_cov x⟩
      dsimp [eT]
      rw [← hunionA, Finset.sum_biUnion hdisjA]
      apply Finset.sum_le_sum; intro i _
      calc (A i).card * 2 ^ i = ∑ _x ∈ A i, 2 ^ i := by simp
        _ ≤ ∑ x ∈ A i, (T₂.filter (G.Adj x)).card := by
            apply Finset.sum_le_sum; intro x hx
            obtain ⟨hx1, hlog⟩ := Finset.mem_filter.mp hx
            rw [← hlog]
            exact Nat.pow_log_le_self 2 (by have := hdegT₁_pos x hx1; omega)
    exact_mod_cast hnat
  have hsumB_le : ∑ j ∈ Finset.range L, ((B j).card : ℝ) * (2 : ℝ) ^ j ≤ (eT : ℝ) := by
    have hnat : ∑ j ∈ Finset.range L, (B j).card * 2 ^ j ≤ eT := by
      have hdisjB : (Finset.range L : Set ℕ).PairwiseDisjoint B := fun i _ j _ hne => by
        dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro y h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hunionB : (Finset.range L).biUnion B = T₂ := by
        ext y; simp only [Finset.mem_biUnion]
        exact ⟨fun ⟨_, _, hy⟩ => (Finset.mem_filter.mp hy).1, hB_cov y⟩
      rw [heT_sym, ← hunionB, Finset.sum_biUnion hdisjB]
      apply Finset.sum_le_sum; intro j _
      calc (B j).card * 2 ^ j = ∑ _y ∈ B j, 2 ^ j := by simp
        _ ≤ ∑ y ∈ B j, (T₁.filter (G.Adj y)).card := by
            apply Finset.sum_le_sum; intro y hy
            obtain ⟨hy2, hlog⟩ := Finset.mem_filter.mp hy
            rw [← hlog]
            exact Nat.pow_log_le_self 2 (by have := hdegT₂_pos y hy2; omega)
    exact_mod_cast hnat
  -- Weighted pigeonhole for `(i, j) ∈ range L × range L`:
  have hex_ij : ∃ i ∈ Finset.range L, ∃ j ∈ Finset.range L,
      ((A i).card : ℝ) * ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2)) +
      ((B j).card : ℝ) * ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2)) < (eAB i j : ℝ) := by
    by_contra hall
    push Not at hall
    have htot := Finset.sum_le_sum fun i (hi : i ∈ Finset.range L) =>
      Finset.sum_le_sum fun j (hj : j ∈ Finset.range L) => hall i hi j hj
    have hRHS : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, (eAB i j : ℝ) = (eT : ℝ) := by
      exact_mod_cast hsum_eAB
    have hLHS : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        (((A i).card : ℝ) * ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2)) +
         ((B j).card : ℝ) * ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2))) ≤ (eT : ℝ) / 2 := by
      simp_rw [Finset.sum_add_distrib]
      have hpart1 : ∑ i ∈ Finset.range L, ∑ _j ∈ Finset.range L,
          ((A i).card : ℝ) * ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2)) ≤ (eT : ℝ) / 4 := by
        calc ∑ i ∈ Finset.range L, ∑ _j ∈ Finset.range L,
                ((A i).card : ℝ) * ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2))
            = ((L : ℝ) / (4 * (L : ℝ) ^ 2)) * ∑ i ∈ Finset.range L, ((A i).card : ℝ) * (2 : ℝ) ^ i := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by simp; ring
          _ ≤ ((L : ℝ) / (4 * (L : ℝ) ^ 2)) * (eT : ℝ) := by gcongr
          _ = (eT : ℝ) / (4 * (L : ℝ)) := by field_simp [hLposR.ne']
          _ ≤ (eT : ℝ) / 4 := by
              apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num)
              have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
              linarith
      have hpart2 : ∑ _i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          ((B j).card : ℝ) * ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2)) ≤ (eT : ℝ) / 4 := by
        calc ∑ _i ∈ Finset.range L, ∑ j ∈ Finset.range L,
                ((B j).card : ℝ) * ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2))
            = ((L : ℝ) / (4 * (L : ℝ) ^ 2)) * ∑ j ∈ Finset.range L, ((B j).card : ℝ) * (2 : ℝ) ^ j := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ ≤ ((L : ℝ) / (4 * (L : ℝ) ^ 2)) * (eT : ℝ) := by gcongr
          _ = (eT : ℝ) / (4 * (L : ℝ)) := by field_simp [hLposR.ne']
          _ ≤ (eT : ℝ) / 4 := by
              apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num)
              have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
              linarith
      linarith
    have heTR : (0 : ℝ) < (eT : ℝ) := by exact_mod_cast heT_pos
    linarith
  obtain ⟨i, _, j, _, hij⟩ := hex_ij
  -- Step 4: Apply `exists_degree_core` to `A i ∪ B j` with asymmetric weights!
  have hABdisj : Disjoint (A i) (B j) := hTdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  let RAB (u v : V) : Prop := G.Adj u v ∧ ((u ∈ A i ∧ v ∈ B j) ∨ (u ∈ B j ∧ v ∈ A i))
  have hRAB_sym : ∀ ⦃u v⦄, RAB u v → RAB v u := by
    rintro u v ⟨huv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨huv.symm, Or.inr ⟨h2, h1⟩⟩
    · exact ⟨huv.symm, Or.inl ⟨h2, h1⟩⟩
  have hRAB_irr : ∀ u, ¬ RAB u u := fun u h => G.irrefl h.1
  let wAB (u : V) : ℝ :=
    if u ∈ A i then (2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2) else (2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2)
  have hdense2 : 2 * ∑ u ∈ (A i ∪ B j), wAB u <
      ∑ u ∈ (A i ∪ B j), (((A i ∪ B j).filter (RAB u)).card : ℝ) := by
    have hsumW : ∑ u ∈ (A i ∪ B j), wAB u =
        ((A i).card : ℝ) * ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2)) +
        ((B j).card : ℝ) * ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2)) := by
      rw [Finset.sum_union hABdisj]
      congr 1
      · calc ∑ u ∈ A i, wAB u = ∑ _u ∈ A i, ((2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2)) :=
              Finset.sum_congr rfl fun u hu => if_pos hu
          _ = _ := by simp
      · calc ∑ v ∈ B j, wAB v = ∑ _v ∈ B j, ((2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2)) :=
              Finset.sum_congr rfl fun v hv => if_neg (Finset.disjoint_right.mp hABdisj hv)
          _ = _ := by simp
    have hsumE : ∑ u ∈ (A i ∪ B j), (((A i ∪ B j).filter (RAB u)).card : ℝ) = 2 * (eAB i j : ℝ) := by
      rw [Finset.sum_union hABdisj]
      have h1 : ∀ u ∈ A i, ((A i ∪ B j).filter (RAB u)).card = ((B j).filter (G.Adj u)).card := by
        intro u hu
        congr 1; ext v
        simp only [Finset.mem_filter, Finset.mem_union, RAB]
        have huB : u ∉ B j := Finset.disjoint_left.mp hABdisj hu
        exact ⟨fun ⟨_, huv, h⟩ => h.elim (fun h' => ⟨h'.2, huv⟩) (fun h' => (huB h'.1).elim),
          fun ⟨hvB, huv⟩ => ⟨Or.inr hvB, huv, Or.inl ⟨hu, hvB⟩⟩⟩
      have h2 : ∀ v ∈ B j, ((A i ∪ B j).filter (RAB v)).card = ((A i).filter (G.Adj v)).card := by
        intro v hv
        congr 1; ext u
        simp only [Finset.mem_filter, Finset.mem_union, RAB]
        have hvA : v ∉ A i := Finset.disjoint_right.mp hABdisj hv
        exact ⟨fun ⟨_, hvu, h⟩ => h.elim (fun h' => (hvA h'.1).elim) (fun h' => ⟨h'.2, hvu⟩),
          fun ⟨huA, hvu⟩ => ⟨Or.inl huA, hvu, Or.inr ⟨hv, huA⟩⟩⟩
      have hsym : ∑ v ∈ B j, ((A i).filter (G.Adj v)).card = eAB i j := by
        dsimp [eAB]; simp only [Finset.card_filter]; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          by_cases h : G.Adj u v
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun h' => h h'.symm)]
      have hs1 : ∑ u ∈ A i, (((A i ∪ B j).filter (RAB u)).card : ℝ) = ∑ u ∈ A i, (((B j).filter (G.Adj u)).card : ℝ) :=
        Finset.sum_congr rfl fun u hu => by rw [h1 u hu]
      have hs2 : ∑ v ∈ B j, (((A i ∪ B j).filter (RAB v)).card : ℝ) = ∑ v ∈ B j, (((A i).filter (G.Adj v)).card : ℝ) :=
        Finset.sum_congr rfl fun v hv => by rw [h2 v hv]
      rw [hs1, hs2, ← Nat.cast_sum, ← Nat.cast_sum, hsym, two_mul]
    rw [hsumW, hsumE]; linarith
  obtain ⟨X, hXsub, hXne, hXdeg⟩ := exists_degree_core (A i ∪ B j) RAB wAB hRAB_sym hRAB_irr
    (by convert hdense2)
  let X₁ := X ∩ A i
  let X₂ := X ∩ B j
  have hXdisj : Disjoint X₁ X₂ := hABdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hXunion : X₁ ∪ X₂ = X := by
    ext u; simp only [X₁, X₂, Finset.mem_union, Finset.mem_inter]
    exact ⟨fun h => h.elim And.left And.left,
      fun hu => (Finset.mem_union.mp (hXsub hu)).elim (fun h1 => Or.inl ⟨hu, h1⟩) (fun h2 => Or.inr ⟨hu, h2⟩)⟩
  let G' : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ ((u ∈ X₁ ∧ v ∈ X₂) ∨ (u ∈ X₂ ∧ v ∈ X₁))
      symm := ⟨by rintro u v ⟨huv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩; exact ⟨huv.symm, Or.inr ⟨h2, h1⟩⟩; exact ⟨huv.symm, Or.inl ⟨h2, h1⟩⟩⟩
      loopless := ⟨fun u h => G.irrefl h.1⟩ }
  have hdegX₁ : ∀ x ∈ X₁, (X₂.filter (G'.Adj x)).card = (X.filter (RAB x)).card := by
    intro x hx
    have hxX := (Finset.mem_inter.mp hx).1
    have hxA := (Finset.mem_inter.mp hx).2
    have hxB : x ∉ B j := Finset.disjoint_left.mp hABdisj hxA
    congr 1; ext y
    simp only [Finset.mem_filter, X₂, Finset.mem_inter, G', RAB]
    constructor
    · rintro ⟨⟨hyX, hyB⟩, hxy, _⟩
      exact ⟨hyX, hxy, Or.inl ⟨hxA, hyB⟩⟩
    · rintro ⟨hyX, hxy, ⟨_, hyB⟩ | ⟨hxB', _⟩⟩
      · exact ⟨⟨hyX, hyB⟩, hxy, Or.inl ⟨hx, hyX, hyB⟩⟩
      · exact (hxB hxB').elim
  have hdegX₂ : ∀ y ∈ X₂, (X₁.filter (G'.Adj y)).card = (X.filter (RAB y)).card := by
    intro y hy
    have hyX := (Finset.mem_inter.mp hy).1
    have hyB := (Finset.mem_inter.mp hy).2
    have hyA : y ∉ A i := Finset.disjoint_right.mp hABdisj hyB
    congr 1; ext x
    simp only [Finset.mem_filter, X₁, Finset.mem_inter, G', RAB]
    constructor
    · rintro ⟨⟨hxX, hxA⟩, hyx, _⟩
      exact ⟨hxX, hyx, Or.inr ⟨hyB, hxA⟩⟩
    · rintro ⟨hxX, hyx, ⟨hyA', _⟩ | ⟨_, hxA⟩⟩
      · exact (hyA hyA').elim
      · exact ⟨⟨hxX, hxA⟩, hyx, Or.inr ⟨hy, hxX, hxA⟩⟩
  have hX₁_lb : ∀ x ∈ X₁, (2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2) ≤ ((X₂.filter (G'.Adj x)).card : ℝ) := by
    intro x hx
    rw [hdegX₁ x hx]
    have h1 : wAB x ≤ ((X.filter (RAB x)).card : ℝ) := by
      convert hXdeg x (Finset.mem_inter.mp hx).1
    simpa [wAB, (Finset.mem_inter.mp hx).2] using h1
  have hX₂_lb : ∀ y ∈ X₂, (2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2) ≤ ((X₁.filter (G'.Adj y)).card : ℝ) := by
    intro y hy
    rw [hdegX₂ y hy]
    have h1 : wAB y ≤ ((X.filter (RAB y)).card : ℝ) := by
      convert hXdeg y (Finset.mem_inter.mp hy).1
    simpa [wAB, Finset.disjoint_right.mp hABdisj (Finset.mem_inter.mp hy).2] using h1
  have hX₁ne : X₁.Nonempty := by
    obtain ⟨z, hzX⟩ := hXne
    rw [← hXunion] at hzX
    rcases Finset.mem_union.mp hzX with h1 | h2
    · exact ⟨z, h1⟩
    · have hpos : (0 : ℝ) < ((X₁.filter (G'.Adj z)).card : ℝ) :=
        lt_of_lt_of_le (by positivity) (hX₂_lb z h2)
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
      exact ⟨x, (Finset.mem_filter.mp hx).1⟩
  have hX₂ne : X₂.Nonempty := by
    obtain ⟨x, hx1⟩ := hX₁ne
    have hpos : (0 : ℝ) < ((X₂.filter (G'.Adj x)).card : ℝ) :=
      lt_of_lt_of_le (by positivity) (hX₁_lb x hx1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
    exact ⟨y, (Finset.mem_filter.mp hy).1⟩
  let D₁ := 2 ^ (i + 1)
  let D₂ := 2 ^ (j + 1)
  have hD₁_ge : d / 5 ≤ (D₁ : ℝ) := by
    obtain ⟨x, hx1⟩ := hX₁ne
    have hxA := (Finset.mem_inter.mp hx1).2
    obtain ⟨hxT₁, hlog⟩ := Finset.mem_filter.mp hxA
    have hlt : (T₂.filter (G.Adj x)).card < 2 ^ (i + 1) := by
      rw [← hlog]; exact Nat.lt_pow_succ_log_self (by decide) _
    exact (hdegT₁_ge x hxT₁).trans (by exact_mod_cast hlt.le)
  have hD₂_ge : d / 5 ≤ (D₂ : ℝ) := by
    obtain ⟨y, hy2⟩ := hX₂ne
    have hyB := (Finset.mem_inter.mp hy2).2
    obtain ⟨hyT₂, hlog⟩ := Finset.mem_filter.mp hyB
    have hlt : (T₁.filter (G.Adj y)).card < 2 ^ (j + 1) := by
      rw [← hlog]; exact Nat.lt_pow_succ_log_self (by decide) _
    exact (hdegT₂_ge y hyT₂).trans (by exact_mod_cast hlt.le)
  have hdeg_X₁_le : ∀ x ∈ X₁, (G'.degree x : ℝ) ≤ (D₁ : ℝ) := by
    intro x hx
    have hxA := (Finset.mem_inter.mp hx).2
    obtain ⟨hxT₁, hlog⟩ := Finset.mem_filter.mp hxA
    have hsub : G'.neighborFinset x ⊆ T₂.filter (G.Adj x) := by
      intro y hy
      obtain ⟨hxy, ⟨_, hy2⟩ | ⟨hx2, _⟩⟩ := (mem_neighborFinset G' x y).mp hy
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hy2).2).1, hxy⟩
      · exact (Finset.disjoint_left.mp hXdisj hx hx2).elim
    have hlt : (T₂.filter (G.Adj x)).card < D₁ := by
      dsimp [D₁]; rw [← hlog]; exact Nat.lt_pow_succ_log_self (by decide) _
    rw [← card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_card hsub).trans hlt.le
  have hdeg_X₂_le : ∀ y ∈ X₂, (G'.degree y : ℝ) ≤ (D₂ : ℝ) := by
    intro y hy
    have hyB := (Finset.mem_inter.mp hy).2
    obtain ⟨hyT₂, hlog⟩ := Finset.mem_filter.mp hyB
    have hsub : G'.neighborFinset y ⊆ T₁.filter (G.Adj y) := by
      intro x hx
      obtain ⟨hyx, ⟨hy1, _⟩ | ⟨_, hx1⟩⟩ := (mem_neighborFinset G' y x).mp hx
      · exact (Finset.disjoint_right.mp hXdisj hy hy1).elim
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hx1).2).1, hyx⟩
    have hlt : (T₁.filter (G.Adj y)).card < D₂ := by
      dsimp [D₂]; rw [← hlog]; exact Nat.lt_pow_succ_log_self (by decide) _
    rw [← card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_card hsub).trans hlt.le
  refine ⟨G', X₁, X₂, D₁, D₂, fun _ _ h => h.1, hXdisj, hX₁ne, hX₂ne, hD₁_ge, hD₂_ge,
    fun _ _ h => h.2, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, by convert hdeg_X₁_le x hx⟩
    have h2eq : (D₁ : ℝ) / (8 * (L : ℝ) ^ 2) = (2 : ℝ) ^ i / (4 * (L : ℝ) ^ 2) := by
      dsimp [D₁]; push_cast; rw [pow_succ]; ring
    rw [h2eq]; convert hX₁_lb x hx
  · intro y hy
    refine ⟨?_, by convert hdeg_X₂_le y hy⟩
    have h2eq : (D₂ : ℝ) / (8 * (L : ℝ) ^ 2) = (2 : ℝ) ^ j / (4 * (L : ℝ) ^ 2) := by
      dsimp [D₂]; push_cast; rw [pow_succ]; ring
    rw [h2eq]; convert hX₂_lb y hy
  · intro v
    by_cases hv1 : v ∈ X₁
    · refine le_trans ?_ (le_max_left (D₁ : ℝ) (D₂ : ℝ))
      refine le_trans (le_of_eq ?_) (hdeg_X₁_le v hv1)
      congr 1; rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      congr 1; ext w; simp only [mem_neighborFinset]
    · by_cases hv2 : v ∈ X₂
      · refine le_trans ?_ (le_max_right (D₁ : ℝ) (D₂ : ℝ))
        refine le_trans (le_of_eq ?_) (hdeg_X₂_le v hv2)
        congr 1; rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        congr 1; ext w; simp only [mem_neighborFinset]
      · have h0 : G'.degree v = 0 := by
          rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro w hw
          rcases ((mem_neighborFinset G' v w).mp hw).2 with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact hv1 h1
          · exact hv2 h2
        have h0R : (G'.degree v : ℝ) ≤ max (D₁ : ℝ) (D₂ : ℝ) := by
          rw [h0, Nat.cast_zero]; exact le_trans (Nat.cast_nonneg _) (le_max_left _ _)
        convert h0R

/-- Helper: `Nat.log 2 m + 2 ≤ 3 * Real.log m` for `m ≥ 8`. -/
private lemma natLog_add_two_le_three_log {m : ℕ} (hm : 8 ≤ m) :
    ((Nat.log 2 m + 2 : ℕ) : ℝ) ≤ 3 * Real.log (m : ℝ) := by
  have h1 : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlogm : (2 : ℝ) ≤ Real.log (m : ℝ) := by
    have h8 : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h3 : 3 * Real.log 2 ≤ Real.log (m : ℝ) := by
      have : Real.log ((2 : ℝ) ^ (3 : ℕ)) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ^ (3 : ℕ) ≤ (m : ℝ))
      rwa [Real.log_pow] at this
    linarith
  have hnl : ((Nat.log 2 m : ℕ) : ℝ) * Real.log 2 ≤ Real.log (m : ℝ) := by
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  push_cast
  nlinarith

/-- Helper: polylogarithmic growth `C * (Real.log m)^p ≤ m^a` for all large `m` (`a > 0`). -/
private lemma eventually_polylog_le_rpow (C a : ℝ) (ha : 0 < a) (p : ℕ) :
    ∀ᶠ m : ℕ in atTop, C * (Real.log (m : ℝ)) ^ p ≤ (m : ℝ) ^ a := by
  have hclean : Tendsto (fun x : ℝ => C * ((Real.log x) ^ p / x ^ a)) atTop (nhds 0) := by
    by_cases hp0 : p = 0
    · subst hp0
      have h0 : Tendsto (fun x : ℝ => C * (1 / x ^ a)) atTop (nhds (C * 0)) :=
        tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop ha).congr' (by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          rw [Real.rpow_neg hx.le, one_div]))
      simpa using h0
    · have h0 := (isLittleO_log_rpow_atTop (show 0 < a / (p : ℝ) by positivity)).tendsto_div_nhds_zero
      have hpow := h0.pow p
      rw [zero_pow hp0] at hpow
      have hmul := (tendsto_const_nhds (x := C)).mul hpow
      rw [mul_zero] at hmul
      exact hmul.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [div_pow, ← Real.rpow_natCast (x ^ (a / (p : ℝ))) p, ← Real.rpow_mul hx.le,
          div_mul_cancel₀ _ (by exact_mod_cast hp0)])
  have hnat := hclean.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℕ)] with m hm1 hmge1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmge1
  have hmpow : 0 < (m : ℝ) ^ a := Real.rpow_pos_of_pos hmpos a
  dsimp only [Function.comp_apply] at hm1
  rw [mul_div_assoc', div_le_one hmpow] at hm1
  exact hm1

/-- Helper (Lemma 2.18): extract a pivot vertex `v`, dyadic codegree scale `s > 0`, and a
symmetric set `𝒟 ⊆ N(v) × V × N(v)` of ordered 4-cycle triples with bounded `y`-fibers. -/
private lemma many_c4_heavy_triples {V : Type} [Fintype V] (F : SimpleGraph V)
    (hm8 : 8 ≤ Fintype.card V)
    (hdF_pos : 0 < 2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hc4 : ∀ e ∈ F.edgeFinset, (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
      (40 * Real.log (Fintype.card V : ℝ) /
        ((Fintype.card V : ℝ) * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) *
        ((orderedC4 F).card : ℝ)) :
    let mN := Fintype.card V
    let m : ℝ := mN
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    let q : ℝ := ((orderedC4 F).card : ℝ)
    let L : ℕ := Nat.log 2 mN + 2
    ∃ (v : V) (s : ℝ) (𝒟 : Finset (V × V × V)),
      0 < s ∧
      q / (2 * m * (L : ℝ)) ≤ (𝒟.card : ℝ) ∧
      (∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟) ∧
      (∀ x y z : V, (x, y, z) ∈ 𝒟 →
        (v, x, y, z) ∈ orderedC4 F ∧
        (((F.neighborFinset v) ∩ (F.neighborFinset y)).card : ℝ) ≤ s ∧
        (((F.neighborFinset x) ∩ (F.neighborFinset z)).card : ℝ) ≤ s ∧
        s / 2 ≤ (((F.neighborFinset v) ∩ (F.neighborFinset y)).card : ℝ) ∧
        2 ≤ ((F.neighborFinset v) ∩ (F.neighborFinset y)).card) ∧
      (∀ x : V,
        (((Finset.univ.filter fun y : V => ∃ z : V, (x, y, z) ∈ 𝒟).card : ℝ)) ≤
          (160 * Real.log m / (m * dF * s)) * q) := by
  dsimp only
  let mN := Fintype.card V
  let m : ℝ := mN
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let q : ℝ := ((orderedC4 F).card : ℝ)
  let L : ℕ := Nat.log 2 mN + 2
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlog_pos : 0 < Real.log m := Real.log_pos (by change (1 : ℝ) < (mN : ℝ); exact_mod_cast (show 1 < mN by omega))
  let codeg (a b : V) : ℕ := ((F.neighborFinset a) ∩ (F.neighborFinset b)).card
  let Q₀ := (orderedC4 F).filter fun t => codeg t.2.1 t.2.2.2 ≤ codeg t.1 t.2.2.1
  have hQ₀_card : q / 2 ≤ (Q₀.card : ℝ) := by
    let rot (t : V × V × V × V) : V × V × V × V := (t.2.1, t.2.2.1, t.2.2.2, t.1)
    have hrot_mem : ∀ t ∈ orderedC4 F, rot t ∈ orderedC4 F := by
      rintro ⟨a, b, c, d⟩ ht
      simp only [orderedC4, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.2.2.2.1, ht.2.2.2.2.1, ht.1.symm, ht.2.2.2.2.2.1, ht.2.1.symm, ht.2.2.1.symm,
        ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.2, ht.2.2.2.2.2.2.1⟩
    have hcov : orderedC4 F ⊆ Q₀ ∪ Q₀.image (fun t => (t.2.2.2, t.1, t.2.1, t.2.2.1)) := by
      intro t ht
      by_cases hle : codeg t.2.1 t.2.2.2 ≤ codeg t.1 t.2.2.1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, hle⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨rot t, ?_, by rcases t with ⟨a,b,c,d⟩; rfl⟩)
        refine Finset.mem_filter.mpr ⟨hrot_mem t ht, ?_⟩
        have hsym : codeg t.2.2.1 t.1 = codeg t.1 t.2.2.1 := by dsimp [codeg]; rw [Finset.inter_comm]
        dsimp [rot]; rw [hsym]; omega
    have hnat : (orderedC4 F).card ≤ 2 * Q₀.card := by
      calc (orderedC4 F).card ≤ (Q₀ ∪ Q₀.image _).card := Finset.card_le_card hcov
        _ ≤ Q₀.card + (Q₀.image _).card := Finset.card_union_le _ _
        _ ≤ Q₀.card + Q₀.card := Nat.add_le_add_left Finset.card_image_le _
        _ = 2 * Q₀.card := by ring
    have hR : q ≤ 2 * (Q₀.card : ℝ) := by dsimp [q]; exact_mod_cast hnat
    linarith
  have hex_v : ∃ v : V, q / (2 * m) ≤ ((Q₀.filter fun t => t.1 = v).card : ℝ) := by
    by_contra hall
    push Not at hall
    have hneV : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
    have hsum := Finset.sum_lt_sum_of_nonempty hneV fun v _ => hall v
    have hpart : ∑ v : V, ((Q₀.filter fun t => t.1 = v).card : ℝ) = (Q₀.card : ℝ) := by
      rw [← Nat.cast_sum]; congr 1
      rw [← Finset.card_biUnion]
      · congr 1; ext t; simp
      · intro v₁ _ v₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro t h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hRHS : ∑ _v : V, q / (2 * m) = q / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [m, mN]; field_simp [hm_pos.ne']
    linarith
  obtain ⟨v, hv_card⟩ := hex_v
  let 𝒟₀ : Finset (V × V × V) := (Q₀.filter fun t => t.1 = v).image fun t => t.2
  have h𝒟₀_card : q / (2 * m) ≤ (𝒟₀.card : ℝ) := by
    have hinj : Set.InjOn (fun t : V × V × V × V => t.2) ((Q₀.filter fun t => t.1 = v) : Set _) := by
      rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 hEq
      have ha1 := (Finset.mem_filter.mp h1).2
      have ha2 := (Finset.mem_filter.mp h2).2
      exact Prod.ext (ha1.trans ha2.symm) hEq
    rw [Finset.card_image_of_injOn hinj]; exact hv_card
  have h𝒟₀_props : ∀ p ∈ 𝒟₀, (v, p.1, p.2.1, p.2.2) ∈ orderedC4 F ∧
      codeg p.1 p.2.2 ≤ codeg v p.2.1 ∧ 2 ≤ codeg v p.2.1 := by
    rintro ⟨x, y, z⟩ hp
    obtain ⟨⟨v', x', y', z'⟩, ht, hEq⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    obtain ⟨htQ, rfl⟩ := Finset.mem_filter.mp ht
    obtain ⟨htC4, hcg⟩ := Finset.mem_filter.mp htQ
    refine ⟨htC4, hcg, ?_⟩
    have hmem : ({x', z'} : Finset V) ⊆ (F.neighborFinset v') ∩ (F.neighborFinset y') := by
      intro w hw
      simp only [orderedC4, Finset.mem_filter, Finset.mem_univ, true_and] at htC4
      rcases Finset.mem_insert.mp hw with rfl | hw2
      · exact Finset.mem_inter.mpr ⟨(mem_neighborFinset F _ _).mpr htC4.2.2.2.2.2.2.1,
          (mem_neighborFinset F _ _).mpr htC4.2.2.2.2.2.2.2.1.symm⟩
      · rw [Finset.mem_singleton.mp hw2]
        exact Finset.mem_inter.mpr ⟨(mem_neighborFinset F _ _).mpr htC4.2.2.2.2.2.2.2.2.2.symm,
          (mem_neighborFinset F _ _).mpr htC4.2.2.2.2.2.2.2.2.1⟩
    have hxz : x' ≠ z' := (Finset.mem_filter.mp htC4).2.2.2.2.2.1
    have h2 : ({x', z'} : Finset V).card = 2 := Finset.card_pair hxz
    exact h2 ▸ Finset.card_le_card hmem
  have hex_i : ∃ i ∈ Finset.range L,
      q / (2 * m * (L : ℝ)) ≤ ((𝒟₀.filter fun p => Nat.log 2 (codeg v p.2.1) = i).card : ℝ) := by
    by_contra hall
    push Not at hall
    have hneL : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hsum := Finset.sum_lt_sum_of_nonempty hneL hall
    have hpart : ∑ i ∈ Finset.range L, ((𝒟₀.filter fun p => Nat.log 2 (codeg v p.2.1) = i).card : ℝ) =
        (𝒟₀.card : ℝ) := by
      rw [← Nat.cast_sum]; congr 1
      rw [← Finset.card_biUnion]
      · congr 1; ext p
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
        exact ⟨fun ⟨_, _, hp, _⟩ => hp, fun hp =>
          ⟨Nat.log 2 (codeg v p.2.1), by
            have hle : codeg v p.2.1 ≤ mN := Finset.card_le_univ _
            have := Nat.log_mono_right (b := 2) hle; dsimp [L]; omega, hp, rfl⟩⟩
      · intro i₁ _ i₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hRHS : ∑ _i ∈ Finset.range L, q / (2 * m * (L : ℝ)) = q / (2 * m) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hL_pos.ne', hm_pos.ne']
    linarith
  obtain ⟨i₀, _, hi₀⟩ := hex_i
  let 𝒟' := 𝒟₀.filter fun p => Nat.log 2 (codeg v p.2.1) = i₀
  let s : ℝ := ((2 ^ (i₀ + 1) : ℕ) : ℝ)
  have hs_pos : 0 < s := by dsimp [s]; positivity
  let 𝒟 : Finset (V × V × V) := 𝒟' ∪ 𝒟'.image fun p => (p.2.2, p.2.1, p.1)
  have h𝒟_card : q / (2 * m * (L : ℝ)) ≤ (𝒟.card : ℝ) :=
    hi₀.trans (by exact_mod_cast Finset.card_le_card Finset.subset_union_left)
  have h𝒟_sym : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟 := by
    intro x y z h
    rcases Finset.mem_union.mp h with h1 | h2
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, y, z), h1, rfl⟩)
    · obtain ⟨⟨a, b, c⟩, habc, hEq⟩ := Finset.mem_image.mp h2
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl, rfl⟩ := hEq
      exact Finset.mem_union_left _ habc
  have h𝒟_props : ∀ x y z : V, (x, y, z) ∈ 𝒟 →
      (v, x, y, z) ∈ orderedC4 F ∧ (codeg v y : ℝ) ≤ s ∧ (codeg x z : ℝ) ≤ s ∧
      s / 2 ≤ (codeg v y : ℝ) ∧ 2 ≤ codeg v y := by
    intro x y z h
    have hbase : ∀ a b c : V, (a, b, c) ∈ 𝒟' →
        (v, a, b, c) ∈ orderedC4 F ∧ (codeg v b : ℝ) ≤ s ∧ (codeg a c : ℝ) ≤ s ∧
        s / 2 ≤ (codeg v b : ℝ) ∧ 2 ≤ codeg v b := by
      intro a b c habc
      obtain ⟨h0, hlog⟩ := Finset.mem_filter.mp habc
      obtain ⟨hc4', hcg, h2⟩ := h𝒟₀_props (a, b, c) h0
      have hlt : codeg v b < 2 ^ (i₀ + 1) := by rw [← hlog]; exact Nat.lt_pow_succ_log_self (by decide) _
      have hge : 2 ^ i₀ ≤ codeg v b := by rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
      have hgeR : s / 2 ≤ (codeg v b : ℝ) := by
        dsimp [s]; push_cast; rw [pow_succ]
        have : (2 : ℝ) ^ i₀ ≤ (codeg v b : ℝ) := by exact_mod_cast hge
        linarith
      have hltR : (codeg v b : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hlt.le
      have hcgR : (codeg a c : ℝ) ≤ (codeg v b : ℝ) := by exact_mod_cast hcg
      exact ⟨hc4', hltR, hcgR.trans hltR, hgeR, h2⟩
    rcases Finset.mem_union.mp h with h1 | h2
    · exact hbase x y z h1
    · obtain ⟨⟨a, b, c⟩, habc, hEq⟩ := Finset.mem_image.mp h2
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl, rfl⟩ := hEq
      obtain ⟨hc4', h1, h2, h3, h4⟩ := hbase a b c habc
      have hc4_rev : (v, c, b, a) ∈ orderedC4 F := by
        simp only [orderedC4, Finset.mem_filter, Finset.mem_univ, true_and] at hc4' ⊢
        exact ⟨hc4'.2.2.1, hc4'.2.1, hc4'.1, hc4'.2.2.2.2.2.1.symm, hc4'.2.2.2.2.1.symm, hc4'.2.2.2.1.symm,
          hc4'.2.2.2.2.2.2.2.2.2.symm, hc4'.2.2.2.2.2.2.2.2.1.symm, hc4'.2.2.2.2.2.2.2.1.symm,
          hc4'.2.2.2.2.2.2.1.symm⟩
      have hcg_sym : codeg c a = codeg a c := by dsimp [codeg]; rw [Finset.inter_comm]
      exact ⟨hc4_rev, h1, hcg_sym ▸ h2, h3, h4⟩
  have h𝒟_cond3 : ∀ x : V,
      (((Finset.univ.filter fun y : V => ∃ z : V, (x, y, z) ∈ 𝒟).card : ℝ)) ≤
        (160 * Real.log m / (m * dF * s)) * q := by
    intro x
    let Yx := Finset.univ.filter fun y : V => ∃ z : V, (x, y, z) ∈ 𝒟
    change (Yx.card : ℝ) ≤ _
    by_cases hYx_ne : Yx.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hYx_ne
      obtain ⟨z₀, hz₀⟩ := (Finset.mem_filter.mp hy₀).2
      have hvx : F.Adj v x := (Finset.mem_filter.mp (h𝒟_props x y₀ z₀ hz₀).1).2.2.2.2.2.2.2.1
      let pairs := Yx.sigma fun y => ((F.neighborFinset v) ∩ (F.neighborFinset y)).erase x
      have hinj : Set.InjOn (fun p : Σ _ : V, V => (v, x, p.1, p.2)) (pairs : Set (Σ _ : V, V)) := by
        rintro ⟨y₁, z₁⟩ _ ⟨y₂, z₂⟩ _ hEq
        simp only [Prod.mk.injEq] at hEq
        exact Sigma.ext hEq.2.2.1 (heq_of_eq hEq.2.2.2)
      have hmaps : pairs.image (fun p : Σ _ : V, V => (v, x, p.1, p.2)) ⊆
          (orderedC4 F).filter (c4HasEdge s(v, x)) := by
        intro t ht
        obtain ⟨⟨y, z⟩, hyz, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨hyY, hzN⟩ := Finset.mem_sigma.mp hyz
        obtain ⟨z', hz'⟩ := (Finset.mem_filter.mp hyY).2
        have hbase := (Finset.mem_filter.mp (h𝒟_props x y z' hz').1).2
        have hzx : z ≠ x := (Finset.mem_erase.mp hzN).1
        have hzv : F.Adj v z := (mem_neighborFinset F _ _).mp (Finset.mem_inter.mp (Finset.mem_erase.mp hzN).2).1
        have hzy : F.Adj y z := (mem_neighborFinset F _ _).mp (Finset.mem_inter.mp (Finset.mem_erase.mp hzN).2).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hvx.ne, hbase.2.1, hzv.ne, hbase.2.2.2.1, hzx.symm, hzy.ne,
          hvx, hbase.2.2.2.2.2.2.2.1, hzy, hzv.symm⟩, Or.inl rfl⟩
      have hp_ge : (Yx.card : ℝ) * (s / 4) ≤ (pairs.card : ℝ) := by
        rw [Finset.card_sigma, Nat.cast_sum]
        calc (Yx.card : ℝ) * (s / 4) = ∑ _y ∈ Yx, (s / 4) := by simp
          _ ≤ ∑ y ∈ Yx, ((((F.neighborFinset v) ∩ (F.neighborFinset y)).erase x).card : ℝ) := by
              apply Finset.sum_le_sum; intro y hy
              obtain ⟨z', hz'⟩ := (Finset.mem_filter.mp hy).2
              have ⟨_, _, _, hs2, h2⟩ := h𝒟_props x y z' hz'
              have hcard_er : (codeg v y : ℝ) / 2 ≤
                  ((((F.neighborFinset v) ∩ (F.neighborFinset y)).erase x).card : ℝ) := by
                have hnat : codeg v y ≤ 2 * (((F.neighborFinset v) ∩ (F.neighborFinset y)).erase x).card := by
                  dsimp [codeg] at h2 ⊢
                  by_cases hxN : x ∈ (F.neighborFinset v) ∩ (F.neighborFinset y)
                  · rw [Finset.card_erase_of_mem hxN]; omega
                  · rw [Finset.erase_eq_of_notMem hxN]; omega
                have : (codeg v y : ℝ) ≤ 2 * ((((F.neighborFinset v) ∩ (F.neighborFinset y)).erase x).card : ℝ) := by
                  exact_mod_cast hnat
                linarith
              linarith
      have hp_le : (pairs.card : ℝ) ≤ (((orderedC4 F).filter (c4HasEdge s(v, x))).card : ℝ) := by
        rw [← Finset.card_image_of_injOn hinj]
        exact_mod_cast Finset.card_le_card hmaps
      have htot := hp_ge.trans (hp_le.trans (hc4 s(v, x) (mem_edgeFinset.mpr hvx)))
      rw [← le_div_iff₀ (by positivity : 0 < s / 4)] at htot
      calc (Yx.card : ℝ) ≤ ((40 * Real.log m / (m * dF)) * q) / (s / 4) := htot
        _ = (160 * Real.log m / (m * dF * s)) * q := by
            field_simp [hm_pos.ne', hdF_pos.ne', hs_pos.ne']; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hYx_ne, Finset.card_empty, Nat.cast_zero]
      positivity
  exact ⟨v, s, 𝒟, hs_pos, h𝒟_card, h𝒟_sym, h𝒟_props, h𝒟_cond3⟩

/-- Helper for `many_c4_dense_GT`: dyadic bucketing of `𝒟` produces `sh` and `GT` on `T = N(v)`
with `sh ≤ K_F d_F` and `|𝒟| / (4 sh L) ≤ e(GT)`. -/
private lemma many_c4_dyadic_GT {V : Type} [Fintype V] (F : SimpleGraph V)
    {K_F : ℝ} (_hm8 : 8 ≤ Fintype.card V)
    (hΔF : ∀ u : V, (F.degree u : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))
    (v : V) (𝒟 : Finset (V × V × V)) (h𝒟_pos : (0 : ℝ) < (𝒟.card : ℝ))
    (h𝒟_sym : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟)
    (h𝒟_c4 : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (v, x, y, z) ∈ orderedC4 F) :
    let mN := Fintype.card V
    let m : ℝ := mN
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    let L : ℕ := Nat.log 2 mN + 2
    let T := F.neighborFinset v
    let hcnt (x z : V) : ℕ := (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟).card
    ∃ (sh : ℕ) (GT : SimpleGraph (T : Set V)),
      (∀ a b, GT.Adj a b ↔ a ≠ b ∧ sh ≤ hcnt a.1 b.1) ∧
      2 ≤ T.card ∧
      (0 : ℝ) < (sh : ℝ) ∧
      (sh : ℝ) ≤ K_F * dF ∧
      (𝒟.card : ℝ) / (4 * (sh : ℝ) * (L : ℝ)) ≤ (GT.edgeFinset.card : ℝ) := by
  dsimp only
  let mN := Fintype.card V
  let m : ℝ := mN
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let L : ℕ := Nat.log 2 mN + 2
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  let T := F.neighborFinset v
  have hT_card_pos : 2 ≤ T.card := by
    have h𝒟ne : 𝒟.Nonempty := Finset.card_pos.mp (by exact_mod_cast h𝒟_pos)
    obtain ⟨⟨x, y, z⟩, hxyz⟩ := h𝒟ne
    have h4 := (Finset.mem_filter.mp (h𝒟_c4 x y z hxyz)).2
    have hsub : ({x, z} : Finset V) ⊆ T := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw2
      · exact (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.1
      · rw [Finset.mem_singleton.mp hw2]; exact (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.2.2.2.symm
    exact (Finset.card_pair h4.2.2.2.2.1).symm ▸ Finset.card_le_card hsub
  let hcnt (x z : V) : ℕ := (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟).card
  have hhcnt_sym : ∀ x z, hcnt x z = hcnt z x := fun x z => by
    dsimp [hcnt]; congr 1; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h𝒟_sym x y z, h𝒟_sym z y x⟩
  have hhcnt_le : ∀ x z, (hcnt x z : ℝ) ≤ K_F * dF := fun x z => by
    have hsub : (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟) ⊆ F.neighborFinset x := by
      intro y hy
      exact (mem_neighborFinset F _ _).mpr
        (Finset.mem_filter.mp (h𝒟_c4 x y z (Finset.mem_filter.mp hy).2)).2.2.2.2.2.2.2.2.1
    have hc : (hcnt x z : ℝ) ≤ ((F.neighborFinset x).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree] at hc
    exact hc.trans (hΔF x)
  have hex_j : ∃ j ∈ Finset.range L,
      (𝒟.card : ℝ) / (L : ℝ) ≤ ((𝒟.filter fun p => Nat.log 2 (hcnt p.1 p.2.2) = j).card : ℝ) := by
    by_contra hall
    push Not at hall
    have hneL : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hsum := Finset.sum_lt_sum_of_nonempty hneL hall
    have hpart : ∑ j ∈ Finset.range L, ((𝒟.filter fun p => Nat.log 2 (hcnt p.1 p.2.2) = j).card : ℝ) =
        (𝒟.card : ℝ) := by
      rw [← Nat.cast_sum]; congr 1
      rw [← Finset.card_biUnion]
      · congr 1; ext p
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
        exact ⟨fun ⟨_, _, hp, _⟩ => hp, fun hp =>
          ⟨Nat.log 2 (hcnt p.1 p.2.2), by
            have hle : hcnt p.1 p.2.2 ≤ mN := Finset.card_le_univ _
            have := Nat.log_mono_right (b := 2) hle; dsimp [L]; omega, hp, rfl⟩⟩
      · intro j₁ _ j₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hRHS : ∑ _j ∈ Finset.range L, (𝒟.card : ℝ) / (L : ℝ) = (𝒟.card : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hL_pos.ne']
    linarith
  obtain ⟨j₀, _, hj₀⟩ := hex_j
  let sh : ℕ := 2 ^ j₀
  have hsh_pos : (0 : ℝ) < (sh : ℝ) := by dsimp [sh]; positivity
  let GT : SimpleGraph (T : Set V) :=
    { Adj := fun a b => a ≠ b ∧ sh ≤ hcnt a.1 b.1
      symm := ⟨fun a b ⟨hne, h⟩ => ⟨hne.symm, (hhcnt_sym a.1 b.1) ▸ h⟩⟩
      loopless := ⟨fun a h => h.1 rfl⟩ }
  have hGT_edges : (𝒟.card : ℝ) / (4 * (sh : ℝ) * (L : ℝ)) ≤ (GT.edgeFinset.card : ℝ) := by
    let 𝒟j := 𝒟.filter fun p => Nat.log 2 (hcnt p.1 p.2.2) = j₀
    have hsub : 𝒟j ⊆ (T ×ˢ T).biUnion fun xz =>
        if xz.1 ≠ xz.2 ∧ sh ≤ hcnt xz.1 xz.2 ∧ hcnt xz.1 xz.2 < 2 * sh then
          (Finset.univ.filter fun y : V => (xz.1, y, xz.2) ∈ 𝒟).image fun y => (xz.1, y, xz.2)
        else ∅ := by
      rintro ⟨x, y, z⟩ hp
      obtain ⟨hpD, hlog⟩ := Finset.mem_filter.mp hp
      have h4 := (Finset.mem_filter.mp (h𝒟_c4 x y z hpD)).2
      have hxT : x ∈ T := (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.1
      have hzT : z ∈ T := (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.2.2.2.symm
      have hne : x ≠ z := h4.2.2.2.2.1
      have hpos : 0 < hcnt x z := Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hpD⟩⟩
      have hge : sh ≤ hcnt x z := by dsimp [sh]; rw [← hlog]; exact Nat.pow_log_le_self 2 hpos.ne'
      have hlt : hcnt x z < 2 * sh := by
        dsimp [sh]; rw [← hlog, ← pow_succ']
        exact Nat.lt_pow_succ_log_self (by decide) _
      refine Finset.mem_biUnion.mpr ⟨(x, z), Finset.mem_product.mpr ⟨hxT, hzT⟩, ?_⟩
      rw [if_pos ⟨hne, hge, hlt⟩]
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hpD⟩, rfl⟩
    have hcard_le : 𝒟j.card ≤ (2 * GT.edgeFinset.card) * (2 * sh) := by
      have h1 : 𝒟j.card ≤ ∑ xz ∈ T ×ˢ T, if xz.1 ≠ xz.2 ∧ sh ≤ hcnt xz.1 xz.2 then 2 * sh else 0 := by
        refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun xz _ => ?_))
        split_ifs with h1 h2
        · exact Finset.card_image_le.trans h1.2.2.le
        · exfalso; exact h2 ⟨h1.1, h1.2.1⟩
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      have h2 : (∑ xz ∈ T ×ˢ T, if xz.1 ≠ xz.2 ∧ sh ≤ hcnt xz.1 xz.2 then 1 else 0) = 2 * GT.edgeFinset.card := by
        rw [← GT.sum_degrees_eq_twice_card_edges]
        rw [Finset.sum_product, ← Finset.sum_coe_sort T]
        apply Finset.sum_congr rfl; rintro ⟨x, hx⟩ _
        rw [← card_neighborFinset_eq_degree, ← Finset.sum_coe_sort T, ← Finset.sum_filter,
          Finset.sum_const, smul_eq_mul, mul_one]
        congr 1; ext ⟨z, hz⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset, GT, ne_eq, Subtype.mk.injEq]
      calc 𝒟j.card ≤ ∑ xz ∈ T ×ˢ T, (if xz.1 ≠ xz.2 ∧ sh ≤ hcnt xz.1 xz.2 then 1 else 0) * (2 * sh) :=
            h1.trans (le_of_eq (Finset.sum_congr rfl fun xz _ => by split_ifs <;> simp))
        _ = (∑ xz ∈ T ×ˢ T, if xz.1 ≠ xz.2 ∧ sh ≤ hcnt xz.1 xz.2 then 1 else 0) * (2 * sh) :=
            (Finset.sum_mul _ _ _).symm
        _ = (2 * GT.edgeFinset.card) * (2 * sh) := by rw [h2]
    have hcardR : (𝒟.card : ℝ) / (L : ℝ) ≤ (2 * (GT.edgeFinset.card : ℝ)) * (2 * (sh : ℝ)) :=
      hj₀.trans (by exact_mod_cast hcard_le)
    rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos)]
    have hLmul := (div_le_iff₀ hL_pos).mp hcardR
    linarith
  have hsh_le_KdF : (sh : ℝ) ≤ K_F * dF := by
    have hne : (𝒟.filter fun p => Nat.log 2 (hcnt p.1 p.2.2) = j₀).Nonempty := Finset.card_pos.mp (by
      have : (0 : ℝ) < ((𝒟.filter fun p => Nat.log 2 (hcnt p.1 p.2.2) = j₀).card : ℝ) :=
        lt_of_lt_of_le (div_pos h𝒟_pos hL_pos) hj₀
      exact_mod_cast this)
    obtain ⟨⟨x, y, z⟩, hp⟩ := hne
    obtain ⟨hpD, hlog⟩ := Finset.mem_filter.mp hp
    have hpos : 0 < hcnt x z := Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hpD⟩⟩
    have hle : sh ≤ hcnt x z := by dsimp [sh]; rw [← hlog]; exact Nat.pow_log_le_self 2 hpos.ne'
    exact (by exact_mod_cast hle : (sh : ℝ) ≤ _).trans (hhcnt_le x z)
  exact ⟨sh, GT, fun _ _ => Iff.rfl, hT_card_pos, hsh_pos, hsh_le_KdF,
    le_trans hGT_edges (le_of_eq (by congr 1; congr 1; ext e; simp only [mem_edgeFinset]; rfl))⟩

/-- Helper (Lemma 2.19a): extract the dyadic multiplicity `sh ≥ 16k` and auxiliary graph `GT` on
`T = N(v)` with average degree `dT ≥ max(m^(3ε/2) / (14400 K_F^2 log^3 m), |𝒟| / (2 sh L |T|))`. -/
private lemma many_c4_dense_GT {V : Type} [Fintype V] (F : SimpleGraph V)
    {ε K_F : ℝ} (_hε0 : 0 < ε) (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] (_hk : 2 ≤ k)
    (hm8 : 8 ≤ Fintype.card V)
    (hm1 : 16 * (k : ℝ) * 14400 * K_F ^ 2 * (Real.log (Fintype.card V : ℝ)) ^ 3 ≤
      (Fintype.card V : ℝ) ^ (3 * ε / 2))
    (hdF : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤
      2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hΔF : ∀ u : V, (F.degree u : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))
    (hq_gt : (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ (5 : ℕ) /
      (40 * (Fintype.card V : ℝ) ^ (3 * ε / 2) * Real.log (Fintype.card V : ℝ)) <
      ((orderedC4 F).card : ℝ))
    (v : V) (𝒟 : Finset (V × V × V))
    (h𝒟_card : ((orderedC4 F).card : ℝ) /
      (2 * (Fintype.card V : ℝ) * ((Nat.log 2 (Fintype.card V) + 2 : ℕ) : ℝ)) ≤ (𝒟.card : ℝ))
    (h𝒟_sym : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟)
    (h𝒟_c4 : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (v, x, y, z) ∈ orderedC4 F) :
    let mN := Fintype.card V
    let m : ℝ := mN
    let L : ℕ := Nat.log 2 mN + 2
    let T := F.neighborFinset v
    let hcnt (x z : V) : ℕ := (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟).card
    ∃ (sh : ℕ) (GT : SimpleGraph (T : Set V)),
      (∀ a b, GT.Adj a b ↔ a ≠ b ∧ sh ≤ hcnt a.1 b.1) ∧
      2 ≤ T.card ∧
      16 * k ≤ sh ∧
      0 < GT.edgeFinset.card ∧
      (𝒟.card : ℝ) / (2 * (sh : ℝ) * (L : ℝ) * (T.card : ℝ)) ≤
        2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ) ∧
      m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤
        2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ) := by
  dsimp only
  let mN := Fintype.card V
  let m : ℝ := mN
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let q : ℝ := ((orderedC4 F).card : ℝ)
  let L : ℕ := Nat.log 2 mN + 2
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log m := Real.log_pos (by change (1 : ℝ) < (mN : ℝ); exact_mod_cast (show 1 < mN by omega))
  have hL_le : (L : ℝ) ≤ 3 * Real.log m := natLog_add_two_le_three_log hm8
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have hq_pos : 0 < q := lt_of_lt_of_le (div_pos (pow_pos hdF_pos 5)
    (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hm_pos _)) hlog_pos)) hq_gt.le
  have hKF_pos : 0 < K_F := by linarith
  have hKF_ne : K_F ≠ 0 := hKF_pos.ne'
  have h𝒟_pos : (0 : ℝ) < (𝒟.card : ℝ) :=
    lt_of_lt_of_le (div_pos hq_pos (mul_pos (mul_pos (by norm_num) hm_pos) hL_pos)) h𝒟_card
  have hdF_cubed : m ^ (1 + 3 * ε) ≤ dF ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm_pos _).le hdF (by norm_num : (0 : ℝ) ≤ ((3 : ℕ) : ℝ))
    rw [← Real.rpow_mul hm_pos.le, Real.rpow_natCast] at h
    rwa [show ((1 : ℝ) / 3 + ε) * ((3 : ℕ) : ℝ) = 1 + 3 * ε by norm_num; ring] at h
  let T := F.neighborFinset v
  have hT_card_le : (T.card : ℝ) ≤ K_F * dF := by
    rw [card_neighborFinset_eq_degree]; exact hΔF v
  obtain ⟨sh, GT, hGT_adj, hT_card_pos, hsh_pos, hsh_le_KdF, hGT_edges⟩ :=
    many_c4_dyadic_GT F hm8 hΔF v 𝒟 h𝒟_pos h𝒟_sym h𝒟_c4
  have h𝒟_lb : dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2) ≤ (𝒟.card : ℝ) := by
    calc dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2)
        = (dF ^ (5 : ℕ) / (40 * m ^ (3 * ε / 2) * Real.log m)) / (2 * m * (3 * Real.log m)) := by
          rw [Real.rpow_add hm_pos, Real.rpow_one]
          have h1 : m ^ (3 * ε / 2) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
          field_simp [hm_pos.ne', hlog_pos.ne', h1]; norm_num
      _ ≤ q / (2 * m * (L : ℝ)) :=
          div_le_div₀ hq_pos.le hq_gt.le (mul_pos (mul_pos (by norm_num) hm_pos) hL_pos)
            (mul_le_mul_of_nonneg_left hL_le (mul_nonneg (by norm_num) hm_pos.le))
      _ ≤ (𝒟.card : ℝ) := h𝒟_card
  have hTpos : (0 : ℝ) < (T.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hT_card_pos)
  have hdT_lb_both : (𝒟.card : ℝ) / (2 * (sh : ℝ) * (L : ℝ) * (T.card : ℝ)) ≤
      2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos) hTpos) hTpos]
    have h1 := (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos)).mp hGT_edges
    have h2 : (𝒟.card : ℝ) * (T.card : ℝ) ≤
        ((GT.edgeFinset.card : ℝ) * (4 * (sh : ℝ) * (L : ℝ))) * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hTpos.le
    linarith
  have hKd_pos : 0 < K_F * dF := mul_pos hKF_pos hdF_pos
  have hdT_ge_m : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤
      2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ) := by
    have h1 : dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2) /
        (2 * (K_F * dF) * (3 * Real.log m) * (K_F * dF)) ≤
        (𝒟.card : ℝ) / (2 * (sh : ℝ) * (L : ℝ) * (T.card : ℝ)) := by
      have hden_pos : 0 < 2 * (sh : ℝ) * (L : ℝ) * (T.card : ℝ) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos) hTpos
      have hden_le : 2 * (sh : ℝ) * (L : ℝ) * (T.card : ℝ) ≤ 2 * (K_F * dF) * (3 * Real.log m) * (K_F * dF) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsh_le_KdF (by norm_num)) hL_le hL_pos.le
          (mul_nonneg (by norm_num) hKd_pos.le)) hT_card_le hTpos.le
          (mul_nonneg (mul_nonneg (by norm_num) hKd_pos.le) (mul_nonneg (by norm_num) hlog_pos.le))
      exact div_le_div₀ (Nat.cast_nonneg _) h𝒟_lb hden_pos hden_le
    have h2 : dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2) /
        (2 * (K_F * dF) * (3 * Real.log m) * (K_F * dF)) =
        dF ^ (3 : ℕ) / (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) := by
      have h1p : m ^ (1 + 3 * ε / 2) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
      field_simp [hdF_pos.ne', hKF_ne, hlog_pos.ne', h1p]; norm_num
    have hlog3_pos : 0 < (Real.log m) ^ 3 := pow_pos hlog_pos 3
    have h1p_pos : 0 < m ^ (1 + 3 * ε / 2) := Real.rpow_pos_of_pos hm_pos _
    have h3 : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤
        dF ^ (3 : ℕ) / (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) := by
      have hpow : m ^ (1 + 3 * ε) = m ^ (1 + 3 * ε / 2) * m ^ (3 * ε / 2) := by
        rw [← Real.rpow_add hm_pos]; congr 1; ring
      have h4 : m ^ (3 * ε / 2) / (1440 * K_F ^ 2 * (Real.log m) ^ 3) ≤
          dF ^ (3 : ℕ) / (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) := by
        rw [div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) hlog3_pos)
            (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) h1p_pos) hlog3_pos)]
        have : m ^ (3 * ε / 2) * (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) =
            m ^ (1 + 3 * ε) * (1440 * K_F ^ 2 * (Real.log m) ^ 3) := by rw [hpow]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hdF_cubed (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K_F)) hlog3_pos.le)
      exact (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hm_pos _).le
        (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) hlog3_pos)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg K_F)) hlog3_pos.le)).trans h4
    exact h3.trans (h2 ▸ h1.trans hdT_lb_both)
  have h16k_le_sh : 16 * k ≤ sh := by
    have hT_le_sq : 2 * (GT.edgeFinset.card : ℝ) ≤ (T.card : ℝ) * (T.card : ℝ) := by
      have := GT.sum_degrees_eq_twice_card_edges
      have hdeg : ∀ a : (T : Set V), GT.degree a ≤ T.card := fun a => by
        rw [← card_neighborFinset_eq_degree]
        exact (Finset.card_le_univ (GT.neighborFinset a)).trans_eq (Fintype.card_coe T)
      have hsum : ∑ a : (T : Set V), GT.degree a ≤ T.card * T.card := by
        calc ∑ a : (T : Set V), GT.degree a ≤ ∑ _a : (T : Set V), T.card := Finset.sum_le_sum fun a _ => hdeg a
          _ = T.card * T.card := by simp
      exact_mod_cast (this ▸ hsum)
    have hKF_pos : 0 < K_F := by linarith
    have hKd_pos : 0 < K_F * dF := mul_pos hKF_pos hdF_pos
    have h1 : (𝒟.card : ℝ) / (2 * (L : ℝ) * (K_F * dF) ^ 2) ≤ (sh : ℝ) := by
      have h2 := (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos)).mp hGT_edges
      have h3 : (T.card : ℝ) ^ 2 ≤ (K_F * dF) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hT_card_le 2
      have hden_pos : 0 < 2 * (L : ℝ) * (K_F * dF) ^ 2 := mul_pos (mul_pos (by norm_num) hL_pos) (pow_pos hKd_pos 2)
      rw [div_le_iff₀ hden_pos]
      have h2e : 2 * (GT.edgeFinset.card : ℝ) ≤ (K_F * dF) ^ 2 := by linarith
      calc (𝒟.card : ℝ)
          ≤ (GT.edgeFinset.card : ℝ) * (4 * (sh : ℝ) * (L : ℝ)) := h2
        _ = (2 * (GT.edgeFinset.card : ℝ)) * (2 * (sh : ℝ) * (L : ℝ)) := by ring
        _ ≤ (K_F * dF) ^ 2 * (2 * (sh : ℝ) * (L : ℝ)) :=
            mul_le_mul_of_nonneg_right h2e (mul_nonneg (mul_nonneg (by norm_num) hsh_pos.le) hL_pos.le)
        _ = (sh : ℝ) * (2 * (L : ℝ) * (K_F * dF) ^ 2) := by ring
    have h2 : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤ (sh : ℝ) := by
      have hpow : m ^ (1 + 3 * ε) = m ^ (1 + 3 * ε / 2) * m ^ (3 * ε / 2) := by
        rw [← Real.rpow_add hm_pos]; congr 1; ring
      have h1pos : 0 < m ^ (1 + 3 * ε / 2) := Real.rpow_pos_of_pos hm_pos _
      have h3 : dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2) /
          (2 * (3 * Real.log m) * (K_F * dF) ^ 2) ≤ (sh : ℝ) := by
        refine le_trans ?_ h1
        have hdenL : 0 < 2 * (L : ℝ) * (K_F * dF) ^ 2 := mul_pos (mul_pos (by norm_num) hL_pos) (pow_pos hKd_pos 2)
        have hdenR : 2 * (L : ℝ) * (K_F * dF) ^ 2 ≤ 2 * (3 * Real.log m) * (K_F * dF) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL_le (by norm_num)) (sq_nonneg _)
        exact div_le_div₀ (Nat.cast_nonneg _) h𝒟_lb hdenL hdenR
      have h4 : dF ^ (5 : ℕ) / (240 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 2) /
          (2 * (3 * Real.log m) * (K_F * dF) ^ 2) =
          dF ^ (3 : ℕ) / (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) := by
        field_simp [hdF_pos.ne', hKF_ne, hlog_pos.ne', h1pos.ne']; norm_num
      rw [h4] at h3
      have hlog3_pos : 0 < (Real.log m) ^ 3 := pow_pos hlog_pos 3
      have h5 : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤
          dF ^ (3 : ℕ) / (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) := by
        rw [div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) hlog3_pos)
            (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) h1pos) hlog3_pos)]
        have : m ^ (3 * ε / 2) * (1440 * K_F ^ 2 * m ^ (1 + 3 * ε / 2) * (Real.log m) ^ 3) =
            m ^ (1 + 3 * ε) * (1440 * K_F ^ 2 * (Real.log m) ^ 3) := by rw [hpow]; ring
        rw [this]
        have h6 : 1440 * K_F ^ 2 * (Real.log m) ^ 3 ≤ 14400 * K_F ^ 2 * (Real.log m) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg K_F))
            hlog3_pos.le
        exact mul_le_mul hdF_cubed h6 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K_F)) hlog3_pos.le)
          (pow_nonneg hdF_pos.le 3)
      exact h5.trans h3
    have h3 : (16 * (k : ℝ)) ≤ (sh : ℝ) := by
      have : (16 * (k : ℝ)) ≤ m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) := by
        rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) (pow_pos hlog_pos 3))]
        have : 16 * (k : ℝ) * (14400 * K_F ^ 2 * (Real.log m) ^ 3) =
            16 * (k : ℝ) * 14400 * K_F ^ 2 * (Real.log m) ^ 3 := by ring
        rw [this]; exact hm1
      exact this.trans h2
    exact_mod_cast h3
  have hGT_pos : 0 < GT.edgeFinset.card := by
    have hpos : (0 : ℝ) < (𝒟.card : ℝ) / (4 * (sh : ℝ) * (L : ℝ)) :=
      div_pos (lt_of_lt_of_le (div_pos (pow_pos hdF_pos 5)
        (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hm_pos _)) (pow_pos hlog_pos 2))) h𝒟_lb)
        (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos)
    have : (0 : ℝ) < (GT.edgeFinset.card : ℝ) := lt_of_lt_of_le hpos hGT_edges
    exact_mod_cast this
  exact ⟨sh, GT, hGT_adj, hT_card_pos, h16k_le_sh, hGT_pos, hdT_lb_both, hdT_ge_m⟩

/-- Helper for `many_c4_build_cycles`: upper bound on non-injective `4k`-walks in `GT'`. -/
private lemma many_c4_badT_bound {U : Type} [Fintype U] (GT' : SimpleGraph U)
    {ε K_F m dT : ℝ} {k D₁ D₂ LT : ℕ} [NeZero k] (hKF : 1 ≤ K_F) (hk : 2 ≤ k)
    (hm_pos : 0 < m) (hlog_pos : 0 < Real.log m)
    (hcardU_le : (Fintype.card U : ℝ) ≤ m)
    (hLT_pos : (0 : ℝ) < (LT : ℝ)) (hLT_le : (LT : ℝ) ≤ 3 * Real.log m)
    (hm2 : 4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4 *
        (Real.log m) ^ 7 ≤ m ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))))
    (hdT_ge_m : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤ dT)
    (hD₁_ge' : dT / 5 ≤ (D₁ : ℝ)) (hD₂_ge' : dT / 5 ≤ (D₂ : ℝ))
    (hGT'_Δ : ∀ u : U, (GT'.degree u : ℝ) ≤ max (D₁ : ℝ) (D₂ : ℝ))
    (htr_T_ge : ((D₁ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ (2 * k) * ((D₂ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ (2 * k) ≤
      Matrix.trace (adjMat GT' ^ (2 * k + 2 * k))) :
    let r := 2 * k
    ((Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card : ℝ) ≤
      Matrix.trace (adjMat GT' ^ (r + r)) / 2 := by
  dsimp only
  let r := 2 * k
  have hr2 : 2 ≤ r := by omega
  have : NeZero r := ⟨by omega⟩
  have : NeZero (2 * r) := ⟨by omega⟩
  have : NeZero (4 * k) := ⟨by omega⟩
  have hKF_pos : 0 < K_F := by linarith
  have hdT_pos : 0 < dT := lt_of_lt_of_le (by positivity) hdT_ge_m
  have hD₁_pos : 0 < (D₁ : ℝ) := lt_of_lt_of_le (by positivity) hD₁_ge'
  have hD₂_pos : 0 < (D₂ : ℝ) := lt_of_lt_of_le (by positivity) hD₂_ge'
  have htr_T_pos : 0 < Matrix.trace (adjMat GT' ^ (r + r)) :=
    lt_of_lt_of_le (mul_pos (pow_pos (by positivity) r) (pow_pos (by positivity) r)) htr_T_ge
  let ΔT := max (D₁ : ℝ) (D₂ : ℝ)
  have hbv := bad_vertex_cycles_le GT' ΔT hGT'_Δ (le_trans hD₁_pos.le (le_max_left _ _)) r hr2
  have h2r : 2 * r = 4 * k := by omega
  have hbad_eq : (Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card =
      (Finset.univ.filter fun x : Fin (2 * r) → U =>
      (∀ t : Fin (2 * r), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card := by
    let eL : Fin (4 * k) ≃ Fin (2 * r) := finCongr h2r.symm
    let eFun : (Fin (4 * k) → U) ≃ (Fin (2 * r) → U) := eL.arrowCongr (Equiv.refl _)
    refine Finset.card_equiv eFun fun x => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hadj_iff : (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ↔
        (∀ t : Fin (2 * r), GT'.Adj (eFun x t) (eFun x (t + 1))) := by
      have hstep : ∀ t : Fin (4 * k), eL (t + 1) = eL t + 1 := fun t => by
        ext
        simp only [eL, finCongr_apply, Fin.val_cast, Fin.val_add,
          fin_val_one_of_gt (by omega : 1 < 4 * k), fin_val_one_of_gt (by omega : 1 < 2 * r), h2r]
      constructor
      · intro h t
        have := h (eL.symm t)
        have h1 : eL.symm (t + 1) = eL.symm t + 1 := eL.injective (by simp [hstep])
        simpa [eFun, h1] using this
      · intro h t
        have := h (eL t)
        simpa [eFun, ← hstep t] using this
    have hinj_iff : Function.Injective x ↔ Function.Injective (eFun x) := by
      constructor
      · intro h a b hab; exact eL.symm.injective (h hab)
      · intro h a b hab; exact eL.injective (h (by simpa [eFun] using hab))
    exact and_congr hadj_iff (not_congr hinj_iff)
  have hbv' : ((Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card : ℝ) ^ (4 * k) ≤
      ((4 * (r : ℝ) ^ 3 * ΔT) ^ r * (Fintype.card U : ℝ)) *
        (Matrix.trace (adjMat GT' ^ (r + r))) ^ (4 * k - 1) := by
    rw [hbad_eq, ← h2r]; convert hbv
  have hmin_ge : dT / 5 ≤ min (D₁ : ℝ) (D₂ : ℝ) := le_min hD₁_ge' hD₂_ge'
  have hprod_D : ΔT * (dT / 5) ≤ (D₁ : ℝ) * (D₂ : ℝ) := by
    have : max (D₁ : ℝ) (D₂ : ℝ) * min (D₁ : ℝ) (D₂ : ℝ) = (D₁ : ℝ) * (D₂ : ℝ) :=
      max_mul_min (D₁ : ℝ) (D₂ : ℝ)
    rw [← this]
    exact mul_le_mul_of_nonneg_left hmin_ge (le_trans hD₁_pos.le (le_max_left _ _))
  have hpow : ((Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card : ℝ) ^ (4 * k) ≤
      (Matrix.trace (adjMat GT' ^ (r + r)) / 2) ^ (4 * k) := by
    have hgoal : (4 * (r : ℝ) ^ 3 * ΔT) ^ r * (Fintype.card U : ℝ) ≤
        ((1 : ℝ) / 2) ^ (4 * k) * Matrix.trace (adjMat GT' ^ (r + r)) := by
      have htr_lb : (ΔT * (dT / 5) / (64 * (LT : ℝ) ^ 4)) ^ r ≤ Matrix.trace (adjMat GT' ^ (r + r)) := by
        calc (ΔT * (dT / 5) / (64 * (LT : ℝ) ^ 4)) ^ r
            ≤ ((D₁ : ℝ) * (D₂ : ℝ) / (64 * (LT : ℝ) ^ 4)) ^ r :=
              pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hprod_D (by positivity)) r
          _ = ((D₁ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r * ((D₂ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r := by
              rw [← mul_pow]; congr 1; ring
          _ ≤ Matrix.trace (adjMat GT' ^ (r + r)) := htr_T_ge
      have hstep : 4 * (r : ℝ) ^ 3 * (64 * (LT : ℝ) ^ 4 * 5) * 4 * m ^ (1 / (r : ℝ)) ≤ dT := by
        have hLT4 : (LT : ℝ) ^ 4 ≤ (3 * Real.log m) ^ 4 :=
          pow_le_pow_left₀ hLT_pos.le hLT_le 4
        have hLHS_le : 4 * (r : ℝ) ^ 3 * (64 * (LT : ℝ) ^ 4 * 5) * 4 * m ^ (1 / (r : ℝ)) ≤
            (4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4) * (Real.log m) ^ 4 * m ^ (1 / (2 * (k : ℝ))) := by
          have hrEq : (r : ℝ) = 2 * (k : ℝ) := by dsimp [r]; push_cast; ring
          rw [hrEq]
          have h1 : 4 * (2 * (k : ℝ)) ^ 3 * (64 * (LT : ℝ) ^ 4 * 5) * 4 ≤
              4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4 * (Real.log m) ^ 4 := by
            have h64 : (64 : ℝ) * (LT : ℝ) ^ 4 * 5 * 4 ≤ (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4 * (Real.log m) ^ 4 := by
              calc (64 : ℝ) * (LT : ℝ) ^ 4 * 5 * 4
                  ≤ 64 * (3 * Real.log m) ^ 4 * 5 * 4 := by gcongr
                _ = 103680 * (Real.log m) ^ 4 := by ring
                _ ≤ (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4 * (Real.log m) ^ 4 :=
                    mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hlog_pos.le 4)
            have hfac : 0 ≤ 4 * (2 * (k : ℝ)) ^ 3 := by positivity
            have := mul_le_mul_of_nonneg_left h64 hfac
            linarith
          exact mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hm_pos _).le
        have hRHS_ge : (4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4) *
            (Real.log m) ^ 4 * m ^ (1 / (2 * (k : ℝ))) ≤
            m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) := by
          rw [le_div_iff₀ (by positivity)]
          have hmpow : m ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))) * m ^ (1 / (2 * (k : ℝ))) = m ^ (3 * ε / 2) := by
            rw [← Real.rpow_add hm_pos, sub_add_cancel]
          have hlog7 : (Real.log m) ^ 4 * (Real.log m) ^ 3 = (Real.log m) ^ 7 := by ring
          calc (4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 2 ^ 4) *
                  (Real.log m) ^ 4 * m ^ (1 / (2 * (k : ℝ))) * (14400 * K_F ^ 2 * (Real.log m) ^ 3)
              = ((4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4) *
                  (Real.log m) ^ 7) * m ^ (1 / (2 * (k : ℝ))) := by rw [← hlog7]; ring
            _ ≤ m ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))) * m ^ (1 / (2 * (k : ℝ))) :=
                mul_le_mul_of_nonneg_right hm2 (Real.rpow_pos_of_pos hm_pos _).le
            _ = m ^ (3 * ε / 2) := hmpow
        exact hLHS_le.trans (hRHS_ge.trans hdT_ge_m)
      have hstep_pow := pow_le_pow_left₀ (by positivity) hstep r
      have hm_pow_r : (m ^ (1 / (r : ℝ))) ^ r = m := by
        have hrpos : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le, one_div_mul_cancel hrpos, Real.rpow_one]
      have h4r : (4 : ℝ) ^ r = ((1 / 2 : ℝ) ^ (4 * k))⁻¹ := by
        rw [one_div, inv_pow, inv_inv, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
          show 2 * r = 4 * k by omega]
      have hcomb : (4 * (r : ℝ) ^ 3 * ΔT) ^ r * m ≤
          ((1 : ℝ) / 2) ^ (4 * k) * (ΔT * (dT / 5) / (64 * (LT : ℝ) ^ 4)) ^ r := by
        have h1 : (4 * (r : ℝ) ^ 3 * (64 * (LT : ℝ) ^ 4 * 5) * 4) ^ r * m ≤ dT ^ r := by
          rw [mul_pow, hm_pow_r] at hstep_pow; exact hstep_pow
        have h2 : ((1 : ℝ) / 2) ^ (4 * k) * (4 : ℝ) ^ r = 1 := by
          rw [h4r, mul_inv_cancel₀ (by positivity)]
        have h3 : (4 * (r : ℝ) ^ 3 * ΔT) ^ r * m * (64 * (LT : ℝ) ^ 4 * 5) ^ r * (4 : ℝ) ^ r ≤
            ΔT ^ r * dT ^ r := by
          calc (4 * (r : ℝ) ^ 3 * ΔT) ^ r * m * (64 * (LT : ℝ) ^ 4 * 5) ^ r * (4 : ℝ) ^ r
              = ΔT ^ r * ((4 * (r : ℝ) ^ 3 * (64 * (LT : ℝ) ^ 4 * 5) * 4) ^ r * m) := by
                simp only [mul_pow]; ring
            _ ≤ ΔT ^ r * dT ^ r := mul_le_mul_of_nonneg_left h1 (by positivity)
        have h4 : (ΔT * (dT / 5) / (64 * (LT : ℝ) ^ 4)) ^ r =
            ΔT ^ r * dT ^ r / (64 * (LT : ℝ) ^ 4 * 5) ^ r := by
          rw [show ΔT * (dT / 5) / (64 * (LT : ℝ) ^ 4) = (ΔT * dT) / (64 * (LT : ℝ) ^ 4 * 5) by ring,
            div_pow, mul_pow]
        rw [h4]
        have hposD : 0 < (64 * (LT : ℝ) ^ 4 * 5) ^ r := by positivity
        calc (4 * (r : ℝ) ^ 3 * ΔT) ^ r * m
            = ((4 * (r : ℝ) ^ 3 * ΔT) ^ r * m * (64 * (LT : ℝ) ^ 4 * 5) ^ r * (4 : ℝ) ^ r) *
                ((1 : ℝ) / 2) ^ (4 * k) / (64 * (LT : ℝ) ^ 4 * 5) ^ r := by
              rw [show ((4 * (r : ℝ) ^ 3 * ΔT) ^ r * m * (64 * (LT : ℝ) ^ 4 * 5) ^ r * (4 : ℝ) ^ r) *
                  ((1 : ℝ) / 2) ^ (4 * k) / (64 * (LT : ℝ) ^ 4 * 5) ^ r =
                  ((4 * (r : ℝ) ^ 3 * ΔT) ^ r * m) * (((1 : ℝ) / 2) ^ (4 * k) * (4 : ℝ) ^ r) *
                  ((64 * (LT : ℝ) ^ 4 * 5) ^ r / (64 * (LT : ℝ) ^ 4 * 5) ^ r) by ring,
                h2, mul_one, div_self hposD.ne', mul_one]
          _ ≤ (ΔT ^ r * dT ^ r) * ((1 : ℝ) / 2) ^ (4 * k) / (64 * (LT : ℝ) ^ 4 * 5) ^ r := by
              gcongr
          _ = ((1 : ℝ) / 2) ^ (4 * k) * (ΔT ^ r * dT ^ r / (64 * (LT : ℝ) ^ 4 * 5) ^ r) := by ring
      exact (mul_le_mul_of_nonneg_left hcardU_le (by positivity)).trans
        (hcomb.trans (mul_le_mul_of_nonneg_left htr_lb (by positivity)))
    rw [div_pow, show (2 : ℝ) ^ (4 * k) = ((1 / 2 : ℝ) ^ (4 * k))⁻¹ by rw [one_div, inv_pow, inv_inv],
      div_eq_mul_inv, inv_inv]
    calc ((Finset.univ.filter fun x : Fin (4 * k) → U =>
          (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card : ℝ) ^ (4 * k)
        ≤ ((4 * (r : ℝ) ^ 3 * ΔT) ^ r * (Fintype.card U : ℝ)) *
            (Matrix.trace (adjMat GT' ^ (r + r))) ^ (4 * k - 1) := hbv'
      _ ≤ (((1 : ℝ) / 2) ^ (4 * k) * Matrix.trace (adjMat GT' ^ (r + r))) *
            (Matrix.trace (adjMat GT' ^ (r + r))) ^ (4 * k - 1) :=
          mul_le_mul_of_nonneg_right hgoal (pow_nonneg htr_T_pos.le _)
      _ = (Matrix.trace (adjMat GT' ^ (r + r))) ^ (4 * k) * ((1 : ℝ) / 2) ^ (4 * k) := by
          rw [mul_assoc, ← pow_succ', show (4 * k - 1) + 1 = 4 * k by omega]; ring
  exact le_of_pow_le_pow_left₀ (by omega : 4 * k ≠ 0) (by positivity) hpow

/-- Helper for `many_c4_build_cycles`: lift injective `4k`-cycles in `T` with heavy `𝒟`-edges to
injective `8k`-cycles in `V`. -/
private lemma many_c4_lift_cycles {V : Type} [Fintype V]
    {k sh : ℕ} [NeZero k] (hk : 2 ≤ k) (h16k_le_sh : 16 * k ≤ sh)
    (T : Finset V) (𝒟 : Finset (V × V × V)) :
    let hcnt (x z : V) : ℕ := (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟).card
    let cycT := Finset.univ.filter fun x : Fin (4 * k) → V =>
      (∀ t : Fin (4 * k), x t ∈ T) ∧ Function.Injective x ∧
      (∀ t : Fin (4 * k), sh ≤ hcnt (x t) (x (t + 1)))
    let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
      Function.Injective w ∧
      ∀ t : Fin (4 * k),
        (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
          w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
    ((cycT.card : ℝ) * ((sh : ℝ) / 2) ^ (4 * k)) ≤ (C.card : ℝ) := by
  dsimp only
  have : NeZero (4 * k) := ⟨by omega⟩
  have : NeZero (8 * k) := ⟨by omega⟩
  let hcnt (x z : V) : ℕ := (Finset.univ.filter fun y : V => (x, y, z) ∈ 𝒟).card
  let cycT := Finset.univ.filter fun x : Fin (4 * k) → V =>
    (∀ t : Fin (4 * k), x t ∈ T) ∧ Function.Injective x ∧
    (∀ t : Fin (4 * k), sh ≤ hcnt (x t) (x (t + 1)))
  let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
    Function.Injective w ∧
    ∀ t : Fin (4 * k),
      (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
        w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
  let lifts (x : Fin (4 * k) → V) : Finset (Fin (4 * k) → V) :=
    Finset.univ.filter fun y =>
      Function.Injective y ∧ (∀ a b : Fin (4 * k), x a ≠ y b) ∧
      ∀ t : Fin (4 * k), (x t, y t, x (t + 1)) ∈ 𝒟
  have hlifts_ge : ∀ x ∈ cycT, (sh - 8 * k) ^ (4 * k) ≤ (lifts x).card := by
    intro x hx
    obtain ⟨_, hxi, hshx⟩ := (Finset.mem_filter.mp hx).2
    let pref (n : ℕ) (hn : n ≤ 4 * k) : Finset (Fin n → V) :=
      Finset.univ.filter fun y =>
        Function.Injective y ∧ (∀ (a : Fin (4 * k)) (b : Fin n), x a ≠ y b) ∧
        ∀ b : Fin n, (x ⟨b.1, by omega⟩, y b, x (⟨b.1, by omega⟩ + 1)) ∈ 𝒟
    have hpref_ge : ∀ (n : ℕ) (hn : n ≤ 4 * k), (sh - 8 * k) ^ n ≤ (pref n hn).card := by
      intro n
      induction n with
      | zero =>
        intro hn
        rw [pow_zero]
        refine Finset.card_pos.mpr ⟨Fin.elim0, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun a => a.elim0, fun _ b => b.elim0, fun b => b.elim0⟩⟩
      | succ n ih =>
        intro hn
        let extSet (y : Fin n → V) : Finset V :=
          (Finset.univ.filter fun u : V =>
            (x ⟨n, by omega⟩, u, x (⟨n, by omega⟩ + 1)) ∈ 𝒟) \
          ((Finset.univ.image x) ∪ (Finset.univ.image y))
        have hext_card : ∀ y : Fin n → V, sh - 8 * k ≤ (extSet y).card := by
          intro y
          have h1 : sh ≤ (Finset.univ.filter fun u : V =>
              (x ⟨n, by omega⟩, u, x (⟨n, by omega⟩ + 1)) ∈ 𝒟).card := hshx ⟨n, by omega⟩
          have h2 : ((Finset.univ.image x) ∪ (Finset.univ.image y)).card ≤ 4 * k + n := by
            calc ((Finset.univ.image x) ∪ (Finset.univ.image y)).card
                ≤ (Finset.univ.image x).card + (Finset.univ.image y).card := Finset.card_union_le _ _
              _ ≤ (Finset.univ : Finset (Fin (4 * k))).card + (Finset.univ : Finset (Fin n)).card :=
                  Nat.add_le_add Finset.card_image_le Finset.card_image_le
              _ = 4 * k + n := by simp
          have h3 := Finset.le_card_sdiff ((Finset.univ.image x) ∪ (Finset.univ.image y))
            (Finset.univ.filter fun u : V => (x ⟨n, by omega⟩, u, x (⟨n, by omega⟩ + 1)) ∈ 𝒟)
          dsimp [extSet]; omega
        let pairs := (pref n (by omega)).sigma extSet
        have hpinj : Set.InjOn (fun p : Σ _ : Fin n → V, V => Fin.snoc (α := fun _ => V) p.1 p.2)
            (pairs : Set (Σ _ : Fin n → V, V)) := by
          rintro ⟨y₁, u₁⟩ _ ⟨y₂, u₂⟩ _ hEq
          have hy : y₁ = y₂ := funext fun j => by
            have := congrFun hEq (Fin.castSucc j)
            simpa [Fin.snoc_castSucc] using this
          have hu : u₁ = u₂ := by
            have := congrFun hEq (Fin.last n)
            simpa [Fin.snoc_last] using this
          subst hy; subst hu; rfl
        have hpmaps : pairs.image (fun p : Σ _ : Fin n → V, V => Fin.snoc (α := fun _ => V) p.1 p.2) ⊆
            pref (n + 1) hn := by
          intro z hz
          obtain ⟨⟨y, u⟩, hyu, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨hyP, huE⟩ := Finset.mem_sigma.mp hyu
          obtain ⟨hyInj, hyDisj, hyD⟩ := (Finset.mem_filter.mp hyP).2
          obtain ⟨huD, huNot⟩ := Finset.mem_sdiff.mp huE
          have huNotX : ∀ a : Fin (4 * k), x a ≠ u := fun a ha =>
            huNot (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩))
          have huNotY : ∀ b : Fin n, y b ≠ u := fun b hb =>
            huNot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩))
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
          · intro a b
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · rfl
            · simp [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact (huNotY b' hab.symm).elim
            · simp [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact (huNotY a' hab).elim
            · simp [Fin.snoc_castSucc] at hab; exact congrArg Fin.castSucc (hyInj hab)
          · intro a b
            refine Fin.lastCases ?_ (fun b' => ?_) b
            · simpa [Fin.snoc_last] using huNotX a
            · simpa [Fin.snoc_castSucc] using hyDisj a b'
          · intro b
            refine Fin.lastCases ?_ (fun b' => ?_) b
            · simpa [Fin.snoc_last] using (Finset.mem_filter.mp huD).2
            · simpa [Fin.snoc_castSucc] using hyD b'
        have hcardP : (pref n (by omega)).card * (sh - 8 * k) ≤ pairs.card := by
          rw [Finset.card_sigma]
          calc (pref n (by omega)).card * (sh - 8 * k) = ∑ _y ∈ pref n (by omega), (sh - 8 * k) := by simp
            _ ≤ ∑ y ∈ pref n (by omega), (extSet y).card := Finset.sum_le_sum fun y _ => hext_card y
        calc (sh - 8 * k) ^ (n + 1) = (sh - 8 * k) ^ n * (sh - 8 * k) := pow_succ _ _
          _ ≤ (pref n (by omega)).card * (sh - 8 * k) := Nat.mul_le_mul_right _ (ih (by omega))
          _ ≤ pairs.card := hcardP
          _ = (pairs.image fun p : Σ _ : Fin n → V, V => Fin.snoc (α := fun _ => V) p.1 p.2).card :=
              (Finset.card_image_of_injOn hpinj).symm
          _ ≤ (pref (n + 1) hn).card := Finset.card_le_card hpmaps
    exact hpref_ge (4 * k) le_rfl
  let combine (p : Σ _ : Fin (4 * k) → V, Fin (4 * k) → V) (i : Fin (8 * k)) : V :=
    if i.1 % 2 = 0 then p.1 ⟨i.1 / 2, by omega⟩ else p.2 ⟨i.1 / 2, by omega⟩
  have hcomb_inj : Function.Injective combine := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hEq
    have hx : x₁ = x₂ := funext fun t => by
      have := congrFun hEq ⟨2 * t.1, by omega⟩
      have hmod : (2 * t.1) % 2 = 0 := by omega
      have hdiv : (2 * t.1) / 2 = t.1 := by omega
      simpa [combine, hmod, hdiv] using this
    have hy : y₁ = y₂ := funext fun t => by
      have := congrFun hEq ⟨2 * t.1 + 1, by omega⟩
      have hmod : (2 * t.1 + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * t.1 + 1) / 2 = t.1 := by omega
      simpa [combine, hmod, hdiv] using this
    subst hx; subst hy; rfl
  have hcomb_maps : (cycT.sigma lifts).image combine ⊆ C := by
    intro w hw
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hxC, hyL⟩ := Finset.mem_sigma.mp hxy
    obtain ⟨_, hxi, _⟩ := (Finset.mem_filter.mp hxC).2
    obtain ⟨hyi, hdisj, hyD⟩ := (Finset.mem_filter.mp hyL).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro i j hij
      dsimp [combine] at hij
      split_ifs at hij with h1 h2 h2
      · ext; have := congrArg Fin.val (hxi hij); dsimp at this; omega
      · exact (hdisj _ _ hij).elim
      · exact (hdisj _ _ hij.symm).elim
      · ext; have := congrArg Fin.val (hyi hij); dsimp at this; omega
    · intro t
      have h0 : combine ⟨x, y⟩ ⟨2 * t.1, by omega⟩ = x t := by
        dsimp [combine]; have hm : (2 * t.1) % 2 = 0 := by omega
        simp only [if_pos hm]; congr 1; ext; dsimp only; omega
      have h1 : combine ⟨x, y⟩ ⟨2 * t.1 + 1, by omega⟩ = y t := by
        dsimp [combine]; have hm : (2 * t.1 + 1) % 2 ≠ 0 := by omega
        simp only [if_neg hm]; congr 1; ext; dsimp only; omega
      have h2 : combine ⟨x, y⟩ ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩ = x (t + 1) := by
        dsimp [combine]
        have hmod2 : ((2 * (t.1 + 1)) % (8 * k)) % 2 = 0 := by
          by_cases hlt : 2 * (t.1 + 1) < 8 * k
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have heq : 2 * (t.1 + 1) = 8 * k := by omega
            rw [heq, Nat.mod_self]
        simp only [if_pos hmod2]
        congr 1; ext; dsimp only
        rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 4 * k)]
        by_cases hlt : 2 * (t.1 + 1) < 8 * k
        · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]; omega
        · have heq : 2 * (t.1 + 1) = 8 * k := by omega
          have heq2 : t.1 + 1 = 4 * k := by omega
          rw [heq, Nat.mod_self, heq2, Nat.mod_self]
      rw [h0, h1, h2]
      exact hyD t
  have hcard_nat : cycT.card * (sh - 8 * k) ^ (4 * k) ≤ C.card := by
    have h1 : cycT.card * (sh - 8 * k) ^ (4 * k) ≤ (cycT.sigma lifts).card := by
      rw [Finset.card_sigma]
      calc cycT.card * (sh - 8 * k) ^ (4 * k) = ∑ _x ∈ cycT, (sh - 8 * k) ^ (4 * k) := by simp
        _ ≤ ∑ x ∈ cycT, (lifts x).card := Finset.sum_le_sum hlifts_ge
    exact h1.trans (by rw [← Finset.card_image_of_injective _ hcomb_inj]; exact Finset.card_le_card hcomb_maps)
  have hsh_half : (sh : ℝ) / 2 ≤ ((sh - 8 * k : ℕ) : ℝ) := by
    have : sh ≤ 2 * (sh - 8 * k) := by omega
    have hR : (sh : ℝ) ≤ 2 * ((sh - 8 * k : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  calc (cycT.card : ℝ) * ((sh : ℝ) / 2) ^ (4 * k)
      ≤ (cycT.card : ℝ) * ((sh - 8 * k : ℕ) : ℝ) ^ (4 * k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsh_half _) (Nat.cast_nonneg _)
    _ ≤ (C.card : ℝ) := by exact_mod_cast hcard_nat

/-- Helper: on any finite graph `GT` on an abstract vertex type `U`, bipartite dyadic regularization
plus trace/bad-cycle bounds produce a subgraph `GT' ≤ GT` with at least `(dT / (40 L²))^(4k) / 2`
injective `4k`-cycles. Keeping `U` abstract avoids `Subtype.instDecidableEq` vs `Classical`
instance mismatches in `Matrix.trace`. -/
private lemma many_c4_goodT_card {U : Type} [Fintype U] (GT : SimpleGraph U)
    {ε K_F m : ℝ} (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] [NeZero (4 * k)] (hk : 2 ≤ k)
    (hm_pos : 0 < m) (hlog_pos : 0 < Real.log m)
    (hcardU_le : (Fintype.card U : ℝ) ≤ m)
    {L : ℕ} (hL_le : (L : ℝ) ≤ 3 * Real.log m)
    (hLT_le : ((Nat.log 2 (Fintype.card U) + 2 : ℕ) : ℝ) ≤ (L : ℝ))
    (hm2 : 4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4 *
        (Real.log m) ^ 7 ≤ m ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))))
    (hU2 : 2 ≤ Fintype.card U) (hGT_pos : 0 < GT.edgeFinset.card)
    (hdT_ge_m : m ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log m) ^ 3) ≤
      2 * (GT.edgeFinset.card : ℝ) / (Fintype.card U : ℝ)) :
    ∃ GT' : SimpleGraph U, GT' ≤ GT ∧
      ((2 * (GT.edgeFinset.card : ℝ) / (Fintype.card U : ℝ)) / (40 * (L : ℝ) ^ 2)) ^ (4 * k) / 2 ≤
        ((Finset.univ.filter fun x : Fin (4 * k) → U =>
          (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ Function.Injective x).card : ℝ) := by
  obtain ⟨GT', X₁, X₂, D₁, D₂, hGT'le, _, hX₁ne, _, hD₁_ge, hD₂_ge,
    _, hX₁_deg, hX₂_deg, hGT'_Δ⟩ := bipartite_dyadic_reg GT hU2 hGT_pos
  let LT := Nat.log 2 (Fintype.card U) + 2
  have hLT_pos : (0 : ℝ) < (LT : ℝ) := by exact_mod_cast (show 0 < LT by omega)
  let r := 2 * k
  let s₁ := ⌈(D₁ : ℝ) / (8 * (LT : ℝ) ^ 2)⌉₊
  let s₂ := ⌈(D₂ : ℝ) / (8 * (LT : ℝ) ^ 2)⌉₊
  have hs₁_ge : ∀ x ∈ X₁, s₁ ≤ (X₂.filter (GT'.Adj x)).card := fun x hx =>
    Nat.ceil_le.mpr (hX₁_deg x hx).1
  have hs₂_ge : ∀ y ∈ X₂, s₂ ≤ (X₁.filter (GT'.Adj y)).card := fun y hy =>
    Nat.ceil_le.mpr (hX₂_deg y hy).1
  have htr_T_ge : ((D₁ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r * ((D₂ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r ≤
      Matrix.trace (adjMat GT' ^ (r + r)) := by
    have h1 := bipartite_trace_even_ge GT' X₁ X₂ hX₁ne s₁ s₂ hs₁_ge hs₂_ge r
    have hle1 : (D₁ : ℝ) / (8 * (LT : ℝ) ^ 2) ≤ (s₁ : ℝ) := Nat.le_ceil _
    have hle2 : (D₂ : ℝ) / (8 * (LT : ℝ) ^ 2) ≤ (s₂ : ℝ) := Nat.le_ceil _
    have hnn1 : 0 ≤ (D₁ : ℝ) / (8 * (LT : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
    have hnn2 : 0 ≤ (D₂ : ℝ) / (8 * (LT : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
    exact (mul_le_mul (pow_le_pow_left₀ hnn1 hle1 r)
      (pow_le_pow_left₀ hnn2 hle2 r) (pow_nonneg hnn2 r) (pow_nonneg (Nat.cast_nonneg _) r)).trans h1
  let dT : ℝ := 2 * (GT.edgeFinset.card : ℝ) / (Fintype.card U : ℝ)
  have hKF_pos : 0 < K_F := by linarith
  have hdT_pos : 0 < dT := lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hm_pos _)
    (mul_pos (mul_pos (by norm_num) (pow_pos hKF_pos 2)) (pow_pos hlog_pos 3))) hdT_ge_m
  have hD₁_pos : 0 < (D₁ : ℝ) := lt_of_lt_of_le (div_pos hdT_pos (by norm_num)) hD₁_ge
  have hD₂_pos : 0 < (D₂ : ℝ) := lt_of_lt_of_le (div_pos hdT_pos (by norm_num)) hD₂_ge
  have hbadT_le : ((Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x).card : ℝ) ≤
      Matrix.trace (adjMat GT' ^ (r + r)) / 2 :=
    many_c4_badT_bound GT' hKF hk hm_pos hlog_pos hcardU_le hLT_pos (hLT_le.trans hL_le) hm2
      hdT_ge_m hD₁_ge hD₂_ge hGT'_Δ htr_T_ge
  let goodT' := Finset.univ.filter fun x : Fin (4 * k) → U =>
    (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ Function.Injective x
  have hgoodT'_ge : Matrix.trace (adjMat GT' ^ (r + r)) / 2 ≤ (goodT'.card : ℝ) := by
    let allT' := Finset.univ.filter fun x : Fin (4 * k) → U =>
      ∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))
    let badT' := Finset.univ.filter fun x : Fin (4 * k) → U =>
      (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ ¬ Function.Injective x
    have hallT' : (allT'.card : ℝ) = Matrix.trace (adjMat GT' ^ (r + r)) := by
      have h := hom_cycle_card_eq_trace GT' (4 * k) (by omega)
      have hrr : 4 * k = r + r := by omega
      exact h.trans (by rw [hrr])
    have hsub : allT' ⊆ goodT' ∪ badT' := fun x hx => by
      by_cases hi : Function.Injective x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2, hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2, hi⟩)
    have hnat : allT'.card ≤ goodT'.card + badT'.card :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hR : (allT'.card : ℝ) ≤ (goodT'.card : ℝ) + (badT'.card : ℝ) := by exact_mod_cast hnat
    linarith
  have htr_dT : (dT / (40 * (L : ℝ) ^ 2)) ^ (4 * k) ≤ Matrix.trace (adjMat GT' ^ (r + r)) := by
    have h8LT : 0 < 8 * (LT : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hLT_pos 2)
    have h8le : 8 * (LT : ℝ) ^ 2 ≤ 8 * (L : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLT_pos.le hLT_le 2) (by norm_num)
    have h1 : dT / (40 * (L : ℝ) ^ 2) ≤ (D₁ : ℝ) / (8 * (LT : ℝ) ^ 2) := by
      calc dT / (40 * (L : ℝ) ^ 2) = (dT / 5) / (8 * (L : ℝ) ^ 2) := by ring
        _ ≤ (D₁ : ℝ) / (8 * (LT : ℝ) ^ 2) := div_le_div₀ hD₁_pos.le hD₁_ge h8LT h8le
    have h2 : dT / (40 * (L : ℝ) ^ 2) ≤ (D₂ : ℝ) / (8 * (LT : ℝ) ^ 2) := by
      calc dT / (40 * (L : ℝ) ^ 2) = (dT / 5) / (8 * (L : ℝ) ^ 2) := by ring
        _ ≤ (D₂ : ℝ) / (8 * (LT : ℝ) ^ 2) := div_le_div₀ hD₂_pos.le hD₂_ge h8LT h8le
    have hnn : 0 ≤ dT / (40 * (L : ℝ) ^ 2) := div_nonneg hdT_pos.le (mul_nonneg (by norm_num) (sq_nonneg _))
    calc (dT / (40 * (L : ℝ) ^ 2)) ^ (4 * k)
        = (dT / (40 * (L : ℝ) ^ 2)) ^ r * (dT / (40 * (L : ℝ) ^ 2)) ^ r := by
          rw [← pow_add, show r + r = 4 * k by omega]
      _ ≤ ((D₁ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r * ((D₂ : ℝ) / (8 * (LT : ℝ) ^ 2)) ^ r :=
          mul_le_mul (pow_le_pow_left₀ hnn h1 r) (pow_le_pow_left₀ hnn h2 r)
            (pow_nonneg hnn r) (pow_nonneg (div_nonneg hD₁_pos.le h8LT.le) r)
      _ ≤ Matrix.trace (adjMat GT' ^ (r + r)) := htr_T_ge
  exact ⟨GT', hGT'le, (div_le_div_of_nonneg_right htr_dT (by norm_num)).trans hgoodT'_ge⟩

/-- Helper: lift injective `4k`-cycles in `GT' ≤ GT` on `T` to `cycT` in `V`. -/
private lemma many_c4_cycT_bound {V : Type} [Fintype V]
    (T : Finset V) (𝒟 : Finset (V × V × V)) (sh : ℕ)
    (GT : SimpleGraph (T : Set V))
    (hGT_adj : ∀ a b, GT.Adj a b ↔ a ≠ b ∧ sh ≤ (Finset.univ.filter fun y : V => (a.1, y, b.1) ∈ 𝒟).card)
    {ε K_F : ℝ} (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] [NeZero (4 * k)] (hk : 2 ≤ k)
    (hm_pos : (0 : ℝ) < (Fintype.card V : ℝ))
    (hlog_pos : 0 < Real.log (Fintype.card V : ℝ))
    (hL_le : ((Nat.log 2 (Fintype.card V) + 2 : ℕ) : ℝ) ≤ 3 * Real.log (Fintype.card V : ℝ))
    (hm2 : 4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4 *
        (Real.log (Fintype.card V : ℝ)) ^ 7 ≤
      (Fintype.card V : ℝ) ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))))
    (hT_card_pos : 2 ≤ T.card) (hGT_pos : 0 < GT.edgeFinset.card)
    (hdT_ge_m : (Fintype.card V : ℝ) ^ (3 * ε / 2) / (14400 * K_F ^ 2 * (Real.log (Fintype.card V : ℝ)) ^ 3) ≤
      2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ)) :
    let L : ℕ := Nat.log 2 (Fintype.card V) + 2
    let dT : ℝ := 2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ)
    (dT / (40 * (L : ℝ) ^ 2)) ^ (4 * k) / 2 ≤
      ((Finset.univ.filter fun x : Fin (4 * k) → V =>
        (∀ t : Fin (4 * k), x t ∈ T) ∧ Function.Injective x ∧
        (∀ t : Fin (4 * k), sh ≤ (Finset.univ.filter fun y : V => (x t, y, x (t + 1)) ∈ 𝒟).card)).card : ℝ) := by
  dsimp only
  have hT_card_eq : Fintype.card (T : Set V) = T.card := Fintype.card_coe T
  have hcardT_le : (Fintype.card (T : Set V) : ℝ) ≤ (Fintype.card V : ℝ) := by
    rw [hT_card_eq]; exact_mod_cast Finset.card_le_univ T
  have hLT_le : ((Nat.log 2 (Fintype.card (T : Set V)) + 2 : ℕ) : ℝ) ≤
      ((Nat.log 2 (Fintype.card V) + 2 : ℕ) : ℝ) := by
    have : Fintype.card (T : Set V) ≤ Fintype.card V := by rw [hT_card_eq]; exact Finset.card_le_univ T
    have := Nat.log_mono_right (b := 2) this
    exact_mod_cast (show Nat.log 2 (Fintype.card (T : Set V)) + 2 ≤ Nat.log 2 (Fintype.card V) + 2 by omega)
  obtain ⟨GT', hGT'le, hgood⟩ := many_c4_goodT_card GT hKF hk hm_pos hlog_pos hcardT_le hL_le hLT_le hm2
    (hT_card_eq.symm ▸ hT_card_pos) hGT_pos (by rwa [hT_card_eq])
  rw [hT_card_eq] at hgood
  let goodT' := Finset.univ.filter fun x : Fin (4 * k) → (T : Set V) =>
    (∀ t : Fin (4 * k), GT'.Adj (x t) (x (t + 1))) ∧ Function.Injective x
  let cycT := Finset.univ.filter fun x : Fin (4 * k) → V =>
    (∀ t : Fin (4 * k), x t ∈ T) ∧ Function.Injective x ∧
    (∀ t : Fin (4 * k), sh ≤ (Finset.univ.filter fun y : V => (x t, y, x (t + 1)) ∈ 𝒟).card)
  have hcard_emb : goodT'.card ≤ cycT.card := by
    let lift (x : Fin (4 * k) → (T : Set V)) : Fin (4 * k) → V := fun t => (x t).1
    have hinj : Function.Injective lift := fun x₁ x₂ h => funext fun t => Subtype.ext (congrFun h t)
    rw [← Finset.card_image_of_injective goodT' hinj]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hcyc, hxi⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t => (x t).2,
      fun a b hab => hxi (Subtype.ext hab), fun t => ((hGT_adj _ _).mp (hGT'le (hcyc t))).2⟩
  exact hgood.trans (by exact_mod_cast hcard_emb)

/-- Helper (Lemma 2.19b): given `v, 𝒟` from `many_c4_heavy_triples`, build the `8k`-cycle family `C`
with `|C| ≥ (1/2) * (q / (256 * 20 * K_F * L^4 * m * dF))^(4k)`. -/
private lemma many_c4_build_cycles {V : Type} [Fintype V] (F : SimpleGraph V)
    {ε K_F : ℝ} (hε0 : 0 < ε) (hKF : 1 ≤ K_F) {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hm8 : 8 ≤ Fintype.card V)
    (hm1 : 16 * (k : ℝ) * 14400 * K_F ^ 2 * (Real.log (Fintype.card V : ℝ)) ^ 3 ≤
      (Fintype.card V : ℝ) ^ (3 * ε / 2))
    (hm2 : 4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4 *
        (Real.log (Fintype.card V : ℝ)) ^ 7 ≤
      (Fintype.card V : ℝ) ^ (3 * ε / 2 - 1 / (2 * (k : ℝ))))
    (hdF : (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤
      2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hΔF : ∀ u : V, (F.degree u : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))
    (hq_gt : (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ (5 : ℕ) /
      (40 * (Fintype.card V : ℝ) ^ (3 * ε / 2) * Real.log (Fintype.card V : ℝ)) <
      ((orderedC4 F).card : ℝ))
    (v : V) (𝒟 : Finset (V × V × V))
    (h𝒟_card : ((orderedC4 F).card : ℝ) /
      (2 * (Fintype.card V : ℝ) * ((Nat.log 2 (Fintype.card V) + 2 : ℕ) : ℝ)) ≤ (𝒟.card : ℝ))
    (h𝒟_sym : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟)
    (h𝒟_c4 : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (v, x, y, z) ∈ orderedC4 F) :
    let mN := Fintype.card V
    let m : ℝ := mN
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    let q : ℝ := ((orderedC4 F).card : ℝ)
    let L : ℕ := Nat.log 2 mN + 2
    let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
      Function.Injective w ∧
      ∀ t : Fin (4 * k),
        (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
          w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
    (1 / 2 : ℝ) * (q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF)) ^ (4 * k) ≤ (C.card : ℝ) := by
  dsimp only
  let mN := Fintype.card V
  let m : ℝ := mN
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let q : ℝ := ((orderedC4 F).card : ℝ)
  let L : ℕ := Nat.log 2 mN + 2
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log m := Real.log_pos (by change (1 : ℝ) < (mN : ℝ); exact_mod_cast (show 1 < mN by omega))
  have hL_le : (L : ℝ) ≤ 3 * Real.log m := natLog_add_two_le_three_log hm8
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have hq_pos : 0 < q := lt_of_lt_of_le (div_pos (pow_pos hdF_pos 5)
    (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hm_pos _)) hlog_pos)) hq_gt.le
  have hKF_pos : 0 < K_F := by linarith
  have hKF_ne : K_F ≠ 0 := hKF_pos.ne'
  let T := F.neighborFinset v
  have hT_card_le : (T.card : ℝ) ≤ K_F * dF := by
    rw [card_neighborFinset_eq_degree]; exact hΔF v
  obtain ⟨sh, GT, hGT_adj, hT_card_pos, h16k_le_sh, hGT_pos, hdT_lb_both, hdT_ge_m⟩ :=
    many_c4_dense_GT F hε0 hKF hk hm8 hm1 hdF hΔF hq_gt v 𝒟 h𝒟_card h𝒟_sym h𝒟_c4
  have hsh_pos : (0 : ℝ) < (sh : ℝ) := by exact_mod_cast (show 0 < sh by omega)
  have : NeZero (4 * k) := ⟨by omega⟩
  let dT : ℝ := 2 * (GT.edgeFinset.card : ℝ) / (T.card : ℝ)
  let cycT := Finset.univ.filter fun x : Fin (4 * k) → V =>
    (∀ t : Fin (4 * k), x t ∈ T) ∧ Function.Injective x ∧
    (∀ t : Fin (4 * k), sh ≤ (Finset.univ.filter fun y : V => (x t, y, x (t + 1)) ∈ 𝒟).card)
  have hcycT_card : (dT / (40 * (L : ℝ) ^ 2)) ^ (4 * k) / 2 ≤ (cycT.card : ℝ) :=
    many_c4_cycT_bound T 𝒟 sh GT hGT_adj hKF hk hm_pos hlog_pos hL_le hm2 hT_card_pos hGT_pos hdT_ge_m
  let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
    Function.Injective w ∧
    ∀ t : Fin (4 * k),
      (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
        w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
  have hC_card : ((cycT.card : ℝ) * ((sh : ℝ) / 2) ^ (4 * k)) ≤ (C.card : ℝ) :=
    many_c4_lift_cycles hk h16k_le_sh T 𝒟
  have hbase : q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF) ≤ (dT / (40 * (L : ℝ) ^ 2)) * ((sh : ℝ) / 2) := by
    have hTpos : (0 : ℝ) < (T.card : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hT_card_pos)
    have h1 : (𝒟.card : ℝ) / (2 * (L : ℝ) * (T.card : ℝ)) ≤ dT * (sh : ℝ) := by
      have h := hdT_lb_both
      rw [div_le_iff₀ (mul_pos (mul_pos (mul_pos (by norm_num) hsh_pos) hL_pos) hTpos)] at h
      rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) hL_pos) hTpos)]
      linarith
    have h2 : (𝒟.card : ℝ) / (2 * (L : ℝ) * (K_F * dF)) ≤ dT * (sh : ℝ) := by
      refine le_trans ?_ h1
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos (mul_pos (by norm_num) hL_pos) hTpos)
        (mul_le_mul_of_nonneg_left hT_card_le (mul_nonneg (by norm_num) hL_pos.le))
    have h80 : (0 : ℝ) < 80 * (L : ℝ) ^ 2 := mul_pos (by norm_num) (pow_pos hL_pos 2)
    have h2LKd : 0 < 2 * (L : ℝ) * (K_F * dF) := mul_pos (mul_pos (by norm_num) hL_pos) (mul_pos hKF_pos hdF_pos)
    calc q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF)
        ≤ q / (320 * K_F * (L : ℝ) ^ 4 * m * dF) := by
          apply div_le_div_of_nonneg_left hq_pos.le
            (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hKF_pos) (pow_pos hL_pos 4)) hm_pos) hdF_pos)
          have hposF : 0 < K_F * (L : ℝ) ^ 4 * m * dF :=
            mul_pos (mul_pos (mul_pos hKF_pos (pow_pos hL_pos 4)) hm_pos) hdF_pos
          have := mul_le_mul_of_nonneg_right (show (320 : ℝ) ≤ 256 * 20 by norm_num) hposF.le
          linarith
      _ = (q / (2 * m * (L : ℝ))) / (2 * (L : ℝ) * (K_F * dF)) / (80 * (L : ℝ) ^ 2) := by
          field_simp [hm_pos.ne', hdF_pos.ne', hL_pos.ne', hKF_ne]; norm_num
      _ ≤ (𝒟.card : ℝ) / (2 * (L : ℝ) * (K_F * dF)) / (80 * (L : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h𝒟_card h2LKd.le) h80.le
      _ ≤ (dT * (sh : ℝ)) / (80 * (L : ℝ) ^ 2) := div_le_div_of_nonneg_right h2 h80.le
      _ = (dT / (40 * (L : ℝ) ^ 2)) * ((sh : ℝ) / 2) := by ring
  have hbase_nn : 0 ≤ q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF) :=
    div_nonneg hq_pos.le (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKF_pos.le)
      (pow_nonneg hL_pos.le 4)) hm_pos.le) hdF_pos.le)
  calc (1 / 2 : ℝ) * (q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF)) ^ (4 * k)
      ≤ (1 / 2 : ℝ) * ((dT / (40 * (L : ℝ) ^ 2)) * ((sh : ℝ) / 2)) ^ (4 * k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase _) (by norm_num)
    _ = ((dT / (40 * (L : ℝ) ^ 2)) ^ (4 * k) / 2) * ((sh : ℝ) / 2) ^ (4 * k) := by rw [mul_pow]; ring
    _ ≤ (cycT.card : ℝ) * ((sh : ℝ) / 2) ^ (4 * k) :=
        mul_le_mul_of_nonneg_right hcycT_card (pow_nonneg (div_nonneg hsh_pos.le (by norm_num)) _)
    _ ≤ (C.card : ℝ) := hC_card

/-- Helper (Condition 3 projection bound for Lemma 2.14): for any `p : Fin (8 * k)`, dropping
indices `p + 1, p + 2` from the `8k`-cycle family `C` leaves at most
`(K_F * dF) * Mstep^(4k - 2) * ((160 * log m / (m * dF * s)) * q)` partial cycles. -/
private lemma many_c4_dropTwo_bound {V : Type} [Fintype V] (F : SimpleGraph V)
    {K_F s : ℝ} {k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (hs_pos : 0 < s) (hm_pos : (0 : ℝ) < (Fintype.card V : ℝ))
    (hdF_pos : 0 < 2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))
    (hlog_pos : 0 < Real.log (Fintype.card V : ℝ))
    (hΔF : ∀ u : V, (F.degree u : ℝ) ≤ K_F * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))
    (hc4 : ∀ e ∈ F.edgeFinset, (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
      (40 * Real.log (Fintype.card V : ℝ) /
        ((Fintype.card V : ℝ) * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) *
        ((orderedC4 F).card : ℝ))
    (v : V) (𝒟 : Finset (V × V × V))
    (h𝒟_sym : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (z, y, x) ∈ 𝒟)
    (h𝒟_c4 : ∀ x y z : V, (x, y, z) ∈ 𝒟 → (v, x, y, z) ∈ orderedC4 F)
    (h𝒟_cond3 : ∀ x : V,
      (((Finset.univ.filter fun y : V => ∃ z : V, (x, y, z) ∈ 𝒟).card : ℝ)) ≤
        (160 * Real.log (Fintype.card V : ℝ) /
          ((Fintype.card V : ℝ) * (2 * (F.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * s)) *
          ((orderedC4 F).card : ℝ))
    (p : Fin (8 * k)) :
    let m : ℝ := Fintype.card V
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    let q : ℝ := ((orderedC4 F).card : ℝ)
    let Mstep : ℝ := (40 * Real.log m / (m * dF)) * q
    let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
      Function.Injective w ∧
      ∀ t : Fin (4 * k),
        (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
          w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
    ((C.image (dropTwo p)).card : ℝ) ≤
      ((K_F * dF) * Mstep ^ (4 * k - 2)) * ((160 * Real.log m / (m * dF * s)) * q) := by
  dsimp only
  let m : ℝ := Fintype.card V
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let q : ℝ := ((orderedC4 F).card : ℝ)
  let Mstep : ℝ := (40 * Real.log m / (m * dF)) * q
  let T := F.neighborFinset v
  have hT_card_le : (T.card : ℝ) ≤ K_F * dF := by
    rw [card_neighborFinset_eq_degree]; exact hΔF v
  let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
    Function.Injective w ∧
    ∀ t : Fin (4 * k),
      (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
        w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
  have : NeZero (8 * k) := ⟨by omega⟩
  have h1v : (1 : Fin (8 * k)).val = 1 := fin_val_one_of_gt (by omega)
  have h2v : (2 : Fin (8 * k)).val = 2 := by change 2 % (8 * k) = 2; exact Nat.mod_eq_of_lt (by omega)
  have h3v : (3 : Fin (8 * k)).val = 3 := by change 3 % (8 * k) = 3; exact Nat.mod_eq_of_lt (by omega)
  have h4v : (4 : Fin (8 * k)).val = 4 := by change 4 % (8 * k) = 4; exact Nat.mod_eq_of_lt (by omega)
  have hMstep_nn : 0 ≤ Mstep := by dsimp [Mstep]; positivity
  have hstep_cnt : ∀ x : V,
      (((Finset.univ.filter fun yz : V × V => (x, yz.1, yz.2) ∈ 𝒟).card : ℝ)) ≤ Mstep := by
    intro x
    let S := Finset.univ.filter fun yz : V × V => (x, yz.1, yz.2) ∈ 𝒟
    change (S.card : ℝ) ≤ Mstep
    by_cases hSne : S.Nonempty
    · obtain ⟨⟨y₀, z₀⟩, h0⟩ := hSne
      have hvx : F.Adj v x := (Finset.mem_filter.mp (h𝒟_c4 x y₀ z₀ (Finset.mem_filter.mp h0).2)).2.2.2.2.2.2.2.1
      have hinj : Set.InjOn (fun yz : V × V => (v, x, yz.1, yz.2)) (S : Set _) := by
        rintro ⟨y₁, z₁⟩ _ ⟨y₂, z₂⟩ _ hEq; simp only [Prod.mk.injEq] at hEq; exact Prod.ext hEq.2.2.1 hEq.2.2.2
      have hmaps : S.image (fun yz : V × V => (v, x, yz.1, yz.2)) ⊆ (orderedC4 F).filter (c4HasEdge s(v, x)) := by
        intro t ht
        obtain ⟨⟨y, z⟩, hyz, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_filter.mpr ⟨h𝒟_c4 x y z (Finset.mem_filter.mp hyz).2, Or.inl rfl⟩
      have hle : (S.card : ℝ) ≤ (((orderedC4 F).filter (c4HasEdge s(v, x))).card : ℝ) := by
        rw [← Finset.card_image_of_injOn hinj]; exact_mod_cast Finset.card_le_card hmaps
      exact hle.trans (hc4 s(v, x) (mem_edgeFinset.mpr hvx))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hSne, Finset.card_empty, Nat.cast_zero]; exact hMstep_nn
  let Chain (len : ℕ) : Finset (Fin (2 * len + 1) → V) :=
    Finset.univ.filter fun f =>
      f ⟨0, by omega⟩ ∈ T ∧
      ∀ a : Fin len, (f ⟨2 * a.1, by omega⟩, f ⟨2 * a.1 + 1, by omega⟩, f ⟨2 * a.1 + 2, by omega⟩) ∈ 𝒟
  have hChain_card : ∀ len : ℕ, ((Chain len).card : ℝ) ≤ (K_F * dF) * Mstep ^ len := by
    intro len
    induction len with
    | zero =>
      have h1 : (Chain 0).card ≤ T.card := by
        let toV (f : Fin 1 → V) : V := f 0
        have hinj : Function.Injective toV := fun f₁ f₂ h => funext fun i => by fin_cases i; exact h
        rw [← Finset.card_image_of_injective _ hinj]
        exact Finset.card_le_card fun u hu => by
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
          exact (Finset.mem_filter.mp hf).2.1
      rw [pow_zero, mul_one]
      exact (by exact_mod_cast h1 : _ ≤ (T.card : ℝ)).trans hT_card_le
    | succ len ih =>
      let extP (f : Fin (2 * len + 1) → V) : Finset (V × V) :=
        Finset.univ.filter fun yz => (f ⟨2 * len, by omega⟩, yz.1, yz.2) ∈ 𝒟
      let glue (p : Σ _ : Fin (2 * len + 1) → V, V × V) (i : Fin (2 * (len + 1) + 1)) : V :=
        if h1 : i.1 < 2 * len + 1 then p.1 ⟨i.1, h1⟩
        else if i.1 = 2 * len + 1 then p.2.1
        else p.2.2
      have hsub : Chain (len + 1) ⊆ ((Chain len).sigma extP).image glue := by
        intro g hg
        obtain ⟨hg0, hgD⟩ := (Finset.mem_filter.mp hg).2
        let f : Fin (2 * len + 1) → V := fun i => g ⟨i.1, by omega⟩
        let yz : V × V := (g ⟨2 * len + 1, by omega⟩, g ⟨2 * len + 2, by omega⟩)
        have hfC : f ∈ Chain len := Finset.mem_filter.mpr ⟨Finset.mem_univ f, hg0, fun a => hgD ⟨a.1, by omega⟩⟩
        have hyzE : yz ∈ extP f := Finset.mem_filter.mpr ⟨Finset.mem_univ yz, hgD ⟨len, by omega⟩⟩
        refine Finset.mem_image.mpr ⟨⟨f, yz⟩, Finset.mem_sigma.mpr ⟨hfC, hyzE⟩, ?_⟩
        funext i; dsimp [glue, f, yz]
        split_ifs with h1 h2
        · rfl
        · congr 1; ext; change 2 * len + 1 = i.1; omega
        · congr 1; ext; change 2 * len + 2 = i.1; omega
      have hnat : (Chain (len + 1)).card ≤ ∑ f ∈ Chain len, (extP f).card := by
        exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_sigma]))
      calc ((Chain (len + 1)).card : ℝ)
          ≤ ∑ f ∈ Chain len, ((extP f).card : ℝ) := by exact_mod_cast hnat
        _ ≤ ∑ _f ∈ Chain len, Mstep := Finset.sum_le_sum fun f _ => hstep_cnt _
        _ = ((Chain len).card : ℝ) * Mstep := by simp
        _ ≤ ((K_F * dF) * Mstep ^ len) * Mstep := mul_le_mul_of_nonneg_right ih hMstep_nn
        _ = (K_F * dF) * Mstep ^ (len + 1) := by rw [pow_succ]; ring
  let startIdx : Fin (8 * k) := if p.1 % 2 = 0 then p + 4 else p + 3
  let extraIdx : Fin (8 * k) := if p.1 % 2 = 0 then p + 3 else p
  let anchorStep : Fin (2 * (4 * k - 2) + 1) :=
    if p.1 % 2 = 0 then ⟨0, by omega⟩ else ⟨2 * (4 * k - 2), by omega⟩
  have hstart_even : startIdx.1 % 2 = 0 := by
    dsimp [startIdx]
    split_ifs with hp0
    · rw [Fin.val_add, h4v]
      by_cases hlt : p.1 + 4 < 8 * k
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · rw [Nat.mod_eq_sub_mod (a := p.1 + 4) (b := 8 * k) (by omega),
          Nat.mod_eq_of_lt (by omega : p.1 + 4 - 8 * k < 8 * k)]; omega
    · rw [Fin.val_add, h3v]
      by_cases hlt : p.1 + 3 < 8 * k
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · rw [Nat.mod_eq_sub_mod (a := p.1 + 3) (b := 8 * k) (by omega),
          Nat.mod_eq_of_lt (by omega : p.1 + 3 - 8 * k < 8 * k)]; omega
  let mkF (a : ℕ) : Fin (8 * k) := ⟨a % (8 * k), Nat.mod_lt _ (by omega)⟩
  have hmkF_val : ∀ a : ℕ, (mkF a).val = a % (8 * k) := fun _ => rfl
  have hmkF_0 : mkF 0 = 0 := by ext; rw [hmkF_val, Fin.val_zero, Nat.zero_mod]
  have hmkF_1 : mkF 1 = 1 := by ext; rw [hmkF_val, h1v, Nat.mod_eq_of_lt (by omega : 1 < 8 * k)]
  have hmkF_2 : mkF 2 = 2 := by ext; rw [hmkF_val, h2v, Nat.mod_eq_of_lt (by omega : 2 < 8 * k)]
  have hmkF_add : ∀ a b : ℕ, mkF (a + b) = mkF a + mkF b := fun a b => by
    ext; rw [hmkF_val, Fin.val_add, hmkF_val, hmkF_val]; exact Nat.add_mod a b (8 * k)
  have hmkF_3 : mkF 3 = 3 := by ext; rw [hmkF_val, h3v, Nat.mod_eq_of_lt (by omega : 3 < 8 * k)]
  have hmkF_4 : mkF 4 = 4 := by ext; rw [hmkF_val, h4v, Nat.mod_eq_of_lt (by omega : 4 < 8 * k)]
  have hnot_omitted_chain : ∀ j : Fin (2 * (4 * k - 2) + 1),
      startIdx + mkF j.1 ≠ p + 1 ∧ startIdx + mkF j.1 ≠ p + 2 := by
    have hnot_add : ∀ c : ℕ, c = 3 ∨ c = 4 → ∀ t : ℕ, t = 1 ∨ t = 2 →
        ∀ j : Fin (2 * (4 * k - 2) + 1), p + mkF c + mkF j.1 ≠ p + mkF t := by
      intro c hc t ht j h
      rw [add_assoc, ← hmkF_add] at h
      have h0 := congrArg (· - p) h
      simp only [add_sub_cancel_left] at h0
      have hv := congrArg Fin.val h0
      rw [hmkF_val, hmkF_val, Nat.mod_eq_of_lt (by omega : t < 8 * k)] at hv
      by_cases hlt : c + j.1 < 8 * k
      · rw [Nat.mod_eq_of_lt hlt] at hv; omega
      · rw [Nat.mod_eq_sub_mod (a := c + j.1) (b := 8 * k) (by omega),
          Nat.mod_eq_of_lt (by omega : c + j.1 - 8 * k < 8 * k)] at hv; omega
    intro j
    dsimp [startIdx]
    split_ifs with hp0
    · rw [← hmkF_4, ← hmkF_1, ← hmkF_2]
      exact ⟨hnot_add 4 (Or.inr rfl) 1 (Or.inl rfl) j, hnot_add 4 (Or.inr rfl) 2 (Or.inr rfl) j⟩
    · rw [← hmkF_3, ← hmkF_1, ← hmkF_2]
      exact ⟨hnot_add 3 (Or.inl rfl) 1 (Or.inl rfl) j, hnot_add 3 (Or.inl rfl) 2 (Or.inr rfl) j⟩
  have hnot_omitted_extra : extraIdx ≠ p + 1 ∧ extraIdx ≠ p + 2 := by
    constructor <;> (intro h; dsimp [extraIdx] at h; split_ifs at h with hp0 <;>
      (have h0 := congrArg (· - p) h; simp only [add_sub_cancel_left, sub_self] at h0;
       have hv := congrArg Fin.val h0;
       simp only [h1v, h2v, h3v, Fin.val_zero] at hv; omega))
  let toSig (q : {j : Fin (8 * k) // j ≠ p + 1 ∧ j ≠ p + 2} → V) :
      Σ _ : Fin (2 * (4 * k - 2) + 1) → V, V :=
    ⟨fun j => q ⟨startIdx + mkF j.1, hnot_omitted_chain j⟩, q ⟨extraIdx, hnot_omitted_extra⟩⟩
  have htoSig_inj : Function.Injective toSig := by
    intro q₁ q₂ hEq
    have hfEq : (fun j : Fin (2 * (4 * k - 2) + 1) => q₁ ⟨startIdx + mkF j.1, hnot_omitted_chain j⟩) =
        (fun j => q₂ ⟨startIdx + mkF j.1, hnot_omitted_chain j⟩) := congrArg Sigma.fst hEq
    have huEq : q₁ ⟨extraIdx, hnot_omitted_extra⟩ = q₂ ⟨extraIdx, hnot_omitted_extra⟩ :=
      eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
    funext ⟨i, hi1, hi2⟩
    by_cases hxi : i = extraIdx
    · subst hxi; exact huEq
    · let d := (i - startIdx).1
      have hd_lt : d < 2 * (4 * k - 2) + 1 := by
        by_contra hge; push Not at hge
        have hcases : d = 8 * k - 3 ∨ d = 8 * k - 2 ∨ d = 8 * k - 1 := by
          have := (i - startIdx).2; omega
        have hdiff_eq : i = startIdx + mkF d := by
          have : mkF d = i - startIdx := by
            ext; rw [hmkF_val, Nat.mod_eq_of_lt (i - startIdx).2]
          rw [this, add_sub_cancel]
        dsimp [startIdx, extraIdx] at hdiff_eq hxi
        split_ifs at hdiff_eq hxi with hp0
        · rcases hcases with h1 | h2 | h3
          · apply hi1; rw [hdiff_eq, h1]; ext
            simp only [Fin.val_add, hmkF_val, h4v, h1v, Nat.mod_eq_of_lt (by omega : 8 * k - 3 < 8 * k)]
            have : p.1 + 4 + (8 * k - 3) = (p.1 + 1) + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right]
          · apply hi2; rw [hdiff_eq, h2]; ext
            simp only [Fin.val_add, hmkF_val, h4v, h2v, Nat.mod_eq_of_lt (by omega : 8 * k - 2 < 8 * k)]
            have : p.1 + 4 + (8 * k - 2) = (p.1 + 2) + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right]
          · apply hxi; rw [hdiff_eq, h3]; ext
            simp only [Fin.val_add, hmkF_val, h4v, h3v, Nat.mod_eq_of_lt (by omega : 8 * k - 1 < 8 * k)]
            have : p.1 + 4 + (8 * k - 1) = (p.1 + 3) + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right]
        · rcases hcases with h1 | h2 | h3
          · apply hxi; rw [hdiff_eq, h1]; ext
            simp only [Fin.val_add, hmkF_val, h3v, Nat.mod_eq_of_lt (by omega : 8 * k - 3 < 8 * k)]
            have : p.1 + 3 + (8 * k - 3) = p.1 + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right, Nat.mod_eq_of_lt p.2]
          · apply hi1; rw [hdiff_eq, h2]; ext
            simp only [Fin.val_add, hmkF_val, h3v, h1v, Nat.mod_eq_of_lt (by omega : 8 * k - 2 < 8 * k)]
            have : p.1 + 3 + (8 * k - 2) = (p.1 + 1) + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right]
          · apply hi2; rw [hdiff_eq, h3]; ext
            simp only [Fin.val_add, hmkF_val, h3v, h2v, Nat.mod_eq_of_lt (by omega : 8 * k - 1 < 8 * k)]
            have : p.1 + 3 + (8 * k - 1) = (p.1 + 2) + 8 * k := by omega
            rw [Nat.mod_add_mod, this, Nat.add_mod_right]
      have hpos : startIdx + mkF d = i := by
        have : mkF d = i - startIdx := by
          ext; rw [hmkF_val, Nat.mod_eq_of_lt (i - startIdx).2]
        rw [this, add_sub_cancel]
      have hstep := congrFun hfEq ⟨d, hd_lt⟩
      convert hstep using 2 <;> exact Subtype.ext hpos.symm
  let tailY (f : Fin (2 * (4 * k - 2) + 1) → V) : Finset V :=
    Finset.univ.filter fun y => ∃ z : V, (f anchorStep, y, z) ∈ 𝒟
  have hmaps : (C.image (dropTwo p)).image toSig ⊆ (Chain (4 * k - 2)).sigma tailY := by
    intro sig hsig
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hsig
    obtain ⟨w, hwC, rfl⟩ := Finset.mem_image.mp hq
    have hwD := (Finset.mem_filter.mp hwC).2.2
    have hD_at : ∀ u : Fin (8 * k), u.1 % 2 = 0 → (w u, w (u + 1), w (u + 2)) ∈ 𝒟 := by
      intro u hu
      let t : Fin (4 * k) := ⟨u.1 / 2, by omega⟩
      have h0 : (⟨2 * t.1, by omega⟩ : Fin (8 * k)) = u := by ext; dsimp [t]; omega
      have h1 : (⟨2 * t.1 + 1, by omega⟩ : Fin (8 * k)) = u + 1 := by
        ext; rw [Fin.val_add, h1v, Nat.mod_eq_of_lt (by omega)]; dsimp [t]; omega
      have h2 : (⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩ : Fin (8 * k)) = u + 2 := by
        ext; rw [Fin.val_add, h2v]; dsimp [t]
        have : 2 * (u.1 / 2 + 1) = u.1 + 2 := by omega
        rw [this]
      have := hwD t
      rwa [h0, h1, h2] at this
    refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    · dsimp [toSig, dropTwo]
      rw [hmkF_0, add_zero]
      exact (mem_neighborFinset F _ _).mpr
        (Finset.mem_filter.mp (h𝒟_c4 _ _ _ (hD_at startIdx hstart_even))).2.2.2.2.2.2.2.1
    · intro a
      dsimp [toSig, dropTwo]
      let u : Fin (8 * k) := startIdx + mkF (2 * a.1)
      have hu_even : u.1 % 2 = 0 := by
        dsimp [u]; rw [Fin.val_add, hmkF_val, Nat.mod_eq_of_lt (by omega : 2 * a.1 < 8 * k)]
        by_cases hlt : startIdx.1 + 2 * a.1 < 8 * k
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · rw [Nat.mod_eq_sub_mod (a := startIdx.1 + 2 * a.1) (b := 8 * k) (by omega),
            Nat.mod_eq_of_lt (by omega : startIdx.1 + 2 * a.1 - 8 * k < 8 * k)]; omega
      have h1 : startIdx + mkF (2 * a.1 + 1) = u + 1 := by
        dsimp [u]; rw [hmkF_add, hmkF_1, add_assoc]
      have h2 : startIdx + mkF (2 * a.1 + 2) = u + 2 := by
        dsimp [u]; rw [hmkF_add, hmkF_2, add_assoc]
      rw [h1, h2]; exact hD_at u hu_even
    · dsimp [toSig, dropTwo, anchorStep, startIdx, extraIdx]
      split_ifs with hp0
      · have h2even : (p + 2).1 % 2 = 0 := by
          rw [Fin.val_add, h2v]
          by_cases hlt : p.1 + 2 < 8 * k
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · rw [Nat.mod_eq_sub_mod (a := p.1 + 2) (b := 8 * k) (by omega),
              Nat.mod_eq_of_lt (by omega : p.1 + 2 - 8 * k < 8 * k)]; omega
        have hD2 := hD_at (p + 2) h2even
        have h3 : (p + 2) + 1 = p + 3 := by
          ext; rw [Fin.val_add, Fin.val_add, Fin.val_add, h1v, h2v, h3v, Nat.mod_add_mod, add_assoc]
        have h4 : (p + 2) + 2 = p + 4 := by
          ext; rw [Fin.val_add, Fin.val_add, Fin.val_add, h2v, h4v, Nat.mod_add_mod, add_assoc]
        rw [h3, h4] at hD2
        rw [Fin.val_zero, hmkF_0, add_zero]
        exact ⟨w (p + 2), h𝒟_sym _ _ _ hD2⟩
      · have hanc : (p + 3) + mkF (2 * (4 * k - 2)) = p - 1 := by
          ext
          have h8k : (2 * (4 * k - 2) : ℕ) = 8 * k - 4 := by omega
          rw [h8k, Fin.val_add, Fin.val_add, hmkF_val, h3v, Nat.mod_eq_of_lt (by omega : 8 * k - 4 < 8 * k)]
          rw [Nat.mod_add_mod]
          have hsum : p.1 + 3 + (8 * k - 4) = p.1 + (8 * k - 1) := by omega
          rw [hsum]
          have hp1 : 1 ≤ p.1 := by omega
          have hsub : (p - 1).1 = p.1 - 1 := by
            rw [Fin.val_sub, h1v]
            have : 8 * k - 1 + p.1 = (p.1 - 1) + 8 * k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]
          have : p.1 + (8 * k - 1) = (p.1 - 1) + 8 * k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hpeven : (p - 1).1 % 2 = 0 := by
          have hp1 : 1 ≤ p.1 := by omega
          have hsub : (p - 1).1 = p.1 - 1 := by
            rw [Fin.val_sub, h1v]
            have : 8 * k - 1 + p.1 = (p.1 - 1) + 8 * k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]; omega
        dsimp only
        rw [hanc]
        have hDm1 := hD_at (p - 1) hpeven
        have h1 : (p - 1) + 1 = p := sub_add_cancel p 1
        have h2 : (p - 1) + 2 = p + 1 := by
          have : (2 : Fin (8 * k)) = 1 + 1 := by
            ext; rw [Fin.val_add, h1v, h2v, Nat.mod_eq_of_lt (by omega : 1 + 1 < 8 * k)]
          rw [this, ← add_assoc, sub_add_cancel]
        rw [h1, h2] at hDm1
        exact ⟨w (p + 1), hDm1⟩
  have hcard_le : (C.image (dropTwo p)).card ≤ ∑ f ∈ Chain (4 * k - 2), (tailY f).card := by
    rw [← Finset.card_image_of_injective _ htoSig_inj]
    exact (Finset.card_le_card hmaps).trans (by rw [Finset.card_sigma])
  calc ((C.image (dropTwo p)).card : ℝ)
      ≤ ∑ f ∈ Chain (4 * k - 2), ((tailY f).card : ℝ) := by exact_mod_cast hcard_le
    _ ≤ ∑ _f ∈ Chain (4 * k - 2), ((160 * Real.log m / (m * dF * s)) * q) :=
        Finset.sum_le_sum fun f _ => h𝒟_cond3 _
    _ = ((Chain (4 * k - 2)).card : ℝ) * ((160 * Real.log m / (m * dF * s)) * q) := by simp
    _ ≤ ((K_F * dF) * Mstep ^ (4 * k - 2)) * ((160 * Real.log m / (m * dF * s)) * q) :=
        mul_le_mul_of_nonneg_right (hChain_card (4 * k - 2)) (by positivity)

/-- Lemma 2.14 (Many 4-cycles): if `F` on `m` vertices (`m` large) has `d_F ≥ m^(1/3 + ε)`,
`Δ ≤ K_F d_F`, every edge in at most `(40 log m / (m d_F)) * q` ordered 4-cycles, and
`q > d_F^5 / (40 m^(3ε/2) log m)`, then `F` admits a nonempty `m^(-ε/2)`-good set of `8k`-cycles. -/
private theorem many_c4_betaGood {ε K_F : ℝ} (hε0 : 0 < ε) (_hε1 : ε ≤ 1 / 12) (hKF : 1 ≤ K_F)
    {k : ℕ} [NeZero k] (hk : 2 ≤ k) (hkε : 2 / ε ≤ (k : ℝ)) :
    ∃ M₀ : ℕ, ∀ (V : Type) [Fintype V] (F : SimpleGraph V),
      M₀ ≤ Fintype.card V →
      let m : ℝ := Fintype.card V
      let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
      let q : ℝ := ((orderedC4 F).card : ℝ)
      m ^ ((1 : ℝ) / 3 + ε) ≤ dF →
      (∀ v : V, (F.degree v : ℝ) ≤ K_F * dF) →
      (∀ e ∈ F.edgeFinset, (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
        (40 * Real.log m / (m * dF)) * q) →
      dF ^ (5 : ℕ) / (40 * m ^ (3 * ε / 2) * Real.log m) < q →
      ∃ C : Finset (Fin (8 * k) → V), C.Nonempty ∧ IsBetaGood F (m ^ (-ε / 2)) C := by
  have ht1 := eventually_polylog_le_rpow (16 * (k : ℝ) * 14400 * K_F ^ 2) (3 * ε / 2) (by positivity) 3
  have ht2 := eventually_polylog_le_rpow
    (4 * (2 * (k : ℝ)) ^ 3 * (200 * 3 ^ 2) ^ 2 * 5 * 14400 * K_F ^ 2 * 2 ^ 4) (3 * ε / 2 - 1 / (2 * (k : ℝ)))
    (by
      have h2k : 2 ≤ (k : ℝ) * ε := (div_le_iff₀ hε0).mp hkε
      have : 1 / (2 * (k : ℝ)) ≤ ε / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith) 7
  have ht3 := eventually_polylog_le_rpow
    (5120 * (k : ℝ) * K_F * (40 : ℝ) ^ (4 * k) * (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k))
    ε hε0 (20 * k + 1)
  have hall := ht1.and (ht2.and (ht3.and (eventually_ge_atTop (8 : ℕ))))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hall
  refine ⟨M₀, fun V _ F hVm => ?_⟩
  obtain ⟨hm1, hm2, hm3, hm8⟩ := hM₀ (Fintype.card V) hVm
  dsimp only
  intro hdF hΔF hc4 hq_gt
  let mN := Fintype.card V
  let m : ℝ := mN
  let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
  let q : ℝ := ((orderedC4 F).card : ℝ)
  let L : ℕ := Nat.log 2 mN + 2
  have hm_pos : 0 < m := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log m := Real.log_pos (by change (1 : ℝ) < (mN : ℝ); exact_mod_cast (show 1 < mN by omega))
  have hlog_ge1 : 1 ≤ Real.log m := by
    have : (3 : ℝ) ≤ m := by change (3 : ℝ) ≤ (mN : ℝ); exact_mod_cast (show 3 ≤ mN by omega)
    have h2 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    exact (Real.log_exp 1).symm ▸ Real.log_le_log (Real.exp_pos 1) (h2.trans this)
  have hL_le : (L : ℝ) ≤ 3 * Real.log m := natLog_add_two_le_three_log hm8
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF
  have hq_pos : 0 < q := lt_of_lt_of_le (by positivity) hq_gt.le
  have hdF_cubed : m ^ (1 + 3 * ε) ≤ dF ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hm_pos _).le hdF (by norm_num : (0 : ℝ) ≤ ((3 : ℕ) : ℝ))
    rw [← Real.rpow_mul hm_pos.le, Real.rpow_natCast] at h
    rwa [show ((1 : ℝ) / 3 + ε) * ((3 : ℕ) : ℝ) = 1 + 3 * ε by norm_num; ring] at h
  obtain ⟨v, s, 𝒟, hs_pos, h𝒟_card, h𝒟_sym, h𝒟_props, h𝒟_cond3⟩ :=
    many_c4_heavy_triples F hm8 hdF_pos hc4
  have hC_lb := many_c4_build_cycles F hε0 hKF hk hm8 hm1 hm2 hdF hΔF hq_gt v 𝒟 h𝒟_card h𝒟_sym
    (fun x y z h => (h𝒟_props x y z h).1)
  let C : Finset (Fin (8 * k) → V) := Finset.univ.filter fun w =>
    Function.Injective w ∧
    ∀ t : Fin (4 * k),
      (w ⟨2 * t.1, by omega⟩, w ⟨2 * t.1 + 1, by omega⟩,
        w ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩) ∈ 𝒟
  have hC_ne : C.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < (C.card : ℝ) := lt_of_lt_of_le (by positivity) hC_lb
    exact_mod_cast this)
  have : NeZero (8 * k) := ⟨by omega⟩
  refine ⟨C, hC_ne, s, hs_pos, ?_, ?_, ?_⟩
  · -- Condition 1: every `w ∈ C` is an injective `8k`-cycle in `F`:
    intro w hw
    obtain ⟨hwi, hwD⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨hwi, fun i => ?_⟩
    let t : Fin (4 * k) := ⟨i.1 / 2, by omega⟩
    have h4 := (Finset.mem_filter.mp (h𝒟_props _ _ _ (hwD t)).1).2
    by_cases hpar : i.1 % 2 = 0
    · have hi0 : (⟨2 * t.1, by omega⟩ : Fin (8 * k)) = i := by ext; dsimp [t]; omega
      have hi1 : (⟨2 * t.1 + 1, by omega⟩ : Fin (8 * k)) = i + 1 := by
        ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k), Nat.mod_eq_of_lt (by omega)]; dsimp [t]; omega
      have hE := h4.2.2.2.2.2.2.2.1
      rwa [hi0, hi1] at hE
    · have hi1 : (⟨2 * t.1 + 1, by omega⟩ : Fin (8 * k)) = i := by ext; dsimp [t]; omega
      have hi2 : (⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩ : Fin (8 * k)) = i + 1 := by
        ext; rw [Fin.val_add, fin_val_one_of_gt (by omega : 1 < 8 * k)]; dsimp [t]
        have : 2 * (i.1 / 2 + 1) = i.1 + 1 := by omega
        rw [this]
      have hE := h4.2.2.2.2.2.2.2.2.1
      rwa [hi1, hi2] at hE
  · -- Condition 2: fixing all `j ≠ i` leaves `≤ s` choices:
    intro y hy i
    obtain ⟨_, hyD⟩ := (Finset.mem_filter.mp hy).2
    have hinj : Set.InjOn (fun x : Fin (8 * k) → V => x i)
        ((C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j) : Set _) := by
      intro x₁ hx₁ x₂ hx₂ hEq; funext j
      by_cases hj : j = i
      · subst hj; exact hEq
      · exact ((Finset.mem_filter.mp hx₁).2 j hj).trans ((Finset.mem_filter.mp hx₂).2 j hj).symm
    let t : Fin (4 * k) := ⟨i.1 / 2, by omega⟩
    by_cases hpar : i.1 % 2 = 0
    · have hi0 : (⟨2 * t.1, by omega⟩ : Fin (8 * k)) = i := by ext; dsimp [t]; omega
      have hne1 : (⟨2 * t.1 + 1, by omega⟩ : Fin (8 * k)) ≠ i := by
        intro h; have := congrArg Fin.val h; dsimp [t] at this; omega
      have hsub : (C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).image (fun x => x i) ⊆
          (F.neighborFinset v) ∩ (F.neighborFinset (y ⟨2 * t.1 + 1, by omega⟩)) := by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hxC, hxy⟩ := Finset.mem_filter.mp hx
        have h4 := (Finset.mem_filter.mp (h𝒟_props _ _ _ ((Finset.mem_filter.mp hxC).2.2 t)).1).2
        rw [hi0, hxy _ hne1] at h4
        exact Finset.mem_inter.mpr ⟨(mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.1,
          (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.2.1.symm⟩
      have hcard : ((C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).card : ℝ) ≤
          (((F.neighborFinset v) ∩ (F.neighborFinset (y ⟨2 * t.1 + 1, by omega⟩))).card : ℝ) := by
        rw [← Finset.card_image_of_injOn hinj]; exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (h𝒟_props _ _ _ (hyD t)).2.1
    · have hi1 : (⟨2 * t.1 + 1, by omega⟩ : Fin (8 * k)) = i := by ext; dsimp [t]; omega
      have hne0 : (⟨2 * t.1, by omega⟩ : Fin (8 * k)) ≠ i := by
        intro h; have := congrArg Fin.val h; dsimp [t] at this; omega
      have hne2 : (⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩ : Fin (8 * k)) ≠ i := by
        intro h; have := congrArg Fin.val h; dsimp [t] at this
        by_cases hlt : 2 * (i.1 / 2 + 1) < 8 * k
        · rw [Nat.mod_eq_of_lt hlt] at this; omega
        · have heq : 2 * (i.1 / 2 + 1) = 8 * k := by omega
          rw [heq, Nat.mod_self] at this; omega
      have hsub : (C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).image (fun x => x i) ⊆
          (F.neighborFinset (y ⟨2 * t.1, by omega⟩)) ∩
          (F.neighborFinset (y ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩)) := by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hxC, hxy⟩ := Finset.mem_filter.mp hx
        have h4 := (Finset.mem_filter.mp (h𝒟_props _ _ _ ((Finset.mem_filter.mp hxC).2.2 t)).1).2
        rw [hi1, hxy _ hne0, hxy _ hne2] at h4
        exact Finset.mem_inter.mpr ⟨(mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.2.1,
          (mem_neighborFinset F _ _).mpr h4.2.2.2.2.2.2.2.2.1.symm⟩
      have hcard : ((C.filter fun x => ∀ j : Fin (8 * k), j ≠ i → x j = y j).card : ℝ) ≤
          (((F.neighborFinset (y ⟨2 * t.1, by omega⟩)) ∩
            (F.neighborFinset (y ⟨(2 * (t.1 + 1)) % (8 * k), Nat.mod_lt _ (by omega)⟩))).card : ℝ) := by
        rw [← Finset.card_image_of_injOn hinj]; exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (h𝒟_props _ _ _ (hyD t)).2.2.1
  · -- Condition 3: compare `many_c4_dropTwo_bound` against `m^(-ε/2) * |C| / (16 * k * s)`:
    intro p
    let Mstep : ℝ := (40 * Real.log m / (m * dF)) * q
    have hproj_le := many_c4_dropTwo_bound F hk hs_pos hm_pos hdF_pos hlog_pos hΔF hc4 v 𝒟
      h𝒟_sym (fun x y z h => (h𝒟_props x y z h).1) h𝒟_cond3 p
    refine hproj_le.trans ?_
    rw [le_div_iff₀ (by positivity : 0 < 16 * (k : ℝ) * s)]
    let Q := q / (m * dF)
    have hQ_gt : dF * m ^ (3 * ε / 2) / (40 * Real.log m) < Q := by
      dsimp [Q]
      have hpow : m ^ (1 + 3 * ε) = m * m ^ (3 * ε / 2) * m ^ (3 * ε / 2) := by
        rw [show (1 : ℝ) + 3 * ε = 1 + (3 * ε / 2) + (3 * ε / 2) by ring,
          Real.rpow_add hm_pos, Real.rpow_add hm_pos, Real.rpow_one]
      have h1 : dF * m ^ (3 * ε / 2) / (40 * Real.log m) ≤
          (dF ^ (5 : ℕ) / (40 * m ^ (3 * ε / 2) * Real.log m)) / (m * dF) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hLHS : dF * m ^ (3 * ε / 2) * (40 * m ^ (3 * ε / 2) * Real.log m * (m * dF)) =
            40 * Real.log m * dF ^ 2 * m ^ (1 + 3 * ε) := by rw [hpow]; ring
        have hRHS : dF ^ (5 : ℕ) * (40 * Real.log m) = 40 * Real.log m * dF ^ 2 * dF ^ (3 : ℕ) := by ring
        rw [hLHS, hRHS]
        exact mul_le_mul_of_nonneg_left hdF_cubed (by positivity)
      exact h1.trans_lt (div_lt_div_of_pos_right hq_gt (by positivity))
    have hLHS_rew : ((K_F * dF) * Mstep ^ (4 * k - 2)) * ((160 * Real.log m / (m * dF * s)) * q) *
        (16 * (k : ℝ) * s) =
        (64 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1)) * Q ^ (4 * k - 1) := by
      have hM : Mstep = (40 * Real.log m) * Q := by dsimp [Mstep, Q]; ring
      have htail : (160 * Real.log m / (m * dF * s)) * q = 4 / s * ((40 * Real.log m) * Q) := by
        dsimp [Q]; field_simp [hm_pos.ne', hdF_pos.ne', hs_pos.ne']; ring
      rw [hM, htail]
      have hpow1 : ((40 * Real.log m) * Q) ^ (4 * k - 2) * ((40 * Real.log m) * Q) =
          ((40 * Real.log m) * Q) ^ (4 * k - 1) := by
        rw [← pow_succ, show (4 * k - 2) + 1 = 4 * k - 1 by omega]
      rw [mul_pow] at hpow1 ⊢
      have : ((K_F * dF) * ((40 * Real.log m) ^ (4 * k - 2) * Q ^ (4 * k - 2))) *
          (4 / s * ((40 * Real.log m) * Q)) * (16 * (k : ℝ) * s) =
          64 * (k : ℝ) * K_F * dF * ((40 * Real.log m) ^ (4 * k - 2) * Q ^ (4 * k - 2) *
            ((40 * Real.log m) * Q)) * (s / s) := by ring
      rw [this, hpow1, div_self hs_pos.ne', mul_one, mul_pow]; ring
    rw [hLHS_rew]
    have hC_Q : (1 / 2 : ℝ) * (Q / (256 * 20 * K_F * (L : ℝ) ^ 4)) ^ (4 * k) ≤ (C.card : ℝ) := by
      have heq : q / (256 * 20 * K_F * (L : ℝ) ^ 4 * m * dF) = Q / (256 * 20 * K_F * (L : ℝ) ^ 4) := by
        dsimp [Q]; ring
      rwa [← heq]
    have hcoeff : 128 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1) *
        (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) ≤ m ^ (-ε / 2) * Q := by
      have hL4 : (L : ℝ) ^ 4 ≤ (3 * Real.log m) ^ 4 := pow_le_pow_left₀ hL_pos.le hL_le 4
      have h1 : 128 * (k : ℝ) * K_F * (40 * Real.log m) ^ (4 * k - 1) *
          (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) * (40 * Real.log m) ≤
          5120 * (k : ℝ) * K_F * (40 : ℝ) ^ (4 * k) * (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) *
            (Real.log m) ^ (20 * k + 1) := by
        have h40 : (40 * Real.log m) ^ (4 * k - 1) * (40 * Real.log m) = (40 : ℝ) ^ (4 * k) * (Real.log m) ^ (4 * k) := by
          rw [← pow_succ, show (4 * k - 1) + 1 = 4 * k by omega, mul_pow]
        have hL4k : (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) ≤
            (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) * (Real.log m) ^ (16 * k) := by
          calc (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k)
              ≤ (256 * 20 * K_F * (3 * Real.log m) ^ 4) ^ (4 * k) :=
                pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hL4 (by positivity)) _
            _ = ((256 * 20 * K_F * (3 : ℝ) ^ 4) * (Real.log m) ^ 4) ^ (4 * k) := by congr 1; ring
            _ = (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) * (Real.log m) ^ (16 * k) := by
                rw [mul_pow, ← pow_mul, show 4 * (4 * k) = 16 * k by omega]
        have hlog20 : (Real.log m) ^ (4 * k) * (Real.log m) ^ (16 * k) ≤ (Real.log m) ^ (20 * k + 1) := by
          rw [← pow_add, show 4 * k + 16 * k = 20 * k by omega]
          exact pow_le_pow_right₀ hlog_ge1 (by omega)
        calc 128 * (k : ℝ) * K_F * (40 * Real.log m) ^ (4 * k - 1) *
                (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) * (40 * Real.log m)
            = 128 * (k : ℝ) * K_F * ((40 * Real.log m) ^ (4 * k - 1) * (40 * Real.log m)) *
                (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) := by ring
          _ ≤ 128 * (k : ℝ) * K_F * ((40 : ℝ) ^ (4 * k) * (Real.log m) ^ (4 * k)) *
                ((256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) * (Real.log m) ^ (16 * k)) := by
              rw [h40]; gcongr
          _ = 128 * (k : ℝ) * K_F * (40 : ℝ) ^ (4 * k) * (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) *
                ((Real.log m) ^ (4 * k) * (Real.log m) ^ (16 * k)) := by ring
          _ ≤ 5120 * (k : ℝ) * K_F * (40 : ℝ) ^ (4 * k) * (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) *
                (Real.log m) ^ (20 * k + 1) := by
              have h128 : (128 : ℝ) ≤ 5120 := by norm_num
              gcongr
      have h2 : 128 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1) *
          (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) ≤
          m ^ (-ε / 2) * (dF * m ^ (3 * ε / 2) / (40 * Real.log m)) := by
        have hmpow : m ^ (-ε / 2) * m ^ (3 * ε / 2) = m ^ ε := by
          rw [← Real.rpow_add hm_pos]; congr 1; ring
        have : m ^ (-ε / 2) * (dF * m ^ (3 * ε / 2) / (40 * Real.log m)) =
            dF * m ^ ε / (40 * Real.log m) := by
          calc m ^ (-ε / 2) * (dF * m ^ (3 * ε / 2) / (40 * Real.log m))
              = dF * (m ^ (-ε / 2) * m ^ (3 * ε / 2)) / (40 * Real.log m) := by ring
            _ = dF * m ^ ε / (40 * Real.log m) := by rw [hmpow]
        rw [this, le_div_iff₀ (by positivity)]
        calc 128 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1) *
                (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) * (40 * Real.log m)
            = dF * (128 * (k : ℝ) * K_F * (40 * Real.log m) ^ (4 * k - 1) *
                (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) * (40 * Real.log m)) := by ring
          _ ≤ dF * (5120 * (k : ℝ) * K_F * (40 : ℝ) ^ (4 * k) *
                (256 * 20 * K_F * (3 : ℝ) ^ 4) ^ (4 * k) * (Real.log m) ^ (20 * k + 1)) :=
              mul_le_mul_of_nonneg_left h1 hdF_pos.le
          _ ≤ dF * m ^ ε := mul_le_mul_of_nonneg_left hm3 hdF_pos.le
      exact h2.trans (mul_le_mul_of_nonneg_left hQ_gt.le (Real.rpow_pos_of_pos hm_pos _).le)
    calc (64 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1)) * Q ^ (4 * k - 1)
        = (128 * (k : ℝ) * K_F * dF * (40 * Real.log m) ^ (4 * k - 1) *
            (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k)) *
            ((1 / 2 : ℝ) * Q ^ (4 * k - 1) / (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k)) := by
          have hpos : (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) ≠ 0 := by positivity
          field_simp [hpos]; ring
      _ ≤ (m ^ (-ε / 2) * Q) *
            ((1 / 2 : ℝ) * Q ^ (4 * k - 1) / (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = m ^ (-ε / 2) * ((1 / 2 : ℝ) * (Q / (256 * 20 * K_F * (L : ℝ) ^ 4)) ^ (4 * k)) := by
          have hQpow : Q * Q ^ (4 * k - 1) = Q ^ (4 * k) := by
            rw [← pow_succ', show (4 * k - 1) + 1 = 4 * k by omega]
          have hdiv : (Q / (256 * 20 * K_F * (L : ℝ) ^ 4)) ^ (4 * k) =
              Q ^ (4 * k) / (256 * 20 * K_F * (L : ℝ) ^ 4) ^ (4 * k) := div_pow _ _ _
          rw [hdiv, ← hQpow]; ring
      _ ≤ m ^ (-ε / 2) * (C.card : ℝ) :=
          mul_le_mul_of_nonneg_left hC_Q (Real.rpow_pos_of_pos hm_pos _).le

/- ### Section 7: Assembly and Main Theorem -/

/-- Main theorem proving `OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2.H1`. -/
theorem main : OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2.H1 := by
  intro ε₀ hε₀
  let ε : ℝ := min ε₀ (1 / 12)
  have hε_pos : 0 < ε := lt_min hε₀ (by norm_num)
  have hε_le : ε ≤ 1 / 12 := min_le_right _ _
  have hε_le0 : ε ≤ ε₀ := min_le_left _ _
  let α : ℝ := 1 / 3 + ε
  have hα0 : 0 < α := by dsimp [α]; linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  let K₀ : ℕ := ⌈(32 : ℝ) ^ (1 / α)⌉₊ + 3
  let K_F : ℝ := 4 * (K₀ : ℝ)
  have hKF_ge1 : 1 ≤ K_F := by
    have : (3 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (show 3 ≤ K₀ by omega)
    dsimp [K_F]; linarith
  let k : ℕ := max 2 ⌈2 / ε⌉₊
  have hk2 : 2 ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := by omega
  have hkε : 2 / ε ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈2 / ε⌉₊)
  let ℓ : ℕ := ⌈16 * (k : ℝ) / ε⌉₊ + 2
  have hℓ2 : 2 ≤ ℓ := by omega
  have : NeZero k := ⟨by omega⟩
  have : NeZero ℓ := ⟨by omega⟩
  -- Thresholds from Lemma 2.13 (few `C_4`), Lemma 2.14 (many `C_4`), and Lemma 2.16 (`hsmall`):
  obtain ⟨M₁, hM₁⟩ := few_c4_betaGood hε_pos hε_le hKF_ge1 hk2 hkε
  obtain ⟨M₂, hM₂⟩ := many_c4_betaGood hε_pos hε_le hKF_ge1 hk2 hkε
  have hM₃_ev : ∀ᶠ m : ℕ in atTop,
      ((m : ℝ) ^ (4 * k)) * (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2 * (m : ℝ) ^ (-ε / 2))) ^ ℓ < 1 := by
    have hexp : (4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ) < 0 := by
      have hℓge : 16 * (k : ℝ) / ε ≤ (ℓ : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈16 * (k : ℝ) / ε⌉₊ ≤ ℓ by omega))
      have hmul : 16 * (k : ℝ) ≤ (ℓ : ℝ) * ε := (div_le_iff₀ hε_pos).mp hℓge
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      linarith
    have hlim : Tendsto (fun m : ℕ =>
        (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ * (m : ℝ) ^ ((4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ)))
        atTop (nhds 0) := by
      have hpow0 : Tendsto (fun m : ℕ => (m : ℝ) ^ ((4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ))) atTop (nhds 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < -((4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ)))).comp
          tendsto_natCast_atTop_atTop).congr fun m => by dsimp only [Function.comp_apply]; congr 1; ring
      simpa using (tendsto_const_nhds (x := (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ)).mul hpow0
    filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℕ)] with m hm hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have heq : ((m : ℝ) ^ (4 * k)) * (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2 * (m : ℝ) ^ (-ε / 2))) ^ ℓ =
        (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ * (m : ℝ) ^ ((4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ)) := by
      have h1 : (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2 * (m : ℝ) ^ (-ε / 2))) ^ ℓ =
          (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ * ((m : ℝ) ^ (-ε / 2)) ^ ℓ := by
        rw [← mul_pow]; congr 1; ring
      rw [h1, ← Real.rpow_natCast (m : ℝ) (4 * k), ← Real.rpow_natCast ((m : ℝ) ^ (-ε / 2)) ℓ,
        ← Real.rpow_mul hmpos.le]
      have hadd : (m : ℝ) ^ ((4 * k : ℕ) : ℝ) * (m : ℝ) ^ (-ε / 2 * (ℓ : ℝ)) =
          (m : ℝ) ^ ((4 * (k : ℝ)) - (ε / 2) * (ℓ : ℝ)) := by
        rw [← Real.rpow_add hmpos]; congr 1; push_cast; ring
      calc (m : ℝ) ^ ((4 * k : ℕ) : ℝ) * ((4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ *
              (m : ℝ) ^ (-ε / 2 * (ℓ : ℝ)))
          = (4 * (ℓ : ℝ) ^ 3 * (16 * (k : ℝ) ^ 2)) ^ ℓ *
              ((m : ℝ) ^ ((4 * k : ℕ) : ℝ) * (m : ℝ) ^ (-ε / 2 * (ℓ : ℝ))) := by ring
        _ = _ := by rw [hadd]
    rw [heq]; exact hm
  obtain ⟨M₃, hM₃⟩ := eventually_atTop.mp hM₃_ev
  let M_req := max (max M₁ M₂) (max M₃ 8)
  -- Choose `C₀ ≥ 2` large enough so `(2 * C₀)^(1/(1 - α)) ≥ 2 * M_req`, and set `C := 2 * C₀`:
  let C₀ : ℝ := max 2 ((2 * (M_req : ℝ)) ^ (1 - α))
  have hC₀_ge2 : 2 ≤ C₀ := le_max_left _ _
  have hC₀_ge1 : 1 ≤ C₀ := by linarith
  let C : ℝ := 2 * C₀
  have hC_pos : 0 ≤ C := by dsimp [C]; linarith
  -- Force `janzerGraph k ℓ hk1 hℓ2 ⊑ G` whenever `∀ v, C * |V|^α < deg(v)`:
  have hforce : ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      (∀ v, C * (Fintype.card V : ℝ) ^ α < (G.degree v : ℝ)) →
      janzerGraph k ℓ hk1 hℓ2 ⊑ G := by
    intro V _ hVne G hdeg
    have hGe : C₀ * (Fintype.card V : ℝ) ^ (1 + α) ≤ (G.edgeFinset.card : ℝ) := by
      have hsum : (Fintype.card V : ℝ) * (C * (Fintype.card V : ℝ) ^ α) ≤
          2 * (G.edgeFinset.card : ℝ) := by
        have h1 : (Fintype.card V : ℝ) * (C * (Fintype.card V : ℝ) ^ α) =
            ∑ _v : V, C * (Fintype.card V : ℝ) ^ α := by simp
        have h2 : ∑ v : V, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
        rw [h1, ← h2]
        exact Finset.sum_le_sum fun v _ => (hdeg v).le
      have hVpos : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos (α := V)
      have hpow : (Fintype.card V : ℝ) ^ (1 + α) = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ α := by
        rw [Real.rpow_add hVpos, Real.rpow_one]
      dsimp [C] at hsum; rw [hpow]; linarith
    obtain ⟨S, hSne, hm_lb, hdH, hΔH⟩ := exists_regularized_subgraph G hα0 hα1 hC₀_ge1 hGe hVne
    let H := G.induce (S : Set V)
    have hS_ge : M_req ≤ S.card := by
      have h1 : (2 * (M_req : ℝ)) ≤ (2 * C₀) ^ (1 / (1 - α)) := by
        have hC_ge : (2 * (M_req : ℝ)) ^ (1 - α) ≤ 2 * C₀ :=
          (le_max_right _ _).trans (by linarith)
        have hpow := Real.rpow_le_rpow (by positivity) hC_ge (by positivity : 0 ≤ 1 / (1 - α))
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith : 1 - α ≠ 0), Real.rpow_one] at hpow
        exact hpow
      have h2 : (M_req : ℝ) ≤ (S.card : ℝ) := by linarith
      exact_mod_cast h2
    have hS_eq : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
    have hH_edges4 : 4 ≤ H.edgeFinset.card := by
      have hm8 : 8 ≤ S.card := (le_max_right _ _).trans ((le_max_right _ _).trans hS_ge)
      have hmpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
      have h1 : (2 : ℝ) * (S.card : ℝ) ≤ 2 * (H.edgeFinset.card : ℝ) := by
        have hd2 : 2 ≤ 2 * (H.edgeFinset.card : ℝ) / (S.card : ℝ) := by
          calc (2 : ℝ) ≤ C₀ := hC₀_ge2
            _ ≤ C₀ * (S.card : ℝ) ^ α := by
                have h1 : (1 : ℝ) ≤ (S.card : ℝ) ^ α :=
                  Real.one_le_rpow (by exact_mod_cast (show 1 ≤ S.card by omega)) hα0.le
                nlinarith
            _ ≤ 2 * (H.edgeFinset.card : ℝ) / (S.card : ℝ) := hdH
        exact (le_div_iff₀ hmpos).mp hd2
      have : (8 : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
        have : (8 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hm8
        linarith
      exact_mod_cast (show (4 : ℝ) ≤ (H.edgeFinset.card : ℝ) by linarith)
    -- Pass to `C_4`-balanced spanning subgraph `F ≤ H`:
    obtain ⟨F, hFH, hFe_half, hFc4⟩ := exists_balanced_c4_spanning H
      (by rw [hS_eq]; have : 8 ≤ S.card := (le_max_right _ _).trans ((le_max_right _ _).trans hS_ge); omega)
      hH_edges4
    let m : ℝ := (Fintype.card (S : Set V) : ℝ)
    let dF : ℝ := 2 * (F.edgeFinset.card : ℝ) / m
    have hm_pos : 0 < m := by
      dsimp [m]; rw [Fintype.card_coe]; exact_mod_cast hSne.card_pos
    have hdF_ge : m ^ ((1 : ℝ) / 3 + ε) ≤ dF := by
      dsimp [dF, m, α] at hdH ⊢
      rw [Fintype.card_coe]
      have h2e : (H.edgeFinset.card : ℝ) ≤ 2 * (F.edgeFinset.card : ℝ) := by exact_mod_cast hFe_half
      calc (S.card : ℝ) ^ ((1 : ℝ) / 3 + ε)
          ≤ (C₀ / 2) * (S.card : ℝ) ^ ((1 : ℝ) / 3 + ε) := by
            have : 1 ≤ C₀ / 2 := by linarith
            nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < S.card by exact_mod_cast hSne.card_pos) ((1 : ℝ) / 3 + ε)]
        _ = (C₀ * (S.card : ℝ) ^ ((1 : ℝ) / 3 + ε)) / 2 := by ring
        _ ≤ (2 * (H.edgeFinset.card : ℝ) / (S.card : ℝ)) / 2 := div_le_div_of_nonneg_right hdH (by norm_num)
        _ = (H.edgeFinset.card : ℝ) / (S.card : ℝ) := by ring
        _ ≤ 2 * (F.edgeFinset.card : ℝ) / (S.card : ℝ) := div_le_div_of_nonneg_right h2e (by positivity)
    have hΔF : ∀ v : (S : Set V), (F.degree v : ℝ) ≤ K_F * dF := by
      intro v
      have hdeg_le : F.degree v ≤ H.degree v := by
        rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        exact Finset.card_le_card fun w hw => (mem_neighborFinset H _ _).mpr (hFH ((mem_neighborFinset F _ _).mp hw))
      have h2e : (H.edgeFinset.card : ℝ) ≤ 2 * (F.edgeFinset.card : ℝ) := by exact_mod_cast hFe_half
      calc (F.degree v : ℝ) ≤ (H.degree v : ℝ) := by exact_mod_cast hdeg_le
        _ ≤ (2 * (K₀ : ℝ)) * (2 * (H.edgeFinset.card : ℝ) / (S.card : ℝ)) := hΔH v
        _ ≤ (2 * (K₀ : ℝ)) * (2 * (2 * (F.edgeFinset.card : ℝ)) / (S.card : ℝ)) := by gcongr
        _ = K_F * dF := by dsimp [K_F, dF, m]; rw [Fintype.card_coe]; ring
    have hFc4' : ∀ e ∈ F.edgeFinset,
        (((orderedC4 F).filter (c4HasEdge e)).card : ℝ) ≤
          (40 * Real.log m / (m * dF)) * ((orderedC4 F).card : ℝ) := by
      intro e he
      have h := hFc4 e he
      have heq : 20 * Real.log m / (F.edgeFinset.card : ℝ) = 40 * Real.log m / (m * dF) := by
        have hFe_pos : (0 : ℝ) < (F.edgeFinset.card : ℝ) := by
          have h4 : 4 ≤ H.edgeFinset.card := hH_edges4
          have h2 : H.edgeFinset.card ≤ 2 * F.edgeFinset.card := by convert hFe_half
          have : 0 < F.edgeFinset.card := by omega
          exact_mod_cast this
        dsimp [dF]; field_simp [hm_pos.ne', hFe_pos.ne']; ring
      rwa [heq] at h
    -- Split into Few `C_4`s vs Many `C_4`s!
    have hex_good : ∃ Cset : Finset (Fin (8 * k) → (S : Set V)),
        Cset.Nonempty ∧ IsBetaGood F (m ^ (-ε / 2)) Cset := by
      by_cases hq : ((orderedC4 F).card : ℝ) ≤ dF ^ (5 : ℕ) / (40 * m ^ (3 * ε / 2) * Real.log m)
      · refine hM₁ (S : Set V) F (by rw [hS_eq]; exact (le_max_left _ _).trans ((le_max_left _ _).trans hS_ge))
          hdF_ge hΔF fun e he => (hFc4' e he).trans ?_
        have hlog_pos : 0 < Real.log m := Real.log_pos (by
          dsimp [m]; rw [Fintype.card_coe]
          have : 8 ≤ S.card := (le_max_right _ _).trans ((le_max_right _ _).trans hS_ge)
          exact_mod_cast (show 1 < S.card by omega))
        have hdF_pos : 0 < dF := lt_of_lt_of_le (Real.rpow_pos_of_pos hm_pos _) hdF_ge
        calc (40 * Real.log m / (m * dF)) * ((orderedC4 F).card : ℝ)
            ≤ (40 * Real.log m / (m * dF)) * (dF ^ (5 : ℕ) / (40 * m ^ (3 * ε / 2) * Real.log m)) :=
              mul_le_mul_of_nonneg_left hq (by positivity)
          _ = dF ^ (4 : ℕ) / m ^ (1 + 3 * ε / 2) := by
              rw [Real.rpow_add hm_pos, Real.rpow_one]
              have h1p : m ^ (3 * ε / 2) ≠ 0 := (Real.rpow_pos_of_pos hm_pos _).ne'
              field_simp [hm_pos.ne', hdF_pos.ne', hlog_pos.ne', h1p]
      · push Not at hq
        exact hM₂ (S : Set V) F (by rw [hS_eq]; exact (le_max_right _ _).trans ((le_max_left _ _).trans hS_ge))
          hdF_ge hΔF hFc4' hq
    obtain ⟨C₀set, hC₀ne, hgood⟩ := hex_good
    obtain ⟨Cnice, hCnice_ne, hnice⟩ := exists_betaNice_of_betaGood hk1 F
      (Real.rpow_pos_of_pos hm_pos _) C₀set hC₀ne hgood
    have hcopyF : janzerGraph k ℓ hk1 hℓ2 ⊑ F :=
      janzerGraph_copy_of_betaNice hk1 hℓ2 F (Real.rpow_pos_of_pos hm_pos _).le Cnice hCnice_ne hnice
        (hM₃ (Fintype.card (S : Set V)) (by rw [hS_eq]; exact (le_max_left _ _).trans ((le_max_right _ _).trans hS_ge)))
    have hcopyH : janzerGraph k ℓ hk1 hℓ2 ⊑ H :=
      hcopyF.trans ⟨⟨SimpleGraph.Hom.ofLE hFH, Function.injective_id⟩⟩
    exact hcopyH.trans ⟨Copy.induce G (S : Set V)⟩
  have hO_eps : (fun n : ℕ => (extremalNumber n (janzerGraph k ℓ hk1 hℓ2) : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (α + 1) :=
    extremal_of_degree_threshold (janzerGraph k ℓ hk1 hℓ2) hα0.le hC_pos hforce
  have hO : (fun n : ℕ => (extremalNumber n (janzerGraph k ℓ hk1 hℓ2) : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 - 2 / (3 : ℝ) + ε₀) := by
    refine hO_eps.trans (Asymptotics.IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hpos _).le,
        Real.norm_of_nonneg (Real.rpow_pos_of_pos hpos _).le, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [α]; linarith)
  have : Nonempty (Fin (4 * k) × Fin (2 * ℓ)) := ⟨⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  exact regular_witness_on_fin (janzerGraph k ℓ hk1 hℓ2) 3 (janzerGraph_isRegular k ℓ hk1 hℓ2) _ hO

end OMA.P_Erdos147_erdos_147_variants_janzer_conjecture_R2_H1

theorem OMA.solution : OMA.R_Erdos147_erdos_147_variants_janzer_conjecture_R2.H1 :=
  OMA.P_Erdos147_erdos_147_variants_janzer_conjecture_R2_H1.main


