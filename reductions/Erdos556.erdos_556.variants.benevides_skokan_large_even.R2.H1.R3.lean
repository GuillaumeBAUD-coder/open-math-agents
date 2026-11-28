import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1.R3 of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1
-- Credit: @gmarisi
-- uses note #86260

open Filter SimpleGraph Finset

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R3

def H1 : Prop :=
  ∀ α μ δ : ℝ, 0 < α → α ≤ 1 → 0 < μ → μ ≤ α / 100000 → 0 < δ →
  ∀ᶠ m : ℕ in atTop,
  ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
    (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
    (∃ i, cycleGraph (2 * m) ⊑ c i) ∨
    ∃ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)),
    let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
    let B := fun S : Finset (Fin 4) => Finset.univ.filter (fun v : Fin (4 * m) => f v ∈ S)
    let dense := fun (β : ℝ) (i : Fin 3) (S T : Finset (Fin 4)) =>
      (1 - β) * ((B S).card : ℝ) * (B T).card ≤
        ∑ x ∈ B S, (((B T).filter ((c (σ i)).Adj x)).card : ℝ)
    ((∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
      ∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
        dense α k S T) ∨
    ((∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
      ∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (1, {0, 1}, {2}), (2, {0, 1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
        dense α k S T) ∨
    (((1 - 4 / 5 * μ) * (m : ℝ) ≤ min ((W 0).card : ℝ) (min ((W 1).card : ℝ) ((W 2).card : ℝ)) ∧
      μ * (m : ℝ) ≤ (W 3).card ∧
      max ((W 1).card : ℝ) (max ((W 2).card : ℝ) ((W 3).card : ℝ)) + μ * (m : ℝ) ≤ (W 0).card ∧
      ((W 0).card : ℝ) + (W 3).card ≤ (1 + 3 / 10 * μ) * (2 * m)) ∧
      ∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
        dense δ k S T)

def H2 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ n : ℕ in atTop, Even n →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (∀ j, (1 - α) * n / 2 ≤ (Nat.card {v // f v = j} : ℝ)) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - α) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

def H3 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ᶠ n : ℕ in atTop, Even n → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ c : Fin 3 → SimpleGraph (Fin (2 * n)), (⊤ : SimpleGraph (Fin (2 * n))).IsEdgeColouring c →
        ∀ f : Fin (2 * n) → Fin 4,
          (let a : Fin 4 → ℝ := (fun j => Nat.card {v // f v = j});
            (1 - 4 / 5 * μ) * n / 2 ≤ min (a 0) (min (a 1) (a 2)) ∧ μ * n / 2 ≤ a 3 ∧
            max (a 1) (max (a 2) (a 3)) + μ * n / 2 ≤ a 0 ∧ a 0 + a 3 ≤ (1 + 3 / 10 * μ) * n) →
          (∀ k S T, (k, S, T) ∈ ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] : List (Fin 3 × Finset (Fin 4) × Finset (Fin 4))) →
            (1 - δ) * Nat.card {v // f v ∈ S} * Nat.card {v // f v ∈ T} ≤
              (Nat.card {e : Fin (2 * n) × Fin (2 * n) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c k).Adj e.1 e.2} : ℝ)) →
          ∃ i, cycleGraph n ⊑ c i

lemma edgeColouring_permute {V : Type*} (c : Fin 3 → SimpleGraph V)
    (hc : (⊤ : SimpleGraph V).IsEdgeColouring c) (σ : Equiv.Perm (Fin 3)) :
    (⊤ : SimpleGraph V).IsEdgeColouring (fun k => c (σ k)) := by
  constructor
  · rw [hc.1]
    exact (Equiv.iSup_comp (g := c) σ).symm
  · intro i j hij
    exact hc.2 (σ i) (σ j) (fun h => hij (σ.injective h))

lemma relation_count {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r] :
    Nat.card {e : V × V // e.1 ∈ X ∧ e.2 ∈ Y ∧ r e.1 e.2} =
      ∑ x ∈ X, (Y.filter (r x)).card := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : V => x ∈ X ∧ y ∈ Y ∧ r x y)), Fintype.card_sigma]
  calc
    _ = ∑ x : V, if x ∈ X then (Y.filter (r x)).card else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ X
      · simp only [if_pos hx, Fintype.card_subtype]
        congr 1
        ext y
        simp [hx]
      · simp [hx]
    _ = _ := by simp

lemma relation_count_symm {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : Finset V) (r : V → V → Prop) [DecidableRel r]
    (hr : ∀ x y, r x y → r y x) :
    (∑ x ∈ X, (Y.filter (r x)).card) = ∑ y ∈ Y, (X.filter (r y)).card := by
  rw [← relation_count X Y r, ← relation_count Y X r]
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨(e.val.2, e.val.1), e.property.2.1, e.property.1,
      hr _ _ e.property.2.2⟩
    invFun := fun e => ⟨(e.val.2, e.val.1), e.property.2.1, e.property.1,
      hr _ _ e.property.2.2⟩
    left_inv := fun e => by cases e; rfl
    right_inv := fun e => by cases e; rfl }

theorem main : H1 → H2 → H3 → OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2.H1 := by
  classical
  intro h1 h2 h3 α hα
  obtain ⟨α₁, hα₁, habs₁⟩ := h2
  obtain ⟨μ₀, hμ₀, habs₃⟩ := h3
  let β : ℝ := min α (min α₁ 1)
  have hβ : 0 < β := lt_min hα (lt_min hα₁ (by norm_num))
  have hβα : β ≤ α := min_le_left _ _
  have hβα₁ : β ≤ α₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hβone : β ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let μ : ℝ := min (μ₀ / 2) (β / 200000)
  have hμ : 0 < μ := lt_min (by positivity) (by positivity)
  have hμ₀' : μ ≤ μ₀ := by
    have hh : μ ≤ μ₀ / 2 := min_le_left _ _
    linarith
  have hμsmall : μ ≤ β / 100000 := by
    have hh : μ ≤ β / 200000 := min_le_right _ _
    linarith
  obtain ⟨δ, hδ, habs₃'⟩ := habs₃ μ hμ hμ₀'
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (h1 β μ δ hβ hβone hμ hμsmall hδ)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (habs₁ β hβ hβα₁)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp habs₃'
  filter_upwards [Filter.eventually_ge_atTop (max M₀ (max N₁ N₃))] with m hm
  intro c _ hc
  have hm₀ : M₀ ≤ m := (le_max_left _ _).trans hm
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm₃ : N₃ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  rcases hM₀ m hm₀ c hc with hcyc | ⟨f, σ, hcases⟩
  · exact Or.inl hcyc
  · let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
    let B := fun S : Finset (Fin 4) => Finset.univ.filter (fun v : Fin (4 * m) => f v ∈ S)
    have hcardW (j : Fin 4) : Nat.card {v : Fin (4 * m) // f v = j} = (W j).card := by
      simp [W, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcardB (S : Finset (Fin 4)) : Nat.card {v : Fin (4 * m) // f v ∈ S} = (B S).card := by
      simp [B, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hpair (k : Fin 3) (S T : Finset (Fin 4)) :
        Nat.card {e : Fin (4 * m) × Fin (4 * m) // f e.1 ∈ S ∧ f e.2 ∈ T ∧ (c (σ k)).Adj e.1 e.2} =
          ∑ x ∈ B S, ((B T).filter ((c (σ k)).Adj x)).card := by
      simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using
        relation_count (B S) (B T) ((c (σ k)).Adj)
    have half_double (x : ℝ) : x * (2 * (m : ℝ)) / 2 = x * m := by ring
    rcases hcases with ⟨hsz, hdn⟩ | ⟨hsz, hdn⟩ | ⟨hsz, hdn⟩
    · left
      have hev : Even (2 * m) := ⟨m, by omega⟩
      have h1' := hN₁ (2 * m) (by omega) hev
      rw [show 2 * (2 * m) = 4 * m by omega] at h1'
      obtain ⟨i, hi⟩ := h1' (fun k => c (σ k)) (edgeColouring_permute c hc σ) f (by
        intro j
        rw [hcardW j]
        have := hsz j
        push_cast
        linarith) (by
        intro k S T hmem
        rw [hcardB S, hcardB T, hpair k S T]
        push_cast
        exact hdn k S T hmem)
      exact ⟨σ i, hi⟩
    · right
      refine ⟨f, σ, ?_, ?_, ?_, ?_⟩
      · intro j
        have := hsz j
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      · have h0 : (1 - β) * ((B {0}).card : ℝ) * (B {1}).card ≤
            ∑ x ∈ B {0}, (((B {1}).filter ((c (σ 0)).Adj x)).card : ℝ) := hdn 0 {0} {1} (by simp)
        have hB0 : B {0} = W 0 := by ext v; simp [B, W]
        have hB1 : B {1} = W 1 := by ext v; simp [B, W]
        rw [hB0, hB1] at h0
        change (1 - α) * ((W 0).card : ℝ) * (W 1).card ≤
          ∑ x ∈ W 0, (((W 1).filter ((c (σ 0)).Adj x)).card : ℝ)
        have hnn : (0 : ℝ) ≤ ((W 0).card : ℝ) * (W 1).card := by positivity
        nlinarith
      · have h1' : (1 - β) * ((B {0, 1}).card : ℝ) * (B {2}).card ≤
            ∑ x ∈ B {0, 1}, (((B {2}).filter ((c (σ 1)).Adj x)).card : ℝ) := hdn 1 {0, 1} {2} (by simp)
        have hB01 : B {0, 1} = W 0 ∪ W 1 := by ext v; simp [B, W]
        have hB2 : B {2} = W 2 := by ext v; simp [B, W]
        rw [hB01, hB2] at h1'
        have hsym := relation_count_symm (W 0 ∪ W 1) (W 2) (c (σ 1)).Adj (fun _ _ h => h.symm)
        have hsymR : (∑ x ∈ W 0 ∪ W 1, (((W 2).filter ((c (σ 1)).Adj x)).card : ℝ)) =
            ∑ x ∈ W 2, (((W 0 ∪ W 1).filter ((c (σ 1)).Adj x)).card : ℝ) := by
          exact_mod_cast hsym
        rw [hsymR] at h1'
        change (1 - α) * ((W 2).card : ℝ) * (W 0 ∪ W 1).card ≤
          ∑ x ∈ W 2, (((W 0 ∪ W 1).filter ((c (σ 1)).Adj x)).card : ℝ)
        have hnn : (0 : ℝ) ≤ ((W 2).card : ℝ) * ((W 0 ∪ W 1).card : ℝ) := by positivity
        nlinarith
      · have h2' : (1 - β) * ((B {0, 1}).card : ℝ) * (B {3}).card ≤
            ∑ x ∈ B {0, 1}, (((B {3}).filter ((c (σ 2)).Adj x)).card : ℝ) := hdn 2 {0, 1} {3} (by simp)
        have hB01 : B {0, 1} = W 0 ∪ W 1 := by ext v; simp [B, W]
        have hB3 : B {3} = W 3 := by ext v; simp [B, W]
        rw [hB01, hB3] at h2'
        have hsym := relation_count_symm (W 0 ∪ W 1) (W 3) (c (σ 2)).Adj (fun _ _ h => h.symm)
        have hsymR : (∑ x ∈ W 0 ∪ W 1, (((W 3).filter ((c (σ 2)).Adj x)).card : ℝ)) =
            ∑ x ∈ W 3, (((W 0 ∪ W 1).filter ((c (σ 2)).Adj x)).card : ℝ) := by
          exact_mod_cast hsym
        rw [hsymR] at h2'
        change (1 - α) * ((W 3).card : ℝ) * (W 0 ∪ W 1).card ≤
          ∑ x ∈ W 3, (((W 0 ∪ W 1).filter ((c (σ 2)).Adj x)).card : ℝ)
        have hnn : (0 : ℝ) ≤ ((W 3).card : ℝ) * ((W 0 ∪ W 1).card : ℝ) := by positivity
        nlinarith
    · left
      have hev : Even (2 * m) := ⟨m, by omega⟩
      have h3' := hN₃ (2 * m) (by omega) hev δ hδ le_rfl
      rw [show 2 * (2 * m) = 4 * m by omega] at h3'
      obtain ⟨i, hi⟩ := h3' (fun k => c (σ k)) (edgeColouring_permute c hc σ) f (by
        rcases hsz with ⟨s1, s2, s3, s4⟩
        simp only [hcardW]
        refine ⟨?_, ?_, ?_, ?_⟩
        · push_cast; linarith
        · push_cast; linarith
        · push_cast; linarith
        · push_cast; linarith) (by
        intro k S T hmem
        rw [hcardB S, hcardB T, hpair k S T]
        push_cast
        exact hdn k S T hmem)
      exact ⟨σ i, hi⟩

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R3
