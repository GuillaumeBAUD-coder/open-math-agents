import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3
import Mathlib

-- Credit: @kaceymon

/-!
# Qualitative Szemerédi for 4-term progressions from the tetrahedron removal lemma (Solymosi)

The target is step H2 of reduction R3 of `Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H1`:
a 4-AP-free subset of `[1, N]` of density at least `exp (-J)` forces `log log N` to be bounded.
That is the qualitative Szemerédi theorem for progressions of length four.

We follow Solymosi's derivation of the k = 4 case from the removal lemma for 3-uniform hypergraphs
(J. Solymosi, Note on a generalization of Roth's theorem, Algorithms Combin. 25 (2003), 825-827).
The hypergraph removal lemma for the tetrahedron is due to Frankl and Rödl (Random Structures
Algorithms 20 (2002)) and in general to Gowers and to Nagle, Rödl, Schacht and Skokan.

* H1: the tetrahedron removal lemma, stated for 4-partite 3-uniform hypergraphs with all four parts
  equal to a finite type `V`. A face set `E_j` lists the triples that omit the j-th vertex.
* H2: an elementary transfer lemma. Embed `[1, N]` into `ZMod M` with `M > 2 N`. A set with no
  4-term progression of positive step then has no 4-term progression in `ZMod M` with nonzero step.

The proof of `main` (Solymosi): put `M = 2 N + 1` and `V = ZMod M`, and let `S'` be the image of `S`.
A quadruple `(x, y, z, w)` spans a tetrahedron if the four linear forms
`-y - 2z - 3w`, `x - z - 2w`, `2x + y - w`, `3x + 2y + z` all lie in `S'`. Each form omits one
variable, and the four values form a progression with step `x + y + z + w`.
By H2 every tetrahedron has `w = -(x + y + z)`, so there are at most `M^3` of them.
The `M^2 |S|` tetrahedra with step zero are pairwise face-disjoint, so removing them costs at least
`M^2 |S|` faces. Removal at `eps = exp (-J) / 4` then gives `|S| <= eps * M`, which contradicts the
density hypothesis once `M >= 1 / delta`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3_H2_R1

open Finset

/-- The tetrahedron removal lemma for 4-partite 3-uniform hypergraphs (Frankl-Rödl): few
tetrahedra can be destroyed by deleting few faces. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (E₁ E₂ E₃ E₄ : Finset (V × V × V)),
      ((univ.filter fun q : V × V × V × V =>
          (q.2.1, q.2.2.1, q.2.2.2) ∈ E₁ ∧ (q.1, q.2.2.1, q.2.2.2) ∈ E₂ ∧
            (q.1, q.2.1, q.2.2.2) ∈ E₃ ∧ (q.1, q.2.1, q.2.2.1) ∈ E₄).card : ℝ)
          ≤ δ * (Fintype.card V : ℝ) ^ 4 →
        ∃ F₁ ⊆ E₁, ∃ F₂ ⊆ E₂, ∃ F₃ ⊆ E₃, ∃ F₄ ⊆ E₄,
          (((E₁ \ F₁).card + (E₂ \ F₂).card + (E₃ \ F₃).card + (E₄ \ F₄).card : ℕ) : ℝ)
              ≤ ε * (Fintype.card V : ℝ) ^ 3 ∧
            ∀ x y z w : V, ¬ ((y, z, w) ∈ F₁ ∧ (x, z, w) ∈ F₂ ∧ (x, y, w) ∈ F₃ ∧ (x, y, z) ∈ F₄)

/-- A subset of `[1, N]` with no 4-term progression of positive step has no 4-term progression
with nonzero step after reduction modulo any `M > 2 N`. -/
def H2 : Prop :=
  ∀ (M N : ℕ) (S : Finset ℕ), 2 * N < M → S ⊆ Finset.Icc 1 N →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
    ∀ t s : ZMod M, (∀ j : ℕ, j < 4 → t + (j : ZMod M) * s ∈ S.image (fun n : ℕ => (n : ZMod M))) →
      s = 0

/-- The density form of qualitative Szemerédi for 4-term progressions, from H1 and H2. -/
lemma szemeredi4 (hrem : H1) (htr : H2) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ N₁ : ℕ, ∀ (N : ℕ) (S : Finset ℕ), N₁ ≤ N → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) → δ₀ * (N : ℝ) ≤ (S.card : ℝ) → False := by
  classical
  obtain ⟨δ, hδ, hR⟩ := hrem (δ₀ / 4) (by positivity)
  refine ⟨⌈1 / δ⌉₊ + 1, ?_⟩
  intro N S hN hS hfree hdens
  set M : ℕ := 2 * N + 1 with hMdef
  haveI : NeZero M := ⟨by omega⟩
  set Sb : Finset (ZMod M) := S.image (fun n : ℕ => (n : ZMod M)) with hSb
  set E₁ : Finset (ZMod M × ZMod M × ZMod M) :=
    univ.filter fun f => -f.1 - 2 * f.2.1 - 3 * f.2.2 ∈ Sb with hE₁
  set E₂ : Finset (ZMod M × ZMod M × ZMod M) :=
    univ.filter fun f => f.1 - f.2.1 - 2 * f.2.2 ∈ Sb with hE₂
  set E₃ : Finset (ZMod M × ZMod M × ZMod M) :=
    univ.filter fun f => 2 * f.1 + f.2.1 - f.2.2 ∈ Sb with hE₃
  set E₄ : Finset (ZMod M × ZMod M × ZMod M) :=
    univ.filter fun f => 3 * f.1 + 2 * f.2.1 + f.2.2 ∈ Sb with hE₄
  have hcardV : Fintype.card (ZMod M) = M := ZMod.card M
  have hN1 : 1 ≤ N := by omega
  have hNδ : 1 / δ ≤ (N : ℝ) := by
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / δ⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈1 / δ⌉₊ ≤ N)
    linarith
  have hMR : (M : ℝ) = 2 * N + 1 := by rw [hMdef]; push_cast; ring
  have hδM : 1 ≤ δ * (M : ℝ) := by
    have : 1 ≤ δ * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_left hNδ hδ.le
      rwa [mul_one_div_cancel hδ.ne'] at this
    rw [hMR]; nlinarith
  -- every tetrahedron has step zero
  have hstep : ∀ x y z w : ZMod M, (y, z, w) ∈ E₁ → (x, z, w) ∈ E₂ → (x, y, w) ∈ E₃ →
      (x, y, z) ∈ E₄ → w = -(x + y + z) := by
    intro x y z w h1 h2 h3 h4
    simp only [hE₁, hE₂, hE₃, hE₄, mem_filter, mem_univ, true_and] at h1 h2 h3 h4
    have hs := htr M N S (by omega) hS hfree (-y - 2 * z - 3 * w) (x + y + z + w) (by
      intro j hj
      interval_cases j
      · have e : -y - 2 * z - 3 * w + ((0 : ℕ) : ZMod M) * (x + y + z + w) = -y - 2 * z - 3 * w := by
          push_cast; ring
        rw [e]; exact h1
      · have e : -y - 2 * z - 3 * w + ((1 : ℕ) : ZMod M) * (x + y + z + w) = x - z - 2 * w := by
          push_cast; ring
        rw [e]; exact h2
      · have e : -y - 2 * z - 3 * w + ((2 : ℕ) : ZMod M) * (x + y + z + w) = 2 * x + y - w := by
          push_cast; ring
        rw [e]; exact h3
      · have e : -y - 2 * z - 3 * w + ((3 : ℕ) : ZMod M) * (x + y + z + w) = 3 * x + 2 * y + z := by
          push_cast; ring
        rw [e]; exact h4)
    linear_combination hs
  -- few tetrahedra
  set Tet := (univ.filter fun q : ZMod M × ZMod M × ZMod M × ZMod M =>
      (q.2.1, q.2.2.1, q.2.2.2) ∈ E₁ ∧ (q.1, q.2.2.1, q.2.2.2) ∈ E₂ ∧
        (q.1, q.2.1, q.2.2.2) ∈ E₃ ∧ (q.1, q.2.1, q.2.2.1) ∈ E₄) with hTet
  have hTetle : Tet.card ≤ M ^ 3 := by
    have hsub : Tet ⊆ (univ : Finset (ZMod M × ZMod M × ZMod M)).image
        (fun p => (p.1, p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2))) := by
      intro q hq
      rw [hTet, mem_filter] at hq
      obtain ⟨_, h1, h2, h3, h4⟩ := hq
      have hw := hstep q.1 q.2.1 q.2.2.1 q.2.2.2 h1 h2 h3 h4
      rw [mem_image]
      refine ⟨(q.1, q.2.1, q.2.2.1), mem_univ _, ?_⟩
      show (q.1, q.2.1, q.2.2.1, -(q.1 + q.2.1 + q.2.2.1)) = q
      rw [← hw]
    calc Tet.card ≤ _ := card_le_card hsub
      _ ≤ (univ : Finset (ZMod M × ZMod M × ZMod M)).card := card_image_le
      _ = M ^ 3 := by simp [Finset.card_univ, Fintype.card_prod, hcardV]; ring
  have hTetR : (Tet.card : ℝ) ≤ δ * (Fintype.card (ZMod M) : ℝ) ^ 4 := by
    rw [hcardV]
    have h1 : (Tet.card : ℝ) ≤ (M : ℝ) ^ 3 := by exact_mod_cast hTetle
    have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
    calc (Tet.card : ℝ) ≤ (M : ℝ) ^ 3 := h1
      _ = 1 * (M : ℝ) ^ 3 := by ring
      _ ≤ (δ * M) * (M : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hδM hM0
      _ = δ * (M : ℝ) ^ 4 := by ring
  obtain ⟨F₁, hF₁, F₂, hF₂, F₃, hF₃, F₄, hF₄, hdel, hnoT⟩ := hR (ZMod M) E₁ E₂ E₃ E₄ hTetR
  -- the zero-step tetrahedra
  have hSbcard : Sb.card = S.card := by
    rw [hSb]
    apply card_image_of_injOn
    intro a ha b hb hab
    have ha' := hS ha; have hb' := hS hb
    rw [Finset.mem_Icc] at ha' hb'
    have := (ZMod.natCast_eq_natCast_iff' a b M).mp hab
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hE4card : E₄.card = M * M * S.card := by
    rw [← hSbcard]
    have : E₄.card = ((univ : Finset (ZMod M)) ×ˢ ((univ : Finset (ZMod M)) ×ˢ Sb)).card := by
      refine Finset.card_bij' (fun p _ => (p.1, p.2.1, 3 * p.1 + 2 * p.2.1 + p.2.2))
        (fun p _ => (p.1, p.2.1, p.2.2 - 3 * p.1 - 2 * p.2.1)) ?_ ?_ ?_ ?_
      · intro p hp
        rw [hE₄, mem_filter] at hp
        simp only [mem_product, mem_univ, true_and]
        exact hp.2
      · intro p hp
        simp only [mem_product, mem_univ, true_and] at hp
        rw [hE₄, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        have e : 3 * p.1 + 2 * p.2.1 + (p.2.2 - 3 * p.1 - 2 * p.2.1) = p.2.2 := by ring
        simpa only [e] using hp
      · intro p _
        obtain ⟨a, b, c⟩ := p
        simp only [Prod.mk.injEq, true_and]
        ring
      · intro p _
        obtain ⟨a, b, c⟩ := p
        simp only [Prod.mk.injEq, true_and]
        ring
    rw [this, card_product, card_product, card_univ, hcardV, mul_assoc]
  -- every zero-step tetrahedron loses a face
  set D₁ := E₄.filter fun p => (p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∉ F₁ with hD₁
  set D₂ := E₄.filter fun p => (p.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∉ F₂ with hD₂
  set D₃ := E₄.filter fun p => (p.1, p.2.1, -(p.1 + p.2.1 + p.2.2)) ∉ F₃ with hD₃
  set D₄ := E₄.filter fun p => (p.1, p.2.1, p.2.2) ∉ F₄ with hD₄
  have hcover : E₄ ⊆ D₁ ∪ D₂ ∪ D₃ ∪ D₄ := by
    intro p hp
    simp only [hD₁, hD₂, hD₃, hD₄, mem_union, mem_filter]
    by_cases h1 : (p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∈ F₁
    · by_cases h2 : (p.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∈ F₂
      · by_cases h3 : (p.1, p.2.1, -(p.1 + p.2.1 + p.2.2)) ∈ F₃
        · right; exact ⟨hp, fun h4 => hnoT _ _ _ _ ⟨h1, h2, h3, h4⟩⟩
        · left; right; exact ⟨hp, h3⟩
      · left; left; right; exact ⟨hp, h2⟩
    · left; left; left; exact ⟨hp, h1⟩
  have hfaces : ∀ p ∈ E₄, (p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∈ E₁ ∧
      (p.1, p.2.2, -(p.1 + p.2.1 + p.2.2)) ∈ E₂ ∧ (p.1, p.2.1, -(p.1 + p.2.1 + p.2.2)) ∈ E₃ ∧
      (p.1, p.2.1, p.2.2) ∈ E₄ := by
    intro p hp
    have hv : 3 * p.1 + 2 * p.2.1 + p.2.2 ∈ Sb := by
      have hp' := hp
      rw [hE₄, mem_filter] at hp'
      exact hp'.2
    refine ⟨?_, ?_, ?_, hp⟩
    · rw [hE₁, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have e : -p.2.1 - 2 * p.2.2 - 3 * -(p.1 + p.2.1 + p.2.2) = 3 * p.1 + 2 * p.2.1 + p.2.2 := by ring
      rw [e]; exact hv
    · rw [hE₂, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have e : p.1 - p.2.2 - 2 * -(p.1 + p.2.1 + p.2.2) = 3 * p.1 + 2 * p.2.1 + p.2.2 := by ring
      rw [e]; exact hv
    · rw [hE₃, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have e : 2 * p.1 + p.2.1 - -(p.1 + p.2.1 + p.2.2) = 3 * p.1 + 2 * p.2.1 + p.2.2 := by ring
      rw [e]; exact hv
  have hc₁ : D₁.card ≤ (E₁ \ F₁).card := by
    apply card_le_card_of_injOn (fun p => (p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)))
    · intro p hp
      simp only [hD₁, Finset.mem_coe, mem_filter] at hp
      simp only [Finset.mem_coe]
      exact mem_sdiff.mpr ⟨(hfaces p hp.1).1, hp.2⟩
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1, h2, h3⟩ := hpq
      have h0 : p.1 = q.1 := by linear_combination -h3 - h1 - h2
      ext <;> simp [h0, h1, h2]
  have hc₂ : D₂.card ≤ (E₂ \ F₂).card := by
    apply card_le_card_of_injOn (fun p => (p.1, p.2.2, -(p.1 + p.2.1 + p.2.2)))
    · intro p hp
      simp only [hD₂, Finset.mem_coe, mem_filter] at hp
      simp only [Finset.mem_coe]
      exact mem_sdiff.mpr ⟨(hfaces p hp.1).2.1, hp.2⟩
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1, h2, h3⟩ := hpq
      have h0 : p.2.1 = q.2.1 := by linear_combination -h3 - h1 - h2
      ext <;> simp [h0, h1, h2]
  have hc₃ : D₃.card ≤ (E₃ \ F₃).card := by
    apply card_le_card_of_injOn (fun p => (p.1, p.2.1, -(p.1 + p.2.1 + p.2.2)))
    · intro p hp
      simp only [hD₃, Finset.mem_coe, mem_filter] at hp
      simp only [Finset.mem_coe]
      exact mem_sdiff.mpr ⟨(hfaces p hp.1).2.2.1, hp.2⟩
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1, h2, h3⟩ := hpq
      have h0 : p.2.2 = q.2.2 := by linear_combination -h3 - h1 - h2
      ext <;> simp [h0, h1, h2]
  have hc₄ : D₄.card ≤ (E₄ \ F₄).card := by
    apply card_le_card_of_injOn (fun p => (p.1, p.2.1, p.2.2))
    · intro p hp
      simp only [hD₄, Finset.mem_coe, mem_filter] at hp
      simp only [Finset.mem_coe]
      exact mem_sdiff.mpr ⟨(hfaces p hp.1).2.2.2, hp.2⟩
    · intro p _ q _ hpq
      simpa using hpq
  have hE4le : E₄.card ≤ (E₁ \ F₁).card + (E₂ \ F₂).card + (E₃ \ F₃).card + (E₄ \ F₄).card := by
    calc E₄.card ≤ (D₁ ∪ D₂ ∪ D₃ ∪ D₄).card := card_le_card hcover
      _ ≤ D₁.card + D₂.card + D₃.card + D₄.card := by
        refine (card_union_le _ _).trans ?_
        refine Nat.add_le_add_right ((card_union_le _ _).trans ?_) _
        exact Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ _ := by omega
  -- conclude
  rw [hcardV] at hdel
  have hmain : ((M * M * S.card : ℕ) : ℝ) ≤ δ₀ / 4 * (M : ℝ) ^ 3 := by
    rw [← hE4card]
    exact le_trans (by exact_mod_cast hE4le) hdel
  push_cast at hmain
  have hMpos : (0 : ℝ) < M := by rw [hMR]; positivity
  have hS' : (S.card : ℝ) ≤ δ₀ / 4 * M := by
    have h2 : (M : ℝ) * M * S.card ≤ (M * M) * (δ₀ / 4 * M) := by nlinarith
    have hMM : (0 : ℝ) < M * M := by positivity
    exact le_of_mul_le_mul_left (by linarith) hMM
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [hMR] at hS'
  nlinarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3.H2 := by
  intro hrem htr J
  obtain ⟨N₁, hN₁⟩ := szemeredi4 hrem htr (Real.exp (-(J : ℝ))) (Real.exp_pos _)
  refine ⟨Real.log (Real.log ((max N₁ 2 : ℕ) : ℝ)) + 1, ?_⟩
  intro N S hN hS hfree hdens
  by_contra hQ
  push Not at hQ
  have hlt : max N₁ 2 < N := by
    by_contra h
    push Not at h
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have h1 : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log ((max N₁ 2 : ℕ) : ℝ)) := by
      apply Real.log_le_log hlogN
      apply Real.log_le_log (by positivity)
      exact_mod_cast h
    linarith
  exact hN₁ N S (by omega) hS hfree (by rw [mul_comm]; exact hdens)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3_H2_R1
