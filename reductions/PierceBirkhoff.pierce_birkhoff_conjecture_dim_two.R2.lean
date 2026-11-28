import FormalConjectures.Wikipedia.PierceBirkhoff
import Mathlib

/-!
# Reduction of the 2-dimensional Pierce-Birkhoff conjecture via Madden's real-spectrum framework

This reduction proves Madden's (1989) equivalence between the global Pierce-Birkhoff representation
`f = sup_i inf_j g_{i,j}` and the local separating-ideal condition on `Sper ℝ[X, Y]`, using:
- Tychonoff compactness of the constructible topology on prime cones (`MvPolynomial (Fin 2) ℝ → Bool`),
- Madden's algebraic square-decomposition trick `a = ((a + 1) / 2)^2 - ((a - 1) / 2)^2`,
- Double compactness on the clopen constructible sets covering `Sper ℝ[X, Y]`.

The remaining three independent classical pillars are:
- `H1`: Artin-Lang / Tarski-Seidenberg transfer in `ℝ[X, Y]`.
- `H2`: Finiteness theorem for closed semialgebraic sets in `ℝ²` (Bochnak-Coste-Roy 2.7.2).
- `H3`: Mahé-Madden local separation theorem in `Sper ℝ[X, Y]`.
-/

namespace OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R2

/-- Artin-Lang / Tarski-Seidenberg transfer for `ℝ[X, Y]`: every nonempty basic constructible
subset of `Sper ℝ[X, Y]` contains a classical real point `x : Fin 2 → ℝ`. -/
def H1 : Prop :=
  ∀ (α : Set (MvPolynomial (Fin 2) ℝ)),
    (0 ∈ α ∧ 1 ∈ α ∧ (-1 : MvPolynomial (Fin 2) ℝ) ∉ α ∧
      (∀ p q, p ∈ α → q ∈ α → p + q ∈ α) ∧
      (∀ p q, p ∈ α → q ∈ α → p * q ∈ α) ∧
      (∀ p, p ∈ α ∨ -p ∈ α) ∧
      (∀ p q, p * q ∈ α → -(p * q) ∈ α → (p ∈ α ∧ -p ∈ α) ∨ (q ∈ α ∧ -q ∈ α))) →
    ∀ (p₀ p₁ : Finset (MvPolynomial (Fin 2) ℝ)),
      (∀ p ∈ p₀, p ∈ α ∧ -p ∈ α) →
      (∀ p ∈ p₁, -p ∉ α) →
      ∃ x : Fin 2 → ℝ,
        (∀ p ∈ p₀, MvPolynomial.eval x p = 0) ∧
        (∀ p ∈ p₁, 0 < MvPolynomial.eval x p)

/-- Finiteness theorem for closed semialgebraic sets in `ℝ²` (Bochnak-Coste-Roy, Theorem 2.7.2):
every closed semialgebraic subset of `ℝ²` is a finite union of basic closed semialgebraic sets. -/
def H2 : Prop :=
  ∀ (S : Set (Fin 2 → ℝ)),
    IsClosed S →
    PierceBirkhoff.IsSemiAlgebraic S →
    ∃ (F : Finset (Finset (MvPolynomial (Fin 2) ℝ))),
      S = ⋃ s ∈ F, {x : Fin 2 → ℝ | ∀ p ∈ s, 0 ≤ MvPolynomial.eval x p}

/-- Mahé-Madden local separation theorem in `Sper ℝ[X, Y]`: for any finite cover of `Sper ℝ[X, Y]`
by basic closed constructible sets with polynomials agreeing on overlaps, the difference `g i - g j`
lies in the separating ideal `⟨α, β⟩` whenever `α ∈ P̃ i` and `β ∈ P̃ j`. -/
def H3 : Prop :=
  let isCone : Set (MvPolynomial (Fin 2) ℝ) → Prop := fun α =>
    0 ∈ α ∧ 1 ∈ α ∧ (-1 : MvPolynomial (Fin 2) ℝ) ∉ α ∧
      (∀ p q, p ∈ α → q ∈ α → p + q ∈ α) ∧
      (∀ p q, p ∈ α → q ∈ α → p * q ∈ α) ∧
      (∀ p, p ∈ α ∨ -p ∈ α) ∧
      (∀ p q, p * q ∈ α → -(p * q) ∈ α → (p ∈ α ∧ -p ∈ α) ∨ (q ∈ α ∧ -q ∈ α))
  ∀ (ι : Type) [Finite ι]
    (F : ι → Finset (Finset (MvPolynomial (Fin 2) ℝ)))
    (g : ι → MvPolynomial (Fin 2) ℝ),
    (∀ α, isCone α → ∃ i, ∃ s ∈ F i, ∀ p ∈ s, p ∈ α) →
    (∀ i j α, isCone α →
      (∃ s ∈ F i, ∀ p ∈ s, p ∈ α) →
      (∃ s ∈ F j, ∀ p ∈ s, p ∈ α) →
      g i - g j ∈ α ∧ -(g i - g j) ∈ α) →
    ∀ i j α β, isCone α → isCone β →
      (∃ s ∈ F i, ∀ p ∈ s, p ∈ α) →
      (∃ s ∈ F j, ∀ p ∈ s, p ∈ β) →
      g i - g j ∈ Ideal.span {s : MvPolynomial (Fin 2) ℝ | s ∈ α ∧ -s ∈ β}

lemma supinf_eq {ι κ : Type} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (a : ι → κ → ℝ) (y : ℝ) (h1 : ∀ i, ∃ j, a i j ≤ y) (h2 : ∃ i, ∀ j, y ≤ a i j) :
    ⨆ i, ⨅ j, a i j = y := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    obtain ⟨j, hj⟩ := h1 i
    exact (ciInf_le (Set.finite_range _).bddBelow j).trans hj
  · obtain ⟨i, hi⟩ := h2
    exact (le_ciInf hi).trans (le_ciSup (Set.finite_range (fun i => ⨅ j, a i j)).bddAbove i)

lemma cone_sq_mem {α : Set (MvPolynomial (Fin 2) ℝ)}
    (hmul : ∀ p q, p ∈ α → q ∈ α → p * q ∈ α)
    (htot : ∀ p, p ∈ α ∨ -p ∈ α)
    (u : MvPolynomial (Fin 2) ℝ) : u * u ∈ α := by
  rcases htot u with hu | hnu
  · exact hmul u u hu hu
  · simpa [neg_mul_neg] using hmul (-u) (-u) hnu hnu

lemma separating_ideal_decomp
    {α β : Set (MvPolynomial (Fin 2) ℝ)}
    (hα0 : (0 : MvPolynomial (Fin 2) ℝ) ∈ α)
    (hαadd : ∀ p q, p ∈ α → q ∈ α → p + q ∈ α)
    (hαmul : ∀ p q, p ∈ α → q ∈ α → p * q ∈ α)
    (hαtot : ∀ p, p ∈ α ∨ -p ∈ α)
    (hβ0 : (0 : MvPolynomial (Fin 2) ℝ) ∈ β)
    (hβadd : ∀ p q, p ∈ β → q ∈ β → p + q ∈ β)
    (hβmul : ∀ p q, p ∈ β → q ∈ β → p * q ∈ β)
    (hβtot : ∀ p, p ∈ β ∨ -p ∈ β)
    {r : MvPolynomial (Fin 2) ℝ}
    (hr : r ∈ Ideal.span {s : MvPolynomial (Fin 2) ℝ | s ∈ α ∧ -s ∈ β}) :
    ∃ P Q : MvPolynomial (Fin 2) ℝ,
      (P ∈ α ∧ -P ∈ β) ∧ (Q ∈ α ∧ -Q ∈ β) ∧ r = P - Q := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hr
  · intro s hs
    exact ⟨s, 0, hs, ⟨hα0, by simpa using hβ0⟩, by ring⟩
  · exact ⟨0, 0, ⟨hα0, by simpa using hβ0⟩, ⟨hα0, by simpa using hβ0⟩, by ring⟩
  · rintro x y _ _ ⟨Px, Qx, hPx, hQx, rfl⟩ ⟨Py, Qy, hPy, hQy, rfl⟩
    refine ⟨Px + Py, Qx + Qy,
      ⟨hαadd _ _ hPx.1 hPy.1, by rw [neg_add]; exact hβadd _ _ hPx.2 hPy.2⟩,
      ⟨hαadd _ _ hQx.1 hQy.1, by rw [neg_add]; exact hβadd _ _ hQx.2 hQy.2⟩,
      by ring⟩
  · rintro a x _ ⟨Px, Qx, hPx, hQx, rfl⟩
    set u : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (1 / 2 : ℝ) * (a + 1)
    set v : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (1 / 2 : ℝ) * (a - 1)
    have huα : u * u ∈ α := cone_sq_mem hαmul hαtot u
    have hvα : v * v ∈ α := cone_sq_mem hαmul hαtot v
    have huβ : u * u ∈ β := cone_sq_mem hβmul hβtot u
    have hvβ : v * v ∈ β := cone_sq_mem hβmul hβtot v
    have huv : u * u - v * v = a := by
      have h4 : (MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) *
          MvPolynomial.C (1 / 2 : ℝ) = MvPolynomial.C (1 / 4 : ℝ) := by
        rw [← map_mul]; norm_num
      have h1 : (4 : MvPolynomial (Fin 2) ℝ) * MvPolynomial.C (1 / 4 : ℝ) = 1 := by
        rw [← map_ofNat (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ) 4, ← map_mul]
        norm_num
      calc u * u - v * v
          = ((MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) *
              MvPolynomial.C (1 / 2 : ℝ)) *
              ((a + 1) * (a + 1) - (a - 1) * (a - 1)) := by ring
        _ = MvPolynomial.C (1 / 4 : ℝ) * ((4 : MvPolynomial (Fin 2) ℝ) * a) := by
              rw [h4]; ring
        _ = ((4 : MvPolynomial (Fin 2) ℝ) * MvPolynomial.C (1 / 4 : ℝ)) * a := by ring
        _ = a := by rw [h1, one_mul]
    refine ⟨u * u * Px + v * v * Qx, u * u * Qx + v * v * Px,
      ⟨hαadd _ _ (hαmul _ _ huα hPx.1) (hαmul _ _ hvα hQx.1), ?_⟩,
      ⟨hαadd _ _ (hαmul _ _ huα hQx.1) (hαmul _ _ hvα hPx.1), ?_⟩, ?_⟩
    · have : -(u * u * Px + v * v * Qx) = u * u * (-Px) + v * v * (-Qx) := by ring
      rw [this]
      exact hβadd _ _ (hβmul _ _ huβ hPx.2) (hβmul _ _ hvβ hQx.2)
    · have : -(u * u * Qx + v * v * Px) = u * u * (-Qx) + v * v * (-Px) := by ring
      rw [this]
      exact hβadd _ _ (hβmul _ _ huβ hQx.2) (hβmul _ _ hvβ hPx.2)
    · calc a • (Px - Qx) = a * (Px - Qx) := rfl
        _ = (u * u - v * v) * (Px - Qx) := by rw [huv]
        _ = (u * u * Px + v * v * Qx) - (u * u * Qx + v * v * Px) := by ring

lemma isClosed_sper :
    IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool |
      b 0 = true ∧ b 1 = true ∧ b (-1) = false ∧
      (∀ p q, b p = true → b q = true → b (p + q) = true) ∧
      (∀ p q, b p = true → b q = true → b (p * q) = true) ∧
      (∀ p, b p = true ∨ b (-p) = true) ∧
      (∀ p q, b (p * q) = true → b (-(p * q)) = true →
        (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true))} := by
  have hcoord : ∀ (p : MvPolynomial (Fin 2) ℝ) (v : Bool),
      IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool | b p = v} := fun p v =>
    isClosed_eq (continuous_apply p) continuous_const
  have h1 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool | b 0 = true} := hcoord 0 true
  have h2 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool | b 1 = true} := hcoord 1 true
  have h3 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool | b (-1) = false} := hcoord (-1) false
  have h4 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool |
      ∀ p q, b p = true → b q = true → b (p + q) = true} := by
    have : {b : MvPolynomial (Fin 2) ℝ → Bool |
        ∀ p q, b p = true → b q = true → b (p + q) = true} =
        ⋂ p, ⋂ q, ({b | b p = false} ∪ {b | b q = false} ∪ {b | b (p + q) = true}) := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h p q
        cases hp : b p <;> cases hq : b q
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (h p q hp hq)
      · intro h p q hp hq
        rcases h p q with (h1 | h2) | h3
        · rw [hp] at h1; cases h1
        · rw [hq] at h2; cases h2
        · exact h3
    rw [this]
    exact isClosed_iInter fun p => isClosed_iInter fun q =>
      ((hcoord p false).union (hcoord q false)).union (hcoord (p + q) true)
  have h5 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool |
      ∀ p q, b p = true → b q = true → b (p * q) = true} := by
    have : {b : MvPolynomial (Fin 2) ℝ → Bool |
        ∀ p q, b p = true → b q = true → b (p * q) = true} =
        ⋂ p, ⋂ q, ({b | b p = false} ∪ {b | b q = false} ∪ {b | b (p * q) = true}) := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h p q
        cases hp : b p <;> cases hq : b q
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (h p q hp hq)
      · intro h p q hp hq
        rcases h p q with (h1 | h2) | h3
        · rw [hp] at h1; cases h1
        · rw [hq] at h2; cases h2
        · exact h3
    rw [this]
    exact isClosed_iInter fun p => isClosed_iInter fun q =>
      ((hcoord p false).union (hcoord q false)).union (hcoord (p * q) true)
  have h6 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool |
      ∀ p, b p = true ∨ b (-p) = true} := by
    have : {b : MvPolynomial (Fin 2) ℝ → Bool | ∀ p, b p = true ∨ b (-p) = true} =
        ⋂ p, ({b | b p = true} ∪ {b | b (-p) = true}) := by
      ext b; simp
    rw [this]
    exact isClosed_iInter fun p => (hcoord p true).union (hcoord (-p) true)
  have h7 : IsClosed {b : MvPolynomial (Fin 2) ℝ → Bool |
      ∀ p q, b (p * q) = true → b (-(p * q)) = true →
        (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true)} := by
    have : {b : MvPolynomial (Fin 2) ℝ → Bool |
        ∀ p q, b (p * q) = true → b (-(p * q)) = true →
          (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true)} =
        ⋂ p, ⋂ q, ({b | b (p * q) = false} ∪ {b | b (-(p * q)) = false} ∪
          ({b | b p = true} ∩ {b | b (-p) = true}) ∪
          ({b | b q = true} ∩ {b | b (-q) = true})) := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_inter_iff]
      constructor
      · intro h p q
        cases h1 : b (p * q) <;> cases h2 : b (-(p * q))
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inl (Or.inr rfl))
        · rcases h p q h1 h2 with hp | hq
          · exact Or.inl (Or.inr hp)
          · exact Or.inr hq
      · intro h p q h1 h2
        rcases h p q with ((ha | hb) | hp) | hq
        · rw [h1] at ha; cases ha
        · rw [h2] at hb; cases hb
        · exact Or.inl hp
        · exact Or.inr hq
    rw [this]
    exact isClosed_iInter fun p => isClosed_iInter fun q =>
      (((hcoord (p * q) false).union (hcoord (-(p * q)) false)).union
        ((hcoord p true).inter (hcoord (-p) true))).union
        ((hcoord q true).inter (hcoord (-q) true))
  have hcomb : {b : MvPolynomial (Fin 2) ℝ → Bool |
      b 0 = true ∧ b 1 = true ∧ b (-1) = false ∧
      (∀ p q, b p = true → b q = true → b (p + q) = true) ∧
      (∀ p q, b p = true → b q = true → b (p * q) = true) ∧
      (∀ p, b p = true ∨ b (-p) = true) ∧
      (∀ p q, b (p * q) = true → b (-(p * q)) = true →
        (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true))} =
      {b | b 0 = true} ∩ {b | b 1 = true} ∩ {b | b (-1) = false} ∩
      {b | ∀ p q, b p = true → b q = true → b (p + q) = true} ∩
      {b | ∀ p q, b p = true → b q = true → b (p * q) = true} ∩
      {b | ∀ p, b p = true ∨ b (-p) = true} ∩
      {b | ∀ p q, b (p * q) = true → b (-(p * q)) = true →
        (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true)} := by
    ext b; simp [and_assoc]
  rw [hcomb]
  exact (((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7

theorem main : H1 → H2 → H3 → type_of% @PierceBirkhoff.pierce_birkhoff_conjecture_dim_two := by
  intro h1 h2 h3 f hf
  classical
  obtain ⟨ι, P, g, hfin, hcl, hsa, hcov, heq⟩ := hf
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Rewrite each closed semialgebraic piece P i as a finite union of basic closed sets via H2.
  choose F hF using fun i => h2 (P i) (hcl i) (hsa i)
  -- Work in the compact space (MvPolynomial (Fin 2) ℝ → Bool).
  let Sper : Set (MvPolynomial (Fin 2) ℝ → Bool) :=
    {b | b 0 = true ∧ b 1 = true ∧ b (-1) = false ∧
      (∀ p q, b p = true → b q = true → b (p + q) = true) ∧
      (∀ p q, b p = true → b q = true → b (p * q) = true) ∧
      (∀ p, b p = true ∨ b (-p) = true) ∧
      (∀ p q, b (p * q) = true → b (-(p * q)) = true →
        (b p = true ∧ b (-p) = true) ∨ (b q = true ∧ b (-q) = true))}
  let toSet : (MvPolynomial (Fin 2) ℝ → Bool) → Set (MvPolynomial (Fin 2) ℝ) :=
    fun b => {p | b p = true}
  let pt : (Fin 2 → ℝ) → (MvPolynomial (Fin 2) ℝ → Bool) :=
    fun x p => decide (0 ≤ MvPolynomial.eval x p)
  have hpt_sper : ∀ x : Fin 2 → ℝ, pt x ∈ Sper := by
    intro x
    refine ⟨by simp [pt], by simp [pt], by simp [pt], ?_, ?_, ?_, ?_⟩
    · intro p q hp hq
      simp only [pt, decide_eq_true_eq, map_add] at hp hq ⊢
      linarith
    · intro p q hp hq
      simp only [pt, decide_eq_true_eq, map_mul] at hp hq ⊢
      exact mul_nonneg hp hq
    · intro p
      simp only [pt, decide_eq_true_eq, map_neg, Left.nonneg_neg_iff]
      exact le_total 0 (MvPolynomial.eval x p)
    · intro p q h1' h2'
      simp only [pt, decide_eq_true_eq, map_mul, map_neg, Left.nonneg_neg_iff] at h1' h2' ⊢
      have hmul0 : MvPolynomial.eval x p * MvPolynomial.eval x q = 0 := le_antisymm h2' h1'
      rcases mul_eq_zero.mp hmul0 with hp | hq
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
  have hcone_iff : ∀ (b : MvPolynomial (Fin 2) ℝ → Bool),
      b ∈ Sper ↔
        (0 ∈ toSet b ∧ 1 ∈ toSet b ∧ (-1 : MvPolynomial (Fin 2) ℝ) ∉ toSet b ∧
          (∀ p q, p ∈ toSet b → q ∈ toSet b → p + q ∈ toSet b) ∧
          (∀ p q, p ∈ toSet b → q ∈ toSet b → p * q ∈ toSet b) ∧
          (∀ p, p ∈ toSet b ∨ -p ∈ toSet b) ∧
          (∀ p q, p * q ∈ toSet b → -(p * q) ∈ toSet b →
            (p ∈ toSet b ∧ -p ∈ toSet b) ∨ (q ∈ toSet b ∧ -q ∈ toSet b))) := by
    intro b
    simp [Sper, toSet]
  let Ptilde : ι → Set (MvPolynomial (Fin 2) ℝ → Bool) :=
    fun i => Sper ∩ ⋃ s ∈ F i, {b | ∀ p ∈ s, b p = true}
  have hPtilde_compact : ∀ i, IsCompact (Ptilde i) := by
    intro i
    apply IsClosed.isCompact
    apply isClosed_sper.inter
    refine (F i).finite_toSet.isClosed_biUnion fun s _ => ?_
    have : {b : MvPolynomial (Fin 2) ℝ → Bool | ∀ p ∈ s, b p = true} =
        ⋂ p ∈ s, {b | b p = true} := by ext b; simp
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_eq (continuous_apply p) continuous_const
  have hpt_mem : ∀ i (x : Fin 2 → ℝ), pt x ∈ Ptilde i ↔ x ∈ P i := by
    intro i x
    rw [hF i]
    simp [Ptilde, hpt_sper x, pt]
  -- Lift covering property from ℝ² to Sper via H1.
  have hcov_sper : ∀ α : Set (MvPolynomial (Fin 2) ℝ),
      (0 ∈ α ∧ 1 ∈ α ∧ (-1 : MvPolynomial (Fin 2) ℝ) ∉ α ∧
        (∀ p q, p ∈ α → q ∈ α → p + q ∈ α) ∧
        (∀ p q, p ∈ α → q ∈ α → p * q ∈ α) ∧
        (∀ p, p ∈ α ∨ -p ∈ α) ∧
        (∀ p q, p * q ∈ α → -(p * q) ∈ α → (p ∈ α ∧ -p ∈ α) ∨ (q ∈ α ∧ -q ∈ α))) →
      ∃ i, ∃ s ∈ F i, ∀ p ∈ s, p ∈ α := by
    intro α hα
    by_contra hno
    push Not at hno
    have hbad : ∀ (i : ι) (s : Finset (MvPolynomial (Fin 2) ℝ)),
        s ∈ F i → ∃ p ∈ s, p ∉ α := fun i s hs => hno i s hs
    choose bad hbad_mem hbad_nmem using hbad
    let p₁ : Finset (MvPolynomial (Fin 2) ℝ) :=
      Finset.univ.biUnion fun i => (F i).attach.image fun s => -(bad i s.1 s.2)
    have hp₁ : ∀ q ∈ p₁, -q ∉ α := by
      intro q hq
      simp only [p₁, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, Subtype.exists] at hq
      rcases hq with ⟨i, s, hs, rfl⟩
      simpa using hbad_nmem i s hs
    obtain ⟨x, _, hx1⟩ := h1 α hα ∅ p₁ (by simp) hp₁
    have hx_cov : x ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_cov
    rw [hF i] at hxi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hxi
    obtain ⟨s, hs, hxs⟩ := hxi
    have hmem : -(bad i s hs) ∈ p₁ := by
      simp only [p₁, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, Subtype.exists]
      exact ⟨i, s, hs, rfl⟩
    have hpos := hx1 _ hmem
    have hge := hxs _ (hbad_mem i s hs)
    simp only [map_neg, Left.neg_pos_iff] at hpos
    linarith
  -- Lift overlap agreement from ℝ² to Sper via H1.
  have hoverlap_sper : ∀ (i j : ι) (α : Set (MvPolynomial (Fin 2) ℝ)),
      (0 ∈ α ∧ 1 ∈ α ∧ (-1 : MvPolynomial (Fin 2) ℝ) ∉ α ∧
        (∀ p q, p ∈ α → q ∈ α → p + q ∈ α) ∧
        (∀ p q, p ∈ α → q ∈ α → p * q ∈ α) ∧
        (∀ p, p ∈ α ∨ -p ∈ α) ∧
        (∀ p q, p * q ∈ α → -(p * q) ∈ α → (p ∈ α ∧ -p ∈ α) ∨ (q ∈ α ∧ -q ∈ α))) →
      (∃ s ∈ F i, ∀ p ∈ s, p ∈ α) →
      (∃ s ∈ F j, ∀ p ∈ s, p ∈ α) →
      g i - g j ∈ α ∧ -(g i - g j) ∈ α := by
    intro i j α hα ⟨si, hsi, hαi⟩ ⟨sj, hsj, hαj⟩
    by_contra hno
    let S := si ∪ sj
    let p₀ : Finset (MvPolynomial (Fin 2) ℝ) := S.filter fun p => -p ∈ α
    let p₁_base : Finset (MvPolynomial (Fin 2) ℝ) := S.filter fun p => -p ∉ α
    have hsplit : ∃ d : MvPolynomial (Fin 2) ℝ,
        (d = g i - g j ∨ d = -(g i - g j)) ∧ -d ∉ α := by
      by_cases hA : g i - g j ∈ α
      · refine ⟨g i - g j, Or.inl rfl, ?_⟩
        intro hB; exact hno ⟨hA, hB⟩
      · refine ⟨-(g i - g j), Or.inr rfl, ?_⟩
        simpa using hA
    obtain ⟨d, hd_eq, hd_pos⟩ := hsplit
    let p₁ : Finset (MvPolynomial (Fin 2) ℝ) := insert d p₁_base
    have hp₀ : ∀ p ∈ p₀, p ∈ α ∧ -p ∈ α := by
      intro p hp
      simp only [p₀, Finset.mem_filter, S, Finset.mem_union] at hp
      refine ⟨?_, hp.2⟩
      rcases hp.1 with hpi | hpj
      · exact hαi p hpi
      · exact hαj p hpj
    have hp₁ : ∀ p ∈ p₁, -p ∉ α := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hd_pos
      · exact (Finset.mem_filter.mp hp').2
    obtain ⟨x, hx0, hx1⟩ := h1 α hα p₀ p₁ hp₀ hp₁
    have hx_nonneg : ∀ p ∈ S, 0 ≤ MvPolynomial.eval x p := by
      intro p hp
      by_cases hnp : -p ∈ α
      · have := hx0 p (Finset.mem_filter.mpr ⟨hp, hnp⟩)
        linarith
      · have := hx1 p (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, hnp⟩))
        linarith
    have hxi : x ∈ P i := by
      rw [hF i]
      exact Set.mem_iUnion₂.mpr ⟨si, hsi, fun p hp => hx_nonneg p (Finset.mem_union_left _ hp)⟩
    have hxj : x ∈ P j := by
      rw [hF j]
      exact Set.mem_iUnion₂.mpr ⟨sj, hsj, fun p hp => hx_nonneg p (Finset.mem_union_right _ hp)⟩
    have hgi_eq_gj : MvPolynomial.eval x (g i) = MvPolynomial.eval x (g j) := by
      rw [← heq i x hxi, ← heq j x hxj]
    have hd_gt : 0 < MvPolynomial.eval x d := hx1 d (Finset.mem_insert_self _ _)
    rcases hd_eq with rfl | rfl
    · simp only [map_sub] at hd_gt; linarith
    · simp only [map_neg, map_sub] at hd_gt; linarith
  -- Pointwise separation via H3 + Madden's algebraic lemma.
  have hsep : ∀ (i j : ι) (α β : MvPolynomial (Fin 2) ℝ → Bool),
      α ∈ Ptilde i → β ∈ Ptilde j →
      ∃ h : MvPolynomial (Fin 2) ℝ, α (h - g i) = true ∧ β (g j - h) = true := by
    intro i j α β hα hβ
    have hα_cone := (hcone_iff α).mp hα.1
    have hβ_cone := (hcone_iff β).mp hβ.1
    have hα_mem : ∃ s ∈ F i, ∀ p ∈ s, p ∈ toSet α := by
      simpa [Ptilde, toSet] using hα.2
    have hβ_mem : ∃ s ∈ F j, ∀ p ∈ s, p ∈ toSet β := by
      simpa [Ptilde, toSet] using hβ.2
    have hid := h3 ι F g hcov_sper hoverlap_sper i j (toSet α) (toSet β)
      hα_cone hβ_cone hα_mem hβ_mem
    obtain ⟨P0, Q0, hP0, hQ0, hsub⟩ := separating_ideal_decomp
      hα_cone.1 hα_cone.2.2.2.1 hα_cone.2.2.2.2.1 hα_cone.2.2.2.2.2.1
      hβ_cone.1 hβ_cone.2.2.2.1 hβ_cone.2.2.2.2.1 hβ_cone.2.2.2.2.2.1 hid
    refine ⟨g i + Q0, ?_, ?_⟩
    · have : g i + Q0 - g i = Q0 := by ring
      rw [this]; exact hQ0.1
    · have : g j - (g i + Q0) = -P0 := by
        have h1' : g i - g j = P0 - Q0 := hsub
        linear_combination -h1'
      rw [this]; exact hP0.2
  -- First compactness: fix i and α ∈ Ptilde i; cover every Ptilde j by finitely many h.
  have hcover_j : ∀ (i : ι) (α : MvPolynomial (Fin 2) ℝ → Bool), α ∈ Ptilde i →
      ∃ S : Finset (MvPolynomial (Fin 2) ℝ),
        S.Nonempty ∧
        (∀ h ∈ S, α (h - g i) = true) ∧
        (∀ j : ι, ∀ β ∈ Ptilde j, ∃ h ∈ S, β (g j - h) = true) := by
    intro i α hα
    have hone_j : ∀ j : ι, ∃ Sj : Finset (MvPolynomial (Fin 2) ℝ),
        (∀ h ∈ Sj, α (h - g i) = true) ∧
        (∀ β ∈ Ptilde j, ∃ h ∈ Sj, β (g j - h) = true) := by
      intro j
      let U : {h : MvPolynomial (Fin 2) ℝ // α (h - g i) = true} →
          Set (MvPolynomial (Fin 2) ℝ → Bool) :=
        fun h => {β | β (g j - h.1) = true}
      have hU_open : ∀ h, IsOpen (U h) := by
        intro h
        have hEq : U h = (fun β : MvPolynomial (Fin 2) ℝ → Bool => β (g j - h.1)) ⁻¹' {true} := by
          ext β; simp [U]
        rw [hEq]
        exact (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply (g j - h.1))
      have hU_cov : Ptilde j ⊆ ⋃ h, U h := by
        intro β hβ
        obtain ⟨h, hhα, hhβ⟩ := hsep i j α β hα hβ
        exact Set.mem_iUnion.mpr ⟨⟨h, hhα⟩, hhβ⟩
      obtain ⟨T, hT⟩ := (hPtilde_compact j).elim_finite_subcover U hU_open hU_cov
      refine ⟨T.image Subtype.val, ?_, ?_⟩
      · intro h hh
        obtain ⟨⟨h', hh'⟩, _, rfl⟩ := Finset.mem_image.mp hh
        exact hh'
      · intro β hβ
        have hmem := hT hβ
        simp only [Set.mem_iUnion, U, Set.mem_setOf_eq] at hmem
        rcases hmem with ⟨h, hmemT, hhβ⟩
        exact ⟨h.1, Finset.mem_image.mpr ⟨h, hmemT, rfl⟩, hhβ⟩
    choose Sj hSj_α hSj_β using hone_j
    refine ⟨insert (g i) (Finset.univ.biUnion Sj), Finset.insert_nonempty _ _, ?_, ?_⟩
    · intro h hh
      rcases Finset.mem_insert.mp hh with rfl | hh'
      · rw [sub_self]; exact hα.1.1
      · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hh'
        exact hSj_α j h hj
    · intro j β hβ
      obtain ⟨h, hh, hhβ⟩ := hSj_β j β hβ
      exact ⟨h, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hh⟩), hhβ⟩
  -- Second compactness: cover each Ptilde i by finitely many S.
  have hcover_i : ∀ i : ι, ∃ Li : Finset (Finset (MvPolynomial (Fin 2) ℝ)),
      (∀ S ∈ Li, S.Nonempty) ∧
      (∀ α ∈ Ptilde i, ∃ S ∈ Li, ∀ h ∈ S, α (h - g i) = true) ∧
      (∀ S ∈ Li, ∀ j : ι, ∀ β ∈ Ptilde j, ∃ h ∈ S, β (g j - h) = true) := by
    intro i
    let Good : Set (Finset (MvPolynomial (Fin 2) ℝ)) :=
      {S | S.Nonempty ∧ ∀ j : ι, ∀ β ∈ Ptilde j, ∃ h ∈ S, β (g j - h) = true}
    let V : {S // S ∈ Good} → Set (MvPolynomial (Fin 2) ℝ → Bool) :=
      fun S => {α | ∀ h ∈ S.1, α (h - g i) = true}
    have hV_open : ∀ S, IsOpen (V S) := by
      intro S
      have : V S = ⋂ h ∈ S.1, {α | α (h - g i) = true} := by ext α; simp [V]
      rw [this]
      refine S.1.finite_toSet.isOpen_biInter fun h _ => ?_
      have hEq : {α : MvPolynomial (Fin 2) ℝ → Bool | α (h - g i) = true} =
          (fun α : MvPolynomial (Fin 2) ℝ → Bool => α (h - g i)) ⁻¹' {true} := by
        ext α; simp
      rw [hEq]
      exact (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply (h - g i))
    have hV_cov : Ptilde i ⊆ ⋃ S, V S := by
      intro α hα
      obtain ⟨S, hSne, hSα, hSβ⟩ := hcover_j i α hα
      exact Set.mem_iUnion.mpr ⟨⟨S, hSne, hSβ⟩, hSα⟩
    obtain ⟨T, hT⟩ := (hPtilde_compact i).elim_finite_subcover V hV_open hV_cov
    refine ⟨T.image Subtype.val, ?_, ?_, ?_⟩
    · intro S hS
      obtain ⟨⟨S', hS'⟩, _, rfl⟩ := Finset.mem_image.mp hS
      exact hS'.1
    · intro α hα
      have hmem := hT hα
      simp only [Set.mem_iUnion, V, Set.mem_setOf_eq] at hmem
      rcases hmem with ⟨S, hST, hSα⟩
      exact ⟨S.1, Finset.mem_image.mpr ⟨S, hST, rfl⟩, hSα⟩
    · intro S hS j β hβ
      obtain ⟨⟨S', hS'⟩, _, rfl⟩ := Finset.mem_image.mp hS
      exact hS'.2 j β hβ
  choose Li hLi_ne hLi_α hLi_β using hcover_i
  let L : Finset (Finset (MvPolynomial (Fin 2) ℝ)) := Finset.univ.biUnion Li
  have hL_ne_el : ∀ S ∈ L, S.Nonempty := by
    intro S hS
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hS
    exact hLi_ne i S hi
  have hL_nonempty : L.Nonempty := by
    have h0 : (0 : Fin 2 → ℝ) ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h0
    have hpt0 : pt 0 ∈ Ptilde i := (hpt_mem i 0).mpr hi
    obtain ⟨S, hS, _⟩ := hLi_α i (pt 0) hpt0
    exact ⟨S, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hS⟩⟩
  let M : Finset (MvPolynomial (Fin 2) ℝ) := L.biUnion id
  have hM_nonempty : M.Nonempty := by
    obtain ⟨S, hS⟩ := hL_nonempty
    obtain ⟨h, hh⟩ := hL_ne_el S hS
    exact ⟨h, Finset.mem_biUnion.mpr ⟨S, hS, hh⟩⟩
  -- Build the finite sup-inf matrix G : {S // S ∈ L} → {p // p ∈ M} → MvPolynomial (Fin 2) ℝ.
  let G : {S // S ∈ L} → {p // p ∈ M} → MvPolynomial (Fin 2) ℝ :=
    fun S p => if p.1 ∈ S.1 then p.1 else (hL_ne_el S.1 S.2).choose
  have hG_mem : ∀ (S : {S // S ∈ L}) (p : {p // p ∈ M}), G S p ∈ S.1 := by
    intro S p
    simp only [G]
    split_ifs with hp
    · exact hp
    · exact (hL_ne_el S.1 S.2).choose_spec
  have hG_surj : ∀ (S : {S // S ∈ L}) (h : MvPolynomial (Fin 2) ℝ),
      h ∈ S.1 → ∃ p : {p // p ∈ M}, G S p = h := by
    intro S h hh
    refine ⟨⟨h, Finset.mem_biUnion.mpr ⟨S.1, S.2, hh⟩⟩, ?_⟩
    simp [G, hh]
  haveI : Nonempty {S // S ∈ L} := hL_nonempty.to_subtype
  haveI : Nonempty {p // p ∈ M} := hM_nonempty.to_subtype
  refine ⟨{S // S ∈ L}, {p // p ∈ M}, G, inferInstance, inferInstance, fun x => ?_⟩
  symm
  apply supinf_eq
  · intro S
    have hx_cov : x ∈ ⋃ j, P j := by rw [hcov]; trivial
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx_cov
    have hptj : pt x ∈ Ptilde j := (hpt_mem j x).mpr hxj
    obtain ⟨i0, _, hi0⟩ := Finset.mem_biUnion.mp S.2
    obtain ⟨h, hhS, hhβ⟩ := hLi_β i0 S.1 hi0 j (pt x) hptj
    obtain ⟨p, hp⟩ := hG_surj S h hhS
    refine ⟨p, ?_⟩
    rw [hp, heq j x hxj]
    simp only [pt, decide_eq_true_eq, map_sub, sub_nonneg] at hhβ
    exact hhβ
  · have hx_cov : x ∈ ⋃ i, P i := by rw [hcov]; trivial
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_cov
    have hpti : pt x ∈ Ptilde i := (hpt_mem i x).mpr hxi
    obtain ⟨S, hSLi, hSα⟩ := hLi_α i (pt x) hpti
    refine ⟨⟨S, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hSLi⟩⟩, fun p => ?_⟩
    rw [heq i x hxi]
    have hmem := hG_mem ⟨S, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hSLi⟩⟩ p
    have hle := hSα _ hmem
    simp only [pt, decide_eq_true_eq, map_sub, sub_nonneg] at hle
    exact hle

end OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R2
