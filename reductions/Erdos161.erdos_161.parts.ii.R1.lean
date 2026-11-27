import FormalConjectures.ErdosProblems.«161»
import Mathlib

/-!
# Reduction of Erdős Problem 161 — ii

For fixed uniformity `t ≥ 3` and densities `α, β ∈ (0, 1/2)`, Erdős Problem 161 (ii) asks
whether `Hypergraph.balancedColoringThreshold n t α =Θ[atTop] Hypergraph.balancedColoringThreshold n t β`.

In this reduction we prove unconditionally the probabilistic-method upper bound
`Hypergraph.balancedColoringThreshold n t α = O((log n)^(1/(t-1)))` for all `t ≥ 3` and
`α ∈ (0, 1/2)`, via averaging from exact-size subsets and a finite Chernoff/Hoeffding
exponential-moment counting argument over all `2^(n.choose t)` colorings.

This reduces the target to the matching almost-monochromatic lower bounds:
- `H1`: the `t = 3` case (`Ω(√(log n))`), a known theorem of Conlon, Fox, and Sudakov (2011).
- `H2`: the `t ≥ 4` case (`Ω((log n)^(1/(t-1)))`), the exact open core of Erdős Problem 161 (ii).
-/

-- Credit: @preternatural-tocsin

namespace OMA.R_Erdos161_erdos_161_parts_ii_R1

open Filter Asymptotics Finset

/-- Conlon--Fox--Sudakov (2011), Theorem 1 (2-color case): every 2-coloring of the
3-subsets of an n-element set contains a subset of size Ω(√(log n)) in which some
color has density less than α. -/
def H1 : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ col : Finset (Fin n) → Bool,
        ∃ X : Finset (Fin n), c * Real.sqrt (Real.log n) ≤ (X.card : ℝ) ∧
          ∃ b : Bool,
            (((X.powersetCard 3).filter (fun e ↦ col e = b)).card : ℝ) <
              α * (X.card.choose 3 : ℝ)

/-- Higher-uniformity almost-monochromatic subsets (t ≥ 4): every 2-coloring of the
t-subsets of an n-element set contains a subset of size Ω((log n)^(1/(t-1))) in which
some color has density less than α. -/
def H2 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ col : Finset (Fin n) → Bool,
        ∃ X : Finset (Fin n),
          c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (X.card : ℝ) ∧
          ∃ b : Bool,
            (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
              α * (X.card.choose t : ℝ)

/- ### Part 1: Averaging from subsets of exact size `m` to subsets of size `≥ m` -/

lemma card_superset_powersetCard {n t m : ℕ} {Y e : Finset (Fin n)}
    (heY : e ⊆ Y) (het : e.card = t) (htm : t ≤ m) :
    ((Y.powersetCard m).filter (fun X ↦ e ⊆ X)).card = (Y.card - t).choose (m - t) := by
  have hbij : ((Y.powersetCard m).filter (fun X ↦ e ⊆ X)).card =
      ((Y \ e).powersetCard (m - t)).card := by
    symm
    refine Finset.card_bij (fun A _ ↦ e ∪ A) ?_ ?_ ?_
    · intro A hA
      rw [mem_powersetCard] at hA
      rw [mem_filter, mem_powersetCard]
      have hdisj : Disjoint e A := disjoint_sdiff.mono_right hA.1
      refine ⟨⟨union_subset heY (hA.1.trans sdiff_subset), ?_⟩, subset_union_left⟩
      rw [card_union_of_disjoint hdisj, het, hA.2]
      omega
    · intro A₁ hA₁ A₂ hA₂ hEq
      rw [mem_powersetCard] at hA₁ hA₂
      have hd₁ : Disjoint e A₁ := disjoint_sdiff.mono_right hA₁.1
      have hd₂ : Disjoint e A₂ := disjoint_sdiff.mono_right hA₂.1
      have h1 : (e ∪ A₁) \ e = A₁ := union_sdiff_cancel_left hd₁
      have h2 : (e ∪ A₂) \ e = A₂ := union_sdiff_cancel_left hd₂
      rw [← h1, ← h2, hEq]
    · intro X hX
      rw [mem_filter, mem_powersetCard] at hX
      refine ⟨X \ e, ?_, union_sdiff_of_subset hX.2⟩
      rw [mem_powersetCard]
      refine ⟨sdiff_subset_sdiff hX.1.1 Subset.rfl, ?_⟩
      rw [card_sdiff_of_subset hX.2, hX.1.2, het]
  rw [hbij, card_powersetCard, card_sdiff_of_subset heY, het]

lemma averaging_powersetCard {n t m : ℕ} {Y : Finset (Fin n)}
    {P : Finset (Fin n) → Prop} [DecidablePred P] {α : ℝ}
    (htm : t ≤ m) (hmY : m ≤ Y.card)
    (hX : ∀ X ∈ Y.powersetCard m,
      α * (m.choose t : ℝ) ≤ (((X.powersetCard t).filter P).card : ℝ)) :
    α * (Y.card.choose t : ℝ) ≤ (((Y.powersetCard t).filter P).card : ℝ) := by
  have hsum_ge :
      (Y.card.choose m : ℝ) * (α * (m.choose t : ℝ)) ≤
        ∑ X ∈ Y.powersetCard m, (((X.powersetCard t).filter P).card : ℝ) := by
    have h1 : ∑ X ∈ Y.powersetCard m, (α * (m.choose t : ℝ)) ≤
        ∑ X ∈ Y.powersetCard m, (((X.powersetCard t).filter P).card : ℝ) :=
      Finset.sum_le_sum hX
    simpa [Finset.sum_const, card_powersetCard, nsmul_eq_mul] using h1
  have hdouble :
      ∑ X ∈ Y.powersetCard m, ((X.powersetCard t).filter P).card =
        ((Y.card - t).choose (m - t)) * ((Y.powersetCard t).filter P).card := by
    have hstep1 :
        ∑ X ∈ Y.powersetCard m, ((X.powersetCard t).filter P).card =
          ∑ X ∈ Y.powersetCard m,
            ∑ e ∈ (Y.powersetCard t).filter P, if e ⊆ X then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro X hX'
      rw [mem_powersetCard] at hX'
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext e
      simp only [mem_filter, mem_powersetCard]
      exact ⟨fun ⟨⟨heX, het⟩, hPe⟩ ↦ ⟨⟨⟨heX.trans hX'.1, het⟩, hPe⟩, heX⟩,
             fun ⟨⟨⟨_, het⟩, hPe⟩, heX⟩ ↦ ⟨⟨heX, het⟩, hPe⟩⟩
    rw [hstep1, Finset.sum_comm]
    have hstep2 :
        ∑ e ∈ (Y.powersetCard t).filter P,
            ∑ X ∈ Y.powersetCard m, (if e ⊆ X then 1 else 0) =
          ∑ e ∈ (Y.powersetCard t).filter P, (Y.card - t).choose (m - t) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [mem_filter, mem_powersetCard] at he
      rw [Finset.sum_boole, Nat.cast_id]
      exact card_superset_powersetCard he.1.1 he.1.2 htm
    rw [hstep2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hdoubleR :
      ∑ X ∈ Y.powersetCard m, (((X.powersetCard t).filter P).card : ℝ) =
        (((Y.card - t).choose (m - t) : ℕ) : ℝ) * (((Y.powersetCard t).filter P).card : ℝ) := by
    exact_mod_cast hdouble
  have hchoose : Y.card.choose m * m.choose t = Y.card.choose t * (Y.card - t).choose (m - t) :=
    Nat.choose_mul (n := Y.card) htm
  have hchooseR :
      (Y.card.choose m : ℝ) * (m.choose t : ℝ) =
        (Y.card.choose t : ℝ) * ((Y.card - t).choose (m - t) : ℝ) := by
    exact_mod_cast hchoose
  have hpos : (0 : ℝ) < ((Y.card - t).choose (m - t) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m - t ≤ Y.card - t)
  have hineq :
      ((Y.card - t).choose (m - t) : ℝ) * (α * (Y.card.choose t : ℝ)) ≤
        ((Y.card - t).choose (m - t) : ℝ) * (((Y.powersetCard t).filter P).card : ℝ) := by
    calc
      ((Y.card - t).choose (m - t) : ℝ) * (α * (Y.card.choose t : ℝ))
          = α * ((Y.card.choose t : ℝ) * ((Y.card - t).choose (m - t) : ℝ)) := by ring
      _ = α * ((Y.card.choose m : ℝ) * (m.choose t : ℝ)) := by rw [hchooseR]
      _ = (Y.card.choose m : ℝ) * (α * (m.choose t : ℝ)) := by ring
      _ ≤ ∑ X ∈ Y.powersetCard m, (((X.powersetCard t).filter P).card : ℝ) := hsum_ge
      _ = ((Y.card - t).choose (m - t) : ℝ) * (((Y.powersetCard t).filter P).card : ℝ) := hdoubleR
  exact le_of_mul_le_mul_left hineq hpos

/- ### Part 2: Elementary Hoeffding / Chernoff exponential bound -/

lemma exp_add_exp_neg_div_two_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    (Real.exp u + Real.exp (-u)) / 2 ≤ Real.exp (2 * u ^ 2) := by
  have h1mu_pos : 0 < 1 - u := by linarith
  have h1pu_pos : 0 < 1 + u := by linarith
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hexp_neg_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hle1 : Real.exp u ≤ (1 - u)⁻¹ := by
    have h := Real.add_one_le_exp (-u)
    have h' : 1 - u ≤ (Real.exp u)⁻¹ := by
      rw [← Real.exp_neg]
      linarith
    exact (le_inv_comm₀ hexp_pos h1mu_pos).mpr h'
  have hle2 : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    have h := Real.add_one_le_exp u
    have h' : 1 + u ≤ Real.exp u := by linarith
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hexp_pos h1pu_pos).mpr h'
  have hsum : ((1 - u)⁻¹ + (1 + u)⁻¹) / 2 = (1 - u ^ 2)⁻¹ := by
    have h1 : 1 - u ≠ 0 := ne_of_gt h1mu_pos
    have h2 : 1 + u ≠ 0 := ne_of_gt h1pu_pos
    have h3 : 1 - u ^ 2 ≠ 0 := by nlinarith
    field_simp [h1, h2, h3]
    ring
  have h1mu2_pos : 0 < 1 - u ^ 2 := by nlinarith
  have hfrac : (1 - u ^ 2)⁻¹ ≤ 1 + 2 * u ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1mu2_pos]
    have hquart : 0 ≤ u ^ 2 * (1 - 2 * u ^ 2) :=
      mul_nonneg (sq_nonneg u) (by nlinarith)
    linarith
  calc
    (Real.exp u + Real.exp (-u)) / 2 ≤ ((1 - u)⁻¹ + (1 + u)⁻¹) / 2 := by linarith
    _ = (1 - u ^ 2)⁻¹ := hsum
    _ ≤ 1 + 2 * u ^ 2 := hfrac
    _ ≤ Real.exp (2 * u ^ 2) := by linarith [Real.add_one_le_exp (2 * u ^ 2)]

lemma mgf_factor_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    Real.exp (((1 / 2 - α) / 2) * α) * ((1 + Real.exp (-((1 / 2 - α) / 2))) / 2) ≤
      Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2) := by
  set δ : ℝ := 1 / 2 - α
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 / 2 := by dsimp [δ]; linarith
  set u : ℝ := δ / 4
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 / 2 := by dsimp [u]; linarith
  have hrew : (1 + Real.exp (-(δ / 2))) / 2 = Real.exp (-u) * ((Real.exp u + Real.exp (-u)) / 2) := by
    have h1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-u) * Real.exp (-u) = Real.exp (-(δ / 2)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [u]
      ring
    linarith [mul_add (Real.exp (-u)) (Real.exp u) (Real.exp (-u))]
  have hbound := exp_add_exp_neg_div_two_le hu0 hu1
  have hpos : 0 ≤ Real.exp ((δ / 2) * α) * Real.exp (-u) := by positivity
  calc
    Real.exp ((δ / 2) * α) * ((1 + Real.exp (-(δ / 2))) / 2)
        = (Real.exp ((δ / 2) * α) * Real.exp (-u)) * ((Real.exp u + Real.exp (-u)) / 2) := by
          rw [hrew]; ring
    _ ≤ (Real.exp ((δ / 2) * α) * Real.exp (-u)) * Real.exp (2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hbound hpos
    _ = Real.exp ((δ / 2) * α + (-u) + 2 * u ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(1 / 4) * δ ^ 2) := by
          apply Real.exp_le_exp.mpr
          dsimp [u, δ]
          nlinarith

/- ### Part 3: Finite Chernoff counting bound over all 2-colorings -/

lemma card_bad_colorings_for_subset {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (b : Bool) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    (((Finset.univ : Finset (E → Bool)).filter
        (fun f ↦ ((S.filter (fun e ↦ f e = b)).card : ℝ) < α * (S.card : ℝ))).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card E * Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (S.card : ℝ)) := by
  set lam : ℝ := (1 / 2 - α) / 2
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hstep1 :
      (((Finset.univ : Finset (E → Bool)).filter
          (fun f ↦ ((S.filter (fun e ↦ f e = b)).card : ℝ) < α * (S.card : ℝ))).card : ℝ) ≤
        ∑ f : E → Bool,
          Real.exp (lam * (α * (S.card : ℝ) - ((S.filter (fun e ↦ f e = b)).card : ℝ))) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    have hsub :
        ∑ f ∈ (Finset.univ : Finset (E → Bool)).filter
            (fun f ↦ ((S.filter (fun e ↦ f e = b)).card : ℝ) < α * (S.card : ℝ)), (1 : ℝ) ≤
          ∑ f ∈ (Finset.univ : Finset (E → Bool)).filter
              (fun f ↦ ((S.filter (fun e ↦ f e = b)).card : ℝ) < α * (S.card : ℝ)),
            Real.exp (lam * (α * (S.card : ℝ) - ((S.filter (fun e ↦ f e = b)).card : ℝ))) := by
      refine Finset.sum_le_sum ?_
      intro f hf
      rw [mem_filter] at hf
      exact Real.one_le_exp (by nlinarith [hf.2])
    refine hsub.trans ?_
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hfactor : ∀ f : E → Bool,
      Real.exp (lam * (α * (S.card : ℝ) - ((S.filter (fun e ↦ f e = b)).card : ℝ))) =
        Real.exp (lam * α * (S.card : ℝ)) *
          ∏ e : E, (if e ∈ S then (if f e = b then Real.exp (-lam) else 1) else 1) := by
    intro f
    have hprod :
        ∏ e : E, (if e ∈ S then (if f e = b then Real.exp (-lam) else 1) else 1) =
          Real.exp (-(lam * ((S.filter (fun e ↦ f e = b)).card : ℝ))) := by
      have h1 :
          ∏ e : E, (if e ∈ S then (if f e = b then Real.exp (-lam) else 1) else 1) =
            ∏ e ∈ S, (if f e = b then Real.exp (-lam) else 1) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : E ↦ e ∈ S)]
        have hA : (Finset.univ : Finset E).filter (fun e ↦ e ∈ S) = S := by
          ext e; simp
        have hB : ∏ e ∈ (Finset.univ : Finset E).filter (fun e ↦ e ∉ S),
            (if e ∈ S then (if f e = b then Real.exp (-lam) else 1) else 1) = 1 := by
          refine Finset.prod_eq_one ?_
          intro e he
          rw [mem_filter] at he
          simp [he.2]
        rw [hA, hB, mul_one]
        refine Finset.prod_congr rfl ?_
        intro e he
        simp [he]
      rw [h1, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hprod, ← Real.exp_add]
    congr 1
    ring
  have hsum_eval :
      ∑ f : E → Bool,
          Real.exp (lam * (α * (S.card : ℝ) - ((S.filter (fun e ↦ f e = b)).card : ℝ))) =
        (2 : ℝ) ^ Fintype.card E *
          (Real.exp (lam * α) * ((1 + Real.exp (-lam)) / 2)) ^ S.card := by
    simp_rw [hfactor]
    rw [← Finset.mul_sum]
    have hps :
        (∑ f : E → Bool, ∏ e : E, (if e ∈ S then (if f e = b then Real.exp (-lam) else 1) else 1)) =
          ∏ e : E, ∑ v : Bool, (if e ∈ S then (if v = b then Real.exp (-lam) else 1) else 1) := by
      symm
      exact Fintype.prod_sum (fun e v ↦ if e ∈ S then (if v = b then Real.exp (-lam) else 1) else 1)
    rw [hps]
    have hinner : ∀ e : E,
        (∑ v : Bool, (if e ∈ S then (if v = b then Real.exp (-lam) else 1) else 1)) =
          if e ∈ S then 1 + Real.exp (-lam) else 2 := by
      intro e
      by_cases he : e ∈ S
      · simp only [he, ↓reduceIte]
        cases b <;> simp [add_comm]
      · simp only [he, ↓reduceIte]
        norm_num
    simp_rw [hinner]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hc1 : ((Finset.univ : Finset E).filter (fun e ↦ e ∈ S)).card = S.card := by
      have : (Finset.univ : Finset E).filter (fun e ↦ e ∈ S) = S := by ext e; simp
      rw [this]
    have hc2 : ((Finset.univ : Finset E).filter (fun e ↦ e ∉ S)).card =
        Fintype.card E - S.card := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    rw [hc1, hc2]
    have hSle : S.card ≤ Fintype.card E := Finset.card_le_univ S
    have hpow2 : (2 : ℝ) ^ Fintype.card E = (2 : ℝ) ^ S.card * (2 : ℝ) ^ (Fintype.card E - S.card) := by
      rw [← pow_add, Nat.add_sub_of_le hSle]
    have hexp_pow : Real.exp (lam * α * (S.card : ℝ)) = (Real.exp (lam * α)) ^ S.card := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hexp_pow, hpow2, mul_pow, div_pow]
    have h2ne : (2 : ℝ) ^ S.card ≠ 0 := by positivity
    field_simp [h2ne]
  have hmgf := mgf_factor_bound hα0 hα1
  have hnonneg : 0 ≤ Real.exp (lam * α) * ((1 + Real.exp (-lam)) / 2) := by positivity
  calc
    (((Finset.univ : Finset (E → Bool)).filter
        (fun f ↦ ((S.filter (fun e ↦ f e = b)).card : ℝ) < α * (S.card : ℝ))).card : ℝ)
        ≤ ∑ f : E → Bool,
            Real.exp (lam * (α * (S.card : ℝ) - ((S.filter (fun e ↦ f e = b)).card : ℝ))) := hstep1
    _ = (2 : ℝ) ^ Fintype.card E *
          (Real.exp (lam * α) * ((1 + Real.exp (-lam)) / 2)) ^ S.card := hsum_eval
    _ ≤ (2 : ℝ) ^ Fintype.card E *
          (Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2)) ^ S.card := by
          gcongr
    _ = (2 : ℝ) ^ Fintype.card E * Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (S.card : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 2
          ring

lemma exists_balanced_coloring_of_bound {n t m : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 2) (htm : t ≤ m) (_hmn : m ≤ n)
    (hbound : 2 * (n.choose m : ℝ) *
      Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ)) < 1) :
    ∃ c : Finset (Fin n) → Bool, ∀ Y : Finset (Fin n), m ≤ Y.card →
      ∀ b : Bool,
        let count := ((Y.powersetCard t).filter (fun e ↦ c e = b)).card
        0 < count ∧ α * (Y.card.choose t : ℝ) ≤ (count : ℝ) := by
  let E := {e : Finset (Fin n) // e.card = t}
  have hcardE : (Fintype.card (E → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card E := by
    simp [Fintype.card_bool]
  let badPair : Finset (Fin n) × Bool → Finset (E → Bool) := fun p ↦
    (Finset.univ : Finset (E → Bool)).filter (fun f ↦
      (((Finset.univ : Finset E).filter (fun e ↦ e.1 ⊆ p.1 ∧ f e = p.2)).card : ℝ) <
        α * (p.1.card.choose t : ℝ))
  let pairs : Finset (Finset (Fin n) × Bool) :=
    ((Finset.univ : Finset (Fin n)).powersetCard m) ×ˢ (Finset.univ : Finset Bool)
  let badAll : Finset (E → Bool) := pairs.biUnion badPair
  have hbad_lt : (badAll.card : ℝ) < (Fintype.card (E → Bool) : ℝ) := by
    have h1 : (badAll.card : ℝ) ≤ ∑ p ∈ pairs, ((badPair p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∀ p ∈ pairs, ((badPair p).card : ℝ) ≤
        (2 : ℝ) ^ Fintype.card E * Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ)) := by
      intro p hp
      rw [mem_product, mem_powersetCard] at hp
      set SX : Finset E := (Finset.univ : Finset E).filter (fun e ↦ e.1 ⊆ p.1)
      have hSX_card : SX.card = m.choose t := by
        have hbij : SX.card = (p.1.powersetCard t).card := by
          refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
          · intro e he
            rw [mem_filter] at he
            rw [mem_powersetCard]
            exact ⟨he.2, e.2⟩
          · intro e₁ _ e₂ _ hEq
            exact Subtype.ext hEq
          · intro s hs
            rw [mem_powersetCard] at hs
            exact ⟨⟨s, hs.2⟩, by simp [SX, hs.1], rfl⟩
        rw [hbij, card_powersetCard, hp.1.2]
      have hEq : badPair p = (Finset.univ : Finset (E → Bool)).filter (fun f ↦
          ((SX.filter (fun e ↦ f e = p.2)).card : ℝ) < α * (SX.card : ℝ)) := by
        ext f
        simp only [badPair, mem_filter, mem_univ, true_and, hSX_card, hp.1.2]
        have hfilt : (Finset.univ : Finset E).filter (fun e ↦ e.1 ⊆ p.1 ∧ f e = p.2) =
            SX.filter (fun e ↦ f e = p.2) := by
          ext e; simp [SX]
        rw [hfilt]
      rw [hEq]
      have hcb := card_bad_colorings_for_subset SX p.2 hα0 hα1
      simpa [hSX_card] using hcb
    have hsum : ∑ p ∈ pairs, ((badPair p).card : ℝ) ≤
        (pairs.card : ℝ) *
          ((2 : ℝ) ^ Fintype.card E *
            Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ))) := by
      have := Finset.sum_le_sum h2
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have hpairs_card : (pairs.card : ℝ) = 2 * (n.choose m : ℝ) := by
      simp [pairs, card_product, card_powersetCard, mul_comm]
    rw [hcardE]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card E := by positivity
    calc
      (badAll.card : ℝ) ≤ ∑ p ∈ pairs, ((badPair p).card : ℝ) := h1
      _ ≤ (pairs.card : ℝ) *
            ((2 : ℝ) ^ Fintype.card E *
              Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ))) := hsum
      _ = (2 : ℝ) ^ Fintype.card E *
            (2 * (n.choose m : ℝ) *
              Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ))) := by
            rw [hpairs_card]; ring
      _ < (2 : ℝ) ^ Fintype.card E * 1 := mul_lt_mul_of_pos_left hbound h2pos
      _ = (2 : ℝ) ^ Fintype.card E := mul_one _
  have hbad_lt_nat : badAll.card < (Finset.univ : Finset (E → Bool)).card := by
    rw [Finset.card_univ]
    exact_mod_cast hbad_lt
  obtain ⟨f, _, hf_not_bad⟩ : ∃ f ∈ (Finset.univ : Finset (E → Bool)), f ∉ badAll := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (E → Bool)) ⊆ badAll := fun x hx ↦ h x hx
    exact not_lt_of_ge (Finset.card_le_card hsub) hbad_lt_nat
  refine ⟨fun s ↦ if hs : s.card = t then f ⟨s, hs⟩ else false, ?_⟩
  intro Y hYm b
  have hcount : ∀ X ∈ Y.powersetCard m,
      α * (m.choose t : ℝ) ≤
        (((X.powersetCard t).filter (fun e ↦ (if hs : e.card = t then f ⟨e, hs⟩ else false) = b)).card : ℝ) := by
    intro X hX
    rw [mem_powersetCard] at hX
    have hp : (X, b) ∈ pairs := by
      simp [pairs, mem_powersetCard, hX.2]
    have hf_good : f ∉ badPair (X, b) := fun hmem ↦
      hf_not_bad (mem_biUnion.mpr ⟨(X, b), hp, hmem⟩)
    simp only [badPair, mem_filter, mem_univ, true_and, not_lt, hX.2] at hf_good
    have hcard_eq :
        ((Finset.univ : Finset E).filter (fun e ↦ e.1 ⊆ X ∧ f e = b)).card =
          ((X.powersetCard t).filter
            (fun e ↦ (if hs : e.card = t then f ⟨e, hs⟩ else false) = b)).card := by
      refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
      · intro e he
        rw [mem_filter] at he
        rw [mem_filter, mem_powersetCard]
        refine ⟨⟨he.2.1, e.2⟩, ?_⟩
        simp [e.2, he.2.2]
      · intro e₁ _ e₂ _ hEq
        exact Subtype.ext hEq
      · intro s hs
        rw [mem_filter, mem_powersetCard] at hs
        refine ⟨⟨s, hs.1.2⟩, ?_, rfl⟩
        rw [mem_filter]
        refine ⟨mem_univ _, hs.1.1, ?_⟩
        simpa [hs.1.2] using hs.2
    rw [← hcard_eq]
    exact hf_good
  have hY := averaging_powersetCard htm hYm hcount
  refine ⟨?_, hY⟩
  have hchoose_pos : (0 : ℝ) < (Y.card.choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos (le_trans htm hYm)
  have hposR : (0 : ℝ) < (((Y.powersetCard t).filter
      (fun e ↦ (if hs : e.card = t then f ⟨e, hs⟩ else false) = b)).card : ℝ) :=
    lt_of_lt_of_le (mul_pos hα0 hchoose_pos) hY
  exact_mod_cast hposR

/- ### Part 4: Elementary binomial lower bound and asymptotic upper bound -/

lemma choose_ge_pow_div {m t : ℕ} (h : 2 * t ≤ m) :
    (m : ℝ) ^ t / ((2 : ℝ) ^ t * (t.factorial : ℝ)) ≤ (m.choose t : ℝ) := by
  have hnat : m ^ t ≤ 2 ^ t * (t.factorial * m.choose t) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    have hdesc : ∀ k : ℕ, k ≤ t → m ^ k ≤ 2 ^ k * m.descFactorial k := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_succ, Nat.descFactorial_succ]
        have hk1 : m ≤ 2 * (m - k) := by omega
        calc
          m ^ k * m ≤ (2 ^ k * m.descFactorial k) * (2 * (m - k)) :=
            Nat.mul_le_mul (ih (by omega)) hk1
          _ = 2 ^ k * 2 * ((m - k) * m.descFactorial k) := by ring
    exact hdesc t le_rfl
  have hR : (m : ℝ) ^ t ≤ ((2 : ℝ) ^ t * (t.factorial : ℝ)) * (m.choose t : ℝ) := by
    have : ((m ^ t : ℕ) : ℝ) ≤ ((2 ^ t * (t.factorial * m.choose t) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at this
    linarith
  have hden : (0 : ℝ) < (2 : ℝ) ^ t * (t.factorial : ℝ) := by positivity
  exact (div_le_iff₀ hden).mpr (by linarith)

lemma balancedColoringThreshold_le_of_bound {n t m : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 2) (htm : t ≤ m) (hmn : m ≤ n)
    (hbound : 2 * (n.choose m : ℝ) *
      Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ)) < 1) :
    Hypergraph.balancedColoringThreshold n t α ≤ m := by
  unfold Hypergraph.balancedColoringThreshold
  exact Nat.sInf_le (exists_balanced_coloring_of_bound hα0 hα1 htm hmn hbound)

lemma balancedColoringThreshold_upper {t : ℕ} (ht : 3 ≤ t) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤
        C * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) := by
  set δ : ℝ := 1 / 2 - α
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  set κ : ℝ := (1 / 4) * δ ^ 2 / ((2 : ℝ) ^ t * (t.factorial : ℝ))
  have hκ0 : 0 < κ := by positivity
  have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  set C₀ : ℝ := (2 / κ) ^ (((t : ℝ) - 1)⁻¹)
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨C₀ + 1, by linarith, ?_⟩
  have hlog_top : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow_top : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.mpr ht1)).comp hlog_top
  have hscaled_top : Tendsto (fun n : ℕ ↦ C₀ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) atTop atTop :=
    Tendsto.const_mul_atTop hC₀ hrpow_top
  have hlittle : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    have h : (fun x : ℝ ↦ Real.log x) =o[atTop] (fun x : ℝ ↦ x) := by
      simpa [Real.rpow_one] using isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
    exact h.comp_tendsto tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, C₀ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) + 1 ≤ (n : ℝ) := by
    have h1 := hlittle.bound (show (0 : ℝ) < (2 * (C₀ + 1))⁻¹ by positivity)
    filter_upwards [h1, eventually_ge_atTop 3, hlog_top.eventually (eventually_ge_atTop 1)] with n hn h3 hlog1
    have hrle : (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) ≤ Real.log (n : ℝ) := by
      have hexp : ((t : ℝ) - 1)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ ht1]
        have : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        linarith
      calc
        (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) ≤ (Real.log (n : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 hexp
        _ = Real.log (n : ℝ) := Real.rpow_one _
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hn_nonneg] at hn
    have hmul : (2 * (C₀ + 1)) * Real.log (n : ℝ) ≤ (n : ℝ) := by
      have hpos : (0 : ℝ) < 2 * (C₀ + 1) := by positivity
      calc
        (2 * (C₀ + 1)) * Real.log (n : ℝ)
            ≤ (2 * (C₀ + 1)) * ((2 * (C₀ + 1))⁻¹ * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hn hpos.le
        _ = (n : ℝ) := by field_simp [ne_of_gt hpos]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
    nlinarith
  filter_upwards [
    eventually_ge_atTop 3,
    hlog_top.eventually (eventually_ge_atTop 1),
    hrpow_top.eventually (eventually_ge_atTop 1),
    hscaled_top.eventually (eventually_ge_atTop (2 * (t : ℝ))),
    hsmall
  ] with n hn3 hlog1 hrpow1 hge2t hle_n
  set x : ℝ := C₀ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)
  set m : ℕ := Nat.ceil x
  have hx_le_m : x ≤ (m : ℝ) := Nat.le_ceil x
  have hm_lt : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm2t : 2 * t ≤ m := by
    have : ((2 * t : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have htm : t ≤ m := by omega
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by
      have : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    linarith
  have hchoose_le : (n.choose m : ℝ) ≤ (n : ℝ) ^ m := by
    have hnat : n.choose m ≤ n ^ m := by
      calc
        n.choose m ≤ m.factorial * n.choose m := Nat.le_mul_of_pos_left _ (Nat.factorial_pos m)
        _ = n.descFactorial m := (Nat.descFactorial_eq_factorial_mul_choose n m).symm
        _ ≤ n ^ m := Nat.descFactorial_le_pow n m
    exact_mod_cast hnat
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    linarith
  have hnpow_eq : (n : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hn_pos]
  have hchoose_ge := choose_ge_pow_div hm2t
  have hm_pow : (2 / κ) * Real.log (n : ℝ) ≤ (m : ℝ) ^ (t - 1) := by
    have hx_nonneg : 0 ≤ x := by positivity
    have hx_pow : x ^ (t - 1) = (2 / κ) * Real.log (n : ℝ) := by
      have ht1_eq : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
      rw [← Real.rpow_natCast x (t - 1), ht1_eq]
      dsimp [x, C₀]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by linarith)]
      rw [inv_mul_cancel₀ (ne_of_gt ht1), Real.rpow_one, Real.rpow_one]
    calc
      (2 / κ) * Real.log (n : ℝ) = x ^ (t - 1) := hx_pow.symm
      _ ≤ (m : ℝ) ^ (t - 1) := pow_le_pow_left₀ hx_nonneg hx_le_m (t - 1)
  have hkappa_mt : 2 * (m : ℝ) * Real.log (n : ℝ) ≤ κ * (m : ℝ) ^ t := by
    have hmt : (m : ℝ) ^ t = (m : ℝ) * (m : ℝ) ^ (t - 1) := by
      conv_lhs => rw [show t = (t - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hmt]
    have h1 : 2 * Real.log (n : ℝ) ≤ κ * (m : ℝ) ^ (t - 1) := by
      have := mul_le_mul_of_nonneg_left hm_pow hκ0.le
      have hsimp : κ * ((2 / κ) * Real.log (n : ℝ)) = 2 * Real.log (n : ℝ) := by
        field_simp [ne_of_gt hκ0]
      linarith
    have := mul_le_mul_of_nonneg_left h1 hm_pos.le
    linarith
  have hlog2_lt : Real.log 2 < 1 := by
    have h2e : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    calc
      Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  have hexp_arg : Real.log 2 + (m : ℝ) * Real.log (n : ℝ) <
      (1 / 4) * δ ^ 2 * (m.choose t : ℝ) := by
    have h1 : κ * (m : ℝ) ^ t ≤ (1 / 4) * δ ^ 2 * (m.choose t : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hchoose_ge (show (0 : ℝ) ≤ (1 / 4) * δ ^ 2 by positivity)
      have heq : κ * (m : ℝ) ^ t =
          (1 / 4) * δ ^ 2 * ((m : ℝ) ^ t / ((2 : ℝ) ^ t * (t.factorial : ℝ))) := by
        dsimp [κ]; ring
      linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      linarith
    have hmlog : (1 : ℝ) ≤ (m : ℝ) * Real.log (n : ℝ) := by nlinarith
    linarith
  have hbound : 2 * (n.choose m : ℝ) *
      Real.exp (-(1 / 4) * (1 / 2 - α) ^ 2 * (m.choose t : ℝ)) < 1 := by
    calc
      2 * (n.choose m : ℝ) * Real.exp (-(1 / 4) * δ ^ 2 * (m.choose t : ℝ))
          ≤ 2 * (n : ℝ) ^ m * Real.exp (-(1 / 4) * δ ^ 2 * (m.choose t : ℝ)) := by
            gcongr
      _ = Real.exp (Real.log 2) * Real.exp ((m : ℝ) * Real.log (n : ℝ)) *
            Real.exp (-(1 / 4) * δ ^ 2 * (m.choose t : ℝ)) := by
            rw [Real.exp_log (by norm_num), hnpow_eq]
      _ = Real.exp (Real.log 2 + (m : ℝ) * Real.log (n : ℝ) -
            (1 / 4) * δ ^ 2 * (m.choose t : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hthresh : Hypergraph.balancedColoringThreshold n t α ≤ m :=
    balancedColoringThreshold_le_of_bound hα0 hα1 htm hmn hbound
  have hthreshR : (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hthresh
  calc
    (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤ (m : ℝ) := hthreshR
    _ ≤ x + 1 := hm_lt.le
    _ = C₀ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) + 1 := rfl
    _ ≤ C₀ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) +
          1 * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) := by linarith
    _ = (C₀ + 1) * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹) := by ring

/- ### Part 5: Lower bound extraction from `H1` / `H2` and assembly of `main` -/

lemma balancedColoringThreshold_ge_of_forall {n t : ℕ} {α B : ℝ}
    (h : ∀ col : Finset (Fin n) → Bool,
      ∃ X : Finset (Fin n), B ≤ (X.card : ℝ) ∧
        ∃ b : Bool,
          (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
            α * (X.card.choose t : ℝ)) :
    B ≤ (Hypergraph.balancedColoringThreshold n t α : ℝ) := by
  unfold Hypergraph.balancedColoringThreshold
  set S : Set ℕ := {m | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
    0 < count ∧ α * (X.card.choose t : ℝ) ≤ count}
  have hne : S.Nonempty := by
    refine ⟨n + 1, fun _ ↦ false, ?_⟩
    intro X hX
    have hle : X.card ≤ n := by
      simpa using Finset.card_le_univ X
    omega
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  rcases hmem with ⟨col, hcol⟩
  rcases h col with ⟨X, hXB, b, hb⟩
  have hlt : X.card < sInf S := by
    by_contra hge
    push Not at hge
    have := (hcol X hge b).2
    linarith
  have hltR : (X.card : ℝ) < ((sInf S : ℕ) : ℝ) := by exact_mod_cast hlt
  linarith

lemma balancedColoringThreshold_lower (h1 : H1) (h2 : H2) {t : ℕ} (ht : 3 ≤ t)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (Hypergraph.balancedColoringThreshold n t α : ℝ) := by
  by_cases ht3 : t = 3
  · subst ht3
    obtain ⟨c, hc, hev⟩ := h1 α hα0 hα1
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev, eventually_ge_atTop 1] with n hn _
    have hpow : (Real.log (n : ℝ)) ^ ((((3 : ℕ) : ℝ) - 1)⁻¹) = Real.sqrt (Real.log (n : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [hpow]
    exact balancedColoringThreshold_ge_of_forall hn
  · have ht4 : 4 ≤ t := by omega
    obtain ⟨c, hc, hev⟩ := h2 t ht4 α hα0 hα1
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with n hn
    exact balancedColoringThreshold_ge_of_forall hn

theorem main : H1 → H2 → type_of% @Erdos161.erdos_161.parts.ii := by
  intro h1 h2 t ht α β hα0 hα1 hβ0 hβ1
  obtain ⟨Cα, hCα, hUα⟩ := balancedColoringThreshold_upper ht hα0 hα1
  obtain ⟨Cβ, hCβ, hUβ⟩ := balancedColoringThreshold_upper ht hβ0 hβ1
  obtain ⟨cα, hcα, hLα⟩ := balancedColoringThreshold_lower h1 h2 ht hα0 hα1
  obtain ⟨cβ, hcβ, hLβ⟩ := balancedColoringThreshold_lower h1 h2 ht hβ0 hβ1
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨Cα / cβ, ?_⟩
    filter_upwards [hUα, hLβ] with n hUa hLb
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h1' : (Hypergraph.balancedColoringThreshold n t α : ℝ) * cβ ≤
        Cα * (Hypergraph.balancedColoringThreshold n t β : ℝ) := by
      calc
        (Hypergraph.balancedColoringThreshold n t α : ℝ) * cβ
            ≤ (Cα * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) * cβ :=
              mul_le_mul_of_nonneg_right hUa hcβ.le
        _ = Cα * (cβ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) := by ring
        _ ≤ Cα * (Hypergraph.balancedColoringThreshold n t β : ℝ) :=
              mul_le_mul_of_nonneg_left hLb hCα.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hcβ]
    exact h1'
  · rw [Asymptotics.isBigO_iff]
    refine ⟨Cβ / cα, ?_⟩
    filter_upwards [hUβ, hLα] with n hUb hLa
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h2' : (Hypergraph.balancedColoringThreshold n t β : ℝ) * cα ≤
        Cβ * (Hypergraph.balancedColoringThreshold n t α : ℝ) := by
      calc
        (Hypergraph.balancedColoringThreshold n t β : ℝ) * cα
            ≤ (Cβ * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) * cα :=
              mul_le_mul_of_nonneg_right hUb hcα.le
        _ = Cβ * (cα * (Real.log (n : ℝ)) ^ (((t : ℝ) - 1)⁻¹)) := by ring
        _ ≤ Cβ * (Hypergraph.balancedColoringThreshold n t α : ℝ) :=
              mul_le_mul_of_nonneg_left hLa hCβ.le
    rw [div_mul_eq_mul_div, le_div_iff₀ hcα]
    exact h2'

end OMA.R_Erdos161_erdos_161_parts_ii_R1
