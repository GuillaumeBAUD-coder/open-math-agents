import FormalConjectures.ErdosProblems.«244»

-- Reduction Erdos244.erdos_244.variants.Romanoff.R1 of Erdős Problem 244, Romanoff
-- Credit: @senamakel
-- Romanoff (1934): for an integer C > 1 the numbers p + C^k have positive lower density.
-- H1 (first moment, elementary from Chebyshev): the number of pairs (p, k) with p + C^k < x is >= c x.
-- H2 (second moment, Romanoff's sieve estimate, the hard part): sum_{n<x} r_C(n)^2 <= K x,
--   where r_C(n) counts the representations n = p + C^k.
-- main glues them by Cauchy-Schwarz: N(x)^2 <= #{n < x represented} * sum r_C(n)^2.
namespace OMA.R_Erdos244_erdos_244_variants_Romanoff_R1

def H1 : Prop :=
  ∀ C : ℕ, 1 < C → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x ≤ (((Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ)

def H2 : Prop :=
  ∀ C : ℕ, 1 < C → ∃ K : ℝ, ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    ∑ n ∈ Finset.range x, (((Finset.range n ×ˢ Finset.range n).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 = n)).card : ℝ) ^ 2 ≤ K * x

lemma lt_pow_of_one_lt {C : ℕ} (hC : 1 < C) (k : ℕ) : k < C ^ k :=
  Nat.lt_pow_self hC

lemma count_le {C : ℕ} (hC : 1 < C) (x : ℕ) :
    (((Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ) ^ 2 ≤
    (({ p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) } ∩ Set.Iio x).ncard : ℝ) *
    ∑ n ∈ Finset.range x, (((Finset.range n ×ˢ Finset.range n).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 = n)).card : ℝ) ^ 2 := by
  set P := (Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x) with hP
  set f : ℕ × ℕ → ℕ := fun q => q.1 + C ^ q.2 with hf
  set r : ℕ → ℝ := fun n => (((Finset.range n ×ˢ Finset.range n).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 = n)).card : ℝ) with hr
  set t := P.image f with ht
  have hmaps : Set.MapsTo f (P : Set (ℕ × ℕ)) (t : Set ℕ) := fun q hq =>
    Finset.mem_coe.2 (Finset.mem_image_of_mem f (Finset.mem_coe.1 hq))
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ n ∈ t, ((P.filter fun q => f q = n).card : ℝ) = r n := by
    intro n hn
    simp only [hr]
    congr 2
    ext ⟨p, k⟩
    simp only [hP, hf, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have hnx : n < x := by
      obtain ⟨q, hq, hqn⟩ := Finset.mem_image.1 hn
      simp only [hP, Finset.mem_filter] at hq
      rw [← hqn]; exact hq.2.2
    have h1 := lt_pow_of_one_lt hC k
    have h2 : 0 < C ^ k := by positivity
    constructor
    · rintro ⟨⟨⟨_, _⟩, hp, _⟩, he⟩
      exact ⟨⟨by omega, by omega⟩, hp, he⟩
    · rintro ⟨⟨_, _⟩, hp, he⟩
      exact ⟨⟨⟨by omega, by omega⟩, hp, by omega⟩, he⟩
  have hsub : t ⊆ Finset.range x := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
    simp only [hP, Finset.mem_filter] at hq
    exact Finset.mem_range.2 hq.2.2
  have hS : (t : Set ℕ) ⊆ { p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) } ∩ Set.Iio x := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hn)
    simp only [hP, Finset.mem_filter] at hq
    refine ⟨⟨q.1, q.2, hq.2.1, ?_⟩, Set.mem_Iio.2 hq.2.2⟩
    simp only [hf]
    congr 1
  have hfin : ({ p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) } ∩ Set.Iio x).Finite :=
    (Set.finite_Iio x).subset Set.inter_subset_right
  have htc : (t.card : ℝ) ≤
      (({ p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) } ∩ Set.Iio x).ncard : ℝ) := by
    have := Set.ncard_le_ncard hS hfin
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hPsum : (P.card : ℝ) = ∑ n ∈ t, r n := by
    rw [hcard, Nat.cast_sum]
    exact Finset.sum_congr rfl hfib
  calc (P.card : ℝ) ^ 2 = (∑ n ∈ t, r n) ^ 2 := by rw [hPsum]
    _ ≤ t.card * ∑ n ∈ t, r n ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ * ∑ n ∈ Finset.range x, r n ^ 2 := by
        exact mul_le_mul htc
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem main : H1 → H2 → type_of% @Erdos244.erdos_244.variants.Romanoff := by
  intro h1 h2 C hC
  obtain ⟨c, hc, x₁, hx₁⟩ := h1 C hC
  obtain ⟨K, x₂, hx₂⟩ := h2 C hC
  set S : Set ℕ := { p + ⌊C ^ k⌋₊ | (p) (k) (_ : p.Prime) } with hSdef
  -- K is positive
  have key : ∀ x : ℕ, max (max x₁ x₂) 1 ≤ x →
      0 < K ∧ c ^ 2 / K ≤ S.partialDensity Set.univ x := by
    intro x hx
    have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxpos : (0 : ℝ) < x := by
      have : 1 ≤ x := le_trans (le_max_right _ _) hx
      exact_mod_cast this
    have A := hx₁ x hx1
    have B := hx₂ x hx2
    have D := count_le hC x
    set N := (((Finset.range x ×ˢ Finset.range x).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x)).card : ℝ)
    set M := ((S ∩ Set.Iio x).ncard : ℝ)
    set Q := ∑ n ∈ Finset.range x, (((Finset.range n ×ˢ Finset.range n).filter
      (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 = n)).card : ℝ) ^ 2
    have hM : 0 ≤ M := Nat.cast_nonneg _
    have hcx : 0 < c * x := mul_pos hc hxpos
    have hN2 : (c * x) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hcx.le A 2
    have hMQ : (c * x) ^ 2 ≤ M * (K * x) :=
      le_trans hN2 (le_trans D (mul_le_mul_of_nonneg_left B hM))
    have hKpos : 0 < K := by
      by_contra hK
      push Not at hK
      have : M * (K * x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hM (mul_nonpos_of_nonpos_of_nonneg hK hxpos.le)
      nlinarith [pow_pos hcx 2]
    refine ⟨hKpos, ?_⟩
    have hpd : S.partialDensity Set.univ x = M / x := by
      have hI : (Set.Iio x : Set ℕ) = ((Finset.range x : Finset ℕ) : Set ℕ) :=
        (Finset.coe_range x).symm
      show (((S ∩ Set.univ) ∩ Set.Iio x).ncard : ℝ) / ((Set.univ ∩ Set.Iio x).ncard : ℝ) = M / x
      rw [Set.inter_univ, Set.univ_inter, hI, Set.ncard_coe_finset, Finset.card_range, ← hI]
    rw [hpd, div_le_div_iff₀ hKpos hxpos]
    nlinarith
  obtain ⟨hK, _⟩ := key _ le_rfl
  have hev : ∀ᶠ x : ℕ in Filter.atTop, c ^ 2 / K ≤ S.partialDensity Set.univ x :=
    Filter.eventually_atTop.2 ⟨_, fun x hx => (key x hx).2⟩
  have hbdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun x : ℕ => S.partialDensity Set.univ x) :=
    Filter.IsBoundedUnder.isCoboundedUnder_ge
      (Filter.isBoundedUnder_of ⟨1, fun x => Set.partialDensity_le_one _ _ x⟩)
  have := Filter.le_liminf_of_le hbdd hev
  exact lt_of_lt_of_le (div_pos (pow_pos hc 2) hK) this

end OMA.R_Erdos244_erdos_244_variants_Romanoff_R1
