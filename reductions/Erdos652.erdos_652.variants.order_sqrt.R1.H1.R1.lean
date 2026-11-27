import OMAReductions.R_Erdos652_erdos_652_variants_order_sqrt_R1
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Use Mathialagan, On Bipartite Distinct Distances in the Plane, Theorem 14.
Only sufficiently large sets for each fixed number of centers are needed.
A crude count of the bisectors determined by two centers suffices in that
range, so the geometric construction can discard all repeated edges.
The two-circle argument handles the bounded numbers of centers separately.
-/

-- Credit: @dk8827

open Filter Finset EuclideanGeometry InnerProductSpace
open scoped BigOperators Classical

namespace OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1_H1_R1

private theorem two_circles (p q : ℝ²) (r d : ℝ) (hne : p ≠ q) (W : Finset ℝ²)
    (hW : ∀ w ∈ W, dist p w = r ∧ dist q w = d) :
    W.card ≤ 2 := by
  classical
  by_cases hn : W.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp hn]
  obtain ⟨a,ha⟩ := hn
  let L : Submodule ℝ ℝ² := (ℝ ∙ (q-p))ᗮ
  have hDim : Module.finrank ℝ L = 1 := by
    have hs := (ℝ ∙ (q-p)).finrank_add_finrank_orthogonal
    have hSub : q-p ≠ 0 := sub_ne_zero.mpr hne.symm
    rw [finrank_span_singleton hSub] at hs
    have hd : Module.finrank ℝ ℝ² = 2 := by simp
    change 1 + Module.finrank ℝ L = _ at hs
    omega
  have hneL : L ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hDim
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hneL
  have he : ℝ ∙ v = L := by
    apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv))
    rw [finrank_span_singleton hv0, hDim]
  have hOrth (x : ℝ²) (hx : x ∈ W) : x-a ∈ L := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have hp : (dist p x)^2 = (dist p a)^2 := by rw [(hW x hx).1, (hW a ha).1]
    have hq : (dist q x)^2 = (dist q a)^2 := by rw [(hW x hx).2, (hW a ha).2]
    simp only [dist_eq_norm, norm_sub_sq_real] at hp hq
    simp only [inner_sub_left, inner_sub_right]
    linarith
  let S : EuclideanGeometry.Sphere ℝ² := ⟨p,r⟩
  have hs (x : ℝ²) (hx : x ∈ W) : x ∈ S := by
    change dist x p = r
    rw [dist_comm]
    exact (hW x hx).1
  have hSub : W ⊆ {a, S.secondInter a v} := by
    intro x hx
    have hLine : x ∈ AffineSubspace.mk' a (ℝ ∙ v) := by
      rw [AffineSubspace.mem_mk', he]
      exact hOrth x hx
    have h := (Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem (hs a ha) hLine).mpr (hs x hx)
    exact mem_insert.mpr (h.imp_right mem_singleton.mpr)
  exact (card_le_card hSub).trans card_le_two

private theorem two_center_bound (P Q : Finset ℝ²) (hP : 2 ≤ P.card)
    (t : ℕ) (ht : ∀ p ∈ P, (Q.image fun q => dist q p).card ≤ t) : Q.card ≤ 2 * t ^ 2 := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.1 (by omega : 1 < P.card)
  let A := Q.image fun x => dist x p
  let B := Q.image fun x => dist x q
  let F := fun x : ℝ² => (dist x p, dist x q)
  have hF (x : ℝ²) (hx : x ∈ Q) : F x ∈ A ×ˢ B :=
    mem_product.2 ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩
  calc
    Q.card = ∑ a ∈ A ×ˢ B, (Q.filter fun x => F x = a).card := card_eq_sum_card_fiberwise hF
    _ ≤ ∑ _a ∈ A ×ˢ B, (2 : ℕ) := by
      apply sum_le_sum
      intro a _
      apply two_circles p q a.1 a.2 hpq
      intro x hx
      have he := (mem_filter.1 hx).2
      exact ⟨by rw [dist_comm]; exact congrArg Prod.fst he,
        by rw [dist_comm]; exact congrArg Prod.snd he⟩
    _ = 2 * (A.card * B.card) := by simp [card_product, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul (ht p hp) (ht q hq))


/-- Crossing inequality for a finite drawing of a simple graph. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset ℝ²) (E : Finset (ℝ² × ℝ²))
    (γ : (ℝ² × ℝ²) → ℝ → ℝ²), 0 < Q.card → 6 * Q.card ≤ E.card →
  (∀ e ∈ E, e.1 ∈ Q ∧ e.2 ∈ Q ∧ e.1 ≠ e.2 ∧ e.swap ∉ E ∧
    γ e 0 = e.1 ∧ γ e 1 = e.2 ∧ ContinuousOn (γ e) (Set.Icc 0 1) ∧
    Set.InjOn (γ e) (Set.Icc 0 1) ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, γ e x ∉ Q) →
  (∀ e ∈ E, ∀ f ∈ E, e ≠ f →
    ((γ e '' Set.Ioo (0 : ℝ) 1) ∩ (γ f '' Set.Ioo (0 : ℝ) 1)).Finite) →
  let X := ∑ e ∈ E, ∑ f ∈ E.erase e,
    ((γ e '' Set.Ioo (0 : ℝ) 1) ∩ (γ f '' Set.Ioo (0 : ℝ) 1)).ncard
  (E.card : ℝ) ^ 3 ≤ C * (Q.card : ℝ) ^ 2 * (X : ℝ)

/-- Drawing by consecutive circular arcs, with repeated edges discarded. -/
def H2 : Prop :=
  ∀ (P Q : Finset ℝ²), P ⊆ Q → 16 ≤ P.card → 64 * P.card ^ 5 ≤ Q.card →
  ∀ t : ℕ, 1 ≤ t → (t : ℝ) ≤ Real.sqrt ((P.card : ℝ) * Q.card) →
  (∀ p ∈ P, (Q.image fun q => dist q p).card ≤ t) →
  ∃ (E : Finset (ℝ² × ℝ²)) (γ : (ℝ² × ℝ²) → ℝ → ℝ²),
    P.card * Q.card ≤ 2 * E.card ∧
    (∀ e ∈ E, e.1 ∈ Q ∧ e.2 ∈ Q ∧ e.1 ≠ e.2 ∧ e.swap ∉ E ∧
    γ e 0 = e.1 ∧ γ e 1 = e.2 ∧ ContinuousOn (γ e) (Set.Icc 0 1) ∧
    Set.InjOn (γ e) (Set.Icc 0 1) ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, γ e x ∉ Q) ∧
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f →
    ((γ e '' Set.Ioo (0 : ℝ) 1) ∩ (γ f '' Set.Ioo (0 : ℝ) 1)).Finite) ∧
    let X := ∑ e ∈ E, ∑ f ∈ E.erase e,
    ((γ e '' Set.Ioo (0 : ℝ) 1) ∩ (γ f '' Set.Ioo (0 : ℝ) 1)).ncard
    X ≤ 2 * (P.card * t) ^ 2

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1.H1 := by
  classical
  rintro ⟨C, hC, cross⟩ draw
  let c : ℝ := min (1 / 8) (1 / Real.sqrt (16 * C))
  have hCroot : 0 < Real.sqrt (16 * C) := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  refine ⟨c, hc, fun k hk => ?_⟩
  rw [frequently_atTop]
  intro N
  let n := max N (64 * k ^ 5)
  have hnlarge : 64 * k ^ 5 ≤ n := le_max_right _ _
  have hn : 0 < n := lt_of_lt_of_le (by positivity) hnlarge
  refine ⟨n, le_max_left _ _, fun P Q hPQ hP hQ => ?_⟩
  let t := P.sup (fun p => (Q.image fun q => dist q p).card)
  have hPnon : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨p, hp, he⟩ := exists_mem_eq_sup P hPnon (fun p => (Q.image fun q => dist q p).card)
  have ht (q : ℝ²) (hq : q ∈ P) : (Q.image fun x => dist x q).card ≤ t :=
    Finset.le_sup (f := fun a : ℝ² => (Q.image fun x => dist x a).card) hq
  have hQpos : 0 < Q.card := by omega
  have ht₁ : 1 ≤ t := (card_pos.2 ((card_pos.1 hQpos).image _)).trans_le (ht p hp)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let S := Real.sqrt ((k : ℝ) * n)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hc8 : c ≤ 1 / 8 := min_le_left _ _
  have hroot : c * S ≤ t := by
    by_cases htlo : (t : ℝ) ≤ S
    swap
    · calc
        _ ≤ 1 * S := mul_le_mul_of_nonneg_right (hc8.trans (by norm_num)) hS
        _ ≤ _ := by simpa only [one_mul] using (le_of_not_ge htlo)
    by_cases hkbig : 16 ≤ k
    swap
    · have ht₂ := two_center_bound P Q (by omega) t ht
      rw [hQ] at ht₂
      have hb : (n : ℝ) ≤ 2 * (t : ℝ) ^ 2 := by exact_mod_cast ht₂
      have hkl : (k : ℝ) ≤ 16 := by exact_mod_cast (show k ≤ 16 by omega)
      have hkN := mul_le_mul_of_nonneg_right hkl hnr.le
      have hs2 : S ^ 2 = (k : ℝ) * n := Real.sq_sqrt (by positivity)
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hsafe : (1 / 8 : ℝ) * S ≤ t := by
        apply le_of_sq_le_sq _ ht0
        nlinarith only [hb, hkN, hs2, sq_nonneg (t : ℝ)]
      exact (mul_le_mul_of_nonneg_right hc8 hS).trans hsafe
    have hks : 16 ≤ P.card := by omega
    have hns : 64 * P.card ^ 5 ≤ Q.card := by rwa [hP, hQ]
    have hT : (t : ℝ) ≤ Real.sqrt ((P.card : ℝ) * Q.card) := by rwa [hP, hQ]
    obtain ⟨E, γ, hE, good, finite, hX⟩ := draw P Q hPQ hks hns t ht₁ hT ht
    let X := ∑ e ∈ E, ∑ f ∈ E.erase e,
      ((γ e '' Set.Ioo (0 : ℝ) 1) ∩ (γ f '' Set.Ioo (0 : ℝ) 1)).ncard
    have hcount : 6 * Q.card ≤ E.card := by
      have hl := Nat.mul_le_mul_right Q.card hks
      omega
    have hcross := cross Q E γ hQpos hcount good finite
    have hEr : (k : ℝ) * n ≤ 2 * (E.card : ℝ) := by
      rw [hP, hQ] at hE
      exact_mod_cast hE
    change X ≤ 2 * (P.card * t) ^ 2 at hX
    have hXr : (X : ℝ) ≤ 2 * ((k : ℝ) * (t : ℝ)) ^ 2 := by
      rw [hP] at hX
      exact_mod_cast hX
    change (E.card : ℝ) ^ 3 ≤ C * (Q.card : ℝ) ^ 2 * (X : ℝ) at hcross
    rw [hQ] at hcross
    have hfactor : 0 < (k : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
    have hineq : (k : ℝ) * n ≤ 16 * C * (t : ℝ) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hfactor).1
      calc
        _ = ((k : ℝ) * n) ^ 3 := by ring
        _ ≤ (2 * (E.card : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hEr 3
        _ = 8 * (E.card : ℝ) ^ 3 := by ring
        _ ≤ 8 * (C * (n : ℝ) ^ 2 * (X : ℝ)) := mul_le_mul_of_nonneg_left hcross (by norm_num)
        _ ≤ 8 * (C * (n : ℝ) ^ 2 * (2 * ((k : ℝ) * t) ^ 2)) := by gcongr
        _ = _ := by ring
    have hs' := Real.sqrt_le_sqrt hineq
    rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * C), Real.sqrt_sq (by positivity : 0 ≤ (t : ℝ))] at hs'
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hS).trans (by
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_le_iff₀ hCroot).2
      rw [mul_comm (t : ℝ)]
      exact hs')
  exact ⟨p, hp, by simpa only [S, show t = _ from he] using hroot⟩

end OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1_H1_R1
