import FormalConjectures.ErdosProblems.«835»

/-! A reduction to a gap in the coefficients of the polynomial of the
field labels above each star. For seventeen colors it suffices to kill
the coefficients in degrees nine through sixteen. -/

-- Credit: @ellisjr

open Finset SimpleGraph Polynomial

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R3

/-- Find field labels such that every star polynomial has a remainder of degree
less than half the field order after its leading monomial is removed.
Its derivative must be nonzero. -/
def H1 : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ (k+1).Prime ∧ ∃ c : Finset (Fin (2*k)) → ZMod (k+1),
    ∀ S : Finset (Fin (2*k)), S.card + 1 = k →
      ∃ g : Polynomial (ZMod (k+1)), 2 * g.natDegree < k+1 ∧ g.derivative ≠ 0 ∧
        (∏ a ∈ Sᶜ, (X - C (c (insert a S)))) = X^(k+1) + g

/-- A split degree-p polynomial with such a gap and nonzero derivative has
distinct roots. This is a local assertion about one list over a prime field. -/
def H2 : Prop :=
  ∀ (p : ℕ), p.Prime → 3 ≤ p → ∀ (n : ℕ) (D : Finset (Fin n)), D.card = p →
    ∀ (f : Fin n → ZMod p) (g : Polynomial (ZMod p)),
      2 * g.natDegree < p → g.derivative ≠ 0 →
      (∏ a ∈ D, (X - C (f a))) = X^p + g → Set.InjOn f D

lemma extend_by_one {α : Type*} [DecidableEq α] {S U : Finset α}
    (sub : S ⊆ U) (size : S.card + 1 = U.card) :
    ∃ a ∉ S, insert a S = U := by
  have h : (U \ S).card = 1 := by rw [Finset.card_sdiff_of_subset sub]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hin : a ∈ U \ S := by rw [ha]; exact Finset.mem_singleton_self _
  refine ⟨a, (Finset.mem_sdiff.mp hin).2, ?_⟩
  rw [Finset.insert_eq, ← ha, Finset.sdiff_union_of_subset sub]

lemma star_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ((k+1 : ℕ) : ℕ∞) ≤ J(2*k, k).chromaticNumber := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2*k))))
    (n := k-1) (by simp; omega)
  let b (a : ↑(Sᶜ : Finset (Fin (2*k)))) : {U : Finset (Fin (2*k)) // U.card = k} :=
    ⟨insert a.1 S, by rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp a.2), hS]; omega⟩
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj (f := b)
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hS]
    omega
  · intro a z hne
    have haz : a.1 ≠ z.1 := fun h => hne (Subtype.ext h)
    change (insert a.1 S ∩ insert z.1 S).card + 1 = k
    rw [Finset.insert_inter_of_notMem (by simp [haz, Finset.mem_compl.mp a.2]),
      Finset.inter_eq_left.mpr (Finset.subset_insert _ _), hS]
    omega

theorem main : H1 → H2 → type_of% @Erdos835.erdos_835.variants.johnson := by
  classical
  rintro ⟨k, hk, prime, c, hstars⟩ rigid
  have proper : J(2*k, k).Colorable (k+1) := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => (ZMod.finEquiv (k+1)).symm (c v.1)) ?_⟩
    intro u v adj eq
    let S := u.1 ∩ v.1
    have hs : S.card + 1 = k := adj
    obtain ⟨a, ha, hu⟩ := extend_by_one (show S ⊆ u.1 from Finset.inter_subset_left)
      (hs.trans u.2.symm)
    obtain ⟨b, hb, hv⟩ := extend_by_one (show S ⊆ v.1 from Finset.inter_subset_right)
      (hs.trans v.2.symm)
    obtain ⟨g, deg, deriv, prod⟩ := hstars S hs
    have outside : Sᶜ.card = k+1 := by rw [Finset.card_compl, Fintype.card_fin]; omega
    have inj := rigid (k+1) prime (by omega) (2*k) Sᶜ outside (fun i => c (insert i S))
      g deg deriv prod
    have same : c u.1 = c v.1 := (ZMod.finEquiv (k+1)).symm.injective eq
    have e : a = b := inj (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr hb) (by
      simpa only [hu,hv] using same)
    have uv : u = v := Subtype.ext (hu.symm.trans (e ▸ hv))
    exact adj.ne uv
  refine ⟨k-3, ?_⟩
  change J(2*(k-3+3), k-3+3).chromaticNumber = ((k-3+3 : ℕ) : ℕ∞) + 1
  rw [show k-3+3 = k by omega, ← Nat.cast_add_one]
  exact le_antisymm proper.chromaticNumber_le (star_lower_bound k hk)

end OMA.R_Erdos835_erdos_835_variants_johnson_R3
