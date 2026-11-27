import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
import Mathlib

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H2: hypothesis H2 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1
-- Credit: @ivillar
--
-- Write n = 2^k m with k >= 2 and m odd. Over a finite field F with more than two elements, the
-- squares x + y and a x + y (a not 0 or 1) are orthogonal Latin squares; use F = GaloisField 2 k.
-- Over ZMod m (m odd, m >= 3) use x + y and 2 x + y. The direct product of two orthogonal pairs
-- is an orthogonal pair, and orthogonal pairs transport along bijections to Fin n.

namespace OMA.Erdos724H2

/-- A pair of distinct orthogonal Latin squares on the type α. -/
def Good (α : Type*) : Prop :=
  ∃ f g : α → α → α, (∀ a, Function.Injective (f a)) ∧ (∀ b, Function.Injective (fun a => f a b)) ∧
    (∀ a, Function.Injective (g a)) ∧ (∀ b, Function.Injective (fun a => g a b)) ∧ f ≠ g ∧
    Function.Injective (fun p : α × α => (f p.1 p.2, g p.1 p.2))

lemma good_of_equiv {α β : Type*} (e : α ≃ β) (h : Good α) : Good β := by
  obtain ⟨f, g, hf1, hf2, hg1, hg2, hfg, horth⟩ := h
  refine ⟨fun x y => e (f (e.symm x) (e.symm y)), fun x y => e (g (e.symm x) (e.symm y)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a x y hxy
    exact e.symm.injective (hf1 _ (e.injective hxy))
  · intro b x y hxy
    exact e.symm.injective (hf2 _ (e.injective hxy))
  · intro a x y hxy
    exact e.symm.injective (hg1 _ (e.injective hxy))
  · intro b x y hxy
    exact e.symm.injective (hg2 _ (e.injective hxy))
  · intro h
    apply hfg
    funext x y
    have := congrFun (congrFun h (e x)) (e y)
    simpa using this
  · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    simp only [Prod.mk.injEq] at hxy
    have := horth (a₁ := (e.symm x, e.symm y)) (a₂ := (e.symm x', e.symm y'))
      (by simp only [Prod.mk.injEq]; exact ⟨e.injective hxy.1, e.injective hxy.2⟩)
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at this
    rw [this.1, this.2]

lemma good_prod {α β : Type*} [Nonempty β] (hα : Good α) (hβ : Good β) : Good (α × β) := by
  obtain ⟨f, g, hf1, hf2, hg1, hg2, hfg, horth⟩ := hα
  obtain ⟨f', g', hf1', hf2', hg1', hg2', -, horth'⟩ := hβ
  refine ⟨fun x y => (f x.1 y.1, f' x.2 y.2), fun x y => (g x.1 y.1, g' x.2 y.2),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hf1 _ hxy.1) (hf1' _ hxy.2)
  · intro b x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hf2 _ hxy.1) (hf2' _ hxy.2)
  · intro a x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hg1 _ hxy.1) (hg1' _ hxy.2)
  · intro b x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hg2 _ hxy.1) (hg2' _ hxy.2)
  · intro h
    apply hfg
    obtain ⟨b0⟩ := ‹Nonempty β›
    funext x y
    have := congrFun (congrFun h (x, b0)) (y, b0)
    simp only [Prod.mk.injEq] at this
    exact this.1
  · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    simp only [Prod.mk.injEq] at hxy
    have h1 := horth (a₁ := (x.1, y.1)) (a₂ := (x'.1, y'.1))
      (by simp only [Prod.mk.injEq]; exact ⟨hxy.1.1, hxy.2.1⟩)
    have h2 := horth' (a₁ := (x.2, y.2)) (a₂ := (x'.2, y'.2))
      (by simp only [Prod.mk.injEq]; exact ⟨hxy.1.2, hxy.2.2⟩)
    simp only [Prod.mk.injEq] at h1 h2
    exact Prod.ext (Prod.ext h1.1 h2.1) (Prod.ext h1.2 h2.2)

/-- Orthogonal squares x + y and c x + y over a commutative ring, for c with c and c - 1 cancellable. -/
lemma good_ring {R : Type*} [CommRing R] (c : R) (hc0 : ∀ x y : R, c * x = c * y → x = y)
    (hc1 : ∀ x y : R, (c - 1) * x = (c - 1) * y → x = y) (hne : c ≠ 1) : Good R := by
  refine ⟨fun x y => x + y, fun x y => c * x + y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a x y h; simpa using h
  · intro b x y h; simpa using h
  · intro a x y h; simpa using h
  · intro b x y h
    apply hc0
    simpa using h
  · intro h
    have := congrFun (congrFun h 1) 0
    simp only [add_zero, mul_one] at this
    exact hne this.symm
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx : x = x' := by
      apply hc1
      linear_combination h2 - h1
    subst hx
    have : y = y' := by linear_combination h1
    rw [this]

lemma good_field (F : Type*) [Field F] [Fintype F] (h : 2 < Fintype.card F) : Good F := by
  classical
  have : ((Finset.univ : Finset F) \ {0, 1}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨c, hc⟩ := this
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hc
  refine good_ring c (fun x y h => mul_left_cancel₀ hc.1 h) (fun x y h => ?_) hc.2
  exact mul_left_cancel₀ (sub_ne_zero.mpr hc.2) h

lemma good_zmod (m : ℕ) (hm : Odd m) (h3 : 3 ≤ m) : Good (ZMod m) := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : (2 : ZMod (2 * j + 1)) * ((j + 1 : ℕ) : ZMod (2 * j + 1)) = 1 := by
    have : ((2 * (j + 1) : ℕ) : ZMod (2 * j + 1)) = 1 := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.cast_add, ZMod.natCast_self, zero_add,
        Nat.cast_one]
    rw [← this]
    push_cast
    ring
  have cancel : ∀ x y : ZMod (2 * j + 1), 2 * x = 2 * y → x = y := by
    intro x y hxy
    calc x = ((j + 1 : ℕ) : ZMod (2 * j + 1)) * (2 * x) := by
            rw [← mul_assoc, mul_comm _ (2 : ZMod (2 * j + 1)), h2, one_mul]
      _ = ((j + 1 : ℕ) : ZMod (2 * j + 1)) * (2 * y) := by rw [hxy]
      _ = y := by rw [← mul_assoc, mul_comm _ (2 : ZMod (2 * j + 1)), h2, one_mul]
  have hne : (2 : ZMod (2 * j + 1)) ≠ 1 := by
    intro h
    have h' : ((1 : ℕ) : ZMod (2 * j + 1)) = 0 := by
      have : (2 : ZMod (2 * j + 1)) - 1 = 0 := by rw [h]; ring
      simpa [show (2 : ZMod (2 * j + 1)) - 1 = 1 by ring] using this
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd one_pos h'
    omega
  refine good_ring 2 cancel (fun x y h => ?_) hne
  simpa [show (2 : ZMod (2 * j + 1)) - 1 = 1 by ring] using h

lemma latin_of_good (n : ℕ) (h : Good (Fin n)) :
    ∃ L M : LatinSquare n, L ≠ M ∧ Erdos724.IsOrthogonal L M := by
  obtain ⟨f, g, hf1, hf2, hg1, hg2, hfg, horth⟩ := h
  refine ⟨⟨f, hf1, hf2⟩, ⟨g, hg1, hg2⟩, ?_, horth⟩
  intro h
  apply hfg
  have := congrArg LatinSquare.mat h
  exact this

end OMA.Erdos724H2

open OMA.Erdos724H2 in
theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2 := by
  unfold OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2
  intro n h4 hn
  apply latin_of_good
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hk : 2 ≤ k := by
    by_contra hk
    obtain ⟨j, rfl⟩ := hm
    interval_cases k <;> omega
  classical
  haveI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k (by omega)]
  have hF : Good (GaloisField 2 k) := by
    apply good_field
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · have hm1 : m = 1 := by obtain ⟨j, rfl⟩ := hm; omega
    subst hm1
    rw [mul_one]
    exact good_of_equiv (Fintype.equivFinOfCardEq hcard) hF
  · haveI : NeZero m := ⟨by omega⟩
    have hP := good_prod hF (good_zmod m hm hm3)
    have hcard2 : Fintype.card (GaloisField 2 k × ZMod m) = 2 ^ k * m := by
      rw [Fintype.card_prod, hcard, ZMod.card]
    exact good_of_equiv (Fintype.equivFinOfCardEq hcard2) hP
