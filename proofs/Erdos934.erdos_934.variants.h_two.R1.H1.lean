import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1
import Mathlib

-- Step Erdos934.erdos_934.variants.h_two.R1.H1: hypothesis H1 of reduction
-- Erdos934.erdos_934.variants.h_two.R1
-- Credit: @ivillar
--
-- Construction. For d = 2k take the blow-up of the 5-cycle: vertices Fin 5 × Fin k (moved to
-- Fin (5 * k) by finProdFinEquiv), with (a, i) adjacent to (b, j) iff a and b are neighbours on
-- the 5-cycle. Every vertex has its neighbours in two classes of size k, so degree at most 2k;
-- the edges s((a, i), (a + 1, j)) are 5 k ^ 2 distinct edges; and any two edges of the 5-cycle
-- have adjacent endpoints (checked by decide), so any two edges of the blow-up have endpoints at
-- distance at most 1.

open SimpleGraph Finset

namespace OMA.Erdos934H1

/-- Any two edges of the 5-cycle have a pair of adjacent endpoints. -/
lemma c5_close : ∀ a b c e : Fin 5, (b = a + 1 ∨ a = b + 1) → (e = c + 1 ∨ c = e + 1) →
    ((c = a + 1 ∨ a = c + 1) ∨ (e = a + 1 ∨ a = e + 1) ∨
      (c = b + 1 ∨ b = c + 1) ∨ (e = b + 1 ∨ b = e + 1)) := by
  decide

lemma c5_irrefl : ∀ a : Fin 5, ¬ (a = a + 1 ∨ a = a + 1) := by decide

lemma c5_pred : ∀ a b : Fin 5, a = b + 1 → b = a + 4 := by decide

lemma c5_no_two : ∀ a a' : Fin 5, a = a' + 1 → a + 1 = a' → False := by decide

/-- The blow-up of the 5-cycle with `k` vertices per class. -/
def blowup (k : ℕ) : SimpleGraph (Fin (5 * k)) where
  Adj i j := (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm i).1 + 1 ∨
    (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> exact c5_irrefl _ (Or.inl h)⟩

lemma degree_le (k : ℕ) (i : Fin (5 * k)) : ((blowup k).neighborSet i).ncard ≤ k + k := by
  classical
  set a := (finProdFinEquiv.symm i).1 with ha
  let S : Finset (Fin 5 × Fin k) := ({a + 1, a + 4} : Finset (Fin 5)) ×ˢ (Finset.univ)
  have hsub : (blowup k).neighborSet i ⊆
      ((S.map (finProdFinEquiv : Fin 5 × Fin k ≃ Fin (5 * k)).toEmbedding : Finset _) : Set _) := by
    intro j hj
    rw [mem_neighborSet] at hj
    have hj' : (finProdFinEquiv.symm j).1 = a + 1 ∨ a = (finProdFinEquiv.symm j).1 + 1 := hj
    rw [Finset.coe_map, Set.mem_image]
    refine ⟨finProdFinEquiv.symm j, ?_, Equiv.apply_symm_apply _ _⟩
    rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hj' with h | h
    · exact Or.inl h
    · exact Or.inr (c5_pred _ _ h)
  calc ((blowup k).neighborSet i).ncard
      ≤ ((S.map (finProdFinEquiv : Fin 5 × Fin k ≃ Fin (5 * k)).toEmbedding : Finset _) :
          Set _).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = #S := by rw [Set.ncard_coe_finset, Finset.card_map]
    _ ≤ 2 * k := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (Finset.card_le_two)
    _ = k + k := by ring

lemma edges_ge (k : ℕ) : 5 * k * k ≤ (blowup k).edgeSet.ncard := by
  classical
  let e : Fin 5 × Fin k ≃ Fin (5 * k) := finProdFinEquiv
  let f : Fin 5 × Fin k × Fin k → Sym2 (Fin (5 * k)) := fun x => s(e (x.1, x.2.1), e (x.1 + 1, x.2.2))
  have hinj : Function.Injective f := by
    rintro ⟨a, i, j⟩ ⟨a', i', j'⟩ h
    simp only [f, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' := e.injective h1
      have h2' := e.injective h2
      simp only [Prod.mk.injEq] at h1' h2'
      obtain ⟨rfl, rfl⟩ := h1'
      rw [h2'.2]
    · have h1' := e.injective h1
      have h2' := e.injective h2
      simp only [Prod.mk.injEq] at h1' h2'
      exact (c5_no_two a a' h1'.1 h2'.1).elim
  have hsub : ((Finset.univ.image f : Finset _) : Set (Sym2 (Fin (5 * k)))) ⊆ (blowup k).edgeSet := by
    intro z hz
    rw [Finset.coe_image, Set.mem_image] at hz
    obtain ⟨⟨a, i, j⟩, -, rfl⟩ := hz
    simp only [f, mem_edgeSet, blowup, e, Equiv.symm_apply_apply]
    first | exact Or.inl rfl | exact Or.inl trivial | simp
  calc 5 * k * k = #(Finset.univ.image f) := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
        ring
    _ = ((Finset.univ.image f : Finset _) : Set (Sym2 (Fin (5 * k)))).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (blowup k).edgeSet.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

lemma not_far (k : ℕ) : ¬ Erdos934.HasFarEdges (blowup k) 2 := by
  rintro ⟨u, v, w, x, huv, hwx, h⟩
  have key : ∀ a b : Fin (5 * k), (blowup k).Adj a b → ¬ ((2 : ℕ) : ℕ∞) ≤ (blowup k).edist a b := by
    intro a b hab hle
    have h1 : (blowup k).edist a b = 1 := edist_eq_one_iff_adj.mpr hab
    rw [h1] at hle
    norm_num at hle
  have hc := c5_close (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm v).1
    (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm x).1 huv hwx
  rcases hc with hc | hc | hc | hc
  · exact key u w hc (h u (by simp) w (by simp))
  · exact key u x hc (h u (by simp) x (by simp))
  · exact key v w hc (h v (by simp) w (by simp))
  · exact key v x hc (h v (by simp) x (by simp))

end OMA.Erdos934H1

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 := by
  unfold OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1
  intro d hd
  obtain ⟨k, rfl⟩ := hd
  refine ⟨5 * k, OMA.Erdos934H1.blowup k, OMA.Erdos934H1.degree_le k, ?_,
    OMA.Erdos934H1.not_far k⟩
  have h4 : 5 * (k + k) ^ 2 = 4 * (5 * k * k) := by ring
  rw [h4, Nat.mul_div_cancel_left _ (by norm_num)]
  exact OMA.Erdos934H1.edges_ge k
