import OMAReductions.R_Erdos934_erdos_934_variants_h_two_R1

-- Step Erdos934.erdos_934.variants.h_two.R1.H1: the blow-up of the 5-cycle with m vertices per class
-- (d = 2m) has maximum degree d, 5m^2 = 5d^2/4 edges, and any two edges are at distance at most 1.

open SimpleGraph Finset

namespace OMA.E934H1

/-- The class (position on the 5-cycle) of a vertex of `Fin (5 * m)`. -/
def cls {m : ℕ} (u : Fin (5 * m)) : Fin 5 := (finProdFinEquiv.symm u).1

lemma fin5_ne_succ : ∀ c : Fin 5, c ≠ c + 1 := by decide

/-- The blow-up of the 5-cycle with `m` vertices per class. -/
def C5blow (m : ℕ) : SimpleGraph (Fin (5 * m)) where
  Adj u v := cls v = cls u + 1 ∨ cls u = cls v + 1
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by rcases h with h | h <;> exact fin5_ne_succ _ h⟩

instance (m : ℕ) : DecidableRel (C5blow m).Adj := fun u v =>
  inferInstanceAs (Decidable (cls v = cls u + 1 ∨ cls u = cls v + 1))

lemma two_nbr_classes : ∀ a : Fin 5,
    (univ.filter (fun b : Fin 5 => b = a + 1 ∨ a = b + 1)).card = 2 := by decide

lemma degree_eq (m : ℕ) (u : Fin (5 * m)) : (C5blow m).degree u = 2 * m := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hn : (C5blow m).neighborFinset u =
      univ.filter (fun v => cls v = cls u + 1 ∨ cls u = cls v + 1) := by
    ext v; rw [mem_neighborFinset, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl
  rw [hn]
  rw [Finset.card_equiv (finProdFinEquiv.symm)
    (t := (univ.filter (fun b : Fin 5 => b = cls u + 1 ∨ cls u = b + 1)) ×ˢ (univ : Finset (Fin m)))]
  · rw [Finset.card_product, two_nbr_classes, Finset.card_univ, Fintype.card_fin]
  · intro v; simp [cls]

lemma ncard_nbr (m : ℕ) (u : Fin (5 * m)) : ((C5blow m).neighborSet u).ncard = 2 * m := by
  classical
  rw [Set.ncard_eq_toFinset_card', ← degree_eq m u]
  rfl

lemma ncard_edges (m : ℕ) : (C5blow m).edgeSet.ncard = 5 * m ^ 2 := by
  classical
  have h := sum_degrees_eq_twice_card_edges (C5blow m)
  simp only [degree_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [Set.ncard_eq_toFinset_card']
  have : (C5blow m).edgeSet.toFinset = (C5blow m).edgeFinset := rfl
  rw [this]
  nlinarith [h]

lemma classes_close : ∀ p q r s : Fin 5, (q = p + 1 ∨ p = q + 1) → (s = r + 1 ∨ r = s + 1) →
    (r = p + 1 ∨ p = r + 1) ∨ (s = p + 1 ∨ p = s + 1) ∨
    (r = q + 1 ∨ q = r + 1) ∨ (s = q + 1 ∨ q = s + 1) := by decide

lemma no_far (m : ℕ) : ¬ Erdos934.HasFarEdges (C5blow m) 2 := by
  rintro ⟨u, v, w, x, huv, hwx, h⟩
  have key : ∀ a ∈ ({u, v} : Set (Fin (5 * m))), ∀ b ∈ ({w, x} : Set (Fin (5 * m))),
      ¬ (C5blow m).Adj a b := by
    intro a ha b hb hab
    have h2 := h a ha b hb
    rw [(edist_eq_one_iff_adj).mpr hab] at h2
    norm_num at h2
  have hu : u ∈ ({u, v} : Set (Fin (5 * m))) := by simp
  have hv : v ∈ ({u, v} : Set (Fin (5 * m))) := by simp
  have hw : w ∈ ({w, x} : Set (Fin (5 * m))) := by simp
  have hx : x ∈ ({w, x} : Set (Fin (5 * m))) := by simp
  rcases classes_close (cls u) (cls v) (cls w) (cls x) huv hwx with h1 | h1 | h1 | h1
  · exact key u hu w hw h1
  · exact key u hu x hx h1
  · exact key v hv w hw h1
  · exact key v hv x hx h1

theorem h1 : ∀ d : ℕ, Even d → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ d) ∧ 5 * d ^ 2 / 4 ≤ G.edgeSet.ncard ∧
      ¬ Erdos934.HasFarEdges G 2 := by
  rintro d ⟨m, rfl⟩
  refine ⟨5 * m, C5blow m, fun v => ?_, ?_, no_far m⟩
  · rw [ncard_nbr]; omega
  · rw [ncard_edges]
    have : 5 * (m + m) ^ 2 = 4 * (5 * m ^ 2) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

end OMA.E934H1

theorem OMA.solution : OMA.R_Erdos934_erdos_934_variants_h_two_R1.H1 :=
  OMA.E934H1.h1
