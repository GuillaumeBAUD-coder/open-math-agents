import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R1

Varnavides supersaturation in ZMod p. For each pair w = (a, d) with d nonzero consider the
window of positions j in [1, M] with a + j d in A.

* Double counting: the windows have total size M (p - 1) |A|, because for fixed j and d the map
  a -> a + j d is a bijection.
* A window of size more than (alpha / 2) M contains an integer progression j0 + i delta by
  hypothesis, giving the modular progression (a + j0 d, delta d) in A with nonzero step; the map
  w -> (progression, j0, delta) is injective, so the number G of such windows is at most
  M^2 times the number of modular progressions.
* Averaging: M (p - 1) alpha p <= G M + p (p - 1) (alpha / 2) M, hence G >= (alpha / 2) p (p - 1).
-/

namespace Varna

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- The positions `j` in `[1, M]` at which the modular progression `w.1 + j * w.2` hits `A`. -/
def win (A : Finset (ZMod p)) (M : ℕ) (w : ZMod p × ZMod p) : Finset ℕ :=
  (Icc 1 M).filter fun j => w.1 + (j : ZMod p) * w.2 ∈ A

lemma win_subset (A : Finset (ZMod p)) (M : ℕ) (w : ZMod p × ZMod p) : win A M w ⊆ Icc 1 M :=
  filter_subset _ _

lemma card_win_le (A : Finset (ZMod p)) (M : ℕ) (w : ZMod p × ZMod p) : (win A M w).card ≤ M := by
  have := card_le_card (win_subset A M w)
  simpa using this

lemma card_X : (univ.filter fun w : ZMod p × ZMod p => w.2 ≠ 0).card = p * (p - 1) := by
  have h : (univ.filter fun w : ZMod p × ZMod p => w.2 ≠ 0) =
      (univ : Finset (ZMod p)) ×ˢ (univ.filter fun d : ZMod p => d ≠ 0) := by
    ext w
    simp
  rw [h, card_product, filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

lemma sum_win (A : Finset (ZMod p)) (M : ℕ) :
    ∑ w ∈ univ.filter (fun w : ZMod p × ZMod p => w.2 ≠ 0), (win A M w).card =
      M * ((p - 1) * A.card) := by
  have h2 : ∀ j : ℕ, ((univ.filter fun w : ZMod p × ZMod p => w.2 ≠ 0).filter
      fun w => w.1 + (j : ZMod p) * w.2 ∈ A).card = (p - 1) * A.card := by
    intro j
    have hb : ((univ.filter fun w : ZMod p × ZMod p => w.2 ≠ 0).filter
        fun w => w.1 + (j : ZMod p) * w.2 ∈ A).card =
        ((univ.filter fun d : ZMod p => d ≠ 0) ×ˢ A).card := by
      refine card_bij (fun w _ => (w.2, w.1 + (j : ZMod p) * w.2)) ?_ ?_ ?_
      · intro w hw
        simp only [mem_filter, mem_univ, true_and] at hw
        simp only [mem_product, mem_filter, mem_univ, true_and]
        exact hw
      · intro w1 _ w2 _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h2, h1⟩ := h
        rw [h2] at h1
        exact Prod.ext (add_right_cancel h1) h2
      · intro b hb
        simp only [mem_product, mem_filter, mem_univ, true_and] at hb
        refine ⟨(b.2 - (j : ZMod p) * b.1, b.1), ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and, sub_add_cancel]
          exact hb
        · simp
    rw [hb, card_product, filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have h1 : ∀ w : ZMod p × ZMod p, (win A M w).card =
      ∑ j ∈ Icc 1 M, if w.1 + (j : ZMod p) * w.2 ∈ A then 1 else 0 := fun w => card_filter _ _
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [← card_filter, h2]
  simp

lemma good_le (A : Finset (ZMod p)) (M k : ℕ) (hk : 2 ≤ k) (hMp : M < p)
    (G : Finset (ZMod p × ZMod p))
    (hG2 : ∀ w ∈ G, w.2 ≠ 0)
    (hG : ∀ w ∈ G, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ win A M w) :
    G.card ≤ (univ.filter fun u : ZMod p × ZMod p =>
      u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card * (M * M) := by
  classical
  choose! a d hd using hG
  have ha_mem : ∀ w ∈ G, a w ∈ Icc 1 M := fun w hw => by
    have := win_subset A M w ((hd w hw).2 0 (by omega))
    simpa using this
  have hd_mem : ∀ w ∈ G, d w ∈ Icc 1 M := fun w hw => by
    have h1 := mem_Icc.mp (win_subset A M w ((hd w hw).2 1 (by omega)))
    have h0 := (hd w hw).1
    exact mem_Icc.mpr ⟨h0, by omega⟩
  have hd_ne : ∀ w ∈ G, (d w : ZMod p) ≠ 0 := fun w hw h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    have h1 := mem_Icc.mp (hd_mem w hw)
    have := Nat.le_of_dvd (by omega) h
    omega
  let φ : ZMod p × ZMod p → (ZMod p × ZMod p) × (ℕ × ℕ) := fun w =>
    ((w.1 + (a w : ZMod p) * w.2, (d w : ZMod p) * w.2), (a w, d w))
  have hmaps : ∀ w ∈ G, φ w ∈ (univ.filter fun u : ZMod p × ZMod p =>
      u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) ×ˢ (Icc 1 M ×ˢ Icc 1 M) := by
    intro w hw
    refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, mul_ne_zero (hd_ne w hw) (hG2 w hw), ?_⟩,
      mem_product.mpr ⟨ha_mem w hw, hd_mem w hw⟩⟩
    intro i
    have := (mem_filter.mp ((hd w hw).2 i i.2)).2
    convert this using 1
    push_cast
    ring
  have hinj : Set.InjOn φ G := by
    intro w hw w' hw' h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, ha, hdd⟩ := h
    rw [ha] at h1
    rw [hdd] at h2
    have e2 : w.2 = w'.2 := mul_left_cancel₀ (hd_ne w' hw') h2
    rw [e2] at h1
    exact Prod.ext (add_right_cancel h1) e2
  calc G.card ≤ ((univ.filter fun u : ZMod p × ZMod p =>
        u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) ×ˢ
          (Icc 1 M ×ˢ Icc 1 M)).card := card_le_card_of_injOn φ hmaps hinj
    _ = _ := by simp [card_product]

theorem varnavides (k M : ℕ) (hk : 2 ≤ k) (hM : 2 ≤ M) (hMp : M < p) (α : ℝ)
    (A : Finset (ZMod p)) (hα : 0 < α) (hA : α * (p : ℝ) ≤ (A.card : ℝ))
    (hS : ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 M → (α / 2) * (M : ℝ) < (S.card : ℝ) →
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    (α / 2) * (p : ℝ) * ((p : ℝ) - 1) ≤ (M : ℝ) ^ 2 *
      ((Finset.univ.filter fun u : ZMod p × ZMod p =>
        u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card : ℝ) := by
  classical
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set X := univ.filter (fun w : ZMod p × ZMod p => w.2 ≠ 0) with hX
  set G := X.filter (fun w => (α / 2) * (M : ℝ) < ((win A M w).card : ℝ)) with hGdef
  have hGle := good_le A M k hk hMp G (fun w hw => (mem_filter.mp (mem_filter.mp hw).1).2)
    (fun w hw => hS _ (win_subset A M w) (mem_filter.mp hw).2)
  have hsum : (∑ w ∈ X, ((win A M w).card : ℝ)) = M * (((p : ℝ) - 1) * A.card) := by
    have := sum_win (p := p) A M
    have h' : ((∑ w ∈ X, (win A M w).card : ℕ) : ℝ) = ((M * ((p - 1) * A.card) : ℕ) : ℝ) := by
      rw [this]
    rw [Nat.cast_sum] at h'
    rw [h']
    push_cast [Nat.cast_sub hp1]
    ring
  have hsplit : (∑ w ∈ X, ((win A M w).card : ℝ)) ≤
      G.card * M + ((p : ℝ) * ((p : ℝ) - 1)) * ((α / 2) * M) := by
    rw [← sum_filter_add_sum_filter_not X
      (fun w => (α / 2) * (M : ℝ) < ((win A M w).card : ℝ))]
    refine add_le_add ?_ ?_
    · calc ∑ w ∈ G, ((win A M w).card : ℝ) ≤ ∑ _w ∈ G, (M : ℝ) :=
            sum_le_sum fun w _ => by exact_mod_cast card_win_le A M w
        _ = G.card * M := by simp
    · calc ∑ w ∈ X.filter (fun w => ¬ (α / 2) * (M : ℝ) < ((win A M w).card : ℝ)),
            ((win A M w).card : ℝ)
          ≤ ∑ _w ∈ X.filter (fun w => ¬ (α / 2) * (M : ℝ) < ((win A M w).card : ℝ)),
              (α / 2) * (M : ℝ) := sum_le_sum fun w hw => not_lt.mp (mem_filter.mp hw).2
        _ = (X.filter (fun w => ¬ (α / 2) * (M : ℝ) < ((win A M w).card : ℝ))).card *
              ((α / 2) * M) := by simp
        _ ≤ ((p : ℝ) * ((p : ℝ) - 1)) * ((α / 2) * M) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h1 : (X.filter (fun w => ¬ (α / 2) * (M : ℝ) <
                ((win A M w).card : ℝ))).card ≤ p * (p - 1) := by
              rw [← card_X (p := p)]
              exact card_le_card (filter_subset _ _)
            have h2 : ((p * (p - 1) : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
              push_cast [Nat.cast_sub hp1]
              ring
            rw [← h2]
            exact_mod_cast h1
  have hGR : (α / 2) * (p : ℝ) * ((p : ℝ) - 1) ≤ (G.card : ℝ) := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h3 : (M : ℝ) * (((p : ℝ) - 1) * (α * p)) ≤
        G.card * M + ((p : ℝ) * ((p : ℝ) - 1)) * ((α / 2) * M) := by
      calc (M : ℝ) * (((p : ℝ) - 1) * (α * p)) ≤ M * (((p : ℝ) - 1) * A.card) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hp0) hMR.le
        _ = _ := hsum.symm
        _ ≤ _ := hsplit
    have h4 : ((α / 2) * (p : ℝ) * ((p : ℝ) - 1)) * M ≤ (G.card : ℝ) * M := by linarith
    exact le_of_mul_le_mul_right h4 hMR
  calc (α / 2) * (p : ℝ) * ((p : ℝ) - 1) ≤ (G.card : ℝ) := hGR
    _ ≤ (((univ.filter fun u : ZMod p × ZMod p =>
          u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card * (M * M) : ℕ) : ℝ) := by
        exact_mod_cast hGle
    _ = _ := by push_cast; ring

end Varna

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1.H2 := by
  intro k M p hp
  have : Fact p.Prime := ⟨hp⟩
  intro _ hk hM hMp α A hα hA hS
  exact Varna.varnavides k M hk hM hMp α A hα hA hS
