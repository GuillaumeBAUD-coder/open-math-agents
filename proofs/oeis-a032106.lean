import OMAStatements.S_oeis_a032106
import Mathlib

/-!
# A032106: reversible strings with n black beads

A word is a triple `(A, B, C)` of subsets of `Fin (n-1)`, `Fin (n-1)`, `Unit` with `n` elements in
total. Such triples correspond to `n`-subsets of a `(2n-1)`-set (`card_triples`, via
`Finset.toLeft` / `toRight`). Swapping `A` and `B` pairs the triples with key `A < B` and key `B < A`
(`split`); the rest have `A = B`, and these are counted by `card_diag`. So
`2 · beadCount n + diag = C(2n-1, n)`, and `C(2N, N) = 2 C(2N-1, N)` gives the stated form.
-/


namespace OMA.A032106Common

/-- Triples of finsets with a given total size: `(2|α| + |β|).choose k` of them. -/
lemma card_triples (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (k : ℕ) :
    (Finset.univ.filter fun w : Finset α × Finset α × Finset β =>
      w.1.card + w.2.1.card + w.2.2.card = k).card = (2 * Fintype.card α + Fintype.card β).choose k := by
  let e : Finset (α ⊕ α ⊕ β) ≃ Finset α × Finset α × Finset β :=
    { toFun := fun u => (u.toLeft, u.toRight.toLeft, u.toRight.toRight)
      invFun := fun w => w.1.disjSum (w.2.1.disjSum w.2.2)
      left_inv := fun u => by simp [Finset.toLeft_disjSum_toRight]
      right_inv := fun w => by simp }
  have hc : ∀ u : Finset (α ⊕ α ⊕ β),
      (e u).1.card + (e u).2.1.card + (e u).2.2.card = u.card := by
    intro u
    show u.toLeft.card + u.toRight.toLeft.card + u.toRight.toRight.card = u.card
    rw [add_assoc, Finset.card_toLeft_add_card_toRight, Finset.card_toLeft_add_card_toRight]
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (e.symm.subtypeEquiv (p := fun w => w.1.card + w.2.1.card + w.2.2.card = k)
    (q := fun u => u.card = k) (fun w => by rw [← hc (e.symm w), Equiv.apply_symm_apply]))]
  rw [Fintype.card_subtype, Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_sum, Fintype.card_sum]
  congr 1; ring

/-- `halfKey`-style keys are injective. -/
lemma key_inj {m : ℕ} {s t : Finset (Fin m)}
    (h : List.ofFn (fun i : Fin m => decide (i ∈ s)) = List.ofFn (fun i : Fin m => decide (i ∈ t))) :
    s = t := by
  have := List.ofFn_injective h
  ext i
  have hi := congrFun this i
  simpa using hi

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Swapping the first two sets pairs the triples with `key A < key B` and `key B < key A`;
what is left are the triples with `A = B`. -/
lemma split (W : Finset (Finset α × Finset α × Finset β))
    (hW : ∀ w ∈ W, (w.2.1, w.1, w.2.2) ∈ W) (key : Finset α → List Bool)
    (hk : Function.Injective key) :
    W.card = 2 * (W.filter fun w => key w.1 < key w.2.1).card +
      (W.filter fun w => w.1 = w.2.1).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := W) (fun w => key w.1 < key w.2.1)
  set N := W.filter fun w => ¬ key w.1 < key w.2.1
  have h2 := Finset.card_filter_add_card_filter_not (s := N) (fun w => w.1 = w.2.1)
  have hE : N.filter (fun w => w.1 = w.2.1) = W.filter fun w => w.1 = w.2.1 := by
    ext w; simp only [N, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h; exact ⟨⟨h.1, by rw [h.2]; exact lt_irrefl _⟩, h.2⟩
  have hG : N.filter (fun w => ¬ w.1 = w.2.1) = W.filter fun w => key w.2.1 < key w.1 := by
    ext w; simp only [N, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, h1⟩, h2⟩
      refine ⟨hw, ?_⟩
      rcases lt_trichotomy (key w.1) (key w.2.1) with h | h | h
      · exact absurd h h1
      · exact absurd (hk h) h2
      · exact h
    · rintro ⟨hw, h⟩
      exact ⟨⟨hw, fun h' => lt_asymm h h'⟩, fun h' => by rw [h'] at h; exact lt_irrefl _ h⟩
  have hLG : (W.filter fun w => key w.1 < key w.2.1).card =
      (W.filter fun w => key w.2.1 < key w.1).card := by
    refine Finset.card_bij' (fun w _ => (w.2.1, w.1, w.2.2)) (fun w _ => (w.2.1, w.1, w.2.2))
      ?_ ?_ ?_ ?_
    · intro w hw; simp only [Finset.mem_filter] at hw ⊢; exact ⟨hW w hw.1, hw.2⟩
    · intro w hw; simp only [Finset.mem_filter] at hw ⊢; exact ⟨hW w hw.1, hw.2⟩
    · intro w _; rfl
    · intro w _; rfl
  rw [hE, hG] at h2
  omega

/-- Diagonal triples `(A, A, C)` with forced sizes `|A| = a`, `|C| = c`. -/
lemma card_diag (k a c : ℕ)
    (hac : ∀ A : Finset α, ∀ C : Finset β, 2 * A.card + C.card = k ↔ A.card = a ∧ C.card = c) :
    ((Finset.univ.filter fun w : Finset α × Finset α × Finset β =>
      w.1.card + w.2.1.card + w.2.2.card = k).filter fun w => w.1 = w.2.1).card =
      (Fintype.card α).choose a * (Fintype.card β).choose c := by
  rw [← Finset.card_univ (α := α), ← Finset.card_univ (α := β), ← Finset.card_powersetCard,
    ← Finset.card_powersetCard, ← Finset.card_product]
  refine Finset.card_bij' (fun w _ => (w.1, w.2.2)) (fun p _ => (p.1, p.1, p.2)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨h1, h2⟩ := hw
    have h3 : 2 * w.1.card + w.2.2.card = k := by rw [← h2] at h1; omega
    simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact (hac w.1 w.2.2).1 h3
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hp
    have := (hac p.1 p.2).2 hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    omega
  · intro w hw
    simp only [Finset.mem_filter] at hw
    obtain ⟨a1, a2, a3⟩ := w
    simp only at hw ⊢
    rw [hw.2]
  · intro p _; rfl

end OMA.A032106Common

namespace OMA.A032106Proof
open OMA.S_oeis_a032106 OMA.A032106Common

lemma central (s : ℕ) : (2 * s + 2).choose (s + 1) = 2 * (2 * s + 1).choose (s + 1) := by
  rw [show 2 * s + 2 = (2 * s + 1) + 1 by ring, Nat.choose_succ_succ,
    show (2 * s + 1).choose s = (2 * s + 1).choose (s + 1) from (Nat.choose_symm_half s).symm]
  ring

theorem main' : beadCount 1 = 1 ∧ ∀ n : ℕ, 1 < n → beadCount n =
    if Even n then ((2*n).choose n - n.choose (n/2))/4
    else ((2*n-1).choose (n-1) - (n-1).choose ((n-1)/2))/2 := by
  refine ⟨by decide, fun n hn => ?_⟩
  have hb : beadCount n = ((words n).filter fun w => halfKey w.1 < halfKey w.2.1).card := by
    unfold beadCount
    congr 1
    refine Finset.filter_congr fun w _ => ⟨fun h => ?_, fun h => Or.inr h⟩
    rcases h with h | h
    · omega
    · exact h
  have hsplit := split (words n) (fun w hw => by
      rw [words, Finset.mem_filter] at hw ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h2 := hw.2
      unfold blackCount at h2 ⊢
      dsimp only at h2 ⊢
      omega)
    (halfKey (m := n - 1)) (fun s t h => key_inj h)
  have htot : (words n).card = (2 * (n - 1) + 1).choose n := by
    have := card_triples (Fin (n - 1)) Unit n
    simp only [Fintype.card_fin, Fintype.card_unit] at this
    rw [← this]; rfl
  rw [hb]
  generalize ((words n).filter fun w => halfKey w.1 < halfKey w.2.1).card = L at hsplit ⊢
  split_ifs with he
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 2 := by obtain ⟨t, ht⟩ := he; exact ⟨t - 1, by omega⟩
    have hd : ((words (2 * s + 2)).filter fun w => w.1 = w.2.1).card =
        (2 * s + 2 - 1).choose (s + 1) := by
      have := card_diag (α := Fin (2 * s + 2 - 1)) (β := Unit) (2 * s + 2) (s + 1) 0
        (fun A C => by
          have : C.card ≤ 1 := by simpa using Finset.card_le_univ C
          omega)
      simp only [Fintype.card_fin, Fintype.card_unit, Nat.choose_zero_right, mul_one] at this
      rw [← this]; rfl
    rw [hd, htot] at hsplit
    rw [show 2 * (2 * s + 2 - 1) + 1 = 2 * (2 * s + 1) + 1 by omega,
      show 2 * s + 2 - 1 = 2 * s + 1 by omega] at hsplit
    have c1 := central (2 * s + 1)
    have c2 := central s
    rw [show 2 * s + 1 + 1 = 2 * s + 2 by ring] at c1
    rw [show 2 * (2 * s + 2) = 2 * (2 * s + 1) + 2 by ring, show (2 * s + 2) / 2 = s + 1 by omega,
      c1, c2]
    omega
  · obtain ⟨t, rfl⟩ := Nat.not_even_iff_odd.mp he
    have hd : ((words (2 * t + 1)).filter fun w => w.1 = w.2.1).card = (2 * t).choose t := by
      have := card_diag (α := Fin (2 * t + 1 - 1)) (β := Unit) (2 * t + 1) t 1 (fun A C => by
        have : C.card ≤ 1 := by simpa using Finset.card_le_univ C
        omega)
      simp only [Fintype.card_fin, Fintype.card_unit, Nat.choose_one_right, mul_one,
        Nat.add_sub_cancel] at this
      rw [← this]; rfl
    rw [hd, htot, show 2 * (2 * t + 1 - 1) + 1 = 4 * t + 1 by omega] at hsplit
    rw [show 2 * (2 * t + 1) - 1 = 4 * t + 1 by omega, show 2 * t + 1 - 1 = 2 * t by omega,
      show 2 * t / 2 = t by omega]
    have hs : (4 * t + 1).choose (2 * t + 1) = (4 * t + 1).choose (2 * t) := by
      rw [show 4 * t + 1 = 2 * (2 * t) + 1 by ring]; exact Nat.choose_symm_half (2 * t)
    rw [hs] at hsplit
    omega

end OMA.A032106Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032106.main := OMA.A032106Proof.main'
