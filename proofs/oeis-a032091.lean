import OMAStatements.S_oeis_a032091
import Mathlib

/-!
# A032091: reversible strings with 4 black beads

A word for `n` is a triple `(A, B, C)` of subsets of `Fin m`, `Fin m`, `Fin r` (`m = ⌊(n-1)/2⌋`,
`r = (n-1) mod 2`) with 4 elements in total; these correspond to 4-subsets of an `(n-1)`-set
(`card_triples`). Swapping `A` and `B` pairs the triples with key `A < B` and key `B < A` (`split`);
the rest have `A = B`, hence `|A| = 2` and `C = ∅` (`card_diag`). So
`2 · beadCount n + C(m, 2) = C(n-1, 4)`, and expanding the binomials gives the two quartics.
-/

namespace OMA.A032091Common

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

end OMA.A032091Common

namespace OMA.A032091Proof
open OMA.S_oeis_a032091 OMA.A032091Common

lemma c4 (j : ℕ) : 24 * (j + 4).choose 4 = (j + 4) * (j + 3) * (j + 2) * (j + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (j + 4) 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at h
  rw [show j + 4 - 3 = j + 1 by omega, show j + 4 - 2 = j + 2 by omega,
    show j + 4 - 1 = j + 3 by omega, show j + 4 - 0 = j + 4 by omega] at h
  linarith

lemma c2 (j : ℕ) : 2 * (j + 2).choose 2 = (j + 2) * (j + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (j + 2) 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at h
  rw [show j + 2 - 1 = j + 1 by omega, show j + 2 - 0 = j + 2 by omega] at h
  linarith

/-- `2 · beadCount n + C(⌊(n-1)/2⌋, 2) = C(n-1, 4)`. -/
lemma count (n : ℕ) : 2 * beadCount n + ((n - 1) / 2).choose 2 = (n - 1).choose 4 := by
  have hsplit := split (words (n - 1)) (fun w hw => by
      rw [words, Finset.mem_filter] at hw ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h2 := hw.2
      unfold blackCount at h2 ⊢
      dsimp only at h2 ⊢
      omega)
    (halfKey (m := (n - 1) / 2)) (fun s t h => key_inj h)
  have htot : (words (n - 1)).card = (n - 1).choose 4 := by
    have := card_triples (Fin ((n - 1) / 2)) (Fin ((n - 1) % 2)) 4
    simp only [Fintype.card_fin] at this
    rw [show 2 * ((n - 1) / 2) + (n - 1) % 2 = n - 1 by omega] at this
    rw [← this]; rfl
  have hd : ((words (n - 1)).filter fun w => w.1 = w.2.1).card = ((n - 1) / 2).choose 2 := by
    have := card_diag (α := Fin ((n - 1) / 2)) (β := Fin ((n - 1) % 2)) 4 2 0 (fun A C => by
      have h1 : C.card ≤ (n - 1) % 2 := by simpa using Finset.card_le_univ C
      have h2 : (n - 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega)
    simp only [Fintype.card_fin, Nat.choose_zero_right, mul_one] at this
    rw [← this]; rfl
  have hb : beadCount n = ((words (n - 1)).filter fun w => halfKey w.1 < halfKey w.2.1).card := rfl
  rw [hb]
  generalize ((words (n - 1)).filter fun w => halfKey w.1 < halfKey w.2.1).card = L at hsplit ⊢
  rw [hd, htot] at hsplit
  omega

theorem main' : ∀ n : ℕ, 6 ≤ n → (beadCount n : ℚ) =
    if Even n then ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 32*n)/48
    else ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 38*n + 15)/48 := by
  intro n hn
  have hc := count n
  generalize beadCount n = B at hc ⊢
  split_ifs with he
  · obtain ⟨u, rfl⟩ : ∃ u, n = 2 * u + 6 := by obtain ⟨t, ht⟩ := he; exact ⟨t - 3, by omega⟩
    rw [show (2 * u + 6 - 1) / 2 = u + 2 by omega, show 2 * u + 6 - 1 = (2 * u + 1) + 4 by omega] at hc
    have h4 := c4 (2 * u + 1)
    have h2 := c2 u
    have q1 : (2 * (B : ℚ)) + ((u + 2).choose 2 : ℕ) = (((2 * u + 1) + 4).choose 4 : ℕ) := by
      exact_mod_cast hc
    have q2 : (24 : ℚ) * (((2 * u + 1) + 4).choose 4 : ℕ) =
        ((2 * u + 1 : ℕ) + 4) * ((2 * u + 1 : ℕ) + 3) * ((2 * u + 1 : ℕ) + 2) * ((2 * u + 1 : ℕ) + 1) := by
      exact_mod_cast h4
    have q3 : (2 : ℚ) * ((u + 2).choose 2 : ℕ) = ((u : ℚ) + 2) * ((u : ℚ) + 1) := by exact_mod_cast h2
    push_cast at q1 q2 q3 ⊢
    linear_combination (1 / 2 : ℚ) * q1 + (1 / 48 : ℚ) * q2 - (1 / 4 : ℚ) * q3
  · obtain ⟨u, rfl⟩ : ∃ u, n = 2 * u + 7 := by
      obtain ⟨t, ht⟩ := Nat.not_even_iff_odd.mp he; exact ⟨t - 3, by omega⟩
    rw [show (2 * u + 7 - 1) / 2 = (u + 1) + 2 by omega, show 2 * u + 7 - 1 = (2 * u + 2) + 4 by omega] at hc
    have h4 := c4 (2 * u + 2)
    have h2 := c2 (u + 1)
    have q1 : (2 * (B : ℚ)) + (((u + 1) + 2).choose 2 : ℕ) = (((2 * u + 2) + 4).choose 4 : ℕ) := by
      exact_mod_cast hc
    have q2 : (24 : ℚ) * (((2 * u + 2) + 4).choose 4 : ℕ) =
        ((2 * u + 2 : ℕ) + 4) * ((2 * u + 2 : ℕ) + 3) * ((2 * u + 2 : ℕ) + 2) * ((2 * u + 2 : ℕ) + 1) := by
      exact_mod_cast h4
    have q3 : (2 : ℚ) * (((u + 1) + 2).choose 2 : ℕ) = ((u + 1 : ℕ) + 2) * ((u + 1 : ℕ) + 1) := by
      exact_mod_cast h2
    push_cast at q1 q2 q3 ⊢
    linear_combination (1 / 2 : ℚ) * q1 + (1 / 48 : ℚ) * q2 - (1 / 4 : ℚ) * q3

end OMA.A032091Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032091.main := OMA.A032091Proof.main'
