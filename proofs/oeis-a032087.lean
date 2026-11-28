import OMAStatements.S_oeis_a032087
import Mathlib

/-!
# A032087: reversible strings over four letters

Reversal is an involution on words, so it swaps the words below their reversal with the words
above it, and the remaining words are the palindromes. A palindrome is fixed by its first
`⌈n/2⌉` letters (`palEquiv`), so there are `4 ^ ⌈n/2⌉` of them. Hence
`2 · beadCount n + 4 ^ ⌈n/2⌉ = 4 ^ n` for `n > 1`, and `4 ^ ⌈n/2⌉` is `2 ^ n` or `2 ^ (n + 1)`.
-/

namespace OMA.A032087Proof
open OMA.S_oeis_a032087

lemma rev_rev {n : ℕ} (w : Word n) : reverseWord (reverseWord w) = w := by
  funext i; simp [reverseWord, Fin.rev_rev]

/-- Palindromes are determined by their first `⌈n/2⌉` letters. -/
def palEquiv (n : ℕ) : {w : Word n // w = reverseWord w} ≃ (Fin ((n + 1) / 2) → Fin 4) where
  toFun w := fun j => w.1 ⟨j, by omega⟩
  invFun v := ⟨fun i => if h : i.val < (n + 1) / 2 then v ⟨i, h⟩ else v ⟨n - 1 - i, by omega⟩, by
    funext i
    simp only [reverseWord, Fin.val_rev]
    by_cases h1 : i.val < (n + 1) / 2 <;> by_cases h2 : n - (i.val + 1) < (n + 1) / 2
    · rw [dif_pos h1, dif_pos h2]; congr 1; ext; simp; omega
    · rw [dif_pos h1, dif_neg h2]; congr 1; ext; simp; omega
    · rw [dif_neg h1, dif_pos h2]; congr 1; ext; simp; omega
    · exfalso; omega⟩
  left_inv w := by
    obtain ⟨w, hw⟩ := w
    apply Subtype.ext
    funext i
    simp only
    by_cases h1 : i.val < (n + 1) / 2
    · rw [dif_pos h1]
    · rw [dif_neg h1]
      conv_rhs => rw [hw]
      simp only [reverseWord]
      congr 1; ext; simp; omega
  right_inv v := by
    funext j
    simp only
    rw [dif_pos j.2]

lemma card_pal (n : ℕ) :
    (Finset.univ.filter fun w : Word n => w = reverseWord w).card = 4 ^ ((n + 1) / 2) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (palEquiv n)]
  simp

lemma card_lt_eq_card_gt (n : ℕ) :
    (Finset.univ.filter fun w : Word n => List.ofFn w < List.ofFn (reverseWord w)).card =
    (Finset.univ.filter fun w : Word n => List.ofFn (reverseWord w) < List.ofFn w).card := by
  refine Finset.card_bij' (fun w _ => reverseWord w) (fun w _ => reverseWord w) ?_ ?_ ?_ ?_
  · intro w hw; simpa [rev_rev] using hw
  · intro w hw; simpa [rev_rev] using hw
  · intro w _; exact rev_rev w
  · intro w _; exact rev_rev w

lemma count (n : ℕ) :
    2 * (Finset.univ.filter fun w : Word n => List.ofFn w < List.ofFn (reverseWord w)).card
      + 4 ^ ((n + 1) / 2) = 4 ^ n := by
  have hT : (Finset.univ : Finset (Word n)).card = 4 ^ n := by simp
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Word n))) (fun w : Word n => List.ofFn w < List.ofFn (reverseWord w))
  set N := Finset.univ.filter fun w : Word n => ¬ List.ofFn w < List.ofFn (reverseWord w)
  have h2 := Finset.card_filter_add_card_filter_not (s := N) (fun w : Word n => w = reverseWord w)
  have hE : N.filter (fun w : Word n => w = reverseWord w) =
      Finset.univ.filter fun w : Word n => w = reverseWord w := by
    ext w; simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; refine ⟨?_, h⟩; rw [← h]; exact lt_irrefl _
  have hG : N.filter (fun w : Word n => ¬ w = reverseWord w) =
      Finset.univ.filter fun w : Word n => List.ofFn (reverseWord w) < List.ofFn w := by
    ext w; simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy (List.ofFn w) (List.ofFn (reverseWord w)) with h | h | h
      · exact absurd h h1
      · exact absurd (List.ofFn_injective h) h2
      · exact h
    · intro h
      exact ⟨fun h' => lt_asymm h h', fun h' => by rw [← h'] at h; exact lt_irrefl _ h⟩
  rw [hE, hG, card_pal, ← card_lt_eq_card_gt] at h2
  omega

theorem main' : beadCount 1 = 4 ∧ ∀ n : ℕ, 1 < n →
    beadCount n = (4 ^ n - (if Even n then 2 ^ n else 2 ^ (n + 1))) / 2 := by
  refine ⟨?_, fun n hn => ?_⟩
  · unfold beadCount
    simp
  · have hb : beadCount n =
        (Finset.univ.filter fun w : Word n => List.ofFn w < List.ofFn (reverseWord w)).card := by
      unfold beadCount
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h | h)
        · omega
        · exact h
      · exact Or.inr
    have hc := count n
    have hp : (if Even n then 2 ^ n else 2 ^ (n + 1)) = 4 ^ ((n + 1) / 2) := by
      split_ifs with he
      · obtain ⟨k, rfl⟩ := he
        rw [show (k + k + 1) / 2 = k by omega, show k + k = 2 * k by ring, pow_mul]; norm_num
      · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp he
        rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
          pow_mul]; norm_num
    rw [hb, hp]
    omega

end OMA.A032087Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032087.main := OMA.A032087Proof.main'
