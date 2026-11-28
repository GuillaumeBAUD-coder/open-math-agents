import OMAStatements.S_oeis_a132616
import Mathlib

namespace OMA.A132616proof

open OMA.S_oeis_a132616

/-- Two vectors agree on the coordinates `0..i`. -/
def Agree (i : ℕ) (v w : ℕ → ℕ) : Prop := ∀ j ≤ i, v j = w j

lemma Agree.trans {i : ℕ} {u v w : ℕ → ℕ} (h1 : Agree i u v) (h2 : Agree i v w) : Agree i u w :=
  fun j hj => (h1 j hj).trans (h2 j hj)

lemma iter_agree {i : ℕ} (f : (ℕ → ℕ) → ℕ → ℕ) (hf : ∀ v w, Agree i v w → Agree i (f v) (f w))
    (m : ℕ) : ∀ v w, Agree i v w → Agree i (f^[m] v) (f^[m] w) := by
  induction m with
  | zero => intro v w h; exact h
  | succ m ih => intro v w h; simp only [Function.iterate_succ_apply]; exact ih _ _ (hf v w h)

lemma agree_matrix (k : ℕ) : ∀ i v w, Agree i v w → Agree i (matrix k v) (matrix k w) := by
  induction k with
  | zero => intro i v w h; exact h
  | succ k ih =>
    intro i v w h j hj
    simp only [matrix]
    split_ifs with hjk
    · subst hjk
      rw [h _ hj, iter_agree (matrix k) (ih i) _ v w h k (by omega)]
    · exact ih i v w h j hj

lemma iter_succ_agree (k m : ℕ) (v : ℕ → ℕ) :
    Agree k ((matrix (k + 1))^[m] v) ((matrix k)^[m] v) := by
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    refine Agree.trans (fun j hj => ?_) (agree_matrix k k _ _ ih)
    simp only [matrix]; rw [if_neg (by omega)]

def G (k m : ℕ) : ℕ := ((matrix k)^[m] first) k

lemma matrix_top (k : ℕ) (v : ℕ → ℕ) :
    matrix (k + 1) v (k + 1) = v (k + 1) + ((matrix k)^[exponent k] v) k := by
  simp [matrix]

lemma G_succ (k m : ℕ) : G (k + 1) (m + 1) = G (k + 1) m + G k (exponent k + m) := by
  unfold G
  rw [Function.iterate_succ_apply', matrix_top]
  congr 1
  rw [Function.iterate_add_apply]
  exact iter_agree (matrix k) (agree_matrix k k) _ _ _ (iter_succ_agree k m first) k le_rfl

lemma G_sum (k m : ℕ) : G (k + 1) m = ∑ t ∈ Finset.range m, G k (exponent k + t) := by
  induction m with
  | zero => simp [G, first]
  | succ m ih => rw [G_succ, ih, Finset.sum_range_succ]

lemma G_zero (m : ℕ) : G 0 m = 1 := by
  unfold G
  show (id^[m] first) 0 = 1
  simp [first]

lemma Q (k : ℕ) : ∀ b, G (k + 1) (b + 2 * k) = nested (k + 2) b := by
  induction k with
  | zero => intro b; rw [G_sum]; simp [G_zero, nested]
  | succ k ih =>
    intro b
    rw [G_sum, show nested (k + 1 + 2) b =
      ∑ j ∈ Finset.range (b + 2 * (k + 1)), nested (k + 1 + 1) (j + 1) from rfl]
    refine Finset.sum_congr (by ring_nf) fun t _ => ?_
    rw [show exponent (k + 1) + t = (t + 1) + 2 * k by unfold exponent; omega, ih]

theorem a132616 : type_of% @OMA.S_oeis_a132616.main := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | k + 2 =>
    unfold a
    rw [matrix_top, show first (k + 1 + 1) = 0 from rfl, zero_add,
      show exponent (k + 1) = 1 + 2 * k by unfold exponent; omega]
    exact Q k 1

end OMA.A132616proof

theorem OMA.solution : type_of% @OMA.S_oeis_a132616.main := OMA.A132616proof.a132616
