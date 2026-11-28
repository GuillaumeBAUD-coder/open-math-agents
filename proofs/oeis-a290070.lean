import OMAStatements.S_oeis_a290070
import Mathlib

namespace OMA.S_oeis_a290070

def nxt (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (641 : ℕ).testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

lemma state_succ (t : ℕ) : state 641 (t+1) = nxt (state 641 t) := by
  funext x y; rfl

def Q1 (x y : ℤ) : Bool := decide (1 < x.natAbs + y.natAbs)

def P (b : Bool) (x y : ℤ) : Bool :=
  decide ((-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1) → (b = true ∧ x = 0 ∧ y = 0))

lemma state1 : state 641 1 = Q1 := by
  rw [state_succ]
  funext x y
  have hx : x ≤ -3 ∨ (-2 ≤ x ∧ x ≤ 2) ∨ 3 ≤ x := by omega
  have hy : y ≤ -3 ∨ (-2 ≤ y ∧ y ≤ 2) ∨ 3 ≤ y := by omega
  by_cases hf : x ≤ -3 ∨ 3 ≤ x ∨ y ≤ -3 ∨ 3 ≤ y
  · have h0 : ∀ a b : ℤ, (a ≤ -2 ∨ 2 ≤ a ∨ b ≤ -2 ∨ 2 ≤ b) → state 641 0 a b = false := by
      intro a b h
      simp only [state]
      simp
      omega
    have e1 := h0 x y (by omega)
    have e2 := h0 (x-1) y (by omega)
    have e3 := h0 (x+1) y (by omega)
    have e4 := h0 x (y-1) (by omega)
    have e5 := h0 x (y+1) (by omega)
    simp only [nxt, e1, e2, e3, e4, e5]
    have : Q1 x y = true := by simp [Q1]; omega
    rw [this]; decide
  · have hx' : -2 ≤ x ∧ x ≤ 2 := by omega
    have hy' : -2 ≤ y ∧ y ≤ 2 := by omega
    obtain ⟨hx1, hx2⟩ := hx'
    obtain ⟨hy1, hy2⟩ := hy'
    interval_cases x <;> interval_cases y <;> decide

lemma state2 : state 641 2 = P true := by
  rw [state_succ, state1]
  funext x y
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have h0 : ∀ a b : ℤ, (a ≤ -3 ∨ 3 ≤ a ∨ b ≤ -3 ∨ b ≤ -3 ∨ 3 ≤ b) → Q1 a b = true := by
      intro a b h; simp [Q1]; omega
    have e1 := h0 x y (by omega)
    have e2 := h0 (x-1) y (by omega)
    have e3 := h0 (x+1) y (by omega)
    have e4 := h0 x (y-1) (by omega)
    have e5 := h0 x (y+1) (by omega)
    simp only [nxt, e1, e2, e3, e4, e5]
    have : P true x y = true := by simp [P]; omega
    rw [this]; decide
  · have hx' : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy' : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx'
    obtain ⟨hy1, hy2⟩ := hy'
    interval_cases x <;> interval_cases y <;> decide

lemma stepP (b : Bool) : nxt (P b) = P (!b) := by
  funext x y
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have h0 : ∀ a b' : ℤ, (a ≤ -3 ∨ 3 ≤ a ∨ b' ≤ -3 ∨ 3 ≤ b') → P b a b' = true := by
      intro a b' h; simp [P]; omega
    have e1 := h0 x y (by omega)
    have e2 := h0 (x-1) y (by omega)
    have e3 := h0 (x+1) y (by omega)
    have e4 := h0 x (y-1) (by omega)
    have e5 := h0 x (y+1) (by omega)
    simp only [nxt, e1, e2, e3, e4, e5]
    have : P (!b) x y = true := by simp [P]; omega
    rw [this]; decide
  · have hx' : -3 ≤ x ∧ x ≤ 3 := by omega
    have hy' : -3 ≤ y ∧ y ≤ 3 := by omega
    obtain ⟨hx1, hx2⟩ := hx'
    obtain ⟨hy1, hy2⟩ := hy'
    cases b <;> interval_cases x <;> interval_cases y <;> decide

lemma stateP (n : ℕ) : state 641 (n+2) = P (decide (n % 2 = 0)) := by
  induction n with
  | zero => simpa using state2
  | succ k ih =>
    rw [show k + 1 + 2 = (k+2)+1 by ring, state_succ, ih, stepP]
    congr 1
    by_cases h : k % 2 = 0
    · have : ¬ (k+1) % 2 = 0 := by omega
      simp [h, this]
    · have : (k+1) % 2 = 0 := by omega
      simp [h, this]

/-- ON-ness of the diagonal / central row cells. -/
lemma Pdiag (b : Bool) (k : ℕ) : P b (-(k:ℤ)) (-(k:ℤ)) = P b (-(k:ℤ)) 0 := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> simp [P]
  · have h' : (2:ℤ) ≤ k := by exact_mod_cast h
    have a : P b (-(k:ℤ)) (-(k:ℤ)) = true := by simp [P]; omega
    have c : P b (-(k:ℤ)) 0 = true := by simp [P]; omega
    rw [a, c]

def tt (e : ℤ) (k : ℕ) : ℤ := if k = 0 then e else if k = 1 then 0 else 10 ^ k

lemma Pval (b : Bool) (k : ℕ) : ((P b (-(k:ℤ)) 0).toNat : ℤ) = if k = 0 then (if b then 1 else 0) else if k = 1 then 0 else 1 := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> cases b <;> simp [P]
  · have h' : (2:ℤ) ≤ k := by exact_mod_cast h
    have c : P b (-(k:ℤ)) 0 = true := by simp [P]; omega
    rw [c]; simp; omega

lemma digits_eq (n : ℕ) (hn : 2 ≤ n) (f : ℤ → ℤ → Bool)
    (hf : ∀ k : ℕ, f (-(n:ℤ) + (n - k : ℕ)) (-(n:ℤ) + (n-k:ℕ)) = f (-(n:ℤ) + (n - k : ℕ)) (-(n:ℤ) + (n-k:ℕ))) : True := trivial

lemma sumform (n : ℕ) (b : Bool) (g : ℕ → ℤ)
    (hg : ∀ k, g k = ((P b (-(k:ℤ)) 0).toNat : ℤ)) :
    9 * (∑ k ∈ Finset.range (n+2), g k * 10 ^ k) = 9 * (if b then 1 else 0) + 10 ^ (n+2) - 100 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_succ, hg, Pval]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hg, Pval]
    simp
    ring

lemma digits_form (n : ℕ) (hn : 2 ≤ n) (diag : Bool) :
    9 * (∑ i ∈ Finset.range (n+1),
      ((state 641 n ((i : ℤ) - n) (if diag then ((i : ℤ) - n) else 0)).toNat : ℤ) * 10 ^ (n-i)) =
      9 * (if n % 2 = 0 then 1 else 0) + 10 ^ (n+1) - 100 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
  rw [stateP]
  have : (∑ i ∈ Finset.range (m+2+1),
      ((P (decide (m % 2 = 0)) ((i : ℤ) - ↑(m+2)) (if diag then ((i : ℤ) - ↑(m+2)) else 0)).toNat : ℤ) * 10 ^ (m+2-i))
      = ∑ k ∈ Finset.range (m+2+1), ((P (decide (m % 2 = 0)) (-(k:ℤ)) 0).toNat : ℤ) * 10 ^ k := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m + 2 + 1 := Finset.mem_range.1 hk
    have e1 : m + 2 + 1 - 1 - k = m + 2 - k := by omega
    rw [e1]
    have e2 : ((((m+2-k : ℕ)) : ℤ) - ((m+2 : ℕ) : ℤ)) = -(k:ℤ) := by
      push_cast [Nat.cast_sub (show k ≤ m+2 by omega)]; ring
    have e3 : m + 2 - (m + 2 - k) = k := by omega
    rw [e2, e3]
    cases diag <;> simp [Pdiag]
  rw [this]
  have := sumform (m+1) (decide (m % 2 = 0)) (fun k => ((P (decide (m % 2 = 0)) (-(k:ℤ)) 0).toNat : ℤ)) (fun k => rfl)
  rw [this]
  by_cases h : m % 2 = 0
  · have h2 : (m+2) % 2 = 0 := by omega
    simp [h, h2]
  · have h2 : ¬ (m+2) % 2 = 0 := by omega
    simp [h, h2]

lemma ha (n : ℕ) (hn : 2 ≤ n) :
    9 * a n = 9 * (if n % 2 = 0 then 1 else 0) + 10 ^ (n+1) - 100 := by
  have := digits_form n hn true
  simpa [a, digits] using this

lemma hrow (n : ℕ) (hn : 2 ≤ n) : a n = A283504 n := by
  have h1 := digits_form n hn true
  have h2 := digits_form n hn false
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  have : 9 * a n = 9 * A283504 n := by
    have h3 := h1.trans h2.symm
    simpa [a, digits, A283504] using h3
  omega

lemma hrec (m : ℕ) : a (m+5) = 10 * a (m+4) + a (m+3) - 10 * a (m+2) := by
  have h5 := ha (m+5) (by omega)
  have h4 := ha (m+4) (by omega)
  have h3 := ha (m+3) (by omega)
  have h2 := ha (m+2) (by omega)
  have e : (10:ℤ) ^ (m+5+1) = 10 * 10 ^ (m+4+1) := by ring
  have e' : (10:ℤ) ^ (m+4+1) = 10 * 10 ^ (m+3+1) := by ring
  have e'' : (10:ℤ) ^ (m+3+1) = 10 * 10 ^ (m+2+1) := by ring
  by_cases h : m % 2 = 0
  · have a1 : (m+5) % 2 ≠ 0 := by omega
    have a2 : (m+4) % 2 = 0 := by omega
    have a3 : (m+3) % 2 ≠ 0 := by omega
    have a4 : (m+2) % 2 = 0 := by omega
    simp only [a1, a2, a3, a4, if_true, if_false] at h5 h4 h3 h2
    omega
  · have a1 : (m+5) % 2 = 0 := by omega
    have a2 : (m+4) % 2 ≠ 0 := by omega
    have a3 : (m+3) % 2 = 0 := by omega
    have a4 : (m+2) % 2 ≠ 0 := by omega
    simp only [a1, a2, a3, a4, if_true, if_false] at h5 h4 h3 h2
    omega

lemma a0 : a 0 = 1 := by
  simp [a, digits, state]

lemma a1v : a 1 = 10 := by
  simp [a, digits, Finset.sum_range_succ, state1, Q1]

lemma a2v : a 2 = 101 := by have := ha 2 (by omega); norm_num at this; omega
lemma a3v : a 3 = 1100 := by have := ha 3 (by omega); norm_num at this; omega
lemma a4v : a 4 = 11101 := by have := ha 4 (by omega); norm_num at this; omega

end OMA.S_oeis_a290070

open OMA.S_oeis_a290070 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a290070.main := by
  refine ⟨?_, ?_⟩
  · have e : (PowerSeries.mk a) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
        PowerSeries.mk a - 10 * (PowerSeries.mk a * X) - PowerSeries.mk a * X ^ 2
          + 10 * (PowerSeries.mk a * X ^ 3) := by ring
    have c10 : (10:ℤ⟦X⟧) = C 10 := by simp
    have c90 : (90:ℤ⟦X⟧) = C 90 := by simp
    have c100 : (100:ℤ⟦X⟧) = C 100 := by simp
    rw [e, c90, c100, c10]
    ext n
    simp only [map_add, map_sub, coeff_mk]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X_pow, coeff_C]
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> simp [a0, a1v, a2v, a3v, a4v]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n-5, by omega⟩
      have := hrec m
      simp
      omega
  · intro n hn
    exact ⟨by obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n-5, by omega⟩; simpa using hrec m, hrow n (by omega)⟩
