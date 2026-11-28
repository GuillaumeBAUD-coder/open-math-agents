import OMAStatements.S_mo_440995
import Mathlib

namespace OMA.P_mo_440995

open Finset

lemma ind_eq (p a : ℕ) (hp : 0 < p) (ha : a < p) :
    ((if (a + 1) ^ 2 % p < a ^ 2 % p then 1 else 0 : ℤ)) =
      (((a + 1) ^ 2 / p : ℕ) : ℤ) - ((a ^ 2 / p : ℕ) : ℤ) -
        (if p ≤ 2 * a + 1 then 1 else 0) := by
  have e1 := Nat.div_add_mod (a ^ 2) p
  have e2 := Nat.div_add_mod ((a + 1) ^ 2) p
  have r1 := Nat.mod_lt (a ^ 2) hp
  have r2 := Nat.mod_lt ((a + 1) ^ 2) hp
  set q1 := a ^ 2 / p
  set q2 := (a + 1) ^ 2 / p
  set s1 := a ^ 2 % p
  set s2 := (a + 1) ^ 2 % p
  have e1' : (p : ℤ) * q1 + s1 = (a : ℤ) ^ 2 := by exact_mod_cast e1
  have e2' : (p : ℤ) * q2 + s2 = ((a : ℤ) + 1) ^ 2 := by exact_mod_cast e2
  have key : (p : ℤ) * ((q2 : ℤ) - q1) = 2 * a + 1 + s1 - s2 := by
    linear_combination e2' - e1'
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have r1' : (s1 : ℤ) < p := by exact_mod_cast r1
  have r2' : (s2 : ℤ) < p := by exact_mod_cast r2
  have ha' : (a : ℤ) < p := by exact_mod_cast ha
  have s1n : (0 : ℤ) ≤ s1 := by positivity
  have s2n : (0 : ℤ) ≤ s2 := by positivity
  have an : (0 : ℤ) ≤ a := by positivity
  generalize hQ : (q2 : ℤ) - q1 = Q at key ⊢
  split_ifs with h1 h2 h2
  · have h1' : (s2 : ℤ) < s1 := by exact_mod_cast h1
    have h2' : (p : ℤ) ≤ 2 * a + 1 := by exact_mod_cast h2
    have lo : 1 < Q := by
      by_contra h; rw [not_lt] at h; nlinarith
    have hi : Q < 3 := by
      by_contra h; rw [not_lt] at h; nlinarith
    omega
  · have h1' : (s2 : ℤ) < s1 := by exact_mod_cast h1
    have h2' : 2 * (a : ℤ) + 1 < p := by
      have : 2 * a + 1 < p := by omega
      exact_mod_cast this
    have lo : 0 < Q := by
      by_contra h; rw [not_lt] at h; nlinarith
    have hi : Q < 2 := by
      by_contra h; rw [not_lt] at h; nlinarith
    omega
  · have h1' : (s1 : ℤ) ≤ s2 := by
      have : s1 ≤ s2 := by omega
      exact_mod_cast this
    have h2' : (p : ℤ) ≤ 2 * a + 1 := by exact_mod_cast h2
    have lo : 0 < Q := by
      by_contra h; rw [not_lt] at h; nlinarith
    have hi : Q < 2 := by
      by_contra h; rw [not_lt] at h; nlinarith
    omega
  · have h1' : (s1 : ℤ) ≤ s2 := by
      have : s1 ≤ s2 := by omega
      exact_mod_cast this
    have h2' : 2 * (a : ℤ) + 1 < p := by
      have : 2 * a + 1 < p := by omega
      exact_mod_cast this
    have lo : -1 < Q := by
      by_contra h; rw [not_lt] at h; nlinarith
    have hi : Q < 1 := by
      by_contra h; rw [not_lt] at h; nlinarith
    omega

lemma abel (f : ℕ → ℤ) (n : ℕ) :
    ∑ a ∈ range n, (a : ℤ) * (f (a + 1) - f a) = n * f n - ∑ a ∈ range n, f (a + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; push_cast; ring

lemma sq_sum (n : ℕ) :
    6 * ∑ a ∈ range n, ((a : ℤ) + 1) ^ 2 = (n : ℤ) * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

lemma lin_sum (c n : ℕ) :
    2 * ∑ k ∈ range n, ((c : ℤ) + k) = 2 * (n : ℤ) * (c : ℤ) + (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

lemma half_sum (p m : ℕ) (hm : p = 2 * m + 1) :
    8 * ∑ a ∈ range p, (if p ≤ 2 * a + 1 then (a : ℤ) else 0) = 3 * ((p : ℤ) ^ 2 - 1) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ p by omega)]
  have h0 : ∑ a ∈ range m, (if p ≤ 2 * a + 1 then (a : ℤ) else 0) = 0 := by
    apply sum_eq_zero
    intro a ha
    rw [mem_range] at ha
    rw [if_neg (by omega)]
  have h1 : ∑ a ∈ Ico m p, (if p ≤ 2 * a + 1 then (a : ℤ) else 0) =
      ∑ a ∈ Ico m p, (a : ℤ) := by
    apply sum_congr rfl
    intro a ha
    rw [mem_Ico] at ha
    rw [if_pos (by omega)]
  rw [h0, h1, zero_add, Finset.sum_Ico_eq_sum_range]
  have h2 := lin_sum m (p - m)
  push_cast at h2 ⊢
  have hpm : ((p - m : ℕ) : ℤ) = m + 1 := by omega
  rw [hpm] at h2
  rw [hm] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination 4 * h2

lemma R_eq (p : ℕ) [hp : Fact p.Prime] (h4 : p % 4 = 1) :
    2 * ∑ b ∈ range p, b ^ 2 % p = p * (p - 1) := by
  have hconv : ∑ b ∈ range p, b ^ 2 % p = ∑ x : ZMod p, (x ^ 2).val := by
    refine Finset.sum_bij' (fun b _ => (b : ZMod p)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intros; simp
    · intro x _; simp [ZMod.val_lt]
    · intro b hb; rw [mem_range] at hb; exact ZMod.val_cast_of_lt hb
    · intro x _; simp
    · intro b _; rw [← Nat.cast_pow, ZMod.val_natCast]
  obtain ⟨i, hi⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hbij : Function.Bijective (fun x : ZMod p => i * x) := mulLeft_bijective₀ i hi0
  have h2 : ∑ x : ZMod p, ((i * x) ^ 2).val = ∑ x : ZMod p, (x ^ 2).val :=
    Fintype.sum_bijective _ hbij _ _ (fun x => rfl)
  have h3 : ∀ x : ZMod p, ((i * x) ^ 2).val = (-(x ^ 2)).val := by
    intro x
    congr 1
    linear_combination (-(x ^ 2)) * hi
  have h5 : ∀ x : ZMod p, (x ^ 2).val + (-(x ^ 2)).val = if x = 0 then 0 else p := by
    intro x
    split_ifs with hx
    · subst hx; simp
    · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      rw [ZMod.neg_val, if_neg hx2]
      have := ZMod.val_lt (x ^ 2)
      omega
  have h6 : ∑ x : ZMod p, (if x = 0 then 0 else p) + p = p * p := by
    have hA : ∑ x : ZMod p, (if x = 0 then p else 0) = p := by simp
    have hC : ∀ x : ZMod p, (if x = 0 then 0 else p) + (if x = 0 then p else 0) = p := by
      intro x; split_ifs <;> simp
    have hB : ∑ x : ZMod p, ((if x = 0 then 0 else p) + (if x = 0 then p else 0)) = p * p := by
      simp only [hC, sum_const, card_univ, ZMod.card, smul_eq_mul]
    rw [Finset.sum_add_distrib, hA] at hB
    exact hB
  have h7 : ∑ x : ZMod p, (x ^ 2).val + ∑ x : ZMod p, (x ^ 2).val =
      ∑ x : ZMod p, ((x ^ 2).val + (-(x ^ 2)).val) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← h2]
    exact sum_congr rfl (fun x _ => h3 x)
  simp only [h5] at h7
  rw [hconv, Nat.mul_sub_one]
  omega

end OMA.P_mo_440995

open Finset in
theorem OMA.solution : type_of% @OMA.S_mo_440995.main := by
  intro p hp h4
  have := Fact.mk hp
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  unfold OMA.S_mo_440995.descentSet
  rw [Finset.sum_filter, Finset.sum_range_succ]
  have hlast : ¬ ((p + 1) ^ 2 % p < p ^ 2 % p) := by
    rw [show p ^ 2 % p = 0 by simp [sq]]
    exact Nat.not_lt_zero _
  rw [if_neg hlast, add_zero]
  -- integer form
  have hS : ((∑ x ∈ range p, if (x + 1) ^ 2 % p < x ^ 2 % p then x else 0 : ℕ) : ℤ) =
      ∑ a ∈ range p, (a : ℤ) * (if (a + 1) ^ 2 % p < a ^ 2 % p then 1 else 0) := by
    push_cast
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hS2 : ∑ a ∈ range p, (a : ℤ) * (if (a + 1) ^ 2 % p < a ^ 2 % p then 1 else 0) =
      ∑ a ∈ range p, (a : ℤ) * ((((a + 1) ^ 2 / p : ℕ) : ℤ) - ((a ^ 2 / p : ℕ) : ℤ)) -
        ∑ a ∈ range p, (if p ≤ 2 * a + 1 then (a : ℤ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    rw [OMA.P_mo_440995.ind_eq p a hp0 ha]
    split_ifs <;> ring
  have hT1 := OMA.P_mo_440995.abel (fun a => ((a ^ 2 / p : ℕ) : ℤ)) p
  have hfp : ((p ^ 2 / p : ℕ) : ℤ) = p := by
    rw [sq, Nat.mul_div_cancel _ hp0]
  rw [hfp] at hT1
  have hQ : (p : ℤ) * ∑ a ∈ range p, (((a + 1) ^ 2 / p : ℕ) : ℤ) =
      ∑ a ∈ range p, ((a : ℤ) + 1) ^ 2 - ∑ a ∈ range p, (((a + 1) ^ 2 % p : ℕ) : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    have := Nat.div_add_mod ((a + 1) ^ 2) p
    have h' : (p : ℤ) * (((a + 1) ^ 2 / p : ℕ) : ℤ) + (((a + 1) ^ 2 % p : ℕ) : ℤ) =
        ((a : ℤ) + 1) ^ 2 := by exact_mod_cast this
    linarith
  have hRshift : ∑ a ∈ range p, (((a + 1) ^ 2 % p : ℕ) : ℤ) =
      ((∑ b ∈ range p, b ^ 2 % p : ℕ) : ℤ) := by
    push_cast
    have hp2 : p ^ 2 % p = 0 := by simp [sq]
    have e1 : ∑ b ∈ range (p + 1), ((b ^ 2 % p : ℕ) : ℤ) =
        ∑ a ∈ range p, (((a + 1) ^ 2 % p : ℕ) : ℤ) + ((0 ^ 2 % p : ℕ) : ℤ) :=
      Finset.sum_range_succ' (fun b => ((b ^ 2 % p : ℕ) : ℤ)) p
    have e2 : ∑ b ∈ range (p + 1), ((b ^ 2 % p : ℕ) : ℤ) =
        ∑ b ∈ range p, ((b ^ 2 % p : ℕ) : ℤ) + ((p ^ 2 % p : ℕ) : ℤ) :=
      Finset.sum_range_succ (fun b => ((b ^ 2 % p : ℕ) : ℤ)) p
    rw [hp2] at e2
    have h00 : ((0 ^ 2 % p : ℕ) : ℤ) = 0 := by simp
    rw [h00] at e1
    push_cast at e1 e2
    linarith
  have hR := OMA.P_mo_440995.R_eq p h4
  have hR' : 2 * ((∑ b ∈ range p, b ^ 2 % p : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
    have : ((2 * ∑ b ∈ range p, b ^ 2 % p : ℕ) : ℤ) = ((p * (p - 1) : ℕ) : ℤ) := by rw [hR]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_ofNat,
      Nat.cast_one] at this
    exact this
  have hsq := OMA.P_mo_440995.sq_sum p
  have hT2 := OMA.P_mo_440995.half_sum p (p / 2) (by omega)
  have hint : (p : ℤ) * (24 * ((∑ x ∈ range p,
      if (x + 1) ^ 2 % p < x ^ 2 % p then x else 0 : ℕ) : ℤ) - 7 * ((p : ℤ) ^ 2 - 1)) = 0 := by
    rw [hS, hS2, hT1]
    linear_combination (-24) * hQ + 12 * hR' - 3 * (p : ℤ) * hT2 - 4 * hsq
      + 24 * hRshift
  have hp0' : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hint2 := (mul_eq_zero.mp hint).resolve_left hp0'
  have hq : (24 : ℚ) * ((∑ x ∈ range p,
      if (x + 1) ^ 2 % p < x ^ 2 % p then x else 0 : ℕ) : ℚ) = 7 * ((p : ℚ) ^ 2 - 1) := by
    have h' : (24 : ℤ) * ((∑ x ∈ range p,
        if (x + 1) ^ 2 % p < x ^ 2 % p then x else 0 : ℕ) : ℤ) = 7 * ((p : ℤ) ^ 2 - 1) := by
      linarith
    exact_mod_cast h'
  linarith
