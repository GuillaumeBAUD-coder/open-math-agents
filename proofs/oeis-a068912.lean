import OMAStatements.S_oeis_a068912
import Mathlib

/-!
# OEIS A068912

Walks of length `n` with steps `±1` that stay inside `[-3, 3]`.
The endpoint after an even number of steps lies in `{-2, 0, 2}`, and both one-step
extensions of any such walk remain inside the interval, so `a (2k+1) = 2 * a (2k)`.
The even subsequence satisfies `a (2(k+2)) = 4 * a (2(k+1)) - 2 * a (2k)`, with
characteristic roots `2 + √2` and `2 - √2`. Luschny's expression exceeds `a n` by a
positive amount strictly less than `1`.
-/

open OMA.S_oeis_a068912
open scoped Classical

namespace OMA.A068912Aux

/-- Reflect a walk by swapping `+1` and `-1`. -/
def flip {n : ℕ} (w : Fin n → Bool) : Fin n → Bool :=
  fun i => !(w i)

lemma step_not (b : Bool) : step (!b) = -step b := by
  cases b <;> simp [step]

lemma flip_flip {n : ℕ} (w : Fin n → Bool) : flip (flip w) = w := by
  ext i
  simp [flip]

def flipEquiv (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

lemma partialSum_flip {n : ℕ} (w : Fin n → Bool) (k : ℕ) :
    partialSum (flip w) k = -partialSum w k := by
  unfold partialSum flip
  simp_rw [step_not, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases h : j.val < k
  · simp [h]
  · simp [h]

lemma stays_flip {n : ℕ} (w : Fin n → Bool) : stays (flip w) ↔ stays w := by
  constructor
  · intro h k
    have hk := h k
    rw [partialSum_flip] at hk
    constructor <;> linarith
  · intro h k
    rw [partialSum_flip]
    have hk := h k
    constructor <;> linarith

/-- Number of valid walks of length `n` that end at `s`. -/
def count (n : ℕ) (s : ℤ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => stays w ∧ partialSum w n = s).card

lemma count_neg (n : ℕ) (s : ℤ) : count n (-s) = count n s := by
  classical
  let sneg := Finset.univ.filter fun w : Fin n → Bool => stays w ∧ partialSum w n = -s
  let spos := Finset.univ.filter fun w : Fin n → Bool => stays w ∧ partialSum w n = s
  have h := Finset.card_equiv (flipEquiv n) (s := sneg) (t := spos) ?_
  · simpa [count, sneg, spos] using h
  · intro w
    simp only [sneg, spos, flipEquiv, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hw, hend⟩
      refine ⟨(stays_flip w).mpr hw, ?_⟩
      rw [partialSum_flip, hend]
      ring
    · rintro ⟨hw, hend⟩
      refine ⟨(stays_flip w).mp hw, ?_⟩
      rw [partialSum_flip] at hend
      exact neg_eq_iff_eq_neg.mp hend

lemma partialSum_snoc_of_le {n : ℕ} (w : Fin n → Bool) (b : Bool) {k : ℕ} (hk : k ≤ n) :
    partialSum (Fin.snoc w b) k = partialSum w k := by
  unfold partialSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hnk : ¬n < k := Nat.not_lt.mpr hk
  rw [if_neg hnk, add_zero]

lemma partialSum_full {n : ℕ} (w : Fin n → Bool) :
    partialSum w n = ∑ j : Fin n, step (w j) := by
  unfold partialSum
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [j.isLt]

lemma partialSum_snoc_full {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    partialSum (Fin.snoc w b) (n + 1) = partialSum w n + step b := by
  unfold partialSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hlast : n < n + 1 := Nat.lt_succ_self n
  rw [if_pos hlast]
  have hlt : ∀ i : Fin n, i.val < n + 1 := fun i => Nat.lt_succ_of_lt i.isLt
  simp only [hlt, ite_true]
  refine congrArg (fun t => t + step b) ?_
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [j.isLt]

lemma stays_snoc {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    stays (Fin.snoc w b) ↔
      stays w ∧ -3 ≤ partialSum w n + step b ∧ partialSum w n + step b ≤ 3 := by
  constructor
  · intro h
    have hfull := h ⟨n + 1, by omega⟩
    rw [partialSum_snoc_full] at hfull
    refine ⟨?_, hfull.1, hfull.2⟩
    intro k
    have hk : k.val ≤ n := by
      have := k.isLt
      omega
    have hk' := h ⟨k.val, by omega⟩
    rwa [partialSum_snoc_of_le w b hk] at hk'
  · rintro ⟨hw, hlo, hhi⟩ k
    by_cases hk : k.val ≤ n
    · rw [partialSum_snoc_of_le w b hk]
      exact hw ⟨k.val, by omega⟩
    · have hk' : k.val = n + 1 := by
        have := k.isLt
        omega
      have hkf : k = ⟨n + 1, by omega⟩ := Fin.ext hk'
      rw [hkf, partialSum_snoc_full]
      exact ⟨hlo, hhi⟩

lemma partialSum_zero (w : Fin 0 → Bool) (k : ℕ) : partialSum w k = 0 := by
  simp [partialSum]

lemma stays_zero (w : Fin 0 → Bool) : stays w := by
  intro k
  simp [partialSum]

lemma count_zero_zero : count 0 0 = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun w : Fin 0 → Bool => stays w ∧ partialSum w 0 = 0) = Finset.univ := by
    ext w
    simp [stays_zero, partialSum_zero]
  unfold count
  rw [hfilter, Finset.card_univ]
  simp

lemma count_zero_ne {s : ℤ} (hs : s ≠ 0) : count 0 s = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero]
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty, true_and, iff_false]
  rintro ⟨_, hend⟩
  rw [partialSum_zero] at hend
  exact hs.symm hend

lemma count_out {n : ℕ} {s : ℤ} (hs : ¬(-3 ≤ s ∧ s ≤ 3)) : count n s = 0 := by
  classical
  unfold count
  rw [Finset.card_eq_zero]
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.notMem_empty, true_and, iff_false]
  rintro ⟨hw, hend⟩
  apply hs
  have hk := hw ⟨n, Nat.lt_succ_self n⟩
  rw [hend] at hk
  exact hk

lemma card_filter_sum {m : ℕ} (p : (Fin m → Bool) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ w : Fin m → Bool, if p w then (1 : ℕ) else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma count_succ_in (n : ℕ) {s : ℤ} (hs : -3 ≤ s ∧ s ≤ 3) :
    count (n + 1) s = count n (s - 1) + count n (s + 1) := by
  classical
  let e : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) := Fin.snocEquiv (fun _ => Bool)
  have he : ∀ b : Bool, ∀ w : Fin n → Bool, e (b, w) = Fin.snoc w b := by
    intro b w
    ext i
    simp [e, Fin.snocEquiv_apply]
  unfold count
  rw [card_filter_sum]
  have hchange :
      ∑ w : Fin (n + 1) → Bool, (if stays w ∧ partialSum w (n + 1) = s then 1 else 0) =
        ∑ p : Bool × (Fin n → Bool),
          if stays (e p) ∧ partialSum (e p) (n + 1) = s then 1 else 0 :=
    (Equiv.sum_comp e (fun w => if stays w ∧ partialSum w (n + 1) = s then 1 else 0)).symm
  rw [hchange, Fintype.sum_prod_type]
  have hiff : ∀ b : Bool, ∀ w : Fin n → Bool,
      (stays (Fin.snoc w b) ∧ partialSum (Fin.snoc w b) (n + 1) = s) ↔
        stays w ∧ partialSum w n = s - step b := by
    intro b w
    rw [stays_snoc, partialSum_snoc_full]
    constructor
    · rintro ⟨⟨hw, _hlo, _hhi⟩, hend⟩
      exact ⟨hw, eq_sub_iff_add_eq.mpr hend⟩
    · rintro ⟨hw, hend⟩
      have hend' : partialSum w n + step b = s := eq_sub_iff_add_eq.mp hend
      refine ⟨⟨hw, ?_, ?_⟩, hend'⟩
      · linarith [hs.1]
      · linarith [hs.2]
  simp_rw [he, hiff]
  rw [Fintype.sum_bool]
  have htrue : step true = 1 := by simp [step]
  have hfalse : step false = -1 := by simp [step]
  simp_rw [htrue, hfalse]
  have hsub : ∀ s : ℤ, s - (-1) = s + 1 := fun s => by omega
  simp_rw [hsub s]
  rw [← card_filter_sum (fun w : Fin n → Bool => stays w ∧ partialSum w n = s - 1),
    ← card_filter_sum (fun w : Fin n → Bool => stays w ∧ partialSum w n = s + 1)]

/-- Valid walks of length `n` ending at `0`, `1`, `2`, and `3`. -/
def u (n : ℕ) : ℕ := count n 0
def v (n : ℕ) : ℕ := count n 1
def w (n : ℕ) : ℕ := count n 2
def x (n : ℕ) : ℕ := count n 3

lemma u_succ (n : ℕ) : u (n + 1) = 2 * v n := by
  unfold u v
  rw [count_succ_in n (by omega : -3 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ 3)]
  have hneg : count n ((0 : ℤ) - 1) = count n 1 := by
    rw [show (0 : ℤ) - 1 = -1 by omega, count_neg]
  have hpos : count n ((0 : ℤ) + 1) = count n 1 := by
    rw [show (0 : ℤ) + 1 = 1 by omega]
  rw [hneg, hpos]
  omega

lemma v_succ (n : ℕ) : v (n + 1) = u n + w n := by
  unfold v u w
  rw [count_succ_in n (by omega : -3 ≤ (1 : ℤ) ∧ (1 : ℤ) ≤ 3)]
  have h0 : (1 : ℤ) - 1 = 0 := by omega
  have h2 : (1 : ℤ) + 1 = 2 := by omega
  rw [h0, h2]

lemma w_succ (n : ℕ) : w (n + 1) = v n + x n := by
  unfold w v x
  rw [count_succ_in n (by omega : -3 ≤ (2 : ℤ) ∧ (2 : ℤ) ≤ 3)]
  have h1 : (2 : ℤ) - 1 = 1 := by omega
  have h3 : (2 : ℤ) + 1 = 3 := by omega
  rw [h1, h3]

lemma x_succ (n : ℕ) : x (n + 1) = w n := by
  unfold x w
  rw [count_succ_in n (by omega : -3 ≤ (3 : ℤ) ∧ (3 : ℤ) ≤ 3)]
  have h2 : (3 : ℤ) - 1 = 2 := by omega
  have h4 : count n ((3 : ℤ) + 1) = 0 :=
    count_out (by omega : ¬(-3 ≤ ((3 : ℤ) + 1) ∧ ((3 : ℤ) + 1) ≤ 3))
  rw [h2, h4]
  omega

lemma endpoint_in {n : ℕ} {w : Fin n → Bool} (hw : stays w) :
    partialSum w n ∈ Finset.Icc (-3 : ℤ) 3 := by
  have h := hw ⟨n, Nat.lt_succ_self n⟩
  exact Finset.mem_Icc.mpr h

lemma count_as_fiber (n : ℕ) (s : ℤ) :
    ((Finset.univ.filter fun w : Fin n → Bool => stays w).filter
        fun w => partialSum w n = s).card =
      count n s := by
  classical
  unfold count
  rw [Finset.filter_filter]

lemma staying_in_range (n : ℕ) :
    ((Finset.univ.filter fun w : Fin n → Bool => stays w).filter
        fun w => partialSum w n ∈ Finset.Icc (-3 : ℤ) 3).card = a n := by
  classical
  unfold a
  apply congrArg Finset.card
  rw [Finset.filter_true_of_mem]
  intro wt hwt
  exact endpoint_in (Finset.mem_filter.mp hwt).2

lemma a_eq_sum (n : ℕ) : ∑ s ∈ Finset.Icc (-3 : ℤ) 3, count n s = a n := by
  classical
  rw [← staying_in_range n]
  rw [← Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter (fun wt : Fin n → Bool => stays wt))
      (Finset.Icc (-3 : ℤ) 3) (fun wt => partialSum wt n)]
  refine Finset.sum_congr rfl ?_
  intro s _
  exact (count_as_fiber n s).symm

lemma sum_shift (f : ℤ → ℕ) :
    ∑ i ∈ Finset.range 7, f ((-3 : ℤ) + i) =
      f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 + f 3 := by
  simp [Finset.sum_range_succ]

lemma sum_expand (n : ℕ) :
    ∑ s ∈ Finset.Icc (-3 : ℤ) 3, count n s =
      count n (-3) + count n (-2) + count n (-1) + count n 0 +
        count n 1 + count n 2 + count n 3 := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have hlen : ((3 : ℤ) + 1 - (-3)).toNat = 7 := by decide
  rw [hlen]
  exact sum_shift (count n)

lemma a_decomp (n : ℕ) : a n = u n + 2 * v n + 2 * w n + 2 * x n := by
  have hs := sum_expand n
  have hsum := a_eq_sum n
  rw [← hsum, hs, count_neg n 1, count_neg n 2, count_neg n 3]
  unfold u v w x
  omega

/-- Counts at `0, ±1, ±2, ±3`, started from the empty walk and stepped by `±1`. -/
def recState : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
      (2 * (recState n).2.1,
        (recState n).1 + (recState n).2.2.1,
        (recState n).2.1 + (recState n).2.2.2,
        (recState n).2.2.1)

lemma state_eq (n : ℕ) : (u n, v n, w n, x n) = recState n := by
  induction n with
  | zero =>
    unfold u v w x
    rw [count_zero_zero,
      count_zero_ne (by omega : (1 : ℤ) ≠ 0),
      count_zero_ne (by omega : (2 : ℤ) ≠ 0),
      count_zero_ne (by omega : (3 : ℤ) ≠ 0)]
    rfl
  | succ n ih =>
    rw [u_succ, v_succ, w_succ, x_succ]
    have hr : recState (n + 1) =
        (2 * (recState n).2.1, (recState n).1 + (recState n).2.2.1,
          (recState n).2.1 + (recState n).2.2.2, (recState n).2.2.1) := by
      rfl
    rw [hr]
    have hu : u n = (recState n).1 := congrArg Prod.fst ih
    have hv : v n = (recState n).2.1 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) ih
    have hw : w n = (recState n).2.2.1 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) ih
    have hx : x n = (recState n).2.2.2 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) ih
    rw [hu, hv, hw, hx]

lemma a_rec (n : ℕ) :
    a n = (recState n).1 + 2 * (recState n).2.1 +
      2 * (recState n).2.2.1 + 2 * (recState n).2.2.2 := by
  have h := state_eq n
  have hu : u n = (recState n).1 := congrArg Prod.fst h
  have hv : v n = (recState n).2.1 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) h
  have hw : w n = (recState n).2.2.1 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) h
  have hx : x n = (recState n).2.2.2 := congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2) h
  rw [a_decomp, hu, hv, hw, hx]

lemma a_from_rec (n u0 v0 w0 x0 val : ℕ) (ht : recState n = (u0, v0, w0, x0))
    (hv : u0 + 2 * v0 + 2 * w0 + 2 * x0 = val) : a n = val := by
  rw [a_rec, ht, hv]

lemma a_zero : a 0 = 1 := a_from_rec 0 1 0 0 0 1 rfl (by omega)
lemma a_one : a 1 = 2 := a_from_rec 1 0 1 0 0 2 rfl (by omega)
lemma a_two : a 2 = 4 := a_from_rec 2 2 0 1 0 4 rfl (by omega)
lemma a_three : a 3 = 8 := a_from_rec 3 0 3 0 1 8 rfl (by omega)
lemma a_four : a 4 = 14 := a_from_rec 4 6 0 4 0 14 rfl (by omega)
lemma a_five : a 5 = 28 := a_from_rec 5 0 10 0 4 28 rfl (by omega)
lemma a_six : a 6 = 48 := a_from_rec 6 20 0 14 0 48 rfl (by omega)
lemma a_seven : a 7 = 96 := a_from_rec 7 0 34 0 14 96 rfl (by omega)

lemma initial_data :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧
      a 4 = 14 ∧ a 5 = 28 ∧ a 6 = 48 ∧ a 7 = 96 :=
  ⟨a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven⟩

lemma even_zero (k : ℕ) : v (2 * k) = 0 ∧ x (2 * k) = 0 := by
  induction k with
  | zero =>
    constructor
    · simpa [v] using count_zero_ne (by omega : (1 : ℤ) ≠ 0)
    · simpa [x] using count_zero_ne (by omega : (3 : ℤ) ≠ 0)
  | succ k ih =>
    obtain ⟨hv, hx⟩ := ih
    have hu1 : u (2 * k + 1) = 0 := by
      rw [u_succ, hv]
    have hw1 : w (2 * k + 1) = 0 := by
      rw [w_succ, hv, hx]
    constructor
    · rw [show 2 * (k + 1) = 2 * k + 2 by omega, v_succ, hu1, hw1]
    · rw [show 2 * (k + 1) = 2 * k + 2 by omega, x_succ, hw1]

lemma a_even (k : ℕ) : a (2 * k) = u (2 * k) + 2 * w (2 * k) := by
  obtain ⟨hv, hx⟩ := even_zero k
  rw [a_decomp, hv, hx]
  omega

lemma u_two (n : ℕ) : u (n + 2) = 2 * (u n + w n) := by
  rw [u_succ, v_succ]

lemma w_two (n : ℕ) : w (n + 2) = u n + 2 * w n := by
  rw [w_succ, v_succ, x_succ]
  omega

lemma a_step (k : ℕ) : a (2 * (k + 1)) = 4 * u (2 * k) + 6 * w (2 * k) := by
  have he : a (2 * (k + 1)) = u (2 * (k + 1)) + 2 * w (2 * (k + 1)) := a_even (k + 1)
  have hu : u (2 * (k + 1)) = 2 * (u (2 * k) + w (2 * k)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact u_two (2 * k)
  have hw : w (2 * (k + 1)) = u (2 * k) + 2 * w (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact w_two (2 * k)
  rw [he, hu, hw]
  omega

lemma a_even_add (k : ℕ) :
    a (2 * (k + 2)) + 2 * a (2 * k) = 4 * a (2 * (k + 1)) := by
  have h0 : a (2 * k) = u (2 * k) + 2 * w (2 * k) := a_even k
  have h1 : a (2 * (k + 1)) = 4 * u (2 * k) + 6 * w (2 * k) := a_step k
  have h2 : a (2 * (k + 2)) = 4 * u (2 * (k + 1)) + 6 * w (2 * (k + 1)) := a_step (k + 1)
  have hu : u (2 * (k + 1)) = 2 * (u (2 * k) + w (2 * k)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact u_two (2 * k)
  have hw : w (2 * (k + 1)) = u (2 * k) + 2 * w (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact w_two (2 * k)
  rw [h0, h1, h2, hu, hw]
  omega

lemma a_even_rec_real (k : ℕ) :
    (a (2 * (k + 2)) : ℝ) = 4 * (a (2 * (k + 1)) : ℝ) - 2 * (a (2 * k) : ℝ) := by
  have h := a_even_add k
  have hcast := congrArg (fun t : ℕ => (t : ℝ)) h
  push_cast at hcast
  linarith

lemma a_double (k : ℕ) : a (2 * k + 1) = 2 * a (2 * k) := by
  obtain ⟨hv0, hx0⟩ := even_zero k
  have hu := u_succ (2 * k)
  have hv := v_succ (2 * k)
  have hw := w_succ (2 * k)
  have hx := x_succ (2 * k)
  have ha0 := a_even k
  have ha1 := a_decomp (2 * k + 1)
  rw [hv0] at hu
  rw [hv0, hx0] at hw
  omega

noncomputable def α : ℝ := 1 + r
noncomputable def β : ℝ := 2 - Real.sqrt 2

lemma sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hs : Real.sqrt 2 < Real.sqrt (2 ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (2 : ℝ) < 2 ^ 2)
  rw [Real.sqrt_sq h2] at hs
  exact hs

lemma alpha_pos : 0 < α := by
  unfold α r
  positivity

lemma beta_pos : 0 < β := by
  unfold β
  linarith [sqrt_two_lt_two]

lemma beta_lt_one : β < 1 := by
  unfold β
  linarith [sqrt_two_gt_one]

lemma alpha_sq : α ^ 2 = 4 * α - 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hα : α = 2 + Real.sqrt 2 := by
    unfold α r
    ring
  rw [hα]
  ring_nf
  rw [hs]
  ring

lemma beta_sq : β ^ 2 = 4 * β - 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold β
  ring_nf
  rw [hs]
  ring

lemma pow_char {z : ℝ} (hz : z ^ 2 = 4 * z - 2) (k : ℕ) :
    z ^ (k + 2) = 4 * z ^ (k + 1) - 2 * z ^ k := by
  calc
    z ^ (k + 2) = z ^ k * z ^ 2 := by rw [pow_add]
    _ = z ^ k * (4 * z - 2) := by rw [hz]
    _ = 4 * (z ^ k * z) - 2 * z ^ k := by ring
    _ = 4 * z ^ (k + 1) - 2 * z ^ k := by rw [← pow_succ]

noncomputable def closed (k : ℕ) : ℝ :=
  (r * α ^ k + (1 - Real.sqrt 2) * β ^ k) / 2

lemma closed_zero : closed 0 = 1 := by
  unfold closed r
  simp [pow_zero]

lemma closed_one : closed 1 = 4 := by
  unfold closed α β r
  rw [pow_one, pow_one]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hα : 1 + (1 + Real.sqrt 2) = 2 + Real.sqrt 2 := by ring
  have hprod :
      (1 + Real.sqrt 2) * (2 + Real.sqrt 2) +
          (1 - Real.sqrt 2) * (2 - Real.sqrt 2) = 8 := by
    ring_nf
    rw [hs]
    ring
  rw [hα, hprod]
  ring

lemma closed_rec (k : ℕ) : closed (k + 2) = 4 * closed (k + 1) - 2 * closed k := by
  unfold closed
  rw [pow_char alpha_sq k, pow_char beta_sq k]
  ring

lemma closed_eq (k : ℕ) : closed k = (a (2 * k) : ℝ) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [closed_zero, a_zero]
    norm_num
  | one =>
    rw [closed_one, a_two]
    norm_num
  | more k ih0 ih1 =>
    rw [closed_rec, ih0, ih1]
    exact (a_even_rec_real k).symm

lemma neg_one_even (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

lemma neg_one_odd (k : ℕ) : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
  rw [pow_succ, neg_one_even, one_mul]

lemma luschny_even (k : ℕ) : luschny (2 * k) = α ^ k * r / 2 := by
  unfold luschny
  have hdiv : ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) := by
    push_cast
    ring
  have hpow : (1 + r) ^ (((2 * k : ℕ) : ℝ) / 2) = α ^ k := by
    rw [hdiv, show (1 + r) = α by rfl, Real.rpow_natCast]
  have hsign := neg_one_even k
  set s : ℝ := Real.sqrt (2 * (1 + r))
  rw [hpow, hsign]
  have : r + s + 1 * (r - s) = 2 * r := by ring
  rw [this]
  ring

lemma alpha_sqrt_mul : Real.sqrt α * Real.sqrt (2 * α) = α * Real.sqrt 2 := by
  have hα : 0 ≤ α := alpha_pos.le
  calc
    Real.sqrt α * Real.sqrt (2 * α) = Real.sqrt (α * (2 * α)) := by
      rw [← Real.sqrt_mul hα]
    _ = Real.sqrt (2 * α ^ 2) := by
      congr 1
      ring
    _ = Real.sqrt 2 * Real.sqrt (α ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * α := by
      rw [Real.sqrt_sq hα]
    _ = α * Real.sqrt 2 := by ring

lemma alpha_sqrt_div : α * Real.sqrt 2 / 2 = r := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hα : α = 2 + Real.sqrt 2 := by
    unfold α r
    ring
  rw [hα]
  unfold r
  have hmul : (2 + Real.sqrt 2) * Real.sqrt 2 = 2 * Real.sqrt 2 + 2 := by
    ring_nf
    rw [hs]
    ring
  rw [hmul]
  ring

lemma luschny_odd (k : ℕ) : luschny (2 * k + 1) = r * α ^ k := by
  have hαpos := alpha_pos
  unfold luschny
  set s : ℝ := Real.sqrt (2 * (1 + r)) with hsdef
  have hs : s = Real.sqrt (2 * α) := by
    simp [hsdef, α]
  have hexp : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hpow : (1 + r) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) = α ^ k * Real.sqrt α := by
    rw [hexp, show (1 + r) = α by rfl, Real.rpow_add hαpos, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
  have hsign := neg_one_odd k
  have hpar : r + s + (-1 : ℝ) ^ (2 * k + 1) * (r - s) = 2 * s := by
    rw [hsign]
    ring
  rw [hpow, hpar, hs]
  calc
    (α ^ k * Real.sqrt α * (2 * Real.sqrt (2 * α))) / 4
        = (α ^ k * (Real.sqrt α * Real.sqrt (2 * α)) * 2) / 4 := by ring
    _ = (α ^ k * (α * Real.sqrt 2) * 2) / 4 := by rw [alpha_sqrt_mul]
    _ = α ^ k * (α * Real.sqrt 2 / 2) := by ring
    _ = α ^ k * r := by rw [alpha_sqrt_div]
    _ = r * α ^ k := by ring

lemma diff_even (k : ℕ) :
    luschny (2 * k) - (a (2 * k) : ℝ) = (Real.sqrt 2 - 1) * β ^ k / 2 := by
  rw [luschny_even, ← closed_eq]
  unfold closed r
  ring

lemma diff_odd (k : ℕ) :
    luschny (2 * k + 1) - (a (2 * k + 1) : ℝ) = (Real.sqrt 2 - 1) * β ^ k := by
  rw [luschny_odd, a_double]
  push_cast
  rw [← closed_eq]
  unfold closed r
  ring

lemma beta_pow_pos (k : ℕ) : 0 < β ^ k :=
  pow_pos beta_pos k

lemma beta_pow_le (k : ℕ) : β ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [beta_pos.le, beta_lt_one.le, ih]

lemma diff_even_bounds (k : ℕ) :
    0 < luschny (2 * k) - (a (2 * k) : ℝ) ∧ luschny (2 * k) - (a (2 * k) : ℝ) < 1 := by
  rw [diff_even]
  constructor
  · apply div_pos
    · exact mul_pos (by linarith [sqrt_two_gt_one]) (beta_pow_pos k)
    · norm_num
  · have hβ : β ^ k ≤ 1 := beta_pow_le k
    have hc : 0 ≤ (Real.sqrt 2 - 1) / 2 := by linarith [sqrt_two_gt_one]
    have hle : (Real.sqrt 2 - 1) * β ^ k / 2 ≤ (Real.sqrt 2 - 1) / 2 := by
      have hmul : (Real.sqrt 2 - 1) * β ^ k ≤ Real.sqrt 2 - 1 := by
        nlinarith [hβ, sqrt_two_gt_one]
      linarith
    have hlt : (Real.sqrt 2 - 1) / 2 < 1 := by linarith [sqrt_two_lt_two]
    linarith

lemma diff_odd_bounds (k : ℕ) :
    0 < luschny (2 * k + 1) - (a (2 * k + 1) : ℝ) ∧
      luschny (2 * k + 1) - (a (2 * k + 1) : ℝ) < 1 := by
  rw [diff_odd]
  constructor
  · exact mul_pos (by linarith [sqrt_two_gt_one]) (beta_pow_pos k)
  · have hβ : β ^ k ≤ 1 := beta_pow_le k
    have hle : (Real.sqrt 2 - 1) * β ^ k ≤ Real.sqrt 2 - 1 := by
      nlinarith [hβ, sqrt_two_gt_one]
    have hlt : Real.sqrt 2 - 1 < 1 := by linarith [sqrt_two_lt_two]
    linarith

lemma floor_of_sub {n : ℕ} (h0 : 0 < luschny n - (a n : ℝ))
    (h1 : luschny n - (a n : ℝ) < 1) : (a n : ℤ) = ⌊luschny n⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

lemma floor_even (k : ℕ) : (a (2 * k) : ℤ) = ⌊luschny (2 * k)⌋ :=
  floor_of_sub (diff_even_bounds k).1 (diff_even_bounds k).2

lemma floor_odd (k : ℕ) : (a (2 * k + 1) : ℤ) = ⌊luschny (2 * k + 1)⌋ :=
  floor_of_sub (diff_odd_bounds k).1 (diff_odd_bounds k).2

lemma floor_main (n : ℕ) : (a n : ℤ) = ⌊luschny n⌋ := by
  by_cases h : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by
      have hdiv := Nat.div_add_mod n 2
      omega
    rw [hn]
    exact floor_even (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      have hdiv := Nat.div_add_mod n 2
      omega
    rw [hn]
    exact floor_odd (n / 2)

end OMA.A068912Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a068912.main :=
  OMA.A068912Aux.floor_main
