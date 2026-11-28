import OMAStatements.S_oeis_a201553
import Mathlib

/-!
Proof of Barker's g.f. and recurrence for A201553. The number of k-tuples in -n..n with sum s is
obtained by iterating a window sum (c_succ), which turns the binomial counts Q into shifted
differences (T_iter); this gives a(n) = C(6n+5,5) - 6 C(4n+4,5) + 15 C(2n+3,5), a polynomial of
degree 5 in n, from which the recurrence and the g.f. follow.
-/

namespace A201553P

open Finset

/-- Number of k-tuples with entries in I and sum s. -/
noncomputable def c (k : ℕ) (I : Finset ℤ) (s : ℤ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k => I).filter fun x => ∑ i, x i = s).card

theorem c_zero (I : Finset ℤ) (s : ℤ) : c 0 I s = if s = 0 then 1 else 0 := by
  unfold c
  by_cases h : s = 0
  · subst h; simp
  · rw [if_neg h]
    simp [eq_comm, h]

theorem c_succ (k : ℕ) (I : Finset ℤ) (s : ℤ) : c (k + 1) I s = ∑ v ∈ I, c k I (s - v) := by
  unfold c
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (k + 1) → ℤ => x 0) (t := I)]
  · refine Finset.sum_congr rfl fun v hv => ?_
    refine Finset.card_nbij' (fun x => Fin.tail x) (fun y => Fin.cons v y) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
      obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
      refine ⟨fun i => hx1 _, ?_⟩
      rw [Fin.sum_univ_succ] at hx2
      simp only [Fin.tail]
      linarith
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨⟨?_, ?_⟩, by simp⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hv
        · simpa using hy1 j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        linarith
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      rw [← hx.2]
      exact Fin.cons_self_tail x
    · intro y hy
      exact Fin.tail_cons (α := fun _ => ℤ) v y
  · intro x hx
    exact Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1 0

/-- Shifted difference. -/
def E (L : ℤ) (g : ℤ → ℤ) : ℤ → ℤ := fun m => g m - g (m - L)

/-- Window sum. -/
def T (L : ℕ) (g : ℤ → ℤ) : ℤ → ℤ := fun m => ∑ x ∈ range L, g (m - x)

/-- Number of (k+1)-tuples of nonnegative integers with sum m. -/
def Q (k : ℕ) (m : ℤ) : ℤ := if 0 ≤ m then ((m.toNat + k).choose k : ℤ) else 0

theorem T_E (L : ℕ) (M : ℤ) (g : ℤ → ℤ) : T L (E M g) = E M (T L g) := by
  funext m
  simp only [T, E, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sub_right_comm]

theorem E_E (a b : ℤ) (g : ℤ → ℤ) : E a (E b g) = E b (E a g) := by
  funext m
  simp only [E]
  rw [sub_right_comm m a b]
  ring

theorem T_D (L : ℕ) (g : ℤ → ℤ) : T L (E 1 g) = E L g := by
  funext m
  simp only [T, E]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [sub_sub m (L : ℤ) 1]
    ring

theorem T_Eiter (L : ℕ) (M : ℤ) (k : ℕ) (g : ℤ → ℤ) :
    T L ((E M)^[k] g) = (E M)^[k] (T L g) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T_E, ih]

theorem E_Eiter (a b : ℤ) (k : ℕ) (g : ℤ → ℤ) :
    E a ((E b)^[k] g) = (E b)^[k] (E a g) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E_E, ih]

theorem Q_pascal (k : ℕ) : Q k = E 1 (Q (k + 1)) := by
  funext m
  simp only [E, Q]
  rcases lt_trichotomy m 0 with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · subst h; simp
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = (t : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((t : ℤ) + 1).toNat = t + 1 := by omega
    have h2 : ((t : ℤ) + 1 - 1).toNat = t := by omega
    rw [h1, h2]
    have := Nat.choose_succ_succ (t + k) k
    have e1 : t + 1 + k = t + k + 1 := by ring
    have e2 : t + 1 + (k + 1) = t + k + 1 + 1 := by ring
    have e3 : t + (k + 1) = t + k + 1 := by ring
    rw [e1, e2, e3, Nat.choose_succ_succ (t + k + 1) k]
    push_cast
    ring

theorem delta_eq : (fun m : ℤ => if m = 0 then (1 : ℤ) else 0) = E 1 (Q 0) := by
  funext m
  simp only [E, Q, Nat.choose_zero_right, Nat.cast_one]
  rcases lt_trichotomy m 0 with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · subst h; simp
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; simp

theorem T_iter (L k : ℕ) : (T L)^[k] (E 1 (Q 0)) = (E L)^[k] (E 1 (Q k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, T_Eiter, Function.iterate_succ_apply',
      Q_pascal k, T_D, E_Eiter, ← Q_pascal k]

theorem sum_Icc_shift (n : ℕ) (f : ℤ → ℤ) :
    ∑ v ∈ Icc (-(n : ℤ)) n, f v = ∑ y ∈ range (2 * n + 1), f ((y : ℤ) - n) := by
  have : Icc (-(n : ℤ)) n = (range (2 * n + 1)).image (fun y : ℕ => (y : ℤ) - n) := by
    ext v
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro h
      exact ⟨(v + n).toNat, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  rw [this, Finset.sum_image]
  intro x _ y _ h
  simpa using h

theorem c_eq (n k : ℕ) (s : ℤ) :
    (c k (Icc (-(n : ℤ)) n) s : ℤ) = (T (2 * n + 1))^[k] (E 1 (Q 0)) (s + k * n) := by
  induction k generalizing s with
  | zero =>
    rw [c_zero, ← delta_eq]
    simp
  | succ k ih =>
    rw [c_succ, Function.iterate_succ_apply']
    push_cast
    rw [sum_Icc_shift]
    simp only [T]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ih]
    apply congrArg
    ring

theorem E6 (L : ℤ) (g : ℤ → ℤ) (m : ℤ) :
    (E L)^[6] g m = g m - 6 * g (m - L) + 15 * g (m - 2 * L) - 20 * g (m - 3 * L)
      + 15 * g (m - 4 * L) - 6 * g (m - 5 * L) + g (m - 6 * L) := by
  have h : ∀ j : ℤ, ∀ x : ℤ, x - j * L - L = x - (j + 1) * L := fun j x => by ring
  have h1 : m - L = m - 1 * L := by ring
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, E]
  rw [h1]
  simp only [h]
  norm_num
  ring

theorem choose5 (m : ℕ) :
    (120 : ℤ) * (m.choose 5 : ℤ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> simp [Nat.choose]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' h
    have := Nat.descFactorial_eq_factorial_mul_choose (t + 5) 5
    simp only [Nat.descFactorial] at this
    have h2 : (Nat.factorial 5 : ℤ) = 120 := by norm_num [Nat.factorial]
    rw [← h2]
    rw [← Nat.cast_mul, ← this]
    push_cast
    simp
    ring

theorem Qv (m : ℤ) (r : ℕ) (h : m + 5 = r) : Q 5 m = (r.choose 5 : ℤ) := by
  unfold Q
  split_ifs with h0
  · have : m.toNat + 5 = r := by omega
    rw [this]
  · have : r < 5 := by omega
    rw [Nat.choose_eq_zero_of_lt this]
    rfl

theorem Qneg (m : ℤ) (h : m < 0) : Q 5 m = 0 := by
  unfold Q
  rw [if_neg (by omega)]

theorem final (n : ℕ) (m L : ℤ) (hm : m = 6 * n) (hL : L = 2 * n + 1) :
    (E L)^[6] (Q 5) m = ((6 * n + 5).choose 5 : ℤ) - 6 * ((4 * n + 4).choose 5 : ℤ)
      + 15 * ((2 * n + 3).choose 5 : ℤ) := by
  subst hm hL
  rw [E6, Qv (6 * n) (6 * n + 5) (by push_cast; ring),
    Qv (6 * n - (2 * n + 1)) (4 * n + 4) (by push_cast; ring),
    Qv (6 * n - 2 * (2 * n + 1)) (2 * n + 3) (by push_cast; ring),
    Qneg (6 * n - 3 * (2 * n + 1)) (by omega), Qneg (6 * n - 4 * (2 * n + 1)) (by omega),
    Qneg (6 * n - 5 * (2 * n + 1)) (by omega), Qneg (6 * n - 6 * (2 * n + 1)) (by omega)]
  ring

open OMA.S_oeis_a201553 in
theorem a_eq (n : ℕ) :
    (a n : ℤ) = ((6 * n + 5).choose 5 : ℤ) - 6 * ((4 * n + 4).choose 5 : ℤ)
      + 15 * ((2 * n + 3).choose 5 : ℤ) := by
  have h0 : a n = c 6 (Icc (-(n : ℤ)) n) 0 := rfl
  rw [h0, c_eq, T_iter, ← Q_pascal]
  exact final n _ _ (by push_cast; ring) (by push_cast; ring)

open OMA.S_oeis_a201553 in
theorem a_poly (n : ℕ) :
    (120 : ℤ) * (a n : ℤ) = (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
      - 6 * ((4 * n + 4) * (4 * n + 3) * (4 * n + 2) * (4 * n + 1) * (4 * n))
      + 15 * ((2 * n + 3) * (2 * n + 2) * (2 * n + 1) * (2 * n) * (2 * n - 1)) := by
  rw [a_eq]
  have h1 := choose5 (6 * n + 5)
  have h2 := choose5 (4 * n + 4)
  have h3 := choose5 (2 * n + 3)
  push_cast at h1 h2 h3
  linear_combination h1 - 6 * h2 + 15 * h3

open OMA.S_oeis_a201553 in
theorem rec (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
      + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 6 := ⟨n - 6, by omega⟩
  have e1 : t + 6 - 1 = t + 5 := by omega
  have e2 : t + 6 - 2 = t + 4 := by omega
  have e3 : t + 6 - 3 = t + 3 := by omega
  have e4 : t + 6 - 4 = t + 2 := by omega
  have e5 : t + 6 - 5 = t + 1 := by omega
  have e6 : t + 6 - 6 = t := by omega
  rw [e1, e2, e3, e4, e5, e6]
  have h0 := a_poly t
  have h1 := a_poly (t + 1)
  have h2 := a_poly (t + 2)
  have h3 := a_poly (t + 3)
  have h4 := a_poly (t + 4)
  have h5 := a_poly (t + 5)
  have h6 := a_poly (t + 6)
  push_cast at h0 h1 h2 h3 h4 h5 h6
  have : (120 : ℤ) * (a (t + 6) : ℤ) = 120 * (6 * a (t + 5) - 15 * a (t + 4) + 20 * a (t + 3)
      - 15 * a (t + 2) + 6 * a (t + 1) - a t) := by
    linear_combination h6 - 6 * h5 + 15 * h4 - 20 * h3 + 15 * h2 - 6 * h1 + h0
  linarith

open OMA.S_oeis_a201553 in
theorem a_val (n v : ℕ) (h : (120 : ℤ) * v = (6 * n + 5) * (6 * n + 4) * (6 * n + 3) * (6 * n + 2) * (6 * n + 1)
      - 6 * ((4 * n + 4) * (4 * n + 3) * (4 * n + 2) * (4 * n + 1) * (4 * n))
      + 15 * ((2 * n + 3) * (2 * n + 2) * (2 * n + 1) * (2 * n) * (2 * n - 1))) : a n = v := by
  have := a_poly n
  have h2 : (a n : ℤ) = v := by linarith
  exact_mod_cast h2

open OMA.S_oeis_a201553 PowerSeries in
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (141 + 905 * X + 940 * X ^ 2 + 120 * X ^ 3 + 7 * X ^ 4 - X ^ 5) := by
  have hL : (1 - X : PowerSeries ℤ) ^ 6
      = 1 - 6 * X + 15 * X ^ 2 - 20 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5 + X ^ 6 := by ring
  have hR : (X * (141 + 905 * X + 940 * X ^ 2 + 120 * X ^ 3 + 7 * X ^ 4 - X ^ 5) : PowerSeries ℤ)
      = 141 * X + 905 * X ^ 2 + 940 * X ^ 3 + 120 * X ^ 4 + 7 * X ^ 5 - X ^ 6 := by ring
  have hc : ∀ (p : PowerSeries ℤ) (z : ℤ) (k n : ℕ),
      coeff n (p * ((z : PowerSeries ℤ) * X ^ k)) = if k ≤ n then z * coeff (n - k) p else 0 := by
    intro p z k n
    rw [mul_left_comm, ← eq_intCast C z, coeff_C_mul, coeff_mul_X_pow']
    split_ifs <;> simp
  have hd : ∀ (z : ℤ) (k n : ℕ),
      coeff n ((z : PowerSeries ℤ) * X ^ k) = if n = k then z else 0 := by
    intro z k n
    rw [← eq_intCast C z, coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have h1 := a_val 1 141 (by norm_num)
  have h2 := a_val 2 1751 (by norm_num)
  have h3 := a_val 3 9331 (by norm_num)
  have h4 := a_val 4 32661 (by norm_num)
  have h5 := a_val 5 88913 (by norm_num)
  have h6 := a_val 6 204763 (by norm_num)
  rw [hL, hR]
  have hL2 : (1 - 6 * X + 15 * X ^ 2 - 20 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5 + X ^ 6 : PowerSeries ℤ)
      = ((1 : ℤ) : PowerSeries ℤ) * X ^ 0 + ((-6 : ℤ) : PowerSeries ℤ) * X ^ 1
        + ((15 : ℤ) : PowerSeries ℤ) * X ^ 2 + ((-20 : ℤ) : PowerSeries ℤ) * X ^ 3
        + ((15 : ℤ) : PowerSeries ℤ) * X ^ 4 + ((-6 : ℤ) : PowerSeries ℤ) * X ^ 5
        + ((1 : ℤ) : PowerSeries ℤ) * X ^ 6 := by
    push_cast; ring
  have hR2 : (141 * X + 905 * X ^ 2 + 940 * X ^ 3 + 120 * X ^ 4 + 7 * X ^ 5 - X ^ 6 : PowerSeries ℤ)
      = ((141 : ℤ) : PowerSeries ℤ) * X ^ 1 + ((905 : ℤ) : PowerSeries ℤ) * X ^ 2
        + ((940 : ℤ) : PowerSeries ℤ) * X ^ 3 + ((120 : ℤ) : PowerSeries ℤ) * X ^ 4
        + ((7 : ℤ) : PowerSeries ℤ) * X ^ 5 + ((-1 : ℤ) : PowerSeries ℤ) * X ^ 6 := by
    push_cast; ring
  rw [hL2, hR2]
  ext n
  simp only [mul_add, map_add, hc, hd, coeff_mk]
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> simp [h1, h2, h3, h4, h5, h6]
  · have hr := rec n (by omega)
    have g : ∀ j : ℕ, j ≤ 6 → n - j ≠ 0 := fun j hj => by omega
    simp only [if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_neg (g 0 (by omega)), if_neg (g 1 (by omega)), if_neg (g 2 (by omega)),
      if_neg (g 3 (by omega)), if_neg (g 4 (by omega)), if_neg (g 5 (by omega)),
      if_neg (g 6 (by omega)),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega)]
    simp only [Nat.sub_zero] at hr ⊢
    linarith

end A201553P

theorem OMA.solution : type_of% @OMA.S_oeis_a201553.main := ⟨A201553P.gf, A201553P.rec⟩
