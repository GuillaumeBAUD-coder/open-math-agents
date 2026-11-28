import OMAStatements.S_oeis_a273767

/-!
# OEIS A273767

Source: https://oeis.org/A273767 (OEIS Foundation, CC BY-SA 4.0).
Robert Price submitted the sequence. Lars Blomberg conjectured the rule
equivalences and closed form, and Colin Barker gave the recurrence and
generating function. The upstream Lean statement was submitted by @jleguina.
Proof: @grp06.
-/

namespace OMA.S_oeis_a273767

open PowerSeries

private def code (i : Fin 6) : ℕ := 913 + 8 * i.val

private def background : ℕ → Bool
  | 0 => false
  | _ + 1 => true

private theorem birth : ∀ i : Fin 6, ruleOf (code i) false 0 = true := by decide +kernel

private theorem persistence : ∀ i : Fin 6, ruleOf (code i) true 4 = true := by decide +kernel

private def outside (t : ℕ) (p : ℤ × ℤ) : Prop :=
  p.1 < -(t : ℤ) ∨ (t : ℤ) < p.1 ∨ p.2 < -(t : ℤ) ∨ (t : ℤ) < p.2

private instance (t : ℕ) (p : ℤ × ℤ) : Decidable (outside t p) := by
  unfold outside
  infer_instance

private theorem outside_previous {t : ℕ} {p : ℤ × ℤ} (h : outside (t + 1) p) :
    outside t p ∧ ∀ q ∈ nbrs p, outside t q := by
  obtain ⟨x, y⟩ := p
  simp only [outside] at h
  constructor
  · simp only [outside]
    omega
  · intro q hq
    simp only [nbrs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp only [outside] <;> omega

private theorem zero_outside {r : ℕ} {p : ℤ × ℤ} (h : outside 0 p) :
    stateOf r 0 p = background 0 := by
  have hp : p ≠ (0, 0) := by
    intro he
    subst p
    simp [outside] at h
  simp [stateOf, background, hp]

private def advance (r : ℕ) (f : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  ruleOf r (f p) ((nbrs p).countP f)

private theorem advance_congr {r : ℕ} {f g : ℤ × ℤ → Bool} {p : ℤ × ℤ}
    (hp : f p = g p) (hn : ∀ q ∈ nbrs p, f q = g q) :
    advance r f p = advance r g p := by
  have hc : (nbrs p).countP f = (nbrs p).countP g :=
    List.countP_congr (by intro q hq; rw [hn q hq])
  unfold advance
  rw [hp, hc]

private theorem advance_background (i : Fin 6) (t : ℕ) (p : ℤ × ℤ) :
    advance (code i) (fun _ => background t) p = background (t + 1) := by
  cases t <;> simp [advance, background, nbrs, birth, persistence]

private theorem outside_background (i : Fin 6) (t : ℕ) (p : ℤ × ℤ)
    (h : outside t p) : stateOf (code i) t p = background t := by
  induction t generalizing p with
  | zero => exact zero_outside h
  | succ t ih =>
    obtain ⟨hp, hs⟩ := outside_previous h
    change advance (code i) (stateOf (code i) t) p = background (t + 1)
    exact (advance_congr (ih p hp) (fun q hq => ih q (hs q hq))).trans
      (advance_background i t p)

private def cell (t x y : ℕ) : ℤ × ℤ :=
  ((x : ℤ) - (t : ℤ), (y : ℤ) - (t : ℤ))

private theorem inside_cell {t : ℕ} {p : ℤ × ℤ} (h : ¬ outside t p) :
    ∃ x y : Fin (2 * t + 1), cell t x.val y.val = p := by
  obtain ⟨x, y⟩ := p
  simp only [outside] at h
  let u := (x + (t : ℤ)).toNat
  let v := (y + (t : ℤ)).toNat
  have hu : (u : ℤ) = x + (t : ℤ) := Int.toNat_of_nonneg (by omega)
  have hv : (v : ℤ) = y + (t : ℤ) := Int.toNat_of_nonneg (by omega)
  refine ⟨⟨u, by omega⟩, ⟨v, by omega⟩, ?_⟩
  change ((u : ℤ) - (t : ℤ), (v : ℤ) - (t : ℤ)) = (x, y)
  simp only [hu, hv, add_sub_cancel_right]

/--
A bit is set where the window differs from its homogeneous background.
For coordinates `(x,y)` in `[-t,t]²`, the bit index is
`(x+t)*(2*t+1)+(y+t)`. At time 2 the first two rules have a different mask
from the other four rules.
-/
private def mask (i : Fin 6) (t : ℕ) : ℕ :=
  match t with
  | 0 => 1
  | 1 => 186
  | 2 => if i.val < 2 then 469440 else 141440
  | 3 => 16777216
  | _ => 0

private def board (i : Fin 6) (t : ℕ) (p : ℤ × ℤ) : Bool :=
  if outside t p then background t
  else if (mask i t).testBit
      ((p.1 + (t : ℤ)).toNat * (2 * t + 1) + (p.2 + (t : ℤ)).toNat)
    then !(background t)
    else background t

private theorem board_zero (i : Fin 6) (p : ℤ × ℤ) :
    stateOf (code i) 0 p = board i 0 p := by
  by_cases h : outside 0 p
  · rw [board, if_pos h]
    exact zero_outside h
  · obtain ⟨x, y⟩ := p
    simp only [outside, Nat.cast_zero, neg_zero] at h
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    fin_cases i <;> decide +kernel

-- Each check computes one step using only the preceding bit mask.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem finite_steps (i : Fin 6) (t : Fin 7) :
    ∀ x y : Fin (2 * (t.val + 1) + 1),
      board i (t.val + 1) (cell (t.val + 1) x.val y.val) =
        advance (code i) (board i t.val) (cell (t.val + 1) x.val y.val) := by
  fin_cases i <;> fin_cases t <;> decide +kernel

private theorem board_correct (i : Fin 6) (t : ℕ) (ht : t ≤ 7) (p : ℤ × ℤ) :
    stateOf (code i) t p = board i t p := by
  induction t generalizing p with
  | zero => exact board_zero i p
  | succ t ih =>
    by_cases h : outside (t + 1) p
    · rw [board, if_pos h]
      exact outside_background i (t + 1) p h
    · obtain ⟨x, y, rfl⟩ := inside_cell h
      change advance (code i) (stateOf (code i) t) _ = _
      have hf : stateOf (code i) t = board i t := funext (ih (by omega))
      rw [hf]
      exact (finite_steps i ⟨t, by omega⟩ x y).symm

private theorem all_on (i : Fin 6) (t : ℕ) (ht : 7 ≤ t) (p : ℤ × ℤ) :
    stateOf (code i) t p = true := by
  have he : t = 7 + (t - 7) := by omega
  suffices h : ∀ k : ℕ, ∀ q, stateOf (code i) (7 + k) q = true by
    rw [he]
    exact h (t - 7) p
  intro k
  induction k with
  | zero =>
    intro q
    change stateOf (code i) 7 q = true
    rw [board_correct i 7 (by decide)]
    simp [board, background, mask]
  | succ k ih =>
    intro q
    change advance (code i) (stateOf (code i) (7 + k)) q = true
    simp [advance, nbrs, ih, persistence]

private def boardCount (i : Fin 6) (t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * t + 1), ∑ y ∈ Finset.range (2 * t + 1),
    if board i t (cell t x y) then 1 else 0

private def initial (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | _ => 48

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem board_samples (i : Fin 6) (n : Fin 3) :
    boardCount i (2 ^ n.val - 1) = initial n.val := by
  fin_cases i <;> fin_cases n <;> decide +kernel

private theorem count_initial (i : Fin 6) (n : ℕ) (hn : n < 3) :
    aOf (code i) n = initial n := by
  have ht : 2 ^ n - 1 ≤ 7 := by interval_cases n <;> decide
  calc
    aOf (code i) n = boardCount i (2 ^ n - 1) := by
      unfold aOf boardCount
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      exact congrArg (fun b : Bool => if b then (1 : ℕ) else 0)
        (board_correct i _ ht (cell _ x y))
    _ = initial n := board_samples i ⟨n, hn⟩

private theorem two_pow_pos (n : ℕ) : 1 ≤ (2 : ℕ) ^ n :=
  Nat.succ_le_of_lt (pow_pos (by decide) _)

private theorem count_large (i : Fin 6) (n : ℕ) (hn : 3 ≤ n) :
    aOf (code i) n = (2 * (2 ^ n - 1) + 1) ^ 2 := by
  have hpow : 2 ^ 3 ≤ (2 : ℕ) ^ n := pow_le_pow_right₀ (by decide) hn
  have ht : 7 ≤ 2 ^ n - 1 := by omega
  simp [aOf, all_on i _ ht, Finset.sum_const, pow_two]

private theorem state_specializes (t : ℕ) (p : ℤ × ℤ) : state t p = stateOf 913 t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => simp only [state, stateOf, rule, ruleOf, ih]

private theorem a_specializes (n : ℕ) : a n = aOf (code 0) n := by
  change a n = aOf 913 n
  simp only [a, aOf, state_specializes]

private theorem same_counts (i : Fin 6) (n : ℕ) : aOf (code i) n = a n := by
  rw [a_specializes]
  by_cases h : n < 3
  · rw [count_initial i n h, count_initial 0 n h]
  · rw [count_large i n (by omega), count_large 0 n (by omega)]

private theorem form (R : Type*) [CommRing R] (n : ℕ) (hn : 3 ≤ n) :
    (a n : R) = (2 ^ (n + 1) - 1) ^ 2 := by
  rw [a_specializes, count_large 0 n hn]
  push_cast [Nat.cast_sub (two_pow_pos n)]
  rw [pow_succ (2 : R) n]
  ring

private theorem recurrence_at {R : Type*} [CommRing R] (f : ℕ → R)
    (h : ∀ n, 3 ≤ n → f n = (2 ^ (n + 1) - 1) ^ 2)
    (m : ℕ) (hm : 3 ≤ m) :
    f (m + 3) = 7 * f (m + 2) - 14 * f (m + 1) + 8 * f m := by
  rw [h (m + 3) (by omega), h (m + 2) (by omega), h (m + 1) (by omega), h m hm]
  simp only [pow_add]
  ring

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  have h := recurrence_at (fun k => (a k : ℤ)) (form ℤ) (n - 3) (by omega)
  rwa [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega] at h

private theorem small_zero : a 0 = 1 := (a_specializes 0).trans (count_initial 0 0 (by decide))
private theorem small_one : a 1 = 4 := (a_specializes 1).trans (count_initial 0 1 (by decide))
private theorem small_two : a 2 = 48 := (a_specializes 2).trans (count_initial 0 2 (by decide))

set_option maxHeartbeats 4000000 in
private theorem generating :
    A = (1 - 3 * X + 34 * X ^ 2 - 63 * X ^ 3 + 26 * X ^ 4 + 8 * X ^ 5) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ := by
  let D : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X) * (1 - 4 * X)
  let N : ℚ⟦X⟧ := 1 - 3 * X + 34 * X ^ 2 - 63 * X ^ 3 + 26 * X ^ 4 + 8 * X ^ 5
  change A = N * D⁻¹
  have hD : A * D = A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) -
      C 8 * (A * X ^ 3) := by
    simp only [D, map_ofNat, pow_one]
    ring
  have hN : N = 1 - C 3 * X ^ 1 + C 34 * X ^ 2 - C 63 * X ^ 3 +
      C 26 * X ^ 4 + C 8 * X ^ 5 := by
    simp only [N, map_ofNat, pow_one]
  have hprod : A * D = N := by
    apply PowerSeries.ext
    intro n
    rw [hD, hN]
    simp only [map_sub, map_add, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_mul_X_pow', coeff_one, A, coeff_mk]
    by_cases hn : n < 6
    · have h3 : (a 3 : ℚ) = 225 := by rw [form ℚ 3 (by decide)] <;> norm_num
      have h4 : (a 4 : ℚ) = 961 := by rw [form ℚ 4 (by decide)] <;> norm_num
      have h5 : (a 5 : ℚ) = 3969 := by rw [form ℚ 5 (by decide)] <;> norm_num
      interval_cases n <;>
        norm_num only [small_zero, small_one, small_two, h3, h4, h5, if_true, if_false]
    · have h := recurrence_at (fun k => (a k : ℚ)) (form ℚ) (n - 3) (by omega)
      rw [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
        show n - 3 + 1 = n - 2 by omega] at h
      simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
        if_pos (show 3 ≤ n by omega), if_neg (show n ≠ 0 by omega),
        if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
        if_neg (show n ≠ 5 by omega)]
      linarith only [h]
  have hD0 : constantCoeff D ≠ 0 := by simp [D]
  calc
    A = (A * D) * D⁻¹ := by rw [mul_assoc, PowerSeries.mul_inv_cancel D hD0, mul_one]
    _ = N * D⁻¹ := by rw [hprod]

end OMA.S_oeis_a273767

open OMA.S_oeis_a273767 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273767.main := by
  exact ⟨same_counts 1, same_counts 2, same_counts 3, same_counts 4, same_counts 5,
    fun n hn => form ℚ n (by omega), recurrence, generating⟩
