import OMAStatements.S_oeis_a214526
import Mathlib

open OMA.S_oeis_a214526

namespace A214526Proof

abbrev S (j : ℕ) : List (ℤ × ℤ) := steps j

lemma S_succ (j : ℕ) : S (j + 1) = S j ++ List.replicate (j / 2 + 1) (dir j) := by
  simp [S, steps, List.range_succ, List.flatMap_append]

lemma S_ext (j k : ℕ) : ∃ X, S (j + 1 + k) = S (j + 1) ++ X := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨X, hX⟩ := ih
    refine ⟨X ++ List.replicate ((j + 1 + k) / 2 + 1) (dir (j + 1 + k)), ?_⟩
    rw [show j + 1 + (k + 1) = (j + 1 + k) + 1 by omega, S_succ, hX, List.append_assoc]

lemma S_len_ge (j : ℕ) : j ≤ (S j).length := by
  induction j with
  | zero => simp
  | succ j ih => rw [S_succ, List.length_append, List.length_replicate]; omega

lemma take_S (j r s : ℕ) (hs : s ≤ j / 2 + 1) (hjr : j < r) :
    (S r).take ((S j).length + s) = S j ++ List.replicate s (dir j) := by
  obtain ⟨X, hX⟩ := S_ext j (r - j - 1)
  rw [show r = j + 1 + (r - j - 1) by omega, hX, S_succ, List.append_assoc,
    List.take_length_add_append, List.take_append_of_le_length (by simp; omega),
    List.take_replicate, Nat.min_eq_left hs]

lemma pos_eq (n j s : ℕ) (hn : 1 ≤ n) (hs : s ≤ j / 2 + 1) (hm : n - 1 = (S j).length + s) :
    pos n = (S j).sum + s • dir j := by
  have hj := S_len_ge j
  have hjn : j < n := by omega
  unfold pos
  rw [hm, show steps n = S n from rfl, take_S j n s hs hjn, List.sum_append,
    List.sum_replicate]

lemma len_even (t : ℕ) : (S (2 * t)).length = t * (t + 1) := by
  induction t with
  | zero => simp [S, steps]
  | succ t ih =>
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega, S_succ, S_succ, List.length_append,
      List.length_append, List.length_replicate, List.length_replicate, ih]
    have h1 : (2 * t + 1) / 2 = t := by omega
    have h2 : (2 * t) / 2 = t := by omega
    rw [h1, h2]; ring

lemma len_odd (t : ℕ) : (S (2 * t + 1)).length = (t + 1) * (t + 1) := by
  rw [S_succ, List.length_append, List.length_replicate, len_even]
  have h2 : (2 * t) / 2 = t := by omega
  rw [h2]; ring

lemma dir1 (L : ℕ) : dir (4 * L + 1) = (1, 0) := by
  unfold dir; rw [if_neg (by omega), if_pos (by omega)]
lemma dir2 (L : ℕ) : dir (4 * L + 2) = (0, -1) := by
  unfold dir; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
lemma dir3 (L : ℕ) : dir (4 * L + 3) = (-1, 0) := by
  unfold dir; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
lemma dir0 (L : ℕ) : dir (4 * L + 4) = (0, 1) := by
  unfold dir; rw [if_pos (by omega)]

lemma sum1 (L : ℕ) : (S (4 * L + 1)).sum = (-(L : ℤ), (L : ℤ) + 1) := by
  induction L with
  | zero => decide
  | succ L ih =>
    rw [show 4 * (L + 1) + 1 = 4 * L + 4 + 1 by omega, S_succ,
      show 4 * L + 4 = 4 * L + 3 + 1 by omega, S_succ,
      show 4 * L + 3 = 4 * L + 2 + 1 by omega, S_succ,
      show 4 * L + 2 = 4 * L + 1 + 1 by omega, S_succ]
    simp only [List.sum_append, List.sum_replicate, ih]
    rw [show 4 * L + 1 + 1 + 1 + 1 = 4 * L + 4 by omega, show 4 * L + 1 + 1 + 1 = 4 * L + 3 by omega,
      show 4 * L + 1 + 1 = 4 * L + 2 by omega, dir1, dir2, dir3, dir0]
    have e1 : (4 * L + 1) / 2 + 1 = 2 * L + 1 := by omega
    have e2 : (4 * L + 2) / 2 + 1 = 2 * L + 2 := by omega
    have e3 : (4 * L + 3) / 2 + 1 = 2 * L + 2 := by omega
    have e4 : (4 * L + 4) / 2 + 1 = 2 * L + 3 := by omega
    rw [e1, e2, e3, e4]
    ext <;> simp <;> push_cast <;> ring

lemma sum2 (L : ℕ) : (S (4 * L + 2)).sum = ((L : ℤ) + 1, (L : ℤ) + 1) := by
  rw [show 4 * L + 2 = 4 * L + 1 + 1 by omega, S_succ, List.sum_append, List.sum_replicate, sum1,
    dir1, show (4 * L + 1) / 2 + 1 = 2 * L + 1 by omega]
  ext <;> simp <;> push_cast <;> ring

lemma sum3 (L : ℕ) : (S (4 * L + 3)).sum = ((L : ℤ) + 1, -((L : ℤ) + 1)) := by
  rw [show 4 * L + 3 = 4 * L + 2 + 1 by omega, S_succ, List.sum_append, List.sum_replicate, sum2,
    dir2, show (4 * L + 2) / 2 + 1 = 2 * L + 2 by omega]
  ext <;> simp <;> push_cast <;> ring

lemma sum4 (L : ℕ) : (S (4 * L + 4)).sum = (-((L : ℤ) + 1), -((L : ℤ) + 1)) := by
  rw [show 4 * L + 4 = 4 * L + 3 + 1 by omega, S_succ, List.sum_append, List.sum_replicate, sum3,
    dir3, show (4 * L + 3) / 2 + 1 = 2 * L + 2 by omega]
  ext <;> simp <;> push_cast <;> ring

lemma lenA (L : ℕ) : (S (4 * L + 1)).length = (2 * L + 1) ^ 2 := by
  rw [show 4 * L + 1 = 2 * (2 * L) + 1 by omega, len_odd]; ring
lemma lenB (L : ℕ) : (S (4 * L + 2)).length = (2 * L + 1) ^ 2 + (2 * L + 1) := by
  rw [show 4 * L + 2 = 2 * (2 * L + 1) by omega, len_even]; ring
lemma lenC (L : ℕ) : (S (4 * L + 3)).length = (2 * L + 1) ^ 2 + (4 * L + 3) := by
  rw [show 4 * L + 3 = 2 * (2 * L + 1) + 1 by omega, len_odd]; ring
lemma lenD (L : ℕ) : (S (4 * L + 4)).length = (2 * L + 1) ^ 2 + (6 * L + 5) := by
  rw [show 4 * L + 4 = 2 * (2 * L + 2) by omega, len_even]; ring

lemma layer_eq (n L : ℕ) (h1 : (2 * L + 1) ^ 2 < n) (h2 : n ≤ (2 * L + 3) ^ 2) :
    layer n = (L : ℤ) + 1 := by
  unfold layer
  rw [Int.ceil_eq_iff]
  have hn : (0 : ℝ) ≤ n := by positivity
  constructor
  · have : (2 * (L : ℝ) + 1) < Real.sqrt n := by
      rw [Real.lt_sqrt (by positivity)]
      exact_mod_cast h1
    push_cast; linarith
  · have : Real.sqrt n ≤ 2 * (L : ℝ) + 3 := by
      rw [show (2 * (L : ℝ) + 3) = Real.sqrt ((2 * (L : ℝ) + 3) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast h2)
    push_cast; linarith

lemma emod_of (x d q r : ℤ) (h : x = r + d * q) (h0 : 0 ≤ r) (h1 : r < d) : x % d = r := by
  subst h
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

end A214526Proof

open A214526Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a214526.main := by
  intro n hn
  set m := n - 1 with hm
  have hm1 : 1 ≤ m := by omega
  set L := (Nat.sqrt m - 1) / 2 with hL
  have hq1 : 1 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
  have hsq := Nat.sqrt_le' m
  have hlt := Nat.lt_succ_sqrt' m
  have hlo : (2 * L + 1) ^ 2 ≤ m := by
    have : 2 * L + 1 ≤ Nat.sqrt m := by omega
    calc (2 * L + 1) ^ 2 ≤ Nat.sqrt m ^ 2 := Nat.pow_le_pow_left this 2
      _ ≤ m := hsq
  have hhi : m ≤ (2 * L + 1) ^ 2 + (8 * L + 7) := by
    have : Nat.sqrt m + 1 ≤ 2 * L + 3 := by omega
    have := Nat.pow_le_pow_left this 2
    nlinarith
  have hsq3 : (2 * L + 3) ^ 2 = (2 * L + 1) ^ 2 + 8 * L + 8 := by ring
  have hlay : layer n = (L : ℤ) + 1 := layer_eq n L (by omega) (by omega)
  rw [hlay]
  have hn1 : ((n : ℤ) - 1) = ((2 * L + 1) ^ 2 : ℕ) + ((m - (2 * L + 1) ^ 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hlo]; omega
  set t := m - (2 * L + 1) ^ 2 with ht
  have htb : t ≤ 8 * L + 7 := by omega
  rw [hn1]
  unfold a
  have hm' : n - 1 = (2 * L + 1) ^ 2 + t := by omega
  push_cast
  rcases (show t ≤ 2 * L ∨ (2 * L + 1 ≤ t ∧ t ≤ 4 * L + 2) ∨ (4 * L + 3 ≤ t ∧ t ≤ 6 * L + 4) ∨
      (6 * L + 5 ≤ t ∧ t ≤ 8 * L + 6) ∨ t = 8 * L + 7 by omega) with h | h | h | h | h
  · rw [pos_eq n (4 * L + 1) t (by omega) (by omega) (by rw [lenA]; omega), sum1, dir1,
      emod_of _ _ (2 * L) (1 + (t : ℤ)) (by push_cast; ring) (by positivity) (by push_cast; omega)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add, mul_neg, Int.natCast_natAbs]
    simp only [abs_eq_max_neg]
    omega
  · rw [pos_eq n (4 * L + 2) (t - (2 * L + 1)) (by omega) (by omega) (by rw [lenB]; omega), sum2, dir2,
      emod_of _ _ (2 * L + 1) ((t : ℤ) - (2 * L + 1)) (by push_cast; ring) (by omega) (by push_cast; omega)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add, mul_neg, Int.natCast_natAbs]
    simp only [abs_eq_max_neg]
    omega
  · rw [pos_eq n (4 * L + 3) (t - (4 * L + 3)) (by omega) (by omega) (by rw [lenC]; omega), sum3, dir3,
      emod_of _ _ (2 * L + 2) ((t : ℤ) - (4 * L + 3)) (by push_cast; ring) (by omega) (by push_cast; omega)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add, mul_neg, Int.natCast_natAbs]
    simp only [abs_eq_max_neg]
    omega
  · rw [pos_eq n (4 * L + 4) (t - (6 * L + 5)) (by omega) (by omega) (by rw [lenD]; omega), sum4, dir0,
      emod_of _ _ (2 * L + 3) ((t : ℤ) - (6 * L + 5)) (by push_cast; ring) (by omega) (by push_cast; omega)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add, mul_neg, Int.natCast_natAbs]
    simp only [abs_eq_max_neg]
    omega
  · rw [pos_eq n (4 * L + 4) (t - (6 * L + 5)) (by omega) (by omega) (by rw [lenD]; omega), sum4, dir0,
      emod_of _ _ (2 * L + 4) 0 (by push_cast; rw [h]; push_cast; ring) (le_refl _) (by push_cast; omega)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, nsmul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add, mul_neg, Int.natCast_natAbs]
    simp only [abs_eq_max_neg]
    omega
