import OMAReductions.R_OeisA157237_conjecture_R1
import Mathlib

/-!
For each listed `n`, with `N = 2n - 1 ≤ 2^17`, only exponents `x, y ≤ 17` can satisfy
`2^x + 11 * 2^y < N`; for those a kernel check shows `N - 2^x - 11 * 2^y` is not a prime
`≡ 1 (mod 6)`, using a trial-division test that is exact for primality.
-/

namespace OMA.A157237

def ptest (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range' 2 (Nat.sqrt n - 1)).all (fun d => n % d != 0)

theorem ptest_complete {n : ℕ} (h : n.Prime) : ptest n = true := by
  unfold ptest
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq]
  refine ⟨h.two_le, fun d ⟨hd2, hd⟩ hmod => ?_⟩
  have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
  have hsq : d ≤ Nat.sqrt n := by omega
  have hdn : d < n := lt_of_le_of_lt hsq (Nat.sqrt_lt_self h.one_lt)
  rcases (Nat.dvd_prime h).mp hdvd with rfl | rfl <;> omega

def bad (N x y : ℕ) : Bool :=
  !(decide (2 ^ x + 11 * 2 ^ y < N)) || (N - (2 ^ x + 11 * 2 ^ y)) % 6 != 1 ||
    !ptest (N - (2 ^ x + 11 * 2 ^ y))

theorem bad_sound {N x y : ℕ} (h : bad N x y = true) :
    ¬ (2 ^ x + 11 * 2 ^ y < N ∧ (N - (2 ^ x + 11 * 2 ^ y)).Prime ∧
      (N - (2 ^ x + 11 * 2 ^ y)) % 6 = 1) := by
  rintro ⟨h1, h2, h3⟩
  unfold bad at h
  rw [ptest_complete h2] at h
  simp [h1, h3] at h

def grid (N K : ℕ) : Bool :=
  (List.range' 1 K).all fun x => (List.range' 1 K).all fun y => bad N x y

theorem a_zero (n K : ℕ) (hn : n ≠ 0) (hK : 2 * n - 1 ≤ 2 ^ K) (hg : grid (2 * n - 1) K = true) :
    OeisA157237.a n = 0 := by
  unfold OeisA157237.a
  rw [if_neg hn]
  simp only
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
  rw [if_neg]
  intro hc
  have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
  have hy1 : 1 ≤ y := (Finset.mem_Icc.mp hy).1
  by_cases hxK : x ≤ K
  · by_cases hyK : y ≤ K
    · unfold grid at hg
      have := List.all_eq_true.mp (List.all_eq_true.mp hg x (List.mem_range'_1.mpr ⟨hx1, by omega⟩))
        y (List.mem_range'_1.mpr ⟨hy1, by omega⟩)
      exact bad_sound this hc
    · have hy2 : 2 ^ K < 2 ^ y := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hle : 2 ^ y ≤ 2 ^ x + 11 * 2 ^ y :=
        (Nat.le_mul_of_pos_left _ (by norm_num)).trans (Nat.le_add_left _ _)
      exact absurd (hle.trans_lt (hc.1.trans_le hK)) (not_lt.mpr hy2.le)
  · have hx2 : 2 ^ K < 2 ^ x := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hle : 2 ^ x ≤ 2 ^ x + 11 * 2 ^ y := Nat.le_add_right _ _
    exact absurd (hle.trans_lt (hc.1.trans_le hK)) (not_lt.mpr hx2.le)

theorem all_ok : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 21, 24, 51, 84, 1011, 59586] : List ℕ).all
    (fun n => grid (2 * n - 1) 17) = true := by
  decide +kernel

end OMA.A157237

theorem OMA.solution : OMA.R_OeisA157237_conjecture_R1.H1 := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · unfold OeisA157237.a; simp
  have hmem : n ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 21, 24, 51, 84, 1011, 59586] : List ℕ) := by
    rcases hn with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have hg := List.all_eq_true.mp OMA.A157237.all_ok n hmem
  have hle : n ≤ 59586 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem; omega
  exact OMA.A157237.a_zero n 17 (by omega) (by norm_num; omega) hg
