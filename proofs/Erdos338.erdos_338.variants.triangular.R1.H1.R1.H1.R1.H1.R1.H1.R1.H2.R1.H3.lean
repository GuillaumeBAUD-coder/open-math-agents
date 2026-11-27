import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-! Averaging the divisor convolution of the Jacobi symbol.

The symbol is periodic of period s. Convergence of its Dirichlet series forces
the sum over one period to vanish, so every running sum is at most s. Splitting
the fractional-part error at sqrt(n) then shows that the error is o(n), and the
average of the convolution tends to the same limit. -/

open Finset Filter Topology

namespace Erdos338Hyperbola

abbrev chi (s a : ℕ) : ℤ := jacobiSym (a : ℤ) s

def cum (s N : ℕ) : ℤ := ∑ a ∈ Icc 1 N, chi s a

noncomputable def series (s N : ℕ) : ℝ := ∑ a ∈ Icc 1 N, (chi s a : ℝ) / a

lemma chi_add (s n : ℕ) : chi s (n + s) = chi s n := by
  apply jacobiSym.mod_left'
  rw [Int.natCast_add]
  exact Int.add_emod_right (n : ℤ) (s : ℤ)

lemma chi_mul_add (s j r : ℕ) : chi s (j * s + r) = chi s r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : (j + 1) * s + r = j * s + r + s := by ring
    rw [hstep, chi_add, ih]

lemma abs_chi_le (s a : ℕ) : |chi s a| ≤ 1 := by
  rcases jacobiSym.trichotomy (a : ℤ) s with h | h | h
  · simp [chi, h]
  · simp [chi, h]
  · simp [chi, h, abs_neg]

lemma abs_sum_chi_le (s : ℕ) (t : Finset ℕ) :
    |∑ a ∈ t, chi s a| ≤ (t.card : ℤ) := by
  refine le_trans (abs_sum_le_sum_abs (fun a => chi s a) t) ?_
  refine le_trans (sum_le_sum fun a _ => abs_chi_le s a) ?_
  simp

lemma cum_succ (s N : ℕ) : cum s (N + 1) = cum s N + chi s (N + 1) := by
  unfold cum
  rw [sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]

lemma cum_add (s m k : ℕ) :
    cum s (m + k) = cum s m + ∑ r ∈ Icc 1 k, chi s (m + r) := by
  induction k with
  | zero => simp [cum]
  | succ k ih =>
    rw [Nat.add_succ, cum_succ, ih, sum_Icc_succ_top (by omega : (1 : ℕ) ≤ k + 1)]
    abel

lemma cum_periods (_hs : 1 < s) (hσ : ∑ r ∈ Icc 1 s, chi s r = 0) (q : ℕ) :
    cum s (q * s) = 0 := by
  induction q with
  | zero => simp [cum]
  | succ q ih =>
    have hstep : (q + 1) * s = q * s + s := by ring
    rw [hstep, cum_add, ih, zero_add]
    have hblock : ∑ r ∈ Icc 1 s, chi s (q * s + r) = ∑ r ∈ Icc 1 s, chi s r := by
      apply sum_congr rfl
      intro r _
      exact chi_mul_add s q r
    rw [hblock, hσ]

lemma abs_cum_le (hs : 1 < s) (hσ : ∑ r ∈ Icc 1 s, chi s r = 0) (N : ℕ) :
    |(cum s N : ℝ)| ≤ s := by
  have hpos : 0 < s := by omega
  have hsplit : N = s * (N / s) + N % s := (Nat.div_add_mod N s).symm
  have hcomm : s * (N / s) = N / s * s := Nat.mul_comm _ _
  rw [hsplit, hcomm, cum_add, cum_periods hs hσ, zero_add]
  have heq : ∑ t ∈ Icc 1 (N % s), chi s (N / s * s + t) =
      ∑ t ∈ Icc 1 (N % s), chi s t := by
    apply sum_congr rfl
    intro t _
    exact chi_mul_add s (N / s) t
  rw [heq]
  have hr : N % s < s := Nat.mod_lt N hpos
  have habs : |∑ t ∈ Icc 1 (N % s), chi s t| ≤ (N % s : ℤ) := by
    calc
      |∑ t ∈ Icc 1 (N % s), chi s t| ≤ ((Icc 1 (N % s)).card : ℤ) :=
        abs_sum_chi_le s _
      _ ≤ N % s := by
        rw [Nat.card_Icc]
        omega
  have habs' : |∑ t ∈ Icc 1 (N % s), chi s t| ≤ (s : ℤ) := le_trans habs (by omega)
  exact_mod_cast habs'

lemma series_succ (s N : ℕ) :
    series s (N + 1) = series s N + (chi s (N + 1) : ℝ) / ↑(N + 1) := by
  unfold series
  rw [sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1)]

lemma series_add (s m k : ℕ) :
    series s (m + k) = series s m + ∑ r ∈ Icc 1 k, (chi s (m + r) : ℝ) / (m + r) := by
  induction k with
  | zero => simp [series]
  | succ k ih =>
    rw [Nat.add_succ, series_succ, ih, sum_Icc_succ_top (by omega : (1 : ℕ) ≤ k + 1)]
    simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]

lemma abel (s N : ℕ) (hN : 0 < N) :
    series s N = (cum s N : ℝ) / N +
      ∑ a ∈ Icc 1 (N - 1), (cum s a : ℝ) / (a * (a + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h0 : N = 0
    · subst h0
      simp [series, cum]
    · have ih' := ih (by omega)
      rw [series_succ, ih', cum_succ]
      have hsplit : Icc 1 N = Icc 1 (N - 1) ∪ {N} := by
        ext a
        simp only [mem_union, mem_singleton, mem_Icc]
        omega
      have hdisj : Disjoint (Icc 1 (N - 1)) ({N} : Finset ℕ) := by
        rw [disjoint_iff_ne]
        intro a ha b hb
        simp only [mem_Icc, mem_singleton] at ha hb
        omega
      rw [show (N + 1) - 1 = N by omega, hsplit, sum_union hdisj, sum_singleton]
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hN0, hN1]
      ring

lemma sum_diff (a b : ℕ) (h : a ≤ b) (g : ℕ → ℝ) :
    ∑ i ∈ Icc a b, (g i - g (i + 1)) = g a - g (b + 1) := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    simp
  | succ b ih =>
    by_cases hle : a ≤ b
    · rw [sum_Icc_succ_top (by omega : a ≤ b + 1), ih hle]
      ring
    · have : a = b + 1 := by omega
      subst this
      simp

lemma one_div_sq_le (j : ℕ) (hj : 2 ≤ j) :
    (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / ↑(j - 1) - 1 / (j : ℝ) := by
  have hsub : ↑(j - 1) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j)]
    simp
  rw [hsub]
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hjm : (j : ℝ) - 1 ≠ 0 := by linarith
  have hid : (1 : ℝ) / ((j : ℝ) - 1) - 1 / j = 1 / (((j : ℝ) - 1) * j) := by
    rw [div_sub_div 1 1 hjm hj0]
    have : (1 : ℝ) * j - ((j : ℝ) - 1) * 1 = 1 := by ring
    rw [this]
  rw [hid]
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith

lemma sum_inv_sq_le (M : ℕ) : ∑ j ∈ Icc 1 M, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  cases M with
  | zero => simp
  | succ M =>
    cases M with
    | zero => simp
    | succ M =>
      have hsplit : Icc 1 (M.succ.succ) = insert 1 (Icc 2 (M.succ.succ)) := by
        ext a
        simp only [mem_insert, mem_Icc]
        omega
      have hnot : 1 ∉ Icc 2 (M.succ.succ) := by
        simp only [mem_Icc]
        omega
      rw [hsplit, sum_insert hnot]
      have hone : (1 : ℝ) / ↑(1 : ℕ) ^ 2 = 1 := by norm_num
      rw [hone]
      have hle : ∑ j ∈ Icc 2 (M.succ.succ), (1 : ℝ) / (j : ℝ) ^ 2 ≤
          ∑ j ∈ Icc 2 (M.succ.succ), (1 / ↑(j - 1) - 1 / (j : ℝ)) := by
        apply sum_le_sum
        intro j hj
        exact one_div_sq_le j (by simp only [mem_Icc] at hj; omega)
      have htel : ∑ j ∈ Icc 2 (M.succ.succ), (1 / ↑(j - 1) - 1 / (j : ℝ)) =
          1 - 1 / (M.succ.succ : ℝ) := by
        have h := sum_diff 2 (M.succ.succ) (by omega) (fun j => (1 : ℝ) / ↑(j - 1))
        have h2 : (2 - 1 : ℕ) = 1 := by omega
        have hM : M.succ.succ + 1 - 1 = M.succ.succ := by omega
        simpa [h2, hM, Nat.add_sub_cancel] using h
      have hrest : (0 : ℝ) ≤ 1 / (M.succ.succ : ℝ) := by positivity
      have hsum : ∑ j ∈ Icc 2 (M.succ.succ), (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 := by
        linarith [htel, hle, hrest]
      linarith

lemma inv_mul_succ (a : ℕ) (ha : 0 < a) :
    (1 : ℝ) / (a * (a + 1)) = 1 / a - 1 / (a + 1 : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have ha1 : ((a : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma weighted (s T : ℕ) (f : ℕ → ℝ) :
    ∀ n, T < n →
      ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * f a =
        (cum s n : ℝ) * f n - (cum s T : ℝ) * f (T + 1) +
          ∑ a ∈ Icc (T + 1) (n - 1), (cum s a : ℝ) * (f a - f (a + 1)) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hle : n ≤ T
    · have hnT : n = T := by omega
      have hsing : Icc (T + 1) (n + 1) = {n + 1} := by
        ext a
        simp only [mem_Icc, mem_singleton]
        omega
      have hempty : Icc (T + 1) ((n + 1) - 1) = ∅ :=
        Icc_eq_empty_iff.mpr (by omega)
      rw [hsing, sum_singleton, hempty, sum_empty, cum_succ, hnT]
      have hcast : ((cum s T + chi s (T + 1) : ℤ) : ℝ) =
          (cum s T : ℝ) + (chi s (T + 1) : ℝ) := by exact_mod_cast rfl
      rw [hcast]
      ring
    · have ih' := ih (by omega)
      have hsplit : Icc (T + 1) (n + 1) = Icc (T + 1) n ∪ {n + 1} := by
        ext a
        simp only [mem_union, mem_Icc, mem_singleton]
        omega
      have hdisj : Disjoint (Icc (T + 1) n) ({n + 1} : Finset ℕ) := by
        rw [disjoint_iff_ne]
        intro a ha b hb
        simp only [mem_Icc, mem_singleton] at ha hb
        omega
      rw [hsplit, sum_union hdisj, sum_singleton, ih']
      have hsum : Icc (T + 1) n = Icc (T + 1) (n - 1) ∪ {n} := by
        ext a
        simp only [mem_union, mem_Icc, mem_singleton]
        omega
      have hdisj2 : Disjoint (Icc (T + 1) (n - 1)) ({n} : Finset ℕ) := by
        rw [disjoint_iff_ne]
        intro a ha b hb
        simp only [mem_Icc, mem_singleton] at ha hb
        omega
      rw [show n + 1 - 1 = n by omega, hsum, sum_union hdisj2, sum_singleton, cum_succ]
      have hcast : ((cum s n + chi s (n + 1) : ℤ) : ℝ) =
          (cum s n : ℝ) + (chi s (n + 1) : ℝ) := by exact_mod_cast rfl
      rw [hcast]
      ring

lemma mod_div (n a : ℕ) (ha : 0 < a) :
    ↑(n % a) / (a : ℝ) = (n : ℝ) / a - ↑(n / a) := by
  have h := Nat.div_add_mod n a
  have hcast : (n : ℝ) = (a : ℝ) * ↑(n / a) + ↑(n % a) := by
    simpa [Nat.cast_add, Nat.cast_mul] using congrArg (fun k : ℕ => (k : ℝ)) h.symm
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [eq_sub_iff_add_eq]
  field_simp [ha0]
  linarith

lemma conv (s n : ℕ) :
    ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (chi s a : ℝ) =
      ∑ a ∈ Icc 1 n, (chi s a : ℝ) * (n / a : ℕ) := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  · have hrewrite (k : ℕ) (hk : k ∈ Icc 1 n) :
        ∑ a ∈ k.divisors, (chi s a : ℝ) =
          ∑ a ∈ Icc 1 n, if a ∣ k then (chi s a : ℝ) else 0 := by
      have hk0 : k ≠ 0 := by
        simp only [mem_Icc] at hk
        omega
      have hk' : 1 ≤ k ∧ k ≤ n := by simpa [mem_Icc] using hk
      have hset : k.divisors = (Icc 1 n).filter (fun a => a ∣ k) := by
        ext a
        simp only [Nat.mem_divisors, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hd, _⟩
          have ha : 0 < a := Nat.pos_of_dvd_of_pos hd (by omega)
          have hale : a ≤ k := Nat.le_of_dvd (by omega) hd
          exact ⟨⟨ha, le_trans hale hk'.2⟩, hd⟩
        · rintro ⟨⟨_, _⟩, hd⟩
          exact ⟨hd, hk0⟩
      rw [hset, sum_filter]
    rw [sum_congr rfl hrewrite, sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    refine congrArg (fun t : ℝ => (chi s a : ℝ) * t) ?_
    have hset : (Icc 1 n).filter (fun k => a ∣ k) =
        (Ioc 0 n).filter (fun k => a ∣ k) := by
      ext k
      simp only [mem_filter, mem_Icc, mem_Ioc]
      omega
    have hcard : ((Icc 1 n).filter (fun k => a ∣ k)).card = n / a := by
      rw [hset]
      exact Nat.Ioc_filter_dvd_card_eq_div n a
    exact_mod_cast hcard

lemma harm_eq (m : ℕ) :
    ∑ j ∈ Icc 1 m, (1 : ℝ) / j = ∑ i ∈ range m, (1 : ℝ) / (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_Icc_succ_top (by omega : (1 : ℕ) ≤ m + 1), ih]
    simp [Nat.cast_add, add_comm]

lemma block_sum (s q : ℕ) :
    series s (q * s) =
      ∑ j ∈ range q, ∑ r ∈ Icc 1 s, (chi s (j * s + r) : ℝ) / (j * s + r) := by
  induction q with
  | zero => simp [series]
  | succ q ih =>
    have hstep : (q + 1) * s = q * s + s := by ring
    rw [hstep, series_add, ih, sum_range_succ]
    simp [Nat.cast_mul]

lemma series_tail_le (hs : 1 < s) (hσ : ∑ r ∈ Icc 1 s, chi s r = 0)
    (T n : ℕ) (hT : 0 < T) (hTn : T < n) :
    |series s n - series s T| ≤ 2 * (s : ℝ) / T := by
  have hn : 0 < n := by omega
  rw [abel s n hn, abel s T hT]
  have hsplit : Icc 1 (n - 1) = Icc 1 (T - 1) ∪ Icc T (n - 1) := by
    ext a
    simp only [mem_union, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 (T - 1)) (Icc T (n - 1)) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_Icc] at ha hb
    omega
  rw [hsplit, sum_union hdisj]
  have hbound (a : ℕ) : |(cum s a : ℝ)| ≤ s := abs_cum_le hs hσ a
  have hsumle : |∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1))| ≤
      (s : ℝ) * (1 / T - 1 / (n : ℝ)) := by
    calc
      |∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1))| ≤
          ∑ a ∈ Icc T (n - 1), |(cum s a : ℝ) / (a * (a + 1))| := by
        exact abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Icc T (n - 1), |(cum s a : ℝ)| / (a * (a + 1)) := by
        apply sum_congr rfl
        intro a ha
        have ha0 : 0 < a := by simp only [mem_Icc] at ha; omega
        have hpos : (0 : ℝ) < (a : ℝ) * ((a : ℝ) + 1) :=
          mul_pos (by exact_mod_cast ha0) (by exact_mod_cast (show 0 < a + 1 by omega))
        rw [abs_div, abs_of_pos hpos]
      _ ≤ ∑ a ∈ Icc T (n - 1), (s : ℝ) / (a * (a + 1)) := by
        apply sum_le_sum
        intro a ha
        have ha0 : 0 < a := by simp only [mem_Icc] at ha; omega
        have hpos : (0 : ℝ) ≤ (a : ℝ) * ((a : ℝ) + 1) :=
          le_of_lt (mul_pos (by exact_mod_cast ha0) (by exact_mod_cast (show 0 < a + 1 by omega)))
        exact div_le_div_of_nonneg_right (hbound a) hpos
      _ = (s : ℝ) * ∑ a ∈ Icc T (n - 1), (1 : ℝ) / (a * (a + 1)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
      _ = (s : ℝ) * ∑ a ∈ Icc T (n - 1), (1 / a - 1 / (a + 1 : ℝ)) := by
        congr 1
        apply sum_congr rfl
        intro a ha
        exact inv_mul_succ a (by simp only [mem_Icc] at ha; omega)
      _ = (s : ℝ) * (1 / T - 1 / (n : ℝ)) := by
        congr 1
        have htel := sum_diff T (n - 1) (by omega) (fun a => (1 : ℝ) / a)
        have hn1 : (n - 1) + 1 = n := by omega
        simpa [hn1] using htel
  have hmain : |(cum s n : ℝ) / n - (cum s T : ℝ) / T| ≤ (s : ℝ) / n + (s : ℝ) / T := by
    calc
      |(cum s n : ℝ) / n - (cum s T : ℝ) / T| ≤
          |(cum s n : ℝ) / n| + |(cum s T : ℝ) / T| := by
        exact abs_sub _ _
      _ = |(cum s n : ℝ)| / n + |(cum s T : ℝ)| / T := by
        rw [abs_div, abs_div, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n),
          abs_of_pos (by exact_mod_cast hT : (0 : ℝ) < T)]
      _ ≤ (s : ℝ) / n + (s : ℝ) / T := by
        gcongr
        · exact hbound n
        · exact hbound T
  have hrearr :
      (cum s n : ℝ) / n +
        (∑ a ∈ Icc 1 (T - 1), (cum s a : ℝ) / (a * (a + 1)) +
          ∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1))) -
        ((cum s T : ℝ) / T + ∑ a ∈ Icc 1 (T - 1), (cum s a : ℝ) / (a * (a + 1))) =
      (cum s n : ℝ) / n - (cum s T : ℝ) / T +
        ∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1)) := by
    ring
  rw [hrearr]
  have hgoal :
      |(cum s n : ℝ) / n - (cum s T : ℝ) / T +
        ∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1))| ≤
      (s : ℝ) / n + (s : ℝ) / T + (s : ℝ) * (1 / T - 1 / (n : ℝ)) := by
    calc
      _ ≤ |(cum s n : ℝ) / n - (cum s T : ℝ) / T| +
          |∑ a ∈ Icc T (n - 1), (cum s a : ℝ) / (a * (a + 1))| := by
        exact abs_add_le _ _
      _ ≤ (s : ℝ) / n + (s : ℝ) / T + (s : ℝ) * (1 / T - 1 / (n : ℝ)) := by
        linarith [hmain, hsumle]
  have hsimp : (s : ℝ) / n + s / T + s * (1 / T - 1 / (n : ℝ)) = 2 * s / T := by
    field_simp
    ring
  linarith [hgoal, hsimp]

lemma floor_sum_le (hs : 1 < s) (hσ : ∑ r ∈ Icc 1 s, chi s r = 0)
    (T n : ℕ) (hTn : T < n) :
    |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (n / a : ℕ)| ≤
      2 * (s : ℝ) * (n / (T + 1) : ℕ) := by
  let f : ℕ → ℝ := fun a => (n / a : ℕ)
  have hf0 : ∀ a, T < a → a ≤ n → 0 ≤ f a := by
    intro a _ _
    exact Nat.cast_nonneg _
  have hfanti : ∀ a, T < a → a < n → f (a + 1) ≤ f a := by
    intro a _ _
    have hdiv : n / (a + 1) ≤ n / a :=
      Nat.div_le_div_left (Nat.le_succ a) (by omega : 0 < a)
    simpa [f] using (by exact_mod_cast hdiv : ((n / (a + 1) : ℕ) : ℝ) ≤ ↑(n / a))
  rw [weighted s T f n hTn]
  have hB (a : ℕ) : |(cum s a : ℝ)| ≤ s := abs_cum_le hs hσ a
  have htel : ∑ a ∈ Icc (T + 1) (n - 1), (f a - f (a + 1)) = f (T + 1) - f n := by
    by_cases h : T + 1 ≤ n - 1
    · have hdiff := sum_diff (T + 1) (n - 1) h f
      have hn1 : (n - 1) + 1 = n := by omega
      simpa [hn1] using hdiff
    · rw [Icc_eq_empty_iff.mpr h, sum_empty]
      have hn : n = T + 1 := by omega
      simp [f, hn]
  have hdiff_nonneg : ∀ a ∈ Icc (T + 1) (n - 1), 0 ≤ f a - f (a + 1) := by
    intro a ha
    simp only [mem_Icc] at ha
    have : f (a + 1) ≤ f a := hfanti a (by omega) (by omega)
    linarith
  have hsumle : |∑ a ∈ Icc (T + 1) (n - 1), (cum s a : ℝ) * (f a - f (a + 1))| ≤
      (s : ℝ) * (f (T + 1) - f n) := by
    calc
      _ ≤ ∑ a ∈ Icc (T + 1) (n - 1), |(cum s a : ℝ) * (f a - f (a + 1))| := by
        exact abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Icc (T + 1) (n - 1), |(cum s a : ℝ)| * (f a - f (a + 1)) := by
        apply sum_congr rfl
        intro a ha
        rw [abs_mul, abs_of_nonneg (hdiff_nonneg a ha)]
      _ ≤ ∑ a ∈ Icc (T + 1) (n - 1), (s : ℝ) * (f a - f (a + 1)) := by
        apply sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_right (hB a) (hdiff_nonneg a ha)
      _ = (s : ℝ) * (f (T + 1) - f n) := by
        rw [← htel, mul_sum]
  have hfn : 0 ≤ f n := Nat.cast_nonneg _
  have hfT : 0 ≤ f (T + 1) := Nat.cast_nonneg _
  have hfirst : |(cum s n : ℝ) * f n| ≤ (s : ℝ) * f n := by
    rw [abs_mul, abs_of_nonneg hfn]
    exact mul_le_mul_of_nonneg_right (hB n) hfn
  have hsecond : |(cum s T : ℝ) * f (T + 1)| ≤ (s : ℝ) * f (T + 1) := by
    rw [abs_mul, abs_of_nonneg hfT]
    exact mul_le_mul_of_nonneg_right (hB T) hfT
  have habs : |(cum s n : ℝ) * f n - (cum s T : ℝ) * f (T + 1) +
      ∑ a ∈ Icc (T + 1) (n - 1), (cum s a : ℝ) * (f a - f (a + 1))| ≤
      (s : ℝ) * f n + (s : ℝ) * f (T + 1) + (s : ℝ) * (f (T + 1) - f n) := by
    calc
      _ ≤ |(cum s n : ℝ) * f n - (cum s T : ℝ) * f (T + 1)| +
          |∑ a ∈ Icc (T + 1) (n - 1), (cum s a : ℝ) * (f a - f (a + 1))| := by
        exact abs_add_le _ _
      _ ≤ |(cum s n : ℝ) * f n| + |(cum s T : ℝ) * f (T + 1)| +
          (s : ℝ) * (f (T + 1) - f n) := by
        have := abs_sub ((cum s n : ℝ) * f n) ((cum s T : ℝ) * f (T + 1))
        linarith [hsumle, this]
      _ ≤ (s : ℝ) * f n + (s : ℝ) * f (T + 1) + (s : ℝ) * (f (T + 1) - f n) := by
        linarith
  have hcancel : (s : ℝ) * f n + s * f (T + 1) + s * (f (T + 1) - f n) =
      2 * s * f (T + 1) := by ring
  calc
    _ ≤ (s : ℝ) * f n + (s : ℝ) * f (T + 1) + (s : ℝ) * (f (T + 1) - f n) := habs
    _ = 2 * (s : ℝ) * f (T + 1) := hcancel

lemma err_ratio (hs : 1 < s) (hσ : ∑ r ∈ Icc 1 s, chi s r = 0) (n : ℕ) (hn : 0 < n) :
    |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤
      (1 + 4 * (s : ℝ)) / Nat.sqrt n := by
  let T := Nat.sqrt n
  have hTle : T ≤ n := Nat.sqrt_le_self n
  have hTpos : 0 < T := by
    rw [Nat.sqrt_pos]
    exact hn
  have hsq : T * T ≤ n := Nat.sqrt_le n
  have hsmall : |∑ a ∈ Icc 1 T, (chi s a : ℝ) * (↑(n % a) / a)| ≤ T := by
    calc
      _ ≤ ∑ a ∈ Icc 1 T, |(chi s a : ℝ) * (↑(n % a) / a)| := by
        exact abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Icc 1 T, 1 := by
        apply sum_le_sum
        intro a ha
        have ha0 : 0 < a := by simp only [mem_Icc] at ha; omega
        have hmod : n % a < a := Nat.mod_lt n ha0
        have hfrac : |↑(n % a) / (a : ℝ)| ≤ 1 := by
          have hden : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
          rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (n % a)), abs_of_pos hden, div_le_one₀ hden]
          exact_mod_cast hmod.le
        have hchi : |(chi s a : ℝ)| ≤ 1 := by exact_mod_cast abs_chi_le s a
        rw [abs_mul]
        have hnonneg : (0 : ℝ) ≤ |(chi s a : ℝ)| := abs_nonneg _
        nlinarith [hchi, hfrac]
      _ = ((Icc 1 T).card : ℝ) := by simp
      _ ≤ T := by
        exact_mod_cast (by rw [Nat.card_Icc]; omega : (Icc 1 T).card ≤ T)
  have hsplit : Icc 1 n = Icc 1 T ∪ Icc (T + 1) n := by
    ext a
    simp only [mem_union, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 T) (Icc (T + 1) n) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_Icc] at ha hb
    omega
  have hE : ∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a) =
      ∑ a ∈ Icc 1 T, (chi s a : ℝ) * (↑(n % a) / a) +
        ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (↑(n % a) / a) := by
    rw [← sum_union hdisj, hsplit]
  have hpoint : ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (↑(n % a) / a) =
      (n : ℝ) * ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) / a -
        ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (n / a : ℕ) := by
    have hterm (a : ℕ) (ha : a ∈ Icc (T + 1) n) :
        (chi s a : ℝ) * (↑(n % a) / a) =
          (n : ℝ) * ((chi s a : ℝ) / a) - (chi s a : ℝ) * (n / a : ℕ) := by
      have ha0 : 0 < a := by simp only [mem_Icc] at ha; omega
      rw [mod_div n a ha0]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib]
    congr 1
    rw [mul_sum]
  have htail_id : ∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) / a = series s n - series s T := by
    unfold series
    have : Icc 1 n = Icc 1 T ∪ Icc (T + 1) n := hsplit
    rw [this, sum_union hdisj]
    ring
  by_cases hTn : n ≤ T
  · have hnT : n = T := le_antisymm hTn hTle
    have hempty : Icc (T + 1) n = ∅ := Icc_eq_empty_iff.mpr (by omega)
    have hnum : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| ≤ (T : ℝ) := by
      rw [hE, hempty, sum_empty, add_zero]
      exact hsmall
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤ (T : ℝ) / n :=
      div_le_div_of_nonneg_right hnum (le_of_lt hn0)
    have hsq' : T * T ≤ 1 * n := by simpa using hsq
    have hsqrt : (T : ℝ) / n ≤ 1 / T := by
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
      rw [div_le_div_iff₀ hn0 hT0]
      exact_mod_cast hsq'
    have hC : (1 : ℝ) / T ≤ (1 + 4 * (s : ℝ)) / T := by
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
      rw [div_le_div_iff_of_pos_right hT0]
      have : (0 : ℝ) ≤ 4 * s := by positivity
      linarith
    have : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤
        (1 + 4 * (s : ℝ)) / T := by linarith
    simpa [T] using this
  · have hlt : T < n := by omega
    have htail : |series s n - series s T| ≤ 2 * (s : ℝ) / T :=
      series_tail_le hs hσ T n hTpos hlt
    have hfloor : |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (n / a : ℕ)| ≤
        2 * (s : ℝ) * (n / (T + 1) : ℕ) := floor_sum_le hs hσ T n hlt
    have hfloor' : |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (n / a : ℕ)| ≤
        2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
      have hcast : ((n / (T + 1) : ℕ) : ℝ) ≤ (n : ℝ) / ↑(T + 1) := Nat.cast_div_le
      have hcast' : ((n / (T + 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((T : ℝ) + 1) := by
        simpa [Nat.cast_add] using hcast
      have hs0 : (0 : ℝ) ≤ 2 * s := by positivity
      have : 2 * (s : ℝ) * ↑(n / (T + 1)) ≤
          2 * (s : ℝ) * ((n : ℝ) / ((T : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcast' hs0
      linarith [hfloor, this]
    have hlarge : |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (↑(n % a) / a)| ≤
        (n : ℝ) * (2 * (s : ℝ) / T) + 2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
      rw [hpoint, htail_id]
      calc
        _ ≤ |(n : ℝ) * (series s n - series s T)| +
            |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (n / a : ℕ)| := by
          exact abs_sub _ _
        _ ≤ (n : ℝ) * |series s n - series s T| +
            2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
          linarith [htail, hfloor']
        _ ≤ (n : ℝ) * (2 * (s : ℝ) / T) + 2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
          gcongr
    have hEabs : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| ≤
        (T : ℝ) + (n : ℝ) * (2 * (s : ℝ) / T) + 2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
      rw [hE]
      calc
        _ ≤ |∑ a ∈ Icc 1 T, (chi s a : ℝ) * (↑(n % a) / a)| +
            |∑ a ∈ Icc (T + 1) n, (chi s a : ℝ) * (↑(n % a) / a)| := by
          exact abs_add_le _ _
        _ ≤ T + ((n : ℝ) * (2 * (s : ℝ) / T) + 2 * (s : ℝ) * ((n : ℝ) / (T + 1))) := by
          linarith [hsmall, hlarge]
        _ = (T : ℝ) + (n : ℝ) * (2 * (s : ℝ) / T) +
            2 * (s : ℝ) * ((n : ℝ) / (T + 1)) := by
          ring
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤
        (T : ℝ) / n + 2 * (s : ℝ) / T + 2 * (s : ℝ) / (T + 1) := by
      have hle := div_le_div_of_nonneg_right hEabs (le_of_lt hn0)
      have hmul : ((T : ℝ) + (n : ℝ) * (2 * (s : ℝ) / T) +
          2 * (s : ℝ) * ((n : ℝ) / (T + 1))) / n =
          (T : ℝ) / n + 2 * (s : ℝ) / T + 2 * (s : ℝ) / (T + 1) := by
        field_simp
      linarith [hle, hmul]
    have hTdiv : (T : ℝ) / n ≤ 1 / T := by
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
      have hsq' : T * T ≤ 1 * n := by simpa using hsq
      rw [div_le_div_iff₀ hn0 hT0]
      exact_mod_cast hsq'
    have hlast : 2 * (s : ℝ) / (T + 1) ≤ 2 * (s : ℝ) / T := by
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
      have hT1 : (0 : ℝ) < T + 1 := by linarith
      have hs0 : (0 : ℝ) ≤ 2 * s := by positivity
      exact div_le_div_of_nonneg_left hs0 hT0 (by linarith : (T : ℝ) ≤ T + 1)
    have : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤
        (1 + 4 * (s : ℝ)) / T := by
      have : (T : ℝ) / n + 2 * s / T + 2 * s / (T + 1) ≤ 1 / T + 2 * s / T + 2 * s / T := by
        linarith
      have hsum : (1 : ℝ) / T + 2 * s / T + 2 * s / T = (1 + 4 * s) / T := by
        field_simp
        ring
      linarith
    simpa [T] using this

lemma period_sum_zero (hs : 1 < s) {L : ℝ}
    (hL : Tendsto (fun N => series s N) atTop (𝓝 L)) :
    ∑ r ∈ Icc 1 s, chi s r = 0 := by
  by_contra hσ
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hσR : (∑ r ∈ Icc 1 s, chi s r : ℝ) ≠ 0 := by exact_mod_cast hσ
  have hc : (0 : ℝ) < |(∑ r ∈ Icc 1 s, chi s r : ℝ) / s| := by
    rw [abs_pos, div_ne_zero_iff]
    exact ⟨hσR, by exact_mod_cast (show s ≠ 0 by omega)⟩
  let σ : ℤ := ∑ r ∈ Icc 1 s, chi s r
  let C0 : ℝ := ∑ r ∈ Icc 1 s, (chi s r : ℝ) / r
  let K : ℝ := |C0| + 2
  have herr (q : ℕ) (hq : 0 < q) :
      |series s (q * s) - (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j| ≤ K := by
    rw [block_sum]
    have hrange : range q = insert 0 (Icc 1 (q - 1)) := by
      ext j
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    have hnot : 0 ∉ Icc 1 (q - 1) := by
      simp only [mem_Icc, not_and, not_le]
      omega
    rw [hrange, sum_insert hnot]
    have hzero : ∑ r ∈ Icc 1 s, (chi s (0 * s + r) : ℝ) / (↑(0 : ℕ) * ↑s + ↑r) = C0 := by
      simp [C0, zero_mul, zero_add]
    rw [hzero]
    have hrest : ∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
        (chi s (j * s + r) : ℝ) / (j * s + r) =
        ∑ j ∈ Icc 1 (q - 1), ((σ : ℝ) / (j * s) -
          ∑ r ∈ Icc 1 s, (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))) := by
      apply sum_congr rfl
      intro j hj
      have hj0 : 0 < j := by simp only [mem_Icc] at hj; omega
      have hterm (r : ℕ) (hr : r ∈ Icc 1 s) :
          (chi s (j * s + r) : ℝ) / (j * s + r) =
            (chi s r : ℝ) / (j * s) -
              (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r)) := by
        rw [chi_mul_add]
        have hr0 : (0 : ℝ) < r := by simp only [mem_Icc] at hr; exact_mod_cast (by omega : 0 < r)
        have hjs : (0 : ℝ) < j * s := by positivity
        have hden : (j * s + r : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [sum_congr rfl hterm, sum_sub_distrib]
      congr 1
      rw [← sum_div]
      simp [σ]
    rw [hrest, sum_sub_distrib]
    have hcoef : ∑ j ∈ Icc 1 (q - 1), (σ : ℝ) / (j * s) =
        (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hj0 : (j : ℝ) ≠ 0 := by
        simp only [mem_Icc] at hj
        exact_mod_cast (by omega : j ≠ 0)
      have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
      field_simp
    rw [hcoef]
    have hEj : |∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
        (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))| ≤
        ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / (j : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ j ∈ Icc 1 (q - 1), |∑ r ∈ Icc 1 s,
            (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))| := by
          exact abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
            |(chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))| := by
          apply sum_le_sum
          intro j _
          exact abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / (j : ℝ) ^ 2 := by
          apply sum_le_sum
          intro j hj
          have hj0 : 0 < j := by simp only [mem_Icc] at hj; omega
          calc
            ∑ r ∈ Icc 1 s, |(chi s r : ℝ) * (r : ℝ) /
                ((j * s : ℝ) * (j * s + r))| ≤
                ∑ r ∈ Icc 1 s, (s : ℝ) / ((j * s : ℝ) * (j * s)) := by
              apply sum_le_sum
              intro r hr
              have hr0 : 0 < r := by simp only [mem_Icc] at hr; omega
              have hrs : r ≤ s := by simp only [mem_Icc] at hr; omega
              have hchi : |(chi s r : ℝ)| ≤ 1 := by exact_mod_cast abs_chi_le s r
              have hdenpos : (0 : ℝ) < (j * s : ℝ) * (j * s + r) := by positivity
              have hden2 : (0 : ℝ) < (j * s : ℝ) * (j * s) := by positivity
              rw [abs_div]
              rw [abs_of_pos hdenpos]
              rw [abs_mul]
              have hrabs : |(r : ℝ)| = r := abs_of_nonneg (Nat.cast_nonneg r)
              rw [hrabs]
              have hcmp : (j * s : ℝ) * (j * s) ≤ (j * s : ℝ) * (j * s + r) := by
                have : (0 : ℝ) ≤ j * s := by positivity
                have : (j * s : ℝ) ≤ j * s + r := by linarith [show (0 : ℝ) ≤ r by exact Nat.cast_nonneg r]
                nlinarith
              have habs : |(chi s r : ℝ)| * r / ((j * s : ℝ) * (j * s + r)) ≤
                  (s : ℝ) / ((j * s : ℝ) * (j * s)) := by
                have hrle : (r : ℝ) ≤ s := by exact_mod_cast hrs
                calc
                  |(chi s r : ℝ)| * r / ((j * s : ℝ) * (j * s + r)) ≤
                      1 * (s : ℝ) / ((j * s : ℝ) * (j * s + r)) := by
                    gcongr
                  _ ≤ (s : ℝ) / ((j * s : ℝ) * (j * s)) := by
                    rw [one_mul]
                    exact div_le_div_of_nonneg_left (by exact Nat.cast_nonneg s) hden2 hcmp
              exact habs
            _ = (1 : ℝ) / (j : ℝ) ^ 2 := by
              have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
              have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast hj0.ne'
              rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
              have hcard : s + 1 - 1 = s := by omega
              rw [hcard]
              field_simp [hsne, hjne]
    have hsq : ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := sum_inv_sq_le (q - 1)
    have : |C0 - ∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
        (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))| ≤ |C0| +
        ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / (j : ℝ) ^ 2 := by
      calc
        _ ≤ |C0| + |∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
            (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))| := abs_sub _ _
        _ ≤ |C0| + ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / (j : ℝ) ^ 2 := by linarith
    have hrearr :
        C0 + ((σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j -
            ∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
              (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r))) -
          (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j =
        C0 - ∑ j ∈ Icc 1 (q - 1), ∑ r ∈ Icc 1 s,
          (chi s r : ℝ) * r / ((j * s : ℝ) * (j * s + r)) := by
      ring
    rw [hrearr]
    linarith [this, hsq]
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨N, hN⟩ := hL 1 (by norm_num)
  have hharm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [tendsto_atTop_atTop] at hharm
  let thresh : ℝ := (K + |L| + 2) / |(σ : ℝ) / s|
  obtain ⟨M, hM⟩ := hharm (thresh + 1)
  let q := max (M + 1) (max N 1)
  have hq1 : 1 ≤ q := by
    have : 1 ≤ max N 1 := le_max_right _ _
    exact le_trans this (le_max_right _ _)
  have hqM : M ≤ q - 1 := by omega
  have hgrow : thresh + 1 ≤ ∑ i ∈ range (q - 1), (1 : ℝ) / (i + 1) := hM (q - 1) hqM
  have hharmq : thresh + 1 ≤ ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j := by
    rw [harm_eq]
    exact hgrow
  have herrq := herr q (by omega)
  have hqs : N ≤ q * s := by
    have hNq : N ≤ q := le_trans (le_max_left _ _) (le_max_right _ _)
    have hs1 : 1 ≤ s := by omega
    calc
      N ≤ q := hNq
      _ ≤ q * s := Nat.le_mul_of_pos_right q (by omega : 0 < s)
  have hclose := hN (q * s) hqs
  have hclose' : |series s (q * s) - L| < 1 := by
    simpa [Real.dist_eq] using hclose
  have hσcast : (σ : ℝ) = ∑ r ∈ Icc 1 s, (chi s r : ℝ) := by
    simp only [σ, Int.cast_sum]
  have hcoef : (0 : ℝ) < |(σ : ℝ) / s| := by
    rw [hσcast]
    exact hc
  by_cases hsign : 0 < (σ : ℝ)
  · have hlow : series s (q * s) ≥ (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j - K := by
      have := abs_le.mp herrq
      linarith
    have hposc : (σ : ℝ) / s = |(σ : ℝ) / s| := by
      rw [abs_of_pos (div_pos hsign hs0)]
    have hbig : (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j - K > |L| + 2 := by
      rw [hposc]
      have hmul : |(σ : ℝ) / s| * (thresh + 1) ≤
          |(σ : ℝ) / s| * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j :=
        mul_le_mul_of_nonneg_left hharmq (le_of_lt hcoef)
      have hth : |(σ : ℝ) / s| * thresh = K + |L| + 2 := by
        unfold thresh
        field_simp
      linarith
    have hgt : series s (q * s) > |L| + 2 := by linarith
    have hdiff : (1 : ℝ) < series s (q * s) - L := by
      have : L ≤ |L| := le_abs_self L
      linarith
    have : (1 : ℝ) < |series s (q * s) - L| := lt_abs.mpr (Or.inl hdiff)
    linarith
  · have hneg : (σ : ℝ) < 0 := by
      have hne : (σ : ℝ) ≠ 0 := by exact_mod_cast hσ
      exact lt_of_le_of_ne (le_of_not_gt hsign) hne
    have hup : series s (q * s) ≤ (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j + K := by
      have := abs_le.mp herrq
      linarith
    have hnegc : (σ : ℝ) / s = -|(σ : ℝ) / s| := by
      rw [abs_of_neg (div_neg_of_neg_of_pos hneg hs0)]
      ring
    have hsmall : (σ : ℝ) / s * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j + K < -(|L| + 2) := by
      rw [hnegc]
      have hmul : |(σ : ℝ) / s| * (thresh + 1) ≤
          |(σ : ℝ) / s| * ∑ j ∈ Icc 1 (q - 1), (1 : ℝ) / j :=
        mul_le_mul_of_nonneg_left hharmq (le_of_lt hcoef)
      have hth : |(σ : ℝ) / s| * thresh = K + |L| + 2 := by
        unfold thresh
        field_simp
      linarith
    have hlt : series s (q * s) < -(|L| + 2) := by linarith
    have hdiff : (1 : ℝ) < -(series s (q * s) - L) := by
      have : -|L| ≤ L := neg_abs_le L
      linarith
    have : (1 : ℝ) < |series s (q * s) - L| := lt_abs.mpr (Or.inr hdiff)
    linarith

end Erdos338Hyperbola

open Erdos338Hyperbola

theorem OMA.solution :
    OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H3 := by
  intro s hs hmod L hL
  have hs1 : 1 < s := by
    have hdiv : s = 8 * (s / 8) + s % 8 := (Nat.div_add_mod s 8).symm
    omega
  have hσ : ∑ r ∈ Icc 1 s, chi s r = 0 := period_sum_zero hs1 hL
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rw [Metric.tendsto_atTop] at hL
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N1, hN1⟩ := hL (ε / 2) hε2
  let C : ℝ := 1 + 4 * s
  have hCpos : 0 < C := by positivity
  obtain ⟨T0, hT0⟩ := exists_nat_gt (C / (ε / 2))
  have hT0pos : 0 < T0 := by
    have hnonneg : (0 : ℝ) ≤ C / (ε / 2) := by positivity
    have : (0 : ℝ) < T0 := lt_of_le_of_lt hnonneg hT0
    exact_mod_cast this
  have hT0lt : C / (T0 : ℝ) < ε / 2 := by
    have hTp : (0 : ℝ) < T0 := by exact_mod_cast hT0pos
    have hmul : C < (ε / 2) * (T0 : ℝ) := by
      have : C < (T0 : ℝ) * (ε / 2) := by
        rwa [div_lt_iff₀ hε2] at hT0
      linarith
    rwa [div_lt_iff₀ hTp]
  refine ⟨max N1 (T0 ^ 2), ?_⟩
  intro n hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hnT : T0 ^ 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by
    have : 0 < T0 ^ 2 := by
      have : 0 < T0 := hT0pos
      exact Nat.pow_pos this
    omega
  have hclose := hN1 n hn1
  have herr := err_ratio hs1 hσ n hn0
  have hsq : (T0 : ℝ) ≤ Nat.sqrt n := by
    exact_mod_cast Nat.le_sqrt.mpr (by simpa [Nat.pow_two] using hnT)
  have hsqrtpos : (0 : ℝ) < Nat.sqrt n := by
    have : (0 : ℝ) < T0 := by exact_mod_cast hT0pos
    linarith
  have hratio : (1 + 4 * (s : ℝ)) / Nat.sqrt n ≤ C / T0 := by
    dsimp [C]
    apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hT0pos) hsq
  have hconv : ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (chi s a : ℝ) =
      ∑ a ∈ Icc 1 n, (chi s a : ℝ) * (n / a : ℕ) := conv s n
  have hE : ∑ a ∈ Icc 1 n, (chi s a : ℝ) * (n / a : ℕ) =
      (n : ℝ) * series s n -
        ∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a) := by
    have hterm (a : ℕ) (ha : a ∈ Icc 1 n) :
        (chi s a : ℝ) * (n / a : ℕ) =
          (n : ℝ) * ((chi s a : ℝ) / a) -
            (chi s a : ℝ) * (↑(n % a) / a) := by
      have ha0 : 0 < a := by simp only [mem_Icc] at ha; omega
      have hmod := (mod_div n a ha0).symm
      -- (n/a : ℕ) = n/a - (n%a)/a
      have : (n / a : ℕ) = (n : ℝ) / a - ↑(n % a) / a := by
        linarith
      rw [this]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib]
    unfold series
    rw [← Finset.mul_sum]
  have havg : (∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (jacobiSym a s : ℝ)) / n -
      series s n =
      -(∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)) / n := by
    have hchi : ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (jacobiSym (a : ℤ) s : ℝ) =
        ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (chi s a : ℝ) := by rfl
    -- jacobiSym a s is definitionally jacobiSym (a : ℤ) s
    rw [hconv, hE]
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    field_simp
    ring
  have herr' : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤ ε / 2 := by
    have : |∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)| / n ≤
        (1 + 4 * (s : ℝ)) / Nat.sqrt n := herr
    linarith
  have : |(∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (jacobiSym a s : ℝ)) / n - L| < ε := by
    have hdiff : |(∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (jacobiSym a s : ℝ)) / n -
        series s n| ≤ ε / 2 := by
      rw [havg]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [show (-∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)) / n =
          -((∑ a ∈ Icc 1 n, (chi s a : ℝ) * (↑(n % a) / a)) / n) by ring,
        abs_neg, abs_div, abs_of_pos hnR]
      exact herr'
    have hseries : |series s n - L| < ε / 2 := hclose
    have := abs_sub_le ((∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, (jacobiSym a s : ℝ)) / n)
      (series s n) L
    linarith
  exact this
