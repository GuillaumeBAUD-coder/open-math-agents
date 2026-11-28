import OMAStatements.S_oeis_a381737
import Mathlib

namespace A381737P
open Polynomial OMA.S_oeis_a381737

lemma H_ss (n : ℕ) : H (n + 2) = C 2 * X * H (n + 1) - C (2 * ((n : ℤ) + 1)) * H n := by
  rw [H]

lemma deriv_H : ∀ n : ℕ, derivative (H (n + 1)) = C (2 * ((n : ℤ) + 1)) * H n
  | 0 => by simp [H]
  | 1 => by
    rw [H_ss]; simp [H]; ring
  | n + 2 => by
    rw [H_ss, derivative_sub, derivative_mul, derivative_mul, derivative_mul,
      deriv_H (n + 1), deriv_H n, H_ss n]
    simp only [derivative_C, derivative_X]
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]
    push_cast
    ring

lemma H_succ (n : ℕ) : H (n + 1) = C 2 * X * H n - derivative (H n) := by
  cases n with
  | zero => simp [H]
  | succ n => rw [H_ss, deriv_H]

lemma coeff_H_succ_zero (n : ℕ) : (H (n + 1)).coeff 0 = -(H n).coeff 1 := by
  rw [H_succ, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul_zero, coeff_derivative]
  simp

lemma coeff_H_succ_succ (n i : ℕ) : (H (n + 1)).coeff (i + 1) =
    2 * (H n).coeff i - (i + 2) * (H n).coeff (i + 2) := by
  rw [H_succ, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_derivative]
  push_cast
  ring

lemma coeff_H_eq (n i : ℕ) : (H n).coeff i = 2 ^ ((n + i) / 2) * (hermite n).coeff i := by
  induction n generalizing i with
  | zero =>
    rcases i with _ | i
    · simp [H]
    · simp [H, coeff_one]
  | succ n ih =>
    rcases i with _ | i
    · rw [coeff_H_succ_zero, coeff_hermite_succ_zero, ih]
      simp
    · rw [coeff_H_succ_succ, coeff_hermite_succ_succ, ih, ih,
        show (n + 1 + (i + 1)) / 2 = (n + i) / 2 + 1 by omega,
        show (n + (i + 2)) / 2 = (n + i) / 2 + 1 by omega]
      ring

open scoped Nat in
lemma coeff_H_explicit (j i : ℕ) : (H (2 * j + i)).coeff i =
    (-1) ^ j * (2 ^ (j + i) * (2 * j - 1)‼ * Nat.choose (2 * j + i) i : ℕ) := by
  rw [coeff_H_eq, coeff_hermite_explicit, show (2 * j + i + i) / 2 = j + i by omega]
  push_cast
  ring

lemma coeff_H_odd {n i : ℕ} (h : Odd (n + i)) : (H n).coeff i = 0 := by
  rw [coeff_H_eq, coeff_hermite_of_odd_add h, mul_zero]

lemma coeff_H_lt {n i : ℕ} (h : n < i) : (H n).coeff i = 0 := by
  rw [coeff_H_eq, coeff_hermite_of_lt h, mul_zero]


open scoped Nat

/-- absolute value of the coefficient of `x^(k-2j)` in `H k`. -/
def g (k j : ℕ) : ℕ := 2 ^ (k - j) * (2 * j - 1)‼ * Nat.choose k (2 * j)

lemma natAbs_coeff (k j : ℕ) (h : 2 * j ≤ k) : ((H k).coeff (k - 2 * j)).natAbs = g k j := by
  obtain ⟨i, rfl⟩ : ∃ i, k = 2 * j + i := ⟨k - 2 * j, by omega⟩
  rw [show 2 * j + i - 2 * j = i by omega, coeff_H_explicit, Int.natAbs_mul, Int.natAbs_pow]
  simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast]
  unfold g
  rw [show 2 * j + i - j = j + i by omega, Nat.choose_symm_add]

lemma g_pos (k j : ℕ) (h : 2 * j ≤ k) : 0 < g k j := by
  unfold g
  have := Nat.choose_pos h
  have := Nat.doubleFactorial_pos (2 * j - 1)
  positivity

lemma mem_support_H (k i : ℕ) : i ∈ (H k).support ↔ ∃ j, 2 * j ≤ k ∧ i = k - 2 * j := by
  rw [mem_support_iff]
  constructor
  · intro hne
    have hik : i ≤ k := by
      by_contra hc
      exact hne (coeff_H_lt (by omega))
    have hev : Even (k + i) := by
      by_contra hc
      exact hne (coeff_H_odd (Nat.not_even_iff_odd.1 hc))
    obtain ⟨r, hr⟩ := hev
    exact ⟨(k - i) / 2, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩ h0
    have h1 := natAbs_coeff k j hj
    rw [h0] at h1
    have := g_pos k j hj
    simp at h1
    omega

lemma g_ratio (k j : ℕ) (h : 2 * j + 2 ≤ k) :
    g k (j + 1) * (4 * (j + 1)) = g k j * ((k - 2 * j) * (k - 2 * j - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = 2 * j + 2 + r := ⟨k - (2 * j + 2), by omega⟩
  have h1 := Nat.choose_succ_right_eq (2 * j + 2 + r) (2 * j + 1)
  have h2 := Nat.choose_succ_right_eq (2 * j + 2 + r) (2 * j)
  rw [show 2 * j + 2 + r - (2 * j + 1) = r + 1 by omega] at h1
  rw [show 2 * j + 2 + r - 2 * j = r + 2 by omega] at h2
  unfold g
  rw [show 2 * j + 2 + r - (j + 1) = j + 1 + r by omega,
    show 2 * j + 2 + r - j = (j + 1 + r) + 1 by omega,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.doubleFactorial_add_one,
    show 2 * j + 2 + r - 2 * j = r + 2 by omega, show r + 2 - 1 = r + 1 by omega,
    show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
  set D := (2 * j - 1)‼
  set C0 := (2 * j + 2 + r).choose (2 * j)
  set C1 := (2 * j + 2 + r).choose (2 * j + 1)
  set C2 := (2 * j + 2 + r).choose (2 * j + 1 + 1)
  set P := 2 ^ (j + 1 + r)
  calc P * ((2 * j + 1) * D) * C2 * (4 * (j + 1))
      = 2 * P * D * (2 * j + 1) * (C2 * (2 * j + 1 + 1)) := by ring
    _ = 2 * P * D * (r + 1) * (C1 * (2 * j + 1)) := by rw [h1]; ring
    _ = 2 * P * D * (r + 1) * (C0 * (r + 2)) := by rw [h2]
    _ = P * 2 * D * C0 * ((r + 2) * (r + 1)) := by ring
    _ = 2 ^ (j + 1 + r + 1) * D * C0 * ((r + 2) * (r + 1)) := by rw [pow_succ]

def Q (k j : ℕ) : ℕ := (k - 2 * j) * (k - 2 * j - 1)

lemma g_lt_succ (k j : ℕ) (h : 2 * j + 2 ≤ k) (hq : 4 * (j + 1) < Q k j) : g k j < g k (j + 1) := by
  have e := g_ratio k j h
  have := g_pos k j (by omega)
  unfold Q at hq
  have : g k j * (4 * (j + 1)) < g k (j + 1) * (4 * (j + 1)) := by
    rw [e]; exact Nat.mul_lt_mul_of_pos_left hq this
  exact Nat.lt_of_mul_lt_mul_right this

lemma g_succ_lt (k j : ℕ) (h : 2 * j + 2 ≤ k) (hq : Q k j < 4 * (j + 1)) : g k (j + 1) < g k j := by
  have e := g_ratio k j h
  have := g_pos k j (by omega)
  unfold Q at hq
  have : g k (j + 1) * (4 * (j + 1)) < g k j * (4 * (j + 1)) := by
    rw [e]; exact Nat.mul_lt_mul_of_pos_left hq this
  exact Nat.lt_of_mul_lt_mul_right this

lemma g_succ_eq (k j : ℕ) (h : 2 * j + 2 ≤ k) (hq : Q k j = 4 * (j + 1)) : g k (j + 1) = g k j := by
  have e := g_ratio k j h
  unfold Q at hq
  rw [hq] at e
  exact Nat.eq_of_mul_eq_mul_right (by omega) e

lemma Q_strict (k j l : ℕ) (hq : Q k j ≤ 4 * (j + 1)) (hl : j < l) : Q k l < 4 * (l + 1) := by
  unfold Q at *
  have : (k - 2 * l) * (k - 2 * l - 1) ≤ (k - 2 * j) * (k - 2 * j - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

lemma g_dec (k j : ℕ) (hq : Q k j < 4 * (j + 1)) :
    ∀ l, j + 1 ≤ l → 2 * l ≤ k → g k l < g k j := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => intro h; exact g_succ_lt k j (by omega) hq
  | succ l hl ih =>
    intro h
    have h1 := g_succ_lt k l (by omega) (Q_strict k j l hq.le (by omega))
    have h2 := ih (by omega)
    omega

lemma g_inc (k j0 : ℕ) (hk : 2 * j0 ≤ k) (hq : ∀ m, m < j0 → 4 * (m + 1) < Q k m) :
    ∀ d l, l + d = j0 → g k l ≤ g k j0 := by
  intro d
  induction d with
  | zero => intro l h; rw [← h]; simp
  | succ d ih =>
    intro l h
    have h1 := ih (l + 1) (by omega)
    have h2 := g_lt_succ k l (by omega) (hq l (by omega))
    omega


lemma support_eq (k : ℕ) :
    (H k).support = (Finset.range (k / 2 + 1)).image (fun j => k - 2 * j) := by
  ext i
  rw [mem_support_H, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, Finset.mem_range.2 (by omega), rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by rw [Finset.mem_range] at hj; omega, rfl⟩

lemma isTerm_iff_g (k : ℕ) : isTerm k ↔
    ((Finset.range (k / 2 + 1)).filter
      (fun j => g k j = (Finset.range (k / 2 + 1)).sup (g k))).card = 2 := by
  have hM : maxAbsCoeff k = (Finset.range (k / 2 + 1)).sup (g k) := by
    unfold maxAbsCoeff
    rw [support_eq, Finset.sup_image]
    apply Finset.sup_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    exact natAbs_coeff k j (by omega)
  unfold isTerm
  rw [hM, support_eq, Finset.filter_image, Finset.card_image_of_injOn]
  · apply Iff.of_eq
    congr 2
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [natAbs_coeff k j (by omega)]
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    omega

lemma isTerm_iff (k : ℕ) : isTerm k ↔ ∃ j, 2 * j + 2 ≤ k ∧ Q k j = 4 * (j + 1) := by
  rw [isTerm_iff_g]
  set T := Finset.range (k / 2 + 1)
  have memT : ∀ j, j ∈ T ↔ 2 * j ≤ k := fun j => by rw [Finset.mem_range]; omega
  constructor
  · intro hc
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 hc
    have hx : x ∈ T.filter (fun j => g k j = T.sup (g k)) := by rw [hs]; simp
    have hy : y ∈ T.filter (fun j => g k j = T.sup (g k)) := by rw [hs]; simp
    rw [Finset.mem_filter, memT] at hx hy
    -- wlog x < y
    have key : ∀ u v, u < v → 2 * u ≤ k → 2 * v ≤ k → g k u = T.sup (g k) →
        g k v = T.sup (g k) → ∃ j, 2 * j + 2 ≤ k ∧ Q k j = 4 * (j + 1) := by
      intro u v huv hu hv gu gv
      refine ⟨u, by omega, ?_⟩
      rcases lt_trichotomy (Q k u) (4 * (u + 1)) with hl | he | hg
      · have := g_dec k u hl v (by omega) hv
        omega
      · exact he
      · have h1 := g_lt_succ k u (by omega) hg
        have h2 : g k (u + 1) ≤ T.sup (g k) := Finset.le_sup ((memT _).2 (by omega))
        omega
    rcases lt_or_gt_of_ne hxy with h | h
    · exact key x y h hx.1 hy.1 hx.2 hy.2
    · exact key y x h hy.1 hx.1 hy.2 hx.2
  · rintro ⟨j0, hj0, hq⟩
    have hbefore : ∀ m, m < j0 → 4 * (m + 1) < Q k m := by
      intro m hm
      by_contra hc
      have := Q_strict k m j0 (by omega) hm
      omega
    have hafter : Q k (j0 + 1) < 4 * (j0 + 1 + 1) := Q_strict k j0 (j0 + 1) hq.le (by omega)
    have heq := g_succ_eq k j0 hj0 hq
    have hle : ∀ l, 2 * l ≤ k → g k l ≤ g k j0 := by
      intro l hl
      rcases lt_or_ge l (j0 + 2) with h | h
      · rcases lt_or_ge l (j0 + 1) with h' | h'
        · exact g_inc k j0 (by omega) hbefore (j0 - l) l (by omega)
        · rw [show l = j0 + 1 by omega, heq]
      · have := g_dec k (j0 + 1) hafter l (by omega) hl
        omega
    have hsup : T.sup (g k) = g k j0 := by
      apply le_antisymm
      · exact Finset.sup_le fun l hl => hle l ((memT l).1 hl)
      · exact Finset.le_sup ((memT j0).2 (by omega))
    rw [Finset.card_eq_two]
    refine ⟨j0, j0 + 1, by omega, ?_⟩
    ext l
    rw [Finset.mem_filter, memT, hsup]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, hg⟩
      by_contra hne
      rcases lt_or_ge l j0 with h | h
      · have h1 := g_inc k j0 (by omega) hbefore (j0 - (l + 1)) (l + 1) (by omega)
        have h2 := g_lt_succ k l (by omega) (hbefore l h)
        omega
      · have := g_dec k (j0 + 1) hafter l (by omega) hl
        omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, rfl⟩
      · exact ⟨by omega, heq⟩


/-- the terms in increasing order, 0-indexed -/
def f (n : ℕ) : ℕ :=
  if n % 2 = 0 then 8 * (n / 2) ^ 2 + 18 * (n / 2) + 8 else 8 * (n / 2) ^ 2 + 22 * (n / 2) + 13

lemma f_even (u : ℕ) : f (2 * u) = 8 * u ^ 2 + 18 * u + 8 := by
  unfold f; rw [if_pos (by omega), show 2 * u / 2 = u by omega]

lemma f_odd (u : ℕ) : f (2 * u + 1) = 8 * u ^ 2 + 22 * u + 13 := by
  unfold f; rw [if_neg (by omega), show (2 * u + 1) / 2 = u by omega]

lemma f_strictMono : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro n
  rcases Nat.even_or_odd' n with ⟨u, rfl | rfl⟩
  · rw [f_even, f_odd]; omega
  · rw [f_odd, show 2 * u + 1 + 1 = 2 * (u + 1) by ring, f_even]; ring_nf; omega

lemma char_f (k : ℕ) : (∃ j, 2 * j + 2 ≤ k ∧ Q k j = 4 * (j + 1)) ↔ ∃ n, f n = k := by
  constructor
  · rintro ⟨j, hj, hq⟩
    unfold Q at hq
    obtain ⟨p, hp⟩ : ∃ p, k - 2 * j = p + 1 := ⟨k - 2 * j - 1, by omega⟩
    rw [hp, show p + 1 - 1 = p by omega] at hq
    have hk : k = p + 1 + 2 * j := by omega
    have hp1 : 1 ≤ p := by omega
    obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 4 ∧ p = 4 * t + r := ⟨p / 4, p % 4, by omega, by omega⟩
    interval_cases r
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      refine ⟨2 * u + 1, ?_⟩
      rw [f_odd, hk]
      ring_nf at hq ⊢
      omega
    · ring_nf at hq; omega
    · ring_nf at hq; omega
    · refine ⟨2 * t, ?_⟩
      rw [f_even, hk]
      ring_nf at hq ⊢
      omega
  · rintro ⟨n, rfl⟩
    rcases Nat.even_or_odd' n with ⟨u, rfl | rfl⟩
    · refine ⟨4 * u ^ 2 + 7 * u + 2, ?_, ?_⟩
      · rw [f_even]; ring_nf; omega
      · unfold Q
        rw [f_even, show 8 * u ^ 2 + 18 * u + 8 - 2 * (4 * u ^ 2 + 7 * u + 2) = 4 * u + 4 by
          ring_nf; omega, show 4 * u + 4 - 1 = 4 * u + 3 by omega]
        ring
    · refine ⟨4 * u ^ 2 + 9 * u + 4, ?_, ?_⟩
      · rw [f_odd]; ring_nf; omega
      · unfold Q
        rw [f_odd, show 8 * u ^ 2 + 22 * u + 13 - 2 * (4 * u ^ 2 + 9 * u + 4) = 4 * u + 5 by
          ring_nf; omega, show 4 * u + 5 - 1 = 4 * u + 4 by omega]
        ring

lemma isTerm_iff_f (k : ℕ) : isTerm k ↔ ∃ n, f n = k := by
  rw [isTerm_iff, char_f]

lemma nth_eq_f (n : ℕ) : Nat.nth isTerm n = f n := by
  have hinf : (Set.ofPred isTerm).Infinite := by
    apply Set.infinite_of_injective_forall_mem f_strictMono.injective
    intro m
    exact (isTerm_iff_f (f m)).2 ⟨m, rfl⟩
  have huniv : { n : ℕ | ∀ hf : Set.Finite (Set.ofPred isTerm), n < hf.toFinset.card } =
      Set.univ := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro hf
    exact absurd hf hinf
  have := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := isTerm) f
    (by
      rw [huniv]
      intro k hk
      obtain ⟨m, hm⟩ := (isTerm_iff_f k).1 hk
      exact ⟨m, Set.mem_univ _, hm⟩)
    (by
      rw [huniv]
      intro m _
      exact (isTerm_iff_f (f m)).2 ⟨m, rfl⟩)
    (by rw [huniv]; exact f_strictMono.strictMonoOn _)
  rw [huniv] at this
  exact (this (Set.mem_univ n)).symm

lemma a_closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 2 * n * (n + 2) + (n + 1) * (-1) ^ (n + 1) := by
  unfold a
  rw [nth_eq_f]
  rcases Nat.even_or_odd' n with ⟨u, rfl | rfl⟩
  · obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have hs : ((-1 : ℤ)) ^ (2 * (v + 1) + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [show 2 * (v + 1) - 1 = 2 * v + 1 by omega, f_odd, hs]
    push_cast
    ring
  · rw [show 2 * u + 1 - 1 = 2 * u by omega, f_even,
      show 2 * u + 1 + 1 = 2 * (u + 1) by ring, pow_mul]
    push_cast
    ring

end A381737P

open A381737P OMA.S_oeis_a381737 in
theorem OMA.solution : type_of% @OMA.S_oeis_a381737.main := by
  have hrec : ∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega]
    rw [a_closed _ (by omega), a_closed _ (by omega), a_closed _ (by omega),
      a_closed _ (by omega), a_closed _ (by omega), a_closed _ (by omega)]
    push_cast
    ring
  refine ⟨a_closed, hrec, ?_⟩
  have hval : ∀ n, 1 ≤ n → (a n : ℚ) = 2 * n * (n + 2) + (n + 1) * (-1) ^ (n + 1) := by
    intro n hn
    have h := a_closed n hn
    have h2 : ((a n : ℤ) : ℚ) = ((2 * n * (n + 2) + (n + 1) * (-1) ^ (n + 1) : ℤ) : ℚ) := by
      rw [h]
    push_cast at h2
    exact h2
  set A : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hA
  have hden : ((1 : PowerSeries ℚ) - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 =
      1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by ring
  have hrhs : (8 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 5 * PowerSeries.X ^ 3 -
      PowerSeries.X ^ 4 - PowerSeries.X ^ 5 : PowerSeries ℚ) =
      PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    simp only [map_ofNat, pow_one]
  rw [mul_assoc, hden, hrhs]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [hA, hval] <;> norm_num
  · have h := hrec n hn
    have d0 : n ≠ 0 := by omega
    have d1 : n ≠ 1 := by omega
    have d2 : n ≠ 2 := by omega
    have d3 : n ≠ 3 := by omega
    have d4 : n ≠ 4 := by omega
    have d5 : n ≠ 5 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    simp only [hA, d0, d1, d2, d3, d4, d5, e1, e2, e3, e4, e5, c1, c2, c3, c4, c5,
      if_true, if_false, ite_true, ite_false]
    have h' : (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
      exact_mod_cast h
    rw [h']
    ring
