import OMAStatements.S_oeis_a335159
import Mathlib

open OMA.S_oeis_a335159

/-- Nim products `c ⊗ r` for `c ≤ 4` and `r < 16`. -/
def a335159_T (c r : ℕ) : ℕ :=
  ([[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5],
    [0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10],
    [0, 4, 8, 12, 6, 2, 14, 10, 11, 15, 3, 7, 13, 9, 5, 1]].getD c []).getD r 0

theorem a335159_T0 : ∀ c < 5, a335159_T c 0 = 0 := by decide +kernel

theorem a335159_Tlt : ∀ c < 5, ∀ r < 16, a335159_T c r < 16 := by decide +kernel

theorem a335159_F1 : ∀ c < 5, ∀ d < c, ∀ t < 16, ∃ s < 16,
    a335159_T c s ^^^ a335159_T d s = t := by decide +kernel

theorem a335159_F2 : ∀ c < 5, ∀ r < 16, ∀ m < a335159_T c r, ∃ d < c, ∃ s < r,
    m = a335159_T d r ^^^ a335159_T c s ^^^ a335159_T d s := by decide +kernel

theorem a335159_F3 : ∀ c < 5, ∀ d < c, ∀ r < 16, ∀ s < r,
    a335159_T c r ≠ a335159_T d r ^^^ a335159_T c s ^^^ a335159_T d s := by decide +kernel

/-- The table applied to each base 16 digit of `b`. -/
def a335159_M (c b : ℕ) : ℕ :=
  if h : b = 0 then 0 else a335159_T c (b % 16) + 16 * a335159_M c (b / 16)
termination_by b
decreasing_by omega

theorem a335159_M0 (c : ℕ) : a335159_M c 0 = 0 := by
  rw [a335159_M, dif_pos rfl]

theorem a335159_Mpos (c b : ℕ) (h : b ≠ 0) :
    a335159_M c b = a335159_T c (b % 16) + 16 * a335159_M c (b / 16) := by
  conv_lhs => rw [a335159_M]
  rw [dif_neg h]

theorem a335159_Msplit (c q r : ℕ) (hc : c < 5) (hr : r < 16) :
    a335159_M c (16 * q + r) = 16 * a335159_M c q + a335159_T c r := by
  by_cases h : 16 * q + r = 0
  · have hq : q = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hq
    subst hr0
    simp [a335159_M0, a335159_T0 c hc]
  · have e1 : (16 * q + r) % 16 = r := by omega
    have e2 : (16 * q + r) / 16 = q := by omega
    rw [a335159_Mpos c _ h, e1, e2]
    ring

theorem a335159_xlt (x y : ℕ) (hx : x < 16) (hy : y < 16) : x ^^^ y < 16 := by
  have p : (2 : ℕ) ^ 4 = 16 := by norm_num
  have h := Nat.xor_lt_two_pow (x := x) (y := y) (n := 4) (by rw [p]; exact hx) (by rw [p]; exact hy)
  rw [p] at h
  exact h

theorem a335159_xsplit (q r q' r' : ℕ) (hr : r < 16) (hr' : r' < 16) :
    (16 * q + r) ^^^ (16 * q' + r') = 16 * (q ^^^ q') + (r ^^^ r') := by
  have p : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hd := Nat.xor_div_two_pow (a := 16 * q + r) (b := 16 * q' + r') (n := 4)
  have hm := Nat.xor_mod_two_pow (a := 16 * q + r) (b := 16 * q' + r') (n := 4)
  rw [p] at hd hm
  have e1 : (16 * q + r) / 16 = q := by omega
  have e2 : (16 * q' + r') / 16 = q' := by omega
  have e3 : (16 * q + r) % 16 = r := by omega
  have e4 : (16 * q' + r') % 16 = r' := by omega
  rw [e1, e2] at hd
  rw [e3, e4] at hm
  omega

/-- The value `M c b` is excluded from the set whose least excluded number defines the product. -/
theorem a335159_notin (c : ℕ) (hc : c < 5) : ∀ b d s, d < c → s < b →
    a335159_M c b ≠ a335159_M d b ^^^ a335159_M c s ^^^ a335159_M d s := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro d s hd hs heq
    have hd5 : d < 5 := by omega
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 16 ∧ b = 16 * q + r :=
      ⟨b / 16, b % 16, by omega, by omega⟩
    obtain ⟨q', r', hr', rfl⟩ : ∃ q' r', r' < 16 ∧ s = 16 * q' + r' :=
      ⟨s / 16, s % 16, by omega, by omega⟩
    have t1 := a335159_Tlt c hc r hr
    have t2 := a335159_Tlt d hd5 r hr
    have t3 := a335159_Tlt c hc r' hr'
    have t4 := a335159_Tlt d hd5 r' hr'
    have x3 := a335159_xlt _ _ (a335159_xlt _ _ t2 t3) t4
    rw [a335159_Msplit c q r hc hr, a335159_Msplit d q r hd5 hr, a335159_Msplit c q' r' hc hr',
      a335159_Msplit d q' r' hd5 hr', a335159_xsplit _ _ _ _ t2 t3,
      a335159_xsplit _ _ _ _ (a335159_xlt _ _ t2 t3) t4] at heq
    have hq1 : a335159_M c q = a335159_M d q ^^^ a335159_M c q' ^^^ a335159_M d q' := by omega
    have hr1 : a335159_T c r = a335159_T d r ^^^ a335159_T c r' ^^^ a335159_T d r' := by omega
    rcases Nat.lt_or_ge q' q with hlt | hge
    · exact ih q (by omega) d q' hd hlt hq1
    · exact a335159_F3 c hc d hd r hr r' (by omega) hr1

/-- Every number below `M c b` belongs to that set. -/
theorem a335159_below (c : ℕ) (hc : c < 5) : ∀ b m, m < a335159_M c b →
    ∃ d < c, ∃ s < b, m = a335159_M d b ^^^ a335159_M c s ^^^ a335159_M d s := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro m hm
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 16 ∧ b = 16 * q + r :=
      ⟨b / 16, b % 16, by omega, by omega⟩
    obtain ⟨m1, m0, hm0, rfl⟩ : ∃ m1 m0, m0 < 16 ∧ m = 16 * m1 + m0 :=
      ⟨m / 16, m % 16, by omega, by omega⟩
    rw [a335159_Msplit c q r hc hr] at hm
    have t1 := a335159_Tlt c hc r hr
    rcases (show m1 < a335159_M c q ∨ (m1 = a335159_M c q ∧ m0 < a335159_T c r) by omega)
      with h1 | ⟨h1, h2⟩
    · have hqpos : q ≠ 0 := by
        intro h0
        rw [h0, a335159_M0] at h1
        omega
      obtain ⟨d, hd, q', hq', e⟩ := ih q (by omega) m1 h1
      have hd5 : d < 5 := by omega
      have t2 := a335159_Tlt d hd5 r hr
      obtain ⟨s, hs, es⟩ := a335159_F1 c hc d hd (m0 ^^^ a335159_T d r) (a335159_xlt _ _ hm0 t2)
      have t3 := a335159_Tlt c hc s hs
      have t4 := a335159_Tlt d hd5 s hs
      have key : a335159_T d r ^^^ a335159_T c s ^^^ a335159_T d s = m0 := by
        rw [Nat.xor_assoc, es, Nat.xor_comm m0, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      refine ⟨d, hd, 16 * q' + s, by omega, ?_⟩
      rw [a335159_Msplit d q r hd5 hr, a335159_Msplit c q' s hc hs, a335159_Msplit d q' s hd5 hs,
        a335159_xsplit _ _ _ _ t2 t3, a335159_xsplit _ _ _ _ (a335159_xlt _ _ t2 t3) t4, ← e, key]
    · obtain ⟨d, hd, s, hs, es⟩ := a335159_F2 c hc r hr m0 h2
      have hd5 : d < 5 := by omega
      have hs16 : s < 16 := by omega
      have t2 := a335159_Tlt d hd5 r hr
      have t3 := a335159_Tlt c hc s hs16
      have t4 := a335159_Tlt d hd5 s hs16
      have key : a335159_M d q ^^^ a335159_M c q ^^^ a335159_M d q = a335159_M c q := by
        rw [Nat.xor_comm (a335159_M d q), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      refine ⟨d, hd, 16 * q + s, by omega, ?_⟩
      rw [a335159_Msplit d q r hd5 hr, a335159_Msplit c q s hc hs16, a335159_Msplit d q s hd5 hs16,
        a335159_xsplit _ _ _ _ t2 t3, a335159_xsplit _ _ _ _ (a335159_xlt _ _ t2 t3) t4, key, ← es, h1]

/-- Conway's product agrees with the digit table for a left factor at most 4. -/
theorem a335159_nim : ∀ n c b, c + b = n → c < 5 → nimMul c b = a335159_M c b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c b hn hc
    have h1 : ∀ d < c, ∀ s < b, nimMul d b ^^^ nimMul c s ^^^ nimMul d s
        = a335159_M d b ^^^ a335159_M c s ^^^ a335159_M d s := by
      intro d hd s hs
      rw [ih (d + b) (by omega) d b rfl (by omega), ih (c + s) (by omega) c s rfl hc,
        ih (d + s) (by omega) d s rfl (by omega)]
    rw [nimMul]
    apply le_antisymm
    · apply Nat.sInf_le
      show ∀ d < c, ∀ s < b, a335159_M c b ≠ nimMul d b ^^^ nimMul c s ^^^ nimMul d s
      intro d hd s hs
      rw [h1 d hd s hs]
      exact a335159_notin c hc b d s hd hs
    · refine le_csInf ⟨a335159_M c b, ?_⟩ ?_
      · show ∀ d < c, ∀ s < b, a335159_M c b ≠ nimMul d b ^^^ nimMul c s ^^^ nimMul d s
        intro d hd s hs
        rw [h1 d hd s hs]
        exact a335159_notin c hc b d s hd hs
      · intro m hm
        by_contra hlt
        obtain ⟨d, hd, s, hs, e⟩ := a335159_below c hc b m (by omega)
        have hm' : ∀ d < c, ∀ s < b, m ≠ nimMul d b ^^^ nimMul c s ^^^ nimMul d s := hm
        apply hm' d hd s hs
        rw [h1 d hd s hs]
        exact e

theorem a335159_aeq (n : ℕ) : a n = a335159_M 4 (2 ^ n) := by
  have e : (2 : ℕ) ^ 2 = 4 := by norm_num
  unfold a
  rw [e]
  exact a335159_nim (4 + 2 ^ n) 4 (2 ^ n) rfl (by norm_num)

theorem a335159_Msmall (c r : ℕ) (hc : c < 5) (hr : r < 16) :
    a335159_M c r = a335159_T c r := by
  have h := a335159_Msplit c 0 r hc hr
  rw [a335159_M0] at h
  simpa using h

theorem a335159_val (n : ℕ) (hn : n < 4) : a n = a335159_T 4 (2 ^ n) := by
  have h16 : 2 ^ n < 16 := by interval_cases n <;> norm_num
  rw [a335159_aeq]
  exact a335159_Msmall 4 (2 ^ n) (by norm_num) h16

theorem a335159_rec (n : ℕ) : a (n + 4) = 16 * a n := by
  have e1 : (2 : ℕ) ^ (n + 4) = 16 * 2 ^ n + 0 := by ring
  have e2 := a335159_Msplit 4 (2 ^ n) 0 (by norm_num) (by norm_num)
  have e3 := a335159_T0 4 (by norm_num)
  have e4 := a335159_aeq (n + 4)
  have e5 := a335159_aeq n
  rw [e1, e2, e3] at e4
  omega

/-- The generating function identity, from four initial values and the recurrence. -/
theorem a335159_ps (g : ℕ → ℕ) (h0 : g 0 = 4) (h1 : g 1 = 8) (h2 : g 2 = 6) (h3 : g 3 = 11)
    (hr : ∀ n, g (n + 4) = 16 * g n) :
    (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 + 4 * PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n => (g n : ℤ)) =
      (4 + 8 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 11 * PowerSeries.X ^ 3 : PowerSeries ℤ) := by
  have c16 : (PowerSeries.C (16 : ℤ) : PowerSeries ℤ) = 16 := by simp
  have c4 : (PowerSeries.C (4 : ℤ) : PowerSeries ℤ) = 4 := by simp
  have c8 : (PowerSeries.C (8 : ℤ) : PowerSeries ℤ) = 8 := by simp
  have c6 : (PowerSeries.C (6 : ℤ) : PowerSeries ℤ) = 6 := by simp
  have c11 : (PowerSeries.C (11 : ℤ) : PowerSeries ℤ) = 11 := by simp
  have e : (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 + 4 * PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n => (g n : ℤ)) =
      PowerSeries.mk (fun n => (g n : ℤ)) -
        PowerSeries.C (16 : ℤ) * (PowerSeries.X ^ 4 * PowerSeries.mk (fun n => (g n : ℤ))) := by
    rw [c16]
    ring
  have e2 : (4 + 8 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 11 * PowerSeries.X ^ 3 :
        PowerSeries ℤ) =
      PowerSeries.C (4 : ℤ) + PowerSeries.C (8 : ℤ) * PowerSeries.X +
        PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (11 : ℤ) * PowerSeries.X ^ 3 := by
    rw [c4, c8, c6, c11]
  rw [e, e2]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | rfl | h
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · have h4 := hr (n - 4)
    rw [Nat.sub_add_cancel h] at h4
    simp [h, h4, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a335159.main := by
  have v0 : a 0 = 4 := (a335159_val 0 (by norm_num)).trans (by decide)
  have v1 : a 1 = 8 := (a335159_val 1 (by norm_num)).trans (by decide)
  have v2 : a 2 = 6 := (a335159_val 2 (by norm_num)).trans (by decide)
  have v3 : a 3 = 11 := (a335159_val 3 (by norm_num)).trans (by decide)
  refine ⟨?_, ?_⟩
  · intro n hn
    have h4 : 4 ≤ n := by omega
    have h := a335159_rec (n - 4)
    rw [Nat.sub_add_cancel h4] at h
    exact h
  · exact a335159_ps a v0 v1 v2 v3 a335159_rec
