import OMAReductions.R_oeis_a085265_R1
import Mathlib

/-! Every `14 ≤ n < 10 ^ 6` is `s + k ^ 2` with `s ≥ 1` squarefree and `k ≥ 1`, by a kernel-checked
search over `k`. Below `10 ^ 6 + 1` a number `s > 0` is squarefree when `gcd(s, P ^ 2) = gcd(s, P)` for
`P` the product of the primes up to `1000`. -/

namespace OMA.Step_oeis_a085265_R1_H1

/-- The product of the primes up to `1000`. -/
def P : ℕ := 19590340644999083431262508198206381046123972390589368223882605328968666316379870661851951648789482321596229559115436019149189529725215266728292282990852649023362731392404017939142010958261393634959471483757196721672243410067118516227661133135192488848989914892157188308679896875137439519338903968094905549750386407106033836586660683539201011635917900039904495065203299749542985993134669814805318474080581207891125910

/-- Its square. -/
def P2 : ℕ := P * P

theorem hit : ∀ m : ℕ, m ≤ 1000 → 2 ≤ m → Nat.gcd m P ≠ 1 := by decide +kernel

theorem no_sq : ∀ m : ℕ, m ≤ 1000 → 2 ≤ m → P % (m * m) ≠ 0 := by decide +kernel

/-- For `0 < m ≤ 10 ^ 6`, `m` is squarefree when `gcd m P² = gcd m P`. -/
theorem sqfree_of {m : ℕ} (hm0 : 0 < m) (hm : m < 1000001) (h : Nat.gcd m P2 = Nat.gcd m P) :
    Squarefree m := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpm : p * p ≤ m := Nat.le_of_dvd hm0 hpp
  have h2 := hp.two_le
  have hp1000 : p ≤ 1000 := by nlinarith
  have hpP : p ∣ P := by
    by_contra hnd
    exact hit p hp1000 h2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have h1 : p * p ∣ P2 := mul_dvd_mul hpP hpP
  have h3 : p * p ∣ Nat.gcd m P2 := Nat.dvd_gcd hpp h1
  rw [h] at h3
  exact no_sq p hp1000 h2 (Nat.mod_eq_zero_of_dvd (h3.trans (Nat.gcd_dvd_right m P)))

/-- A squarefree test valid below `10 ^ 6 + 1`. -/
def sqB (s : ℕ) : Bool := decide (0 < s) && decide (s < 1000001) && Nat.gcd s P2 == Nat.gcd s P

theorem sqB_spec {s : ℕ} (h : sqB s = true) : 0 < s ∧ Squarefree s := by
  simp only [sqB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, sqfree_of h.1.1 h.1.2 h.2⟩

/-- Search `k = d, d + 1, ...` (at most `fuel` values) with `k ^ 2 < n` and `n - k ^ 2` squarefree. -/
def findK (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => (decide (d * d < n) && sqB (n - d * d)) || findK n f (d + 1)

theorem findK_spec (n : ℕ) : ∀ f d : ℕ, 1 ≤ d → findK n f d = true →
    ∃ s k : ℕ, 1 ≤ s ∧ Squarefree s ∧ 1 ≤ k ∧ s + k ^ 2 = n := by
  intro f
  induction f with
  | zero => intro d _ h; simp [findK] at h
  | succ f ih =>
    intro d hd h
    simp only [findK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · obtain ⟨hs0, hsq⟩ := sqB_spec h2
      exact ⟨n - d * d, d, hs0, hsq, hd, by rw [sq]; omega⟩
    · exact ih (d + 1) (by omega) h

/-- `test x` holds for every `x` in `[s, s + c)`. -/
def checkFrom (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, s => test s && checkFrom test c (s + 1)

theorem checkFrom_spec (test : ℕ → Bool) : ∀ c s : ℕ, checkFrom test c s = true →
    ∀ n : ℕ, s ≤ n → n < s + c → test n = true := by
  intro c
  induction c with
  | zero => intro s _ n h1 h2; omega
  | succ c ih =>
    intro s h n h1 h2
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (s + 1) h.2 n hlt (by omega)

/-- The search for one `n`. -/
def termB (n : ℕ) : Bool := findK n 1000 1

set_option maxHeartbeats 0 in
theorem chunk0 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (0 + a) + b < 14) || termB (1000 * (0 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk1 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (100 + a) + b < 14) || termB (1000 * (100 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk2 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (200 + a) + b < 14) || termB (1000 * (200 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk3 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (300 + a) + b < 14) || termB (1000 * (300 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk4 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (400 + a) + b < 14) || termB (1000 * (400 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk5 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (500 + a) + b < 14) || termB (1000 * (500 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk6 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (600 + a) + b < 14) || termB (1000 * (600 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk7 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (700 + a) + b < 14) || termB (1000 * (700 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk8 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (800 + a) + b < 14) || termB (1000 * (800 + a) + b)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chunk9 : ((List.range 100).all fun a => (List.range 1000).all fun b =>
    decide (1000 * (900 + a) + b < 14) || termB (1000 * (900 + a) + b)) = true := by
  decide +kernel

theorem all_terms (n : ℕ) (h14 : 14 ≤ n) (h6 : n < 10 ^ 6) :
    ∃ s k : ℕ, 1 ≤ s ∧ Squarefree s ∧ 1 ≤ k ∧ s + k ^ 2 = n := by
  apply findK_spec n 1000 1 le_rfl
  change termB n = true
  have hb : n % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
  have ha : n / 1000 % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have hn : 1000 * (100 * (n / 1000 / 100) + n / 1000 % 100) + n % 1000 = n := by omega
  have hi : n / 1000 / 100 < 10 := by omega
  interval_cases hq : n / 1000 / 100
  · have hc := chunk0
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (0 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk1
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (100 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk2
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (200 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk3
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (300 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk4
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (400 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk5
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (500 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk6
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (600 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk7
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (700 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk8
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (800 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)
  · have hc := chunk9
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hc
    have := hc (n / 1000 % 100) ha (n % 1000) hb
    rw [show 1000 * (900 + n / 1000 % 100) + n % 1000 = n by omega] at this
    exact this.resolve_left (by omega)

end OMA.Step_oeis_a085265_R1_H1

open OMA.S_oeis_a085265 in
theorem OMA.solution : OMA.R_oeis_a085265_R1.H1 :=
  fun n h14 h6 => OMA.Step_oeis_a085265_R1_H1.all_terms n h14 h6
