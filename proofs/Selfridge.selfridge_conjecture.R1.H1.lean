import OMAReductions.R_Selfridge_selfridge_conjecture_R1

-- The PSW (Selfridge) conjecture for p <= 10000.
-- For every odd p = 2 or 3 mod 5 up to 10000 the kernel checks that p is prime (verified trial division isP),
-- or 2^(p-1) is not 1 mod p, or F_(p+1) is not 0 mod p (fibm computes Fibonacci numbers modulo p and is
-- proved equal to Nat.fib modulo p). The base-two pseudoprimes 1387, 2047, 3277, 4033, 7957 in these classes
-- are the ones that need the Fibonacci test.
-- A verified numerical range only; not progress on the conjecture.

namespace OMA.PS

/-- Trial division with fuel: `q` has no divisor `m` with `d ≤ m` and `m * m ≤ q`. -/
def tdiv : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, d, q => if q < d * d then true else if q % d = 0 then false else tdiv f (d + 1) q

theorem tdiv_spec : ∀ (f d q : ℕ), tdiv f d q = true → 2 ≤ q →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ q) → q.Prime := by
  intro f
  induction f with
  | zero =>
    intro d q h
    simp [tdiv] at h
  | succ f ih =>
    intro d q h hq hm
    rw [tdiv] at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hq, fun m hm1 hm2 => hm m hm1 ?_⟩
      have h3 : m * m ≤ q := Nat.le_sqrt.mp hm2
      by_contra hc
      have hc' : d ≤ m := Nat.le_of_not_lt hc
      have h4 : d * d ≤ m * m := Nat.mul_le_mul hc' hc'
      omega
    · refine ih (d + 1) q h hq (fun m hm1 hm2 => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm2 with hlt | rfl
      · exact hm m hm1 hlt
      · intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

/-- A kernel-friendly primality test. -/
def isP (q : ℕ) : Bool := decide (2 ≤ q) && tdiv q 2 q

theorem isP_spec (q : ℕ) (h : isP q = true) : q.Prime := by
  rw [isP, Bool.and_eq_true, decide_eq_true_eq] at h
  exact tdiv_spec q 2 q h.2 h.1 (fun m h1 h2 => by omega)

end OMA.PS

namespace OMA.PSW

open OMA.PS

/-- `fibm f a b p` advances the pair `(a, b) = (F_i, F_(i+1))` modulo `p` by `f` steps and returns
the first component. -/
def fibm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, a, _, _ => a
  | f + 1, a, b, p => fibm f b ((a + b) % p) p

theorem fibm_spec : ∀ (f i a b p : ℕ), a = Nat.fib i % p → b = Nat.fib (i + 1) % p →
    fibm f a b p = Nat.fib (i + f) % p := by
  intro f
  induction f with
  | zero =>
    intro i a b p ha _
    rw [fibm, Nat.add_zero, ha]
  | succ f ih =>
    intro i a b p ha hb
    rw [fibm]
    have h2 : (a + b) % p = Nat.fib (i + 1 + 1) % p := by
      rw [ha, hb, Nat.fib_add_two, ← Nat.add_mod]
    have h3 := ih (i + 1) b ((a + b) % p) p hb h2
    have e : i + 1 + f = i + (f + 1) := by omega
    rwa [e] at h3

/-- The test: `p` is prime, or fails the base-two Fermat test, or fails the Fibonacci test. -/
def ok (p : ℕ) : Bool :=
  isP p || decide (2 ^ (p - 1) % p ≠ 1 % p) || decide (fibm (p + 1) (0 % p) (1 % p) p ≠ 0)

theorem ok_spec (p : ℕ) (h : ok p = true) (h2 : 2 ^ (p - 1) ≡ 1 [MOD p])
    (h3 : (p + 1).fib ≡ 0 [MOD p]) : p.Prime := by
  rw [ok, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact isP_spec p h
  · exact absurd h2 h
  · exfalso
    apply h
    have hf := fibm_spec (p + 1) 0 (0 % p) (1 % p) p (by simp) (by simp)
    rw [Nat.zero_add] at hf
    rw [hf]
    exact h3

/-- All candidates `p, p + 1, ..., p + c - 1` (odd, congruent to 2 or 3 modulo 5) pass the test. -/
def all : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, p =>
    (decide (p % 2 = 0) || decide (p % 5 ≠ 2 ∧ p % 5 ≠ 3) || ok p) && all c (p + 1)

theorem all_spec : ∀ (c p : ℕ), all c p = true → ∀ i, i < c →
    (p + i) % 2 = 1 → ((p + i) % 5 = 2 ∨ (p + i) % 5 = 3) → ok (p + i) = true := by
  intro c
  induction c with
  | zero =>
    intro p _ i hi
    omega
  | succ c ih =>
    intro p h i hi h1 h2
    rw [all, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [Nat.add_zero] at h1 h2 ⊢
      rcases h.1 with (h0 | h0) | h0
      · omega
      · omega
      · exact h0
    · have h4 := ih (p + 1) h.2 (i - 1) (by omega)
      have e : p + 1 + (i - 1) = p + i := by omega
      rw [e] at h4
      exact h4 h1 h2

set_option maxRecDepth 1000000 in
theorem t0 : all 500 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t1 : all 500 500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t2 : all 500 1000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t3 : all 500 1500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t4 : all 500 2000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t5 : all 500 2500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t6 : all 500 3000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t7 : all 500 3500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t8 : all 500 4000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t9 : all 500 4500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t10 : all 500 5000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t11 : all 500 5500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t12 : all 500 6000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t13 : all 500 6500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t14 : all 500 7000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t15 : all 500 7500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t16 : all 500 8000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t17 : all 500 8500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t18 : all 500 9000 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t19 : all 500 9500 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t20 : all 1 10000 = true := by decide +kernel

theorem range_ok (p : ℕ) (hN : p ≤ 10000) (h1 : p % 2 = 1) (h2 : p % 5 = 2 ∨ p % 5 = 3) :
    ok p = true := by
  by_cases g0 : p < 500
  · have h4 := all_spec _ _ t0 (p - 0) (by omega)
    have e : 0 + (p - 0) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g1 : p < 1000
  · have h4 := all_spec _ _ t1 (p - 500) (by omega)
    have e : 500 + (p - 500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g2 : p < 1500
  · have h4 := all_spec _ _ t2 (p - 1000) (by omega)
    have e : 1000 + (p - 1000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g3 : p < 2000
  · have h4 := all_spec _ _ t3 (p - 1500) (by omega)
    have e : 1500 + (p - 1500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g4 : p < 2500
  · have h4 := all_spec _ _ t4 (p - 2000) (by omega)
    have e : 2000 + (p - 2000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g5 : p < 3000
  · have h4 := all_spec _ _ t5 (p - 2500) (by omega)
    have e : 2500 + (p - 2500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g6 : p < 3500
  · have h4 := all_spec _ _ t6 (p - 3000) (by omega)
    have e : 3000 + (p - 3000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g7 : p < 4000
  · have h4 := all_spec _ _ t7 (p - 3500) (by omega)
    have e : 3500 + (p - 3500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g8 : p < 4500
  · have h4 := all_spec _ _ t8 (p - 4000) (by omega)
    have e : 4000 + (p - 4000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g9 : p < 5000
  · have h4 := all_spec _ _ t9 (p - 4500) (by omega)
    have e : 4500 + (p - 4500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g10 : p < 5500
  · have h4 := all_spec _ _ t10 (p - 5000) (by omega)
    have e : 5000 + (p - 5000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g11 : p < 6000
  · have h4 := all_spec _ _ t11 (p - 5500) (by omega)
    have e : 5500 + (p - 5500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g12 : p < 6500
  · have h4 := all_spec _ _ t12 (p - 6000) (by omega)
    have e : 6000 + (p - 6000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g13 : p < 7000
  · have h4 := all_spec _ _ t13 (p - 6500) (by omega)
    have e : 6500 + (p - 6500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g14 : p < 7500
  · have h4 := all_spec _ _ t14 (p - 7000) (by omega)
    have e : 7000 + (p - 7000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g15 : p < 8000
  · have h4 := all_spec _ _ t15 (p - 7500) (by omega)
    have e : 7500 + (p - 7500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g16 : p < 8500
  · have h4 := all_spec _ _ t16 (p - 8000) (by omega)
    have e : 8000 + (p - 8000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g17 : p < 9000
  · have h4 := all_spec _ _ t17 (p - 8500) (by omega)
    have e : 8500 + (p - 8500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g18 : p < 9500
  · have h4 := all_spec _ _ t18 (p - 9000) (by omega)
    have e : 9000 + (p - 9000) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  by_cases g19 : p < 10000
  · have h4 := all_spec _ _ t19 (p - 9500) (by omega)
    have e : 9500 + (p - 9500) = p := by omega
    rw [e] at h4
    exact h4 h1 h2
  have h4 := all_spec _ _ t20 (p - 10000) (by omega)
  have e : 10000 + (p - 10000) = p := by omega
  rw [e] at h4
  exact h4 h1 h2

end OMA.PSW

theorem OMA.solution : OMA.R_Selfridge_selfridge_conjecture_R1.H1 := by
  intro p hN hp
  have h1 : p % 2 = 1 := Nat.odd_iff.mp hp.is_odd
  have h2 : p % 5 = 2 ∨ p % 5 = 3 := by
    rcases hp.mod_5 with h | h
    · left
      exact h
    · right
      exact h
  exact OMA.PSW.ok_spec p (OMA.PSW.range_ok p hN h1 h2) hp.pow_2 hp.fib
