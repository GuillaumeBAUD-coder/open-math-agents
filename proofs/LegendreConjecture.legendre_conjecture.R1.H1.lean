import OMAReductions.R_LegendreConjecture_legendre_conjecture_R1

-- Legendre's conjecture for 1 <= n <= 1000: a prime strictly between n^2 and (n + 1)^2.
-- isP is a trial-division primality test proved sound against Nat.Prime (tdiv_spec); find searches an interval
-- for a prime; the kernel evaluates the search in blocks of 100 values (decide +kernel).
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
namespace OMA.PS

/-- Search for a prime `q` with `p ≤ q < hi`, with fuel. -/
def find : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, p, hi => (decide (p < hi) && isP p) || find f (p + 1) hi

theorem find_spec : ∀ (f p hi : ℕ), find f p hi = true → ∃ q, p ≤ q ∧ q < hi ∧ q.Prime := by
  intro f
  induction f with
  | zero =>
    intro p hi h
    simp [find] at h
  | succ f ih =>
    intro p hi h
    rw [find, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, le_refl p, h.1, isP_spec p h.2⟩
    · obtain ⟨q, h1, h2, h3⟩ := ih (p + 1) hi h
      exact ⟨q, by omega, h2, h3⟩

end OMA.PS

namespace OMA.Leg

open OMA.PS

/-- All of `n, n + 1, ..., n + c - 1` have a prime strictly between the two bounds. -/
def all : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, n => find (2 * n) (n ^ 2 + 1) ((n + 1) ^ 2) && all c (n + 1)

theorem all_spec : ∀ (c n : ℕ), all c n = true → ∀ i, i < c →
    ∃ q, (n + i) ^ 2 < q ∧ q < (n + i + 1) ^ 2 ∧ q.Prime := by
  intro c
  induction c with
  | zero =>
    intro n _ i hi
    omega
  | succ c ih =>
    intro n h i hi
    rw [all, Bool.and_eq_true] at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · obtain ⟨q, h1, h2, h3⟩ := find_spec _ _ _ h.1
      exact ⟨q, by simpa using h1, by simpa using h2, h3⟩
    · obtain ⟨q, h1, h2, h3⟩ := ih (n + 1) h.2 (i - 1) (by omega)
      have e : n + 1 + (i - 1) = n + i := by omega
      rw [e] at h1 h2
      exact ⟨q, h1, h2, h3⟩

set_option maxRecDepth 100000 in
theorem t0 : all 100 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t1 : all 100 101 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t2 : all 100 201 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t3 : all 100 301 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t4 : all 100 401 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t5 : all 100 501 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t6 : all 100 601 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t7 : all 100 701 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t8 : all 100 801 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t9 : all 100 901 = true := by decide +kernel

theorem range (n : ℕ) (h1 : 1 ≤ n) (hN : n ≤ 1000) : ∃ q, n ^ 2 < q ∧ q < (n + 1) ^ 2 ∧ q.Prime := by
  have hi : ∃ i, n = 1 + i := ⟨n - 1, by omega⟩
  obtain ⟨i, rfl⟩ := hi
  by_cases g0 : i < 100
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t0 (i - 0) (by omega)
    have e : 1 + (i - 0) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g1 : i < 200
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t1 (i - 100) (by omega)
    have e : 101 + (i - 100) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g2 : i < 300
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t2 (i - 200) (by omega)
    have e : 201 + (i - 200) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g3 : i < 400
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t3 (i - 300) (by omega)
    have e : 301 + (i - 300) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g4 : i < 500
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t4 (i - 400) (by omega)
    have e : 401 + (i - 400) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g5 : i < 600
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t5 (i - 500) (by omega)
    have e : 501 + (i - 500) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g6 : i < 700
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t6 (i - 600) (by omega)
    have e : 601 + (i - 600) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g7 : i < 800
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t7 (i - 700) (by omega)
    have e : 701 + (i - 700) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  by_cases g8 : i < 900
  · obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t8 (i - 800) (by omega)
    have e : 801 + (i - 800) = 1 + i := by omega
    rw [e] at h1 h2
    exact ⟨q, h1, h2, h3⟩
  obtain ⟨q, h1, h2, h3⟩ := all_spec _ _ t9 (i - 900) (by omega)
  have e : 901 + (i - 900) = 1 + i := by omega
  rw [e] at h1 h2
  exact ⟨q, h1, h2, h3⟩

end OMA.Leg

theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_R1.H1 := by
  intro n hn hN
  obtain ⟨q, h1, h2, h3⟩ := OMA.Leg.range n hn hN
  exact ⟨q, Set.mem_Ioo.mpr ⟨h1, h2⟩, h3⟩
