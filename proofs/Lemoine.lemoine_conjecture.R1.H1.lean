import OMAReductions.R_Lemoine_lemoine_conjecture_R1

-- Lemoine's conjecture for odd n with 6 < n <= 10001: n = p + 2 q with p, q prime.
-- isP is a trial-division primality test proved sound against Nat.Prime (tdiv_spec); lem searches for a prime
-- q with n - 2 q prime; the kernel evaluates the search in blocks of 500 values (decide +kernel).
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

namespace OMA.Lem

open OMA.PS

/-- Search for a prime `q' ≥ q` (within fuel) with `n - 2 * q'` prime. -/
def lem : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, q, n => (decide (2 * q ≤ n) && isP q && isP (n - 2 * q)) || lem f (q + 1) n

theorem lem_spec : ∀ (f q n : ℕ), lem f q n = true → ∃ a b, a.Prime ∧ b.Prime ∧ a + 2 * b = n := by
  intro f
  induction f with
  | zero =>
    intro q n h
    simp [lem] at h
  | succ f ih =>
    intro q n h
    rw [lem, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨n - 2 * q, q, isP_spec (n - 2 * q) h.2, isP_spec q h.1.2, by omega⟩
    · exact ih (q + 1) n h

/-- All of `n, n + 2, ..., n + 2 (c - 1)` pass the search. -/
def lemAll : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, n => lem 400 2 n && lemAll c (n + 2)

theorem lemAll_spec : ∀ (c n : ℕ), lemAll c n = true → ∀ i, i < c →
    ∃ a b, a.Prime ∧ b.Prime ∧ a + 2 * b = n + 2 * i := by
  intro c
  induction c with
  | zero =>
    intro n _ i hi
    omega
  | succ c ih =>
    intro n h i hi
    rw [lemAll, Bool.and_eq_true] at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact lem_spec 400 2 n h.1
    · obtain ⟨a, b, ha, hb, hab⟩ := ih (n + 2) h.2 (i - 1) (by omega)
      exact ⟨a, b, ha, hb, by omega⟩

set_option maxRecDepth 100000 in
theorem t0 : lemAll 500 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t1 : lemAll 500 1007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t2 : lemAll 500 2007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t3 : lemAll 500 3007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t4 : lemAll 500 4007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t5 : lemAll 500 5007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t6 : lemAll 500 6007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t7 : lemAll 500 7007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t8 : lemAll 500 8007 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t9 : lemAll 498 9007 = true := by decide +kernel

theorem range (n : ℕ) (h6 : 6 < n) (ho : Odd n) (hN : n ≤ 10001) :
    ∃ a b, a.Prime ∧ b.Prime ∧ a + 2 * b = n := by
  obtain ⟨m, hm⟩ := ho
  have hi : ∃ i, n = 7 + 2 * i := ⟨m - 3, by omega⟩
  obtain ⟨i, rfl⟩ := hi
  by_cases g0 : i < 500
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t0 (i - 0) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g1 : i < 1000
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t1 (i - 500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g2 : i < 1500
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t2 (i - 1000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g3 : i < 2000
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t3 (i - 1500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g4 : i < 2500
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t4 (i - 2000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g5 : i < 3000
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t5 (i - 2500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g6 : i < 3500
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t6 (i - 3000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g7 : i < 4000
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t7 (i - 3500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g8 : i < 4500
  · obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t8 (i - 4000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  obtain ⟨a, b, ha, hb, hab⟩ := lemAll_spec _ _ t9 (i - 4500) (by omega)
  exact ⟨a, b, ha, hb, by omega⟩

end OMA.Lem

theorem OMA.solution : OMA.R_Lemoine_lemoine_conjecture_R1.H1 := by
  intro n hn ho hN
  exact OMA.Lem.range n hn ho hN
