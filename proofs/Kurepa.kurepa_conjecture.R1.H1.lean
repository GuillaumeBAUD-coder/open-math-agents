import OMAReductions.R_Kurepa_kurepa_conjecture_R1

/-! For every n ≤ N, n divides both N! and the difference between the left factorials at N and n. A single gcd at N = 65536 certifies the full interval. -/

namespace OMA.KurepaCertificate
open Kurepa

/-- The product of the next consecutive integers and the sum of all its proper prefix products. -/
def block : ℕ → ℕ → ℕ × ℕ
  | 0, i => (i + 1, 1)
  | d + 1, i =>
    let (p, s) := block d i
    let (q, t) := block d (i + 2^d)
    (p * q, s + p * t)

lemma block_spec (d i : ℕ) :
    (i + 2^d).factorial = i.factorial * (block d i).1 ∧
    left_factorial (i + 2^d) = left_factorial i + i.factorial * (block d i).2 := by
  induction d generalizing i with
  | zero => simp [block, Nat.factorial_succ, Nat.mul_comm, left_factorial, Finset.sum_range_succ]
  | succ d ih =>
    obtain ⟨f, s⟩ := ih i
    obtain ⟨f', s'⟩ := ih (i + 2^d)
    rw [show i + 2^(d+1) = i + 2^d + 2^d by rw [pow_succ]; omega, f', s', f, s]
    constructor <;> simp only [block] <;> ring

lemma lift_dvd {n m : ℕ} (h : n ≤ m) (hn : 0 < n)
    (hd : n ∣ left_factorial n) : n ∣ left_factorial m := by
  induction m, h using Nat.le_induction with
  | base => exact hd
  | succ k hk ih =>
    simpa only [left_factorial, Finset.sum_range_succ] using
      Nat.dvd_add ih (Nat.dvd_factorial hn hk)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 3000000 in
theorem certificate : (block 16 0).1.gcd (block 16 0).2 = 2 := by decide +kernel

end OMA.KurepaCertificate

open Kurepa OMA.KurepaCertificate in
theorem OMA.solution : OMA.R_Kurepa_kurepa_conjecture_R1.H1 := by
  intro n hn hb h
  have hN : n ≤ 0 + 2^16 := by omega
  have fac := Nat.dvd_factorial (by omega : 0 < n) hN
  have sum := lift_dvd hN (by omega) (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨hf, hs⟩ := block_spec 16 0
  simp only [Nat.factorial_zero, one_mul] at hf
  simp only [show left_factorial 0 = 0 by rfl, Nat.factorial_zero, one_mul, zero_add] at hs
  rw [hf] at fac
  rw [Nat.zero_add, hs] at sum
  have hd := Nat.dvd_gcd fac sum
  rw [certificate] at hd
  exact (Nat.not_dvd_of_pos_of_lt (by decide) hn) hd
