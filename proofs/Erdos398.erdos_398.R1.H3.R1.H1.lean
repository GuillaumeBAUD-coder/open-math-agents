import OMAReductions.R_Erdos398_erdos_398_R1_H3_R1
import Mathlib

/-!
Brocard's equation `n! + 1 = m^2` has no solution for `128 ≤ n < 10000`.

For each such `n` one of thirteen primes `p` makes `n! + 1` a quadratic non-residue modulo `p`,
detected by Euler's criterion `(n! + 1)^((p-1)/2) ≡ -1 (mod p)`. The factorials modulo `p` are
computed incrementally, and the whole table is checked by kernel evaluation.
-/
namespace Brocard398

/-- Euler test: `(r + 1)^((p-1)/2) ≡ -1 (mod p)`. -/
def ok (r p : ℕ) : Bool := (r + 1) ^ ((p - 1) / 2) % p == p - 1

/-- `[k! % p, (k+1)! % p, …]`, `m` entries, computed incrementally from `f = k! % p`. -/
def facAux (p : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | k, f, m + 1 => f :: facAux p (k + 1) (f * (k + 1) % p) m

theorem facAux_eq (p : ℕ) (m : ℕ) : ∀ k, facAux p k (k.factorial % p) m =
    (List.range' k m).map (fun n => n.factorial % p) := by
  induction m with
  | zero => intro k; rfl
  | succ m ih =>
    intro k
    have h : k.factorial % p * (k + 1) % p = (k + 1).factorial % p := by
      rw [Nat.factorial_succ, Nat.mul_mod, Nat.mod_mod, mul_comm, ← Nat.mul_mod]
    simp only [facAux, List.range'_succ, List.map_cons, h, ih]

/-- Coverage of `n ∈ [128, 10000)` by the prime `p`. -/
def cov (p : ℕ) : List Bool :=
  List.zipWith (fun _ r => ok r p) (List.range' 128 9872) (facAux p 128 (Nat.factorial 128 % p) 9872)

theorem cov_eq (p : ℕ) : cov p = (List.range' 128 9872).map (fun n => ok (n.factorial % p) p) := by
  unfold cov
  rw [facAux_eq, List.zipWith_map_right, List.zipWith_self]

def primes : List ℕ :=
  [10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111]

def covAll : List ℕ → List Bool
  | [] => List.replicate 9872 false
  | p :: ps => List.zipWith (· || ·) (cov p) (covAll ps)

theorem covAll_eq : ∀ ps : List ℕ, covAll ps =
    (List.range' 128 9872).map (fun n => ps.any (fun p => ok (n.factorial % p) p))
  | [] => by
    rw [covAll]
    simp only [List.any_nil]
    rw [List.map_const', List.length_range']
  | p :: ps => by
    rw [covAll, covAll_eq ps, cov_eq, List.zipWith_map, List.zipWith_self]
    simp [List.any_cons]

theorem table : (covAll primes).all id = true := by
  decide +kernel

theorem covered (n : ℕ) (h1 : 128 ≤ n) (h2 : n < 10000) :
    ∃ p ∈ primes, ok (n.factorial % p) p = true := by
  have ht := table
  rw [covAll_eq, List.all_map] at ht
  have hn : n ∈ List.range' 128 9872 := by
    rw [List.mem_range']; refine ⟨n - 128, by omega, by omega⟩
  have := List.all_eq_true.mp ht n hn
  simpa [List.any_eq_true] using this

/-- Euler's criterion, the easy direction: a square is not a non-residue. -/
theorem not_sq_of_ok {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : ok (a % p) p = true) :
    ∀ y : ℕ, a + 1 ≠ y ^ 2 := by
  intro y hy
  have := Fact.mk hp
  simp only [ok, beq_iff_eq] at h
  have hodd : (p - 1) / 2 * 2 = p - 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases hp.eq_two_or_odd with h' | h'
    · exact absurd h' hp2
    · omega
  have hz : (((a % p + 1) ^ ((p - 1) / 2) % p : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by rw [h]
  have hcast : (((a % p + 1) ^ ((p - 1) / 2) % p : ℕ) : ZMod p) = ((y : ZMod p)) ^ (p - 1) := by
    rw [ZMod.natCast_mod]
    push_cast
    rw [ZMod.natCast_mod]
    have : ((a : ZMod p) + 1) = (y : ZMod p) ^ 2 := by
      have := congrArg (Nat.cast : ℕ → ZMod p) hy; push_cast at this; exact this
    rw [this, ← pow_mul, mul_comm, hodd]
  have hm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le]; simp
  rw [hcast, hm1] at hz
  by_cases hy0 : (y : ZMod p) = 0
  · rw [hy0, zero_pow (by have := hp.two_le; omega)] at hz
    exact one_ne_zero (neg_eq_zero.mp hz.symm)
  · rw [ZMod.pow_card_sub_one_eq_one hy0] at hz
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast; linear_combination hz
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    exact hp2 this

theorem primes_prime : ∀ p ∈ primes, p.Prime ∧ p ≠ 2 := by
  intro p hp
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num⟩

theorem h1 : OMA.R_Erdos398_erdos_398_R1_H3_R1.H1 := by
  intro n hn1 hn2 x hx
  obtain ⟨p, hp, hok⟩ := covered n hn1 hn2
  obtain ⟨hpp, hp2⟩ := primes_prime p hp
  have h4 : 4 ∣ n.factorial :=
    (by decide : 4 ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial (by omega))
  have hsq : n.factorial + 1 = (2 * x + 1) ^ 2 := by
    have := Nat.div_mul_cancel h4
    rw [hx] at this
    nlinarith [this]
  exact not_sq_of_ok hpp hp2 hok (2 * x + 1) hsq

end Brocard398

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1_H3_R1.H1 := Brocard398.h1
