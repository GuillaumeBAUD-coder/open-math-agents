import OMAReductions.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1
import Mathlib

-- Step Erdos409.erdos_409.variants.sigma_prime_termination.R1.H1: hypothesis H1 of reduction
-- Erdos409.erdos_409.variants.sigma_prime_termination.R1
-- Finite check: for every 1 < n ≤ 300 the orbit of m ↦ σ(m) - 1 reaches a prime within 10 steps
-- (at most 6 are needed). σ is computed by a divisor loop proved equal to Mathlib's sigma 1,
-- primality by trial division, all run by decide +kernel.

namespace OMA.E409H1

/-- `noDivFrom p d fuel = true` means no `e ≥ d` with `e * e ≤ p` divides `p`
(`false` when the fuel runs out). -/
def noDivFrom (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else (p % d != 0) && noDivFrom p (d + 1) fuel

lemma noDivFrom_spec (p : ℕ) : ∀ fuel d, noDivFrom p d fuel = true →
    ∀ e, d ≤ e → e * e ≤ p → ¬ e ∣ p := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDivFrom] at h
  | succ f ih =>
    intro d h e hde hep hdvd
    simp only [noDivFrom] at h
    split_ifs at h with hlt
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨hmod, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
      · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih (d + 1) hrest e hlt' hep hdvd

def isPrimeB (p : ℕ) : Bool := decide (2 ≤ p) && noDivFrom p 2 p

lemma isPrimeB_spec (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  by_contra hnp
  have hm := Nat.minFac_sq_le_self (by omega) hnp
  have hmp := Nat.minFac_prime (show p ≠ 1 by omega)
  rw [sq] at hm
  exact noDivFrom_spec p p 2 hnd (Nat.minFac p) hmp.two_le hm (Nat.minFac_dvd p)

/-- Sum of the divisors of `m` that are at most `k`. -/
def sumDivs (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumDivs m k + if m % (k + 1) = 0 then k + 1 else 0

lemma sumDivs_eq (m : ℕ) : ∀ k, sumDivs m k = ∑ d ∈ Finset.Ico 1 (k + 1), if d ∣ m then d else 0 := by
  intro k
  induction k with
  | zero => simp [sumDivs]
  | succ k ih =>
    rw [sumDivs, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
    congr 1
    by_cases h : (k + 1) ∣ m
    · simp [h, Nat.mod_eq_zero_of_dvd h]
    · have : m % (k + 1) ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
      simp [h, this]

lemma sumDivs_sigma (m : ℕ) : sumDivs m m = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply, sumDivs_eq, ← Finset.sum_filter]
  rfl

/-- `reach m fuel = true` means the orbit of `m` hits a number passing the trial division
within `fuel` values. -/
def reach : ℕ → ℕ → Bool
  | _, 0 => false
  | m, fuel + 1 => isPrimeB m || reach (sumDivs m m - 1) fuel

lemma reach_spec : ∀ fuel m, reach m fuel = true →
    ∃ i, ((fun x => ArithmeticFunction.sigma 1 x - 1)^[i] m).Prime := by
  intro fuel
  induction fuel with
  | zero => intro m h; simp [reach] at h
  | succ f ih =>
    intro m h
    simp only [reach, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨0, isPrimeB_spec _ h⟩
    · obtain ⟨i, hi⟩ := ih _ h
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [sumDivs_sigma] using hi

def cond (n : ℕ) : Bool := decide (n ≤ 1) || decide (300 < n) || reach n 10

/-- `chk k lo` checks `cond` on `[lo, lo + 2 ^ k)` (binary splitting). -/
def chk : ℕ → ℕ → Bool
  | 0, lo => cond lo
  | k + 1, lo => chk k lo && chk k (lo + 2 ^ k)

lemma chk_spec : ∀ k lo, chk k lo = true → ∀ n, lo ≤ n → n < lo + 2 ^ k → cond n = true := by
  intro k
  induction k with
  | zero =>
    intro lo h n h1 h2
    simp only [pow_zero] at h2
    obtain rfl : n = lo := by omega
    simpa [chk] using h
  | succ k ih =>
    intro lo h n h1 h2
    simp only [chk, Bool.and_eq_true] at h
    by_cases hn : n < lo + 2 ^ k
    · exact ih lo h.1 n h1 hn
    · exact ih (lo + 2 ^ k) h.2 n (by omega) (by rw [pow_succ] at h2; omega)

theorem chk_ok : chk 9 0 = true := by decide +kernel

theorem h1 : ∀ n : ℕ, 1 < n → n ≤ 300 →
    ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime := by
  intro n hn hle
  have hc := chk_spec 9 0 chk_ok n (Nat.zero_le n) (by norm_num; omega)
  have e1 : decide (n ≤ 1) = false := by simp; omega
  have e2 : decide (300 < n) = false := by simp; omega
  simp only [cond, e1, e2, Bool.false_or] at hc
  exact reach_spec 10 n hc

end OMA.E409H1

theorem OMA.solution : OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1.H1 :=
  OMA.E409H1.h1
