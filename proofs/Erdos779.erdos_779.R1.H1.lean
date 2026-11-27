import OMAReductions.R_Erdos779_erdos_779_R1
import Mathlib.NumberTheory.Bertrand

-- Step Erdos779.erdos_779.R1.H1: hypothesis H1 of reduction Erdos779.erdos_779.R1
-- Credit: @plamen0606-source

/-!
Proof of hypothesis H1 of reduction `Erdos779.erdos_779.R1`:
for `n >= 3`, any prime `q` with `P + 1 < q` and `q - P < (nth Nat.Prime (n + 1)) ^ 2`
yields a prime offset `p = q - P` satisfying `nth Nat.Prime n < p < P` and `(P + p).Prime`.
-/

namespace OMA.Erdos779R1H1

open Finset Nat

private lemma nth_prime_strictMono : StrictMono (nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private lemma nth_prime_prime (k : ℕ) : (nth Nat.Prime k).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k

private lemma nth_prime_succ_le_of_lt {n r : ℕ} (hr : r.Prime) (hlt : nth Nat.Prime n < r) :
    nth Nat.Prime (n + 1) ≤ r := by
  have heq : nth Nat.Prime (Nat.count Nat.Prime r) = r := Nat.nth_count hr
  have hlt_idx : n < Nat.count Nat.Prime r := by
    by_contra hle
    have hge : nth Nat.Prime (Nat.count Nat.Prime r) ≤ nth Nat.Prime n :=
      nth_prime_strictMono.monotone (Nat.le_of_not_lt hle)
    omega
  rw [← heq]
  exact nth_prime_strictMono.monotone (Nat.succ_le_of_lt hlt_idx)

private lemma nth_prime_zero : nth Nat.Prime 0 = 2 := by
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide)

private lemma nth_prime_one : nth Nat.Prime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide)

private lemma nth_prime_two : nth Nat.Prime 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide)

private lemma nth_prime_three : nth Nat.Prime 3 = 7 := by
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide)

private lemma nth_prime_four : nth Nat.Prime 4 = 11 := by
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  rw [← hc]
  exact Nat.nth_count (by decide)

private lemma nth_prime_succ_le_two_mul (k : ℕ) :
    nth Nat.Prime (k + 1) ≤ 2 * nth Nat.Prime k := by
  have hne : nth Nat.Prime k ≠ 0 := (nth_prime_prime k).ne_zero
  obtain ⟨r, hr, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (nth Nat.Prime k) hne
  exact (nth_prime_succ_le_of_lt hr hlt).trans hle

private lemma sq_nth_prime_succ_le_primorial :
    ∀ n : ℕ, 3 ≤ n → (nth Nat.Prime (n + 1)) ^ 2 ≤ ∏ i ∈ range (n + 1), nth Nat.Prime i := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction m with
  | zero =>
    simp only [Nat.zero_add, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      nth_prime_zero, nth_prime_one, nth_prime_two, nth_prime_three]
    rw [show (3 + 1 : ℕ) = 4 by rfl, nth_prime_four]
    norm_num
  | succ m ih =>
    have ih' := ih (by omega)
    have hbert : nth Nat.Prime (m + 1 + 3 + 1) ≤ 2 * nth Nat.Prime (m + 3 + 1) := by
      have hidx : m + 1 + 3 + 1 = (m + 3 + 1) + 1 := by omega
      rw [hidx]
      exact nth_prime_succ_le_two_mul (m + 3 + 1)
    have h4 : 4 ≤ nth Nat.Prime (m + 3 + 1) := by
      have hge : nth Nat.Prime 4 ≤ nth Nat.Prime (m + 3 + 1) :=
        nth_prime_strictMono.monotone (by omega)
      rw [nth_prime_four] at hge
      omega
    have hprod : ∏ i ∈ range (m + 1 + 3 + 1), nth Nat.Prime i =
        (∏ i ∈ range (m + 3 + 1), nth Nat.Prime i) * nth Nat.Prime (m + 3 + 1) := by
      have hidx : m + 1 + 3 + 1 = (m + 3 + 1) + 1 := by omega
      rw [hidx, Finset.prod_range_succ]
    rw [hprod]
    calc
      (nth Nat.Prime (m + 1 + 3 + 1)) ^ 2
          ≤ (2 * nth Nat.Prime (m + 3 + 1)) ^ 2 := Nat.pow_le_pow_left hbert 2
      _ = 4 * (nth Nat.Prime (m + 3 + 1)) ^ 2 := by ring
      _ ≤ nth Nat.Prime (m + 3 + 1) * (nth Nat.Prime (m + 3 + 1)) ^ 2 :=
            Nat.mul_le_mul_right _ h4
      _ ≤ nth Nat.Prime (m + 3 + 1) * ∏ i ∈ range (m + 3 + 1), nth Nat.Prime i :=
            Nat.mul_le_mul_left _ ih'
      _ = (∏ i ∈ range (m + 3 + 1), nth Nat.Prime i) * nth Nat.Prime (m + 3 + 1) :=
            Nat.mul_comm _ _

private lemma minFac_sq_le_of_not_prime {p : ℕ} (hp2 : 2 ≤ p) (hnp : ¬ p.Prime) :
    p.minFac ^ 2 ≤ p := by
  have hrp : p.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ := Nat.minFac_dvd p
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hk
    exact hnp (hk ▸ hrp)
  have hkp : k.minFac.Prime := Nat.minFac_prime hk1
  have hkdvd : k.minFac ∣ p := by
    rw [hk]
    exact dvd_mul_of_dvd_right (Nat.minFac_dvd k) p.minFac
  have hle1 : p.minFac ≤ k.minFac := Nat.minFac_le_of_dvd hkp.two_le hkdvd
  have hle2 : k.minFac ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.minFac_dvd k)
  have hle : p.minFac ≤ k := hle1.trans hle2
  calc
    p.minFac ^ 2 = p.minFac * p.minFac := by ring
    _ ≤ p.minFac * k := Nat.mul_le_mul_left _ hle
    _ = p := hk.symm

end OMA.Erdos779R1H1

theorem OMA.solution : OMA.R_Erdos779_erdos_779_R1.H1 := by
  open Finset Nat OMA.Erdos779R1H1 in
  intro n hn
  dsimp only
  set P := ∏ i ∈ range (n + 1), nth Nat.Prime i
  intro q hq hlo hhi
  set p := q - P
  have hPq : P + p = q := Nat.add_sub_of_le (by omega)
  have hp2 : 2 ≤ p := by omega
  have hPpos : 0 < P := Finset.prod_pos fun i _ => (nth_prime_prime i).pos
  have hno_small : ∀ r : ℕ, r.Prime → r ≤ nth Nat.Prime n → ¬ r ∣ p := by
    intro r hr hle hdvd
    have heq : nth Nat.Prime (Nat.count Nat.Prime r) = r := Nat.nth_count hr
    have hidx : Nat.count Nat.Prime r ≤ n := by
      by_contra hgt
      have hlt : nth Nat.Prime n < nth Nat.Prime (Nat.count Nat.Prime r) :=
        nth_prime_strictMono (Nat.lt_of_not_ge hgt)
      omega
    have hrP : r ∣ P := by
      rw [← heq]
      exact Finset.dvd_prod_of_mem (fun i => nth Nat.Prime i) (Finset.mem_range.mpr (by omega))
    have hrq : r ∣ q := by
      rw [← hPq]
      exact dvd_add hrP hdvd
    have hreq : r = q := (hq.eq_one_or_self_of_dvd r hrq).resolve_left hr.ne_one
    have hrleP : r ≤ P := Nat.le_of_dvd hPpos hrP
    omega
  have hmin_prime : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin_gt : nth Nat.Prime n < p.minFac := by
    by_contra hle
    exact hno_small p.minFac hmin_prime (Nat.le_of_not_lt hle) (Nat.minFac_dvd p)
  have hmin_ge_next : nth Nat.Prime (n + 1) ≤ p.minFac :=
    nth_prime_succ_le_of_lt hmin_prime hmin_gt
  have hp_prime : p.Prime := by
    by_contra hnp
    have hsq : p.minFac ^ 2 ≤ p := minFac_sq_le_of_not_prime hp2 hnp
    have hnext_sq : (nth Nat.Prime (n + 1)) ^ 2 ≤ p.minFac ^ 2 :=
      Nat.pow_le_pow_left hmin_ge_next 2
    omega
  have hp_gt : nth Nat.Prime n < p := by
    have hle : p.minFac ≤ p := Nat.le_of_dvd (by omega) (Nat.minFac_dvd p)
    omega
  have hp_lt_P : p < P := by
    have hsq_le : (nth Nat.Prime (n + 1)) ^ 2 ≤ P := sq_nth_prime_succ_le_primorial n hn
    omega
  exact ⟨p, hp_prime, hPq.symm ▸ hq, hp_gt, hp_lt_P⟩
