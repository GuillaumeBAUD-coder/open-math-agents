import OMAStatements.S_oeis_a259533
import Mathlib

-- Problem: OEIS A259533 (a conjecture of Peter Bala). The sequence
-- a(n) = Sum_{j=0..n} Stirling2(n,j) * j! * g(j) satisfies a(n + phi(k)) = a(n) mod k for n >= k.
-- Proof, valid for every weight sequence g. (1) Stirling2(n,j) * j! = Sum_{i=0..j} (-1)^(j+i) *
-- C(j,i) * i^n (number of surjections), by induction on n from the recurrence. (2) For n >= k one
-- has i^(n + phi(k)) = i^n mod k for every i: check it modulo each prime power p^e dividing k;
-- if p divides i both sides vanish since e <= k <= n, otherwise use Euler's theorem and
-- phi(p^e) | phi(k). (3) k divides j! for j >= k, so modulo k only the terms j < k of a(n)
-- matter, and each of them is periodic by (1) and (2).

open Finset

lemma OMA.surj (s : ℕ → ℕ → ℕ) (h00 : s 0 0 = 1) (hn0 : ∀ n, s (n + 1) 0 = 0)
    (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j) :
    ∀ n j : ℕ, (s n j : ℤ) * (j.factorial : ℤ)
      = ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · simp [h00]
    · rw [h0j]
      have h := Int.alternating_sum_range_choose (n := j + 1)
      have h2 : ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ (j + 1 + i) * ((j + 1).choose i : ℤ) * (i : ℤ) ^ 0
          = (-1 : ℤ) ^ (j + 1) * ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ i * ((j + 1).choose i : ℤ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [pow_add]
        ring
      rw [h2, h]
      simp
  | succ n ih =>
    intro j
    rcases j with _ | j
    · rw [hn0]
      simp
    · have e1 : (s (n + 1) (j + 1) : ℤ) * ((j + 1).factorial : ℤ)
          = ((j : ℤ) + 1) * ((s n (j + 1) : ℤ) * ((j + 1).factorial : ℤ))
            + ((j : ℤ) + 1) * ((s n j : ℤ) * (j.factorial : ℤ)) := by
        rw [hrec, Nat.factorial_succ]
        push_cast
        ring
      have e2 : ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n
          = ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
        rw [Finset.sum_range_succ _ (j + 1), Nat.choose_succ_self]
        simp
      rw [e1, ih (j + 1), ih j, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases i with _ | i
      · simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero, mul_one]
        ring
      · have hc : ((j + 1).choose (i + 1) : ℤ) = (j.choose i : ℤ) + (j.choose (i + 1) : ℤ) := by
          rw [Nat.choose_succ_succ]
          push_cast
          ring
        have hm : ((j : ℤ) + 1) * (j.choose i : ℤ)
            = ((j + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) := by
          have h3 := Nat.add_one_mul_choose_eq j i
          exact_mod_cast h3
        rw [hc] at hm
        have hs : (-1 : ℤ) ^ (j + 1 + (i + 1)) = -(-1 : ℤ) ^ (j + (i + 1)) := by
          have h4 : j + 1 + (i + 1) = (j + (i + 1)) + 1 := by ring
          rw [h4, pow_succ]
          ring
        push_cast
        rw [hs, hc, pow_succ]
        linear_combination (-(-1 : ℤ) ^ (j + (i + 1)) * ((i : ℤ) + 1) ^ n) * hm

lemma OMA.pow_per (k i n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    i ^ (n + Nat.totient k) ≡ i ^ n [MOD k] := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h1 : n ≠ 0 := by omega
    have h2 : n + Nat.totient k ≠ 0 := by omega
    rw [zero_pow h1, zero_pow h2]
  have hle : i ^ n ≤ i ^ (n + Nat.totient k) := Nat.pow_le_pow_right hi (Nat.le_add_right _ _)
  refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  refine (Nat.modEq_iff_dvd' hle).mp ?_
  by_cases hpi : p ∣ i
  · have he : e ≤ n := by
      have h1 : p ^ e ≤ k := Nat.le_of_dvd (by omega) hpe
      have h2 : e < p ^ e := Nat.lt_pow_self hp.one_lt
      omega
    have hd1 : p ^ e ∣ i ^ n := (pow_dvd_pow p he).trans (pow_dvd_pow_of_dvd hpi n)
    have hd2 : p ^ e ∣ i ^ (n + Nat.totient k) :=
      hd1.trans (pow_dvd_pow i (Nat.le_add_right _ _))
    exact (Nat.modEq_zero_iff_dvd.mpr hd1).trans (Nat.modEq_zero_iff_dvd.mpr hd2).symm
  · have hcop : Nat.Coprime i (p ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpi).symm
    have h1 : i ^ Nat.totient (p ^ e) ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcop
    obtain ⟨t, ht⟩ := Nat.totient_dvd_of_dvd hpe
    have h2 : i ^ Nat.totient k ≡ 1 [MOD p ^ e] := by
      rw [ht, pow_mul]
      have h5 := h1.pow t
      rwa [one_pow] at h5
    have h3 := h2.mul_left (i ^ n)
    rw [← pow_add, mul_one] at h3
    exact h3.symm

lemma OMA.trunc (s : ℕ → ℕ → ℕ) (g : ℕ → ℤ) (k m : ℕ) (hk : 1 ≤ k) (hm : k ≤ m + 1) :
    ∑ j ∈ range (m + 1), ((s m j : ℤ) * (j.factorial : ℤ)) * g j
      ≡ ∑ j ∈ range k, ((s m j : ℤ) * (j.factorial : ℤ)) * g j [ZMOD k] := by
  rw [Int.modEq_iff_dvd]
  have h := Finset.sum_Ico_eq_sub (fun j => ((s m j : ℤ) * (j.factorial : ℤ)) * g j) hm
  have hd : (k : ℤ) ∣ ∑ j ∈ Ico k (m + 1), ((s m j : ℤ) * (j.factorial : ℤ)) * g j := by
    refine Finset.dvd_sum (fun j hj => ?_)
    have hkj : k ≤ j := (Finset.mem_Ico.mp hj).1
    have h6 : (k : ℤ) ∣ (j.factorial : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial (by omega) hkj)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _
  rw [h] at hd
  have h7 := (dvd_neg (a := (k : ℤ))).mpr hd
  rwa [neg_sub] at h7

lemma OMA.T_per (s : ℕ → ℕ → ℕ) (h00 : s 0 0 = 1) (hn0 : ∀ n, s (n + 1) 0 = 0)
    (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j)
    (k n j : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    (s (n + Nat.totient k) j : ℤ) * (j.factorial : ℤ)
      ≡ (s n j : ℤ) * (j.factorial : ℤ) [ZMOD k] := by
  rw [OMA.surj s h00 hn0 h0j hrec, OMA.surj s h00 hn0 h0j hrec]
  refine Int.ModEq.sum (fun i _ => ?_)
  have h := OMA.pow_per k i n hk hn
  have h' : ((i ^ (n + Nat.totient k) : ℕ) : ℤ) ≡ ((i ^ n : ℕ) : ℤ) [ZMOD (k : ℤ)] :=
    Int.natCast_modEq_iff.mpr h
  push_cast at h'
  exact Int.ModEq.mul_left _ h'

theorem OMA.gen (s : ℕ → ℕ → ℕ) (h00 : s 0 0 = 1) (hn0 : ∀ n, s (n + 1) 0 = 0)
    (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j)
    (g : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : k ≤ n) :
    ∑ j ∈ range (n + Nat.totient k + 1),
        ((s (n + Nat.totient k) j : ℤ) * (j.factorial : ℤ)) * g j
      ≡ ∑ j ∈ range (n + 1), ((s n j : ℤ) * (j.factorial : ℤ)) * g j [ZMOD k] := by
  have h1 := OMA.trunc s g k (n + Nat.totient k) hk (by omega)
  have h2 := OMA.trunc s g k n hk (by omega)
  have h3 : ∑ j ∈ range k, ((s (n + Nat.totient k) j : ℤ) * (j.factorial : ℤ)) * g j
      ≡ ∑ j ∈ range k, ((s n j : ℤ) * (j.factorial : ℤ)) * g j [ZMOD k] := by
    refine Int.ModEq.sum (fun j _ => ?_)
    exact (OMA.T_per s h00 hn0 h0j hrec k n j hk hn).mul_right _
  exact (h1.trans h3).trans h2.symm

open OMA.S_oeis_a259533

theorem OMA.solution : type_of% @OMA.S_oeis_a259533.main := by
  have h00 : stirling2 0 0 = 1 := by
    rw [stirling2]
  have hn0 : ∀ n, stirling2 (n + 1) 0 = 0 := fun n => by
    rw [stirling2]
  have h0j : ∀ j, stirling2 0 (j + 1) = 0 := fun j => by
    rw [stirling2]
  have hrec : ∀ n j, stirling2 (n + 1) (j + 1)
      = (j + 1) * stirling2 n (j + 1) + stirling2 n j := fun n j => by
    rw [stirling2]
  have e : ∀ m, ((a m : ℕ) : ℤ)
      = ∑ j ∈ range (m + 1), ((stirling2 m j : ℤ) * (j.factorial : ℤ)) * ((coeffG j : ℕ) : ℤ) := by
    intro m
    unfold a
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  apply Int.natCast_modEq_iff.mp
  rw [e, e]
  exact OMA.gen stirling2 h00 hn0 h0j hrec (fun j => ((coeffG j : ℕ) : ℤ)) k hk n hn
