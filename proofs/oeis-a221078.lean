import OMAStatements.S_oeis_a221078
import Mathlib

/-!
# Proof of OEIS A221078 Conjecture

Using `stirling2Fact n j = j! * S(n, j)`:
1. For every `n, j`, `j! ∣ stirling2Fact n j` and `stirling2Fact n j = 0` for `n < j`.
2. Modulo any odd prime `p`, all terms with `j >= p` (hence all `m >= p`) vanish since `p ∣ j!`.
3. For any `t` with `(p - 1) ∣ t` and `4 ∣ t` (namely `t = p - 1` for `p ≡ 1 (mod 4)` and
   `t = 2 * (p - 1)` for `p ≡ 3 (mod 4)`), every remaining term `1 <= m <= j < p` is invariant
   under `n ↦ n + t` in `ZMod p` by Fermat's little theorem.
-/

namespace OeisA221078Proof

open Finset

private def Δ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) : ℤ :=
  ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r)

private lemma Δ_succ (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ g (j + 1) x = Δ g j (x + 1) - Δ g j x := by
  unfold Δ
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * g (x + r))]
  rw [Finset.sum_range_succ (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + r))]
  rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + r))]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
             Nat.choose_zero_right, Nat.cast_zero, add_zero, Nat.cast_add]
  have hlast : x + ((j : ℤ) + 1) = x + 1 + (j : ℤ) := by ring
  rw [hlast]
  have hmid : ∑ r ∈ Finset.range j,
      (-1 : ℤ) ^ (j + 1 - (r + 1)) * (Nat.choose (j + 1) (r + 1) : ℤ) * g (x + ((r : ℤ) + 1)) =
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * g (x + 1 + (r : ℤ))) -
      (∑ r ∈ Finset.range j, (-1 : ℤ) ^ (j - (r + 1)) * (Nat.choose j (r + 1) : ℤ) * g (x + ((r : ℤ) + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r < j := Finset.mem_range.mp hr
    have h1 : j + 1 - (r + 1) = j - r := by omega
    have h2 : j - r = (j - (r + 1)) + 1 := by omega
    have harg : x + ((r : ℤ) + 1) = x + 1 + (r : ℤ) := by ring
    rw [h1, Nat.choose_succ_succ, Nat.succ_eq_add_one, Nat.cast_add, harg, h2, pow_succ]
    ring
  rw [hmid, pow_succ]
  ring

private lemma Δ_shift (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g (y + 1)) j x = Δ g j x + Δ g (j + 1) x := by
  have h1 : Δ (fun y => g (y + 1)) j x = Δ g j (x + 1) := by
    unfold Δ
    apply Finset.sum_congr rfl
    intro r _
    congr 1; ring
  rw [h1, Δ_succ]
  ring

private lemma Δ_add (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y + g₂ y) j x = Δ g₁ j x + Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_sub (g₁ g₂ : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => g₁ y - g₂ y) j x = Δ g₁ j x - Δ g₂ j x := by
  unfold Δ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_const_mul (a : ℤ) (g : ℤ → ℤ) (j : ℕ) (x : ℤ) :
    Δ (fun y => a * g y) j x = a * Δ g j x := by
  unfold Δ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma Δ_pow_eq_zero_of_lt (d j : ℕ) (hdj : d < j) :
    ∀ x : ℤ, Δ (fun y => y ^ d) j x = 0 := by
  induction d using Nat.strong_induction_on generalizing j with
  | h d ih =>
    intro x
    cases j with
    | zero => omega
    | succ j =>
      rw [Δ_succ]
      cases d with
      | zero =>
        have hconst : ∀ m : ℕ, ∀ y : ℤ, Δ (fun _ => (1 : ℤ)) m y = if m = 0 then 1 else 0 := by
          intro m
          induction m with
          | zero => intro y; simp [Δ]
          | succ m ihm => intro y; rw [Δ_succ, ihm, ihm]; simp
        simp only [pow_zero]
        rw [hconst, hconst]; simp
      | succ d =>
        have hbin : (fun y : ℤ => (y + 1) ^ (d + 1) - y ^ (d + 1)) =
            fun y : ℤ => ∑ i ∈ Finset.range (d + 1), (Nat.choose (d + 1) i : ℤ) * y ^ i := by
          ext y
          rw [add_pow, Finset.sum_range_succ]
          simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
          apply Finset.sum_congr rfl
          intro i _; ring
        have hstep : Δ (fun y => y ^ (d + 1)) j (x + 1) - Δ (fun y => y ^ (d + 1)) j x =
            Δ (fun y => (y + 1) ^ (d + 1) - y ^ (d + 1)) j x := by
          rw [Δ_sub]
          congr 1
          unfold Δ
          apply Finset.sum_congr rfl
          intro r _; congr 2; ring
        rw [hstep, hbin]
        have hsum : ∀ s : Finset ℕ, (∀ i ∈ s, i < d + 1) → (∀ i ∈ s, i < j) →
            Δ (fun y => ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i) j x = 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty => intro _ _; simp [Δ]
          | @insert a s ha ihs =>
            intro hltd hlt
            have hfun : (fun y : ℤ => ∑ i ∈ insert a s, (Nat.choose (d + 1) i : ℤ) * y ^ i) =
                fun y : ℤ => (Nat.choose (d + 1) a : ℤ) * y ^ a +
                  ∑ i ∈ s, (Nat.choose (d + 1) i : ℤ) * y ^ i := by
              ext y; rw [Finset.sum_insert ha]
            rw [hfun, Δ_add, Δ_const_mul,
                ih a (hltd a (Finset.mem_insert_self a s)) j (hlt a (Finset.mem_insert_self a s)) x,
                mul_zero, zero_add]
            exact ihs (fun i hi => hltd i (Finset.mem_insert_of_mem hi))
              (fun i hi => hlt i (Finset.mem_insert_of_mem hi))
        exact hsum (Finset.range (d + 1))
          (fun i hi => Finset.mem_range.mp hi)
          (fun i hi => by have := Finset.mem_range.mp hi; omega)

private lemma Δ_pow_zero_eq_stirling (n j : ℕ) :
    Δ (fun y => y ^ n) j 0 = (j.factorial * Nat.stirlingSecond n j : ℕ) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [Δ]
    | succ j =>
      rw [Δ_pow_eq_zero_of_lt 0 (j + 1) (by omega) 0]
      simp [Nat.stirlingSecond_zero_succ]
  | succ n ih =>
    cases j with
    | zero =>
      simp [Δ, zero_pow (Nat.succ_ne_zero n)]
    | succ j =>
      have hrec : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
          ((j + 1 : ℕ) : ℤ) * (Δ (fun y => y ^ n) (j + 1) 0 + Δ (fun y => y ^ n) j 0) := by
        have hstep1 : Δ (fun y => y ^ (n + 1)) (j + 1) 0 =
            ((j + 1 : ℕ) : ℤ) * Δ (fun y => (y + 1) ^ n) j 0 := by
          unfold Δ
          simp only [zero_add]
          rw [Finset.sum_range_succ' (f := fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ (n + 1))]
          simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          have hsub : j + 1 - (r + 1) = j - r := by omega
          have hch : (r + 1) * Nat.choose (j + 1) (r + 1) = (j + 1) * Nat.choose j r := by
            have := Nat.add_one_mul_choose_eq j r
            linarith
          have hchz : ((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ) =
              ((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ) := by
            exact_mod_cast hch
          rw [hsub, pow_succ ((r + 1 : ℕ) : ℤ) n]
          push_cast
          calc (-1 : ℤ) ^ (j - r) * (Nat.choose (j + 1) (r + 1) : ℤ) * (((r : ℤ) + 1) ^ n * ((r : ℤ) + 1))
              = (-1 : ℤ) ^ (j - r) * (((r + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r + 1) : ℤ)) * ((r : ℤ) + 1) ^ n := by
                push_cast; ring
            _ = (-1 : ℤ) ^ (j - r) * (((j + 1 : ℕ) : ℤ) * (Nat.choose j r : ℤ)) * ((r : ℤ) + 1) ^ n := by
                rw [hchz]
            _ = ((j : ℤ) + 1) * ((-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * ((r : ℤ) + 1) ^ n) := by
                push_cast; ring
        rw [hstep1, Δ_shift (fun y => y ^ n) j 0]
        ring
      rw [hrec, ih (j + 1), ih j, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma stirling2Fact_eq_Δ (n j : ℕ) :
    OMA.S_oeis_a221078.stirling2Fact n j = Δ (fun y => y ^ n) j 0 := by
  unfold OMA.S_oeis_a221078.stirling2Fact Δ
  simp only [zero_add]

private lemma fact_dvd_stirling2Fact (n j : ℕ) :
    (j.factorial : ℤ) ∣ OMA.S_oeis_a221078.stirling2Fact n j := by
  rw [stirling2Fact_eq_Δ, Δ_pow_zero_eq_stirling]
  push_cast
  exact dvd_mul_right _ _

private lemma stirling2Fact_eq_zero_of_lt {n j : ℕ} (h : n < j) :
    OMA.S_oeis_a221078.stirling2Fact n j = 0 := by
  rw [stirling2Fact_eq_Δ]
  exact Δ_pow_eq_zero_of_lt n j h 0

private lemma zmod_pow_add_pred {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (x : ZMod p) :
    x ^ (n + (p - 1)) = x ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega), zero_pow (by omega)]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

private lemma periodic_step {p n t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (ht_dvd : (p - 1) ∣ t) (ht4 : 4 ∣ t) :
    OMA.S_oeis_a221078.a (n + t) ≡ OMA.S_oeis_a221078.a n [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  have hpow_t : ∀ x : ZMod p, ∀ k : ℕ, 1 ≤ k → x ^ (k + t) = x ^ k := by
    intro x k hk
    clear ht4
    rcases ht_dvd with ⟨c, rfl⟩
    induction c with
    | zero => simp
    | succ c ihc =>
      rw [show k + (p - 1) * (c + 1) = (k + (p - 1) * c) + (p - 1) by ring]
      rw [zmod_pow_add_pred hp (by omega), ihc]
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  have h2_pow_t : (2 : ZMod p) ^ t = 1 := by
    have h := hpow_t (2 : ZMod p) 1 le_rfl
    rw [pow_add, pow_one] at h
    exact mul_left_cancel₀ h2_ne (by simpa using h)
  have hst_mod : ∀ j : ℕ,
      (OMA.S_oeis_a221078.stirling2Fact (n + t) j : ZMod p) =
      (OMA.S_oeis_a221078.stirling2Fact n j : ZMod p) := by
    intro j
    unfold OMA.S_oeis_a221078.stirling2Fact
    push_cast
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    exact hpow_t (r : ZMod p) n hn
  have htan_zero_ge : ∀ m k : ℕ, p ≤ m → (OMA.S_oeis_a221078.tanPowCoeff m k : ZMod p) = 0 := by
    intro m k hpm
    unfold OMA.S_oeis_a221078.tanPowCoeff
    split_ifs
    · have := hp.two_le; omega
    · simp
    · simp
    · push_cast
      have hsum0 : ∑ j ∈ Finset.Icc m k,
          ((-1 : ZMod p) ^ (j - m) * ((Nat.choose (j - 1) (m - 1) : ZMod p) *
            (2 : ZMod p) ^ (k - j)) * (OMA.S_oeis_a221078.stirling2Fact k j : ZMod p)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hmj : m ≤ j := (Finset.mem_Icc.mp hj).1
        have hdvd : (p : ℤ) ∣ OMA.S_oeis_a221078.stirling2Fact k j :=
          dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_factorial hp.pos (by omega)))
            (fact_dvd_stirling2Fact k j)
        have h0 : (OMA.S_oeis_a221078.stirling2Fact k j : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
        rw [h0, mul_zero]
      have hcast : (∑ j ∈ Finset.Icc m k,
          ((-1 : ZMod p) ^ (j - m) * (Nat.choose (j - 1) (m - 1) : ZMod p) *
            (2 : ZMod p) ^ (k - j) * (OMA.S_oeis_a221078.stirling2Fact k j : ZMod p))) = 0 := by
        rw [← hsum0]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [hcast, mul_zero]
  have htrunc : ∀ k : ℕ, 1 ≤ k →
      (OMA.S_oeis_a221078.a k : ZMod p) =
      ∑ m ∈ Finset.range p, (m : ZMod p) ^ k * (OMA.S_oeis_a221078.tanPowCoeff m k : ZMod p) := by
    intro k hk
    unfold OMA.S_oeis_a221078.a
    push_cast
    by_cases hkp : k + 1 ≤ p
    · have hsplit : Finset.range p = Finset.range (k + 1) ∪ (Finset.range p \ Finset.range (k + 1)) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ m ∈ Finset.range p \ Finset.range (k + 1),
          (m : ZMod p) ^ k * (OMA.S_oeis_a221078.tanPowCoeff m k : ZMod p) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_sdiff, Finset.mem_range] at hm
        have h0 : OMA.S_oeis_a221078.tanPowCoeff m k = 0 := by
          unfold OMA.S_oeis_a221078.tanPowCoeff
          have hm0 : m ≠ 0 := by omega
          have hkm : k < m := by omega
          simp [hm0, hkm]
        rw [h0, Int.cast_zero, mul_zero]
      rw [htail, add_zero]
    · have hsplit : Finset.range (k + 1) = Finset.range p ∪ (Finset.range (k + 1) \ Finset.range p) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
      rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
      have htail : ∑ m ∈ Finset.range (k + 1) \ Finset.range p,
          (m : ZMod p) ^ k * (OMA.S_oeis_a221078.tanPowCoeff m k : ZMod p) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_sdiff, Finset.mem_range] at hm
        rw [htan_zero_ge m k (by omega), mul_zero]
      rw [htail, add_zero]
  rw [htrunc (n + t) (by omega), htrunc n hn]
  apply Finset.sum_congr rfl
  intro m hm
  have hmp : m < p := Finset.mem_range.mp hm
  rw [hpow_t (m : ZMod p) n hn]
  congr 1
  by_cases hm0 : m = 0
  · subst hm0
    unfold OMA.S_oeis_a221078.tanPowCoeff
    simp [show n ≠ 0 by omega]
  · by_cases hmn : n < m
    · -- LHS also vanishes mod p because stirling2Fact (n + t) j ≡ stirling2Fact n j = 0 for all j >= m > n
      have hR : OMA.S_oeis_a221078.tanPowCoeff m n = 0 := by
        unfold OMA.S_oeis_a221078.tanPowCoeff
        simp [hm0, hmn]
      rw [hR, Int.cast_zero]
      unfold OMA.S_oeis_a221078.tanPowCoeff
      simp only [hm0, ↓reduceIte]
      split_ifs
      · simp
      · push_cast
        have hsum0 : ∑ j ∈ Finset.Icc m (n + t),
            ((-1 : ZMod p) ^ (j - m) * (Nat.choose (j - 1) (m - 1) : ZMod p) *
              (2 : ZMod p) ^ (n + t - j) * (OMA.S_oeis_a221078.stirling2Fact (n + t) j : ZMod p)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hmj : m ≤ j := (Finset.mem_Icc.mp hj).1
          rw [hst_mod j, stirling2Fact_eq_zero_of_lt (by omega), Int.cast_zero, mul_zero]
        rw [hsum0, mul_zero]
    · have hnm : m ≤ n := by omega
      have hpar : (n + t - m) % 2 = (n - m) % 2 := by
        rcases ht4 with ⟨q, rfl⟩; omega
      unfold OMA.S_oeis_a221078.tanPowCoeff
      have hcond1 : ¬ (n + t < m ∨ (n + t - m) % 2 ≠ 0) ↔ ¬ (n < m ∨ (n - m) % 2 ≠ 0) := by
        omega
      by_cases hodd : (n - m) % 2 ≠ 0
      · have hodd' : (n + t - m) % 2 ≠ 0 := by omega
        simp [hm0, hodd, hodd']
      · have hodd' : ¬ (n + t - m) % 2 ≠ 0 := by omega
        have hnot1 : ¬ (n + t < m ∨ (n + t - m) % 2 ≠ 0) := by omega
        have hnot2 : ¬ (n < m ∨ (n - m) % 2 ≠ 0) := by omega
        simp only [hm0, ↓reduceIte, hnot1, hnot2]
        push_cast
        have hsign : (-1 : ZMod p) ^ ((n + t - m) / 2) = (-1 : ZMod p) ^ ((n - m) / 2) := by
          rcases ht4 with ⟨q, rfl⟩
          have hdiv : (n + 4 * q - m) / 2 = (n - m) / 2 + 2 * q := by omega
          rw [hdiv, pow_add, pow_mul]
          norm_num
        rw [hsign]
        congr 1
        have hsplit : Finset.Icc m (n + t) =
            Finset.Icc m n ∪ (Finset.Icc m (n + t) \ Finset.Icc m n) := by
          ext j; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
        have htail : ∑ j ∈ Finset.Icc m (n + t) \ Finset.Icc m n,
            ((-1 : ZMod p) ^ (j - m) * (Nat.choose (j - 1) (m - 1) : ZMod p) *
              (2 : ZMod p) ^ (n + t - j) * (OMA.S_oeis_a221078.stirling2Fact (n + t) j : ZMod p)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          simp only [Finset.mem_sdiff, Finset.mem_Icc] at hj
          have hnj : n < j := by omega
          rw [hst_mod j, stirling2Fact_eq_zero_of_lt hnj, Int.cast_zero, mul_zero]
        rw [htail, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
        rw [hst_mod j, show n + t - j = (n - j) + t by omega, pow_add, h2_pow_t, mul_one]

end OeisA221078Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a221078.main := by
  constructor
  · intro p n hp hmod hn
    exact OeisA221078Proof.periodic_step hp (by omega) hn (dvd_refl _) ⟨(p - 1) / 4, by omega⟩
  · intro p n hp hmod hn
    exact OeisA221078Proof.periodic_step hp (by omega) hn (dvd_mul_left _ 2) ⟨(p - 1) / 2, by omega⟩
