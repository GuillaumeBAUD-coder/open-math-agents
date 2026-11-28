import OMAStatements.S_oeis_a144750

-- Problem: OEIS A144750, pseudo-factorials modulo 9
-- Credit: @ceejcake
-- Proof:
-- 1. Define the period-9 sequence c(n) = (2 * ((n + 1) / 3)) % 3.
-- 2. Using the mod-3 binomial-sum vector v(n, r) = ∑_{k ≡ r (mod 9)} C(n, k) (mod 3),
--    Pascal's identity gives v(n+1) = step(v(n)), and step^3(w)(r) = w(r) + w(r-3) in ZMod 3,
--    whence v(n+9) = -v(n) and v(n+18) = v(n).
-- 3. By strong induction on n, pseudoFactorial n ≡ (-1)^n * (1 + 3 * c(n)) (mod 9),
--    so a(n) = pseudoFactorial n % 9 is purely periodic with period 18.
-- 4. The period-18 table directly yields the order-8 linear recurrence for n > 7
--    and the rational ordinary generating function in PowerSeries ℤ.

namespace ProofA144750

open OMA.S_oeis_a144750 PowerSeries

private def cNat (n : ℕ) : ℕ := (2 * ((n + 1) / 3)) % 3

private lemma cNat_mod9 (n : ℕ) : cNat n = cNat (n % 9) := by
  unfold cNat
  have : (n + 1) / 3 % 3 = (n % 9 + 1) / 3 % 3 := by omega
  omega

private lemma cNat_add9 (n : ℕ) : cNat (n + 9) = cNat n := by
  rw [cNat_mod9 (n + 9), cNat_mod9 n, Nat.add_mod_right]

private def target (n : ℕ) : ℤ := ((-1 : ℤ) ^ n * (1 + 3 * (cNat n : ℤ))) % 9

private lemma target_mod18 (n : ℕ) : target n = target (n % 18) := by
  unfold target
  have hc : cNat n = cNat (n % 18) := by
    rw [cNat_mod9 n, cNat_mod9 (n % 18)]
    have : n % 18 % 9 = n % 9 := by omega
    rw [this]
  have hs : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 18) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h1 : Even (k + k) := ⟨k, rfl⟩
      have h2 : Even ((k + k) % 18) := by
        refine ⟨(k + k) % 18 / 2, by omega⟩
      rw [h1.neg_one_pow, h2.neg_one_pow]
    · have h1 : Odd (2 * k + 1) := ⟨k, rfl⟩
      have h2 : Odd ((2 * k + 1) % 18) := by
        refine ⟨(2 * k + 1) % 18 / 2, by omega⟩
      rw [h1.neg_one_pow, h2.neg_one_pow]
  rw [hc, hs]

-- Mod-3 binomial sum vector indexed by Fin 9
private def bvec (n : ℕ) (r : Fin 9) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), if k % 9 = r.1 then (n.choose k : ZMod 3) else 0

private def bstep (w : Fin 9 → ZMod 3) (r : Fin 9) : ZMod 3 :=
  w r + w (r - 1)

private lemma bvec_succ (n : ℕ) : bvec (n + 1) = bstep (bvec n) := by
  funext r
  unfold bvec bstep
  rw [Finset.sum_range_succ']
  have hsplit : ∀ k ∈ Finset.range (n + 1),
      (if (k + 1) % 9 = r.1 then ((n + 1).choose (k + 1) : ZMod 3) else 0) =
      (if (k + 1) % 9 = r.1 then (n.choose (k + 1) : ZMod 3) else 0) +
      (if (k + 1) % 9 = r.1 then (n.choose k : ZMod 3) else 0) := by
    intro k _
    split_ifs <;> simp [Nat.choose_succ_succ, add_comm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : (∑ k ∈ Finset.range (n + 1),
      if (k + 1) % 9 = r.1 then (n.choose (k + 1) : ZMod 3) else 0) +
      (if 0 % 9 = r.1 then ((n + 1).choose 0 : ZMod 3) else 0) =
      ∑ k ∈ Finset.range (n + 1), if k % 9 = r.1 then (n.choose k : ZMod 3) else 0 := by
    have h0 : ((n + 1).choose 0 : ZMod 3) = (n.choose 0 : ZMod 3) := by simp
    rw [h0, ← Finset.sum_range_succ' (fun k => if k % 9 = r.1 then (n.choose k : ZMod 3) else 0) (n + 1),
        Finset.sum_range_succ]
    simp [Nat.choose_succ_self]
  have h2 : (∑ k ∈ Finset.range (n + 1),
      if (k + 1) % 9 = r.1 then (n.choose k : ZMod 3) else 0) =
      ∑ k ∈ Finset.range (n + 1), if k % 9 = (r - 1).1 then (n.choose k : ZMod 3) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    have hiff : (k + 1) % 9 = r.1 ↔ k % 9 = (r - 1).1 := by
      have hr : r.1 < 9 := r.2
      have hsub : (r - 1).1 = (r.1 + 8) % 9 := by
        fin_cases r <;> decide
      omega
    simp [hiff]
  rw [add_right_comm, h1, h2]

private lemma bstep_three (w : Fin 9 → ZMod 3) (r : Fin 9) :
    bstep (bstep (bstep w)) r = w r + w (r - 3) := by
  simp only [bstep]
  have h1 : r - 1 - 1 = r - 2 := by fin_cases r <;> decide
  have h2 : r - 2 - 1 = r - 3 := by fin_cases r <;> decide
  rw [h1, h2]
  have h3 : (3 : ZMod 3) = 0 := by decide
  calc
    w r + w (r - 1) + (w (r - 1) + w (r - 2)) + (w (r - 1) + w (r - 2) + (w (r - 2) + w (r - 3)))
      = w r + 3 * w (r - 1) + 3 * w (r - 2) + w (r - 3) := by ring
    _ = w r + w (r - 3) := by rw [h3]; ring

private lemma bstep_nine (w : Fin 9 → ZMod 3) : bstep^[9] w = - w := by
  funext r
  have h9 : bstep^[9] w r =
      bstep (bstep (bstep (bstep (bstep (bstep (bstep (bstep (bstep w)))))))) r := rfl
  rw [h9]
  simp only [bstep_three]
  have h6 : r - 3 - 3 = r - 6 := by fin_cases r <;> decide
  have h9r : r - 6 - 3 = r := by fin_cases r <;> decide
  rw [h6, h9r]
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h2 : (2 : ZMod 3) = -1 := by decide
  calc
    w r + w (r - 3) + (w (r - 3) + w (r - 6)) + (w (r - 3) + w (r - 6) + (w (r - 6) + w r))
      = 2 * w r + 3 * w (r - 3) + 3 * w (r - 6) := by ring
    _ = - w r := by rw [h3, h2]; ring

private lemma bvec_add18 (n : ℕ) : bvec (n + 18) = bvec n := by
  have hiter : ∀ m, bvec (n + m) = bstep^[m] (bvec n) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← Nat.add_assoc, bvec_succ, ih, Function.iterate_succ_apply']
  have h9 : bvec (n + 9) = - bvec n := by rw [hiter 9, bstep_nine]
  have h18 : bvec (n + 18) = bvec (n + 9 + 9) := rfl
  rw [h18]
  have h9' : bvec (n + 9 + 9) = - bvec (n + 9) := by
    have hiter' : ∀ m, bvec (n + 9 + m) = bstep^[m] (bvec (n + 9)) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [← Nat.add_assoc, bvec_succ, ih, Function.iterate_succ_apply']
    rw [hiter' 9, bstep_nine]
  rw [h9', h9, neg_neg]

private def bsum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * cNat k

private lemma bsum_zmod3 (n : ℕ) :
    (bsum n : ZMod 3) = ∑ r : Fin 9, bvec n r * (cNat r.1 : ZMod 3) := by
  unfold bsum bvec
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hterm : ∑ r : Fin 9, (if k % 9 = r.1 then (n.choose k : ZMod 3) else 0) * (cNat r.1 : ZMod 3) =
      (n.choose k : ZMod 3) * (cNat (k % 9) : ZMod 3) := by
    rw [Finset.sum_eq_single ⟨k % 9, Nat.mod_lt k (by omega)⟩]
    · simp
    · intro r _ hne
      have : k % 9 ≠ r.1 := fun h => hne (Fin.ext h.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hterm, ← cNat_mod9 k]

private lemma bsum_mod3_add18 (n : ℕ) : bsum (n + 18) % 3 = bsum n % 3 := by
  have hz : (bsum (n + 18) : ZMod 3) = (bsum n : ZMod 3) := by
    rw [bsum_zmod3, bsum_zmod3, bvec_add18]
  have := (ZMod.natCast_eq_natCast_iff' (bsum (n + 18)) (bsum n) 3).mp hz
  exact this

private lemma bsum_mod3_mod18 (n : ℕ) : bsum n % 3 = bsum (n % 18) % 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < 18
    · rw [Nat.mod_eq_of_lt hlt]
    · have hsub : n = (n - 18) + 18 := by omega
      rw [hsub, bsum_mod3_add18, ih (n - 18) (by omega), Nat.add_mod_right]

private lemma pow2_mod9_mod18 (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 18) % 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < 18
    · rw [Nat.mod_eq_of_lt hlt]
    · have hsub : n = (n - 18) + 18 := by omega
      rw [hsub, pow_add, Nat.mul_mod, show 2 ^ 18 % 9 = 1 by decide, mul_one, Nat.mod_mod,
          ih (n - 18) (by omega), Nat.add_mod_right]

private lemma step_congr_base : ∀ n : Fin 18,
    ((-(2 ^ n.1 : ℤ) + 3 * (bsum n.1 : ℤ)) % 9) = target (n.1 + 1) := by decide

private lemma step_congr (n : ℕ) :
    ((-(2 ^ n : ℤ) + 3 * (bsum n : ℤ)) % 9) = target (n + 1) := by
  have h2 : (2 ^ n : ℤ) % 9 = (2 ^ (n % 18) : ℤ) % 9 := by
    exact_mod_cast pow2_mod9_mod18 n
  have hb : (bsum n : ℤ) % 3 = (bsum (n % 18) : ℤ) % 3 := by
    exact_mod_cast bsum_mod3_mod18 n
  have h3b : (3 * (bsum n : ℤ)) % 9 = (3 * (bsum (n % 18) : ℤ)) % 9 := by omega
  have hlhs : (-(2 ^ n : ℤ) + 3 * (bsum n : ℤ)) % 9 =
      (-(2 ^ (n % 18) : ℤ) + 3 * (bsum (n % 18) : ℤ)) % 9 := by omega
  rw [hlhs, step_congr_base ⟨n % 18, Nat.mod_lt n (by omega)⟩, target_mod18 (n + 1), target_mod18 (n % 18 + 1)]
  have : (n % 18 + 1) % 18 = (n + 1) % 18 := by omega
  rw [this]

private lemma pseudoFactorial_zmod9 : ∀ n : ℕ,
    (pseudoFactorial n : ZMod 9) = (-1 : ZMod 9) ^ n * (1 + 3 * (cNat n : ZMod 9)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp [pseudoFactorial, cNat]
    | succ n =>
      rw [pseudoFactorial]
      push_cast
      have hterm : ∀ k : Fin (n + 1),
          (n.choose k.1 : ZMod 9) * (pseudoFactorial k.1 : ZMod 9) * (pseudoFactorial (n - k.1) : ZMod 9) =
          (-1 : ZMod 9) ^ n * (n.choose k.1 : ZMod 9) *
            (1 + 3 * (cNat k.1 : ZMod 9) + 3 * (cNat (n - k.1) : ZMod 9)) := by
        intro k
        rw [ih k.1 (by omega), ih (n - k.1) (by omega)]
        have h9 : (9 : ZMod 9) = 0 := by decide
        have hpow : (-1 : ZMod 9) ^ k.1 * (-1 : ZMod 9) ^ (n - k.1) = (-1 : ZMod 9) ^ n := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        calc
          (n.choose k.1 : ZMod 9) * ((-1 : ZMod 9) ^ k.1 * (1 + 3 * (cNat k.1 : ZMod 9))) *
              ((-1 : ZMod 9) ^ (n - k.1) * (1 + 3 * (cNat (n - k.1) : ZMod 9)))
            = ((-1 : ZMod 9) ^ k.1 * (-1 : ZMod 9) ^ (n - k.1)) * (n.choose k.1 : ZMod 9) *
                (1 + 3 * (cNat k.1 : ZMod 9) + 3 * (cNat (n - k.1) : ZMod 9) +
                  9 * (cNat k.1 : ZMod 9) * (cNat (n - k.1) : ZMod 9)) := by ring
          _ = (-1 : ZMod 9) ^ n * (n.choose k.1 : ZMod 9) *
                (1 + 3 * (cNat k.1 : ZMod 9) + 3 * (cNat (n - k.1) : ZMod 9)) := by
            rw [hpow, h9]; ring
      simp_rw [hterm]
      rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ZMod 9) ^ n * (n.choose k : ZMod 9) *
            (1 + 3 * (cNat k : ZMod 9) + 3 * (cNat (n - k) : ZMod 9)))]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      have hsign : (-1 : ZMod 9) ^ (n + 1) * (-1 : ZMod 9) ^ n = -1 := by
        rw [← pow_add]
        have hodd : Odd (n + 1 + n) := ⟨n, by omega⟩
        exact hodd.neg_one_pow
      rw [← mul_assoc, hsign]
      have hsum_split :
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) *
              (1 + 3 * (cNat k : ZMod 9) + 3 * (cNat (n - k) : ZMod 9))) =
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9)) +
          3 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (cNat k : ZMod 9)) +
          3 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (cNat (n - k) : ZMod 9)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · congr 1
          · simp
          · apply Finset.sum_congr rfl; intro k _; ring
        · apply Finset.sum_congr rfl; intro k _; ring
      rw [hsum_split]
      have hbinom : (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9)) = (2 : ZMod 9) ^ n := by
        have hnat := congr_arg (Nat.cast (R := ZMod 9)) (Nat.sum_range_choose n)
        simpa using hnat
      have hsymm :
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (cNat (n - k) : ZMod 9)) =
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (cNat k : ZMod 9)) := by
        rw [← Finset.sum_range_reflect (fun k => (n.choose k : ZMod 9) * (cNat k : ZMod 9)) (n + 1)]
        apply Finset.sum_congr rfl
        intro k hk
        have hle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub : n + 1 - 1 - k = n - k := by omega
        rw [hsub, Nat.choose_symm hle]
      have hbsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (cNat k : ZMod 9)) = (bsum n : ZMod 9) := by
        unfold bsum; push_cast; rfl
      rw [hbinom, hsymm, hbsum]
      have h6 : (-1 : ZMod 9) * ((2 : ZMod 9) ^ n + 3 * (bsum n : ZMod 9) + 3 * (bsum n : ZMod 9)) =
          ((-(2 ^ n : ℤ) + 3 * (bsum n : ℤ)) : ℤ) := by
        have h9 : (9 : ZMod 9) = 0 := by decide
        push_cast
        calc
          (-1 : ZMod 9) * (2 ^ n + 3 * (bsum n : ZMod 9) + 3 * (bsum n : ZMod 9))
            = -2 ^ n + 3 * (bsum n : ZMod 9) - 9 * (bsum n : ZMod 9) := by ring
          _ = -2 ^ n + 3 * (bsum n : ZMod 9) := by rw [h9]; ring
      rw [h6]
      have hstep := step_congr n
      have hz : ((-(2 ^ n : ℤ) + 3 * (bsum n : ℤ) : ℤ) : ZMod 9) =
          (((-1 : ℤ) ^ (n + 1) * (1 + 3 * (cNat (n + 1) : ℤ)) : ℤ) : ZMod 9) := by
        rw [ZMod.intCast_eq_intCast_iff']
        simpa [target] using hstep
      rw [hz]
      push_cast; rfl

private lemma a_eq_target (n : ℕ) : a n = target n := by
  unfold a target
  have h := pseudoFactorial_zmod9 n
  have h' : (pseudoFactorial n : ZMod 9) = (((-1 : ℤ) ^ n * (1 + 3 * (cNat n : ℤ)) : ℤ) : ZMod 9) := by
    push_cast; exact h
  exact (ZMod.intCast_eq_intCast_iff' _ _ 9).mp h'

private lemma rec_table : ∀ r : Fin 18,
    target ((r.1 + 8) % 18) =
      target ((r.1 + 6) % 18) + target ((r.1 + 5) % 18) -
      target ((r.1 + 3) % 18) - target ((r.1 + 2) % 18) + target (r.1 % 18) := by decide

private lemma a_rec (n : ℕ) (hn : 7 < n) :
    a n = a (n - 2) + a (n - 3) - a (n - 5) - a (n - 6) + a (n - 8) := by
  simp only [a_eq_target]
  let m := n - 8
  have hn0 : n = m + 8 := by omega
  have hn2 : n - 2 = m + 6 := by omega
  have hn3 : n - 3 = m + 5 := by omega
  have hn5 : n - 5 = m + 3 := by omega
  have hn6 : n - 6 = m + 2 := by omega
  have hn8 : n - 8 = m := rfl
  rw [hn2, hn3, hn5, hn6, hn8, hn0,
      target_mod18 (m + 8), target_mod18 (m + 6), target_mod18 (m + 5),
      target_mod18 (m + 3), target_mod18 (m + 2), target_mod18 m]
  have hmod : ∀ d : ℕ, (m + d) % 18 = (m % 18 + d) % 18 := fun d => by omega
  rw [hmod 8, hmod 6, hmod 5, hmod 3, hmod 2]
  have hr := rec_table ⟨m % 18, Nat.mod_lt m (by omega)⟩
  dsimp only at hr
  rwa [Nat.mod_mod] at hr

private lemma a_base :
    a 0 = 1 ∧ a 1 = 8 ∧ a 2 = 7 ∧ a 3 = 2 ∧ a 4 = 7 ∧ a 5 = 5 ∧ a 6 = 4 ∧ a 7 = 5 := by
  simp only [a_eq_target]
  decide

private lemma gf_eq :
    let X : PowerSeries ℤ := PowerSeries.X
    PowerSeries.mk a * ((X - 1) * (X + 1) * (X ^ 6 - X ^ 3 + 1)) =
      -8 * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 -
        6 * X ^ 2 - 8 * X - 1 := by
  intro X
  have hden : (X - 1) * (X + 1) * (X ^ 6 - X ^ 3 + 1) =
      X ^ 8 - X ^ 6 - X ^ 5 + X ^ 3 + X ^ 2 - 1 := by ring
  rw [hden]
  ext n
  have hcoeff_pow : ∀ k : ℕ, (PowerSeries.coeff n) (PowerSeries.mk a * X ^ k) =
      if k ≤ n then a (n - k) else 0 := by
    intro k
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
    simp
  have hlhs : (PowerSeries.coeff n) (PowerSeries.mk a * (X ^ 8 - X ^ 6 - X ^ 5 + X ^ 3 + X ^ 2 - 1)) =
      (if 8 ≤ n then a (n - 8) else 0) -
      (if 6 ≤ n then a (n - 6) else 0) -
      (if 5 ≤ n then a (n - 5) else 0) +
      (if 3 ≤ n then a (n - 3) else 0) +
      (if 2 ≤ n then a (n - 2) else 0) -
      a n := by
    rw [mul_sub, mul_add, mul_add, mul_sub, mul_sub, mul_one]
    simp only [map_sub, map_add, hcoeff_pow, PowerSeries.coeff_mk]
  rw [hlhs]
  have hX1 : (PowerSeries.coeff n) X = if n = 1 then 1 else 0 := by
    simp [X, PowerSeries.coeff_X]
  have hXk : ∀ k : ℕ, (PowerSeries.coeff n) (X ^ k) = if n = k then 1 else 0 := by
    intro k; simp [X, PowerSeries.coeff_X_pow]
  have h1 : (PowerSeries.coeff n) (1 : PowerSeries ℤ) = if n = 0 then 1 else 0 := by
    simp [PowerSeries.coeff_one]
  have hrhs : (PowerSeries.coeff n)
      (-8 * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 - 6 * X ^ 2 - 8 * X - 1) =
      -8 * (if n = 7 then 1 else 0) - 4 * (if n = 6 then 1 else 0) +
      3 * (if n = 5 then 1 else 0) + 8 * (if n = 4 then 1 else 0) +
      7 * (if n = 3 then 1 else 0) - 6 * (if n = 2 then 1 else 0) -
      8 * (if n = 1 then 1 else 0) - (if n = 0 then 1 else 0) := by
    have hnum : (-8 * X ^ 7 - 4 * X ^ 6 + 3 * X ^ 5 + 8 * X ^ 4 + 7 * X ^ 3 - 6 * X ^ 2 - 8 * X - 1 : PowerSeries ℤ) =
        (-8 : ℤ) • X ^ 7 - (4 : ℤ) • X ^ 6 + (3 : ℤ) • X ^ 5 +
        (8 : ℤ) • X ^ 4 + (7 : ℤ) • X ^ 3 - (6 : ℤ) • X ^ 2 -
        (8 : ℤ) • X - 1 := by
      simp [zsmul_eq_mul]
    rw [hnum]
    simp only [map_sub, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, hXk, hX1, h1]
  rw [hrhs]
  rcases a_base with ⟨h0, h1', h2, h3, h4, h5, h6, h7⟩
  by_cases hn : 7 < n
  · have hrec := a_rec n hn
    have hne : n ≠ 7 ∧ n ≠ 6 ∧ n ≠ 5 ∧ n ≠ 4 ∧ n ≠ 3 ∧ n ≠ 2 ∧ n ≠ 1 ∧ n ≠ 0 := by omega
    have hge : 8 ≤ n ∧ 6 ≤ n ∧ 5 ≤ n ∧ 3 ≤ n ∧ 2 ≤ n := by omega
    simp only [hne, hge, ↓reduceIte]
    omega
  · interval_cases n <;> simp [h0, h1', h2, h3, h4, h5, h6, h7]

end ProofA144750

theorem OMA.solution : type_of% @OMA.S_oeis_a144750.main :=
  ⟨ProofA144750.a_rec, ProofA144750.gf_eq⟩
