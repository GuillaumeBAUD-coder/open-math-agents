import OMAStatements.S_oeis_a277216

/-!
# Fixed points of the decimal digit product of the divisor sum

For a positive fixed point, the nonzero decimal digits give a factorization
over 2, 3, 5, and 7. The geometric prime-power divisor sums give a uniform
upper bound on the ratio of the divisor sum to the fixed point. Retaining
the leading digit in the product estimate bounds the divisor sum to fifteen
digits. Each digit contributes at most six units to a weighted exponent
budget, so a kernel-checked finite calculation completes the classification.
-/

namespace OMA.A277216

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

private def geometric (p i : ℕ) : ℕ := (p ^ (i + 1) - 1) / (p - 1)

private theorem sigmaPrimePower (p e : ℕ) (hp : p.Prime) : σ 1 (p ^ e) = geometric p e := by
  rw [sigma_one_apply_prime_pow hp, geometric, ← geom_sum_mul_of_one_le hp.one_lt.le]
  exact (Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hp.one_lt)).symm

private theorem coprimePowers {p q : ℕ} (hpq : p.Coprime q) (i j : ℕ) :
    (p ^ i).Coprime (q ^ j) :=
  (hpq.pow_left i).pow_right j

private theorem sigmaSmooth (i j k l : ℕ) :
    σ 1 (2 ^ i * 3 ^ j * 5 ^ k * 7 ^ l) =
      geometric 2 i * geometric 3 j * geometric 5 k * geometric 7 l := by
  have h23 := coprimePowers (by decide : Nat.Coprime 2 3) i j
  have h25 := coprimePowers (by decide : Nat.Coprime 2 5) i k
  have h27 := coprimePowers (by decide : Nat.Coprime 2 7) i l
  have h35 := coprimePowers (by decide : Nat.Coprime 3 5) j k
  have h37 := coprimePowers (by decide : Nat.Coprime 3 7) j l
  have h57 := coprimePowers (by decide : Nat.Coprime 5 7) k l
  rw [isMultiplicative_sigma.map_mul_of_coprime ((h27.mul_left h37).mul_left h57),
    isMultiplicative_sigma.map_mul_of_coprime (h25.mul_left h35),
    isMultiplicative_sigma.map_mul_of_coprime h23,
    sigmaPrimePower 2 i Nat.prime_two, sigmaPrimePower 3 j Nat.prime_three,
    sigmaPrimePower 5 k Nat.prime_five, sigmaPrimePower 7 l Nat.prime_seven]

private theorem geometricBound {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p - 1) * geometric p e ≤ p * p ^ e := by
  rw [← sigmaPrimePower p e hp, sigma_one_apply_prime_pow hp, mul_comm (p - 1),
    geom_sum_mul_of_one_le hp.one_lt.le, pow_succ, mul_comm (p ^ e)]
  exact Nat.sub_le _ _

private theorem sigmaSmoothBound (i j k l : ℕ) :
    48 * σ 1 (2 ^ i * 3 ^ j * 5 ^ k * 7 ^ l) ≤ 210 * (2 ^ i * 3 ^ j * 5 ^ k * 7 ^ l) := by
  have h2 : 1 * geometric 2 i ≤ 2 * 2 ^ i := geometricBound Nat.prime_two i
  have h3 : 2 * geometric 3 j ≤ 3 * 3 ^ j := geometricBound Nat.prime_three j
  have h5 : 4 * geometric 5 k ≤ 5 * 5 ^ k := geometricBound Nat.prime_five k
  have h7 : 6 * geometric 7 l ≤ 7 * 7 ^ l := geometricBound Nat.prime_seven l
  rw [sigmaSmooth]
  calc
    _ = (1 * geometric 2 i) * (2 * geometric 3 j) *
          (4 * geometric 5 k) * (6 * geometric 7 l) := by ring
    _ ≤ (2 * 2 ^ i) * (3 * 3 ^ j) * (5 * 5 ^ k) * (7 * 7 ^ l) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h5) h7
    _ = _ := by ring

private def smoothN (a b c d : ℕ) : ℕ := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d

private theorem digit_factorization (e : ℕ) (hp : 0 < e) (hlt : e < 10) :
    ∃ a b c d : ℕ, e = smoothN a b c d ∧ 2*a + 3*b + 6*c + 6*d ≤ 6 := by
  interval_cases e
  · exact ⟨0,0,0,0,by decide,by decide⟩
  · exact ⟨1,0,0,0,by decide,by decide⟩
  · exact ⟨0,1,0,0,by decide,by decide⟩
  · exact ⟨2,0,0,0,by decide,by decide⟩
  · exact ⟨0,0,1,0,by decide,by decide⟩
  · exact ⟨1,1,0,0,by decide,by decide⟩
  · exact ⟨0,0,0,1,by decide,by decide⟩
  · exact ⟨3,0,0,0,by decide,by decide⟩
  · exact ⟨0,2,0,0,by decide,by decide⟩

/-- Each decimal digit uses at most six units of the weighted exponent budget. -/
private theorem product_factorization (digits : List ℕ)
    (hd : ∀ x ∈ digits, x < 10) (hp : 0 < digits.prod) :
    ∃ a b c d : ℕ, digits.prod = smoothN a b c d ∧
      2*a + 3*b + 6*c + 6*d ≤ 6*digits.length := by
  induction digits with
  | nil => exact ⟨0,0,0,0,by decide,by decide⟩
  | cons e digits ih =>
    rw [List.prod_cons] at hp
    have hep : 0 < e := Nat.pos_of_mul_pos_right hp
    have hdp : 0 < digits.prod := Nat.pos_of_mul_pos_left hp
    obtain ⟨i,j,k,l,he,heb⟩ := digit_factorization e hep (hd e List.mem_cons_self)
    obtain ⟨a,b,c,d,ht,htb⟩ :=
      ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)) hdp
    refine ⟨i+a,j+b,k+c,l+d,?_,?_⟩
    · rw [List.prod_cons, he, ht]
      simp only [smoothN, pow_add]
      ring
    · simp only [List.length_cons]
      omega

/-- Keep the leading digit on both sides of the digit-product estimate. -/
private theorem leading_digit_bound (digits : List ℕ)
    (hn : digits ≠ []) (hd : ∀ x ∈ digits, x < 10) :
    10 ^ (digits.length - 1) * digits.prod ≤
      9 ^ (digits.length - 1) * Nat.ofDigits 10 digits := by
  induction digits with
  | nil => contradiction
  | cons e digits ih =>
    cases digits with
    | nil => simp
    | cons x xs =>
      let tail := x :: xs
      have hb := ih (by simp) (fun y hy => hd y (List.mem_cons_of_mem _ hy))
      change 10 ^ (tail.length - 1) * tail.prod ≤
        9 ^ (tail.length - 1) * Nat.ofDigits 10 tail at hb
      have he : e ≤ 9 := by
        have := hd e List.mem_cons_self
        omega
      have hlen : tail.length = tail.length - 1 + 1 := by simp [tail]
      change 10 ^ tail.length * (e * tail.prod) ≤
        9 ^ tail.length * Nat.ofDigits 10 (e :: tail)
      calc
        _ = (10 * e) * (10 ^ (tail.length - 1) * tail.prod) := by
          rw [show 10 ^ tail.length = 10 ^ (tail.length - 1) * 10 by rw [← pow_succ, ← hlen]]
          ring
        _ ≤ (10 * 9) * (9 ^ (tail.length - 1) * Nat.ofDigits 10 tail) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 10 he) hb
        _ = 9 ^ tail.length * (10 * Nat.ofDigits 10 tail) := by
          rw [show 9 ^ tail.length = 9 ^ (tail.length - 1) * 9 by rw [← pow_succ, ← hlen]]
          ring
        _ ≤ _ := by
          rw [Nat.ofDigits_cons]
          exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

private theorem powers_separate (k : ℕ) (hk : 15 ≤ k) : 210 * 9 ^ k < 48 * 10 ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h₁ : 210 * 9 ^ 15 < 48 * 10 ^ 15 := by decide +kernel
  have h₂ : 9 ^ j ≤ 10 ^ j := Nat.pow_le_pow_left (by decide) _
  rw [pow_add, pow_add, ← mul_assoc, ← mul_assoc]
  exact (Nat.mul_lt_mul_of_pos_right h₁ (by positivity)).trans_le (Nat.mul_le_mul_left _ h₂)

private theorem digit_length_bound (n s : ℕ) (hp : 0 < n)
    (hs : 48*s ≤ 210*n) (hfix : (Nat.digits 10 s).prod = n)
    (hne : Nat.digits 10 s ≠ []) : (Nat.digits 10 s).length ≤ 15 := by
  let k := (Nat.digits 10 s).length - 1
  have hd := leading_digit_bound (Nat.digits 10 s) hne
    (fun _ hx => Nat.digits_lt_base (by decide) hx)
  rw [Nat.ofDigits_digits, hfix] at hd
  change 10^k * n ≤ 9^k * s at hd
  have hcancel : (48 * 10^k) * n ≤ (210 * 9^k) * n := by
    calc
      _ = 48 * (10^k*n) := by ring
      _ ≤ 48 * (9^k*s) := Nat.mul_le_mul_left _ hd
      _ = 9^k * (48*s) := by ring
      _ ≤ 9^k * (210*n) := Nat.mul_le_mul_left _ hs
      _ = _ := by ring
  have hpow := Nat.le_of_mul_le_mul_right hcancel hp
  by_contra! hh
  have hk : 15 ≤ k := by dsimp [k]; omega
  exact (not_lt_of_ge hpow) (powers_separate k hk)

/-- A fuel bound keeps the certificate's digit calculation transparent to the kernel. -/
private def digitProduct : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, n => if n = 0 then 1 else (n % 10) * digitProduct f (n / 10)

private theorem digitProduct_correct (f n : ℕ) (h : n < 10^f) :
    digitProduct f n = (Nat.digits 10 n).prod := by
  induction f generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, digitProduct]
  | succ f ih =>
    by_cases h0 : n = 0
    · simp [h0, digitProduct]
    · have hn : 0 < n := Nat.pos_of_ne_zero h0
      rw [digitProduct, if_neg h0, Nat.digits_of_two_le_of_pos (by decide) hn, List.prod_cons]
      rw [ih]
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ, Nat.mul_comm] using h

private def smoothSigma (a b c d : ℕ) : ℕ :=
  geometric 2 a * geometric 3 b * geometric 5 c * geometric 7 d

private def testTuple (a b c d : ℕ) : Bool :=
  let n := smoothN a b c d
  (n == 1) || (n == 210) || (digitProduct 15 (smoothSigma a b c d) != n)

private def testChunk (a : ℕ) : Bool :=
  (List.range ((90 - 2*a)/3 + 1)).all fun b =>
    (List.range ((90 - 2*a - 3*b)/6 + 1)).all fun c =>
      (List.range ((90 - 2*a - 3*b - 6*c)/6 + 1)).all fun d =>
        testTuple a b c d

set_option maxHeartbeats 0 in
private theorem chunk_correct (a : ℕ) (ha : a ≤ 45) : testChunk a = true := by
  interval_cases a <;> decide +kernel

private theorem tuple_correct (a b c d : ℕ) (h : 2*a + 3*b + 6*c + 6*d ≤ 90)
    (hf : digitProduct 15 (smoothSigma a b c d) = smoothN a b c d) :
    smoothN a b c d = 1 ∨ smoothN a b c d = 210 := by
  have ha : a ≤ 45 := by omega
  have hb : b ∈ List.range ((90 - 2*a)/3 + 1) := by rw [List.mem_range]; omega
  have hc : c ∈ List.range ((90 - 2*a - 3*b)/6 + 1) := by rw [List.mem_range]; omega
  have hd : d ∈ List.range ((90 - 2*a - 3*b - 6*c)/6 + 1) := by rw [List.mem_range]; omega
  have ht := chunk_correct a ha
  unfold testChunk at ht
  have hfirst := (List.all_eq_true.mp ht) _ hb
  have hsecond := (List.all_eq_true.mp hfirst) _ hc
  have hthird := (List.all_eq_true.mp hsecond) _ hd
  simpa [testTuple, hf] using hthird

private theorem fixedPoints (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (σ 1 n)).prod = n ↔ n = 1 ∨ n = 210 := by
  constructor
  · intro hfix
    let s := σ 1 n
    let ds := Nat.digits 10 s
    change ds.prod = n at hfix
    have hd : ∀ x ∈ ds, x < 10 := fun _ hx => Nat.digits_lt_base (by decide) hx
    by_cases hne : ds = []
    · left
      simpa only [hne, List.prod_nil] using hfix.symm
    have hp : 0 < ds.prod := hfix.symm ▸ hn
    obtain ⟨a, b, c, d, hN, hbudget⟩ := product_factorization ds hd hp
    have hnN : n = smoothN a b c d := hfix.symm.trans hN
    have hsComp : s = smoothSigma a b c d := by
      dsimp [s]
      rw [hnN]
      exact sigmaSmooth a b c d
    have hsBound : 48 * s ≤ 210 * n := by
      dsimp [s]
      rw [hnN]
      exact sigmaSmoothBound a b c d
    have hlen : ds.length ≤ 15 := digit_length_bound n s hn hsBound hfix hne
    have hsl : s < 10 ^ 15 := (Nat.lt_base_pow_length_digits (by decide : 1 < 10)).trans_le
      (Nat.pow_le_pow_right (by decide) hlen)
    have hchecked : digitProduct 15 (smoothSigma a b c d) = smoothN a b c d := by
      calc
        _ = digitProduct 15 s := congrArg _ hsComp.symm
        _ = ds.prod := digitProduct_correct 15 s hsl
        _ = _ := hN
    simpa only [hnN] using tuple_correct a b c d (by omega) hchecked
  · rintro (rfl | rfl)
    · have hs : σ 1 1 = 1 := by
        simpa only [pow_zero, one_mul] using (sigmaSmooth 0 0 0 0).trans (by decide)
      rw [hs, ← digitProduct_correct 15 _ (by decide)]
      decide
    · have hs : σ 1 210 = 576 := by
        calc
          σ 1 210 = σ 1 (2 ^ 1 * 3 ^ 1 * 5 ^ 1 * 7 ^ 1) := by congr 1
          _ = 576 := (sigmaSmooth 1 1 1 1).trans (by decide)
      rw [hs, ← digitProduct_correct 15 _ (by decide)]
      decide

end OMA.A277216

theorem OMA.solution : type_of% @OMA.S_oeis_a277216.main := OMA.A277216.fixedPoints
