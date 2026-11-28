import OMAStatements.S_oeis_a358319

-- The gcd sum equals the Dirichlet convolution of g(d) = d (-1)^ω(d) with φ (group k by gcd(n, k)
-- and use φ(n/d) = #{k < n : gcd(n, k) = d}). Both a and g * φ are multiplicative, and at p^(k+1)
-- the convolution is p^k (p - 1) - k p^k (p - 1) - p^(k+1) = ((p - 2) - (p - 1)(k + 1)) p^k.

namespace OMA.A358319
open ArithmeticFunction

def af (u : ℕ → ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else u n, by simp⟩

lemma af_apply (u : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) : af u n = u n := by
  show (if n = 0 then 0 else u n) = u n
  rw [if_neg hn]

lemma conv (u v : ℕ → ℤ) {n : ℕ} (_hn : n ≠ 0) :
    (af u * af v) n = ∑ d ∈ n.divisors, u d * v (n / d) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => af u x * af v y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_ne_zero hd0)).ne'
  rw [af_apply u hd0, af_apply v hq]

lemma mult_af (u : ℕ → ℤ) (h1 : u 1 = 1)
    (hm : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → u (m * n) = u m * u n) :
    (af u).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [af_apply u one_ne_zero, h1], fun {m n} hm0 hn0 hmn => ?_⟩
  rw [af_apply u (mul_ne_zero hm0 hn0), af_apply u hm0, af_apply u hn0, hm m n hm0 hn0 hmn]

def g (d : ℕ) : ℤ := (d : ℤ) * (-1) ^ (cardDistinctFactors d)

def F (k n : ℕ) : ℤ := (Nat.gcd k n : ℤ) * (-1) ^ (cardDistinctFactors (Nat.gcd k n))

lemma gcd_sum (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, F k n = ∑ d ∈ n.divisors, g d * (Nat.totient (n / d) : ℤ) := by
  have e1 : ∑ k ∈ Finset.Icc 1 n, F k n = ∑ k ∈ Finset.range n, g (Nat.gcd n k) := by
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from rfl, Finset.sum_Ico_eq_sum_range,
      show n + 1 - 1 = n by omega]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [F, g, Nat.gcd_zero_right]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [add_comm 1 k, Nat.gcd_comm (k + 1)]
    · rw [add_comm 1 m, Nat.gcd_self]
  rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := n.divisors)
    (g := fun k => Nat.gcd n k) (fun k _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn.ne'⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
    Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul, mul_comm]

lemma prime_pow_val (p k : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (k + 2), g (p ^ j) * (Nat.totient (p ^ (k + 1) / p ^ j) : ℤ) =
      (((p : ℤ) - 2) - ((p : ℤ) - 1) * (k + 1 : ℕ)) * (p : ℤ) ^ k := by
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by rw [Nat.cast_sub hp.one_le]; simp
  have gpow : ∀ j, j ≠ 0 → g (p ^ j) = -(p : ℤ) ^ j := by
    intro j hj
    rw [g, cardDistinctFactors_apply_prime_pow hp hj]; push_cast; ring
  have hdiv : ∀ j, j ≤ k + 1 → p ^ (k + 1) / p ^ j = p ^ (k + 1 - j) := by
    intro j hj
    rw [Nat.pow_div hj hp.pos]
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hmid : ∀ j ∈ Finset.range k,
      g (p ^ (j + 1)) * (Nat.totient (p ^ (k + 1) / p ^ (j + 1)) : ℤ) =
        -((p : ℤ) ^ k * ((p : ℤ) - 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [gpow _ (by omega), hdiv _ (by omega), Nat.totient_prime_pow hp (by omega)]
    push_cast [hp1]
    have : (p : ℤ) ^ (j + 1) * (p : ℤ) ^ (k - j - 1) = (p : ℤ) ^ k := by
      rw [← pow_add]; congr 1; omega
    linear_combination (-((p : ℤ) - 1)) * this
  rw [Finset.sum_congr rfl hmid, Finset.sum_const, Finset.card_range, gpow _ (by omega),
    hdiv _ le_rfl, Nat.sub_self, pow_zero, Nat.totient_one, Nat.div_one,
    Nat.totient_prime_pow hp (by omega)]
  simp only [g, Nat.cast_one, one_mul, cardDistinctFactors_one, pow_zero, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_one]
  push_cast [hp1]
  ring

end OMA.A358319

open OMA.A358319 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a358319.main := by
  intro a ha1 hmul hpp n hn
  have hA : (af a).IsMultiplicative := mult_af a ha1 (fun m n _ _ h => hmul m n h)
  have hG : (af g).IsMultiplicative := by
    apply mult_af
    · simp [g, cardDistinctFactors_one]
    · intro m n hm hn hmn
      rw [g, g, g, cardDistinctFactors_mul hmn]; push_cast; ring
  have hΦ : (af (fun n => (Nat.totient n : ℤ))).IsMultiplicative := by
    apply mult_af
    · simp
    · intro m n _ _ hmn
      rw [Nat.totient_mul hmn]; push_cast; ring
  have heq : af a = af g * af (fun n => (Nat.totient n : ℤ)) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ (hG.mul hΦ)]
    intro p i hp
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, hA.map_one, (hG.mul hΦ).map_one]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hne : p ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [af_apply _ hne, hpp p (k + 1) hp (by omega), conv _ _ hne,
        Nat.sum_divisors_prime_pow hp, prime_pow_val p k hp, Nat.add_sub_cancel]
  have := DFunLike.congr_fun heq n
  rw [af_apply _ hn.ne', conv _ _ hn.ne', ← gcd_sum n hn] at this
  exact this

