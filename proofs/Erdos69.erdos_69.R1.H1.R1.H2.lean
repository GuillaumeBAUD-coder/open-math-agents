import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1

-- Step Erdos69.erdos_69.R1.H1.R1.H2 (Erdős Problem 69): small and medium primes
-- Credit: @chris01-dev

/-!
The weighted count of prime factors up to `R = x ^ (1 / (log log x) ^ 2)` at the near shifts,
times `q`, is at distance at least `1 / 10` from the integers for a tenth of the progression
(Tao–Teräväinen, arXiv:2512.01739, Sections 9.4 and 9.9 to 9.11).

The primes dividing the modulus contribute a constant. For the others the phase of the count
is a product over primes of local factors `1 + g ℓ n`, of modulus one, and

* `prod_trunc`: the expansion of such a product can be truncated at subsets of bounded size,
  with an error given by the next elementary symmetric sum of the norms;
* `moment_ind`, `moment1`: over the progression the local factors at distinct primes are
  independent up to a bounded error (Chinese remainder theorem), so each truncated term is
  the product of the local means `Γ / ℓ`;
* `fourier_bound`: hence the exponential sum is the model product over `1 + Γ / ℓ`, up to
  errors controlled by `esymm_le` and a count of subsets;
* `re_bound`, `prod_model_bound`, `prime_recip_lower`: the real part of `Γ` is negative of
  size `q ^ 2 / 2 ^ K`, and the reciprocals of the primes between `exp (exp (l / 2))` and `R`
  sum to at least a multiple of `log log x` (Chebyshev, by blocks), so the model product is
  tiny;
* `prop_of_fourier`: a small exponential sum forces the proportion statement.

This replaces the moment method of the paper by a direct expansion of the product; the
truncation uses only that every partial product has modulus at most one.
-/

namespace E69S3

lemma count_range (B m v : ℕ) (hm : 0 < m) :
    (((Finset.range B).filter (fun n => n % m = v % m)).card : ℝ) ≤ (B : ℝ) / m + 1 ∧
    (B : ℝ) / m - 1 ≤ (((Finset.range B).filter (fun n => n % m = v % m)).card : ℝ) := by
  have h := Nat.count_modEq_card (b := B) hm v
  have e : ((Finset.range B).filter (fun n => n % m = v % m)).card
      = B.count (· ≡ v [MOD m]) := by
    rw [Nat.count_eq_card_filter_range]
    rfl
  rw [e, h]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : ((B / m : ℕ) : ℝ) * m ≤ B := by exact_mod_cast Nat.div_mul_le_self B m
  have hlt : (B : ℝ) < ((B / m : ℕ) + 1) * m := by
    have : B < (B / m + 1) * m := by
      have := Nat.div_add_mod B m
      have := Nat.mod_lt B hm
      nlinarith
    exact_mod_cast this
  have h1 : ((B / m : ℕ) : ℝ) ≤ (B : ℝ) / m := by
    rw [le_div_iff₀ hmR]
    exact hdiv
  have h2 : (B : ℝ) / m < (B / m : ℕ) + 1 := by
    rw [div_lt_iff₀ hmR]
    exact hlt
  push_cast
  constructor
  · split_ifs <;> simp <;> linarith
  · split_ifs <;> simp <;> linarith

/-- The number of integers of an interval in a residue class, up to an error at most 2. -/
lemma ap_count (L U m v : ℕ) (hm : 0 < m) (hLU : L ≤ U + 1) :
    |(((Finset.Icc L U).filter (fun n => n % m = v % m)).card : ℝ)
      - ((U : ℝ) + 1 - L) / m| ≤ 2 := by
  have hun : Finset.range (U + 1) = Finset.range L ∪ Finset.Icc L U := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdis : Disjoint ((Finset.range L).filter (fun n => n % m = v % m))
      ((Finset.Icc L U).filter (fun n => n % m = v % m)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    have a1 := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have a2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hcard : ((Finset.range (U + 1)).filter (fun n => n % m = v % m)).card
      = ((Finset.range L).filter (fun n => n % m = v % m)).card
        + ((Finset.Icc L U).filter (fun n => n % m = v % m)).card := by
    rw [hun, Finset.filter_union, Finset.card_union_of_disjoint hdis]
  obtain ⟨u1, u2⟩ := count_range (U + 1) m v hm
  obtain ⟨l1, l2⟩ := count_range L m v hm
  have hc : (((Finset.range (U + 1)).filter (fun n => n % m = v % m)).card : ℝ)
      = (((Finset.range L).filter (fun n => n % m = v % m)).card : ℝ)
        + (((Finset.Icc L U).filter (fun n => n % m = v % m)).card : ℝ) := by
    exact_mod_cast hcard
  have e : ((U : ℝ) + 1 - L) / m = ((U + 1 : ℕ) : ℝ) / m - (L : ℝ) / m := by
    push_cast
    ring
  rw [e, abs_le]
  constructor <;> linarith

lemma dvd_iff_mod (ℓ n : ℕ) (r : ℤ) (hℓ : 0 < ℓ) :
    ((ℓ : ℤ) ∣ (n : ℤ) + r) ↔ n % ℓ = ((-r) % (ℓ : ℤ)).toNat % ℓ := by
  have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have h1 : ((ℓ : ℤ) ∣ (n : ℤ) + r) ↔ (-r) ≡ (n : ℤ) [ZMOD ℓ] := by
    rw [Int.modEq_iff_dvd, sub_neg_eq_add]
  have h2 : (-r) ≡ ((((-r) % (ℓ : ℤ)).toNat : ℕ) : ℤ) [ZMOD ℓ] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')]
    exact (Int.mod_modEq _ _).symm
  rw [h1]
  constructor
  · intro h
    exact Int.natCast_modEq_iff.mp (h.symm.trans h2)
  · intro h
    exact h2.trans (Int.natCast_modEq_iff.mpr h).symm

lemma crt2 (m1 m2 v1 v2 : ℕ) (hco : Nat.Coprime m1 m2) :
    ∃ c : ℕ, ∀ n : ℕ, (n % m1 = v1 % m1 ∧ n % m2 = v2 % m2)
      ↔ n % (m1 * m2) = c % (m1 * m2) := by
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hco v1 v2
  refine ⟨c, fun n => ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
      ⟨(show n ≡ v1 [MOD m1] from h1).trans hc1.symm,
        (show n ≡ v2 [MOD m2] from h2).trans hc2.symm⟩
  · intro h
    obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr
      (show n ≡ c [MOD m1 * m2] from h)
    exact ⟨h1.trans hc1, h2.trans hc2⟩

/-- In a progression modulo `Q`, the integers `n` with `ℓ ∣ n + r` have relative density
`1 / ℓ` up to a bounded error, for a prime `ℓ` not dividing `Q`. -/
lemma count_one (L U Q b ℓ : ℕ) (r : ℤ) (hQ : 0 < Q) (hℓ : ℓ.Prime) (hco : Nat.Coprime Q ℓ)
    (hLU : L ≤ U + 1) :
    |((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
        (fun n : ℕ => (ℓ : ℤ) ∣ (n : ℤ) + r)).card : ℝ)
      - (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / ℓ| ≤ 3 := by
  obtain ⟨c, hc⟩ := crt2 Q ℓ b ((-r) % (ℓ : ℤ)).toNat hco
  have hfil : ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
      (fun n : ℕ => (ℓ : ℤ) ∣ (n : ℤ) + r)
      = (Finset.Icc L U).filter (fun n => n % (Q * ℓ) = c % (Q * ℓ)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [dvd_iff_mod ℓ n r hℓ.pos]
    exact hc n
  rw [hfil]
  have h1 := ap_count L U (Q * ℓ) c (Nat.mul_pos hQ hℓ.pos) hLU
  have h2 := ap_count L U Q b hQ hLU
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  have e : ((U : ℝ) + 1 - L) / ((Q * ℓ : ℕ) : ℝ) = ((U : ℝ) + 1 - L) / Q / ℓ := by
    push_cast
    rw [div_div]
  rw [e] at h1
  rw [abs_le] at h1 h2 ⊢
  have hd : ∀ t : ℝ, t / ℓ ≤ |t| / 2 := by
    intro t
    calc t / ℓ ≤ |t| / ℓ := div_le_div_of_nonneg_right (le_abs_self t) (by linarith)
      _ ≤ |t| / 2 := div_le_div_of_nonneg_left (abs_nonneg t) (by norm_num) hℓR
  have key : |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / ℓ
      - ((U : ℝ) + 1 - L) / Q / ℓ| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ℓ)]
    have habs : |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
        - ((U : ℝ) + 1 - L) / Q| ≤ 2 := abs_le.mpr h2
    calc |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
          - ((U : ℝ) + 1 - L) / Q| / ℓ ≤ 2 / ℓ :=
          div_le_div_of_nonneg_right habs (by linarith)
      _ ≤ 2 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hℓR
      _ = 1 := by norm_num
  rw [abs_le] at key
  constructor <;> linarith

/-- The same for two distinct primes and two shifts. -/
lemma count_two (L U Q b ℓ ℓ' : ℕ) (r r' : ℤ) (hQ : 0 < Q) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hne : ℓ ≠ ℓ') (hco : Nat.Coprime Q ℓ) (hco' : Nat.Coprime Q ℓ') (hLU : L ≤ U + 1) :
    |((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
        (fun n : ℕ => (ℓ : ℤ) ∣ (n : ℤ) + r ∧ (ℓ' : ℤ) ∣ (n : ℤ) + r')).card : ℝ)
      - (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / (ℓ * ℓ')| ≤ 3 := by
  have hll : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
  obtain ⟨c1, hc1⟩ := crt2 ℓ ℓ' ((-r) % (ℓ : ℤ)).toNat ((-r') % (ℓ' : ℤ)).toNat hll
  obtain ⟨c, hc⟩ := crt2 Q (ℓ * ℓ') b c1 (Nat.Coprime.mul_right hco hco')
  have hfil : ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
      (fun n : ℕ => (ℓ : ℤ) ∣ (n : ℤ) + r ∧ (ℓ' : ℤ) ∣ (n : ℤ) + r')
      = (Finset.Icc L U).filter (fun n => n % (Q * (ℓ * ℓ')) = c % (Q * (ℓ * ℓ'))) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun n _ => ?_
    rw [dvd_iff_mod ℓ n r hℓ.pos, dvd_iff_mod ℓ' n r' hℓ'.pos, hc1 n]
    exact hc n
  rw [hfil]
  have hm : 0 < ℓ * ℓ' := Nat.mul_pos hℓ.pos hℓ'.pos
  have h1 := ap_count L U (Q * (ℓ * ℓ')) c (Nat.mul_pos hQ hm) hLU
  have h2 := ap_count L U Q b hQ hLU
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmR : (2 : ℝ) ≤ (ℓ : ℝ) * ℓ' := by
    have a1 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
    have a2 : (2 : ℝ) ≤ ℓ' := by exact_mod_cast hℓ'.two_le
    nlinarith
  have e : ((U : ℝ) + 1 - L) / ((Q * (ℓ * ℓ') : ℕ) : ℝ)
      = ((U : ℝ) + 1 - L) / Q / ((ℓ : ℝ) * ℓ') := by
    push_cast
    rw [div_div]
  rw [e] at h1
  have key : |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / ((ℓ : ℝ) * ℓ')
      - ((U : ℝ) + 1 - L) / Q / ((ℓ : ℝ) * ℓ')| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (ℓ : ℝ) * ℓ')]
    calc |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
          - ((U : ℝ) + 1 - L) / Q| / ((ℓ : ℝ) * ℓ') ≤ 2 / ((ℓ : ℝ) * ℓ') :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ ≤ 2 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      _ = 1 := by norm_num
  rw [abs_le] at h1 key ⊢
  constructor <;> linarith



/-- Chebyshev on a dyadic block: the primes in `[2 ^ j, 2 ^ (j + 1))` have reciprocal sum at
most `4 / j`. -/
lemma block_sum (j : ℕ) (hj : 1 ≤ j) :
    ∑ ℓ ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / ℓ ≤ 4 / j := by
  classical
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  -- each term is at most 1 / 2 ^ j
  have h1 : ∑ ℓ ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / ℓ
      ≤ (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * (1 / 2 ^ j) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun ℓ hℓ => ?_
    have hle : 2 ^ j ≤ ℓ := (Finset.mem_Ico.mp (Finset.mem_filter.mp hℓ).1).1
    have hleR : (2 : ℝ) ^ j ≤ ℓ := by exact_mod_cast hle
    exact one_div_le_one_div_of_le h2j hleR
  -- the number of primes in the block
  have h2 : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * (j * Real.log 2)
      ≤ Real.log 4 * (2 : ℝ) ^ (j + 1) := by
    have hth := Chebyshev.theta_le_log4_mul_x (x := (((2 ^ (j + 1) : ℕ)) : ℝ)) (by positivity)
    rw [Chebyshev.theta, Nat.floor_natCast] at hth
    have hsub : (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime
        ⊆ (Finset.Ioc 0 (2 ^ (j + 1))).filter (fun p => p.Prime) := by
      intro ℓ hℓ
      obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
      obtain ⟨b1, b2⟩ := Finset.mem_Ico.mp a1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨a2.pos, b2.le⟩, a2⟩
    have hsum : ∑ ℓ ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (ℓ : ℝ)
        ≤ ∑ p ∈ (Finset.Ioc (0 : ℕ) (2 ^ (j + 1))).filter (fun p : ℕ => p.Prime),
          Real.log ((p : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    have hlow : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ)
        * (j * Real.log 2)
        ≤ ∑ ℓ ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (ℓ : ℝ) := by
      rw [← nsmul_eq_mul]
      refine Finset.card_nsmul_le_sum _ _ _ fun ℓ hℓ => ?_
      have hle : 2 ^ j ≤ ℓ := (Finset.mem_Ico.mp (Finset.mem_filter.mp hℓ).1).1
      have hleR : (2 : ℝ) ^ j ≤ ℓ := by exact_mod_cast hle
      have e : (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := by rw [Real.log_pow]
      rw [e]
      exact Real.log_le_log h2j hleR
    push_cast at hth
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  -- card ≤ 4 * 2 ^ j / j
  have h3 : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * j
      ≤ 4 * (2 : ℝ) ^ j := by
    have e2 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [hlog4, e2] at h2
    have : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * j * Real.log 2
        ≤ 4 * (2 : ℝ) ^ j * Real.log 2 := by linarith
    exact le_of_mul_le_mul_right this hlog2
  refine h1.trans ?_
  rw [le_div_iff₀ hjR]
  calc (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * (1 / 2 ^ j) * j
      = (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * j * (1 / 2 ^ j) := by
        ring
    _ ≤ 4 * (2 : ℝ) ^ j * (1 / 2 ^ j) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 4 := by field_simp

lemma harm_sum (j0 : ℕ) (hj0 : 1 ≤ j0) (d : ℕ) :
    ∑ j ∈ Finset.Icc j0 (j0 + d), (1 : ℝ) / j
      ≤ 1 / j0 + Real.log ((j0 + d : ℕ) : ℝ) - Real.log (j0 : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show j0 + (d + 1) = (j0 + d) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
    have hpos : (0 : ℝ) < ((j0 + d : ℕ) : ℝ) := by
      have : 0 < j0 + d := by omega
      exact_mod_cast this
    have hpos' : (0 : ℝ) < ((j0 + d + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((j0 + d + 1 : ℕ) : ℝ)
        ≤ Real.log ((j0 + d + 1 : ℕ) : ℝ) - Real.log ((j0 + d : ℕ) : ℝ) := by
      rw [← Real.log_div hpos'.ne' hpos.ne']
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hpos' hpos)
      have e : 1 - (((j0 + d + 1 : ℕ) : ℝ) / ((j0 + d : ℕ) : ℝ))⁻¹
          = 1 / ((j0 + d + 1 : ℕ) : ℝ) := by
        rw [inv_div]
        field_simp
        push_cast
        ring
      linarith
    linarith

/-- A Mertens-type upper bound: primes in `[2 ^ j0, 2 ^ (j1 + 1))`. -/
lemma prime_recip_sum (T : Finset ℕ) (j0 j1 : ℕ) (hj0 : 1 ≤ j0) (hj : j0 ≤ j1)
    (hT : ∀ ℓ ∈ T, ℓ.Prime ∧ 2 ^ j0 ≤ ℓ ∧ ℓ < 2 ^ (j1 + 1)) :
    ∑ ℓ ∈ T, (1 : ℝ) / ℓ ≤ 4 * (1 + Real.log (j1 : ℝ) - Real.log (j0 : ℝ)) := by
  classical
  have hmaps : ∀ ℓ ∈ T, Nat.log 2 ℓ ∈ Finset.Icc j0 j1 := by
    intro ℓ hℓ
    obtain ⟨h1, h2, h3⟩ := hT ℓ hℓ
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.le_log_of_pow_le (by norm_num) h2
    · have := Nat.log_lt_of_lt_pow h1.ne_zero h3
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.Icc j0 j1, ∑ ℓ ∈ T.filter (fun ℓ => Nat.log 2 ℓ = j), (1 : ℝ) / ℓ
      ≤ 4 * (1 / (j : ℝ)) := by
    intro j hjm
    have hj1 : 1 ≤ j := le_trans hj0 (Finset.mem_Icc.mp hjm).1
    have hsub : T.filter (fun ℓ => Nat.log 2 ℓ = j)
        ⊆ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime := by
      intro ℓ hℓ
      obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
      obtain ⟨b1, _, _⟩ := hT ℓ a1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, b1⟩
      · rw [← a2]
        exact Nat.pow_log_le_self 2 b1.ne_zero
      · rw [← a2]
        exact Nat.lt_pow_succ_log_self (by norm_num) ℓ
    calc ∑ ℓ ∈ T.filter (fun ℓ => Nat.log 2 ℓ = j), (1 : ℝ) / ℓ
        ≤ ∑ ℓ ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / ℓ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 4 / j := block_sum j hj1
      _ = 4 * (1 / (j : ℝ)) := by ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h := harm_sum j0 hj0 d
  have hj0R : (1 : ℝ) ≤ j0 := by exact_mod_cast hj0
  have hinv : (1 : ℝ) / j0 ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hj0R
  linarith


/-- Consequences of the structural conditions on the cube: sizes of the near shifts, their
distinctness, the size of the modulus, and the primes that cannot divide it. -/
lemma adm_bounds (K H Q M W : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ) (hK : 0 < K)
    (hp : ∀ E ∈ (Finset.range K).powerset,
      (p E).Prime ∧ p E ≤ M ∧ |s E| ≤ 8 * (K : ℤ) ^ 2 * (p E : ℤ))
    (hWdef : W = ∏ y ∈ ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).offDiag,
      ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1 - ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)).natAbs)
    (hW0 : W ≠ 0)
    (hQ : Q = (∏ E ∈ (Finset.range K).powerset, p E)
      * ∏ ℓ ∈ W.primeFactors \ (Finset.range K).powerset.image p, ℓ ^ W.factorization ℓ) :
    (∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      |(p y.1 : ℤ) * (y.2 : ℤ) - s y.1| ≤ (((K + H + 8 * K ^ 2) * M : ℕ) : ℤ)) ∧
    (∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ∀ z ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1), y ≠ z →
      (p y.1 : ℤ) * (y.2 : ℤ) - s y.1 ≠ (p z.1 : ℤ) * (z.2 : ℤ) - s z.1) ∧
    0 < Q ∧
    Q ≤ M ^ (2 ^ K) * (2 * ((K + H + 8 * K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) ∧
    ∀ ℓ : ℕ, ℓ.Prime → M < ℓ → 2 * ((K + H + 8 * K ^ 2) * M) < ℓ →
      Nat.Coprime Q ℓ ∧
      ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
        ∀ z ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1), y ≠ z →
        ¬ (ℓ : ℤ) ∣ ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1) - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1) := by
  classical
  have hrabs : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      |(p y.1 : ℤ) * (y.2 : ℤ) - s y.1| ≤ (((K + H + 8 * K ^ 2) * M : ℕ) : ℤ) := by
    intro y hy
    obtain ⟨hyE, hyh⟩ := Finset.mem_product.mp hy
    obtain ⟨_, hpM, hsE⟩ := hp y.1 hyE
    have hh : (y.2 : ℤ) ≤ K + H := by
      have := (Finset.mem_Ico.mp hyh).2
      exact_mod_cast (by omega : y.2 ≤ K + H)
    have hpM' : (p y.1 : ℤ) ≤ M := by exact_mod_cast hpM
    have e1 : |(p y.1 : ℤ) * (y.2 : ℤ)| ≤ (M : ℤ) * (K + H) := by
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul hpM' hh (by positivity) (by positivity)
    have e2 : |s y.1| ≤ 8 * (K : ℤ) ^ 2 * M :=
      hsE.trans (mul_le_mul_of_nonneg_left hpM' (by positivity))
    calc |(p y.1 : ℤ) * (y.2 : ℤ) - s y.1| ≤ |(p y.1 : ℤ) * (y.2 : ℤ)| + |s y.1| := abs_sub _ _
      _ ≤ (M : ℤ) * (K + H) + 8 * (K : ℤ) ^ 2 * M := add_le_add e1 e2
      _ = (((K + H + 8 * K ^ 2) * M : ℕ) : ℤ) := by
          push_cast
          ring
  have hfac : ∀ y ∈ ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).offDiag,
      ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1
        - ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)).natAbs ≠ 0 := by
    rw [hWdef] at hW0
    exact Finset.prod_ne_zero_iff.mp hW0
  have hdist : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ∀ z ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1), y ≠ z →
      (p y.1 : ℤ) * (y.2 : ℤ) - s y.1 ≠ (p z.1 : ℤ) * (z.2 : ℤ) - s z.1 := by
    intro y hy z hz hne heq
    have := hfac (y, z) (Finset.mem_offDiag.mpr ⟨hy, hz, hne⟩)
    rw [Int.natAbs_ne_zero] at this
    exact this (sub_eq_zero.mpr heq)
  have hnat : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1).natAbs ≤ (K + H + 8 * K ^ 2) * M := by
    intro y hy
    have : ((((p y.1 : ℤ) * (y.2 : ℤ) - s y.1).natAbs : ℕ) : ℤ)
        ≤ (((K + H + 8 * K ^ 2) * M : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hrabs y hy
    exact_mod_cast this
  have hdiff : ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ∀ z ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1 - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)).natAbs
        ≤ 2 * ((K + H + 8 * K ^ 2) * M) := by
    intro y hy z hz
    have := Int.natAbs_sub_le ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1) ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)
    have := hnat y hy
    have := hnat z hz
    omega
  have hM1 : 1 ≤ M := by
    obtain ⟨e1, e2, _⟩ := hp ∅ (Finset.empty_mem_powerset _)
    have := e1.pos
    omega
  have hDpos : 1 ≤ 2 * ((K + H + 8 * K ^ 2) * M) := by
    have : 1 ≤ (K + H + 8 * K ^ 2) * M := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hWle : W ≤ (2 * ((K + H + 8 * K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) := by
    rw [hWdef]
    refine (Finset.prod_le_pow_card _ _ (2 * ((K + H + 8 * K ^ 2) * M)) ?_).trans ?_
    · intro y hy
      obtain ⟨hy1, hy2, _⟩ := Finset.mem_offDiag.mp hy
      exact hdiff y.1 hy1 y.2 hy2
    · refine Nat.pow_le_pow_right hDpos ?_
      rw [Finset.offDiag_card, Finset.card_product, Finset.card_powerset, Finset.card_range,
        Nat.card_Ico]
      have : K + H + 1 - (K + 1) = H := by omega
      rw [this]
      exact Nat.sub_le _ _
  have hWfdvd : (∏ ℓ ∈ W.primeFactors \ (Finset.range K).powerset.image p,
      ℓ ^ W.factorization ℓ) ∣ W := by
    have hWeq : W = ∏ ℓ ∈ W.primeFactors, ℓ ^ W.factorization ℓ :=
      (Nat.prod_factorization_pow_eq_self hW0).symm.trans
        (Nat.prod_factorization_eq_prod_primeFactors _)
    have h := Finset.prod_dvd_prod_of_subset
      (W.primeFactors \ (Finset.range K).powerset.image p)
      W.primeFactors (fun ℓ => ℓ ^ W.factorization ℓ) Finset.sdiff_subset
    rw [← hWeq] at h
    exact h
  have hWfle := Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hWfdvd
  have hprodle : ∏ E ∈ (Finset.range K).powerset, p E ≤ M ^ (2 ^ K) := by
    have := Finset.prod_le_pow_card (Finset.range K).powerset p M (fun E hE => (hp E hE).2.1)
    rwa [Finset.card_powerset, Finset.card_range] at this
  refine ⟨hrabs, hdist, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Nat.mul_pos (Finset.prod_pos fun E hE => (hp E hE).1.pos)
      (Finset.prod_pos fun ℓ hℓ =>
        pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_sdiff.mp hℓ).1) _)
  · rw [hQ]
    exact Nat.mul_le_mul hprodle (hWfle.trans hWle)
  · intro ℓ hℓ hMℓ hDℓ
    constructor
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hℓ]
      intro hdvd
      rw [hQ] at hdvd
      rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
      · obtain ⟨E, hE, hE'⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp h
        have := (Nat.prime_dvd_prime_iff_eq hℓ (hp E hE).1).mp hE'
        have := (hp E hE).2.1
        omega
      · have hW' := h.trans hWfdvd
        rw [hWdef] at hW'
        obtain ⟨y, hy, hdy⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).mp hW'
        obtain ⟨hy1, hy2, _⟩ := Finset.mem_offDiag.mp hy
        have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hfac y hy)) hdy
        have h2 := hdiff y.1 hy1 y.2 hy2
        omega
    · intro y hy z hz hne hdvd
      have h0 : ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1 - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)).natAbs
          ≠ 0 := hfac (y, z) (Finset.mem_offDiag.mpr ⟨hy, hz, hne⟩)
      have h1 : ℓ ∣ ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1
          - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)).natAbs := Int.natCast_dvd.mp hdvd
      have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h1
      have h3 := hdiff y hy z hz
      omega


lemma exp_half_big (l : ℝ) (hl : 6 * 10 ^ 12 ≤ l) : 3 * l ^ 11 ≤ Real.exp (l / 2) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have h := Real.pow_div_factorial_le_exp (x := l / 2) (by positivity) 12
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h2 : 3 * l ^ 11 ≤ (l / 2) ^ 12 / 479001600 := by
    rw [le_div_iff₀ (by norm_num)]
    have e : (l / 2) ^ 12 = l ^ 11 * l / 4096 := by ring
    rw [e]
    have h11 : 0 < l ^ 11 := by positivity
    have hl' : 3 * 479001600 * 4096 ≤ l := by linarith
    have := mul_le_mul_of_nonneg_left hl' h11.le
    linarith
  linarith

/-- The size comparisons at scale `l = log log log x`, for arbitrary admissible data. -/
lemma numeric3 (l : ℝ) (hl : 6 * 10 ^ 12 ≤ l) (K H M : ℕ)
    (hK : K = ⌊2 * Real.log l / Real.log 2⌋₊) (hH : H = ⌊l ^ 2⌋₊)
    (hM : M = ⌊Real.exp (l ^ 3)⌋₊) :
    0 < K ∧ (2 : ℝ) ^ K ≤ l ^ 2 ∧ l ^ 2 < 2 ^ (K + 1) ∧
    (M : ℝ) ≤ Real.exp (l ^ 3) ∧
    ((2 * ((K + H + 8 * K ^ 2) * M) : ℕ) : ℝ) ≤ Real.exp (Real.exp (l / 2)) ∧
    ((M ^ (2 ^ K) * (2 * ((K + H + 8 * K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
      ≤ Real.exp (Real.exp (l / 2)) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hl1 : 1 ≤ l := le_trans (by norm_num) hl
  have hE3 := exp_half_big l hl
  have hlogl : 0 < Real.log l := Real.log_pos (lt_of_lt_of_le (by norm_num) hl)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKle : (K : ℝ) ≤ 2 * Real.log l / Real.log 2 := by
    rw [hK]
    exact Nat.floor_le (by positivity)
  have hKlt : 2 * Real.log l / Real.log 2 < K + 1 := by
    rw [hK]
    exact Nat.lt_floor_add_one _
  have hF1 : (2 : ℝ) ^ K ≤ l ^ 2 := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have := (le_div_iff₀ hlog2).mp hKle
    push_cast
    linarith
  have hF2 : l ^ 2 < (2 : ℝ) ^ (K + 1) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have := (div_lt_iff₀ hlog2).mp hKlt
    push_cast
    linarith
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hF2
      norm_num at hF2
      nlinarith
    · exact h
  have hMP : (M : ℝ) ≤ Real.exp (l ^ 3) := by
    rw [hM]
    exact Nat.floor_le (Real.exp_pos _).le
  have hHle : (H : ℝ) ≤ l ^ 2 := by
    rw [hH]
    exact Nat.floor_le (by positivity)
  have hKl2 : (K : ℝ) ≤ l ^ 2 := by
    have h1 : (K : ℝ) < (2 : ℝ) ^ K := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  have hl4 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hl1 (by norm_num)
  have hK2 : (K : ℝ) ^ 2 ≤ l ^ 4 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg K) hKl2 2
    calc (K : ℝ) ^ 2 ≤ (l ^ 2) ^ 2 := this
      _ = l ^ 4 := by ring
  have hP0 : 0 < Real.exp (l ^ 3) := Real.exp_pos _
  have hl3 : l ≤ l ^ 3 := by
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ 3 := pow_le_pow_right₀ hl1 (by norm_num)
  have hexp1 : Real.exp (l / 2) ≤ Real.exp (l ^ 3) := Real.exp_le_exp.mpr (by linarith)
  have hpow11 : ∀ j : ℕ, j ≤ 11 → l ^ j ≤ l ^ 11 := fun j hj => pow_le_pow_right₀ hl1 hj
  have hl11 : 0 < l ^ 11 := by positivity
  have hpow10 : ∀ j : ℕ, j ≤ 10 → 8 * l ^ j ≤ l ^ 11 := by
    intro j hj
    have h1 : l ^ (j + 1) ≤ l ^ 11 := pow_le_pow_right₀ hl1 (by omega)
    have h2 : 0 < l ^ j := by positivity
    have h3 : (8 : ℝ) ≤ l := le_trans (by norm_num) hl
    have h4 : 8 * l ^ j ≤ l ^ j * l := by nlinarith
    rw [pow_succ] at h1
    linarith
  have hRM : (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) ≤ 10 * l ^ 4 * Real.exp (l ^ 3) := by
    push_cast
    have h1 : (K : ℝ) + H + 8 * (K : ℝ) ^ 2 ≤ 10 * l ^ 4 := by linarith
    exact mul_le_mul h1 hMP (Nat.cast_nonneg _) (by positivity)
  have h20 : 20 * l ^ 4 ≤ Real.exp (l / 2) := by
    have := hpow10 4 (by norm_num)
    have h0 : 0 < l ^ 4 := by positivity
    linarith
  have h2RM : (2 : ℝ) * (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) ≤ Real.exp (2 * l ^ 3) := by
    have e : Real.exp (2 * l ^ 3) = Real.exp (l ^ 3) * Real.exp (l ^ 3) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    calc (2 : ℝ) * (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) ≤ 20 * l ^ 4 * Real.exp (l ^ 3) := by
          linarith
      _ ≤ Real.exp (l ^ 3) * Real.exp (l ^ 3) :=
        mul_le_mul_of_nonneg_right (h20.trans hexp1) hP0.le
  have h2l3 : 2 * l ^ 3 ≤ Real.exp (l / 2) := by
    have := hpow10 3 (by norm_num)
    have h0 : 0 < l ^ 3 := by positivity
    linarith
  have h3l11 : Real.exp (3 * l ^ 11) ≤ Real.exp (Real.exp (l / 2)) := Real.exp_le_exp.mpr hE3
  refine ⟨hK0, hF1, hF2, hMP, ?_, ?_⟩
  · rw [Nat.cast_mul, Nat.cast_ofNat]
    exact h2RM.trans (Real.exp_le_exp.mpr h2l3)
  · have hn : (((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) ≤ l ^ 8 := by
      push_cast
      have h1 : (2 : ℝ) ^ K * H ≤ l ^ 2 * l ^ 2 :=
        mul_le_mul hF1 hHle (Nat.cast_nonneg _) (by positivity)
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ K * H := by positivity
      calc (2 : ℝ) ^ K * H * ((2 : ℝ) ^ K * H) ≤ (l ^ 2 * l ^ 2) * (l ^ 2 * l ^ 2) :=
            mul_le_mul h1 h1 h0 (by positivity)
        _ = l ^ 8 := by ring
    have hA : ((M ^ (2 ^ K) : ℕ) : ℝ) ≤ Real.exp (l ^ 5) := by
      push_cast
      calc (M : ℝ) ^ (2 ^ K) ≤ (Real.exp (l ^ 3)) ^ (2 ^ K) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
        _ = Real.exp (((2 ^ K : ℕ) : ℝ) * l ^ 3) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (l ^ 5) := by
            refine Real.exp_le_exp.mpr ?_
            push_cast
            calc (2 : ℝ) ^ K * l ^ 3 ≤ l ^ 2 * l ^ 3 :=
                  mul_le_mul_of_nonneg_right hF1 (by positivity)
              _ = l ^ 5 := by ring
    have hB : (((2 * ((K + H + 8 * K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
        ≤ Real.exp (2 * l ^ 11) := by
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
      calc ((2 : ℝ) * (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ)) ^ ((2 ^ K * H) * (2 ^ K * H))
          ≤ (Real.exp (2 * l ^ 3)) ^ ((2 ^ K * H) * (2 ^ K * H)) :=
            pow_le_pow_left₀ (by positivity) h2RM _
        _ = Real.exp ((((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) * (2 * l ^ 3)) :=
            (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (2 * l ^ 11) := by
            refine Real.exp_le_exp.mpr ?_
            calc (((2 ^ K * H) * (2 ^ K * H) : ℕ) : ℝ) * (2 * l ^ 3) ≤ l ^ 8 * (2 * l ^ 3) :=
                  mul_le_mul_of_nonneg_right hn (by positivity)
              _ = 2 * l ^ 11 := by ring
    rw [Nat.cast_mul]
    calc ((M ^ (2 ^ K) : ℕ) : ℝ)
          * (((2 * ((K + H + 8 * K ^ 2) * M)) ^ ((2 ^ K * H) * (2 ^ K * H)) : ℕ) : ℝ)
        ≤ Real.exp (l ^ 5) * Real.exp (2 * l ^ 11) :=
          mul_le_mul hA hB (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (l ^ 5 + 2 * l ^ 11) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (3 * l ^ 11) := by
          refine Real.exp_le_exp.mpr ?_
          have := hpow11 5 (by norm_num)
          linarith
      _ ≤ Real.exp (Real.exp (l / 2)) := h3l11

/-- The weights on the near shifts: zero sum, absolute sum at most one, small square sum. -/
lemma weights (K H : ℕ) (hK : 0 < K) :
    ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ((-1 : ℝ) ^ a.1.card / 2 ^ a.2) = 0 ∧
    ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      |((-1 : ℝ) ^ a.1.card / 2 ^ a.2)| ≤ 1 ∧
    ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ((-1 : ℝ) ^ a.1.card / 2 ^ a.2) ^ 2 ≤ 1 / 2 ^ K := by
  have hsign := OMA.R_Erdos69_erdos_69_R1_H1_R1.sign_sum K hK
  have hcardC : (((Finset.range K).powerset.card : ℕ) : ℝ) = 2 ^ K := by
    rw [Finset.card_powerset, Finset.card_range]
    push_cast
    rfl
  have habs : ∀ a : Finset ℕ × ℕ, |((-1 : ℝ) ^ a.1.card / 2 ^ a.2)| = 1 / 2 ^ a.2 := by
    intro a
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1),
        ((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2)
        = (-1 : ℝ) ^ E.card * ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / (2 : ℝ) ^ h := by
      intro E _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hsign, zero_mul]
  · rw [Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1),
        |((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2)|
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / (2 : ℝ) ^ h := by
      intro E _
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [habs]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardC, Finset.mul_sum]
    have e : ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K * (1 / 2 ^ h)
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / 2 ^ h :=
      Finset.sum_congr rfl fun h _ => by ring
    rw [e, OMA.R_Erdos69_erdos_69_R1_H1_R1.geom_one]
    have : (0 : ℝ) < 1 / 2 ^ H := by positivity
    linarith
  · rw [Finset.sum_product]
    have : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1),
        ((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2) ^ 2
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), 1 / ((2 : ℝ) ^ h) ^ 2 := by
      intro E _
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← sq_abs, habs, div_pow, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcardC, Finset.mul_sum]
    have e : ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K * (1 / (2 ^ h) ^ 2)
        = ∑ h ∈ Finset.Ico (K + 1) (K + H + 1), (2 : ℝ) ^ K / (2 ^ h) ^ 2 :=
      Finset.sum_congr rfl fun h _ => by ring
    rw [e, OMA.R_Erdos69_erdos_69_R1_H1_R1.geom_two]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1' : (0 : ℝ) < 1 / (2 ^ H) ^ 2 := by positivity
    have h2' : (0 : ℝ) < 2 ^ K := by positivity
    nlinarith

/-- The number of prime factors in a window as a sum of indicators over a fixed set of primes. -/
lemma card_window (z : ℤ) (hz : z ≠ 0) (R y : ℝ) :
    ((z.natAbs.primeFactors.filter (fun ℓ : ℕ => R < ℓ ∧ (ℓ : ℝ) ≤ y)).card : ℝ)
      = ∑ ℓ ∈ (Finset.range (⌊y⌋₊ + 1)).filter
          (fun ℓ : ℕ => ℓ.Prime ∧ R < ℓ ∧ (ℓ : ℝ) ≤ y),
        (if (ℓ : ℤ) ∣ z then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_boole]
  congr 2
  ext ℓ
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h3, h4⟩
    exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor h4), h1, h3, h4⟩, Int.natCast_dvd.mpr h2⟩
  · rintro ⟨⟨_, h1, h3, h4⟩, h2⟩
    exact ⟨⟨h1, Int.natCast_dvd.mp h2, Int.natAbs_ne_zero.mpr hz⟩, h3, h4⟩



/-- Recurrence for sums of products over subsets of a given size. -/
lemma pc_insert {R : Type*} [CommSemiring R] (f : ℕ → R) (s : Finset ℕ) (a : ℕ) (ha : a ∉ s)
    (j : ℕ) :
    ∑ D ∈ (insert a s).powersetCard (j + 1), ∏ i ∈ D, f i
      = ∑ D ∈ s.powersetCard (j + 1), ∏ i ∈ D, f i
        + f a * ∑ D ∈ s.powersetCard j, ∏ i ∈ D, f i := by
  classical
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union, Finset.sum_image, Finset.mul_sum]
  · congr 1
    refine Finset.sum_congr rfl fun D hD => ?_
    have haD : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
    rw [Finset.prod_insert haD]
  · intro D hD D' hD' h
    have haD : a ∉ D := fun h => ha ((Finset.mem_powersetCard.mp hD).1 h)
    have haD' : a ∉ D' := fun h => ha ((Finset.mem_powersetCard.mp hD').1 h)
    have := congrArg (fun t => t.erase a) h
    simpa [Finset.erase_insert haD, Finset.erase_insert haD'] using this
  · rw [Finset.disjoint_left]
    intro D hD hD'
    obtain ⟨D0, _, rfl⟩ := Finset.mem_image.mp hD'
    exact ha ((Finset.mem_powersetCard.mp hD).1 (Finset.mem_insert_self a D0))

lemma pc_zero {R : Type*} [CommSemiring R] (f : ℕ → R) (s : Finset ℕ) :
    ∑ D ∈ s.powersetCard 0, ∏ i ∈ D, f i = 1 := by
  simp

/-- Truncating the expansion of a product of unimodular-bounded factors `1 + g i` at subsets of
size `M`: the error is at most the sum over subsets of size `M + 1` of the products of norms. -/
lemma prod_trunc (g : ℕ → ℂ) (s : Finset ℕ) (hg : ∀ i ∈ s, ‖1 + g i‖ ≤ 1) :
    ∀ M : ℕ, ‖∏ i ∈ s, (1 + g i)
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i‖
      ≤ ∑ D ∈ s.powersetCard (M + 1), ∏ i ∈ D, ‖g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro M
    have h1 : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ (∅ : Finset ℕ).powersetCard j, ∏ i ∈ D, g i
        = 1 := by
      rw [Finset.sum_range_succ', Finset.sum_eq_zero]
      · simp
      · intro j _
        rw [Finset.powersetCard_eq_empty.mpr (by simp)]
        simp
    rw [h1, Finset.prod_empty, sub_self, norm_zero]
    exact Finset.sum_nonneg fun D _ => Finset.prod_nonneg fun i _ => norm_nonneg _
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hprod1 : ‖∏ i ∈ s, (1 + g i)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    intro M
    rw [Finset.prod_insert ha, pc_insert (fun i => ‖g i‖) s a ha M]
    -- the truncated sum for the larger set
    have hT : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ (insert a s).powersetCard j, ∏ i ∈ D, g i
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i
          + g a * ∑ j ∈ Finset.range M, ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ' _ M, pc_zero, pc_zero, Finset.mul_sum,
        Finset.sum_congr rfl (fun j _ => pc_insert g s a ha j), Finset.sum_add_distrib]
      ring
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have hT0 : ∑ j ∈ Finset.range (0 + 1), ∑ D ∈ (insert a s).powersetCard j, ∏ i ∈ D, g i
          = 1 := by simp
      have hT0' : ∑ j ∈ Finset.range (0 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i = 1 := by
        simp
      rw [hT0]
      have e : (1 + g a) * ∏ i ∈ s, (1 + g i) - 1
          = (∏ i ∈ s, (1 + g i) - 1) + g a * ∏ i ∈ s, (1 + g i) := by ring
      rw [e]
      have h0 := ih' 0
      rw [hT0'] at h0
      have h1 : ‖g a * ∏ i ∈ s, (1 + g i)‖ ≤ ‖g a‖ * 1 := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hprod1 (norm_nonneg _)
      rw [pc_zero]
      calc ‖(∏ i ∈ s, (1 + g i) - 1) + g a * ∏ i ∈ s, (1 + g i)‖
          ≤ ‖∏ i ∈ s, (1 + g i) - 1‖ + ‖g a * ∏ i ∈ s, (1 + g i)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add h0 h1
    · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [hT]
      have e : (1 + g a) * ∏ i ∈ s, (1 + g i)
          - (∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i
            + g a * ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
          = (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
            + g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i) := by ring
      rw [e]
      have h1 := ih' (M' + 1)
      have h2 := ih' M'
      calc ‖(∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)
            + g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)‖
          ≤ ‖∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1 + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i‖
            + ‖g a * (∏ i ∈ s, (1 + g i)
              - ∑ j ∈ Finset.range (M' + 1), ∑ D ∈ s.powersetCard j, ∏ i ∈ D, g i)‖ :=
            norm_add_le _ _
        _ ≤ _ := by
            rw [norm_mul]
            exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

lemma pow_succ_add_le (p x : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (n : ℕ) :
    p ^ (n + 1) + (n + 1) * (x * p ^ n) ≤ (p + x) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (p + x) ^ (n + 1 + 1) = (p + x) ^ (n + 1) * (p + x) := pow_succ _ _
    have h2 : (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x)
        ≤ (p + x) ^ (n + 1) * (p + x) := mul_le_mul_of_nonneg_right ih (by linarith)
    have h3 : p ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * (x * p ^ (n + 1))
        ≤ (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x) := by
      have e : (p ^ (n + 1) + (n + 1) * (x * p ^ n)) * (p + x)
          - (p ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * (x * p ^ (n + 1)))
          = (n + 1) * (x ^ 2 * p ^ n) := by
        push_cast
        ring
      have h0 : (0 : ℝ) ≤ (n + 1) * (x ^ 2 * p ^ n) := by positivity
      linarith
    rw [h1]
    exact h3.trans h2

/-- Elementary symmetric sums are at most the power of the sum divided by the factorial. -/
lemma esymm_le (x : ℕ → ℝ) (s : Finset ℕ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ j : ℕ, (j.factorial : ℝ) * ∑ D ∈ s.powersetCard j, ∏ i ∈ D, x i ≤ (∑ i ∈ s, x i) ^ j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [Finset.powersetCard_eq_empty.mpr (by simpa using hj)]
      simp
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hp : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [pc_insert x s a ha j', Finset.sum_insert ha]
      have h1 := ih' (j' + 1)
      have h2 := ih' j'
      have hfac : ((j' + 1).factorial : ℝ) = (j' + 1) * (j'.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have h3 : ((j' + 1).factorial : ℝ) * (x a * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)
          ≤ (j' + 1) * (x a * (∑ i ∈ s, x i) ^ j') := by
        rw [hfac]
        have : (j' + 1 : ℝ) * (j'.factorial : ℝ) * (x a * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)
            = (j' + 1) * (x a * ((j'.factorial : ℝ) * ∑ D ∈ s.powersetCard j', ∏ i ∈ D, x i)) := by
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hxa) (by positivity)
      have h4 := pow_succ_add_le (∑ i ∈ s, x i) (x a) hp hxa j'
      rw [mul_add, add_comm (x a) (∑ i ∈ s, x i)]
      linarith



/-- Integers of the progression in a further residue class modulo `m` coprime to `Q`. -/
lemma count_mod (L U Q b m c : ℕ) (hQ : 0 < Q) (hm : 0 < m) (hco : Nat.Coprime Q m)
    (hLU : L ≤ U + 1) :
    |((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
        (fun n : ℕ => n % m = c % m)).card : ℝ)
      - (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m| ≤ 4 := by
  obtain ⟨c', hc'⟩ := crt2 Q m b c hco
  have hfil : ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
      (fun n : ℕ => n % m = c % m)
      = (Finset.Icc L U).filter (fun n => n % (Q * m) = c' % (Q * m)) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun n _ => hc' n
  rw [hfil]
  have h1 := ap_count L U (Q * m) c' (Nat.mul_pos hQ hm) hLU
  have h2 := ap_count L U Q b hQ hLU
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e : ((U : ℝ) + 1 - L) / ((Q * m : ℕ) : ℝ) = ((U : ℝ) + 1 - L) / Q / m := by
    push_cast
    rw [div_div]
  rw [e] at h1
  have key : |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m
      - ((U : ℝ) + 1 - L) / Q / m| ≤ 2 := by
    rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < m)]
    calc |(((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
          - ((U : ℝ) + 1 - L) / Q| / m ≤ 2 / m :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ ≤ 2 / 1 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmR
      _ = 2 := by norm_num
  rw [abs_le] at h1 key ⊢
  constructor <;> linarith

/-- Joint moments of the local factors over the progression: exact independence modulo
distinct primes, up to a bounded error. -/
lemma moment_ind {𝕜 : Type*} [RCLike 𝕜] (L U Q b : ℕ) (hQ : 0 < Q) (hLU : L ≤ U + 1)
    (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (γ : Finset ℕ × ℕ → 𝕜) (D : Finset ℕ) :
    ∀ (m c : ℕ), 0 < m → Nat.Coprime Q m →
      (∀ ℓ ∈ D, ℓ.Prime ∧ Nat.Coprime Q ℓ ∧ Nat.Coprime m ℓ) →
      ‖∑ n ∈ ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
            (fun n : ℕ => n % m = c % m),
          ∏ ℓ ∈ D, ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : 𝕜) else 0)
        - ((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m : ℝ)
          * ∏ ℓ ∈ D, ((∑ a ∈ S, γ a) / (ℓ : 𝕜))‖
      ≤ 4 * (∑ a ∈ S, ‖γ a‖) ^ D.card := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro m c hm hco _
    simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_empty,
      pow_zero]
    have h := count_mod L U Q b m c hQ hm hco hLU
    have e : ((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
        (fun n : ℕ => n % m = c % m)).card : 𝕜)
        - (((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m : ℝ) : 𝕜)
        = (((((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
          (fun n : ℕ => n % m = c % m)).card : ℝ)
          - (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m) : ℝ) : 𝕜) := by
      push_cast
      ring
    rw [e, RCLike.norm_ofReal]
    exact h
  | insert a D ha ih =>
    intro m c hm hco hD
    obtain ⟨hap, haQ, ham⟩ := hD a (Finset.mem_insert_self a D)
    have hD' : ∀ ℓ ∈ D, ℓ.Prime ∧ Nat.Coprime Q ℓ ∧ Nat.Coprime m ℓ :=
      fun ℓ hℓ => hD ℓ (Finset.mem_insert_of_mem hℓ)
    have hma : 0 < m * a := Nat.mul_pos hm hap.pos
    have hcoma : Nat.Coprime Q (m * a) := Nat.Coprime.mul_right hco haQ
    have hDma : ∀ ℓ ∈ D, ℓ.Prime ∧ Nat.Coprime Q ℓ ∧ Nat.Coprime (m * a) ℓ := by
      intro ℓ hℓ
      obtain ⟨h1, h2, h3⟩ := hD' ℓ hℓ
      refine ⟨h1, h2, Nat.Coprime.mul_left h3 ?_⟩
      refine (Nat.coprime_primes hap h1).mpr ?_
      intro h
      exact ha (h ▸ hℓ)
    -- split according to the active shift at the prime a
    have hsplit : ∑ n ∈ ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
          (fun n : ℕ => n % m = c % m),
        ∏ ℓ ∈ insert a D, ∑ α ∈ S, γ α * (if (ℓ : ℤ) ∣ (n : ℤ) + r α then (1 : 𝕜) else 0)
        = ∑ α ∈ S, γ α * ∑ n ∈ (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
            (fun n : ℕ => n % m = c % m)).filter (fun n : ℕ => (a : ℤ) ∣ (n : ℤ) + r α),
          ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ : ℤ) ∣ (n : ℤ) + r β then (1 : 𝕜) else 0) := by
      have h1 : ∀ n : ℕ,
          ∏ ℓ ∈ insert a D, ∑ α ∈ S, γ α * (if (ℓ : ℤ) ∣ (n : ℤ) + r α then (1 : 𝕜) else 0)
          = ∑ α ∈ S, γ α * ((if (a : ℤ) ∣ (n : ℤ) + r α then (1 : 𝕜) else 0)
            * ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ : ℤ) ∣ (n : ℤ) + r β then (1 : 𝕜) else 0)) := by
        intro n
        rw [Finset.prod_insert ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        ring
      rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      conv_lhs => rw [← Finset.mul_sum]
      conv_rhs => rw [Finset.sum_filter]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> simp
    rw [hsplit]
    -- each inner sum is over a single class modulo m * a
    have hinner : ∀ α ∈ S, ∃ c' : ℕ,
        (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
          (fun n : ℕ => n % m = c % m)).filter (fun n : ℕ => (a : ℤ) ∣ (n : ℤ) + r α)
        = ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
          (fun n : ℕ => n % (m * a) = c' % (m * a)) := by
      intro α _
      obtain ⟨c', hc'⟩ := crt2 m a c ((-(r α)) % (a : ℤ)).toNat ham
      refine ⟨c', ?_⟩
      rw [Finset.filter_filter]
      refine Finset.filter_congr fun n _ => ?_
      rw [dvd_iff_mod a n (r α) hap.pos]
      exact hc' n
    have hbound : ∀ α ∈ S,
        ‖∑ n ∈ (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
            (fun n : ℕ => n % m = c % m)).filter (fun n : ℕ => (a : ℤ) ∣ (n : ℤ) + r α),
          ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ : ℤ) ∣ (n : ℤ) + r β then (1 : 𝕜) else 0)
          - ((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / (m * a : ℕ) : ℝ)
            * ∏ ℓ ∈ D, ((∑ β ∈ S, γ β) / (ℓ : 𝕜))‖
        ≤ 4 * (∑ β ∈ S, ‖γ β‖) ^ D.card := by
      intro α hα
      obtain ⟨c', hc'⟩ := hinner α hα
      rw [hc']
      exact ih (m * a) c' hma hcoma hDma
    have hmain : (((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) / m : ℝ) : 𝕜)
        * ∏ ℓ ∈ insert a D, ((∑ β ∈ S, γ β) / (ℓ : 𝕜))
        = ∑ α ∈ S, γ α * ((((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
            / (m * a : ℕ) : ℝ) : 𝕜) * ∏ ℓ ∈ D, ((∑ β ∈ S, γ β) / (ℓ : 𝕜))) := by
      rw [Finset.prod_insert ha, ← Finset.sum_mul]
      have ham0 : (a : 𝕜) ≠ 0 := by exact_mod_cast hap.ne_zero
      have hm0 : (m : 𝕜) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hmain, ← Finset.sum_sub_distrib]
    calc ‖∑ α ∈ S, (γ α * ∑ n ∈ (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
              (fun n : ℕ => n % m = c % m)).filter (fun n : ℕ => (a : ℤ) ∣ (n : ℤ) + r α),
            ∏ ℓ ∈ D, ∑ β ∈ S, γ β * (if (ℓ : ℤ) ∣ (n : ℤ) + r β then (1 : 𝕜) else 0)
          - γ α * ((((((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
            / (m * a : ℕ) : ℝ) : 𝕜) * ∏ ℓ ∈ D, ((∑ β ∈ S, γ β) / (ℓ : 𝕜))))‖
        ≤ ∑ α ∈ S, ‖γ α‖ * (4 * (∑ β ∈ S, ‖γ β‖) ^ D.card) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
          rw [← mul_sub, norm_mul]
          exact mul_le_mul_of_nonneg_left (hbound α hα) (norm_nonneg _)
      _ = 4 * (∑ a ∈ S, ‖γ a‖) ^ (insert a D).card := by
          rw [← Finset.sum_mul, Finset.card_insert_of_notMem ha, pow_succ]
          ring


/-- Joint moments over the whole progression. -/
lemma moment1 {𝕜 : Type*} [RCLike 𝕜] (L U Q b : ℕ) (hQ : 0 < Q) (hLU : L ≤ U + 1)
    (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (γ : Finset ℕ × ℕ → 𝕜) (D : Finset ℕ)
    (hD : ∀ ℓ ∈ D, ℓ.Prime ∧ Nat.Coprime Q ℓ) :
    ‖∑ n ∈ (Finset.Icc L U).filter (fun n => n % Q = b % Q),
        ∏ ℓ ∈ D, ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : 𝕜) else 0)
      - (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : 𝕜)
        * ∏ ℓ ∈ D, ((∑ a ∈ S, γ a) / (ℓ : 𝕜))‖
    ≤ 4 * (∑ a ∈ S, ‖γ a‖) ^ D.card := by
  have h := moment_ind (𝕜 := 𝕜) L U Q b hQ hLU S r γ D 1 0 Nat.one_pos (Nat.coprime_one_right Q)
    (fun ℓ hℓ => ⟨(hD ℓ hℓ).1, (hD ℓ hℓ).2, Nat.coprime_one_left ℓ⟩)
  have hfil : ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).filter
      (fun n : ℕ => n % 1 = 0 % 1) = (Finset.Icc L U).filter (fun n => n % Q = b % Q) :=
    Finset.filter_true_of_mem fun n _ => by simp [Nat.mod_one]
  rw [hfil] at h
  simpa using h

/-- The phase of a sum of weights over the shifts divisible by `ℓ`, when at most one shift is
divisible. -/
lemma local_factor (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (wt : Finset ℕ × ℕ → ℝ)
    (q : ℝ) (ℓ n : ℕ)
    (hsep : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ (ℓ : ℤ) ∣ r a - r c) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) : ℝ) : ℂ))
      = 1 + ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) := by
  classical
  by_cases h : ∃ a ∈ S, (ℓ : ℤ) ∣ (n : ℤ) + r a
  · obtain ⟨a0, ha0, hact⟩ := h
    have hother : ∀ c ∈ S, c ≠ a0 → ¬ (ℓ : ℤ) ∣ (n : ℤ) + r c := by
      intro c hc hne hc'
      apply hsep a0 ha0 c hc (Ne.symm hne)
      have := dvd_sub hact hc'
      simpa using this
    have e1 : ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) = wt a0 := by
      rw [Finset.sum_eq_single a0]
      · rw [if_pos hact, mul_one]
      · intro c hc hne
        rw [if_neg (hother c hc hne), mul_zero]
      · intro h
        exact absurd ha0 h
    have e2 : ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)
        = Complex.exp (2 * Real.pi * Complex.I * ((q * wt a0 : ℝ) : ℂ)) - 1 := by
      rw [Finset.sum_eq_single a0]
      · rw [if_pos hact, mul_one]
      · intro c hc hne
        rw [if_neg (hother c hc hne), mul_zero]
      · intro h
        exact absurd ha0 h
    rw [e1, e2]
    ring
  · push Not at h
    have e1 : ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [if_neg (h a ha), mul_zero]
    have e2 : ∑ a ∈ S, (Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) - 1)
          * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [if_neg (h a ha), mul_zero]
    rw [e1, e2]
    simp

/-- The Fourier coefficient of a product of local factors over a progression: comparison with
the independent model, truncating the expansion of the product at subsets of size `M`. -/
lemma fourier_bound (L U Q b : ℕ) (hQ : 0 < Q) (hLU : L ≤ U + 1)
    (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (γ : Finset ℕ × ℕ → ℂ) (P : Finset ℕ)
    (M : ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime ∧ Nat.Coprime Q ℓ)
    (hunit : ∀ n ∈ (Finset.Icc L U).filter (fun n => n % Q = b % Q), ∀ ℓ ∈ P,
      ‖1 + ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)‖ ≤ 1)
    (hmodel : ∀ ℓ ∈ P, ‖1 + (∑ a ∈ S, γ a) / (ℓ : ℂ)‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Icc L U).filter (fun n => n % Q = b % Q),
        ∏ ℓ ∈ P, (1 + ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0))‖
      ≤ (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
          * ‖∏ ℓ ∈ P, (1 + (∑ a ∈ S, γ a) / (ℓ : ℂ))‖
        + 2 * (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)
          * ((∑ a ∈ S, ‖γ a‖) ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ)
        + 4 * ∑ j ∈ Finset.range (M + 2), (P.card.choose j : ℝ) * (∑ a ∈ S, ‖γ a‖) ^ j := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Finset ℕ, N = (Finset.Icc L U).filter (fun n => n % Q = b % Q) :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ a ∈ S, ‖γ a‖ := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℂ, Γ = ∑ a ∈ S, γ a := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ → ℂ, ∀ ℓ n,
      g ℓ n = ∑ a ∈ S, γ a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  rw [← hN] at hunit ⊢
  rw [← hG, ← hΓ]
  rw [← hΓ] at hmodel
  simp only [← hg] at hunit ⊢
  have hG0 : 0 ≤ G := by rw [hG]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΓG : ‖Γ‖ ≤ G := by rw [hΓ, hG]; exact norm_sum_le _ _
  have hNn : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  -- moments
  have hmom : ∀ D ⊆ P, ‖∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
      ≤ 4 * G ^ D.card := by
    intro D hD
    have := moment1 (𝕜 := ℂ) L U Q b hQ hLU S r γ D (fun ℓ hℓ => hP ℓ (hD hℓ))
    rw [← hN, ← hG, ← hΓ] at this
    simp only [← hg] at this
    exact this
  -- the real majorant
  have hmaj : ∀ D ⊆ P, ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
      ≤ (N.card : ℝ) * (G ^ D.card * ∏ ℓ ∈ D, (1 : ℝ) / ℓ) + 4 * G ^ D.card := by
    intro D hD
    have h := moment1 (𝕜 := ℝ) L U Q b hQ hLU S r (fun a => ‖γ a‖) D (fun ℓ hℓ => hP ℓ (hD hℓ))
    rw [← hN] at h
    simp only [norm_norm] at h
    rw [← hG] at h
    have hle : ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
        ≤ ∑ n ∈ N, ∏ ℓ ∈ D, ∑ a ∈ S, ‖γ a‖ * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum fun n _ => Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
      intro ℓ _
      rw [hg]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      split_ifs <;> simp
    have hprod : ∏ ℓ ∈ D, (G / (ℓ : ℝ)) = G ^ D.card * ∏ ℓ ∈ D, (1 : ℝ) / ℓ := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      ring
    rw [hprod, Real.norm_eq_abs, abs_le] at h
    linarith [h.2]
  -- truncation for each n
  have htrunc : ∀ n ∈ N, ‖∏ ℓ ∈ P, (1 + g ℓ n)
      - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n‖
      ≤ ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖g ℓ n‖ := fun n hn =>
    prod_trunc (fun ℓ => g ℓ n) P (hunit n hn) M
  have htrunc' : ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
      - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
      ≤ ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖Γ / (ℓ : ℂ)‖ :=
    prod_trunc (fun ℓ => Γ / (ℓ : ℂ)) P hmodel M
  have hsub : ∀ j, ∀ D ∈ P.powersetCard j, D ⊆ P ∧ D.card = j :=
    fun j D hD => Finset.mem_powersetCard.mp hD
  -- bound on the model remainder
  have hmodrem : ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖Γ / (ℓ : ℂ)‖
      ≤ G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun D hD => ?_
    obtain ⟨_, hcard⟩ := hsub _ D hD
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun ℓ _ => ?_
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hΓG (by positivity)
  -- bound on the summed remainders
  have hrem : ∑ n ∈ N, ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, ‖g ℓ n‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ)
        + 4 * ((P.card.choose (M + 1) : ℝ) * G ^ (M + 1)) := by
    rw [Finset.sum_comm]
    calc ∑ D ∈ P.powersetCard (M + 1), ∑ n ∈ N, ∏ ℓ ∈ D, ‖g ℓ n‖
        ≤ ∑ D ∈ P.powersetCard (M + 1),
            ((N.card : ℝ) * (G ^ (M + 1) * ∏ ℓ ∈ D, (1 : ℝ) / ℓ) + 4 * G ^ (M + 1)) := by
          refine Finset.sum_le_sum fun D hD => ?_
          obtain ⟨hDP, hcard⟩ := hsub _ D hD
          have := hmaj D hDP
          rw [hcard] at this
          exact this
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- the error in the main terms
  have hθ : ‖∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
        (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))‖
      ≤ 4 * ∑ j ∈ Finset.range (M + 1), (P.card.choose j : ℝ) * G ^ j := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ D ∈ P.powersetCard j,
          ‖∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))‖
        ≤ ∑ _D ∈ P.powersetCard j, 4 * G ^ j := by
          refine Finset.sum_le_sum fun D hD => ?_
          obtain ⟨hDP, hcard⟩ := hsub _ D hD
          have := hmom D hDP
          rw [hcard] at this
          exact this
      _ = 4 * ((P.card.choose j : ℝ) * G ^ j) := by
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
          ring
  -- algebraic decomposition
  have hdecomp : ∑ n ∈ N, ∏ ℓ ∈ P, (1 + g ℓ n)
      = (N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - (N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        + ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
            (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        + ∑ n ∈ N, (∏ ℓ ∈ P, (1 + g ℓ n)
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n) := by
    have e1 : ∑ n ∈ N, ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
    have e2 : ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
          (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        = ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n
          - (N.card : ℂ) * ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
              ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [e2, Finset.sum_sub_distrib, e1]
    ring
  rw [hdecomp]
  have hn1 : ‖(N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))‖
      = (N.card : ℝ) * ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))‖ := by
    rw [norm_mul, Complex.norm_natCast]
  have hn2 : ‖(N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ) := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (htrunc'.trans hmodrem) hNn
  have hn4 : ‖∑ n ∈ N, (∏ ℓ ∈ P, (1 + g ℓ n)
        - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n)‖
      ≤ (N.card : ℝ) * (G ^ (M + 1) * ∑ D ∈ P.powersetCard (M + 1), ∏ ℓ ∈ D, (1 : ℝ) / ℓ)
        + 4 * ((P.card.choose (M + 1) : ℝ) * G ^ (M + 1)) :=
    ((norm_sum_le _ _).trans (Finset.sum_le_sum htrunc)).trans hrem
  have hchoose : ∑ j ∈ Finset.range (M + 2), (P.card.choose j : ℝ) * G ^ j
      = ∑ j ∈ Finset.range (M + 1), (P.card.choose j : ℝ) * G ^ j
        + (P.card.choose (M + 1) : ℝ) * G ^ (M + 1) := Finset.sum_range_succ _ _
  rw [hchoose]
  have t1 := norm_add_le
    ((N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - (N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ)))
        + ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
            (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))))
    (∑ n ∈ N, (∏ ℓ ∈ P, (1 + g ℓ n)
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, g ℓ n))
  have t2 := norm_add_le
    ((N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
        - (N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))))
    (∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j,
            (∑ n ∈ N, ∏ ℓ ∈ D, g ℓ n - (N.card : ℂ) * ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))))
  have t3 := norm_sub_le
    ((N.card : ℂ) * ∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ)))
    ((N.card : ℂ) * (∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))
            - ∑ j ∈ Finset.range (M + 1), ∑ D ∈ P.powersetCard j, ∏ ℓ ∈ D, (Γ / (ℓ : ℂ))))
  rw [hn1] at t3
  linarith


/-- If the exponential sum of `Y` over `N` is small, then `Y` is far from the integers on a
positive proportion of `N`. -/
lemma prop_of_fourier (N : Finset ℕ) (Y : ℕ → ℝ) (hN : N.Nonempty)
    (hF : ‖∑ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * ((Y n : ℝ) : ℂ))‖ ≤ N.card / 10) :
    ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ N ∧ (N.card : ℝ) ≤ 10 * A.card ∧
      ∀ n ∈ A, ∀ z : ℤ, 1 / 10 ≤ |Y n - z| := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A = N.filter (fun n => ∀ z : ℤ, 1 / 10 ≤ |Y n - z|) :=
    ⟨_, rfl⟩
  have hAN : A ⊆ N := by rw [hA]; exact Finset.filter_subset _ _
  have hNpos : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.mpr hN
  have hre : ∀ n, (Complex.exp (2 * Real.pi * Complex.I * ((Y n : ℝ) : ℂ))).re
      = Real.cos (2 * Real.pi * Y n) := by
    intro n
    have e : (2 * Real.pi * Complex.I * ((Y n : ℝ) : ℂ) : ℂ)
        = ((2 * Real.pi * Y n : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.exp_ofReal_mul_I_re]
  have hpi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hgood : ∀ n ∈ N, n ∉ A → (4 / 5 : ℝ) ≤ Real.cos (2 * Real.pi * Y n) := by
    intro n hn hnA
    have : ¬ ∀ z : ℤ, 1 / 10 ≤ |Y n - z| := fun h => hnA (by
      rw [hA]
      exact Finset.mem_filter.mpr ⟨hn, h⟩)
    push Not at this
    obtain ⟨z, hz⟩ := this
    have hcos : Real.cos (2 * Real.pi * Y n) = Real.cos (2 * Real.pi * (Y n - z)) := by
      have e : 2 * Real.pi * (Y n - z) = 2 * Real.pi * Y n - z * (2 * Real.pi) := by ring
      rw [e, Real.cos_sub_int_mul_two_pi]
    rw [hcos]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (Y n - z))
    have h2 : (2 * Real.pi * (Y n - z)) ^ 2 ≤ (2 * Real.pi * (1 / 10)) ^ 2 := by
      rw [← sq_abs (2 * Real.pi * (Y n - z))]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      exact mul_le_mul_of_nonneg_left hz.le (by positivity)
    have h3 : (2 * Real.pi * (1 / 10)) ^ 2 ≤ 2 / 5 := by nlinarith
    linarith
  have hall : ∀ n, (-1 : ℝ) ≤ Real.cos (2 * Real.pi * Y n) := fun n => Real.neg_one_le_cos _
  by_cases hbig : (N.card : ℝ) ≤ 10 * A.card
  · refine ⟨A, ?_, hAN, hbig, ?_⟩
    · refine Finset.card_pos.mp ?_
      have : (0 : ℝ) < A.card := by linarith
      exact_mod_cast this
    · intro n hn
      rw [hA] at hn
      exact (Finset.mem_filter.mp hn).2
  · exfalso
    rw [not_le] at hbig
    have hsum : (∑ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * ((Y n : ℝ) : ℂ))).re
        = ∑ n ∈ N, Real.cos (2 * Real.pi * Y n) := by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun n _ => hre n
    have hlow : (4 / 5 : ℝ) * (N.card - A.card) - A.card
        ≤ ∑ n ∈ N, Real.cos (2 * Real.pi * Y n) := by
      rw [← Finset.sum_sdiff hAN]
      have h1 : (4 / 5 : ℝ) * (N.card - A.card) ≤ ∑ n ∈ N \ A, Real.cos (2 * Real.pi * Y n) := by
        have hc : ((N \ A).card : ℝ) = N.card - A.card := by
          rw [Finset.card_sdiff_of_subset hAN, Nat.cast_sub (Finset.card_le_card hAN)]
        rw [← hc, mul_comm, ← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun n hn => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hn
        exact hgood n h1 h2
      have h2 : -(A.card : ℝ) ≤ ∑ n ∈ A, Real.cos (2 * Real.pi * Y n) := by
        have : ∑ _n ∈ A, (-1 : ℝ) ≤ ∑ n ∈ A, Real.cos (2 * Real.pi * Y n) :=
          Finset.sum_le_sum fun n _ => hall n
        rw [Finset.sum_const, nsmul_eq_mul] at this
        linarith
      linarith
    have hle := Complex.re_le_norm (∑ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * ((Y n : ℝ) : ℂ)))
    rw [hsum] at hle
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    linarith

/-- Decay of the model product: each factor with a large enough prime loses a definite amount. -/
lemma prod_model_bound (P P' : Finset ℕ) (Γ : ℂ) (ρ : ℝ) (_hρ : 0 < ρ) (hre : Γ.re ≤ -ρ)
    (hsub : P' ⊆ P) (hsmall : ∀ ℓ ∈ P, ‖1 + Γ / (ℓ : ℂ)‖ ≤ 1)
    (hbig : ∀ ℓ ∈ P', 0 < ℓ ∧ ‖Γ‖ ^ 2 ≤ ρ * ℓ) :
    ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))‖ ^ 2 ≤ Real.exp (-(ρ * ∑ ℓ ∈ P', (1 : ℝ) / ℓ)) := by
  classical
  have h1 : ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))‖ ≤ ∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖ := by
    rw [norm_prod, ← Finset.prod_sdiff hsub]
    have : ∏ ℓ ∈ P \ P', ‖1 + Γ / (ℓ : ℂ)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun ℓ hℓ => hsmall ℓ (Finset.mem_sdiff.mp hℓ).1)
    have h0 : 0 ≤ ∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc (∏ ℓ ∈ P \ P', ‖1 + Γ / (ℓ : ℂ)‖) * ∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖
        ≤ 1 * ∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖ := mul_le_mul_of_nonneg_right this h0
      _ = _ := one_mul _
  have h2 : ∀ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖ ^ 2 ≤ Real.exp (-(ρ * ((1 : ℝ) / ℓ))) := by
    intro ℓ hℓ
    obtain ⟨hpos, hb⟩ := hbig ℓ hℓ
    have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hpos
    have hrepart : (1 + Γ / (ℓ : ℂ)).re = 1 + Γ.re / ℓ := by
      simp [Complex.div_natCast_re]
    have himpart : (1 + Γ / (ℓ : ℂ)).im = Γ.im / ℓ := by
      simp [Complex.div_natCast_im]
    have hsq : ‖1 + Γ / (ℓ : ℂ)‖ ^ 2 = (1 + Γ.re / ℓ) ^ 2 + (Γ.im / ℓ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hrepart, himpart]
      ring
    have hΓsq : ‖Γ‖ ^ 2 = Γ.re ^ 2 + Γ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hexpand : (1 + Γ.re / ℓ) ^ 2 + (Γ.im / ℓ) ^ 2
        = 1 + 2 * Γ.re / ℓ + ‖Γ‖ ^ 2 / (ℓ : ℝ) ^ 2 := by
      rw [hΓsq]
      field_simp
      ring
    have hb' : ‖Γ‖ ^ 2 / (ℓ : ℝ) ^ 2 ≤ ρ / ℓ := by
      rw [div_le_div_iff₀ (by positivity) hℓR]
      nlinarith
    have hre' : 2 * Γ.re / ℓ ≤ -(2 * ρ) / ℓ :=
      div_le_div_of_nonneg_right (by linarith) hℓR.le
    have hfinal : ‖1 + Γ / (ℓ : ℂ)‖ ^ 2 ≤ 1 - ρ / ℓ := by
      rw [hsq, hexpand]
      have e : -(2 * ρ) / (ℓ : ℝ) = -2 * (ρ / ℓ) := by ring
      linarith
    have hexp := Real.add_one_le_exp (-(ρ * ((1 : ℝ) / ℓ)))
    have e2 : ρ * ((1 : ℝ) / ℓ) = ρ / ℓ := by ring
    linarith
  calc ‖∏ ℓ ∈ P, (1 + Γ / (ℓ : ℂ))‖ ^ 2
      ≤ (∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ∏ ℓ ∈ P', ‖1 + Γ / (ℓ : ℂ)‖ ^ 2 := (Finset.prod_pow _ _ _).symm
    _ ≤ ∏ ℓ ∈ P', Real.exp (-(ρ * ((1 : ℝ) / ℓ))) :=
        Finset.prod_le_prod (fun _ _ => by positivity) h2
    _ = Real.exp (-(ρ * ∑ ℓ ∈ P', (1 : ℝ) / ℓ)) := by
        rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]


lemma pow_lin (j : ℕ) (hj : 20 ≤ j) : (16 * (j + 2)) ^ 2 ≤ 2 ^ (j + 2) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : (16 * (j + 1 + 2)) ^ 2 ≤ 2 * (16 * (j + 2)) ^ 2 := by nlinarith
    calc (16 * (j + 1 + 2)) ^ 2 ≤ 2 * (16 * (j + 2)) ^ 2 := h1
      _ ≤ 2 * 2 ^ (j + 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (j + 1 + 2) := by ring

/-- Chebyshev lower bound on a block: the primes in `(2 ^ j, 2 ^ (j + 2)]` have reciprocal sum
at least `1 / (4 (j + 2))`. -/
lemma block_lower (j : ℕ) (hj : 20 ≤ j) :
    (1 : ℝ) / (4 * (j + 2))
      ≤ ∑ ℓ ∈ (Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime, (1 : ℝ) / ℓ := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpl := pow_lin j hj
  have hth := Chebyshev.theta_ge (2 ^ (j + 2))
  have hth2 := Chebyshev.theta_le_log4_mul_x (x := (((2 ^ j : ℕ)) : ℝ)) (by positivity)
  rw [Chebyshev.theta, Nat.floor_natCast] at hth hth2
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hnR : (((2 ^ (j + 2) : ℕ)) : ℝ) = 4 * 2 ^ j := by
    push_cast
    ring
  have hjR : (((2 ^ j : ℕ)) : ℝ) = 2 ^ j := by push_cast; ring
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  -- split the sum defining theta
  have hunion : (Finset.Ioc 0 (2 ^ (j + 2))).filter (fun p => p.Prime)
      = (Finset.Ioc 0 (2 ^ j)).filter (fun p => p.Prime)
        ∪ (Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))]
  have hdisj : Disjoint ((Finset.Ioc 0 (2 ^ j)).filter (fun p => p.Prime))
      ((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have a1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2
    have a2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  rw [hunion, Finset.sum_union hdisj] at hth
  have hblock : ∑ ℓ ∈ (Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime, Real.log (ℓ : ℝ)
      ≤ (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ)
        * ((j + 2) * Real.log 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun ℓ hℓ => ?_
    obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
    have a3 := (Finset.mem_Ioc.mp a1).2
    have a4 : (ℓ : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by exact_mod_cast a3
    have a5 := Real.log_le_log (by exact_mod_cast a2.pos) a4
    rw [Real.log_pow] at a5
    push_cast at a5
    exact a5
  -- the error terms
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (((2 ^ (j + 2) : ℕ)) : ℝ) := ⟨_, rfl⟩
  rw [← hn] at hth
  have hn4 : n = 4 * 2 ^ j := by rw [hn, hnR]
  have hn0 : 0 ≤ n := by rw [hn4]; positivity
  have hn1 : 1 ≤ n := by
    rw [hn4]
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hsqrt : 16 * ((j : ℝ) + 2) ≤ Real.sqrt n := by
    refine Real.le_sqrt_of_sq_le ?_
    have : (((16 * (j + 2)) ^ 2 : ℕ) : ℝ) ≤ (((2 ^ (j + 2) : ℕ)) : ℝ) := by exact_mod_cast hpl
    rw [hn]
    push_cast at this ⊢
    exact this
  have hsq := Real.mul_self_sqrt hn0
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hlogn : Real.log n = (j + 2) * Real.log 2 := by
    rw [hn]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have h16 : Real.sqrt n * (16 * ((j : ℝ) + 2)) ≤ n := by
    calc Real.sqrt n * (16 * ((j : ℝ) + 2)) ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_left hsqrt hsqrt0
      _ = n := hsq
  have hterm2 : 2 * Real.sqrt n * Real.log n ≤ 2 ^ j * Real.log 2 / 2 := by
    rw [hlogn]
    have e : 2 * Real.sqrt n * (((j : ℝ) + 2) * Real.log 2)
        = Real.sqrt n * (16 * ((j : ℝ) + 2)) * (Real.log 2 / 8) := by ring
    rw [e]
    calc Real.sqrt n * (16 * ((j : ℝ) + 2)) * (Real.log 2 / 8) ≤ n * (Real.log 2 / 8) :=
          mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = 2 ^ j * Real.log 2 / 2 := by rw [hn4]; ring
  have hterm1 : Real.log (n + 1) ≤ 2 ^ j * Real.log 2 / 2 := by
    have a1 : n + 1 ≤ 2 * n := by linarith
    have a2 := Real.log_le_log (by linarith) a1
    rw [Real.log_mul (by norm_num) (by linarith), hlogn] at a2
    have a3 : 2 * ((j : ℝ) + 3) ≤ 2 ^ j := by
      have : 2 * (j + 3) ≤ 2 ^ j := by
        have e : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
        nlinarith
      exact_mod_cast this
    have a4 := mul_le_mul_of_nonneg_right a3 hlog2.le
    linarith
  rw [hjR, hlog4] at hth2
  have hnlog : n * Real.log 2 = 4 * (2 ^ j * Real.log 2) := by rw [hn4]; ring
  have hcount : (2 : ℝ) ^ j * Real.log 2
      ≤ (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ)
        * ((j + 2) * Real.log 2) := by
    linarith
  have hcount' : (2 : ℝ) ^ j
      ≤ (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ) * (j + 2) := by
    have : (2 : ℝ) ^ j * Real.log 2
        ≤ (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ) * (j + 2)
          * Real.log 2 := by linarith
    exact le_of_mul_le_mul_right this hlog2
  have hlow : (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ)
      * (1 / (4 * 2 ^ j))
      ≤ ∑ ℓ ∈ (Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime, (1 : ℝ) / ℓ := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun ℓ hℓ => ?_
    obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
    have a3 := (Finset.mem_Ioc.mp a1).2
    have a4 : (ℓ : ℝ) ≤ 4 * 2 ^ j := by
      have : (ℓ : ℝ) ≤ (((2 ^ (j + 2) : ℕ)) : ℝ) := by exact_mod_cast a3
      rw [hnR] at this
      exact this
    exact one_div_le_one_div_of_le (by exact_mod_cast a2.pos) a4
  refine le_trans ?_ hlow
  rw [div_le_iff₀ (by positivity)]
  have e : (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ) * (1 / (4 * 2 ^ j))
      * (4 * ((j : ℝ) + 2))
      = (((Finset.Ioc (2 ^ j) (2 ^ (j + 2))).filter Nat.Prime).card : ℝ) * (j + 2) / 2 ^ j := by
    field_simp
  rw [e, le_div_iff₀ h2j]
  linarith

/-- A Mertens-type lower bound: primes in `(2 ^ ja, 2 ^ (ja + 2 I)]`. -/
lemma prime_recip_lower (ja : ℕ) (hja : 20 ≤ ja) (I : ℕ) :
    1 / 8 * Real.log (((ja + 2 * I + 2 : ℕ) : ℝ) / ((ja + 2 : ℕ) : ℝ))
      ≤ ∑ ℓ ∈ (Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * I))).filter Nat.Prime, (1 : ℝ) / ℓ := by
  classical
  induction I with
  | zero => simp
  | succ I ih =>
    have hunion : (Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * (I + 1)))).filter Nat.Prime
        = (Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * I))).filter Nat.Prime
          ∪ (Finset.Ioc (2 ^ (ja + 2 * I)) (2 ^ (ja + 2 * I + 2))).filter Nat.Prime := by
      rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc
        (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.pow_le_pow_right (by norm_num) (by omega))]
      rfl
    have hdisj : Disjoint ((Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * I))).filter Nat.Prime)
        ((Finset.Ioc (2 ^ (ja + 2 * I)) (2 ^ (ja + 2 * I + 2))).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      have a1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2
      have a2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
      omega
    rw [hunion, Finset.sum_union hdisj]
    have hb := block_lower (ja + 2 * I) (by omega)
    have hm : (0 : ℝ) < ((ja + 2 * I + 2 : ℕ) : ℝ) := by positivity
    have hm0 : (0 : ℝ) < ((ja + 2 : ℕ) : ℝ) := by positivity
    have hsplit : Real.log (((ja + 2 * (I + 1) + 2 : ℕ) : ℝ) / ((ja + 2 : ℕ) : ℝ))
        = Real.log (((ja + 2 * I + 2 : ℕ) : ℝ) / ((ja + 2 : ℕ) : ℝ))
          + Real.log (((ja + 2 * (I + 1) + 2 : ℕ) : ℝ) / ((ja + 2 * I + 2 : ℕ) : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep : Real.log (((ja + 2 * (I + 1) + 2 : ℕ) : ℝ) / ((ja + 2 * I + 2 : ℕ) : ℝ))
        ≤ 2 / ((ja + 2 * I + 2 : ℕ) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((ja + 2 * (I + 1) + 2 : ℕ) : ℝ) / ((ja + 2 * I + 2 : ℕ) : ℝ) by
          positivity)
      have e : ((ja + 2 * (I + 1) + 2 : ℕ) : ℝ) / ((ja + 2 * I + 2 : ℕ) : ℝ) - 1
          = 2 / ((ja + 2 * I + 2 : ℕ) : ℝ) := by
        field_simp
        push_cast
        ring
      linarith
    have hb' : 1 / 8 * (2 / ((ja + 2 * I + 2 : ℕ) : ℝ))
        ≤ ∑ ℓ ∈ (Finset.Ioc (2 ^ (ja + 2 * I)) (2 ^ (ja + 2 * I + 2))).filter Nat.Prime,
          (1 : ℝ) / ℓ := by
      refine le_trans (le_of_eq ?_) hb
      push_cast
      field_simp
      ring
    rw [hsplit]
    linarith


/-- A prime coprime to the modulus does not divide any difference of two near shifts. -/
lemma sep_of_coprime (K H Q W : ℕ) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (hWdef : W = ∏ y ∈ ((Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1)).offDiag,
      ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1 - ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)).natAbs)
    (hW0 : W ≠ 0)
    (hQ : Q = (∏ E ∈ (Finset.range K).powerset, p E)
      * ∏ ℓ ∈ W.primeFactors \ (Finset.range K).powerset.image p, ℓ ^ W.factorization ℓ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hco : Nat.Coprime Q ℓ) :
    ∀ y ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      ∀ z ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1), y ≠ z →
      ¬ (ℓ : ℤ) ∣ ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1) - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1) := by
  classical
  intro y hy z hz hne hdvd
  have hnotdvd : ¬ ℓ ∣ Q := by
    intro h
    have := (Nat.Coprime.symm hco).eq_one_of_dvd h
    exact hℓ.one_lt.ne' this
  have h1 : ℓ ∣ ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1 - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)).natAbs :=
    Int.natCast_dvd.mp hdvd
  have h2 : ((p y.1 : ℤ) * (y.2 : ℤ) - s y.1 - ((p z.1 : ℤ) * (z.2 : ℤ) - s z.1)).natAbs ∣ W := by
    rw [hWdef]
    exact Finset.dvd_prod_of_mem
      (fun y : (Finset ℕ × ℕ) × (Finset ℕ × ℕ) =>
        ((p y.1.1 : ℤ) * (y.1.2 : ℤ) - s y.1.1 - ((p y.2.1 : ℤ) * (y.2.2 : ℤ) - s y.2.1)).natAbs)
      (a := (y, z)) (Finset.mem_offDiag.mpr ⟨hy, hz, hne⟩)
  have hℓW : ℓ ∣ W := h1.trans h2
  apply hnotdvd
  rw [hQ]
  by_cases himg : ℓ ∈ (Finset.range K).powerset.image p
  · obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp himg
    exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem p hE) _
  · have hmem : ℓ ∈ W.primeFactors \ (Finset.range K).powerset.image p :=
      Finset.mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hℓ, hℓW, hW0⟩, himg⟩
    have hpos : 0 < W.factorization ℓ := Nat.Prime.factorization_pos_of_dvd hℓ hW0 hℓW
    have h3 : ℓ ∣ ℓ ^ W.factorization ℓ := dvd_pow_self ℓ hpos.ne'
    have h4 : ℓ ^ W.factorization ℓ
        ∣ ∏ ℓ ∈ W.primeFactors \ (Finset.range K).powerset.image p, ℓ ^ W.factorization ℓ :=
      Finset.dvd_prod_of_mem (fun ℓ => ℓ ^ W.factorization ℓ) hmem
    exact Dvd.dvd.mul_left (h3.trans h4) _

/-- If the shifts are distinct modulo `ℓ`, there are at most `ℓ` of them. -/
lemma card_le_of_sep (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hsep : ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ (ℓ : ℤ) ∣ r a - r c) : S.card ≤ ℓ := by
  classical
  have hpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range ℓ)
    (fun a => ((r a) % (ℓ : ℤ)).toNat) ?_ ?_
  · rwa [Finset.card_range] at h
  · intro a _
    rw [Finset.mem_coe, Finset.mem_range]
    have h1 := Int.emod_lt_of_pos (r a) hpos
    have h2 := Int.emod_nonneg (r a) hpos.ne'
    exact (Int.toNat_lt h2).mpr h1
  · intro a ha c hc heq
    by_contra hne
    apply hsep a (Finset.mem_coe.mp ha) c (Finset.mem_coe.mp hc) hne
    have h2a := Int.emod_nonneg (r a) hpos.ne'
    have h2c := Int.emod_nonneg (r c) hpos.ne'
    have heq' : (r a) % (ℓ : ℤ) = (r c) % (ℓ : ℤ) := by
      have : (((r a) % (ℓ : ℤ)).toNat : ℤ) = (((r c) % (ℓ : ℤ)).toNat : ℤ) := by
        exact_mod_cast heq
      rwa [Int.toNat_of_nonneg h2a, Int.toNat_of_nonneg h2c] at this
    exact Int.modEq_iff_dvd.mp (show (r c) ≡ (r a) [ZMOD ℓ] from heq'.symm)

/-- The number of prime factors up to `R` as a sum of indicators over the primes up to `R`. -/
lemma card_small (z : ℤ) (hz : z ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    ((z.natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)
      = ∑ ℓ ∈ (Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime,
        (if (ℓ : ℤ) ∣ z then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_boole]
  congr 2
  ext ℓ
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h3⟩
    exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor h3), h1⟩, Int.natCast_dvd.mpr h2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨h1, Int.natCast_dvd.mp h2, Int.natAbs_ne_zero.mpr hz⟩, ?_⟩
    have : ℓ ≤ ⌊R⌋₊ := Nat.lt_succ_iff.mp h0
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hR)

/-- The model factor is a convex combination of points of the unit disc. -/
lemma model_le_one (S : Finset (Finset ℕ × ℕ)) (e : Finset ℕ × ℕ → ℂ) (he : ∀ a ∈ S, ‖e a‖ ≤ 1)
    (ℓ : ℕ) (hℓ : S.card ≤ ℓ) (hℓ0 : 0 < ℓ) :
    ‖1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ)‖ ≤ 1 := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ0
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0.ne'
  have e1 : 1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ)
      = ((((ℓ : ℝ) - S.card : ℝ) : ℂ) + ∑ a ∈ S, e a) / (ℓ : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rw [e1, norm_div, Complex.norm_natCast, div_le_one hℓR]
  have hcard : (S.card : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  calc ‖(((ℓ : ℝ) - S.card : ℝ) : ℂ) + ∑ a ∈ S, e a‖
      ≤ ‖(((ℓ : ℝ) - S.card : ℝ) : ℂ)‖ + ‖∑ a ∈ S, e a‖ := norm_add_le _ _
    _ ≤ ((ℓ : ℝ) - S.card) + S.card := by
        refine add_le_add ?_ ?_
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        · calc ‖∑ a ∈ S, e a‖ ≤ ∑ a ∈ S, ‖e a‖ := norm_sum_le _ _
            _ ≤ ∑ _a ∈ S, (1 : ℝ) := Finset.sum_le_sum he
            _ = S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ℓ := by ring

lemma fact_bound (A : ℝ) (hA : 0 ≤ A) (Mp : ℕ) (hMp : 1 ≤ Mp) (h6 : 6 * A ≤ Mp) :
    A ^ Mp / (Mp.factorial : ℝ) ≤ (1 / 2) ^ Mp := by
  have hMpR : (0 : ℝ) < Mp := by exact_mod_cast hMp
  have hexp := Real.pow_div_factorial_le_exp (x := (Mp : ℝ)) hMpR.le Mp
  have hfac : (0 : ℝ) < Mp.factorial := by exact_mod_cast Nat.factorial_pos Mp
  have h1 : A ≤ Mp / 6 := by linarith
  have h2 : A ^ Mp ≤ ((Mp : ℝ) / 6) ^ Mp := pow_le_pow_left₀ hA h1 Mp
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hexpMp : Real.exp (Mp : ℝ) = (Real.exp 1) ^ Mp := by
    rw [← Real.exp_nat_mul, mul_one]
  have h3 : (Real.exp 1) ^ Mp ≤ (3 : ℝ) ^ Mp := pow_le_pow_left₀ (Real.exp_pos 1).le he Mp
  rw [div_le_iff₀ hfac]
  have h4 : (Mp : ℝ) ^ Mp ≤ (3 : ℝ) ^ Mp * Mp.factorial := by
    rw [div_le_iff₀ hfac, hexpMp] at hexp
    exact hexp.trans (mul_le_mul_of_nonneg_right h3 hfac.le)
  calc A ^ Mp ≤ ((Mp : ℝ) / 6) ^ Mp := h2
    _ = (Mp : ℝ) ^ Mp * (1 / 6) ^ Mp := by rw [div_eq_mul_one_div, mul_pow]
    _ ≤ (3 : ℝ) ^ Mp * Mp.factorial * (1 / 6) ^ Mp :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (1 / 2) ^ Mp * Mp.factorial := by
        have : (3 : ℝ) ^ Mp * (1 / 6) ^ Mp = (1 / 2) ^ Mp := by
          rw [← mul_pow]
          norm_num
        calc (3 : ℝ) ^ Mp * Mp.factorial * (1 / 6) ^ Mp
            = (3 : ℝ) ^ Mp * (1 / 6) ^ Mp * Mp.factorial := by ring
          _ = (1 / 2) ^ Mp * Mp.factorial := by rw [this]

lemma choose_sum_le (n Mp : ℕ) (hn : 1 ≤ n) (G G1 : ℝ) (hG : 0 ≤ G) (hG1 : G ≤ G1) (h1 : 1 ≤ G1) :
    ∑ j ∈ Finset.range (Mp + 1), (n.choose j : ℝ) * G ^ j
      ≤ ((Mp : ℝ) + 1) * ((n : ℝ) * G1) ^ Mp := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterm : ∀ j ∈ Finset.range (Mp + 1), (n.choose j : ℝ) * G ^ j ≤ ((n : ℝ) * G1) ^ Mp := by
    intro j hj
    have hjM : j ≤ Mp := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have a1 : (n.choose j : ℝ) ≤ (n : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow n j
    have a2 : (n : ℝ) ^ j ≤ (n : ℝ) ^ Mp := pow_le_pow_right₀ hnR hjM
    have a3 : G ^ j ≤ G1 ^ j := pow_le_pow_left₀ hG hG1 j
    have a4 : G1 ^ j ≤ G1 ^ Mp := pow_le_pow_right₀ h1 hjM
    rw [mul_pow]
    exact mul_le_mul (a1.trans a2) (a3.trans a4) (by positivity) (by positivity)
  calc ∑ j ∈ Finset.range (Mp + 1), (n.choose j : ℝ) * G ^ j
      ≤ ∑ _j ∈ Finset.range (Mp + 1), ((n : ℝ) * G1) ^ Mp := Finset.sum_le_sum hterm
    _ = ((Mp : ℝ) + 1) * ((n : ℝ) * G1) ^ Mp := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring


lemma phase_eq (θ : ℝ) : Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ))
    = Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring

lemma phase_norm (θ : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ))‖ = 1 := by
  rw [phase_eq, Complex.norm_exp_ofReal_mul_I]

lemma phase_sub_one (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ)) - 1‖ ≤ 2 * Real.pi * |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * θ)
  have e : Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [e]
  refine h.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]

lemma phase_re (θ : ℝ) : (Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ)) - 1).re
    = Real.cos (2 * Real.pi * θ) - 1 := by
  rw [Complex.sub_re, phase_eq, Complex.exp_ofReal_mul_I_re, Complex.one_re]

/-- Non-concentration modulo one of the weighted count of prime factors up to `R`, from the
analytic inputs. -/
lemma h2_main (L U Q b : ℕ) (hQ : 0 < Q) (hLU : L ≤ U + 1)
    (S : Finset (Finset ℕ × ℕ)) (r : Finset ℕ × ℕ → ℤ) (wt : Finset ℕ × ℕ → ℝ) (q R ρ : ℝ)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hρ : 0 < ρ) (Mp : ℕ) (hMp : 7 ≤ Mp) (P' : Finset ℕ)
    (hNne : ((Finset.Icc L U).filter (fun n => n % Q = b % Q)).Nonempty)
    (hpos : ∀ n ∈ (Finset.Icc L U).filter (fun n => n % Q = b % Q), ∀ a ∈ S,
      (n : ℤ) + r a ≠ 0)
    (hsep : ∀ ℓ : ℕ, ℓ.Prime → Nat.Coprime Q ℓ →
      ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ (ℓ : ℤ) ∣ r a - r c)
    (hwt1 : ∑ a ∈ S, |wt a| ≤ 1)
    (hre : ∑ a ∈ S, (Real.cos (2 * Real.pi * (q * wt a)) - 1) ≤ -ρ)
    (hP' : P' ⊆ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter (fun ℓ => Nat.Coprime Q ℓ))
    (hbig : ∀ ℓ ∈ P', (2 * Real.pi * q) ^ 2 ≤ ρ * ℓ)
    (hprod : 8 ≤ ρ * ∑ ℓ ∈ P', (1 : ℝ) / ℓ)
    (hfact : 6 * (2 * Real.pi * q * ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
      (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ) ≤ Mp)
    (hcount : 160 * (((Mp : ℝ) + 1) * (((((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ)).card + 1 : ℝ) * (2 * Real.pi * q + 1)) ^ Mp)
      ≤ (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ)) :
    ∃ A : Finset ℕ, A.Nonempty ∧ A ⊆ (Finset.Icc L U).filter (fun n => n % Q = b % Q) ∧
      (((Finset.Icc L U).filter (fun n => n % Q = b % Q)).card : ℝ) ≤ 10 * A.card ∧
      ∀ n ∈ A, ∀ z : ℤ, 1 / 10 ≤ |q * (∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)) - z| := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = T.filter (fun ℓ => Nat.Coprime Q ℓ) := ⟨_, rfl⟩
  rw [← hT, ← hPdef] at hP' hfact hcount
  obtain ⟨N, hN⟩ : ∃ N : Finset ℕ, N = (Finset.Icc L U).filter (fun n => n % Q = b % Q) :=
    ⟨_, rfl⟩
  have hTprime : ∀ ℓ ∈ T, ℓ.Prime := by
    intro ℓ hℓ
    rw [hT] at hℓ
    exact (Finset.mem_filter.mp hℓ).2
  have hPmem : ∀ ℓ ∈ P, ℓ.Prime ∧ Nat.Coprime Q ℓ := by
    intro ℓ hℓ
    rw [hPdef] at hℓ
    obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
    exact ⟨hTprime ℓ a1, a2⟩
  obtain ⟨e, he⟩ : ∃ e : Finset ℕ × ℕ → ℂ,
      ∀ a, e a = Complex.exp (2 * Real.pi * Complex.I * ((q * wt a : ℝ) : ℂ)) :=
    ⟨_, fun _ => rfl⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have hγnorm : ∀ a, ‖e a - 1‖ ≤ 2 * Real.pi * q * |wt a| := by
    intro a
    rw [he]
    have := phase_sub_one (q * wt a)
    rw [abs_mul, abs_of_nonneg hq] at this
    linarith
  have hG : ∑ a ∈ S, ‖e a - 1‖ ≤ 2 * Real.pi * q := by
    calc ∑ a ∈ S, ‖e a - 1‖ ≤ ∑ a ∈ S, 2 * Real.pi * q * |wt a| :=
          Finset.sum_le_sum fun a _ => hγnorm a
      _ = 2 * Real.pi * q * ∑ a ∈ S, |wt a| := by rw [Finset.mul_sum]
      _ ≤ 2 * Real.pi * q * 1 := mul_le_mul_of_nonneg_left hwt1 (by positivity)
      _ = 2 * Real.pi * q := mul_one _
  have hG0 : 0 ≤ ∑ a ∈ S, ‖e a - 1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΓre : (∑ a ∈ S, (e a - 1)).re ≤ -ρ := by
    rw [Complex.re_sum]
    simp only [he, phase_re]
    exact hre
  have hΓnorm : ‖∑ a ∈ S, (e a - 1)‖ ≤ 2 * Real.pi * q := (norm_sum_le _ _).trans hG
  have hsmall : ∀ ℓ ∈ P, ‖1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ)‖ ≤ 1 := by
    intro ℓ hℓ
    obtain ⟨a1, a2⟩ := hPmem ℓ hℓ
    exact model_le_one S e (fun a _ => by rw [he, phase_norm]) ℓ
      (card_le_of_sep S r ℓ a1.pos (hsep ℓ a1 a2)) a1.pos
  -- the local factors
  have hloc : ∀ ℓ ∈ P, ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I *
        ((q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) : ℝ) : ℂ))
      = 1 + ∑ a ∈ S, (e a - 1) * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0) := by
    intro ℓ hℓ n
    obtain ⟨a1, a2⟩ := hPmem ℓ hℓ
    have := local_factor S r wt q ℓ n (hsep ℓ a1 a2)
    simp only [← he] at this
    exact this
  have hunit : ∀ n ∈ (Finset.Icc L U).filter (fun n => n % Q = b % Q), ∀ ℓ ∈ P,
      ‖1 + ∑ a ∈ S, (e a - 1) * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)‖ ≤ 1 := by
    intro n _ ℓ hℓ
    rw [← hloc ℓ hℓ n, phase_norm]
  -- the constant from the primes dividing the modulus
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = ∑ ℓ ∈ T.filter (fun ℓ => ¬ Nat.Coprime Q ℓ),
      ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (b : ℤ) + r a then (1 : ℝ) else 0) := ⟨_, rfl⟩
  have hY : ∀ n ∈ N, q * (∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ))
      = q * c0 + ∑ ℓ ∈ P,
          q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) := by
    intro n hn
    rw [hN] at hn
    have hnQ : (n : ℤ) ≡ (b : ℤ) [ZMOD Q] := Int.natCast_modEq_iff.mpr (Finset.mem_filter.mp hn).2
    have h1 : ∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)
        = ∑ ℓ ∈ T, ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [card_small _ (hpos n hn a ha) R hR, ← hT, Finset.mul_sum]
    have h2 := Finset.sum_filter_add_sum_filter_not T (fun ℓ => Nat.Coprime Q ℓ)
      (fun ℓ => ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0))
    have h3 : ∑ ℓ ∈ T.filter (fun ℓ => ¬ Nat.Coprime Q ℓ),
        ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) = c0 := by
      rw [hc0]
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
      have hℓp := hTprime ℓ a1
      have hdvd : ℓ ∣ Q := by
        by_contra hnd
        exact a2 ((Nat.Prime.coprime_iff_not_dvd hℓp).mpr hnd).symm
      have hdvdZ : (ℓ : ℤ) ∣ (Q : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
      refine Finset.sum_congr rfl fun a _ => ?_
      have hmodℓ : (n : ℤ) + r a ≡ (b : ℤ) + r a [ZMOD (ℓ : ℤ)] :=
        (hnQ.add_right (r a)).of_dvd hdvdZ
      have hiff : ((ℓ : ℤ) ∣ (n : ℤ) + r a) ↔ ((ℓ : ℤ) ∣ (b : ℤ) + r a) := hmodℓ.dvd_iff
      simp only [hiff]
    rw [h1, ← h2, h3, ← hPdef, mul_add, Finset.mul_sum]
    ring
  -- the exponential sum
  have hexp : ∀ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * (((q * (∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)) : ℝ)) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((q * c0 : ℝ) : ℂ))
        * ∏ ℓ ∈ P, (1 + ∑ a ∈ S, (e a - 1) * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0)) := by
    intro n hn
    rw [hY n hn]
    have : (2 * Real.pi * Complex.I * (((q * c0 + ∑ ℓ ∈ P,
          q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) : ℝ)) : ℂ))
        = 2 * Real.pi * Complex.I * ((q * c0 : ℝ) : ℂ)
          + ∑ ℓ ∈ P, 2 * Real.pi * Complex.I *
            ((q * ∑ a ∈ S, wt a * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.mul_sum]
    rw [this, Complex.exp_add, Complex.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun ℓ hℓ => hloc ℓ hℓ n
  have hnormeq : ‖∑ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * (((q * (∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)) : ℝ)) : ℂ))‖
      = ‖∑ n ∈ N, ∏ ℓ ∈ P,
          (1 + ∑ a ∈ S, (e a - 1) * (if (ℓ : ℤ) ∣ (n : ℤ) + r a then (1 : ℂ) else 0))‖ := by
    rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum, norm_mul, phase_norm, one_mul]
  -- the Fourier bound
  have hMp1 : Mp - 1 + 1 = Mp := by omega
  have hMp2 : Mp - 1 + 2 = Mp + 1 := by omega
  have hfb := fourier_bound L U Q b hQ hLU S r (fun a => e a - 1) P (Mp - 1) hPmem hunit hsmall
  rw [← hN, hMp1, hMp2] at hfb
  -- the three pieces
  have hNn : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
  have hb1 : ‖∏ ℓ ∈ P, (1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ))‖ ≤ 1 / 40 := by
    have hbig' : ∀ ℓ ∈ P', 0 < ℓ ∧ ‖∑ a ∈ S, (e a - 1)‖ ^ 2 ≤ ρ * ℓ := by
      intro ℓ hℓ
      refine ⟨(hPmem ℓ (hP' hℓ)).1.pos, ?_⟩
      calc ‖∑ a ∈ S, (e a - 1)‖ ^ 2 ≤ (2 * Real.pi * q) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hΓnorm 2
        _ ≤ ρ * ℓ := hbig ℓ hℓ
    have h := prod_model_bound P P' (∑ a ∈ S, (e a - 1)) ρ hρ hΓre hP' hsmall hbig'
    have hexp8 : Real.exp (-(ρ * ∑ ℓ ∈ P', (1 : ℝ) / ℓ)) ≤ (1 / 40) ^ 2 := by
      have a1 : Real.exp (-(ρ * ∑ ℓ ∈ P', (1 : ℝ) / ℓ)) ≤ Real.exp (-8) :=
        Real.exp_le_exp.mpr (by linarith)
      have a2 : Real.exp (-8) = 1 / Real.exp 1 ^ 8 := by
        rw [Real.exp_neg, ← Real.exp_nat_mul]
        norm_num
      have a3 : (2.7 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := by
        have := Real.exp_one_gt_d9
        exact pow_le_pow_left₀ (by norm_num) (by linarith) 8
      have a4 : 1 / Real.exp 1 ^ 8 ≤ 1 / (2.7 : ℝ) ^ 8 :=
        one_div_le_one_div_of_le (by positivity) a3
      have a5 : (1 : ℝ) / 2.7 ^ 8 ≤ (1 / 40) ^ 2 := by norm_num
      linarith
    have h2 : ‖∏ ℓ ∈ P, (1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ))‖ ^ 2 ≤ (1 / 40) ^ 2 := h.trans hexp8
    exact (abs_le_of_sq_le_sq' h2 (by norm_num)).2
  have hb2 : (∑ a ∈ S, ‖e a - 1‖) ^ Mp * ∑ D ∈ P.powersetCard Mp, ∏ ℓ ∈ D, (1 : ℝ) / ℓ
      ≤ 1 / 128 := by
    have hes := esymm_le (fun ℓ : ℕ => (1 : ℝ) / ℓ) P (fun _ _ => by positivity) Mp
    have hfac : (0 : ℝ) < Mp.factorial := by exact_mod_cast Nat.factorial_pos Mp
    have hL0 : 0 ≤ ∑ ℓ ∈ P, (1 : ℝ) / ℓ := Finset.sum_nonneg fun _ _ => by positivity
    have hA0 : 0 ≤ 2 * Real.pi * q * ∑ ℓ ∈ P, (1 : ℝ) / ℓ := by positivity
    have hfb2 := fact_bound (2 * Real.pi * q * ∑ ℓ ∈ P, (1 : ℝ) / ℓ) hA0 Mp (by omega) hfact
    have he0 : 0 ≤ ∑ D ∈ P.powersetCard Mp, ∏ ℓ ∈ D, (1 : ℝ) / ℓ :=
      Finset.sum_nonneg fun D _ => Finset.prod_nonneg fun _ _ => by positivity
    have h1 : ∑ D ∈ P.powersetCard Mp, ∏ ℓ ∈ D, (1 : ℝ) / ℓ
        ≤ (∑ ℓ ∈ P, (1 : ℝ) / ℓ) ^ Mp / Mp.factorial := by
      rw [le_div_iff₀ hfac]
      linarith
    have h2 : (∑ a ∈ S, ‖e a - 1‖) ^ Mp ≤ (2 * Real.pi * q) ^ Mp := pow_le_pow_left₀ hG0 hG Mp
    calc (∑ a ∈ S, ‖e a - 1‖) ^ Mp * ∑ D ∈ P.powersetCard Mp, ∏ ℓ ∈ D, (1 : ℝ) / ℓ
        ≤ (2 * Real.pi * q) ^ Mp * ((∑ ℓ ∈ P, (1 : ℝ) / ℓ) ^ Mp / Mp.factorial) :=
          mul_le_mul h2 h1 he0 (by positivity)
      _ = (2 * Real.pi * q * ∑ ℓ ∈ P, (1 : ℝ) / ℓ) ^ Mp / Mp.factorial := by
          rw [mul_pow]
          ring
      _ ≤ (1 / 2) ^ Mp := hfb2
      _ ≤ (1 / 2) ^ 7 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hMp
      _ = 1 / 128 := by norm_num
  have hb3 : ∑ j ∈ Finset.range (Mp + 1), (P.card.choose j : ℝ) * (∑ a ∈ S, ‖e a - 1‖) ^ j
      ≤ ((Mp : ℝ) + 1) * (((P.card : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp := by
    have h1 : ∑ j ∈ Finset.range (Mp + 1), (P.card.choose j : ℝ) * (∑ a ∈ S, ‖e a - 1‖) ^ j
        ≤ ∑ j ∈ Finset.range (Mp + 1),
          ((P.card + 1).choose j : ℝ) * (∑ a ∈ S, ‖e a - 1‖) ^ j := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Nat.choose_le_choose j (Nat.le_succ P.card)
    have h2 := choose_sum_le (P.card + 1) Mp (by omega) (∑ a ∈ S, ‖e a - 1‖)
      (2 * Real.pi * q + 1) hG0 (by linarith) (by nlinarith)
    push_cast at h2
    exact h1.trans h2
  -- conclusion
  have hF : ‖∑ n ∈ N, Complex.exp (2 * Real.pi * Complex.I * (((q * (∑ a ∈ S, wt a *
        ((((n : ℤ) + r a).natAbs.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ R)).card : ℝ)) : ℝ)) : ℂ))‖
      ≤ N.card / 10 := by
    rw [hnormeq]
    refine hfb.trans ?_
    rw [← hN] at hcount
    have t1 : (N.card : ℝ) * ‖∏ ℓ ∈ P, (1 + (∑ a ∈ S, (e a - 1)) / (ℓ : ℂ))‖
        ≤ N.card * (1 / 40) := mul_le_mul_of_nonneg_left hb1 hNn
    have t2 : 2 * (N.card : ℝ) * ((∑ a ∈ S, ‖e a - 1‖) ^ Mp
        * ∑ D ∈ P.powersetCard Mp, ∏ ℓ ∈ D, (1 : ℝ) / ℓ) ≤ 2 * N.card * (1 / 128) :=
      mul_le_mul_of_nonneg_left hb2 (by positivity)
    linarith
  rw [← hN] at hNne ⊢
  exact prop_of_fourier N _ hNne hF


/-- The real part of the sum of the local phases is negative of size `q ^ 2 / 2 ^ K`. -/
lemma re_bound (K H : ℕ) (hH : 0 < H) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 2 ^ K) :
    ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
        (Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ a.1.card / 2 ^ a.2))) - 1)
      ≤ -(2 * q ^ 2 / 2 ^ K) := by
  classical
  have hpi := Real.pi_pos
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  -- one term at the first near shift
  have hone : ∀ c : ℕ, Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ c / 2 ^ (K + 1)))) - 1
      ≤ -(2 * (q / 2 ^ K) ^ 2) := by
    intro c
    have hcos : Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ c / 2 ^ (K + 1))))
        = Real.cos (2 * (Real.pi * q / 2 ^ (K + 1))) := by
      rcases neg_one_pow_eq_or ℝ c with h | h
      · rw [h]
        congr 1
        ring
      · rw [h, ← Real.cos_neg]
        congr 1
        ring
    rw [hcos, Real.cos_two_mul]
    have hx0 : 0 ≤ Real.pi * q / 2 ^ (K + 1) := by positivity
    have hx1 : Real.pi * q / 2 ^ (K + 1) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num), pow_succ]
      nlinarith
    have hsin := Real.mul_le_sin hx0 hx1
    have hsin0 : 0 ≤ Real.sin (Real.pi * q / 2 ^ (K + 1)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
    have e : 2 / Real.pi * (Real.pi * q / 2 ^ (K + 1)) = q / 2 ^ K := by
      rw [pow_succ]
      field_simp
    rw [e] at hsin
    have hq2 : 0 ≤ q / 2 ^ K := by positivity
    have hsq : (q / 2 ^ K) ^ 2 ≤ Real.sin (Real.pi * q / 2 ^ (K + 1)) ^ 2 :=
      pow_le_pow_left₀ hq2 hsin 2
    have hpyth := Real.sin_sq_add_cos_sq (Real.pi * q / 2 ^ (K + 1))
    nlinarith
  have hnonpos : ∀ a : Finset ℕ × ℕ,
      Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ a.1.card / 2 ^ a.2))) - 1 ≤ 0 := by
    intro a
    have := Real.cos_le_one (2 * Real.pi * (q * ((-1 : ℝ) ^ a.1.card / 2 ^ a.2)))
    linarith
  rw [Finset.sum_product]
  have hmem : K + 1 ∈ Finset.Ico (K + 1) (K + H + 1) := Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
  have hrow : ∀ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1),
      (Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2))) - 1)
      ≤ -(2 * (q / 2 ^ K) ^ 2) := by
    intro E _
    rw [← Finset.add_sum_erase _ _ hmem]
    have h1 := hone E.card
    have h2 : ∑ h ∈ (Finset.Ico (K + 1) (K + H + 1)).erase (K + 1),
        (Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2))) - 1) ≤ 0 :=
      Finset.sum_nonpos fun h _ => hnonpos (E, h)
    linarith
  calc ∑ E ∈ (Finset.range K).powerset, ∑ h ∈ Finset.Ico (K + 1) (K + H + 1),
        (Real.cos (2 * Real.pi * (q * ((-1 : ℝ) ^ (E, h).1.card / 2 ^ (E, h).2))) - 1)
      ≤ ∑ _E ∈ (Finset.range K).powerset, -(2 * (q / 2 ^ K) ^ 2) := Finset.sum_le_sum hrow
    _ = -(2 * q ^ 2 / 2 ^ K) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-- Comparisons between `l`, `u = exp l`, `t = exp u` and `q`. -/
lemma scale2 (l u t : ℝ) (q : ℕ) (hl6 : 6 * 10 ^ 12 ≤ l) (hlq : 5000 * (q : ℝ) ≤ l)
    (hexpl : Real.exp l = u) (hexpu : Real.exp u = t) :
    l + 1 ≤ u ∧ u ^ 4 / 24 ≤ t ∧ 152 * (q : ℝ) * (1 + u) ≤ u ^ 2 / 16 - 1 ∧ u ^ 2 * l ≤ t ∧
    32 * l ^ 2 + 3 * l + 2 ≤ u ∧ 16 * (q : ℝ) ≤ u ∧ 20 * u ^ 2 ≤ t / 16 := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl6
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : l + 1 ≤ u := by rw [← hexpl]; exact Real.add_one_le_exp l
  have hu0 : 0 < u := by linarith
  have hf4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have h2 : l ^ 4 / 24 ≤ u := by
    have := Real.pow_div_factorial_le_exp (x := l) hl0.le 4
    rw [hf4, hexpl] at this
    exact this
  have h3 : u ^ 4 / 24 ≤ t := by
    have := Real.pow_div_factorial_le_exp (x := u) hu0.le 4
    rw [hf4, hexpu] at this
    exact this
  have hl2 : (840 : ℝ) ≤ l ^ 2 := by nlinarith
  have h5 : 32 * l ^ 2 + 3 * l + 2 ≤ u := by
    have a1 : 35 * l ^ 2 ≤ l ^ 4 / 24 := by
      have : l ^ 4 = l ^ 2 * l ^ 2 := by ring
      nlinarith
    have a2 : 3 * l + 2 ≤ 3 * l ^ 2 := by nlinarith
    linarith
  have hu24 : (7680 : ℝ) ≤ u := by linarith
  have hqu : (q : ℝ) ≤ u / 5000 := by linarith
  refine ⟨h1, h3, ?_, ?_, h5, by linarith, ?_⟩
  · have a1 : 152 * (q : ℝ) * (1 + u) ≤ 152 * (u / 5000) * (1 + u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · have a1 : u ^ 2 * l ≤ u ^ 2 * u := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have a2 : u ^ 2 * u ≤ u ^ 4 / 24 := by
      have : u ^ 4 = u ^ 2 * u * u := by ring
      nlinarith [pow_pos hu0 3]
    linarith
  · have hu2 : (7680 : ℝ) ≤ u ^ 2 := by nlinarith
    have a0 : 7680 * u ^ 2 ≤ u ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)
    have a1 : 320 * u ^ 2 ≤ u ^ 4 / 24 := by
      have : u ^ 4 = u ^ 2 * u ^ 2 := by ring
      linarith
    linarith

lemma count_arith (y0 a c d Nc : ℝ) (_ha0 : 0 ≤ a) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (ha : a ≤ y0)
    (hc : c ≤ y0) (hd : d ≤ y0) (hy : 1 ≤ y0) (hN : y0 ^ 12 ≤ Nc) : a * (c * d) ≤ Nc := by
  have h1 : c * d ≤ y0 * y0 := mul_le_mul hc hd hd0 (by linarith)
  have h2 : a * (c * d) ≤ y0 * (y0 * y0) := mul_le_mul ha h1 (by positivity) (by linarith)
  have h3 : y0 * (y0 * y0) = y0 ^ 3 := by ring
  have h4 : y0 ^ 3 ≤ y0 ^ 12 := pow_le_pow_right₀ hy (by norm_num)
  linarith

/-- The dyadic range of primes used for the decay of the model product. -/
lemma ja_jb (l u t : ℝ) (ja jb : ℕ) (hl6 : 6 * 10 ^ 12 ≤ l) (hexpl : Real.exp l = u)
    (hexpu : Real.exp u = t) (hu1 : l + 1 ≤ u) (ht4 : u ^ 4 / 24 ≤ t)
    (h5 : 32 * l ^ 2 + 3 * l + 2 ≤ u)
    (hja : ja = ⌈Real.exp (l / 2) / Real.log 2⌉₊ + 20)
    (hjb : jb = ⌊t / (u ^ 2 * Real.log 2)⌋₊) :
    Real.exp (Real.exp (l / 2)) ≤ (2 : ℝ) ^ ja ∧ (2 : ℝ) ^ jb ≤ Real.exp (t / u ^ 2) ∧
    ja ≤ jb ∧ 20 ≤ ja ∧
    32 * l ^ 2 ≤ Real.log (((ja + 2 * ((jb - ja) / 2) + 2 : ℕ) : ℝ) / ((ja + 2 : ℕ) : ℝ)) := by
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl6
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2a := Real.log_two_gt_d9
  have hlog2b := Real.log_two_lt_d9
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht4
  have hw : Real.exp (l / 2) ≤ u := by
    rw [← hexpl]
    exact Real.exp_le_exp.mpr (by linarith)
  have hw0 : 0 < Real.exp (l / 2) := Real.exp_pos _
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ j = Real.exp (j * Real.log 2) := by
    intro j
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  -- ja
  have hja1 : Real.exp (l / 2) / Real.log 2 ≤ ja := by
    rw [hja]
    push_cast
    have := Nat.le_ceil (Real.exp (l / 2) / Real.log 2)
    linarith
  have hja2 : (ja : ℝ) ≤ Real.exp (l / 2) / Real.log 2 + 21 := by
    rw [hja]
    push_cast
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Real.exp (l / 2) / Real.log 2 by positivity)
    linarith
  have hja3 : (ja : ℝ) ≤ 2 * u + 21 := by
    have : Real.exp (l / 2) / Real.log 2 ≤ 2 * u := by
      rw [div_le_iff₀ hlog2]
      nlinarith
    linarith
  -- jb
  have hu2 : 0 < u ^ 2 := by positivity
  have hjb1 : (jb : ℝ) ≤ t / (u ^ 2 * Real.log 2) := by
    rw [hjb]
    exact Nat.floor_le (by positivity)
  have hjb2 : t / (u ^ 2 * Real.log 2) < jb + 1 := by
    rw [hjb]
    exact Nat.lt_floor_add_one _
  have htu : u ^ 2 / 24 ≤ t / u ^ 2 := by
    rw [le_div_iff₀ hu2]
    have : u ^ 2 / 24 * u ^ 2 = u ^ 4 / 24 := by ring
    linarith
  have htu2 : t / u ^ 2 ≤ t / (u ^ 2 * Real.log 2) := by
    rw [div_le_div_iff₀ hu2 (by positivity)]
    have : t * (u ^ 2 * Real.log 2) ≤ t * (u ^ 2 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hu2.le) ht0.le
    linarith
  have hubig : (6 * 10 ^ 12 : ℝ) ≤ u := by linarith
  have hjab : (ja : ℝ) + 2 ≤ jb := by
    have : 2 * u + 24 ≤ u ^ 2 / 24 := by nlinarith
    linarith
  refine ⟨?_, ?_, by exact_mod_cast (by linarith : (ja : ℝ) ≤ jb), by omega, ?_⟩
  · rw [hpow]
    refine Real.exp_le_exp.mpr ?_
    have := (div_le_iff₀ hlog2).mp hja1
    exact this
  · rw [hpow]
    refine Real.exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_right hjb1 hlog2.le
    have e : t / (u ^ 2 * Real.log 2) * Real.log 2 = t / u ^ 2 := by
      field_simp
    linarith
  · have hjanat : ja ≤ jb := by exact_mod_cast (by linarith : (ja : ℝ) ≤ jb)
    have hI : jb ≤ ja + 2 * ((jb - ja) / 2) + 1 := by omega
    have hnum : t / u ^ 2 ≤ ((ja + 2 * ((jb - ja) / 2) + 2 : ℕ) : ℝ) := by
      have a1 : ((jb + 1 : ℕ) : ℝ) ≤ ((ja + 2 * ((jb - ja) / 2) + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : jb + 1 ≤ ja + 2 * ((jb - ja) / 2) + 2)
      push_cast at a1 ⊢
      linarith
    have hden : ((ja + 2 : ℕ) : ℝ) ≤ 3 * u := by
      push_cast
      linarith
    have hden0 : (0 : ℝ) < ((ja + 2 : ℕ) : ℝ) := by positivity
    have hratio : t / (3 * u ^ 3) ≤ ((ja + 2 * ((jb - ja) / 2) + 2 : ℕ) : ℝ) / ((ja + 2 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hden0]
      have a1 : t * ((ja + 2 : ℕ) : ℝ) ≤ t * (3 * u) := mul_le_mul_of_nonneg_left hden ht0.le
      have a2 : t / u ^ 2 * (3 * u ^ 3) ≤ ((ja + 2 * ((jb - ja) / 2) + 2 : ℕ) : ℝ) * (3 * u ^ 3) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      have e : t / u ^ 2 * (3 * u ^ 3) = t * (3 * u) := by
        field_simp
      linarith
    have hlog := Real.log_le_log (by positivity) hratio
    have hlogt : Real.log t = u := by rw [← hexpu, Real.log_exp]
    have hlogu : Real.log u = l := by rw [← hexpl, Real.log_exp]
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, hlogt, hlogu] at hlog
    simp only [Nat.cast_ofNat] at hlog
    linarith


lemma arith_N (z Nc D Qr : ℝ) (hz4 : 4 ≤ z) (hQ : 0 < Qr) (hQz : Qr ≤ z)
    (hlow : D / Qr - 2 ≤ Nc) (hD : z ^ 8 / 2 ≤ D) : z ^ 6 ≤ Nc := by
  have hz0 : 0 < z := by linarith
  have h1 : z ^ 7 / 2 ≤ D / Qr := by
    rw [le_div_iff₀ hQ]
    have a1 : z ^ 7 / 2 * Qr ≤ z ^ 7 / 2 * z := mul_le_mul_of_nonneg_left hQz (by positivity)
    have e : z ^ 7 / 2 * z = z ^ 8 / 2 := by ring
    linarith
  have hz6 : (4 : ℝ) ^ 6 ≤ z ^ 6 := pow_le_pow_left₀ (by norm_num) hz4 6
  have h2 : 4 * z ^ 6 ≤ z ^ 7 := by
    have e : z ^ 7 = z ^ 6 * z := by ring
    rw [e]
    nlinarith [pow_pos hz0 6]
  norm_num at hz6
  linarith

lemma big_prime_arith (l q ℓ : ℝ) (hl1 : 1 ≤ l) (hq0 : 0 ≤ q) (hql : q ≤ l)
    (hℓ : 20 * l ^ 4 ≤ ℓ) : (2 * Real.pi * q) ^ 2 ≤ 2 / l ^ 2 * ℓ := by
  have hpi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hl2 : 0 < l ^ 2 := by positivity
  have h1 : (2 * Real.pi * q) ^ 2 ≤ 40 * q ^ 2 := by
    have : Real.pi ^ 2 ≤ 10 := by nlinarith
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    nlinarith
  have h2 : q ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hq0 hql 2
  have h3 : 40 * l ^ 2 ≤ 2 / l ^ 2 * ℓ := by
    have : 2 / l ^ 2 * (20 * l ^ 4) = 40 * l ^ 2 := by
      field_simp
      ring
    have h4 : 2 / l ^ 2 * (20 * l ^ 4) ≤ 2 / l ^ 2 * ℓ :=
      mul_le_mul_of_nonneg_left hℓ (by positivity)
    linarith
  linarith

lemma count_pieces (u t l R y0 : ℝ) (q Mp Pc : ℕ) (hq : 1 ≤ q) (hu0 : 0 < u) (ht0 : 0 < t)
    (hexpl : Real.exp l = u) (hR : R = Real.exp (t / u ^ 2)) (hy0 : y0 = Real.exp (t / 16))
    (hR2 : 2 ≤ R) (hMp : (Mp : ℝ) ≤ u ^ 2 / 16) (hPc : (Pc : ℝ) ≤ R + 1)
    (h16 : 16 * (q : ℝ) ≤ u) (hul : u ^ 2 * l ≤ t) (h20 : 20 * u ^ 2 ≤ t / 16) (hl0 : 0 ≤ l)
    (hu160 : 160 ≤ 10 * u ^ 2) :
    160 * (((Mp : ℝ) + 1) * ((((Pc : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp)) ≤ y0 ^ 3 := by
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi := Real.pi_pos
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hy1 : 1 ≤ y0 := by
    rw [hy0]
    exact Real.one_le_exp (by positivity)
  have hu2 : 0 < u ^ 2 := by positivity
  have hMp0 : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  -- the three factors
  have ha : 160 * ((Mp : ℝ) + 1) ≤ y0 := by
    have a1 : 160 * ((Mp : ℝ) + 1) ≤ t / 16 := by linarith
    have a2 := Real.add_one_le_exp (t / 16)
    rw [hy0]
    linarith
  have hc : (16 * (q : ℝ)) ^ Mp ≤ y0 := by
    calc (16 * (q : ℝ)) ^ Mp ≤ u ^ Mp := pow_le_pow_left₀ (by positivity) h16 Mp
      _ = Real.exp ((Mp : ℝ) * l) := by rw [← hexpl, Real.exp_nat_mul]
      _ ≤ Real.exp (t / 16) := by
          refine Real.exp_le_exp.mpr ?_
          have : (Mp : ℝ) * l ≤ u ^ 2 / 16 * l := mul_le_mul_of_nonneg_right hMp hl0
          linarith
      _ = y0 := hy0.symm
  have hd : R ^ Mp ≤ y0 := by
    calc R ^ Mp = Real.exp ((Mp : ℝ) * (t / u ^ 2)) := by rw [hR, Real.exp_nat_mul]
      _ ≤ Real.exp (t / 16) := by
          refine Real.exp_le_exp.mpr ?_
          have a1 : (Mp : ℝ) * (t / u ^ 2) ≤ u ^ 2 / 16 * (t / u ^ 2) :=
            mul_le_mul_of_nonneg_right hMp (by positivity)
          have e : u ^ 2 / 16 * (t / u ^ 2) = t / 16 := by field_simp
          linarith
      _ = y0 := hy0.symm
  have hbase : ((Pc : ℝ) + 1) * (2 * Real.pi * q + 1) ≤ (16 * (q : ℝ)) * R := by
    have b1 : (Pc : ℝ) + 1 ≤ 2 * R := by linarith
    have b2 : 2 * Real.pi * q + 1 ≤ 8 * q := by nlinarith
    have b3 : (0 : ℝ) ≤ (Pc : ℝ) + 1 := by positivity
    calc ((Pc : ℝ) + 1) * (2 * Real.pi * q + 1) ≤ (2 * R) * (8 * q) :=
          mul_le_mul b1 b2 (by positivity) (by linarith)
      _ = (16 * (q : ℝ)) * R := by ring
  have hpowbase : (((Pc : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp ≤ (16 * (q : ℝ)) ^ Mp * R ^ Mp := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase Mp
  have hcd : (16 * (q : ℝ)) ^ Mp * R ^ Mp ≤ y0 * y0 :=
    mul_le_mul hc hd (by positivity) (by linarith)
  have h1 : 160 * (((Mp : ℝ) + 1) * ((((Pc : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp))
      = (160 * ((Mp : ℝ) + 1)) * ((((Pc : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp) := by ring
  rw [h1]
  calc (160 * ((Mp : ℝ) + 1)) * ((((Pc : ℝ) + 1) * (2 * Real.pi * q + 1)) ^ Mp)
      ≤ y0 * (y0 * y0) := mul_le_mul ha (hpowbase.trans hcd) (by positivity) (by linarith)
    _ = y0 ^ 3 := by ring

end E69S3

open E69S3

set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1.H2 := by
  classical
  intro q hq
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℝ, L0 = max (6 * 10 ^ 12) (5000 * (q : ℝ)) := ⟨_, rfl⟩
  refine ⟨⌈Real.exp (Real.exp (Real.exp L0))⌉₊, fun x hx => ?_⟩
  intro K H Q b p s
  dsimp only
  intro hK hH hE hpinj hW hQ hWb
  have hxr : Real.exp (Real.exp (Real.exp L0)) ≤ x :=
    (Nat.le_ceil _).trans (by exact_mod_cast hx)
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxr
  have h1 : Real.exp (Real.exp L0) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxr
  have h1pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : Real.exp L0 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le h1pos).mpr h1
  have h2pos : 0 < Real.log (Real.log x) := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : L0 ≤ Real.log (Real.log (Real.log x)) := (Real.le_log_iff_exp_le h2pos).mpr h2
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.log x := ⟨_, rfl⟩
  rw [← ht] at h1 h1pos h2 h2pos h3
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log t := ⟨_, rfl⟩
  rw [← hu] at h2 h2pos h3
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log u := ⟨_, rfl⟩
  rw [← ht, ← hu, ← hl] at hK hH hE
  rw [← ht, ← hu]
  have hlL : L0 ≤ l := by rw [hl]; exact h3
  have hl6 : 6 * 10 ^ 12 ≤ l := by rw [hL0] at hlL; exact (le_max_left _ _).trans hlL
  have hlq : 5000 * (q : ℝ) ≤ l := by rw [hL0] at hlL; exact (le_max_right _ _).trans hlL
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) hl6
  have hl1 : 1 ≤ l := le_trans (by norm_num) hl6
  have hexpl : Real.exp l = u := by rw [hl, Real.exp_log h2pos]
  have hexpu : Real.exp u = t := by rw [hu, Real.exp_log h1pos]
  have hexpt : Real.exp t = x := by rw [ht, Real.exp_log hx0]
  obtain ⟨hu1, ht4, hf3, hf4, hf5, hf6, hf7⟩ := scale2 l u t q hl6 hlq hexpl hexpu
  have hu0 : 0 < u := by linarith
  have hubig : (6 * 10 ^ 12 : ℝ) ≤ u := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht4
  have hqR1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hql : (q : ℝ) ≤ l := by linarith
  have hhalf : Real.exp (l / 2) ≤ u := by
    rw [← hexpl]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Real.exp (l ^ 3)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hK0, hF1, hF2, hMP, h2D, hQb⟩ := numeric3 l hl6 K H M hK hH hM
  have hp' : ∀ E ∈ (Finset.range K).powerset,
      (p E).Prime ∧ p E ≤ M ∧ |s E| ≤ 8 * (K : ℤ) ^ 2 * (p E : ℤ) := by
    intro E hE'
    obtain ⟨e1, _, e3, e4, _⟩ := hE E hE'
    refine ⟨e1, ?_, e4⟩
    rw [hM]
    exact Nat.le_floor e3
  obtain ⟨hrabs, hdist, hQ0, hQle, hprime⟩ := adm_bounds K H Q M _ p s hK0 hp' rfl hW hQ
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.exp (t / 8) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hz]; exact Real.exp_pos _
  have hz8 : z ^ 8 = x := by
    rw [hz, ← Real.exp_nat_mul, ← hexpt]
    congr 1
    push_cast
    ring
  have hBz : Real.exp (Real.exp (l / 2)) ≤ z := by
    rw [hz]
    refine Real.exp_le_exp.mpr ?_
    have : u ≤ t / 8 := by
      have := Real.quadratic_le_exp_of_nonneg (x := u) (by linarith)
      rw [hexpu] at this
      nlinarith
    linarith
  have hzl : l / 2 + 2 ≤ z := by
    have a1 := Real.add_one_le_exp (Real.exp (l / 2))
    have a2 := Real.add_one_le_exp (l / 2)
    linarith
  have hz4 : 4 ≤ z := by linarith
  have hQz : (Q : ℝ) ≤ z := (Nat.cast_le.mpr hQle).trans (hQb.trans hBz)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDz : ((2 * ((K + H + 8 * K ^ 2) * M) : ℕ) : ℝ) ≤ z := h2D.trans hBz
  have hxz : (x : ℝ) = z ^ 8 := hz8.symm
  have hMD : M ≤ 2 * ((K + H + 8 * K ^ 2) * M) := by
    have : M ≤ (K + H + 8 * K ^ 2) * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hNcard : z ^ 6 ≤ (((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card : ℝ) := by
    have hap := ap_count (x / 2) x Q b hQ0 (by omega)
    rw [abs_le] at hap
    have hhalf' : ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
      have : 2 * (x / 2) ≤ x := Nat.mul_div_le x 2
      have : (2 : ℝ) * ((x / 2 : ℕ) : ℝ) ≤ x := by exact_mod_cast this
      linarith
    have hnum : (x : ℝ) / 2 ≤ (x : ℝ) + 1 - ((x / 2 : ℕ) : ℝ) := by linarith
    have hnum' : z ^ 8 / 2 ≤ (x : ℝ) + 1 - ((x / 2 : ℕ) : ℝ) := by
      rw [← hxz]
      exact hnum
    exact arith_N z _ ((x : ℝ) + 1 - ((x / 2 : ℕ) : ℝ)) Q hz4 hQR hQz (by linarith [hap.1]) hnum'
  have hNne : ((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).Nonempty := by
    refine Finset.card_pos.mp ?_
    have : (0 : ℝ) < (((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card : ℝ) :=
      lt_of_lt_of_le (by positivity) hNcard
    exact_mod_cast this
  -- the threshold R
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (x : ℝ) ^ (1 / u ^ 2) := ⟨_, rfl⟩
  rw [← hRdef]
  have hRexp : R = Real.exp (t / u ^ 2) := by
    rw [hRdef, Real.rpow_def_of_pos hx0, ← ht]
    congr 1
    ring
  have hu3 : u ^ 3 < t := by
    have : u ^ 3 * 24 < u ^ 4 := by nlinarith [pow_pos hu0 3]
    linarith
  have hBR : Real.exp (Real.exp (l / 2)) < R := by
    rw [hRexp]
    refine Real.exp_lt_exp.mpr ?_
    have : u < t / u ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      calc u * u ^ 2 = u ^ 3 := by ring
        _ < t := hu3
    linarith
  have hR2 : 2 ≤ R := by
    have a1 := Real.add_one_le_exp (Real.exp (l / 2))
    have a2 := Real.add_one_le_exp (l / 2)
    linarith
  have hR0 : 0 ≤ R := by linarith
  have hlogR : Real.log R = t / u ^ 2 := by rw [hRexp, Real.log_exp]
  obtain ⟨w0, w1, w2⟩ := weights K H hK0
  -- positivity of n + r
  have hpos : ∀ n ∈ (Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q),
      ∀ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      (n : ℤ) + ((p a.1 : ℤ) * (a.2 : ℤ) - s a.1) ≠ 0 := by
    intro n hn a ha
    have hnI := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn2 : x ≤ 2 * n + 1 := by omega
    have hn2R : (x : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hn2
    have hra := hrabs a ha
    have hD : (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) < n := by
      have e : ((2 * ((K + H + 8 * K ^ 2) * M) : ℕ) : ℝ)
          = 2 * (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) := by push_cast; ring
      rw [e] at hDz
      have hz7 : (4 : ℝ) ^ 7 ≤ z ^ 7 := pow_le_pow_left₀ (by norm_num) hz4 7
      have hz8' : (4 : ℝ) ^ 7 * z ≤ z ^ 8 := by
        have e8 : z ^ 8 = z ^ 7 * z := by ring
        rw [e8]
        exact mul_le_mul_of_nonneg_right hz7 hz0.le
      have hDn0 : (0 : ℝ) ≤ (((K + H + 8 * K ^ 2) * M : ℕ) : ℝ) := Nat.cast_nonneg _
      norm_num at hz8'
      linarith
    have hD' : (((K + H + 8 * K ^ 2) * M : ℕ) : ℤ) < n := by exact_mod_cast hD
    have := abs_le.mp hra
    intro h0
    linarith [this.1]
  -- parameters
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℕ, Mp = ⌊u ^ 2 / 16⌋₊ := ⟨_, rfl⟩
  have hMple : (Mp : ℝ) ≤ u ^ 2 / 16 := by
    rw [hMp]
    exact Nat.floor_le (by positivity)
  have hMplt : u ^ 2 / 16 < Mp + 1 := by
    rw [hMp]
    exact Nat.lt_floor_add_one _
  have hMp7 : 7 ≤ Mp := by
    rw [hMp]
    refine Nat.le_floor ?_
    have : u ≤ u ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    push_cast
    linarith
  obtain ⟨ja, hja⟩ : ∃ ja : ℕ, ja = ⌈Real.exp (l / 2) / Real.log 2⌉₊ + 20 := ⟨_, rfl⟩
  obtain ⟨jb, hjb⟩ : ∃ jb : ℕ, jb = ⌊t / (u ^ 2 * Real.log 2)⌋₊ := ⟨_, rfl⟩
  obtain ⟨hja1, hjb1, hjab, hja20, hlogratio⟩ :=
    ja_jb l u t ja jb hl6 hexpl hexpu hu1 ht4 hf5 hja hjb
  have hH0 : 0 < H := by
    rw [hH]
    exact Nat.floor_pos.mpr (one_le_pow₀ hl1)
  have hq2K : (q : ℝ) ≤ 2 ^ K := by
    have e : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by ring
    rw [e] at hF2
    have h2l : 2 * l ≤ l * l := mul_le_mul_of_nonneg_right (by linarith) hl0.le
    have hsq : l ^ 2 = l * l := sq l
    linarith
  have hre := re_bound K H hH0 (q : ℝ) (Nat.cast_nonneg q) hq2K
  have hre' : ∑ a ∈ (Finset.range K).powerset ×ˢ Finset.Ico (K + 1) (K + H + 1),
      (Real.cos (2 * Real.pi * ((q : ℝ) * ((-1 : ℝ) ^ a.1.card / 2 ^ a.2))) - 1)
      ≤ -(2 / l ^ 2) := by
    refine hre.trans ?_
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    have a1 : 2 / l ^ 2 ≤ 2 / (2 : ℝ) ^ K := div_le_div_of_nonneg_left (by norm_num) h2K hF1
    have a2 : 2 / (2 : ℝ) ^ K ≤ 2 * (q : ℝ) ^ 2 / 2 ^ K := by
      refine div_le_div_of_nonneg_right ?_ h2K.le
      have : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hqR1
      linarith
    linarith
  -- the set of primes for the decay
  have h2jaR : ((2 * ((K + H + 8 * K ^ 2) * M) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ja := h2D.trans hja1
  have h2jaN : 2 * ((K + H + 8 * K ^ 2) * M) ≤ 2 ^ ja := by exact_mod_cast h2jaR
  have hjaI : ja + 2 * ((jb - ja) / 2) ≤ jb := by omega
  have h2jbR : (2 : ℝ) ^ jb ≤ R := by rw [hRexp]; exact hjb1
  have hP' : (Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * ((jb - ja) / 2)))).filter Nat.Prime
      ⊆ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter (fun ℓ => Nat.Coprime Q ℓ) := by
    intro ℓ hℓ
    obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨b1, b2⟩ := Finset.mem_Ioc.mp a1
    have c1 : ℓ ≤ 2 ^ jb := b2.trans (Nat.pow_le_pow_right (by norm_num) hjaI)
    have c2 : (ℓ : ℝ) ≤ R := by
      have : (ℓ : ℝ) ≤ ((2 ^ jb : ℕ) : ℝ) := by exact_mod_cast c1
      push_cast at this
      linarith
    have c3 : ℓ ≤ ⌊R⌋₊ := Nat.le_floor c2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), a2⟩, ?_⟩
    exact (hprime ℓ a2 (by omega) (by omega)).1
  have hbig : ∀ ℓ ∈ (Finset.Ioc (2 ^ ja) (2 ^ (ja + 2 * ((jb - ja) / 2)))).filter Nat.Prime,
      (2 * Real.pi * (q : ℝ)) ^ 2 ≤ 2 / l ^ 2 * ℓ := by
    intro ℓ hℓ
    obtain ⟨a1, _⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨b1, _⟩ := Finset.mem_Ioc.mp a1
    have c1 : (2 : ℝ) ^ ja ≤ ℓ := by
      have : ((2 ^ ja : ℕ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast b1.le
      push_cast at this
      exact this
    have c2 := exp_half_big l hl6
    have c3 := Real.add_one_le_exp (Real.exp (l / 2))
    have c4 : l ^ 4 ≤ l ^ 11 := pow_le_pow_right₀ hl1 (by norm_num)
    have c5 : 20 * l ^ 4 ≤ 3 * l ^ 11 := by
      have : l ^ 11 = l ^ 4 * l ^ 7 := by ring
      have h7 : (7 : ℝ) ≤ l ^ 7 := le_trans (by linarith) (le_self_pow₀ hl1 (by norm_num))
      have h4 : 0 ≤ l ^ 4 := by positivity
      have h47 := mul_le_mul_of_nonneg_left h7 h4
      linarith
    exact big_prime_arith l q ℓ hl1 (Nat.cast_nonneg q) hql (by linarith)
  have hprod : 8 ≤ 2 / l ^ 2 * ∑ ℓ ∈ (Finset.Ioc (2 ^ ja)
      (2 ^ (ja + 2 * ((jb - ja) / 2)))).filter Nat.Prime, (1 : ℝ) / ℓ := by
    have hlow := prime_recip_lower ja hja20 ((jb - ja) / 2)
    have hl2 : 0 < l ^ 2 := by positivity
    have h4 : 4 * l ^ 2 ≤ ∑ ℓ ∈ (Finset.Ioc (2 ^ ja)
        (2 ^ (ja + 2 * ((jb - ja) / 2)))).filter Nat.Prime, (1 : ℝ) / ℓ := by linarith
    have h5 : 2 / l ^ 2 * (4 * l ^ 2) = 8 := by
      field_simp
      norm_num
    have h6 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 / l ^ 2 by positivity)
    linarith
  -- the reciprocal sum over all primes up to R
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' := Real.log_two_gt_d9
  have hL : ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
      (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ ≤ 4 * (1 + u) := by
    have hsubT : ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ
        ≤ ∑ ℓ ∈ (Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / ℓ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    obtain ⟨j1, hj1⟩ : ∃ j1 : ℕ, j1 = Nat.log 2 ⌊R⌋₊ := ⟨_, rfl⟩
    have hfR : 2 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hR2)
    have hj11 : 1 ≤ j1 := by
      rw [hj1]
      exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    have hprop : ∀ ℓ ∈ (Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime,
        ℓ.Prime ∧ 2 ^ 1 ≤ ℓ ∧ ℓ < 2 ^ (j1 + 1) := by
      intro ℓ hℓ
      obtain ⟨a1, a2⟩ := Finset.mem_filter.mp hℓ
      have a3 := Finset.mem_range.mp a1
      have a4 : ⌊R⌋₊ < 2 ^ (j1 + 1) := by
        rw [hj1]
        exact Nat.lt_pow_succ_log_self (by norm_num) _
      exact ⟨a2, a2.two_le, by omega⟩
    have hsum := prime_recip_sum _ 1 j1 (le_refl 1) hj11 hprop
    have hj1t : (j1 : ℝ) ≤ t := by
      have c1 : 2 ^ j1 ≤ ⌊R⌋₊ := by
        rw [hj1]
        exact Nat.pow_log_le_self 2 (by omega)
      have c2 : (2 : ℝ) ^ j1 ≤ R := by
        have c3 : ((2 ^ j1 : ℕ) : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast c1
        have c4 := Nat.floor_le hR0
        push_cast at c3
        linarith
      have c5 := Real.log_le_log (by positivity) c2
      rw [Real.log_pow, hlogR] at c5
      have hu2 : (2 : ℝ) ≤ u ^ 2 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
      have c6 : t / u ^ 2 ≤ t / 2 := div_le_div_of_nonneg_left ht0.le (by norm_num) hu2
      have hj0 : (0 : ℝ) ≤ j1 := Nat.cast_nonneg _
      have c7 : (j1 : ℝ) * (1 / 2) ≤ (j1 : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hj0
      linarith
    have hj1pos : (0 : ℝ) < j1 := by exact_mod_cast hj11
    have hlogj : Real.log (j1 : ℝ) ≤ u := by
      rw [hu]
      exact Real.log_le_log hj1pos hj1t
    simp only [Nat.cast_one, Real.log_one, sub_zero] at hsum
    linarith
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi := Real.pi_pos
  have hfact : 6 * (2 * Real.pi * (q : ℝ) * ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter
      Nat.Prime).filter (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ) ≤ Mp := by
    have hS0 : 0 ≤ ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ := Finset.sum_nonneg fun _ _ => by positivity
    have a1 : 2 * Real.pi * (q : ℝ) * ∑ ℓ ∈ ((Finset.range (⌊R⌋₊ + 1)).filter
        Nat.Prime).filter (fun ℓ => Nat.Coprime Q ℓ), (1 : ℝ) / ℓ
        ≤ 2 * 3.15 * (q : ℝ) * (4 * (1 + u)) := by
      have b1 : 2 * Real.pi * (q : ℝ) ≤ 2 * 3.15 * (q : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg q)
      exact mul_le_mul b1 hL hS0 (by positivity)
    have a2 : 6 * (2 * 3.15 * (q : ℝ) * (4 * (1 + u))) ≤ 152 * (q : ℝ) * (1 + u) := by
      have h0 : (0 : ℝ) ≤ (q : ℝ) * (1 + u) := by positivity
      have e1 : 6 * (2 * 3.15 * (q : ℝ) * (4 * (1 + u))) = 151.2 * ((q : ℝ) * (1 + u)) := by ring
      have e2 : 152 * (q : ℝ) * (1 + u) = 152 * ((q : ℝ) * (1 + u)) := by ring
      rw [e1, e2]
      linarith
    linarith
  -- the counting error
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℝ, y0 = Real.exp (t / 16) := ⟨_, rfl⟩
  have hy12 : y0 ^ 12 = z ^ 6 := by
    rw [hy0, hz, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hy1 : 1 ≤ y0 := by
    rw [hy0]
    exact Real.one_le_exp (by positivity)
  have hPc : ((((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
      (fun ℓ => Nat.Coprime Q ℓ)).card : ℝ) ≤ R + 1 := by
    have c1 : (((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ)).card ≤ ⌊R⌋₊ + 1 := by
      refine (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans ?_)
      rw [Finset.card_range]
    have c2 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
    have c3 : ((((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ)).card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast c1
    linarith
  have hcount : 160 * (((Mp : ℝ) + 1) * (((((Finset.range (⌊R⌋₊ + 1)).filter Nat.Prime).filter
        (fun ℓ => Nat.Coprime Q ℓ)).card + 1 : ℝ) * (2 * Real.pi * (q : ℝ) + 1)) ^ Mp)
      ≤ (((Finset.Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card : ℝ) := by
    have h := count_pieces u t l R y0 q Mp _ hq hu0 ht0 hexpl hRexp hy0 hR2 hMple hPc hf6 hf4 hf7
      hl0.le (by
        have : u ≤ u ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
        linarith)
    have h3 : y0 ^ 3 ≤ y0 ^ 12 := pow_le_pow_right₀ hy1 (by norm_num)
    linarith
  exact h2_main (x / 2) x Q b hQ0 (by omega) _
    (fun a => (p a.1 : ℤ) * (a.2 : ℤ) - s a.1) (fun a => (-1 : ℝ) ^ a.1.card / 2 ^ a.2)
    (q : ℝ) R (2 / l ^ 2) (Nat.cast_nonneg q) hR0 (by positivity) Mp hMp7 _ hNne hpos
    (fun ℓ hℓ hco => sep_of_coprime K H Q _ p s rfl hW hQ ℓ hℓ hco) w1 hre' hP' hbig hprod hfact
    hcount
