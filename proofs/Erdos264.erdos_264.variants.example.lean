import FormalConjectures.ErdosProblems.«264»

-- Problem: Erdős Problem 264 — example
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/264.lean:68 (declaration Erdos264.erdos_264.variants.example)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA264

noncomputable def A (n : ℕ) : ℝ := (2 : ℝ) ^ (2 ^ n)

lemma A_succ (n : ℕ) : A (n + 1) = A n ^ 2 := by
  unfold A; rw [pow_succ, pow_mul]

lemma A_ge_two (n : ℕ) : 2 ≤ A n := by
  unfold A
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ n) := pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow

lemma A_pos (n : ℕ) : 0 < A n := by linarith [A_ge_two n]

lemma A_add (N k : ℕ) : A N * 2 ^ k ≤ A (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, A_succ, pow_succ]
    have h2 := A_ge_two (N + k)
    nlinarith [A_pos (N + k)]

lemma A_ge_lin (n : ℕ) : 2 * (n : ℝ) ≤ A n := by
  have h := A_add 0 n
  have h0 : A 0 = 2 := by simp [A]
  rw [h0, zero_add] at h
  have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  linarith

lemma prod_A (N : ℕ) : ∏ n ∈ Finset.range N, A n = A N / 2 := by
  induction N with
  | zero => simp [A]
  | succ N ih => rw [Finset.prod_range_succ, ih, A_succ]; ring

lemma sq_le_two_pow (N : ℕ) (h : 4 ≤ N) : N * N ≤ 2 ^ N := by
  induction N, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; nlinarith

lemma growth (K R : ℕ) : ∃ N0, ∀ N ≥ N0, K * R ^ N ≤ 2 ^ (2 ^ N) := by
  refine ⟨K + R + 4, fun N hN => ?_⟩
  have h1 : K ≤ 2 ^ N := le_trans (by omega) (Nat.lt_two_pow_self).le
  have h2 : R ^ N ≤ (2 ^ R) ^ N := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le N
  have h3 : N * N ≤ 2 ^ N := sq_le_two_pow N (by omega)
  calc K * R ^ N ≤ 2 ^ N * (2 ^ R) ^ N := Nat.mul_le_mul h1 h2
    _ = 2 ^ (N + R * N) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (N * N) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ ≤ 2 ^ (2 ^ N) := Nat.pow_le_pow_right (by norm_num) h3

def cZ (b : ℕ → ℤ) (n : ℕ) : ℤ := 2 ^ (2 ^ n) + b n

def D (b : ℕ → ℤ) (N : ℕ) : ℤ := ∏ n ∈ Finset.range N, cZ b n

def P (b : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | N + 1 => cZ b N * P b N + D b N

lemma cZ_cast (b : ℕ → ℤ) (n : ℕ) : (cZ b n : ℝ) = A n + b n := by
  simp [cZ, A]

lemma P_cast (b : ℕ → ℤ) (hc : ∀ n, cZ b n ≠ 0) (N : ℕ) :
    (P b N : ℝ) = D b N * ∑ n ∈ Finset.range N, 1 / (cZ b n : ℝ) := by
  induction N with
  | zero => simp [P]
  | succ N ih =>
    have hN : (cZ b N : ℝ) ≠ 0 := by exact_mod_cast hc N
    simp only [P, D, Finset.prod_range_succ, Finset.sum_range_succ, Int.cast_add, Int.cast_mul,
      Int.cast_prod] at ih ⊢
    rw [ih]
    field_simp

lemma x_bound (B : ℕ) (Av c0 c1 b0 b1 t : ℝ) (hA : 2 ≤ Av) (hAB : 2 * (B : ℝ) ≤ Av)
    (h0 : c0 = Av + b0) (h1 : c1 = Av ^ 2 + b1) (hb0 : |b0| ≤ B) (hb1 : |b1| ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 4 / Av ^ 4) :
    |(c0 - 1) * (1 / c0 + 1 / c1 + t) - 1| ≤ (16 * ((B : ℝ) + 1) ^ 2 + 8) / Av ^ 2 := by
  obtain ⟨hb0l, hb0u⟩ := abs_le.mp hb0
  obtain ⟨hb1l, hb1u⟩ := abs_le.mp hb1
  have hApos : 0 < Av := by linarith
  have hc0 : Av / 2 ≤ c0 := by rw [h0]; linarith
  have hAsq : 2 * Av ≤ Av ^ 2 := by nlinarith
  have hc1 : Av ^ 2 / 2 ≤ c1 := by rw [h1]; nlinarith
  have hc0p : 0 < c0 := by linarith
  have hc1p : 0 < c1 := by nlinarith
  have hsplit : (c0 - 1) * (1 / c0 + 1 / c1 + t) - 1
      = (c0 ^ 2 - c0 - c1) / (c0 * c1) + (c0 - 1) * t := by
    field_simp; ring
  rw [hsplit]
  have hnum : |c0 ^ 2 - c0 - c1| ≤ 4 * ((B : ℝ) + 1) ^ 2 * Av := by
    rw [h0, h1, abs_le]
    have e : (Av + b0) ^ 2 - (Av + b0) - (Av ^ 2 + b1) = 2 * Av * b0 + b0 ^ 2 - Av - b0 - b1 := by
      ring
    rw [e]
    have hBn : (0 : ℝ) ≤ B := by positivity
    have q1 : Av * b0 ≤ Av * B := by nlinarith
    have q2 : -(Av * B) ≤ Av * b0 := by nlinarith
    have q3 : b0 ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
    have q4 : (B : ℝ) ≤ B * Av := by nlinarith
    have q5 : (B : ℝ) ^ 2 ≤ B ^ 2 * Av := by nlinarith
    constructor <;> nlinarith [sq_nonneg (b0 : ℝ)]
  have hden : Av ^ 3 / 4 ≤ c0 * c1 := by
    have := mul_le_mul hc0 hc1 (by positivity) hc0p.le
    nlinarith
  have hterm1 : |(c0 ^ 2 - c0 - c1) / (c0 * c1)| ≤ 16 * ((B : ℝ) + 1) ^ 2 / Av ^ 2 := by
    rw [abs_div, abs_of_pos (mul_pos hc0p hc1p), div_le_div_iff₀ (mul_pos hc0p hc1p) (by positivity)]
    have hB2 : (0 : ℝ) ≤ 4 * ((B : ℝ) + 1) ^ 2 * Av := by positivity
    calc |c0 ^ 2 - c0 - c1| * Av ^ 2 ≤ 4 * ((B : ℝ) + 1) ^ 2 * Av * Av ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = 16 * ((B : ℝ) + 1) ^ 2 * (Av ^ 3 / 4) := by ring
      _ ≤ 16 * ((B : ℝ) + 1) ^ 2 * (c0 * c1) := mul_le_mul_of_nonneg_left hden (by positivity)
  have hc0le : c0 ≤ 2 * Av := by rw [h0]; linarith
  have hterm2 : |(c0 - 1) * t| ≤ 8 / Av ^ 2 := by
    have hc01 : 0 ≤ c0 - 1 := by linarith
    rw [abs_of_nonneg (mul_nonneg hc01 ht0)]
    have h4 : 4 / Av ^ 4 * (2 * Av) ≤ 8 / Av ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 8 * Av ^ 2 ≤ 8 * Av ^ 3 := by nlinarith
      nlinarith
    calc (c0 - 1) * t ≤ (2 * Av) * (4 / Av ^ 4) := mul_le_mul (by linarith) ht1 ht0 (by linarith)
      _ = 4 / Av ^ 4 * (2 * Av) := by ring
      _ ≤ 8 / Av ^ 2 := h4
  calc |(c0 ^ 2 - c0 - c1) / (c0 * c1) + (c0 - 1) * t|
      ≤ |(c0 ^ 2 - c0 - c1) / (c0 * c1)| + |(c0 - 1) * t| := abs_add_le _ _
    _ ≤ 16 * ((B : ℝ) + 1) ^ 2 / Av ^ 2 + 8 / Av ^ 2 := add_le_add hterm1 hterm2
    _ = (16 * ((B : ℝ) + 1) ^ 2 + 8) / Av ^ 2 := by ring

theorem main (b : ℕ → ℤ) (hbu : BddAbove (Set.range b)) (hbl : BddBelow (Set.range b))
    (hc : ∀ n, cZ b n ≠ 0) : Irrational (∑' n, 1 / (A n + b n)) := by
  obtain ⟨Bu, hBu⟩ := hbu
  obtain ⟨Bl, hBl⟩ := hbl
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ n, |(b n : ℝ)| ≤ B := by
    refine ⟨(max Bu (-Bl)).toNat, fun n => ?_⟩
    have h1 : b n ≤ Bu := hBu ⟨n, rfl⟩
    have h2 : Bl ≤ b n := hBl ⟨n, rfl⟩
    have hm : max Bu (-Bl) ≤ ((max Bu (-Bl)).toNat : ℤ) := Int.self_le_toNat _
    have : |b n| ≤ ((max Bu (-Bl)).toNat : ℤ) :=
      abs_le.mpr ⟨by linarith [le_max_right Bu (-Bl)], by linarith [le_max_left Bu (-Bl)]⟩
    exact_mod_cast this
  set f : ℕ → ℝ := fun n => 1 / (A n + b n) with hf
  have hcR : ∀ n, A n + b n = (cZ b n : ℝ) := fun n => (cZ_cast b n).symm
  have hcne : ∀ n, A n + b n ≠ 0 := fun n => by rw [hcR]; exact_mod_cast hc n
  -- large indices
  have hlarge : ∀ n, B ≤ n → A n / 2 ≤ A n + b n := by
    intro n hn
    have := A_ge_lin n
    have hb := (abs_le.mp (hB n)).1
    have : (B : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfpos : ∀ n, B ≤ n → 0 < f n := by
    intro n hn
    have := hlarge n hn
    have := A_pos n
    simp only [hf]; apply div_pos one_pos; linarith
  have hfle : ∀ N, B ≤ N → ∀ k, f (k + N) ≤ (2 / A N) * (1 / 2) ^ k := by
    intro N hN k
    have h1 := hlarge (k + N) (by omega)
    have h2 := A_add N k
    have h3 := A_pos N
    have h4 := A_pos (k + N)
    rw [add_comm k N] at h1 h4 ⊢
    simp only [hf]
    rw [div_le_iff₀ (by linarith)]
    have : (2 / A N) * (1 / 2) ^ k * (A N * 2 ^ k) = 2 := by
      have e : ((1:ℝ) / 2) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
      rw [show (2 / A N) * (1 / 2) ^ k * (A N * 2 ^ k) = 2 * ((1 / 2) ^ k * 2 ^ k) * (A N / A N) by
        ring, e, div_self h3.ne']
      ring
    have h5 : 0 ≤ (2 / A N) * (1 / 2) ^ k := by positivity
    nlinarith
  have hsumN : ∀ N, B ≤ N → Summable (fun k => f (k + N)) := by
    intro N hN
    refine Summable.of_nonneg_of_le (fun k => (hfpos (k + N) (by omega)).le) (hfle N hN) ?_
    exact (summable_geometric_two).mul_left _
  have hsum : Summable f := (summable_nat_add_iff B).mp (hsumN B le_rfl)
  have hsumall : ∀ N, Summable (fun k => f (k + N)) := fun N => (summable_nat_add_iff N).mpr hsum
  set T : ℕ → ℝ := fun N => ∑' k, f (k + N) with hT
  have hTrec : ∀ N, T N = f N + T (N + 1) := by
    intro N
    simp only [hT]
    rw [(hsumall N).tsum_eq_zero_add, zero_add]
    congr 1
    apply tsum_congr; intro k; congr 1; ring
  have hTnn : ∀ N, B ≤ N → 0 ≤ T N := by
    intro N hN
    exact tsum_nonneg (fun k => (hfpos (k + N) (by omega)).le)
  have hTle : ∀ N, B ≤ N → T N ≤ 4 / A N := by
    intro N hN
    have := Summable.tsum_le_tsum (hfle N hN) (hsumall N) ((summable_geometric_two).mul_left _)
    rw [tsum_mul_left, tsum_geometric_two] at this
    have e : 2 / A N * 2 = 4 / A N := by ring
    simp only [hT]; linarith
  have hS : ∀ N, ∑' n, f n = ∑ n ∈ Finset.range N, f n + T N := by
    intro N
    induction N with
    | zero => simp [hT]
    | succ N ih => rw [ih, Finset.sum_range_succ, hTrec N]; ring
  -- rationality
  intro hrat
  obtain ⟨q, hq⟩ := hrat
  set p := q.num
  set d := q.den
  have hd : (0 : ℝ) < d := by exact_mod_cast q.den_pos
  have hqpd : (q : ℝ) = p / d := by rw [Rat.cast_def]
  have hDne : ∀ N, D b N ≠ 0 := by
    intro N; simp only [D]; exact Finset.prod_ne_zero_iff.mpr (fun n _ => hc n)
  set I : ℕ → ℤ := fun N => p * D b N - d * P b N with hI
  have hIreal : ∀ N, (I N : ℝ) = d * D b N * T N := by
    intro N
    have h1 := hS N
    rw [← hq, hqpd] at h1
    have h2 := P_cast b hc N
    have hsum' : ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range N, 1 / (cZ b n : ℝ) := by
      apply Finset.sum_congr rfl; intro n _; simp only [hf, hcR]
    simp only [hI, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [h2, ← hsum']
    have : T N = p / d - ∑ n ∈ Finset.range N, f n := by linarith
    rw [this]; field_simp
  have hIrec : ∀ N, I (N + 1) = cZ b N * I N - d * D b N := by
    intro N; simp only [hI, P, D, Finset.prod_range_succ]; ring
  have hDabs : ∀ N, |(D b N : ℝ)| ≤ ((B : ℝ) + 1) ^ N * (A N / 2) := by
    intro N
    simp only [D, Int.cast_prod, Finset.abs_prod]
    have hpc : ((B : ℝ) + 1) ^ N = ∏ _n ∈ Finset.range N, ((B : ℝ) + 1) := by simp
    rw [← prod_A N, hpc, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun n _ => abs_nonneg _)
    intro n _
    rw [cZ_cast]
    have := A_ge_two n
    have hb := hB n
    calc |A n + b n| ≤ |A n| + |(b n : ℝ)| := abs_add_le _ _
      _ ≤ A n + B := by rw [abs_of_pos (A_pos n)]; linarith
      _ ≤ ((B : ℝ) + 1) * A n := by nlinarith
  -- growth threshold
  set M : ℝ := 16 * ((B : ℝ) + 1) ^ 2 + 8 with hM
  obtain ⟨N0, hN0⟩ := growth (d * (16 * (B + 1) ^ 2 + 8)) (B + 1)
  have hgrowth : ∀ N ≥ N0, (d : ℝ) * M * ((B : ℝ) + 1) ^ N ≤ A N := by
    intro N hN
    have := hN0 N hN
    have : ((d * (16 * (B + 1) ^ 2 + 8) * (B + 1) ^ N : ℕ) : ℝ) ≤ ((2 ^ (2 ^ N) : ℕ) : ℝ) := by
      exact_mod_cast this
    simp only [hM, A]; push_cast at this; linarith
  set N1 := N0 + B + 1 with hN1
  -- key step: for N ≥ N1, (c N - 1) T N = 1
  have hkey : ∀ N, N1 ≤ N → (A N + b N - 1) * T N = 1 := by
    intro N hN
    have hBN : B ≤ N := by omega
    have hx := x_bound B (A N) (A N + b N) (A (N + 1) + b (N + 1)) (b N) (b (N + 1)) (T (N + 2))
      (A_ge_two N) (by have := A_ge_lin N; have : (B : ℝ) ≤ N := by exact_mod_cast hBN
                       linarith)
      rfl (by rw [A_succ]) (hB N) (hB (N + 1)) (hTnn (N + 2) (by omega))
      (by have := hTle (N + 2) (by omega); rw [A_succ, A_succ] at this
          calc T (N + 2) ≤ 4 / ((A N ^ 2) ^ 2) := this
            _ = 4 / A N ^ 4 := by ring)
    have hTN : T N = 1 / (A N + b N) + 1 / (A (N + 1) + b (N + 1)) + T (N + 2) := by
      rw [hTrec N, hTrec (N + 1)]; simp only [hf]; ring
    rw [← hTN] at hx
    -- difference of I
    have hdiff : ((I (N + 1) - I N : ℤ) : ℝ) = d * D b N * ((A N + b N - 1) * T N - 1) := by
      rw [hIrec N]; push_cast; rw [hIreal N, cZ_cast]; ring
    have hlt : |((I (N + 1) - I N : ℤ) : ℝ)| < 1 := by
      rw [hdiff, abs_mul, abs_mul, abs_of_pos hd]
      have hg := hgrowth N (by omega)
      have hAp := A_pos N
      have hDa := hDabs N
      have hxa : 0 ≤ |(A N + b N - 1) * T N - 1| := abs_nonneg _
      calc (d : ℝ) * |(D b N : ℝ)| * |(A N + b N - 1) * T N - 1|
          ≤ d * (((B : ℝ) + 1) ^ N * (A N / 2)) * (M / A N ^ 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hDa hd.le) hx hxa (by positivity)
        _ = (d * M * ((B : ℝ) + 1) ^ N) / A N / 2 := by field_simp
        _ ≤ A N / A N / 2 := by gcongr
        _ < 1 := by rw [div_self hAp.ne']; norm_num
    have hz : I (N + 1) - I N = 0 := by
      have h' : |I (N + 1) - I N| < 1 := by
        have : ((|I (N + 1) - I N| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; simpa using hlt
        exact_mod_cast this
      rw [abs_lt] at h'; omega
    have : (d : ℝ) * D b N * ((A N + b N - 1) * T N - 1) = 0 := by
      rw [← hdiff, hz]; simp
    have hdD : (d : ℝ) * D b N ≠ 0 := mul_ne_zero hd.ne' (by exact_mod_cast hDne N)
    have := (mul_eq_zero.mp this).resolve_left hdD
    linarith
  -- contradiction
  have k0 := hkey N1 le_rfl
  have k1 := hkey (N1 + 1) (by omega)
  have hr := hTrec N1
  have hc0 := hlarge N1 (by omega)
  have hc1 := hlarge (N1 + 1) (by omega)
  have hA4 := A_ge_two N1
  have hA1 : A (N1 + 1) = A N1 ^ 2 := A_succ N1
  have hc0' : A N1 + b N1 - 1 ≠ 0 := by intro h; rw [h] at k0; simp at k0
  have hc1' : A (N1 + 1) + b (N1 + 1) - 1 ≠ 0 := by intro h; rw [h] at k1; simp at k1
  have hcn0 := hcne N1
  have hT0 : T N1 = 1 / (A N1 + b N1 - 1) := by field_simp; linarith
  have hT1 : T (N1 + 1) = 1 / (A (N1 + 1) + b (N1 + 1) - 1) := by field_simp; linarith
  rw [hT0, hT1] at hr
  simp only [hf] at hr
  field_simp at hr
  rw [hA1] at hr
  -- hr : polynomial identity
  have hg := hgrowth N1 (by omega)
  have hpow : (1 : ℝ) ≤ ((B : ℝ) + 1) ^ N1 := one_le_pow₀ (by linarith [(Nat.cast_nonneg B : (0:ℝ) ≤ B)])
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast q.den_pos
  have hMbig : M ≤ A N1 := by
    have : M ≤ (d : ℝ) * M * ((B : ℝ) + 1) ^ N1 := by
      have hM0 : 0 ≤ M := by positivity
      nlinarith [mul_le_mul hd1 hpow zero_le_one (by linarith)]
    linarith
  have hb0 := abs_le.mp (hB N1)
  have hb1 := abs_le.mp (hB (N1 + 1))
  have hBn : (0 : ℝ) ≤ B := by positivity
  have key : A N1 * (2 * b N1 - 1) = b (N1 + 1) - 1 - (b N1) ^ 2 + b N1 := by
    linear_combination -hr
  have hb0sq : ((b N1 : ℝ)) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
  have hMv : M = 16 * ((B : ℝ) + 1) ^ 2 + 8 := hM
  have hApos := A_pos N1
  rcases le_or_gt (b N1) 0 with hneg | hpos
  · have h1 : (b N1 : ℝ) ≤ 0 := by exact_mod_cast hneg
    have h2 : A N1 * (2 * b N1 - 1 + 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hApos.le (by linarith)
    have h3 : A N1 * (2 * b N1 - 1) ≤ - A N1 := by linarith
    have h4 : -((B : ℝ) + 1) ^ 2 ≤ b (N1 + 1) - 1 - (b N1) ^ 2 + b N1 := by
      have : ((B : ℝ) + 1) ^ 2 = B ^ 2 + 2 * B + 1 := by ring
      linarith [hb0.1, hb1.1]
    have : (0 : ℝ) ≤ ((B : ℝ) + 1) ^ 2 := by positivity
    linarith
  · have h1 : (1 : ℝ) ≤ b N1 := by exact_mod_cast hpos
    have h2 : 0 ≤ A N1 * (2 * b N1 - 1 - 1) :=
      mul_nonneg hApos.le (by linarith)
    have h3 : A N1 ≤ A N1 * (2 * b N1 - 1) := by linarith
    have h4 : b (N1 + 1) - 1 - (b N1) ^ 2 + b N1 ≤ ((B : ℝ) + 1) ^ 2 := by
      have : ((B : ℝ) + 1) ^ 2 = B ^ 2 + 2 * B + 1 := by ring
      have : (0 : ℝ) ≤ (b N1) ^ 2 := sq_nonneg _
      linarith [hb0.2, hb1.2]
    have : (0 : ℝ) ≤ ((B : ℝ) + 1) ^ 2 := by positivity
    linarith

end OMA264

theorem OMA.solution : type_of% @Erdos264.erdos_264.variants.example := by
  intro b hbu hbl h0 _
  have hc : ∀ n, OMA264.cZ b n ≠ 0 := by
    intro n h
    apply h0
    exact ⟨n, by simpa [OMA264.cZ] using h⟩
  have := OMA264.main b hbu hbl hc
  simpa [OMA264.A] using this
