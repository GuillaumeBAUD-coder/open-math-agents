import OMAStatements.S_oeis_a023688
import Mathlib

noncomputable section

namespace Proof_oeis_a023688

open PowerSeries

/-! ### Part 1: Binary weight `s2`, Legendre/Kummer 2-adic valuation, and submask parity -/

private abbrev s2 := OMA.S_oeis_a023688.s2

private lemma s2_zero : s2 0 = 0 := rfl

private lemma s2_pos_rec (n : ℕ) (hn : 0 < n) :
    s2 n = (if n % 2 = 1 then 1 else 0) + s2 (n / 2) := by
  unfold s2 OMA.S_oeis_a023688.s2
  rw [Nat.digits_def' (by norm_num : 1 < 2) hn]
  simp only [List.filter_cons]
  by_cases h : n % 2 = 1
  · simp [h]; omega
  · simp [h]

private lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [s2_pos_rec (2 * n) (by omega)]
    have hmod : 2 * n % 2 = 0 := by omega
    have hdiv : 2 * n / 2 = n := by omega
    simp [hmod, hdiv]

private lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  rw [s2_pos_rec (2 * n + 1) (by omega)]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hmod, hdiv]
  omega

private lemma s2_le (n : ℕ) : s2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [s2_zero]
    · rw [s2_pos_rec n hn]
      have h1 := ih (n / 2) (by omega)
      split_ifs <;> omega

private lemma s2_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ s2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [s2_pos_rec n (by omega)]
    split_ifs with h
    · omega
    · have := ih (n / 2) (by omega) (by omega)
      omega

private lemma padicValNat_two_factorial_add_s2 (n : ℕ) :
    padicValNat 2 n.factorial + s2 n = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n with
  | zero => simp [s2_zero]
  | succ n ih =>
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
    -- Prove padicValNat 2 (n + 1) + s2 (n + 1) = s2 n + 1 by strong induction on n
    have hstep : ∀ m : ℕ, padicValNat 2 (m + 1) + s2 (m + 1) = s2 m + 1 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ihm =>
        by_cases hm : m % 2 = 0
        · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
          rw [s2_two_mul_add_one, s2_two_mul]
          have hodd : ¬ (2 ∣ 2 * k + 1) := by omega
          rw [padicValNat.eq_zero_of_not_dvd hodd, zero_add]
        · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
          rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
            padicValNat.mul (by omega) (by omega), padicValNat.self (by norm_num),
            s2_two_mul, s2_two_mul_add_one]
          have := ihm k (by omega)
          omega
    have := hstep n
    omega

private lemma padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 ((2 * n).choose n) = s2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcb : (2 * n).choose n * (n.factorial * n.factorial) = (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    linarith [h]
  have hne1 : (2 * n).choose n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hne2 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hv := congrArg (padicValNat 2) hcb
  rw [padicValNat.mul hne1 (mul_ne_zero hne2 hne2), padicValNat.mul hne2 hne2] at hv
  have h1 := padicValNat_two_factorial_add_s2 (2 * n)
  have h2 := padicValNat_two_factorial_add_s2 n
  rw [s2_two_mul] at h1
  omega

private lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [s2_zero]
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [s2_zero]
      · rw [s2_pos_rec a ha, s2_pos_rec b hb, s2_pos_rec (a + b) (by omega)]
        by_cases ha1 : a % 2 = 1 <;> by_cases hb1 : b % 2 = 1
        · have hab0 : (a + b) % 2 = 0 := by omega
          have hdiv : (a + b) / 2 = a / 2 + (b / 2 + 1) := by omega
          rw [if_pos ha1, if_pos hb1, if_neg (by omega : ¬ (a + b) % 2 = 1), hdiv]
          have hstep : s2 (b / 2 + 1) ≤ s2 (b / 2) + 1 := by
            have := padicValNat_two_factorial_add_s2 (b / 2 + 1)
            have := padicValNat_two_factorial_add_s2 (b / 2)
            -- direct bound via s2_two_mul / s2_two_mul_add_one
            have h1 : ∀ m, s2 (m + 1) ≤ s2 m + 1 := by
              intro m
              induction m using Nat.strong_induction_on with
              | h m ihm =>
                by_cases hm : m % 2 = 0
                · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
                  rw [s2_two_mul_add_one, s2_two_mul]
                · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
                  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, s2_two_mul, s2_two_mul_add_one]
                  have := ihm k (by omega)
                  omega
            exact h1 (b / 2)
          have hrec := ih (a / 2) (by omega) (b / 2 + 1)
          omega
        · have hab1 : (a + b) % 2 = 1 := by omega
          have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
          rw [if_pos ha1, if_neg hb1, if_pos hab1, hdiv]
          have := ih (a / 2) (by omega) (b / 2)
          omega
        · have hab1 : (a + b) % 2 = 1 := by omega
          have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
          rw [if_neg ha1, if_pos hb1, if_pos hab1, hdiv]
          have := ih (a / 2) (by omega) (b / 2)
          omega
        · have hab0 : (a + b) % 2 = 0 := by omega
          have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
          rw [if_neg ha1, if_neg hb1, if_neg (by omega : ¬ (a + b) % 2 = 1), hdiv]
          have := ih (a / 2) (by omega) (b / 2)
          omega

private lemma s2_add_eq_iff (a b : ℕ) :
    s2 (a + b) = s2 a + s2 b ↔
      (a % 2 = 0 ∨ b % 2 = 0) ∧ s2 (a / 2 + b / 2) = s2 (a / 2) + s2 (b / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Use padicValNat_two_factorial_add_s2 on (a+b)! = choose(a+b,a) * a! * b!
  -- Actually direct binary check is even shorter!
  have hcarry : ∀ m : ℕ, s2 (m + 1) ≤ s2 m + 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ihm =>
      by_cases hm : m % 2 = 0
      · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
        rw [s2_two_mul_add_one, s2_two_mul]
      · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, s2_two_mul, s2_two_mul_add_one]
        have := ihm k (by omega)
        omega
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [s2_zero]
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [s2_zero]
    · rw [s2_pos_rec a ha, s2_pos_rec b hb, s2_pos_rec (a + b) (by omega)]
      by_cases ha1 : a % 2 = 1 <;> by_cases hb1 : b % 2 = 1
      · have hab0 : ¬ (a + b) % 2 = 1 := by omega
        have hdiv : (a + b) / 2 = a / 2 + (b / 2 + 1) := by omega
        rw [if_pos ha1, if_pos hb1, if_neg hab0, hdiv]
        have h1 := s2_add_le (a / 2) (b / 2 + 1)
        have h2 := hcarry (b / 2)
        constructor
        · intro heq; omega
        · rintro ⟨h0 | h0, _⟩ <;> omega
      · have hab1 : (a + b) % 2 = 1 := by omega
        have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        rw [if_pos ha1, if_neg hb1, if_pos hab1, hdiv]
        constructor
        · intro heq; exact ⟨Or.inr (by omega), by omega⟩
        · rintro ⟨_, heq⟩; omega
      · have hab1 : (a + b) % 2 = 1 := by omega
        have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        rw [if_neg ha1, if_pos hb1, if_pos hab1, hdiv]
        constructor
        · intro heq; exact ⟨Or.inl (by omega), by omega⟩
        · rintro ⟨_, heq⟩; omega
      · have hab0 : ¬ (a + b) % 2 = 1 := by omega
        have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        rw [if_neg ha1, if_neg hb1, if_neg hab0, hdiv]
        constructor
        · intro heq; exact ⟨Or.inl (by omega), by omega⟩
        · rintro ⟨_, heq⟩; omega

private lemma submask_card (k : ℕ) :
    ((Finset.range (k + 1)).filter (fun j => s2 j + s2 (k - j) = s2 k)).card = 2 ^ s2 k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · by_cases heven : k % 2 = 0
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
        rw [s2_two_mul]
        have hbij : ((Finset.range (2 * m + 1)).filter (fun j => s2 j + s2 (2 * m - j) = s2 m)) =
            ((Finset.range (m + 1)).filter (fun j => s2 j + s2 (m - j) = s2 m)).image (2 * ·) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨hj, heq⟩
            have hadd : s2 (j + (2 * m - j)) = s2 j + s2 (2 * m - j) := by
              rw [Nat.add_sub_of_le (by omega), s2_two_mul, heq]
            have hiff := (s2_add_eq_iff j (2 * m - j)).mp hadd
            have hj2 : j % 2 = 0 := by rcases hiff.1 with h | h <;> omega
            refine ⟨j / 2, ⟨by omega, ?_⟩, by omega⟩
            have hsub : (2 * m - j) / 2 = m - j / 2 := by omega
            have hrec := hiff.2
            rw [hsub, Nat.add_sub_of_le (by omega)] at hrec
            exact hrec.symm
          · rintro ⟨i, ⟨hi, heq⟩, rfl⟩
            refine ⟨by omega, ?_⟩
            rw [s2_two_mul, show 2 * m - 2 * i = 2 * (m - i) by omega, s2_two_mul, heq]
        rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by omega)]
        exact ih m (by omega)
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
        rw [s2_two_mul_add_one, pow_succ]
        set S := (Finset.range (2 * m + 2)).filter (fun j => s2 j + s2 (2 * m + 1 - j) = s2 m + 1)
        set A := ((Finset.range (m + 1)).filter (fun i => s2 i + s2 (m - i) = s2 m)).image (2 * ·)
        set B := ((Finset.range (m + 1)).filter (fun i => s2 i + s2 (m - i) = s2 m)).image (fun i => 2 * i + 1)
        have hdisj : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          simp only [A, B, Finset.mem_image] at hxA hxB
          obtain ⟨a, _, rfl⟩ := hxA
          obtain ⟨b, _, hb⟩ := hxB
          omega
        have hunion : S = A ∪ B := by
          ext j
          simp only [S, A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨hj, heq⟩
            have hadd : s2 (j + (2 * m + 1 - j)) = s2 j + s2 (2 * m + 1 - j) := by
              rw [Nat.add_sub_of_le (by omega), s2_two_mul_add_one, heq]
            have hiff := (s2_add_eq_iff j (2 * m + 1 - j)).mp hadd
            by_cases hj2 : j % 2 = 0
            · left
              refine ⟨j / 2, ⟨by omega, ?_⟩, by omega⟩
              have hsub : (2 * m + 1 - j) / 2 = m - j / 2 := by omega
              have hrec := hiff.2
              rw [hsub, Nat.add_sub_of_le (by omega)] at hrec
              exact hrec.symm
            · right
              refine ⟨j / 2, ⟨by omega, ?_⟩, by omega⟩
              have hsub : (2 * m + 1 - j) / 2 = m - j / 2 := by omega
              have hrec := hiff.2
              rw [hsub, Nat.add_sub_of_le (by omega)] at hrec
              exact hrec.symm
          · rintro (⟨i, ⟨hi, heq⟩, rfl⟩ | ⟨i, ⟨hi, heq⟩, rfl⟩)
            · refine ⟨by omega, ?_⟩
              rw [s2_two_mul, show 2 * m + 1 - 2 * i = 2 * (m - i) + 1 by omega,
                s2_two_mul_add_one]
              omega
            · refine ⟨by omega, ?_⟩
              rw [s2_two_mul_add_one, show 2 * m + 1 - (2 * i + 1) = 2 * (m - i) by omega,
                s2_two_mul]
              omega
        rw [hunion, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun a b hab => by omega),
          Finset.card_image_of_injective _ (fun a b hab => by omega),
          ih m (by omega)]
        ring

private lemma submask_pos_card_odd {k : ℕ} (hk : 1 ≤ k) :
    Odd ((Finset.Icc 1 k).filter (fun j => s2 j + s2 (k - j) = s2 k)).card := by
  have hset : (Finset.range (k + 1)).filter (fun j => s2 j + s2 (k - j) = s2 k) =
      insert 0 ((Finset.Icc 1 k).filter (fun j => s2 j + s2 (k - j) = s2 k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · rintro ⟨hj, heq⟩
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · left; rfl
      · right; exact ⟨⟨by omega, by omega⟩, heq⟩
    · rintro (rfl | ⟨⟨_, hj⟩, heq⟩)
      · exact ⟨by omega, by simp [s2_zero]⟩
      · exact ⟨by omega, heq⟩
  have hnot : (0 : ℕ) ∉ (Finset.Icc 1 k).filter (fun j => s2 j + s2 (k - j) = s2 k) := by
    simp
  have hcard := submask_card k
  rw [hset, Finset.card_insert_of_notMem hnot] at hcard
  have hs : 1 ≤ s2 k := s2_pos hk
  have hpow : 2 ^ s2 k = 2 * 2 ^ (s2 k - 1) := by
    conv_lhs => rw [show s2 k = (s2 k - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have h2pos : 1 ≤ 2 ^ (s2 k - 1) := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨2 ^ (s2 k - 1) - 1, ?_⟩
  omega

/-- Coefficient of `y^m` in `sqrt(1 - 64 y)`: `1` at `m = 0`, `-2 * C_{m-1} * 16^m` for `m ≥ 1`. -/
private def sqCoeff : ℕ → ℤ
  | 0 => 1
  | m + 1 => -2 * (catalan m : ℤ) * 16 ^ (m + 1)

private lemma sqCoeff_dvd (m : ℕ) (hm : 1 ≤ m) : (2 : ℤ) ^ (3 * s2 m + 1) ∣ sqCoeff m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  dsimp only [sqCoeff]
  have hs : s2 (r + 1) ≤ r + 1 := s2_le (r + 1)
  have h16 : (16 : ℤ) ^ (r + 1) = (2 : ℤ) ^ (4 * (r + 1)) := by
    rw [show (16 : ℤ) = 2 ^ 4 by norm_num, ← pow_mul]
  rw [h16]
  have hexp : 3 * s2 (r + 1) + 1 ≤ 4 * (r + 1) + 1 := by omega
  have hdvd : (2 : ℤ) ^ (3 * s2 (r + 1) + 1) ∣ (2 : ℤ) ^ (4 * (r + 1) + 1) :=
    pow_dvd_pow 2 hexp
  have hrew : -2 * (catalan r : ℤ) * 2 ^ (4 * (r + 1)) = -(catalan r : ℤ) * 2 ^ (4 * (r + 1) + 1) := by
    rw [pow_succ]; ring
  rw [hrew]
  exact dvd_mul_of_dvd_right hdvd _

private lemma sqCoeff_sq : (PowerSeries.mk sqCoeff : PowerSeries ℤ) ^ 2 = 1 - 64 * X := by
  rw [sq]
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk sqCoeff) * coeff j (mk sqCoeff))]
  rcases n with _ | _ | m
  · simp [sqCoeff]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    have h64 : (64 : PowerSeries ℤ) = C 64 := rfl
    rw [map_sub, h64, coeff_C_mul, coeff_one, coeff_X]
    simp only [zero_add, Nat.sub_self, Nat.sub_zero, coeff_mk, sqCoeff, if_true]
    norm_num
  · have h01 : coeff (m + 2) (1 : PowerSeries ℤ) = 0 := by rw [coeff_one]; exact if_neg (by omega)
    have h0X : coeff (m + 2) (X : PowerSeries ℤ) = 0 := by rw [coeff_X]; exact if_neg (by omega)
    rw [map_sub, show (64 : PowerSeries ℤ) = C 64 by rfl, coeff_C_mul, h01, h0X, mul_zero, sub_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, Nat.sub_zero, coeff_mk]
    have hcat : (catalan (m + 1) : ℤ) = ∑ i ∈ Finset.range (m + 1), (catalan i : ℤ) * (catalan (m - i) : ℤ) := by
      have h := catalan_succ' m
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => catalan i * catalan j)] at h
      exact_mod_cast h
    have hmid : ∑ i ∈ Finset.range (m + 1),
        (-2 * (catalan i : ℤ) * 16 ^ (i + 1)) * (-2 * (catalan (m - i) : ℤ) * 16 ^ (m + 1 - i)) =
        4 * 16 ^ (m + 2) * ∑ i ∈ Finset.range (m + 1), (catalan i : ℤ) * (catalan (m - i) : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hp : (16 : ℤ) ^ (i + 1) * 16 ^ (m + 1 - i) = 16 ^ (m + 2) := by
        rw [← pow_add]; congr 1; omega
      calc (-2 * (catalan i : ℤ) * 16 ^ (i + 1)) * (-2 * (catalan (m - i) : ℤ) * 16 ^ (m + 1 - i))
          = 4 * ((catalan i : ℤ) * (catalan (m - i) : ℤ)) * (16 ^ (i + 1) * 16 ^ (m + 1 - i)) := by ring
        _ = 4 * 16 ^ (m + 2) * ((catalan i : ℤ) * (catalan (m - i) : ℤ)) := by rw [hp]; ring
    have hsum_eq : ∑ x ∈ Finset.range (m + 1),
        sqCoeff (x + 1) * sqCoeff (m + 2 - (x + 1)) =
        4 * 16 ^ (m + 2) * (catalan (m + 1) : ℤ) := by
      rw [hcat, ← hmid]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hsub : m + 2 - (i + 1) = (m - i) + 1 := by omega
      rw [hsub]
      dsimp only [sqCoeff]
      rw [show m - i + 1 = m + 1 - i by omega]
    rw [hsum_eq]
    have hsq0 : sqCoeff 0 = 1 := rfl
    have hsqm : sqCoeff (m + 2) = -2 * (catalan (m + 1) : ℤ) * 16 ^ (m + 2) := rfl
    rw [hsq0, hsqm]
    ring

private def hCoeff (n : ℕ) : ℤ := ((2 * n).choose n : ℤ) ^ 3

private lemma hCoeff_val (n : ℕ) :
    (2 : ℤ) ^ (3 * s2 n) ∣ hCoeff n ∧ ¬ ((2 : ℤ) ^ (3 * s2 n + 1) ∣ hCoeff n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (2 * n).choose n ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hv : padicValNat 2 ((2 * n).choose n) = s2 n := padicValNat_two_centralBinom n
  have hd1 : 2 ^ s2 n ∣ (2 * n).choose n := by
    rw [← hv]; exact pow_padicValNat_dvd
  have hnd1 : ¬ (2 ^ (s2 n + 1) ∣ (2 * n).choose n) := by
    rw [← hv]
    intro h
    have := (padicValNat_dvd_iff_le hne).mp h
    omega
  obtain ⟨u, hu⟩ := hd1
  have hu_odd : u % 2 = 1 := by
    by_contra he
    have h2u : 2 ∣ u := by omega
    obtain ⟨v, rfl⟩ := h2u
    apply hnd1
    refine ⟨v, ?_⟩
    rw [hu, pow_succ]; ring
  have hcube : hCoeff n = (2 : ℤ) ^ (3 * s2 n) * (u : ℤ) ^ 3 := by
    unfold hCoeff
    rw [hu]
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm (s2 n) 3]
  constructor
  · exact ⟨(u : ℤ) ^ 3, hcube⟩
  · intro ⟨w, hw⟩
    rw [hcube, pow_succ (2 : ℤ)] at hw
    have hpos : (2 : ℤ) ^ (3 * s2 n) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2u3 : (u : ℤ) ^ 3 = 2 * w := by
      apply mul_left_cancel₀ hpos
      rw [hw]; ring
    have hmod : ((u : ℤ) ^ 3) % 2 = 1 := by
      have : (u : ℤ) % 2 = 1 := by exact_mod_cast hu_odd
      have h1 : (u : ℤ) = 2 * ((u : ℤ) / 2) + 1 := by omega
      rw [h1]
      have : (2 * ((u : ℤ) / 2) + 1) ^ 3 = 2 * (4 * ((u : ℤ) / 2) ^ 3 + 6 * ((u : ℤ) / 2) ^ 2 + 3 * ((u : ℤ) / 2)) + 1 := by ring
      omega
    omega

private def gCoeff (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), sqCoeff i * hCoeff (n - i)

private lemma gCoeff_zero : gCoeff 0 = 1 := by
  simp [gCoeff, sqCoeff, hCoeff]

private lemma gCoeff_val (n : ℕ) :
    (2 : ℤ) ^ (3 * s2 n) ∣ gCoeff n ∧ ¬ ((2 : ℤ) ^ (3 * s2 n + 1) ∣ gCoeff n) := by
  unfold gCoeff
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, sqCoeff, one_mul]
  have htail : (2 : ℤ) ^ (3 * s2 n + 1) ∣
      ∑ k ∈ Finset.range n, sqCoeff (k + 1) * hCoeff (n - (k + 1)) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 := sqCoeff_dvd (k + 1) (by omega)
    have h2 := (hCoeff_val (n - (k + 1))).1
    have hmul : (2 : ℤ) ^ (3 * s2 (k + 1) + 1 + 3 * s2 (n - (k + 1))) ∣
        sqCoeff (k + 1) * hCoeff (n - (k + 1)) := by
      rw [pow_add]; exact mul_dvd_mul h1 h2
    have hsle : s2 n ≤ s2 (k + 1) + s2 (n - (k + 1)) := by
      simpa [Nat.add_sub_of_le (show k + 1 ≤ n by omega)] using s2_add_le (k + 1) (n - (k + 1))
    exact dvd_trans (pow_dvd_pow 2 (by omega)) hmul
  have hh := hCoeff_val n
  constructor
  · exact dvd_add (dvd_trans (pow_dvd_pow 2 (by omega)) htail) hh.1
  · intro hd
    have := (dvd_add_right htail).mp hd
    exact hh.2 this

/-- If `c 0 = 1` and `∑_{j=0}^k gCoeff j * c (k - j) = 0` for all `k ≥ 1`,
then `v_2(c k) = 3 * s2 k` for all `k`. -/
private lemma inv_val_exact (cSeq : ℕ → ℤ) (hc0 : cSeq 0 = 1)
    (hrec : ∀ k : ℕ, 1 ≤ k → ∑ j ∈ Finset.range (k + 1), gCoeff j * cSeq (k - j) = 0) :
    ∀ k : ℕ, (2 : ℤ) ^ (3 * s2 k) ∣ cSeq k ∧ ¬ ((2 : ℤ) ^ (3 * s2 k + 1) ∣ cSeq k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hc0, s2_zero]
      constructor
      · norm_num
      · norm_num
    · have hsum := hrec k hk
      rw [Finset.sum_range_succ'] at hsum
      simp only [Nat.sub_zero, gCoeff_zero, one_mul] at hsum
      have hck : cSeq k = - ∑ j ∈ Finset.Icc 1 k, gCoeff j * cSeq (k - j) := by
        have hidx : ∑ i ∈ Finset.range k, gCoeff (i + 1) * cSeq (k - (i + 1)) =
            ∑ j ∈ Finset.Icc 1 k, gCoeff j * cSeq (k - j) := by
          apply Finset.sum_bij (fun i _ => i + 1)
          · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
          · intro a _ b _ h; omega
          · intro j hj; rw [Finset.mem_Icc] at hj
            exact ⟨j - 1, by rw [Finset.mem_range]; omega, by omega⟩
          · intro i _; rfl
        linarith [hsum, hidx]
      rw [hck, dvd_neg, dvd_neg]
      -- Split Icc 1 k into submasks (s2 j + s2 (k-j) = s2 k) and non-submasks (> s2 k)
      set S := (Finset.Icc 1 k).filter (fun j => s2 j + s2 (k - j) = s2 k)
      set T := (Finset.Icc 1 k).filter (fun j => ¬ (s2 j + s2 (k - j) = s2 k))
      have hsplit : ∑ j ∈ Finset.Icc 1 k, gCoeff j * cSeq (k - j) =
          (∑ j ∈ S, gCoeff j * cSeq (k - j)) + (∑ j ∈ T, gCoeff j * cSeq (k - j)) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      rw [hsplit]
      have hT : (2 : ℤ) ^ (3 * s2 k + 1) ∣ ∑ j ∈ T, gCoeff j * cSeq (k - j) := by
        apply Finset.dvd_sum
        intro j hj
        simp only [T, Finset.mem_filter, Finset.mem_Icc] at hj
        have h1 := (gCoeff_val j).1
        have h2 := (ih (k - j) (by omega)).1
        have hsle : s2 k ≤ s2 j + s2 (k - j) := by
          simpa [Nat.add_sub_of_le hj.1.2] using s2_add_le j (k - j)
        have hlt : s2 k < s2 j + s2 (k - j) := lt_of_le_of_ne hsle (Ne.symm hj.2)
        have hmul : (2 : ℤ) ^ (3 * s2 j + 3 * s2 (k - j)) ∣ gCoeff j * cSeq (k - j) := by
          rw [pow_add]; exact mul_dvd_mul h1 h2
        exact dvd_trans (pow_dvd_pow 2 (by omega)) hmul
      have hS_each : ∀ j ∈ S, (2 : ℤ) ^ (3 * s2 k) ∣ gCoeff j * cSeq (k - j) ∧
          ¬ ((2 : ℤ) ^ (3 * s2 k + 1) ∣ gCoeff j * cSeq (k - j)) := by
        intro j hj
        simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj
        have hg := gCoeff_val j
        have hc := ih (k - j) (by omega)
        obtain ⟨u, hu⟩ := hg.1
        obtain ⟨v, hv⟩ := hc.1
        have hu_odd : u % 2 = 1 := by
          by_contra he
          apply hg.2
          obtain ⟨u', hu'⟩ : ∃ u', u = 2 * u' := ⟨u / 2, by omega⟩
          exact ⟨u', by rw [hu, hu', pow_succ]; ring⟩
        have hv_odd : v % 2 = 1 := by
          by_contra he
          apply hc.2
          obtain ⟨v', hv'⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
          exact ⟨v', by rw [hv, hv', pow_succ]; ring⟩
        have hprod : gCoeff j * cSeq (k - j) = (2 : ℤ) ^ (3 * s2 k) * (u * v) := by
          rw [hu, hv]
          have hexp : 3 * s2 j + 3 * s2 (k - j) = 3 * s2 k := by omega
          calc (2 : ℤ) ^ (3 * s2 j) * u * ((2 : ℤ) ^ (3 * s2 (k - j)) * v)
              = ((2 : ℤ) ^ (3 * s2 j) * (2 : ℤ) ^ (3 * s2 (k - j))) * (u * v) := by ring
            _ = (2 : ℤ) ^ (3 * s2 k) * (u * v) := by rw [← pow_add, hexp]
        constructor
        · exact ⟨u * v, hprod⟩
        · intro ⟨w, hw⟩
          rw [hprod, pow_succ] at hw
          have hpos : (2 : ℤ) ^ (3 * s2 k) ≠ 0 := pow_ne_zero _ (by norm_num)
          have h2uv : u * v = 2 * w := by
            apply mul_left_cancel₀ hpos; linarith
          have huv_odd : (u * v) % 2 = 1 := by
            rw [Int.mul_emod, hu_odd, hv_odd]; norm_num
          omega
      have hS_dvd : (2 : ℤ) ^ (3 * s2 k) ∣ ∑ j ∈ S, gCoeff j * cSeq (k - j) :=
        Finset.dvd_sum (fun j hj => (hS_each j hj).1)
      have hS_ndvd : ¬ ((2 : ℤ) ^ (3 * s2 k + 1) ∣ ∑ j ∈ S, gCoeff j * cSeq (k - j)) := by
        -- Factor out 2^(3*s2 k); each quotient is odd, and S.card is odd!
        set P : ℤ := (2 : ℤ) ^ (3 * s2 k)
        have hPpos : P ≠ 0 := pow_ne_zero _ (by norm_num)
        have hquot : ∑ j ∈ S, gCoeff j * cSeq (k - j) =
            P * ∑ j ∈ S, (gCoeff j * cSeq (k - j)) / P := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact (Int.mul_ediv_cancel' (hS_each j hj).1).symm
        intro ⟨w, hw⟩
        rw [hquot, pow_succ] at hw
        have heven : (∑ j ∈ S, (gCoeff j * cSeq (k - j)) / P) % 2 = 0 := by
          have h2w : ∑ j ∈ S, (gCoeff j * cSeq (k - j)) / P = 2 * w := by
            apply mul_left_cancel₀ hPpos; linarith
          omega
        have hodd_sum : (∑ j ∈ S, (gCoeff j * cSeq (k - j)) / P) % 2 = (S.card : ℤ) % 2 := by
          have hmod_each : ∀ j ∈ S, ((gCoeff j * cSeq (k - j)) / P) % 2 = 1 := by
            intro j hj
            by_contra he
            apply (hS_each j hj).2
            set q := (gCoeff j * cSeq (k - j)) / P
            have h1 : P * q = gCoeff j * cSeq (k - j) := Int.mul_ediv_cancel' (hS_each j hj).1
            obtain ⟨q', hq'⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
            refine ⟨q', ?_⟩
            rw [pow_succ]
            calc gCoeff j * cSeq (k - j) = P * q := h1.symm
              _ = P * (2 * q') := by rw [hq']
              _ = P * 2 * q' := by ring
          have hcong : ∑ j ∈ S, ((gCoeff j * cSeq (k - j)) / P) ≡ ∑ _j ∈ S, (1 : ℤ) [ZMOD 2] := by
            have hstep : ∀ A : Finset ℕ, (∀ j ∈ A, ((gCoeff j * cSeq (k - j)) / P) % 2 = 1) →
                (∑ j ∈ A, (gCoeff j * cSeq (k - j)) / P) % 2 = (∑ _j ∈ A, (1 : ℤ)) % 2 := by
              intro A hA
              classical
              induction A using Finset.induction with
              | empty => simp
              | insert a B ha ihB =>
                rw [Finset.sum_insert ha, Finset.sum_insert ha, Int.add_emod,
                  hA a (Finset.mem_insert_self a B),
                  ihB (fun j hj => hA j (Finset.mem_insert_of_mem hj))]
                omega
            exact hstep S hmod_each
          simpa [Int.ModEq] using hcong
        have hcard_odd := submask_pos_card_odd hk
        obtain ⟨m, hm⟩ := hcard_odd
        have : (S.card : ℤ) % 2 = 1 := by
          have : (S.card : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
          omega
        omega
      constructor
      · exact dvd_add hS_dvd (dvd_trans (pow_dvd_pow 2 (by omega)) hT)
      · intro hd
        exact hS_ndvd ((dvd_add_left hT).mp hd)




/-! ### Part 2A: Formal power series toolkit in `ℚ⟦X⟧`, infinite products, and Lagrange inversion -/

private def dPS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f)

private lemma coeff_dPS (n : ℕ) (f : PowerSeries ℚ) :
    coeff n (dPS f) = ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f :=
  coeff_mk n _

private lemma dPS_zero : dPS 0 = 0 := by
  ext n; simp [coeff_dPS]

private lemma dPS_one : dPS 1 = 0 := by
  ext n; simp [coeff_dPS, coeff_one]

private lemma dPS_C (r : ℚ) : dPS (C r) = 0 := by
  ext n; simp [coeff_dPS]

private lemma dPS_X : dPS X = 1 := by
  ext n
  rw [coeff_dPS, coeff_X, coeff_one]
  rcases n with _ | m
  · simp
  · simp

private lemma dPS_add (f g : PowerSeries ℚ) : dPS (f + g) = dPS f + dPS g := by
  ext n; simp only [coeff_dPS, map_add]; ring

private lemma dPS_sub (f g : PowerSeries ℚ) : dPS (f - g) = dPS f - dPS g := by
  ext n; simp only [coeff_dPS, map_sub]; ring

private lemma dPS_neg (f : PowerSeries ℚ) : dPS (-f) = -dPS f := by
  ext n; simp only [coeff_dPS, map_neg]; ring

private lemma dPS_smul (r : ℚ) (f : PowerSeries ℚ) : dPS (r • f) = r • dPS f := by
  ext n; simp only [coeff_dPS, map_smul, smul_eq_mul]; ring

private lemma dPS_C_mul (r : ℚ) (f : PowerSeries ℚ) : dPS (C r * f) = C r * dPS f := by
  ext n; simp only [coeff_dPS, coeff_C_mul]; ring

private lemma dPS_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    dPS (∑ i ∈ s, f i) = ∑ i ∈ s, dPS (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dPS_zero]
  | insert a b ha ih => simp [Finset.sum_insert ha, dPS_add, ih]

private lemma dPS_mul (f g : PowerSeries ℚ) : dPS (f * g) = dPS f * g + f * dPS g := by
  ext n
  rw [coeff_dPS, map_add, coeff_mul, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (dPS f) * coeff j g),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j (dPS g))]
  have h1 : ∑ i ∈ Finset.range (n + 1), coeff i (dPS f) * coeff (n - i) g =
      ∑ j ∈ Finset.range (n + 2), (j : ℚ) * coeff j f * coeff (n + 1 - j) g := by
    symm
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_dPS]
    have : n + 1 - (i + 1) = n - i := by omega
    rw [this]
  have h2 : ∑ i ∈ Finset.range (n + 1), coeff i f * coeff (n - i) (dPS g) =
      ∑ j ∈ Finset.range (n + 2), ((n + 1 - j : ℕ) : ℚ) * coeff j f * coeff (n + 1 - j) g := by
    symm
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_dPS]
    have hsub : n - i + 1 = n + 1 - i := by omega
    rw [hsub]; ring
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hnat : (j : ℚ) + ((n + 1 - j : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.add_sub_of_le (show j ≤ n + 1 by omega)
  calc ((n + 1 : ℕ) : ℚ) * (coeff j f * coeff (n + 1 - j) g)
      = ((j : ℚ) + ((n + 1 - j : ℕ) : ℚ)) * (coeff j f * coeff (n + 1 - j) g) := by rw [hnat]
    _ = (j : ℚ) * coeff j f * coeff (n + 1 - j) g +
        ((n + 1 - j : ℕ) : ℚ) * coeff j f * coeff (n + 1 - j) g := by ring

private lemma dPS_pow (f : PowerSeries ℚ) :
    ∀ k : ℕ, dPS (f ^ k) = (k : PowerSeries ℚ) * f ^ (k - 1) * dPS f
  | 0 => by simp [dPS_one]
  | 1 => by simp
  | k + 2 => by
    rw [pow_succ, dPS_mul, dPS_pow f (k + 1)]
    have h1 : k + 1 - 1 = k := rfl
    have h2 : k + 2 - 1 = k + 1 := rfl
    rw [h1, h2, pow_succ]
    push_cast
    ring

/-! #### `psSq`: substitution `X ↦ X^2` -/

private def psSq (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n % 2 = 0 then coeff (n / 2) f else 0)

private lemma coeff_psSq (n : ℕ) (f : PowerSeries ℚ) :
    coeff n (psSq f) = if n % 2 = 0 then coeff (n / 2) f else 0 :=
  coeff_mk n _

private lemma coeff_psSq_even (m : ℕ) (f : PowerSeries ℚ) :
    coeff (2 * m) (psSq f) = coeff m f := by
  rw [coeff_psSq]
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  simp [h1, h2]

private lemma coeff_psSq_odd (m : ℕ) (f : PowerSeries ℚ) :
    coeff (2 * m + 1) (psSq f) = 0 := by
  rw [coeff_psSq]
  simp

private lemma psSq_zero : psSq 0 = 0 := by
  ext n; simp [coeff_psSq]

private lemma psSq_one : psSq 1 = 1 := by
  ext n
  simp only [coeff_psSq, coeff_one]
  split_ifs <;> first | rfl | omega

private lemma psSq_C (r : ℚ) : psSq (C r) = C r := by
  ext n
  simp only [coeff_psSq, coeff_C]
  split_ifs <;> first | rfl | omega

private lemma psSq_X : psSq X = X ^ 2 := by
  ext n
  simp only [coeff_psSq, coeff_X_pow, coeff_X]
  split_ifs <;> first | rfl | omega

private lemma psSq_add (f g : PowerSeries ℚ) : psSq (f + g) = psSq f + psSq g := by
  ext n; simp only [coeff_psSq, map_add]; split_ifs <;> ring

private lemma psSq_sub (f g : PowerSeries ℚ) : psSq (f - g) = psSq f - psSq g := by
  ext n; simp only [coeff_psSq, map_sub]; split_ifs <;> ring

private lemma psSq_neg (f : PowerSeries ℚ) : psSq (-f) = -psSq f := by
  ext n; simp only [coeff_psSq, map_neg]; split_ifs <;> ring

private lemma psSq_mul (f g : PowerSeries ℚ) : psSq (f * g) = psSq f * psSq g := by
  ext n
  rw [coeff_psSq]
  conv_rhs => rw [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psSq f) * coeff j (psSq g))]
  by_cases hn : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [if_pos hn, show 2 * m / 2 = m by omega, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]
    have hsplit : ∑ i ∈ Finset.range (2 * m + 1), coeff i (psSq f) * coeff (2 * m - i) (psSq g) =
        ∑ i ∈ (Finset.range (2 * m + 1)).filter (fun i => i % 2 = 0),
          coeff i (psSq f) * coeff (2 * m - i) (psSq g) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * m + 1)) (fun i => i % 2 = 0)]
      have hodd : ∑ i ∈ (Finset.range (2 * m + 1)).filter (fun i => ¬ i % 2 = 0),
          coeff i (psSq f) * coeff (2 * m - i) (psSq g) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [coeff_psSq, if_neg hi.2, zero_mul]
      rw [hodd, add_zero]
    rw [hsplit]
    apply Finset.sum_bij (fun j _ => 2 * j)
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · intro a _ b _ h; omega
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨i / 2, by rw [Finset.mem_range]; omega, by omega⟩
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [coeff_psSq_even, show 2 * m - 2 * j = 2 * (m - j) by omega, coeff_psSq_even]
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_psSq, coeff_psSq]
    by_cases hi2 : i % 2 = 0
    · have hsub : ¬ (n - i) % 2 = 0 := by omega
      rw [if_neg hsub, mul_zero]
    · rw [if_neg hi2, zero_mul]

private lemma psSq_pow (f : PowerSeries ℚ) : ∀ k : ℕ, psSq (f ^ k) = (psSq f) ^ k
  | 0 => by simp [psSq_one]
  | k + 1 => by rw [pow_succ, pow_succ, psSq_mul, psSq_pow f k]

private lemma psSq_X_pow (k : ℕ) : psSq (X ^ k) = X ^ (2 * k) := by
  rw [psSq_pow, psSq_X, ← pow_mul]

private lemma psSq_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    psSq (∏ i ∈ s, f i) = ∏ i ∈ s, psSq (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [psSq_one]
  | insert a b ha ih => simp [Finset.prod_insert ha, psSq_mul, ih]

private lemma dPS_psSq (f : PowerSeries ℚ) : dPS (psSq f) = 2 * X * psSq (dPS f) := by
  ext n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [coeff_dPS, coeff_psSq_odd, mul_zero]
    rcases m with _ | m
    · rw [show 2 * 0 = 0 by omega, mul_assoc, show (2 : PowerSeries ℚ) = C 2 by rfl,
        coeff_C_mul, coeff_zero_X_mul, mul_zero]
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, mul_assoc,
        show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C_mul, coeff_succ_X_mul,
        coeff_psSq_odd, mul_zero]
  · rw [coeff_dPS, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, coeff_psSq_even,
      mul_assoc, show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C_mul, coeff_succ_X_mul,
      coeff_psSq_even, coeff_dPS]
    push_cast
    ring

private lemma eq_one_of_psSq_eq {f : PowerSeries ℚ} (hf : psSq f = f) (h0 : coeff 0 f = 1) :
    f = 1 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, coeff_one]
    · rw [coeff_one, if_neg (by omega), ← hf, coeff_psSq]
      split_ifs with he
      · have hlt : n / 2 < n := by omega
        have hpos : n / 2 ≠ 0 := by omega
        have hrec := ih (n / 2) hlt
        rw [coeff_one, if_neg hpos] at hrec
        exact hrec
      · rfl

/-! #### Power series units / inverses -/

private lemma exists_ps_inv {f : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) :
    ∃ g : PowerSeries ℚ, f * g = 1 := by
  have hfc : constantCoeff f ≠ 0 := by rwa [← coeff_zero_eq_constantCoeff]
  have hu : IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hfc)
  exact ⟨↑(hu.unit⁻¹), hu.unit.mul_inv⟩

private noncomputable def psInv (f : PowerSeries ℚ) : PowerSeries ℚ :=
  if h : coeff 0 f ≠ 0 then Classical.choose (exists_ps_inv h) else 0

private lemma mul_psInv {f : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) : f * psInv f = 1 := by
  unfold psInv
  rw [dif_pos hf]
  exact Classical.choose_spec (exists_ps_inv hf)

private lemma psInv_mul {f : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) : psInv f * f = 1 := by
  rw [mul_comm]; exact mul_psInv hf

private lemma coeff_zero_psInv {f : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) :
    coeff 0 (psInv f) = (coeff 0 f)⁻¹ := by
  have h := congrArg constantCoeff (mul_psInv hf)
  rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff] at h
  exact eq_inv_of_mul_eq_one_right h

private lemma psSq_psInv {f : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) :
    psSq (psInv f) = psInv (psSq f) := by
  have h0 : coeff 0 (psSq f) ≠ 0 := by rwa [coeff_psSq_even 0 f]
  have h1 : psSq f * psSq (psInv f) = 1 := by
    rw [← psSq_mul, mul_psInv hf, psSq_one]
  have h2 : psSq f * psInv (psSq f) = 1 := mul_psInv h0
  have hne : psSq f ≠ 0 := by intro hz; rw [hz, map_zero] at h0; exact h0 rfl
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-! #### Composition `psComp f g` for `coeff 0 g = 0` -/

private lemma coeff_pow_eq_zero_of_lt {g : PowerSeries ℚ} (hg : coeff 0 g = 0) :
    ∀ {k n : ℕ}, n < k → coeff n (g ^ k) = 0
  | 0, _, h => by omega
  | k + 1, n, h => by
    rw [pow_succ, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (g ^ k) * coeff j g)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hin : i = n
    · subst hin; rw [Nat.sub_self, hg, mul_zero]
    · rw [coeff_pow_eq_zero_of_lt hg (show i < k by omega), zero_mul]

private def psComp (f g : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1), coeff k f * coeff n (g ^ k))

private def psTrunc (N : ℕ) (f g : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range (N + 1), C (coeff k f) * g ^ k

private lemma coeff_psComp_eq_trunc {f g : PowerSeries ℚ} (hg : coeff 0 g = 0)
    {n N : ℕ} (hN : n ≤ N) :
    coeff n (psComp f g) = coeff n (psTrunc N f g) := by
  unfold psComp psTrunc
  rw [coeff_mk, map_sum]
  simp only [coeff_C_mul]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  rw [Finset.mem_range] at hk
  have hlt : n < k := by omega
  rw [coeff_pow_eq_zero_of_lt hg hlt, mul_zero]

private lemma coeff_zero_psComp (f g : PowerSeries ℚ) :
    coeff 0 (psComp f g) = coeff 0 f := by
  simp [psComp, coeff_mk]

private lemma psComp_zero (g : PowerSeries ℚ) : psComp 0 g = 0 := by
  ext n; simp [psComp, coeff_mk]

private lemma psComp_one (g : PowerSeries ℚ) : psComp 1 g = 1 := by
  ext n
  simp only [psComp, coeff_mk, coeff_one]
  rw [Finset.sum_range_succ']
  simp only [if_true, one_mul, pow_zero, coeff_one]
  have h0 : ∑ k ∈ Finset.range n, (if k + 1 = 0 then (1 : ℚ) else 0) * coeff n (g ^ (k + 1)) = 0 := by
    apply Finset.sum_eq_zero; intro k _; simp
  rw [h0, zero_add]

private lemma psComp_C (r : ℚ) (g : PowerSeries ℚ) : psComp (C r) g = C r := by
  ext n
  simp only [psComp, coeff_mk, coeff_C]
  rw [Finset.sum_range_succ']
  simp only [if_true, pow_zero, coeff_one]
  have h0 : ∑ k ∈ Finset.range n, (if k + 1 = 0 then r else 0) * coeff n (g ^ (k + 1)) = 0 := by
    apply Finset.sum_eq_zero; intro k _; simp
  rw [h0, zero_add]
  split_ifs <;> ring

private lemma psComp_X {g : PowerSeries ℚ} (hg : coeff 0 g = 0) : psComp X g = g := by
  ext n
  rw [coeff_psComp_eq_trunc hg (show n ≤ n + 1 by omega)]
  unfold psTrunc
  rw [map_sum]
  simp only [coeff_C_mul, coeff_X]
  have hmem : (1 : ℕ) ∈ Finset.range (n + 2) := by rw [Finset.mem_range]; omega
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hmem h

private lemma psComp_add (f₁ f₂ g : PowerSeries ℚ) :
    psComp (f₁ + f₂) g = psComp f₁ g + psComp f₂ g := by
  ext n
  simp only [psComp, map_add, coeff_mk, add_mul, Finset.sum_add_distrib]

private lemma psComp_sub (f₁ f₂ g : PowerSeries ℚ) :
    psComp (f₁ - f₂) g = psComp f₁ g - psComp f₂ g := by
  ext n
  simp only [psComp, map_sub, coeff_mk, sub_mul, Finset.sum_sub_distrib]

private lemma psComp_smul (r : ℚ) (f g : PowerSeries ℚ) :
    psComp (r • f) g = r • psComp f g := by
  ext n
  simp only [psComp, map_smul, coeff_mk, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma psComp_C_mul (r : ℚ) (f g : PowerSeries ℚ) :
    psComp (C r * f) g = C r * psComp f g := by
  ext n
  simp only [psComp, coeff_C_mul, coeff_mk, Finset.mul_sum, mul_assoc]

private lemma psComp_congr_trunc {f₁ f₂ g : PowerSeries ℚ} {n : ℕ}
    (h : ∀ k ≤ n, coeff k f₁ = coeff k f₂) :
    coeff n (psComp f₁ g) = coeff n (psComp f₂ g) := by
  simp only [psComp, coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [h k (by omega)]

private lemma coeff_mul_congr {a₁ a₂ b₁ b₂ : PowerSeries ℚ} {n : ℕ}
    (ha : ∀ k ≤ n, coeff k a₁ = coeff k a₂) (hb : ∀ k ≤ n, coeff k b₁ = coeff k b₂) :
    coeff n (a₁ * b₁) = coeff n (a₂ * b₂) := by
  rw [coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i a₁ * coeff j b₁),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i a₂ * coeff j b₂)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [ha i (by omega), hb (n - i) (by omega)]

private lemma psComp_mul (f₁ f₂ : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : coeff 0 g = 0) :
    psComp (f₁ * f₂) g = psComp f₁ g * psComp f₂ g := by
  ext n
  have h1 : coeff n (psComp f₁ g * psComp f₂ g) = coeff n (psTrunc n f₁ g * psTrunc n f₂ g) := by
    apply coeff_mul_congr
    · intro k hk; exact coeff_psComp_eq_trunc hg hk
    · intro k hk; exact coeff_psComp_eq_trunc hg hk
  rw [h1]
  unfold psTrunc
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [map_sum]
  simp only [map_sum]
  have hrew : ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
        coeff n (C (coeff a f₁) * g ^ a * (C (coeff b f₂) * g ^ b)) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
        coeff a f₁ * coeff b f₂ * coeff n (g ^ (a + b)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have : C (coeff a f₁) * g ^ a * (C (coeff b f₂) * g ^ b) =
        C (coeff a f₁ * coeff b f₂) * g ^ (a + b) := by
      rw [map_mul, pow_add]; ring
    rw [this, coeff_C_mul]
  rw [hrew]
  -- Group by k = a + b <= n (since a + b > n gives coeff n (g^(a+b)) = 0)
  simp only [psComp, coeff_mk]
  have hzero : ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
        coeff a f₁ * coeff b f₂ * coeff n (g ^ (a + b)) =
      ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 + p.2 ≤ n),
        coeff p.1 f₁ * coeff p.2 f₂ * coeff n (g ^ (p.1 + p.2)) := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1) ×ˢ Finset.range (n + 1))
      (fun p => p.1 + p.2 ≤ n)]
    have hhi : ∑ p ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => ¬ p.1 + p.2 ≤ n),
        coeff p.1 f₁ * coeff p.2 f₂ * coeff n (g ^ (p.1 + p.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [coeff_pow_eq_zero_of_lt hg (by omega), mul_zero]
    rw [hhi, add_zero]
  rw [hzero]
  have hfiber : ∑ k ∈ Finset.range (n + 1), coeff k (f₁ * f₂) * coeff n (g ^ k) =
      ∑ k ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (k + 1),
        coeff a f₁ * coeff (k - a) f₂ * coeff n (g ^ k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f₁ * coeff j f₂),
      Finset.sum_mul]
  rw [hfiber]
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun p _ => ⟨p.1 + p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro p₁ hp₁ p₂ hp₂ h
    simp only [Sigma.mk.inj_iff] at h
    rcases p₁ with ⟨a₁, b₁⟩; rcases p₂ with ⟨a₂, b₂⟩
    dsimp at h
    have ha : a₁ = a₂ := eq_of_heq h.2
    have hb : b₁ = b₂ := by omega
    exact Prod.ext ha hb
  · intro ⟨k, a⟩ hka
    simp only [Finset.mem_sigma, Finset.mem_range] at hka
    refine ⟨(a, k - a), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · simp only [Sigma.mk.inj_iff]
      exact ⟨by omega, HEq.rfl⟩
  · intro p _
    dsimp
    rw [Nat.add_sub_cancel_left]

private lemma psComp_pow (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : coeff 0 g = 0) :
    ∀ k : ℕ, psComp (f ^ k) g = (psComp f g) ^ k
  | 0 => by simp [psComp_one]
  | k + 1 => by rw [pow_succ, pow_succ, psComp_mul _ _ hg, psComp_pow f hg k]

private lemma psComp_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (g : PowerSeries ℚ) :
    psComp (∑ i ∈ s, f i) g = ∑ i ∈ s, psComp (f i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp [psComp_zero]
  | insert a b ha ih => simp [Finset.sum_insert ha, psComp_add, ih]

private lemma dPS_psComp (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : coeff 0 g = 0) :
    dPS (psComp f g) = psComp (dPS f) g * dPS g := by
  ext n
  rw [coeff_dPS, coeff_psComp_eq_trunc hg (le_refl (n + 1)), ← coeff_dPS]
  have hd : dPS (psTrunc (n + 1) f g) = psTrunc n (dPS f) g * dPS g := by
    unfold psTrunc
    rw [dPS_sum, Finset.sum_range_succ']
    simp only [pow_zero, mul_one, dPS_C, add_zero]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [dPS_C_mul, dPS_pow, Nat.add_sub_cancel, coeff_dPS, map_mul, map_natCast]
    ring
  rw [hd]
  apply coeff_mul_congr
  · intro k hk; exact (coeff_psComp_eq_trunc hg hk).symm
  · intro k _; rfl

private lemma psComp_comp (f : PowerSeries ℚ) {g h : PowerSeries ℚ}
    (hg : coeff 0 g = 0) (hh : coeff 0 h = 0) :
    psComp (psComp f g) h = psComp f (psComp g h) := by
  have hgh0 : coeff 0 (psComp g h) = 0 := by rw [coeff_zero_psComp, hg]
  ext n
  rw [coeff_psComp_eq_trunc hgh0 (le_refl n)]
  have htr : psTrunc n f (psComp g h) = psComp (psTrunc n f g) h := by
    unfold psTrunc
    rw [psComp_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [psComp_C_mul, psComp_pow g hh k]
  rw [htr]
  apply psComp_congr_trunc
  intro k hk
  exact coeff_psComp_eq_trunc hg hk

private lemma psComp_X_sq (f : PowerSeries ℚ) : psComp f (X ^ 2) = psSq f := by
  have h0 : coeff 0 (X ^ 2 : PowerSeries ℚ) = 0 := by rw [coeff_X_pow]; norm_num
  ext n
  rw [psComp, coeff_mk, coeff_psSq]
  by_cases hn : n % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [if_pos hn, show 2 * m / 2 = m by omega]
    have hmem : m ∈ Finset.range (2 * m + 1) := by rw [Finset.mem_range]; omega
    rw [Finset.sum_eq_single m]
    · rw [← pow_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro k _ hkm
      rw [← pow_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hm; exact absurd hmem hm
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro k _
    rw [← pow_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-! #### Infinite products `infProd` -/

private def infProd (a : ℕ → PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => coeff n (∏ m ∈ Finset.range n, a m))

private lemma coeff_mul_of_one_mod {f g : PowerSeries ℚ} {n : ℕ}
    (hg0 : coeff 0 g = 1) (hg : ∀ k, 1 ≤ k → k ≤ n → coeff k g = 0) :
    coeff n (f * g) = coeff n f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]
  rw [Finset.sum_range_succ, Nat.sub_self, hg0, mul_one]
  have h0 : ∑ i ∈ Finset.range n, coeff i f * coeff (n - i) g = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hg (n - i) (by omega) (by omega), mul_zero]
  rw [h0, zero_add]

private lemma coeff_infProd_eq {a : ℕ → PowerSeries ℚ}
    (ha : ∀ m, coeff 0 (a m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a m) = 0)
    {n N : ℕ} (hN : n ≤ N) :
    coeff n (infProd a) = coeff n (∏ m ∈ Finset.range N, a m) := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    simp [infProd, coeff_mk]
  | succ N ih =>
    by_cases hle : n ≤ N
    · rw [Finset.prod_range_succ, coeff_mul_of_one_mod (ha N).1 (fun k hk1 hkn => (ha N).2 k hk1 (by omega))]
      exact ih hle
    · have hn : n = N + 1 := by omega
      subst hn
      simp [infProd, coeff_mk]

private lemma coeff_zero_infProd (a : ℕ → PowerSeries ℚ) :
    coeff 0 (infProd a) = 1 := by
  simp [infProd, coeff_mk, coeff_one]

private lemma one_mod_mul {a b : PowerSeries ℚ} {m : ℕ}
    (ha0 : coeff 0 a = 1) (ha : ∀ k, 1 ≤ k → k ≤ m → coeff k a = 0)
    (hb0 : coeff 0 b = 1) (hb : ∀ k, 1 ≤ k → k ≤ m → coeff k b = 0) :
    coeff 0 (a * b) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a * b) = 0 := by
  constructor
  · rw [coeff_zero_eq_constantCoeff, map_mul, ← coeff_zero_eq_constantCoeff, ha0, hb0, mul_one]
  · intro k hk1 hkm
    rw [coeff_mul_of_one_mod hb0 (fun j hj1 hjk => hb j hj1 (by omega))]
    exact ha k hk1 hkm

private lemma one_mod_pow {a : PowerSeries ℚ} {m : ℕ}
    (ha0 : coeff 0 a = 1) (ha : ∀ k, 1 ≤ k → k ≤ m → coeff k a = 0) :
    ∀ r : ℕ, coeff 0 (a ^ r) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a ^ r) = 0
  | 0 => ⟨by simp [coeff_one], fun k hk1 _ => by rw [pow_zero, coeff_one]; exact if_neg (by omega)⟩
  | r + 1 => by
    rw [pow_succ]
    have ih := one_mod_pow ha0 ha r
    exact one_mod_mul ih.1 ih.2 ha0 ha

private lemma infProd_mul {a b : ℕ → PowerSeries ℚ}
    (ha : ∀ m, coeff 0 (a m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a m) = 0)
    (hb : ∀ m, coeff 0 (b m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (b m) = 0) :
    infProd a * infProd b = infProd (fun m => a m * b m) := by
  ext n
  have hab : ∀ m, coeff 0 (a m * b m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a m * b m) = 0 :=
    fun m => one_mod_mul (ha m).1 (ha m).2 (hb m).1 (hb m).2
  rw [coeff_infProd_eq hab (le_refl n), Finset.prod_mul_distrib]
  apply coeff_mul_congr
  · intro k hk; exact coeff_infProd_eq ha hk
  · intro k hk; exact coeff_infProd_eq hb hk

private lemma infProd_pow {a : ℕ → PowerSeries ℚ}
    (ha : ∀ m, coeff 0 (a m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a m) = 0) :
    ∀ r : ℕ, (infProd a) ^ r = infProd (fun m => (a m) ^ r)
  | 0 => by
    ext n; simp [infProd, coeff_mk]
  | r + 1 => by
    have har : ∀ m, coeff 0 ((a m) ^ r) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k ((a m) ^ r) = 0 :=
      fun m => one_mod_pow (ha m).1 (ha m).2 r
    rw [pow_succ, infProd_pow ha r, infProd_mul har ha]
    simp only [pow_succ]

private lemma psSq_infProd {a : ℕ → PowerSeries ℚ}
    (ha : ∀ m, coeff 0 (a m) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (a m) = 0) :
    psSq (infProd a) = infProd (fun m => psSq (a m)) := by
  have hasq : ∀ m, coeff 0 (psSq (a m)) = 1 ∧ ∀ k, 1 ≤ k → k ≤ m → coeff k (psSq (a m)) = 0 := by
    intro m
    refine ⟨by rw [coeff_psSq_even 0, (ha m).1], fun k hk1 hkm => ?_⟩
    rw [coeff_psSq]
    split_ifs with he
    · exact (ha m).2 (k / 2) (by omega) (by omega)
    · rfl
  ext n
  rw [coeff_infProd_eq hasq (le_refl n), ← psSq_prod, coeff_psSq, coeff_psSq]
  split_ifs with he
  · exact coeff_infProd_eq ha (by omega)
  · rfl

private lemma one_mod_one_add_X_pow (c : ℚ) {d m : ℕ} (hd : m < d) :
    coeff 0 (1 + C c * X ^ d : PowerSeries ℚ) = 1 ∧
      ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C c * X ^ d : PowerSeries ℚ) = 0 := by
  constructor
  · rw [map_add, coeff_one, coeff_C_mul, coeff_X_pow]
    simp [show 0 ≠ d by omega]
  · intro k hk1 hkm
    rw [map_add, coeff_one, coeff_C_mul, coeff_X_pow]
    simp [show k ≠ 0 by omega, show k ≠ d by omega]

/-! #### Euler's infinite product identity `P_odd * M_odd * P_even = 1` -/

private def E_even : PowerSeries ℚ := infProd (fun m => 1 + C (-1) * X ^ (2 * (m + 1)))
private def P_odd  : PowerSeries ℚ := infProd (fun m => 1 + C 1 * X ^ (2 * m + 1))
private def M_odd  : PowerSeries ℚ := infProd (fun m => 1 + C (-1) * X ^ (2 * m + 1))
private def P_even : PowerSeries ℚ := infProd (fun m => 1 + C 1 * X ^ (2 * (m + 1)))

private lemma hE_even_mod : ∀ m, coeff 0 (1 + C (-1 : ℚ) * X ^ (2 * (m + 1))) = 1 ∧
    ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (-1 : ℚ) * X ^ (2 * (m + 1))) = 0 :=
  fun m => one_mod_one_add_X_pow (-1) (by omega)

private lemma hP_odd_mod : ∀ m, coeff 0 (1 + C (1 : ℚ) * X ^ (2 * m + 1)) = 1 ∧
    ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (1 : ℚ) * X ^ (2 * m + 1)) = 0 :=
  fun m => one_mod_one_add_X_pow 1 (by omega)

private lemma hM_odd_mod : ∀ m, coeff 0 (1 + C (-1 : ℚ) * X ^ (2 * m + 1)) = 1 ∧
    ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (-1 : ℚ) * X ^ (2 * m + 1)) = 0 :=
  fun m => one_mod_one_add_X_pow (-1) (by omega)

private lemma hP_even_mod : ∀ m, coeff 0 (1 + C (1 : ℚ) * X ^ (2 * (m + 1))) = 1 ∧
    ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (1 : ℚ) * X ^ (2 * (m + 1))) = 0 :=
  fun m => one_mod_one_add_X_pow 1 (by omega)

private lemma euler_prod_id : P_odd * M_odd * P_even = 1 := by
  have h1 : E_even * P_even = psSq E_even := by
    unfold E_even P_even
    rw [infProd_mul hE_even_mod hP_even_mod, psSq_infProd hE_even_mod]
    congr 1; funext m
    rw [psSq_add, psSq_one, psSq_mul, psSq_C, psSq_X_pow]
    have hpow : (X : PowerSeries ℚ) ^ (2 * (m + 1)) * X ^ (2 * (m + 1)) = X ^ (2 * (2 * (m + 1))) := by
      rw [← pow_add]; congr 1; omega
    calc (1 + C (-1 : ℚ) * X ^ (2 * (m + 1))) * (1 + C 1 * X ^ (2 * (m + 1)))
        = 1 + (C (-1) + C 1) * X ^ (2 * (m + 1)) + C (-1) * C 1 * (X ^ (2 * (m + 1)) * X ^ (2 * (m + 1))) := by ring
      _ = 1 + C (-1) * X ^ (2 * (2 * (m + 1))) := by rw [hpow, ← map_add, ← map_mul]; norm_num
  have h2 : P_odd * M_odd * psSq E_even = E_even := by
    have hPM : P_odd * M_odd = infProd (fun m => 1 + C (-1) * X ^ (2 * (2 * m + 1))) := by
      unfold P_odd M_odd
      rw [infProd_mul hP_odd_mod hM_odd_mod]
      congr 1; funext m
      have hpow : (X : PowerSeries ℚ) ^ (2 * m + 1) * X ^ (2 * m + 1) = X ^ (2 * (2 * m + 1)) := by
        rw [← pow_add]; congr 1; omega
      calc (1 + C (1 : ℚ) * X ^ (2 * m + 1)) * (1 + C (-1) * X ^ (2 * m + 1))
          = 1 + (C 1 + C (-1)) * X ^ (2 * m + 1) + C 1 * C (-1) * (X ^ (2 * m + 1) * X ^ (2 * m + 1)) := by ring
        _ = 1 + C (-1) * X ^ (2 * (2 * m + 1)) := by rw [hpow, ← map_add, ← map_mul]; norm_num
    have hPM_mod : ∀ m, coeff 0 (1 + C (-1 : ℚ) * X ^ (2 * (2 * m + 1))) = 1 ∧
        ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (-1 : ℚ) * X ^ (2 * (2 * m + 1))) = 0 :=
      fun m => one_mod_one_add_X_pow (-1) (by omega)
    have hSq_mod : ∀ m, coeff 0 (1 + C (-1 : ℚ) * X ^ (2 * (2 * (m + 1)))) = 1 ∧
        ∀ k, 1 ≤ k → k ≤ m → coeff k (1 + C (-1 : ℚ) * X ^ (2 * (2 * (m + 1)))) = 0 :=
      fun m => one_mod_one_add_X_pow (-1) (by omega)
    have hSq : psSq E_even = infProd (fun m => 1 + C (-1) * X ^ (2 * (2 * (m + 1)))) := by
      unfold E_even
      rw [psSq_infProd hE_even_mod]
      congr 1; funext m
      rw [psSq_add, psSq_one, psSq_mul, psSq_C, psSq_X_pow]
    rw [hPM, hSq, infProd_mul hPM_mod hSq_mod]
    ext n
    rw [coeff_infProd_eq (fun m => one_mod_mul (hPM_mod m).1 (hPM_mod m).2 (hSq_mod m).1 (hSq_mod m).2) (le_refl n)]
    unfold E_even
    rw [coeff_infProd_eq hE_even_mod (show n ≤ 2 * n by omega)]
    congr 1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]
  have hE_ne : E_even ≠ 0 := by
    intro hz
    have := congrArg (coeff 0) hz
    unfold E_even at this
    rw [coeff_zero_infProd, map_zero] at this
    exact one_ne_zero this
  apply mul_left_cancel₀ hE_ne
  calc E_even * (P_odd * M_odd * P_even)
      = P_odd * M_odd * (E_even * P_even) := by ring
    _ = P_odd * M_odd * psSq E_even := by rw [h1]
    _ = E_even := h2
    _ = E_even * 1 := (mul_one E_even).symm

/-! #### 10-line Lagrange inversion and `24 ∣ c k` -/

private lemma lagrange_recurrence {Q y G : PowerSeries ℚ}
    (hQ0 : coeff 0 Q = 1) (hQy : Q * y = X) (hDE : X * dPS y = y * psComp G y) :
    ∀ k : ℕ, 1 ≤ k →
      ∑ j ∈ Finset.range (k + 1), coeff j G * coeff (k - j) (Q ^ (k - j)) = 0 := by
  have hy0 : coeff 0 y = 0 := by
    have h := congrArg constantCoeff hQy
    rw [map_mul, ← coeff_zero_eq_constantCoeff, hQ0, one_mul, coeff_X] at h
    simpa using h
  intro k hk
  have hdQy : dPS Q * y + Q * dPS y = 1 := by
    rw [← dPS_mul, hQy, dPS_X]
  have hQ_dy : Q ^ (k + 1) * dPS y = Q ^ k - X * Q ^ (k - 1) * dPS Q := by
    have hpow : Q ^ k = Q ^ (k - 1) * Q := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    calc Q ^ (k + 1) * dPS y
        = Q ^ k * (Q * dPS y) := by rw [pow_succ]; ring
      _ = Q ^ k * (1 - dPS Q * y) := by
          have : Q * dPS y = 1 - dPS Q * y := eq_sub_of_add_eq' hdQy
          rw [this]
      _ = Q ^ k - (Q ^ (k - 1) * Q) * dPS Q * y := by rw [← hpow]; ring
      _ = Q ^ k - (Q * y) * Q ^ (k - 1) * dPS Q := by ring
      _ = Q ^ k - X * Q ^ (k - 1) * dPS Q := by rw [hQy]
  have hlhs_zero : coeff (k + 1) (X * Q ^ (k + 1) * dPS y) = 0 := by
    rw [mul_assoc, coeff_succ_X_mul, hQ_dy, map_sub]
    have hscale : (k : ℚ) * coeff k (X * Q ^ (k - 1) * dPS Q) = (k : ℚ) * coeff k (Q ^ k) := by
      have h1 : coeff k (X * dPS (Q ^ k)) = (k : ℚ) * coeff k (Q ^ k) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [coeff_succ_X_mul, coeff_dPS, show k - 1 + 1 = k by omega]
      have h2 : X * dPS (Q ^ k) = C (k : ℚ) * (X * Q ^ (k - 1) * dPS Q) := by
        rw [dPS_pow, show (k : PowerSeries ℚ) = C (k : ℚ) by simp]; ring
      rw [h2, coeff_C_mul] at h1
      exact h1
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have heq : coeff k (X * Q ^ (k - 1) * dPS Q) = coeff k (Q ^ k) :=
      mul_left_cancel₀ hkQ hscale
    rw [heq, sub_self]
  have hmul := congrArg (fun p => coeff (k + 1) (Q ^ (k + 1) * p)) hDE
  have hlhs_rew : Q ^ (k + 1) * (X * dPS y) = X * Q ^ (k + 1) * dPS y := by ring
  have hrhs_rew : Q ^ (k + 1) * (y * psComp G y) = X * (Q ^ k * psComp G y) := by
    calc Q ^ (k + 1) * (y * psComp G y)
        = (Q * y) * (Q ^ k * psComp G y) := by rw [pow_succ]; ring
      _ = X * (Q ^ k * psComp G y) := by rw [hQy]
  rw [hlhs_rew, hrhs_rew, hlhs_zero, coeff_succ_X_mul] at hmul
  have htr : coeff k (Q ^ k * psComp G y) = coeff k (Q ^ k * psTrunc k G y) := by
    apply coeff_mul_congr
    · intro _ _; rfl
    · intro m hm; exact coeff_psComp_eq_trunc hy0 hm
  rw [htr] at hmul
  unfold psTrunc at hmul
  rw [Finset.mul_sum, map_sum] at hmul
  symm
  rw [hmul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hterm : Q ^ k * (C (coeff j G) * y ^ j) = C (coeff j G) * (X ^ j * Q ^ (k - j)) := by
    have hsplit : Q ^ k = Q ^ (k - j) * Q ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    calc Q ^ k * (C (coeff j G) * y ^ j)
        = C (coeff j G) * ((Q ^ j * y ^ j) * Q ^ (k - j)) := by rw [hsplit]; ring
      _ = C (coeff j G) * ((Q * y) ^ j * Q ^ (k - j)) := by rw [mul_pow]
      _ = C (coeff j G) * (X ^ j * Q ^ (k - j)) := by rw [hQy]
  rw [hterm, coeff_C_mul]
  have hshift : ∀ (r m : ℕ) (f : PowerSeries ℚ), coeff (m + r) (X ^ r * f) = coeff m f := by
    intro r
    induction r with
    | zero => intro m f; simp
    | succ r ih =>
      intro m f
      rw [show m + (r + 1) = (m + r) + 1 by omega, pow_succ', mul_assoc, coeff_succ_X_mul, ih]
  have hsub := hshift j (k - j) (Q ^ (k - j))
  rw [Nat.sub_add_cancel (by omega)] at hsub
  rw [hsub]

private lemma c_eq_coeff_Q_pow (k : ℕ) :
    (OMA.S_oeis_a023688.c k : ℚ) = coeff k ((P_odd ^ 24) ^ k) := by
  unfold OMA.S_oeis_a023688.c
  rw [← pow_mul]
  unfold P_odd
  rw [infProd_pow hP_odd_mod (24 * k)]
  have hmod : ∀ m, coeff 0 ((1 + C (1 : ℚ) * X ^ (2 * m + 1)) ^ (24 * k)) = 1 ∧
      ∀ j, 1 ≤ j → j ≤ m → coeff j ((1 + C (1 : ℚ) * X ^ (2 * m + 1)) ^ (24 * k)) = 0 :=
    fun m => one_mod_pow (hP_odd_mod m).1 (hP_odd_mod m).2 (24 * k)
  rw [coeff_infProd_eq hmod (le_refl k)]
  -- Map Polynomial ℤ -> PowerSeries ℚ
  let φ : Polynomial ℤ →+* PowerSeries ℚ :=
    (PowerSeries.map (Int.castRingHom ℚ)).comp (Polynomial.coeToPowerSeries.ringHom)
  have hcoeff : ∀ (p : Polynomial ℤ) (n : ℕ), (p.coeff n : ℚ) = coeff n (φ p) := by
    intro p n
    simp [φ, PowerSeries.coeff_map, Polynomial.coeff_coe]
  rw [hcoeff]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro m _
  simp [φ, map_pow, map_add, map_one, Polynomial.coe_X]

private lemma dvd_24_c {k : ℕ} (hk : 1 ≤ k) : (24 : ℤ) ∣ OMA.S_oeis_a023688.c k := by
  unfold OMA.S_oeis_a023688.c
  set P : Polynomial ℤ := ∏ m ∈ Finset.range k, (1 + Polynomial.X ^ (2 * m + 1) : Polynomial ℤ)
  have hprod : (∏ m ∈ Finset.range k, (1 + Polynomial.X ^ (2 * m + 1) : Polynomial ℤ) ^ (24 * k)) =
      P ^ (24 * k) := by
    rw [← Finset.prod_pow]
  rw [hprod]
  have hd : Polynomial.derivative (P ^ (24 * k)) =
      Polynomial.C ((24 * k : ℕ) : ℤ) * P ^ (24 * k - 1) * Polynomial.derivative P := by
    rw [Polynomial.derivative_pow]
  have hc := congrArg (fun q => q.coeff (k - 1)) hd
  rw [Polynomial.coeff_derivative] at hc
  have hsub : k - 1 + 1 = k := by omega
  have hnat : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by omega
  rw [hsub, hnat, mul_assoc, Polynomial.coeff_C_mul] at hc
  have hk_ne : (k : ℤ) ≠ 0 := by omega
  have hcancel : (P ^ (24 * k)).coeff k = 24 * (P ^ (24 * k - 1) * Polynomial.derivative P).coeff (k - 1) := by
    apply mul_left_cancel₀ hk_ne
    have hmul : (k : ℤ) * (P ^ (24 * k)).coeff k = (P ^ (24 * k)).coeff k * (k : ℤ) := mul_comm _ _
    rw [hmul, hc]
    push_cast
    ring
  exact ⟨(P ^ (24 * k - 1) * Polynomial.derivative P).coeff (k - 1), hcancel⟩



/-! ### Part 2B: Finite `q`-binomial Jacobi Triple Product, AGM identities, Landen & Clausen ODEs -/

private def qBinom : ℕ → ℕ → PowerSeries ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => 1
  | n + 1, k + 1 => qBinom n (k + 1) + X ^ (2 * (n - k)) * qBinom n k

private lemma qBinom_zero_right (n : ℕ) : qBinom n 0 = 1 := by
  cases n <;> rfl

private lemma qBinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → qBinom n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    dsimp only [qBinom]
    rw [qBinom_eq_zero_of_lt (show n < k + 1 by omega),
      qBinom_eq_zero_of_lt (show n < k by omega), mul_zero, add_zero]

private lemma qBinom_self : ∀ n : ℕ, qBinom n n = 1
  | 0 => rfl
  | n + 1 => by
    dsimp only [qBinom]
    rw [qBinom_eq_zero_of_lt (by omega), Nat.sub_self, mul_zero, pow_zero, one_mul,
      zero_add, qBinom_self n]

private lemma qBinom_prod : ∀ (n r : ℕ), r ≤ n →
    qBinom n r * (∏ j ∈ Finset.range r, (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ)) =
      ∏ j ∈ Finset.range r, (1 - X ^ (2 * (n - r + j + 1)) : PowerSeries ℚ)
  | 0, r, hr => by
    have h0 : r = 0 := by omega
    subst h0; simp [qBinom]
  | n + 1, 0, _ => by simp [qBinom_zero_right]
  | n + 1, k + 1, hk => by
    by_cases hkn : k = n
    · subst hkn
      rw [qBinom_self, one_mul]
      apply Finset.prod_congr rfl
      intro j _
      simp
    · have hk_lt : k + 1 ≤ n := by omega
      dsimp only [qBinom]
      rw [add_mul]
      have h1 : qBinom n (k + 1) * ∏ j ∈ Finset.range (k + 1), (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ) =
          (1 - X ^ (2 * (n - k))) * ∏ j ∈ Finset.range k, (1 - X ^ (2 * (n - k + j + 1)) : PowerSeries ℚ) := by
        rw [qBinom_prod n (k + 1) hk_lt, Finset.prod_range_succ']
        rw [mul_comm]
        congr 1
        · congr 1; congr 1; omega
        · apply Finset.prod_congr rfl
          intro j _
          congr 1; congr 1; omega
      have h2 : X ^ (2 * (n - k)) * qBinom n k *
            ∏ j ∈ Finset.range (k + 1), (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ) =
          X ^ (2 * (n - k)) * (1 - X ^ (2 * (k + 1))) *
            ∏ j ∈ Finset.range k, (1 - X ^ (2 * (n - k + j + 1)) : PowerSeries ℚ) := by
        rw [Finset.prod_range_succ]
        calc X ^ (2 * (n - k)) * qBinom n k *
              ((∏ j ∈ Finset.range k, (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ)) * (1 - X ^ (2 * (k + 1))))
            = X ^ (2 * (n - k)) * (1 - X ^ (2 * (k + 1))) *
              (qBinom n k * ∏ j ∈ Finset.range k, (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ)) := by ring
          _ = X ^ (2 * (n - k)) * (1 - X ^ (2 * (k + 1))) *
              ∏ j ∈ Finset.range k, (1 - X ^ (2 * (n - k + j + 1)) : PowerSeries ℚ) := by
                rw [qBinom_prod n k (by omega)]
      rw [h1, h2, ← add_mul, Finset.prod_range_succ]
      rw [mul_comm _ (1 - X ^ (2 * (n + 1 - (k + 1) + k + 1)) : PowerSeries ℚ)]
      congr 1
      · have hpow : (X : PowerSeries ℚ) ^ (2 * (n - k)) * X ^ (2 * (k + 1)) =
            X ^ (2 * (n + 1 - (k + 1) + k + 1)) := by
          rw [← pow_add]; congr 1; omega
        calc ((1 : PowerSeries ℚ) - X ^ (2 * (n - k))) + X ^ (2 * (n - k)) * (1 - X ^ (2 * (k + 1)))
            = (1 : PowerSeries ℚ) - X ^ (2 * (n - k)) * X ^ (2 * (k + 1)) := by ring
          _ = (1 : PowerSeries ℚ) - X ^ (2 * (n + 1 - (k + 1) + k + 1)) := by rw [hpow]
      · apply Finset.prod_congr rfl
        intro j _
        congr 1; congr 1; omega

private lemma prod_one_sub_X_pow_ne_zero (r : ℕ) :
    (∏ j ∈ Finset.range r, (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ)) ≠ 0 := by
  intro hz
  have hc := congrArg constantCoeff hz
  rw [map_prod, map_zero] at hc
  have h1 : ∀ j ∈ Finset.range r, constantCoeff (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ) = 1 := by
    intro j _
    rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero]
  rw [Finset.prod_eq_one h1] at hc
  exact one_ne_zero hc

private lemma qBinom_symm {n r : ℕ} (hr : r ≤ n) : qBinom n (n - r) = qBinom n r := by
  set P : ℕ → PowerSeries ℚ := fun m => ∏ j ∈ Finset.range m, (1 - X ^ (2 * (j + 1)) : PowerSeries ℚ)
  have hP : P (n - r) * P r ≠ 0 := mul_ne_zero (prod_one_sub_X_pow_ne_zero _) (prod_one_sub_X_pow_ne_zero _)
  have hsplit : ∀ a b : ℕ, P a * (∏ j ∈ Finset.range b, (1 - X ^ (2 * (a + j + 1)) : PowerSeries ℚ)) = P (a + b) := by
    intro a b
    induction b with
    | zero => simp [P]
    | succ b ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, show a + (b + 1) = (a + b) + 1 by omega]
      dsimp only [P]
      rw [Finset.prod_range_succ]
  apply mul_right_cancel₀ hP
  have hlhs : qBinom n (n - r) * (P (n - r) * P r) = P n := by
    calc qBinom n (n - r) * (P (n - r) * P r)
        = P r * (qBinom n (n - r) * P (n - r)) := by ring
      _ = P r * ∏ j ∈ Finset.range (n - r), (1 - X ^ (2 * (n - (n - r) + j + 1)) : PowerSeries ℚ) := by
          rw [qBinom_prod n (n - r) (by omega)]
      _ = P r * ∏ j ∈ Finset.range (n - r), (1 - X ^ (2 * (r + j + 1)) : PowerSeries ℚ) := by
          congr 1; apply Finset.prod_congr rfl; intro j _; congr 1; congr 1; omega
      _ = P (r + (n - r)) := hsplit r (n - r)
      _ = P n := by rw [Nat.add_sub_of_le hr]
  have hrhs : qBinom n r * (P (n - r) * P r) = P n := by
    calc qBinom n r * (P (n - r) * P r)
        = P (n - r) * (qBinom n r * P r) := by ring
      _ = P (n - r) * ∏ j ∈ Finset.range r, (1 - X ^ (2 * (n - r + j + 1)) : PowerSeries ℚ) := by
          rw [qBinom_prod n r hr]
      _ = P ((n - r) + r) := hsplit (n - r) r
      _ = P n := by rw [Nat.sub_add_cancel hr]
  exact hlhs.trans hrhs.symm

private lemma qBinom_succ_right (n k : ℕ) :
    qBinom (n + 1) (k + 1) = X ^ (2 * (k + 1)) * qBinom n (k + 1) + qBinom n k := by
  by_cases hkn : k < n
  · have h1 : qBinom (n + 1) (k + 1) = qBinom (n + 1) (n - k) := by
      rw [← qBinom_symm (show k + 1 ≤ n + 1 by omega)]
      congr 1; omega
    have h2 : n - k = (n - k - 1) + 1 := by omega
    rw [h1, h2]
    dsimp only [qBinom]
    have h3 : n - (n - k - 1) = k + 1 := by omega
    have h4 : qBinom n (n - k - 1 + 1) = qBinom n k := by
      rw [← qBinom_symm (show k ≤ n by omega)]
      congr 1; omega
    have h5 : qBinom n (n - k - 1) = qBinom n (k + 1) := by
      have hsub : n - (k + 1) = n - k - 1 := by omega
      rw [← hsub, qBinom_symm (show k + 1 ≤ n by omega)]
    rw [h3, h4, h5, add_comm]
  · by_cases heq : k = n
    · subst heq
      rw [qBinom_self, qBinom_self, qBinom_eq_zero_of_lt (by omega), mul_zero, zero_add]
    · rw [qBinom_eq_zero_of_lt (by omega), qBinom_eq_zero_of_lt (by omega),
        qBinom_eq_zero_of_lt (by omega), mul_zero, add_zero]

private lemma qVandermonde (A B K : ℕ) :
    ∑ r ∈ Finset.range (K + 1),
      qBinom A r * qBinom B (K - r) * X ^ (2 * r * (B - (K - r))) = qBinom (A + B) K := by
  induction B generalizing K with
  | zero =>
    rw [add_zero]
    have hmem : K ∈ Finset.range (K + 1) := by rw [Finset.mem_range]; omega
    rw [Finset.sum_eq_single K]
    · simp [qBinom_zero_right]
    · intro r hr hne
      rw [Finset.mem_range] at hr
      rw [qBinom_eq_zero_of_lt (show 0 < K - r by omega), mul_zero, zero_mul]
    · intro h; exact absurd hmem h
  | succ B ih =>
    rcases K with _ | K
    · simp [qBinom_zero_right]
    · rw [show A + (B + 1) = (A + B) + 1 by omega, qBinom_succ_right,
        ← ih (K + 1), ← ih K, Finset.mul_sum]
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun r => X ^ (2 * (K + 1)) * _)]
      have hlast : qBinom A (K + 1) * qBinom (B + 1) (K + 1 - (K + 1)) *
            X ^ (2 * (K + 1) * (B + 1 - (K + 1 - (K + 1)))) =
          X ^ (2 * (K + 1)) * (qBinom A (K + 1) * qBinom B (K + 1 - (K + 1)) *
            X ^ (2 * (K + 1) * (B - (K + 1 - (K + 1))))) := by
        simp only [Nat.sub_self, Nat.sub_zero, qBinom_zero_right, mul_one]
        have hp : (X : PowerSeries ℚ) ^ (2 * (K + 1) * (B + 1)) =
            X ^ (2 * (K + 1)) * X ^ (2 * (K + 1) * B) := by
          rw [← pow_add]; congr 1; ring
        rw [hp]; ring
      rw [hlast]
      have hmain : ∑ r ∈ Finset.range (K + 1),
            qBinom A r * qBinom (B + 1) (K + 1 - r) * X ^ (2 * r * (B + 1 - (K + 1 - r))) =
          (∑ r ∈ Finset.range (K + 1), X ^ (2 * (K + 1)) *
            (qBinom A r * qBinom B (K + 1 - r) * X ^ (2 * r * (B - (K + 1 - r))))) +
          ∑ r ∈ Finset.range (K + 1),
            qBinom A r * qBinom B (K - r) * X ^ (2 * r * (B - (K - r))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mem_range] at hr
        have hsub : K + 1 - r = (K - r) + 1 := by omega
        rw [hsub, qBinom_succ_right, mul_add, add_mul]
        congr 1
        · by_cases hle : K - r + 1 ≤ B
          · have hp : (X : PowerSeries ℚ) ^ (2 * (K - r + 1)) *
                X ^ (2 * r * (B + 1 - (K - r + 1))) =
                X ^ (2 * (K + 1)) * X ^ (2 * r * (B - (K - r + 1))) := by
              rw [← pow_add, ← pow_add]; congr 1
              have h1 : B + 1 - (K - r + 1) = B - (K - r + 1) + 1 := by omega
              rw [h1]
              have h2 : K - r + 1 + r = K + 1 := by omega
              nlinarith
            calc qBinom A r * (X ^ (2 * (K - r + 1)) * qBinom B (K - r + 1)) *
                  X ^ (2 * r * (B + 1 - (K - r + 1)))
                = qBinom A r * qBinom B (K - r + 1) *
                  (X ^ (2 * (K - r + 1)) * X ^ (2 * r * (B + 1 - (K - r + 1)))) := by ring
              _ = qBinom A r * qBinom B (K - r + 1) *
                  (X ^ (2 * (K + 1)) * X ^ (2 * r * (B - (K - r + 1)))) := by rw [hp]
              _ = X ^ (2 * (K + 1)) * (qBinom A r * qBinom B (K - r + 1) *
                  X ^ (2 * r * (B - (K - r + 1)))) := by ring
          · rw [qBinom_eq_zero_of_lt (show B < K - r + 1 by omega)]
            ring
        · have hb : B + 1 - (K - r + 1) = B - (K - r) := by omega
          rw [hb]
      rw [hmain]
      ring

private lemma finite_qbinom_thm (u : PowerSeries ℚ) (N : ℕ) :
    ∏ j ∈ Finset.range N, (1 + u * X ^ (2 * j + 1) : PowerSeries ℚ) =
      ∑ r ∈ Finset.range (N + 1), qBinom N r * X ^ (r * r) * u ^ r := by
  induction N with
  | zero => simp [qBinom]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]
    rw [Finset.sum_range_succ' (fun r => qBinom (N + 1) r * X ^ (r * r) * u ^ r),
      Finset.sum_range_succ (fun r => qBinom (N + 1) (r + 1) * X ^ ((r + 1) * (r + 1)) * u ^ (r + 1)),
      Finset.sum_range_succ' (fun r => qBinom N r * X ^ (r * r) * u ^ r),
      Finset.sum_range_succ (fun r => qBinom N r * X ^ (r * r) * u ^ r * (u * X ^ (2 * N + 1)))]
    simp only [qBinom_zero_right, qBinom_self, mul_zero, pow_zero, one_mul, mul_one]
    have hmid : ∑ k ∈ Finset.range N, qBinom (N + 1) (k + 1) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1) =
        (∑ k ∈ Finset.range N, qBinom N (k + 1) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1)) +
        ∑ k ∈ Finset.range N, qBinom N k * X ^ (k * k) * u ^ k * (u * X ^ (2 * N + 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      dsimp only [qBinom]
      have hp : (X : PowerSeries ℚ) ^ (2 * (N - k)) * X ^ ((k + 1) * (k + 1)) =
          X ^ (k * k) * X ^ (2 * N + 1) := by
        rw [← pow_add, ← pow_add]; congr 1
        have h1 : 2 * (N - k) + 2 * k = 2 * N := by omega
        nlinarith
      calc (qBinom N (k + 1) + X ^ (2 * (N - k)) * qBinom N k) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1)
          = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1) +
            qBinom N k * (X ^ (2 * (N - k)) * X ^ ((k + 1) * (k + 1))) * (u ^ k * u) := by
              rw [pow_succ]; ring
        _ = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1) +
            qBinom N k * (X ^ (k * k) * X ^ (2 * N + 1)) * (u ^ k * u) := by rw [hp]
        _ = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1)) * u ^ (k + 1) +
            qBinom N k * X ^ (k * k) * u ^ k * (u * X ^ (2 * N + 1)) := by ring
    have htop : (X : PowerSeries ℚ) ^ (N * N) * u ^ N * (u * X ^ (2 * N + 1)) =
        X ^ ((N + 1) * (N + 1)) * u ^ (N + 1) := by
      have hp : (X : PowerSeries ℚ) ^ (N * N) * X ^ (2 * N + 1) = X ^ ((N + 1) * (N + 1)) := by
        rw [← pow_add]; congr 1; ring
      rw [pow_succ]; calc X ^ (N * N) * u ^ N * (u * X ^ (2 * N + 1))
          = (X ^ (N * N) * X ^ (2 * N + 1)) * (u ^ N * u) := by ring
        _ = X ^ ((N + 1) * (N + 1)) * (u ^ N * u) := by rw [hp]
    rw [hmid, htop]
    ring

private lemma finite_qbinom_shift (N : ℕ) :
    ∏ j ∈ Finset.range N, (1 + X ^ (2 * j) : PowerSeries ℚ) =
      ∑ s ∈ Finset.range (N + 1), qBinom N s * X ^ (s * s - s) := by
  induction N with
  | zero => simp [qBinom]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]
    rw [Finset.sum_range_succ' (fun s => qBinom (N + 1) s * _),
      Finset.sum_range_succ (fun s => qBinom (N + 1) (s + 1) * _),
      Finset.sum_range_succ' (fun s => qBinom N s * X ^ (s * s - s)),
      Finset.sum_range_succ (fun s => qBinom N s * X ^ (s * s - s) * X ^ (2 * N))]
    simp only [qBinom_zero_right, qBinom_self, mul_zero, Nat.sub_self, pow_zero, one_mul]
    have hmid : ∑ k ∈ Finset.range N, qBinom (N + 1) (k + 1) * X ^ ((k + 1) * (k + 1) - (k + 1)) =
        (∑ k ∈ Finset.range N, qBinom N (k + 1) * X ^ ((k + 1) * (k + 1) - (k + 1))) +
        ∑ k ∈ Finset.range N, qBinom N k * X ^ (k * k - k) * X ^ (2 * N) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      dsimp only [qBinom]
      have hp : (X : PowerSeries ℚ) ^ (2 * (N - k)) * X ^ ((k + 1) * (k + 1) - (k + 1)) =
          X ^ (k * k - k) * X ^ (2 * N) := by
        rw [← pow_add, ← pow_add]; congr 1
        have hk1 : k ≤ k * k := Nat.le_mul_self k
        have hk2 : k + 1 ≤ (k + 1) * (k + 1) := Nat.le_mul_self (k + 1)
        have hkn : k ≤ N := by omega
        zify [hk1, hk2, hkn]
        ring
      calc (qBinom N (k + 1) + X ^ (2 * (N - k)) * qBinom N k) * X ^ ((k + 1) * (k + 1) - (k + 1))
          = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1) - (k + 1)) +
            qBinom N k * (X ^ (2 * (N - k)) * X ^ ((k + 1) * (k + 1) - (k + 1))) := by ring
        _ = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1) - (k + 1)) +
            qBinom N k * (X ^ (k * k - k) * X ^ (2 * N)) := by rw [hp]
        _ = qBinom N (k + 1) * X ^ ((k + 1) * (k + 1) - (k + 1)) +
            qBinom N k * X ^ (k * k - k) * X ^ (2 * N) := by ring
    have htop : (X : PowerSeries ℚ) ^ (N * N - N) * X ^ (2 * N) =
        X ^ ((N + 1) * (N + 1) - (N + 1)) := by
      rw [← pow_add]; congr 1
      have hN1 : N ≤ N * N := Nat.le_mul_self N
      have hN2 : N + 1 ≤ (N + 1) * (N + 1) := Nat.le_mul_self (N + 1)
      zify [hN1, hN2]; ring
    rw [hmid, htop]
    ring

private lemma finite_jtp_unit (c : ℚ) (hc : c * c = 1) (N : ℕ) :
    (∏ j ∈ Finset.range N, (1 + C c * X ^ (2 * j + 1) : PowerSeries ℚ)) ^ 2 =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        C (c ^ k.natAbs) * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat := by
  rw [sq, finite_qbinom_thm (C c) N, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product']
  -- Partition (range (N+1) × range (N+1)) by k = r - s ∈ Icc (-N) N
  have hgroup : ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        qBinom N p.1 * X ^ (p.1 * p.1) * (C c) ^ p.1 * (qBinom N p.2 * X ^ (p.2 * p.2) * (C c) ^ p.2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = k),
          qBinom N p.1 * X ^ (p.1 * p.1) * (C c) ^ p.1 * (qBinom N p.2 * X ^ (p.2 * p.2) * (C c) ^ p.2) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))]
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_Icc]; omega
  rw [hgroup]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  set K : ℕ := (N + k).toNat
  have hK : (K : ℤ) = (N : ℤ) + k := Int.toNat_of_nonneg (by omega)
  have hK_le : K ≤ 2 * N := by omega
  -- Rewrite RHS using qVandermonde N N K
  rw [show 2 * N = N + N by omega, ← qVandermonde N N K, Finset.mul_sum, Finset.sum_mul]
  -- Filter qVandermonde sum to r with r ≤ N and K - r ≤ N (outside qBinom vanishes)
  have hvand : ∑ r ∈ Finset.range (K + 1),
        C (c ^ k.natAbs) * (qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r)))) * X ^ (k * k).toNat =
      ∑ r ∈ (Finset.range (K + 1)).filter (fun r => r ≤ N ∧ K - r ≤ N),
        C (c ^ k.natAbs) * (qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r)))) * X ^ (k * k).toNat := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (K + 1)) (fun r => r ≤ N ∧ K - r ≤ N)]
    have h0 : ∑ r ∈ (Finset.range (K + 1)).filter (fun r => ¬ (r ≤ N ∧ K - r ≤ N)),
        C (c ^ k.natAbs) * (qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r)))) * X ^ (k * k).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_filter] at hr
      by_cases h1 : r ≤ N
      · have h2 : N < K - r := by omega
        rw [qBinom_eq_zero_of_lt h2]; ring
      · rw [qBinom_eq_zero_of_lt (show N < r by omega)]; ring
    rw [h0, add_zero]
  rw [hvand]
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, by omega⟩
  · intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
    exact Prod.ext h (by omega)
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    refine ⟨(r, N - (K - r)), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have hq2 : qBinom N (K - p.1) = qBinom N p.2 := by
      rw [← qBinom_symm (show p.2 ≤ N by omega)]
      congr 1; omega
    have hsub : N - (K - p.1) = p.2 := by omega
    have hcpow : (C c : PowerSeries ℚ) ^ p.1 * (C c) ^ p.2 = C (c ^ k.natAbs) := by
      rw [← map_pow, ← map_pow, ← map_mul, ← pow_add]
      congr 1
      have hpar : p.1 + p.2 = k.natAbs + 2 * min p.1 p.2 := by
        have hkabs : (k.natAbs : ℤ) = |(p.1 : ℤ) - (p.2 : ℤ)| := by
          rw [← hp.2]; exact Int.natCast_natAbs _
        have : k.natAbs = (if p.1 ≥ p.2 then p.1 - p.2 else p.2 - p.1) := by
          split_ifs <;> omega
        rw [this]; split_ifs <;> omega
      rw [hpar, pow_add, pow_mul, show c ^ 2 = 1 by rw [sq]; exact hc, one_pow, mul_one]
    have hxpow : (X : PowerSeries ℚ) ^ (p.1 * p.1) * X ^ (p.2 * p.2) =
        X ^ (2 * p.1 * p.2) * X ^ (k * k).toNat := by
      rw [← pow_add, ← pow_add]; congr 1
      have hk2 : ((k * k).toNat : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
      zify; rw [hk2, ← hp.2]; ring
    rw [hq2, hsub]
    calc qBinom N p.1 * X ^ (p.1 * p.1) * C c ^ p.1 * (qBinom N p.2 * X ^ (p.2 * p.2) * C c ^ p.2)
        = (C c ^ p.1 * C c ^ p.2) * (qBinom N p.1 * qBinom N p.2) * (X ^ (p.1 * p.1) * X ^ (p.2 * p.2)) := by ring
      _ = C (c ^ k.natAbs) * (qBinom N p.1 * qBinom N p.2) * (X ^ (2 * p.1 * p.2) * X ^ (k * k).toNat) := by
          rw [hcpow, hxpow]
      _ = C (c ^ k.natAbs) * (qBinom N p.1 * qBinom N p.2 * X ^ (2 * p.1 * p.2)) * X ^ (k * k).toNat := by ring

private lemma finite_jtp_X (N : ℕ) :
    (∏ j ∈ Finset.range N, (1 + X ^ (2 * (j + 1)) : PowerSeries ℚ)) *
      (∏ j ∈ Finset.range N, (1 + X ^ (2 * j) : PowerSeries ℚ)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        qBinom (2 * N) (N + k).toNat * X ^ (k * k + k).toNat := by
  have hfirst : (∏ j ∈ Finset.range N, (1 + X ^ (2 * (j + 1)) : PowerSeries ℚ)) =
      ∑ r ∈ Finset.range (N + 1), qBinom N r * X ^ (r * r + r) := by
    have h1 := finite_qbinom_thm X N
    have hprod : (∏ j ∈ Finset.range N, (1 + X ^ (2 * (j + 1)) : PowerSeries ℚ)) =
        ∏ j ∈ Finset.range N, (1 + X * X ^ (2 * j + 1) : PowerSeries ℚ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← pow_succ', show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
    rw [hprod, h1]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_assoc, ← pow_add]
  rw [hfirst, finite_qbinom_shift N, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product']
  have hgroup : ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        qBinom N p.1 * X ^ (p.1 * p.1 + p.1) * (qBinom N p.2 * X ^ (p.2 * p.2 - p.2)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = k),
          qBinom N p.1 * X ^ (p.1 * p.1 + p.1) * (qBinom N p.2 * X ^ (p.2 * p.2 - p.2)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))]
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_Icc]; omega
  rw [hgroup]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  set K : ℕ := (N + k).toNat
  have hK : (K : ℤ) = (N : ℤ) + k := Int.toNat_of_nonneg (by omega)
  rw [show 2 * N = N + N by omega, ← qVandermonde N N K, Finset.sum_mul]
  have hvand : ∑ r ∈ Finset.range (K + 1),
        qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r))) * X ^ (k * k + k).toNat =
      ∑ r ∈ (Finset.range (K + 1)).filter (fun r => r ≤ N ∧ K - r ≤ N),
        qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r))) * X ^ (k * k + k).toNat := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (K + 1)) (fun r => r ≤ N ∧ K - r ≤ N)]
    have h0 : ∑ r ∈ (Finset.range (K + 1)).filter (fun r => ¬ (r ≤ N ∧ K - r ≤ N)),
        qBinom N r * qBinom N (K - r) * X ^ (2 * r * (N - (K - r))) * X ^ (k * k + k).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_filter] at hr
      by_cases h1 : r ≤ N
      · rw [qBinom_eq_zero_of_lt (show N < K - r by omega)]; ring
      · rw [qBinom_eq_zero_of_lt (show N < r by omega)]; ring
    rw [h0, add_zero]
  rw [hvand]
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, by omega⟩
  · intro p₁ hp₁ p₂ hp₂ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
    exact Prod.ext h (by omega)
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    refine ⟨(r, N - (K - r)), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have hq2 : qBinom N (K - p.1) = qBinom N p.2 := by
      rw [← qBinom_symm (show p.2 ≤ N by omega)]
      congr 1; omega
    have hsub : N - (K - p.1) = p.2 := by omega
    have hxpow : (X : PowerSeries ℚ) ^ (p.1 * p.1 + p.1) * X ^ (p.2 * p.2 - p.2) =
        X ^ (2 * p.1 * p.2) * X ^ (k * k + k).toNat := by
      rw [← pow_add, ← pow_add]; congr 1
      have hp2 : p.2 ≤ p.2 * p.2 := Nat.le_mul_self p.2
      have hkn : 0 ≤ k * k + k := by nlinarith [sq_nonneg k]
      have hk2 : ((k * k + k).toNat : ℤ) = k * k + k := Int.toNat_of_nonneg hkn
      zify [hp2]; rw [hk2, ← hp.2]; ring
    rw [hq2, hsub]
    calc qBinom N p.1 * X ^ (p.1 * p.1 + p.1) * (qBinom N p.2 * X ^ (p.2 * p.2 - p.2))
        = qBinom N p.1 * qBinom N p.2 * (X ^ (p.1 * p.1 + p.1) * X ^ (p.2 * p.2 - p.2)) := by ring
      _ = qBinom N p.1 * qBinom N p.2 * (X ^ (2 * p.1 * p.2) * X ^ (k * k + k).toNat) := by rw [hxpow]
      _ = qBinom N p.1 * qBinom N p.2 * X ^ (2 * p.1 * p.2) * X ^ (k * k + k).toNat := by ring

/-! #### Limit of `E_even * qBinom (2*N) r` modulo `X^(n+1)` -/

private lemma coeff_E_even_mul_qBinom {n N r : ℕ} (hr1 : n ≤ r) (hr2 : n + r ≤ 2 * N) :
    ∀ m ≤ n, coeff m (E_even * qBinom (2 * N) r) = coeff m 1 := by
  intro m hm
  have hE : ∀ j ≤ m, coeff j E_even = coeff j (∏ i ∈ Finset.range r, (1 - X ^ (2 * (i + 1)) : PowerSeries ℚ)) := by
    intro j hj
    unfold E_even
    rw [coeff_infProd_eq hE_even_mod (show j ≤ r by omega)]
    congr 1; apply Finset.prod_congr rfl; intro i _; rw [show (1 : PowerSeries ℚ) + C (-1) * X ^ (2 * (i + 1)) = 1 - X ^ (2 * (i + 1)) by simp [sub_eq_add_neg]]
  rw [coeff_mul_congr hE (fun _ _ => rfl), mul_comm, qBinom_prod (2 * N) r (by omega)]
  have hprod_mod : ∀ s : ℕ, coeff 0 (∏ i ∈ Finset.range s, (1 - X ^ (2 * (2 * N - r + i + 1)) : PowerSeries ℚ)) = 1 ∧
      ∀ k, 1 ≤ k → k ≤ n → coeff k (∏ i ∈ Finset.range s, (1 - X ^ (2 * (2 * N - r + i + 1)) : PowerSeries ℚ)) = 0 := by
    intro s
    induction s with
    | zero =>
      refine ⟨by simp [coeff_one], fun k hk1 _ => by rw [Finset.prod_range_zero, coeff_one]; exact if_neg (by omega)⟩
    | succ s ih =>
      rw [Finset.prod_range_succ]
      have hfac := one_mod_one_add_X_pow (-1 : ℚ) (d := 2 * (2 * N - r + s + 1)) (m := n) (by omega)
      have hrew : (1 : PowerSeries ℚ) - X ^ (2 * (2 * N - r + s + 1)) =
          1 + C (-1 : ℚ) * X ^ (2 * (2 * N - r + s + 1)) := by simp [sub_eq_add_neg]
      rw [hrew]
      exact one_mod_mul ih.1 ih.2 hfac.1 hfac.2
  rcases Nat.eq_zero_or_pos m with rfl | hmp
  · rw [(hprod_mod r).1, coeff_one]; simp
  · rw [(hprod_mod r).2 m hmp hm, coeff_one]; exact (if_neg (by omega)).symm

/-! #### Theta series `T3`, `T4`, `T2'` and Jacobi Triple Product -/

private def T3 : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (((Finset.Icc (-(n : ℤ)) n).filter (fun k => k * k = (n : ℤ))).card : ℚ))

private def T4 : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (-1 : ℚ) ^ n * coeff n T3)

private def T2' : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (((Finset.Icc (-(n : ℤ) - 1) n).filter (fun k => k * k + k = (n : ℤ))).card : ℚ))

private lemma neg_one_pow_natAbs_eq_sq (k : ℤ) : (-1 : ℚ) ^ k.natAbs = (-1 : ℚ) ^ (k * k).toNat := by
  have hsq : (k * k).toNat = k.natAbs * k.natAbs := by
    have : ((k * k).toNat : ℤ) = (k.natAbs * k.natAbs : ℕ) := by
      rw [Int.toNat_of_nonneg (mul_self_nonneg k)]
      push_cast
      rw [abs_mul_abs_self]
    exact_mod_cast this
  rw [hsq]
  rcases Nat.even_or_odd k.natAbs with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show (m + m) * (m + m) = 2 * (2 * m * m) by ring, show m + m = 2 * m by ring]
    simp [pow_mul]
  · rw [hm, show (2 * m + 1) * (2 * m + 1) = 2 * (2 * m * m + 2 * m) + 1 by ring]
    simp [pow_succ, pow_mul]

private lemma T3_eq_prod : T3 = E_even * P_odd ^ 2 := by
  ext n
  set N : ℕ := 2 * n + 2
  have hP : ∀ j ≤ n, coeff j (P_odd ^ 2) =
      coeff j ((∏ m ∈ Finset.range N, (1 + C (1 : ℚ) * X ^ (2 * m + 1))) ^ 2) := by
    intro j hj
    rw [sq, sq]
    apply coeff_mul_congr
    · intro i hi; unfold P_odd; exact coeff_infProd_eq hP_odd_mod (by omega)
    · intro i hi; unfold P_odd; exact coeff_infProd_eq hP_odd_mod (by omega)
  rw [coeff_mul_congr (fun _ _ => rfl) hP, finite_jtp_unit 1 (by norm_num) N, Finset.mul_sum, map_sum]
  have hterm : ∀ k ∈ Finset.Icc (-(N : ℤ)) N,
      coeff n (E_even * (C ((1 : ℚ) ^ k.natAbs) * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat)) =
      if k * k = (n : ℤ) then (1 : ℚ) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [one_pow, map_one, one_mul, ← mul_assoc]
    by_cases hbig : n < (k * k).toNat
    · have h0 : coeff n (E_even * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat) = 0 := by
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (E_even * qBinom (2 * N) (N + k).toNat) * coeff j (X ^ (k * k).toNat))]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeff_X_pow, if_neg (by omega), mul_zero]
      rw [h0, if_neg]
      intro heq
      have : (k * k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
      omega
    · have hk_le : -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) := by
        have : (k * k).toNat ≤ n := by omega
        have hkk : k * k ≤ (n : ℤ) := by
          have := Int.toNat_of_nonneg (mul_self_nonneg k)
          omega
        constructor <;> nlinarith
      have h1 := coeff_E_even_mul_qBinom (n := n) (N := N) (r := (N + k).toNat) (by omega) (by omega)
      rw [coeff_mul_congr h1 (fun _ _ => rfl), one_mul, coeff_X_pow]
      by_cases heq : k * k = (n : ℤ)
      · have htn : (k * k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
        rw [if_pos htn.symm, if_pos heq]
      · have htn : n ≠ (k * k).toNat := by
          intro h; apply heq
          have := Int.toNat_of_nonneg (mul_self_nonneg k)
          omega
        rw [if_neg htn, if_neg heq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  unfold T3
  rw [coeff_mk]
  congr 2
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by omega, by omega⟩, hkk⟩
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hkk⟩

private lemma T4_eq_prod : T4 = E_even * M_odd ^ 2 := by
  ext n
  set N : ℕ := 2 * n + 2
  have hM : ∀ j ≤ n, coeff j (M_odd ^ 2) =
      coeff j ((∏ m ∈ Finset.range N, (1 + C (-1 : ℚ) * X ^ (2 * m + 1))) ^ 2) := by
    intro j hj
    rw [sq, sq]
    apply coeff_mul_congr
    · intro i hi; unfold M_odd; exact coeff_infProd_eq hM_odd_mod (by omega)
    · intro i hi; unfold M_odd; exact coeff_infProd_eq hM_odd_mod (by omega)
  rw [coeff_mul_congr (fun _ _ => rfl) hM, finite_jtp_unit (-1) (by norm_num) N, Finset.mul_sum, map_sum]
  have hterm : ∀ k ∈ Finset.Icc (-(N : ℤ)) N,
      coeff n (E_even * (C ((-1 : ℚ) ^ k.natAbs) * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat)) =
      if k * k = (n : ℤ) then (-1 : ℚ) ^ n else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hpull : E_even * (C ((-1 : ℚ) ^ k.natAbs) * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat) =
        C ((-1 : ℚ) ^ k.natAbs) * (E_even * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat) := by ring
    rw [hpull, coeff_C_mul]
    by_cases hbig : n < (k * k).toNat
    · have h0 : coeff n (E_even * qBinom (2 * N) (N + k).toNat * X ^ (k * k).toNat) = 0 := by
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (E_even * qBinom (2 * N) (N + k).toNat) * coeff j (X ^ (k * k).toNat))]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeff_X_pow, if_neg (by omega), mul_zero]
      rw [h0, mul_zero, if_neg]
      intro heq
      have : (k * k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
      omega
    · have hk_le : -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) := by
        have : (k * k).toNat ≤ n := by omega
        have hkk : k * k ≤ (n : ℤ) := by
          have := Int.toNat_of_nonneg (mul_self_nonneg k)
          omega
        constructor <;> nlinarith
      have h1 := coeff_E_even_mul_qBinom (n := n) (N := N) (r := (N + k).toNat) (by omega) (by omega)
      rw [coeff_mul_congr h1 (fun _ _ => rfl), one_mul, coeff_X_pow]
      by_cases heq : k * k = (n : ℤ)
      · have htn : (k * k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
        rw [if_pos htn.symm, if_pos heq, mul_one, neg_one_pow_natAbs_eq_sq, htn]
      · have htn : n ≠ (k * k).toNat := by
          intro h; apply heq
          have := Int.toNat_of_nonneg (mul_self_nonneg k)
          omega
        rw [if_neg htn, if_neg heq, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  unfold T4 T3
  rw [coeff_mk, coeff_mk]
  congr 3
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by omega, by omega⟩, hkk⟩
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hkk⟩

private lemma T2'_eq_prod : T2' = 2 * E_even * P_even ^ 2 := by
  ext n
  set N : ℕ := 2 * n + 3
  have hshift_eq : (∏ j ∈ Finset.range N, (1 + X ^ (2 * j) : PowerSeries ℚ)) =
      2 * ∏ j ∈ Finset.range (N - 1), (1 + X ^ (2 * (j + 1)) : PowerSeries ℚ) := by
    have hN : N = (N - 1) + 1 := by omega
    conv_lhs => rw [hN, Finset.prod_range_succ']
    simp only [mul_zero, pow_zero]
    ring
  have hP : ∀ j ≤ n, coeff j (2 * P_even ^ 2) =
      coeff j ((∏ m ∈ Finset.range N, (1 + X ^ (2 * (m + 1)) : PowerSeries ℚ)) *
               (∏ m ∈ Finset.range N, (1 + X ^ (2 * m) : PowerSeries ℚ))) := by
    intro j hj
    rw [hshift_eq, show (∏ m ∈ Finset.range N, (1 + X ^ (2 * (m + 1)) : PowerSeries ℚ)) *
        (2 * ∏ m ∈ Finset.range (N - 1), (1 + X ^ (2 * (m + 1)) : PowerSeries ℚ)) =
        2 * ((∏ m ∈ Finset.range N, (1 + C (1 : ℚ) * X ^ (2 * (m + 1)))) *
             (∏ m ∈ Finset.range (N - 1), (1 + C (1 : ℚ) * X ^ (2 * (m + 1))))) by
      simp only [map_one, one_mul]; ring]
    rw [sq]
    apply coeff_mul_congr (fun _ _ => rfl)
    intro i hi
    apply coeff_mul_congr
    · intro a ha; unfold P_even; exact coeff_infProd_eq hP_even_mod (by omega)
    · intro a ha; unfold P_even; exact coeff_infProd_eq hP_even_mod (by omega)
  have hrhs_rew : 2 * E_even * P_even ^ 2 = E_even * (2 * P_even ^ 2) := by ring
  rw [hrhs_rew, coeff_mul_congr (fun _ _ => rfl) hP, finite_jtp_X N, Finset.mul_sum, map_sum]
  have hterm : ∀ k ∈ Finset.Icc (-(N : ℤ)) N,
      coeff n (E_even * (qBinom (2 * N) (N + k).toNat * X ^ (k * k + k).toNat)) =
      if k * k + k = (n : ℤ) then (1 : ℚ) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← mul_assoc]
    have hkn : 0 ≤ k * k + k := by nlinarith [sq_nonneg k]
    by_cases hbig : n < (k * k + k).toNat
    · have h0 : coeff n (E_even * qBinom (2 * N) (N + k).toNat * X ^ (k * k + k).toNat) = 0 := by
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (E_even * qBinom (2 * N) (N + k).toNat) * coeff j (X ^ (k * k + k).toNat))]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeff_X_pow, if_neg (by omega), mul_zero]
      rw [h0, if_neg]
      intro heq
      have : (k * k + k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
      omega
    · have hk_le : -(n : ℤ) - 1 ≤ k ∧ k ≤ (n : ℤ) := by
        have : (k * k + k).toNat ≤ n := by omega
        have hkk : k * k + k ≤ (n : ℤ) := by
          have := Int.toNat_of_nonneg hkn
          omega
        constructor <;> nlinarith
      have h1 := coeff_E_even_mul_qBinom (n := n) (N := N) (r := (N + k).toNat) (by omega) (by omega)
      rw [coeff_mul_congr h1 (fun _ _ => rfl), one_mul, coeff_X_pow]
      by_cases heq : k * k + k = (n : ℤ)
      · have htn : (k * k + k).toNat = n := by rw [heq]; exact Int.toNat_natCast n
        rw [if_pos htn.symm, if_pos heq]
      · have htn : n ≠ (k * k + k).toNat := by
          intro h; apply heq
          have := Int.toNat_of_nonneg hkn
          omega
        rw [if_neg htn, if_neg heq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  unfold T2'
  rw [coeff_mk]
  congr 2
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by omega, by omega⟩, hkk⟩
  · rintro ⟨⟨_, _⟩, hkk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hkk⟩

/-! #### Four AGM identities via `ℤ²`-bijections and Jacobi's abstruse identity -/

private lemma coeff_T3_sq (n : ℕ) :
    coeff n (T3 ^ 2) =
      (((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
        (fun p => p.1 * p.1 + p.2 * p.2 = (n : ℤ))).card : ℚ) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T3 * coeff j T3)]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coeff i T3 * coeff (n - i) T3 =
      (((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
        (fun p => p.1 * p.1 = (i : ℤ) ∧ p.2 * p.2 = ((n - i : ℕ) : ℤ))).card : ℚ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold T3; simp only [coeff_mk]
    have hA : (Finset.Icc (-(i : ℤ)) i).filter (fun k => k * k = (i : ℤ)) =
        (Finset.Icc (-(n : ℤ)) n).filter (fun k => k * k = (i : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    have hB : (Finset.Icc (-((n - i : ℕ) : ℤ)) (n - i : ℕ)).filter (fun k => k * k = ((n - i : ℕ) : ℤ)) =
        (Finset.Icc (-(n : ℤ)) n).filter (fun k => k * k = ((n - i : ℕ) : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    rw [hA, hB, ← Nat.cast_mul, ← Finset.card_product]
    congr 2
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum]
  congr 1
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, hab, ha, hb⟩
      exact ⟨hab, by omega⟩
    · rintro ⟨hab, hsum⟩
      refine ⟨(a * a).toNat, ?_, hab, ?_, ?_⟩
      · have h1 := Int.toNat_of_nonneg (mul_self_nonneg a)
        have h2 := mul_self_nonneg b
        omega
      · exact Int.toNat_of_nonneg (mul_self_nonneg a) |>.symm
      · have h1 := Int.toNat_of_nonneg (mul_self_nonneg a)
        have h2 := mul_self_nonneg b
        omega
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega

private lemma coeff_T4_sq (n : ℕ) : coeff n (T4 ^ 2) = (-1 : ℚ) ^ n * coeff n (T3 ^ 2) := by
  rw [sq, sq, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T4 * coeff j T4),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T3 * coeff j T3),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  unfold T4
  simp only [coeff_mk]
  have hp : (-1 : ℚ) ^ i * (-1 : ℚ) ^ (n - i) = (-1 : ℚ) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  calc (-1 : ℚ) ^ i * coeff i T3 * ((-1 : ℚ) ^ (n - i) * coeff (n - i) T3)
      = ((-1 : ℚ) ^ i * (-1 : ℚ) ^ (n - i)) * (coeff i T3 * coeff (n - i) T3) := by ring
    _ = (-1 : ℚ) ^ n * (coeff i T3 * coeff (n - i) T3) := by rw [hp]

private lemma coeff_T2'_sq (n : ℕ) :
    coeff n (T2' ^ 2) =
      (((Finset.Icc (-(n : ℤ) - 1) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).filter
        (fun p => (p.1 * p.1 + p.1) + (p.2 * p.2 + p.2) = (n : ℤ))).card : ℚ) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T2' * coeff j T2')]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coeff i T2' * coeff (n - i) T2' =
      (((Finset.Icc (-(n : ℤ) - 1) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).filter
        (fun p => p.1 * p.1 + p.1 = (i : ℤ) ∧ p.2 * p.2 + p.2 = ((n - i : ℕ) : ℤ))).card : ℚ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold T2'; simp only [coeff_mk]
    have hA : (Finset.Icc (-(i : ℤ) - 1) i).filter (fun k => k * k + k = (i : ℤ)) =
        (Finset.Icc (-(n : ℤ) - 1) n).filter (fun k => k * k + k = (i : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    have hB : (Finset.Icc (-((n - i : ℕ) : ℤ) - 1) (n - i : ℕ)).filter (fun k => k * k + k = ((n - i : ℕ) : ℤ)) =
        (Finset.Icc (-(n : ℤ) - 1) n).filter (fun k => k * k + k = ((n - i : ℕ) : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    rw [hA, hB, ← Nat.cast_mul, ← Finset.card_product]
    congr 2
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum]
  congr 1
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, hab, ha, hb⟩
      exact ⟨hab, by omega⟩
    · rintro ⟨hab, hsum⟩
      have ha0 : 0 ≤ a * a + a := by nlinarith [sq_nonneg a]
      have hb0 : 0 ≤ b * b + b := by nlinarith [sq_nonneg b]
      refine ⟨(a * a + a).toNat, ?_, hab, ?_, ?_⟩
      · have h1 := Int.toNat_of_nonneg ha0; omega
      · exact (Int.toNat_of_nonneg ha0).symm
      · have h1 := Int.toNat_of_nonneg ha0; omega
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega

private lemma coeff_T3_mul_T2' (n : ℕ) :
    coeff n (T3 * T2') =
      (((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).filter
        (fun p => p.1 * p.1 + (p.2 * p.2 + p.2) = (n : ℤ))).card : ℚ) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T3 * coeff j T2')]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      coeff i T3 * coeff (n - i) T2' =
      (((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ) - 1) n).filter
        (fun p => p.1 * p.1 = (i : ℤ) ∧ p.2 * p.2 + p.2 = ((n - i : ℕ) : ℤ))).card : ℚ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold T3 T2'; simp only [coeff_mk]
    have hA : (Finset.Icc (-(i : ℤ)) i).filter (fun k => k * k = (i : ℤ)) =
        (Finset.Icc (-(n : ℤ)) n).filter (fun k => k * k = (i : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    have hB : (Finset.Icc (-((n - i : ℕ) : ℤ) - 1) (n - i : ℕ)).filter (fun k => k * k + k = ((n - i : ℕ) : ℤ)) =
        (Finset.Icc (-(n : ℤ) - 1) n).filter (fun k => k * k + k = ((n - i : ℕ) : ℤ)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
      · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
    rw [hA, hB, ← Nat.cast_mul, ← Finset.card_product]
    congr 2
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum]
  congr 1
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, hab, ha, hb⟩; exact ⟨hab, by omega⟩
    · rintro ⟨hab, hsum⟩
      have ha0 : 0 ≤ a * a := mul_self_nonneg a
      have hb0 : 0 ≤ b * b + b := by nlinarith [sq_nonneg b]
      refine ⟨(a * a).toNat, ?_, hab, ?_, ?_⟩
      · have h1 := Int.toNat_of_nonneg ha0; omega
      · exact (Int.toNat_of_nonneg ha0).symm
      · have h1 := Int.toNat_of_nonneg ha0; omega
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    omega

private lemma agm1 : T3 ^ 2 + T4 ^ 2 = 2 * psSq (T3 ^ 2) := by
  ext n
  rw [map_add, coeff_T4_sq, show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C_mul]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [coeff_psSq_even, Even.neg_one_pow ⟨m, by omega⟩, one_mul, ← two_mul]
    congr 1
    rw [coeff_T3_sq, coeff_T3_sq]
    congr 1
    symm
    apply Finset.card_bij (fun p _ => (p.1 + p.2, p.1 - p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      have hsum : (p.1 + p.2) * (p.1 + p.2) + (p.1 - p.2) * (p.1 - p.2) = ((2 * m : ℕ) : ℤ) := by
        push_cast; linarith [hp.2]
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
    · intro p₁ _ p₂ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      have hpar : (q.1 + q.2) % 2 = 0 := by
        have hmod : (q.1 * q.1 + q.2 * q.2) % 2 = 0 := by rw [hq.2]; omega
        have h1 : (q.1 + q.2) * (q.1 + q.2) = q.1 * q.1 + q.2 * q.2 + 2 * (q.1 * q.2) := by ring
        have h2 : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 0 := by omega
        by_contra hne
        have : (q.1 + q.2) % 2 = 1 := by omega
        have : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 1 := by rw [Int.mul_emod, this]; norm_num
        omega
      refine ⟨((q.1 + q.2) / 2, (q.1 - q.2) / 2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hq1 : 2 * ((q.1 + q.2) / 2) = q.1 + q.2 := by omega
        have hq2 : 2 * ((q.1 - q.2) / 2) = q.1 - q.2 := by omega
        have hqsum : q.1 * q.1 + q.2 * q.2 = 2 * (m : ℤ) := by push_cast at hq; exact hq.2
        have hsum : ((q.1 + q.2) / 2) * ((q.1 + q.2) / 2) + ((q.1 - q.2) / 2) * ((q.1 - q.2) / 2) = (m : ℤ) := by
          nlinarith [hqsum, hq1, hq2]
        exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
      · exact Prod.ext (by omega) (by omega)
  · rw [coeff_psSq_odd, Odd.neg_one_pow ⟨m, rfl⟩]; ring

private lemma agm2 : T3 ^ 2 - T4 ^ 2 = 2 * X * psSq (T2' ^ 2) := by
  ext n
  rw [map_sub, coeff_T4_sq, mul_assoc, show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C_mul]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [Even.neg_one_pow ⟨m, by omega⟩, one_mul, sub_self]
    rcases m with _ | m
    · rw [show 2 * 0 = 0 by omega, coeff_zero_X_mul, mul_zero]
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, coeff_succ_X_mul, coeff_psSq_odd, mul_zero]
  · rw [Odd.neg_one_pow ⟨m, rfl⟩, coeff_succ_X_mul, coeff_psSq_even]
    have hlhs : coeff (2 * m + 1) (T3 ^ 2) - -1 * coeff (2 * m + 1) (T3 ^ 2) = 2 * coeff (2 * m + 1) (T3 ^ 2) := by ring
    rw [hlhs]
    congr 1
    rw [coeff_T3_sq, coeff_T2'_sq]
    congr 1
    symm
    apply Finset.card_bij (fun p _ => (p.1 + p.2 + 1, p.1 - p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      have hsum : (p.1 + p.2 + 1) * (p.1 + p.2 + 1) + (p.1 - p.2) * (p.1 - p.2) = ((2 * m + 1 : ℕ) : ℤ) := by
        push_cast; linarith [hp.2]
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
    · intro p₁ _ p₂ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      have hpar : (q.1 + q.2) % 2 = 1 := by
        have hmod : (q.1 * q.1 + q.2 * q.2) % 2 = 1 := by rw [hq.2]; omega
        have h1 : (q.1 + q.2) * (q.1 + q.2) = q.1 * q.1 + q.2 * q.2 + 2 * (q.1 * q.2) := by ring
        have h2 : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 1 := by omega
        by_contra hne
        have : (q.1 + q.2) % 2 = 0 := by omega
        have : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 0 := by rw [Int.mul_emod, this]; norm_num
        omega
      refine ⟨((q.1 + q.2 - 1) / 2, (q.1 - q.2 - 1) / 2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hu : 2 * ((q.1 + q.2 - 1) / 2) = q.1 + q.2 - 1 := by omega
        have hv : 2 * ((q.1 - q.2 - 1) / 2) = q.1 - q.2 - 1 := by omega
        have hqsum : q.1 * q.1 + q.2 * q.2 = 2 * (m : ℤ) + 1 := by push_cast at hq; exact hq.2
        have hsum : ((q.1 + q.2 - 1) / 2) * ((q.1 + q.2 - 1) / 2) + (q.1 + q.2 - 1) / 2 +
            (((q.1 - q.2 - 1) / 2) * ((q.1 - q.2 - 1) / 2) + (q.1 - q.2 - 1) / 2) = (m : ℤ) := by
          nlinarith [hqsum, hu, hv]
        exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
      · exact Prod.ext (by omega) (by omega)

private lemma agm3 : T3 * T4 = psSq (T4 ^ 2) := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i T3 * coeff j T4)]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [coeff_psSq_even, coeff_T4_sq, coeff_T3_sq]
    have hlhs : ∑ i ∈ Finset.range (2 * m + 1), coeff i T3 * coeff (2 * m - i) T4 =
        ∑ p ∈ (Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ) ×ˢ Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter
          (fun p => p.1 * p.1 + p.2 * p.2 = ((2 * m : ℕ) : ℤ)), (-1 : ℚ) ^ p.2.natAbs := by
      have hterm : ∀ i ∈ Finset.range (2 * m + 1),
          coeff i T3 * coeff (2 * m - i) T4 =
          ∑ p ∈ (Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ) ×ˢ Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter
            (fun p => p.1 * p.1 = (i : ℤ) ∧ p.2 * p.2 = ((2 * m - i : ℕ) : ℤ)), (-1 : ℚ) ^ p.2.natAbs := by
        intro i hi
        rw [Finset.mem_range] at hi
        unfold T4; simp only [coeff_mk]
        have hconst : ∀ p ∈ (Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ) ×ˢ Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter
            (fun p => p.1 * p.1 = (i : ℤ) ∧ p.2 * p.2 = ((2 * m - i : ℕ) : ℤ)),
            (-1 : ℚ) ^ p.2.natAbs = (-1 : ℚ) ^ (2 * m - i) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [neg_one_pow_natAbs_eq_sq, hp.2.2, Int.toNat_natCast]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
        have hcard : (((Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ) ×ˢ Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter
            (fun p => p.1 * p.1 = (i : ℤ) ∧ p.2 * p.2 = ((2 * m - i : ℕ) : ℤ))).card : ℚ) =
            coeff i T3 * coeff (2 * m - i) T3 := by
          unfold T3; simp only [coeff_mk]
          have hA : (Finset.Icc (-(i : ℤ)) i).filter (fun k => k * k = (i : ℤ)) =
              (Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter (fun k => k * k = (i : ℤ)) := by
            ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
            · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
            · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
          have hB : (Finset.Icc (-((2 * m - i : ℕ) : ℤ)) (2 * m - i : ℕ)).filter (fun k => k * k = ((2 * m - i : ℕ) : ℤ)) =
              (Finset.Icc (-((2 * m : ℕ) : ℤ)) (2 * m : ℕ)).filter (fun k => k * k = ((2 * m - i : ℕ) : ℤ)) := by
            ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
            · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by omega, by omega⟩, hk⟩
            · rintro ⟨⟨_, _⟩, hk⟩; exact ⟨⟨by nlinarith, by nlinarith⟩, hk⟩
          rw [hA, hB, ← Nat.cast_mul, ← Finset.card_product]
          congr 2; ext ⟨a, b⟩; simp only [Finset.mem_product, Finset.mem_filter]; tauto
        rw [hcard]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_biUnion]
      · congr 1
        ext ⟨a, b⟩
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        constructor
        · rintro ⟨i, _, hab, ha, hb⟩; exact ⟨hab, by omega⟩
        · rintro ⟨hab, hsum⟩
          refine ⟨(a * a).toNat, ?_, hab, ?_, ?_⟩
          · have h1 := Int.toNat_of_nonneg (mul_self_nonneg a); have h2 := mul_self_nonneg b; omega
          · exact (Int.toNat_of_nonneg (mul_self_nonneg a)).symm
          · have h1 := Int.toNat_of_nonneg (mul_self_nonneg a); have h2 := mul_self_nonneg b; omega
      · intro i _ j _ hij
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_filter] at hp1 hp2
        omega
    rw [hlhs]
    have hrhs : (-1 : ℚ) ^ m * (((Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m).filter
        (fun p => p.1 * p.1 + p.2 * p.2 = (m : ℤ))).card : ℚ) =
        ∑ p ∈ (Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m).filter
          (fun p => p.1 * p.1 + p.2 * p.2 = (m : ℤ)), (-1 : ℚ) ^ m := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hrhs]
    symm
    apply Finset.sum_bij (fun p _ => (p.1 + p.2, p.1 - p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      have hsum : (p.1 + p.2) * (p.1 + p.2) + (p.1 - p.2) * (p.1 - p.2) = ((2 * m : ℕ) : ℤ) := by
        push_cast; linarith [hp.2]
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
    · intro p₁ _ p₂ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      have hpar : (q.1 + q.2) % 2 = 0 := by
        have hmod : (q.1 * q.1 + q.2 * q.2) % 2 = 0 := by rw [hq.2]; omega
        have h1 : (q.1 + q.2) * (q.1 + q.2) = q.1 * q.1 + q.2 * q.2 + 2 * (q.1 * q.2) := by ring
        have h2 : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 0 := by omega
        by_contra hne
        have : (q.1 + q.2) % 2 = 1 := by omega
        have : ((q.1 + q.2) * (q.1 + q.2)) % 2 = 1 := by rw [Int.mul_emod, this]; norm_num
        omega
      refine ⟨((q.1 + q.2) / 2, (q.1 - q.2) / 2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hq1 : 2 * ((q.1 + q.2) / 2) = q.1 + q.2 := by omega
        have hq2 : 2 * ((q.1 - q.2) / 2) = q.1 - q.2 := by omega
        have hqsum : q.1 * q.1 + q.2 * q.2 = 2 * (m : ℤ) := by push_cast at hq; exact hq.2
        have hsum : ((q.1 + q.2) / 2) * ((q.1 + q.2) / 2) + ((q.1 - q.2) / 2) * ((q.1 - q.2) / 2) = (m : ℤ) := by
          nlinarith [hqsum, hq1, hq2]
        exact ⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, hsum⟩
      · exact Prod.ext (by omega) (by omega)
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rw [neg_one_pow_natAbs_eq_sq]
      have hpar : ((p.1 - p.2) * (p.1 - p.2)).toNat % 2 = m % 2 := by
        have h1 : ((p.1 - p.2) * (p.1 - p.2)).toNat = ((p.1 - p.2) * (p.1 - p.2)) := by
          exact_mod_cast Int.toNat_of_nonneg (mul_self_nonneg (p.1 - p.2))
        have h2 : (p.1 - p.2) * (p.1 - p.2) = (m : ℤ) - 2 * (p.1 * p.2) := by linarith [hp.2]
        omega
      rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
      · have he : Even ((p.1 - p.2) * (p.1 - p.2)).toNat := by
          refine ⟨((p.1 - p.2) * (p.1 - p.2)).toNat / 2, by omega⟩
        rw [Even.neg_one_pow ⟨r, hr⟩, Even.neg_one_pow he]
      · have ho : Odd ((p.1 - p.2) * (p.1 - p.2)).toNat := by
          refine ⟨((p.1 - p.2) * (p.1 - p.2)).toNat / 2, by omega⟩
        rw [Odd.neg_one_pow ⟨r, hr⟩, Odd.neg_one_pow ho]
  · rw [coeff_psSq_odd]
    -- Reverse sum i ↦ 2m + 1 - i negates every term since (-1)^(2m+1-i) = -(-1)^i!
    set S := ∑ i ∈ Finset.range (2 * m + 1 + 1), coeff i T3 * coeff (2 * m + 1 - i) T4
    have hneg : S = -S := by
      dsimp only [S]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_bij (fun i _ => 2 * m + 1 - i)
      · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
      · intro a ha b hb h; rw [Finset.mem_range] at ha hb; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨2 * m + 1 - j, by rw [Finset.mem_range]; omega, by omega⟩
      · intro i hi
        rw [Finset.mem_range] at hi
        unfold T4; simp only [coeff_mk]
        rw [show 2 * m + 1 - (2 * m + 1 - i) = i by omega]
        have hsign : (-1 : ℚ) ^ (2 * m + 1 - i) = -((-1 : ℚ) ^ i) := by
          have hp : (-1 : ℚ) ^ (2 * m + 1 - i) * (-1 : ℚ) ^ i = -1 := by
            rw [← pow_add, Nat.sub_add_cancel (by omega), Odd.neg_one_pow ⟨m, rfl⟩]
          have hsq : (-1 : ℚ) ^ i * (-1 : ℚ) ^ i = 1 := by
            rw [← pow_add, show i + i = 2 * i by omega, Even.neg_one_pow ⟨i, by omega⟩]
          calc (-1 : ℚ) ^ (2 * m + 1 - i)
              = (-1 : ℚ) ^ (2 * m + 1 - i) * ((-1 : ℚ) ^ i * (-1 : ℚ) ^ i) := by rw [hsq, mul_one]
            _ = ((-1 : ℚ) ^ (2 * m + 1 - i) * (-1 : ℚ) ^ i) * (-1 : ℚ) ^ i := by ring
            _ = -((-1 : ℚ) ^ i) := by rw [hp]; ring
        rw [hsign]; ring
    linarith

private lemma agm4 : T2' ^ 2 = 2 * psSq (T3 * T2') := by
  ext n
  rw [show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C_mul]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [coeff_psSq_even, coeff_T2'_sq, coeff_T3_mul_T2']
    set A := (Finset.Icc (-((2 * m : ℕ) : ℤ) - 1) (2 * m : ℕ) ×ˢ Finset.Icc (-((2 * m : ℕ) : ℤ) - 1) (2 * m : ℕ)).filter
      (fun p => (p.1 * p.1 + p.1) + (p.2 * p.2 + p.2) = ((2 * m : ℕ) : ℤ))
    set A_same := A.filter (fun p => (p.1 - p.2) % 2 = 0)
    set A_diff := A.filter (fun p => ¬ (p.1 - p.2) % 2 = 0)
    set B := (Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ) - 1) m).filter
      (fun p => p.1 * p.1 + (p.2 * p.2 + p.2) = (m : ℤ))
    have hpart : A.card = A_same.card + A_diff.card := by
      have h := Finset.card_filter_add_card_filter_not (s := A) (p := fun p => (p.1 - p.2) % 2 = 0)
      exact h.symm
    have hsame_diff : A_same.card = A_diff.card := by
      apply Finset.card_bij (fun p _ => (p.1, -1 - p.2))
      · intro p hp
        simp only [A_same, A_diff, A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        have hp2_le : -((2 * m : ℕ) : ℤ) - 1 ≤ -1 - p.2 ∧ -1 - p.2 ≤ ((2 * m : ℕ) : ℤ) := by
          have h1 := hp.1.1.2.1; have h2 := hp.1.1.2.2; omega
        have hsum : (p.1 * p.1 + p.1) + ((-1 - p.2) * (-1 - p.2) + (-1 - p.2)) = ((2 * m : ℕ) : ℤ) := by
          linarith [hp.1.2]
        exact ⟨⟨⟨hp.1.1.1, hp2_le⟩, hsum⟩, by omega⟩
      · intro p₁ _ p₂ _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by omega)
      · intro q hq
        simp only [A_diff, A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
        refine ⟨(q.1, -1 - q.2), ?_, Prod.ext rfl (by omega)⟩
        simp only [A_same, A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hq2_le : -((2 * m : ℕ) : ℤ) - 1 ≤ -1 - q.2 ∧ -1 - q.2 ≤ ((2 * m : ℕ) : ℤ) := by
          have h1 := hq.1.1.2.1; have h2 := hq.1.1.2.2; omega
        have hsum : (q.1 * q.1 + q.1) + ((-1 - q.2) * (-1 - q.2) + (-1 - q.2)) = ((2 * m : ℕ) : ℤ) := by
          linarith [hq.1.2]
        exact ⟨⟨⟨hq.1.1.1, hq2_le⟩, hsum⟩, by omega⟩
    have hsame_B : A_same.card = B.card := by
      symm
      apply Finset.card_bij (fun p _ => (p.2 + p.1, p.2 - p.1))
      · intro p hp
        simp only [A_same, A, B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        have hsum : ((p.2 + p.1) * (p.2 + p.1) + (p.2 + p.1)) +
            ((p.2 - p.1) * (p.2 - p.1) + (p.2 - p.1)) = ((2 * m : ℕ) : ℤ) := by
          push_cast; linarith [hp.2]
        have hbd1 : -((2 * m : ℕ) : ℤ) - 1 ≤ p.2 + p.1 ∧ p.2 + p.1 ≤ ((2 * m : ℕ) : ℤ) := by
          have h1 := hp.1.1.1; have h2 := hp.1.1.2; have h3 := hp.1.2.1; have h4 := hp.1.2.2; omega
        have hbd2 : -((2 * m : ℕ) : ℤ) - 1 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ ((2 * m : ℕ) : ℤ) := by
          have h1 := hp.1.1.1; have h2 := hp.1.1.2; have h3 := hp.1.2.1; have h4 := hp.1.2.2; omega
        exact ⟨⟨⟨hbd1, hbd2⟩, hsum⟩, by omega⟩
      · intro p₁ _ p₂ _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) (by omega)
      · intro q hq
        simp only [A_same, A, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
        refine ⟨((q.1 - q.2) / 2, (q.1 + q.2) / 2), ?_, Prod.ext (by omega) (by omega)⟩
        simp only [B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        set u : ℤ := (q.1 - q.2) / 2
        set v : ℤ := (q.1 + q.2) / 2
        have hu : 2 * u = q.1 - q.2 := by dsimp only [u]; omega
        have hv : 2 * v = q.1 + q.2 := by dsimp only [v]; omega
        have hqsum : (q.1 * q.1 + q.1) + (q.2 * q.2 + q.2) = 2 * (m : ℤ) := by
          push_cast at hq; exact hq.1.2
        have hq1 : q.1 = v + u := by omega
        have hq2 : q.2 = v - u := by omega
        have hsum : u * u + (v * v + v) = (m : ℤ) := by
          rw [hq1, hq2] at hqsum; linarith
        have hu_le : -(m : ℤ) ≤ u ∧ u ≤ (m : ℤ) := by
          have hv0 : 0 ≤ v * v + v := by nlinarith only [sq_nonneg v]
          constructor
          · nlinarith only [hsum, hv0, sq_nonneg (u + 1)]
          · nlinarith only [hsum, hv0, sq_nonneg (u - 1)]
        have hv_le : -(m : ℤ) - 1 ≤ v ∧ v ≤ (m : ℤ) := by
          have hu0 : 0 ≤ u * u := mul_self_nonneg u
          constructor
          · nlinarith only [hsum, hu0, sq_nonneg (v + 1)]
          · nlinarith only [hsum, hu0, sq_nonneg v]
        exact ⟨⟨hu_le, hv_le⟩, hsum⟩
    have hcard : A.card = 2 * B.card := by omega
    change (A.card : ℚ) = 2 * (B.card : ℚ)
    exact_mod_cast hcard
  · rw [coeff_psSq_odd, mul_zero, coeff_T2'_sq]
    have hempty : ((Finset.Icc (-((2 * m + 1 : ℕ) : ℤ) - 1) (2 * m + 1 : ℕ) ×ˢ
        Finset.Icc (-((2 * m + 1 : ℕ) : ℤ) - 1) (2 * m + 1 : ℕ)).filter
        (fun p => (p.1 * p.1 + p.1) + (p.2 * p.2 + p.2) = ((2 * m + 1 : ℕ) : ℤ))) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p _ hsum
      have he1 : (p.1 * p.1 + p.1) % 2 = 0 := by
        rcases Int.even_or_odd p.1 with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk]; have : (k + k) * (k + k) + (k + k) = 2 * (2 * k * k + k) := by ring
          omega
        · rw [hk]; have : (2 * k + 1) * (2 * k + 1) + (2 * k + 1) = 2 * (2 * k * k + 3 * k + 1) := by ring
          omega
      have he2 : (p.2 * p.2 + p.2) % 2 = 0 := by
        rcases Int.even_or_odd p.2 with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk]; have : (k + k) * (k + k) + (k + k) = 2 * (2 * k * k + k) := by ring
          omega
        · rw [hk]; have : (2 * k + 1) * (2 * k + 1) + (2 * k + 1) = 2 * (2 * k * k + 3 * k + 1) := by ring
          omega
      omega
    rw [hempty]; simp

private lemma jacobi_abstruse : T3 ^ 4 - T4 ^ 4 = X * T2' ^ 4 := by
  have h1 : T3 ^ 4 - T4 ^ 4 = (T3 ^ 2 + T4 ^ 2) * (T3 ^ 2 - T4 ^ 2) := by ring
  have h2 : T2' ^ 4 = 4 * psSq (T3 ^ 2 * T2' ^ 2) := by
    calc T2' ^ 4 = (T2' ^ 2) ^ 2 := by ring
      _ = (2 * psSq (T3 * T2')) ^ 2 := by rw [agm4]
      _ = 4 * (psSq (T3 * T2') * psSq (T3 * T2')) := by ring
      _ = 4 * psSq ((T3 * T2') * (T3 * T2')) := by rw [← psSq_mul]
      _ = 4 * psSq (T3 ^ 2 * T2' ^ 2) := by congr 2; ring
  rw [h1, agm1, agm2, h2]
  calc 2 * psSq (T3 ^ 2) * (2 * X * psSq (T2' ^ 2))
      = X * (4 * (psSq (T3 ^ 2) * psSq (T2' ^ 2))) := by ring
    _ = X * (4 * psSq (T3 ^ 2 * T2' ^ 2)) := by rw [← psSq_mul]


/-! ### Part 2C: Differential identity, Landen & Clausen ODEs, and final assembly -/

private lemma coeff_zero_T3 : coeff 0 T3 = 1 := by
  unfold T3; rw [coeff_mk]; decide

private lemma coeff_one_T3 : coeff 1 T3 = 2 := by
  unfold T3; rw [coeff_mk]; decide

private lemma coeff_zero_T4 : coeff 0 T4 = 1 := by
  unfold T4; rw [coeff_mk, pow_zero, one_mul, coeff_zero_T3]

private lemma coeff_one_T4 : coeff 1 T4 = -2 := by
  unfold T4; rw [coeff_mk, pow_one, coeff_one_T3]; norm_num

private lemma coeff_zero_T2' : coeff 0 T2' = 2 := by
  unfold T2'; rw [coeff_mk]; decide

private lemma coeff_zero_mul (f g : PowerSeries ℚ) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_zero_eq_constantCoeff, map_mul]

private lemma coeff_zero_pow (f : PowerSeries ℚ) (k : ℕ) :
    coeff 0 (f ^ k) = (coeff 0 f) ^ k := by
  rw [coeff_zero_eq_constantCoeff, map_pow]

private lemma coeff_one_mul (f g : PowerSeries ℚ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Nat.sub_zero, Nat.sub_self]

private lemma ps_ne_zero_of_coeff {f : PowerSeries ℚ} {n : ℕ} (h : coeff n f ≠ 0) : f ≠ 0 := by
  intro hz; rw [hz, map_zero] at h; exact h rfl

private lemma psSq_psComp (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : coeff 0 g = 0) :
    psSq (psComp f g) = psComp f (psSq g) := by
  have hsq0 : coeff 0 (psSq g) = 0 := by rw [coeff_psSq_even 0, hg]
  have hX2 : coeff 0 (X ^ 2 : PowerSeries ℚ) = 0 := by rw [coeff_X_pow]; norm_num
  calc psSq (psComp f g) = psComp (psComp f g) (X ^ 2) := (psComp_X_sq _).symm
    _ = psComp f (psComp g (X ^ 2)) := psComp_comp f hg hX2
    _ = psComp f (psSq g) := by rw [psComp_X_sq]

private lemma coeff_zero_T3_pow (k : ℕ) : coeff 0 (T3 ^ k) = 1 := by
  rw [coeff_zero_pow, coeff_zero_T3, one_pow]

private def muPS : PowerSeries ℚ := T2' ^ 4 * psInv (T3 ^ 4)
private def lamPS : PowerSeries ℚ := X * muPS
private def kpPS : PowerSeries ℚ := T4 ^ 2 * psInv (T3 ^ 2)
private def vPS : PowerSeries ℚ := (1 - kpPS) * psInv (1 + kpPS)
private def yPS : PowerSeries ℚ := lamPS * (1 - lamPS) * C (1 / 16)

private lemma coeff_zero_muPS : coeff 0 muPS = 16 := by
  unfold muPS
  rw [coeff_zero_mul, coeff_zero_pow, coeff_zero_T2', coeff_zero_psInv (by rw [coeff_zero_T3_pow]; norm_num),
    coeff_zero_T3_pow]
  norm_num

private lemma coeff_zero_lamPS : coeff 0 lamPS = 0 := by
  unfold lamPS; exact coeff_zero_X_mul (φ := muPS)

private lemma coeff_zero_kpPS : coeff 0 kpPS = 1 := by
  unfold kpPS
  rw [coeff_zero_mul, coeff_zero_pow, coeff_zero_T4, coeff_zero_psInv (by rw [coeff_zero_T3_pow]; norm_num),
    coeff_zero_T3_pow]
  norm_num

private lemma coeff_zero_one_add_kpPS : coeff 0 (1 + kpPS) = 2 := by
  rw [map_add, coeff_one, if_pos rfl, coeff_zero_kpPS]; norm_num

private lemma coeff_zero_vPS : coeff 0 vPS = 0 := by
  unfold vPS
  rw [coeff_zero_mul, map_sub, coeff_one, if_pos rfl, coeff_zero_kpPS, sub_self, zero_mul]

private lemma coeff_zero_yPS : coeff 0 yPS = 0 := by
  unfold yPS
  rw [coeff_zero_mul, coeff_zero_mul, coeff_zero_lamPS, zero_mul, zero_mul]

private lemma T3_pow4_mul_lamPS : T3 ^ 4 * lamPS = X * T2' ^ 4 := by
  unfold lamPS muPS
  calc T3 ^ 4 * (X * (T2' ^ 4 * psInv (T3 ^ 4)))
      = X * T2' ^ 4 * (T3 ^ 4 * psInv (T3 ^ 4)) := by ring
    _ = X * T2' ^ 4 * 1 := by rw [mul_psInv (by rw [coeff_zero_T3_pow]; norm_num)]
    _ = X * T2' ^ 4 := mul_one _

private lemma T3_sq_mul_kpPS : T3 ^ 2 * kpPS = T4 ^ 2 := by
  unfold kpPS
  calc T3 ^ 2 * (T4 ^ 2 * psInv (T3 ^ 2))
      = T4 ^ 2 * (T3 ^ 2 * psInv (T3 ^ 2)) := by ring
    _ = T4 ^ 2 * 1 := by rw [mul_psInv (by rw [coeff_zero_T3_pow]; norm_num)]
    _ = T4 ^ 2 := mul_one _

private lemma lamPS_add_kpPS_sq : lamPS + kpPS ^ 2 = 1 := by
  have hne : T3 ^ 4 ≠ 0 := ps_ne_zero_of_coeff (by rw [coeff_zero_T3_pow]; norm_num)
  apply mul_left_cancel₀ hne
  have hk2 : T3 ^ 4 * kpPS ^ 2 = T4 ^ 4 := by
    calc T3 ^ 4 * kpPS ^ 2 = (T3 ^ 2 * kpPS) ^ 2 := by ring
      _ = (T4 ^ 2) ^ 2 := by rw [T3_sq_mul_kpPS]
      _ = T4 ^ 4 := by ring
  rw [mul_add, T3_pow4_mul_lamPS, hk2, mul_one]
  linear_combination -jacobi_abstruse

private lemma one_sub_lamPS : 1 - lamPS = kpPS ^ 2 := by
  linear_combination -lamPS_add_kpPS_sq

private lemma one_add_kp_mul_v : (1 + kpPS) * vPS = 1 - kpPS := by
  unfold vPS
  calc (1 + kpPS) * ((1 - kpPS) * psInv (1 + kpPS))
      = (1 - kpPS) * ((1 + kpPS) * psInv (1 + kpPS)) := by ring
    _ = (1 - kpPS) * 1 := by rw [mul_psInv (by rw [coeff_zero_one_add_kpPS]; norm_num)]
    _ = 1 - kpPS := mul_one _

private lemma one_add_kp_mul_one_add_v : (1 + kpPS) * (1 + vPS) = 2 := by
  have := one_add_kp_mul_v
  calc (1 + kpPS) * (1 + vPS) = (1 + kpPS) + (1 + kpPS) * vPS := by ring
    _ = (1 + kpPS) + (1 - kpPS) := by rw [this]
    _ = 2 := by ring

private lemma coeff_zero_one_add_vPS : coeff 0 (1 + vPS) = 1 := by
  rw [map_add, coeff_one, if_pos rfl, coeff_zero_vPS, add_zero]

private lemma Q_mul_yPS : P_odd ^ 24 * yPS = X := by
  have hne : (16 : PowerSeries ℚ) * T3 ^ 8 ≠ 0 := by
    apply ps_ne_zero_of_coeff (n := 0)
    rw [show (16 : PowerSeries ℚ) = C 16 by rfl, coeff_C_mul, coeff_zero_T3_pow]
    norm_num
  apply mul_left_cancel₀ hne
  have h16y : (16 : PowerSeries ℚ) * yPS = lamPS * (1 - lamPS) := by
    unfold yPS
    have h16 : (16 : PowerSeries ℚ) * C (1 / 16) = 1 := by
      rw [show (16 : PowerSeries ℚ) = C 16 by rfl, ← map_mul]; norm_num
    calc (16 : PowerSeries ℚ) * (lamPS * (1 - lamPS) * C (1 / 16))
        = lamPS * (1 - lamPS) * ((16 : PowerSeries ℚ) * C (1 / 16)) := by ring
      _ = lamPS * (1 - lamPS) * 1 := by rw [h16]
      _ = lamPS * (1 - lamPS) := mul_one _
  have hT4_4 : T3 ^ 4 * (1 - lamPS) = T4 ^ 4 := by
    rw [one_sub_lamPS]
    calc T3 ^ 4 * kpPS ^ 2 = (T3 ^ 2 * kpPS) ^ 2 := by ring
      _ = (T4 ^ 2) ^ 2 := by rw [T3_sq_mul_kpPS]
      _ = T4 ^ 4 := by ring
  have hprod : P_odd ^ 24 * T2' ^ 4 * T4 ^ 4 = 16 * T3 ^ 8 := by
    rw [T2'_eq_prod, T4_eq_prod, T3_eq_prod]
    calc P_odd ^ 24 * (2 * E_even * P_even ^ 2) ^ 4 * (E_even * M_odd ^ 2) ^ 4
        = 16 * (E_even * P_odd ^ 2) ^ 8 * (P_odd * M_odd * P_even) ^ 8 := by ring
      _ = 16 * (E_even * P_odd ^ 2) ^ 8 * 1 ^ 8 := by rw [euler_prod_id]
      _ = 16 * (E_even * P_odd ^ 2) ^ 8 := by ring
  calc 16 * T3 ^ 8 * (P_odd ^ 24 * yPS)
      = P_odd ^ 24 * (T3 ^ 4 * T3 ^ 4 * (16 * yPS)) := by ring
    _ = P_odd ^ 24 * ((T3 ^ 4 * lamPS) * (T3 ^ 4 * (1 - lamPS))) := by rw [h16y]; ring
    _ = P_odd ^ 24 * ((X * T2' ^ 4) * T4 ^ 4) := by rw [T3_pow4_mul_lamPS, hT4_4]
    _ = X * (P_odd ^ 24 * T2' ^ 4 * T4 ^ 4) := by ring
    _ = X * (16 * T3 ^ 8) := by rw [hprod]
    _ = 16 * T3 ^ 8 * X := by ring

private lemma psSq_lamPS : psSq lamPS = vPS ^ 2 := by
  have hne : (T3 ^ 2 + T4 ^ 2) ^ 2 ≠ 0 := by
    apply ps_ne_zero_of_coeff (n := 0)
    rw [coeff_zero_pow, map_add, coeff_zero_pow, coeff_zero_pow, coeff_zero_T3, coeff_zero_T4]
    norm_num
  apply mul_right_cancel₀ hne
  have h1 : psSq lamPS * (T3 ^ 2 + T4 ^ 2) ^ 2 = (T3 ^ 2 - T4 ^ 2) ^ 2 := by
    rw [agm1, agm2]
    calc psSq lamPS * (2 * psSq (T3 ^ 2)) ^ 2
        = 4 * (psSq lamPS * psSq (T3 ^ 4)) := by
          rw [show (T3 ^ 4 : PowerSeries ℚ) = T3 ^ 2 * T3 ^ 2 by ring, psSq_mul]; ring
      _ = 4 * psSq (lamPS * T3 ^ 4) := by rw [← psSq_mul]
      _ = 4 * psSq (X * T2' ^ 4) := by rw [mul_comm lamPS, T3_pow4_mul_lamPS]
      _ = 4 * (psSq X * psSq (T2' ^ 2 * T2' ^ 2)) := by
          rw [psSq_mul]; congr 2; ring
      _ = (2 * X * psSq (T2' ^ 2)) ^ 2 := by rw [psSq_X, psSq_mul]; ring
  have h2 : vPS * (T3 ^ 2 + T4 ^ 2) = T3 ^ 2 - T4 ^ 2 := by
    calc vPS * (T3 ^ 2 + T4 ^ 2)
        = vPS * (T3 ^ 2 + T3 ^ 2 * kpPS) := by rw [T3_sq_mul_kpPS]
      _ = ((1 + kpPS) * vPS) * T3 ^ 2 := by ring
      _ = (1 - kpPS) * T3 ^ 2 := by rw [one_add_kp_mul_v]
      _ = T3 ^ 2 - T3 ^ 2 * kpPS := by ring
      _ = T3 ^ 2 - T4 ^ 2 := by rw [T3_sq_mul_kpPS]
  rw [h1, ← h2]; ring

private lemma lamPS_from_vPS : 4 * vPS * psInv ((1 + vPS) ^ 2) = lamPS := by
  have h1 : (1 + kpPS) ^ 2 ≠ 0 := ps_ne_zero_of_coeff (by rw [coeff_zero_pow, coeff_zero_one_add_kpPS]; norm_num)
  have h2 : (1 + vPS) ^ 2 ≠ 0 := ps_ne_zero_of_coeff (by rw [coeff_zero_pow, coeff_zero_one_add_vPS]; norm_num)
  have hmul : (1 + vPS) ^ 2 * lamPS = 4 * vPS := by
    apply mul_left_cancel₀ h1
    have hlam : lamPS = (1 + kpPS) * (1 - kpPS) := by linear_combination lamPS_add_kpPS_sq
    calc (1 + kpPS) ^ 2 * ((1 + vPS) ^ 2 * lamPS)
        = ((1 + kpPS) * (1 + vPS)) ^ 2 * lamPS := by ring
      _ = 2 ^ 2 * ((1 + kpPS) * (1 - kpPS)) := by rw [one_add_kp_mul_one_add_v, ← hlam]
      _ = 4 * (1 + kpPS) * ((1 + kpPS) * vPS) := by rw [one_add_kp_mul_v]; ring
      _ = (1 + kpPS) ^ 2 * (4 * vPS) := by ring
  calc 4 * vPS * psInv ((1 + vPS) ^ 2)
      = ((1 + vPS) ^ 2 * lamPS) * psInv ((1 + vPS) ^ 2) := by rw [hmul]
    _ = lamPS * ((1 + vPS) ^ 2 * psInv ((1 + vPS) ^ 2)) := by ring
    _ = lamPS * 1 := by rw [mul_psInv (by rw [coeff_zero_pow, coeff_zero_one_add_vPS]; norm_num)]
    _ = lamPS := mul_one _

private lemma T3_sq_psSq : (1 + vPS) * psSq (T3 ^ 2) = T3 ^ 2 := by
  have h1 : 1 + kpPS ≠ 0 := ps_ne_zero_of_coeff (by rw [coeff_zero_one_add_kpPS]; norm_num)
  apply mul_left_cancel₀ h1
  calc (1 + kpPS) * ((1 + vPS) * psSq (T3 ^ 2))
      = ((1 + kpPS) * (1 + vPS)) * psSq (T3 ^ 2) := by ring
    _ = 2 * psSq (T3 ^ 2) := by rw [one_add_kp_mul_one_add_v]
    _ = T3 ^ 2 + T4 ^ 2 := agm1.symm
    _ = T3 ^ 2 + T3 ^ 2 * kpPS := by rw [T3_sq_mul_kpPS]
    _ = (1 + kpPS) * T3 ^ 2 := by ring

private lemma X_dPS_lamPS : X * dPS lamPS = lamPS * (1 - lamPS) * T3 ^ 4 := by
  set D : PowerSeries ℚ := muPS * (1 - lamPS) * T3 ^ 4
  have hD0 : coeff 0 D = 16 := by
    dsimp only [D]
    rw [coeff_zero_mul, coeff_zero_mul, coeff_zero_muPS, map_sub, coeff_one, if_pos rfl,
      coeff_zero_lamPS, coeff_zero_T3_pow]
    norm_num
  have hD0_ne : coeff 0 D ≠ 0 := by rw [hD0]; norm_num
  set L : PowerSeries ℚ := dPS lamPS * psInv D
  have hL0 : coeff 0 L = 1 := by
    have hdlam : dPS lamPS = muPS + X * dPS muPS := by
      unfold lamPS; rw [dPS_mul, dPS_X, one_mul]
    have hdlam0 : coeff 0 (dPS lamPS) = 16 := by
      rw [hdlam, map_add, coeff_zero_muPS, coeff_zero_X_mul, add_zero]
    dsimp only [L]
    rw [coeff_zero_mul, hdlam0, coeff_zero_psInv hD0_ne, hD0]
    norm_num
  have hL_def : L * (lamPS * (1 - lamPS) * T3 ^ 4) = X * dPS lamPS := by
    have hXD : X * D = lamPS * (1 - lamPS) * T3 ^ 4 := by
      dsimp only [D]; unfold lamPS; ring
    rw [← hXD]
    calc L * (X * D) = X * (dPS lamPS * (D * psInv D)) := by dsimp only [L]; ring
      _ = X * (dPS lamPS * 1) := by rw [mul_psInv hD0_ne]
      _ = X * dPS lamPS := by ring
  have hpsSq_L : psSq L = L := by
    -- Key derivative relations
    have hdv : (1 + kpPS) ^ 2 * dPS vPS = -2 * dPS kpPS := by
      have hd1 := congrArg dPS one_add_kp_mul_v
      rw [dPS_mul, dPS_add, dPS_sub, dPS_one, zero_add, zero_sub] at hd1
      -- hd1 : dPS kpPS * vPS + (1 + kpPS) * dPS vPS = -dPS kpPS
      have hsub : (1 + kpPS) * dPS vPS = -(1 + vPS) * dPS kpPS := by linear_combination hd1
      calc (1 + kpPS) ^ 2 * dPS vPS = (1 + kpPS) * ((1 + kpPS) * dPS vPS) := by ring
        _ = (1 + kpPS) * (-(1 + vPS) * dPS kpPS) := by rw [hsub]
        _ = -((1 + kpPS) * (1 + vPS)) * dPS kpPS := by ring
        _ = -2 * dPS kpPS := by rw [one_add_kp_mul_one_add_v]
    have hdlam_kp : dPS lamPS = -2 * kpPS * dPS kpPS := by
      have hd1 := congrArg dPS lamPS_add_kpPS_sq
      rw [dPS_add, dPS_pow, dPS_one] at hd1
      simp only [Nat.cast_ofNat, show 2 - 1 = 1 by rfl, pow_one] at hd1
      linear_combination hd1
    have hkp_dv : (1 + kpPS) ^ 2 * kpPS * dPS vPS = dPS lamPS := by
      calc (1 + kpPS) ^ 2 * kpPS * dPS vPS
          = kpPS * ((1 + kpPS) ^ 2 * dPS vPS) := by ring
        _ = kpPS * (-2 * dPS kpPS) := by rw [hdv]
        _ = -2 * kpPS * dPS kpPS := by ring
        _ = dPS lamPS := hdlam_kp.symm
    have hps_Xdlam : psSq (X * dPS lamPS) = X * vPS * dPS vPS := by
      have h1 : 2 * psSq (X * dPS lamPS) = 2 * (X * vPS * dPS vPS) := by
        calc 2 * psSq (X * dPS lamPS)
            = 2 * (psSq X * psSq (dPS lamPS)) := by rw [psSq_mul]
          _ = X * (2 * X * psSq (dPS lamPS)) := by rw [psSq_X]; ring
          _ = X * dPS (psSq lamPS) := by rw [dPS_psSq]
          _ = X * dPS (vPS ^ 2) := by rw [psSq_lamPS]
          _ = X * (2 * vPS * dPS vPS) := by rw [dPS_pow]; simp
          _ = 2 * (X * vPS * dPS vPS) := by ring
      have h2ne : (2 : PowerSeries ℚ) ≠ 0 := ps_ne_zero_of_coeff (n := 0) (by rw [show (2 : PowerSeries ℚ) = C 2 by rfl, coeff_C]; norm_num)
      exact mul_left_cancel₀ h2ne h1
    have hps_1_sub_lam : (1 + kpPS) ^ 2 * (1 - psSq lamPS) = 4 * kpPS := by
      rw [psSq_lamPS]
      have hsub : (1 + kpPS) * (1 - vPS) = 2 * kpPS := by
        have := one_add_kp_mul_v
        calc (1 + kpPS) * (1 - vPS) = (1 + kpPS) - (1 + kpPS) * vPS := by ring
          _ = (1 + kpPS) - (1 - kpPS) := by rw [this]
          _ = 2 * kpPS := by ring
      calc (1 + kpPS) ^ 2 * (1 - vPS ^ 2)
          = ((1 + kpPS) * (1 - vPS)) * ((1 + kpPS) * (1 + vPS)) := by ring
        _ = (2 * kpPS) * 2 := by rw [hsub, one_add_kp_mul_one_add_v]
        _ = 4 * kpPS := by ring
    have hps_T3_4 : 4 * psSq (T3 ^ 4) = (1 + kpPS) ^ 2 * T3 ^ 4 := by
      have hsq : (1 + vPS) ^ 2 * psSq (T3 ^ 4) = T3 ^ 4 := by
        calc (1 + vPS) ^ 2 * psSq (T3 ^ 4)
            = ((1 + vPS) * psSq (T3 ^ 2)) ^ 2 := by
              rw [show (T3 ^ 4 : PowerSeries ℚ) = T3 ^ 2 * T3 ^ 2 by ring, psSq_mul]; ring
          _ = (T3 ^ 2) ^ 2 := by rw [T3_sq_psSq]
          _ = T3 ^ 4 := by ring
      calc 4 * psSq (T3 ^ 4)
          = ((1 + kpPS) * (1 + vPS)) ^ 2 * psSq (T3 ^ 4) := by rw [one_add_kp_mul_one_add_v]; ring
        _ = (1 + kpPS) ^ 2 * ((1 + vPS) ^ 2 * psSq (T3 ^ 4)) := by ring
        _ = (1 + kpPS) ^ 2 * T3 ^ 4 := by rw [hsq]
    have hbig : psSq L * (4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4) =
        L * (4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4) := by
      have hps_eq : psSq L * (psSq lamPS * (1 - psSq lamPS) * psSq (T3 ^ 4)) = X * vPS * dPS vPS := by
        rw [← psSq_one, ← psSq_sub, ← psSq_mul, ← psSq_mul, ← psSq_mul, hL_def, hps_Xdlam]
      have hden : 4 * (1 + kpPS) ^ 2 * (psSq lamPS * (1 - psSq lamPS) * psSq (T3 ^ 4)) =
          4 * vPS ^ 2 * kpPS * (1 + kpPS) ^ 2 * T3 ^ 4 := by
        calc 4 * (1 + kpPS) ^ 2 * (psSq lamPS * (1 - psSq lamPS) * psSq (T3 ^ 4))
            = psSq lamPS * ((1 + kpPS) ^ 2 * (1 - psSq lamPS)) * (4 * psSq (T3 ^ 4)) := by ring
          _ = vPS ^ 2 * (4 * kpPS) * ((1 + kpPS) ^ 2 * T3 ^ 4) := by rw [hps_1_sub_lam, psSq_lamPS, hps_T3_4]
          _ = 4 * vPS ^ 2 * kpPS * (1 + kpPS) ^ 2 * T3 ^ 4 := by ring
      have hlam_v : (1 + kpPS) ^ 2 * vPS = lamPS := by
        have hlam : lamPS = (1 + kpPS) * (1 - kpPS) := by linear_combination lamPS_add_kpPS_sq
        calc (1 + kpPS) ^ 2 * vPS = (1 + kpPS) * ((1 + kpPS) * vPS) := by ring
          _ = (1 + kpPS) * (1 - kpPS) := by rw [one_add_kp_mul_v]
          _ = lamPS := hlam.symm
      calc psSq L * (4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4)
          = (psSq L * (4 * vPS ^ 2 * kpPS * (1 + kpPS) ^ 2 * T3 ^ 4)) * kpPS := by ring
        _ = (psSq L * (4 * (1 + kpPS) ^ 2 * (psSq lamPS * (1 - psSq lamPS) * psSq (T3 ^ 4)))) * kpPS := by rw [← hden]
        _ = 4 * (1 + kpPS) ^ 2 * kpPS * (psSq L * (psSq lamPS * (1 - psSq lamPS) * psSq (T3 ^ 4))) := by ring
        _ = 4 * (1 + kpPS) ^ 2 * kpPS * (X * vPS * dPS vPS) := by rw [← mul_assoc, ← hps_eq]; ring
        _ = 4 * vPS * (X * ((1 + kpPS) ^ 2 * kpPS * dPS vPS)) := by ring
        _ = 4 * vPS * (X * dPS lamPS) := by rw [hkp_dv]
        _ = 4 * vPS * (L * (lamPS * (1 - lamPS) * T3 ^ 4)) := by rw [← hL_def]
        _ = L * (4 * vPS * ((1 + kpPS) ^ 2 * vPS) * kpPS ^ 2 * T3 ^ 4) := by rw [one_sub_lamPS, ← hlam_v]; ring
        _ = L * (4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4) := by ring
    -- Cancel the nonzero factor 4 * vPS^2 * kpPS^2 * (1 + kpPS)^2 * T3^4
    have hv_ne : vPS ≠ 0 := by
      intro hvz
      have h1 := one_add_kp_mul_v
      rw [hvz, mul_zero] at h1
      have hkp1 : kpPS = 1 := by linear_combination h1
      have hT : T3 ^ 2 = T4 ^ 2 := by rw [← T3_sq_mul_kpPS, hkp1, mul_one]
      have hc := congrArg (coeff 1) hT
      rw [sq, sq, coeff_one_mul, coeff_one_mul, coeff_zero_T3, coeff_one_T3, coeff_zero_T4, coeff_one_T4] at hc
      norm_num at hc
    have hrest_ne : 4 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4 ≠ 0 := by
      apply ps_ne_zero_of_coeff (n := 0)
      rw [coeff_zero_mul, coeff_zero_mul, coeff_zero_mul, show (4 : PowerSeries ℚ) = C 4 by rfl,
        coeff_C, if_pos rfl, coeff_zero_pow, coeff_zero_kpPS, coeff_zero_pow, coeff_zero_one_add_kpPS,
        coeff_zero_T3_pow]
      norm_num
    have hfac_ne : 4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4 ≠ 0 := by
      have : 4 * vPS ^ 2 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4 =
          vPS ^ 2 * (4 * kpPS ^ 2 * (1 + kpPS) ^ 2 * T3 ^ 4) := by ring
      rw [this]
      exact mul_ne_zero (pow_ne_zero 2 hv_ne) hrest_ne
    exact mul_right_cancel₀ hfac_ne hbig
  have hL1 : L = 1 := eq_one_of_psSq_eq hpsSq_L hL0
  rw [← hL_def, hL1, one_mul]

private lemma X_dPS_yPS : X * dPS yPS = yPS * (1 - 2 * lamPS) * T3 ^ 4 := by
  have hd : dPS yPS = (1 - 2 * lamPS) * C (1 / 16) * dPS lamPS := by
    unfold yPS
    rw [dPS_mul, dPS_mul, dPS_C, mul_zero, add_zero, dPS_sub, dPS_one, zero_sub]
    ring
  calc X * dPS yPS = (1 - 2 * lamPS) * C (1 / 16) * (X * dPS lamPS) := by rw [hd]; ring
    _ = (1 - 2 * lamPS) * C (1 / 16) * (lamPS * (1 - lamPS) * T3 ^ 4) := by rw [X_dPS_lamPS]
    _ = (lamPS * (1 - lamPS) * C (1 / 16)) * (1 - 2 * lamPS) * T3 ^ 4 := by ring
    _ = yPS * (1 - 2 * lamPS) * T3 ^ 4 := rfl

private lemma psComp_sq_yPS :
    psComp (PowerSeries.mk (fun n => (sqCoeff n : ℚ))) yPS = 1 - 2 * lamPS := by
  set sqQ : PowerSeries ℚ := PowerSeries.mk (fun n => (sqCoeff n : ℚ))
  have hsqQ_sq : sqQ ^ 2 = 1 - 64 * X := by
    have hZ := congrArg (PowerSeries.map (Int.castRingHom ℚ)) sqCoeff_sq
    rw [map_pow, map_sub, map_one, map_mul, map_ofNat, PowerSeries.map_X] at hZ
    have hmap : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk sqCoeff) = sqQ := by
      ext n; simp [sqQ, PowerSeries.coeff_map]
    rwa [hmap] at hZ
  set A : PowerSeries ℚ := psComp sqQ yPS
  set B : PowerSeries ℚ := 1 - 2 * lamPS
  have hA2 : A ^ 2 = 1 - 64 * yPS := by
    calc A ^ 2 = psComp (sqQ ^ 2) yPS := (psComp_pow sqQ coeff_zero_yPS 2).symm
      _ = psComp (1 - 64 * X) yPS := by rw [hsqQ_sq]
      _ = psComp 1 yPS - psComp (C 64 * X) yPS := by rw [psComp_sub]; rfl
      _ = 1 - 64 * yPS := by rw [psComp_one, psComp_C_mul, psComp_X coeff_zero_yPS]; rfl
  have hB2 : B ^ 2 = 1 - 64 * yPS := by
    dsimp only [B]; unfold yPS
    have h64 : (64 : PowerSeries ℚ) * C (1 / 16) = 4 := by
      rw [show (64 : PowerSeries ℚ) = C 64 by rfl, ← map_mul]; norm_num; rfl
    calc (1 - 2 * lamPS) ^ 2 = 1 - 4 * (lamPS * (1 - lamPS)) := by ring
      _ = 1 - ((64 : PowerSeries ℚ) * C (1 / 16)) * (lamPS * (1 - lamPS)) := by rw [h64]
      _ = 1 - 64 * (lamPS * (1 - lamPS) * C (1 / 16)) := by ring
  have hdiff : (A - B) * (A + B) = 0 := by
    calc (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
      _ = (1 - 64 * yPS) - (1 - 64 * yPS) := by rw [hA2, hB2]
      _ = 0 := sub_self _
  have hsum_ne : A + B ≠ 0 := by
    apply ps_ne_zero_of_coeff (n := 0)
    rw [map_add]
    have hA0 : coeff 0 A = 1 := by
      dsimp only [A, sqQ]; rw [coeff_zero_psComp, coeff_mk]; rfl
    have hB0 : coeff 0 B = 1 := by
      dsimp only [B]; rw [map_sub, coeff_one, if_pos rfl, show (2 : PowerSeries ℚ) = C 2 by rfl,
        coeff_C_mul, coeff_zero_lamPS]; norm_num
    rw [hA0, hB0]; norm_num
  have hAB : A - B = 0 := (mul_eq_zero.mp hdiff).resolve_right hsum_ne
  exact sub_eq_zero.mp hAB

/-! #### Hypergeometric series `F`, `H`, Landen's ODE, and Clausen's ODE -/

private def F_ps : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (((2 * n).choose n : ℚ) / 4 ^ n) ^ 2)

private def H_ps : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((2 * n).choose n : ℚ) ^ 3)

private lemma centralBinom_succ_rat (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * ((2 * (n + 1)).choose (n + 1) : ℚ) =
      2 * ((2 * n + 1 : ℕ) : ℚ) * ((2 * n).choose n : ℚ) := by
  have hnat : (n + 1) * (2 * (n + 1)).choose (n + 1) = 2 * (2 * n + 1) * (2 * n).choose n := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * (n + 1) by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega] at h1
    rw [show 2 * n - n = n by omega] at h2
    have hfac : (2 * (n + 1)).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have hpos : 0 < n.factorial * n.factorial * (n + 1) := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (n + 1) * (2 * (n + 1)).choose (n + 1) * (n.factorial * n.factorial * (n + 1))
        = (2 * (n + 1)).choose (n + 1) * ((n + 1).factorial * (n + 1).factorial) := by
          rw [Nat.factorial_succ]; ring
      _ = (2 * (n + 1)).factorial := by linarith [h1]
      _ = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := hfac
      _ = (2 * n + 2) * (2 * n + 1) * ((2 * n).choose n * (n.factorial * n.factorial)) := by rw [← h2]; ring
      _ = 2 * (2 * n + 1) * (2 * n).choose n * (n.factorial * n.factorial * (n + 1)) := by ring
  exact_mod_cast hnat

private lemma F_coeff_rec (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) ^ 2 * coeff (n + 1) F_ps = ((n : ℚ) + 1 / 2) ^ 2 * coeff n F_ps := by
  unfold F_ps; simp only [coeff_mk]
  have hcb := centralBinom_succ_rat n
  have h4 : (4 : ℚ) ^ (n + 1) = 4 * (4 : ℚ) ^ n := by rw [pow_succ]; ring
  rw [h4]
  have hdiv : ((n + 1 : ℕ) : ℚ) * (((2 * (n + 1)).choose (n + 1) : ℚ) / (4 * 4 ^ n)) =
      ((n : ℚ) + 1 / 2) * (((2 * n).choose n : ℚ) / 4 ^ n) := by
    have h4ne : (4 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    field_simp [h4ne]
    push_cast at hcb ⊢
    linarith [hcb]
  calc ((n + 1 : ℕ) : ℚ) ^ 2 * (((2 * (n + 1)).choose (n + 1) : ℚ) / (4 * 4 ^ n)) ^ 2
      = (((n + 1 : ℕ) : ℚ) * (((2 * (n + 1)).choose (n + 1) : ℚ) / (4 * 4 ^ n))) ^ 2 := by ring
    _ = (((n : ℚ) + 1 / 2) * (((2 * n).choose n : ℚ) / 4 ^ n)) ^ 2 := by rw [hdiv]
    _ = ((n : ℚ) + 1 / 2) ^ 2 * (((2 * n).choose n : ℚ) / 4 ^ n) ^ 2 := by ring

private lemma H_coeff_rec (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) ^ 3 * coeff (n + 1) H_ps = 8 * (2 * (n : ℚ) + 1) ^ 3 * coeff n H_ps := by
  unfold H_ps; simp only [coeff_mk]
  have hcb := centralBinom_succ_rat n
  push_cast at hcb ⊢
  calc ((n : ℚ) + 1) ^ 3 * ((2 * (n + 1)).choose (n + 1) : ℚ) ^ 3
      = (((n : ℚ) + 1) * ((2 * (n + 1)).choose (n + 1) : ℚ)) ^ 3 := by ring
    _ = (2 * (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ)) ^ 3 := by rw [hcb]
    _ = 8 * (2 * (n : ℚ) + 1) ^ 3 * ((2 * n).choose n : ℚ) ^ 3 := by ring

private lemma coeff_X_mul_eq (n : ℕ) (f : PowerSeries ℚ) :
    coeff n (X * f) = if n = 0 then 0 else coeff (n - 1) f := by
  rcases n with _ | m
  · simp [coeff_zero_X_mul]
  · simp [coeff_succ_X_mul]

private lemma coeff_X_pow_mul_eq (k n : ℕ) (f : PowerSeries ℚ) :
    coeff n (X ^ k * f) = if n < k then 0 else coeff (n - k) f := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, coeff_X_mul_eq]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      rw [ih m]
      by_cases h : m < k
      · rw [if_pos h, if_pos (show m + 1 < k + 1 by omega)]
      · rw [if_neg h, if_neg (show ¬ (m + 1 < k + 1) by omega),
          show m + 1 - (k + 1) = m - k by omega]

private lemma F_ode :
    X * (1 - X) * dPS (dPS F_ps) + (1 - 2 * X) * dPS F_ps - C (1 / 4) * F_ps = 0 := by
  have hrew : X * (1 - X) * dPS (dPS F_ps) + (1 - 2 * X) * dPS F_ps - C (1 / 4) * F_ps =
      X * dPS (dPS F_ps) - X ^ 2 * dPS (dPS F_ps) + dPS F_ps - C 2 * (X * dPS F_ps) - C (1 / 4) * F_ps := by
    rw [show (2 : PowerSeries ℚ) = C 2 by rfl]; ring
  rw [hrew]
  ext n
  rw [map_zero, map_sub, map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul,
    coeff_X_mul_eq, coeff_X_pow_mul_eq, coeff_X_mul_eq]
  have hrec := F_coeff_rec n
  rcases n with _ | _ | m
  · simp only [if_true, coeff_dPS, Nat.cast_zero, zero_add] at hrec ⊢
    push_cast at hrec ⊢
    linarith [hrec]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      show (1 : ℕ) < 2 by omega, if_true, Nat.sub_self, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢
    linarith [hrec]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      show ¬ (m + 2 < 2) by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢
    linarith [hrec]

private lemma H_ode :
    X ^ 2 * (1 - 64 * X) * dPS (dPS (dPS H_ps)) + 3 * X * (1 - 96 * X) * dPS (dPS H_ps) +
      (1 - 208 * X) * dPS H_ps - 8 * H_ps = 0 := by
  have hrew : X ^ 2 * (1 - 64 * X) * dPS (dPS (dPS H_ps)) + 3 * X * (1 - 96 * X) * dPS (dPS H_ps) +
        (1 - 208 * X) * dPS H_ps - 8 * H_ps =
      X ^ 2 * dPS (dPS (dPS H_ps)) - C 64 * (X ^ 3 * dPS (dPS (dPS H_ps))) +
      C 3 * (X * dPS (dPS H_ps)) - C 288 * (X ^ 2 * dPS (dPS H_ps)) +
      dPS H_ps - C 208 * (X * dPS H_ps) - C 8 * H_ps := by
    have hc3 : (3 : PowerSeries ℚ) = C 3 := rfl
    have hc8 : (8 : PowerSeries ℚ) = C 8 := rfl
    have hc64 : (64 : PowerSeries ℚ) = C 64 := rfl
    have hc96 : (96 : PowerSeries ℚ) = C 96 := rfl
    have hc208 : (208 : PowerSeries ℚ) = C 208 := rfl
    rw [hc3, hc8, hc64, hc96, hc208]
    have h396 : C (3 : ℚ) * C 96 = C 288 := by rw [← map_mul]; norm_num
    calc X ^ 2 * (1 - C 64 * X) * dPS (dPS (dPS H_ps)) + C 3 * X * (1 - C 96 * X) * dPS (dPS H_ps) +
          (1 - C 208 * X) * dPS H_ps - C 8 * H_ps
        = X ^ 2 * dPS (dPS (dPS H_ps)) - C 64 * (X ^ 3 * dPS (dPS (dPS H_ps))) +
          C 3 * (X * dPS (dPS H_ps)) - (C 3 * C 96) * (X ^ 2 * dPS (dPS H_ps)) +
          dPS H_ps - C 208 * (X * dPS H_ps) - C 8 * H_ps := by ring
      _ = _ := by rw [h396]
  rw [hrew]
  ext n
  rw [map_zero, map_sub, map_sub, map_add, map_sub, map_add, map_sub,
    coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_mul_eq, coeff_X_pow_mul_eq, coeff_X_mul_eq]
  have hrec := H_coeff_rec n
  rcases n with _ | _ | _ | m
  · simp only [show (0 : ℕ) < 2 by omega, show (0 : ℕ) < 3 by omega, if_true, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢; linarith [hrec]
  · simp only [show (1 : ℕ) < 2 by omega, show (1 : ℕ) < 3 by omega,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_true, if_false, Nat.sub_self, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢; linarith [hrec]
  · simp only [show ¬ ((2 : ℕ) < 2) by omega, show (2 : ℕ) < 3 by omega,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_true, if_false,
      show 2 - 1 = 1 by rfl, show 2 - 2 = 0 by rfl, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢; linarith [hrec]
  · simp only [show ¬ (m + 3 < 2) by omega, show ¬ (m + 3 < 3) by omega,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, coeff_dPS] at hrec ⊢
    push_cast at hrec ⊢; linarith [hrec]

private lemma landen_ode_unique {Y : PowerSeries ℚ}
    (hode : X * (1 - X ^ 2) * dPS (dPS Y) + (1 - 3 * X ^ 2) * dPS Y - X * Y = 0)
    (h0 : coeff 0 Y = 0) : Y = 0 := by
  have hrew : X * (1 - X ^ 2) * dPS (dPS Y) + (1 - 3 * X ^ 2) * dPS Y - X * Y =
      X * dPS (dPS Y) - X ^ 3 * dPS (dPS Y) + dPS Y - C 3 * (X ^ 2 * dPS Y) - X * Y := by
    rw [show (3 : PowerSeries ℚ) = C 3 by rfl]; ring
  rw [hrew] at hode
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | m
    · exact h0
    · have hc := congrArg (coeff m) hode
      rw [map_zero, map_sub, map_sub, map_add, map_sub, coeff_C_mul,
        coeff_X_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_mul_eq] at hc
      have hprev : ∀ k ≤ m, coeff k Y = 0 := fun k hk => ih k (by omega)
      have hterm1 : (if m = 0 then (0 : ℚ) else coeff (m - 1) (dPS (dPS Y))) =
          ((m : ℚ) * ((m + 1 : ℕ) : ℚ)) * coeff (m + 1) Y := by
        rcases m with _ | m'
        · simp
        · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel, coeff_dPS]
          push_cast; ring
      have hterm2 : (if m < 3 then (0 : ℚ) else coeff (m - 3) (dPS (dPS Y))) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, coeff_dPS, hprev (m - 3 + 1 + 1) (by omega)]; ring
      have hterm3 : (if m < 2 then (0 : ℚ) else coeff (m - 2) (dPS Y)) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, hprev (m - 2 + 1) (by omega)]; ring
      have hterm4 : (if m = 0 then (0 : ℚ) else coeff (m - 1) Y) = 0 := by
        split_ifs with h
        · rfl
        · exact hprev (m - 1) (by omega)
      rw [hterm1, hterm2, hterm3, hterm4, coeff_dPS] at hc
      have hfac : (((m + 1 : ℕ) : ℚ) ^ 2) * coeff (m + 1) Y = 0 := by
        push_cast at hc ⊢; linarith [hc]
      have hm_ne : (((m + 1 : ℕ) : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (by positivity)
      exact (mul_eq_zero.mp hfac).resolve_left hm_ne

private lemma landen_id :
    psComp F_ps (X ^ 2) = psInv (1 + X) * psComp F_ps (4 * X * psInv ((1 + X) ^ 2)) := by
  have h1pX0 : coeff 0 (1 + X : PowerSeries ℚ) = 1 := by
    rw [map_add, coeff_one, if_pos rfl, coeff_X, if_neg (by decide), add_zero]
  have h1pX0_ne : coeff 0 (1 + X : PowerSeries ℚ) ≠ 0 := by rw [h1pX0]; norm_num
  have h1pX2_ne : coeff 0 ((1 + X : PowerSeries ℚ) ^ 2) ≠ 0 := by rw [coeff_zero_pow, h1pX0]; norm_num
  set A : PowerSeries ℚ := psComp F_ps (X ^ 2)
  set w : PowerSeries ℚ := 4 * X * psInv ((1 + X) ^ 2)
  set B : PowerSeries ℚ := psInv (1 + X) * psComp F_ps w
  have hw0 : coeff 0 w = 0 := by
    dsimp only [w]
    rw [coeff_zero_mul, coeff_zero_mul, coeff_X, if_neg (by decide), mul_zero, zero_mul]
  have hX2_0 : coeff 0 (X ^ 2 : PowerSeries ℚ) = 0 := by rw [coeff_X_pow]; norm_num
  have hA_ode : X * (1 - X ^ 2) * dPS (dPS A) + (1 - 3 * X ^ 2) * dPS A - X * A = 0 := by
    set F0 := psComp F_ps (X ^ 2)
    set F1 := psComp (dPS F_ps) (X ^ 2)
    set F2 := psComp (dPS (dPS F_ps)) (X ^ 2)
    have hdA : dPS A = 2 * X * F1 := by
      dsimp only [A, F1]
      rw [dPS_psComp F_ps hX2_0, dPS_pow, dPS_X]; simp; ring
    have hddA : dPS (dPS A) = 2 * F1 + 4 * X ^ 2 * F2 := by
      rw [hdA, dPS_mul, dPS_mul, show (2 : PowerSeries ℚ) = C 2 by rfl, dPS_C, dPS_X,
        dPS_psComp (dPS F_ps) hX2_0, dPS_pow, dPS_X]
      dsimp only [F2]
      rw [show C (2 : ℚ) = 2 by rfl]
      simp; ring
    have hF_at : X ^ 2 * (1 - X ^ 2) * F2 + (1 - 2 * X ^ 2) * F1 - C (1 / 4) * F0 = 0 := by
      have h := congrArg (fun p => psComp p (X ^ 2)) F_ode
      simp only [psComp_zero, psComp_sub, psComp_add, psComp_mul _ _ hX2_0, psComp_one,
        psComp_X hX2_0, show (2 : PowerSeries ℚ) = C 2 by rfl, psComp_C] at h
      simpa only [F0, F1, F2, show C (2 : ℚ) = 2 by rfl] using h
    have h4 : (4 : PowerSeries ℚ) * C (1 / 4) = 1 := by
      rw [show (4 : PowerSeries ℚ) = C 4 by rfl, ← map_mul]; norm_num
    calc X * (1 - X ^ 2) * dPS (dPS A) + (1 - 3 * X ^ 2) * dPS A - X * A
        = X * (1 - X ^ 2) * (2 * F1 + 4 * X ^ 2 * F2) + (1 - 3 * X ^ 2) * (2 * X * F1) - X * F0 := by
          rw [hddA, hdA]
      _ = 4 * X * (X ^ 2 * (1 - X ^ 2) * F2 + (1 - 2 * X ^ 2) * F1) - (4 * C (1 / 4)) * X * F0 := by
          rw [h4]; ring
      _ = 4 * X * (X ^ 2 * (1 - X ^ 2) * F2 + (1 - 2 * X ^ 2) * F1 - C (1 / 4) * F0) := by ring
      _ = 4 * X * 0 := by rw [hF_at]
      _ = 0 := mul_zero _
  have hB_ode : X * (1 - X ^ 2) * dPS (dPS B) + (1 - 3 * X ^ 2) * dPS B - X * B = 0 := by
    set F0 := psComp F_ps w
    set F1 := psComp (dPS F_ps) w
    set F2 := psComp (dPS (dPS F_ps)) w
    set s : PowerSeries ℚ := 1 + X
    have hs_ne : s ^ 7 ≠ 0 := ps_ne_zero_of_coeff (by rw [coeff_zero_pow, h1pX0]; norm_num)
    have hs_w : s ^ 2 * w = 4 * X := by
      dsimp only [s, w]
      calc (1 + X) ^ 2 * (4 * X * psInv ((1 + X) ^ 2))
          = 4 * X * ((1 + X) ^ 2 * psInv ((1 + X) ^ 2)) := by ring
        _ = 4 * X * 1 := by rw [mul_psInv h1pX2_ne]
        _ = 4 * X := mul_one _
    have hs_B : s * B = F0 := by
      dsimp only [s, B, F0]
      calc (1 + X) * (psInv (1 + X) * psComp F_ps w)
          = ((1 + X) * psInv (1 + X)) * psComp F_ps w := by ring
        _ = 1 * psComp F_ps w := by rw [mul_psInv h1pX0_ne]
        _ = psComp F_ps w := one_mul _
    have hds : dPS s = 1 := by dsimp only [s]; rw [dPS_add, dPS_one, dPS_X, zero_add]
    have hdw : s ^ 3 * dPS w = 4 * (1 - X) := by
      have hd := congrArg dPS hs_w
      rw [dPS_mul, dPS_pow, hds, show (4 : PowerSeries ℚ) = C 4 by rfl, dPS_C_mul, dPS_X] at hd
      simp only [Nat.cast_ofNat, show 2 - 1 = 1 by rfl, pow_one, mul_one] at hd
      calc s ^ 3 * dPS w = s * (2 * s * w + s ^ 2 * dPS w) - 2 * (s ^ 2 * w) := by ring
        _ = s * C 4 - 2 * (4 * X) := by rw [hd, hs_w]
        _ = 4 * (1 - X) := by dsimp only [s]; rw [show C (4 : ℚ) = 4 by rfl]; ring
    have hddw : s ^ 4 * dPS (dPS w) = 8 * (X - 2) := by
      have hd := congrArg dPS hdw
      rw [dPS_mul, dPS_pow, hds, show (4 : PowerSeries ℚ) = C 4 by rfl, dPS_C_mul, dPS_sub, dPS_one, dPS_X] at hd
      simp only [Nat.cast_ofNat, show 3 - 1 = 2 by rfl, mul_one, zero_sub] at hd
      calc s ^ 4 * dPS (dPS w) = s * (3 * s ^ 2 * dPS w + s ^ 3 * dPS (dPS w)) - 3 * (s ^ 3 * dPS w) := by ring
        _ = s * (C 4 * (-1)) - 3 * (4 * (1 - X)) := by rw [hd, hdw]
        _ = 8 * (X - 2) := by dsimp only [s]; rw [show C (4 : ℚ) = 4 by rfl]; ring
    have hdF0 : dPS F0 = F1 * dPS w := dPS_psComp F_ps hw0
    have hdF1 : dPS F1 = F2 * dPS w := dPS_psComp (dPS F_ps) hw0
    have hd_sB : B + s * dPS B = F1 * dPS w := by
      have hd := congrArg dPS hs_B
      rwa [dPS_mul, hds, one_mul, hdF0] at hd
    have hdB4 : s ^ 4 * dPS B = 4 * (1 - X) * F1 - s ^ 2 * F0 := by
      calc s ^ 4 * dPS B = s ^ 3 * (B + s * dPS B) - s ^ 2 * (s * B) := by ring
        _ = F1 * (s ^ 3 * dPS w) - s ^ 2 * F0 := by rw [hd_sB, hs_B]; ring
        _ = 4 * (1 - X) * F1 - s ^ 2 * F0 := by rw [hdw]; ring
    have hddB7 : s ^ 7 * dPS (dPS B) =
        16 * (1 - X) ^ 2 * F2 + 8 * s ^ 2 * (2 * X - 3) * F1 + 2 * s ^ 4 * F0 := by
      have hd2 := congrArg dPS hd_sB
      have hd2_gen : ∀ (p q : PowerSeries ℚ), dPS p = 1 →
          dPS (q + p * dPS q) = 2 * dPS q + p * dPS (dPS q) := by
        intro p q hp; rw [dPS_add, dPS_mul, hp, one_mul]; ring
      have hd2_lhs : dPS (B + s * dPS B) = 2 * dPS B + s * dPS (dPS B) := hd2_gen s B hds
      have hd2_rhs : dPS (F1 * dPS w) = F2 * (dPS w) ^ 2 + F1 * dPS (dPS w) := by
        rw [dPS_mul, hdF1]; ring
      have h2B : 2 * dPS B + s * dPS (dPS B) = F2 * (dPS w) ^ 2 + F1 * dPS (dPS w) := by
        rw [← hd2_lhs, ← hd2_rhs]; exact hd2
      calc s ^ 7 * dPS (dPS B)
          = s ^ 6 * (2 * dPS B + s * dPS (dPS B)) - 2 * s ^ 2 * (s ^ 4 * dPS B) := by ring
        _ = F2 * (s ^ 3 * dPS w) ^ 2 + s ^ 2 * F1 * (s ^ 4 * dPS (dPS w)) -
            2 * s ^ 2 * (4 * (1 - X) * F1 - s ^ 2 * F0) := by rw [h2B, hdB4]; ring
        _ = F2 * (4 * (1 - X)) ^ 2 + s ^ 2 * F1 * (8 * (X - 2)) -
            2 * s ^ 2 * (4 * (1 - X) * F1 - s ^ 2 * F0) := by rw [hdw, hddw]
        _ = 16 * (1 - X) ^ 2 * F2 + 8 * s ^ 2 * (2 * X - 3) * F1 + 2 * s ^ 4 * F0 := by ring
    have hF_at : w * (1 - w) * F2 + (1 - 2 * w) * F1 - C (1 / 4) * F0 = 0 := by
      have h := congrArg (fun p => psComp p w) F_ode
      simp only [psComp_zero, psComp_sub, psComp_add, psComp_mul _ _ hw0, psComp_one,
        psComp_X hw0, show (2 : PowerSeries ℚ) = C 2 by rfl, psComp_C] at h
      simpa only [F0, F1, F2, show C (2 : ℚ) = 2 by rfl] using h
    have hF_cleared : 4 * X * (1 - X) ^ 2 * F2 + s ^ 2 * (1 - 6 * X + X ^ 2) * F1 - C (1 / 4) * s ^ 4 * F0 = 0 := by
      have h4w : s ^ 4 * (w * (1 - w)) = 4 * X * (1 - X) ^ 2 := by
        calc s ^ 4 * (w * (1 - w)) = (s ^ 2 * w) * (s ^ 2 - s ^ 2 * w) := by ring
          _ = (4 * X) * (s ^ 2 - 4 * X) := by rw [hs_w]
          _ = 4 * X * (1 - X) ^ 2 := by dsimp only [s]; ring
      have h2w : s ^ 4 * (1 - 2 * w) = s ^ 2 * (1 - 6 * X + X ^ 2) := by
        calc s ^ 4 * (1 - 2 * w) = s ^ 2 * (s ^ 2 - 2 * (s ^ 2 * w)) := by ring
          _ = s ^ 2 * (s ^ 2 - 2 * (4 * X)) := by rw [hs_w]
          _ = s ^ 2 * (1 - 6 * X + X ^ 2) := by dsimp only [s]; ring
      calc 4 * X * (1 - X) ^ 2 * F2 + s ^ 2 * (1 - 6 * X + X ^ 2) * F1 - C (1 / 4) * s ^ 4 * F0
          = s ^ 4 * (w * (1 - w) * F2 + (1 - 2 * w) * F1 - C (1 / 4) * F0) := by
            rw [← h4w, ← h2w]; ring
        _ = s ^ 4 * 0 := by rw [hF_at]
        _ = 0 := mul_zero _
    have h4 : (4 : PowerSeries ℚ) * C (1 / 4) = 1 := by
      rw [show (4 : PowerSeries ℚ) = C 4 by rfl, ← map_mul]; norm_num
    apply mul_left_cancel₀ hs_ne
    rw [mul_zero]
    calc s ^ 7 * (X * (1 - X ^ 2) * dPS (dPS B) + (1 - 3 * X ^ 2) * dPS B - X * B)
        = X * (1 - X ^ 2) * (s ^ 7 * dPS (dPS B)) + s ^ 3 * (1 - 3 * X ^ 2) * (s ^ 4 * dPS B) -
          X * s ^ 6 * (s * B) := by ring
      _ = X * (1 - X ^ 2) * (16 * (1 - X) ^ 2 * F2 + 8 * s ^ 2 * (2 * X - 3) * F1 + 2 * s ^ 4 * F0) +
          s ^ 3 * (1 - 3 * X ^ 2) * (4 * (1 - X) * F1 - s ^ 2 * F0) - X * s ^ 6 * F0 := by
          rw [hddB7, hdB4, hs_B]
      _ = 4 * (1 - X) * s * (4 * X * (1 - X) ^ 2 * F2 + s ^ 2 * (1 - 6 * X + X ^ 2) * F1) -
          (4 * C (1 / 4)) * (1 - X) * s ^ 5 * F0 := by
          rw [h4]; dsimp only [s]; ring
      _ = 4 * (1 - X) * s * (4 * X * (1 - X) ^ 2 * F2 + s ^ 2 * (1 - 6 * X + X ^ 2) * F1 -
          C (1 / 4) * s ^ 4 * F0) := by ring
      _ = 4 * (1 - X) * s * 0 := by rw [hF_cleared]
      _ = 0 := mul_zero _
  have hdiff_ode : X * (1 - X ^ 2) * dPS (dPS (A - B)) + (1 - 3 * X ^ 2) * dPS (A - B) - X * (A - B) = 0 := by
    simp only [dPS_sub]
    linear_combination hA_ode - hB_ode
  have hdiff0 : coeff 0 (A - B) = 0 := by
    rw [map_sub]
    have hA0 : coeff 0 A = 1 := by
      dsimp only [A]; rw [coeff_zero_psComp]; unfold F_ps; rw [coeff_mk]; norm_num
    have hB0 : coeff 0 B = 1 := by
      dsimp only [B]; rw [coeff_zero_mul, coeff_zero_psInv h1pX0_ne, h1pX0, coeff_zero_psComp]
      unfold F_ps; rw [coeff_mk]; norm_num
    rw [hA0, hB0, sub_self]
  exact sub_eq_zero.mp (landen_ode_unique hdiff_ode hdiff0)

private lemma psComp_psInv {f g : PowerSeries ℚ} (hf : coeff 0 f ≠ 0) (hg : coeff 0 g = 0) :
    psComp (psInv f) g = psInv (psComp f g) := by
  have h0 : coeff 0 (psComp f g) ≠ 0 := by rwa [coeff_zero_psComp]
  have hne : psComp f g ≠ 0 := ps_ne_zero_of_coeff h0
  apply mul_left_cancel₀ hne
  rw [← psComp_mul f (psInv f) hg, mul_psInv hf, psComp_one, mul_psInv h0]

private lemma T3_sq_eq_F_lam : T3 ^ 2 = psComp F_ps lamPS := by
  have h1pX0 : coeff 0 (1 + X : PowerSeries ℚ) ≠ 0 := by
    rw [map_add, coeff_one, if_pos rfl, coeff_X, if_neg (by decide)]; norm_num
  have h1pX2 : coeff 0 ((1 + X : PowerSeries ℚ) ^ 2) ≠ 0 := by
    rw [coeff_zero_pow, map_add, coeff_one, if_pos rfl, coeff_X, if_neg (by decide)]; norm_num
  have hsub := congrArg (fun p => psComp p vPS) landen_id
  have hX2_0 : coeff 0 (X ^ 2 : PowerSeries ℚ) = 0 := by rw [coeff_X_pow]; norm_num
  have hw0 : coeff 0 (4 * X * psInv ((1 + X) ^ 2)) = 0 := by
    rw [coeff_zero_mul, coeff_zero_mul, coeff_X, if_neg (by decide), mul_zero, zero_mul]
  have hlhs : psComp (psComp F_ps (X ^ 2)) vPS = psSq (psComp F_ps lamPS) := by
    rw [psComp_comp F_ps hX2_0 coeff_zero_vPS, psComp_pow X coeff_zero_vPS 2,
      psComp_X coeff_zero_vPS, ← psSq_lamPS, ← psSq_psComp F_ps coeff_zero_lamPS]
  have hrhs : psComp (psInv (1 + X) * psComp F_ps (4 * X * psInv ((1 + X) ^ 2))) vPS =
      psInv (1 + vPS) * psComp F_ps lamPS := by
    rw [psComp_mul _ _ coeff_zero_vPS, psComp_psInv h1pX0 coeff_zero_vPS,
      psComp_add, psComp_one, psComp_X coeff_zero_vPS,
      psComp_comp F_ps hw0 coeff_zero_vPS,
      psComp_mul _ _ coeff_zero_vPS, psComp_mul _ _ coeff_zero_vPS,
      show (4 : PowerSeries ℚ) = C 4 by rfl, psComp_C, psComp_X coeff_zero_vPS,
      psComp_psInv h1pX2 coeff_zero_vPS, psComp_pow _ coeff_zero_vPS 2,
      psComp_add, psComp_one, psComp_X coeff_zero_vPS]
    rw [show C (4 : ℚ) = 4 by rfl, lamPS_from_vPS]
  rw [hlhs, hrhs] at hsub
  -- Multiply by (1 + vPS): (1 + vPS) * psSq (psComp F_ps lamPS) = psComp F_ps lamPS
  have hF_rec : (1 + vPS) * psSq (psComp F_ps lamPS) = psComp F_ps lamPS := by
    calc (1 + vPS) * psSq (psComp F_ps lamPS)
        = (1 + vPS) * (psInv (1 + vPS) * psComp F_ps lamPS) := by rw [hsub]
      _ = ((1 + vPS) * psInv (1 + vPS)) * psComp F_ps lamPS := by ring
      _ = 1 * psComp F_ps lamPS := by rw [mul_psInv (by rw [coeff_zero_one_add_vPS]; norm_num)]
      _ = psComp F_ps lamPS := one_mul _
  have hF0 : coeff 0 (psComp F_ps lamPS) = 1 := by
    rw [coeff_zero_psComp]; unfold F_ps; rw [coeff_mk]; norm_num
  have hF0_ne : coeff 0 (psComp F_ps lamPS) ≠ 0 := by rw [hF0]; norm_num
  set R : PowerSeries ℚ := T3 ^ 2 * psInv (psComp F_ps lamPS)
  have hR0 : coeff 0 R = 1 := by
    dsimp only [R]
    rw [coeff_zero_mul, coeff_zero_T3_pow, coeff_zero_psInv hF0_ne, hF0]
    norm_num
  have hR_psSq : psSq R = R := by
    have hne : (1 + vPS) * psSq (psComp F_ps lamPS) ≠ 0 := by
      rw [hF_rec]; exact ps_ne_zero_of_coeff hF0_ne
    apply mul_right_cancel₀ hne
    have hinv_ps : psSq (psComp F_ps lamPS) * psSq (psInv (psComp F_ps lamPS)) = 1 := by
      rw [← psSq_mul, mul_psInv hF0_ne, psSq_one]
    calc psSq R * ((1 + vPS) * psSq (psComp F_ps lamPS))
        = ((1 + vPS) * psSq (T3 ^ 2)) * (psSq (psComp F_ps lamPS) * psSq (psInv (psComp F_ps lamPS))) := by
          dsimp only [R]; rw [psSq_mul]; ring
      _ = T3 ^ 2 * 1 := by rw [T3_sq_psSq, hinv_ps]
      _ = T3 ^ 2 * (psComp F_ps lamPS * psInv (psComp F_ps lamPS)) := by rw [mul_psInv hF0_ne]
      _ = R * psComp F_ps lamPS := by dsimp only [R]; ring
      _ = R * ((1 + vPS) * psSq (psComp F_ps lamPS)) := by rw [hF_rec]
  have hR1 : R = 1 := eq_one_of_psSq_eq hR_psSq hR0
  calc T3 ^ 2 = T3 ^ 2 * (psInv (psComp F_ps lamPS) * psComp F_ps lamPS) := by
        rw [psInv_mul hF0_ne, mul_one]
    _ = R * psComp F_ps lamPS := by dsimp only [R]; ring
    _ = 1 * psComp F_ps lamPS := by rw [hR1]
    _ = psComp F_ps lamPS := one_mul _

private lemma clausen_ode_unique {U : PowerSeries ℚ}
    (hode : X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS U)) +
            3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS U) +
            (1 - 7 * X + 7 * X ^ 2) * dPS U - C (1 / 2) * (1 - 2 * X) * U = 0)
    (h0 : coeff 0 U = 0) : U = 0 := by
  have hrew : X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS U)) +
        3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS U) +
        (1 - 7 * X + 7 * X ^ 2) * dPS U - C (1 / 2) * (1 - 2 * X) * U =
      X ^ 2 * dPS (dPS (dPS U)) - C 2 * (X ^ 3 * dPS (dPS (dPS U))) + X ^ 4 * dPS (dPS (dPS U)) +
      C 3 * (X * dPS (dPS U)) - C 9 * (X ^ 2 * dPS (dPS U)) + C 6 * (X ^ 3 * dPS (dPS U)) +
      dPS U - C 7 * (X * dPS U) + C 7 * (X ^ 2 * dPS U) - C (1 / 2) * U + X * U := by
    have hc2 : C (2 : ℚ) = 2 := rfl
    have hc3 : C (3 : ℚ) = 3 := rfl
    have hc6 : C (6 : ℚ) = 6 := rfl
    have hc7 : C (7 : ℚ) = 7 := rfl
    have hc9 : C (9 : ℚ) = 9 := rfl
    have hhalf2 : C (1 / 2 : ℚ) * 2 = 1 := by rw [← hc2, ← map_mul]; norm_num
    rw [hc2, hc3, hc6, hc7, hc9]
    calc X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS U)) +
          3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS U) +
          (1 - 7 * X + 7 * X ^ 2) * dPS U - C (1 / 2) * (1 - 2 * X) * U
        = X ^ 2 * dPS (dPS (dPS U)) - 2 * (X ^ 3 * dPS (dPS (dPS U))) + X ^ 4 * dPS (dPS (dPS U)) +
          3 * (X * dPS (dPS U)) - 9 * (X ^ 2 * dPS (dPS U)) +
          6 * (X ^ 3 * dPS (dPS U)) +
          dPS U - 7 * (X * dPS U) + 7 * (X ^ 2 * dPS U) -
          C (1 / 2) * U + (C (1 / 2) * 2) * (X * U) := by ring
      _ = _ := by rw [hhalf2, one_mul]
  rw [hrew] at hode
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | m
    · exact h0
    · have hc := congrArg (coeff m) hode
      rw [map_zero, map_add, map_sub, map_add, map_sub, map_add, map_add, map_sub, map_add,
        map_add, map_sub,
        coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
        coeff_X_pow_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
        coeff_X_mul_eq, coeff_X_pow_mul_eq, coeff_X_pow_mul_eq,
        coeff_X_mul_eq, coeff_X_pow_mul_eq, coeff_X_mul_eq] at hc
      have hprev : ∀ k ≤ m, coeff k U = 0 := fun k hk => ih k (by omega)
      have ht3_2 : (if m < 2 then (0 : ℚ) else coeff (m - 2) (dPS (dPS (dPS U)))) =
          ((m : ℚ) * ((m : ℚ) - 1) * ((m + 1 : ℕ) : ℚ)) * coeff (m + 1) U := by
        rcases m with _ | _ | m'
        · simp
        · simp
        · simp only [show ¬ (m' + 2 < 2) by omega, if_false, show m' + 2 - 2 = m' by omega, coeff_dPS]
          push_cast; ring
      have ht3_3 : (if m < 3 then (0 : ℚ) else coeff (m - 3) (dPS (dPS (dPS U)))) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, coeff_dPS, coeff_dPS, hprev (m - 3 + 1 + 1 + 1) (by omega)]; ring
      have ht3_4 : (if m < 4 then (0 : ℚ) else coeff (m - 4) (dPS (dPS (dPS U)))) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, coeff_dPS, coeff_dPS, hprev (m - 4 + 1 + 1 + 1) (by omega)]; ring
      have ht2_1 : (if m = 0 then (0 : ℚ) else coeff (m - 1) (dPS (dPS U))) =
          ((m : ℚ) * ((m + 1 : ℕ) : ℚ)) * coeff (m + 1) U := by
        rcases m with _ | m'
        · simp
        · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel, coeff_dPS]
          push_cast; ring
      have ht2_2 : (if m < 2 then (0 : ℚ) else coeff (m - 2) (dPS (dPS U))) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, coeff_dPS, hprev (m - 2 + 1 + 1) (by omega)]; ring
      have ht2_3 : (if m < 3 then (0 : ℚ) else coeff (m - 3) (dPS (dPS U))) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, coeff_dPS, hprev (m - 3 + 1 + 1) (by omega)]; ring
      have ht1_1 : (if m = 0 then (0 : ℚ) else coeff (m - 1) (dPS U)) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, hprev (m - 1 + 1) (by omega)]; ring
      have ht1_2 : (if m < 2 then (0 : ℚ) else coeff (m - 2) (dPS U)) = 0 := by
        split_ifs with h
        · rfl
        · rw [coeff_dPS, hprev (m - 2 + 1) (by omega)]; ring
      have ht0_1 : (if m = 0 then (0 : ℚ) else coeff (m - 1) U) = 0 := by
        split_ifs with h
        · rfl
        · exact hprev (m - 1) (by omega)
      rw [ht3_2, ht3_3, ht3_4, ht2_1, ht2_2, ht2_3, ht1_1, ht1_2, ht0_1,
        hprev m (le_refl m), coeff_dPS] at hc
      have hfac : (((m + 1 : ℕ) : ℚ) ^ 3) * coeff (m + 1) U = 0 := by
        push_cast at hc ⊢; linarith [hc]
      have hm_ne : (((m + 1 : ℕ) : ℚ) ^ 3) ≠ 0 := pow_ne_zero 3 (by positivity)
      exact (mul_eq_zero.mp hfac).resolve_left hm_ne

private lemma clausen_id : F_ps ^ 2 = psComp H_ps (X * (1 - X) * C (1 / 16)) := by
  set U : PowerSeries ℚ := F_ps ^ 2
  set y : PowerSeries ℚ := X * (1 - X) * C (1 / 16)
  set V : PowerSeries ℚ := psComp H_ps y
  have hy0 : coeff 0 y = 0 := by
    dsimp only [y]; rw [coeff_zero_mul, coeff_zero_mul, coeff_X, if_neg (by decide), zero_mul, zero_mul]
  have hU_ode : X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS U)) +
      3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS U) +
      (1 - 7 * X + 7 * X ^ 2) * dPS U - C (1 / 2) * (1 - 2 * X) * U = 0 := by
    set F0 := F_ps
    set F1 := dPS F_ps
    set F2 := dPS (dPS F_ps)
    set F3 := dPS (dPS (dPS F_ps))
    have hLF : X * (1 - X) * F2 + (1 - 2 * X) * F1 - C (1 / 4) * F0 = 0 := F_ode
    have hLF1 : X * (1 - X) * F3 + 2 * (1 - 2 * X) * F2 - C (9 / 4) * F1 = 0 := by
      have hd := congrArg dPS hLF
      have hd2 : dPS (2 : PowerSeries ℚ) = 0 := by rw [show (2 : PowerSeries ℚ) = C 2 by rfl, dPS_C]
      simp only [dPS_zero, dPS_sub, dPS_add, dPS_mul, dPS_one, dPS_X, dPS_C, hd2] at hd
      have h94 : C (9 / 4 : ℚ) = 2 + C (1 / 4) := by
        rw [show (2 : PowerSeries ℚ) = C 2 by rfl, ← map_add]; norm_num
      rw [h94]
      dsimp only [F0, F1, F2, F3] at hd ⊢
      linear_combination hd
    have hdU : dPS U = 2 * F0 * F1 := by
      dsimp only [U, F0, F1]; rw [dPS_pow]; simp
    have hddU : dPS (dPS U) = 2 * F1 ^ 2 + 2 * F0 * F2 := by
      rw [hdU, dPS_mul, dPS_mul, show (2 : PowerSeries ℚ) = C 2 by rfl, dPS_C, zero_mul, zero_add]
      rw [show C (2 : ℚ) = 2 by rfl]
      dsimp only [F0, F1, F2]; ring
    have hdddU : dPS (dPS (dPS U)) = 6 * F1 * F2 + 2 * F0 * F3 := by
      rw [hddU, dPS_add, dPS_mul, dPS_mul, dPS_mul, show (2 : PowerSeries ℚ) = C 2 by rfl, dPS_C,
        dPS_pow]
      rw [show C (2 : ℚ) = 2 by rfl]
      simp only [zero_mul, zero_add, Nat.cast_ofNat, show 2 - 1 = 1 by rfl, pow_one]
      dsimp only [F0, F1, F2, F3]; ring
    have h12 : C (1 / 2 : ℚ) = 2 * C (1 / 4) := by
      rw [show (2 : PowerSeries ℚ) = C 2 by rfl, ← map_mul]; norm_num
    have h92 : (2 : PowerSeries ℚ) * C (9 / 4) = C (9 / 2) := by
      rw [show (2 : PowerSeries ℚ) = C 2 by rfl, ← map_mul]; norm_num
    have h64 : (6 : PowerSeries ℚ) * C (1 / 4) = C (3 / 2) := by
      rw [show (6 : PowerSeries ℚ) = C 6 by rfl, ← map_mul]; norm_num
    have hcomb : C (9 / 2 : ℚ) + C (3 / 2) = 6 := by
      rw [← map_add]; norm_num; rfl
    rw [hdddU, hddU, hdU]
    calc X ^ 2 * (1 - X) ^ 2 * (6 * F1 * F2 + 2 * F0 * F3) +
          3 * X * (1 - X) * (1 - 2 * X) * (2 * F1 ^ 2 + 2 * F0 * F2) +
          (1 - 7 * X + 7 * X ^ 2) * (2 * F0 * F1) - C (1 / 2) * (1 - 2 * X) * F0 ^ 2
        = 2 * X * (1 - X) * F0 * (X * (1 - X) * F3 + 2 * (1 - 2 * X) * F2 - C (9 / 4) * F1) +
          2 * (1 - 2 * X) * F0 * (X * (1 - X) * F2 + (1 - 2 * X) * F1 - C (1 / 4) * F0) +
          6 * X * (1 - X) * F1 * (X * (1 - X) * F2 + (1 - 2 * X) * F1 - C (1 / 4) * F0) +
          ((2 * C (9 / 4) + 6 * C (1 / 4)) - 6) * X * (1 - X) * F0 * F1 +
          (2 * C (1 / 4) - C (1 / 2)) * (1 - 2 * X) * F0 ^ 2 := by ring
      _ = 2 * X * (1 - X) * F0 * 0 + 2 * (1 - 2 * X) * F0 * 0 + 6 * X * (1 - X) * F1 * 0 +
          0 * X * (1 - X) * F0 * F1 + 0 * (1 - 2 * X) * F0 ^ 2 := by
          rw [hLF1, hLF, h92, h64, hcomb, sub_self, ← h12, sub_self]
      _ = 0 := by ring
  have hV_ode : X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS V)) +
      3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS V) +
      (1 - 7 * X + 7 * X ^ 2) * dPS V - C (1 / 2) * (1 - 2 * X) * V = 0 := by
    set H0 := psComp H_ps y
    set H1 := psComp (dPS H_ps) y
    set H2 := psComp (dPS (dPS H_ps)) y
    set H3 := psComp (dPS (dPS (dPS H_ps))) y
    have hdy : dPS y = (1 - 2 * X) * C (1 / 16) := by
      dsimp only [y]
      rw [dPS_mul, dPS_mul, dPS_C, mul_zero, add_zero, dPS_sub, dPS_one, dPS_X, zero_sub]
      ring
    have hddy : dPS (dPS y) = C (-1 / 8) := by
      rw [hdy, dPS_mul, dPS_C, mul_zero, add_zero, dPS_sub, dPS_one,
        show (2 : PowerSeries ℚ) = C 2 by rfl, dPS_C_mul, dPS_X, mul_one, zero_sub,
        ← map_neg, ← map_mul]
      norm_num
    have hdV : dPS V = H1 * dPS y := dPS_psComp H_ps hy0
    have hddV : dPS (dPS V) = H2 * (dPS y) ^ 2 + H1 * dPS (dPS y) := by
      rw [hdV, dPS_mul, dPS_psComp (dPS H_ps) hy0]; ring
    have hdddV : dPS (dPS (dPS V)) = H3 * (dPS y) ^ 3 + 3 * H2 * dPS y * dPS (dPS y) := by
      have hd_ddy : dPS (dPS (dPS y)) = 0 := by rw [hddy, dPS_C]
      have hdH2 : dPS H2 = H3 * dPS y := dPS_psComp (dPS (dPS H_ps)) hy0
      have hdH1 : dPS H1 = H2 * dPS y := dPS_psComp (dPS H_ps) hy0
      have hgen : ∀ (a1 a2 a3 u : PowerSeries ℚ),
          dPS a1 = a2 * dPS u → dPS a2 = a3 * dPS u → dPS (dPS (dPS u)) = 0 →
          dPS (a2 * (dPS u) ^ 2 + a1 * dPS (dPS u)) = a3 * (dPS u) ^ 3 + 3 * a2 * dPS u * dPS (dPS u) := by
        intro a1 a2 a3 u h1 h2 h3
        rw [dPS_add, dPS_mul, dPS_mul, dPS_pow, h1, h2, h3]
        simp only [Nat.cast_ofNat, show 2 - 1 = 1 by rfl, pow_one, mul_zero, add_zero]
        ring
      rw [hddV]
      exact hgen H1 H2 H3 y hdH1 hdH2 hd_ddy
    have hH_at : y ^ 2 * (1 - 64 * y) * H3 + 3 * y * (1 - 96 * y) * H2 + (1 - 208 * y) * H1 - 8 * H0 = 0 := by
      have h := congrArg (fun p => psComp p y) H_ode
      simp only [psComp_zero, psComp_sub, psComp_add, psComp_mul _ _ hy0, psComp_pow _ hy0,
        psComp_one, psComp_X hy0,
        show (3 : PowerSeries ℚ) = C 3 by rfl, show (8 : PowerSeries ℚ) = C 8 by rfl,
        show (64 : PowerSeries ℚ) = C 64 by rfl, show (96 : PowerSeries ℚ) = C 96 by rfl,
        show (208 : PowerSeries ℚ) = C 208 by rfl, psComp_C] at h
      simpa only [H0, H1, H2, H3, show C (3 : ℚ) = 3 by rfl, show C (8 : ℚ) = 8 by rfl,
        show C (64 : ℚ) = 64 by rfl, show C (96 : ℚ) = 96 by rfl,
        show C (208 : ℚ) = 208 by rfl] using h
    -- Clear factor 16^4 = 65536 so everything is pure ring with C (1/16) = a!
    set a : PowerSeries ℚ := C (1 / 16)
    have ha16 : (16 : PowerSeries ℚ) * a = 1 := by
      dsimp only [a]; rw [show (16 : PowerSeries ℚ) = C 16 by rfl, ← map_mul]; norm_num
    have hne : (16 : PowerSeries ℚ) ^ 4 ≠ 0 := by
      apply ps_ne_zero_of_coeff (n := 0)
      rw [coeff_zero_pow, show (16 : PowerSeries ℚ) = C 16 by rfl, coeff_C, if_pos rfl]; norm_num
    have hy_eq : 16 * y = X * (1 - X) := by
      dsimp only [y]; calc 16 * (X * (1 - X) * a) = X * (1 - X) * (16 * a) := by ring
        _ = X * (1 - X) * 1 := by rw [ha16]
        _ = X * (1 - X) := mul_one _
    have hdy_eq : 16 * dPS y = 1 - 2 * X := by
      rw [hdy]; calc 16 * ((1 - 2 * X) * a) = (1 - 2 * X) * (16 * a) := by ring
        _ = (1 - 2 * X) * 1 := by rw [ha16]
        _ = 1 - 2 * X := mul_one _
    have hddy_eq : 16 * dPS (dPS y) = -2 := by
      rw [hddy, show (16 : PowerSeries ℚ) = C 16 by rfl, ← map_mul]; norm_num; rfl
    have h12_16 : (16 : PowerSeries ℚ) * C (1 / 2) = 8 := by
      rw [show (16 : PowerSeries ℚ) = C 16 by rfl, ← map_mul]; norm_num; rfl
    apply mul_left_cancel₀ hne
    rw [mul_zero]
    have hLHS : 16 ^ 4 * (X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS V)) +
          3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS V) +
          (1 - 7 * X + 7 * X ^ 2) * dPS V - C (1 / 2) * (1 - 2 * X) * V) =
        (1 - 2 * X) * (16 ^ 3 * (y ^ 2 * (1 - 64 * y) * H3 +
          3 * y * (1 - 96 * y) * H2 + (1 - 208 * y) * H1 - 8 * H0)) := by
      rw [hdddV, hddV, hdV]
      have hV0 : V = H0 := rfl
      rw [hV0]
      calc 16 ^ 4 * (X ^ 2 * (1 - X) ^ 2 * (H3 * (dPS y) ^ 3 + 3 * H2 * dPS y * dPS (dPS y)) +
            3 * X * (1 - X) * (1 - 2 * X) * (H2 * (dPS y) ^ 2 + H1 * dPS (dPS y)) +
            (1 - 7 * X + 7 * X ^ 2) * (H1 * dPS y) - C (1 / 2) * (1 - 2 * X) * H0)
          = 16 * X ^ 2 * (1 - X) ^ 2 * (16 * dPS y) ^ 3 * H3 +
            (48 * 16 * X ^ 2 * (1 - X) ^ 2 * (16 * dPS y) * (16 * dPS (dPS y)) +
             3 * 16 ^ 2 * X * (1 - X) * (1 - 2 * X) * (16 * dPS y) ^ 2) * H2 +
            (3 * 16 ^ 3 * X * (1 - X) * (1 - 2 * X) * (16 * dPS (dPS y)) +
             16 ^ 3 * (1 - 7 * X + 7 * X ^ 2) * (16 * dPS y)) * H1 -
            16 ^ 3 * (16 * C (1 / 2)) * (1 - 2 * X) * H0 := by ring
        _ = 16 * X ^ 2 * (1 - X) ^ 2 * (1 - 2 * X) ^ 3 * H3 +
            (48 * 16 * X ^ 2 * (1 - X) ^ 2 * (1 - 2 * X) * (-2) +
             3 * 16 ^ 2 * X * (1 - X) * (1 - 2 * X) * (1 - 2 * X) ^ 2) * H2 +
            (3 * 16 ^ 3 * X * (1 - X) * (1 - 2 * X) * (-2) +
             16 ^ 3 * (1 - 7 * X + 7 * X ^ 2) * (1 - 2 * X)) * H1 -
            16 ^ 3 * 8 * (1 - 2 * X) * H0 := by rw [hdy_eq, hddy_eq, h12_16]
        _ = (1 - 2 * X) * (16 * (X * (1 - X)) ^ 2 * (1 - 4 * (X * (1 - X))) * H3 +
            3 * 16 ^ 2 * (X * (1 - X)) * (1 - 6 * (X * (1 - X))) * H2 +
            16 ^ 3 * (1 - 13 * (X * (1 - X))) * H1 - 8 * 16 ^ 3 * H0) := by ring
        _ = (1 - 2 * X) * (16 * (16 * y) ^ 2 * (1 - 4 * (16 * y)) * H3 +
            3 * 16 ^ 2 * (16 * y) * (1 - 6 * (16 * y)) * H2 +
            16 ^ 3 * (1 - 13 * (16 * y)) * H1 - 8 * 16 ^ 3 * H0) := by rw [← hy_eq]
        _ = (1 - 2 * X) * (16 ^ 3 * (y ^ 2 * (1 - 64 * y) * H3 +
            3 * y * (1 - 96 * y) * H2 + (1 - 208 * y) * H1 - 8 * H0)) := by ring
    rw [hLHS, hH_at]; ring
  have hdiff_ode : X ^ 2 * (1 - X) ^ 2 * dPS (dPS (dPS (U - V))) +
      3 * X * (1 - X) * (1 - 2 * X) * dPS (dPS (U - V)) +
      (1 - 7 * X + 7 * X ^ 2) * dPS (U - V) - C (1 / 2) * (1 - 2 * X) * (U - V) = 0 := by
    rw [dPS_sub, dPS_sub, dPS_sub]
    linear_combination hU_ode - hV_ode
  have hdiff0 : coeff 0 (U - V) = 0 := by
    rw [map_sub]
    have hU0 : coeff 0 U = 1 := by
      dsimp only [U]; rw [coeff_zero_pow]; unfold F_ps; rw [coeff_mk]; norm_num
    have hV0 : coeff 0 V = 1 := by
      dsimp only [V]; rw [coeff_zero_psComp]; unfold H_ps; rw [coeff_mk]; norm_num
    rw [hU0, hV0, sub_self]
  exact sub_eq_zero.mp (clausen_ode_unique hdiff_ode hdiff0)

private lemma T3_pow4_eq_H_yPS : T3 ^ 4 = psComp H_ps yPS := by
  have hy_comp : psComp (X * (1 - X) * C (1 / 16)) lamPS = yPS := by
    unfold yPS
    rw [psComp_mul _ _ coeff_zero_lamPS, psComp_mul _ _ coeff_zero_lamPS,
      psComp_sub, psComp_one, psComp_C, psComp_X coeff_zero_lamPS]
  have hy0 : coeff 0 (X * ((1 : PowerSeries ℚ) - X) * C (1 / 16)) = 0 := by
    rw [coeff_zero_mul, coeff_zero_mul, coeff_X, if_neg (by decide), zero_mul, zero_mul]
  calc T3 ^ 4 = (T3 ^ 2) ^ 2 := by ring
    _ = (psComp F_ps lamPS) ^ 2 := by rw [T3_sq_eq_F_lam]
    _ = psComp (F_ps ^ 2) lamPS := (psComp_pow F_ps coeff_zero_lamPS 2).symm
    _ = psComp (psComp H_ps (X * (1 - X) * C (1 / 16))) lamPS := by rw [clausen_id]
    _ = psComp H_ps (psComp (X * (1 - X) * C (1 / 16)) lamPS) := psComp_comp H_ps hy0 coeff_zero_lamPS
    _ = psComp H_ps yPS := by rw [hy_comp]

private lemma c_recurrence : ∀ k : ℕ, 1 ≤ k →
    ∑ j ∈ Finset.range (k + 1), gCoeff j * OMA.S_oeis_a023688.c (k - j) = 0 := by
  set G_ps : PowerSeries ℚ := PowerSeries.mk (fun n => (gCoeff n : ℚ))
  have hG_eq : G_ps = PowerSeries.mk (fun n => (sqCoeff n : ℚ)) * H_ps := by
    ext n
    dsimp only [G_ps]
    rw [coeff_mk, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (PowerSeries.mk (fun n => (sqCoeff n : ℚ))) * coeff j H_ps)]
    unfold gCoeff hCoeff H_ps
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    simp only [coeff_mk]
  have hDE : X * dPS yPS = yPS * psComp G_ps yPS := by
    calc X * dPS yPS = yPS * (1 - 2 * lamPS) * T3 ^ 4 := X_dPS_yPS
      _ = yPS * (psComp (PowerSeries.mk (fun n => (sqCoeff n : ℚ))) yPS * psComp H_ps yPS) := by
          rw [psComp_sq_yPS, T3_pow4_eq_H_yPS]; ring
      _ = yPS * psComp (PowerSeries.mk (fun n => (sqCoeff n : ℚ)) * H_ps) yPS := by
          rw [psComp_mul _ _ coeff_zero_yPS]
      _ = yPS * psComp G_ps yPS := by rw [← hG_eq]
  have hQ0 : coeff 0 (P_odd ^ 24) = 1 := by
    rw [coeff_zero_pow]; unfold P_odd; rw [coeff_zero_infProd, one_pow]
  have hrecQ := lagrange_recurrence hQ0 Q_mul_yPS hDE
  intro k hk
  have hq := hrecQ k hk
  have hcast : ((∑ j ∈ Finset.range (k + 1), gCoeff j * OMA.S_oeis_a023688.c (k - j) : ℤ) : ℚ) = 0 := by
    push_cast
    rw [← hq]
    apply Finset.sum_congr rfl
    intro j _
    rw [c_eq_coeff_Q_pow (k - j)]
    dsimp only [G_ps]; rw [coeff_mk]
  exact_mod_cast hcast

private lemma main_proof : ∀ k : ℕ, 1 ≤ k →
    padicValInt 2 (OMA.S_oeis_a023688.A005148 k) = 3 * (OMA.S_oeis_a023688.s2 k - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc0 : OMA.S_oeis_a023688.c 0 = 1 := by
    unfold OMA.S_oeis_a023688.c; simp
  have hval := inv_val_exact OMA.S_oeis_a023688.c hc0 c_recurrence
  intro k hk
  have hck := hval k
  have hd24 := dvd_24_c hk
  have hA_mul : 24 * OMA.S_oeis_a023688.A005148 k = OMA.S_oeis_a023688.c k :=
    Int.mul_ediv_cancel' hd24
  have hs_pos : 1 ≤ s2 k := s2_pos hk
  have hexp : 3 * s2 k = 3 + 3 * (s2 k - 1) := by omega
  have hA_dvd : (2 : ℤ) ^ (3 * (s2 k - 1)) ∣ OMA.S_oeis_a023688.A005148 k := by
    obtain ⟨u, hu⟩ := hck.1
    rw [hexp, pow_add] at hu
    have h8 : (2 : ℤ) ^ 3 = 8 := by norm_num
    rw [h8] at hu
    have h3A : 3 * OMA.S_oeis_a023688.A005148 k = (2 : ℤ) ^ (3 * (s2 k - 1)) * u := by linarith
    have hcop : IsCoprime ((2 : ℤ) ^ (3 * (s2 k - 1))) (3 : ℤ) := by
      have h23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
      exact h23.pow_left
    have hd : (2 : ℤ) ^ (3 * (s2 k - 1)) ∣ 3 * OMA.S_oeis_a023688.A005148 k := ⟨u, h3A⟩
    exact hcop.dvd_of_dvd_mul_left hd
  have hA_ndvd : ¬ ((2 : ℤ) ^ (3 * (s2 k - 1) + 1) ∣ OMA.S_oeis_a023688.A005148 k) := by
    intro ⟨w, hw⟩
    apply hck.2
    refine ⟨3 * w, ?_⟩
    have hexp1 : 3 * s2 k + 1 = 3 + (3 * (s2 k - 1) + 1) := by omega
    rw [← hA_mul, hw, hexp1, pow_add]
    ring
  have hA_ne : OMA.S_oeis_a023688.A005148 k ≠ 0 := by
    intro hz; apply hA_ndvd; rw [hz]; exact dvd_zero _
  -- Convert exact 2-adic divisibility on ℤ to padicValInt 2
  unfold padicValInt
  have hnat_ne : (OMA.S_oeis_a023688.A005148 k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA_ne
  have hd_nat : 2 ^ (3 * (s2 k - 1)) ∣ (OMA.S_oeis_a023688.A005148 k).natAbs := by
    rw [← Int.natCast_dvd]
    simpa using hA_dvd
  have hnd_nat : ¬ (2 ^ (3 * (s2 k - 1) + 1) ∣ (OMA.S_oeis_a023688.A005148 k).natAbs) := by
    intro h
    apply hA_ndvd
    rw [← Int.natCast_dvd] at h
    simpa using h
  have hle1 : 3 * (s2 k - 1) ≤ padicValNat 2 (OMA.S_oeis_a023688.A005148 k).natAbs :=
    (padicValNat_dvd_iff_le hnat_ne).mp hd_nat
  have hlt2 : ¬ (3 * (s2 k - 1) + 1 ≤ padicValNat 2 (OMA.S_oeis_a023688.A005148 k).natAbs) := by
    intro h; exact hnd_nat ((padicValNat_dvd_iff_le hnat_ne).mpr h)
  change padicValNat 2 (OMA.S_oeis_a023688.A005148 k).natAbs = 3 * (s2 k - 1)
  omega

end Proof_oeis_a023688

theorem OMA.solution : type_of% @OMA.S_oeis_a023688.main :=
  Proof_oeis_a023688.main_proof
end

