import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1
import Mathlib

/-!
# Primitive divisors for powers of a positive Pell unit

Write Xₘ + Yₘ√D for the m-th power of a positive Pell solution. The addition
laws give strong divisibility of Yₘ and exact lifting at every prime that
divides Yₘ. If every prime of Yₙ appeared earlier, the positive Möbius
product would divide n times the negative one. The ratio of the products
is at least 3 ^ φ(n), which exceeds n for every n ≥ 2.

The divisibility argument adapts Andyi955's proof for the ordinary Pell
numbers (OEIS A247250, open-math-agents PR #11600). Here the
radicand and the initial coordinates vary. A prime can already divide Y₁.
-/

namespace Erdos649Pell

open Finset
open scoped Classical

private abbrev PellUnit (D : ℕ) :=
  {u : Pell.Solution₁ (D : ℤ) // 1 < u.x ∧ 0 < u.y}

variable {D : ℕ} (u : PellUnit D)

private def xCoord (n : ℕ) : ℕ := (u.val ^ n).x.natAbs
private def yCoord (n : ℕ) : ℕ := (u.val ^ n).y.natAbs

private lemma x_cast (n : ℕ) : (xCoord u n : ℤ) = (u.val ^ n).x := by
  exact Int.natAbs_of_nonneg (Pell.Solution₁.x_pow_pos (zero_lt_one.trans u.property.1) n).le

private lemma y_cast (n : ℕ) : (yCoord u n : ℤ) = (u.val ^ n).y := by
  apply Int.natAbs_of_nonneg
  cases n with
  | zero => simp
  | succ n => exact (Pell.Solution₁.y_pow_succ_pos (zero_lt_one.trans u.property.1) u.property.2 n).le

private lemma y_pos {n : ℕ} (hn : 0 < n) : 0 < yCoord u n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact Int.natAbs_pos.mpr (Pell.Solution₁.y_pow_succ_pos
    (zero_lt_one.trans u.property.1) u.property.2 m).ne'

private lemma y_ne_zero {n : ℕ} (hn : 0 < n) : yCoord u n ≠ 0 := (y_pos u hn).ne'

private lemma coords_add (m n : ℕ) :
    yCoord u (m + n) = yCoord u m * xCoord u n + xCoord u m * yCoord u n ∧
    xCoord u (m + n) = xCoord u m * xCoord u n + D * yCoord u m * yCoord u n := by
  constructor
  · exact_mod_cast (show (yCoord u (m + n) : ℤ) =
        (yCoord u m : ℤ) * xCoord u n + (xCoord u m : ℤ) * yCoord u n by
      simp only [x_cast, y_cast, pow_add, Pell.Solution₁.y_mul, add_comm])
  · exact_mod_cast (show (xCoord u (m + n) : ℤ) =
        (xCoord u m : ℤ) * xCoord u n + (D : ℤ) * yCoord u m * yCoord u n by
      simp only [x_cast, y_cast, pow_add, Pell.Solution₁.x_mul, mul_assoc])

private lemma coords_coprime (n : ℕ) : Nat.Coprime (yCoord u n) (xCoord u n) := by
  let g := Nat.gcd (yCoord u n) (xCoord u n)
  have gy : (g : ℤ) ∣ (u.val ^ n).y := y_cast u n ▸ Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
  have gx : (g : ℤ) ∣ (u.val ^ n).x := x_cast u n ▸ Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
  have h : (g : ℤ) ∣ 1 := (u.val ^ n).prop ▸
    dvd_sub (dvd_pow gx (by decide : 2 ≠ 0))
      (dvd_mul_of_dvd_right (dvd_pow gy (by decide : 2 ≠ 0)) (D : ℤ))
  exact Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp h)

private lemma y_add_gcd (m n : ℕ) :
    Nat.gcd (yCoord u (m + n)) (yCoord u m) = Nat.gcd (yCoord u n) (yCoord u m) := by
  rw [(coords_add u m n).1]
  have h1 : Nat.gcd (yCoord u m * xCoord u n + xCoord u m * yCoord u n) (yCoord u m) =
      Nat.gcd (xCoord u m * yCoord u n) (yCoord u m) := by
    rw [Nat.add_comm, Nat.mul_comm (yCoord u m) (xCoord u n)]
    exact Nat.gcd_add_mul_right_left (yCoord u m) (xCoord u m * yCoord u n) (xCoord u n)
  rw [h1]
  exact (coords_coprime u m).symm.gcd_mul_left_cancel (yCoord u n)

private lemma y_gcd (m n : ℕ) :
    Nat.gcd (yCoord u m) (yCoord u n) = yCoord u (Nat.gcd m n) := by
  induction h : m + n using Nat.strong_induction_on generalizing m n with
  | h s ih =>
    rcases m with _ | m
    · simp [yCoord]
    rcases n with _ | n
    · simp [yCoord]
    rcases le_total (m + 1) (n + 1) with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, Nat.gcd_comm, y_add_gcd u, Nat.gcd_comm,
        Nat.gcd_comm (m + 1) (m + 1 + k), Nat.add_comm (m + 1) k,
        Nat.gcd_add_self_left, Nat.gcd_comm]
      exact ih (k + (m + 1)) (by omega) k (m + 1) rfl
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, y_add_gcd u, Nat.add_comm (n + 1) k, Nat.gcd_add_self_left]
      exact ih (k + (n + 1)) (by omega) k (n + 1) rfl

private lemma y_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : yCoord u m ∣ yCoord u n := by
  have hg : Nat.gcd m n = m := Nat.gcd_eq_left h
  have h1 : Nat.gcd (yCoord u m) (yCoord u n) = yCoord u m := by rw [y_gcd u, hg]
  rw [← h1]
  exact Nat.gcd_dvd_right _ _

/-- Lifting the exponent via a linear recurrence modulo `(yCoord u m)^2`. -/
private lemma y_mul_quot_mod (m k : ℕ) :
    ∃ a : ℕ, yCoord u (k * m) = yCoord u m * a ∧
      (k = 0 → a = 0) ∧
      (0 < k → a ≡ k * (xCoord u m) ^ (k - 1) [MOD (yCoord u m) ^ 2]) ∧
      xCoord u (k * m) ≡ (xCoord u m) ^ k [MOD (yCoord u m) ^ 2] := by
  induction k with
  | zero =>
    refine ⟨0, by simp [yCoord], fun _ => rfl, fun h => (Nat.lt_irrefl 0 h).elim, ?_⟩
    simpa [xCoord] using Nat.ModEq.rfl
  | succ k ih =>
    obtain ⟨a, ha_eq, ha0, ha_mod, hH_mod⟩ := ih
    refine ⟨a * xCoord u m + xCoord u (k * m), ?_, by omega, ?_, ?_⟩
    · rw [Nat.succ_mul, (coords_add u (k * m) m).1, ha_eq]
      ring
    · intro _
      rcases k with _ | k
      · simpa [ha0 rfl, xCoord] using Nat.ModEq.rfl
      · have hkpos : 0 < k + 1 := Nat.succ_pos k
        have h1 : a * xCoord u m ≡ ((k + 1) * xCoord u m ^ k) * xCoord u m [MOD (yCoord u m) ^ 2] :=
          (ha_mod hkpos).mul_right (xCoord u m)
        have h2 : a * xCoord u m + xCoord u ((k + 1) * m) ≡
            (k + 1) * xCoord u m ^ k * xCoord u m + xCoord u m ^ (k + 1) [MOD (yCoord u m) ^ 2] :=
          h1.add hH_mod
        have h3 : (k + 1) * xCoord u m ^ k * xCoord u m + xCoord u m ^ (k + 1) =
            (k + 2) * xCoord u m ^ (k + 1) := by ring
        simpa only [Nat.add_sub_cancel, h3] using h2
    · rw [Nat.succ_mul, (coords_add u (k * m) m).2, ha_eq]
      have h1 : xCoord u (k * m) * xCoord u m ≡ xCoord u m ^ k * xCoord u m [MOD (yCoord u m) ^ 2] :=
        hH_mod.mul_right (xCoord u m)
      have h2 : D * (yCoord u m * a) * yCoord u m = (yCoord u m) ^ 2 * (D * a) := by ring
      rw [h2, pow_succ]
      have h3 : xCoord u (k * m) * xCoord u m + yCoord u m ^ 2 * (D * a) ≡ xCoord u (k * m) * xCoord u m [MOD (yCoord u m) ^ 2] := by
        rw [Nat.ModEq, Nat.add_mul_mod_self_left]
      exact h3.trans h1

private lemma prime_not_dvd_x {p m : ℕ} (hp : p.Prime) (hpy : p ∣ yCoord u m) : ¬ p ∣ xCoord u m := by
  intro hpx
  have hd := Nat.dvd_gcd hpy hpx
  rw [(coords_coprime u m).gcd_eq_one] at hd
  exact hp.not_dvd_one hd

private lemma valuation_mul_coprime {p m k : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ yCoord u m) (hk : 0 < k) (hpk : ¬ p ∣ k) :
    (yCoord u (k * m)).factorization p = (yCoord u m).factorization p := by
  obtain ⟨a, ha_eq, _, ha_mod, _⟩ := y_mul_quot_mod u m k
  have hp2 : p ^ 2 ∣ (yCoord u m) ^ 2 := pow_dvd_pow_of_dvd hpm 2
  have ha_mod_p : a ≡ k * (xCoord u m) ^ (k - 1) [MOD p] :=
    (ha_mod hk).of_dvd ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hp2)
  have hpa : ¬ p ∣ a := by
    intro hd
    have hd2 : p ∣ k * (xCoord u m) ^ (k - 1) := (Nat.ModEq.dvd_iff ha_mod_p dvd_rfl).mp hd
    rcases hp.dvd_mul.mp hd2 with hk' | hH'
    · exact hpk hk'
    · exact prime_not_dvd_x u hp hpm (hp.dvd_of_dvd_pow hH')
  have ha_ne : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
  rw [ha_eq, Nat.factorization_mul (y_ne_zero u hm) ha_ne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpa, add_zero]

private lemma valuation_mul_prime {p m : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ yCoord u m) :
    (yCoord u (p * m)).factorization p = (yCoord u m).factorization p + 1 := by
  obtain ⟨a, ha_eq, _, ha_mod, _⟩ := y_mul_quot_mod u m p
  have hp2 : p ^ 2 ∣ (yCoord u m) ^ 2 := pow_dvd_pow_of_dvd hpm 2
  have ha_mod_p2 : a ≡ p * (xCoord u m) ^ (p - 1) [MOD p ^ 2] :=
    (ha_mod hp.pos).of_dvd hp2
  have hpa : p ∣ a := by
    have h1 : p ∣ p * (xCoord u m) ^ (p - 1) := dvd_mul_right p _
    exact (Nat.ModEq.dvd_iff (ha_mod_p2.of_dvd (dvd_pow_self p (by decide : 2 ≠ 0))) dvd_rfl).mpr h1
  have hp2a : ¬ p ^ 2 ∣ a := by
    intro hd
    have hd2 : p ^ 2 ∣ p * (xCoord u m) ^ (p - 1) := (Nat.ModEq.dvd_iff ha_mod_p2 dvd_rfl).mp hd
    rw [sq] at hd2
    have hH1 : p ∣ (xCoord u m) ^ (p - 1) := (Nat.mul_dvd_mul_iff_left hp.pos).mp hd2
    exact prime_not_dvd_x u hp hpm (hp.dvd_of_dvd_pow hH1)
  have ha_ne : a ≠ 0 := by rintro rfl; exact hp2a (dvd_zero _)
  have hva : a.factorization p = 1 := by
    have hge : 1 ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization ha_ne).mp (by simpa using hpa)
    have hlt : ¬ 2 ≤ a.factorization p := fun h => hp2a ((hp.pow_dvd_iff_le_factorization ha_ne).mpr h)
    omega
  rw [ha_eq, Nat.factorization_mul (y_ne_zero u hm) ha_ne, Finsupp.add_apply, hva]

private lemma valuation_mul {p m k : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ yCoord u m) (hk : 0 < k) :
    (yCoord u (k * m)).factorization p = (yCoord u m).factorization p + k.factorization p := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hpk : p ∣ k
    · obtain ⟨k', rfl⟩ := hpk
      have hk' : 0 < k' := Nat.pos_of_mul_pos_left hk
      have hlt : k' < p * k' := lt_mul_of_one_lt_left hk' hp.one_lt
      have hpm' : p ∣ yCoord u (k' * m) := hpm.trans (y_dvd_of_dvd u (dvd_mul_left m k'))
      rw [show p * k' * m = p * (k' * m) by ring]
      rw [valuation_mul_prime u hp (Nat.mul_pos hk' hm) hpm']
      rw [ih k' hlt hk']
      rw [Nat.factorization_mul hp.ne_zero hk'.ne', Finsupp.add_apply, hp.factorization_self]
      omega
    · rw [valuation_mul_coprime u hp hm hpm hk hpk,
        Nat.factorization_eq_zero_of_not_dvd hpk, add_zero]

private lemma moebius_cases (k : ℕ) :
    ArithmeticFunction.moebius k = 0 ∨
    ArithmeticFunction.moebius k = 1 ∨
    ArithmeticFunction.moebius k = -1 := by
  by_cases hsq : Squarefree k
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    exact Or.inr (neg_one_pow_eq_or ℤ _)
  · exact Or.inl (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq)

private lemma invert_sum (f g : ℕ → ℤ)
    (h : ∀ m > 0, ∑ d ∈ m.divisors, f d = g m) (t : ℕ) (ht : 0 < t) :
    ∑ e ∈ t.divisors, ArithmeticFunction.moebius (t / e) * g e = f t := by
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp h t ht
  simpa only [Int.cast_id, Nat.sum_divisorsAntidiagonal'
    (fun i j => ArithmeticFunction.moebius i * g j)] using hi

/-- Count the divisors of r * m of the form r * p ^ a for positive exponents a. -/
private lemma count_rank_powers {r m p : ℕ} (hr : 0 < r) (hm : 0 < m) (hp : p.Prime) :
    (∑ d ∈ (r * m).divisors, if ∃ a > 0, d = r * p ^ a then (1 : ℤ) else 0) =
      (m.factorization p : ℤ) := by
  have inj : Function.Injective (fun a : ℕ => r * p ^ a) :=
    fun _ _ h => Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_left hr h)
  have powers : (r * m).divisors.filter (fun d => ∃ a > 0, d = r * p ^ a) =
      (Finset.Icc 1 (m.factorization p)).image (fun a => r * p ^ a) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, a, ha, rfl⟩
      exact ⟨a, ⟨ha, (hp.pow_dvd_iff_le_factorization hm.ne').mp
        ((Nat.mul_dvd_mul_iff_left hr).mp hd)⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hd⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left r ((hp.pow_dvd_iff_le_factorization hm.ne').mpr hd),
        (Nat.mul_pos hr hm).ne'⟩, a, ha, rfl⟩
  simp only [Finset.sum_boole, powers, Finset.card_image_of_injective _ inj,
    Nat.card_Icc, Nat.add_sub_cancel]

private abbrev mobiusDivisors (n : ℕ) (sign : ℤ) :=
  n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = sign)

private abbrev mobiusProduct (seq : ℕ → ℕ) (n : ℕ) (sign : ℤ) :=
  ∏ d ∈ mobiusDivisors n sign, seq d

/-- If `yCoord u n` has no primitive prime divisor, then the positive Möbius product divides `n` times
the negative Möbius product. -/
private lemma moebius_prod_dvd_of_no_prim {n : ℕ} (hn : 1 < n)
    (hnoprim : ∀ p : ℕ, p.Prime → p ∣ yCoord u n → ∃ m : ℕ, 0 < m ∧ m < n ∧ p ∣ yCoord u m) :
    mobiusProduct (yCoord u) n 1 ∣ mobiusProduct (yCoord u) n (-1) * n := by
  let A := mobiusProduct (yCoord u) n 1
  let B := mobiusProduct (yCoord u) n (-1)
  have nonzero (sign : ℤ) : mobiusProduct (yCoord u) n sign ≠ 0 := Finset.prod_ne_zero_iff.mpr fun d hd =>
        y_ne_zero u (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hn0 : n ≠ 0 := by omega
  rw [← Nat.factorization_le_iff_dvd (nonzero 1) (mul_ne_zero (nonzero (-1)) hn0)]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [Nat.factorization_mul (nonzero (-1)) hn0, Finsupp.add_apply]
  change A.factorization p ≤ B.factorization p + n.factorization p
  let v (d : ℕ) : ℤ := (yCoord u d).factorization p
  have prod_val (S : Finset ℕ) (hS : S ⊆ n.divisors) :
      (((∏ d ∈ S, yCoord u d).factorization p : ℕ) : ℤ) = ∑ d ∈ S, v d := by
    rw [Nat.factorization_prod (fun d hd => y_ne_zero u (Nat.pos_of_mem_divisors (hS hd))),
      Finsupp.finsetSum_apply, Nat.cast_sum]
  have hdiff : (A.factorization p : ℤ) - (B.factorization p : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * v d := by
    rw [prod_val (mobiusDivisors n 1) (Finset.filter_subset _ _),
      prod_val (mobiusDivisors n (-1)) (Finset.filter_subset _ _),
      Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rcases moebius_cases (n / d) with h | h | h <;> simp [h]
  suffices hle : ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * v d ≤ (n.factorization p : ℤ) by
    omega
  by_cases hpn : p ∣ yCoord u n
  swap
  · rw [Finset.sum_eq_zero]
    · exact Nat.cast_nonneg _
    · intro d hd
      have hnd : ¬ p ∣ yCoord u d := fun h => hpn (h.trans (y_dvd_of_dvd u (Nat.dvd_of_mem_divisors hd)))
      simp [v, Nat.factorization_eq_zero_of_not_dvd hnd]
  · have hex : ∃ m : ℕ, 0 < m ∧ p ∣ yCoord u m := ⟨n, by omega, hpn⟩
    let r := Nat.find hex
    have hr_pos : 0 < r := (Nat.find_spec hex).1
    have hpr : p ∣ yCoord u r := (Nat.find_spec hex).2
    have hr_min : ∀ m : ℕ, 0 < m → p ∣ yCoord u m → r ≤ m := fun m hm hpm => Nat.find_min' hex ⟨hm, hpm⟩
    have rank_dvd {m : ℕ} (hpm : p ∣ yCoord u m) : r ∣ m := by
      have hpg : p ∣ yCoord u (Nat.gcd r m) := y_gcd u r m ▸ Nat.dvd_gcd hpr hpm
      have hle := hr_min _ (Nat.gcd_pos_of_pos_left m hr_pos) hpg
      exact (le_antisymm (Nat.gcd_le_left m hr_pos) hle) ▸ Nat.gcd_dvd_right r m
    have hr_lt_n : r < n := by
      obtain ⟨m, hm0, hmn, hpm⟩ := hnoprim p hp hpn
      exact lt_of_le_of_lt (hr_min m hm0 hpm) hmn
    -- The valuation first contributes at r, then once at each index r * p ^ a.
    let gain (d : ℕ) : ℤ := (if d = r then v r else 0) +
      (if ∃ a > 0, d = r * p ^ a then 1 else 0)
    have total (m : ℕ) (hm : 0 < m) : ∑ d ∈ m.divisors, gain d = v m := by
      by_cases hrm : r ∣ m
      · obtain ⟨t, rfl⟩ := hrm
        have ht := Nat.pos_of_mul_pos_left hm
        simp only [gain, Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos (Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hm.ne'⟩), count_rank_powers hr_pos ht hp]
        dsimp only [v]
        rw [mul_comm r t, valuation_mul u hp hr_pos hpr ht, Nat.cast_add]
      · have hzero := Nat.factorization_eq_zero_of_not_dvd (mt rank_dvd hrm)
        change _ = ((yCoord u m).factorization p : ℤ)
        rw [hzero, Nat.cast_zero]
        apply Finset.sum_eq_zero
        intro d hd
        have hrd : ¬ r ∣ d := fun h => hrm (h.trans (Nat.dvd_of_mem_divisors hd))
        have hpow : ¬ ∃ a > 0, d = r * p ^ a := fun ⟨_, _, h⟩ => hrd ⟨_, h⟩
        have hdr : d ≠ r := by rintro rfl; exact hrd dvd_rfl
        simp [gain, hdr, hpow]
    rw [invert_sum gain v total n (by omega)]
    simp only [gain, if_neg hr_lt_n.ne', zero_add]
    split_ifs with hpow
    · obtain ⟨a, ha, he⟩ := hpow
      have hp_dvd : p ∣ n := he ▸ dvd_mul_of_dvd_right (dvd_pow_self p ha.ne') r
      exact_mod_cast (hp.pow_dvd_iff_le_factorization hn0).mp (by simpa using hp_dvd : p ^ 1 ∣ n)
    · exact Nat.cast_nonneg _

/-- Evaluation of the two real embeddings of the quadratic unit. -/
private lemma binet (n : ℕ) :
    (xCoord u n : ℝ) + yCoord u n * Real.sqrt D =
      ((xCoord u 1 : ℝ) + yCoord u 1 * Real.sqrt D) ^ n ∧
    (xCoord u n : ℝ) - yCoord u n * Real.sqrt D =
      ((xCoord u 1 : ℝ) - yCoord u 1 * Real.sqrt D) ^ n := by
  induction n with
  | zero => simp [xCoord, yCoord]
  | succ n ih =>
    obtain ⟨hy, hx⟩ := coords_add u n 1
    have hsq := Real.sq_sqrt (Nat.cast_nonneg D)
    have y : (yCoord u (n + 1) : ℝ) =
        (yCoord u n : ℝ) * xCoord u 1 + (xCoord u n : ℝ) * yCoord u 1 := by exact_mod_cast hy
    have x : (xCoord u (n + 1) : ℝ) =
        (xCoord u n : ℝ) * xCoord u 1 + (D : ℝ) * yCoord u n * yCoord u 1 := by exact_mod_cast hx
    constructor
    · rw [pow_succ, ← ih.1, x, y]
      linear_combination -(yCoord u n : ℝ) * (yCoord u 1 : ℝ) * hsq
    · rw [pow_succ, ← ih.2, x, y]
      linear_combination -(yCoord u n : ℝ) * (yCoord u 1 : ℝ) * hsq

/-- The two conjugates give a lower bound for the alternating Möbius product. -/
private lemma moebius_prod_lower_bound (seq : ℕ → ℕ) {α β scale : ℝ}
    (hβ : 0 < β) (hgap : 3 ≤ α - β) (hscale : 0 < scale)
    (binet_eq : ∀ d : ℕ, scale * (seq d : ℝ) = α ^ d - β ^ d)
    {n : ℕ} (hn : 1 < n) :
    (mobiusProduct seq n (-1) : ℝ) * 3 ^ n.totient ≤ mobiusProduct seq n 1 := by
  let Dpos := mobiusDivisors n 1
  let Dneg := mobiusDivisors n (-1)
  let z := α / β
  have hz : 1 < z := (one_lt_div hβ).mpr (by linarith)
  -- The divisor product recovers the original term when the factor at one absorbs the scale.
  let F (k : ℕ) : ℝ :=
    β ^ k.totient * (Polynomial.cyclotomic k ℝ).eval z / (if k = 1 then scale else 1)
  have hF (k : ℕ) : 0 < F k :=
    div_pos (mul_pos (pow_pos hβ _) (Polynomial.cyclotomic_pos' k hz)) (by split <;> positivity)
  have hprod (m : ℕ) (hm : 0 < m) : ∏ k ∈ m.divisors, F k = (seq m : ℝ) := by
    simp only [F, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Nat.one_mem_divisors.mpr hm.ne', if_true, Finset.prod_pow_eq_pow_sum, Nat.sum_totient,
      ← Polynomial.eval_prod, Polynomial.prod_cyclotomic_eq_X_pow_sub_one hm,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    apply (div_eq_iff hscale.ne').mpr
    rw [mul_comm (seq m : ℝ), binet_eq, mul_sub, mul_one]
    dsimp only [z]
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero m hβ.ne')]
  have hseq (m : ℕ) (hm : 0 < m) : 0 < (seq m : ℝ) := by
    rw [← hprod m hm]
    exact Finset.prod_pos fun k _ => hF k
  have inv := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
    (fun k _ => (hF k).ne') (fun m hm => (hseq m hm).ne')).mp hprod n (by omega)
  rw [Nat.prod_divisorsAntidiagonal' (fun i j => (seq j : ℝ) ^ ArithmeticFunction.moebius i)] at inv
  have term (d : ℕ) :
      (seq d : ℝ) ^ ArithmeticFunction.moebius (n / d) =
        (if ArithmeticFunction.moebius (n / d) = 1 then (seq d : ℝ) else 1) /
        (if ArithmeticFunction.moebius (n / d) = -1 then (seq d : ℝ) else 1) := by
    rcases moebius_cases (n / d) with h | h | h <;> simp [h]
  rw [Finset.prod_congr rfl (fun d _ => term d), Finset.prod_div_distrib,
    ← Finset.prod_filter, ← Finset.prod_filter] at inv
  have hneg : 0 < ∏ d ∈ Dneg, (seq d : ℝ) :=
    Finset.prod_pos fun d hd => hseq d (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have bound : (3 : ℝ) ^ n.totient ≤ F n := by
    simp only [F, if_neg hn.ne', div_one]
    have h := mul_le_mul_of_nonneg_left (Polynomial.sub_one_pow_totient_le_cyclotomic_eval hz n)
      (pow_nonneg hβ.le n.totient)
    have hz' : β * (z - 1) = α - β := by dsimp [z]; field_simp
    rw [← mul_pow, hz'] at h
    exact (pow_le_pow_left₀ (by norm_num) hgap _).trans h
  simp only [mobiusProduct, Nat.cast_prod]
  calc (∏ d ∈ Dneg, (seq d : ℝ)) * 3 ^ n.totient ≤ (∏ d ∈ Dneg, (seq d : ℝ)) * F n :=
          mul_le_mul_of_nonneg_left bound hneg.le
    _ = ∏ d ∈ Dpos, (seq d : ℝ) := by
          rw [mul_comm]
          exact ((div_eq_iff hneg.ne').mp inv).symm

private lemma pell_product_lower_bound {n : ℕ} (hn : 1 < n) :
    (mobiusProduct (yCoord u) n (-1) : ℝ) * 3 ^ n.totient ≤ mobiusProduct (yCoord u) n 1 := by
  let x : ℝ := xCoord u 1
  let y : ℝ := yCoord u 1
  let s : ℝ := Real.sqrt D
  have hd : 1 ≤ D := by exact_mod_cast (Pell.Solution₁.d_pos_of_one_lt_x u.property.1)
  have hs : 1 ≤ s := by exact Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hy : 1 ≤ y := by
    change (1 : ℝ) ≤ (yCoord u 1 : ℝ)
    exact_mod_cast (show 1 ≤ yCoord u 1 from y_pos u (by decide : 0 < 1))
  have hx : 2 ≤ x := by
    have h : (1 : ℤ) < (xCoord u 1 : ℤ) := by simpa [x_cast] using u.property.1
    change (2 : ℝ) ≤ (xCoord u 1 : ℝ)
    exact_mod_cast (show 2 ≤ xCoord u 1 by omega)
  have hys : 1 ≤ y * s := one_le_mul_of_one_le_of_one_le hy hs
  have hnorm : x ^ 2 - (D : ℝ) * y ^ 2 = 1 := by
    have h : (xCoord u 1 : ℤ) ^ 2 - (D : ℤ) * (yCoord u 1 : ℤ) ^ 2 = 1 := by
      simp only [x_cast, y_cast, Pell.Solution₁.prop]
    have hr := congrArg (fun t : ℤ => (t : ℝ)) h
    push_cast at hr
    exact hr
  have hsq : s ^ 2 = (D : ℝ) := Real.sq_sqrt (Nat.cast_nonneg D)
  have hnorm' : x ^ 2 - (y * s) ^ 2 = 1 := by
    rw [mul_pow, hsq]
    linarith
  have hconj : 0 < x - y * s := by nlinarith [hnorm']
  -- The norm identity and x ≥ 2 give (y * s) ^ 2 ≥ 3.
  have hgap : 3 ≤ 2 * (y * s) := by
    by_contra! h
    have hlt : (2 * (y * s)) ^ 2 < (3 : ℝ) ^ 2 := sq_lt_sq' (by linarith) h
    nlinarith [sq_le_sq' (by linarith : -x ≤ (2 : ℝ)) hx]
  refine moebius_prod_lower_bound (yCoord u) (α := x + y * s) (β := x - y * s)
    (scale := 2 * s) hconj (by linarith) (by linarith) ?_ hn
  intro d
  have h := binet u d
  dsimp only [x, y, s]
  linarith [h.1, h.2]

/-- For odd m, Euler's theorem puts m below 2 ^ φ(m). This also controls 2m;
each further factor of two doubles the totient. -/
private lemma lt_three_pow_totient (n : ℕ) (hn : 0 < n) : n < 3 ^ n.totient := by
  have odd_bound (m : ℕ) (hm : Odd m) : m < 2 ^ m.totient := by
    have hφ := Nat.totient_pos.mpr ((show 0 < m by obtain ⟨k, rfl⟩ := hm; omega))
    have hpow := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hφ.ne'
    have hd := (Nat.modEq_iff_dvd' hpow.le).mp (Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hm)).symm
    have := Nat.le_of_dvd (by omega : 0 < 2 ^ m.totient - 1) hd
    omega
  have twice (k : ℕ) : 2 * (2 ^ k - 1) < 3 ^ k := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [pow_succ 2, pow_succ 3]
      have := pow_pos (by decide : 0 < (2 : ℕ)) k
      have := pow_pos (by decide : 0 < (3 : ℕ)) k
      omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := he.two_dvd
      have hm : 0 < m := by omega
      rcases Nat.even_or_odd m with he | ho
      · rw [Nat.totient_two_mul_of_even he, two_mul m.totient, pow_add]
        have hr := ih m (by omega) hm
        nlinarith
      · rw [Nat.totient_two_mul_of_odd ho]
        have h := odd_bound m ho
        have h' := twice m.totient
        omega
    · exact (odd_bound n ho).trans_le (Nat.pow_le_pow_left (by decide) _)

private theorem primitive_at_index {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ yCoord u n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ yCoord u m := by
  by_contra hno
  push Not at hno
  have hdvd := moebius_prod_dvd_of_no_prim u hn hno
  let A := mobiusProduct (yCoord u) n 1
  let B := mobiusProduct (yCoord u) n (-1)
  have hBpos : 0 < B :=
    Finset.prod_pos fun d hd => y_pos u (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hABn : A ≤ B * n := Nat.le_of_dvd (Nat.mul_pos hBpos (by omega)) hdvd
  have hlow := pell_product_lower_bound u hn
  have hABnR : (A : ℝ) ≤ (B : ℝ) * (n : ℝ) := by exact_mod_cast hABn
  have hpow : 3 ^ n.totient ≤ n := by
    exact_mod_cast le_of_mul_le_mul_left (hlow.trans hABnR) (by exact_mod_cast hBpos : (0 : ℝ) < B)
  exact (lt_three_pow_totient n (by omega)).not_ge hpow

/-- Every nontrivial positive Pell solution has a new prime in its second coordinate
at every index from two onward. -/
theorem primitive_prime_divisor (v : Pell.Solution₁ (D : ℤ)) (hx : 1 < v.x) (hy : 0 < v.y)
    {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ (v ^ n).y.natAbs ∧
      ∀ j : ℕ, 0 < j → j < n → ¬ p ∣ (v ^ j).y.natAbs :=
  primitive_at_index (⟨v, hx, hy⟩ : PellUnit D) hn

end Erdos649Pell

theorem OMA.solution : OMA.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1.H1 := by
  intro D u hu k hk
  exact Erdos649Pell.primitive_prime_divisor u hu.1 hu.2.1 (by omega : 1 < k)
