import FormalConjectures.ErdosProblems.«69»
import Mathlib

/-!
# Irrationality of the binary series counting distinct prime factors

Terence Tao and Joni Teräväinen proved the irrationality theorem in
*Quantitative correlations and some problems on prime factors of consecutive
integers*, Theorem 1.3 (arXiv:2512.01739). The use of shifted tails and
alternating dilations here is inspired by sections 5.1 and 5.2 of that paper.
Kyle Pratt earlier identified the role of a large number of prime factors at
the first surviving shift in a conditional argument (arXiv:2409.15185, §2).

This formal proof groups four depths into twelve signed affine terms, isolates
one term on a pair of congruence classes, and bounds the remaining terms by an
unconditional first-moment estimate. The resulting error is bounded by a
constant times (m+1)(3/4)^m. All estimates used in the last contradiction are
proved below.
-/

section

/-
连续四个深度的一次有限差分。每个块的系数压缩成十二个不同的斜率，
随后用十六进制位拼接各块。偏移量的表格采用块内深度 1、2、3、4。
-/

namespace Erdos69Independent.Blocks

open Finset

def digitSlope : Fin 12 → ℕ := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 13]

def digitOffset : Fin 12 → ℤ := ![0, 4, 2, 10, 8, 12, 21, 25, 23, 31, 29, 33]

def digitSign : Fin 12 → ℤ := ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1]

theorem digitSlope_lt (d : Fin 12) : digitSlope d < 16 := by decide +revert

theorem digitSlope_injective : Function.Injective digitSlope := by decide

theorem digitSign_eq (d : Fin 12) : digitSign d = 1 ∨ digitSign d = -1 := by decide +revert

def localShift (e : ℤ) (d : Fin 12) : ℤ := digitSlope d * e - digitOffset d

def blockShift (t : ℕ) (h : ℤ) (d : Fin 12) : ℤ :=
  16 ^ t * localShift (h - 4 * t) d

-- 这里只对四个整数逐项求和。相同位置上的两个函数值系数相反。
theorem digit_annihilates {A : Type*} [AddCommGroup A] (f : ℤ → A) (w x e : ℤ)
    (he₁ : 1 ≤ e) (he₄ : e ≤ 4) :
    ∑ d : Fin 12, digitSign d • f (x + w * localShift e d) = 0 := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, digitSign, digitSlope, digitOffset, localShift] <;> abel

theorem block_annihilates {A : Type*} [AddCommGroup A] (f : ℤ → A) (t : ℕ) (h x : ℤ)
    (h₁ : 4 * (t : ℤ) < h) (h₄ : h ≤ 4 * (t : ℤ) + 4) :
    ∑ d : Fin 12, digitSign d • f (x + blockShift t h d) = 0 :=
  digit_annihilates _ _ _ _ (by omega) (by omega)

-- 每一位都可以由总斜率唯一恢复。
def Path : ℕ → Type
  | 0 => Unit
  | m + 1 => Fin 12 × Path m

instance pathFintype : (m : ℕ) → Fintype (Path m)
  | 0 => inferInstanceAs (Fintype Unit)
  | m + 1 =>
    letI := pathFintype m
    inferInstanceAs (Fintype (Fin 12 × Path m))

instance pathDecidableEq : (m : ℕ) → DecidableEq (Path m)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | m + 1 =>
    letI := pathDecidableEq m
    inferInstanceAs (DecidableEq (Fin 12 × Path m))

theorem card_path (m : ℕ) : Fintype.card (Path m) = 12 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Fin 12 × Path m) = 12 ^ (m + 1)
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

def slope : (m : ℕ) → Path m → ℕ
  | 0, _ => 0
  | m + 1, (d, p) => 16 ^ m * digitSlope d + slope m p

def offset : (m : ℕ) → Path m → ℤ
  | 0, _ => 0
  | m + 1, (d, p) =>
    16 ^ m * (4 * (m : ℤ) * digitSlope d + digitOffset d) + offset m p

def sign : (m : ℕ) → Path m → ℤ
  | 0, _ => 1
  | m + 1, (d, p) => digitSign d * sign m p

def shift : (m : ℕ) → ℤ → Path m → ℤ
  | 0, _, _ => 0
  | m + 1, h, (d, p) => blockShift m h d + shift m h p

theorem shift_eq_affine (m : ℕ) (h : ℤ) (p : Path m) :
    shift m h p = (slope m p : ℤ) * h - offset m p := by
  induction m with
  | zero => simp [shift, slope, offset]
  | succ m ih =>
    obtain ⟨d, p⟩ := p
    simp only [shift, slope, offset, blockShift, localShift, ih, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring

theorem slope_lt (m : ℕ) (p : Path m) : slope m p < 16 ^ m := by
  induction m with
  | zero => simp [slope]
  | succ m ih =>
    obtain ⟨d, p⟩ := p
    have hd : digitSlope d + 1 ≤ 16 := digitSlope_lt d
    calc
      slope (m + 1) (d, p) < 16 ^ m * digitSlope d + 16 ^ m :=
        Nat.add_lt_add_left (ih p) _
      _ = 16 ^ m * (digitSlope d + 1) := by ring
      _ ≤ 16 ^ m * 16 := Nat.mul_le_mul_left _ hd
      _ = 16 ^ (m + 1) := (pow_succ _ _).symm

theorem slope_injective (m : ℕ) : Function.Injective (slope m) := by
  induction m with
  | zero => exact fun _ _ _ => Subsingleton.elim (α := Unit) _ _
  | succ m ih =>
    rintro ⟨d, p⟩ ⟨e, q⟩ heq
    change 16 ^ m * digitSlope d + slope m p = 16 ^ m * digitSlope e + slope m q at heq
    have hpow : 0 < 16 ^ m := by positivity
    have hdigit := congrArg (· / 16 ^ m) heq
    simp only [Nat.mul_add_div hpow, Nat.div_eq_of_lt (slope_lt m _), Nat.add_zero] at hdigit
    obtain rfl := digitSlope_injective hdigit
    exact Prod.ext rfl (ih (Nat.add_left_cancel heq))

theorem sign_eq (m : ℕ) (p : Path m) : sign m p = 1 ∨ sign m p = -1 := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    obtain ⟨d,p⟩ := p
    rcases digitSign_eq d with hd | hd <;> rcases ih p with hp | hp <;> simp [sign, hd, hp]

-- 对所有平移和所有加法交换群同时消元，因而也能作用在单点指示函数上。
theorem sum_annihilates {A : Type*} [AddCommGroup A] (f : ℤ → A) (m : ℕ) (h x : ℤ)
    (h₁ : 1 ≤ h) (hm : h ≤ 4 * (m : ℤ)) :
    ∑ p : Path m, sign m p • f (x + shift m h p) = 0 := by
  induction m generalizing x with
  | zero => omega
  | succ m ih =>
    change ∑ z : Fin 12 × Path m, (digitSign z.1 * sign m z.2) •
      f (x + (blockShift m h z.1 + shift m h z.2)) = 0
    rw [Fintype.sum_prod_type]
    by_cases hsmall : h ≤ 4 * (m : ℤ)
    · apply sum_eq_zero
      intro d _
      simp only [mul_smul, ← add_assoc, ← Finset.smul_sum, ih _ hsmall, smul_zero]
    · rw [Finset.sum_comm]
      apply sum_eq_zero
      intro p _
      calc
        _ = sign m p • ∑ d : Fin 12, digitSign d •
              f ((x + shift m h p) + blockShift m h d) := by
          rw [Finset.smul_sum]
          apply sum_congr rfl
          intro d _
          rw [mul_comm, mul_smul]
          congr 3
          abel
        _ = 0 := by rw [block_annihilates _ _ _ _ (by omega) (by omega), smul_zero]

def topPath : (m : ℕ) → Path m
  | 0 => ()
  | m + 1 => (11, topPath m)

theorem sign_top (m : ℕ) : sign m (topPath m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [topPath, sign, ih, digitSign]

theorem localShift_lt_top (e : ℤ) (he : 5 ≤ e) (d : Fin 12) (hd : d ≠ 11) :
    localShift e d < localShift e 11 := by
  change localShift e d < 13 * e - 33
  fin_cases d <;> first
    | exact False.elim (hd rfl)
    | (norm_num [localShift, digitSlope, digitOffset]; omega)

theorem shift_lt_top_of_ne (m : ℕ) (h : ℤ) (hh : 4 * (m : ℤ) < h) (p : Path m)
    (hp : p ≠ topPath m) : shift m h p < shift m h (topPath m) := by
  induction m with
  | zero => exact False.elim (hp (Subsingleton.elim (α := Unit) _ _))
  | succ m ih =>
    obtain ⟨d, p⟩ := p
    have hprev : 4 * (m : ℤ) < h := by omega
    have hlast : 5 ≤ h - 4 * (m : ℤ) := by omega
    change blockShift m h d + shift m h p < blockShift m h 11 + shift m h (topPath m)
    by_cases hd : d = 11
    · subst d
      exact add_lt_add_right (ih hprev p (fun hpt => hp (by rw [hpt]; rfl))) _
    · have hdlt : blockShift m h d < blockShift m h 11 :=
        mul_lt_mul_of_pos_left (localShift_lt_top _ hlast _ hd) (by positivity)
      have hple : shift m h p ≤ shift m h (topPath m) := by
        by_cases hpt : p = topPath m
        · rw [hpt]
        · exact (ih hprev p hpt).le
      exact add_lt_add_of_lt_of_le hdlt hple

-- 重合的整数位置先求和；末层最大位置的系数恰好为 1。
def coefficient (m : ℕ) (h r : ℤ) : ℤ :=
  ∑ p : Path m, if shift m h p = r then sign m p else 0

theorem coefficient_zero (m : ℕ) (h r : ℤ) (h₁ : 1 ≤ h) (hm : h ≤ 4 * (m : ℤ)) :
    coefficient m h r = 0 := by
  simpa [coefficient, smul_ite, zsmul_eq_mul] using
    sum_annihilates (fun z => if z = r then (1 : ℤ) else 0) m h 0 h₁ hm

theorem coefficient_top (m : ℕ) (h : ℤ) (hh : 4 * (m : ℤ) < h) :
    coefficient m h (shift m h (topPath m)) = 1 := by
  unfold coefficient
  rw [Finset.sum_eq_single (topPath m)]
  · simp [sign_top]
  · intro p _ hp
    simp [(shift_lt_top_of_ne m h hh p hp).ne]
  · simp

end Erdos69Independent.Blocks

end

section

/- 第 69 题的有限模数构造。所有同余从自然数的中国剩余定理推出。 -/

namespace Erdos69CRT

open Finset
open scoped BigOperators

/-- 参数选取保证每个斜率在步长阶乘的所有素因子处都等于一。 -/
def factorialSlope (V L a : ℕ) : ℕ := 1 + (L + a) * (V + 1).factorial

theorem factorialSlope_pos (V L a : ℕ) : 0 < factorialSlope V L a := by
  unfold factorialSlope
  omega

private theorem factorialSlope_coprime_of_lt {V L a b : ℕ} (hab : a < b) (hb : b ≤ V) :
    (factorialSlope V L a).Coprime (factorialSlope V L b) := by
  by_contra hn
  obtain ⟨p, hp, ha', hb'⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
  let D := (V + 1).factorial
  have hsum : factorialSlope V L b = factorialSlope V L a + (b - a) * D := by
    simp only [factorialSlope, D]
    conv_lhs => rw [show b = a + (b - a) by omega]
    ring
  rw [hsum] at hb'
  have hprod := (Nat.dvd_add_iff_right ha').mpr hb'
  have hd : p ∣ D := by
    rcases hp.dvd_mul.mp hprod with h | h
    · exact h.trans (Nat.dvd_factorial (by omega) (by omega))
    · exact h
  have hmul : p ∣ (L + a) * D := hd.trans (Nat.dvd_mul_left _ _)
  have hone := (Nat.dvd_add_iff_left hmul).mpr ha'
  exact hp.ne_one (Nat.dvd_one.mp hone)

theorem factorialSlope_coprime {V L a b : ℕ} (ha : a ≤ V) (hb : b ≤ V) (hne : a ≠ b) :
    (factorialSlope V L a).Coprime (factorialSlope V L b) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact factorialSlope_coprime_of_lt h hb
  · exact (factorialSlope_coprime_of_lt h ha).symm

private def negResidue (m c : ℕ) : ℕ := m * (c + 1) - c

private theorem negResidue_add {m : ℕ} (hm : 0 < m) (c : ℕ) :
    m ∣ negResidue m c + c := by
  have h : c ≤ m * (c + 1) := by nlinarith
  simp only [negResidue, Nat.sub_add_cancel h]
  exact Nat.dvd_mul_right _ _

/-- 平方模数容许为每个斜率独立规定一个偏移。 -/
theorem bounded_square_solutions {ι : Type*} (s : Finset ι) (a c : ι → ℕ) (V L : ℕ)
    (hv : ∀ i ∈ s, a i ≤ V) (hi : Set.InjOn a (s : Set ι)) :
    ∃ x < ∏ i ∈ s, (factorialSlope V L (a i)) ^ 2,
      ∀ i ∈ s, (factorialSlope V L (a i)) ^ 2 ∣ x + c i := by
  classical
  let m := fun i => factorialSlope V L (a i) ^ 2
  have hm : ∀ i ∈ s, m i ≠ 0 := fun i _ => (pow_pos (factorialSlope_pos ..) _).ne'
  have hc : Set.Pairwise (s : Set ι) (fun i j => (m i).Coprime (m j)) := by
    intro i bis j bjs hij
    exact ((factorialSlope_coprime (L := L) (hv i bis) (hv j bjs)
      (fun h => hij (hi bis bjs h))).pow_left 2).pow_right 2
  let r := fun i => negResidue (m i) (c i)
  let x := Nat.chineseRemainderOfFinset r m s hm hc
  refine ⟨x, Nat.chineseRemainderOfFinset_lt_prod r m hm hc, ?_⟩
  intro i his
  exact ((x.prop i his).add_right (c i)).dvd_iff (dvd_refl _) |>.mpr
    (negResidue_add (Nat.pos_of_ne_zero (hm i his)) _)

/-- 任意指定数量的素数，全部严格超过 B，并有显式的最大素数上界。 -/
theorem bounded_prime_pool (B : ℕ) (hB : B ≠ 0) (k : ℕ) :
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧ B < p ∧ p ≤ 2 ^ k * B := by
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨P, hcard, hP⟩ := ih
    obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k * B)
      (mul_ne_zero (pow_ne_zero _ (by decide)) hB)
    have hbnd : B ≤ 2 ^ k * B := Nat.le_mul_of_pos_left B (by positivity)
    have hqP : q ∉ P := fun h => (Nat.not_lt_of_ge (hP q h).2.2) hlo
    refine ⟨insert q P, by simp [hcard, hqP], ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | h
    · exact ⟨hq, hbnd.trans_lt hlo, by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hhi⟩
    · obtain ⟨hprime, hlarge, hsmall⟩ := hP p h
      refine ⟨hprime, hlarge, ?_⟩
      rw [pow_succ]
      nlinarith

/-- 两个同余于零的偏移若均小于模数，则偏移本身相等。 -/
theorem shift_dvd_iff_eq {m n c d : ℕ} (hc : c < m) (hd : d < m) (hn : m ∣ n + d) :
    m ∣ n + c ↔ c = d := by
  constructor
  · intro h
    exact (Nat.ModEq.add_left_cancel' n (h.modEq_zero_nat.trans hn.zero_modEq_nat)
      ).eq_of_lt_of_lt hc hd
  · rintro rfl
    exact hn

/-- 在固定底数模 F 上自由指定另一个互素模 G 的零点偏移。 -/
theorem shifted_crt (F G x t : ℕ) (hF : 0 < F) (hG : 0 < G) (hcop : F.Coprime G) :
    ∃ r < F * G, ∀ j : ℕ,
      r + F * G * j ≡ x [MOD F] ∧ G ∣ r + F * G * j + t := by
  let r := Nat.chineseRemainder hcop x (negResidue G t)
  refine ⟨r, Nat.chineseRemainder_lt_mul hcop _ _ hF.ne' hG.ne', ?_⟩
  intro j
  have hstep : r.val + F * G * j ≡ r.val [MOD F * G] :=
    Nat.add_modulus_mul_modEq_iff.mpr (Nat.ModEq.refl _)
  constructor
  · exact (hstep.of_dvd (Nat.dvd_mul_right F G)).trans r.prop.1
  · have hs := ((hstep.of_dvd (Nat.dvd_mul_left G F)).trans r.prop.2).add_right t
    exact (hs.dvd_iff (dvd_refl _)).mpr (negResidue_add hG t)

def squarePeriod {ι : Type*} (s : Finset ι) (a : ι → ℕ) (V L : ℕ) : ℕ :=
  ∏ i ∈ s, factorialSlope V L (a i) ^ 2

def poolPeriod (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

/-- 两条等差数列有共同周期和相同的底数模 F 的余数。
第一条对全部选择素数精确命中 t，第二条在 [0,B] 内全部避开。 -/
structure ControlledPair {ι : Type*} (s : Finset ι) (a c : ι → ℕ)
    (V L : ℕ) (P : Finset ℕ) (t B : ℕ) where
  hit : ℕ
  miss : ℕ
  hit_lt : hit < squarePeriod s a V L * poolPeriod P
  miss_lt : miss < squarePeriod s a V L * poolPeriod P
  common : hit ≡ miss [MOD squarePeriod s a V L]
  square_hit : ∀ j i, i ∈ s → factorialSlope V L (a i) ^ 2 ∣
    hit + squarePeriod s a V L * poolPeriod P * j + c i
  square_miss : ∀ j i, i ∈ s → factorialSlope V L (a i) ^ 2 ∣
    miss + squarePeriod s a V L * poolPeriod P * j + c i
  selected_hit : ∀ j p, p ∈ P → ∀ d ≤ B, p ∣
    hit + squarePeriod s a V L * poolPeriod P * j + d ↔ d = t
  selected_miss : ∀ j p, p ∈ P → ∀ d ≤ B, ¬p ∣
    miss + squarePeriod s a V L * poolPeriod P * j + d

theorem controlled_pair {ι : Type*} (s : Finset ι) (a c : ι → ℕ) (V L : ℕ)
    (hv : ∀ i ∈ s, a i ≤ V) (hi : Set.InjOn a (s : Set ι))
    (P : Finset ℕ) (t B : ℕ) (ht : t ≤ B)
    (hp : ∀ p ∈ P, p.Prime ∧ B + 1 < p)
    (ha : ∀ p ∈ P, ∀ i ∈ s, factorialSlope V L (a i) < p) :
    Nonempty (ControlledPair s a c V L P t B) := by
  classical
  let F := squarePeriod s a V L
  let G := poolPeriod P
  have hF : 0 < F := Finset.prod_pos (fun i _ => pow_pos (factorialSlope_pos ..) 2)
  have hG : 0 < G := Finset.prod_pos (fun p h => (hp p h).1.pos)
  have hcop : F.Coprime G := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p h
    apply Nat.coprime_prod_left_iff.mpr
    intro i his
    have hnot : ¬p ∣ factorialSlope V L (a i) := fun hdiv =>
      (Nat.not_le_of_gt (ha p h i his)) (Nat.le_of_dvd (factorialSlope_pos ..) hdiv)
    exact ((hp p h).1.coprime_iff_not_dvd.mpr hnot).symm.pow_left 2
  obtain ⟨x, _, hx⟩ := bounded_square_solutions s a c V L hv hi
  obtain ⟨r, hr, hrs⟩ := shifted_crt F G x t hF hG hcop
  obtain ⟨z, hz, hzs⟩ := shifted_crt F G x (B + 1) hF hG hcop
  have base (w : ℕ) (hw : w ≡ x [MOD F]) (i : ι) (his : i ∈ s) :
      factorialSlope V L (a i) ^ 2 ∣ w + c i :=
    ((hw.add_right (c i)).dvd_iff
      (Finset.dvd_prod_of_mem (fun l => factorialSlope V L (a l) ^ 2) his)).mpr (hx i his)
  refine ⟨⟨r, z, hr, hz, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa using ((hrs 0).1.trans (hzs 0).1.symm)
  · exact fun j i h => base _ (hrs j).1 i h
  · exact fun j i h => base _ (hzs j).1 i h
  · intro j p h d hd
    have hq := (hp p h).2
    exact shift_dvd_iff_eq (by omega) (by omega)
      ((Finset.dvd_prod_of_mem id h).trans (hrs j).2)
  · intro j p h d hd hdiv
    have hq := (hp p h).2
    have hfalse := (shift_dvd_iff_eq (m := p) (c := d) (d := B + 1)
      (by omega) hq ((Finset.dvd_prod_of_mem id h).trans (hzs j).2)).mp hdiv
    omega

end Erdos69CRT

end

section

/- 将十二项的整数平移变为具有互素正斜率的自然数仿射式。
首个未消去深度的最大位置在整个尾部只出现一次。 -/

namespace Erdos69Independent.AffineBlocks

open Finset

def K (m : ℕ) := 4 * m
def V (m : ℕ) := 16 ^ m
def L (m : ℕ) := (K m + 2) * (V m + 1)
def D (m : ℕ) := (V m + 1).factorial
def H (m : ℕ) := (m + 1) ^ 2 + 4 * m + 1
def B (m : ℕ) := 1 + D m * K m * V m + (1 + D m * (L m + V m)) * (H m + 1)

def a (m : ℕ) (p : Blocks.Path m) : ℕ := 1 + D m * (L m + Blocks.slope m p)
def c (m : ℕ) (p : Blocks.Path m) : ℕ := D m * (K m * V m - (Blocks.offset m p).toNat)
def shift (m h : ℕ) (p : Blocks.Path m) : ℕ := a m p * h + c m p
def special (m : ℕ) : ℕ := shift m (K m + 1) (Blocks.topPath m)

theorem a_pos (m : ℕ) (p : Blocks.Path m) : 0 < a m p := by unfold a; omega

theorem a_eq_factorialSlope (m : ℕ) (p : Blocks.Path m) :
    a m p = Erdos69CRT.factorialSlope (V m) (L m) (Blocks.slope m p) := by
  simp only [a, D, Erdos69CRT.factorialSlope, Nat.mul_comm (V m + 1).factorial]

theorem shift_pos (m h : ℕ) (p : Blocks.Path m) (hh : 0 < h) : 0 < shift m h p :=
  Nat.lt_of_lt_of_le (Nat.mul_pos (a_pos m p) hh) (Nat.le_add_right _ _)

theorem a_injective (m : ℕ) : Function.Injective (a m) := by
  intro p q hpq
  apply Blocks.slope_injective m
  have hD : 0 < D m := Nat.factorial_pos _
  simp [a, hD.ne'] at hpq
  exact hpq

theorem a_coprime_of_ne (m : ℕ) (p q : Blocks.Path m) (hpq : p ≠ q) :
    (a m p).Coprime (a m q) := by
  simpa only [a, D, Erdos69CRT.factorialSlope, Nat.mul_comm (V m + 1).factorial] using
    Erdos69CRT.factorialSlope_coprime (V := V m) (L := L m) (Blocks.slope_lt m p).le
      (Blocks.slope_lt m q).le (fun h => hpq (Blocks.slope_injective m h))

private theorem digitOffset_bounds (d : Fin 12) :
    0 ≤ Blocks.digitOffset d ∧ Blocks.digitOffset d ≤ 4 * (Blocks.digitSlope d : ℤ) := by
  decide +revert

theorem offset_nonneg (m : ℕ) (p : Blocks.Path m) : 0 ≤ Blocks.offset m p := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨d,p⟩ := p
    have hd := (digitOffset_bounds d).1
    have hp := ih p
    dsimp only [Blocks.offset]
    positivity

theorem offset_le_depth_slope (m : ℕ) (p : Blocks.Path m) :
    Blocks.offset m p ≤ (4 * (m : ℤ)) * Blocks.slope m p := by
  induction m with
  | zero => simp [Blocks.offset, Blocks.slope]
  | succ m ih =>
    obtain ⟨d,p⟩ := p
    have hd := (digitOffset_bounds d).2
    have ha : 4 * (m : ℤ) * Blocks.digitSlope d + Blocks.digitOffset d ≤
        4 * ((m : ℤ) + 1) * Blocks.digitSlope d := by linarith
    have hs := mul_le_mul_of_nonneg_left ha (show 0 ≤ (16 : ℤ)^m by positivity)
    have hsum := add_le_add hs (ih p)
    simp only [Blocks.offset, Blocks.slope, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_succ]
    linarith [Nat.cast_nonneg (α := ℤ) (Blocks.slope m p)]

theorem offset_toNat_le (m : ℕ) (p : Blocks.Path m) :
    (Blocks.offset m p).toNat ≤ K m * V m := by
  apply Int.toNat_le.mpr
  have hs : (Blocks.slope m p : ℤ) ≤ V m := by exact_mod_cast (Blocks.slope_lt m p).le
  calc
    _ ≤ 4 * (m : ℤ) * Blocks.slope m p := offset_le_depth_slope _ _
    _ ≤ 4 * (m : ℤ) * V m := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by simp [K]

theorem shift_cast (m h : ℕ) (p : Blocks.Path m) :
    (shift m h p : ℤ) = h + D m * ((L m : ℤ) * h + K m * V m + Blocks.shift m h p) := by
  simp only [shift, a, c, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_sub (offset_toNat_le _ _), Int.toNat_of_nonneg (offset_nonneg _ _),
    Blocks.shift_eq_affine]
  ring

theorem sum_annihilates {A : Type*} [AddCommGroup A] (f : ℕ → A) (m h : ℕ)
    (h₁ : 1 ≤ h) (hm : h ≤ K m) :
    ∑ p : Blocks.Path m, Blocks.sign m p • f (shift m h p) = 0 := by
  let g := fun t : ℤ => f ((h : ℤ) + D m * ((L m : ℤ) * h + K m * V m + t)).toNat
  have heq (p : Blocks.Path m) : g (0 + Blocks.shift m (h : ℤ) p) = f (shift m h p) := by
    simp [g, ← shift_cast]
  simpa only [heq] using Blocks.sum_annihilates g m h 0 (by exact_mod_cast h₁)
    (by exact_mod_cast hm : (h : ℤ) ≤ 4 * m)

theorem shift_lt_top_of_ne (m h : ℕ) (hh : K m < h) (p : Blocks.Path m)
    (hp : p ≠ Blocks.topPath m) : shift m h p < shift m h (Blocks.topPath m) := by
  apply Int.ofNat_lt.mp
  rw [shift_cast, shift_cast]
  have hlt := Blocks.shift_lt_top_of_ne m h (by exact_mod_cast hh) p hp
  have hD : 0 < (D m : ℤ) := by exact_mod_cast Nat.factorial_pos (V m + 1)
  gcongr

private theorem raw_nonneg (m h : ℕ) (hh : K m ≤ h) (p : Blocks.Path m) :
    0 ≤ Blocks.shift m h p := by
  have hcast : 4 * (m : ℤ) ≤ h := by exact_mod_cast hh
  have hmul := mul_le_mul_of_nonneg_right hcast (Nat.cast_nonneg (α := ℤ) (Blocks.slope m p))
  rw [Blocks.shift_eq_affine]
  linarith [offset_le_depth_slope m p]

theorem special_lt_of_later (m h : ℕ) (hh : K m + 1 < h) (p : Blocks.Path m) :
    special m < shift m h p := by
  apply Int.ofNat_lt.mp
  simp only [special, shift_cast, Nat.cast_succ]
  have hcast : (K m : ℤ) + 1 < h := by exact_mod_cast hh
  have hsep : (V m : ℤ) * (K m + 1) < L m := by
    simp only [L, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    nlinarith [Nat.cast_nonneg (α := ℤ) (V m), Nat.cast_nonneg (α := ℤ) (K m)]
  have hs : (Blocks.slope m (Blocks.topPath m) : ℤ) ≤ V m := by
    exact_mod_cast (Blocks.slope_lt m _).le
  have hbound : Blocks.shift m ((K m : ℤ) + 1) (Blocks.topPath m) < L m := by
    rw [Blocks.shift_eq_affine]
    have hmul := mul_le_mul_of_nonneg_right hs (show 0 ≤ (K m : ℤ) + 1 by positivity)
    linarith [offset_nonneg m (Blocks.topPath m)]
  have hl := mul_le_mul_of_nonneg_left (show (K m : ℤ) + 1 + 1 ≤ h by omega)
    (Nat.cast_nonneg (α := ℤ) (L m))
  have hraw := raw_nonneg m h (by omega) p
  have hinner : (L m : ℤ) * (K m + 1) + K m * V m +
      Blocks.shift m ((K m : ℤ) + 1) (Blocks.topPath m) <
      (L m : ℤ) * h + K m * V m + Blocks.shift m h p := by linarith
  exact add_lt_add hcast (mul_lt_mul_of_pos_left hinner
    (by exact_mod_cast Nat.factorial_pos (V m + 1) : 0 < (D m : ℤ)))

theorem shift_eq_special_iff (m h : ℕ) (hh : K m < h) (p : Blocks.Path m) :
    shift m h p = special m ↔ h = K m + 1 ∧ p = Blocks.topPath m := by
  constructor
  · intro heq
    by_cases hfirst : h = K m + 1
    · subst h
      refine ⟨rfl, by_contra fun hp => ?_⟩
      exact (shift_lt_top_of_ne m _ hh p hp).ne heq
    · exact False.elim ((special_lt_of_later m h (by omega) p).ne' heq)
  · rintro ⟨rfl,rfl⟩
    rfl

theorem shift_lt_bound (m h : ℕ) (p : Blocks.Path m) (hh : h ≤ H m) :
    shift m h p < B m := by
  have ha : a m p ≤ 1 + D m * (L m + V m) := by
    unfold a
    gcongr
    exact (Blocks.slope_lt m p).le
  have hc : c m p ≤ D m * (K m * V m) :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hp := Nat.mul_le_mul ha hh
  unfold shift B
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc (D m) (K m)]
  omega

theorem first_le_height (m : ℕ) : K m + 1 ≤ H m := by unfold K H; omega

theorem special_lt_bound (m : ℕ) : special m < B m :=
  shift_lt_bound _ _ _ (first_le_height m)

theorem a_lt_bound (m : ℕ) (p : Blocks.Path m) : a m p < B m := by
  have hH : 1 ≤ H m := (show 1 ≤ K m + 1 by omega).trans (first_le_height m)
  have h := shift_lt_bound m 1 p hH
  simp only [shift, Nat.mul_one] at h
  omega

theorem c_lt_bound (m : ℕ) (p : Blocks.Path m) : c m p < B m := by
  simpa only [shift, Nat.mul_zero, Nat.zero_add] using shift_lt_bound m 0 p (Nat.zero_le _)

theorem shift_le_bound_mul (m h : ℕ) (p : Blocks.Path m) : shift m h p ≤ B m * (h + 1) := by
  rw [shift, Nat.mul_add, Nat.mul_one]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (a_lt_bound _ _).le) (c_lt_bound _ _).le

theorem signed_special {A : Type*} [AddCommGroup A] (m h : ℕ) (hh : K m < h) (v : A) :
    ∑ p : Blocks.Path m, Blocks.sign m p • (if shift m h p = special m then v else 0) =
      if h = K m + 1 then v else 0 := by
  classical
  simp_rw [shift_eq_special_iff _ _ hh]
  by_cases heq : h = K m + 1
  · simp [heq, smul_ite, Blocks.sign_top]
  · simp [heq]

theorem finite_special_sum (m : ℕ) (v : ℝ) :
    ∑ h ∈ Icc (K m + 1) (H m),
      (∑ p : Blocks.Path m, Blocks.sign m p •
        (if shift m h p = special m then v else 0)) / 2^h = v / 2^(K m + 1) := by
  rw [Finset.sum_eq_single (K m + 1)]
  · rw [signed_special m (K m + 1) (Nat.lt_succ_self _) v, if_pos rfl]
  · intro h hh heq
    rw [signed_special m h (Finset.mem_Icc.mp hh).1 v, if_neg heq, zero_div]
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨le_rfl, first_le_height m⟩))

end Erdos69Independent.AffineBlocks

end

section

/- 把质因子分成两条数列共有的、由同余指定的、以及周期以外的三部分。 -/

open scoped ArithmeticFunction.omega
open Finset

namespace Erdos69Independent

def poolCount (P : Finset ℕ) (n : ℕ) : ℕ := (P.filter (· ∣ n)).card

def freeCount (M n : ℕ) : ℕ := (n.primeFactors.filter (fun p => ¬ p ∣ M)).card

theorem omega_partition {F n : ℕ} (P : Finset ℕ) (hF : 0<F) (hn : 0<n)
    (hp : ∀ p ∈ P, Nat.Prime p) :
    ω n = poolCount (F.primeFactors \ P) n + poolCount P n + freeCount (F*∏ p ∈ P,p) n := by
  classical
  let M := F*∏ p ∈ P,p
  have hG : 0 < ∏ p ∈ P,p := Finset.prod_pos fun p h => (hp p h).pos
  have hM : M ≠ 0 := (Nat.mul_pos hF hG).ne'
  have huv : (F.primeFactors \ P) ∪ P = M.primeFactors := by
    rw [show M.primeFactors = F.primeFactors ∪ P by
      rw [Nat.primeFactors_mul hF.ne' hG.ne', Nat.primeFactors_prod hp]]
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have he : n.primeFactors.filter (· ∣ M) = M.primeFactors.filter (· ∣ n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hM,
      Nat.mem_primeFactors_of_ne_zero hn.ne']
    tauto
  have hd : Disjoint ((F.primeFactors \ P).filter (· ∣ n)) (P.filter (· ∣ n)) := by
    refine Finset.disjoint_left.mpr fun p h₁ h₂ => ?_
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h₁).1).2 (Finset.mem_filter.mp h₂).1
  have ht := n.primeFactors.card_filter_add_card_filter_not (fun p => p ∣ M)
  rw [he, ← huv, Finset.filter_union, Finset.card_union_of_disjoint hd] at ht
  exact ht.symm

theorem omega_partition_diff {F u v : ℕ} (P : Finset ℕ) (hF : 0<F) (hu : 0<u)
    (hv : 0<v) (huv : u ≡ v [MOD F]) (hp : ∀ p ∈ P, Nat.Prime p) :
    (ω u : ℝ) - ω v = (poolCount P u : ℝ) - poolCount P v +
      ((freeCount (F*∏ p ∈ P,p) u : ℝ) - freeCount (F*∏ p ∈ P,p) v) := by
  have he : poolCount (F.primeFactors \ P) u = poolCount (F.primeFactors \ P) v := by
    unfold poolCount
    congr 1
    apply Finset.filter_congr
    intro p h
    exact huv.dvd_iff (Nat.mem_primeFactors.mp (Finset.mem_sdiff.mp h).1).2.1
  have h₁ := omega_partition P hF hu hp
  have h₂ := omega_partition P hF hv hp
  rw [he] at h₁
  rw [h₁, h₂]
  push_cast
  ring

theorem poolCount_bound (P : Finset ℕ) (n : ℕ) : poolCount P n ≤ P.card :=
  Finset.card_filter_le ..

theorem poolCount_hit {P : Finset ℕ} {u t d : ℕ}
    (hit : ∀ p ∈ P, p ∣ u ↔ d=t) : poolCount P u = if d=t then P.card else 0 := by
  by_cases h : d=t
  · simp [poolCount,h, Finset.filter_true_of_mem (fun p hp => (hit p hp).mpr h)]
  · simp [poolCount,h, Finset.filter_false_of_mem (fun p hp hd => h ((hit p hp).mp hd))]

theorem poolCount_miss {P : Finset ℕ} {u : ℕ} (miss : ∀ p ∈ P, ¬p ∣ u) :
    poolCount P u = 0 := by simp [poolCount, Finset.filter_false_of_mem miss]

end Erdos69Independent

end

section

/- 两条等差数列的有符号逐层差。前段严格消失，中段恰好减去指定的主项，
余下各层对自由质因子和选定质因子分别求和估计。 -/

namespace Erdos69Independent.AffineBlocks

open Finset
open scoped ArithmeticFunction.omega

noncomputable def row (m M hit miss i j : ℕ) : ℝ :=
  (∑ p : Blocks.Path m, (Blocks.sign m p : ℝ) *
    ((ω (hit + M*i + shift m (j+1) p) : ℝ) - ω (miss + M*i + shift m (j+1) p))) / 2^(j+1)

theorem row_zero (m M hit miss i j : ℕ) (hj : j < K m) : row m M hit miss i j = 0 := by
  unfold row
  have hz := sum_annihilates (fun d => (ω (hit + M*i + d) : ℝ) - ω (miss + M*i + d))
    m (j+1) (by omega) (by omega)
  simpa only [zsmul_eq_mul, hz, zero_div] using congrArg (· / (2 : ℝ)^(j+1)) hz

private theorem abs_signed_diff_le (m : ℕ) (u v : Blocks.Path m → ℕ) :
    |∑ p : Blocks.Path m, (Blocks.sign m p : ℝ) * ((u p : ℝ) - v p)| ≤
      ∑ p : Blocks.Path m, ((u p : ℝ) + v p) := by
  refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun p _ => ?_)
  have hs : |(Blocks.sign m p : ℝ)| = 1 := by
    rcases Blocks.sign_eq m p with hp | hp <;> simp [hp]
  rw [abs_mul, hs, one_mul]
  exact abs_sub_le_iff.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) (v p)],
    by linarith [Nat.cast_nonneg (α := ℝ) (u p)]⟩

theorem row_bound (m j : ℕ) (P : Finset ℕ) {F M hit miss : ℕ} (A : ℝ)
    (hF : 0 < F) (hM : M = F * ∏ q ∈ P, q) (hp : ∀ q ∈ P, q.Prime)
    (hcommon : hit ≡ miss [MOD F])
    (hsel : ∀ i q, q ∈ P → ∀ d ≤ B m, q ∣ hit + M*i + d ↔ d = special m)
    (havoid : ∀ i q, q ∈ P → ∀ d ≤ B m, ¬ q ∣ miss + M*i + d)
    (hfreeHit : ∀ p : Blocks.Path m, ∑ i ∈ range M,
      (freeCount M (hit + M*i + shift m (j+1) p) : ℝ) ≤ (M : ℝ) * (A+j))
    (hfreeMiss : ∀ p : Blocks.Path m, ∑ i ∈ range M,
      (freeCount M (miss + M*i + shift m (j+1) p) : ℝ) ≤ (M : ℝ) * (A+j)) :
    ∑ i ∈ range M, |row m M hit miss i j -
      (if j = K m then (P.card : ℝ) / 2^(K m+1) else 0)| ≤
        (if K m ≤ j then 2 * (M : ℝ) * (12 : ℝ)^m * (A+j) / 2^(j+1) else 0) +
        (if H m ≤ j then 2 * (M : ℝ) * (12 : ℝ)^m * (P.card : ℝ) / 2^(j+1) else 0) := by
  classical
  by_cases hj : K m ≤ j
  case neg =>
    have hj' : j < K m := Nat.lt_of_not_ge hj
    have hH : ¬ H m ≤ j := by have := first_le_height m; omega
    simp [row_zero _ _ _ _ _ _ hj', hj'.ne, hj, hH]
  let d := fun p => shift m (j+1) p
  let U := fun i p => hit + M*i + d p
  let W := fun i p => miss + M*i + d p
  let pool := fun i => ∑ p : Blocks.Path m,
    (Blocks.sign m p : ℝ) * ((poolCount P (U i p) : ℝ) - poolCount P (W i p))
  let free := fun i => ∑ p : Blocks.Path m,
    (Blocks.sign m p : ℝ) * ((freeCount M (U i p) : ℝ) - freeCount M (W i p))
  let E := fun i => ∑ p : Blocks.Path m, ((freeCount M (U i p) : ℝ) + freeCount M (W i p))
  let T := if H m ≤ j then 2 * (12 : ℝ)^m * (P.card : ℝ) else 0
  let main : ℝ := if j = K m then (P.card : ℝ) else 0
  have hdpos (p : Blocks.Path m) : 0 < d p := shift_pos _ _ _ (by omega)
  have split (i : ℕ) : row m M hit miss i j = (free i + pool i) / 2^(j+1) := by
    unfold row
    congr 1
    dsimp only [free, pool]
    rw [← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro p _
    rw [← mul_add, add_comm ((freeCount M (U i p) : ℝ) - freeCount M (W i p))]
    congr 1
    have h := omega_partition_diff P hF (u := U i p) (v := W i p)
      (by dsimp [U]; have := hdpos p; omega) (by dsimp [W]; have := hdpos p; omega)
      ((hcommon.add_right (M*i)).add_right (d p)) hp
    simpa only [← hM] using h
  have abs_free (i : ℕ) : |free i| ≤ E i := abs_signed_diff_le ..
  have abs_pool (i : ℕ) : |pool i - main| ≤ T := by
    by_cases hlate : H m ≤ j
    · have hne : j ≠ K m := by have := first_le_height m; omega
      simp only [main, if_neg hne, sub_zero, T, if_pos hlate]
      refine (abs_signed_diff_le m (fun p => poolCount P (U i p))
        (fun p => poolCount P (W i p))).trans ?_
      calc
        _ ≤ ∑ _p : Blocks.Path m, ((P.card : ℝ) + P.card) := by
          apply sum_le_sum
          intro p _
          exact_mod_cast Nat.add_le_add (poolCount_bound ..) (poolCount_bound ..)
        _ = _ := by simp [Blocks.card_path]; ring
    · have hdB (p : Blocks.Path m) : d p ≤ B m :=
        (shift_lt_bound m (j+1) p (by omega)).le
      have hhit (p : Blocks.Path m) : poolCount P (U i p) =
          if d p = special m then P.card else 0 :=
        poolCount_hit (fun q hq => hsel i q hq _ (hdB p))
      have hmiss (p : Blocks.Path m) : poolCount P (W i p) = 0 :=
        poolCount_miss (fun q hq => havoid i q hq _ (hdB p))
      have equal : pool i = main := by
        dsimp only [pool, main]
        simp only [hhit, hmiss, Nat.cast_ite, Nat.cast_zero, sub_zero]
        have h := signed_special m (j+1) (by omega) (P.card : ℝ)
        simpa only [zsmul_eq_mul, Nat.add_right_cancel_iff] using h
      simp [equal, T, hlate]
  have hcenter : (if j = K m then (P.card : ℝ) / 2^(K m+1) else 0) = main / 2^(j+1) := by
    by_cases heq : j = K m <;> simp [main, heq]
  have point (i : ℕ) : |row m M hit miss i j - main / 2^(j+1)| ≤
      (E i + T) / 2^(j+1) := by
    rw [split, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^(j+1))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [add_sub_assoc]
    exact (abs_add_le _ _).trans (add_le_add (abs_free i) (abs_pool i))
  have sum_free : ∑ i ∈ range M, E i ≤ 2 * (M : ℝ) * (12 : ℝ)^m * (A+j) := by
    calc
      _ = ∑ p : Blocks.Path m, ((∑ i ∈ range M, (freeCount M (U i p) : ℝ)) +
          ∑ i ∈ range M, (freeCount M (W i p) : ℝ)) := by
        dsimp only [E]
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib]
      _ ≤ ∑ _p : Blocks.Path m, ((M : ℝ) * (A+j) + M * (A+j)) :=
        sum_le_sum (fun p _ => add_le_add (hfreeHit p) (hfreeMiss p))
      _ = _ := by simp [Blocks.card_path]; ring
  rw [hcenter, if_pos hj]
  calc
    _ ≤ ∑ i ∈ range M, (E i + T) / 2^(j+1) := sum_le_sum (fun i _ => point i)
    _ = ((∑ i ∈ range M, E i) + M * T) / 2^(j+1) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp
    _ ≤ (2 * (M : ℝ) * (12 : ℝ)^m * (A+j) + M * T) / 2^(j+1) := by gcongr
    _ = _ := by
      by_cases hlate : H m ≤ j <;> simp [T, hlate, add_div]
      ring

end Erdos69Independent.AffineBlocks

end

section

/- 阶乘斜率、选择素数和中国剩余模数的定量控制。 -/

namespace Erdos69CRT

open Finset

/-- 截断范围和每个斜率都在这个统一高度之内。 -/
theorem cutoff_height (m : ℕ) :
    let V := 16 ^ m
    let K := 4 * m
    let L := (K + 2) * (V + 1)
    let H := (m + 1) ^ 2 + 4 * m + 1
    let D := (V + 1).factorial
    let B := 1 + D * K * V + (1 + D * (L + V)) * (H + 1)
    B + 1 ≤ 2 ^ (8 * (16 ^ (m + 1)) ^ 4) := by
  dsimp only
  let W := 16 ^ (m + 1)
  let V := 16 ^ m
  let K := 4 * m
  let L := (K + 2) * (V + 1)
  let H := (m + 1) ^ 2 + 4 * m + 1
  let D := (V + 1).factorial
  let T := 2 ^ (W ^ 4)
  change 1 + D * K * V + (1 + D * (L + V)) * (H + 1) + 1 ≤ 2 ^ (8 * W ^ 4)
  have hW : 16 ≤ W := by
    dsimp [W]
    exact (Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ m+1))
  have hm : m + 1 ≤ W := (m+1).lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left (by decide : 2 ≤ 16) _)
  have hV : V ≤ W := Nat.pow_le_pow_right (by decide) (Nat.le_succ m)
  have hWsq : 6 * W ≤ W ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right W (show 6 ≤ W by omega)
  have hK2 : K + 2 ≤ W ^ 2 := by dsimp [K]; omega
  have hV1 : V + 1 ≤ W ^ 2 := by omega
  have hL : L ≤ W ^ 4 := by
    calc L ≤ W^2 * W^2 := Nat.mul_le_mul hK2 hV1
         _ = W^4 := by ring
  have hH : H ≤ W ^ 4 := by
    calc H ≤ (K+2)^2 := by dsimp [H,K]; nlinarith only [Nat.zero_le (m*m)]
         _ ≤ (W^2)^2 := Nat.pow_le_pow_left hK2 _
         _ = W^4 := by ring
  have hD : D ≤ T := by
    calc D ≤ (V+1)^(V+1) := Nat.factorial_le_pow _
         _ ≤ (2^(V+1))^(V+1) := Nat.pow_le_pow_left (V+1).lt_two_pow_self.le _
         _ = 2^((V+1)*(V+1)) := by rw [pow_mul]
         _ ≤ T := by
           apply Nat.pow_le_pow_right (by decide)
           calc (V+1)*(V+1) ≤ W^2 * W^2 := Nat.mul_le_mul hV1 hV1
                _ = W^4 := by ring
  have hWT : W^4 ≤ T := (W^4).lt_two_pow_self.le
  have h24 : W^2 ≤ W^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hKT : K ≤ T := (by omega : K ≤ W^2) |>.trans (h24.trans hWT)
  have hVT : V ≤ T := (by omega : V ≤ W^2) |>.trans (h24.trans hWT)
  have hT : 16 ≤ T := by omega
  calc
    _ ≤ 1 + T*T*T + (1+T*(T+T))*(T+1)+1 := by
      gcongr
      · exact hL.trans hWT
      · exact hH.trans hWT
    _ ≤ 16*T^3 := by nlinarith only [Nat.zero_le ((T-1)*(T-1)*(T-1)),
      Nat.mul_le_mul_right (T*T) (show 2 ≤ T by omega),
      Nat.mul_le_mul_right T (show 2 ≤ T by omega), hT]
    _ ≤ T^5 * T^3 := by
      apply Nat.mul_le_mul_right
      exact hT.trans (Nat.le_self_pow (by decide : 5 ≠ 0) T)
    _ = 2^(8*W^4) := by
      rw [← pow_add, Nat.add_comm 5 3, show 3 + 5 = 8 by decide]
      dsimp [T]
      rw [← pow_mul, Nat.mul_comm]

/-- 优先从大于 B+1 的素数中选取，左右两条进程共用同一个周期。
显式常数与 q 和 m 无关。 -/
theorem period_bound {ι : Type*} {s : Finset ι} {a : ι → ℕ} {V L B m : ℕ}
    {P : Finset ℕ} (hs : s.card ≤ 16 ^ m) (hP : P.card ≤ 16 ^ m)
    (ha : ∀ i ∈ s, factorialSlope V L (a i) ≤ B + 1)
    (hp : ∀ p ∈ P, p ≤ 2 ^ P.card * (B+1))
    (hb : B+1 ≤ 2 ^ (8 * (16 ^ (m+1)) ^ 4)) :
    squarePeriod s a V L * poolPeriod P ≤ 2 ^ (2 ^ (28 * (m+1))) := by
  let W := 16^(m+1)
  let E := 8 * W^4
  have hW : 16 ≤ W := Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ m+1)
  have hsW : s.card ≤ W := hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
  have hpW : P.card ≤ W := hP.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
  have hsquare : squarePeriod s a V L ≤ 2 ^ (2*E*s.card) := by
    calc squarePeriod s a V L ≤ ((2^E)^2)^s.card := by
           apply Finset.prod_le_pow_card
           exact fun i h => Nat.pow_le_pow_left ((ha i h).trans hb) _
         _ = 2 ^ (2*E*s.card) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have hpool : poolPeriod P ≤ 2 ^ ((P.card+E)*P.card) := by
    calc poolPeriod P ≤ (2^P.card * 2^E)^P.card := by
           apply Finset.prod_le_pow_card
           exact fun p h => (hp p h).trans (Nat.mul_le_mul_left _ hb)
         _ = 2^((P.card+E)*P.card) := by rw [← pow_add, pow_mul]
  calc
    _ ≤ 2^(2*E*s.card) * 2^((P.card+E)*P.card) := Nat.mul_le_mul hsquare hpool
    _ = 2^(2*E*s.card + (P.card+E)*P.card) := (pow_add ..).symm
    _ ≤ 2^(2^(28*(m+1))) := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      calc
        _ ≤ 2*E*W + (W+E)*W := by gcongr
        _ ≤ W^7 := by
          change 2*(8*W^4)*W + (W+8*W^4)*W ≤ W^7
          have hrad : 25 ≤ W*W := by nlinarith only [Nat.mul_le_mul hW hW]
          have hW2 : W^2 ≤ W^5 := Nat.pow_le_pow_right (by omega) (by decide)
          have hbig : 24 * W^5 + W^2 ≤ 25*W^5 := by omega
          nlinarith only [Nat.mul_le_mul_right (W^5) hrad, hbig]
        _ = 2^(28*(m+1)) := by
          dsimp [W]
          rw [show (16:ℕ) = 2^4 by decide, ← pow_mul, ← pow_mul]
          congr 1
          ring

end Erdos69CRT

end

section

/- 给定深度和素数个数，落实十二项仿射分块的两条等差数列。 -/

namespace Erdos69Independent.AffineBlocks

open Finset

def basePeriod (m : ℕ) : ℕ := ∏ p : Blocks.Path m, a m p ^ 2

def period (m : ℕ) (P : Finset ℕ) : ℕ := basePeriod m * Erdos69CRT.poolPeriod P

theorem basePeriod_pos (m : ℕ) : 0 < basePeriod m := prod_pos fun p _ => pow_pos (a_pos m p) _

private theorem slope_eq_a (m : ℕ) (p : Blocks.Path m) :
    Erdos69CRT.factorialSlope (V m) (L m) (Blocks.slope m p) = a m p := by
  simp only [Erdos69CRT.factorialSlope, a, D, Nat.mul_comm (L m + Blocks.slope m p)]

private theorem squarePeriod_eq (m : ℕ) :
    Erdos69CRT.squarePeriod univ (Blocks.slope m) (V m) (L m) = basePeriod m := by
  simp only [Erdos69CRT.squarePeriod, basePeriod, slope_eq_a]

/-- 除素数池 P 本身之外，包含每个周期点可直接使用的整除与同余数据。 -/
structure CRTPair (m k : ℕ) where
  P : Finset ℕ
  card_P : P.card = k
  primes : ∀ p ∈ P, p.Prime ∧ B m + 1 < p
  hit : ℕ
  miss : ℕ
  hit_lt : hit < period m P
  miss_lt : miss < period m P
  period_le : period m P ≤ 2 ^ (2 ^ (28 * (m + 1)))
  common : hit ≡ miss [MOD basePeriod m]
  square_hit : ∀ j p, a m p ^ 2 ∣ hit + period m P * j + c m p
  square_miss : ∀ j p, a m p ^ 2 ∣ miss + period m P * j + c m p
  selected_hit : ∀ j p, p ∈ P → ∀ d ≤ B m,
    p ∣ hit + period m P * j + d ↔ d = special m
  selected_miss : ∀ j p, p ∈ P → ∀ d ≤ B m, ¬p ∣ miss + period m P * j + d

theorem concrete_pair (m k : ℕ) (hk : k ≤ 16 ^ m) : Nonempty (CRTPair m k) := by
  classical
  obtain ⟨P, hcard, hp⟩ := Erdos69CRT.bounded_prime_pool (B m + 1) (by omega) k
  have hPrime := fun p h => (hp p h).1
  have hlarge := fun p h => (hp p h).2.1
  have hsmall : ∀ p ∈ P, p ≤ 2 ^ P.card * (B m + 1) := by
    simpa only [hcard] using fun p h => (hp p h).2.2
  have ha (i : Blocks.Path m) :
      Erdos69CRT.factorialSlope (V m) (L m) (Blocks.slope m i) ≤ B m + 1 := by
    rw [slope_eq_a]
    exact (a_lt_bound m i).le.trans (Nat.le_succ _)
  have hperm : period m P ≤ 2 ^ (2 ^ (28 * (m + 1))) := by
    rw [period, ← squarePeriod_eq]
    apply Erdos69CRT.period_bound (m := m) ?_ (hcard ▸ hk) (fun i _ => ha i) hsmall
      (Erdos69CRT.cutoff_height m)
    · simpa [Blocks.card_path] using Nat.pow_le_pow_left (by decide : 12 ≤ 16) m
  obtain ⟨R⟩ := Erdos69CRT.controlled_pair univ (Blocks.slope m) (c m) (V m) (L m)
    (fun i _ => (Blocks.slope_lt m i).le)
    (fun _ _ _ _ h => Blocks.slope_injective m h) P (special m) (B m)
    (special_lt_bound m).le (fun p h => ⟨hPrime p h, hlarge p h⟩)
    (fun p h i _ => (ha i).trans_lt (hlarge p h))
  refine ⟨⟨P, hcard, fun p h => ⟨hPrime p h, hlarge p h⟩, R.hit, R.miss,
    ?_, ?_, hperm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [period, squarePeriod_eq] using R.hit_lt
  · simpa only [period, squarePeriod_eq] using R.miss_lt
  · simpa only [squarePeriod_eq] using R.common
  · intro j p
    simpa only [period, squarePeriod_eq, slope_eq_a] using R.square_hit j p (mem_univ p)
  · intro j p
    simpa only [period, squarePeriod_eq, slope_eq_a] using R.square_miss j p (mem_univ p)
  · simpa only [period, squarePeriod_eq] using R.selected_hit
  · simpa only [period, squarePeriod_eq] using R.selected_miss

theorem CRTPair.period_pos {m k : ℕ} (R : CRTPair m k) : 0 < period m R.P :=
  Nat.zero_lt_of_lt R.hit_lt

theorem CRTPair.bound_lt_period {m k : ℕ} (R : CRTPair m k) (hk : 0 < k) :
    B m < period m R.P := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (R.card_P ▸ hk)
  have hG : 0 < Erdos69CRT.poolPeriod R.P := prod_pos (fun q h => (R.primes q h).1.pos)
  have hdiv : p ∣ Erdos69CRT.poolPeriod R.P := Finset.dvd_prod_of_mem id hp
  exact ((Nat.lt_succ_self _).trans (R.primes p hp).2).trans_le
    ((Nat.le_of_dvd hG hdiv).trans (Nat.le_mul_of_pos_left _ (basePeriod_pos m)))

theorem CRTPair.square_dvd_period {m k : ℕ} (R : CRTPair m k) (p : Blocks.Path m) :
    (a m p) ^ 2 ∣ period m R.P :=
  (Finset.dvd_prod_of_mem (fun i => (a m i)^2) (mem_univ p)).trans (Nat.dvd_mul_right _ _)

end Erdos69Independent.AffineBlocks

end

section

/- Erdős 第 69 题：有理数假设给出的移位尾和整性（论文式 5.1）。 -/

open scoped ArithmeticFunction.omega

namespace Erdos69Independent

noncomputable def tail (n : ℕ) : ℝ :=
  ∑' j : ℕ, (ω (n + j + 1) : ℝ) / 2 ^ (j + 1)

private lemma tail_scale (n : ℕ) :
    tail n = 2 ^ n * ∑' j : ℕ, (ω (j + (n + 1)) : ℝ) / 2 ^ (j + (n + 1)) := by
  rw [tail, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [show j + (n + 1) = n + j + 1 by omega,
    show n + j + 1 = n + (j + 1) by omega, pow_add]
  field_simp
  rw [pow_add, pow_succ]
  ring

-- 每移动一位，尾和翻倍，并扣掉刚刚越过的整数项。
theorem tail_step (n : ℕ) : tail (n + 1) = 2 * tail n - ω (n + 1) := by
  let f (k : ℕ) : ℝ := (ω k : ℝ) / 2 ^ k
  have hs : Summable f := ArithmeticFunction.summable_cardDistinctFactors_div_two_pow
  have split := ((summable_nat_add_iff (n + 1)).2 hs).sum_add_tsum_nat_add 1
  have hs' : f (n + 1) + (∑' j : ℕ, f (j + (n + 2))) = ∑' j : ℕ, f (j + (n+1)) := by
    simpa only [Finset.sum_range_one, zero_add,
      show ∀ j : ℕ, j + 1 + (n+1) = j + (n+2) by omega] using split
  rw [tail_scale, tail_scale]
  change 2 ^ (n + 1) * _ = 2 * (2 ^ n * ∑' j : ℕ, f (j + (n + 1))) - _
  rw [← hs']
  dsimp [f]
  rw [pow_succ]
  field_simp
  ring

theorem rational_tails
    (h : ¬ Irrational (∑' k : ℕ, (ω (k + 2) : ℝ) / 2 ^ (k + 2))) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ, ∃ z : ℤ, (q : ℝ) * tail n = z := by
  obtain ⟨a, ha⟩ := not_not.mp h
  have hs : Summable (fun k : ℕ => (ω k : ℝ) / 2 ^ k) :=
    ArithmeticFunction.summable_cardDistinctFactors_div_two_pow
  have h0 : tail 0 = (a : ℝ) := by
    rw [tail_scale, pow_zero, one_mul, ha]
    have h1 := hs.sum_add_tsum_nat_add 1
    have h2 := hs.sum_add_tsum_nat_add 2
    simp [Finset.sum_range_succ] at h1 h2
    exact h1.trans h2.symm
  refine ⟨a.den, a.den_pos, ?_⟩
  intro n
  induction n with
  | zero =>
    refine ⟨a.num, ?_⟩
    rw [h0, Rat.cast_def]
    field_simp
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨2 * z - (a.den : ℤ) * ω (n + 1), ?_⟩
    rw [tail_step]
    push_cast
    linarith only [hz]

end Erdos69Independent

end

section

/- 平方同余条件下，两个复合斜率级数之差具有统一的分母。 -/

open scoped ArithmeticFunction.omega

namespace Erdos69Independent

theorem tail_summable (u : ℕ) :
    Summable (fun j : ℕ => (ω (u+j+1) : ℝ) / 2^(j+1)) := by
  have hs := ((summable_nat_add_iff (u+1)).mpr
    ArithmeticFunction.summable_cardDistinctFactors_div_two_pow).mul_left ((2:ℝ)^u)
  apply hs.congr
  intro j
  rw [show j + (u+1) = u + (j+1) by omega, pow_add, Nat.add_assoc]
  field_simp

-- 两个起点同时被斜率整除时，乘斜率带来的重复质因子逐项抵消。
theorem omega_mul_diff (a u v h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hu : a ∣ u) (hv : a ∣ v) :
    ω (a*(u+h)) + ω (v+h) = ω (a*(v+h)) + ω (u+h) := by
  have hu' : u+h ≠ 0 := by omega
  have hv' : v+h ≠ 0 := by omega
  have hi : a.primeFactors ∩ (u+h).primeFactors = a.primeFactors ∩ (v+h).primeFactors := by
    ext p
    simp only [Finset.mem_inter, Nat.mem_primeFactors, hu', hv', ne_eq, not_false_eq_true,
      and_true]
    constructor
    · rintro ⟨hp, hpu, hdu⟩
      exact ⟨hp, hpu, dvd_add (hp.2.1.trans hv)
        ((Nat.dvd_add_right (hp.2.1.trans hu)).mp hdu)⟩
    · rintro ⟨hp, hpv, hdv⟩
      exact ⟨hp, hpv, dvd_add (hp.2.1.trans hu)
        ((Nat.dvd_add_right (hp.2.1.trans hv)).mp hdv)⟩
  change (a*(u+h)).primeFactors.card + (v+h).primeFactors.card =
    (a*(v+h)).primeFactors.card + (u+h).primeFactors.card
  rw [Nat.primeFactors_mul ha.ne' hu', Nat.primeFactors_mul ha.ne' hv']
  have x := Finset.card_union_add_card_inter a.primeFactors (u+h).primeFactors
  have y := Finset.card_union_add_card_inter a.primeFactors (v+h).primeFactors
  rw [hi] at x
  omega

noncomputable def diffTerm (n n' c a j : ℕ) : ℝ :=
  ((ω (n+c+a*(j+1)) : ℝ) - ω (n'+c+a*(j+1))) / 2^(j+1)

theorem composite_tail_diff {a n n' c : ℕ} (ha : 0<a)
    (hn : a^2 ∣ n+c) (hn' : a^2 ∣ n'+c) :
    Summable (diffTerm n n' c a) ∧
      ∑' j, diffTerm n n' c a j = tail ((n+c)/a) - tail ((n'+c)/a) := by
  obtain ⟨x,hx⟩ := hn
  obtain ⟨y,hy⟩ := hn'
  have hux : (n+c)/a = a*x := by rw [hx, pow_two, Nat.mul_assoc, Nat.mul_div_cancel_left _ ha]
  have huy : (n'+c)/a = a*y := by rw [hy, pow_two, Nat.mul_assoc, Nat.mul_div_cancel_left _ ha]
  have he (j : ℕ) : diffTerm n n' c a j =
      (ω (a*x+j+1) : ℝ)/2^(j+1) - (ω (a*y+j+1) : ℝ)/2^(j+1) := by
    rw [diffTerm, hx, hy, ← sub_div]
    congr 1
    have ht := omega_mul_diff a (a*x) (a*y) (j+1) ha (by omega) (dvd_mul_right ..)
      (dvd_mul_right ..)
    simp only [← Nat.add_assoc, Nat.mul_add, ← Nat.mul_assoc, ← pow_two] at ht
    rw [show a^2*x+a*(j+1) = a*(a*x+(j+1)) by ring,
      show a^2*y+a*(j+1) = a*(a*y+(j+1)) by ring, ← Nat.add_assoc, ← Nat.add_assoc]
    apply sub_eq_sub_iff_add_eq_add.mpr
    rw [add_comm (ω (a*x+j+1) : ℝ)]
    exact_mod_cast (by simpa only [Nat.mul_add, ← Nat.mul_assoc, ← pow_two] using ht :
      ω (a*(a*x+j+1)) + ω (a*y+j+1) = ω (a*(a*y+j+1)) + ω (a*x+j+1))
  refine ⟨((tail_summable (a*x)).sub (tail_summable (a*y))).congr (fun j => (he j).symm), ?_⟩
  rw [tsum_congr he, (tail_summable (a*x)).tsum_sub (tail_summable (a*y)), hux, huy]
  rfl

theorem dyadic_integer {q : ℕ} (hq : ∀ n, ∃ z : ℤ, (q:ℝ)*tail n=z)
    {a n n' c : ℕ} (ha : 0<a) (hn : a^2 ∣ n+c) (hn' : a^2 ∣ n'+c) :
    ∃ z : ℤ, (q:ℝ)*(∑' j, diffTerm n n' c a j) = z := by
  obtain ⟨x,hx⟩ := hq ((n+c)/a)
  obtain ⟨y,hy⟩ := hq ((n'+c)/a)
  exact ⟨x-y, by rw [(composite_tail_diff ha hn hn').2, mul_sub, hx, hy, Int.cast_sub]⟩

end Erdos69Independent

end

section

/- 平方同余条件使每一条仿射式的两点差都落在同一分母的整数格上。
有限个带符号的斜率求和后仍在该整数格上。 -/

namespace Erdos69Independent.AffineBlocks

open Finset

theorem row_integer {m k q : ℕ} (R : CRTPair m k)
    (hq : ∀ n, ∃ z : ℤ, (q : ℝ) * tail n = z) (i : ℕ) :
    Summable (row m (period m R.P) R.hit R.miss i) ∧
      ∃ z : ℤ, (q : ℝ) * (∑' j, row m (period m R.P) R.hit R.miss i j) = z := by
  classical
  let n := R.hit + period m R.P * i
  let n' := R.miss + period m R.P * i
  let f := fun p : Blocks.Path m => diffTerm n n' (c m p) (a m p)
  have heq (j : ℕ) : row m (period m R.P) R.hit R.miss i j =
      ∑ p : Blocks.Path m, (Blocks.sign m p : ℝ) * f p j := by
    unfold row
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro p _
    simp only [f, diffTerm, n, n', shift, mul_div_assoc, Nat.add_comm (a m p * (j+1)) (c m p),
      Nat.add_assoc]
  have hs (p : Blocks.Path m) : Summable (fun j => (Blocks.sign m p : ℝ) * f p j) :=
    (composite_tail_diff (a_pos m p) (R.square_hit i p) (R.square_miss i p)).1.mul_left _
  have hz (p : Blocks.Path m) : ∃ z : ℤ, (q : ℝ) * (∑' j, f p j) = z :=
    dyadic_integer hq (a_pos m p) (R.square_hit i p) (R.square_miss i p)
  choose z hz using hz
  refine ⟨(summable_sum (s := univ) (fun p _ => hs p)).congr (fun j => (heq j).symm),
    ∑ p : Blocks.Path m, Blocks.sign m p * z p, ?_⟩
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun p _ => hs p), Finset.mul_sum]
  push_cast
  apply sum_congr rfl
  intro p _
  rw [tsum_mul_left, ← hz p]
  ring

end Erdos69Independent.AffineBlocks

end

section

/- 分母给定后，选择消元块数和强制素数数目，使误差小于四分之一。 -/

open Filter Topology

namespace Erdos69Independent.AffineBlocks

noncomputable def envelope (m : ℕ) : ℝ := 200*((m:ℝ)+1)

private theorem block_mass (m : ℕ) :
    (12:ℝ)^m/2^(K m) = (3/4:ℝ)^m := by
  rw [K, pow_mul, ← div_pow]
  norm_num

private theorem horizon_large (m : ℕ) : 2*(K m) ≤ H m := by
  unfold K H
  cases m with
  | zero => decide
  | succ m => nlinarith

private theorem envelope_bound (m k : ℕ) (hk : k ≤ 16^m) :
    2*(12:ℝ)^m*((envelope m + K m + 1)/2^(K m) + (k:ℝ)/2^(H m)) ≤
      500*((m:ℝ)+1)*(3/4:ℝ)^m := by
  have he : (k:ℝ) ≤ (2:ℝ)^(K m) := by
    rw [K, pow_mul]
    norm_num
    exact_mod_cast hk
  have hd : (2:ℝ)^(K m)*(2:ℝ)^(K m) ≤ 2^(H m) := by
    rw [← pow_add, ← two_mul]
    exact pow_le_pow_right₀ (by norm_num) (horizon_large m)
  have hp : 0 < (2:ℝ)^(K m) := by positivity
  have ht : (k:ℝ)/2^(H m) ≤ 1/(2:ℝ)^(K m) := by
    apply (div_le_div_iff₀ (by positivity) hp).mpr
    simpa using (mul_le_mul_of_nonneg_right he hp.le).trans hd
  calc
    _ ≤ 2*(12:ℝ)^m*((envelope m + K m + 1)/2^(K m) + 1/2^(K m)) := by gcongr
    _ = 2*(envelope m + K m + 2)*((12:ℝ)^m / 2^(K m)) := by ring
    _ ≤ _ := by
      rw [block_mass]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simp only [envelope, K, Nat.cast_mul, Nat.cast_ofNat]
      linarith [Nat.cast_nonneg (α := ℝ) m]

theorem choose_blocks (q : ℕ) (hq : 0<q) :
    ∃ m k : ℕ, 0<k ∧ k≤16^m ∧
      1/4 < (q:ℝ)*((k:ℝ)/2^(K m+1)) ∧
      (q:ℝ)*((k:ℝ)/2^(K m+1)) ≤ 1/2 ∧
      (q:ℝ)*(2*(12:ℝ)^m*((envelope m + K m + 1)/2^(K m) + (k:ℝ)/2^(H m))) < 1/4 := by
  have ht₁ := tendsto_self_mul_const_pow_of_lt_one (r := (3/4:ℝ)) (by norm_num) (by norm_num)
  have ht₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3/4:ℝ)) (by norm_num) (by norm_num)
  have ht : Tendsto (fun m : ℕ => (q:ℝ)*(500*((m:ℝ)+1)*(3/4)^m)) atTop (𝓝 0) := by
    convert ((ht₁.add ht₂).const_mul ((q:ℝ)*500)) using 1
    · ext m
      ring
    · ring
  have hev := ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/4)
  obtain ⟨m, hsize, herr⟩ := ((eventually_ge_atTop (2*q)).and hev).exists
  have hbig : 2*q ≤ 16^m :=
    hsize.trans (m.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide) m))
  let k := 16^m / q
  have hpos : 0<k := Nat.div_pos (by omega) hq
  have hup : k≤16^m := Nat.div_le_self .. 
  have hmod := Nat.mod_lt (16^m) hq
  have hdiv : 16^m % q + q*k = 16^m := Nat.mod_add_div .. 
  have hlow : 16^m < 2*(q*k) := by omega
  have hhigh : q*k ≤ 16^m := by omega
  have hd : (2:ℝ)^(K m+1) = (16:ℝ)^m * 2 := by rw [pow_succ, K, pow_mul]; norm_num
  refine ⟨m,k,hpos,hup,?_,?_,(mul_le_mul_of_nonneg_left (envelope_bound m k hup)
    (Nat.cast_nonneg q)).trans_lt herr⟩
  · rw [hd, ← mul_div_assoc]
    apply (lt_div_iff₀ (by positivity)).mpr
    have hc : (16:ℝ)^m < 2*((q:ℝ)*k) := by exact_mod_cast hlow
    linarith
  · rw [hd, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    have hc : (q:ℝ)*k ≤ (16:ℝ)^m := by exact_mod_cast hhigh
    linarith

end Erdos69Independent.AffineBlocks

end

section

open Finset Real

namespace Erdos69Independent

/-- 二进区间内的质数倒数之和，由切比雪夫函数控制。 -/
theorem dyadic_prime_reciprocal_sum_le (k : ℕ) (hk : 0 < k) :
    ∑ p ∈ Nat.primesLE (2^(k+1)) \ Nat.primesLE (2^k), (1 : ℝ) / p ≤ 4 / k := by
  let D := Nat.primesLE (2^(k+1)) \ Nat.primesLE (2^k)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ)^k := by positivity
  have hpoint (p : ℕ) (hp : p ∈ D) :
      (1 : ℝ) / p * ((2:ℝ)^k * (k * log 2)) ≤ log p := by
    obtain ⟨hp', hn⟩ := mem_sdiff.mp hp
    have hlt : 2^k < p := by
      by_contra! h
      exact hn (Nat.mem_primesLE.mpr ⟨h, Nat.prime_of_mem_primesLE hp'⟩)
    have hlt' : (2 : ℝ)^k ≤ p := by exact_mod_cast hlt.le
    have hpos : 0 < (p : ℝ) := hpow.trans_le hlt'
    have hfrac : (2 : ℝ)^k / p ≤ 1 := (div_le_one hpos).mpr hlt'
    have hlog' := Real.log_le_log hpow hlt'
    rw [Real.log_pow] at hlog'
    calc
      _ = ((2:ℝ)^k / p) * (k * log 2) := by ring
      _ ≤ 1 * (k * log 2) := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ ≤ _ := by simpa using hlog'
  have hθ : (∑ p ∈ D, (1:ℝ) / p) * ((2:ℝ)^k * (k * log 2)) ≤
      log 4 * (2:ℝ)^(k+1) := by
    calc
      _ = ∑ p ∈ D, (1:ℝ) / p * ((2:ℝ)^k * (k * log 2)) := sum_mul ..
      _ ≤ ∑ p ∈ D, log p := sum_le_sum hpoint
      _ ≤ ∑ p ∈ Nat.primesLE (2^(k+1)), log p := by
        refine sum_le_sum_of_subset_of_nonneg sdiff_subset ?_
        intro p hp _
        exact log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ = Chebyshev.theta ((2^(k+1) : ℕ) : ℝ) :=
        (Chebyshev.theta_eq_sum_primesLE_log _).symm
      _ ≤ _ := by
        simpa using Chebyshev.theta_le_log4_mul_x
          (x := ((2^(k+1) : ℕ) : ℝ)) (by positivity)
  have h4 : log 4 = 2 * log 2 := by
    calc
      log 4 = log ((2 : ℝ)^2) := by norm_num
      _ = _ := by rw [log_pow]; norm_num
  rw [h4, pow_succ] at hθ
  apply (le_div_iff₀ hk').2
  apply (le_of_mul_le_mul_right ?_ (show 0 < (2:ℝ)^k * log 2 by positivity))
  change (∑ p ∈ D, (1:ℝ) / p) * k * ((2:ℝ)^k * log 2) ≤ _
  convert hθ using 1 <;> ring

/-- 所有不超过 2^(K+1) 的质数之倒数和，有显式的调和数界。 -/
theorem prime_reciprocal_sum_pow_le (K : ℕ) :
    (∑ p ∈ Nat.primesLE (2^(K+1)), (1 : ℝ) / p) ≤ 1 / 2 + 4 * (harmonic K : ℝ) := by
  induction K with
  | zero =>
    have htwo : Nat.primesLE 2 = {2} := by decide
    norm_num [htwo]
  | succ K ih =>
    let A := Nat.primesLE (2^(K+1))
    let B := Nat.primesLE (2^(K+1+1))
    have hsub : A ⊆ B := Nat.primesLE_mono (Nat.pow_le_pow_right (by decide) (by omega))
    have hsplit := sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
    have hdy := dyadic_prime_reciprocal_sum_le (K+1) (by omega)
    rw [harmonic_succ]
    push_cast
    change (∑ p ∈ B, (1 : ℝ) / p) ≤ _
    change (∑ p ∈ B \ A, (1 : ℝ) / p) ≤ _ at hdy
    change (∑ p ∈ A, (1 : ℝ) / p) ≤ _ at ih
    rw [← hsplit]
    apply (add_le_add hdy ih).trans
    apply le_of_eq
    push_cast
    ring

/-- 任意上限下的显式双对数界，在 M = 0,1 处同样适用。 -/
theorem prime_reciprocal_sum_le (M : ℕ) :
    (∑ p ∈ Nat.primesLE M, (1 : ℝ) / p) ≤
      1 / 2 + 4 * (1 + Real.log (Nat.log 2 M)) := by
  have hM := (Nat.lt_pow_succ_log_self (b := 2) (by decide) M).le
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (2^(Nat.log 2 M + 1)), (1 : ℝ) / p :=
      sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hM) (fun _ _ _ => by positivity)
    _ ≤ _ := (prime_reciprocal_sum_pow_le _).trans (by linarith [harmonic_le_one_add_log (Nat.log 2 M)])

end Erdos69Independent

end

section

open Finset

namespace Erdos69Independent

/-- 互素步长同余类在长度 N 的样本中至多出现 ⌊N/p⌋+1 次。 -/
theorem progression_prime_hits_le (p b D N : ℕ) (hD : p.Coprime D) :
    ((range N).filter (fun i => p ∣ b + D*i)).card ≤ N / p + 1 := by
  let S := (range N).filter (fun i => p ∣ b + D*i)
  have hm : Set.MapsTo (fun i : ℕ => i / p) S (range (N / p + 1)) := by
    intro i hi
    have hlt := mem_range.mp (mem_filter.mp hi).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hlt.le))
  have hinj : Set.InjOn (fun i : ℕ => i / p) S := by
    intro i hi j hj he
    have hi0 := Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hi).2
    have hj0 := Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hj).2
    have hmul := Nat.ModEq.add_left_cancel' b (hi0.trans hj0.symm)
    have hmod := Nat.ModEq.cancel_left_of_coprime hD hmul
    change i % p = j % p at hmod
    change i / p = j / p at he
    rw [← Nat.mod_add_div i p, ← Nat.mod_add_div j p, hmod, he]
  simpa only [card_range] using card_le_card_of_injOn _ hm hinj

/-- 大于 M 的不同质数各至少贡献因子 M+1。 -/
theorem large_prime_factors_card_le {M n C : ℕ} (hM : 0 < M) (hn : 0 < n)
    (hsize : n ≤ (M+1)^C) :
    (n.primeFactors.filter (M < ·)).card ≤ C := by
  let S := n.primeFactors.filter (M < ·)
  have hprod : (∏ p ∈ S, p) ∣ n :=
    (prod_dvd_prod_of_subset S n.primeFactors id (filter_subset _ _)).trans n.prod_primeFactors_dvd
  have hpow : (M+1)^S.card ≤ ∏ p ∈ S, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' (fun p hp => Nat.succ_le_of_lt (mem_filter.mp hp).2)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < M+1)).mp
    (hpow.trans ((Nat.le_of_dvd hn hprod).trans hsize))

/-- 只计不整除步长的不同质数。 -/
def outsidePrimeCount (M n : ℕ) : ℕ := (n.primeFactors.filter (fun p => ¬ p ∣ M)).card

-- 小质数指示函数的求和形式，方便交换质数与样本两个指标。
private theorem outsidePrimeCount_le {M n C : ℕ} (hM : 0 < M) (hn : 0 < n)
    (hsize : n ≤ (M+1)^C) :
    (outsidePrimeCount M n : ℝ) ≤
      (∑ p ∈ (Nat.primesLE M).filter (fun p => ¬ p ∣ M),
        if p ∣ n then (1 : ℝ) else 0) + C := by
  let S := n.primeFactors.filter (fun p => ¬ p ∣ M)
  let P := (Nat.primesLE M).filter (fun p => ¬ p ∣ M)
  have hsplit := card_filter_add_card_filter_not (fun p : ℕ => p ≤ M) (s := S)
  have hsmall : S.filter (· ≤ M) = P.filter (· ∣ n) := by
    ext p
    simp only [S, P, mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hp, hd, _⟩, hnd⟩, hle⟩
      exact ⟨⟨⟨hle, hp⟩, hnd⟩, hd⟩
    · rintro ⟨⟨⟨hle, hp⟩, hnd⟩, hd⟩
      exact ⟨⟨⟨hp, hd, hn.ne'⟩, hnd⟩, hle⟩
  have hlarge : S.filter (fun p => ¬ p ≤ M) ⊆ n.primeFactors.filter (M < ·) := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1, Nat.lt_of_not_ge (mem_filter.mp hp).2⟩
  have hbound := (card_le_card hlarge).trans (large_prime_factors_card_le hM hn hsize)
  have hnat : outsidePrimeCount M n ≤ (P.filter (· ∣ n)).card + C := by
    change S.card ≤ _
    rw [← hsplit, hsmall]
    omega
  simpa only [P, Nat.cast_add, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero] using (show (outsidePrimeCount M n : ℝ) ≤ ((P.filter (· ∣ n)).card + C : ℕ) by exact_mod_cast hnat)

/-- 等差数列上非步长质因子数的一阶矩。上界与首项无关。 -/
theorem outsidePrimeCount_first_moment {M b C : ℕ} (hM : 0 < M)
    (hn : ∀ i ∈ range M, 0 < b + M*i)
    (hsize : ∀ i ∈ range M, b + M*i ≤ (M+1)^C) :
    (∑ i ∈ range M, (outsidePrimeCount M (b+M*i) : ℝ)) ≤
      M * (1 + C + ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p) := by
  let P := (Nat.primesLE M).filter (fun p => ¬ p ∣ M)
  have hsmall (p : ℕ) (hp : p ∈ P) :
      (∑ i ∈ range M, if p ∣ b+M*i then (1:ℝ) else 0) ≤ (M:ℝ) / p + 1 := by
    have hp' := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
    have hit := progression_prime_hits_le p b M M (hp'.coprime_iff_not_dvd.mpr (mem_filter.mp hp).2)
    have hit' : (↑((range M).filter (fun i => p ∣ b + M*i)).card : ℝ) ≤ (↑(M / p) : ℝ) + 1 := by
      exact_mod_cast hit
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hit'
    exact hit'.trans (by linarith [Nat.cast_div_le (α := ℝ) (m := M) (n := p)])
  have hcard : P.card ≤ M := by
    apply (Finset.card_le_card (show P ⊆ Icc 1 M by
      intro p hp
      have hp' := (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp').one_le, Nat.le_of_mem_primesLE hp'⟩)).trans
    simp
  have hpr : (∑ p ∈ P, (1:ℝ) / p) ≤ ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ i ∈ range M, ((∑ p ∈ P, if p ∣ b+M*i then (1:ℝ) else 0) + C) :=
      sum_le_sum (fun i hi => outsidePrimeCount_le hM (hn i hi) (hsize i hi))
    _ = (∑ p ∈ P, ∑ i ∈ range M, if p ∣ b+M*i then (1:ℝ) else 0) + M*C := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp
    _ ≤ (∑ p ∈ P, ((M:ℝ) / p + 1)) + M*C := add_le_add (sum_le_sum hsmall) le_rfl
    _ = M * (∑ p ∈ P, (1:ℝ) / p) + P.card + M*C := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp [div_eq_mul_inv]
    _ ≤ _ := by
      have hcard' : (P.card : ℝ) ≤ M := by exact_mod_cast hcard
      nlinarith [mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg M : 0 ≤ (M:ℝ))]

/-- 对步长以外的质因子数取平均，显式余项只有双对数量级。 -/
theorem outsidePrimeCount_average_le {M b C : ℕ} (hM : 0 < M)
    (hn : ∀ i ∈ range M, 0 < b + M*i)
    (hsize : ∀ i ∈ range M, b + M*i ≤ (M+1)^C) :
    (∑ i ∈ range M, (outsidePrimeCount M (b+M*i) : ℝ)) / M ≤
      1 + C + (1/2 + 4 * (1 + Real.log (Nat.log 2 M))) := by
  apply (div_le_iff₀ (show 0 < (M:ℝ) by exact_mod_cast hM)).mpr
  rw [mul_comm]
  refine (outsidePrimeCount_first_moment hM hn hsize).trans ?_
  gcongr
  exact prime_reciprocal_sum_le M

/-- 样本大小随位移 h 线性增长时，右侧只额外增加 h。 -/
theorem outsidePrimeCount_average_shift_le {M b h d : ℕ} (hM : 0 < M)
    (hn : ∀ i ∈ range M, 0 < b + M*i)
    (hsize : ∀ i ∈ range M, b + M*i ≤ (M+1)^d * (h+1)) :
    (∑ i ∈ range M, (outsidePrimeCount M (b+M*i) : ℝ)) / M ≤
      1 + ((d+h : ℕ) : ℝ) + (1/2 + 4 * (1 + Real.log (Nat.log 2 M))) := by
  refine outsidePrimeCount_average_le hM hn (fun i hi => (hsize i hi).trans ?_)
  rw [pow_add]
  apply Nat.mul_le_mul_left
  exact (Nat.succ_le_of_lt h.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega : 2 ≤ M+1) h)

end Erdos69Independent

end

section

open Finset

namespace Erdos69Independent

/-- 显式双指数周期上界转为余质因子平均值的线性误差。 -/
theorem log_natLog_le_of_le_double_pow {M T : ℕ} (h : M ≤ 2^(2^T)) :
    Real.log (Nat.log 2 M) ≤ T := by
  have hl := Nat.log_mono_right (b := 2) h
  rw [Nat.log_pow (by decide)] at hl
  rcases Nat.eq_zero_or_pos (Nat.log 2 M) with hz | hp
  · simp [hz]
  have h' : (Nat.log 2 M : ℝ) ≤ (2:ℝ)^T := by exact_mod_cast hl
  have hp' : 0 < (Nat.log 2 M : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ Real.log ((2:ℝ)^T) := Real.log_le_log hp' h'
    _ = T * Real.log 2 := Real.log_pow ..
    _ ≤ T * 1 := mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos (x := 2) (by norm_num)]) (by positivity)
    _ = _ := mul_one _

theorem outsidePrimeCount_average_linear {M b h d T : ℕ} (hM : 0 < M)
    (hperiod : M ≤ 2^(2^T))
    (hn : ∀ i ∈ range M, 0 < b + M*i)
    (hsize : ∀ i ∈ range M, b + M*i ≤ (M+1)^d * (h+1)) :
    (∑ i ∈ range M, (outsidePrimeCount M (b+M*i) : ℝ)) / M ≤
      6 + d + h + 4*T := by
  have hp := outsidePrimeCount_average_shift_le hM hn hsize
  push_cast at hp
  linarith [log_natLog_le_of_le_double_pow hperiod]

/-- 等比尾权重作用于线性函数的精确总和。 -/
theorem linear_geometric_tail_hasSum (K : ℕ) (A : ℝ) :
    HasSum (fun j : ℕ => (A + (K+j+1 : ℕ)) / 2^(K+j+1)) ((A+K+2)/2^K) := by
  have hgeo : HasSum (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
    convert! hasSum_geometric_of_norm_lt_one (ξ := (1/2 : ℝ)) (by norm_num) using 1
    norm_num
  have hlin : HasSum (fun j : ℕ => (j:ℝ)*(1/2 : ℝ)^j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2 : ℝ)) (by norm_num) using 1
    norm_num
  have hs := ((hgeo.mul_left (A+K+1)).add hlin).mul_right (1/(2:ℝ)^(K+1))
  convert! hs using 1
  · ext j
    rw [show K+j+1 = K+1+j by omega, pow_add]
    push_cast
    rw [div_pow, one_pow]
    ring
  · rw [pow_succ]
    ring

end Erdos69Independent

end

section

/- 把一般等差数列的一阶矩估计应用到实际选定的两个同余类。 -/

open Finset

namespace Erdos69Independent.AffineBlocks

theorem sample_mean {m k : ℕ} (R : CRTPair m k) (hk : 0<k)
    (b : ℕ) (hb : b < period m R.P) (j : ℕ) (p : Blocks.Path m) :
    (∑ i ∈ range (period m R.P),
      (freeCount (period m R.P) (b + period m R.P * i + shift m (j+1) p) : ℝ)) ≤
        (period m R.P : ℝ) * (envelope m + j) := by
  let M := period m R.P
  let s := shift m (j+1) p
  have hM : 0<M := R.period_pos
  have hM' : 0 < (M:ℝ) := by exact_mod_cast hM
  have ha : a m p ≤ M := ((a_lt_bound m p).trans (R.bound_lt_period hk)).le
  have hc : c m p ≤ M := ((c_lt_bound m p).trans (R.bound_lt_period hk)).le
  have hs : 0<s := shift_pos _ _ _ (by omega)
  have hpos (i : ℕ) (_hi : i ∈ range M) : 0 < b+s+M*i := by omega
  have hsize (i : ℕ) (hi : i ∈ range M) : b+s+M*i ≤ (M+1)^2*((j+1)+1) := by
    have h₁ := Nat.mul_le_mul_right (j+1) ha
    have h₂ := Nat.mul_le_mul_left M (mem_range.mp hi).le
    have h₃ : b ≤ M := hb.le
    change b+(a m p*(j+1)+c m p)+M*i ≤ _
    calc
      _ ≤ M + (M*(j+1)+M) + M*M := by omega
      _ ≤ (M+1)^2*((j+1)+1) := by nlinarith
  have h := outsidePrimeCount_average_linear hM R.period_le hpos hsize
  have hraw := (div_le_iff₀ hM').mp h
  have hconst : (6:ℝ) + (2:ℕ) + ((j+1:ℕ):ℝ) + 4*((28*(m+1):ℕ):ℝ) ≤ envelope m + j := by
    simp only [envelope, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hbound := hraw.trans (mul_le_mul_of_nonneg_right hconst hM'.le)
  rw [mul_comm (envelope m + j)] at hbound
  simpa only [M, s, freeCount, outsidePrimeCount, Nat.add_right_comm b (shift m (j+1) p)]
    using hbound

end Erdos69Independent.AffineBlocks

end

section

open Finset

namespace Erdos69Independent

private theorem cutoff_linear_hasSum (K : ℕ) (A : ℝ) :
    HasSum (fun j : ℕ => if K ≤ j then (A+j)/2^(j+1) else 0) ((A+K+1)/2^K) := by
  apply (hasSum_nat_add_iff' K).mp
  have hz : (∑ i ∈ range K, if K ≤ i then (A+i)/2^(i+1) else 0) = 0 :=
    sum_eq_zero fun i hi => if_neg (Nat.not_le.mpr (mem_range.mp hi))
  rw [hz, sub_zero]
  convert! linear_geometric_tail_hasSum K (A-1) using 1
  · ext j
    rw [if_pos (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_comm j K]
    ring
  · ring

private theorem cutoff_geometric_hasSum (H : ℕ) :
    HasSum (fun j : ℕ => if H ≤ j then (1:ℝ)/2^(j+1) else 0) (1/2^H) := by
  apply (hasSum_nat_add_iff' H).mp
  have hz : (∑ i ∈ range H, if H ≤ i then (1:ℝ)/2^(i+1) else 0) = 0 :=
    sum_eq_zero fun i hi => if_neg (Nat.not_le.mpr (mem_range.mp hi))
  rw [hz, sub_zero]
  convert! (hasSum_geometric_two' 1).div_const ((2:ℝ)^H) using 1
  ext j
  simp only [Nat.le_add_left, if_true, pow_succ, pow_add]
  ring

/-- 利用逐深度的一阶矩，在有限样本中找到整条级数贴近指定中心的样本。 -/
theorem exists_close_of_weighted_row_bounds {M K H : ℕ} (hM : 0 < M)
    (W : ℕ → ℕ → ℝ) (t A S k : ℝ)
    (hs : ∀ i < M, Summable (W i))
    (hrow : ∀ j : ℕ, (∑ i ∈ range M, |W i j - (if j=K then t else 0)|) ≤
      (if K≤j then 2*(M:ℝ)*S*(A+j)/2^(j+1) else 0) +
      (if H≤j then 2*(M:ℝ)*S*k/2^(j+1) else 0)) :
    ∃ i < M, |(∑' j, W i j)-t| ≤ 2*S*((A+K+1)/2^K + k/2^H) := by
  let center (j : ℕ) : ℝ := if j = K then t else 0
  let err (i j : ℕ) := |W i j - center j|
  have hc : HasSum center t := hasSum_ite_eq K t
  have he (i : ℕ) (hi : i ∈ range M) : Summable (err i) :=
    ((hs i (mem_range.mp hi)).sub hc.summable).abs
  let C : ℝ := 2*M*S
  let bound (j : ℕ) := (if K≤j then C*(A+j)/2^(j+1) else 0) +
    (if H≤j then C*k/2^(j+1) else 0)
  have hb : HasSum bound (C*((A+K+1)/2^K+k/2^H)) := by
    convert! ((cutoff_linear_hasSum K A).mul_left C).add
      ((cutoff_geometric_hasSum H).mul_left (C*k)) using 1
    · ext j
      simp only [bound]
      split_ifs <;> ring
    · ring
  have htot : (∑ i ∈ range M, ∑' j, err i j) ≤ C*((A+K+1)/2^K+k/2^H) := by
    rw [← Summable.tsum_finsetSum he, ← hb.tsum_eq]
    exact Summable.tsum_le_tsum hrow (summable_sum he) hb.summable
  have htriangle (i : ℕ) (hi : i ∈ range M) : |(∑' j, W i j)-t| ≤ ∑' j, err i j := by
    have hdiff := (hs i (mem_range.mp hi)).tsum_sub hc.summable
    rw [hc.tsum_eq] at hdiff
    rw [← hdiff]
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun j => W i j - center j) (by simpa only [Real.norm_eq_abs] using he i hi))
  have hsum : (∑ i ∈ range M, |(∑' j, W i j)-t|) ≤
      ∑ _i ∈ range M, (2*S*((A+K+1)/2^K + k/2^H)) := by
    refine (sum_le_sum htriangle).trans (htot.trans_eq ?_)
    simp [C]
    ring
  obtain ⟨i, hi, hi'⟩ := Finset.exists_le_of_sum_le (s := range M) ⟨0, mem_range.mpr hM⟩ hsum
  exact ⟨i, mem_range.mp hi, hi'⟩

end Erdos69Independent

end

section

/- 统一分母迫使每个样本为整数。选取靠近指定主项的样本后，得到严格介于零与一之间的整数。 -/

open scoped ArithmeticFunction.omega

namespace Erdos69Independent

open AffineBlocks

theorem irrational_omega_series : Irrational (∑' n : ℕ, (ω (n+2) : ℝ)/2^(n+2)) := by
  by_contra hr
  obtain ⟨q,hq,hden⟩ := rational_tails hr
  obtain ⟨m,k,hk,hbound,hlo,hhi,htol⟩ := choose_blocks q hq
  obtain ⟨R⟩ := concrete_pair m k hbound
  let M := period m R.P
  let W := row m M R.hit R.miss
  have hrow (j : ℕ) := row_bound m j R.P (envelope m) (basePeriod_pos m)
    (show M = basePeriod m * ∏ p ∈ R.P,p from rfl) (fun p h => (R.primes p h).1)
    R.common R.selected_hit R.selected_miss (sample_mean R hk R.hit R.hit_lt j)
    (sample_mean R hk R.miss R.miss_lt j)
  simp only [R.card_P] at hrow
  obtain ⟨i,_,hclose⟩ := exists_close_of_weighted_row_bounds R.period_pos W
    ((k:ℝ)/2^(K m+1)) (envelope m) ((12:ℝ)^m) k
    (fun i _ => (row_integer R hden i).1) hrow
  obtain ⟨z,hz⟩ := (row_integer R hden i).2
  change (q:ℝ)*(∑' j,W i j) = z at hz
  have hscaled := (mul_le_mul_of_nonneg_left hclose (Nat.cast_nonneg q)).trans_lt htol
  have hdist : |(z:ℝ) - (q:ℝ)*((k:ℝ)/2^(K m+1))| < 1/4 := by
    calc
      _ = |(q:ℝ)*((∑' j,W i j) - (k:ℝ)/2^(K m+1))| := by rw [mul_sub, hz]
      _ = (q:ℝ)*|(∑' j,W i j) - (k:ℝ)/2^(K m+1)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
      _ < 1/4 := hscaled
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hdist
  have hzp : (0:ℝ)<z := by linarith
  have hzl : (z:ℝ)<1 := by linarith
  have hzp' : 0<z := by exact_mod_cast hzp
  have hzl' : z<1 := by exact_mod_cast hzl
  omega

end Erdos69Independent

theorem OMA.solution : type_of% @Erdos69.erdos_69 := Erdos69Independent.irrational_omega_series

end
