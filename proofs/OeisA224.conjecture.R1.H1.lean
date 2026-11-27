import OMAReductions.R_OeisA224_conjecture_R1
import Mathlib.Tactic

namespace A224Step

def sqModSet (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun x : ℕ => x ^ 2 % n)

lemma a_eq_card {n : ℕ} (hn : 0 < n) : OeisA224.a n = (sqModSet n).card := by
  unfold OeisA224.a sqModSet
  rw [if_neg hn.ne']

lemma one_le_a (n : ℕ) : 1 ≤ OeisA224.a n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [OeisA224.a]
  · rw [a_eq_card hn]
    refine Finset.card_pos.mpr ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩⟩

lemma odd_prime_ge_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p ∧ Odd p := by
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · have := hp.two_le
    exact ⟨by omega, ⟨p / 2, by omega⟩⟩

lemma half_pow_div_card (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((Finset.range ((p ^ (j + 1) + 1) / 2)).filter (fun x => p ∣ x)) =
      (Finset.range ((p ^ j + 1) / 2)).image (fun q => p * q) := by
  obtain ⟨hp3, hp_odd⟩ := odd_prime_ge_three hp hp2
  have hpj_odd : Odd (p ^ j) := Odd.pow hp_odd
  obtain ⟨r, hr⟩ := hp_odd
  obtain ⟨s, hs⟩ := hpj_odd
  have h1 : (p ^ j + 1) / 2 = s + 1 := by omega
  have h2 : (p ^ (j + 1) + 1) / 2 = p * s + r + 1 := by
    have hmul : p ^ (j + 1) = p * p ^ j := by ring
    have hexp : p * p ^ j = 2 * (p * s + r) + 1 := by
      calc p * p ^ j = p * (2 * s + 1) := by rw [hs]
        _ = 2 * p * s + (2 * r + 1) := by rw [hr]; ring
        _ = 2 * (p * s + r) + 1 := by ring
    omega
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, h1, h2]
  constructor
  · rintro ⟨hx, q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    by_contra hq
    have hqs : s + 1 ≤ q := by omega
    have : p * (s + 1) ≤ p * q := Nat.mul_le_mul_left p hqs
    nlinarith
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, q, rfl⟩
    have hqs : q ≤ s := by omega
    have : p * q ≤ p * s := Nat.mul_le_mul_left p hqs
    nlinarith

lemma half_pow_ndiv_card (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((Finset.range ((p ^ (j + 1) + 1) / 2)).filter (fun x => ¬ p ∣ x)).card =
      p ^ j * (p - 1) / 2 := by
  obtain ⟨_, hp_odd⟩ := odd_prime_ge_three hp hp2
  have hpj_odd : Odd (p ^ j) := Odd.pow hp_odd
  obtain ⟨r, hr⟩ := hp_odd
  obtain ⟨s, hs⟩ := hpj_odd
  have htot := Finset.card_filter_add_card_filter_not (p := fun x => p ∣ x)
    (s := Finset.range ((p ^ (j + 1) + 1) / 2))
  rw [half_pow_div_card p j hp hp2,
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h),
    Finset.card_range, Finset.card_range] at htot
  have h1 : (p ^ j + 1) / 2 = s + 1 := by omega
  have h2 : (p ^ (j + 1) + 1) / 2 = p * s + r + 1 := by
    have hmul : p ^ (j + 1) = p * p ^ j := by ring
    have hexp : p * p ^ j = 2 * (p * s + r) + 1 := by
      calc p * p ^ j = p * (2 * s + 1) := by rw [hs]
        _ = 2 * p * s + (2 * r + 1) := by rw [hr]; ring
        _ = 2 * (p * s + r) + 1 := by ring
    omega
  have h3 : p ^ j * (p - 1) / 2 = p ^ j * r := by
    have : p - 1 = 2 * r := by omega
    rw [this]
    have : p ^ j * (2 * r) = 2 * (p ^ j * r) := by ring
    omega
  rw [h1, h2] at htot
  rw [h2, h3]
  have hps : p * s + r = s + p ^ j * r := by
    rw [hs, hr]
    ring
  omega

lemma sq_mod_eq_sub {N x : ℕ} (hx : x ≤ N) : (N - x) ^ 2 % N = x ^ 2 % N := by
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff]
  push_cast [Nat.cast_sub hx]
  simp

lemma inj_helper {p k x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx_lt : x < (p ^ k + 1) / 2) (hy_lt : y < (p ^ k + 1) / 2)
    (hx_ndiv : ¬ p ∣ x) (hle : y ≤ x)
    (hmod : x ^ 2 % p ^ k = y ^ 2 % p ^ k) : x = y := by
  obtain ⟨hp3, hp_odd⟩ := odd_prime_ge_three hp hp2
  have hpk_odd : Odd (p ^ k) := Odd.pow hp_odd
  obtain ⟨t, ht⟩ := hpk_odd
  have hdvd : p ^ k ∣ (x + y) * (x - y) := by
    rw [← Nat.sq_sub_sq]
    exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hle 2)).mp hmod.symm
  by_cases hpsub : p ∣ x - y
  · have hpadd : ¬ p ∣ x + y := by
      intro hpa
      have h2x : (x - y) + (x + y) = 2 * x := by omega
      have hd2x : p ∣ 2 * x := h2x ▸ dvd_add hpsub hpa
      rcases hp.dvd_mul.mp hd2x with hp2' | hpx
      · have := Nat.le_of_dvd (by omega) hp2'
        omega
      · exact hx_ndiv hpx
    have hcop : (p ^ k).Coprime (x + y) := (hp.coprime_iff_not_dvd.mpr hpadd).pow_left k
    have hdvd_sub : p ^ k ∣ x - y := hcop.dvd_of_dvd_mul_left hdvd
    by_contra hne
    have hpos : 0 < x - y := by omega
    have := Nat.le_of_dvd hpos hdvd_sub
    omega
  · have hcop : (p ^ k).Coprime (x - y) := (hp.coprime_iff_not_dvd.mpr hpsub).pow_left k
    have hdvd_add : p ^ k ∣ x + y := hcop.dvd_of_dvd_mul_right hdvd
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with rfl | h
      · exact absurd (dvd_zero p) hx_ndiv
      · exact h
    have := Nat.le_of_dvd (by omega) hdvd_add
    omega

lemma sqModSet_ndiv_card (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ((sqModSet (p ^ (j + 1))).filter (fun r => ¬ p ∣ r)).card = p ^ j * (p - 1) / 2 := by
  set k := j + 1
  obtain ⟨hp3, hp_odd⟩ := odd_prime_ge_three hp hp2
  have hpk_odd : Odd (p ^ k) := Odd.pow hp_odd
  obtain ⟨t, ht⟩ := hpk_odd
  have hpk_dvd : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hp3k : 3 ≤ p ^ k := by
    calc 3 ≤ p ^ 1 := by simp [hp3]
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  let U := (Finset.range ((p ^ k + 1) / 2)).filter (fun x => ¬ p ∣ x)
  have himg : (sqModSet (p ^ k)).filter (fun r => ¬ p ∣ r) =
      U.image (fun x => x ^ 2 % p ^ k) := by
    ext r
    simp only [sqModSet, U, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hr_ndiv⟩
      have hx_ndiv : ¬ p ∣ x := by
        intro hpx
        apply hr_ndiv
        rw [Nat.dvd_mod_iff hpk_dvd]
        exact dvd_trans hpx (dvd_pow_self x (by omega))
      by_cases hlt : x < (p ^ k + 1) / 2
      · exact ⟨x, ⟨hlt, hx_ndiv⟩, rfl⟩
      · refine ⟨p ^ k - x, ⟨?_, ?_⟩, sq_mod_eq_sub hx.le⟩
        · omega
        · intro hsub
          apply hx_ndiv
          have heq : x = p ^ k - (p ^ k - x) := by omega
          rw [heq]
          exact Nat.dvd_sub hpk_dvd hsub
    · rintro ⟨x, ⟨hx_lt, hx_ndiv⟩, rfl⟩
      refine ⟨⟨x, by omega, rfl⟩, ?_⟩
      rw [Nat.dvd_mod_iff hpk_dvd]
      intro hpx2
      exact hx_ndiv (hp.dvd_of_dvd_pow hpx2)
  rw [himg, Finset.card_image_of_injOn]
  · exact half_pow_ndiv_card p j hp hp2
  · intro x hx y hy hxy
    have hx' : x < (p ^ k + 1) / 2 ∧ ¬ p ∣ x := by simpa [U] using hx
    have hy' : y < (p ^ k + 1) / 2 ∧ ¬ p ∣ y := by simpa [U] using hy
    rcases le_total y x with hle | hle
    · exact inj_helper hp hp2 hx'.1 hy'.1 hx'.2 hle hxy
    · exact (inj_helper hp hp2 hy'.1 hx'.1 hy'.2 hle hxy.symm).symm

lemma a_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    OeisA224.a p = (p + 1) / 2 := by
  obtain ⟨hp3, hp_odd⟩ := odd_prime_ge_three hp hp2
  obtain ⟨r, hr⟩ := hp_odd
  rw [a_eq_card hp.pos]
  have htot := Finset.card_filter_add_card_filter_not (p := fun x => p ∣ x) (s := sqModSet p)
  have hndiv := sqModSet_ndiv_card p 0 hp hp2
  simp only [zero_add, pow_one, pow_zero, one_mul] at hndiv
  have hdiv : (sqModSet p).filter (fun x => p ∣ x) = {0} := by
    ext x
    simp only [sqModSet, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨y, _, rfl⟩, hd⟩
      have hlt : y ^ 2 % p < p := Nat.mod_lt _ hp.pos
      rcases Nat.eq_zero_or_pos (y ^ 2 % p) with h0 | hpos
      · exact h0
      · have := Nat.le_of_dvd hpos hd
        omega
    · rintro rfl
      exact ⟨⟨0, hp.pos, by simp⟩, dvd_zero p⟩
  rw [hdiv, Finset.card_singleton, hndiv] at htot
  omega

lemma a_prime_pow_succ_succ (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    OeisA224.a (p ^ (m + 2)) = OeisA224.a (p ^ m) + p ^ (m + 1) * (p - 1) / 2 := by
  rw [a_eq_card (pow_pos hp.pos (m + 2)), a_eq_card (pow_pos hp.pos m)]
  have htot := Finset.card_filter_add_card_filter_not (p := fun r => p ∣ r)
    (s := sqModSet (p ^ (m + 2)))
  have hndiv := sqModSet_ndiv_card p (m + 1) hp hp2
  have hdiv : (sqModSet (p ^ (m + 2))).filter (fun r => p ∣ r) =
      (sqModSet (p ^ m)).image (fun r => p ^ 2 * r) := by
    have hpk_dvd : p ∣ p ^ (m + 2) := dvd_pow_self p (by omega)
    have hpm2 : p ^ (m + 2) = p ^ 2 * p ^ m := by ring
    ext r
    simp only [sqModSet, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hr_dvd⟩
      have hpx2 : p ∣ x ^ 2 := (Nat.dvd_mod_iff hpk_dvd).mp hr_dvd
      obtain ⟨y, rfl⟩ := hp.dvd_of_dvd_pow hpx2
      refine ⟨y ^ 2 % p ^ m, ⟨y % p ^ m, Nat.mod_lt y (pow_pos hp.pos m), ?_⟩, ?_⟩
      · exact Nat.ModEq.pow 2 (Nat.mod_modEq y (p ^ m))
      · have hpy2 : (p * y) ^ 2 = p ^ 2 * y ^ 2 := by ring
        rw [hpy2, hpm2, Nat.mul_mod_mul_left]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨⟨p * z, ?_, ?_⟩, ?_⟩
      · have hp1 : 1 ≤ p := hp.one_le
        have : p * z < p * p ^ m := Nat.mul_lt_mul_of_pos_left hz hp.pos
        have : p * p ^ m ≤ p ^ 2 * p ^ m := Nat.mul_le_mul_right (p ^ m) (by nlinarith)
        linarith
      · have hpz2 : (p * z) ^ 2 = p ^ 2 * z ^ 2 := by ring
        rw [hpz2, hpm2, Nat.mul_mod_mul_left]
      · exact ⟨p * (z ^ 2 % p ^ m), by ring⟩
  rw [hdiv, Finset.card_image_of_injective _
    (fun a b h => Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h), hndiv] at htot
  omega

lemma dvd_a_even_sub_one (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ OeisA224.a (p ^ (2 * m)) - 1 := by
  obtain ⟨_, hp_odd⟩ := odd_prime_ge_three hp hp2
  obtain ⟨r, hr⟩ := hp_odd
  induction m with
  | zero =>
    rw [mul_zero, pow_zero, OeisA224.a_1]
    exact dvd_zero p
  | succ m ih =>
    have hrec : OeisA224.a (p ^ (2 * (m + 1))) =
        OeisA224.a (p ^ (2 * m)) + p ^ (2 * m + 1) * (p - 1) / 2 := by
      have he : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [he]
      exact a_prime_pow_succ_succ p (2 * m) hp hp2
    have h1 := one_le_a (p ^ (2 * m))
    have hsub : OeisA224.a (p ^ (2 * (m + 1))) - 1 =
        (OeisA224.a (p ^ (2 * m)) - 1) + p ^ (2 * m + 1) * (p - 1) / 2 := by omega
    rw [hsub]
    refine dvd_add ih ?_
    have hterm : p ^ (2 * m + 1) * (p - 1) / 2 = p * (p ^ (2 * m) * r) := by
      have hp_sub : p - 1 = 2 * r := by omega
      have hmul : p ^ (2 * m + 1) * (2 * r) = 2 * (p * (p ^ (2 * m) * r)) := by ring
      rw [hp_sub, hmul]
      omega
    rw [hterm]
    exact dvd_mul_right p _

lemma a_odd_formula (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (p + 1) * OeisA224.a (p ^ (2 * m + 1)) = p ^ (2 * m + 2) + 2 * p + 1 := by
  obtain ⟨_, hp_odd⟩ := odd_prime_ge_three hp hp2
  obtain ⟨r, hr⟩ := hp_odd
  induction m with
  | zero =>
    simp only [mul_zero, zero_add, pow_one]
    rw [a_prime p hp hp2]
    have h1 : (p + 1) / 2 = r + 1 := by omega
    rw [h1, hr]
    ring
  | succ m ih =>
    have he1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    have he2 : 2 * (m + 1) + 2 = 2 * m + 4 := by omega
    rw [he1, he2, a_prime_pow_succ_succ p (2 * m + 1) hp hp2]
    have hterm : p ^ (2 * m + 2) * (p - 1) / 2 = p ^ (2 * m + 2) * r := by
      have hp_sub : p - 1 = 2 * r := by omega
      have hmul : p ^ (2 * m + 2) * (2 * r) = 2 * (p ^ (2 * m + 2) * r) := by ring
      rw [hp_sub, hmul]
      omega
    rw [hterm, mul_add, ih]
    calc p ^ (2 * m + 2) + 2 * p + 1 + 2 * (p + 1) * (p ^ (2 * m + 2) * r)
        = p ^ (2 * m + 2) * (1 + 2 * r * (p + 1)) + 2 * p + 1 := by ring
      _ = p ^ (2 * m + 2) * p ^ 2 + 2 * p + 1 := by
          have : 1 + 2 * r * (p + 1) = p ^ 2 := by rw [hr]; ring
          rw [this]
      _ = p ^ (2 * m + 4) + 2 * p + 1 := by ring

lemma not_dvd_between {D N q : ℕ} (h1 : q * D < N) (h2 : N < (q + 1) * D) : ¬ D ∣ N := by
  rintro ⟨c, rfl⟩
  have hq1 : q < c := by
    by_contra hle
    have : c * D ≤ q * D := Nat.mul_le_mul_right D (by omega)
    linarith
  have hq2 : c < q + 1 := by
    by_contra hle
    have : (q + 1) * D ≤ c * D := Nat.mul_le_mul_right D (by omega)
    linarith
  omega

lemma odd_exp_not_dvd (p m : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    ¬ ((p ^ (2 * m + 2) + 2 * p + 1) * (p ^ (2 * m + 2) - 1)) ∣
      4 * (p + 1) ^ 2 * (p ^ (4 * m + 2) - 1) := by
  obtain ⟨hp3, hp_odd⟩ := odd_prime_ge_three hp hp2
  set X : ℕ := p ^ (2 * m)
  have hX_ge : p ^ 2 ≤ X := Nat.pow_le_pow_right hp.one_le (by omega)
  have hX9 : 9 ≤ X := by
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hp2m2 : p ^ (2 * m + 2) = p ^ 2 * X := by
    simp only [X]; ring
  have hp4m2 : p ^ (4 * m + 2) = p ^ 2 * X ^ 2 := by
    simp only [X]; ring
  rw [hp2m2, hp4m2]
  have hsub1 : 1 ≤ p ^ 2 * X := Nat.mul_pos (pow_pos hp.pos 2) (by omega)
  have hsub2 : 1 ≤ p ^ 2 * X ^ 2 := Nat.mul_pos (pow_pos hp.pos 2) (pow_pos (by omega) 2)
  by_cases hp9 : 9 ≤ p
  · refine not_dvd_between (q := 4) ?_ ?_
    · zify [hsub1, hsub2]
      have hpz : (9 : ℤ) ≤ p := by exact_mod_cast hp9
      have hXz : (9 : ℤ) ≤ X := by exact_mod_cast hX9
      have hid : 4 * ((p : ℤ) + 1) ^ 2 * ((p : ℤ) ^ 2 * X ^ 2 - 1) -
          4 * (((p : ℤ) ^ 2 * X + 2 * p + 1) * ((p : ℤ) ^ 2 * X - 1)) =
          8 * (p : ℤ) ^ 3 * X * ((X : ℤ) - 1) + 4 * (p : ℤ) ^ 2 * ((X : ℤ) ^ 2 - 1) := by ring
      have hp3_pos : (0 : ℤ) < (p : ℤ) ^ 3 * X := by positivity
      have hX1_pos : (0 : ℤ) < (X : ℤ) - 1 := by linarith
      have hp2_pos : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
      have hX2_pos : (0 : ℤ) < (X : ℤ) ^ 2 - 1 := by nlinarith
      have hprod1 : (0 : ℤ) < 8 * (p : ℤ) ^ 3 * X * ((X : ℤ) - 1) := by
        have := mul_pos hp3_pos hX1_pos
        linarith
      have hprod2 : (0 : ℤ) < 4 * (p : ℤ) ^ 2 * ((X : ℤ) ^ 2 - 1) := by
        have := mul_pos hp2_pos hX2_pos
        linarith
      linarith
    · zify [hsub1, hsub2]
      have hpz : (9 : ℤ) ≤ p := by exact_mod_cast hp9
      have hXz : (9 : ℤ) ≤ X := by exact_mod_cast hX9
      have hid : (4 + 1) * (((p : ℤ) ^ 2 * X + 2 * p + 1) * ((p : ℤ) ^ 2 * X - 1)) -
          4 * ((p : ℤ) + 1) ^ 2 * ((p : ℤ) ^ 2 * X ^ 2 - 1) =
          (p : ℤ) ^ 2 * (X : ℤ) ^ 2 * (((p : ℤ) - 9) * ((p : ℤ) + 1) + 5) +
          10 * (p : ℤ) ^ 3 * X + (4 * (p : ℤ) ^ 2 - 2 * p - 1) := by ring
      have h1 : (0 : ℤ) ≤ (p : ℤ) ^ 2 * (X : ℤ) ^ 2 := by positivity
      have h2 : (5 : ℤ) ≤ ((p : ℤ) - 9) * ((p : ℤ) + 1) + 5 := by
        have : (0 : ℤ) ≤ ((p : ℤ) - 9) * ((p : ℤ) + 1) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      have h3 : (0 : ℤ) ≤ (p : ℤ) ^ 2 * (X : ℤ) ^ 2 * (((p : ℤ) - 9) * ((p : ℤ) + 1) + 5) :=
        mul_nonneg h1 (by linarith)
      have h4 : (0 : ℤ) < 10 * (p : ℤ) ^ 3 * X := by positivity
      have h5 : (0 : ℤ) < 4 * (p : ℤ) ^ 2 - 2 * p - 1 := by nlinarith
      linarith
  · obtain ⟨r, hr⟩ := hp_odd
    have hr_lt : r ≤ 3 := by omega
    interval_cases r
    · omega
    · -- p = 3
      have hp_eq : p = 3 := by omega
      subst hp_eq
      rcases eq_or_lt_of_le hm with rfl | hm2
      · have hX_val : X = 9 := by simp [X]
        rw [hX_val]
        exact not_dvd_between (q := 6) (by norm_num) (by norm_num)
      · have hX81 : 81 ≤ X := by
          calc 81 = 3 ^ 4 := by norm_num
            _ ≤ 3 ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
        refine not_dvd_between (q := 7) ?_ ?_
        · zify [hsub1, hsub2]
          have hXz : (81 : ℤ) ≤ X := by exact_mod_cast hX81
          nlinarith [sq_nonneg ((X : ℤ) - 81)]
        · zify [hsub1, hsub2]
          have hXz : (81 : ℤ) ≤ X := by exact_mod_cast hX81
          nlinarith
    · -- p = 5
      have hp_eq : p = 5 := by omega
      subst hp_eq
      refine not_dvd_between (q := 5) ?_ ?_
      · zify [hsub1, hsub2]
        have hXz : (25 : ℤ) ≤ X := by exact_mod_cast hX_ge
        nlinarith [sq_nonneg ((X : ℤ) - 25)]
      · zify [hsub1, hsub2]
        have hXz : (25 : ℤ) ≤ X := by exact_mod_cast hX_ge
        nlinarith
    · -- p = 7
      have hp_eq : p = 7 := by omega
      subst hp_eq
      refine not_dvd_between (q := 5) ?_ ?_
      · zify [hsub1, hsub2]
        have hXz : (49 : ℤ) ≤ X := by exact_mod_cast hX_ge
        nlinarith [sq_nonneg ((X : ℤ) - 49)]
      · zify [hsub1, hsub2]
        have hXz : (49 : ℤ) ≤ X := by exact_mod_cast hX_ge
        nlinarith

end A224Step

theorem prove_A224_H1 :
    ∀ p k : ℕ, p.Prime → p ≠ 2 → 2 ≤ k →
      ¬ (p ^ k) ^ 2 ≡ 1 [MOD OeisA224.a (p ^ k) * (OeisA224.a (p ^ k) - 1)] := by
  intro p k hp hp2 hk hcong
  obtain ⟨hp3, _⟩ := A224Step.odd_prime_ge_three hp hp2
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h2m : m + m = 2 * m := by ring
    rw [h2m] at hcong hk
    have hdvd_a : p ∣ OeisA224.a (p ^ (2 * m)) * (OeisA224.a (p ^ (2 * m)) - 1) :=
      dvd_mul_of_dvd_right (A224Step.dvd_a_even_sub_one p m hp hp2) _
    have hmodp : (p ^ (2 * m)) ^ 2 ≡ 1 [MOD p] := Nat.ModEq.of_dvd hdvd_a hcong
    have hdiv0 : p ∣ (p ^ (2 * m)) ^ 2 := by
      have : (p ^ (2 * m)) ^ 2 = p ^ (4 * m) := by ring
      rw [this]
      exact dvd_pow_self p (by omega)
    unfold Nat.ModEq at hmodp
    rw [Nat.mod_eq_zero_of_dvd hdiv0, Nat.mod_eq_of_lt (by omega)] at hmodp
    omega
  · have hm : 1 ≤ m := by omega
    set a := OeisA224.a (p ^ (2 * m + 1))
    have ha_pos : 1 ≤ a := A224Step.one_le_a _
    have hf1 := A224Step.a_odd_formula p m hp hp2
    have hf2 : 2 * (p + 1) * (a - 1) = p ^ (2 * m + 2) - 1 := by
      rw [Nat.mul_sub_left_distrib, mul_one, hf1]
      omega
    have hp_ge1 : 1 ≤ (p ^ (2 * m + 1)) ^ 2 :=
      pow_pos (pow_pos hp.pos _) 2
    have hdvd : a * (a - 1) ∣ (p ^ (2 * m + 1)) ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' hp_ge1).mp hcong.symm
    have hdvd_mul : (2 * (p + 1)) ^ 2 * (a * (a - 1)) ∣
        (2 * (p + 1)) ^ 2 * ((p ^ (2 * m + 1)) ^ 2 - 1) :=
      mul_dvd_mul_left ((2 * (p + 1)) ^ 2) hdvd
    have hlhs : (2 * (p + 1)) ^ 2 * (a * (a - 1)) =
        (p ^ (2 * m + 2) + 2 * p + 1) * (p ^ (2 * m + 2) - 1) := by
      calc (2 * (p + 1)) ^ 2 * (a * (a - 1))
          = (2 * (p + 1) * a) * (2 * (p + 1) * (a - 1)) := by ring
        _ = (p ^ (2 * m + 2) + 2 * p + 1) * (p ^ (2 * m + 2) - 1) := by rw [hf1, hf2]
    have hrhs : (2 * (p + 1)) ^ 2 * ((p ^ (2 * m + 1)) ^ 2 - 1) =
        4 * (p + 1) ^ 2 * (p ^ (4 * m + 2) - 1) := by
      have he : (p ^ (2 * m + 1)) ^ 2 = p ^ (4 * m + 2) := by ring
      have he2 : (2 * (p + 1)) ^ 2 = 4 * (p + 1) ^ 2 := by ring
      rw [he, he2]
    rw [hlhs, hrhs] at hdvd_mul
    exact A224Step.odd_exp_not_dvd p m hp hp2 hm hdvd_mul


theorem OMA.solution : OMA.R_OeisA224_conjecture_R1.H1 :=
  prove_A224_H1
