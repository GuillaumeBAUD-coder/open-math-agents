import OMAStatements.S_oeis_a373308
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

namespace OMA.ThueCube

open OMA.S_oeis_a373308 Polynomial

lemma coeff_factor (f : Polynomial ℤ) (j n : ℕ) :
    (f * (1 - X ^ j) ^ 3).coeff n = f.coeff n -
      3 * (if j ≤ n then f.coeff (n-j) else 0) +
      3 * (if j*2 ≤ n then f.coeff (n-j*2) else 0) -
      (if j*3 ≤ n then f.coeff (n-j*3) else 0) := by
  have h : f * (1-X^j)^3 = f - C (3:ℤ) * (f*X^j) +
      C (3:ℤ) * (f*X^(j*2)) - f*X^(j*3) := by
    simp only [map_ofNat, pow_mul]
    ring
  rw [h]
  simp [coeff_mul_X_pow']

lemma trunc_stable (d n : ℕ) (hd : n < d) : (truncation d).coeff n = a n := by
  induction d, hd using Nat.le_induction with
  | base => rfl
  | succ d hd ih =>
    have he : d < 2 ^ d := Nat.lt_two_pow_self
    rw [truncation, Finset.prod_range_succ, coeff_factor]
    simpa [truncation, show ¬ 2^d ≤ n by omega, show ¬ 2^d*2 ≤ n by omega,
      show ¬ 2^d*3 ≤ n by omega] using ih

lemma expand_rec (d : ℕ) :
    truncation (d+1) = expand ℤ 2 (truncation d) * (1-X^1)^3 := by
  rw [truncation, Finset.prod_range_succ', truncation, map_prod]
  simp only [map_pow, map_sub, map_one, expand_X, pow_one, pow_zero]
  apply congrArg (fun p : Polynomial ℤ => p * (1 - X) ^ 3)
  apply Finset.prod_congr rfl
  intro j hj
  rw [← pow_mul, pow_succ' 2 j]

lemma single_coeff (n : ℕ) :
    a n = (expand ℤ 2 (truncation (n+1)) * (1-X^1)^3).coeff n := by
  rw [← expand_rec, trunc_stable _ _ (by omega)]

lemma first : a 0 = 1 ∧ a 1 = -3 := by
  have h0 : a 0 = (1 * (1-X^1)^3 : Polynomial ℤ).coeff 0 := by simp [a, truncation]
  have h1 : a 1 = ((1 * (1-X^1)^3) * (1-X^2)^3 : Polynomial ℤ).coeff 1 := by
    simp [a, truncation, Finset.prod_range_succ]
  rw [h0, h1]
  simp only [coeff_factor]
  norm_num [coeff_one]

lemma ev (n : ℕ) : a (2*n+2) = a (n+1) + 3 * a n := by
  rw [single_coeff, coeff_factor]
  simp only [one_mul, coeff_expand (by decide : 0 < 2)]
  split_ifs <;> try omega
  all_goals simp only [show (2*n+2)/2=n+1 by omega, show (2*n+2-2)/2=n by omega,
    sub_zero, mul_zero]
  all_goals rw [trunc_stable _ _ (by omega),trunc_stable _ _ (by omega)]

lemma od (n : ℕ) : a (2*n+3) = -(3*a (n+1)) - a n := by
  rw [single_coeff, coeff_factor]
  simp only [one_mul, coeff_expand (by decide : 0 < 2)]
  split_ifs <;> try omega
  all_goals simp only [show (2*n+3-1)/2=n+1 by omega, show (2*n+3-3)/2=n by omega,
    zero_sub, mul_zero, add_zero]
  all_goals rw [trunc_stable _ _ (by omega),trunc_stable _ _ (by omega)]

-- Gawron, Miska and Ulas, Lemma 3.5.
lemma four_three (n : ℕ) : a (4*n+3) = 8*a n := by
  cases n with
  | zero => simp only [Nat.mul_zero, zero_add] ; rw [show 3=2*0+3 by decide, od, first.1, first.2]; norm_num
  | succ n =>
    rw [show 4*(n+1)+3=2*(2*n+2)+3 by omega, od, show 2*n+2+1=2*n+3 by omega, od, ev]
    ring

lemma four_six (n : ℕ) : a (4*n+6) = 8*a n := by
  rw [show 4*n+6=2*(2*n+2)+2 by omega, ev, show 2*n+2+1=2*n+3 by omega, od, ev]
  ring

lemma parity_a (n : ℕ) : a n % 2 = if n%4 ≤ 1 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · norm_num [first.1]
    rcases n with _ | n
    · norm_num [first.2]
    let k := n / 2
    have h1 := ih k (by dsimp [k]; omega)
    have h2 := ih (k+1) (by dsimp [k]; omega)
    have hc : n+1+1=2*k+2 ∨ n+1+1=2*k+3 := by dsimp [k]; omega
    rcases hc with hc | hc <;> rw [hc]
    · rw [ev]
      split_ifs at * <;> omega
    · rw [od]
      split_ifs at * <;> omega

def good (b : ℕ) : Prop := ∀ t ∈ Nat.digits 4 b, t ≤ 1

lemma good_digits (b : ℕ) : good b ↔ b%4 ≤ 1 ∧ good (b/4) := by
  by_cases h : b=0
  · simp [h, good]
  unfold good
  rw [Nat.digits_eq_cons_digits_div (by decide : 1<4) h]
  simp

lemma zero_step (m : ℕ) :
    zeroIndex m ↔ (m%4=0 ∨ m%4=3) ∧ zeroIndex (m/4) := by
  change (∃ b, m = 3*b ∧ good b) ↔ _ ∧ (∃ b, m/4=3*b ∧ good b)
  constructor
  · rintro ⟨b, rfl, hg⟩
    obtain ⟨hb,h⟩ := (good_digits b).mp hg
    have hb' : b%4=0 ∨ b%4=1 := by omega
    rcases hb' with hb' | hb' <;> exact ⟨by omega, b/4, by omega, h⟩
  · rintro ⟨hm, b, h, hg⟩
    rcases hm with hm | hm
    · refine ⟨4*b, by omega, (good_digits _).mpr ⟨by omega, ?_⟩⟩
      simpa using hg
    · refine ⟨4*b+1, by omega, (good_digits _).mpr ⟨by omega, ?_⟩⟩
      rwa [show (4*b+1)/4=b by omega]

lemma classify (n : ℕ) : a n=0 ↔ zeroIndex (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n%4 ≤ 1
    · have hp := parity_a n
      rw [if_pos hsmall] at hp
      rw [zero_step]
      constructor
      · intro h
        rw [h] at hp
        omega
      · intro h
        omega
    by_cases htwo : n=2
    · subst n
      have ha := ev 0
      rw [first.1, first.2] at ha
      norm_num at ha
      constructor
      · intro _
        exact ⟨1, rfl, by decide⟩
      · intro _
        omega
    by_cases hrem : n%4=2
    · let k:=n/4-1
      have he : n=4*k+6 := by dsimp [k]; omega
      have hh := ih k (by omega)
      rw [zero_step, show (n+1)/4=k+1 by omega, ← hh,
        show a n=8*a k by simpa only [he] using four_six k]
      have hr : (n+1)%4=3 := by omega
      simp [hr]
    · let k:=n/4
      have he : n=4*k+3 := by dsimp [k]; omega
      have hh := ih k (by omega)
      rw [zero_step, show (n+1)/4=k+1 by omega, ← hh,
        show a n=8*a k by simpa only [he] using four_three k]
      have hr : (n+1)%4=0 := by omega
      simp [hr]

lemma thue_even (k : ℕ) : thue (2*k) = thue k := by
  by_cases hk : k=0
  · simp [hk]
  unfold thue
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) (by omega : 2*k≠0)]
  simp

lemma thue_odd (k : ℕ) : thue (2*k+1) = -thue k := by
  unfold thue
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) (by omega : 2*k+1≠0)]
  rw [show (2*k+1)%2=1 by omega, show (2*k+1)/2=k by omega]
  simp [pow_add]

lemma residue (n : ℕ) :
    a n ≡ (if 3 ∣ n then thue (n/3) else 0) [ZMOD 3] := by
  rw [Int.modEq_iff_dvd]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · norm_num [first.1, thue]
    rcases n with _ | n
    · norm_num [first.2]
    let k := n / 2
    have h1 := ih k (by dsimp [k]; omega)
    have h2 := ih (k+1) (by dsimp [k]; omega)
    have hc : n+1+1=2*k+2 ∨ n+1+1=2*k+3 := by dsimp [k]; omega
    rcases hc with hc | hc
    · rw [hc, ev]
      by_cases hd : 3∣k+1
      · rw [if_pos hd] at h2
        rw [if_pos (by omega), show (2*k+2)/3=2*((k+1)/3) by omega, thue_even]
        omega
      · rw [if_neg hd] at h2
        rw [if_neg (by omega)]
        omega
    · rw [hc, od]
      by_cases hd : 3∣k
      · rw [if_pos hd] at h1
        rw [if_pos (by omega), show (2*k+3)/3=2*(k/3)+1 by omega, thue_odd]
        omega
      · rw [if_neg hd] at h1
        rw [if_neg (by omega)]
        omega

end OMA.ThueCube

open OMA.S_oeis_a373308 OMA.ThueCube

theorem OMA.solution : type_of% @OMA.S_oeis_a373308.main := by
  refine ⟨?_, classify⟩
  intro n
  have h := residue (3*n)
  have h1 := residue (3*n+1)
  have h2 := residue (3*n+2)
  rw [if_pos (by omega), show 3*n/3=n by omega] at h
  rw [if_neg (by omega), Int.modEq_iff_dvd] at h1 h2
  exact ⟨h, by omega, by omega⟩
