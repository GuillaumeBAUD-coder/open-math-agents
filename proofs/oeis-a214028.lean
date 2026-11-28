import OMAStatements.S_oeis_a214028
import Mathlib

namespace OMA.P_oeis_a214028

open OMA.S_oeis_a214028

/-- The step matrix. -/
def M (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![2, 1; 1, 0]

theorem M_pow (R : Type) [CommRing R] (k : ℕ) :
    M R ^ k = !![(pell (k + 1) : R), (pell k : R); (pell k : R), (pell (k + 1) : R) - 2 * pell k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pell, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, ih]
    have h : pell (k + 1 + 1) = 2 * pell (k + 1) + pell k := rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two, h] <;> ring

theorem pow_01 (R : Type) [CommRing R] (k : ℕ) : (M R ^ k) 0 1 = (pell k : R) := by
  rw [M_pow]; simp

theorem pow_00 (R : Type) [CommRing R] (k : ℕ) : (M R ^ k) 0 0 = (pell (k + 1) : R) := by
  rw [M_pow]; simp

theorem pow_eq_one_iff (R : Type) [CommRing R] (k : ℕ) :
    M R ^ k = 1 ↔ (pell k : R) = 0 ∧ (pell (k + 1) : R) = 1 := by
  constructor
  · intro h
    have h1 := pow_01 R k
    have h0 := pow_00 R k
    rw [h] at h1 h0
    simp at h1 h0
    exact ⟨h1.symm, h0.symm⟩
  · rintro ⟨h1, h2⟩
    rw [M_pow, h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem pow_eq_scalar (R : Type) [CommRing R] (k : ℕ) (h : (pell k : R) = 0) :
    M R ^ k = (pell (k + 1) : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [M_pow, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_period (n : ℕ) [NeZero n] : ∃ p : ℕ, 0 < p ∧ M (ZMod n) ^ p = 1 := by
  have hu : IsUnit (M (ZMod n)) := by
    refine IsUnit.of_mul_eq_one (!![0, 1; 1, -2]) ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
  obtain ⟨u, hu⟩ := hu
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]
  rfl

theorem mem_period_iff (n : ℕ) (p : ℕ) :
    (∀ k : ℕ, pell (k + p) ≡ pell k [MOD n]) ↔ M (ZMod n) ^ p = 1 := by
  constructor
  · intro h
    rw [pow_eq_one_iff]
    have h0 := h 0
    have h1 := h 1
    rw [← ZMod.natCast_eq_natCast_iff] at h0 h1
    rw [zero_add] at h0
    rw [add_comm] at h1
    simpa [pell] using And.intro h0 h1
  · intro h k
    rw [← ZMod.natCast_eq_natCast_iff, ← pow_01, ← pow_01, pow_add, h, mul_one]

theorem dvd_iff (n k : ℕ) : n ∣ pell k ↔ (pell k : ZMod n) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).symm

theorem solution_aux (n : ℕ) (hn : 1 ≤ n) :
    period n = a n * zeros n ∧ zeros n ∣ period n ∧ period n / zeros n = a n := by
  haveI : NeZero n := ⟨by omega⟩
  -- the period
  have hPne : {p : ℕ | 0 < p ∧ ∀ k : ℕ, pell (k + p) ≡ pell k [MOD n]}.Nonempty := by
    obtain ⟨p, hp, h⟩ := exists_period n
    exact ⟨p, hp, (mem_period_iff n p).2 h⟩
  have hP := Nat.sInf_mem hPne
  change (0 < period n ∧ ∀ k : ℕ, pell (k + period n) ≡ pell k [MOD n]) at hP
  obtain ⟨hp0, hp⟩ := hP
  have hMp : M (ZMod n) ^ period n = 1 := (mem_period_iff n _).1 hp
  have hpz : (pell (period n) : ZMod n) = 0 := ((pow_eq_one_iff _ _).1 hMp).1
  -- the entry point
  have hAne : {k : ℕ | 0 < k ∧ n ∣ pell k}.Nonempty := ⟨period n, hp0, (dvd_iff _ _).2 hpz⟩
  have hA := Nat.sInf_mem hAne
  change (0 < a n ∧ n ∣ pell (a n)) at hA
  obtain ⟨ha0, ha⟩ := hA
  have hmin : ∀ r : ℕ, 0 < r → n ∣ pell r → a n ≤ r := fun r h1 h2 => Nat.sInf_le ⟨h1, h2⟩
  have haz : (pell (a n) : ZMod n) = 0 := (dvd_iff _ _).1 ha
  have hsc := pow_eq_scalar (ZMod n) (a n) haz
  set c : ZMod n := (pell (a n + 1) : ZMod n) with hc
  have hpowq : ∀ q : ℕ, M (ZMod n) ^ (a n * q) = (c ^ q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    intro q
    rw [pow_mul, hsc, smul_pow, one_pow]
  have hcu : IsUnit c := by
    have h1 := hpowq (period n)
    rw [mul_comm, pow_mul, hMp, one_pow] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
    exact IsUnit.of_pow_eq_one h2.symm hp0.ne'
  -- zeros are the multiples of the entry point
  have key : ∀ k : ℕ, n ∣ pell k ↔ a n ∣ k := by
    intro k
    constructor
    · intro hk
      have hk' : (pell k : ZMod n) = 0 := (dvd_iff _ _).1 hk
      have hdm := Nat.div_add_mod k (a n)
      have h1 : M (ZMod n) ^ k = (c ^ (k / a n)) • M (ZMod n) ^ (k % a n) := by
        conv_lhs => rw [← hdm]
        rw [pow_add, hpowq, smul_mul_assoc, one_mul]
      have h2 := congrFun (congrFun h1 0) 1
      rw [Matrix.smul_apply, pow_01, pow_01, hk', smul_eq_mul] at h2
      have h3 : (pell (k % a n) : ZMod n) = 0 := ((hcu.pow _).mul_right_eq_zero).1 h2.symm
      have h4 : n ∣ pell (k % a n) := (dvd_iff _ _).2 h3
      by_contra hnd
      have hpos : 0 < k % a n := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
      have := hmin _ hpos h4
      have := Nat.mod_lt k ha0
      omega
    · rintro ⟨q, rfl⟩
      rw [dvd_iff, ← pow_01, hpowq]
      simp
  obtain ⟨t, ht⟩ := (key (period n)).1 ((dvd_iff _ _).2 hpz)
  have hz : zeros n = t := by
    unfold zeros
    rw [ht]
    have : (Finset.range (a n * t)).filter (fun k => n ∣ pell k)
        = (Finset.range t).image (fun i => a n * i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, key]
      constructor
      · rintro ⟨h1, q, rfl⟩
        exact ⟨q, lt_of_mul_lt_mul_left h1 (Nat.zero_le _), rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨Nat.mul_lt_mul_of_pos_left hq ha0, q, rfl⟩
    rw [this, Finset.card_image_of_injective _ (fun x y h => Nat.eq_of_mul_eq_mul_left ha0 h),
      Finset.card_range]
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht; omega
    · exact h
  rw [hz, ht]
  exact ⟨rfl, Dvd.intro_left _ rfl, Nat.mul_div_cancel _ ht0⟩

end OMA.P_oeis_a214028

theorem OMA.solution : type_of% @OMA.S_oeis_a214028.main := fun n hn =>
  OMA.P_oeis_a214028.solution_aux n hn
