import OMAStatements.S_oeis_a247031
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA247031Proof

open OMA.S_oeis_a247031

private lemma three_eq_zero_ps3 : (3 : PowerSeries (ZMod 3)) = 0 := by
  ext k; rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (3 : ZMod 3) = 0 by decide]

private lemma add_pow3_ps3 (u v : PowerSeries (ZMod 3)) :
    (u + v) ^ 3 = u ^ 3 + v ^ 3 := by
  calc (u + v) ^ 3 = u ^ 3 + v ^ 3 + 3 * (u ^ 2 * v + u * v ^ 2) := by ring
    _ = u ^ 3 + v ^ 3 := by rw [three_eq_zero_ps3, zero_mul, add_zero]

private lemma finset_sum_pow3_ps3 {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → PowerSeries (ZMod 3)) :
    (∑ i ∈ s, f i) ^ 3 = ∑ i ∈ s, (f i) ^ 3 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, add_pow3_ps3, ih, Finset.sum_insert ha]

private lemma coeff_cube_mul3_mod3 (f : PowerSeries (ZMod 3)) (n : ℕ) :
    PowerSeries.coeff (3 * n) (f ^ 3) = PowerSeries.coeff n f := by
  let P : PowerSeries (ZMod 3) :=
    ∑ i ∈ Finset.range (3 * n + 1), PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i
  let R : PowerSeries (ZMod 3) := f - P
  have hP_coeff : ∀ j ≤ 3 * n, PowerSeries.coeff j P = PowerSeries.coeff j f := by
    intro j hj
    dsimp only [P]
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hR_zero : ∀ j ≤ 3 * n, PowerSeries.coeff j R = 0 := by
    intro j hj
    dsimp only [R]
    rw [map_sub, hP_coeff j hj, sub_self]
  have hR_mul_zero : ∀ g : PowerSeries (ZMod 3), PowerSeries.coeff (3 * n) (R * g) = 0 := by
    intro g
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i R * PowerSeries.coeff j g)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hR_zero i (by omega), zero_mul]
  have hf_eq : f = P + R := by dsimp only [R]; ring
  have hf3 : PowerSeries.coeff (3 * n) (f ^ 3) = PowerSeries.coeff (3 * n) (P ^ 3) := by
    rw [hf_eq, add_pow3_ps3, map_add, show R ^ 3 = R * R ^ 2 by ring, hR_mul_zero, add_zero]
  rw [hf3]
  dsimp only [P]
  rw [finset_sum_pow3_ps3, map_sum]
  have hterm : ∀ i : ℕ,
      PowerSeries.coeff (3 * n) ((PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i) ^ 3) =
        if 3 * n = 3 * i then PowerSeries.coeff i f else 0 := by
    intro i
    rw [mul_pow, ← map_pow, ← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      show i * 3 = 3 * i by ring]
    have hcube3 : ∀ x : ZMod 3, x ^ 3 = x := by decide
    rw [hcube3]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hne; rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end OeisA247031Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a247031.main := by
  intro A B hAB n
  change PowerSeries.coeff (3 * n) A ≡ 2 [ZMOD ((3 : ℕ) : ℤ)] ↔
    PowerSeries.coeff n B ≡ 2 [ZMOD ((3 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  have hmap : PowerSeries.map (Int.castRingHom (ZMod 3)) A =
      (PowerSeries.map (Int.castRingHom (ZMod 3)) B) ^ 3 := by
    rw [hAB, map_pow]
  have hc := congrArg (PowerSeries.coeff (3 * n)) hmap
  rw [OeisA247031Proof.coeff_cube_mul3_mod3] at hc
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at hc
  rw [hc]
