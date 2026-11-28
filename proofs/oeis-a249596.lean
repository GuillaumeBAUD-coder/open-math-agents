import OMAStatements.S_oeis_a249596

/-!
# The corrected binary rotation formula for A249596

If the leading one of a number of width w is moved to the right and
the result is r, then twice the number plus one equals 2^w + r.
Consequently a quotient by n requires (2n-1)r = 2^w-1. The smallest
permitted width gives the smallest permitted number.

Sources: https://oeis.org/A249596 and https://oeis.org/A165781.
Credit: @Solitude1312
-/

open OMA.S_oeis_a249596

namespace OMA.BinaryRotation

private lemma period_spec (k : ℕ) :
    0 < period k ∧ 2 * k + 1 ∣ 2 ^ period k - 1 := by
  have hcop : Nat.Coprime 2 (2 * k + 1) := Nat.coprime_two_left.mpr ⟨k, rfl⟩
  have heuler := Nat.ModEq.pow_totient hcop
  have hp : 1 ≤ (2 : ℕ) ^ (2 * k + 1).totient := Nat.pow_pos (by decide : 0 < 2)
  exact Nat.sInf_mem (s := {e : ℕ | 0 < e ∧ 2 * k + 1 ∣ 2 ^ e - 1})
    ⟨(2 * k + 1).totient, Nat.totient_pos.mpr (by omega), (Nat.modEq_iff_dvd' hp).mp heuler.symm⟩

private lemma width_identity {m : ℕ} (hm : 0 < m) :
    2 * m + 1 = 2 ^ (Nat.log 2 m + 1) + rotate m := by
  have h := Nat.pow_log_le_self 2 hm.ne'
  rw [rotate, pow_succ]
  omega

/-- At OEIS index k+1 the multiplier is A165781(k). This includes k=0. -/
lemma corrected (k : ℕ) : a249596 (k + 1) = (k + 1) * a165781 k := by
  let q := 2 * k + 1
  let d := period k
  let z := a165781 k
  let m := (k + 1) * z
  have hq : 0 < q := by dsimp [q]; omega
  obtain ⟨hd, hdvd⟩ := period_spec k
  change 0 < d at hd
  change q ∣ 2 ^ d - 1 at hdvd
  have hz : q * z = 2 ^ d - 1 := Nat.mul_div_cancel' hdvd
  have hpower : 1 < (2 : ℕ) ^ d := one_lt_pow₀ (by decide) hd.ne'
  have hzpos : 0 < z := by
    by_contra! h
    have hz0 : z = 0 := by omega
    rw [hz0, mul_zero] at hz
    omega
  have hzle : z ≤ 2 ^ d - 1 := (Nat.le_mul_of_pos_left _ hq).trans hz.le
  have hscale : 2 * m = q * z + z := by dsimp [m, q]; ring
  have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd]
      _ = _ := pow_succ _ _
  have hlo : 2 ^ (d - 1) ≤ m := by omega
  have hhi : m < 2 ^ d := by omega
  have hlog : Nat.log 2 m = d - 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow hlo (by simpa [Nat.sub_add_cancel hd] using hhi)
  have hrotate : rotate m = z := by rw [rotate, hlog]; omega
  unfold a249596
  change sInf {x : ℕ | 0 < x ∧ x = (k + 1) * rotate x} = m
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨Nat.mul_pos (by omega) hzpos, by rw [hrotate]⟩
  · rintro x ⟨hx, hxrot⟩
    have hxwidth := width_identity hx
    have hxscale : 2 * x = q * rotate x + rotate x := calc
      2 * x = 2 * ((k + 1) * rotate x) := congrArg (2 * ·) hxrot
      _ = _ := by dsimp [q]; ring
    have hxprod : q * rotate x = 2 ^ (Nat.log 2 x + 1) - 1 := by omega
    have hwidth : d ≤ Nat.log 2 x + 1 :=
      Nat.sInf_le (s := {e : ℕ | 0 < e ∧ 2 * k + 1 ∣ 2 ^ e - 1})
        ⟨by omega, ⟨rotate x, hxprod.symm⟩⟩
    have hmono : (2 : ℕ) ^ d ≤ 2 ^ (Nat.log 2 x + 1) := Nat.pow_le_pow_right (by decide) hwidth
    have hmin : z ≤ rotate x := by
      by_contra! hlt
      have := Nat.mul_lt_mul_of_pos_left hlt hq
      omega
    exact (Nat.mul_le_mul_left (k + 1) hmin).trans_eq hxrot.symm

end OMA.BinaryRotation

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a249596.main) := by
  intro h
  have h1 : period 1 = 2 := by
    apply IsLeast.csInf_eq
    refine ⟨by decide, ?_⟩
    intro e he
    by_contra! hlt
    interval_cases e <;> revert he <;> decide
  have h2 : period 2 = 4 := by
    apply IsLeast.csInf_eq
    refine ⟨by decide, ?_⟩
    intro e he
    by_contra! hlt
    interval_cases e <;> revert he <;> decide
  have hbad := h 2 (by decide)
  rw [show a249596 2 = 2 * a165781 1 from OMA.BinaryRotation.corrected 1] at hbad
  norm_num [a165781, h1, h2] at hbad
