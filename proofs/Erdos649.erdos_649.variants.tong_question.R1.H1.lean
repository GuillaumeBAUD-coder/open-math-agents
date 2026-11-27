import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1
import Mathlib

-- Step Erdos649.erdos_649.variants.tong_question.R1.H1: hypothesis H1 of reduction Erdos649.erdos_649.variants.tong_question.R1
-- Credit: @ivillar

/-!
The largest prime factor of some positive power `q ^ e - 1` is `p` exactly when it is for the
exponent `orderOf q` modulo `p`: `p ∣ q ^ e - 1` forces `orderOf q ∣ e`, hence
`q ^ orderOf q - 1 ∣ q ^ e - 1`.
-/
namespace F2E649

theorem dvd_iff (p q e : ℕ) (hq : 0 < q) : p ∣ q ^ e - 1 ↔ (q : ZMod p) ^ e = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow,
    Nat.cast_one, sub_eq_zero]

theorem two_le_pow (q e : ℕ) (hq : 2 ≤ q) (he : 0 < e) : 2 ≤ q ^ e :=
  calc 2 ≤ q := hq
    _ = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ e := Nat.pow_le_pow_right (by omega) he

theorem pure : ∀ p q : ℕ, p.Prime → q.Prime → q < p →
    ((∃ e : ℕ, 0 < e ∧ (q ^ e - 1).maxPrimeFac = p) ↔
      (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac = p) := by
  intro p q hp hq hqp
  constructor
  · rintro ⟨e, he, hmax⟩
    have hpe : p ∣ q ^ e - 1 := hmax ▸ Nat.maxPrimeFac_dvd
    have hpow : (q : ZMod p) ^ e = 1 := (dvd_iff p q e hq.pos).mp hpe
    have hde : orderOf (q : ZMod p) ∣ e := orderOf_dvd_of_pow_eq_one hpow
    have hd : 0 < orderOf (q : ZMod p) := Nat.pos_of_dvd_of_pos hde he
    have hpd : p ∣ q ^ orderOf (q : ZMod p) - 1 :=
      (dvd_iff p q _ hq.pos).mpr (pow_orderOf_eq_one _)
    obtain ⟨k, hk⟩ := hde
    have hdvd : q ^ orderOf (q : ZMod p) - 1 ∣ q ^ e - 1 := by
      have h : q ^ orderOf (q : ZMod p) - 1 ∣ (q ^ orderOf (q : ZMod p)) ^ k - 1 :=
        Nat.sub_one_dvd_pow_sub_one _ _
      rw [← pow_mul, ← hk] at h
      exact h
    have h2d := two_le_pow q _ hq.two_le hd
    have h2e := two_le_pow q e hq.two_le he
    have hpos : 0 < q ^ orderOf (q : ZMod p) - 1 := by omega
    have hgt : 1 < q ^ orderOf (q : ZMod p) - 1 :=
      lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hpd)
    have hpr := Nat.prime_maxPrimeFac_of_one_lt _ hgt
    have hepos : q ^ e - 1 ≠ 0 := by omega
    have hle : (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac ≤ p := by
      calc (q ^ orderOf (q : ZMod p) - 1).maxPrimeFac ≤ (q ^ e - 1).maxPrimeFac :=
            Nat.le_maxPrimeFac hepos hpr (Nat.maxPrimeFac_dvd.trans hdvd)
        _ = p := hmax
    exact Nat.maxPrimeFac_eq_of_dvd_of_le _ p hpos hp hpd hle
  · intro hmax
    refine ⟨orderOf (q : ZMod p), ?_, hmax⟩
    by_contra h0
    have h00 : orderOf (q : ZMod p) = 0 := by omega
    rw [h00, pow_zero, Nat.sub_self, Nat.maxPrimeFac_zero] at hmax
    exact hp.ne_zero hmax.symm

end F2E649

theorem OMA.solution : OMA.R_Erdos649_erdos_649_variants_tong_question_R1.H1 :=
  F2E649.pure
