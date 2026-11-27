import OMAReductions.R_Schinzel_schinzel_conjecture_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP

-- Step Schinzel.schinzel_conjecture.R1.H1
-- Credit: @caa1982

open Polynomial

private lemma eval_of_natDegree_eq_one {f : ℤ[X]} (hdeg : f.natDegree = 1) (x : ℤ) :
    f.eval x = f.coeff 1 * x + f.coeff 0 := by
  have h := Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
  conv_lhs => rw [h]
  simp

private lemma single_linear (f : ℤ[X]) (hdeg : f.natDegree = 1)
    (hb : BunyakovskyCondition f) (hs : SchinzelCondition {f}) :
    Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
  set a : ℤ := f.coeff 1
  set b : ℤ := f.coeff 0
  have ha_pos : 0 < a := by
    have := hb.2.2
    rw [Polynomial.leadingCoeff, hdeg] at this
    exact this
  set q : ℕ := a.natAbs
  have hqa : (q : ℤ) = a := Int.natAbs_of_nonneg ha_pos.le
  have hq0 : q ≠ 0 := by omega
  have hcop : IsCoprime b (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    set g : ℕ := Int.gcd b (q : ℤ)
    have hg0 : g ≠ 0 := by
      intro h0
      have := Int.gcd_eq_zero_iff.mp h0
      omega
    set p : ℕ := g.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpg : (p : ℤ) ∣ (g : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd g)
    have hpb : (p : ℤ) ∣ b := hpg.trans (Int.gcd_dvd_left b (q : ℤ))
    have hpa : (p : ℤ) ∣ a := by
      rw [← hqa]
      exact hpg.trans (Int.gcd_dvd_right b (q : ℤ))
    obtain ⟨n, hn⟩ := hs p hp
    have hfn := hn f (Finset.mem_singleton_self f)
    apply hfn
    rw [eval_of_natDegree_eq_one hdeg]
    exact dvd_add (dvd_mul_of_dvd_left hpa _) hpb
  rw [Set.infinite_coe_iff]
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq (q * N + b.natAbs) hq0 hcop
  have hdvd : (q : ℤ) ∣ (p : ℤ) - b := (Int.modEq_iff_dvd.mp hp_mod.symm)
  obtain ⟨k, hk⟩ := hdvd
  have hkp : a * k + b = (p : ℤ) := by
    rw [← hqa]
    linarith
  have hk_gt : (N : ℤ) < k := by
    have h1 : (q : ℤ) * (N : ℤ) + (b.natAbs : ℤ) < (p : ℤ) := by exact_mod_cast hp_gt
    have hb_le : b ≤ (b.natAbs : ℤ) := Int.le_natAbs
    nlinarith
  refine ⟨k.toNat, ?_, ?_⟩
  · change (f.eval (k.toNat : ℤ)).natAbs.Prime
    rw [eval_of_natDegree_eq_one hdeg, Int.toNat_of_nonneg (by omega), hkp, Int.natAbs_natCast]
    exact hp_prime
  · omega

theorem OMA.solution : OMA.R_Schinzel_schinzel_conjecture_R1.H1 := by
  intro fs hbun hsch hcard hdeg
  rcases Nat.eq_zero_or_pos fs.card with h0 | hpos
  · have hemp : fs = ∅ := Finset.card_eq_zero.mp h0
    subst hemp
    rw [Set.infinite_coe_iff]
    have huniv : {n : ℕ | ∀ f ∈ (∅ : Finset ℤ[X]), (f.eval (n : ℤ)).natAbs.Prime} = Set.univ := by
      ext n; simp
    rw [huniv]
    exact Set.infinite_univ
  · have h1 : fs.card = 1 := by omega
    obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp h1
    have hinf := single_linear f (hdeg f (Finset.mem_singleton_self f))
      (hbun f (Finset.mem_singleton_self f)) hsch
    have heq : {n : ℕ | ∀ g ∈ ({f} : Finset ℤ[X]), (g.eval (n : ℤ)).natAbs.Prime} =
        {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
      ext n; simp
    rw [heq]
    exact hinf
