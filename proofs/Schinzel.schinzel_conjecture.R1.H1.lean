import OMAReductions.R_Schinzel_schinzel_conjecture_R1

/-!
Proof of `Schinzel.schinzel_conjecture.R1.H1` (Dirichlet's theorem for a single linear polynomial):
if `fs` has at most one polynomial, of degree `1`, satisfying the Bunyakovsky and Schinzel
conditions, then infinitely many `n : ℕ` make `(f.eval n).natAbs` prime for every `f ∈ fs`.
Directly uses Mathlib's `Nat.forall_exists_prime_gt_and_zmodEq`.
-/

namespace SchinzelR1H1

open Polynomial

private lemma eval_deg_one {f : ℤ[X]} (hdeg : f.natDegree = 1) (x : ℤ) :
    f.eval x = f.coeff 1 * x + f.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range, hdeg]
  simp [Finset.sum_range_succ, mul_comm, add_comm]

private lemma isCoprime_coeff_zero_one {f : ℤ[X]} (hdeg : f.natDegree = 1)
    (hsch : SchinzelCondition {f}) :
    IsCoprime (f.coeff 0) (f.coeff 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  set p := (Int.gcd (f.coeff 0) (f.coeff 1)).minFac
  have hp : p.Prime := Nat.minFac_prime hne
  have hp_dvd : p ∣ Int.gcd (f.coeff 0) (f.coeff 1) := Nat.minFac_dvd _
  have h0 : (p : ℤ) ∣ f.coeff 0 := (Int.natCast_dvd_natCast.mpr hp_dvd).trans (Int.gcd_dvd_left _ _)
  have h1 : (p : ℤ) ∣ f.coeff 1 := (Int.natCast_dvd_natCast.mpr hp_dvd).trans (Int.gcd_dvd_right _ _)
  obtain ⟨n, hn⟩ := hsch p hp
  apply hn f (Finset.mem_singleton_self f)
  rw [eval_deg_one hdeg]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) h0

theorem main_proof : OMA.R_Schinzel_schinzel_conjecture_R1.H1 := by
  intro fs hbun hsch hcard hdeg
  by_cases hempty : fs = ∅
  · subst hempty
    have hset : {n : ℕ | ∀ f ∈ (∅ : Finset ℤ[X]), (f.eval (n : ℤ)).natAbs.Prime} = Set.univ := by
      ext n; simp
    rw [hset]
    exact Set.infinite_univ.to_subtype
  · have hcard1 : fs.card = 1 := by
      have hpos : 0 < fs.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      omega
    obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp hcard1
    have hf_deg : f.natDegree = 1 := hdeg f (Finset.mem_singleton_self f)
    have hf_bun : BunyakovskyCondition f := hbun f (Finset.mem_singleton_self f)
    have ha_pos : 0 < f.coeff 1 := by
      have hlc : f.leadingCoeff = f.coeff 1 := by rw [Polynomial.leadingCoeff, hf_deg]
      rw [← hlc]
      exact hf_bun.2.2
    set q : ℕ := (f.coeff 1).natAbs
    have hq_eq : (q : ℤ) = f.coeff 1 := Int.natAbs_of_nonneg ha_pos.le
    have hq_ne : q ≠ 0 := by omega
    have hcop : IsCoprime (f.coeff 0) (q : ℤ) := by
      rw [hq_eq]
      exact isCoprime_coeff_zero_one hf_deg hsch
    apply Set.Infinite.to_subtype
    rw [Set.infinite_iff_exists_gt]
    intro N
    set M : ℕ := q * N + (f.coeff 0).natAbs
    obtain ⟨p, hpM, hp_prime, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_zmodEq M (q := q) (a := f.coeff 0) hq_ne hcop
    have hdvd : (q : ℤ) ∣ (p : ℤ) - f.coeff 0 := hmod.symm.dvd
    obtain ⟨k, hk⟩ := hdvd
    have hb_le : f.coeff 0 ≤ ((f.coeff 0).natAbs : ℤ) := Int.le_natAbs
    have hqk_gt : (q : ℤ) * (N : ℤ) < (q : ℤ) * k := by
      have hpM' : (q : ℤ) * (N : ℤ) + ((f.coeff 0).natAbs : ℤ) < (p : ℤ) := by
        exact_mod_cast hpM
      linarith
    have hk_gt : (N : ℤ) < k := by
      have hq_pos : (0 : ℤ) < (q : ℤ) := by omega
      nlinarith
    set n : ℕ := k.toNat
    have hn_eq : (n : ℤ) = k := Int.toNat_of_nonneg (by omega)
    have hn_gt : N < n := by omega
    refine ⟨n, ?_, hn_gt⟩
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
    rw [eval_deg_one hf_deg, ← hq_eq, hn_eq]
    have heval : (q : ℤ) * k + f.coeff 0 = (p : ℤ) := by linarith
    rw [heval, Int.natAbs_natCast]
    exact hp_prime

end SchinzelR1H1

theorem OMA.solution : OMA.R_Schinzel_schinzel_conjecture_R1.H1 :=
  SchinzelR1H1.main_proof
