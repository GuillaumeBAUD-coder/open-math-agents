import OMAReductions.R_Bunyakovsky_bunyakovsky_conjecture_R1

-- The Bunyakovsky conjecture in degree one.
-- For no form the statement is empty. For one form a * n + b with a > 0 the Schinzel condition forces
-- gcd(a, b) = 1, and Dirichlet's theorem (in Mathlib as Nat.forall_exists_prime_gt_and_zmodEq) gives arbitrarily
-- large primes p = b mod a; each is a value a * n + b with n as large as wanted. The Lean proof here is the
-- translation between the polynomial statement and Dirichlet's theorem.
-- The classical degree-one case, not progress on the conjecture in higher degree.

namespace OMA.Dickson1

open Polynomial

theorem one_form (fs : Finset ℤ[X])
    (hfs : ∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f) (hfs' : SchinzelCondition fs)
    (hc : fs.card ≤ 1) :
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime} := by
  rw [Set.infinite_coe_iff]
  rcases Nat.eq_zero_or_pos fs.card with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    subst h0
    have huniv : {n : ℕ | ∀ f ∈ (∅ : Finset ℤ[X]), (f.eval (n : ℤ)).natAbs.Prime} = Set.univ := by
      ext n
      simp
    rw [huniv]
    exact Set.infinite_univ
  · have h1 : fs.card = 1 := by omega
    obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨hdeg, -, -, hlead⟩ := hfs f (Finset.mem_singleton_self f)
    have hf := Polynomial.eq_X_add_C_of_degree_eq_one hdeg
    have heval : ∀ x : ℤ, f.eval x = f.leadingCoeff * x + f.coeff 0 := by
      intro x
      conv_lhs => rw [hf]
      simp
    -- the two coefficients are coprime
    have hcop : IsCoprime (f.coeff 0) ((f.leadingCoeff.natAbs : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      apply Nat.Coprime.symm
      apply Nat.coprime_of_dvd
      intro p hp hpa hpb
      obtain ⟨n, hn⟩ := hfs' p hp
      apply hn f (Finset.mem_singleton_self f)
      rw [heval]
      have h1' : (p : ℤ) ∣ f.leadingCoeff := by
        rw [Int.natAbs_natCast] at hpa
        exact Int.natCast_dvd.mpr hpa
      have h2' : (p : ℤ) ∣ f.coeff 0 := Int.natCast_dvd.mpr hpb
      exact dvd_add (Dvd.dvd.mul_right h1' _) h2'
    have hA0 : f.leadingCoeff.natAbs ≠ 0 := by
      intro h
      have := Int.natAbs_eq_zero.mp h
      omega
    have hAeq : ((f.leadingCoeff.natAbs : ℕ) : ℤ) = f.leadingCoeff := by
      rw [Int.natCast_natAbs]
      exact abs_of_pos hlead
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq
      (f.leadingCoeff.natAbs * (N + 1) + (f.coeff 0).natAbs) hA0 hcop
    rw [Int.modEq_iff_dvd, hAeq] at hmod
    obtain ⟨t, ht⟩ := hmod
    -- p = a * (-t) + b
    have hpz : (p : ℤ) = f.leadingCoeff * (-t) + f.coeff 0 := by linarith
    have hbig : f.leadingCoeff * ((N : ℤ) + 1) + |f.coeff 0| < (p : ℤ) := by
      have h3 : ((f.leadingCoeff.natAbs * (N + 1) + (f.coeff 0).natAbs : ℕ) : ℤ) < (p : ℤ) := by
        exact_mod_cast hpN
      push_cast at h3
      rw [abs_of_pos hlead] at h3
      exact h3
    have hb := le_abs_self (f.coeff 0)
    have htpos : (N : ℤ) + 1 ≤ -t := by
      by_contra hlt
      have hle : -t ≤ (N : ℤ) := by omega
      have hmul : f.leadingCoeff * (-t) ≤ f.leadingCoeff * (N : ℤ) :=
        mul_le_mul_of_nonneg_left hle hlead.le
      nlinarith
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ -t)
    refine ⟨m, ?_, by omega⟩
    intro g hg
    rw [Finset.mem_singleton] at hg
    subst hg
    rw [heval, ← hm, ← hpz, Int.natAbs_natCast]
    exact hp


theorem degree_one (f : ℤ[X]) (hd : f.natDegree = 1) (hb : BunyakovskyCondition f)
    (hs : SchinzelCondition {f}) : Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
  have hdeg : f.degree = 1 := by
    have h := (Polynomial.degree_eq_iff_natDegree_eq_of_pos (p := f) (n := 1) (by norm_num)).mpr hd
    exact_mod_cast h
  have h := one_form {f} (fun g hg => by
    rw [Finset.mem_singleton] at hg
    subst hg
    exact ⟨hdeg, hb⟩) hs (by simp)
  have hset : {n : ℕ | ∀ g ∈ ({f} : Finset ℤ[X]), (g.eval (n : ℤ)).natAbs.Prime} =
      {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
    ext n
    simp
  rw [hset] at h
  exact h

end OMA.Dickson1

theorem OMA.solution : OMA.R_Bunyakovsky_bunyakovsky_conjecture_R1.H1 := by
  intro f hd hb hs
  exact OMA.Dickson1.degree_one f hd hb hs
