import OMAReductions.R_OeisA5258_conjecture_R1

-- Credit: @jagong-cmu

/-! Step H1 of OeisA5258.conjecture.R1: the case where n + 1 is prime (Eisenstein). -/

open Polynomial

namespace OMA.A5258H1

/-- The integer version of the Apery polynomial. -/
noncomputable def G (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℤ) * X ^ k

lemma map_G (n : ℕ) : (G n).map (Int.castRingHom ℚ) = OeisA5258.aperyPoly n := by
  simp [G, OeisA5258.aperyPoly, Polynomial.map_sum]

lemma coeff_G (n j : ℕ) : (G n).coeff j =
    if j ≤ n then (((n.choose j) ^ 2 * ((n + j).choose j) : ℕ) : ℤ) else 0 := by
  simp only [G, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma coeff_G_zero (n : ℕ) : (G n).coeff 0 = 1 := by
  simp [coeff_G]

lemma natDegree_G (n : ℕ) : (G n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have : ¬ N ≤ n := by exact_mod_cast not_le.mpr hN
    simp [coeff_G, this]
  · rw [coeff_G, if_pos le_rfl]
    have : 0 < (n + n).choose n := Nat.choose_pos (by omega)
    simp only [Nat.choose_self, one_pow, one_mul]
    exact_mod_cast this.ne'

lemma natTrailingDegree_G (n : ℕ) : (G n).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]
  right
  simp [coeff_G_zero]

/-- Irreducibility of the reverse implies irreducibility, when the constant term is 1. -/
lemma irreducible_of_reverse {f : ℤ[X]} (h : Irreducible f.reverse) (h0 : f.coeff 0 = 1) :
    Irreducible f := by
  refine ⟨?_, ?_⟩
  · intro hu
    apply h.not_isUnit
    obtain ⟨r, hr, hrf⟩ := Polynomial.isUnit_iff.mp hu
    rw [← hrf, reverse_C]
    exact isUnit_C.mpr hr
  · intro a b hab
    have hc : a.coeff 0 * b.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hab, h0]
    have key : ∀ u v : ℤ[X], u.coeff 0 * v.coeff 0 = 1 → IsUnit u.reverse → IsUnit u := by
      intro u v huv hu
      have hu0 : u.coeff 0 ≠ 0 := by
        intro h'; rw [h', zero_mul] at huv; exact zero_ne_one huv
      have ht : u.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hu0)
      have hd : u.natDegree = 0 := by
        rw [natDegree_eq_reverse_natDegree_add_natTrailingDegree, ht,
          natDegree_eq_zero_of_isUnit hu]
      rw [eq_C_of_natDegree_eq_zero hd]
      exact isUnit_C.mpr ⟨⟨_, _, huv, by rw [mul_comm]; exact huv⟩, rfl⟩
    rw [hab, reverse_mul_of_domain] at h
    rcases h.isUnit_or_isUnit rfl with h1 | h2
    · exact Or.inl (key a b hc h1)
    · exact Or.inr (key b a (by rw [mul_comm]; exact hc) h2)

lemma reverse_G_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 1).Prime) :
    Irreducible (G n).reverse := by
  set p := n + 1 with hpdef
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpZ
  have hnd : (G n).reverse.natDegree = n := by
    rw [reverse_natDegree, natDegree_G, natTrailingDegree_G]; rfl
  have hlc : (G n).reverse.leadingCoeff = 1 := by
    rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_G, coeff_G_zero]
  have hmon : (G n).reverse.Monic := hlc
  have hne : (G n).reverse ≠ 0 := hmon.ne_zero
  have hdeg : (G n).reverse.degree = n := by rw [degree_eq_natDegree hne, hnd]
  have hcoeff : ∀ m, m ≤ n → (G n).reverse.coeff m =
      (((n.choose (n - m)) ^ 2 * ((n + (n - m)).choose (n - m)) : ℕ) : ℤ) := by
    intro m hm
    rw [coeff_reverse, natDegree_G, revAt_le hm, coeff_G, if_pos (Nat.sub_le n m)]
  apply irreducible_of_eisenstein_criterion hP
  · rw [hlc, Ideal.mem_span_singleton]
    exact hpZ.not_dvd_one
  · intro m hm
    rw [hdeg] at hm
    have hm' : m < n := by exact_mod_cast hm
    rw [hcoeff m hm'.le, Ideal.mem_span_singleton]
    apply Int.natCast_dvd_natCast.mpr
    apply Dvd.dvd.mul_left
    have h := Nat.Prime.dvd_choose_add hp (a := n - m) (b := n) (by omega) (by omega) (by omega)
    rwa [add_comm (n - m) n] at h
  · rw [hdeg]; exact_mod_cast hn
  · rw [hcoeff 0 (Nat.zero_le n), Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [Nat.sub_zero, Nat.choose_self, one_pow, one_mul]
    intro hdvd
    have hdvd' : p ^ 2 ∣ (n + n).choose n := by exact_mod_cast hdvd
    have hpos : (n + n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have h2 := (hp.pow_dvd_iff_le_factorization hpos).mp hdvd'
    have h1 : ((n + n).choose n).factorization p ≤ 1 :=
      Nat.factorization_choose_le_one (by rw [hpdef]; nlinarith)
    omega
  · exact hmon.isPrimitive

theorem h1 : ∀ n : ℕ, 1 ≤ n → (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n) := by
  intro n hn hp
  have hG : Irreducible (G n) := irreducible_of_reverse (reverse_G_irreducible n hn hp) (coeff_G_zero n)
  have hprim : (G n).IsPrimitive := by
    intro r hr
    have := (C_dvd_iff_dvd_coeff r (G n)).mp hr 0
    rw [coeff_G_zero] at this
    exact isUnit_of_dvd_one this
  rw [← map_G]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hG

end OMA.A5258H1

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := OMA.A5258H1.h1
