import OMAStatements.S_mo_487715
import Mathlib

-- Problem: Discrete Fourier Transform using not the n-th roots of unity, but the 2n-th primitive roots of unity
-- Upstream: formal-conjectures statements/mo-487715.lean:0 (declaration OMA.S_mo_487715.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Polynomial Finset OMA.S_mo_487715

theorem OMA.solution : type_of% @OMA.S_mo_487715.main := by
  intro d n ζ hζ
  have hn : 0 < n := Nat.two_pow_pos d
  have h2n : 0 < 2 * n := by omega
  have : NeZero (2 * n) := ⟨by omega⟩
  have hζn2 : IsPrimitiveRoot (ζ ^ n) 2 := hζ.pow h2n (mul_comm 2 n)
  have hζn : ζ ^ n = -1 := hζn2.eq_neg_one_of_two_right
  have hω : IsPrimitiveRoot (ζ ^ 2) n := hζ.pow h2n rfl
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hfreq : ∀ i, frequency ζ i ^ n = -1 := by
    intro i
    unfold frequency
    rw [← pow_mul, mul_comm, pow_mul, hζn]
    exact Odd.neg_one_pow ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    unfold frequency
    apply hζ.pow_of_coprime
    have h2 : 2 * n = 2 ^ (d + 1) := by
      show 2 * 2 ^ d = 2 ^ (d + 1)
      ring
    rw [h2]
    apply Nat.Coprime.pow_right
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
  · intro z
    constructor
    · intro hz
      have hz2 : z ^ (2 * n) = 1 := by
        rw [mul_comm, pow_mul, hz]
        norm_num
      obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz2
      have h3 : (ζ ^ k) ^ n = (ζ ^ n) ^ k := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [h3, hζn] at hz
      have hodd : Odd k := by
        rcases Nat.even_or_odd k with he | ho
        · exfalso
          rw [he.neg_one_pow] at hz
          norm_num at hz
        · exact ho
      obtain ⟨i, rfl⟩ := hodd
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact hfreq i
  · intro m s c
    have hz : ∀ j, ‖frequency ζ j‖ = 1 := by
      intro j
      unfold frequency
      rw [norm_pow, hnorm, one_pow]
    have hz0 : ∀ j, frequency ζ j ≠ 0 := fun j => pow_ne_zero _ hζ0
    have E : ∀ k ∈ range n, ∀ l ∈ range n,
        ∑ j ∈ range n, (frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ l)
          = if k = l then (n : ℂ) else 0 := by
      intro k hk l hl
      rw [Finset.mem_range] at hk hl
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl]
        have h1 : ∀ j, frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ k = 1 := by
          intro j
          rw [← mul_pow, mul_inv_cancel₀ (hz0 j), one_pow]
        rw [Finset.sum_congr rfl (fun j _ => h1 j)]
        simp
      · rw [if_neg hkl]
        obtain ⟨e, he⟩ : ∃ e : ℤ, e = (k : ℤ) - l := ⟨_, rfl⟩
        have hterm : ∀ j : ℕ, frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ l
            = ζ ^ e * ((ζ ^ 2) ^ e) ^ j := by
          intro j
          unfold frequency
          have h1 : (ζ ^ (2 * j + 1)) ^ k * ((ζ ^ (2 * j + 1))⁻¹) ^ l = (ζ ^ (2 * j + 1)) ^ e := by
            rw [he, zpow_sub₀ (pow_ne_zero _ hζ0), zpow_natCast, zpow_natCast, inv_pow,
              div_eq_mul_inv]
          have h2 : (ζ ^ (2 * j + 1)) ^ e = ζ ^ (((2 * j + 1 : ℕ) : ℤ) * e) := by
            rw [zpow_mul, zpow_natCast]
          have h3 : ζ ^ e * ((ζ ^ 2) ^ e) ^ j = ζ ^ (e + ((2 : ℤ) * e) * (j : ℤ)) := by
            rw [zpow_add₀ hζ0, zpow_mul, zpow_mul, zpow_ofNat, zpow_natCast]
          rw [h1, h2, h3]
          congr 1
          push_cast
          ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
        have hr1 : (ζ ^ 2) ^ e ≠ 1 := by
          intro h
          rw [hω.zpow_eq_one_iff_dvd] at h
          have h0 : e = 0 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
          omega
        have hrn : ((ζ ^ 2) ^ e) ^ n = 1 := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one,
            one_zpow]
        rw [geom_sum_eq hr1, hrn, sub_self, zero_div, mul_zero]
    have P : ∀ g : ℤ[X], g.natDegree < n →
        ∑ j ∈ range n, ‖aeval (frequency ζ j) g‖ ^ 2
          = (n : ℝ) * coefficientNormSq n g := by
      intro g hg
      have hw : ∀ j, ((‖aeval (frequency ζ j) g‖ : ℝ) : ℂ) ^ 2
          = ∑ k ∈ range n, ∑ l ∈ range n, (g.coeff k : ℂ) * (g.coeff l : ℂ) *
              (frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ l) := by
        intro j
        rw [← Complex.mul_conj', aeval_eq_sum_range' hg]
        simp only [zsmul_eq_mul, map_sum, map_mul, map_pow, map_intCast,
          ← Complex.inv_eq_conj (hz j)]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
      have key : ∑ j ∈ range n, ((‖aeval (frequency ζ j) g‖ : ℝ) : ℂ) ^ 2
          = (n : ℂ) * ∑ k ∈ range n, ((‖((g.coeff k : ℤ) : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
        calc ∑ j ∈ range n, ((‖aeval (frequency ζ j) g‖ : ℝ) : ℂ) ^ 2
            = ∑ j ∈ range n, ∑ k ∈ range n, ∑ l ∈ range n, (g.coeff k : ℂ) * (g.coeff l : ℂ) *
                (frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ l) :=
              Finset.sum_congr rfl (fun j _ => hw j)
          _ = ∑ k ∈ range n, ∑ l ∈ range n, ∑ j ∈ range n, (g.coeff k : ℂ) * (g.coeff l : ℂ) *
                (frequency ζ j ^ k * (frequency ζ j)⁻¹ ^ l) := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
          _ = ∑ k ∈ range n, ∑ l ∈ range n, (g.coeff k : ℂ) * (g.coeff l : ℂ) *
                (if k = l then (n : ℂ) else 0) := by
              refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => ?_))
              rw [← Finset.mul_sum, E k hk l hl]
          _ = ∑ k ∈ range n, (g.coeff k : ℂ) * (g.coeff k : ℂ) * (n : ℂ) := by
              refine Finset.sum_congr rfl (fun k hk => ?_)
              simp only [mul_ite, mul_zero]
              rw [Finset.sum_ite_eq, if_pos hk]
          _ = (n : ℂ) * ∑ k ∈ range n, ((‖((g.coeff k : ℤ) : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              have h5 : ((‖((g.coeff k : ℤ) : ℂ)‖ : ℝ) : ℂ) ^ 2
                  = (g.coeff k : ℂ) * (g.coeff k : ℂ) := by
                rw [← Complex.mul_conj', map_intCast]
              rw [h5]
              ring
      unfold coefficientNormSq
      exact_mod_cast key
    have hmonic : (X ^ n + 1 : ℤ[X]).Monic := by
      have h := monic_X_pow_add_C (1 : ℤ) hn.ne'
      simpa using h
    have hdeg : (X ^ n + 1 : ℤ[X]).natDegree = n := by
      have h := natDegree_X_pow_add_C (R := ℤ) (n := n) (r := 1)
      simpa using h
    have hne1 : (X ^ n + 1 : ℤ[X]) ≠ 1 := by
      intro h
      have h' := congrArg natDegree h
      rw [hdeg, natDegree_one] at h'
      omega
    have hrep : ∀ (f : ℤ[X]) (j : ℕ),
        aeval (frequency ζ j) (representative n f) = aeval (frequency ζ j) f := by
      intro f j
      unfold representative
      have h := modByMonic_add_div f (X ^ n + 1 : ℤ[X])
      have h2 := congrArg (aeval (frequency ζ j)) h
      rw [map_add, map_mul] at h2
      have h3 : aeval (frequency ζ j) (X ^ n + 1 : ℤ[X]) = 0 := by
        simp [hfreq j]
      rw [h3, zero_mul, add_zero] at h2
      exact h2
    have hdegrep : ∀ f : ℤ[X], (representative n f).natDegree < n := by
      intro f
      unfold representative
      have h := natDegree_modByMonic_lt f hmonic hne1
      rwa [hdeg] at h
    have step : ∀ i, (n : ℝ) * coefficientNormSq n (representative n (c * s i))
        = ∑ j ∈ range n, ‖aeval (frequency ζ j) c‖ ^ 2 * ‖aeval (frequency ζ j) (s i)‖ ^ 2 := by
      intro i
      rw [← P _ (hdegrep _)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hrep, map_mul, norm_mul, mul_pow]
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => step i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
