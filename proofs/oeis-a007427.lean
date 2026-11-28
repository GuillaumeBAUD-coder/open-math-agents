import OMAStatements.S_oeis_a007427
import Mathlib

/-!
Proof of Stephan's conjecture on A007427.

* a = mu * mu (Dirichlet convolution), since the first Moebius transform of 1,0,0,0,... is mu.
* For squarefree d and e, mu(d) mu(e) = (-1)^Omega(d e), so every nonzero term of a(n) has the
  sign (-1)^Omega(n) and |a(n)| = Sum_{d e = n} |mu(d)| |mu(e)|: |a| is |mu| convolved with |mu|.
* Every n ≥ 1 is uniquely (squarefree) times (square), so |mu| convolved with the indicator of
  the squares is the constant 1, and the L-series of that indicator at s is zeta(2s).
* Hence L(|mu|, s) zeta(2s) = zeta(s), and L(|a|, s) = L(|mu|, s)^2 = zeta(s)^2 / zeta(2s)^2.
-/

namespace OMA.P007427

open OMA.S_oeis_a007427
open ArithmeticFunction

/-- The first Moebius transform of 1,0,0,0,... is mu. -/
lemma mt_delta (n : ℕ) : moebiusTransform delta n = moebius n := by
  unfold moebiusTransform delta
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro d _ hd1
      simp [hd1]
    · intro h
      exact absurd (Nat.one_mem_divisors.mpr hn.ne') h

/-- a(n) = Sum_{d e = n} mu(d) mu(e). -/
lemma a_eq (n : ℕ) : a n = ∑ p ∈ n.divisorsAntidiagonal, moebius p.1 * moebius p.2 := by
  unfold a
  rw [moebiusTransform]
  simp_rw [mt_delta]
  rw [Nat.sum_divisorsAntidiagonal (fun i j => moebius i * moebius j)]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- mu(d) mu(e) = (-1)^Omega(d e) |mu(d)| |mu(e)| for nonzero d, e. -/
lemma term_eq (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) :
    moebius d * moebius e = (-1) ^ cardFactors (d * e) * (|moebius d| * |moebius e|) := by
  by_cases h1 : Squarefree d
  · by_cases h2 : Squarefree e
    · rw [moebius_apply_of_squarefree h1, moebius_apply_of_squarefree h2, cardFactors_mul hd he,
        pow_add]
      simp [abs_pow]
    · simp [moebius_eq_zero_of_not_squarefree h2]
  · simp [moebius_eq_zero_of_not_squarefree h1]

/-- |a(n)| = Sum_{d e = n} |mu(d)| |mu(e)|. -/
lemma abs_a (n : ℕ) :
    |a n| = ∑ p ∈ n.divisorsAntidiagonal, |moebius p.1| * |moebius p.2| := by
  have h : a n = (-1) ^ cardFactors n *
      ∑ p ∈ n.divisorsAntidiagonal, |moebius p.1| * |moebius p.2| := by
    rw [a_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    obtain ⟨h1, h2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp
    rw [term_eq p.1 p.2 h1 h2, hp'.1]
  rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- |mu| as a complex sequence. -/
noncomputable def F (n : ℕ) : ℂ := ((|moebius n| : ℤ) : ℂ)

/-- The indicator of the squares. -/
noncomputable def Q (n : ℕ) : ℂ := if IsSquare n then 1 else 0

lemma absa_eq_conv (n : ℕ) : ((|a n| : ℤ) : ℂ) = LSeries.convolution F F n := by
  rw [LSeries.convolution_def, abs_a n]
  push_cast
  rfl

/-- The squarefree part is unique: x u^2 = y v^2 with x, y squarefree forces x = y. -/
lemma sqf_unique (x y u v : ℕ) (hx : Squarefree x) (hy : Squarefree y) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : x * u ^ 2 = y * v ^ 2) : x = y := by
  have hx0 : x ≠ 0 := hx.ne_zero
  have hy0 : y ≠ 0 := hy.ne_zero
  apply Nat.eq_of_factorization_eq hx0 hy0
  intro p
  have e := congrArg (fun m => Nat.factorization m p) h
  rw [Nat.factorization_mul hx0 (pow_ne_zero 2 hu), Nat.factorization_mul hy0 (pow_ne_zero 2 hv),
    Nat.factorization_pow, Nat.factorization_pow] at e
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at e
  have h1 := hx.natFactorization_le_one p
  have h2 := hy.natFactorization_le_one p
  omega

/-- |mu| convolved with the indicator of the squares is 1 at every n ≥ 1. -/
lemma conv_FQ (n : ℕ) (hn : n ≠ 0) : LSeries.convolution F Q n = 1 := by
  obtain ⟨x, b, hx0, hb0, hxb, hx⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  rw [LSeries.convolution_def]
  simp only
  have hmem : (x, b ^ 2) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by rw [← hxb]; ring, hn⟩
  have hsq : IsSquare (b ^ 2) := ⟨b, sq b⟩
  rw [Finset.sum_eq_single (x, b ^ 2)]
  · simp [F, Q, hx, hsq]
  · rintro ⟨d, e⟩ hp hne
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    simp only at hp'
    by_cases hd : Squarefree d
    · by_cases he : IsSquare e
      · exfalso
        obtain ⟨c, rfl⟩ := he
        have hc : c ≠ 0 := by
          rintro rfl
          apply hp'.2
          rw [← hp'.1]
          ring
        have h1 : d * c ^ 2 = x * b ^ 2 := by
          calc d * c ^ 2 = d * (c * c) := by ring
            _ = n := hp'.1
            _ = b ^ 2 * x := hxb.symm
            _ = x * b ^ 2 := by ring
        have hdx : d = x := sqf_unique d x c b hd hx hc hb0.ne' h1
        subst hdx
        have h2 : c ^ 2 = b ^ 2 := Nat.eq_of_mul_eq_mul_left hx0 h1
        apply hne
        rw [← h2, sq]
      · simp [Q, he]
    · simp [F, hd]
  · intro h
    exact absurd hmem h

lemma F_bound (n : ℕ) : ‖F n‖ ≤ 1 := by
  simp only [F, abs_moebius]
  split_ifs <;> simp

lemma Q_bound (n : ℕ) : ‖Q n‖ ≤ 1 := by
  simp only [Q]
  split_ifs <;> simp

/-- The L-series of the indicator of the squares at s is zeta(2s). -/
lemma LSeries_Q (s : ℂ) (hs : 1 < s.re) : LSeries Q s = riemannZeta (2 * s) := by
  have h2 : 1 < (2 * s).re := by
    simp
    linarith
  rw [← LSeries_one_eq_riemannZeta h2, LSeries, LSeries]
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := by
    intro m k hmk
    simpa using hmk
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
      have hsq : IsSquare (m ^ 2) := ⟨m, sq m⟩
      have hQ : Q (m ^ 2) = 1 := by simp [Q, hsq]
      rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm, hQ, Pi.one_apply]
      congr 1
      have hc : ((m ^ 2 : ℕ) : ℂ) = (m : ℂ) * (m : ℂ) := by push_cast; ring
      rw [hc, Complex.natCast_mul_natCast_cpow, two_mul,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hm)]
  · intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact absurd (LSeries.term_zero _ _) hn
    · rw [LSeries.term_of_ne_zero hn0] at hn
      by_cases hq : IsSquare n
      · obtain ⟨r, rfl⟩ := hq
        exact ⟨r, by simp [sq]⟩
      · simp [Q, hq] at hn

theorem sol : type_of% @OMA.S_oeis_a007427.main := by
  intro s hs
  have hF : LSeriesSummable F s := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ => F_bound n) hs
  have hQ : LSeriesSummable Q s := LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ => Q_bound n) hs
  have hcongr : ∀ {n : ℕ}, n ≠ 0 →
      (fun n => ((|a n| : ℤ) : ℂ)) n = LSeries.convolution F F n :=
    fun {n} _ => absa_eq_conv n
  have h2 : 1 < (2 * s).re := by
    simp
    linarith
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2
  have hLF : LSeries F s = riemannZeta s / riemannZeta (2 * s) := by
    rw [eq_div_iff hz2, ← LSeries_Q s hs, ← LSeries_convolution' hF hQ,
      ← LSeries_one_eq_riemannZeta hs]
    exact LSeries_congr (fun {n} hn => by rw [conv_FQ n hn]; rfl) s
  refine ⟨?_, ?_⟩
  · rw [LSeriesSummable_congr s hcongr]
    exact hF.convolution hF
  · rw [LSeries_congr hcongr s, LSeries_convolution' hF hF, hLF]
    ring

end OMA.P007427

theorem OMA.solution : type_of% @OMA.S_oeis_a007427.main := OMA.P007427.sol

