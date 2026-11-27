import FormalConjectures.ErdosProblems.«12»

/-!
# Baier's bound for pairwise coprime sets with the Erdős–Sárközy property

S. Baier, A note on P-sets, Integers 4 (2004), A13. Let `A` be good and pairwise coprime.

* Arithmetic large sieve (Baier, Lemma 2): the moduli are the products of distinct elements
  of `D = A ∩ (2, Q]`, and the frequencies are the sums `a₁/q₁ + ... + a_r/q_r` with every
  `a_i` nonzero modulo `q_i`. They are `1/Q²`-separated modulo one, and each product carries
  energy at least `|B|²` where `B = A ∩ (Q, Q²]`. Hence `F(Q) * |B| ≤ 100 Q²`, where `F(Q)`
  counts the subsets of `D` with product at most `Q`.
* Baier's Lemma 3 (Lucht's mean value theorem) is replaced by Rankin's trick, since the
  constant of the statement is free: if the counting function of `A` exceeded
  `100 N^(2/3) / log N` for all large `N`, then `F(Q) ≤ 4 Q^(2/3) log Q`, and the Euler product
  `∑_{I ⊆ D} (∏ I)^(-s) = ∏_{q ∈ D} (1 + q^(-s))` at `s = 2/3 + 1/J` would be both at least
  `c J^3` and at most `K J^2`.

The Fourier analytic lemmas are copied from the merged proof of
`Erdos12.erdos_12.variants.schoen` (P. Papageorgiou).
-/

open Finset Real MeasureTheory Set
open scoped ComplexConjugate

namespace Baier

noncomputable def phase (b : ℕ) (x : ℝ) : ℂ := fourier (b : ℤ) (x : AddCircle (1 : ℝ))

noncomputable def wave (B : Finset ℕ) (x : ℝ) : ℂ := ∑ b ∈ B, phase b x

lemma phase_cont (b : ℕ) : Continuous (phase b) :=
  (fourier (T := 1) (b : ℤ)).continuous.comp (AddCircle.continuous_mk' 1)

lemma phase_orthogonal (b c : ℕ) :
    (∫ x : ℝ in 0..1, conj (phase b x) * phase c x) = if b = c then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) (c : ℤ)) (b : ℤ)
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at h
  simpa only [zero_add, div_one, one_smul, smul_eq_mul, fourier_neg,
    Pi.single_apply, Int.natCast_inj, eq_comm, phase] using h

lemma parseval (B : Finset ℕ) (u : ℕ → ℂ) :
    (∫ x : ℝ in 0..1, ‖∑ b ∈ B, u b * phase b x‖ ^ 2) = ∑ b ∈ B, ‖u b‖ ^ 2 := by
  let term (b c : ℕ) (x : ℝ) := (conj (u b) * u c) * (conj (phase b x) * phase c x)
  have ht (b c) : Continuous (term b c) :=
    continuous_const.mul ((Complex.continuous_conj.comp (phase_cont b)).mul (phase_cont c))
  have hex (x : ℝ) : ((‖∑ b ∈ B, u b * phase b x‖ ^ 2 : ℝ) : ℂ) =
      ∑ b ∈ B, ∑ c ∈ B, term b c x := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum, sum_mul]
    apply sum_congr rfl
    intro b _
    rw [map_mul, mul_sum]
    apply sum_congr rfl
    intro c _
    dsimp [term]
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (fun b _ => (continuous_finsetSum B (fun c _ => ht b c)).intervalIntegrable _ _)]
  push_cast
  apply sum_congr rfl
  intro b hb
  rw [intervalIntegral.integral_finsetSum (fun c _ => (ht b c).intervalIntegrable _ _)]
  simp only [term, intervalIntegral.integral_const_mul, phase_orthogonal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq B b (fun c => conj (u b) * u c), if_pos hb]
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]

/-- Bound the value at the left endpoint by integrating the derivative of the squared norm. -/
lemma sample_interval {F G : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : Continuous G) (a L : ℝ) (hL : 0 < L) :
    ‖F a‖ ^ 2 ≤ ∫ x in a..a + L, (2 / L) * ‖F x‖ ^ 2 + L * ‖G x‖ ^ 2 := by
  let f (x : ℝ) := ‖F x‖ ^ 2
  let g (x : ℝ) := 2 * inner ℝ (F x) (G x)
  let v (x : ℝ) := (1 / L) * f x + L * ‖G x‖ ^ 2
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hcf : Continuous f := hcF.norm.pow 2
  have hcg : Continuous g := continuous_const.mul (hcF.inner hG)
  have hcv : Continuous v := ((continuous_const.mul hcf).add (continuous_const.mul (hG.norm.pow 2)))
  have hnv (x) : 0 ≤ v x := by dsimp [v, f]; positivity
  have hg (x : ℝ) : -g x ≤ v x := by
    have hi := (neg_le_abs (inner ℝ (F x) (G x))).trans (abs_real_inner_le_norm _ _)
    change -(2 * inner ℝ (F x) (G x)) ≤ (1 / L) * ‖F x‖ ^ 2 + L * ‖G x‖ ^ 2
    apply (mul_le_mul_iff_of_pos_left hL).mp
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hL.ne', one_mul]
    nlinarith [sq_nonneg (‖F x‖-L * ‖G x‖), mul_le_mul_of_nonneg_left hi hL.le]
  have sub (x : ℝ) (hx : x ∈ Set.Icc a (a + L)) :
      f a - f x ≤ ∫ y in a..a + L, v y := by
    have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := x)
      (f := f) (f':=g) (fun y _ => (hF y).norm_sq) (hcg.intervalIntegrable _ _)
    have h1 := intervalIntegral.integral_mono_on (μ := volume) hx.1 (hcg.neg.intervalIntegrable a x)
      (hcv.intervalIntegrable a x) (fun y _ => hg y)
    change (∫ y in a..x, -g y) ≤ ∫ y in a..x, v y at h1
    rw [intervalIntegral.integral_neg, ftc] at h1
    have h2 := intervalIntegral.integral_mono_interval (μ := volume) (le_refl a) hx.1 hx.2
      (Filter.Eventually.of_forall hnv) (hcv.intervalIntegrable a (a + L))
    linarith
  have ha : a ≤ a + L := by linarith
  have hmean := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => f a)
    (g := fun x => f x + ∫ y in a..a + L, v y) ha (continuous_const.intervalIntegrable _ _)
    ((hcf.add continuous_const).intervalIntegrable _ _) (fun x hx => by linarith only [sub x hx])
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hcf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const] at hmean
  simp only [add_sub_cancel_left, smul_eq_mul] at hmean
  have hsplit : (∫ x in a..a + L, (2 / L) * ‖F x‖ ^ 2 + L * ‖G x‖ ^ 2) =
      (1 / L) * (∫ x in a..a + L, f x) + ∫ x in a..a + L, v x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (f := fun x => (1 / L) * f x) (g := v)
      ((continuous_const.mul hcf).intervalIntegrable _ _) (hcv.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [v, f]
    ring
  rw [hsplit]
  change f a ≤ _
  apply (mul_le_mul_iff_of_pos_left hL).mp
  rw [mul_add, ← mul_assoc, mul_one_div_cancel hL.ne', one_mul]
  exact hmean

lemma count_segment (A : Set ℕ) (a b : ℕ) [DecidablePred (· ∈ A)] :
    (A ∩ Set.Icc 1 b).ncard ≤ a + ((Finset.Ioc a b).filter (· ∈ A)).card := by
  let small := Finset.Icc 1 a
  let large := (Finset.Ioc a b).filter (· ∈ A)
  have h : A ∩ Set.Icc 1 b ⊆ ↑(small ∪ large) := by
    intro x hx
    rcases hx with ⟨hA, hl, hr⟩
    by_cases hx : x ≤ a
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hl, hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hr⟩, hA⟩)
  have hh := Set.ncard_le_ncard h
  rw [Set.ncard_coe_finset] at hh
  simpa [small, large, Nat.card_Icc] using hh.trans (Finset.card_union_le small large)



/- ## The analytic large sieve for separated points (from the merged count_product) -/

lemma large_sieve_points {ι : Type*} (S : Finset ι) (θ : ι → ℝ) (B : Finset ℕ) (N : ℕ)
    (hN : 0 < N) (hB : ∀ b ∈ B, b ≤ N)
    (hθ : ∀ p ∈ S, 0 ≤ θ p ∧ θ p + 1 / (N : ℝ) ≤ 1)
    (hsep : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      θ p + 1 / (N : ℝ) ≤ θ r ∨ θ r + 1 / (N : ℝ) ≤ θ p) :
    ∑ p ∈ S, ‖wave B (θ p)‖ ^ 2 ≤ 100 * N * B.card := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let L : ℝ := 1 / (N : ℝ)
  have hL : 0 < L := one_div_pos.mpr hNpos
  let u (b : ℕ) : ℂ := 2 * Real.pi * Complex.I * b
  let G (x : ℝ) := ∑ b ∈ B, u b * phase b x
  have hG : Continuous G := continuous_finsetSum B fun b _ => continuous_const.mul (phase_cont b)
  have hF : ∀ x, HasDerivAt (wave B) (G x) x := by
    intro x
    apply HasDerivAt.fun_sum
    intro b _
    change HasDerivAt (fun y : ℝ => fourier (b : ℤ) (y : AddCircle (1 : ℝ))) (u b * phase b x) x
    simpa only [phase, u, Int.cast_natCast, Complex.ofReal_one, div_one] using
      hasDerivAt_fourier 1 (b : ℤ) x
  let W (x : ℝ) := (2 / L) * ‖wave B x‖ ^ 2 + L * ‖G x‖ ^ 2
  have hcF : Continuous (wave B) := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hcW : Continuous W := (continuous_const.mul (hcF.norm.pow 2)).add
    (continuous_const.mul (hG.norm.pow 2))
  have hW (x) : 0 ≤ W x := by dsimp [W]; positivity
  let J (p : ι) := Set.Ioc (θ p) (θ p + L)
  have hdis : (S : Set ι).Pairwise (Function.onFun Disjoint J) := by
    intro p hp r hr hne
    have sep := hsep p hp r hr hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    change θ p < x ∧ x ≤ θ p + L at hx
    change θ r < x ∧ x ≤ θ r + L at hy
    change θ p + L ≤ θ r ∨ θ r + L ≤ θ p at sep
    rcases sep with h | h <;> linarith only [hx.1, hx.2, hy.1, hy.2, h]
  have hunion : (⋃ p ∈ S, J p) ⊆ Set.Ioc 0 1 := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(hθ p hp).1.trans_lt hx.1, hx.2.trans (hθ p hp).2⟩
  have htotal : ∑ p ∈ S, ‖wave B (θ p)‖ ^ 2 ≤ ∫ x in (0 : ℝ)..1, W x := by
    calc
      _ ≤ ∑ p ∈ S, ∫ x in J p, W x := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [intervalIntegral.integral_of_le (show θ p ≤ θ p + L by linarith only [hL])]
          using sample_interval hF hG (θ p) L hL
      _ = ∫ x in ⋃ p ∈ S, J p, W x := (integral_biUnion_finset S
        (fun _ _ => measurableSet_Ioc) hdis (fun _ _ => (hcW.intervalIntegrable _ _).1)).symm
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact setIntegral_mono_set (hcW.intervalIntegrable 0 1).1 (Filter.Eventually.of_forall hW)
          (Filter.Eventually.of_forall hunion)
  have hmass : (∫ x in (0 : ℝ)..1, ‖wave B x‖ ^ 2) = B.card := by
    simpa only [one_mul, wave, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      using parseval B (fun _ => 1)
  have hder : (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) ≤ (B.card : ℝ) * (8 * (N : ℝ)) ^ 2 := by
    rw [show (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) = _ from parseval B u]
    calc
      _ ≤ ∑ b ∈ B, (8 * (N : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        have hb' : (b : ℝ) ≤ N := by exact_mod_cast hB b hb
        have hh : ‖u b‖ ≤ 8 * (N : ℝ) := by
          simp only [u, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_natCast]
          nlinarith only [hb', mul_nonneg (show 0 ≤ (b : ℝ) by positivity)
            (le_of_lt (sub_pos.mpr Real.pi_lt_four))]
        exact pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by simp
  have hupper : (∫ x in (0 : ℝ)..1, W x) ≤ 100 * (N : ℝ) * B.card := by
    dsimp only [W]
    rw [intervalIntegral.integral_add (f := fun x => (2 / L) * ‖wave B x‖ ^ 2)
        (g := fun x => L * ‖G x‖ ^ 2)
        ((continuous_const.mul (hcF.norm.pow 2)).intervalIntegrable _ _)
        ((continuous_const.mul (hG.norm.pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmass]
    dsimp only [L]
    field_simp
    nlinarith only [hder, mul_nonneg (sq_nonneg (N : ℝ)) (Nat.cast_nonneg (α := ℝ) B.card)]
  exact htotal.trans hupper

/-- The Fourier sum only depends on the point modulo one. -/
lemma wave_fract (B : Finset ℕ) (x : ℝ) : wave B (Int.fract x) = wave B x := by
  simp only [wave, phase, AddCircle.coe_fract]

/- ## Frequencies attached to the products of distinct moduli -/

/-- The frequency `∑_{q ∈ I} a_q / q`. -/
noncomputable def theta (I : Finset ℕ) (a : (q : ℕ) → q ∈ I → ℕ) : ℝ :=
  ∑ q ∈ I.attach, (a q.1 q.2 : ℝ) / (q.1 : ℝ)

private def digit (I : Finset ℕ) (a : (q : ℕ) → q ∈ I → ℕ) (q : ℕ) : ℕ :=
  if h : q ∈ I then a q h else 0

private def weight (U : Finset ℕ) (q : ℕ) := ∏ r ∈ U.erase q, r

private def numerator (U : Finset ℕ) (v : ℕ → ℕ) := ∑ q ∈ U, v q * weight U q

private lemma theta_grid {U I : Finset ℕ} (h : I ⊆ U) (hp : ∀ q ∈ U, 0 < q)
    (a : (q : ℕ) → q ∈ I → ℕ) :
    Int.fract (theta I a) =
      ((numerator U (digit I a) % (∏ r ∈ U, r) : ℕ) : ℝ) / (∏ r ∈ U, r : ℕ) := by
  let K := ∏ r ∈ U, r
  have hK : 0 < K := Finset.prod_pos hp
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have ht : theta I a = ∑ q ∈ U, (digit I a q : ℝ) / q := by
    calc
      _ = ∑ q ∈ I.attach, (digit I a q.1 : ℝ) / q.1 := by
        apply sum_congr rfl
        intro q _
        simp [digit, q.2]
      _ = ∑ q ∈ I, (digit I a q : ℝ) / q :=
        Finset.sum_attach I (fun q => (digit I a q : ℝ) / q)
      _ = _ := Finset.sum_subset h fun q _ hq => by simp [digit, hq]
  have he : theta I a = (numerator U (digit I a) : ℝ) / K := by
    rw [eq_div_iff hk.ne', ht, Finset.sum_mul, numerator, Nat.cast_sum]
    apply sum_congr rfl
    intro q hq
    have hh : (weight U q : ℝ) * q = (K : ℝ) := by
      exact_mod_cast Finset.prod_erase_mul U (fun r => r) hq
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (hp q hq).ne'
    rw [← hh, Nat.cast_mul]
    field_simp
  rw [he, Int.fract_div_natCast_eq_div_natCast_mod]

/-- Energy of a product of moduli: if no modulus of `I` divides a sum of two elements of `B`,
the frequencies of `I` carry at least `|B|²` (the signed sum of the squares is `± |B|²`). -/
lemma product_energy (I B : Finset ℕ) (hI : ∀ q ∈ I, 0 < q)
    (hn : ∀ q ∈ I, ∀ b ∈ B, ∀ c ∈ B, ¬ q ∣ b + c) :
    (B.card : ℝ) ^ 2 ≤
      ∑ a ∈ I.pi (fun q => (Finset.range q).erase 0), ‖wave B (theta I a)‖ ^ 2 := by
  classical
  let T (q : ℕ) := (range q).erase 0
  have heval (d : ℕ) (a : (q : ℕ) → q ∈ I → ℕ) :
      phase d (theta I a) = ∏ q ∈ I.attach, phase d ((a q.1 q.2 : ℝ) / q.1) := by
    simp only [theta, phase, fourier_coe_apply, Complex.ofReal_one, div_one,
      Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  have hone (q : ℕ) (hq : q ∈ I) (d : ℕ) (hnd : ¬q ∣ d) :
      ∑ k ∈ T q, phase d ((k : ℝ) / q) = -1 := by
    let z := Complex.exp (2 * Real.pi * Complex.I / q)
    have hz : IsPrimitiveRoot z q := Complex.isPrimitiveRoot_exp q (hI q hq).ne'
    have hchar (k : ℕ) : phase d ((k : ℝ) / q) = (z ^ d) ^ k := by
      simp only [phase, fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_div,
        Complex.ofReal_natCast, Int.cast_natCast, z, ← Complex.exp_nat_mul]
      congr 1
      ring
    have hp : (z ^ d) ^ q = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    have hg := geom_sum_mul (z ^ d) q
    rw [hp, sub_self, mul_eq_zero] at hg
    have hzero := hg.resolve_right (sub_ne_zero.mpr (mt (hz.pow_eq_one_iff_dvd _).mp hnd))
    simp_rw [hchar]
    apply eq_neg_of_add_eq_zero_left
    simpa [T] using (Finset.sum_erase_add (range q) (fun k => (z ^ d) ^ k)
      (Finset.mem_range.mpr (hI q hq))).trans hzero
  have hpair (b : ℕ) (hb : b ∈ B) (c : ℕ) (hc : c ∈ B) :
      ∑ a ∈ I.pi T, phase b (theta I a) * phase c (theta I a) = (-1 : ℂ) ^ I.card := by
    have hadd (x : ℝ) : phase b x * phase c x = phase (b+c) x := by
      simp only [phase, Nat.cast_add, fourier_add]
    simp_rw [hadd, heval]
    rw [← Finset.prod_sum I T (fun q k => phase (b+c) ((k : ℝ) / q))]
    calc
      _ = ∏ q ∈ I, (-1 : ℂ) :=
        prod_congr rfl fun q hq => hone q hq (b+c) (hn q hq b hb c hc)
      _ = _ := by simp
  have hs : ∑ a ∈ I.pi T, wave B (theta I a) ^ 2 =
      (B.card : ℂ) ^ 2 * (-1 : ℂ) ^ I.card := by
    simp only [wave, sq, sum_mul, mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ b ∈ B, ∑ c ∈ B, (-1 : ℂ) ^ I.card := by
        apply sum_congr rfl
        intro b hb
        rw [sum_comm]
        exact sum_congr rfl fun c hc => hpair c hc b hb
      _ = _ := by simp [mul_assoc]
  have ht := norm_sum_le (I.pi T) (fun a => wave B (theta I a) ^ 2)
  rw [hs] at ht
  simpa [norm_mul, norm_pow, T] using ht

private lemma numerator_residue {U : Finset ℕ} {q : ℕ} (hq : q ∈ U) (v : ℕ → ℕ) :
    numerator U v ≡ v q * weight U q [MOD q] := by
  have hdiv : q ∣ ∑ r ∈ U.erase q, v r * weight U r := by
    apply Finset.dvd_sum
    intro r hr
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun x : ℕ => x)
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1.symm, hq⟩ : q ∈ U.erase r)) _
  unfold numerator
  rw [← Finset.sum_erase_add U (fun r => v r * weight U r) hq]
  simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr hdiv).add
    (Nat.ModEq.refl (v q * weight U q))

private lemma digit_lt {I : Finset ℕ} {a : (q : ℕ) → q ∈ I → ℕ}
    (ha : a ∈ I.pi (fun q => (range q).erase 0)) {q : ℕ} (hq : 0 < q) :
    digit I a q < q := by
  by_cases h : q ∈ I
  · simpa [digit, h] using Finset.mem_range.mp (Finset.mem_erase.mp ((Finset.mem_pi.mp ha) q h)).2
  · simpa [digit, h] using hq

private lemma digit_support {I : Finset ℕ} {a : (q : ℕ) → q ∈ I → ℕ}
    (ha : a ∈ I.pi (fun q => (range q).erase 0)) (q : ℕ) : q ∈ I ↔ digit I a q ≠ 0 := by
  by_cases h : q ∈ I
  · simp [digit, h, (Finset.mem_erase.mp ((Finset.mem_pi.mp ha) q h)).1]
  · simp [digit, h]

/-- Two distinct frequencies with products at most `Q` are `1/Q²`-separated modulo one. -/
lemma product_separated {Q : ℕ} {D I J : Finset ℕ} {a : (q : ℕ) → q ∈ I → ℕ}
    {b : (q : ℕ) → q ∈ J → ℕ}
    (hcop : (D : Set ℕ).Pairwise Nat.Coprime) (hpos : ∀ q ∈ D, 0 < q)
    (hI : I ⊆ D) (hJ : J ⊆ D) (hIQ : ∏ q ∈ I, q ≤ Q) (hJQ : ∏ q ∈ J, q ≤ Q)
    (ha : a ∈ I.pi (fun q => (Finset.range q).erase 0))
    (hb : b ∈ J.pi (fun q => (Finset.range q).erase 0))
    (hne : (⟨I, a⟩ : (I : Finset ℕ) × ((q : ℕ) → q ∈ I → ℕ)) ≠ ⟨J, b⟩) :
    Int.fract (theta I a) + 1 / ((Q : ℝ) ^ 2) ≤ Int.fract (theta J b) ∨
      Int.fract (theta J b) + 1 / ((Q : ℝ) ^ 2) ≤ Int.fract (theta I a) := by
  let U := I ∪ J
  have hi : I ⊆ U := Finset.subset_union_left
  have hj : J ⊆ U := Finset.subset_union_right
  have hu : U ⊆ D := Finset.union_subset hI hJ
  have hp : ∀ q ∈ U, 0 < q := fun q hq => hpos q (hu hq)
  let K := ∏ r ∈ U, r
  have hk : 0 < K := Finset.prod_pos hp
  have hk' : (0 : ℝ) < K := by exact_mod_cast hk
  have hKQ : K ≤ Q ^ 2 := by
    have h1 : 0 < ∏ r ∈ I ∩ J, r := Finset.prod_pos fun q hq => hpos q (hI (mem_inter.mp hq).1)
    calc
      K ≤ K * ∏ r ∈ I ∩ J, r := Nat.le_mul_of_pos_right _ h1
      _ = (∏ r ∈ I, r) * ∏ r ∈ J, r := Finset.prod_union_inter
      _ ≤ Q ^ 2 := by simpa [sq] using Nat.mul_le_mul hIQ hJQ
  let m := numerator U (digit I a) % K
  let n := numerator U (digit J b) % K
  have hmn : m ≠ n := by
    intro e
    have he : numerator U (digit I a) ≡ numerator U (digit J b) [MOD K] := e
    have hd (q : ℕ) (hq : q ∈ U) : digit I a q = digit J b q := by
      have hqk : q ∣ K := Finset.dvd_prod_of_mem (fun r => r) hq
      have hc : q.Coprime (weight U q) := Nat.Coprime.prod_right fun r hr =>
        hcop (hu hq) (hu (mem_erase.mp hr).2) (mem_erase.mp hr).1.symm
      have hmod := ((numerator_residue hq (digit I a)).symm.trans (he.of_dvd hqk)).trans
        (numerator_residue hq (digit J b))
      exact (hmod.cancel_right_of_coprime hc).eq_of_lt_of_lt (digit_lt ha (hp q hq))
        (digit_lt hb (hp q hq))
    have hij : I = J := by
      ext q
      constructor
      · intro hq
        exact (digit_support hb q).mpr ((hd q (hi hq)) ▸ (digit_support ha q).mp hq)
      · intro hq
        exact (digit_support ha q).mpr ((hd q (hj hq)).symm ▸ (digit_support hb q).mp hq)
    subst J
    have hab : a = b := by
      funext q hq
      simpa [digit, hq] using hd q (hi hq)
    exact hne (hab ▸ rfl)
  rw [theta_grid hi hp a, theta_grid hj hp b]
  change (m : ℝ) / K + 1 / (Q : ℝ) ^ 2 ≤ (n : ℝ) / K ∨
    (n : ℝ) / K + 1 / (Q : ℝ) ^ 2 ≤ (m : ℝ) / K
  have hrec := one_div_le_one_div_of_le hk' (show (K : ℝ) ≤ (Q : ℝ)^2 by exact_mod_cast hKQ)
  have hstep (i j : ℕ) (hij : i < j) : (i : ℝ) / K + 1 / (Q : ℝ)^2 ≤ (j : ℝ) / K := by
    refine (add_le_add (le_refl _) hrec).trans ?_
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij : (i : ℝ) + 1 ≤ j) hk'.le
  exact (lt_or_gt_of_ne hmn).imp (hstep m n) (hstep n m)

/-- A frequency with product at most `Q` stays `1/Q²` away from one. -/
lemma product_endpoint {Q : ℕ} {I : Finset ℕ} {a : (q : ℕ) → q ∈ I → ℕ} (hQ : 0 < Q)
    (hpos : ∀ q ∈ I, 0 < q) (hIQ : ∏ q ∈ I, q ≤ Q) :
    Int.fract (theta I a) + 1 / ((Q : ℝ) ^ 2) ≤ 1 := by
  rw [theta_grid (U := I) (fun _ h => h) hpos]
  let K := ∏ r ∈ I, r
  have hk : 0 < K := Finset.prod_pos hpos
  have hk' : (0 : ℝ) < K := by exact_mod_cast hk
  have hbig : (K : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast hIQ.trans (by simpa [sq] using Nat.le_mul_of_pos_right Q hQ : Q ≤ Q ^ 2)
  have hh : ((numerator I (digit I a) % K : ℕ) : ℝ) + 1 ≤ K := by
    exact_mod_cast Nat.mod_lt _ hk
  have he := (div_le_one hk').mpr hh
  rw [add_div] at he
  exact (add_le_add (le_refl _) (one_div_le_one_div_of_le hk' hbig)).trans he

/-- Number of subsets of `D` whose product is at most `y`. -/
def Fcount (D : Finset ℕ) (y : ℕ) : ℕ := (D.powerset.filter (fun I => ∏ i ∈ I, i ≤ y)).card

/-- Baier's Lemma 2: the arithmetic large sieve with the products of distinct moduli. -/
lemma count_products (Q : ℕ) (D B : Finset ℕ) (hQ : 0 < Q)
    (hD : ∀ d ∈ D, 2 < d ∧ d ≤ Q) (hB : ∀ b ∈ B, b ≤ Q ^ 2)
    (hcop : (D : Set ℕ).Pairwise Nat.Coprime)
    (hn : ∀ d ∈ D, ∀ b ∈ B, ∀ c ∈ B, ¬ d ∣ b + c) :
    Fcount D Q * B.card ≤ 100 * Q ^ 2 := by
  classical
  let P := D.powerset.filter (fun I => ∏ i ∈ I, i ≤ Q)
  let T := fun I : Finset ℕ => I.pi (fun q => (range q).erase 0)
  let θ := fun p : (I : Finset ℕ) × ((q : ℕ) → q ∈ I → ℕ) => Int.fract (theta p.1 p.2)
  have hpos (q : ℕ) (hq : q ∈ D) : 0 < q := by have := (hD q hq).1; omega
  have hmem {I : Finset ℕ} (h : I ∈ P) : I ⊆ D ∧ (∏ q ∈ I, q) ≤ Q :=
    ⟨mem_powerset.mp (mem_filter.mp h).1, (mem_filter.mp h).2⟩
  have hupper := large_sieve_points (P.sigma T) θ B (Q^2) (by positivity) hB
    (fun p hp => by
      obtain ⟨hI, _⟩ := mem_sigma.mp hp
      obtain ⟨hi, hQ'⟩ := hmem hI
      exact ⟨Int.fract_nonneg _, by simpa [θ] using
        (product_endpoint (a := p.2) hQ (fun q hq => hpos q (hi hq)) hQ')⟩)
    (fun p hp r hr hne => by
      obtain ⟨hI, ha⟩ := mem_sigma.mp hp
      obtain ⟨hJ, hb⟩ := mem_sigma.mp hr
      obtain ⟨hi, hIQ⟩ := hmem hI
      obtain ⟨hj, hJQ⟩ := hmem hJ
      simpa only [θ, Nat.cast_pow] using product_separated hcop hpos hi hj hIQ hJQ ha hb hne)
  have hlower : (P.card : ℝ) * (B.card : ℝ)^2 ≤ ∑ p ∈ P.sigma T, ‖wave B (θ p)‖^2 := by
    rw [Finset.sum_sigma]
    calc
      _ = ∑ I ∈ P, (B.card : ℝ)^2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro I hI
        have hi := (hmem hI).1
        simpa only [T, θ, wave_fract] using
          product_energy I B (fun q hq => hpos q (hi hq)) (fun q hq => hn q (hi hq))
  by_cases hb : B.card = 0
  · simp [hb]
  have hb' : (0 : ℝ) < B.card := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hh := hlower.trans hupper
  rw [sq (B.card : ℝ), ← mul_assoc] at hh
  exact_mod_cast (le_of_mul_le_mul_right hh hb')


/- ## Counting and Rankin's trick -/

open Classical in
/-- The elements of `A` in `(2, Q]`. -/
noncomputable def dset (A : Set ℕ) (Q : ℕ) : Finset ℕ := (Finset.Ioc 2 Q).filter (· ∈ A)

lemma mem_dset {A : Set ℕ} {Q x : ℕ} : x ∈ dset A Q ↔ (2 < x ∧ x ≤ Q) ∧ x ∈ A := by
  classical
  simp [dset]

/-- A subset with product at most `y` of elements at least one lies below `y`. -/
lemma Fcount_mono (A : Set ℕ) (X y : ℕ) : Fcount (dset A X) y ≤ Fcount (dset A y) y := by
  classical
  apply Finset.card_le_card
  intro I hI
  obtain ⟨hsub, hp⟩ := Finset.mem_filter.mp hI
  have h := Finset.mem_powerset.mp hsub
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hp⟩
  intro i hi
  obtain ⟨⟨hlt, _⟩, hA⟩ := mem_dset.mp (h hi)
  refine mem_dset.mpr ⟨⟨hlt, le_trans ?_ hp⟩, hA⟩
  exact Finset.single_le_prod' (f := fun k : ℕ => k)
    (fun k hk => by have := (mem_dset.mp (h hk)).1.1; omega) hi

/-- The Euler product at `s` and the inequality `exp (u/2) ≤ 1 + u` on `[0, 1]`. -/
lemma euler_lower (D : Finset ℕ) (s : ℝ) (hs : 0 < s) (hD : ∀ d ∈ D, 1 ≤ d) :
    Real.exp ((∑ d ∈ D, (d : ℝ) ^ (-s)) / 2) ≤
      ∑ I ∈ D.powerset, ((∏ i ∈ I, i : ℕ) : ℝ) ^ (-s) := by
  classical
  rw [Finset.sum_div, Real.exp_sum]
  calc
    _ ≤ ∏ d ∈ D, (1 + (d : ℝ) ^ (-s)) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      intro d hd
      let u := (d : ℝ) ^ (-s)
      have hu : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hD d hd) (by linarith)
      change Real.exp (u / 2) ≤ 1 + u
      have hp : 0 < 1 + u := by linarith
      rw [← Real.exp_log hp, Real.exp_le_exp]
      refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
      rw [← one_div, le_sub_comm, div_le_iff₀ hp]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
    _ = _ := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl
      intro I _
      rw [Nat.cast_prod]
      exact Real.finsetProd_rpow I _ (fun _ _ => Nat.cast_nonneg _) _

/-- Discrete layer-cake lower bound for `∑ d^(-s)`. -/
lemma layer_lower (D : Finset ℕ) (s : ℝ) (hs : 0 < s) (J : ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ 2 ^ J) :
    ∑ j ∈ Finset.range J, ((2 : ℝ) ^ (-((j : ℝ) * s)) - (2 : ℝ) ^ (-(((j : ℝ) + 1) * s))) *
        ((D.filter (· ≤ 2 ^ j)).card : ℝ) ≤ ∑ d ∈ D, (d : ℝ) ^ (-s) := by
  classical
  let w (j : ℕ) := (2 : ℝ) ^ (-((j : ℝ) * s))
  have hw (j : ℕ) : w (j + 1) ≤ w j := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  simp_rw [← Nat.cast_add_one]
  change ∑ j ∈ range J, (w j - w (j + 1)) * _ ≤ _
  simp_rw [Finset.natCast_card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d hd
  let u := (d : ℝ) ^ (-s)
  have haux (n : ℕ) :
      (∑ j ∈ range n, if d ≤ 2 ^ j then w j - w (j + 1) else 0) + min u (w n) ≤ u := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hn : d ≤ 2 ^ n
      · have hn' : w n ≤ u := by
          dsimp [w, u]
          rw [← mul_neg, Real.rpow_natCast_mul (by norm_num)]
          apply Real.rpow_le_rpow_of_nonpos
          · exact_mod_cast (hD d hd).1
          · exact_mod_cast hn
          · linarith
        rw [if_pos hn, min_eq_right ((hw n).trans hn')]
        rw [min_eq_right hn'] at ih
        linarith
      · rw [if_neg hn, add_zero]
        exact (add_le_add_right (min_le_min_left u (hw n)) _).trans ih
  have hp : 0 ≤ min u (w J) := le_min (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (by norm_num) _)
  exact (le_add_of_nonneg_right hp).trans (haux J)

/-- The Euler product of `A ∩ (2, 2^J]` at `s = 2/3 + 1/J`. -/
noncomputable def rankinSum (A : Set ℕ) (J : ℕ) : ℝ :=
  ∑ I ∈ (dset A (2 ^ J)).powerset, ((∏ i ∈ I, i : ℕ) : ℝ) ^ (-(2 / 3 + 1 / (J : ℝ)))

/-- Under the contrary hypothesis, the sum of `q^(-s)` over `A ∩ (2, 2^J]` grows like
`25 log J` (the constant `100/4`). -/
lemma sum_inv_lower (A : Set ℕ) (N₀ : ℕ)
    (H : ∀ N : ℕ, N₀ ≤ N →
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / Real.log N < ((A ∩ Set.Icc 1 N).ncard : ℝ)) :
    ∃ K₁ : ℝ, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      25 * Real.log J - K₁ ≤ ∑ d ∈ dset A (2 ^ J), (d : ℝ) ^ (-(2 / 3 + 1 / (J : ℝ))) := by
  classical
  let M := N₀ + 1
  refine ⟨25 * Real.log M + 2, M, ?_⟩
  intro J hJ
  have hM : 0 < M := Nat.succ_pos _
  have hJr : 0 < (J : ℝ) := by exact_mod_cast (hM.trans_le hJ)
  let s : ℝ := 2 / 3 + 1 / J
  let w (j : ℕ) := (2 : ℝ) ^ (-((j : ℝ) * s))
  let D := dset A (2 ^ J)
  let C (j : ℕ) : ℝ := (D.filter (· ≤ 2 ^ j)).card
  have hs : 0 < s := by dsimp [s]; positivity
  have hw (j : ℕ) : 0 ≤ w j := Real.rpow_nonneg (by norm_num) _
  have hdiff (j : ℕ) : 0 ≤ w j - w (j + 1) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hcoef : 7 / 20 ≤ 1 - (2 : ℝ) ^ (-s) := by
    have h : (2 : ℝ) ^ (-s) ≤ 2 ^ (-(2 / 3 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [s]
      linarith [one_div_pos.mpr hJr]
    have h' : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 13 / 20 := by
      apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by norm_num)
      rw [← Real.rpow_mul_natCast (by norm_num)]
      norm_num
    linarith
  have hstep (j : ℕ) (hMj : M ≤ j) (hjJ : j ≤ J) :
      25 * (Real.log (j + 1 : ℕ) - Real.log j) ≤ (w j - w (j + 1)) * (C j + 2) := by
    have hjr : 0 < (j : ℝ) := by exact_mod_cast hM.trans_le hMj
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    let p : ℝ := ((2 : ℝ) ^ j) ^ (2 / 3 : ℝ)
    have hcard : ((A ∩ Set.Icc 1 (2 ^ j)).ncard : ℝ) ≤ C j + 2 := by
      let T := D.filter (· ≤ 2 ^ j)
      have hsub : A ∩ Set.Icc 1 (2 ^ j) ⊆ (T : Set ℕ) ∪ Set.Icc 1 2 := by
        intro i hi
        by_cases h2 : i ≤ 2
        · exact Or.inr ⟨hi.2.1, h2⟩
        · exact Or.inl (Finset.mem_filter.mpr ⟨mem_dset.mpr
            ⟨⟨by omega, hi.2.2.trans (Nat.pow_le_pow_right (by decide) hjJ)⟩, hi.1⟩, hi.2.2⟩)
      have h := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
      simp only [Set.ncard_coe_finset, Set.ncard_Icc_nat] at h
      change _ ≤ (T.card : ℝ) + 2
      exact_mod_cast h
    have hn : N₀ ≤ 2 ^ j := by have := j.lt_two_pow_self; dsimp [M] at hMj; omega
    have hdens := (H (2 ^ j) hn).le.trans hcard
    push_cast at hdens
    rw [Real.log_pow] at hdens
    change 100 * p / ((j : ℝ) * Real.log 2) ≤ C j + 2 at hdens
    have hpw : 1 / 2 ≤ w j * p := by
      dsimp [p, w]
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      calc
        1 / 2 = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hj' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
          dsimp [s]
          field_simp
          nlinarith
    have hfactor : w j - w (j + 1) = w j * (1 - (2 : ℝ) ^ (-s)) := by
      dsimp [w]
      push_cast
      rw [show -(((j : ℝ) + 1) * s) = -((j : ℝ) * s) + -s by ring,
        Real.rpow_add (by norm_num)]
      ring
    have hnum : 25 / (j : ℝ) ≤ (w j - w (j + 1)) * (C j + 2) := by
      rw [hfactor]
      calc
        25 / (j : ℝ) ≤ (7 / 20) * (100 * (w j * p)) / ((j : ℝ) * Real.log 2) := by
          rw [le_div_iff₀ (mul_pos hjr hlog)]
          field_simp
          nlinarith [Real.log_two_lt_d9]
        _ = w j * (7 / 20) * (100 * p / ((j : ℝ) * Real.log 2)) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hcoef (hw j)) hdens
          (by dsimp [p]; positivity) (mul_nonneg (hw j) (by linarith))
    apply le_trans _ hnum
    push_cast
    rw [← Real.log_div (by positivity) hjr.ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (j : ℝ) + 1) hjr)
    calc
      _ ≤ 25 * (((j : ℝ) + 1) / j - 1) := by linarith
      _ = _ := by field_simp; ring
  let S (n : ℕ) := ∑ j ∈ range n, (w j - w (j + 1)) * C j
  have haux (n : ℕ) (hn : M ≤ n) : n ≤ J →
      25 * (Real.log n - Real.log M) - 2 * (w M - w n) ≤ S n := by
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      simp only [sub_self, mul_zero]
      dsimp [S]
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (hdiff j) (Nat.cast_nonneg _)
    | succ n hn ih =>
      intro hn'
      have h := ih (Nat.le_of_succ_le hn')
      have ht := hstep n hn (Nat.le_of_succ_le hn')
      change _ ≤ ∑ j ∈ range (n + 1), (w j - w (j + 1)) * C j
      rw [Finset.sum_range_succ]
      change _ ≤ S n + _
      linarith
  have hbound : w M ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) hs.le))
  have hlow : 25 * Real.log J - (25 * Real.log M + 2) ≤ S J := by
    linarith [haux J hJ le_rfl, hw J]
  apply hlow.trans
  have hl := layer_lower D s hs J (fun d hd =>
    ⟨by have := (mem_dset.mp hd).1.1; omega, (mem_dset.mp hd).1.2⟩)
  simpa only [S, w, C, Nat.cast_add_one] using hl

/-- Lower half of Rankin's trick. -/
lemma rankin_lower (A : Set ℕ) (N₀ : ℕ)
    (H : ∀ N : ℕ, N₀ ≤ N →
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / Real.log N < ((A ∩ Set.Icc 1 N).ncard : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ J₁ : ℕ, ∀ J : ℕ, J₁ ≤ J → c * (J : ℝ) ^ 3 ≤ rankinSum A J := by
  obtain ⟨K, M, h⟩ := sum_inv_lower A N₀ H
  refine ⟨Real.exp (-K / 2), Real.exp_pos _, max M 1, ?_⟩
  intro J hJ
  have h1 : 1 ≤ J := (le_max_right _ _).trans hJ
  have hJ' : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ J by exact_mod_cast h1)
  have hsum := h J ((le_max_left _ _).trans hJ)
  apply le_trans _ (euler_lower (dset A (2 ^ J)) (2 / 3 + 1 / (J : ℝ))
    (by positivity) (fun d hd => by have := (mem_dset.mp hd).1.1; omega))
  have hpow : (J : ℝ) ^ 3 = Real.exp ((3 : ℕ) * Real.log J) := by
    rw [Real.exp_nat_mul, Real.exp_log hJ']
  rw [hpow]
  rw [← Real.exp_add, Real.exp_le_exp]
  push_cast only [Nat.cast_ofNat]
  linarith only [hsum, hlog]

private lemma aux3_dyadic (M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ 2 ^ M) :
    ∃ j ≤ M, k ≤ 2 ^ j ∧ 2 ^ j ≤ 2 * k := by
  induction M with
  | zero => exact ⟨0, le_rfl, hkM, by simp; omega⟩
  | succ M ih =>
    by_cases h : k ≤ 2 ^ M
    · obtain ⟨j, hj, h₁, h₂⟩ := ih h
      exact ⟨j, Nat.le_succ_of_le hj, h₁, h₂⟩
    · exact ⟨M + 1, le_rfl, hkM, by rw [pow_succ]; omega⟩

/-- Discrete layer-cake upper bound for the Euler product in terms of `Fcount`. -/
lemma layer_upper (D : Finset ℕ) (s : ℝ) (hs : 0 < s) (hD : ∀ d ∈ D, 1 ≤ d) (M : ℕ)
    (hM : ∏ d ∈ D, d ≤ 2 ^ M) :
    ∑ I ∈ D.powerset, ((∏ i ∈ I, i : ℕ) : ℝ) ^ (-s) ≤
      (2 : ℝ) ^ s * ∑ j ∈ Finset.range (M + 1), (2 : ℝ) ^ (-((j : ℝ) * s)) * (Fcount D (2 ^ j) : ℝ) := by
  classical
  let w (j : ℕ) : ℝ := (2 : ℝ) ^ (-((j : ℝ) * s))
  let k (I : Finset ℕ) := ∏ i ∈ I, i
  let v (I : Finset ℕ) (j : ℕ) : ℝ := if k I ≤ 2 ^ j then w j else 0
  have hp (I : Finset ℕ) (hI : I ∈ D.powerset) :
      (k I : ℝ) ^ (-s) ≤ (2 : ℝ) ^ s * ∑ j ∈ range (M + 1), v I j := by
    have hsub := Finset.mem_powerset.mp hI
    have hk : 1 ≤ k I := Finset.one_le_prod' (fun i hi => hD i (hsub hi))
    have hkM : k I ≤ 2 ^ M := le_trans
      (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i hi _ => hD i hi)) hM
    obtain ⟨j, hj, hlo, hhi⟩ := aux3_dyadic M (k I) hk hkM
    have hhi' : (2 : ℝ) ^ j ≤ 2 * (k I : ℝ) := by exact_mod_cast hhi
    have hsingle : w j ≤ ∑ a ∈ range (M + 1), v I a := by
      rw [← show v I j = w j by simp [v, hlo]]
      apply Finset.single_le_sum _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      intro a _
      dsimp [v, w]
      split <;> positivity
    calc
      (k I : ℝ) ^ (-s) ≤ ((2 : ℝ) ^ j / 2) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hhi']) (by linarith)
      _ = (2 : ℝ) ^ s * w j := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) s,
          div_inv_eq_mul, ← Real.rpow_natCast_mul (by norm_num), mul_neg, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (by positivity)
  calc
    _ ≤ ∑ I ∈ D.powerset, (2 : ℝ) ^ s * ∑ j ∈ range (M + 1), v I j := Finset.sum_le_sum hp
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      change (∑ I ∈ D.powerset, if k I ≤ 2 ^ j then w j else 0) = w j * (Fcount D (2 ^ j) : ℝ)
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Fcount, k, mul_comm]

/-- The large sieve and the contrary hypothesis bound the number of products. -/
lemma F_upper (A : Set ℕ) (hA : Erdos12.IsGood A) (hcop : A.Pairwise Nat.Coprime) (N₀ : ℕ)
    (H : ∀ N : ℕ, N₀ ≤ N →
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / Real.log N < ((A ∩ Set.Icc 1 N).ncard : ℝ)) :
    ∃ Q₁ : ℕ, ∀ Q : ℕ, Q₁ ≤ Q →
      (Fcount (dset A Q) Q : ℝ) ≤ 4 * (Q : ℝ) ^ (2 / 3 : ℝ) * Real.log Q := by
  classical
  refine ⟨N₀ + 2, ?_⟩
  intro Q hQ
  have hq : 1 < Q := by omega
  let D := dset A Q
  let B := (Finset.Ioc Q (Q ^ 2)).filter (· ∈ A)
  have hd {d} (h : d ∈ D) := mem_dset.mp h
  have hb {b} (h : b ∈ B) : (Q < b ∧ b ≤ Q ^ 2) ∧ b ∈ A := by simpa [B] using h
  have hmul := count_products Q D B (by omega) (fun d h => (hd h).1) (fun b h => (hb h).1.2)
    (fun _ h _ h' hne => hcop (hd h).2 (hd h').2 hne) (by
      intro d hd' b hb' c hc' hdiv
      obtain ⟨⟨hd2, hdQ⟩, hdA⟩ := hd hd'
      obtain ⟨⟨hbQ, _⟩, hbA⟩ := hb hb'
      obtain ⟨⟨hcQ, _⟩, hcA⟩ := hb hc'
      have hdb := hdQ.trans_lt hbQ
      obtain rfl := hA.2 d hdA b hbA c hcA hdiv hdb (hdQ.trans_lt hcQ)
      have h := (hcop hdA hbA hdb.ne).dvd_of_dvd_mul_right
        (show d ∣ 2 * b by simpa [two_mul] using hdiv)
      exact (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt hd2)
  have hseg := count_segment A Q (Q ^ 2)
  change _ ≤ Q + B.card at hseg
  have hdens := H (Q ^ 2) (by nlinarith)
  have hseg' : ((A ∩ Set.Icc 1 (Q ^ 2)).ncard : ℝ) ≤ (Q : ℝ) + B.card := by exact_mod_cast hseg
  have hbound := hdens.trans_le hseg'
  let X := (Q : ℝ) ^ (1 / 3 : ℝ)
  let L := Real.log Q
  let F : ℝ := Fcount D Q
  let b : ℝ := B.card
  have hX : 0 < X := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < Q by omega)) _
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hq)
  have hx3 : X ^ 3 = Q := by
    dsimp [X]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num
  have hx2 : (Q : ℝ) ^ (2 / 3 : ℝ) = X ^ 2 := by
    dsimp [X]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]; norm_num
  have hx4 : ((Q : ℝ) ^ (2 : ℕ)) ^ (2 / 3 : ℝ) = X ^ 4 := by
    dsimp [X]; rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    norm_num
  have hlog : L ≤ 3 * X := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg Q) (by norm_num : (0 : ℝ) < 1 / 3)
    dsimp [L, X]; linarith only [h]
  push_cast at hbound
  rw [hx4, Real.log_pow] at hbound
  norm_num only [Nat.cast_ofNat] at hbound
  change 100 * X ^ 4 / (2 * L) < (Q : ℝ) + b at hbound
  have hm := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * L)).mp hbound
  rw [← hx3] at hm
  have hbL : 25 * X ^ 4 ≤ b * L := by
    nlinarith only [hm, mul_le_mul_of_nonneg_left hlog (show 0 ≤ X ^ 3 by positivity), pow_nonneg hX.le 4]
  have hp : F * b ≤ 100 * (Q : ℝ) ^ 2 := by dsimp [F, b]; exact_mod_cast hmul
  rw [← hx3] at hp
  have hF : 0 ≤ F := Nat.cast_nonneg _
  change F ≤ _
  rw [hx2]
  change F ≤ 4 * X ^ 2 * L
  refine le_of_mul_le_mul_right (a := 25 * X ^ 4) ?_ (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left hbL hF, mul_le_mul_of_nonneg_right hp hL.le]

private lemma aux4_count (A : Set ℕ) (Q : ℕ)
    (hQ : ∀ y : ℕ, Q ≤ y → (Fcount (dset A y) y : ℝ) ≤
      4 * (y : ℝ) ^ (2 / 3 : ℝ) * Real.log y) (X j : ℕ) :
    (Fcount (dset A X) (2 ^ j) : ℝ) ≤
      ((2 : ℝ) ^ Q + 4) * ((j : ℝ) + 1) * (2 : ℝ) ^ ((j : ℝ) * (2 / 3 : ℝ)) := by
  classical
  have hm : (Fcount (dset A X) (2 ^ j) : ℝ) ≤ Fcount (dset A (2 ^ j)) (2 ^ j) := by
    exact_mod_cast Fcount_mono A X (2 ^ j)
  apply hm.trans
  let p := (2 : ℝ) ^ ((j : ℝ) * (2 / 3 : ℝ))
  have hp : 1 ≤ p := Real.one_le_rpow (by norm_num) (by positivity)
  change _ ≤ ((2 : ℝ) ^ Q + 4) * ((j : ℝ) + 1) * p
  by_cases h : Q ≤ 2 ^ j
  · have hf := hQ (2 ^ j) h
    push_cast at hf
    rw [Real.log_pow, ← Real.rpow_natCast_mul (by norm_num)] at hf
    change _ ≤ 4 * p * ((j : ℝ) * Real.log 2) at hf
    apply hf.trans
    calc
      _ ≤ 4 * p * ((j : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j)
          (show 0 ≤ 1 - Real.log 2 by linarith [Real.log_two_lt_d9])]
      _ = 4 * ((j : ℝ) + 1) * p := by ring
      _ ≤ _ := by gcongr; linarith [show 0 ≤ (2 : ℝ) ^ Q by positivity]
  · let y := 2 ^ j
    have hc : (dset A y).card ≤ y := by
      calc
        _ ≤ (Finset.Ioc 2 y).card := Finset.card_filter_le _ _
        _ ≤ y := by rw [Nat.card_Ioc]; exact Nat.sub_le _ _
    have hf : Fcount (dset A y) y ≤ 2 ^ Q := by
      calc
        _ ≤ (dset A y).powerset.card := Finset.card_filter_le _ _
        _ = _ := Finset.card_powerset _
        _ ≤ 2 ^ Q := Nat.pow_le_pow_right (by decide) (hc.trans (by dsimp [y]; omega))
    calc
      _ ≤ (2 : ℝ) ^ Q := by exact_mod_cast hf
      _ = (2 : ℝ) ^ Q * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) j]

private lemma aux4_series {r : ℝ} (hr : 0 < r) (hr' : r < 1) (M : ℕ) :
    ∑ j ∈ range (M + 1), ((j : ℝ) + 1) * r ^ j ≤ (1 / (1 - r)) ^ 2 := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr'
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add
    (hasSum_geometric_of_lt_one hr.le hr')
  have he : 1 - r ≠ 0 := by linarith
  calc
    _ = ∑ j ∈ range (M + 1), ((j : ℝ) * r ^ j + r ^ j) := by simp [add_mul]
    _ ≤ r / (1 - r) ^ 2 + (1 - r)⁻¹ := sum_le_hasSum _ (fun j _ => by positivity) h
    _ = _ := by field_simp; ring

/-- Upper half of Rankin's trick. -/
lemma rankin_upper (A : Set ℕ) (hA : Erdos12.IsGood A) (hcop : A.Pairwise Nat.Coprime) (N₀ : ℕ)
    (H : ∀ N : ℕ, N₀ ≤ N →
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / Real.log N < ((A ∩ Set.Icc 1 N).ncard : ℝ)) :
    ∃ K : ℝ, ∃ J₂ : ℕ, ∀ J : ℕ, J₂ ≤ J → rankinSum A J ≤ K * (J : ℝ) ^ 2 := by
  classical
  obtain ⟨Q, hQ⟩ := F_upper A hA hcop N₀ H
  let C := (2 : ℝ) ^ Q + 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨8 * C, 3, ?_⟩
  intro J hJ
  have hJ3 : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  let D := dset A (2 ^ J)
  let M := J * D.card
  let s := 2 / 3 + 1 / (J : ℝ)
  let r := (2 : ℝ) ^ (-(1 / (J : ℝ)))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs' : s ≤ 1 := by
    dsimp [s]
    have : 1 / (J : ℝ) ≤ 1 / 3 := by gcongr
    linarith
  have h2s : (2 : ℝ) ^ s ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hs'
  have hr : 0 < r := by dsimp [r]; positivity
  have hr' : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr (by positivity))
  have hp : ∏ d ∈ D, d ≤ 2 ^ M := by
    rw [show 2 ^ M = (2 ^ J : ℕ) ^ D.card from pow_mul _ _ _]
    exact Finset.prod_le_pow_card D id _ (fun d hd => (mem_dset.mp hd).1.2)
  have hl := layer_upper D s hs (fun d hd => by have := (mem_dset.mp hd).1.1; omega) M hp
  have hterm (j : ℕ) : (2 : ℝ) ^ (-((j : ℝ) * s)) * (Fcount D (2 ^ j) : ℝ) ≤
      C * (((j : ℝ) + 1) * r ^ j) := by
    have hpow : (2 : ℝ) ^ (-((j : ℝ) * s)) * (2 : ℝ) ^ ((j : ℝ) * (2 / 3 : ℝ)) = r ^ j := by
      dsimp [r, s]
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    calc
      _ ≤ (2 : ℝ) ^ (-((j : ℝ) * s)) *
          (C * ((j : ℝ) + 1) * (2 : ℝ) ^ ((j : ℝ) * (2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (aux4_count A Q hQ (2 ^ J) j) (by positivity)
      _ = _ := by rw [← hpow]; ring
  have hbern := one_add_mul_le_pow (show -2 ≤ r - 1 by linarith) J
  have hrJ : r ^ J = 1 / 2 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num), show -(1 / (J : ℝ)) * J = -1 by field_simp]
    norm_num
  rw [show 1 + (r - 1) = r by ring, hrJ] at hbern
  have hinv : 1 / (1 - r) ≤ 2 * J := by
    rw [div_le_iff₀ (sub_pos.mpr hr')]
    linarith only [hbern]
  have hsum : (∑ j ∈ range (M + 1), (2 : ℝ) ^ (-((j : ℝ) * s)) * (Fcount D (2 ^ j) : ℝ)) ≤
      C * (2 * (J : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ range (M + 1), C * (((j : ℝ) + 1) * r ^ j) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = C * ∑ j ∈ range (M + 1), ((j : ℝ) + 1) * r ^ j := (Finset.mul_sum ..).symm
      _ ≤ C * (1 / (1 - r)) ^ 2 := mul_le_mul_of_nonneg_left (aux4_series hr hr' M) hC
      _ ≤ _ := by gcongr
  calc
    rankinSum A J ≤ _ := hl
    _ ≤ 2 * (C * (2 * (J : ℝ)) ^ 2) := mul_le_mul h2s hsum (by positivity) (by norm_num)
    _ = _ := by ring

end Baier

open Baier

theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.baier := by
  classical
  intro A hA hcop
  refine ⟨100, by norm_num, ?_⟩
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N₀, hN₀⟩ := hfin.bddAbove
  have H : ∀ N : ℕ, N₀ + 1 ≤ N →
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / Real.log N < ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
    intro N hN
    by_contra h
    have hle := hN₀ (show N ∈ {N : ℕ | ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤
      100 * (N : ℝ) ^ (2 / 3 : ℝ) / (N : ℝ).log} from le_of_not_gt h)
    omega
  obtain ⟨c, hc, J₁, hlow⟩ := rankin_lower A (N₀ + 1) H
  obtain ⟨K, J₂, hup⟩ := rankin_upper A hA hcop (N₀ + 1) H
  obtain ⟨n, hn⟩ := exists_nat_gt (K / c)
  set J := max (max J₁ J₂) (n + 1) with hJdef
  have hJ1 : J₁ ≤ J := le_trans (le_max_left _ _) (le_max_left _ _)
  have hJ2 : J₂ ≤ J := le_trans (le_max_right _ _) (le_max_left _ _)
  have hJn : n + 1 ≤ J := le_max_right _ _
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hnJ : (n : ℝ) < J := by exact_mod_cast (show n < J by omega)
  have h3 : c * (J : ℝ) ^ 3 ≤ K * (J : ℝ) ^ 2 := (hlow J hJ1).trans (hup J hJ2)
  have hJ2pos : (0 : ℝ) < (J : ℝ) ^ 2 := by positivity
  have hcJ : c * (J : ℝ) ≤ K := by
    have h4 : (c * (J : ℝ)) * (J : ℝ) ^ 2 ≤ K * (J : ℝ) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h4 hJ2pos
  have hJK : (J : ℝ) ≤ K / c := by
    rw [le_div_iff₀ hc]
    linarith
  linarith
