import FormalConjectures.ErdosProblems.«12»

/-!
# Schoen's bound for pairwise coprime sets with the Erdős–Sárközy property

For each small modulus from the set, the absence of opposite residues forces a lower
bound on the energy of the Fourier sum of the tail. The nonzero fractions belonging to
these moduli are separated, so integrating on disjoint intervals gives a large sieve
upper bound. Comparing the counting function at a cube and its square finishes the proof.
-/

open Finset Real MeasureTheory Set
open scoped ComplexConjugate

namespace Schoen

noncomputable def phase (b : ℕ) (x : ℝ) : ℂ := fourier (b : ℤ) (x : AddCircle (1 : ℝ))

noncomputable def wave (B : Finset ℕ) (x : ℝ) : ℂ := ∑ b ∈ B, phase b x

/-- The sum of the squared Fourier sums over all residues vanishes because every pair
of tail elements has nonzero sum modulo q. Removing the zero frequency gives the bound. -/
lemma modular_energy (B : Finset ℕ) (q : ℕ) (hq : 0 < q)
    (hn : ∀ b ∈ B, ∀ c ∈ B, ¬q ∣ b + c) :
    (B.card : ℝ) ^ 2 ≤ ∑ k ∈ (range q).erase 0, ‖wave B (k / q)‖ ^ 2 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / q)
  have hz : IsPrimitiveRoot z q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hchar (b k : ℕ) : phase b ((k : ℝ) / q) = (z ^ b) ^ k := by
    simp only [phase, fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_div,
      Complex.ofReal_natCast, Int.cast_natCast, z, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hzero (b c : ℕ) (hn' : ¬q ∣ b + c) :
      ∑ k ∈ range q, phase b ((k : ℝ) / q) * phase c ((k : ℝ) / q) = 0 := by
    simp_rw [hchar, ← mul_pow, ← pow_add]
    have hp : (z ^ (b + c)) ^ q = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    have hg := geom_sum_mul (z ^ (b + c)) q
    rw [hp, sub_self, mul_eq_zero] at hg
    exact hg.resolve_right (sub_ne_zero.mpr (mt (hz.pow_eq_one_iff_dvd _).mp hn'))
  have hs : ∑ k ∈ range q, wave B ((k : ℝ) / q) ^ 2 = 0 := by
    simp only [wave, sq, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro b hb
    rw [sum_comm]
    exact sum_eq_zero (fun c hc => hzero c b (hn c hc b hb))
  have hadd := Finset.sum_erase_add (range q) (fun k : ℕ => wave B ((k : ℝ) / q) ^ 2)
    (by simpa using hq : 0 ∈ range q)
  rw [hs] at hadd
  have h0 : wave B ((0 : ℕ) / (q : ℝ)) = (B.card : ℂ) := by simp [wave, phase]
  rw [h0] at hadd
  have heq := congrArg norm (eq_neg_of_add_eq_zero_left hadd)
  simp only [norm_neg, norm_pow, Complex.norm_natCast] at heq
  rw [← heq]
  exact (norm_sum_le ((range q).erase 0) (fun k : ℕ => wave B ((k : ℝ) / q) ^ 2)).trans_eq
    (Finset.sum_congr rfl fun k _ => norm_pow _ _)

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

/-- Two distinct nonzero fractions with these denominators differ by at least 1 / Q². -/
lemma separated {Q q r k j : ℕ} (hq : q ≤ Q) (hr : r ≤ Q)
    (hk : 0 < k ∧ k < q) (hj : 0 < j ∧ j < r)
    (hc : q ≠ r → q.Coprime r) (hne : q ≠ r ∨ k ≠ j) :
    (k : ℝ) / q + 1 / (Q : ℝ) ^ 2 ≤ (j : ℝ) / r ∨
    (j : ℝ) / r + 1 / (Q : ℝ) ^ 2 ≤ (k : ℝ) / q := by
  have hdiff : k * r ≠ j * q := by
    intro he
    by_cases e : q = r
    · subst r
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) he
      exact hne.elim (fun h => h rfl) (fun h => h this)
    · have hdiv : q ∣ k * r := he ▸ dvd_mul_left q j
      have := (hc e).dvd_of_dvd_mul_right hdiv
      exact (Nat.le_of_dvd hk.1 this).not_gt hk.2
  have qpos : (0 : ℝ)<q := by exact_mod_cast (show 0 < q by omega)
  have rpos : (0 : ℝ)<r := by exact_mod_cast (show 0 < r by omega)
  have Qpos : (0 : ℝ)<Q := by exact_mod_cast (show 0 < Q by omega)
  have hprod : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    rw [sq]
    exact_mod_cast Nat.mul_le_mul hq hr
  have hrec := one_div_le_one_div_of_le (mul_pos qpos rpos) hprod
  rcases lt_or_gt_of_ne hdiff with h | h
  · left
    have hg : (k : ℝ) * r + 1 ≤ (j : ℝ) * q := by exact_mod_cast h
    have : (k : ℝ) / q + 1 / ((q : ℝ) * r) ≤ (j : ℝ) / r := by
      field_simp
      linarith
    linarith
  · right
    have hg : (j : ℝ) * q + 1 ≤ (k : ℝ) * r := by exact_mod_cast h
    have : (j : ℝ) / r + 1 / ((q : ℝ) * r) ≤ (k : ℝ) / q := by
      field_simp
      linarith
    linarith

lemma right_endpoint {Q q k : ℕ} (hk : k < q) (hq : q ≤ Q) :
    (k : ℝ) / q + 1 / (Q : ℝ) ^ 2 ≤ 1 := by
  have hq' : (0 : ℝ)<q := by exact_mod_cast (show 0 < q by omega)
  have hbig : (q : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast (hq.trans (Nat.le_self_pow (by decide : 2 ≠ 0) Q))
  have hr := one_div_le_one_div_of_le hq' hbig
  have h : (k : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hk
  have : (k : ℝ) / q + 1 / (q : ℝ) ≤ 1 := by rw [← add_div]; exact (div_le_one hq').mpr h
  linarith

/-- A large sieve bound for the nonzero fractions of the pairwise coprime moduli in D. -/
lemma count_product (Q : ℕ) (D B : Finset ℕ) (hQ : 0 < Q)
    (hD : ∀ d ∈ D, 2 < d ∧ d ≤ Q) (hB : ∀ b ∈ B, Q < b ∧ b ≤ Q ^ 2)
    (hcop : (D : Set ℕ).Pairwise Nat.Coprime)
    (hn : ∀ d ∈ D, ∀ b ∈ B, ∀ c ∈ B, ¬d ∣ b + c) :
    D.card * B.card ≤ 100 * Q ^ 2 := by
  classical
  let N : ℝ := (Q : ℝ) ^ 2
  let L : ℝ := 1 / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hL : 0 < L := one_div_pos.mpr hN
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
  let K (q : ℕ) := (Finset.range q).erase 0
  let S := D.sigma K
  let theta (p : (q : ℕ) × ℕ) : ℝ := p.2 / p.1
  let J (p : (q : ℕ) × ℕ) := Set.Ioc (theta p) (theta p + L)
  have mem {p} (hp : p ∈ S) : p.1 ∈ D ∧ (0 < p.2 ∧ p.2 < p.1) := by
    simpa [S, K, Nat.pos_iff_ne_zero] using hp
  have hdis : (S : Set _).Pairwise (Function.onFun Disjoint J) := by
    intro p hp r hr hne
    have hne' : p.1 ≠ r.1 ∨ p.2 ≠ r.2 := by
      by_contra! he
      exact hne (Sigma.ext he.1 (heq_of_eq he.2))
    have sep := separated (hD _ (mem hp).1).2 (hD _ (mem hr).1).2 (mem hp).2 (mem hr).2
      (fun e => hcop (mem hp).1 (mem hr).1 e) hne'
    apply Set.disjoint_left.mpr
    intro x hx hy
    change theta p < x ∧ x ≤ theta p + L at hx
    change theta r < x ∧ x ≤ theta r + L at hy
    change theta p + L ≤ theta r ∨ theta r + L ≤ theta p at sep
    rcases sep with h | h <;> linarith only [hx.1, hx.2, hy.1, hy.2, h]
  have hunion : (⋃ p ∈ S, J p) ⊆ Set.Ioc 0 1 := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hx
    have hlo : 0 ≤ theta p := by dsimp [theta]; positivity
    exact ⟨hlo.trans_lt hx.1, hx.2.trans (right_endpoint (mem hp).2.2 (hD _ (mem hp).1).2)⟩
  have htotal : ∑ p ∈ S, ‖wave B (theta p)‖ ^ 2 ≤ ∫ x in (0 : ℝ)..1, W x := by
    calc
      _ ≤ ∑ p ∈ S, ∫ x in J p, W x := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [intervalIntegral.integral_of_le (show theta p ≤ theta p + L by linarith only [hL])] using
          sample_interval hF hG (theta p) L hL
      _ = ∫ x in ⋃ p ∈ S, J p, W x := (integral_biUnion_finset S
        (fun _ _ => measurableSet_Ioc) hdis (fun _ _ => (hcW.intervalIntegrable _ _).1)).symm
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact setIntegral_mono_set (hcW.intervalIntegrable 0 1).1 (Filter.Eventually.of_forall hW)
          (Filter.Eventually.of_forall hunion)
  have hmass : (∫ x in (0 : ℝ)..1, ‖wave B x‖ ^ 2) = B.card := by
    simpa only [one_mul, wave, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      using parseval B (fun _ => 1)
  have hder : (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) ≤ (B.card : ℝ) * (8 * N) ^ 2 := by
    rw [show (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) = _ from parseval B u]
    calc
      _ ≤ ∑ b ∈ B, (8 * N) ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        have hb' : (b : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast (hB b hb).2
        have hh : ‖u b‖ ≤ 8 * N := by
          simp only [u, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_natCast]
          nlinarith only [hb', mul_nonneg (show 0 ≤ (b : ℝ) by positivity) (le_of_lt (sub_pos.mpr Real.pi_lt_four))]
        exact pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by simp
  have hupper : (∫ x in (0 : ℝ)..1, W x) ≤ 100 * N * B.card := by
    dsimp only [W]
    rw [intervalIntegral.integral_add (f := fun x => (2 / L) * ‖wave B x‖ ^ 2) (g := fun x => L * ‖G x‖ ^ 2)
        ((continuous_const.mul (hcF.norm.pow 2)).intervalIntegrable _ _)
        ((continuous_const.mul (hG.norm.pow 2)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmass]
    dsimp only [L]
    field_simp
    nlinarith only [hder, mul_nonneg (sq_nonneg N) (Nat.cast_nonneg (α := ℝ) B.card)]
  have hlower : (D.card : ℝ) * (B.card : ℝ) ^ 2 ≤ ∑ p ∈ S, ‖wave B (theta p)‖ ^ 2 := by
    rw [← Finset.sum_sigma' D K (fun q k => ‖wave B ((k : ℝ) / q)‖ ^ 2)]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := D) (fun q hq => modular_energy B q (by have := (hD q hq).1; omega) (hn q hq))
  by_cases hzero : B.card = 0
  · simp [hzero]
  have pos : (0 : ℝ) < B.card := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hh := hlower.trans (htotal.trans hupper)
  rw [sq, ← mul_assoc] at hh
  dsimp only [N] at hh
  exact_mod_cast (le_of_mul_le_mul_right hh pos)

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

end Schoen

open Schoen

theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.schoen := by
  classical
  intro A hA hcop
  refine ⟨102, by norm_num, ?_⟩
  rw [Set.infinite_iff_exists_gt]
  intro M
  let t := M + 2
  have ht : 2 ≤ t := by dsimp [t]; omega
  have past (k : ℕ) (hk : 1 ≤ k) : M < t ^ k := by
    have h := Nat.pow_le_pow_right (by omega : 0 < t) hk
    simp only [pow_one] at h
    dsimp [t] at h ⊢
    omega
  have powval (k : ℕ) : (((t ^ (3 * k) : ℕ) : ℝ) ^ (2 / 3 : ℝ)) = (t ^ (2 * k) : ℕ) := by
    push_cast
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg t)]
    norm_cast
    rw [show ((3 * k : ℕ) : ℝ) * (2 / 3) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    rfl
  let D := (Finset.Ioc 2 (t ^ 3)).filter (· ∈ A)
  let B := (Finset.Ioc (t ^ 3) (t ^ 6)).filter (· ∈ A)
  have hd {d} (h : d ∈ D) : (2 < d ∧ d ≤ t ^ 3) ∧ d ∈ A := by simpa [D] using h
  have hb {b} (h : b ∈ B) : (t ^ 3 < b ∧ b ≤ t ^ 6) ∧ b ∈ A := by simpa [B] using h
  have hs := count_product (t ^ 3) D B (by positivity) (fun d h => (hd h).1)
    (fun b h => ⟨(hb h).1.1, by simpa [← pow_mul] using (hb h).1.2⟩)
    (fun d hd' e he' hne => hcop (hd hd').2 (hd he').2 hne) (by
      intro d hd' b hb' c hc' hdiv
      obtain ⟨⟨hd2, hdQ⟩, hdA⟩ := hd hd'
      obtain ⟨⟨hbQ, _⟩, hbA⟩ := hb hb'
      obtain ⟨⟨hcQ, _⟩, hcA⟩ := hb hc'
      have hdb := hdQ.trans_lt hbQ
      obtain rfl := hA.2 d hdA b hbA c hcA hdiv hdb (hdQ.trans_lt hcQ)
      have h := (hcop hdA hbA hdb.ne).dvd_of_dvd_mul_right
        (show d ∣ 2 * b by simpa [two_mul] using hdiv)
      exact (Nat.le_of_dvd (by decide : 0 < 2) h).not_gt hd2)
  -- At least one of the two cutoffs meets the desired bound.
  by_cases h : D.card ≤ 100 * t ^ 2
  · refine ⟨t ^ 3, ?_, past 3 (by decide)⟩
    change ((A ∩ Set.Icc 1 (t ^ 3)).ncard : ℝ) ≤ _
    rw [show (3 : ℕ) = 3 * 1 by decide, powval]
    change ((A ∩ Set.Icc 1 (t ^ 3)).ncard : ℝ) ≤ 102 * (t ^ 2 : ℕ)
    exact_mod_cast (show (A ∩ Set.Icc 1 (t ^ 3)).ncard ≤ 102 * t ^ 2 by
      have := count_segment A 2 (t ^ 3)
      change _ ≤ 2 + D.card at this
      have hp : 0 < t ^ 2 := by positivity
      omega)
  · refine ⟨t ^ 6, ?_, past 6 (by decide)⟩
    change ((A ∩ Set.Icc 1 (t ^ 6)).ncard : ℝ) ≤ _
    rw [show (6 : ℕ) = 3 * 2 by decide, powval]
    change ((A ∩ Set.Icc 1 (t ^ 6)).ncard : ℝ) ≤ 102 * (t ^ 4 : ℕ)
    exact_mod_cast (show (A ∩ Set.Icc 1 (t ^ 6)).ncard ≤ 102 * t ^ 4 by
      have hB : B.card ≤ t ^ 4 := by
        by_contra! h'
        have hlt := Nat.mul_lt_mul_of_lt_of_lt (lt_of_not_ge h) h'
        nlinarith
      have := count_segment A (t ^ 3) (t ^ 6)
      change _ ≤ t ^ 3 + B.card at this
      nlinarith [Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 3 ≤ 4)])
