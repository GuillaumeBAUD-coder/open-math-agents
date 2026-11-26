import OMAReductions.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1_H2_R1

/-! Chebyshev's bound makes the number of primes up to the block parameter sublinear.
In the specified band, each sufficiently large prime contributes at most the
degree of the polynomial to the root sum. -/

open Filter
open scoped Classical

namespace Erdos978RootCount

open Polynomial

/-- Gauss's lemma and separability over the rationals give a nonzero integral resultant. -/
lemma derivative_resultant_ne_zero (f : ℤ[X]) (hi : Irreducible f) (hd : f.natDegree ≠ 0) :
    f.resultant f.derivative ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hφ : Function.Injective φ := Int.cast_injective
  have hirr : Irreducible (f.map φ) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive hd)).mp hi
  have hcop : IsCoprime (f.map φ) (f.derivative.map φ) := by
    simpa only [derivative_map] using (separable_def _).mp hirr.separable
  have hr := resultant_ne_zero (f.map φ) (f.derivative.map φ) hcop
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map] at hr
  exact fun h => hr (by rw [h, map_zero])

/-- Evaluating the resultant identity excludes a common root with the derivative. -/
lemma not_dvd_derivative_at_root (f : ℤ[X]) (hd : f.natDegree ≠ 0) (p x : ℤ)
    (hres : ¬ p ∣ f.resultant f.derivative) (hx : p ∣ f.eval x) :
    ¬ p ∣ f.derivative.eval x := by
  obtain ⟨a, b, _, _, hbez⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl le_rfl (Or.inl hd)
  have he := congrArg (fun g : ℤ[X] => g.eval x) hbez
  simp only [eval_add, eval_mul, eval_C] at he
  intro hdx
  apply hres
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_left hdx _)

/-- Two roots above the same simple residue agree modulo the whole prime power. -/
lemma simple_lifts_congruent (f : ℤ[X]) {p k : ℕ} (hp : p.Prime) {x y : ℤ}
    (hx : (p : ℤ) ^ k ∣ f.eval x) (hy : (p : ℤ) ^ k ∣ f.eval y)
    (hxy : (p : ℤ) ∣ y - x) (hs : ¬ (p : ℤ) ∣ f.derivative.eval x) :
    (p : ℤ) ^ k ∣ y - x := by
  obtain ⟨c, ht⟩ := exists_mul_sq_add_linear_part_eq_eval_add f x (y - x)
  rw [show x + (y - x) = y by ring] at ht
  have hfactor : (f.derivative.eval x + c * (y - x)) * (y - x) = f.eval y - f.eval x := by
    linear_combination ht
  have hunit : ¬ (p : ℤ) ∣ f.derivative.eval x + c * (y - x) := by
    intro h
    have hcd := dvd_mul_of_dvd_right hxy c
    exact hs (by simpa only [add_sub_cancel_right] using dvd_sub h hcd)
  apply (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left k hunit
  rw [hfactor]
  exact dvd_sub hy hx

lemma count_lifts_le_degree (f : ℤ[X]) (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0)
    (hlc : ¬ (p : ℤ) ∣ f.leadingCoeff)
    (hs : ∀ x : ℤ, (p : ℤ) ∣ f.eval x → ¬ (p : ℤ) ∣ f.derivative.eval x) :
    ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card ≤
      f.natDegree := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let φ := Int.castRingHom (ZMod p)
  let g := f.map φ
  have hgne : g ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff f.natDegree) hz
    have he : (f.leadingCoeff : ZMod p) = 0 := by simpa [g, φ, coeff_map] using hc
    exact hlc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he)
  let S := (Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ k := dvd_pow_self _ hk
  have hcard : S.card ≤ g.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n : ZMod p))
    · intro n hn
      have hb : (p : ℤ) ∣ f.eval (n : ℤ) := hpdiv.trans (Finset.mem_filter.mp hn).2
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hgne).mpr
      change (f.map φ).eval (n : ZMod p) = 0
      have hcast : φ (n : ℤ) = (n : ZMod p) := by simp [φ]
      rw [← hcast, eval_map_apply]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
    · intro n hn m hm he
      obtain ⟨hnr, hfn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hmr, hfm⟩ := Finset.mem_filter.mp hm
      have hmod := (ZMod.natCast_eq_natCast_iff n m p).mp he
      have hpow := simple_lifts_congruent f hp hfn hfm hmod.dvd (hs n (hpdiv.trans hfn))
      have hlift : n ≡ m [MOD p ^ k] :=
        Nat.modEq_of_dvd (by simpa only [Nat.cast_pow] using hpow)
      exact hlift.eq_of_lt_of_lt (Finset.mem_range.mp hnr) (Finset.mem_range.mp hmr)
  exact hcard.trans ((Multiset.toFinset_card_le g.roots).trans
    (card_roots_map_le_natDegree (f := φ) f))

end Erdos978RootCount

open Erdos978RootCount Polynomial in
lemma Erdos978RootCount.eventual_bound (f : ℤ[X]) (hi : Irreducible f) (hd : 9 ≤ f.natDegree) :
    ∃ D Y₀ : ℕ, 0 < D ∧ ∀ p : ℕ, p.Prime → Y₀ < p →
      ((Finset.range (p ^ (f.natDegree - 2))).filter fun (r : ℕ) =>
        (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (r : ℤ)).card ≤ D := by
  let R := f.resultant f.derivative
  refine ⟨f.natDegree, max f.leadingCoeff.natAbs R.natAbs, by omega, ?_⟩
  intro p hp hlarge
  have avoid (z : ℤ) (hz : z ≠ 0) (hlt : z.natAbs < p) : ¬ (p : ℤ) ∣ z := by
    intro h
    exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natCast_dvd.mp h))
  apply count_lifts_le_degree f p (f.natDegree - 2) hp (by omega)
  · exact avoid _ (leadingCoeff_ne_zero.mpr hi.ne_zero) ((le_max_left _ _).trans_lt hlarge)
  · intro x hx
    have hR := avoid R (derivative_resultant_ne_zero f hi (by omega))
      ((le_max_right _ _).trans_lt hlarge)
    exact not_dvd_derivative_at_root f (by omega) p x hR hx

namespace Erdos978Intermediate

lemma prime_count_sublinear (A : ℕ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, A * N.primeCounting < N := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hπ : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) ≤ (Real.log 4 + 1) * (n : ℝ) / Real.log n := by
    simpa using hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  have hlog : ∀ᶠ n : ℕ in atTop, (A : ℝ) * (Real.log 4 + 1) < Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hcast).eventually_gt_atTop _
  apply eventually_atTop.mp
  filter_upwards [hπ, hlog, eventually_gt_atTop 1] with n hπn hlogn hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hupper := mul_le_mul_of_nonneg_left ((le_div_iff₀ hp).mp hπn) (Nat.cast_nonneg A : 0 ≤ (A : ℝ))
  have hlower := mul_lt_mul_of_pos_right hlogn (lt_trans zero_lt_one hn1)
  have hstrict : ((A : ℝ) * n.primeCounting) * Real.log n < (n : ℝ) * Real.log n := by
    nlinarith only [hupper, hlower]
  exact_mod_cast (lt_of_mul_lt_mul_right hstrict hp.le)

end Erdos978Intermediate

open Erdos978RootCount Erdos978Intermediate in
theorem OMA.solution : OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1_H2_R1.H1 := by
  classical
  intro f hi hd
  dsimp only
  intro A hA
  let k := f.natDegree - 2
  obtain ⟨D, Y₀, _, hroots⟩ := eventual_bound f hi hd
  obtain ⟨N₀, hsmall⟩ := prime_count_sublinear (A * D)
  refine ⟨max N₀ (Y₀ * Y₀), ?_⟩
  intro N hN
  let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
  let count (p : ℕ) := ((Finset.range (p ^ k)).filter fun (r : ℕ) =>
    (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card
  have hsqrt : Y₀ ≤ N.sqrt := Nat.le_sqrt.mpr ((le_max_right _ _).trans hN)
  have hcard : S.card ≤ N.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp hI).2, hprime⟩
  have hsum : (∑ p ∈ S, count p) ≤ N.primeCounting * D := calc
    _ ≤ ∑ _p ∈ S, D := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hp
      exact hroots p hprime (hsqrt.trans_lt (Finset.mem_Ioc.mp hI).1)
    _ = S.card * D := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard
  change A * (∑ p ∈ S, count p) < N
  calc
    _ ≤ A * (N.primeCounting * D) := Nat.mul_le_mul_left _ hsum
    _ = (A * D) * N.primeCounting := by ring
    _ < _ := hsmall N ((le_max_left _ _).trans hN)
