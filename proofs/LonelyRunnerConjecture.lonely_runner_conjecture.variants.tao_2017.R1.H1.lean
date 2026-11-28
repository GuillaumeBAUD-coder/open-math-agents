import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.MeanInequalitiesPow

/-!
Proof of LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017.R1.H1.

Following Green-Walker (2021) and Hu-Jing (2026), combined with pair_overlap_lower_bound
adapted from PR #11345 by @John-A-McMahon for the reduction by @jared-jasinski.
-/

section Part12
open MeasureTheory MeasureTheory.Measure Function Metric Set Filter


-- Adapted from PR #11345 (@John-A-McMahon)
lemma pair_overlap_lower_bound (n u v D : ℕ) (hn : 2 ≤ n)
    (hu : 0 < u) (_hv : 0 < v) (hD : 0 < D)
    (hheight : max u v ≤ D * Nat.gcd u v) :
    1 / ((n : ℝ) * D) ≤ volume.real
      (((fun t : UnitAddCircle => (u : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ)))) ∩
       ((fun t : UnitAddCircle => (v : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ))))) := by
  let g := Nat.gcd u v
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let r : ℝ := 1 / (2 * (n : ℝ) * D)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : 2 * r ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hND : (1 : ℝ) ≤ (n : ℝ) * D := by
      simpa using mul_le_mul hn1 hD1 zero_le_one (by positivity : (0 : ℝ) ≤ n)
    dsimp [r]
    rw [mul_one_div]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * n * D)).2
    nlinarith
  have hmul : (D : ℝ) * r = 1 / (2 * (n : ℝ)) := by
    dsimp [r]
    field_simp [hnR.ne', hDR.ne']
  have hsub (w : ℕ) (hw : g ∣ w) (hbound : w ≤ D * g) :
      (fun t : UnitAddCircle => (g : ℤ) • t) ⁻¹' closedBall 0 r ⊆
        (fun t : UnitAddCircle => (w : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ))) := by
    intro t ht
    have hnorm : ‖(g : ℤ) • t‖ ≤ r := by
      simpa only [mem_preimage, mem_closedBall, dist_zero_right] using ht
    have hwD : w / g ≤ D := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hbound)
    have hwDR : ((w / g : ℕ) : ℝ) ≤ D := by exact_mod_cast hwD
    have heq : (w : ℤ) • t = (w / g : ℕ) • ((g : ℤ) • t) := by
      calc
        (w : ℤ) • t = (((w / g) * g : ℕ) : ℤ) • t := by
          rw [Nat.div_mul_cancel hw]
        _ = ((w / g : ℕ) : ℤ) • ((g : ℤ) • t) := by
          rw [Nat.cast_mul, mul_smul]
        _ = (w / g : ℕ) • ((g : ℤ) • t) := natCast_zsmul _ _
    change dist ((w : ℤ) • t) 0 ≤ _
    rw [dist_zero_right, heq]
    calc
      ‖(w / g : ℕ) • ((g : ℤ) • t)‖ ≤ ((w / g : ℕ) : ℝ) * ‖(g : ℤ) • t‖ :=
        norm_nsmul_le
      _ ≤ (D : ℝ) * r := mul_le_mul hwDR hnorm (norm_nonneg _) (by positivity)
      _ = _ := hmul
  have hm : MeasurePreserving (fun t : UnitAddCircle => (g : ℤ) • t) volume volume :=
    measurePreserving_zsmul volume (by exact_mod_cast hg.ne')
  have hmass : volume.real
      ((fun t : UnitAddCircle => (g : ℤ) • t) ⁻¹' closedBall 0 r) =
        1 / ((n : ℝ) * D) := by
    unfold Measure.real
    rw [hm.measure_preimage measurableSet_closedBall.nullMeasurableSet,
      AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by positivity)),
      min_eq_right hrsmall]
    dsimp [r]
    field_simp [hnR.ne', hDR.ne']
  rw [← hmass]
  refine measureReal_mono ?_ (by finiteness)
  exact subset_inter
    (hsub u (Nat.gcd_dvd_left u v) ((le_max_left u v).trans hheight))
    (hsub v (Nat.gcd_dvd_right u v) ((le_max_right u v).trans hheight))

lemma matching_overlap_lower_bound {n : ℕ} (hn : 2 ≤ n) (v : Fin n ↪ ℕ) (hv : ∀ i, 0 < v i)
    {D m : ℕ} (hD : 0 < D) (e : Fin m × Bool ↪ Fin n)
    (he : ∀ p : Fin m, max (v (e (p, false))) (v (e (p, true))) ≤
      D * Nat.gcd (v (e (p, false))) (v (e (p, true)))) :
    let A (i : Fin n) : Set UnitAddCircle :=
      (fun t => (v i : ℤ) • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
    (m : ℝ) / ((n : ℝ) * D) ≤ ∑ i, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j) := by
  classical
  intro A
  let F (i : Fin n) : ℝ := volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j)
  have hinj : Function.Injective (fun p : Fin m => e (p, false)) := fun p q hpq =>
    congrArg Prod.fst (e.injective hpq)
  have hpoint (p : Fin m) : 1 / ((n : ℝ) * D) ≤ F (e (p, false)) := by
    have hne : e (p, true) ≠ e (p, false) := by
      intro h
      exact Bool.noConfusion (congrArg Prod.snd (e.injective h))
    have hpair := pair_overlap_lower_bound n (v (e (p, false))) (v (e (p, true))) D
      hn (hv _) (hv _) hD (he p)
    refine hpair.trans (measureReal_mono ?_ (by finiteness))
    rintro t ⟨ht, hs⟩
    exact ⟨ht, mem_iUnion.mpr ⟨e (p, true), mem_iUnion.mpr ⟨hne, hs⟩⟩⟩
  calc
    (m : ℝ) / ((n : ℝ) * D) = ∑ _p : Fin m, 1 / ((n : ℝ) * D) := by simp [div_eq_mul_inv]
    _ ≤ ∑ p : Fin m, F (e (p, false)) := Finset.sum_le_sum fun p _ => hpoint p
    _ = ∑ i ∈ Finset.univ.image (fun p : Fin m => e (p, false)), F i := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hinj h
    _ ≤ ∑ i : Fin n, F i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => measureReal_nonneg

-- Smooth and rough parts relative to a finite set of primes P
private def smoothPart (P : Finset ℕ) (x : ℕ) : ℕ := ∏ p ∈ P, p ^ (x.factorization p)
private def roughPart (P : Finset ℕ) (x : ℕ) : ℕ := x / smoothPart P x

private lemma smoothPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (_x : ℕ) :
    0 < smoothPart P _x := by
  unfold smoothPart
  exact Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _

private lemma smoothPart_dvd (P : Finset ℕ) (_hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    smoothPart P x ∣ x := by
  by_cases hx : x = 0
  · subst hx; exact dvd_zero _
  · unfold smoothPart
    have hprod : x.factorization.prod (fun p e => p ^ e) = x :=
      Nat.prod_factorization_pow_eq_self hx
    nth_rw 2 [← hprod]
    unfold Finsupp.prod
    have h1 : ∏ p ∈ P, p ^ (x.factorization p) =
        ∏ p ∈ P ∩ x.factorization.support, p ^ (x.factorization p) := by
      rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ x.factorization.support)]
      have hsub : P.filter (fun p => p ∈ x.factorization.support) = P ∩ x.factorization.support := by
        ext p; simp [Finset.mem_inter]
      have hone : ∏ p ∈ P.filter (fun p => p ∉ x.factorization.support), p ^ (x.factorization p) = 1 := by
        refine Finset.prod_eq_one fun p hp => ?_
        have hnot : x.factorization p = 0 := Finsupp.notMem_support_iff.mp (Finset.mem_filter.mp hp).2
        rw [hnot, pow_zero]
      rw [hsub, hone, mul_one]
    rw [h1]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun p => p ^ (x.factorization p)) Finset.inter_subset_right

private lemma smoothPart_mul_roughPart (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    smoothPart P x * roughPart P x = x :=
  Nat.mul_div_cancel' (smoothPart_dvd P hP x)

private lemma smoothPart_primeFactors_subset (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    (smoothPart P x).primeFactors ⊆ P := by
  intro q hq
  have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  have hqdvd : q ∣ ∏ p ∈ P, p ^ (x.factorization p) := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨p, hp, hqp_dvd⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp hqdvd
  have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hqp (hP p hp)).mp (hqp.prime.dvd_of_dvd_pow hqp_dvd)
  exact hqp_eq ▸ hp

private lemma factorization_smoothPart (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ)
    {p : ℕ} (hp : p ∈ P) : (smoothPart P x).factorization p = x.factorization p := by
  classical
  unfold smoothPart
  rw [← Finset.mul_prod_erase P (fun q => q ^ (x.factorization q)) hp]
  have hpos1 : p ^ (x.factorization p) ≠ 0 := pow_ne_zero _ (hP p hp).ne_zero
  have hpos2 : (∏ q ∈ P.erase p, q ^ (x.factorization q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (hP q (Finset.mem_of_mem_erase hq)).ne_zero
  rw [Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul, (hP p hp).factorization_self, mul_one]
  have hzero : (∏ q ∈ P.erase p, q ^ (x.factorization q)).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨q, hq, hqdvd⟩ := (Prime.dvd_finsetProd_iff (hP p hp).prime _).mp hdvd
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q (Finset.mem_of_mem_erase hq))).mp
      ((hP p hp).prime.dvd_of_dvd_pow hqdvd)
    exact (Finset.mem_erase.mp hq).1 hpq.symm
  omega

private lemma roughPart_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) {x : ℕ} (hx : 0 < x) :
    Nat.Coprime (roughPart P x) (∏ p ∈ P, p) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  rw [Nat.coprime_comm, (hP p hp).coprime_iff_not_dvd]
  intro hdvd
  have hrpos : roughPart P x ≠ 0 := by
    have := smoothPart_mul_roughPart P hP x
    intro h0; rw [h0, mul_zero] at this; omega
  have hfac_r : 0 < (roughPart P x).factorization p :=
    (hP p hp).factorization_pos_of_dvd hrpos hdvd
  have hmul : smoothPart P x * roughPart P x = x := smoothPart_mul_roughPart P hP x
  have hspos : smoothPart P x ≠ 0 := (smoothPart_pos P hP x).ne'
  have hfac := congrArg (fun n => n.factorization p) hmul
  rw [Nat.factorization_mul hspos hrpos, Finsupp.add_apply, factorization_smoothPart P hP x hp] at hfac
  omega

private lemma sum_smooth_le_prod (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (f : ℕ → ℝ) (hf0 : ∀ p ∈ P, 0 ≤ f p) (hf1 : ∀ p ∈ P, f p < 1)
    (N : ℕ) (T : Finset ℕ) (hT1 : ∀ s ∈ T, 1 ≤ s ∧ s ≤ N) (hTp : ∀ s ∈ T, s.primeFactors ⊆ P) :
    (∑ s ∈ T, ∏ p ∈ P, (f p) ^ (s.factorization p)) ≤ ∏ p ∈ P, (1 - f p)⁻¹ := by
  classical
  let box : Finset ((p : ℕ) → p ∈ P → ℕ) := P.pi (fun _ => Finset.range (N + 1))
  let embed : ℕ → (p : ℕ) → p ∈ P → ℕ := fun s p _ => s.factorization p
  have hinj : Set.InjOn embed T := by
    intro s₁ hs₁ s₂ hs₂ heq
    have hs1ne : s₁ ≠ 0 := by have := (hT1 s₁ hs₁).1; omega
    have hs2ne : s₂ ≠ 0 := by have := (hT1 s₂ hs₂).1; omega
    refine Nat.eq_of_factorization_eq hs1ne hs2ne fun p => ?_
    by_cases hp : p ∈ P
    · exact congrFun (congrFun heq p) hp
    · have h1 : s₁.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact fun hmem => hp (hTp s₁ hs₁ hmem)
      have h2 : s₂.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact fun hmem => hp (hTp s₂ hs₂ hmem)
      rw [h1, h2]
  have himg : (T.image embed) ⊆ box := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hs_le : s ≤ N := (hT1 s hs).2
    have hs_ne : s ≠ 0 := by have := (hT1 s hs).1; omega
    have hp_ge2 : 2 ≤ p := (hP p hp).two_le
    have hpow_le : p ^ (s.factorization p) ≤ s := by
      have hdvd : p ^ (s.factorization p) ∣ s := Nat.ordProj_dvd s p
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hs_ne) hdvd
    have hlt : s.factorization p < 2 ^ (s.factorization p) := Nat.lt_two_pow_self
    have h2le : 2 ^ (s.factorization p) ≤ p ^ (s.factorization p) :=
      Nat.pow_le_pow_left hp_ge2 _
    dsimp [embed]
    omega
  have hrew : (∑ s ∈ T, ∏ p ∈ P, (f p) ^ (s.factorization p)) =
      ∑ g ∈ T.image embed, ∏ x ∈ P.attach, (f x.1) ^ (g x.1 x.2) := by
    rw [Finset.sum_image (fun s₁ hs₁ s₂ hs₂ h => hinj hs₁ hs₂ h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (Finset.prod_attach P (fun p => (f p) ^ (s.factorization p))).symm
  rw [hrew]
  have hle1 : (∑ g ∈ T.image embed, ∏ x ∈ P.attach, (f x.1) ^ (g x.1 x.2)) ≤
      ∑ g ∈ box, ∏ x ∈ P.attach, (f x.1) ^ (g x.1 x.2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg himg fun g _ _ => ?_
    exact Finset.prod_nonneg fun x _ => pow_nonneg (hf0 x.1 x.2) _
  have hprod_sum : (∑ g ∈ box, ∏ x ∈ P.attach, (f x.1) ^ (g x.1 x.2)) =
      ∏ p ∈ P, ∑ e ∈ Finset.range (N + 1), (f p) ^ e := by
    simpa [box] using (Finset.prod_sum P (fun _ => Finset.range (N + 1)) (fun p e => (f p) ^ e)).symm
  refine hle1.trans (hprod_sum.le.trans ?_)
  refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun e _ => pow_nonneg (hf0 p ‹_›) _) ?_
  intro p hp
  have hpos : 0 < 1 - f p := sub_pos.mpr (hf1 p hp)
  rw [geom_sum_eq (hf1 p hp).ne (N + 1)]
  have hrew_div : (f p ^ (N + 1) - 1) / (f p - 1) = (1 - f p ^ (N + 1)) / (1 - f p) := by
    field_simp [show f p - 1 ≠ 0 by linarith, hpos.ne']; ring
  rw [hrew_div, ← one_div]
  have hpow0 : 0 ≤ (f p) ^ (N + 1) := pow_nonneg (hf0 p hp) _
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

private lemma harmonic_dyadic_lower (K : ℕ) :
    1 + (K : ℝ) / 2 ≤ ∑ k ∈ Finset.Icc (1 : ℕ) (2 ^ K), (1 : ℝ) / (k : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hsplit : Finset.Icc (1 : ℕ) (2 ^ (K + 1)) =
        Finset.Icc (1 : ℕ) (2 ^ K) ∪ Finset.Icc (2 ^ K + 1 : ℕ) (2 ^ (K + 1)) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      have : 1 ≤ 2 ^ K := Nat.one_le_two_pow
      have : 2 ^ K < 2 ^ (K + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self K)
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) (2 ^ K)) (Finset.Icc (2 ^ K + 1 : ℕ) (2 ^ (K + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hblock : (1 : ℝ) / 2 ≤ ∑ k ∈ Finset.Icc (2 ^ K + 1 : ℕ) (2 ^ (K + 1)), (1 : ℝ) / (k : ℝ) := by
      have hcard : (Finset.Icc (2 ^ K + 1 : ℕ) (2 ^ (K + 1))).card = 2 ^ K := by
        have hpow1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        have hpow2 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by rw [pow_succ]; ring
        rw [Nat.card_Icc]
        omega
      have hle : ∀ k ∈ Finset.Icc (2 ^ K + 1 : ℕ) (2 ^ (K + 1)),
          (1 : ℝ) / (2 ^ (K + 1) : ℝ) ≤ (1 : ℝ) / (k : ℝ) := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
        have hkle : (k : ℝ) ≤ (2 ^ (K + 1) : ℝ) := by exact_mod_cast hk.2
        exact one_div_le_one_div_of_le hkpos hkle
      have hsum := Finset.sum_le_sum hle
      simp only [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
      have hhalf : (1 : ℝ) / 2 = ((2 ^ K : ℕ) : ℝ) * ((1 : ℝ) / (2 ^ (K + 1) : ℝ)) := by
        have hpow : (2 ^ (K + 1) : ℝ) = 2 * ((2 ^ K : ℕ) : ℝ) := by
          push_cast; rw [pow_succ]; ring
        have h2pos : ((2 ^ K : ℕ) : ℝ) ≠ 0 := by positivity
        rw [hpow]
        field_simp [h2pos]
      exact hhalf.le.trans hsum
    push_cast
    linarith

private lemma exists_prime_finset_small_density (C : ℝ) (hC : 1 ≤ C) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ 1 / (8 * C) := by
  let K : ℕ := Nat.ceil (16 * C)
  let N : ℕ := 2 ^ K
  let P : Finset ℕ := (Finset.Icc 2 N).filter Nat.Prime
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  refine ⟨P, hP, ?_⟩
  have hsum : (∑ s ∈ Finset.Icc 1 N, ∏ p ∈ P, (1 / (p : ℝ)) ^ (s.factorization p)) ≤
      ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := by
    refine sum_smooth_le_prod P hP (fun p => 1 / (p : ℝ))
      (fun p _ => by positivity)
      (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        rw [div_lt_one (by linarith)]
        linarith)
      N (Finset.Icc 1 N)
      (fun s hs => Finset.mem_Icc.mp hs)
      (fun s hs q hq => by
        have hs1 := Finset.mem_Icc.mp hs
        have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
        have hqdvd : q ∣ s := Nat.dvd_of_mem_primeFactors hq
        have hqle : q ≤ s := Nat.le_of_dvd (by omega) hqdvd
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.two_le, hqle.trans hs1.2⟩, hqp⟩)
  have hrewrite : ∀ s ∈ Finset.Icc 1 N,
      (∏ p ∈ P, (1 / (p : ℝ)) ^ (s.factorization p)) = (1 : ℝ) / (s : ℝ) := by
    intro s hs
    have hs1 := Finset.mem_Icc.mp hs
    have hsne : s ≠ 0 := by omega
    have hsp : smoothPart P s = s := by
      have hsub : s.primeFactors ⊆ P := fun q hq => by
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqle := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.two_le, hqle.trans hs1.2⟩, hqp⟩
      unfold smoothPart
      have hprod := Nat.prod_factorization_pow_eq_self hsne
      nth_rw 2 [← hprod]
      unfold Finsupp.prod
      rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ s.factorization.support)]
      have hfilt : P.filter (fun p => p ∈ s.factorization.support) = s.factorization.support := by
        ext p
        rw [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · intro h
          have hmem : p ∈ s.primeFactors := by rwa [← Nat.support_factorization]
          exact ⟨hsub hmem, h⟩
      have hone : ∏ p ∈ P.filter (fun p => p ∉ s.factorization.support), p ^ (s.factorization p) = 1 := by
        refine Finset.prod_eq_one fun p hp => ?_
        have hnot : s.factorization p = 0 := Finsupp.notMem_support_iff.mp (Finset.mem_filter.mp hp).2
        rw [hnot, pow_zero]
      rw [hfilt, hone, mul_one]
    calc
      (∏ p ∈ P, (1 / (p : ℝ)) ^ (s.factorization p))
          = ∏ p ∈ P, (1 : ℝ) / ((p : ℝ) ^ (s.factorization p)) := by
            refine Finset.prod_congr rfl fun p _ => ?_
            rw [one_div, inv_pow, one_div]
      _ = (1 : ℝ) / ((smoothPart P s : ℕ) : ℝ) := by
            unfold smoothPart
            push_cast
            rw [Finset.prod_div_distrib, Finset.prod_const_one]
      _ = (1 : ℝ) / (s : ℝ) := by rw [hsp]
  have hharm : 1 + (K : ℝ) / 2 ≤ ∑ s ∈ Finset.Icc 1 N, (1 : ℝ) / (s : ℝ) := harmonic_dyadic_lower K
  have heq_sum : (∑ s ∈ Finset.Icc 1 N, ∏ p ∈ P, (1 / (p : ℝ)) ^ (s.factorization p)) =
      ∑ s ∈ Finset.Icc 1 N, (1 : ℝ) / (s : ℝ) := Finset.sum_congr rfl hrewrite
  rw [heq_sum] at hsum
  have hbig : 8 * C ≤ 1 + (K : ℝ) / 2 := by
    have hK : 16 * C ≤ (K : ℝ) := Nat.le_ceil (16 * C)
    linarith
  have hinv : 8 * C ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := hbig.trans (hharm.trans hsum)
  have hprod_pos : 0 < ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    linarith [show (1 : ℝ) / p ≤ 1 / 2 by exact one_div_le_one_div_of_le (by norm_num) hp2]
  have hprod_inv : ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ = (∏ p ∈ P, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
  rw [hprod_inv] at hinv
  rw [le_div_iff₀ (by positivity), mul_comm, ← le_div_iff₀ hprod_pos, div_eq_mul_inv, one_mul]
  exact hinv

private lemma rough_count_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (A : ℕ) :
    (((Finset.Icc 1 A).filter (fun r => Nat.Coprime r (∏ p ∈ P, p))).card : ℝ) ≤
      (A : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) + ((∏ p ∈ P, p : ℕ) : ℝ) := by
  let M : ℕ := ∏ p ∈ P, p
  have hMpos : 0 < M := Finset.prod_pos fun p hp => (hP p hp).pos
  let S := (Finset.Icc 1 A).filter (fun r => Nat.Coprime r M)
  let T := Finset.range (A / M + 1) ×ˢ ((Finset.range M).filter (fun x => Nat.Coprime x M))
  have hinj : Set.InjOn (fun r => (r / M, r % M)) S := by
    intro r₁ _ r₂ _ heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp at h1 h2
    have hr1 : M * (r₁ / M) + r₁ % M = r₁ := Nat.div_add_mod r₁ M
    have hr2 : M * (r₂ / M) + r₂ % M = r₂ := Nat.div_add_mod r₂ M
    rw [← hr1, ← hr2, h1, h2]
  have himg : S.image (fun r => (r / M, r % M)) ⊆ T := by
    intro xy hxy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hxy
    have hr' := Finset.mem_filter.mp hr
    have hrle : r ≤ A := (Finset.mem_Icc.mp hr'.1).2
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt r hMpos), ?_⟩⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right hrle)
    · have hc : Nat.Coprime r M := hr'.2
      have hmod : M.Coprime (r % M) := by
        rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm, ← Nat.coprime_iff_gcd_eq_one] at hc
      exact hmod.symm
  have hcard : S.card ≤ T.card := by
    calc
      S.card = (S.image (fun r => (r / M, r % M))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ T.card := Finset.card_le_card himg
  have hTcard : T.card = (A / M + 1) * M.totient := by
    rw [Finset.card_product, Finset.card_range]
    congr 1
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext x
    simp [Nat.coprime_comm]
  have htot : (M.totient : ℝ) / (M : ℝ) = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have hprod_tot : M.totient = ∏ p ∈ P, (p - 1) := by
      clear hcard hTcard S T hinj himg A
      induction P using Finset.induction with
      | empty => simp [M]
      | @insert p P' hp ih =>
        have hP' : ∀ q ∈ P', Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
        have hpp : Nat.Prime p := hP p (Finset.mem_insert_self p P')
        have hcop : Nat.Coprime p (∏ q ∈ P', q) := by
          refine Nat.Coprime.prod_right fun q hq => ?_
          exact (Nat.coprime_primes hpp (hP' q hq)).mpr (fun heq => hp (heq ▸ hq))
        change (∏ q ∈ insert p P', q).totient = ∏ q ∈ insert p P', (q - 1)
        rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
          Nat.totient_prime hpp, ih hP' (Finset.prod_pos fun q hq => (hP' q hq).pos)]
    rw [hprod_tot]
    have hM_cast : (M : ℝ) = ∏ p ∈ P, (p : ℝ) := by unfold M; push_cast; rfl
    have htot_cast : ((∏ p ∈ P, (p - 1) : ℕ) : ℝ) = ∏ p ∈ P, ((p : ℝ) - 1) := by
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp1 : 1 ≤ p := (hP p hp).one_le
      rw [Nat.cast_sub hp1, Nat.cast_one]
    rw [htot_cast, hM_cast, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hppos : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    field_simp [hppos]
  have hdiv : ((A / M : ℕ) : ℝ) ≤ (A : ℝ) / (M : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hMpos)]
    exact_mod_cast Nat.div_mul_le_self A M
  have htot_le : (M.totient : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
  calc
    (S.card : ℝ) ≤ ((A / M + 1) * M.totient : ℕ) := by exact_mod_cast hcard.trans_eq hTcard
    _ = ((A / M : ℕ) : ℝ) * M.totient + M.totient := by push_cast; ring
    _ ≤ ((A : ℝ) / (M : ℝ)) * M.totient + M := by gcongr
    _ = (A : ℝ) * ((M.totient : ℝ) / (M : ℝ)) + M := by ring
    _ = (A : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) + M := by rw [htot]

private lemma fiber_pairing {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (f : α → β) (R : Finset β) (hf : ∀ x ∈ W, f x ∈ R) :
    ∃ L : List (α × α),
      (∀ p ∈ L, p.1 ∈ W ∧ p.2 ∈ W ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2) ∧
      (L.flatMap fun p => [p.1, p.2]).Nodup ∧
      W.card ≤ 2 * L.length + R.card := by
  classical
  induction hcard : W.card using Nat.strong_induction_on generalizing W with
  | h k ih =>
    by_cases hpair : ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ f x = f y
    · obtain ⟨x, hxW, y, hyW, hxy, hfxy⟩ := hpair
      let W' := (W.erase x).erase y
      have hW'sub : W' ⊆ W := fun z hz => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
      have hy_in : y ∈ W.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyW⟩
      have hW'card : W'.card + 2 = W.card := by
        have h1 : (W.erase x).card + 1 = W.card := Finset.card_erase_add_one hxW
        have h2 : W'.card + 1 = (W.erase x).card := Finset.card_erase_add_one hy_in
        omega
      have hlt : W'.card < k := by omega
      obtain ⟨L', hL'mem, hL'nodup, hL'card⟩ :=
        ih W'.card hlt W' (fun z hz => hf z (hW'sub hz)) rfl
      refine ⟨(x, y) :: L', ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hxW, hyW, hxy, hfxy⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hL'mem p hp'
          exact ⟨hW'sub h1, hW'sub h2, h3, h4⟩
      · change (x :: y :: L'.flatMap fun p => [p.1, p.2]).Nodup
        have hx_not : x ∉ L'.flatMap fun p => [p.1, p.2] := by
          intro hmem
          obtain ⟨p, hpL, hpx⟩ := List.mem_flatMap.mp hmem
          obtain ⟨hp1, hp2, _, _⟩ := hL'mem p hpL
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpx
          rcases hpx with rfl | rfl
          · exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hp1)).1 rfl
          · exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hp2)).1 rfl
        have hy_not : y ∉ L'.flatMap fun p => [p.1, p.2] := by
          intro hmem
          obtain ⟨p, hpL, hpy⟩ := List.mem_flatMap.mp hmem
          obtain ⟨hp1, hp2, _, _⟩ := hL'mem p hpL
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpy
          rcases hpy with rfl | rfl
          · exact (Finset.mem_erase.mp hp1).1 rfl
          · exact (Finset.mem_erase.mp hp2).1 rfl
        rw [List.nodup_cons, List.nodup_cons]
        refine ⟨?_, hy_not, hL'nodup⟩
        simp only [List.mem_cons]
        rintro (rfl | hmem)
        · exact hxy rfl
        · exact hx_not hmem
      · simp only [List.length_cons]
        omega
    · push Not at hpair
      have hinj : Set.InjOn f W := by
        intro x hx y hy heq
        by_contra hne
        exact hpair x hx y hy hne heq
      have himg : W.image f ⊆ R := by
        intro r hr
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
        exact hf x hx
      have hle : W.card ≤ R.card := by
        calc
          W.card = (W.image f).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ R.card := Finset.card_le_card himg
      exact ⟨[], by simp, by simp, by omega⟩

private lemma flatMap_pair_length {α : Type*} (L : List (α × α)) :
    (L.flatMap fun p => [p.1, p.2]).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]; ring

private lemma flatMap_pair_getElem {α : Type*} (L : List (α × α)) (i : Fin L.length) (b : Bool)
    (hlt : 2 * i.1 + (if b then 1 else 0) < (L.flatMap fun p => [p.1, p.2]).length) :
    (if b then L[i.1].2 else L[i.1].1) = (L.flatMap fun p => [p.1, p.2])[2 * i.1 + (if b then 1 else 0)] := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons hd tl ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · cases b <;> simp
    · have hlen : 2 * j.1 + (if b then 1 else 0) < (tl.flatMap fun p => [p.1, p.2]).length := by
        rw [flatMap_pair_length] at hlt ⊢; simp at hlt; omega
      have hidx : 2 * (j.succ : ℕ) + (if b then 1 else 0) =
          (2 * j.1 + (if b then 1 else 0)) + 2 := by simp; omega
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ, hidx]
      exact ih j hlen

private lemma list_pairs_to_emb {n : ℕ} (L : List (Fin n × Fin n))
    (hnodup : (L.flatMap fun p => [p.1, p.2]).Nodup) :
    ∃ e : Fin L.length × Bool ↪ Fin n,
      ∀ i : Fin L.length, e (i, false) = (L[i.1]'i.2).1 ∧ e (i, true) = (L[i.1]'i.2).2 := by
  let g : Fin L.length × Bool → Fin n :=
    fun (i, b) => if b then (L[i.1]'i.2).2 else (L[i.1]'i.2).1
  have hinj : Function.Injective g := by
    let flat := L.flatMap fun p => [p.1, p.2]
    have hflat_len : flat.length = 2 * L.length := flatMap_pair_length L
    let idx : Fin L.length × Bool → Fin flat.length := fun (i, b) =>
      ⟨2 * i.1 + (if b then 1 else 0), by
        rw [hflat_len]
        (cases b <;> simp); omega⟩
    have hidx_inj : Function.Injective idx := by
      intro ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ h
      have hv := congrArg Fin.val h
      dsimp [idx] at hv
      have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp at hv ⊢ <;> omega
      have hi : i₁ = i₂ := Fin.ext (by cases b₁ <;> cases b₂ <;> simp at hv ⊢ <;> omega)
      exact Prod.ext hi hb
    intro p₁ p₂ hp
    have hp1 := flatMap_pair_getElem L p₁.1 p₁.2 (idx p₁).2
    have hp2 := flatMap_pair_getElem L p₂.1 p₂.2 (idx p₂).2
    dsimp [g] at hp
    rw [hp1, hp2] at hp
    have hinj_get := List.nodup_iff_injective_getElem.mp hnodup
    let j₁ : Fin (L.flatMap fun p => [p.1, p.2]).length := ⟨(idx p₁).1, (idx p₁).2⟩
    let j₂ : Fin (L.flatMap fun p => [p.1, p.2]).length := ⟨(idx p₂).1, (idx p₂).2⟩
    have hj_eq : j₁ = j₂ := hinj_get (a₁ := j₁) (a₂ := j₂) hp
    exact hidx_inj (Fin.ext (congrArg Fin.val hj_eq))
  exact ⟨⟨g, hinj⟩, fun i => by simp [g]⟩

private lemma sqrt_pow_nat (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Real.sqrt (a ^ k) = (Real.sqrt a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha _), ih, pow_succ]

private lemma rational_box_pair_height {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {S D u v ax1 ax2 ay1 ay2 : ℕ} (hu : 0 < u) (_hv : 0 < v)
    (_hax1 : 0 < ax1) (_hax2 : 0 < ax2) (hay1 : 0 < ay1) (hay2 : 0 < ay2)
    (hSD : S ^ 2 ≤ D)
    (hsx1 : smoothPart P ax1 ≤ S) (hsx2 : smoothPart P ax2 ≤ S)
    (hsy1 : smoothPart P ay1 ≤ S) (hsy2 : smoothPart P ay2 ≤ S)
    (hrx : roughPart P ax1 = roughPart P ay1) (hry : roughPart P ax2 = roughPart P ay2)
    (hnat : u * (ax2 * ay1) = v * (ay2 * ax1)) :
    max u v ≤ D * Nat.gcd u v := by
  have hmul_x1 := smoothPart_mul_roughPart P hP ax1
  have hmul_x2 := smoothPart_mul_roughPart P hP ax2
  have hmul_y1 := smoothPart_mul_roughPart P hP ay1
  have hmul_y2 := smoothPart_mul_roughPart P hP ay2
  let sx1 := smoothPart P ax1
  let sx2 := smoothPart P ax2
  let sy1 := smoothPart P ay1
  let sy2 := smoothPart P ay2
  let r₁ := roughPart P ay1
  let r₂ := roughPart P ay2
  have hr1_pos : 0 < r₁ := by
    by_cases h0 : r₁ = 0
    · dsimp [r₁] at h0; rw [h0, mul_zero] at hmul_y1; omega
    · exact Nat.pos_of_ne_zero h0
  have hr2_pos : 0 < r₂ := by
    by_cases h0 : r₂ = 0
    · dsimp [r₂] at h0; rw [h0, mul_zero] at hmul_y2; omega
    · exact Nat.pos_of_ne_zero h0
  have hx2_eq : ax2 = sx2 * r₂ := by dsimp [r₂]; rw [← hry]; exact hmul_x2.symm
  have hy1_eq : ay1 = sy1 * r₁ := hmul_y1.symm
  have hy2_eq : ay2 = sy2 * r₂ := hmul_y2.symm
  have hx1_eq : ax1 = sx1 * r₁ := by dsimp [r₁]; rw [← hrx]; exact hmul_x1.symm
  have hcancel : (r₁ * r₂) * (u * (sx2 * sy1)) = (r₁ * r₂) * (v * (sy2 * sx1)) := by
    calc
      (r₁ * r₂) * (u * (sx2 * sy1)) = u * ((sx2 * r₂) * (sy1 * r₁)) := by ring
      _ = u * (ax2 * ay1) := by rw [← hx2_eq, ← hy1_eq]
      _ = v * (ay2 * ax1) := hnat
      _ = v * ((sy2 * r₂) * (sx1 * r₁)) := by rw [hy2_eq, hx1_eq]
      _ = (r₁ * r₂) * (v * (sy2 * sx1)) := by ring
  have hsm_eq : u * (sx2 * sy1) = v * (sy2 * sx1) :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr1_pos hr2_pos) hcancel
  let P₁ := sx1 * sy2
  let P₂ := sy1 * sx2
  have hP1_pos : 0 < P₁ := Nat.mul_pos (smoothPart_pos P hP _) (smoothPart_pos P hP _)
  have hP2_pos : 0 < P₂ := Nat.mul_pos (smoothPart_pos P hP _) (smoothPart_pos P hP _)
  have hP1_le : P₁ ≤ D := ((Nat.mul_le_mul hsx1 hsy2).trans_eq (by ring)).trans hSD
  have hP2_le : P₂ ≤ D := ((Nat.mul_le_mul hsy1 hsx2).trans_eq (by ring)).trans hSD
  have heq : u * P₂ = v * P₁ := by
    calc
      u * P₂ = u * (sx2 * sy1) := by dsimp [P₂]; ring
      _ = v * (sy2 * sx1) := hsm_eq
      _ = v * P₁ := by dsimp [P₁]; ring
  let g := Nat.gcd u v
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hu
  have hgu : g ∣ u := Nat.gcd_dvd_left _ _
  have hgv : g ∣ v := Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime (u / g) (v / g) := Nat.coprime_div_gcd_div_gcd hg
  have hu_eq : u = g * (u / g) := (Nat.mul_div_cancel' hgu).symm
  have hv_eq : v = g * (v / g) := (Nat.mul_div_cancel' hgv).symm
  have hdiv_eq : (u / g) * P₂ = (v / g) * P₁ := by
    have hh := heq
    rw [hu_eq, hv_eq] at hh
    exact Nat.eq_of_mul_eq_mul_left hg (by linarith)
  have hdvd1 : u / g ∣ P₁ := hcop.dvd_of_dvd_mul_left ⟨P₂, hdiv_eq.symm⟩
  have hdvd2 : v / g ∣ P₂ := hcop.symm.dvd_of_dvd_mul_left ⟨P₁, hdiv_eq⟩
  have hule : u ≤ D * g := by
    calc
      u = (u / g) * g := (Nat.div_mul_cancel hgu).symm
      _ ≤ P₁ * g := Nat.mul_le_mul_right g (Nat.le_of_dvd hP1_pos hdvd1)
      _ ≤ D * g := Nat.mul_le_mul_right g hP1_le
  have hvle : v ≤ D * g := by
    calc
      v = (v / g) * g := (Nat.div_mul_cancel hgv).symm
      _ ≤ P₂ * g := Nat.mul_le_mul_right g (Nat.le_of_dvd hP2_pos hdvd2)
      _ ≤ D * g := Nat.mul_le_mul_right g hP2_le
  exact max_le hule hvle

-- Hu and Jing Lemma 5.1
lemma rational_box_matching :
    ∀ C : ℝ, 1 ≤ C → ∃ (D : ℕ) (η : ℝ), 0 < D ∧ 0 < η ∧
      ∀ (n : ℕ) (v : Fin n ↪ ℕ), (∀ i, 0 < v i) →
        ∀ U : Finset (Fin n), 2 ≤ U.card →
        ∀ (ξ : ℚ) (A B : ℕ), 0 < ξ → 0 < A → 0 < B →
          (A : ℝ) * B ≤ C * U.card →
          (∀ i ∈ U, ∃ a b : ℕ, 0 < a ∧ a ≤ A ∧ 0 < b ∧ b ≤ B ∧
            (v i : ℚ) = ξ * a / b) →
          ∃ (m : ℕ) (e : Fin m × Bool ↪ Fin n), η * U.card ≤ m ∧
            ∀ p : Fin m, e (p, false) ∈ U ∧ e (p, true) ∈ U ∧
              max (v (e (p, false))) (v (e (p, true))) ≤
                D * Nat.gcd (v (e (p, false))) (v (e (p, true))) := by
  classical
  intro C hC
  obtain ⟨P, hP, hdP⟩ := exists_prime_finset_small_density C hC
  let M : ℕ := ∏ p ∈ P, p
  let A_P : ℝ := ∏ p ∈ P, (1 - 1 / Real.sqrt (p : ℝ))⁻¹
  have hPsqrt1 : ∀ p ∈ P, 1 / Real.sqrt (p : ℝ) < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hs : 1 < Real.sqrt (p : ℝ) := by
      rw [Real.lt_sqrt (by positivity)]
      linarith
    exact (div_lt_one (by positivity)).mpr hs
  have hAP_pos : 0 < A_P := Finset.prod_pos fun p hp => inv_pos.mpr (sub_pos.mpr (hPsqrt1 p hp))
  let S : ℕ := Nat.ceil ((8 * C * A_P) ^ 2) + 1
  have hS_pos : 0 < S := Nat.succ_pos _
  let N₁ : ℕ := Nat.ceil (64 * (M : ℝ) ^ 2 * C) + 1
  let D_small : ℕ := Nat.ceil (C * (N₁ : ℝ)) + 1
  let D : ℕ := max (S ^ 2) D_small
  let η : ℝ := min (1 / 4 : ℝ) (1 / (N₁ : ℝ))
  refine ⟨D, η, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (pow_pos hS_pos 2) (le_max_left _ _)
  · positivity
  intro n v hv U hU ξ A B hξ hA hB harea hrepr
  let ab : Fin n → ℕ × ℕ := fun i =>
    if hi : i ∈ U then
      let h := hrepr i hi
      (h.choose, h.choose_spec.choose)
    else (1, 1)
  have hab_spec : ∀ i ∈ U, 0 < (ab i).1 ∧ (ab i).1 ≤ A ∧ 0 < (ab i).2 ∧ (ab i).2 ≤ B ∧
      (v i : ℚ) = ξ * (ab i).1 / (ab i).2 := by
    intro i hi
    dsimp [ab]
    rw [dif_pos hi]
    let h := hrepr i hi
    exact h.choose_spec.choose_spec
  have hab_inj : Set.InjOn ab U := by
    intro i hi j hj hij
    apply v.injective
    have hi' := hab_spec i hi
    have hj' := hab_spec j hj
    have hq : (v i : ℚ) = (v j : ℚ) := by
      rw [hi'.2.2.2.2, hj'.2.2.2.2, hij]
    exact_mod_cast hq
  -- Helper: cross-multiply ratio from representation
  have hcross : ∀ x ∈ U, ∀ y ∈ U,
      v x * ((ab x).2 * (ab y).1) = v y * ((ab y).2 * (ab x).1) := by
    intro x hxU y hyU
    have hx' := hab_spec x hxU
    have hy' := hab_spec y hyU
    have hbx_ne : ((ab x).2 : ℚ) ≠ 0 := by exact_mod_cast hx'.2.2.1.ne'
    have hby_ne : ((ab y).2 : ℚ) ≠ 0 := by exact_mod_cast hy'.2.2.1.ne'
    have h1 : (v x : ℚ) * (ab x).2 = ξ * (ab x).1 := by
      rw [hx'.2.2.2.2, div_mul_cancel₀ _ hbx_ne]
    have h2 : (v y : ℚ) * (ab y).2 = ξ * (ab y).1 := by
      rw [hy'.2.2.2.2, div_mul_cancel₀ _ hby_ne]
    have hq : (v x : ℚ) * (ab x).2 * (ab y).1 = (v y : ℚ) * (ab y).2 * (ab x).1 := by
      calc
        (v x : ℚ) * (ab x).2 * (ab y).1 = ξ * (ab x).1 * (ab y).1 := by rw [h1]
        _ = ξ * (ab y).1 * (ab x).1 := by ring
        _ = (v y : ℚ) * (ab y).2 * (ab x).1 := by rw [h2]
    have hnatq : ((v x * ((ab x).2 * (ab y).1) : ℕ) : ℚ) =
        ((v y * ((ab y).2 * (ab x).1) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast hnatq
  -- Helper: u * P2 = w * P1 with P1, P2 ≤ D implies max u w ≤ D * gcd u w
  have hheight_of_eq : ∀ u w P₁ P₂ : ℕ, 0 < u → 0 < P₁ → 0 < P₂ →
      P₁ ≤ D → P₂ ≤ D → u * P₂ = w * P₁ → max u w ≤ D * Nat.gcd u w := by
    intro u w P₁ P₂ hu hP1_pos hP2_pos hP1 hP2 heq
    let g := Nat.gcd u w
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hu
    have hgu : g ∣ u := Nat.gcd_dvd_left _ _
    have hgw : g ∣ w := Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime (u / g) (w / g) := Nat.coprime_div_gcd_div_gcd hg
    have hu_eq : u = g * (u / g) := (Nat.mul_div_cancel' hgu).symm
    have hw_eq : w = g * (w / g) := (Nat.mul_div_cancel' hgw).symm
    have hdiv_eq : (u / g) * P₂ = (w / g) * P₁ := by
      have hh := heq
      rw [hu_eq, hw_eq] at hh
      exact Nat.eq_of_mul_eq_mul_left hg (by linarith)
    have hdvd1 : u / g ∣ P₁ := hcop.dvd_of_dvd_mul_left ⟨P₂, hdiv_eq.symm⟩
    have hdvd2 : w / g ∣ P₂ := hcop.symm.dvd_of_dvd_mul_left ⟨P₁, hdiv_eq⟩
    have hule : u ≤ D * g := by
      calc
        u = (u / g) * g := (Nat.div_mul_cancel hgu).symm
        _ ≤ P₁ * g := Nat.mul_le_mul_right g (Nat.le_of_dvd hP1_pos hdvd1)
        _ ≤ D * g := Nat.mul_le_mul_right g hP1
    have hwle : w ≤ D * g := by
      calc
        w = (w / g) * g := (Nat.div_mul_cancel hgw).symm
        _ ≤ P₂ * g := Nat.mul_le_mul_right g (Nat.le_of_dvd hP2_pos hdvd2)
        _ ≤ D * g := Nat.mul_le_mul_right g hP2
    exact max_le hule hwle
  -- Small U case: U.card < N₁
  by_cases hm_small : U.card < N₁
  · obtain ⟨x, hxU, y, hyU, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
    let e : Fin 1 × Bool ↪ Fin n :=
      ⟨fun p => if p.2 then y else x, by
        intro ⟨i₁, b₁⟩ ⟨i₂, b₂⟩ h
        have hi : i₁ = i₂ := Fin.ext (by omega)
        subst hi
        cases b₁ <;> cases b₂ <;> simp at h ⊢
        · exact absurd h hxy
        · exact absurd h.symm hxy⟩
    refine ⟨1, e, ?_, ?_⟩
    · have h1 : η ≤ 1 / (N₁ : ℝ) := min_le_right _ _
      have hU_lt : (U.card : ℝ) < (N₁ : ℝ) := by exact_mod_cast hm_small
      have hNpos : (0 : ℝ) < N₁ := by exact_mod_cast (show 0 < N₁ by omega)
      calc
        η * (U.card : ℝ) ≤ (1 / (N₁ : ℝ)) * (U.card : ℝ) := by gcongr
        _ ≤ (1 / (N₁ : ℝ)) * (N₁ : ℝ) := by gcongr
        _ = 1 := one_div_mul_cancel hNpos.ne'
        _ = ((1 : ℕ) : ℝ) := by norm_num
    · intro p
      refine ⟨hxU, hyU, ?_⟩
      have hx' := hab_spec x hxU
      have hy' := hab_spec y hyU
      have hAB : (A : ℝ) * B ≤ D_small := by
        have h1 : (A : ℝ) * B ≤ C * U.card := harea
        have h2 : C * (U.card : ℝ) ≤ C * N₁ := by gcongr
        exact (h1.trans h2).trans ((Nat.le_ceil _).trans (by dsimp [D_small]; push_cast; linarith))
      have h1nat : (ab x).1 * (ab y).2 ≤ D := by
        have hle : ((ab x).1 * (ab y).2 : ℝ) ≤ A * B := by
          exact_mod_cast Nat.mul_le_mul hx'.2.1 hy'.2.2.2.1
        exact (by exact_mod_cast hle.trans hAB : (ab x).1 * (ab y).2 ≤ D_small).trans (le_max_right _ _)
      have h2nat : (ab y).1 * (ab x).2 ≤ D := by
        have hle : ((ab y).1 * (ab x).2 : ℝ) ≤ A * B := by
          exact_mod_cast Nat.mul_le_mul hy'.2.1 hx'.2.2.2.1
        exact (by exact_mod_cast hle.trans hAB : (ab y).1 * (ab x).2 ≤ D_small).trans (le_max_right _ _)
      have hnat := hcross x hxU y hyU
      have heq' : v x * ((ab y).1 * (ab x).2) = v y * ((ab x).1 * (ab y).2) := by
        calc
          v x * ((ab y).1 * (ab x).2) = v x * ((ab x).2 * (ab y).1) := by ring
          _ = v y * ((ab y).2 * (ab x).1) := hnat
          _ = v y * ((ab x).1 * (ab y).2) := by ring
      exact hheight_of_eq (v x) (v y) ((ab x).1 * (ab y).2) ((ab y).1 * (ab x).2)
        (hv x) (Nat.mul_pos hx'.1 hy'.2.2.1) (Nat.mul_pos hy'.1 hx'.2.2.1) h1nat h2nat heq'
  -- Large U case: N₁ ≤ U.card
  have hU_large : N₁ ≤ U.card := Nat.le_of_not_lt hm_small
  let m : ℕ := U.card
  have hm_pos : 0 < m := by omega
  have hsmooth_tail : ∀ X : ℕ, 0 < X →
      (((Finset.Icc 1 X).filter (fun x => S < smoothPart P x)).card : ℝ) ≤ (X : ℝ) / (8 * C) := by
    intro X hX
    let T_gt := ((Finset.Icc 1 X).image (smoothPart P)).filter (fun s => S < s)
    have hT_sub : (Finset.Icc 1 X).filter (fun x => S < smoothPart P x) ⊆
        T_gt.biUnion (fun s => (Finset.Icc 1 (X / s)).image (fun k => s * k)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxIcc := Finset.mem_Icc.mp hx.1
      rw [Finset.mem_biUnion]
      refine ⟨smoothPart P x, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hx.1, hx.2⟩, ?_⟩
      rw [Finset.mem_image]
      refine ⟨roughPart P x, Finset.mem_Icc.mpr ⟨?_, ?_⟩, smoothPart_mul_roughPart P hP x⟩
      · by_cases h0 : roughPart P x = 0
        · have hmul := smoothPart_mul_roughPart P hP x
          rw [h0, mul_zero] at hmul
          omega
        · omega
      · exact Nat.div_le_div_right hxIcc.2
    have hcard_bi : (((Finset.Icc 1 X).filter (fun x => S < smoothPart P x)).card : ℝ) ≤
        ∑ s ∈ T_gt, ((X : ℝ) / (s : ℝ)) := by
      have h1 := Finset.card_le_card hT_sub
      have h2 := h1.trans Finset.card_biUnion_le
      have h3 : (∑ s ∈ T_gt, ((Finset.Icc 1 (X / s)).image (fun k => s * k)).card : ℕ) ≤
          ∑ s ∈ T_gt, (X / s) := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact Finset.card_image_le.trans (by simp [Nat.card_Icc])
      have h4 : ((∑ s ∈ T_gt, (X / s) : ℕ) : ℝ) ≤ ∑ s ∈ T_gt, (X : ℝ) / (s : ℝ) := by
        push_cast
        refine Finset.sum_le_sum fun s hs => ?_
        have hs' := (Finset.mem_filter.mp hs).2
        have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
        rw [le_div_iff₀ hspos]
        exact_mod_cast Nat.div_mul_le_self X s
      exact (by exact_mod_cast h2.trans h3 : ((_ : ℕ) : ℝ) ≤ _).trans h4
    have hsum_inv : (∑ s ∈ T_gt, (1 : ℝ) / (s : ℝ)) ≤ 1 / (8 * C) := by
      have hT_sqrt : (∑ s ∈ T_gt, (1 : ℝ) / (s : ℝ)) ≤
          (1 / Real.sqrt (S : ℝ)) * ∑ s ∈ T_gt, (1 : ℝ) / Real.sqrt (s : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun s hs => ?_
        have hs' := (Finset.mem_filter.mp hs).2
        have hSpos : (0 : ℝ) < Real.sqrt S := Real.sqrt_pos.mpr (by exact_mod_cast hS_pos)
        have hspos : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
        have hle_sqrt : Real.sqrt (S : ℝ) ≤ Real.sqrt (s : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hs'.le)
        calc
          (1 : ℝ) / (s : ℝ) = (1 / Real.sqrt s) * (1 / Real.sqrt s) := by
            rw [one_div_mul_one_div, Real.mul_self_sqrt (by exact_mod_cast (by omega : 0 ≤ s))]
          _ ≤ (1 / Real.sqrt S) * (1 / Real.sqrt s) := by gcongr
      have hprod_sqrt : (∑ s ∈ T_gt, (1 : ℝ) / Real.sqrt (s : ℝ)) ≤ A_P := by
        have hsum2 := sum_smooth_le_prod P hP (fun p => 1 / Real.sqrt (p : ℝ))
          (fun p _ => by positivity) (fun p hp => hPsqrt1 p hp) X T_gt
          (fun s hs => by
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
            have hxIcc := Finset.mem_Icc.mp hx
            exact ⟨smoothPart_pos P hP x, (Nat.le_of_dvd (by omega) (smoothPart_dvd P hP x)).trans hxIcc.2⟩)
          (fun s hs => by
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
            exact smoothPart_primeFactors_subset P hP x)
        have hrew : ∀ s ∈ T_gt,
            (∏ p ∈ P, (1 / Real.sqrt (p : ℝ)) ^ (s.factorization p)) = (1 : ℝ) / Real.sqrt (s : ℝ) := by
          intro s hs
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
          have h1 : ∀ p ∈ P, (smoothPart P x).factorization p = x.factorization p :=
            fun p hp => factorization_smoothPart P hP x hp
          have h2 : (∏ p ∈ P, (1 / Real.sqrt (p : ℝ)) ^ ((smoothPart P x).factorization p)) =
              ∏ p ∈ P, (1 : ℝ) / Real.sqrt ((p ^ (x.factorization p) : ℕ) : ℝ) := by
            refine Finset.prod_congr rfl fun p hp => ?_
            rw [h1 p hp, one_div, inv_pow, one_div]
            congr 1
            push_cast
            rw [sqrt_pow_nat (p : ℝ) (by positivity) (x.factorization p)]
          rw [h2]
          have hsqrt_prod : ∀ Q : Finset ℕ, (g : ℕ → ℕ) →
              (∏ p ∈ Q, (1 : ℝ) / Real.sqrt ((g p : ℕ) : ℝ)) =
                (1 : ℝ) / Real.sqrt ((∏ p ∈ Q, g p : ℕ) : ℝ) := by
            intro Q g
            induction Q using Finset.induction with
            | empty => simp
            | @insert p Q' hp ih =>
              rw [Finset.prod_insert hp, Finset.prod_insert hp, ih]
              push_cast
              rw [Real.sqrt_mul (by positivity)]
              ring
          rw [hsqrt_prod P (fun p => p ^ (x.factorization p))]
          rfl
        rw [Finset.sum_congr rfl hrew] at hsum2
        exact hsum2
      have hS_bound : (1 : ℝ) / Real.sqrt (S : ℝ) * A_P ≤ 1 / (8 * C) := by
        have hS1 : (8 * C * A_P) ^ 2 ≤ (S : ℝ) := by
          have := Nat.le_ceil ((8 * C * A_P) ^ 2)
          dsimp [S]; push_cast; linarith
        have hS2 : 8 * C * A_P ≤ Real.sqrt (S : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 8 * C * A_P)]
          exact Real.sqrt_le_sqrt hS1
        have hSpos : 0 < Real.sqrt (S : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hS_pos)
        rw [one_div_mul_eq_div, div_le_div_iff₀ hSpos (by positivity)]
        linarith
      calc
        (∑ s ∈ T_gt, (1 : ℝ) / (s : ℝ)) ≤ (1 / Real.sqrt S) * ∑ s ∈ T_gt, (1 / Real.sqrt s) := hT_sqrt
        _ ≤ (1 / Real.sqrt S) * A_P := by
          exact mul_le_mul_of_nonneg_left hprod_sqrt (by positivity)
        _ ≤ 1 / (8 * C) := hS_bound
    have hmulX : (∑ s ∈ T_gt, (X : ℝ) / (s : ℝ)) = (X : ℝ) * ∑ s ∈ T_gt, (1 : ℝ) / (s : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    exact hcard_bi.trans (by
      rw [hmulX]
      exact (mul_le_mul_of_nonneg_left hsum_inv (by positivity)).trans_eq (by ring))
  let U_badA := U.filter (fun i => S < smoothPart P (ab i).1)
  let U_badB := U.filter (fun i => S < smoothPart P (ab i).2)
  have hbadA : (U_badA.card : ℝ) ≤ (m : ℝ) / 8 := by
    let T_a := (Finset.Icc 1 A).filter (fun a => S < smoothPart P a)
    have hsub : U_badA.image ab ⊆ T_a ×ˢ Finset.Icc 1 B := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hiU := (Finset.mem_filter.mp hi).1
      have hiS := (Finset.mem_filter.mp hi).2
      have hsp := hab_spec i hiU
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsp.1, hsp.2.1⟩, hiS⟩,
        Finset.mem_Icc.mpr ⟨hsp.2.2.1, hsp.2.2.2.1⟩⟩
    have hcard : U_badA.card ≤ T_a.card * B := by
      have hinj : Set.InjOn ab U_badA := hab_inj.mono (Finset.filter_subset _ _)
      rw [← Finset.card_image_of_injOn hinj]
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product, Nat.card_Icc]; simp)
    have hTa : (T_a.card : ℝ) ≤ (A : ℝ) / (8 * C) := hsmooth_tail A hA
    calc
      (U_badA.card : ℝ) ≤ (T_a.card : ℝ) * B := by exact_mod_cast hcard
      _ ≤ ((A : ℝ) / (8 * C)) * B := by gcongr
      _ = ((A : ℝ) * B) / (8 * C) := by ring
      _ ≤ (C * m) / (8 * C) := by gcongr
      _ = (m : ℝ) / 8 := by field_simp [(by linarith : C ≠ 0)]
  have hbadB : (U_badB.card : ℝ) ≤ (m : ℝ) / 8 := by
    let T_b := (Finset.Icc 1 B).filter (fun b => S < smoothPart P b)
    have hsub : U_badB.image ab ⊆ Finset.Icc 1 A ×ˢ T_b := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      have hiU := (Finset.mem_filter.mp hi).1
      have hiS := (Finset.mem_filter.mp hi).2
      have hsp := hab_spec i hiU
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hsp.1, hsp.2.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsp.2.2.1, hsp.2.2.2.1⟩, hiS⟩⟩
    have hcard : U_badB.card ≤ A * T_b.card := by
      have hinj : Set.InjOn ab U_badB := hab_inj.mono (Finset.filter_subset _ _)
      rw [← Finset.card_image_of_injOn hinj]
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product, Nat.card_Icc]; simp)
    have hTb : (T_b.card : ℝ) ≤ (B : ℝ) / (8 * C) := hsmooth_tail B hB
    calc
      (U_badB.card : ℝ) ≤ A * (T_b.card : ℝ) := by exact_mod_cast hcard
      _ ≤ A * ((B : ℝ) / (8 * C)) := by gcongr
      _ = ((A : ℝ) * B) / (8 * C) := by ring
      _ ≤ (C * m) / (8 * C) := by gcongr
      _ = (m : ℝ) / 8 := by field_simp [(by linarith : C ≠ 0)]
  let W := U.filter (fun i => smoothPart P (ab i).1 ≤ S ∧ smoothPart P (ab i).2 ≤ S)
  have hW_card : (3 : ℝ) * m / 4 ≤ W.card := by
    have hcov : U ⊆ W ∪ (U_badA ∪ U_badB) := by
      intro i hi
      by_cases ha : S < smoothPart P (ab i).1
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, ha⟩))
      · by_cases hb : S < smoothPart P (ab i).2
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hb⟩))
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, by omega, by omega⟩)
    have hle := Finset.card_le_card hcov
    have hle' := hle.trans (Finset.card_union_le _ _)
    have hle'' := hle'.trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    have hleR : (U.card : ℝ) ≤ W.card + U_badA.card + U_badB.card := by
      exact_mod_cast hle''.trans_eq (add_assoc _ _ _).symm
    change (m : ℝ) ≤ W.card + U_badA.card + U_badB.card at hleR
    linarith only [hleR, hbadA, hbadB]
  let R_A := (Finset.Icc 1 A).filter (fun r => Nat.Coprime r M)
  let R_B := (Finset.Icc 1 B).filter (fun r => Nat.Coprime r M)
  let R := R_A ×ˢ R_B
  have hR_card : (R.card : ℝ) ≤ (m : ℝ) / 4 := by
    have hRA_le_A : R_A.card ≤ A := (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])
    have hRB_le_B : R_B.card ≤ B := (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])
    have hRA_rough : (R_A.card : ℝ) ≤ (A : ℝ) / (8 * C) + M := by
      calc
        (R_A.card : ℝ) ≤ (A : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) + M := rough_count_le P hP A
        _ ≤ (A : ℝ) * (1 / (8 * C)) + M := by gcongr
        _ = (A : ℝ) / (8 * C) + M := by ring
    have hRB_rough : (R_B.card : ℝ) ≤ (B : ℝ) / (8 * C) + M := by
      calc
        (R_B.card : ℝ) ≤ (B : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) + M := rough_count_le P hP B
        _ ≤ (B : ℝ) * (1 / (8 * C)) + M := by gcongr
        _ = (B : ℝ) / (8 * C) + M := by ring
    have hmin_bound : (M : ℝ) * min (A : ℝ) B ≤ (m : ℝ) / 8 := by
      have hmin_sq : (min (A : ℝ) B) ^ 2 ≤ (A : ℝ) * B := by
        rcases le_total (A : ℝ) B with hAB | hBA
        · rw [min_eq_left hAB, sq]; exact mul_le_mul_of_nonneg_left hAB (by positivity)
        · rw [min_eq_right hBA, sq]; exact mul_le_mul_of_nonneg_right hBA (by positivity)
      have hN1_bound : 64 * (M : ℝ) ^ 2 * C ≤ (m : ℝ) := by
        have h1 : 64 * (M : ℝ) ^ 2 * C ≤ (N₁ : ℝ) :=
          (Nat.le_ceil _).trans (by dsimp [N₁]; push_cast; linarith)
        exact h1.trans (by exact_mod_cast hU_large)
      have hsq : ((M : ℝ) * min (A : ℝ) B) ^ 2 ≤ ((m : ℝ) / 8) ^ 2 := by
        calc
          ((M : ℝ) * min (A : ℝ) B) ^ 2 = (M : ℝ) ^ 2 * (min (A : ℝ) B) ^ 2 := by ring
          _ ≤ (M : ℝ) ^ 2 * ((A : ℝ) * B) := by gcongr
          _ ≤ (M : ℝ) ^ 2 * (C * m) := by gcongr
          _ = (64 * (M : ℝ) ^ 2 * C) * m / 64 := by ring
          _ ≤ (m : ℝ) * m / 64 := by gcongr
          _ = ((m : ℝ) / 8) ^ 2 := by ring
      nlinarith [show (0 : ℝ) ≤ M * min (A : ℝ) B by positivity, show (0 : ℝ) ≤ (m : ℝ) / 8 by positivity]
    have hR_prod : (R.card : ℝ) = (R_A.card : ℝ) * (R_B.card : ℝ) := by
      rw [Finset.card_product]; push_cast; rfl
    rw [hR_prod]
    rcases le_total (A : ℝ) B with hAB | hBA
    · calc
        (R_A.card : ℝ) * (R_B.card : ℝ) ≤ (A : ℝ) * ((B : ℝ) / (8 * C) + M) := by
          exact mul_le_mul (by exact_mod_cast hRA_le_A) hRB_rough (by positivity) (by positivity)
        _ = ((A : ℝ) * B) / (8 * C) + M * A := by ring
        _ ≤ (C * m) / (8 * C) + M * min (A : ℝ) B := by
          rw [min_eq_left hAB]; gcongr
        _ ≤ (m : ℝ) / 8 + (m : ℝ) / 8 := by
          have : (C * (m : ℝ)) / (8 * C) = (m : ℝ) / 8 := by field_simp [(by linarith : C ≠ 0)]
          linarith
        _ = (m : ℝ) / 4 := by ring
    · calc
        (R_A.card : ℝ) * (R_B.card : ℝ) ≤ ((A : ℝ) / (8 * C) + M) * (B : ℝ) := by
          exact mul_le_mul hRA_rough (by exact_mod_cast hRB_le_B) (by positivity) (by positivity)
        _ = ((A : ℝ) * B) / (8 * C) + M * B := by ring
        _ ≤ (C * m) / (8 * C) + M * min (A : ℝ) B := by
          rw [min_eq_right hBA]; gcongr
        _ ≤ (m : ℝ) / 8 + (m : ℝ) / 8 := by
          have : (C * (m : ℝ)) / (8 * C) = (m : ℝ) / 8 := by field_simp [(by linarith : C ≠ 0)]
          linarith
        _ = (m : ℝ) / 4 := by ring
  let roughPair : Fin n → ℕ × ℕ := fun i => (roughPart P (ab i).1, roughPart P (ab i).2)
  have hrough_mem : ∀ i ∈ W, roughPair i ∈ R := by
    intro i hi
    have hiU := (Finset.mem_filter.mp hi).1
    have hsp := hab_spec i hiU
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · by_cases h0 : roughPart P (ab i).1 = 0
      · have hmul := smoothPart_mul_roughPart P hP (ab i).1
        rw [h0, mul_zero] at hmul; exfalso; exact hsp.1.ne' hmul.symm
      · exact Nat.pos_of_ne_zero h0
    · exact (Nat.div_le_self _ _).trans hsp.2.1
    · exact roughPart_coprime P hP hsp.1
    · by_cases h0 : roughPart P (ab i).2 = 0
      · have hmul := smoothPart_mul_roughPart P hP (ab i).2
        rw [h0, mul_zero] at hmul; exfalso; exact hsp.2.2.1.ne' hmul.symm
      · exact Nat.pos_of_ne_zero h0
    · exact (Nat.div_le_self _ _).trans hsp.2.2.2.1
    · exact roughPart_coprime P hP hsp.2.2.1
  obtain ⟨L, hLmem, hLnodup, hLcard⟩ := fiber_pairing W roughPair R hrough_mem
  obtain ⟨e, he_eq⟩ := list_pairs_to_emb L hLnodup
  have hLcardR : (W.card : ℝ) ≤ 2 * (L.length : ℝ) + R.card := by exact_mod_cast hLcard
  have hη_le : η ≤ 1 / 4 := min_le_left _ _
  have h4 : (m : ℝ) / 4 ≤ L.length := by linarith only [hW_card, hR_card, hLcardR]
  have hm_nn : (0 : ℝ) ≤ m := by positivity
  have hlen : η * (U.card : ℝ) ≤ L.length := by
    calc
      η * (U.card : ℝ) = η * (m : ℝ) := rfl
      _ ≤ (1 / 4 : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_right hη_le hm_nn
      _ = (m : ℝ) / 4 := by ring
      _ ≤ L.length := h4
  have hpair_all : ∀ p : Fin L.length, e (p, false) ∈ U ∧ e (p, true) ∈ U ∧
      max (v (e (p, false))) (v (e (p, true))) ≤
        D * Nat.gcd (v (e (p, false))) (v (e (p, true))) := by
    intro p
    have hp_mem : L[p.1]'p.2 ∈ L := List.getElem_mem p.2
    obtain ⟨hxW, hyW, _, hfxy⟩ := hLmem (L[p.1]'p.2) hp_mem
    have hWsub : W ⊆ U := Finset.filter_subset _ _
    have hxU : (L[p.1]'p.2).1 ∈ U := hWsub hxW
    have hyU : (L[p.1]'p.2).2 ∈ U := hWsub hyW
    have hxS := (Finset.mem_filter.mp hxW).2
    have hyS := (Finset.mem_filter.mp hyW).2
    have hx' := hab_spec (L[p.1]'p.2).1 hxU
    have hy' := hab_spec (L[p.1]'p.2).2 hyU
    have hres := rational_box_pair_height (D := D) hP (hv (L[p.1]'p.2).1) (hv (L[p.1]'p.2).2)
      hx'.1 hx'.2.2.1 hy'.1 hy'.2.2.1 (le_max_left (S ^ 2) D_small)
      hxS.1 hxS.2 hyS.1 hyS.2 (congrArg Prod.fst hfxy) (congrArg Prod.snd hfxy)
      (hcross (L[p.1]'p.2).1 hxU (L[p.1]'p.2).2 hyU)
    rw [(he_eq p).1, (he_eq p).2]
    exact ⟨hxU, hyU, hres⟩
  exact ⟨L.length, e, hlen, hpair_all⟩

end Part12

section Part34
open Function Filter


private def C_conc : ℝ := 36 * (205 : ℝ) ^ 3

private lemma one_sub_rpow_one_fifth_le {γ : ℝ} (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (1 - γ) ^ ((1 : ℝ) / 5) ≤ 1 - γ / 5 := by
  have h0 : 0 ≤ 1 - γ := sub_nonneg.mpr hγ1
  have h1 : 0 ≤ 1 - γ / 5 := by linarith
  have hpow : ((1 - γ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) ≤ (1 - γ / 5) ^ (5 : ℕ) := by
    have heq : ((1 - γ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) = 1 - γ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
      norm_num
    rw [heq]
    have hbern := one_add_mul_le_pow (a := -γ / 5) (by linarith) 5
    have hbern' : 1 + (5 : ℕ) * (-γ / 5) = 1 - γ := by push_cast; ring
    have hbern'' : 1 + (-γ / 5) = 1 - γ / 5 := by ring
    linarith [hbern]
  exact le_of_pow_le_pow_left₀ (by norm_num) h1 hpow

private lemma sum_shift_sqrt_le (S₁ S₂ : Finset ℕ) (α β : ℕ → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (d : ℤ) :
    (∑ i ∈ S₁, ∑ j ∈ S₂, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) ≤
      Real.sqrt ((∑ i ∈ S₁, α i) * (∑ j ∈ S₂, β j)) := by
  classical
  let g : ℕ → ℝ := fun i =>
    if 0 ≤ (i : ℤ) - d ∧ ((i : ℤ) - d).toNat ∈ S₂ then Real.sqrt (β ((i : ℤ) - d).toNat) else 0
  have hrew : (∑ i ∈ S₁, ∑ j ∈ S₂, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) =
      ∑ i ∈ S₁, Real.sqrt (α i) * g i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 ≤ (i : ℤ) - d ∧ ((i : ℤ) - d).toNat ∈ S₂
    · have hid : 0 ≤ (i : ℤ) - d := h.1
      have huniq : ∀ j : ℕ, (d = (i : ℤ) - j ↔ ((i : ℤ) - d).toNat = j) := by
        intro j
        constructor
        · intro hij; omega
        · intro hj; omega
      have hsum_j : (∑ j ∈ S₂, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) =
          Real.sqrt (α i) * Real.sqrt (β ((i : ℤ) - d).toNat) := by
        have hcong : (∑ j ∈ S₂, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) =
            ∑ j ∈ S₂, if ((i : ℤ) - d).toNat = j then Real.sqrt (α i) * Real.sqrt (β j) else 0 :=
          Finset.sum_congr rfl fun j _ => if_congr (huniq j) rfl rfl
        rw [hcong, Finset.sum_ite_eq S₂ ((i : ℤ) - d).toNat, if_pos h.2]
      rw [hsum_j]
      simp only [g, if_pos h]
    · have hzero : ∀ j ∈ S₂, d ≠ (i : ℤ) - j := by
        intro j hj hij
        apply h
        refine ⟨by omega, ?_⟩
        have : ((i : ℤ) - d).toNat = j := by omega
        rwa [this]
      rw [Finset.sum_eq_zero fun j hj => if_neg (hzero j hj)]
      simp only [g, if_neg h, mul_zero]
  rw [hrew]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S₁ (fun i => Real.sqrt (α i)) g
  have hsq1 : (∑ i ∈ S₁, (Real.sqrt (α i)) ^ 2) = ∑ i ∈ S₁, α i :=
    Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hα0 i)
  have hsq2 : (∑ i ∈ S₁, (g i) ^ 2) ≤ ∑ j ∈ S₂, β j := by
    let S₁' : Finset ℕ := S₁.filter (fun i : ℕ => 0 ≤ (i : ℤ) - d ∧ ((i : ℤ) - d).toNat ∈ S₂)
    have hsum_g : (∑ i ∈ S₁, (g i) ^ 2) = ∑ i ∈ S₁', β ((i : ℤ) - d).toNat := by
      rw [← Finset.sum_filter_add_sum_filter_not S₁ (fun i : ℕ => 0 ≤ (i : ℤ) - d ∧ ((i : ℤ) - d).toNat ∈ S₂)]
      have h0 : (∑ i ∈ S₁.filter (fun i : ℕ => ¬ (0 ≤ (i : ℤ) - d ∧ ((i : ℤ) - d).toNat ∈ S₂)), (g i) ^ 2) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          have hnot := (Finset.mem_filter.mp hi).2
          simp only [g, if_neg hnot, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [g, if_pos hi']
      exact Real.sq_sqrt (hβ0 _)
    rw [hsum_g]
    have hinj : Set.InjOn (fun i : ℕ => ((i : ℤ) - d).toNat) S₁' := by
      intro i₁ hi₁ i₂ hi₂ heq
      have h1 := (Finset.mem_filter.mp hi₁).2.1
      have h2 := (Finset.mem_filter.mp hi₂).2.1
      have h1z : (((i₁ : ℤ) - d).toNat : ℤ) = (i₁ : ℤ) - d := Int.toNat_of_nonneg h1
      have h2z : (((i₂ : ℤ) - d).toNat : ℤ) = (i₂ : ℤ) - d := Int.toNat_of_nonneg h2
      have heq' : (((i₁ : ℤ) - d).toNat : ℤ) = (((i₂ : ℤ) - d).toNat : ℤ) := by
        dsimp at heq; exact_mod_cast heq
      omega
    have himg : S₁'.image (fun i : ℕ => ((i : ℤ) - d).toNat) ⊆ S₂ := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hi).2.2
    calc
      (∑ i ∈ S₁', β ((i : ℤ) - d).toNat)
          = ∑ j ∈ S₁'.image (fun i : ℕ => ((i : ℤ) - d).toNat), β j := by
            rw [Finset.sum_image]
            exact fun i₁ hi₁ i₂ hi₂ h => hinj hi₁ hi₂ h
      _ ≤ ∑ j ∈ S₂, β j :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => hβ0 j
  rw [hsq1] at hcs
  have hcs2 : (∑ i ∈ S₁, Real.sqrt (α i) * g i) ^ 2 ≤ (∑ i ∈ S₁, α i) * (∑ j ∈ S₂, β j) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq2 (Finset.sum_nonneg fun i _ => hα0 i))
  exact Real.le_sqrt_of_sq_le hcs2

private lemma sum_geom_Icc1_le {lam : ℝ} (h0 : 0 ≤ lam) (hlt1 : lam < 1) (M : ℕ) :
    (∑ m ∈ Finset.Icc (1 : ℕ) M, lam ^ m) ≤ lam / (1 - lam) := by
  have hrew : (∑ m ∈ Finset.Icc (1 : ℕ) M, lam ^ m) = lam * ∑ k ∈ Finset.range M, lam ^ k := by
    rw [Finset.mul_sum]
    have himg : Finset.Icc (1 : ℕ) M = (Finset.range M).image (· + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      exact ⟨fun ⟨h1, h2⟩ => ⟨x - 1, by omega, by omega⟩, fun ⟨k, hk, h⟩ => by omega⟩
    rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']
  rw [hrew, geom_sum_eq hlt1.ne M]
  have hsub : 0 < 1 - lam := by linarith
  have h1 : (lam ^ M - 1) / (lam - 1) = (1 - lam ^ M) / (1 - lam) := by
    field_simp [show lam - 1 ≠ 0 by linarith, hsub.ne']; ring
  rw [h1]
  have hle1 : 1 - lam ^ M ≤ 1 := by linarith [pow_nonneg h0 M]
  calc
    lam * ((1 - lam ^ M) / (1 - lam)) ≤ lam * (1 / (1 - lam)) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle1 hsub.le) h0
    _ = lam / (1 - lam) := by ring

private lemma sum_geom_Icc_erase0_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 4 / 5) (M : ℕ) :
    (∑ d ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0, lam ^ Int.natAbs d) ≤ 10 * lam := by
  have hsub1 : (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0 =
      (Finset.Icc (1 : ℤ) (M : ℤ)) ∪ ((Finset.Icc (1 : ℤ) (M : ℤ)).image (fun x : ℤ => -x)) := by
    ext d; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro ⟨hd0, hlo, hhi⟩
      rcases lt_or_gt_of_ne hd0 with hlt | hgt
      · exact Or.inr ⟨-d, ⟨by omega, by omega⟩, by omega⟩
      · exact Or.inl ⟨by omega, hhi⟩
    · rintro (⟨h1', h2'⟩ | ⟨a, ⟨h1', h2'⟩, rfl⟩)
      · exact ⟨by omega, by omega, h2'⟩
      · exact ⟨by omega, by omega, by omega⟩
  have hdisj : Disjoint (Finset.Icc (1 : ℤ) (M : ℤ))
      ((Finset.Icc (1 : ℤ) (M : ℤ)).image (fun x : ℤ => -x)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_Icc, Finset.mem_image] at hx1 hx2; omega
  have heq1 : (∑ d ∈ Finset.Icc (1 : ℤ) (M : ℤ), lam ^ Int.natAbs d) =
      ∑ m ∈ Finset.Icc (1 : ℕ) M, lam ^ m := by
    have himg : Finset.Icc (1 : ℤ) (M : ℤ) = (Finset.Icc (1 : ℕ) M).image (fun m : ℕ => (m : ℤ)) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro ⟨hd1, hdM⟩
        have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
        refine ⟨d.toNat, ⟨by omega, by omega⟩, hdn⟩
      · rintro ⟨m, ⟨hm1, hmM⟩, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
    exact Finset.sum_congr rfl fun m _ => by simp
  have heq2 : (∑ d ∈ (Finset.Icc (1 : ℤ) (M : ℤ)).image (fun x : ℤ => -x), lam ^ Int.natAbs d) =
      ∑ m ∈ Finset.Icc (1 : ℕ) M, lam ^ m := by
    rw [Finset.sum_image (fun _ _ _ _ h => by omega)]
    have heq_neg : (∑ x ∈ Finset.Icc (1 : ℤ) (M : ℤ), lam ^ Int.natAbs (-x)) =
        ∑ x ∈ Finset.Icc (1 : ℤ) (M : ℤ), lam ^ Int.natAbs x :=
      Finset.sum_congr rfl fun x _ => by simp
    rw [heq_neg]
    exact heq1
  rw [hsub1, Finset.sum_union hdisj, heq1, heq2]
  have hpos := sum_geom_Icc1_le h0 (by linarith : lam < 1) M
  have hsub : 0 < 1 - lam := by linarith
  have h5 : lam / (1 - lam) ≤ 5 * lam := by
    rw [div_le_iff₀ hsub]; nlinarith
  linarith

private lemma sum_geom_Icc_int {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 4 / 5) (M : ℕ) :
    (∑ d ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), lam ^ Int.natAbs d) ≤ 9 := by
  have h0in : (0 : ℤ) ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.add_sum_erase (Finset.Icc (-(M : ℤ)) (M : ℤ)) _ h0in, Int.natAbs_zero, pow_zero]
  have hle := sum_geom_Icc_erase0_le h0 h1 M
  linarith

private lemma conc_c_ge (S : Finset ℕ) (hSne : S.Nonempty)
    (α β : ℕ → ℝ) (μ : ℕ → ℕ → ℝ) (c lam : ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j)
    (hα1 : ∑ i ∈ S, α i = 1) (hβ1 : ∑ j ∈ S, β j = 1)
    (hμ1 : ∑ i ∈ S, ∑ j ∈ S, μ i j = 1)
    (hc : 0 < c) (hlam : 0 < lam ∧ lam ≤ 4 / 5)
    (hbound : ∀ i ∈ S, ∀ j ∈ S,
      μ i j ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5)) :
    1 / 9 ≤ c := by
  have hα_le1 : ∀ i ∈ S, α i ≤ 1 := fun i hi =>
    (Finset.single_le_sum (fun x _ => hα0 x) hi).trans_eq hα1
  have hβ_le1 : ∀ j ∈ S, β j ≤ 1 := fun j hj =>
    (Finset.single_le_sum (fun x _ => hβ0 x) hj).trans_eq hβ1
  let M : ℕ := S.sup' hSne id
  have hM : ∀ i ∈ S, i ≤ M := fun i hi => Finset.le_sup' id hi
  let J := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hstep1 : 1 ≤ c * ∑ i ∈ S, ∑ j ∈ S,
      lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) := by
    have hsum : (∑ i ∈ S, ∑ j ∈ S, μ i j) ≤
        ∑ i ∈ S, ∑ j ∈ S, c * (lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j))) := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
      have hb := hbound i hi j hj
      have hmul1 : α i * β j ≤ 1 := mul_le_one₀ (hα_le1 i hi) (hβ0 j) (hβ_le1 j hj)
      have hxy0 : 0 ≤ α i * β j := mul_nonneg (hα0 i) (hβ0 j)
      have hr1 : (α i * β j) ^ ((3 : ℝ) / 5) ≤ Real.sqrt (α i) * Real.sqrt (β j) := by
        rw [← Real.sqrt_mul (hα0 i), Real.sqrt_eq_rpow]
        by_cases hxz : α i * β j = 0
        · rw [hxz]; norm_num
        · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hxy0 (Ne.symm hxz)) hmul1 (by norm_num)
      calc
        μ i j ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) := hb
        _ ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) :=
          mul_le_mul_of_nonneg_left hr1 (mul_nonneg hc.le (pow_nonneg hlam.1.le _))
        _ = c * (lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j))) := by ring
    simp_rw [← Finset.mul_sum] at hsum
    linarith [hμ1, hsum]
  have hswap : (∑ i ∈ S, ∑ j ∈ S, lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j))) =
      ∑ d ∈ J, lam ^ Int.natAbs d *
        ∑ i ∈ S, ∑ j ∈ S, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0 := by
    have hpt : ∀ i ∈ S, ∀ j ∈ S,
        lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) =
          ∑ d ∈ J, if d = (i : ℤ) - j then
            lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 := by
      intro i hi j hj
      have hdJ : (i : ℤ) - j ∈ J := Finset.mem_Icc.mpr ⟨by have := hM j hj; omega, by have := hM i hi; omega⟩
      rw [Finset.sum_ite_eq' J ((i : ℤ) - j), if_pos hdJ]
    calc
      (∑ i ∈ S, ∑ j ∈ S, lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)))
          = ∑ i ∈ S, ∑ j ∈ S, ∑ d ∈ J, if d = (i : ℤ) - j then
              lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 :=
            Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hpt i hi j hj
      _ = ∑ i ∈ S, ∑ d ∈ J, ∑ j ∈ S, if d = (i : ℤ) - j then
            lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ d ∈ J, ∑ i ∈ S, ∑ j ∈ S, if d = (i : ℤ) - j then
            lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 := Finset.sum_comm
      _ = ∑ d ∈ J, lam ^ Int.natAbs d *
            ∑ i ∈ S, ∑ j ∈ S, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0 := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  have h2 : (∑ d ∈ J, lam ^ Int.natAbs d *
      ∑ i ∈ S, ∑ j ∈ S, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) ≤ 9 := by
    calc
      (∑ d ∈ J, lam ^ Int.natAbs d *
          ∑ i ∈ S, ∑ j ∈ S, if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0)
          ≤ ∑ d ∈ J, lam ^ Int.natAbs d * 1 := by
            refine Finset.sum_le_sum fun d _ => ?_
            have hcs := sum_shift_sqrt_le S S α β hα0 hβ0 d
            rw [hα1, hβ1, mul_one, Real.sqrt_one] at hcs
            exact mul_le_mul_of_nonneg_left hcs (pow_nonneg hlam.1.le _)
      _ = ∑ d ∈ J, lam ^ Int.natAbs d := by simp
      _ ≤ 9 := sum_geom_Icc_int hlam.1.le hlam.2 M
  rw [hswap] at hstep1
  have h9c : 1 ≤ c * 9 := hstep1.trans (mul_le_mul_of_nonneg_left h2 hc.le)
  linarith

private lemma conc_sigma_ray (S : Finset ℕ) (hSne : S.Nonempty) (k : ℕ)
    (w : ℕ → ℝ) (lam γ : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hγ0 : 0 ≤ γ) (hwsum : (∑ x ∈ S.erase k, w x) ≤ 2 * γ)
    (hlam : 0 < lam ∧ lam ≤ 4 / 5) :
    (∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
      lam ^ Int.natAbs ((x : ℤ) - k) * (w x) ^ ((3 : ℝ) / 5) else 0) ≤
      4 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by
  let M : ℕ := S.sup' hSne id
  have hM : ∀ x ∈ S, x ≤ M := fun x hx => Finset.le_sup' id hx
  have h2γ0 : 0 ≤ 2 * γ := by linarith
  have hw_pt : ∀ x ∈ S.erase k, w x ≤ 2 * γ := fun x hx =>
    (Finset.single_le_sum (fun y _ => hw0 y) hx).trans hwsum
  have hstep1 : (∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
      lam ^ Int.natAbs ((x : ℤ) - k) * (w x) ^ ((3 : ℝ) / 5) else 0) ≤
      (25 / 16) * lam ^ 2 * (2 * γ) ^ ((1 : ℝ) / 10) *
        ∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
          (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    split_ifs with h2
    · have hlam_le : lam ^ Int.natAbs ((x : ℤ) - k) ≤
          (25 / 16 : ℝ) * lam ^ 2 * (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) := by
        let m := Int.natAbs ((x : ℤ) - k)
        change lam ^ m ≤ (25 / 16 : ℝ) * lam ^ 2 * (4 / 5 : ℝ) ^ m
        have hm2 : 2 ≤ m := h2
        have h54 : (5 / 4 : ℝ) * lam ≤ 1 := by linarith [hlam.2]
        have h1 : ((5 / 4 : ℝ) * lam) ^ m ≤ ((5 / 4 : ℝ) * lam) ^ 2 :=
          pow_le_pow_of_le_one (mul_nonneg (by norm_num) hlam.1.le) h54 hm2
        have h2' : (5 / 4 : ℝ) ^ m * lam ^ m ≤ (25 / 16 : ℝ) * lam ^ 2 := by
          calc
            (5 / 4 : ℝ) ^ m * lam ^ m = ((5 / 4 : ℝ) * lam) ^ m := (mul_pow _ _ m).symm
            _ ≤ ((5 / 4 : ℝ) * lam) ^ 2 := h1
            _ = (25 / 16 : ℝ) * lam ^ 2 := by ring
        calc
          lam ^ m = ((4 / 5 : ℝ) ^ m) * ((5 / 4 : ℝ) ^ m * lam ^ m) := by
            rw [← mul_assoc, ← mul_pow]; norm_num
          _ ≤ ((4 / 5 : ℝ) ^ m) * ((25 / 16 : ℝ) * lam ^ 2) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
          _ = (25 / 16 : ℝ) * lam ^ 2 * (4 / 5 : ℝ) ^ m := by ring
      have hw_rpow : (w x) ^ ((3 : ℝ) / 5) ≤ (2 * γ) ^ ((1 : ℝ) / 10) * Real.sqrt (w x) := by
        have hwx0 := hw0 x
        have hwxle := hw_pt x hx
        have hprod : (w x) ^ ((3 : ℝ) / 5) = (w x) ^ ((1 : ℝ) / 10) * (w x) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add' hwx0 (by norm_num)]; norm_num
        rw [hprod, ← Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hwx0 hwxle (by norm_num)) (Real.sqrt_nonneg _)
      calc
        lam ^ Int.natAbs ((x : ℤ) - k) * (w x) ^ ((3 : ℝ) / 5)
            ≤ ((25 / 16 : ℝ) * lam ^ 2 * (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) *
                ((2 * γ) ^ ((1 : ℝ) / 10) * Real.sqrt (w x)) :=
              mul_le_mul hlam_le hw_rpow (Real.rpow_nonneg (hw0 x) _) (by positivity)
        _ = (25 / 16) * lam ^ 2 * (2 * γ) ^ ((1 : ℝ) / 10) *
              ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x)) := by ring
    · simp
  let S_far : Finset ℕ := (S.erase k).filter (fun x : ℕ => 2 ≤ Int.natAbs ((x : ℤ) - k))
  have hcs_far : (∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
      (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x) else 0) ≤
      (32 / 15 : ℝ) * Real.sqrt γ := by
    have hrew : (∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
        (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x) else 0) =
        ∑ x ∈ S_far, (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x) := by
      rw [← Finset.sum_filter]
    rw [hrew]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S_far
      (fun x => (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) (fun x => Real.sqrt (w x))
    have hsum_w : (∑ x ∈ S_far, (Real.sqrt (w x)) ^ 2) ≤ 2 * γ := by
      calc
        (∑ x ∈ S_far, (Real.sqrt (w x)) ^ 2) = ∑ x ∈ S_far, w x :=
          Finset.sum_congr rfl fun x _ => Real.sq_sqrt (hw0 x)
        _ ≤ ∑ x ∈ S.erase k, w x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hw0 x
        _ ≤ 2 * γ := hwsum
    have hsum_geom : (∑ x ∈ S_far, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) ≤ 512 / 225 := by
      let M_far := M + k + 2
      have hgeom2 : (∑ m ∈ Finset.Icc (2 : ℕ) M_far, ((4 / 5 : ℝ) ^ m) ^ 2) ≤ 256 / 225 := by
        have hrew2 : ∀ m : ℕ, ((4 / 5 : ℝ) ^ m) ^ 2 = (16 / 25 : ℝ) ^ m := fun m => by
          rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
        rw [Finset.sum_congr rfl fun m _ => hrew2 m]
        have himg : Finset.Icc (2 : ℕ) M_far = (Finset.range (M_far - 1)).image (· + 2) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
          exact ⟨fun ⟨h1, h2⟩ => ⟨m - 2, by omega, by omega⟩, fun ⟨t, ht, h⟩ => by omega⟩
        rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
        have hfac : (∑ t ∈ Finset.range (M_far - 1), (16 / 25 : ℝ) ^ (t + 2)) =
            (256 / 625 : ℝ) * ∑ t ∈ Finset.range (M_far - 1), (16 / 25 : ℝ) ^ t := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => by rw [pow_add]; norm_num; ring
        rw [hfac, geom_sum_eq (by norm_num : (16 / 25 : ℝ) ≠ 1) (M_far - 1)]
        have h1 : ((16 / 25 : ℝ) ^ (M_far - 1) - 1) / ((16 / 25 : ℝ) - 1) =
            (1 - (16 / 25 : ℝ) ^ (M_far - 1)) / (9 / 25 : ℝ) := by ring
        rw [h1]
        have hpos : 0 ≤ (16 / 25 : ℝ) ^ (M_far - 1) := by positivity
        nlinarith
      let S_pos := S_far.filter (fun x : ℕ => k < x)
      let S_neg := S_far.filter (fun x : ℕ => x < k)
      have hsplit : S_far = S_pos ∪ S_neg := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, S_pos, S_neg]
        constructor
        · intro hx
          have hxk : x ≠ k := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
          rcases lt_or_gt_of_ne hxk with hlt | hgt
          · exact Or.inr ⟨hx, hlt⟩
          · exact Or.inl ⟨hx, hgt⟩
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      have hdisj : Disjoint S_pos S_neg := by
        rw [Finset.disjoint_left]; intro x h1 h2
        simp only [Finset.mem_filter, S_pos, S_neg] at h1 h2; omega
      have hp1 : (∑ x ∈ S_pos, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) ≤ 256 / 225 := by
        have hinj : Set.InjOn (fun x : ℕ => x - k) S_pos := by
          intro x₁ hx₁ x₂ hx₂ h
          have h1 := (Finset.mem_filter.mp hx₁).2
          have h2 := (Finset.mem_filter.mp hx₂).2
          dsimp at h; omega
        have hsub : S_pos.image (fun x : ℕ => x - k) ⊆ Finset.Icc (2 : ℕ) M_far := by
          intro m hm
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
          have hx1 := (Finset.mem_filter.mp hx).1
          have hx2 := (Finset.mem_filter.mp hx).2
          have hfar := (Finset.mem_filter.mp hx1).2
          have hxM := hM x (Finset.mem_of_mem_erase (Finset.mem_filter.mp hx1).1)
          rw [Finset.mem_Icc]
          omega
        have hrew' : (∑ x ∈ S_pos, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) =
            ∑ m ∈ S_pos.image (fun x : ℕ => x - k), ((4 / 5 : ℝ) ^ m) ^ 2 := by
          rw [Finset.sum_image (fun x₁ hx₁ x₂ hx₂ h => hinj hx₁ hx₂ h)]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx' := (Finset.mem_filter.mp hx).2
          rw [show Int.natAbs ((x : ℤ) - k) = x - k by omega]
        rw [hrew']
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hgeom2
      have hp2 : (∑ x ∈ S_neg, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) ≤ 256 / 225 := by
        have hinj : Set.InjOn (fun x : ℕ => k - x) S_neg := by
          intro x₁ hx₁ x₂ hx₂ h
          have h1 := (Finset.mem_filter.mp hx₁).2
          have h2 := (Finset.mem_filter.mp hx₂).2
          dsimp at h; omega
        have hsub : S_neg.image (fun x : ℕ => k - x) ⊆ Finset.Icc (2 : ℕ) M_far := by
          intro m hm
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
          have hx1 := (Finset.mem_filter.mp hx).1
          have hx2 := (Finset.mem_filter.mp hx).2
          have hfar := (Finset.mem_filter.mp hx1).2
          rw [Finset.mem_Icc]
          omega
        have hrew' : (∑ x ∈ S_neg, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) =
            ∑ m ∈ S_neg.image (fun x : ℕ => k - x), ((4 / 5 : ℝ) ^ m) ^ 2 := by
          rw [Finset.sum_image (fun x₁ hx₁ x₂ hx₂ h => hinj hx₁ hx₂ h)]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hx' := (Finset.mem_filter.mp hx).2
          rw [show Int.natAbs ((x : ℤ) - k) = k - x by omega]
        rw [hrew']
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hgeom2
      nth_rw 1 [hsplit]
      rw [Finset.sum_union hdisj]
      linarith
    have hsq_bd : (∑ x ∈ S_far, (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x)) ^ 2 ≤
        ((32 / 15 : ℝ) * Real.sqrt γ) ^ 2 := by
      calc
        (∑ x ∈ S_far, (4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k) * Real.sqrt (w x)) ^ 2
            ≤ (∑ x ∈ S_far, ((4 / 5 : ℝ) ^ Int.natAbs ((x : ℤ) - k)) ^ 2) *
                (∑ x ∈ S_far, (Real.sqrt (w x)) ^ 2) := hcs
        _ ≤ (512 / 225 : ℝ) * (2 * γ) := by
          exact mul_le_mul hsum_geom hsum_w (Finset.sum_nonneg fun x _ => sq_nonneg _) (by positivity)
        _ = ((32 / 15 : ℝ) * Real.sqrt γ) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hγ0]; ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq_bd
  have hpow210 : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 6 / 5 := by
    refine le_of_pow_le_pow_left₀ (by norm_num : 10 ≠ 0) (by norm_num) ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc
    (∑ x ∈ S.erase k, if 2 ≤ Int.natAbs ((x : ℤ) - k) then
        lam ^ Int.natAbs ((x : ℤ) - k) * (w x) ^ ((3 : ℝ) / 5) else 0)
        ≤ (25 / 16) * lam ^ 2 * (2 * γ) ^ ((1 : ℝ) / 10) * ((32 / 15 : ℝ) * Real.sqrt γ) :=
          hstep1.trans (mul_le_mul_of_nonneg_left hcs_far (by positivity))
    _ = (10 / 3 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) * lam ^ 2 * (γ ^ ((1 : ℝ) / 10) * γ ^ ((1 : ℝ) / 2)) := by
          rw [Real.mul_rpow (by norm_num) hγ0, Real.sqrt_eq_rpow]; ring
    _ = (10 / 3 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by
          rw [← Real.rpow_add' hγ0 (by norm_num)]; norm_num
    _ ≤ (10 / 3 : ℝ) * (6 / 5 : ℝ) * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow210 (by norm_num)) (sq_nonneg lam))
            (Real.rpow_nonneg hγ0 _)
    _ = 4 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by ring

private lemma conc_lemma (S : Finset ℕ) (hSne : S.Nonempty)
    (α β : ℕ → ℝ) (μ : ℕ → ℕ → ℝ) (c lam : ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hμ0 : ∀ i j, 0 ≤ μ i j)
    (hα1 : ∑ i ∈ S, α i = 1) (hβ1 : ∑ j ∈ S, β j = 1)
    (hμ1 : ∑ i ∈ S, ∑ j ∈ S, μ i j = 1)
    (hc : 0 < c ∧ c ≤ 1) (hlam : 0 < lam ∧ lam ≤ 4 / 5)
    (hbound : ∀ i ∈ S, ∀ j ∈ S,
      μ i j ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5)) :
    1 / 9 ≤ c ∧ ∃ k ∈ S,
      (∑ i ∈ S, ∑ j ∈ S,
        if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) ≤
        C_conc * lam ^ 3 := by
  have hc_ge := conc_c_ge S hSne α β μ c lam hα0 hβ0 hα1 hβ1 hμ1 hc.1 hlam hbound
  have hα_le1 : ∀ i ∈ S, α i ≤ 1 := fun i hi =>
    (Finset.single_le_sum (fun x _ => hα0 x) hi).trans_eq hα1
  have hβ_le1 : ∀ j ∈ S, β j ≤ 1 := fun j hj =>
    (Finset.single_le_sum (fun x _ => hβ0 x) hj).trans_eq hβ1
  let M : ℕ := S.sup' hSne id
  have hM : ∀ i ∈ S, i ≤ M := fun i hi => Finset.le_sup' id hi
  obtain ⟨k, hkS, hkmax⟩ := Finset.exists_max_image S (fun i => α i * β i) hSne
  let γ : ℝ := 1 - Real.sqrt (α k * β k)
  have hγ0 : 0 ≤ γ := by
    have : α k * β k ≤ 1 := mul_le_one₀ (hα_le1 k hkS) (hβ0 k) (hβ_le1 k hkS)
    have : Real.sqrt (α k * β k) ≤ 1 := Real.sqrt_le_one.mpr this
    dsimp [γ]; linarith
  have hγ1 : γ ≤ 1 := by
    have : 0 ≤ Real.sqrt (α k * β k) := Real.sqrt_nonneg _
    dsimp [γ]; linarith
  have h1mγ : Real.sqrt (α k * β k) = 1 - γ := by dsimp [γ]; ring
  have hαk_ge : 1 - 2 * γ ≤ α k := by
    have hle : 1 - γ ≤ Real.sqrt (α k) := by
      rw [← h1mγ]
      exact Real.sqrt_le_sqrt (mul_le_of_le_one_right (hα0 k) (hβ_le1 k hkS))
    have hsq : (1 - γ) ^ 2 ≤ α k :=
      (pow_le_pow_left₀ (by linarith) hle 2).trans_eq (Real.sq_sqrt (hα0 k))
    nlinarith
  have hβk_ge : 1 - 2 * γ ≤ β k := by
    have hle : 1 - γ ≤ Real.sqrt (β k) := by
      rw [← h1mγ]
      exact Real.sqrt_le_sqrt (mul_le_of_le_one_left (hβ0 k) (hα_le1 k hkS))
    have hsq : (1 - γ) ^ 2 ≤ β k :=
      (pow_le_pow_left₀ (by linarith) hle 2).trans_eq (Real.sq_sqrt (hβ0 k))
    nlinarith
  have hα_erase_sum : (∑ i ∈ S.erase k, α i) ≤ 2 * γ := by
    have := Finset.add_sum_erase S α hkS
    linarith
  have hβ_erase_sum : (∑ j ∈ S.erase k, β j) ≤ 2 * γ := by
    have := Finset.add_sum_erase S β hkS
    linarith
  have hα_erase_pt : ∀ i ∈ S.erase k, α i ≤ 2 * γ := fun i hi =>
    (Finset.single_le_sum (fun x _ => hα0 x) hi).trans hα_erase_sum
  have hβ_erase_pt : ∀ j ∈ S.erase k, β j ≤ 2 * γ := fun j hj =>
    (Finset.single_le_sum (fun x _ => hβ0 x) hj).trans hβ_erase_sum
  have h2γ0 : 0 ≤ 2 * γ := by linarith
  have hγ_rpow_split : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ 2 * γ → y ≤ 2 * γ →
      (x * y) ^ ((3 : ℝ) / 5) ≤ (2 * γ) ^ ((1 : ℝ) / 5) * (Real.sqrt x * Real.sqrt y) := by
    intro x y hx0 hy0 hxle hyle
    have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
    have hxy_le : x * y ≤ (2 * γ) ^ 2 := by nlinarith
    have h1 : (x * y) ^ ((1 : ℝ) / 10) ≤ (2 * γ) ^ ((1 : ℝ) / 5) := by
      have hsq : ((2 * γ) ^ 2) ^ ((1 : ℝ) / 10) = (2 * γ) ^ ((1 : ℝ) / 5) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h2γ0]; norm_num
      rw [← hsq]
      exact Real.rpow_le_rpow hxy0 hxy_le (by norm_num)
    have hprod : (x * y) ^ ((3 : ℝ) / 5) = (x * y) ^ ((1 : ℝ) / 10) * (x * y) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add' hxy0 (by norm_num)]; norm_num
    rw [hprod, ← Real.sqrt_eq_rpow, Real.sqrt_mul hx0]
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- Σ1
  have hSigma1 : (∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
      if i ≠ j then μ i j else 0) ≤ 25 * lam * γ ^ ((6 : ℝ) / 5) := by
    let J' := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase 0
    have hgeom' := sum_geom_Icc_erase0_le hlam.1.le hlam.2 M
    have hterm : ∀ i ∈ S.erase k, ∀ j ∈ S.erase k,
        (if i ≠ j then μ i j else 0) ≤
          (2 * γ) ^ ((1 : ℝ) / 5) * (if i ≠ j then
            lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) else 0) := by
      intro i hi j hj
      split_ifs with hij
      · have hbi := hbound i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)
        have hsp := hγ_rpow_split (α i) (β j) (hα0 i) (hβ0 j) (hα_erase_pt i hi) (hβ_erase_pt j hj)
        have hcle : c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) ≤
            lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hlam.1.le _) hc.2)
            (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 j)) _)
        calc
          μ i j ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) := hbi
          _ ≤ lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) := hcle
          _ ≤ lam ^ Int.natAbs ((i : ℤ) - j) *
              ((2 * γ) ^ ((1 : ℝ) / 5) * (Real.sqrt (α i) * Real.sqrt (β j))) :=
            mul_le_mul_of_nonneg_left hsp (pow_nonneg hlam.1.le _)
          _ = (2 * γ) ^ ((1 : ℝ) / 5) * (lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j))) := by
            ring
      · simp
    have hstep1 : (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0) ≤
        (2 * γ) ^ ((1 : ℝ) / 5) * ∑ d ∈ J', lam ^ Int.natAbs d *
          ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
            if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0 := by
      have hswap : ∀ i ∈ S.erase k, ∀ j ∈ S.erase k,
          (if i ≠ j then lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) else 0) =
            ∑ d ∈ J', if d = (i : ℤ) - j then
              lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 := by
        intro i hi j hj
        by_cases hij : i ≠ j
        · have hdJ : (i : ℤ) - j ∈ J' := by
            rw [Finset.mem_erase, Finset.mem_Icc]
            have := hM i (Finset.mem_of_mem_erase hi)
            have := hM j (Finset.mem_of_mem_erase hj)
            exact ⟨by omega, by omega, by omega⟩
          rw [if_pos hij, Finset.sum_ite_eq' J' ((i : ℤ) - j), if_pos hdJ]
        · rw [if_neg hij]
          symm
          refine Finset.sum_eq_zero fun d hd => if_neg ?_
          have hd0 := (Finset.mem_erase.mp hd).1
          intro h
          apply hd0
          omega
      calc
        (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0)
            ≤ ∑ i ∈ S.erase k, ∑ j ∈ S.erase k, (2 * γ) ^ ((1 : ℝ) / 5) * (if i ≠ j then
                lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) else 0) :=
              Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
        _ = (2 * γ) ^ ((1 : ℝ) / 5) * ∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then
              lam ^ Int.natAbs ((i : ℤ) - j) * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ = (2 * γ) ^ ((1 : ℝ) / 5) * ∑ i ∈ S.erase k, ∑ j ∈ S.erase k, ∑ d ∈ J',
              if d = (i : ℤ) - j then lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 := by
            congr 1
            exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hswap i hi j hj
        _ = (2 * γ) ^ ((1 : ℝ) / 5) * ∑ d ∈ J', lam ^ Int.natAbs d *
              ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
                if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0 := by
            congr 1
            calc
              (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, ∑ d ∈ J',
                  if d = (i : ℤ) - j then lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0)
                  = ∑ i ∈ S.erase k, ∑ d ∈ J', ∑ j ∈ S.erase k,
                      if d = (i : ℤ) - j then lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 :=
                    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
              _ = ∑ d ∈ J', ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
                    if d = (i : ℤ) - j then lam ^ Int.natAbs d * (Real.sqrt (α i) * Real.sqrt (β j)) else 0 :=
                  Finset.sum_comm
              _ = ∑ d ∈ J', lam ^ Int.natAbs d * ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
                    if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0 := by
                  refine Finset.sum_congr rfl fun d _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have hstep2 : (∑ d ∈ J', lam ^ Int.natAbs d *
        ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
          if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) ≤
        10 * lam * (2 * γ) := by
      have hcs : ∀ d, (∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
          if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0) ≤ 2 * γ := by
        intro d
        have h0 := sum_shift_sqrt_le (S.erase k) (S.erase k) α β hα0 hβ0 d
        have hprod : (∑ i ∈ S.erase k, α i) * (∑ j ∈ S.erase k, β j) ≤ (2 * γ) * (2 * γ) :=
          mul_le_mul hα_erase_sum hβ_erase_sum (Finset.sum_nonneg fun j _ => hβ0 j) h2γ0
        have hsqrt : Real.sqrt ((∑ i ∈ S.erase k, α i) * (∑ j ∈ S.erase k, β j)) ≤ 2 * γ :=
          (Real.sqrt_le_sqrt (by linarith)).trans_eq (Real.sqrt_sq h2γ0)
        exact h0.trans hsqrt
      calc
        (∑ d ∈ J', lam ^ Int.natAbs d * ∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
            if d = (i : ℤ) - j then Real.sqrt (α i) * Real.sqrt (β j) else 0)
            ≤ ∑ d ∈ J', lam ^ Int.natAbs d * (2 * γ) :=
              Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hcs d) (pow_nonneg hlam.1.le _)
        _ = (∑ d ∈ J', lam ^ Int.natAbs d) * (2 * γ) := (Finset.sum_mul _ _ _).symm
        _ ≤ (10 * lam) * (2 * γ) := mul_le_mul_of_nonneg_right hgeom' h2γ0
        _ = 10 * lam * (2 * γ) := by ring
    have hpow26 : (2 : ℝ) ^ ((6 : ℝ) / 5) ≤ 5 / 2 := by
      refine le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num) ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    calc
      (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0)
          ≤ (2 * γ) ^ ((1 : ℝ) / 5) * (10 * lam * (2 * γ)) :=
            hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg h2γ0 _))
      _ = 10 * lam * ((2 * γ) ^ ((1 : ℝ) / 5) * (2 * γ)) := by ring
      _ = 10 * lam * (2 * γ) ^ ((6 : ℝ) / 5) := by
            congr 2
            nth_rw 2 [← Real.rpow_one (2 * γ)]
            rw [← Real.rpow_add' h2γ0 (by norm_num)]; norm_num
      _ = 10 * (2 : ℝ) ^ ((6 : ℝ) / 5) * lam * γ ^ ((6 : ℝ) / 5) := by
            rw [Real.mul_rpow (by norm_num) hγ0]; ring
      _ ≤ 10 * (5 / 2 : ℝ) * lam * γ ^ ((6 : ℝ) / 5) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow26 (by norm_num)) hlam.1.le)
              (Real.rpow_nonneg hγ0 _)
      _ = 25 * lam * γ ^ ((6 : ℝ) / 5) := by ring
  -- Σ2 and Σ3
  have hSigma2 : (∑ j ∈ S.erase k, if 2 ≤ Int.natAbs ((j : ℤ) - k) then μ k j else 0) ≤
      4 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by
    have h1 : (∑ j ∈ S.erase k, if 2 ≤ Int.natAbs ((j : ℤ) - k) then μ k j else 0) ≤
        ∑ j ∈ S.erase k, if 2 ≤ Int.natAbs ((j : ℤ) - k) then
          lam ^ Int.natAbs ((j : ℤ) - k) * (β j) ^ ((3 : ℝ) / 5) else 0 := by
      refine Finset.sum_le_sum fun j hj => ?_
      split_ifs with h2
      · have hb := hbound k hkS j (Finset.mem_of_mem_erase hj)
        have hnat : Int.natAbs ((k : ℤ) - j) = Int.natAbs ((j : ℤ) - k) := by
          rw [← Int.natAbs_neg, neg_sub]
        rw [hnat] at hb
        have hα1' : (α k) ^ ((3 : ℝ) / 5) ≤ 1 := Real.rpow_le_one (hα0 k) (hα_le1 k hkS) (by norm_num)
        have hcle : c * lam ^ Int.natAbs ((j : ℤ) - k) * (α k * β j) ^ ((3 : ℝ) / 5) ≤
            lam ^ Int.natAbs ((j : ℤ) - k) * (α k * β j) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hlam.1.le _) hc.2)
            (Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 j)) _)
        calc
          μ k j ≤ c * lam ^ Int.natAbs ((j : ℤ) - k) * (α k * β j) ^ ((3 : ℝ) / 5) := hb
          _ ≤ lam ^ Int.natAbs ((j : ℤ) - k) * (α k * β j) ^ ((3 : ℝ) / 5) := hcle
          _ = lam ^ Int.natAbs ((j : ℤ) - k) * ((α k) ^ ((3 : ℝ) / 5) * (β j) ^ ((3 : ℝ) / 5)) := by
            rw [Real.mul_rpow (hα0 k) (hβ0 j)]
          _ ≤ lam ^ Int.natAbs ((j : ℤ) - k) * (1 * (β j) ^ ((3 : ℝ) / 5)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hα1' (Real.rpow_nonneg (hβ0 j) _))
              (pow_nonneg hlam.1.le _)
          _ = lam ^ Int.natAbs ((j : ℤ) - k) * (β j) ^ ((3 : ℝ) / 5) := by ring
      · simp
    exact h1.trans (conc_sigma_ray S hSne k β lam γ hβ0 hγ0 hβ_erase_sum hlam)
  have hSigma3 : (∑ i ∈ S.erase k, if 2 ≤ Int.natAbs ((i : ℤ) - k) then μ i k else 0) ≤
      4 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) := by
    have h1 : (∑ i ∈ S.erase k, if 2 ≤ Int.natAbs ((i : ℤ) - k) then μ i k else 0) ≤
        ∑ i ∈ S.erase k, if 2 ≤ Int.natAbs ((i : ℤ) - k) then
          lam ^ Int.natAbs ((i : ℤ) - k) * (α i) ^ ((3 : ℝ) / 5) else 0 := by
      refine Finset.sum_le_sum fun i hi => ?_
      split_ifs with h2
      · have hb := hbound i (Finset.mem_of_mem_erase hi) k hkS
        have hβ1' : (β k) ^ ((3 : ℝ) / 5) ≤ 1 := Real.rpow_le_one (hβ0 k) (hβ_le1 k hkS) (by norm_num)
        have hcle : c * lam ^ Int.natAbs ((i : ℤ) - k) * (α i * β k) ^ ((3 : ℝ) / 5) ≤
            lam ^ Int.natAbs ((i : ℤ) - k) * (α i * β k) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (pow_nonneg hlam.1.le _) hc.2)
            (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 k)) _)
        calc
          μ i k ≤ c * lam ^ Int.natAbs ((i : ℤ) - k) * (α i * β k) ^ ((3 : ℝ) / 5) := hb
          _ ≤ lam ^ Int.natAbs ((i : ℤ) - k) * (α i * β k) ^ ((3 : ℝ) / 5) := hcle
          _ = lam ^ Int.natAbs ((i : ℤ) - k) * ((α i) ^ ((3 : ℝ) / 5) * (β k) ^ ((3 : ℝ) / 5)) := by
            rw [Real.mul_rpow (hα0 i) (hβ0 k)]
          _ ≤ lam ^ Int.natAbs ((i : ℤ) - k) * ((α i) ^ ((3 : ℝ) / 5) * 1) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ1' (Real.rpow_nonneg (hα0 i) _))
              (pow_nonneg hlam.1.le _)
          _ = lam ^ Int.natAbs ((i : ℤ) - k) * (α i) ^ ((3 : ℝ) / 5) := by ring
      · simp
    exact h1.trans (conc_sigma_ray S hSne k α lam γ hα0 hγ0 hα_erase_sum hlam)
  -- Σ5
  have hSigma5 : (∑ i ∈ S.erase k, μ i i) ≤ 3 * γ ^ ((6 : ℝ) / 5) := by
    have h1 : (∑ i ∈ S.erase k, μ i i) ≤
        (2 * γ) ^ ((1 : ℝ) / 5) * ∑ i ∈ S.erase k, Real.sqrt (α i) * Real.sqrt (β i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hb := hbound i (Finset.mem_of_mem_erase hi) i (Finset.mem_of_mem_erase hi)
      rw [sub_self, Int.natAbs_zero, pow_zero, mul_one] at hb
      have hsp := hγ_rpow_split (α i) (β i) (hα0 i) (hβ0 i) (hα_erase_pt i hi) (hβ_erase_pt i hi)
      have hcle : c * (α i * β i) ^ ((3 : ℝ) / 5) ≤ (α i * β i) ^ ((3 : ℝ) / 5) :=
        mul_le_of_le_one_left (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 i)) _) hc.2
      exact hb.trans (hcle.trans hsp)
    have hcs : (∑ i ∈ S.erase k, Real.sqrt (α i) * Real.sqrt (β i)) ≤ 2 * γ := by
      have h0 := Finset.sum_mul_sq_le_sq_mul_sq (S.erase k) (fun i => Real.sqrt (α i)) (fun i => Real.sqrt (β i))
      have hsq1 : (∑ i ∈ S.erase k, (Real.sqrt (α i)) ^ 2) = ∑ i ∈ S.erase k, α i :=
        Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hα0 i)
      have hsq2 : (∑ i ∈ S.erase k, (Real.sqrt (β i)) ^ 2) = ∑ i ∈ S.erase k, β i :=
        Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hβ0 i)
      rw [hsq1, hsq2] at h0
      have hprod : (∑ i ∈ S.erase k, α i) * (∑ i ∈ S.erase k, β i) ≤ (2 * γ) ^ 2 := by
        nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ S.erase k) => hα0 i),
          Finset.sum_nonneg (fun i (_ : i ∈ S.erase k) => hβ0 i)]
      nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ S.erase k) => mul_nonneg (Real.sqrt_nonneg (α i)) (Real.sqrt_nonneg (β i)))]
    have hpow26 : (2 : ℝ) ^ ((6 : ℝ) / 5) ≤ 3 := by
      refine le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num) ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    calc
      (∑ i ∈ S.erase k, μ i i) ≤ (2 * γ) ^ ((1 : ℝ) / 5) * (2 * γ) :=
        h1.trans (mul_le_mul_of_nonneg_left hcs (Real.rpow_nonneg h2γ0 _))
      _ = (2 * γ) ^ ((6 : ℝ) / 5) := by
        nth_rw 2 [← Real.rpow_one (2 * γ)]
        rw [← Real.rpow_add' h2γ0 (by norm_num)]; norm_num
      _ = (2 : ℝ) ^ ((6 : ℝ) / 5) * γ ^ ((6 : ℝ) / 5) := Real.mul_rpow (by norm_num) hγ0
      _ ≤ 3 * γ ^ ((6 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hpow26 (Real.rpow_nonneg hγ0 _)
  -- Σ5 + Σ6
  have hSigma56 : (∑ i ∈ S, μ i i) ≤ 1 - γ / 5 := by
    have h1 : (∑ i ∈ S, μ i i) ≤ (1 - γ / 5) * ∑ i ∈ S, Real.sqrt (α i) * Real.sqrt (β i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hb := hbound i hi i hi
      rw [sub_self, Int.natAbs_zero, pow_zero, mul_one] at hb
      have hmax : α i * β i ≤ α k * β k := hkmax i hi
      have hsq_le : Real.sqrt (α i * β i) ≤ 1 - γ := (Real.sqrt_le_sqrt hmax).trans_eq h1mγ
      have hprod_le : (α i * β i) ^ ((3 : ℝ) / 5) ≤ (1 - γ / 5) * (Real.sqrt (α i) * Real.sqrt (β i)) := by
        have hxy0 : 0 ≤ α i * β i := mul_nonneg (hα0 i) (hβ0 i)
        have h1' : (α i * β i) ^ ((1 : ℝ) / 10) ≤ (1 - γ) ^ ((1 : ℝ) / 5) := by
          have hsq' : ((1 - γ) ^ 2) ^ ((1 : ℝ) / 10) = (1 - γ) ^ ((1 : ℝ) / 5) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
          rw [← hsq']
          have hxy_le' : α i * β i ≤ (1 - γ) ^ 2 := by
            calc
              α i * β i = (Real.sqrt (α i * β i)) ^ 2 := (Real.sq_sqrt hxy0).symm
              _ ≤ (1 - γ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le 2
          exact Real.rpow_le_rpow hxy0 hxy_le' (by norm_num)
        have h2' := one_sub_rpow_one_fifth_le hγ0 hγ1
        have hprod : (α i * β i) ^ ((3 : ℝ) / 5) =
            (α i * β i) ^ ((1 : ℝ) / 10) * (α i * β i) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add' hxy0 (by norm_num)]; norm_num
        rw [hprod, ← Real.sqrt_eq_rpow, Real.sqrt_mul (hα0 i)]
        exact mul_le_mul (h1'.trans h2') le_rfl (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by linarith)
      have hcle : c * (α i * β i) ^ ((3 : ℝ) / 5) ≤ (α i * β i) ^ ((3 : ℝ) / 5) :=
        mul_le_of_le_one_left (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 i)) _) hc.2
      exact hb.trans (hcle.trans hprod_le)
    have hcs : (∑ i ∈ S, Real.sqrt (α i) * Real.sqrt (β i)) ≤ 1 := by
      have h0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (α i)) (fun i => Real.sqrt (β i))
      have hsq1 : (∑ i ∈ S, (Real.sqrt (α i)) ^ 2) = 1 :=
        (Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hα0 i)).trans hα1
      have hsq2 : (∑ i ∈ S, (Real.sqrt (β i)) ^ 2) = 1 :=
        (Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hβ0 i)).trans hβ1
      rw [hsq1, hsq2, mul_one] at h0
      nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ S) => mul_nonneg (Real.sqrt_nonneg (α i)) (Real.sqrt_nonneg (β i)))]
    exact h1.trans (mul_le_of_le_one_right (by linarith) hcs)
  -- Σ4
  have hSigma4 : (∑ i ∈ S, ∑ j ∈ S,
      if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
        μ i j else 0) ≤ 8 * lam * γ ^ ((3 : ℝ) / 5) := by
    have h4_1 : (∑ j ∈ S.erase k, if Int.natAbs ((j : ℤ) - k) = 1 then μ k j else 0) ≤
        4 * lam * γ ^ ((3 : ℝ) / 5) := by
      have hsub : (S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1) ⊆
          ({k + 1, k - 1} : Finset ℕ) := by
        intro j hj
        have hj1 := Finset.mem_erase.mp (Finset.mem_filter.mp hj).1
        have hj2 := (Finset.mem_filter.mp hj).2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [← Finset.sum_filter]
      have hpt : ∀ j ∈ (S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1),
          μ k j ≤ 2 * lam * γ ^ ((3 : ℝ) / 5) := by
        intro j hj
        have hj1 := (Finset.mem_filter.mp hj).1
        have hj2 := (Finset.mem_filter.mp hj).2
        have hb := hbound k hkS j (Finset.mem_of_mem_erase hj1)
        have hnat : Int.natAbs ((k : ℤ) - j) = 1 := by rw [← Int.natAbs_neg, neg_sub]; exact hj2
        rw [hnat, pow_one] at hb
        have hα1' : (α k) ^ ((3 : ℝ) / 5) ≤ 1 := Real.rpow_le_one (hα0 k) (hα_le1 k hkS) (by norm_num)
        have hβ' : (β j) ^ ((3 : ℝ) / 5) ≤ (2 * γ) ^ ((3 : ℝ) / 5) :=
          Real.rpow_le_rpow (hβ0 j) (hβ_erase_pt j hj1) (by norm_num)
        have h2p : (2 : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 :=
          Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
        have hcle : c * lam * (α k * β j) ^ ((3 : ℝ) / 5) ≤ lam * (α k * β j) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hlam.1.le hc.2)
            (Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 j)) _)
        calc
          μ k j ≤ c * lam * (α k * β j) ^ ((3 : ℝ) / 5) := hb
          _ ≤ lam * (α k * β j) ^ ((3 : ℝ) / 5) := hcle
          _ = lam * ((α k) ^ ((3 : ℝ) / 5) * (β j) ^ ((3 : ℝ) / 5)) := by
            rw [Real.mul_rpow (hα0 k) (hβ0 j)]
          _ ≤ lam * (1 * (2 * γ) ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hα1' hβ' (Real.rpow_nonneg (hβ0 j) _) (by norm_num)) hlam.1.le
          _ = lam * ((2 : ℝ) ^ ((3 : ℝ) / 5) * γ ^ ((3 : ℝ) / 5)) := by
            rw [one_mul, Real.mul_rpow (by norm_num) hγ0]
          _ ≤ lam * (2 * γ ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hγ0 _)) hlam.1.le
          _ = 2 * lam * γ ^ ((3 : ℝ) / 5) := by ring
      have hcard : ((S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1)).card ≤ 2 :=
        (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
      calc
        (∑ j ∈ (S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1), μ k j)
            ≤ ∑ _j ∈ (S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1),
                2 * lam * γ ^ ((3 : ℝ) / 5) := Finset.sum_le_sum hpt
        _ = (((S.erase k).filter (fun j : ℕ => Int.natAbs ((j : ℤ) - k) = 1)).card : ℝ) *
              (2 * lam * γ ^ ((3 : ℝ) / 5)) := by simp
        _ ≤ 2 * (2 * lam * γ ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
              (mul_nonneg (mul_nonneg (by norm_num) hlam.1.le) (Real.rpow_nonneg hγ0 _))
        _ = 4 * lam * γ ^ ((3 : ℝ) / 5) := by ring
    have h4_2 : (∑ i ∈ S.erase k, if Int.natAbs ((i : ℤ) - k) = 1 then μ i k else 0) ≤
        4 * lam * γ ^ ((3 : ℝ) / 5) := by
      have hsub : (S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1) ⊆
          ({k + 1, k - 1} : Finset ℕ) := by
        intro i hi
        have hi1 := Finset.mem_erase.mp (Finset.mem_filter.mp hi).1
        have hi2 := (Finset.mem_filter.mp hi).2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [← Finset.sum_filter]
      have hpt : ∀ i ∈ (S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1),
          μ i k ≤ 2 * lam * γ ^ ((3 : ℝ) / 5) := by
        intro i hi
        have hi1 := (Finset.mem_filter.mp hi).1
        have hi2 := (Finset.mem_filter.mp hi).2
        have hb := hbound i (Finset.mem_of_mem_erase hi1) k hkS
        rw [hi2, pow_one] at hb
        have hβ1' : (β k) ^ ((3 : ℝ) / 5) ≤ 1 := Real.rpow_le_one (hβ0 k) (hβ_le1 k hkS) (by norm_num)
        have hα' : (α i) ^ ((3 : ℝ) / 5) ≤ (2 * γ) ^ ((3 : ℝ) / 5) :=
          Real.rpow_le_rpow (hα0 i) (hα_erase_pt i hi1) (by norm_num)
        have h2p : (2 : ℝ) ^ ((3 : ℝ) / 5) ≤ 2 :=
          Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
        have hcle : c * lam * (α i * β k) ^ ((3 : ℝ) / 5) ≤ lam * (α i * β k) ^ ((3 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hlam.1.le hc.2)
            (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 k)) _)
        calc
          μ i k ≤ c * lam * (α i * β k) ^ ((3 : ℝ) / 5) := hb
          _ ≤ lam * (α i * β k) ^ ((3 : ℝ) / 5) := hcle
          _ = lam * ((α i) ^ ((3 : ℝ) / 5) * (β k) ^ ((3 : ℝ) / 5)) := by
            rw [Real.mul_rpow (hα0 i) (hβ0 k)]
          _ ≤ lam * ((2 * γ) ^ ((3 : ℝ) / 5) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hα' hβ1' (Real.rpow_nonneg (hβ0 k) _) (by positivity)) hlam.1.le
          _ = lam * ((2 : ℝ) ^ ((3 : ℝ) / 5) * γ ^ ((3 : ℝ) / 5)) := by
            rw [mul_one, Real.mul_rpow (by norm_num) hγ0]
          _ ≤ lam * (2 * γ ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hγ0 _)) hlam.1.le
          _ = 2 * lam * γ ^ ((3 : ℝ) / 5) := by ring
      have hcard : ((S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1)).card ≤ 2 :=
        (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
      calc
        (∑ i ∈ (S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1), μ i k)
            ≤ ∑ _i ∈ (S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1),
                2 * lam * γ ^ ((3 : ℝ) / 5) := Finset.sum_le_sum hpt
        _ = (((S.erase k).filter (fun i : ℕ => Int.natAbs ((i : ℤ) - k) = 1)).card : ℝ) *
              (2 * lam * γ ^ ((3 : ℝ) / 5)) := by simp
        _ ≤ 2 * (2 * lam * γ ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
              (mul_nonneg (mul_nonneg (by norm_num) hlam.1.le) (Real.rpow_nonneg hγ0 _))
        _ = 4 * lam * γ ^ ((3 : ℝ) / 5) := by ring
    have hsplit4 : (∑ i ∈ S, ∑ j ∈ S,
        if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
          μ i j else 0) ≤
        (∑ j ∈ S.erase k, if Int.natAbs ((j : ℤ) - k) = 1 then μ k j else 0) +
        (∑ i ∈ S.erase k, if Int.natAbs ((i : ℤ) - k) = 1 then μ i k else 0) := by
      rw [← Finset.add_sum_erase S _ hkS]
      have hk_row : (∑ j ∈ S, if (k = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨
          (j = k ∧ Int.natAbs ((k : ℤ) - k) = 1) then μ k j else 0) =
          ∑ j ∈ S.erase k, if Int.natAbs ((j : ℤ) - k) = 1 then μ k j else 0 := by
        rw [← Finset.add_sum_erase S _ hkS]
        have hkk : Int.natAbs ((k : ℤ) - k) = 0 := by simp
        simp only [hkk, zero_ne_one, and_false, or_self, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
        simp only [true_and, or_false]
      have h_rest : (∑ i ∈ S.erase k, ∑ j ∈ S,
          if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
            μ i j else 0) =
          ∑ i ∈ S.erase k, if Int.natAbs ((i : ℤ) - k) = 1 then μ i k else 0 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        rw [← Finset.add_sum_erase S _ hkS]
        have hother : (∑ j ∈ S.erase k, if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨
            (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then μ i j else 0) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
          simp [hik, hjk]
        rw [hother, add_zero]
        simp [hik]
      rw [hk_row, h_rest]
    linarith only [hsplit4, h4_1, h4_2]
  have hbad_bound : (∑ i ∈ S, ∑ j ∈ S,
      if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) ≤
      (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0) +
      (∑ j ∈ S.erase k, if 2 ≤ Int.natAbs ((j : ℤ) - k) then μ k j else 0) +
      (∑ i ∈ S.erase k, if 2 ≤ Int.natAbs ((i : ℤ) - k) then μ i k else 0) +
      (∑ i ∈ S.erase k, μ i i) := by
    rw [← Finset.add_sum_erase S _ hkS]
    have hrow_k : (∑ j ∈ S, if 2 ≤ Int.natAbs ((k : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ k j else 0) =
        ∑ j ∈ S.erase k, if 2 ≤ Int.natAbs ((j : ℤ) - k) then μ k j else 0 := by
      rw [← Finset.add_sum_erase S _ hkS]
      simp [Int.natAbs_zero]
    have hcol_k : (∑ i ∈ S.erase k, ∑ j ∈ S,
        if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) =
        (∑ i ∈ S.erase k, if 2 ≤ Int.natAbs ((i : ℤ) - k) then μ i k else 0) +
        (∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
          if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.add_sum_erase S _ hkS]
      simp [Int.natAbs_zero]
    have hdiag : (∑ i ∈ S.erase k, ∑ j ∈ S.erase k,
        if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) =
        (∑ i ∈ S.erase k, ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0) +
        (∑ i ∈ S.erase k, μ i i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≠ k := (Finset.mem_erase.mp hi).1
      rw [← Finset.add_sum_erase (S.erase k) _ hi]
      have hii : 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((i : ℤ) - k) := by omega
      have hrest1 : (∑ j ∈ (S.erase k).erase i,
          if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) =
          ∑ j ∈ (S.erase k).erase i, if i ≠ j then μ i j else 0 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        have hjk : j ≠ k := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj)).1
        have h2 : 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) := by omega
        rw [if_pos h2, if_pos hij]
      have hrest2 : (∑ j ∈ (S.erase k).erase i, if i ≠ j then μ i j else 0) =
          ∑ j ∈ S.erase k, if i ≠ j then μ i j else 0 := by
        rw [← Finset.add_sum_erase (S.erase k) _ hi]
        simp
      rw [if_pos hii, hrest1, hrest2]
      ring
    linarith only [hrow_k, hcol_k, hdiag]
  have hfull : (∑ i ∈ S, ∑ j ∈ S, μ i j) ≤
      (∑ i ∈ S, ∑ j ∈ S,
        if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) +
      (∑ i ∈ S, ∑ j ∈ S,
        if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
          μ i j else 0) +
      μ k k := by
    have hsplit : ∀ i ∈ S, ∀ j ∈ S,
        μ i j ≤
          (if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) +
          (if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
            μ i j else 0) +
          (if i = k ∧ j = k then μ i j else 0) := by
      intro i _ j _
      have h0 := hμ0 i j
      by_cases hbad : 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k)
      · rw [if_pos hbad]; split_ifs <;> linarith
      · rw [if_neg hbad]
        have hsmall : Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) ≤ 1 := by omega
        by_cases hkk : i = k ∧ j = k
        · rw [if_pos hkk]; split_ifs <;> linarith
        · have h4 : (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨
              (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) := by omega
          rw [if_pos h4, if_neg hkk]; linarith
    have hsum_kk : (∑ i ∈ S, ∑ j ∈ S, if i = k ∧ j = k then μ i j else 0) = μ k k := by
      have hrow : ∀ i ∈ S, (∑ j ∈ S, if i = k ∧ j = k then μ i j else 0) =
          if i = k then μ k k else 0 := by
        intro i _
        by_cases hik : i = k
        · subst hik; simp [hkS]
        · simp [hik]
      rw [Finset.sum_congr rfl hrow]
      simp [hkS]
    calc
      (∑ i ∈ S, ∑ j ∈ S, μ i j)
          ≤ ∑ i ∈ S, ∑ j ∈ S,
              ((if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) +
               (if (i = k ∧ Int.natAbs ((j : ℤ) - k) = 1) ∨ (j = k ∧ Int.natAbs ((i : ℤ) - k) = 1) then
                  μ i j else 0) +
               (if i = k ∧ j = k then μ i j else 0)) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hsplit i hi j hj
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [hsum_kk]
  have h56_ge : (∑ i ∈ S.erase k, μ i i) + μ k k = ∑ i ∈ S, μ i i := by
    rw [← Finset.add_sum_erase S (fun i => μ i i) hkS]; ring
  have h1_le : (1 : ℝ) ≤ 25 * lam * γ ^ ((6 : ℝ) / 5) + 8 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) +
      8 * lam * γ ^ ((3 : ℝ) / 5) + (1 - γ / 5) := by
    have hmu_le := hμ1.symm.le.trans hfull
    linarith only [hmu_le, hbad_bound, hSigma1, hSigma2, hSigma3, hSigma4, hSigma56, h56_ge]
  have hγ_65_le_35 : γ ^ ((6 : ℝ) / 5) ≤ γ ^ ((3 : ℝ) / 5) := by
    by_cases h0 : γ = 0
    · rw [h0]; norm_num
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hγ0 (Ne.symm h0)) hγ1 (by norm_num)
  have hlam2_le : lam ^ 2 ≤ lam := by nlinarith [hlam.1, hlam.2]
  have hγ_ineq : γ / 5 ≤ 41 * lam * γ ^ ((3 : ℝ) / 5) := by
    have h1 : 25 * lam * γ ^ ((6 : ℝ) / 5) ≤ 25 * lam * γ ^ ((3 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left hγ_65_le_35 (mul_nonneg (by norm_num) hlam.1.le)
    have h2 : 8 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) ≤ 8 * lam * γ ^ ((3 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam2_le (by norm_num)) (Real.rpow_nonneg hγ0 _)
    linarith only [h1_le, h1, h2]
  have hγ25_le : γ ^ ((2 : ℝ) / 5) ≤ 205 * lam := by
    by_cases h0 : γ = 0
    · rw [h0]; norm_num; linarith [hlam.1]
    · have hpos : 0 < γ := lt_of_le_of_ne hγ0 (Ne.symm h0)
      have hrpos : 0 < γ ^ ((3 : ℝ) / 5) := Real.rpow_pos_of_pos hpos _
      have hdiv : γ / γ ^ ((3 : ℝ) / 5) ≤ 205 * lam := by
        rw [div_le_iff₀ hrpos]; linarith only [hγ_ineq]
      have heq : γ / γ ^ ((3 : ℝ) / 5) = γ ^ ((2 : ℝ) / 5) := by
        nth_rw 1 [← Real.rpow_one γ]
        rw [← Real.rpow_sub hpos]; norm_num
      rwa [heq] at hdiv
  have hbad_final : (∑ i ∈ S, ∑ j ∈ S,
      if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) ≤
      C_conc * lam ^ 3 := by
    have h65 : γ ^ ((6 : ℝ) / 5) ≤ (205 : ℝ) ^ 3 * lam ^ 3 := by
      have h1 : γ ^ ((6 : ℝ) / 5) = (γ ^ ((2 : ℝ) / 5)) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hγ0]; norm_num
      rw [h1]
      calc
        (γ ^ ((2 : ℝ) / 5)) ^ 3 ≤ (205 * lam) ^ 3 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hγ0 _) hγ25_le 3
        _ = (205 : ℝ) ^ 3 * lam ^ 3 := by ring
    have hlam_35 : lam ^ 2 * γ ^ ((3 : ℝ) / 5) ≤ (205 : ℝ) ^ 3 * lam ^ 3 := by
      have hsq : (lam ^ 2 * γ ^ ((3 : ℝ) / 5)) ^ 2 ≤ ((205 : ℝ) ^ 2 * lam ^ 3) ^ 2 := by
        have h1 : (γ ^ ((3 : ℝ) / 5)) ^ 2 = γ ^ ((6 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hγ0]; norm_num
        have hlam7 : lam ^ 7 ≤ lam ^ 6 := by
          have := mul_le_mul_of_nonneg_left (by linarith [hlam.2] : lam ≤ 1) (pow_nonneg hlam.1.le 6)
          linarith [show lam ^ 6 * lam = lam ^ 7 by ring, show lam ^ 6 * 1 = lam ^ 6 by ring]
        calc
          (lam ^ 2 * γ ^ ((3 : ℝ) / 5)) ^ 2 = lam ^ 4 * (γ ^ ((3 : ℝ) / 5)) ^ 2 := by ring
          _ = lam ^ 4 * γ ^ ((6 : ℝ) / 5) := by rw [h1]
          _ ≤ lam ^ 4 * ((205 : ℝ) ^ 3 * lam ^ 3) := mul_le_mul_of_nonneg_left h65 (pow_nonneg hlam.1.le 4)
          _ = (205 : ℝ) ^ 3 * lam ^ 7 := by ring
          _ ≤ (205 : ℝ) ^ 3 * lam ^ 6 := mul_le_mul_of_nonneg_left hlam7 (by norm_num)
          _ ≤ (205 : ℝ) ^ 4 * lam ^ 6 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hlam.1.le 6)
          _ = ((205 : ℝ) ^ 2 * lam ^ 3) ^ 2 := by ring
      have hle2 : lam ^ 2 * γ ^ ((3 : ℝ) / 5) ≤ (205 : ℝ) ^ 2 * lam ^ 3 :=
        le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg hlam.1.le 3)) hsq
      calc
        lam ^ 2 * γ ^ ((3 : ℝ) / 5) ≤ (205 : ℝ) ^ 2 * lam ^ 3 := hle2
        _ ≤ (205 : ℝ) ^ 3 * lam ^ 3 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hlam.1.le 3)
    have htot : (∑ i ∈ S, ∑ j ∈ S,
        if 2 ≤ Int.natAbs ((i : ℤ) - k) + Int.natAbs ((j : ℤ) - k) then μ i j else 0) ≤
        25 * lam * γ ^ ((6 : ℝ) / 5) + 8 * lam ^ 2 * γ ^ ((3 : ℝ) / 5) + 3 * γ ^ ((6 : ℝ) / 5) := by
      linarith only [hbad_bound, hSigma1, hSigma2, hSigma3, hSigma5]
    have hlam1 : 25 * lam * γ ^ ((6 : ℝ) / 5) ≤ 25 * (205 : ℝ) ^ 3 * lam ^ 3 := by
      calc
        25 * lam * γ ^ ((6 : ℝ) / 5) ≤ 25 * 1 * ((205 : ℝ) ^ 3 * lam ^ 3) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hlam.2]) (by norm_num))
            h65 (Real.rpow_nonneg hγ0 _) (by norm_num)
        _ = 25 * (205 : ℝ) ^ 3 * lam ^ 3 := by ring
    dsimp [C_conc]
    linarith only [htot, hlam1, hlam_35, h65]
  exact ⟨hc_ge, k, hkS, hbad_final⟩


private def p0 : ℕ := 256 ^ 34

private lemma prime_tail_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p0 < p) :
    C_conc * ∑ p ∈ P, (p : ℝ) ^ (-(9 : ℝ) / 8) ≤ 1 / 2 := by
  by_cases hPe : P = ∅
  · subst hPe; simp
  have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPe
  let Kmax : ℕ := P.sup (Nat.log 2) + 1
  let I : Finset ℕ := Finset.Ico 272 Kmax
  have hmap : ∀ p ∈ P, Nat.log 2 p ∈ I := by
    intro p hp
    have hgt0 : 256 ^ 34 < p := hP p hp
    have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
    have hgt : (2 : ℕ) ^ (8 * 34) ≤ p := by rw [pow_mul, h256]; exact hgt0.le
    have hlo : 272 ≤ Nat.log 2 p := by simpa using Nat.le_log_of_pow_le (by norm_num) hgt
    have hhi : Nat.log 2 p < Kmax := Nat.lt_succ_of_le (Finset.le_sup hp)
    exact Finset.mem_Ico.mpr ⟨hlo, hhi⟩
  let r : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 8)
  have hr0 : 0 < r := by positivity
  have hr8 : r ^ 8 = 1 / 2 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hr_lt : r < 15 / 16 := by
    refine lt_of_pow_lt_pow_left₀ 8 (by norm_num) ?_
    rw [hr8]
    norm_num
  have hle_sum : (∑ p ∈ P, (p : ℝ) ^ (-(9 : ℝ) / 8)) ≤ ∑ k ∈ I, r ^ k := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_le_sum fun k _ => ?_
    let Pk := P.filter (fun p => Nat.log 2 p = k)
    have hPk_sub : Pk ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
      intro p hp
      have hp_mem := (Finset.mem_filter.mp hp).1
      have hk := (Finset.mem_filter.mp hp).2
      have hp0 : p ≠ 0 := (lt_trans (pow_pos (by norm_num) 34) (hP p hp_mem)).ne'
      rw [Finset.mem_Ico, ← hk]
      exact ⟨Nat.pow_log_le_self 2 hp0, Nat.lt_pow_succ_log_self (by norm_num) p⟩
    have hterm : ∀ p ∈ Pk, (p : ℝ) ^ (-(9 : ℝ) / 8) ≤ ((2 ^ k : ℕ) : ℝ) ^ (-(9 : ℝ) / 8) := by
      intro p hp
      have hp_sub := Finset.mem_Ico.mp (hPk_sub hp)
      have hle : ((2 ^ k : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_sub.1
      have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.two_pow_pos k
      exact Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
    have hcard : (Pk.card : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      have h1 : Pk.card ≤ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card := Finset.card_le_card hPk_sub
      have h2 : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).card = 2 ^ k := by
        rw [Nat.card_Ico, pow_succ]; omega
      exact_mod_cast h1.trans_eq h2
    have hprod_eq : ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ (-(9 : ℝ) / 8) = r ^ k := by
      have h2k : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by push_cast; rw [Real.rpow_natCast]
      rw [h2k]
      nth_rw 1 [← Real.rpow_one ((2 : ℝ) ^ (k : ℝ))]
      rw [← Real.rpow_add' (by positivity) (by norm_num)]
      have h1 : (1 : ℝ) + (-(9 : ℝ) / 8) = -(1 : ℝ) / 8 := by norm_num
      rw [h1, ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ), Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    calc
      (∑ p ∈ Pk, (p : ℝ) ^ (-(9 : ℝ) / 8)) ≤ ∑ _p ∈ Pk, ((2 ^ k : ℕ) : ℝ) ^ (-(9 : ℝ) / 8) :=
        Finset.sum_le_sum hterm
      _ = (Pk.card : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ (-(9 : ℝ) / 8) := by simp
      _ ≤ ((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ (-(9 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)
      _ = r ^ k := hprod_eq
  have hgeom : (∑ k ∈ I, r ^ k) ≤ (1 / 2 : ℝ) ^ 34 * 16 := by
    by_cases hK : Kmax ≤ 272
    · have hIe : I = ∅ := Finset.Ico_eq_empty_of_le hK
      rw [hIe, Finset.sum_empty]
      positivity
    · have hK' : 272 ≤ Kmax := by omega
      have himg : I = (Finset.range (Kmax - 272)).image (· + 272) := by
        ext k; simp only [I, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
        exact ⟨fun ⟨h1, h2⟩ => ⟨k - 272, by omega, by omega⟩, fun ⟨t, ht, h⟩ => by omega⟩
      rw [himg, Finset.sum_image (fun _ _ _ _ h => by omega)]
      have hfac : (∑ t ∈ Finset.range (Kmax - 272), r ^ (t + 272)) =
          r ^ 272 * ∑ t ∈ Finset.range (Kmax - 272), r ^ t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by rw [pow_add]; ring
      rw [hfac, geom_sum_eq (by linarith : r ≠ 1) (Kmax - 272)]
      have hr272 : r ^ 272 = (1 / 2 : ℝ) ^ 34 := by
        calc
          r ^ 272 = (r ^ 8) ^ 34 := by rw [← pow_mul]
          _ = (1 / 2 : ℝ) ^ 34 := by rw [hr8]
      have hsub : 0 < 1 - r := by linarith
      have h1m : (r ^ (Kmax - 272) - 1) / (r - 1) = (1 - r ^ (Kmax - 272)) / (1 - r) := by
        field_simp [show r - 1 ≠ 0 by linarith, hsub.ne']; ring
      rw [hr272, h1m]
      have hinv16 : (1 - r ^ (Kmax - 272)) / (1 - r) ≤ 16 := by
        rw [div_le_iff₀ hsub]
        have hpow0 : 0 ≤ r ^ (Kmax - 272) := pow_nonneg hr0.le _
        linarith
      exact mul_le_mul_of_nonneg_left hinv16 (by positivity)
  have hnum : C_conc * ((1 / 2 : ℝ) ^ 34 * 16) ≤ 1 / 2 := by
    dsimp [C_conc]
    norm_num
  exact (mul_le_mul_of_nonneg_left (hle_sum.trans hgeom) (by dsimp [C_conc]; positivity)).trans hnum

private lemma gcd_mul_pow_prime {p x y i j : ℕ} (hp : Nat.Prime p) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) :
    Nat.gcd (x * p ^ i) (y * p ^ j) = Nat.gcd x y * p ^ (min i j) := by
  let m := min i j
  have hi : p ^ i = p ^ (i - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel (min_le_left i j)]
  have hj : p ^ j = p ^ (j - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel (min_le_right i j)]
  rw [hi, hj, ← mul_assoc, ← mul_assoc, Nat.gcd_mul_right]
  congr 1
  rcases le_total i j with hij | hji
  · have h0 : i - m = 0 := by omega
    rw [h0, pow_zero, mul_one, Nat.gcd_comm]
    rw [(hp.coprime_iff_not_dvd.mpr hx).pow_left (j - m) |>.gcd_mul_right_cancel y, Nat.gcd_comm]
  · have h0 : j - m = 0 := by omega
    rw [h0, pow_zero, mul_one]
    exact (hp.coprime_iff_not_dvd.mpr hy).pow_left (i - m) |>.gcd_mul_right_cancel x

private def primesOf (S : Finset ℕ) : Finset ℕ := S.biUnion Nat.primeFactors

private lemma mem_primesOf_prime {S : Finset ℕ} {p : ℕ} (hp : p ∈ primesOf S) : Nat.Prime p := by
  obtain ⟨x, _, hxp⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hxp

private structure GWState (X₀ Y₀ : Finset ℕ) (A₀ B₀ D₀ : ℝ) where
  X : Finset ℕ
  Y : Finset ℕ
  E : Finset (ℕ × ℕ)
  sX : ℕ
  sY : ℕ
  sD : ℕ
  hsX : 0 < sX
  hsY : 0 < sY
  hsD : 0 < sD
  hXne : X.Nonempty
  hYne : Y.Nonempty
  hXpos : ∀ x ∈ X, 0 < x
  hYpos : ∀ y ∈ Y, 0 < y
  hEne : E.Nonempty
  hEsub : E ⊆ X ×ˢ Y
  hXrng : ∀ x ∈ X, A₀ / sX ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * (A₀ / sX)
  hYrng : ∀ y ∈ Y, B₀ / sY ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * (B₀ / sY)
  hEgcd : ∀ xy ∈ E, D₀ / sD < (Nat.gcd xy.1 xy.2 : ℝ)
  hYmap : ∀ y ∈ Y, y * sY ∈ Y₀
  hXcard : X.card ≤ X₀.card
  hYcard : Y.card ≤ Y₀.card

private def smallPrimes {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ} (st : GWState X₀ Y₀ A₀ B₀ D₀) : ℕ :=
  ((primesOf (st.X ∪ st.Y)).filter (· ≤ p0)).card

private noncomputable def F_val {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ} (q σ : ℝ)
    (st : GWState X₀ Y₀ A₀ B₀ D₀) : ℝ :=
  let a : ℝ := st.X.card
  let b : ℝ := st.Y.card
  let ρ : ℝ := (st.E.card : ℝ) / (a * b)
  let A : ℝ := A₀ / st.sX
  let B : ℝ := B₀ / st.sY
  let D : ℝ := D₀ / st.sD
  let z : ℝ := (a * b) / ((X₀.card : ℝ) * Y₀.card)
  ρ ^ q * a * b * (D ^ 2 / (A * B)) * z ^ σ * ((1000 : ℝ)⁻¹) ^ (smallPrimes st)

private def stepGW {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ} (st : GWState X₀ Y₀ A₀ B₀ D₀)
    (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty) :
    GWState X₀ Y₀ A₀ B₀ D₀ :=
  let hprime : Nat.Prime p := mem_primesOf_prime hp
  let Xi := st.X.filter (fun x => x.factorization p = i)
  let Yj := st.Y.filter (fun y => y.factorization p = j)
  let Eij := st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)
  have hp_pos : 0 < p := hprime.pos
  have hpi_pos : 0 < p ^ i := pow_pos hp_pos i
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos j
  have hpmin_pos : 0 < p ^ (min i j) := pow_pos hp_pos _
  have hXne' : Xi.Nonempty := by
    obtain ⟨xy, hxy⟩ := hEne
    have h1 := (Finset.mem_filter.mp hxy).1
    have h2 := (Finset.mem_filter.mp hxy).2
    exact ⟨xy.1, Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (st.hEsub h1)).1, h2.1⟩⟩
  have hYne' : Yj.Nonempty := by
    obtain ⟨xy, hxy⟩ := hEne
    have h1 := (Finset.mem_filter.mp hxy).1
    have h2 := (Finset.mem_filter.mp hxy).2
    exact ⟨xy.2, Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (st.hEsub h1)).2, h2.2⟩⟩
  have hdivX : ∀ x ∈ Xi, p ^ i ∣ x := fun x hx => by
    have := (Finset.mem_filter.mp hx).2
    rw [← this]; exact Nat.ordProj_dvd x p
  have hdivY : ∀ y ∈ Yj, p ^ j ∣ y := fun y hy => by
    have := (Finset.mem_filter.mp hy).2
    rw [← this]; exact Nat.ordProj_dvd y p
  { X := Xi.image (· / p ^ i)
    Y := Yj.image (· / p ^ j)
    E := Eij.image (fun xy => (xy.1 / p ^ i, xy.2 / p ^ j))
    sX := st.sX * p ^ i
    sY := st.sY * p ^ j
    sD := st.sD * p ^ (min i j)
    hsX := Nat.mul_pos st.hsX hpi_pos
    hsY := Nat.mul_pos st.hsY hpj_pos
    hsD := Nat.mul_pos st.hsD hpmin_pos
    hXne := hXne'.image _
    hYne := hYne'.image _
    hXpos := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
      have hx_pos := st.hXpos x (Finset.mem_filter.mp hx).1
      have hmul := Nat.div_mul_cancel (hdivX x hx)
      by_cases h0 : x / p ^ i = 0
      · rw [h0, zero_mul] at hmul; omega
      · exact Nat.pos_of_ne_zero h0
    hYpos := fun y' hy' => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
      have hy_pos := st.hYpos y (Finset.mem_filter.mp hy).1
      have hmul := Nat.div_mul_cancel (hdivY y hy)
      by_cases h0 : y / p ^ j = 0
      · rw [h0, zero_mul] at hmul; omega
      · exact Nat.pos_of_ne_zero h0
    hEne := hEne.image _
    hEsub := fun xy' hxy' => by
      obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hxy'
      have h1 := (Finset.mem_filter.mp hxy).1
      have h2 := (Finset.mem_filter.mp hxy).2
      have hmem := Finset.mem_product.mp (st.hEsub h1)
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hmem.1, h2.1⟩),
         Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hmem.2, h2.2⟩)⟩
    hXrng := fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
      have hxr := st.hXrng x (Finset.mem_filter.mp hx).1
      have hmul : ((x / p ^ i : ℕ) : ℝ) * (p ^ i : ℝ) = (x : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (hdivX x hx)
      have hpiR : (0 : ℝ) < p ^ i := by positivity
      have hsXR : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
      push_cast
      rw [← div_div]
      constructor
      · rw [div_le_iff₀ hpiR]; linarith [hmul, hxr.1]
      · rw [← mul_div_assoc, le_div_iff₀ hpiR]; linarith [hmul, hxr.2]
    hYrng := fun y' hy' => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
      have hyr := st.hYrng y (Finset.mem_filter.mp hy).1
      have hmul : ((y / p ^ j : ℕ) : ℝ) * (p ^ j : ℝ) = (y : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (hdivY y hy)
      have hpjR : (0 : ℝ) < p ^ j := by positivity
      push_cast
      rw [← div_div]
      constructor
      · rw [div_le_iff₀ hpjR]; linarith [hmul, hyr.1]
      · rw [← mul_div_assoc, le_div_iff₀ hpjR]; linarith [hmul, hyr.2]
    hEgcd := fun xy' hxy' => by
      obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hxy'
      have h1 := (Finset.mem_filter.mp hxy).1
      have h2 := (Finset.mem_filter.mp hxy).2
      have hmem := Finset.mem_product.mp (st.hEsub h1)
      have hdx := hdivX xy.1 (Finset.mem_filter.mpr ⟨hmem.1, h2.1⟩)
      have hdy := hdivY xy.2 (Finset.mem_filter.mpr ⟨hmem.2, h2.2⟩)
      have hnx : ¬ p ∣ xy.1 / p ^ i := by
        intro hd
        have hxpos := st.hXpos xy.1 hmem.1
        have hmul := Nat.div_mul_cancel hdx
        have hdvd : p ^ (i + 1) ∣ xy.1 := by
          obtain ⟨k, hk⟩ := hd
          refine ⟨k, ?_⟩
          rw [← hmul, hk, pow_succ']; ring
        have hle := Nat.Prime.pow_dvd_iff_le_factorization hprime hxpos.ne' |>.mp hdvd
        omega
      have hny : ¬ p ∣ xy.2 / p ^ j := by
        intro hd
        have hypos := st.hYpos xy.2 hmem.2
        have hmul := Nat.div_mul_cancel hdy
        have hdvd : p ^ (j + 1) ∣ xy.2 := by
          obtain ⟨k, hk⟩ := hd
          refine ⟨k, ?_⟩
          rw [← hmul, hk, pow_succ']; ring
        have hle := Nat.Prime.pow_dvd_iff_le_factorization hprime hypos.ne' |>.mp hdvd
        omega
      have hgcd_eq : Nat.gcd xy.1 xy.2 = Nat.gcd (xy.1 / p ^ i) (xy.2 / p ^ j) * p ^ min i j := by
        nth_rw 1 [← Nat.div_mul_cancel hdx]
        nth_rw 1 [← Nat.div_mul_cancel hdy]
        exact gcd_mul_pow_prime hprime hnx hny
      have hg := st.hEgcd xy h1
      rw [hgcd_eq] at hg
      have hpminR : (0 : ℝ) < (p : ℝ) ^ min i j := by positivity
      push_cast
      rw [← div_div, div_lt_iff₀ hpminR]
      exact_mod_cast hg
    hYmap := fun y' hy' => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
      have hyS := (Finset.mem_filter.mp hy).1
      have hdy := hdivY y hy
      have : (y / p ^ j) * (st.sY * p ^ j) = y * st.sY := by
        calc
          (y / p ^ j) * (st.sY * p ^ j) = ((y / p ^ j) * p ^ j) * st.sY := by ring
          _ = y * st.sY := by rw [Nat.div_mul_cancel hdy]
      rw [this]
      exact st.hYmap y hyS
    hXcard := by
      have hinj : Set.InjOn (· / p ^ i) Xi := fun x₁ hx₁ x₂ hx₂ heq => by
        have h1 := Nat.div_mul_cancel (hdivX x₁ hx₁)
        have h2 := Nat.div_mul_cancel (hdivX x₂ hx₂)
        dsimp at heq
        rw [← h1, ← h2, heq]
      rw [Finset.card_image_of_injOn hinj]
      exact (Finset.card_filter_le _ _).trans st.hXcard
    hYcard := by
      have hinj : Set.InjOn (· / p ^ j) Yj := fun y₁ hy₁ y₂ hy₂ heq => by
        have h1 := Nat.div_mul_cancel (hdivY y₁ hy₁)
        have h2 := Nat.div_mul_cancel (hdivY y₂ hy₂)
        dsimp at heq
        rw [← h1, ← h2, heq]
      rw [Finset.card_image_of_injOn hinj]
      exact (Finset.card_filter_le _ _).trans st.hYcard }

private lemma stepGW_primes_subset {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (st : GWState X₀ Y₀ A₀ B₀ D₀) (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty) :
    primesOf ((stepGW st p i j hp hEne).X ∪ (stepGW st p i j hp hEne).Y) ⊆
      (primesOf (st.X ∪ st.Y)).erase p := by
  have hprime := mem_primesOf_prime hp
  intro q hq
  obtain ⟨z', hz', hqz⟩ := Finset.mem_biUnion.mp hq
  have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors hqz
  have hqdvd : q ∣ z' := Nat.dvd_of_mem_primeFactors hqz
  rcases Finset.mem_union.mp hz' with hx' | hy'
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    have hx_mem := (Finset.mem_filter.mp hx).1
    have hxi := (Finset.mem_filter.mp hx).2
    have hdx : p ^ i ∣ x := by rw [← hxi]; exact Nat.ordProj_dvd x p
    have hnx : ¬ p ∣ x / p ^ i := by
      intro hd
      have hxpos := st.hXpos x hx_mem
      have hmul := Nat.div_mul_cancel hdx
      have hdvd : p ^ (i + 1) ∣ x := by
        obtain ⟨k, hk⟩ := hd; refine ⟨k, ?_⟩; rw [← hmul, hk, pow_succ']; ring
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization hprime hxpos.ne').mp hdvd
      omega
    have hqp_ne : q ≠ p := fun heq => hnx (heq ▸ hqdvd)
    have hqx : q ∣ x := hqdvd.trans (Nat.div_dvd_of_dvd hdx)
    refine Finset.mem_erase.mpr ⟨hqp_ne, Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left _ hx_mem, ?_⟩⟩
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqx, (st.hXpos x hx_mem).ne'⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    have hy_mem := (Finset.mem_filter.mp hy).1
    have hyj := (Finset.mem_filter.mp hy).2
    have hdy : p ^ j ∣ y := by rw [← hyj]; exact Nat.ordProj_dvd y p
    have hny : ¬ p ∣ y / p ^ j := by
      intro hd
      have hypos := st.hYpos y hy_mem
      have hmul := Nat.div_mul_cancel hdy
      have hdvd : p ^ (j + 1) ∣ y := by
        obtain ⟨k, hk⟩ := hd; refine ⟨k, ?_⟩; rw [← hmul, hk, pow_succ']; ring
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization hprime hypos.ne').mp hdvd
      omega
    have hqp_ne : q ≠ p := fun heq => hny (heq ▸ hqdvd)
    have hqy : q ∣ y := hqdvd.trans (Nat.div_dvd_of_dvd hdy)
    refine Finset.mem_erase.mpr ⟨hqp_ne, Finset.mem_biUnion.mpr ⟨y, Finset.mem_union_right _ hy_mem, ?_⟩⟩
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqy, (st.hYpos y hy_mem).ne'⟩

private lemma F_val_pos {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    (q σ : ℝ) (st : GWState X₀ Y₀ A₀ B₀ D₀) : 0 < F_val q σ st := by
  unfold F_val
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hX0' : (0 : ℝ) < X₀.card := by exact_mod_cast hX0
  have hY0' : (0 : ℝ) < Y₀.card := by exact_mod_cast hY0
  have hsX : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
  have hsY : (0 : ℝ) < st.sY := by exact_mod_cast st.hsY
  have hsD : (0 : ℝ) < st.sD := by exact_mod_cast st.hsD
  have hρ : 0 < (st.E.card : ℝ) / (st.X.card * st.Y.card) := by positivity
  have hz : 0 < (st.X.card : ℝ) * st.Y.card / (X₀.card * Y₀.card) := by positivity
  have hA : 0 < A₀ / st.sX := by positivity
  have hB : 0 < B₀ / st.sY := by positivity
  have hD : 0 < D₀ / st.sD := by positivity
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hρ _) ha) hb)
    (by positivity)) (Real.rpow_pos_of_pos hz _)) (pow_pos (by norm_num) _)

private lemma stepGW_card_X {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (st : GWState X₀ Y₀ A₀ B₀ D₀) (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty) :
    (stepGW st p i j hp hEne).X.card = (st.X.filter (fun x => x.factorization p = i)).card := by
  dsimp [stepGW]
  refine Finset.card_image_of_injOn fun x₁ hx₁ x₂ hx₂ heq => ?_
  have hd1 : p ^ i ∣ x₁ := by rw [← (Finset.mem_filter.mp hx₁).2]; exact Nat.ordProj_dvd x₁ p
  have hd2 : p ^ i ∣ x₂ := by rw [← (Finset.mem_filter.mp hx₂).2]; exact Nat.ordProj_dvd x₂ p
  rw [← Nat.div_mul_cancel hd1, ← Nat.div_mul_cancel hd2, heq]

private lemma stepGW_card_Y {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (st : GWState X₀ Y₀ A₀ B₀ D₀) (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty) :
    (stepGW st p i j hp hEne).Y.card = (st.Y.filter (fun y => y.factorization p = j)).card := by
  dsimp [stepGW]
  refine Finset.card_image_of_injOn fun y₁ hy₁ y₂ hy₂ heq => ?_
  have hd1 : p ^ j ∣ y₁ := by rw [← (Finset.mem_filter.mp hy₁).2]; exact Nat.ordProj_dvd y₁ p
  have hd2 : p ^ j ∣ y₂ := by rw [← (Finset.mem_filter.mp hy₂).2]; exact Nat.ordProj_dvd y₂ p
  rw [← Nat.div_mul_cancel hd1, ← Nat.div_mul_cancel hd2, heq]

private lemma stepGW_card_E {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (st : GWState X₀ Y₀ A₀ B₀ D₀) (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty) :
    (stepGW st p i j hp hEne).E.card =
      (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).card := by
  dsimp [stepGW]
  refine Finset.card_image_of_injOn fun xy₁ hxy₁ xy₂ hxy₂ heq => ?_
  have h1 := (Finset.mem_filter.mp hxy₁).2
  have h2 := (Finset.mem_filter.mp hxy₂).2
  have hd1x : p ^ i ∣ xy₁.1 := by rw [← h1.1]; exact Nat.ordProj_dvd _ p
  have hd1y : p ^ j ∣ xy₁.2 := by rw [← h1.2]; exact Nat.ordProj_dvd _ p
  have hd2x : p ^ i ∣ xy₂.1 := by rw [← h2.1]; exact Nat.ordProj_dvd _ p
  have hd2y : p ^ j ∣ xy₂.2 := by rw [← h2.2]; exact Nat.ordProj_dvd _ p
  have hx : xy₁.1 / p ^ i = xy₂.1 / p ^ i := congrArg Prod.fst heq
  have hy : xy₁.2 / p ^ j = xy₂.2 / p ^ j := congrArg Prod.snd heq
  ext
  · rw [← Nat.div_mul_cancel hd1x, ← Nat.div_mul_cancel hd2x, hx]
  · rw [← Nat.div_mul_cancel hd1y, ← Nat.div_mul_cancel hd2y, hy]

private lemma real_pow_abs_diff {p : ℝ} (hp : p ≠ 0) (i j : ℕ) :
    p ^ i * p ^ j / (p ^ min i j) ^ 2 = p ^ Int.natAbs ((i : ℤ) - j) := by
  rcases le_total i j with hij | hji
  · rw [min_eq_left hij, show Int.natAbs ((i : ℤ) - j) = j - i by omega]
    have hj : p ^ j = p ^ i * p ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj]
    field_simp [pow_ne_zero i hp]
  · rw [min_eq_right hji, show Int.natAbs ((i : ℤ) - j) = i - j by omega]
    have hi : p ^ i = p ^ j * p ^ (i - j) := by rw [← pow_add]; congr 1; omega
    rw [hi]
    field_simp [pow_ne_zero j hp]

private lemma F_val_stepGW_core {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    {q σ : ℝ} (hq0 : 0 < q) (hσ0 : 0 ≤ σ) (hqσ : q / (1 + σ) = 5 / 2)
    (st st' : GWState X₀ Y₀ A₀ B₀ D₀) (p : ℝ) (hp_pos : 0 < p) (i j t : ℕ)
    (αi βj μij : ℝ) (hαi : 0 < αi) (hβj : 0 < βj) (hμij : 0 < μij)
    (hXeq : (st'.X.card : ℝ) = αi * st.X.card)
    (hYeq : (st'.Y.card : ℝ) = βj * st.Y.card)
    (hEeq : (st'.E.card : ℝ) = μij * st.E.card)
    (hsX' : (st'.sX : ℝ) = (st.sX : ℝ) * p ^ i)
    (hsY' : (st'.sY : ℝ) = (st.sY : ℝ) * p ^ j)
    (hsD' : (st'.sD : ℝ) = (st.sD : ℝ) * p ^ min i j)
    (hsm : ((1000 : ℝ)⁻¹) ^ smallPrimes st * (1000 : ℝ) ^ t ≤
      ((1000 : ℝ)⁻¹) ^ smallPrimes st')
    (hloc : F_val q σ st' ≤ F_val q σ st) :
    μij ≤ (1000 : ℝ) ^ (-(t : ℝ) / q) *
      (p ^ (-(1 : ℝ) / q)) ^ Int.natAbs ((i : ℤ) - j) * (αi * βj) ^ ((3 : ℝ) / 5) := by
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hX0R : (0 : ℝ) < X₀.card := by exact_mod_cast hX0
  have hY0R : (0 : ℝ) < Y₀.card := by exact_mod_cast hY0
  have hsX : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
  have hsY : (0 : ℝ) < st.sY := by exact_mod_cast st.hsY
  have hsD : (0 : ℝ) < st.sD := by exact_mod_cast st.hsD
  have hαβ : 0 < αi * βj := mul_pos hαi hβj
  let ρ : ℝ := (st.E.card : ℝ) / ((st.X.card : ℝ) * (st.Y.card : ℝ))
  let A : ℝ := A₀ / st.sX
  let B : ℝ := B₀ / st.sY
  let D : ℝ := D₀ / st.sD
  let z : ℝ := ((st.X.card : ℝ) * (st.Y.card : ℝ)) / ((X₀.card : ℝ) * (Y₀.card : ℝ))
  have hρ0 : 0 < ρ := div_pos he (mul_pos ha hb)
  have hA0' : 0 < A := div_pos hA0 hsX
  have hB0' : 0 < B := div_pos hB0 hsY
  have hD0' : 0 < D := div_pos hD0 hsD
  have hz0 : 0 < z := div_pos (mul_pos ha hb) (mul_pos hX0R hY0R)
  have hρ' : (st'.E.card : ℝ) / ((st'.X.card : ℝ) * (st'.Y.card : ℝ)) =
      (μij / (αi * βj)) * ρ := by
    rw [hEeq, hXeq, hYeq]; dsimp [ρ]; field_simp [ha.ne', hb.ne', hαi.ne', hβj.ne']
  have hz' : ((st'.X.card : ℝ) * (st'.Y.card : ℝ)) / ((X₀.card : ℝ) * (Y₀.card : ℝ)) =
      (αi * βj) * z := by
    rw [hXeq, hYeq]; dsimp [z]; ring
  have hDAB' : (D₀ / (st'.sD : ℝ)) ^ 2 / ((A₀ / (st'.sX : ℝ)) * (B₀ / (st'.sY : ℝ))) =
      (D ^ 2 / (A * B)) * p ^ Int.natAbs ((i : ℤ) - j) := by
    rw [hsX', hsY', hsD', ← real_pow_abs_diff hp_pos.ne' i j]
    dsimp [A, B, D]
    have hpi0 : p ^ i ≠ 0 := pow_ne_zero i hp_pos.ne'
    have hpj0 : p ^ j ≠ 0 := pow_ne_zero j hp_pos.ne'
    have hpm0 : p ^ min i j ≠ 0 := pow_ne_zero _ hp_pos.ne'
    field_simp [hsX.ne', hsY.ne', hsD.ne', hpi0, hpj0, hpm0]
  have hF'_eq : F_val q σ st' =
      (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
        (μij ^ q * (αi * βj) ^ (1 + σ - q) * p ^ Int.natAbs ((i : ℤ) - j)) *
        ((1000 : ℝ)⁻¹) ^ smallPrimes st' := by
    unfold F_val; dsimp only
    rw [hρ', hz', hXeq, hYeq, hDAB']
    have hpow_ρ : ((μij / (αi * βj)) * ρ) ^ q = μij ^ q * (αi * βj) ^ (-q) * ρ ^ q := by
      rw [Real.mul_rpow (div_pos hμij hαβ).le hρ0.le,
        Real.div_rpow hμij.le hαβ.le, div_eq_mul_inv, Real.rpow_neg hαβ.le]
    have hpow_z : ((αi * βj) * z) ^ σ = (αi * βj) ^ σ * z ^ σ :=
      Real.mul_rpow hαβ.le hz0.le
    have hpow_αβ : (αi * βj) ^ (-q) * (αi * βj) * (αi * βj) ^ σ = (αi * βj) ^ (1 + σ - q) := by
      nth_rw 2 [← Real.rpow_one (αi * βj)]
      rw [← Real.rpow_add hαβ, ← Real.rpow_add hαβ]
      congr 1; ring
    rw [hpow_ρ, hpow_z]
    calc
      μij ^ q * (αi * βj) ^ (-q) * ρ ^ q * (αi * st.X.card) * (βj * st.Y.card) *
          (D ^ 2 / (A * B) * p ^ Int.natAbs ((i : ℤ) - j)) *
          ((αi * βj) ^ σ * z ^ σ) * ((1000 : ℝ)⁻¹) ^ smallPrimes st'
          = (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
              (μij ^ q * ((αi * βj) ^ (-q) * (αi * βj) * (αi * βj) ^ σ) *
                p ^ Int.natAbs ((i : ℤ) - j)) *
              ((1000 : ℝ)⁻¹) ^ smallPrimes st' := by ring
      _ = _ := by rw [hpow_αβ]
  have hqexp : (1 + σ - q) + ((3 : ℝ) / 5) * q = 0 := by
    have h1σ : 0 < 1 + σ := by linarith
    have hq_eq : q = (5 / 2 : ℝ) * (1 + σ) := by
      rw [← hqσ, div_mul_cancel₀ _ h1σ.ne']
    linarith
  have hαβ_pos_pow : 0 < (αi * βj) ^ (((3 : ℝ) / 5) * q) := Real.rpow_pos_of_pos hαβ _
  have hcancel : (αi * βj) ^ (1 + σ - q) * (αi * βj) ^ (((3 : ℝ) / 5) * q) = 1 := by
    rw [← Real.rpow_add hαβ, hqexp, Real.rpow_zero]
  have hF_pos := F_val_pos hX0 hY0 hA0 hB0 hD0 q σ st
  have hF_expand : F_val q σ st =
      (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
        ((1000 : ℝ)⁻¹) ^ smallPrimes st := rfl
  have hstep_base : F_val q σ st * (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j) * (1000 : ℝ) ^ t) ≤
      F_val q σ st' * (αi * βj) ^ (((3 : ℝ) / 5) * q) := by
    have hnonneg : 0 ≤ (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
        (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j)) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hρ0.le _) ha.le) hb.le)
        (div_nonneg (pow_nonneg hD0'.le 2) (mul_nonneg hA0'.le hB0'.le))) (Real.rpow_nonneg hz0.le _))
        (mul_nonneg (Real.rpow_nonneg hμij.le _) (pow_nonneg hp_pos.le _))
    have h1 := mul_le_mul_of_nonneg_left hsm hnonneg
    calc
      F_val q σ st * (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j) * (1000 : ℝ) ^ t)
          = (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
              (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j)) *
              (((1000 : ℝ)⁻¹) ^ smallPrimes st * (1000 : ℝ) ^ t) := by rw [hF_expand]; ring
      _ ≤ (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
              (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j)) *
              ((1000 : ℝ)⁻¹) ^ smallPrimes st' := h1
      _ = (ρ ^ q * st.X.card * st.Y.card * (D ^ 2 / (A * B)) * z ^ σ) *
              (μij ^ q * ((αi * βj) ^ (1 + σ - q) * (αi * βj) ^ (((3 : ℝ) / 5) * q)) *
                p ^ Int.natAbs ((i : ℤ) - j)) *
              ((1000 : ℝ)⁻¹) ^ smallPrimes st' := by rw [hcancel, mul_one]
      _ = F_val q σ st' * (αi * βj) ^ (((3 : ℝ) / 5) * q) := by rw [hF'_eq]; ring
  have hstep_le : F_val q σ st * (μij ^ q * p ^ Int.natAbs ((i : ℤ) - j) * (1000 : ℝ) ^ t) ≤
      F_val q σ st * (αi * βj) ^ (((3 : ℝ) / 5) * q) :=
    hstep_base.trans (mul_le_mul_of_nonneg_right hloc hαβ_pos_pow.le)
  have hqpow : μij ^ q * p ^ Int.natAbs ((i : ℤ) - j) * (1000 : ℝ) ^ t ≤
      (αi * βj) ^ (((3 : ℝ) / 5) * q) := le_of_mul_le_mul_left hstep_le hF_pos
  let kexp := Int.natAbs ((i : ℤ) - j)
  have hqpow' : μij ^ q ≤
      (1000 : ℝ) ^ (-(t : ℝ)) * p ^ (-(kexp : ℝ)) * (αi * βj) ^ (((3 : ℝ) / 5) * q) := by
    have h1000 : (0 : ℝ) < (1000 : ℝ) ^ t := pow_pos (by norm_num) t
    have hpk : (0 : ℝ) < p ^ kexp := pow_pos hp_pos kexp
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast,
      Real.rpow_neg hp_pos.le, Real.rpow_natCast]
    calc
      μij ^ q = (μij ^ q * p ^ kexp * (1000 : ℝ) ^ t) * ((1000 : ℝ) ^ t)⁻¹ * (p ^ kexp)⁻¹ := by
        field_simp [h1000.ne', hpk.ne']
      _ ≤ (αi * βj) ^ (((3 : ℝ) / 5) * q) * ((1000 : ℝ) ^ t)⁻¹ * (p ^ kexp)⁻¹ := by
        gcongr
      _ = ((1000 : ℝ) ^ t)⁻¹ * (p ^ kexp)⁻¹ * (αi * βj) ^ (((3 : ℝ) / 5) * q) := by ring
  have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg hμij.le q) hqpow' (div_nonneg zero_le_one hq0.le)
  have hLHS : (μij ^ q) ^ ((1 : ℝ) / q) = μij := by
    rw [← Real.rpow_mul hμij.le, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have hRHS : ((1000 : ℝ) ^ (-(t : ℝ)) * p ^ (-(kexp : ℝ)) * (αi * βj) ^ (((3 : ℝ) / 5) * q)) ^
      ((1 : ℝ) / q) =
      (1000 : ℝ) ^ (-(t : ℝ) / q) * (p ^ (-(1 : ℝ) / q)) ^ kexp *
        (αi * βj) ^ ((3 : ℝ) / 5) := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hp_pos.le _))
        (Real.rpow_nonneg hαβ.le _),
      Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hp_pos.le _)]
    have h1 : ((1000 : ℝ) ^ (-(t : ℝ))) ^ ((1 : ℝ) / q) = (1000 : ℝ) ^ (-(t : ℝ) / q) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    have h2 : (p ^ (-(kexp : ℝ))) ^ ((1 : ℝ) / q) = (p ^ (-(1 : ℝ) / q)) ^ kexp := by
      rw [← Real.rpow_mul hp_pos.le, ← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
      congr 1; ring
    have h3 : ((αi * βj) ^ (((3 : ℝ) / 5) * q)) ^ ((1 : ℝ) / q) = (αi * βj) ^ ((3 : ℝ) / 5) := by
      rw [← Real.rpow_mul hαβ.le]; congr 1; field_simp [hq0.ne']
    rw [h1, h2, h3]
  rw [hLHS, hRHS] at hrpow
  exact hrpow

private lemma F_val_stepGW_bound {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    {q σ : ℝ} (hq0 : 0 < q) (hσ0 : 0 ≤ σ) (hqσ : q / (1 + σ) = 5 / 2)
    (st : GWState X₀ Y₀ A₀ B₀ D₀) (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
    (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty)
    (hloc : F_val q σ (stepGW st p i j hp hEne) ≤ F_val q σ st) :
    let Xi := st.X.filter (fun x => x.factorization p = i)
    let Yj := st.Y.filter (fun y => y.factorization p = j)
    let Eij := st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)
    let t : ℕ := if p ≤ p0 then 1 else 0
    (Eij.card : ℝ) / (st.E.card : ℝ) ≤
      (1000 : ℝ) ^ (-(t : ℝ) / q) *
        ((p : ℝ) ^ (-(1 : ℝ) / q)) ^ Int.natAbs ((i : ℤ) - j) *
        (((Xi.card : ℝ) / (st.X.card : ℝ)) * ((Yj.card : ℝ) / (st.Y.card : ℝ))) ^ ((3 : ℝ) / 5) := by
  intro Xi Yj Eij t
  have hprime := mem_primesOf_prime hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hXne' : Xi.Nonempty := by
    obtain ⟨xy, hxy⟩ := hEne
    exact ⟨xy.1, Finset.mem_filter.mpr
      ⟨(Finset.mem_product.mp (st.hEsub (Finset.mem_filter.mp hxy).1)).1,
       (Finset.mem_filter.mp hxy).2.1⟩⟩
  have hYne' : Yj.Nonempty := by
    obtain ⟨xy, hxy⟩ := hEne
    exact ⟨xy.2, Finset.mem_filter.mpr
      ⟨(Finset.mem_product.mp (st.hEsub (Finset.mem_filter.mp hxy).1)).2,
       (Finset.mem_filter.mp hxy).2.2⟩⟩
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have ha' : (0 : ℝ) < Xi.card := by exact_mod_cast hXne'.card_pos
  have hb' : (0 : ℝ) < Yj.card := by exact_mod_cast hYne'.card_pos
  have he' : (0 : ℝ) < Eij.card := by exact_mod_cast hEne.card_pos
  let αi : ℝ := (Xi.card : ℝ) / (st.X.card : ℝ)
  let βj : ℝ := (Yj.card : ℝ) / (st.Y.card : ℝ)
  let μij : ℝ := (Eij.card : ℝ) / (st.E.card : ℝ)
  have ht_le : smallPrimes (stepGW st p i j hp hEne) + t ≤ smallPrimes st := by
    have hps := stepGW_primes_subset st p i j hp hEne
    by_cases hple : p ≤ p0
    · have ht1 : t = 1 := if_pos hple
      rw [ht1]
      have hsub : (primesOf ((stepGW st p i j hp hEne).X ∪ (stepGW st p i j hp hEne).Y)).filter (· ≤ p0) ⊆
          ((primesOf (st.X ∪ st.Y)).filter (· ≤ p0)).erase p := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hq' := Finset.mem_erase.mp (hps hq.1)
        exact Finset.mem_erase.mpr ⟨hq'.1, Finset.mem_filter.mpr ⟨hq'.2, hq.2⟩⟩
      have hmem : p ∈ (primesOf (st.X ∪ st.Y)).filter (· ≤ p0) := Finset.mem_filter.mpr ⟨hp, hple⟩
      have hlt : smallPrimes (stepGW st p i j hp hEne) < smallPrimes st := by
        calc
          smallPrimes (stepGW st p i j hp hEne) ≤
              (((primesOf (st.X ∪ st.Y)).filter (· ≤ p0)).erase p).card :=
            Finset.card_le_card hsub
          _ < smallPrimes st := Finset.card_erase_lt_of_mem hmem
      omega
    · have ht0 : t = 0 := if_neg hple
      rw [ht0, add_zero]
      have hsub : (primesOf ((stepGW st p i j hp hEne).X ∪ (stepGW st p i j hp hEne).Y)).filter (· ≤ p0) ⊆
          (primesOf (st.X ∪ st.Y)).filter (· ≤ p0) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hps hq.1)).2, hq.2⟩
      exact Finset.card_le_card hsub
  have hsm : ((1000 : ℝ)⁻¹) ^ smallPrimes st * (1000 : ℝ) ^ t ≤
      ((1000 : ℝ)⁻¹) ^ smallPrimes (stepGW st p i j hp hEne) := by
    have h1 : ((1000 : ℝ)⁻¹) ^ smallPrimes st ≤
        ((1000 : ℝ)⁻¹) ^ (smallPrimes (stepGW st p i j hp hEne) + t) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) ht_le
    have h2 : ((1000 : ℝ)⁻¹) ^ (smallPrimes (stepGW st p i j hp hEne) + t) * (1000 : ℝ) ^ t =
        ((1000 : ℝ)⁻¹) ^ smallPrimes (stepGW st p i j hp hEne) := by
      rw [pow_add, mul_assoc, ← mul_pow]; norm_num
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1000) t]
  exact F_val_stepGW_core hX0 hY0 hA0 hB0 hD0 hq0 hσ0 hqσ st (stepGW st p i j hp hEne) p hp_pos i j t
    αi βj μij (div_pos ha' ha) (div_pos hb' hb) (div_pos he' he)
    (by rw [stepGW_card_X]; dsimp [αi, Xi]; field_simp [ha.ne'])
    (by rw [stepGW_card_Y]; dsimp [βj, Yj]; field_simp [hb.ne'])
    (by rw [stepGW_card_E]; dsimp [μij, Eij]; field_simp [he.ne'])
    (by dsimp [stepGW]; push_cast; rfl)
    (by dsimp [stepGW]; push_cast; rfl)
    (by dsimp [stepGW]; push_cast; rfl)
    hsm hloc

private lemma gw_local_maximizer {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (q σ : ℝ) :
    ∀ k : ℕ, ∀ st₀ : GWState X₀ Y₀ A₀ B₀ D₀, (primesOf (st₀.X ∪ st₀.Y)).card ≤ k →
      ∃ st : GWState X₀ Y₀ A₀ B₀ D₀,
        F_val q σ st₀ ≤ F_val q σ st ∧
        ∀ (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
          (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty),
          F_val q σ (stepGW st p i j hp hEne) ≤ F_val q σ st := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro st₀ hk
    by_cases hmax : ∀ (p i j : ℕ) (hp : p ∈ primesOf (st₀.X ∪ st₀.Y))
        (hEne : (st₀.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty),
        F_val q σ (stepGW st₀ p i j hp hEne) ≤ F_val q σ st₀
    · exact ⟨st₀, le_rfl, hmax⟩
    · push Not at hmax
      obtain ⟨p, i, j, hp, hEne, hlt⟩ := hmax
      let st₁ := stepGW st₀ p i j hp hEne
      have hcard_lt : (primesOf (st₁.X ∪ st₁.Y)).card < (primesOf (st₀.X ∪ st₀.Y)).card := by
        calc
          (primesOf (st₁.X ∪ st₁.Y)).card ≤ ((primesOf (st₀.X ∪ st₀.Y)).erase p).card :=
            Finset.card_le_card (stepGW_primes_subset st₀ p i j hp hEne)
          _ < (primesOf (st₀.X ∪ st₀.Y)).card := Finset.card_erase_lt_of_mem hp
      have hcard_le : (primesOf (st₁.X ∪ st₁.Y)).card ≤ (primesOf (st₀.X ∪ st₀.Y)).card - 1 := by
        omega
      obtain ⟨st, hle, hloc⟩ := ih ((primesOf (st₀.X ∪ st₀.Y)).card - 1) (by omega) st₁ hcard_le
      exact ⟨st, (hlt.le.trans hle), hloc⟩

private lemma gw_conc_at_max {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    {q σ : ℝ} (hq_lo : 2 ≤ q) (hq_hi : q ≤ 8 / 3) (hσ0 : 0 ≤ σ) (hqσ : q / (1 + σ) = 5 / 2)
    (st : GWState X₀ Y₀ A₀ B₀ D₀)
    (hloc : ∀ (p i j : ℕ) (hp : p ∈ primesOf (st.X ∪ st.Y))
      (hEne : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty),
      F_val q σ (stepGW st p i j hp hEne) ≤ F_val q σ st) :
    smallPrimes st = 0 ∧
      ∃ N : ℕ, 0 < N ∧ (∀ q', q' ∉ primesOf (st.X ∪ st.Y) → N.factorization q' = 0) ∧
        ∃ E' ⊆ st.E, E'.Nonempty ∧ st.E.card ≤ 2 * E'.card ∧
          ∀ xy ∈ E', ∀ p : ℕ, Nat.Prime p →
            Int.natAbs ((xy.1.factorization p : ℤ) - N.factorization p) +
              Int.natAbs ((xy.2.factorization p : ℤ) - N.factorization p) ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hprime_data : ∀ p ∈ primesOf (st.X ∪ st.Y),
      p0 < p ∧ ∃ k_p : ℕ,
        ((st.E.filter (fun xy =>
          2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - k_p) +
            Int.natAbs ((xy.2.factorization p : ℤ) - k_p))).card : ℝ) / (st.E.card : ℝ) ≤
          C_conc * (p : ℝ) ^ (-(9 : ℝ) / 8) := by
    intro p hp
    have hprime := mem_primesOf_prime hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    let Sp : Finset ℕ := (st.X.image (fun x => x.factorization p)) ∪
      (st.Y.image (fun y => y.factorization p))
    have hSpne : Sp.Nonempty := by
      obtain ⟨x, hx⟩ := st.hXne
      exact ⟨x.factorization p, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)⟩
    let α : ℕ → ℝ := fun i => ((st.X.filter (fun x => x.factorization p = i)).card : ℝ) / (st.X.card : ℝ)
    let β : ℕ → ℝ := fun j => ((st.Y.filter (fun y => y.factorization p = j)).card : ℝ) / (st.Y.card : ℝ)
    let μ : ℕ → ℕ → ℝ := fun i j =>
      ((st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).card : ℝ) / (st.E.card : ℝ)
    have hα0 : ∀ i, 0 ≤ α i := fun i => by positivity
    have hβ0 : ∀ j, 0 ≤ β j := fun j => by positivity
    have hμ0 : ∀ i j, 0 ≤ μ i j := fun i j => by positivity
    have hα1 : ∑ i ∈ Sp, α i = 1 := by
      have hmap : ∀ x ∈ st.X, x.factorization p ∈ Sp := fun x hx =>
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
      have hf := Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ => x.factorization p)
        (f := fun _ => (1 : ℝ)) hmap
      have hcard : (∑ i ∈ Sp, ((st.X.filter (fun x => x.factorization p = i)).card : ℝ)) = st.X.card := by
        simpa using hf
      dsimp [α]
      rw [← Finset.sum_div, hcard, div_self (by exact_mod_cast st.hXne.card_pos.ne')]
    have hβ1 : ∑ j ∈ Sp, β j = 1 := by
      have hmap : ∀ y ∈ st.Y, y.factorization p ∈ Sp := fun y hy =>
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)
      have hf := Finset.sum_fiberwise_of_maps_to (g := fun y : ℕ => y.factorization p)
        (f := fun _ => (1 : ℝ)) hmap
      have hcard : (∑ j ∈ Sp, ((st.Y.filter (fun y => y.factorization p = j)).card : ℝ)) = st.Y.card := by
        simpa using hf
      dsimp [β]
      rw [← Finset.sum_div, hcard, div_self (by exact_mod_cast st.hYne.card_pos.ne')]
    have hμ1 : ∑ i ∈ Sp, ∑ j ∈ Sp, μ i j = 1 := by
      have hmap : ∀ xy ∈ st.E, (xy.1.factorization p, xy.2.factorization p) ∈ Sp ×ˢ Sp := fun xy hxy => by
        have hm := Finset.mem_product.mp (st.hEsub hxy)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1),
           Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)⟩
      have hf := Finset.sum_fiberwise_of_maps_to
        (g := fun xy : ℕ × ℕ => (xy.1.factorization p, xy.2.factorization p))
        (f := fun _ => (1 : ℝ)) hmap
      have hcard : (∑ ij ∈ Sp ×ˢ Sp,
          ((st.E.filter (fun xy => (xy.1.factorization p, xy.2.factorization p) = ij)).card : ℝ)) =
          st.E.card := by
        simpa using hf
      have hprod_sum : (∑ i ∈ Sp, ∑ j ∈ Sp, μ i j) =
          (∑ ij ∈ Sp ×ˢ Sp,
            ((st.E.filter (fun xy => (xy.1.factorization p, xy.2.factorization p) = ij)).card : ℝ)) /
          (st.E.card : ℝ) := by
        rw [Finset.sum_div, ← Finset.sum_product']
        refine Finset.sum_congr rfl fun ij _ => ?_
        dsimp [μ]
        refine congrArg (fun S : Finset (ℕ × ℕ) => (S.card : ℝ) / (st.E.card : ℝ)) ?_
        ext xy; simp [Prod.ext_iff]
      rw [hprod_sum, hcard, div_self (by exact_mod_cast st.hEne.card_pos.ne')]
    let t : ℕ := if p ≤ p0 then 1 else 0
    let c : ℝ := (1000 : ℝ) ^ (-(t : ℝ) / q)
    let lam : ℝ := (p : ℝ) ^ (-(1 : ℝ) / q)
    have hc : 0 < c ∧ c ≤ 1 := by
      refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have ht0 : (0 : ℝ) ≤ t := by positivity
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht0) hq0.le)
    have hlam : 0 < lam ∧ lam ≤ 4 / 5 := by
      refine ⟨Real.rpow_pos_of_pos hp_pos _, ?_⟩
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have h1 : (p : ℝ) ^ (-(1 : ℝ) / q) ≤ (2 : ℝ) ^ (-(1 : ℝ) / q) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (div_nonpos_of_nonpos_of_nonneg (by norm_num) hq0.le)
      have h2 : (2 : ℝ) ^ (-(1 : ℝ) / q) ≤ (2 : ℝ) ^ (-(3 : ℝ) / 8) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hinv : (3 : ℝ) / 8 ≤ 1 / q := by
          rw [div_le_div_iff₀ (by norm_num) hq0]
          linarith
        rw [neg_div, neg_div]
        linarith
      have h3 : (2 : ℝ) ^ (-(3 : ℝ) / 8) ≤ (4 / 5 : ℝ) := by
        refine le_of_pow_le_pow_left₀ (by norm_num : 8 ≠ 0) (by norm_num) ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      exact h1.trans (h2.trans h3)
    have hbound : ∀ i ∈ Sp, ∀ j ∈ Sp,
        μ i j ≤ c * lam ^ Int.natAbs ((i : ℤ) - j) * (α i * β j) ^ ((3 : ℝ) / 5) := by
      intro i _ j _
      by_cases hEij : (st.E.filter (fun xy => xy.1.factorization p = i ∧ xy.2.factorization p = j)).Nonempty
      · exact F_val_stepGW_bound hX0 hY0 hA0 hB0 hD0 hq0 hσ0 hqσ st p i j hp hEij
          (hloc p i j hp hEij)
      · rw [Finset.not_nonempty_iff_eq_empty] at hEij
        have hμ0' : μ i j = 0 := by dsimp [μ]; rw [hEij]; simp
        rw [hμ0']
        exact mul_nonneg (mul_nonneg hc.1.le (pow_nonneg hlam.1.le _))
          (Real.rpow_nonneg (mul_nonneg (hα0 i) (hβ0 j)) _)
    obtain ⟨hc_ge, k_p, _, hconc⟩ := conc_lemma Sp hSpne α β μ c lam hα0 hβ0 hμ0 hα1 hβ1 hμ1 hc hlam hbound
    have hp_gt : p0 < p := by
      by_contra hle
      have hple : p ≤ p0 := Nat.not_lt.mp hle
      have ht1 : (t : ℝ) = 1 := by dsimp [t]; rw [if_pos hple]; norm_num
      have hclt : c < 1 / 9 := by
        dsimp [c]
        rw [ht1]
        have h1 : (1000 : ℝ) ^ (-(1 : ℝ) / q) < (1000 : ℝ) ^ (-(1 : ℝ) / 3) := by
          refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
          rw [neg_div, neg_div, neg_lt_neg_iff, one_div_lt_one_div (by norm_num) hq0]
          linarith
        have h2 : (1000 : ℝ) ^ (-(1 : ℝ) / 3) < (1 / 9 : ℝ) := by
          refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        exact h1.trans h2
      linarith
    refine ⟨hp_gt, k_p, ?_⟩
    have hlam3 : lam ^ 3 ≤ (p : ℝ) ^ (-(9 : ℝ) / 8) := by
      dsimp [lam]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hprime.one_lt.le) ?_
      have hinv : (9 : ℝ) / 8 ≤ 3 / q := by
        rw [div_le_div_iff₀ (by norm_num) hq0]
        linarith
      have hlhs : -(1 : ℝ) / q * (3 : ℕ) = -(3 / q) := by push_cast; ring
      have hrhs : -(9 : ℝ) / 8 = -((9 : ℝ) / 8) := by ring
      rw [hlhs, hrhs]
      linarith
    have hbad_sub : st.E.filter (fun xy =>
        2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - k_p) +
          Int.natAbs ((xy.2.factorization p : ℤ) - k_p)) ⊆
        (Sp ×ˢ Sp).biUnion (fun ij =>
          if 2 ≤ Int.natAbs ((ij.1 : ℤ) - k_p) + Int.natAbs ((ij.2 : ℤ) - k_p) then
            st.E.filter (fun xy => xy.1.factorization p = ij.1 ∧ xy.2.factorization p = ij.2)
          else ∅) := by
      intro xy hxy
      rw [Finset.mem_filter] at hxy
      have hm := Finset.mem_product.mp (st.hEsub hxy.1)
      rw [Finset.mem_biUnion]
      refine ⟨(xy.1.factorization p, xy.2.factorization p), Finset.mem_product.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm.1),
         Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm.2)⟩, ?_⟩
      rw [if_pos hxy.2]
      exact Finset.mem_filter.mpr ⟨hxy.1, rfl, rfl⟩
    have hcard_bad : ((st.E.filter (fun xy =>
        2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - k_p) +
          Int.natAbs ((xy.2.factorization p : ℤ) - k_p))).card : ℝ) / (st.E.card : ℝ) ≤
        ∑ i ∈ Sp, ∑ j ∈ Sp,
          if 2 ≤ Int.natAbs ((i : ℤ) - k_p) + Int.natAbs ((j : ℤ) - k_p) then μ i j else 0 := by
      have he_pos : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
      have h1 := (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
      have h2 : ((∑ ij ∈ Sp ×ˢ Sp,
          (if 2 ≤ Int.natAbs ((ij.1 : ℤ) - k_p) + Int.natAbs ((ij.2 : ℤ) - k_p) then
            st.E.filter (fun xy => xy.1.factorization p = ij.1 ∧ xy.2.factorization p = ij.2)
          else ∅).card : ℕ) : ℝ) / (st.E.card : ℝ) =
          ∑ i ∈ Sp, ∑ j ∈ Sp,
            if 2 ≤ Int.natAbs ((i : ℤ) - k_p) + Int.natAbs ((j : ℤ) - k_p) then μ i j else 0 := by
        rw [← Finset.sum_product']
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun ij _ => ?_
        split_ifs with h <;> simp [μ]
      calc
        ((st.E.filter _).card : ℝ) / (st.E.card : ℝ) ≤ ((∑ ij ∈ Sp ×ˢ Sp, _ : ℕ) : ℝ) / (st.E.card : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast h1) he_pos.le
        _ = _ := h2
    exact hcard_bad.trans (hconc.trans (mul_le_mul_of_nonneg_left hlam3 (by dsimp [C_conc]; positivity)))
  have hsmall0 : smallPrimes st = 0 := by
    unfold smallPrimes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    exact not_le.mpr (hprime_data p hp).1
  refine ⟨hsmall0, ?_⟩
  let P := primesOf (st.X ∪ st.Y)
  let kfn : ℕ → ℕ := fun p => if hp : p ∈ P then (hprime_data p hp).2.choose else 0
  let N : ℕ := ∏ p ∈ P, p ^ kfn p
  have hNpos : 0 < N := Finset.prod_pos fun p hp => pow_pos (mem_primesOf_prime hp).pos _
  have hNfact : ∀ q', N.factorization q' = kfn q' := by
    intro q'
    have hprod : ∀ Q : Finset ℕ, (∀ p ∈ Q, Nat.Prime p) →
        (∏ p ∈ Q, p ^ kfn p).factorization q' = if q' ∈ Q then kfn q' else 0 := by
      intro Q hQ
      induction Q using Finset.induction with
      | empty => simp
      | @insert p Q' hp ih =>
        have hpp := hQ p (Finset.mem_insert_self _ _)
        have hQ' : ∀ r ∈ Q', Nat.Prime r := fun r hr => hQ r (Finset.mem_insert_of_mem hr)
        have hnz1 : p ^ kfn p ≠ 0 := pow_ne_zero _ hpp.ne_zero
        have hnz2 : ∏ r ∈ Q', r ^ kfn r ≠ 0 :=
          (Finset.prod_pos fun r hr => pow_pos (hQ' r hr).pos _).ne'
        rw [Finset.prod_insert hp, Nat.factorization_mul hnz1 hnz2, Finsupp.add_apply,
          Nat.Prime.factorization_pow hpp, ih hQ']
        by_cases hqp : q' = p
        · subst hqp; simp [hp]
        · simp [hqp]
    rw [hprod P (fun p hp => mem_primesOf_prime hp)]
    by_cases hqP : q' ∈ P
    · simp [hqP]
    · simp [kfn, hqP]
  have hNout : ∀ q', q' ∉ P → N.factorization q' = 0 := fun q' hq => by
    rw [hNfact q']; simp [kfn, hq]
  let E' := st.E.filter (fun xy => ∀ p ∈ P,
    Int.natAbs ((xy.1.factorization p : ℤ) - kfn p) +
      Int.natAbs ((xy.2.factorization p : ℤ) - kfn p) ≤ 1)
  have htail : C_conc * ∑ p ∈ P, (p : ℝ) ^ (-(9 : ℝ) / 8) ≤ 1 / 2 :=
    prime_tail_sum_le P (fun p hp => (hprime_data p hp).1)
  have hbad_cov : st.E \ E' ⊆ P.biUnion (fun p =>
      st.E.filter (fun xy =>
        2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - kfn p) +
          Int.natAbs ((xy.2.factorization p : ℤ) - kfn p))) := by
    intro xy hxy
    rw [Finset.mem_sdiff, Finset.mem_filter] at hxy
    push Not at hxy
    obtain ⟨hxyE, hbad⟩ := hxy
    obtain ⟨p, hpP, hgt⟩ := hbad hxyE
    exact Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_filter.mpr ⟨hxyE, by omega⟩⟩
  have he_pos : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hdiff_le : ((st.E \ E').card : ℝ) / (st.E.card : ℝ) ≤ 1 / 2 := by
    have h1 := (Finset.card_le_card hbad_cov).trans Finset.card_biUnion_le
    have h2 : (∑ p ∈ P,
        ((st.E.filter (fun xy =>
          2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - kfn p) +
            Int.natAbs ((xy.2.factorization p : ℤ) - kfn p))).card : ℝ) / (st.E.card : ℝ)) ≤
        C_conc * ∑ p ∈ P, (p : ℝ) ^ (-(9 : ℝ) / 8) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hk_eq : kfn p = (hprime_data p hp).2.choose := by simp [kfn, hp]
      rw [hk_eq]
      exact (hprime_data p hp).2.choose_spec
    calc
      ((st.E \ E').card : ℝ) / (st.E.card : ℝ)
          ≤ ((∑ p ∈ P, (st.E.filter (fun xy =>
              2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - kfn p) +
                Int.natAbs ((xy.2.factorization p : ℤ) - kfn p))).card : ℕ) : ℝ) / (st.E.card : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast h1) he_pos.le
      _ = ∑ p ∈ P,
            ((st.E.filter (fun xy =>
              2 ≤ Int.natAbs ((xy.1.factorization p : ℤ) - kfn p) +
                Int.natAbs ((xy.2.factorization p : ℤ) - kfn p))).card : ℝ) / (st.E.card : ℝ) := by
            push_cast; rw [Finset.sum_div]
      _ ≤ C_conc * ∑ p ∈ P, (p : ℝ) ^ (-(9 : ℝ) / 8) := h2
      _ ≤ 1 / 2 := htail
  have hE'card : st.E.card ≤ 2 * E'.card := by
    have hsub : E' ⊆ st.E := Finset.filter_subset _ _
    have hadd : (st.E \ E').card + E'.card = st.E.card := Finset.card_sdiff_add_card_eq_card hsub
    have h1 : ((st.E \ E').card : ℝ) ≤ (st.E.card : ℝ) / 2 := by
      rw [div_le_iff₀ he_pos] at hdiff_le
      linarith
    have h2 : (st.E \ E').card * 2 ≤ st.E.card := by
      exact_mod_cast (show ((st.E \ E').card : ℝ) * 2 ≤ st.E.card by linarith)
    omega
  have hE'ne : E'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he0
    rw [he0, Finset.card_empty, mul_zero] at hE'card
    have := st.hEne.card_pos
    omega
  refine ⟨N, hNpos, hNout, E', Finset.filter_subset _ _, hE'ne, hE'card, ?_⟩
  intro xy hxy p hprime
  have h1 := (Finset.mem_filter.mp hxy).2
  rw [hNfact p]
  by_cases hpP : p ∈ P
  · exact h1 p hpP
  · have hm := Finset.mem_product.mp (st.hEsub (Finset.mem_filter.mp hxy).1)
    have hx0 : xy.1.factorization p = 0 := by
      by_contra hne
      have hd := (hprime.pow_dvd_iff_le_factorization (st.hXpos xy.1 hm.1).ne').mpr
        (by omega : 1 ≤ xy.1.factorization p)
      rw [pow_one] at hd
      exact hpP (Finset.mem_biUnion.mpr ⟨xy.1, Finset.mem_union_left _ hm.1,
        Nat.mem_primeFactors.mpr ⟨hprime, hd, (st.hXpos xy.1 hm.1).ne'⟩⟩)
    have hy0 : xy.2.factorization p = 0 := by
      by_contra hne
      have hd := (hprime.pow_dvd_iff_le_factorization (st.hYpos xy.2 hm.2).ne').mpr
        (by omega : 1 ≤ xy.2.factorization p)
      rw [pow_one] at hd
      exact hpP (Finset.mem_biUnion.mpr ⟨xy.2, Finset.mem_union_right _ hm.2,
        Nat.mem_primeFactors.mpr ⟨hprime, hd, (st.hYpos xy.2 hm.2).ne'⟩⟩)
    have hk0 : kfn p = 0 := by simp [kfn, hpP]
    rw [hx0, hy0, hk0]
    norm_num

private noncomputable def xPlus (P : Finset ℕ) (N x : ℕ) : ℕ :=
  ∏ p ∈ P.filter (fun p => N.factorization p < x.factorization p), p

private noncomputable def xMinus (P : Finset ℕ) (N x : ℕ) : ℕ :=
  ∏ p ∈ P.filter (fun p => x.factorization p < N.factorization p), p

private noncomputable def xStar (P : Finset ℕ) (N x : ℕ) : ℕ :=
  xPlus P N x * xMinus P N x

private lemma factorization_prod_primes (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Nat.Prime p) (q : ℕ) :
    (∏ p ∈ Q, p).factorization q = if q ∈ Q then 1 else 0 := by
  induction Q using Finset.induction with
  | empty => simp
  | @insert p Q' hp ih =>
    have hpp := hQ p (Finset.mem_insert_self _ _)
    have hQ' : ∀ r ∈ Q', Nat.Prime r := fun r hr => hQ r (Finset.mem_insert_of_mem hr)
    have hnz : ∏ r ∈ Q', r ≠ 0 := (Finset.prod_pos fun r hr => (hQ' r hr).pos).ne'
    rw [Finset.prod_insert hp, Nat.factorization_mul hpp.ne_zero hnz, Finsupp.add_apply,
      hpp.factorization, ih hQ']
    by_cases hqp : q = p
    · subst hqp; simp [hp]
    · simp [hqp]

private lemma gw_defect_identities {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {N x : ℕ} (hN : 0 < N) (hx : 0 < x)
    (hNout : ∀ q, q ∉ P → N.factorization q = 0)
    (hxout : ∀ q, q ∉ P → x.factorization q = 0)
    (hdiff : ∀ p, Nat.Prime p → Int.natAbs ((x.factorization p : ℤ) - N.factorization p) ≤ 1) :
    xPlus P N x * N = x * xMinus P N x := by
  have hP1 : ∀ p ∈ P.filter (fun p => N.factorization p < x.factorization p), Nat.Prime p :=
    fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hP2 : ∀ p ∈ P.filter (fun p => x.factorization p < N.factorization p), Nat.Prime p :=
    fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hpos1 : 0 < xPlus P N x := Finset.prod_pos fun p hp => (hP1 p hp).pos
  have hpos2 : 0 < xMinus P N x := Finset.prod_pos fun p hp => (hP2 p hp).pos
  apply Nat.factorization_inj (Nat.mul_pos hpos1 hN).ne' (Nat.mul_pos hx hpos2).ne'
  ext q
  rw [Nat.factorization_mul hpos1.ne' hN.ne', Nat.factorization_mul hx.ne' hpos2.ne',
    Finsupp.add_apply, Finsupp.add_apply]
  unfold xPlus xMinus
  rw [factorization_prod_primes _ hP1 q, factorization_prod_primes _ hP2 q]
  simp only [Finset.mem_filter]
  by_cases hqP : q ∈ P
  · have hd := hdiff q (hP q hqP)
    rcases lt_trichotomy (x.factorization q) (N.factorization q) with hlt | heq | hgt
    · have h1 : ¬ (q ∈ P ∧ N.factorization q < x.factorization q) := by omega
      have h2 : q ∈ P ∧ x.factorization q < N.factorization q := ⟨hqP, hlt⟩
      rw [if_neg h1, if_pos h2]
      omega
    · have h1 : ¬ (q ∈ P ∧ N.factorization q < x.factorization q) := by omega
      have h2 : ¬ (q ∈ P ∧ x.factorization q < N.factorization q) := by omega
      rw [if_neg h1, if_neg h2, heq]; ring
    · have h1 : q ∈ P ∧ N.factorization q < x.factorization q := ⟨hqP, hgt⟩
      have h2 : ¬ (q ∈ P ∧ x.factorization q < N.factorization q) := by omega
      rw [if_pos h1, if_neg h2]
      omega
  · have h1 := hNout q hqP
    have h2 := hxout q hqP
    simp [hqP, h1, h2]

private lemma gw_gcd_defect {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {N x y : ℕ} (hN : 0 < N) (hx : 0 < x) (hy : 0 < y)
    (hNout : ∀ q, q ∉ P → N.factorization q = 0)
    (hxout : ∀ q, q ∉ P → x.factorization q = 0)
    (hyout : ∀ q, q ∉ P → y.factorization q = 0)
    (hdiff : ∀ p, Nat.Prime p →
      Int.natAbs ((x.factorization p : ℤ) - N.factorization p) +
        Int.natAbs ((y.factorization p : ℤ) - N.factorization p) ≤ 1) :
    Nat.gcd x y * xMinus P N x * xMinus P N y = N := by
  have hPx : ∀ p ∈ P.filter (fun p => x.factorization p < N.factorization p), Nat.Prime p :=
    fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hPy : ∀ p ∈ P.filter (fun p => y.factorization p < N.factorization p), Nat.Prime p :=
    fun p hp => hP p (Finset.mem_filter.mp hp).1
  have hgx : 0 < xMinus P N x := Finset.prod_pos fun p hp => (hPx p hp).pos
  have hgy : 0 < xMinus P N y := Finset.prod_pos fun p hp => (hPy p hp).pos
  have hgcd : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left y hx
  apply Nat.factorization_inj (Nat.mul_pos (Nat.mul_pos hgcd hgx) hgy).ne' hN.ne'
  ext q
  rw [Nat.factorization_mul (Nat.mul_pos hgcd hgx).ne' hgy.ne',
    Nat.factorization_mul hgcd.ne' hgx.ne',
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_gcd hx.ne' hy.ne',
    Finsupp.inf_apply]
  unfold xMinus
  rw [factorization_prod_primes _ hPx q, factorization_prod_primes _ hPy q]
  simp only [Finset.mem_filter]
  by_cases hqP : q ∈ P
  · have hd := hdiff q (hP q hqP)
    rcases le_total (x.factorization q) (y.factorization q) with hxy | hyx
    · rw [inf_of_le_left hxy]
      by_cases hxN : x.factorization q < N.factorization q <;>
        by_cases hyN : y.factorization q < N.factorization q <;>
        simp [hqP, hxN, hyN] <;> omega
    · rw [inf_of_le_right hyx]
      by_cases hxN : x.factorization q < N.factorization q <;>
        by_cases hyN : y.factorization q < N.factorization q <;>
        simp [hqP, hxN, hyN] <;> omega
  · have h1 := hNout q hqP
    have h2 := hxout q hqP
    have h3 := hyout q hqP
    simp [hqP, h1, h2, h3]

private lemma gw_count_defect {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (N : ℕ) (hN : 0 < N) (hNout : ∀ q, q ∉ P → N.factorization q = 0)
    (S : Finset ℕ) (lo : ℝ) (hlo : 0 < lo)
    (hSpos : ∀ x ∈ S, 0 < x)
    (hSout : ∀ x ∈ S, ∀ q, q ∉ P → x.factorization q = 0)
    (hSdiff : ∀ x ∈ S, ∀ p, Nat.Prime p → Int.natAbs ((x.factorization p : ℤ) - N.factorization p) ≤ 1)
    (hSrng : ∀ x ∈ S, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * lo)
    {T : ℝ} (hT : 0 < T) :
    ((S.filter (fun x => (xStar P N x : ℝ) ≤ T)).card : ℝ) ≤ 2 * T := by
  let U := S.filter (fun x => (xStar P N x : ℝ) ≤ T)
  let Aup : ℕ := Nat.floor (Real.sqrt (2 * lo * T / (N : ℝ)))
  let Bup : ℕ := Nat.floor (Real.sqrt ((N : ℝ) * T / lo))
  have hN_real : (0 : ℝ) < N := by exact_mod_cast hN
  have hinj : Set.InjOn (fun x => (xPlus P N x, xMinus P N x)) U := by
    intro x hx y hy heq
    have hxS := (Finset.mem_filter.mp hx).1
    have hyS := (Finset.mem_filter.mp hy).1
    have hPx : ∀ p ∈ P.filter (fun p => x.factorization p < N.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hmx_pos : 0 < xMinus P N x := Finset.prod_pos fun p hp => (hPx p hp).pos
    have idx := gw_defect_identities hP hN (hSpos x hxS) hNout (hSout x hxS) (hSdiff x hxS)
    have idy := gw_defect_identities hP hN (hSpos y hyS) hNout (hSout y hyS) (hSdiff y hyS)
    have hp1 : xPlus P N x = xPlus P N y := congrArg Prod.fst heq
    have hm1 : xMinus P N x = xMinus P N y := congrArg Prod.snd heq
    have hxy_mul : x * xMinus P N x = y * xMinus P N x := by
      calc
        x * xMinus P N x = xPlus P N x * N := idx.symm
        _ = xPlus P N y * N := by rw [hp1]
        _ = y * xMinus P N y := idy
        _ = y * xMinus P N x := by rw [hm1]
    exact Nat.eq_of_mul_eq_mul_right hmx_pos hxy_mul
  have hsub : U.image (fun x => (xPlus P N x, xMinus P N x)) ⊆
      Finset.Icc 1 Aup ×ˢ Finset.Icc 1 Bup := by
    intro ab hab
    obtain ⟨x, hxU, rfl⟩ := Finset.mem_image.mp hab
    have hxS := (Finset.mem_filter.mp hxU).1
    have hxstar : (xStar P N x : ℝ) ≤ T := (Finset.mem_filter.mp hxU).2
    have hxpos := hSpos x hxS
    have hxr := hSrng x hxS
    have hP1 : ∀ p ∈ P.filter (fun p => N.factorization p < x.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hP2 : ∀ p ∈ P.filter (fun p => x.factorization p < N.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hpx_pos : 0 < xPlus P N x := Finset.prod_pos fun p hp => (hP1 p hp).pos
    have hmx_pos : 0 < xMinus P N x := Finset.prod_pos fun p hp => (hP2 p hp).pos
    have hid := gw_defect_identities hP hN hxpos hNout (hSout x hxS) (hSdiff x hxS)
    have hidR : (xPlus P N x : ℝ) * (N : ℝ) = (x : ℝ) * (xMinus P N x : ℝ) := by
      exact_mod_cast hid
    have hstarR : (xPlus P N x : ℝ) * (xMinus P N x : ℝ) ≤ T := by
      exact_mod_cast hxstar
    have hplus_sq : (xPlus P N x : ℝ) ^ 2 ≤ 2 * lo * T / (N : ℝ) := by
      have h1 : (xPlus P N x : ℝ) ^ 2 * (N : ℝ) = (x : ℝ) * ((xPlus P N x : ℝ) * (xMinus P N x : ℝ)) := by
        linear_combination (xPlus P N x : ℝ) * hidR
      have h2 : (xPlus P N x : ℝ) ^ 2 * (N : ℝ) ≤ (2 * lo) * T := by
        rw [h1]
        exact mul_le_mul hxr.2 hstarR (mul_nonneg (by positivity) (by positivity)) (by positivity)
      rw [le_div_iff₀ hN_real]
      linarith
    have hminus_sq : (xMinus P N x : ℝ) ^ 2 ≤ (N : ℝ) * T / lo := by
      have h1 : (x : ℝ) * (xMinus P N x : ℝ) ^ 2 = ((xPlus P N x : ℝ) * (xMinus P N x : ℝ)) * (N : ℝ) := by
        linear_combination -(xMinus P N x : ℝ) * hidR
      have h2 : lo * (xMinus P N x : ℝ) ^ 2 ≤ T * (N : ℝ) := by
        calc
          lo * (xMinus P N x : ℝ) ^ 2 ≤ (x : ℝ) * (xMinus P N x : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hxr.1 (sq_nonneg _)
          _ = ((xPlus P N x : ℝ) * (xMinus P N x : ℝ)) * (N : ℝ) := h1
          _ ≤ T * (N : ℝ) := mul_le_mul_of_nonneg_right hstarR hN_real.le
      rw [le_div_iff₀ hlo]
      linarith
    have hplus_le : xPlus P N x ≤ Aup := by
      have hsq' := Real.sqrt_le_sqrt hplus_sq
      rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hsq'
      exact Nat.le_floor hsq'
    have hminus_le : xMinus P N x ≤ Bup := by
      have hsq' := Real.sqrt_le_sqrt hminus_sq
      rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hsq'
      exact Nat.le_floor hsq'
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hpx_pos, hplus_le⟩,
      Finset.mem_Icc.mpr ⟨hmx_pos, hminus_le⟩⟩
  have hcard : U.card ≤ Aup * Bup := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]; simp)
  have hAup : (Aup : ℝ) ≤ Real.sqrt (2 * lo * T / (N : ℝ)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hBup : (Bup : ℝ) ≤ Real.sqrt ((N : ℝ) * T / lo) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hsq : ((Aup : ℝ) * Bup) ^ 2 ≤ (2 * T) ^ 2 := by
    calc
      ((Aup : ℝ) * Bup) ^ 2 = (Aup : ℝ) ^ 2 * (Bup : ℝ) ^ 2 := by ring
      _ ≤ (Real.sqrt (2 * lo * T / (N : ℝ))) ^ 2 * (Real.sqrt ((N : ℝ) * T / lo)) ^ 2 := by
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hAup 2)
          (pow_le_pow_left₀ (by positivity) hBup 2) (by positivity) (by positivity)
      _ = (2 * lo * T / (N : ℝ)) * ((N : ℝ) * T / lo) := by
        rw [Real.sq_sqrt (div_nonneg (by positivity) hN_real.le),
          Real.sq_sqrt (div_nonneg (by positivity) hlo.le)]
      _ = 2 * T ^ 2 := by field_simp [hN_real.ne', hlo.ne']
      _ ≤ 4 * T ^ 2 := by nlinarith [hT.le]
      _ = (2 * T) ^ 2 := by ring
  have hprod_le : (Aup : ℝ) * Bup ≤ 2 * T :=
    le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
  exact (by exact_mod_cast hcard : (U.card : ℝ) ≤ (Aup : ℝ) * Bup).trans hprod_le

private lemma gw_box_at_max {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    (st : GWState X₀ Y₀ A₀ B₀ D₀)
    (N : ℕ) (hN : 0 < N)
    (hNout : ∀ q', q' ∉ primesOf (st.X ∪ st.Y) → N.factorization q' = 0)
    (E' : Finset (ℕ × ℕ)) (hE'sub : E' ⊆ st.E) (_hE'ne : E'.Nonempty)
    (hE'card : st.E.card ≤ 2 * E'.card)
    (hdiff : ∀ xy ∈ E', ∀ p : ℕ, Nat.Prime p →
      Int.natAbs ((xy.1.factorization p : ℤ) - N.factorization p) +
        Int.natAbs ((xy.2.factorization p : ℤ) - N.factorization p) ≤ 1) :
    let a : ℝ := st.X.card
    let b : ℝ := st.Y.card
    let ρ : ℝ := (st.E.card : ℝ) / (a * b)
    let A : ℝ := A₀ / st.sX
    let B : ℝ := B₀ / st.sY
    let D : ℝ := D₀ / st.sD
    ρ ^ 2 * a * b * (D ^ 2 / (A * B)) < 1024 ∧
      ∃ U ⊆ st.Y, U.Nonempty ∧ (st.E.card : ℝ) / (4 * a) ≤ U.card ∧
        ∃ (ξ : ℚ) (A_box B_box : ℕ), 0 < ξ ∧ 0 < A_box ∧ 0 < B_box ∧
          (A_box : ℝ) * B_box ≤ 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * U.card ∧
          ∀ y ∈ U, ∃ a' b' : ℕ, 0 < a' ∧ a' ≤ A_box ∧ 0 < b' ∧ b' ≤ B_box ∧
            ((y * st.sY : ℕ) : ℚ) = ξ * a' / b' := by
  let P := primesOf (st.X ∪ st.Y)
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => mem_primesOf_prime hp
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hsX : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
  have hsY : (0 : ℝ) < st.sY := by exact_mod_cast st.hsY
  have hsD : (0 : ℝ) < st.sD := by exact_mod_cast st.hsD
  let a : ℝ := st.X.card
  let b : ℝ := st.Y.card
  let ρ : ℝ := (st.E.card : ℝ) / (a * b)
  let A : ℝ := A₀ / st.sX
  let B : ℝ := B₀ / st.sY
  let D : ℝ := D₀ / st.sD
  have hρ : 0 < ρ := by positivity
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hD : 0 < D := by positivity
  have hxout : ∀ x ∈ st.X, ∀ q, q ∉ P → x.factorization q = 0 := by
    intro x hx q hq
    by_contra hne
    have hxpos := st.hXpos x hx
    have hqP : q ∣ x := by
      have hp1 : 1 ≤ x.factorization q := by omega
      by_cases hqp : Nat.Prime q
      · rw [← pow_one q]; exact (hqp.pow_dvd_iff_le_factorization hxpos.ne').mpr hp1
      · exfalso; exact hne (Nat.factorization_eq_zero_of_not_prime x hqp)
    have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors
      (by
        by_contra hnp
        have hq0 : q ∉ x.primeFactors := hnp
        have hz : x.factorization q = 0 := Finsupp.notMem_support_iff.mp (by
          simpa [Nat.support_factorization] using hq0)
        exact hne hz)
    exact hq (Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left _ hx,
      Nat.mem_primeFactors.mpr ⟨hqp, hqP, hxpos.ne'⟩⟩)
  have hyout : ∀ y ∈ st.Y, ∀ q, q ∉ P → y.factorization q = 0 := by
    intro y hy q hq
    by_contra hne
    have hypos := st.hYpos y hy
    have hqp : Nat.Prime q := by
      by_contra hnp
      exact hne (Nat.factorization_eq_zero_of_not_prime y hnp)
    have hqP : q ∣ y := by
      rw [← pow_one q]; exact (hqp.pow_dvd_iff_le_factorization hypos.ne').mpr (by omega)
    exact hq (Finset.mem_biUnion.mpr ⟨y, Finset.mem_union_right _ hy,
      Nat.mem_primeFactors.mpr ⟨hqp, hqP, hypos.ne'⟩⟩)
  have hpair_star : ∀ xy ∈ E', (xStar P N xy.1 : ℝ) * (xStar P N xy.2 : ℝ) < 4 * A * B / D ^ 2 := by
    intro xy hxy
    have hxyE := hE'sub hxy
    have hm := Finset.mem_product.mp (st.hEsub hxyE)
    have hxpos := st.hXpos xy.1 hm.1
    have hypos := st.hYpos xy.2 hm.2
    have hxr := st.hXrng xy.1 hm.1
    have hyr := st.hYrng xy.2 hm.2
    have hgx := st.hEgcd xy hxyE
    have hx_diff : ∀ p, Nat.Prime p → Int.natAbs ((xy.1.factorization p : ℤ) - N.factorization p) ≤ 1 :=
      fun p hp => by have := hdiff xy hxy p hp; omega
    have hy_diff : ∀ p, Nat.Prime p → Int.natAbs ((xy.2.factorization p : ℤ) - N.factorization p) ≤ 1 :=
      fun p hp => by have := hdiff xy hxy p hp; omega
    have hidx := gw_defect_identities hP hN hxpos hNout (hxout xy.1 hm.1) hx_diff
    have hidy := gw_defect_identities hP hN hypos hNout (hyout xy.2 hm.2) hy_diff
    have hidgcd := gw_gcd_defect hP hN hxpos hypos hNout (hxout xy.1 hm.1) (hyout xy.2 hm.2) (hdiff xy hxy)
    have hPx1 : ∀ p ∈ P.filter (fun p => N.factorization p < xy.1.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hPx2 : ∀ p ∈ P.filter (fun p => xy.1.factorization p < N.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hPy1 : ∀ p ∈ P.filter (fun p => N.factorization p < xy.2.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hPy2 : ∀ p ∈ P.filter (fun p => xy.2.factorization p < N.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hxmr : (0 : ℝ) < xMinus P N xy.1 := by
      exact_mod_cast Finset.prod_pos fun p hp => (hPx2 p hp).pos
    have hymr : (0 : ℝ) < xMinus P N xy.2 := by
      exact_mod_cast Finset.prod_pos fun p hp => (hPy2 p hp).pos
    have hxpr : 0 ≤ (xPlus P N xy.1 : ℝ) := by positivity
    have hypr : 0 ≤ (xPlus P N xy.2 : ℝ) := by positivity
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hidxR : (xPlus P N xy.1 : ℝ) * N = (xy.1 : ℝ) * xMinus P N xy.1 := by exact_mod_cast hidx
    have hidyR : (xPlus P N xy.2 : ℝ) * N = (xy.2 : ℝ) * xMinus P N xy.2 := by exact_mod_cast hidy
    have hgcdR : (Nat.gcd xy.1 xy.2 : ℝ) * xMinus P N xy.1 * xMinus P N xy.2 = N := by
      exact_mod_cast hidgcd
    have hDxmy : D * xMinus P N xy.1 * xMinus P N xy.2 < N := by
      calc
        D * xMinus P N xy.1 * xMinus P N xy.2
            < (Nat.gcd xy.1 xy.2 : ℝ) * xMinus P N xy.1 * xMinus P N xy.2 := by
              exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hgx hxmr) hymr
        _ = N := hgcdR
    have h1 : (xPlus P N xy.1 : ℝ) * N ≤ 2 * A * xMinus P N xy.1 := by
      rw [hidxR]; exact mul_le_mul_of_nonneg_right hxr.2 hxmr.le
    have h2 : (xPlus P N xy.2 : ℝ) * N ≤ 2 * B * xMinus P N xy.2 := by
      rw [hidyR]; exact mul_le_mul_of_nonneg_right hyr.2 hymr.le
    have hmul_lhs : ((xStar P N xy.1 : ℝ) * (xStar P N xy.2 : ℝ)) * (N : ℝ) ^ 2 * D ^ 2 =
        ((xPlus P N xy.1 : ℝ) * N) * ((xPlus P N xy.2 : ℝ) * N) *
          (xMinus P N xy.1 * xMinus P N xy.2) * D ^ 2 := by
      unfold xStar; push_cast; ring
    have hlt_sq : (D * xMinus P N xy.1 * xMinus P N xy.2) ^ 2 < (N : ℝ) ^ 2 := by
      have h0 : 0 ≤ D * xMinus P N xy.1 * xMinus P N xy.2 := by positivity
      exact pow_lt_pow_left₀ hDxmy h0 (by norm_num)
    have hmain_lt : ((xStar P N xy.1 : ℝ) * (xStar P N xy.2 : ℝ)) * (N : ℝ) ^ 2 * D ^ 2 <
        4 * A * B * (N : ℝ) ^ 2 := by
      calc
        ((xStar P N xy.1 : ℝ) * (xStar P N xy.2 : ℝ)) * (N : ℝ) ^ 2 * D ^ 2
            = ((xPlus P N xy.1 : ℝ) * N) * ((xPlus P N xy.2 : ℝ) * N) *
                (xMinus P N xy.1 * xMinus P N xy.2) * D ^ 2 := hmul_lhs
        _ ≤ (2 * A * xMinus P N xy.1) * (2 * B * xMinus P N xy.2) *
                (xMinus P N xy.1 * xMinus P N xy.2) * D ^ 2 := by
              have hm12 : ((xPlus P N xy.1 : ℝ) * N) * ((xPlus P N xy.2 : ℝ) * N) ≤
                  (2 * A * xMinus P N xy.1) * (2 * B * xMinus P N xy.2) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
              have hm3 := mul_le_mul_of_nonneg_right hm12
                (mul_nonneg hxmr.le hymr.le)
              exact mul_le_mul_of_nonneg_right hm3 (pow_nonneg hD.le 2)
        _ = 4 * A * B * (D * xMinus P N xy.1 * xMinus P N xy.2) ^ 2 := by ring
        _ < 4 * A * B * (N : ℝ) ^ 2 := by gcongr
    rw [lt_div_iff₀ (pow_pos hD 2)]
    nlinarith [pow_pos hNR 2]
  let deg : ℕ → ℕ := fun x => (E'.filter (fun xy => xy.1 = x)).card
  let X_hi : Finset ℕ := st.X.filter (fun x => (st.E.card : ℝ) / (4 * a) ≤ (deg x : ℝ))
  have hsum_deg : (∑ x ∈ st.X, (deg x : ℝ)) = E'.card := by
    have hmap : ∀ xy ∈ E', xy.1 ∈ st.X := fun xy hxy =>
      (Finset.mem_product.mp (st.hEsub (hE'sub hxy))).1
    have hf := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (f := fun _ => (1 : ℝ)) hmap
    simpa [deg] using hf
  have hXhi_card : ρ * a / 4 ≤ X_hi.card := by
    have hcov : st.X = X_hi ∪ (st.X \ X_hi) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, X_hi, Finset.mem_filter]; tauto
    have hdisj : Disjoint X_hi (st.X \ X_hi) := disjoint_sdiff_self_right
    have hsplit : (∑ x ∈ st.X, (deg x : ℝ)) =
        (∑ x ∈ X_hi, (deg x : ℝ)) + ∑ x ∈ st.X \ X_hi, (deg x : ℝ) := by
      nth_rw 1 [hcov]; exact Finset.sum_union hdisj
    have hhi_bd : (∑ x ∈ X_hi, (deg x : ℝ)) ≤ (X_hi.card : ℝ) * b := by
      have hpt : ∀ x ∈ X_hi, (deg x : ℝ) ≤ b := by
        intro x _
        have hsub : (E'.filter (fun xy => xy.1 = x)).image Prod.snd ⊆ st.Y := by
          intro y hy
          obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_product.mp (st.hEsub (hE'sub (Finset.mem_filter.mp hxy).1))).2
        have hc : deg x ≤ st.Y.card := by
          have himg : ((E'.filter (fun xy => xy.1 = x)).image Prod.snd).card = deg x :=
            Finset.card_image_of_injOn fun xy₁ h1 xy₂ h2 heq => by
              have e1 := (Finset.mem_filter.mp h1).2
              have e2 := (Finset.mem_filter.mp h2).2
              ext <;> [exact e1.trans e2.symm; exact heq]
          rw [← himg]
          exact Finset.card_le_card hsub
        dsimp [b]; exact_mod_cast hc
      calc
        (∑ x ∈ X_hi, (deg x : ℝ)) ≤ ∑ _x ∈ X_hi, b := Finset.sum_le_sum hpt
        _ = (X_hi.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlo_bd : (∑ x ∈ st.X \ X_hi, (deg x : ℝ)) ≤ (st.E.card : ℝ) / 4 := by
      have hpt : ∀ x ∈ st.X \ X_hi, (deg x : ℝ) ≤ (st.E.card : ℝ) / (4 * a) := by
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_filter] at hx
        by_contra hgt
        push Not at hgt
        exact hx.2 ⟨hx.1, hgt.le⟩
      have hcard_le : ((st.X \ X_hi).card : ℝ) ≤ a := by
        dsimp [a]; exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : st.X \ X_hi ⊆ st.X)
      have ha_ne : a ≠ 0 := ha.ne'
      have h4a_nn : 0 ≤ (4 : ℝ) * a := mul_nonneg (by norm_num) ha.le
      calc
        (∑ x ∈ st.X \ X_hi, (deg x : ℝ)) ≤ ∑ _x ∈ st.X \ X_hi, (st.E.card : ℝ) / (4 * a) :=
          Finset.sum_le_sum hpt
        _ = ((st.X \ X_hi).card : ℝ) * ((st.E.card : ℝ) / (4 * a)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ a * ((st.E.card : ℝ) / (4 * a)) :=
          mul_le_mul_of_nonneg_right hcard_le (div_nonneg he.le h4a_nn)
        _ = (st.E.card : ℝ) / 4 := by
          calc
            a * ((st.E.card : ℝ) / (4 * a)) = (a / a) * ((st.E.card : ℝ) / 4) := by ring
            _ = 1 * ((st.E.card : ℝ) / 4) := by rw [div_self ha_ne]
            _ = (st.E.card : ℝ) / 4 := one_mul _
    have hE'ge : (st.E.card : ℝ) / 2 ≤ (E'.card : ℝ) := by
      have : (st.E.card : ℝ) ≤ 2 * (E'.card : ℝ) := by exact_mod_cast hE'card
      linarith
    have hge : (st.E.card : ℝ) / 4 ≤ (X_hi.card : ℝ) * b := by linarith only [hsum_deg, hsplit, hhi_bd, hlo_bd, hE'ge]
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne'
    have hreq : (st.E.card : ℝ) / (4 * b) = ρ * a / 4 := by
      calc
        (st.E.card : ℝ) / (4 * b) = ((st.E.card : ℝ) / b) * 1 / 4 := by ring
        _ = ((st.E.card : ℝ) / b) * (a / a) / 4 := by rw [div_self ha_ne]
        _ = ((st.E.card : ℝ) / (a * b)) * a / 4 := by ring
    rw [← hreq, div_le_iff₀ (mul_pos (by norm_num) hb)]
    linarith only [hge]
  have hXhi_out : ∀ x ∈ X_hi, ∀ q, q ∉ P → x.factorization q = 0 :=
    fun x hx => hxout x (Finset.mem_filter.mp hx).1
  have hXhi_pos : ∀ x ∈ X_hi, 0 < x := fun x hx => st.hXpos x (Finset.mem_filter.mp hx).1
  have hXhi_rng : ∀ x ∈ X_hi, A ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * A :=
    fun x hx => st.hXrng x (Finset.mem_filter.mp hx).1
  have hXhi_diff : ∀ x ∈ X_hi, ∀ p, Nat.Prime p →
      Int.natAbs ((x.factorization p : ℤ) - N.factorization p) ≤ 1 := by
    intro x hx p hp
    have hx_deg := (Finset.mem_filter.mp hx).2
    have hd_pos : 0 < deg x := by
      have : (0 : ℝ) < (deg x : ℝ) := lt_of_lt_of_le (div_pos he (mul_pos (by norm_num) ha)) hx_deg
      exact_mod_cast this
    obtain ⟨xy, hxy⟩ := Finset.card_pos.mp hd_pos
    have heq := (Finset.mem_filter.mp hxy).2
    have hm := (Finset.mem_filter.mp hxy).1
    have hd := hdiff xy hm p hp
    rw [← heq]
    omega
  have hx0_ex : ∃ x₀ ∈ X_hi, ρ * a / 16 < (xStar P N x₀ : ℝ) := by
    have hTpos : 0 < ρ * a / 16 := div_pos (mul_pos hρ ha) (by norm_num)
    have hcnt := gw_count_defect hP N hN hNout X_hi A hA hXhi_pos hXhi_out hXhi_diff hXhi_rng hTpos
    by_contra hno
    push Not at hno
    have hsub : X_hi ⊆ X_hi.filter (fun x => (xStar P N x : ℝ) ≤ ρ * a / 16) := fun x hx =>
      Finset.mem_filter.mpr ⟨hx, hno x hx⟩
    have h1 : (X_hi.card : ℝ) ≤ (X_hi.filter (fun x => (xStar P N x : ℝ) ≤ ρ * a / 16)).card :=
      by exact_mod_cast Finset.card_le_card hsub
    have hρa : 0 < ρ * a := mul_pos hρ ha
    linarith only [h1, hcnt, hXhi_card, hρa]
  obtain ⟨x₀, hx₀_hi, hx₀_star⟩ := hx0_ex
  let U : Finset ℕ := (E'.filter (fun xy => xy.1 = x₀)).image Prod.snd
  have hU_sub : U ⊆ st.Y := by
    intro y hy
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_product.mp (st.hEsub (hE'sub (Finset.mem_filter.mp hxy).1))).2
  have hU_card : (st.E.card : ℝ) / (4 * a) ≤ U.card := by
    have hdeg_eq : U.card = deg x₀ := Finset.card_image_of_injOn fun xy₁ h1 xy₂ h2 heq => by
      ext <;> [exact (Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm; exact heq]
    rw [hdeg_eq]
    exact (Finset.mem_filter.mp hx₀_hi).2
  have hU_ne : U.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < U.card := lt_of_lt_of_le (div_pos he (mul_pos (by norm_num) ha)) hU_card
    exact_mod_cast this
  have hU_pair : ∀ y ∈ U, (x₀, y) ∈ E' := by
    intro y hy
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hy
    have hmem := (Finset.mem_filter.mp hxy).1
    have heq := (Finset.mem_filter.mp hxy).2
    simpa [← heq] using hmem
  have hU_diff : ∀ y ∈ U, ∀ p, Nat.Prime p →
      Int.natAbs ((y.factorization p : ℤ) - N.factorization p) ≤ 1 := by
    intro y hy p hp
    have hd := hdiff (x₀, y) (hU_pair y hy) p hp
    dsimp at hd
    omega
  have hy0_ex : ∃ y₀ ∈ U, ρ * b / 16 < (xStar P N y₀ : ℝ) := by
    have hTpos : 0 < ρ * b / 16 := div_pos (mul_pos hρ hb) (by norm_num)
    have hcnt := gw_count_defect hP N hN hNout U B hB
      (fun y hy => st.hYpos y (hU_sub hy)) (fun y hy => hyout y (hU_sub hy)) hU_diff
      (fun y hy => st.hYrng y (hU_sub hy)) hTpos
    by_contra hno
    push Not at hno
    have hsub : U ⊆ U.filter (fun y => (xStar P N y : ℝ) ≤ ρ * b / 16) := fun y hy =>
      Finset.mem_filter.mpr ⟨hy, hno y hy⟩
    have h1 : (U.card : ℝ) ≤ (U.filter (fun y => (xStar P N y : ℝ) ≤ ρ * b / 16)).card :=
      by exact_mod_cast Finset.card_le_card hsub
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne'
    have hU_card' : ρ * b / 4 ≤ U.card := by
      have h1' : (st.E.card : ℝ) / (4 * a) = ρ * b / 4 := by
        calc
          (st.E.card : ℝ) / (4 * a) = ((st.E.card : ℝ) / a) * 1 / 4 := by ring
          _ = ((st.E.card : ℝ) / a) * (b / b) / 4 := by rw [div_self hb_ne]
          _ = ((st.E.card : ℝ) / (a * b)) * b / 4 := by ring
      linarith only [h1', hU_card]
    have hρb : 0 < ρ * b := mul_pos hρ hb
    linarith only [h1, hcnt, hU_card', hρb]
  obtain ⟨y₀, hy₀_U, hy₀_star⟩ := hy0_ex
  have hxy0_bound := hpair_star (x₀, y₀) (hU_pair y₀ hy₀_U)
  dsimp only at hxy0_bound
  have hgw_bound : ρ ^ 2 * a * b * (D ^ 2 / (A * B)) < 1024 := by
    have h1 : (ρ * a / 16) * (ρ * b / 16) < 4 * A * B / D ^ 2 := by
      have hmul : (ρ * a / 16) * (ρ * b / 16) < (xStar P N x₀ : ℝ) * (xStar P N y₀ : ℝ) :=
        mul_lt_mul'' hx₀_star hy₀_star (div_nonneg (mul_nonneg hρ.le ha.le) (by norm_num))
          (div_nonneg (mul_nonneg hρ.le hb.le) (by norm_num))
      exact hmul.trans hxy0_bound
    have h2 : ρ ^ 2 * a * b * (D ^ 2 / (A * B)) =
        256 * ((ρ * a / 16) * (ρ * b / 16)) * (D ^ 2 / (A * B)) := by ring
    rw [h2]
    have h3 : ((ρ * a / 16) * (ρ * b / 16)) * (D ^ 2 / (A * B)) < 4 := by
      rw [mul_div_assoc', div_lt_iff₀ (mul_pos hA hB)]
      have h3' : ((ρ * a / 16) * (ρ * b / 16)) * D ^ 2 < 4 * A * B := by
        rw [← lt_div_iff₀ (pow_pos hD 2)]
        exact h1
      linarith only [h3']
    linarith only [h3]
  refine ⟨hgw_bound, U, hU_sub, hU_ne, hU_card, ?_⟩
  let T₀ : ℝ := 64 * A * B / (ρ * a * D ^ 2)
  have hT0 : 0 < T₀ := div_pos (mul_pos (mul_pos (by norm_num) hA) hB)
    (mul_pos (mul_pos hρ ha) (pow_pos hD 2))
  let A_box : ℕ := Nat.floor (Real.sqrt (2 * B * T₀ / (N : ℝ)))
  let B_box : ℕ := Nat.floor (Real.sqrt ((N : ℝ) * T₀ / B))
  let ξ : ℚ := ((st.sY * N : ℕ) : ℚ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hξ : 0 < ξ := by dsimp [ξ]; exact_mod_cast Nat.mul_pos st.hsY hN
  have hU_y_bound : ∀ y ∈ U, ∃ a' b' : ℕ, 0 < a' ∧ a' ≤ A_box ∧ 0 < b' ∧ b' ≤ B_box ∧
      ((y * st.sY : ℕ) : ℚ) = ξ * a' / b' := by
    intro y hy
    have hmemY := hU_sub hy
    have hypos := st.hYpos y hmemY
    have hyr := st.hYrng y hmemY
    have hP1 : ∀ p ∈ P.filter (fun p => N.factorization p < y.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have hP2 : ∀ p ∈ P.filter (fun p => y.factorization p < N.factorization p), Nat.Prime p :=
      fun p hp => hP p (Finset.mem_filter.mp hp).1
    have ha'_pos : 0 < xPlus P N y := Finset.prod_pos fun p hp => (hP1 p hp).pos
    have hb'_pos : 0 < xMinus P N y := Finset.prod_pos fun p hp => (hP2 p hp).pos
    have hidy := gw_defect_identities hP hN hypos hNout (hyout y hmemY) (hU_diff y hy)
    have hxy_bound := hpair_star (x₀, y) (hU_pair y hy)
    dsimp only at hxy_bound
    have hy_star : (xStar P N y : ℝ) ≤ T₀ := by
      have h1 : (ρ * a / 16) * (xStar P N y : ℝ) ≤ (xStar P N x₀ : ℝ) * (xStar P N y : ℝ) :=
        mul_le_mul_of_nonneg_right hx₀_star.le (Nat.cast_nonneg _)
      have h2 : (ρ * a / 16) * (xStar P N y : ℝ) ≤ 4 * A * B / D ^ 2 := h1.trans hxy_bound.le
      dsimp [T₀]
      rw [le_div_iff₀ (mul_pos (mul_pos hρ ha) (pow_pos hD 2))]
      have h2' := mul_le_mul_of_nonneg_right h2 (pow_nonneg hD.le 2)
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 hD.ne')] at h2'
      linarith only [h2']
    have hidR : (xPlus P N y : ℝ) * (N : ℝ) = (y : ℝ) * (xMinus P N y : ℝ) := by exact_mod_cast hidy
    have hstarR : (xPlus P N y : ℝ) * (xMinus P N y : ℝ) ≤ T₀ := by
      unfold xStar at hy_star; exact_mod_cast hy_star
    have ha'_sq : (xPlus P N y : ℝ) ^ 2 ≤ 2 * B * T₀ / (N : ℝ) := by
      have h1 : (xPlus P N y : ℝ) ^ 2 * (N : ℝ) = (y : ℝ) * ((xPlus P N y : ℝ) * (xMinus P N y : ℝ)) := by
        linear_combination (xPlus P N y : ℝ) * hidR
      have h2 : (xPlus P N y : ℝ) ^ 2 * (N : ℝ) ≤ (2 * B) * T₀ := by
        rw [h1]
        exact mul_le_mul hyr.2 hstarR
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg zero_le_two hB.le)
      rw [le_div_iff₀ hNR]; linarith only [h2]
    have hb'_sq : (xMinus P N y : ℝ) ^ 2 ≤ (N : ℝ) * T₀ / B := by
      have h1 : (y : ℝ) * (xMinus P N y : ℝ) ^ 2 = ((xPlus P N y : ℝ) * (xMinus P N y : ℝ)) * (N : ℝ) := by
        linear_combination -(xMinus P N y : ℝ) * hidR
      have h2 : B * (xMinus P N y : ℝ) ^ 2 ≤ T₀ * (N : ℝ) := by
        calc
          B * (xMinus P N y : ℝ) ^ 2 ≤ (y : ℝ) * (xMinus P N y : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hyr.1 (sq_nonneg _)
          _ = ((xPlus P N y : ℝ) * (xMinus P N y : ℝ)) * (N : ℝ) := h1
          _ ≤ T₀ * (N : ℝ) := mul_le_mul_of_nonneg_right hstarR hNR.le
      rw [le_div_iff₀ hB]; linarith only [h2]
    have ha'_le : xPlus P N y ≤ A_box := by
      have hsq' := Real.sqrt_le_sqrt ha'_sq
      rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hsq'
      exact Nat.le_floor hsq'
    have hb'_le : xMinus P N y ≤ B_box := by
      have hsq' := Real.sqrt_le_sqrt hb'_sq
      rw [Real.sqrt_sq (Nat.cast_nonneg _)] at hsq'
      exact Nat.le_floor hsq'
    refine ⟨xPlus P N y, xMinus P N y, ha'_pos, ha'_le, hb'_pos, hb'_le, ?_⟩
    have hb'_ne : ((xMinus P N y : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb'_pos.ne'
    have hq_id : ((xPlus P N y : ℕ) : ℚ) * (N : ℚ) = (y : ℚ) * ((xMinus P N y : ℕ) : ℚ) := by
      exact_mod_cast hidy
    dsimp [ξ]
    rw [eq_div_iff hb'_ne]
    calc
      ((y * st.sY : ℕ) : ℚ) * ((xMinus P N y : ℕ) : ℚ)
          = (st.sY : ℚ) * (((y : ℕ) : ℚ) * ((xMinus P N y : ℕ) : ℚ)) := by push_cast; ring
      _ = (st.sY : ℚ) * (((xPlus P N y : ℕ) : ℚ) * (N : ℚ)) := by rw [hq_id]
      _ = ((st.sY * N : ℕ) : ℚ) * ((xPlus P N y : ℕ) : ℚ) := by push_cast; ring
  obtain ⟨yw, hywU⟩ := hU_ne
  obtain ⟨aw, bw, haw0, hawle, hbw0, hbwle, _⟩ := hU_y_bound yw hywU
  have hAbox_pos : 0 < A_box := lt_of_lt_of_le haw0 hawle
  have hBbox_pos : 0 < B_box := lt_of_lt_of_le hbw0 hbwle
  refine ⟨ξ, A_box, B_box, hξ, hAbox_pos, hBbox_pos, ?_, hU_y_bound⟩
  have hAup : (A_box : ℝ) ≤ Real.sqrt (2 * B * T₀ / (N : ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
  have hBup : (B_box : ℝ) ≤ Real.sqrt ((N : ℝ) * T₀ / B) := Nat.floor_le (Real.sqrt_nonneg _)
  have h2BT0 : 0 ≤ 2 * B * T₀ / (N : ℝ) := div_nonneg (mul_nonneg (mul_nonneg zero_le_two hB.le) hT0.le) hNR.le
  have hNT0B : 0 ≤ (N : ℝ) * T₀ / B := div_nonneg (mul_nonneg hNR.le hT0.le) hB.le
  have hsq : ((A_box : ℝ) * B_box) ^ 2 ≤ ((3 / 2 : ℝ) * T₀) ^ 2 := by
    calc
      ((A_box : ℝ) * B_box) ^ 2 = (A_box : ℝ) ^ 2 * (B_box : ℝ) ^ 2 := by ring
      _ ≤ (Real.sqrt (2 * B * T₀ / (N : ℝ))) ^ 2 * (Real.sqrt ((N : ℝ) * T₀ / B)) ^ 2 := by
          exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hAup 2)
            (pow_le_pow_left₀ (Nat.cast_nonneg _) hBup 2) (sq_nonneg _) (sq_nonneg _)
      _ = (2 * B * T₀ / (N : ℝ)) * ((N : ℝ) * T₀ / B) := by
          rw [Real.sq_sqrt h2BT0, Real.sq_sqrt hNT0B]
      _ = 2 * T₀ ^ 2 := by
          calc
            (2 * B * T₀ / (N : ℝ)) * ((N : ℝ) * T₀ / B) = (2 * T₀ ^ 2) * ((B / B) * ((N : ℝ) / (N : ℝ))) := by ring
            _ = (2 * T₀ ^ 2) * (1 * 1) := by rw [div_self hB.ne', div_self hNR.ne']
            _ = 2 * T₀ ^ 2 := by ring
      _ ≤ ((3 / 2 : ℝ) * T₀) ^ 2 := by nlinarith only [sq_nonneg T₀]
  have hAB_bd : (A_box : ℝ) * B_box ≤ (3 / 2 : ℝ) * T₀ :=
    le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg (by norm_num) hT0.le) hsq
  have ha_ne : a ≠ 0 := ha.ne'
  have hb_ne : b ≠ 0 := hb.ne'
  have he_ne : (st.E.card : ℝ) ≠ 0 := he.ne'
  have hA_ne : A ≠ 0 := hA.ne'
  have hB_ne : B ≠ 0 := hB.ne'
  have hD_ne : D ≠ 0 := hD.ne'
  have hRHS_eq : (3 / 2 : ℝ) * T₀ = 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * ((st.E.card : ℝ) / (4 * a)) := by
    dsimp [T₀, ρ]
    field_simp [ha_ne, hb_ne, he_ne, hA_ne, hB_ne, hD_ne]
    ring
  have hcoeff_nn : 0 ≤ 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ρ) ha.le) hb.le)
      (div_nonneg (sq_nonneg D) (mul_nonneg hA.le hB.le)))
  calc
    (A_box : ℝ) * B_box ≤ (3 / 2 : ℝ) * T₀ := hAB_bd
    _ = 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * ((st.E.card : ℝ) / (4 * a)) := hRHS_eq
    _ ≤ 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * U.card :=
        mul_le_mul_of_nonneg_left hU_card hcoeff_nn

private noncomputable def GW_K0 : ℝ := 1024 * (1000 : ℝ) ^ (p0 + 1)

private lemma gw_K0_pos : 0 < GW_K0 := by
  unfold GW_K0; positivity

private lemma gw_gcd_bound {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    (st₀ : GWState X₀ Y₀ A₀ B₀ D₀) :
    let a₀ : ℝ := st₀.X.card
    let b₀ : ℝ := st₀.Y.card
    let ρ₀ : ℝ := (st₀.E.card : ℝ) / (a₀ * b₀)
    let A : ℝ := A₀ / st₀.sX
    let B : ℝ := B₀ / st₀.sY
    let D : ℝ := D₀ / st₀.sD
    ρ₀ ^ ((5 : ℝ) / 2) * a₀ * b₀ * (D ^ 2 / (A * B)) < GW_K0 := by
  obtain ⟨st, hle, hloc⟩ := gw_local_maximizer (5 / 2 : ℝ) 0 (primesOf (st₀.X ∪ st₀.Y)).card st₀ le_rfl
  obtain ⟨hsm0, N, hN, hNout, E', hE'sub, hE'ne, hE'card, hdiff⟩ :=
    gw_conc_at_max hX0 hY0 hA0 hB0 hD0 (by norm_num) (by norm_num) le_rfl (by norm_num) st hloc
  obtain ⟨hgw_lt, _⟩ := gw_box_at_max hA0 hB0 hD0 st N hN hNout E' hE'sub hE'ne hE'card hdiff
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hsX : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
  have hsY : (0 : ℝ) < st.sY := by exact_mod_cast st.hsY
  have hsD : (0 : ℝ) < st.sD := by exact_mod_cast st.hsD
  let ρ : ℝ := (st.E.card : ℝ) / ((st.X.card : ℝ) * (st.Y.card : ℝ))
  have hρ_le1 : ρ ≤ 1 := by
    have h1 : st.E.card ≤ (st.X ×ˢ st.Y).card := Finset.card_le_card st.hEsub
    rw [Finset.card_product] at h1
    dsimp [ρ]
    rw [div_le_one (by positivity)]
    exact_mod_cast h1
  have hρ_pos : 0 < ρ := by positivity
  have hρ_pow : ρ ^ ((5 : ℝ) / 2) ≤ ρ ^ 2 := by
    have h2 : ρ ^ 2 = ρ ^ (2 : ℝ) := (Real.rpow_natCast ρ 2).symm
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_ge hρ_pos hρ_le1 (by norm_num)
  have hFst_lt : F_val (5 / 2 : ℝ) 0 st < 1024 := by
    unfold F_val; dsimp only
    rw [hsm0, pow_zero, mul_one, Real.rpow_zero, mul_one]
    calc
      ρ ^ ((5 : ℝ) / 2) * (st.X.card : ℝ) * st.Y.card *
          ((D₀ / st.sD) ^ 2 / ((A₀ / st.sX) * (B₀ / st.sY)))
          ≤ ρ ^ 2 * (st.X.card : ℝ) * st.Y.card *
              ((D₀ / st.sD) ^ 2 / ((A₀ / st.sX) * (B₀ / st.sY))) := by gcongr
      _ < 1024 := hgw_lt
  have hF0_lt : F_val (5 / 2 : ℝ) 0 st₀ < 1024 := hle.trans_lt hFst_lt
  have hsm_le : smallPrimes st₀ ≤ p0 + 1 := by
    unfold smallPrimes
    have hsub : (primesOf (st₀.X ∪ st₀.Y)).filter (· ≤ p0) ⊆ Finset.range (p0 + 1) := by
      intro p hp
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have h1000_le : (1000 : ℝ) ^ smallPrimes st₀ ≤ (1000 : ℝ) ^ (p0 + 1) :=
    pow_le_pow_right₀ (by norm_num) hsm_le
  unfold F_val at hF0_lt
  dsimp only at hF0_lt
  unfold GW_K0
  rw [Real.rpow_zero, mul_one] at hF0_lt
  have hpos_p : (0 : ℝ) < (1000 : ℝ) ^ smallPrimes st₀ := by positivity
  have hprod : ((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * st₀.Y.card)) ^ ((5 : ℝ) / 2) *
      st₀.X.card * st₀.Y.card * ((D₀ / st₀.sD) ^ 2 / ((A₀ / st₀.sX) * (B₀ / st₀.sY))) *
      ((1000 : ℝ)⁻¹) ^ smallPrimes st₀ < 1024 := hF0_lt
  have hinv_eq : (((1000 : ℝ)⁻¹) ^ smallPrimes st₀)⁻¹ = (1000 : ℝ) ^ smallPrimes st₀ := by
    rw [inv_pow, inv_inv]
  have hmul : ((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * st₀.Y.card)) ^ ((5 : ℝ) / 2) *
      st₀.X.card * st₀.Y.card * ((D₀ / st₀.sD) ^ 2 / ((A₀ / st₀.sX) * (B₀ / st₀.sY))) <
      1024 * (1000 : ℝ) ^ smallPrimes st₀ := by
    have h1 := mul_lt_mul_of_pos_right hprod hpos_p
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, mul_one] at h1
    exact h1
  exact lt_of_lt_of_le hmul (mul_le_mul_of_nonneg_left h1000_le (by norm_num))

private lemma gw_box_extraction {X₀ Y₀ : Finset ℕ} {A₀ B₀ D₀ : ℝ}
    (hX0 : 0 < X₀.card) (hY0 : 0 < Y₀.card) (hA0 : 0 < A₀) (hB0 : 0 < B₀) (hD0 : 0 < D₀)
    (st₀ : GWState X₀ Y₀ A₀ B₀ D₀) (F₀ : ℝ) (hF0_pos : 0 < F₀)
    (hF0_le : F₀ ≤ F_val (8 / 3 : ℝ) (1 / 15 : ℝ) st₀) :
    ∃ U ⊆ Y₀, U.Nonempty ∧
      ((1 / 4 : ℝ) * (F₀ / 1024) ^ ((33 : ℝ) / 2)) * (Y₀.card : ℝ) ≤ U.card ∧
      ∃ (ξ : ℚ) (A_box B_box : ℕ), 0 < ξ ∧ 0 < A_box ∧ 0 < B_box ∧
        (A_box : ℝ) * B_box ≤ (400 / F₀) * U.card ∧
        ∀ y ∈ U, ∃ a' b' : ℕ, 0 < a' ∧ a' ≤ A_box ∧ 0 < b' ∧ b' ≤ B_box ∧
          (y : ℚ) = ξ * a' / b' := by
  obtain ⟨st, hle, hloc⟩ :=
    gw_local_maximizer (8 / 3 : ℝ) (1 / 15 : ℝ) (primesOf (st₀.X ∪ st₀.Y)).card st₀ le_rfl
  obtain ⟨hsm0, N, hN, hNout, E', hE'sub, hE'ne, hE'card, hdiff⟩ :=
    gw_conc_at_max hX0 hY0 hA0 hB0 hD0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) st hloc
  obtain ⟨hgw_lt, U', hU'sub, hU'ne, hU'card, ξ, A_box, B_box, hξ, hAb0, hBb0, hbox_area, hbox_repr⟩ :=
    gw_box_at_max hA0 hB0 hD0 st N hN hNout E' hE'sub hE'ne hE'card hdiff
  have ha : (0 : ℝ) < st.X.card := by exact_mod_cast st.hXne.card_pos
  have hb : (0 : ℝ) < st.Y.card := by exact_mod_cast st.hYne.card_pos
  have he : (0 : ℝ) < st.E.card := by exact_mod_cast st.hEne.card_pos
  have hX0R : (0 : ℝ) < X₀.card := by exact_mod_cast hX0
  have hY0R : (0 : ℝ) < Y₀.card := by exact_mod_cast hY0
  have hsX : (0 : ℝ) < st.sX := by exact_mod_cast st.hsX
  have hsY : (0 : ℝ) < st.sY := by exact_mod_cast st.hsY
  have hsD : (0 : ℝ) < st.sD := by exact_mod_cast st.hsD
  let a : ℝ := st.X.card
  let b : ℝ := st.Y.card
  let ρ : ℝ := (st.E.card : ℝ) / (a * b)
  let A : ℝ := A₀ / st.sX
  let B : ℝ := B₀ / st.sY
  let D : ℝ := D₀ / st.sD
  let z : ℝ := (a * b) / ((X₀.card : ℝ) * Y₀.card)
  have hρ0 : 0 < ρ := by positivity
  have hz0 : 0 < z := by positivity
  have hρ1 : ρ ≤ 1 := by
    have h1 : st.E.card ≤ (st.X ×ˢ st.Y).card := Finset.card_le_card st.hEsub
    rw [Finset.card_product] at h1
    dsimp [ρ, a, b]
    rw [div_le_one (mul_pos ha hb)]
    exact_mod_cast h1
  have hz1 : z ≤ 1 := by
    dsimp [z, a, b]
    rw [div_le_one (mul_pos hX0R hY0R)]
    exact mul_le_mul (by exact_mod_cast st.hXcard) (by exact_mod_cast st.hYcard) hb.le hX0R.le
  have hFst : F_val (8 / 3 : ℝ) (1 / 15 : ℝ) st =
      ρ ^ ((8 : ℝ) / 3) * a * b * (D ^ 2 / (A * B)) * z ^ ((1 : ℝ) / 15) := by
    unfold F_val; dsimp only
    rw [hsm0, pow_zero, mul_one]
  have hF_ge : F₀ ≤ ρ ^ ((8 : ℝ) / 3) * a * b * (D ^ 2 / (A * B)) * z ^ ((1 : ℝ) / 15) := by
    linarith [hF0_le.trans hle]
  have hF_split : ρ ^ ((8 : ℝ) / 3) * a * b * (D ^ 2 / (A * B)) * z ^ ((1 : ℝ) / 15) =
      (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * (ρ ^ ((2 : ℝ) / 3) * z ^ ((1 : ℝ) / 15)) := by
    have hpow : ρ ^ ((8 : ℝ) / 3) = ρ ^ 2 * ρ ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ0]
      congr 1; norm_num
    rw [hpow]; ring
  have hprod_ge : F₀ / 1024 ≤ ρ ^ ((2 : ℝ) / 3) * z ^ ((1 : ℝ) / 15) := by
    have hlt : ρ ^ ((8 : ℝ) / 3) * a * b * (D ^ 2 / (A * B)) * z ^ ((1 : ℝ) / 15) <
        1024 * (ρ ^ ((2 : ℝ) / 3) * z ^ ((1 : ℝ) / 15)) := by
      rw [hF_split]
      exact mul_lt_mul_of_pos_right hgw_lt (mul_pos (Real.rpow_pos_of_pos hρ0 _) (Real.rpow_pos_of_pos hz0 _))
    linarith
  have hρ_ge : (F₀ / 1024) ^ ((3 : ℝ) / 2) ≤ ρ := by
    have hz_le1 : z ^ ((1 : ℝ) / 15) ≤ 1 := Real.rpow_le_one hz0.le hz1 (by norm_num)
    have h1 : F₀ / 1024 ≤ ρ ^ ((2 : ℝ) / 3) :=
      hprod_ge.trans (mul_le_of_le_one_right (Real.rpow_nonneg hρ0.le _) hz_le1)
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ (3 : ℝ) / 2)
    rw [← Real.rpow_mul hρ0.le, show ((2 : ℝ) / 3) * ((3 : ℝ) / 2) = 1 by norm_num, Real.rpow_one] at h2
    exact h2
  have hz_ge : (F₀ / 1024) ^ (15 : ℝ) ≤ z := by
    have hρ_le1 : ρ ^ ((2 : ℝ) / 3) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by norm_num)
    have h1 : F₀ / 1024 ≤ z ^ ((1 : ℝ) / 15) :=
      hprod_ge.trans (mul_le_of_le_one_left (Real.rpow_nonneg hz0.le _) hρ_le1)
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : 0 ≤ (15 : ℝ))
    rw [← Real.rpow_mul hz0.le, show ((1 : ℝ) / 15) * (15 : ℝ) = 1 by norm_num, Real.rpow_one] at h2
    exact h2
  let U : Finset ℕ := U'.image (· * st.sY)
  have hU_sub : U ⊆ Y₀ := by
    intro y0 hy0
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy0
    exact st.hYmap y (hU'sub hy)
  have hinj : Set.InjOn (· * st.sY) U' := fun y₁ _ y₂ _ heq =>
    Nat.eq_of_mul_eq_mul_right st.hsY heq
  have hU_card_eq : U.card = U'.card := Finset.card_image_of_injOn hinj
  have hU_ne : U.Nonempty := hU'ne.image _
  have hU_frac : ((1 / 4 : ℝ) * (F₀ / 1024) ^ ((33 : ℝ) / 2)) * (Y₀.card : ℝ) ≤ U.card := by
    have hby0 : z * Y₀.card ≤ b := by
      dsimp [z, a, b]
      have ha_le : (st.X.card : ℝ) ≤ X₀.card := by exact_mod_cast st.hXcard
      calc
        (st.X.card : ℝ) * st.Y.card / ((X₀.card : ℝ) * Y₀.card) * Y₀.card
            = ((st.X.card : ℝ) / X₀.card) * st.Y.card := by field_simp [hX0R.ne', hY0R.ne']
        _ ≤ 1 * st.Y.card := mul_le_mul_of_nonneg_right ((div_le_one hX0R).mpr ha_le) hb.le
        _ = st.Y.card := one_mul _
    have hU'_ρb : ρ * b / 4 ≤ U'.card := by
      have ha_ne : a ≠ 0 := ha.ne'
      have hb_ne : b ≠ 0 := hb.ne'
      have h1 : (st.E.card : ℝ) / (4 * a) = ρ * b / 4 := by dsimp [ρ]; field_simp [ha_ne, hb_ne]
      linarith only [h1, hU'card]
    have hpow33 : (F₀ / 1024) ^ ((33 : ℝ) / 2) = (F₀ / 1024) ^ ((3 : ℝ) / 2) * (F₀ / 1024) ^ (15 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; norm_num
    rw [hU_card_eq]
    calc
      ((1 / 4 : ℝ) * (F₀ / 1024) ^ ((33 : ℝ) / 2)) * (Y₀.card : ℝ)
          = ((F₀ / 1024) ^ ((3 : ℝ) / 2) * ((F₀ / 1024) ^ (15 : ℝ) * Y₀.card)) / 4 := by
              rw [hpow33]; ring
      _ ≤ (ρ * (z * Y₀.card)) / 4 := by gcongr
      _ ≤ (ρ * b) / 4 := by gcongr
      _ ≤ U'.card := hU'_ρb
  have hden_ge : (96 : ℝ) / 100 * F₀ ≤ ρ ^ 2 * a * b * (D ^ 2 / (A * B)) := by
    have hA' : 0 < A := div_pos hA0 hsX
    have hB' : 0 < B := div_pos hB0 hsY
    have hD' : 0 < D := div_pos hD0 hsD
    have hF_le_prod : F₀ ≤ ρ ^ 2 * a * b * (D ^ 2 / (A * B)) := by
      have hr23 : ρ ^ ((2 : ℝ) / 3) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by norm_num)
      have hz15 : z ^ ((1 : ℝ) / 15) ≤ 1 := Real.rpow_le_one hz0.le hz1 (by norm_num)
      have hprod1 : ρ ^ ((2 : ℝ) / 3) * z ^ ((1 : ℝ) / 15) ≤ 1 := by
        simpa only [mul_one] using mul_le_mul hr23 hz15 (Real.rpow_nonneg hz0.le _) zero_le_one
      have hpos_m : 0 ≤ ρ ^ 2 * a * b * (D ^ 2 / (A * B)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ρ) ha.le) hb.le)
          (div_nonneg (sq_nonneg D) (mul_nonneg hA'.le hB'.le))
      calc
        F₀ ≤ ρ ^ ((8 : ℝ) / 3) * a * b * (D ^ 2 / (A * B)) * z ^ ((1 : ℝ) / 15) := hF_ge
        _ = (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * (ρ ^ ((2 : ℝ) / 3) * z ^ ((1 : ℝ) / 15)) := hF_split
        _ ≤ (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) * 1 := mul_le_mul_of_nonneg_left hprod1 hpos_m
        _ = ρ ^ 2 * a * b * (D ^ 2 / (A * B)) := mul_one _
    linarith only [hF_le_prod, hF0_pos]
  have hbox_le : (A_box : ℝ) * B_box ≤ (400 / F₀) * U.card := by
    rw [hU_card_eq]
    have h384 : 384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) ≤ 400 / F₀ := by
      have h96 : (384 : ℝ) / ((96 / 100 : ℝ) * F₀) = 400 / F₀ := by field_simp [hF0_pos.ne']; ring
      calc
        384 / (ρ ^ 2 * a * b * (D ^ 2 / (A * B))) ≤ 384 / ((96 / 100 : ℝ) * F₀) := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_ge
        _ = 400 / F₀ := h96
    exact hbox_area.trans (mul_le_mul_of_nonneg_right h384 (by positivity))
  refine ⟨U, hU_sub, hU_ne, hU_frac, ξ, A_box, B_box, hξ, hAb0, hBb0, hbox_le, ?_⟩
  intro y0 hy0
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy0
  exact hbox_repr y hy

-- Part 4: Hu-Jing Theorem 7.2 (Dyadic Pigeonhole + GW Box Extraction)

private noncomputable def DB_c0 : ℝ := 64 * ((128 : ℝ) ^ 2 * GW_K0) ^ ((2 : ℝ) / 5)
private noncomputable def DB_eta0 : ℝ := (36 * DB_c0) ^ (-10 : ℤ)
private noncomputable def DB_K1 : ℕ := 4 * Nat.ceil (72 * DB_c0) + 4
private noncomputable def DB_F0 : ℝ :=
  (DB_eta0 ^ 2 / 256) ^ ((8 : ℝ) / 3) * (DB_eta0 ^ 2 / 128 ^ 2) * ((1000 : ℝ)⁻¹) ^ (p0 + 1)
private noncomputable def DB_Cbox : ℝ := max 1 (400 / DB_F0)
private noncomputable def DB_theta : ℝ :=
  (1 / 4 : ℝ) * (DB_F0 / 1024) ^ ((33 : ℝ) / 2) * DB_eta0

private lemma DB_c0_ge_one : 1 ≤ DB_c0 := by
  have hgw : 1024 ≤ GW_K0 := by
    unfold GW_K0
    have hpow : (1 : ℝ) ≤ (1000 : ℝ) ^ (p0 + 1) := one_le_pow₀ (by norm_num)
    linarith
  have h1 : (1 : ℝ) ≤ ((128 : ℝ) ^ 2 * GW_K0) ^ ((2 : ℝ) / 5) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  unfold DB_c0
  linarith

private lemma DB_eta0_pos : 0 < DB_eta0 := by
  have hc0 : 0 < DB_c0 := lt_of_lt_of_le zero_lt_one DB_c0_ge_one
  unfold DB_eta0
  positivity

private lemma DB_eta0_rpow : DB_eta0 ^ ((1 : ℝ) / 10) = 1 / (36 * DB_c0) := by
  have hc0 : 0 < DB_c0 := lt_of_lt_of_le zero_lt_one DB_c0_ge_one
  unfold DB_eta0
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by positivity),
    show ((-10 : ℤ) : ℝ) * ((1 : ℝ) / 10) = -1 by norm_num, Real.rpow_neg_one, one_div]

private lemma DB_K1_bound : (4 / 5 : ℝ) ^ DB_K1 ≤ 1 / (72 * DB_c0) := by
  have hc0 : 0 < DB_c0 := lt_of_lt_of_le zero_lt_one DB_c0_ge_one
  have hbern := one_add_mul_le_pow (a := (1 / 4 : ℝ)) (by norm_num) DB_K1
  have hK : 72 * DB_c0 ≤ (DB_K1 : ℝ) * (1 / 4 : ℝ) := by
    have hceil : 72 * DB_c0 ≤ (Nat.ceil (72 * DB_c0) : ℝ) := Nat.le_ceil _
    unfold DB_K1
    push_cast
    linarith
  have hpow : 72 * DB_c0 ≤ (5 / 4 : ℝ) ^ DB_K1 := by
    have h1 : (1 : ℝ) + (1 / 4 : ℝ) = 5 / 4 := by norm_num
    rw [h1] at hbern
    linarith
  have hrecip : ((5 / 4 : ℝ) ^ DB_K1)⁻¹ ≤ (72 * DB_c0)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have heq : (4 / 5 : ℝ) ^ DB_K1 = ((5 / 4 : ℝ) ^ DB_K1)⁻¹ := by
    rw [← inv_pow]
    norm_num
  rw [heq, one_div]
  exact hrecip

private lemma DB_F0_pos : 0 < DB_F0 := by
  have heta := DB_eta0_pos
  unfold DB_F0
  positivity

private lemma DB_Cbox_ge_one : 1 ≤ DB_Cbox := le_max_left _ _

private lemma DB_theta_pos : 0 < DB_theta := by
  have hf := DB_F0_pos
  have heta := DB_eta0_pos
  unfold DB_theta
  positivity

private lemma real_two_rpow_m25_le : (2 : ℝ) ^ (-(2 : ℝ) / 5) ≤ 4 / 5 := by
  refine le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma dyadic_max_ratio (j k : ℕ) :
    (max ((2 : ℝ) ^ j) ((2 : ℝ) ^ k)) ^ 2 / ((2 : ℝ) ^ j * (2 : ℝ) ^ k) =
      (2 : ℝ) ^ Int.natAbs ((j : ℤ) - k) := by
  rcases le_total j k with hjk | hkj
  · have hle : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk
    rw [max_eq_right hle, show Int.natAbs ((j : ℤ) - k) = k - j by omega]
    have hk : (2 : ℝ) ^ k = (2 : ℝ) ^ j * (2 : ℝ) ^ (k - j) := by
      rw [← pow_add]; congr 1; omega
    have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have h2k : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    rw [sq]
    calc
      (2 : ℝ) ^ k * (2 : ℝ) ^ k / ((2 : ℝ) ^ j * (2 : ℝ) ^ k)
          = (2 : ℝ) ^ k / (2 : ℝ) ^ j := by field_simp [h2j, h2k]
      _ = ((2 : ℝ) ^ j * (2 : ℝ) ^ (k - j)) / (2 : ℝ) ^ j := by rw [hk]
      _ = (2 : ℝ) ^ (k - j) := by field_simp [h2j]
  · have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkj
    rw [max_eq_left hle, show Int.natAbs ((j : ℤ) - k) = j - k by omega]
    have hj : (2 : ℝ) ^ j = (2 : ℝ) ^ k * (2 : ℝ) ^ (j - k) := by
      rw [← pow_add]; congr 1; omega
    have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have h2k : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    rw [sq]
    calc
      (2 : ℝ) ^ j * (2 : ℝ) ^ j / ((2 : ℝ) ^ j * (2 : ℝ) ^ k)
          = (2 : ℝ) ^ j / (2 : ℝ) ^ k := by field_simp [h2j, h2k]
      _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ (j - k)) / (2 : ℝ) ^ k := by rw [hj]
      _ = (2 : ℝ) ^ (j - k) := by field_simp [h2k]

lemma dyadic_box_extraction :
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
      n ^ 2 ≤ 64 * ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
        ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64 * n * Nat.gcd (v ij.1) (v ij.2)).card →
      ∃ (U : Finset (Fin n)) (ξ : ℚ) (A B : ℕ),
        DB_theta * n ≤ U.card ∧ 0 < ξ ∧ 0 < A ∧ 0 < B ∧
          (A : ℝ) * B ≤ DB_Cbox * U.card ∧
          ∀ i ∈ U, ∃ a b : ℕ, 0 < a ∧ a ≤ A ∧ 0 < b ∧ b ≤ B ∧
            (v i : ℚ) = ξ * a / b := by
  intro n hn v hv hdense
  have hn_pos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  let V : Finset ℕ := Finset.univ.image v
  have hVcard : V.card = n := by
    rw [Finset.card_image_of_injective _ v.injective, Finset.card_fin]
  have hVpos : ∀ x ∈ V, 0 < x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hv i
  have hVne : V.Nonempty := by
    rw [← Finset.card_pos, hVcard]; exact hn_pos
  let E_full : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
    ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64 * n * Nat.gcd (v ij.1) (v ij.2)
  let E_sym : Finset (ℕ × ℕ) := (V ×ˢ V).filter fun xy =>
    xy.1 ≠ xy.2 ∧ max xy.1 xy.2 ≤ 64 * n * Nat.gcd xy.1 xy.2
  have hEsym_card : E_full.card ≤ E_sym.card := by
    have hinj : Set.InjOn (fun ij : Fin n × Fin n => (v ij.1, v ij.2)) ↑E_full := by
      intro ij₁ _ ij₂ _ heq
      exact Prod.ext (v.injective (congrArg Prod.fst heq)) (v.injective (congrArg Prod.snd heq))
    have himg : E_full.image (fun ij => (v ij.1, v ij.2)) ⊆ E_sym := by
      intro xy hxy
      obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hxy
      have h1 := (Finset.mem_filter.mp hij).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
         Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, h1.2⟩
      intro heq
      have hlt : ij.1 < ij.2 := h1.1
      have hjeq := v.injective heq
      rw [hjeq] at hlt
      exact hlt.ne rfl
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card himg
  have hn2_Esym : n ^ 2 ≤ 64 * E_sym.card := hdense.trans (Nat.mul_le_mul_left 64 hEsym_card)
  have hEsym_ne : E_sym.Nonempty := by
    rw [← Finset.card_pos]
    have : 4 ≤ n ^ 2 := by nlinarith
    omega
  have hEsymR : (0 : ℝ) < E_sym.card := by exact_mod_cast hEsym_ne.card_pos
  let S : Finset ℕ := V.image (Nat.log 2)
  have hSne : S.Nonempty := hVne.image _
  let Vk : ℕ → Finset ℕ := fun k => V.filter (fun x => Nat.log 2 x = k)
  let Ejk : ℕ → ℕ → Finset (ℕ × ℕ) := fun j k =>
    E_sym.filter (fun xy => Nat.log 2 xy.1 = j ∧ Nat.log 2 xy.2 = k)
  let α : ℕ → ℝ := fun k => ((Vk k).card : ℝ) / (n : ℝ)
  let μ : ℕ → ℕ → ℝ := fun j k => ((Ejk j k).card : ℝ) / (E_sym.card : ℝ)
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (Nat.cast_nonneg _) hnR.le
  have hα_le1 : ∀ k, α k ≤ 1 := fun k => by
    dsimp [α]
    rw [div_le_one hnR, ← hVcard]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hα1 : ∑ k ∈ S, α k = 1 := by
    have hmap : ∀ x ∈ V, Nat.log 2 x ∈ S := fun x hx => Finset.mem_image_of_mem _ hx
    have hf := Finset.sum_fiberwise_of_maps_to (g := Nat.log 2) (f := fun _ => (1 : ℝ)) hmap
    have hcard : (∑ k ∈ S, ((Vk k).card : ℝ)) = n := by
      have : (∑ k ∈ S, ((Vk k).card : ℝ)) = V.card := by simpa [Vk] using hf
      rwa [hVcard] at this
    dsimp [α]
    rw [← Finset.sum_div, hcard, div_self hnR.ne']
  have hμ0 : ∀ j k, 0 ≤ μ j k := fun j k => div_nonneg (Nat.cast_nonneg _) hEsymR.le
  have hμ1 : ∑ j ∈ S, ∑ k ∈ S, μ j k = 1 := by
    have hmap : ∀ xy ∈ E_sym, (Nat.log 2 xy.1, Nat.log 2 xy.2) ∈ S ×ˢ S := fun xy hxy => by
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp hxy).1
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hm.1, Finset.mem_image_of_mem _ hm.2⟩
    have hf := Finset.sum_fiberwise_of_maps_to
      (g := fun xy : ℕ × ℕ => (Nat.log 2 xy.1, Nat.log 2 xy.2)) (f := fun _ => (1 : ℝ)) hmap
    have hcard : (∑ jk ∈ S ×ˢ S,
        ((E_sym.filter (fun xy => (Nat.log 2 xy.1, Nat.log 2 xy.2) = jk)).card : ℝ)) =
        E_sym.card := by simpa using hf
    have hprod_sum : (∑ j ∈ S, ∑ k ∈ S, μ j k) =
        (∑ jk ∈ S ×ˢ S,
          ((E_sym.filter (fun xy => (Nat.log 2 xy.1, Nat.log 2 xy.2) = jk)).card : ℝ)) /
        (E_sym.card : ℝ) := by
      rw [Finset.sum_div, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun jk _ => ?_
      dsimp [μ]
      refine congrArg (fun T : Finset (ℕ × ℕ) => (T.card : ℝ) / (E_sym.card : ℝ)) ?_
      ext xy; simp [Ejk, Prod.ext_iff]
    rw [hprod_sum, hcard, div_self hEsymR.ne']
  have hVk_rng : ∀ k, ∀ x ∈ Vk k, (2 : ℝ) ^ k ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
    intro k x hx
    have hxV := (Finset.mem_filter.mp hx).1
    have hlog := (Finset.mem_filter.mp hx).2
    have hx0 := hVpos x hxV
    have h1 : 2 ^ k ≤ x := by rw [← hlog]; exact Nat.pow_log_le_self 2 hx0.ne'
    have h2 : x ≤ 2 * 2 ^ k := by
      have hlt : x < 2 ^ (k + 1) := by rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) x
      rw [pow_succ'] at hlt
      omega
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hμ_bound : ∀ j ∈ S, ∀ k ∈ S,
      μ j k ≤ DB_c0 * (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (α j * α k) ^ ((3 : ℝ) / 5) := by
    intro j _ k _
    by_cases hEne : (Ejk j k).Nonempty
    · have hXne : (Vk j).Nonempty := by
        obtain ⟨xy, hxy⟩ := hEne
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1
        exact ⟨xy.1, Finset.mem_filter.mpr ⟨hm.1, (Finset.mem_filter.mp hxy).2.1⟩⟩
      have hYne : (Vk k).Nonempty := by
        obtain ⟨xy, hxy⟩ := hEne
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1
        exact ⟨xy.2, Finset.mem_filter.mpr ⟨hm.2, (Finset.mem_filter.mp hxy).2.2⟩⟩
      let A₀ : ℝ := (2 : ℝ) ^ j
      let B₀ : ℝ := (2 : ℝ) ^ k
      let D₀ : ℝ := max A₀ B₀ / (128 * (n : ℝ))
      have hA0 : 0 < A₀ := pow_pos (by norm_num) j
      have hB0 : 0 < B₀ := pow_pos (by norm_num) k
      have hD0 : 0 < D₀ := div_pos (lt_of_lt_of_le hA0 (le_max_left _ _)) (mul_pos (by norm_num) hnR)
      let st₀ : GWState (Vk j) (Vk k) A₀ B₀ D₀ :=
        { X := Vk j
          Y := Vk k
          E := Ejk j k
          sX := 1
          sY := 1
          sD := 1
          hsX := zero_lt_one
          hsY := zero_lt_one
          hsD := zero_lt_one
          hXne := hXne
          hYne := hYne
          hXpos := fun x hx => hVpos x (Finset.mem_filter.mp hx).1
          hYpos := fun y hy => hVpos y (Finset.mem_filter.mp hy).1
          hEne := hEne
          hEsub := fun xy hxy => by
            have h1 := Finset.mem_filter.mp hxy
            have hm := Finset.mem_product.mp (Finset.mem_filter.mp h1.1).1
            exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, h1.2.1⟩,
              Finset.mem_filter.mpr ⟨hm.2, h1.2.2⟩⟩
          hXrng := fun x hx => by
            simpa only [Nat.cast_one, div_one] using hVk_rng j x hx
          hYrng := fun y hy => by
            simpa only [Nat.cast_one, div_one] using hVk_rng k y hy
          hEgcd := fun xy hxy => by
            have h1 := Finset.mem_filter.mp hxy
            have hsym := Finset.mem_filter.mp h1.1
            have hm := Finset.mem_product.mp hsym.1
            have hx_rng := hVk_rng j xy.1 (Finset.mem_filter.mpr ⟨hm.1, h1.2.1⟩)
            have hy_rng := hVk_rng k xy.2 (Finset.mem_filter.mpr ⟨hm.2, h1.2.2⟩)
            have hmax_le : max A₀ B₀ ≤ (max xy.1 xy.2 : ℝ) := max_le_max hx_rng.1 hy_rng.1
            have hgcd_ge : (max xy.1 xy.2 : ℝ) ≤ 64 * (n : ℝ) * Nat.gcd xy.1 xy.2 := by
              exact_mod_cast hsym.2.2
            have h2D : 2 * D₀ ≤ Nat.gcd xy.1 xy.2 := by
              dsimp [D₀]
              rw [show 2 * (max A₀ B₀ / (128 * (n : ℝ))) = max A₀ B₀ / (64 * (n : ℝ)) by ring,
                div_le_iff₀ (mul_pos (by norm_num) hnR)]
              linarith only [hmax_le, hgcd_ge]
            rw [Nat.cast_one, div_one]
            linarith only [hD0, h2D]
          hYmap := fun y hy => by simpa only [mul_one] using hy
          hXcard := le_rfl
          hYcard := le_rfl }
      have hgw := gw_gcd_bound hXne.card_pos hYne.card_pos hA0 hB0 hD0 st₀
      dsimp only at hgw
      have ha_pos : (0 : ℝ) < (Vk j).card := by exact_mod_cast hXne.card_pos
      have hb_pos : (0 : ℝ) < (Vk k).card := by exact_mod_cast hYne.card_pos
      have he_pos : (0 : ℝ) < (Ejk j k).card := by exact_mod_cast hEne.card_pos
      have hαj : 0 < α j := div_pos ha_pos hnR
      have hαk : 0 < α k := div_pos hb_pos hnR
      have hαjk : 0 < α j * α k := mul_pos hαj hαk
      let d := Int.natAbs ((j : ℤ) - k)
      have hD_ratio : (D₀ / 1) ^ 2 / ((A₀ / 1) * (B₀ / 1)) =
          (2 : ℝ) ^ d / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        rw [div_one, div_one, div_one]
        dsimp [D₀, A₀, B₀]
        rw [div_pow, mul_pow, ← dyadic_max_ratio j k]
        ring
      let ρjk : ℝ := ((Ejk j k).card : ℝ) / (((Vk j).card : ℝ) * (Vk k).card)
      have hρjk : 0 < ρjk := div_pos he_pos (mul_pos ha_pos hb_pos)
      have hgw' : ρjk ^ ((5 : ℝ) / 2) * (α j * α k) * (2 : ℝ) ^ d ≤ 128 ^ 2 * GW_K0 := by
        have h1 : ρjk ^ ((5 : ℝ) / 2) * ((Vk j).card : ℝ) * (Vk k).card *
            ((2 : ℝ) ^ d / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2)) < GW_K0 := by
          have hcast1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          have hgw0 : ρjk ^ ((5 : ℝ) / 2) * ((Vk j).card : ℝ) * (Vk k).card *
              ((D₀ / ((1 : ℕ) : ℝ)) ^ 2 / ((A₀ / ((1 : ℕ) : ℝ)) * (B₀ / ((1 : ℕ) : ℝ)))) < GW_K0 := hgw
          rwa [hcast1, hD_ratio] at hgw0
        have h2 : ρjk ^ ((5 : ℝ) / 2) * (α j * α k) * (2 : ℝ) ^ d / (128 : ℝ) ^ 2 =
            ρjk ^ ((5 : ℝ) / 2) * ((Vk j).card : ℝ) * (Vk k).card *
              ((2 : ℝ) ^ d / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2)) := by
          dsimp [α]; ring
        rw [← h2, div_lt_iff₀ (by norm_num)] at h1
        linarith only [h1]
      have hpow25 := Real.rpow_le_rpow
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hρjk.le _) hαjk.le) (pow_nonneg (by norm_num) _))
        hgw' (by norm_num : (0 : ℝ) ≤ 2 / 5)
      have hLHS25 : (ρjk ^ ((5 : ℝ) / 2) * (α j * α k) * (2 : ℝ) ^ d) ^ ((2 : ℝ) / 5) =
          ρjk * (α j * α k) ^ ((2 : ℝ) / 5) * ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ d := by
        rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hρjk.le _) hαjk.le) (pow_nonneg (by norm_num) _),
          Real.mul_rpow (Real.rpow_nonneg hρjk.le _) hαjk.le,
          ← Real.rpow_mul hρjk.le, show ((5 : ℝ) / 2) * ((2 : ℝ) / 5) = 1 by norm_num, Real.rpow_one,
          ← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_natCast ((2 : ℝ) ^ ((2 : ℝ) / 5)) d, ← Real.rpow_mul (by norm_num)]
        congr 2; ring
      have hmul_back : ((Ejk j k).card : ℝ) / (n : ℝ) ^ 2 = ρjk * (α j * α k) := by
        dsimp [ρjk, α]
        calc
          ((Ejk j k).card : ℝ) / (n : ℝ) ^ 2
              = (((Ejk j k).card : ℝ) / (n : ℝ) ^ 2) *
                  ((((Vk j).card : ℝ) / ((Vk j).card : ℝ)) * (((Vk k).card : ℝ) / ((Vk k).card : ℝ))) := by
                rw [div_self ha_pos.ne', div_self hb_pos.ne', mul_one, mul_one]
          _ = ((Ejk j k).card : ℝ) / (((Vk j).card : ℝ) * (Vk k).card) *
                (((Vk j).card : ℝ) / n * (((Vk k).card : ℝ) / n)) := by ring
      have hm25_inv : ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ d * ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d = 1 := by
        rw [← mul_pow, ← Real.rpow_add (by norm_num),
          show (2 : ℝ) / 5 + -(2 : ℝ) / 5 = 0 by norm_num, Real.rpow_zero, one_pow]
      have he_n2 : ((Ejk j k).card : ℝ) / (n : ℝ) ^ 2 ≤
          ((128 : ℝ) ^ 2 * GW_K0) ^ ((2 : ℝ) / 5) * ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d *
            (α j * α k) ^ ((3 : ℝ) / 5) := by
        rw [hmul_back]
        have hm25_nn : (0 : ℝ) ≤ ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d :=
          pow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 : ℝ) / 5)) d
        have h35_nn : (0 : ℝ) ≤ (α j * α k) ^ ((3 : ℝ) / 5) :=
          Real.rpow_nonneg hαjk.le ((3 : ℝ) / 5)
        have hstep := mul_le_mul_of_nonneg_right hpow25 (mul_nonneg hm25_nn h35_nn)
        rw [hLHS25] at hstep
        have hL_eq : ρjk * (α j * α k) ^ ((2 : ℝ) / 5) * ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ d *
            (((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d * (α j * α k) ^ ((3 : ℝ) / 5)) = ρjk * (α j * α k) := by
          calc
            _ = ρjk * ((α j * α k) ^ ((2 : ℝ) / 5) * (α j * α k) ^ ((3 : ℝ) / 5)) *
                  (((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ d * ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d) := by ring
            _ = ρjk * (α j * α k) * 1 := by
                  rw [← Real.rpow_add hαjk, show (2 : ℝ) / 5 + 3 / 5 = 1 by norm_num, Real.rpow_one,
                    hm25_inv]
            _ = ρjk * (α j * α k) := mul_one _
        rw [hL_eq] at hstep
        exact hstep.trans_eq (by ring)
      have hμ_64 : μ j k ≤ 64 * (((Ejk j k).card : ℝ) / (n : ℝ) ^ 2) := by
        have hn2R : (n : ℝ) ^ 2 ≤ 64 * (E_sym.card : ℝ) := by exact_mod_cast hn2_Esym
        dsimp [μ]
        rw [div_le_iff₀ hEsymR]
        calc
          ((Ejk j k).card : ℝ) = ((Ejk j k).card : ℝ) / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
            rw [div_mul_cancel₀ _ (pow_ne_zero 2 hnR.ne')]
          _ ≤ ((Ejk j k).card : ℝ) / (n : ℝ) ^ 2 * (64 * (E_sym.card : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hn2R (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
          _ = 64 * (((Ejk j k).card : ℝ) / (n : ℝ) ^ 2) * (E_sym.card : ℝ) := by ring
      have hpow_m25 : ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d ≤ (4 / 5 : ℝ) ^ d :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) real_two_rpow_m25_le d
      have h64_nonneg : 0 ≤ 64 * ((128 : ℝ) ^ 2 * GW_K0) ^ ((2 : ℝ) / 5) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (mul_nonneg (by norm_num) gw_K0_pos.le) _)
      calc
        μ j k ≤ 64 * (((Ejk j k).card : ℝ) / (n : ℝ) ^ 2) := hμ_64
        _ ≤ 64 * (((128 : ℝ) ^ 2 * GW_K0) ^ ((2 : ℝ) / 5) * ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d *
              (α j * α k) ^ ((3 : ℝ) / 5)) := by gcongr
        _ = DB_c0 * ((2 : ℝ) ^ (-(2 : ℝ) / 5)) ^ d * (α j * α k) ^ ((3 : ℝ) / 5) := by
              dsimp [DB_c0]; ring
        _ ≤ DB_c0 * (4 / 5 : ℝ) ^ d * (α j * α k) ^ ((3 : ℝ) / 5) := by
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_m25 h64_nonneg)
                (Real.rpow_nonneg hαjk.le _)
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      have h0 : μ j k = 0 := by dsimp [μ]; rw [hEne]; simp
      rw [h0]
      exact mul_nonneg (mul_nonneg (by linarith [DB_c0_ge_one]) (pow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (mul_nonneg (hα0 j) (hα0 k)) _)
  let M : ℕ := S.sup' hSne id
  let J : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hM : ∀ x ∈ S, x ≤ M := fun x hx => Finset.le_sup' id hx
  have hc0_pos : 0 < DB_c0 := lt_of_lt_of_le zero_lt_one DB_c0_ge_one
  have hsmall_row : ∀ (T₁ T₂ : Finset ℕ), T₁ ⊆ S → T₂ ⊆ S →
      (∀ j ∈ T₁, ∀ k ∈ T₂, α j * α k ≤ DB_eta0) →
      (∑ j ∈ T₁, ∑ k ∈ T₂, μ j k) ≤ 1 / 4 := by
    intro T₁ T₂ hT1 hT2 hprod_le
    have hstep1 : (∑ j ∈ T₁, ∑ k ∈ T₂, μ j k) ≤
        (DB_c0 * DB_eta0 ^ ((1 : ℝ) / 10)) *
          ∑ j ∈ T₁, ∑ k ∈ T₂, (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) *
            (Real.sqrt (α j) * Real.sqrt (α k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hbd := hμ_bound j (hT1 hj) k (hT2 hk)
      have hj0 := hα0 j
      have hk0 := hα0 k
      have hjk0 : 0 ≤ α j * α k := mul_nonneg hj0 hk0
      have h10 : (α j * α k) ^ ((1 : ℝ) / 10) ≤ DB_eta0 ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow hjk0 (hprod_le j hj k hk) (by norm_num)
      have hsp : (α j * α k) ^ ((3 : ℝ) / 5) ≤
          DB_eta0 ^ ((1 : ℝ) / 10) * (Real.sqrt (α j) * Real.sqrt (α k)) := by
        have hp' : (α j * α k) ^ ((3 : ℝ) / 5) =
            (α j * α k) ^ ((1 : ℝ) / 10) * (α j * α k) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add' hjk0 (by norm_num)]; norm_num
        rw [hp', ← Real.sqrt_eq_rpow, Real.sqrt_mul hj0]
        exact mul_le_mul_of_nonneg_right h10 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      calc
        μ j k ≤ DB_c0 * (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (α j * α k) ^ ((3 : ℝ) / 5) := hbd
        _ ≤ DB_c0 * (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) *
              (DB_eta0 ^ ((1 : ℝ) / 10) * (Real.sqrt (α j) * Real.sqrt (α k))) := by
            exact mul_le_mul_of_nonneg_left hsp
              (mul_nonneg hc0_pos.le (pow_nonneg (by norm_num) _))
        _ = (DB_c0 * DB_eta0 ^ ((1 : ℝ) / 10)) *
              ((4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k))) := by
            ring
    have hstep2 : (∑ j ∈ T₁, ∑ k ∈ T₂, (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) *
        (Real.sqrt (α j) * Real.sqrt (α k))) ≤ 9 := by
      have hswap : (∑ j ∈ T₁, ∑ k ∈ T₂, (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) *
          (Real.sqrt (α j) * Real.sqrt (α k))) =
          ∑ d ∈ J, (4 / 5 : ℝ) ^ Int.natAbs d *
            ∑ j ∈ T₁, ∑ k ∈ T₂, if d = (j : ℤ) - k then Real.sqrt (α j) * Real.sqrt (α k) else 0 := by
        have hpt : ∀ j ∈ T₁, ∀ k ∈ T₂, (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) *
            (Real.sqrt (α j) * Real.sqrt (α k)) =
            ∑ d ∈ J, if d = (j : ℤ) - k then
              (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 := by
          intro j hj k hk
          have hdJ : (j : ℤ) - k ∈ J := by
            have hjM := hM j (hT1 hj)
            have hkM := hM k (hT2 hk)
            rw [Finset.mem_Icc]
            omega
          rw [Finset.sum_ite_eq' J ((j : ℤ) - k) (fun d =>
            (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k))), if_pos hdJ]
        calc
          _ = ∑ j ∈ T₁, ∑ k ∈ T₂, ∑ d ∈ J, if d = (j : ℤ) - k then
                (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 :=
              Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hpt j hj k hk
          _ = ∑ j ∈ T₁, ∑ d ∈ J, ∑ k ∈ T₂, if d = (j : ℤ) - k then
                (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ d ∈ J, ∑ j ∈ T₁, ∑ k ∈ T₂, if d = (j : ℤ) - k then
                (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
      rw [hswap]
      have hαT1 : (∑ j ∈ T₁, α j) ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg hT1 fun x _ _ => hα0 x).trans_eq hα1
      have hαT2 : (∑ k ∈ T₂, α k) ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg hT2 fun x _ _ => hα0 x).trans_eq hα1
      calc
        (∑ d ∈ J, (4 / 5 : ℝ) ^ Int.natAbs d *
            ∑ j ∈ T₁, ∑ k ∈ T₂, if d = (j : ℤ) - k then Real.sqrt (α j) * Real.sqrt (α k) else 0)
            ≤ ∑ d ∈ J, (4 / 5 : ℝ) ^ Int.natAbs d * 1 := by
              refine Finset.sum_le_sum fun d _ => ?_
              have hcs := sum_shift_sqrt_le T₁ T₂ α α hα0 hα0 d
              have hle1 : Real.sqrt ((∑ j ∈ T₁, α j) * (∑ k ∈ T₂, α k)) ≤ 1 := by
                rw [Real.sqrt_le_one]
                exact mul_le_one₀ hαT1 (Finset.sum_nonneg fun k _ => hα0 k) hαT2
              exact mul_le_mul_of_nonneg_left (hcs.trans hle1) (pow_nonneg (by norm_num) _)
        _ = ∑ d ∈ J, (4 / 5 : ℝ) ^ Int.natAbs d := by simp only [mul_one]
        _ ≤ 9 := sum_geom_Icc_int (by norm_num) le_rfl M
    have hconst : DB_c0 * DB_eta0 ^ ((1 : ℝ) / 10) * 9 = 1 / 4 := by
      rw [DB_eta0_rpow]
      field_simp [hc0_pos.ne']
      ring
    calc
      (∑ j ∈ T₁, ∑ k ∈ T₂, μ j k)
          ≤ (DB_c0 * DB_eta0 ^ ((1 : ℝ) / 10)) * 9 :=
            hstep1.trans (mul_le_mul_of_nonneg_left hstep2
              (mul_nonneg hc0_pos.le (Real.rpow_nonneg DB_eta0_pos.le _)))
      _ = 1 / 4 := hconst
  let S_sm : Finset ℕ := S.filter (fun j => α j < DB_eta0)
  have hbad1 : (∑ j ∈ S_sm, ∑ k ∈ S, μ j k) ≤ 1 / 4 :=
    hsmall_row S_sm S (Finset.filter_subset _ _) Finset.Subset.rfl fun j hj k _ => by
      have hj' := (Finset.mem_filter.mp hj).2.le
      calc
        α j * α k ≤ DB_eta0 * 1 := mul_le_mul hj' (hα_le1 k) (hα0 k) DB_eta0_pos.le
        _ = DB_eta0 := mul_one _
  have hbad2 : (∑ j ∈ S, ∑ k ∈ S_sm, μ j k) ≤ 1 / 4 :=
    hsmall_row S S_sm Finset.Subset.rfl (Finset.filter_subset _ _) fun j _ k hk => by
      have hk' := (Finset.mem_filter.mp hk).2.le
      calc
        α j * α k ≤ 1 * DB_eta0 := mul_le_mul (hα_le1 j) hk' (hα0 k) zero_le_one
        _ = DB_eta0 := one_mul _
  have hbad3 : (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then μ j k else 0) ≤ 1 / 4 := by
    have hstep1 : (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then μ j k else 0) ≤
        DB_c0 * ∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then
          (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      split_ifs with hfar
      · have hbd := hμ_bound j hj k hk
        have hj0 := hα0 j
        have hk0 := hα0 k
        have hjk0 : 0 ≤ α j * α k := mul_nonneg hj0 hk0
        have hjk1 : α j * α k ≤ 1 := mul_le_one₀ (hα_le1 j) hk0 (hα_le1 k)
        have h10 : (α j * α k) ^ ((1 : ℝ) / 10) ≤ 1 := Real.rpow_le_one hjk0 hjk1 (by norm_num)
        have hsp : (α j * α k) ^ ((3 : ℝ) / 5) ≤ Real.sqrt (α j) * Real.sqrt (α k) := by
          have hp' : (α j * α k) ^ ((3 : ℝ) / 5) =
              (α j * α k) ^ ((1 : ℝ) / 10) * (α j * α k) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add' hjk0 (by norm_num)]; norm_num
          rw [hp', ← Real.sqrt_eq_rpow, Real.sqrt_mul hj0]
          exact mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h10
        calc
          μ j k ≤ DB_c0 * (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (α j * α k) ^ ((3 : ℝ) / 5) := hbd
          _ ≤ DB_c0 * (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k)) := by
              exact mul_le_mul_of_nonneg_left hsp (mul_nonneg hc0_pos.le (pow_nonneg (by norm_num) _))
          _ = DB_c0 * ((4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k))) := by
              ring
      · simp
    let J_far : Finset ℤ := J.filter (fun d => DB_K1 < Int.natAbs d)
    have hswap : (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then
        (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k)) else 0) =
        ∑ d ∈ J_far, (4 / 5 : ℝ) ^ Int.natAbs d *
          ∑ j ∈ S, ∑ k ∈ S, if d = (j : ℤ) - k then Real.sqrt (α j) * Real.sqrt (α k) else 0 := by
      have hpt : ∀ j ∈ S, ∀ k ∈ S, (if DB_K1 < Int.natAbs ((j : ℤ) - k) then
          (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k)) else 0) =
          ∑ d ∈ J_far, if d = (j : ℤ) - k then
            (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 := by
        intro j hj k hk
        by_cases hfar : DB_K1 < Int.natAbs ((j : ℤ) - k)
        · have hdJ : (j : ℤ) - k ∈ J_far := by
            have hjM := hM j hj
            have hkM := hM k hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), hfar⟩
          rw [if_pos hfar, Finset.sum_ite_eq' J_far ((j : ℤ) - k) (fun d =>
            (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k))), if_pos hdJ]
        · have hnot : (j : ℤ) - k ∉ J_far := fun hm => hfar (Finset.mem_filter.mp hm).2
          rw [if_neg hfar, Finset.sum_ite_eq' J_far ((j : ℤ) - k) (fun d =>
            (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k))), if_neg hnot]
      calc
        _ = ∑ j ∈ S, ∑ k ∈ S, ∑ d ∈ J_far, if d = (j : ℤ) - k then
              (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 :=
            Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hpt j hj k hk
        _ = ∑ j ∈ S, ∑ d ∈ J_far, ∑ k ∈ S, if d = (j : ℤ) - k then
              (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ d ∈ J_far, ∑ j ∈ S, ∑ k ∈ S, if d = (j : ℤ) - k then
              (4 / 5 : ℝ) ^ Int.natAbs d * (Real.sqrt (α j) * Real.sqrt (α k)) else 0 := Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    have hgeom_far : (∑ d ∈ J_far, (4 / 5 : ℝ) ^ Int.natAbs d) ≤ 18 * (4 / 5 : ℝ) ^ DB_K1 := by
      let J_pos := J_far.filter (fun d : ℤ => (DB_K1 : ℤ) < d)
      let J_neg := J_far.filter (fun d : ℤ => d < -(DB_K1 : ℤ))
      have hcov : J_far = J_pos ∪ J_neg := by
        ext d
        simp only [Finset.mem_union, Finset.mem_filter, J_pos, J_neg, J_far]
        constructor
        · rintro ⟨hJ, hlt⟩
          rcases lt_or_ge d 0 with hd | hd
          · exact Or.inr ⟨⟨hJ, hlt⟩, by omega⟩
          · exact Or.inl ⟨⟨hJ, hlt⟩, by omega⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint J_pos J_neg := by
        rw [Finset.disjoint_left]; intro d h1 h2
        simp only [Finset.mem_filter, J_pos, J_neg] at h1 h2; omega
      have hp1 : (∑ d ∈ J_pos, (4 / 5 : ℝ) ^ Int.natAbs d) ≤ 9 * (4 / 5 : ℝ) ^ DB_K1 := by
        have hinj : Set.InjOn (fun d : ℤ => d - DB_K1) J_pos := fun d₁ _ d₂ _ h => by linarith only [h]
        have himg : J_pos.image (fun d : ℤ => d - DB_K1) ⊆ J := by
          intro d' hd'
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1)
          have h2 := (Finset.mem_filter.mp hd).2
          exact Finset.mem_Icc.mpr (by omega)
        have hrew : (∑ d ∈ J_pos, (4 / 5 : ℝ) ^ Int.natAbs d) =
            (4 / 5 : ℝ) ^ DB_K1 * ∑ d' ∈ J_pos.image (fun d : ℤ => d - DB_K1), (4 / 5 : ℝ) ^ Int.natAbs d' := by
          rw [Finset.sum_image (fun d₁ hd₁ d₂ hd₂ h => hinj hd₁ hd₂ h), Finset.mul_sum]
          refine Finset.sum_congr rfl fun d hd => ?_
          have h2 := (Finset.mem_filter.mp hd).2
          rcases Int.natAbs_eq d with he1 | he1 <;>
            rcases Int.natAbs_eq (d - DB_K1) with he2 | he2 <;>
            have hexp : Int.natAbs d = DB_K1 + Int.natAbs (d - DB_K1) := by omega
          all_goals rw [hexp, pow_add]
        rw [hrew, mul_comm 9 ((4 / 5 : ℝ) ^ DB_K1)]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
        exact (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => pow_nonneg (by norm_num) _)).trans
          (sum_geom_Icc_int (by norm_num) le_rfl M)
      have hp2 : (∑ d ∈ J_neg, (4 / 5 : ℝ) ^ Int.natAbs d) ≤ 9 * (4 / 5 : ℝ) ^ DB_K1 := by
        have hinj : Set.InjOn (fun d : ℤ => d + DB_K1) J_neg := fun d₁ _ d₂ _ h => by linarith only [h]
        have himg : J_neg.image (fun d : ℤ => d + DB_K1) ⊆ J := by
          intro d' hd'
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
          have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1)
          have h2 := (Finset.mem_filter.mp hd).2
          exact Finset.mem_Icc.mpr (by omega)
        have hrew : (∑ d ∈ J_neg, (4 / 5 : ℝ) ^ Int.natAbs d) =
            (4 / 5 : ℝ) ^ DB_K1 * ∑ d' ∈ J_neg.image (fun d : ℤ => d + DB_K1), (4 / 5 : ℝ) ^ Int.natAbs d' := by
          rw [Finset.sum_image (fun d₁ hd₁ d₂ hd₂ h => hinj hd₁ hd₂ h), Finset.mul_sum]
          refine Finset.sum_congr rfl fun d hd => ?_
          have h2 := (Finset.mem_filter.mp hd).2
          rcases Int.natAbs_eq d with he1 | he1 <;>
            rcases Int.natAbs_eq (d + DB_K1) with he2 | he2 <;>
            have hexp : Int.natAbs d = DB_K1 + Int.natAbs (d + DB_K1) := by omega
          all_goals rw [hexp, pow_add]
        rw [hrew, mul_comm 9 ((4 / 5 : ℝ) ^ DB_K1)]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
        exact (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => pow_nonneg (by norm_num) _)).trans
          (sum_geom_Icc_int (by norm_num) le_rfl M)
      nth_rw 1 [hcov]
      rw [Finset.sum_union hdisj]
      linarith only [hp1, hp2]
    have hstep2 : (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then
        (4 / 5 : ℝ) ^ Int.natAbs ((j : ℤ) - k) * (Real.sqrt (α j) * Real.sqrt (α k)) else 0) ≤
        18 * (4 / 5 : ℝ) ^ DB_K1 := by
      rw [hswap]
      calc
        (∑ d ∈ J_far, (4 / 5 : ℝ) ^ Int.natAbs d *
            ∑ j ∈ S, ∑ k ∈ S, if d = (j : ℤ) - k then Real.sqrt (α j) * Real.sqrt (α k) else 0)
            ≤ ∑ d ∈ J_far, (4 / 5 : ℝ) ^ Int.natAbs d * 1 := by
              refine Finset.sum_le_sum fun d _ => ?_
              have hcs := sum_shift_sqrt_le S S α α hα0 hα0 d
              rw [hα1, mul_one, Real.sqrt_one] at hcs
              exact mul_le_mul_of_nonneg_left hcs (pow_nonneg (by norm_num) _)
        _ = ∑ d ∈ J_far, (4 / 5 : ℝ) ^ Int.natAbs d := by simp only [mul_one]
        _ ≤ 18 * (4 / 5 : ℝ) ^ DB_K1 := hgeom_far
    calc
      (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then μ j k else 0)
          ≤ DB_c0 * (18 * (4 / 5 : ℝ) ^ DB_K1) :=
            hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hc0_pos.le)
      _ ≤ DB_c0 * (18 * (1 / (72 * DB_c0))) := by
            gcongr; exact DB_K1_bound
      _ = 1 / 4 := by field_simp [hc0_pos.ne']; ring
  let G : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun jk =>
    DB_eta0 ≤ α jk.1 ∧ DB_eta0 ≤ α jk.2 ∧ Int.natAbs ((jk.1 : ℤ) - jk.2) ≤ DB_K1)
  have hG_mass : 1 / 4 ≤ ∑ jk ∈ G, μ jk.1 jk.2 := by
    have hsplit : (∑ j ∈ S, ∑ k ∈ S, μ j k) ≤
        (∑ jk ∈ G, μ jk.1 jk.2) +
        (∑ j ∈ S_sm, ∑ k ∈ S, μ j k) +
        (∑ j ∈ S, ∑ k ∈ S_sm, μ j k) +
        (∑ j ∈ S, ∑ k ∈ S, if DB_K1 < Int.natAbs ((j : ℤ) - k) then μ j k else 0) := by
      have hG_eq : (∑ jk ∈ G, μ jk.1 jk.2) =
          ∑ j ∈ S, ∑ k ∈ S,
            if DB_eta0 ≤ α j ∧ DB_eta0 ≤ α k ∧ Int.natAbs ((j : ℤ) - k) ≤ DB_K1 then μ j k else 0 := by
        dsimp [G]
        rw [Finset.sum_filter, ← Finset.sum_product']
      have h1_eq : (∑ j ∈ S_sm, ∑ k ∈ S, μ j k) =
          ∑ j ∈ S, ∑ k ∈ S, if α j < DB_eta0 then μ j k else 0 := by
        have hrow : (∑ j ∈ S_sm, ∑ k ∈ S, μ j k) =
            ∑ j ∈ S, if α j < DB_eta0 then ∑ k ∈ S, μ j k else 0 := by
          dsimp [S_sm]; rw [Finset.sum_filter]
        rw [hrow]
        refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
      have h2_eq : (∑ j ∈ S, ∑ k ∈ S_sm, μ j k) =
          ∑ j ∈ S, ∑ k ∈ S, if α k < DB_eta0 then μ j k else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [S_sm]; rw [Finset.sum_filter]
      rw [hG_eq, h1_eq, h2_eq]
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
      have h0 := hμ0 j k
      by_cases hgood : DB_eta0 ≤ α j ∧ DB_eta0 ≤ α k ∧ Int.natAbs ((j : ℤ) - k) ≤ DB_K1
      · rw [if_pos hgood]; split_ifs <;> linarith
      · rw [if_neg hgood]
        by_cases h1 : α j < DB_eta0
        · rw [if_pos h1]; split_ifs <;> linarith
        · by_cases h2 : α k < DB_eta0
          · rw [if_neg h1, if_pos h2]; split_ifs <;> linarith
          · have h3 : DB_K1 < Int.natAbs ((j : ℤ) - k) := by
              push Not at hgood h1 h2
              exact hgood h1 h2
            rw [if_neg h1, if_neg h2, if_pos h3]
            linarith
    linarith only [hμ1, hsplit, hbad1, hbad2, hbad3]
  let S_lg : Finset ℕ := S.filter (fun j => DB_eta0 ≤ α j)
  have hSlg_card : (S_lg.card : ℝ) ≤ 1 / DB_eta0 := by
    have h1 : (S_lg.card : ℝ) * DB_eta0 ≤ ∑ j ∈ S_lg, α j := by
      calc
        (S_lg.card : ℝ) * DB_eta0 = ∑ _j ∈ S_lg, DB_eta0 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ S_lg, α j := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
    have h2 : (∑ j ∈ S_lg, α j) ≤ ∑ j ∈ S, α j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hα0 x
    rw [le_div_iff₀ DB_eta0_pos]
    linarith only [h1, h2, hα1]
  have hG_sub : G ⊆ S_lg ×ˢ S_lg := by
    intro jk hjk
    have h1 := (Finset.mem_filter.mp hjk).1
    have h2 := (Finset.mem_filter.mp hjk).2
    have hm := Finset.mem_product.mp h1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, h2.1⟩,
      Finset.mem_filter.mpr ⟨hm.2, h2.2.1⟩⟩
  have hG_card : (G.card : ℝ) ≤ (1 / DB_eta0) ^ 2 := by
    have h1 : G.card ≤ S_lg.card * S_lg.card :=
      (Finset.card_le_card hG_sub).trans_eq (Finset.card_product _ _)
    have h2 : (G.card : ℝ) ≤ (S_lg.card : ℝ) * (S_lg.card : ℝ) := by exact_mod_cast h1
    calc
      (G.card : ℝ) ≤ (S_lg.card : ℝ) * (S_lg.card : ℝ) := h2
      _ ≤ (1 / DB_eta0) * (1 / DB_eta0) :=
          mul_le_mul hSlg_card hSlg_card (Nat.cast_nonneg _) (div_nonneg zero_le_one DB_eta0_pos.le)
      _ = (1 / DB_eta0) ^ 2 := (sq _).symm
  have hjk0_ex : ∃ jk ∈ G, DB_eta0 ^ 2 / 4 ≤ μ jk.1 jk.2 := by
    by_contra hno
    push Not at hno
    by_cases hGe : G = ∅
    · rw [hGe, Finset.sum_empty] at hG_mass; norm_num at hG_mass
    · have hGne : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hGe
      have hlt : (∑ jk ∈ G, μ jk.1 jk.2) < ∑ _jk ∈ G, (DB_eta0 ^ 2 / 4) :=
        Finset.sum_lt_sum_of_nonempty hGne hno
      have hrhs : (∑ _jk ∈ G, (DB_eta0 ^ 2 / 4)) = (G.card : ℝ) * (DB_eta0 ^ 2 / 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hrhs2 : (G.card : ℝ) * (DB_eta0 ^ 2 / 4) ≤ 1 / 4 := by
        calc
          (G.card : ℝ) * (DB_eta0 ^ 2 / 4) ≤ (1 / DB_eta0) ^ 2 * (DB_eta0 ^ 2 / 4) :=
            mul_le_mul_of_nonneg_right hG_card (div_nonneg (sq_nonneg _) (by norm_num))
          _ = 1 / 4 := by field_simp [DB_eta0_pos.ne']
      linarith only [hG_mass, hlt, hrhs, hrhs2]
  obtain ⟨⟨j₀, k₀⟩, hjk₀, hμ₀_ge⟩ := hjk0_ex
  have hjk_mem := Finset.mem_filter.mp hjk₀
  have hηj₀ : DB_eta0 ≤ α j₀ := hjk_mem.2.1
  have hηk₀ : DB_eta0 ≤ α k₀ := hjk_mem.2.2.1
  have hEjk_pos : (0 : ℝ) < (Ejk j₀ k₀).card := by
    have : 0 < μ j₀ k₀ := lt_of_lt_of_le (div_pos (pow_pos DB_eta0_pos 2) (by norm_num)) hμ₀_ge
    dsimp [μ] at this
    exact (div_pos_iff_of_pos_right hEsymR).mp this
  have hEjk_ne : (Ejk j₀ k₀).Nonempty := Finset.card_pos.mp (by exact_mod_cast hEjk_pos)
  have hXj₀_ne : (Vk j₀).Nonempty := by
    obtain ⟨xy, hxy⟩ := hEjk_ne
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1
    exact ⟨xy.1, Finset.mem_filter.mpr ⟨hm.1, (Finset.mem_filter.mp hxy).2.1⟩⟩
  have hYk₀_ne : (Vk k₀).Nonempty := by
    obtain ⟨xy, hxy⟩ := hEjk_ne
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1
    exact ⟨xy.2, Finset.mem_filter.mpr ⟨hm.2, (Finset.mem_filter.mp hxy).2.2⟩⟩
  let A₀ : ℝ := (2 : ℝ) ^ j₀
  let B₀ : ℝ := (2 : ℝ) ^ k₀
  let D₀ : ℝ := max A₀ B₀ / (128 * (n : ℝ))
  have hA0 : 0 < A₀ := pow_pos (by norm_num) j₀
  have hB0 : 0 < B₀ := pow_pos (by norm_num) k₀
  have hD0 : 0 < D₀ := div_pos (lt_of_lt_of_le hA0 (le_max_left _ _)) (mul_pos (by norm_num) hnR)
  let st₀ : GWState (Vk j₀) (Vk k₀) A₀ B₀ D₀ :=
    { X := Vk j₀
      Y := Vk k₀
      E := Ejk j₀ k₀
      sX := 1
      sY := 1
      sD := 1
      hsX := zero_lt_one
      hsY := zero_lt_one
      hsD := zero_lt_one
      hXne := hXj₀_ne
      hYne := hYk₀_ne
      hXpos := fun x hx => hVpos x (Finset.mem_filter.mp hx).1
      hYpos := fun y hy => hVpos y (Finset.mem_filter.mp hy).1
      hEne := hEjk_ne
      hEsub := fun xy hxy => by
        have h1 := Finset.mem_filter.mp hxy
        have hm := Finset.mem_product.mp (Finset.mem_filter.mp h1.1).1
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, h1.2.1⟩,
          Finset.mem_filter.mpr ⟨hm.2, h1.2.2⟩⟩
      hXrng := fun x hx => by simpa only [Nat.cast_one, div_one] using hVk_rng j₀ x hx
      hYrng := fun y hy => by simpa only [Nat.cast_one, div_one] using hVk_rng k₀ y hy
      hEgcd := fun xy hxy => by
        have h1 := Finset.mem_filter.mp hxy
        have hsym := Finset.mem_filter.mp h1.1
        have hm := Finset.mem_product.mp hsym.1
        have hx_rng := hVk_rng j₀ xy.1 (Finset.mem_filter.mpr ⟨hm.1, h1.2.1⟩)
        have hy_rng := hVk_rng k₀ xy.2 (Finset.mem_filter.mpr ⟨hm.2, h1.2.2⟩)
        have hmax_le : max A₀ B₀ ≤ (max xy.1 xy.2 : ℝ) := max_le_max hx_rng.1 hy_rng.1
        have hgcd_ge : (max xy.1 xy.2 : ℝ) ≤ 64 * (n : ℝ) * Nat.gcd xy.1 xy.2 := by
          exact_mod_cast hsym.2.2
        have h2D : 2 * D₀ ≤ Nat.gcd xy.1 xy.2 := by
          dsimp [D₀]
          rw [show 2 * (max A₀ B₀ / (128 * (n : ℝ))) = max A₀ B₀ / (64 * (n : ℝ)) by ring,
            div_le_iff₀ (mul_pos (by norm_num) hnR)]
          linarith only [hmax_le, hgcd_ge]
        rw [Nat.cast_one, div_one]
        linarith only [hD0, h2D]
      hYmap := fun y hy => by simpa only [mul_one] using hy
      hXcard := le_rfl
      hYcard := le_rfl }
  have hF0_le : DB_F0 ≤ F_val (8 / 3 : ℝ) (1 / 15 : ℝ) st₀ := by
    have hsm_le : smallPrimes st₀ ≤ p0 + 1 := by
      unfold smallPrimes
      have hsub : (primesOf (st₀.X ∪ st₀.Y)).filter (· ≤ p0) ⊆ Finset.range (p0 + 1) := by
        intro p hp; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have h1000_ge : ((1000 : ℝ)⁻¹) ^ (p0 + 1) ≤ ((1000 : ℝ)⁻¹) ^ smallPrimes st₀ :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsm_le
    have hEjk_ge : DB_eta0 ^ 2 / 256 * (n : ℝ) ^ 2 ≤ (Ejk j₀ k₀).card := by
      have hn2R : (n : ℝ) ^ 2 ≤ 64 * (E_sym.card : ℝ) := by exact_mod_cast hn2_Esym
      have h1 : DB_eta0 ^ 2 / 4 * (E_sym.card : ℝ) ≤ (Ejk j₀ k₀).card := by
        dsimp [μ] at hμ₀_ge
        rwa [le_div_iff₀ hEsymR] at hμ₀_ge
      calc
        DB_eta0 ^ 2 / 256 * (n : ℝ) ^ 2 ≤ DB_eta0 ^ 2 / 256 * (64 * (E_sym.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hn2R (div_nonneg (sq_nonneg _) (by norm_num))
        _ = DB_eta0 ^ 2 / 4 * (E_sym.card : ℝ) := by ring
        _ ≤ (Ejk j₀ k₀).card := h1
    have hVkj_le : ((Vk j₀).card : ℝ) ≤ n := by
      rw [← hVcard]; exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hVkk_le : ((Vk k₀).card : ℝ) ≤ n := by
      rw [← hVcard]; exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hρ_ge : DB_eta0 ^ 2 / 256 ≤ ((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ))) := by
      have hxy_le : (st₀.X.card : ℝ) * (st₀.Y.card : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          (st₀.X.card : ℝ) * (st₀.Y.card : ℝ) = ((Vk j₀).card : ℝ) * (Vk k₀).card := rfl
          _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul hVkj_le hVkk_le (Nat.cast_nonneg _) hnR.le
          _ = (n : ℝ) ^ 2 := (sq _).symm
      have hX_pos : (0 : ℝ) < st₀.X.card := by exact_mod_cast st₀.hXne.card_pos
      have hY_pos : (0 : ℝ) < st₀.Y.card := by exact_mod_cast st₀.hYne.card_pos
      rw [le_div_iff₀ (mul_pos hX_pos hY_pos)]
      calc
        DB_eta0 ^ 2 / 256 * ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ))
            ≤ DB_eta0 ^ 2 / 256 * (n : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hxy_le (div_nonneg (sq_nonneg _) (by norm_num))
        _ ≤ (Ejk j₀ k₀).card := hEjk_ge
        _ = st₀.E.card := rfl
    have hab_ratio : DB_eta0 ^ 2 / 128 ^ 2 ≤
        ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ)) *
          ((D₀ / (st₀.sD : ℝ)) ^ 2 / ((A₀ / (st₀.sX : ℝ)) * (B₀ / (st₀.sY : ℝ)))) := by
      have h2d : (1 : ℝ) ≤ (2 : ℝ) ^ Int.natAbs ((j₀ : ℤ) - k₀) := one_le_pow₀ (by norm_num)
      have hDr : (D₀ / (st₀.sD : ℝ)) ^ 2 / ((A₀ / (st₀.sX : ℝ)) * (B₀ / (st₀.sY : ℝ))) =
          (2 : ℝ) ^ Int.natAbs ((j₀ : ℤ) - k₀) / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        have hcast1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
        change (D₀ / ((1 : ℕ) : ℝ)) ^ 2 / ((A₀ / ((1 : ℕ) : ℝ)) * (B₀ / ((1 : ℕ) : ℝ))) = _
        rw [hcast1, div_one, div_one, div_one]
        dsimp [D₀, A₀, B₀]
        rw [div_pow, mul_pow, ← dyadic_max_ratio j₀ k₀]
        ring
      have hX_ge : DB_eta0 * n ≤ st₀.X.card := by
        change DB_eta0 * n ≤ (Vk j₀).card
        rw [← le_div_iff₀ hnR]; exact hηj₀
      have hY_ge : DB_eta0 * n ≤ st₀.Y.card := by
        change DB_eta0 * n ≤ (Vk k₀).card
        rw [← le_div_iff₀ hnR]; exact hηk₀
      rw [hDr]
      calc
        DB_eta0 ^ 2 / 128 ^ 2 = (DB_eta0 * n) * (DB_eta0 * n) * (1 / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2)) := by
          field_simp [hnR.ne']
        _ ≤ ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ)) *
              ((2 : ℝ) ^ Int.natAbs ((j₀ : ℤ) - k₀) / ((128 : ℝ) ^ 2 * (n : ℝ) ^ 2)) := by
            refine mul_le_mul
              (mul_le_mul hX_ge hY_ge (mul_nonneg DB_eta0_pos.le hnR.le) (Nat.cast_nonneg _))
              (div_le_div_of_nonneg_right h2d (by positivity))
              (div_nonneg zero_le_one (by positivity))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hz_eq : ((st₀.X.card : ℝ) * st₀.Y.card) / ((st₀.X.card : ℝ) * st₀.Y.card) = 1 := by
      have hX_pos : (0 : ℝ) < st₀.X.card := by exact_mod_cast st₀.hXne.card_pos
      have hY_pos : (0 : ℝ) < st₀.Y.card := by exact_mod_cast st₀.hYne.card_pos
      exact div_self (mul_pos hX_pos hY_pos).ne'
    unfold F_val DB_F0; dsimp only
    change _ ≤ (((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ))) ^ ((8 : ℝ) / 3) *
        st₀.X.card * st₀.Y.card *
        ((D₀ / (st₀.sD : ℝ)) ^ 2 / ((A₀ / (st₀.sX : ℝ)) * (B₀ / (st₀.sY : ℝ)))) *
        (((st₀.X.card : ℝ) * st₀.Y.card) / ((Vk j₀).card * (Vk k₀).card)) ^ ((1 : ℝ) / 15) *
        ((1000 : ℝ)⁻¹) ^ smallPrimes st₀)
    have hz1' : (((st₀.X.card : ℝ) * st₀.Y.card) / ((Vk j₀).card * (Vk k₀).card)) ^ ((1 : ℝ) / 15) = 1 := by
      have heq1 : ((st₀.X.card : ℝ) * st₀.Y.card) / ((Vk j₀).card * (Vk k₀).card) = 1 := hz_eq
      rw [heq1, Real.one_rpow]
    rw [hz1', mul_one]
    have hρ_pow : (DB_eta0 ^ 2 / 256) ^ ((8 : ℝ) / 3) ≤
        ((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ))) ^ ((8 : ℝ) / 3) :=
      Real.rpow_le_rpow (div_nonneg (sq_nonneg _) (by norm_num)) hρ_ge (by norm_num)
    have hmain_prod : (DB_eta0 ^ 2 / 256) ^ ((8 : ℝ) / 3) * (DB_eta0 ^ 2 / 128 ^ 2) ≤
        ((st₀.E.card : ℝ) / ((st₀.X.card : ℝ) * (st₀.Y.card : ℝ))) ^ ((8 : ℝ) / 3) *
          st₀.X.card * st₀.Y.card *
          ((D₀ / (st₀.sD : ℝ)) ^ 2 / ((A₀ / (st₀.sX : ℝ)) * (B₀ / (st₀.sY : ℝ)))) := by
      have h1 := mul_le_mul hρ_pow hab_ratio (div_nonneg (sq_nonneg _) (by norm_num))
        (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _)
      linarith only [h1]
    exact mul_le_mul hmain_prod h1000_ge (pow_nonneg (by norm_num) _)
      (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) (div_nonneg (sq_nonneg _) (mul_nonneg (div_nonneg hA0.le (Nat.cast_nonneg _))
        (div_nonneg hB0.le (Nat.cast_nonneg _)))))
  obtain ⟨UN, hUN_sub, _, hUN_card, ξ, A_box, B_box, hξ, hAb, hBb, harea, hrepr⟩ :=
    gw_box_extraction hXj₀_ne.card_pos hYk₀_ne.card_pos hA0 hB0 hD0 st₀ DB_F0 DB_F0_pos hF0_le
  have hUN_V : UN ⊆ V := hUN_sub.trans (Finset.filter_subset _ _)
  let U : Finset (Fin n) := Finset.univ.filter (fun i => v i ∈ UN)
  have himg_eq : U.image v = UN := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, U]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hUN_V hx)
      exact ⟨i, hx, rfl⟩
  have hU_card : U.card = UN.card := by
    rw [← himg_eq]
    exact (Finset.card_image_of_injective U v.injective).symm
  refine ⟨U, ξ, A_box, B_box, ?_, hξ, hAb, hBb, ?_, ?_⟩
  · have hVk_ge : DB_eta0 * n ≤ (Vk k₀).card := by
      rw [← le_div_iff₀ hnR]; exact hηk₀
    have hcoeff_nn : 0 ≤ (1 / 4 : ℝ) * (DB_F0 / 1024) ^ ((33 : ℝ) / 2) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg DB_F0_pos.le (by norm_num)) _)
    rw [hU_card]
    calc
      DB_theta * n = ((1 / 4 : ℝ) * (DB_F0 / 1024) ^ ((33 : ℝ) / 2)) * (DB_eta0 * n) := by
        dsimp [DB_theta]; ring
      _ ≤ ((1 / 4 : ℝ) * (DB_F0 / 1024) ^ ((33 : ℝ) / 2)) * ((Vk k₀).card : ℝ) :=
          mul_le_mul_of_nonneg_left hVk_ge hcoeff_nn
      _ ≤ UN.card := hUN_card
  · rw [hU_card]
    have hC : 400 / DB_F0 ≤ DB_Cbox := le_max_right _ _
    exact harea.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))
  · intro i hi
    exact hrepr (v i) (Finset.mem_filter.mp hi).2

end Part34

theorem OMA.solution :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1.H1 := by
  unfold OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1.H1
  obtain ⟨D, η, hD_pos, hη_pos, hrb⟩ := rational_box_matching DB_Cbox DB_Cbox_ge_one
  let N₀ : ℕ := Nat.ceil (2 / DB_theta) + 2
  have hN0_pos : 0 < N₀ := Nat.succ_pos _
  let k_large : ℝ := (η * DB_theta) / D
  let k_small : ℝ := 1 / ((N₀ : ℝ) * (64 * (N₀ : ℝ)))
  have hk_pos : 0 < min k_large k_small := by
    refine lt_min (div_pos (mul_pos hη_pos DB_theta_pos) (by exact_mod_cast hD_pos)) ?_
    have hN0R : (0 : ℝ) < N₀ := by exact_mod_cast hN0_pos
    exact div_pos zero_lt_one (mul_pos hN0R (mul_pos (by norm_num) hN0R))
  refine ⟨min k_large k_small, hk_pos, ?_⟩
  intro n hn v hv hdense
  dsimp only
  by_cases hn_large : N₀ ≤ n
  · obtain ⟨U, ξ, A, B, hU_frac, hξ, hA, hB, harea, hrepr⟩ :=
      dyadic_box_extraction n hn v hv hdense
    have h2_le_U : 2 ≤ U.card := by
      have h1 : (2 : ℝ) ≤ DB_theta * n := by
        have hceil : 2 / DB_theta ≤ (N₀ : ℝ) := by
          have := Nat.le_ceil (2 / DB_theta)
          dsimp [N₀]; push_cast; linarith
        have hN0n : (N₀ : ℝ) ≤ n := by exact_mod_cast hn_large
        have h2n : 2 / DB_theta ≤ n := hceil.trans hN0n
        rw [div_le_iff₀ DB_theta_pos] at h2n
        linarith only [h2n]
      have h2 : (2 : ℝ) ≤ U.card := h1.trans hU_frac
      exact_mod_cast h2
    obtain ⟨m, e, hm_ge, he_pairs⟩ := hrb n v hv U h2_le_U ξ A B hξ hA hB harea hrepr
    have hmatch := matching_overlap_lower_bound hn v hv hD_pos e
      (fun p => (he_pairs p).2.2)
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD_pos
    have hk_le : k_large ≤ (m : ℝ) / ((n : ℝ) * D) := by
      have hmn : η * DB_theta * n ≤ m := by
        calc
          η * DB_theta * n = η * (DB_theta * n) := by ring
          _ ≤ η * U.card := mul_le_mul_of_nonneg_left hU_frac hη_pos.le
          _ ≤ m := hm_ge
      dsimp [k_large]
      rw [div_le_div_iff₀ hDR (mul_pos hn_pos hDR)]
      calc
        η * DB_theta * ((n : ℝ) * D) = (η * DB_theta * n) * D := by ring
        _ ≤ (m : ℝ) * D := mul_le_mul_of_nonneg_right hmn hDR.le
    exact (min_le_left _ _).trans (hk_le.trans hmatch)
  · have hlt : n < N₀ := Nat.not_le.mp hn_large
    let E_full := (Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
      ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64 * n * Nat.gcd (v ij.1) (v ij.2)
    have hEne : E_full.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      have hle := hdense
      change n ^ 2 ≤ 64 * E_full.card at hle
      rw [h0, Finset.card_empty, mul_zero] at hle
      have : 4 ≤ n ^ 2 := by nlinarith
      omega
    obtain ⟨ij, hij⟩ := hEne
    have hspec := (Finset.mem_filter.mp hij).2
    have hne : ij.2 ≠ ij.1 := hspec.1.ne'
    have hheight : max (v ij.1) (v ij.2) ≤ (64 * N₀) * Nat.gcd (v ij.1) (v ij.2) := by
      have h1 : 64 * n ≤ 64 * N₀ := Nat.mul_le_mul_left 64 hlt.le
      exact hspec.2.trans (Nat.mul_le_mul_right _ h1)
    have hpair := pair_overlap_lower_bound n (v ij.1) (v ij.2) (64 * N₀) hn
      (hv ij.1) (hv ij.2) (Nat.mul_pos (by norm_num) hN0_pos) hheight
    let F (i : Fin n) : ℝ := MeasureTheory.volume.real
      (((fun t : UnitAddCircle => (v i : ℤ) • t) ⁻¹' Metric.closedBall 0 (1 / (2 * (n : ℝ)))) ∩
        ⋃ j, ⋃ (_ : j ≠ i), (fun t : UnitAddCircle => (v j : ℤ) • t) ⁻¹'
          Metric.closedBall 0 (1 / (2 * (n : ℝ))))
    have hmono : MeasureTheory.volume.real
        (((fun t : UnitAddCircle => (v ij.1 : ℤ) • t) ⁻¹'
            Metric.closedBall 0 (1 / (2 * (n : ℝ)))) ∩
          ((fun t : UnitAddCircle => (v ij.2 : ℤ) • t) ⁻¹'
            Metric.closedBall 0 (1 / (2 * (n : ℝ))))) ≤
        F ij.1 := by
      refine MeasureTheory.measureReal_mono ?_ (by finiteness)
      rintro t ⟨ht1, ht2⟩
      exact ⟨ht1, Set.mem_iUnion.mpr ⟨ij.2, Set.mem_iUnion.mpr ⟨hne, ht2⟩⟩⟩
    have hsum : F ij.1 ≤ ∑ i : Fin n, F i :=
      Finset.single_le_sum (f := F) (fun _ _ => MeasureTheory.measureReal_nonneg) (Finset.mem_univ ij.1)
    have hks : k_small ≤ 1 / ((n : ℝ) * ((64 * N₀ : ℕ) : ℝ)) := by
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hN0R : (0 : ℝ) < N₀ := by exact_mod_cast hN0_pos
      have h64N0 : (0 : ℝ) < 64 * (N₀ : ℝ) := mul_pos (by norm_num) hN0R
      have hleR : (n : ℝ) ≤ N₀ := by exact_mod_cast hlt.le
      dsimp [k_small]
      push_cast
      exact one_div_le_one_div_of_le (mul_pos hn_pos h64N0) (mul_le_mul_of_nonneg_right hleR h64N0.le)
    exact (min_le_right _ _).trans (hks.trans (hpair.trans (hmono.trans hsum)))
