import OMAReductions.R_Erdos1204_erdos_1204_variants_A_lower_R1
import Mathlib

/-!
Step Erdos1204.erdos_1204.variants.A_lower.R1.H2:
Lower bound on the Selberg sieve denominator over squarefree integers up to `z`
via the harmonic sum and prime-power fiber decomposition by squarefree radicals.
-/

open scoped Classical BigOperators

lemma swarm_harmonic_log_le (z : ℕ) :
    Real.log ((z : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / n := by
  induction z with
  | zero =>
    simp
  | succ z ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 z)]
    push_cast
    have hpos : (0 : ℝ) < (z : ℝ) + 1 := by positivity
    have hpos2 : (0 : ℝ) < (z : ℝ) + 1 + 1 := by positivity
    have hlog : Real.log (((z : ℝ) + 1 + 1) / ((z : ℝ) + 1)) ≤
        ((z : ℝ) + 1 + 1) / ((z : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hpos2 hpos)
    rw [Real.log_div hpos2.ne' hpos.ne',
      add_div ((z : ℝ) + 1) 1 ((z : ℝ) + 1), div_self hpos.ne'] at hlog
    linarith

lemma swarm_totient_eq (d : ℕ) (hd : Squarefree d) :
    (1 / (d : ℝ)) * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) =
      (1 : ℝ) / d.totient := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hd_real : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have htot0 : (d.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)).ne'
  have h_real : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hq := congr_arg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors d)
    push_cast at hq
    exact hq
  have h_prod :
      (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
        (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h_inv : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by
      rw [sub_div, div_self hp0, one_div]
    rw [h_inv, div_mul_div_comm, mul_comm ((p : ℝ) - 1) (p : ℝ), div_self (mul_ne_zero hp0 hp1)]
  rw [eq_div_iff htot0]
  calc
    ((1 / (d : ℝ)) * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) * (d.totient : ℝ)
        = ((1 / (d : ℝ)) * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
            ((d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)) := by rw [h_real]
    _ = ((1 / (d : ℝ)) * (d : ℝ)) *
          ((∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
            ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)) := by ring
    _ = 1 * 1 := by rw [one_div_mul_cancel hd_real, h_prod]
    _ = 1 := mul_one 1

lemma swarm_radical_squarefree (n : ℕ) : Squarefree (∏ p ∈ n.primeFactors, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdvd
  have hq1 : q ∣ ∏ p ∈ n.primeFactors, p := dvd_trans (dvd_mul_right q q) hdvd
  obtain ⟨p, hp_mem, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime id).mp hq1
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hqp_eq : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left hq.ne_one
  have hq_mem : q ∈ n.primeFactors := hqp_eq ▸ hp_mem
  rw [← Finset.mul_prod_erase n.primeFactors (fun p => p) hq_mem] at hdvd
  have hq2 : q ∣ ∏ p ∈ n.primeFactors.erase q, p :=
    (mul_dvd_mul_iff_left hq.ne_zero).mp hdvd
  obtain ⟨p', hp'_mem, hqp'⟩ := (Prime.dvd_finsetProd_iff hq.prime id).mp hq2
  obtain ⟨hne, hp'_pf⟩ := Finset.mem_erase.mp hp'_mem
  have hp' : Nat.Prime p' := Nat.prime_of_mem_primeFactors hp'_pf
  have hqp'_eq : q = p' := ((Nat.dvd_prime hp').mp hqp').resolve_left hq.ne_one
  exact hne hqp'_eq.symm

lemma swarm_radical_mul_cofactor {n : ℕ} (hn : n ≠ 0) :
    n = (∏ p ∈ n.primeFactors, p) * (∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1)) := by
  have hprod : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    rw [← Nat.support_factorization]
    exact Nat.prod_factorization_pow_eq_self hn
  conv_lhs => rw [← hprod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpos : 1 ≤ n.factorization p := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
    omega
  conv_lhs => rw [show n.factorization p = (n.factorization p - 1) + 1 by omega]
  rw [pow_succ']

lemma swarm_radical_primeFactors (n : ℕ) :
    (∏ p ∈ n.primeFactors, p).primeFactors = n.primeFactors := by
  have hd_pos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  ext q
  constructor
  · intro hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨p, hp_mem, hqp⟩ := (Prime.dvd_finsetProd_iff hq_prime.prime id).mp hq_dvd
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
    have hqp_eq : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left hq_prime.ne_one
    exact hqp_eq ▸ hp_mem
  · intro hq
    exact Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hq, Finset.dvd_prod_of_mem id hq, hd_pos.ne'⟩

lemma swarm_radical_exp_lt {n z : ℕ} (hn1 : 1 ≤ n) (hnz : n ≤ z) (p : ℕ) :
    n.factorization p - 1 < z + 1 := by
  by_cases hk : n.factorization p = 0
  · omega
  · have hp_mem : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      exact hk
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
    have hlt2 : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
    have h2p : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) :=
      Nat.pow_le_pow_left hp.two_le _
    have hpn : p ^ (n.factorization p) ≤ n :=
      Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
    omega

lemma swarm_radical_geom_le {p : ℕ} (hp : Nat.Prime p) (z : ℕ) :
    (∑ k ∈ Finset.range (z + 1), ((1 : ℝ) / p) ^ k) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hgeom : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, ((1 : ℝ) / p) ^ k) * (1 - (1 : ℝ) / p) =
        1 - ((1 : ℝ) / p) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpow : 0 ≤ ((1 : ℝ) / p) ^ (z + 1) := by positivity
  have hle1 : (∑ k ∈ Finset.range (z + 1), ((1 : ℝ) / p) ^ k) * (1 - (1 : ℝ) / p) ≤ 1 := by
    rw [hgeom (z + 1)]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hle1 (show 0 ≤ (p : ℝ) / ((p : ℝ) - 1) by positivity)
  have hinv : (1 - (1 : ℝ) / p) * ((p : ℝ) / ((p : ℝ) - 1)) = 1 := by
    field_simp
  rw [mul_assoc, hinv, mul_one, one_mul] at hmul
  exact hmul

lemma swarm_radical_fiber_le (d z : ℕ) :
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => (∏ p ∈ n.primeFactors, p) = d), (1 : ℝ) / n) ≤
      (1 / (d : ℝ)) * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
  let A := (Finset.Icc 1 z).filter (fun n => (∏ p ∈ n.primeFactors, p) = d)
  let e : ℕ → (∀ _ : d.primeFactors, Fin (z + 1)) :=
    fun n p =>
      if h : n.factorization p.1 - 1 < z + 1 then ⟨n.factorization p.1 - 1, h⟩
      else ⟨0, Nat.succ_pos z⟩
  let g : (∀ _ : d.primeFactors, Fin (z + 1)) → ℝ :=
    fun f => ∏ p : d.primeFactors, ((1 : ℝ) / p.1) ^ (f p : ℕ)
  have hdecomp : ∀ n ∈ A, n = d * ∏ p : d.primeFactors, (p.1) ^ (e n p : ℕ) := by
    intro n hn
    obtain ⟨hnIcc, hrad⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hnIcc
    have hn0 : n ≠ 0 := by omega
    have hpf : n.primeFactors = d.primeFactors := by
      rw [← hrad, swarm_radical_primeFactors]
    have hmul := swarm_radical_mul_cofactor hn0
    rw [hrad, hpf] at hmul
    have he_val : ∀ p : d.primeFactors, (e n p : ℕ) = n.factorization p.1 - 1 := by
      intro p
      dsimp [e]
      rw [dif_pos (swarm_radical_exp_lt hn1 hnz p.1)]
    have hprod_eq : (∏ p : d.primeFactors, (p.1) ^ (e n p : ℕ)) =
        ∏ p : d.primeFactors, (p.1) ^ (n.factorization p.1 - 1) :=
      Finset.prod_congr rfl fun p _ => by rw [he_val p]
    have hcoe : (∏ p : d.primeFactors, (p.1) ^ (n.factorization p.1 - 1)) =
        ∏ p ∈ d.primeFactors, p ^ (n.factorization p - 1) :=
      Finset.prod_coe_sort d.primeFactors (fun p => p ^ (n.factorization p - 1))
    rw [hprod_eq, hcoe]
    exact hmul
  have he_inj : Set.InjOn e A := by
    intro n₁ hn₁ n₂ hn₂ heq
    rw [hdecomp n₁ hn₁, hdecomp n₂ hn₂, heq]
  have hterm : ∀ n ∈ A, (1 : ℝ) / n = (1 / (d : ℝ)) * g (e n) := by
    intro n hn
    have h := congrArg (fun m : ℕ => (m : ℝ)) (hdecomp n hn)
    dsimp at h
    rw [h]
    dsimp [g]
    simp only [one_div, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, mul_inv,
      Finset.prod_inv_distrib, inv_pow]
  have hsum_eq : (∑ n ∈ A, (1 : ℝ) / n) = (1 / (d : ℝ)) * ∑ n ∈ A, g (e n) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  change (∑ n ∈ A, (1 : ℝ) / n) ≤ _
  rw [hsum_eq]
  have hd_nonneg : 0 ≤ 1 / (d : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hd_nonneg
  have himg : ∑ n ∈ A, g (e n) = ∑ f ∈ A.image e, g f :=
    (Finset.sum_image he_inj).symm
  have hg_nonneg : ∀ f ∈ (Finset.univ : Finset (∀ _ : d.primeFactors, Fin (z + 1))),
      f ∉ A.image e → 0 ≤ g f := by
    intro f _ _
    exact Finset.prod_nonneg fun p _ => by positivity
  have hleB : ∑ f ∈ A.image e, g f ≤ ∑ f : (∀ _ : d.primeFactors, Fin (z + 1)), g f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) hg_nonneg
  have hprod_sum : (∑ f : (∀ _ : d.primeFactors, Fin (z + 1)), g f) =
      ∏ p : d.primeFactors, ∑ k : Fin (z + 1), ((1 : ℝ) / p.1) ^ (k : ℕ) :=
    (Fintype.prod_sum
      (fun (p : d.primeFactors) (k : Fin (z + 1)) => ((1 : ℝ) / p.1) ^ (k : ℕ))).symm
  have hprod_le :
      (∏ p : d.primeFactors, ∑ k : Fin (z + 1), ((1 : ℝ) / p.1) ^ (k : ℕ)) ≤
        ∏ p : d.primeFactors, ((p.1 : ℝ) / ((p.1 : ℝ) - 1)) := by
    refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
    · exact Finset.sum_nonneg fun k _ => by positivity
    · rw [Fin.sum_univ_eq_sum_range (fun k => ((1 : ℝ) / p.1) ^ k) (z + 1)]
      exact swarm_radical_geom_le (Nat.prime_of_mem_primeFactors p.2) z
  have hcoe_rhs :
      (∏ p : d.primeFactors, ((p.1 : ℝ) / ((p.1 : ℝ) - 1))) =
        ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) :=
    Finset.prod_coe_sort d.primeFactors (fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1))
  calc
    ∑ n ∈ A, g (e n) = ∑ f ∈ A.image e, g f := himg
    _ ≤ ∑ f : (∀ _ : d.primeFactors, Fin (z + 1)), g f := hleB
    _ = ∏ p : d.primeFactors, ∑ k : Fin (z + 1), ((1 : ℝ) / p.1) ^ (k : ℕ) := hprod_sum
    _ ≤ ∏ p : d.primeFactors, ((p.1 : ℝ) / ((p.1 : ℝ) - 1)) := hprod_le
    _ = ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hcoe_rhs

lemma swarm_harmonic_le_sum_radical (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / n) ≤
      ∑ d ∈ (Finset.Icc 1 z).filter Squarefree,
        (1 / (d : ℝ)) * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) := by
  have hmaps : ∀ n ∈ Finset.Icc 1 z,
      (∏ p ∈ n.primeFactors, p) ∈ (Finset.Icc 1 z).filter Squarefree := by
    intro n hn
    obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, swarm_radical_squarefree n⟩
    · exact Finset.one_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le
    · have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n :=
        ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1),
          swarm_radical_mul_cofactor (by omega)⟩
      exact (Nat.le_of_dvd (by omega) hdvd).trans hnz
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_le_sum fun d _ => swarm_radical_fiber_le d z

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1.H2 := by
  intro z _hz
  calc
    Real.log ((z : ℝ) + 1)
        ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / n := swarm_harmonic_log_le z
    _ ≤ ∑ d ∈ (Finset.Icc 1 z).filter Squarefree,
          (1 / (d : ℝ)) * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) :=
        swarm_harmonic_le_sum_radical z
    _ = ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / d.totient := by
        refine Finset.sum_congr rfl fun d hd => ?_
        exact swarm_totient_eq d (Finset.mem_filter.mp hd).2
