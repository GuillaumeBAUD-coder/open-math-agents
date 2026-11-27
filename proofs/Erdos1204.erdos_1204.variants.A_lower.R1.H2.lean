import OMAReductions.R_Erdos1204_erdos_1204_variants_A_lower_R1

-- Step Erdos1204.erdos_1204.variants.A_lower.R1.H2: hypothesis H2 of reduction Erdos1204.erdos_1204.variants.A_lower.R1
-- Credit: @smurali12
-- H2 := ∀ z : ℕ, 1 ≤ z →     Real.log ((z : ℝ) + 1) ≤       ∑ d ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / d.totient

private lemma log_add_one_le_harmonic' (z : ℕ) :
    Real.log ((z : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 z, (1 : ℝ) / m := by
  induction z with
  | zero => simp
  | succ n ih =>
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by ext x; simp; omega]
    rw [Finset.sum_insert (by simp)]
    have hlog_step :
        Real.log (((n + 1 : ℕ) : ℝ) + 1) =
          Real.log ((n : ℝ) + 1) + Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
      ring
    have hstep : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1))
      have h2 : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      linarith
    linarith

private def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

private lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_p : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    refine Nat.squarefree_mul_iff.mpr ⟨?_, ha_p.squarefree, ih hs_p⟩
    refine ha_p.coprime_iff_not_dvd.mpr fun hd => ?_
    obtain ⟨p, hp, hpa⟩ := (ha_p.prime.dvd_finsetProd_iff _).mp hd
    have heq : p = a := ((hs_p p hp).dvd_iff_eq ha_p.ne_one).mp hpa
    exact ha (heq.symm ▸ hp)

private lemma rad_mem_squarefree_Icc {m z : ℕ} (hm : m ∈ Finset.Icc 1 z) :
    rad m ∈ (Finset.Icc 1 z).filter Squarefree := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  have hm_pos : 0 < m := by omega
  have hrad_pos : 0 < rad m :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hdvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hle : rad m ≤ z := (Nat.le_of_dvd hm_pos hdvd).trans hm.2
  have hsq : Squarefree (rad m) :=
    squarefree_prod_primes m.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp
  exact ⟨⟨hrad_pos, hle⟩, hsq⟩

private lemma totient_eq_prod_sub_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have hnat := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd, mul_comm d] at hnat
  have htot : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := mul_right_cancel₀ hd.ne_zero hnat
  rw [htot, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).pos
  simp [Nat.cast_sub hp1]

private lemma geom_inv_sum_le {p z : ℕ} (hp : p.Prime) :
    ∑ k ∈ Finset.Icc 1 z, (1 : ℝ) / (p : ℝ) ^ k ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : 0 < (p : ℝ) - 1 := by linarith
  have hmul :
      ((p : ℝ) - 1) * ∑ k ∈ Finset.Icc 1 z, (1 : ℝ) / (p : ℝ) ^ k =
        1 - (1 : ℝ) / (p : ℝ) ^ z := by
    induction z with
    | zero => simp
    | succ n ih =>
      rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by ext x; simp; omega]
      rw [Finset.sum_insert (by simp), mul_add, ih]
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      rw [pow_succ]
      field_simp
      ring
  have hle : 1 - (1 : ℝ) / (p : ℝ) ^ z ≤ 1 := by
    have : 0 ≤ (1 : ℝ) / (p : ℝ) ^ z := by positivity
    linarith
  exact (le_div_iff₀ hpm1).mpr (by rw [mul_comm]; linarith)

private lemma fiber_sum_le {d z : ℕ} (hd : d ∈ (Finset.Icc 1 z).filter Squarefree) :
    ∑ m ∈ (Finset.Icc 1 z).filter (fun m => rad m = d), (1 : ℝ) / m ≤ (1 : ℝ) / d.totient := by
  classical
  let S := (Finset.Icc 1 z).filter (fun m => rad m = d)
  let P := d.primeFactors
  let T := P.pi (fun _ => Finset.Icc 1 z)
  have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2
  let φ : ℕ → ∀ p ∈ P, ℕ := fun m p _ => m.factorization p
  have hP : ∀ m ∈ S, m.primeFactors = P := by
    intro m hm
    have hrad : rad m = d := (Finset.mem_filter.mp hm).2
    dsimp [P]
    rw [← hrad]
    exact (Nat.primeFactors_prod_primeFactors m).symm
  have hmem : ∀ m ∈ S, φ m ∈ T := by
    intro m hm
    rw [Finset.mem_pi]
    intro p hp
    rw [← hP m hm] at hp
    have hm_icc := (Finset.mem_filter.mp hm).1
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm_icc).1
    have hm_le : m ≤ z := (Finset.mem_Icc.mp hm_icc).2
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac_pos : 1 ≤ m.factorization p :=
      hprime.factorization_pos_of_dvd hm_pos.ne' (Nat.dvd_of_mem_primeFactors hp)
    have hpow_dvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    have hpow_le : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm_pos hpow_dvd
    have hfac_lt : m.factorization p < 2 ^ m.factorization p := Nat.lt_two_pow_self
    have h2p : 2 ^ m.factorization p ≤ p ^ m.factorization p := Nat.pow_le_pow_left hprime.two_le _
    dsimp [φ]
    exact Finset.mem_Icc.mpr ⟨hfac_pos, by omega⟩
  have hinj : Set.InjOn φ S := by
    intro m₁ hm₁ m₂ hm₂ heq
    have h1_pos : m₁ ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₁).1).1; omega
    have h2_pos : m₂ ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1; omega
    apply Nat.eq_of_factorization_eq h1_pos h2_pos
    intro p
    by_cases hp : p ∈ P
    · exact congrFun (congrFun heq p) hp
    · have h1 : p ∉ m₁.primeFactors := by rwa [hP m₁ hm₁]
      have h2 : p ∉ m₂.primeFactors := by rwa [hP m₂ hm₂]
      have z1 : m₁.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      have z2 : m₂.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
      rw [z1, z2]
  have hval : ∀ m ∈ S, (1 : ℝ) / m = ∏ x ∈ P.attach, (1 : ℝ) / (x.1 : ℝ) ^ (φ m x.1 x.2) := by
    intro m hm
    have hm_pos : m ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega
    have hm_eq : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm_pos]
      simp [Finsupp.prod, Nat.support_factorization]
    have hmR : (m : ℝ) = ∏ x ∈ P.attach, (x.1 : ℝ) ^ (φ m x.1 x.2) := by
      conv_lhs => rw [hm_eq, hP m hm, Nat.cast_prod]
      simp_rw [Nat.cast_pow]
      exact (Finset.prod_attach P (fun p => (p : ℝ) ^ (m.factorization p))).symm
    rw [hmR]
    simp only [one_div, Finset.prod_inv_distrib]
  let f : (∀ p ∈ P, ℕ) → ℝ := fun g => ∏ x ∈ P.attach, (1 : ℝ) / (x.1 : ℝ) ^ (g x.1 x.2)
  have himg : ∑ m ∈ S, f (φ m) = ∑ g ∈ S.image φ, f g :=
    (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
  calc
    ∑ m ∈ S, (1 : ℝ) / m
      = ∑ m ∈ S, f (φ m) := Finset.sum_congr rfl hval
    _ = ∑ g ∈ S.image φ, f g := himg
    _ ≤ ∑ g ∈ T, f g := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro g hg
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hg
          exact hmem m hm
        · intro g _ _
          exact Finset.prod_nonneg fun x _ => by positivity
    _ = ∏ p ∈ P, ∑ k ∈ Finset.Icc 1 z, (1 : ℝ) / (p : ℝ) ^ k :=
        (Finset.prod_sum P (fun _ => Finset.Icc 1 z) (fun p k => (1 : ℝ) / (p : ℝ) ^ k)).symm
    _ ≤ ∏ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_le_prod
        · intro p _; exact Finset.sum_nonneg fun k _ => by positivity
        · intro p hp; exact geom_inv_sum_le (Nat.prime_of_mem_primeFactors hp)
    _ = (1 : ℝ) / d.totient := by
        dsimp [P]
        rw [totient_eq_prod_sub_one_of_squarefree hd_sq]
        simp only [one_div, Finset.prod_inv_distrib]

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_A_lower_R1.H2 := by
  intro z _hz
  refine (log_add_one_le_harmonic' z).trans ?_
  have hmaps : ((Finset.Icc 1 z : Set ℕ)).MapsTo rad ((Finset.Icc 1 z).filter Squarefree) :=
    fun _ hm => rad_mem_squarefree_Icc hm
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun m => (1 : ℝ) / m)]
  exact Finset.sum_le_sum fun d hd => fiber_sum_le hd

