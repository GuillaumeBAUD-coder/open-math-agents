import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1

-- Reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H2.R1 of Step H2 of Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1
-- Credit: @santiemanuel
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.R1.H2.R1.H2.R1.H2.

/-!
# CRT Fractional-Primorial Subcube Expansion & Selberg Sieve Reduction

We isolate the unconditional **CRT fractional-primorial subcube expansion** around any deep
minor-arc trough from the remaining sublevel-set density amplification step:

1. `H1`: **Unconditional CRT fractional-primorial trough expansion**:
   there exists `c₁ > 0` such that for all `θ ∈ (0, 1)`, `ε ∈ (0, 1)`, and sufficiently large `x`,
   if *any* shift `M₀ < Q` (`Q = ∏_{p ≤ x} p`) satisfies `S_min(M₀) < -θ * L`, then unfreezing a
   suitably chosen subset of CRT coordinates produces at least `Q ^ (c₁ * θ * ε)` distinct shifts
   `M < Q` satisfying `S_min(M) < -(3 * θ / 4) * L`.
2. `H2`: **Two-level sublevel-set density amplification (`Q ^ η → Q / √L`)**:
   there exists `θ ∈ (0, 1)` such that for `ε ∈ (0, 1)` and `η > 0`, eventually in `x`, if the
   `-(3 * θ / 4) * L` minor-arc sublevel set has size at least `Q ^ η`, then the `-(θ / 2) * L`
   sublevel set has size at least `Q / √L`.

Inside this reduction we prove unconditionally and export for `H1`:
- `crt_subcube_card`: explicit Chinese-remainder subcube embedding
  `k ↦ (M₀ + k * Q_frozen) % Q` producing `∏_{p ∈ T} p` distinct shifts in `range Q` that preserve
  all residues modulo primes in `P \ T`.
- `selberg_rough_Icc_upper`: Selberg's quadratic-form upper bound sieve showing that any interval
  `[M + 1, M + Y]` contains at most `Y / log z + 4 * z ^ 6` `z`-rough integers for every `z ≥ 2`.
- `main`: chaining `H1` with `H2` at `η = c₁ * θ * ε` yields
  `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H2`.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1

open Filter Finset Real

/-- Unconditional CRT fractional-primorial trough expansion:
there exists `c₁ > 0` such that for every `θ ∈ (0, 1)`, `ε ∈ (0, 1)`, and sufficiently large `x`
(`L = ⌈x ^ (1 + ε)⌉₊ / 2`, `D = L / (Nat.log 2 L + 1)`, `Q = ∏_{p ≤ x} p`), if some shift `M₀ < Q`
satisfies `S_min(M₀) < -θ * L`, then at least `Q ^ (c₁ * θ * ε)` shifts `M < Q` satisfy
`S_min(M) < -(3 * θ / 4) * L`. -/
def H1 : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ x : ℕ in Filter.atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊ / 2
      let D := L / (Nat.log 2 L + 1)
      let Q := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p;
      (∃ M₀ ∈ Finset.range Q,
        ∑ d ∈ Q.divisors.filter (fun d => D < d),
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
              Real.cos (2 * Real.pi * (r : ℝ) * ((M₀ + L : ℕ) : ℝ) / (d : ℝ)) *
                (‖∑ u ∈ Finset.range L,
                  Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                  (L : ℝ)) < -(θ * (L : ℝ))) →
      (Q : ℝ) ^ (c₁ * θ * ε) ≤
        (((Finset.range Q).filter fun M =>
          ∑ d ∈ Q.divisors.filter (fun d => D < d),
            ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
              ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
                Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ Finset.range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ)) < -((3 * θ / 4) * (L : ℝ))).card : ℝ)

/-- Two-level CRT sublevel-set density amplification (`Q ^ η → Q / √L`):
there exists `θ ∈ (0, 1)` such that for every `ε ∈ (0, 1)` and `η > 0`, eventually in `x`, if at
least `Q ^ η` shifts `M < Q` satisfy `S_min(M) < -(3 * θ / 4) * L`, then at least `Q / √L` shifts
`M < Q` satisfy `S_min(M) < -(θ / 2) * L`. -/
def H2 : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ η : ℝ, 0 < η →
    ∀ᶠ x : ℕ in Filter.atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊ / 2
      let D := L / (Nat.log 2 L + 1)
      let Q := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p;
      (Q : ℝ) ^ η ≤
        (((Finset.range Q).filter fun M =>
          ∑ d ∈ Q.divisors.filter (fun d => D < d),
            ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
              ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
                Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ Finset.range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ)) < -((3 * θ / 4) * (L : ℝ))).card : ℝ) →
      (Q : ℝ) / Real.sqrt (L : ℝ) ≤
        (((Finset.range Q).filter fun M =>
          ∑ d ∈ Q.divisors.filter (fun d => D < d),
            ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
              ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
                Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
                  (‖∑ u ∈ Finset.range L,
                    Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                    (L : ℝ)) < -((θ / 2) * (L : ℝ))).card : ℝ)

/-- Explicit CRT subcube construction: for any subset `T ⊆ P` of primes, shifting `M₀` by multiples
of `∏_{p ∈ P \ T} p` modulo `Q = ∏_{p ∈ P} p` yields `∏_{p ∈ T} p` distinct residues in `range Q`,
all congruent to `M₀` modulo every prime in `P \ T`. -/
lemma crt_subcube_card {P T : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hTP : T ⊆ P)
    (M₀ : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hgood : ∀ M ∈ range (∏ p ∈ P, p), (∀ p ∈ P \ T, M % p = M₀ % p) → good M) :
    (∏ p ∈ T, p) ≤ ((range (∏ p ∈ P, p)).filter good).card := by
  let Q := ∏ p ∈ P, p
  let Qf := ∏ p ∈ P \ T, p
  let Qt := ∏ p ∈ T, p
  have hpart : P = (P \ T) ∪ T := (Finset.sdiff_union_of_subset hTP).symm
  have hdisj : Disjoint (P \ T) T := Finset.sdiff_disjoint
  have hQ_eq : Q = Qf * Qt := by
    dsimp [Q, Qf, Qt]
    conv_lhs => rw [hpart]
    exact Finset.prod_union hdisj
  have hQf_pos : 0 < Qf := Finset.prod_pos fun p hp => (hP p (Finset.sdiff_subset hp)).pos
  have hQt_pos : 0 < Qt := Finset.prod_pos fun p hp => (hP p (hTP hp)).pos
  have hQ_pos : 0 < Q := by rw [hQ_eq]; exact Nat.mul_pos hQf_pos hQt_pos
  let f : ℕ → ℕ := fun k => (M₀ + k * Qf) % Q
  have himg_sub : (range Qt).image f ⊆ (range Q).filter good := by
    intro M hM
    obtain ⟨k, _, rfl⟩ := mem_image.mp hM
    have hmemQ : f k ∈ range Q := mem_range.mpr (Nat.mod_lt _ hQ_pos)
    refine mem_filter.mpr ⟨hmemQ, hgood (f k) hmemQ fun p hp => ?_⟩
    have hpQf : p ∣ Qf := Finset.dvd_prod_of_mem _ hp
    have hpQ : p ∣ Q := by rw [hQ_eq]; exact dvd_mul_of_dvd_left hpQf Qt
    dsimp [f]
    rw [Nat.mod_mod_of_dvd _ hpQ]
    obtain ⟨c, hc⟩ := hpQf
    have hmul : M₀ + k * Qf = M₀ + p * (k * c) := by rw [hc]; ring
    rw [hmul, Nat.add_mul_mod_self_left]
  have hinj : Set.InjOn f (range Qt : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁_lt : k₁ < Qt := mem_range.mp (mem_coe.mp hk₁)
    have hk₂_lt : k₂ < Qt := mem_range.mp (mem_coe.mp hk₂)
    have hmodQ : M₀ + k₁ * Qf ≡ M₀ + k₂ * Qf [MOD Q] := heq
    have hmod_mul : k₁ * Qf ≡ k₂ * Qf [MOD Qf * Qt] := by
      rw [← hQ_eq]
      exact Nat.ModEq.add_left_cancel' M₀ hmodQ
    have hdvd : Qf * Qt ∣ (if k₁ ≤ k₂ then (k₂ - k₁) * Qf else (k₁ - k₂) * Qf) := by
      by_cases hle : k₁ ≤ k₂
      · rw [if_pos hle, Nat.sub_mul]
        have hle_mul : k₁ * Qf ≤ k₂ * Qf := Nat.mul_le_mul_right Qf hle
        exact (Nat.modEq_iff_dvd' hle_mul).mp hmod_mul
      · rw [if_neg hle, Nat.sub_mul]
        have hle' : k₂ ≤ k₁ := by omega
        have hle_mul : k₂ * Qf ≤ k₁ * Qf := Nat.mul_le_mul_right Qf hle'
        exact (Nat.modEq_iff_dvd' hle_mul).mp hmod_mul.symm
    by_cases hle : k₁ ≤ k₂
    · rw [if_pos hle] at hdvd
      rw [Nat.mul_comm (k₂ - k₁) Qf] at hdvd
      have hdvd_Qt : Qt ∣ (k₂ - k₁) := (Nat.mul_dvd_mul_iff_left hQf_pos).mp hdvd
      have hsub_lt : k₂ - k₁ < Qt := by omega
      have hsub_zero : k₂ - k₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_Qt hsub_lt
      omega
    · rw [if_neg hle] at hdvd
      rw [Nat.mul_comm (k₁ - k₂) Qf] at hdvd
      have hdvd_Qt : Qt ∣ (k₁ - k₂) := (Nat.mul_dvd_mul_iff_left hQf_pos).mp hdvd
      have hsub_lt : k₁ - k₂ < Qt := by omega
      have hsub_zero : k₁ - k₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_Qt hsub_lt
      omega
  calc
    Qt = (range Qt).card := Finset.card_range Qt |>.symm
    _ = ((range Qt).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((range Q).filter good).card := Finset.card_le_card himg_sub

private lemma smooth_recip_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (z : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 z)
    (hsmooth : ∀ n ∈ A, ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S) :
    ∑ n ∈ A, (n : ℝ)⁻¹ ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹ := by
  induction S using Finset.cons_induction generalizing A with
  | empty =>
    rw [Finset.prod_empty]
    have hA_sub : A ⊆ {1} := by
      intro n hn
      have hnI := mem_Icc.mp (hA hn)
      have hn1 : n = 1 := by
        by_contra hne
        exact Finset.notMem_empty _ (hsmooth n hn n.minFac (Nat.minFac_prime hne) (Nat.minFac_dvd n))
      exact mem_singleton.mpr hn1
    calc
      ∑ n ∈ A, (n : ℝ)⁻¹ ≤ ∑ n ∈ ({1} : Finset ℕ), (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hA_sub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | cons q T hqT ih =>
    have hq : q.Prime := hS q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hS p (mem_cons_of_mem hp)
    let Ae : ℕ → Finset ℕ := fun e => A.filter (fun n => n.factorization q = e)
    have hpart : A = (range (z + 1)).biUnion Ae := by
      ext n
      simp only [Ae, mem_biUnion, mem_range, mem_filter]
      constructor
      · intro hn
        refine ⟨n.factorization q, ?_, hn, rfl⟩
        have hnI := mem_Icc.mp (hA hn)
        have hpow_le : q ^ (n.factorization q) ≤ n :=
          Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n q)
        have hlt_pow : n.factorization q < q ^ (n.factorization q) :=
          lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq.two_le _)
        omega
      · rintro ⟨_, _, hn, _⟩; exact hn
    have hpw : (range (z + 1) : Set ℕ).PairwiseDisjoint Ae := by
      intro e₁ _ e₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro n hn₁ hn₂
      exact hne ((mem_filter.mp hn₁).2.symm.trans (mem_filter.mp hn₂).2)
    have hsum_e : ∀ e ∈ range (z + 1),
        ∑ n ∈ Ae e, (n : ℝ)⁻¹ ≤ ((q : ℝ)⁻¹) ^ e * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro e _
      let Be := (Ae e).image (fun n => n / q ^ e)
      have hBe_sub : Be ⊆ Icc 1 z := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnI := mem_Icc.mp (hA (mem_filter.mp hn).1)
        have hdvd : q ^ e ∣ n := (mem_filter.mp hn).2 ▸ Nat.ordProj_dvd n q
        have hmul : q ^ e * (n / q ^ e) = n := Nat.mul_div_cancel' hdvd
        exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega,
          (Nat.div_le_self n (q ^ e)).trans hnI.2⟩
      have hBe_smooth : ∀ m ∈ Be, ∀ p : ℕ, p.Prime → p ∣ m → p ∈ T := by
        intro m hm p hp hpm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnA := (mem_filter.mp hn).1
        have hnI := mem_Icc.mp (hA hnA)
        have hdvd : q ^ e ∣ n := (mem_filter.mp hn).2 ▸ Nat.ordProj_dvd n q
        have hmul : q ^ e * (n / q ^ e) = n := Nat.mul_div_cancel' hdvd
        have hpn : p ∣ n := dvd_trans hpm ⟨q ^ e, by rw [Nat.mul_comm]; exact hmul.symm⟩
        rcases mem_cons.mp (hsmooth n hnA p hp hpn) with hpq | hpT
        · exfalso
          rw [hpq] at hpm
          obtain ⟨k, hk⟩ := hpm
          have heq : n.factorization q = e := (mem_filter.mp hn).2
          have hpow1 : q ^ (e + 1) ∣ n := ⟨k, by rw [pow_succ, mul_assoc, ← hk, hmul]⟩
          have hle := (hq.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp hpow1
          omega
        · exact hpT
      have hinj : Set.InjOn (fun n => n / q ^ e) (Ae e : Set ℕ) := by
        intro n₁ hn₁ n₂ hn₂ hdiv
        dsimp only at hdiv
        have h1 : q ^ e ∣ n₁ := (mem_filter.mp (mem_coe.mp hn₁)).2 ▸ Nat.ordProj_dvd n₁ q
        have h2 : q ^ e ∣ n₂ := (mem_filter.mp (mem_coe.mp hn₂)).2 ▸ Nat.ordProj_dvd n₂ q
        calc
          n₁ = q ^ e * (n₁ / q ^ e) := (Nat.mul_div_cancel' h1).symm
          _ = q ^ e * (n₂ / q ^ e) := by rw [hdiv]
          _ = n₂ := Nat.mul_div_cancel' h2
      have hfactor : ∑ n ∈ Ae e, (n : ℝ)⁻¹ = ((q : ℝ)⁻¹) ^ e * ∑ m ∈ Be, (m : ℝ)⁻¹ := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hdvd : q ^ e ∣ n := (mem_filter.mp hn).2 ▸ Nat.ordProj_dvd n q
        have hmul : (n : ℝ) = ((q : ℝ) ^ e) * ((n / q ^ e : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
        rw [hmul, mul_inv, inv_pow]
      rw [hfactor]
      exact mul_le_mul_of_nonneg_left (ih hT Be hBe_sub hBe_smooth) (by positivity)
    have hgeom : ∑ e ∈ range (z + 1), ((q : ℝ)⁻¹) ^ e ≤ (1 - (q : ℝ)⁻¹)⁻¹ := by
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
      have hq_inv_le : (q : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq2
      have h1_sub_pos : 0 < 1 - (q : ℝ)⁻¹ := by linarith
      rw [geom_sum_eq (by linarith)]
      have hpow_nn : (0 : ℝ) ≤ ((q : ℝ)⁻¹) ^ (z + 1) := by positivity
      have heq : (((q : ℝ)⁻¹) ^ (z + 1) - 1) / ((q : ℝ)⁻¹ - 1) =
          (1 - ((q : ℝ)⁻¹) ^ (z + 1)) / (1 - (q : ℝ)⁻¹) := by
        rw [← neg_div_neg_eq]; congr 1 <;> ring
      rw [heq, inv_eq_one_div (1 - (q : ℝ)⁻¹)]
      exact div_le_div_of_nonneg_right (by linarith) h1_sub_pos.le
    have hT_nn : 0 ≤ ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hT p hp).two_le
      have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    calc
      ∑ n ∈ A, (n : ℝ)⁻¹ = ∑ e ∈ range (z + 1), ∑ n ∈ Ae e, (n : ℝ)⁻¹ := by
        conv_lhs => rw [hpart]; exact Finset.sum_biUnion hpw
      _ ≤ ∑ e ∈ range (z + 1), ((q : ℝ)⁻¹) ^ e * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := Finset.sum_le_sum hsum_e
      _ = (∑ e ∈ range (z + 1), ((q : ℝ)⁻¹) ^ e) * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (1 - (q : ℝ)⁻¹)⁻¹ * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := mul_le_mul_of_nonneg_right hgeom hT_nn
      _ = ∏ p ∈ cons q T hqT, (1 - (p : ℝ)⁻¹)⁻¹ := by rw [Finset.prod_cons]

private lemma squarefree_divisors_moebius_sum {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∀ m ∈ (∏ p ∈ P, p).divisors,
      (ArithmeticFunction.moebius m : ℝ) ^ 2 = 1 ∧
      (∑ j ∈ m.divisors, (ArithmeticFunction.moebius j : ℝ) = if m = 1 then 1 else 0) ∧
      ((m : ℝ)⁻¹ * (∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) = (Nat.totient m : ℝ)⁻¹) := by
  induction P using Finset.cons_induction with
  | empty =>
    intro m hm
    simp only [Finset.prod_empty, Nat.divisors_one, mem_singleton] at hm
    subst hm
    simp
  | cons q T hqT ih =>
    have hq : q.Prime := hP q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_cons_of_mem hp)
    let QT := ∏ p ∈ T, p
    have hQT_pos : 0 < QT := Finset.prod_pos fun p hp => (hT p hp).pos
    have hcop_qQT : Nat.Coprime q QT :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp)).2 (fun heq => hqT (heq ▸ hp))
    intro m hm
    rw [Finset.prod_cons] at hm
    have hdiv_m := (Nat.mem_divisors.mp hm).1
    by_cases hqm : q ∣ m
    · obtain ⟨d, rfl⟩ := hqm
      have hd_dvd : d ∣ QT := (Nat.mul_dvd_mul_iff_left hq.pos).mp hdiv_m
      have hd_mem : d ∈ QT.divisors := Nat.mem_divisors.mpr ⟨hd_dvd, hQT_pos.ne'⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hQT_pos
      have hcop_qd : Nat.Coprime q d := hcop_qQT.coprime_dvd_right hd_dvd
      obtain ⟨ih_sq, ih_sum, ih_tot⟩ := ih hT d hd_mem
      refine ⟨?_, ?_, ?_⟩
      · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qd,
          ArithmeticFunction.moebius_apply_prime hq]
        push_cast
        nlinarith [ih_sq]
      · have hqm_ne1 : q * d ≠ 1 := by
          have := hq.two_le
          nlinarith
        rw [if_neg hqm_ne1]
        have hdiv_qd : (q * d).divisors = d.divisors ∪ d.divisors.image (fun j => q * j) := by
          ext j
          simp only [Nat.mem_divisors, mem_union, mem_image]
          have hqd0 : q * d ≠ 0 := Nat.mul_ne_zero hq.ne_zero hd_pos.ne'
          constructor
          · rintro ⟨hjd, _⟩
            by_cases hqj : q ∣ j
            · obtain ⟨j', rfl⟩ := hqj
              exact Or.inr ⟨j', ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp hjd, hd_pos.ne'⟩, rfl⟩
            · exact Or.inl ⟨((hq.coprime_iff_not_dvd).mpr hqj).symm.dvd_of_dvd_mul_left hjd, hd_pos.ne'⟩
          · rintro (⟨hjd, _⟩ | ⟨j', ⟨hj'd, _⟩, rfl⟩)
            · exact ⟨dvd_mul_of_dvd_right hjd q, hqd0⟩
            · exact ⟨Nat.mul_dvd_mul_left q hj'd, hqd0⟩
        have hdisj_qd : Disjoint d.divisors (d.divisors.image (fun j => q * j)) := by
          rw [Finset.disjoint_left]
          intro j hjd hjim
          obtain ⟨j', _, rfl⟩ := mem_image.mp hjim
          have hqd_dvd : q ∣ d := dvd_trans (dvd_mul_right q j') (Nat.mem_divisors.mp hjd).1
          exact hq.not_dvd_one (hcop_qd.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hqd_dvd)
        rw [hdiv_qd, Finset.sum_union hdisj_qd,
          Finset.sum_image (fun j₁ _ j₂ _ h => Nat.eq_of_mul_eq_mul_left hq.pos h)]
        have hneg_sum : ∑ j ∈ d.divisors, (ArithmeticFunction.moebius (q * j) : ℝ) =
            -(∑ j ∈ d.divisors, (ArithmeticFunction.moebius j : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hcop_qj : Nat.Coprime q j := hcop_qd.coprime_dvd_right (Nat.mem_divisors.mp hj).1
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qj,
            ArithmeticFunction.moebius_apply_prime hq]
          push_cast
          ring
        rw [hneg_sum]
        ring
      · have hpf_eq : (q * d).primeFactors = insert q d.primeFactors := by
          rw [Nat.primeFactors_mul hq.ne_zero hd_pos.ne', hq.primeFactors, Finset.singleton_union]
        have hq_not_pf : q ∉ d.primeFactors := by
          intro hmem
          have hqd_dvd : q ∣ d := Nat.dvd_of_mem_primeFactors hmem
          exact hq.not_dvd_one (hcop_qd.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hqd_dvd)
        rw [hpf_eq, Finset.prod_insert hq_not_pf, Nat.totient_mul hcop_qd, Nat.totient_prime hq]
        have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        have hq_sub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub hq.one_le, Nat.cast_one]
        have hq1_ne : (q : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
          linarith
        have hq_fac : (q : ℝ)⁻¹ * (1 - (q : ℝ)⁻¹)⁻¹ = (((q - 1 : ℕ) : ℝ))⁻¹ := by
          rw [hq_sub]
          field_simp
        calc
          ((q * d : ℕ) : ℝ)⁻¹ * ((1 - (q : ℝ)⁻¹)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹)
              = ((q : ℝ)⁻¹ * (1 - (q : ℝ)⁻¹)⁻¹) *
                  ((d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
                push_cast; ring
          _ = (((q - 1 : ℕ) : ℝ))⁻¹ * (Nat.totient d : ℝ)⁻¹ := by rw [hq_fac, ih_tot]
          _ = (((q - 1) * Nat.totient d : ℕ) : ℝ)⁻¹ := by push_cast; ring
    · have hd_dvd : m ∣ QT :=
        ((hq.coprime_iff_not_dvd).mpr hqm).symm.dvd_of_dvd_mul_left hdiv_m
      exact ih hT m (Nat.mem_divisors.mpr ⟨hd_dvd, hQT_pos.ne'⟩)

/-- Selberg's quadratic-form upper bound sieve: for every `z ≥ 2`, `M : ℕ`, and `Y ≥ 1`, at most
`Y / log z + 4 * z ^ 6` integers in `[M + 1, M + Y]` avoid all primes `p ≤ z`. -/
lemma selberg_rough_Icc_upper {z : ℕ} (hz : 2 ≤ z) (M Y : ℕ) :
    (((Icc (M + 1) (M + Y)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) ≤
      (Y : ℝ) / Real.log (z : ℝ) + 4 * (z : ℝ) ^ 6 := by
  let Pz := (range (z + 1)).filter Nat.Prime
  have hPz : ∀ p ∈ Pz, p.Prime := fun _ hp => (mem_filter.mp hp).2
  let Qz := ∏ p ∈ Pz, p
  have hQz_pos : 0 < Qz := Finset.prod_pos fun p hp => (hPz p hp).pos
  have hsqf := squarefree_divisors_moebius_sum hPz
  let Tz := Qz.divisors.filter (fun d => d ≤ z)
  have h1_Tz : 1 ∈ Tz := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd Qz, hQz_pos.ne'⟩, by omega⟩
  -- Step 1: Lower-bound `J = ∑_{k ∈ Tz} 1 / φ(k) ≥ log z`.
  let J : ℝ := ∑ k ∈ Tz, (Nat.totient k : ℝ)⁻¹
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hJ_ge_log : Real.log (z : ℝ) ≤ J := by
    let rad : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors, p
    have hrad_mem : ∀ n ∈ Icc 1 z, rad n ∈ Tz := by
      intro n hn
      have hnI := mem_Icc.mp hn
      have hpf_sub : n.primeFactors ⊆ Pz := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpn := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
      have hdvd_Qz : rad n ∣ Qz := Finset.prod_dvd_prod_of_subset _ _ _ hpf_sub
      have hdvd_n : rad n ∣ n := Nat.prod_primeFactors_dvd n
      have hle_z : rad n ≤ z := (Nat.le_of_dvd (by omega) hdvd_n).trans hnI.2
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd_Qz, hQz_pos.ne'⟩, hle_z⟩
    have hpart_z : Icc 1 z = Tz.biUnion (fun k => (Icc 1 z).filter (fun n => rad n = k)) := by
      ext n
      simp only [mem_biUnion, mem_filter]
      constructor
      · intro hn; exact ⟨rad n, hrad_mem n hn, hn, rfl⟩
      · rintro ⟨_, _, hn, _⟩; exact hn
    have hpw_z : (Tz : Set ℕ).PairwiseDisjoint (fun k => (Icc 1 z).filter (fun n => rad n = k)) := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro n h1 h2
      exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    have hfiber : ∀ k ∈ Tz,
        ∑ n ∈ (Icc 1 z).filter (fun n => rad n = k), (n : ℝ)⁻¹ ≤ (Nat.totient k : ℝ)⁻¹ := by
      intro k hk
      have hkQz : k ∈ Qz.divisors := (mem_filter.mp hk).1
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hkQz).1 hQz_pos
      let Ak := ((Icc 1 z).filter (fun n => rad n = k)).image (fun n => n / k)
      have hAk_sub : Ak ⊆ Icc 1 z := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnI := mem_Icc.mp (mem_filter.mp hn).1
        have hdvd_kn : k ∣ n := (mem_filter.mp hn).2 ▸ Nat.prod_primeFactors_dvd n
        have hmul : k * (n / k) = n := Nat.mul_div_cancel' hdvd_kn
        exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega,
          (Nat.div_le_self n k).trans hnI.2⟩
      have hAk_smooth : ∀ m ∈ Ak, ∀ p : ℕ, p.Prime → p ∣ m → p ∈ k.primeFactors := by
        intro m hm p hp hpm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnI := mem_Icc.mp (mem_filter.mp hn).1
        have hrad_eq : rad n = k := (mem_filter.mp hn).2
        have hdvd_kn : k ∣ n := hrad_eq ▸ Nat.prod_primeFactors_dvd n
        have hpn : p ∣ n := dvd_trans hpm ⟨k, by rw [Nat.mul_comm]; exact (Nat.mul_div_cancel' hdvd_kn).symm⟩
        have hpk : p ∣ k := hrad_eq ▸ Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)
        exact Nat.mem_primeFactors.mpr ⟨hp, hpk, hk_pos.ne'⟩
      have hinj_k : Set.InjOn (fun n => n / k) (((Icc 1 z).filter (fun n => rad n = k)) : Set ℕ) := by
        intro n₁ hn₁ n₂ hn₂ hdiv
        dsimp only at hdiv
        have hd1 : k ∣ n₁ := (mem_filter.mp (mem_coe.mp hn₁)).2 ▸ Nat.prod_primeFactors_dvd n₁
        have hd2 : k ∣ n₂ := (mem_filter.mp (mem_coe.mp hn₂)).2 ▸ Nat.prod_primeFactors_dvd n₂
        calc
          n₁ = k * (n₁ / k) := (Nat.mul_div_cancel' hd1).symm
          _ = k * (n₂ / k) := by rw [hdiv]
          _ = n₂ := Nat.mul_div_cancel' hd2
      have hfac_k : ∑ n ∈ (Icc 1 z).filter (fun n => rad n = k), (n : ℝ)⁻¹ =
          (k : ℝ)⁻¹ * ∑ m ∈ Ak, (m : ℝ)⁻¹ := by
        rw [Finset.sum_image hinj_k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hdvd_kn : k ∣ n := (mem_filter.mp hn).2 ▸ Nat.prod_primeFactors_dvd n
        have hmul : (n : ℝ) = (k : ℝ) * ((n / k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hdvd_kn).symm
        rw [hmul, mul_inv]
      rw [hfac_k]
      have hsm := smooth_recip_sum_le k.primeFactors
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) z Ak hAk_sub hAk_smooth
      exact (mul_le_mul_of_nonneg_left hsm (by positivity)).trans_eq (hsqf k hkQz).2.2
    calc
      Real.log (z : ℝ) ≤ ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ :=
        OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.log_le_harmonic (by omega)
      _ = ∑ k ∈ Tz, ∑ n ∈ (Icc 1 z).filter (fun n => rad n = k), (n : ℝ)⁻¹ := by
        conv_lhs => rw [hpart_z]; exact Finset.sum_biUnion hpw_z
      _ ≤ ∑ k ∈ Tz, (Nat.totient k : ℝ)⁻¹ := Finset.sum_le_sum hfiber
  have hJ_pos : 0 < J := lt_of_lt_of_le hlogz_pos hJ_ge_log
  -- Step 2: Define Selberg weights `lam d` on `Tz` and verify `lam 1 = 1` and Möbius inversion.
  let lam : ℕ → ℝ := fun d =>
    ((d : ℝ) / J) * ∑ k ∈ Tz.filter (fun k => d ∣ k),
      ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
        (Nat.totient k : ℝ)
  have hlam1 : lam 1 = 1 := by
    dsimp [lam]
    have hf1 : Tz.filter (fun k => 1 ∣ k) = Tz := by
      ext k; simp
    rw [hf1]
    have hsq1 : ∀ k ∈ Tz,
        ((ArithmeticFunction.moebius (k / 1) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
          (Nat.totient k : ℝ) = (Nat.totient k : ℝ)⁻¹ := by
      intro k hk
      rw [Nat.div_one, ← sq, (hsqf k (mem_filter.mp hk).1).1, one_div]
    rw [Finset.sum_congr rfl hsq1, Nat.cast_one, one_div, inv_mul_cancel₀ hJ_pos.ne']
  have hmob_inv : ∀ k₀ ∈ Tz,
      ∑ d ∈ Tz.filter (fun d => k₀ ∣ d), lam d / (d : ℝ) =
        (ArithmeticFunction.moebius k₀ : ℝ) / (J * (Nat.totient k₀ : ℝ)) := by
    intro k₀ hk₀
    have hexp_d : ∀ d ∈ Tz.filter (fun d => k₀ ∣ d),
        lam d / (d : ℝ) = J⁻¹ * ∑ k ∈ Tz.filter (fun k => d ∣ k),
          ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
            (Nat.totient k : ℝ) := by
      intro d hd
      have hd_pos : 0 < d :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp (mem_filter.mp hd).1).1).1 hQz_pos
      have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
      dsimp [lam]
      field_simp
    rw [Finset.sum_congr rfl hexp_d, ← Finset.mul_sum]
    -- Rewrite double sum over `(d, k)` with `k₀ ∣ d ∣ k` as sum over `k` then `j = k / d ∈ (k / k₀).divisors`.
    have hswap :
        (∑ d ∈ Tz.filter (fun d => k₀ ∣ d),
          ∑ k ∈ Tz.filter (fun k => d ∣ k),
            ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
              (Nat.totient k : ℝ)) =
        ∑ k ∈ Tz.filter (fun k => k₀ ∣ k),
          ((ArithmeticFunction.moebius k : ℝ) / (Nat.totient k : ℝ)) *
            ∑ d ∈ Tz.filter (fun d => k₀ ∣ d ∧ d ∣ k),
              (ArithmeticFunction.moebius (k / d) : ℝ) := by
      trans (∑ d ∈ Tz.filter (fun d => k₀ ∣ d),
        ∑ k ∈ Tz.filter (fun k => k₀ ∣ k),
          if d ∣ k then
            ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
              (Nat.totient k : ℝ)
          else 0)
      · refine Finset.sum_congr rfl fun d hd => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp only [mem_filter]
        have hk₀d := (mem_filter.mp hd).2
        exact ⟨fun ⟨hkT, hdk⟩ => ⟨⟨hkT, dvd_trans hk₀d hdk⟩, hdk⟩,
          fun ⟨⟨hkT, _⟩, hdk⟩ => ⟨hkT, hdk⟩⟩
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_filter, Finset.mul_sum]
        have hf_eq : (Tz.filter (fun d => k₀ ∣ d)).filter (fun d => d ∣ k) =
            Tz.filter (fun d => k₀ ∣ d ∧ d ∣ k) := by
          ext d; simp only [mem_filter]; tauto
        rw [hf_eq]
        refine Finset.sum_congr rfl fun d _ => by ring
    rw [hswap]
    have hinner_k : ∀ k ∈ Tz.filter (fun k => k₀ ∣ k),
        ((ArithmeticFunction.moebius k : ℝ) / (Nat.totient k : ℝ)) *
          (∑ d ∈ Tz.filter (fun d => k₀ ∣ d ∧ d ∣ k),
            (ArithmeticFunction.moebius (k / d) : ℝ)) =
        if k = k₀ then (ArithmeticFunction.moebius k₀ : ℝ) / (Nat.totient k₀ : ℝ) else 0 := by
      intro k hk
      have hkTz : k ∈ Tz := (mem_filter.mp hk).1
      have hkQz : k ∈ Qz.divisors := (mem_filter.mp hkTz).1
      have hk_le_z : k ≤ z := (mem_filter.mp hkTz).2
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hkQz).1 hQz_pos
      have hk₀k : k₀ ∣ k := (mem_filter.mp hk).2
      have hk₀_pos : 0 < k₀ := Nat.pos_of_dvd_of_pos hk₀k hk_pos
      let m := k / k₀
      have hkm : k₀ * m = k := Nat.mul_div_cancel' hk₀k
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hkm; omega
      have hm_mem_Qz : m ∈ Qz.divisors :=
        Nat.mem_divisors.mpr ⟨dvd_trans ⟨k₀, by rw [Nat.mul_comm]; exact hkm.symm⟩ (Nat.mem_divisors.mp hkQz).1,
          hQz_pos.ne'⟩
      have hbij_j :
          (∑ d ∈ Tz.filter (fun d => k₀ ∣ d ∧ d ∣ k), (ArithmeticFunction.moebius (k / d) : ℝ)) =
          ∑ j ∈ m.divisors, (ArithmeticFunction.moebius j : ℝ) := by
        refine Finset.sum_nbij (fun d => k / d) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro d hd
          obtain ⟨_, hk₀d, hdk⟩ := mem_filter.mp hd
          obtain ⟨a, rfl⟩ := hk₀d
          have hak : k₀ * a ∣ k₀ * m := hkm ▸ hdk
          have ham : a ∣ m := (Nat.mul_dvd_mul_iff_left hk₀_pos).mp hak
          have hdiv_eq : k / (k₀ * a) = m / a := by
            rw [← hkm, Nat.mul_div_mul_left _ _ hk₀_pos]
          rw [hdiv_eq]
          exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd ham, hm_pos.ne'⟩
        · intro d₁ hd₁ d₂ hd₂ heq
          dsimp only at heq
          have h1 : d₁ ∣ k := (mem_filter.mp hd₁).2.2
          have h2 : d₂ ∣ k := (mem_filter.mp hd₂).2.2
          have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos h1 hk_pos
          have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos h2 hk_pos
          have hm1 : d₁ * (k / d₁) = k := Nat.mul_div_cancel' h1
          have hm2 : d₂ * (k / d₂) = k := Nat.mul_div_cancel' h2
          have hqd_pos : 0 < k / d₂ :=
            Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hm2; omega
          rw [heq] at hm1
          exact Nat.eq_of_mul_eq_mul_right hqd_pos (hm1.trans hm2.symm)
        · intro j hj
          have hjm : j ∣ m := (Nat.mem_divisors.mp hj).1
          have hj_pos : 0 < j := Nat.pos_of_dvd_of_pos hjm hm_pos
          let d := k₀ * (m / j)
          have hmj : j * (m / j) = m := Nat.mul_div_cancel' hjm
          have hdj : d * j = k := by
            dsimp [d]
            calc
              k₀ * (m / j) * j = k₀ * (j * (m / j)) := by ring
              _ = k₀ * m := by rw [hmj]
              _ = k := hkm
          have hdk : d ∣ k := ⟨j, hdj.symm⟩
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdk hk_pos
          have hdTz : d ∈ Tz := mem_filter.mpr
            ⟨Nat.mem_divisors.mpr ⟨dvd_trans hdk (Nat.mem_divisors.mp hkQz).1, hQz_pos.ne'⟩,
              (Nat.le_of_dvd hk_pos hdk).trans hk_le_z⟩
          refine ⟨d, mem_coe.mpr (mem_filter.mpr ⟨hdTz, ⟨m / j, rfl⟩, hdk⟩), ?_⟩
          dsimp only
          rw [← hdj, Nat.mul_div_cancel_left j hd_pos]
      rw [hbij_j, (hsqf m hm_mem_Qz).2.1]
      by_cases hkeq : k = k₀
      · subst hkeq
        have hm1 : m = 1 := Nat.div_self hk₀_pos
        rw [if_pos hm1, if_pos rfl, mul_one]
      · have hm_ne1 : m ≠ 1 := fun hm1 => by
          rw [hm1, mul_one] at hkm
          exact hkeq hkm.symm
        rw [if_neg hm_ne1, if_neg hkeq, mul_zero]
    rw [Finset.sum_congr rfl hinner_k, Finset.sum_ite_eq' (Tz.filter (fun k => k₀ ∣ k)) k₀,
      if_pos (mem_filter.mpr ⟨hk₀, dvd_rfl⟩)]
    ring
  -- Step 3: Upper-bound the rough count by the Selberg quadratic sum over `Icc (M + 1) (M + Y)`.
  have hpointwise : ∀ n ∈ Icc (M + 1) (M + Y),
      (if ∀ p ≤ z, p.Prime → ¬ (p ∣ n) then (1 : ℝ) else 0) ≤
        (∑ d ∈ Tz.filter (fun d => d ∣ n), lam d) ^ 2 := by
    intro n _
    by_cases hrough : ∀ p ≤ z, p.Prime → ¬ (p ∣ n)
    · rw [if_pos hrough]
      have hf_eq1 : Tz.filter (fun d => d ∣ n) = {1} := by
        ext d
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hdTz, hdn⟩
          by_contra hd_ne1
          have hmp : d.minFac.Prime := Nat.minFac_prime hd_ne1
          have hmd : d.minFac ∣ d := Nat.minFac_dvd d
          have hd_pos : 0 < d :=
            Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hdTz).1).1 hQz_pos
          have hm_le_z : d.minFac ≤ z := (Nat.le_of_dvd hd_pos hmd).trans (mem_filter.mp hdTz).2
          exact hrough d.minFac hm_le_z hmp (dvd_trans hmd hdn)
        · rintro rfl
          exact ⟨h1_Tz, one_dvd n⟩
      rw [hf_eq1, Finset.sum_singleton, hlam1]
      norm_num
    · rw [if_neg hrough]
      exact sq_nonneg _
  have hsum_ind :
      (((Icc (M + 1) (M + Y)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) ≤
        ∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
          lam d₁ * lam d₂ * (((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ) := by
    have hcard_eq :
        (((Icc (M + 1) (M + Y)).filter fun n => ∀ p ≤ z, p.Prime → ¬ (p ∣ n)).card : ℝ) =
        ∑ n ∈ Icc (M + 1) (M + Y), if ∀ p ≤ z, p.Prime → ¬ (p ∣ n) then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
    rw [hcard_eq]
    refine (Finset.sum_le_sum hpointwise).trans_eq ?_
    have hsum_flt : ∀ (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℝ),
        ∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0 := by
      intro s p _ f; rw [Finset.sum_filter]
    have hexp_sq : ∀ n ∈ Icc (M + 1) (M + Y),
        (∑ d ∈ Tz.filter (fun d => d ∣ n), lam d) ^ 2 =
        ∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
          if Nat.lcm d₁ d₂ ∣ n then lam d₁ * lam d₂ else 0 := by
      intro n _
      rw [sq, hsum_flt Tz (fun d => d ∣ n), Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
      by_cases h1 : d₁ ∣ n <;> by_cases h2 : d₂ ∣ n
      · rw [if_pos h1, if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
      · have hnl : ¬ (Nat.lcm d₁ d₂ ∣ n) := fun hl => h2 (dvd_trans (Nat.dvd_lcm_right d₁ d₂) hl)
        rw [if_pos h1, if_neg h2, if_neg hnl, mul_zero]
      · have hnl : ¬ (Nat.lcm d₁ d₂ ∣ n) := fun hl => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) hl)
        rw [if_neg h1, if_neg hnl, zero_mul]
      · have hnl : ¬ (Nat.lcm d₁ d₂ ∣ n) := fun hl => h1 (dvd_trans (Nat.dvd_lcm_left d₁ d₂) hl)
        rw [if_neg h1, if_neg hnl, zero_mul]
    rw [Finset.sum_congr rfl hexp_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [← hsum_flt (Icc (M + 1) (M + Y)) (fun n => Nat.lcm d₁ d₂ ∣ n) (fun _ => lam d₁ * lam d₂),
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 4: Approximate `card {n ∈ Icc (M+1) (M+Y) | m ∣ n}` by `Y / m` with error `≤ 1`.
  have hmult_approx : ∀ m : ℕ, 0 < m →
      |(((Icc (M + 1) (M + Y)).filter fun n => m ∣ n).card : ℝ) - (Y : ℝ) / (m : ℝ)| ≤ 1 := by
    intro m hm_pos
    have hcard_m : ((Icc (M + 1) (M + Y)).filter fun n => m ∣ n).card =
        (M + Y) / m - M / m := by
      have himg : (Icc (M + 1) (M + Y)).filter (fun n => m ∣ n) =
          (Icc (M / m + 1) ((M + Y) / m)).image (fun q => m * q) := by
        ext n
        simp only [mem_filter, mem_Icc, mem_image]
        constructor
        · rintro ⟨⟨hn1, hn2⟩, ⟨q, rfl⟩⟩
          refine ⟨q, ⟨?_, ?_⟩, rfl⟩
          · by_contra hlt
            have hq_le : q ≤ M / m := by omega
            have hmul : m * q ≤ m * (M / m) := Nat.mul_le_mul_left m hq_le
            have hle_M : m * (M / m) ≤ M := Nat.mul_div_le M m
            omega
          · exact (Nat.le_div_iff_mul_le hm_pos).mpr (by rw [Nat.mul_comm]; exact hn2)
        · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
          have hdm : m * (M / m) + M % m = M := Nat.div_add_mod M m
          have hrem : M % m < m := Nat.mod_lt M hm_pos
          have hlo : M + 1 ≤ m * q := by
            have : m * (M / m + 1) ≤ m * q := Nat.mul_le_mul_left m hq1
            rw [Nat.mul_add, Nat.mul_one] at this
            omega
          have hhi : m * q ≤ M + Y := by
            rw [Nat.mul_comm]
            exact (Nat.le_div_iff_mul_le hm_pos).mp hq2
          exact ⟨⟨hlo, hhi⟩, ⟨q, rfl⟩⟩
      rw [himg, Finset.card_image_of_injective _ (fun q₁ q₂ h => Nat.eq_of_mul_eq_mul_left hm_pos h),
        Nat.card_Icc]
      omega
    rw [hcard_m]
    have hle_div : M / m ≤ (M + Y) / m := Nat.div_le_div_right (Nat.le_add_right M Y)
    rw [Nat.cast_sub hle_div]
    have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have h1 : ((M + Y : ℕ) : ℝ) - (m : ℝ) < (m : ℝ) * (((M + Y) / m : ℕ) : ℝ) := by
      have hnat : M + Y < m * ((M + Y) / m + 1) := by
        have hdm := Nat.div_add_mod (M + Y) m
        have hrm := Nat.mod_lt (M + Y) hm_pos
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hr : ((M + Y : ℕ) : ℝ) < (m : ℝ) * ((((M + Y) / m : ℕ) : ℝ) + 1) := by
        exact_mod_cast hnat
      linarith
    have h2 : (m : ℝ) * (((M + Y) / m : ℕ) : ℝ) ≤ ((M + Y : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_div_le (M + Y) m
    have h3 : (M : ℝ) - (m : ℝ) < (m : ℝ) * ((M / m : ℕ) : ℝ) := by
      have hnat : M < m * (M / m + 1) := by
        have hdm := Nat.div_add_mod M m
        have hrm := Nat.mod_lt M hm_pos
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hr : (M : ℝ) < (m : ℝ) * (((M / m : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
      linarith
    have h4 : (m : ℝ) * ((M / m : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.mul_div_le M m
    have hMY : ((M + Y : ℕ) : ℝ) = (M : ℝ) + (Y : ℝ) := by push_cast; rfl
    have hY_eq : (m : ℝ) * ((Y : ℝ) / (m : ℝ)) = (Y : ℝ) := mul_div_cancel₀ (Y : ℝ) hm_pos_r.ne'
    rw [abs_le]
    constructor
    · have hlo : (m : ℝ) * (-1) ≤
          (m : ℝ) * ((((M + Y) / m : ℕ) : ℝ) - ((M / m : ℕ) : ℝ) - (Y : ℝ) / (m : ℝ)) := by
        linarith
      exact le_of_mul_le_mul_left hlo hm_pos_r
    · have hhi : (m : ℝ) * ((((M + Y) / m : ℕ) : ℝ) - ((M / m : ℕ) : ℝ) - (Y : ℝ) / (m : ℝ)) ≤
          (m : ℝ) * 1 := by
        linarith
      exact le_of_mul_le_mul_left hhi hm_pos_r
  -- Step 5: Diagonalize the main quadratic form `∑_{d₁, d₂} lam d₁ * lam d₂ / lcm d₁ d₂ = 1 / J`.
  have hquad_eq :
      (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz, lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))) =
      (Y : ℝ) / J := by
    have hlcm_gcd : ∀ d₁ ∈ Tz, ∀ d₂ ∈ Tz,
        lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) =
        (Y : ℝ) * ∑ k ∈ Tz,
          if k ∣ d₁ ∧ k ∣ d₂ then (Nat.totient k : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ))
          else 0 := by
      intro d₁ hd₁ d₂ hd₂
      have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hd₁).1).1 hQz_pos
      have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hd₂).1).1 hQz_pos
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd₁_pos
      have hl_pos : 0 < Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
      have hmul_gl : (Nat.gcd d₁ d₂ : ℝ) * (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
      have htot_sum : (Nat.gcd d₁ d₂ : ℝ) =
          ∑ k ∈ Tz, if k ∣ d₁ ∧ k ∣ d₂ then (Nat.totient k : ℝ) else 0 := by
        have h1 : (Nat.gcd d₁ d₂ : ℝ) = ∑ k ∈ (Nat.gcd d₁ d₂).divisors, (Nat.totient k : ℝ) := by
          exact_mod_cast (Nat.sum_totient (Nat.gcd d₁ d₂)).symm
        rw [h1, ← Finset.sum_filter]
        congr 1
        ext k
        simp only [Tz, mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨hkg, _⟩
          have hkd₁ : k ∣ d₁ := dvd_trans hkg (Nat.gcd_dvd_left d₁ d₂)
          have hkd₂ : k ∣ d₂ := dvd_trans hkg (Nat.gcd_dvd_right d₁ d₂)
          exact ⟨⟨⟨dvd_trans hkd₁ (Nat.mem_divisors.mp (mem_filter.mp hd₁).1).1, hQz_pos.ne'⟩,
            (Nat.le_of_dvd hd₁_pos hkd₁).trans (mem_filter.mp hd₁).2⟩, hkd₁, hkd₂⟩
        · rintro ⟨_, hkd₁, hkd₂⟩
          exact ⟨Nat.dvd_gcd hkd₁ hkd₂, hg_pos.ne'⟩
      have hdiv_lcm : (1 : ℝ) / (Nat.lcm d₁ d₂ : ℝ) =
          (Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
        have hd1_ne : (d₁ : ℝ) ≠ 0 := by exact_mod_cast hd₁_pos.ne'
        have hd2_ne : (d₂ : ℝ) ≠ 0 := by exact_mod_cast hd₂_pos.ne'
        have hl_ne : (Nat.lcm d₁ d₂ : ℝ) ≠ 0 := by exact_mod_cast hl_pos.ne'
        field_simp
        linarith [hmul_gl]
      calc
        lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))
            = (Y : ℝ) * (lam d₁ * lam d₂ * ((1 : ℝ) / (Nat.lcm d₁ d₂ : ℝ))) := by ring
        _ = (Y : ℝ) * (lam d₁ * lam d₂ * ((Nat.gcd d₁ d₂ : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)))) := by
            rw [hdiv_lcm]
        _ = (Y : ℝ) * ((Nat.gcd d₁ d₂ : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ))) := by ring
        _ = (Y : ℝ) * ∑ k ∈ Tz,
              if k ∣ d₁ ∧ k ∣ d₂ then (Nat.totient k : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ))
              else 0 := by
            congr 1
            rw [htot_sum, Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => ?_
            split_ifs <;> ring
    have h1 :
        (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz, lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))) =
        (Y : ℝ) * ∑ k ∈ Tz, (Nat.totient k : ℝ) *
          (∑ d ∈ Tz.filter (fun d => k ∣ d), lam d / (d : ℝ)) ^ 2 := by
      rw [Finset.sum_congr rfl fun d₁ hd₁ => Finset.sum_congr rfl (hlcm_gcd d₁ hd₁)]
      simp_rw [← Finset.mul_sum]
      congr 1
      trans (∑ d₁ ∈ Tz, ∑ k ∈ Tz, ∑ d₂ ∈ Tz,
        if k ∣ d₁ ∧ k ∣ d₂ then (Nat.totient k : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0)
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hsum_flt_k : (∑ d ∈ Tz.filter (fun d => k ∣ d), lam d / (d : ℝ)) =
            ∑ d ∈ Tz, if k ∣ d then lam d / (d : ℝ) else 0 := by
          have hgen : ∀ (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℝ),
              ∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0 := by
            intro s p _ f; rw [Finset.sum_filter]
          exact hgen Tz (fun d => k ∣ d) (fun d => lam d / (d : ℝ))
        rw [sq, hsum_flt_k, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₂ _ => ?_
        by_cases h1' : k ∣ d₁ <;> by_cases h2' : k ∣ d₂
        · rw [if_pos ⟨h1', h2'⟩, if_pos h1', if_pos h2']; ring
        · rw [if_neg (fun h => h2' h.2), if_pos h1', if_neg h2']; ring
        · rw [if_neg (fun h => h1' h.1), if_neg h1']; ring
        · rw [if_neg (fun h => h1' h.1), if_neg h1']; ring
    rw [h1]
    have hdiag_k : ∀ k ∈ Tz,
        (Nat.totient k : ℝ) * (∑ d ∈ Tz.filter (fun d => k ∣ d), lam d / (d : ℝ)) ^ 2 =
          J ^ (-2 : ℤ) * (Nat.totient k : ℝ)⁻¹ := by
      intro k hk
      rw [hmob_inv k hk]
      have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hk).1).1 hQz_pos
      have hphi_ne : (Nat.totient k : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hk_pos).ne'
      have hmsq : (ArithmeticFunction.moebius k : ℝ) ^ 2 = 1 := (hsqf k (mem_filter.mp hk).1).1
      rw [zpow_neg, zpow_two, div_pow, hmsq]
      field_simp
    have hdiag_k' : ∀ k ∈ Tz,
        (Nat.totient k : ℝ) * (∑ d ∈ Tz.filter (fun d => k ∣ d), lam d / (d : ℝ)) ^ 2 =
          (J ^ 2)⁻¹ * (Nat.totient k : ℝ)⁻¹ := by
      intro k hk
      simpa [zpow_neg, zpow_two] using hdiag_k k hk
    rw [Finset.sum_congr rfl hdiag_k', ← Finset.mul_sum]
    change (Y : ℝ) * ((J ^ 2)⁻¹ * J) = (Y : ℝ) / J
    field_simp
  -- Step 6: Bound the error term `(∑_{d ∈ Tz} |lam d|) ^ 2 ≤ 4 * z ^ 6`.
  have hJ_ge_half : (1 / 2 : ℝ) ≤ J := by
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      rw [Real.log_inv] at h
      linarith
    have hlogz_ge : Real.log 2 ≤ Real.log (z : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hz)
    linarith
  have hTz_sub : Tz ⊆ Icc 1 z := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hd).1).1 hQz_pos,
      (mem_filter.mp hd).2⟩
  have hlam_abs : ∀ d ∈ Tz, |lam d| ≤ 2 * (z : ℝ) ^ 2 := by
    intro d hd
    have hd_le : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast (mem_filter.mp hd).2
    dsimp [lam]
    rw [abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg d), abs_of_pos hJ_pos]
    have hdJ_le : (d : ℝ) / J ≤ 2 * (z : ℝ) := by
      rw [div_le_iff₀ hJ_pos]
      nlinarith
    have hsum_abs :
        |∑ k ∈ Tz.filter (fun k => d ∣ k),
          ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
            (Nat.totient k : ℝ)| ≤ (z : ℝ) := by
      calc
        |∑ k ∈ Tz.filter (fun k => d ∣ k),
            ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
              (Nat.totient k : ℝ)|
            ≤ ∑ k ∈ Tz.filter (fun k => d ∣ k),
                |((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
                  (Nat.totient k : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Tz.filter (fun k => d ∣ k), (1 : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkTz := (mem_filter.mp hk).1
            have hkQz := (mem_filter.mp hkTz).1
            have hdk := (mem_filter.mp hk).2
            have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hkQz).1 hQz_pos
            have hphi_ge1 : (1 : ℝ) ≤ (Nat.totient k : ℝ) := by
              exact_mod_cast Nat.totient_pos.mpr hk_pos
            have hkd_Qz : k / d ∈ Qz.divisors :=
              Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd hdk) (Nat.mem_divisors.mp hkQz).1,
                hQz_pos.ne'⟩
            have hm1 : |(ArithmeticFunction.moebius (k / d) : ℝ)| = 1 :=
              sq_eq_one_iff.mp (hsqf (k / d) hkd_Qz).1 |>.elim (fun h => by rw [h]; simp) (fun h => by rw [h]; simp)
            have hm2 : |(ArithmeticFunction.moebius k : ℝ)| = 1 :=
              sq_eq_one_iff.mp (hsqf k hkQz).1 |>.elim (fun h => by rw [h]; simp) (fun h => by rw [h]; simp)
            rw [abs_div, abs_mul, hm1, hm2, mul_one, abs_of_pos (by linarith)]
            exact div_le_one_of_le₀ hphi_ge1 (by positivity)
        _ = ((Tz.filter (fun k => d ∣ k)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (z : ℝ) := by
            have hcard : (Tz.filter (fun k => d ∣ k)).card ≤ z :=
              ((Finset.card_le_card (Finset.filter_subset _ Tz)).trans (Finset.card_le_card hTz_sub)).trans (by simp)
            exact_mod_cast hcard
    calc
      ((d : ℝ) / J) * |∑ k ∈ Tz.filter (fun k => d ∣ k),
          ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ)) /
            (Nat.totient k : ℝ)|
          ≤ (2 * (z : ℝ)) * (z : ℝ) :=
        mul_le_mul hdJ_le hsum_abs (abs_nonneg _) (by positivity)
      _ = 2 * (z : ℝ) ^ 2 := by ring
  have hsum_lam_abs : ∑ d ∈ Tz, |lam d| ≤ 2 * (z : ℝ) ^ 3 := by
    calc
      ∑ d ∈ Tz, |lam d| ≤ ∑ _d ∈ Tz, (2 * (z : ℝ) ^ 2) := Finset.sum_le_sum hlam_abs
      _ = (Tz.card : ℝ) * (2 * (z : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (z : ℝ) * (2 * (z : ℝ) ^ 2) := by
        have hcard : (Tz.card : ℝ) ≤ (z : ℝ) := by
          have hc : Tz.card ≤ z := (Finset.card_le_card hTz_sub).trans (by simp)
          exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * (z : ℝ) ^ 3 := by ring
  have hrem_term : ∀ d₁ ∈ Tz, ∀ d₂ ∈ Tz,
      lam d₁ * lam d₂ *
        ((((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ) -
          (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) ≤
      |lam d₁| * |lam d₂| := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hd₁).1).1 hQz_pos
    have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (mem_filter.mp hd₂).1).1 hQz_pos
    have hl_pos : 0 < Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁_pos.ne' hd₂_pos.ne')
    have herr := hmult_approx (Nat.lcm d₁ d₂) hl_pos
    set a : ℝ := lam d₁
    set b : ℝ := lam d₂
    set r : ℝ := (((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ) -
      (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)
    have h1 : a * b * r ≤ |a * b * r| := le_abs_self _
    rw [abs_mul, abs_mul] at h1
    exact h1.trans (mul_le_of_le_one_right (mul_nonneg (abs_nonneg a) (abs_nonneg b)) herr)
  have hrem_bound :
      (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
        lam d₁ * lam d₂ * (((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ)) -
      (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz, lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))) ≤
      4 * (z : ℝ) ^ 6 := by
    have hdiff_eq :
        (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
          lam d₁ * lam d₂ * (((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ)) -
        (∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz, lam d₁ * lam d₂ * ((Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))) =
        ∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
          lam d₁ * lam d₂ *
            ((((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ) -
              (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d₂ _ => by ring
    rw [hdiff_eq]
    calc
      ∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz,
          lam d₁ * lam d₂ *
            ((((Icc (M + 1) (M + Y)).filter fun n => Nat.lcm d₁ d₂ ∣ n).card : ℝ) -
              (Y : ℝ) / (Nat.lcm d₁ d₂ : ℝ))
          ≤ ∑ d₁ ∈ Tz, ∑ d₂ ∈ Tz, |lam d₁| * |lam d₂| :=
            Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum (hrem_term d₁ hd₁)
      _ = (∑ d ∈ Tz, |lam d|) ^ 2 := by rw [sq, Finset.sum_mul_sum]
      _ ≤ (2 * (z : ℝ) ^ 3) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hsum_lam_abs 2
      _ = 4 * (z : ℝ) ^ 6 := by ring
  have hmain_le : (Y : ℝ) / J ≤ (Y : ℝ) / Real.log (z : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg Y) hlogz_pos hJ_ge_log
  linarith [hsum_ind, hquad_eq, hrem_bound, hmain_le]

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro hH1 hH2
  obtain ⟨c₁, hc₁_pos, hExp⟩ := hH1
  obtain ⟨θ, hθ_pos, hθ_lt1, hAmp⟩ := hH2
  refine ⟨θ, hθ_pos, hθ_lt1, fun ε hε hε1 => ?_⟩
  have hη_pos : 0 < c₁ * θ * ε := by positivity
  filter_upwards [hExp θ hθ_pos hθ_lt1 ε hε hε1, hAmp ε hε hε1 (c₁ * θ * ε) hη_pos] with x h1 h2
  intro L D Q hprem
  exact h2 (h1 hprem)

end OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1_H2_R1
