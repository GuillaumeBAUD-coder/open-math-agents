import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1

-- Reduction Erdos687.erdos_687.parts.iii.R1.H2.R1 of Step H2 of Erdős Problem 687 — iii
-- Credit: @santiemanuel
-- Each H becomes its own step once this file is accepted. Proving all of them closes H2.

/-!
# Upper-sieve and CRT-tiling reduction of `Erdos687.erdos_687.parts.iii.R1.H2`

We reduce the Buchstab large-prime tail bound `OMA.R_Erdos687_erdos_687_parts_iii_R1.H2` to two
cleaner, completely decoupled ingredients:

1. `H1`: The **upper fundamental lemma of the shifted sieve** with super-cubic accuracy
   `1 + δ / s ^ 3` uniformly for all `s ≥ s₀` (the upper-bound counterpart of `R1.H1`,
   unconditionally provable via Brun's combinatorial upper sieve).
2. `H2`: A **short-interval lower bound for `x`-rough numbers** in arbitrary translates
   `(M, M + ⌈x ^ (1 + ε)⌉₊]` for `0 < ε < 1` (the shift-free, `s`-free, sub-quadratic core
   of Erdős Problem 687 (iii)).

Inside this reduction we prove:
- `eulerProd_le_inv_log`: Mertens' elementary Euler-product upper bound
  `∏_{p ≤ x} (1 - 1 / p) ≤ (Real.log x)⁻¹` for `x ≥ 2`, via truncated Euler expansion of the
  harmonic sum.
- `shifted_sieve_eq_rough_Icc`: Exact Chinese-remainder-theorem bijection identifying arbitrary
  shifted-sieve counts `S(y, x; a)` with `x`-rough integers in a single translate `[M + 1, M + y]`.
- `rough_Icc_tiling`: Block-tiling lift extending any uniform short-interval (`0 < ε < 1`)
  lower bound on `x`-rough numbers to all `ε > 0` with at most a factor of `1 / 2` loss.
- `main`: Combining `H1`, `H2`, `OMA.R_Erdos687_erdos_687_parts_iii_R1.buchstab_identity`, and
  `OMA.R_Erdos687_erdos_687_parts_iii_R1.chebyshev_eulerProd_ratio` yields
  `OMA.R_Erdos687_erdos_687_parts_iii_R1.H2`.
-/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1

open Filter Finset Real

/-- Upper fundamental lemma of the shifted sieve with super-cubic relative accuracy,
uniform for all `s ≥ s₀`: for every `δ > 0`, there is `s₀ ≥ 2` such that for all `s ≥ s₀`,
all sufficiently large `z`, every `y ≥ z ^ s`, and every residue assignment `a : ℕ → ℕ`,
at most `(1 + δ / s ^ 3) * y * ∏_{p ≤ z} (1 - 1 / p)` integers in `[1, y]` avoid every
congruence `a p (mod p)` for primes `p ≤ z`. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℕ, 2 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s →
    ∀ᶠ z : ℕ in Filter.atTop, ∀ y : ℕ, z ^ s ≤ y → ∀ a : ℕ → ℕ,
      (((Finset.Icc 1 y).filter fun m =>
        ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) ≤
      (1 + δ / (s : ℝ) ^ 3) * (y : ℝ) *
        (∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))

/-- Short-interval lower bound for `x`-rough numbers (integers with least prime factor `> x`):
there exists `c > 0` such that for every `ε ∈ (0, 1)`, all sufficiently large `x`, and every
shift `M : ℕ`, letting `y = ⌈x ^ (1 + ε)⌉₊`, the interval `[M + 1, M + y]` contains at least
`c * y / log x` integers not divisible by any prime `p ≤ x`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ᶠ x : ℕ in Filter.atTop, ∀ M : ℕ,
      let y := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      c * (y : ℝ) / Real.log (x : ℝ) ≤
      (((Finset.Icc (M + 1) (M + y)).filter fun n =>
        ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ)

lemma log_le_harmonic {x : ℕ} (hx : 1 ≤ x) :
    Real.log (x : ℝ) ≤ ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ := by
  have hstrong : Real.log ((x + 1 : ℕ) : ℝ) ≤ ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ := by
    induction x, hx using Nat.le_induction with
    | base =>
      simp only [Nat.reduceAdd, Icc_self, sum_singleton, Nat.cast_one, inv_one, Nat.cast_ofNat]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2_pos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
          ((m + 1 : ℕ) : ℝ)⁻¹ := by
        rw [← Real.log_div hm2_pos.ne' hm1_pos.ne']
        have hdiv : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = ((m + 1 : ℕ) : ℝ)⁻¹ := by
          push_cast
          field_simp
          ring
        linarith [Real.log_le_sub_one_of_pos (div_pos hm2_pos hm1_pos)]
      have heq : m + 1 + 1 = m + 2 := by omega
      rw [heq]
      linarith
  have hmono : Real.log (x : ℝ) ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < x by omega)) (by exact_mod_cast Nat.le_succ x)
  exact hmono.trans hstrong

private lemma smooth_recip_sum_le_inv_eulerProd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (x : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 x)
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
        have hmp : n.minFac.Prime := Nat.minFac_prime hne
        have hmd : n.minFac ∣ n := Nat.minFac_dvd n
        exact Finset.notMem_empty _ (hsmooth n hn n.minFac hmp hmd)
      exact mem_singleton.mpr hn1
    calc
      ∑ n ∈ A, (n : ℝ)⁻¹ ≤ ∑ n ∈ ({1} : Finset ℕ), (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hA_sub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | cons q T hqT ih =>
    have hq : q.Prime := hS q (mem_cons_self q T)
    have hT : ∀ p ∈ T, p.Prime := fun p hp => hS p (mem_cons_of_mem hp)
    let Ae : ℕ → Finset ℕ := fun e => A.filter (fun n => n.factorization q = e)
    have hpart : A = (range (x + 1)).biUnion Ae := by
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
      · rintro ⟨_, _, hn, _⟩
        exact hn
    have hpw : (range (x + 1) : Set ℕ).PairwiseDisjoint Ae := by
      intro e₁ _ e₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro n hn₁ hn₂
      exact hne ((mem_filter.mp hn₁).2.symm.trans (mem_filter.mp hn₂).2)
    have hsum_e : ∀ e ∈ range (x + 1),
        ∑ n ∈ Ae e, (n : ℝ)⁻¹ ≤
          ((q : ℝ)⁻¹) ^ e * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro e _
      let Be := (Ae e).image (fun n => n / q ^ e)
      have hBe_sub : Be ⊆ Icc 1 x := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnA : n ∈ A := (mem_filter.mp hn).1
        have heq : n.factorization q = e := (mem_filter.mp hn).2
        have hnI := mem_Icc.mp (hA hnA)
        have hdvd : q ^ e ∣ n := heq ▸ Nat.ordProj_dvd n q
        have hmul : q ^ e * (n / q ^ e) = n := Nat.mul_div_cancel' hdvd
        have hm1 : 1 ≤ n / q ^ e :=
          Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega
        exact mem_Icc.mpr ⟨hm1, (Nat.div_le_self n (q ^ e)).trans hnI.2⟩
      have hBe_smooth : ∀ m ∈ Be, ∀ p : ℕ, p.Prime → p ∣ m → p ∈ T := by
        intro m hm p hp hpm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        have hnA : n ∈ A := (mem_filter.mp hn).1
        have heq : n.factorization q = e := (mem_filter.mp hn).2
        have hnI := mem_Icc.mp (hA hnA)
        have hdvd : q ^ e ∣ n := heq ▸ Nat.ordProj_dvd n q
        have hmul : q ^ e * (n / q ^ e) = n := Nat.mul_div_cancel' hdvd
        have hpn : p ∣ n := dvd_trans hpm ⟨q ^ e, by rw [Nat.mul_comm]; exact hmul.symm⟩
        have hp_mem : p ∈ cons q T hqT := hsmooth n hnA p hp hpn
        rcases mem_cons.mp hp_mem with hpq | hpT
        · exfalso
          rw [hpq] at hpm
          obtain ⟨k, hk⟩ := hpm
          have hpow1 : q ^ (e + 1) ∣ n := ⟨k, by
            rw [pow_succ, mul_assoc, ← hk, hmul]⟩
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
    have hgeom : ∑ e ∈ range (x + 1), ((q : ℝ)⁻¹) ^ e ≤ (1 - (q : ℝ)⁻¹)⁻¹ := by
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
      have hq_inv_le : (q : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq2
      have h1_sub_pos : 0 < 1 - (q : ℝ)⁻¹ := by linarith
      have hq_inv_ne : (q : ℝ)⁻¹ ≠ 1 := by linarith
      rw [geom_sum_eq hq_inv_ne]
      have hpow_nn : (0 : ℝ) ≤ ((q : ℝ)⁻¹) ^ (x + 1) := by positivity
      have heq : (((q : ℝ)⁻¹) ^ (x + 1) - 1) / ((q : ℝ)⁻¹ - 1) =
          (1 - ((q : ℝ)⁻¹) ^ (x + 1)) / (1 - (q : ℝ)⁻¹) := by
        rw [← neg_div_neg_eq]
        congr 1 <;> ring
      rw [heq, inv_eq_one_div (1 - (q : ℝ)⁻¹)]
      exact div_le_div_of_nonneg_right (by linarith) h1_sub_pos.le
    have hT_nn : 0 ≤ ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hT p hp).two_le
      have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    calc
      ∑ n ∈ A, (n : ℝ)⁻¹ = ∑ e ∈ range (x + 1), ∑ n ∈ Ae e, (n : ℝ)⁻¹ := by
        conv_lhs => rw [hpart]
        exact Finset.sum_biUnion hpw
      _ ≤ ∑ e ∈ range (x + 1), ((q : ℝ)⁻¹) ^ e * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ :=
        Finset.sum_le_sum hsum_e
      _ = (∑ e ∈ range (x + 1), ((q : ℝ)⁻¹) ^ e) * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (1 - (q : ℝ)⁻¹)⁻¹ * ∏ p ∈ T, (1 - (p : ℝ)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_right hgeom hT_nn
      _ = ∏ p ∈ cons q T hqT, (1 - (p : ℝ)⁻¹)⁻¹ := by rw [Finset.prod_cons]

/-- Elementary Mertens Euler-product upper bound: `∏_{p ≤ x} (1 - 1 / p) ≤ (Real.log x)⁻¹`
for every `x ≥ 2`. -/
lemma eulerProd_le_inv_log {x : ℕ} (hx : 2 ≤ x) :
    ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) ≤ (Real.log (x : ℝ))⁻¹ := by
  let P := (range (x + 1)).filter Nat.Prime
  have hlog_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hV_pos : 0 < ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  have hsmooth : ∀ n ∈ Icc 1 x, ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P := by
    intro n hn p hp hpn
    have hnI := mem_Icc.mp hn
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩
  have h1 : Real.log (x : ℝ) ≤ ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ := log_le_harmonic (by omega)
  have h2 : ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ :=
    smooth_recip_sum_le_inv_eulerProd P (fun _ hp => (mem_filter.mp hp).2) x (Icc 1 x) le_rfl hsmooth
  have h3 : Real.log (x : ℝ) ≤ (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ := by
    rw [Finset.prod_inv_distrib] at h2
    exact h1.trans h2
  have h4 : Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ 1 := by
    calc
      Real.log (x : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹))
          ≤ (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_right h3 hV_pos.le
      _ = 1 := inv_mul_cancel₀ hV_pos.ne'
  rw [inv_eq_one_div, le_div_iff₀ hlog_pos]
  linarith

/-- Exact Chinese-remainder-theorem identification of shifted-sieve survivors in `[1, y]`
with `x`-rough integers in a single translated interval `[M + 1, M + y]`. -/
lemma shifted_sieve_eq_rough_Icc (x y : ℕ) (a : ℕ → ℕ) :
    ∃ M : ℕ,
      ((Icc 1 y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card =
      ((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card := by
  let P := (range (x + 1)).filter Nat.Prime
  let b : ℕ → ℕ := fun p => (p - a p % p) % p
  have hs : ∀ p ∈ P, id p ≠ 0 := fun p hp => (mem_filter.mp hp).2.ne_zero
  have pp : Set.Pairwise (P : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).2 hpq
  let k := Nat.chineseRemainderOfFinset b id P hs pp
  refine ⟨(k : ℕ), ?_⟩
  have hiff : ∀ p ≤ x, p.Prime → ∀ m : ℕ, m ≡ a p [MOD p] ↔ p ∣ (m + (k : ℕ)) := by
    intro p hpx hpp m
    have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
    have hkp : (k : ℕ) % p = b p % p := k.2 p hpP
    have hbp_lt : b p < p := Nat.mod_lt _ hpp.pos
    have hmod : (m + (k : ℕ)) % p = (m % p + b p) % p := by
      rw [Nat.add_mod, hkp, Nat.mod_eq_of_lt hbp_lt]
    rw [Nat.dvd_iff_mod_eq_zero, hmod]
    have hm_lt : m % p < p := Nat.mod_lt m hpp.pos
    have ha_lt : a p % p < p := Nat.mod_lt (a p) hpp.pos
    by_cases ha0 : a p % p = 0
    · have hbp0 : b p = 0 := by dsimp [b]; rw [ha0, Nat.sub_zero, Nat.mod_self]
      rw [hbp0, Nat.add_zero, Nat.mod_eq_of_lt hm_lt]
      change m % p = a p % p ↔ m % p = 0
      omega
    · have hbp_eq : b p = p - a p % p := by
        dsimp [b]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hbp_eq]
      change m % p = a p % p ↔ (m % p + (p - a p % p)) % p = 0
      constructor
      · intro h
        rw [h, Nat.add_sub_of_le ha_lt.le, Nat.mod_self]
      · intro h
        obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h
        have ht1 : t = 1 := by
          have hpos : 0 < p * t := by omega
          have hlt2 : p * t < p * 2 := by omega
          have ht_pos : 0 < t := by
            by_contra h0
            have ht0 : t = 0 := by omega
            rw [ht0, mul_zero] at hpos
            omega
          have ht_lt2 : t < 2 := Nat.lt_of_mul_lt_mul_left hlt2
          omega
        rw [ht1, mul_one] at ht
        omega
  refine Finset.card_bij (fun m _ => m + (k : ℕ)) ?_ ?_ ?_
  · intro m hm
    obtain ⟨hmI, hmA⟩ := mem_filter.mp hm
    have hmI' := mem_Icc.mp hmI
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, fun p hpx hpp hdiv => ?_⟩
    exact hmA p hpx hpp ((hiff p hpx hpp m).mpr hdiv)
  · intro m₁ _ m₂ _ heq
    omega
  · intro n hn
    obtain ⟨hnI, hnA⟩ := mem_filter.mp hn
    have hnI' := mem_Icc.mp hnI
    refine ⟨n - (k : ℕ), mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, fun p hpx hpp hmod => ?_⟩,
      by omega⟩
    have hdiv : p ∣ (n - (k : ℕ) + (k : ℕ)) := (hiff p hpx hpp (n - (k : ℕ))).mp hmod
    rw [Nat.sub_add_cancel (by omega)] at hdiv
    exact hnA p hpx hpp hdiv

/-- Block-tiling lift: a uniform lower bound `B` on `x`-rough numbers in every interval of length
`L ≤ y` implies a lower bound `⌊y / L⌋ * B` in every interval of length `y`. -/
lemma rough_Icc_tiling {x M L y : ℕ} {B : ℝ}
    (hblock : ∀ M' : ℕ, B ≤
      (((Icc (M' + 1) (M' + L)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ)) :
    ((y / L : ℕ) : ℝ) * B ≤
      (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) := by
  let q := y / L
  let block : ℕ → Finset ℕ := fun k =>
    (Icc (M + k * L + 1) (M + k * L + L)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)
  have hsub : (range q).biUnion block ⊆
      (Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n) := by
    intro n hn
    obtain ⟨k, hk, hnk⟩ := mem_biUnion.mp hn
    obtain ⟨hnI, hnA⟩ := mem_filter.mp hnk
    have hk_lt : k < q := mem_range.mp hk
    have hnI' := mem_Icc.mp hnI
    have hmul : (k + 1) * L ≤ y :=
      (Nat.mul_le_mul_right L (by omega : k + 1 ≤ q)).trans (Nat.div_mul_le_self y L)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hnA⟩
  have hpw : (range q : Set ℕ).PairwiseDisjoint block := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn₁ hn₂
    have h1 := mem_Icc.mp (mem_filter.mp hn₁).1
    have h2 := mem_Icc.mp (mem_filter.mp hn₂).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k₁ + 1) * L ≤ k₂ * L := Nat.mul_le_mul_right L hlt
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · have : (k₂ + 1) * L ≤ k₁ * L := Nat.mul_le_mul_right L hgt
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
  have hcard_nat : ∑ k ∈ range q, (block k).card ≤
      ((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card := by
    rw [← Finset.card_biUnion hpw]
    exact Finset.card_le_card hsub
  have hcard_r : ∑ k ∈ range q, ((block k).card : ℝ) ≤
      (((Icc (M + 1) (M + y)).filter fun n => ∀ p ≤ x, p.Prime → ¬ (p ∣ n)).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hsum_lo : ((q : ℕ) : ℝ) * B ≤ ∑ k ∈ range q, ((block k).card : ℝ) := by
    calc
      ((q : ℕ) : ℝ) * B = ∑ _k ∈ range q, B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ range q, ((block k).card : ℝ) :=
        Finset.sum_le_sum fun k _ => hblock (M + k * L)
  exact hsum_lo.trans hcard_r

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R1.H2 := by
  intro hH1 hH2
  obtain ⟨c, hc_pos, hrough⟩ := hH2
  let c' : ℝ := c / 4
  have hc'_pos : 0 < c' := by dsimp [c']; positivity
  let C₀ : ℝ := 8 * Real.exp 5
  have hC₀_pos : 0 < C₀ := by positivity
  obtain ⟨s₀, hs₀2, hUpper⟩ := hH1 (c' / C₀) (by positivity)
  refine ⟨c', hc'_pos, s₀, hs₀2, fun s hs_ge ε hε => ?_⟩
  have hs2 : 2 ≤ s := hs₀2.trans hs_ge
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp (hUpper s hs_ge)
  -- First establish `2 * c' * y * V(x) ≤ S(y, x; a)` eventually in `x`, for every `ε > 0`.
  have hsurv_ev : ∀ᶠ x : ℕ in Filter.atTop, ∀ a : ℕ → ℕ,
      let y := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      2 * c' * (y : ℝ) *
        (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
      (((Icc 1 y).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
    by_cases hε1 : ε < 1
    · filter_upwards [eventually_ge_atTop 2, hrough ε hε hε1] with x hx2 hrx a
      intro y
      obtain ⟨M, hM⟩ := shifted_sieve_eq_rough_Icc x y a
      rw [hM]
      have hlog_pos : 0 < Real.log (x : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      have hV_le : ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) ≤
          (Real.log (x : ℝ))⁻¹ := eulerProd_le_inv_log hx2
      have h1 : 2 * c' * (y : ℝ) *
          (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
          c * (y : ℝ) / Real.log (x : ℝ) := by
        calc
          2 * c' * (y : ℝ) * (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
              ≤ 2 * c' * (y : ℝ) * (Real.log (x : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hV_le (by positivity)
          _ ≤ c * (y : ℝ) * (Real.log (x : ℝ))⁻¹ := by
            have : 2 * c' ≤ c := by dsimp [c']; linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg y)) (inv_nonneg.mpr hlog_pos.le)
          _ = c * (y : ℝ) / Real.log (x : ℝ) := (div_eq_mul_inv _ _).symm
      exact h1.trans (hrx M)
    · push Not at hε1
      filter_upwards [eventually_ge_atTop 2, hrough (1 / 2 : ℝ) (by norm_num) (by norm_num)] with
        x hx2 hrx a
      intro y
      let L := ⌈(x : ℝ) ^ (1 + (1 / 2 : ℝ))⌉₊
      have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
      have hL1 : 1 ≤ L := by
        have h1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 + (1 / 2 : ℝ)) := by
          calc
            (1 : ℝ) = (1 : ℝ) ^ (1 + (1 / 2 : ℝ)) := (Real.one_rpow _).symm
            _ ≤ (x : ℝ) ^ (1 + (1 / 2 : ℝ)) := Real.rpow_le_rpow (by norm_num) hx_ge1 (by norm_num)
        exact_mod_cast h1.trans (Nat.le_ceil _)
      have hLy : L ≤ y := by
        apply Nat.ceil_mono
        exact Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
      obtain ⟨M, hM⟩ := shifted_sieve_eq_rough_Icc x y a
      rw [hM]
      have hlog_pos : 0 < Real.log (x : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      have hV_le : ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) ≤
          (Real.log (x : ℝ))⁻¹ := eulerProd_le_inv_log hx2
      have htile := rough_Icc_tiling (x := x) (M := M) (L := L) (y := y) (fun M' => hrx M')
      have hqL_ge : (y : ℝ) / 2 ≤ ((y / L : ℕ) : ℝ) * (L : ℝ) := by
        have hq1 : 1 ≤ y / L := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        have hy_lt : y < (y / L + 1) * L := by
          rw [Nat.add_mul, Nat.one_mul]
          have hdm : (y / L) * L + y % L = y := by
            rw [Nat.mul_comm]
            exact Nat.div_add_mod y L
          have hml := Nat.mod_lt y (by omega : 0 < L)
          omega
        have h2 : (y / L + 1) * L ≤ 2 * ((y / L) * L) := by
          rw [Nat.add_mul, Nat.one_mul]
          have : L ≤ (y / L) * L := by
            calc
              L = 1 * L := (Nat.one_mul L).symm
              _ ≤ (y / L) * L := Nat.mul_le_mul_right L hq1
          omega
        have hnat : y ≤ 2 * ((y / L) * L) := by omega
        have hreal : (y : ℝ) ≤ 2 * (((y / L : ℕ) : ℝ) * (L : ℝ)) := by exact_mod_cast hnat
        linarith
      have h1 : 2 * c' * (y : ℝ) *
          (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
          ((y / L : ℕ) : ℝ) * (c * (L : ℝ) / Real.log (x : ℝ)) := by
        calc
          2 * c' * (y : ℝ) * (∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
              ≤ 2 * c' * (y : ℝ) * (Real.log (x : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hV_le (by positivity)
          _ = (c / Real.log (x : ℝ)) * ((y : ℝ) / 2) := by
            dsimp [c']
            ring
          _ ≤ (c / Real.log (x : ℝ)) * (((y / L : ℕ) : ℝ) * (L : ℝ)) :=
            mul_le_mul_of_nonneg_left hqL_ge (by positivity)
          _ = ((y / L : ℕ) : ℝ) * (c * (L : ℝ) / Real.log (x : ℝ)) := by ring
      exact h1.trans htile
  filter_upwards [eventually_ge_atTop (max 2 (Z₀ ^ s)),
    OMA.R_Erdos687_erdos_687_parts_iii_R1.chebyshev_eulerProd_ratio s hs2,
    hsurv_ev] with x hx hRatio hSurv
  intro a z y
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hxZ : Z₀ ^ s ≤ x := le_trans (le_max_right _ _) hx
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hz_ge_Z₀ : Z₀ ≤ z := by
    apply Nat.le_floor
    calc
      (Z₀ : ℝ) = ((Z₀ : ℝ) ^ (s : ℝ)) ^ ((1 : ℝ) / (s : ℝ)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg Z₀), mul_one_div_cancel hs_pos.ne', Real.rpow_one]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        simpa [Real.rpow_natCast] using (show ((Z₀ ^ s : ℕ) : ℝ) ≤ (x : ℝ) by exact_mod_cast hxZ)
  have hzx : z ≤ x := by
    have hrpow_le : (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) := by
      calc
        (x : ℝ) ^ ((1 : ℝ) / (s : ℝ)) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx_ge1
            ((div_le_one hs_pos).mpr (by exact_mod_cast (show 1 ≤ s by omega)))
        _ = (x : ℝ) := Real.rpow_one _
    exact_mod_cast (Nat.floor_le (by positivity)).trans hrpow_le
  have hx_rpow_ge : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
    calc
      (x : ℝ) = (x : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (x : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)
  have hzs_le_y : z ^ s ≤ y := by
    have h1 : ((z ^ s : ℕ) : ℝ) ≤ (x : ℝ) := by
      calc
        ((z ^ s : ℕ) : ℝ) = (z : ℝ) ^ s := by push_cast; rfl
        _ ≤ ((x : ℝ) ^ ((1 : ℝ) / (s : ℝ))) ^ s :=
          pow_le_pow_left₀ (Nat.cast_nonneg z) (Nat.floor_le (by positivity)) s
        _ = (x : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
            one_div_mul_cancel hs_pos.ne', Real.rpow_one]
    have h2 : (x : ℝ) ≤ (y : ℝ) := hx_rpow_ge.trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  let Vz := ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  let Vx := ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  have hRatio' : Vz ≤ C₀ * (s : ℝ) ^ 3 * Vx := hRatio
  have hup : (((Icc 1 y).filter fun m =>
      ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) ≤
      (1 + (c' / C₀) / (s : ℝ) ^ 3) * (y : ℝ) * Vz :=
    hZ₀ z hz_ge_Z₀ y hzs_le_y a
  have hlo : 2 * c' * (y : ℝ) * Vx ≤
      (((Icc 1 y).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := hSurv a
  have hbuch : (((Icc 1 y).filter fun m =>
        ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) =
      (((Icc 1 y).filter fun m =>
        ∀ p ≤ x, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) +
      ∑ q ∈ (Ioc z x).filter Nat.Prime,
        (((Icc 1 y).filter fun m =>
          m ≡ a q [MOD q] ∧ ∀ p < q, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
    exact_mod_cast OMA.R_Erdos687_erdos_687_parts_iii_R1.buchstab_identity z x y hzx a
  have herr : ((c' / C₀) / (s : ℝ) ^ 3) * Vz ≤ c' * Vx := by
    have hfac_nn : 0 ≤ (c' / C₀) / (s : ℝ) ^ 3 := by positivity
    calc
      ((c' / C₀) / (s : ℝ) ^ 3) * Vz
          ≤ ((c' / C₀) / (s : ℝ) ^ 3) * (C₀ * (s : ℝ) ^ 3 * Vx) :=
        mul_le_mul_of_nonneg_left hRatio' hfac_nn
      _ = c' * Vx := by
        have hs3_ne : (s : ℝ) ^ 3 ≠ 0 := by positivity
        field_simp
  have herr_y : ((c' / C₀) / (s : ℝ) ^ 3) * (y : ℝ) * Vz ≤ c' * (y : ℝ) * Vx := by
    have hmul := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg y)
    linarith
  linarith

end OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1
