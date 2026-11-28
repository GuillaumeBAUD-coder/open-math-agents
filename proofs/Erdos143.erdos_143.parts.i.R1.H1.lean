import OMAReductions.R_Erdos143_erdos_143_parts_i_R1

-- Proof of step Erdos143.erdos_143.parts.i.R1.H1
-- Credit: @skhakim

/-!
# Behrend's Theorem (1935): Primitive Sets Have Reciprocal Sum `o(log M)`

We prove `OMA.R_Erdos143_erdos_143_parts_i_R1.H1`: for every `ε > 0`, there exists `M₀` such that
every primitive subset `S ⊆ {2, ..., M}` with `M ≥ M₀` satisfies `∑_{a ∈ S} 1/a ≤ ε * log M`.

The proof is completely elementary and self-contained:
1. Using the divergence of `∑_p 1/(p + 1)` (from the finite Euler product lower bound on the
   harmonic sum), peel off `K` pairwise disjoint finite blocks `P_0, ..., P_{K-1}` of primes with
   `1/2 ≤ ∑_{p ∈ P_j} 1/(p + 1) ≤ 1`.
2. Factor every `a ∈ S` uniquely as `a = v * s * ∏_{p ∈ R} p` where `v` is coprime to
   `Q = ∏_{p ∈ P_all} p`, `s` is a `P_all`-smooth square, and `R ⊆ P_all`. Primitivity of `S`
   implies that for each fixed `(v, s)`, the subsets `R` form an antichain in `P_all.powerset`.
3. Decompose the product Bernoulli(`1/(p+1)`) measure on `P_all.powerset` across the `K` blocks
   into a convex combination of active fair-coin coordinates (weight `2/9` per block) and frozen
   coordinates. Applying Sperner's theorem (via the LYM inequality) on active coordinates and
   Chebyshev's inequality to the number of active coordinates bounds the normalized antichain
   weight by `81 / K + 6 / √K`.
4. Multiply by the `P_all`-smooth square sum `∏ (1 - 1/p²)⁻¹` and the `Q`-block bound
   `∑_{v ≤ M, (v, Q) = 1} 1/v ≤ Q + (φ(Q)/Q) (log M + 1)`. The Euler factors cancel identically,
   yielding `∑_{a ∈ S} 1/a ≤ (81 / K + 6 / √K) * (log M + C(Q)) ≤ ε * log M` for `M` large.
-/

namespace Erdos143R1H1

open Finset BigOperators

/- ## Section 1: Harmonic sums, Euler products, and disjoint prime blocks -/

lemma log_succ_le_harmonic (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    have hsub : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsub, Finset.sum_insert (by simp)]
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
        1 / ((m + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hm2.ne' hm1.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hm2 hm1)
      have hdiv : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
        push_cast; field_simp; ring
      linarith
    linarith

lemma harmonic_le_log_add_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  induction N with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; simp
    · have hm1 : 1 ≤ m := by omega
      have hsub : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      have hih := ih hm1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
          Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hmpos hm1pos)
        rw [Real.log_div hmpos.ne' hm1pos.ne'] at h1
        have hdiv : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp; ring
        linarith
      linarith

lemma geom_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ e ∈ Finset.range n, r ^ e ≤ (1 - r)⁻¹ := by
  rw [geom_sum_eq hr1.ne]
  have h1 : 0 < 1 - r := sub_pos.mpr hr1
  have hrn : 0 ≤ r ^ n := pow_nonneg hr0 n
  rw [show (r ^ n - 1) / (r - 1) = (1 - r ^ n) / (1 - r) by
    have : r - 1 = -(1 - r) := by ring
    rw [this, div_neg]; ring]
  rw [div_eq_mul_inv]
  calc (1 - r ^ n) * (1 - r)⁻¹
      ≤ 1 * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr h1.le)
    _ = (1 - r)⁻¹ := one_mul _

/-- Every positive integer `n ≤ N` factors completely over the primes in `[1, N]`. -/
lemma prod_prime_pow_padicValNat_eq {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p ^ padicValNat p n = n := by
  have hn0 : n ≠ 0 := by omega
  have hsub : n.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    exact ⟨⟨hp_prime.one_lt.le, Nat.le_trans (Nat.le_of_dvd (by omega) hp_dvd) hnN⟩, hp_prime⟩
  rw [← Finset.prod_subset hsub]
  · have hfac := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod] at hfac
    have hsupp : n.factorization.support = n.primeFactors := rfl
    rw [hsupp] at hfac
    conv_rhs => rw [← hfac]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
  · intro p hp hpnot
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hndvd : ¬ p ∣ n := fun hdvd => hpnot (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hn0⟩)
    simp [padicValNat.eq_zero_of_not_dvd hndvd]

/-- Finite Euler product lower bound on the harmonic sum. -/
lemma harmonic_le_euler_prod (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤
      ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
  classical
  let Pr := (Finset.Icc 1 N).filter Nat.Prime
  have hgeom : ∀ p ∈ Pr,
      ∑ e ∈ Finset.range (N + 1), ((1 : ℝ) / (p : ℝ)) ^ e ≤ (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    exact geom_sum_le_inv (by positivity) (by rw [div_lt_one (by linarith)]; linarith) (N + 1)
  have hprod_le :
      ∏ p ∈ Pr, ∑ e ∈ Finset.range (N + 1), ((1 : ℝ) / (p : ℝ)) ^ e ≤
      ∏ p ∈ Pr, (1 - (1 : ℝ) / (p : ℝ))⁻¹ :=
    Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun e _ => by positivity) hgeom
  refine le_trans ?_ hprod_le
  rw [Finset.prod_sum]
  -- Embed `n ∈ Icc 1 N` into `Pr.pi (fun _ => range (N + 1))` via `p ↦ padicValNat p n`.
  let emb : ℕ → ∀ p, p ∈ Pr → ℕ := fun n p _ => padicValNat p n
  have hmaps : ∀ n ∈ Finset.Icc 1 N, emb n ∈ Pr.pi (fun _ => Finset.range (N + 1)) := by
    intro n hn
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hpow_dvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
    have hpow_le : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (by omega) hpow_dvd
    have h2pow : padicValNat p n < 2 ^ padicValNat p n := Nat.lt_two_pow_self
    have h2le : 2 ^ padicValNat p n ≤ p ^ padicValNat p n := Nat.pow_le_pow_left hp2 _
    dsimp [emb]; omega
  have hinj : ∀ n₁ ∈ Finset.Icc 1 N, ∀ n₂ ∈ Finset.Icc 1 N, emb n₁ = emb n₂ → n₁ = n₂ := by
    intro n₁ hn₁ n₂ hn₂ heq
    have h1 := prod_prime_pow_padicValNat_eq (Finset.mem_Icc.mp hn₁).1 (Finset.mem_Icc.mp hn₁).2
    have h2 := prod_prime_pow_padicValNat_eq (Finset.mem_Icc.mp hn₂).1 (Finset.mem_Icc.mp hn₂).2
    rw [← h1, ← h2]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpeq : emb n₁ p hp = emb n₂ p hp := by rw [heq]
    exact congrArg (p ^ ·) hpeq
  have hval : ∀ n ∈ Finset.Icc 1 N,
      (1 : ℝ) / (n : ℝ) = ∏ p ∈ Pr.attach, ((1 : ℝ) / (p.1 : ℝ)) ^ (emb n p.1 p.2) := by
    intro n hn
    have hfac := prod_prime_pow_padicValNat_eq (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    have hfacR : (n : ℝ) = ∏ p ∈ Pr.attach, ((p.1 : ℝ) ^ (emb n p.1 p.2)) := by
      have : (n : ℝ) = ((∏ p ∈ Pr, p ^ padicValNat p n : ℕ) : ℝ) := by rw [hfac]
      rw [this, Nat.cast_prod]
      simp only [Nat.cast_pow, emb]
      exact (Finset.prod_attach Pr (fun p => (p : ℝ) ^ padicValNat p n)).symm
    rw [hfacR, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [one_div, inv_pow]
  calc ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ∏ p ∈ Pr.attach, ((1 : ℝ) / (p.1 : ℝ)) ^ (emb n p.1 p.2) :=
        Finset.sum_congr rfl hval
    _ = ∑ f ∈ (Finset.Icc 1 N).image emb, ∏ p ∈ Pr.attach, ((1 : ℝ) / (p.1 : ℝ)) ^ (f p.1 p.2) :=
        (Finset.sum_image (f := fun g => ∏ p ∈ Pr.attach, ((1 : ℝ) / (p.1 : ℝ)) ^ (g p.1 p.2))
          (fun n₁ hn₁ n₂ hn₂ h => hinj n₁ hn₁ n₂ hn₂ h)).symm
    _ ≤ ∑ f ∈ Pr.pi (fun _ => Finset.range (N + 1)),
          ∏ p ∈ Pr.attach, ((1 : ℝ) / (p.1 : ℝ)) ^ (f p.1 p.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
        intro f hf
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hf
        exact hmaps n hn

/-- `∑_{p ≤ N} 1/(p + 1)` is unbounded as `N → ∞`. -/
lemma prime_rec_succ_unbounded (B : ℝ) :
    ∃ N : ℕ, B ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1) := by
  let N : ℕ := Nat.ceil (Real.exp (Real.exp (3 * max B 0))) + 1
  refine ⟨N, ?_⟩
  have hlog_le : Real.exp (3 * max B 0) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    have h1 : Real.exp (Real.exp (3 * max B 0)) ≤ ((N + 1 : ℕ) : ℝ) := by
      have hceil : Real.exp (Real.exp (3 * max B 0)) ≤
          (Nat.ceil (Real.exp (Real.exp (3 * max B 0))) : ℝ) := Nat.le_ceil _
      have hN : (Nat.ceil (Real.exp (Real.exp (3 * max B 0))) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        dsimp [N]; push_cast; linarith
      linarith
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact h1
  have heuler := (log_succ_le_harmonic N).trans (harmonic_le_euler_prod N)
  have hprod_exp :
      ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤
      Real.exp (3 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      exact inv_nonneg.mpr (by linarith)
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      have h1 : (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤ 1 + 3 * ((1 : ℝ) / ((p : ℝ) + 1)) := by
        have hpos1 : (0 : ℝ) < 1 - (1 : ℝ) / (p : ℝ) := by
          rw [sub_pos, div_lt_one (by linarith)]; linarith
        rw [inv_le_iff_one_le_mul₀' hpos1]
        have hcalc : (1 - (1 : ℝ) / (p : ℝ)) * (1 + 3 * ((1 : ℝ) / ((p : ℝ) + 1))) - 1 =
            (2 * (p : ℝ) - 4) / ((p : ℝ) * ((p : ℝ) + 1)) := by
          field_simp; ring
        have hnn : 0 ≤ (2 * (p : ℝ) - 4) / ((p : ℝ) * ((p : ℝ) + 1)) :=
          div_nonneg (by linarith) (by positivity)
        linarith
      exact h1.trans (by simpa [add_comm] using Real.add_one_le_exp (3 * ((1 : ℝ) / ((p : ℝ) + 1))))
  have hexp_le : Real.exp (3 * max B 0) ≤
      Real.exp (3 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1)) :=
    hlog_le.trans (heuler.trans hprod_exp)
  exact le_trans (le_max_left B 0) (by linarith [Real.exp_le_exp.mp hexp_le])

/-- Above any threshold `M`, there is a finite set `B` of primes `> M` with
`1/2 ≤ ∑_{p ∈ B} 1/(p + 1) ≤ 1`. -/
lemma exists_prime_block_above (M : ℕ) :
    ∃ B : Finset ℕ, (∀ p ∈ B, M < p ∧ p.Prime) ∧
      (1 / 2 : ℝ) ≤ ∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1) ∧
      ∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
  classical
  let sM : ℝ := ∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1)
  have hex : ∃ N : ℕ, (1 / 2 : ℝ) ≤ ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1) := by
    obtain ⟨N, hN⟩ := prime_rec_succ_unbounded (sM + 1)
    refine ⟨max M N, ?_⟩
    have hsplit : (Finset.Icc 1 (max M N)).filter Nat.Prime =
        (Finset.Icc 1 M).filter Nat.Prime ∪ (Finset.Ioc M (max M N)).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hle : p ≤ M
        · exact Or.inl ⟨⟨h1, hle⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
    have hdisj : Disjoint ((Finset.Icc 1 M).filter Nat.Prime) ((Finset.Ioc M (max M N)).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp1 hp2
      omega
    have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ (Finset.Icc 1 (max M N)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, le_trans hp.1.2 (le_max_right M N)⟩, hp.2⟩
    have hge : sM + 1 ≤ ∑ p ∈ (Finset.Icc 1 (max M N)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1) :=
      hN.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
    rw [hsplit, Finset.sum_union hdisj] at hge
    linarith
  let N₀ := Nat.find hex
  have hN₀ : (1 / 2 : ℝ) ≤ ∑ p ∈ (Finset.Ioc M N₀).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1) :=
    Nat.find_spec hex
  have hN₀_gt : M < N₀ := by
    by_contra hle
    have hemp : (Finset.Ioc M N₀).filter Nat.Prime = ∅ := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
    rw [hemp, Finset.sum_empty] at hN₀
    linarith
  have hprev : ∑ p ∈ (Finset.Ioc M (N₀ - 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) + 1) < 1 / 2 := by
    have hmin := Nat.find_min hex (show N₀ - 1 < N₀ by omega)
    linarith
  refine ⟨(Finset.Ioc M N₀).filter Nat.Prime, ?_, hN₀, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.1.1, hp.2⟩
  · have hstep : (Finset.Ioc M N₀).filter Nat.Prime =
        (if N₀.Prime then insert N₀ ((Finset.Ioc M (N₀ - 1)).filter Nat.Prime)
         else (Finset.Ioc M (N₀ - 1)).filter Nat.Prime) := by
      split_ifs with hp
      · ext p; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
        constructor
        · rintro ⟨⟨h1, h2⟩, hpp⟩
          by_cases heq : p = N₀
          · exact Or.inl heq
          · exact Or.inr ⟨⟨h1, by omega⟩, hpp⟩
        · rintro (rfl | ⟨⟨h1, h2⟩, hpp⟩)
          · exact ⟨⟨hN₀_gt, le_rfl⟩, hp⟩
          · exact ⟨⟨h1, by omega⟩, hpp⟩
      · ext p; simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, h2⟩, hpp⟩
          have hne : p ≠ N₀ := fun h => hp (h ▸ hpp)
          exact ⟨⟨h1, by omega⟩, hpp⟩
        · rintro ⟨⟨h1, h2⟩, hpp⟩; exact ⟨⟨h1, by omega⟩, hpp⟩
    rw [hstep]
    split_ifs with hp
    · have hnot : N₀ ∉ (Finset.Ioc M (N₀ - 1)).filter Nat.Prime := by
        simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
      rw [Finset.sum_insert hnot]
      have hN₀2 : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hp.two_le
      have hterm : (1 : ℝ) / ((N₀ : ℝ) + 1) ≤ 1 / 3 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      linarith
    · linarith

/-- Peel off `K` pairwise disjoint finite blocks of primes with reciprocal-plus-one sum in `[1/2, 1]`. -/
lemma exists_disjoint_prime_blocks (K : ℕ) :
    ∃ P : Fin K → Finset ℕ,
      (∀ j : Fin K, ∀ p ∈ P j, p.Prime) ∧
      (∀ i j : Fin K, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ j : Fin K, (1 / 2 : ℝ) ≤ ∑ p ∈ P j, (1 : ℝ) / ((p : ℝ) + 1) ∧
        ∑ p ∈ P j, (1 : ℝ) / ((p : ℝ) + 1) ≤ 1) := by
  induction K with
  | zero =>
    exact ⟨Fin.elim0, fun j => j.elim0, fun i => i.elim0, fun j => j.elim0⟩
  | succ k ih =>
    obtain ⟨P, hPprime, hPdisj, hPsum⟩ := ih
    let U : Finset ℕ := Finset.univ.biUnion P
    let M : ℕ := U.sup id
    obtain ⟨B, hBgt, hBlo, hBhi⟩ := exists_prime_block_above M
    let P' : Fin (k + 1) → Finset ℕ := Fin.snoc P B
    refine ⟨P', ?_, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · intro p hp
        dsimp only [P'] at hp; rw [Fin.snoc_last] at hp
        exact (hBgt p hp).2
      · intro i p hp
        dsimp only [P'] at hp; rw [Fin.snoc_castSucc] at hp
        exact hPprime i p hp
    · intro i j
      refine Fin.lastCases ?_ ?_ i
      · refine Fin.lastCases ?_ ?_ j
        · intro hij; exact (hij rfl).elim
        · intro j' _
          dsimp only [P']; rw [Fin.snoc_last, Fin.snoc_castSucc]
          rw [Finset.disjoint_left]
          intro p hpB hpj
          have hgt := (hBgt p hpB).1
          have hle : p ≤ M := Finset.le_sup (f := id)
            (Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ _, hpj⟩)
          omega
      · intro i'
        refine Fin.lastCases ?_ ?_ j
        · intro _
          dsimp only [P']; rw [Fin.snoc_castSucc, Fin.snoc_last]
          rw [Finset.disjoint_left]
          intro p hpi hpB
          have hgt := (hBgt p hpB).1
          have hle : p ≤ M := Finset.le_sup (f := id)
            (Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _, hpi⟩)
          omega
        · intro j' hij
          dsimp only [P']; rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hPdisj i' j' (fun h => hij (congrArg Fin.castSucc h))
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · dsimp only [P']; rw [Fin.snoc_last]; exact ⟨hBlo, hBhi⟩
      · intro i; dsimp only [P']; rw [Fin.snoc_castSucc]; exact hPsum i

/- ## Section 2: Sperner's theorem (via LYM) and central binomial upper bound -/

/-- Central binomial upper bound: `(C(m, m/2) / 2^m)^2 ≤ 2 / (m + 1)` for all `m : ℕ`. -/
lemma central_binom_div_two_pow_sq_le (m : ℕ) :
    ((m.choose (m / 2) : ℝ) / (2 : ℝ) ^ m) ^ 2 ≤ 2 / ((m : ℝ) + 1) := by
  -- Prove simultaneously for `2 * k` and `2 * k + 1` by induction on `k`.
  have hboth : ∀ k : ℕ,
      (((2 * k).choose k : ℝ) / (2 : ℝ) ^ (2 * k)) ^ 2 ≤ 2 / ((2 * k : ℝ) + 1) ∧
      (((2 * k + 1).choose k : ℝ) / (2 : ℝ) ^ (2 * k + 1)) ^ 2 ≤ 2 / ((2 * k : ℝ) + 3) := by
    intro k
    induction k with
    | zero =>
      constructor <;> norm_num
    | succ r ihr =>
      obtain ⟨_, hodd⟩ := ihr
      -- Step 1: `C(2r + 2, r + 1) = 2 * C(2r + 1, r)`, so `a_{2r+2} = a_{2r+1}`!
      have heven_eq : ((2 * (r + 1)).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * (r + 1)) =
          ((2 * r + 1).choose r : ℝ) / (2 : ℝ) ^ (2 * r + 1) := by
        have hch : (2 * (r + 1)).choose (r + 1) = 2 * (2 * r + 1).choose r := by
          have h1 := Nat.choose_succ_succ (2 * r + 1) r
          have hsym : (2 * r + 1).choose (r + 1) = (2 * r + 1).choose r := by
            rw [← Nat.choose_symm (by omega : r + 1 ≤ 2 * r + 1)]
            congr 1; omega
          rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, h1, hsym]; omega
        rw [hch, Nat.cast_mul, show (2 : ℝ) ^ (2 * (r + 1)) = 2 * (2 : ℝ) ^ (2 * r + 1) by
          rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, pow_succ']]
        push_cast; field_simp
      have heven : (((2 * (r + 1)).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * (r + 1))) ^ 2 ≤
          2 / ((2 * (r + 1 : ℕ) : ℝ) + 1) := by
        rw [heven_eq]
        have heq : (2 * ((r + 1 : ℕ) : ℝ) + 1) = (2 * (r : ℝ) + 3) := by push_cast; ring
        rw [heq]; exact hodd
      -- Step 2: `C(2r + 3, r + 1) * (r + 2) = (2r + 3) * C(2r + 2, r + 1)`
      have hodd_eq : ((2 * (r + 1) + 1).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * (r + 1) + 1) =
          (((2 * (r + 1) : ℝ) + 1) / ((2 * (r + 1) : ℝ) + 2)) *
            (((2 * (r + 1)).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * (r + 1))) := by
        have hch : (2 * (r + 1) + 1).choose (r + 1) * (r + 2) =
            (2 * (r + 1) + 1) * (2 * (r + 1)).choose (r + 1) := by
          have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : r + 1 ≤ 2 * (r + 1) + 1)
          have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : r + 1 ≤ 2 * (r + 1))
          have hf1 : (2 * (r + 1) + 1).factorial = (2 * (r + 1) + 1) * (2 * (r + 1)).factorial :=
            Nat.factorial_succ _
          have hf2 : (2 * (r + 1) + 1 - (r + 1)).factorial =
              (r + 2) * (2 * (r + 1) - (r + 1)).factorial := by
            rw [show 2 * (r + 1) + 1 - (r + 1) = (r + 1) + 1 by omega,
              show 2 * (r + 1) - (r + 1) = r + 1 by omega]
            exact Nat.factorial_succ (r + 1)
          have hpos : 0 < (r + 1).factorial * (2 * (r + 1) - (r + 1)).factorial :=
            Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
          rw [hf1, hf2] at h1
          have hmul : (2 * (r + 1) + 1).choose (r + 1) * (r + 2) *
              ((r + 1).factorial * (2 * (r + 1) - (r + 1)).factorial) =
              (2 * (r + 1) + 1) * (2 * (r + 1)).choose (r + 1) *
              ((r + 1).factorial * (2 * (r + 1) - (r + 1)).factorial) := by
            calc (2 * (r + 1) + 1).choose (r + 1) * (r + 2) *
                  ((r + 1).factorial * (2 * (r + 1) - (r + 1)).factorial)
                = (2 * (r + 1) + 1).choose (r + 1) * (r + 1).factorial *
                  ((r + 2) * (2 * (r + 1) - (r + 1)).factorial) := by ring
              _ = (2 * (r + 1) + 1) * (2 * (r + 1)).factorial := h1
              _ = (2 * (r + 1) + 1) * ((2 * (r + 1)).choose (r + 1) * (r + 1).factorial *
                  (2 * (r + 1) - (r + 1)).factorial) := by rw [← h2]
              _ = (2 * (r + 1) + 1) * (2 * (r + 1)).choose (r + 1) *
                  ((r + 1).factorial * (2 * (r + 1) - (r + 1)).factorial) := by ring
          exact Nat.eq_of_mul_eq_mul_right hpos hmul
        have hchR : ((2 * (r + 1) + 1).choose (r + 1) : ℝ) * ((r : ℝ) + 2) =
            ((2 * (r + 1) : ℝ) + 1) * ((2 * (r + 1)).choose (r + 1) : ℝ) := by
          exact_mod_cast hch
        have hpow : (2 : ℝ) ^ (2 * (r + 1) + 1) = 2 * (2 : ℝ) ^ (2 * (r + 1)) := pow_succ' 2 _
        rw [hpow]
        have hd1 : (2 * ((r + 1 : ℕ) : ℝ) + 2) = 2 * ((r : ℝ) + 2) := by push_cast; ring
        have hp1 : (0 : ℝ) < (r : ℝ) + 2 := by positivity
        have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 * (r + 1)) := by positivity
        field_simp
        nlinarith [hchR, hd1]
      refine ⟨heven, ?_⟩
      rw [hodd_eq, mul_pow]
      have hfac_nn : 0 ≤ (((2 * (r + 1) : ℝ) + 1) / ((2 * (r + 1) : ℝ) + 2)) ^ 2 := sq_nonneg _
      calc (((2 * (r + 1) : ℝ) + 1) / ((2 * (r + 1) : ℝ) + 2)) ^ 2 *
              (((2 * (r + 1)).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * (r + 1))) ^ 2
          ≤ (((2 * (r + 1) : ℝ) + 1) / ((2 * (r + 1) : ℝ) + 2)) ^ 2 *
              (2 / ((2 * ((r + 1 : ℕ) : ℝ)) + 1)) := mul_le_mul_of_nonneg_left heven hfac_nn
        _ ≤ 2 / ((2 * ((r + 1 : ℕ) : ℝ)) + 3) := by
            have hd1 : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) + 1 := by positivity
            have hd2 : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) + 2 := by positivity
            have hd3 : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) + 3 := by positivity
            rw [div_pow]
            have heq : (2 * ((r + 1 : ℕ) : ℝ) + 1) ^ 2 / (2 * ((r + 1 : ℕ) : ℝ) + 2) ^ 2 *
                (2 / (2 * ((r + 1 : ℕ) : ℝ) + 1)) =
                2 * (2 * ((r + 1 : ℕ) : ℝ) + 1) / (2 * ((r + 1 : ℕ) : ℝ) + 2) ^ 2 := by
              field_simp
            push_cast at heq ⊢
            rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h := (hboth k).1
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv]
    simpa [show k + k = 2 * k by omega, Nat.cast_mul] using h
  · have h := (hboth k).2
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [hdiv]
    have hle : (2 : ℝ) / ((2 * k : ℝ) + 3) ≤ 2 / (((2 * k + 1 : ℕ) : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast; linarith
    exact h.trans hle

/-- Central binomial corollary: `C(m, m/2) / 2^m ≤ 2 / √(m + 1)`. -/
lemma central_binom_div_two_pow_le (m : ℕ) :
    (m.choose (m / 2) : ℝ) / (2 : ℝ) ^ m ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
  have hsq := central_binom_div_two_pow_sq_le m
  have h1 : (m.choose (m / 2) : ℝ) / (2 : ℝ) ^ m ≤ Real.sqrt (2 / ((m : ℝ) + 1)) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (m.choose (m / 2) : ℝ) / (2 : ℝ) ^ m)]
    exact Real.sqrt_le_sqrt hsq
  have h2 : Real.sqrt (2 / ((m : ℝ) + 1)) ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
    rw [Real.sqrt_div (by norm_num)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by norm_num
    linarith
  exact h1.trans h2

/-- Sperner's theorem on `Fin m` proved via the LYM permutation counting argument. -/
lemma sperner_fin (m : ℕ) (𝒜 : Finset (Finset (Fin m)))
    (hanti : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ⊆ B → A = B) :
    𝒜.card ≤ m.choose (m / 2) := by
  classical
  -- For each `A ∈ 𝒜`, let `P_A` be permutations sending `{i | i.val < A.card}` into `A`.
  let P (A : Finset (Fin m)) : Finset (Equiv.Perm (Fin m)) :=
    Finset.univ.filter fun σ => ∀ i : Fin m, i.val < A.card → σ i ∈ A
  have hdisj : (𝒜 : Set (Finset (Fin m))).PairwiseDisjoint P := by
    intro A hA B hB hAB
    change Disjoint (P A) (P B)
    rw [Finset.disjoint_left]
    intro σ hσA hσB
    have hA' := (Finset.mem_filter.mp hσA).2
    have hB' := (Finset.mem_filter.mp hσB).2
    -- Show the image of `{i | i.val < A.card}` under `σ` is ALL of `A` (by cardinality!).
    let init (k : ℕ) : Finset (Fin m) := Finset.univ.filter fun i : Fin m => i.val < k
    have hcard_init : ∀ k ≤ m, (init k).card = k := by
      intro k hkm
      have heq : init k = (Finset.range k).attach.image (fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hkm⟩) := by
        ext i; simp only [init, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · intro hi; exact ⟨i.1, Finset.mem_range.mpr hi, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact Finset.mem_range.mp hx
      rw [heq, Finset.card_image_of_injective]
      · simp
      · intro x y h; ext; exact congrArg Fin.val h
    have hA_eq : (init A.card).image σ = A := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hA' i (Finset.mem_filter.mp hi).2
      · rw [Finset.card_image_of_injective _ σ.injective, hcard_init A.card (by simpa using Finset.card_le_univ A)]
    have hB_eq : (init B.card).image σ = B := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hB' i (Finset.mem_filter.mp hi).2
      · rw [Finset.card_image_of_injective _ σ.injective, hcard_init B.card (by simpa using Finset.card_le_univ B)]
    rcases le_total A.card B.card with hle | hle
    · have hsub : A ⊆ B := by
        rw [← hA_eq, ← hB_eq]
        refine Finset.image_subset_image fun i hi => ?_
        simp only [init, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; omega
      exact hAB (hanti A hA B hB hsub)
    · have hsub : B ⊆ A := by
        rw [← hA_eq, ← hB_eq]
        refine Finset.image_subset_image fun i hi => ?_
        simp only [init, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; omega
      exact hAB (hanti B hB A hA hsub).symm
  -- Count `|(P A)| = A.card ! * (m - A.card)!`.
  have hcardP : ∀ A : Finset (Fin m), (P A).card = A.card.factorial * (m - A.card).factorial := by
    intro A
    let initA : Finset (Fin m) := Finset.univ.filter fun i : Fin m => i.val < A.card
    have hcard_initA : initA.card = A.card := by
      have hAm : A.card ≤ m := by simpa using Finset.card_le_univ A
      have heq : initA = (Finset.range A.card).attach.image
          (fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hAm⟩) := by
        ext i; simp only [initA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_attach, true_and, Subtype.exists]
        constructor
        · intro hi; exact ⟨i.1, Finset.mem_range.mpr hi, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact Finset.mem_range.mp hx
      rw [heq, Finset.card_image_of_injective]
      · simp
      · intro x y h; ext; exact congrArg Fin.val h
    have hcard_complA : initAᶜ.card = Aᶜ.card := by
      rw [Finset.card_compl, Finset.card_compl, hcard_initA]
    -- Fix one reference bijection `e₁ : initA ≃ A` and `e₂ : initAᶜ ≃ Aᶜ`.
    let e₁ : initA ≃ A := Fintype.equivOfCardEq (by simp [hcard_initA])
    let e₂ : (initAᶜ : Finset (Fin m)) ≃ (Aᶜ : Finset (Fin m)) :=
      Fintype.equivOfCardEq (by simp [hcard_initA])
    -- Bijection `Equiv.Perm initA × Equiv.Perm initAᶜ ≃ P A`!
    have hbij : Fintype.card (P A) =
        Fintype.card (Equiv.Perm initA × Equiv.Perm (initAᶜ : Finset (Fin m))) := by
      refine Fintype.card_congr ?_
      refine
        { toFun := fun σ =>
            let f1 : Equiv.Perm initA :=
              { toFun := fun x => e₁.symm ⟨σ.1 x.1, (Finset.mem_filter.mp σ.2).2 x.1 (Finset.mem_filter.mp x.2).2⟩
                invFun := fun x =>
                  ⟨σ.1.symm (e₁ x).1, by
                    rw [Finset.mem_filter]
                    refine ⟨Finset.mem_univ _, ?_⟩
                    by_contra hge
                    have hsub : initA.image σ.1 ⊆ A := by
                      intro y hy
                      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
                      exact (Finset.mem_filter.mp σ.2).2 z (Finset.mem_filter.mp hz).2
                    have heqA : initA.image σ.1 = A :=
                      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ σ.1.injective, hcard_initA])
                    have hmemA : (e₁ x).1 ∈ initA.image σ.1 := by rw [heqA]; exact (e₁ x).2
                    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hmemA
                    have hzs : σ.1.symm (e₁ x).1 = z := by
                      rw [← hzeq, Equiv.symm_apply_apply]
                    rw [hzs] at hge
                    exact hge (Finset.mem_filter.mp hz).2⟩
                left_inv := fun x => by ext; simp
                right_inv := fun x => by ext; simp }
            let f2 : Equiv.Perm (initAᶜ : Finset (Fin m)) :=
              { toFun := fun x => e₂.symm ⟨σ.1 x.1, by
                  rw [Finset.mem_compl]
                  intro hmemA
                  have hsub : initA.image σ.1 ⊆ A := by
                    intro y hy
                    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
                    exact (Finset.mem_filter.mp σ.2).2 z (Finset.mem_filter.mp hz).2
                  have heqA : initA.image σ.1 = A :=
                    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ σ.1.injective, hcard_initA])
                  have hmemA' : σ.1 x.1 ∈ initA.image σ.1 := by rw [heqA]; exact hmemA
                  obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hmemA'
                  have hzx : z = x.1 := σ.1.injective hzeq
                  exact (Finset.mem_compl.mp x.2) (hzx ▸ hz)⟩
                invFun := fun x => ⟨σ.1.symm (e₂ x).1, by
                  rw [Finset.mem_compl]
                  intro hin
                  have hmemA := (Finset.mem_filter.mp σ.2).2 _ (Finset.mem_filter.mp hin).2
                  rw [Equiv.apply_symm_apply] at hmemA
                  exact (Finset.mem_compl.mp (e₂ x).2) hmemA⟩
                left_inv := fun x => by ext; simp
                right_inv := fun x => by ext; simp }
            (f1, f2)
          invFun := fun pq =>
            ⟨{ toFun := fun i => if hi : i ∈ initA then (e₁ (pq.1 ⟨i, hi⟩)).1
                  else (e₂ (pq.2 ⟨i, Finset.mem_compl.mpr hi⟩)).1
               invFun := fun j => if hj : j ∈ A then (pq.1.symm (e₁.symm ⟨j, hj⟩)).1
                  else (pq.2.symm (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩)).1
               left_inv := fun i => by
                 by_cases hi : i ∈ initA
                 · simp only [hi, ↓reduceDIte]
                   have hmem : (e₁ (pq.1 ⟨i, hi⟩)).1 ∈ A := (e₁ _).2
                   simp [hmem]
                 · simp only [hi, ↓reduceDIte]
                   have hnot : (e₂ (pq.2 ⟨i, Finset.mem_compl.mpr hi⟩)).1 ∉ A :=
                     Finset.mem_compl.mp (e₂ _).2
                   simp [hnot]
               right_inv := fun j => by
                 by_cases hj : j ∈ A
                 · simp only [hj, ↓reduceDIte]
                   have hmem : (pq.1.symm (e₁.symm ⟨j, hj⟩)).1 ∈ initA := (pq.1.symm _).2
                   simp [hmem]
                 · simp only [hj, ↓reduceDIte]
                   have hnot : (pq.2.symm (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩)).1 ∉ initA :=
                     Finset.mem_compl.mp (pq.2.symm _).2
                   simp [hnot] },
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by
               have hin : i ∈ initA := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
               simp only [Equiv.coe_fn_mk, hin, ↓reduceDIte]
               exact (e₁ _).2⟩⟩
          left_inv := fun σ => by
            ext i; simp only [Equiv.coe_fn_mk]
            by_cases hi : i ∈ initA <;> simp [hi]
          right_inv := fun pq => by
            ext x
            · simp
            · have hx : x.1 ∉ initA := Finset.mem_compl.mp x.2
              simp [hx] }
    rw [← Fintype.card_coe, hbij, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_coe, Fintype.card_coe, hcard_initA, hcard_complA, Finset.card_compl,
      Fintype.card_fin]
  -- Sum cardinalities of disjoint `P A` inside `Equiv.Perm (Fin m)`.
  have hsum_le : ∑ A ∈ 𝒜, A.card.factorial * (m - A.card).factorial ≤ m.factorial := by
    calc ∑ A ∈ 𝒜, A.card.factorial * (m - A.card).factorial
        = ∑ A ∈ 𝒜, (P A).card := Finset.sum_congr rfl fun A _ => (hcardP A).symm
      _ = (𝒜.biUnion P).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin m))).card := Finset.card_le_univ _
      _ = m.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- Each term `k! * (m - k)! = m! / C(m, k) ≥ m! / C(m, m/2)`.
  have hterm_ge : ∀ A ∈ 𝒜, m.factorial ≤ m.choose (m / 2) * (A.card.factorial * (m - A.card).factorial) := by
    intro A _
    have hAm : A.card ≤ m := by simpa using Finset.card_le_univ A
    have hmul : m.choose A.card * (A.card.factorial * (m - A.card).factorial) = m.factorial := by
      have h1 := Nat.choose_mul_factorial_mul_factorial hAm
      linarith
    calc m.factorial
        = m.choose A.card * (A.card.factorial * (m - A.card).factorial) := hmul.symm
      _ ≤ m.choose (m / 2) * (A.card.factorial * (m - A.card).factorial) :=
          Nat.mul_le_mul_right _ (Nat.choose_le_middle A.card m)
  have htot : 𝒜.card * m.factorial ≤ m.choose (m / 2) * m.factorial := by
    calc 𝒜.card * m.factorial
        = ∑ _A ∈ 𝒜, m.factorial := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ A ∈ 𝒜, m.choose (m / 2) * (A.card.factorial * (m - A.card).factorial) :=
          Finset.sum_le_sum hterm_ge
      _ = m.choose (m / 2) * ∑ A ∈ 𝒜, A.card.factorial * (m - A.card).factorial :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ m.choose (m / 2) * m.factorial := Nat.mul_le_mul_left _ hsum_le
  exact Nat.le_of_mul_le_mul_right htot (Nat.factorial_pos m)

/-- Sperner's theorem for any `Finset α` `I`. -/
lemma sperner_finset {α : Type*} [DecidableEq α] (I : Finset α)
    (𝒜 : Finset (Finset α)) (hsub : ∀ A ∈ 𝒜, A ⊆ I)
    (hanti : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ⊆ B → A = B) :
    𝒜.card ≤ I.card.choose (I.card / 2) := by
  classical
  let e : I ≃ Fin I.card := I.equivFin
  let mapSet (A : Finset α) : Finset (Fin I.card) :=
    (I.attach.filter fun x => x.1 ∈ A).image e
  have hinj : Set.InjOn mapSet (𝒜 : Set (Finset α)) := by
    intro A hA B hB heq
    ext x
    constructor
    · intro hxA
      have hxI : x ∈ I := hsub A hA hxA
      have hmem : e ⟨x, hxI⟩ ∈ mapSet B := by
        rw [← heq]
        exact Finset.mem_image.mpr ⟨⟨x, hxI⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hxA⟩, rfl⟩
      obtain ⟨y, hy, hyEq⟩ := Finset.mem_image.mp hmem
      have hyx : y = ⟨x, hxI⟩ := e.injective hyEq
      have h1 := (Finset.mem_filter.mp hy).2
      rw [hyx] at h1; exact h1
    · intro hxB
      have hxI : x ∈ I := hsub B hB hxB
      have hmem : e ⟨x, hxI⟩ ∈ mapSet A := by
        rw [heq]
        exact Finset.mem_image.mpr ⟨⟨x, hxI⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hxB⟩, rfl⟩
      obtain ⟨y, hy, hyEq⟩ := Finset.mem_image.mp hmem
      have hyx : y = ⟨x, hxI⟩ := e.injective hyEq
      have h1 := (Finset.mem_filter.mp hy).2
      rw [hyx] at h1; exact h1
  have hanti' : ∀ A' ∈ 𝒜.image mapSet, ∀ B' ∈ 𝒜.image mapSet, A' ⊆ B' → A' = B' := by
    intro A' hA' B' hB' hAB'
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hA'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    have hAB : A ⊆ B := by
      intro x hxA
      have hxI : x ∈ I := hsub A hA hxA
      have hmem : e ⟨x, hxI⟩ ∈ mapSet B := hAB'
        (Finset.mem_image.mpr ⟨⟨x, hxI⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hxA⟩, rfl⟩)
      obtain ⟨y, hy, hyEq⟩ := Finset.mem_image.mp hmem
      have hyx : y = ⟨x, hxI⟩ := e.injective hyEq
      have h1 := (Finset.mem_filter.mp hy).2
      rw [hyx] at h1; exact h1
    rw [hanti A hA B hB hAB]
  rw [← Finset.card_image_of_injOn hinj]
  exact sperner_fin I.card (𝒜.image mapSet) hanti'

/- ## Section 3: Weighted antichain bound via active/frozen decomposition + Chebyshev -/

/-- Product Bernoulli(`1/(p+1)`) probability weight on `B.powerset`. -/
noncomputable def muBlock (B S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 : ℝ) / ((p : ℝ) + 1)) * (∏ p ∈ B \ S, (p : ℝ) / ((p : ℝ) + 1))

lemma muBlock_nonneg (B S : Finset ℕ) : 0 ≤ muBlock B S := by
  unfold muBlock
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Finset.prod_nonneg fun _ _ => by positivity)

lemma sum_muBlock_eq_one (B : Finset ℕ) :
    ∑ S ∈ B.powerset, muBlock B S = 1 := by
  unfold muBlock
  have h := Finset.prod_add (fun p : ℕ => (1 : ℝ) / ((p : ℝ) + 1))
    (fun p : ℕ => (p : ℝ) / ((p : ℝ) + 1)) B
  have h1 : ∏ p ∈ B, ((1 : ℝ) / ((p : ℝ) + 1) + (p : ℝ) / ((p : ℝ) + 1)) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    field_simp; ring
  exact h.symm.trans h1

/-- If `B` consists of primes with `1/2 ≤ ∑_{p ∈ B} 1/(p + 1) ≤ 1`, then
`1/9 ≤ muBlock B ∅` and `1/9 ≤ 1 - muBlock B ∅`. -/
lemma muBlock_empty_bounds {B : Finset ℕ} (hBprime : ∀ p ∈ B, p.Prime)
    (hlo : (1 / 2 : ℝ) ≤ ∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1))
    (hhi : ∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1) ≤ 1) :
    (1 / 9 : ℝ) ≤ muBlock B ∅ ∧ (1 / 9 : ℝ) ≤ 1 - muBlock B ∅ := by
  have hval : muBlock B ∅ = ∏ p ∈ B, (1 - (1 : ℝ) / ((p : ℝ) + 1)) := by
    unfold muBlock
    simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
    refine Finset.prod_congr rfl fun p _ => ?_
    have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    field_simp; ring
  rw [hval]
  constructor
  · -- Lower bound: `1 - x ≥ exp(-2x)` for `0 ≤ x ≤ 1/3`, so product `≥ exp(-2) ≥ 1/9`.
    have hexp_le : Real.exp (-2 * ∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1)) ≤
        ∏ p ∈ B, (1 - (1 : ℝ) / ((p : ℝ) + 1)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hBprime p hp).two_le
      have hpos : (0 : ℝ) < 1 - (1 : ℝ) / ((p : ℝ) + 1) := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      rw [show -2 * ((1 : ℝ) / ((p : ℝ) + 1)) = -(2 / ((p : ℝ) + 1)) by ring, Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) hpos]
      have h1 : (1 - (1 : ℝ) / ((p : ℝ) + 1))⁻¹ ≤ 1 + 2 / ((p : ℝ) + 1) := by
        rw [inv_le_iff_one_le_mul₀' hpos]
        have hcalc : (1 - (1 : ℝ) / ((p : ℝ) + 1)) * (1 + 2 / ((p : ℝ) + 1)) - 1 =
            ((p : ℝ) - 1) / ((p : ℝ) + 1) ^ 2 := by
          field_simp; ring
        have hnn : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) ^ 2 :=
          div_nonneg (by linarith) (by positivity)
        linarith
      exact h1.trans (by simpa [add_comm] using Real.add_one_le_exp (2 / ((p : ℝ) + 1)))
    have h19 : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.exp_neg, one_div]
      rw [inv_le_inv₀ (by norm_num) (Real.exp_pos _)]
      have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      calc Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
        _ = 9 := by norm_num
    exact h19.trans ((Real.exp_le_exp.mpr (by linarith)).trans hexp_le)
  · -- Upper bound on product: `1 - x ≤ exp(-x)`, so product `≤ exp(-1/2) ≤ 2/3 ≤ 8/9`.
    have hprod_le : ∏ p ∈ B, (1 - (1 : ℝ) / ((p : ℝ) + 1)) ≤
        Real.exp (-(∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1))) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hBprime p hp).two_le
        have : (1 : ℝ) / ((p : ℝ) + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      · have h := Real.add_one_le_exp (-((1 : ℝ) / ((p : ℝ) + 1)))
        linarith
    have h23 : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h := Real.add_one_le_exp (1 / 2 : ℝ)
      linarith
    have hexp_le : Real.exp (-(∑ p ∈ B, (1 : ℝ) / ((p : ℝ) + 1))) ≤ Real.exp (-(1 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith

lemma muBlock_biUnion {K : ℕ} {P : Fin K → Finset ℕ}
    (hPdisj : ∀ i j : Fin K, i ≠ j → Disjoint (P i) (P j))
    (S : Finset ℕ) (hS : S ⊆ Finset.univ.biUnion P) :
    muBlock (Finset.univ.biUnion P) S = ∏ j : Fin K, muBlock (P j) (S ∩ P j) := by
  unfold muBlock
  rw [Finset.prod_mul_distrib]
  congr 1
  · have hS_eq : S = Finset.univ.biUnion (fun j : Fin K => S ∩ P j) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · intro hp
        obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp (hS hp)
        exact ⟨j, hp, hpj⟩
      · rintro ⟨_, hp, _⟩; exact hp
    have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint (fun j => S ∩ P j) := by
      intro i _ j _ hij
      exact (hPdisj i j hij).mono Finset.inter_subset_right Finset.inter_subset_right
    conv_lhs => rw [hS_eq]
    exact Finset.prod_biUnion hd
  · have hD_eq : Finset.univ.biUnion P \ S = Finset.univ.biUnion (fun j : Fin K => P j \ (S ∩ P j)) := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
      constructor
      · rintro ⟨⟨j, hpj⟩, hpS⟩
        exact ⟨j, hpj, fun h => hpS h.1⟩
      · rintro ⟨j, hpj, hnot⟩
        exact ⟨⟨j, hpj⟩, fun hpS => hnot ⟨hpS, hpj⟩⟩
    have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint (fun j => P j \ (S ∩ P j)) := by
      intro i _ j _ hij
      exact (hPdisj i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
    conv_lhs => rw [hD_eq]
    exact Finset.prod_biUnion hd

/-- Chebyshev variance bound for a product distribution on `Fin K → Fin 3` where state `0` has
probability `2 / 9` independently at each coordinate. -/
lemma chebyshev_active_count {K : ℕ} (hK : 1 ≤ K) (w : Fin K → Fin 3 → ℝ)
    (hw_nn : ∀ j s, 0 ≤ w j s)
    (hw_sum : ∀ j, ∑ s : Fin 3, w j s = 1)
    (hw0 : ∀ j, w j 0 = 2 / 9) :
    ∑ σ : Fin K → Fin 3,
      (if ((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) < (K : ℝ) / 9
       then ∏ j : Fin K, w j (σ j) else 0) ≤
    81 / (K : ℝ) := by
  classical
  let X (j : Fin K) (s : Fin 3) : ℝ := (if s = 0 then (1 : ℝ) else 0) - 2 / 9
  have hmean : ∀ j : Fin K, ∑ s : Fin 3, w j s * X j s = 0 := by
    intro j
    rw [Fin.sum_univ_three]
    have hsum := hw_sum j
    rw [Fin.sum_univ_three] at hsum
    have h0 := hw0 j
    dsimp only [X]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, show (2 : Fin 3) ≠ 0 by decide]
    linarith
  have hvar : ∀ j : Fin K, ∑ s : Fin 3, w j s * (X j s) ^ 2 ≤ 1 := by
    intro j
    calc ∑ s : Fin 3, w j s * (X j s) ^ 2
        ≤ ∑ s : Fin 3, w j s * 1 := by
          refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hw_nn j s)
          dsimp only [X]; split_ifs <;> norm_num
      _ = 1 := by simp [hw_sum j]
  -- Compute `∑ σ, (∏ j, w j (σ j)) * (∑ j, X j (σ j))^2 ≤ K`.
  have hEsq : ∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) * (∑ j : Fin K, X j (σ j)) ^ 2 ≤ (K : ℝ) := by
    have hexp : ∀ σ : Fin K → Fin 3,
        (∏ j : Fin K, w j (σ j)) * (∑ j : Fin K, X j (σ j)) ^ 2 =
        ∑ i : Fin K, ∑ j : Fin K, (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X j (σ j)) := by
      intro σ
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hswap :
        (∑ i : Fin K, ∑ σ : Fin K → Fin 3, ∑ j : Fin K,
          (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X j (σ j))) =
        ∑ i : Fin K, ∑ j : Fin K, ∑ σ : Fin K → Fin 3,
          (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X j (σ j)) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap]
    have hpair : ∀ i j : Fin K,
        (∑ σ : Fin K → Fin 3, (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X j (σ j))) =
        if i = j then ∑ s : Fin 3, w i s * (X i s) ^ 2 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have hfac : ∀ σ : Fin K → Fin 3,
            (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X i (σ i)) =
            ∏ r : Fin K, (if r = i then w r (σ r) * (X r (σ r)) ^ 2 else w r (σ r)) := by
          intro σ
          conv_lhs => rw [← Finset.mul_prod_erase Finset.univ (fun r => w r (σ r)) (Finset.mem_univ i)]
          conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
          have hrest :
              ∏ r ∈ Finset.univ.erase i, (if r = i then w r (σ r) * (X r (σ r)) ^ 2 else w r (σ r)) =
              ∏ r ∈ Finset.univ.erase i, w r (σ r) :=
            Finset.prod_congr rfl fun r hr => if_neg (Finset.mem_erase.mp hr).1
          rw [if_pos rfl, hrest]; ring
        simp_rw [hfac]
        rw [← Fintype.prod_sum (fun r s => if r = i then w r s * (X r s) ^ 2 else w r s)]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        have hrest : ∏ r ∈ Finset.univ.erase i,
            (∑ s : Fin 3, if r = i then w r s * (X r s) ^ 2 else w r s) = 1 :=
          Finset.prod_eq_one fun r hr => by
            simp only [if_neg (Finset.mem_erase.mp hr).1, hw_sum r]
        rw [hrest, mul_one]
        simp
      · rw [if_neg hij]
        have hfac : ∀ σ : Fin K → Fin 3,
            (∏ r : Fin K, w r (σ r)) * (X i (σ i) * X j (σ j)) =
            ∏ r : Fin K, (if r = i then w r (σ r) * X r (σ r)
              else if r = j then w r (σ r) * X r (σ r) else w r (σ r)) := by
          intro σ
          have hj_er : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
          conv_lhs =>
            rw [← Finset.mul_prod_erase Finset.univ (fun r => w r (σ r)) (Finset.mem_univ i),
              ← Finset.mul_prod_erase (Finset.univ.erase i) (fun r => w r (σ r)) hj_er]
          conv_rhs =>
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
              ← Finset.mul_prod_erase (Finset.univ.erase i) _ hj_er]
          have hrest :
              ∏ r ∈ (Finset.univ.erase i).erase j,
                (if r = i then w r (σ r) * X r (σ r)
                 else if r = j then w r (σ r) * X r (σ r) else w r (σ r)) =
              ∏ r ∈ (Finset.univ.erase i).erase j, w r (σ r) :=
            Finset.prod_congr rfl fun r hr => by
              have h1 := (Finset.mem_erase.mp hr).1
              have h2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
              rw [if_neg h2, if_neg h1]
          rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl, hrest]; ring
        simp_rw [hfac]
        rw [← Fintype.prod_sum (fun r s =>
          if r = i then w r s * X r s else if r = j then w r s * X r s else w r s)]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp only [↓reduceIte, hmean i]
    simp_rw [hpair]
    have hdiag : ∑ i : Fin K, ∑ j : Fin K, (if i = j then ∑ s : Fin 3, w i s * (X i s) ^ 2 else 0) =
        ∑ i : Fin K, ∑ s : Fin 3, w i s * (X i s) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    rw [hdiag]
    calc ∑ i : Fin K, ∑ s : Fin 3, w i s * (X i s) ^ 2
        ≤ ∑ _i : Fin K, (1 : ℝ) := Finset.sum_le_sum fun i _ => hvar i
      _ = (K : ℝ) := by simp
  -- Markov's inequality: if `card < K / 9`, then `(∑ X)^2 = (card - 2K/9)^2 ≥ (K/9)^2`.
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hmarkov :
      ((K : ℝ) / 9) ^ 2 *
        ∑ σ : Fin K → Fin 3,
          (if ((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) < (K : ℝ) / 9
           then ∏ j : Fin K, w j (σ j) else 0) ≤
      ∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) * (∑ j : Fin K, X j (σ j)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    have hprod_nn : 0 ≤ ∏ j : Fin K, w j (σ j) := Finset.prod_nonneg fun j _ => hw_nn j (σ j)
    split_ifs with hlt
    · have hsumX : ∑ j : Fin K, X j (σ j) =
          ((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) - 2 / 9 * (K : ℝ) := by
        dsimp only [X]
        rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]; ring
      rw [hsumX]
      have hsq : ((K : ℝ) / 9) ^ 2 ≤
          (((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) - 2 / 9 * (K : ℝ)) ^ 2 := by
        nlinarith
      nlinarith
    · rw [mul_zero]
      exact mul_nonneg hprod_nn (sq_nonneg _)
  have htot := hmarkov.trans hEsq
  have hpos2 : (0 : ℝ) < ((K : ℝ) / 9) ^ 2 := by positivity
  rw [le_div_iff₀ hKpos]
  nlinarith

/-- Main weighted antichain bound on `P_all.powerset`:
`∑_{R ∈ 𝒜} muBlock P_all R ≤ 81 / K + 6 / √K`. -/
lemma weighted_antichain_bound {K : ℕ} (hK : 1 ≤ K) (P : Fin K → Finset ℕ)
    (hPprime : ∀ j : Fin K, ∀ p ∈ P j, p.Prime)
    (hPdisj : ∀ i j : Fin K, i ≠ j → Disjoint (P i) (P j))
    (hPsum : ∀ j : Fin K, (1 / 2 : ℝ) ≤ ∑ p ∈ P j, (1 : ℝ) / ((p : ℝ) + 1) ∧
      ∑ p ∈ P j, (1 : ℝ) / ((p : ℝ) + 1) ≤ 1)
    (𝒜 : Finset (Finset ℕ)) (hsub : ∀ R ∈ 𝒜, R ⊆ Finset.univ.biUnion P)
    (hanti : ∀ R₁ ∈ 𝒜, ∀ R₂ ∈ 𝒜, R₁ ⊆ R₂ → R₁ = R₂) :
    ∑ R ∈ 𝒜, muBlock (Finset.univ.biUnion P) R ≤ 81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ) := by
  classical
  let P_all := Finset.univ.biUnion P
  let theta (j : Fin K) : ℝ := 1 - muBlock (P j) ∅
  have hth_bds : ∀ j : Fin K, (1 / 9 : ℝ) ≤ muBlock (P j) ∅ ∧ (1 / 9 : ℝ) ≤ theta j := fun j =>
    muBlock_empty_bounds (hPprime j) (hPsum j).1 (hPsum j).2
  have hth_pos : ∀ j : Fin K, 0 < theta j := fun j => by linarith [(hth_bds j).2]
  -- Nonempty subsets of `P j`
  let NE (j : Fin K) : Finset (Finset ℕ) := (P j).powerset.erase ∅
  let nu (j : Fin K) (T : NE j) : ℝ := muBlock (P j) T.1 / theta j
  have hnu_nn : ∀ j (T : NE j), 0 ≤ nu j T := fun j T =>
    div_nonneg (muBlock_nonneg _ _) (hth_pos j).le
  have hnu_sum : ∀ j : Fin K, ∑ T : NE j, nu j T = 1 := by
    intro j
    dsimp only [nu]
    rw [← Finset.sum_div, Finset.univ_eq_attach]
    have hsumNE : ∑ T ∈ (NE j).attach, muBlock (P j) T.1 = theta j := by
      rw [Finset.sum_attach (NE j) (fun T => muBlock (P j) T)]
      have h1 := sum_muBlock_eq_one (P j)
      have hmem : (∅ : Finset ℕ) ∈ (P j).powerset := Finset.empty_mem_powerset _
      have hadd := Finset.add_sum_erase (P j).powerset (fun S => muBlock (P j) S) hmem
      dsimp only [NE, theta]
      linarith
    rw [hsumNE, div_self (hth_pos j).ne']
  -- Three-state weights: `0` = active fair coin (`2/9`), `1` = frozen `∅`, `2` = frozen `T`
  let w (j : Fin K) (s : Fin 3) : ℝ :=
    if s = 0 then 2 / 9 else if s = 1 then (1 - theta j) - 1 / 9 else theta j - 1 / 9
  have hw_nn : ∀ j s, 0 ≤ w j s := by
    intro j s
    fin_cases s
    · dsimp [w]; norm_num
    · dsimp [w]; have := (hth_bds j).1; dsimp [theta]; linarith
    · dsimp [w]; have := (hth_bds j).2; linarith
  have hw_sum : ∀ j, ∑ s : Fin 3, w j s = 1 := by
    intro j; rw [Fin.sum_univ_three]; dsimp [w]; ring
  have hw0 : ∀ j, w j 0 = 2 / 9 := fun _ => by simp [w]
  -- Combine `(T, σ, b)` into a subset of `P_all`.
  let pick (j : Fin K) (t : NE j) (s : Fin 3) (b : Bool) : Finset ℕ :=
    if s = 2 ∨ (s = 0 ∧ b = true) then t.1 else ∅
  let combine (T : ∀ j : Fin K, NE j) (σ : Fin K → Fin 3) (b : Fin K → Bool) : Finset ℕ :=
    Finset.univ.biUnion fun j : Fin K => pick j (T j) (σ j) (b j)
  -- Coordinatewise exact decomposition: for any `S ∈ P_all.powerset`,
  -- `muBlock P_all S = ∑ T, ∑ σ, ∑ b, (∏ nu) * (∏ w) * (1/2)^K * 1_{combine T σ b = S}`.
  have hdecomp : ∀ R ∈ P_all.powerset,
      muBlock P_all R =
      ∑ T : (∀ j : Fin K, NE j), ∑ σ : Fin K → Fin 3, ∑ b : Fin K → Bool,
        (∏ j : Fin K, nu j (T j)) * (∏ j : Fin K, w j (σ j)) * ((1 / 2 : ℝ) ^ K) *
          (if combine T σ b = R then 1 else 0) := by
    intro R hR
    have hRsub : R ⊆ P_all := Finset.mem_powerset.mp hR
    rw [muBlock_biUnion hPdisj R hRsub]
    -- Show each coordinate `j` matches!
    have hcoord : ∀ j : Fin K,
        muBlock (P j) (R ∩ P j) =
        ∑ t : NE j, ∑ s : Fin 3, ∑ b : Bool,
          nu j t * w j s * (1 / 2 : ℝ) * (if pick j t s b = R ∩ P j then 1 else 0) := by
      intro j
      by_cases hemp : R ∩ P j = ∅
      · rw [hemp]
        have hinner : ∀ t : NE j,
            (∑ s : Fin 3, ∑ b : Bool,
              nu j t * w j s * (1 / 2 : ℝ) * (if pick j t s b = ∅ then 1 else 0)) =
            nu j t * muBlock (P j) ∅ := by
          intro t
          have htne : t.1 ≠ ∅ := (Finset.mem_erase.mp t.2).1
          rw [Fin.sum_univ_three]
          simp only [Fintype.sum_bool, pick, w, theta, htne, Fin.isValue, ↓reduceIte,
            one_ne_zero, show (2 : Fin 3) ≠ 0 by decide, show (0 : Fin 3) ≠ 2 by decide,
            show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide,
            Bool.false_eq_true, and_false, and_true, or_false, or_true]
          ring
        simp_rw [hinner, ← Finset.sum_mul, hnu_sum j, one_mul]
      · have hmemNE : R ∩ P j ∈ NE j :=
          Finset.mem_erase.mpr ⟨hemp, Finset.mem_powerset.mpr Finset.inter_subset_right⟩
        let t₀ : NE j := ⟨R ∩ P j, hmemNE⟩
        rw [Finset.sum_eq_single t₀]
        · rw [Fin.sum_univ_three]
          simp only [Fintype.sum_bool, pick, t₀, nu, w, Fin.isValue, ↓reduceIte,
            one_ne_zero, show (2 : Fin 3) ≠ 0 by decide, show (0 : Fin 3) ≠ 2 by decide,
            show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide,
            Bool.false_eq_true, and_false, and_true, or_false, or_true, Ne.symm hemp]
          have hthne : theta j ≠ 0 := (hth_pos j).ne'
          field_simp; ring
        · intro t _ htne
          refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun b _ => ?_
          have hneq : pick j t s b ≠ R ∩ P j := by
            dsimp only [pick]
            split_ifs
            · intro heq; exact htne (Subtype.ext heq)
            · exact Ne.symm hemp
          simp [hneq]
        · intro habs; exact (habs (Finset.mem_univ _)).elim
    simp_rw [hcoord]
    -- Collapse the product of triple sums via `Fintype.prod_sum` on `Σ` / `Prod`!
    have hprod_eq :
        (∏ j : Fin K, ∑ p : NE j × Fin 3 × Bool,
          nu j p.1 * w j p.2.1 * (1 / 2 : ℝ) * (if pick j p.1 p.2.1 p.2.2 = R ∩ P j then 1 else 0)) =
        ∑ T : (∀ j : Fin K, NE j), ∑ σ : Fin K → Fin 3, ∑ b : Fin K → Bool,
          (∏ j : Fin K, nu j (T j)) * (∏ j : Fin K, w j (σ j)) * ((1 / 2 : ℝ) ^ K) *
            (if combine T σ b = R then 1 else 0) := by
      rw [Fintype.prod_sum]
      -- Equivalence `(∀ j, NE j × Fin 3 × Bool) ≃ ((∀ j, NE j) × (Fin K → Fin 3)) × (Fin K → Bool)`
      let e : (∀ j : Fin K, NE j × Fin 3 × Bool) ≃
          ((∀ j : Fin K, NE j) × (Fin K → Fin 3)) × (Fin K → Bool) :=
        { toFun := fun f => ((fun j => (f j).1, fun j => (f j).2.1), fun j => (f j).2.2)
          invFun := fun g j => (g.1.1 j, g.1.2 j, g.2 j)
          left_inv := fun f => by ext j <;> rfl
          right_inv := fun g => by rfl }
      trans ∑ g : ((∀ j : Fin K, NE j) × (Fin K → Fin 3)) × (Fin K → Bool),
          (∏ j : Fin K, nu j (g.1.1 j)) * (∏ j : Fin K, w j (g.1.2 j)) * ((1 / 2 : ℝ) ^ K) *
            (if combine g.1.1 g.1.2 g.2 = R then 1 else 0)
      · refine Fintype.sum_equiv e _ _ fun f => ?_
        simp only [e, Equiv.coe_fn_mk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        congr 1
        -- Compare `∏ j, if pick j ... = R ∩ P j then 1 else 0` with `if combine ... = R then 1 else 0`.
        have hiff : combine (fun j => (f j).1) (fun j => (f j).2.1) (fun j => (f j).2.2) = R ↔
            ∀ j : Fin K, pick j (f j).1 (f j).2.1 (f j).2.2 = R ∩ P j := by
          constructor
          · intro heq j
            ext p
            simp only [Finset.mem_inter]
            constructor
            · intro hp
              have hpP : p ∈ P j := by
                dsimp only [pick] at hp
                split_ifs at hp
                · exact Finset.mem_powerset.mp (Finset.mem_erase.mp (f j).1.2).2 hp
                · simp at hp
              refine ⟨?_, hpP⟩
              rw [← heq]
              exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩
            · rintro ⟨hpR, hpP⟩
              rw [← heq] at hpR
              obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hpR
              have hpPi : p ∈ P i := by
                dsimp only [pick] at hpi
                split_ifs at hpi
                · exact Finset.mem_powerset.mp (Finset.mem_erase.mp (f i).1.2).2 hpi
                · simp at hpi
              have hij : i = j := by
                by_contra hne
                exact Finset.disjoint_left.mp (hPdisj i j hne) hpPi hpP
              exact hij ▸ hpi
          · intro hall
            ext p
            simp only [combine, Finset.mem_biUnion, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, hpj⟩
              rw [hall j] at hpj
              exact (Finset.mem_inter.mp hpj).1
            · intro hpR
              obtain ⟨j, _, hpP⟩ := Finset.mem_biUnion.mp (hRsub hpR)
              exact ⟨j, by rw [hall j]; exact Finset.mem_inter.mpr ⟨hpR, hpP⟩⟩
        by_cases hcond : ∀ j : Fin K, pick j (f j).1 (f j).2.1 (f j).2.2 = R ∩ P j
        · rw [if_pos (hiff.mpr hcond)]
          exact Finset.prod_eq_one fun j _ => if_pos (hcond j)
        · rw [if_neg (fun h => hcond (hiff.mp h))]
          push Not at hcond
          obtain ⟨j, hj⟩ := hcond
          exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
      · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [← hprod_eq]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type]
  -- Sum `hdecomp` over `R ∈ 𝒜`!
  have hsum_𝒜 :
      ∑ R ∈ 𝒜, muBlock P_all R =
      ∑ T : (∀ j : Fin K, NE j), (∏ j : Fin K, nu j (T j)) *
        ∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) *
          (((1 / 2 : ℝ) ^ K) * ∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then 1 else 0) := by
    have h1 : ∑ R ∈ 𝒜, muBlock P_all R =
        ∑ R ∈ 𝒜, ∑ T : (∀ j : Fin K, NE j), ∑ σ : Fin K → Fin 3, ∑ b : Fin K → Bool,
          (∏ j : Fin K, nu j (T j)) * (∏ j : Fin K, w j (σ j)) * ((1 / 2 : ℝ) ^ K) *
            (if combine T σ b = R then 1 else 0) :=
      Finset.sum_congr rfl fun R hR => hdecomp R (Finset.mem_powerset.mpr (hsub R hR))
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    have hpull :
        (∑ b : Fin K → Bool, ∑ R ∈ 𝒜,
          (∏ j : Fin K, nu j (T j)) * (∏ j : Fin K, w j (σ j)) * ((1 / 2 : ℝ) ^ K) *
            (if combine T σ b = R then 1 else 0)) =
        (∏ j : Fin K, nu j (T j)) * ((∏ j : Fin K, w j (σ j)) *
          (((1 / 2 : ℝ) ^ K) * ∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then 1 else 0)) := by
      have hinner : ∀ b : Fin K → Bool,
          (∑ R ∈ 𝒜, (∏ j : Fin K, nu j (T j)) * (∏ j : Fin K, w j (σ j)) * ((1 / 2 : ℝ) ^ K) *
            (if combine T σ b = R then 1 else 0)) =
          (∏ j : Fin K, nu j (T j)) * ((∏ j : Fin K, w j (σ j)) *
            (((1 / 2 : ℝ) ^ K) * (if combine T σ b ∈ 𝒜 then 1 else 0))) := by
        intro b
        rw [← Finset.mul_sum]
        have hsum_ind : (∑ R ∈ 𝒜, if combine T σ b = R then (1 : ℝ) else 0) =
            if combine T σ b ∈ 𝒜 then 1 else 0 := by
          simp
        rw [hsum_ind]; ring
      simp_rw [hinner, ← Finset.mul_sum]
    exact hpull
  -- For fixed `(T, σ)`, bound the fair-coin average over `b : Fin K → Bool` by Sperner!
  have hinner_bd : ∀ (T : ∀ j : Fin K, NE j) (σ : Fin K → Fin 3),
      let m := (Finset.univ.filter fun j : Fin K => σ j = 0).card
      ((1 / 2 : ℝ) ^ K) * (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) ≤
        min 1 (2 / Real.sqrt ((m : ℝ) + 1)) := by
    intro T σ m
    let I : Finset (Fin K) := Finset.univ.filter fun j : Fin K => σ j = 0
    have hm : m = I.card := rfl
    have hle1 : ((1 / 2 : ℝ) ^ K) * (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) ≤ 1 := by
      have hcnt : (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ K := by
        calc (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0)
            ≤ ∑ _b : Fin K → Bool, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
          _ = (Fintype.card (Fin K → Bool) : ℝ) := by simp
          _ = (2 : ℝ) ^ K := by simp
      calc ((1 / 2 : ℝ) ^ K) * (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0)
          ≤ ((1 / 2 : ℝ) ^ K) * (2 : ℝ) ^ K := mul_le_mul_of_nonneg_left hcnt (by positivity)
        _ = 1 := by rw [← mul_pow]; norm_num
    refine le_min hle1 ?_
    -- Group `b : Fin K → Bool` by `z(b) = I.filter (fun j => b j = true) ∈ I.powerset`.
    let combZ (z : Finset (Fin K)) : Finset ℕ :=
      Finset.univ.biUnion fun j : Fin K => if σ j = 2 ∨ (σ j = 0 ∧ j ∈ z) then (T j).1 else ∅
    have hcomb_eq : ∀ b : Fin K → Bool,
        combine T σ b = combZ (I.filter fun j => b j = true) := by
      intro b
      refine Finset.biUnion_congr rfl fun j _ => ?_
      dsimp only [pick]
      have hiff : (σ j = 2 ∨ (σ j = 0 ∧ b j = true)) ↔
          (σ j = 2 ∨ (σ j = 0 ∧ j ∈ I.filter fun j => b j = true)) := by
        simp [I]
      by_cases h : σ j = 2 ∨ (σ j = 0 ∧ b j = true)
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
    let ℬ : Finset (Finset (Fin K)) := I.powerset.filter fun z => combZ z ∈ 𝒜
    have hℬ_anti : ∀ z₁ ∈ ℬ, ∀ z₂ ∈ ℬ, z₁ ⊆ z₂ → z₁ = z₂ := by
      intro z₁ hz₁ z₂ hz₂ hsub12
      have hc1 : combZ z₁ ∈ 𝒜 := (Finset.mem_filter.mp hz₁).2
      have hc2 : combZ z₂ ∈ 𝒜 := (Finset.mem_filter.mp hz₂).2
      have hcomb_sub : combZ z₁ ⊆ combZ z₂ := by
        intro p hp
        obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
        split_ifs at hpj with h1
        · have h2 : σ j = 2 ∨ (σ j = 0 ∧ j ∈ z₂) := by
            rcases h1 with h1 | ⟨h1, hj1⟩
            · exact Or.inl h1
            · exact Or.inr ⟨h1, hsub12 hj1⟩
          rw [if_pos h2]; exact hpj
        · simp at hpj
      have heq_comb := hanti _ hc1 _ hc2 hcomb_sub
      -- Deduce `z₁ = z₂` because `z₁, z₂ ⊆ I` and each `(T j).1` is nonempty and disjoint!
      ext j
      constructor
      · intro hj1; exact hsub12 hj1
      · intro hj2
        have hjI : j ∈ I := Finset.mem_powerset.mp (Finset.mem_filter.mp hz₂).1 hj2
        have hσj : σ j = 0 := (Finset.mem_filter.mp hjI).2
        have htne : (T j).1.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (T j).2).1
        obtain ⟨p, hpT⟩ := htne
        have hpP : p ∈ P j := Finset.mem_powerset.mp (Finset.mem_erase.mp (T j).2).2 hpT
        have hp2 : p ∈ combZ z₂ := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
          rw [if_pos (Or.inr ⟨hσj, hj2⟩)]; exact hpT⟩
        rw [← heq_comb] at hp2
        obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp2
        have hpPi : p ∈ P i := by
          split_ifs at hpi
          · exact Finset.mem_powerset.mp (Finset.mem_erase.mp (T i).2).2 hpi
          · simp at hpi
        have hij : i = j := by
          by_contra hne
          exact Finset.disjoint_left.mp (hPdisj i j hne) hpPi hpP
        subst hij
        split_ifs at hpi with hc
        · rcases hc with h2 | ⟨_, hj1⟩
          · rw [hσj] at h2; exact (show (0 : Fin 3) ≠ 2 by decide) h2 |>.elim
          · exact hj1
        · simp at hpi
    have hℬ_card : ℬ.card ≤ m.choose (m / 2) := by
      rw [hm]
      exact sperner_finset I ℬ (fun z hz => Finset.mem_powerset.mp (Finset.mem_filter.mp hz).1) hℬ_anti
    -- Count fiber size: for each `z ∈ I.powerset`, `#{b : Fin K → Bool | I.filter (b · = true) = z} = 2^(K - m)`.
    have hfib : ∀ z ∈ I.powerset,
        ((Finset.univ : Finset (Fin K → Bool)).filter
          fun b => I.filter (fun j => b j = true) = z).card = 2 ^ (K - m) := by
      intro z hz
      have hzI : z ⊆ I := Finset.mem_powerset.mp hz
      let e : { b : Fin K → Bool // I.filter (fun j => b j = true) = z } ≃ (↥(Iᶜ : Finset (Fin K)) → Bool) :=
        { toFun := fun b x => b.1 x.1
          invFun := fun g =>
            ⟨fun j => if hj : j ∈ I then decide (j ∈ z) else g ⟨j, Finset.mem_compl.mpr hj⟩, by
              ext j
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hjI, hb⟩
                simp only [hjI, ↓reduceDIte, decide_eq_true_eq] at hb
                exact hb
              · intro hjz
                have hjI := hzI hjz
                simp [hjI, hjz]⟩
          left_inv := fun b => by
            ext j
            by_cases hjI : j ∈ I
            · simp only [hjI, ↓reduceDIte]
              have hiff : j ∈ z ↔ b.1 j = true := by
                have hmem := Finset.ext_iff.mp b.2 j
                simp only [Finset.mem_filter, hjI, true_and] at hmem
                exact hmem.symm
              cases hb : b.1 j
              · rw [decide_eq_false (by rw [hiff, hb]; decide)]
              · rw [decide_eq_true (by rw [hiff, hb])]
            · simp [hjI]
          right_inv := fun g => by
            ext x
            have hx : x.1 ∉ I := Finset.mem_compl.mp x.2
            simp [hx] }
      have hcard_eq : ((Finset.univ : Finset (Fin K → Bool)).filter
          fun b => I.filter (fun j => b j = true) = z).card =
          Fintype.card (↥(Iᶜ : Finset (Fin K)) → Bool) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr ?_
        exact (Equiv.subtypeEquivRight fun b => by simp).trans e
      rw [hcard_eq, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl,
        Fintype.card_fin, hm]
    -- Sum by fibers over `z ∈ ℬ`.
    have hsum_b :
        (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) =
        (ℬ.card : ℝ) * (2 : ℝ) ^ (K - m) := by
      have hcard_b : (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) =
          (((Finset.univ : Finset (Fin K → Bool)).filter fun b => combine T σ b ∈ 𝒜).card : ℝ) := by
        rw [Finset.sum_boole]
      rw [hcard_b]
      have hpart : ((Finset.univ : Finset (Fin K → Bool)).filter fun b => combine T σ b ∈ 𝒜).card =
          ∑ z ∈ ℬ, ((Finset.univ : Finset (Fin K → Bool)).filter
            fun b => I.filter (fun j => b j = true) = z).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun b : Fin K → Bool => I.filter fun j => b j = true) (t := ℬ)]
        · refine Finset.sum_congr rfl fun z hz => ?_
          congr 1
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨_, hzb⟩; exact hzb
          · intro hzb
            refine ⟨?_, hzb⟩
            rw [hcomb_eq, hzb]
            exact (Finset.mem_filter.mp hz).2
        · intro b hb
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.filter_subset _ _, ?_⟩
          rw [← hcomb_eq]
          exact (Finset.mem_filter.mp hb).2
      rw [hpart]
      have hsum_nat : (∑ z ∈ ℬ, ((Finset.univ : Finset (Fin K → Bool)).filter
          fun b => I.filter (fun j => b j = true) = z).card) = ℬ.card * 2 ^ (K - m) := by
        calc ∑ z ∈ ℬ, _
            = ∑ _z ∈ ℬ, 2 ^ (K - m) :=
              Finset.sum_congr rfl fun z hz => hfib z (Finset.mem_filter.mp hz).1
          _ = ℬ.card * 2 ^ (K - m) := by rw [Finset.sum_const, smul_eq_mul]
      exact_mod_cast hsum_nat
    rw [hsum_b]
    have hmK : m ≤ K := by simpa [hm] using Finset.card_le_univ I
    have hpow_simp : ((1 / 2 : ℝ) ^ K) * ((ℬ.card : ℝ) * (2 : ℝ) ^ (K - m)) =
        (ℬ.card : ℝ) / (2 : ℝ) ^ m := by
      have h2K : (2 : ℝ) ^ K = (2 : ℝ) ^ m * (2 : ℝ) ^ (K - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hmK]
      have hne : (2 : ℝ) ^ (K - m) ≠ 0 := by positivity
      calc ((1 / 2 : ℝ) ^ K) * ((ℬ.card : ℝ) * (2 : ℝ) ^ (K - m))
          = ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ (K - m))⁻¹ * ((ℬ.card : ℝ) * (2 : ℝ) ^ (K - m)) := by
            rw [one_div, inv_pow, h2K, mul_inv]
        _ = ((ℬ.card : ℝ) * ((2 : ℝ) ^ m)⁻¹) * (((2 : ℝ) ^ (K - m))⁻¹ * (2 : ℝ) ^ (K - m)) := by ring
        _ = (ℬ.card : ℝ) / (2 : ℝ) ^ m := by rw [inv_mul_cancel₀ hne, mul_one, div_eq_mul_inv]
    rw [hpow_simp]
    calc (ℬ.card : ℝ) / (2 : ℝ) ^ m
        ≤ (m.choose (m / 2) : ℝ) / (2 : ℝ) ^ m :=
          div_le_div_of_nonneg_right (by exact_mod_cast hℬ_card) (by positivity)
      _ ≤ 2 / Real.sqrt ((m : ℝ) + 1) := central_binom_div_two_pow_le m
  -- Combine `hsum_𝒜`, `hinner_bd`, and `chebyshev_active_count`!
  rw [hsum_𝒜]
  have hT_bd : ∀ T : (∀ j : Fin K, NE j),
      (∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) *
        (((1 / 2 : ℝ) ^ K) * ∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then 1 else 0)) ≤
      81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ) := by
    intro T
    have hle :
        (∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) *
          (((1 / 2 : ℝ) ^ K) * ∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then 1 else 0)) ≤
        ∑ σ : Fin K → Fin 3,
          ((if ((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) < (K : ℝ) / 9
            then ∏ j : Fin K, w j (σ j) else 0) +
           (∏ j : Fin K, w j (σ j)) * (6 / Real.sqrt (K : ℝ))) := by
      refine Finset.sum_le_sum fun σ _ => ?_
      have hprod_nn : 0 ≤ ∏ j : Fin K, w j (σ j) := Finset.prod_nonneg fun j _ => hw_nn j (σ j)
      have hbd := hinner_bd T σ
      by_cases hlt : ((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) < (K : ℝ) / 9
      · rw [if_pos hlt]
        have h1 : ((1 / 2 : ℝ) ^ K) * (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) ≤ 1 :=
          hbd.trans (min_le_left _ _)
        have h2 : 0 ≤ (∏ j : Fin K, w j (σ j)) * (6 / Real.sqrt (K : ℝ)) :=
          mul_nonneg hprod_nn (by positivity)
        nlinarith
      · rw [if_neg hlt, zero_add]
        push Not at hlt
        have h2 : ((1 / 2 : ℝ) ^ K) * (∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then (1 : ℝ) else 0) ≤
            6 / Real.sqrt (K : ℝ) := by
          refine (hbd.trans (min_le_right _ _)).trans ?_
          have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
          have hsq_ge : Real.sqrt (K : ℝ) / 3 ≤
              Real.sqrt (((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) + 1) := by
            have h9 : Real.sqrt ((K : ℝ) / 9) = Real.sqrt (K : ℝ) / 3 := by
              rw [Real.sqrt_div hKpos.le]; norm_num
            rw [← h9]
            exact Real.sqrt_le_sqrt (by linarith)
          have hpos_l : (0 : ℝ) < Real.sqrt (K : ℝ) / 3 := by positivity
          calc 2 / Real.sqrt (((Finset.univ.filter fun j : Fin K => σ j = 0).card : ℝ) + 1)
              ≤ 2 / (Real.sqrt (K : ℝ) / 3) := div_le_div_of_nonneg_left (by norm_num) hpos_l hsq_ge
            _ = 6 / Real.sqrt (K : ℝ) := by ring
        exact mul_le_mul_of_nonneg_left h2 hprod_nn
    refine hle.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hsum_w : ∑ σ : Fin K → Fin 3, ∏ j : Fin K, w j (σ j) = 1 := by
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun j _ => hw_sum j
    rw [hsum_w, one_mul]
    linarith [chebyshev_active_count hK w hw_nn hw_sum hw0]
  calc ∑ T : (∀ j : Fin K, NE j), (∏ j : Fin K, nu j (T j)) *
          ∑ σ : Fin K → Fin 3, (∏ j : Fin K, w j (σ j)) *
            (((1 / 2 : ℝ) ^ K) * ∑ b : Fin K → Bool, if combine T σ b ∈ 𝒜 then 1 else 0)
      ≤ ∑ T : (∀ j : Fin K, NE j), (∏ j : Fin K, nu j (T j)) *
          (81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ)) :=
        Finset.sum_le_sum fun T _ =>
          mul_le_mul_of_nonneg_left (hT_bd T) (Finset.prod_nonneg fun j _ => hnu_nn j (T j))
    _ = (∑ T : (∀ j : Fin K, NE j), ∏ j : Fin K, nu j (T j)) *
          (81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ)) := (Finset.sum_mul _ _ _).symm
    _ = 81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ) := by
        have hsum_nu : ∑ T : (∀ j : Fin K, NE j), ∏ j : Fin K, nu j (T j) = 1 := by
          rw [← Fintype.prod_sum]
          exact Finset.prod_eq_one fun j _ => hnu_sum j
        rw [hsum_nu, one_mul]

/- ## Section 4: Factorization into `(v, s, R)`, `Q`-block bound, and closing `H1` -/

/-- `Q`-block upper bound on `∑_{1 ≤ v ≤ M, (v, Q) = 1} 1 / v`. -/
lemma coprime_harmonic_le {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 1 ≤ M) :
    ∑ v ∈ (Finset.Icc 1 M).filter (fun v => Nat.Coprime v Q), (1 : ℝ) / (v : ℝ) ≤
      (Q : ℝ) + ((Nat.totient Q : ℝ) / (Q : ℝ)) * (Real.log (M : ℝ) + 1) := by
  classical
  let A := (Finset.Icc 1 M).filter fun v => Nat.Coprime v Q
  let A₁ := A.filter fun v => v ≤ Q
  let A₂ := A.filter fun v => Q < v
  have hsplit : ∑ v ∈ A, (1 : ℝ) / (v : ℝ) =
      (∑ v ∈ A₁, (1 : ℝ) / (v : ℝ)) + ∑ v ∈ A₂, (1 : ℝ) / (v : ℝ) := by
    have hu : A = A₁ ∪ A₂ := by
      ext v; simp only [A₁, A₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hv
        by_cases hle : v ≤ Q
        · exact Or.inl ⟨hv, hle⟩
        · exact Or.inr ⟨hv, by omega⟩
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    have hd : Disjoint A₁ A₂ := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [A₁, A₂, Finset.mem_filter] at h1 h2; omega
    conv_lhs => rw [hu]
    exact Finset.sum_union hd
  rw [hsplit]
  have h1 : ∑ v ∈ A₁, (1 : ℝ) / (v : ℝ) ≤ (Q : ℝ) := by
    have hsub : A₁ ⊆ Finset.Icc 1 Q := by
      intro v hv
      simp only [A₁, A, Finset.mem_filter, Finset.mem_Icc] at hv ⊢
      exact ⟨hv.1.1.1, hv.2⟩
    calc ∑ v ∈ A₁, (1 : ℝ) / (v : ℝ)
        ≤ ∑ _v ∈ A₁, (1 : ℝ) := Finset.sum_le_sum fun v hv => by
          have hv1 : (1 : ℝ) ≤ (v : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp (hsub hv)).1
          exact div_le_one_of_le₀ hv1 (by linarith)
      _ = (A₁.card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 Q).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (Q : ℝ) := by rw [Nat.card_Icc]; simp
  -- Partition `A₂` into blocks `B k = (Ioc (k * Q) ((k + 1) * Q)).filter (Coprime · Q)` for `k ∈ Icc 1 M`.
  have hcop_mod : ∀ v : ℕ, Nat.Coprime (v % Q) Q ↔ Nat.Coprime v Q := by
    intro v
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm v Q, Nat.gcd_rec Q v]
  let blk (k : ℕ) : Finset ℕ := (Finset.Ioc (k * Q) ((k + 1) * Q)).filter fun v => Nat.Coprime v Q
  have hblk_card : ∀ k : ℕ, (blk k).card = Nat.totient Q := by
    intro k
    rw [Nat.totient_eq_card_coprime]
    refine Finset.card_bij (fun v _ => v % Q) ?_ ?_ ?_
    · intro v hv
      obtain ⟨_, hcop⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt v (by omega)), ?_⟩
      rw [Nat.coprime_comm]
      exact (hcop_mod v).mpr hcop
    · intro v₁ hv₁ v₂ hv₂ hmod
      obtain ⟨hI1, _⟩ := Finset.mem_filter.mp hv₁
      obtain ⟨hI2, _⟩ := Finset.mem_filter.mp hv₂
      rw [Finset.mem_Ioc] at hI1 hI2
      let d₁ := v₁ - k * Q
      let d₂ := v₂ - k * Q
      have hv1 : v₁ = k * Q + d₁ := by dsimp [d₁]; omega
      have hv2 : v₂ = k * Q + d₂ := by dsimp [d₂]; omega
      have hd1_pos : 1 ≤ d₁ := by dsimp [d₁]; omega
      have hd2_pos : 1 ≤ d₂ := by dsimp [d₂]; omega
      have hmulQ : (k + 1) * Q = k * Q + Q := by ring
      have hd1_le : d₁ ≤ Q := by dsimp [d₁]; omega
      have hd2_le : d₂ ≤ Q := by dsimp [d₂]; omega
      have hmod' : d₁ % Q = d₂ % Q := by
        rw [hv1, hv2, Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right] at hmod
        exact hmod
      have hd_eq : d₁ = d₂ := by
        by_cases h1Q : d₁ = Q
        · by_cases h2Q : d₂ = Q
          · omega
          · rw [h1Q, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod'; omega
        · by_cases h2Q : d₂ = Q
          · rw [h2Q, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod'; omega
          · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod'; exact hmod'
      omega
    · intro r hr
      obtain ⟨hrQ, hcop⟩ := Finset.mem_filter.mp hr
      rw [Finset.mem_range] at hrQ
      by_cases hr0 : r = 0
      · refine ⟨(k + 1) * Q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by nlinarith, le_rfl⟩, ?_⟩, ?_⟩
        · subst hr0
          have hQ1 : Q = 1 := by
            rw [Nat.coprime_zero_right] at hcop; exact hcop
          subst hQ1; exact Nat.coprime_one_right _
        · rw [hr0, Nat.mul_mod_left]
      · refine ⟨k * Q + r, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by nlinarith⟩, ?_⟩, ?_⟩
        · rw [Nat.coprime_comm] at hcop
          rw [← hcop_mod, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hrQ]
          exact hcop
        · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hrQ]
  have hsub2 : A₂ ⊆ (Finset.Icc 1 M).biUnion blk := by
    intro v hv
    obtain ⟨hA, hvQ⟩ := Finset.mem_filter.mp hv
    obtain ⟨hI, hcop⟩ := Finset.mem_filter.mp hA
    rw [Finset.mem_Icc] at hI
    let k := (v - 1) / Q
    have hk1 : 1 ≤ k := by
      dsimp [k]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hkM : k ≤ M := by
      dsimp [k]; exact le_trans (Nat.div_le_self _ _) (by omega)
    have hv_lo : k * Q < v := by
      dsimp only [k]
      have := Nat.div_mul_le_self (v - 1) Q
      omega
    have hv_hi : v ≤ (k + 1) * Q := by
      have h1 : v - 1 < ((v - 1) / Q) * Q + Q := by
        have := Nat.lt_div_mul_add (a := v - 1) (b := Q) (by omega)
        linarith
      have h2 : (k + 1) * Q = ((v - 1) / Q) * Q + Q := by dsimp only [k]; ring
      omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkM⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hv_lo, hv_hi⟩, hcop⟩⟩
  have hblk_disj : ((Finset.Icc 1 M : Finset ℕ) : Set ℕ).PairwiseDisjoint blk := by
    intro k₁ _ k₂ _ hne
    change Disjoint (blk k₁) (blk k₂)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have h1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hv₁).1
    have h2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp hv₂).1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (k₁ + 1) * Q ≤ k₂ * Q := Nat.mul_le_mul_right Q (by omega)
      omega
    · have : (k₂ + 1) * Q ≤ k₁ * Q := Nat.mul_le_mul_right Q (by omega)
      omega
  have h2 : ∑ v ∈ A₂, (1 : ℝ) / (v : ℝ) ≤
      ((Nat.totient Q : ℝ) / (Q : ℝ)) * (Real.log (M : ℝ) + 1) := by
    calc ∑ v ∈ A₂, (1 : ℝ) / (v : ℝ)
        ≤ ∑ v ∈ (Finset.Icc 1 M).biUnion blk, (1 : ℝ) / (v : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity
      _ = ∑ k ∈ Finset.Icc 1 M, ∑ v ∈ blk k, (1 : ℝ) / (v : ℝ) :=
          Finset.sum_biUnion hblk_disj
      _ ≤ ∑ k ∈ Finset.Icc 1 M, ∑ _v ∈ blk k, (1 : ℝ) / ((k : ℝ) * (Q : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun v hv => ?_
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hvlo : k * Q < v := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hv).1).1
          have hle : (k : ℝ) * (Q : ℝ) ≤ (v : ℝ) := by exact_mod_cast hvlo.le
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hle
      _ = ((Nat.totient Q : ℝ) / (Q : ℝ)) * ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, hblk_card k, nsmul_eq_mul]
          ring
      _ ≤ ((Nat.totient Q : ℝ) / (Q : ℝ)) * (Real.log (M : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (harmonic_le_log_add_one M hM) (by positivity)
  linarith

/-- For a finite set `P_all` of primes, `φ(∏ P_all) / (∏ P_all) = ∏_{p ∈ P_all} (1 - 1 / p)`. -/
lemma totient_prod_primes_div (P_all : Finset ℕ) (hprime : ∀ p ∈ P_all, p.Prime) :
    ((Nat.totient (∏ p ∈ P_all, p) : ℝ) / ((∏ p ∈ P_all, p : ℕ) : ℝ)) =
      ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ)) := by
  classical
  induction P_all using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
    have hp : p.Prime := hprime p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hs q hq)).mpr (fun heq => hpnot (heq ▸ hq))
    rw [Finset.prod_insert hpnot, Finset.prod_insert hpnot, Nat.totient_mul hcop,
      Nat.totient_prime hp, Nat.cast_mul, Nat.cast_mul]
    have hphi_p : (((p - 1 : ℕ) : ℝ) / (p : ℝ)) = 1 - (1 : ℝ) / (p : ℝ) := by
      have hp1 : 1 ≤ p := hp.one_lt.le
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [Nat.cast_sub hp1, Nat.cast_one]; field_simp
    rw [mul_div_mul_comm, hphi_p, ih hs]

/-- Sum of reciprocals of `P_all`-smooth squares `≤ M` is at most `∏_{p ∈ P_all} (1 - 1/p²)⁻¹`. -/
lemma sum_smooth_squares_le (P_all : Finset ℕ) (hprime : ∀ p ∈ P_all, p.Prime) (M : ℕ) :
    let Ssq := (Finset.Icc 1 M).filter fun s =>
      (∏ p ∈ P_all, p ^ (2 * (padicValNat p s / 2))) = s
    ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) ≤ ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ := by
  classical
  intro Ssq
  have hgeom : ∀ p ∈ P_all,
      ∑ e ∈ Finset.range (M + 1), ((1 : ℝ) / (p : ℝ) ^ 2) ^ e ≤ (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    exact geom_sum_le_inv (by positivity) (by rw [div_lt_one (by positivity)]; nlinarith) (M + 1)
  have hprod_le :
      ∏ p ∈ P_all, ∑ e ∈ Finset.range (M + 1), ((1 : ℝ) / (p : ℝ) ^ 2) ^ e ≤
      ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ :=
    Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hgeom
  refine le_trans ?_ hprod_le
  rw [Finset.prod_sum]
  let emb : ℕ → ∀ p, p ∈ P_all → ℕ := fun s p _ => padicValNat p s / 2
  have hmaps : ∀ s ∈ Ssq, emb s ∈ P_all.pi (fun _ => Finset.range (M + 1)) := by
    intro s hs
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hsM : s ≤ M := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    have hpow_le : p ^ padicValNat p s ≤ s := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have h2pow : padicValNat p s < 2 ^ padicValNat p s := Nat.lt_two_pow_self
    have h2le : 2 ^ padicValNat p s ≤ p ^ padicValNat p s := Nat.pow_le_pow_left hp2 _
    dsimp [emb]; omega
  have hinj : ∀ s₁ ∈ Ssq, ∀ s₂ ∈ Ssq, emb s₁ = emb s₂ → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := (Finset.mem_filter.mp hs₁).2
    have h2 := (Finset.mem_filter.mp hs₂).2
    rw [← h1, ← h2]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpeq : emb s₁ p hp = emb s₂ p hp := by rw [heq]
    exact congrArg (fun k => p ^ (2 * k)) hpeq
  have hval : ∀ s ∈ Ssq,
      (1 : ℝ) / (s : ℝ) = ∏ p ∈ P_all.attach, ((1 : ℝ) / (p.1 : ℝ) ^ 2) ^ (emb s p.1 p.2) := by
    intro s hs
    have hfac := (Finset.mem_filter.mp hs).2
    have hfacR : (s : ℝ) = ∏ p ∈ P_all.attach, ((p.1 : ℝ) ^ 2) ^ (emb s p.1 p.2) := by
      have : (s : ℝ) = ((∏ p ∈ P_all, p ^ (2 * (padicValNat p s / 2)) : ℕ) : ℝ) := by rw [hfac]
      rw [this, Nat.cast_prod]
      simp only [Nat.cast_pow, pow_mul, emb]
      exact (Finset.prod_attach P_all (fun p => ((p : ℝ) ^ 2) ^ (padicValNat p s / 2))).symm
    rw [hfacR, one_div, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [one_div, inv_pow]
  calc ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ)
      = ∑ s ∈ Ssq, ∏ p ∈ P_all.attach, ((1 : ℝ) / (p.1 : ℝ) ^ 2) ^ (emb s p.1 p.2) :=
        Finset.sum_congr rfl hval
    _ = ∑ f ∈ Ssq.image emb, ∏ p ∈ P_all.attach, ((1 : ℝ) / (p.1 : ℝ) ^ 2) ^ (f p.1 p.2) :=
        (Finset.sum_image (f := fun g => ∏ p ∈ P_all.attach, ((1 : ℝ) / (p.1 : ℝ) ^ 2) ^ (g p.1 p.2))
          (fun s₁ hs₁ s₂ hs₂ h => hinj s₁ hs₁ s₂ hs₂ h)).symm
    _ ≤ ∑ f ∈ P_all.pi (fun _ => Finset.range (M + 1)),
          ∏ p ∈ P_all.attach, ((1 : ℝ) / (p.1 : ℝ) ^ 2) ^ (f p.1 p.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
        intro f hf
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf
        exact hmaps s hs

/-- Exact factorization of any `a ≥ 1` into `P_all`-rough `v`, `P_all`-smooth square `s`, and
squarefree `∏_{p ∈ R} p` (`R ⊆ P_all`). -/
lemma factor_rough_sq_sqfree {P_all : Finset ℕ} (hprime : ∀ p ∈ P_all, p.Prime)
    {a : ℕ} (ha : 1 ≤ a) :
    let u := ∏ p ∈ P_all, p ^ padicValNat p a
    let v := a / u
    let s := ∏ p ∈ P_all, p ^ (2 * (padicValNat p a / 2))
    let R := P_all.filter fun p => padicValNat p a % 2 = 1
    a = v * s * (∏ p ∈ R, p) ∧
    Nat.Coprime v (∏ p ∈ P_all, p) ∧
    (∏ p ∈ P_all, p ^ (2 * (padicValNat p s / 2))) = s ∧
    1 ≤ v ∧ 1 ≤ s := by
  classical
  intro u v s R
  have ha0 : a ≠ 0 := by omega
  have hu_pos : 1 ≤ u := Finset.one_le_prod' fun p hp => Nat.one_le_pow _ _ (hprime p hp).pos
  have hs_pos : 1 ≤ s := Finset.one_le_prod' fun p hp => Nat.one_le_pow _ _ (hprime p hp).pos
  have hu_dvd : u ∣ a := by
    dsimp only [u]
    have hgen : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (∏ p ∈ T, p ^ padicValNat p a) ∣ a := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; simp
      | insert p s hpnot ih =>
        intro hTp
        have hp : p.Prime := hTp p (Finset.mem_insert_self p s)
        have hs : ∀ q ∈ s, q.Prime := fun q hq => hTp q (Finset.mem_insert_of_mem hq)
        rw [Finset.prod_insert hpnot]
        have hcop : Nat.Coprime (p ^ padicValNat p a) (∏ q ∈ s, q ^ padicValNat q a) := by
          refine Nat.Coprime.prod_right fun q hq => ?_
          exact ((Nat.coprime_primes hp (hs q hq)).mpr (fun heq => hpnot (heq ▸ hq))).pow _ _
        exact hcop.mul_dvd_of_dvd_of_dvd pow_padicValNat_dvd (ih hs)
    exact hgen P_all hprime
  have hv_pos : 1 ≤ v := by
    have hle := Nat.le_of_dvd (by omega) hu_dvd
    exact Nat.div_pos hle (by omega)
  have ha_eq_vu : a = v * u := (Nat.div_mul_cancel hu_dvd).symm
  -- Split `u = s * ∏_{p ∈ R} p`.
  have hu_eq : u = s * ∏ p ∈ R, p := by
    have hprod_R : ∏ p ∈ R, p = ∏ p ∈ P_all, p ^ (padicValNat p a % 2) := by
      rw [← Finset.prod_filter_mul_prod_filter_not P_all (fun p => padicValNat p a % 2 = 1)]
      have h1 : ∏ p ∈ P_all.filter (fun p => padicValNat p a % 2 = 1), p ^ (padicValNat p a % 2) =
          ∏ p ∈ R, p := Finset.prod_congr rfl fun p hp => by
        rw [(Finset.mem_filter.mp hp).2, pow_one]
      have h2 : ∏ p ∈ P_all.filter (fun p => ¬ padicValNat p a % 2 = 1), p ^ (padicValNat p a % 2) = 1 :=
        Finset.prod_eq_one fun p hp => by
          have : padicValNat p a % 2 = 0 := by have := (Finset.mem_filter.mp hp).2; omega
          rw [this, pow_zero]
      rw [h1, h2, mul_one]
    rw [hprod_R]
    dsimp only [u, s]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add, Nat.div_add_mod]
  -- `v` is coprime to every `p ∈ P_all`.
  have hv_cop : Nat.Coprime v (∏ p ∈ P_all, p) := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    rw [Nat.coprime_comm, (hprime p hp).coprime_iff_not_dvd]
    intro hpv
    have hpu_dvd : p ^ (padicValNat p a + 1) ∣ a := by
      have hpow_u : p ^ padicValNat p a ∣ u :=
        Finset.dvd_prod_of_mem (fun q => q ^ padicValNat q a) hp
      conv_rhs => rw [ha_eq_vu]
      rw [pow_succ']
      exact mul_dvd_mul hpv hpow_u
    have : Fact p.Prime := ⟨hprime p hp⟩
    have hle := (padicValNat_dvd_iff_le ha0).mp hpu_dvd
    omega
  -- `padicValNat p s = 2 * (padicValNat p a / 2)` for every `p ∈ P_all`.
  have hs_val : ∀ p ∈ P_all, padicValNat p s = 2 * (padicValNat p a / 2) := by
    intro p hp
    have : Fact p.Prime := ⟨hprime p hp⟩
    dsimp only [s]
    rw [← Finset.mul_prod_erase P_all _ hp]
    have hcop_rest : Nat.Coprime p (∏ q ∈ P_all.erase p, q ^ (2 * (padicValNat q a / 2))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := (Finset.mem_erase.mp hq).1.symm
      exact ((Nat.coprime_primes (hprime p hp) (hprime q (Finset.mem_erase.mp hq).2)).mpr hne).pow_right _
    have hne1 : p ^ (2 * (padicValNat p a / 2)) ≠ 0 := pow_ne_zero _ (hprime p hp).ne_zero
    have hne2 : (∏ q ∈ P_all.erase p, q ^ (2 * (padicValNat q a / 2))) ≠ 0 := by
      have : 1 ≤ ∏ q ∈ P_all.erase p, q ^ (2 * (padicValNat q a / 2)) :=
        Finset.one_le_prod' fun q hq => Nat.one_le_pow _ _ (hprime q (Finset.mem_erase.mp hq).2).pos
      omega
    rw [padicValNat.mul hne1 hne2, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ((hprime p hp).coprime_iff_not_dvd.mp hcop_rest), add_zero]
  have hs_id : (∏ p ∈ P_all, p ^ (2 * (padicValNat p s / 2))) = s := by
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hs_val p hp]
    congr 1; omega
  refine ⟨?_, hv_cop, hs_id, hv_pos, hs_pos⟩
  rw [ha_eq_vu, hu_eq, mul_assoc]

end Erdos143R1H1

theorem OMA.solution : OMA.R_Erdos143_erdos_143_parts_i_R1.H1 := by
  classical
  open Erdos143R1H1 Finset BigOperators in
  intro ε hε
  -- Choose `K` large enough that `81 / K + 6 / √K ≤ ε / 2`.
  obtain ⟨K, hK1, hK_bd⟩ : ∃ K : ℕ, 1 ≤ K ∧ 81 / (K : ℝ) + 6 / Real.sqrt (K : ℝ) ≤ ε / 2 := by
    let K : ℕ := Nat.ceil (1000 / ε ^ 2) + 1000
    have hK1 : 1 ≤ K := by dsimp [K]; omega
    refine ⟨K, hK1, ?_⟩
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have hKge : 1000 / ε ^ 2 ≤ (K : ℝ) := by
      have h1 : 1000 / ε ^ 2 ≤ (Nat.ceil (1000 / ε ^ 2) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (1000 / ε ^ 2) : ℝ) ≤ (K : ℝ) := by dsimp [K]; push_cast; linarith
      linarith
    have hKge1000 : (1000 : ℝ) ≤ (K : ℝ) := by dsimp [K]; push_cast; linarith
    have hsq_ge : 30 / ε ≤ Real.sqrt (K : ℝ) := by
      have h1 : (30 / ε) ^ 2 ≤ (K : ℝ) := by
        rw [div_pow]; linarith [div_le_div_of_nonneg_right (by norm_num : (900 : ℝ) ≤ 1000) (sq_nonneg ε)]
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 30 / ε)]
      exact Real.sqrt_le_sqrt h1
    have h6 : 6 / Real.sqrt (K : ℝ) ≤ ε / 5 := by
      calc 6 / Real.sqrt (K : ℝ)
          ≤ 6 / (30 / ε) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq_ge
        _ = ε / 5 := by field_simp; ring
    have h81 : 81 / (K : ℝ) ≤ 3 * ε / 10 := by
      have hsq_le : 81 / (K : ℝ) ≤ 81 / (Real.sqrt (K : ℝ) * 30) := by
        have hrt30 : 30 ≤ Real.sqrt (K : ℝ) := by
          rw [show (30 : ℝ) = Real.sqrt 900 by norm_num]
          exact Real.sqrt_le_sqrt (by linarith)
        have hmul : Real.sqrt (K : ℝ) * 30 ≤ (K : ℝ) := by
          calc Real.sqrt (K : ℝ) * 30
              ≤ Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) :=
                mul_le_mul_of_nonneg_left hrt30 (Real.sqrt_nonneg _)
            _ = (K : ℝ) := Real.mul_self_sqrt hKpos.le
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hmul
      calc 81 / (K : ℝ)
          ≤ 81 / (Real.sqrt (K : ℝ) * 30) := hsq_le
        _ ≤ 81 / ((30 / ε) * 30) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_right hsq_ge (by norm_num))
        _ = 9 * ε / 100 := by field_simp; ring
        _ ≤ 3 * ε / 10 := by linarith
    linarith
  -- Peel off `K` disjoint prime blocks `P : Fin K → Finset ℕ`.
  obtain ⟨P, hPprime, hPdisj, hPsum⟩ := exists_disjoint_prime_blocks K
  let P_all : Finset ℕ := Finset.univ.biUnion P
  have hP_all_prime : ∀ p ∈ P_all, p.Prime := by
    intro p hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hPprime j p hpj
  let Q : ℕ := ∏ p ∈ P_all, p
  have hQ1 : 1 ≤ Q := Finset.one_le_prod' fun p hp => (hP_all_prime p hp).pos
  let C_Q : ℝ := 1 + (Q : ℝ) * ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹
  let M₀ : ℕ := max 2 (Nat.ceil (Real.exp C_Q) + 1)
  refine ⟨M₀, fun M hM S hSbds hSprim => ?_⟩
  have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
  have hlog_ge : C_Q ≤ Real.log (M : ℝ) := by
    have hexp_le : Real.exp C_Q ≤ (M : ℝ) := by
      have h1 : Real.exp C_Q ≤ (Nat.ceil (Real.exp C_Q) : ℝ) := Nat.le_ceil _
      have h2 : Nat.ceil (Real.exp C_Q) + 1 ≤ M := le_trans (le_max_right _ _) hM
      have h3 : (Nat.ceil (Real.exp C_Q) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Real.exp C_Q) ≤ M)
      linarith
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < M))]
    exact hexp_le
  -- Set up the rough and smooth-square index sets in `[1, M]`.
  let Vset : Finset ℕ := (Finset.Icc 1 M).filter fun v => Nat.Coprime v Q
  let Ssq : Finset ℕ := (Finset.Icc 1 M).filter fun s =>
    (∏ p ∈ P_all, p ^ (2 * (padicValNat p s / 2))) = s
  let slice (v s : ℕ) : Finset (Finset ℕ) :=
    P_all.powerset.filter fun R => v * s * (∏ p ∈ R, p) ∈ S
  -- Step 1: For every `(v, s)`, `slice v s` is an antichain in `P_all.powerset`!
  have hslice_anti : ∀ v ∈ Vset, ∀ s ∈ Ssq,
      ∀ R₁ ∈ slice v s, ∀ R₂ ∈ slice v s, R₁ ⊆ R₂ → R₁ = R₂ := by
    intro v hv s hs R₁ hR₁ R₂ hR₂ hsub12
    have hm1 : v * s * (∏ p ∈ R₁, p) ∈ S := (Finset.mem_filter.mp hR₁).2
    have hm2 : v * s * (∏ p ∈ R₂, p) ∈ S := (Finset.mem_filter.mp hR₂).2
    have hdvd : v * s * (∏ p ∈ R₁, p) ∣ v * s * (∏ p ∈ R₂, p) :=
      mul_dvd_mul_left (v * s) (Finset.prod_dvd_prod_of_subset _ _ _ hsub12)
    have heq_val : v * s * (∏ p ∈ R₁, p) = v * s * (∏ p ∈ R₂, p) := by
      by_contra hne
      exact hSprim _ hm1 _ hm2 hne hdvd
    have hv1 : 1 ≤ v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
    have hprod_eq : ∏ p ∈ R₁, p = ∏ p ∈ R₂, p := Nat.eq_of_mul_eq_mul_left (by positivity) heq_val
    -- Since `R₁ ⊆ R₂` are sets of primes (`≥ 2`), equal products imply `R₁ = R₂`.
    by_contra hRne
    have hdiff : (R₂ \ R₁).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hRne (Finset.Subset.antisymm hsub12 h))
    obtain ⟨p, hp⟩ := hdiff
    have hp2 : 2 ≤ p := (hP_all_prime p (Finset.mem_powerset.mp (Finset.mem_filter.mp hR₂).1 (Finset.mem_sdiff.mp hp).1)).two_le
    have hprod_diff : 2 ≤ ∏ q ∈ R₂ \ R₁, q := by
      have hle : p ≤ ∏ q ∈ R₂ \ R₁, q :=
        Nat.le_of_dvd (Finset.prod_pos fun q hq => (hP_all_prime q (Finset.mem_powerset.mp (Finset.mem_filter.mp hR₂).1 (Finset.mem_sdiff.mp hq).1)).pos)
          (Finset.dvd_prod_of_mem _ hp)
      omega
    have hsplit : ∏ q ∈ R₂, q = (∏ q ∈ R₁, q) * (∏ q ∈ R₂ \ R₁, q) :=
      (Finset.prod_sdiff hsub12).symm.trans (mul_comm _ _)
    have hpos1 : 0 < ∏ q ∈ R₁, q :=
      Finset.prod_pos fun q hq => (hP_all_prime q (Finset.mem_powerset.mp (Finset.mem_filter.mp hR₁).1 hq)).pos
    nlinarith
  -- Step 2: Bound `∑_{a ∈ S} 1 / a` by grouping by `(v, s, R)`.
  have hgroup :
      ∑ a ∈ S, (1 : ℝ) / (a : ℝ) ≤
      ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) *
        ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
          ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) := by
    let idx := (Vset ×ˢ Ssq).sigma fun p => slice p.1 p.2
    let f : (Σ p : ℕ × ℕ, Finset ℕ) → ℕ := fun x => x.1.1 * x.1.2 * (∏ p ∈ x.2, p)
    have hsurj : ∀ a ∈ S, ∃ x ∈ idx, f x = a := by
      intro a ha
      have ha2 : 2 ≤ a := (hSbds a ha).1
      have haM : a ≤ M := (hSbds a ha).2
      obtain ⟨hfac, hcop, hsid, hv1, hs1⟩ := factor_rough_sq_sqfree hP_all_prime (by omega : 1 ≤ a)
      set u := ∏ p ∈ P_all, p ^ padicValNat p a
      set v := a / u
      set s := ∏ p ∈ P_all, p ^ (2 * (padicValNat p a / 2))
      set R := P_all.filter fun p => padicValNat p a % 2 = 1
      have hRpos : 1 ≤ ∏ p ∈ R, p :=
        Finset.one_le_prod' fun p hp => (hP_all_prime p (Finset.mem_filter.mp hp).1).pos
      have hvM : v ≤ M := by
        have h1 : v ≤ v * (s * ∏ p ∈ R, p) := Nat.le_mul_of_pos_right v (Nat.mul_pos hs1 hRpos)
        rw [← mul_assoc, ← hfac] at h1
        exact h1.trans haM
      have hsM : s ≤ M := by
        have h1 : s ≤ v * s := Nat.le_mul_of_pos_left s hv1
        have h2 : v * s ≤ v * s * ∏ p ∈ R, p := Nat.le_mul_of_pos_right _ hRpos
        rw [← hfac] at h2
        exact (h1.trans h2).trans haM
      refine ⟨⟨(v, s), R⟩, ?_, hfac.symm⟩
      rw [Finset.mem_sigma, Finset.mem_product]
      refine ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hv1, hvM⟩, hcop⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs1, hsM⟩, hsid⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), hfac ▸ ha⟩⟩
    have hsub_img : S ⊆ idx.image f := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := hsurj a ha
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    calc ∑ a ∈ S, (1 : ℝ) / (a : ℝ)
        ≤ ∑ a ∈ idx.image f, (1 : ℝ) / (a : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun _ _ _ => by positivity
      _ ≤ ∑ x ∈ idx, (1 : ℝ) / (f x : ℝ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => by positivity
      _ = ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) *
            ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
              ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) := by
          dsimp only [idx, f]
          rw [Finset.sum_sigma, Finset.sum_product]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
          dsimp only
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R _ => ?_
          push_cast; ring
  -- Step 3: For each `(v, s)`, relate `1 / ∏ R` to `muBlock P_all R * ∏_{p ∈ P_all} (1 + 1/p)`!
  have hweight_eq : ∀ R ∈ P_all.powerset,
      (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) =
        (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) * muBlock P_all R := by
    intro R hR
    have hRsub : R ⊆ P_all := Finset.mem_powerset.mp hR
    have h1 : ∏ p ∈ R, ((1 + (1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / ((p : ℝ) + 1))) =
        (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hP_all_prime p (hRsub hp)).pos
      field_simp
    have h2 : ∏ p ∈ P_all \ R, ((1 + (1 : ℝ) / (p : ℝ)) * ((p : ℝ) / ((p : ℝ) + 1))) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hP_all_prime p (Finset.mem_sdiff.mp hp).1).pos
      field_simp
    symm
    calc (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) * muBlock P_all R
        = ((∏ p ∈ R, (1 + (1 : ℝ) / (p : ℝ))) * (∏ p ∈ P_all \ R, (1 + (1 : ℝ) / (p : ℝ)))) *
            ((∏ p ∈ R, (1 : ℝ) / ((p : ℝ) + 1)) * (∏ p ∈ P_all \ R, (p : ℝ) / ((p : ℝ) + 1))) := by
          unfold muBlock
          rw [← Finset.prod_sdiff hRsub, mul_comm (∏ p ∈ P_all \ R, _)]
      _ = (∏ p ∈ R, ((1 + (1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / ((p : ℝ) + 1)))) *
            (∏ p ∈ P_all \ R, ((1 + (1 : ℝ) / (p : ℝ)) * ((p : ℝ) / ((p : ℝ) + 1)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
      _ = ((1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ)) * 1 := by rw [h1, h2]
      _ = (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) := mul_one _
  have hslice_bd : ∀ v ∈ Vset, ∀ s ∈ Ssq,
      ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) ≤
        (ε / 2) * ∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ)) := by
    intro v hv s hs
    have heq : ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) =
        (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) * ∑ R ∈ slice v s, muBlock P_all R := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun R hR => hweight_eq R (Finset.mem_filter.mp hR).1
    rw [heq, mul_comm]
    have hw := weighted_antichain_bound hK1 P hPprime hPdisj hPsum (slice v s)
      (fun R hR => Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1) (hslice_anti v hv s hs)
    exact mul_le_mul_of_nonneg_right (hw.trans hK_bd)
      (Finset.prod_nonneg fun _ _ => by positivity)
  -- Step 4: Multiply out the three factors and cancel Euler products!
  have hEuler_cancel :
      (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹) =
      ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_all_prime p hp).two_le
    have hne1 : (1 - (1 : ℝ) / (p : ℝ)) ≠ 0 := by
      have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hne2 : (1 + (1 : ℝ) / (p : ℝ)) ≠ 0 := by positivity
    have hdiff : 1 - (1 : ℝ) / (p : ℝ) ^ 2 = (1 - (1 : ℝ) / (p : ℝ)) * (1 + (1 : ℝ) / (p : ℝ)) := by
      field_simp; ring
    rw [hdiff, mul_inv]
    field_simp
  have hprod_cancel :
      (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_all_prime p hp).two_le
    have hne : (1 - (1 : ℝ) / (p : ℝ)) ≠ 0 := by
      have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    exact inv_mul_cancel₀ hne
  have hinv_nn : 0 ≤ ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_all_prime p hp).two_le
      have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      exact inv_nonneg.mpr (by linarith)
  have hstep1 :
      ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) *
        ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
          ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ) ≤
      (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
        ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) := by
    have h1 : ∀ v ∈ Vset,
        (∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
          ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ)) ≤
        (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) := by
      intro v hv
      calc ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
              ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ)
          ≤ ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
              ((ε / 2) * ∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) :=
            Finset.sum_le_sum fun s hs =>
              mul_le_mul_of_nonneg_left (hslice_bd v hv s hs) (by positivity)
        _ = (ε / 2) * (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) *
              ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) := by rw [← Finset.sum_mul]; ring
        _ ≤ (ε / 2) * (∏ p ∈ P_all, (1 + (1 : ℝ) / (p : ℝ))) *
              ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (sum_smooth_squares_le P_all hP_all_prime M)
              (mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => by positivity))
        _ = (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) := by
            rw [mul_assoc, hEuler_cancel]
    calc ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) *
            ∑ s ∈ Ssq, (1 : ℝ) / (s : ℝ) *
              ∑ R ∈ slice v s, (1 : ℝ) / ((∏ p ∈ R, p : ℕ) : ℝ)
        ≤ ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) *
            ((ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹)) :=
          Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (h1 v hv) (by positivity)
      _ = (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
            ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) := by rw [← Finset.sum_mul]; ring
  have hcop_bd := coprime_harmonic_le hQ1 (by omega : 1 ≤ M)
  rw [totient_prod_primes_div P_all hP_all_prime] at hcop_bd
  calc ∑ a ∈ S, (1 : ℝ) / (a : ℝ)
      ≤ (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
          ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) := hgroup.trans hstep1
    _ ≤ (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
          ((Q : ℝ) + (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))) * (Real.log (M : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcop_bd (mul_nonneg (by positivity) hinv_nn)
    _ = (ε / 2) * (Real.log (M : ℝ) + C_Q) := by
        dsimp only [C_Q]
        calc (ε / 2) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
              ((Q : ℝ) + (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))) * (Real.log (M : ℝ) + 1))
            = (ε / 2) * ((Q : ℝ) * (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) +
                ((∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹) *
                  (∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ)))) * (Real.log (M : ℝ) + 1)) := by ring
          _ = (ε / 2) * (Real.log (M : ℝ) + (1 + (Q : ℝ) * ∏ p ∈ P_all, (1 - (1 : ℝ) / (p : ℝ))⁻¹)) := by
              rw [hprod_cancel, one_mul]; ring
    _ ≤ (ε / 2) * (Real.log (M : ℝ) + Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε * Real.log (M : ℝ) := by ring

