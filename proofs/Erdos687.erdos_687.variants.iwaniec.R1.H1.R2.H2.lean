import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2

/-!
# Elementary Mertens-type lower bound for the inverse Euler product

Proves `Real.log (x + 1) ≤ (∏ p ≤ x, (1 - 1 / p))⁻¹` for all `x : ℕ` by comparing
`log (x + 1)` to the harmonic sum `∑_{n=1}^x 1/n`, expanding the geometric series
for each prime `p ≤ x`, and embedding `1 ≤ n ≤ x` via prime factorization.
-/

open Real Finset

private lemma log_succ_le_harmonic (x : ℕ) :
    Real.log ((x : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 x, (n : ℝ)⁻¹ := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ x + 1)]
    have hx1 : (0 : ℝ) < (x : ℝ) + 1 := by positivity
    have hx2 : (0 : ℝ) < (x : ℝ) + 2 := by positivity
    have hlog : Real.log (((x + 1 : ℕ) : ℝ) + 1) - Real.log ((x : ℝ) + 1) ≤
        ((x + 1 : ℕ) : ℝ)⁻¹ := by
      have hdiv : Real.log (((x + 1 : ℕ) : ℝ) + 1) - Real.log ((x : ℝ) + 1) =
          Real.log (((x : ℝ) + 2) / ((x : ℝ) + 1)) := by
        rw [Real.log_div hx2.ne' hx1.ne']
        push_cast
        ring_nf
      rw [hdiv]
      have hle := Real.log_le_sub_one_of_pos (div_pos hx2 hx1)
      have heq : ((x : ℝ) + 2) / ((x : ℝ) + 1) - 1 = ((x + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        ring
      linarith
    linarith

private lemma geom_sum_inv_le (p x : ℕ) (hp : p.Prime) :
    ∑ k ∈ Finset.range (x + 1), ((p : ℝ)⁻¹) ^ k ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1sub : 0 < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith
  rw [inv_eq_one_div (1 - (p : ℝ)⁻¹), le_div_iff₀ h1sub]
  have hgeom := geom_sum_mul_neg (p : ℝ)⁻¹ (x + 1)
  have hpow : 0 ≤ ((p : ℝ)⁻¹) ^ (x + 1) := by positivity
  linarith

private lemma prod_primes_pow_factorization_eq (x n : ℕ) (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p ^ (n.factorization p) = n := by
  have hn0 : n ≠ 0 := by omega
  have hsub : n.factorization.support ⊆ (Finset.range (x + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp.1⟩
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hp.2.1
    omega
  rw [← Finset.prod_subset hsub]
  · exact Nat.prod_factorization_pow_eq_self hn0
  · intro p _ hpn
    have h0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
    simp [h0]

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2.H2 := by
  classical
  intro x
  set P : Finset ℕ := (Finset.range (x + 1)).filter Nat.Prime
  let embed : ℕ → ∀ p : ℕ, p ∈ P → ℕ := fun n p _ => n.factorization p
  have hprod_nat : ∀ n ∈ Finset.Icc 1 x,
      ∏ q ∈ P.attach, q.1 ^ (embed n q.1 q.2) = n := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    rw [Finset.prod_attach P (fun p => p ^ (n.factorization p))]
    exact prod_primes_pow_factorization_eq x n hn1 hnx
  have hinj : Set.InjOn embed (Finset.Icc 1 x) := by
    intro n₁ hn₁ n₂ hn₂ h
    rw [← hprod_nat n₁ hn₁, ← hprod_nat n₂ hn₂]
    exact congr_arg (fun g => ∏ q ∈ P.attach, q.1 ^ (g q.1 q.2)) h
  have hsub_pi : (Finset.Icc 1 x).image embed ⊆ P.pi (fun _ => Finset.range (x + 1)) := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have h1 : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
    have h2 : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) :=
      Nat.pow_le_pow_left hp_prime.two_le _
    have h3 : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
    dsimp [embed]
    omega
  have hterm : ∀ n ∈ Finset.Icc 1 x,
      (n : ℝ)⁻¹ = ∏ q ∈ P.attach, ((q.1 : ℝ)⁻¹) ^ (embed n q.1 q.2) := by
    intro n hn
    have hnat := hprod_nat n hn
    have hcast : (n : ℝ) = ∏ q ∈ P.attach, (q.1 : ℝ) ^ (embed n q.1 q.2) := by
      exact_mod_cast hnat.symm
    rw [hcast, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [inv_pow]
  have hprod_le : ∏ p ∈ P, ∑ k ∈ Finset.range (x + 1), ((p : ℝ)⁻¹) ^ k ≤
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro p _
      exact Finset.sum_nonneg (fun k _ => pow_nonneg (by positivity) k)
    · intro p hp
      exact geom_sum_inv_le p x (Finset.mem_filter.mp hp).2
  calc
    Real.log ((x : ℝ) + 1)
        ≤ ∑ n ∈ Finset.Icc 1 x, (n : ℝ)⁻¹ := log_succ_le_harmonic x
    _ = ∑ n ∈ Finset.Icc 1 x, ∏ q ∈ P.attach, ((q.1 : ℝ)⁻¹) ^ (embed n q.1 q.2) :=
        Finset.sum_congr rfl hterm
    _ = ∑ g ∈ (Finset.Icc 1 x).image embed,
          ∏ q ∈ P.attach, ((q.1 : ℝ)⁻¹) ^ (g q.1 q.2) :=
        (Finset.sum_image
          (f := fun g : ∀ p, p ∈ P → ℕ => ∏ q ∈ P.attach, ((q.1 : ℝ)⁻¹) ^ (g q.1 q.2))
          fun n₁ hn₁ n₂ hn₂ h => hinj hn₁ hn₂ h).symm
    _ ≤ ∑ g ∈ P.pi (fun _ => Finset.range (x + 1)),
          ∏ q ∈ P.attach, ((q.1 : ℝ)⁻¹) ^ (g q.1 q.2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub_pi ?_
        intro g _ _
        exact Finset.prod_nonneg (fun q _ => pow_nonneg (by positivity) _)
    _ = ∏ p ∈ P, ∑ k ∈ Finset.range (x + 1), ((p : ℝ)⁻¹) ^ k :=
        (Finset.prod_sum P (fun _ => Finset.range (x + 1)) (fun p k => ((p : ℝ)⁻¹) ^ k)).symm
    _ ≤ (∏ p ∈ P, (1 - (p : ℝ)⁻¹))⁻¹ := hprod_le
