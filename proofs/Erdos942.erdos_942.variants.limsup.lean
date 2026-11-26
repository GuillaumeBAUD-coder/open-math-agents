import FormalConjectures.ErdosProblems.«942»

-- Problem: Erdős Problem 942 — limsup
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/942.lean:51 (declaration Erdos942.erdos_942.variants.limsup)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAErdos942

open Filter

lemma powerful_mul (p z : ℕ) (hp : p.Prime) : Nat.Powerful (p ^ 3 * z ^ 2) := by
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqd : q ∣ p ^ 3 * z ^ 2 := Nat.dvd_of_mem_primeFactors hq
  rcases (Nat.Prime.dvd_mul hqp).mp hqd with h | h
  · have hq2 : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h)
    subst hq2
    exact Dvd.dvd.mul_right (pow_dvd_pow q (by norm_num)) _
  · have : q ∣ z := hqp.dvd_of_dvd_pow h
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd this 2) _

lemma ne_of_primes (p q z w : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hz : z ≠ 0) (hw : w ≠ 0) : p ^ 3 * z ^ 2 ≠ q ^ 3 * w ^ 2 := by
  intro h
  have h1 := congrArg (fun m => m.factorization p) h
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hz),
    Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hw)] at h1
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))] at h1
  omega

lemma approx (K : ℕ) (α : Fin K → ℝ) (Q : ℕ) (hQ : 0 < Q) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - z| < 1 / Q := by
  set N' := max N 1 with hN'
  let f : ℕ → (Fin K → Fin Q) := fun j i =>
    ⟨⌊Int.fract ((j : ℝ) * N' * α i) * Q⌋₊, by
      apply (Nat.floor_lt (by positivity)).mpr
      have := Int.fract_lt_one ((j : ℝ) * N' * α i)
      have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
      calc Int.fract ((j : ℝ) * N' * α i) * Q < 1 * Q := by gcongr
        _ = Q := one_mul _⟩
  have hc : (Finset.univ : Finset (Fin K → Fin Q)).card < (Finset.range (Q ^ K + 1)).card := by
    simp
  obtain ⟨a, -, b, -, hab, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc (f := f) (fun _ _ => Finset.mem_univ _)
  have key : ∀ j1 j2 : ℕ, j1 < j2 → f j1 = f j2 →
      ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - z| < 1 / Q := by
    intro j1 j2 hlt hfe
    refine ⟨(j2 - j1) * N', ?_, ?_, ?_⟩
    · have : 1 ≤ j2 - j1 := by omega
      calc N ≤ N' := le_max_left _ _
        _ = 1 * N' := (one_mul _).symm
        _ ≤ (j2 - j1) * N' := Nat.mul_le_mul_right _ this
    · have : 1 ≤ j2 - j1 := by omega
      have : 1 ≤ N' := le_max_right _ _
      positivity
    · intro i
      have hi := congrFun hfe i
      simp only [f, Fin.mk.injEq] at hi
      set x := (j2 : ℝ) * N' * α i
      set y := (j1 : ℝ) * N' * α i
      refine ⟨⌊x⌋ - ⌊y⌋, ?_⟩
      have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hx0 := Int.fract_nonneg x
      have hy0 := Int.fract_nonneg y
      have h1 := Nat.floor_le (a := Int.fract x * Q) (by positivity)
      have h2 := Nat.lt_floor_add_one (Int.fract x * Q)
      have h3 := Nat.floor_le (a := Int.fract y * Q) (by positivity)
      have h4 := Nat.lt_floor_add_one (Int.fract y * Q)
      rw [hi] at h3 h4
      have hdiff : |Int.fract x - Int.fract y| * Q < 1 := by
        rw [← abs_of_pos hQ', ← abs_mul, sub_mul, abs_lt]
        constructor <;> linarith
      have heq : ((((j2 - j1) * N' : ℕ)) : ℝ) * α i - ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)
          = Int.fract x - Int.fract y := by
        rw [Nat.cast_mul, Nat.cast_sub hlt.le]
        simp only [Int.fract, x, y]
        push_cast
        ring
      rw [heq, lt_div_iff₀ hQ']
      exact hdiff
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hf
  · exact key b a h hf.symm

lemma card_le_h (K t : ℕ) (S : Finset (Fin K)) (p : Fin K → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (w : Fin K → ℕ)
    (hw : ∀ i ∈ S, 0 < w i ∧ (t : ℝ) ≤ w i * Real.sqrt ((p i : ℝ) ^ 3) ∧
      (w i : ℝ) * Real.sqrt ((p i : ℝ) ^ 3) < t + 1) :
    S.card ≤ Erdos942.erdos_942.h t := by
  unfold Erdos942.erdos_942.h
  apply Finset.card_le_card_of_injOn (fun i => p i ^ 3 * w i ^ 2)
  · intro i hi
    obtain ⟨hw0, hlo, hhi⟩ := hw i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico]
    have hsq : (w i * Real.sqrt ((p i : ℝ) ^ 3)) ^ 2 = ((p i ^ 3 * w i ^ 2 : ℕ) : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      push_cast; ring
    refine ⟨⟨?_, ?_⟩, powerful_mul _ _ (hp i)⟩
    · have : ((t ^ 2 : ℕ) : ℝ) ≤ ((p i ^ 3 * w i ^ 2 : ℕ) : ℝ) := by
        rw [← hsq]; push_cast
        exact pow_le_pow_left₀ (by positivity) hlo 2
      exact_mod_cast this
    · have : ((p i ^ 3 * w i ^ 2 : ℕ) : ℝ) < (((t + 1) ^ 2 : ℕ) : ℝ) := by
        rw [← hsq]; push_cast
        exact pow_lt_pow_left₀ hhi (by positivity) (by norm_num)
      exact_mod_cast this
  · intro i hi j hj hij
    by_contra hne
    exact ne_of_primes _ _ _ _ (hp i) (hp j) (fun h => hne (hinj h))
      (hw i hi).1.ne' (hw j hj).1.ne' hij

lemma frequently (k N : ℕ) : ∃ n, N ≤ n ∧ k ≤ Erdos942.erdos_942.h n := by
  set K := 2 * k
  let p : Fin K → ℕ := fun i => Nat.nth Nat.Prime i
  have hp : ∀ i, (p i).Prime := fun i => Nat.prime_nth_prime i
  have hinj : Function.Injective p := fun i j h =>
    Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h)
  set M : ℕ := ∑ i, p i + 1
  have hpM : ∀ i, p i ≤ M := fun i => by
    have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hM1 : 1 ≤ M := by omega
  set Q : ℕ := M ^ 2
  have hQ : 0 < Q := by positivity
  let α : Fin K → ℝ := fun i => 1 / Real.sqrt ((p i : ℝ) ^ 3)
  obtain ⟨n, hNn, hn0, hz⟩ := approx K α Q hQ (N + 1)
  choose z hz using hz
  have hc : ∀ i, 0 < Real.sqrt ((p i : ℝ) ^ 3) := fun i => by
    have := (hp i).pos
    positivity
  have hQα : ∀ i, 1 / (Q : ℝ) ≤ α i := fun i => by
    simp only [α]
    apply one_div_le_one_div_of_le (hc i)
    rw [Real.sqrt_le_left (by positivity)]
    have : (p i : ℝ) ≤ M := by exact_mod_cast hpM i
    have h0 : (0 : ℝ) ≤ p i := by positivity
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    simp only [Q]; push_cast
    calc (p i : ℝ) ^ 3 ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ h0 this 3
      _ ≤ (M : ℝ) ^ 3 * M := le_mul_of_one_le_right (by positivity) hM
      _ = ((M : ℝ) ^ 2) ^ 2 := by ring
  have hαc : ∀ i, α i * Real.sqrt ((p i : ℝ) ^ 3) = 1 := fun i => by
    simp only [α]; field_simp [(hc i).ne']
  set Sneg := (Finset.univ : Finset (Fin K)).filter (fun i => (n : ℝ) * α i - z i ≤ 0)
  set Spos := (Finset.univ : Finset (Fin K)).filter (fun i => ¬ ((n : ℝ) * α i - z i ≤ 0))
  have hcard : Sneg.card + Spos.card = K := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have hαpos : ∀ i, 0 < α i := fun i => by simp only [α]; exact one_div_pos.mpr (hc i)
  by_cases hk : k ≤ Sneg.card
  · refine ⟨n, by omega, le_trans hk ?_⟩
    apply card_le_h K n Sneg p hp hinj (fun i => (z i).toNat)
    intro i hi
    simp only [Sneg, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hb := (abs_lt.mp (hz i))
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hzpos : (0 : ℝ) < z i := by nlinarith [hαpos i]
    have hz0 : 0 < z i := by exact_mod_cast hzpos
    have hcast : (((z i).toNat : ℕ) : ℝ) = (z i : ℝ) := by
      rw [show (((z i).toNat : ℕ) : ℝ) = (((z i).toNat : ℤ) : ℝ) from rfl,
        Int.toNat_of_nonneg hz0.le]
    refine ⟨by omega, ?_, ?_⟩
    · rw [hcast]
      have : (n : ℝ) * α i ≤ z i := by linarith
      have := mul_le_mul_of_nonneg_right this (hc i).le
      rw [mul_assoc, hαc, mul_one] at this
      exact this
    · rw [hcast]
      have : (z i : ℝ) < (n + 1) * α i := by linarith [hQα i]
      have := mul_lt_mul_of_pos_right this (hc i)
      rw [mul_assoc, hαc, mul_one] at this
      exact this
  · have hk2 : k ≤ Spos.card := by omega
    refine ⟨n - 1, by omega, le_trans hk2 ?_⟩
    apply card_le_h K (n - 1) Spos p hp hinj (fun i => (z i).toNat)
    intro i hi
    simp only [Spos, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    have hb := (abs_lt.mp (hz i))
    have hn1 : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hlow : ((n : ℝ) - 1) * α i < z i := by nlinarith [hQα i]
    have hzpos : (0 : ℝ) < z i := by nlinarith [hαpos i]
    have hz0 : 0 < z i := by exact_mod_cast hzpos
    have hcast : (((z i).toNat : ℕ) : ℝ) = (z i : ℝ) := by
      rw [show (((z i).toNat : ℕ) : ℝ) = (((z i).toNat : ℤ) : ℝ) from rfl,
        Int.toNat_of_nonneg hz0.le]
    refine ⟨by omega, ?_, ?_⟩
    · rw [hcast, hn1]
      have := mul_lt_mul_of_pos_right hlow (hc i)
      rw [mul_assoc, hαc, mul_one] at this
      exact this.le
    · rw [hcast, hn1]
      have : (z i : ℝ) < n * α i := by linarith
      have := mul_lt_mul_of_pos_right this (hc i)
      rw [mul_assoc, hαc, mul_one] at this
      linarith

end OMAErdos942

open Filter in
theorem OMA.solution : type_of% @Erdos942.erdos_942.variants.limsup := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine iInf_eq_top.mpr fun N => ?_
  refine (ENat.eq_top_iff_forall_ge).mpr fun k => ?_
  obtain ⟨n, hn, hk⟩ := OMAErdos942.frequently k N
  exact le_iSup₂_of_le n hn (by simpa using hk)
