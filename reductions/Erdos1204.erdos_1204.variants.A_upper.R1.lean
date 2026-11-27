import FormalConjectures.ErdosProblems.«1204»

-- Reduction Erdos1204.erdos_1204.variants.A_upper.R1 of Erdős Problem 1204 — A upper
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Where `A(k) ≤ (1 + o(1)) k log k` comes from

Take the `k` smallest primes larger than `k`. They form an admissible set: modulo a prime `p ≤ k`
none of them is `0`, and modulo a prime `p > k` there are only `k < p` of them, so some class is
missed. They are the primes with indices `π(k), …, π(k) + k - 1`, so all of them are at most
`p_{π(k) + k}`. Two analytic inputs then give the bound:

* `H1`, the prime number theorem in the form `p_n ≤ (1 + ε) n log n` for large `n`
  (`p_n = Nat.nth Nat.Prime n`, indexed from `0`);
* `H2`, the Chebyshev-type estimate `π(k) = o(k)`.

With `N = π(k) + k ≤ (1 + δ) k`, `p_N ≤ (1 + δ) N log N ≤ (1 + δ)^3 k log k` for large `k`.
Everything except `H1` and `H2` is proved here.
-/

namespace OMA.R_Erdos1204_erdos_1204_variants_A_upper_R1

open Filter Topology

/-- The prime number theorem, upper half, for the `n`-th prime: `p_n ≤ (1 + ε) n log n`. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ (1 + ε) * n * Real.log n

/-- Chebyshev-type density zero of the primes: `π(k) ≤ δ k` for large `k`. -/
def H2 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (Nat.primeCounting k : ℝ) ≤ δ * k

/-- The `k` primes `p_{π(k)}, …, p_{π(k)+k-1}` form an admissible set bounded by `p_{π(k)+k}`. -/
lemma A_le_nth (k : ℕ) : Erdos1204.A k ≤ Nat.nth Nat.Prime (Nat.primeCounting k + k) := by
  set m := Nat.primeCounting k with hm
  have hinf := Nat.infinite_setOfPred_prime
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono hinf
  have hbig : k < Nat.nth Nat.Prime m := by
    have h3 : k + 1 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (k + 1)) :=
      Nat.le_nth_count hinf (k + 1)
    exact h3
  set S : Finset ℕ := (Finset.range k).image (fun j => Nat.nth Nat.Prime (m + j)) with hS
  have hcard : S.card = k := by
    rw [hS, Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have := hmono.injective hab
      omega
  have hmemS : ∀ a ∈ S, a.Prime ∧ k < a ∧ a ≤ Nat.nth Nat.Prime (m + k) := by
    intro a ha
    rw [hS, Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    rw [Finset.mem_range] at hj
    refine ⟨Nat.prime_nth_prime _, ?_, ?_⟩
    · exact lt_of_lt_of_le hbig (hmono.monotone (by omega))
    · exact hmono.monotone (by omega)
  apply Erdos1204.A_le hcard
  · intro p hp
    by_cases hpk : p ≤ k
    · refine ⟨0, fun a ha h0 => ?_⟩
      obtain ⟨hap, hka, -⟩ := hmemS a ha
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := (Nat.prime_dvd_prime_iff_eq hp hap).1 h0
      omega
    · push_neg at hpk
      have : Fact p.Prime := ⟨hp⟩
      have hlt : (S.image (fun a : ℕ => (a : ZMod p))).card < (Finset.univ : Finset (ZMod p)).card := by
        calc (S.image (fun a : ℕ => (a : ZMod p))).card ≤ S.card := Finset.card_image_le
          _ = k := hcard
          _ < p := hpk
          _ = (Finset.univ : Finset (ZMod p)).card := by simp [ZMod.card]
      obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨r, fun a ha har => hr ?_⟩
      exact Finset.mem_image.2 ⟨a, ha, har⟩
  · intro a ha
    exact (hmemS a ha).2.2

theorem main : H1 → H2 → type_of% @Erdos1204.erdos_1204.variants.A_upper := by
  intro h1 h2 ε hε
  set δ : ℝ := min (ε / 7) 1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith) one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδle : 7 * δ ≤ ε := by
    have := min_le_left (ε / 7) 1
    linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 δ hδpos)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (h2 δ hδpos)
  -- `log 2 ≤ δ log k` for large `k`
  have hlog : ∀ᶠ k : ℕ in atTop, Real.log 2 ≤ δ * Real.log k := by
    have ht : Tendsto (fun k : ℕ => δ * Real.log k) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδpos
    exact ht.eventually_ge_atTop _
  filter_upwards [hlog, eventually_ge_atTop (max (max N1 N2) 2)] with k hk hkN
  have hk1 : N1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkN
  have hk2 : N2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkN
  have hk2' : 2 ≤ k := le_trans (le_max_right _ _) hkN
  set n := Nat.primeCounting k + k with hn
  have hnk : N1 ≤ n := by omega
  have hA := A_le_nth k
  have hp := hN1 n hnk
  have hπ := hN2 k hk2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have hnreal : (n : ℝ) = Nat.primeCounting k + k := by rw [hn]; push_cast; ring
  have hnle : (n : ℝ) ≤ (1 + δ) * k := by rw [hnreal]; linarith
  have hnpos : (0 : ℝ) < n := by rw [hnreal]; positivity
  have hlogn : Real.log n ≤ Real.log 2 + Real.log k := by
    rw [← Real.log_mul (by norm_num) hkpos.ne']
    apply Real.log_le_log hnpos
    nlinarith
  have hlogn' : Real.log n ≤ (1 + δ) * Real.log k := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [hnreal]; have := (Nat.primeCounting k).cast_nonneg (α := ℝ); linarith)
  calc (Erdos1204.A k : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast hA
    _ ≤ (1 + δ) * n * Real.log n := hp
    _ ≤ (1 + δ) * ((1 + δ) * k) * ((1 + δ) * Real.log k) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hnle (by linarith)) hlogn' hlogn0
        positivity
    _ = (1 + δ) ^ 3 * (k * Real.log k) := by ring
    _ ≤ (1 + ε) * (k * Real.log k) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hkpos.le hlogk)
        nlinarith [mul_pos hδpos hδpos]
    _ = (1 + ε) * k * Real.log k := by ring

end OMA.R_Erdos1204_erdos_1204_variants_A_upper_R1
