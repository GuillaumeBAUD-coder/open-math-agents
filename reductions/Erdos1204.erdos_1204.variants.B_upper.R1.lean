import FormalConjectures.ErdosProblems.«1204»

-- Reduction Erdos1204.erdos_1204.variants.B_upper.R1 of Erdős Problem 1204 — B upper
-- Credit: @hyprspacecoyote
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Where `B(k) ≤ (1/2 + o(1)) k log k` comes from

Take the `k` smallest primes larger than `k`, i.e. `p_{π(k)}, …, p_{π(k)+k-1}` (`p_n` is
`Nat.nth Nat.Prime n`, indexed from `0`). They form an admissible set: modulo a prime `p ≤ k` none
of them is `0`, and modulo a prime `p > k` there are only `k < p` of them. Two analytic inputs then
bound their sum:

* `H1`, the prime number theorem in the form `p_n ≤ (1 + ε) n log n` for large `n`;
* `H2`, the Chebyshev-type estimate `π(k) = o(k)`.

With `m = π(k) ≤ δ k` and `log (m + k) ≤ (1 + δ) log k`,
`∑_{j<k} p_{m+j} ≤ (1 + δ)^2 log k · ∑_{j<k} (m + j) ≤ (1 + δ)^2 (δ + 1/2) k^2 log k`.
Everything except `H1` and `H2` is proved here.
-/

namespace OMA.R_Erdos1204_erdos_1204_variants_B_upper_R1

open Filter Topology

/-- The prime number theorem, upper half, for the `n`-th prime: `p_n ≤ (1 + ε) n log n`. -/
def H1 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ (1 + ε) * n * Real.log n

/-- Chebyshev-type density zero of the primes: `π(k) ≤ δ k` for large `k`. -/
def H2 : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (Nat.primeCounting k : ℝ) ≤ δ * k

/-- The `k` primes `p_{π(k)}, …, p_{π(k)+k-1}` form an admissible set, so `minSum k` is at most
their sum. -/
lemma minSum_le_sum (k : ℕ) :
    Erdos1204.minSum k ≤ ∑ j ∈ Finset.range k, Nat.nth Nat.Prime (Nat.primeCounting k + j) := by
  set m := Nat.primeCounting k with hm
  have hinf := Nat.infinite_setOfPred_prime
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono hinf
  have hbig : k < Nat.nth Nat.Prime m := by
    have h3 : k + 1 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (k + 1)) :=
      Nat.le_nth_count hinf (k + 1)
    exact h3
  have hinj : Set.InjOn (fun j => Nat.nth Nat.Prime (m + j)) (Finset.range k : Set ℕ) := by
    intro a _ b _ hab
    have := hmono.injective hab
    omega
  set S : Finset ℕ := (Finset.range k).image (fun j => Nat.nth Nat.Prime (m + j)) with hS
  have hcard : S.card = k := by
    rw [hS, Finset.card_image_of_injOn hinj]
    simp
  have hsum : ∑ a ∈ S, a = ∑ j ∈ Finset.range k, Nat.nth Nat.Prime (m + j) := by
    rw [hS, Finset.sum_image hinj]
  have hmemS : ∀ a ∈ S, a.Prime ∧ k < a := by
    intro a ha
    rw [hS, Finset.mem_image] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact ⟨Nat.prime_nth_prime _, lt_of_lt_of_le hbig (hmono.monotone (by omega))⟩
  have hadm : Erdos1204.IsAdmissible S := by
    intro p hp
    by_cases hpk : p ≤ k
    · refine ⟨0, fun a ha h0 => ?_⟩
      obtain ⟨hap, hka⟩ := hmemS a ha
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := (Nat.prime_dvd_prime_iff_eq hp hap).1 h0
      omega
    · push Not at hpk
      have : Fact p.Prime := ⟨hp⟩
      have hlt : (S.image (fun a : ℕ => (a : ZMod p))).card <
          (Finset.univ : Finset (ZMod p)).card := by
        calc (S.image (fun a : ℕ => (a : ZMod p))).card ≤ S.card := Finset.card_image_le
          _ = k := hcard
          _ < p := hpk
          _ = (Finset.univ : Finset (ZMod p)).card := by simp [ZMod.card]
      obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨r, fun a ha har => hr (Finset.mem_image.2 ⟨a, ha, har⟩)⟩
  rw [← hsum]
  exact Nat.sInf_le ⟨S, hcard, hadm, rfl⟩

lemma sum_range_add_le (m : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, (m + (j : ℝ)) ≤ k * m + (k : ℝ) ^ 2 / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem main : H1 → H2 → type_of% @Erdos1204.erdos_1204.variants.B_upper := by
  intro h1 h2 ε hε
  set δ : ℝ := min (ε / 6) 1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith) one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδle : 6 * δ ≤ ε := by
    have := min_le_left (ε / 6) 1
    linarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 δ hδpos)
  have hπ_ev : ∀ᶠ k : ℕ in atTop, max N1 1 ≤ Nat.primeCounting k :=
    Nat.tendsto_primeCounting.eventually_ge_atTop _
  have hlog : ∀ᶠ k : ℕ in atTop, Real.log 2 ≤ δ * Real.log k := by
    have ht : Tendsto (fun k : ℕ => δ * Real.log k) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδpos
    exact ht.eventually_ge_atTop _
  filter_upwards [hlog, h2 δ hδpos, hπ_ev, eventually_ge_atTop 2] with k hk hπ hπN hk2
  set m := Nat.primeCounting k with hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hmk : (m : ℝ) ≤ k := by nlinarith
  have hN1m : N1 ≤ m := le_trans (le_max_left _ _) hπN
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hπN
  -- `log n ≤ (1 + δ) log k` for every `n ≤ m + k`, `n ≥ 1`
  have hlogn : ∀ n : ℕ, 1 ≤ n → n ≤ m + k → Real.log n ≤ (1 + δ) * Real.log k := by
    intro n hn1 hn2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnle : (n : ℝ) ≤ m + k := by exact_mod_cast hn2
    have : Real.log n ≤ Real.log 2 + Real.log k := by
      rw [← Real.log_mul (by norm_num) hkpos.ne']
      apply Real.log_le_log hnpos
      linarith
    linarith
  have hterm : ∀ j ∈ Finset.range k, (Nat.nth Nat.Prime (m + j) : ℝ) ≤
      ((1 + δ) ^ 2 * Real.log k) * ((m : ℝ) + j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hp := hN1 (m + j) (by omega)
    have hl := hlogn (m + j) (by omega) (by omega)
    have hcast : ((m + j : ℕ) : ℝ) = (m : ℝ) + j := by push_cast; ring
    rw [hcast] at hp hl
    have hmj : (0 : ℝ) ≤ (m : ℝ) + j := by positivity
    calc (Nat.nth Nat.Prime (m + j) : ℝ) ≤ (1 + δ) * ((m : ℝ) + j) * Real.log ((m : ℝ) + j) := hp
      _ ≤ (1 + δ) * ((m : ℝ) + j) * ((1 + δ) * Real.log k) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = ((1 + δ) ^ 2 * Real.log k) * ((m : ℝ) + j) := by ring
  have hsumR : (Erdos1204.minSum k : ℝ) ≤
      ((1 + δ) ^ 2 * Real.log k) * (k * m + (k : ℝ) ^ 2 / 2) := by
    calc (Erdos1204.minSum k : ℝ)
        ≤ ((∑ j ∈ Finset.range k, Nat.nth Nat.Prime (m + j) : ℕ) : ℝ) := by
          exact_mod_cast minSum_le_sum k
      _ = ∑ j ∈ Finset.range k, (Nat.nth Nat.Prime (m + j) : ℝ) := by push_cast; rfl
      _ ≤ ∑ j ∈ Finset.range k, ((1 + δ) ^ 2 * Real.log k) * ((m : ℝ) + j) :=
          Finset.sum_le_sum hterm
      _ = ((1 + δ) ^ 2 * Real.log k) * ∑ j ∈ Finset.range k, ((m : ℝ) + j) := by
          rw [Finset.mul_sum]
      _ ≤ ((1 + δ) ^ 2 * Real.log k) * (k * m + (k : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (sum_range_add_le _ _) (by positivity)
  have hkm : (k : ℝ) * m ≤ δ * (k : ℝ) ^ 2 := by nlinarith
  have hfac : (1 + δ) ^ 2 * (δ + 1 / 2) ≤ 1 / 2 + ε := by
    nlinarith [mul_pos hδpos hδpos, mul_pos (mul_pos hδpos hδpos) hδpos]
  unfold Erdos1204.B
  rw [div_le_iff₀ hkpos]
  calc (Erdos1204.minSum k : ℝ) ≤ ((1 + δ) ^ 2 * Real.log k) * (k * m + (k : ℝ) ^ 2 / 2) := hsumR
    _ ≤ ((1 + δ) ^ 2 * Real.log k) * ((δ + 1 / 2) * (k : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = ((1 + δ) ^ 2 * (δ + 1 / 2)) * ((k : ℝ) ^ 2 * Real.log k) := by ring
    _ ≤ (1 / 2 + ε) * ((k : ℝ) ^ 2 * Real.log k) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = (1 / 2 + ε) * k * Real.log k * k := by ring

end OMA.R_Erdos1204_erdos_1204_variants_B_upper_R1
