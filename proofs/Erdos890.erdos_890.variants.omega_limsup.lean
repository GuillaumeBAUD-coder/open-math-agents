import FormalConjectures.ErdosProblems.«890»

-- Problem: Erdős Problem 890 — omega limsup
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/890.lean:80 (declaration Erdos890.erdos_890.variants.omega_limsup)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Proof sketch.

Upper bound.  Split the prime factors of `n` at a real threshold `y > 1`: at most `y` of them are
`≤ y`, and the product of those `> y` divides `n`, so there are at most `log n / log y` of them.
With `L = log n` and `y = L ^ a`, `a = 2 / (c + 1) < 1`, this gives
`ω n * (log L / L) ≤ L ^ a * log L / L + 1 / a`, and `log L = o(L ^ (1 - a))` makes the first
term at most `(c - 1) / 2` eventually, so the whole thing is eventually `≤ c` for every `c > 1`.

Lower bound.  Take `n = ∏ p ≤ N, p`.  Then `ω n = π N`, `2 ^ π N ≤ n ≤ N ^ π N`, and the
Chebyshev bound `Chebyshev.pi_ge` from Mathlib together with `log N = o(N ^ (1 - c))` gives
`π N * log 2 ≥ N ^ c` for large `N`, hence `log log n ≥ c * log N` and
`ω n * (log log n / log n) ≥ c`.  These `n` are unbounded since `n` is divisible by every
prime `≤ N`.
-/

open Filter Finset Real
open scoped Nat.Prime ArithmeticFunction.omega

namespace E890

lemma omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- Splitting the prime factors of `n` at a real threshold `y > 1`. -/
lemma card_primeFactors_le (n : ℕ) (hn : n ≠ 0) (y : ℝ) (hy : 1 < y) :
    (n.primeFactors.card : ℝ) ≤ y + log n / log y := by
  classical
  have hylog : 0 < log y := Real.log_pos hy
  have hcard := Finset.card_filter_add_card_filter_not (s := n.primeFactors)
    (fun p : ℕ => (p : ℝ) ≤ y)
  have h1 : (((n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℕ) : ℝ) ≤ y := by
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ Finset.Icc 1 ⌊y⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      exact ⟨(Nat.prime_of_mem_primeFactors hp.1).one_le, Nat.le_floor hp.2⟩
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    have h' : (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card ≤ ⌊y⌋₊ := by omega
    calc (((n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℕ) : ℝ)
        ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h'
      _ ≤ y := Nat.floor_le (by linarith)
  have h2 : (((n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℕ) : ℝ)
      ≤ log n / log y := by
    rw [le_div_iff₀ hylog]
    have hprod : ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), p ≤ n := by
      apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
        (Nat.prod_primeFactors_dvd n)
    have hpow : y ^ (n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card ≤ (n : ℝ) := by
      calc y ^ (n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card
          = ∏ _p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), y := by simp
        _ ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (p : ℝ) := by
            apply Finset.prod_le_prod
            · intro i _; linarith
            · intro i hi
              rw [Finset.mem_filter] at hi
              exact (not_le.mp hi.2).le
        _ = ((∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), p : ℕ) : ℝ) := by
            push_cast; rfl
        _ ≤ n := by exact_mod_cast hprod
    have h := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at h
    exact h
  have hc : (n.primeFactors.card : ℝ)
      = (((n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℕ) : ℝ)
        + (((n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℕ) : ℝ) := by
    exact_mod_cast hcard.symm
  rw [hc]
  linarith

/-- Upper bound: eventually `ω n * (log log n / log n) ≤ c` for every `c > 1`. -/
lemma upper_eventually (c : ℝ) (hc : 1 < c) :
    ∀ᶠ n : ℕ in atTop, (ω n : ℝ) * (log (log n) / log n) ≤ c := by
  have ha0 : (0 : ℝ) < 2 / (c + 1) := by positivity
  have ha1 : 2 / (c + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hε0 : 0 < (c - 1) / 2 := by linarith
  have hlo := (isLittleO_log_rpow_atTop (r := 1 - 2 / (c + 1)) (by linarith)).bound hε0
  have htend : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := htend.eventually hlo
  have h2 := htend.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hLpos : 0 < log (n : ℝ) := by linarith
  have hl : 0 < log (log (n : ℝ)) := Real.log_pos hn2
  have hY : 1 < log (n : ℝ) ^ (2 / (c + 1)) := Real.one_lt_rpow hn2 ha0
  have hω := card_primeFactors_le n (by omega) (log (n : ℝ) ^ (2 / (c + 1))) hY
  rw [Real.log_rpow hLpos] at hω
  have hZ : 0 < log (n : ℝ) ^ (1 - 2 / (c + 1)) := Real.rpow_pos_of_pos hLpos _
  have hYZ : log (n : ℝ) ^ (2 / (c + 1)) * log (n : ℝ) ^ (1 - 2 / (c + 1)) = log (n : ℝ) := by
    rw [← Real.rpow_add hLpos]; simp
  rw [Real.norm_of_nonneg hl.le, Real.norm_of_nonneg hZ.le] at hn1
  have key : log (n : ℝ) ^ (2 / (c + 1)) * log (log (n : ℝ)) ≤ (c - 1) / 2 * log (n : ℝ) := by
    calc log (n : ℝ) ^ (2 / (c + 1)) * log (log (n : ℝ))
        ≤ log (n : ℝ) ^ (2 / (c + 1)) * ((c - 1) / 2 * log (n : ℝ) ^ (1 - 2 / (c + 1))) := by
          gcongr
      _ = (c - 1) / 2 * (log (n : ℝ) ^ (2 / (c + 1)) * log (n : ℝ) ^ (1 - 2 / (c + 1))) := by
          ring
      _ = (c - 1) / 2 * log (n : ℝ) := by rw [hYZ]
  have hω' : (ω n : ℝ) ≤ log (n : ℝ) ^ (2 / (c + 1))
      + log (n : ℝ) / (2 / (c + 1) * log (log (n : ℝ))) := by
    rw [omega_eq_card]; exact hω
  calc (ω n : ℝ) * (log (log (n : ℝ)) / log (n : ℝ))
      ≤ (log (n : ℝ) ^ (2 / (c + 1)) + log (n : ℝ) / (2 / (c + 1) * log (log (n : ℝ))))
          * (log (log (n : ℝ)) / log (n : ℝ)) := by
        gcongr
    _ = log (n : ℝ) ^ (2 / (c + 1)) * log (log (n : ℝ)) / log (n : ℝ) + (c + 1) / 2 := by
        field_simp
    _ ≤ (c - 1) / 2 + (c + 1) / 2 := by
        have h3 : log (n : ℝ) ^ (2 / (c + 1)) * log (log (n : ℝ)) / log (n : ℝ)
            ≤ (c - 1) / 2 := by
          rw [div_le_iff₀ hLpos]; exact key
        linarith
    _ = c := by ring

/-- The key real inequality for the primorial-type number `n = ∏ p ≤ N, p`. -/
lemma lower_main (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ) (hN2 : 2 ≤ N)
    (n : ℕ) (hn : n = ∏ q ∈ Nat.primesLE N, q)
    (hlo : ‖log (N : ℝ)‖ ≤ (log 2) ^ 2 / 4 * ‖(N : ℝ) ^ (1 - c)‖) :
    c ≤ (ω n : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) := by
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hlog2' : log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 0 < log (N : ℝ) := Real.log_pos (by linarith)
  have hprime : ∀ q ∈ Nat.primesLE N, q.Prime := fun q hq => (Nat.mem_primesLE.mp hq).2
  have hω : ω n = Nat.primeCounting N := by
    rw [hn, omega_eq_card, Nat.primeFactors_prod hprime, Nat.primesLE_card_eq_primeCounting]
  have hlow : (2 : ℝ) ^ (Nat.primeCounting N) ≤ (n : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, hn]
    push_cast
    calc (2:ℝ) ^ (Nat.primesLE N).card = ∏ _q ∈ Nat.primesLE N, (2:ℝ) := by simp
      _ ≤ ∏ q ∈ Nat.primesLE N, (q : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; norm_num
          · intro i hi; exact_mod_cast (hprime i hi).two_le
  have hupp : (n : ℝ) ≤ (N : ℝ) ^ (Nat.primeCounting N) := by
    rw [← Nat.primesLE_card_eq_primeCounting, hn]
    push_cast
    calc ∏ q ∈ Nat.primesLE N, (q : ℝ) ≤ ∏ _q ∈ Nat.primesLE N, (N : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi; exact_mod_cast (Nat.mem_primesLE.mp hi).1
      _ = (N : ℝ) ^ (Nat.primesLE N).card := by simp
  have hk0 : (0 : ℝ) ≤ (Nat.primeCounting N : ℝ) := Nat.cast_nonneg _
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hlow
  have hlogn_low : (Nat.primeCounting N : ℝ) * log 2 ≤ log (n : ℝ) := by
    have h := Real.log_le_log (by positivity) hlow
    rwa [Real.log_pow] at h
  have hlogn_upp : log (n : ℝ) ≤ (Nat.primeCounting N : ℝ) * log (N : ℝ) := by
    have h := Real.log_le_log hnpos hupp
    rwa [Real.log_pow] at h
  have hcheb := Chebyshev.pi_ge N
  rw [div_le_iff₀ hlN] at hcheb
  have hN1 : log ((N : ℝ) + 1) ≤ 2 * log (N : ℝ) := by
    have h0 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h := Real.log_le_log (by positivity) h0
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hA1 : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow (by linarith) hc0
  have hBpos : 0 < (N : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hNpos _
  have hAB : (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) = N := by
    rw [← Real.rpow_add hNpos]; simp
  rw [Real.norm_of_nonneg hlN.le, Real.norm_of_nonneg hBpos.le] at hlo
  have h1 : (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) * log 2
      ≤ ((Nat.primeCounting N : ℝ) + 2) * ((log 2) ^ 2 / 4 * (N : ℝ) ^ (1 - c)) := by
    calc (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) * log 2 = N * log 2 := by rw [hAB]
      _ ≤ ((Nat.primeCounting N : ℝ) + 2) * log (N : ℝ) := by linarith
      _ ≤ ((Nat.primeCounting N : ℝ) + 2) * ((log 2) ^ 2 / 4 * (N : ℝ) ^ (1 - c)) := by
          apply mul_le_mul_of_nonneg_left hlo
          positivity
  have h2 : 4 * (N : ℝ) ^ c ≤ ((Nat.primeCounting N : ℝ) + 2) * log 2 := by
    have h : (4 * (N : ℝ) ^ c) * ((N : ℝ) ^ (1 - c) * log 2 / 4)
        ≤ (((Nat.primeCounting N : ℝ) + 2) * log 2) * ((N : ℝ) ^ (1 - c) * log 2 / 4) := by
      nlinarith
    exact le_of_mul_le_mul_right h (by positivity)
  have h3 : (N : ℝ) ^ c ≤ (Nat.primeCounting N : ℝ) * log 2 := by nlinarith
  have hkpos : 0 < (Nat.primeCounting N : ℝ) := by
    by_contra h
    have h' : (Nat.primeCounting N : ℝ) ≤ 0 := not_lt.mp h
    nlinarith
  have hlogn1 : (N : ℝ) ^ c ≤ log (n : ℝ) := h3.trans hlogn_low
  have hlogn_pos : 0 < log (n : ℝ) := by linarith
  have hloglog : c * log (N : ℝ) ≤ log (log (n : ℝ)) := by
    have h := Real.log_le_log (by linarith) hlogn1
    rwa [Real.log_rpow hNpos] at h
  rw [hω]
  calc c = (Nat.primeCounting N : ℝ)
        * (c * log (N : ℝ) / ((Nat.primeCounting N : ℝ) * log (N : ℝ))) := by
        field_simp
    _ ≤ (Nat.primeCounting N : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hkpos.le
        exact div_le_div₀ (le_trans (by positivity) hloglog) hloglog hlogn_pos hlogn_upp

/-- Lower bound: frequently `c ≤ ω n * (log log n / log n)` for every `0 ≤ c < 1`. -/
lemma lower_frequently (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ᶠ n : ℕ in atTop, c ≤ (ω n : ℝ) * (log (log n) / log n) := by
  rw [Filter.frequently_atTop]
  intro a
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hε0 : 0 < (log 2) ^ 2 / 4 := by positivity
  have hlo := (isLittleO_log_rpow_atTop (r := 1 - c) (by linarith)).bound hε0
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlo
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes a
  have hNp : p ≤ max p (max ⌈X0⌉₊ 2) := le_max_left _ _
  have hNX : X0 ≤ ((max p (max ⌈X0⌉₊ 2) : ℕ) : ℝ) := by
    calc X0 ≤ (⌈X0⌉₊ : ℝ) := Nat.le_ceil X0
      _ ≤ ((max p (max ⌈X0⌉₊ 2) : ℕ) : ℝ) := by
          exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : 2 ≤ max p (max ⌈X0⌉₊ 2) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q, ?_, ?_⟩
  · have hmem : p ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)) := Nat.mem_primesLE.mpr ⟨hNp, hp⟩
    have hdvd : p ∣ ∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q :=
      Finset.dvd_prod_of_mem (fun q => q) hmem
    have hpos : 0 < ∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q :=
      Finset.prod_pos (fun q hq => (Nat.mem_primesLE.mp hq).2.pos)
    exact hpa.trans (Nat.le_of_dvd hpos hdvd)
  · exact lower_main c hc0 _ hN2 _ rfl (hX0 _ hNX)

end E890

theorem OMA.solution : type_of% @Erdos890.erdos_890.variants.omega_limsup := by
  have hfun : (fun n : ℕ => (ω n : EReal) * ((log (log (n : ℝ)) : EReal) / (log (n : ℝ) : EReal)))
      = fun n : ℕ => (((ω n : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) : ℝ) : EReal) := by
    funext n
    rw [EReal.coe_mul, EReal.coe_div, EReal.coe_natCast]
  show limsup (fun n : ℕ => (ω n : EReal) * ((log (log (n : ℝ)) : EReal) / (log (n : ℝ) : EReal)))
    atTop = 1
  rw [hfun]
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨x, hx1, hxb⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hx1' : (1 : ℝ) < x := by exact_mod_cast hx1
    refine le_trans (Filter.limsup_le_of_le (h := ?_)) hxb.le
    filter_upwards [E890.upper_eventually x hx1'] with n hn
    exact_mod_cast hn
  · apply le_of_forall_lt_imp_le_of_dense
    intro b hb
    obtain ⟨x, hbx, hx1⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hx1' : x < 1 := by exact_mod_cast hx1
    have hfreq : ∃ᶠ n : ℕ in atTop, ((max x 0 : ℝ) : EReal)
        ≤ (((ω n : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) : ℝ) : EReal) := by
      refine (E890.lower_frequently (max x 0) (le_max_right _ _) (max_lt hx1' one_pos)).mono ?_
      intro n hn
      exact_mod_cast hn
    have hle : (x : EReal) ≤ ((max x 0 : ℝ) : EReal) := by
      exact_mod_cast le_max_left x 0
    exact le_trans hbx.le (le_trans hle (Filter.le_limsup_of_frequently_le hfreq))
