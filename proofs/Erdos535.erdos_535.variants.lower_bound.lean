import FormalConjectures.ErdosProblems.«535»

-- Problem: Erdős Problem 535 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/535.lean:100 (declaration Erdos535.erdos_535.variants.lower_bound)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős 535: a large set with no three elements of constant pairwise gcd

Erdős's construction (1964). Split the first `2m` primes into `m` pairs and let `A` be the `2^m`
products that take exactly one prime from each pair. If three distinct elements had the same
pairwise gcd `d`, pick a pair where the first two differ; the third agrees with one of them
there, so that prime divides `d`, hence divides the remaining element, which is impossible.
With `y = ⌊log N / log 4⌋` and `m = π(y)/2`, every element divides `y#`, so is at most
`4^y ≤ N`, and Chebyshev's bound `π(y) ≫ y / log y` gives `2^m ≥ N^{(1/20)/log log N}`.
-/

open Filter Real

namespace OMA535

/-- The atoms: the `(2 i + b)`-th prime. -/
noncomputable def q (i : ℕ) (b : Bool) : ℕ := Nat.nth Nat.Prime (2 * i + b.toNat)

lemma q_prime (i : ℕ) (b : Bool) : (q i b).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

lemma q_inj {i j : ℕ} {b c : Bool} (h : q i b = q j c) : i = j ∧ b = c := by
  have h2 : 2 * i + b.toNat = 2 * j + c.toNat := Nat.nth_injective Nat.infinite_setOf_prime h
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hij : i = j := by omega
  subst hij
  refine ⟨rfl, ?_⟩
  cases b <;> cases c <;> simp_all

/-- The element attached to a choice function. -/
noncomputable def a {m : ℕ} (σ : Fin m → Bool) : ℕ :=
  ∏ p ∈ Finset.univ.image (fun i : Fin m => q i (σ i)), p

lemma q_dvd_a {m : ℕ} (σ : Fin m → Bool) (i : Fin m) : q i (σ i) ∣ a σ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

lemma eq_of_q_dvd_a {m : ℕ} (σ : Fin m → Bool) (i : Fin m) (b : Bool)
    (h : q i b ∣ a σ) : σ i = b := by
  have hp : _root_.Prime (q i b) := (q_prime i b).prime
  obtain ⟨p, hp', hdvd⟩ := (Prime.dvd_finset_prod_iff hp _).1 h
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp'
  have := (Nat.prime_dvd_prime_iff_eq (q_prime i b) (q_prime j (σ j))).1 hdvd
  obtain ⟨h1, h2⟩ := q_inj this
  have : i = j := Fin.ext h1
  subst this
  exact h2.symm

lemma a_injective {m : ℕ} : Function.Injective (a (m := m)) := by
  intro σ τ h
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have := eq_of_q_dvd_a τ i (σ i) (h ▸ q_dvd_a σ i)
  exact hi this.symm

lemma a_pos {m : ℕ} (σ : Fin m → Bool) : 0 < a σ :=
  Finset.prod_pos fun p hp => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    exact (q_prime _ _).pos

lemma a_le {m y : ℕ} (hm : 2 * m ≤ Nat.primeCounting y) (σ : Fin m → Bool) :
    a σ ≤ 4 ^ y := by
  refine le_trans ?_ (primorial_le_4_pow y)
  apply Nat.le_of_dvd (primorial_pos y)
  unfold primorial a
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.nth_lt_of_lt_count ?_, q_prime _ _⟩
  have : 2 * (j : ℕ) + (σ j).toNat < Nat.primeCounting y := by
    have := j.isLt; cases σ j <;> simp <;> omega
  exact this

lemma no_sunflower {m : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.univ.image (a (m := m))) (hc : S.card = 3) :
    ¬ (∃ d, (S : Set ℕ).Pairwise fun x y => Nat.gcd x y = d) := by
  rintro ⟨d, hd⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hc
  have hx : x ∈ Finset.univ.image (a (m := m)) := hS (by simp)
  have hy : y ∈ Finset.univ.image (a (m := m)) := hS (by simp)
  have hz : z ∈ Finset.univ.image (a (m := m)) := hS (by simp)
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.1 hz
  have hxy' : Nat.gcd (a σ) (a τ) = d := hd (by simp) (by simp) hxy
  have hxz' : Nat.gcd (a σ) (a ρ) = d := hd (by simp) (by simp) hxz
  have hyz' : Nat.gcd (a τ) (a ρ) = d := hd (by simp) (by simp) hyz
  have hne : σ ≠ τ := fun h => hxy (h ▸ rfl)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hρ : ρ i = σ i ∨ ρ i = τ i := by
    cases h1 : ρ i <;> cases h2 : σ i <;> cases h3 : τ i <;> simp_all
  rcases hρ with h | h
  · have h1 : q i (σ i) ∣ d := hxz' ▸ Nat.dvd_gcd (q_dvd_a σ i) (h ▸ q_dvd_a ρ i)
    have h2 : q i (σ i) ∣ a τ := (hxy' ▸ h1).trans (Nat.gcd_dvd_right _ _)
    exact hi (eq_of_q_dvd_a τ i _ h2).symm
  · have h1 : q i (τ i) ∣ d := hyz' ▸ Nat.dvd_gcd (q_dvd_a τ i) (h ▸ q_dvd_a ρ i)
    have h2 : q i (τ i) ∣ a σ := (hxy' ▸ h1).trans (Nat.gcd_dvd_left _ _)
    exact hi (eq_of_q_dvd_a σ i _ h2)

lemma two_pow_le_f {m y N : ℕ} (hm : 2 * m ≤ Nat.primeCounting y) (hN : 4 ^ y ≤ N) :
    2 ^ m ≤ Erdos535.f 3 N := by
  unfold Erdos535.f
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  · refine ⟨Finset.univ.image (a (m := m)), ?_, fun S hS hc => no_sunflower S hS hc, ?_⟩
    · intro x hx
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_Icc.2 ⟨a_pos σ, (a_le hm σ).trans hN⟩
    · rw [Finset.card_image_of_injective _ a_injective]
      simp


lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at this
  linarith

/-- The analytic heart: with `y = ⌊log N / log 4⌋` and `m = π(y)/2`, `m log 2 ≥ (1/20) log N / log log N`. -/
lemma key {L : ℝ} (hL : 10000 ≤ L) (y : ℕ) (hy1 : (y : ℝ) ≤ L / Real.log 4)
    (hy2 : L / Real.log 4 < y + 1) (m : ℕ) (hm : Nat.primeCounting y ≤ 2 * m + 1) :
    L * (1 / 20) / Real.log L ≤ m * Real.log 2 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl4 : 0 < Real.log 4 := by rw [l4]; linarith
  have hY0 : (0:ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
  have hY1 : (y : ℝ) * Real.log 4 ≤ L := by rwa [le_div_iff₀ hl4] at hy1
  have hY2 : L < ((y : ℝ) + 1) * Real.log 4 := by rwa [div_lt_iff₀ hl4] at hy2
  rw [l4] at hY1 hY2
  have hA : (y : ℝ) ≤ (y : ℝ) * (2 * Real.log 2) := by nlinarith
  have hYL : (y : ℝ) ≤ L := by linarith
  have hB : ((y : ℝ) + 1) * (2 * Real.log 2) ≤ ((y : ℝ) + 1) * 1.3863 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hYlow : L / 1.3863 - 1 ≤ (y : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]; linarith
  have hYbig : 7000 ≤ (y : ℝ) := by linarith
  have hYpos : 0 < (y : ℝ) := by linarith
  have hGpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hHpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hHG : Real.log (y : ℝ) ≤ Real.log L := Real.log_le_log hYpos hYL
  have hpi := Chebyshev.pi_ge y
  have hP : (y : ℝ) * Real.log 2 - Real.log ((y : ℝ) + 1) ≤
      (Nat.primeCounting y : ℝ) * Real.log (y : ℝ) := by
    rwa [div_le_iff₀ hHpos] at hpi
  have hs := log_le_two_sqrt (by linarith : (0:ℝ) ≤ (y : ℝ) + 1)
  have hs1 : Real.sqrt ((y : ℝ) + 1) ≤ (y : ℝ) / 10 :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hC : (y : ℝ) * 0.693 ≤ (y : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) hY0
  have hnum : L / 5 ≤ (y : ℝ) * Real.log 2 - Real.log ((y : ℝ) + 1) := by linarith
  have hP0 : (0:ℝ) ≤ (Nat.primeCounting y : ℝ) := Nat.cast_nonneg _
  have hD : (Nat.primeCounting y : ℝ) * Real.log (y : ℝ) ≤
      (Nat.primeCounting y : ℝ) * Real.log L := mul_le_mul_of_nonneg_left hHG hP0
  have hmR : (Nat.primeCounting y : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).2 hm; push_cast at this; exact this
  have hE : (Nat.primeCounting y : ℝ) * Real.log L ≤ (2 * (m : ℝ) + 1) * Real.log L :=
    mul_le_mul_of_nonneg_right hmR hGpos.le
  have hg := log_le_two_sqrt (by linarith : (0:ℝ) ≤ L)
  have hg1 : Real.sqrt L ≤ L / 50 := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hG : Real.log L ≤ L / 25 := by linarith
  have h2 : 0.08 * L ≤ (m : ℝ) * Real.log L := by nlinarith
  have h3 : 0.693 * (0.08 * L) ≤ Real.log 2 * ((m : ℝ) * Real.log L) :=
    mul_le_mul (by linarith) h2 (by positivity) (by linarith)
  rw [div_le_iff₀ hGpos]
  nlinarith

theorem lower : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) ≤ (Erdos535.f 3 N : ℝ) := by
  refine ⟨1 / 20, by norm_num, ?_⟩
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 10000] with N hN
  set L := Real.log (N : ℝ) with hLdef
  have hNpos : (0:ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [hLdef, this, Real.log_zero] at hN
    linarith
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set y : ℕ := ⌊L / Real.log 4⌋₊
  have hy1 : (y : ℝ) ≤ L / Real.log 4 := Nat.floor_le (by positivity)
  have hy2 : L / Real.log 4 < y + 1 := Nat.lt_floor_add_one _
  set m : ℕ := Nat.primeCounting y / 2
  have hm1 : 2 * m ≤ Nat.primeCounting y := Nat.mul_div_le _ _
  have hm2 : Nat.primeCounting y ≤ 2 * m + 1 := by omega
  have h4 : 4 ^ y ≤ N := by
    have : ((4:ℕ) : ℝ) ^ y ≤ N := by
      rw [← Real.exp_log hNpos, ← Real.exp_log (by positivity : (0:ℝ) < ((4:ℕ):ℝ) ^ y),
        Real.exp_le_exp, Real.log_pow]
      push_cast
      rwa [le_div_iff₀ hl4] at hy1
    exact_mod_cast this
  have hf := two_pow_le_f hm1 h4
  calc (N : ℝ) ^ ((1:ℝ) / 20 / Real.log L)
      = Real.exp (L * (1 / 20 / Real.log L)) := by rw [Real.rpow_def_of_pos hNpos]
    _ ≤ Real.exp (m * Real.log 2) := by
        rw [Real.exp_le_exp]
        have := key hN y hy1 hy2 m hm2
        calc L * (1 / 20 / Real.log L) = L * (1 / 20) / Real.log L := by ring
          _ ≤ _ := this
    _ = (2 : ℝ) ^ m := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ ≤ (Erdos535.f 3 N : ℝ) := by exact_mod_cast hf

end OMA535

theorem OMA.solution : type_of% @Erdos535.erdos_535.variants.lower_bound := by
  exact OMA535.lower
