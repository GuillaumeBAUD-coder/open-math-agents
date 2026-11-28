import FormalConjectures.ErdosProblems.«587»

/-!
Reduction `Erdos587.erdos_587.variants.nguyen_vu.R1` of Erdős Problem 587 (Nguyen-Vu upper bound).
Credit: @B221393 (incorporating the divisor-core descent idea from @VestigeClub note #70592
and the quadratic-residue AP lift from @MechaNuggan note #59740).

`main` unconditionally proves:
1. The divisor-core descent (Nguyen-Vu Lemma 2.4) reducing an arbitrary square-sum-free subset
   `A ⊆ [1, N]` to a divisor-core subset `B ⊆ [1, N / p]` with `|A| ≤ 2 |B|` avoiding `p`-weighted
   square subset sums.
2. The modular quadratic-residue AP lift: any progression `a + q * j` (`0 ≤ j ≤ L`) with
   `a ≡ p * r^2 (mod q)` and `p * (2 * sqrt(a / p) + q) ≤ L` contains a `p`-weighted square.
3. The asymptotic bridge from `H1` (long subset-sum AP + reserved divisor-core pool) and `H2`
   (modular quadratic-residue hitting on the reserved pool) to `MaxNotSqSum N ≪ N^(1/3) (log N)^O`.
-/

namespace OMA.R_Erdos587_erdos_587_variants_nguyen_vu_R1

/-- Szemerédi-Vu / Nguyen-Vu long arithmetic progression extraction for divisor-core sets:
every sufficiently dense divisor-core subset `B ⊆ [1, N / p]` splits into disjoint `B₁, B₂ ⊆ B`
such that the nonempty subset sums of `B₁` cover an arithmetic progression `a₁ + q * j`
(`0 ≤ j ≤ L`) with `p * q ≪ (N / |B|) (log N)^c₂` and `L ≫ |B|² / (log N)^c₂`, while `B₂`
retains size at least `|B| / 4` and the divisor-core property up to a constant factor. -/
def H1 : Prop :=
  ∃ c₁ > (0 : ℝ), ∃ C₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∃ C₂ > (0 : ℝ),
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ p ∈ Finset.Icc 1 N,
        ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 (N / p) →
          (∀ d ≥ 2, B.card / (2 * (Nat.log 2 N + 1)) ≤
            (B.filter (fun b => ¬ d ∣ b)).card) →
          C₁ * Real.nthRoot 3 N * (N : ℝ).log ^ c₁ ≤ (B.card : ℝ) →
          ∃ B₁ B₂ : Finset ℕ, B₁ ⊆ B ∧ B₂ ⊆ B ∧ Disjoint B₁ B₂ ∧
            ∃ a₁ q L : ℕ, 1 ≤ q ∧
              (∀ j ≤ L, ∃ S₁ ⊆ B₁, S₁.Nonempty ∧ (∑ b ∈ S₁, b) = a₁ + q * j) ∧
              (p : ℝ) * (q : ℝ) ≤ C₂ * (N : ℝ) / (B.card : ℝ) * (N : ℝ).log ^ c₂ ∧
              (B.card : ℝ) ^ 2 / (C₂ * (N : ℝ).log ^ c₂) ≤ (L : ℝ) ∧
              (B.card : ℝ) / 4 ≤ (B₂.card : ℝ) ∧
              (∀ d ≥ 2, B₂.card / (8 * (Nat.log 2 N + 1)) ≤
                (B₂.filter (fun b => ¬ d ∣ b)).card)

/-- Nguyen-Vu modular quadratic-residue hitting on a divisor-core pool:
for any polynomial-log bound `p * q ≤ C₄ (N / |B₂|) (log N)^c₄`, every sufficiently dense
divisor-core pool `B₂ ⊆ [1, N / p]` contains a subset `S₂ ⊆ B₂` shifting any base `a₁`
into a `p`-weighted quadratic residue `p * r²` modulo `q`. -/
def H2 : Prop :=
  ∀ C₄ > (0 : ℝ), ∀ c₄ > (0 : ℝ),
    ∃ c₃ > (0 : ℝ), ∃ C₃ > (0 : ℝ),
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ p ∈ Finset.Icc 1 N,
          ∀ B₂ : Finset ℕ, B₂ ⊆ Finset.Icc 1 (N / p) →
            (∀ d ≥ 2, B₂.card / (8 * (Nat.log 2 N + 1)) ≤
              (B₂.filter (fun b => ¬ d ∣ b)).card) →
            C₃ * Real.nthRoot 3 N * (N : ℝ).log ^ c₃ ≤ (B₂.card : ℝ) →
            ∀ a₁ q : ℕ, 1 ≤ q →
              (p : ℝ) * (q : ℝ) ≤ C₄ * (N : ℝ) / (B₂.card : ℝ) * (N : ℝ).log ^ c₄ →
              ∃ S₂ ⊆ B₂, ∃ r : ℕ, (a₁ + ∑ b ∈ S₂, b) % q = (p * r ^ 2) % q

lemma divisor_core_descent (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    ∃ p ∈ Finset.Icc 1 N, ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 (N / p) ∧
      A.card ≤ 2 * B.card ∧
      (∀ d ≥ 2, B.card / (2 * (Nat.log 2 N + 1)) ≤
        (B.filter (fun b => ¬ d ∣ b)).card) ∧
      (∀ S ⊆ B, S.Nonempty → ∀ z : ℕ, (∑ b ∈ S, b) = p * z ^ 2 →
        ∃ S' ⊆ A, S'.Nonempty ∧ IsSquare (∑ a ∈ S', a)) := by
  let L : ℕ := Nat.log 2 N + 1
  let k : ℕ := A.card / (2 * L)
  let c : ℕ → ℕ := fun q => (A.filter (fun a => q ∣ a)).card
  let cand : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun q => A.card ≤ c q + k * Nat.log 2 q)
  have h1cand : 1 ∈ cand := by
    simp only [cand, c, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, hN⟩, ?_⟩
    have hfilt : A.filter (fun a => 1 ∣ a) = A :=
      Finset.filter_true_of_mem (fun a _ => one_dvd a)
    rw [hfilt, Nat.log_one_right, mul_zero, add_zero]
  have hcand_ne : cand.Nonempty := ⟨1, h1cand⟩
  let p : ℕ := cand.max' hcand_ne
  have hp_mem : p ∈ cand := Finset.max'_mem cand hcand_ne
  have hp_icc : p ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hp_mem).1
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp_icc).1
  have hpN : p ≤ N := (Finset.mem_Icc.mp hp_icc).2
  have hp_ineq : A.card ≤ c p + k * Nat.log 2 p := (Finset.mem_filter.mp hp_mem).2
  let Ap : Finset ℕ := A.filter (fun a => p ∣ a)
  let B : Finset ℕ := Ap.image (· / p)
  have hB_sub : B ⊆ Finset.Icc 1 (N / p) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    have haA : a ∈ A := (Finset.mem_filter.mp ha).1
    have hpa : p ∣ a := (Finset.mem_filter.mp ha).2
    have haIcc : a ∈ Finset.Icc 1 N := hA haA
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haIcc).1
    have haN : a ≤ N := (Finset.mem_Icc.mp haIcc).2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right haN⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hpa) (by omega)
  have hinj : Set.InjOn (· / p) (Ap : Set ℕ) := by
    intro a₁ ha₁ a₂ ha₂ heq
    have h1 : p ∣ a₁ := (Finset.mem_filter.mp ha₁).2
    have h2 : p ∣ a₂ := (Finset.mem_filter.mp ha₂).2
    have e1 : p * (a₁ / p) = a₁ := Nat.mul_div_cancel' h1
    have e2 : p * (a₂ / p) = a₂ := Nat.mul_div_cancel' h2
    dsimp only at heq
    rw [← e1, ← e2, heq]
  have hBcard : B.card = c p := Finset.card_image_of_injOn hinj
  have hA2B : A.card ≤ 2 * B.card := by
    have hlog_le : Nat.log 2 p ≤ L := le_trans (Nat.log_mono_right hpN) (Nat.le_succ _)
    have hmul1 : k * Nat.log 2 p ≤ k * L := Nat.mul_le_mul_left k hlog_le
    have hmul2 : 2 * (k * L) ≤ A.card := by
      have hdiv : 2 * L * k ≤ A.card := Nat.mul_div_le A.card (2 * L)
      linarith
    rw [hBcard]
    omega
  have hcore : ∀ d ≥ 2, B.card / (2 * L) ≤ (B.filter (fun b => ¬ d ∣ b)).card := by
    intro d hd
    have hB_le_A : B.card ≤ A.card := by
      rw [hBcard]
      exact Finset.card_filter_le A _
    have hdiv_le : B.card / (2 * L) ≤ k := Nat.div_le_div_right hB_le_A
    refine le_trans hdiv_le ?_
    have hfilt_eq : B.filter (fun b => d ∣ b) = (A.filter (fun a => p * d ∣ a)).image (· / p) := by
      ext b
      simp only [B, Ap, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ⟨haA, hpa⟩, rfl⟩, hdb⟩
        refine ⟨a, ⟨haA, ?_⟩, rfl⟩
        have hpd : p * d ∣ p * (a / p) := mul_dvd_mul_left p hdb
        rwa [Nat.mul_div_cancel' hpa] at hpd
      · rintro ⟨a, ⟨haA, hpda⟩, rfl⟩
        have hpa : p ∣ a := dvd_of_mul_right_dvd hpda
        refine ⟨⟨a, ⟨haA, hpa⟩, rfl⟩, ?_⟩
        rcases hpda with ⟨m, rfl⟩
        refine ⟨m, ?_⟩
        have : p * d * m = p * (d * m) := by ring
        rw [this, Nat.mul_div_right _ (by omega : 0 < p)]
    have hinj_pd : Set.InjOn (· / p) ((A.filter (fun a => p * d ∣ a)) : Set ℕ) := by
      intro a₁ ha₁ a₂ ha₂ heq
      have h1 : p ∣ a₁ := dvd_of_mul_right_dvd (Finset.mem_filter.mp ha₁).2
      have h2 : p ∣ a₂ := dvd_of_mul_right_dvd (Finset.mem_filter.mp ha₂).2
      dsimp only at heq
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
    have hcard_dvd : (B.filter (fun b => d ∣ b)).card = c (p * d) := by
      rw [hfilt_eq, Finset.card_image_of_injOn hinj_pd]
    have hsplit : (B.filter (fun b => d ∣ b)).card + (B.filter (fun b => ¬ d ∣ b)).card = B.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
      congr 1
      ext b
      by_cases hdb : d ∣ b <;> simp [hdb]
    by_cases h0 : c (p * d) = 0
    · have h2k : 2 * k ≤ A.card := by
        have h1L : 1 ≤ L := Nat.succ_le_succ (Nat.zero_le _)
        have hdiv : 2 * L * k ≤ A.card := Nat.mul_div_le A.card (2 * L)
        nlinarith
      omega
    · have hne_pd : (A.filter (fun a => p * d ∣ a)).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      rcases hne_pd with ⟨a, ha⟩
      have haA : a ∈ A := (Finset.mem_filter.mp ha).1
      have hpda : p * d ∣ a := (Finset.mem_filter.mp ha).2
      have haIcc : a ∈ Finset.Icc 1 N := hA haA
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp haIcc).1
      have haN : a ≤ N := (Finset.mem_Icc.mp haIcc).2
      have hpd_le_N : p * d ≤ N := le_trans (Nat.le_of_dvd (by omega) hpda) haN
      have hpd_gt : p < p * d := by nlinarith
      have hpd_not_cand : p * d ∉ cand := by
        intro hmem
        have hle : p * d ≤ p := Finset.le_max' cand (p * d) hmem
        omega
      have hpd_lt : c (p * d) + k * Nat.log 2 (p * d) < A.card := by
        by_contra hge
        push Not at hge
        exact hpd_not_cand (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, hpd_le_N⟩, hge⟩)
      have hlog_step : Nat.log 2 p + 1 ≤ Nat.log 2 (p * d) := by
        have h1 : Nat.log 2 (p * 2) = Nat.log 2 p + 1 :=
          Nat.log_mul_base (by norm_num) (by omega)
        rw [← h1]
        exact Nat.log_mono_right (Nat.mul_le_mul_left p hd)
      have hmul_step : k * (Nat.log 2 p + 1) ≤ k * Nat.log 2 (p * d) :=
        Nat.mul_le_mul_left k hlog_step
      have hlt_c : c (p * d) + k < c p := by nlinarith
      rw [hBcard] at hsplit
      omega
  have hlift : ∀ S ⊆ B, S.Nonempty → ∀ z : ℕ, (∑ b ∈ S, b) = p * z ^ 2 →
      ∃ S' ⊆ A, S'.Nonempty ∧ IsSquare (∑ a ∈ S', a) := by
    intro S hSB hSne z hsum
    refine ⟨S.image (p * ·), ?_, hSne.image _, ?_⟩
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, hbS, rfl⟩
      rcases Finset.mem_image.mp (hSB hbS) with ⟨a, haAp, rfl⟩
      have haA : a ∈ A := (Finset.mem_filter.mp haAp).1
      have hpa : p ∣ a := (Finset.mem_filter.mp haAp).2
      rwa [Nat.mul_div_cancel' hpa]
    · have hsum_img : (∑ a ∈ S.image (p * ·), a) = ∑ b ∈ S, p * b := by
        refine Finset.sum_image ?_
        intro x _ y _ hxy
        exact mul_left_cancel₀ (by omega : p ≠ 0) hxy
      rw [hsum_img, ← Finset.mul_sum, hsum]
      exact ⟨p * z, by ring⟩
  exact ⟨p, hp_icc, B, hB_sub, hA2B, hcore, hlift⟩

lemma weighted_square_in_mod_ap (p q a r L : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hmod : a % q = (p * r ^ 2) % q) (hL : p * (2 * Nat.sqrt (a / p) + q) ≤ L) :
    ∃ j ≤ L, ∃ t : ℕ, a + q * j = p * t ^ 2 := by
  let s : ℕ := Nat.sqrt (a / p)
  let u : ℕ := (r + q - (s + 1) % q) % q
  let t : ℕ := s + 1 + u
  have hu_lt : u < q := Nat.mod_lt _ (by omega)
  have ht_lo : s + 1 ≤ t := by omega
  have ht_hi : t ≤ s + q := by omega
  have ht_mod : t % q = r % q := by
    have hsm : (s + 1) % q < q := Nat.mod_lt _ (by omega)
    dsimp only [t, u]
    rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod_mod]
    have hcancel : (s + 1) % q + (r + q - (s + 1) % q) = r + q := by omega
    rw [hcancel, Nat.add_mod_right]
  have ha_lt : a < p * t ^ 2 := by
    have hsq1 : a / p < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (a / p)
    have hsq2 : (s + 1) * (s + 1) ≤ t ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul ht_lo ht_lo
    have hdiv : a / p + 1 ≤ t ^ 2 := by omega
    have ha_decomp : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
    have hrem : a % p < p := Nat.mod_lt a (by omega)
    nlinarith
  have hpt_mod : (p * t ^ 2) % q = a % q := by
    rw [hmod, sq, sq, Nat.mul_mod p (t * t), Nat.mul_mod t t, ht_mod, ← Nat.mul_mod r r,
      ← Nat.mul_mod p (r * r)]
  have hdvd : q ∣ p * t ^ 2 - a := by
    have h1 : a = q * (a / q) + a % q := (Nat.div_add_mod a q).symm
    have h2 : p * t ^ 2 = q * (p * t ^ 2 / q) + (p * t ^ 2) % q := (Nat.div_add_mod (p * t ^ 2) q).symm
    have hdiv_le : a / q ≤ p * t ^ 2 / q := Nat.div_le_div_right (le_of_lt ha_lt)
    refine ⟨p * t ^ 2 / q - a / q, ?_⟩
    have hmul_sub : q * (p * t ^ 2 / q - a / q) = q * (p * t ^ 2 / q) - q * (a / q) :=
      Nat.mul_sub_left_distrib q (p * t ^ 2 / q) (a / q)
    have hle_mul : q * (a / q) ≤ q * (p * t ^ 2 / q) := Nat.mul_le_mul_left q hdiv_le
    omega
  let j : ℕ := (p * t ^ 2 - a) / q
  have hqj : q * j = p * t ^ 2 - a := Nat.mul_div_cancel' hdvd
  have hsum : a + q * j = p * t ^ 2 := by
    rw [hqj]
    exact Nat.add_sub_of_le (le_of_lt ha_lt)
  have hj_le : j ≤ L := by
    have hs2 : s * s ≤ a / p := Nat.sqrt_le (a / p)
    have hps2 : p * (s * s) ≤ a := by
      have h1 : p * (a / p) ≤ a := Nat.mul_div_le a p
      nlinarith
    have ht2 : t ^ 2 ≤ (s + q) * (s + q) := by
      rw [sq]
      exact Nat.mul_le_mul ht_hi ht_hi
    have hq_bound : q * j ≤ q * (p * (2 * s + q)) := by
      rw [hqj]
      nlinarith
    have hj_bound : j ≤ p * (2 * s + q) := Nat.le_of_mul_le_mul_left hq_bound (by omega)
    exact le_trans hj_bound hL
  exact ⟨j, hj_le, t, hsum⟩

theorem main : H1 → H2 → type_of% @Erdos587.erdos_587.variants.nguyen_vu := by
  intro h1 h2
  rcases h1 with ⟨c₁, hc₁, C₁, hC₁, c₂, hc₂, C₂, hC₂, hev1⟩
  rcases h2 C₂ hC₂ c₂ hc₂ with ⟨c₃, hc₃, C₃, hC₃, hev2⟩
  let O : ℕ := Nat.ceil (max c₁ (max c₃ c₂)) + 1
  let O' : ℝ := max C₁ (max (4 * C₃) (4 * C₂ + 4))
  have hO_pos : 0 < O := Nat.succ_pos _
  have hO_ge_max : max c₁ (max c₃ c₂) ≤ (O : ℝ) := by
    have h1 : max c₁ (max c₃ c₂) ≤ (Nat.ceil (max c₁ (max c₃ c₂)) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (max c₁ (max c₃ c₂)) : ℝ) ≤ (O : ℝ) := by exact_mod_cast Nat.le_succ _
    exact le_trans h1 h2
  have hO'_pos : 0 < O' := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have h2O'_pos : 0 < 2 * O' := by linarith
  refine ⟨O, hO_pos, 2 * O', h2O'_pos, ?_⟩
  have hev_log : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ (N : ℝ).log := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with N hN
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : Real.exp 1 ≤ (N : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    have hle := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at hle
  filter_upwards [hev1, hev2, hev_log, Filter.eventually_ge_atTop (3 : ℕ)] with N hN1 hN2 hlog1 hN3
  have hN1_nat : 1 ≤ N := by omega
  have hR_nonneg : 0 ≤ Real.nthRoot 3 (N : ℝ) := by
    rw [Real.nthRoot_of_nonneg (Nat.cast_nonneg N)]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hR_cube : Real.nthRoot 3 (N : ℝ) ^ 3 = (N : ℝ) :=
    Real.pow_nthRoot (N : ℝ) (Or.inr (by decide))
  have hlogO_eq : (N : ℝ).log ^ (O : ℝ) = (N : ℝ).log ^ O := Real.rpow_natCast (N : ℝ).log O
  have hlogO_pos : 0 < (N : ℝ).log ^ O := pow_pos (by linarith) O
  have hlogc2_pos : 0 < (N : ℝ).log ^ c₂ := Real.rpow_pos_of_pos (by linarith) c₂
  have hbound_nonneg : 0 ≤ 2 * O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O := by positivity
  have hA_bound : ∀ A ∈ (Finset.Icc 1 N).powerset.filter
      (fun A => ∀ S ⊆ A, S ≠ ⊥ → ¬ IsSquare (∑ n ∈ S, n)),
      (A.card : ℝ) ≤ 2 * O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O := by
    intro A hAmem
    have hAsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp hAmem).1
    have hAnosq : ∀ S ⊆ A, S ≠ ⊥ → ¬ IsSquare (∑ n ∈ S, n) := (Finset.mem_filter.mp hAmem).2
    by_contra hgt
    push Not at hgt
    rcases divisor_core_descent N hN1_nat A hAsub with
      ⟨p, hp_icc, B, hB_sub, hA2B, hBcore, hBlift⟩
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp_icc).1
    have hB_ge : O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O ≤ (B.card : ℝ) := by
      have hA2B_real : (A.card : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast hA2B
      linarith
    have hlog_c1 : (N : ℝ).log ^ c₁ ≤ (N : ℝ).log ^ O := by
      rw [← hlogO_eq]
      exact Real.rpow_le_rpow_of_exponent_le hlog1 (le_trans (le_max_left _ _) hO_ge_max)
    have hlog_c3 : (N : ℝ).log ^ c₃ ≤ (N : ℝ).log ^ O := by
      rw [← hlogO_eq]
      exact Real.rpow_le_rpow_of_exponent_le hlog1
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hO_ge_max)
    have hlog_c2 : (N : ℝ).log ^ c₂ ≤ (N : ℝ).log ^ O := by
      rw [← hlogO_eq]
      exact Real.rpow_le_rpow_of_exponent_le hlog1
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hO_ge_max)
    have hB_H1 : C₁ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₁ ≤ (B.card : ℝ) := by
      have hC1_le : C₁ ≤ O' := le_max_left _ _
      have h1 : C₁ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₁ ≤
          O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O := by
        have hstep1 : C₁ * Real.nthRoot 3 (N : ℝ) ≤ O' * Real.nthRoot 3 (N : ℝ) :=
          mul_le_mul_of_nonneg_right hC1_le hR_nonneg
        have hstep2 : C₁ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₁ ≤
            O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₁ :=
          mul_le_mul_of_nonneg_right hstep1 (Real.rpow_nonneg (by linarith) _)
        have hstep3 : O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₁ ≤
            O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O :=
          mul_le_mul_of_nonneg_left hlog_c1 (mul_nonneg (le_of_lt hO'_pos) hR_nonneg)
        exact le_trans hstep2 hstep3
      exact le_trans h1 hB_ge
    rcases hN1 p hp_icc B hB_sub hBcore hB_H1 with
      ⟨B₁, B₂, hB₁B, hB₂B, hdisj, a₁, q, L, hq1, hAP, hpq_le, hL_ge, hB₂_card, hB₂_core⟩
    have hB₂_sub : B₂ ⊆ Finset.Icc 1 (N / p) := Finset.Subset.trans hB₂B hB_sub
    have hB₂_H2 : C₃ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ ≤ (B₂.card : ℝ) := by
      have h4C3_le : 4 * C₃ ≤ O' := le_trans (le_max_left _ _) (le_max_right _ _)
      have h1 : 4 * C₃ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ ≤ (B.card : ℝ) := by
        have hs1 : 4 * C₃ * Real.nthRoot 3 (N : ℝ) ≤ O' * Real.nthRoot 3 (N : ℝ) :=
          mul_le_mul_of_nonneg_right h4C3_le hR_nonneg
        have hs2 : 4 * C₃ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ ≤
            O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ :=
          mul_le_mul_of_nonneg_right hs1 (Real.rpow_nonneg (by linarith) _)
        have hs3 : O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ ≤
            O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O :=
          mul_le_mul_of_nonneg_left hlog_c3 (mul_nonneg (le_of_lt hO'_pos) hR_nonneg)
        exact le_trans (le_trans hs2 hs3) hB_ge
      linarith
    have hB₂_pos : (0 : ℝ) < (B₂.card : ℝ) := by
      have hR_pos : 0 < Real.nthRoot 3 (N : ℝ) := by
        rw [Real.nthRoot_of_nonneg (Nat.cast_nonneg N)]
        exact Real.rpow_pos_of_pos (by positivity) _
      have hlogc3_pos : 0 < (N : ℝ).log ^ c₃ := Real.rpow_pos_of_pos (by linarith) c₃
      have hpos : 0 < C₃ * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ c₃ := by positivity
      linarith
    have hB₂_le_B : (B₂.card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hB₂B
    have hB_pos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le hB₂_pos hB₂_le_B
    have hpq_B₂ : (p : ℝ) * (q : ℝ) ≤ C₂ * (N : ℝ) / (B₂.card : ℝ) * (N : ℝ).log ^ c₂ := by
      have hdiv : C₂ * (N : ℝ) / (B.card : ℝ) ≤ C₂ * (N : ℝ) / (B₂.card : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hB₂_pos hB₂_le_B
      exact le_trans hpq_le (mul_le_mul_of_nonneg_right hdiv (le_of_lt hlogc2_pos))
    rcases hN2 p hp_icc B₂ hB₂_sub hB₂_core hB₂_H2 a₁ q hq1 hpq_B₂ with ⟨S₂, hS₂B₂, r, hmod⟩
    let a : ℕ := a₁ + ∑ b ∈ S₂, b
    have ha_le : p * a ≤ B.card * N := by
      rcases hAP 0 (Nat.zero_le L) with ⟨S₁₀, hS₁₀B₁, _, hS₁₀sum⟩
      have hdisj0 : Disjoint S₁₀ S₂ := Disjoint.mono hS₁₀B₁ hS₂B₂ hdisj
      have hunion_sub : S₁₀ ∪ S₂ ⊆ B :=
        Finset.union_subset (Finset.Subset.trans hS₁₀B₁ hB₁B) (Finset.Subset.trans hS₂B₂ hB₂B)
      have ha_eq : a = ∑ b ∈ S₁₀ ∪ S₂, b := by
        rw [Finset.sum_union hdisj0, hS₁₀sum, mul_zero, add_zero]
      have hsum_le : (∑ b ∈ S₁₀ ∪ S₂, b) ≤ (S₁₀ ∪ S₂).card * (N / p) := by
        calc ∑ b ∈ S₁₀ ∪ S₂, b
            ≤ ∑ _b ∈ S₁₀ ∪ S₂, (N / p) := by
              refine Finset.sum_le_sum ?_
              intro b hb
              exact (Finset.mem_Icc.mp (hB_sub (hunion_sub hb))).2
          _ = (S₁₀ ∪ S₂).card * (N / p) := by simp
      have hcard_le : (S₁₀ ∪ S₂).card ≤ B.card := Finset.card_le_card hunion_sub
      have ha_le_BNp : a ≤ B.card * (N / p) := le_trans (by rw [ha_eq]; exact hsum_le)
        (Nat.mul_le_mul_right _ hcard_le)
      have hp_div : p * (N / p) ≤ N := Nat.mul_div_le N p
      calc p * a ≤ p * (B.card * (N / p)) := Nat.mul_le_mul_left p ha_le_BNp
        _ = B.card * (p * (N / p)) := by ring
        _ ≤ B.card * N := Nat.mul_le_mul_left B.card hp_div
    have hM3 : 16 * C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 ≤ (B.card : ℝ) ^ 3 := by
      have h4C2_le : 4 * C₂ + 4 ≤ O' := le_trans (le_max_right _ _) (le_max_right _ _)
      have hO'3 : 16 * C₂ ^ 2 ≤ O' ^ 3 := by
        have hsq : 16 * C₂ ^ 2 ≤ O' ^ 2 := by nlinarith only [hC₂, h4C2_le]
        have hge1 : (1 : ℝ) ≤ O' := by linarith only [hC₂, h4C2_le]
        nlinarith only [hsq, hge1, sq_nonneg C₂]
      have hlog_le3 : ((N : ℝ).log ^ c₂) ^ 2 ≤ ((N : ℝ).log ^ O) ^ 3 := by
        have h1 : ((N : ℝ).log ^ c₂) ^ 2 ≤ ((N : ℝ).log ^ O) ^ 2 := by
          nlinarith only [hlog_c2, hlogc2_pos, hlogO_pos]
        have h2 : (1 : ℝ) ≤ (N : ℝ).log ^ O := one_le_pow₀ hlog1
        nlinarith only [h1, h2, hlogO_pos]
      have hpow : (O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O) ^ 3 ≤ (B.card : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hB_ge 3
      have hexp3 : (O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O) ^ 3 =
          O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ O) ^ 3 := by
        calc (O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O) ^ 3
            = O' ^ 3 * Real.nthRoot 3 (N : ℝ) ^ 3 * ((N : ℝ).log ^ O) ^ 3 := by ring
          _ = O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ O) ^ 3 := by rw [hR_cube]
      have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hstep : 16 * C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 ≤
          O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ O) ^ 3 := by
        have ha1 : 16 * C₂ ^ 2 * (N : ℝ) ≤ O' ^ 3 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hO'3 hN_nonneg
        have ha2 : 16 * C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 ≤
            O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 :=
          mul_le_mul_of_nonneg_right ha1 (sq_nonneg _)
        have ha3 : O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 ≤
            O' ^ 3 * (N : ℝ) * ((N : ℝ).log ^ O) ^ 3 :=
          mul_le_mul_of_nonneg_left hlog_le3 (by positivity)
        exact le_trans ha2 ha3
      linarith only [hstep, hexp3, hpow]
    have hdenom_pos : 0 < 2 * C₂ * (N : ℝ).log ^ c₂ := by positivity
    have hterm1 : 2 * (p : ℝ) * (Nat.sqrt (a / p) : ℝ) ≤
        (B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂) := by
      have hsq_nat : p * (p * (Nat.sqrt (a / p) * Nat.sqrt (a / p))) ≤ B.card * N := by
        have h1 : Nat.sqrt (a / p) * Nat.sqrt (a / p) ≤ a / p := Nat.sqrt_le (a / p)
        have h2 : p * (a / p) ≤ a := Nat.mul_div_le a p
        have h3 : p * (Nat.sqrt (a / p) * Nat.sqrt (a / p)) ≤ a :=
          le_trans (Nat.mul_le_mul_left p h1) h2
        exact le_trans (Nat.mul_le_mul_left p h3) ha_le
      have hsq_real : (2 * (p : ℝ) * (Nat.sqrt (a / p) : ℝ)) ^ 2 ≤ 4 * (B.card : ℝ) * (N : ℝ) := by
        have hcast : (p : ℝ) * ((p : ℝ) * ((Nat.sqrt (a / p) : ℝ) * (Nat.sqrt (a / p) : ℝ))) ≤
            (B.card : ℝ) * (N : ℝ) := by exact_mod_cast hsq_nat
        linarith only [hcast]
      have hrhs_sq : 4 * (B.card : ℝ) * (N : ℝ) ≤
          ((B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂)) ^ 2 := by
        rw [div_pow, le_div_iff₀ (sq_pos_of_pos hdenom_pos)]
        have hmul : 4 * (B.card : ℝ) * (N : ℝ) * (2 * C₂ * (N : ℝ).log ^ c₂) ^ 2 =
            (B.card : ℝ) * (16 * C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2) := by ring
        rw [hmul]
        have hB4 : (B.card : ℝ) * (B.card : ℝ) ^ 3 = ((B.card : ℝ) ^ 2) ^ 2 := by ring
        rw [← hB4]
        exact mul_le_mul_of_nonneg_left hM3 (le_of_lt hB_pos)
      have hsq_le : (2 * (p : ℝ) * (Nat.sqrt (a / p) : ℝ)) ^ 2 ≤
          ((B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂)) ^ 2 := le_trans hsq_real hrhs_sq
      have h1_nn : 0 ≤ 2 * (p : ℝ) * (Nat.sqrt (a / p) : ℝ) := by positivity
      have h2_nn : 0 ≤ (B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂) :=
        div_nonneg (sq_nonneg _) (le_of_lt hdenom_pos)
      nlinarith only [hsq_le, h1_nn, h2_nn]
    have hterm2 : (p : ℝ) * (q : ℝ) ≤ (B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂) := by
      refine le_trans hpq_le ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hB_pos hdenom_pos]
      have hlhs : C₂ * (N : ℝ) * (N : ℝ).log ^ c₂ * (2 * C₂ * (N : ℝ).log ^ c₂) =
          2 * C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 := by ring
      have hrhs : (B.card : ℝ) ^ 2 * (B.card : ℝ) = (B.card : ℝ) ^ 3 := by ring
      rw [hlhs, hrhs]
      have hpos_term : 0 ≤ C₂ ^ 2 * (N : ℝ) * ((N : ℝ).log ^ c₂) ^ 2 := by positivity
      linarith only [hM3, hpos_term]
    have hL_real : ((p * (2 * Nat.sqrt (a / p) + q) : ℕ) : ℝ) ≤ (L : ℝ) := by
      have hadd : (B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂) +
          (B.card : ℝ) ^ 2 / (2 * C₂ * (N : ℝ).log ^ c₂) =
          (B.card : ℝ) ^ 2 / (C₂ * (N : ℝ).log ^ c₂) := by
        field_simp
        ring
      push_cast
      linarith only [hterm1, hterm2, hadd, hL_ge]
    have hL_nat : p * (2 * Nat.sqrt (a / p) + q) ≤ L := by exact_mod_cast hL_real
    rcases weighted_square_in_mod_ap p q a r L hp1 hq1 hmod hL_nat with ⟨j, hjL, t, hsq_eq⟩
    rcases hAP j hjL with ⟨S₁, hS₁B₁, hS₁ne, hS₁sum⟩
    have hdisj_S : Disjoint S₁ S₂ := Disjoint.mono hS₁B₁ hS₂B₂ hdisj
    have hS_sub : S₁ ∪ S₂ ⊆ B :=
      Finset.union_subset (Finset.Subset.trans hS₁B₁ hB₁B) (Finset.Subset.trans hS₂B₂ hB₂B)
    have hS_ne : (S₁ ∪ S₂).Nonempty := hS₁ne.mono Finset.subset_union_left
    have hS_sum : (∑ b ∈ S₁ ∪ S₂, b) = p * t ^ 2 := by
      rw [Finset.sum_union hdisj_S, hS₁sum]
      dsimp only [a] at hsq_eq
      omega
    rcases hBlift (S₁ ∪ S₂) hS_sub hS_ne t hS_sum with ⟨S', hS'A, hS'ne, hS'sq⟩
    exact hAnosq S' hS'A (Finset.nonempty_iff_ne_empty.mp hS'ne) hS'sq
  unfold Erdos587.MaxNotSqSum
  have hsup_nat : ∀ A ∈ (Finset.Icc 1 N).powerset.filter
      (fun A => ∀ S ⊆ A, S ≠ ⊥ → ¬ IsSquare (∑ n ∈ S, n)),
      A.card ≤ Nat.floor (2 * O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O) := by
    intro A hAmem
    exact Nat.le_floor (hA_bound A hAmem)
  have hle_floor : ((Finset.Icc 1 N).powerset.filter
      (fun A => ∀ S ⊆ A, S ≠ ⊥ → ¬ IsSquare (∑ n ∈ S, n))).sup Finset.card ≤
      Nat.floor (2 * O' * Real.nthRoot 3 (N : ℝ) * (N : ℝ).log ^ O) :=
    Finset.sup_le hsup_nat
  exact le_trans (by exact_mod_cast hle_floor) (Nat.floor_le hbound_nonneg)

end OMA.R_Erdos587_erdos_587_variants_nguyen_vu_R1
