import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.GCDMonoid.Finset

/-!
Proof of `LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R1.H1`
(the Lonely Runner Conjecture for 6 runners / `k = 5` positive integer speeds).

Formalizes Jérôme Renault (2004), *View-obstruction: a shorter proof for 6 lonely runners*,
Discrete Mathematics 287, 93-101, combined with the unconditional 5-runner (`k = 4`) theorem
via `5`-adic prime filtering (Bohman-Holzman-Kleitman 2001 / Barajas-Serra 2008).

Credit: @paynebrowning
-/

namespace LRCBaseFour
noncomputable section


private lemma unitAddCircle_dist_neg (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs_single (x : ℝ) :
    dist ((|x| : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, unitAddCircle_dist_neg]

private lemma unitAddCircle_dist_eq_abs_of_lt_half {x : ℝ} (hx : |x| < 1 / 2) :
    dist (x : UnitAddCircle) 0 = |x| := by
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hround_zero : round x = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(round x : ℝ)| := by
      have hint : (1 : ℤ) ≤ |round x| := Int.one_le_abs hne
      exact_mod_cast hint
    have h2 : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have h3 : |(round x : ℝ)| ≤ |x - (round x : ℝ)| + |x| := by
      calc
        |(round x : ℝ)| = |((round x : ℝ) - x) + x| := by ring_nf
        _ ≤ |(round x : ℝ) - x| + |x| := abs_add_le _ _
        _ = |x - (round x : ℝ)| + |x| := by rw [abs_sub_comm]
    linarith
  rw [hround_zero, Int.cast_zero, sub_zero]

private lemma unitAddCircle_int_cast_eq_zero (z : ℤ) :
    (((z : ℝ) : UnitAddCircle)) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

private lemma unitAddCircle_dist_ge_of_Icc (x δ : ℝ) (k : ℤ)
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  rw [ge_iff_le, dist_zero_right, UnitAddCircle.norm_eq]
  set m : ℤ := round x
  rcases le_or_gt m k with hmk | hkm
  · have hmk' : (m : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hmk
    have hle : δ ≤ x - (m : ℝ) := by linarith
    exact hle.trans (le_abs_self _)
  · have hkm1 : k + 1 ≤ m := Int.add_one_le_iff.mpr hkm
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm1
    have hle : δ ≤ -(x - (m : ℝ)) := by linarith
    exact hle.trans (neg_le_abs _)

private lemma unitAddCircle_dist_ge_of_Icc_zero (x δ : ℝ)
    (h1 : δ ≤ x) (h2 : x ≤ 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  refine unitAddCircle_dist_ge_of_Icc x δ 0 ?_ ?_
  · simp [h1]
  · simp [h2]


private lemma unitAddCircle_dist_ge_of_mod_Icc {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (lam w : ℕ) (hlo : N ≤ p * ((lam * w) % N)) (hhi : p * ((lam * w) % N) ≤ (p - 1) * N) :
    dist (((((lam : ℝ) / (N : ℝ)) * (w : ℝ) : ℝ)) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let q_nat : ℕ := (lam * w) / N
  let r_nat : ℕ := (lam * w) % N
  have hdiv : N * q_nat + r_nat = lam * w := Nat.div_add_mod (lam * w) N
  have hdiv_real : (N : ℝ) * (q_nat : ℝ) + (r_nat : ℝ) = (lam : ℝ) * (w : ℝ) := by
    exact_mod_cast hdiv
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hx_eq : ((lam : ℝ) / (N : ℝ)) * (w : ℝ) = ((q_nat : ℤ) : ℝ) + (r_nat : ℝ) / (N : ℝ) := by
    push_cast
    field_simp [ne_of_gt hN_pos]
    linarith
  have hlo_real : (N : ℝ) ≤ (p : ℝ) * (r_nat : ℝ) := by exact_mod_cast hlo
  have hhi_real : (p : ℝ) * (r_nat : ℝ) ≤ ((p - 1 : ℕ) : ℝ) * (N : ℝ) := by exact_mod_cast hhi
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hp1] at hhi_real
  refine unitAddCircle_dist_ge_of_Icc _ (1 / (p : ℝ)) (q_nat : ℤ) ?_ ?_
  · rw [hx_eq]
    have h1 : 1 / (p : ℝ) ≤ (r_nat : ℝ) / (N : ℝ) := by
      rw [div_le_div_iff₀ hp_pos hN_pos]
      linarith
    linarith
  · rw [hx_eq]
    have h2 : (r_nat : ℝ) / (N : ℝ) ≤ 1 - 1 / (p : ℝ) := by
      have hsub : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
        field_simp [ne_of_gt hp_pos]
      rw [hsub, div_le_div_iff₀ hN_pos hp_pos]
      linarith
    linarith

private lemma lrc_small_divisor_sieve {k j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k + 1)
    (w : Fin k → ℕ) (hnot_dvd : ∀ i : Fin k, ¬ (j ∣ w i)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  refine ⟨1 / (j : ℝ), by positivity, fun i => ?_⟩
  have hmod_ne : (1 * w i) % j ≠ 0 := by
    rw [one_mul]
    intro h0
    exact hnot_dvd i (Nat.dvd_of_mod_eq_zero h0)
  have hmod_ge : 1 ≤ (1 * w i) % j := Nat.one_le_iff_ne_zero.mpr hmod_ne
  have hmod_lt : (1 * w i) % j < j := Nat.mod_lt _ (by omega)
  have hmod_le : (1 * w i) % j ≤ j - 1 := by omega
  have hdist_j : dist ((((1 : ℝ) / (j : ℝ)) * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (j : ℝ) := by
    simpa [Nat.cast_one] using
      unitAddCircle_dist_ge_of_mod_Icc (N := j) (p := j) (by omega) hj2 1 (w i)
        (by nlinarith) (by nlinarith)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
  have hjk_real : (j : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hjk
  exact le_trans (one_div_le_one_div_of_le hj_pos hjk_real) hdist_j

private lemma exists_pow_mul_not_dvd {p : ℕ} (hp : 2 ≤ p) :
    ∀ n : ℕ, 0 < n → ∃ e u : ℕ, 0 < u ∧ ¬ (p ∣ u) ∧ n = p ^ e * u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hdvd : p ∣ n
    · obtain ⟨m, hm⟩ := hdvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hm; omega
        · exact hpos
      have hm_lt : m < n := by nlinarith
      obtain ⟨e, u, hu_pos, hnot, hmu⟩ := ih m hm_lt hm_pos
      refine ⟨e + 1, u, hu_pos, hnot, ?_⟩
      rw [hm, hmu, pow_succ]
      ring
    · exact ⟨0, n, hn, hdvd, by simp⟩

private lemma div_pow_mod_pow_succ {p m : ℕ} (hp : 2 ≤ p) (a s : ℕ) (hs : s < p ^ m) :
    ((a * p ^ m + s) % p ^ (m + 1)) / p ^ m = a % p := by
  have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
  have ha_eq : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
  have hlt : (a % p) * p ^ m + s < p ^ (m + 1) := by
    have hap : a % p ≤ p - 1 := by
      have := Nat.mod_lt a (by omega : 0 < p)
      omega
    calc
      (a % p) * p ^ m + s ≤ (p - 1) * p ^ m + s :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hap) s
      _ < (p - 1) * p ^ m + p ^ m := Nat.add_lt_add_left hs _
      _ = p ^ (m + 1) := by
        rw [pow_succ']
        cases p with
        | zero => omega
        | succ p' => simp [Nat.succ_mul]
  have hrew : a * p ^ m + s = ((a % p) * p ^ m + s) + p ^ (m + 1) * (a / p) := by
    conv_lhs => rw [ha_eq]
    rw [pow_succ']
    ring
  rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpm_pos, Nat.div_eq_of_lt hs, zero_add]

private lemma add_mul_mod_inj {p : ℕ} (hp : Nat.Prime p) {q₀ b : ℕ} (hb : ¬ (p ∣ b)) :
    Function.Injective (fun x : Fin p => (q₀ + x.val * b) % p) := by
  intro x₁ x₂ heq
  by_contra hne
  have hval_ne : x₁.val ≠ x₂.val := fun hv => hne (Fin.ext hv)
  have hcop : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hb
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hle : q₀ + x₁.val * b ≤ q₀ + x₂.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hlt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₂.val * b) - (q₀ + x₁.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq
    have hsub : (q₀ + x₂.val * b) - (q₀ + x₁.val * b) = (x₂.val - x₁.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have hdvd_diff : p ∣ x₂.val - x₁.val := hcop.dvd_of_dvd_mul_right hdvd1
    have := Nat.le_of_dvd (by omega) hdvd_diff
    omega
  · have hle : q₀ + x₂.val * b ≤ q₀ + x₁.val * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hgt.le) q₀
    have hdvd1 : p ∣ (q₀ + x₁.val * b) - (q₀ + x₂.val * b) :=
      (Nat.modEq_iff_dvd' hle).mp heq.symm
    have hsub : (q₀ + x₁.val * b) - (q₀ + x₂.val * b) = (x₁.val - x₂.val) * b := by
      rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    rw [hsub] at hdvd1
    have hdvd_diff : p ∣ x₁.val - x₂.val := hcop.dvd_of_dvd_mul_right hdvd1
    have := Nat.le_of_dvd (by omega) hdvd_diff
    omega

private lemma card_filter_eq_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) {f : α → β} (hf : Function.Injective f) (y : β) :
    (s.filter (fun x => f x = y)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact hf (ha.2.trans hb.2.symm)

private theorem prime_filtering_step {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hm : 1 ≤ m)
    (e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hlevel : ∀ j < m, (Finset.univ.filter (fun i : Fin k => e i = j)).card ≤ (p - 1) / 2) :
    ∀ t ≤ m, ∃ lam : ℕ, ¬ (p ∣ lam) ∧
      ∀ i : Fin k, m - t ≤ e i → e i < m →
        1 ≤ ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ∧
        ((lam * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m ≤ p - 2 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨1, ?_, fun i hge hlt => by omega⟩
    intro hdvd
    have := Nat.le_of_dvd zero_lt_one hdvd
    omega
  | succ t ih =>
    intro ht_le
    obtain ⟨lam₀, hlam₀, hprev⟩ := ih (by omega)
    let j : ℕ := m - (t + 1)
    have hj_lt : j < m := by omega
    let Sj : Finset (Fin k) := Finset.univ.filter (fun i => e i = j)
    let f_digit : Fin k → Fin p → ℕ :=
      fun i x => (((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ (e i) * u i)) % p ^ (m + 1)) / p ^ m
    have hdigit_formula : ∀ i ∈ Sj, ∀ x : Fin p,
        f_digit i x = ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) +
          x.val * (lam₀ * u i)) % p := by
      intro i hi x
      have hei : e i = j := (Finset.mem_filter.mp hi).2
      dsimp [f_digit]
      rw [hei]
      let q₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m
      let s₀ : ℕ := ((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) % p ^ m
      have hs₀_lt : s₀ < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
      have hrem_decomp : (lam₀ * (p ^ j * u i)) % p ^ (m + 1) = q₀ * p ^ m + s₀ := by
        dsimp only [q₀, s₀]
        rw [mul_comm _ (p ^ m), Nat.div_add_mod]
      have hpow_add : p ^ (m - j) * p ^ j = p ^ m := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj_lt)]
      have hexpand : (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i) =
          lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by
        calc
          (lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)
            = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * (p ^ (m - j) * p ^ j) := by ring
          _ = lam₀ * (p ^ j * u i) + (x.val * (lam₀ * u i)) * p ^ m := by rw [hpow_add]
      have hmod_N : ((lam₀ * (1 + x.val * p ^ (m - j))) * (p ^ j * u i)) % p ^ (m + 1) =
          ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) % p ^ (m + 1) := by
        rw [hexpand]
        conv_lhs => rw [← Nat.div_add_mod (lam₀ * (p ^ j * u i)) (p ^ (m + 1)), hrem_decomp]
        have hring : p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) + (q₀ * p ^ m + s₀) +
            x.val * (lam₀ * u i) * p ^ m =
            ((q₀ + x.val * (lam₀ * u i)) * p ^ m + s₀) +
            p ^ (m + 1) * (lam₀ * (p ^ j * u i) / p ^ (m + 1)) := by ring
        rw [hring, Nat.add_mul_mod_self_left]
      rw [hmod_N]
      exact div_pow_mod_pow_succ (by omega) (q₀ + x.val * (lam₀ * u i)) s₀ hs₀_lt
    let badFor : Fin k → Finset (Fin p) :=
      fun i => Finset.univ.filter (fun x : Fin p => f_digit i x = 0 ∨ f_digit i x = p - 1)
    have hbad_card : ∀ i ∈ Sj, (badFor i).card ≤ 2 := by
      intro i hi
      have hb_not : ¬ (p ∣ lam₀ * u i) := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with h1 | h2
        · exact hlam₀ h1
        · exact hu_not i h2
      let g : Fin p → ℕ :=
        fun x => ((((lam₀ * (p ^ j * u i)) % p ^ (m + 1)) / p ^ m) + x.val * (lam₀ * u i)) % p
      have hg_inj : Function.Injective g := add_mul_mod_inj hp hb_not
      have hsub : badFor i ⊆
          (Finset.univ.filter (fun x => g x = 0)) ∪ (Finset.univ.filter (fun x => g x = p - 1)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [hdigit_formula i hi x] at hx
        rcases hx.2 with h0 | hp1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h0⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hp1⟩)
      calc
        (badFor i).card ≤ ((Finset.univ.filter (fun x => g x = 0)) ∪
            (Finset.univ.filter (fun x => g x = p - 1))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x => g x = 0)).card +
            (Finset.univ.filter (fun x => g x = p - 1)).card := Finset.card_union_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (card_filter_eq_le_one _ hg_inj 0)
            (card_filter_eq_le_one _ hg_inj (p - 1))
        _ = 2 := rfl
    let allBad : Finset (Fin p) := Sj.biUnion badFor
    have hallBad_lt : allBad.card < p := by
      calc
        allBad.card ≤ ∑ i ∈ Sj, (badFor i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Sj, 2 := Finset.sum_le_sum hbad_card
        _ = 2 * Sj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 (hlevel j hj_lt)
        _ ≤ p - 1 := Nat.mul_div_le (p - 1) 2
        _ < p := by omega
    have hexists_good : (Finset.univ \ allBad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : (Finset.univ : Finset (Fin p)) ⊆ allBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_fin] at hcard
      omega
    obtain ⟨x₀, hx₀⟩ := hexists_good
    have hx₀_not_bad : x₀ ∉ allBad := (Finset.mem_sdiff.mp hx₀).2
    let lam : ℕ := lam₀ * (1 + x₀.val * p ^ (m - j))
    have hlam_not : ¬ (p ∣ lam) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hlam₀ h1
      · have hdvd_pow : p ∣ x₀.val * p ^ (m - j) := by
          refine dvd_mul_of_dvd_right ?_ x₀.val
          exact dvd_pow_self p (by omega)
        have hdvd_one : p ∣ 1 := (Nat.dvd_add_left hdvd_pow).mp h2
        have := Nat.le_of_dvd zero_lt_one hdvd_one
        omega
    refine ⟨lam, hlam_not, fun i hge hlt => ?_⟩
    rcases eq_or_lt_of_le hge with hei_eq | hei_gt
    · have hi_mem : i ∈ Sj := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hei_eq.symm⟩
      have hx_not_i : x₀ ∉ badFor i := fun h => hx₀_not_bad (Finset.mem_biUnion.mpr ⟨i, hi_mem, h⟩)
      have hnot_or : ¬ (f_digit i x₀ = 0 ∨ f_digit i x₀ = p - 1) := by
        intro hor
        exact hx_not_i (Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hor⟩)
      have hlt_p : f_digit i x₀ < p := by
        dsimp [f_digit]
        have hlt_N := Nat.mod_lt ((lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i))
          (pow_pos (by omega : 0 < p) (m + 1))
        rw [pow_succ] at hlt_N
        exact Nat.div_lt_of_lt_mul hlt_N
      change 1 ≤ f_digit i x₀ ∧ f_digit i x₀ ≤ p - 2
      omega
    · have hge_prev : m - t ≤ e i := by omega
      have hmod_same : (lam * (p ^ (e i) * u i)) % p ^ (m + 1) =
          (lam₀ * (p ^ (e i) * u i)) % p ^ (m + 1) := by
        dsimp [lam]
        have he_split : m - j + e i = (m + 1) + (e i - (j + 1)) := by omega
        have hexp : (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i) =
            lam₀ * (p ^ (e i) * u i) +
            p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
          calc
            (lam₀ * (1 + x₀.val * p ^ (m - j))) * (p ^ (e i) * u i)
              = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * (p ^ (m - j) * p ^ (e i)) := by ring
            _ = lam₀ * (p ^ (e i) * u i) +
                (lam₀ * x₀.val * u i) * p ^ ((m + 1) + (e i - (j + 1))) := by
                  rw [← pow_add, he_split]
            _ = lam₀ * (p ^ (e i) * u i) +
                p ^ (m + 1) * (lam₀ * x₀.val * u i * p ^ (e i - (j + 1))) := by
                  rw [pow_add]; ring
        rw [hexp, Nat.add_mul_mod_self_left]
      rw [hmod_same]
      exact hprev i hge_prev hlt

private theorem prime_filtering_finish {k p m : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (w e u : Fin k → ℕ) (hu_not : ∀ i, ¬ (p ∣ u i))
    (hw_decomp : ∀ i, w i = p ^ (e i) * u i) (he_le : ∀ i, e i ≤ m)
    (lam : ℕ) (hlam_not : ¬ (p ∣ lam))
    (hdigits : ∀ i : Fin k, e i < m →
      1 ≤ ((lam * w i) % p ^ (m + 1)) / p ^ m ∧
      ((lam * w i) % p ^ (m + 1)) / p ^ m ≤ p - 2) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (p : ℝ) := by
  let N : ℕ := p ^ (m + 1)
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  refine ⟨(lam : ℝ) / (N : ℝ), by positivity, fun i => ?_⟩
  rcases lt_or_eq_of_le (he_le i) with hlt | heq
  · obtain ⟨hq_lo, hq_hi⟩ := hdigits i hlt
    let q_i : ℕ := ((lam * w i) % N) / p ^ m
    let s_i : ℕ := ((lam * w i) % N) % p ^ m
    have hq_lo' : 1 ≤ q_i := hq_lo
    have hq_hi' : q_i ≤ p - 2 := hq_hi
    have hs_lt : s_i < p ^ m := Nat.mod_lt _ (pow_pos (by omega) m)
    have hrem_eq : (lam * w i) % N = p ^ m * q_i + s_i :=
      (Nat.div_add_mod ((lam * w i) % N) (p ^ m)).symm
    have hN_eq : N = p * p ^ m := pow_succ' p m
    have hlo : N ≤ p * ((lam * w i) % N) := by
      rw [hrem_eq, hN_eq]
      have : p ^ m ≤ p ^ m * q_i := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
    have hhi : p * ((lam * w i) % N) ≤ (p - 1) * N := by
      rw [hrem_eq, hN_eq]
      have h1 : p ^ m * q_i + s_i ≤ p ^ m * (p - 2) + (p ^ m - 1) := by
        have hmul : p ^ m * q_i ≤ p ^ m * (p - 2) := Nat.mul_le_mul_left _ hq_hi'
        omega
      have h2 : p ^ m * (p - 2) + (p ^ m - 1) < p ^ m * (p - 1) := by
        have hpm_pos : 0 < p ^ m := pow_pos (by omega) m
        have hsub : p - 1 = (p - 2) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
        omega
      have h3 : p ^ m * q_i + s_i ≤ p ^ m * (p - 1) := by omega
      nlinarith
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi
  · have hwi : w i = p ^ m * u i := by rw [hw_decomp i, heq]
    have hprod_not : ¬ (p ∣ lam * u i) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hlam_not h1
      · exact hu_not i h2
    let r_u : ℕ := (lam * u i) % p
    have hru_ge : 1 ≤ r_u := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      intro h0
      exact hprod_not (Nat.dvd_of_mod_eq_zero h0)
    have hru_lt : r_u < p := Nat.mod_lt _ (by omega)
    have hru_le : r_u ≤ p - 1 := by omega
    have hmod_eq : (lam * w i) % N = r_u * p ^ m := by
      dsimp [N]
      rw [hwi]
      have hrew : lam * (p ^ m * u i) = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by
        have hdiv := (Nat.div_add_mod (lam * u i) p).symm
        calc
          lam * (p ^ m * u i) = (lam * u i) * p ^ m := by ring
          _ = (p * ((lam * u i) / p) + r_u) * p ^ m := by rw [← hdiv]
          _ = r_u * p ^ m + p ^ (m + 1) * ((lam * u i) / p) := by rw [pow_succ']; ring
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_right hru_lt (pow_pos (by omega) m)
    have hN_eq : N = p * p ^ m := pow_succ' p m
    have hlo : N ≤ p * ((lam * w i) % N) := by
      rw [hmod_eq, hN_eq]
      nlinarith [pow_pos (by omega : 0 < p) m]
    have hhi : p * ((lam * w i) % N) ≤ (p - 1) * N := by
      rw [hmod_eq, hN_eq]
      nlinarith [pow_pos (by omega : 0 < p) m]
    exact unitAddCircle_dist_ge_of_mod_Icc hN_pos (by omega) lam (w i) hlo hhi

private lemma bs5_decidable_compression :
    ∀ (s : Fin 2) (c0 : Fin 4) (q1 : Fin 5) (c1 : Fin 4),
      ∃ (j : Fin 3) (k0 : Fin 5),
        (let r_val := s.val + 1
         let step_k := if s.val = 0 then 1 else 3
         let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
           if jv = 0 then 0
           else if jv = 1 then (if c.val < 2 then 0 else 1)
           else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
         let d0_good1 := (c_lookup c0 j.val + k0.val * r_val) % 5
         let d1_good1 := ((j.val + 1) * q1.val + c_lookup c1 j.val + k0.val * r_val) % 5
         let d0_good2 := (c_lookup c0 j.val + (k0.val + step_k) * r_val) % 5
         let d1_good2 := ((j.val + 1) * q1.val + c_lookup c1 j.val + (k0.val + step_k) * r_val) % 5
         1 ≤ d0_good1 ∧ d0_good1 ≤ 3 ∧ 1 ≤ d1_good1 ∧ d1_good1 ≤ 3 ∧
         1 ≤ d0_good2 ∧ d0_good2 ≤ 3 ∧ 1 ≤ d1_good2 ∧ d1_good2 ≤ 3) := by
  decide

private lemma bs5_decidable_same_class :
    ∀ (s : Fin 2) (c0 : Fin 4) (q1 : Fin 5) (c1 : Fin 4) (q2 : Fin 5) (c2 : Fin 4),
      ∃ (j : Fin 3) (k : Fin 5),
        (let r_val := s.val + 1
         let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
           if jv = 0 then 0
           else if jv = 1 then (if c.val < 2 then 0 else 1)
           else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
         let v0 := (c_lookup c0 j.val + k.val * r_val) % 5
         let v1 := ((j.val + 1) * q1.val + c_lookup c1 j.val + k.val * r_val) % 5
         let v2 := ((j.val + 1) * q2.val + c_lookup c2 j.val + k.val * r_val) % 5
         1 ≤ v0 ∧ v0 ≤ 3 ∧ 1 ≤ v1 ∧ v1 ≤ 3 ∧ 1 ≤ v2 ∧ v2 ≤ 3) := by
  decide

private lemma carry_code_exists {m : ℕ} (rem : ℕ) (hrem : rem < 5 ^ m) :
    ∃ c : Fin 4,
      (let c_lookup := fun (jv : ℕ) =>
         if jv = 0 then 0
         else if jv = 1 then (if c.val < 2 then 0 else 1)
         else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
       (1 * rem) / 5 ^ m = c_lookup 0 ∧
       (2 * rem) / 5 ^ m = c_lookup 1 ∧
       (3 * rem) / 5 ^ m = c_lookup 2) := by
  have h5m_pos : 0 < 5 ^ m := pow_pos (by omega) m
  have h5m_odd : Odd (5 ^ m) := Odd.pow (by decide : Odd 5)
  obtain ⟨h_half, hh_eq⟩ := h5m_odd
  have hc1 : (1 * rem) / 5 ^ m = 0 := by rw [one_mul]; exact Nat.div_eq_of_lt hrem
  let d2 : ℕ := (2 * rem) / 5 ^ m
  let d3 : ℕ := (3 * rem) / 5 ^ m
  have hd2_lt : d2 < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hd3_lt : d3 < 3 := Nat.div_lt_of_lt_mul (by omega)
  rcases Nat.eq_zero_or_pos d2 with hd2_0 | hd2_pos
  · have h2rem_lt : 2 * rem < 5 ^ m := by
      by_contra hge
      have : 1 ≤ d2 := Nat.div_pos (by omega) h5m_pos
      omega
    have hd3_lt2 : d3 < 2 := Nat.div_lt_of_lt_mul (by omega)
    rcases Nat.eq_zero_or_pos d3 with hd3_0 | hd3_pos
    · refine ⟨⟨0, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_0, hd3_0⟩
    · have hd3_1 : d3 = 1 := by omega
      refine ⟨⟨1, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_0, hd3_1⟩
  · have hd2_1 : d2 = 1 := by omega
    have h2rem_ge : 5 ^ m ≤ 2 * rem := by
      by_contra hlt
      have : d2 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have h2rem_gt : 5 ^ m + 1 ≤ 2 * rem := by omega
    have hd3_ge1 : 1 ≤ d3 := Nat.div_pos (by omega) h5m_pos
    rcases eq_or_lt_of_le hd3_ge1 with hd3_1 | hd3_gt1
    · refine ⟨⟨2, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_1, hd3_1.symm⟩
    · have hd3_2 : d3 = 2 := by omega
      refine ⟨⟨3, by decide⟩, ?_⟩
      dsimp; exact ⟨hc1, hd2_1, hd3_2⟩

private lemma bs5_three_unit_runners {m : ℕ} (hm : 1 ≤ m) (d : Fin 3 → ℕ)
    (hd_not : ∀ a : Fin 3, ¬ (5 ∣ d a)) :
    ∃ lam : ℕ, ¬ (5 ∣ lam) ∧
      ∀ a : Fin 3,
        1 ≤ ((lam * d a) % 5 ^ (m + 1)) / 5 ^ m ∧
        ((lam * d a) % 5 ^ (m + 1)) / 5 ^ m ≤ 3 := by
  have hp5 : Nat.Prime 5 := by decide
  let N : ℕ := 5 ^ (m + 1)
  have hN_eq : N = 5 * 5 ^ m := pow_succ' 5 m
  have h5m_pos : 0 < 5 ^ m := pow_pos (by omega) m
  have hN_pos : 0 < N := pow_pos (by omega) (m + 1)
  let v : Fin 3 → ℕ := fun a =>
    if (d a) % 5 = 1 ∨ (d a) % 5 = 2 then (d a) % N else N - ((d a) % N)
  have hv_mod5 : ∀ a, v a % 5 = 1 ∨ v a % 5 = 2 := by
    intro a
    have hmodN_mod5 : ((d a) % N) % 5 = (d a) % 5 :=
      Nat.mod_mod_of_dvd (d a) ⟨5 ^ m, hN_eq⟩
    have hrem5_ne : (d a) % 5 ≠ 0 := fun h0 => hd_not a (Nat.dvd_of_mod_eq_zero h0)
    have hrem5_lt : (d a) % 5 < 5 := Nat.mod_lt _ (by omega)
    dsimp [v]
    split_ifs with h12
    · rwa [hmodN_mod5]
    · have h34 : (d a) % 5 = 3 ∨ (d a) % 5 = 4 := by omega
      have hmod_lt : (d a) % N < N := Nat.mod_lt _ hN_pos
      have hsub_mod5 : (N - (d a) % N) % 5 = (5 - ((d a) % N) % 5) % 5 := by
        let r := (d a) % N
        have hr_lt5 : r % 5 < 5 := Nat.mod_lt _ (by decide)
        have hdiv_lt : r / 5 < 5 ^ m := by
          have hr_lt_mul : r < 5 * 5 ^ m := by dsimp [r]; rwa [← hN_eq]
          exact Nat.div_lt_of_lt_mul hr_lt_mul
        have hdiv_le : r / 5 + 1 ≤ 5 ^ m := hdiv_lt
        have hrew_z : (((N - r) : ℕ) : ℤ) =
            ((((5 - r % 5) + 5 * (5 ^ m - (r / 5 + 1))) : ℕ) : ℤ) := by
          have hq_z : (5 : ℤ) * ((r / 5 : ℕ) : ℤ) + ((r % 5 : ℕ) : ℤ) = (r : ℤ) := by
            rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
          have hN_z : (N : ℤ) = (5 : ℤ) * ((5 ^ m : ℕ) : ℤ) := by
            rw [hN_eq, Nat.cast_mul, Nat.cast_ofNat]
          have hr_le_N : r ≤ N := hmod_lt.le
          rw [Nat.cast_sub hr_le_N, Nat.cast_add, Nat.cast_sub hr_lt5.le,
            Nat.cast_mul, Nat.cast_sub hdiv_le, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          linarith
        have hrew : N - r = (5 - r % 5) + 5 * (5 ^ m - (r / 5 + 1)) :=
          Int.ofNat.inj hrew_z
        dsimp [r] at hrew
        rw [hrew, Nat.add_mul_mod_self_left]
      rw [hsub_mod5, hmodN_mod5]
      rcases h34 with h3 | h4 <;> [right; left] <;> omega
  have hv_to_d : ∀ (lam : ℕ) (a : Fin 3), ¬ (5 ∣ lam) →
      (1 ≤ ((lam * v a) % N) / 5 ^ m ∧ ((lam * v a) % N) / 5 ^ m ≤ 3) →
      (1 ≤ ((lam * d a) % N) / 5 ^ m ∧ ((lam * d a) % N) / 5 ^ m ≤ 3) := by
    intro lam a hlam ⟨hlo, hhi⟩
    dsimp [v] at hlo hhi
    split_ifs at hlo hhi with h12
    · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod] at hlo hhi
      exact ⟨hlo, hhi⟩
    · have h5m_not : ¬ (5 ^ m ∣ lam * d a) := by
        intro hdvd
        have h5_dvd_5m : 5 ∣ 5 ^ m := dvd_pow_self 5 (by omega)
        rcases hp5.dvd_mul.mp (dvd_trans h5_dvd_5m hdvd) with h1 | h2
        · exact hlam h1
        · exact hd_not a h2
      have hrem_pos : 0 < ((lam * d a) % N) % 5 ^ m := by
        refine Nat.pos_of_ne_zero ?_
        intro h0
        have hdvd1 : 5 ^ m ∣ (lam * d a) % N := Nat.dvd_of_mod_eq_zero h0
        have hdvdN : 5 ^ m ∣ N := ⟨5, by rw [hN_eq]; ring⟩
        have hdvd_tot : 5 ^ m ∣ lam * d a := by
          have h := (Nat.div_add_mod (lam * d a) N).symm
          rw [h]
          exact dvd_add (dvd_mul_of_dvd_left hdvdN _) hdvd1
        exact h5m_not hdvd_tot
      have hmod_lt : (d a) % N < N := Nat.mod_lt _ hN_pos
      have hlam_sub : (lam * (N - (d a) % N)) % N = N - (lam * d a) % N := by
        let r : ℕ := (d a) % N
        let rem : ℕ := (lam * r) % N
        let quot : ℕ := (lam * r) / N
        have hrem_eq : rem = (lam * d a) % N := by
          dsimp [rem, r]
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        have hrem_pos' : 0 < rem := by
          rw [hrem_eq]
          exact Nat.pos_of_ne_zero (fun h0 => hrem_pos.ne' (by rw [h0, Nat.zero_mod]))
        have hrem_lt : rem < N := Nat.mod_lt _ hN_pos
        have hlam_pos : 0 < lam := by
          rcases Nat.eq_zero_or_pos lam with rfl | hpos
          · simp [rem] at hrem_pos'
          · exact hpos
        have hquot_lt : quot < lam := by
          have hdiv : N * quot + rem = lam * r := Nat.div_add_mod (lam * r) N
          have h1 : N * quot < lam * r := by omega
          have h2 : lam * r < N * lam := by
            rw [mul_comm N lam]
            exact Nat.mul_lt_mul_of_pos_left hmod_lt hlam_pos
          exact Nat.lt_of_mul_lt_mul_left (lt_trans h1 h2)
        have hquot_le : quot + 1 ≤ lam := hquot_lt
        have hrew_z : (((lam * (N - r)) : ℕ) : ℤ) =
            ((((N - rem) + N * (lam - (quot + 1))) : ℕ) : ℤ) := by
          have hdiv_z : (N : ℤ) * (quot : ℤ) + (rem : ℤ) = (lam : ℤ) * (r : ℤ) := by
            exact_mod_cast Nat.div_add_mod (lam * r) N
          rw [Nat.cast_mul, Nat.cast_sub hmod_lt.le, Nat.cast_add, Nat.cast_sub hrem_lt.le,
            Nat.cast_mul, Nat.cast_sub hquot_le, Nat.cast_add, Nat.cast_one]
          linarith
        have hrew : lam * (N - r) = (N - rem) + N * (lam - (quot + 1)) :=
          Int.ofNat.inj hrew_z
        dsimp [r] at hrew
        rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), hrem_eq]
      rw [hlam_sub] at hlo hhi
      let q_d : ℕ := ((lam * d a) % N) / 5 ^ m
      let s_d : ℕ := ((lam * d a) % N) % 5 ^ m
      have hs_lt : s_d < 5 ^ m := Nat.mod_lt _ h5m_pos
      have hdecomp : (lam * d a) % N = 5 ^ m * q_d + s_d :=
        (Nat.div_add_mod ((lam * d a) % N) (5 ^ m)).symm
      have hqd_lt : q_d < 5 := by
        have hltN : (lam * d a) % N < 5 ^ m * 5 := by
          rw [← pow_succ]
          exact Nat.mod_lt _ hN_pos
        exact Nat.div_lt_of_lt_mul hltN
      have hsub_div : (N - (lam * d a) % N) / 5 ^ m = 4 - q_d := by
        have hltN : (lam * d a) % N < N := Nat.mod_lt _ hN_pos
        have hqd_le : q_d ≤ 4 := by omega
        have hrew_z : (((N - (lam * d a) % N) : ℕ) : ℤ) =
            ((((5 ^ m - s_d) + (4 - q_d) * 5 ^ m) : ℕ) : ℤ) := by
          have hdec_z : (((lam * d a) % N : ℕ) : ℤ) = (5 ^ m : ℤ) * (q_d : ℤ) + (s_d : ℤ) := by
            exact_mod_cast hdecomp
          have hN_z : (N : ℤ) = 5 * (5 ^ m : ℤ) := by exact_mod_cast hN_eq
          rw [Nat.cast_sub hltN.le, Nat.cast_add, Nat.cast_sub hs_lt.le,
            Nat.cast_mul, Nat.cast_sub hqd_le]
          push_cast
          linarith
        have hrew : N - (lam * d a) % N = (5 ^ m - s_d) + (4 - q_d) * 5 ^ m :=
          Int.ofNat.inj hrew_z
        have h5s_lt : 5 ^ m - s_d < 5 ^ m := by omega
        rw [hrew, Nat.add_mul_div_right _ _ h5m_pos, Nat.div_eq_of_lt h5s_lt, zero_add]
      rw [hsub_div] at hlo hhi
      omega
  have hs12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have hs12_1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have hs02_0 : Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide
  have hs02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  have hexists_perm : ∃ perm : Equiv.Perm (Fin 3), v (perm 0) % 5 = v (perm 1) % 5 := by
    rcases hv_mod5 0 with h0 | h0 <;> rcases hv_mod5 1 with h1 | h1 <;> rcases hv_mod5 2 with h2 | h2
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.swap 1 2, by rw [hs12_0, hs12_1, h0, h2]⟩
    · exact ⟨Equiv.swap 0 2, by rw [hs02_0, hs02_1, h2, h1]⟩
    · exact ⟨Equiv.swap 0 2, by rw [hs02_0, hs02_1, h2, h1]⟩
    · exact ⟨Equiv.swap 1 2, by rw [hs12_0, hs12_1, h0, h2]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
    · exact ⟨Equiv.refl _, by simp [h0, h1]⟩
  obtain ⟨perm, hperm01⟩ := hexists_perm
  let u : Fin 3 → ℕ := fun a => v (perm a)
  have hu0_not : ¬ (5 ∣ u 0) := by
    intro hdvd
    have h0 : u 0 % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    dsimp only [u] at h0
    rcases hv_mod5 (perm 0) with h | h <;> omega
  have hshift_inj := add_mul_mod_inj hp5 hu0_not (q₀ := (u 0) / 5 ^ m)
  have hshift_surj : Function.Surjective
      (fun x : Fin 5 => ⟨((u 0) / 5 ^ m + x.val * u 0) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5 → Fin 5) := by
    refine Finite.injective_iff_surjective.mp ?_
    intro x₁ x₂ h
    exact hshift_inj (congr_arg Fin.val h)
  obtain ⟨x_init, hx_init⟩ := hshift_surj ⟨0, by decide⟩
  let mu₀ : ℕ := 1 + x_init.val * 5 ^ m
  have hmu₀_not : ¬ (5 ∣ mu₀) := by
    intro hdvd
    have hdvd_pow : 5 ∣ x_init.val * 5 ^ m := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have hdvd1 : 5 ∣ 1 := (Nat.dvd_add_left hdvd_pow).mp hdvd
    have := Nat.le_of_dvd zero_lt_one hdvd1
    omega
  let w' : Fin 3 → ℕ := fun a => (mu₀ * u a) % N
  have hw'_mod5 : ∀ a, w' a % 5 = u a % 5 := by
    intro a
    dsimp [w', mu₀]
    have hdvd5 : 5 ∣ N := ⟨5 ^ m, hN_eq⟩
    rw [Nat.mod_mod_of_dvd _ hdvd5]
    have hrew : (1 + x_init.val * 5 ^ m) * u a =
        u a + 5 * (x_init.val * 5 ^ (m - 1) * u a) := by
      have hm1 : 5 ^ m = 5 * 5 ^ (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
      rw [hm1]; ring
    rw [hrew, Nat.add_mul_mod_self_left]
  have hw'0_div : w' 0 / 5 ^ m = 0 := by
    dsimp [w', mu₀, N]
    let q_u0 : ℕ := u 0 / 5 ^ m
    let s_u0 : ℕ := u 0 % 5 ^ m
    have hs_lt : s_u0 < 5 ^ m := Nat.mod_lt _ h5m_pos
    have hu0_eq : u 0 = q_u0 * 5 ^ m + s_u0 := by
      dsimp only [q_u0, s_u0]
      rw [mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hrew : (1 + x_init.val * 5 ^ m) * u 0 =
        ((q_u0 + x_init.val * u 0) * 5 ^ m + s_u0) := by
      calc
        (1 + x_init.val * 5 ^ m) * u 0 = u 0 + (x_init.val * u 0) * 5 ^ m := by ring
        _ = (q_u0 * 5 ^ m + s_u0) + (x_init.val * u 0) * 5 ^ m := by rw [hu0_eq]
        _ = (q_u0 + x_init.val * u 0) * 5 ^ m + s_u0 := by ring
    rw [hrew, div_pow_mod_pow_succ (by decide) _ _ hs_lt]
    exact congr_arg Fin.val hx_init
  let q_fn : Fin 3 → Fin 5 := fun a =>
    ⟨w' a / 5 ^ m, by
      have hlt : w' a < 5 ^ m * 5 := by
        rw [← pow_succ]
        exact Nat.mod_lt _ hN_pos
      exact Nat.div_lt_of_lt_mul hlt⟩
  let rem_fn : Fin 3 → ℕ := fun a => w' a % 5 ^ m
  obtain ⟨c0, hc0⟩ := carry_code_exists (rem_fn 0) (Nat.mod_lt _ h5m_pos)
  obtain ⟨c1, hc1⟩ := carry_code_exists (rem_fn 1) (Nat.mod_lt _ h5m_pos)
  obtain ⟨c2, hc2⟩ := carry_code_exists (rem_fn 2) (Nat.mod_lt _ h5m_pos)
  let s_class : Fin 2 := if w' 0 % 5 = 1 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  have hs_val : s_class.val + 1 = w' 0 % 5 := by
    dsimp [s_class]
    have h012 : w' 0 % 5 = 1 ∨ w' 0 % 5 = 2 := by rw [hw'_mod5 0]; exact hv_mod5 (perm 0)
    rcases h012 with h1 | h2
    · simp [h1]
    · simp [h2]
  have hw'1_mod5 : w' 1 % 5 = s_class.val + 1 := by
    rw [hs_val, hw'_mod5 1, hw'_mod5 0]
    exact hperm01.symm
  let c_lookup := fun (c : Fin 4) (jv : ℕ) =>
    if jv = 0 then 0
    else if jv = 1 then (if c.val < 2 then 0 else 1)
    else (if c.val = 0 then 0 else if c.val < 3 then 1 else 2)
  have h_eval_digit : ∀ (a : Fin 3) (c_a : Fin 4),
      ((1 * rem_fn a) / 5 ^ m = c_lookup c_a 0 ∧
       (2 * rem_fn a) / 5 ^ m = c_lookup c_a 1 ∧
       (3 * rem_fn a) / 5 ^ m = c_lookup c_a 2) →
      ∀ (j : Fin 3) (k : ℕ),
        ((((j.val + 1) + k * 5 ^ m) * w' a) % N) / 5 ^ m =
          ((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) % 5 := by
    intro a c_a ⟨hc_0, hc_1, hc_2⟩ j k
    have hj012 : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    have hc_j : ((j.val + 1) * rem_fn a) / 5 ^ m = c_lookup c_a j.val := by
      rcases hj012 with rfl | rfl | rfl
      · exact hc_0
      · exact hc_1
      · exact hc_2
    let s_rem : ℕ := ((j.val + 1) * rem_fn a) % 5 ^ m
    have hs_rem_lt : s_rem < 5 ^ m := Nat.mod_lt _ h5m_pos
    have hj_rem_eq : (j.val + 1) * rem_fn a = c_lookup c_a j.val * 5 ^ m + s_rem := by
      dsimp only [s_rem]
      rw [← hc_j, mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hw'_eq : w' a = (q_fn a).val * 5 ^ m + rem_fn a := by
      dsimp only [q_fn, rem_fn]
      rw [mul_comm _ (5 ^ m), Nat.div_add_mod]
    have hrem_mod5 : rem_fn a % 5 = w' a % 5 := by
      dsimp [rem_fn]
      exact Nat.mod_mod_of_dvd (w' a) (dvd_pow_self 5 (by omega))
    have hrem_div5 : rem_fn a = 5 * (rem_fn a / 5) + (w' a % 5) := by
      rw [← hrem_mod5]
      exact (Nat.div_add_mod (rem_fn a) 5).symm
    have h2m : 5 ^ m * 5 ^ m = N * 5 ^ (m - 1) := by
      dsimp [N]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hexp : (((j.val + 1) + k * 5 ^ m) * w' a) % N =
        (((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) * 5 ^ m + s_rem) % N := by
      conv_lhs => rw [hw'_eq]
      have h1 : ((j.val + 1) + k * 5 ^ m) * ((q_fn a).val * 5 ^ m + rem_fn a) =
          (j.val + 1) * (q_fn a).val * 5 ^ m + (j.val + 1) * rem_fn a +
          k * (q_fn a).val * (5 ^ m * 5 ^ m) + k * rem_fn a * 5 ^ m := by ring
      have h2 : k * rem_fn a * 5 ^ m = k * (w' a % 5) * 5 ^ m + N * (k * (rem_fn a / 5)) := by
        conv_lhs => rw [hrem_div5]
        rw [hN_eq]
        ring
      rw [h1, hj_rem_eq, h2m, h2]
      have h3 : (j.val + 1) * (q_fn a).val * 5 ^ m + (c_lookup c_a j.val * 5 ^ m + s_rem) +
          k * (q_fn a).val * (N * 5 ^ (m - 1)) +
          (k * (w' a % 5) * 5 ^ m + N * (k * (rem_fn a / 5))) =
          (((j.val + 1) * (q_fn a).val + c_lookup c_a j.val + k * (w' a % 5)) * 5 ^ m + s_rem) +
          N * (k * (q_fn a).val * 5 ^ (m - 1) + k * (rem_fn a / 5)) := by ring
      rw [h3, Nat.add_mul_mod_self_left]
    rw [hexp]
    exact div_pow_mod_pow_succ (by decide) _ _ hs_rem_lt
  have hq0_zero : (q_fn 0).val = 0 := hw'0_div
  have hexists_jk : ∃ (j : Fin 3) (k_nat : ℕ),
      ∀ a : Fin 3,
        1 ≤ ((((j.val + 1) + k_nat * 5 ^ m) * w' a) % N) / 5 ^ m ∧
        ((((j.val + 1) + k_nat * 5 ^ m) * w' a) % N) / 5 ^ m ≤ 3 := by
    by_cases hsame2 : w' 2 % 5 = s_class.val + 1
    · obtain ⟨j, k, hk_good⟩ := bs5_decidable_same_class s_class c0 (q_fn 1) c1 (q_fn 2) c2
      refine ⟨j, k.val, fun a => ?_⟩
      dsimp at hk_good
      have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
      rcases ha012 with rfl | rfl | rfl
      · rw [h_eval_digit 0 c0 hc0 j k.val, hq0_zero, mul_zero, zero_add, ← hs_val]
        exact ⟨hk_good.1, hk_good.2.1⟩
      · rw [h_eval_digit 1 c1 hc1 j k.val, hw'1_mod5]
        exact ⟨hk_good.2.2.1, hk_good.2.2.2.1⟩
      · rw [h_eval_digit 2 c2 hc2 j k.val, hsame2]
        exact ⟨hk_good.2.2.2.2.1, hk_good.2.2.2.2.2⟩
    · obtain ⟨j, k0, hk_comp⟩ := bs5_decidable_compression s_class c0 (q_fn 1) c1
      dsimp at hk_comp
      let step_k : ℕ := if s_class.val = 0 then 1 else 3
      have hw'2_12 : w' 2 % 5 = 1 ∨ w' 2 % 5 = 2 := by rw [hw'_mod5 2]; exact hv_mod5 (perm 2)
      let base2 : ℕ := ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + k0.val * (w' 2 % 5)) % 5
      let next2 : ℕ := ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + (k0.val + step_k) * (w' 2 % 5)) % 5
      have hstep_prod : (step_k * (w' 2 % 5)) % 5 = 2 ∨ (step_k * (w' 2 % 5)) % 5 = 3 := by
        have hs_lt2 : s_class.val < 2 := s_class.isLt
        dsimp [step_k]
        rcases hw'2_12 with h2_1 | h2_2
        · have hs1 : s_class.val = 1 := by omega
          rw [if_neg (by omega), h2_1]; right; rfl
        · have hs0 : s_class.val = 0 := by omega
          rw [if_pos hs0, h2_2]; left; rfl
      have h_one_good : (1 ≤ base2 ∧ base2 ≤ 3) ∨ (1 ≤ next2 ∧ next2 ≤ 3) := by
        have hstep : next2 = (base2 + (step_k * (w' 2 % 5)) % 5) % 5 := by
          dsimp [base2, next2]
          have h1 : (j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + (k0.val + step_k) * (w' 2 % 5) =
              ((j.val + 1) * (q_fn 2).val + c_lookup c2 j.val + k0.val * (w' 2 % 5)) +
              step_k * (w' 2 % 5) := by ring
          rw [h1, Nat.add_mod]
        have hb_lt : base2 < 5 := Nat.mod_lt _ (by decide)
        rcases hstep_prod with hp2 | hp3
        · rw [hp2] at hstep; omega
        · rw [hp3] at hstep; omega
      rcases h_one_good with hbase | hnext
      · refine ⟨j, k0.val, fun a => ?_⟩
        have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
        rcases ha012 with rfl | rfl | rfl
        · rw [h_eval_digit 0 c0 hc0 j k0.val, hq0_zero, mul_zero, zero_add, ← hs_val]
          exact ⟨hk_comp.1, hk_comp.2.1⟩
        · rw [h_eval_digit 1 c1 hc1 j k0.val, hw'1_mod5]
          exact ⟨hk_comp.2.2.1, hk_comp.2.2.2.1⟩
        · rw [h_eval_digit 2 c2 hc2 j k0.val]
          exact hbase
      · refine ⟨j, k0.val + step_k, fun a => ?_⟩
        have ha012 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
        rcases ha012 with rfl | rfl | rfl
        · rw [h_eval_digit 0 c0 hc0 j (k0.val + step_k), hq0_zero, mul_zero, zero_add, ← hs_val]
          exact ⟨hk_comp.2.2.2.2.1, hk_comp.2.2.2.2.2.1⟩
        · rw [h_eval_digit 1 c1 hc1 j (k0.val + step_k), hw'1_mod5]
          exact ⟨hk_comp.2.2.2.2.2.2.1, hk_comp.2.2.2.2.2.2.2⟩
        · rw [h_eval_digit 2 c2 hc2 j (k0.val + step_k)]
          exact hnext
  obtain ⟨j, k_nat, hjk⟩ := hexists_jk
  let lam₁ : ℕ := (j.val + 1) + k_nat * 5 ^ m
  have hlam₁_not : ¬ (5 ∣ lam₁) := by
    intro hdvd
    have hdvd_pow : 5 ∣ k_nat * 5 ^ m := dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _
    have hdvd_j : 5 ∣ (j.val + 1) := (Nat.dvd_add_left hdvd_pow).mp hdvd
    have hj_lt : j.val < 3 := j.isLt
    have := Nat.le_of_dvd (by omega) hdvd_j
    omega
  let lam : ℕ := lam₁ * mu₀
  have hlam_not : ¬ (5 ∣ lam) := by
    intro hdvd
    rcases hp5.dvd_mul.mp hdvd with h1 | h2
    · exact hlam₁_not h1
    · exact hmu₀_not h2
  refine ⟨lam, hlam_not, fun a => ?_⟩
  apply hv_to_d lam a hlam_not
  let a' : Fin 3 := perm.symm a
  have hua' : u a' = v a := by dsimp [u, a']; simp
  have hmod_eq : (lam * v a) % N = (lam₁ * w' a') % N := by
    rw [← hua']
    dsimp [lam, w']
    rw [Nat.mul_mod lam₁, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
  rw [hmod_eq]
  exact hjk a'

private lemma lrc_nat_four (w : Fin 4 → ℕ) (hw : ∀ i : Fin 4, 0 < w i)
    (hgcd : Finset.univ.gcd w = 1) (hdvd5 : ∃ i : Fin 4, 5 ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 4, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
  have hp5 : Nat.Prime 5 := by decide
  have hex := fun i => exists_pow_mul_not_dvd (p := 5) (by decide) (w i) (hw i)
  let e : Fin 4 → ℕ := fun i => Classical.choose (hex i)
  let u : Fin 4 → ℕ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hu_spec : ∀ i, 0 < u i ∧ ¬ (5 ∣ u i) ∧ w i = 5 ^ (e i) * u i :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hu_not : ∀ i, ¬ (5 ∣ u i) := fun i => (hu_spec i).2.1
  have hw_decomp : ∀ i, w i = 5 ^ (e i) * u i := fun i => (hu_spec i).2.2
  let m : ℕ := Finset.univ.sup e
  have he_le : ∀ i, e i ≤ m := fun i => Finset.le_sup (Finset.mem_univ i)
  have hm_ge : 1 ≤ m := by
    obtain ⟨i₀, hi₀⟩ := hdvd5
    have he_pos : 1 ≤ e i₀ := by
      rcases Nat.eq_zero_or_pos (e i₀) with h0 | hpos
      · exfalso
        rw [hw_decomp i₀, h0, pow_zero, one_mul] at hi₀
        exact hu_not i₀ hi₀
      · exact hpos
    exact le_trans he_pos (he_le i₀)
  have h5_cast : (((4 + 1 : ℕ) : ℝ)) = (5 : ℝ) := by norm_num
  rw [h5_cast]
  by_cases hlevels : ∀ j < m, (Finset.univ.filter (fun i : Fin 4 => e i = j)).card ≤ (5 - 1) / 2
  · obtain ⟨lam, hlam_not, hstep⟩ := prime_filtering_step hp5 (by decide) hm_ge e u hu_not hlevels m le_rfl
    refine prime_filtering_finish hp5 (by decide) w e u hu_not hw_decomp he_le lam hlam_not ?_
    intro i hlt
    rw [hw_decomp i]
    exact hstep i (by omega) hlt
  · simp only [not_forall, not_le] at hlevels
    obtain ⟨j₀, hj₀_lt, hj₀_card⟩ := hlevels
    let S₀ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = 0)
    let Sₘ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = m)
    let Sj₀ : Finset (Fin 4) := Finset.univ.filter (fun i => e i = j₀)
    have hS₀_ne : S₀.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hall_dvd : ∀ i : Fin 4, 5 ∣ w i := by
        intro i
        have hei_ne : e i ≠ 0 := by
          intro h0
          have : i ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩
          rw [hemp] at this; exact Finset.notMem_empty i this
        rw [hw_decomp i]
        exact dvd_mul_of_dvd_left (dvd_pow_self 5 hei_ne) _
      have hdvd_gcd : 5 ∣ Finset.univ.gcd w := Finset.dvd_gcd (fun i _ => hall_dvd i)
      rw [hgcd] at hdvd_gcd
      have := Nat.le_of_dvd zero_lt_one hdvd_gcd
      omega
    have hSₘ_ne : Sₘ.Nonempty := by
      obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ e ⟨0, Finset.mem_univ 0⟩
      have he_max : e i_max = m := le_antisymm (he_le i_max) (Finset.sup_le fun i _ => hi_max i (Finset.mem_univ i))
      exact ⟨i_max, Finset.mem_filter.mpr ⟨Finset.mem_univ i_max, he_max⟩⟩
    have hdisj_jm : Disjoint Sj₀ Sₘ := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2; omega
    have hcard_Sj₀ : 3 ≤ Sj₀.card := by
      change (5 - 1) / 2 < Sj₀.card at hj₀_card
      omega
    have hcard_Sₘ : 1 ≤ Sₘ.card := Finset.card_pos.mpr hSₘ_ne
    have hsum_le : Sj₀.card + Sₘ.card ≤ 4 := by
      rw [← Finset.card_union_of_disjoint hdisj_jm]
      exact le_trans (Finset.card_le_univ _) (by simp)
    have hSj₀_eq3 : Sj₀.card = 3 := by omega
    have hunion_univ : Sj₀ ∪ Sₘ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj_jm, Finset.card_fin]
      omega
    have hj₀_zero : j₀ = 0 := by
      obtain ⟨i₀, hi₀⟩ := hS₀_ne
      have hi₀_mem : i₀ ∈ Sj₀ ∪ Sₘ := by rw [hunion_univ]; exact Finset.mem_univ i₀
      have hei₀ : e i₀ = 0 := (Finset.mem_filter.mp hi₀).2
      rcases Finset.mem_union.mp hi₀_mem with h1 | h2
      · have := (Finset.mem_filter.mp h1).2; omega
      · have := (Finset.mem_filter.mp h2).2; omega
    subst hj₀_zero
    let emb := S₀.orderEmbOfFin hSj₀_eq3
    let d : Fin 3 → ℕ := fun a => w (emb a)
    have hd_not : ∀ a : Fin 3, ¬ (5 ∣ d a) := by
      intro a
      have hmem : emb a ∈ S₀ := Finset.orderEmbOfFin_mem S₀ hSj₀_eq3 a
      have he0 : e (emb a) = 0 := (Finset.mem_filter.mp hmem).2
      dsimp [d]
      rw [hw_decomp (emb a), he0, pow_zero, one_mul]
      exact hu_not (emb a)
    obtain ⟨lam, hlam_not, hlam_good⟩ := bs5_three_unit_runners hm_ge d hd_not
    refine prime_filtering_finish hp5 (by decide) w e u hu_not hw_decomp he_le lam hlam_not ?_
    intro i hlt
    have hi_in_union : i ∈ Sj₀ ∪ Sₘ := by rw [hunion_univ]; exact Finset.mem_univ i
    have hi_not_Sm : i ∉ Sₘ := by
      intro hm_in
      have := (Finset.mem_filter.mp hm_in).2
      omega
    have hi_in_S₀ : i ∈ S₀ := (Finset.mem_union.mp hi_in_union).resolve_right hi_not_Sm
    have hi_range : i ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact hi_in_S₀
    obtain ⟨a, ha⟩ := hi_range
    rw [← ha]
    exact hlam_good a



lemma lrc_nat_four_any (u : Fin 4 → ℕ) (hu : ∀ i : Fin 4, 0 < u i) :
    ∃ t : ℝ, ∀ i : Fin 4, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
  let g : ℕ := Finset.univ.gcd u
  have i0_mem : (0 : Fin 4) ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ 0
  have hg_ne : g ≠ 0 := fun hg0 =>
    Nat.ne_of_gt (hu 0) ((Finset.gcd_eq_zero_iff.mp hg0) 0 i0_mem)
  let w' : Fin 4 → ℕ := fun i => u i / g
  have hw_mul : ∀ i : Fin 4, g * w' i = u i :=
    fun i => Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))
  have hw'_pos : ∀ i : Fin 4, 0 < w' i := by
    intro i
    rcases Nat.eq_zero_or_pos (w' i) with hw'0 | hpos
    · exfalso; exact Nat.ne_of_gt (hu i) (by rw [← hw_mul i, hw'0, mul_zero])
    · exact hpos
  have hw'_gcd : Finset.univ.gcd w' = 1 := by
    apply Nat.dvd_one.mp
    have hdvd_g : g * Finset.univ.gcd w' ∣ g * 1 := by
      rw [mul_one]; refine Finset.dvd_gcd fun i hi => ?_
      rw [← hw_mul i]; exact mul_dvd_mul_left g (Finset.gcd_dvd hi)
    exact (mul_dvd_mul_iff_left hg_ne).mp hdvd_g
  have hprim : ∃ t' : ℝ, t' ≥ 0 ∧
      ∀ i : Fin 4, dist ((t' * (w' i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
    by_cases hdvd5 : ∃ i : Fin 4, 5 ∣ w' i
    · exact lrc_nat_four w' hw'_pos hw'_gcd hdvd5
    · exact lrc_small_divisor_sieve (k := 4) (j := 5) (by decide) (by decide) w'
        (fun i hi => hdvd5 ⟨i, hi⟩)
  obtain ⟨t', _, ht'⟩ := hprim
  refine ⟨t' / (g : ℝ), fun i => ?_⟩
  have hui_cast : (u i : ℝ) = (g : ℝ) * (w' i : ℝ) := by exact_mod_cast (hw_mul i).symm
  have h_scale : t' / (g : ℝ) * (u i : ℝ) = t' * (w' i : ℝ) := by
    rw [hui_cast]; field_simp [Nat.cast_ne_zero.mpr hg_ne]
  rw [h_scale]; exact ht' i

end
end LRCBaseFour




namespace RenaultPart2

noncomputable section

private lemma fract_add_fract (x y : ℝ) :
    Int.fract (x + y) = Int.fract (Int.fract x + Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mul_nat (lam : ℕ) (x : ℝ) :
    Int.fract ((lam : ℝ) * x) = Int.fract ((lam : ℝ) * Int.fract x) := by
  conv_lhs => rw [← Int.floor_add_fract x]
  have h : (lam : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) =
      (lam : ℝ) * Int.fract x + (((lam : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_eq_sub_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) ≤ x) (h2 : x < (z : ℝ) + 1) :
    Int.fract x = x - (z : ℝ) := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  conv_lhs => rw [hrew]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_mem_Icc_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b < 1)
    (h1 : (z : ℝ) + a ≤ x) (h2 : x ≤ (z : ℝ) + b) :
    a ≤ Int.fract x ∧ Int.fract x ≤ b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma fract_mem_Ioo_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (h1 : (z : ℝ) + a < x) (h2 : x < (z : ℝ) + b) :
    a < Int.fract x ∧ Int.fract x < b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma fract_not_Icc_of_near_int (y : ℝ) (z : ℤ)
    (h1 : (z : ℝ) - 1 / 6 < y) (h2 : y < (z : ℝ) + 1 / 6) :
    ¬ (1 / 6 ≤ Int.fract y ∧ Int.fract y ≤ 5 / 6) := by
  rcases lt_or_ge y (z : ℝ) with hlt | hge
  · rw [fract_eq_sub_int y (z - 1) (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; intro ⟨_, hle⟩; linarith
  · rw [fract_eq_sub_int y z hge (by linarith)]
    intro ⟨hlo, _⟩; linarith

private lemma not_safe_shift6_iff {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (α : ℕ) (hα1 : 1 ≤ α) (hα5 : α ≤ 5) :
    ¬ (1 / 6 ≤ Int.fract (y + (α : ℝ) / 6) ∧ Int.fract (y + (α : ℝ) / 6) ≤ 5 / 6) ↔
      (5 - (α : ℝ)) / 6 < y ∧ y < (7 - (α : ℝ)) / 6 := by
  have hα_lo : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα1
  have hα_hi : (α : ℝ) ≤ 5 := by exact_mod_cast hα5
  set s := y + (α : ℝ) / 6
  constructor
  · intro hnot
    rcases lt_or_ge s 1 with hs1 | hs1
    · rw [fract_eq_sub_int s 0 (by dsimp [s]; push_cast; linarith) (by push_cast; linarith)] at hnot
      push_cast at hnot
      have hs_gt : 5 / 6 < s := by
        by_contra hle; exact hnot ⟨by dsimp [s]; linarith, by linarith⟩
      exact ⟨by dsimp [s] at hs_gt; linarith, by dsimp [s] at hs1; linarith⟩
    · rw [fract_eq_sub_int s 1 (by push_cast; linarith) (by dsimp [s]; push_cast; linarith)] at hnot
      push_cast at hnot
      have hs_lt : s - 1 < 1 / 6 := by
        by_contra hge; exact hnot ⟨le_of_not_gt hge, by dsimp [s]; linarith⟩
      exact ⟨by dsimp [s] at hs1; linarith, by dsimp [s] at hs_lt; linarith⟩
  · rintro ⟨hlo, hhi⟩
    exact fract_not_Icc_of_near_int s 1 (by dsimp [s]; push_cast; linarith) (by dsimp [s]; push_cast; linarith)

private lemma half_fract_Ioo (x a b : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha : 0 ≤ a) (_hb : b ≤ 1)
    (hlo : a < Int.fract (2 * x)) (hhi : Int.fract (2 * x) < b) :
    (a / 2 < x ∧ x < b / 2) ∨ ((1 + a) / 2 < x ∧ x < (1 + b) / 2) := by
  rcases lt_or_ge (2 * x) 1 with hlt1 | hge1
  · left
    rw [fract_eq_sub_int (2 * x) 0 (by push_cast; linarith) (by push_cast; linarith)] at hlo hhi
    push_cast at hlo hhi; exact ⟨by linarith, by linarith⟩
  · right
    rw [fract_eq_sub_int (2 * x) 1 (by push_cast; linarith) (by push_cast; linarith)] at hlo hhi
    push_cast at hlo hhi; exact ⟨by linarith, by linarith⟩

lemma renault_claim_2_4 {x : ℝ} (hx1 : 1 / 6 < x) (hx2 : x < 5 / 6) :
    ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
      ¬ (1 / 6 ≤ Int.fract ((lam : ℝ) * x) ∧ Int.fract ((lam : ℝ) * x) ≤ 5 / 6) := by
  rcases lt_or_ge x (7 / 30) with h1 | h1
  · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
  · rcases lt_or_ge x (7 / 24) with h2 | h2
    · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
    · rcases lt_or_ge x (7 / 18) with h3 | h3
      · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
      · rcases lt_or_ge x (13 / 30) with h4 | h4
        · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
        · rcases lt_or_ge x (7 / 12) with h5 | h5
          · exact ⟨2, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
          · rcases lt_or_ge x (19 / 30) with h6 | h6
            · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
            · rcases lt_or_ge x (13 / 18) with h7 | h7
              · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
              · rcases lt_or_ge x (19 / 24) with h8 | h8
                · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
                · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 4 (by push_cast; linarith) (by push_cast; linarith)⟩

private lemma three_distinct_fin3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  intro r
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> simp_all

private lemma lemma_5_1_buckets (y : Fin 3 → ℝ)
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i < 1)
    (hfail : ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      ∃ i : Fin 3, ¬ (1 / 6 ≤ Int.fract (y i + (α : ℝ) / 6) ∧ Int.fract (y i + (α : ℝ) / 6) ≤ 5 / 6)) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ((0 < y i ∧ y i < 1 / 6 ∧ 1 / 3 < y j ∧ y j < 1 / 2 ∧ 2 / 3 < y k ∧ y k < 5 / 6) ∨
       (5 / 6 < y i ∧ y i < 1 ∧ 1 / 2 < y j ∧ y j < 2 / 3 ∧ 1 / 6 < y k ∧ y k < 1 / 3) ∨
       (2 / 3 < y i ∧ y i ≤ 5 / 6 ∧ 1 / 6 ≤ y j ∧ y j < 1 / 3 ∧ 1 / 3 < y k ∧ y k < 2 / 3)) := by
  have hb : ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      ∃ r : Fin 3, (5 - (α : ℝ)) / 6 < y r ∧ y r < (7 - (α : ℝ)) / 6 := by
    intro α h1 h5
    obtain ⟨r, hr⟩ := hfail α h1 h5
    exact ⟨r, (not_safe_shift6_iff (hy0 r) (hy1 r) α h1 h5).mp hr⟩
  obtain ⟨r5, hr5_lo, hr5_hi⟩ := hb 5 (by omega) (by omega)
  obtain ⟨r3, hr3_lo, hr3_hi⟩ := hb 3 (by omega) (by omega)
  obtain ⟨r1, hr1_lo, hr1_hi⟩ := hb 1 (by omega) (by omega)
  obtain ⟨r4, hr4_lo, hr4_hi⟩ := hb 4 (by omega) (by omega)
  obtain ⟨r2, hr2_lo, hr2_hi⟩ := hb 2 (by omega) (by omega)
  push_cast at hr5_lo hr5_hi hr3_lo hr3_hi hr1_lo hr1_hi hr4_lo hr4_hi hr2_lo hr2_hi
  have h53 : r5 ≠ r3 := fun h => by rw [h] at hr5_hi; linarith
  have h51 : r5 ≠ r1 := fun h => by rw [h] at hr5_hi; linarith
  have h31 : r3 ≠ r1 := fun h => by rw [h] at hr3_hi; linarith
  have hcover := three_distinct_fin3 h53 h51 h31
  rcases lt_or_ge (y r5) (1 / 6) with h_a | h_na
  · have hr4_eq : r4 = r3 := by
      rcases hcover r4 with rfl | rfl | rfl <;> [exfalso; rfl; exfalso] <;> linarith
    rw [hr4_eq] at hr4_hi
    have hr2_eq : r2 = r1 := by
      rcases hcover r2 with rfl | rfl | rfl <;> [exfalso; exfalso; rfl] <;> linarith
    rw [hr2_eq] at hr2_hi
    exact ⟨r5, r3, r1, h53, h51, h31, Or.inl ⟨by linarith, h_a, by linarith, by linarith, by linarith, by linarith⟩⟩
  · rcases lt_or_ge (5 / 6) (y r1) with h_b | h_nb
    · have hr2_eq : r2 = r3 := by
        rcases hcover r2 with rfl | rfl | rfl <;> [exfalso; rfl; exfalso] <;> linarith
      rw [hr2_eq] at hr2_lo
      have hr4_eq : r4 = r5 := by
        rcases hcover r4 with rfl | rfl | rfl <;> [rfl; exfalso; exfalso] <;> linarith
      rw [hr4_eq] at hr4_lo
      exact ⟨r1, r3, r5, h31.symm, h51.symm, h53.symm,
        Or.inr (Or.inl ⟨h_b, by linarith, by linarith, by linarith, by linarith, by linarith⟩)⟩
    · exact ⟨r1, r5, r3, h51.symm, h31.symm, h53,
        Or.inr (Or.inr ⟨by linarith, h_nb, h_na, by linarith, by linarith, by linarith⟩)⟩

-- Scalar Case (a) of Lemma 5.1 on (x0, x1, x2 : ℝ) — zero Fin 3 overhead!
private lemma lemma_5_1_case_a (x0 x1 x2 : ℝ)
    (hx0_0 : 0 ≤ x0) (hx0_1 : x0 < 1)
    (hx1_0 : 0 ≤ x1) (hx1_1 : x1 < 1)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (h2_0 : 0 < Int.fract (2 * x0) ∧ Int.fract (2 * x0) < 1 / 6)
    (h2_1 : 1 / 3 < Int.fract (2 * x1) ∧ Int.fract (2 * x1) < 1 / 2)
    (h2_2 : 2 / 3 < Int.fract (2 * x2) ∧ Int.fract (2 * x2) < 5 / 6)
    -- From bucket 3: exactly one of {3*x0, 3*x1, 3*x2} has fract < 1/3 and two have ≥ 1/3
    (hb3 : (Int.fract (3 * x0) < 1 / 3 ∧ 1 / 3 ≤ Int.fract (3 * x1) ∧ 1 / 3 ≤ Int.fract (3 * x2)) ∨
           (1 / 3 ≤ Int.fract (3 * x0) ∧ Int.fract (3 * x1) < 1 / 3 ∧ 1 / 3 ≤ Int.fract (3 * x2)) ∨
           (1 / 3 ≤ Int.fract (3 * x0) ∧ 1 / 3 ≤ Int.fract (3 * x1) ∧ Int.fract (3 * x2) < 1 / 3)) :
    ∃ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4) ∧
      (1 / 6 < Int.fract (x0 + (α : ℝ) / 6) ∧ Int.fract (x0 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x1 + (α : ℝ) / 6) ∧ Int.fract (x1 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + (α : ℝ) / 6) ∧ Int.fract (x2 + (α : ℝ) / 6) < 5 / 6) := by
  have hx0 := half_fract_Ioo x0 0 (1 / 6) hx0_0 hx0_1 (by norm_num) (by norm_num) h2_0.1 h2_0.2
  have hx1 := half_fract_Ioo x1 (1 / 3) (1 / 2) hx1_0 hx1_1 (by norm_num) (by norm_num) h2_1.1 h2_1.2
  have hx2 := half_fract_Ioo x2 (2 / 3) (5 / 6) hx2_0 hx2_1 (by norm_num) (by norm_num) h2_2.1 h2_2.2
  rcases hb3 with ⟨f0, f1, f2⟩ | ⟨f0, f1, f2⟩ | ⟨f0, f1, f2⟩
  · -- x0 ∈ (0, 1/12), x1 ∈ (1/6, 1/4), x2 ∈ (5/6, 11/12) -> α = 2
    rcases hx0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
    · rcases hx1 with ⟨a1, b1⟩ | ⟨a1, b1⟩
      · rcases hx2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
        · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x2) 0 (1 / 4) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
          exfalso; linarith
        · refine ⟨2, Or.inr (Or.inl rfl),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
      · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x1) 0 (1 / 4) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        exfalso; linarith
    · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x0) (1 / 2) (3 / 4) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exfalso; linarith
  · -- x0 ∈ (1/2, 7/12), x1 ∈ (2/3, 3/4), x2 ∈ (5/6, 11/12) -> α = 4
    rcases hx0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
    · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x0) 0 (1 / 4) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exfalso; linarith
    · rcases hx1 with ⟨a1, b1⟩ | ⟨a1, b1⟩
      · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x1) (1 / 2) (3 / 4) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        exfalso; linarith
      · rcases hx2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
        · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x2) 0 (1 / 4) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
          exfalso; linarith
        · refine ⟨4, Or.inr (Or.inr rfl),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
  · -- x0 ∈ (1/2, 7/12), x1 ∈ (1/6, 1/4), x2 ∈ (1/3, 5/12) -> α = 1
    rcases hx0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
    · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x0) 0 (1 / 4) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exfalso; linarith
    · rcases hx1 with ⟨a1, b1⟩ | ⟨a1, b1⟩
      · rcases hx2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
        · refine ⟨1, Or.inl rfl,
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
        · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x2) (1 / 2) (3 / 4) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
          exfalso; linarith
      · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x1) 0 (1 / 4) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        exfalso; linarith

private lemma lemma_5_1_case_b_sub3 (x0 x1 x2 : ℝ)
    (a0 : 5 / 12 < x0) (b0 : x0 < 1 / 2)
    (a1 : 3 / 4 < x1) (b1 : x1 < 5 / 6)
    (a2 : 7 / 12 < x2) (b2 : x2 < 2 / 3)
    (hb3_no_b : 5 / 6 < Int.fract (3 * x2) →
      (1 / 2 < Int.fract (3 * x0) ∧ Int.fract (3 * x0) < 2 / 3) ∨
      (1 / 2 < Int.fract (3 * x1) ∧ Int.fract (3 * x1) < 2 / 3))
    (hb3_lo : Int.fract (3 * x0) < 1 / 3 ∨ Int.fract (3 * x1) < 1 / 3 ∨ Int.fract (3 * x2) < 1 / 3)
    (hb3_mid : (1 / 3 < Int.fract (3 * x0) ∧ Int.fract (3 * x0) < 2 / 3) ∨
               (1 / 3 < Int.fract (3 * x1) ∧ Int.fract (3 * x1) < 2 / 3) ∨
               (1 / 3 < Int.fract (3 * x2) ∧ Int.fract (3 * x2) < 2 / 3))
    (hb4_cap : 0 < Int.fract (4 * x1) → Int.fract (4 * x1) < 1 / 6 →
      1 / 3 < Int.fract (4 * x2) → Int.fract (4 * x2) < 1 / 2 →
      2 / 3 < Int.fract (4 * x0) → Int.fract (4 * x0) < 5 / 6)
    (hb5_mid : (1 / 3 < Int.fract (5 * x0) ∧ Int.fract (5 * x0) < 2 / 3) ∨
               (1 / 3 < Int.fract (5 * x1) ∧ Int.fract (5 * x1) < 2 / 3) ∨
               (1 / 3 < Int.fract (5 * x2) ∧ Int.fract (5 * x2) < 2 / 3)) :
    False := by
  have hf3_0 : Int.fract (3 * x0) = 3 * x0 - 1 :=
    fract_eq_sub_int (3 * x0) 1 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
  have hf3_1 : Int.fract (3 * x1) = 3 * x1 - 2 :=
    fract_eq_sub_int (3 * x1) 2 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
  have hf3_2 : Int.fract (3 * x2) = 3 * x2 - 1 :=
    fract_eq_sub_int (3 * x2) 1 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
  have hx2_le : x2 ≤ 11 / 18 := by
    by_contra hgt
    rcases hb3_no_b (by linarith) with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  rcases lt_or_ge x1 (7 / 9) with hx1_lt | hx1_ge
  · have hx0_gt : 4 / 9 < x0 := by
      rcases hb3_mid with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
    have hf4_1 : Int.fract (4 * x1) = 4 * x1 - 3 :=
      fract_eq_sub_int (4 * x1) 3 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
    have hf4_2 : Int.fract (4 * x2) = 4 * x2 - 2 :=
      fract_eq_sub_int (4 * x2) 2 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
    have hf4_0 : Int.fract (4 * x0) = 4 * x0 - 1 :=
      fract_eq_sub_int (4 * x0) 1 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
    have hx0_lt : x0 < 11 / 24 := by
      have := hb4_cap (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
    rcases hb5_mid with ⟨m1, m2⟩ | ⟨m1, m2⟩ | ⟨m1, m2⟩
    · rw [fract_eq_sub_int (5 * x0) 2 (by push_cast; linarith) (by push_cast; linarith)] at m1; push_cast at m1; linarith
    · rw [fract_eq_sub_int (5 * x1) 3 (by push_cast; linarith) (by push_cast; linarith)] at m2; push_cast at m2; linarith
    · rcases lt_or_ge (5 * x2) 3 with hk5 | hk5
      · rw [fract_eq_sub_int (5 * x2) 2 (by push_cast; linarith) (by push_cast; linarith)] at m2; push_cast at m2; linarith
      · rw [fract_eq_sub_int (5 * x2) 3 (by push_cast; linarith) (by push_cast; linarith)] at m1; push_cast at m1; linarith
  · have hx0_le : x0 ≤ 4 / 9 := by
      rcases hb3_lo with h | h | h <;> linarith
    rcases hb5_mid with ⟨m1, m2⟩ | ⟨m1, m2⟩ | ⟨m1, m2⟩
    · rw [fract_eq_sub_int (5 * x0) 2 (by push_cast; linarith) (by push_cast; linarith)] at m1; push_cast at m1; linarith
    · rcases lt_or_ge (5 * x1) 4 with hj5 | hj5
      · rw [fract_eq_sub_int (5 * x1) 3 (by push_cast; linarith) (by push_cast; linarith)] at m2; push_cast at m2; linarith
      · rw [fract_eq_sub_int (5 * x1) 4 (by push_cast; linarith) (by push_cast; linarith)] at m1; push_cast at m1; linarith
    · rcases lt_or_ge (5 * x2) 3 with hk5 | hk5
      · rw [fract_eq_sub_int (5 * x2) 2 (by push_cast; linarith) (by push_cast; linarith)] at m2; push_cast at m2; linarith
      · rw [fract_eq_sub_int (5 * x2) 3 (by push_cast; linarith) (by push_cast; linarith)] at m1; push_cast at m1; linarith

-- Scalar Case (b) of Lemma 5.1 on (x0, x1, x2 : ℝ)
private lemma lemma_5_1_case_b (x0 x1 x2 : ℝ)
    (hx0_0 : 0 ≤ x0) (hx0_1 : x0 < 1)
    (hx1_0 : 0 ≤ x1) (hx1_1 : x1 < 1)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (h2_0 : 5 / 6 < Int.fract (2 * x0) ∧ Int.fract (2 * x0) < 1)
    (h2_1 : 1 / 2 < Int.fract (2 * x1) ∧ Int.fract (2 * x1) < 2 / 3)
    (h2_2 : 1 / 6 < Int.fract (2 * x2) ∧ Int.fract (2 * x2) < 1 / 3)
    -- Bucket 3 constraints:
    (hb3_hi : (2 / 3 < Int.fract (3 * x0) ∧ Int.fract (3 * x1) ≤ 2 / 3 ∧ Int.fract (3 * x2) ≤ 2 / 3) ∨
              (Int.fract (3 * x0) ≤ 2 / 3 ∧ 2 / 3 < Int.fract (3 * x1) ∧ Int.fract (3 * x2) ≤ 2 / 3) ∨
              (Int.fract (3 * x0) ≤ 2 / 3 ∧ Int.fract (3 * x1) ≤ 2 / 3 ∧ 2 / 3 < Int.fract (3 * x2)))
    -- No runner can have fract(3*x) > 5/6 unless another has fract(3*x) ∈ (1/2, 2/3)
    (hb3_no_b : 5 / 6 < Int.fract (3 * x2) →
      (1 / 2 < Int.fract (3 * x0) ∧ Int.fract (3 * x0) < 2 / 3) ∨
      (1 / 2 < Int.fract (3 * x1) ∧ Int.fract (3 * x1) < 2 / 3))
    -- For lam = 3, at least one runner ∈ (0, 1/3) and at least one ∈ (1/3, 2/3)
    (hb3_lo : Int.fract (3 * x0) < 1 / 3 ∨ Int.fract (3 * x1) < 1 / 3 ∨ Int.fract (3 * x2) < 1 / 3)
    (hb3_mid : (1 / 3 < Int.fract (3 * x0) ∧ Int.fract (3 * x0) < 2 / 3) ∨
               (1 / 3 < Int.fract (3 * x1) ∧ Int.fract (3 * x1) < 2 / 3) ∨
               (1 / 3 < Int.fract (3 * x2) ∧ Int.fract (3 * x2) < 2 / 3))
    -- For lam = 4, if one runner has fract(4*x) ∈ (0, 1/6) and another ∈ (1/3, 1/2), the third has < 5/6
    (hb4_cap : 0 < Int.fract (4 * x1) → Int.fract (4 * x1) < 1 / 6 →
      1 / 3 < Int.fract (4 * x2) → Int.fract (4 * x2) < 1 / 2 →
      2 / 3 < Int.fract (4 * x0) → Int.fract (4 * x0) < 5 / 6)
    -- For lam = 5, some runner has fract(5*x) ∈ (1/3, 2/3)
    (hb5_mid : (1 / 3 < Int.fract (5 * x0) ∧ Int.fract (5 * x0) < 2 / 3) ∨
               (1 / 3 < Int.fract (5 * x1) ∧ Int.fract (5 * x1) < 2 / 3) ∨
               (1 / 3 < Int.fract (5 * x2) ∧ Int.fract (5 * x2) < 2 / 3)) :
    ∃ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4) ∧
      (1 / 6 < Int.fract (x0 + (α : ℝ) / 6) ∧ Int.fract (x0 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x1 + (α : ℝ) / 6) ∧ Int.fract (x1 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + (α : ℝ) / 6) ∧ Int.fract (x2 + (α : ℝ) / 6) < 5 / 6) := by
  have hx0 := half_fract_Ioo x0 (5 / 6) 1 hx0_0 hx0_1 (by norm_num) (by norm_num) h2_0.1 h2_0.2
  have hx1 := half_fract_Ioo x1 (1 / 2) (2 / 3) hx1_0 hx1_1 (by norm_num) (by norm_num) h2_1.1 h2_1.2
  have hx2 := half_fract_Ioo x2 (1 / 6) (1 / 3) hx2_0 hx2_1 (by norm_num) (by norm_num) h2_2.1 h2_2.2
  rcases hb3_hi with ⟨f0, f1, f2⟩ | ⟨f0, f1, f2⟩ | ⟨f0, f1, f2⟩
  · -- x0 ∈ (11/12, 1), x1 ∈ (3/4, 5/6), x2 ∈ (1/12, 1/6) -> α = 4
    rcases hx0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
    · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x0) (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exfalso; linarith
    · rcases hx1 with ⟨a1, b1⟩ | ⟨a1, b1⟩
      · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x1) (3 / 4) 1 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        exfalso; linarith
      · rcases hx2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
        · refine ⟨4, Or.inr (Or.inr rfl),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
        · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x2) (3 / 4) 1 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
          exfalso; linarith
  · -- x0 ∈ (5/12, 1/2), x1 ∈ (1/4, 1/3), x2 ∈ (1/12, 1/6) -> α = 1
    rcases hx0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
    · rcases hx1 with ⟨a1, b1⟩ | ⟨a1, b1⟩
      · rcases hx2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
        · refine ⟨1, Or.inl rfl,
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
            fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
        · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x2) (3 / 4) 1 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
          exfalso; linarith
      · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x1) (1 / 4) (1 / 2) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        exfalso; linarith
    · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x0) (3 / 4) 1 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exfalso; linarith
  · -- x0 ∈ (5/12, 1/2), x1 ∈ (3/4, 5/6), x2 ∈ (7/12, 2/3) -> contradiction!
    exfalso
    have ⟨a0, b0⟩ : 5 / 12 < x0 ∧ x0 < 1 / 2 := by
      rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x0) (3 / 4) 1 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        linarith
    have ⟨a1, b1⟩ : 3 / 4 < x1 ∧ x1 < 5 / 6 := by
      rcases hx1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ⟨u, _⟩ := fract_mem_Ioo_of_int (3 * x1) (3 / 4) 1 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        linarith
      · exact ⟨by linarith, by linarith⟩
    have ⟨a2, b2⟩ : 7 / 12 < x2 ∧ x2 < 2 / 3 := by
      rcases hx2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ⟨_, u⟩ := fract_mem_Ioo_of_int (3 * x2) (1 / 4) (1 / 2) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        linarith
      · exact ⟨by linarith, by linarith⟩
    exact lemma_5_1_case_b_sub3 x0 x1 x2 a0 b0 a1 b1 a2 b2 hb3_no_b hb3_lo hb3_mid hb4_cap hb5_mid

lemma renault_lemma_5_1 (x : Fin 3 → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) :
    (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
      ∀ i : Fin 3, 1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
        Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6) ∨
    (∃ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4) ∧
      ∀ i : Fin 3, 1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧
        Int.fract (x i + (α : ℝ) / 6) < 5 / 6) := by
  by_contra hboth
  have hnot1 : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 → ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      ∃ i : Fin 3, ¬ (1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
        Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6) := by
    intro lam hl2 hl5 α ha1 ha5
    by_contra hall; apply hboth; left; refine ⟨lam, hl2, hl5, α, ha1, ha5, fun i => ?_⟩
    by_contra hi; exact hall ⟨i, hi⟩
  have hnot2 : ∀ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4) →
      ∃ i : Fin 3, ¬ (1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧
        Int.fract (x i + (α : ℝ) / 6) < 5 / 6) := by
    intro α hα
    by_contra hall; apply hboth; right; refine ⟨α, hα, fun i => ?_⟩
    by_contra hi; exact hall ⟨i, hi⟩
  have hbucket : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 →
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        ((0 < Int.fract ((lam : ℝ) * x i) ∧ Int.fract ((lam : ℝ) * x i) < 1 / 6 ∧
          1 / 3 < Int.fract ((lam : ℝ) * x j) ∧ Int.fract ((lam : ℝ) * x j) < 1 / 2 ∧
          2 / 3 < Int.fract ((lam : ℝ) * x k) ∧ Int.fract ((lam : ℝ) * x k) < 5 / 6) ∨
         (5 / 6 < Int.fract ((lam : ℝ) * x i) ∧ Int.fract ((lam : ℝ) * x i) < 1 ∧
          1 / 2 < Int.fract ((lam : ℝ) * x j) ∧ Int.fract ((lam : ℝ) * x j) < 2 / 3 ∧
          1 / 6 < Int.fract ((lam : ℝ) * x k) ∧ Int.fract ((lam : ℝ) * x k) < 1 / 3) ∨
         (2 / 3 < Int.fract ((lam : ℝ) * x i) ∧ Int.fract ((lam : ℝ) * x i) ≤ 5 / 6 ∧
          1 / 6 ≤ Int.fract ((lam : ℝ) * x j) ∧ Int.fract ((lam : ℝ) * x j) < 1 / 3 ∧
          1 / 3 < Int.fract ((lam : ℝ) * x k) ∧ Int.fract ((lam : ℝ) * x k) < 2 / 3)) := by
    intro lam hl2 hl5
    refine lemma_5_1_buckets (fun i => Int.fract ((lam : ℝ) * x i))
      (fun i => Int.fract_nonneg _) (fun i => Int.fract_lt_one _) ?_
    intro α ha1 ha5
    obtain ⟨i, hi⟩ := hnot1 lam hl2 hl5 α ha1 ha5
    refine ⟨i, ?_⟩
    have hfr : Int.fract (Int.fract ((lam : ℝ) * x i) + (α : ℝ) / 6) =
        Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) := by
      rw [fract_add_fract, Int.fract_fract, ← fract_add_fract]
    rwa [hfr]
  obtain ⟨i, j, k, hij, hik, hjk, hcases2⟩ := hbucket 2 (by omega) (by omega)
  have hcover := three_distinct_fin3 hij hik hjk
  obtain ⟨a3, b3, c3, hab3, hac3, hbc3, hc3⟩ := hbucket 3 (by omega) (by omega)
  have hcover3 := three_distinct_fin3 hab3 hac3 hbc3
  rcases hcases2 with ⟨hi1, hi2, hj1, hj2, hk1, hk2⟩ | ⟨hi1, hi2, hj1, hj2, hk1, hk2⟩ | ⟨hi1, hi2, hj1, hj2, hk1, hk2⟩
  · -- Case (a)
    push_cast at hi1 hi2 hj1 hj2 hk1 hk2
    have hb3 : (Int.fract (3 * x i) < 1 / 3 ∧ 1 / 3 ≤ Int.fract (3 * x j) ∧ 1 / 3 ≤ Int.fract (3 * x k)) ∨
               (1 / 3 ≤ Int.fract (3 * x i) ∧ Int.fract (3 * x j) < 1 / 3 ∧ 1 / 3 ≤ Int.fract (3 * x k)) ∨
               (1 / 3 ≤ Int.fract (3 * x i) ∧ 1 / 3 ≤ Int.fract (3 * x j) ∧ Int.fract (3 * x k) < 1 / 3) := by
      have hex_low : ∃ u : Fin 3, Int.fract (3 * x u) < 1 / 3 ∧ ∀ v : Fin 3, v ≠ u → 1 / 3 ≤ Int.fract (3 * x v) := by
        rcases hc3 with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨a3, by linarith, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [exact absurd heq hv; (rw [heq]; linarith); (rw [heq]; linarith)]
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨c3, h6, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [(rw [heq]; linarith); (rw [heq]; linarith); exact absurd heq hv]
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨b3, h4, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [(rw [heq]; linarith); exact absurd heq hv; (rw [heq]; linarith)]
      obtain ⟨u, hu1, hu2⟩ := hex_low
      rcases hcover u with heq | heq | heq
      · left; rw [← heq]; exact ⟨hu1, hu2 j (heq ▸ hij.symm), hu2 k (heq ▸ hik.symm)⟩
      · right; left; rw [← heq]; exact ⟨hu2 i (heq ▸ hij), hu1, hu2 k (heq ▸ hjk.symm)⟩
      · right; right; rw [← heq]; exact ⟨hu2 i (heq ▸ hik), hu2 j (heq ▸ hjk), hu1⟩
    obtain ⟨α, hα, hs0, hs1, hs2⟩ := lemma_5_1_case_a (x i) (x j) (x k)
      (hx0 i) (hx1 i) (hx0 j) (hx1 j) (hx0 k) (hx1 k) ⟨hi1, hi2⟩ ⟨hj1, hj2⟩ ⟨hk1, hk2⟩ hb3
    obtain ⟨r, hr⟩ := hnot2 α hα
    rcases hcover r with heq | heq | heq <;> rw [heq] at hr <;> [exact hr hs0; exact hr hs1; exact hr hs2]
  · -- Case (b)
    push_cast at hi1 hi2 hj1 hj2 hk1 hk2
    have hb3_hi : (2 / 3 < Int.fract (3 * x i) ∧ Int.fract (3 * x j) ≤ 2 / 3 ∧ Int.fract (3 * x k) ≤ 2 / 3) ∨
                  (Int.fract (3 * x i) ≤ 2 / 3 ∧ 2 / 3 < Int.fract (3 * x j) ∧ Int.fract (3 * x k) ≤ 2 / 3) ∨
                  (Int.fract (3 * x i) ≤ 2 / 3 ∧ Int.fract (3 * x j) ≤ 2 / 3 ∧ 2 / 3 < Int.fract (3 * x k)) := by
      have hex_hi : ∃ u : Fin 3, 2 / 3 < Int.fract (3 * x u) ∧ ∀ v : Fin 3, v ≠ u → Int.fract (3 * x v) ≤ 2 / 3 := by
        rcases hc3 with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨c3, h5, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [(rw [heq]; linarith); (rw [heq]; linarith); exact absurd heq hv]
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨a3, by linarith, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [exact absurd heq hv; (rw [heq]; linarith); (rw [heq]; linarith)]
        · push_cast at h1 h2 h3 h4 h5 h6; refine ⟨a3, h1, fun v hv => ?_⟩
          rcases hcover3 v with heq | heq | heq <;> [exact absurd heq hv; (rw [heq]; linarith); (rw [heq]; linarith)]
      obtain ⟨u, hu1, hu2⟩ := hex_hi
      rcases hcover u with heq | heq | heq
      · left; rw [← heq]; exact ⟨hu1, hu2 j (heq ▸ hij.symm), hu2 k (heq ▸ hik.symm)⟩
      · right; left; rw [← heq]; exact ⟨hu2 i (heq ▸ hij), hu1, hu2 k (heq ▸ hjk.symm)⟩
      · right; right; rw [← heq]; exact ⟨hu2 i (heq ▸ hik), hu2 j (heq ▸ hjk), hu1⟩
    have hb3_no_b : 5 / 6 < Int.fract (3 * x k) →
        (1 / 2 < Int.fract (3 * x i) ∧ Int.fract (3 * x i) < 2 / 3) ∨
        (1 / 2 < Int.fract (3 * x j) ∧ Int.fract (3 * x j) < 2 / 3) := by
      intro hgt
      rcases hc3 with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
      · push_cast at h1 h2 h3 h4 h5 h6; exfalso; rcases hcover3 k with heq | heq | heq <;> rw [heq] at hgt <;> linarith
      · push_cast at h1 h2 h3 h4 h5 h6
        rcases hcover b3 with heq | heq | heq
        · left; rw [← heq]; exact ⟨h3, h4⟩
        · right; rw [← heq]; exact ⟨h3, h4⟩
        · exfalso; rw [heq] at h4; linarith
      · push_cast at h1 h2 h3 h4 h5 h6; exfalso; rcases hcover3 k with heq | heq | heq <;> rw [heq] at hgt <;> linarith
    have hb3_lo : Int.fract (3 * x i) < 1 / 3 ∨ Int.fract (3 * x j) < 1 / 3 ∨ Int.fract (3 * x k) < 1 / 3 := by
      rcases hc3 with ⟨h1, h2, _, _, _, _⟩ | ⟨_, _, _, _, _, h6⟩ | ⟨_, _, _, h4, _, _⟩
      · push_cast at h1 h2; rcases hcover a3 with heq | heq | heq <;> rw [heq] at h2 <;> [left; (right; left); (right; right)] <;> linarith
      · push_cast at h6; rcases hcover c3 with heq | heq | heq <;> rw [heq] at h6 <;> [left; (right; left); (right; right)] <;> linarith
      · push_cast at h4; rcases hcover b3 with heq | heq | heq <;> rw [heq] at h4 <;> [left; (right; left); (right; right)] <;> linarith
    have hb3_mid : (1 / 3 < Int.fract (3 * x i) ∧ Int.fract (3 * x i) < 2 / 3) ∨
                   (1 / 3 < Int.fract (3 * x j) ∧ Int.fract (3 * x j) < 2 / 3) ∨
                   (1 / 3 < Int.fract (3 * x k) ∧ Int.fract (3 * x k) < 2 / 3) := by
      rcases hc3 with ⟨_, _, h3, h4, _, _⟩ | ⟨_, _, h3, h4, _, _⟩ | ⟨_, _, _, _, h5, h6⟩
      · push_cast at h3 h4; rcases hcover b3 with heq | heq | heq <;> rw [heq] at h3 h4 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
      · push_cast at h3 h4; rcases hcover b3 with heq | heq | heq <;> rw [heq] at h3 h4 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
      · push_cast at h5 h6; rcases hcover c3 with heq | heq | heq <;> rw [heq] at h5 h6 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
    have hb4_cap : 0 < Int.fract (4 * x j) → Int.fract (4 * x j) < 1 / 6 →
        1 / 3 < Int.fract (4 * x k) → Int.fract (4 * x k) < 1 / 2 →
        2 / 3 < Int.fract (4 * x i) → Int.fract (4 * x i) < 5 / 6 := by
      intro g1 g2 g3 g4 g5
      obtain ⟨a4, b4, c4, hab4, hac4, hbc4, hc4⟩ := hbucket 4 (by omega) (by omega)
      have hcover4 := three_distinct_fin3 hab4 hac4 hbc4
      rcases hc4 with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
      · push_cast at h1 h2 h3 h4 h5 h6
        rcases hcover4 i with heq | heq | heq <;> rw [heq] at g5 <;> [linarith; linarith; (rw [← heq] at h6; exact h6)]
      · push_cast at h1 h2 h3 h4 h5 h6; exfalso
        rcases hcover4 j with heq | heq | heq <;> rw [heq] at g2 <;> linarith
      · push_cast at h1 h2 h3 h4 h5 h6; exfalso
        rcases hcover4 j with heq | heq | heq <;> rw [heq] at g2 <;> linarith
    have hb5_mid : (1 / 3 < Int.fract (5 * x i) ∧ Int.fract (5 * x i) < 2 / 3) ∨
                   (1 / 3 < Int.fract (5 * x j) ∧ Int.fract (5 * x j) < 2 / 3) ∨
                   (1 / 3 < Int.fract (5 * x k) ∧ Int.fract (5 * x k) < 2 / 3) := by
      obtain ⟨a5, b5, c5, _, _, _, hc5⟩ := hbucket 5 (by omega) (by omega)
      rcases hc5 with ⟨_, _, h3, h4, _, _⟩ | ⟨_, _, h3, h4, _, _⟩ | ⟨_, _, _, _, h5, h6⟩
      · push_cast at h3 h4; rcases hcover b5 with heq | heq | heq <;> rw [heq] at h3 h4 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
      · push_cast at h3 h4; rcases hcover b5 with heq | heq | heq <;> rw [heq] at h3 h4 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
      · push_cast at h5 h6; rcases hcover c5 with heq | heq | heq <;> rw [heq] at h5 h6 <;> [left; (right; left); (right; right)] <;> exact ⟨by linarith, by linarith⟩
    obtain ⟨α, hα, hs0, hs1, hs2⟩ := lemma_5_1_case_b (x i) (x j) (x k)
      (hx0 i) (hx1 i) (hx0 j) (hx1 j) (hx0 k) (hx1 k) ⟨hi1, hi2⟩ ⟨hj1, hj2⟩ ⟨hk1, hk2⟩
      hb3_hi hb3_no_b hb3_lo hb3_mid hb4_cap hb5_mid
    obtain ⟨r, hr⟩ := hnot2 α hα
    rcases hcover r with heq | heq | heq <;> rw [heq] at hr <;> [exact hr hs0; exact hr hs1; exact hr hs2]
  · -- Case (c) for lam = 2
    have hf4i : 1 / 3 ≤ Int.fract (((4 : ℕ) : ℝ) * x i) ∧ Int.fract (((4 : ℕ) : ℝ) * x i) ≤ 2 / 3 := by
      have hmul : Int.fract (((4 : ℕ) : ℝ) * x i) = Int.fract ((2 : ℝ) * Int.fract (((2 : ℕ) : ℝ) * x i)) := by
        have h4 : ((4 : ℕ) : ℝ) * x i = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * x i) := by push_cast; ring
        rw [h4, fract_mul_nat 2]; push_cast; rfl
      rw [hmul]
      exact fract_mem_Icc_of_int _ (1 / 3) (2 / 3) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    have hf4j : 1 / 3 ≤ Int.fract (((4 : ℕ) : ℝ) * x j) ∧ Int.fract (((4 : ℕ) : ℝ) * x j) ≤ 2 / 3 := by
      have hmul : Int.fract (((4 : ℕ) : ℝ) * x j) = Int.fract ((2 : ℝ) * Int.fract (((2 : ℕ) : ℝ) * x j)) := by
        have h4 : ((4 : ℕ) : ℝ) * x j = ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * x j) := by push_cast; ring
        rw [h4, fract_mul_nat 2]; push_cast; rfl
      rw [hmul]
      exact fract_mem_Icc_of_int _ (1 / 3) (2 / 3) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    obtain ⟨a4, b4, c4, _, _, _, hc4⟩ := hbucket 4 (by omega) (by omega)
    have ⟨⟨r_lo, hrlo⟩, ⟨r_hi, hrhi⟩⟩ :
        (∃ r : Fin 3, Int.fract (((4 : ℕ) : ℝ) * x r) < 1 / 3) ∧
        (∃ r : Fin 3, 2 / 3 < Int.fract (((4 : ℕ) : ℝ) * x r)) := by
      rcases hc4 with ⟨_, h2, _, _, h5, _⟩ | ⟨h1, _, _, _, _, h6⟩ | ⟨h1, _, _, h4, _, _⟩
      · exact ⟨⟨a4, by linarith⟩, ⟨c4, h5⟩⟩
      · exact ⟨⟨c4, h6⟩, ⟨a4, by linarith⟩⟩
      · exact ⟨⟨b4, h4⟩, ⟨a4, h1⟩⟩
    have hrlo_k : r_lo = k := by
      rcases hcover r_lo with heq | heq | heq <;> [exfalso; exfalso; exact heq] <;> (rw [heq] at hrlo; linarith)
    have hrhi_k : r_hi = k := by
      rcases hcover r_hi with heq | heq | heq <;> [exfalso; exfalso; exact heq] <;> (rw [heq] at hrhi; linarith)
    rw [hrlo_k] at hrlo; rw [hrhi_k] at hrhi; linarith


end
end RenaultPart2



namespace RenaultPart3

noncomputable section

private lemma fract_add_fract (x y : ℝ) :
    Int.fract (x + y) = Int.fract (Int.fract x + Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mul_nat (lam : ℕ) (x : ℝ) :
    Int.fract ((lam : ℝ) * x) = Int.fract ((lam : ℝ) * Int.fract x) := by
  conv_lhs => rw [← Int.floor_add_fract x]
  have h : (lam : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) =
      (lam : ℝ) * Int.fract x + (((lam : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mem_Icc_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b < 1)
    (h1 : (z : ℝ) + a ≤ x) (h2 : x ≤ (z : ℝ) + b) :
    a ≤ Int.fract x ∧ Int.fract x ≤ b := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  rw [hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨by linarith, by linarith⟩

private lemma fract_mem_Ioo_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (h1 : (z : ℝ) + a < x) (h2 : x < (z : ℝ) + b) :
    a < Int.fract x ∧ Int.fract x < b := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  rw [hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  exact ⟨by linarith, by linarith⟩

private lemma fract_not_Icc_of_near_int (y : ℝ) (z : ℤ)
    (h1 : (z : ℝ) - 1 / 6 < y) (h2 : y < (z : ℝ) + 1 / 6) :
    ¬ (1 / 6 ≤ Int.fract y ∧ Int.fract y ≤ 5 / 6) := by
  rcases lt_or_ge y (z : ℝ) with hlt | hge
  · have hrew : y = (y - ((z - 1 : ℤ) : ℝ)) + ((z - 1 : ℤ) : ℝ) := by ring
    have hfr : Int.fract y = y - (z : ℝ) + 1 := by
      rw [hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
      push_cast; ring
    rw [hfr]; intro ⟨_, hle⟩; linarith
  · have hrew : y = (y - (z : ℝ)) + (z : ℝ) := by ring
    have hfr : Int.fract y = y - (z : ℝ) := by
      conv_lhs => rw [hrew]
      rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hfr]; intro ⟨hlo, _⟩; linarith

private lemma not_safe_shift6_iff {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (α : ℕ) (hα1 : 1 ≤ α) (hα5 : α ≤ 5) :
    ¬ (1 / 6 ≤ Int.fract (y + (α : ℝ) / 6) ∧ Int.fract (y + (α : ℝ) / 6) ≤ 5 / 6) ↔
      (5 - (α : ℝ)) / 6 < y ∧ y < (7 - (α : ℝ)) / 6 := by
  have hα_lo : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα1
  have hα_hi : (α : ℝ) ≤ 5 := by exact_mod_cast hα5
  set s := y + (α : ℝ) / 6
  constructor
  · intro hnot
    rcases lt_or_ge s 1 with hs1 | hs1
    · rw [Int.fract_eq_self.mpr ⟨by dsimp [s]; linarith, hs1⟩] at hnot
      have hs_gt : 5 / 6 < s := by
        by_contra hle; exact hnot ⟨by dsimp [s]; linarith, le_of_not_gt hle⟩
      exact ⟨by dsimp [s] at hs_gt; linarith, by dsimp [s] at hs1; linarith⟩
    · have hrew : s = (s - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
      have hfr : Int.fract s = s - 1 := by
        conv_lhs => rw [hrew]
        rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by dsimp [s]; linarith⟩]
      rw [hfr] at hnot
      have hs_lt : s - 1 < 1 / 6 := by
        by_contra hge; exact hnot ⟨le_of_not_gt hge, by dsimp [s]; linarith⟩
      exact ⟨by dsimp [s] at hs1; linarith, by dsimp [s] at hs_lt; linarith⟩
  · rintro ⟨hlo, hhi⟩
    exact fract_not_Icc_of_near_int s 1 (by dsimp [s]; push_cast; linarith) (by dsimp [s]; push_cast; linarith)

private lemma half_fract_Ioo {x a b : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha : 0 ≤ a) (_hb : b ≤ 1)
    (hlo : a < Int.fract (2 * x)) (hhi : Int.fract (2 * x) < b) :
    (a / 2 < x ∧ x < b / 2) ∨ ((1 + a) / 2 < x ∧ x < (1 + b) / 2) := by
  rcases lt_or_ge (2 * x) 1 with hlt1 | hge1
  · left
    rw [Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩] at hlo hhi
    exact ⟨by linarith, by linarith⟩
  · right
    have hrew : 2 * x = (2 * x - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [hrew, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at hlo hhi
    exact ⟨by linarith, by linarith⟩

private lemma renault_claim_2_4 {x : ℝ} (hx1 : 1 / 6 < x) (hx2 : x < 5 / 6) :
    ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
      ¬ (1 / 6 ≤ Int.fract ((lam : ℝ) * x) ∧ Int.fract ((lam : ℝ) * x) ≤ 5 / 6) := by
  rcases lt_or_ge x (7 / 30) with h1 | h1
  · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
  · rcases lt_or_ge x (7 / 24) with h2 | h2
    · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
    · rcases lt_or_ge x (7 / 18) with h3 | h3
      · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
      · rcases lt_or_ge x (13 / 30) with h4 | h4
        · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
        · rcases lt_or_ge x (7 / 12) with h5 | h5
          · exact ⟨2, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
          · rcases lt_or_ge x (19 / 30) with h6 | h6
            · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
            · rcases lt_or_ge x (13 / 18) with h7 | h7
              · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
              · rcases lt_or_ge x (19 / 24) with h8 | h8
                · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
                · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 4 (by push_cast; linarith) (by push_cast; linarith)⟩

/- ### Renault Lemma 6.4 (page 8) -/

private lemma three_distinct_fin3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  intro r
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> simp_all

lemma renault_lemma_6_4 (x : Fin 3 → ℝ)
    (hx_lo : ∀ i, 1 / 6 ≤ x i) (hx_hi : ∀ i, x i ≤ 5 / 6) :
    (∀ i : Fin 3, 1 / 6 < Int.fract (2 * x i) ∧ Int.fract (2 * x i) < 5 / 6) ∨
    (∃ α : ℕ, (α = 1 ∨ α = 5) ∧
      ∀ i : Fin 3, 1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧ Int.fract (x i + (α : ℝ) / 6) < 5 / 6) ∨
    (∃ lam : ℕ, (lam = 3 ∨ lam = 5) ∧ ∃ α : ℕ, α ≤ 5 ∧
      ∀ i : Fin 3, 1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
        Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6) := by
  by_contra hnone
  have hn1 : ∃ i₀ : Fin 3, ¬ (1 / 6 < Int.fract (2 * x i₀) ∧ Int.fract (2 * x i₀) < 5 / 6) := by
    by_contra h; apply hnone; left; intro i; by_contra hi; exact h ⟨i, hi⟩
  have hn2 : ∀ α : ℕ, (α = 1 ∨ α = 5) →
      ∃ i : Fin 3, ¬ (1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧ Int.fract (x i + (α : ℝ) / 6) < 5 / 6) := by
    intro α hα; by_contra h; apply hnone; right; left; refine ⟨α, hα, fun i => ?_⟩
    by_contra hi; exact h ⟨i, hi⟩
  have hn3 : ∀ lam : ℕ, (lam = 3 ∨ lam = 5) → ∀ α : ℕ, α ≤ 5 →
      ∃ i : Fin 3, ¬ (1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
        Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6) := by
    intro lam hl α hα; by_contra h; apply hnone; right; right; refine ⟨lam, hl, α, hα, fun i => ?_⟩
    by_contra hi; exact h ⟨i, hi⟩
  obtain ⟨i₀, hi₀⟩ := hn1
  have hxi₀ : 5 / 12 ≤ x i₀ ∧ x i₀ ≤ 7 / 12 := by
    have hlo0 := hx_lo i₀; have hhi0 := hx_hi i₀
    constructor
    · by_contra hlt
      exact hi₀ (fract_mem_Ioo_of_int (2 * x i₀) (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by linarith) (by linarith))
    · by_contra hgt
      exact hi₀ (fract_mem_Ioo_of_int (2 * x i₀) (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by linarith) (by linarith))
  obtain ⟨i₁, hi₁⟩ := hn2 5 (Or.inr rfl)
  have hxi₁ : x i₁ ≤ 1 / 3 := by
    have hlo1 := hx_lo i₁; have hhi1 := hx_hi i₁
    by_contra hgt
    exact hi₁ (fract_mem_Ioo_of_int (x i₁ + ((5 : ℕ) : ℝ) / 6) (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith))
  obtain ⟨i₂, hi₂⟩ := hn2 1 (Or.inl rfl)
  have hxi₂ : 2 / 3 ≤ x i₂ := by
    have hlo2 := hx_lo i₂; have hhi2 := hx_hi i₂
    by_contra hlt
    exact hi₂ (fract_mem_Ioo_of_int (x i₂ + ((1 : ℕ) : ℝ) / 6) (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith))
  have h01 : i₀ ≠ i₁ := fun h => by rw [h] at hxi₀; linarith
  have h02 : i₀ ≠ i₂ := fun h => by rw [h] at hxi₀; linarith
  have h12 : i₁ ≠ i₂ := fun h => by rw [h] at hxi₁; linarith
  have hcover := three_distinct_fin3 h01 h02 h12
  have hlo1 := hx_lo i₁; have hhi2 := hx_hi i₂
  -- Helper to contradict hn3 when all three runners land in [1/6, 5/6]
  have hcheck3 : ∀ (lam α : ℕ), (lam = 3 ∨ lam = 5) → α ≤ 5 →
      (∀ r : Fin 3, ∃ z : ℤ, (z : ℝ) + 1 / 6 ≤ (lam : ℝ) * x r + (α : ℝ) / 6 ∧
        (lam : ℝ) * x r + (α : ℝ) / 6 ≤ (z : ℝ) + 5 / 6) → False := by
    intro lam α hl hα hall
    obtain ⟨r, hr⟩ := hn3 lam hl α hα
    obtain ⟨z, hz1, hz2⟩ := hall r
    exact hr (fract_mem_Icc_of_int _ (1 / 6) (5 / 6) z (by norm_num) (by norm_num) hz1 hz2)
  -- Consider lam = 3, α = 0: x i₀ is always safe!
  obtain ⟨r30, hr30⟩ := hn3 3 (Or.inl rfl) 0 (by omega)
  have hr30_cases : 5 / 18 < x i₁ ∨ x i₂ < 13 / 18 := by
    rcases hcover r30 with rfl | rfl | rfl
    · exfalso; apply hr30
      exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
        (by push_cast; linarith) (by push_cast; linarith)
    · left; by_contra hle; apply hr30
      exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
        (by push_cast; linarith) (by push_cast; linarith)
    · right; by_contra hge; apply hr30
      exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
        (by push_cast; linarith) (by push_cast; linarith)
  rcases hr30_cases with hbranch1 | hbranch2
  · -- Branch 1: x i₁ ∈ (5/18, 1/3]
    -- Helper: for α ∈ {2, 3, 4, 5}, 3 * x i₁ + α / 6 ∈ (5/6 + α/6, 1 + α/6] ⊂ (1 + 1/6, 1 + 5/6]!
    have hi₁_safe3 : ∀ α : ℕ, 2 ≤ α → α ≤ 5 →
        1 / 6 ≤ Int.fract (((3 : ℕ) : ℝ) * x i₁ + (α : ℝ) / 6) ∧
        Int.fract (((3 : ℕ) : ℝ) * x i₁ + (α : ℝ) / 6) ≤ 5 / 6 := by
      intro α ha2 ha5
      have ha_lo : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast ha2
      have ha_hi : (α : ℝ) ≤ 5 := by exact_mod_cast ha5
      exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
        (by push_cast; linarith) (by push_cast; linarith)
    -- At (lam=3, α=2): i₁ is safe, and 3*x i₂ + 2/6 ∈ [2 + 1/3, 2 + 5/6] is safe -> i₀ unsafe -> x i₀ > 1/2!
    have hxi₀_gt : 1 / 2 < x i₀ := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 2 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · by_contra hle; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₁_safe3 2 (by omega) (by omega)) hr
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
    -- At (lam=3, α=4): i₁ is safe, and for x i₀ ∈ (1/2, 7/12], 3*x i₀ + 4/6 ∈ (2 + 1/6, 2 + 5/12] is safe -> i₂ unsafe -> x i₂ > 13/18!
    have hxi₂_gt : 13 / 18 < x i₂ := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 4 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₁_safe3 4 (by omega) (by omega)) hr
      · by_contra hle; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
    -- At (lam=3, α=5): i₁ is safe, and 3*x i₀ + 5/6 ∈ (2 + 1/3, 2 + 7/12] is safe -> i₂ unsafe -> x i₂ < 14/18!
    have hxi₂_lt : x i₂ < 14 / 18 := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 5 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₁_safe3 5 (by omega) (by omega)) hr
      · by_contra hge; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 3 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
    -- At (lam=3, α=3): i₁ is safe, and for x i₂ ∈ (13/18, 14/18), 3*x i₂ + 3/6 ∈ (2 + 2/3, 2 + 5/6) is safe -> i₀ unsafe -> x i₀ < 5/9!
    have hxi₀_lt : x i₀ < 5 / 9 := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 3 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · by_contra hge; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₁_safe3 3 (by omega) (by omega)) hr
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
    -- Contradiction at (lam = 5, α = 5)!
    refine hcheck3 5 5 (Or.inr rfl) (by omega) fun r => ?_
    rcases hcover r with rfl | rfl | rfl
    · exact ⟨3, by push_cast; linarith, by push_cast; linarith⟩
    · exact ⟨2, by push_cast; linarith, by push_cast; linarith⟩
    · exact ⟨4, by push_cast; linarith, by push_cast; linarith⟩
  · -- Branch 2: x i₂ ∈ [2/3, 13/18) (symmetric mirror!)
    have hi₂_safe3 : ∀ α : ℕ, 1 ≤ α → α ≤ 4 →
        1 / 6 ≤ Int.fract (((3 : ℕ) : ℝ) * x i₂ + (α : ℝ) / 6) ∧
        Int.fract (((3 : ℕ) : ℝ) * x i₂ + (α : ℝ) / 6) ≤ 5 / 6 := by
      intro α ha1 ha4
      have ha_lo : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast ha1
      have ha_hi : (α : ℝ) ≤ 4 := by exact_mod_cast ha4
      exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
        (by push_cast; linarith) (by push_cast; linarith)
    -- At (lam=3, α=4): i₂ safe, 3*x i₁ + 4/6 ∈ [1 + 1/6, 1 + 2/3] safe -> i₀ unsafe -> x i₀ < 1/2!
    have hxi₀_lt : x i₀ < 1 / 2 := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 4 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · by_contra hge; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₂_safe3 4 (by omega) (by omega)) hr
    -- At (lam=3, α=2): i₂ safe, 3*x i₀ + 2/6 ∈ [1 + 7/12, 1 + 5/6) safe -> i₁ unsafe -> x i₁ < 5/18!
    have hxi₁_lt : x i₁ < 5 / 18 := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 2 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · by_contra hge; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₂_safe3 2 (by omega) (by omega)) hr
    -- At (lam=3, α=1): i₂ safe, 3*x i₀ + 1/6 ∈ [1 + 5/12, 1 + 2/3) safe -> i₁ unsafe -> x i₁ > 2/9!
    have hxi₁_gt : 2 / 9 < x i₁ := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 1 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · by_contra hle; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₂_safe3 1 (by omega) (by omega)) hr
    -- At (lam=3, α=3): i₂ safe, 3*x i₁ + 3/6 ∈ (1 + 1/6, 1 + 1/3) safe -> i₀ unsafe -> x i₀ > 4/9!
    have hxi₀_gt : 4 / 9 < x i₀ := by
      obtain ⟨r, hr⟩ := hn3 3 (Or.inl rfl) 3 (by omega)
      rcases hcover r with rfl | rfl | rfl
      · by_contra hle; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exfalso; apply hr
        exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num)
          (by push_cast; linarith) (by push_cast; linarith)
      · exact absurd (hi₂_safe3 3 (by omega) (by omega)) hr
    -- Contradiction at (lam = 5, α = 1)!
    refine hcheck3 5 1 (Or.inr rfl) (by omega) fun r => ?_
    rcases hcover r with rfl | rfl | rfl
    · exact ⟨2, by push_cast; linarith, by push_cast; linarith⟩
    · exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩
    · exact ⟨3, by push_cast; linarith, by push_cast; linarith⟩


end
end RenaultPart3



namespace RenaultLem61

noncomputable section

private lemma fract_add_fract (x y : ℝ) :
    Int.fract (x + y) = Int.fract (Int.fract x + Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_sub_fract (x y : ℝ) :
    Int.fract (x - y) = Int.fract (Int.fract x - Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) - ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x - Int.fract y) + ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mul_nat (lam : ℕ) (x : ℝ) :
    Int.fract ((lam : ℝ) * x) = Int.fract ((lam : ℝ) * Int.fract x) := by
  conv_lhs => rw [← Int.floor_add_fract x]
  have h : (lam : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) =
      (lam : ℝ) * Int.fract x + (((lam : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_eq_sub_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) ≤ x) (h2 : x < (z : ℝ) + 1) :
    Int.fract x = x - (z : ℝ) := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  conv_lhs => rw [hrew]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_mem_Icc_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b < 1)
    (h1 : (z : ℝ) + a ≤ x) (h2 : x ≤ (z : ℝ) + b) :
    a ≤ Int.fract x ∧ Int.fract x ≤ b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma fract_mem_Ioo_of_int (x a b : ℝ) (z : ℤ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (h1 : (z : ℝ) + a < x) (h2 : x < (z : ℝ) + b) :
    a < Int.fract x ∧ Int.fract x < b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma fract_not_Icc_of_near_int (y : ℝ) (z : ℤ)
    (h1 : (z : ℝ) - 1 / 6 < y) (h2 : y < (z : ℝ) + 1 / 6) :
    ¬ (1 / 6 ≤ Int.fract y ∧ Int.fract y ≤ 5 / 6) := by
  rcases lt_or_ge y (z : ℝ) with hlt | hge
  · rw [fract_eq_sub_int y (z - 1) (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; intro ⟨_, hle⟩; linarith
  · rw [fract_eq_sub_int y z hge (by linarith)]
    intro ⟨hlo, _⟩; linarith

private lemma not_safe_shift6_iff {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1)
    (α : ℕ) (hα1 : 1 ≤ α) (hα5 : α ≤ 5) :
    ¬ (1 / 6 ≤ Int.fract (y + (α : ℝ) / 6) ∧ Int.fract (y + (α : ℝ) / 6) ≤ 5 / 6) ↔
      (5 - (α : ℝ)) / 6 < y ∧ y < (7 - (α : ℝ)) / 6 := by
  have hα_lo : (1 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα1
  have hα_hi : (α : ℝ) ≤ 5 := by exact_mod_cast hα5
  set s := y + (α : ℝ) / 6
  constructor
  · intro hnot
    rcases lt_or_ge s 1 with hs1 | hs1
    · rw [fract_eq_sub_int s 0 (by dsimp [s]; push_cast; linarith) (by push_cast; linarith)] at hnot
      push_cast at hnot
      have hs_gt : 5 / 6 < s := by
        by_contra hle; exact hnot ⟨by dsimp [s]; linarith, by linarith⟩
      exact ⟨by dsimp [s] at hs_gt; linarith, by dsimp [s] at hs1; linarith⟩
    · rw [fract_eq_sub_int s 1 (by push_cast; linarith) (by dsimp [s]; push_cast; linarith)] at hnot
      push_cast at hnot
      have hs_lt : s - 1 < 1 / 6 := by
        by_contra hge; exact hnot ⟨le_of_not_gt hge, by dsimp [s]; linarith⟩
      exact ⟨by dsimp [s] at hs1; linarith, by dsimp [s] at hs_lt; linarith⟩
  · rintro ⟨hlo, hhi⟩
    exact fract_not_Icc_of_near_int s 1 (by dsimp [s]; push_cast; linarith) (by dsimp [s]; push_cast; linarith)

private lemma half_fract_Ioo (x a b : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (_ha : 0 ≤ a) (_hb : b ≤ 1)
    (hlo : a < Int.fract (2 * x)) (hhi : Int.fract (2 * x) < b) :
    (a / 2 < x ∧ x < b / 2) ∨ ((1 + a) / 2 < x ∧ x < (1 + b) / 2) := by
  rcases lt_or_ge (2 * x) 1 with hlt1 | hge1
  · left
    rw [fract_eq_sub_int (2 * x) 0 (by push_cast; linarith) (by push_cast; linarith)] at hlo hhi
    push_cast at hlo hhi; exact ⟨by linarith, by linarith⟩
  · right
    rw [fract_eq_sub_int (2 * x) 1 (by push_cast; linarith) (by push_cast; linarith)] at hlo hhi
    push_cast at hlo hhi; exact ⟨by linarith, by linarith⟩

private lemma renault_claim_2_4 {x : ℝ} (hx1 : 1 / 6 < x) (hx2 : x < 5 / 6) :
    ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
      ¬ (1 / 6 ≤ Int.fract ((lam : ℝ) * x) ∧ Int.fract ((lam : ℝ) * x) ≤ 5 / 6) := by
  rcases lt_or_ge x (7 / 30) with h1 | h1
  · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
  · rcases lt_or_ge x (7 / 24) with h2 | h2
    · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
    · rcases lt_or_ge x (7 / 18) with h3 | h3
      · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
      · rcases lt_or_ge x (13 / 30) with h4 | h4
        · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
        · rcases lt_or_ge x (7 / 12) with h5 | h5
          · exact ⟨2, by omega, by omega, fract_not_Icc_of_near_int _ 1 (by push_cast; linarith) (by push_cast; linarith)⟩
          · rcases lt_or_ge x (19 / 30) with h6 | h6
            · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
            · rcases lt_or_ge x (13 / 18) with h7 | h7
              · exact ⟨3, by omega, by omega, fract_not_Icc_of_near_int _ 2 (by push_cast; linarith) (by push_cast; linarith)⟩
              · rcases lt_or_ge x (19 / 24) with h8 | h8
                · exact ⟨4, by omega, by omega, fract_not_Icc_of_near_int _ 3 (by push_cast; linarith) (by push_cast; linarith)⟩
                · exact ⟨5, by omega, by omega, fract_not_Icc_of_near_int _ 4 (by push_cast; linarith) (by push_cast; linarith)⟩

private lemma u2_safe_subset (u2 : ℝ) (_hu0 : 0 ≤ u2) (_hu1 : u2 < 1) :
    (∀ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4 ∨ α = 5) →
      1 / 6 ≤ Int.fract (u2 + 2 * (α : ℝ) / 6) ∧ Int.fract (u2 + 2 * (α : ℝ) / 6) ≤ 5 / 6) ∨
    (∀ α : ℕ, (α = 1 ∨ α = 3 ∨ α = 4) →
      1 / 6 ≤ Int.fract (u2 + 2 * (α : ℝ) / 6) ∧ Int.fract (u2 + 2 * (α : ℝ) / 6) ≤ 5 / 6) ∨
    (∀ α : ℕ, (α = 2 ∨ α = 3 ∨ α = 5) →
      1 / 6 ≤ Int.fract (u2 + 2 * (α : ℝ) / 6) ∧ Int.fract (u2 + 2 * (α : ℝ) / 6) ≤ 5 / 6) := by
  rcases lt_or_ge u2 (1 / 6) with h1 | h1
  · left; intro α hα
    rcases hα with rfl | rfl | rfl | rfl
    · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
  · rcases le_or_gt u2 (1 / 2) with h2 | h2
    · right; left; intro α hα
      rcases hα with rfl | rfl | rfl
      · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    · rcases le_or_gt u2 (5 / 6) with h3 | h3
      · right; right; intro α hα
        rcases hα with rfl | rfl | rfl
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      · left; intro α hα
        rcases hα with rfl | rfl | rfl | rfl
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
        · exact fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)

private lemma lemma_6_1_dist_gt (u2 u4 u5 : ℝ)
    (hu2_0 : 0 ≤ u2) (hu2_1 : u2 < 1)
    (hu4_0 : 0 ≤ u4) (hu4_1 : u4 < 1)
    (hu5_0 : 0 ≤ u5) (hu5_1 : u5 < 1)
    (hfail : ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      ¬ ((1 / 6 ≤ Int.fract (u4 + (α : ℝ) / 6) ∧ Int.fract (u4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
         (1 / 6 ≤ Int.fract (u5 + (α : ℝ) / 6) ∧ Int.fract (u5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
         (1 / 6 ≤ Int.fract (u2 + 2 * (α : ℝ) / 6) ∧ Int.fract (u2 + 2 * (α : ℝ) / 6) ≤ 5 / 6))) :
    1 / 6 < |u4 - u5| ∧ |u4 - u5| < 5 / 6 := by
  have hbad45 : ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      (1 / 6 ≤ Int.fract (u2 + 2 * (α : ℝ) / 6) ∧ Int.fract (u2 + 2 * (α : ℝ) / 6) ≤ 5 / 6) →
      ((5 - (α : ℝ)) / 6 < u4 ∧ u4 < (7 - (α : ℝ)) / 6) ∨
      ((5 - (α : ℝ)) / 6 < u5 ∧ u5 < (7 - (α : ℝ)) / 6) := by
    intro α h1 h5 hu2_s
    by_contra hnb
    have hs4 : 1 / 6 ≤ Int.fract (u4 + (α : ℝ) / 6) ∧ Int.fract (u4 + (α : ℝ) / 6) ≤ 5 / 6 := by
      by_contra h4; exact hnb (Or.inl ((not_safe_shift6_iff hu4_0 hu4_1 α h1 h5).mp h4))
    have hs5 : 1 / 6 ≤ Int.fract (u5 + (α : ℝ) / 6) ∧ Int.fract (u5 + (α : ℝ) / 6) ≤ 5 / 6 := by
      by_contra h5'; exact hnb (Or.inr ((not_safe_shift6_iff hu5_0 hu5_1 α h1 h5).mp h5'))
    exact hfail α h1 h5 ⟨hs4, hs5, hu2_s⟩
  rcases u2_safe_subset u2 hu2_0 hu2_1 with hs1245 | hs134 | hs235
  · have b1 := hbad45 1 (by omega) (by omega) (hs1245 1 (Or.inl rfl))
    have b2 := hbad45 2 (by omega) (by omega) (hs1245 2 (Or.inr (Or.inl rfl)))
    have b4 := hbad45 4 (by omega) (by omega) (hs1245 4 (Or.inr (Or.inr (Or.inl rfl))))
    have b5 := hbad45 5 (by omega) (by omega) (hs1245 5 (Or.inr (Or.inr (Or.inr rfl))))
    push_cast at b1 b2 b4 b5
    rcases b1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
    · have ⟨h4a, h4b⟩ : 1 / 6 < u5 ∧ u5 < 1 / 2 := by rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;> [linarith; exact ⟨by linarith, by linarith⟩]
      have h2b : u4 < 5 / 6 := by rcases b2 with ⟨_, h⟩ | ⟨_, _⟩ <;> linarith
      have h5b : u5 < 1 / 3 := by rcases b5 with ⟨_, _⟩ | ⟨_, h⟩ <;> linarith
      rw [abs_of_nonneg (by linarith)]; exact ⟨by linarith, by linarith⟩
    · have ⟨h4a, h4b⟩ : 1 / 6 < u4 ∧ u4 < 1 / 2 := by rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;> [exact ⟨by linarith, by linarith⟩; linarith]
      have h2b : u5 < 5 / 6 := by rcases b2 with ⟨_, _⟩ | ⟨_, h⟩ <;> linarith
      have h5b : u4 < 1 / 3 := by rcases b5 with ⟨_, h⟩ | ⟨_, _⟩ <;> linarith
      rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
  · have b1 := hbad45 1 (by omega) (by omega) (hs134 1 (Or.inl rfl))
    have b4 := hbad45 4 (by omega) (by omega) (hs134 4 (Or.inr (Or.inr rfl)))
    push_cast at b1 b4
    rcases b1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
    · have ⟨h4a, h4b⟩ : 1 / 6 < u5 ∧ u5 < 1 / 2 := by rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;> [linarith; exact ⟨by linarith, by linarith⟩]
      rw [abs_of_nonneg (by linarith)]; exact ⟨by linarith, by linarith⟩
    · have ⟨h4a, h4b⟩ : 1 / 6 < u4 ∧ u4 < 1 / 2 := by rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;> [exact ⟨by linarith, by linarith⟩; linarith]
      rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
  · have b2 := hbad45 2 (by omega) (by omega) (hs235 2 (Or.inl rfl))
    have b5 := hbad45 5 (by omega) (by omega) (hs235 5 (Or.inr (Or.inr rfl)))
    push_cast at b2 b5
    rcases b2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
    · have ⟨h5a, h5b⟩ : 0 < u5 ∧ u5 < 1 / 3 := by rcases b5 with ⟨_, _⟩ | ⟨_, _⟩ <;> [linarith; exact ⟨by linarith, by linarith⟩]
      rw [abs_of_nonneg (by linarith)]; exact ⟨by linarith, by linarith⟩
    · have ⟨h5a, h5b⟩ : 0 < u4 ∧ u4 < 1 / 3 := by rcases b5 with ⟨_, _⟩ | ⟨_, _⟩ <;> [exact ⟨by linarith, by linarith⟩; linarith]
      rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩

-- Helper Case (A) of Lemma 6.1
private lemma lemma_6_1_case_A (x2 x4 x5 : ℝ)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (hx4_0 : 0 ≤ x4) (hx4_1 : x4 < 1)
    (hx5_0 : 0 ≤ x5) (hx5_1 : x5 < 1)
    (hx45_close : |x4 - x5| < 1 / 6 ∨ 5 / 6 < |x4 - x5|)
    (hv4 : 2 / 3 < Int.fract (2 * x4) ∧ Int.fract (2 * x4) < 5 / 6)
    (hv5 : 1 / 3 < Int.fract (2 * x5) ∧ Int.fract (2 * x5) < 1 / 2)
    (hv2 : 1 / 6 < Int.fract (2 * x2) ∧ Int.fract (2 * x2) < 1 / 2) :
    ∃ α : ℕ, 1 ≤ α ∧ α ≤ 4 ∧
      (1 / 6 < Int.fract (x4 + (α : ℝ) / 6) ∧ Int.fract (x4 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x5 + (α : ℝ) / 6) ∧ Int.fract (x5 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (x2 + 2 * (α : ℝ) / 6) < 5 / 6) := by
  have hx4_h := half_fract_Ioo x4 (2 / 3) (5 / 6) hx4_0 hx4_1 (by norm_num) (by norm_num) hv4.1 hv4.2
  have hx5_h := half_fract_Ioo x5 (1 / 3) (1 / 2) hx5_0 hx5_1 (by norm_num) (by norm_num) hv5.1 hv5.2
  have hx2_h := half_fract_Ioo x2 (1 / 6) (1 / 2) hx2_0 hx2_1 (by norm_num) (by norm_num) hv2.1 hv2.2
  rcases hx5_h with ⟨a5, b5⟩ | ⟨a5, b5⟩
  · have ⟨a4, b4⟩ : 1 / 3 < x4 ∧ x4 < 5 / 12 := by
      rcases hx4_h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exfalso; rcases hx45_close with hc | hc <;> [rw [abs_lt] at hc; rw [lt_abs] at hc] <;>
          [linarith; (rcases hc with _ | _ <;> linarith)]
    rcases hx2_h with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact ⟨1, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
    · exact ⟨2, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
  · have ⟨a4, b4⟩ : 5 / 6 < x4 ∧ x4 < 11 / 12 := by
      rcases hx4_h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; rcases hx45_close with hc | hc <;> [rw [abs_lt] at hc; rw [lt_abs] at hc] <;>
          [linarith; (rcases hc with _ | _ <;> linarith)]
      · exact ⟨by linarith, by linarith⟩
    rcases hx2_h with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact ⟨4, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
    · exact ⟨3, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩

-- Helper Case (B) of Lemma 6.1
private lemma lemma_6_1_case_B (x2 x4 x5 : ℝ)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (hx4_0 : 0 ≤ x4) (hx4_1 : x4 < 1)
    (hx5_0 : 0 ≤ x5) (hx5_1 : x5 < 1)
    (hx45_close : |x4 - x5| < 1 / 6 ∨ 5 / 6 < |x4 - x5|)
    (hv4 : 1 / 2 < Int.fract (2 * x4) ∧ Int.fract (2 * x4) < 2 / 3)
    (hv5 : 1 / 6 < Int.fract (2 * x5) ∧ Int.fract (2 * x5) < 1 / 3)
    (hv2 : 1 / 2 < Int.fract (2 * x2) ∧ Int.fract (2 * x2) < 5 / 6) :
    (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6)) ∨
    (∃ α : ℕ, 1 ≤ α ∧ α ≤ 4 ∧
      (1 / 6 < Int.fract (x4 + (α : ℝ) / 6) ∧ Int.fract (x4 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x5 + (α : ℝ) / 6) ∧ Int.fract (x5 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (x2 + 2 * (α : ℝ) / 6) < 5 / 6)) := by
  have hx4_h := half_fract_Ioo x4 (1 / 2) (2 / 3) hx4_0 hx4_1 (by norm_num) (by norm_num) hv4.1 hv4.2
  have hx5_h := half_fract_Ioo x5 (1 / 6) (1 / 3) hx5_0 hx5_1 (by norm_num) (by norm_num) hv5.1 hv5.2
  have hx2_h := half_fract_Ioo x2 (1 / 2) (5 / 6) hx2_0 hx2_1 (by norm_num) (by norm_num) hv2.1 hv2.2
  rcases hx4_h with ⟨a4, b4⟩ | ⟨a4, b4⟩
  · have ⟨a5, b5⟩ : 1 / 12 < x5 ∧ x5 < 1 / 6 := by
      rcases hx5_h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exfalso; rcases hx45_close with hc | hc <;> [rw [abs_lt] at hc; rw [lt_abs] at hc] <;>
          [linarith; (rcases hc with _ | _ <;> linarith)]
    rcases hx2_h with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · right; exact ⟨3, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
    · right; exact ⟨2, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
  · have ⟨a5, b5⟩ : 7 / 12 < x5 ∧ x5 < 2 / 3 := by
      rcases hx5_h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; rcases hx45_close with hc | hc <;> [rw [abs_lt] at hc; rw [lt_abs] at hc] <;>
          [linarith; (rcases hc with _ | _ <;> linarith)]
      · exact ⟨by linarith, by linarith⟩
    rcases hx2_h with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · right; exact ⟨4, by omega, by omega,
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
        fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
    · rcases le_or_gt x2 (5 / 6) with hx2_le | hx2_gt
      · left; exact ⟨4, by omega, by omega, 1, by omega, by omega,
          fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 3 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
          fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
          fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 3 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩
      · right; exact ⟨4, by omega, by omega,
          fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
          fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith),
          fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)⟩

private lemma lemma_6_1_ordered (x2 x4 x5 : ℝ)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (hx4_0 : 0 ≤ x4) (hx4_1 : x4 < 1)
    (hx5_0 : 0 ≤ x5) (hx5_1 : x5 < 1)
    (hord : Int.fract (2 * x5) ≤ Int.fract (2 * x4)) :
    (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6)) ∨
    (∃ α : ℕ, 1 ≤ α ∧ α ≤ 4 ∧
      (1 / 6 < Int.fract (x4 + (α : ℝ) / 6) ∧ Int.fract (x4 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x5 + (α : ℝ) / 6) ∧ Int.fract (x5 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (x2 + 2 * (α : ℝ) / 6) < 5 / 6)) := by
  by_contra hboth
  have hn1 : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 → ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      ¬ ((1 / 6 ≤ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
         (1 / 6 ≤ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
         (1 / 6 ≤ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6)) := by
    intro lam hl2 hl5 α ha1 ha5 hgood
    exact hboth (Or.inl ⟨lam, hl2, hl5, α, ha1, ha5, hgood⟩)
  have hdist_lam : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 →
      1 / 6 < |Int.fract ((lam : ℝ) * x4) - Int.fract ((lam : ℝ) * x5)| ∧
      |Int.fract ((lam : ℝ) * x4) - Int.fract ((lam : ℝ) * x5)| < 5 / 6 := by
    intro lam hl2 hl5
    refine lemma_6_1_dist_gt (Int.fract ((lam : ℝ) * x2)) (Int.fract ((lam : ℝ) * x4)) (Int.fract ((lam : ℝ) * x5))
      (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
      (Int.fract_nonneg _) (Int.fract_lt_one _) fun α ha1 ha5 hg => hn1 lam hl2 hl5 α ha1 ha5 ?_
    have rw_fr : ∀ z c : ℝ, Int.fract (Int.fract z + c) = Int.fract (z + c) := fun z c => by
      rw [fract_add_fract, Int.fract_fract, ← fract_add_fract]
    rwa [rw_fr, rw_fr, rw_fr] at hg
  let d : ℝ := Int.fract (x4 - x5)
  have hd_lam : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 →
      1 / 6 < Int.fract ((lam : ℝ) * d) ∧ Int.fract ((lam : ℝ) * d) < 5 / 6 := by
    intro lam hl2 hl5
    have ⟨hlo, hhi⟩ := hdist_lam lam hl2 hl5
    have hd_eq : Int.fract ((lam : ℝ) * d) =
        Int.fract (Int.fract ((lam : ℝ) * x4) - Int.fract ((lam : ℝ) * x5)) := by
      dsimp [d]
      rw [← fract_mul_nat lam (x4 - x5), mul_sub, fract_sub_fract]
    rw [hd_eq]
    rcases le_or_gt (Int.fract ((lam : ℝ) * x5)) (Int.fract ((lam : ℝ) * x4)) with hle | hgt
    · rw [abs_of_nonneg (by linarith)] at hlo hhi
      exact fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
    · rw [abs_of_neg (by linarith)] at hlo hhi
      exact fract_mem_Ioo_of_int _ (1 / 6) (5 / 6) (-1) (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
  have hd_not_mid : ¬ (1 / 6 < d ∧ d < 5 / 6) := by
    rintro ⟨h1, h2⟩
    obtain ⟨lam, hl2, hl5, hnot⟩ := renault_claim_2_4 h1 h2
    obtain ⟨g1, g2⟩ := hd_lam lam hl2 hl5
    exact hnot ⟨g1.le, g2.le⟩
  have hd_not_16 : d ≠ 1 / 6 ∧ d ≠ 5 / 6 := by
    constructor <;> intro heq
    · have ⟨_, g2⟩ := hd_lam 5 (by omega) (by omega)
      rw [heq, fract_eq_sub_int (((5 : ℕ) : ℝ) * (1 / 6)) 0 (by push_cast; norm_num) (by push_cast; norm_num)] at g2
      push_cast at g2; linarith
    · have ⟨g1, _⟩ := hd_lam 5 (by omega) (by omega)
      rw [heq, fract_eq_sub_int (((5 : ℕ) : ℝ) * (5 / 6)) 4 (by push_cast; norm_num) (by push_cast; norm_num)] at g1
      push_cast at g1; linarith
  have hd_range : (1 / 12 < d ∧ d < 1 / 6) ∨ (5 / 6 < d ∧ d < 11 / 12) := by
    have hd0 : 0 ≤ d := Int.fract_nonneg _
    have hd1 : d < 1 := Int.fract_lt_one _
    have ⟨g1, g2⟩ := hd_lam 2 (by omega) (by omega)
    rcases le_or_gt d (1 / 6) with hle | hgt
    · left; refine ⟨?_, lt_of_le_of_ne hle hd_not_16.1⟩
      by_contra hle12
      rw [fract_eq_sub_int (((2 : ℕ) : ℝ) * d) 0 (by push_cast; linarith) (by push_cast; linarith)] at g1
      push_cast at g1; linarith
    · have hge56 : 5 / 6 ≤ d := by by_contra hlt; exact hd_not_mid ⟨hgt, lt_of_not_ge hlt⟩
      right; refine ⟨lt_of_le_of_ne hge56 hd_not_16.2.symm, ?_⟩
      by_contra hge11
      rw [fract_eq_sub_int (((2 : ℕ) : ℝ) * d) 1 (by push_cast; linarith) (by push_cast; linarith)] at g2
      push_cast at g2; linarith
  have hx45_close : |x4 - x5| < 1 / 6 ∨ 5 / 6 < |x4 - x5| := by
    rcases le_or_gt x5 x4 with hle | hgt
    · have hfr : d = x4 - x5 := fract_eq_sub_int (x4 - x5) 0 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
      rw [abs_of_nonneg (by linarith), ← hfr]
      rcases hd_range with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]
    · have hfr : d = x4 - x5 + 1 := fract_eq_sub_int (x4 - x5) (-1) (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
      rw [abs_of_neg (by linarith)]
      rcases hd_range with ⟨h, _⟩ | ⟨_, h⟩ <;> [right; left] <;> linarith
  set v4 := Int.fract (2 * x4)
  set v5 := Int.fract (2 * x5)
  set v2 := Int.fract (2 * x2)
  have hv4_0 : 0 ≤ v4 := Int.fract_nonneg _; have hv4_1 : v4 < 1 := Int.fract_lt_one _
  have hv5_0 : 0 ≤ v5 := Int.fract_nonneg _; have hv5_1 : v5 < 1 := Int.fract_lt_one _
  have hv2_0 : 0 ≤ v2 := Int.fract_nonneg _; have hv2_1 : v2 < 1 := Int.fract_lt_one _
  have hv_diff_or : (1 / 6 < v4 - v5 ∧ v4 - v5 < 1 / 3) ∨ (2 / 3 < v4 - v5 ∧ v4 - v5 < 5 / 6) := by
    have h2d : v4 - v5 = Int.fract (2 * d) := by
      have h1 : Int.fract (v4 - v5) = v4 - v5 :=
        fract_eq_sub_int (v4 - v5) 0 (by push_cast; linarith) (by push_cast; linarith) |>.trans (by push_cast; ring)
      have h2 : Int.fract (2 * d) = Int.fract (v4 - v5) := by
        have hc2 : (2 : ℝ) * d = ((2 : ℕ) : ℝ) * (x4 - x5) - ((2 : ℤ) * ⌊x4 - x5⌋ : ℤ) := by
          have hf := Int.floor_add_fract (x4 - x5)
          dsimp [d]; push_cast; linarith
        have hsub : ((2 : ℕ) : ℝ) * (x4 - x5) - (((2 : ℤ) * ⌊x4 - x5⌋ : ℤ) : ℝ) =
            (v4 - v5) + ((⌊2 * x4⌋ - ⌊2 * x5⌋ - 2 * ⌊x4 - x5⌋ : ℤ) : ℝ) := by
          dsimp [v4, v5]
          have f4 := Int.floor_add_fract (2 * x4)
          have f5 := Int.floor_add_fract (2 * x5)
          push_cast; linarith
        rw [hc2, hsub, Int.fract_add_intCast]
      linarith
    rcases hd_range with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have ⟨g1, g2⟩ := fract_mem_Ioo_of_int (2 * d) (1 / 6) (1 / 3) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exact ⟨by linarith, by linarith⟩
    · right
      have ⟨g1, g2⟩ := fract_mem_Ioo_of_int (2 * d) (2 / 3) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith)
      exact ⟨by linarith, by linarith⟩
  have hbad2 : ∀ α : ℕ, 1 ≤ α → α ≤ 5 →
      (1 / 6 ≤ Int.fract (v2 + 2 * (α : ℝ) / 6) ∧ Int.fract (v2 + 2 * (α : ℝ) / 6) ≤ 5 / 6) →
      ((5 - (α : ℝ)) / 6 < v4 ∧ v4 < (7 - (α : ℝ)) / 6) ∨
      ((5 - (α : ℝ)) / 6 < v5 ∧ v5 < (7 - (α : ℝ)) / 6) := by
    intro α h1 h5 hv2_s
    by_contra hnb
    have hrw_gen : ∀ z : ℝ, Int.fract (((2 : ℕ) : ℝ) * z + (α : ℝ) / 6) = Int.fract (Int.fract (2 * z) + (α : ℝ) / 6) := by
      intro z
      have h : ((2 : ℕ) : ℝ) * z + (α : ℝ) / 6 = (Int.fract (2 * z) + (α : ℝ) / 6) + (⌊2 * z⌋ : ℝ) := by
        have := Int.floor_add_fract (2 * z); push_cast; linarith
      rw [h, Int.fract_add_intCast]
    have hs4 : 1 / 6 ≤ Int.fract (((2 : ℕ) : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract (((2 : ℕ) : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6 := by
      rw [hrw_gen x4]; by_contra h4; exact hnb (Or.inl ((not_safe_shift6_iff hv4_0 hv4_1 α h1 h5).mp h4))
    have hs5 : 1 / 6 ≤ Int.fract (((2 : ℕ) : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract (((2 : ℕ) : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6 := by
      rw [hrw_gen x5]; by_contra h5'; exact hnb (Or.inr ((not_safe_shift6_iff hv5_0 hv5_1 α h1 h5).mp h5'))
    have hs2 : 1 / 6 ≤ Int.fract (((2 : ℕ) : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (((2 : ℕ) : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6 := by
      have h : ((2 : ℕ) : ℝ) * x2 + 2 * (α : ℝ) / 6 = (v2 + 2 * (α : ℝ) / 6) + (⌊2 * x2⌋ : ℝ) := by
        dsimp [v2]; have := Int.floor_add_fract (2 * x2); linarith
      rwa [h, Int.fract_add_intCast]
    exact hn1 2 (by omega) (by omega) α h1 h5 ⟨hs4, hs5, hs2⟩
  have hv_diff : 1 / 6 < v4 - v5 ∧ v4 - v5 < 1 / 3 := by
    rcases hv_diff_or with hgood | ⟨hgt23, hlt56⟩
    · exact hgood
    · exfalso
      rcases u2_safe_subset v2 hv2_0 hv2_1 with hs1245 | hs134 | hs235
      · have b2 := hbad2 2 (by omega) (by omega) (hs1245 2 (Or.inr (Or.inl rfl)))
        have b4 := hbad2 4 (by omega) (by omega) (hs1245 4 (Or.inr (Or.inr (Or.inl rfl))))
        push_cast at b2 b4
        rcases b2 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      · have b3 := hbad2 3 (by omega) (by omega) (hs134 3 (Or.inr (Or.inl rfl)))
        push_cast at b3; rcases b3 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      · have b3 := hbad2 3 (by omega) (by omega) (hs235 3 (Or.inr (Or.inl rfl)))
        push_cast at b3; rcases b3 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  rcases u2_safe_subset v2 hv2_0 hv2_1 with hs1245 | hs134 | hs235
  · have b1 := hbad2 1 (by omega) (by omega) (hs1245 1 (Or.inl rfl))
    have b5 := hbad2 5 (by omega) (by omega) (hs1245 5 (Or.inr (Or.inr (Or.inr rfl))))
    push_cast at b1 b5
    rcases b1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases b5 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  · have b1 := hbad2 1 (by omega) (by omega) (hs134 1 (Or.inl rfl))
    have b4 := hbad2 4 (by omega) (by omega) (hs134 4 (Or.inr (Or.inr rfl)))
    push_cast at b1 b4
    have hv45 : 2 / 3 < v4 ∧ v4 < 5 / 6 ∧ 1 / 3 < v5 ∧ v5 < 1 / 2 := by
      rcases b1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases b4 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hv2_mid : 1 / 6 < v2 ∧ v2 < 1 / 2 := by
      have hv2_not5 : ¬ (1 / 6 ≤ Int.fract (v2 + 2 * ((5 : ℕ) : ℝ) / 6) ∧ Int.fract (v2 + 2 * ((5 : ℕ) : ℝ) / 6) ≤ 5 / 6) := by
        intro hs5
        have b5 := hbad2 5 (by omega) (by omega) hs5
        push_cast at b5; rcases b5 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      constructor
      · by_contra hle
        exact hv2_not5 (fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith))
      · by_contra hge
        exact hv2_not5 (fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 2 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith))
    exact hboth (Or.inr (lemma_6_1_case_A x2 x4 x5 hx2_0 hx2_1 hx4_0 hx4_1 hx5_0 hx5_1 hx45_close
      ⟨hv45.1, hv45.2.1⟩ ⟨hv45.2.2.1, hv45.2.2.2⟩ hv2_mid))
  · have b2 := hbad2 2 (by omega) (by omega) (hs235 2 (Or.inl rfl))
    have b5 := hbad2 5 (by omega) (by omega) (hs235 5 (Or.inr (Or.inr rfl)))
    push_cast at b2 b5
    have hv45 : 1 / 2 < v4 ∧ v4 < 2 / 3 ∧ 1 / 6 < v5 ∧ v5 < 1 / 3 := by
      rcases b2 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases b5 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hv2_hi : 1 / 2 < v2 ∧ v2 < 5 / 6 := by
      have hv2_not1 : ¬ (1 / 6 ≤ Int.fract (v2 + 2 * ((1 : ℕ) : ℝ) / 6) ∧ Int.fract (v2 + 2 * ((1 : ℕ) : ℝ) / 6) ≤ 5 / 6) := by
        intro hs1
        have b1 := hbad2 1 (by omega) (by omega) hs1
        push_cast at b1; rcases b1 with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
      constructor
      · by_contra hle
        exact hv2_not1 (fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 0 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith))
      · by_contra hge
        exact hv2_not1 (fract_mem_Icc_of_int _ (1 / 6) (5 / 6) 1 (by norm_num) (by norm_num) (by push_cast; linarith) (by push_cast; linarith))
    exact hboth (lemma_6_1_case_B x2 x4 x5 hx2_0 hx2_1 hx4_0 hx4_1 hx5_0 hx5_1 hx45_close
      ⟨hv45.1, hv45.2.1⟩ ⟨hv45.2.2.1, hv45.2.2.2⟩ hv2_hi)

lemma renault_lemma_6_1 (x2 x4 x5 : ℝ)
    (hx2_0 : 0 ≤ x2) (hx2_1 : x2 < 1)
    (hx4_0 : 0 ≤ x4) (hx4_1 : x4 < 1)
    (hx5_0 : 0 ≤ x5) (hx5_1 : x5 < 1) :
    (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
      (1 / 6 ≤ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6)) ∨
    (∃ α : ℕ, 1 ≤ α ∧ α ≤ 4 ∧
      (1 / 6 < Int.fract (x4 + (α : ℝ) / 6) ∧ Int.fract (x4 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x5 + (α : ℝ) / 6) ∧ Int.fract (x5 + (α : ℝ) / 6) < 5 / 6) ∧
      (1 / 6 < Int.fract (x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (x2 + 2 * (α : ℝ) / 6) < 5 / 6)) := by
  rcases le_or_gt (Int.fract (2 * x5)) (Int.fract (2 * x4)) with hle | hgt
  · exact lemma_6_1_ordered x2 x4 x5 hx2_0 hx2_1 hx4_0 hx4_1 hx5_0 hx5_1 hle
  · rcases lemma_6_1_ordered x2 x5 x4 hx2_0 hx2_1 hx5_0 hx5_1 hx4_0 hx4_1 hgt.le with
      ⟨lam, hl2, hl5, α, ha1, ha5, hs5, hs4, hs2⟩ | ⟨α, ha1, ha4, hs5, hs4, hs2⟩
    · exact Or.inl ⟨lam, hl2, hl5, α, ha1, ha5, hs4, hs5, hs2⟩
    · exact Or.inr ⟨α, ha1, ha4, hs4, hs5, hs2⟩


end
end RenaultLem61



namespace RenaultSec56

noncomputable section

private abbrev circDist (x : ℝ) : ℝ := dist (x : UnitAddCircle) 0

private lemma fract_eq_sub_floor (x : ℝ) : Int.fract x = x - (⌊x⌋ : ℝ) := by
  linarith [Int.floor_add_fract x]

private lemma circDist_int_cast (z : ℤ) : ((z : ℝ) : UnitAddCircle) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

private lemma circDist_add_int (x : ℝ) (z : ℤ) : circDist (x + z) = circDist x := by
  dsimp [circDist]; rw [circDist_int_cast, add_zero]

private lemma circDist_sub_int (x : ℝ) (z : ℤ) : circDist (x - z) = circDist x := by
  have h : x - (z : ℝ) = x + ((-z : ℤ) : ℝ) := by push_cast; ring
  rw [h, circDist_add_int]

private lemma circDist_neg (x : ℝ) : circDist (-x) = circDist x := by
  dsimp [circDist]; rw [dist_zero_right, dist_zero_right, norm_neg]

private lemma circDist_fract (x : ℝ) : circDist (Int.fract x) = circDist x := by
  rw [fract_eq_sub_floor, circDist_sub_int]

private lemma circDist_nonneg (x : ℝ) : 0 ≤ circDist x := dist_nonneg

private lemma circDist_eq_min_fract (x : ℝ) :
    circDist x = min (Int.fract x) (1 - Int.fract x) := by
  rw [← circDist_fract]
  set f := Int.fract x
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  dsimp [circDist]
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  rcases le_or_gt f (1 / 2) with hle | hgt
  · rw [min_eq_left (by linarith)]
    rcases eq_or_lt_of_le hle with hfeq | hlt
    · rw [hfeq]
      have hle_half : |(1 / 2 : ℝ) - (round (1 / 2 : ℝ) : ℝ)| ≤ 1 / 2 := abs_sub_round (1 / 2)
      have hge_half : (1 / 2 : ℝ) ≤ |(1 / 2 : ℝ) - (round (1 / 2 : ℝ) : ℝ)| := by
        rcases le_or_gt (round (1 / 2 : ℝ)) 0 with hr0 | hr1
        · have : (round (1 / 2 : ℝ) : ℝ) ≤ 0 := by exact_mod_cast hr0
          exact le_trans (by linarith) (le_abs_self _)
        · have : (1 : ℝ) ≤ (round (1 / 2 : ℝ) : ℝ) := by exact_mod_cast hr1
          exact le_trans (by linarith) (neg_le_abs _)
      linarith
    · have hr0 : round f = 0 := by
        by_contra hne
        have h1 : (1 : ℝ) ≤ |(round f : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h2 : |f - (round f : ℝ)| ≤ 1 / 2 := abs_sub_round f
        have h3 : |(round f : ℝ)| ≤ |f - (round f : ℝ)| + |f| := by
          calc |(round f : ℝ)| = |((round f : ℝ) - f) + f| := by ring_nf
            _ ≤ |(round f : ℝ) - f| + |f| := abs_add_le _ _
            _ = |f - (round f : ℝ)| + |f| := by rw [abs_sub_comm]
        rw [abs_of_nonneg hf0] at h3; linarith
      rw [hr0, Int.cast_zero, sub_zero, abs_of_nonneg hf0]
  · rw [min_eq_right (by linarith)]
    have hr1 : round f = 1 := by
      by_contra hne
      have hdiff : (1 : ℤ) ≤ |round f - 1| := Int.one_le_abs (sub_ne_zero.mpr hne)
      have h1 : (1 : ℝ) ≤ |(round f : ℝ) - 1| := by exact_mod_cast hdiff
      have h2 : |f - (round f : ℝ)| ≤ 1 / 2 := abs_sub_round f
      have h3 : |(round f : ℝ) - 1| ≤ |f - (round f : ℝ)| + (1 - f) := by
        have hpos : |1 - f| = 1 - f := abs_of_nonneg (by linarith)
        calc |(round f : ℝ) - 1| = |((round f : ℝ) - f) + (f - 1)| := by ring_nf
          _ ≤ |(round f : ℝ) - f| + |f - 1| := abs_add_le _ _
          _ = |f - (round f : ℝ)| + |1 - f| := by rw [abs_sub_comm, abs_sub_comm f 1]
          _ = |f - (round f : ℝ)| + (1 - f) := by rw [hpos]
      linarith
    rw [hr1, Int.cast_one, abs_of_neg (by linarith)]; ring

private lemma circDist_ge_iff_fract (x δ : ℝ) :
    circDist x ≥ δ ↔ δ ≤ Int.fract x ∧ Int.fract x ≤ 1 - δ := by
  rw [ge_iff_le, circDist_eq_min_fract, le_min_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

private lemma circDist_gt_iff_fract (x δ : ℝ) :
    δ < circDist x ↔ δ < Int.fract x ∧ Int.fract x < 1 - δ := by
  rw [circDist_eq_min_fract, lt_min_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

private lemma circDist_eq_zero_iff_fract (x : ℝ) :
    circDist x = 0 ↔ Int.fract x = 0 := by
  rw [circDist_eq_min_fract]
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  constructor
  · intro h
    rcases min_cases (Int.fract x) (1 - Int.fract x) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> linarith
  · intro h
    rw [h, min_eq_left (by norm_num)]

private lemma fract_eq_sub_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) ≤ x) (h2 : x < (z : ℝ) + 1) :
    Int.fract x = x - (z : ℝ) := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  conv_lhs => rw [hrew]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_neg_of_pos {x : ℝ} (hx : 0 < Int.fract x) :
    Int.fract (-x) = 1 - Int.fract x := by
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  have h : -x = (1 - Int.fract x) + ((-⌊x⌋ - 1 : ℤ) : ℝ) := by
    have := Int.floor_add_fract x; push_cast; linarith
  conv_lhs => rw [h]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_add_fract (x y : ℝ) :
    Int.fract (x + y) = Int.fract (Int.fract x + Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mul_nat (lam : ℕ) (x : ℝ) :
    Int.fract ((lam : ℝ) * x) = Int.fract ((lam : ℝ) * Int.fract x) := by
  conv_lhs => rw [← Int.floor_add_fract x]
  have h : (lam : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) =
      (lam : ℝ) * Int.fract x + (((lam : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma circDist_mul_nat (lam : ℕ) (x : ℝ) :
    circDist ((lam : ℝ) * x) = circDist ((lam : ℝ) * Int.fract x) := by
  rw [circDist_eq_min_fract, circDist_eq_min_fract, fract_mul_nat]

private lemma fract_shift_dvd {l v : ℕ} (hl : 0 < l) (hdvd : l ∣ v) (t : ℝ) (m : ℤ) :
    Int.fract ((t + (m : ℝ) / (l : ℝ)) * (v : ℝ)) = Int.fract (t * (v : ℝ)) := by
  obtain ⟨q, rfl⟩ := hdvd
  have hl_ne : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : (t + (m : ℝ) / (l : ℝ)) * (((l * q : ℕ) : ℝ)) =
      t * (((l * q : ℕ) : ℝ)) + ((m * (q : ℤ) : ℤ) : ℝ) := by
    push_cast; field_simp [hl_ne]
  rw [h, Int.fract_add_intCast]

private lemma circDist_shift_dvd {l v : ℕ} (hl : 0 < l) (hdvd : l ∣ v) (t : ℝ) (m : ℤ) :
    circDist ((t + (m : ℝ) / (l : ℝ)) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  rw [circDist_eq_min_fract, circDist_eq_min_fract, fract_shift_dvd hl hdvd]

private lemma continuous_circDist_mul (v : ℝ) : Continuous (fun t : ℝ => circDist (t * v)) := by
  dsimp [circDist]
  exact (QuotientAddGroup.continuous_mk.comp (continuous_id.mul continuous_const)).dist continuous_const

private lemma circDist_periodic_nat (t : ℝ) (v : ℕ) (z : ℤ) :
    circDist ((t + (z : ℝ)) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  have h : (t + (z : ℝ)) * (v : ℝ) = t * (v : ℝ) + ((z * (v : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h, circDist_add_int]

private lemma exists_periodic_max {T : Set ℝ} {f : ℝ → ℝ}
    (hT_closed : IsClosed T)
    (hT_per : ∀ t : ℝ, ∀ z : ℤ, t + (z : ℝ) ∈ T ↔ t ∈ T)
    (hT_ne : T.Nonempty)
    (hf_cont : Continuous f)
    (hf_per : ∀ t : ℝ, ∀ z : ℤ, f (t + (z : ℝ)) = f t) :
    ∃ t_bar ∈ T, ∀ t ∈ T, f t ≤ f t_bar := by
  let K : Set ℝ := Set.Icc 0 1 ∩ T
  have hK_comp : IsCompact K := isCompact_Icc.inter_right hT_closed
  obtain ⟨t₀, ht₀⟩ := hT_ne
  have ht₀_fr_mem : Int.fract t₀ ∈ K := by
    refine ⟨⟨Int.fract_nonneg t₀, (Int.fract_lt_one t₀).le⟩, ?_⟩
    have h : Int.fract t₀ = t₀ + ((-⌊t₀⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h]; exact (hT_per t₀ (-⌊t₀⌋)).mpr ht₀
  obtain ⟨t_bar, ht_barK, hmax⟩ := hK_comp.exists_isMaxOn ⟨Int.fract t₀, ht₀_fr_mem⟩ hf_cont.continuousOn
  refine ⟨t_bar, ht_barK.2, fun t ht => ?_⟩
  have hfr_K : Int.fract t ∈ K := by
    refine ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
    have h : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h]; exact (hT_per t (-⌊t⌋)).mpr ht
  have hf_eq : f (Int.fract t) = f t := by
    have h : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h, hf_per]
  rw [← hf_eq]; exact hmax hfr_K

private lemma exists_pos_le_fin :
    ∀ (m : ℕ) (b₀ : ℝ), 0 < b₀ → ∀ (b : Fin m → ℝ), (∀ i, 0 < b i) →
      ∃ η : ℝ, 0 < η ∧ η ≤ b₀ ∧ ∀ i : Fin m, η ≤ b i := by
  intro m
  induction m with
  | zero => intro b₀ hb₀ _ _; exact ⟨b₀, hb₀, le_rfl, fun i => Fin.elim0 i⟩
  | succ m' ih =>
    intro b₀ hb₀ b hb
    obtain ⟨η₁, hη₁_pos, hη₁_le, hη₁_rest⟩ :=
      ih b₀ hb₀ (fun j => b (Fin.castSucc j)) (fun j => hb (Fin.castSucc j))
    refine ⟨min η₁ (b (Fin.last m')), lt_min hη₁_pos (hb (Fin.last m')),
      le_trans (min_le_left _ _) hη₁_le, ?_⟩
    intro i; refine Fin.lastCases (min_le_right _ _) (fun j => le_trans (min_le_left _ _) (hη₁_rest j)) i

private lemma exists_right_perturb {m : ℕ} (v : Fin (m + 1) → ℕ)
    (hv_pos : ∀ i, 0 < v i) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1 / 2)
    (s : ℝ)
    (hs0_pos : 0 < Int.fract (s * (v 0 : ℝ)))
    (hs0_lt : Int.fract (s * (v 0 : ℝ)) < δ)
    (hs_rest : ∀ i : Fin m, δ ≤ Int.fract (s * (v i.succ : ℝ)) ∧
      Int.fract (s * (v i.succ : ℝ)) < 1 - δ) :
    ∃ s' : ℝ, (∀ i : Fin m, circDist (s' * (v i.succ : ℝ)) ≥ δ) ∧
      circDist (s * (v 0 : ℝ)) < circDist (s' * (v 0 : ℝ)) := by
  have hv0_r : (0 : ℝ) < (v 0 : ℝ) := Nat.cast_pos.mpr (hv_pos 0)
  let gap0 : ℝ := (δ - Int.fract (s * (v 0 : ℝ))) / (2 * (v 0 : ℝ))
  have hgap0_pos : 0 < gap0 := div_pos (by linarith) (by positivity)
  let b : Fin m → ℝ := fun i =>
    ((1 - δ) - Int.fract (s * (v i.succ : ℝ))) / (2 * (v i.succ : ℝ))
  have hb_pos : ∀ i : Fin m, 0 < b i := by
    intro i
    have hvi : (0 : ℝ) < (v i.succ : ℝ) := Nat.cast_pos.mpr (hv_pos i.succ)
    have hlt := (hs_rest i).2
    exact div_pos (by linarith) (by positivity)
  obtain ⟨η, hη_pos, hη_gap0, hη_b⟩ := exists_pos_le_fin m gap0 hgap0_pos b hb_pos
  refine ⟨s + η, fun i => ?_, ?_⟩
  · obtain ⟨hlo, hhi⟩ := hs_rest i
    have hvi_pos : (0 : ℝ) < (v i.succ : ℝ) := Nat.cast_pos.mpr (hv_pos i.succ)
    have hηv_pos : 0 < η * (v i.succ : ℝ) := mul_pos hη_pos hvi_pos
    have hηv_hi : η * (v i.succ : ℝ) ≤ ((1 - δ) - Int.fract (s * (v i.succ : ℝ))) / 2 := by
      have h1 := mul_le_mul_of_nonneg_right (hη_b i) hvi_pos.le
      have h2 : b i * (v i.succ : ℝ) = ((1 - δ) - Int.fract (s * (v i.succ : ℝ))) / 2 := by
        dsimp [b]; field_simp [ne_of_gt hvi_pos]
      linarith
    have hfr_add : Int.fract ((s + η) * (v i.succ : ℝ)) =
        Int.fract (s * (v i.succ : ℝ)) + η * (v i.succ : ℝ) := by
      have hexp : (s + η) * (v i.succ : ℝ) =
          (Int.fract (s * (v i.succ : ℝ)) + η * (v i.succ : ℝ)) + (⌊s * (v i.succ : ℝ)⌋ : ℝ) := by
        have := Int.floor_add_fract (s * (v i.succ : ℝ)); linarith
      rw [hexp, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [circDist_ge_iff_fract, hfr_add]
    exact ⟨by linarith, by linarith⟩
  · have hηv0_pos : 0 < η * (v 0 : ℝ) := mul_pos hη_pos hv0_r
    have hηv0_le : η * (v 0 : ℝ) ≤ (δ - Int.fract (s * (v 0 : ℝ))) / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hη_gap0 hv0_r.le
      have h2 : gap0 * (v 0 : ℝ) = (δ - Int.fract (s * (v 0 : ℝ))) / 2 := by
        dsimp [gap0]; field_simp [ne_of_gt hv0_r]
      linarith
    have hfr0_add : Int.fract ((s + η) * (v 0 : ℝ)) =
        Int.fract (s * (v 0 : ℝ)) + η * (v 0 : ℝ) := by
      have hexp : (s + η) * (v 0 : ℝ) =
          (Int.fract (s * (v 0 : ℝ)) + η * (v 0 : ℝ)) + (⌊s * (v 0 : ℝ)⌋ : ℝ) := by
        have := Int.floor_add_fract (s * (v 0 : ℝ)); linarith
      rw [hexp, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [circDist_eq_min_fract, circDist_eq_min_fract, hfr0_add,
      min_eq_left (by linarith), min_eq_left (by linarith)]
    linarith

private lemma renault_maximizer_extract {m : ℕ} (hm : 1 ≤ m) (v : Fin (m + 1) → ℕ)
    (hv_pos : ∀ i, 0 < v i)
    (ht0_ex : ∃ t₀ : ℝ, ∀ i : Fin m, circDist (t₀ * (v i.succ : ℝ)) ≥ 1 / ((m + 1 : ℕ) : ℝ))
    (hfail : ¬ ∃ t : ℝ, ∀ i : Fin (m + 1), circDist (t * (v i : ℝ)) ≥ 1 / ((m + 2 : ℕ) : ℝ)) :
    ∃ t_bar : ℝ,
      (∀ i : Fin m, circDist (t_bar * (v i.succ : ℝ)) ≥ 1 / ((m + 2 : ℕ) : ℝ)) ∧
      0 < Int.fract (t_bar * (v 0 : ℝ)) ∧
      Int.fract (t_bar * (v 0 : ℝ)) < 1 / ((m + 2 : ℕ) : ℝ) ∧
      (∃ j : Fin m, Int.fract (t_bar * (v j.succ : ℝ)) = 1 - 1 / ((m + 2 : ℕ) : ℝ)) ∧
      (∀ t : ℝ, (∀ i : Fin m, circDist (t * (v i.succ : ℝ)) ≥ 1 / ((m + 2 : ℕ) : ℝ)) →
        circDist (t * (v 0 : ℝ)) ≤ Int.fract (t_bar * (v 0 : ℝ))) := by
  let δ : ℝ := 1 / ((m + 2 : ℕ) : ℝ)
  have hm2_pos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_half : δ < 1 / 2 := by
    dsimp [δ]; rw [div_lt_div_iff₀ hm2_pos (by norm_num)]
    have : (3 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ m + 2)
    linarith
  have hδ_lt_prev : δ < 1 / ((m + 1 : ℕ) : ℝ) := by
    dsimp [δ]; rw [div_lt_div_iff₀ hm2_pos hm1_pos]
    have : ((m + 1 : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 < m + 2)
    linarith
  let T : Set ℝ := {t : ℝ | ∀ i : Fin m, δ ≤ circDist (t * (v i.succ : ℝ))}
  have hT_eq : T = ⋂ i : Fin m, {t : ℝ | δ ≤ circDist (t * (v i.succ : ℝ))} := by ext t; simp [T]
  have hT_closed : IsClosed T := by
    rw [hT_eq]; exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_circDist_mul _)
  have hT_per : ∀ t : ℝ, ∀ z : ℤ, t + (z : ℝ) ∈ T ↔ t ∈ T := by
    intro t z; change (∀ i : Fin m, _) ↔ (∀ i : Fin m, _); simp only [circDist_periodic_nat]
  obtain ⟨t₀, ht₀⟩ := ht0_ex
  have ht₀_mem : t₀ ∈ T := fun i => le_trans hδ_lt_prev.le (ht₀ i)
  obtain ⟨t₁, ht₁_T, ht₁_max⟩ := exists_periodic_max hT_closed hT_per ⟨t₀, ht₀_mem⟩
    (continuous_circDist_mul (v 0 : ℝ)) (fun t z => circDist_periodic_nat t (v 0) z)
  have hmax_pos : 0 < circDist (t₁ * (v 0 : ℝ)) := by
    by_contra hle0
    have hzero : ∀ t ∈ T, circDist (t * (v 0 : ℝ)) = 0 := fun t ht =>
      le_antisymm (le_trans (ht₁_max t ht) (by linarith)) (circDist_nonneg _)
    let gap_prev : ℝ := 1 / ((m + 1 : ℕ) : ℝ) - δ
    have hgp_pos : 0 < gap_prev := by dsimp [gap_prev]; linarith
    have hv0_r : (0 : ℝ) < (v 0 : ℝ) := Nat.cast_pos.mpr (hv_pos 0)
    obtain ⟨η, hη_pos, hη_v0, hη_rest⟩ := exists_pos_le_fin m (1 / (2 * (v 0 : ℝ))) (by positivity)
      (fun i => gap_prev / (2 * (v i.succ : ℝ))) (fun i => by
        have : (0 : ℝ) < (v i.succ : ℝ) := Nat.cast_pos.mpr (hv_pos i.succ)
        positivity)
    have ht₀_zero : Int.fract (t₀ * (v 0 : ℝ)) = 0 :=
      (circDist_eq_zero_iff_fract _).mp (hzero t₀ ht₀_mem)
    have ht_eta_T : t₀ + η ∈ T := by
      intro i
      have hvi_r : (0 : ℝ) < (v i.succ : ℝ) := Nat.cast_pos.mpr (hv_pos i.succ)
      obtain ⟨hfr_lo, hfr_hi⟩ := (circDist_ge_iff_fract _ _).mp (ht₀ i)
      have hη_vi : η * (v i.succ : ℝ) ≤ gap_prev / 2 := by
        have h1 := mul_le_mul_of_nonneg_right (hη_rest i) hvi_r.le
        have h2 : (gap_prev / (2 * (v i.succ : ℝ))) * (v i.succ : ℝ) = gap_prev / 2 := by
          field_simp [ne_of_gt hvi_r]
        linarith
      have hη_vi_pos : 0 < η * (v i.succ : ℝ) := mul_pos hη_pos hvi_r
      have hfr_eq : Int.fract ((t₀ + η) * (v i.succ : ℝ)) =
          Int.fract (t₀ * (v i.succ : ℝ)) + η * (v i.succ : ℝ) := by
        have hexp : (t₀ + η) * (v i.succ : ℝ) =
            (Int.fract (t₀ * (v i.succ : ℝ)) + η * (v i.succ : ℝ)) + (⌊t₀ * (v i.succ : ℝ)⌋ : ℝ) := by
          have := Int.floor_add_fract (t₀ * (v i.succ : ℝ)); linarith
        rw [hexp, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      have hgoal : circDist ((t₀ + η) * (v i.succ : ℝ)) ≥ δ :=
        (circDist_ge_iff_fract _ _).mpr ⟨by rw [hfr_eq]; dsimp [gap_prev] at hη_vi; linarith,
          by rw [hfr_eq]; dsimp [gap_prev] at hη_vi; linarith⟩
      exact hgoal
    have hfr_eta0 : Int.fract ((t₀ + η) * (v 0 : ℝ)) = η * (v 0 : ℝ) := by
      have hη0_le : η * (v 0 : ℝ) ≤ 1 / 2 := by
        have h1 := mul_le_mul_of_nonneg_right hη_v0 hv0_r.le
        have h2 : (1 / (2 * (v 0 : ℝ))) * (v 0 : ℝ) = 1 / 2 := by field_simp [ne_of_gt hv0_r]
        linarith
      have hη0_pos : 0 < η * (v 0 : ℝ) := mul_pos hη_pos hv0_r
      have hexp : (t₀ + η) * (v 0 : ℝ) = η * (v 0 : ℝ) + (⌊t₀ * (v 0 : ℝ)⌋ : ℝ) := by
        have := Int.floor_add_fract (t₀ * (v 0 : ℝ)); rw [ht₀_zero] at this; linarith
      rw [hexp, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    have hzero_eta : Int.fract ((t₀ + η) * (v 0 : ℝ)) = 0 :=
      (circDist_eq_zero_iff_fract _).mp (hzero (t₀ + η) ht_eta_T)
    have : 0 < η * (v 0 : ℝ) := mul_pos hη_pos hv0_r
    linarith
  have hmax_lt_δ : circDist (t₁ * (v 0 : ℝ)) < δ := by
    by_contra hge; apply hfail
    refine ⟨t₁, fun i => Fin.cases (le_of_not_gt hge) (fun j => ht₁_T j) i⟩
  have ht₁_fr_cases : Int.fract (t₁ * (v 0 : ℝ)) < δ ∨ 1 - δ < Int.fract (t₁ * (v 0 : ℝ)) := by
    by_contra hboth
    have h1 : δ ≤ Int.fract (t₁ * (v 0 : ℝ)) := by by_contra h; exact hboth (Or.inl (lt_of_not_ge h))
    have h2 : Int.fract (t₁ * (v 0 : ℝ)) ≤ 1 - δ := by by_contra h; exact hboth (Or.inr (lt_of_not_ge h))
    have : circDist (t₁ * (v 0 : ℝ)) ≥ δ := (circDist_ge_iff_fract _ _).mpr ⟨h1, h2⟩
    linarith
  let t_bar : ℝ := if Int.fract (t₁ * (v 0 : ℝ)) < δ then t₁ else -t₁
  have ht_bar_T : t_bar ∈ T := by
    dsimp [t_bar]; split_ifs with h
    · exact ht₁_T
    · intro i; have hneg : (-t₁) * (v i.succ : ℝ) = -(t₁ * (v i.succ : ℝ)) := by ring
      rw [hneg, circDist_neg]; exact ht₁_T i
  have ht_bar_dist0 : circDist (t_bar * (v 0 : ℝ)) = circDist (t₁ * (v 0 : ℝ)) := by
    dsimp [t_bar]; split_ifs with h
    · rfl
    · have hneg : (-t₁) * (v 0 : ℝ) = -(t₁ * (v 0 : ℝ)) := by ring
      rw [hneg, circDist_neg]
  have ht_bar_fr0_pos : 0 < Int.fract (t_bar * (v 0 : ℝ)) := by
    by_contra hle
    have h0 : Int.fract (t_bar * (v 0 : ℝ)) = 0 := le_antisymm (le_of_not_gt hle) (Int.fract_nonneg _)
    have := (circDist_eq_zero_iff_fract _).mpr h0; linarith
  have ht_bar_fr0_lt : Int.fract (t_bar * (v 0 : ℝ)) < δ := by
    dsimp [t_bar]; split_ifs with h
    · exact h
    · rcases ht₁_fr_cases with hlt | hgt
      · exact absurd hlt h
      · have hpos1 : 0 < Int.fract (t₁ * (v 0 : ℝ)) := by linarith
        have hneg : (-t₁) * (v 0 : ℝ) = -(t₁ * (v 0 : ℝ)) := by ring
        rw [hneg, fract_neg_of_pos hpos1]; linarith
  have ht_bar_dist_eq_fr : circDist (t_bar * (v 0 : ℝ)) = Int.fract (t_bar * (v 0 : ℝ)) := by
    rw [circDist_eq_min_fract, min_eq_left (by linarith)]
  have hex_j : ∃ j : Fin m, Int.fract (t_bar * (v j.succ : ℝ)) = 1 - δ := by
    by_contra hnone
    have hs_rest : ∀ i : Fin m, δ ≤ Int.fract (t_bar * (v i.succ : ℝ)) ∧
        Int.fract (t_bar * (v i.succ : ℝ)) < 1 - δ := by
      intro i
      obtain ⟨hlo, hhi⟩ := (circDist_ge_iff_fract _ _).mp (ht_bar_T i)
      refine ⟨hlo, lt_of_le_of_ne hhi (fun heq => hnone ⟨i, heq⟩)⟩
    obtain ⟨s', hs'_T, hs'_gt⟩ :=
      exists_right_perturb v hv_pos δ hδ_pos hδ_lt_half t_bar ht_bar_fr0_pos ht_bar_fr0_lt hs_rest
    have hle := ht₁_max s' hs'_T; linarith
  refine ⟨t_bar, ht_bar_T, ht_bar_fr0_pos, ht_bar_fr0_lt, hex_j, fun t ht => ?_⟩
  rw [← ht_bar_dist_eq_fr, ht_bar_dist0]; exact ht₁_max t ht

/- ### Sign-Lift & Mod-6 Arithmetic Helpers -/

private lemma circDist_signed_fract (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (lam : ℕ) (x c : ℝ) :
    circDist ((lam : ℝ) * Int.fract ((ε : ℝ) * x) + c) =
      circDist ((lam : ℝ) * x + (ε : ℝ) * c) := by
  have h1 : (lam : ℝ) * Int.fract ((ε : ℝ) * x) + c =
      ((lam : ℝ) * ((ε : ℝ) * x) + c) - (((lam : ℤ) * ⌊(ε : ℝ) * x⌋ : ℤ) : ℝ) := by
    rw [fract_eq_sub_floor]; push_cast; ring
  rw [h1, circDist_sub_int]
  rcases hε with rfl | rfl
  · push_cast; ring_nf
  · have hneg : (lam : ℝ) * (((-1 : ℤ) : ℝ) * x) + c = -((lam : ℝ) * x + ((-1 : ℤ) : ℝ) * c) := by
      push_cast; ring
    rw [hneg, circDist_neg]

private lemma circDist_mul_gt_of_lt_sixth {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1 / 6)
    {lam : ℕ} (hl2 : 2 ≤ lam) (hl5 : lam ≤ 5) :
    f < circDist ((lam : ℝ) * f) := by
  have hl_lo : (2 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hl2
  have hl_hi : (lam : ℝ) ≤ 5 := by exact_mod_cast hl5
  have hfr : Int.fract ((lam : ℝ) * f) = (lam : ℝ) * f :=
    Int.fract_eq_self.mpr ⟨by nlinarith, by nlinarith⟩
  rw [circDist_eq_min_fract, hfr, lt_min_iff]
  exact ⟨by nlinarith, by nlinarith⟩

private lemma mod6_decomp_odd_not_dvd3 (v : ℕ) (hodd : ¬ 2 ∣ v) (hnot3 : ¬ 3 ∣ v) :
    ∃ (q : ℤ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (v : ℝ) = 6 * (q : ℝ) + (ε : ℝ) := by
  have hr : v % 6 = 1 ∨ v % 6 = 5 := by omega
  rcases hr with h1 | h5
  · refine ⟨(v / 6 : ℕ), 1, Or.inl rfl, ?_⟩
    have hdiv : 6 * (v / 6) + 1 = v := by rw [← h1]; exact Nat.div_add_mod v 6
    exact_mod_cast hdiv.symm
  · refine ⟨(v / 6 : ℕ) + 1, -1, Or.inr rfl, ?_⟩
    have hdiv : 6 * (v / 6) + 5 = v := by rw [← h5]; exact Nat.div_add_mod v 6
    have hz : (v : ℤ) = 6 * ((v / 6 : ℕ) + 1) + (-1) := by omega
    exact_mod_cast hz

private lemma mod6_decomp_even_not_dvd3 (v : ℕ) (heven : 2 ∣ v) (hnot3 : ¬ 3 ∣ v) :
    ∃ (q : ℤ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (v : ℝ) = 6 * (q : ℝ) + 2 * (ε : ℝ) := by
  have hr : v % 6 = 2 ∨ v % 6 = 4 := by omega
  rcases hr with h2 | h4
  · refine ⟨(v / 6 : ℕ), 1, Or.inl rfl, ?_⟩
    have hdiv : 6 * (v / 6) + 2 = v := by rw [← h2]; exact Nat.div_add_mod v 6
    have hz : (v : ℤ) = 6 * (v / 6 : ℕ) + 2 * 1 := by omega
    exact_mod_cast hz
  · refine ⟨(v / 6 : ℕ) + 1, -1, Or.inr rfl, ?_⟩
    have hdiv : 6 * (v / 6) + 4 = v := by rw [← h4]; exact Nat.div_add_mod v 6
    have hz : (v : ℤ) = 6 * ((v / 6 : ℕ) + 1) + 2 * (-1) := by omega
    exact_mod_cast hz

private lemma circDist_shift_sixth_odd (t : ℝ) (v : ℕ) (q ε m : ℤ)
    (hv : (v : ℝ) = 6 * (q : ℝ) + (ε : ℝ)) :
    circDist ((t + (m : ℝ) / 6) * (v : ℝ)) = circDist (t * (v : ℝ) + (ε : ℝ) * (m : ℝ) / 6) := by
  have h : (t + (m : ℝ) / 6) * (v : ℝ) =
      (t * (v : ℝ) + (ε : ℝ) * (m : ℝ) / 6) + ((m * q : ℤ) : ℝ) := by
    rw [hv]; push_cast; ring
  rw [h, circDist_add_int]

private lemma fract_shift_sixth_odd (t : ℝ) (v : ℕ) (q ε m : ℤ)
    (hv : (v : ℝ) = 6 * (q : ℝ) + (ε : ℝ)) :
    Int.fract ((t + (m : ℝ) / 6) * (v : ℝ)) = Int.fract (t * (v : ℝ) + (ε : ℝ) * (m : ℝ) / 6) := by
  have h : (t + (m : ℝ) / 6) * (v : ℝ) =
      (t * (v : ℝ) + (ε : ℝ) * (m : ℝ) / 6) + ((m * q : ℤ) : ℝ) := by
    rw [hv]; push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma circDist_shift_sixth_even (t : ℝ) (v : ℕ) (q ε m : ℤ)
    (hv : (v : ℝ) = 6 * (q : ℝ) + 2 * (ε : ℝ)) :
    circDist ((t + (m : ℝ) / 6) * (v : ℝ)) = circDist (t * (v : ℝ) + 2 * (ε : ℝ) * (m : ℝ) / 6) := by
  have h : (t + (m : ℝ) / 6) * (v : ℝ) =
      (t * (v : ℝ) + 2 * (ε : ℝ) * (m : ℝ) / 6) + ((m * q : ℤ) : ℝ) := by
    rw [hv]; push_cast; ring
  rw [h, circDist_add_int]

private lemma fract_shift_sixth_even (t : ℝ) (v : ℕ) (q ε m : ℤ)
    (hv : (v : ℝ) = 6 * (q : ℝ) + 2 * (ε : ℝ)) :
    Int.fract ((t + (m : ℝ) / 6) * (v : ℝ)) = Int.fract (t * (v : ℝ) + 2 * (ε : ℝ) * (m : ℝ) / 6) := by
  have h : (t + (m : ℝ) / 6) * (v : ℝ) =
      (t * (v : ℝ) + 2 * (ε : ℝ) * (m : ℝ) / 6) + ((m * q : ℤ) : ℝ) := by
    rw [hv]; push_cast; ring
  rw [h, Int.fract_add_intCast]

/- ### Renault Proposition 5.4: A Unique Even Speed (pages 5–6) -/

lemma renault_prop_5_4
    (h_lrc4 : ∀ u : Fin 4 → ℕ, (∀ i, 0 < u i) → ∃ t : ℝ, ∀ i, circDist (t * (u i : ℝ)) ≥ 1 / ((4 + 1 : ℕ) : ℝ))
    (h_lem51 : ∀ x : Fin 3 → ℝ, (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
      (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
        ∀ i : Fin 3, 1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
          Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6) ∨
      (∃ α : ℕ, (α = 1 ∨ α = 2 ∨ α = 4) ∧
        ∀ i : Fin 3, 1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧
          Int.fract (x i + (α : ℝ) / 6) < 5 / 6))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (hdvd6_0 : 6 ∣ v 0)
    (hodd : ∀ j : Fin 4, ¬ 2 ∣ v j.succ)
    (hnot3 : ∀ j : Fin 4, ¬ 3 ∣ v j.succ) :
    ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  by_contra hfail
  obtain ⟨t_bar, ht_safe, hf0_pos, hf0_lt, ⟨j₀, hj₀_eq⟩, hmax⟩ :=
    renault_maximizer_extract (m := 4) (by omega) v hv_pos
      (h_lrc4 (fun j => v j.succ) (fun j => hv_pos j.succ)) hfail
  have h16 : (1 : ℝ) / ((4 + 2 : ℕ) : ℝ) = 1 / 6 := by norm_num
  rw [h16] at ht_safe hf0_lt hj₀_eq hmax
  -- Swap j₀.succ to position 1 so runner 1 is at 5/6!
  let perm : Equiv.Perm (Fin 4) := Equiv.swap 0 j₀
  let w : Fin 5 → ℕ := Fin.cases (v 0) (fun j => v (perm j).succ)
  have hw_pos : ∀ i, 0 < w i := Fin.cases (hv_pos 0) (fun j => hv_pos _)
  have hw0 : w 0 = v 0 := rfl
  have hw1_fr : Int.fract (t_bar * (w 1 : ℝ)) = 5 / 6 := by
    change Int.fract (t_bar * (v (perm 0).succ : ℝ)) = 5 / 6
    simp only [perm, Equiv.swap_apply_left]; linarith
  have hw_max : ∀ t : ℝ, (∀ j : Fin 4, circDist (t * (w j.succ : ℝ)) ≥ 1 / 6) →
      circDist (t * (w 0 : ℝ)) ≤ Int.fract (t_bar * (w 0 : ℝ)) := by
    intro t ht; apply hmax t; intro j
    have := ht (perm.symm j)
    simpa [w, perm] using this
  obtain ⟨q1, ε1, hε1, hw1_mod⟩ := mod6_decomp_odd_not_dvd3 (w 1) (hodd (perm 0)) (hnot3 (perm 0))
  have hmod_rest : ∀ r : Fin 3, ∃ (qr εr : ℤ), (εr = 1 ∨ εr = -1) ∧
      (w r.succ.succ : ℝ) = 6 * (qr : ℝ) + (εr : ℝ) :=
    fun r => mod6_decomp_odd_not_dvd3 _ (hodd (perm r.succ)) (hnot3 (perm r.succ))
  let q_r : Fin 3 → ℤ := fun r => Classical.choose (hmod_rest r)
  let ε_r : Fin 3 → ℤ := fun r => Classical.choose (Classical.choose_spec (hmod_rest r))
  have hε_r : ∀ r, (ε_r r = 1 ∨ ε_r r = -1) ∧ (w r.succ.succ : ℝ) = 6 * (q_r r : ℝ) + (ε_r r : ℝ) :=
    fun r => Classical.choose_spec (Classical.choose_spec (hmod_rest r))
  -- Define t_tilde = t_bar + ε1 / 6: then fract(t_tilde * w 1) = 0 and fract(t_tilde * w 0) = fract(t_bar * w 0)!
  let t_tilde : ℝ := t_bar + (ε1 : ℝ) / 6
  have ht_tilde_w0 : Int.fract (t_tilde * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) :=
    fract_shift_dvd (by omega) hdvd6_0 t_bar ε1
  have ht_tilde_w1 : Int.fract (t_tilde * (w 1 : ℝ)) = 0 := by
    rw [fract_shift_sixth_odd t_bar (w 1) q1 ε1 ε1 hw1_mod, fract_add_fract, hw1_fr]
    have hsq : (ε1 : ℝ) * (ε1 : ℝ) / 6 = 1 / 6 := by rcases hε1 with rfl | rfl <;> norm_num
    have hf16 : Int.fract (1 / 6 : ℝ) = 1 / 6 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hsum1 : (5 / 6 : ℝ) + 1 / 6 = ((1 : ℤ) : ℝ) := by norm_num
    rw [hsq, hf16, hsum1, Int.fract_intCast]
  -- Sign factor σ = ε1: apply Lemma 5.1 to y_r = Int.fract ((ε1 * ε_r r) * (t_tilde * w r.succ.succ))!
  let δ_sign : Fin 3 → ℤ := fun r => ε1 * ε_r r
  have hδ_sign : ∀ r, δ_sign r = 1 ∨ δ_sign r = -1 := by
    intro r; dsimp [δ_sign]
    rcases hε1 with h1 | h1 <;> rcases (hε_r r).1 with h2 | h2 <;> rw [h1, h2] <;> simp
  let y : Fin 3 → ℝ := fun r => Int.fract ((δ_sign r : ℝ) * (t_tilde * (w r.succ.succ : ℝ)))
  rcases h_lem51 y (fun _ => Int.fract_nonneg _) (fun _ => Int.fract_lt_one _) with
    ⟨lam, hl2, hl5, α_raw, ha1, ha5, hgood1⟩ | ⟨α_raw, hα_set, hgood2⟩
  · -- Property (1) with lam ∈ [2..5]! Choose α = α_raw if ε1 = 1 else 6 - α_raw!
    let α : ℕ := if ε1 = 1 then α_raw else 6 - α_raw
    let s : ℝ := (lam : ℝ) * t_tilde + (α : ℝ) / 6
    have hcast_a : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
    have hs_all : ∀ j : Fin 4, circDist (s * (w j.succ : ℝ)) ≥ 1 / 6 := by
      intro j; refine Fin.cases ?_ ?_ j
      · -- w 1: s * w 1 = (lam * t_tilde + α / 6) * w 1
        dsimp [s]
        rw [hcast_a, circDist_shift_sixth_odd ((lam : ℝ) * t_tilde) (w 1) q1 ε1 (α : ℤ) hw1_mod]
        have hlam_w1 : circDist ((lam : ℝ) * t_tilde * (w 1 : ℝ) + (ε1 : ℝ) * ((α : ℤ) : ℝ) / 6) =
            circDist ((ε1 : ℝ) * (α : ℝ) / 6) := by
          have hexp : (lam : ℝ) * t_tilde * (w 1 : ℝ) =
              (lam : ℝ) * Int.fract (t_tilde * (w 1 : ℝ)) + (((lam : ℤ) * ⌊t_tilde * (w 1 : ℝ)⌋ : ℤ) : ℝ) := by
            rw [fract_eq_sub_floor]; push_cast; ring
          rw [hexp, ht_tilde_w1, mul_zero, zero_add]
          have h3 : (((lam : ℤ) * ⌊t_tilde * (w 1 : ℝ)⌋ : ℤ) : ℝ) + (ε1 : ℝ) * ((α : ℤ) : ℝ) / 6 =
              (ε1 : ℝ) * (α : ℝ) / 6 + (((lam : ℤ) * ⌊t_tilde * (w 1 : ℝ)⌋ : ℤ) : ℝ) := by push_cast; ring
          rw [h3, circDist_add_int]
        rw [hlam_w1]
        have hα_lo : (1 : ℝ) ≤ (α_raw : ℝ) := by exact_mod_cast ha1
        have hα_hi : (α_raw : ℝ) ≤ 5 := by exact_mod_cast ha5
        dsimp [α]; split_ifs with he1
        · rw [he1]; push_cast
          rw [circDist_ge_iff_fract, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
          exact ⟨by linarith, by linarith⟩
        · have he_neg : ε1 = -1 := hε1.resolve_left he1
          rw [he_neg, Nat.cast_sub (by omega : α_raw ≤ 6)]; push_cast
          have hneg_eq : ((-1 : ℝ) * (6 - (α_raw : ℝ)) / 6) = ((α_raw : ℝ) / 6) - ((1 : ℤ) : ℝ) := by push_cast; ring
          rw [hneg_eq, circDist_sub_int, circDist_ge_iff_fract, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
          exact ⟨by linarith, by linarith⟩
      · intro r
        dsimp [s]
        rw [hcast_a, circDist_shift_sixth_odd ((lam : ℝ) * t_tilde) (w r.succ.succ) (q_r r) (ε_r r) (α : ℤ) (hε_r r).2]
        have heq_d : circDist ((lam : ℝ) * t_tilde * (w r.succ.succ : ℝ) + (ε_r r : ℝ) * ((α : ℤ) : ℝ) / 6) =
            circDist ((lam : ℝ) * y r + (α_raw : ℝ) / 6) := by
          dsimp [y]
          rw [circDist_signed_fract (δ_sign r) (hδ_sign r) lam (t_tilde * (w r.succ.succ : ℝ)) ((α_raw : ℝ) / 6)]
          dsimp [α, δ_sign]; split_ifs with he1
          · rw [he1]; push_cast; ring_nf
          · have he_neg : ε1 = -1 := hε1.resolve_left he1
            rw [he_neg, Int.natCast_sub (by omega : α_raw ≤ 6)]
            have hrw : (lam : ℝ) * t_tilde * (w r.succ.succ : ℝ) + (ε_r r : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                ((lam : ℝ) * (t_tilde * (w r.succ.succ : ℝ)) + (((-1 : ℤ) * ε_r r : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                ((ε_r r : ℤ) : ℝ) := by push_cast; ring
            rw [hrw, circDist_add_int]
        rw [heq_d, circDist_ge_iff_fract]
        have := hgood1 r; exact ⟨this.1, by linarith [this.2]⟩
    -- Now circDist (s * w 0) = circDist (lam * fract(t_bar * w 0)) > fract(t_bar * w 0), contradiction!
    have hs_w0 : circDist (s * (w 0 : ℝ)) = circDist ((lam : ℝ) * Int.fract (t_bar * (w 0 : ℝ))) := by
      dsimp [s, w]
      dsimp [w] at ht_tilde_w0
      have h6 : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [hcast_a, h6, circDist_shift_dvd (by omega) hdvd6_0 ((lam : ℝ) * t_tilde) (α : ℤ),
        mul_assoc, circDist_mul_nat lam (t_tilde * (v 0 : ℝ)), ht_tilde_w0]
    have hgt := circDist_mul_gt_of_lt_sixth hf0_pos hf0_lt hl2 hl5
    have hle := hw_max s hs_all
    dsimp [w] at hs_w0 hle
    linarith
  · -- Property (2) with lam = 1 and α_raw ∈ {1, 2, 4}!
    let α : ℕ := if ε1 = 1 then α_raw else 6 - α_raw
    let s : ℝ := t_tilde + (α : ℝ) / 6
    have hcast_a : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
    have hα_bounds : 1 ≤ α_raw ∧ α_raw ≤ 4 := by rcases hα_set with rfl | rfl | rfl <;> omega
    -- Check s satisfies hypotheses of exists_right_perturb!
    have hs0_eq : Int.fract (s * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) := by
      dsimp [s, w]
      dsimp [w] at ht_tilde_w0
      have h6 : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
      rw [hcast_a, h6, fract_shift_dvd (by omega) hdvd6_0 t_tilde (α : ℤ), ht_tilde_w0]
    have hs_rest : ∀ j : Fin 4, 1 / 6 ≤ Int.fract (s * (w j.succ : ℝ)) ∧
        Int.fract (s * (w j.succ : ℝ)) < 1 - 1 / 6 := by
      intro j; refine Fin.cases ?_ ?_ j
      · -- w 1: fract(s * w 1) = α_raw / 6 ∈ {1/6, 2/6, 4/6} ⊂ [1/6, 5/6)!
        dsimp [s]
        rw [hcast_a, fract_shift_sixth_odd t_tilde (w 1) q1 ε1 (α : ℤ) hw1_mod,
          fract_add_fract, ht_tilde_w1, zero_add, Int.fract_fract]
        dsimp [α]; split_ifs with he1
        · rw [he1]; push_cast
          have h1 : (1 : ℝ) ≤ (α_raw : ℝ) := by exact_mod_cast hα_bounds.1
          have h4 : (α_raw : ℝ) ≤ 4 := by exact_mod_cast hα_bounds.2
          rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
          exact ⟨by linarith, by linarith⟩
        · have he_neg : ε1 = -1 := hε1.resolve_left he1
          rw [he_neg, Int.natCast_sub (by omega : α_raw ≤ 6)]; push_cast
          have h1 : (1 : ℝ) ≤ (α_raw : ℝ) := by exact_mod_cast hα_bounds.1
          have h4 : (α_raw : ℝ) ≤ 4 := by exact_mod_cast hα_bounds.2
          rw [fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]
          push_cast; exact ⟨by linarith, by linarith⟩
      · intro r
        -- Open safe > 1/6 for r.succ.succ!
        have hgt_sixth : 1 / 6 < circDist (s * (w r.succ.succ : ℝ)) := by
          dsimp [s]
          rw [hcast_a, circDist_shift_sixth_odd t_tilde (w r.succ.succ) (q_r r) (ε_r r) (α : ℤ) (hε_r r).2]
          have heq_d : circDist (t_tilde * (w r.succ.succ : ℝ) + (ε_r r : ℝ) * ((α : ℤ) : ℝ) / 6) =
              circDist ((1 : ℕ) * y r + (α_raw : ℝ) / 6) := by
            dsimp [y]
            rw [circDist_signed_fract (δ_sign r) (hδ_sign r) 1 (t_tilde * (w r.succ.succ : ℝ)) ((α_raw : ℝ) / 6)]
            dsimp [α, δ_sign]; split_ifs with he1
            · rw [he1]; push_cast; ring_nf
            · have he_neg : ε1 = -1 := hε1.resolve_left he1
              rw [he_neg, Int.natCast_sub (by omega : α_raw ≤ 6)]
              have hrw : t_tilde * (w r.succ.succ : ℝ) + (ε_r r : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                  (((1 : ℕ) : ℝ) * (t_tilde * (w r.succ.succ : ℝ)) + (((-1 : ℤ) * ε_r r : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                  ((ε_r r : ℤ) : ℝ) := by push_cast; ring
              rw [hrw, circDist_add_int]
          rw [heq_d, Nat.cast_one, one_mul, circDist_gt_iff_fract]
          have := hgood2 r; exact ⟨this.1, by linarith [this.2]⟩
        obtain ⟨glo, ghi⟩ := (circDist_gt_iff_fract _ _).mp hgt_sixth
        exact ⟨glo.le, ghi⟩
    obtain ⟨s', hs'_T, hs'_gt⟩ := exists_right_perturb w hw_pos (1 / 6) (by norm_num) (by norm_num)
      s (by rw [hs0_eq]; exact hf0_pos) (by rw [hs0_eq]; exact hf0_lt) hs_rest
    have hle := hw_max s' hs'_T
    have hs_dist0 : circDist (s * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) := by
      rw [circDist_eq_min_fract, hs0_eq, min_eq_left (by dsimp [w]; linarith)]
    linarith

/- ### Renault Proposition 6.6: Exactly Two Even Speeds (pages 7–8) -/

private lemma odd_sixth_circDist_ge (z : ℤ) (hz : Odd z) :
    circDist ((z : ℝ) / 6) ≥ 1 / 6 := by
  obtain ⟨k, rfl⟩ := hz
  let r : ℤ := (2 * k + 1) % 6
  let q : ℤ := (2 * k + 1) / 6
  have hdiv : 6 * q + r = 2 * k + 1 := by omega
  have hr_cases : r = 1 ∨ r = 3 ∨ r = 5 := by omega
  have hrew : ((2 * k + 1 : ℤ) : ℝ) / 6 = (r : ℝ) / 6 + (q : ℝ) := by
    have hc : ((2 * k + 1 : ℤ) : ℝ) = 6 * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    rw [hc]; ring
  rw [hrew, circDist_add_int, circDist_ge_iff_fract]
  rcases hr_cases with hr | hr | hr <;> rw [hr] <;> push_cast <;>
    rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩] <;> constructor <;> norm_num

lemma renault_prop_6_6
    (h_lrc4 : ∀ u : Fin 4 → ℕ, (∀ i, 0 < u i) → ∃ t : ℝ, ∀ i, circDist (t * (u i : ℝ)) ≥ 1 / ((4 + 1 : ℕ) : ℝ))
    (h_lem61 : ∀ x2 x4 x5 : ℝ, 0 ≤ x2 → x2 < 1 → 0 ≤ x4 → x4 < 1 → 0 ≤ x5 → x5 < 1 →
      (∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧ ∃ α : ℕ, 1 ≤ α ∧ α ≤ 5 ∧
        (1 / 6 ≤ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x4 + (α : ℝ) / 6) ≤ 5 / 6) ∧
        (1 / 6 ≤ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x5 + (α : ℝ) / 6) ≤ 5 / 6) ∧
        (1 / 6 ≤ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ∧ Int.fract ((lam : ℝ) * x2 + 2 * (α : ℝ) / 6) ≤ 5 / 6)) ∨
      (∃ α : ℕ, 1 ≤ α ∧ α ≤ 4 ∧
        (1 / 6 < Int.fract (x4 + (α : ℝ) / 6) ∧ Int.fract (x4 + (α : ℝ) / 6) < 5 / 6) ∧
        (1 / 6 < Int.fract (x5 + (α : ℝ) / 6) ∧ Int.fract (x5 + (α : ℝ) / 6) < 5 / 6) ∧
        (1 / 6 < Int.fract (x2 + 2 * (α : ℝ) / 6) ∧ Int.fract (x2 + 2 * (α : ℝ) / 6) < 5 / 6)))
    (h_lem64 : ∀ x : Fin 3 → ℝ, (∀ i, 1 / 6 ≤ x i) → (∀ i, x i ≤ 5 / 6) →
      (∀ i : Fin 3, 1 / 6 < Int.fract (2 * x i) ∧ Int.fract (2 * x i) < 5 / 6) ∨
      (∃ α : ℕ, (α = 1 ∨ α = 5) ∧
        ∀ i : Fin 3, 1 / 6 < Int.fract (x i + (α : ℝ) / 6) ∧ Int.fract (x i + (α : ℝ) / 6) < 5 / 6) ∨
      (∃ lam : ℕ, (lam = 3 ∨ lam = 5) ∧ ∃ α : ℕ, α ≤ 5 ∧
        ∀ i : Fin 3, 1 / 6 ≤ Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ∧
          Int.fract ((lam : ℝ) * x i + (α : ℝ) / 6) ≤ 5 / 6))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (hdvd6_0 : 6 ∣ v 0) (heven1 : 2 ∣ v 1)
    (hodd : ∀ r : Fin 3, ¬ 2 ∣ v r.succ.succ)
    (hnot3 : ∀ j : Fin 4, ¬ 3 ∣ v j.succ) :
    ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  by_contra hfail
  obtain ⟨t_bar, ht_safe, hf0_pos, hf0_lt, ⟨j₀, hj₀_eq⟩, hmax⟩ :=
    renault_maximizer_extract (m := 4) (by omega) v hv_pos
      (h_lrc4 (fun j => v j.succ) (fun j => hv_pos j.succ)) hfail
  have h16 : (1 : ℝ) / ((4 + 2 : ℕ) : ℝ) = 1 / 6 := by norm_num
  rw [h16] at ht_safe hf0_lt hj₀_eq hmax
  obtain ⟨q1, ε1, hε1, hv1_mod⟩ := mod6_decomp_even_not_dvd3 (v 1) heven1 (hnot3 0)
  refine Fin.cases (motive := fun j₀ : Fin 4 => Int.fract (t_bar * (v j₀.succ : ℝ)) = 1 - 1 / 6 → False)
    ?_ ?_ j₀ hj₀_eq
  · -- Subcase 1: j₀ = 0, so Int.fract (t_bar * v 1) = 5 / 6!
    intro hv1_fr
    change Int.fract (t_bar * (v 1 : ℝ)) = 1 - 1 / 6 at hv1_fr
    have hv1_fr' : Int.fract (t_bar * (v 1 : ℝ)) = 5 / 6 := by linarith
    have hmod_rest : ∀ r : Fin 3, ∃ (qr εr : ℤ), (εr = 1 ∨ εr = -1) ∧
        (v r.succ.succ : ℝ) = 6 * (qr : ℝ) + (εr : ℝ) :=
      fun r => mod6_decomp_odd_not_dvd3 _ (hodd r) (hnot3 r.succ)
    let q_r : Fin 3 → ℤ := fun r => Classical.choose (hmod_rest r)
    let ε_r : Fin 3 → ℤ := fun r => Classical.choose (Classical.choose_spec (hmod_rest r))
    have hε_r : ∀ r, (ε_r r = 1 ∨ ε_r r = -1) ∧ (v r.succ.succ : ℝ) = 6 * (q_r r : ℝ) + (ε_r r : ℝ) :=
      fun r => Classical.choose_spec (Classical.choose_spec (hmod_rest r))
    let y : Fin 3 → ℝ := fun r => Int.fract ((ε_r r : ℝ) * (t_bar * (v r.succ.succ : ℝ)))
    have hy_bounds : ∀ r : Fin 3, 1 / 6 ≤ y r ∧ y r ≤ 5 / 6 := by
      intro r
      obtain ⟨hlo, hhi⟩ := (circDist_ge_iff_fract _ _).mp (ht_safe r.succ)
      dsimp [y]
      rcases (hε_r r).1 with he | he <;> rw [he]
      · simp only [Int.cast_one, one_mul]; exact ⟨hlo, by linarith⟩
      · have hneg : ((-1 : ℤ) : ℝ) * (t_bar * (v r.succ.succ : ℝ)) = -(t_bar * (v r.succ.succ : ℝ)) := by push_cast; ring
        rw [hneg, fract_neg_of_pos (by linarith)]; exact ⟨by linarith, by linarith⟩
    rcases h_lem64 y (fun r => (hy_bounds r).1) (fun r => (hy_bounds r).2) with
      h64_1 | ⟨α, hα_15, h64_2⟩ | ⟨lam, hlam_35, α, hα5, h64_3⟩
    · -- (1) s = 2 * t_bar
      let s : ℝ := ((2 : ℕ) : ℝ) * t_bar
      have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      have hs_safe : ∀ j : Fin 4, circDist (s * (v j.succ : ℝ)) ≥ 1 / 6 := by
        intro j; refine Fin.cases ?_ ?_ j
        · change circDist (((2 : ℕ) : ℝ) * t_bar * (v 1 : ℝ)) ≥ 1 / 6
          rw [mul_assoc, circDist_mul_nat 2, hv1_fr', circDist_ge_iff_fract]
          push_cast; rw [fract_eq_sub_int (2 * (5 / 6 : ℝ)) 1 (by push_cast; linarith) (by push_cast; linarith)]
          push_cast; constructor <;> norm_num
        · intro r
          have hd : circDist (s * (v r.succ.succ : ℝ)) = circDist (((2 : ℕ) : ℝ) * y r) := by
            have h1 := circDist_signed_fract (ε_r r) (hε_r r).1 2 (t_bar * (v r.succ.succ : ℝ)) 0
            rw [add_zero, mul_zero, add_zero] at h1
            have h2 : s * (v r.succ.succ : ℝ) = ((2 : ℕ) : ℝ) * (t_bar * (v r.succ.succ : ℝ)) := by
              dsimp [s]; ring
            rw [h2]; exact h1.symm
          rw [hd, circDist_ge_iff_fract]; push_cast
          have := h64_1 r; exact ⟨this.1.le, by linarith [this.2]⟩
      have hs0 : circDist (s * (v 0 : ℝ)) = circDist (((2 : ℕ) : ℝ) * Int.fract (t_bar * (v 0 : ℝ))) := by
        have h2 : s * (v 0 : ℝ) = ((2 : ℕ) : ℝ) * (t_bar * (v 0 : ℝ)) := by dsimp [s]; ring
        rw [h2, circDist_mul_nat 2]
      have hgt := circDist_mul_gt_of_lt_sixth hf0_pos hf0_lt (lam := 2) (by omega) (by omega)
      have hle := hmax s hs_safe; linarith
    · -- (2) s = t_bar + α / 6 with α ∈ {1, 5}: right-perturb!
      let s : ℝ := t_bar + (α : ℝ) / 6
      have hs0_eq : Int.fract (s * (v 0 : ℝ)) = Int.fract (t_bar * (v 0 : ℝ)) := by
        have hca : (α : ℝ) / 6 = ((α : ℤ) : ℝ) / ((6 : ℕ) : ℝ) := by push_cast; norm_num
        dsimp [s]; rw [hca]; exact fract_shift_dvd (by omega) hdvd6_0 t_bar (α : ℤ)
      have hs_rest : ∀ j : Fin 4, 1 / 6 ≤ Int.fract (s * (v j.succ : ℝ)) ∧
          Int.fract (s * (v j.succ : ℝ)) < 1 - 1 / 6 := by
        intro j; refine Fin.cases ?_ ?_ j
        · change 1 / 6 ≤ Int.fract (s * (v 1 : ℝ)) ∧ Int.fract (s * (v 1 : ℝ)) < 1 - 1 / 6
          dsimp [s]
          have hca : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
          rw [hca, fract_shift_sixth_even t_bar (v 1) q1 ε1 (α : ℤ) hv1_mod, fract_add_fract, hv1_fr']
          rcases hε1 with rfl | rfl <;> rcases hα_15 with rfl | rfl <;> push_cast
          · have hf1 : Int.fract (2 * 1 * 1 / 6 : ℝ) = 1 / 3 := by
              rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
            rw [hf1, fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; constructor <;> norm_num
          · have hf1 : Int.fract (2 * 1 * 5 / 6 : ℝ) = 2 / 3 := by
              rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
            rw [hf1, fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; constructor <;> norm_num
          · have hf1 : Int.fract (2 * (-1) * 1 / 6 : ℝ) = 2 / 3 := by
              rw [fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
            rw [hf1, fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; constructor <;> norm_num
          · have hf1 : Int.fract (2 * (-1) * 5 / 6 : ℝ) = 1 / 3 := by
              rw [fract_eq_sub_int _ (-2) (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
            rw [hf1, fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; constructor <;> norm_num
        · intro r
          have hgt_sixth : 1 / 6 < circDist (s * (v r.succ.succ : ℝ)) := by
            dsimp [s]
            have hca : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
            rw [hca, circDist_shift_sixth_odd t_bar (v r.succ.succ) (q_r r) (ε_r r) (α : ℤ) (hε_r r).2]
            have hd := circDist_signed_fract (ε_r r) (hε_r r).1 1 (t_bar * (v r.succ.succ : ℝ)) ((α : ℝ) / 6)
            push_cast at hd; rw [one_mul, one_mul] at hd
            have hmul_eq : t_bar * (v r.succ.succ : ℝ) + (ε_r r : ℝ) * ((α : ℤ) : ℝ) / 6 =
                t_bar * (v r.succ.succ : ℝ) + (ε_r r : ℝ) * ((α : ℝ) / 6) := by push_cast; ring
            rw [hmul_eq, ← hd, circDist_gt_iff_fract]
            have := h64_2 r; exact ⟨this.1, by linarith [this.2]⟩
          obtain ⟨glo, ghi⟩ := (circDist_gt_iff_fract _ _).mp hgt_sixth
          exact ⟨glo.le, ghi⟩
      obtain ⟨s', hs'_T, hs'_gt⟩ := exists_right_perturb v hv_pos (1 / 6) (by norm_num) (by norm_num)
        s (by rw [hs0_eq]; exact hf0_pos) (by rw [hs0_eq]; exact hf0_lt) hs_rest
      have hle := hmax s' hs'_T
      have hs_dist0 : circDist (s * (v 0 : ℝ)) = Int.fract (t_bar * (v 0 : ℝ)) := by
        rw [circDist_eq_min_fract, hs0_eq, min_eq_left (by linarith)]
      linarith
    · -- (3) s = lam * t_bar + α / 6 with lam ∈ {3, 5}, α ≤ 5
      let s : ℝ := (lam : ℝ) * t_bar + (α : ℝ) / 6
      have hs_safe : ∀ j : Fin 4, circDist (s * (v j.succ : ℝ)) ≥ 1 / 6 := by
        intro j; refine Fin.cases ?_ ?_ j
        · change circDist (s * (v 1 : ℝ)) ≥ 1 / 6
          dsimp [s]
          have hca : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
          rw [hca, circDist_shift_sixth_even ((lam : ℝ) * t_bar) (v 1) q1 ε1 (α : ℤ) hv1_mod]
          have hexp : (lam : ℝ) * t_bar * (v 1 : ℝ) + 2 * (ε1 : ℝ) * ((α : ℤ) : ℝ) / 6 =
              (((5 * (lam : ℤ) + 2 * ε1 * (α : ℤ) : ℤ) : ℝ) / 6) +
              (((lam : ℤ) * ⌊t_bar * (v 1 : ℝ)⌋ : ℤ) : ℝ) := by
            have hf := Int.floor_add_fract (t_bar * (v 1 : ℝ))
            rw [hv1_fr'] at hf
            have ht_eq : t_bar * (v 1 : ℝ) = (⌊t_bar * (v 1 : ℝ)⌋ : ℝ) + 5 / 6 := by linarith
            conv_lhs => rw [mul_assoc, ht_eq]
            push_cast; ring
          rw [hexp, circDist_add_int]
          apply odd_sixth_circDist_ge
          rcases hlam_35 with rfl | rfl
          · exact ⟨7 + ε1 * (α : ℤ), by push_cast; ring⟩
          · exact ⟨12 + ε1 * (α : ℤ), by push_cast; ring⟩
        · intro r
          dsimp [s]
          have hca : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
          rw [hca, circDist_shift_sixth_odd ((lam : ℝ) * t_bar) (v r.succ.succ) (q_r r) (ε_r r) (α : ℤ) (hε_r r).2]
          have hd := circDist_signed_fract (ε_r r) (hε_r r).1 lam (t_bar * (v r.succ.succ : ℝ)) ((α : ℝ) / 6)
          have hmul_assoc : (lam : ℝ) * (t_bar * (v r.succ.succ : ℝ)) + (ε_r r : ℝ) * ((α : ℝ) / 6) =
              (lam : ℝ) * t_bar * (v r.succ.succ : ℝ) + (ε_r r : ℝ) * ((α : ℤ) : ℝ) / 6 := by push_cast; ring
          rw [← hmul_assoc, ← hd, circDist_ge_iff_fract]
          have := h64_3 r; exact ⟨this.1, by linarith [this.2]⟩
      have hl2 : 2 ≤ lam := by rcases hlam_35 with rfl | rfl <;> omega
      have hl5 : lam ≤ 5 := by rcases hlam_35 with rfl | rfl <;> omega
      have hs0 : circDist (s * (v 0 : ℝ)) = circDist ((lam : ℝ) * Int.fract (t_bar * (v 0 : ℝ))) := by
        have hca : (α : ℝ) / 6 = ((α : ℤ) : ℝ) / ((6 : ℕ) : ℝ) := by push_cast; norm_num
        dsimp [s]; rw [hca, circDist_shift_dvd (by omega) hdvd6_0 ((lam : ℝ) * t_bar) (α : ℤ),
          mul_assoc, circDist_mul_nat lam]
      have hgt := circDist_mul_gt_of_lt_sixth hf0_pos hf0_lt hl2 hl5
      have hle := hmax s hs_safe; linarith
  · -- Subcase 2: j₀ = r₀.succ (one of the 3 odd speeds is at 5/6!)
    intro r₀ hr₀_fr
    let perm3 : Equiv.Perm (Fin 3) := Equiv.swap 0 r₀
    let w : Fin 5 → ℕ := Fin.cases (v 0) (Fin.cases (v 1) (fun r => v (perm3 r).succ.succ))
    have hw_pos : ∀ i, 0 < w i := Fin.cases (hv_pos 0) (Fin.cases (hv_pos 1) (fun r => hv_pos _))
    have hw2_fr : Int.fract (t_bar * (w 2 : ℝ)) = 5 / 6 := by
      change Int.fract (t_bar * (v (perm3 0).succ.succ : ℝ)) = 5 / 6
      simp only [perm3, Equiv.swap_apply_left]; linarith
    have hw_max : ∀ t : ℝ, (∀ j : Fin 4, circDist (t * (w j.succ : ℝ)) ≥ 1 / 6) →
        circDist (t * (w 0 : ℝ)) ≤ Int.fract (t_bar * (w 0 : ℝ)) := by
      intro t ht; apply hmax t; intro j
      refine Fin.cases (ht 0) (fun r => ?_) j
      have := ht (perm3.symm r).succ
      simpa [w, perm3] using this
    obtain ⟨q2, ε2, hε2, hw2_mod⟩ := mod6_decomp_odd_not_dvd3 (w 2) (hodd (perm3 0)) (hnot3 (perm3 0).succ)
    obtain ⟨q3, ε3, hε3, hw3_mod⟩ := mod6_decomp_odd_not_dvd3 (w 3) (hodd (perm3 1)) (hnot3 (perm3 1).succ)
    obtain ⟨q4, ε4, hε4, hw4_mod⟩ := mod6_decomp_odd_not_dvd3 (w 4) (hodd (perm3 2)) (hnot3 (perm3 2).succ)
    let t_tilde : ℝ := t_bar + (ε2 : ℝ) / 6
    have ht_tilde_w0 : Int.fract (t_tilde * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) :=
      fract_shift_dvd (by omega) hdvd6_0 t_bar ε2
    have ht_tilde_w2 : Int.fract (t_tilde * (w 2 : ℝ)) = 0 := by
      rw [fract_shift_sixth_odd t_bar (w 2) q2 ε2 ε2 hw2_mod, fract_add_fract, hw2_fr]
      have hsq : (ε2 : ℝ) * (ε2 : ℝ) / 6 = 1 / 6 := by rcases hε2 with rfl | rfl <;> norm_num
      have hf16 : Int.fract (1 / 6 : ℝ) = 1 / 6 := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hsum1 : (5 / 6 : ℝ) + 1 / 6 = ((1 : ℤ) : ℝ) := by norm_num
      rw [hsq, hf16, hsum1, Int.fract_intCast]
    let δ1 : ℤ := ε2 * ε1; let δ3 : ℤ := ε2 * ε3; let δ4 : ℤ := ε2 * ε4
    have hδ1 : δ1 = 1 ∨ δ1 = -1 := by dsimp [δ1]; rcases hε2 with h|h <;> rcases hε1 with g|g <;> rw [h,g] <;> simp
    have hδ3 : δ3 = 1 ∨ δ3 = -1 := by dsimp [δ3]; rcases hε2 with h|h <;> rcases hε3 with g|g <;> rw [h,g] <;> simp
    have hδ4 : δ4 = 1 ∨ δ4 = -1 := by dsimp [δ4]; rcases hε2 with h|h <;> rcases hε4 with g|g <;> rw [h,g] <;> simp
    let x_even : ℝ := Int.fract ((δ1 : ℝ) * (t_tilde * (w 1 : ℝ)))
    let x_odd3 : ℝ := Int.fract ((δ3 : ℝ) * (t_tilde * (w 3 : ℝ)))
    let x_odd4 : ℝ := Int.fract ((δ4 : ℝ) * (t_tilde * (w 4 : ℝ)))
    rcases h_lem61 x_even x_odd3 x_odd4
      (Int.fract_nonneg _) (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
      (Int.fract_nonneg _) (Int.fract_lt_one _) with
      ⟨lam, hl2, hl5, α_raw, ha1, ha5, hg3, hg4, hg1⟩ | ⟨α_raw, ha1, ha4, hg3, hg4, hg1⟩
    · -- Property (1) with lam ∈ [2..5]
      let α : ℕ := if ε2 = 1 then α_raw else 6 - α_raw
      let s : ℝ := (lam : ℝ) * t_tilde + (α : ℝ) / 6
      have hcast_a : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
      -- Helper connecting (lam*t_tilde + α/6) for odd/even runners
      have hs_all : ∀ j : Fin 4, circDist (s * (w j.succ : ℝ)) ≥ 1 / 6 := by
        intro j
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with rfl | rfl | rfl | rfl
        · -- w 1 (even): 2 * ε1 * α / 6
          dsimp [s]; rw [hcast_a, circDist_shift_sixth_even ((lam : ℝ) * t_tilde) (w 1) q1 ε1 (α : ℤ) hv1_mod]
          have hd := circDist_signed_fract δ1 hδ1 lam (t_tilde * (w 1 : ℝ)) (2 * (α_raw : ℝ) / 6)
          have hrel : circDist ((lam : ℝ) * t_tilde * (w 1 : ℝ) + 2 * (ε1 : ℝ) * ((α : ℤ) : ℝ) / 6) =
              circDist ((lam : ℝ) * (t_tilde * (w 1 : ℝ)) + (δ1 : ℝ) * (2 * (α_raw : ℝ) / 6)) := by
            dsimp [α, δ1]; split_ifs with he2
            · rw [he2]; push_cast; ring_nf
            · have he_neg : ε2 = -1 := hε2.resolve_left he2
              rw [he_neg, Int.natCast_sub (by omega : α_raw ≤ 6)]
              have hrw : (lam : ℝ) * t_tilde * (w 1 : ℝ) + 2 * (ε1 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                  ((lam : ℝ) * (t_tilde * (w 1 : ℝ)) + (((-1 : ℤ) * ε1 : ℤ) : ℝ) * (2 * (α_raw : ℝ) / 6)) +
                  ((2 * ε1 : ℤ) : ℝ) := by push_cast; ring
              rw [hrw, circDist_add_int]
          rw [hrel, ← hd, circDist_ge_iff_fract]; exact ⟨hg1.1, by linarith [hg1.2]⟩
        · -- w 2 (at 0 at t_tilde)
          dsimp [s]; rw [hcast_a, circDist_shift_sixth_odd ((lam : ℝ) * t_tilde) (w 2) q2 ε2 (α : ℤ) hw2_mod]
          have hexp : (lam : ℝ) * t_tilde * (w 2 : ℝ) + (ε2 : ℝ) * ((α : ℤ) : ℝ) / 6 =
              (ε2 : ℝ) * (α : ℝ) / 6 + (((lam : ℤ) * ⌊t_tilde * (w 2 : ℝ)⌋ : ℤ) : ℝ) := by
            have hf := Int.floor_add_fract (t_tilde * (w 2 : ℝ)); rw [ht_tilde_w2] at hf
            have ht0 : t_tilde * (w 2 : ℝ) = (⌊t_tilde * (w 2 : ℝ)⌋ : ℝ) := by linarith
            conv_lhs => rw [mul_assoc, ht0]
            push_cast; ring
          rw [hexp, circDist_add_int]
          have h1r : (1 : ℝ) ≤ (α_raw : ℝ) := by exact_mod_cast ha1
          have h5r : (α_raw : ℝ) ≤ 5 := by exact_mod_cast ha5
          dsimp [α]; split_ifs with he2
          · rw [he2]; push_cast; rw [circDist_ge_iff_fract, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
            exact ⟨by linarith, by linarith⟩
          · rw [hε2.resolve_left he2, Nat.cast_sub (by omega : α_raw ≤ 6)]; push_cast
            have hn : (-1 : ℝ) * (6 - (α_raw : ℝ)) / 6 = (α_raw : ℝ) / 6 - ((1 : ℤ) : ℝ) := by push_cast; ring
            rw [hn, circDist_sub_int, circDist_ge_iff_fract, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
            exact ⟨by linarith, by linarith⟩
        · -- w 3
          dsimp [s]; rw [hcast_a, circDist_shift_sixth_odd ((lam : ℝ) * t_tilde) (w 3) q3 ε3 (α : ℤ) hw3_mod]
          have hd := circDist_signed_fract δ3 hδ3 lam (t_tilde * (w 3 : ℝ)) ((α_raw : ℝ) / 6)
          have hrel : circDist ((lam : ℝ) * t_tilde * (w 3 : ℝ) + (ε3 : ℝ) * ((α : ℤ) : ℝ) / 6) =
              circDist ((lam : ℝ) * (t_tilde * (w 3 : ℝ)) + (δ3 : ℝ) * ((α_raw : ℝ) / 6)) := by
            dsimp [α, δ3]; split_ifs with he2
            · rw [he2]; push_cast; ring_nf
            · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]
              have hrw : (lam : ℝ) * t_tilde * (w 3 : ℝ) + (ε3 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                  ((lam : ℝ) * (t_tilde * (w 3 : ℝ)) + (((-1 : ℤ) * ε3 : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                  ((ε3 : ℤ) : ℝ) := by push_cast; ring
              rw [hrw, circDist_add_int]
          rw [hrel, ← hd, circDist_ge_iff_fract]; exact ⟨hg3.1, by linarith [hg3.2]⟩
        · -- w 4
          dsimp [s]; rw [hcast_a, circDist_shift_sixth_odd ((lam : ℝ) * t_tilde) (w 4) q4 ε4 (α : ℤ) hw4_mod]
          have hd := circDist_signed_fract δ4 hδ4 lam (t_tilde * (w 4 : ℝ)) ((α_raw : ℝ) / 6)
          have hrel : circDist ((lam : ℝ) * t_tilde * (w 4 : ℝ) + (ε4 : ℝ) * ((α : ℤ) : ℝ) / 6) =
              circDist ((lam : ℝ) * (t_tilde * (w 4 : ℝ)) + (δ4 : ℝ) * ((α_raw : ℝ) / 6)) := by
            dsimp [α, δ4]; split_ifs with he2
            · rw [he2]; push_cast; ring_nf
            · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]
              have hrw : (lam : ℝ) * t_tilde * (w 4 : ℝ) + (ε4 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                  ((lam : ℝ) * (t_tilde * (w 4 : ℝ)) + (((-1 : ℤ) * ε4 : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                  ((ε4 : ℤ) : ℝ) := by push_cast; ring
              rw [hrw, circDist_add_int]
          rw [hrel, ← hd, circDist_ge_iff_fract]; exact ⟨hg4.1, by linarith [hg4.2]⟩
      have hs0 : circDist (s * (w 0 : ℝ)) = circDist ((lam : ℝ) * Int.fract (t_bar * (v 0 : ℝ))) := by
        have hca : (α : ℝ) / 6 = ((α : ℤ) : ℝ) / ((6 : ℕ) : ℝ) := by push_cast; norm_num
        dsimp [s, w]; dsimp [w] at ht_tilde_w0
        rw [hca, circDist_shift_dvd (by omega) hdvd6_0 ((lam : ℝ) * t_tilde) (α : ℤ),
          mul_assoc, circDist_mul_nat lam, ht_tilde_w0]
      have hgt := circDist_mul_gt_of_lt_sixth hf0_pos hf0_lt hl2 hl5
      have hle := hw_max s hs_all; dsimp [w] at hs0 hle; linarith
    · -- Property (2) with lam = 1 and 1 ≤ α_raw ≤ 4: right-perturb!
      let α : ℕ := if ε2 = 1 then α_raw else 6 - α_raw
      let s : ℝ := t_tilde + (α : ℝ) / 6
      have hcast_a : (α : ℝ) = ((α : ℤ) : ℝ) := by push_cast; rfl
      have hs0_eq : Int.fract (s * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) := by
        have hca : (α : ℝ) / 6 = ((α : ℤ) : ℝ) / ((6 : ℕ) : ℝ) := by push_cast; norm_num
        dsimp [s, w]; dsimp [w] at ht_tilde_w0
        rw [hca, fract_shift_dvd (by omega) hdvd6_0 t_tilde (α : ℤ), ht_tilde_w0]
      have hs_rest : ∀ j : Fin 4, 1 / 6 ≤ Int.fract (s * (w j.succ : ℝ)) ∧
          Int.fract (s * (w j.succ : ℝ)) < 1 - 1 / 6 := by
        intro j
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by fin_cases j <;> simp) with rfl | rfl | rfl | rfl
        · -- w 1: open safe > 1/6
          have hgt6 : 1 / 6 < circDist (s * (w 1 : ℝ)) := by
            dsimp [s]; rw [hcast_a, circDist_shift_sixth_even t_tilde (w 1) q1 ε1 (α : ℤ) hv1_mod]
            have hd := circDist_signed_fract δ1 hδ1 1 (t_tilde * (w 1 : ℝ)) (2 * (α_raw : ℝ) / 6)
            have hrel : circDist (t_tilde * (w 1 : ℝ) + 2 * (ε1 : ℝ) * ((α : ℤ) : ℝ) / 6) =
                circDist (((1 : ℕ) : ℝ) * (t_tilde * (w 1 : ℝ)) + (δ1 : ℝ) * (2 * (α_raw : ℝ) / 6)) := by
              dsimp [α, δ1]; split_ifs with he2
              · rw [he2]; push_cast; ring_nf
              · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]
                have hrw : t_tilde * (w 1 : ℝ) + 2 * (ε1 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                    (((1 : ℕ) : ℝ) * (t_tilde * (w 1 : ℝ)) + (((-1 : ℤ) * ε1 : ℤ) : ℝ) * (2 * (α_raw : ℝ) / 6)) +
                    ((2 * ε1 : ℤ) : ℝ) := by push_cast; ring
                rw [hrw, circDist_add_int]
            rw [hrel, ← hd, Nat.cast_one, one_mul, circDist_gt_iff_fract]
            exact ⟨hg1.1, by linarith [hg1.2]⟩
          obtain ⟨glo, ghi⟩ := (circDist_gt_iff_fract _ _).mp hgt6; exact ⟨glo.le, ghi⟩
        · -- w 2: fract ∈ {1/6, 2/6, 3/6, 4/6} ⊂ [1/6, 5/6)!
          dsimp [s]; rw [hcast_a, fract_shift_sixth_odd t_tilde (w 2) q2 ε2 (α : ℤ) hw2_mod,
            fract_add_fract, ht_tilde_w2, zero_add, Int.fract_fract]
          have h1r : (1 : ℝ) ≤ (α_raw : ℝ) := by exact_mod_cast ha1
          have h4r : (α_raw : ℝ) ≤ 4 := by exact_mod_cast ha4
          dsimp [α]; split_ifs with he2
          · rw [he2]; push_cast; rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
            exact ⟨by linarith, by linarith⟩
          · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]; push_cast
            rw [fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; exact ⟨by linarith, by linarith⟩
        · -- w 3: open safe > 1/6
          have hgt6 : 1 / 6 < circDist (s * (w 3 : ℝ)) := by
            dsimp [s]; rw [hcast_a, circDist_shift_sixth_odd t_tilde (w 3) q3 ε3 (α : ℤ) hw3_mod]
            have hd := circDist_signed_fract δ3 hδ3 1 (t_tilde * (w 3 : ℝ)) ((α_raw : ℝ) / 6)
            have hrel : circDist (t_tilde * (w 3 : ℝ) + (ε3 : ℝ) * ((α : ℤ) : ℝ) / 6) =
                circDist (((1 : ℕ) : ℝ) * (t_tilde * (w 3 : ℝ)) + (δ3 : ℝ) * ((α_raw : ℝ) / 6)) := by
              dsimp [α, δ3]; split_ifs with he2
              · rw [he2]; push_cast; ring_nf
              · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]
                have hrw : t_tilde * (w 3 : ℝ) + (ε3 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                    (((1 : ℕ) : ℝ) * (t_tilde * (w 3 : ℝ)) + (((-1 : ℤ) * ε3 : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                    ((ε3 : ℤ) : ℝ) := by push_cast; ring
                rw [hrw, circDist_add_int]
            rw [hrel, ← hd, Nat.cast_one, one_mul, circDist_gt_iff_fract]
            exact ⟨hg3.1, by linarith [hg3.2]⟩
          obtain ⟨glo, ghi⟩ := (circDist_gt_iff_fract _ _).mp hgt6; exact ⟨glo.le, ghi⟩
        · -- w 4: open safe > 1/6
          have hgt6 : 1 / 6 < circDist (s * (w 4 : ℝ)) := by
            dsimp [s]; rw [hcast_a, circDist_shift_sixth_odd t_tilde (w 4) q4 ε4 (α : ℤ) hw4_mod]
            have hd := circDist_signed_fract δ4 hδ4 1 (t_tilde * (w 4 : ℝ)) ((α_raw : ℝ) / 6)
            have hrel : circDist (t_tilde * (w 4 : ℝ) + (ε4 : ℝ) * ((α : ℤ) : ℝ) / 6) =
                circDist (((1 : ℕ) : ℝ) * (t_tilde * (w 4 : ℝ)) + (δ4 : ℝ) * ((α_raw : ℝ) / 6)) := by
              dsimp [α, δ4]; split_ifs with he2
              · rw [he2]; push_cast; ring_nf
              · rw [hε2.resolve_left he2, Int.natCast_sub (by omega : α_raw ≤ 6)]
                have hrw : t_tilde * (w 4 : ℝ) + (ε4 : ℝ) * ((((6 : ℕ) : ℤ) - (α_raw : ℤ) : ℤ) : ℝ) / 6 =
                    (((1 : ℕ) : ℝ) * (t_tilde * (w 4 : ℝ)) + (((-1 : ℤ) * ε4 : ℤ) : ℝ) * ((α_raw : ℝ) / 6)) +
                    ((ε4 : ℤ) : ℝ) := by push_cast; ring
                rw [hrw, circDist_add_int]
            rw [hrel, ← hd, Nat.cast_one, one_mul, circDist_gt_iff_fract]
            exact ⟨hg4.1, by linarith [hg4.2]⟩
          obtain ⟨glo, ghi⟩ := (circDist_gt_iff_fract _ _).mp hgt6; exact ⟨glo.le, ghi⟩
      obtain ⟨s', hs'_T, hs'_gt⟩ := exists_right_perturb w hw_pos (1 / 6) (by norm_num) (by norm_num)
        s (by rw [hs0_eq]; exact hf0_pos) (by rw [hs0_eq]; exact hf0_lt) hs_rest
      have hle := hw_max s' hs'_T
      have hs_dist0 : circDist (s * (w 0 : ℝ)) = Int.fract (t_bar * (w 0 : ℝ)) := by
        rw [circDist_eq_min_fract, hs0_eq, min_eq_left (by dsimp [w]; linarith)]
      linarith


end
end RenaultSec56



namespace RenaultSec34

noncomputable section

private abbrev circDist (x : ℝ) : ℝ := dist (x : UnitAddCircle) 0

private lemma fract_eq_sub_floor (x : ℝ) : Int.fract x = x - (⌊x⌋ : ℝ) := by
  linarith [Int.floor_add_fract x]

private lemma circDist_int_cast (z : ℤ) : ((z : ℝ) : UnitAddCircle) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact ⟨z, by simp⟩

private lemma circDist_add_int (x : ℝ) (z : ℤ) : circDist (x + z) = circDist x := by
  dsimp [circDist]; rw [circDist_int_cast, add_zero]

private lemma circDist_sub_int (x : ℝ) (z : ℤ) : circDist (x - z) = circDist x := by
  have h : x - (z : ℝ) = x + ((-z : ℤ) : ℝ) := by push_cast; ring
  rw [h, circDist_add_int]

private lemma circDist_neg (x : ℝ) : circDist (-x) = circDist x := by
  dsimp [circDist]; rw [dist_zero_right, dist_zero_right, norm_neg]

private lemma circDist_fract (x : ℝ) : circDist (Int.fract x) = circDist x := by
  rw [fract_eq_sub_floor, circDist_sub_int]

private lemma circDist_nonneg (x : ℝ) : 0 ≤ circDist x := dist_nonneg

private lemma circDist_eq_min_fract (x : ℝ) :
    circDist x = min (Int.fract x) (1 - Int.fract x) := by
  rw [← circDist_fract]
  set f := Int.fract x
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  dsimp [circDist]
  rw [dist_zero_right, UnitAddCircle.norm_eq]
  rcases le_or_gt f (1 / 2) with hle | hgt
  · rw [min_eq_left (by linarith)]
    rcases eq_or_lt_of_le hle with hfeq | hlt
    · rw [hfeq]
      have hle_half : |(1 / 2 : ℝ) - (round (1 / 2 : ℝ) : ℝ)| ≤ 1 / 2 := abs_sub_round (1 / 2)
      have hge_half : (1 / 2 : ℝ) ≤ |(1 / 2 : ℝ) - (round (1 / 2 : ℝ) : ℝ)| := by
        rcases le_or_gt (round (1 / 2 : ℝ)) 0 with hr0 | hr1
        · have : (round (1 / 2 : ℝ) : ℝ) ≤ 0 := by exact_mod_cast hr0
          exact le_trans (by linarith) (le_abs_self _)
        · have : (1 : ℝ) ≤ (round (1 / 2 : ℝ) : ℝ) := by exact_mod_cast hr1
          exact le_trans (by linarith) (neg_le_abs _)
      linarith
    · have hr0 : round f = 0 := by
        by_contra hne
        have h1 : (1 : ℝ) ≤ |(round f : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h2 : |f - (round f : ℝ)| ≤ 1 / 2 := abs_sub_round f
        have h3 : |(round f : ℝ)| ≤ |f - (round f : ℝ)| + |f| := by
          calc |(round f : ℝ)| = |((round f : ℝ) - f) + f| := by ring_nf
            _ ≤ |(round f : ℝ) - f| + |f| := abs_add_le _ _
            _ = |f - (round f : ℝ)| + |f| := by rw [abs_sub_comm]
        rw [abs_of_nonneg hf0] at h3; linarith
      rw [hr0, Int.cast_zero, sub_zero, abs_of_nonneg hf0]
  · rw [min_eq_right (by linarith)]
    have hr1 : round f = 1 := by
      by_contra hne
      have hdiff : (1 : ℤ) ≤ |round f - 1| := Int.one_le_abs (sub_ne_zero.mpr hne)
      have h1 : (1 : ℝ) ≤ |(round f : ℝ) - 1| := by exact_mod_cast hdiff
      have h2 : |f - (round f : ℝ)| ≤ 1 / 2 := abs_sub_round f
      have h3 : |(round f : ℝ) - 1| ≤ |f - (round f : ℝ)| + (1 - f) := by
        have hpos : |1 - f| = 1 - f := abs_of_nonneg (by linarith)
        calc |(round f : ℝ) - 1| = |((round f : ℝ) - f) + (f - 1)| := by ring_nf
          _ ≤ |(round f : ℝ) - f| + |f - 1| := abs_add_le _ _
          _ = |f - (round f : ℝ)| + |1 - f| := by rw [abs_sub_comm, abs_sub_comm f 1]
          _ = |f - (round f : ℝ)| + (1 - f) := by rw [hpos]
      linarith
    rw [hr1, Int.cast_one, abs_of_neg (by linarith)]; ring

private lemma circDist_ge_iff_fract (x δ : ℝ) :
    circDist x ≥ δ ↔ δ ≤ Int.fract x ∧ Int.fract x ≤ 1 - δ := by
  rw [ge_iff_le, circDist_eq_min_fract, le_min_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

private lemma circDist_gt_iff_fract (x δ : ℝ) :
    δ < circDist x ↔ δ < Int.fract x ∧ Int.fract x < 1 - δ := by
  rw [circDist_eq_min_fract, lt_min_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

private lemma circDist_eq_zero_iff_fract (x : ℝ) :
    circDist x = 0 ↔ Int.fract x = 0 := by
  rw [circDist_eq_min_fract]
  have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  constructor
  · intro h
    rcases min_cases (Int.fract x) (1 - Int.fract x) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> linarith
  · intro h
    rw [h, min_eq_left (by norm_num)]

private lemma fract_eq_sub_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) ≤ x) (h2 : x < (z : ℝ) + 1) :
    Int.fract x = x - (z : ℝ) := by
  have hrew : x = (x - (z : ℝ)) + (z : ℝ) := by ring
  conv_lhs => rw [hrew]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_mem_Icc_of_int (x a b : ℝ) (z : ℤ)
    (_ha : 0 ≤ a) (_hb : b < 1)
    (h1 : (z : ℝ) + a ≤ x) (h2 : x ≤ (z : ℝ) + b) :
    a ≤ Int.fract x ∧ Int.fract x ≤ b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma fract_mem_Ioo_of_int (x a b : ℝ) (z : ℤ)
    (_ha : 0 ≤ a) (_hb : b ≤ 1)
    (h1 : (z : ℝ) + a < x) (h2 : x < (z : ℝ) + b) :
    a < Int.fract x ∧ Int.fract x < b := by
  rw [fract_eq_sub_int x z (by linarith) (by linarith)]
  exact ⟨by linarith, by linarith⟩

private lemma circDist_ge_sixth_of_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) + 1 / 6 ≤ x) (h2 : x ≤ (z : ℝ) + 5 / 6) :
    circDist x ≥ 1 / 6 := by
  obtain ⟨g1, g2⟩ := fract_mem_Icc_of_int x (1 / 6) (5 / 6) z (by norm_num) (by norm_num) h1 h2
  exact (circDist_ge_iff_fract x (1 / 6)).mpr ⟨g1, by linarith⟩

private lemma circDist_gt_tenth_of_int (x : ℝ) (z : ℤ)
    (h1 : (z : ℝ) + 1 / 10 < x) (h2 : x < (z : ℝ) + 9 / 10) :
    1 / 10 < circDist x := by
  obtain ⟨g1, g2⟩ := fract_mem_Ioo_of_int x (1 / 10) (9 / 10) z (by norm_num) (by norm_num) h1 h2
  exact (circDist_gt_iff_fract x (1 / 10)).mpr ⟨g1, by linarith⟩

private lemma fract_neg_of_pos {x : ℝ} (hx : 0 < Int.fract x) :
    Int.fract (-x) = 1 - Int.fract x := by
  have hf1 : Int.fract x < 1 := Int.fract_lt_one x
  have h : -x = (1 - Int.fract x) + ((-⌊x⌋ - 1 : ℤ) : ℝ) := by
    have := Int.floor_add_fract x; push_cast; linarith
  conv_lhs => rw [h]
  rw [Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

private lemma fract_add_fract (x y : ℝ) :
    Int.fract (x + y) = Int.fract (Int.fract x + Int.fract y) := by
  conv_lhs => rw [← Int.floor_add_fract x, ← Int.floor_add_fract y]
  have h : ((⌊x⌋ : ℝ) + Int.fract x) + ((⌊y⌋ : ℝ) + Int.fract y) =
      (Int.fract x + Int.fract y) + ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma fract_mul_nat (lam : ℕ) (x : ℝ) :
    Int.fract ((lam : ℝ) * x) = Int.fract ((lam : ℝ) * Int.fract x) := by
  conv_lhs => rw [← Int.floor_add_fract x]
  have h : (lam : ℝ) * ((⌊x⌋ : ℝ) + Int.fract x) =
      (lam : ℝ) * Int.fract x + (((lam : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma circDist_mul_nat (lam : ℕ) (x : ℝ) :
    circDist ((lam : ℝ) * x) = circDist ((lam : ℝ) * Int.fract x) := by
  rw [circDist_eq_min_fract, circDist_eq_min_fract, fract_mul_nat]

private lemma fract_shift_dvd {l v : ℕ} (hl : 0 < l) (hdvd : l ∣ v) (t : ℝ) (m : ℤ) :
    Int.fract ((t + (m : ℝ) / (l : ℝ)) * (v : ℝ)) = Int.fract (t * (v : ℝ)) := by
  obtain ⟨q, rfl⟩ := hdvd
  have hl_ne : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : (t + (m : ℝ) / (l : ℝ)) * (((l * q : ℕ) : ℝ)) =
      t * (((l * q : ℕ) : ℝ)) + ((m * (q : ℤ) : ℤ) : ℝ) := by
    push_cast; field_simp [hl_ne]
  rw [h, Int.fract_add_intCast]

private lemma circDist_shift_dvd {l v : ℕ} (hl : 0 < l) (hdvd : l ∣ v) (t : ℝ) (m : ℤ) :
    circDist ((t + (m : ℝ) / (l : ℝ)) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  rw [circDist_eq_min_fract, circDist_eq_min_fract, fract_shift_dvd hl hdvd]

private lemma continuous_circDist_mul (v : ℝ) : Continuous (fun t : ℝ => circDist (t * v)) := by
  dsimp [circDist]
  exact (QuotientAddGroup.continuous_mk.comp (continuous_id.mul continuous_const)).dist continuous_const

private lemma circDist_periodic_nat (t : ℝ) (v : ℕ) (z : ℤ) :
    circDist ((t + (z : ℝ)) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  have h : (t + (z : ℝ)) * (v : ℝ) = t * (v : ℝ) + ((z * (v : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h, circDist_add_int]

private lemma fract_periodic_nat (t : ℝ) (v : ℕ) (z : ℤ) :
    Int.fract ((t + (z : ℝ)) * (v : ℝ)) = Int.fract (t * (v : ℝ)) := by
  have h : (t + (z : ℝ)) * (v : ℝ) = t * (v : ℝ) + ((z * (v : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

private lemma unitAddCircle_eq_iff_fract_eq (x r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((x : ℝ) : UnitAddCircle) = ((r : ℝ) : UnitAddCircle) ↔ Int.fract x = r := by
  constructor
  · intro heq
    have hzero : ((Int.fract x - r : ℝ) : UnitAddCircle) = 0 := by
      have hx : ((Int.fract x : ℝ) : UnitAddCircle) = ((x : ℝ) : UnitAddCircle) := by
        rw [fract_eq_sub_floor, QuotientAddGroup.mk_sub, circDist_int_cast, sub_zero]
      rw [QuotientAddGroup.mk_sub, hx, heq, sub_self]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hzero
    obtain ⟨z, hz⟩ := hzero
    have hz' : (z : ℝ) = Int.fract x - r := by simpa using hz
    have hf0 := Int.fract_nonneg x; have hf1 := Int.fract_lt_one x
    have hz0 : z = 0 := by
      have h1 : (-1 : ℤ) < z := by exact_mod_cast (show (-1 : ℝ) < (z : ℝ) by linarith)
      have h2 : z < (1 : ℤ) := by exact_mod_cast (show (z : ℝ) < 1 by linarith)
      omega
    rw [hz0, Int.cast_zero] at hz'; linarith
  · intro hfr
    rw [← hfr, fract_eq_sub_floor, QuotientAddGroup.mk_sub, circDist_int_cast, sub_zero]

private lemma exists_periodic_max {T : Set ℝ} {f : ℝ → ℝ}
    (hT_closed : IsClosed T)
    (hT_per : ∀ t : ℝ, ∀ z : ℤ, t + (z : ℝ) ∈ T ↔ t ∈ T)
    (hT_ne : T.Nonempty)
    (hf_cont : Continuous f)
    (hf_per : ∀ t : ℝ, ∀ z : ℤ, f (t + (z : ℝ)) = f t) :
    ∃ t_bar ∈ T, ∀ t ∈ T, f t ≤ f t_bar := by
  let K : Set ℝ := Set.Icc 0 1 ∩ T
  have hK_comp : IsCompact K := isCompact_Icc.inter_right hT_closed
  obtain ⟨t₀, ht₀⟩ := hT_ne
  have ht₀_fr_mem : Int.fract t₀ ∈ K := by
    refine ⟨⟨Int.fract_nonneg t₀, (Int.fract_lt_one t₀).le⟩, ?_⟩
    have h : Int.fract t₀ = t₀ + ((-⌊t₀⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h]; exact (hT_per t₀ (-⌊t₀⌋)).mpr ht₀
  obtain ⟨t_bar, ht_barK, hmax⟩ := hK_comp.exists_isMaxOn ⟨Int.fract t₀, ht₀_fr_mem⟩ hf_cont.continuousOn
  refine ⟨t_bar, ht_barK.2, fun t ht => ?_⟩
  have hfr_K : Int.fract t ∈ K := by
    refine ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
    have h : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h]; exact (hT_per t (-⌊t⌋)).mpr ht
  have hf_eq : f (Int.fract t) = f t := by
    have h : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [fract_eq_sub_floor]; push_cast; ring
    rw [h, hf_per]
  rw [← hf_eq]; exact hmax hfr_K

/- ### Renault Lemma 2.2 (page 2) -/

private lemma renault_lemma_2_2
    (h_lrc4 : ∀ u : Fin 4 → ℕ, (∀ i, 0 < u i) → ∃ t : ℝ, ∀ i, circDist (t * (u i : ℝ)) ≥ 1 / ((4 + 1 : ℕ) : ℝ))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (i₀ : Fin 5) (hlac : ∀ j : Fin 5, j ≠ i₀ → 5 * v j ≤ v i₀) :
    ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  let perm : Equiv.Perm (Fin 5) := Equiv.swap 0 i₀
  let u : Fin 5 → ℕ := fun i => v (perm i)
  have hu_pos : ∀ i, 0 < u i := fun i => hv_pos _
  have hu_lac : ∀ j : Fin 4, 5 * u j.succ ≤ u 0 := by
    intro j; dsimp [u, perm]
    rw [Equiv.swap_apply_left]
    refine hlac _ ?_
    intro heq
    have := perm.injective (heq.trans (Equiv.swap_apply_left 0 i₀).symm)
    exact Fin.succ_ne_zero j this
  obtain ⟨t₀, ht₀⟩ := h_lrc4 (fun j => u j.succ) (fun j => hu_pos j.succ)
  have h16 : (1 : ℝ) / ((5 + 1 : ℕ) : ℝ) = 1 / 6 := by norm_num
  have h15 : (1 : ℝ) / ((4 + 1 : ℕ) : ℝ) = 1 / 5 := by norm_num
  rw [h15] at ht₀
  suffices hex : ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (u i : ℝ)) ≥ 1 / 6 by
    obtain ⟨t, ht⟩ := hex
    refine ⟨t, fun i => ?_⟩
    rw [h16]; have := ht (perm.symm i); simpa [u] using this
  by_cases h0_ok : circDist (t₀ * (u 0 : ℝ)) ≥ 1 / 6
  · refine ⟨t₀, Fin.cases h0_ok (fun j => le_trans (by norm_num) (ht₀ j))⟩
  · have hlt : circDist (t₀ * (u 0 : ℝ)) < 1 / 6 := lt_of_not_ge h0_ok
    let t₁ : ℝ := if Int.fract (t₀ * (u 0 : ℝ)) < 1 / 6 then t₀ else -t₀
    have ht₁_rest : ∀ j : Fin 4, circDist (t₁ * (u j.succ : ℝ)) ≥ 1 / 5 := by
      intro j; dsimp [t₁]; split_ifs with h
      · exact ht₀ j
      · have hn : (-t₀) * (u j.succ : ℝ) = -(t₀ * (u j.succ : ℝ)) := by ring
        rw [hn, circDist_neg]; exact ht₀ j
    have ht₁_0 : Int.fract (t₁ * (u 0 : ℝ)) < 1 / 6 := by
      dsimp [t₁]; split_ifs with h
      · exact h
      · have hgt : 5 / 6 < Int.fract (t₀ * (u 0 : ℝ)) := by
          by_contra hle
          have := (circDist_ge_iff_fract (t₀ * (u 0 : ℝ)) (1 / 6)).mpr ⟨le_of_not_gt h, by linarith⟩
          linarith
        have hn : (-t₀) * (u 0 : ℝ) = -(t₀ * (u 0 : ℝ)) := by ring
        rw [hn, fract_neg_of_pos (by linarith)]; linarith
    have hu0_r : (0 : ℝ) < (u 0 : ℝ) := Nat.cast_pos.mpr (hu_pos 0)
    let δt : ℝ := (1 / 6 - Int.fract (t₁ * (u 0 : ℝ))) / (u 0 : ℝ)
    have hδt_pos : 0 < δt := div_pos (by linarith) hu0_r
    have hδt_le : δt ≤ 1 / (6 * (u 0 : ℝ)) := by
      dsimp [δt]; rw [div_le_div_iff₀ hu0_r (by positivity)]
      have := Int.fract_nonneg (t₁ * (u 0 : ℝ)); nlinarith
    refine ⟨t₁ + δt, Fin.cases ?_ ?_⟩
    · have hexp : (t₁ + δt) * (u 0 : ℝ) = (1 / 6 : ℝ) + (⌊t₁ * (u 0 : ℝ)⌋ : ℝ) := by
        have hf := Int.floor_add_fract (t₁ * (u 0 : ℝ))
        have hd : δt * (u 0 : ℝ) = 1 / 6 - Int.fract (t₁ * (u 0 : ℝ)) := div_mul_cancel₀ _ (ne_of_gt hu0_r)
        linarith
      rw [hexp, circDist_add_int, circDist_ge_iff_fract, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
      exact ⟨by norm_num, by norm_num⟩
    · intro j
      obtain ⟨hlo, hhi⟩ := (circDist_ge_iff_fract _ _).mp (ht₁_rest j)
      have huj_le : 5 * (u j.succ : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast hu_lac j
      have hstep_pos : 0 ≤ δt * (u j.succ : ℝ) := mul_nonneg hδt_pos.le (Nat.cast_nonneg _)
      have hstep_le : δt * (u j.succ : ℝ) ≤ 1 / 30 := by
        have h1 := mul_le_mul_of_nonneg_right hδt_le (Nat.cast_nonneg (u j.succ))
        have h2 : (1 / (6 * (u 0 : ℝ))) * (u j.succ : ℝ) ≤ 1 / 30 := by
          rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
      have hexp : (t₁ + δt) * (u j.succ : ℝ) =
          (Int.fract (t₁ * (u j.succ : ℝ)) + δt * (u j.succ : ℝ)) + (⌊t₁ * (u j.succ : ℝ)⌋ : ℝ) := by
        have := Int.floor_add_fract (t₁ * (u j.succ : ℝ)); linarith
      rw [hexp, circDist_add_int, circDist_ge_iff_fract,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      exact ⟨by linarith, by linarith⟩

/- ### Shift-by-1/3 Helpers & Renault Arguments 1, 2, 3 (pages 3–4) -/

private lemma shift_third_not_both_unsafe {v : ℕ} (hnot3 : ¬ 3 ∣ v) (t : ℝ)
    {l₁ l₂ : Fin 3} (hne : l₁ ≠ l₂) :
    circDist ((t + (l₁.val : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6 ∨
    circDist ((t + (l₂.val : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6 := by
  by_contra hboth
  have h1 : circDist ((t + (l₁.val : ℝ) / 3) * (v : ℝ)) < 1 / 6 :=
    lt_of_not_ge fun h => hboth (Or.inl h)
  have h2 : circDist ((t + (l₂.val : ℝ) / 3) * (v : ℝ)) < 1 / 6 :=
    lt_of_not_ge fun h => hboth (Or.inr h)
  -- Their difference on UnitAddCircle is ((l₁ - l₂) * v) / 3, which has circDist = 1 / 3!
  let x₁ : ℝ := (t + (l₁.val : ℝ) / 3) * (v : ℝ)
  let x₂ : ℝ := (t + (l₂.val : ℝ) / 3) * (v : ℝ)
  have hdiff_dist : circDist (x₁ - x₂) = 1 / 3 := by
    have hdiff : x₁ - x₂ = (((l₁.val : ℤ) - (l₂.val : ℤ)) * (v : ℤ) : ℝ) / 3 := by
      dsimp [x₁, x₂]; push_cast; ring
    let n : ℤ := ((l₁.val : ℤ) - (l₂.val : ℤ)) * (v : ℤ)
    have hn_not3 : n % 3 = 1 ∨ n % 3 = 2 := by
      have hv_mod : (v : ℤ) % 3 = 1 ∨ (v : ℤ) % 3 = 2 := by omega
      have hl_cases : (l₁.val : ℤ) - (l₂.val : ℤ) = 1 ∨ (l₁.val : ℤ) - (l₂.val : ℤ) = -1 ∨
          (l₁.val : ℤ) - (l₂.val : ℤ) = 2 ∨ (l₁.val : ℤ) - (l₂.val : ℤ) = -2 := by
        have := l₁.isLt; have := l₂.isLt
        have hv_ne : l₁.val ≠ l₂.val := fun h => hne (Fin.ext h)
        omega
      dsimp [n]
      rcases hl_cases with hl | hl | hl | hl <;> rw [hl] <;> rcases hv_mod with hv | hv <;> omega
    have hdiv : 3 * (n / 3) + (n % 3) = n := by omega
    have hrew : (n : ℝ) / 3 = ((n % 3 : ℤ) : ℝ) / 3 + ((n / 3 : ℤ) : ℝ) := by
      have hc : (n : ℝ) = 3 * ((n / 3 : ℤ) : ℝ) + ((n % 3 : ℤ) : ℝ) := by exact_mod_cast hdiv.symm
      rw [hc]; ring
    change circDist (x₁ - x₂) = 1 / 3
    have hdiff' : x₁ - x₂ = (n : ℝ) / 3 := by dsimp [n]; push_cast; exact hdiff
    rw [hdiff', hrew, circDist_add_int, circDist_eq_min_fract]
    rcases hn_not3 with hr | hr <;> rw [hr] <;> push_cast <;>
      rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] <;> norm_num
  -- Triangle inequality on UnitAddCircle: circDist (x₁ - x₂) ≤ circDist x₁ + circDist x₂!
  have htri : circDist (x₁ - x₂) ≤ circDist x₁ + circDist x₂ := by
    have hmk : ((x₁ - x₂ : ℝ) : UnitAddCircle) = (x₁ : UnitAddCircle) - (x₂ : UnitAddCircle) :=
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).map_sub x₁ x₂
    change dist ((x₁ - x₂ : ℝ) : UnitAddCircle) 0 ≤
      dist (x₁ : UnitAddCircle) 0 + dist (x₂ : UnitAddCircle) 0
    rw [hmk, dist_zero_right, ← dist_eq_norm]
    calc dist (x₁ : UnitAddCircle) (x₂ : UnitAddCircle)
        ≤ dist (x₁ : UnitAddCircle) 0 + dist 0 (x₂ : UnitAddCircle) := dist_triangle _ 0 _
      _ = dist (x₁ : UnitAddCircle) 0 + dist (x₂ : UnitAddCircle) 0 := by rw [dist_comm 0]
  linarith

private lemma shift_third_safe_of_le_sixth {v : ℕ} (hnot3 : ¬ 3 ∣ v) (t : ℝ)
    (hle : circDist (t * (v : ℝ)) ≤ 1 / 6) :
    circDist ((t + 1 / 3) * (v : ℝ)) ≥ 1 / 6 ∧
    circDist ((t + 2 / 3) * (v : ℝ)) ≥ 1 / 6 := by
  have hv_mod : v % 3 = 1 ∨ v % 3 = 2 := by omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · constructor
    · rcases shift_third_not_both_unsafe hnot3 t (l₁ := 0) (l₂ := 1) (by decide) with h0 | h1
      · change circDist ((t + ((0 : ℕ) : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6 at h0
        rw [Nat.cast_zero, zero_div, add_zero] at h0; linarith
      · simpa using h1
    · rcases shift_third_not_both_unsafe hnot3 t (l₁ := 0) (l₂ := 2) (by decide) with h0 | h2
      · change circDist ((t + ((0 : ℕ) : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6 at h0
        rw [Nat.cast_zero, zero_div, add_zero] at h0; linarith
      · simpa using h2
  · -- circDist (t * v) = 1 / 6 -> Int.fract (t * v) ∈ {1/6, 5/6} -> + 1/3, + 2/3 ∈ {1/6, 1/2, 5/6}!
    have hfr_cases : Int.fract (t * (v : ℝ)) = 1 / 6 ∨ Int.fract (t * (v : ℝ)) = 5 / 6 := by
      rw [circDist_eq_min_fract] at heq
      have hf0 := Int.fract_nonneg (t * (v : ℝ)); have hf1 := Int.fract_lt_one (t * (v : ℝ))
      rcases min_cases (Int.fract (t * (v : ℝ))) (1 - Int.fract (t * (v : ℝ))) with ⟨hm, hle'⟩ | ⟨hm, hle'⟩
      · left; linarith
      · right; linarith
    have hcheck : ∀ m : ℕ, (m = 1 ∨ m = 2) → circDist ((t + (m : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6 := by
      intro m hm
      have hdiv : 3 * (v / 3) + v % 3 = v := Nat.div_add_mod v 3
      let qv : ℕ := v / 3
      have hexp2 : (t + (m : ℝ) / 3) * (v : ℝ) =
          (Int.fract (t * (v : ℝ)) + (m : ℝ) * ((v % 3 : ℕ) : ℝ) / 3) +
          ((⌊t * (v : ℝ)⌋ + (m : ℤ) * (qv : ℤ) : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract (t * (v : ℝ))
        have hvc : (v : ℝ) = 3 * (qv : ℝ) + ((v % 3 : ℕ) : ℝ) := by dsimp [qv]; exact_mod_cast hdiv.symm
        have hm_v : ((m : ℝ) / 3) * (v : ℝ) = (m : ℝ) * (qv : ℝ) + (m : ℝ) * ((v % 3 : ℕ) : ℝ) / 3 := by
          rw [hvc]; ring
        calc (t + (m : ℝ) / 3) * (v : ℝ)
            = t * (v : ℝ) + ((m : ℝ) / 3) * (v : ℝ) := add_mul _ _ _
          _ = ((⌊t * (v : ℝ)⌋ : ℝ) + Int.fract (t * (v : ℝ))) +
              ((m : ℝ) * (qv : ℝ) + (m : ℝ) * ((v % 3 : ℕ) : ℝ) / 3) := by rw [hf, hm_v]
          _ = _ := by push_cast; ring
      rw [hexp2, circDist_add_int, circDist_ge_iff_fract]
      rcases hfr_cases with hf | hf <;> rw [hf] <;> rcases hm with rfl | rfl <;>
        rcases hv_mod with hv | hv <;> rw [hv] <;> push_cast
      · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
      · rw [fract_eq_sub_int _ 2 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
    exact ⟨by simpa using hcheck 1 (Or.inl rfl), by simpa using hcheck 2 (Or.inr rfl)⟩

-- Helper: if `¬ 3 ∣ v` and `Int.fract (s * v) ∈ {1/6, 1/2, 5/6}`, then:
-- (a) ALL THREE shifts `s + l / 3` (`l : Fin 3`) keep `v` safe (`≥ 1/6`), AND
-- (b) SOME shift `s + l / 3` (`l : Fin 3`) puts `Int.fract ((s + l / 3) * v) = 5 / 6`!
private lemma shift_third_grid_sixth {v : ℕ} (hnot3 : ¬ 3 ∣ v) (s : ℝ)
    (hgrid : Int.fract (s * (v : ℝ)) = 1 / 6 ∨ Int.fract (s * (v : ℝ)) = 1 / 2 ∨
      Int.fract (s * (v : ℝ)) = 5 / 6) :
    (∀ l : Fin 3, circDist ((s + (l.val : ℝ) / 3) * (v : ℝ)) ≥ 1 / 6) ∧
    (∃ l : Fin 3, Int.fract ((s + (l.val : ℝ) / 3) * (v : ℝ)) = 5 / 6) := by
  have hv_mod : v % 3 = 1 ∨ v % 3 = 2 := by omega
  have hdiv : 3 * (v / 3) + v % 3 = v := Nat.div_add_mod v 3
  let qv : ℕ := v / 3
  have hexp : ∀ l : Fin 3, Int.fract ((s + (l.val : ℝ) / 3) * (v : ℝ)) =
      Int.fract (Int.fract (s * (v : ℝ)) + (l.val : ℝ) * ((v % 3 : ℕ) : ℝ) / 3) := by
    intro l
    have hf := Int.floor_add_fract (s * (v : ℝ))
    have hvc : (v : ℝ) = 3 * (qv : ℝ) + ((v % 3 : ℕ) : ℝ) := by dsimp [qv]; exact_mod_cast hdiv.symm
    have hm_v : ((l.val : ℝ) / 3) * (v : ℝ) =
        (l.val : ℝ) * (qv : ℝ) + (l.val : ℝ) * ((v % 3 : ℕ) : ℝ) / 3 := by rw [hvc]; ring
    have htot : (s + (l.val : ℝ) / 3) * (v : ℝ) =
        (Int.fract (s * (v : ℝ)) + (l.val : ℝ) * ((v % 3 : ℕ) : ℝ) / 3) +
        ((⌊s * (v : ℝ)⌋ + (l.val : ℤ) * (qv : ℤ) : ℤ) : ℝ) := by
      calc (s + (l.val : ℝ) / 3) * (v : ℝ)
          = s * (v : ℝ) + ((l.val : ℝ) / 3) * (v : ℝ) := add_mul _ _ _
        _ = ((⌊s * (v : ℝ)⌋ : ℝ) + Int.fract (s * (v : ℝ))) + _ := by rw [hf, hm_v]
        _ = _ := by push_cast; ring
    rw [htot, Int.fract_add_intCast]
  constructor
  · intro l
    rw [circDist_ge_iff_fract, hexp l]
    have hl_cases : l.val = 0 ∨ l.val = 1 ∨ l.val = 2 := by fin_cases l <;> simp
    rcases hgrid with hf | hf | hf <;> rw [hf] <;> rcases hv_mod with hv | hv <;> rw [hv] <;>
      rcases hl_cases with hl | hl | hl <;> rw [hl] <;> push_cast
    all_goals
      first
      | (rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num)
      | (rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num)
      | (rw [fract_eq_sub_int _ 2 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num)
  · rcases hgrid with hf | hf | hf <;> rcases hv_mod with hv | hv
    · refine ⟨2, ?_⟩; rw [hexp 2, hf, hv]; simp; rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
    · refine ⟨1, ?_⟩; rw [hexp 1, hf, hv]; simp; rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
    · refine ⟨1, ?_⟩; rw [hexp 1, hf, hv]; simp; rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
    · refine ⟨2, ?_⟩; rw [hexp 2, hf, hv]; simp
      rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; norm_num
    · refine ⟨0, ?_⟩; rw [hexp 0, hf]; simp; norm_num
    · refine ⟨0, ?_⟩; rw [hexp 0, hf]; simp; norm_num

-- Renault Argument 1: v0, v1 multiples of 3 (both safe at t), v2, v3, v4 not multiples of 3,
-- and at least TWO of {v2, v3, v4} have circDist ≤ 1/6 at t -> ∃ l ∈ {1, 2}, t + l/3 ∈ D!
private lemma renault_arg1 (v : Fin 5 → ℕ)
    (hdvd0 : 3 ∣ v 0) (hdvd1 : 3 ∣ v 1)
    (hnot3 : ∀ r : Fin 3, ¬ 3 ∣ v r.succ.succ)
    (t : ℝ) (hs0 : circDist (t * (v 0 : ℝ)) ≥ 1 / 6) (hs1 : circDist (t * (v 1 : ℝ)) ≥ 1 / 6)
    (r₁ r₂ : Fin 3) (hne : r₁ ≠ r₂)
    (hu1 : circDist (t * (v r₁.succ.succ : ℝ)) ≤ 1 / 6)
    (hu2 : circDist (t * (v r₂.succ.succ : ℝ)) ≤ 1 / 6) :
    ∃ t' : ℝ, ∀ i : Fin 5, circDist (t' * (v i : ℝ)) ≥ 1 / 6 := by
  obtain ⟨h1_1, h1_2⟩ := shift_third_safe_of_le_sixth (hnot3 r₁) t hu1
  obtain ⟨h2_1, h2_2⟩ := shift_third_safe_of_le_sixth (hnot3 r₂) t hu2
  let r₃ : Fin 3 := ⟨3 - r₁.val - r₂.val, by
    have := r₁.isLt; have := r₂.isLt
    have : r₁.val ≠ r₂.val := fun h => hne (Fin.ext h)
    omega⟩
  have h3c : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  have hcov : ∀ r : Fin 3, r = r₁ ∨ r = r₂ ∨ r = r₃ := by
    intro r
    have := r₁.isLt; have := r₂.isLt; have := r.isLt
    have hne' : r₁.val ≠ r₂.val := fun h => hne (Fin.ext h)
    have hval : r.val = r₁.val ∨ r.val = r₂.val ∨ r.val = 3 - r₁.val - r₂.val := by omega
    rcases hval with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases shift_third_not_both_unsafe (hnot3 r₃) t (l₁ := 1) (l₂ := 2) (by decide) with hg1 | hg2
  · refine ⟨t + ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ), fun i => ?_⟩
    have hrs : ∀ r : Fin 3, circDist ((t + ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)) * (v r.succ.succ : ℝ)) ≥ 1 / 6 := by
      intro r; rcases hcov r with rfl | rfl | rfl
      · simpa using h1_1
      · simpa using h2_1
      · simpa using hg1
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl | rfl
    · rw [circDist_shift_dvd (by omega) hdvd0]; exact hs0
    · rw [circDist_shift_dvd (by omega) hdvd1]; exact hs1
    · exact hrs 0
    · exact hrs 1
    · exact hrs 2
  · refine ⟨t + ((2 : ℤ) : ℝ) / ((3 : ℕ) : ℝ), fun i => ?_⟩
    have hrs : ∀ r : Fin 3, circDist ((t + ((2 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)) * (v r.succ.succ : ℝ)) ≥ 1 / 6 := by
      intro r; rcases hcov r with rfl | rfl | rfl
      · simpa using h1_2
      · simpa using h2_2
      · simpa using hg2
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl | rfl
    · rw [circDist_shift_dvd (by omega) hdvd0]; exact hs0
    · rw [circDist_shift_dvd (by omega) hdvd1]; exact hs1
    · exact hrs 0
    · exact hrs 1
    · exact hrs 2

-- Renault Argument 2: v0, v1 multiples of 3 (both safe at t), v2, v3, v4 not multiples of 3,
-- and v2 has Int.fract (t * v2) ∈ {1/6, 1/2, 5/6} -> ∃ l ∈ {0, 1, 2}, t + l/3 ∈ D!
private lemma renault_arg2 (v : Fin 5 → ℕ)
    (hdvd0 : 3 ∣ v 0) (hdvd1 : 3 ∣ v 1)
    (hnot3 : ∀ r : Fin 3, ¬ 3 ∣ v r.succ.succ)
    (t : ℝ) (hs0 : circDist (t * (v 0 : ℝ)) ≥ 1 / 6) (hs1 : circDist (t * (v 1 : ℝ)) ≥ 1 / 6)
    (hgrid2 : Int.fract (t * (v 2 : ℝ)) = 1 / 6 ∨ Int.fract (t * (v 2 : ℝ)) = 1 / 2 ∨
      Int.fract (t * (v 2 : ℝ)) = 5 / 6) :
    ∃ t' : ℝ, ∀ i : Fin 5, circDist (t' * (v i : ℝ)) ≥ 1 / 6 := by
  have hall2 := (shift_third_grid_sixth (hnot3 0) t hgrid2).1
  have hex_l : ∃ l : Fin 3,
      circDist ((t + (l.val : ℝ) / 3) * (v 3 : ℝ)) ≥ 1 / 6 ∧
      circDist ((t + (l.val : ℝ) / 3) * (v 4 : ℝ)) ≥ 1 / 6 := by
    by_contra hnone
    have hb : ∀ l : Fin 3, circDist ((t + (l.val : ℝ) / 3) * (v 3 : ℝ)) < 1 / 6 ∨
        circDist ((t + (l.val : ℝ) / 3) * (v 4 : ℝ)) < 1 / 6 := by
      intro l
      rcases le_or_gt (1 / 6) (circDist ((t + (l.val : ℝ) / 3) * (v 3 : ℝ))) with g3 | g3
      · rcases le_or_gt (1 / 6) (circDist ((t + (l.val : ℝ) / 3) * (v 4 : ℝ))) with g4 | g4
        · exfalso; exact hnone ⟨l, g3, g4⟩
        · exact Or.inr g4
      · exact Or.inl g3
    have hnot3_3 : ¬ 3 ∣ v 3 := hnot3 1
    have hnot3_4 : ¬ 3 ∣ v 4 := hnot3 2
    have u3_01 := shift_third_not_both_unsafe hnot3_3 t (l₁ := 0) (l₂ := 1) (by decide)
    have u3_02 := shift_third_not_both_unsafe hnot3_3 t (l₁ := 0) (l₂ := 2) (by decide)
    have u3_12 := shift_third_not_both_unsafe hnot3_3 t (l₁ := 1) (l₂ := 2) (by decide)
    have u4_01 := shift_third_not_both_unsafe hnot3_4 t (l₁ := 0) (l₂ := 1) (by decide)
    have u4_02 := shift_third_not_both_unsafe hnot3_4 t (l₁ := 0) (l₂ := 2) (by decide)
    have u4_12 := shift_third_not_both_unsafe hnot3_4 t (l₁ := 1) (l₂ := 2) (by decide)
    rcases hb 0 with h0 | h0 <;> rcases hb 1 with h1 | h1 <;> rcases hb 2 with h2 | h2 <;>
      [ (rcases u3_01 with g|g <;> linarith);
        (rcases u3_01 with g|g <;> linarith);
        (rcases u3_02 with g|g <;> linarith);
        (rcases u4_12 with g|g <;> linarith);
        (rcases u3_12 with g|g <;> linarith);
        (rcases u4_02 with g|g <;> linarith);
        (rcases u4_01 with g|g <;> linarith);
        (rcases u4_01 with g|g <;> linarith) ]
  obtain ⟨l, hl3, hl4⟩ := hex_l
  refine ⟨t + ((l.val : ℤ) : ℝ) / ((3 : ℕ) : ℝ), fun i => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl | rfl
  · rw [circDist_shift_dvd (by omega) hdvd0]; exact hs0
  · rw [circDist_shift_dvd (by omega) hdvd1]; exact hs1
  · simpa using hall2 l
  · simpa using hl3
  · simpa using hl4

-- Renault Argument 3: 3 ∣ v0 (safe at t), v1, v2, v3, v4 not multiples of 3,
-- and THREE of {v1, v2, v3, v4} (say v2, v3, v4) have circDist ≤ 1/6 at t -> ∃ l ∈ {1, 2}, t + l/3 ∈ D!
private lemma renault_arg3 (v : Fin 5 → ℕ)
    (hdvd0 : 3 ∣ v 0)
    (hnot3 : ∀ j : Fin 4, ¬ 3 ∣ v j.succ)
    (t : ℝ) (hs0 : circDist (t * (v 0 : ℝ)) ≥ 1 / 6)
    (hu2 : circDist (t * (v 2 : ℝ)) ≤ 1 / 6)
    (hu3 : circDist (t * (v 3 : ℝ)) ≤ 1 / 6)
    (hu4 : circDist (t * (v 4 : ℝ)) ≤ 1 / 6) :
    ∃ t' : ℝ, ∀ i : Fin 5, circDist (t' * (v i : ℝ)) ≥ 1 / 6 := by
  obtain ⟨h2_1, h2_2⟩ := shift_third_safe_of_le_sixth (hnot3 1) t hu2
  obtain ⟨h3_1, h3_2⟩ := shift_third_safe_of_le_sixth (hnot3 2) t hu3
  obtain ⟨h4_1, h4_2⟩ := shift_third_safe_of_le_sixth (hnot3 3) t hu4
  rcases shift_third_not_both_unsafe (hnot3 0) t (l₁ := 1) (l₂ := 2) (by decide) with hg1 | hg2
  · refine ⟨t + ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ), fun i => ?_⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl | rfl
    · rw [circDist_shift_dvd (by omega) hdvd0]; exact hs0
    · simpa using hg1
    · simpa using h2_1
    · simpa using h3_1
    · simpa using h4_1
  · refine ⟨t + ((2 : ℤ) : ℝ) / ((3 : ℕ) : ℝ), fun i => ?_⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl | rfl
    · rw [circDist_shift_dvd (by omega) hdvd0]; exact hs0
    · simpa using hg2
    · simpa using h2_2
    · simpa using h3_2
    · simpa using h4_2

/- ### Parity / Mod-6 Shift Helpers & Renault Proposition 4.1 (Three Even Speeds, page 4) -/

private lemma circDist_sub_le (a b : ℝ) : circDist (a - b) ≤ circDist a + circDist b := by
  have hmk : ((a - b : ℝ) : UnitAddCircle) = (a : UnitAddCircle) - (b : UnitAddCircle) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).map_sub a b
  change dist ((a - b : ℝ) : UnitAddCircle) 0 ≤
    dist (a : UnitAddCircle) 0 + dist (b : UnitAddCircle) 0
  rw [hmk, dist_zero_right, ← dist_eq_norm]
  calc dist (a : UnitAddCircle) (b : UnitAddCircle)
      ≤ dist (a : UnitAddCircle) 0 + dist 0 (b : UnitAddCircle) := dist_triangle _ 0 _
    _ = dist (a : UnitAddCircle) 0 + dist (b : UnitAddCircle) 0 := by rw [dist_comm 0]

private lemma circDist_even_add_half {v : ℕ} (heven : 2 ∣ v) (t : ℝ) :
    circDist ((t + 1 / 2) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  obtain ⟨k, rfl⟩ := heven
  have h : (t + 1 / 2) * ((2 * k : ℕ) : ℝ) = t * ((2 * k : ℕ) : ℝ) + ((k : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, circDist_add_int]

private lemma circDist_even_sub_half {v : ℕ} (heven : 2 ∣ v) (t : ℝ) :
    circDist ((t - 1 / 2) * (v : ℝ)) = circDist (t * (v : ℝ)) := by
  obtain ⟨k, rfl⟩ := heven
  have h : (t - 1 / 2) * ((2 * k : ℕ) : ℝ) = t * ((2 * k : ℕ) : ℝ) - ((k : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, circDist_sub_int]

private lemma circDist_even_sixth_1 {v : ℕ} (heven : 2 ∣ v) (t : ℝ) :
    circDist ((t + 1 / 6) * (v : ℝ)) = circDist ((t + 2 / 3) * (v : ℝ)) := by
  have h : t + (1 / 6 : ℝ) = (t + 2 / 3) - 1 / 2 := by ring
  rw [h, circDist_even_sub_half heven]

private lemma circDist_even_sixth_5 {v : ℕ} (heven : 2 ∣ v) (t : ℝ) :
    circDist ((t + 5 / 6) * (v : ℝ)) = circDist ((t + 1 / 3) * (v : ℝ)) := by
  have h : t + (5 / 6 : ℝ) = (t + 1 / 3) + 1 / 2 := by ring
  rw [h, circDist_even_add_half heven]

private lemma odd_half_not_both_unsafe {v : ℕ} (hodd : ¬ 2 ∣ v) (t : ℝ) :
    circDist (t * (v : ℝ)) ≥ 1 / 6 ∨ circDist ((t + 1 / 2) * (v : ℝ)) ≥ 1 / 6 := by
  by_contra hboth
  have h1 : circDist (t * (v : ℝ)) < 1 / 6 := lt_of_not_ge fun h => hboth (Or.inl h)
  have h2 : circDist ((t + 1 / 2) * (v : ℝ)) < 1 / 6 := lt_of_not_ge fun h => hboth (Or.inr h)
  let qv : ℕ := v / 2
  have hdiv : 2 * qv + 1 = v := by dsimp [qv]; omega
  let x₁ : ℝ := t * (v : ℝ)
  let x₂ : ℝ := (t + 1 / 2) * (v : ℝ)
  have hdiff : x₂ - x₁ = (1 / 2 : ℝ) + ((qv : ℤ) : ℝ) := by
    dsimp [x₁, x₂]
    have hvc : (v : ℝ) = 2 * (qv : ℝ) + 1 := by exact_mod_cast hdiv.symm
    rw [hvc]; push_cast; ring
  have hd : circDist (x₂ - x₁) = 1 / 2 := by
    rw [hdiff, circDist_add_int, circDist_eq_min_fract,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    norm_num
  have htri := circDist_sub_le x₂ x₁
  linarith

private lemma odd_half_unsafe_imp_mid {v : ℕ} (hodd : ¬ 2 ∣ v) (t : ℝ)
    (hu : circDist ((t + 1 / 2) * (v : ℝ)) < 1 / 6) :
    1 / 3 < Int.fract (t * (v : ℝ)) ∧ Int.fract (t * (v : ℝ)) < 2 / 3 := by
  let qv : ℕ := v / 2
  have hdiv : 2 * qv + 1 = v := by dsimp [qv]; omega
  set f := Int.fract (t * (v : ℝ))
  have hf0 : 0 ≤ f := Int.fract_nonneg _; have hf1 : f < 1 := Int.fract_lt_one _
  have hexp : (t + 1 / 2) * (v : ℝ) = (f + 1 / 2) + ((⌊t * (v : ℝ)⌋ + (qv : ℤ) : ℤ) : ℝ) := by
    have hf_eq := Int.floor_add_fract (t * (v : ℝ))
    have hvc : (1 / 2 : ℝ) * (v : ℝ) = (qv : ℝ) + 1 / 2 := by
      have hv1 : (v : ℝ) = 2 * (qv : ℝ) + 1 := by exact_mod_cast hdiv.symm
      rw [hv1]; ring
    calc (t + 1 / 2) * (v : ℝ) = t * (v : ℝ) + (1 / 2) * (v : ℝ) := add_mul _ _ _
      _ = ((⌊t * (v : ℝ)⌋ : ℝ) + f) + ((qv : ℝ) + 1 / 2) := by dsimp [f]; linarith [hf_eq, hvc]
      _ = _ := by push_cast; ring
  rw [hexp, circDist_add_int, circDist_eq_min_fract] at hu
  rcases lt_or_ge f (1 / 2) with hlt | hge
  · rw [fract_eq_sub_int (f + 1 / 2) 0 (by push_cast; linarith) (by push_cast; linarith)] at hu
    push_cast at hu
    rcases min_cases (f + 1 / 2 - 0) (1 - (f + 1 / 2 - 0)) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int (f + 1 / 2) 1 (by push_cast; linarith) (by push_cast; linarith)] at hu
    push_cast at hu
    rcases min_cases (f + 1 / 2 - 1) (1 - (f + 1 / 2 - 1)) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
      exact ⟨by linarith, by linarith⟩

private lemma odd_double_plus_half_safe {v : ℕ} (hodd : ¬ 2 ∣ v) (t : ℝ)
    (h : circDist (t * (v : ℝ)) < 1 / 6 ∨
      (1 / 3 < Int.fract (t * (v : ℝ)) ∧ Int.fract (t * (v : ℝ)) < 2 / 3)) :
    circDist ((2 * t + 1 / 2) * (v : ℝ)) ≥ 1 / 6 := by
  let qv : ℕ := v / 2
  have hdiv : 2 * qv + 1 = v := by dsimp [qv]; omega
  set f := Int.fract (t * (v : ℝ))
  have hf0 : 0 ≤ f := Int.fract_nonneg _; have hf1 : f < 1 := Int.fract_lt_one _
  have hexp : (2 * t + 1 / 2) * (v : ℝ) = (2 * f + 1 / 2) + ((2 * ⌊t * (v : ℝ)⌋ + (qv : ℤ) : ℤ) : ℝ) := by
    have hf_eq := Int.floor_add_fract (t * (v : ℝ))
    have hvc : (1 / 2 : ℝ) * (v : ℝ) = (qv : ℝ) + 1 / 2 := by
      have hv1 : (v : ℝ) = 2 * (qv : ℝ) + 1 := by exact_mod_cast hdiv.symm
      rw [hv1]; ring
    calc (2 * t + 1 / 2) * (v : ℝ) = 2 * (t * (v : ℝ)) + (1 / 2) * (v : ℝ) := by ring
      _ = 2 * ((⌊t * (v : ℝ)⌋ : ℝ) + f) + ((qv : ℝ) + 1 / 2) := by dsimp [f]; linarith [hf_eq, hvc]
      _ = _ := by push_cast; ring
  rw [hexp, circDist_add_int, circDist_ge_iff_fract]
  rcases h with hu | ⟨h1, h2⟩
  · have hfr_or : f < 1 / 6 ∨ 5 / 6 < f := by
      by_contra hmid
      have := (circDist_ge_iff_fract (t * (v : ℝ)) (1 / 6)).mpr
        ⟨le_of_not_gt fun g => hmid (Or.inl g), le_of_not_gt fun g => hmid (Or.inr (by linarith))⟩
      linarith
    rcases hfr_or with hlo | hhi
    · rw [fract_eq_sub_int (2 * f + 1 / 2) 0 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact ⟨by linarith, by linarith⟩
    · rw [fract_eq_sub_int (2 * f + 1 / 2) 2 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int (2 * f + 1 / 2) 1 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩

private lemma two_not3_common_third {v₁ v₂ : ℕ} (h1 : ¬ 3 ∣ v₁) (h2 : ¬ 3 ∣ v₂) (t : ℝ) :
    ∃ l : Fin 3,
      circDist ((t + (l.val : ℝ) / 3) * (v₁ : ℝ)) ≥ 1 / 6 ∧
      circDist ((t + (l.val : ℝ) / 3) * (v₂ : ℝ)) ≥ 1 / 6 := by
  by_contra hnone
  have hb : ∀ l : Fin 3, circDist ((t + (l.val : ℝ) / 3) * (v₁ : ℝ)) < 1 / 6 ∨
      circDist ((t + (l.val : ℝ) / 3) * (v₂ : ℝ)) < 1 / 6 := by
    intro l
    rcases le_or_gt (1 / 6) (circDist ((t + (l.val : ℝ) / 3) * (v₁ : ℝ))) with g1 | g1
    · rcases le_or_gt (1 / 6) (circDist ((t + (l.val : ℝ) / 3) * (v₂ : ℝ))) with g2 | g2
      · exfalso; exact hnone ⟨l, g1, g2⟩
      · exact Or.inr g2
    · exact Or.inl g1
  have u1_01 := shift_third_not_both_unsafe h1 t (l₁ := 0) (l₂ := 1) (by decide)
  have u1_02 := shift_third_not_both_unsafe h1 t (l₁ := 0) (l₂ := 2) (by decide)
  have u1_12 := shift_third_not_both_unsafe h1 t (l₁ := 1) (l₂ := 2) (by decide)
  have u2_01 := shift_third_not_both_unsafe h2 t (l₁ := 0) (l₂ := 1) (by decide)
  have u2_02 := shift_third_not_both_unsafe h2 t (l₁ := 0) (l₂ := 2) (by decide)
  have u2_12 := shift_third_not_both_unsafe h2 t (l₁ := 1) (l₂ := 2) (by decide)
  rcases hb 0 with c0 | c0 <;> rcases hb 1 with c1 | c1 <;> rcases hb 2 with c2 | c2 <;>
    [ (rcases u1_01 with g|g <;> linarith);
      (rcases u1_01 with g|g <;> linarith);
      (rcases u1_02 with g|g <;> linarith);
      (rcases u2_12 with g|g <;> linarith);
      (rcases u1_12 with g|g <;> linarith);
      (rcases u2_02 with g|g <;> linarith);
      (rcases u2_01 with g|g <;> linarith);
      (rcases u2_01 with g|g <;> linarith) ]

private lemma odd_not3_mod6 (v : ℕ) (hodd : ¬ 2 ∣ v) (hnot3 : ¬ 3 ∣ v) :
    ∃ (q : ℤ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (v : ℝ) = 6 * (q : ℝ) + (ε : ℝ) := by
  have hm : v % 6 = 1 ∨ v % 6 = 5 := by omega
  have hdiv : 6 * (v / 6) + v % 6 = v := Nat.div_add_mod v 6
  rcases hm with h1 | h5
  · refine ⟨(v / 6 : ℕ), 1, Or.inl rfl, ?_⟩
    have : v = 6 * (v / 6) + 1 := by omega
    exact_mod_cast this
  · refine ⟨(v / 6 : ℕ) + 1, -1, Or.inr rfl, ?_⟩
    have : (v : ℤ) = 6 * ((v / 6 : ℕ) + 1) + (-1) := by omega
    exact_mod_cast this

private lemma odd_not3_zero_shift_safe {v : ℕ} (hodd : ¬ 2 ∣ v) (hnot3 : ¬ 3 ∣ v)
    (t : ℝ) (hz : Int.fract (t * (v : ℝ)) = 0) {m : ℕ} (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    circDist ((t + (m : ℝ) / 6) * (v : ℝ)) ≥ 1 / 6 := by
  obtain ⟨q, ε, hε, hvc⟩ := odd_not3_mod6 v hodd hnot3
  have ht_int : t * (v : ℝ) = (⌊t * (v : ℝ)⌋ : ℝ) := by
    have := Int.floor_add_fract (t * (v : ℝ)); linarith
  have hexp : (t + (m : ℝ) / 6) * (v : ℝ) =
      (ε : ℝ) * (m : ℝ) / 6 + ((⌊t * (v : ℝ)⌋ + (m : ℤ) * q : ℤ) : ℝ) := by
    have hm_v : ((m : ℝ) / 6) * (v : ℝ) = (m : ℝ) * (q : ℝ) + (ε : ℝ) * (m : ℝ) / 6 := by
      rw [hvc]; ring
    calc (t + (m : ℝ) / 6) * (v : ℝ) = t * (v : ℝ) + ((m : ℝ) / 6) * (v : ℝ) := add_mul _ _ _
      _ = (⌊t * (v : ℝ)⌋ : ℝ) + ((m : ℝ) * (q : ℝ) + (ε : ℝ) * (m : ℝ) / 6) := by linarith [ht_int, hm_v]
      _ = _ := by push_cast; ring
  rw [hexp, circDist_add_int, circDist_ge_iff_fract]
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm5r : (m : ℝ) ≤ 5 := by exact_mod_cast hm5
  rcases hε with rfl | rfl <;> push_cast
  · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩

private lemma odd_not3_unsafe_mid_shift_safe {v : ℕ} (hodd : ¬ 2 ∣ v) (hnot3 : ¬ 3 ∣ v)
    (t : ℝ) (hu : circDist (t * (v : ℝ)) ≤ 1 / 6) {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) :
    circDist ((t + (m : ℝ) / 6) * (v : ℝ)) ≥ 1 / 6 := by
  obtain ⟨q, ε, hε, hvc⟩ := odd_not3_mod6 v hodd hnot3
  set f := Int.fract (t * (v : ℝ))
  have hf0 : 0 ≤ f := Int.fract_nonneg _; have hf1 : f < 1 := Int.fract_lt_one _
  have hfr_or : f ≤ 1 / 6 ∨ 5 / 6 ≤ f := by
    by_contra hmid
    have := (circDist_gt_iff_fract (t * (v : ℝ)) (1 / 6)).mpr
      ⟨lt_of_not_ge fun g => hmid (Or.inl g), lt_of_not_ge fun g => hmid (Or.inr (by linarith))⟩
    linarith
  have hexp : (t + (m : ℝ) / 6) * (v : ℝ) =
      (f + (ε : ℝ) * (m : ℝ) / 6) + ((⌊t * (v : ℝ)⌋ + (m : ℤ) * q : ℤ) : ℝ) := by
    have hf_eq := Int.floor_add_fract (t * (v : ℝ))
    have hm_v : ((m : ℝ) / 6) * (v : ℝ) = (m : ℝ) * (q : ℝ) + (ε : ℝ) * (m : ℝ) / 6 := by
      rw [hvc]; ring
    calc (t + (m : ℝ) / 6) * (v : ℝ) = t * (v : ℝ) + ((m : ℝ) / 6) * (v : ℝ) := add_mul _ _ _
      _ = ((⌊t * (v : ℝ)⌋ : ℝ) + f) + ((m : ℝ) * (q : ℝ) + (ε : ℝ) * (m : ℝ) / 6) := by dsimp [f]; linarith [hf_eq, hm_v]
      _ = _ := by push_cast; ring
  rw [hexp, circDist_add_int, circDist_ge_iff_fract]
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm4r : (m : ℝ) ≤ 4 := by exact_mod_cast hm4
  rcases hfr_or with hlo | hhi <;> rcases hε with rfl | rfl <;> push_cast
  · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩
  · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; exact ⟨by linarith, by linarith⟩

private lemma scale_into_twelfth_sixth {x : ℝ} (hpos : 0 < circDist x) (hle : circDist x ≤ 1 / 6) :
    ∃ μ : ℕ, 1 ≤ μ ∧ 1 / 12 < circDist ((μ : ℝ) * x) ∧ circDist ((μ : ℝ) * x) ≤ 1 / 6 := by
  set d := circDist x
  let μz : ℤ := ⌊1 / (6 * d)⌋
  have h1_le : (1 : ℝ) ≤ 1 / (6 * d) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hμz_ge1 : 1 ≤ μz := Int.le_floor.mpr (by push_cast; exact h1_le)
  let μ : ℕ := μz.toNat
  have hμ_ge1 : 1 ≤ μ := by dsimp [μ]; omega
  have hμ_cast : (μ : ℝ) = (μz : ℝ) := by
    have : (μ : ℤ) = μz := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hμ_ub : (μ : ℝ) * d ≤ 1 / 6 := by
    have hfl : (μz : ℝ) ≤ 1 / (6 * d) := Int.floor_le _
    rw [hμ_cast]; have := mul_le_mul_of_nonneg_right hfl hpos.le
    have hrhs : (1 / (6 * d)) * d = 1 / 6 := by field_simp
    linarith
  have hμ_lb : 1 / 12 < (μ : ℝ) * d := by
    have hlt : 1 / (6 * d) < (μz : ℝ) + 1 := Int.lt_floor_add_one _
    have hgt : 1 / 6 < ((μ : ℝ) + 1) * d := by
      rw [hμ_cast]
      have := mul_lt_mul_of_pos_right hlt hpos
      have hlhs : (1 / (6 * d)) * d = 1 / 6 := by field_simp
      linarith
    have h1r : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ_ge1
    nlinarith
  -- Show circDist (μ * x) = μ * d!
  have hd_mul : circDist ((μ : ℝ) * x) = (μ : ℝ) * d := by
    have hf_or : Int.fract x = d ∨ Int.fract (-x) = d := by
      have hmin : d = min (Int.fract x) (1 - Int.fract x) := circDist_eq_min_fract x
      rcases min_cases (Int.fract x) (1 - Int.fract x) with ⟨hm, _⟩ | ⟨hm, _⟩
      · left; linarith
      · right
        have hfx_pos : 0 < Int.fract x := by
          have := Int.fract_lt_one x; linarith
        rw [fract_neg_of_pos hfx_pos]; linarith
    rcases hf_or with hfx | hfnx
    · have hexp : (μ : ℝ) * x = (μ : ℝ) * d + (((μ : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract x; rw [hfx] at hf
        calc (μ : ℝ) * x = (μ : ℝ) * ((⌊x⌋ : ℝ) + d) := by rw [hf]
          _ = _ := by push_cast; ring
      rw [hexp, circDist_add_int, circDist_eq_min_fract,
        Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩, min_eq_left (by linarith)]
    · rw [← circDist_neg]
      have hnx : -((μ : ℝ) * x) = (μ : ℝ) * (-x) := by ring
      have hexp : (μ : ℝ) * (-x) = (μ : ℝ) * d + (((μ : ℤ) * ⌊-x⌋ : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract (-x); rw [hfnx] at hf
        calc (μ : ℝ) * (-x) = (μ : ℝ) * ((⌊-x⌋ : ℝ) + d) := by rw [hf]
          _ = _ := by push_cast; ring
      rw [hnx, hexp, circDist_add_int, circDist_eq_min_fract,
        Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩, min_eq_left (by linarith)]
  exact ⟨μ, hμ_ge1, by linarith, by linarith⟩

private lemma renault_prop_4_1
    (h_claim24 : ∀ x : ℝ, 1 / 6 < x → x < 5 / 6 →
      ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
        (Int.fract ((lam : ℝ) * x) < 1 / 6 ∨ 5 / 6 < Int.fract ((lam : ℝ) * x)))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (hdvd6_0 : 6 ∣ v 0)
    (heven1 : 2 ∣ v 1) (heven2 : 2 ∣ v 2)
    (hodd3 : ¬ 2 ∣ v 3) (hodd4 : ¬ 2 ∣ v 4)
    (hnot3 : ∀ j : Fin 4, ¬ 3 ∣ v j.succ) :
    ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  by_contra hfail
  have h16 : (1 : ℝ) / ((5 + 1 : ℕ) : ℝ) = 1 / 6 := by norm_num
  have hno_D : ∀ t : ℝ, ¬ (∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / 6) := by
    intro t ht; exact hfail ⟨t, fun i => by rw [h16]; exact ht i⟩
  -- Key structural lemma: for any permutation (u1, u2) of (v 1, v 2) and (w3, w4) of (v 3, v 4),
  -- w3 ∣ v 0!
  have hdvd_odd : ∀ (w3 w4 : ℕ), ¬ 2 ∣ w3 → ¬ 3 ∣ w3 → 0 < w3 → ¬ 2 ∣ w4 → ¬ 3 ∣ w4 →
      (∀ t : ℝ, ¬ (circDist (t * (v 0 : ℝ)) ≥ 1 / 6 ∧ circDist (t * (v 1 : ℝ)) ≥ 1 / 6 ∧
        circDist (t * (v 2 : ℝ)) ≥ 1 / 6 ∧ circDist (t * (w3 : ℝ)) ≥ 1 / 6 ∧
        circDist (t * (w4 : ℝ)) ≥ 1 / 6)) →
      w3 ∣ v 0 := by
    intro w3 w4 hw3_odd hw3_not3 hw3_pos hw4_odd hw4_not3 hno5
    -- Step A: if circDist (t * v 0) ≥ 1/6 and fract(t * w3) = 0, then 1/3 < fract(t * w4) < 2/3!
    have hmid_w4 : ∀ t : ℝ, circDist (t * (v 0 : ℝ)) ≥ 1 / 6 → Int.fract (t * (w3 : ℝ)) = 0 →
        1 / 3 < Int.fract (t * (w4 : ℝ)) ∧ Int.fract (t * (w4 : ℝ)) < 2 / 3 := by
      intro t hs0 hz3
      -- First show circDist (t * v 1) > 1/6 and circDist (t * v 2) > 1/6 (Subclaim 4.1a)
      have heven_gt : ∀ (u_a u_b : ℕ), 2 ∣ u_a → ¬ 3 ∣ u_a → 2 ∣ u_b → ¬ 3 ∣ u_b →
          (∀ s : ℝ, circDist (s * (v 0 : ℝ)) ≥ 1 / 6 → circDist (s * (u_a : ℝ)) ≥ 1 / 6 →
            circDist (s * (u_b : ℝ)) ≥ 1 / 6 → circDist (s * (w3 : ℝ)) ≥ 1 / 6 →
            circDist (s * (w4 : ℝ)) ≥ 1 / 6 → False) →
          1 / 6 < circDist (t * (u_a : ℝ)) := by
        intro u_a u_b hua2 hua3 hub2 hub3 hno_ab
        by_contra hle_a
        obtain ⟨ha_1, ha_2⟩ := shift_third_safe_of_le_sixth hua3 t (le_of_not_gt hle_a)
        rcases shift_third_not_both_unsafe hub3 t (l₁ := 1) (l₂ := 2) (by decide) with hb_1 | hb_2
        · -- u_b safe at t + 1/3 -> test m = 2 (t + 2/6 = t + 1/3) and m = 5 (t + 5/6 = (t + 1/3) + 1/2)!
          have hb_1' : circDist ((t + 1 / 3) * (u_b : ℝ)) ≥ 1 / 6 := by simpa using hb_1
          rcases odd_half_not_both_unsafe hw4_odd (t + 1 / 3) with hw4_a | hw4_b
          · apply hno_ab (t + ((2 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
            · rw [circDist_shift_dvd (by omega) hdvd6_0]; exact hs0
            · have heq : t + ((2 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 3 := by push_cast; ring
              rw [heq]; exact ha_1
            · have heq : t + ((2 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 3 := by push_cast; ring
              rw [heq]; exact hb_1'
            · have heq : t + ((2 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + ((2 : ℕ) : ℝ) / 6 := by push_cast; ring
              rw [heq]; exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
            · have heq : t + ((2 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 3 := by push_cast; ring
              rw [heq]; exact hw4_a
          · apply hno_ab (t + ((5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
            · rw [circDist_shift_dvd (by omega) hdvd6_0]; exact hs0
            · have heq : t + ((5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 5 / 6 := by push_cast; ring
              rw [heq, circDist_even_sixth_5 hua2]; exact ha_1
            · have heq : t + ((5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 5 / 6 := by push_cast; ring
              rw [heq, circDist_even_sixth_5 hub2]; exact hb_1'
            · have heq : t + ((5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + ((5 : ℕ) : ℝ) / 6 := by push_cast; ring
              rw [heq]; exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
            · have heq : t + ((5 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = (t + 1 / 3) + 1 / 2 := by push_cast; ring
              rw [heq]; exact hw4_b
        · -- u_b safe at t + 2/3 -> test m = 4 (t + 4/6 = t + 2/3) and m = 1 (t + 1/6 = (t + 2/3) - 1/2)!
          have hb_2' : circDist ((t + 2 / 3) * (u_b : ℝ)) ≥ 1 / 6 := by simpa using hb_2
          rcases odd_half_not_both_unsafe hw4_odd (t + 1 / 6) with hw4_a | hw4_b
          · apply hno_ab (t + ((1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
            · rw [circDist_shift_dvd (by omega) hdvd6_0]; exact hs0
            · have heq : t + ((1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 6 := by push_cast; ring
              rw [heq, circDist_even_sixth_1 hua2]; exact ha_2
            · have heq : t + ((1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 6 := by push_cast; ring
              rw [heq, circDist_even_sixth_1 hub2]; exact hb_2'
            · have heq : t + ((1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + ((1 : ℕ) : ℝ) / 6 := by push_cast; ring
              rw [heq]; exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
            · have heq : t + ((1 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 1 / 6 := by push_cast; ring
              rw [heq]; exact hw4_a
          · apply hno_ab (t + ((4 : ℤ) : ℝ) / ((6 : ℕ) : ℝ))
            · rw [circDist_shift_dvd (by omega) hdvd6_0]; exact hs0
            · have heq : t + ((4 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 2 / 3 := by push_cast; ring
              rw [heq]; exact ha_2
            · have heq : t + ((4 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + 2 / 3 := by push_cast; ring
              rw [heq]; exact hb_2'
            · have heq : t + ((4 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = t + ((4 : ℕ) : ℝ) / 6 := by push_cast; ring
              rw [heq]; exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
            · have heq : t + ((4 : ℤ) : ℝ) / ((6 : ℕ) : ℝ) = (t + 1 / 6) + 1 / 2 := by push_cast; ring
              rw [heq]; exact hw4_b
      have hv1_gt : 1 / 6 < circDist (t * (v 1 : ℝ)) :=
        heven_gt (v 1) (v 2) heven1 (hnot3 0) heven2 (hnot3 1)
          (fun s h0 h1 h2 h3 h4 => hno5 s ⟨h0, h1, h2, h3, h4⟩)
      have hv2_gt : 1 / 6 < circDist (t * (v 2 : ℝ)) :=
        heven_gt (v 2) (v 1) heven2 (hnot3 1) heven1 (hnot3 0)
          (fun s h0 h2 h1 h3 h4 => hno5 s ⟨h0, h1, h2, h3, h4⟩)
      -- Subclaim 4.1b: circDist (t * w4) > 1/6 (otherwise some m ∈ {2, 3, 4} works!)
      have hw4_gt : 1 / 6 < circDist (t * (w4 : ℝ)) := by
        by_contra hle4
        obtain ⟨l, hl1, hl2⟩ := two_not3_common_third (hnot3 0) (hnot3 1) t
        let m : ℕ := if l.val = 0 then 3 else if l.val = 1 then 2 else 4
        have hm2 : 2 ≤ m := by dsimp [m]; split_ifs <;> omega
        have hm4 : m ≤ 4 := by dsimp [m]; split_ifs <;> omega
        have heven_m : ∀ {u : ℕ}, 2 ∣ u →
            circDist ((t + (m : ℝ) / 6) * (u : ℝ)) = circDist ((t + (l.val : ℝ) / 3) * (u : ℝ)) := by
          intro u hu2
          have hl_c : l.val = 0 ∨ l.val = 1 ∨ l.val = 2 := by fin_cases l <;> simp
          rcases hl_c with hl0 | hl1' | hl2'
          · dsimp [m]; rw [hl0]; simp only [↓reduceIte, Nat.cast_zero, zero_div, add_zero]
            have heq : t + ((3 : ℕ) : ℝ) / 6 = t + 1 / 2 := by push_cast; ring
            rw [heq, circDist_even_add_half hu2]
          · dsimp [m]; rw [hl1']; simp only [one_ne_zero, ↓reduceIte]
            have heq : t + ((2 : ℕ) : ℝ) / 6 = t + ((1 : ℕ) : ℝ) / 3 := by push_cast; ring
            rw [heq]
          · dsimp [m]; rw [hl2']; norm_num
        apply hno5 (t + (m : ℝ) / 6)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hca : (m : ℝ) / 6 = ((m : ℤ) : ℝ) / ((6 : ℕ) : ℝ) := by push_cast; norm_num
          rw [hca, circDist_shift_dvd (by omega) hdvd6_0]; exact hs0
        · rw [heven_m heven1]; exact hl1
        · rw [heven_m heven2]; exact hl2
        · exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
        · exact odd_not3_unsafe_mid_shift_safe hw4_odd hw4_not3 t (le_of_not_gt hle4) hm2 hm4
      -- Now test t + 1 / 2: v 0, v 1, v 2, w3 are all safe, so w4 must be unsafe (< 1/6)!
      have hu_half : circDist ((t + 1 / 2) * (w4 : ℝ)) < 1 / 6 := by
        by_contra hge
        apply hno5 (t + 1 / 2)
        refine ⟨?_, ?_, ?_, ?_, le_of_not_gt hge⟩
        · rw [circDist_even_add_half (dvd_trans (by decide : 2 ∣ 6) hdvd6_0)]; exact hs0
        · rw [circDist_even_add_half heven1]; exact hv1_gt.le
        · rw [circDist_even_add_half heven2]; exact hv2_gt.le
        · have heq : t + (1 / 2 : ℝ) = t + ((3 : ℕ) : ℝ) / 6 := by push_cast; ring
          rw [heq]; exact odd_not3_zero_shift_safe hw3_odd hw3_not3 t hz3 (by omega) (by omega)
      exact odd_half_unsafe_imp_mid hw4_odd t hu_half
    -- Step B: deduce w3 ∣ v 0!
    by_contra hndvd
    have hw3_r : (0 : ℝ) < (w3 : ℝ) := Nat.cast_pos.mpr hw3_pos
    let t₀ : ℝ := 1 / (w3 : ℝ)
    have ht₀_mul_ne_int : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) →
        Int.fract ((m : ℝ) * (t₀ * (v 0 : ℝ))) ≠ 0 := by
      intro m hm hfr0
      have hnn : 0 ≤ (m : ℝ) * (t₀ * (v 0 : ℝ)) := by dsimp [t₀]; positivity
      let kz : ℤ := ⌊(m : ℝ) * (t₀ * (v 0 : ℝ))⌋
      have hkz_nn : 0 ≤ kz := Int.floor_nonneg.mpr hnn
      let kn : ℕ := kz.toNat
      have heq_r : (m : ℝ) * (t₀ * (v 0 : ℝ)) = (kn : ℝ) := by
        have hf := Int.floor_add_fract ((m : ℝ) * (t₀ * (v 0 : ℝ)))
        have hkc : (kn : ℝ) = (kz : ℝ) := by
          have : (kn : ℤ) = kz := Int.toNat_of_nonneg hkz_nn
          exact_mod_cast this
        rw [hfr0, add_zero] at hf; dsimp [kz] at hkc; linarith
      have hmul_r : ((m * v 0 : ℕ) : ℝ) = ((w3 * kn : ℕ) : ℝ) := by
        have h1 : (m : ℝ) * ((v 0 : ℝ) / (w3 : ℝ)) = (kn : ℝ) := by dsimp [t₀] at heq_r; ring_nf at heq_r ⊢; linarith
        have h2 := congrArg (fun z => (w3 : ℝ) * z) h1
        have h3 : (w3 : ℝ) * ((m : ℝ) * ((v 0 : ℝ) / (w3 : ℝ))) = (m : ℝ) * (v 0 : ℝ) := by
          field_simp [ne_of_gt hw3_r]
        push_cast; linarith
      have hdvd_m : w3 ∣ m * v 0 := ⟨kn, by exact_mod_cast hmul_r⟩
      have cop2 : Nat.Coprime 2 w3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hw3_odd
      have cop3 : Nat.Coprime 3 w3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hw3_not3
      rcases hm with rfl | rfl | rfl | rfl
      · rw [one_mul] at hdvd_m; exact hndvd hdvd_m
      · exact hndvd (cop2.symm.dvd_of_dvd_mul_left hdvd_m)
      · exact hndvd (cop3.symm.dvd_of_dvd_mul_left hdvd_m)
      · have h4 : 4 * v 0 = 2 * (2 * v 0) := by ring
        rw [h4] at hdvd_m
        exact hndvd (cop2.symm.dvd_of_dvd_mul_left (cop2.symm.dvd_of_dvd_mul_left hdvd_m))
    -- Find μ ≥ 1 such that s = μ * t₀ has circDist(s * v 0) ∈ (1/12, 1/6] ∪ {1/5}!
    have hex_μ : ∃ μ : ℕ, 1 ≤ μ ∧
        ((1 / 12 < circDist (((μ : ℝ) * t₀) * (v 0 : ℝ)) ∧
          circDist (((μ : ℝ) * t₀) * (v 0 : ℝ)) ≤ 1 / 6) ∨
         circDist (((μ : ℝ) * t₀) * (v 0 : ℝ)) = 1 / 5) := by
      rcases le_or_gt (circDist (t₀ * (v 0 : ℝ))) (1 / 6) with hle6 | hgt6
      · have hpos0 : 0 < circDist (t₀ * (v 0 : ℝ)) := by
          rcases eq_or_lt_of_le (circDist_nonneg (t₀ * (v 0 : ℝ))) with heq0 | hgt0
          · exfalso; apply ht₀_mul_ne_int 1 (Or.inl rfl)
            rw [Nat.cast_one, one_mul]; exact (circDist_eq_zero_iff_fract _).mp heq0.symm
          · exact hgt0
        obtain ⟨μ, hμ1, hlo, hhi⟩ := scale_into_twelfth_sixth hpos0 hle6
        refine ⟨μ, hμ1, Or.inl ?_⟩
        rw [mul_assoc]; exact ⟨hlo, hhi⟩
      · obtain ⟨f_lo, f_hi⟩ := (circDist_gt_iff_fract _ _).mp hgt6
        obtain ⟨lam, hl2, hl5, hlam_bad⟩ := h_claim24 (Int.fract (t₀ * (v 0 : ℝ))) f_lo (by linarith)
        have hd_lam : circDist ((lam : ℝ) * (t₀ * (v 0 : ℝ))) < 1 / 6 := by
          rw [circDist_mul_nat lam, circDist_eq_min_fract]
          rcases hlam_bad with h1 | h2
          · exact lt_of_le_of_lt (min_le_left _ _) h1
          · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
        rcases eq_or_lt_of_le (circDist_nonneg ((lam : ℝ) * (t₀ * (v 0 : ℝ)))) with hz_lam | hpos_lam
        · -- circDist = 0 -> lam = 5 and fract(t₀ * v 0) ∈ {1/5, 2/5, 3/5, 4/5}!
          have hfr_lam : Int.fract ((lam : ℝ) * (t₀ * (v 0 : ℝ))) = 0 :=
            (circDist_eq_zero_iff_fract _).mp hz_lam.symm
          have hlam5 : lam = 5 := by
            have hcases : lam = 2 ∨ lam = 3 ∨ lam = 4 ∨ lam = 5 := by omega
            rcases hcases with rfl | rfl | rfl | rfl
            · exfalso; exact ht₀_mul_ne_int 2 (by simp) hfr_lam
            · exfalso; exact ht₀_mul_ne_int 3 (by simp) hfr_lam
            · exfalso; exact ht₀_mul_ne_int 4 (by simp) hfr_lam
            · rfl
          rw [hlam5] at hfr_lam
          set f0 := Int.fract (t₀ * (v 0 : ℝ)) with hf0_def
          have hf0_lo : 1 / 6 < f0 := f_lo
          have h5f_fr : Int.fract (5 * f0) = 0 := by
            have hexp : ((5 : ℕ) : ℝ) * (t₀ * (v 0 : ℝ)) = 5 * f0 + ((5 * ⌊t₀ * (v 0 : ℝ)⌋ : ℤ) : ℝ) := by
              have := Int.floor_add_fract (t₀ * (v 0 : ℝ)); rw [← hf0_def] at this; push_cast; linarith
            rw [hexp, Int.fract_add_intCast] at hfr_lam; exact hfr_lam
          let rz : ℤ := ⌊5 * f0⌋
          have h5f_eq : 5 * f0 = (rz : ℝ) := by have := Int.floor_add_fract (5 * f0); linarith
          have hrz_pos_r : ((0 : ℤ) : ℝ) < (rz : ℝ) := by push_cast; linarith
          have hrz_pos : (0 : ℤ) < rz := Int.cast_lt.mp hrz_pos_r
          have hrz_1 : (1 : ℤ) ≤ rz := by omega
          have hrz_4 : rz ≤ 4 := by
            have : (rz : ℝ) < 5 := by linarith
            have : rz < (5 : ℤ) := by exact_mod_cast this
            omega
          have hrz_cases : rz = 1 ∨ rz = 2 ∨ rz = 3 ∨ rz = 4 := by omega
          rcases hrz_cases with hr | hr | hr | hr
          · refine ⟨1, le_rfl, Or.inr ?_⟩
            have hf0_val : Int.fract (t₀ * (v 0 : ℝ)) = 1 / 5 := by
              rw [← hf0_def]; rw [hr] at h5f_eq; push_cast at h5f_eq; linarith
            rw [Nat.cast_one, one_mul, circDist_eq_min_fract, hf0_val]; norm_num
          · refine ⟨2, by omega, Or.inr ?_⟩
            have hf0_val : Int.fract (t₀ * (v 0 : ℝ)) = 2 / 5 := by
              rw [← hf0_def]; rw [hr] at h5f_eq; push_cast at h5f_eq; linarith
            rw [mul_assoc, circDist_mul_nat 2, hf0_val, circDist_eq_min_fract]
            push_cast; rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; norm_num
          · refine ⟨2, by omega, Or.inr ?_⟩
            have hf0_val : Int.fract (t₀ * (v 0 : ℝ)) = 3 / 5 := by
              rw [← hf0_def]; rw [hr] at h5f_eq; push_cast at h5f_eq; linarith
            rw [mul_assoc, circDist_mul_nat 2, hf0_val, circDist_eq_min_fract]
            push_cast; rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]
            push_cast; norm_num
          · refine ⟨1, le_rfl, Or.inr ?_⟩
            have hf0_val : Int.fract (t₀ * (v 0 : ℝ)) = 4 / 5 := by
              rw [← hf0_def]; rw [hr] at h5f_eq; push_cast at h5f_eq; linarith
            rw [Nat.cast_one, one_mul, circDist_eq_min_fract, hf0_val]; norm_num
        · obtain ⟨μ', hμ'1, hlo, hhi⟩ := scale_into_twelfth_sixth hpos_lam hd_lam.le
          refine ⟨μ' * lam, by nlinarith, Or.inl ?_⟩
          have hm_eq : (((μ' * lam : ℕ) : ℝ) * t₀) * (v 0 : ℝ) = (μ' : ℝ) * ((lam : ℝ) * (t₀ * (v 0 : ℝ))) := by
            push_cast; ring
          rw [hm_eq]; exact ⟨hlo, hhi⟩
    obtain ⟨μ, _, hs_dist⟩ := hex_μ
    let s : ℝ := (μ : ℝ) * t₀
    -- Both 2 * s and 4 * s satisfy fract(· * w3) = 0 and circDist(· * v 0) ≥ 1/6!
    have hz_mul_s : ∀ c : ℕ, Int.fract (((c : ℝ) * s) * (w3 : ℝ)) = 0 := by
      intro c
      have heq : ((c : ℝ) * s) * (w3 : ℝ) = (((c * μ : ℕ) : ℤ) : ℝ) := by
        dsimp [s, t₀]; push_cast; field_simp [ne_of_gt hw3_r]
      rw [heq, Int.fract_intCast]
    have h24_safe : circDist (((2 : ℕ) : ℝ) * (s * (v 0 : ℝ))) ≥ 1 / 6 ∧
        circDist (((4 : ℕ) : ℝ) * (s * (v 0 : ℝ))) ≥ 1 / 6 := by
      rw [circDist_mul_nat 2, circDist_mul_nat 4]
      set f := Int.fract (s * (v 0 : ℝ))
      have hf0 := Int.fract_nonneg (s * (v 0 : ℝ)); have hf1 := Int.fract_lt_one (s * (v 0 : ℝ))
      rcases hs_dist with ⟨hlo, hhi⟩ | heq5
      · rw [circDist_eq_min_fract] at hlo hhi
        have hcases : (1 / 12 < f ∧ f ≤ 1 / 6) ∨ (5 / 6 ≤ f ∧ f < 11 / 12) := by
          rcases min_cases f (1 - f) with ⟨hm, _⟩ | ⟨hm, _⟩
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
        constructor <;> rw [circDist_ge_iff_fract] <;> push_cast
        · rcases hcases with ⟨g1, g2⟩ | ⟨g1, g2⟩
          · rw [fract_eq_sub_int (2 * f) 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; exact ⟨by linarith, by linarith⟩
          · rw [fract_eq_sub_int (2 * f) 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; exact ⟨by linarith, by linarith⟩
        · rcases hcases with ⟨g1, g2⟩ | ⟨g1, g2⟩
          · rw [fract_eq_sub_int (4 * f) 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; exact ⟨by linarith, by linarith⟩
          · rw [fract_eq_sub_int (4 * f) 3 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; exact ⟨by linarith, by linarith⟩
      · rw [circDist_eq_min_fract] at heq5
        have hcases : f = 1 / 5 ∨ f = 4 / 5 := by
          rcases min_cases f (1 - f) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> [left; right] <;> linarith
        constructor <;> rw [circDist_ge_iff_fract] <;> push_cast <;> rcases hcases with hf_v | hf_v <;> rw [hf_v]
        · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
        · rw [fract_eq_sub_int _ 1 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
        · rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
        · rw [fract_eq_sub_int _ 3 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; constructor <;> norm_num
    have hm2 := hmid_w4 (((2 : ℕ) : ℝ) * s) (by rw [mul_assoc]; exact h24_safe.1) (hz_mul_s 2)
    have hm4 := hmid_w4 (((4 : ℕ) : ℝ) * s) (by rw [mul_assoc]; exact h24_safe.2) (hz_mul_s 4)
    set y := Int.fract ((((2 : ℕ) : ℝ) * s) * (w4 : ℝ)) with hy_def
    have hy4 : Int.fract ((((4 : ℕ) : ℝ) * s) * (w4 : ℝ)) = Int.fract (2 * y) := by
      have h2s : (((4 : ℕ) : ℝ) * s) * (w4 : ℝ) = 2 * ((((2 : ℕ) : ℝ) * s) * (w4 : ℝ)) := by push_cast; ring
      have hexp : 2 * ((((2 : ℕ) : ℝ) * s) * (w4 : ℝ)) = 2 * y + ((2 * ⌊(((2 : ℕ) : ℝ) * s) * (w4 : ℝ)⌋ : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract ((((2 : ℕ) : ℝ) * s) * (w4 : ℝ))
        rw [← hy_def] at hf
        calc 2 * ((((2 : ℕ) : ℝ) * s) * (w4 : ℝ)) = 2 * ((⌊(((2 : ℕ) : ℝ) * s) * (w4 : ℝ)⌋ : ℝ) + y) := by rw [hf]
          _ = _ := by push_cast; ring
      rw [h2s, hexp, Int.fract_add_intCast]
    rw [hy4] at hm4
    rcases lt_or_ge y (1 / 2) with hylt | hyge
    · rw [fract_eq_sub_int (2 * y) 0 (by push_cast; linarith) (by push_cast; linarith)] at hm4
      push_cast at hm4; linarith [hm2.1, hm4.2]
    · rw [fract_eq_sub_int (2 * y) 1 (by push_cast; linarith) (by push_cast; linarith)] at hm4
      push_cast at hm4; linarith [hm2.2, hm4.1]
  -- Apply hdvd_odd to (v 3, v 4) and (v 4, v 3)!
  have hdvd3 : v 3 ∣ v 0 := hdvd_odd (v 3) (v 4) hodd3 (hnot3 2) (hv_pos 3) hodd4 (hnot3 3)
    (fun t ⟨h0, h1, h2, h3, h4⟩ => hno_D t fun i => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl <;> assumption)
  have hdvd4 : v 4 ∣ v 0 := hdvd_odd (v 4) (v 3) hodd4 (hnot3 3) (hv_pos 4) hodd3 (hnot3 2)
    (fun t ⟨h0, h1, h2, h4, h3⟩ => hno_D t fun i => by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl <;> assumption)
  have h6v3_le : 6 * v 3 ≤ v 0 := by
    have hcop : Nat.Coprime 6 (v 3) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd3).mul_left
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hnot3 2))
    exact Nat.le_of_dvd (hv_pos 0) (hcop.mul_dvd_of_dvd_of_dvd hdvd6_0 hdvd3)
  have h6v4_le : 6 * v 4 ≤ v 0 := by
    have hcop : Nat.Coprime 6 (v 4) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd4).mul_left
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hnot3 3))
    exact Nat.le_of_dvd (hv_pos 0) (hcop.mul_dvd_of_dvd_of_dvd hdvd6_0 hdvd4)
  -- Finale of Prop 4.1: test t_tilde = 1 / (6 * v 0)!
  have hv0_r : (0 : ℝ) < (v 0 : ℝ) := Nat.cast_pos.mpr (hv_pos 0)
  let t_tilde : ℝ := 1 / (6 * (v 0 : ℝ))
  have hv1_safe_all : ∀ lam : ℕ, 1 ≤ lam → lam ≤ 5 →
      1 / 6 < circDist (((lam : ℝ) * t_tilde) * (v 1 : ℝ)) := by
    intro lam hl1 hl5
    by_contra hle1
    have hs0 : circDist (((lam : ℝ) * t_tilde) * (v 0 : ℝ)) ≥ 1 / 6 := by
      have heq : ((lam : ℝ) * t_tilde) * (v 0 : ℝ) = (lam : ℝ) / 6 := by
        dsimp [t_tilde]; field_simp [ne_of_gt hv0_r]
      rw [heq, circDist_ge_iff_fract]
      have h1r : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hl1
      have h5r : (lam : ℝ) ≤ 5 := by exact_mod_cast hl5
      rw [fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact ⟨by linarith, by linarith⟩
    have hu_small : ∀ {u : ℕ}, 6 * u ≤ v 0 → circDist (((lam : ℝ) * t_tilde) * (u : ℝ)) ≤ 1 / 6 := by
      intro u hu_le
      have hur : 6 * (u : ℝ) ≤ (v 0 : ℝ) := by exact_mod_cast hu_le
      have hl5r : (lam : ℝ) ≤ 5 := by exact_mod_cast hl5
      have hnn : 0 ≤ ((lam : ℝ) * t_tilde) * (u : ℝ) := by dsimp [t_tilde]; positivity
      have hub : ((lam : ℝ) * t_tilde) * (u : ℝ) ≤ 5 / 36 := by
        dsimp [t_tilde]
        have : ((lam : ℝ) * (1 / (6 * (v 0 : ℝ)))) * (u : ℝ) = ((lam : ℝ) * (u : ℝ)) / (6 * (v 0 : ℝ)) := by ring
        rw [this, div_le_iff₀ (by positivity)]
        nlinarith
      rw [circDist_eq_min_fract, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact le_trans (min_le_left _ _) (by linarith)
    -- Swap v 1 and v 2 so v 1 is in slot 2 for renault_arg3!
    let w : Fin 5 → ℕ := ![v 0, v 2, v 1, v 3, v 4]
    have hw_not3 : ∀ j : Fin 4, ¬ 3 ∣ w j.succ := by
      intro j; fin_cases j <;> [exact hnot3 1; exact hnot3 0; exact hnot3 2; exact hnot3 3]
    obtain ⟨t', ht'⟩ := renault_arg3 w (dvd_trans (by decide : 3 ∣ 6) hdvd6_0) hw_not3
      ((lam : ℝ) * t_tilde) hs0 (le_of_not_gt hle1) (hu_small h6v3_le) (hu_small h6v4_le)
    apply hno_D t'
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl
    · exact ht' 0
    · exact ht' 2
    · exact ht' 1
    · exact ht' 3
    · exact ht' 4
  have h1_gt := hv1_safe_all 1 le_rfl (by omega)
  rw [Nat.cast_one, one_mul] at h1_gt
  obtain ⟨flo, fhi⟩ := (circDist_gt_iff_fract _ _).mp h1_gt
  obtain ⟨lam, hl2, hl5, hbad⟩ := h_claim24 (Int.fract (t_tilde * (v 1 : ℝ))) flo (by linarith)
  have hlam_gt := hv1_safe_all lam (by omega) hl5
  rw [mul_assoc, circDist_mul_nat lam, circDist_gt_iff_fract] at hlam_gt
  rcases hbad with h1 | h2 <;> linarith [hlam_gt.1, hlam_gt.2]

/- ### Renault Proposition 3.1: Two Multiples of 3 (pages 3–4) -/

private lemma three_5_intersect_intervals {x : ℝ} (_hx0 : 0 ≤ x) (_hx1 : x < 1)
    (h3 : circDist (((3 : ℕ) : ℝ) * x) < 1 / 6)
    (h5 : circDist (((5 : ℕ) : ℝ) * x) < 1 / 6) :
    (x < 1 / 30 ∨ 29 / 30 < x) ∨ (11 / 30 < x ∧ x < 7 / 18) ∨ (11 / 18 < x ∧ x < 19 / 30) := by
  by_contra hnone
  push_cast at h3 h5
  rcases lt_or_ge x (1 / 30) with c1 | c1
  · exact hnone (Or.inl (Or.inl c1))
  rcases lt_or_ge x (1 / 5) with c2 | c2
  · rcases lt_or_ge x (1 / 18) with c2a | c2a
    · have := circDist_ge_sixth_of_int (5 * x) 0 (by push_cast; linarith) (by push_cast; linarith)
      linarith
    · have := circDist_ge_sixth_of_int (3 * x) 0 (by push_cast; linarith) (by push_cast; linarith)
      linarith
  rcases le_or_gt x (11 / 30) with c3 | c3
  · rcases le_or_gt x (5 / 18) with c3a | c3a
    · have := circDist_ge_sixth_of_int (3 * x) 0 (by push_cast; linarith) (by push_cast; linarith)
      linarith
    · have := circDist_ge_sixth_of_int (5 * x) 1 (by push_cast; linarith) (by push_cast; linarith)
      linarith
  rcases lt_or_ge x (7 / 18) with c4 | c4
  · exact hnone (Or.inr (Or.inl ⟨c3, c4⟩))
  rcases le_or_gt x (11 / 18) with c5 | c5
  · have := circDist_ge_sixth_of_int (3 * x) 1 (by push_cast; linarith) (by push_cast; linarith)
    linarith
  rcases lt_or_ge x (19 / 30) with c6 | c6
  · exact hnone (Or.inr (Or.inr ⟨c5, c6⟩))
  rcases le_or_gt x (4 / 5) with c7 | c7
  · rcases lt_or_ge x (13 / 18) with c7a | c7a
    · have := circDist_ge_sixth_of_int (5 * x) 3 (by push_cast; linarith) (by push_cast; linarith)
      linarith
    · have := circDist_ge_sixth_of_int (3 * x) 2 (by push_cast; linarith) (by push_cast; linarith)
      linarith
  rcases le_or_gt x (29 / 30) with c8 | c8
  · rcases le_or_gt x (17 / 18) with c8a | c8a
    · have := circDist_ge_sixth_of_int (3 * x) 2 (by push_cast; linarith) (by push_cast; linarith)
      linarith
    · have := circDist_ge_sixth_of_int (5 * x) 4 (by push_cast; linarith) (by push_cast; linarith)
      linarith
  · exact hnone (Or.inl (Or.inr c8))

private lemma prop_3_1_band_consequences {x : ℝ}
    (hband : (11 / 30 < x ∧ x < 7 / 18) ∨ (11 / 18 < x ∧ x < 19 / 30)) :
    circDist x ≥ 1 / 6 ∧
    circDist (((2 : ℕ) : ℝ) * x) ≥ 1 / 6 ∧
    circDist (((2 : ℕ) : ℝ) * x + 1 / 2) ≥ 1 / 6 ∧
    circDist (((4 : ℕ) : ℝ) * x) ≥ 1 / 6 ∧
    1 / 10 < circDist (((3 : ℕ) : ℝ) * x) ∧
    circDist (((3 : ℕ) : ℝ) * x + 1 / 2) ≥ 1 / 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact circDist_ge_sixth_of_int x 0 (by push_cast; linarith) (by push_cast; linarith)
  · push_cast; rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact circDist_ge_sixth_of_int (2 * x) 0 (by push_cast; linarith) (by push_cast; linarith)
    · exact circDist_ge_sixth_of_int (2 * x) 1 (by push_cast; linarith) (by push_cast; linarith)
  · push_cast; rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact circDist_ge_sixth_of_int (2 * x + 1 / 2) 1 (by push_cast; linarith) (by push_cast; linarith)
  · push_cast; rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact circDist_ge_sixth_of_int (4 * x) 1 (by push_cast; linarith) (by push_cast; linarith)
    · exact circDist_ge_sixth_of_int (4 * x) 2 (by push_cast; linarith) (by push_cast; linarith)
  · push_cast; rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact circDist_gt_tenth_of_int (3 * x) 1 (by push_cast; linarith) (by push_cast; linarith)
  · push_cast; rcases hband with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact circDist_ge_sixth_of_int (3 * x + 1 / 2) 1 (by push_cast; linarith) (by push_cast; linarith)
    · exact circDist_ge_sixth_of_int (3 * x + 1 / 2) 2 (by push_cast; linarith) (by push_cast; linarith)

private lemma mult3_shift_pm_sixth {u : ℕ} (hdvd3 : 3 ∣ u) (s : ℝ) {α : ℤ} (hα : α = 1 ∨ α = -1) :
    (6 ∣ u → circDist ((s + (α : ℝ) / 6) * (u : ℝ)) = circDist (s * (u : ℝ))) ∧
    (¬ 6 ∣ u → circDist ((s + (α : ℝ) / 6) * (u : ℝ)) = circDist (Int.fract (s * (u : ℝ)) + 1 / 2)) := by
  constructor
  · intro hd6
    have h6 : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [h6]; exact circDist_shift_dvd (by omega) hd6 s α
  · intro hnd6
    have hm6 : u % 6 = 3 := by omega
    let q : ℕ := u / 6
    have hdiv : 6 * q + 3 = u := by dsimp [q]; omega
    have huc : (u : ℝ) = 6 * (q : ℝ) + 3 := by exact_mod_cast hdiv.symm
    rcases hα with rfl | rfl
    · have hexp : (s + ((1 : ℤ) : ℝ) / 6) * (u : ℝ) =
          (Int.fract (s * (u : ℝ)) + 1 / 2) + ((⌊s * (u : ℝ)⌋ + (q : ℤ) : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract (s * (u : ℝ))
        have hu16 : (((1 : ℤ) : ℝ) / 6) * (u : ℝ) = (q : ℝ) + 1 / 2 := by rw [huc]; push_cast; ring
        calc (s + ((1 : ℤ) : ℝ) / 6) * (u : ℝ) = s * (u : ℝ) + (((1 : ℤ) : ℝ) / 6) * (u : ℝ) := add_mul _ _ _
          _ = ((⌊s * (u : ℝ)⌋ : ℝ) + Int.fract (s * (u : ℝ))) + ((q : ℝ) + 1 / 2) := by linarith [hf, hu16]
          _ = _ := by push_cast; ring
      rw [hexp, circDist_add_int]
    · have hexp : (s + ((-1 : ℤ) : ℝ) / 6) * (u : ℝ) =
          (Int.fract (s * (u : ℝ)) + 1 / 2) + ((⌊s * (u : ℝ)⌋ - (q : ℤ) - 1 : ℤ) : ℝ) := by
        have hf := Int.floor_add_fract (s * (u : ℝ))
        have hu16 : (((-1 : ℤ) : ℝ) / 6) * (u : ℝ) = -(q : ℝ) - 1 / 2 := by rw [huc]; push_cast; ring
        calc (s + ((-1 : ℤ) : ℝ) / 6) * (u : ℝ) = s * (u : ℝ) + (((-1 : ℤ) : ℝ) / 6) * (u : ℝ) := add_mul _ _ _
          _ = ((⌊s * (u : ℝ)⌋ : ℝ) + Int.fract (s * (u : ℝ))) + (-(q : ℝ) - 1 / 2) := by linarith [hf, hu16]
          _ = _ := by push_cast; ring
      rw [hexp, circDist_add_int]

private lemma prop_3_1_hsym
    (u0 u1 v2 v3 v4 : ℕ) (t_hat : ℝ)
    (ht_hat_fr2 : Int.fract (t_hat * (v2 : ℝ)) = 5 / 6)
    (hv2_not3 : ¬ 3 ∣ v2) (hv3_not3 : ¬ 3 ∣ v3) (hv4_not3 : ¬ 3 ∣ v4)
    (hu0_3 : 3 ∣ u0) (hu1_3 : 3 ∣ u1) (hu_6 : 6 ∣ u0 ∨ 6 ∣ u1)
    (hu_even : (2 ∣ u0 ∧ 2 ∣ u1 ∧ 2 ∣ v2) → (¬ 2 ∣ v3 ∧ ¬ 2 ∣ v4))
    (hno_u : ∀ t : ℝ, ¬ (circDist (t * (u0 : ℝ)) ≥ 1 / 6 ∧ circDist (t * (u1 : ℝ)) ≥ 1 / 6 ∧
      circDist (t * (v2 : ℝ)) ≥ 1 / 6 ∧ circDist (t * (v3 : ℝ)) ≥ 1 / 6 ∧
      circDist (t * (v4 : ℝ)) ≥ 1 / 6))
    (hmax_u : ∀ s : ℝ, (Int.fract (s * (v2 : ℝ)) = 1 / 6 ∨ Int.fract (s * (v2 : ℝ)) = 1 / 2 ∨
      Int.fract (s * (v2 : ℝ)) = 5 / 6) →
      min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) ≤ circDist (t_hat * (u0 : ℝ)))
    (hle_u : circDist (t_hat * (u0 : ℝ)) ≤ circDist (t_hat * (u1 : ℝ))) :
    circDist (t_hat * (u0 : ℝ)) = 0 := by
  have hd0_lt : circDist (t_hat * (u0 : ℝ)) < 1 / 6 := by
    by_contra hge0
    have hs0 : circDist (t_hat * (u0 : ℝ)) ≥ 1 / 6 := le_of_not_gt hge0
    have hs1 : circDist (t_hat * (u1 : ℝ)) ≥ 1 / 6 := le_trans hs0 hle_u
    let w : Fin 5 → ℕ := ![u0, u1, v2, v3, v4]
    have hw_not3 : ∀ r : Fin 3, ¬ 3 ∣ w r.succ.succ := by
      intro r; fin_cases r <;> [exact hv2_not3; exact hv3_not3; exact hv4_not3]
    obtain ⟨t', ht'⟩ := renault_arg2 w hu0_3 hu1_3 hw_not3 t_hat hs0 hs1 (Or.inr (Or.inr ht_hat_fr2))
    exact hno_u t' ⟨ht' 0, ht' 1, ht' 2, ht' 3, ht' 4⟩
  by_contra hd0_ne
  have hd0_pos : 0 < circDist (t_hat * (u0 : ℝ)) :=
    lt_of_le_of_ne (circDist_nonneg _) (Ne.symm hd0_ne)
  set d0 := circDist (t_hat * (u0 : ℝ))
  have hu0_mul_gt : ∀ lam : ℕ, 2 ≤ lam → lam ≤ 5 → d0 < circDist (((lam : ℝ) * t_hat) * (u0 : ℝ)) := by
    intro lam hl2 hl5
    rw [mul_assoc, circDist_mul_nat lam]
    set f0 := Int.fract (t_hat * (u0 : ℝ))
    have hf0_0 := Int.fract_nonneg (t_hat * (u0 : ℝ)); have hf0_1 := Int.fract_lt_one (t_hat * (u0 : ℝ))
    have hd0_def : d0 = min f0 (1 - f0) := circDist_eq_min_fract _
    have hl2r : (2 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hl2
    have hl5r : (lam : ℝ) ≤ 5 := by exact_mod_cast hl5
    rcases min_cases f0 (1 - f0) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [circDist_gt_iff_fract, Int.fract_eq_self.mpr ⟨by positivity, by nlinarith⟩]
      exact ⟨by nlinarith, by nlinarith⟩
    · have hfn : Int.fract (-(t_hat * (u0 : ℝ))) = d0 := by
        rw [fract_neg_of_pos (by linarith)]; linarith
      have hsym_n : circDist ((lam : ℝ) * f0) = circDist ((lam : ℝ) * d0) := by
        rw [← circDist_mul_nat lam, ← circDist_neg]
        have h1 : -((lam : ℝ) * (t_hat * (u0 : ℝ))) = (lam : ℝ) * (-(t_hat * (u0 : ℝ))) := by ring
        rw [h1, circDist_mul_nat lam, hfn]
      rw [hsym_n, circDist_gt_iff_fract, Int.fract_eq_self.mpr ⟨by positivity, by nlinarith⟩]
      exact ⟨by nlinarith, by nlinarith⟩
  have hfr2_3 : Int.fract ((((3 : ℕ) : ℝ) * t_hat) * (v2 : ℝ)) = 1 / 2 := by
    have hexp : (((3 : ℕ) : ℝ) * t_hat) * (v2 : ℝ) = (1 / 2 : ℝ) + ((3 * ⌊t_hat * (v2 : ℝ)⌋ + 2 : ℤ) : ℝ) := by
      have hf := Int.floor_add_fract (t_hat * (v2 : ℝ)); rw [ht_hat_fr2] at hf; push_cast; linarith
    rw [hexp, Int.fract_add_intCast, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; ring
  have hfr2_5 : Int.fract ((((5 : ℕ) : ℝ) * t_hat) * (v2 : ℝ)) = 1 / 6 := by
    have hexp : (((5 : ℕ) : ℝ) * t_hat) * (v2 : ℝ) = (1 / 6 : ℝ) + ((5 * ⌊t_hat * (v2 : ℝ)⌋ + 4 : ℤ) : ℝ) := by
      have hf := Int.floor_add_fract (t_hat * (v2 : ℝ)); rw [ht_hat_fr2] at hf; push_cast; linarith
    rw [hexp, Int.fract_add_intCast, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]; push_cast; ring
  have hu1_3_le : circDist ((((3 : ℕ) : ℝ) * t_hat) * (u1 : ℝ)) ≤ d0 := by
    have hm := hmax_u (((3 : ℕ) : ℝ) * t_hat) (Or.inr (Or.inl hfr2_3))
    have hg := hu0_mul_gt 3 (by omega) (by omega)
    rcases min_cases (circDist ((((3 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)))
      (circDist ((((3 : ℕ) : ℝ) * t_hat) * (u1 : ℝ))) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> linarith
  have hu1_5_le : circDist ((((5 : ℕ) : ℝ) * t_hat) * (u1 : ℝ)) ≤ d0 := by
    have hm := hmax_u (((5 : ℕ) : ℝ) * t_hat) (Or.inl hfr2_5)
    have hg := hu0_mul_gt 5 (by omega) (by omega)
    rcases min_cases (circDist ((((5 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)))
      (circDist ((((5 : ℕ) : ℝ) * t_hat) * (u1 : ℝ))) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> linarith
  set x1 := Int.fract (t_hat * (u1 : ℝ)) with hx1_def
  have h3x1 : circDist (((3 : ℕ) : ℝ) * x1) ≤ d0 := by
    rw [← circDist_mul_nat 3, ← mul_assoc]; exact hu1_3_le
  have h5x1 : circDist (((5 : ℕ) : ℝ) * x1) ≤ d0 := by
    rw [← circDist_mul_nat 5, ← mul_assoc]; exact hu1_5_le
  have hband : (11 / 30 < x1 ∧ x1 < 7 / 18) ∨ (11 / 18 < x1 ∧ x1 < 19 / 30) := by
    rcases three_5_intersect_intervals (Int.fract_nonneg _) (Int.fract_lt_one _)
      (lt_of_le_of_lt h3x1 hd0_lt) (lt_of_le_of_lt h5x1 hd0_lt) with hsmall | hb1 | hb2
    · exfalso
      have hd1_ge : d0 ≤ circDist x1 := by rw [circDist_fract]; exact hle_u
      have h3_eq : circDist (((3 : ℕ) : ℝ) * x1) = 3 * circDist x1 := by
        push_cast; rw [circDist_eq_min_fract, circDist_eq_min_fract]
        have hx0 : 0 ≤ x1 := Int.fract_nonneg _
        have hx1' : x1 < 1 := Int.fract_lt_one _
        rcases hsmall with hlo | hhi
        · rw [Int.fract_eq_self.mpr ⟨hx0, hx1'⟩,
            fract_eq_sub_int (3 * x1) 0 (by push_cast; linarith) (by push_cast; linarith)]
          push_cast
          rw [min_eq_left (by linarith), min_eq_left (by linarith)]
          ring
        · rw [Int.fract_eq_self.mpr ⟨hx0, hx1'⟩,
            fract_eq_sub_int (3 * x1) 2 (by push_cast; linarith) (by push_cast; linarith)]
          push_cast
          rw [min_eq_right (by linarith), min_eq_right (by linarith)]
          ring
      linarith
    · exact Or.inl hb1
    · exact Or.inr hb2
  obtain ⟨hx1_safe, h2x1_safe, h2x1_half_safe, h4x1_safe, h3x1_gt10, h3x1_half_safe⟩ :=
    prop_3_1_band_consequences hband
  have hd0_gt10 : 1 / 10 < d0 := lt_of_lt_of_le h3x1_gt10 h3x1
  have hu0_bounds :
      circDist ((((2 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)) ≥ 1 / 6 ∧
      circDist (Int.fract ((((2 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)) + 1 / 2) ≥ 1 / 6 ∧
      circDist ((((3 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)) ≥ 1 / 6 ∧
      circDist ((((4 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)) ≥ 1 / 6 ∧
      circDist (Int.fract (t_hat * (u0 : ℝ)) + 1 / 2) ≥ 1 / 6 := by
    set f0 := Int.fract (t_hat * (u0 : ℝ))
    have hf0_0 := Int.fract_nonneg (t_hat * (u0 : ℝ)); have hf0_1 := Int.fract_lt_one (t_hat * (u0 : ℝ))
    have hd0_def : d0 = min f0 (1 - f0) := circDist_eq_min_fract _
    have hf0_or : (1 / 10 < f0 ∧ f0 < 1 / 6) ∨ (5 / 6 < f0 ∧ f0 < 9 / 10) := by
      rcases min_cases f0 (1 - f0) with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_assoc, circDist_mul_nat 2]; push_cast
      rcases hf0_or with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact circDist_ge_sixth_of_int (2 * f0) 0 (by push_cast; linarith) (by push_cast; linarith)
      · exact circDist_ge_sixth_of_int (2 * f0) 1 (by push_cast; linarith) (by push_cast; linarith)
    · have h2f : Int.fract ((((2 : ℕ) : ℝ) * t_hat) * (u0 : ℝ)) = Int.fract (2 * f0) := by
        have hexp : (((2 : ℕ) : ℝ) * t_hat) * (u0 : ℝ) = 2 * f0 + ((2 * ⌊t_hat * (u0 : ℝ)⌋ : ℤ) : ℝ) := by
          have := Int.floor_add_fract (t_hat * (u0 : ℝ)); push_cast; linarith
        rw [hexp, Int.fract_add_intCast]
      rw [h2f]
      rcases hf0_or with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · rw [fract_eq_sub_int (2 * f0) 0 (by push_cast; linarith) (by push_cast; linarith)]
        exact circDist_ge_sixth_of_int _ 0 (by push_cast; linarith) (by push_cast; linarith)
      · rw [fract_eq_sub_int (2 * f0) 1 (by push_cast; linarith) (by push_cast; linarith)]
        exact circDist_ge_sixth_of_int _ 1 (by push_cast; linarith) (by push_cast; linarith)
    · rw [mul_assoc, circDist_mul_nat 3]; push_cast
      rcases hf0_or with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact circDist_ge_sixth_of_int (3 * f0) 0 (by push_cast; linarith) (by push_cast; linarith)
      · exact circDist_ge_sixth_of_int (3 * f0) 2 (by push_cast; linarith) (by push_cast; linarith)
    · rw [mul_assoc, circDist_mul_nat 4]; push_cast
      rcases hf0_or with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact circDist_ge_sixth_of_int (4 * f0) 0 (by push_cast; linarith) (by push_cast; linarith)
      · exact circDist_ge_sixth_of_int (4 * f0) 3 (by push_cast; linarith) (by push_cast; linarith)
    · rcases hf0_or with ⟨g1, g2⟩ | ⟨g1, g2⟩
      · exact circDist_ge_sixth_of_int (f0 + 1 / 2) 0 (by push_cast; linarith) (by push_cast; linarith)
      · exact circDist_ge_sixth_of_int (f0 + 1 / 2) 1 (by push_cast; linarith) (by push_cast; linarith)
  obtain ⟨hu0_2, hu0_2h, hu0_3s, hu0_4, hu0_1h⟩ := hu0_bounds
  -- Helper for fract((lam * t_hat + α / 6) * v2) when v2 = 6 * q2 + rem2!
  have hv2_shift_fr : ∀ (lam : ℕ) (α : ℤ) (rem2 : ℕ), v2 % 6 = rem2 →
      Int.fract ((((lam : ℝ) * t_hat + (α : ℝ) / 6) * (v2 : ℝ))) =
      Int.fract ((5 * (lam : ℝ) + (α : ℝ) * (rem2 : ℝ)) / 6) := by
    intro lam α rem2 hrem
    let q2 : ℕ := v2 / 6
    have hdiv2 : 6 * q2 + rem2 = v2 := by dsimp [q2]; omega
    have hv2c : (v2 : ℝ) = 6 * (q2 : ℝ) + (rem2 : ℝ) := by exact_mod_cast hdiv2.symm
    have hf := Int.floor_add_fract (t_hat * (v2 : ℝ))
    rw [ht_hat_fr2] at hf
    have htv : t_hat * (v2 : ℝ) = (⌊t_hat * (v2 : ℝ)⌋ : ℝ) + 5 / 6 := by linarith
    have hav : ((α : ℝ) / 6) * (v2 : ℝ) = (α : ℝ) * (q2 : ℝ) + (α : ℝ) * (rem2 : ℝ) / 6 := by
      rw [hv2c]; ring
    have hexp : ((lam : ℝ) * t_hat + (α : ℝ) / 6) * (v2 : ℝ) =
        ((5 * (lam : ℝ) + (α : ℝ) * (rem2 : ℝ)) / 6) +
        (((lam : ℤ) * ⌊t_hat * (v2 : ℝ)⌋ + α * (q2 : ℤ) : ℤ) : ℝ) := by
      calc ((lam : ℝ) * t_hat + (α : ℝ) / 6) * (v2 : ℝ)
          = (lam : ℝ) * (t_hat * (v2 : ℝ)) + ((α : ℝ) / 6) * (v2 : ℝ) := by ring
        _ = (lam : ℝ) * ((⌊t_hat * (v2 : ℝ)⌋ : ℝ) + 5 / 6) +
            ((α : ℝ) * (q2 : ℝ) + (α : ℝ) * (rem2 : ℝ) / 6) := by
              rw [hav]; conv_lhs => rw [htv]
        _ = _ := by push_cast; ring
    rw [hexp, Int.fract_add_intCast]
  have hlam_x1_half : ∀ lam : ℕ,
      circDist (Int.fract ((((lam : ℕ) : ℝ) * t_hat) * (u1 : ℝ)) + 1 / 2) =
      circDist (((lam : ℕ) : ℝ) * x1 + 1 / 2) := by
    intro lam
    have hexp : (((lam : ℕ) : ℝ) * t_hat) * (u1 : ℝ) =
        ((lam : ℕ) : ℝ) * x1 + (((lam : ℤ) * ⌊t_hat * (u1 : ℝ)⌋ : ℤ) : ℝ) := by
      have hf := Int.floor_add_fract (t_hat * (u1 : ℝ)); rw [← hx1_def] at hf
      calc (((lam : ℕ) : ℝ) * t_hat) * (u1 : ℝ) = ((lam : ℕ) : ℝ) * ((⌊t_hat * (u1 : ℝ)⌋ : ℝ) + x1) := by
            rw [mul_assoc, hf]
        _ = _ := by push_cast; ring
    rw [hexp, Int.fract_add_intCast]
    have hsub := fract_eq_sub_floor (((lam : ℕ) : ℝ) * x1)
    have hrw : Int.fract (((lam : ℕ) : ℝ) * x1) + 1 / 2 =
        (((lam : ℕ) : ℝ) * x1 + 1 / 2) - (⌊((lam : ℕ) : ℝ) * x1⌋ : ℝ) := by linarith
    rw [hrw, circDist_sub_int]
  -- Helper when 6 ∣ u0, 6 ∣ u1, and 2 ∣ v2!
  have hboth6_even2 : 6 ∣ u0 → 6 ∣ u1 → 2 ∣ v2 → False := by
    intro h6_0 h6_1 he2_2
    obtain ⟨hodd3, hodd4⟩ := hu_even ⟨dvd_trans (by decide) h6_0, dvd_trans (by decide) h6_1, he2_2⟩
    let t1 : ℝ := ((2 : ℕ) : ℝ) * t_hat
    have ht1_v2 : circDist (t1 * (v2 : ℝ)) ≥ 1 / 6 := by
      change circDist ((((2 : ℕ) : ℝ) * t_hat) * (v2 : ℝ)) ≥ 1 / 6
      rw [mul_assoc, circDist_mul_nat 2, ht_hat_fr2]
      exact circDist_ge_sixth_of_int _ 1 (by push_cast; norm_num) (by push_cast; norm_num)
    have ht1_u1 : circDist (t1 * (u1 : ℝ)) ≥ 1 / 6 := by
      change circDist ((((2 : ℕ) : ℝ) * t_hat) * (u1 : ℝ)) ≥ 1 / 6
      rw [mul_assoc, circDist_mul_nat 2]; exact h2x1_safe
    have h34_t1 : circDist (t1 * (v3 : ℝ)) < 1 / 6 ∨ circDist (t1 * (v4 : ℝ)) < 1 / 6 := by
      by_contra hge
      exact hno_u t1 ⟨hu0_2, ht1_u1, ht1_v2,
        le_of_not_gt fun g => hge (Or.inl g), le_of_not_gt fun g => hge (Or.inr g)⟩
    have h34_t2 : circDist ((t1 + 1 / 2) * (v3 : ℝ)) < 1 / 6 ∨ circDist ((t1 + 1 / 2) * (v4 : ℝ)) < 1 / 6 := by
      by_contra hge
      apply hno_u (t1 + 1 / 2)
      refine ⟨?_, ?_, ?_, le_of_not_gt fun g => hge (Or.inl g), le_of_not_gt fun g => hge (Or.inr g)⟩
      · rw [circDist_even_add_half (dvd_trans (by decide) h6_0)]; exact hu0_2
      · rw [circDist_even_add_half (dvd_trans (by decide) h6_1)]; exact ht1_u1
      · rw [circDist_even_add_half he2_2]; exact ht1_v2
    apply hno_u (2 * t1 + 1 / 2)
    have h2t1 : 2 * t1 = ((4 : ℕ) : ℝ) * t_hat := by dsimp [t1]; push_cast; ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [circDist_even_add_half (dvd_trans (by decide) h6_0), h2t1]; exact hu0_4
    · rw [circDist_even_add_half (dvd_trans (by decide) h6_1), h2t1, mul_assoc, circDist_mul_nat 4]; exact h4x1_safe
    · rw [circDist_even_add_half he2_2, h2t1, mul_assoc, circDist_mul_nat 4, ht_hat_fr2]
      exact circDist_ge_sixth_of_int _ 3 (by push_cast; norm_num) (by norm_num)
    · apply odd_double_plus_half_safe hodd3 t1
      rcases h34_t1 with g1 | g1
      · exact Or.inl g1
      · rcases h34_t2 with g2 | g2
        · exact Or.inr (odd_half_unsafe_imp_mid hodd3 t1 g2)
        · exfalso; rcases odd_half_not_both_unsafe hodd4 t1 with c | c <;> linarith
    · apply odd_double_plus_half_safe hodd4 t1
      rcases h34_t1 with g1 | g1
      · rcases h34_t2 with g2 | g2
        · exfalso; rcases odd_half_not_both_unsafe hodd3 t1 with c | c <;> linarith
        · exact Or.inr (odd_half_unsafe_imp_mid hodd4 t1 g2)
      · exact Or.inl g1
  have hv2_mod6 : v2 % 6 = 1 ∨ v2 % 6 = 5 ∨ v2 % 6 = 2 ∨ v2 % 6 = 4 := by omega
  rcases hv2_mod6 with hv2_1 | hv2_5 | hv2_2 | hv2_4
  · -- v2 % 6 = 1: s = 2 * t_hat + 1 / 6
    let s : ℝ := ((2 : ℕ) : ℝ) * t_hat + ((1 : ℤ) : ℝ) / 6
    have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 5 / 6 := by
      rw [hv2_shift_fr 2 1 1 hv2_1, fract_eq_sub_int _ 1 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
    have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
      by_cases h6 : 6 ∣ u0
      · rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inl rfl)).1 h6]; exact hu0_2
      · rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inl rfl)).2 h6]; exact hu0_2h
    have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
      by_cases h6 : 6 ∣ u1
      · rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inl rfl)).1 h6, mul_assoc, circDist_mul_nat 2]; exact h2x1_safe
      · rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inl rfl)).2 h6, hlam_x1_half 2]; exact h2x1_half_safe
    have hm := hmax_u s (Or.inr (Or.inr hs_fr2))
    have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
    linarith
  · -- v2 % 6 = 5: s = 2 * t_hat - 1 / 6
    let s : ℝ := ((2 : ℕ) : ℝ) * t_hat + ((-1 : ℤ) : ℝ) / 6
    have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 5 / 6 := by
      rw [hv2_shift_fr 2 (-1) 5 hv2_5, fract_eq_sub_int _ 0 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
    have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
      by_cases h6 : 6 ∣ u0
      · rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inr rfl)).1 h6]; exact hu0_2
      · rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inr rfl)).2 h6]; exact hu0_2h
    have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
      by_cases h6 : 6 ∣ u1
      · rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inr rfl)).1 h6, mul_assoc, circDist_mul_nat 2]; exact h2x1_safe
      · rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inr rfl)).2 h6, hlam_x1_half 2]; exact h2x1_half_safe
    have hm := hmax_u s (Or.inr (Or.inr hs_fr2))
    have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
    linarith
  · -- v2 % 6 = 2
    by_cases h6_0 : 6 ∣ u0
    · by_cases h6_1 : 6 ∣ u1
      · exact False.elim (hboth6_even2 h6_0 h6_1 (by omega))
      · let s : ℝ := ((3 : ℕ) : ℝ) * t_hat + ((1 : ℤ) : ℝ) / 6
        have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 5 / 6 := by
          rw [hv2_shift_fr 3 1 2 hv2_2, fract_eq_sub_int _ 2 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
        have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
          rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inl rfl)).1 h6_0]; exact hu0_3s
        have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
          rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inl rfl)).2 h6_1, hlam_x1_half 3]; exact h3x1_half_safe
        have hm := hmax_u s (Or.inr (Or.inr hs_fr2))
        have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
        linarith
    · have h6_1 : 6 ∣ u1 := hu_6.resolve_left h6_0
      let s : ℝ := ((1 : ℕ) : ℝ) * t_hat + ((1 : ℤ) : ℝ) / 6
      have hs_eq : s = t_hat + ((1 : ℤ) : ℝ) / 6 := by dsimp [s]; ring
      have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 1 / 6 := by
        rw [hv2_shift_fr 1 1 2 hv2_2, fract_eq_sub_int _ 1 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
      have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
        rw [hs_eq, (mult3_shift_pm_sixth hu0_3 _ (Or.inl rfl)).2 h6_0]; exact hu0_1h
      have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
        rw [hs_eq, (mult3_shift_pm_sixth hu1_3 _ (Or.inl rfl)).1 h6_1, ← circDist_fract]; exact hx1_safe
      have hm := hmax_u s (Or.inl hs_fr2)
      have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
      linarith
  · -- v2 % 6 = 4
    by_cases h6_0 : 6 ∣ u0
    · by_cases h6_1 : 6 ∣ u1
      · exact False.elim (hboth6_even2 h6_0 h6_1 (by omega))
      · let s : ℝ := ((3 : ℕ) : ℝ) * t_hat + ((-1 : ℤ) : ℝ) / 6
        have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 5 / 6 := by
          rw [hv2_shift_fr 3 (-1) 4 hv2_4, fract_eq_sub_int _ 1 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
        have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
          rw [(mult3_shift_pm_sixth hu0_3 _ (Or.inr rfl)).1 h6_0]; exact hu0_3s
        have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
          rw [(mult3_shift_pm_sixth hu1_3 _ (Or.inr rfl)).2 h6_1, hlam_x1_half 3]; exact h3x1_half_safe
        have hm := hmax_u s (Or.inr (Or.inr hs_fr2))
        have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
        linarith
    · have h6_1 : 6 ∣ u1 := hu_6.resolve_left h6_0
      let s : ℝ := ((1 : ℕ) : ℝ) * t_hat + ((1 : ℤ) : ℝ) / 6
      have hs_eq : s = t_hat + ((1 : ℤ) : ℝ) / 6 := by dsimp [s]; ring
      have hs_fr2 : Int.fract (s * (v2 : ℝ)) = 1 / 2 := by
        rw [hv2_shift_fr 1 1 4 hv2_4, fract_eq_sub_int _ 1 (by push_cast; norm_num) (by push_cast; norm_num)]; push_cast; norm_num
      have hs_u0 : circDist (s * (u0 : ℝ)) ≥ 1 / 6 := by
        rw [hs_eq, (mult3_shift_pm_sixth hu0_3 _ (Or.inl rfl)).2 h6_0]; exact hu0_1h
      have hs_u1 : circDist (s * (u1 : ℝ)) ≥ 1 / 6 := by
        rw [hs_eq, (mult3_shift_pm_sixth hu1_3 _ (Or.inl rfl)).1 h6_1, ← circDist_fract]; exact hx1_safe
      have hm := hmax_u s (Or.inr (Or.inl hs_fr2))
      have : 1 / 6 ≤ min (circDist (s * (u0 : ℝ))) (circDist (s * (u1 : ℝ))) := le_min hs_u0 hs_u1
      linarith

private lemma prop_3_1_div_single
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (hdvd3_0 : 3 ∣ v 0) (hdvd3_1 : 3 ∣ v 1)
    (hdvd6_or : 6 ∣ v 0 ∨ 6 ∣ v 1)
    (hnot3 : ∀ r : Fin 3, ¬ 3 ∣ v r.succ.succ)
    (heven_cap : (2 ∣ v 0 ∧ 2 ∣ v 1 ∧ 2 ∣ v 2) → (¬ 2 ∣ v 3 ∧ ¬ 2 ∣ v 4))
    (hno_D : ∀ t : ℝ, ¬ (∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / 6)) :
    6 * v 2 ∣ v 0 ∨ 6 * v 2 ∣ v 1 := by
  have hv2_pos : 0 < v 2 := hv_pos 2
  have hv2_r : (0 : ℝ) < (v 2 : ℝ) := Nat.cast_pos.mpr hv2_pos
  let g : ℕ → ℝ := fun k => (6 * (k : ℝ) + 5) / (6 * (v 2 : ℝ))
  let obj : ℝ → ℝ := fun t => min (circDist (t * (v 0 : ℝ))) (circDist (t * (v 1 : ℝ)))
  obtain ⟨k_max, _, hk_max⟩ := Finset.exists_max_image (Finset.range (v 2)) (fun k => obj (g k))
    ⟨0, Finset.mem_range.mpr hv2_pos⟩
  let t_hat : ℝ := g k_max
  have ht_hat_fr2 : Int.fract (t_hat * (v 2 : ℝ)) = 5 / 6 := by
    have heq : t_hat * (v 2 : ℝ) = (5 / 6 : ℝ) + ((k_max : ℤ) : ℝ) := by
      dsimp [t_hat, g]; push_cast; field_simp [ne_of_gt hv2_r]; ring
    rw [heq, Int.fract_add_intCast, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; ring
  have hmax_56 : ∀ t : ℝ, Int.fract (t * (v 2 : ℝ)) = 5 / 6 → obj t ≤ obj t_hat := by
    intro t ht_fr
    let N : ℤ := ⌊t * (v 2 : ℝ)⌋
    have hex_div : ∃ (k : ℕ) (qz : ℤ), k < v 2 ∧ (N : ℝ) = (v 2 : ℝ) * (qz : ℝ) + (k : ℝ) := by
      rcases le_or_gt 0 N with hnn | hneg
      · let n : ℕ := N.toNat
        have hn_eq : (n : ℤ) = N := Int.toNat_of_nonneg hnn
        let qn : ℕ := n / v 2
        let rn : ℕ := n % v 2
        refine ⟨rn, (qn : ℤ), Nat.mod_lt n hv2_pos, ?_⟩
        have hdm : v 2 * qn + rn = n := Nat.div_add_mod n (v 2)
        have hdm_r : (v 2 : ℝ) * (qn : ℝ) + (rn : ℝ) = (n : ℝ) := by exact_mod_cast hdm
        have hn_r : (n : ℝ) = (N : ℝ) := by exact_mod_cast hn_eq
        push_cast; linarith
      · let m : ℕ := (-1 - N).toNat
        have hm_eq : (m : ℤ) = -1 - N := Int.toNat_of_nonneg (by omega)
        let r0 : ℕ := m % v 2
        let q0 : ℕ := m / v 2
        have hr0_lt : r0 < v 2 := Nat.mod_lt m hv2_pos
        let k : ℕ := v 2 - 1 - r0
        have hk_lt : k < v 2 := by dsimp [k]; omega
        refine ⟨k, -((q0 : ℤ) + 1), hk_lt, ?_⟩
        have hdm : v 2 * q0 + r0 = m := Nat.div_add_mod m (v 2)
        have hdm_r : (v 2 : ℝ) * (q0 : ℝ) + (r0 : ℝ) = (m : ℝ) := by exact_mod_cast hdm
        have hk_r : (k : ℝ) = (v 2 : ℝ) - 1 - (r0 : ℝ) := by
          have : k + r0 + 1 = v 2 := by dsimp [k]; omega
          have hr : (k : ℝ) + (r0 : ℝ) + 1 = (v 2 : ℝ) := by exact_mod_cast this
          linarith
        have hm_r : (m : ℝ) = -1 - (N : ℝ) := by exact_mod_cast hm_eq
        push_cast; linarith
    obtain ⟨k, qz, hk_lt, hNc⟩ := hex_div
    have hk_mem : k ∈ Finset.range (v 2) := Finset.mem_range.mpr hk_lt
    have ht_eq : t = g k + (qz : ℝ) := by
      have hf := Int.floor_add_fract (t * (v 2 : ℝ))
      rw [ht_fr] at hf
      have htv : t * (v 2 : ℝ) = (N : ℝ) + 5 / 6 := by dsimp [N]; linarith
      have hgk : (g k + (qz : ℝ)) * (v 2 : ℝ) = (N : ℝ) + 5 / 6 := by
        dsimp [g]; rw [hNc]; field_simp [ne_of_gt hv2_r]; ring
      exact mul_right_cancel₀ (ne_of_gt hv2_r) (htv.trans hgk.symm)
    have hobj_eq : obj t = obj (g k) := by
      dsimp [obj]
      have h0 : (g k + (qz : ℝ)) * (v 0 : ℝ) = g k * (v 0 : ℝ) + ((qz * (v 0 : ℤ) : ℤ) : ℝ) := by push_cast; ring
      have h1 : (g k + (qz : ℝ)) * (v 1 : ℝ) = g k * (v 1 : ℝ) + ((qz * (v 1 : ℤ) : ℤ) : ℝ) := by push_cast; ring
      rw [ht_eq, h0, h1, circDist_add_int, circDist_add_int]
    rw [hobj_eq]; exact hk_max k hk_mem
  have hmax_grid : ∀ s : ℝ,
      (Int.fract (s * (v 2 : ℝ)) = 1 / 6 ∨ Int.fract (s * (v 2 : ℝ)) = 1 / 2 ∨
        Int.fract (s * (v 2 : ℝ)) = 5 / 6) →
      obj s ≤ obj t_hat := by
    intro s hgrid
    obtain ⟨l, hl56⟩ := (shift_third_grid_sixth (hnot3 0) s hgrid).2
    let s' : ℝ := s + ((l.val : ℤ) : ℝ) / ((3 : ℕ) : ℝ)
    have hs'_eq : s' = s + (l.val : ℝ) / 3 := by dsimp [s']; push_cast; norm_num
    have hobj_s' : obj s' = obj s := by
      dsimp [obj]
      rw [circDist_shift_dvd (by omega) hdvd3_0, circDist_shift_dvd (by omega) hdvd3_1]
    rw [← hobj_s']; apply hmax_56 s'; rw [hs'_eq]; exact hl56
  have hobj_zero : obj t_hat = 0 := by
    rcases le_total (circDist (t_hat * (v 0 : ℝ))) (circDist (t_hat * (v 1 : ℝ))) with h01 | h10
    · have hz := prop_3_1_hsym (v 0) (v 1) (v 2) (v 3) (v 4) t_hat ht_hat_fr2
        (hnot3 0) (hnot3 1) (hnot3 2) hdvd3_0 hdvd3_1 hdvd6_or heven_cap
        (fun t ⟨h0, h1, h2, h3, h4⟩ => hno_D t fun i => by
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl <;> assumption)
        (fun s hgr => (hmax_grid s hgr).trans (min_eq_left h01).le) h01
      dsimp [obj]; rw [min_eq_left h01]; exact hz
    · have hz := prop_3_1_hsym (v 1) (v 0) (v 2) (v 3) (v 4) t_hat ht_hat_fr2
        (hnot3 0) (hnot3 1) (hnot3 2) hdvd3_1 hdvd3_0 hdvd6_or.symm
        (fun ⟨e1, e0, e2⟩ => heven_cap ⟨e0, e1, e2⟩)
        (fun t ⟨h1, h0, h2, h3, h4⟩ => hno_D t fun i => by
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl <;> assumption)
        (fun s hgr => by rw [min_comm]; exact (hmax_grid s hgr).trans (min_eq_right h10).le) h10
      dsimp [obj]; rw [min_eq_right h10]; exact hz
  let t_test : ℝ := -1 / (6 * (v 2 : ℝ))
  have ht_test_fr2 : Int.fract (t_test * (v 2 : ℝ)) = 5 / 6 := by
    have heq : t_test * (v 2 : ℝ) = (-1 / 6 : ℝ) := by dsimp [t_test]; field_simp [ne_of_gt hv2_r]
    rw [heq, fract_eq_sub_int _ (-1) (by push_cast; linarith) (by push_cast; linarith)]; push_cast; ring
  have hle_zero : obj t_test ≤ 0 := by rw [← hobj_zero]; exact hmax_56 t_test ht_test_fr2
  have hge_zero : 0 ≤ obj t_test := le_min (circDist_nonneg _) (circDist_nonneg _)
  have hmin0 : min (circDist (t_test * (v 0 : ℝ))) (circDist (t_test * (v 1 : ℝ))) = 0 :=
    le_antisymm hle_zero hge_zero
  have hdvd_of_zero : ∀ u : ℕ, circDist (t_test * (u : ℝ)) = 0 → 6 * v 2 ∣ u := by
    intro u hz
    have hpos_r : circDist ((u : ℝ) / (6 * (v 2 : ℝ))) = 0 := by
      have hn : (u : ℝ) / (6 * (v 2 : ℝ)) = -(t_test * (u : ℝ)) := by dsimp [t_test]; ring
      rw [hn, circDist_neg]; exact hz
    have hfr0 := (circDist_eq_zero_iff_fract _).mp hpos_r
    let kz : ℤ := ⌊(u : ℝ) / (6 * (v 2 : ℝ))⌋
    have hkz_nn : 0 ≤ kz := Int.floor_nonneg.mpr (by positivity)
    let kn : ℕ := kz.toNat
    have heq_r : (u : ℝ) / (6 * (v 2 : ℝ)) = (kn : ℝ) := by
      have hf := Int.floor_add_fract ((u : ℝ) / (6 * (v 2 : ℝ)))
      have hkc : (kn : ℝ) = (kz : ℝ) := by
        have : (kn : ℤ) = kz := Int.toNat_of_nonneg hkz_nn
        exact_mod_cast this
      rw [hfr0, add_zero] at hf; dsimp [kz] at hkc; linarith
    have hmul : ((u : ℕ) : ℝ) = ((6 * v 2 * kn : ℕ) : ℝ) := by
      have h1 := congrArg (fun z => (6 * (v 2 : ℝ)) * z) heq_r
      have h2 : (6 * (v 2 : ℝ)) * ((u : ℝ) / (6 * (v 2 : ℝ))) = (u : ℝ) := by field_simp [ne_of_gt hv2_r]
      push_cast; linarith
    exact ⟨kn, by exact_mod_cast hmul⟩
  rcases min_cases (circDist (t_test * (v 0 : ℝ))) (circDist (t_test * (v 1 : ℝ))) with ⟨hm, _⟩ | ⟨hm, _⟩
  · exact Or.inl (hdvd_of_zero (v 0) (by linarith))
  · exact Or.inr (hdvd_of_zero (v 1) (by linarith))

private lemma renault_prop_3_1
    (h_lrc4 : ∀ u : Fin 4 → ℕ, (∀ i, 0 < u i) → ∃ t : ℝ, ∀ i, circDist (t * (u i : ℝ)) ≥ 1 / ((4 + 1 : ℕ) : ℝ))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i)
    (hdvd6_0 : 6 ∣ v 0) (hdvd3_1 : 3 ∣ v 1)
    (hnot3 : ∀ r : Fin 3, ¬ 3 ∣ v r.succ.succ)
    (hno4even : ∀ (i₀ i₁ i₂ j : Fin 5), i₀ ≠ i₁ → i₀ ≠ i₂ → i₀ ≠ j → i₁ ≠ i₂ → i₁ ≠ j → i₂ ≠ j →
      2 ∣ v i₀ → 2 ∣ v i₁ → 2 ∣ v i₂ → ¬ 2 ∣ v j) :
    ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  by_contra hfail
  have h16 : (1 : ℝ) / ((5 + 1 : ℕ) : ℝ) = 1 / 6 := by norm_num
  have hno_D : ∀ t : ℝ, ¬ (∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / 6) := by
    intro t ht; exact hfail ⟨t, fun i => by rw [h16]; exact ht i⟩
  have hdvd3_0 : 3 ∣ v 0 := dvd_trans (by decide) hdvd6_0
  have hd2 : 6 * v 2 ∣ v 0 ∨ 6 * v 2 ∣ v 1 :=
    prop_3_1_div_single v hv_pos hdvd3_0 hdvd3_1 (Or.inl hdvd6_0) hnot3
      (fun ⟨e0, e1, e2⟩ => ⟨hno4even 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e2,
        hno4even 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e2⟩)
      hno_D
  let w3 : Fin 5 → ℕ := ![v 0, v 1, v 3, v 2, v 4]
  have hd3 : 6 * v 3 ∣ v 0 ∨ 6 * v 3 ∣ v 1 :=
    prop_3_1_div_single w3 (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_0 hdvd3_1 (Or.inl hdvd6_0)
      (fun r => by fin_cases r <;> [exact hnot3 1; exact hnot3 0; exact hnot3 2])
      (fun ⟨e0, e1, e3⟩ => ⟨hno4even 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e3,
        hno4even 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e3⟩)
      (fun t ht => hno_D t fun i => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl
        · exact ht 0
        · exact ht 1
        · exact ht 3
        · exact ht 2
        · exact ht 4)
  let w4 : Fin 5 → ℕ := ![v 0, v 1, v 4, v 2, v 3]
  have hd4 : 6 * v 4 ∣ v 0 ∨ 6 * v 4 ∣ v 1 :=
    prop_3_1_div_single w4 (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_0 hdvd3_1 (Or.inl hdvd6_0)
      (fun r => by fin_cases r <;> [exact hnot3 2; exact hnot3 0; exact hnot3 1])
      (fun ⟨e0, e1, e4⟩ => ⟨hno4even 0 1 4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e4,
        hno4even 0 1 4 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e0 e1 e4⟩)
      (fun t ht => hno_D t fun i => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by fin_cases i <;> simp) with rfl|rfl|rfl|rfl|rfl
        · exact ht 0
        · exact ht 1
        · exact ht 3
        · exact ht 4
        · exact ht 2)
  have hfinale : ∀ (u : Fin 5 → ℕ), (∀ i, 0 < u i) → 3 ∣ u 0 → 3 ∣ u 1 →
      (∀ r : Fin 3, ¬ 3 ∣ u r.succ.succ) →
      (∀ t : ℝ, ¬ (∀ i : Fin 5, circDist (t * (u i : ℝ)) ≥ 1 / 6)) →
      6 * u 3 ≤ u 0 → 6 * u 4 ≤ u 0 → (6 * u 2 ≤ u 0 ∨ 6 * u 2 ≤ u 1) → False := by
    intro u hu_pos hu0_3 hu1_3 hu_not3 hno_u hb_le hc_le ha_or
    have hno_u' : ¬ ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (u i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
      rintro ⟨t, ht⟩; exact hno_u t fun i => by rw [h16] at ht; exact ht i
    have hu0_lt_5u1 : u 0 < 5 * u 1 := by
      by_contra hge
      apply hno_u'
      refine renault_lemma_2_2 h_lrc4 u hu_pos 0 fun j hj => ?_
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by fin_cases j <;> simp) with rfl|rfl|rfl|rfl|rfl
      · exact absurd rfl hj
      · omega
      · rcases ha_or with h1 | h2 <;> omega
      · omega
      · omega
    have hu1_lt_5u0 : u 1 < 5 * u 0 := by
      by_contra hge
      apply hno_u'
      refine renault_lemma_2_2 h_lrc4 u hu_pos 1 fun j hj => ?_
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by fin_cases j <;> simp) with rfl|rfl|rfl|rfl|rfl
      · omega
      · exact absurd rfl hj
      · rcases ha_or with h1 | h2 <;> omega
      · omega
      · omega
    have hu0_r : (0 : ℝ) < (u 0 : ℝ) := Nat.cast_pos.mpr (hu_pos 0)
    let t_bar : ℝ := 1 / (6 * (u 0 : ℝ))
    have ht_bar_0 : circDist (t_bar * (u 0 : ℝ)) ≥ 1 / 6 := by
      have heq : t_bar * (u 0 : ℝ) = 1 / 6 := by dsimp [t_bar]; field_simp [ne_of_gt hu0_r]
      rw [heq]; exact circDist_ge_sixth_of_int _ 0 (by push_cast; norm_num) (by push_cast; norm_num)
    have hsmall_tbar : ∀ {w : ℕ}, 6 * w ≤ u 0 → circDist (t_bar * (w : ℝ)) ≤ 1 / 6 := by
      intro w hw
      have hwr : 6 * (w : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast hw
      have hub : t_bar * (w : ℝ) ≤ 1 / 36 := by
        dsimp [t_bar]; rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]; linarith
      have hnn : 0 ≤ t_bar * (w : ℝ) := by dsimp [t_bar]; positivity
      rw [circDist_eq_min_fract, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact le_trans (min_le_left _ _) (by linarith)
    have ht_bar_1_unsafe : circDist (t_bar * (u 1 : ℝ)) < 1 / 6 := by
      by_contra hge1
      obtain ⟨t', ht'⟩ := renault_arg1 u hu0_3 hu1_3 hu_not3 t_bar ht_bar_0 (le_of_not_gt hge1)
        1 2 (by decide) (hsmall_tbar hb_le) (hsmall_tbar hc_le)
      exact hno_u t' ht'
    have hu1_r1 : (u 0 : ℝ) < 5 * (u 1 : ℝ) := by exact_mod_cast hu0_lt_5u1
    have hu1_r2 : (u 1 : ℝ) < 5 * (u 0 : ℝ) := by exact_mod_cast hu1_lt_5u0
    have ht_bar_1_gt : 1 / 30 < t_bar * (u 1 : ℝ) := by
      dsimp [t_bar]; rw [one_div_mul_eq_div, lt_div_iff₀ (by positivity)]; linarith
    have ht_bar_1_lt56 : t_bar * (u 1 : ℝ) < 5 / 6 := by
      dsimp [t_bar]; rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity)]; linarith
    have ht_bar_1_lt16 : t_bar * (u 1 : ℝ) < 1 / 6 := by
      by_contra hge16
      have := circDist_ge_sixth_of_int (t_bar * (u 1 : ℝ)) 0 (by push_cast; linarith) (by push_cast; linarith)
      linarith
    let s : ℝ := 5 * t_bar
    have hs_0 : circDist (s * (u 0 : ℝ)) ≥ 1 / 6 := by
      have heq : s * (u 0 : ℝ) = 5 / 6 := by dsimp [s, t_bar]; field_simp [ne_of_gt hu0_r]
      rw [heq]; exact circDist_ge_sixth_of_int _ 0 (by push_cast; norm_num) (by push_cast; norm_num)
    have hs_1 : circDist (s * (u 1 : ℝ)) ≥ 1 / 6 := by
      have hlo : 1 / 6 < s * (u 1 : ℝ) := by dsimp [s]; linarith
      have hhi : s * (u 1 : ℝ) < 5 / 6 := by dsimp [s]; linarith
      exact circDist_ge_sixth_of_int _ 0 (by push_cast; linarith) (by push_cast; linarith)
    have hsmall_s : ∀ {w : ℕ}, 6 * w ≤ u 0 → circDist (s * (w : ℝ)) ≤ 1 / 6 := by
      intro w hw
      have hwr : 6 * (w : ℝ) ≤ (u 0 : ℝ) := by exact_mod_cast hw
      have hub : s * (w : ℝ) ≤ 5 / 36 := by
        dsimp [s, t_bar]
        have : (5 * (1 / (6 * (u 0 : ℝ)))) * (w : ℝ) = (5 * (w : ℝ)) / (6 * (u 0 : ℝ)) := by ring
        rw [this, div_le_iff₀ (by positivity)]; linarith
      have hnn : 0 ≤ s * (w : ℝ) := by dsimp [s, t_bar]; positivity
      rw [circDist_eq_min_fract, fract_eq_sub_int _ 0 (by push_cast; linarith) (by push_cast; linarith)]
      push_cast; exact le_trans (min_le_left _ _) (by linarith)
    obtain ⟨t', ht'⟩ := renault_arg1 u hu0_3 hu1_3 hu_not3 s hs_0 hs_1
      1 2 (by decide) (hsmall_s hb_le) (hsmall_s hc_le)
    exact hno_u t' ht'
  have hl2 : 6 * v 2 ≤ v 0 ∨ 6 * v 2 ≤ v 1 :=
    hd2.imp (Nat.le_of_dvd (hv_pos 0)) (Nat.le_of_dvd (hv_pos 1))
  have hl3 : 6 * v 3 ≤ v 0 ∨ 6 * v 3 ≤ v 1 :=
    hd3.imp (Nat.le_of_dvd (hv_pos 0)) (Nat.le_of_dvd (hv_pos 1))
  have hl4 : 6 * v 4 ≤ v 0 ∨ 6 * v 4 ≤ v 1 :=
    hd4.imp (Nat.le_of_dvd (hv_pos 0)) (Nat.le_of_dvd (hv_pos 1))
  have hnot3' : ∀ r : Fin 3, ¬ 3 ∣ (![v 1, v 0, v 2, v 3, v 4] : Fin 5 → ℕ) r.succ.succ := by
    intro r; fin_cases r <;> [exact hnot3 0; exact hnot3 1; exact hnot3 2]
  rcases hl2 with c2 | c2 <;> rcases hl3 with c3 | c3 <;> rcases hl4 with c4 | c4
  · exact hfinale v hv_pos hdvd3_0 hdvd3_1 hnot3 hno_D c3 c4 (Or.inl c2)
  · exact hfinale ![v 0, v 1, v 4, v 2, v 3] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_0 hdvd3_1
      (fun r => by fin_cases r <;> [exact hnot3 2; exact hnot3 0; exact hnot3 1])
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 0; exact ht 1; exact ht 3; exact ht 4; exact ht 2])
      c2 c3 (Or.inr c4)
  · exact hfinale ![v 0, v 1, v 3, v 2, v 4] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_0 hdvd3_1
      (fun r => by fin_cases r <;> [exact hnot3 1; exact hnot3 0; exact hnot3 2])
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 0; exact ht 1; exact ht 3; exact ht 2; exact ht 4])
      c2 c4 (Or.inr c3)
  · exact hfinale ![v 1, v 0, v 2, v 3, v 4] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_1 hdvd3_0 hnot3'
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 1; exact ht 0; exact ht 2; exact ht 3; exact ht 4])
      c3 c4 (Or.inr c2)
  · exact hfinale v hv_pos hdvd3_0 hdvd3_1 hnot3 hno_D c3 c4 (Or.inr c2)
  · exact hfinale ![v 1, v 0, v 3, v 2, v 4] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_1 hdvd3_0
      (fun r => by fin_cases r <;> [exact hnot3 1; exact hnot3 0; exact hnot3 2])
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 1; exact ht 0; exact ht 3; exact ht 2; exact ht 4])
      c2 c4 (Or.inr c3)
  · exact hfinale ![v 1, v 0, v 4, v 2, v 3] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_1 hdvd3_0
      (fun r => by fin_cases r <;> [exact hnot3 2; exact hnot3 0; exact hnot3 1])
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 1; exact ht 0; exact ht 3; exact ht 4; exact ht 2])
      c2 c3 (Or.inr c4)
  · exact hfinale ![v 1, v 0, v 2, v 3, v 4] (fun i => by fin_cases i <;> exact hv_pos _) hdvd3_1 hdvd3_0 hnot3'
      (fun t ht => hno_D t fun i => by fin_cases i <;> [exact ht 1; exact ht 0; exact ht 2; exact ht 3; exact ht 4])
      c3 c4 (Or.inl c2)

/- ### Master Dispatcher `lrc_nat_five`: Arbitrary 5 Positive Integer Speeds -/

private lemma fin5_compl_four :
    ∀ (a b c d : Fin 5), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ e : Fin 5, ∀ k : Fin 5, k = a ∨ k = b ∨ k = c ∨ k = d ∨ k = e := by
  decide

private lemma fin5_compl_three :
    ∀ (a b c : Fin 5), a ≠ b → a ≠ c → b ≠ c →
      ∃ d e : Fin 5, ∀ k : Fin 5, k = a ∨ k = b ∨ k = c ∨ k = d ∨ k = e := by
  decide

lemma lrc_nat_five
    (h_lrc4 : ∀ u : Fin 4 → ℕ, (∀ i, 0 < u i) → ∃ t : ℝ, ∀ i, circDist (t * (u i : ℝ)) ≥ 1 / ((4 + 1 : ℕ) : ℝ))
    (h_claim24 : ∀ x : ℝ, 1 / 6 < x → x < 5 / 6 →
      ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
        (Int.fract ((lam : ℝ) * x) < 1 / 6 ∨ 5 / 6 < Int.fract ((lam : ℝ) * x)))
    (h_prop54 : ∀ v : Fin 5 → ℕ, (∀ i, 0 < v i) → 6 ∣ v 0 →
      (∀ j : Fin 4, ¬ 2 ∣ v j.succ) → (∀ j : Fin 4, ¬ 3 ∣ v j.succ) →
      ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ))
    (h_prop66 : ∀ v : Fin 5 → ℕ, (∀ i, 0 < v i) → 6 ∣ v 0 → 2 ∣ v 1 →
      (∀ r : Fin 3, ¬ 2 ∣ v r.succ.succ) → (∀ j : Fin 4, ¬ 3 ∣ v j.succ) →
      ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ))
    (v : Fin 5 → ℕ) (hv_pos : ∀ i, 0 < v i) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
  have h16 : (1 : ℝ) / ((5 + 1 : ℕ) : ℝ) = 1 / 6 := by norm_num
  have h15 : (1 : ℝ) / ((4 + 1 : ℕ) : ℝ) = 1 / 5 := by norm_num
  suffices hreal : ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (v i : ℝ)) ≥ 1 / 6 by
    obtain ⟨t, ht⟩ := hreal
    refine ⟨Int.fract t, Int.fract_nonneg t, fun i => ?_⟩
    rw [h16]
    have hexp : Int.fract t * (v i : ℝ) = t * (v i : ℝ) - ((⌊t⌋ * (v i : ℤ) : ℤ) : ℝ) := by
      conv_lhs => rw [fract_eq_sub_floor]
      push_cast; ring
    rw [hexp, circDist_sub_int]; exact ht i
  let g : ℕ := Finset.univ.gcd v
  have hg_pos : 0 < g := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    have hd : g ∣ v 0 := Finset.gcd_dvd (Finset.mem_univ (0 : Fin 5))
    rw [hz] at hd
    exact absurd (Nat.eq_zero_of_zero_dvd hd) (ne_of_gt (hv_pos 0))
  let u : Fin 5 → ℕ := fun i => v i / g
  have hgu : ∀ i, g * u i = v i := fun i => Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))
  have hu_pos : ∀ i, 0 < u i := fun i => by
    by_contra hz; simp only [not_lt, Nat.le_zero] at hz
    have := hgu i; rw [hz, mul_zero] at this; exact absurd this.symm (ne_of_gt (hv_pos i))
  have hu_gcd : Finset.univ.gcd u = 1 := by
    let d : ℕ := Finset.univ.gcd u
    have hd_pos : 0 < d := by
      refine Nat.pos_of_ne_zero fun hz => ?_
      have hd0 : d ∣ u 0 := Finset.gcd_dvd (Finset.mem_univ (0 : Fin 5))
      rw [hz] at hd0
      exact absurd (Nat.eq_zero_of_zero_dvd hd0) (ne_of_gt (hu_pos 0))
    have hgd_dvd : g * d ∣ g := by
      refine Finset.dvd_gcd fun i _ => ?_
      rw [← hgu i]; exact mul_dvd_mul_left g (Finset.gcd_dvd (Finset.mem_univ i))
    have hle : g * d ≤ g := Nat.le_of_dvd hg_pos hgd_dvd
    nlinarith
  suffices hu_ok : ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (u i : ℝ)) ≥ 1 / 6 by
    obtain ⟨t, ht⟩ := hu_ok
    have hg_r : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hg_pos)
    refine ⟨t / (g : ℝ), fun i => ?_⟩
    have heq : (t / (g : ℝ)) * (v i : ℝ) = t * (u i : ℝ) := by
      have hvc : (v i : ℝ) = (g : ℝ) * (u i : ℝ) := by exact_mod_cast (hgu i).symm
      rw [hvc]; field_simp [hg_r]
    rw [heq]; exact ht i
  by_contra hfail
  have hno_u : ∀ t : ℝ, ¬ (∀ i : Fin 5, circDist (t * (u i : ℝ)) ≥ 1 / 6) :=
    fun t ht => hfail ⟨t, ht⟩
  -- Step 1: ∃ i₀, 6 ∣ u i₀!
  have hex_6 : ∃ i₀ : Fin 5, 6 ∣ u i₀ := by
    by_contra hnone6
    apply hno_u (1 / 6)
    intro i
    have hnd6 : ¬ 6 ∣ u i := fun h => hnone6 ⟨i, h⟩
    have hrem : 1 ≤ u i % 6 ∧ u i % 6 ≤ 5 := by omega
    have hdiv : 6 * (u i / 6) + u i % 6 = u i := Nat.div_add_mod (u i) 6
    let qi : ℕ := u i / 6
    have hexp : (1 / 6 : ℝ) * (u i : ℝ) = ((u i % 6 : ℕ) : ℝ) / 6 + ((qi : ℤ) : ℝ) := by
      have huc : (u i : ℝ) = 6 * (qi : ℝ) + ((u i % 6 : ℕ) : ℝ) := by dsimp [qi]; exact_mod_cast hdiv.symm
      rw [huc]; push_cast; ring
    rw [hexp, circDist_add_int]
    have h1r : (1 : ℝ) ≤ ((u i % 6 : ℕ) : ℝ) := by exact_mod_cast hrem.1
    have h5r : ((u i % 6 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hrem.2
    exact circDist_ge_sixth_of_int _ 0 (by push_cast; linarith) (by push_cast; linarith)
  -- Step 2: No 4 distinct indices have 2 ∣ u!
  have hno4even_u : ∀ (a b c d : Fin 5), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      2 ∣ u a → 2 ∣ u b → 2 ∣ u c → ¬ 2 ∣ u d := by
    intro a b c d nab nac nad nbc nbd ncd ha hb hc hd
    obtain ⟨e, hcov⟩ := fin5_compl_four a b c d nab nac nad nbc nbd ncd
    by_cases he : 2 ∣ u e
    · have h2g : 2 ∣ Finset.univ.gcd u := Finset.dvd_gcd fun k _ => by
        rcases hcov k with rfl | rfl | rfl | rfl | rfl <;> assumption
      rw [hu_gcd] at h2g; omega
    · obtain ⟨t₀, ht₀⟩ := h_lrc4 ![u a, u b, u c, u d] (fun j => by fin_cases j <;> exact hu_pos _)
      rw [h15] at ht₀
      rcases odd_half_not_both_unsafe he t₀ with g0 | g_half
      · apply hno_u t₀; intro k
        rcases hcov k with rfl | rfl | rfl | rfl | rfl
        · exact le_trans (by norm_num) (ht₀ 0)
        · exact le_trans (by norm_num) (ht₀ 1)
        · exact le_trans (by norm_num) (ht₀ 2)
        · exact le_trans (by norm_num) (ht₀ 3)
        · exact g0
      · apply hno_u (t₀ + 1 / 2); intro k
        rcases hcov k with rfl | rfl | rfl | rfl | rfl
        · rw [circDist_even_add_half ha]; exact le_trans (by norm_num) (ht₀ 0)
        · rw [circDist_even_add_half hb]; exact le_trans (by norm_num) (ht₀ 1)
        · rw [circDist_even_add_half hc]; exact le_trans (by norm_num) (ht₀ 2)
        · rw [circDist_even_add_half hd]; exact le_trans (by norm_num) (ht₀ 3)
        · exact g_half
  -- Step 3: No 3 distinct indices have 3 ∣ u (Renault Lemma 2.3)!
  have hno3mult3_u : ∀ (a b c : Fin 5), a ≠ b → a ≠ c → b ≠ c →
      3 ∣ u a → 3 ∣ u b → ¬ 3 ∣ u c := by
    intro a b c nab nac nbc ha hb hc
    obtain ⟨d, e, hcov⟩ := fin5_compl_three a b c nab nac nbc
    by_cases hd : 3 ∣ u d
    · by_cases he : 3 ∣ u e
      · have h3g : 3 ∣ Finset.univ.gcd u := Finset.dvd_gcd fun k _ => by
          rcases hcov k with rfl | rfl | rfl | rfl | rfl <;> assumption
        rw [hu_gcd] at h3g; omega
      · obtain ⟨t₀, ht₀⟩ := h_lrc4 ![u a, u b, u c, u d] (fun j => by fin_cases j <;> exact hu_pos _)
        rw [h15] at ht₀
        rcases shift_third_not_both_unsafe he t₀ (l₁ := 0) (l₂ := 1) (by decide) with g0 | g1
        · apply hno_u t₀; intro k
          rcases hcov k with rfl | rfl | rfl | rfl | rfl
          · exact le_trans (by norm_num) (ht₀ 0)
          · exact le_trans (by norm_num) (ht₀ 1)
          · exact le_trans (by norm_num) (ht₀ 2)
          · exact le_trans (by norm_num) (ht₀ 3)
          · simpa using g0
        · apply hno_u (t₀ + ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)); intro k
          rcases hcov k with rfl | rfl | rfl | rfl | rfl
          · rw [circDist_shift_dvd (by omega) ha]; exact le_trans (by norm_num) (ht₀ 0)
          · rw [circDist_shift_dvd (by omega) hb]; exact le_trans (by norm_num) (ht₀ 1)
          · rw [circDist_shift_dvd (by omega) hc]; exact le_trans (by norm_num) (ht₀ 2)
          · rw [circDist_shift_dvd (by omega) hd]; exact le_trans (by norm_num) (ht₀ 3)
          · simpa using g1
    · by_cases he : 3 ∣ u e
      · obtain ⟨t₀, ht₀⟩ := h_lrc4 ![u a, u b, u c, u e] (fun j => by fin_cases j <;> exact hu_pos _)
        rw [h15] at ht₀
        rcases shift_third_not_both_unsafe hd t₀ (l₁ := 0) (l₂ := 1) (by decide) with g0 | g1
        · apply hno_u t₀; intro k
          rcases hcov k with rfl | rfl | rfl | rfl | rfl
          · exact le_trans (by norm_num) (ht₀ 0)
          · exact le_trans (by norm_num) (ht₀ 1)
          · exact le_trans (by norm_num) (ht₀ 2)
          · simpa using g0
          · exact le_trans (by norm_num) (ht₀ 3)
        · apply hno_u (t₀ + ((1 : ℤ) : ℝ) / ((3 : ℕ) : ℝ)); intro k
          rcases hcov k with rfl | rfl | rfl | rfl | rfl
          · rw [circDist_shift_dvd (by omega) ha]; exact le_trans (by norm_num) (ht₀ 0)
          · rw [circDist_shift_dvd (by omega) hb]; exact le_trans (by norm_num) (ht₀ 1)
          · rw [circDist_shift_dvd (by omega) hc]; exact le_trans (by norm_num) (ht₀ 2)
          · simpa using g1
          · rw [circDist_shift_dvd (by omega) he]; exact le_trans (by norm_num) (ht₀ 3)
      · obtain ⟨t₀, ht₀⟩ := h_lrc4 ![u a, u b, u c, u a] (fun j => by fin_cases j <;> exact hu_pos _)
        rw [h15] at ht₀
        obtain ⟨l, hld, hle⟩ := two_not3_common_third hd he t₀
        apply hno_u (t₀ + ((l.val : ℤ) : ℝ) / ((3 : ℕ) : ℝ)); intro k
        rcases hcov k with rfl | rfl | rfl | rfl | rfl
        · rw [circDist_shift_dvd (by omega) ha]; exact le_trans (by norm_num) (ht₀ 0)
        · rw [circDist_shift_dvd (by omega) hb]; exact le_trans (by norm_num) (ht₀ 1)
        · rw [circDist_shift_dvd (by omega) hc]; exact le_trans (by norm_num) (ht₀ 2)
        · simpa using hld
        · simpa using hle
  -- Step 4: Permute the multiple of 6 to index 0, then dispatch!
  obtain ⟨i₆, hi₆⟩ := hex_6
  let σ₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 i₆
  let w : Fin 5 → ℕ := fun i => u (σ₀ i)
  have hw_pos : ∀ i, 0 < w i := fun i => hu_pos _
  have hw_6 : 6 ∣ w 0 := by dsimp [w, σ₀]; rw [Equiv.swap_apply_left]; exact hi₆
  have hw_no4even : ∀ (a b c d : Fin 5), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      2 ∣ w a → 2 ∣ w b → 2 ∣ w c → ¬ 2 ∣ w d :=
    fun a b c d nab nac nad nbc nbd ncd =>
      hno4even_u _ _ _ _ (σ₀.injective.ne nab) (σ₀.injective.ne nac) (σ₀.injective.ne nad)
        (σ₀.injective.ne nbc) (σ₀.injective.ne nbd) (σ₀.injective.ne ncd)
  have hw_no3mult3 : ∀ (a b c : Fin 5), a ≠ b → a ≠ c → b ≠ c →
      3 ∣ w a → 3 ∣ w b → ¬ 3 ∣ w c :=
    fun a b c nab nac nbc =>
      hno3mult3_u _ _ _ (σ₀.injective.ne nab) (σ₀.injective.ne nac) (σ₀.injective.ne nbc)
  have hno_w : ¬ ∃ t : ℝ, ∀ i : Fin 5, circDist (t * (w i : ℝ)) ≥ 1 / ((5 + 1 : ℕ) : ℝ) := by
    rintro ⟨t, ht⟩; apply hno_u t; intro i
    have := ht (σ₀.symm i); rw [h16] at this; simpa [w] using this
  by_cases hex3_rest : ∃ j₁ : Fin 4, 3 ∣ w j₁.succ
  · -- Two multiples of 3 -> Proposition 3.1!
    obtain ⟨j₁, hj₁⟩ := hex3_rest
    let τ : Equiv.Perm (Fin 5) := Equiv.swap 1 j₁.succ
    let w' : Fin 5 → ℕ := fun i => w (τ i)
    have hw'0_6 : 6 ∣ w' 0 := by
      dsimp [w', τ]; rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Fin.succ_ne_zero j₁).symm]; exact hw_6
    have hw'1_3 : 3 ∣ w' 1 := by dsimp [w', τ]; rw [Equiv.swap_apply_left]; exact hj₁
    have hw'_no4even : ∀ (a b c d : Fin 5), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        2 ∣ w' a → 2 ∣ w' b → 2 ∣ w' c → ¬ 2 ∣ w' d :=
      fun a b c d nab nac nad nbc nbd ncd =>
        hw_no4even _ _ _ _ (τ.injective.ne nab) (τ.injective.ne nac) (τ.injective.ne nad)
          (τ.injective.ne nbc) (τ.injective.ne nbd) (τ.injective.ne ncd)
    have hw'_not3 : ∀ r : Fin 3, ¬ 3 ∣ w' r.succ.succ := fun r =>
      hw_no3mult3 (τ 0) (τ 1) (τ r.succ.succ)
        (τ.injective.ne (by decide))
        (τ.injective.ne (by fin_cases r <;> decide))
        (τ.injective.ne (by fin_cases r <;> decide))
        (dvd_trans (by decide) hw'0_6) hw'1_3
    obtain ⟨t, ht⟩ := renault_prop_3_1 h_lrc4 w' (fun i => hw_pos _) hw'0_6 hw'1_3 hw'_not3 hw'_no4even
    exact hno_w ⟨t, fun i => by simpa [w'] using ht (τ.symm i)⟩
  · -- Unique multiple of 3 -> count even speeds among w 1..4!
    have hw_not3 : ∀ j : Fin 4, ¬ 3 ∣ w j.succ := fun j hj => hex3_rest ⟨j, hj⟩
    by_cases hex2_1 : ∃ j₁ : Fin 4, 2 ∣ w j₁.succ
    · obtain ⟨j₁, hj₁⟩ := hex2_1
      let τ₁ : Equiv.Perm (Fin 5) := Equiv.swap 1 j₁.succ
      let w₁ : Fin 5 → ℕ := fun i => w (τ₁ i)
      have hw₁0_6 : 6 ∣ w₁ 0 := by
        dsimp [w₁, τ₁]; rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Fin.succ_ne_zero j₁).symm]; exact hw_6
      have hw₁1_2 : 2 ∣ w₁ 1 := by dsimp [w₁, τ₁]; rw [Equiv.swap_apply_left]; exact hj₁
      have hw₁_not3 : ∀ j : Fin 4, ¬ 3 ∣ w₁ j.succ := by
        intro j
        have hne0 : τ₁ j.succ ≠ 0 := fun h =>
          Fin.succ_ne_zero j (τ₁.injective (h.trans (Equiv.swap_apply_of_ne_of_ne (by decide) (Fin.succ_ne_zero j₁).symm).symm))
        obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hne0
        dsimp [w₁]; rw [hk]; exact hw_not3 k
      have hw₁_no4even : ∀ (a b c d : Fin 5), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          2 ∣ w₁ a → 2 ∣ w₁ b → 2 ∣ w₁ c → ¬ 2 ∣ w₁ d :=
        fun a b c d nab nac nad nbc nbd ncd =>
          hw_no4even _ _ _ _ (τ₁.injective.ne nab) (τ₁.injective.ne nac) (τ₁.injective.ne nad)
            (τ₁.injective.ne nbc) (τ₁.injective.ne nbd) (τ₁.injective.ne ncd)
      by_cases hex2_2 : ∃ r₁ : Fin 3, 2 ∣ w₁ r₁.succ.succ
      · -- Three even speeds -> Proposition 4.1!
        obtain ⟨r₁, hr₁⟩ := hex2_2
        let τ₂ : Equiv.Perm (Fin 5) := Equiv.swap 2 r₁.succ.succ
        let w₂ : Fin 5 → ℕ := fun i => w₁ (τ₂ i)
        have h2_ne0 : (2 : Fin 5) ≠ 0 := by decide
        have h2_ne1 : (2 : Fin 5) ≠ 1 := by decide
        have hr_ne0 : r₁.succ.succ ≠ 0 := by fin_cases r₁ <;> decide
        have hr_ne1 : r₁.succ.succ ≠ 1 := by fin_cases r₁ <;> decide
        have hw₂0_6 : 6 ∣ w₂ 0 := by
          dsimp [w₂, τ₂]; rw [Equiv.swap_apply_of_ne_of_ne h2_ne0.symm hr_ne0.symm]; exact hw₁0_6
        have hw₂1_2 : 2 ∣ w₂ 1 := by
          dsimp [w₂, τ₂]; rw [Equiv.swap_apply_of_ne_of_ne h2_ne1.symm hr_ne1.symm]; exact hw₁1_2
        have hw₂2_2 : 2 ∣ w₂ 2 := by dsimp [w₂, τ₂]; rw [Equiv.swap_apply_left]; exact hr₁
        have hw₂_not3 : ∀ j : Fin 4, ¬ 3 ∣ w₂ j.succ := by
          intro j
          have hne0 : τ₂ j.succ ≠ 0 := fun h =>
            Fin.succ_ne_zero j (τ₂.injective (h.trans (Equiv.swap_apply_of_ne_of_ne h2_ne0.symm hr_ne0.symm).symm))
          obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hne0
          dsimp [w₂]; rw [hk]; exact hw₁_not3 k
        have hw₂_odd : ∀ (idx : Fin 5), idx ≠ 0 → idx ≠ 1 → idx ≠ 2 → ¬ 2 ∣ w₂ idx := fun idx n0 n1 n2 =>
          hw₁_no4even (τ₂ 0) (τ₂ 1) (τ₂ 2) (τ₂ idx)
            (τ₂.injective.ne (by decide)) (τ₂.injective.ne (by decide)) (τ₂.injective.ne n0.symm)
            (τ₂.injective.ne (by decide)) (τ₂.injective.ne n1.symm) (τ₂.injective.ne n2.symm)
            (dvd_trans (by decide) hw₂0_6) hw₂1_2 hw₂2_2
        obtain ⟨t, ht⟩ := renault_prop_4_1 h_claim24 w₂ (fun i => hw_pos _) hw₂0_6 hw₂1_2 hw₂2_2
          (hw₂_odd 3 (by decide) (by decide) (by decide))
          (hw₂_odd 4 (by decide) (by decide) (by decide))
          hw₂_not3
        exact hno_w ⟨t, fun i => by simpa [w₂, w₁] using ht (τ₂.symm (τ₁.symm i))⟩
      · -- Exactly two even speeds -> Proposition 6.6!
        have hw₁_odd : ∀ r : Fin 3, ¬ 2 ∣ w₁ r.succ.succ := fun r hr => hex2_2 ⟨r, hr⟩
        obtain ⟨t, ht⟩ := h_prop66 w₁ (fun i => hw_pos _) hw₁0_6 hw₁1_2 hw₁_odd hw₁_not3
        exact hno_w ⟨t, fun i => by simpa [w₁] using ht (τ₁.symm i)⟩
    · -- Unique even speed -> Proposition 5.4!
      have hw_odd : ∀ j : Fin 4, ¬ 2 ∣ w j.succ := fun j hj => hex2_1 ⟨j, hj⟩
      exact hno_w (h_prop54 w hw_pos hw_6 hw_odd hw_not3)


end
end RenaultSec34


namespace RenaultCompleteFive
noncomputable section

lemma claim_2_4_or {x : ℝ} (hx1 : 1 / 6 < x) (hx2 : x < 5 / 6) :
    ∃ lam : ℕ, 2 ≤ lam ∧ lam ≤ 5 ∧
      (Int.fract ((lam : ℝ) * x) < 1 / 6 ∨ 5 / 6 < Int.fract ((lam : ℝ) * x)) := by
  obtain ⟨lam, hl2, hl5, hnot⟩ := RenaultPart2.renault_claim_2_4 hx1 hx2
  refine ⟨lam, hl2, hl5, ?_⟩
  rcases lt_or_ge (Int.fract ((lam : ℝ) * x)) (1 / 6) with hlo | hge
  · exact Or.inl hlo
  · exact Or.inr (lt_of_not_ge fun hle => hnot ⟨hge, hle⟩)

theorem lrc_five_all (v : Fin 5 → ℕ) (hv_pos : ∀ i : Fin 5, 0 < v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 5, dist ((t * (v i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((5 + 1 : ℕ) : ℝ) :=
  RenaultSec34.lrc_nat_five
    LRCBaseFour.lrc_nat_four_any
    (fun _ hx1 hx2 => claim_2_4_or hx1 hx2)
    (RenaultSec56.renault_prop_5_4 LRCBaseFour.lrc_nat_four_any RenaultPart2.renault_lemma_5_1)
    (RenaultSec56.renault_prop_6_6 LRCBaseFour.lrc_nat_four_any RenaultLem61.renault_lemma_6_1 RenaultPart3.renault_lemma_6_4)
    v hv_pos

end
end RenaultCompleteFive

theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R1.H1 := by
  intro w hw_pos _ _ _ _ _ _ _
  exact RenaultCompleteFive.lrc_five_all w hw_pos

