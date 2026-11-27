import FormalConjectures.ErdosProblems.«942»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Real.Irrational

/-!
# Proof of Erdős Problem 942 (density variant)

For each $n \in \mathbb{N}$, `erdos_942.h n` counts the number of powerful integers in
$[n^2, (n+1)^2)$. We prove that for every $l \in \mathbb{N}$, the set $\{n \mid h(n) = l\}$
has a natural density $\delta(l)$, and $\sum_{l=0}^{\infty} \delta(l) = 1$.
-/

open Nat Filter Topology Finset

namespace Erdos942DensityProof

/- ### Section 1: Powerful numbers as `a ^ 2 * b ^ 3` and tail bound -/

private lemma exists_sq_mul_squarefree :
    ∀ m : ℕ, 1 ≤ m → ∃ x b : ℕ, 1 ≤ x ∧ Squarefree b ∧ m = x ^ 2 * b := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hsq : Squarefree m
    · exact ⟨1, m, le_rfl, hsq, by ring⟩
    · rw [Squarefree] at hsq
      push Not at hsq
      obtain ⟨d, hd_dvd, hd_nu⟩ := hsq
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0, mul_zero, zero_dvd_iff] at hd_dvd
        omega
      have hd1 : d ≠ 1 := by
        intro h1
        exact hd_nu (h1 ▸ isUnit_one)
      have hd2 : 2 ≤ d := by omega
      obtain ⟨m', hm'⟩ := hd_dvd
      have hm'_pos : 1 ≤ m' := by
        rcases Nat.eq_zero_or_pos m' with rfl | h
        · simp at hm'; omega
        · omega
      have hm'_lt : m' < m := by
        have : 4 ≤ d * d := by nlinarith
        nlinarith
      obtain ⟨x', b, hx', hb, hmb⟩ := ih m' hm'_lt hm'_pos
      refine ⟨d * x', b, by nlinarith, hb, ?_⟩
      calc m = d * d * m' := hm'
        _ = d * d * (x' ^ 2 * b) := by rw [hmb]
        _ = (d * x') ^ 2 * b := by ring

private lemma powerful_iff_sq_mul_cube {m : ℕ} (hm : 1 ≤ m) :
    m.Powerful ↔ ∃ a b : ℕ, 1 ≤ a ∧ Squarefree b ∧ m = a ^ 2 * b ^ 3 := by
  constructor
  · intro hpow
    obtain ⟨x, b, hx, hb, rfl⟩ := exists_sq_mul_squarefree m hm
    have hb0 : b ≠ 0 := hb.ne_zero
    have hx0 : x ≠ 0 := by omega
    have hm0 : x ^ 2 * b ≠ 0 := by positivity
    have hbx : b ∣ x := by
      rw [← Nat.factorization_le_iff_dvd hb0 hx0]
      intro p
      by_cases hbp : b.factorization p = 0
      · simp [hbp]
      · have hp_mem_b : p ∈ b.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors
            (Finsupp.mem_support_iff.mpr hbp), Nat.dvd_of_factorization_pos hbp, hb0⟩
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem_b
        have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp_mem_b
        have hbp_le : b.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hb0).mp hb p
        have hp_mem_m : p ∈ (x ^ 2 * b).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_right hpb _, hm0⟩
        have hp2_dvd : p ^ 2 ∣ x ^ 2 * b := hpow p hp_mem_m
        have h2_le : 2 ≤ (x ^ 2 * b).factorization p :=
          (hp.pow_dvd_iff_le_factorization hm0).mp hp2_dvd
        rw [Nat.factorization_mul (by positivity) hb0, Finsupp.add_apply,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h2_le
        omega
    obtain ⟨a, rfl⟩ := hbx
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at hx
      · omega
    exact ⟨a, b, ha, hb, by ring⟩
  · rintro ⟨a, b, _, _, rfl⟩ p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ a ^ 2 * b ^ 3 := Nat.dvd_of_mem_primeFactors hp
    rcases hp_prime.dvd_mul.mp hp_dvd with hpa | hpb
    · have hpa' : p ∣ a := hp_prime.dvd_of_dvd_pow hpa
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpa' 2) _
    · have hpb' : p ∣ b := hp_prime.dvd_of_dvd_pow hpb
      have hpb2 : p ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd hpb' 2
      have hb23 : b ^ 2 ∣ b ^ 3 := ⟨b, by ring⟩
      exact dvd_mul_of_dvd_right (dvd_trans hpb2 hb23) _

private lemma sq_mul_cube_unique {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : 1 ≤ a₁) (hb₁ : Squarefree b₁) (ha₂ : 1 ≤ a₂) (hb₂ : Squarefree b₂)
    (heq : a₁ ^ 2 * b₁ ^ 3 = a₂ ^ 2 * b₂ ^ 3) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hb₁0 : b₁ ≠ 0 := hb₁.ne_zero
  have hb₂0 : b₂ ≠ 0 := hb₂.ne_zero
  have ha₁0 : a₁ ≠ 0 := by omega
  have ha₂0 : a₂ ≠ 0 := by omega
  have hb_eq : b₁ = b₂ := by
    apply Nat.eq_of_factorization_eq hb₁0 hb₂0
    intro p
    have hfp := congrArg (fun n => n.factorization p) heq
    simp only [Nat.factorization_mul (by positivity : a₁ ^ 2 ≠ 0) (by positivity : b₁ ^ 3 ≠ 0),
      Nat.factorization_mul (by positivity : a₂ ^ 2 ≠ 0) (by positivity : b₂ ^ 3 ≠ 0),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hfp
    have h1 : b₁.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hb₁0).mp hb₁ p
    have h2 : b₂.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hb₂0).mp hb₂ p
    omega
  subst hb_eq
  have hb3_pos : 0 < b₁ ^ 3 := by positivity
  have ha_sq : a₁ ^ 2 = a₂ ^ 2 := Nat.eq_of_mul_eq_mul_right hb3_pos heq
  have ha_eq : a₁ = a₂ := by nlinarith
  exact ⟨ha_eq, rfl⟩

/-- `E b n` holds iff there exists `a ≥ 1` with `a ^ 2 * b ^ 3 ∈ [n ^ 2, (n + 1) ^ 2)`. -/
private abbrev E (b n : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ n ^ 2 ≤ a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n + 1) ^ 2

private lemma E_unique_a {b n a₁ a₂ : ℕ} (hb : 1 ≤ b)
    (h₁ : n ^ 2 ≤ a₁ ^ 2 * b ^ 3 ∧ a₁ ^ 2 * b ^ 3 < (n + 1) ^ 2)
    (h₂ : n ^ 2 ≤ a₂ ^ 2 * b ^ 3 ∧ a₂ ^ 2 * b ^ 3 < (n + 1) ^ 2) : a₁ = a₂ := by
  by_contra hne
  wlog hlt : a₁ < a₂ generalizing a₁ a₂
  · exact this h₂ h₁ (Ne.symm hne) (by omega)
  have h1 : a₁ + 1 ≤ a₂ := hlt
  have hb3 : 1 ≤ b ^ 3 := Nat.one_le_pow 3 b hb
  have hsq : n ^ 2 ≤ (a₁ * b ^ 3) ^ 2 := by
    calc n ^ 2 ≤ a₁ ^ 2 * b ^ 3 := h₁.1
      _ ≤ a₁ ^ 2 * (b ^ 3 * b ^ 3) := by nlinarith
      _ = (a₁ * b ^ 3) ^ 2 := by ring
  have hn_le : n ≤ a₁ * b ^ 3 := le_of_pow_le_pow_left₀ two_ne_zero (Nat.zero_le _) hsq
  have hstep : (n + 1) ^ 2 ≤ (a₁ + 1) ^ 2 * b ^ 3 := by nlinarith
  have hstep2 : (a₁ + 1) ^ 2 * b ^ 3 ≤ a₂ ^ 2 * b ^ 3 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 2)
  omega

private lemma h_zero : Erdos942.erdos_942.h 0 = 1 := by
  unfold Erdos942.erdos_942.h
  have hIco : Finset.Ico (0 ^ 2) ((0 + 1) ^ 2) = {0} := by decide
  rw [hIco, Finset.filter_singleton, if_pos (Nat.Full.zero_right 2)]
  simp

private lemma b_le_sq_mul_cube {a b : ℕ} (ha : 1 ≤ a) : b ≤ a ^ 2 * b ^ 3 := by
  have h1 : b ≤ b ^ 3 := Nat.le_self_pow (by decide) b
  have h2 : b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
  omega

private lemma h_eq_card_E {n : ℕ} (hn : 1 ≤ n) :
    Erdos942.erdos_942.h n =
      open scoped Classical in
      ((Finset.Icc 1 ((n + 1) ^ 2)).filter (fun b => Squarefree b ∧ E b n)).card := by
  classical
  unfold Erdos942.erdos_942.h
  symm
  refine Finset.card_bij
    (fun b hb => (Classical.choose ((Finset.mem_filter.mp hb).2.2)) ^ 2 * b ^ 3) ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbI, hsq, hE⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha1, hlo, hhi⟩ := Classical.choose_spec hE
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hlo, hhi⟩, ?_⟩
    have hm1 : 1 ≤ Classical.choose hE ^ 2 * b ^ 3 := by
      have : 1 ≤ n ^ 2 := by nlinarith
      omega
    exact (powerful_iff_sq_mul_cube hm1).mpr ⟨Classical.choose hE, b, ha1, hsq, rfl⟩
  · intro b₁ hb₁ b₂ hb₂ heq
    obtain ⟨_, hsq₁, hE₁⟩ := Finset.mem_filter.mp hb₁
    obtain ⟨_, hsq₂, hE₂⟩ := Finset.mem_filter.mp hb₂
    have ha₁ := (Classical.choose_spec hE₁).1
    have ha₂ := (Classical.choose_spec hE₂).1
    exact (sq_mul_cube_unique ha₁ hsq₁ ha₂ hsq₂ heq).2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Ico] at hm
    obtain ⟨⟨hlo, hhi⟩, hpow⟩ := hm
    have hm1 : 1 ≤ m := by nlinarith
    obtain ⟨a, b, ha1, hsq, rfl⟩ := (powerful_iff_sq_mul_cube hm1).mp hpow
    have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hsq.ne_zero
    have hb_le : b ≤ (n + 1) ^ 2 := le_of_lt (lt_of_le_of_lt (b_le_sq_mul_cube ha1) hhi)
    have hE : E b n := ⟨a, ha1, hlo, hhi⟩
    have hmem : b ∈ (Finset.Icc 1 ((n + 1) ^ 2)).filter (fun b => Squarefree b ∧ E b n) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb1, hb_le⟩, hsq, hE⟩
    refine ⟨b, hmem, ?_⟩
    have hspec := Classical.choose_spec hE
    have ha_eq : Classical.choose hE = a :=
      E_unique_a hb1 ⟨hspec.2.1, hspec.2.2⟩ ⟨hlo, hhi⟩
    rw [ha_eq]

/-- Truncated count of powerful numbers in `[n ^ 2, (n + 1) ^ 2)` coming from `b ≤ B`. -/
private noncomputable def hTrunc (B n : ℕ) : ℕ :=
  open scoped Classical in
  ((Finset.Icc 1 B).filter (fun b => Squarefree b ∧ E b n)).card

private lemma hTrunc_le_h {B n : ℕ} (hn : 1 ≤ n) : hTrunc B n ≤ Erdos942.erdos_942.h n := by
  classical
  rw [h_eq_card_E hn, hTrunc]
  apply Finset.card_le_card
  intro b hb
  rw [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
  obtain ⟨⟨hb1, _⟩, hsq, ⟨a, ha1, hlo, hhi⟩⟩ := hb
  exact ⟨⟨hb1, le_of_lt (lt_of_le_of_lt (b_le_sq_mul_cube ha1) hhi)⟩, hsq, ⟨a, ha1, hlo, hhi⟩⟩

private lemma h_sub_hTrunc_le {B n N : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    Erdos942.erdos_942.h n - hTrunc B n ≤
      open scoped Classical in
      ((Finset.Ioc B (N ^ 2)).filter (fun b => E b n)).card := by
  classical
  rw [h_eq_card_E hn, hTrunc]
  set S₁ := (Finset.Icc 1 ((n + 1) ^ 2)).filter (fun b => Squarefree b ∧ E b n)
  set S₂ := (Finset.Icc 1 B).filter (fun b => Squarefree b ∧ E b n)
  have hsub : S₂ ⊆ S₁ := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    obtain ⟨⟨hb1, _⟩, hsq, ⟨a, ha1, hlo, hhi⟩⟩ := hb
    exact ⟨⟨hb1, le_of_lt (lt_of_le_of_lt (b_le_sq_mul_cube ha1) hhi)⟩, hsq, ⟨a, ha1, hlo, hhi⟩⟩
  rw [← Finset.card_sdiff_of_subset hsub]
  apply Finset.card_le_card
  intro b hb
  rw [Finset.mem_sdiff] at hb
  obtain ⟨hb1, hb2⟩ := hb
  rw [Finset.mem_filter, Finset.mem_Icc] at hb1 hb2
  rw [Finset.mem_filter, Finset.mem_Ioc]
  have hBb : B < b := by
    by_contra hle
    push Not at hle
    exact hb2 ⟨⟨hb1.1.1, hle⟩, hb1.2⟩
  have hbN : b ≤ N ^ 2 := by
    have : n + 1 ≤ N := hnN
    have : (n + 1) ^ 2 ≤ N ^ 2 := by nlinarith
    omega
  exact ⟨⟨hBb, hbN⟩, hb1.2.2⟩

private lemma card_E_le {b N : ℕ} (hb : 1 ≤ b) :
    open scoped Classical in
    (((Finset.Ico 1 N).filter (fun n => E b n)).card : ℝ) ≤
      (N : ℝ) * (((b : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  classical
  set r : ℝ := (b : ℝ) ^ (3 / 2 : ℝ)
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hb_pos _
  have hr_sq : r ^ 2 = (b : ℝ) ^ 3 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb_pos.le]
    norm_num
  set M : ℕ := Nat.floor ((N : ℝ) * r⁻¹)
  have hcard : ((Finset.Ico 1 N).filter (fun n => E b n)).card ≤ (Finset.Icc 1 M).card := by
    refine Finset.card_le_card_of_injOn
      (fun n => if h : ∃ a : ℕ, 1 ≤ a ∧ n ^ 2 ≤ a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n + 1) ^ 2
        then Classical.choose h else 0) ?_ ?_
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hn
      obtain ⟨⟨_, hnN⟩, hE⟩ := hn
      have hE' : ∃ a : ℕ, 1 ≤ a ∧ n ^ 2 ≤ a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n + 1) ^ 2 := hE
      simp only [dif_pos hE', Finset.mem_coe, Finset.mem_Icc]
      obtain ⟨ha1, _, hhi⟩ := Classical.choose_spec hE'
      set a : ℕ := Classical.choose hE'
      refine ⟨ha1, ?_⟩
      have hN2 : a ^ 2 * b ^ 3 < N ^ 2 := by
        have : (n + 1) ^ 2 ≤ N ^ 2 := by nlinarith
        omega
      have hR : ((a : ℝ) * r) ^ 2 < (N : ℝ) ^ 2 := by
        have hcast : ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) < (N : ℝ) ^ 2 := by
          exact_mod_cast hN2
        calc ((a : ℝ) * r) ^ 2
            = (a : ℝ) ^ 2 * r ^ 2 := by ring
          _ = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by rw [hr_sq]
          _ < (N : ℝ) ^ 2 := hcast
      have hlt : (a : ℝ) * r < (N : ℝ) := by nlinarith
      have hlt' : (a : ℝ) ≤ (N : ℝ) * r⁻¹ := by
        rw [le_mul_inv_iff₀ hr_pos]
        exact hlt.le
      exact Nat.le_floor hlt'
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
      have hE₁ : ∃ a : ℕ, 1 ≤ a ∧ n₁ ^ 2 ≤ a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n₁ + 1) ^ 2 := hn₁.2
      have hE₂ : ∃ a : ℕ, 1 ≤ a ∧ n₂ ^ 2 ≤ a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 < (n₂ + 1) ^ 2 := hn₂.2
      simp only [dif_pos hE₁, dif_pos hE₂] at heq
      have h₁ := Classical.choose_spec hE₁
      have h₂ := Classical.choose_spec hE₂
      rw [← heq] at h₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (n₁ + 1) ^ 2 ≤ n₂ ^ 2 := by nlinarith
        omega
      · have : (n₂ + 1) ^ 2 ≤ n₁ ^ 2 := by nlinarith
        omega
  calc (((Finset.Ico 1 N).filter (fun n => E b n)).card : ℝ)
      ≤ ((Finset.Icc 1 M).card : ℝ) := by exact_mod_cast hcard
    _ = (M : ℝ) := by simp [Nat.card_Icc]
    _ ≤ (N : ℝ) * r⁻¹ := Nat.floor_le (by positivity)

private noncomputable def tailSum (B : ℕ) : ℝ :=
  ∑' k : ℕ, (((B + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹

private lemma summable_rpow_three_halves :
    Summable (fun b : ℕ => ((b : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  simpa using Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)

private lemma summable_tail (B : ℕ) :
    Summable (fun k : ℕ => (((B + 1 + k : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  summable_rpow_three_halves.comp_injective (add_right_injective (B + 1))

private lemma sum_h_sub_hTrunc_le (B N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, ((Erdos942.erdos_942.h n - hTrunc B n : ℕ) : ℝ)) ≤
      (N : ℝ) * tailSum B := by
  classical
  have h1 : ∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n - hTrunc B n) ≤
      ∑ n ∈ Finset.Ico 1 N, ((Finset.Ioc B (N ^ 2)).filter (fun b => E b n)).card := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact h_sub_hTrunc_le hn.1 hn.2
  have hswap : ∑ n ∈ Finset.Ico 1 N, ((Finset.Ioc B (N ^ 2)).filter (fun b => E b n)).card =
      ∑ b ∈ Finset.Ioc B (N ^ 2), ((Finset.Ico 1 N).filter (fun n => E b n)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : (∑ n ∈ Finset.Ico 1 N, ((Erdos942.erdos_942.h n - hTrunc B n : ℕ) : ℝ)) ≤
      ∑ b ∈ Finset.Ioc B (N ^ 2), (N : ℝ) * (((b : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    calc (∑ n ∈ Finset.Ico 1 N, ((Erdos942.erdos_942.h n - hTrunc B n : ℕ) : ℝ))
        = ((∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n - hTrunc B n) : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ((∑ b ∈ Finset.Ioc B (N ^ 2), ((Finset.Ico 1 N).filter (fun n => E b n)).card : ℕ) : ℝ) := by
          exact_mod_cast hswap ▸ h1
      _ = ∑ b ∈ Finset.Ioc B (N ^ 2), (((Finset.Ico 1 N).filter (fun n => E b n)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ b ∈ Finset.Ioc B (N ^ 2), (N : ℝ) * (((b : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          exact card_E_le (by omega)
  calc (∑ n ∈ Finset.Ico 1 N, ((Erdos942.erdos_942.h n - hTrunc B n : ℕ) : ℝ))
      ≤ (N : ℝ) * ∑ b ∈ Finset.Ioc B (N ^ 2), (((b : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
        rw [Finset.mul_sum]; exact h2
    _ ≤ (N : ℝ) * tailSum B := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
        have hIoc : Finset.Ioc B (N ^ 2) =
            (Finset.range (N ^ 2 - B)).image (fun k => B + 1 + k) := by
          ext b
          simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
          constructor
          · intro ⟨h1, h2⟩
            exact ⟨b - (B + 1), by omega, by omega⟩
          · rintro ⟨k, hk, rfl⟩
            omega
        rw [hIoc, Finset.sum_image (by intro x _ y _ h; dsimp at h; omega)]
        exact (summable_tail B).sum_le_tsum (Finset.range (N ^ 2 - B))
          (fun k _ => by positivity)

private lemma tendsto_tailSum_zero : Tendsto tailSum atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)
  have h' : Tendsto (fun B : ℕ => ∑' k : ℕ, (((k + (B + 1) : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun B => ?_
  dsimp [tailSum]
  congr 1
  ext k
  have : k + (B + 1) = B + 1 + k := by omega
  rw [this]

/- ### Section 2: Fractional part characterization of `E b n` -/

private noncomputable def alpha (b : ℕ) : ℝ := ((b : ℝ) * Real.sqrt b)⁻¹

private lemma alpha_pos {b : ℕ} (hb : 1 ≤ b) : 0 < alpha b := by
  unfold alpha
  have : (0 : ℝ) < (b : ℝ) := by positivity
  have : 0 < Real.sqrt b := Real.sqrt_pos.mpr this
  positivity

private lemma alpha_lt_one {b : ℕ} (hb : 1 < b) : alpha b < 1 := by
  unfold alpha
  rw [inv_lt_one_iff₀]
  right
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hsq : (1 : ℝ) ≤ Real.sqrt b := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  nlinarith

private lemma irrational_alpha {b : ℕ} (hb : Squarefree b) (hb1 : 1 < b) :
    Irrational (alpha b) := by
  have hnsq : ¬ IsSquare b := by
    rintro ⟨k, hk⟩
    have hdvd : k * k ∣ b := ⟨1, by linarith⟩
    have hunit : IsUnit k := hb k hdvd
    have hk1 : k = 1 := Nat.isUnit_iff.mp hunit
    subst hk1
    omega
  have hirr : Irrational (Real.sqrt b) := irrational_sqrt_natCast_iff.mpr hnsq
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hsq_eq : alpha b = ((b ^ 2 : ℚ) : ℝ)⁻¹ * Real.sqrt b := by
    unfold alpha
    push_cast
    have hsqrt_sq : Real.sqrt b * Real.sqrt b = (b : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg b)
    have hsqrt_ne : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
    linarith
  rw [hsq_eq]
  have hq : ((b ^ 2 : ℚ)⁻¹ : ℚ) ≠ 0 := by
    have : (b : ℚ) ≠ 0 := by positivity
    positivity
  simpa using hirr.ratCast_mul hq

private lemma E_one {n : ℕ} (hn : 1 ≤ n) : E 1 n :=
  ⟨n, hn, by nlinarith, by nlinarith⟩

private lemma E_iff_fract_gt {b n : ℕ} (hb : Squarefree b) (hb1 : 1 < b) (hn : 1 ≤ n) :
    E b n ↔ 1 - alpha b < Int.fract ((n : ℝ) * alpha b) := by
  have hirr := irrational_alpha hb hb1
  have hα_pos : 0 < alpha b := alpha_pos (by omega)
  have hα_lt : alpha b < 1 := alpha_lt_one hb1
  have hb_pos : (0 : ℝ) < (b : ℝ) := by positivity
  have hbs_pos : 0 < (b : ℝ) * Real.sqrt b := by positivity
  have hbs_sq : ((b : ℝ) * Real.sqrt b) ^ 2 = (b : ℝ) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hb_pos.le]; ring
  have hn_not_int : ∀ z : ℤ, (n : ℝ) * alpha b ≠ (z : ℝ) := by
    intro z hz
    have : Irrational ((n : ℝ) * alpha b) := by
      have hn0 : (n : ℚ) ≠ 0 := by positivity
      simpa using hirr.ratCast_mul hn0
    exact this.ne_int z hz
  have hfract_pos : 0 < Int.fract ((n : ℝ) * alpha b) := by
    have hge := Int.fract_nonneg ((n : ℝ) * alpha b)
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h.symm
      exact hn_not_int z hz.symm
  constructor
  · rintro ⟨a, ha1, hlo, hhi⟩
    have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) * ((b : ℝ) * Real.sqrt b) := by positivity
    have hloR : (n : ℝ) ≤ (a : ℝ) * ((b : ℝ) * Real.sqrt b) := by
      have h1 : (n : ℝ) ^ 2 ≤ ((a : ℝ) * ((b : ℝ) * Real.sqrt b)) ^ 2 := by
        rw [mul_pow, hbs_sq]
        exact_mod_cast hlo
      nlinarith
    have hhiR : (a : ℝ) * ((b : ℝ) * Real.sqrt b) < (n : ℝ) + 1 := by
      have h1 : ((a : ℝ) * ((b : ℝ) * Real.sqrt b)) ^ 2 < ((n : ℝ) + 1) ^ 2 := by
        rw [mul_pow, hbs_sq]
        exact_mod_cast hhi
      nlinarith
    have hlo' : (n : ℝ) * alpha b ≤ (a : ℝ) := by
      unfold alpha
      rw [mul_inv_le_iff₀ hbs_pos]
      linarith
    have hhi' : (a : ℝ) < ((n : ℝ) + 1) * alpha b := by
      unfold alpha
      rw [lt_mul_inv_iff₀ hbs_pos]
      linarith
    set k : ℤ := ⌊(n : ℝ) * alpha b⌋
    have hk_lt : (k : ℝ) < (a : ℝ) := by
      have : (k : ℝ) + Int.fract ((n : ℝ) * alpha b) = (n : ℝ) * alpha b := Int.floor_add_fract _
      linarith
    have hk1_le : k + 1 ≤ (a : ℤ) := by
      have : k < (a : ℤ) := by exact_mod_cast hk_lt
      omega
    have hk1_leR : (k : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hk1_le
    have hdecomp : (k : ℝ) + Int.fract ((n : ℝ) * alpha b) = (n : ℝ) * alpha b :=
      Int.floor_add_fract _
    linarith
  · intro hgt
    set k : ℤ := ⌊(n : ℝ) * alpha b⌋
    have hk_nonneg : 0 ≤ k := Int.floor_nonneg.mpr (by positivity)
    set a : ℕ := (k + 1).toNat
    have ha_cast : (a : ℝ) = (k : ℝ) + 1 := by
      have : (a : ℤ) = k + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have ha1 : 1 ≤ a := by omega
    have hdecomp : (k : ℝ) + Int.fract ((n : ℝ) * alpha b) = (n : ℝ) * alpha b :=
      Int.floor_add_fract _
    have hfrac_lt : Int.fract ((n : ℝ) * alpha b) < 1 := Int.fract_lt_one _
    have hlo' : (n : ℝ) * alpha b ≤ (a : ℝ) := by linarith
    have hhi' : (a : ℝ) < ((n : ℝ) + 1) * alpha b := by linarith
    have hloR : (n : ℝ) ≤ (a : ℝ) * ((b : ℝ) * Real.sqrt b) := by
      unfold alpha at hlo'
      rwa [mul_inv_le_iff₀ hbs_pos] at hlo'
    have hhiR : (a : ℝ) * ((b : ℝ) * Real.sqrt b) < (n : ℝ) + 1 := by
      unfold alpha at hhi'
      rwa [lt_mul_inv_iff₀ hbs_pos] at hhi'
    refine ⟨a, ha1, ?_, ?_⟩
    · have : (n : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
        calc (n : ℝ) ^ 2 ≤ ((a : ℝ) * ((b : ℝ) * Real.sqrt b)) ^ 2 := by nlinarith
          _ = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by rw [mul_pow, hbs_sq]
      exact_mod_cast this
    · have : (a : ℝ) ^ 2 * (b : ℝ) ^ 3 < ((n : ℝ) + 1) ^ 2 := by
        calc (a : ℝ) ^ 2 * (b : ℝ) ^ 3 = ((a : ℝ) * ((b : ℝ) * Real.sqrt b)) ^ 2 := by
              rw [mul_pow, hbs_sq]
          _ < ((n : ℝ) + 1) ^ 2 := by nlinarith
      exact_mod_cast this

private lemma not_E_iff_fract_lt {b n : ℕ} (hb : Squarefree b) (hb1 : 1 < b) (hn : 1 ≤ n) :
    ¬ E b n ↔ 0 < Int.fract ((n : ℝ) * alpha b) ∧ Int.fract ((n : ℝ) * alpha b) < 1 - alpha b := by
  have hirr := irrational_alpha hb hb1
  have hn_not_int : ∀ z : ℤ, (n : ℝ) * alpha b ≠ (z : ℝ) := by
    intro z hz
    have : Irrational ((n : ℝ) * alpha b) := by
      have hn0 : (n : ℚ) ≠ 0 := by positivity
      simpa using hirr.ratCast_mul hn0
    exact this.ne_int z hz
  have hn1_not_int : ∀ z : ℤ, ((n + 1 : ℕ) : ℝ) * alpha b ≠ (z : ℝ) := by
    intro z hz
    have : Irrational (((n + 1 : ℕ) : ℝ) * alpha b) := by
      have hn0 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      simpa using hirr.ratCast_mul hn0
    exact this.ne_int z hz
  have hpos : 0 < Int.fract ((n : ℝ) * alpha b) := by
    have hge := Int.fract_nonneg ((n : ℝ) * alpha b)
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h.symm
      exact hn_not_int z hz.symm
  have hne : Int.fract ((n : ℝ) * alpha b) ≠ 1 - alpha b := by
    intro heq
    have hdecomp : (⌊(n : ℝ) * alpha b⌋ : ℝ) + Int.fract ((n : ℝ) * alpha b) = (n : ℝ) * alpha b :=
      Int.floor_add_fract _
    have h1 : ((n + 1 : ℕ) : ℝ) * alpha b = ((⌊(n : ℝ) * alpha b⌋ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact hn1_not_int (⌊(n : ℝ) * alpha b⌋ + 1) h1
  rw [E_iff_fract_gt hb hb1 hn]
  constructor
  · intro h
    refine ⟨hpos, lt_of_le_of_ne (not_lt.mp h) hne⟩
  · intro ⟨_, hlt⟩
    linarith

/- ### Section 3: Torus Cesàro convergence, 1D Weyl equidistribution, and box density -/

section TorusDensity

open ContinuousMap MeasureTheory

private noncomputable def torusChar {ι : Type*} [Fintype ι] (m : ι → ℤ) :
    C(ι → UnitAddCircle, ℂ) where
  toFun x := ∏ i : ι, fourier (T := (1 : ℝ)) (m i) (x i)
  continuous_toFun := continuous_finsetProd _ fun i _ =>
    (fourier (T := (1 : ℝ)) (m i)).continuous.comp (continuous_apply i)

private lemma torusChar_zero {ι : Type*} [Fintype ι] :
    torusChar (ι := ι) 0 = 1 := by
  ext x
  simp [torusChar]

private lemma torusChar_add {ι : Type*} [Fintype ι] (m₁ m₂ : ι → ℤ) :
    torusChar (m₁ + m₂) = torusChar m₁ * torusChar m₂ := by
  ext x
  simp [torusChar, Finset.prod_mul_distrib]

private lemma torusChar_neg {ι : Type*} [Fintype ι] (m : ι → ℤ) :
    torusChar (-m) = star (torusChar m) := by
  ext x
  simp [torusChar]

private noncomputable def torusSubalgebra (ι : Type*) [Fintype ι] :
    StarSubalgebra ℂ C(ι → UnitAddCircle, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (torusChar (ι := ι)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (torusChar (ι := ι))) ≤
      star (Algebra.adjoin ℂ (Set.range (torusChar (ι := ι))))
    refine Algebra.adjoin_le ?_
    rintro - ⟨m, rfl⟩
    exact Algebra.subset_adjoin ⟨-m, torusChar_neg m⟩

private lemma torusSubalgebra_coe (ι : Type*) [Fintype ι] :
    Subalgebra.toSubmodule (torusSubalgebra ι).toSubalgebra =
      Submodule.span ℂ (Set.range (torusChar (ι := ι))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ h => h) ⟨0, torusChar_zero⟩ ?_ hx
  rintro - - - - ⟨m₁, rfl⟩ ⟨m₂, rfl⟩
  exact ⟨m₁ + m₂, torusChar_add m₁ m₂⟩

private lemma torusSubalgebra_separatesPoints (ι : Type*) [Fintype ι] :
    (torusSubalgebra ι).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨torusChar (Pi.single (M := fun _ => ℤ) i 1),
    Algebra.subset_adjoin ⟨Pi.single (M := fun _ => ℤ) i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only [torusChar, ContinuousMap.coe_mk]
  have eval_single : ∀ z : ι → UnitAddCircle,
      (∏ j : ι, fourier (T := (1 : ℝ)) (Pi.single (M := fun _ => ℤ) i 1 j) (z j)) =
        AddCircle.toCircle (z i) := by
    intro z
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  rw [eval_single x, eval_single y]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext hi)

private lemma span_torusChar_closure_eq_top (ι : Type*) [Fintype ι] :
    (Submodule.span ℂ (Set.range (torusChar (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← torusSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (torusSubalgebra ι) (torusSubalgebra_separatesPoints ι))

private noncomputable def cesaroC {ι : Type*} (α : ι → ℝ)
    (f : (ι → UnitAddCircle) → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (fun i => ((n : ℝ) * α i : UnitAddCircle))

private noncomputable def cesaroR {ι : Type*} (α : ι → ℝ)
    (f : (ι → UnitAddCircle) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (fun i => ((n : ℝ) * α i : UnitAddCircle))

private lemma tendsto_cesaro_geom {z : ℂ} (hz_norm : ‖z‖ = 1) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n) atTop
      (𝓝 (if z = 1 then (1 : ℂ) else 0)) := by
  by_cases hz : z = 1
  · subst hz
    simp only [↓reduceIte, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact (inv_mul_cancel₀ hN0).symm
  · simp only [hz, ↓reduceIte]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n‖ ≤
        (2 / ‖z - 1‖) / (N : ℝ) := by
      intro N
      by_cases hN : N = 0
      · simp [hN]
      · rw [geom_sum_eq hz N, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
        have hnum : ‖z ^ N - 1‖ ≤ 2 := by
          calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = ‖z‖ ^ N + 1 := by simp [norm_pow]
            _ = 2 := by rw [hz_norm]; norm_num
        have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
        have hdiv : ‖z ^ N - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ :=
          div_le_div_of_nonneg_right hnum hden.le
        have hN_nonneg : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
        calc (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖)
            ≤ (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := mul_le_mul_of_nonneg_left hdiv hN_nonneg
          _ = (2 / ‖z - 1‖) / (N : ℝ) := by ring
    exact squeeze_zero (fun N => norm_nonneg _) hbd
      (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖z - 1‖))

private lemma exists_tendsto_cesaroC_torusChar {ι : Type*} [Fintype ι] (α : ι → ℝ) (m : ι → ℤ) :
    ∃ L : ℂ, Tendsto (cesaroC α (torusChar m)) atTop (𝓝 L) := by
  set z : ℂ := ∏ i : ι, fourier (T := (1 : ℝ)) (m i) (α i : UnitAddCircle)
  have hz_norm : ‖z‖ = 1 := by
    dsimp [z]
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro i _
    exact Circle.norm_coe _
  refine ⟨if z = 1 then 1 else 0, ?_⟩
  refine (tendsto_cesaro_geom hz_norm).congr fun N => ?_
  dsimp [cesaroC]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  change (∏ i : ι, fourier (T := (1 : ℝ)) (m i) (α i : UnitAddCircle)) ^ n =
    ∏ i : ι, fourier (T := (1 : ℝ)) (m i) (((n : ℝ) * α i : ℝ) : UnitAddCircle)
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma exists_tendsto_cesaroC_span {ι : Type*} [Fintype ι] (α : ι → ℝ)
    {g : C(ι → UnitAddCircle, ℂ)}
    (hg : g ∈ Submodule.span ℂ (Set.range (torusChar (ι := ι)))) :
    ∃ L : ℂ, Tendsto (cesaroC α g) atTop (𝓝 L) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact exists_tendsto_cesaroC_torusChar α m
  | zero =>
    refine ⟨0, ?_⟩
    have heq : cesaroC α ⇑(0 : C(ι → UnitAddCircle, ℂ)) = fun _ => 0 := by
      ext N
      simp [cesaroC]
    rw [heq]
    exact tendsto_const_nhds
  | add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨L₁, hL₁⟩ := ih₁
    obtain ⟨L₂, hL₂⟩ := ih₂
    refine ⟨L₁ + L₂, ?_⟩
    have heq : cesaroC α ⇑(f₁ + f₂) = fun N => cesaroC α ⇑f₁ N + cesaroC α ⇑f₂ N := by
      ext N
      simp [cesaroC, Finset.sum_add_distrib, mul_add]
    rw [heq]
    exact hL₁.add hL₂
  | smul c f _ ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨c * L, ?_⟩
    have heq : cesaroC α ⇑(c • f) = fun N => c * cesaroC α ⇑f N := by
      ext N
      simp [cesaroC, ← Finset.mul_sum]
      ring
    rw [heq]
    exact hL.const_mul c

private lemma norm_cesaroC_sub_le {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (f g : C(ι → UnitAddCircle, ℂ)) (N : ℕ) :
    ‖cesaroC α f N - cesaroC α g N‖ ≤ ‖f - g‖ := by
  by_cases hN : N = 0
  · simp [cesaroC, hN]
  · have hsub : cesaroC α f N - cesaroC α g N =
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f - g) (fun i => ((n : ℝ) * α i : UnitAddCircle)) := by
      simp [cesaroC, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [hsub, norm_mul, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ n ∈ Finset.range N, (f - g) (fun i => ((n : ℝ) * α i : UnitAddCircle))‖ ≤
        (N : ℝ) * ‖f - g‖ := by
      calc ‖∑ n ∈ Finset.range N, (f - g) (fun i => ((n : ℝ) * α i : UnitAddCircle))‖
          ≤ ∑ n ∈ Finset.range N, ‖(f - g) (fun i => ((n : ℝ) * α i : UnitAddCircle))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
            Finset.sum_le_sum fun _ _ => ContinuousMap.norm_coe_le_norm (f - g) _
        _ = (N : ℝ) * ‖f - g‖ := by simp
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f - g) (fun i => ((n : ℝ) * α i : UnitAddCircle))‖
        ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖f - g‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ‖f - g‖ := by field_simp

private lemma exists_tendsto_cesaroC {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (f : C(ι → UnitAddCircle, ℂ)) :
    ∃ L : ℂ, Tendsto (cesaroC α f) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hf_mem : f ∈ closure ((Submodule.span ℂ (Set.range (torusChar (ι := ι))) :
      Submodule ℂ C(ι → UnitAddCircle, ℂ)) : Set C(ι → UnitAddCircle, ℂ)) := by
    change f ∈ (Submodule.span ℂ (Set.range (torusChar (ι := ι)))).topologicalClosure
    rw [span_torusChar_closure_eq_top]
    trivial
  rw [Metric.mem_closure_iff] at hf_mem
  obtain ⟨g, hg_mem, hfg⟩ := hf_mem (ε / 3) (by positivity)
  have hfg' : ‖f - g‖ < ε / 3 := by rwa [dist_eq_norm] at hfg
  obtain ⟨L, hL⟩ := exists_tendsto_cesaroC_span α hg_mem
  have hcauchy := Metric.cauchySeq_iff.mp hL.cauchySeq (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := hcauchy
  refine ⟨N₀, fun m hm n hn => ?_⟩
  have h1 : dist (cesaroC α f m) (cesaroC α g m) < ε / 3 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (norm_cesaroC_sub_le α f g m) hfg'
  have h2 : dist (cesaroC α g m) (cesaroC α g n) < ε / 3 := hN₀ m hm n hn
  have h3 : dist (cesaroC α g n) (cesaroC α f n) < ε / 3 := by
    rw [_root_.dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (norm_cesaroC_sub_le α f g n) hfg'
  linarith [dist_triangle4 (cesaroC α f m) (cesaroC α g m) (cesaroC α g n) (cesaroC α f n)]

private lemma exists_tendsto_cesaroR {ι : Type*} [Fintype ι] (α : ι → ℝ)
    (f : C(ι → UnitAddCircle, ℝ)) :
    ∃ L : ℝ, Tendsto (cesaroR α f) atTop (𝓝 L) := by
  let fC : C(ι → UnitAddCircle, ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  obtain ⟨L, hL⟩ := exists_tendsto_cesaroC α fC
  refine ⟨L.re, ?_⟩
  have hre := (Complex.continuous_re.tendsto L).comp hL
  refine hre.congr fun N => ?_
  dsimp [Function.comp_def, cesaroC, cesaroR, fC]
  have : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f (fun i => ((n : ℝ) * α i : UnitAddCircle)) : ℂ)) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (fun i => ((n : ℝ) * α i : UnitAddCircle)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

/- 1D Weyl equidistribution for irrational rotations -/

private lemma integral_fourier_unitAddCircle (k : ℤ) :
    ∫ t : UnitAddCircle, fourier (T := (1 : ℝ)) k t ∂AddCircle.haarAddCircle =
      if k = 0 then (1 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · simp only [hk, ↓reduceIte]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk one_pos)

private lemma tendsto_cesaro_1d_fourier {β : ℝ} (hβ : Irrational β) (k : ℤ) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      fourier (T := (1 : ℝ)) k (((n : ℝ) * β : ℝ) : UnitAddCircle)) atTop
      (𝓝 (∫ t : UnitAddCircle, fourier (T := (1 : ℝ)) k t ∂AddCircle.haarAddCircle)) := by
  rw [integral_fourier_unitAddCircle]
  set z : ℂ := fourier (T := (1 : ℝ)) k (β : UnitAddCircle)
  have hz_norm : ‖z‖ = 1 := Circle.norm_coe _
  have hconv : ∀ N : ℕ,
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        fourier (T := (1 : ℝ)) k (((n : ℝ) * β : ℝ) : UnitAddCircle) =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
    intro N
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    change fourier (T := (1 : ℝ)) k (((n : ℝ) * β : ℝ) : UnitAddCircle) =
      (fourier (T := (1 : ℝ)) k (β : UnitAddCircle)) ^ n
    rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hconv]
  have hiff : z = 1 ↔ k = 0 := by
    constructor
    · intro hz1
      by_contra hk
      have h0 : AddCircle.toCircle (k • (β : UnitAddCircle)) =
          AddCircle.toCircle (0 : UnitAddCircle) := by
        apply Subtype.ext
        change (fourier (T := (1 : ℝ)) k (β : UnitAddCircle)) = (1 : ℂ) at hz1
        simpa [fourier_apply, AddCircle.toCircle_zero] using hz1
      have hq0 : k • (β : UnitAddCircle) = 0 :=
        AddCircle.injective_toCircle one_ne_zero h0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at hq0
      rw [AddSubgroup.mem_zmultiples_iff] at hq0
      obtain ⟨m, hm⟩ := hq0
      simp only [zsmul_eq_mul, mul_one] at hm
      have hrat : ((m : ℚ) / (k : ℚ) : ℝ) = β := by
        push_cast
        have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
        field_simp
        linarith
      exact hβ ⟨(m : ℚ) / (k : ℚ), by simpa using hrat⟩
    · intro hk
      subst hk
      simp [z]
  simpa [hiff] using tendsto_cesaro_geom hz_norm

private lemma tendsto_cesaro_1d_span {β : ℝ} (hβ : Irrational β)
    {g : C(UnitAddCircle, ℂ)}
    (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      g (((n : ℝ) * β : ℝ) : UnitAddCircle)) atTop
      (𝓝 (∫ t : UnitAddCircle, g t ∂AddCircle.haarAddCircle)) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact tendsto_cesaro_1d_fourier hβ k
  | zero =>
    simp
  | add f₁ f₂ _ _ ih₁ ih₂ =>
    have hf₁ : Integrable f₁ AddCircle.haarAddCircle :=
      f₁.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hf₂ : Integrable f₂ AddCircle.haarAddCircle :=
      f₂.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hint : ∫ t : UnitAddCircle, (f₁ + f₂) t ∂AddCircle.haarAddCircle =
        (∫ t, f₁ t ∂AddCircle.haarAddCircle) + (∫ t, f₂ t ∂AddCircle.haarAddCircle) :=
      integral_add hf₁ hf₂
    rw [hint]
    have hsum : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        (f₁ + f₂) (((n : ℝ) * β : ℝ) : UnitAddCircle)) =
        fun N : ℕ => ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f₁ (((n : ℝ) * β : ℝ) : UnitAddCircle)) +
          ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f₂ (((n : ℝ) * β : ℝ) : UnitAddCircle)) := by
      ext N
      simp [Finset.sum_add_distrib, mul_add]
    rw [hsum]
    exact ih₁.add ih₂
  | smul c f _ ih =>
    have hint : ∫ t : UnitAddCircle, (c • f) t ∂AddCircle.haarAddCircle =
        c * ∫ t, f t ∂AddCircle.haarAddCircle := by
      simpa [smul_eq_mul] using integral_const_mul c (f : UnitAddCircle → ℂ)
    rw [hint]
    have hmul : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        (c • f) (((n : ℝ) * β : ℝ) : UnitAddCircle)) =
        fun N : ℕ => c * ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (((n : ℝ) * β : ℝ) : UnitAddCircle)) := by
      ext N
      simp [← Finset.mul_sum]
      ring
    rw [hmul]
    exact ih.const_mul c

private lemma tendsto_cesaro_1d_complex {β : ℝ} (hβ : Irrational β)
    (ψ : C(UnitAddCircle, ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      ψ (((n : ℝ) * β : ℝ) : UnitAddCircle)) atTop
      (𝓝 (∫ t : UnitAddCircle, ψ t ∂AddCircle.haarAddCircle)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hψ_mem : ψ ∈ closure ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
      Submodule ℂ C(UnitAddCircle, ℂ)) : Set C(UnitAddCircle, ℂ)) := by
    change ψ ∈ (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  rw [Metric.mem_closure_iff] at hψ_mem
  obtain ⟨g, hg_mem, hψg⟩ := hψ_mem (ε / 3) (by positivity)
  have hψg' : ‖ψ - g‖ < ε / 3 := by rwa [dist_eq_norm] at hψg
  have hg_tend := Metric.tendsto_atTop.mp (tendsto_cesaro_1d_span hβ hg_mem) (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := hg_tend
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ψ (((n : ℝ) * β : ℝ) : UnitAddCircle))
      ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (((n : ℝ) * β : ℝ) : UnitAddCircle)) < ε / 3 := by
    rw [dist_eq_norm]
    have hbd : ‖((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ψ (((n : ℝ) * β : ℝ) : UnitAddCircle)) -
        ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (((n : ℝ) * β : ℝ) : UnitAddCircle))‖ ≤ ‖ψ - g‖ := by
      by_cases hN0 : N = 0
      · simp [hN0]
      · rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
        have hsum : ‖∑ n ∈ Finset.range N,
            (ψ (((n : ℝ) * β : ℝ) : UnitAddCircle) - g (((n : ℝ) * β : ℝ) : UnitAddCircle))‖ ≤
            (N : ℝ) * ‖ψ - g‖ := by
          calc _ ≤ ∑ n ∈ Finset.range N, ‖(ψ - g) (((n : ℝ) * β : ℝ) : UnitAddCircle)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _n ∈ Finset.range N, ‖ψ - g‖ :=
                Finset.sum_le_sum fun _ _ => ContinuousMap.norm_coe_le_norm (ψ - g) _
            _ = (N : ℝ) * ‖ψ - g‖ := by simp
        calc (N : ℝ)⁻¹ * _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖ψ - g‖) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = ‖ψ - g‖ := by field_simp
    exact lt_of_le_of_lt hbd hψg'
  have h2 := hN₀ N hN
  have h3 : dist (∫ t : UnitAddCircle, g t ∂AddCircle.haarAddCircle)
      (∫ t : UnitAddCircle, ψ t ∂AddCircle.haarAddCircle) < ε / 3 := by
    rw [_root_.dist_comm, dist_eq_norm]
    have hψ_int : Integrable ψ AddCircle.haarAddCircle :=
      ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hg_int : Integrable g AddCircle.haarAddCircle :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hψ_int hg_int]
    have hbd : ‖∫ t : UnitAddCircle, (ψ t - g t) ∂AddCircle.haarAddCircle‖ ≤ ‖ψ - g‖ := by
      have h := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
        (C := ‖ψ - g‖) (f := fun t => ψ t - g t)
        (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm (ψ - g) t)
      simpa using h
    exact lt_of_le_of_lt hbd hψg'
  linarith [dist_triangle4
    ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ψ (((n : ℝ) * β : ℝ) : UnitAddCircle))
    ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (((n : ℝ) * β : ℝ) : UnitAddCircle))
    (∫ t : UnitAddCircle, g t ∂AddCircle.haarAddCircle)
    (∫ t : UnitAddCircle, ψ t ∂AddCircle.haarAddCircle)]

private lemma tendsto_cesaro_1d_real {β : ℝ} (hβ : Irrational β)
    (ψ : C(UnitAddCircle, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ψ (((n : ℝ) * β : ℝ) : UnitAddCircle)) atTop
      (𝓝 (∫ t : UnitAddCircle, ψ t)) := by
  let ψC : C(UnitAddCircle, ℂ) := ⟨fun t => (ψ t : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
  have hC := tendsto_cesaro_1d_complex hβ ψC
  have hre := (Complex.continuous_re.tendsto _).comp hC
  have hint : (∫ t : UnitAddCircle, ψC t ∂AddCircle.haarAddCircle).re =
      ∫ t : UnitAddCircle, ψ t := by
    have hvol : (AddCircle.haarAddCircle (T := (1 : ℝ))) = volume := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp
    rw [hvol]
    have hψC_int : Integrable ψC volume :=
      ψC.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have := Complex.reCLM.integral_comp_comm hψC_int
    simpa [ψC] using this.symm
  rw [hint] at hre
  refine hre.congr fun N => ?_
  dsimp [Function.comp_def, ψC]
  have : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (ψ (((n : ℝ) * β : ℝ) : UnitAddCircle) : ℂ)) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ψ (((n : ℝ) * β : ℝ) : UnitAddCircle) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

/- Trapezoid approximations on `UnitAddCircle` -/

private noncomputable def trapFn (a b δ t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - a) / δ) ((b - t) / δ)))

private lemma trapFn_continuous (a b δ : ℝ) : Continuous (trapFn a b δ) := by
  unfold trapFn
  fun_prop

private lemma trapFn_nonneg (a b δ t : ℝ) : 0 ≤ trapFn a b δ t := le_max_left _ _

private lemma trapFn_le_one (a b δ t : ℝ) : trapFn a b δ t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

private lemma trapFn_eq_zero_of_le_left {a b δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ a) :
    trapFn a b δ t = 0 := by
  unfold trapFn
  have h1 : (t - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have h2 : min 1 (min ((t - a) / δ) ((b - t) / δ)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1)
  exact max_eq_left h2

private lemma trapFn_eq_zero_of_ge_right {a b δ t : ℝ} (hδ : 0 < δ) (ht : b ≤ t) :
    trapFn a b δ t = 0 := by
  unfold trapFn
  have h1 : (b - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have h2 : min 1 (min ((t - a) / δ) ((b - t) / δ)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1)
  exact max_eq_left h2

private lemma trapFn_eq_one_of_mem {a b δ t : ℝ} (hδ : 0 < δ) (h1 : a + δ ≤ t) (h2 : t ≤ b - δ) :
    trapFn a b δ t = 1 := by
  unfold trapFn
  have h1' : 1 ≤ (t - a) / δ := (one_le_div hδ).mpr (by linarith)
  have h2' : 1 ≤ (b - t) / δ := (one_le_div hδ).mpr (by linarith)
  have hmin : min 1 (min ((t - a) / δ) ((b - t) / δ)) = 1 :=
    min_eq_left (le_min h1' h2')
  rw [hmin]
  norm_num

private noncomputable def phiMinus (u v δ : ℝ) (hδ : 0 < δ) (huv : v - u < 1) :
    C(UnitAddCircle, ℝ) where
  toFun := AddCircle.liftIco (1 : ℝ) u (trapFn u v δ)
  continuous_toFun := by
    apply AddCircle.liftIco_continuous
    · rw [trapFn_eq_zero_of_le_left hδ le_rfl, trapFn_eq_zero_of_ge_right hδ (by linarith)]
    · exact (trapFn_continuous u v δ).continuousOn

private noncomputable def phiPlus (u v δ : ℝ) (hδ : 0 < δ) (huv : u < v) :
    C(UnitAddCircle, ℝ) where
  toFun := AddCircle.liftIco (1 : ℝ) u (fun t => 1 - trapFn v (u + 1) δ t)
  continuous_toFun := by
    apply AddCircle.liftIco_continuous
    · rw [trapFn_eq_zero_of_le_left hδ huv.le, trapFn_eq_zero_of_ge_right hδ le_rfl]
    · exact (continuous_const.sub (trapFn_continuous v (u + 1) δ)).continuousOn

private lemma phiMinus_le_phiPlus {u v δ : ℝ} (hδ : 0 < δ) (huv : u < v) (huv1 : v - u < 1)
    (z : UnitAddCircle) :
    0 ≤ phiMinus u v δ hδ huv1 z ∧
    phiMinus u v δ hδ huv1 z ≤ phiPlus u v δ hδ huv z ∧
    phiPlus u v δ hδ huv z ≤ 1 := by
  obtain ⟨t, ht, rfl⟩ := by
    have : z ∈ Set.univ := trivial
    rw [← AddCircle.coe_image_Ico_eq (1 : ℝ) u] at this
    exact this
  dsimp [phiMinus, phiPlus]
  rw [AddCircle.liftIco_coe_apply ht, AddCircle.liftIco_coe_apply ht]
  refine ⟨trapFn_nonneg _ _ _ _, ?_, ?_⟩
  · by_cases htv : t ≤ v
    · rw [trapFn_eq_zero_of_le_left hδ htv, sub_zero]
      exact trapFn_le_one _ _ _ _
    · push Not at htv
      rw [trapFn_eq_zero_of_ge_right hδ htv.le]
      linarith [trapFn_le_one v (u + 1) δ t]
  · linarith [trapFn_nonneg v (u + 1) δ t]

private lemma phi_sandwich {u v δ : ℝ} (hδ : 0 < δ)
    (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1) (huv1 : v - u < 1) (x : ℝ) :
    phiMinus u v δ hδ huv1 (x : UnitAddCircle) ≤
      (if u < Int.fract x ∧ Int.fract x < v then (1 : ℝ) else 0) ∧
    (if u < Int.fract x ∧ Int.fract x < v then (1 : ℝ) else 0) ≤
      phiPlus u v δ hδ huv (x : UnitAddCircle) := by
  set r : ℝ := Int.fract x
  have hr0 : 0 ≤ r := Int.fract_nonneg x
  have hr1 : r < 1 := Int.fract_lt_one x
  have hcoe_r : (x : UnitAddCircle) = (r : UnitAddCircle) := by
    rw [QuotientAddGroup.eq]
    have : -x + r = (-⌊x⌋ : ℤ) • (1 : ℝ) := by
      simp only [r, Int.fract, zsmul_eq_mul, mul_one, Int.cast_neg]
      ring
    rw [this]
    exact AddSubgroup.zsmul_mem_zmultiples _ _
  rw [hcoe_r]
  by_cases hru : u ≤ r
  · have hmem : r ∈ Set.Ico u (u + 1) := ⟨hru, by linarith⟩
    dsimp [phiMinus, phiPlus]
    rw [AddCircle.liftIco_coe_apply hmem, AddCircle.liftIco_coe_apply hmem]
    split_ifs with hcond
    · refine ⟨trapFn_le_one _ _ _ _, ?_⟩
      rw [trapFn_eq_zero_of_le_left hδ hcond.2.le, sub_zero]
    · refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hru with rfl | hgt
        · rw [trapFn_eq_zero_of_le_left hδ le_rfl]
        · have hvle : v ≤ r := by
            by_contra hlt
            push Not at hlt
            exact hcond ⟨hgt, hlt⟩
          rw [trapFn_eq_zero_of_ge_right hδ hvle]
      · linarith [trapFn_le_one v (u + 1) δ r]
  · push Not at hru
    have hcoe_r1 : (r : UnitAddCircle) = ((r + 1 : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq]
      have : -r + (r + 1) = (1 : ℤ) • (1 : ℝ) := by norm_num
      rw [this]
      exact AddSubgroup.zsmul_mem_zmultiples _ _
    have hmem : r + 1 ∈ Set.Ico u (u + 1) := ⟨by linarith, by linarith⟩
    rw [hcoe_r1]
    change AddCircle.liftIco (1 : ℝ) u (trapFn u v δ) ((r + 1 : ℝ) : UnitAddCircle) ≤ _ ∧
      _ ≤ AddCircle.liftIco (1 : ℝ) u (fun t => 1 - trapFn v (u + 1) δ t) ((r + 1 : ℝ) : UnitAddCircle)
    rw [AddCircle.liftIco_coe_apply hmem, AddCircle.liftIco_coe_apply hmem]
    have hnot : ¬ (u < r ∧ r < v) := fun h => by linarith
    simp only [hnot, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [trapFn_eq_zero_of_ge_right hδ (by linarith)]
    · linarith [trapFn_le_one v (u + 1) δ (r + 1)]

private lemma integral_phiPlus_sub_phiMinus_le {u v δ : ℝ} (hδ : 0 < δ)
    (huv : 2 * δ < v - u) (huv1 : 2 * δ < 1 - (v - u)) :
    ∫ z : UnitAddCircle, (phiPlus u v δ hδ (by linarith) z -
      phiMinus u v δ hδ (by linarith) z) ≤ 4 * δ := by
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) u]
  set g : ℝ → ℝ := fun t => (1 - trapFn v (u + 1) δ t) - trapFn u v δ t
  have hg_cont : Continuous g := by
    dsimp [g]
    exact (continuous_const.sub (trapFn_continuous _ _ _)).sub (trapFn_continuous _ _ _)
  have hcongr : ∫ a in u..u + 1,
      (phiPlus u v δ hδ (by linarith) (a : UnitAddCircle) -
        phiMinus u v δ hδ (by linarith) (a : UnitAddCircle)) =
      ∫ a in u..u + 1, g a := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ a : ℝ ∂volume, a ≠ u + 1 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with a ha hmem
    rw [Set.uIoc_of_le (by linarith : u ≤ u + 1)] at hmem
    have ha_mem : a ∈ Set.Ico u (u + 1) := ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ha⟩
    dsimp [phiPlus, phiMinus, g]
    rw [AddCircle.liftIco_coe_apply ha_mem, AddCircle.liftIco_coe_apply ha_mem]
  rw [hcongr]
  have hg_le1 : ∀ t, g t ≤ 1 := by
    intro t
    dsimp [g]
    linarith [trapFn_nonneg v (u + 1) δ t, trapFn_nonneg u v δ t]
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  have hsplit : ∫ t in u..u + 1, g t =
      (∫ t in u..u + δ, g t) + (∫ t in u + δ..v - δ, g t) +
      (∫ t in v - δ..v + δ, g t) + (∫ t in v + δ..u + 1 - δ, g t) +
      (∫ t in u + 1 - δ..u + 1, g t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hg_int _ _) (hg_int _ _),
      intervalIntegral.integral_add_adjacent_intervals (hg_int _ _) (hg_int _ _),
      intervalIntegral.integral_add_adjacent_intervals (hg_int _ _) (hg_int _ _),
      intervalIntegral.integral_add_adjacent_intervals (hg_int _ _) (hg_int _ _)]
  rw [hsplit]
  have hI1 : ∫ t in u..u + δ, g t ≤ δ := by
    have := intervalIntegral.integral_mono_on (by linarith : u ≤ u + δ) (hg_int _ _)
      intervalIntegrable_const (fun t _ => hg_le1 t)
    simpa using this
  have hI2 : ∫ t in u + δ..v - δ, g t = 0 := by
    rw [← intervalIntegral.integral_zero (a := u + δ) (b := v - δ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    dsimp [g]
    rw [trapFn_eq_one_of_mem hδ ht.1 ht.2, trapFn_eq_zero_of_le_left hδ (by linarith [ht.2])]
    ring
  have hI3 : ∫ t in v - δ..v + δ, g t ≤ 2 * δ := by
    have := intervalIntegral.integral_mono_on (by linarith : v - δ ≤ v + δ) (hg_int _ _)
      intervalIntegrable_const (fun t _ => hg_le1 t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    linarith
  have hI4 : ∫ t in v + δ..u + 1 - δ, g t = 0 := by
    rw [← intervalIntegral.integral_zero (a := v + δ) (b := u + 1 - δ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    dsimp [g]
    rw [trapFn_eq_one_of_mem hδ ht.1 ht.2, trapFn_eq_zero_of_ge_right hδ (by linarith [ht.1])]
    ring
  have hI5 : ∫ t in u + 1 - δ..u + 1, g t ≤ δ := by
    have := intervalIntegral.integral_mono_on (by linarith : u + 1 - δ ≤ u + 1) (hg_int _ _)
      intervalIntegrable_const (fun t _ => hg_le1 t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    linarith
  linarith

private lemma prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1) :
    (∏ i ∈ s, b i) - (∏ i ∈ s, a i) ≤ ∑ i ∈ s, (b i - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hj' := h j (Finset.mem_insert_self j s)
    have hs' : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hih := ih hs'
    have hprod_a_nonneg : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i hi => (hs' i hi).1
    have hprod_b_nonneg : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i hi =>
      le_trans (hs' i hi).1 (hs' i hi).2.1
    have hprod_a_le_b : ∏ i ∈ s, a i ≤ ∏ i ∈ s, b i :=
      Finset.prod_le_prod (fun i hi => (hs' i hi).1) (fun i hi => (hs' i hi).2.1)
    have hprod_b_le1 : ∏ i ∈ s, b i ≤ 1 :=
      Finset.prod_le_one (fun i hi => le_trans (hs' i hi).1 (hs' i hi).2.1)
        (fun i hi => (hs' i hi).2.2)
    have h1 : (b j - a j) * ∏ i ∈ s, b i ≤ b j - a j := by nlinarith
    have h2 : a j * ((∏ i ∈ s, b i) - (∏ i ∈ s, a i)) ≤ (∏ i ∈ s, b i) - (∏ i ∈ s, a i) := by
      nlinarith
    have hid : b j * (∏ i ∈ s, b i) - a j * (∏ i ∈ s, a i) =
        (b j - a j) * (∏ i ∈ s, b i) + a j * ((∏ i ∈ s, b i) - (∏ i ∈ s, a i)) := by ring
    linarith

private lemma partialDensity_eq_card_div (S : Set ℕ) (N : ℕ) :
    open scoped Classical in
    S.partialDensity Set.univ N =
      (((Finset.range N).filter (fun n => n ∈ S)).card : ℝ) / (N : ℝ) := by
  classical
  simp only [Set.partialDensity, Set.inter_univ]
  congr 1
  · congr 1
    have hset : S ∩ Set.Iio N = ↑((Finset.range N).filter (fun n => n ∈ S)) := by
      ext n
      simp [Set.mem_Iio, and_comm]
    rw [hset, Set.ncard_coe_finset]
  · simp

private lemma torusBox_hasDensity {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, Irrational (α i))
    (u v : ι → ℝ) (huv : ∀ i, 0 ≤ u i ∧ u i < v i ∧ v i ≤ 1 ∧ v i - u i < 1) :
    ∃ d : ℝ, {n : ℕ | ∀ i : ι, u i < Int.fract ((n : ℝ) * α i) ∧
      Int.fract ((n : ℝ) * α i) < v i}.HasDensity d := by
  classical
  set S : Set ℕ := {n : ℕ | ∀ i : ι, u i < Int.fract ((n : ℝ) * α i) ∧
    Int.fract ((n : ℝ) * α i) < v i}
  by_cases hempty : IsEmpty ι
  · refine ⟨1, ?_⟩
    have hSu : S = Set.univ := by
      ext n
      simp [S]
    rw [hSu]
    exact Set.HasDensity.univ
  · rw [not_isEmpty_iff] at hempty
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set k : ℕ := Fintype.card ι
    have hk_pos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := Fintype.card_pos
      positivity
    set m : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun i : ι => min (v i - u i) (1 - (v i - u i)))
    have hm_pos : 0 < m := by
      rw [Finset.lt_inf'_iff]
      intro i _
      have hi := huv i
      exact lt_min (by linarith) (by linarith)
    set δ : ℝ := min (ε / (24 * (k : ℝ))) (m / 4)
    have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ_k : 4 * (k : ℝ) * δ < ε / 3 := by
      have hle : δ ≤ ε / (24 * (k : ℝ)) := min_le_left _ _
      have : 4 * (k : ℝ) * δ ≤ 4 * (k : ℝ) * (ε / (24 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have hsimp : 4 * (k : ℝ) * (ε / (24 * (k : ℝ))) = ε / 6 := by field_simp; ring
      linarith
    have hδ_i : ∀ i : ι, 2 * δ < v i - u i ∧ 2 * δ < 1 - (v i - u i) := by
      intro i
      have hle1 : δ ≤ m / 4 := min_le_right _ _
      have hle2 : m ≤ min (v i - u i) (1 - (v i - u i)) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have h1 : m ≤ v i - u i := le_trans hle2 (min_le_left _ _)
      have h2 : m ≤ 1 - (v i - u i) := le_trans hle2 (min_le_right _ _)
      constructor <;> linarith
    let FMinus : C(ι → UnitAddCircle, ℝ) :=
      { toFun := fun z => ∏ i : ι, phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 (z i)
        continuous_toFun := continuous_finsetProd _ fun i _ =>
          (phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2).continuous.comp (continuous_apply i) }
    let FPlus : C(ι → UnitAddCircle, ℝ) :=
      { toFun := fun z => ∏ i : ι, phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 (z i)
        continuous_toFun := continuous_finsetProd _ fun i _ =>
          (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1).continuous.comp (continuous_apply i) }
    obtain ⟨LMinus, hLMinus⟩ := exists_tendsto_cesaroR α FMinus
    obtain ⟨LPlus, hLPlus⟩ := exists_tendsto_cesaroR α FPlus
    have hL_diff : LPlus - LMinus ≤ 4 * (k : ℝ) * δ := by
      have h1d : ∀ i : ι,
          Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 (((n : ℝ) * α i : ℝ) : UnitAddCircle) -
             phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 (((n : ℝ) * α i : ℝ) : UnitAddCircle)))
            atTop
            (𝓝 (∫ t : UnitAddCircle,
              (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 t -
               phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 t))) :=
        fun i => tendsto_cesaro_1d_real (hα i)
          ((phiPlus (u i) (v i) δ hδ_pos (huv i).2.1) -
           (phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2))
      have hsum_tend := tendsto_finsetSum Finset.univ fun i _ => h1d i
      have hle_N : ∀ N : ℕ, cesaroR α FPlus N - cesaroR α FMinus N ≤
          ∑ i : ι, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 (((n : ℝ) * α i : ℝ) : UnitAddCircle) -
             phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 (((n : ℝ) * α i : ℝ) : UnitAddCircle)) := by
        intro N
        dsimp [cesaroR, FPlus, FMinus]
        rw [← mul_sub, ← Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro n _
        exact prod_sub_prod_le_sum Finset.univ _ _ fun i _ =>
          phiMinus_le_phiPlus hδ_pos (huv i).2.1 (huv i).2.2.2 _
      have hlim_le : LPlus - LMinus ≤
          ∑ i : ι, ∫ t : UnitAddCircle,
            (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 t -
             phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 t) :=
        le_of_tendsto_of_tendsto (hLPlus.sub hLMinus) hsum_tend (Eventually.of_forall hle_N)
      calc LPlus - LMinus
          ≤ ∑ i : ι, ∫ t : UnitAddCircle,
              (phiPlus (u i) (v i) δ hδ_pos (huv i).2.1 t -
               phiMinus (u i) (v i) δ hδ_pos (huv i).2.2.2 t) := hlim_le
        _ ≤ ∑ _i : ι, (4 * δ) := Finset.sum_le_sum fun i _ =>
              integral_phiPlus_sub_phiMinus_le hδ_pos (hδ_i i).1 (hδ_i i).2
        _ = 4 * (k : ℝ) * δ := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, k]
              ring
    have hsand_N : ∀ N : ℕ,
        cesaroR α FMinus N ≤ S.partialDensity Set.univ N ∧
        S.partialDensity Set.univ N ≤ cesaroR α FPlus N := by
      intro N
      rw [partialDensity_eq_card_div, div_eq_inv_mul, Finset.card_filter]
      dsimp [cesaroR, FMinus, FPlus]
      push_cast
      constructor
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro n _
        have hind : (if n ∈ S then (1 : ℝ) else 0) =
            ∏ i : ι, (if u i < Int.fract ((n : ℝ) * α i) ∧
              Int.fract ((n : ℝ) * α i) < v i then (1 : ℝ) else 0) := by
          by_cases hn : n ∈ S
          · simp only [hn, ↓reduceIte]
            symm
            apply Finset.prod_eq_one
            intro i _
            simp [hn i]
          · simp only [hn, ↓reduceIte]
            dsimp [S] at hn
            push Not at hn
            obtain ⟨i, hi⟩ := hn
            symm
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            have : ¬ (u i < Int.fract ((n : ℝ) * α i) ∧ Int.fract ((n : ℝ) * α i) < v i) :=
              fun h => not_lt.mpr (hi h.1) h.2
            simp [this]
        rw [hind]
        apply Finset.prod_le_prod
        · intro i _
          exact (phiMinus_le_phiPlus hδ_pos (huv i).2.1 (huv i).2.2.2 _).1
        · intro i _
          exact (phi_sandwich hδ_pos (huv i).1 (huv i).2.1 (huv i).2.2.1 (huv i).2.2.2 _).1
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro n _
        have hind : (if n ∈ S then (1 : ℝ) else 0) =
            ∏ i : ι, (if u i < Int.fract ((n : ℝ) * α i) ∧
              Int.fract ((n : ℝ) * α i) < v i then (1 : ℝ) else 0) := by
          by_cases hn : n ∈ S
          · simp only [hn, ↓reduceIte]
            symm
            apply Finset.prod_eq_one
            intro i _
            simp [hn i]
          · simp only [hn, ↓reduceIte]
            dsimp [S] at hn
            push Not at hn
            obtain ⟨i, hi⟩ := hn
            symm
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            have : ¬ (u i < Int.fract ((n : ℝ) * α i) ∧ Int.fract ((n : ℝ) * α i) < v i) :=
              fun h => not_lt.mpr (hi h.1) h.2
            simp [this]
        rw [hind]
        apply Finset.prod_le_prod
        · intro i _
          split_ifs <;> norm_num
        · intro i _
          exact (phi_sandwich hδ_pos (huv i).1 (huv i).2.1 (huv i).2.2.1 (huv i).2.2.2 _).2
    have hM1 := Metric.tendsto_atTop.mp hLMinus (ε / 3) (by positivity)
    have hM2 := Metric.tendsto_atTop.mp hLPlus (ε / 3) (by positivity)
    obtain ⟨N₁, hN₁⟩ := hM1
    obtain ⟨N₂, hN₂⟩ := hM2
    refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
    have hm1 := hN₁ m (le_trans (le_max_left _ _) hm)
    have hm2 := hN₂ m (le_trans (le_max_right _ _) hm)
    have hn1 := hN₁ n (le_trans (le_max_left _ _) hn)
    have hn2 := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq] at hm1 hm2 hn1 hn2 ⊢
    rw [abs_lt] at hm1 hm2 hn1 hn2 ⊢
    have hsm := hsand_N m
    have hsn := hsand_N n
    constructor <;> linarith

end TorusDensity

/- ### Section 4: Density of `hTrunc`, passing `B → ∞`, and `∑' l, δ l = 1` -/

private lemma hasDensity_congr_ge_one {S T : Set ℕ} {d : ℝ}
    (h : ∀ n ≥ 1, n ∈ S ↔ n ∈ T) (hS : S.HasDensity d) : T.HasDensity d := by
  classical
  rw [Set.HasDensity] at hS ⊢
  have hdiff : Tendsto (fun N : ℕ => T.partialDensity Set.univ N - S.partialDensity Set.univ N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ N : ℕ, ‖T.partialDensity Set.univ N - S.partialDensity Set.univ N‖ ≤
        (1 : ℝ) / (N : ℝ) := by
      intro N
      by_cases hN : N = 0
      · simp [Set.partialDensity, hN]
      · rw [partialDensity_eq_card_div, partialDensity_eq_card_div, ← sub_div, Real.norm_eq_abs,
          abs_div, Nat.abs_cast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        have h1 : ((Finset.range N).filter (fun n => n ∈ T)).card ≤
            ((Finset.range N).filter (fun n => n ∈ S)).card + 1 := by
          have hsub : (Finset.range N).filter (fun n => n ∈ T) ⊆
              insert 0 ((Finset.range N).filter (fun n => n ∈ S)) := by
            intro n hn
            rw [Finset.mem_filter] at hn
            rcases Nat.eq_zero_or_pos n with rfl | hpos
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (Finset.mem_filter.mpr ⟨hn.1, (h n hpos).mpr hn.2⟩)
          calc _ ≤ (insert 0 ((Finset.range N).filter (fun n => n ∈ S))).card :=
                Finset.card_le_card hsub
            _ ≤ _ + 1 := Finset.card_insert_le _ _
        have h2 : ((Finset.range N).filter (fun n => n ∈ S)).card ≤
            ((Finset.range N).filter (fun n => n ∈ T)).card + 1 := by
          have hsub : (Finset.range N).filter (fun n => n ∈ S) ⊆
              insert 0 ((Finset.range N).filter (fun n => n ∈ T)) := by
            intro n hn
            rw [Finset.mem_filter] at hn
            rcases Nat.eq_zero_or_pos n with rfl | hpos
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (Finset.mem_filter.mpr ⟨hn.1, (h n hpos).mp hn.2⟩)
          calc _ ≤ (insert 0 ((Finset.range N).filter (fun n => n ∈ T))).card :=
                Finset.card_le_card hsub
            _ ≤ _ + 1 := Finset.card_insert_le _ _
        have h1R : (((Finset.range N).filter (fun n => n ∈ T)).card : ℝ) ≤
            (((Finset.range N).filter (fun n => n ∈ S)).card : ℝ) + 1 := by exact_mod_cast h1
        have h2R : (((Finset.range N).filter (fun n => n ∈ S)).card : ℝ) ≤
            (((Finset.range N).filter (fun n => n ∈ T)).card : ℝ) + 1 := by exact_mod_cast h2
        rw [abs_le]
        constructor <;> linarith
    exact squeeze_zero (fun _ => norm_nonneg _) hbd tendsto_one_div_atTop_nhds_zero_nat
  have := hS.add hdiff
  simpa using this

private lemma hasDensity_biUnion_finset {α : Type*} (I : Finset α)
    (F : α → Set ℕ) (d : α → ℝ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (F i) (F j))
    (hdens : ∀ i ∈ I, (F i).HasDensity (d i)) :
    (⋃ i ∈ I, F i).HasDensity (∑ i ∈ I, d i) := by
  classical
  rw [Set.HasDensity]
  have hsum := tendsto_finsetSum I fun i hi => hdens i hi
  refine hsum.congr fun N => ?_
  simp only [partialDensity_eq_card_div, ← Finset.sum_div]
  congr 1
  norm_cast
  have hEq : (Finset.range N).filter (fun n => n ∈ ⋃ i ∈ I, F i) =
      I.biUnion (fun i => (Finset.range N).filter (fun n => n ∈ F i)) := by
    ext n
    simp only [Finset.mem_filter, Set.mem_iUnion, Finset.mem_biUnion]
    tauto
  rw [hEq, Finset.card_biUnion]
  intro i hi j hj hij
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro n hni hnj
  rw [Finset.mem_filter] at hni hnj
  exact Set.disjoint_left.mp (hdisj i hi j hj hij) hni.2 hnj.2

private lemma exists_hasDensity_hTrunc (B l : ℕ) (hB : 1 ≤ B) :
    ∃ d : ℝ, {n : ℕ | hTrunc B n = l}.HasDensity d := by
  classical
  set ℬ : Finset ℕ := (Finset.Icc 2 B).filter Squarefree
  let F : Finset ℕ → Set ℕ := fun J =>
    {n : ℕ | ∀ b : {x // x ∈ ℬ},
      (if (b : ℕ) ∈ J then 1 - alpha b else 0) < Int.fract ((n : ℝ) * alpha b) ∧
      Int.fract ((n : ℝ) * alpha b) < (if (b : ℕ) ∈ J then 1 else 1 - alpha b)}
  have hF_dens : ∀ J : Finset ℕ, ∃ d : ℝ, (F J).HasDensity d := by
    intro J
    apply torusBox_hasDensity (fun b : {x // x ∈ ℬ} => alpha b)
    · intro ⟨b, hb⟩
      dsimp only
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      exact irrational_alpha hb.2 (by omega)
    · intro ⟨b, hb⟩
      dsimp only
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      have hpos : 0 < alpha b := alpha_pos (by omega)
      have hlt : alpha b < 1 := alpha_lt_one (by omega)
      split_ifs <;> refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  let dF : Finset ℕ → ℝ := fun J => Classical.choose (hF_dens J)
  have hdF : ∀ J : Finset ℕ, (F J).HasDensity (dF J) := fun J => Classical.choose_spec (hF_dens J)
  set I : Finset (Finset ℕ) := ℬ.powerset.filter (fun J => J.card + 1 = l)
  refine ⟨∑ J ∈ I, dF J, ?_⟩
  have hUnion : (⋃ J ∈ I, F J).HasDensity (∑ J ∈ I, dF J) := by
    apply hasDensity_biUnion_finset I F dF _ (fun J _ => hdF J)
    intro J₁ hJ₁ J₂ hJ₂ hne
    rw [Set.disjoint_left]
    intro n hn₁ hn₂
    rw [Finset.mem_filter, Finset.mem_powerset] at hJ₁ hJ₂
    apply hne
    ext b
    by_cases hb : b ∈ ℬ
    · have h1 := hn₁ ⟨b, hb⟩
      have h2 := hn₂ ⟨b, hb⟩
      dsimp at h1 h2
      by_cases hb1 : b ∈ J₁ <;> by_cases hb2 : b ∈ J₂
      · simp [hb1, hb2]
      · simp only [hb1, ↓reduceIte, hb2] at h1 h2
        linarith
      · simp only [hb1, ↓reduceIte, hb2] at h1 h2
        linarith
      · simp [hb1, hb2]
    · have h1 : b ∉ J₁ := fun h => hb (hJ₁.1 h)
      have h2 : b ∉ J₂ := fun h => hb (hJ₂.1 h)
      simp [h1, h2]
  refine hasDensity_congr_ge_one (fun n hn => ?_) hUnion
  have hsplit : hTrunc B n = (ℬ.filter (fun b => E b n)).card + 1 := by
    unfold hTrunc
    have hEq : (Finset.Icc 1 B).filter (fun b => Squarefree b ∧ E b n) =
        insert 1 (ℬ.filter (fun b => E b n)) := by
      ext b
      simp only [ℬ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
      constructor
      · intro ⟨⟨hb1, hbB⟩, hsq, hE⟩
        rcases eq_or_lt_of_le hb1 with rfl | hgt
        · left; rfl
        · right; exact ⟨⟨⟨by omega, hbB⟩, hsq⟩, hE⟩
      · rintro (rfl | ⟨⟨⟨hb2, hbB⟩, hsq⟩, hE⟩)
        · exact ⟨⟨le_rfl, hB⟩, squarefree_one, E_one hn⟩
        · exact ⟨⟨by omega, hbB⟩, hsq, hE⟩
    have h1not : 1 ∉ ℬ.filter (fun b => E b n) := by
      simp [ℬ]
    rw [hEq, Finset.card_insert_of_notMem h1not]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, I, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨J, ⟨hJsub, hJcard⟩, hnJ⟩
    have hJeq : ℬ.filter (fun b => E b n) = J := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hb, hE⟩
        have hb' := hb
        rw [Finset.mem_filter, Finset.mem_Icc] at hb'
        have hgt := (E_iff_fract_gt hb'.2 (by omega) hn).mp hE
        have hspec := hnJ ⟨b, hb⟩
        by_contra hnot
        simp only [hnot, ↓reduceIte] at hspec
        linarith
      · intro hbJ
        have hb : b ∈ ℬ := hJsub hbJ
        have hb' := hb
        rw [Finset.mem_filter, Finset.mem_Icc] at hb'
        have hspec := hnJ ⟨b, hb⟩
        simp only [hbJ, ↓reduceIte] at hspec
        exact ⟨hb, (E_iff_fract_gt hb'.2 (by omega) hn).mpr hspec.1⟩
    rw [hsplit, hJeq, hJcard]
  · intro hl
    refine ⟨ℬ.filter (fun b => E b n), ⟨Finset.filter_subset _ _, by omega⟩, ?_⟩
    intro ⟨b, hb⟩
    have hb' := hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb'
    by_cases hE : E b n
    · have hmem : b ∈ ℬ.filter (fun b => E b n) := Finset.mem_filter.mpr ⟨hb, hE⟩
      simp only [hmem, ↓reduceIte]
      exact ⟨(E_iff_fract_gt hb'.2 (by omega) hn).mp hE, Int.fract_lt_one _⟩
    · have hnot : b ∉ ℬ.filter (fun b => E b n) := by
        simp [hE]
      simp only [hnot, ↓reduceIte]
      exact (not_E_iff_fract_lt hb'.2 (by omega) hn).mp hE

private lemma abs_partialDensity_h_sub_hTrunc_le (B l N : ℕ) (hN : 1 ≤ N) :
    |({n : ℕ | Erdos942.erdos_942.h n = l}).partialDensity Set.univ N -
      ({n : ℕ | hTrunc B n = l}).partialDensity Set.univ N| ≤
      (1 : ℝ) / (N : ℝ) + tailSum B := by
  classical
  rw [partialDensity_eq_card_div, partialDensity_eq_card_div, ← sub_div, abs_div, Nat.abs_cast]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [div_le_iff₀ hN_pos]
  set A := (Finset.range N).filter (fun n => Erdos942.erdos_942.h n = l)
  set C := (Finset.range N).filter (fun n => hTrunc B n = l)
  set D := (Finset.Ico 1 N).filter (fun n => hTrunc B n < Erdos942.erdos_942.h n)
  have hAC : A.card ≤ C.card + (D.card + 1) := by
    have hsub : A ⊆ C ∪ (D ∪ {0}) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · by_cases heq : hTrunc B n = Erdos942.erdos_942.h n
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, by omega⟩)
        · have hlt : hTrunc B n < Erdos942.erdos_942.h n :=
            lt_of_le_of_ne (hTrunc_le_h hpos) heq
          exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, hn.1⟩, hlt⟩))
    calc A.card ≤ (C ∪ (D ∪ {0})).card := Finset.card_le_card hsub
      _ ≤ C.card + (D ∪ {0}).card := Finset.card_union_le _ _
      _ ≤ C.card + (D.card + ({0} : Finset ℕ).card) := by linarith [Finset.card_union_le D {0}]
      _ = C.card + (D.card + 1) := by simp
  have hCA : C.card ≤ A.card + (D.card + 1) := by
    have hsub : C ⊆ A ∪ (D ∪ {0}) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · by_cases heq : hTrunc B n = Erdos942.erdos_942.h n
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, by omega⟩)
        · have hlt : hTrunc B n < Erdos942.erdos_942.h n :=
            lt_of_le_of_ne (hTrunc_le_h hpos) heq
          exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, hn.1⟩, hlt⟩))
    calc C.card ≤ (A ∪ (D ∪ {0})).card := Finset.card_le_card hsub
      _ ≤ A.card + (D ∪ {0}).card := Finset.card_union_le _ _
      _ ≤ A.card + (D.card + ({0} : Finset ℕ).card) := by linarith [Finset.card_union_le D {0}]
      _ = A.card + (D.card + 1) := by simp
  have hD_le : (D.card : ℝ) ≤ (N : ℝ) * tailSum B := by
    have hD1 : D.card ≤ ∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n - hTrunc B n) := by
      calc D.card = ∑ _n ∈ D, 1 := by simp
        _ ≤ ∑ n ∈ D, (Erdos942.erdos_942.h n - hTrunc B n) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_filter] at hn
            omega
        _ ≤ ∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n - hTrunc B n) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    calc (D.card : ℝ)
        ≤ ((∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n - hTrunc B n) : ℕ) : ℝ) := by
          exact_mod_cast hD1
      _ = ∑ n ∈ Finset.Ico 1 N, ((Erdos942.erdos_942.h n - hTrunc B n : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ (N : ℝ) * tailSum B := sum_h_sub_hTrunc_le B N
  have hAC_R : (A.card : ℝ) ≤ (C.card : ℝ) + (D.card : ℝ) + 1 := by exact_mod_cast hAC
  have hCA_R : (C.card : ℝ) ≤ (A.card : ℝ) + (D.card : ℝ) + 1 := by exact_mod_cast hCA
  have hrhs : ((1 : ℝ) / (N : ℝ) + tailSum B) * (N : ℝ) = 1 + (N : ℝ) * tailSum B := by
    field_simp
  have hA_eq : ∀ inst : DecidablePred (fun n => n ∈ {n | Erdos942.erdos_942.h n = l}),
      (@Finset.filter ℕ _ inst (Finset.range N)).card = A.card := fun _ => by
    congr 1; ext n; simp [A]
  have hC_eq : ∀ inst : DecidablePred (fun n => n ∈ {n | hTrunc B n = l}),
      (@Finset.filter ℕ _ inst (Finset.range N)).card = C.card := fun _ => by
    congr 1; ext n; simp [C]
  rw [hA_eq, hC_eq, hrhs, abs_le]
  constructor <;> linarith

private lemma exists_hasDensity_h (l : ℕ) :
    ∃ d : ℝ, {n : ℕ | Erdos942.erdos_942.h n = l}.HasDensity d := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have htail := Metric.tendsto_atTop.mp tendsto_tailSum_zero (ε / 4) (by positivity)
  obtain ⟨B₀, hB₀⟩ := htail
  set B : ℕ := max B₀ 1
  have hB_tail : tailSum B < ε / 4 := by
    have h := hB₀ B (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  obtain ⟨dB, hdB⟩ := exists_hasDensity_hTrunc B l (le_max_right _ _)
  have hcauchy := Metric.cauchySeq_iff.mp hdB.cauchySeq (ε / 4) (by positivity)
  obtain ⟨N₀, hN₀⟩ := hcauchy
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 / ε)
  refine ⟨max (max N₀ N₁) 1, fun m hm n hn => ?_⟩
  have hm_pos : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hn_pos : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hm0 : N₀ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hm1 : (1 : ℝ) / (m : ℝ) < ε / 8 := by
    have hmR : (8 / ε : ℝ) < (m : ℝ) := lt_of_lt_of_le hN₁
      (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm)
    have hm_posR : (0 : ℝ) < (m : ℝ) := by positivity
    rw [div_lt_div_iff₀ hm_posR (by norm_num)]
    have : 8 < (m : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hmR
    linarith
  have hn1 : (1 : ℝ) / (n : ℝ) < ε / 8 := by
    have hnR : (8 / ε : ℝ) < (n : ℝ) := lt_of_lt_of_le hN₁
      (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have hn_posR : (0 : ℝ) < (n : ℝ) := by positivity
    rw [div_lt_div_iff₀ hn_posR (by norm_num)]
    have : 8 < (n : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hnR
    linarith
  have h1 : dist ({n : ℕ | Erdos942.erdos_942.h n = l}.partialDensity Set.univ m)
      ({n : ℕ | hTrunc B n = l}.partialDensity Set.univ m) ≤ (1 : ℝ) / (m : ℝ) + tailSum B := by
    rw [Real.dist_eq]
    exact abs_partialDensity_h_sub_hTrunc_le B l m hm_pos
  have h2 := hN₀ m hm0 n hn0
  have h3 : dist ({n : ℕ | hTrunc B n = l}.partialDensity Set.univ n)
      ({n : ℕ | Erdos942.erdos_942.h n = l}.partialDensity Set.univ n) ≤
      (1 : ℝ) / (n : ℝ) + tailSum B := by
    rw [_root_.dist_comm, Real.dist_eq]
    exact abs_partialDensity_h_sub_hTrunc_le B l n hn_pos
  linarith [dist_triangle4
    ({n : ℕ | Erdos942.erdos_942.h n = l}.partialDensity Set.univ m)
    ({n : ℕ | hTrunc B n = l}.partialDensity Set.univ m)
    ({n : ℕ | hTrunc B n = l}.partialDensity Set.univ n)
    ({n : ℕ | Erdos942.erdos_942.h n = l}.partialDensity Set.univ n)]

private lemma main_density :
    ∃ δ : ℕ → ℝ, ∀ l, {n | Erdos942.erdos_942.h n = l}.HasDensity (δ l) ∧
    ∑' l, δ l = 1 := by
  classical
  let δ : ℕ → ℝ := fun l => Classical.choose (exists_hasDensity_h l)
  have hδ : ∀ l, {n | Erdos942.erdos_942.h n = l}.HasDensity (δ l) :=
    fun l => Classical.choose_spec (exists_hasDensity_h l)
  have hδ_nonneg : ∀ l, 0 ≤ δ l := fun l => Set.HasDensity.nonneg (hδ l)
  have htsum : ∑' l, δ l = 1 := by
    apply HasSum.tsum_eq
    rw [hasSum_iff_tendsto_nat_of_nonneg hδ_nonneg]
    set C : ℝ := tailSum 0
    have hC_nonneg : 0 ≤ C := tsum_nonneg fun k => by positivity
    have hbounds : ∀ L : ℕ, 2 ≤ L →
        1 - C / (L : ℝ) ≤ ∑ l ∈ Finset.range L, δ l ∧ ∑ l ∈ Finset.range L, δ l ≤ 1 := by
      intro L hL
      have hsum_tend : Tendsto (fun N : ℕ =>
          ∑ l ∈ Finset.range L,
            ({n : ℕ | Erdos942.erdos_942.h n = l}).partialDensity Set.univ N)
          atTop (𝓝 (∑ l ∈ Finset.range L, δ l)) :=
        tendsto_finsetSum _ fun l _ => hδ l
      have hN_bounds : ∀ N : ℕ, 1 ≤ N →
          1 - C / (L : ℝ) ≤
            ∑ l ∈ Finset.range L,
              ({n : ℕ | Erdos942.erdos_942.h n = l}).partialDensity Set.univ N ∧
          ∑ l ∈ Finset.range L,
            ({n : ℕ | Erdos942.erdos_942.h n = l}).partialDensity Set.univ N ≤ 1 := by
        intro N hN
        have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
        have hL_pos : (0 : ℝ) < (L : ℝ) := by positivity
        have hpart : ∑ l ∈ Finset.range L,
            ((Finset.range N).filter (fun n => Erdos942.erdos_942.h n = l)).card +
            ((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card = N := by
          have hdisj_union : (Finset.range N).filter (fun n => Erdos942.erdos_942.h n < L) =
              (Finset.range L).biUnion (fun l =>
                (Finset.range N).filter (fun n => Erdos942.erdos_942.h n = l)) := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
            constructor
            · intro ⟨hn, hlt⟩; exact ⟨Erdos942.erdos_942.h n, hlt, hn, rfl⟩
            · rintro ⟨l, hl, hn, rfl⟩; exact ⟨hn, hl⟩
          have hcard_lt : ((Finset.range N).filter (fun n => Erdos942.erdos_942.h n < L)).card =
              ∑ l ∈ Finset.range L,
                ((Finset.range N).filter (fun n => Erdos942.erdos_942.h n = l)).card := by
            rw [hdisj_union, Finset.card_biUnion]
            intro l₁ _ l₂ _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro n h1 h2
            rw [Finset.mem_filter] at h1 h2
            exact hne (h1.2.symm.trans h2.2)
          rw [← hcard_lt]
          have hcompl : ((Finset.range N).filter (fun n => Erdos942.erdos_942.h n < L)) ∪
              ((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)) = Finset.range N := by
            ext n
            simp only [Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro h
              rcases lt_or_ge (Erdos942.erdos_942.h n) L with hlt | hge
              · exact Or.inl ⟨h, hlt⟩
              · exact Or.inr ⟨h, hge⟩
          have hdisj : Disjoint ((Finset.range N).filter (fun n => Erdos942.erdos_942.h n < L))
              ((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)) := by
            rw [Finset.disjoint_left]
            intro n h1 h2
            rw [Finset.mem_filter] at h1 h2
            omega
          rw [← Finset.card_union_of_disjoint hdisj, hcompl, Finset.card_range]
        have hmarkov : (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) ≤
            (N : ℝ) * C / (L : ℝ) := by
          rw [le_div_iff₀ hL_pos]
          have hsub_ico : (Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n) ⊆
              Finset.Ico 1 N := by
            intro n hn
            rw [Finset.mem_filter, Finset.mem_range] at hn
            rw [Finset.mem_Ico]
            refine ⟨?_, hn.1⟩
            rcases Nat.eq_zero_or_pos n with rfl | hpos
            · rw [h_zero] at hn; omega
            · exact hpos
          have h1 : ((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card * L ≤
              ∑ n ∈ Finset.Ico 1 N, Erdos942.erdos_942.h n := by
            calc ((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card * L
                = ∑ _n ∈ (Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n), L := by
                  simp
              _ ≤ ∑ n ∈ (Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n),
                    Erdos942.erdos_942.h n := by
                  apply Finset.sum_le_sum
                  intro n hn
                  exact (Finset.mem_filter.mp hn).2
              _ ≤ ∑ n ∈ Finset.Ico 1 N, Erdos942.erdos_942.h n :=
                  Finset.sum_le_sum_of_subset hsub_ico
          have h0 : ∀ n, hTrunc 0 n = 0 := by
            intro n
            simp [hTrunc]
          have h2 : (∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n : ℝ)) ≤ (N : ℝ) * C := by
            have := sum_h_sub_hTrunc_le 0 N
            simpa [h0, C] using this
          calc (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) * (L : ℝ)
              ≤ ((∑ n ∈ Finset.Ico 1 N, Erdos942.erdos_942.h n : ℕ) : ℝ) := by
                exact_mod_cast h1
            _ = ∑ n ∈ Finset.Ico 1 N, (Erdos942.erdos_942.h n : ℝ) := by push_cast; rfl
            _ ≤ (N : ℝ) * C := h2
        have hsum_eq : ∑ l ∈ Finset.range L,
            ({n : ℕ | Erdos942.erdos_942.h n = l}).partialDensity Set.univ N =
            1 - (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) /
              (N : ℝ) := by
          simp_rw [partialDensity_eq_card_div]
          rw [← Finset.sum_div]
          have hpartR : (∑ l ∈ Finset.range L,
              (((Finset.range N).filter (fun n => Erdos942.erdos_942.h n = l)).card : ℝ)) +
              (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) =
              (N : ℝ) := by exact_mod_cast hpart
          simp only [Set.mem_ofPred_eq]
          field_simp
          linarith
        rw [hsum_eq]
        constructor
        · have : (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) /
              (N : ℝ) ≤ C / (L : ℝ) := by
            rw [div_le_iff₀ hN_pos]
            have : C / (L : ℝ) * (N : ℝ) = (N : ℝ) * C / (L : ℝ) := by ring
            rw [this]
            exact hmarkov
          linarith
        · have : 0 ≤ (((Finset.range N).filter (fun n => L ≤ Erdos942.erdos_942.h n)).card : ℝ) /
              (N : ℝ) := by positivity
          linarith
      exact ⟨ge_of_tendsto hsum_tend
          (eventually_atTop.mpr ⟨1, fun N hN => (hN_bounds N hN).1⟩),
        le_of_tendsto hsum_tend
          (eventually_atTop.mpr ⟨1, fun N hN => (hN_bounds N hN).2⟩)⟩
    have hlo : Tendsto (fun L : ℕ => 1 - C / (L : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat C)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
      (eventually_atTop.mpr ⟨2, fun L hL => (hbounds L hL).1⟩)
      (eventually_atTop.mpr ⟨2, fun L hL => (hbounds L hL).2⟩)
  exact ⟨δ, fun l => ⟨hδ l, htsum⟩⟩

end Erdos942DensityProof

-- Problem: Erdős Problem 942 — density
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/942.lean:60 (declaration Erdos942.erdos_942.variants.density)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos942.erdos_942.variants.density := by
  exact Erdos942DensityProof.main_density
