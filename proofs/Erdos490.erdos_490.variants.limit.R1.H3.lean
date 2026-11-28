import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1
import Mathlib.NumberTheory.Chebyshev

open Finset Filter ArithmeticFunction

namespace Erdos490H3

private lemma sum_log_Icc (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, Real.log (m : ℝ) = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring

private lemma sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, (Real.log (n : ℝ) - Real.log (m : ℝ)) ≤ (n : ℝ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    sum_log_Icc]
  have hterm : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) (n + 1)
    have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
    have hle : (n : ℝ) ^ n / (n.factorial : ℝ) ≤
        ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k / (k.factorial : ℝ) :=
      Finset.single_le_sum (f := fun k => (n : ℝ) ^ k / (k.factorial : ℝ))
        (fun k _ => by positivity) hmem
    exact hle.trans hsum
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hlog := Real.log_le_log (by positivity) hterm
  rw [Real.log_div (by positivity) hfac_pos.ne', Real.log_pow, Real.log_exp] at hlog
  exact hlog

private lemma harmonic_le_one_add_log (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div hk_pos.ne' hk1_pos.ne'] at h1
      have h2 : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -((1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp [hk1_pos.ne']; ring
      linarith
    linarith

private lemma card_mul_log_le {n : ℕ} (hn : 2 ≤ n) {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 n) (h1 : 1 ∈ S)
    (hdiv : ∀ m ∈ S, ∀ d : ℕ, d ∣ m → d ≠ 0 → d ∈ S) :
    (S.card : ℝ) * Real.log (n : ℝ) ≤
      (Real.log 4 + 5) * (n : ℝ) * ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
  have hdiff : (S.card : ℝ) * Real.log (n : ℝ) - ∑ m ∈ S, Real.log (m : ℝ) ≤ (n : ℝ) := by
    have heq : (S.card : ℝ) * Real.log (n : ℝ) - ∑ m ∈ S, Real.log (m : ℝ) =
        ∑ m ∈ S, (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [heq]
    calc ∑ m ∈ S, (Real.log (n : ℝ) - Real.log (m : ℝ))
        ≤ ∑ m ∈ Finset.Icc 1 n, (Real.log (n : ℝ) - Real.log (m : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro m hm _
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
          have : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
            Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmn)
          linarith
      _ ≤ (n : ℝ) := sum_log_div_le n (by omega)
  have hsum_log : ∑ m ∈ S, Real.log (m : ℝ) ≤
      (Real.log 4 + 4) * (n : ℝ) * ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    have hvm : ∑ m ∈ S, Real.log (m : ℝ) = ∑ m ∈ S, ∑ k ∈ m.divisors, Λ k := by
      apply Finset.sum_congr rfl
      intro m _
      exact (ArithmeticFunction.vonMangoldt_sum).symm
    rw [hvm, Finset.sum_sigma']
    let φ : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun x => ⟨x.1 / x.2, x.2⟩
    have hφ_sub : (S.sigma (fun m => m.divisors)).image φ ⊆
        S.sigma (fun d => Finset.Ioc 0 (n / d)) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hx
      rcases hx with ⟨hmS, ⟨hkd, hm0⟩⟩
      have hk0 : x.2 ≠ 0 := fun h => hm0 (by simpa [h] using hkd)
      have hq_dvd : x.1 / x.2 ∣ x.1 := Nat.div_dvd_of_dvd hkd
      have hq0 : x.1 / x.2 ≠ 0 := by
        intro hq
        have := Nat.div_mul_cancel hkd
        rw [hq, zero_mul] at this
        exact hm0 this.symm
      have hqS : x.1 / x.2 ∈ S := hdiv x.1 hmS (x.1 / x.2) hq_dvd hq0
      have hm_le : x.1 ≤ n := (Finset.mem_Icc.mp (hsub hmS)).2
      have hk_le : x.2 ≤ n / (x.1 / x.2) := by
        rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq0)]
        rw [mul_comm, Nat.div_mul_cancel hkd]
        exact hm_le
      exact Finset.mem_sigma.mpr ⟨hqS, Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hk0, hk_le⟩⟩
    have hφ_inj : Set.InjOn φ (S.sigma (fun m => m.divisors) : Set (Σ _ : ℕ, ℕ)) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_sigma, Nat.mem_divisors] at hx hy
      have h2 : x.2 = y.2 := congrArg Sigma.snd hxy
      have h1 : x.1 / x.2 = y.1 / y.2 := congrArg Sigma.fst hxy
      have h1' : x.1 = y.1 := by
        rw [← Nat.div_mul_cancel hx.2.1, ← Nat.div_mul_cancel hy.2.1, h1, h2]
      exact Sigma.ext h1' (heq_of_eq h2)
    have hle_sig : ∑ x ∈ S.sigma (fun m => m.divisors), Λ x.2 ≤
        ∑ y ∈ S.sigma (fun d => Finset.Ioc 0 (n / d)), Λ y.2 := by
      calc ∑ x ∈ S.sigma (fun m => m.divisors), Λ x.2
          = ∑ y ∈ (S.sigma (fun m => m.divisors)).image φ, Λ y.2 :=
            (Finset.sum_image (f := fun y : (Σ _ : ℕ, ℕ) => Λ y.2) hφ_inj).symm
        _ ≤ ∑ y ∈ S.sigma (fun d => Finset.Ioc 0 (n / d)), Λ y.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hφ_sub
              (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    refine hle_sig.trans ?_
    rw [Finset.sum_sigma]
    calc ∑ d ∈ S, ∑ k ∈ Finset.Ioc 0 (n / d), Λ k
        ≤ ∑ d ∈ S, (Real.log 4 + 4) * ((n : ℝ) / (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd_pos : 0 < d := (Finset.mem_Icc.mp (hsub hd)).1
          have hfloor : ⌊(n : ℝ) / (d : ℝ)⌋₊ = n / d := by
            rw [Nat.floor_eq_iff (by positivity)]
            have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
            constructor
            · rw [le_div_iff₀ hd_posR]
              exact_mod_cast Nat.div_mul_le_self n d
            · rw [div_lt_iff₀ hd_posR]
              have h1 : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
              have h2 : n % d < d := Nat.mod_lt n hd_pos
              have h3 : n < (n / d + 1) * d := by nlinarith
              exact_mod_cast h3
          have hpsi : ∑ k ∈ Finset.Ioc 0 (n / d), Λ k = Chebyshev.psi ((n : ℝ) / (d : ℝ)) := by
            rw [Chebyshev.psi, hfloor]
          rw [hpsi]
          exact Chebyshev.psi_le_const_mul_self (by positivity)
      _ = (Real.log 4 + 4) * (n : ℝ) * ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
  have hone_le : (1 : ℝ) ≤ ∑ d ∈ S, (1 : ℝ) / (d : ℝ) := by
    have := Finset.single_le_sum (f := fun d : ℕ => (1 : ℝ) / (d : ℝ))
      (fun d _ => by positivity) h1
    simpa using this
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

end Erdos490H3

theorem OMA.solution : OMA.R_Erdos490_erdos_490_variants_limit_R1.H3 := by
  classical
  intro Y K
  refine ⟨(K : ℝ) ^ 2 * (4 * (Real.log 4 + 5) ^ 2), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  intro A B hA hB hsep hcof
  let isPA : ℕ → Prop := fun p => p.Prime ∧ Y ≤ p ∧ ∃ a ∈ A, p ∣ a
  let isPB : ℕ → Prop := fun p => p.Prime ∧ Y ≤ p ∧ ∃ b ∈ B, p ∣ b
  have hdisj : ∀ p, isPA p → ¬ isPB p := by
    rintro p ⟨hp, hYp, a, ha, hpa⟩ ⟨_, _, b, hb, hpb⟩
    exact hsep a ha b hb p hp hYp hpa hpb
  let SA : Finset ℕ := (Finset.Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → isPA p)
  let SB : Finset ℕ := (Finset.Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → isPB p)
  have hSA_sub : SA ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  have hSB_sub : SB ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  have h1SA : 1 ∈ SA := by
    simp only [SA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, fun p hp h => absurd (Nat.dvd_one.mp h) hp.ne_one⟩
  have h1SB : 1 ∈ SB := by
    simp only [SB, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, fun p hp h => absurd (Nat.dvd_one.mp h) hp.ne_one⟩
  have hSA_div : ∀ m ∈ SA, ∀ d : ℕ, d ∣ m → d ≠ 0 → d ∈ SA := by
    intro m hm d hdm hd0
    simp only [SA, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨Nat.pos_of_ne_zero hd0, (Nat.le_of_dvd (by omega) hdm).trans hm.1.2⟩, ?_⟩
    intro p hp hpd
    exact hm.2 p hp (hpd.trans hdm)
  have hSB_div : ∀ m ∈ SB, ∀ d : ℕ, d ∣ m → d ≠ 0 → d ∈ SB := by
    intro m hm d hdm hd0
    simp only [SB, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨Nat.pos_of_ne_zero hd0, (Nat.le_of_dvd (by omega) hdm).trans hm.1.2⟩, ?_⟩
    intro p hp hpd
    exact hm.2 p hp (hpd.trans hdm)
  have hA_card : A.card ≤ K * SA.card := by
    have hsub : A ⊆ (Finset.Icc 1 K).biUnion (fun u => SA.image (fun m => u * m)) := by
      intro a ha
      obtain ⟨u, huK, hua, hup⟩ := hcof a (Finset.mem_union_left _ ha)
      have ha_pos : 1 ≤ a := (Finset.mem_Icc.mp (hA ha)).1
      have ha_le : a ≤ n := (Finset.mem_Icc.mp (hA ha)).2
      have hu_pos : 1 ≤ u := by
        by_contra h0
        have hu0 : u = 0 := by omega
        rw [hu0, zero_dvd_iff] at hua
        omega
      have hq_mem : a / u ∈ SA := by
        simp only [SA, Finset.mem_filter, Finset.mem_Icc]
        have hq_pos : 1 ≤ a / u := Nat.div_pos (Nat.le_of_dvd (by omega) hua) (by omega)
        have hq_le : a / u ≤ n := (Nat.div_le_self a u).trans ha_le
        refine ⟨⟨hq_pos, hq_le⟩, fun p hp hpd => ?_⟩
        exact ⟨hp, hup p hp hpd, a, ha, hpd.trans (Nat.div_dvd_of_dvd hua)⟩
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_Icc.mpr ⟨hu_pos, huK⟩,
        Finset.mem_image.mpr ⟨a / u, hq_mem, Nat.mul_div_cancel' hua⟩⟩
    calc A.card ≤ ((Finset.Icc 1 K).biUnion (fun u => SA.image (fun m => u * m))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Finset.Icc 1 K, (SA.image (fun m => u * m)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ Finset.Icc 1 K, SA.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = K * SA.card := by simp
  have hB_card : B.card ≤ K * SB.card := by
    have hsub : B ⊆ (Finset.Icc 1 K).biUnion (fun u => SB.image (fun m => u * m)) := by
      intro b hb
      obtain ⟨u, huK, hub, hup⟩ := hcof b (Finset.mem_union_right _ hb)
      have hb_pos : 1 ≤ b := (Finset.mem_Icc.mp (hB hb)).1
      have hb_le : b ≤ n := (Finset.mem_Icc.mp (hB hb)).2
      have hu_pos : 1 ≤ u := by
        by_contra h0
        have hu0 : u = 0 := by omega
        rw [hu0, zero_dvd_iff] at hub
        omega
      have hq_mem : b / u ∈ SB := by
        simp only [SB, Finset.mem_filter, Finset.mem_Icc]
        have hq_pos : 1 ≤ b / u := Nat.div_pos (Nat.le_of_dvd (by omega) hub) (by omega)
        have hq_le : b / u ≤ n := (Nat.div_le_self b u).trans hb_le
        refine ⟨⟨hq_pos, hq_le⟩, fun p hp hpd => ?_⟩
        exact ⟨hp, hup p hp hpd, b, hb, hpd.trans (Nat.div_dvd_of_dvd hub)⟩
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_Icc.mpr ⟨hu_pos, huK⟩,
        Finset.mem_image.mpr ⟨b / u, hq_mem, Nat.mul_div_cancel' hub⟩⟩
    calc B.card ≤ ((Finset.Icc 1 K).biUnion (fun u => SB.image (fun m => u * m))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ Finset.Icc 1 K, (SB.image (fun m => u * m)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ Finset.Icc 1 K, SB.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = K * SB.card := by simp
  have hcop : ∀ a ∈ SA, ∀ b ∈ SB, Nat.Coprime a b := by
    intro a ha b hb
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_left a b)
    have hpb : p ∣ b := hpg.trans (Nat.gcd_dvd_right a b)
    exact hdisj p ((Finset.mem_filter.mp ha).2 p hp hpa) ((Finset.mem_filter.mp hb).2 p hp hpb)
  have hprod_recip : (∑ a ∈ SA, (1 : ℝ) / (a : ℝ)) * (∑ b ∈ SB, (1 : ℝ) / (b : ℝ)) ≤
      4 * Real.log (n : ℝ) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hle_harm : ∑ x ∈ SA ×ˢ SB, ((1 : ℝ) / (x.1 : ℝ)) * ((1 : ℝ) / (x.2 : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 (n * n), (1 : ℝ) / (m : ℝ) := by
      let ψ : ℕ × ℕ → ℕ := fun x => x.1 * x.2
      have hψ_sub : (SA ×ˢ SB).image ψ ⊆ Finset.Icc 1 (n * n) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨x, hx, rfl⟩
        rcases Finset.mem_product.mp hx with ⟨h1, h2⟩
        have h1' := Finset.mem_Icc.mp (hSA_sub h1)
        have h2' := Finset.mem_Icc.mp (hSB_sub h2)
        exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h1'.1 h2'.1, Nat.mul_le_mul h1'.2 h2'.2⟩
      have hψ_inj : Set.InjOn ψ ↑(SA ×ˢ SB) := by
        intro x hx y hy hxy
        rcases Finset.mem_product.mp (Finset.mem_coe.mp hx) with ⟨hx1, hx2⟩
        rcases Finset.mem_product.mp (Finset.mem_coe.mp hy) with ⟨hy1, hy2⟩
        have h12 : Nat.Coprime x.1 y.2 := hcop x.1 hx1 y.2 hy2
        have h21 : Nat.Coprime y.1 x.2 := hcop y.1 hy1 x.2 hx2
        have hxy' : x.1 * x.2 = y.1 * y.2 := hxy
        have hd1 : x.1 ∣ y.1 := h12.dvd_of_dvd_mul_right ⟨x.2, hxy'.symm⟩
        have hd2 : y.1 ∣ x.1 := h21.dvd_of_dvd_mul_right ⟨y.2, hxy'⟩
        have heq1 : x.1 = y.1 := Nat.dvd_antisymm hd1 hd2
        have hx1_pos : 0 < x.1 := (Finset.mem_Icc.mp (hSA_sub hx1)).1
        have heq2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hx1_pos (heq1 ▸ hxy')
        exact Prod.ext heq1 heq2
      calc ∑ x ∈ SA ×ˢ SB, ((1 : ℝ) / (x.1 : ℝ)) * ((1 : ℝ) / (x.2 : ℝ))
          = ∑ x ∈ SA ×ˢ SB, (1 : ℝ) / ((ψ x : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro x _
            simp only [ψ, Nat.cast_mul, one_div, mul_inv]
        _ = ∑ m ∈ (SA ×ˢ SB).image ψ, (1 : ℝ) / (m : ℝ) :=
            (Finset.sum_image (f := fun m : ℕ => (1 : ℝ) / (m : ℝ)) hψ_inj).symm
        _ ≤ ∑ m ∈ Finset.Icc 1 (n * n), (1 : ℝ) / (m : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hψ_sub (fun _ _ _ => by positivity)
    refine hle_harm.trans ?_
    have h1 := Erdos490H3.harmonic_le_one_add_log (n * n) (by nlinarith)
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hlog_sq : Real.log ((n * n : ℕ) : ℝ) = 2 * Real.log (n : ℝ) := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
      ring
    linarith
  have hSA_bd := Erdos490H3.card_mul_log_le hn hSA_sub h1SA hSA_div
  have hSB_bd := Erdos490H3.card_mul_log_le hn hSB_sub h1SB hSB_div
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hSA_SB : (SA.card : ℝ) * (SB.card : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
      (Real.log 4 + 5) ^ 2 * (n : ℝ) ^ 2 * (4 * Real.log (n : ℝ)) := by
    have hmul := mul_le_mul hSA_bd hSB_bd (by positivity) (by positivity)
    have h1 : (SA.card : ℝ) * Real.log (n : ℝ) * ((SB.card : ℝ) * Real.log (n : ℝ)) =
        (SA.card : ℝ) * (SB.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by ring
    have h2 : (Real.log 4 + 5) * (n : ℝ) * (∑ d ∈ SA, (1 : ℝ) / (d : ℝ)) *
        ((Real.log 4 + 5) * (n : ℝ) * (∑ d ∈ SB, (1 : ℝ) / (d : ℝ))) =
        (Real.log 4 + 5) ^ 2 * (n : ℝ) ^ 2 *
          ((∑ d ∈ SA, (1 : ℝ) / (d : ℝ)) * (∑ d ∈ SB, (1 : ℝ) / (d : ℝ))) := by ring
    rw [h1, h2] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left hprod_recip (by positivity))
  have hSA_SB' : (SA.card : ℝ) * (SB.card : ℝ) * Real.log (n : ℝ) ≤
      4 * (Real.log 4 + 5) ^ 2 * (n : ℝ) ^ 2 := by
    have : (SA.card : ℝ) * (SB.card : ℝ) * Real.log (n : ℝ) * Real.log (n : ℝ) ≤
        4 * (Real.log 4 + 5) ^ 2 * (n : ℝ) ^ 2 * Real.log (n : ℝ) := by linarith
    exact le_of_mul_le_mul_right this hlog_pos
  have hAB_le : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) ^ 2 * ((SA.card : ℝ) * (SB.card : ℝ)) := by
    have hA' : (A.card : ℝ) ≤ (K : ℝ) * (SA.card : ℝ) := by exact_mod_cast hA_card
    have hB' : (B.card : ℝ) ≤ (K : ℝ) * (SB.card : ℝ) := by exact_mod_cast hB_card
    have := mul_le_mul hA' hB' (by positivity) (by positivity)
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos hn_pos)]
  calc (A.card : ℝ) * (B.card : ℝ) * Real.log (n : ℝ)
      ≤ (K : ℝ) ^ 2 * ((SA.card : ℝ) * (SB.card : ℝ)) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hAB_le hlog_pos.le
    _ = (K : ℝ) ^ 2 * ((SA.card : ℝ) * (SB.card : ℝ) * Real.log (n : ℝ)) := by ring
    _ ≤ (K : ℝ) ^ 2 * (4 * (Real.log 4 + 5) ^ 2 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hSA_SB' (by positivity)
    _ = (K : ℝ) ^ 2 * (4 * (Real.log 4 + 5) ^ 2) * (n : ℝ) ^ 2 := by ring
