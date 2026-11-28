import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2

open Filter Set Real
open scoped Topology

private lemma dini_nonincreasing {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hdini : ∀ x ∈ Ico a b, ∀ r > 0, ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (f y - f x) < r) :
    f b ≤ f a := by
  by_contra hlt
  push_neg at hlt
  rcases eq_or_lt_of_le hab with rfl | hlt_ab
  · exact lt_irrefl _ hlt
  let ε : ℝ := (f b - f a) / (2 * (b - a))
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (by linarith)
  let g : ℝ → ℝ := fun x => f x - f a - ε * (x - a)
  have hg_cont : ContinuousOn g (Icc a b) := by
    refine (hcont.sub continuousOn_const).sub ?_
    exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
  let S : Set ℝ := {x ∈ Icc a b | g x ≤ 0}
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, by simp [g]⟩
  have hS_ne : S.Nonempty := ⟨a, haS⟩
  have hS_bdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  have hS_closed : IsClosed S := by
    have hpre : S = Icc a b ∩ g ⁻¹' Iic 0 := by
      ext x
      simp [S, mem_Iic]
    rw [hpre]
    exact hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  let c : ℝ := sSup S
  have hcS : c ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  have hcb : c ≤ b := hcS.1.2
  have hca : a ≤ c := hcS.1.1
  have hgc : g c ≤ 0 := hcS.2
  have hc_lt : c < b := by
    rcases eq_or_lt_of_le hcb with hce | hlt'
    · exfalso
      have hgb : g b ≤ 0 := hce ▸ hgc
      have hgb_val : g b = (f b - f a) / 2 := by
        dsimp [g, ε]
        have hba : b - a ≠ 0 := sub_ne_zero.mpr hlt_ab.ne'
        field_simp [hba]
        ring
      linarith
    · exact hlt'
  have hfreq := hdini c ⟨hca, hc_lt⟩ ε hε
  have hIoo : Ioo c b ∈ 𝓝[>] c := Ioo_mem_nhdsGT hc_lt
  have hfreq' := hfreq.and_eventually hIoo
  obtain ⟨y, hy_ineq, hy_gt, hy_lt⟩ := hfreq'.exists
  have hyc_pos : 0 < y - c := sub_pos.mpr hy_gt
  have hfy : f y - f c < ε * (y - c) := by
    have h1 := mul_lt_mul_of_pos_left hy_ineq hyc_pos
    rw [mul_inv_cancel_left₀ hyc_pos.ne'] at h1
    linarith
  have hgy : g y ≤ 0 := by
    have hdiff : g y - g c = (f y - f c) - ε * (y - c) := by
      dsimp [g]
      ring
    linarith
  have hyS : y ∈ S := ⟨⟨hca.trans hy_gt.le, hy_lt.le⟩, hgy⟩
  have hyle : y ≤ c := le_csSup hS_bdd hyS
  linarith

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2.H1 := by
  intro n t w ht0 hmono hcont hdini hjump hw0 hwn
  let Φ : (ℝ → ℝ) → ℝ → ℝ := fun u s =>
    u s * (4 * s + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * s + 1) ^ (1 / 4 : ℝ)
  have ht_nonneg : ∀ k : ℕ, 0 ≤ t k := fun k => ht0 ▸ hmono (Nat.zero_le k)
  have hstep : ∀ i < n, Φ (w (i + 1)) (t (i + 1)) ≤ Φ (w i) (t i) := by
    intro i hi
    have hti : 0 ≤ t i := ht_nonneg i
    have hti1 : 0 ≤ t (i + 1) := ht_nonneg (i + 1)
    have hle : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
    have hPhi_cont : ContinuousOn (Φ (w i)) (Icc (t i) (t (i + 1))) := by
      have hlin : ContinuousOn (fun s : ℝ => 4 * s + 1) (Icc (t i) (t (i + 1))) :=
        (continuousOn_const.mul continuousOn_id).add continuousOn_const
      have hne : ∀ s ∈ Icc (t i) (t (i + 1)), (4 * s + 1 : ℝ) ≠ 0 := by
        intro s hs
        have : 0 ≤ s := hti.trans hs.1
        linarith
      have hp1 : ContinuousOn (fun s : ℝ => (4 * s + 1) ^ (-(3 / 4) : ℝ)) (Icc (t i) (t (i + 1))) :=
        hlin.rpow_const fun s hs => Or.inl (hne s hs)
      have hp2 : ContinuousOn (fun s : ℝ => (4 * s + 1) ^ (1 / 4 : ℝ)) (Icc (t i) (t (i + 1))) :=
        hlin.rpow_const fun s hs => Or.inl (hne s hs)
      exact ((hcont i hi).mul hp1).add (continuousOn_const.mul hp2)
    have hdec : Φ (w i) (t (i + 1)) ≤ Φ (w i) (t i) :=
      dini_nonincreasing hle hPhi_cont (hdini i hi)
    have hpos : 0 ≤ (4 * t (i + 1) + 1) ^ (-(3 / 4) : ℝ) :=
      rpow_nonneg (by linarith) _
    have hj : Φ (w (i + 1)) (t (i + 1)) ≤ Φ (w i) (t (i + 1)) := by
      dsimp [Φ]
      gcongr
      exact hjump i hi
    exact hj.trans hdec
  have hind : ∀ k ≤ n, Φ (w k) (t k) ≤ Φ (w 0) (t 0) := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ m ih =>
      exact (hstep m (by omega)).trans (ih (by omega))
  have hfinal : Φ (w n) (t n) ≤ Φ (w 0) (t 0) := hind n le_rfl
  have hPhi0 : Φ (w 0) (t 0) = w 0 0 + 2 * Real.pi := by
    dsimp [Φ]
    rw [ht0]
    norm_num
  have htn0 : 0 ≤ t n := ht_nonneg n
  have hbase_pos : 0 < 4 * t n + 1 := by linarith
  have hwn_term : 0 ≤ w n (t n) * (4 * t n + 1) ^ (-(3 / 4) : ℝ) :=
    mul_nonneg hwn (rpow_nonneg hbase_pos.le _)
  have hineq1 : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ w 0 0 + 2 * Real.pi := by
    dsimp [Φ] at hfinal
    linarith [hfinal, hPhi0, hwn_term]
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hineq2 : (4 * t n + 1) ^ (1 / 4 : ℝ) ≤ 1 + w 0 0 / (2 * Real.pi) := by
    have hdiv := div_le_div_of_nonneg_right hineq1 h2pi_pos.le
    have hlhs : 2 * Real.pi * (4 * t n + 1) ^ (1 / 4 : ℝ) / (2 * Real.pi) =
        (4 * t n + 1) ^ (1 / 4 : ℝ) := by
      field_simp [h2pi_pos.ne']
    have hrhs : (w 0 0 + 2 * Real.pi) / (2 * Real.pi) = 1 + w 0 0 / (2 * Real.pi) := by
      field_simp [h2pi_pos.ne']
      ring
    linarith
  have hpow4 : ((4 * t n + 1) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) ≤ (1 + w 0 0 / (2 * Real.pi)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (rpow_nonneg hbase_pos.le _) hineq2 4
  have hlhs4 : ((4 * t n + 1) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = 4 * t n + 1 := by
    rw [← rpow_natCast, ← rpow_mul hbase_pos.le]
    norm_num
  rw [hlhs4] at hpow4
  linarith
