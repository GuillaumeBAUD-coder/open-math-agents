import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
import Mathlib.NumberTheory.Bertrand

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R1.H2.R1 of step Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R1.H2
-- Credit: @jktcv2kz4f-cyber

/-!
# Prime-cyclic Bertrand reduction for polylogarithmic k-AP bounds (k ≥ 5)

We reduce the interval polylogarithmic bound `r k N < N / (⌈log N⌉₊ + 1) ^ 4` (`k ≥ 5`)
to prime-cyclic bounds on `ZMod p` with factor `4`, split between `k = 5` (`H1`) and
`k ≥ 6` (`H2`), via Bertrand's postulate (`2 * N < p ≤ 4 * N`) and modular `k`-AP lifting.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1_H2_R1

open Erdos142 Filter Real

/-- Prime-cyclic polylogarithmic 5-AP-free bound on ZMod p. -/
def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime → ∀ A : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 5 → a + (i : ZMod p) * d ∈ A) →
    (A.card : ℝ) < (p : ℝ) / (4 * (((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ))

/-- Prime-cyclic polylogarithmic k-AP-free bound on ZMod p for k ≥ 6. -/
def H2 : Prop :=
  ∀ k : ℕ, 6 ≤ k → ∀ᶠ p : ℕ in atTop, p.Prime → ∀ A : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
    (A.card : ℝ) < (p : ℝ) / (4 * (((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ))

lemma mod_ap_lift {k N p : ℕ} (hk : 2 ≤ k) (hp : 2 * N < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hfree : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    ¬ ∃ a d : ZMod p, d ≠ 0 ∧
      ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ S.image (fun x : ℕ => (x : ZMod p)) := by
  rintro ⟨a, d, hd, hmem⟩
  have hlift : ∀ i : ℕ, i < k → ∃ x ∈ S, (x : ZMod p) = a + (i : ZMod p) * d := by
    intro i hi
    obtain ⟨x, hxS, hxEq⟩ := Finset.mem_image.mp (hmem i hi)
    exact ⟨x, hxS, hxEq⟩
  choose x hxS hxEq using hlift
  have hxBounds : ∀ i (hi : i < k), 1 ≤ x i hi ∧ x i hi ≤ N := fun i hi =>
    Finset.mem_Icc.mp (hS (hxS i hi))
  let d_int : ∀ i, i + 1 < k → ℤ := fun i hi => (x (i + 1) hi : ℤ) - (x i (by omega) : ℤ)
  have hdiff_mod : ∀ i (hi : i + 1 < k), (d_int i hi : ZMod p) = d := by
    intro i hi
    dsimp only [d_int]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hxEq (i + 1) hi, hxEq i (by omega)]
    push_cast
    ring
  have hdiff_eq : ∀ i (hi : i + 1 < k), d_int i hi = d_int 0 (by omega) := by
    intro i hi
    have h0 : ((d_int i hi - d_int 0 (by omega) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, hdiff_mod i hi, hdiff_mod 0 (by omega), sub_self]
    have hdvd : (p : ℤ) ∣ (d_int i hi - d_int 0 (by omega)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    have hb1 := hxBounds (i + 1) hi
    have hb2 := hxBounds i (by omega)
    have hb3 := hxBounds 1 (by omega)
    have hb4 := hxBounds 0 (by omega)
    obtain ⟨q, hq⟩ := hdvd
    dsimp only [d_int] at hq ⊢
    have hq0 : q = 0 := by nlinarith
    rw [hq0, mul_zero] at hq
    omega
  set Δ : ℤ := d_int 0 (by omega)
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    have hd0 : d = 0 := by
      rw [← hdiff_mod 0 (by omega)]
      change (Δ : ZMod p) = 0
      rw [h0, Int.cast_zero]
    exact hd hd0
  have hlinear : ∀ i (hi : i < k), (x i hi : ℤ) = (x 0 (by omega) : ℤ) + (i : ℤ) * Δ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simp
    | succ j ih =>
      intro hj
      have hstep := hdiff_eq j hj
      have hjprev := ih (by omega)
      dsimp only [d_int] at hstep
      push_cast
      linarith
  rcases lt_or_gt_of_ne hΔ_ne with hneg | hpos
  · apply hfree
    refine ⟨x (k - 1) (by omega), (-Δ).toNat, by omega, fun i hi => ?_⟩
    have hidx : k - 1 - i < k := by omega
    have hval : x (k - 1) (by omega) + i * (-Δ).toNat = x (k - 1 - i) hidx := by
      have h1 := hlinear (k - 1) (by omega)
      have h2 := hlinear (k - 1 - i) hidx
      have htoNat : ((-Δ).toNat : ℤ) = -Δ := Int.toNat_of_nonneg (by omega)
      have hsub : ((k - 1 - i : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - (i : ℤ) := by omega
      have hcast : ((x (k - 1) (by omega) + i * (-Δ).toNat : ℕ) : ℤ) =
          (x (k - 1 - i) hidx : ℤ) := by
        push_cast
        rw [htoNat, h1, h2, hsub]
        ring
      exact_mod_cast hcast
    rw [hval]
    exact hxS (k - 1 - i) hidx
  · apply hfree
    refine ⟨x 0 (by omega), Δ.toNat, by omega, fun i hi => ?_⟩
    have hval : x 0 (by omega) + i * Δ.toNat = x i hi := by
      have h1 := hlinear i hi
      have htoNat : (Δ.toNat : ℤ) = Δ := Int.toNat_of_nonneg (by omega)
      have hcast : ((x 0 (by omega) + i * Δ.toNat : ℕ) : ℤ) = (x i hi : ℤ) := by
        push_cast
        rw [htoNat, h1]
      exact_mod_cast hcast
    rw [hval]
    exact hxS i hi

lemma extremizer_exists {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hap
    have ht0 : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    exact (Set.not_isAPOfLength_empty (by exact_mod_cast (show 0 < k by omega)) (ht0 ▸ hap)).elim
  have hbdd : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, _, rfl⟩
    exact (Finset.card_mono hS).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbdd
  exact ⟨S, hS, hfree, hcard⟩

lemma no_pos_ap {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T : Finset ℕ := (Finset.range k).image (fun i => a + i * d)
  have hinj : Function.Injective (fun i : ℕ => a + i * d) := fun _ _ h =>
    Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  exact (not_le_of_gt hk) (by exact_mod_cast hfree (T : Set ℕ) hsub hap)

lemma polylog_of_zmod {k : ℕ} (hk : 2 ≤ k)
    (hz : ∀ᶠ p : ℕ in atTop, p.Prime → ∀ A : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A) →
      (A.card : ℝ) < (p : ℝ) / (4 * (((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) < (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hz
  filter_upwards [eventually_ge_atTop (max P₀ 2)] with N hN
  have hNP : P₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hp_ge : P₀ ≤ p := by omega
  obtain ⟨S, hSsub, hSfree, hScard⟩ := extremizer_exists (by omega : 1 < k) N
  let A : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hAcard : A.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxB := Finset.mem_Icc.mp (hSsub hx)
    have hyB := Finset.mem_Icc.mp (hSsub hy)
    have hxp : x < p := by omega
    have hyp : y < p := by omega
    have hval := congrArg ZMod.val hxy
    haveI : NeZero p := ⟨hp_prime.ne_zero⟩
    simpa [ZMod.val_natCast_of_lt hxp, ZMod.val_natCast_of_lt hyp] using hval
  have hAfree : ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ A :=
    mod_ap_lift hk hp_gt hSsub (no_pos_ap (by omega) hSfree)
  have hbound := hP₀ p hp_ge hp_prime A hAfree
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp_leR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast (show p ≤ 4 * N by omega)
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast (show N ≤ p by omega))
  have hceil_le : ⌈Real.log (N : ℝ)⌉₊ ≤ ⌈Real.log (p : ℝ)⌉₊ := Nat.ceil_mono hlog_le
  have hden_le : ((((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) ≤
      ((((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hceil_le 1) 4
  have hdenN_pos : (0 : ℝ) < ((((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) := by positivity
  have hdenp_pos : (0 : ℝ) < 4 * ((((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) := by positivity
  rw [← hScard, ← hAcard]
  calc
    (A.card : ℝ) < (p : ℝ) / (4 * (((⌈Real.log (p : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) := hbound
    _ ≤ (4 * (N : ℝ)) / (4 * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) := by
        apply div_le_div₀ (by positivity) hp_leR (by positivity)
        linarith
    _ = (N : ℝ) / (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
        field_simp [hdenN_pos.ne']

theorem main :
    H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1.H2 := by
  intro h5 h6 k hk
  by_cases hk5 : k = 5
  · subst hk5
    exact polylog_of_zmod (by decide) h5
  · exact polylog_of_zmod (by omega) (h6 k (by omega))

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1_H2_R1
