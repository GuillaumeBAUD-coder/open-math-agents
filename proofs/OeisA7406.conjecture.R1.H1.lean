import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.Tactic

/-!
# Proof of OeisA7406 H1

For every prime `n > 3`, `Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n`.
-/

open BigOperators

private lemma six_mul_sum_range_sq (m : ℕ) :
    6 * ∑ k ∈ Finset.range m, (k : ℤ) ^ 2 = (m : ℤ) * ((m : ℤ) - 1) * (2 * (m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma zmod_sum_range_sq_eq_zero {n : ℕ} (hn3 : 3 < n) (hn_prime : n.Prime) :
    ∑ k ∈ Finset.range n, (k : ZMod n) ^ 2 = 0 := by
  have : Fact n.Prime := ⟨hn_prime⟩
  have hcast := congrArg (Int.cast : ℤ → ZMod n) (six_mul_sum_range_sq n)
  push_cast at hcast
  rw [ZMod.natCast_self, zero_mul, zero_mul] at hcast
  have h6_ne : (6 : ZMod n) ≠ 0 := by
    have hcast6 : ((6 : ℕ) : ZMod n) = (6 : ZMod n) := by norm_num
    rw [← hcast6]
    intro h60
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff 6 n).mp h60
    rcases eq_or_ne c 0 with rfl | hc0
    · omega
    · rcases eq_or_ne c 1 with rfl | hc1
      · have hn6 : n = 6 := by omega
        rw [hn6] at hn_prime
        norm_num at hn_prime
      · have hmul : 4 * 2 ≤ n * c := Nat.mul_le_mul (by omega) (by omega)
        omega
  rcases mul_eq_zero.mp hcast with h6 | hsum
  · exact absurd h6 h6_ne
  · exact hsum

private lemma zmod_sum_Icc_inv_sq_eq_zero {n : ℕ} (hn3 : 3 < n) (hn_prime : n.Prime) :
    ∑ k ∈ Finset.Icc 1 (n - 1), ((k : ZMod n)⁻¹) ^ 2 = 0 := by
  have : Fact n.Prime := ⟨hn_prime⟩
  have hrange_eq : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0_not_mem : (0 : ℕ) ∉ Finset.Icc 1 (n - 1) := by simp
  have hsum_range : ∑ k ∈ Finset.Icc 1 (n - 1), ((k : ZMod n)⁻¹) ^ 2 =
      ∑ k ∈ Finset.range n, ((k : ZMod n)⁻¹) ^ 2 := by
    rw [hrange_eq, Finset.sum_insert h0_not_mem, Nat.cast_zero, inv_zero, sq, zero_mul, zero_add]
  rw [hsum_range]
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod n)) (Finset.range n) := by
    intro r1 hr1 r2 hr2 heq
    dsimp only at heq
    simp only [Finset.coe_range, Set.mem_Iio] at hr1 hr2
    rcases le_total r1 r2 with hle | hle
    · have hsub : ((r2 - r1 : ℕ) : ZMod n) = 0 := by
        rw [Nat.cast_sub hle, heq, sub_self]
      obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hsub
      rcases eq_or_ne c 0 with rfl | hc0
      · omega
      · have hge : n ≤ n * c := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hc0)
        omega
    · have hsub : ((r1 - r2 : ℕ) : ZMod n) = 0 := by
        rw [Nat.cast_sub hle, heq, sub_self]
      obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hsub
      rcases eq_or_ne c 0 with rfl | hc0
      · omega
      · have hge : n ≤ n * c := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hc0)
        omega
  have himg : (Finset.range n).image (fun k : ℕ => (k : ZMod n)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_univ, ZMod.card]
  have h_to_univ : ∑ k ∈ Finset.range n, ((k : ZMod n)⁻¹) ^ 2 = ∑ x : ZMod n, (x⁻¹) ^ 2 := by
    rw [← himg, Finset.sum_image hinj]
  have hinj_inv : Function.Injective (fun x : ZMod n => x⁻¹) := by
    intro x y h
    simpa only [inv_inv] using congrArg Inv.inv h
  have himg_inv : Finset.univ.image (fun x : ZMod n => x⁻¹) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injective _ hinj_inv]
  have h_inv_sq : ∑ x : ZMod n, (x⁻¹) ^ 2 = ∑ y : ZMod n, y ^ 2 := by
    conv_rhs => rw [← himg_inv]
    rw [Finset.sum_image (fun x _ y _ h => hinj_inv h)]
  have h_back_range : ∑ y : ZMod n, y ^ 2 = ∑ k ∈ Finset.range n, (k : ZMod n) ^ 2 := by
    rw [← himg, Finset.sum_image hinj]
  rw [h_to_univ, h_inv_sq, h_back_range]
  exact zmod_sum_range_sq_eq_zero hn3 hn_prime

theorem prove_OeisA7406_H1 :
    ∀ n : ℕ, 3 < n → n.Prime → Nat.gcd n (OeisA7406.a (n - 1)) = OeisA89026.a n := by
  intro n hn3 hn_prime
  have : Fact n.Prime := ⟨hn_prime⟩
  rw [OeisA89026.a, if_pos hn_prime]
  suffices hdvd : n ∣ OeisA7406.a (n - 1) from
    Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd dvd_rfl hdvd)
  unfold OeisA7406.a
  let q : ℚ := ∑ k ∈ Finset.Icc 1 (n - 1), (1 : ℚ) / (k : ℚ) ^ 2
  change n ∣ q.num.natAbs
  let F : ℕ := (n - 1).factorial
  let M : ℕ := F ^ 2
  have hnot_dvd_F : ¬ n ∣ F := by
    intro h
    have hle : n ≤ n - 1 := (hn_prime.dvd_factorial).mp h
    omega
  have hcopF : Nat.Coprime n F := hn_prime.coprime_iff_not_dvd.mpr hnot_dvd_F
  have hcopM : Nat.Coprime n M := hcopF.pow_right 2
  let c : ℕ → ℕ := fun k => M / k ^ 2
  let N : ℕ := ∑ k ∈ Finset.Icc 1 (n - 1), c k
  have hc_mul : ∀ k ∈ Finset.Icc 1 (n - 1), c k * k ^ 2 = M := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkF : k ∣ F := Nat.dvd_factorial (by omega) hk.2
    have hk2M : k ^ 2 ∣ M := pow_dvd_pow_of_dvd hkF 2
    exact Nat.div_mul_cancel hk2M
  have hMq : (M : ℚ) * q = (N : ℚ) := by
    dsimp [q, N]
    rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hcm := congrArg (Nat.cast : ℕ → ℚ) (hc_mul k hk)
    push_cast at hcm
    rw [Finset.mem_Icc] at hk
    have hk2_ne : (k : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
    rw [← hcm, mul_one_div, mul_div_cancel_right₀ _ hk2_ne]
  have hq_eq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
  have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have h_clear_rat : (M : ℚ) * (q.num : ℚ) = (N : ℚ) * (q.den : ℚ) := by
    rw [← hq_eq, ← mul_div_assoc, div_eq_iff hden_ne] at hMq
    exact hMq
  have h_clear_int : (M : ℤ) * q.num = (N : ℤ) * (q.den : ℤ) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    exact h_clear_rat
  have h_clear_nat : M * q.num.natAbs = N * q.den := by
    have h := congrArg Int.natAbs h_clear_int
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h
  have hn_dvd_N : n ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    dsimp [N]
    rw [Nat.cast_sum]
    have hterm : ∀ k ∈ Finset.Icc 1 (n - 1),
        (c k : ZMod n) = (M : ZMod n) * ((k : ZMod n)⁻¹) ^ 2 := by
      intro k hk
      have hcm := congrArg (Nat.cast : ℕ → ZMod n) (hc_mul k hk)
      push_cast at hcm
      rw [Finset.mem_Icc] at hk
      have hk_ne : (k : ZMod n) ≠ 0 := by
        intro hk0
        obtain ⟨d, hd⟩ := (ZMod.natCast_eq_zero_iff k n).mp hk0
        rcases eq_or_ne d 0 with rfl | hd0
        · omega
        · have hge : n ≤ n * d := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0)
          omega
      have hk2_ne : (k : ZMod n) ^ 2 ≠ 0 := pow_ne_zero 2 hk_ne
      rw [← hcm, inv_pow, mul_assoc, mul_inv_cancel₀ hk2_ne, mul_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      zmod_sum_Icc_inv_sq_eq_zero hn3 hn_prime, mul_zero]
  have hn_dvd_prod : n ∣ M * q.num.natAbs := by
    rw [h_clear_nat]
    exact dvd_mul_of_dvd_left hn_dvd_N q.den
  exact hcopM.dvd_of_dvd_mul_left hn_dvd_prod

theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 :=
  prove_OeisA7406_H1
