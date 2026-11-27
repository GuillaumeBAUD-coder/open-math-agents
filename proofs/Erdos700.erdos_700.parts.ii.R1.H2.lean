import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Erdos Problem 700, Step H2

Existence of arbitrarily large prime triples `p < q < r` with increasing gaps
`q - p < r - q` and `2 * (r - p) ^ 2 < p`, proved via elementary Chebyshev bounds
and block pigeonhole.
-/

open Finset

private lemma two_pow_le_succ_mul_pow_primeCounting (x : ℕ) (hx : 0 < x) :
    2 ^ x ≤ (x + 1) * x ^ Nat.primeCounting x := by
  have hlcm : x.lcmUpto ≤ x ^ Nat.primeCounting x := by
    rw [Nat.lcmUpto_eq_prod_pow_log, ← Nat.primesLE_card_eq_primeCounting, ← Finset.prod_const]
    gcongr with p _
    exact Nat.pow_log_le_self p hx.ne'
  calc 2 ^ x ≤ (x + 1) * x.lcmUpto := Chebyshev.two_pow_le_mul_lcmUpto x
    _ ≤ (x + 1) * x ^ Nat.primeCounting x := Nat.mul_le_mul_left (x + 1) hlcm

private lemma quad_lt_two_pow (m : ℕ) (hm : 12 ≤ m) :
    (3 * m + 1) * (2 * m + 4) < 2 ^ m := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le hm with heq | hlt
    · have hn : n = 11 := by omega
      subst hn
      norm_num
    · have ihn : (3 * n + 1) * (2 * n + 4) < 2 ^ n := ih (by omega)
      have hstep : (3 * (n + 1) + 1) * (2 * (n + 1) + 4) ≤
          2 * ((3 * n + 1) * (2 * n + 4)) := by
        have h1 : (3 * (n + 1) + 1) * (2 * (n + 1) + 4) = 6 * (n * n) + 26 * n + 24 := by ring
        have h2 : 2 * ((3 * n + 1) * (2 * n + 4)) = 12 * (n * n) + 28 * n + 8 := by ring
        omega
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

private lemma primeCounting_pow3_gt (m : ℕ) (hm : 12 ≤ m) :
    (2 * m + 1) * 2 ^ (2 * m) < Nat.primeCounting (2 ^ (3 * m)) := by
  set Y := 2 ^ (3 * m)
  set k := Nat.primeCounting Y
  have hY_pos : 0 < Y := Nat.pos_of_ne_zero (by positivity)
  by_contra hle
  have hk_le : k ≤ (2 * m + 1) * 2 ^ (2 * m) := by omega
  have h2m_pos : 0 < 2 ^ (2 * m) := Nat.pos_of_ne_zero (by positivity)
  have hk1_le : k + 1 ≤ (2 * m + 4) * 2 ^ (2 * m) := by
    have h1 : (2 * m + 4) * 2 ^ (2 * m) = (2 * m + 1) * 2 ^ (2 * m) + 3 * 2 ^ (2 * m) := by ring
    omega
  have hcheb : 2 ^ Y ≤ (Y + 1) * Y ^ k := two_pow_le_succ_mul_pow_primeCounting Y hY_pos
  have hY1_le : Y + 1 ≤ 2 ^ (3 * m + 1) := by
    have hpow : 2 ^ (3 * m + 1) = 2 * Y := by dsimp [Y]; ring
    omega
  have hupper : (Y + 1) * Y ^ k ≤ 2 ^ ((3 * m + 1) * (k + 1)) := by
    calc (Y + 1) * Y ^ k ≤ 2 ^ (3 * m + 1) * (2 ^ (3 * m)) ^ k :=
          Nat.mul_le_mul hY1_le le_rfl
      _ = 2 ^ (3 * m + 1) * 2 ^ (3 * m * k) := by rw [← pow_mul]
      _ = 2 ^ ((3 * m + 1) + 3 * m * k) := (pow_add 2 (3 * m + 1) (3 * m * k)).symm
      _ ≤ 2 ^ ((3 * m + 1) * (k + 1)) := by
          apply Nat.pow_le_pow_right (by omega)
          have hmul : (3 * m + 1) * (k + 1) = (3 * m + 1) + 3 * m * k + k := by ring
          omega
  have hY_le_exp : Y ≤ (3 * m + 1) * (k + 1) := by
    by_contra hlt
    have hpow_lt : 2 ^ ((3 * m + 1) * (k + 1)) < 2 ^ Y :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hcancel : 2 ^ m ≤ (3 * m + 1) * (2 * m + 4) := by
    apply Nat.le_of_mul_le_mul_right _ h2m_pos
    calc 2 ^ m * 2 ^ (2 * m) = 2 ^ (m + 2 * m) := (pow_add 2 m (2 * m)).symm
      _ = Y := by dsimp [Y]; congr 1; ring
      _ ≤ (3 * m + 1) * (k + 1) := hY_le_exp
      _ ≤ (3 * m + 1) * ((2 * m + 4) * 2 ^ (2 * m)) := Nat.mul_le_mul_left (3 * m + 1) hk1_le
      _ = (3 * m + 1) * (2 * m + 4) * 2 ^ (2 * m) := by ring
  have hquad := quad_lt_two_pow m hm
  omega

private lemma card_primesIco_le_add (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    #((Finset.Ico a c).filter Nat.Prime) ≤
      #((Finset.Ico a b).filter Nat.Prime) + #((Finset.Ico b c).filter Nat.Prime) := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.filter_union]
  exact Finset.card_union_le _ _

private lemma exists_block_primesIco (X L m : ℕ) :
    ∀ B : ℕ, m * B < #((Finset.Ico X (X + B * L)).filter Nat.Prime) →
      ∃ t < B, m + 1 ≤ #((Finset.Ico (X + t * L) (X + (t + 1) * L)).filter Nat.Prime) := by
  intro B
  induction B with
  | zero => simp
  | succ B ih =>
    intro hcard
    have hle_end : X + B * L ≤ X + (B + 1) * L := by
      have h1 : (B + 1) * L = B * L + L := by ring
      omega
    have hsplit := card_primesIco_le_add X (X + B * L) (X + (B + 1) * L) (by omega) hle_end
    by_cases hlast : m + 1 ≤ #((Finset.Ico (X + B * L) (X + (B + 1) * L)).filter Nat.Prime)
    · exact ⟨B, by omega, hlast⟩
    · have hmB : m * (B + 1) = m * B + m := by ring
      obtain ⟨t, ht, htm⟩ := ih (by omega)
      exact ⟨t, by omega, htm⟩

private lemma exists_increasing_gap_finset :
    ∀ k : ℕ, 2 ≤ k → ∀ S : Finset ℕ, k + 1 ≤ #S →
      (∀ x ∈ S, ∀ y ∈ S, y - x < 2 ^ (k - 1)) →
      ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p < q ∧ q < r ∧ q - p < r - q := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    intro S hcard hspan
    have hne₀ : S.Nonempty := Finset.card_pos.mp (by omega)
    let a₀ := S.min' hne₀
    let b := S.max' hne₀
    have ha₀S : a₀ ∈ S := S.min'_mem hne₀
    have hbS : b ∈ S := S.max'_mem hne₀
    let S' := S.erase a₀
    have hcard' : #S' = #S - 1 := Finset.card_erase_of_mem ha₀S
    have hne₁ : S'.Nonempty := Finset.card_pos.mp (by omega)
    let a₁ := S'.min' hne₁
    have ha₁S' : a₁ ∈ S' := S'.min'_mem hne₁
    have ha₁_ne : a₁ ≠ a₀ := (Finset.mem_erase.mp ha₁S').1
    have ha₁S : a₁ ∈ S := (Finset.mem_erase.mp ha₁S').2
    have ha₀_le_a₁ : a₀ ≤ a₁ := S.min'_le a₁ ha₁S
    have ha₀_lt_a₁ : a₀ < a₁ := by omega
    let S'' := S'.erase a₁
    have hcard'' : #S'' = #S' - 1 := Finset.card_erase_of_mem ha₁S'
    have hne₂ : S''.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hne₂
    have hz_ne : z ≠ a₁ := (Finset.mem_erase.mp hz).1
    have hzS' : z ∈ S' := (Finset.mem_erase.mp hz).2
    have hzS : z ∈ S := (Finset.mem_erase.mp hzS').2
    have ha₁_le_z : a₁ ≤ z := S'.min'_le z hzS'
    have hz_le_b : z ≤ b := S.le_max' z hzS
    have ha₁_lt_b : a₁ < b := by omega
    have hb_span : b - a₀ < 2 ^ m := by
      simpa using hspan a₀ ha₀S b hbS
    rcases eq_or_lt_of_le hk with heq | hlt
    · have hm1 : m = 1 := by omega
      subst hm1
      norm_num at hb_span
      omega
    · have hm2 : 2 ≤ m := by omega
      by_cases hgap : a₁ - a₀ < b - a₁
      · exact ⟨a₀, ha₀S, a₁, ha₁S, b, hbS, ha₀_lt_a₁, ha₁_lt_b, hgap⟩
      · have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
          calc 2 ^ m = 2 ^ (1 + (m - 1)) := by congr 1; omega
            _ = 2 ^ 1 * 2 ^ (m - 1) := pow_add 2 1 (m - 1)
            _ = 2 * 2 ^ (m - 1) := by ring
        have hb_a₁ : b - a₁ < 2 ^ (m - 1) := by omega
        obtain ⟨p, hpS', q, hqS', r, hrS', hpq, hqr, hgap'⟩ :=
          ih hm2 S' (by omega) (fun x hx y hy => by
            have ha₁_x : a₁ ≤ x := S'.min'_le x hx
            have hy_b : y ≤ b := S.le_max' y (Finset.mem_erase.mp hy).2
            omega)
        exact ⟨p, (Finset.mem_erase.mp hpS').2, q, (Finset.mem_erase.mp hqS').2,
          r, (Finset.mem_erase.mp hrS').2, hpq, hqr, hgap'⟩

theorem prove_Erdos700_H2 :
    ∀ N : ℕ, ∃ p q r : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
      q - p < r - q ∧ 2 * (r - p) ^ 2 < p := by
  intro N
  let m := N + 12
  have hm12 : 12 ≤ m := by omega
  let X := 2 ^ (2 * m)
  let L := 2 ^ (m - 1)
  let B := 2 ^ (2 * m + 1)
  let Y := 2 ^ (3 * m)
  have hX_pos : 0 < X := Nat.pos_of_ne_zero (by positivity)
  have hBL : B * L = Y := by
    dsimp [B, L, Y]
    rw [← pow_add]
    congr 1
    omega
  have hpiY_gt : X + m * B < Nat.primeCounting Y := by
    have hgt := primeCounting_pow3_gt m hm12
    have hsum : X + m * B = (2 * m + 1) * 2 ^ (2 * m) := by
      dsimp [X, B]
      ring
    rw [hsum]
    exact hgt
  have hpi_le : Nat.primeCounting Y ≤ #((Finset.Ico 0 (X + B * L)).filter Nat.Prime) := by
    calc Nat.primeCounting Y = Nat.primeCounting' (Y + 1) :=
          Nat.primeCounting_eq_primeCounting'_succ Y
      _ ≤ Nat.primeCounting' (X + B * L) := Nat.monotone_primeCounting' (by omega)
      _ = #(Nat.primesBelow (X + B * L)) :=
          (Nat.primesBelow_card_eq_primeCounting' (X + B * L)).symm
      _ = #((Finset.Ico 0 (X + B * L)).filter Nat.Prime) := by
          rw [Nat.primesBelow_eq_filter_Ico_zero]
  have h0X : #((Finset.Ico 0 X).filter Nat.Prime) ≤ X := by
    calc #((Finset.Ico 0 X).filter Nat.Prime) ≤ #(Finset.Ico 0 X) := Finset.card_filter_le _ _
      _ = X := by simp
  have hsplit := card_primesIco_le_add 0 X (X + B * L) (by omega) (by omega)
  have hmB_lt : m * B < #((Finset.Ico X (X + B * L)).filter Nat.Prime) := by omega
  obtain ⟨t, _, hblock⟩ := exists_block_primesIco X L m B hmB_lt
  set S := (Finset.Ico (X + t * L) (X + (t + 1) * L)).filter Nat.Prime
  have hspan : ∀ x ∈ S, ∀ y ∈ S, y - x < 2 ^ (m - 1) := by
    intro x hx y hy
    have hxI : X + t * L ≤ x ∧ x < X + (t + 1) * L := Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
    have hyI : X + t * L ≤ y ∧ y < X + (t + 1) * L := Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1
    have hend : X + (t + 1) * L = X + t * L + L := by ring
    have hL_def : L = 2 ^ (m - 1) := rfl
    omega
  obtain ⟨p, hpS, q, hqS, r, hrS, hpq, hqr, hgap⟩ :=
    exists_increasing_gap_finset m (by omega) S hblock hspan
  have hpF := Finset.mem_filter.mp hpS
  have hqF := Finset.mem_filter.mp hqS
  have hrF := Finset.mem_filter.mp hrS
  have hpI := Finset.mem_Ico.mp hpF.1
  have hrI := Finset.mem_Ico.mp hrF.1
  have hN_lt_X : N < X := by
    have hlt2m : 2 * m < 2 ^ (2 * m) := Nat.lt_two_pow_self
    have hX_def : X = 2 ^ (2 * m) := rfl
    omega
  have hsmall : 2 * (r - p) ^ 2 < p := by
    have hend : X + (t + 1) * L = X + t * L + L := by ring
    have hrp_lt : r - p < L := by omega
    have hsq_lt : (r - p) ^ 2 < L ^ 2 := by
      have hmul : (r - p) ^ 2 + 2 * (r - p) + 1 ≤ L ^ 2 := by
        calc (r - p) ^ 2 + 2 * (r - p) + 1 = (r - p + 1) * (r - p + 1) := by ring
          _ ≤ L * L := Nat.mul_le_mul (by omega) (by omega)
          _ = L ^ 2 := by ring
      omega
    have hX_eq : X = 4 * L ^ 2 := by
      show 2 ^ (2 * m) = 4 * (2 ^ (m - 1)) ^ 2
      rw [show 2 * m = 2 * (m - 1) + 2 by omega]
      ring
    omega
  exact ⟨p, q, r, by omega, hpF.2, hqF.2, hrF.2, hpq, hqr, hgap, hsmall⟩

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 :=
  prove_Erdos700_H2
