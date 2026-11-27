import OMAReductions.R_Erdos939_erdos_939_R1
import Mathlib.Tactic

/-!
# Erdos Problem 939, Step H2

Proof that `(Erdos939.Erdos939Sums r).Nonempty` for every `r ≥ 6`, using the
odd-index binomial expansion of `(A + B) ^ r - (A - B) ^ r` and binary splitting
of the `j = 1` term.
-/

open Finset

private lemma full_pow (r x : ℕ) : r.Full (x ^ r) := by
  intro p hp
  obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨c, hc⟩ := hp_prime.dvd_of_dvd_pow hp_dvd
  exact ⟨c ^ r, by rw [hc]; ring⟩

private lemma full_mul_pow (r C W : ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ C → p ∣ W) : r.Full (C * W ^ r) := by
  intro p hp
  obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpW : p ∣ W := by
    rcases hp_prime.dvd_mul.mp hp_dvd with hC | hWr
    · exact hprime p hp_prime hC
    · exact hp_prime.dvd_of_dvd_pow hWr
  obtain ⟨c, hc⟩ := hpW
  exact ⟨C * c ^ r, by rw [hc]; ring⟩

private lemma sub_neg_pow (b : ℤ) (j : ℕ) :
    b ^ j - (-b) ^ j = if j % 2 = 0 then 0 else 2 * b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j % 2 = 0
    · have hj1 : (j + 1) % 2 ≠ 0 := by omega
      rw [if_pos hj] at ih
      rw [if_neg hj1]
      have hbj : (-b) ^ j = b ^ j := by linarith
      calc b ^ (j + 1) - (-b) ^ (j + 1) = b ^ j * b - (-b) ^ j * (-b) := by ring
        _ = b ^ j * b - b ^ j * (-b) := by rw [hbj]
        _ = 2 * b ^ (j + 1) := by ring
    · have hj1 : (j + 1) % 2 = 0 := by omega
      rw [if_neg hj] at ih
      rw [if_pos hj1]
      have hbj : (-b) ^ j = -b ^ j := by linarith
      calc b ^ (j + 1) - (-b) ^ (j + 1) = b ^ j * b - (-b) ^ j * (-b) := by ring
        _ = b ^ j * b - (-b ^ j) * (-b) := by rw [hbj]
        _ = 0 := by ring

private lemma sum_odd_range (g : ℕ → ℤ) (N : ℕ) :
    (∑ j ∈ Finset.range N, if j % 2 = 0 then 0 else g j) =
      ∑ k ∈ Finset.range (N / 2), g (2 * k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hN : N % 2 = 0
    · have hdiv : (N + 1) / 2 = N / 2 := by omega
      rw [if_pos hN, hdiv, add_zero]
    · have hdiv : (N + 1) / 2 = N / 2 + 1 := by omega
      have hN_eq : 2 * (N / 2) + 1 = N := by omega
      rw [if_neg hN, hdiv, Finset.sum_range_succ, hN_eq]

private lemma binom_odd_sum (A B r : ℕ) (hBA : B ≤ A) :
    (A + B) ^ r = (A - B) ^ r +
      ∑ k ∈ Finset.range ((r + 1) / 2),
        2 * r.choose (2 * k + 1) * A ^ (r - (2 * k + 1)) * B ^ (2 * k + 1) := by
  suffices hZ : ((A + B : ℕ) : ℤ) ^ r - ((A - B : ℕ) : ℤ) ^ r =
      ∑ k ∈ Finset.range ((r + 1) / 2),
        2 * (r.choose (2 * k + 1) : ℤ) * (A : ℤ) ^ (r - (2 * k + 1)) * (B : ℤ) ^ (2 * k + 1) by
    have hZ' : (((A + B) ^ r : ℕ) : ℤ) =
        (((A - B) ^ r + ∑ k ∈ Finset.range ((r + 1) / 2),
          2 * r.choose (2 * k + 1) * A ^ (r - (2 * k + 1)) * B ^ (2 * k + 1) : ℕ) : ℤ) := by
      push_cast at hZ ⊢
      linarith
    exact Int.ofNat_inj.mp hZ'
  rw [Nat.cast_add, Nat.cast_sub hBA]
  set a : ℤ := (A : ℤ)
  set b : ℤ := (B : ℤ)
  have h1 : (a + b) ^ r = (b + a) ^ r := by ring
  have h2 : (a - b) ^ r = (-b + a) ^ r := by ring
  rw [h1, h2, _root_.add_pow b a r, _root_.add_pow (-b) a r, ← Finset.sum_sub_distrib]
  have hcongr : (∑ j ∈ Finset.range (r + 1),
      (b ^ j * a ^ (r - j) * (r.choose j : ℤ) - (-b) ^ j * a ^ (r - j) * (r.choose j : ℤ))) =
      ∑ j ∈ Finset.range (r + 1),
        if j % 2 = 0 then 0 else 2 * (r.choose j : ℤ) * a ^ (r - j) * b ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsub : b ^ j * a ^ (r - j) * (r.choose j : ℤ) - (-b) ^ j * a ^ (r - j) * (r.choose j : ℤ) =
        (b ^ j - (-b) ^ j) * a ^ (r - j) * (r.choose j : ℤ) := by ring
    rw [hsub, sub_neg_pow b j]
    split_ifs <;> ring
  rw [hcongr]
  exact sum_odd_range (fun j => 2 * (r.choose j : ℤ) * a ^ (r - j) * b ^ j) (r + 1)

private lemma geom_two_sum (s : ℕ) : (∑ i ∈ Finset.range s, 2 ^ i) + 1 = 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    omega

private lemma sum_range_add_eq (f : ℕ → ℕ) (a b : ℕ) :
    ∑ i ∈ Finset.range (a + b), f i =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range b, f (a + i) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

private lemma sum_range_rev (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, f (n - 1 - i) = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hcongr : (∑ i ∈ Finset.range n, f (n + 1 - 1 - (i + 1))) =
        ∑ i ∈ Finset.range n, f (n - 1 - i) :=
      Finset.sum_congr rfl fun i _ => by congr 1; omega
    rw [hcongr, ih]
    simp

private lemma choose_le_two_pow (r j : ℕ) (hj : j ≤ r) : r.choose j ≤ 2 ^ r := by
  rw [← Nat.sum_range_choose r]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

private lemma injOn_range_of_step (f : ℕ → ℕ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → f i < f (i + 1)) :
    Set.InjOn f (Finset.range N) := by
  have hlt : ∀ a b, a < b → b < N → f a < f b := by
    intro a b hab hbN
    induction b with
    | zero => omega
    | succ b ih =>
      rcases eq_or_lt_of_le (by omega : a ≤ b) with rfl | hab'
      · exact hstep a hbN
      · exact lt_trans (ih hab' (by omega)) (hstep b hbN)
  intro a ha b hb hab
  have haN : a < N := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hbN : b < N := Finset.mem_range.mp (Finset.mem_coe.mp hb)
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (hlt a b h hbN).ne
  · exact h
  · exact absurd hab.symm (hlt b a h haN).ne

private lemma dvd_M_of_prime_dvd_choose (r j D p : ℕ) (hj : j ≤ r) (hp : p.Prime)
    (hdvd : p ∣ 2 * r.choose j * D ^ j) : p ∣ 2 * r.factorial * D := by
  rcases hp.dvd_mul.mp hdvd with h2c | hDj
  · rcases hp.dvd_mul.mp h2c with h2 | hc
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
    · have hcf : r.choose j ∣ r.factorial :=
        ⟨j.factorial * (r - j).factorial, by
          rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hj]⟩
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hc.trans hcf) _) _
  · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hDj) _

theorem prove_Erdos939_H2 :
    ∀ r ≥ 6, (Erdos939.Erdos939Sums r).Nonempty := by
  intro r hr
  let m := (r + 1) / 2
  let s := r - 2 - m
  have hm_ge : 3 ≤ m := by omega
  have hs_ge : 1 ≤ s := by omega
  have hm_top : 2 * (m - 2) + 3 ≤ r := by omega
  have hlen : (m - 1) + s = r - 3 := by omega
  let D := 2 ^ s - 1
  have h2s_ge : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs_ge
  have hD_pos : 0 < D := by omega
  have hD_sum : (∑ i ∈ Finset.range s, 2 ^ i) = D := by
    have h := geom_two_sum s
    omega
  let M := 2 * r.factorial * D
  have hrf_pos : 0 < r.factorial := Nat.factorial_pos r
  have hM_pos : 0 < M := Nat.mul_pos (Nat.mul_pos (by omega) hrf_pos) hD_pos
  let B := D * M ^ r
  have hMr_pos : 0 < M ^ r := pow_pos hM_pos r
  have hB_pos : 0 < B := Nat.mul_pos hD_pos hMr_pos
  obtain ⟨q, hq_ge, hq⟩ := Nat.exists_infinite_primes (2 ^ (r + 1) * r * B ^ 3 + 1)
  let A := q ^ r
  have hq_pos : 0 < q := hq.pos
  have hA_pos : 0 < A := pow_pos hq_pos r
  have hq_le_A : q ≤ A := Nat.le_self_pow (by omega) q
  have h2r_pos : 0 < 2 ^ r := pow_pos (by omega) r
  have hB_le_B2 : B ≤ B ^ 2 := by
    calc B = B * 1 := by ring
      _ ≤ B * B := Nat.mul_le_mul_left B hB_pos
      _ = B ^ 2 := by ring
  have hB2_le_B3 : B ^ 2 ≤ B ^ 3 := by
    calc B ^ 2 = B ^ 2 * 1 := by ring
      _ ≤ B ^ 2 * B := Nat.mul_le_mul_left (B ^ 2) hB_pos
      _ = B ^ 3 := by ring
  have hB_le_B3 : B ≤ B ^ 3 := le_trans hB_le_B2 hB2_le_B3
  have hA_gt : 2 ^ (r + 1) * r * B ^ 3 < A := lt_of_lt_of_le (by omega) hq_le_A
  have h2B_lt_A : 2 * B < A := by
    have h1 : 2 * B ≤ 2 ^ (r + 1) * r * B ^ 3 := by
      calc 2 * B = 2 * 1 * B := by ring
        _ ≤ 2 ^ (r + 1) * r * B ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul
              (by calc 2 = 2 ^ 1 := by ring
                    _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega))
              (by omega)) hB_le_B3
    omega
  have h2rB3_lt_A : 2 ^ r * B ^ 3 < A := by
    have h1 : 2 ^ r * B ^ 3 ≤ 2 ^ (r + 1) * r * B ^ 3 := by
      calc 2 ^ r * B ^ 3 = 2 ^ r * 1 * B ^ 3 := by ring
        _ ≤ 2 ^ (r + 1) * r * B ^ 3 :=
            Nat.mul_le_mul (Nat.mul_le_mul
              (Nat.pow_le_pow_right (by omega) (by omega)) (by omega)) le_rfl
    omega
  have hA_le_A2 : A ≤ A ^ 2 := by
    calc A = A * 1 := by ring
      _ ≤ A * A := Nat.mul_le_mul_left A hA_pos
      _ = A ^ 2 := by ring
  let v : ℕ → ℕ := fun k =>
    2 * r.choose (2 * k + 3) * A ^ (r - (2 * k + 3)) * B ^ (2 * k + 3)
  let u : ℕ → ℕ := fun i =>
    2 ^ i * (2 * r * A ^ (r - 1) * M ^ r)
  let term : ℕ → ℕ := fun idx =>
    if idx < m - 1 then v (m - 2 - idx)
    else if idx < r - 3 then u (idx - (m - 1))
    else (A - B) ^ r
  -- Stepwise strict monotonicity of term on range (r - 2)
  have hstep : ∀ idx, idx + 1 < r - 2 → term idx < term (idx + 1) := by
    intro idx hidx
    by_cases h1 : idx + 1 < m - 1
    · have h0 : idx < m - 1 := by omega
      dsimp [term]
      rw [if_pos h0, if_pos h1]
      set k := m - 2 - (idx + 1)
      have hk_succ : m - 2 - idx = k + 1 := by omega
      rw [hk_succ]
      dsimp [v]
      set j := 2 * k + 3
      have hj2_le : j + 2 ≤ r := by omega
      have hj_eq : 2 * (k + 1) + 3 = j + 2 := by omega
      rw [hj_eq]
      have hpowA : A ^ (r - j) = A ^ (r - (j + 2)) * A ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      have hpowB : B ^ (j + 2) = B ^ j * B ^ 2 := pow_add B j 2
      have hc_hi : r.choose (j + 2) ≤ 2 ^ r := choose_le_two_pow r (j + 2) hj2_le
      have hc_lo : 1 ≤ r.choose j := Nat.choose_pos (by omega)
      have hfront : r.choose (j + 2) * B ^ 2 < r.choose j * A ^ 2 := by
        have hle1 : r.choose (j + 2) * B ^ 2 ≤ 2 ^ r * B ^ 3 := Nat.mul_le_mul hc_hi hB2_le_B3
        have hle2 : A ^ 2 ≤ r.choose j * A ^ 2 := by
          calc A ^ 2 = 1 * A ^ 2 := by ring
            _ ≤ r.choose j * A ^ 2 := Nat.mul_le_mul_right (A ^ 2) hc_lo
        omega
      have hcommon_pos : 0 < 2 * A ^ (r - (j + 2)) * B ^ j :=
        Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hA_pos _)) (pow_pos hB_pos j)
      calc 2 * r.choose (j + 2) * A ^ (r - (j + 2)) * B ^ (j + 2)
          = r.choose (j + 2) * B ^ 2 * (2 * A ^ (r - (j + 2)) * B ^ j) := by rw [hpowB]; ring
        _ < r.choose j * A ^ 2 * (2 * A ^ (r - (j + 2)) * B ^ j) :=
            Nat.mul_lt_mul_of_pos_right hfront hcommon_pos
        _ = 2 * r.choose j * A ^ (r - j) * B ^ j := by rw [hpowA]; ring
    · by_cases h0 : idx < m - 1
      · have hidx_eq : idx = m - 2 := by omega
        have h1_lt : idx + 1 < r - 3 := by omega
        dsimp [term]
        rw [if_pos h0, if_neg h1, if_pos h1_lt]
        have hk0 : m - 2 - idx = 0 := by omega
        have hi0 : idx + 1 - (m - 1) = 0 := by omega
        rw [hk0, hi0]
        dsimp [v, u]
        have hpowA : A ^ (r - 1) = A ^ (r - 3) * A ^ 2 := by
          rw [← pow_add]
          congr 1
          omega
        have hc3 : r.choose 3 ≤ 2 ^ r := choose_le_two_pow r 3 (by omega)
        have hfront : r.choose 3 * B ^ 3 < r * A ^ 2 * M ^ r := by
          have hle1 : r.choose 3 * B ^ 3 ≤ 2 ^ r * B ^ 3 := Nat.mul_le_mul_right (B ^ 3) hc3
          have hle2 : A ^ 2 ≤ r * A ^ 2 * M ^ r := by
            calc A ^ 2 = 1 * A ^ 2 * 1 := by ring
              _ ≤ r * A ^ 2 * M ^ r :=
                  Nat.mul_le_mul (Nat.mul_le_mul_right (A ^ 2) (by omega)) hMr_pos
          omega
        have hcommon_pos : 0 < 2 * A ^ (r - 3) := Nat.mul_pos (by omega) (pow_pos hA_pos _)
        calc 2 * r.choose 3 * A ^ (r - 3) * B ^ 3
            = r.choose 3 * B ^ 3 * (2 * A ^ (r - 3)) := by ring
          _ < r * A ^ 2 * M ^ r * (2 * A ^ (r - 3)) :=
              Nat.mul_lt_mul_of_pos_right hfront hcommon_pos
          _ = 2 ^ 0 * (2 * r * A ^ (r - 1) * M ^ r) := by rw [hpowA]; ring
      · by_cases h2 : idx + 1 < r - 3
        · have h2' : idx < r - 3 := by omega
          dsimp [term]
          rw [if_neg h0, if_pos h2', if_neg h1, if_pos h2]
          set i := idx - (m - 1)
          have hi_succ : idx + 1 - (m - 1) = i + 1 := by omega
          rw [hi_succ]
          dsimp [u]
          have hpow2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
          have hcommon_pos : 0 < 2 * r * A ^ (r - 1) * M ^ r :=
            Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hA_pos _)) hMr_pos
          exact Nat.mul_lt_mul_of_pos_right hpow2 hcommon_pos
        · have hidx_eq : idx + 1 = r - 3 := by omega
          have h2' : idx < r - 3 := by omega
          dsimp [term]
          rw [if_neg h0, if_pos h2', if_neg h1, if_neg h2]
          have hi_eq : idx - (m - 1) = s - 1 := by omega
          rw [hi_eq]
          dsimp [u]
          have h2s1_le_D : 2 ^ (s - 1) ≤ D := by
            have hpow_s : 2 * 2 ^ (s - 1) = 2 ^ s := by
              calc 2 * 2 ^ (s - 1) = 2 ^ 1 * 2 ^ (s - 1) := by ring
                _ = 2 ^ (1 + (s - 1)) := (pow_add 2 1 (s - 1)).symm
                _ = 2 ^ s := by congr 1; omega
            have h2s1_pos : 0 < 2 ^ (s - 1) := pow_pos (by omega) _
            have hD_def : D = 2 ^ s - 1 := rfl
            omega
          have hu_le : 2 ^ (s - 1) * (2 * r * A ^ (r - 1) * M ^ r) ≤ 2 * r * B * A ^ (r - 1) := by
            calc 2 ^ (s - 1) * (2 * r * A ^ (r - 1) * M ^ r)
                ≤ D * (2 * r * A ^ (r - 1) * M ^ r) := Nat.mul_le_mul_right _ h2s1_le_D
              _ = 2 * r * (D * M ^ r) * A ^ (r - 1) := by ring
              _ = 2 * r * B * A ^ (r - 1) := rfl
          have hA_le_2AB : A ≤ 2 * (A - B) := by omega
          have hAr_le : A ^ r ≤ 2 ^ r * (A - B) ^ r := by
            calc A ^ r ≤ (2 * (A - B)) ^ r := Nat.pow_le_pow_left hA_le_2AB r
              _ = 2 ^ r * (A - B) ^ r := by ring
          have hmul_lt : 2 ^ r * (2 * r * B) < A := by
            have hpow_r1 : 2 ^ r * 2 = 2 ^ (r + 1) := by ring
            have hle_B3 : 2 ^ (r + 1) * r * B ≤ 2 ^ (r + 1) * r * B ^ 3 :=
              Nat.mul_le_mul_left _ hB_le_B3
            have heq : 2 ^ r * (2 * r * B) = 2 ^ (r + 1) * r * B := by
              calc 2 ^ r * (2 * r * B) = (2 ^ r * 2) * r * B := by ring
                _ = 2 ^ (r + 1) * r * B := by rw [hpow_r1]
            omega
          have hscaled : 2 ^ r * (2 ^ (s - 1) * (2 * r * A ^ (r - 1) * M ^ r)) <
              2 ^ r * (A - B) ^ r := by
            calc 2 ^ r * (2 ^ (s - 1) * (2 * r * A ^ (r - 1) * M ^ r))
                ≤ 2 ^ r * (2 * r * B * A ^ (r - 1)) := Nat.mul_le_mul_left (2 ^ r) hu_le
              _ = (2 ^ r * (2 * r * B)) * A ^ (r - 1) := by ring
              _ < A * A ^ (r - 1) := Nat.mul_lt_mul_of_pos_right hmul_lt (pow_pos hA_pos _)
              _ = A ^ (1 + (r - 1)) := by rw [pow_add, pow_one]
              _ = A ^ r := by congr 1; omega
              _ ≤ 2 ^ r * (A - B) ^ r := hAr_le
          by_contra hge
          have hcontra : 2 ^ r * (A - B) ^ r ≤
              2 ^ r * (2 ^ (s - 1) * (2 * r * A ^ (r - 1) * M ^ r)) :=
            Nat.mul_le_mul_left (2 ^ r) (by omega)
          omega
  have hinj : Set.InjOn term (Finset.range (r - 2)) :=
    injOn_range_of_step term (r - 2) hstep
  let S := (Finset.range (r - 2)).image term
  refine ⟨S, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. S.card = r - 2
    dsimp [S]
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · -- 2. S.Coprime
    unfold Finset.Coprime
    set g := S.gcd id
    have hu0_mem : u 0 ∈ S := by
      have hmem : m - 1 ∈ Finset.range (r - 2) := Finset.mem_range.mpr (by omega)
      have ht : term (m - 1) = u 0 := by
        dsimp [term]
        rw [if_neg (by omega), if_pos (by omega), Nat.sub_self]
      rw [← ht]
      exact Finset.mem_image_of_mem term hmem
    have hdiff_mem : (A - B) ^ r ∈ S := by
      have hmem : r - 3 ∈ Finset.range (r - 2) := Finset.mem_range.mpr (by omega)
      have ht : term (r - 3) = (A - B) ^ r := by
        dsimp [term]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [← ht]
      exact Finset.mem_image_of_mem term hmem
    have hg_u0 : g ∣ u 0 := Finset.gcd_dvd hu0_mem
    have hg_diff : g ∣ (A - B) ^ r := Finset.gcd_dvd hdiff_mem
    by_contra hg1
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
    have hp_AB : p ∣ A - B := hp.dvd_of_dvd_pow (hpg.trans hg_diff)
    have hp_u0 : p ∣ (2 * r * M ^ r) * A ^ (r - 1) := by
      have hu0_eq : u 0 = (2 * r * M ^ r) * A ^ (r - 1) := by dsimp [u]; ring
      rw [← hu0_eq]
      exact hpg.trans hg_u0
    have hq_dvd_B : q ∣ B := by
      rcases hp.dvd_mul.mp hp_u0 with h2rM | hAr1
      · have hp_M : p ∣ M := by
          rcases hp.dvd_mul.mp h2rM with h2r | hMr
          · rcases hp.dvd_mul.mp h2r with h2 | hr_dvd
            · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
            · exact dvd_mul_of_dvd_left
                (dvd_mul_of_dvd_right (hr_dvd.trans (Nat.dvd_factorial (by omega) le_rfl)) _) _
          · exact hp.dvd_of_dvd_pow hMr
        have hM_dvd_Mr : M ∣ M ^ r :=
          ⟨M ^ (r - 1), by
            conv_lhs => rw [show r = 1 + (r - 1) by omega, pow_add, pow_one]⟩
        have hp_B : p ∣ B := dvd_mul_of_dvd_right (hp_M.trans hM_dvd_Mr) D
        have hp_A : p ∣ A := by
          have hsum_AB : A - B + B = A := by omega
          rw [← hsum_AB]
          exact dvd_add hp_AB hp_B
        have hp_q : p ∣ q := hp.dvd_of_dvd_pow hp_A
        have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hp_q
        rwa [← hp_eq_q]
      · have hp_A : p ∣ A := hp.dvd_of_dvd_pow hAr1
        have hp_q : p ∣ q := hp.dvd_of_dvd_pow hp_A
        have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hp_q
        rw [hp_eq_q] at hp_AB hp_A
        have hsum_AB : A - B + B = A := by omega
        rw [← hsum_AB] at hp_A
        exact (Nat.dvd_add_right hp_AB).mp hp_A
    have hq_le_B : q ≤ B := Nat.le_of_dvd hB_pos hq_dvd_B
    have hB_lt_q : B < q := by
      have h1 : B ≤ 2 ^ (r + 1) * r * B ^ 3 := by
        calc B ≤ B ^ 3 := hB_le_B3
          _ = 1 * 1 * B ^ 3 := by ring
          _ ≤ 2 ^ (r + 1) * r * B ^ 3 :=
              Nat.mul_le_mul (Nat.mul_le_mul (pow_pos (by omega : 0 < 2) (r + 1)) (by omega)) le_rfl
      omega
    omega
  · -- 3. r.Full (∑ s ∈ S, s)
    have hsum_eq : (∑ x ∈ S, x) = (A + B) ^ r := by
      dsimp [S]
      rw [Finset.sum_image hinj]
      rw [show r - 2 = (r - 3) + 1 by omega, Finset.sum_range_succ]
      have ht_last : term (r - 3) = (A - B) ^ r := by
        dsimp [term]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [ht_last, ← hlen, sum_range_add_eq term (m - 1) s]
      have hpart1 : (∑ idx ∈ Finset.range (m - 1), term idx) =
          ∑ k ∈ Finset.range (m - 1), v k := by
        have hcongr : (∑ idx ∈ Finset.range (m - 1), term idx) =
            ∑ idx ∈ Finset.range (m - 1), v ((m - 1) - 1 - idx) := by
          refine Finset.sum_congr rfl fun idx hidx => ?_
          have hlt : idx < m - 1 := Finset.mem_range.mp hidx
          dsimp [term]
          rw [if_pos hlt]
          rfl
        rw [hcongr, sum_range_rev v (m - 1)]
      have hpart2 : (∑ i ∈ Finset.range s, term ((m - 1) + i)) =
          2 * r.choose 1 * A ^ (r - 1) * B ^ 1 := by
        have hcongr : (∑ i ∈ Finset.range s, term ((m - 1) + i)) =
            ∑ i ∈ Finset.range s, u i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hlt : i < s := Finset.mem_range.mp hi
          dsimp [term]
          rw [if_neg (by omega), if_pos (by omega)]
          congr 1
          omega
        rw [hcongr]
        dsimp [u]
        rw [← Finset.sum_mul, hD_sum, Nat.choose_one_right]
        dsimp [B]
        ring
      rw [hpart1, hpart2]
      have hbinom := binom_odd_sum A B r (by omega)
      have hm_eq : (r + 1) / 2 = (m - 1) + 1 := by omega
      rw [hm_eq, Finset.sum_range_succ'] at hbinom
      have hbinom_v : (∑ k ∈ Finset.range (m - 1),
          2 * r.choose (2 * (k + 1) + 1) * A ^ (r - (2 * (k + 1) + 1)) * B ^ (2 * (k + 1) + 1)) =
          ∑ k ∈ Finset.range (m - 1), v k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp [v]
        have h2k : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
        rw [h2k]
      rw [hbinom_v] at hbinom
      simp only [mul_zero, zero_add] at hbinom
      omega
    rw [hsum_eq]
    exact full_pow r (A + B)
  · -- 4. ∀ x ∈ S, 0 < x ∧ r.Full x
    intro x hx
    obtain ⟨idx, hidx_mem, rfl⟩ := Finset.mem_image.mp hx
    have hidx : idx < r - 2 := Finset.mem_range.mp hidx_mem
    dsimp [term]
    split_ifs with h1 h2
    · set k := m - 2 - idx
      set j := 2 * k + 3
      have hj_le : j ≤ r := by omega
      dsimp [v]
      change 0 < 2 * r.choose j * A ^ (r - j) * B ^ j ∧
        r.Full (2 * r.choose j * A ^ (r - j) * B ^ j)
      refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.choose_pos hj_le))
        (pow_pos hA_pos _)) (pow_pos hB_pos j), ?_⟩
      have hv_eq : 2 * r.choose j * A ^ (r - j) * B ^ j =
          (2 * r.choose j * D ^ j) * (q ^ (r - j) * M ^ j) ^ r := by
        dsimp [A, B]
        rw [mul_pow D (M ^ r) j, mul_pow (q ^ (r - j)) (M ^ j) r,
          ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
          mul_comm r (r - j), mul_comm r j]
        ring
      rw [hv_eq]
      refine full_mul_pow r (2 * r.choose j * D ^ j) (q ^ (r - j) * M ^ j) ?_
      intro p hp hdvd
      have hp_M : p ∣ M := dvd_M_of_prime_dvd_choose r j D p hj_le hp hdvd
      have hM_Mj : M ∣ M ^ j :=
        ⟨M ^ (j - 1), by
          conv_lhs => rw [show j = 1 + (j - 1) by omega, pow_add, pow_one]⟩
      exact dvd_mul_of_dvd_right (hp_M.trans hM_Mj) _
    · set i := idx - (m - 1)
      dsimp [u]
      refine ⟨Nat.mul_pos (pow_pos (by omega) i)
        (Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hA_pos _)) hMr_pos), ?_⟩
      have hu_eq : 2 ^ i * (2 * r * A ^ (r - 1) * M ^ r) =
          (2 ^ (i + 1) * r) * (q ^ (r - 1) * M) ^ r := by
        dsimp [A]
        rw [mul_pow (q ^ (r - 1)) M r, ← pow_mul, ← pow_mul, mul_comm r (r - 1),
          pow_add 2 i 1, pow_one]
        ring
      rw [hu_eq]
      refine full_mul_pow r (2 ^ (i + 1) * r) (q ^ (r - 1) * M) ?_
      intro p hp hdvd
      have hp_M : p ∣ M := by
        rcases hp.dvd_mul.mp hdvd with h2i | hr_dvd
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow h2i) _) _
        · exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right (hr_dvd.trans (Nat.dvd_factorial (by omega) le_rfl)) _) _
      exact dvd_mul_of_dvd_right hp_M _
    · exact ⟨pow_pos (by omega) r, full_pow r (A - B)⟩

theorem OMA.solution : OMA.R_Erdos939_erdos_939_R1.H2 :=
  prove_Erdos939_H2
