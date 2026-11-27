import FormalConjectures.ErdosProblems.«878»

-- Problem: Erdős Problem 878 — H lower quadruple log infinitely often
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/878.lean (declaration Erdos878.erdos_878.variants.H_lower_quadruple_log_infinitely_often)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Proof: pigeonhole (Dirichlet) gives x = 3 * 2^j lying within a factor 2..4 of a power of every
-- prime p in [5, y]; each such p then contributes x/(16p) to H(x), and sum 1/p >> log log y is
-- proved from the Chebyshev bounds on 4-adic blocks; finally log log log log x << log log y.

open Finset Real

namespace E878

lemma card_Ioc_dvd (a b d : ℕ) (hab : a ≤ b) :
    #{x ∈ Ioc a b | d ∣ x} = b / d - a / d := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div b d
  have h2 := Nat.Ioc_filter_dvd_card_eq_div a d
  have hu : Ioc 0 a ∪ Ioc a b = Ioc 0 b := Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab
  have hdisj : Disjoint ({x ∈ Ioc 0 a | d ∣ x}) ({x ∈ Ioc a b | d ∣ x}) := by
    apply Finset.disjoint_filter_filter
    exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have : #{x ∈ Ioc 0 b | d ∣ x} = #{x ∈ Ioc 0 a | d ∣ x} + #{x ∈ Ioc a b | d ∣ x} := by
    rw [← card_union_of_disjoint hdisj, ← filter_union, hu]
  omega

lemma card_Ioc_dvd_ge (a b d : ℕ) (hab : a ≤ b) (hd : 0 < d) :
    ((b : ℝ) - a) / d - 1 ≤ (#{x ∈ Ioc a b | d ∣ x} : ℝ) := by
  rw [card_Ioc_dvd _ _ _ hab]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have k1 := Nat.div_add_mod b d
  have k2 := Nat.div_add_mod a d
  have k3 := Nat.mod_lt a hd
  have k4 := Nat.mod_lt b hd
  have hle : a / d ≤ b / d := Nat.div_le_div_right hab
  have : b ≤ (b / d - a / d) * d + a + d := by
    rw [Nat.sub_mul]
    have := Nat.mul_comm d (b / d)
    have := Nat.mul_comm d (a / d)
    have : a / d * d ≤ b / d * d := Nat.mul_le_mul_right _ hle
    omega
  have hc : (b : ℝ) ≤ (((b / d - a / d : ℕ)) : ℝ) * d + a + d := by exact_mod_cast this
  rw [sub_le_iff_le_add, div_le_iff₀ hdR]
  linarith

lemma H_ge (x : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, ∑ n ∈ (Ico 1 x).filter (p ∣ ·), ((p ^ Nat.log p n : ℕ) : ℝ) / n ≤ Erdos878.H x := by
  unfold Erdos878.H Erdos878.f
  push_cast
  simp_rw [sum_div]
  calc ∑ p ∈ S, ∑ n ∈ (Ico 1 x).filter (p ∣ ·), ((p : ℝ) ^ Nat.log p n) / n
      = ∑ n ∈ Ico 1 x, ∑ p ∈ S.filter (· ∣ n), ((p : ℝ) ^ Nat.log p n) / n := by
        simp_rw [sum_filter]; rw [sum_comm]
    _ ≤ _ := by
        refine sum_le_sum fun n hn => ?_
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp
          rw [Nat.mem_primeFactors]
          exact ⟨hS p hp.1, hp.2, by have := (mem_Ico.1 hn).1; omega⟩
        · intros; positivity

lemma contrib (p K x : ℕ) (hp : p.Prime) (h1 : 2 * p ^ K ≤ x) (h2 : x ≤ 4 * p ^ K)
    (h16 : 16 * p ≤ x) :
    (x : ℝ) / (16 * p) ≤ ∑ n ∈ (Ico 1 x).filter (p ∣ ·), ((p ^ Nat.log p n : ℕ) : ℝ) / n := by
  set T := (Ioc (p ^ K) (x - 1)).filter (p ∣ ·) with hT
  have hp2 := hp.two_le
  have hpK : 1 ≤ p ^ K := Nat.one_le_pow _ _ (by omega)
  have hsub : T ⊆ (Ico 1 x).filter (p ∣ ·) := by
    intro n hn
    simp only [hT, mem_filter, mem_Ioc, mem_Ico] at hn ⊢
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hterm : ∀ n ∈ T, (1 : ℝ) / 4 ≤ ((p ^ Nat.log p n : ℕ) : ℝ) / n := by
    intro n hn
    simp only [hT, mem_filter, mem_Ioc] at hn
    have hlog : K ≤ Nat.log p n := Nat.le_log_of_pow_le (by omega) (by omega)
    have hpow : p ^ K ≤ p ^ Nat.log p n := Nat.pow_le_pow_right (by omega) hlog
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_le_div_iff₀ (by norm_num) hn0]
    have : (n : ℝ) ≤ x := by exact_mod_cast (show n ≤ x by omega)
    have : (x : ℝ) ≤ 4 * p ^ K := by exact_mod_cast h2
    have : ((p ^ K : ℕ) : ℝ) ≤ ((p ^ Nat.log p n : ℕ) : ℝ) := by exact_mod_cast hpow
    push_cast at *
    linarith
  have hsumT : (#T : ℝ) / 4 ≤ ∑ n ∈ T, ((p ^ Nat.log p n : ℕ) : ℝ) / n := by
    have := sum_le_sum hterm
    simp only [sum_const, nsmul_eq_mul] at this
    linarith
  have hmono : ∑ n ∈ T, ((p ^ Nat.log p n : ℕ) : ℝ) / n ≤
      ∑ n ∈ (Ico 1 x).filter (p ∣ ·), ((p ^ Nat.log p n : ℕ) : ℝ) / n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hcard := card_Ioc_dvd_ge (p ^ K) (x - 1) p (by omega) (by omega)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hx1 : ((x - 1 : ℕ) : ℝ) = x - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hx1] at hcard
  have h1R : 2 * ((p ^ K : ℕ) : ℝ) ≤ x := by exact_mod_cast h1
  have h16R : 16 * (p : ℝ) ≤ x := by exact_mod_cast h16
  have key : (x : ℝ) / (4 * p) ≤ (#T : ℝ) := by
    refine le_trans ?_ hcard
    rw [div_le_iff₀ (by positivity)]
    rw [sub_mul, div_mul_eq_mul_div, mul_div_assoc]
    have e : (4 * (p : ℝ)) / p = 4 := by field_simp
    rw [e]
    nlinarith
  have : (x : ℝ) / (16 * p) = (x / (4 * p)) / 4 := by field_simp; ring
  rw [this]
  linarith


def M (p : ℕ) : ℕ := 4 * (Nat.log 2 p + 1)

lemma M_pos (p : ℕ) : 0 < M p := by unfold M; omega

lemma log_div_M {p : ℕ} (hp : 2 ≤ p) : log p / M p < log 2 / 4 := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h' : (p : ℝ) < (2 : ℝ) ^ (Nat.log 2 p + 1) := by exact_mod_cast h
  have hl : log p < (Nat.log 2 p + 1 : ℕ) * log 2 := by
    rw [← Real.log_pow]; exact Real.log_lt_log hpR h'
  have hM : ((M p : ℕ) : ℝ) = 4 * ((Nat.log 2 p + 1 : ℕ) : ℝ) := by unfold M; push_cast; ring
  rw [hM, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

lemma approx (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ∏ p ∈ S, M p ∧ ∀ p ∈ S, ∃ K : ℕ,
      p ^ (4 * K) < 2 * 2 ^ (4 * j) ∧ 2 ^ (4 * j) < 2 * p ^ (4 * K) := by
  classical
  set N := ∏ p ∈ S, M p with hN
  let α : ℕ → ℝ := fun p => log 2 / log p
  let θ : ℕ → ℕ → ℝ := fun j p => Int.fract ((j : ℝ) * α p)
  let F : ℕ → (S → ℕ) := fun j p => ⌊(M p : ℝ) * θ j p⌋₊
  let T : Finset (S → ℕ) := Fintype.piFinset fun p : S => range (M p)
  have hT : #T = N := by
    simp only [T, Fintype.card_piFinset, card_range, hN]
    exact prod_coe_sort S M
  have hmaps : ∀ j ∈ range (N + 1), F j ∈ T := by
    intro j _
    simp only [T, Fintype.mem_piFinset, mem_range, F]
    intro p
    have hθ := Int.fract_lt_one ((j : ℝ) * α p)
    have hθ0 := Int.fract_nonneg ((j : ℝ) * α p)
    have hMp : (0 : ℝ) < M p := by exact_mod_cast M_pos p
    rw [Nat.floor_lt (by positivity)]
    nlinarith
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hT, card_range]; omega) hmaps
  -- wlog j1 < j2
  have main : ∀ a b, a ∈ range (N + 1) → b ∈ range (N + 1) → a < b → F a = F b →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ N ∧ ∀ p ∈ S, ∃ K : ℕ,
        p ^ (4 * K) < 2 * 2 ^ (4 * j) ∧ 2 ^ (4 * j) < 2 * p ^ (4 * K) := by
    intro a b ha hb hab hF
    refine ⟨b - a, by omega, by simp at ha hb; omega, fun p hp => ?_⟩
    have hp2 := hS p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have hlogp : 0 < log p := Real.log_pos hpR
    have hα : 0 < α p := div_pos (Real.log_pos (by norm_num)) hlogp
    have hMp : (0 : ℝ) < M p := by exact_mod_cast M_pos p
    have hbin := congrFun hF ⟨p, hp⟩
    simp only [F] at hbin
    set u := (M p : ℝ) * θ a p with hu
    set v := (M p : ℝ) * θ b p with hv
    have hu0 : 0 ≤ u := mul_nonneg hMp.le (Int.fract_nonneg _)
    have hv0 : 0 ≤ v := mul_nonneg hMp.le (Int.fract_nonneg _)
    have h1 := Nat.floor_le hu0
    have h2 := Nat.lt_floor_add_one u
    have h3 := Nat.floor_le hv0
    have h4 := Nat.lt_floor_add_one v
    rw [hbin] at h1 h2
    have huv : |θ b p - θ a p| < 1 / M p := by
      rw [abs_lt]
      have e : (1 : ℝ) / M p * M p = 1 := by field_simp
      constructor
      · rw [neg_lt, ← sub_neg, ← mul_lt_mul_iff_of_pos_right hMp]; nlinarith
      · rw [← mul_lt_mul_iff_of_pos_right hMp]; nlinarith
    set Kz : ℤ := ⌊(b : ℝ) * α p⌋ - ⌊(a : ℝ) * α p⌋ with hKz
    have hK0 : 0 ≤ Kz := by
      rw [hKz, sub_nonneg]
      apply Int.floor_mono
      have : (a : ℝ) ≤ b := by exact_mod_cast hab.le
      nlinarith
    refine ⟨Kz.toNat, ?_⟩
    have hKR : ((Kz.toNat : ℕ) : ℝ) = (Kz : ℝ) := by
      rw [show ((Kz.toNat : ℕ) : ℝ) = ((Kz.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg hK0]
    have hdiff : ((b - a : ℕ) : ℝ) * α p - Kz = θ b p - θ a p := by
      have e1 := Int.floor_add_fract ((b : ℝ) * α p)
      have e2 := Int.floor_add_fract ((a : ℝ) * α p)
      rw [Nat.cast_sub hab.le, hKz]
      push_cast
      simp only [θ]
      linarith
    have hbound : |((b - a : ℕ) : ℝ) * log 2 - (Kz.toNat : ℕ) * log p| < log 2 / 4 := by
      have : ((b - a : ℕ) : ℝ) * log 2 - (Kz.toNat : ℕ) * log p
          = log p * (((b - a : ℕ) : ℝ) * α p - Kz) := by
        rw [hKR]; simp only [α]; field_simp
      rw [this, abs_mul, abs_of_pos hlogp, hdiff]
      calc log p * |θ b p - θ a p| < log p * (1 / M p) :=
            mul_lt_mul_of_pos_left huv hlogp
        _ = log p / M p := by ring
        _ < log 2 / 4 := log_div_M hp2
    rw [abs_lt] at hbound
    set J := b - a
    set K := Kz.toNat
    have hppos : (0 : ℝ) < p := by linarith
    have l1 : log ((p : ℝ) ^ (4 * K)) = 4 * (K * log p) := by
      rw [Real.log_pow]; push_cast; ring
    have l2 : log ((2 : ℝ) ^ (4 * J)) = 4 * (J * log 2) := by
      rw [Real.log_pow]; push_cast; ring
    constructor
    · have : log ((p : ℝ) ^ (4 * K)) < log (2 * (2 : ℝ) ^ (4 * J)) := by
        rw [Real.log_mul (by norm_num) (by positivity), l1, l2]; linarith
      have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 this
      exact_mod_cast this
    · have : log ((2 : ℝ) ^ (4 * J)) < log (2 * (p : ℝ) ^ (4 * K)) := by
        rw [Real.log_mul (by norm_num) (by positivity), l1, l2]; linarith
      have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 this
      exact_mod_cast this
  rcases lt_or_gt_of_ne hne with h | h
  · exact main j1 j2 hj1 hj2 h heq
  · exact main j2 j1 hj2 hj1 h heq.symm


lemma log4_gt : (1 : ℝ) < log 4 := by
  have : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

open Filter in
lemma block_count : ∃ k0 : ℕ, 18 ≤ k0 ∧ ∀ k ≥ k0,
    (4 : ℝ) ^ k / (2 * k) ≤ (Nat.primeCounting (4 ^ (k + 1)) : ℝ) - Nat.primeCounting (4 ^ k) := by
  have hev := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 0.1) (by norm_num))
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 18))
  refine ⟨k1 + 18, by omega, fun k hk => ?_⟩
  have hk' := (hk1 k (by omega)).1
  have hk18 : (18 : ℝ) ≤ k := by exact_mod_cast (show 18 ≤ k by omega)
  set Q : ℝ := (4 : ℝ) ^ k with hQ
  have hfl : ⌊(4 : ℝ) ^ k⌋₊ = 4 ^ k := by
    rw [show ((4 : ℝ) ^ k) = ((4 ^ k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hfl] at hk'
  have hl4 := log4_gt
  have hlogQ : log Q = k * log 4 := by rw [hQ, Real.log_pow]
  rw [hlogQ] at hk'
  set A : ℝ := (Nat.primeCounting (4 ^ (k + 1)) : ℝ)
  set B : ℝ := (Nat.primeCounting (4 ^ k) : ℝ)
  have hkpos : (0 : ℝ) < k := by linarith
  have hB : k * B ≤ 1.1 * Q := by
    have h := hk'
    rw [le_div_iff₀ (by positivity)] at h
    have : (log 4 + 0.1) * Q ≤ 1.1 * Q * log 4 := by
      have : 0 ≤ Q := by positivity
      nlinarith
    have : k * B * log 4 ≤ 1.1 * Q * log 4 := by linarith
    exact le_of_mul_le_mul_right this (by linarith)
  have hA : (k + 1) * A ≥ 2 * Q - 2 * (k + 1) := by
    have h := Chebyshev.pi_ge (4 ^ (k + 1))
    set n : ℕ := 4 ^ (k + 1)
    have hnR : (n : ℝ) = 4 * Q := by simp only [n, hQ]; push_cast; ring
    have hn2 : (2 : ℝ) ≤ n := by rw [hnR]; have : (1 : ℝ) ≤ Q := one_le_pow₀ (by norm_num); linarith
    have hlogn : log (n : ℝ) = (k + 1) * (2 * log 2) := by
      rw [hnR, hQ, ← pow_succ', Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hlogn1 : log ((n : ℝ) + 1) ≤ 2 * log n := by
      have : log ((n : ℝ) + 1) ≤ log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hlnpos : 0 < log (n : ℝ) := by rw [hlogn]; positivity
    rw [div_le_iff₀ hlnpos] at h
    have hAn : (n.primeCounting : ℝ) = A := rfl
    rw [hlogn] at h hlogn1
    rw [hnR] at h hlogn1
    rw [hAn] at h
    have : (k + 1) * A * (2 * log 2) ≥ (2 * Q - 2 * (k + 1)) * (2 * log 2) := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have hQk : 7 * ((k : ℝ) + 1) ≤ Q := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 7 * (k + 1) ≤ 4 ^ k := by
      have : 4 ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      nlinarith
    have : ((7 * (k + 1) : ℕ) : ℝ) ≤ ((4 ^ k : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at this; rw [hQ]; linarith
  rw [div_le_iff₀ (by positivity)]
  -- goal: Q ≤ (A - B) * (2 * k)
  have hQ0 : 0 ≤ Q := by positivity
  nlinarith


noncomputable def sP (z : ℕ) : ℝ := ∑ p ∈ Nat.primesLE z, (1 : ℝ) / p

lemma sP_mono {a b : ℕ} (h : a ≤ b) : sP a ≤ sP b := by
  unfold sP
  apply sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono h)
  intros; positivity

lemma sP_step (k : ℕ) (hk : 1 ≤ k)
    (hblock : (4 : ℝ) ^ k / (2 * k) ≤
      (Nat.primeCounting (4 ^ (k + 1)) : ℝ) - Nat.primeCounting (4 ^ k)) :
    sP (4 ^ k) + 1 / (8 * k) ≤ sP (4 ^ (k + 1)) := by
  unfold sP
  have hsub : Nat.primesLE (4 ^ k) ⊆ Nat.primesLE (4 ^ (k + 1)) :=
    Nat.primesLE_mono (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← sum_sdiff hsub]
  set D := Nat.primesLE (4 ^ (k + 1)) \ Nat.primesLE (4 ^ k)
  have hcard : (#D : ℝ) = (Nat.primeCounting (4 ^ (k + 1)) : ℝ) - Nat.primeCounting (4 ^ k) := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hQ : (0 : ℝ) < 4 ^ (k + 1) := by positivity
  have hterm : ∀ p ∈ D, (1 : ℝ) / 4 ^ (k + 1) ≤ 1 / p := by
    intro p hp
    have hp' := (Nat.mem_primesLE.1 (mem_sdiff.1 hp).1)
    have : (p : ℝ) ≤ 4 ^ (k + 1) := by exact_mod_cast hp'.1
    exact one_div_le_one_div_of_le (by exact_mod_cast hp'.2.pos) this
  have hsum : (#D : ℝ) * (1 / 4 ^ (k + 1)) ≤ ∑ p ∈ D, (1 : ℝ) / p := by
    have := sum_le_sum hterm
    simpa [sum_const, nsmul_eq_mul] using this
  rw [hcard] at hsum
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 1 / (8 * (k : ℝ)) ≤ (4 : ℝ) ^ k / (2 * k) * (1 / 4 ^ (k + 1)) := by
    rw [pow_succ]
    have : (0 : ℝ) < 4 ^ k := by positivity
    field_simp
    ring_nf
    linarith
  have := mul_le_mul_of_nonneg_right hblock (by positivity : (0 : ℝ) ≤ 1 / 4 ^ (k + 1))
  linarith

lemma sP_lower : ∃ k0 : ℕ, 18 ≤ k0 ∧ ∀ m ≥ k0, (log m - log k0) / 8 ≤ sP (4 ^ m) := by
  obtain ⟨k0, hk0, hb⟩ := block_count
  refine ⟨k0, hk0, fun m hm => ?_⟩
  induction m, hm using Nat.le_induction with
  | base => simp only [sub_self, zero_div]; unfold sP; positivity
  | succ m hm ih =>
    have hstep := sP_step m (by omega) (hb m hm)
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlog : log ((m + 1 : ℕ) : ℝ) - log m ≤ 1 / m := by
      rw [← Real.log_div (by positivity) hmR.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      push_cast; field_simp; ring
    have : 1 / (8 * (m : ℝ)) = (1 / m) / 8 := by ring
    linarith

lemma mertens : ∃ k0 : ℕ, 18 ≤ k0 ∧ ∀ z : ℕ, 4 ^ k0 ≤ z →
    (log (log z) - 2 - log k0) / 8 ≤ sP z := by
  obtain ⟨k0, hk0, h⟩ := sP_lower
  refine ⟨k0, hk0, fun z hz => ?_⟩
  set m := Nat.log 4 z
  have hm : k0 ≤ m := Nat.le_log_of_pow_le (by norm_num) hz
  have h4m : 4 ^ m ≤ z := Nat.pow_log_le_self 4 (by have := Nat.one_le_pow k0 4 (by norm_num); omega)
  have hz4 : z < 4 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) z
  have h1 := h m hm
  have h2 := sP_mono h4m
  have hmR : (18 : ℝ) ≤ m := by exact_mod_cast (show 18 ≤ m by omega)
  have hzR : (2 : ℝ) ≤ z := by
    have : 4 ^ 18 ≤ z := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hz
    exact_mod_cast (show 2 ≤ z by omega)
  have hlz : 0 < log (z : ℝ) := Real.log_pos (by linarith)
  have hlz' : log (z : ℝ) < (m + 1) * log 4 := by
    have : (z : ℝ) < (4 : ℝ) ^ (m + 1) := by exact_mod_cast hz4
    have := Real.log_lt_log (by linarith) this
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hl4 := log4_gt
  have hll : log (log (z : ℝ)) ≤ log m + 2 := by
    have : log (log (z : ℝ)) ≤ log ((m + 1) * log 4) := Real.log_le_log hlz hlz'.le
    rw [Real.log_mul (by positivity) (by positivity)] at this
    have a1 : log ((m : ℝ) + 1) ≤ log (2 * m) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at a1
    have a2 : log (log 4) ≤ log 4 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have a3 : log 2 < 0.6931471808 := Real.log_two_lt_d9
    have a4 : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  linarith


lemma pow4_bounds {p K j : ℕ} (h1 : p ^ (4 * K) < 2 * 2 ^ (4 * j))
    (h2 : 2 ^ (4 * j) < 2 * p ^ (4 * K)) : 2 * p ^ K < 3 * 2 ^ j ∧ 3 * 2 ^ j < 4 * p ^ K := by
  constructor
  · have : (2 * p ^ K) ^ 4 < (3 * 2 ^ j) ^ 4 := by
      have e1 : (2 * p ^ K) ^ 4 = 16 * p ^ (4 * K) := by ring
      have e2 : (3 * 2 ^ j) ^ 4 = 81 * 2 ^ (4 * j) := by ring
      rw [e1, e2]; omega
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) this
  · have : (3 * 2 ^ j) ^ 4 < (4 * p ^ K) ^ 4 := by
      have e1 : (4 * p ^ K) ^ 4 = 256 * p ^ (4 * K) := by ring
      have e2 : (3 * 2 ^ j) ^ 4 = 81 * 2 ^ (4 * j) := by ring
      rw [e1, e2]; omega
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) this

lemma four_mul_le (L : ℕ) (hL : 5 ≤ L) : 4 * (L + 1) ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih => rw [pow_succ]; omega

lemma M_le {p y : ℕ} (hy : 64 ≤ y) (hp : p ≤ y) (hp2 : 2 ≤ p) : M p ≤ y := by
  unfold M
  have hL : Nat.log 2 p ≤ Nat.log 2 y := Nat.log_mono_right hp
  have hy' : 2 ^ Nat.log 2 y ≤ y := Nat.pow_log_le_self 2 (by omega)
  have h6 : 6 ≤ Nat.log 2 y := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have := four_mul_le (Nat.log 2 y) (by omega)
  omega

lemma loglog_bound {x N y : ℕ} (hx : x ≤ 4 ^ N) (hN : N ≤ y ^ y) (hx20 : 2 ^ 20 ≤ x)
    (hy : 2 ≤ y) :
    0 < log (log (log (x : ℝ))) ∧
    log (log (log (log (x : ℝ)))) ≤ log 2 + log (log y) := by
  have hl2 := Real.log_two_gt_d9
  have hxR : (2 : ℝ) ^ 20 ≤ x := by exact_mod_cast hx20
  have hx0 : (0 : ℝ) < x := by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) 20]
  have hlx : 13 ≤ log (x : ℝ) := by
    have := Real.log_le_log (by positivity) hxR
    rw [Real.log_pow] at this; push_cast at this; linarith
  have he := Real.exp_one_lt_d9
  have hllx : 1 < log (log (x : ℝ)) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have hlllx : 0 < log (log (log (x : ℝ))) := Real.log_pos hllx
  refine ⟨hlllx, ?_⟩
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hNpos : 1 ≤ N := by
    by_contra h; push Not at h
    have : N = 0 := by omega
    rw [this] at hx; omega
  have hNR : (N : ℝ) ≤ (y : ℝ) ^ y := by exact_mod_cast hN
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hl4 := log4_gt
  have hl4' : log 4 < 2 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  -- log x ≤ 2 N
  have h1 : log (x : ℝ) ≤ 2 * N := by
    have : (x : ℝ) ≤ (4 : ℝ) ^ N := by exact_mod_cast hx
    have := Real.log_le_log hx0 this
    rw [Real.log_pow] at this; nlinarith
  have hlogy : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  -- log log x ≤ log 2 + y log y ≤ y^2
  have h2 : log (log (x : ℝ)) ≤ (y : ℝ) ^ 2 := by
    have a := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at a
    have b := Real.log_le_log (by positivity) hNR
    rw [Real.log_pow] at b
    have c : log (y : ℝ) ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have d : log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have : (y : ℝ) * log y ≤ y * (y - 1) := mul_le_mul_of_nonneg_left c (by linarith)
    nlinarith
  have h3 : log (log (log (x : ℝ))) ≤ 2 * log y := by
    have := Real.log_le_log (by linarith) h2
    rw [Real.log_pow] at this; push_cast at this; linarith
  have := Real.log_le_log hlllx h3
  rw [Real.log_mul (by norm_num) hlogy.ne'] at this
  exact this


open Filter in
theorem main : ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℕ in atTop,
      c * ((x : ℝ) * Real.log (Real.log (Real.log (Real.log (x : ℝ))))) ≤ Erdos878.H x := by
  obtain ⟨k0, hk0, hmert⟩ := mertens
  set C1 : ℝ := 18 + log k0 with hC1
  refine ⟨1 / 256, by norm_num, ?_⟩
  rw [frequently_atTop]
  intro X0
  set z0 : ℕ := ⌈Real.exp (Real.exp (2 * C1 + 2))⌉₊
  set z : ℕ := max X0 (max (4 ^ k0) (max (2 ^ 20) z0)) with hz
  have hzX : X0 ≤ z := le_max_left _ _
  have hz4 : 4 ^ k0 ≤ z := le_trans (le_max_left _ _) (le_max_right _ _)
  have hz20 : 2 ^ 20 ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hz0 : z0 ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)
  set y := 16 * z with hy
  set S := (Nat.primesLE y).filter (5 ≤ ·) with hS
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => by
    have := (mem_filter.1 hp).2; omega
  obtain ⟨j, hj1, hjN, hjK⟩ := approx S hS2
  set x := 3 * 2 ^ j with hx
  -- a large prime in S
  obtain ⟨q, hq, hqlo, hqhi⟩ := Nat.exists_prime_lt_and_le_two_mul (y / 2) (by omega)
  have hqS : q ∈ S := by
    rw [hS, mem_filter, Nat.mem_primesLE]; exact ⟨⟨by omega, hq⟩, by omega⟩
  obtain ⟨Kq, hKq1, hKq2⟩ := hjK q hqS
  have hxq := pow4_bounds hKq1 hKq2
  have hKq : 1 ≤ Kq := by
    by_contra h; push Not at h
    have : Kq = 0 := by omega
    rw [this] at hKq2
    have : 2 ≤ 2 ^ (4 * j) := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
    simp at hKq2; omega
  have hqK : q ≤ q ^ Kq := Nat.le_self_pow (by omega) q
  have hxy : y < x := by omega
  refine ⟨x, by omega, ?_⟩
  -- lower bound on H
  set S' := (Nat.primesLE z).filter (5 ≤ ·) with hS'
  have hS'S : S' ⊆ S := by
    intro p hp
    simp only [hS', hS, mem_filter, Nat.mem_primesLE] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hH1 := H_ge x S' (fun p hp => (Nat.mem_primesLE.1 (mem_filter.1 hp).1).2)
  have hcontrib : ∀ p ∈ S', (x : ℝ) / (16 * p) ≤
      ∑ n ∈ (Ico 1 x).filter (p ∣ ·), ((p ^ Nat.log p n : ℕ) : ℝ) / n := by
    intro p hp
    obtain ⟨K, hK1, hK2⟩ := hjK p (hS'S hp)
    have hb := pow4_bounds hK1 hK2
    have hpz := (Nat.mem_primesLE.1 (mem_filter.1 hp).1)
    exact contrib p K x hpz.2 hb.1.le hb.2.le (by omega)
  have hH2 : (x : ℝ) / 16 * ∑ p ∈ S', (1 : ℝ) / p ≤ Erdos878.H x := by
    refine le_trans ?_ (le_trans (sum_le_sum hcontrib) hH1)
    rw [mul_sum]
    refine sum_le_sum fun p _ => le_of_eq ?_
    ring
  -- sum over S' vs sP z
  have hsP : sP z - 2 ≤ ∑ p ∈ S', (1 : ℝ) / p := by
    unfold sP
    have hsub : Nat.primesLE z ⊆ S' ∪ {2, 3, 4} := by
      intro p hp
      rw [mem_union, hS', mem_filter]
      by_cases h5 : 5 ≤ p
      · exact Or.inl ⟨hp, h5⟩
      · right
        have := (Nat.mem_primesLE.1 hp).2.two_le
        simp; omega
    have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      (f := fun p : ℕ => (1 : ℝ) / p)
    have h2 := sum_union_inter (s₁ := S') (s₂ := {2, 3, 4}) (f := fun p : ℕ => (1 : ℝ) / p)
    have h4 : 0 ≤ ∑ p ∈ S' ∩ {2, 3, 4}, (1 : ℝ) / (p : ℝ) := sum_nonneg fun _ _ => by positivity
    have h3 : ∑ p ∈ ({2, 3, 4} : Finset ℕ), (1 : ℝ) / (p : ℝ) ≤ 2 := by norm_num
    linarith
  have hm := hmert z hz4
  -- size of x
  have hN : ∏ p ∈ S, M p ≤ y ^ y := by
    have h1 : ∏ p ∈ S, M p ≤ y ^ #S := prod_le_pow_card S M y (fun p hp => by
      have hpS := mem_filter.1 hp
      exact M_le (by omega) (Nat.mem_primesLE.1 hpS.1).1 (by omega))
    have h2 : #S ≤ y := by
      have : S ⊆ Icc 1 y := by
        intro p hp
        have hpS := mem_filter.1 hp
        have := (Nat.mem_primesLE.1 hpS.1).1
        rw [mem_Icc]; omega
      simpa using card_le_card this
    exact h1.trans (Nat.pow_le_pow_right (by omega) h2)
  have hx4 : x ≤ 4 ^ (∏ p ∈ S, M p) := by
    have hj4 : 4 ≤ 2 ^ j := by omega
    have : 3 * 2 ^ j ≤ 4 ^ j := by
      have : 4 ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
      rw [this]; nlinarith
    exact this.trans (Nat.pow_le_pow_right (by norm_num) hjN)
  obtain ⟨hpos3, hlog4⟩ := loglog_bound hx4 hN (by omega) (by omega)
  -- relate log log y to log log z
  have hzR : (2 : ℝ) ^ 20 ≤ z := by exact_mod_cast hz20
  have hz1 : (1 : ℝ) < z := by linarith [one_le_pow₀ (M₀ := ℝ) (n := 20) (by norm_num : (1:ℝ) ≤ 2)]
  have hlz : 0 < log (z : ℝ) := Real.log_pos hz1
  have hyy : log (log (y : ℝ)) ≤ log 2 + log (log z) := by
    have hyR : (y : ℝ) = 16 * z := by rw [hy]; push_cast; ring
    have a : log (y : ℝ) ≤ 2 * log z := by
      rw [hyR, Real.log_mul (by norm_num) (by positivity)]
      have : log (16 : ℝ) ≤ log z := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have b := Real.log_le_log (by rw [hyR]; exact Real.log_pos (by linarith)) a
    rwa [Real.log_mul (by norm_num) hlz.ne'] at b
  have hl2 : log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  -- log log z large
  have hLz : 2 * C1 + 2 ≤ log (log (z : ℝ)) := by
    have hzz : Real.exp (Real.exp (2 * C1 + 2)) ≤ z := by
      have := Nat.le_ceil (Real.exp (Real.exp (2 * C1 + 2)))
      have h' : ((z0 : ℕ) : ℝ) ≤ z := by exact_mod_cast hz0
      linarith
    have a : Real.exp (2 * C1 + 2) ≤ log z := by
      rw [← Real.log_exp (Real.exp (2 * C1 + 2))]
      exact Real.log_le_log (Real.exp_pos _) hzz
    rw [← Real.log_exp (2 * C1 + 2)]
    exact Real.log_le_log (Real.exp_pos _) a
  set L := log (log (z : ℝ))
  have hxR : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hfin : log (log (log (log (x : ℝ)))) ≤ L + 2 := by linarith
  have hsum : (L - C1) / 8 ≤ ∑ p ∈ S', (1 : ℝ) / p := by
    rw [hC1]; linarith
  have : (1 : ℝ) / 256 * (x * log (log (log (log (x : ℝ))))) ≤ (x : ℝ) / 16 * ((L - C1) / 8) := by
    have h1 : (x : ℝ) * log (log (log (log (x : ℝ)))) ≤ x * (L + 2) :=
      mul_le_mul_of_nonneg_left hfin hxR
    have h2 : (L + 2) / 256 ≤ (L - C1) / 128 := by linarith
    nlinarith
  have h3 : (x : ℝ) / 16 * ((L - C1) / 8) ≤ (x : ℝ) / 16 * ∑ p ∈ S', (1 : ℝ) / p :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith

end E878

theorem OMA.solution : type_of% @Erdos878.erdos_878.variants.H_lower_quadruple_log_infinitely_often :=
  E878.main
