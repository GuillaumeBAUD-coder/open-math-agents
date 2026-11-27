import FormalConjectures.ErdosProblems.«1004»
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Totient

/-!
A prime p near the cube root of n yields a totient collision shortly above n.
Write d = p - 1 and choose t with t * d^2 just above n and p ∤ t.
Then the totients of t * d^2 and t * d * p agree by the gcd product formula.
-/

-- Credit: @dk8827

open Filter
open scoped Topology

namespace OMA.TotientRun

private theorem totient_mul_divisor {d m : ℕ} (hd : 0 < d) (h : d ∣ m) :
    Nat.totient (m * d) = d * Nat.totient m := by
  have he := Nat.totient_gcd_mul_totient_mul m d
  rw [Nat.gcd_eq_right h] at he
  have hpos := Nat.totient_pos.2 hd
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = _ := he
    _ = _ := by ring

private theorem cube_root_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem collision (n : ℕ) (hn : 1 ≤ n) :
    ∃ u v : ℕ, n < u ∧ u < v ∧ Nat.totient u = Nat.totient v ∧
      (v : ℝ) ≤ n + 41 * ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) := by
  let z := (n : ℝ) ^ (1 / 3 : ℝ)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz1 : 1 ≤ z := Real.one_le_rpow hn1 (by norm_num)
  have hz0 : 0 < z := zero_lt_one.trans_le hz1
  have hz3 : z ^ 3 = n := cube_root_cube (by positivity)
  let R := ⌈z⌉₊
  have hR : z ≤ (R : ℝ) := Nat.le_ceil z
  have hR0 : R ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hR
    exact hz0.not_ge hR
  obtain ⟨p, hp, hRp, hpR⟩ := Nat.exists_prime_lt_and_le_two_mul R hR0
  let d := p - 1
  have hpd : p = d + 1 := by
    have := hp.two_le
    dsimp only [d]
    omega
  have hd0 : 0 < d := by have := hp.two_le; omega
  have hd1 : z ≤ (d : ℝ) :=
    hR.trans (by exact_mod_cast (show R ≤ d by omega))
  have hd4 : (d : ℝ) ≤ 4 * z := by
    have hp' : (p : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hpR
    have hd' : (d : ℝ) ≤ p := by exact_mod_cast (show d ≤ p by omega)
    have := Nat.ceil_lt_add_one hz0.le
    change (R : ℝ) < z + 1 at this
    linarith only [hp', hd', this, hz1]
  let a := d * d
  have ha : 0 < a := Nat.mul_pos hd0 hd0
  let t₀ := n / a + 1
  let t := if p ∣ t₀ then t₀ + 1 else t₀
  have htlo : t₀ ≤ t := by dsimp only [t]; split <;> omega
  have hthi : t ≤ t₀ + 1 := by dsimp only [t]; split <;> omega
  have htd : ¬ p ∣ t := by
    dsimp only [t]
    split
    · rename_i h
      intro hb
      have h1 : p ∣ 1 := by
        have hh := Nat.dvd_sub hb h
        simpa using hh
      have := Nat.le_of_dvd (by decide : 0 < 1) h1
      exact hp.one_lt.not_ge this
    · assumption
  have hdp : ¬ p ∣ d := fun h => by
    have := Nat.le_of_dvd hd0 h
    omega
  let m := t * d
  let u := m * d
  let v := m * p
  have hu_eq : u = t * a := by dsimp only [u, m, a]; ring
  have hu : n < u := by
    rw [hu_eq]
    exact (Nat.div_lt_iff_lt_mul ha).1 (show n / a < t by
      have := Nat.lt_succ_self (n / a)
      exact this.trans_le htlo)
  have huv_eq : v = u + m := by
    dsimp only [v, u]
    rw [hpd, Nat.mul_add, Nat.mul_one]
  have hm0 : 0 < m := by
    have ht0 : 0 < t := (Nat.succ_pos (n / a)).trans_le htlo
    exact Nat.mul_pos ht0 hd0
  have huv : u < v := by omega
  have htoti : Nat.totient u = Nat.totient v := by
    have hmD : d ∣ m := ⟨t, Nat.mul_comm _ _⟩
    have hpm : ¬ p ∣ m := fun h => (hp.dvd_mul.1 h).elim htd hdp
    change Nat.totient (m * d) = Nat.totient (m * p)
    rw [totient_mul_divisor hd0 hmD, Nat.mul_comm m p, Nat.totient_mul_of_prime_of_not_dvd hp hpm]
  have hu_le : u ≤ n + 2 * a := by
    have hb := Nat.mul_le_mul_right a hthi
    change t * a ≤ (n / a + 1 + 1) * a at hb
    have hc : (n / a + 1 + 1) * a = n / a * a + 2 * a := by ring
    rw [hc] at hb
    have hdv := Nat.div_mul_le_self n a
    omega
  have hu' : (u : ℝ) ≤ n + 2 * (d : ℝ) ^ 2 := by
    have h : u ≤ n + 2 * d ^ 2 := by simpa only [a, pow_two] using hu_le
    exact_mod_cast h
  have hm' : (m : ℝ) ≤ z ^ 2 + 2 * d := by
    apply (le_of_mul_le_mul_right · (show (0 : ℝ) < d by exact_mod_cast hd0))
    have hdN : (n : ℝ) ≤ z ^ 2 * (d : ℝ) := by
      rw [← hz3, pow_succ]
      exact mul_le_mul_of_nonneg_left hd1 (sq_nonneg _)
    calc
      (m : ℝ) * d = (u : ℝ) := (Nat.cast_mul m d).symm
      _ ≤ n + 2 * (d : ℝ) ^ 2 := hu'
      _ ≤ (z ^ 2 + 2 * (d : ℝ)) * d := by nlinarith only [hdN]
  have hdsq : (d : ℝ) ^ 2 ≤ 16 * z ^ 2 := by
    have h : (d : ℝ) * d ≤ (4 * z) * (4 * z) :=
      mul_le_mul hd4 hd4 (by positivity) (by positivity)
    nlinarith only [h]
  have hdlin : (d : ℝ) ≤ 4 * z ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hz1 hz0.le
    nlinarith only [hd4, h]
  have hv_eq : (v : ℝ) = (u : ℝ) + m := by exact_mod_cast huv_eq
  exact ⟨u, v, hu, huv, htoti, by
    change (v : ℝ) ≤ n + 41 * z ^ 2
    linarith only [hu', hm', hdsq, hdlin, hv_eq]⟩

private theorem growth {x : ℝ} (hx : 0 < x) (hL : 1000 ≤ Real.log x) :
    41 * (x ^ (1 / 3 : ℝ)) ^ (2 : ℕ) ≤
      x / Real.exp ((Real.log x) ^ (1 / 3 : ℝ)) := by
  let L := Real.log x
  let y := L ^ (1 / 3 : ℝ)
  have hL0 : 0 < L := by linarith only [hL]
  have hy0 : 0 < y := Real.rpow_pos_of_pos hL0 _
  have hycube : y ^ 3 = L := cube_root_cube hL0.le
  have hy10 : 10 ≤ y := by
    by_contra! h
    have hh : y ^ (3 : ℕ) < 10 ^ (3 : ℕ) := pow_lt_pow_left₀ h hy0.le (by decide)
    norm_num at hh
    linarith only [hh, hycube, hL]
  have hy6 : 6 * y ≤ L := by
    have hy2 : 6 ≤ y ^ 2 := by nlinarith only [hy10, sq_nonneg (y - 10)]
    have h := mul_le_mul_of_nonneg_right hy2 hy0.le
    nlinarith only [hycube, h]
  have h41 : Real.log 41 ≤ 40 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 41)
    norm_num at h ⊢
    exact h
  apply (Real.log_le_log_iff (by positivity) (by positivity)).1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_rpow hx,
    Real.log_div hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  change Real.log 41 + (2 : ℝ) * ((1 / 3 : ℝ) * L) ≤ L - y
  linarith only [h41, hy6, hL]

end OMA.TotientRun

theorem OMA.solution : type_of% @Erdos1004.erdos_1004.variants.le_of_isDistinctTotientRun := by
  refine ⟨1, by norm_num, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop 1000] with n hn hlogn
  intro K hrun
  rw [one_mul]
  obtain ⟨u, v, hnu, huv, ht, hv⟩ := OMA.TotientRun.collision n hn
  have hbound : (K : ℝ) ≤ 41 * ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) := by
    by_contra! h
    have hnv : (v : ℝ) ≤ n + K := by linarith only [hv, h]
    have hnv' : v ≤ n + K := by exact_mod_cast hnv
    exact huv.ne (hrun ⟨by omega, by omega⟩ ⟨by omega, hnv'⟩ ht)
  exact hbound.trans (OMA.TotientRun.growth (by exact_mod_cast (show 0 < n by omega)) hlogn)
