import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1
import Mathlib

/-! A finite upper bound for the reciprocal sum of compatible odd primes.
Splitting on the primes through 43 suffices. Inclusion of r eliminates every
q with r dividing q - 1. The integer upper weights round 10⁸/p upward. -/

open scoped BigOperators

namespace OMA.PrimeAntichainSeventeen

private def wt (p : ℕ) : ℕ := 100000000 / p + 1

private def cost (a : Finset ℕ) : ℕ := ∑ p ∈ a, wt p

private def leftAt (p : ℕ) (a : Finset ℕ) : Finset ℕ := a.erase p

private def rightAt (p : ℕ) (a : Finset ℕ) : Finset ℕ :=
  a.filter (fun q => ¬ p ∣ q - 1)

private def walk : List ℕ → Finset ℕ → Bool
  | [], a => decide (cost a ≤ 111000000)
  | p :: ps, a =>
    if cost a ≤ 111000000 then true else
      if p ∈ a then walk ps (leftAt p a) && walk ps (rightAt p a)
      else walk ps a

private theorem walk_bound {S : Finset ℕ}
    (hc : ∀ p ∈ S, ∀ q ∈ S, ¬ p ∣ q - 1) (ps : List ℕ) (a : Finset ℕ)
    (hS : S ⊆ a) (ok : walk ps a = true) : cost S ≤ 111000000 := by
  have mono : ∀ a : Finset ℕ, S ⊆ a → cost S ≤ cost a := by
    intro b hb
    exact Finset.sum_le_sum_of_subset hb
  induction ps generalizing a with
  | nil =>
    exact (mono a hS).trans (of_decide_eq_true ok)
  | cons p ps ih =>
    by_cases cheap : cost a ≤ 111000000
    · exact (mono a hS).trans cheap
    · by_cases ha : p ∈ a
      · have both : walk ps (leftAt p a) = true ∧ walk ps (rightAt p a) = true := by
          simpa only [walk, if_neg cheap, if_pos ha, Bool.and_eq_true] using ok
        by_cases h : p ∈ S
        · apply ih (rightAt p a) _ both.2
          intro q hq
          exact Finset.mem_filter.mpr ⟨hS hq, hc p h q hq⟩
        · apply ih (leftAt p a) _ both.1
          intro q hq
          exact Finset.mem_erase.mpr ⟨fun e => h (e ▸ hq), hS hq⟩
      · apply ih a hS
        simpa only [walk, if_neg cheap, if_neg ha] using ok

private def tail : List ℕ := [17, 19, 23, 29, 31, 37, 41, 43]

private def seed (yes no : List ℕ) : Finset ℕ :=
  (Finset.Ioc 2 (2^17)).filter (fun q => q.Prime ∧ q ∉ no ∧ ∀ r ∈ yes, ¬ r ∣ q-1)

private theorem seed_bound {S : Finset ℕ}
    (hs : ∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≤ 2^17)
    (hc : ∀ p ∈ S, ∀ q ∈ S, ¬ p ∣ q - 1) (yes no : List ℕ)
    (hy : ∀ r ∈ yes, r ∈ S) (hn : ∀ r ∈ no, r ∉ S)
    (ok : walk tail (seed yes no) = true) : cost S ≤ 111000000 := by
  apply walk_bound hc tail (seed yes no) _ ok
  intro q hq
  have hp := hs q hq
  have h2 := hp.1.two_le
  have ho := hp.2.1
  rcases ho with ⟨k, hk⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hp.2.2⟩,
    hp.1, fun hm => hn q hm hq, fun r hr => hc r (hy r hr) q hq⟩

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00000 : walk tail (seed [] [3, 5, 7, 11, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00001 : walk tail (seed [13] [3, 5, 7, 11]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00010 : walk tail (seed [11] [3, 5, 7, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00011 : walk tail (seed [11, 13] [3, 5, 7]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00100 : walk tail (seed [7] [3, 5, 11, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00101 : walk tail (seed [7, 13] [3, 5, 11]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00110 : walk tail (seed [7, 11] [3, 5, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c00111 : walk tail (seed [7, 11, 13] [3, 5]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c01000 : walk tail (seed [5] [3, 7, 11, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c01001 : walk tail (seed [5, 13] [3, 7, 11]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c01100 : walk tail (seed [5, 7] [3, 11, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c01101 : walk tail (seed [5, 7, 13] [3, 11]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c10000 : walk tail (seed [3] [5, 7, 11, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c10010 : walk tail (seed [3, 11] [5, 7, 13]) = true := by
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
private theorem c11000 : walk tail (seed [3, 5] [7, 11, 13]) = true := by
  decide +kernel

private theorem bound {S : Finset ℕ}
    (hs : ∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≤ 2^17)
    (hc : ∀ p ∈ S, ∀ q ∈ S, ¬ p ∣ q - 1) : cost S ≤ 111000000 := by
  by_cases h3 : 3 ∈ S
  · by_cases h5 : 5 ∈ S
    · by_cases h7 : 7 ∈ S
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 7 h7 (by decide)).elim
          · exact (hc 3 h3 7 h7 (by decide)).elim
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 7 h7 (by decide)).elim
          · exact (hc 3 h3 7 h7 (by decide)).elim
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 13 h13 (by decide)).elim
          · exact (hc 5 h5 11 h11 (by decide)).elim
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 13 h13 (by decide)).elim
          · exact seed_bound hs hc [3, 5] [7, 11, 13] (by simp_all) (by simp_all) c11000
    · by_cases h7 : 7 ∈ S
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 7 h7 (by decide)).elim
          · exact (hc 3 h3 7 h7 (by decide)).elim
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 7 h7 (by decide)).elim
          · exact (hc 3 h3 7 h7 (by decide)).elim
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 13 h13 (by decide)).elim
          · exact seed_bound hs hc [3, 11] [5, 7, 13] (by simp_all) (by simp_all) c10010
        · by_cases h13 : 13 ∈ S
          · exact (hc 3 h3 13 h13 (by decide)).elim
          · exact seed_bound hs hc [3] [5, 7, 11, 13] (by simp_all) (by simp_all) c10000
  · by_cases h5 : 5 ∈ S
    · by_cases h7 : 7 ∈ S
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 5 h5 11 h11 (by decide)).elim
          · exact (hc 5 h5 11 h11 (by decide)).elim
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [5, 7, 13] [3, 11] (by simp_all) (by simp_all) c01101
          · exact seed_bound hs hc [5, 7] [3, 11, 13] (by simp_all) (by simp_all) c01100
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact (hc 5 h5 11 h11 (by decide)).elim
          · exact (hc 5 h5 11 h11 (by decide)).elim
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [5, 13] [3, 7, 11] (by simp_all) (by simp_all) c01001
          · exact seed_bound hs hc [5] [3, 7, 11, 13] (by simp_all) (by simp_all) c01000
    · by_cases h7 : 7 ∈ S
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [7, 11, 13] [3, 5] (by simp_all) (by simp_all) c00111
          · exact seed_bound hs hc [7, 11] [3, 5, 13] (by simp_all) (by simp_all) c00110
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [7, 13] [3, 5, 11] (by simp_all) (by simp_all) c00101
          · exact seed_bound hs hc [7] [3, 5, 11, 13] (by simp_all) (by simp_all) c00100
      · by_cases h11 : 11 ∈ S
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [11, 13] [3, 5, 7] (by simp_all) (by simp_all) c00011
          · exact seed_bound hs hc [11] [3, 5, 7, 13] (by simp_all) (by simp_all) c00010
        · by_cases h13 : 13 ∈ S
          · exact seed_bound hs hc [13] [3, 5, 7, 11] (by simp_all) (by simp_all) c00001
          · exact seed_bound hs hc [] [3, 5, 7, 11, 13] (by simp) (by simp_all) c00000


private theorem point {p : ℕ} (hp : 0 < p) : (p : ℝ)⁻¹ ≤ (wt p : ℝ) / 100000000 := by
  have hNat : 100000000 ≤ wt p * p := by
    have hm := Nat.mod_lt 100000000 hp
    have hid := Nat.div_add_mod 100000000 p
    unfold wt
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (100000000 / p) p]
    omega
  have hReal : (100000000 : ℝ) ≤ (wt p : ℝ) * (p : ℝ) := by exact_mod_cast hNat
  rw [inv_eq_one_div, div_le_div_iff₀ (by exact_mod_cast hp) (by norm_num)]
  simpa using hReal

end OMA.PrimeAntichainSeventeen

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3_H2_R1_H2_R1_H1_R1.H1 := by
  intro S hs hc
  have hn := OMA.PrimeAntichainSeventeen.bound hs hc
  change (∑ p ∈ S, OMA.PrimeAntichainSeventeen.wt p) ≤ 111000000 at hn
  have hr : (∑ p ∈ S, (OMA.PrimeAntichainSeventeen.wt p : ℝ)) ≤ 111000000 := by
    exact_mod_cast hn
  calc
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤ ∑ p ∈ S, (OMA.PrimeAntichainSeventeen.wt p : ℝ) / 100000000 :=
      Finset.sum_le_sum fun p hp => OMA.PrimeAntichainSeventeen.point (hs p hp).1.pos
    _ = (∑ p ∈ S, (OMA.PrimeAntichainSeventeen.wt p : ℝ)) / 100000000 := by rw [Finset.sum_div]
    _ ≤ 111 / 100 := by linarith
