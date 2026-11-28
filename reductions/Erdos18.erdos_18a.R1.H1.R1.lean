import OMAReductions.R_Erdos18_erdos_18a_R1
import Mathlib

/-!
# Erdős 18 dyadic representatives: digit entropy and harmonic mixing

This reduction isolates the two quantitative inputs in the harmonic dyadic
shift route.  The first is an optimized uniform factorial-digit law with
nonconcentration at every lower dyadic scale.  The second is the sharp
harmonic mixing transport from that law to explicit shifted-digit witnesses
on a dense residue set.  The arithmetic expansion of those witnesses is
carried out here.
-/

namespace OMA.R_Erdos18_erdos_18a_R1_H1_R1

open Filter

/-- Optimized divisor-digit input: small factorial digits have a nonempty
finite uniform law whose lower dyadic prefixes are nonconcentrated at the
sharp rate needed by the harmonic argument. -/
def H1 : Prop :=
  ∀ᶠ k : ℕ in atTop, ∃ xs : List ℕ,
    0 < xs.length ∧
    (∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) ∧
    (∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ)))

/-- Quantitative harmonic-mixing input: shifted copies of a nonconcentrated
uniform digit law cover a dense dyadic residue set by explicitly bounded
shifted-digit sums. -/
def H2 : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ xs : List ℕ,
    0 < xs.length →
    (∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) →
    (∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) →
    ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ w : List (ℕ × ℕ),
        w.length ≤ (Nat.log 2 k + 1) ^ 4 ∧
        (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
        (w.map fun p => 2 ^ p.1 * p.2).sum ≤ 2 ^ (3 * k) ∧
        (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = y

theorem factorial_power_dvd (m r : ℕ) :
    m.factorial ^ r ∣ (r * m).factorial := by
  simpa using Nat.prod_factorial_dvd_factorial_sum (Finset.range r) (fun _ => m)

theorem factorial_binary_reserve (m k : ℕ) :
    2 ^ k * m.factorial ∣ (m + 2 * k).factorial := by
  have hpow : 2 ^ k ∣ (2 * k).factorial := by
    simpa [Nat.factorial, Nat.mul_comm] using factorial_power_dvd 2 k
  exact (mul_dvd_mul hpow (dvd_refl m.factorial)).trans
    (by simpa [Nat.add_comm] using
      Nat.factorial_mul_factorial_dvd_factorial_add (2 * k) m)

theorem shifted_divisor_dvd_factorial {m k b d : ℕ}
    (hd : d ∣ m.factorial) (hb : b ≤ k) :
    2 ^ b * d ∣ (m + 2 * k).factorial :=
  (mul_dvd_mul (pow_dvd_pow 2 hb) hd).trans (factorial_binary_reserve m k)

theorem list_sum_map_mul_left (c : ℕ) : ∀ U : List ℕ,
    (U.map fun d => c * d).sum = c * U.sum := by
  intro U
  induction U with
  | nil => simp
  | cons d U ih =>
      simp [ih, Nat.mul_add]

theorem exists_shift_expansion {k : ℕ} {xs : List ℕ}
    (hrep : ∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) :
    ∀ w : List (ℕ × ℕ), (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) →
      ∃ T : List ℕ,
        (∀ d ∈ T, d ∣ (36 * k).factorial) ∧
        T.length ≤ w.length * (Nat.log 2 k + 1) ∧
        T.sum = (w.map fun p => 2 ^ p.1 * p.2).sum := by
  intro w
  induction w with
  | nil =>
      intro _
      exact ⟨[], by simp, by simp, by simp⟩
  | cons p w ih =>
      intro hw
      have hp : p.1 < k ∧ p.2 ∈ xs := hw p (by simp)
      have htail : ∀ q ∈ w, q.1 < k ∧ q.2 ∈ xs := by
        intro q hq
        exact hw q (by simp [hq])
      obtain ⟨T, hTdiv, hTlen, hTsum⟩ := ih htail
      obtain ⟨hxbound, U, hUdiv, hUlen, hUsum⟩ := hrep p.2 hp.2
      refine ⟨(U.map fun d => 2 ^ p.1 * d) ++ T, ?_, ?_, ?_⟩
      · intro d hd
        rw [List.mem_append] at hd
        rcases hd with hdV | hdT
        · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hdV
          have hd0div : d₀ ∣ (32 * k).factorial := hUdiv d₀ hd₀
          have hshift : 2 ^ p.1 * d₀ ∣ (32 * k + 2 * k).factorial :=
            shifted_divisor_dvd_factorial hd0div (Nat.le_of_lt hp.1)
          have hhost : (32 * k + 2 * k).factorial ∣ (36 * k).factorial :=
            Nat.factorial_dvd_factorial (by omega)
          exact hshift.trans hhost
        · exact hTdiv d hdT
      · rw [List.length_append, List.length_map]
        calc
          U.length + T.length ≤
              (Nat.log 2 k + 1) + w.length * (Nat.log 2 k + 1) :=
            Nat.add_le_add hUlen hTlen
          _ = (w.length + 1) * (Nat.log 2 k + 1) := by ring
          _ = (p :: w).length * (Nat.log 2 k + 1) := by simp
      · rw [List.sum_append, list_sum_map_mul_left, hUsum, hTsum]
        simp

theorem main : H1 → H2 → OMA.R_Erdos18_erdos_18a_R1.H1 := by
  intro hlawEvent hmixEvent
  filter_upwards [hlawEvent, hmixEvent] with k hlawk hmixk
  obtain ⟨xs, hxne, hrep, hcap⟩ := hlawk
  obtain ⟨B, hdense, hwitness⟩ := hmixk xs hxne hrep hcap
  refine ⟨B, hdense, ?_⟩
  intro y hy
  obtain ⟨w, hwlen, hwvalid, hwheight, hwcong⟩ := hwitness y hy
  obtain ⟨T, hTdiv, hTlen, hTsum⟩ := exists_shift_expansion hrep w hwvalid
  refine ⟨T, hTdiv, ?_, ?_, ?_⟩
  · calc
      T.length ≤ w.length * (Nat.log 2 k + 1) := hTlen
      _ ≤ (Nat.log 2 k + 1) ^ 4 * (Nat.log 2 k + 1) :=
        Nat.mul_le_mul_right _ hwlen
      _ = (Nat.log 2 k + 1) ^ 5 := by ring
  · rw [hTsum]
    exact hwheight
  · rw [hTsum]
    exact hwcong

end OMA.R_Erdos18_erdos_18a_R1_H1_R1
