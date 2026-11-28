import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1

-- Step Erdos507.erdos_507.variants.upper_cpz24.R1.H2.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos507.erdos_507.variants.upper_cpz24.R1.H2.R1.H1.R1.
-- Written with Claude Code (AI-assisted).
-- Round each coordinate down to the grid (1/q)ℤ: ⌊q x⌋ / q is within 1/q of x, and
-- ⌊q x⌋ stays in [-q, q] (in [0, q] when x ≥ 0) because |x| ≤ 1.

namespace OMA.Erdos507R1H2R1H1R1H2

theorem round_down (q : ℕ) (hq : 0 < q) (x : ℝ) (hlo : -1 ≤ x) (hhi : x ≤ 1) :
    -(q : ℤ) ≤ ⌊(q : ℝ) * x⌋ ∧ ⌊(q : ℝ) * x⌋ ≤ q ∧
      (0 ≤ x → 0 ≤ ⌊(q : ℝ) * x⌋) ∧
      |x - (⌊(q : ℝ) * x⌋ : ℝ) / q| < 1 / (q : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := Int.floor_le ((q : ℝ) * x)
  have h2 := Int.lt_floor_add_one ((q : ℝ) * x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    nlinarith
  · have : ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) ≤ (q : ℝ) := by nlinarith
    exact_mod_cast this
  · intro hx
    exact Int.floor_nonneg.mpr (by positivity)
  · have e : x - (⌊(q : ℝ) * x⌋ : ℝ) / q = ((q : ℝ) * x - ⌊(q : ℝ) * x⌋) / q := by
      field_simp
    rw [e, abs_div, abs_of_pos hqr, div_lt_div_iff_of_pos_right hqr, abs_lt]
    constructor <;> linarith

end OMA.Erdos507R1H2R1H1R1H2

open OMA.Erdos507R1H2R1H1R1H2 in
theorem OMA.solution :
    OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1.H2 := by
  intro I q hq a b s hab
  refine ⟨fun i => ⌊(q : ℝ) * a i⌋, fun i => ⌊(q : ℝ) * b i⌋, fun i => ⌊(q : ℝ) * s i⌋,
    fun i => ?_, fun i => ?_⟩
  · obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, hs⟩ := hab i
    obtain ⟨hs0, hs1⟩ := abs_le.mp hs
    have rA := round_down q hq (a i) (by linarith) ha1
    have rB := round_down q hq (b i) (by linarith) hb1
    have rS := round_down q hq (s i) hs0 hs1
    exact ⟨rA.2.2.1 ha0, rA.2.1, rB.2.2.1 hb0, rB.2.1, rS.1, rS.2.1⟩
  · obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, hs⟩ := hab i
    obtain ⟨hs0, hs1⟩ := abs_le.mp hs
    exact ⟨(round_down q hq (a i) (by linarith) ha1).2.2.2,
      (round_down q hq (b i) (by linarith) hb1).2.2.2,
      (round_down q hq (s i) hs0 hs1).2.2.2⟩
