import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step Erdos420.erdos_420.parts.i.R1.H2: hypothesis H2 of reduction Erdos420.erdos_420.parts.i.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ a b p s : ℕ, p.Prime → 0 < s → s < p → a < s * p → s * p ≤ b →     (s + 1) * (σ 0 a.factorial) ≤ s * (σ 0 b.factorial)

/-! The reduction file already contains a complete proof of this hypothesis, the lemma
`prime_gain_proof` written by the reduction's author: since `s < p`, the prime `p` divides
`a!` at most `s - 1` times and `b!` at least `s` times, so passing from `a!` to `b!` multiplies
the divisor count by at least `(s + 1) / s`. This step only records that lemma as the proof. -/

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 :=
  OMA.R_Erdos420_erdos_420_parts_i_R1.prime_gain_proof
