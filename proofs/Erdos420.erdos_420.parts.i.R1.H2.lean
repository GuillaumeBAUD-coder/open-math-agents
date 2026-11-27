import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step Erdos420.erdos_420.parts.i.R1.H2: hypothesis H2 of reduction Erdos420.erdos_420.parts.i.R1
-- The merged reduction already carries the arithmetic argument as the lemma
-- `prime_gain_proof : H2` (factorial divisor counts grow by the prime gain factor
-- (v_p(n!)+1)/(v_p((n-1)!)+1) = (s+1)/s at n = s*p), so the step is that lemma.

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 :=
  OMA.R_Erdos420_erdos_420_parts_i_R1.prime_gain_proof
