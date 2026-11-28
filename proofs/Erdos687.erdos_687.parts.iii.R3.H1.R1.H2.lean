import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R1
import Mathlib

/-!
`H2` asks: for every `C`, for all sufficiently large `n`, every `d` with
`d ^ 8 ≤ C ^ 8 * n ^ 5` satisfies `d ^ 3 ≤ n ^ 2`.

Cubing the hypothesis gives `(d^3)^8 = d^24 ≤ C^24 * n^15`. Once `n ≥ C^24`
this is at most `n^16 = (n^2)^8`, so `d^3 ≤ n^2`.
-/

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R1.H2 := by
  intro C
  refine Filter.eventually_atTop.mpr ⟨C ^ 24, fun n hn => ?_⟩
  intro d hd
  have h : (d ^ 3) ^ 8 ≤ (n ^ 2) ^ 8 :=
    calc (d ^ 3) ^ 8 = d ^ 24 := by ring
      _ = (d ^ 8) ^ 3 := by ring
      _ ≤ (C ^ 8 * n ^ 5) ^ 3 := Nat.pow_le_pow_left hd 3
      _ = C ^ 24 * n ^ 15 := by ring
      _ = n ^ 15 * C ^ 24 := by ring
      _ ≤ n ^ 15 * n := Nat.mul_le_mul_left (n ^ 15) hn
      _ = (n ^ 2) ^ 8 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : 8 ≠ 0)).mp h
