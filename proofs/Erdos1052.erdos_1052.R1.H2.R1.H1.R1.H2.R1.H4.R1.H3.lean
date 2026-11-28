import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H3:
-- Hypothesis H3 of reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1
-- Credit: @alanaut24

/-!
# Shorter proof of step H3

The original proof and seven prime-chain exclusions are by @sanchan.
The z = 11 branch uses the forced chain 7321 -> 523 -> 131.
For odd a, both 2^a+1 and 131+1 supply the simple prime 3.
For even a, a prime q = 2 mod 3 dividing 2^a+1 must be 1 mod 4,
so q is neither 11 nor 131; q+1 and 131+1 again give two sources of 3.
This replaces the original weighted estimate and preserves the exact target.
Related parity argument: @DPS0340, pull request #39771.
-/

namespace OMA.H3Proof

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

private theorem hK_singleton {z e : ℕ} (hz : z.Prime) :
    ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := by
  intro c hc hcd
  rw [Finset.mem_singleton]
  exact (Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hcd)


private theorem p_53699 : Nat.Prime 53699 := by
  refine lucas_primality 53699 (2 : ZMod 53699) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 53699 - 1 = [2 ^ 1, 26849 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_71917 : Nat.Prime 71917 := by
  refine lucas_primality 71917 (2 : ZMod 71917) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 71917 - 1 = [2 ^ 2, 3 ^ 1, 13 ^ 1, 461 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_77969 : Nat.Prime 77969 := by
  refine lucas_primality 77969 (3 : ZMod 77969) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 77969 - 1 = [2 ^ 4, 11 ^ 1, 443 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_143833 : Nat.Prime 143833 := by
  refine lucas_primality 143833 (11 : ZMod 143833) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 143833 - 1 = [2 ^ 3, 3 ^ 1, 13 ^ 1, 461 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_145517 : Nat.Prime 145517 := by
  refine lucas_primality 145517 (2 : ZMod 145517) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 145517 - 1 = [2 ^ 2, 7 ^ 1, 5197 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_696617 : Nat.Prime 696617 := by
  refine lucas_primality 696617 (3 : ZMod 696617) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 696617 - 1 = [2 ^ 3, 19 ^ 1, 4583 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_1935371 : Nat.Prime 1935371 := by
  refine lucas_primality 1935371 (2 : ZMod 1935371) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1935371 - 1 = [2 ^ 1, 5 ^ 1, 103 ^ 1, 1879 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_11384189 : Nat.Prime 11384189 := by
  refine lucas_primality 11384189 (2 : ZMod 11384189) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11384189 - 1 = [2 ^ 2, 53 ^ 1, 53699 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_53699 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16718809 : Nat.Prime 16718809 := by
  refine lucas_primality 16718809 (22 : ZMod 16718809) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16718809 - 1 = [2 ^ 3, 3 ^ 1, 696617 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_696617 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_61931873 : Nat.Prime 61931873 := by
  refine lucas_primality 61931873 (3 : ZMod 61931873) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 61931873 - 1 = [2 ^ 5, 1935371 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_1935371 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_126667477 : Nat.Prime 126667477 := by
  refine lucas_primality 126667477 (2 : ZMod 126667477) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 126667477 - 1 = [2 ^ 2, 3 ^ 4, 13 ^ 1, 17 ^ 1, 29 ^ 1, 61 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_220899323 : Nat.Prime 220899323 := by
  refine lucas_primality 220899323 (2 : ZMod 220899323) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 220899323 - 1 = [2 ^ 1, 7 ^ 1, 29 ^ 1, 101 ^ 1, 5387 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_432599183 : Nat.Prime 432599183 := by
  refine lucas_primality 432599183 (5 : ZMod 432599183) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 432599183 - 1 = [2 ^ 1, 19 ^ 1, 11384189 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_11384189 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_506669909 : Nat.Prime 506669909 := by
  refine lucas_primality 506669909 (2 : ZMod 506669909) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 506669909 - 1 = [2 ^ 2, 126667477 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_126667477 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_727426751 : Nat.Prime 727426751 := by
  refine lucas_primality 727426751 (7 : ZMod 727426751) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 727426751 - 1 = [2 ^ 1, 5 ^ 3, 23 ^ 1, 73 ^ 1, 1733 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_3534389167 : Nat.Prime 3534389167 := by
  refine lucas_primality 3534389167 (6 : ZMod 3534389167) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3534389167 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 61 ^ 1, 83 ^ 1, 1511 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_3852708091 : Nat.Prime 3852708091 := by
  refine lucas_primality 3852708091 (7 : ZMod 3852708091) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3852708091 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_6921586927 : Nat.Prime 6921586927 := by
  refine lucas_primality 6921586927 (5 : ZMod 6921586927) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6921586927 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_16718809 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_7705416181 : Nat.Prime 7705416181 := by
  refine lucas_primality 7705416181 (24 : ZMod 7705416181) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7705416181 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_11488517041 : Nat.Prime 11488517041 := by
  refine lucas_primality 11488517041 (38 : ZMod 11488517041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11488517041 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_13843173853 : Nat.Prime 13843173853 := by
  refine lucas_primality 13843173853 (2 : ZMod 13843173853) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 13843173853 - 1 = [2 ^ 2, 3 ^ 2, 23 ^ 1, 16718809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_16718809 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_15410832361 : Nat.Prime 15410832361 := by
  refine lucas_primality 15410832361 (13 : ZMod 15410832361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 15410832361 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 19 ^ 1, 41 ^ 1, 2141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16003388521 : Nat.Prime 16003388521 := by
  refine lucas_primality 16003388521 (11 : ZMod 16003388521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16003388521 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_16969333201 : Nat.Prime 16969333201 := by
  refine lucas_primality 16969333201 (13 : ZMod 16969333201) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16969333201 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_22977034081 : Nat.Prime 22977034081 := by
  refine lucas_primality 22977034081 (31 : ZMod 22977034081) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 22977034081 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 97 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_32006777041 : Nat.Prime 32006777041 := by
  refine lucas_primality 32006777041 (11 : ZMod 32006777041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 32006777041 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 251 ^ 1, 25301 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_33938666401 : Nat.Prime 33938666401 := by
  refine lucas_primality 33938666401 (29 : ZMod 33938666401) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 33938666401 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_38506913083 : Nat.Prime 38506913083 := by
  refine lucas_primality 38506913083 (2 : ZMod 38506913083) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 38506913083 - 1 = [2 ^ 1, 3 ^ 3, 11 ^ 1, 41 ^ 1, 67 ^ 1, 23599 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_67877332801 : Nat.Prime 67877332801 := by
  refine lucas_primality 67877332801 (14 : ZMod 67877332801) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 67877332801 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_110745390823 : Nat.Prime 110745390823 := by
  refine lucas_primality 110745390823 (3 : ZMod 110745390823) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 110745390823 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 31 ^ 1, 1291 ^ 1, 41927 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_303957468361 : Nat.Prime 303957468361 := by
  refine lucas_primality 303957468361 (11 : ZMod 303957468361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 303957468361 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 2, 13 ^ 1, 17 ^ 1, 77969 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact p_77969 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_539096783161 : Nat.Prime 539096783161 := by
  refine lucas_primality 539096783161 (7 : ZMod 539096783161) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 539096783161 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 509 ^ 1, 39937 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem p_1550435471521 : Nat.Prime 1550435471521 := by
  refine lucas_primality 1550435471521 (11 : ZMod 1550435471521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1550435471521 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 83 ^ 1, 293 ^ 1, 601 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

private theorem kill_419 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 419 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 419 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 419) (e := e) (by norm_num)) E
  have hD : 1 + 419 ^ 4 ∣ 1 + 419 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_15410832361 : 15410832361 ∈ P := S7 15410832361 p_15410832361 (by norm_num) (by simp) ((by norm_num : 15410832361 ∣ 1 + 419 ^ 4).trans hD)
  have hp_7705416181 : 7705416181 ∈ P := S1 7705416181 p_7705416181 (by norm_num) (by simp) 15410832361 hp_15410832361 (by norm_num)
  have hp_3852708091 : 3852708091 ∈ P := S1 3852708091 p_3852708091 (by norm_num) (by simp) 7705416181 hp_7705416181 (by norm_num)
  have hp_6619 : 6619 ∈ P := S1 6619 (by norm_num) (by norm_num) (by simp) 3852708091 hp_3852708091 (by norm_num)
  have hp_145517 : 145517 ∈ P := S1 145517 p_145517 (by norm_num) (by simp) 3852708091 hp_3852708091 (by norm_num)
  have hp_5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (by simp) 6619 hp_6619 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 145517 hp_145517 5 hp_5 (by norm_num) (by norm_num)
  omega

private theorem kill_463 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 463 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 463 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 463) (e := e) (by norm_num)) E
  have hD : 1 + 463 ^ 4 ∣ 1 + 463 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_22977034081 : 22977034081 ∈ P := S7 22977034081 p_22977034081 (by norm_num) (by simp) ((by norm_num : 22977034081 ∣ 1 + 463 ^ 4).trans hD)
  have hp_11488517041 : 11488517041 ∈ P := S1 11488517041 p_11488517041 (by norm_num) (by simp) 22977034081 hp_22977034081 (by norm_num)
  have hp_143833 : 143833 ∈ P := S1 143833 p_143833 (by norm_num) (by simp) 11488517041 hp_11488517041 (by norm_num)
  have hp_71917 : 71917 ∈ P := S1 71917 p_71917 (by norm_num) (by simp) 143833 hp_143833 (by norm_num)
  have hp_467 : 467 ∈ P := S1 467 (by norm_num) (by norm_num) (by simp) 71917 hp_71917 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by simp) 467 hp_467 (by norm_num)

private theorem kill_503 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 503 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 503 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 503) (e := e) (by norm_num)) E
  have hD : 1 + 503 ^ 4 ∣ 1 + 503 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_32006777041 : 32006777041 ∈ P := S7 32006777041 p_32006777041 (by norm_num) (by simp) ((by norm_num : 32006777041 ∣ 1 + 503 ^ 4).trans hD)
  have hp_16003388521 : 16003388521 ∈ P := S1 16003388521 p_16003388521 (by norm_num) (by simp) 32006777041 hp_32006777041 (by norm_num)
  have hp_11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (by simp) 16003388521 hp_16003388521 (by norm_num)
  have hp_727426751 : 727426751 ∈ P := S1 727426751 p_727426751 (by norm_num) (by simp) 16003388521 hp_16003388521 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 11 hp_11 727426751 hp_727426751 (by norm_num) (by norm_num)
  omega

private theorem kill_607 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 607 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 607 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 607) (e := e) (by norm_num)) E
  have hD : 1 + 607 ^ 4 ∣ 1 + 607 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_67877332801 : 67877332801 ∈ P := S7 67877332801 p_67877332801 (by norm_num) (by simp) ((by norm_num : 67877332801 ∣ 1 + 607 ^ 4).trans hD)
  have hp_33938666401 : 33938666401 ∈ P := S1 33938666401 p_33938666401 (by norm_num) (by simp) 67877332801 hp_67877332801 (by norm_num)
  have hp_16969333201 : 16969333201 ∈ P := S1 16969333201 p_16969333201 (by norm_num) (by simp) 33938666401 hp_33938666401 (by norm_num)
  have hp_137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (by simp) 16969333201 hp_16969333201 (by norm_num)
  have hp_61931873 : 61931873 ∈ P := S1 61931873 p_61931873 (by norm_num) (by simp) 16969333201 hp_16969333201 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 137 hp_137 61931873 hp_61931873 (by norm_num) (by norm_num)
  omega

private theorem kill_883 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 883 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 883 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 883) (e := e) (by norm_num)) E
  have hD : 1 + 883 ^ 4 ∣ 1 + 883 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_303957468361 : 303957468361 ∈ P := S7 303957468361 p_303957468361 (by norm_num) (by simp) ((by norm_num : 303957468361 ∣ 1 + 883 ^ 4).trans hD)
  have hp_43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (by simp) 303957468361 hp_303957468361 (by norm_num)
  have hp_3534389167 : 3534389167 ∈ P := S1 3534389167 p_3534389167 (by norm_num) (by simp) 303957468361 hp_303957468361 (by norm_num)
  have hp_11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (by simp) 43 hp_43 (by norm_num)
  have hp_220899323 : 220899323 ∈ P := S1 220899323 p_220899323 (by norm_num) (by simp) 3534389167 hp_3534389167 (by norm_num)
  have hEq := S3 3 (by norm_num) (by norm_num) (by simp) 11 hp_11 220899323 hp_220899323 (by norm_num) (by norm_num)
  omega

private theorem kill_1019 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 1019 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1019 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 1019) (e := e) (by norm_num)) E
  have hD : 1 + 1019 ^ 4 ∣ 1 + 1019 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_539096783161 : 539096783161 ∈ P := S7 539096783161 p_539096783161 (by norm_num) (by simp) ((by norm_num : 539096783161 ∣ 1 + 1019 ^ 4).trans hD)
  have hp_38506913083 : 38506913083 ∈ P := S1 38506913083 p_38506913083 (by norm_num) (by simp) 539096783161 hp_539096783161 (by norm_num)
  have hp_19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (by simp) 38506913083 hp_38506913083 (by norm_num)
  have hp_506669909 : 506669909 ∈ P := S1 506669909 p_506669909 (by norm_num) (by simp) 38506913083 hp_38506913083 (by norm_num)
  have hEq := S3 5 (by norm_num) (by norm_num) (by simp) 19 hp_19 506669909 hp_506669909 (by norm_num) (by norm_num)
  omega

private theorem kill_1327 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 1327 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1327 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) : False := by
  obtain ⟨S1, -, S3, -, -, S6, S7, -⟩ := facts hP (hK_singleton (z := 1327) (e := e) (by norm_num)) E
  have hD : 1 + 1327 ^ 4 ∣ 1 + 1327 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_1550435471521 : 1550435471521 ∈ P := S7 1550435471521 p_1550435471521 (by norm_num) (by simp) ((by norm_num : 1550435471521 ∣ 1 + 1327 ^ 4).trans hD)
  have hp_110745390823 : 110745390823 ∈ P := S1 110745390823 p_110745390823 (by norm_num) (by simp) 1550435471521 hp_1550435471521 (by norm_num)
  have hp_13843173853 : 13843173853 ∈ P := S1 13843173853 p_13843173853 (by norm_num) (by simp) 110745390823 hp_110745390823 (by norm_num)
  have hp_6921586927 : 6921586927 ∈ P := S1 6921586927 p_6921586927 (by norm_num) (by simp) 13843173853 hp_13843173853 (by norm_num)
  have hp_432599183 : 432599183 ∈ P := S1 432599183 p_432599183 (by norm_num) (by simp) 6921586927 hp_6921586927 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by simp) 432599183 hp_432599183 (by norm_num)

private theorem kill_11 {m e : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p)
    (he : e % 8 = 4) (hm : 10 ≤ m) : False := by
  obtain ⟨S1, S2, S3, S4, _, _, S7, _⟩ :=
    facts hP (hK_singleton (z := 11) (e := e) (by norm_num)) E
  have hD : 1 + 11 ^ 4 ∣ 1 + 11 ^ e := one_add_pow_dvd_of_odd_mul he
  have hp_7321 : 7321 ∈ P := S7 7321 (by norm_num) (by norm_num) (by simp)
    ((by norm_num : 7321 ∣ 1 + 11 ^ 4).trans hD)
  have hp_523 : 523 ∈ P := S1 523 (by norm_num) (by norm_num) (by simp) 7321 hp_7321 (by norm_num)
  have hp_131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (by simp) 523 hp_523 (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
  · have hmEven : Even m := Nat.even_iff.mpr hm0
    have hmod : (2 ^ m + 1) % 3 = 2 := by
      obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
      rw [hk, pow_mul]
      have hp : (2 ^ 2) ^ k % 3 = 1 := by norm_num [Nat.pow_mod]
      omega
    obtain ⟨q, hqp, hqd, hq3⟩ := exists_prime_mod3 _ hmod
    have hq2 : q ≠ 2 := by
      rintro rfl
      have h2d : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
      have hbad : 2 ∣ 1 := (Nat.dvd_add_right h2d).mp hqd
      norm_num at hbad
    have hq4 : q % 4 = 1 := mod_four_of_dvd_one_add_pow_even hqp hq2 hmEven
      (by simpa [add_comm] using hqd)
    have hq11 : q ≠ 11 := by intro h; subst q; norm_num at hq4
    have hqP : q ∈ P := S2 q hqp hq2 (by simpa using hq11) hqd
    have h3q : 3 ∣ q + 1 := by omega
    have hq131 : q = 131 := S3 3 (by norm_num) (by norm_num) (by simp)
      q hqP 131 hp_131 h3q (by norm_num)
    rw [hq131] at hq4
    norm_num at hq4
  · exact S4 3 (by norm_num) (by norm_num) (by simp)
      (three_dvd_two_pow_add_one hm1) 131 hp_131 (by norm_num)

end OMA.H3Proof

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H3 := by
  refine ⟨9, fun n h z hz hS he hzmem _ _ _ _ _ _ _ _ _ _ => ?_⟩
  obtain ⟨hzn, hs⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := by
    intro h2
    subst h2
    simp at hzmem
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
  rcases hzmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_contra hgt
    exact OMA.H3Proof.kill_11 hP E he (by omega)
  · exact (OMA.H3Proof.kill_419 hP E he).elim
  · exact (OMA.H3Proof.kill_463 hP E he).elim
  · exact (OMA.H3Proof.kill_503 hP E he).elim
  · exact (OMA.H3Proof.kill_607 hP E he).elim
  · exact (OMA.H3Proof.kill_883 hP E he).elim
  · exact (OMA.H3Proof.kill_1019 hP E he).elim
  · exact (OMA.H3Proof.kill_1327 hP E he).elim
