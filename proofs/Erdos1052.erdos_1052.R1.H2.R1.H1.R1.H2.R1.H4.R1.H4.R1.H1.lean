import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H1: hypothesis H1 of reduction
-- Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1
-- Upstream path: proofs/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1.H1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- The step: the unitary perfect number n has exactly one repeated odd prime z, the exponent
-- e = v_z(n) is 16 mod 32, and z is one of the 31 primes
--   41, 73, 113, 157, 167, 173, 199, 307, 449, 599, 607, 617, 643, 743, 811, 937,
--   967, 1201, 1213, 1237, 1249, 1277, 1297, 1373, 1579, 1637, 1667, 1747, 1979, 2011, 2027
-- left over by the sieve of the reduction.  Claim: a = padicValNat 2 n is bounded.
--
-- Proof: the case is impossible, so the bound holds with A = 0 (the conditions on a are not used).
-- With P = the set of simple odd primes of n, the balance equation is
--   (2^a + 1)(1 + z^e) prod_P (p + 1) = 2^(a+1) z^e prod_P p,
-- in which every odd prime other than z occurs exactly once on the left.  Since e = 16 mod 32,
-- z^16 + 1 divides 1 + z^e; its odd primes are simple primes of n, and the odd primes (other than z)
-- of p + 1 for simple p are simple again.  For each of the 31 primes z the forced chain recorded in
-- k16_<z> ends in a contradiction: a square divides some p + 1 (25 primes z) or a prime has two
-- sources on the left (6).  The comment above each k16_<z> names the contradiction.
-- Primes above 4.3 * 10^7 on the chains carry a Lucas certificate (theorems prime_<p>, 94 new, up to
-- 53 digits; p - 1 factorizations from trial division, GMP-ECM and factordb, re-checked here by Lean).

namespace OMA.Erdos1052Z16

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1 hiding H1 H2 main

theorem prime_61414943 : Nat.Prime 61414943 := by
  refine lucas_primality 61414943 (5 : ZMod 61414943) ?_ (fun q hq hd => ?_)
  · rw [show 61414943 - 1 = 61414942 from by norm_num]
    reduce_mod_char
  · have e : 61414943 - 1 = [2 ^ 1, 30707471 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61414943 - 1) / 2 = 30707471 from by norm_num]
      have h2 : (5 : ZMod 61414943) ^ 30707471 = ((61414942 : ℕ) : ZMod 61414943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61414943 - 1) / 30707471 = 2 from by norm_num]
      have h2 : (5 : ZMod 61414943) ^ 2 = ((25 : ℕ) : ZMod 61414943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_234850742033 : Nat.Prime 234850742033 := by
  refine lucas_primality 234850742033 (3 : ZMod 234850742033) ?_ (fun q hq hd => ?_)
  · rw [show 234850742033 - 1 = 234850742032 from by norm_num]
    reduce_mod_char
  · have e : 234850742033 - 1 = [2 ^ 4, 239 ^ 1, 61414943 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234850742033 - 1) / 2 = 117425371016 from by norm_num]
      have h2 : (3 : ZMod 234850742033) ^ 117425371016 = ((234850742032 : ℕ) : ZMod 234850742033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234850742033 - 1) / 239 = 982639088 from by norm_num]
      have h2 : (3 : ZMod 234850742033) ^ 982639088 = ((108122845972 : ℕ) : ZMod 234850742033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_61414943).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (234850742033 - 1) / 61414943 = 3824 from by norm_num]
      have h2 : (3 : ZMod 234850742033) ^ 3824 = ((224361847871 : ℕ) : ZMod 234850742033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31879515457326527173216321 : Nat.Prime 31879515457326527173216321 := by
  refine lucas_primality 31879515457326527173216321 (26 : ZMod 31879515457326527173216321) ?_ (fun q hq hd => ?_)
  · rw [show 31879515457326527173216321 - 1 = 31879515457326527173216320 from by norm_num]
    reduce_mod_char
  · have e : 31879515457326527173216321 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 29 ^ 2, 137 ^ 1, 10313 ^ 1, 234850742033 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 2 = 15939757728663263586608160 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 15939757728663263586608160 = ((31879515457326527173216320 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 3 = 10626505152442175724405440 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 10626505152442175724405440 = ((10026574331554652199999786 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 5 = 6375903091465305434643264 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 6375903091465305434643264 = ((18559905867995493885096424 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 7 = 4554216493903789596173760 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 4554216493903789596173760 = ((8547349067384223626022263 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 17 = 1875265615136854539600960 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 1875265615136854539600960 = ((11890349281208590615569816 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 29 = 1099293636459535419766080 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 1099293636459535419766080 = ((6783366848111998865315482 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 137 = 232697193119171731191360 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 232697193119171731191360 = ((31416864911989706075164555 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 10313 = 3091197077215798232640 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 3091197077215798232640 = ((5782205520453166054460405 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_234850742033).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31879515457326527173216321 - 1) / 234850742033 = 135743728895040 from by norm_num]
      have h2 : (26 : ZMod 31879515457326527173216321) ^ 135743728895040 = ((20771030968887967048008078 : ℕ) : ZMod 31879515457326527173216321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15939757728663263586608161 : Nat.Prime 15939757728663263586608161 := by
  refine lucas_primality 15939757728663263586608161 (26 : ZMod 15939757728663263586608161) ?_ (fun q hq hd => ?_)
  · rw [show 15939757728663263586608161 - 1 = 15939757728663263586608160 from by norm_num]
    reduce_mod_char
  · have e : 15939757728663263586608161 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 29 ^ 2, 137 ^ 1, 10313 ^ 1, 234850742033 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 2 = 7969878864331631793304080 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 7969878864331631793304080 = ((15939757728663263586608160 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 3 = 5313252576221087862202720 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 5313252576221087862202720 = ((3992462614560 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 5 = 3187951545732652717321632 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 3187951545732652717321632 = ((2750591446329343967505167 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 7 = 2277108246951894798086880 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 2277108246951894798086880 = ((5381427512381004270374879 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 17 = 937632807568427269800480 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 937632807568427269800480 = ((5797249298411637041422719 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 29 = 549646818229767709883040 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 549646818229767709883040 = ((12547787240546224677966376 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 137 = 116348596559585865595680 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 116348596559585865595680 = ((5077208056507924450284715 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 10313 = 1545598538607899116320 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 1545598538607899116320 = ((13896286851741975960857535 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_234850742033).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15939757728663263586608161 - 1) / 234850742033 = 67871864447520 from by norm_num]
      have h2 : (26 : ZMod 15939757728663263586608161) ^ 67871864447520 = ((406049893489245087216179 : ℕ) : ZMod 15939757728663263586608161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_325188939908904785521061417281 : Nat.Prime 325188939908904785521061417281 := by
  refine lucas_primality 325188939908904785521061417281 (14 : ZMod 325188939908904785521061417281) ?_ (fun q hq hd => ?_)
  · rw [show 325188939908904785521061417281 - 1 = 325188939908904785521061417280 from by norm_num]
    reduce_mod_char
  · have e : 325188939908904785521061417281 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 13 ^ 1, 17 ^ 1, 37 ^ 1, 41 ^ 1, 113 ^ 1, 25057 ^ 1, 8377153 ^ 1, 14199121 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 2 = 162594469954452392760530708640 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 162594469954452392760530708640 = ((325188939908904785521061417280 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 3 = 108396313302968261840353805760 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 108396313302968261840353805760 = ((251063940734115895426109020780 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 5 = 65037787981780957104212283456 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 65037787981780957104212283456 = ((308254825666842316340688296471 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 13 = 25014533839146521963158570560 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 25014533839146521963158570560 = ((200482837308085948069268402297 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 17 = 19128761171112046207121259840 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 19128761171112046207121259840 = ((17222425384088160540629839154 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 37 = 8788890267808237446515173440 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 8788890267808237446515173440 = ((177667401031391937936893194541 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 41 = 7931437558753775256611254080 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 7931437558753775256611254080 = ((87747395895915600188073540473 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 113 = 2877778229282343234699658560 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 2877778229282343234699658560 = ((231878689139329214521691911202 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 25057 = 12977967829704465240095040 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 12977967829704465240095040 = ((150555966708461457196736974162 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 8377153 = 38818550873895318077760 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 38818550873895318077760 = ((248447662759100858593984557667 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (325188939908904785521061417281 - 1) / 14199121 = 22902047240030195215680 from by norm_num]
      have h2 : (14 : ZMod 325188939908904785521061417281) ^ 22902047240030195215680 = ((197424725247494909398029691920 : ℕ) : ZMod 325188939908904785521061417281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1110085633 : Nat.Prime 1110085633 := by
  refine lucas_primality 1110085633 (5 : ZMod 1110085633) ?_ (fun q hq hd => ?_)
  · rw [show 1110085633 - 1 = 1110085632 from by norm_num]
    reduce_mod_char
  · have e : 1110085633 - 1 = [2 ^ 12, 3 ^ 2, 30113 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1110085633 - 1) / 2 = 555042816 from by norm_num]
      have h2 : (5 : ZMod 1110085633) ^ 555042816 = ((1110085632 : ℕ) : ZMod 1110085633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1110085633 - 1) / 3 = 370028544 from by norm_num]
      have h2 : (5 : ZMod 1110085633) ^ 370028544 = ((320444854 : ℕ) : ZMod 1110085633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1110085633 - 1) / 30113 = 36864 from by norm_num]
      have h2 : (5 : ZMod 1110085633) ^ 36864 = ((148421400 : ℕ) : ZMod 1110085633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52898477 : Nat.Prime 52898477 := by
  refine lucas_primality 52898477 (2 : ZMod 52898477) ?_ (fun q hq hd => ?_)
  · rw [show 52898477 - 1 = 52898476 from by norm_num]
    reduce_mod_char
  · have e : 52898477 - 1 = [2 ^ 2, 13224619 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52898477 - 1) / 2 = 26449238 from by norm_num]
      have h2 : (2 : ZMod 52898477) ^ 26449238 = ((52898476 : ℕ) : ZMod 52898477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52898477 - 1) / 13224619 = 4 from by norm_num]
      have h2 : (2 : ZMod 52898477) ^ 4 = ((16 : ℕ) : ZMod 52898477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_250527187073 : Nat.Prime 250527187073 := by
  refine lucas_primality 250527187073 (3 : ZMod 250527187073) ?_ (fun q hq hd => ?_)
  · rw [show 250527187073 - 1 = 250527187072 from by norm_num]
    reduce_mod_char
  · have e : 250527187073 - 1 = [2 ^ 7, 37 ^ 1, 52898477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250527187073 - 1) / 2 = 125263593536 from by norm_num]
      have h2 : (3 : ZMod 250527187073) ^ 125263593536 = ((250527187072 : ℕ) : ZMod 250527187073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250527187073 - 1) / 37 = 6771005056 from by norm_num]
      have h2 : (3 : ZMod 250527187073) ^ 6771005056 = ((73098012373 : ℕ) : ZMod 250527187073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_52898477).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250527187073 - 1) / 52898477 = 4736 from by norm_num]
      have h2 : (3 : ZMod 250527187073) ^ 4736 = ((135569100508 : ℕ) : ZMod 250527187073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_353366276339896558409817277595521 : Nat.Prime 353366276339896558409817277595521 := by
  refine lucas_primality 353366276339896558409817277595521 (23 : ZMod 353366276339896558409817277595521) ?_ (fun q hq hd => ?_)
  · rw [show 353366276339896558409817277595521 - 1 = 353366276339896558409817277595520 from by norm_num]
    reduce_mod_char
  · have e : 353366276339896558409817277595521 - 1 = [2 ^ 7, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 19 ^ 1, 1277 ^ 1, 3121 ^ 1, 81523681 ^ 1, 250527187073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 2 = 176683138169948279204908638797760 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 176683138169948279204908638797760 = ((353366276339896558409817277595520 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 3 = 117788758779965519469939092531840 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 117788758779965519469939092531840 = ((11227168731416576475767484081526 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 5 = 70673255267979311681963455519104 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 70673255267979311681963455519104 = ((166719113813759394132078149108217 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 7 = 50480896619985222629973896799360 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 50480896619985222629973896799360 = ((75210062319184605328193806158918 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 17 = 20786251549405679906459839858560 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 20786251549405679906459839858560 = ((4158673343407072709998035152955 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 19 = 18598225070520871495253540926080 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 18598225070520871495253540926080 = ((8917039189690758832612779127806 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 1277 = 276715956413388064533921125760 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 276715956413388064533921125760 = ((245156322614457035024146388565557 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 3121 = 113222132758698032172322101120 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 113222132758698032172322101120 = ((163403633521597602529274426229665 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81523681).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 81523681 = 4334523073607244972289920 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 4334523073607244972289920 = ((92463361383891393969405985917193 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_250527187073).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (353366276339896558409817277595521 - 1) / 250527187073 = 1410490735430365626240 from by norm_num]
      have h2 : (23 : ZMod 353366276339896558409817277595521) ^ 1410490735430365626240 = ((127555481171293529814637891740757 : ℕ) : ZMod 353366276339896558409817277595521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_176683138169948279204908638797761 : Nat.Prime 176683138169948279204908638797761 := by
  refine lucas_primality 176683138169948279204908638797761 (11 : ZMod 176683138169948279204908638797761) ?_ (fun q hq hd => ?_)
  · rw [show 176683138169948279204908638797761 - 1 = 176683138169948279204908638797760 from by norm_num]
    reduce_mod_char
  · have e : 176683138169948279204908638797761 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 19 ^ 1, 1277 ^ 1, 3121 ^ 1, 81523681 ^ 1, 250527187073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 2 = 88341569084974139602454319398880 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 88341569084974139602454319398880 = ((176683138169948279204908638797760 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 3 = 58894379389982759734969546265920 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 58894379389982759734969546265920 = ((176683138169948265912687674265600 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 5 = 35336627633989655840981727759552 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 35336627633989655840981727759552 = ((117792000249367148600166855037119 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 7 = 25240448309992611314986948399680 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 25240448309992611314986948399680 = ((128993710140139339285470989578122 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 17 = 10393125774702839953229919929280 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 10393125774702839953229919929280 = ((141818082460043711035536798965620 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 19 = 9299112535260435747626770463040 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 9299112535260435747626770463040 = ((41006080693962614463962207537282 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 1277 = 138357978206694032266960562880 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 138357978206694032266960562880 = ((17641893620388497134657123493822 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 3121 = 56611066379349016086161050560 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 56611066379349016086161050560 = ((11909214062770608536589980852582 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81523681).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 81523681 = 2167261536803622486144960 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 2167261536803622486144960 = ((24585341876828098247960387626161 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_250527187073).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176683138169948279204908638797761 - 1) / 250527187073 = 705245367715182813120 from by norm_num]
      have h2 : (11 : ZMod 176683138169948279204908638797761) ^ 705245367715182813120 = ((58950745479151855161523693033825 : ℕ) : ZMod 176683138169948279204908638797761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_142307322503233 : Nat.Prime 142307322503233 := by
  refine lucas_primality 142307322503233 (5 : ZMod 142307322503233) ?_ (fun q hq hd => ?_)
  · rw [show 142307322503233 - 1 = 142307322503232 from by norm_num]
    reduce_mod_char
  · have e : 142307322503233 - 1 = [2 ^ 6, 3 ^ 1, 353 ^ 1, 43133 ^ 1, 48679 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142307322503233 - 1) / 2 = 71153661251616 from by norm_num]
      have h2 : (5 : ZMod 142307322503233) ^ 71153661251616 = ((142307322503232 : ℕ) : ZMod 142307322503233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142307322503233 - 1) / 3 = 47435774167744 from by norm_num]
      have h2 : (5 : ZMod 142307322503233) ^ 47435774167744 = ((68039622838148 : ℕ) : ZMod 142307322503233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142307322503233 - 1) / 353 = 403136890944 from by norm_num]
      have h2 : (5 : ZMod 142307322503233) ^ 403136890944 = ((27846003087179 : ℕ) : ZMod 142307322503233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142307322503233 - 1) / 43133 = 3299267904 from by norm_num]
      have h2 : (5 : ZMod 142307322503233) ^ 3299267904 = ((20820179347178 : ℕ) : ZMod 142307322503233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142307322503233 - 1) / 48679 = 2923382208 from by norm_num]
      have h2 : (5 : ZMod 142307322503233) ^ 2923382208 = ((100580776436837 : ℕ) : ZMod 142307322503233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_68134087338311652398492776425866401 : Nat.Prime 68134087338311652398492776425866401 := by
  refine lucas_primality 68134087338311652398492776425866401 (11 : ZMod 68134087338311652398492776425866401) ?_ (fun q hq hd => ?_)
  · rw [show 68134087338311652398492776425866401 - 1 = 68134087338311652398492776425866400 from by norm_num]
    reduce_mod_char
  · have e : 68134087338311652398492776425866401 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 2, 13 ^ 1, 17 ^ 1, 29 ^ 1, 79 ^ 1, 113 ^ 1, 1297 ^ 1, 2688377 ^ 1, 142307322503233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 2 = 34067043669155826199246388212933200 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 34067043669155826199246388212933200 = ((68134087338311652398492776425866400 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 3 = 22711362446103884132830925475288800 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 22711362446103884132830925475288800 = ((50571493955820416490068412296128818 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 5 = 13626817467662330479698555285173280 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 13626817467662330479698555285173280 = ((20807534080535058380804194048772167 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 13 = 5241083641408588646037905878912800 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 5241083641408588646037905878912800 = ((27532915166281206418048905227946925 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 17 = 4007887490488920729323104495639200 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 4007887490488920729323104495639200 = ((43422032246595106048050106547662793 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 29 = 2349451287527988013741130221581600 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 2349451287527988013741130221581600 = ((26877974583475783369618413435386952 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 79 = 862456801750780410107503499061600 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 862456801750780410107503499061600 = ((44604967181161284226524421220950701 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 113 = 602956525117802233614980322352800 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 602956525117802233614980322352800 = ((54878300394436514689426524532615240 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 1297 = 52532064254673594755969758231200 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 52532064254673594755969758231200 = ((36806465095408500655918365857589515 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 2688377 = 25343948165867976254257783200 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 25343948165867976254257783200 = ((58990117128135805548355683896182749 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_142307322503233).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68134087338311652398492776425866401 - 1) / 142307322503233 = 478781317361682160800 from by norm_num]
      have h2 : (11 : ZMod 68134087338311652398492776425866401) ^ 478781317361682160800 = ((51233322568819479967688695549484591 : ℕ) : ZMod 68134087338311652398492776425866401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4235092033 : Nat.Prime 4235092033 := by
  refine lucas_primality 4235092033 (5 : ZMod 4235092033) ?_ (fun q hq hd => ?_)
  · rw [show 4235092033 - 1 = 4235092032 from by norm_num]
    reduce_mod_char
  · have e : 4235092033 - 1 = [2 ^ 6, 3 ^ 1, 31 ^ 1, 139 ^ 1, 5119 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4235092033 - 1) / 2 = 2117546016 from by norm_num]
      have h2 : (5 : ZMod 4235092033) ^ 2117546016 = ((4235092032 : ℕ) : ZMod 4235092033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4235092033 - 1) / 3 = 1411697344 from by norm_num]
      have h2 : (5 : ZMod 4235092033) ^ 1411697344 = ((2493391609 : ℕ) : ZMod 4235092033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4235092033 - 1) / 31 = 136615872 from by norm_num]
      have h2 : (5 : ZMod 4235092033) ^ 136615872 = ((2697106735 : ℕ) : ZMod 4235092033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4235092033 - 1) / 139 = 30468288 from by norm_num]
      have h2 : (5 : ZMod 4235092033) ^ 30468288 = ((357534981 : ℕ) : ZMod 4235092033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4235092033 - 1) / 5119 = 827328 from by norm_num]
      have h2 : (5 : ZMod 4235092033) ^ 827328 = ((2760732889 : ℕ) : ZMod 4235092033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_182992606302133822302202039519035841 : Nat.Prime 182992606302133822302202039519035841 := by
  refine lucas_primality 182992606302133822302202039519035841 (13 : ZMod 182992606302133822302202039519035841) ?_ (fun q hq hd => ?_)
  · rw [show 182992606302133822302202039519035841 - 1 = 182992606302133822302202039519035840 from by norm_num]
    reduce_mod_char
  · have e : 182992606302133822302202039519035841 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 41 ^ 1, 83 ^ 1, 97 ^ 1, 2789 ^ 1, 43313 ^ 1, 9485321 ^ 1, 4235092033 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 2 = 91496303151066911151101019759517920 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 91496303151066911151101019759517920 = ((182992606302133822302202039519035840 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 3 = 60997535434044607434067346506345280 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 60997535434044607434067346506345280 = ((4115853405084702008649119187774199 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 5 = 36598521260426764460440407903807168 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 36598521260426764460440407903807168 = ((79393780990200188555031524710101566 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 7 = 26141800900304831757457434217005120 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 26141800900304831757457434217005120 = ((34403496687529888155204638141930079 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 17 = 10764270958949048370717767030531520 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 10764270958949048370717767030531520 = ((42255935134280558801632577713502029 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 41 = 4463234300052044446395171695586240 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 4463234300052044446395171695586240 = ((113175454698024820496285432694686655 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 83 = 2204730196411250871110867946012480 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 2204730196411250871110867946012480 = ((43447296883381108054489614145078380 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 97 = 1886521714454987858785588036278720 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 1886521714454987858785588036278720 = ((41814373657474271601807006108818839 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 2789 = 65612264719302195160344940666560 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 65612264719302195160344940666560 = ((37956272343146333611874105120079352 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 43313 = 4224888747076716512414333791680 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 4224888747076716512414333791680 = ((106455075227315922647129484314659614 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 9485321 = 19292189089028597166316463040 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 19292189089028597166316463040 = ((113225446285240250155596668088924977 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4235092033).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182992606302133822302202039519035841 - 1) / 4235092033 = 43208649275210171637420480 from by norm_num]
      have h2 : (13 : ZMod 182992606302133822302202039519035841) ^ 43208649275210171637420480 = ((121957513395308986385510161231331249 : ℕ) : ZMod 182992606302133822302202039519035841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_143446410721 : Nat.Prime 143446410721 := by
  refine lucas_primality 143446410721 (14 : ZMod 143446410721) ?_ (fun q hq hd => ?_)
  · rw [show 143446410721 - 1 = 143446410720 from by norm_num]
    reduce_mod_char
  · have e : 143446410721 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 17 ^ 1, 43 ^ 1, 136273 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 2 = 71723205360 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 71723205360 = ((143446410720 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 3 = 47815470240 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 47815470240 = ((113756234075 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 5 = 28689282144 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 28689282144 = ((117025909673 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 17 = 8438024160 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 8438024160 = ((64530609192 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 43 = 3335963040 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 3335963040 = ((33271344090 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (143446410721 - 1) / 136273 = 1052640 from by norm_num]
      have h2 : (14 : ZMod 143446410721) ^ 1052640 = ((27795341151 : ℕ) : ZMod 143446410721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_321890125642414371933129862358702881 : Nat.Prime 321890125642414371933129862358702881 := by
  refine lucas_primality 321890125642414371933129862358702881 (7 : ZMod 321890125642414371933129862358702881) ?_ (fun q hq hd => ?_)
  · rw [show 321890125642414371933129862358702881 - 1 = 321890125642414371933129862358702880 from by norm_num]
    reduce_mod_char
  · have e : 321890125642414371933129862358702881 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 29 ^ 1, 41 ^ 1, 43 ^ 1, 73 ^ 1, 769 ^ 1, 164513 ^ 1, 582409 ^ 1, 143446410721 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 2 = 160945062821207185966564931179351440 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 160945062821207185966564931179351440 = ((321890125642414371933129862358702880 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 3 = 107296708547471457311043287452900960 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 107296708547471457311043287452900960 = ((313007961329394725347128116007713155 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 5 = 64378025128482874386625972471740576 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 64378025128482874386625972471740576 = ((196387319919881182759458378200056943 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 17 = 18934713273083198349007638962276640 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 18934713273083198349007638962276640 = ((169281481827731942056235815368132673 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 29 = 11099659504910840411487236633058720 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 11099659504910840411487236633058720 = ((278879219107665961308050571435858588 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 41 = 7850978674205228583734874691675680 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 7850978674205228583734874691675680 = ((54258484004471495998656456372765306 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 43 = 7485816875404985393793717729272160 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 7485816875404985393793717729272160 = ((206156877754975527821896423860816097 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 73 = 4409453775923484547029176196694560 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 4409453775923484547029176196694560 = ((196264600023543035018039100211776628 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 769 = 418582738156585659210832070687520 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 418582738156585659210832070687520 = ((235646975206275131899888872186657778 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 164513 = 1956624252444575030138225321760 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 1956624252444575030138225321760 = ((305461486771814183333487214411774269 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 582409 = 552687416647775655824566348320 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 552687416647775655824566348320 = ((175638158690427328614920325033627541 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_143446410721).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (321890125642414371933129862358702881 - 1) / 143446410721 = 2243974763986833599381280 from by norm_num]
      have h2 : (7 : ZMod 321890125642414371933129862358702881) ^ 2243974763986833599381280 = ((106305912549014289295586763819767477 : ℕ) : ZMod 321890125642414371933129862358702881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_180385374178753 : Nat.Prime 180385374178753 := by
  refine lucas_primality 180385374178753 (5 : ZMod 180385374178753) ?_ (fun q hq hd => ?_)
  · rw [show 180385374178753 - 1 = 180385374178752 from by norm_num]
    reduce_mod_char
  · have e : 180385374178753 - 1 = [2 ^ 6, 3 ^ 1, 17 ^ 1, 5813 ^ 1, 9507161 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (180385374178753 - 1) / 2 = 90192687089376 from by norm_num]
      have h2 : (5 : ZMod 180385374178753) ^ 90192687089376 = ((180385374178752 : ℕ) : ZMod 180385374178753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (180385374178753 - 1) / 3 = 60128458059584 from by norm_num]
      have h2 : (5 : ZMod 180385374178753) ^ 60128458059584 = ((51743174605532 : ℕ) : ZMod 180385374178753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (180385374178753 - 1) / 17 = 10610904363456 from by norm_num]
      have h2 : (5 : ZMod 180385374178753) ^ 10610904363456 = ((557293194378 : ℕ) : ZMod 180385374178753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (180385374178753 - 1) / 5813 = 31031373504 from by norm_num]
      have h2 : (5 : ZMod 180385374178753) ^ 31031373504 = ((8712368297316 : ℕ) : ZMod 180385374178753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (180385374178753 - 1) / 9507161 = 18973632 from by norm_num]
      have h2 : (5 : ZMod 180385374178753) ^ 18973632 = ((2533960082678 : ℕ) : ZMod 180385374178753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3024260707038777360639558573762398401 : Nat.Prime 3024260707038777360639558573762398401 := by
  refine lucas_primality 3024260707038777360639558573762398401 (13 : ZMod 3024260707038777360639558573762398401) ?_ (fun q hq hd => ?_)
  · rw [show 3024260707038777360639558573762398401 - 1 = 3024260707038777360639558573762398400 from by norm_num]
    reduce_mod_char
  · have e : 3024260707038777360639558573762398401 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 2, 11 ^ 1, 17 ^ 1, 401 ^ 1, 19801 ^ 1, 784119601 ^ 1, 180385374178753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 2 = 1512130353519388680319779286881199200 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 1512130353519388680319779286881199200 = ((3024260707038777360639558573762398400 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 3 = 1008086902346259120213186191254132800 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 1008086902346259120213186191254132800 = ((834767492046117312119259142401148181 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 5 = 604852141407755472127911714752479680 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 604852141407755472127911714752479680 = ((2215711275349701801920029450286918502 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 11 = 274932791548979760058141688523854400 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 274932791548979760058141688523854400 = ((2879646734424894190230106251903066958 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 17 = 177897688649339844743503445515435200 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 177897688649339844743503445515435200 = ((2255429149900171837552847446979809615 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 401 = 7541797274410916111320594947038400 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 7541797274410916111320594947038400 = ((1082449692934370201297668658928602382 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 19801 = 152732725975394038717214210078400 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 152732725975394038717214210078400 = ((2484906217256619748275406028460396567 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_784119601).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 784119601 = 3856887014661909160257758400 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 3856887014661909160257758400 = ((1823084417871471781884462503611627777 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_180385374178753).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3024260707038777360639558573762398401 - 1) / 180385374178753 = 16765553863817608132800 from by norm_num]
      have h2 : (13 : ZMod 3024260707038777360639558573762398401) ^ 16765553863817608132800 = ((2632059641751034360238189952396641764 : ℕ) : ZMod 3024260707038777360639558573762398401) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_71811199 : Nat.Prime 71811199 := by
  refine lucas_primality 71811199 (3 : ZMod 71811199) ?_ (fun q hq hd => ?_)
  · rw [show 71811199 - 1 = 71811198 from by norm_num]
    reduce_mod_char
  · have e : 71811199 - 1 = [2 ^ 1, 3 ^ 4, 23 ^ 1, 19273 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71811199 - 1) / 2 = 35905599 from by norm_num]
      have h2 : (3 : ZMod 71811199) ^ 35905599 = ((71811198 : ℕ) : ZMod 71811199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71811199 - 1) / 3 = 23937066 from by norm_num]
      have h2 : (3 : ZMod 71811199) ^ 23937066 = ((65620724 : ℕ) : ZMod 71811199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71811199 - 1) / 23 = 3122226 from by norm_num]
      have h2 : (3 : ZMod 71811199) ^ 3122226 = ((71542929 : ℕ) : ZMod 71811199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71811199 - 1) / 19273 = 3726 from by norm_num]
      have h2 : (3 : ZMod 71811199) ^ 3726 = ((27113777 : ℕ) : ZMod 71811199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62352909436247 : Nat.Prime 62352909436247 := by
  refine lucas_primality 62352909436247 (5 : ZMod 62352909436247) ?_ (fun q hq hd => ?_)
  · rw [show 62352909436247 - 1 = 62352909436246 from by norm_num]
    reduce_mod_char
  · have e : 62352909436247 - 1 = [2 ^ 1, 11 ^ 2, 13 ^ 1, 71761 ^ 1, 276191 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62352909436247 - 1) / 2 = 31176454718123 from by norm_num]
      have h2 : (5 : ZMod 62352909436247) ^ 31176454718123 = ((62352909436246 : ℕ) : ZMod 62352909436247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62352909436247 - 1) / 11 = 5668446312386 from by norm_num]
      have h2 : (5 : ZMod 62352909436247) ^ 5668446312386 = ((14277723645615 : ℕ) : ZMod 62352909436247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62352909436247 - 1) / 13 = 4796377648942 from by norm_num]
      have h2 : (5 : ZMod 62352909436247) ^ 4796377648942 = ((12568515765084 : ℕ) : ZMod 62352909436247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62352909436247 - 1) / 71761 = 868896886 from by norm_num]
      have h2 : (5 : ZMod 62352909436247) ^ 868896886 = ((49790629284353 : ℕ) : ZMod 62352909436247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62352909436247 - 1) / 276191 = 225760106 from by norm_num]
      have h2 : (5 : ZMod 62352909436247) ^ 225760106 = ((28727347635017 : ℕ) : ZMod 62352909436247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_498823275489977 : Nat.Prime 498823275489977 := by
  refine lucas_primality 498823275489977 (3 : ZMod 498823275489977) ?_ (fun q hq hd => ?_)
  · rw [show 498823275489977 - 1 = 498823275489976 from by norm_num]
    reduce_mod_char
  · have e : 498823275489977 - 1 = [2 ^ 3, 62352909436247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (498823275489977 - 1) / 2 = 249411637744988 from by norm_num]
      have h2 : (3 : ZMod 498823275489977) ^ 249411637744988 = ((498823275489976 : ℕ) : ZMod 498823275489977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_62352909436247).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (498823275489977 - 1) / 62352909436247 = 8 from by norm_num]
      have h2 : (3 : ZMod 498823275489977) ^ 8 = ((6561 : ℕ) : ZMod 498823275489977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_111736413709754849 : Nat.Prime 111736413709754849 := by
  refine lucas_primality 111736413709754849 (3 : ZMod 111736413709754849) ?_ (fun q hq hd => ?_)
  · rw [show 111736413709754849 - 1 = 111736413709754848 from by norm_num]
    reduce_mod_char
  · have e : 111736413709754849 - 1 = [2 ^ 5, 7 ^ 1, 498823275489977 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111736413709754849 - 1) / 2 = 55868206854877424 from by norm_num]
      have h2 : (3 : ZMod 111736413709754849) ^ 55868206854877424 = ((111736413709754848 : ℕ) : ZMod 111736413709754849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111736413709754849 - 1) / 7 = 15962344815679264 from by norm_num]
      have h2 : (3 : ZMod 111736413709754849) ^ 15962344815679264 = ((77641680035349217 : ℕ) : ZMod 111736413709754849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_498823275489977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111736413709754849 - 1) / 498823275489977 = 224 from by norm_num]
      have h2 : (3 : ZMod 111736413709754849) ^ 224 = ((63923073481836398 : ℕ) : ZMod 111736413709754849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3836148153553 : Nat.Prime 3836148153553 := by
  refine lucas_primality 3836148153553 (5 : ZMod 3836148153553) ?_ (fun q hq hd => ?_)
  · rw [show 3836148153553 - 1 = 3836148153552 from by norm_num]
    reduce_mod_char
  · have e : 3836148153553 - 1 = [2 ^ 4, 3 ^ 2, 11 ^ 1, 13 ^ 1, 787 ^ 1, 236713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 2 = 1918074076776 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 1918074076776 = ((3836148153552 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 3 = 1278716051184 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 1278716051184 = ((2543429369712 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 11 = 348740741232 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 348740741232 = ((1220751477319 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 13 = 295088319504 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 295088319504 = ((2725403471585 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 787 = 4874394096 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 4874394096 = ((3345737101782 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3836148153553 - 1) / 236713 = 16205904 from by norm_num]
      have h2 : (5 : ZMod 3836148153553) ^ 16205904 = ((447392822515 : ℕ) : ZMod 3836148153553) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56596504371295886017 : Nat.Prime 56596504371295886017 := by
  refine lucas_primality 56596504371295886017 (5 : ZMod 56596504371295886017) ?_ (fun q hq hd => ?_)
  · rw [show 56596504371295886017 - 1 = 56596504371295886016 from by norm_num]
    reduce_mod_char
  · have e : 56596504371295886017 - 1 = [2 ^ 6, 3 ^ 1, 43 ^ 1, 1787 ^ 1, 3836148153553 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56596504371295886017 - 1) / 2 = 28298252185647943008 from by norm_num]
      have h2 : (5 : ZMod 56596504371295886017) ^ 28298252185647943008 = ((56596504371295886016 : ℕ) : ZMod 56596504371295886017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56596504371295886017 - 1) / 3 = 18865501457098628672 from by norm_num]
      have h2 : (5 : ZMod 56596504371295886017) ^ 18865501457098628672 = ((39048228862120700577 : ℕ) : ZMod 56596504371295886017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56596504371295886017 - 1) / 43 = 1316197776076648512 from by norm_num]
      have h2 : (5 : ZMod 56596504371295886017) ^ 1316197776076648512 = ((17486556890653375573 : ℕ) : ZMod 56596504371295886017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56596504371295886017 - 1) / 1787 = 31671239155733568 from by norm_num]
      have h2 : (5 : ZMod 56596504371295886017) ^ 31671239155733568 = ((4694459649832789948 : ℕ) : ZMod 56596504371295886017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3836148153553).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56596504371295886017 - 1) / 3836148153553 = 14753472 from by norm_num]
      have h2 : (5 : ZMod 56596504371295886017) ^ 14753472 = ((52996512394469971533 : ℕ) : ZMod 56596504371295886017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1998628480753 : Nat.Prime 1998628480753 := by
  refine lucas_primality 1998628480753 (5 : ZMod 1998628480753) ?_ (fun q hq hd => ?_)
  · rw [show 1998628480753 - 1 = 1998628480752 from by norm_num]
    reduce_mod_char
  · have e : 1998628480753 - 1 = [2 ^ 4, 3 ^ 1, 71 ^ 1, 19997 ^ 1, 29327 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1998628480753 - 1) / 2 = 999314240376 from by norm_num]
      have h2 : (5 : ZMod 1998628480753) ^ 999314240376 = ((1998628480752 : ℕ) : ZMod 1998628480753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1998628480753 - 1) / 3 = 666209493584 from by norm_num]
      have h2 : (5 : ZMod 1998628480753) ^ 666209493584 = ((1772934675526 : ℕ) : ZMod 1998628480753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1998628480753 - 1) / 71 = 28149696912 from by norm_num]
      have h2 : (5 : ZMod 1998628480753) ^ 28149696912 = ((848837658479 : ℕ) : ZMod 1998628480753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1998628480753 - 1) / 19997 = 99946416 from by norm_num]
      have h2 : (5 : ZMod 1998628480753) ^ 99946416 = ((593402165005 : ℕ) : ZMod 1998628480753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1998628480753 - 1) / 29327 = 68149776 from by norm_num]
      have h2 : (5 : ZMod 1998628480753) ^ 68149776 = ((1118037163852 : ℕ) : ZMod 1998628480753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_137340670268189743177332632848914035541595201 : Nat.Prime 137340670268189743177332632848914035541595201 := by
  refine lucas_primality 137340670268189743177332632848914035541595201 (7 : ZMod 137340670268189743177332632848914035541595201) ?_ (fun q hq hd => ?_)
  · rw [show 137340670268189743177332632848914035541595201 - 1 = 137340670268189743177332632848914035541595200 from by norm_num]
    reduce_mod_char
  · have e : 137340670268189743177332632848914035541595201 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 2, 13 ^ 1, 17 ^ 1, 23 ^ 1, 61 ^ 1, 173 ^ 1, 1249 ^ 1, 4153 ^ 1, 3319633 ^ 1, 15499417 ^ 1, 1998628480753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 2 = 68670335134094871588666316424457017770797600 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 68670335134094871588666316424457017770797600 = ((137340670268189743177332632848914035541595200 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 3 = 45780223422729914392444210949638011847198400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 45780223422729914392444210949638011847198400 = ((48968139578352538311257892301333660626141152 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 5 = 27468134053637948635466526569782807108319040 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 27468134053637948635466526569782807108319040 = ((118212813345578693101902793912201776393999614 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 13 = 10564666943706903321333279449916464272430400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 10564666943706903321333279449916464272430400 = ((71900184283610249981520194104982621217134437 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 17 = 8078862956952337833960743108759649149505600 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 8078862956952337833960743108759649149505600 = ((45300380566917595924939322668696481029095830 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 23 = 5971333489921293181623157949952784153982400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 5971333489921293181623157949952784153982400 = ((77874008265505600670033034106600242291471522 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 61 = 2251486397839176117661190702441213697403200 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 2251486397839176117661190702441213697403200 = ((4139147036073312383009629858114895017876371 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 173 = 793876706752541868077067241901237199662400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 793876706752541868077067241901237199662400 = ((51248266455319716222933760939008594011420069 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 1249 = 109960504618246391655190258485919964404800 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 109960504618246391655190258485919964404800 = ((68478002035091467292222783055186745899518794 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 4153 = 33070231222776244444337258090275472078400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 33070231222776244444337258090275472078400 = ((34530308958951213309442735818689802382174841 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 3319633 = 41372245145228325895462731226287374400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 41372245145228325895462731226287374400 = ((45790849349204139025504016985917965749994752 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 15499417 = 8861021693150764520841824750499585600 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 8861021693150764520841824750499585600 = ((63138565243739674684841688416985625071986176 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1998628480753).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (137340670268189743177332632848914035541595201 - 1) / 1998628480753 = 68717458792764474519236803598400 from by norm_num]
      have h2 : (7 : ZMod 137340670268189743177332632848914035541595201) ^ 68717458792764474519236803598400 = ((82911653662216992892805953040698786454159960 : ℕ) : ZMod 137340670268189743177332632848914035541595201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67877332801 : Nat.Prime 67877332801 := by
  refine lucas_primality 67877332801 (14 : ZMod 67877332801) ?_ (fun q hq hd => ?_)
  · rw [show 67877332801 - 1 = 67877332800 from by norm_num]
    reduce_mod_char
  · have e : 67877332801 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 2, 19 ^ 1, 101 ^ 1, 7369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 2 = 33938666400 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 33938666400 = ((67877332800 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 3 = 22625777600 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 22625777600 = ((5154346374 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 5 = 13575466560 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 13575466560 = ((5200596782 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 19 = 3572491200 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 3572491200 = ((59126839537 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 101 = 672052800 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 672052800 = ((52977531416 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67877332801 - 1) / 7369 = 9211200 from by norm_num]
      have h2 : (14 : ZMod 67877332801) ^ 9211200 = ((44595845053 : ℕ) : ZMod 67877332801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1444801313 : Nat.Prime 1444801313 := by
  refine lucas_primality 1444801313 (3 : ZMod 1444801313) ?_ (fun q hq hd => ?_)
  · rw [show 1444801313 - 1 = 1444801312 from by norm_num]
    reduce_mod_char
  · have e : 1444801313 - 1 = [2 ^ 5, 107 ^ 1, 233 ^ 1, 1811 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1444801313 - 1) / 2 = 722400656 from by norm_num]
      have h2 : (3 : ZMod 1444801313) ^ 722400656 = ((1444801312 : ℕ) : ZMod 1444801313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1444801313 - 1) / 107 = 13502816 from by norm_num]
      have h2 : (3 : ZMod 1444801313) ^ 13502816 = ((1386758118 : ℕ) : ZMod 1444801313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1444801313 - 1) / 233 = 6200864 from by norm_num]
      have h2 : (3 : ZMod 1444801313) ^ 6200864 = ((1433955575 : ℕ) : ZMod 1444801313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1444801313 - 1) / 1811 = 797792 from by norm_num]
      have h2 : (3 : ZMod 1444801313) ^ 797792 = ((497753138 : ℕ) : ZMod 1444801313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3320045537 : Nat.Prime 3320045537 := by
  refine lucas_primality 3320045537 (3 : ZMod 3320045537) ?_ (fun q hq hd => ?_)
  · rw [show 3320045537 - 1 = 3320045536 from by norm_num]
    reduce_mod_char
  · have e : 3320045537 - 1 = [2 ^ 5, 61 ^ 1, 1039 ^ 1, 1637 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3320045537 - 1) / 2 = 1660022768 from by norm_num]
      have h2 : (3 : ZMod 3320045537) ^ 1660022768 = ((3320045536 : ℕ) : ZMod 3320045537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3320045537 - 1) / 61 = 54426976 from by norm_num]
      have h2 : (3 : ZMod 3320045537) ^ 54426976 = ((961199004 : ℕ) : ZMod 3320045537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3320045537 - 1) / 1039 = 3195424 from by norm_num]
      have h2 : (3 : ZMod 3320045537) ^ 3195424 = ((872721950 : ℕ) : ZMod 3320045537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3320045537 - 1) / 1637 = 2028128 from by norm_num]
      have h2 : (3 : ZMod 3320045537) ^ 2028128 = ((1772345373 : ℕ) : ZMod 3320045537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_169820087978821461720620325094410956611411201 : Nat.Prime 169820087978821461720620325094410956611411201 := by
  refine lucas_primality 169820087978821461720620325094410956611411201 (7 : ZMod 169820087978821461720620325094410956611411201) ?_ (fun q hq hd => ?_)
  · rw [show 169820087978821461720620325094410956611411201 - 1 = 169820087978821461720620325094410956611411200 from by norm_num]
    reduce_mod_char
  · have e : 169820087978821461720620325094410956611411201 - 1 = [2 ^ 8, 3 ^ 1, 5 ^ 2, 17 ^ 1, 19 ^ 1, 101 ^ 1, 113 ^ 1, 7369 ^ 1, 1444801313 ^ 1, 3320045537 ^ 1, 67877332801 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 2 = 84910043989410730860310162547205478305705600 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 84910043989410730860310162547205478305705600 = ((169820087978821461720620325094410956611411200 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 3 = 56606695992940487240206775031470318870470400 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 56606695992940487240206775031470318870470400 = ((135629919678829839448854589007688331950157758 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 5 = 33964017595764292344124065018882191322282240 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 33964017595764292344124065018882191322282240 = ((5241277623593508685932165958018774410342375 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 17 = 9989416939930674218860019123200644506553600 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 9989416939930674218860019123200644506553600 = ((55346529427965477386992560863078302283845368 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 19 = 8937899367306392722137911847074260874284800 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 8937899367306392722137911847074260874284800 = ((128840028119948148358372448241204394419100588 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 101 = 1681387009691301601194260644499118382291200 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 1681387009691301601194260644499118382291200 = ((66814613342392931495243103525051443419046688 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 113 = 1502832636980720900182480753047884571782400 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 1502832636980720900182480753047884571782400 = ((60742406211115152383963884499759389551224996 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 7369 = 23045201245599329857595375911848413164800 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 23045201245599329857595375911848413164800 = ((12830823617919277992082615813091589103167623 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1444801313).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 1444801313 = 117538713766950640721504054374022400 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 117538713766950640721504054374022400 = ((85555752024891655551379435194310311087868269 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3320045537).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 3320045537 = 51149927338728987355037089991097600 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 51149927338728987355037089991097600 = ((101911184298772554615495225302085668369451445 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_67877332801).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (169820087978821461720620325094410956611411201 - 1) / 67877332801 = 2501867427182106281781275572051200 from by norm_num]
      have h2 : (7 : ZMod 169820087978821461720620325094410956611411201) ^ 2501867427182106281781275572051200 = ((134078096393090392639637505808945518415022542 : ℕ) : ZMod 169820087978821461720620325094410956611411201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_769078493 : Nat.Prime 769078493 := by
  refine lucas_primality 769078493 (2 : ZMod 769078493) ?_ (fun q hq hd => ?_)
  · rw [show 769078493 - 1 = 769078492 from by norm_num]
    reduce_mod_char
  · have e : 769078493 - 1 = [2 ^ 2, 7 ^ 1, 13 ^ 1, 29 ^ 1, 41 ^ 1, 1777 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 2 = 384539246 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 384539246 = ((769078492 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 7 = 109868356 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 109868356 = ((464883144 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 13 = 59159884 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 59159884 = ((405809404 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 29 = 26519948 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 26519948 = ((256055988 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 41 = 18758012 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 18758012 = ((178044212 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (769078493 - 1) / 1777 = 432796 from by norm_num]
      have h2 : (2 : ZMod 769078493) ^ 432796 = ((237290140 : ℕ) : ZMod 769078493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22321734180833 : Nat.Prime 22321734180833 := by
  refine lucas_primality 22321734180833 (3 : ZMod 22321734180833) ?_ (fun q hq hd => ?_)
  · rw [show 22321734180833 - 1 = 22321734180832 from by norm_num]
    reduce_mod_char
  · have e : 22321734180833 - 1 = [2 ^ 5, 907 ^ 1, 769078493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22321734180833 - 1) / 2 = 11160867090416 from by norm_num]
      have h2 : (3 : ZMod 22321734180833) ^ 11160867090416 = ((22321734180832 : ℕ) : ZMod 22321734180833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22321734180833 - 1) / 907 = 24610511776 from by norm_num]
      have h2 : (3 : ZMod 22321734180833) ^ 24610511776 = ((16282266683711 : ℕ) : ZMod 22321734180833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_769078493).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22321734180833 - 1) / 769078493 = 29024 from by norm_num]
      have h2 : (3 : ZMod 22321734180833) ^ 29024 = ((19959558582999 : ℕ) : ZMod 22321734180833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_220562984078060416488507466656249330775640641 : Nat.Prime 220562984078060416488507466656249330775640641 := by
  refine lucas_primality 220562984078060416488507466656249330775640641 (13 : ZMod 220562984078060416488507466656249330775640641) ?_ (fun q hq hd => ?_)
  · rw [show 220562984078060416488507466656249330775640641 - 1 = 220562984078060416488507466656249330775640640 from by norm_num]
    reduce_mod_char
  · have e : 220562984078060416488507466656249330775640641 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 11 ^ 1, 17 ^ 1, 103 ^ 1, 953 ^ 1, 5657 ^ 1, 13441 ^ 1, 38069 ^ 1, 27674161 ^ 1, 22321734180833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 2 = 110281492039030208244253733328124665387820320 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 110281492039030208244253733328124665387820320 = ((220562984078060416488507466656249330775640640 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 3 = 73520994692686805496169155552083110258546880 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 73520994692686805496169155552083110258546880 = ((188080463642727552529666736390411813371551635 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 5 = 44112596815612083297701493331249866155128128 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 44112596815612083297701493331249866155128128 = ((162312779883250038035908834891871118691137143 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 7 = 31508997725437202355501066665178475825091520 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 31508997725437202355501066665178475825091520 = ((70076443908458069848356412766730323307335864 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 11 = 20051180370732765135318860605113575525058240 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 20051180370732765135318860605113575525058240 = ((170523650198189538367911935764690184235232329 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 17 = 12974293181062377440500439215073490045625920 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 12974293181062377440500439215073490045625920 = ((67140384537968417977271735268114512025149601 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 103 = 2141388194932625402801043365594653696850880 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 2141388194932625402801043365594653696850880 = ((1739978478295120676015832145104948749352017 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 953 = 231440696829024571341560825452517660834880 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 231440696829024571341560825452517660834880 = ((192431910599376690214898756319449824560103229 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 5657 = 38989390857002018117112863117597548307520 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 38989390857002018117112863117597548307520 = ((211327018824336241774349496796667208258855798 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 13441 = 16409715354368009559445537285637179583040 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 16409715354368009559445537285637179583040 = ((155470644498436990904090754010902855195264681 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 38069 = 5793768790303407404673289728026723338560 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 5793768790303407404673289728026723338560 = ((196985094404760093350434988907119636670333656 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 27674161 = 7969997142029361485918487886814322240 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 7969997142029361485918487886814322240 = ((120318979668363629324964609051113863198785997 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_22321734180833).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220562984078060416488507466656249330775640641 - 1) / 22321734180833 = 9881086401765826937906691478080 from by norm_num]
      have h2 : (13 : ZMod 220562984078060416488507466656249330775640641) ^ 9881086401765826937906691478080 = ((191248126067429451104596516674317169097777122 : ℕ) : ZMod 220562984078060416488507466656249330775640641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_109978849 : Nat.Prime 109978849 := by
  refine lucas_primality 109978849 (11 : ZMod 109978849) ?_ (fun q hq hd => ?_)
  · rw [show 109978849 - 1 = 109978848 from by norm_num]
    reduce_mod_char
  · have e : 109978849 - 1 = [2 ^ 5, 3 ^ 2, 7 ^ 1, 17 ^ 1, 3209 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109978849 - 1) / 2 = 54989424 from by norm_num]
      have h2 : (11 : ZMod 109978849) ^ 54989424 = ((109978848 : ℕ) : ZMod 109978849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109978849 - 1) / 3 = 36659616 from by norm_num]
      have h2 : (11 : ZMod 109978849) ^ 36659616 = ((30268734 : ℕ) : ZMod 109978849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109978849 - 1) / 7 = 15711264 from by norm_num]
      have h2 : (11 : ZMod 109978849) ^ 15711264 = ((100836514 : ℕ) : ZMod 109978849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109978849 - 1) / 17 = 6469344 from by norm_num]
      have h2 : (11 : ZMod 109978849) ^ 6469344 = ((85899216 : ℕ) : ZMod 109978849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109978849 - 1) / 3209 = 34272 from by norm_num]
      have h2 : (11 : ZMod 109978849) ^ 34272 = ((93706247 : ℕ) : ZMod 109978849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_105579695041 : Nat.Prime 105579695041 := by
  refine lucas_primality 105579695041 (11 : ZMod 105579695041) ?_ (fun q hq hd => ?_)
  · rw [show 105579695041 - 1 = 105579695040 from by norm_num]
    reduce_mod_char
  · have e : 105579695041 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 109978849 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105579695041 - 1) / 2 = 52789847520 from by norm_num]
      have h2 : (11 : ZMod 105579695041) ^ 52789847520 = ((105579695040 : ℕ) : ZMod 105579695041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105579695041 - 1) / 3 = 35193231680 from by norm_num]
      have h2 : (11 : ZMod 105579695041) ^ 35193231680 = ((78506786428 : ℕ) : ZMod 105579695041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105579695041 - 1) / 5 = 21115939008 from by norm_num]
      have h2 : (11 : ZMod 105579695041) ^ 21115939008 = ((30624376700 : ℕ) : ZMod 105579695041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_109978849).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105579695041 - 1) / 109978849 = 960 from by norm_num]
      have h2 : (11 : ZMod 105579695041) ^ 960 = ((71261214477 : ℕ) : ZMod 105579695041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116330952583 : Nat.Prime 116330952583 := by
  refine lucas_primality 116330952583 (3 : ZMod 116330952583) ?_ (fun q hq hd => ?_)
  · rw [show 116330952583 - 1 = 116330952582 from by norm_num]
    reduce_mod_char
  · have e : 116330952583 - 1 = [2 ^ 1, 3 ^ 2, 13 ^ 1, 29 ^ 1, 563 ^ 1, 30449 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 2 = 58165476291 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 58165476291 = ((116330952582 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 3 = 38776984194 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 38776984194 = ((108007297864 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 13 = 8948534814 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 8948534814 = ((107685110299 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 29 = 4011412158 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 4011412158 = ((9579341244 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 563 = 206626914 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 206626914 = ((85235630882 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116330952583 - 1) / 30449 = 3820518 from by norm_num]
      have h2 : (3 : ZMod 116330952583) ^ 3820518 = ((9754788890 : ℕ) : ZMod 116330952583) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2736104004752161 : Nat.Prime 2736104004752161 := by
  refine lucas_primality 2736104004752161 (29 : ZMod 2736104004752161) ?_ (fun q hq hd => ?_)
  · rw [show 2736104004752161 - 1 = 2736104004752160 from by norm_num]
    reduce_mod_char
  · have e : 2736104004752161 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 2, 116330952583 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2736104004752161 - 1) / 2 = 1368052002376080 from by norm_num]
      have h2 : (29 : ZMod 2736104004752161) ^ 1368052002376080 = ((2736104004752160 : ℕ) : ZMod 2736104004752161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2736104004752161 - 1) / 3 = 912034668250720 from by norm_num]
      have h2 : (29 : ZMod 2736104004752161) ^ 912034668250720 = ((1643418542527081 : ℕ) : ZMod 2736104004752161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2736104004752161 - 1) / 5 = 547220800950432 from by norm_num]
      have h2 : (29 : ZMod 2736104004752161) ^ 547220800950432 = ((399877464769381 : ℕ) : ZMod 2736104004752161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2736104004752161 - 1) / 7 = 390872000678880 from by norm_num]
      have h2 : (29 : ZMod 2736104004752161) ^ 390872000678880 = ((1793596765229055 : ℕ) : ZMod 2736104004752161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_116330952583).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2736104004752161 - 1) / 116330952583 = 23520 from by norm_num]
      have h2 : (29 : ZMod 2736104004752161) ^ 23520 = ((801803736939287 : ℕ) : ZMod 2736104004752161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_69979891 : Nat.Prime 69979891 := by
  refine lucas_primality 69979891 (3 : ZMod 69979891) ?_ (fun q hq hd => ?_)
  · rw [show 69979891 - 1 = 69979890 from by norm_num]
    reduce_mod_char
  · have e : 69979891 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 2332663 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69979891 - 1) / 2 = 34989945 from by norm_num]
      have h2 : (3 : ZMod 69979891) ^ 34989945 = ((69979890 : ℕ) : ZMod 69979891) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69979891 - 1) / 3 = 23326630 from by norm_num]
      have h2 : (3 : ZMod 69979891) ^ 23326630 = ((33601081 : ℕ) : ZMod 69979891) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69979891 - 1) / 5 = 13995978 from by norm_num]
      have h2 : (3 : ZMod 69979891) ^ 13995978 = ((43885332 : ℕ) : ZMod 69979891) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69979891 - 1) / 2332663 = 30 from by norm_num]
      have h2 : (3 : ZMod 69979891) ^ 30 = ((5728672 : ℕ) : ZMod 69979891) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2099396731 : Nat.Prime 2099396731 := by
  refine lucas_primality 2099396731 (2 : ZMod 2099396731) ?_ (fun q hq hd => ?_)
  · rw [show 2099396731 - 1 = 2099396730 from by norm_num]
    reduce_mod_char
  · have e : 2099396731 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 69979891 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099396731 - 1) / 2 = 1049698365 from by norm_num]
      have h2 : (2 : ZMod 2099396731) ^ 1049698365 = ((2099396730 : ℕ) : ZMod 2099396731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099396731 - 1) / 3 = 699798910 from by norm_num]
      have h2 : (2 : ZMod 2099396731) ^ 699798910 = ((545887940 : ℕ) : ZMod 2099396731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099396731 - 1) / 5 = 419879346 from by norm_num]
      have h2 : (2 : ZMod 2099396731) ^ 419879346 = ((1699676843 : ℕ) : ZMod 2099396731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_69979891).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099396731 - 1) / 69979891 = 30 from by norm_num]
      have h2 : (2 : ZMod 2099396731) ^ 30 = ((1073741824 : ℕ) : ZMod 2099396731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7457057188513 : Nat.Prime 7457057188513 := by
  refine lucas_primality 7457057188513 (17 : ZMod 7457057188513) ?_ (fun q hq hd => ?_)
  · rw [show 7457057188513 - 1 = 7457057188512 from by norm_num]
    reduce_mod_char
  · have e : 7457057188513 - 1 = [2 ^ 5, 3 ^ 1, 37 ^ 1, 2099396731 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7457057188513 - 1) / 2 = 3728528594256 from by norm_num]
      have h2 : (17 : ZMod 7457057188513) ^ 3728528594256 = ((7457057188512 : ℕ) : ZMod 7457057188513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7457057188513 - 1) / 3 = 2485685729504 from by norm_num]
      have h2 : (17 : ZMod 7457057188513) ^ 2485685729504 = ((123345058329 : ℕ) : ZMod 7457057188513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7457057188513 - 1) / 37 = 201542086176 from by norm_num]
      have h2 : (17 : ZMod 7457057188513) ^ 201542086176 = ((2234704042074 : ℕ) : ZMod 7457057188513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2099396731).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7457057188513 - 1) / 2099396731 = 3552 from by norm_num]
      have h2 : (17 : ZMod 7457057188513) ^ 3552 = ((2125063215899 : ℕ) : ZMod 7457057188513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_803214949635937 : Nat.Prime 803214949635937 := by
  refine lucas_primality 803214949635937 (7 : ZMod 803214949635937) ?_ (fun q hq hd => ?_)
  · rw [show 803214949635937 - 1 = 803214949635936 from by norm_num]
    reduce_mod_char
  · have e : 803214949635937 - 1 = [2 ^ 5, 3 ^ 3, 47 ^ 1, 653 ^ 1, 2297 ^ 1, 13187 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 2 = 401607474817968 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 401607474817968 = ((803214949635936 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 3 = 267738316545312 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 267738316545312 = ((204997670210782 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 47 = 17089679779488 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 17089679779488 = ((2052012441871 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 653 = 1230038207712 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 1230038207712 = ((252527736570418 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 2297 = 349679995488 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 349679995488 = ((104910326676928 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (803214949635937 - 1) / 13187 = 60909604128 from by norm_num]
      have h2 : (7 : ZMod 803214949635937) ^ 60909604128 = ((200595010150998 : ℕ) : ZMod 803214949635937) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2494456365329 : Nat.Prime 2494456365329 := by
  refine lucas_primality 2494456365329 (3 : ZMod 2494456365329) ?_ (fun q hq hd => ?_)
  · rw [show 2494456365329 - 1 = 2494456365328 from by norm_num]
    reduce_mod_char
  · have e : 2494456365329 - 1 = [2 ^ 4, 157 ^ 1, 839 ^ 1, 1183571 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2494456365329 - 1) / 2 = 1247228182664 from by norm_num]
      have h2 : (3 : ZMod 2494456365329) ^ 1247228182664 = ((2494456365328 : ℕ) : ZMod 2494456365329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2494456365329 - 1) / 157 = 15888257104 from by norm_num]
      have h2 : (3 : ZMod 2494456365329) ^ 15888257104 = ((1599699646172 : ℕ) : ZMod 2494456365329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2494456365329 - 1) / 839 = 2973130352 from by norm_num]
      have h2 : (3 : ZMod 2494456365329) ^ 2973130352 = ((1095274899587 : ℕ) : ZMod 2494456365329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2494456365329 - 1) / 1183571 = 2107568 from by norm_num]
      have h2 : (3 : ZMod 2494456365329) ^ 2107568 = ((2219558951841 : ℕ) : ZMod 2494456365329) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49530851957501 : Nat.Prime 49530851957501 := by
  refine lucas_primality 49530851957501 (2 : ZMod 49530851957501) ?_ (fun q hq hd => ?_)
  · rw [show 49530851957501 - 1 = 49530851957500 from by norm_num]
    reduce_mod_char
  · have e : 49530851957501 - 1 = [2 ^ 2, 5 ^ 4, 23 ^ 1, 83 ^ 1, 2729 ^ 1, 3803 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 2 = 24765425978750 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 24765425978750 = ((49530851957500 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 5 = 9906170391500 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 9906170391500 = ((38759740729312 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 23 = 2153515302500 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 2153515302500 = ((39536765090377 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 83 = 596757252500 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 596757252500 = ((5520232687509 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 2729 = 18149817500 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 18149817500 = ((43226483514813 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49530851957501 - 1) / 3803 = 13024152500 from by norm_num]
      have h2 : (2 : ZMod 49530851957501) ^ 13024152500 = ((32812115591343 : ℕ) : ZMod 49530851957501) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_65246471 : Nat.Prime 65246471 := by
  refine lucas_primality 65246471 (11 : ZMod 65246471) ?_ (fun q hq hd => ?_)
  · rw [show 65246471 - 1 = 65246470 from by norm_num]
    reduce_mod_char
  · have e : 65246471 - 1 = [2 ^ 1, 5 ^ 1, 6524647 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65246471 - 1) / 2 = 32623235 from by norm_num]
      have h2 : (11 : ZMod 65246471) ^ 32623235 = ((65246470 : ℕ) : ZMod 65246471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65246471 - 1) / 5 = 13049294 from by norm_num]
      have h2 : (11 : ZMod 65246471) ^ 13049294 = ((9751824 : ℕ) : ZMod 65246471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65246471 - 1) / 6524647 = 10 from by norm_num]
      have h2 : (11 : ZMod 65246471) ^ 10 = ((34575614 : ℕ) : ZMod 65246471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_310244476401636693981217 : Nat.Prime 310244476401636693981217 := by
  refine lucas_primality 310244476401636693981217 (7 : ZMod 310244476401636693981217) ?_ (fun q hq hd => ?_)
  · rw [show 310244476401636693981217 - 1 = 310244476401636693981216 from by norm_num]
    reduce_mod_char
  · have e : 310244476401636693981217 - 1 = [2 ^ 5, 3 ^ 1, 65246471 ^ 1, 49530851957501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (310244476401636693981217 - 1) / 2 = 155122238200818346990608 from by norm_num]
      have h2 : (7 : ZMod 310244476401636693981217) ^ 155122238200818346990608 = ((310244476401636693981216 : ℕ) : ZMod 310244476401636693981217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (310244476401636693981217 - 1) / 3 = 103414825467212231327072 from by norm_num]
      have h2 : (7 : ZMod 310244476401636693981217) ^ 103414825467212231327072 = ((144335526734098076165219 : ℕ) : ZMod 310244476401636693981217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_65246471).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (310244476401636693981217 - 1) / 65246471 = 4754961787920096 from by norm_num]
      have h2 : (7 : ZMod 310244476401636693981217) ^ 4754961787920096 = ((79442800794117366712275 : ℕ) : ZMod 310244476401636693981217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_49530851957501).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (310244476401636693981217 - 1) / 49530851957501 = 6263661216 from by norm_num]
      have h2 : (7 : ZMod 310244476401636693981217) ^ 6263661216 = ((224728247605520910336339 : ℕ) : ZMod 310244476401636693981217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_264882169 : Nat.Prime 264882169 := by
  refine lucas_primality 264882169 (11 : ZMod 264882169) ?_ (fun q hq hd => ?_)
  · rw [show 264882169 - 1 = 264882168 from by norm_num]
    reduce_mod_char
  · have e : 264882169 - 1 = [2 ^ 3, 3 ^ 2, 17 ^ 1, 23 ^ 1, 97 ^ 2].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (264882169 - 1) / 2 = 132441084 from by norm_num]
      have h2 : (11 : ZMod 264882169) ^ 132441084 = ((264882168 : ℕ) : ZMod 264882169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (264882169 - 1) / 3 = 88294056 from by norm_num]
      have h2 : (11 : ZMod 264882169) ^ 88294056 = ((159185210 : ℕ) : ZMod 264882169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (264882169 - 1) / 17 = 15581304 from by norm_num]
      have h2 : (11 : ZMod 264882169) ^ 15581304 = ((133472232 : ℕ) : ZMod 264882169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (264882169 - 1) / 23 = 11516616 from by norm_num]
      have h2 : (11 : ZMod 264882169) ^ 11516616 = ((187446745 : ℕ) : ZMod 264882169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (264882169 - 1) / 97 = 2730744 from by norm_num]
      have h2 : (11 : ZMod 264882169) ^ 2730744 = ((212089931 : ℕ) : ZMod 264882169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_95586439034017 : Nat.Prime 95586439034017 := by
  refine lucas_primality 95586439034017 (5 : ZMod 95586439034017) ?_ (fun q hq hd => ?_)
  · rw [show 95586439034017 - 1 = 95586439034016 from by norm_num]
    reduce_mod_char
  · have e : 95586439034017 - 1 = [2 ^ 5, 3 ^ 2, 7 ^ 1, 179 ^ 1, 264882169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95586439034017 - 1) / 2 = 47793219517008 from by norm_num]
      have h2 : (5 : ZMod 95586439034017) ^ 47793219517008 = ((95586439034016 : ℕ) : ZMod 95586439034017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95586439034017 - 1) / 3 = 31862146344672 from by norm_num]
      have h2 : (5 : ZMod 95586439034017) ^ 31862146344672 = ((74905597288413 : ℕ) : ZMod 95586439034017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95586439034017 - 1) / 7 = 13655205576288 from by norm_num]
      have h2 : (5 : ZMod 95586439034017) ^ 13655205576288 = ((21911371284921 : ℕ) : ZMod 95586439034017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95586439034017 - 1) / 179 = 534002452704 from by norm_num]
      have h2 : (5 : ZMod 95586439034017) ^ 534002452704 = ((82767261409610 : ℕ) : ZMod 95586439034017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_264882169).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95586439034017 - 1) / 264882169 = 360864 from by norm_num]
      have h2 : (5 : ZMod 95586439034017) ^ 360864 = ((16079662542383 : ℕ) : ZMod 95586439034017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_452505857 : Nat.Prime 452505857 := by
  refine lucas_primality 452505857 (3 : ZMod 452505857) ?_ (fun q hq hd => ?_)
  · rw [show 452505857 - 1 = 452505856 from by norm_num]
    reduce_mod_char
  · have e : 452505857 - 1 = [2 ^ 8, 11 ^ 1, 37 ^ 1, 43 ^ 1, 101 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (452505857 - 1) / 2 = 226252928 from by norm_num]
      have h2 : (3 : ZMod 452505857) ^ 226252928 = ((452505856 : ℕ) : ZMod 452505857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (452505857 - 1) / 11 = 41136896 from by norm_num]
      have h2 : (3 : ZMod 452505857) ^ 41136896 = ((400559091 : ℕ) : ZMod 452505857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (452505857 - 1) / 37 = 12229888 from by norm_num]
      have h2 : (3 : ZMod 452505857) ^ 12229888 = ((352307767 : ℕ) : ZMod 452505857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (452505857 - 1) / 43 = 10523392 from by norm_num]
      have h2 : (3 : ZMod 452505857) ^ 10523392 = ((366858987 : ℕ) : ZMod 452505857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (452505857 - 1) / 101 = 4480256 from by norm_num]
      have h2 : (3 : ZMod 452505857) ^ 4480256 = ((185606316 : ℕ) : ZMod 452505857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70148737 : Nat.Prime 70148737 := by
  refine lucas_primality 70148737 (5 : ZMod 70148737) ?_ (fun q hq hd => ?_)
  · rw [show 70148737 - 1 = 70148736 from by norm_num]
    reduce_mod_char
  · have e : 70148737 - 1 = [2 ^ 7, 3 ^ 2, 7 ^ 1, 8699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70148737 - 1) / 2 = 35074368 from by norm_num]
      have h2 : (5 : ZMod 70148737) ^ 35074368 = ((70148736 : ℕ) : ZMod 70148737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70148737 - 1) / 3 = 23382912 from by norm_num]
      have h2 : (5 : ZMod 70148737) ^ 23382912 = ((23607667 : ℕ) : ZMod 70148737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70148737 - 1) / 7 = 10021248 from by norm_num]
      have h2 : (5 : ZMod 70148737) ^ 10021248 = ((28979751 : ℕ) : ZMod 70148737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70148737 - 1) / 8699 = 8064 from by norm_num]
      have h2 : (5 : ZMod 70148737) ^ 8064 = ((43584644 : ℕ) : ZMod 70148737) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_136620642578120829137 : Nat.Prime 136620642578120829137 := by
  refine lucas_primality 136620642578120829137 (3 : ZMod 136620642578120829137) ?_ (fun q hq hd => ?_)
  · rw [show 136620642578120829137 - 1 = 136620642578120829136 from by norm_num]
    reduce_mod_char
  · have e : 136620642578120829137 - 1 = [2 ^ 4, 269 ^ 1, 70148737 ^ 1, 452505857 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136620642578120829137 - 1) / 2 = 68310321289060414568 from by norm_num]
      have h2 : (3 : ZMod 136620642578120829137) ^ 68310321289060414568 = ((136620642578120829136 : ℕ) : ZMod 136620642578120829137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136620642578120829137 - 1) / 269 = 507883429658441744 from by norm_num]
      have h2 : (3 : ZMod 136620642578120829137) ^ 507883429658441744 = ((89944545296615267688 : ℕ) : ZMod 136620642578120829137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_70148737).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136620642578120829137 - 1) / 70148737 = 1947585208528 from by norm_num]
      have h2 : (3 : ZMod 136620642578120829137) ^ 1947585208528 = ((40702012058568930345 : ℕ) : ZMod 136620642578120829137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_452505857).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (136620642578120829137 - 1) / 452505857 = 301920164048 from by norm_num]
      have h2 : (3 : ZMod 136620642578120829137) ^ 301920164048 = ((117755990310211459159 : ℕ) : ZMod 136620642578120829137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10983552195457570260986954785955861855365952457121 : Nat.Prime 10983552195457570260986954785955861855365952457121 := by
  refine lucas_primality 10983552195457570260986954785955861855365952457121 (7 : ZMod 10983552195457570260986954785955861855365952457121) ?_ (fun q hq hd => ?_)
  · rw [show 10983552195457570260986954785955861855365952457121 - 1 = 10983552195457570260986954785955861855365952457120 from by norm_num]
    reduce_mod_char
  · have e : 10983552195457570260986954785955861855365952457121 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 101 ^ 1, 241 ^ 1, 281 ^ 1, 607 ^ 1, 1009 ^ 1, 2081 ^ 1, 7681 ^ 1, 147137 ^ 1, 136620642578120829137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 2 = 5491776097728785130493477392977930927682976228560 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 5491776097728785130493477392977930927682976228560 = ((10983552195457570260986954785955861855365952457120 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 3 = 3661184065152523420328984928651953951788650819040 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 3661184065152523420328984928651953951788650819040 = ((4332700620197685418165995632469379488310938414055 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 5 = 2196710439091514052197390957191172371073190491424 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 2196710439091514052197390957191172371073190491424 = ((7362611935336512355961421408283169927836912185472 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 17 = 646091305615151191822762046232697756197997203360 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 646091305615151191822762046232697756197997203360 = ((9353342834960197633782708704433934646150945535097 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 101 = 108748041539183863970167869167879820350157945120 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 108748041539183863970167869167879820350157945120 = ((2495009056480291638841075111567191003874124049555 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 241 = 45574905375342615190817239775750464130149180320 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 45574905375342615190817239775750464130149180320 = ((1133026109248361981485656730926245430256114262348 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 281 = 39087374361058968900309447636853600908775631520 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 39087374361058968900309447636853600908775631520 = ((3047416711253966501250180200924668511841399748192 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 607 = 18094814160556128930785757472744418213123480160 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 18094814160556128930785757472744418213123480160 = ((2777862029835042114632264547867992662572362630628 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 1009 = 10885581957837036928629291165466661898281419680 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 10885581957837036928629291165466661898281419680 = ((7038389267215458751901404504594760222507265678542 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 2081 = 5278016432223724296485802395942269031891375520 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 5278016432223724296485802395942269031891375520 = ((9132841392503158690119749553828503863790612613420 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 7681 = 1429963832242881169247097355286533245067823520 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 1429963832242881169247097355286533245067823520 = ((9681768221051289680778187673255394264170979815521 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 147137 = 74648471801501799418140608996757184497209760 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 74648471801501799418140608996757184497209760 = ((1137597004531311650884837631503513888926708606960 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_136620642578120829137).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10983552195457570260986954785955861855365952457121 - 1) / 136620642578120829137 = 80394528880780830808505849760 from by norm_num]
      have h2 : (7 : ZMod 10983552195457570260986954785955861855365952457121) ^ 80394528880780830808505849760 = ((318919411784893643100257034279007238046740036811 : ℕ) : ZMod 10983552195457570260986954785955861855365952457121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1105799549 : Nat.Prime 1105799549 := by
  refine lucas_primality 1105799549 (2 : ZMod 1105799549) ?_ (fun q hq hd => ?_)
  · rw [show 1105799549 - 1 = 1105799548 from by norm_num]
    reduce_mod_char
  · have e : 1105799549 - 1 = [2 ^ 2, 7 ^ 1, 3923 ^ 1, 10067 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1105799549 - 1) / 2 = 552899774 from by norm_num]
      have h2 : (2 : ZMod 1105799549) ^ 552899774 = ((1105799548 : ℕ) : ZMod 1105799549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1105799549 - 1) / 7 = 157971364 from by norm_num]
      have h2 : (2 : ZMod 1105799549) ^ 157971364 = ((1027632162 : ℕ) : ZMod 1105799549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1105799549 - 1) / 3923 = 281876 from by norm_num]
      have h2 : (2 : ZMod 1105799549) ^ 281876 = ((340307648 : ℕ) : ZMod 1105799549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1105799549 - 1) / 10067 = 109844 from by norm_num]
      have h2 : (2 : ZMod 1105799549) ^ 109844 = ((276024859 : ℕ) : ZMod 1105799549) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_35715113833603 : Nat.Prime 35715113833603 := by
  refine lucas_primality 35715113833603 (7 : ZMod 35715113833603) ?_ (fun q hq hd => ?_)
  · rw [show 35715113833603 - 1 = 35715113833602 from by norm_num]
    reduce_mod_char
  · have e : 35715113833603 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 769 ^ 1, 1105799549 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35715113833603 - 1) / 2 = 17857556916801 from by norm_num]
      have h2 : (7 : ZMod 35715113833603) ^ 17857556916801 = ((35715113833602 : ℕ) : ZMod 35715113833603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35715113833603 - 1) / 3 = 11905037944534 from by norm_num]
      have h2 : (7 : ZMod 35715113833603) ^ 11905037944534 = ((7713087685265 : ℕ) : ZMod 35715113833603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35715113833603 - 1) / 7 = 5102159119086 from by norm_num]
      have h2 : (7 : ZMod 35715113833603) ^ 5102159119086 = ((7523939192322 : ℕ) : ZMod 35715113833603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35715113833603 - 1) / 769 = 46443581058 from by norm_num]
      have h2 : (7 : ZMod 35715113833603) ^ 46443581058 = ((27494704584340 : ℕ) : ZMod 35715113833603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1105799549).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35715113833603 - 1) / 1105799549 = 32298 from by norm_num]
      have h2 : (7 : ZMod 35715113833603) ^ 32298 = ((13480869511276 : ℕ) : ZMod 35715113833603) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_337734688130619396257 : Nat.Prime 337734688130619396257 := by
  refine lucas_primality 337734688130619396257 (3 : ZMod 337734688130619396257) ?_ (fun q hq hd => ?_)
  · rw [show 337734688130619396257 - 1 = 337734688130619396256 from by norm_num]
    reduce_mod_char
  · have e : 337734688130619396257 - 1 = [2 ^ 5, 17 ^ 1, 17383 ^ 1, 35715113833603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (337734688130619396257 - 1) / 2 = 168867344065309698128 from by norm_num]
      have h2 : (3 : ZMod 337734688130619396257) ^ 168867344065309698128 = ((337734688130619396256 : ℕ) : ZMod 337734688130619396257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (337734688130619396257 - 1) / 17 = 19866746360624670368 from by norm_num]
      have h2 : (3 : ZMod 337734688130619396257) ^ 19866746360624670368 = ((233377624102329477061 : ℕ) : ZMod 337734688130619396257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (337734688130619396257 - 1) / 17383 = 19429021925480032 from by norm_num]
      have h2 : (3 : ZMod 337734688130619396257) ^ 19429021925480032 = ((258605719344501405635 : ℕ) : ZMod 337734688130619396257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_35715113833603).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (337734688130619396257 - 1) / 35715113833603 = 9456352 from by norm_num]
      have h2 : (3 : ZMod 337734688130619396257) ^ 9456352 = ((220625821111203272196 : ℕ) : ZMod 337734688130619396257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_72203917 : Nat.Prime 72203917 := by
  refine lucas_primality 72203917 (5 : ZMod 72203917) ?_ (fun q hq hd => ?_)
  · rw [show 72203917 - 1 = 72203916 from by norm_num]
    reduce_mod_char
  · have e : 72203917 - 1 = [2 ^ 2, 3 ^ 1, 6016993 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (72203917 - 1) / 2 = 36101958 from by norm_num]
      have h2 : (5 : ZMod 72203917) ^ 36101958 = ((72203916 : ℕ) : ZMod 72203917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (72203917 - 1) / 3 = 24067972 from by norm_num]
      have h2 : (5 : ZMod 72203917) ^ 24067972 = ((5750555 : ℕ) : ZMod 72203917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (72203917 - 1) / 6016993 = 12 from by norm_num]
      have h2 : (5 : ZMod 72203917) ^ 12 = ((27528874 : ℕ) : ZMod 72203917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_311920921441 : Nat.Prime 311920921441 := by
  refine lucas_primality 311920921441 (7 : ZMod 311920921441) ?_ (fun q hq hd => ?_)
  · rw [show 311920921441 - 1 = 311920921440 from by norm_num]
    reduce_mod_char
  · have e : 311920921441 - 1 = [2 ^ 5, 3 ^ 3, 5 ^ 1, 72203917 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (311920921441 - 1) / 2 = 155960460720 from by norm_num]
      have h2 : (7 : ZMod 311920921441) ^ 155960460720 = ((311920921440 : ℕ) : ZMod 311920921441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (311920921441 - 1) / 3 = 103973640480 from by norm_num]
      have h2 : (7 : ZMod 311920921441) ^ 103973640480 = ((435640170 : ℕ) : ZMod 311920921441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (311920921441 - 1) / 5 = 62384184288 from by norm_num]
      have h2 : (7 : ZMod 311920921441) ^ 62384184288 = ((202307308752 : ℕ) : ZMod 311920921441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_72203917).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (311920921441 - 1) / 72203917 = 4320 from by norm_num]
      have h2 : (7 : ZMod 311920921441) ^ 4320 = ((12089403981 : ℕ) : ZMod 311920921441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11996958517 : Nat.Prime 11996958517 := by
  refine lucas_primality 11996958517 (6 : ZMod 11996958517) ?_ (fun q hq hd => ?_)
  · rw [show 11996958517 - 1 = 11996958516 from by norm_num]
    reduce_mod_char
  · have e : 11996958517 - 1 = [2 ^ 2, 3 ^ 1, 23 ^ 1, 131 ^ 1, 449 ^ 1, 739 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 2 = 5998479258 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 5998479258 = ((11996958516 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 3 = 3998986172 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 3998986172 = ((2200191114 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 23 = 521606892 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 521606892 = ((1483519190 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 131 = 91579836 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 91579836 = ((4209218434 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 449 = 26719284 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 26719284 = ((6809991233 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11996958517 - 1) / 739 = 16234044 from by norm_num]
      have h2 : (6 : ZMod 11996958517) ^ 16234044 = ((3907297260 : ℕ) : ZMod 11996958517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5998479259 : Nat.Prime 5998479259 := by
  refine lucas_primality 5998479259 (2 : ZMod 5998479259) ?_ (fun q hq hd => ?_)
  · rw [show 5998479259 - 1 = 5998479258 from by norm_num]
    reduce_mod_char
  · have e : 5998479259 - 1 = [2 ^ 1, 3 ^ 1, 23 ^ 1, 131 ^ 1, 449 ^ 1, 739 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 2 = 2999239629 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 2999239629 = ((5998479258 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 3 = 1999493086 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 1999493086 = ((5747597651 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 23 = 260803446 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 260803446 = ((3036099748 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 131 = 45789918 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 45789918 = ((1615900745 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 449 = 13359642 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 13359642 = ((5561304595 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5998479259 - 1) / 739 = 8117022 from by norm_num]
      have h2 : (2 : ZMod 5998479259) ^ 8117022 = ((1577707576 : ℕ) : ZMod 5998479259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_107044633 : Nat.Prime 107044633 := by
  refine lucas_primality 107044633 (7 : ZMod 107044633) ?_ (fun q hq hd => ?_)
  · rw [show 107044633 - 1 = 107044632 from by norm_num]
    reduce_mod_char
  · have e : 107044633 - 1 = [2 ^ 3, 3 ^ 3, 19 ^ 1, 26083 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107044633 - 1) / 2 = 53522316 from by norm_num]
      have h2 : (7 : ZMod 107044633) ^ 53522316 = ((107044632 : ℕ) : ZMod 107044633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107044633 - 1) / 3 = 35681544 from by norm_num]
      have h2 : (7 : ZMod 107044633) ^ 35681544 = ((59948985 : ℕ) : ZMod 107044633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107044633 - 1) / 19 = 5633928 from by norm_num]
      have h2 : (7 : ZMod 107044633) ^ 5633928 = ((39006652 : ℕ) : ZMod 107044633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107044633 - 1) / 26083 = 4104 from by norm_num]
      have h2 : (7 : ZMod 107044633) ^ 4104 = ((96186452 : ℕ) : ZMod 107044633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_207817026647174251535873 : Nat.Prime 207817026647174251535873 := by
  refine lucas_primality 207817026647174251535873 (3 : ZMod 207817026647174251535873) ?_ (fun q hq hd => ?_)
  · rw [show 207817026647174251535873 - 1 = 207817026647174251535872 from by norm_num]
    reduce_mod_char
  · have e : 207817026647174251535873 - 1 = [2 ^ 9, 7 ^ 1, 19 ^ 1, 31277 ^ 1, 911527 ^ 1, 107044633 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 2 = 103908513323587125767936 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 103908513323587125767936 = ((207817026647174251535872 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 7 = 29688146663882035933696 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 29688146663882035933696 = ((2696839917293813724689 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 19 = 10937738244588118501888 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 10937738244588118501888 = ((70267559087109771796116 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 31277 = 6644404087577908736 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 6644404087577908736 = ((186817608487121478224484 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 911527 = 227987790429876736 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 227987790429876736 = ((133416459964613016134149 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_107044633).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207817026647174251535873 - 1) / 107044633 = 1941405382249984 from by norm_num]
      have h2 : (3 : ZMod 207817026647174251535873) ^ 1941405382249984 = ((44623048866465640243909 : ℕ) : ZMod 207817026647174251535873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14246089457 : Nat.Prime 14246089457 := by
  refine lucas_primality 14246089457 (3 : ZMod 14246089457) ?_ (fun q hq hd => ?_)
  · rw [show 14246089457 - 1 = 14246089456 from by norm_num]
    reduce_mod_char
  · have e : 14246089457 - 1 = [2 ^ 4, 29 ^ 1, 83 ^ 1, 369913 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14246089457 - 1) / 2 = 7123044728 from by norm_num]
      have h2 : (3 : ZMod 14246089457) ^ 7123044728 = ((14246089456 : ℕ) : ZMod 14246089457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14246089457 - 1) / 29 = 491244464 from by norm_num]
      have h2 : (3 : ZMod 14246089457) ^ 491244464 = ((5410482029 : ℕ) : ZMod 14246089457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14246089457 - 1) / 83 = 171639632 from by norm_num]
      have h2 : (3 : ZMod 14246089457) ^ 171639632 = ((3290240284 : ℕ) : ZMod 14246089457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14246089457 - 1) / 369913 = 38512 from by norm_num]
      have h2 : (3 : ZMod 14246089457) ^ 38512 = ((4357370907 : ℕ) : ZMod 14246089457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11739987604453404097 : Nat.Prime 11739987604453404097 := by
  refine lucas_primality 11739987604453404097 (10 : ZMod 11739987604453404097) ?_ (fun q hq hd => ?_)
  · rw [show 11739987604453404097 - 1 = 11739987604453404096 from by norm_num]
    reduce_mod_char
  · have e : 11739987604453404097 - 1 = [2 ^ 6, 3 ^ 6, 17 ^ 1, 1039 ^ 1, 14246089457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11739987604453404097 - 1) / 2 = 5869993802226702048 from by norm_num]
      have h2 : (10 : ZMod 11739987604453404097) ^ 5869993802226702048 = ((11739987604453404096 : ℕ) : ZMod 11739987604453404097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11739987604453404097 - 1) / 3 = 3913329201484468032 from by norm_num]
      have h2 : (10 : ZMod 11739987604453404097) ^ 3913329201484468032 = ((843948282271375996 : ℕ) : ZMod 11739987604453404097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11739987604453404097 - 1) / 17 = 690587506144317888 from by norm_num]
      have h2 : (10 : ZMod 11739987604453404097) ^ 690587506144317888 = ((9116244546714262023 : ℕ) : ZMod 11739987604453404097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11739987604453404097 - 1) / 1039 = 11299314344998464 from by norm_num]
      have h2 : (10 : ZMod 11739987604453404097) ^ 11299314344998464 = ((8344422304465781038 : ℕ) : ZMod 11739987604453404097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14246089457).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11739987604453404097 - 1) / 14246089457 = 824084928 from by norm_num]
      have h2 : (10 : ZMod 11739987604453404097) ^ 824084928 = ((3260131606192733392 : ℕ) : ZMod 11739987604453404097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_110951060221 : Nat.Prime 110951060221 := by
  refine lucas_primality 110951060221 (22 : ZMod 110951060221) ?_ (fun q hq hd => ?_)
  · rw [show 110951060221 - 1 = 110951060220 from by norm_num]
    reduce_mod_char
  · have e : 110951060221 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 1, 13 ^ 1, 23 ^ 1, 41 ^ 1, 653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 2 = 55475530110 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 55475530110 = ((110951060220 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 3 = 36983686740 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 36983686740 = ((54282818173 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 5 = 22190212044 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 22190212044 = ((567110573 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 7 = 15850151460 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 15850151460 = ((23364091685 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 11 = 10086460020 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 10086460020 = ((105109537117 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 13 = 8534696940 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 8534696940 = ((53451828468 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 23 = 4823959140 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 4823959140 = ((68207260482 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 41 = 2706123420 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 2706123420 = ((47274115152 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (110951060221 - 1) / 653 = 169909740 from by norm_num]
      have h2 : (22 : ZMod 110951060221) ^ 169909740 = ((23089842948 : ℕ) : ZMod 110951060221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_55697432230943 : Nat.Prime 55697432230943 := by
  refine lucas_primality 55697432230943 (5 : ZMod 55697432230943) ?_ (fun q hq hd => ?_)
  · rw [show 55697432230943 - 1 = 55697432230942 from by norm_num]
    reduce_mod_char
  · have e : 55697432230943 - 1 = [2 ^ 1, 251 ^ 1, 110951060221 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55697432230943 - 1) / 2 = 27848716115471 from by norm_num]
      have h2 : (5 : ZMod 55697432230943) ^ 27848716115471 = ((55697432230942 : ℕ) : ZMod 55697432230943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55697432230943 - 1) / 251 = 221902120442 from by norm_num]
      have h2 : (5 : ZMod 55697432230943) ^ 221902120442 = ((47102545501395 : ℕ) : ZMod 55697432230943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_110951060221).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55697432230943 - 1) / 110951060221 = 502 from by norm_num]
      have h2 : (5 : ZMod 55697432230943) ^ 502 = ((26304382070743 : ℕ) : ZMod 55697432230943) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9091986456255036663841 : Nat.Prime 9091986456255036663841 := by
  refine lucas_primality 9091986456255036663841 (11 : ZMod 9091986456255036663841) ?_ (fun q hq hd => ?_)
  · rw [show 9091986456255036663841 - 1 = 9091986456255036663840 from by norm_num]
    reduce_mod_char
  · have e : 9091986456255036663841 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 19 ^ 1, 2557 ^ 1, 55697432230943 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 2 = 4545993228127518331920 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 4545993228127518331920 = ((9091986456255036663840 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 3 = 3030662152085012221280 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 3030662152085012221280 = ((5848961048092485194423 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 5 = 1818397291251007332768 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 1818397291251007332768 = ((7141913530498678230915 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 7 = 1298855208036433809120 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 1298855208036433809120 = ((8412946358866089239587 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 19 = 478525602960791403360 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 478525602960791403360 = ((5146984547561499092357 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 2557 = 3555724073623401120 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 3555724073623401120 = ((2492599437791319220279 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_55697432230943).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9091986456255036663841 - 1) / 55697432230943 = 163238880 from by norm_num]
      have h2 : (11 : ZMod 9091986456255036663841) ^ 163238880 = ((6055655703959510028388 : ℕ) : ZMod 9091986456255036663841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2191612183 : Nat.Prime 2191612183 := by
  refine lucas_primality 2191612183 (3 : ZMod 2191612183) ?_ (fun q hq hd => ?_)
  · rw [show 2191612183 - 1 = 2191612182 from by norm_num]
    reduce_mod_char
  · have e : 2191612183 - 1 = [2 ^ 1, 3 ^ 1, 419 ^ 1, 871763 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191612183 - 1) / 2 = 1095806091 from by norm_num]
      have h2 : (3 : ZMod 2191612183) ^ 1095806091 = ((2191612182 : ℕ) : ZMod 2191612183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191612183 - 1) / 3 = 730537394 from by norm_num]
      have h2 : (3 : ZMod 2191612183) ^ 730537394 = ((985912112 : ℕ) : ZMod 2191612183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191612183 - 1) / 419 = 5230578 from by norm_num]
      have h2 : (3 : ZMod 2191612183) ^ 5230578 = ((77354998 : ℕ) : ZMod 2191612183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2191612183 - 1) / 871763 = 2514 from by norm_num]
      have h2 : (3 : ZMod 2191612183) ^ 2514 = ((1417290297 : ℕ) : ZMod 2191612183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1073889969671 : Nat.Prime 1073889969671 := by
  refine lucas_primality 1073889969671 (14 : ZMod 1073889969671) ?_ (fun q hq hd => ?_)
  · rw [show 1073889969671 - 1 = 1073889969670 from by norm_num]
    reduce_mod_char
  · have e : 1073889969671 - 1 = [2 ^ 1, 5 ^ 1, 7 ^ 2, 2191612183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073889969671 - 1) / 2 = 536944984835 from by norm_num]
      have h2 : (14 : ZMod 1073889969671) ^ 536944984835 = ((1073889969670 : ℕ) : ZMod 1073889969671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073889969671 - 1) / 5 = 214777993934 from by norm_num]
      have h2 : (14 : ZMod 1073889969671) ^ 214777993934 = ((689873988785 : ℕ) : ZMod 1073889969671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073889969671 - 1) / 7 = 153412852810 from by norm_num]
      have h2 : (14 : ZMod 1073889969671) ^ 153412852810 = ((1032745370155 : ℕ) : ZMod 1073889969671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2191612183).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073889969671 - 1) / 2191612183 = 490 from by norm_num]
      have h2 : (14 : ZMod 1073889969671) ^ 490 = ((514096542397 : ℕ) : ZMod 1073889969671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_45103378726183 : Nat.Prime 45103378726183 := by
  refine lucas_primality 45103378726183 (3 : ZMod 45103378726183) ?_ (fun q hq hd => ?_)
  · rw [show 45103378726183 - 1 = 45103378726182 from by norm_num]
    reduce_mod_char
  · have e : 45103378726183 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 1073889969671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45103378726183 - 1) / 2 = 22551689363091 from by norm_num]
      have h2 : (3 : ZMod 45103378726183) ^ 22551689363091 = ((45103378726182 : ℕ) : ZMod 45103378726183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45103378726183 - 1) / 3 = 15034459575394 from by norm_num]
      have h2 : (3 : ZMod 45103378726183) ^ 15034459575394 = ((15100263868993 : ℕ) : ZMod 45103378726183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45103378726183 - 1) / 7 = 6443339818026 from by norm_num]
      have h2 : (3 : ZMod 45103378726183) ^ 6443339818026 = ((28478359085422 : ℕ) : ZMod 45103378726183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1073889969671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45103378726183 - 1) / 1073889969671 = 42 from by norm_num]
      have h2 : (3 : ZMod 45103378726183) ^ 42 = ((41580320174712 : ℕ) : ZMod 45103378726183) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_587426404529807393 : Nat.Prime 587426404529807393 := by
  refine lucas_primality 587426404529807393 (3 : ZMod 587426404529807393) ?_ (fun q hq hd => ?_)
  · rw [show 587426404529807393 - 1 = 587426404529807392 from by norm_num]
    reduce_mod_char
  · have e : 587426404529807393 - 1 = [2 ^ 5, 11 ^ 1, 37 ^ 1, 45103378726183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (587426404529807393 - 1) / 2 = 293713202264903696 from by norm_num]
      have h2 : (3 : ZMod 587426404529807393) ^ 293713202264903696 = ((587426404529807392 : ℕ) : ZMod 587426404529807393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (587426404529807393 - 1) / 11 = 53402400411800672 from by norm_num]
      have h2 : (3 : ZMod 587426404529807393) ^ 53402400411800672 = ((34692869675238407 : ℕ) : ZMod 587426404529807393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (587426404529807393 - 1) / 37 = 15876389311616416 from by norm_num]
      have h2 : (3 : ZMod 587426404529807393) ^ 15876389311616416 = ((299544345872181717 : ℕ) : ZMod 587426404529807393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_45103378726183).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (587426404529807393 - 1) / 45103378726183 = 13024 from by norm_num]
      have h2 : (3 : ZMod 587426404529807393) ^ 13024 = ((441012663736202664 : ℕ) : ZMod 587426404529807393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14942674107901 : Nat.Prime 14942674107901 := by
  refine lucas_primality 14942674107901 (6 : ZMod 14942674107901) ?_ (fun q hq hd => ?_)
  · rw [show 14942674107901 - 1 = 14942674107900 from by norm_num]
    reduce_mod_char
  · have e : 14942674107901 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 2, 7 ^ 1, 11 ^ 1, 811 ^ 1, 265873 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 2 = 7471337053950 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 7471337053950 = ((14942674107900 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 3 = 4980891369300 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 4980891369300 = ((1750913208842 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 5 = 2988534821580 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 2988534821580 = ((5678546248801 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 7 = 2134667729700 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 2134667729700 = ((11368401327397 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 11 = 1358424918900 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 1358424918900 = ((1176436279454 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 811 = 18424998900 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 18424998900 = ((13792949713310 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14942674107901 - 1) / 265873 = 56202300 from by norm_num]
      have h2 : (6 : ZMod 14942674107901) ^ 56202300 = ((10055577877852 : ℕ) : ZMod 14942674107901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_179312089294813 : Nat.Prime 179312089294813 := by
  refine lucas_primality 179312089294813 (5 : ZMod 179312089294813) ?_ (fun q hq hd => ?_)
  · rw [show 179312089294813 - 1 = 179312089294812 from by norm_num]
    reduce_mod_char
  · have e : 179312089294813 - 1 = [2 ^ 2, 3 ^ 1, 14942674107901 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179312089294813 - 1) / 2 = 89656044647406 from by norm_num]
      have h2 : (5 : ZMod 179312089294813) ^ 89656044647406 = ((179312089294812 : ℕ) : ZMod 179312089294813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179312089294813 - 1) / 3 = 59770696431604 from by norm_num]
      have h2 : (5 : ZMod 179312089294813) ^ 59770696431604 = ((75966500165914 : ℕ) : ZMod 179312089294813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14942674107901).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179312089294813 - 1) / 14942674107901 = 12 from by norm_num]
      have h2 : (5 : ZMod 179312089294813) ^ 12 = ((244140625 : ℕ) : ZMod 179312089294813) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_97904400754967899 : Nat.Prime 97904400754967899 := by
  refine lucas_primality 97904400754967899 (10 : ZMod 97904400754967899) ?_ (fun q hq hd => ?_)
  · rw [show 97904400754967899 - 1 = 97904400754967898 from by norm_num]
    reduce_mod_char
  · have e : 97904400754967899 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 13 ^ 1, 179312089294813 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97904400754967899 - 1) / 2 = 48952200377483949 from by norm_num]
      have h2 : (10 : ZMod 97904400754967899) ^ 48952200377483949 = ((97904400754967898 : ℕ) : ZMod 97904400754967899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97904400754967899 - 1) / 3 = 32634800251655966 from by norm_num]
      have h2 : (10 : ZMod 97904400754967899) ^ 32634800251655966 = ((6110972299200390 : ℕ) : ZMod 97904400754967899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97904400754967899 - 1) / 7 = 13986342964995414 from by norm_num]
      have h2 : (10 : ZMod 97904400754967899) ^ 13986342964995414 = ((58846986132794176 : ℕ) : ZMod 97904400754967899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97904400754967899 - 1) / 13 = 7531107750382146 from by norm_num]
      have h2 : (10 : ZMod 97904400754967899) ^ 7531107750382146 = ((63994580451619525 : ℕ) : ZMod 97904400754967899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_179312089294813).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97904400754967899 - 1) / 179312089294813 = 546 from by norm_num]
      have h2 : (10 : ZMod 97904400754967899) ^ 546 = ((82001511959366379 : ℕ) : ZMod 97904400754967899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3241961815913 : Nat.Prime 3241961815913 := by
  refine lucas_primality 3241961815913 (3 : ZMod 3241961815913) ?_ (fun q hq hd => ?_)
  · rw [show 3241961815913 - 1 = 3241961815912 from by norm_num]
    reduce_mod_char
  · have e : 3241961815913 - 1 = [2 ^ 3, 257 ^ 1, 37591 ^ 1, 41947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3241961815913 - 1) / 2 = 1620980907956 from by norm_num]
      have h2 : (3 : ZMod 3241961815913) ^ 1620980907956 = ((3241961815912 : ℕ) : ZMod 3241961815913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3241961815913 - 1) / 257 = 12614637416 from by norm_num]
      have h2 : (3 : ZMod 3241961815913) ^ 12614637416 = ((2872961727774 : ℕ) : ZMod 3241961815913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3241961815913 - 1) / 37591 = 86243032 from by norm_num]
      have h2 : (3 : ZMod 3241961815913) ^ 86243032 = ((2895644441464 : ℕ) : ZMod 3241961815913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3241961815913 - 1) / 41947 = 77287096 from by norm_num]
      have h2 : (3 : ZMod 3241961815913) ^ 77287096 = ((1960518974800 : ℕ) : ZMod 3241961815913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_60209714845136237 : Nat.Prime 60209714845136237 := by
  refine lucas_primality 60209714845136237 (2 : ZMod 60209714845136237) ?_ (fun q hq hd => ?_)
  · rw [show 60209714845136237 - 1 = 60209714845136236 from by norm_num]
    reduce_mod_char
  · have e : 60209714845136237 - 1 = [2 ^ 2, 4643 ^ 1, 3241961815913 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60209714845136237 - 1) / 2 = 30104857422568118 from by norm_num]
      have h2 : (2 : ZMod 60209714845136237) ^ 30104857422568118 = ((60209714845136236 : ℕ) : ZMod 60209714845136237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60209714845136237 - 1) / 4643 = 12967847263652 from by norm_num]
      have h2 : (2 : ZMod 60209714845136237) ^ 12967847263652 = ((48246484051681215 : ℕ) : ZMod 60209714845136237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3241961815913).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60209714845136237 - 1) / 3241961815913 = 18572 from by norm_num]
      have h2 : (2 : ZMod 60209714845136237) ^ 18572 = ((40415181143048372 : ℕ) : ZMod 60209714845136237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2244618169426678915361 : Nat.Prime 2244618169426678915361 := by
  refine lucas_primality 2244618169426678915361 (3 : ZMod 2244618169426678915361) ?_ (fun q hq hd => ?_)
  · rw [show 2244618169426678915361 - 1 = 2244618169426678915360 from by norm_num]
    reduce_mod_char
  · have e : 2244618169426678915361 - 1 = [2 ^ 5, 5 ^ 1, 233 ^ 1, 60209714845136237 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2244618169426678915361 - 1) / 2 = 1122309084713339457680 from by norm_num]
      have h2 : (3 : ZMod 2244618169426678915361) ^ 1122309084713339457680 = ((2244618169426678915360 : ℕ) : ZMod 2244618169426678915361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2244618169426678915361 - 1) / 5 = 448923633885335783072 from by norm_num]
      have h2 : (3 : ZMod 2244618169426678915361) ^ 448923633885335783072 = ((823338832229010133897 : ℕ) : ZMod 2244618169426678915361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2244618169426678915361 - 1) / 233 = 9633554375221797920 from by norm_num]
      have h2 : (3 : ZMod 2244618169426678915361) ^ 9633554375221797920 = ((1740558867766837715665 : ℕ) : ZMod 2244618169426678915361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_60209714845136237).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2244618169426678915361 - 1) / 60209714845136237 = 37280 from by norm_num]
      have h2 : (3 : ZMod 2244618169426678915361) ^ 37280 = ((578342456105570514131 : ℕ) : ZMod 2244618169426678915361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_668858171 : Nat.Prime 668858171 := by
  refine lucas_primality 668858171 (6 : ZMod 668858171) ?_ (fun q hq hd => ?_)
  · rw [show 668858171 - 1 = 668858170 from by norm_num]
    reduce_mod_char
  · have e : 668858171 - 1 = [2 ^ 1, 5 ^ 1, 23 ^ 1, 31 ^ 1, 93809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (668858171 - 1) / 2 = 334429085 from by norm_num]
      have h2 : (6 : ZMod 668858171) ^ 334429085 = ((668858170 : ℕ) : ZMod 668858171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (668858171 - 1) / 5 = 133771634 from by norm_num]
      have h2 : (6 : ZMod 668858171) ^ 133771634 = ((75300188 : ℕ) : ZMod 668858171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (668858171 - 1) / 23 = 29080790 from by norm_num]
      have h2 : (6 : ZMod 668858171) ^ 29080790 = ((115688589 : ℕ) : ZMod 668858171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (668858171 - 1) / 31 = 21576070 from by norm_num]
      have h2 : (6 : ZMod 668858171) ^ 21576070 = ((653637522 : ℕ) : ZMod 668858171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (668858171 - 1) / 93809 = 7130 from by norm_num]
      have h2 : (6 : ZMod 668858171) ^ 7130 = ((313667668 : ℕ) : ZMod 668858171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_27080729627449 : Nat.Prime 27080729627449 := by
  refine lucas_primality 27080729627449 (29 : ZMod 27080729627449) ?_ (fun q hq hd => ?_)
  · rw [show 27080729627449 - 1 = 27080729627448 from by norm_num]
    reduce_mod_char
  · have e : 27080729627449 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 241 ^ 1, 668858171 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27080729627449 - 1) / 2 = 13540364813724 from by norm_num]
      have h2 : (29 : ZMod 27080729627449) ^ 13540364813724 = ((27080729627448 : ℕ) : ZMod 27080729627449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27080729627449 - 1) / 3 = 9026909875816 from by norm_num]
      have h2 : (29 : ZMod 27080729627449) ^ 9026909875816 = ((22758694635300 : ℕ) : ZMod 27080729627449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27080729627449 - 1) / 7 = 3868675661064 from by norm_num]
      have h2 : (29 : ZMod 27080729627449) ^ 3868675661064 = ((770096667384 : ℕ) : ZMod 27080729627449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27080729627449 - 1) / 241 = 112368172728 from by norm_num]
      have h2 : (29 : ZMod 27080729627449) ^ 112368172728 = ((8192345928001 : ℕ) : ZMod 27080729627449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_668858171).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27080729627449 - 1) / 668858171 = 40488 from by norm_num]
      have h2 : (29 : ZMod 27080729627449) ^ 40488 = ((25809909224218 : ℕ) : ZMod 27080729627449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_108322918509797 : Nat.Prime 108322918509797 := by
  refine lucas_primality 108322918509797 (2 : ZMod 108322918509797) ?_ (fun q hq hd => ?_)
  · rw [show 108322918509797 - 1 = 108322918509796 from by norm_num]
    reduce_mod_char
  · have e : 108322918509797 - 1 = [2 ^ 2, 27080729627449 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108322918509797 - 1) / 2 = 54161459254898 from by norm_num]
      have h2 : (2 : ZMod 108322918509797) ^ 54161459254898 = ((108322918509796 : ℕ) : ZMod 108322918509797) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_27080729627449).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108322918509797 - 1) / 27080729627449 = 4 from by norm_num]
      have h2 : (2 : ZMod 108322918509797) ^ 4 = ((16 : ℕ) : ZMod 108322918509797) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6523639444334014529 : Nat.Prime 6523639444334014529 := by
  refine lucas_primality 6523639444334014529 (3 : ZMod 6523639444334014529) ?_ (fun q hq hd => ?_)
  · rw [show 6523639444334014529 - 1 = 6523639444334014528 from by norm_num]
    reduce_mod_char
  · have e : 6523639444334014529 - 1 = [2 ^ 6, 941 ^ 1, 108322918509797 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6523639444334014529 - 1) / 2 = 3261819722167007264 from by norm_num]
      have h2 : (3 : ZMod 6523639444334014529) ^ 3261819722167007264 = ((6523639444334014528 : ℕ) : ZMod 6523639444334014529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6523639444334014529 - 1) / 941 = 6932666784627008 from by norm_num]
      have h2 : (3 : ZMod 6523639444334014529) ^ 6932666784627008 = ((5562911858377247756 : ℕ) : ZMod 6523639444334014529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_108322918509797).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6523639444334014529 - 1) / 108322918509797 = 60224 from by norm_num]
      have h2 : (3 : ZMod 6523639444334014529) ^ 60224 = ((2670938639583966105 : ℕ) : ZMod 6523639444334014529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_87555682126817 : Nat.Prime 87555682126817 := by
  refine lucas_primality 87555682126817 (3 : ZMod 87555682126817) ?_ (fun q hq hd => ?_)
  · rw [show 87555682126817 - 1 = 87555682126816 from by norm_num]
    reduce_mod_char
  · have e : 87555682126817 - 1 = [2 ^ 5, 43 ^ 1, 145441 ^ 1, 437501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (87555682126817 - 1) / 2 = 43777841063408 from by norm_num]
      have h2 : (3 : ZMod 87555682126817) ^ 43777841063408 = ((87555682126816 : ℕ) : ZMod 87555682126817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (87555682126817 - 1) / 43 = 2036178654112 from by norm_num]
      have h2 : (3 : ZMod 87555682126817) ^ 2036178654112 = ((1036803936588 : ℕ) : ZMod 87555682126817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (87555682126817 - 1) / 145441 = 602001376 from by norm_num]
      have h2 : (3 : ZMod 87555682126817) ^ 602001376 = ((25154161090976 : ℕ) : ZMod 87555682126817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (87555682126817 - 1) / 437501 = 200126816 from by norm_num]
      have h2 : (3 : ZMod 87555682126817) ^ 200126816 = ((48293573947827 : ℕ) : ZMod 87555682126817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3764059536281775725352726583190853613559085003075361 : Nat.Prime 3764059536281775725352726583190853613559085003075361 := by
  refine lucas_primality 3764059536281775725352726583190853613559085003075361 (7 : ZMod 3764059536281775725352726583190853613559085003075361) ?_ (fun q hq hd => ?_)
  · rw [show 3764059536281775725352726583190853613559085003075361 - 1 = 3764059536281775725352726583190853613559085003075360 from by norm_num]
    reduce_mod_char
  · have e : 3764059536281775725352726583190853613559085003075361 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 13 ^ 1, 17 ^ 1, 19 ^ 1, 23 ^ 1, 97 ^ 1, 1381 ^ 1, 82657 ^ 1, 109609 ^ 1, 5994449 ^ 1, 42490849 ^ 1, 87555682126817 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 2 = 1882029768140887862676363291595426806779542501537680 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 1882029768140887862676363291595426806779542501537680 = ((3764059536281775725352726583190853613559085003075360 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 3 = 1254686512093925241784242194396951204519695001025120 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 1254686512093925241784242194396951204519695001025120 = ((3058294121753778914488066614975942834242578557879186 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 5 = 752811907256355145070545316638170722711817000615072 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 752811907256355145070545316638170722711817000615072 = ((2942205305049671121015013011223502474783265777372551 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 13 = 289543041252444286565594352553142585658391154082720 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 289543041252444286565594352553142585658391154082720 = ((3646876962366041744691228030600428739800124028774677 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 17 = 221415266840104454432513328422991389032887353122080 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 221415266840104454432513328422991389032887353122080 = ((2663404174469891803854676003270373047313427558408059 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 19 = 198108396646409248702775083325834400713636052793440 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 198108396646409248702775083325834400713636052793440 = ((99675018431898924325936268720085754152290769851313 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 23 = 163654762447033727189248981877863200589525434916320 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 163654762447033727189248981877863200589525434916320 = ((1219919697992120524414530039549152005179474655224643 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 97 = 38804737487440986859306459620524264057310154670880 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 38804737487440986859306459620524264057310154670880 = ((2320833548292050107913114179318155560889303065711553 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 1381 = 2725604298538577643267723811144716592005130342560 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 2725604298538577643267723811144716592005130342560 = ((3087629246817906549747358362970812469710236256950060 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 82657 = 45538303305004727069125743532802468194576200480 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 45538303305004727069125743532802468194576200480 = ((3283973062551602506428938114515214305854935699522212 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 109609 = 34340788952383250694310928693728193976398699040 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 34340788952383250694310928693728193976398699040 = ((576922525225345287692528244142096494271971898093492 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 5994449 = 627924190577278366260639899211896475148772640 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 627924190577278366260639899211896475148772640 = ((1301408439584773138898290112050594351512558319336183 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 42490849 = 88585180688711955963805914614482135048868640 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 88585180688711955963805914614482135048868640 = ((2871167698590732228765227917098925293601765970115485 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_87555682126817).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3764059536281775725352726583190853613559085003075361 - 1) / 87555682126817 = 42990465551166100853974219185368290080 from by norm_num]
      have h2 : (7 : ZMod 3764059536281775725352726583190853613559085003075361) ^ 42990465551166100853974219185368290080 = ((1847810351559816811890043593911139863986890714660758 : ℕ) : ZMod 3764059536281775725352726583190853613559085003075361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12710094097 : Nat.Prime 12710094097 := by
  refine lucas_primality 12710094097 (10 : ZMod 12710094097) ?_ (fun q hq hd => ?_)
  · rw [show 12710094097 - 1 = 12710094096 from by norm_num]
    reduce_mod_char
  · have e : 12710094097 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 173 ^ 1, 218657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12710094097 - 1) / 2 = 6355047048 from by norm_num]
      have h2 : (10 : ZMod 12710094097) ^ 6355047048 = ((12710094096 : ℕ) : ZMod 12710094097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12710094097 - 1) / 3 = 4236698032 from by norm_num]
      have h2 : (10 : ZMod 12710094097) ^ 4236698032 = ((836781127 : ℕ) : ZMod 12710094097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12710094097 - 1) / 7 = 1815727728 from by norm_num]
      have h2 : (10 : ZMod 12710094097) ^ 1815727728 = ((12336400308 : ℕ) : ZMod 12710094097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12710094097 - 1) / 173 = 73468752 from by norm_num]
      have h2 : (10 : ZMod 12710094097) ^ 73468752 = ((4803864214 : ℕ) : ZMod 12710094097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12710094097 - 1) / 218657 = 58128 from by norm_num]
      have h2 : (10 : ZMod 12710094097) ^ 58128 = ((11085399994 : ℕ) : ZMod 12710094097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_79387247729863 : Nat.Prime 79387247729863 := by
  refine lucas_primality 79387247729863 (19 : ZMod 79387247729863) ?_ (fun q hq hd => ?_)
  · rw [show 79387247729863 - 1 = 79387247729862 from by norm_num]
    reduce_mod_char
  · have e : 79387247729863 - 1 = [2 ^ 1, 3 ^ 2, 347 ^ 1, 12710094097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79387247729863 - 1) / 2 = 39693623864931 from by norm_num]
      have h2 : (19 : ZMod 79387247729863) ^ 39693623864931 = ((79387247729862 : ℕ) : ZMod 79387247729863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79387247729863 - 1) / 3 = 26462415909954 from by norm_num]
      have h2 : (19 : ZMod 79387247729863) ^ 26462415909954 = ((54925718610386 : ℕ) : ZMod 79387247729863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79387247729863 - 1) / 347 = 228781693746 from by norm_num]
      have h2 : (19 : ZMod 79387247729863) ^ 228781693746 = ((76460042215339 : ℕ) : ZMod 79387247729863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_12710094097).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79387247729863 - 1) / 12710094097 = 6246 from by norm_num]
      have h2 : (19 : ZMod 79387247729863) ^ 6246 = ((78880259784755 : ℕ) : ZMod 79387247729863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_317548990919453 : Nat.Prime 317548990919453 := by
  refine lucas_primality 317548990919453 (2 : ZMod 317548990919453) ?_ (fun q hq hd => ?_)
  · rw [show 317548990919453 - 1 = 317548990919452 from by norm_num]
    reduce_mod_char
  · have e : 317548990919453 - 1 = [2 ^ 2, 79387247729863 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317548990919453 - 1) / 2 = 158774495459726 from by norm_num]
      have h2 : (2 : ZMod 317548990919453) ^ 158774495459726 = ((317548990919452 : ℕ) : ZMod 317548990919453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_79387247729863).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317548990919453 - 1) / 79387247729863 = 4 from by norm_num]
      have h2 : (2 : ZMod 317548990919453) ^ 4 = ((16 : ℕ) : ZMod 317548990919453) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6919702714312346410535393 : Nat.Prime 6919702714312346410535393 := by
  refine lucas_primality 6919702714312346410535393 (3 : ZMod 6919702714312346410535393) ?_ (fun q hq hd => ?_)
  · rw [show 6919702714312346410535393 - 1 = 6919702714312346410535392 from by norm_num]
    reduce_mod_char
  · have e : 6919702714312346410535393 - 1 = [2 ^ 5, 17093 ^ 1, 39839 ^ 1, 317548990919453 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6919702714312346410535393 - 1) / 2 = 3459851357156173205267696 from by norm_num]
      have h2 : (3 : ZMod 6919702714312346410535393) ^ 3459851357156173205267696 = ((6919702714312346410535392 : ℕ) : ZMod 6919702714312346410535393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6919702714312346410535393 - 1) / 17093 = 404826695975682818144 from by norm_num]
      have h2 : (3 : ZMod 6919702714312346410535393) ^ 404826695975682818144 = ((4932923058505446891639193 : ℕ) : ZMod 6919702714312346410535393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6919702714312346410535393 - 1) / 39839 = 173691676857158724128 from by norm_num]
      have h2 : (3 : ZMod 6919702714312346410535393) ^ 173691676857158724128 = ((1821556499264654449171145 : ℕ) : ZMod 6919702714312346410535393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_317548990919453).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6919702714312346410535393 - 1) / 317548990919453 = 21790976864 from by norm_num]
      have h2 : (3 : ZMod 6919702714312346410535393) ^ 21790976864 = ((1221243996318517201983442 : ℕ) : ZMod 6919702714312346410535393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_27675961108278836246365933814911910609547337515848161 : Nat.Prime 27675961108278836246365933814911910609547337515848161 := by
  refine lucas_primality 27675961108278836246365933814911910609547337515848161 (14 : ZMod 27675961108278836246365933814911910609547337515848161) ?_ (fun q hq hd => ?_)
  · rw [show 27675961108278836246365933814911910609547337515848161 - 1 = 27675961108278836246365933814911910609547337515848160 from by norm_num]
    reduce_mod_char
  · have e : 27675961108278836246365933814911910609547337515848161 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 11 ^ 1, 17 ^ 1, 23 ^ 1, 43 ^ 1, 409 ^ 1, 941 ^ 1, 2081 ^ 1, 65729 ^ 1, 285281 ^ 1, 6919702714312346410535393 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 2 = 13837980554139418123182966907455955304773668757924080 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 13837980554139418123182966907455955304773668757924080 = ((27675961108278836246365933814911910609547337515848160 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 3 = 9225320369426278748788644604970636869849112505282720 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 9225320369426278748788644604970636869849112505282720 = ((15794012762452469560854840775969229986844559670743361 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 5 = 5535192221655767249273186762982382121909467503169632 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 5535192221655767249273186762982382121909467503169632 = ((23974166473669287644102403635462984350119249692923268 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 11 = 2515996464388985113305993983173810055413394319622560 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 2515996464388985113305993983173810055413394319622560 = ((22438646668428860696463130682643615512499284820280493 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 17 = 1627997712251696249786231400877171212326313971520480 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 1627997712251696249786231400877171212326313971520480 = ((12119062971631545374393200671107629317552828235419140 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 23 = 1203302656881688532450692774561387417806405978949920 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 1203302656881688532450692774561387417806405978949920 = ((1251214563021509162873429195211960908957103586488697 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 43 = 643627002518112470845719391044463037431333430601120 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 643627002518112470845719391044463037431333430601120 = ((13175929752698251916926797429565453101458063255547868 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 409 = 67667386572808890577911818618366529607695201750240 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 67667386572808890577911818618366529607695201750240 = ((15483089406210800543338792276578915921141220697513434 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 941 = 29411223281911621940877719250703411912377616913760 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 29411223281911621940877719250703411912377616913760 = ((5853975300044997114857175596500521747757574750976507 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 2081 = 13299356611378585413919237777468481792189974779360 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 13299356611378585413919237777468481792189974779360 = ((1839578610009335375006304639005404929713609675424167 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 65729 = 421061648713335609036588626251911798590383811040 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 421061648713335609036588626251911798590383811040 = ((3259255459853905880342100410332334532615749125199099 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 285281 = 97012984069317046162786634283081980957537787360 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 97012984069317046162786634283081980957537787360 = ((24450634000368210839074536529388750596883646683252176 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6919702714312346410535393).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27675961108278836246365933814911910609547337515848161 - 1) / 6919702714312346410535393 = 3999588168872536225289457120 from by norm_num]
      have h2 : (14 : ZMod 27675961108278836246365933814911910609547337515848161) ^ 3999588168872536225289457120 = ((12393396356239773184614600292942780185702594030223383 : ℕ) : ZMod 27675961108278836246365933814911910609547337515848161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4546777541 : Nat.Prime 4546777541 := by
  refine lucas_primality 4546777541 (7 : ZMod 4546777541) ?_ (fun q hq hd => ?_)
  · rw [show 4546777541 - 1 = 4546777540 from by norm_num]
    reduce_mod_char
  · have e : 4546777541 - 1 = [2 ^ 2, 5 ^ 1, 23 ^ 1, 9884299 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546777541 - 1) / 2 = 2273388770 from by norm_num]
      have h2 : (7 : ZMod 4546777541) ^ 2273388770 = ((4546777540 : ℕ) : ZMod 4546777541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546777541 - 1) / 5 = 909355508 from by norm_num]
      have h2 : (7 : ZMod 4546777541) ^ 909355508 = ((4223444061 : ℕ) : ZMod 4546777541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546777541 - 1) / 23 = 197685980 from by norm_num]
      have h2 : (7 : ZMod 4546777541) ^ 197685980 = ((1061168224 : ℕ) : ZMod 4546777541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546777541 - 1) / 9884299 = 460 from by norm_num]
      have h2 : (7 : ZMod 4546777541) ^ 460 = ((71545569 : ℕ) : ZMod 4546777541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18559945922363 : Nat.Prime 18559945922363 := by
  refine lucas_primality 18559945922363 (2 : ZMod 18559945922363) ?_ (fun q hq hd => ?_)
  · rw [show 18559945922363 - 1 = 18559945922362 from by norm_num]
    reduce_mod_char
  · have e : 18559945922363 - 1 = [2 ^ 1, 13 ^ 1, 157 ^ 1, 4546777541 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18559945922363 - 1) / 2 = 9279972961181 from by norm_num]
      have h2 : (2 : ZMod 18559945922363) ^ 9279972961181 = ((18559945922362 : ℕ) : ZMod 18559945922363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18559945922363 - 1) / 13 = 1427688147874 from by norm_num]
      have h2 : (2 : ZMod 18559945922363) ^ 1427688147874 = ((3123598530323 : ℕ) : ZMod 18559945922363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18559945922363 - 1) / 157 = 118216216066 from by norm_num]
      have h2 : (2 : ZMod 18559945922363) ^ 118216216066 = ((15500446853917 : ℕ) : ZMod 18559945922363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4546777541).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18559945922363 - 1) / 4546777541 = 4082 from by norm_num]
      have h2 : (2 : ZMod 18559945922363) ^ 4082 = ((4374738773227 : ℕ) : ZMod 18559945922363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1400284701649479471689453046497 : Nat.Prime 1400284701649479471689453046497 := by
  refine lucas_primality 1400284701649479471689453046497 (5 : ZMod 1400284701649479471689453046497) ?_ (fun q hq hd => ?_)
  · rw [show 1400284701649479471689453046497 - 1 = 1400284701649479471689453046496 from by norm_num]
    reduce_mod_char
  · have e : 1400284701649479471689453046497 - 1 = [2 ^ 5, 13 ^ 1, 19 ^ 1, 474049 ^ 1, 20135827 ^ 1, 18559945922363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 2 = 700142350824739735844726523248 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 700142350824739735844726523248 = ((1400284701649479471689453046496 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 13 = 107714207819190728591496388192 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 107714207819190728591496388192 = ((11376444238969442486408183972 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 19 = 73699194823656814299444897184 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 73699194823656814299444897184 = ((1329810630184506366105109173273 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 474049 = 2953881775195136940884704 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 2953881775195136940884704 = ((667508505279244980967224920941 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 20135827 = 69541951351165237548448 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 69541951351165237548448 = ((798597730755927369052430161435 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_18559945922363).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1400284701649479471689453046497 - 1) / 18559945922363 = 75446593837445792 from by norm_num]
      have h2 : (5 : ZMod 1400284701649479471689453046497) ^ 75446593837445792 = ((392136057485459345710035009573 : ℕ) : ZMod 1400284701649479471689453046497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_819307039 : Nat.Prime 819307039 := by
  refine lucas_primality 819307039 (12 : ZMod 819307039) ?_ (fun q hq hd => ?_)
  · rw [show 819307039 - 1 = 819307038 from by norm_num]
    reduce_mod_char
  · have e : 819307039 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 12413743 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (819307039 - 1) / 2 = 409653519 from by norm_num]
      have h2 : (12 : ZMod 819307039) ^ 409653519 = ((819307038 : ℕ) : ZMod 819307039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (819307039 - 1) / 3 = 273102346 from by norm_num]
      have h2 : (12 : ZMod 819307039) ^ 273102346 = ((97243770 : ℕ) : ZMod 819307039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (819307039 - 1) / 11 = 74482458 from by norm_num]
      have h2 : (12 : ZMod 819307039) ^ 74482458 = ((627014267 : ℕ) : ZMod 819307039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (819307039 - 1) / 12413743 = 66 from by norm_num]
      have h2 : (12 : ZMod 819307039) ^ 66 = ((207528045 : ℕ) : ZMod 819307039) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9831684469 : Nat.Prime 9831684469 := by
  refine lucas_primality 9831684469 (7 : ZMod 9831684469) ?_ (fun q hq hd => ?_)
  · rw [show 9831684469 - 1 = 9831684468 from by norm_num]
    reduce_mod_char
  · have e : 9831684469 - 1 = [2 ^ 2, 3 ^ 1, 819307039 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9831684469 - 1) / 2 = 4915842234 from by norm_num]
      have h2 : (7 : ZMod 9831684469) ^ 4915842234 = ((9831684468 : ℕ) : ZMod 9831684469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9831684469 - 1) / 3 = 3277228156 from by norm_num]
      have h2 : (7 : ZMod 9831684469) ^ 3277228156 = ((7597055707 : ℕ) : ZMod 9831684469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_819307039).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9831684469 - 1) / 819307039 = 12 from by norm_num]
      have h2 : (7 : ZMod 9831684469) ^ 12 = ((4009602732 : ℕ) : ZMod 9831684469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_124767963752916421361 : Nat.Prime 124767963752916421361 := by
  refine lucas_primality 124767963752916421361 (11 : ZMod 124767963752916421361) ?_ (fun q hq hd => ?_)
  · rw [show 124767963752916421361 - 1 = 124767963752916421360 from by norm_num]
    reduce_mod_char
  · have e : 124767963752916421361 - 1 = [2 ^ 4, 5 ^ 1, 41 ^ 1, 3869023 ^ 1, 9831684469 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (124767963752916421361 - 1) / 2 = 62383981876458210680 from by norm_num]
      have h2 : (11 : ZMod 124767963752916421361) ^ 62383981876458210680 = ((124767963752916421360 : ℕ) : ZMod 124767963752916421361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (124767963752916421361 - 1) / 5 = 24953592750583284272 from by norm_num]
      have h2 : (11 : ZMod 124767963752916421361) ^ 24953592750583284272 = ((118517221565989780762 : ℕ) : ZMod 124767963752916421361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (124767963752916421361 - 1) / 41 = 3043121067144302960 from by norm_num]
      have h2 : (11 : ZMod 124767963752916421361) ^ 3043121067144302960 = ((53446486263681136365 : ℕ) : ZMod 124767963752916421361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (124767963752916421361 - 1) / 3869023 = 32247925058320 from by norm_num]
      have h2 : (11 : ZMod 124767963752916421361) ^ 32247925058320 = ((8447225074993139739 : ℕ) : ZMod 124767963752916421361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9831684469).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (124767963752916421361 - 1) / 9831684469 = 12690395440 from by norm_num]
      have h2 : (11 : ZMod 124767963752916421361) ^ 12690395440 = ((90002653080765389884 : ℕ) : ZMod 124767963752916421361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_30038530241 : Nat.Prime 30038530241 := by
  refine lucas_primality 30038530241 (3 : ZMod 30038530241) ?_ (fun q hq hd => ?_)
  · rw [show 30038530241 - 1 = 30038530240 from by norm_num]
    reduce_mod_char
  · have e : 30038530241 - 1 = [2 ^ 6, 5 ^ 1, 79 ^ 1, 1188233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30038530241 - 1) / 2 = 15019265120 from by norm_num]
      have h2 : (3 : ZMod 30038530241) ^ 15019265120 = ((30038530240 : ℕ) : ZMod 30038530241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30038530241 - 1) / 5 = 6007706048 from by norm_num]
      have h2 : (3 : ZMod 30038530241) ^ 6007706048 = ((24700125332 : ℕ) : ZMod 30038530241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30038530241 - 1) / 79 = 380234560 from by norm_num]
      have h2 : (3 : ZMod 30038530241) ^ 380234560 = ((8524425283 : ℕ) : ZMod 30038530241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30038530241 - 1) / 1188233 = 25280 from by norm_num]
      have h2 : (3 : ZMod 30038530241) ^ 25280 = ((1715744660 : ℕ) : ZMod 30038530241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_40609718909822860125593921085059883221916065593219681 : Nat.Prime 40609718909822860125593921085059883221916065593219681 := by
  refine lucas_primality 40609718909822860125593921085059883221916065593219681 (11 : ZMod 40609718909822860125593921085059883221916065593219681) ?_ (fun q hq hd => ?_)
  · rw [show 40609718909822860125593921085059883221916065593219681 - 1 = 40609718909822860125593921085059883221916065593219680 from by norm_num]
    reduce_mod_char
  · have e : 40609718909822860125593921085059883221916065593219681 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 2, 17 ^ 1, 281 ^ 1, 673 ^ 1, 1013 ^ 1, 1697 ^ 1, 24169 ^ 1, 30038530241 ^ 1, 124767963752916421361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 2 = 20304859454911430062796960542529941610958032796609840 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 20304859454911430062796960542529941610958032796609840 = ((40609718909822860125593921085059883221916065593219680 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 3 = 13536572969940953375197973695019961073972021864406560 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 13536572969940953375197973695019961073972021864406560 = ((27961554485194409413132197633831989714707396552377399 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 5 = 8121943781964572025118784217011976644383213118643936 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 8121943781964572025118784217011976644383213118643936 = ((19897293642155991402152428544757430163621170635015305 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 13 = 3123824531524835394276455468081529478608928122555360 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 3123824531524835394276455468081529478608928122555360 = ((36723181836528215158873284010543754724366557744109692 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 17 = 2388806994695462360329054181474110777759768564307040 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 2388806994695462360329054181474110777759768564307040 = ((29566040896891921676928225804059665665508379740950390 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 281 = 144518572632821566283252388203060082640270696061280 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 144518572632821566283252388203060082640270696061280 = ((35202639149486771956084547947013533877206732288531377 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 673 = 60341335675814056650213850052094923063768299544160 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 60341335675814056650213850052094923063768299544160 = ((7430466815926636134138634200873330962879018823675904 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 1013 = 40088567531908055405324699985251612262503519835360 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 40088567531908055405324699985251612262503519835360 = ((457510627347483278340325927097696724137976348087880 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 1697 = 23930299887933329478841438470866165717098447609440 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 23930299887933329478841438470866165717098447609440 = ((20306037898155000212242678631569997813727338756351898 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 24169 = 1680239931723400228623191736731345244814268922720 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 1680239931723400228623191736731345244814268922720 = ((25521192848903608759321134461438844115019066516710954 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_30038530241).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 30038530241 = 1351920968969184131314699668666118584144480 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 1351920968969184131314699668666118584144480 = ((5242181683738886460793876829484728260612727244400903 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_124767963752916421361).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40609718909822860125593921085059883221916065593219681 - 1) / 124767963752916421361 = 325481940141654492960698627702880 from by norm_num]
      have h2 : (11 : ZMod 40609718909822860125593921085059883221916065593219681) ^ 325481940141654492960698627702880 = ((30780204064581394775780584503678155451507941379001763 : ℕ) : ZMod 40609718909822860125593921085059883221916065593219681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- z = 41: 3^2 | 17+1
theorem k16_41 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 41 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 41 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 41 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 41 ^ 16 ∣ 1 + 41 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g31879515457326527173216321 := S7 31879515457326527173216321 prime_31879515457326527173216321 (by norm_num) (by decide) ((by norm_num : 31879515457326527173216321 ∣ 1 + 41 ^ 16).trans hd)
  have g15939757728663263586608161 := S1 15939757728663263586608161 prime_15939757728663263586608161 (by norm_num) (by decide) 31879515457326527173216321 g31879515457326527173216321 (by norm_num)
  have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 15939757728663263586608161 g15939757728663263586608161 (by norm_num)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 73: 7 | 325188939908904785521061417281+1, 1110085633+1
theorem k16_73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 73 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 73 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 73 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 73 ^ 16 ∣ 1 + 73 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g325188939908904785521061417281 := S7 325188939908904785521061417281 prime_325188939908904785521061417281 (by norm_num) (by decide) ((by norm_num : 325188939908904785521061417281 ∣ 1 + 73 ^ 16).trans hd)
  have g1110085633 := S1 1110085633 prime_1110085633 (by norm_num) (by decide) 325188939908904785521061417281 g325188939908904785521061417281 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 325188939908904785521061417281 g325188939908904785521061417281 1110085633 g1110085633 (by norm_num) (by norm_num)) (by norm_num)

-- z = 113: 3 | 2207+1, 23+1
theorem k16_113 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 113 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 113 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 113 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 113 ^ 16 ∣ 1 + 113 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g353366276339896558409817277595521 := S7 353366276339896558409817277595521 prime_353366276339896558409817277595521 (by norm_num) (by decide) ((by norm_num : 353366276339896558409817277595521 ∣ 1 + 113 ^ 16).trans hd)
  have g176683138169948279204908638797761 := S1 176683138169948279204908638797761 prime_176683138169948279204908638797761 (by norm_num) (by decide) 353366276339896558409817277595521 g353366276339896558409817277595521 (by norm_num)
  have g2207 := S1 2207 (by norm_num) (by norm_num) (by decide) 176683138169948279204908638797761 g176683138169948279204908638797761 (by norm_num)
  have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 2207 g2207 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2207 g2207 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- z = 157: 7 | 68134087338311652398492776425866401+1, 6243691+1
theorem k16_157 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 157 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 157 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 157 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 157 ^ 16 ∣ 1 + 157 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g68134087338311652398492776425866401 := S7 68134087338311652398492776425866401 prime_68134087338311652398492776425866401 (by norm_num) (by decide) ((by norm_num : 68134087338311652398492776425866401 ∣ 1 + 157 ^ 16).trans hd)
  have g12487381 := S1 12487381 (by norm_num) (by norm_num) (by decide) 68134087338311652398492776425866401 g68134087338311652398492776425866401 (by norm_num)
  have g6243691 := S1 6243691 (by norm_num) (by norm_num) (by decide) 12487381 g12487381 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (by decide) 68134087338311652398492776425866401 g68134087338311652398492776425866401 6243691 g6243691 (by norm_num) (by norm_num)) (by norm_num)

-- z = 167: 3^2 | 647+1
theorem k16_167 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 167 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 167 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 167 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 167 ^ 16 ∣ 1 + 167 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g182992606302133822302202039519035841 := S7 182992606302133822302202039519035841 prime_182992606302133822302202039519035841 (by norm_num) (by decide) ((by norm_num : 182992606302133822302202039519035841 ∣ 1 + 167 ^ 16).trans hd)
  have g130693 := S1 130693 (by norm_num) (by norm_num) (by decide) 182992606302133822302202039519035841 g182992606302133822302202039519035841 (by norm_num)
  have g647 := S1 647 (by norm_num) (by norm_num) (by decide) 130693 g130693 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 647 g647 (by norm_num)

-- z = 173: 7^2 | 104173+1
theorem k16_173 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 173 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 173 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 173 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 173 ^ 16 ∣ 1 + 173 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g321890125642414371933129862358702881 := S7 321890125642414371933129862358702881 prime_321890125642414371933129862358702881 (by norm_num) (by decide) ((by norm_num : 321890125642414371933129862358702881 ∣ 1 + 173 ^ 16).trans hd)
  have g104173 := S1 104173 (by norm_num) (by norm_num) (by decide) 321890125642414371933129862358702881 g321890125642414371933129862358702881 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (by decide) 104173 g104173 (by norm_num)

-- z = 199: 5^2 | 71811199+1
theorem k16_199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 199 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 199 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 199 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 199 ^ 16 ∣ 1 + 199 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g3024260707038777360639558573762398401 := S7 3024260707038777360639558573762398401 prime_3024260707038777360639558573762398401 (by norm_num) (by decide) ((by norm_num : 3024260707038777360639558573762398401 ∣ 1 + 199 ^ 16).trans hd)
  have g71811199 := S1 71811199 prime_71811199 (by norm_num) (by decide) 3024260707038777360639558573762398401 g3024260707038777360639558573762398401 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 71811199 g71811199 (by norm_num)

-- z = 307: 3^2 | 111736413709754849+1
theorem k16_307 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 307 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 307 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 307 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 307 ^ 16 ∣ 1 + 307 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g111736413709754849 := S7 111736413709754849 prime_111736413709754849 (by norm_num) (by decide) ((by norm_num : 111736413709754849 ∣ 1 + 307 ^ 16).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 111736413709754849 g111736413709754849 (by norm_num)

-- z = 449: 7^2 | 56596504371295886017+1
theorem k16_449 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 449 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 449 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 449 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 449 ^ 16 ∣ 1 + 449 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g56596504371295886017 := S7 56596504371295886017 prime_56596504371295886017 (by norm_num) (by decide) ((by norm_num : 56596504371295886017 ∣ 1 + 449 ^ 16).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (by decide) 56596504371295886017 g56596504371295886017 (by norm_num)

-- z = 599: 3^2 | 71+1
theorem k16_599 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 599 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 599 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 599 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 599 ^ 16 ∣ 1 + 599 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g137340670268189743177332632848914035541595201 := S7 137340670268189743177332632848914035541595201 prime_137340670268189743177332632848914035541595201 (by norm_num) (by decide) ((by norm_num : 137340670268189743177332632848914035541595201 ∣ 1 + 599 ^ 16).trans hd)
  have g14767 := S1 14767 (by norm_num) (by norm_num) (by decide) 137340670268189743177332632848914035541595201 g137340670268189743177332632848914035541595201 (by norm_num)
  have g71 := S1 71 (by norm_num) (by norm_num) (by decide) 14767 g14767 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 71 g71 (by norm_num)

-- z = 607: 3 | 11+1, 23+1
theorem k16_607 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 607 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 607 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 607 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 607 ^ 16 ∣ 1 + 607 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g169820087978821461720620325094410956611411201 := S7 169820087978821461720620325094410956611411201 prime_169820087978821461720620325094410956611411201 (by norm_num) (by decide) ((by norm_num : 169820087978821461720620325094410956611411201 ∣ 1 + 607 ^ 16).trans hd)
  have g43 := S1 43 (by norm_num) (by norm_num) (by decide) 169820087978821461720620325094410956611411201 g169820087978821461720620325094410956611411201 (by norm_num)
  have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 43 g43 (by norm_num)
  have g643 := S1 643 (by norm_num) (by norm_num) (by decide) 169820087978821461720620325094410956611411201 g169820087978821461720620325094410956611411201 (by norm_num)
  have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 643 g643 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- z = 617: 31^2 | 220562984078060416488507466656249330775640641+1
theorem k16_617 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 617 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 617 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 617 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 617 ^ 16 ∣ 1 + 617 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g220562984078060416488507466656249330775640641 := S7 220562984078060416488507466656249330775640641 prime_220562984078060416488507466656249330775640641 (by norm_num) (by decide) ((by norm_num : 220562984078060416488507466656249330775640641 ∣ 1 + 617 ^ 16).trans hd)
  exact S6 31 (by norm_num) (by norm_num) (by decide) 220562984078060416488507466656249330775640641 g220562984078060416488507466656249330775640641 (by norm_num)

-- z = 643: 3^2 | 792593+1
theorem k16_643 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 643 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 643 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 643 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 643 ^ 16 ∣ 1 + 643 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g105579695041 := S7 105579695041 prime_105579695041 (by norm_num) (by decide) ((by norm_num : 105579695041 ∣ 1 + 643 ^ 16).trans hd)
  have g3170371 := S1 3170371 (by norm_num) (by norm_num) (by decide) 105579695041 g105579695041 (by norm_num)
  have g792593 := S1 792593 (by norm_num) (by norm_num) (by decide) 3170371 g3170371 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 792593 g792593 (by norm_num)

-- z = 743: 3^2 | 17+1
theorem k16_743 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 743 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 743 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 743 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 743 ^ 16 ∣ 1 + 743 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2736104004752161 := S7 2736104004752161 prime_2736104004752161 (by norm_num) (by decide) ((by norm_num : 2736104004752161 ∣ 1 + 743 ^ 16).trans hd)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 2736104004752161 g2736104004752161 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 811: 3^2 | 179+1
theorem k16_811 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 811 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 811 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 811 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 811 ^ 16 ∣ 1 + 811 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g7457057188513 := S7 7457057188513 prime_7457057188513 (by norm_num) (by decide) ((by norm_num : 7457057188513 ∣ 1 + 811 ^ 16).trans hd)
  have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 7457057188513 g7457057188513 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)

-- z = 937: 3^2 | 2494456365329+1
theorem k16_937 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 937 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 937 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 937 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 937 ^ 16 ∣ 1 + 937 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g803214949635937 := S7 803214949635937 prime_803214949635937 (by norm_num) (by decide) ((by norm_num : 803214949635937 ∣ 1 + 937 ^ 16).trans hd)
  have g2494456365329 := S1 2494456365329 prime_2494456365329 (by norm_num) (by decide) 803214949635937 g803214949635937 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 2494456365329 g2494456365329 (by norm_num)

-- z = 967: 7^2 | 310244476401636693981217+1
theorem k16_967 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 967 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 967 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 967 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 967 ^ 16 ∣ 1 + 967 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g310244476401636693981217 := S7 310244476401636693981217 prime_310244476401636693981217 (by norm_num) (by decide) ((by norm_num : 310244476401636693981217 ∣ 1 + 967 ^ 16).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (by decide) 310244476401636693981217 g310244476401636693981217 (by norm_num)

-- z = 1201: 3^2 | 881207+1
theorem k16_1201 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1201 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1201 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1201 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1201 ^ 16 ∣ 1 + 1201 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g95586439034017 := S7 95586439034017 prime_95586439034017 (by norm_num) (by decide) ((by norm_num : 95586439034017 ∣ 1 + 1201 ^ 16).trans hd)
  have g881207 := S1 881207 (by norm_num) (by norm_num) (by decide) 95586439034017 g95586439034017 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 881207 g881207 (by norm_num)

-- z = 1213: 3^2 | 17+1
theorem k16_1213 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1213 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1213 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1213 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1213 ^ 16 ∣ 1 + 1213 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g10983552195457570260986954785955861855365952457121 := S7 10983552195457570260986954785955861855365952457121 prime_10983552195457570260986954785955861855365952457121 (by norm_num) (by decide) ((by norm_num : 10983552195457570260986954785955861855365952457121 ∣ 1 + 1213 ^ 16).trans hd)
  have g3894223 := S1 3894223 (by norm_num) (by norm_num) (by decide) 10983552195457570260986954785955861855365952457121 g10983552195457570260986954785955861855365952457121 (by norm_num)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 3894223 g3894223 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 1237: 3^2 | 1331279+1
theorem k16_1237 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1237 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1237 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1237 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1237 ^ 16 ∣ 1 + 1237 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g337734688130619396257 := S7 337734688130619396257 prime_337734688130619396257 (by norm_num) (by decide) ((by norm_num : 337734688130619396257 ∣ 1 + 1237 ^ 16).trans hd)
  have g37275811 := S1 37275811 (by norm_num) (by norm_num) (by decide) 337734688130619396257 g337734688130619396257 (by norm_num)
  have g1331279 := S1 1331279 (by norm_num) (by norm_num) (by decide) 37275811 g37275811 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 1331279 g1331279 (by norm_num)

-- z = 1249: 5^2 | 1999+1
theorem k16_1249 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1249 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1249 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1249 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1249 ^ 16 ∣ 1 + 1249 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g311920921441 := S7 311920921441 prime_311920921441 (by norm_num) (by decide) ((by norm_num : 311920921441 ∣ 1 + 1249 ^ 16).trans hd)
  have g11996958517 := S1 11996958517 prime_11996958517 (by norm_num) (by decide) 311920921441 g311920921441 (by norm_num)
  have g5998479259 := S1 5998479259 prime_5998479259 (by norm_num) (by decide) 11996958517 g11996958517 (by norm_num)
  have g1999 := S1 1999 (by norm_num) (by norm_num) (by decide) 5998479259 g5998479259 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 1999 g1999 (by norm_num)

-- z = 1277: 5^2 | 149+1
theorem k16_1277 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1277 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1277 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1277 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1277 ^ 16 ∣ 1 + 1277 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g207817026647174251535873 := S7 207817026647174251535873 prime_207817026647174251535873 (by norm_num) (by decide) ((by norm_num : 207817026647174251535873 ∣ 1 + 1277 ^ 16).trans hd)
  have g149 := S1 149 (by norm_num) (by norm_num) (by decide) 207817026647174251535873 g207817026647174251535873 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 149 g149 (by norm_num)

-- z = 1297: 3 | 11+1, 29+1
theorem k16_1297 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1297 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1297 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1297 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1297 ^ 16 ∣ 1 + 1297 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g11739987604453404097 := S7 11739987604453404097 prime_11739987604453404097 (by norm_num) (by decide) ((by norm_num : 11739987604453404097 ∣ 1 + 1297 ^ 16).trans hd)
  have g11 := S1 11 (by norm_num) (by norm_num) (by decide) 11739987604453404097 g11739987604453404097 (by norm_num)
  have g12037 := S1 12037 (by norm_num) (by norm_num) (by decide) 11739987604453404097 g11739987604453404097 (by norm_num)
  have g463 := S1 463 (by norm_num) (by norm_num) (by decide) 12037 g12037 (by norm_num)
  have g29 := S1 29 (by norm_num) (by norm_num) (by decide) 463 g463 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 11 g11 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- z = 1373: 13^2 | 1013+1
theorem k16_1373 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1373 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1373 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1373 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1373 ^ 16 ∣ 1 + 1373 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g9091986456255036663841 := S7 9091986456255036663841 prime_9091986456255036663841 (by norm_num) (by decide) ((by norm_num : 9091986456255036663841 ∣ 1 + 1373 ^ 16).trans hd)
  have g8101 := S1 8101 (by norm_num) (by norm_num) (by decide) 9091986456255036663841 g9091986456255036663841 (by norm_num)
  have g4051 := S1 4051 (by norm_num) (by norm_num) (by decide) 8101 g8101 (by norm_num)
  have g1013 := S1 1013 (by norm_num) (by norm_num) (by decide) 4051 g4051 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (by decide) 1013 g1013 (by norm_num)

-- z = 1579: 5^2 | 97904400754967899+1
theorem k16_1579 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1579 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1579 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1579 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1579 ^ 16 ∣ 1 + 1579 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g587426404529807393 := S7 587426404529807393 prime_587426404529807393 (by norm_num) (by decide) ((by norm_num : 587426404529807393 ∣ 1 + 1579 ^ 16).trans hd)
  have g97904400754967899 := S1 97904400754967899 prime_97904400754967899 (by norm_num) (by decide) 587426404529807393 g587426404529807393 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (by decide) 97904400754967899 g97904400754967899 (by norm_num)

-- z = 1637: 3 | 2244618169426678915361+1, 23+1
theorem k16_1637 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1637 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1637 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1637 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1637 ^ 16 ∣ 1 + 1637 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g2244618169426678915361 := S7 2244618169426678915361 prime_2244618169426678915361 (by norm_num) (by decide) ((by norm_num : 2244618169426678915361 ∣ 1 + 1637 ^ 16).trans hd)
  have g47581 := S1 47581 (by norm_num) (by norm_num) (by decide) 2244618169426678915361 g2244618169426678915361 (by norm_num)
  have g643 := S1 643 (by norm_num) (by norm_num) (by decide) 47581 g47581 (by norm_num)
  have g23 := S1 23 (by norm_num) (by norm_num) (by decide) 643 g643 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (by decide) 2244618169426678915361 g2244618169426678915361 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- z = 1667: 3^2 | 179+1
theorem k16_1667 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1667 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1667 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1667 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1667 ^ 16 ∣ 1 + 1667 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g6523639444334014529 := S7 6523639444334014529 prime_6523639444334014529 (by norm_num) (by decide) ((by norm_num : 6523639444334014529 ∣ 1 + 1667 ^ 16).trans hd)
  have g179 := S1 179 (by norm_num) (by norm_num) (by decide) 6523639444334014529 g6523639444334014529 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 179 g179 (by norm_num)

-- z = 1747: 7^2 | 3764059536281775725352726583190853613559085003075361+1
theorem k16_1747 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1747 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1747 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1747 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1747 ^ 16 ∣ 1 + 1747 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g3764059536281775725352726583190853613559085003075361 := S7 3764059536281775725352726583190853613559085003075361 prime_3764059536281775725352726583190853613559085003075361 (by norm_num) (by decide) ((by norm_num : 3764059536281775725352726583190853613559085003075361 ∣ 1 + 1747 ^ 16).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (by decide) 3764059536281775725352726583190853613559085003075361 g3764059536281775725352726583190853613559085003075361 (by norm_num)

-- z = 1979: 3^2 | 17+1
theorem k16_1979 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 1979 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 1979 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 1979 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 1979 ^ 16 ∣ 1 + 1979 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g27675961108278836246365933814911910609547337515848161 := S7 27675961108278836246365933814911910609547337515848161 prime_27675961108278836246365933814911910609547337515848161 (by norm_num) (by decide) ((by norm_num : 27675961108278836246365933814911910609547337515848161 ∣ 1 + 1979 ^ 16).trans hd)
  have g937 := S1 937 (by norm_num) (by norm_num) (by decide) 27675961108278836246365933814911910609547337515848161 g27675961108278836246365933814911910609547337515848161 (by norm_num)
  have g67 := S1 67 (by norm_num) (by norm_num) (by decide) 937 g937 (by norm_num)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 67 g67 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- z = 2011: 3^2 | 1400284701649479471689453046497+1
theorem k16_2011 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 2011 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 2011 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 2011 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 2011 ^ 16 ∣ 1 + 2011 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g1400284701649479471689453046497 := S7 1400284701649479471689453046497 prime_1400284701649479471689453046497 (by norm_num) (by decide) ((by norm_num : 1400284701649479471689453046497 ∣ 1 + 2011 ^ 16).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 1400284701649479471689453046497 g1400284701649479471689453046497 (by norm_num)

-- z = 2027: 3^2 | 17+1
theorem k16_2027 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (he : e % 32 = 16)
    (E : (2 ^ m + 1) * (1 + 2027 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 2027 ^ e * ∏ p ∈ P, p) : False := by
  have hz : Nat.Prime 2027 := by norm_num
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have hd : 1 + 2027 ^ 16 ∣ 1 + 2027 ^ e := one_add_pow_dvd_of_odd_mul (by omega)
  clear E S2 S4 S5
  have g40609718909822860125593921085059883221916065593219681 := S7 40609718909822860125593921085059883221916065593219681 prime_40609718909822860125593921085059883221916065593219681 (by norm_num) (by decide) ((by norm_num : 40609718909822860125593921085059883221916065593219681 ∣ 1 + 2027 ^ 16).trans hd)
  have g383587 := S1 383587 (by norm_num) (by norm_num) (by decide) 40609718909822860125593921085059883221916065593219681 g40609718909822860125593921085059883221916065593219681 (by norm_num)
  have g17 := S1 17 (by norm_num) (by norm_num) (by decide) 383587 g383587 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (by decide) 17 g17 (by norm_num)

-- The step: e = 16 mod 32 is impossible for each of the 31 primes.
theorem H1_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1.H1 := by
  refine ⟨0, fun n h z hz hS c hm _ _ _ _ _ _ _ _ _ _ => False.elim ?_⟩
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hz2 : z ≠ 2 := by omega
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k16_41 hP c E
  · exact k16_73 hP c E
  · exact k16_113 hP c E
  · exact k16_157 hP c E
  · exact k16_167 hP c E
  · exact k16_173 hP c E
  · exact k16_199 hP c E
  · exact k16_307 hP c E
  · exact k16_449 hP c E
  · exact k16_599 hP c E
  · exact k16_607 hP c E
  · exact k16_617 hP c E
  · exact k16_643 hP c E
  · exact k16_743 hP c E
  · exact k16_811 hP c E
  · exact k16_937 hP c E
  · exact k16_967 hP c E
  · exact k16_1201 hP c E
  · exact k16_1213 hP c E
  · exact k16_1237 hP c E
  · exact k16_1249 hP c E
  · exact k16_1277 hP c E
  · exact k16_1297 hP c E
  · exact k16_1373 hP c E
  · exact k16_1579 hP c E
  · exact k16_1637 hP c E
  · exact k16_1667 hP c E
  · exact k16_1747 hP c E
  · exact k16_1979 hP c E
  · exact k16_2011 hP c E
  · exact k16_2027 hP c E

end OMA.Erdos1052Z16

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1.H1 := OMA.Erdos1052Z16.H1_proof
