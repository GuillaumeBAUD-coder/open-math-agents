import OMAReductions.R_OeisA218656_conjecture_3_R1
import Mathlib.NumberTheory.LucasPrimality

/-!
Mauro Fiorentini reported numerical verification of the eighth-power conjecture
through odd totals of one million (OEIS A218656, September 2023).
Here each admissible input through n = 64 has an explicit partition.
The predecessor factors and primitive roots below certify primality via Lucas's criterion.
The modular exponentiation lemma is from the project's A229232 conjecture 5 proof
by @zarnab222-dev (commit ae59879b).
-/

namespace EighthPowerCertificates


def powAux (q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f+1, b, e, acc =>
    if e = 0 then acc
    else powAux q f (b*b % q) (e/2) (if e % 2 = 1 then acc*b % q else acc)

theorem powAux_spec (q : ℕ) :
    ∀ f b e acc, e < 2^f → powAux q f b e acc % q = acc * b^e % q := by
  intro f
  induction f with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp [powAux]
  | succ f ih =>
    intro b e acc he
    unfold powAux
    by_cases h0 : e = 0
    · simp [h0]
    · rw [if_neg h0, ih _ _ _ (by rw [pow_succ] at he; omega)]
      change _ ≡ _ [MOD q]
      have hb : (b*b % q)^(e/2) ≡ b^(2*(e/2)) [MOD q] := by
        rw [pow_mul, pow_two]
        exact (Nat.mod_modEq _ _).pow _
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        have he2 : e = 2*(e/2) + 1 := by omega
        calc acc*b % q * (b*b % q)^(e/2) ≡ acc*b * b^(2*(e/2)) [MOD q] :=
              (Nat.mod_modEq _ _).mul hb
          _ = acc * b^(2*(e/2)+1) := by ring
          _ = acc * b^e := by rw [← he2]
      · rw [if_neg h1]
        have he2 : e = 2*(e/2) := by omega
        calc acc * (b*b % q)^(e/2) ≡ acc * b^(2*(e/2)) [MOD q] := (Nat.ModEq.refl _).mul hb
          _ = acc * b^e := by rw [← he2]

def powMod (a e q : ℕ) : ℕ := powAux q 64 a e 1 % q

theorem powMod_eq {a e q : ℕ} (he : e < 2^64) : powMod a e q = a^e % q := by
  rw [powMod, powAux_spec q 64 a e 1 he, one_mul]

theorem powMod_eq_one_iff {a e q : ℕ} (hq : 1 < q) (he : e < 2^64) :
    powMod a e q = 1 ↔ ((a : ℕ) : ZMod q)^e = 1 := by
  rw [powMod_eq he, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod q), ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hq]



private def AllPrime (ps : List ℕ) := ∀ p ∈ ps, Nat.Prime p
private theorem empty : AllPrime [] := by simp [AllPrime]
private theorem cons {p : ℕ} {ps : List ℕ} (h : p.Prime) (hs : AllPrime ps) :
    AllPrime (p :: ps) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h
  · exact hs _ hr

/-- The listed primes cover all divisors of q-1; the modular checks give an element of order q-1. -/
private theorem certificate (q g : ℕ) (ps : List ℕ) (hs : AllPrime ps)
    (hq : 1 < q) (hbound : q < 2^64) (cover : ps.prod^64 % (q-1) = 0)
    (full : powMod g (q-1) q = 1)
    (parts : ps.all (fun p => decide (powMod g ((q-1)/p) q ≠ 1)) = true) : q.Prime := by
  have hb : q - 1 < 2^64 := by omega
  apply lucas_primality q (g : ZMod q) ((powMod_eq_one_iff hq hb).mp full)
  intro p hp hd heq
  have hd' : p ∣ ps.prod := hp.dvd_of_dvd_pow (hd.trans (Nat.dvd_of_mod_eq_zero cover))
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_prod_iff hp.prime).mp hd'
  have eq := (Nat.prime_dvd_prime_iff_eq hp (hs _ hr)).mp hpr
  subst r
  have hne := of_decide_eq_true ((List.all_eq_true.mp parts) p hr)
  exact hne ((powMod_eq_one_iff hq (lt_of_le_of_lt (Nat.div_le_self _ _) hb)).mpr heq)

set_option maxRecDepth 16000 in
private theorem p503 : Nat.Prime 503 :=
  certificate 503 5 [2, 251]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p509 : Nat.Prime 509 :=
  certificate 509 2 [2, 127]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p521 : Nat.Prime 521 :=
  certificate 521 3 [2, 5, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p541 : Nat.Prime 541 :=
  certificate 541 2 [2, 3, 5]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p547 : Nat.Prime 547 :=
  certificate 547 2 [2, 3, 7, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p557 : Nat.Prime 557 :=
  certificate 557 2 [2, 139]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p601 : Nat.Prime 601 :=
  certificate 601 7 [2, 3, 5]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p613 : Nat.Prime 613 :=
  certificate 613 2 [2, 3, 17]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p617 : Nat.Prime 617 :=
  certificate 617 3 [2, 7, 11]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p619 : Nat.Prime 619 :=
  certificate 619 2 [2, 3, 103]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p641 : Nat.Prime 641 :=
  certificate 641 3 [2, 5]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p653 : Nat.Prime 653 :=
  certificate 653 2 [2, 163]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p677 : Nat.Prime 677 :=
  certificate 677 2 [2, 13]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p719 : Nat.Prime 719 :=
  certificate 719 11 [2, 359]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p739 : Nat.Prime 739 :=
  certificate 739 3 [2, 3, 41]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p811 : Nat.Prime 811 :=
  certificate 811 3 [2, 3, 5]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p881 : Nat.Prime 881 :=
  certificate 881 3 [2, 5, 11]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p883 : Nat.Prime 883 :=
  certificate 883 2 [2, 3, 7]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p887 : Nat.Prime 887 :=
  certificate 887 5 [2, 443]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p911 : Nat.Prime 911 :=
  certificate 911 17 [2, 5, 7, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p919 : Nat.Prime 919 :=
  certificate 919 7 [2, 3, 17]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p937 : Nat.Prime 937 :=
  certificate 937 5 [2, 3, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p947 : Nat.Prime 947 :=
  certificate 947 2 [2, 11, 43]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1019 : Nat.Prime 1019 :=
  certificate 1019 2 [2, 509]
    (cons (by decide) (cons p509 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1069 : Nat.Prime 1069 :=
  certificate 1069 6 [2, 3, 89]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1237 : Nat.Prime 1237 :=
  certificate 1237 2 [2, 3, 103]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1249 : Nat.Prime 1249 :=
  certificate 1249 7 [2, 3, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1327 : Nat.Prime 1327 :=
  certificate 1327 3 [2, 3, 13, 17]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1447 : Nat.Prime 1447 :=
  certificate 1447 3 [2, 3, 241]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1511 : Nat.Prime 1511 :=
  certificate 1511 11 [2, 5, 151]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1531 : Nat.Prime 1531 :=
  certificate 1531 2 [2, 3, 5, 17]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1549 : Nat.Prime 1549 :=
  certificate 1549 2 [2, 3, 43]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1627 : Nat.Prime 1627 :=
  certificate 1627 3 [2, 3, 271]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1637 : Nat.Prime 1637 :=
  certificate 1637 2 [2, 409]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1657 : Nat.Prime 1657 :=
  certificate 1657 11 [2, 3, 23]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1823 : Nat.Prime 1823 :=
  certificate 1823 5 [2, 911]
    (cons (by decide) (cons p911 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1831 : Nat.Prime 1831 :=
  certificate 1831 3 [2, 3, 5, 61]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1847 : Nat.Prime 1847 :=
  certificate 1847 5 [2, 13, 71]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1877 : Nat.Prime 1877 :=
  certificate 1877 2 [2, 7, 67]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1949 : Nat.Prime 1949 :=
  certificate 1949 2 [2, 487]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2141 : Nat.Prime 2141 :=
  certificate 2141 2 [2, 5, 107]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2153 : Nat.Prime 2153 :=
  certificate 2153 3 [2, 269]
    (cons (by decide) (cons (by decide) empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2297 : Nat.Prime 2297 :=
  certificate 2297 5 [2, 7, 41]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2383 : Nat.Prime 2383 :=
  certificate 2383 5 [2, 3, 397]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2521 : Nat.Prime 2521 :=
  certificate 2521 17 [2, 3, 5, 7]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2803 : Nat.Prime 2803 :=
  certificate 2803 2 [2, 3, 467]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3019 : Nat.Prime 3019 :=
  certificate 3019 2 [2, 3, 503]
    (cons (by decide) (cons (by decide) (cons p503 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3023 : Nat.Prime 3023 :=
  certificate 3023 5 [2, 1511]
    (cons (by decide) (cons p1511 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3691 : Nat.Prime 3691 :=
  certificate 3691 2 [2, 3, 5, 41]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4057 : Nat.Prime 4057 :=
  certificate 4057 5 [2, 3, 13]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4549 : Nat.Prime 4549 :=
  certificate 4549 6 [2, 3, 379]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p5171 : Nat.Prime 5171 :=
  certificate 5171 2 [2, 5, 11, 47]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p5227 : Nat.Prime 5227 :=
  certificate 5227 2 [2, 3, 13, 67]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p5309 : Nat.Prime 5309 :=
  certificate 5309 2 [2, 1327]
    (cons (by decide) (cons p1327 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p6037 : Nat.Prime 6037 :=
  certificate 6037 5 [2, 3, 503]
    (cons (by decide) (cons (by decide) (cons p503 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p6563 : Nat.Prime 6563 :=
  certificate 6563 5 [2, 17, 193]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p7043 : Nat.Prime 7043 :=
  certificate 7043 2 [2, 7, 503]
    (cons (by decide) (cons (by decide) (cons p503 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p7577 : Nat.Prime 7577 :=
  certificate 7577 3 [2, 947]
    (cons (by decide) (cons p947 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p9109 : Nat.Prime 9109 :=
  certificate 9109 10 [2, 3, 11, 23]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p9539 : Nat.Prime 9539 :=
  certificate 9539 2 [2, 19, 251]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p9661 : Nat.Prime 9661 :=
  certificate 9661 2 [2, 3, 5, 7, 23]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p9859 : Nat.Prime 9859 :=
  certificate 9859 2 [2, 3, 31, 53]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p11083 : Nat.Prime 11083 :=
  certificate 11083 2 [2, 3, 1847]
    (cons (by decide) (cons (by decide) (cons p1847 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p13127 : Nat.Prime 13127 :=
  certificate 13127 5 [2, 6563]
    (cons (by decide) (cons p6563 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p13963 : Nat.Prime 13963 :=
  certificate 13963 3 [2, 3, 13, 179]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p14327 : Nat.Prime 14327 :=
  certificate 14327 5 [2, 13, 19, 29]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p18541 : Nat.Prime 18541 :=
  certificate 18541 6 [2, 3, 5, 103]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p19121 : Nat.Prime 19121 :=
  certificate 19121 6 [2, 5, 239]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p19333 : Nat.Prime 19333 :=
  certificate 19333 2 [2, 3, 179]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p22279 : Nat.Prime 22279 :=
  certificate 22279 3 [2, 3, 47, 79]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p24847 : Nat.Prime 24847 :=
  certificate 24847 3 [2, 3, 41, 101]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p25117 : Nat.Prime 25117 :=
  certificate 25117 5 [2, 3, 7, 13, 23]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p26861 : Nat.Prime 26861 :=
  certificate 26861 2 [2, 5, 17, 79]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p29581 : Nat.Prime 29581 :=
  certificate 29581 10 [2, 3, 5, 17, 29]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p30187 : Nat.Prime 30187 :=
  certificate 30187 5 [2, 3, 13, 43]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p33637 : Nat.Prime 33637 :=
  certificate 33637 2 [2, 3, 2803]
    (cons (by decide) (cons (by decide) (cons p2803 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p36229 : Nat.Prime 36229 :=
  certificate 36229 2 [2, 3, 3019]
    (cons (by decide) (cons (by decide) (cons p3019 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p37021 : Nat.Prime 37021 :=
  certificate 37021 6 [2, 3, 5, 617]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p617 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p37363 : Nat.Prime 37363 :=
  certificate 37363 3 [2, 3, 13, 479]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p42821 : Nat.Prime 42821 :=
  certificate 42821 2 [2, 5, 2141]
    (cons (by decide) (cons (by decide) (cons p2141 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p52967 : Nat.Prime 52967 :=
  certificate 52967 5 [2, 71, 373]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p59723 : Nat.Prime 59723 :=
  certificate 59723 2 [2, 13, 2297]
    (cons (by decide) (cons (by decide) (cons p2297 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p65537 : Nat.Prime 65537 :=
  certificate 65537 3 [2]
    (cons (by decide) empty) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p66499 : Nat.Prime 66499 :=
  certificate 66499 2 [2, 3, 11083]
    (cons (by decide) (cons (by decide) (cons p11083 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p103349 : Nat.Prime 103349 :=
  certificate 103349 3 [2, 7, 3691]
    (cons (by decide) (cons (by decide) (cons p3691 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p104119 : Nat.Prime 104119 :=
  certificate 104119 6 [2, 3, 7, 37, 67]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p106181 : Nat.Prime 106181 :=
  certificate 106181 2 [2, 5, 5309]
    (cons (by decide) (cons (by decide) (cons p5309 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p109897 : Nat.Prime 109897 :=
  certificate 109897 10 [2, 3, 19, 241]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p111317 : Nat.Prime 111317 :=
  certificate 111317 2 [2, 17, 1637]
    (cons (by decide) (cons (by decide) (cons p1637 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p112603 : Nat.Prime 112603 :=
  certificate 112603 2 [2, 3, 7, 383]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p118273 : Nat.Prime 118273 :=
  certificate 118273 5 [2, 3, 7, 11]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p130469 : Nat.Prime 130469 :=
  certificate 130469 2 [2, 13, 193]
    (cons (by decide) (cons (by decide) (cons (by decide) empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p173651 : Nat.Prime 173651 :=
  certificate 173651 2 [2, 5, 23, 151]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p175411 : Nat.Prime 175411 :=
  certificate 175411 2 [2, 3, 5, 1949]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p1949 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p181123 : Nat.Prime 181123 :=
  certificate 181123 3 [2, 3, 30187]
    (cons (by decide) (cons (by decide) (cons p30187 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p183119 : Nat.Prime 183119 :=
  certificate 183119 17 [2, 13, 7043]
    (cons (by decide) (cons (by decide) (cons p7043 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p222127 : Nat.Prime 222127 :=
  certificate 222127 3 [2, 3, 37021]
    (cons (by decide) (cons (by decide) (cons p37021 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p267193 : Nat.Prime 267193 :=
  certificate 267193 5 [2, 3, 1237]
    (cons (by decide) (cons (by decide) (cons p1237 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p273271 : Nat.Prime 273271 :=
  certificate 273271 6 [2, 3, 5, 9109]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p9109 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p294241 : Nat.Prime 294241 :=
  certificate 294241 7 [2, 3, 5, 613]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p613 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p366239 : Nat.Prime 366239 :=
  certificate 366239 11 [2, 183119]
    (cons (by decide) (cons p183119 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p366607 : Nat.Prime 366607 :=
  certificate 366607 3 [2, 3, 31, 73]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p447829 : Nat.Prime 447829 :=
  certificate 447829 2 [2, 3, 67, 557]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p557 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p447859 : Nat.Prime 447859 :=
  certificate 447859 2 [2, 3, 139, 179]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p505231 : Nat.Prime 505231 :=
  certificate 505231 12 [2, 3, 5, 11, 1531]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p1531 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p507289 : Nat.Prime 507289 :=
  certificate 507289 7 [2, 3, 23, 919]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p919 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p524591 : Nat.Prime 524591 :=
  certificate 524591 7 [2, 5, 11, 19, 251]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p571861 : Nat.Prime 571861 :=
  certificate 571861 2 [2, 3, 5, 353]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p629113 : Nat.Prime 629113 :=
  certificate 629113 10 [2, 3, 11, 2383]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p2383 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p675481 : Nat.Prime 675481 :=
  certificate 675481 19 [2, 3, 5, 13, 433]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p704719 : Nat.Prime 704719 :=
  certificate 704719 37 [2, 3, 7, 17, 47]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p918899 : Nat.Prime 918899 :=
  certificate 918899 2 [2, 101, 4549]
    (cons (by decide) (cons (by decide) (cons p4549 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1389209 : Nat.Prime 1389209 :=
  certificate 1389209 3 [2, 173651]
    (cons (by decide) (cons p173651 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2070241 : Nat.Prime 2070241 :=
  certificate 2070241 22 [2, 3, 5, 19, 227]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2127071 : Nat.Prime 2127071 :=
  certificate 2127071 11 [2, 5, 11, 61, 317]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2199643 : Nat.Prime 2199643 :=
  certificate 2199643 2 [2, 3, 366607]
    (cons (by decide) (cons (by decide) (cons p366607 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2360999 : Nat.Prime 2360999 :=
  certificate 2360999 7 [2, 47, 25117]
    (cons (by decide) (cons (by decide) (cons p25117 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2416441 : Nat.Prime 2416441 :=
  certificate 2416441 7 [2, 3, 5, 13, 1549]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p1549 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2464751 : Nat.Prime 2464751 :=
  certificate 2464751 7 [2, 5, 9859]
    (cons (by decide) (cons (by decide) (cons p9859 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2602007 : Nat.Prime 2602007 :=
  certificate 2602007 5 [2, 11, 118273]
    (cons (by decide) (cons (by decide) (cons p118273 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2633783 : Nat.Prime 2633783 :=
  certificate 2633783 5 [2, 53, 24847]
    (cons (by decide) (cons (by decide) (cons p24847 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3029339 : Nat.Prime 3029339 :=
  certificate 3029339 6 [2, 13, 37, 47, 67]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3300263 : Nat.Prime 3300263 :=
  certificate 3300263 7 [2, 7, 19, 653]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p653 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4721999 : Nat.Prime 4721999 :=
  certificate 4721999 7 [2, 2360999]
    (cons (by decide) (cons p2360999 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p6862333 : Nat.Prime 6862333 :=
  certificate 6862333 2 [2, 3, 571861]
    (cons (by decide) (cons (by decide) (cons p571861 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p7549357 : Nat.Prime 7549357 :=
  certificate 7549357 5 [2, 3, 629113]
    (cons (by decide) (cons (by decide) (cons p629113 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p8348773 : Nat.Prime 8348773 :=
  certificate 8348773 5 [2, 3, 53, 13127]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p13127 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p11113673 : Nat.Prime 11113673 :=
  certificate 11113673 3 [2, 1389209]
    (cons (by decide) (cons p1389209 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p14498647 : Nat.Prime 14498647 :=
  certificate 14498647 3 [2, 3, 2416441]
    (cons (by decide) (cons (by decide) (cons p2416441 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p15612043 : Nat.Prime 15612043 :=
  certificate 15612043 2 [2, 3, 2602007]
    (cons (by decide) (cons (by decide) (cons p2602007 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p17354219 : Nat.Prime 17354219 :=
  certificate 17354219 2 [2, 7, 677, 1831]
    (cons (by decide) (cons (by decide) (cons p677 (cons p1831 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p17482847 : Nat.Prime 17482847 :=
  certificate 17482847 5 [2, 67, 130469]
    (cons (by decide) (cons (by decide) (cons p130469 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p19561667 : Nat.Prime 19561667 :=
  certificate 19561667 2 [2, 89, 109897]
    (cons (by decide) (cons (by decide) (cons p109897 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p25605071 : Nat.Prime 25605071 :=
  certificate 25605071 7 [2, 5, 31, 151, 547]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p547 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p29143141 : Nat.Prime 29143141 :=
  certificate 29143141 2 [2, 3, 5, 13, 37363]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p37363 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p42659941 : Nat.Prime 42659941 :=
  certificate 42659941 14 [2, 3, 5, 19, 23, 1627]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p1627 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p52121723 : Nat.Prime 52121723 :=
  certificate 52121723 2 [2, 881, 29581]
    (cons (by decide) (cons p881 (cons p29581 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p57453527 : Nat.Prime 57453527 :=
  certificate 57453527 5 [2, 13, 37, 59723]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p59723 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p100006561 : Nat.Prime 100006561 :=
  certificate 100006561 11 [2, 3, 5, 37, 1877]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p1877 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p104897083 : Nat.Prime 104897083 :=
  certificate 104897083 7 [2, 3, 17482847]
    (cons (by decide) (cons (by decide) (cons p17482847 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p141659971 : Nat.Prime 141659971 :=
  certificate 141659971 2 [2, 3, 5, 4721999]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p4721999 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p352926923 : Nat.Prime 352926923 :=
  certificate 352926923 2 [2, 67, 2633783]
    (cons (by decide) (cons (by decide) (cons p2633783 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p435746497 : Nat.Prime 435746497 :=
  certificate 435746497 5 [2, 3, 53, 42821]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p42821 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p447829001 : Nat.Prime 447829001 :=
  certificate 447829001 3 [2, 5, 447829]
    (cons (by decide) (cons (by decide) (cons p447829 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p476889587 : Nat.Prime 476889587 :=
  certificate 476889587 2 [2, 353, 675481]
    (cons (by decide) (cons (by decide) (cons p675481 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p815730977 : Nat.Prime 815730977 :=
  certificate 815730977 3 [2, 229, 111317]
    (cons (by decide) (cons (by decide) (cons p111317 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p832507937 : Nat.Prime 832507937 :=
  certificate 832507937 5 [2, 13, 59, 107, 317]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p849959827 : Nat.Prime 849959827 :=
  certificate 849959827 2 [2, 3, 141659971]
    (cons (by decide) (cons (by decide) (cons p141659971 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p953975101 : Nat.Prime 953975101 :=
  certificate 953975101 2 [2, 3, 5, 13, 331, 739]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p739 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1475795617 : Nat.Prime 1475795617 :=
  certificate 1475795617 15 [2, 3, 29, 37, 14327]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p14327 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2112660037 : Nat.Prime 2112660037 :=
  certificate 2112660037 5 [2, 3, 19561667]
    (cons (by decide) (cons (by decide) (cons p19561667 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2579667841 : Nat.Prime 2579667841 :=
  certificate 2579667841 19 [2, 3, 5, 447859]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p447859 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3972555259 : Nat.Prime 3972555259 :=
  certificate 3972555259 3 [2, 3, 7, 43, 2199643]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p2199643 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4338014017 : Nat.Prime 4338014017 :=
  certificate 4338014017 5 [2, 3, 7, 31, 104119]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p104119 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p5110698017 : Nat.Prime 5110698017 :=
  certificate 5110698017 3 [2, 719, 222127]
    (cons (by decide) (cons p719 (cons p222127 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p7621509937 : Nat.Prime 7621509937 :=
  certificate 7621509937 5 [2, 3, 313, 507289]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p507289 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p11246831411 : Nat.Prime 11246831411 :=
  certificate 11246831411 2 [2, 5, 23, 149, 307, 1069]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p1069 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p14063687591 : Nat.Prime 14063687591 :=
  certificate 14063687591 14 [2, 5, 97, 14498647]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p14498647 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p17995718017 : Nat.Prime 17995718017 :=
  certificate 17995718017 10 [2, 3, 17, 918899]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p918899 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p25605764801 : Nat.Prime 25605764801 :=
  certificate 25605764801 3 [2, 5, 7, 11, 307, 677]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p677 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p32575757441 : Nat.Prime 32575757441 :=
  certificate 32575757441 3 [2, 5, 23, 79, 109, 257]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p103910985281 : Nat.Prime 103910985281 :=
  certificate 103910985281 3 [2, 5, 619, 524591]
    (cons (by decide) (cons (by decide) (cons p619 (cons p524591 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p110081078977 : Nat.Prime 110081078977 :=
  certificate 110081078977 10 [2, 3, 11, 52121723]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p52121723 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p117051071617 : Nat.Prime 117051071617 :=
  certificate 117051071617 5 [2, 3, 293, 541, 641]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p541 (cons p641 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p152604667841 : Nat.Prime 152604667841 :=
  certificate 152604667841 3 [2, 5, 476889587]
    (cons (by decide) (cons (by decide) (cons p476889587 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p188386299457 : Nat.Prime 188386299457 :=
  certificate 188386299457 5 [2, 3, 23, 42659941]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p42659941 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p225810627617 : Nat.Prime 225810627617 :=
  certificate 225810627617 3 [2, 7, 409, 2464751]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p2464751 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p250110826817 : Nat.Prime 250110826817 :=
  certificate 250110826817 3 [2, 22279, 175411]
    (cons (by decide) (cons p22279 (cons p175411 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p378016357217 : Nat.Prime 378016357217 :=
  certificate 378016357217 3 [2, 23, 19121, 26861]
    (cons (by decide) (cons (by decide) (cons p19121 (cons p26861 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p555122286497 : Nat.Prime 555122286497 :=
  certificate 555122286497 3 [2, 179, 5227, 18541]
    (cons (by decide) (cons (by decide) (cons p5227 (cons p18541 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p673083563041 : Nat.Prime 673083563041 :=
  certificate 673083563041 11 [2, 3, 5, 7, 109, 151, 4057]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p4057 empty))))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p861859264579 : Nat.Prime 861859264579 :=
  certificate 861859264579 3 [2, 3, 13, 849959827]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p849959827 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p907766910977 : Nat.Prime 907766910977 :=
  certificate 907766910977 3 [2, 811, 273271]
    (cons (by decide) (cons p811 (cons p273271 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1252099518401 : Nat.Prime 1252099518401 :=
  certificate 1252099518401 3 [2, 5, 433, 1249, 1447]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p1249 (cons p1447 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1500664960903 : Nat.Prime 1500664960903 :=
  certificate 1500664960903 3 [2, 3, 250110826817]
    (cons (by decide) (cons (by decide) (cons p250110826817 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2068223441377 : Nat.Prime 2068223441377 :=
  certificate 2068223441377 5 [2, 3, 37, 5171, 112603]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p5171 (cons p112603 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p2505920246017 : Nat.Prime 2505920246017 :=
  certificate 2505920246017 5 [2, 3, 11, 19, 15612043]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p15612043 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p3192202523137 : Nat.Prime 3192202523137 :=
  certificate 3192202523137 5 [2, 3, 11, 17, 11113673]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p11113673 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4500380029121 : Nat.Prime 4500380029121 :=
  certificate 4500380029121 3 [2, 5, 14063687591]
    (cons (by decide) (cons (by decide) (cons p14063687591 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p4520690860027 : Nat.Prime 4520690860027 :=
  certificate 4520690860027 2 [2, 3, 11, 43, 211, 7549357]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p7549357 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p5072985298081 : Nat.Prime 5072985298081 :=
  certificate 5072985298081 33 [2, 3, 5, 7, 29, 17354219]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p17354219 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p6002659843613 : Nat.Prime 6002659843613 :=
  certificate 6002659843613 2 [2, 1500664960903]
    (cons (by decide) (cons p1500664960903 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p10066079453921 : Nat.Prime 10066079453921 :=
  certificate 10066079453921 3 [2, 5, 7, 33637, 267193]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p33637 (cons p267193 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p11692495244897 : Nat.Prime 11692495244897 :=
  certificate 11692495244897 3 [2, 937, 2153, 181123]
    (cons (by decide) (cons p937 (cons p2153 (cons p181123 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p11905609260481 : Nat.Prime 11905609260481 :=
  certificate 11905609260481 7 [2, 3, 5, 13, 953975101]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p953975101 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p21370852274017 : Nat.Prime 21370852274017 :=
  certificate 21370852274017 5 [2, 3, 7, 43, 13963, 52967]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p13963 (cons p52967 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p26632396569217 : Nat.Prime 26632396569217 :=
  certificate 26632396569217 7 [2, 3, 641, 1019, 106181]
    (cons (by decide) (cons (by decide) (cons p641 (cons p1019 (cons p106181 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p39079483563041 : Nat.Prime 39079483563041 :=
  certificate 39079483563041 3 [2, 5, 9539, 25605071]
    (cons (by decide) (cons (by decide) (cons p9539 (cons p25605071 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p66607482549857 : Nat.Prime 66607482549857 :=
  certificate 66607482549857 3 [2, 36229, 57453527]
    (cons (by decide) (cons p36229 (cons p57453527 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p80286886568257 : Nat.Prime 80286886568257 :=
  certificate 80286886568257 5 [2, 3, 223, 619, 3029339]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p619 (cons p3029339 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p88081730029121 : Nat.Prime 88081730029121 :=
  certificate 88081730029121 3 [2, 5, 617, 883, 505231]
    (cons (by decide) (cons (by decide) (cons p617 (cons p883 (cons p505231 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p93416589887041 : Nat.Prime 93416589887041 :=
  certificate 93416589887041 13 [2, 3, 5, 7, 53, 29143141]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p29143141 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p97570202611457 : Nat.Prime 97570202611457 :=
  certificate 97570202611457 3 [2, 67, 19333, 294241]
    (cons (by decide) (cons (by decide) (cons p19333 (cons p294241 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p101322190411361 : Nat.Prime 101322190411361 :=
  certificate 101322190411361 3 [2, 5, 6037, 104897083]
    (cons (by decide) (cons (by decide) (cons p6037 (cons p104897083 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p173831026288417 : Nat.Prime 173831026288417 :=
  certificate 173831026288417 5 [2, 3, 7, 23, 11246831411]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p11246831411 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p192085114995617 : Nat.Prime 192085114995617 :=
  certificate 192085114995617 3 [2, 6002659843613]
    (cons (by decide) (cons p6002659843613 empty)) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p230221290411361 : Nat.Prime 230221290411361 :=
  certificate 230221290411361 11 [2, 3, 5, 151, 352926923]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p352926923 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p281481952468097 : Nat.Prime 281481952468097 :=
  certificate 281481952468097 3 [2, 17, 19, 9661, 704719]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons p9661 (cons p704719 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p288424624571297 : Nat.Prime 288424624571297 :=
  certificate 288424624571297 3 [2, 521, 2521, 6862333]
    (cons (by decide) (cons p521 (cons p2521 (cons p6862333 empty)))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p319770394715297 : Nat.Prime 319770394715297 :=
  certificate 319770394715297 3 [2, 7, 1823, 7577, 103349]
    (cons (by decide) (cons (by decide) (cons p1823 (cons p7577 (cons p103349 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p320430606795521 : Nat.Prime 320430606795521 :=
  certificate 320430606795521 3 [2, 5, 13, 43, 447829001]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p447829001 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p393273536839297 : Nat.Prime 393273536839297 :=
  certificate 393273536839297 5 [2, 3, 97, 179, 887, 66499]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p887 (cons p66499 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p415362124464641 : Nat.Prime 415362124464641 :=
  certificate 415362124464641 3 [2, 5, 211, 233, 3300263]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p3300263 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p458569648271617 : Nat.Prime 458569648271617 :=
  certificate 458569648271617 5 [2, 3, 7, 17, 601, 8348773]
    (cons (by decide) (cons (by decide) (cons (by decide) (cons (by decide) (cons p601 (cons p8348773 empty)))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p468851439930977 : Nat.Prime 468851439930977 :=
  certificate 468851439930977 3 [2, 17, 861859264579]
    (cons (by decide) (cons (by decide) (cons p861859264579 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p723310537604321 : Nat.Prime 723310537604321 :=
  certificate 723310537604321 3 [2, 5, 4520690860027]
    (cons (by decide) (cons (by decide) (cons p4520690860027 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p742470842819777 : Nat.Prime 742470842819777 :=
  certificate 742470842819777 5 [2, 7, 503, 1549, 2127071]
    (cons (by decide) (cons (by decide) (cons p503 (cons p1549 (cons p2127071 empty))))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p808245885798977 : Nat.Prime 808245885798977 :=
  certificate 808245885798977 3 [2, 1657, 7621509937]
    (cons (by decide) (cons p1657 (cons p7621509937 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p1537156422138497 : Nat.Prime 1537156422138497 :=
  certificate 1537156422138497 3 [2, 3023, 3972555259]
    (cons (by decide) (cons p3023 (cons p3972555259 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 16000 in
private theorem p24759631977306977 : Nat.Prime 24759631977306977 :=
  certificate 24759631977306977 3 [2, 366239, 2112660037]
    (cons (by decide) (cons p366239 (cons p2112660037 empty))) (by decide) (by decide) (by decide) (by decide) (by decide)

end EighthPowerCertificates

open EighthPowerCertificates

set_option maxRecDepth 16000 in
theorem OMA.solution : OMA.R_OeisA218656_conjecture_3_R1.H1 := by
  intro n hn hu he
  interval_cases n
  · exact ⟨1, by decide, by decide, (by decide)⟩
  · exact ⟨1, by decide, by decide, p65537⟩
  · exact (he (by decide)).elim
  · exact (he (by decide)).elim
  · exact ⟨5, by decide, by decide, p2070241⟩
  · exact ⟨3, by decide, by decide, p100006561⟩
  · exact ⟨2, by decide, by decide, p815730977⟩
  · exact ⟨3, by decide, by decide, p1475795617⟩
  · exact ⟨7, by decide, by decide, p435746497⟩
  · exact ⟨8, by decide, by decide, p832507937⟩
  · exact ⟨8, by decide, by decide, p2579667841⟩
  · exact ⟨9, by decide, by decide, p4338014017⟩
  · exact ⟨7, by decide, by decide, p25605764801⟩
  · exact ⟨13, by decide, by decide, p5110698017⟩
  · exact ⟨7, by decide, by decide, p110081078977⟩
  · exact ⟨8, by decide, by decide, p152604667841⟩
  · exact ⟨17, by decide, by decide, p17995718017⟩
  · exact ⟨17, by decide, by decide, p32575757441⟩
  · exact ⟨11, by decide, by decide, p378016357217⟩
  · exact ⟨17, by decide, by decide, p117051071617⟩
  · exact ⟨20, by decide, by decide, p103910985281⟩
  · exact ⟨19, by decide, by decide, p225810627617⟩
  · exact ⟨23, by decide, by decide, p188386299457⟩
  · exact ⟨19, by decide, by decide, p673083563041⟩
  · exact ⟨22, by decide, by decide, p555122286497⟩
  · exact ⟨22, by decide, by decide, p907766910977⟩
  · exact (he (by decide)).elim
  · exact ⟨25, by decide, by decide, p1252099518401⟩
  · exact ⟨16, by decide, by decide, p11692495244897⟩
  · exact ⟨27, by decide, by decide, p2068223441377⟩
  · exact ⟨25, by decide, by decide, p4500380029121⟩
  · exact ⟨32, by decide, by decide, p2505920246017⟩
  · exact ⟨33, by decide, by decide, p3192202523137⟩
  · exact ⟨19, by decide, by decide, p39079483563041⟩
  · exact ⟨35, by decide, by decide, p5072985298081⟩
  · exact (he (by decide)).elim
  · exact (he (by decide)).elim
  · exact ⟨37, by decide, by decide, p10066079453921⟩
  · exact ⟨39, by decide, by decide, p11905609260481⟩
  · exact ⟨17, by decide, by decide, p281481952468097⟩
  · exact ⟨36, by decide, by decide, p26632396569217⟩
  · exact ⟨42, by decide, by decide, p21370852274017⟩
  · exact ⟨31, by decide, by decide, p97570202611457⟩
  · exact ⟨28, by decide, by decide, p192085114995617⟩
  · exact ⟨38, by decide, by decide, p66607482549857⟩
  · exact ⟨38, by decide, by decide, p88081730029121⟩
  · exact ⟨41, by decide, by decide, p80286886568257⟩
  · exact ⟨42, by decide, by decide, p93416589887041⟩
  · exact ⟨34, by decide, by decide, p320430606795521⟩
  · exact ⟨33, by decide, by decide, p458569648271617⟩
  · exact ⟨50, by decide, by decide, p101322190411361⟩
  · exact (he (by decide)).elim
  · exact ⟨34, by decide, by decide, p808245885798977⟩
  · exact ⟨51, by decide, by decide, p173831026288417⟩
  · exact ⟨43, by decide, by decide, p468851439930977⟩
  · exact ⟨53, by decide, by decide, p230221290411361⟩
  · exact ⟨49, by decide, by decide, p393273536839297⟩
  · exact ⟨56, by decide, by decide, p288424624571297⟩
  · exact ⟨58, by decide, by decide, p319770394715297⟩
  · exact ⟨56, by decide, by decide, p415362124464641⟩
  · exact ⟨11, by decide, by decide, p24759631977306977⟩
  · exact ⟨46, by decide, by decide, p1537156422138497⟩
  · exact ⟨56, by decide, by decide, p742470842819777⟩
  · exact ⟨59, by decide, by decide, p723310537604321⟩
