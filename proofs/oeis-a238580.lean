import OMAStatements.S_oeis_a238580
import Mathlib

/-!
# A238580: the second part of the conjecture fails at n = 29

For n = 29 (prime(29) = 109) the only k in 1..29 with 2k + 1 and prime(k) * 109 - 2 both prime is
k = 8 (17 and 2069 are prime), so a(29) = 1, while 29 is not in the printed list.
The k-th primes are computed with `Nat.nth_count`.
-/

namespace OMA.Helpers

theorem a238580_nth_of_count {p c : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = c) :
    Nat.nth Nat.Prime c = p := hc ▸ Nat.nth_count hp

theorem a238580_p0 : Nat.nth Nat.Prime 0 = 2 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p1 : Nat.nth Nat.Prime 1 = 3 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p2 : Nat.nth Nat.Prime 2 = 5 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p3 : Nat.nth Nat.Prime 3 = 7 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p4 : Nat.nth Nat.Prime 4 = 11 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p5 : Nat.nth Nat.Prime 5 = 13 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p6 : Nat.nth Nat.Prime 6 = 17 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p7 : Nat.nth Nat.Prime 7 = 19 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p8 : Nat.nth Nat.Prime 8 = 23 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p9 : Nat.nth Nat.Prime 9 = 29 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p10 : Nat.nth Nat.Prime 10 = 31 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p11 : Nat.nth Nat.Prime 11 = 37 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p12 : Nat.nth Nat.Prime 12 = 41 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p13 : Nat.nth Nat.Prime 13 = 43 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p14 : Nat.nth Nat.Prime 14 = 47 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p15 : Nat.nth Nat.Prime 15 = 53 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p16 : Nat.nth Nat.Prime 16 = 59 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p17 : Nat.nth Nat.Prime 17 = 61 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p18 : Nat.nth Nat.Prime 18 = 67 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p19 : Nat.nth Nat.Prime 19 = 71 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p20 : Nat.nth Nat.Prime 20 = 73 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p21 : Nat.nth Nat.Prime 21 = 79 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p22 : Nat.nth Nat.Prime 22 = 83 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p23 : Nat.nth Nat.Prime 23 = 89 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p24 : Nat.nth Nat.Prime 24 = 97 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p25 : Nat.nth Nat.Prime 25 = 101 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p26 : Nat.nth Nat.Prime 26 = 103 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p27 : Nat.nth Nat.Prime 27 = 107 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_p28 : Nat.nth Nat.Prime 28 = 109 :=
  a238580_nth_of_count (by norm_num) (by decide +kernel)

theorem a238580_filter :
    (Finset.Icc 1 29).filter (fun k => (2 * k + 1).Prime ∧
      (OMA.S_oeis_a238580.prime k * OMA.S_oeis_a238580.prime 29 - 2).Prime) = {8} := by
  ext k
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  unfold OMA.S_oeis_a238580.prime
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    interval_cases k <;> first | rfl | (revert h3 h4; norm_num [a238580_p0, a238580_p1, a238580_p2, a238580_p3, a238580_p4, a238580_p5, a238580_p6, a238580_p7, a238580_p8, a238580_p9, a238580_p10, a238580_p11, a238580_p12, a238580_p13, a238580_p14, a238580_p15, a238580_p16, a238580_p17, a238580_p18, a238580_p19, a238580_p20, a238580_p21, a238580_p22, a238580_p23, a238580_p24, a238580_p25, a238580_p26, a238580_p27, a238580_p28])
  · rintro rfl
    norm_num [a238580_p0, a238580_p1, a238580_p2, a238580_p3, a238580_p4, a238580_p5, a238580_p6, a238580_p7, a238580_p8, a238580_p9, a238580_p10, a238580_p11, a238580_p12, a238580_p13, a238580_p14, a238580_p15, a238580_p16, a238580_p17, a238580_p18, a238580_p19, a238580_p20, a238580_p21, a238580_p22, a238580_p23, a238580_p24, a238580_p25, a238580_p26, a238580_p27, a238580_p28]

theorem a238580_a29 : OMA.S_oeis_a238580.a 29 = 1 := by
  unfold OMA.S_oeis_a238580.a
  rw [a238580_filter]
  rfl

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a238580.main) := by
  intro h
  have h29 := h.2 29 (by norm_num) OMA.Helpers.a238580_a29
  revert h29
  decide

