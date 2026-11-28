import OMAStatements.S_oeis_a140831
import Mathlib.Tactic

-- Credit: @Denyven

namespace OMA.S_oeis_a140831

private theorem inversion_of_prime_powers {n p q : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpow : q < p ^ 2)
    (hpd : p ^ 2 ∣ n) (hqd : q ∣ n) (hqnd : ¬ q ^ 2 ∣ n) : inversion n := by
  have hpev := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpd
  have hqev := (hq.dvd_iff_one_le_factorization hn.ne').mp hqd
  have hqevLt : n.factorization q < 2 :=
    lt_of_not_ge (mt (hq.pow_dvd_iff_le_factorization hn.ne').mpr hqnd)
  have hqevEq : n.factorization q = 1 := by omega
  refine ⟨hn, p, q, hp, hq, hpq, dvd_trans (dvd_pow_self p (by decide)) hpd, hqd, ?_⟩
  rw [hqevEq, pow_one]
  exact hpow.trans_le (pow_le_pow_right' hp.one_le hpev)

end OMA.S_oeis_a140831

theorem OMA.solution : type_of% @OMA.S_oeis_a140831.main := by
  -- The progression fixes the exponents of 3 in k and of 7 in k + 1 at one.
  -- At the same time 4 divides k and 25 divides k + 1.
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 3324 + 44100 * t)
    (by
      intro a b hab
      change 3324 + 44100 * a = 3324 + 44100 * b at hab
      omega) ?_
  intro t
  change OMA.S_oeis_a140831.inversion (3324 + 44100 * t) ∧
    OMA.S_oeis_a140831.inversion (3324 + 44100 * t + 1)
  constructor
  · apply OMA.S_oeis_a140831.inversion_of_prime_powers (p := 2) (q := 3)
      (by omega) (by decide) (by decide) (by decide) (by decide)
    · change 4 ∣ 3324 + 44100 * t
      omega
    · omega
    · change ¬ 9 ∣ 3324 + 44100 * t
      omega
  · apply OMA.S_oeis_a140831.inversion_of_prime_powers (p := 5) (q := 7)
      (by omega) (by decide) (by decide) (by decide) (by decide)
    · change 25 ∣ 3324 + 44100 * t + 1
      omega
    · omega
    · change ¬ 49 ∣ 3324 + 44100 * t + 1
      omega
