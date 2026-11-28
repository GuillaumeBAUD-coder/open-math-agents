import OMAStatements.S_mo_173510

/-!
# Disproof of `OMA.S_mo_173510.main`

The target statement is imported unchanged from the pinned module
`OMAStatements.S_mo_173510`.  That module's own header records where the statement comes from
and who formalised it; none of it is reproduced, quoted or edited here, and no part of this
file is taken from it.  Everything below is new work: the disproof.

The statement claims that for an arithmetic progression `a₁ + k d` with `d > a₁ ≥ 1` and
`gcd a₁ d = 1`, every term exceeding `φ(d) d²` is either prime or the average of two primes
that are again terms of the progression.

It is false.  Take `a₁ = 4`, `d = 13`, `k = 180`, so the term is `t = 4 + 180 * 13 = 2344`.

* The hypotheses hold: `1 ≤ 4`, `4 < 13`, `Nat.Coprime 4 13`, and
  `φ(13) * 13 ^ 2 = 12 * 169 = 2028 < 2344`, so the hypothesis of the statement applies to `t`.
* `t = 2344 = 2 ^ 3 * 293` is not prime, so the first alternative fails.
* If `p = 4 + 13 i` and `q = 4 + 13 j` are both prime with `p + q = 2 t`, then
  `13 * (i + j) = 4680`, hence `i + j = 360`; so `p + q = 4688` leaves only the `361` splits
  `i + j = 360`, `0 ≤ i ≤ 360`, and in every one of them at least one of the two terms is
  composite.  This is the finite check `key` below, decided in the kernel: for each `i` the
  witness is a divisor `d ≤ 68` of the composite term (a composite number `≤ 4688` has a
  prime factor `≤ √4688 < 69`), which is far cheaper to verify than primality of both terms.
-/

set_option maxRecDepth 100000 in
private theorem key :
    ∀ i : Fin 361,
      ∃ d : Fin 69,
        (2 ≤ (d : ℕ) ∧ (d : ℕ) ∣ 4 + (i : ℕ) * 13 ∧ (d : ℕ) < 4 + (i : ℕ) * 13) ∨
          (2 ≤ (d : ℕ) ∧ (d : ℕ) ∣ 4 + (360 - (i : ℕ)) * 13 ∧
            (d : ℕ) < 4 + (360 - (i : ℕ)) * 13) := by
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_173510.main) := by
  intro h
  have ht : (13).totient * 13 ^ 2 < 4 + 180 * 13 := by decide
  rcases h 4 13 (by norm_num) (by norm_num) (by norm_num) 180 ht with h1 | ⟨i, j, hi, hj, heq⟩
  · norm_num at h1
  · have hij : i + j = 360 := by omega
    have hji : j = 360 - i := by omega
    subst hji
    have hi361 : i < 361 := by omega
    have hval : (↑(⟨i, hi361⟩ : Fin 361) : ℕ) = i := rfl
    have hkey := key ⟨i, hi361⟩
    rw [hval] at hkey
    obtain ⟨d, hd | hd⟩ := hkey
    · obtain ⟨hd2, hddvd, hdlt⟩ := hd
      rcases hi.eq_one_or_self_of_dvd (d : ℕ) hddvd with h | h <;> omega
    · obtain ⟨hd2, hddvd, hdlt⟩ := hd
      rcases hj.eq_one_or_self_of_dvd (d : ℕ) hddvd with h | h <;> omega
