import FormalConjectures.ErdosProblems.«418»

/-!
Browkin and Schinzel: no number `2 ^ (k + 1) * 509203` is of the form `n - φ(n)`.

Write `q = 509203` (a prime) and suppose `n - φ(n) = 2 ^ (k + 1) * q`. Then `n = 2 ^ (a + 1) * m`
with `m` odd, and comparing powers of two leaves two cases.

* `2 * m = 2 ^ (j + 2) * q + φ(m)`. Then `4 ∤ φ(m)`, so `m = p ^ (e + 1)` is a prime power and
  `p ^ e * (p + 1) = 2 ^ (j + 2) * q`. Either `p = 2 ^ (j + 2) * q - 1`, which is never prime
  (`q` is a Riesel number, with covering set `3, 5, 7, 13, 17, 241`), or `p = q` and `q + 1` divides
  a power of two, which it does not.
* `2 * m = 2 * q + φ(m)`. Browkin and Schinzel settle this by a machine search over `q < m < 2 * q`.
  Here the search is organised so that the kernel can run it: `m` is squarefree, and once all prime
  factors of `m` but the largest are fixed, the largest is determined by a division. The function
  `go` walks the tree of those partial factorisations (about eleven thousand nodes).
-/

namespace OMA

/-- Trial division: `comp f d t` is `true` only if `t` has a divisor `e` with `d ≤ e` and
`e * e ≤ t`. The first argument bounds the number of steps. -/
def comp : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, d, t => if t < d * d then false else if t % d = 0 then true else comp f (d + 1) t

lemma comp_sound : ∀ (f d t : ℕ), 2 ≤ d → comp f d t = true → ¬ t.Prime := by
  intro f
  induction f with
  | zero => intro d t _ h; simp [comp] at h
  | succ f ih =>
    intro d t hd h
    simp only [comp] at h
    by_cases h1 : t < d * d
    · simp [h1] at h
    · by_cases h2 : t % d = 0
      · intro hp
        have hdvd : d ∣ t := Nat.dvd_of_mod_eq_zero h2
        rcases (Nat.dvd_prime hp).mp hdvd with h3 | h3
        · omega
        · subst h3
          nlinarith
      · simp only [h1, h2, if_false] at h
        exact ih (d + 1) t (by omega) h

lemma comp_prime (f t : ℕ) (ht : t.Prime) : comp f 2 t = false := by
  by_contra h
  exact comp_sound f 2 t (le_refl 2) (by simpa using h) ht

/-- The last step of the search: all remaining cofactors are primes `R ≥ p`, and such an `R`
satisfies `R * (2 * P - Φ) = 2 * q - Φ`. -/
def fin (P Φ p : ℕ) : Bool :=
  ((1018406 - Φ) % (2 * P - Φ) != 0) ||
    (decide ((1018406 - Φ) / (2 * P - Φ) < p) || comp 1100 2 ((1018406 - Φ) / (2 * P - Φ)))

/-- `go f P Φ p = true` certifies that `2 * P * R = 2 * q + Φ * φ(R)` has no squarefree solution
`R > 1` all of whose prime factors are at least `p`. Here `P` is the product of the primes chosen
so far and `Φ = φ(P)`. -/
def go : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f + 1, P, Φ, p =>
    if 1018406 ≤ P * p * p then fin P Φ p
    else
      (comp 40 2 p ||
        ((2 * P * p != 1018406 + Φ * (p - 1)) && go f (P * p) (Φ * (p - 1)) (p + 1))) &&
      go f P Φ (p + 1)

lemma go_sound : ∀ (f P Φ p : ℕ), go f P Φ p = true → 0 < P → Φ ≤ P →
    ∀ R : ℕ, Squarefree R → 1 < R → p ≤ R.minFac →
      2 * P * R ≠ 1018406 + Φ * R.totient := by
  intro f
  induction f with
  | zero => intro P Φ p h; simp [go] at h
  | succ f ih =>
    intro P Φ p h hP hΦ R hsq hR hp heq
    simp only [go] at h
    have htot : R.totient < R := Nat.totient_lt R hR
    have hPR : P * R < 1018406 := by
      have h1 : Φ * R.totient ≤ P * R.totient := Nat.mul_le_mul_right _ hΦ
      have h2 : P * R.totient < P * R := Nat.mul_lt_mul_of_pos_left htot hP
      have h3 : 2 * P * R = 2 * (P * R) := by ring
      omega
    by_cases hbig : 1018406 ≤ P * p * p
    · rw [if_pos hbig] at h
      have hprime : R.Prime := by
        by_contra hnp
        have h1 : R.minFac ^ 2 ≤ R := Nat.minFac_sq_le_self (by omega) hnp
        have h2 : p * p ≤ R := by nlinarith
        have h3 : P * p * p ≤ P * R := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ h2
        omega
      rw [Nat.totient_prime hprime] at heq
      have e1 : R * (2 * P - Φ) + Φ = 1018406 := by
        obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
        obtain ⟨d, rfl⟩ : ∃ d, P = Φ + d := ⟨P - Φ, by omega⟩
        have h1 : 2 * (Φ + d) - Φ = Φ + 2 * d := by omega
        rw [h1]
        simp only [Nat.add_sub_cancel] at heq
        nlinarith
      have hD : 0 < 2 * P - Φ := by omega
      have e2 : 1018406 - Φ = R * (2 * P - Φ) := by omega
      have hpR : ¬ R < p := by
        rw [Nat.Prime.minFac_eq hprime] at hp
        omega
      simp only [fin, e2, Nat.mul_mod_left, Nat.mul_div_cancel _ hD, comp_prime _ _ hprime] at h
      simp [hpR] at h
    · rw [if_neg hbig, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      by_cases hmf : R.minFac = p
      · have hpp : p.Prime := hmf ▸ Nat.minFac_prime (by omega)
        rw [comp_prime _ _ hpp, Bool.false_or, Bool.and_eq_true] at h1
        obtain ⟨h3, h4⟩ := h1
        have hpd : p ∣ R := hmf ▸ Nat.minFac_dvd R
        obtain ⟨R', rfl⟩ := hpd
        have hpR' : ¬ p ∣ R' := by
          intro hdvd
          have h5 : p * p ∣ p * R' := Nat.mul_dvd_mul_left p hdvd
          exact hpp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p h5))
        have hcop : Nat.Coprime p R' := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpR'
        rw [Nat.totient_mul hcop, Nat.totient_prime hpp] at heq
        have hsq' : Squarefree R' := hsq.of_mul_right
        by_cases hR'1 : R' = 1
        · subst hR'1
          simp only [Nat.totient_one, mul_one] at heq
          simp [heq] at h3
        · have hR'0 : R' ≠ 0 := by
            rintro rfl
            simp at hR
          have hR'gt : 1 < R' := by omega
          have hmf' : p + 1 ≤ R'.minFac := by
            have hq' := Nat.minFac_prime hR'1
            have hdv : R'.minFac ∣ p * R' := Dvd.dvd.mul_left (Nat.minFac_dvd R') p
            have hle : (p * R').minFac ≤ R'.minFac := Nat.minFac_le_of_dvd hq'.two_le hdv
            have hne : R'.minFac ≠ p := fun e => hpR' (e ▸ Nat.minFac_dvd R')
            omega
          refine ih (P * p) (Φ * (p - 1)) (p + 1) h4 (Nat.mul_pos hP hpp.pos)
            (Nat.mul_le_mul hΦ (Nat.sub_le _ _)) R' hsq' hR'gt hmf' ?_
          rw [show 2 * (P * p) * R' = 2 * P * (p * R') by ring, heq]
          ring
      · exact ih P Φ (p + 1) h2 hP hΦ R hsq hR (by omega) heq

lemma go_ok : go 1100 1 1 3 = true := by decide +kernel

lemma q_prime : Nat.Prime 509203 := by norm_num

/-- The base equation has no odd solution. -/
lemma base (m : ℕ) (hodd : Odd m) : 2 * m ≠ 1018406 + m.totient := by
  intro heq
  have hm : 1 < m := by
    rcases m with _ | _ | m
    · simp at hodd
    · simp at heq
    · omega
  have hlt := Nat.totient_lt m hm
  have hsq : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h1 : p ∣ m := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    have h2 : p ∣ m.totient := by
      have h6 : (p * p).totient ∣ m.totient := Nat.totient_dvd_of_dvd hdvd
      rw [← sq, Nat.totient_prime_pow hp (by norm_num)] at h6
      exact Dvd.dvd.trans (Dvd.dvd.mul_right (dvd_pow_self p (by norm_num)) _) h6
    have h3 : p ∣ 2 * 509203 := by
      have h7 : p ∣ 2 * m := Dvd.dvd.mul_left h1 2
      rw [heq] at h7
      exact (Nat.dvd_add_left h2).mp h7
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hodd
      omega
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h5 | h5
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)
    · have h8 := (Nat.prime_dvd_prime_iff_eq hp q_prime).mp h5
      subst h8
      have h9 := Nat.le_of_dvd (by omega) hdvd
      omega
  have hmf : 3 ≤ m.minFac := by
    have h2 := (Nat.minFac_prime (by omega : m ≠ 1)).two_le
    have h3 : m.minFac ≠ 2 := by
      intro h
      have h4 := Nat.minFac_dvd m
      rw [h] at h4
      obtain ⟨c, hc⟩ := hodd
      omega
    omega
  exact go_sound 1100 1 1 3 go_ok (by norm_num) (le_refl 1) m hsq hm hmf (by simpa using heq)

/-- `509203` is a Riesel number: `2 ^ (j + 1) * 509203 - 1` always has a factor among
`3, 5, 7, 13, 17, 241`. -/
lemma riesel (j : ℕ) : ¬ (2 ^ (j + 1) * 509203 - 1).Prime := by
  have key : ∀ r < 24, ∃ d ∈ ([3, 5, 7, 13, 17, 241] : List ℕ),
      1 ≡ 2 ^ r * 509203 [MOD d] := by decide
  have hper : ∀ d ∈ ([3, 5, 7, 13, 17, 241] : List ℕ), 2 ^ 24 ≡ 1 [MOD d] ∧ 2 ≤ d ∧ d ≤ 241 := by
    decide
  obtain ⟨d, hd, hmod⟩ := key ((j + 1) % 24) (Nat.mod_lt _ (by norm_num))
  obtain ⟨h24, hd2, hd241⟩ := hper d hd
  have h1 : 2 ^ (j + 1) ≡ 2 ^ ((j + 1) % 24) [MOD d] := by
    conv_lhs => rw [← Nat.div_add_mod (j + 1) 24, pow_add, pow_mul]
    simpa using (h24.pow ((j + 1) / 24)).mul_right (2 ^ ((j + 1) % 24))
  have h2 : 1 ≡ 2 ^ (j + 1) * 509203 [MOD d] := hmod.trans (h1.mul_right 509203).symm
  have hbig : 2 * 509203 ≤ 2 ^ (j + 1) * 509203 :=
    Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : d ∣ 2 ^ (j + 1) * 509203 - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h2
  intro hp
  rcases (Nat.dvd_prime hp).mp h3 with h4 | h4 <;> omega

/-- An odd number whose totient is not divisible by four is a prime power. -/
lemma prime_pow_of_totient (m : ℕ) (hodd : Odd m) (hm : 1 < m) (h4 : ¬ 4 ∣ m.totient) :
    ∃ p e, p.Prime ∧ m = p ^ (e + 1) := by
  have hpp : m.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, m', hndvd, hmeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) m.minFac hpp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hmeq
    exact hndvd (hmeq ▸ Nat.minFac_dvd m)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  refine ⟨m.minFac, e, hpp, ?_⟩
  by_contra hne
  have hcop : Nat.Coprime (m.minFac ^ (e + 1)) m' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hndvd)
  have hodd2 : Odd (m.minFac ^ (e + 1)) ∧ Odd m' := by
    rw [hmeq] at hodd
    exact Nat.odd_mul.mp hodd
  have hm'1 : m' ≠ 1 := by
    rintro rfl
    exact hne (by simpa using hmeq)
  have hm'3 : 2 < m' := by
    obtain ⟨c, hc⟩ := hodd2.2
    omega
  have hpe3 : 2 < m.minFac ^ (e + 1) := by
    have h1 : 1 < m.minFac ^ (e + 1) := Nat.one_lt_pow (by omega) hpp.one_lt
    obtain ⟨c, hc⟩ := hodd2.1
    omega
  obtain ⟨a, ha⟩ := Nat.totient_even hpe3
  obtain ⟨b, hb⟩ := Nat.totient_even hm'3
  apply h4
  rw [hmeq, Nat.totient_mul hcop, ha, hb]
  exact ⟨a * b, by ring⟩

end OMA

theorem OMA.solution : type_of% @Erdos418.erdos_418.variants.soln := by
  rintro x ⟨k, rfl⟩ ⟨n, hn⟩
  have hbig : 2 * 509203 ≤ 2 ^ (k + 1) * 509203 :=
    Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hle : n.totient ≤ n := Nat.totient_le n
  have heq : n = 2 ^ (k + 1) * 509203 + n.totient := by omega
  have hev : Even n.totient := Nat.totient_even (by omega)
  have hne : Even n := by
    rw [heq]
    exact Even.add (Even.mul_right (Nat.even_pow.mpr ⟨even_two, by omega⟩) _) hev
  obtain ⟨a, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hnm
    rw [hnm] at hne
    exact (Nat.not_even_iff_odd.mpr hmodd) hne
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  have hcop : Nat.Coprime (2 ^ (a + 1)) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd)
  have htot : n.totient = 2 ^ a * m.totient := by
    rw [hnm, Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  rw [htot, hnm] at heq
  -- heq : 2 ^ (a + 1) * m = 2 ^ (k + 1) * 509203 + 2 ^ a * φ(m)
  have hm0 : 0 < m := by
    obtain ⟨c, hc⟩ := hmodd
    omega
  by_cases hm1 : m = 1
  · subst hm1
    have h1 : 2 ^ a = 2 ^ (k + 1) * 509203 := by
      simp only [Nat.totient_one, mul_one, pow_succ] at heq
      simp only [pow_succ]
      omega
    have h2 : 509203 ∣ 2 ^ a := Dvd.intro_left _ h1.symm
    have h3 := Nat.le_of_dvd (by norm_num) (OMA.q_prime.dvd_of_dvd_pow h2)
    omega
  · have hm3 : 2 < m := by
      obtain ⟨c, hc⟩ := hmodd
      omega
    obtain ⟨c, hc⟩ := Nat.totient_even hm3
    rcases Nat.lt_or_ge k a with hka | hak
    · -- too many twos on the left: `509203` would be even
      obtain ⟨i, rfl⟩ : ∃ i, a = k + 1 + i := ⟨a - (k + 1), by omega⟩
      have h1 : 2 ^ (k + 1) * (2 ^ (i + 1) * m) =
          2 ^ (k + 1) * (509203 + 2 ^ (i + 1) * c) := by
        rw [hc] at heq
        have e1 : 2 ^ (k + 1 + i + 1) * m = 2 ^ (k + 1) * (2 ^ (i + 1) * m) := by ring
        have e2 : 2 ^ (k + 1 + i) * (c + c) = 2 ^ (k + 1) * (2 ^ (i + 1) * c) := by ring
        rw [e1, e2] at heq
        rw [heq]
        ring
      have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
      obtain ⟨u, hu⟩ : 2 ∣ 2 ^ (i + 1) * m := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) m
      obtain ⟨v, hv⟩ : 2 ∣ 2 ^ (i + 1) * c := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) c
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = a + j := ⟨k - a, by omega⟩
      have h1 : 2 ^ (a + 1) * m = 2 ^ (a + 1) * (2 ^ j * 509203 + c) := by
        rw [hc] at heq
        have e2 : 2 ^ a * (c + c) = 2 ^ (a + 1) * c := by ring
        rw [e2] at heq
        rw [heq]
        ring
      have h2 : m = 2 ^ j * 509203 + c := Nat.eq_of_mul_eq_mul_left (by positivity) h1
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact OMA.base m hmodd (by omega)
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        -- `c` is odd, so `4 ∤ φ(m)` and `m` is a prime power
        have h4 : ¬ 4 ∣ m.totient := by
          rintro ⟨w, hw⟩
          obtain ⟨u, hu⟩ : 2 ∣ 2 ^ (j + 1) * 509203 :=
            Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
          obtain ⟨s, hs⟩ := hmodd
          omega
        obtain ⟨p, e, hp, rfl⟩ := OMA.prime_pow_of_totient m hmodd (by omega) h4
        rw [Nat.totient_prime_pow hp (by omega), Nat.add_sub_cancel] at hc
        have hp1 : 1 ≤ p := hp.one_le
        -- `p ^ e * (p + 1) = 2 ^ (j + 2) * 509203`
        have h5 : p ^ e * (p + 1) = 2 ^ (j + 2) * 509203 := by
          obtain ⟨t, rfl⟩ : ∃ t, p = t + 1 := ⟨p - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hc
          have e3 : (t + 1) ^ (e + 1) = (t + 1) ^ e * t + (t + 1) ^ e := by ring
          have e4 : (t + 1) ^ e * (t + 1 + 1) = (t + 1) ^ e * t + 2 * (t + 1) ^ e := by ring
          have e5 : 2 ^ (j + 2) * 509203 = 2 * (2 ^ (j + 1) * 509203) := by ring
          rw [e3] at h2
          rw [e4, e5]
          omega
        have hpodd : p ≠ 2 := by
          rintro rfl
          have h6 : Even (2 ^ (e + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
          exact (Nat.not_even_iff_odd.mpr hmodd) h6
        rcases Nat.eq_zero_or_pos e with rfl | he
        · rw [pow_zero, one_mul] at h5
          have h6 : p = 2 ^ (j + 2) * 509203 - 1 := by omega
          rw [h6] at hp
          exact OMA.riesel (j + 1) hp
        · obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
          have h6 : p ∣ 2 ^ (j + 2) * 509203 :=
            Dvd.intro _ (by rw [← h5]; ring : p * (p ^ e * (p + 1)) = _)
          rcases (Nat.Prime.dvd_mul hp).mp h6 with h7 | h7
          · exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h7))
          · have h8 := (Nat.prime_dvd_prime_iff_eq hp OMA.q_prime).mp h7
            subst h8
            have h9 : 509203 * (509203 ^ e * 509204) = 509203 * 2 ^ (j + 2) := by
              rw [← mul_comm (2 ^ (j + 2)), ← h5]
              ring
            have h10 : 509203 ^ e * 509204 = 2 ^ (j + 2) :=
              Nat.eq_of_mul_eq_mul_left (by norm_num) h9
            have h11 : 127301 ∣ 2 ^ (j + 2) :=
              Dvd.intro_left (509203 ^ e * 4) (by rw [← h10]; ring)
            have h12 : Nat.Coprime 127301 (2 ^ (j + 2)) :=
              Nat.Coprime.pow_right _ (by norm_num)
            have h13 := Nat.Coprime.eq_one_of_dvd h12 h11
            omega
