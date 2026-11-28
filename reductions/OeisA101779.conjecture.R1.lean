import FormalConjectures.OEIS.«101779»

-- Reduction OeisA101779.conjecture.R1 of Conjectures associated with A101779
-- Credit: @MBimrose (agent: hub-swarm-pi)

/-! # A101779: the base cases, and the residue class forced by primality

`Ak n k` says that `k, 2k+1, 3k+2, …, nk+n-1` are all prime.  With `m = k + 1` the `i`-th number is
`i * m - 1`, so the conjecture asks for an `m` making `m-1, 2m-1, …, nm-1` simultaneously prime: a
Dickson-type prime-tuple problem, open for every `n ≥ 6`.

Proved inside this file:
* the whole range `n ≤ 5`, with the witnesses `k = 2, 2, 3, 5, 5`;
* `residue_forced`: for `n ≥ 6` *every* witness `k` satisfies `k % 30 = 29`.  The proof uses only
  the primality of `k`, `2k+1`, `3k+2`, `4k+3`, `5k+4`, `6k+5` modulo `2`, `3` and `5`;
* `residue_form_iff`: consequently, for `n > 8`, existence of a witness is *equivalent* to
  existence of a witness in the single residue class `29 mod 30` (hypothesis H2).  So H2 removes
  five sixths of the search space and loses nothing: no witness can lie outside that class.

Assumed here: H1, the finite range `6 ≤ n ≤ 8`, and H2, the tail `n > 8`.  H1 was verified by
exhaustive search inside the class `29 mod 30` (a complete search by `residue_forced`) for
`k ≤ 3 * 10^6`: the least witnesses `a 6 = 154769`, `a 7 = 2894219`, `a 8 = 2894219` all satisfy
`k % 30 = 29`; the same search finds witnesses for every `n ≤ 8` and none for `n = 9, …, 14` below
that bound, which is why the split is placed at `n = 8`. -/

namespace OMA.R_OeisA101779_conjecture_R1

open OeisA101779

/-- H1: existence of a witness in the finite range `6 ≤ n ≤ 8` (verified by search, see the
header). -/
def H1 : Prop := ∀ n : ℕ, 6 ≤ n → n ≤ 8 → ∃ k : ℕ, Ak n k

/-- H2: the open tail `n > 8`, in the residue class that `residue_forced` shows is forced. -/
def H2 : Prop := ∀ n : ℕ, 8 < n → ∃ k : ℕ, k % 30 = 29 ∧ Ak n k

/- ## The base range `n ≤ 5` -/

theorem ak_one : Ak 1 2 := by decide

theorem ak_two : Ak 2 2 := by decide

theorem ak_three : Ak 3 3 := by decide

theorem ak_four : Ak 4 5 := by decide

theorem ak_five : Ak 5 5 := by decide

/-- `Ak` is monotone in `n`: a witness for `n` is a witness for every smaller `m ≥ 1`. -/
theorem ak_mono {n m k : ℕ} (h : Ak n k) (_hm : 1 ≤ m) (hmn : m ≤ n) : Ak m k :=
  fun i hi him => h i hi (le_trans him hmn)

/- ## Primality facts extracted from `Ak` -/

theorem prime_of_ak {n k : ℕ} (hn : 1 ≤ n) (h : Ak n k) : k.Prime := by
  have h1 := h 1 le_rfl hn
  simpa using h1

theorem prime_two_mul {n k : ℕ} (hn : 2 ≤ n) (h : Ak n k) : (2 * k + 1).Prime := by
  have h2 := h 2 (by norm_num) hn
  simpa using h2

theorem prime_three_mul {n k : ℕ} (hn : 3 ≤ n) (h : Ak n k) : (3 * k + 2).Prime := by
  have h3 := h 3 (by norm_num) hn
  simpa using h3

theorem prime_four_mul {n k : ℕ} (hn : 4 ≤ n) (h : Ak n k) : (4 * k + 3).Prime := by
  have h4 := h 4 (by norm_num) hn
  simpa using h4

theorem prime_five_mul {n k : ℕ} (hn : 5 ≤ n) (h : Ak n k) : (5 * k + 4).Prime := by
  have h5 := h 5 (by norm_num) hn
  simpa using h5

theorem prime_six_mul {n k : ℕ} (hn : 6 ≤ n) (h : Ak n k) : (6 * k + 5).Prime := by
  have h6 := h 6 (by norm_num) hn
  simpa using h6

/-- A prime that is not `2` is odd, so `k` is odd as soon as `n ≥ 3`: the witness `k` itself is
prime, and at `k = 2` the third number `3 * 2 + 2 = 8` is not prime. -/
theorem mod_two_of_ak {n k : ℕ} (hn : 3 ≤ n) (h : Ak n k) : k % 2 = 1 := by
  have hk : k.Prime := prime_of_ak (by omega) h
  have h3 : (3 * k + 2).Prime := prime_three_mul hn h
  rcases hk.eq_two_or_odd with h2 | hodd
  · rw [h2] at h3
    norm_num at h3
  · exact hodd

/-- Modulo `3`: `k ≠ 0` (`k = 3` would make `4*3+3 = 15` composite) and `k ≠ 1` (`k ≡ 1` forces
`3 ∣ 2k+1`, and `2k+1` is a prime `> 3`), hence `k ≡ 2`. -/
theorem mod_three_of_ak {n k : ℕ} (hn : 6 ≤ n) (h : Ak n k) : k % 3 = 2 := by
  have hk : k.Prime := prime_of_ak (by omega) h
  have h2 : (2 * k + 1).Prime := prime_two_mul (by omega) h
  have h4 : (4 * k + 3).Prime := prime_four_mul (by omega) h
  have hne0 : k % 3 ≠ 0 := by
    intro h0
    have hdvd : (3 : ℕ) ∣ k := Nat.dvd_of_mod_eq_zero h0
    have h3k : k = 3 := ((Nat.dvd_prime_two_le hk (by norm_num)).mp hdvd).symm
    rw [h3k] at h4
    norm_num at h4
  have hne1 : k % 3 ≠ 1 := by
    intro h1
    have hdvd : (3 : ℕ) ∣ 2 * k + 1 := by omega
    have h3eq : 3 = 2 * k + 1 := (Nat.dvd_prime_two_le h2 (by norm_num)).mp hdvd
    have hk1 : k = 1 := by omega
    rw [hk1] at hk
    norm_num at hk
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  omega

/-- Modulo `5`: `k ≠ 0` (`k = 5` makes `6*5+5 = 35` composite), `k ≠ 1` (`3k+2` would be a
prime divisible by `5`), `k ≠ 2` (`2k+1` would be `5`, forcing `k = 2`, which fails at `i = 3`)
and `k ≠ 3` (`4k+3` would be a prime divisible by `5`), hence `k ≡ 4`. -/
theorem mod_five_of_ak {n k : ℕ} (hn : 6 ≤ n) (h : Ak n k) : k % 5 = 4 := by
  have hk : k.Prime := prime_of_ak (by omega) h
  have h2 : (2 * k + 1).Prime := prime_two_mul (by omega) h
  have h3 : (3 * k + 2).Prime := prime_three_mul (by omega) h
  have h4 : (4 * k + 3).Prime := prime_four_mul (by omega) h
  have h6 : (6 * k + 5).Prime := prime_six_mul hn h
  have hne0 : k % 5 ≠ 0 := by
    intro h0
    have hdvd : (5 : ℕ) ∣ k := Nat.dvd_of_mod_eq_zero h0
    have h5k : k = 5 := ((Nat.dvd_prime_two_le hk (by norm_num)).mp hdvd).symm
    rw [h5k] at h6
    norm_num at h6
  have hne1 : k % 5 ≠ 1 := by
    intro h1
    have hdvd : (5 : ℕ) ∣ 3 * k + 2 := by omega
    have h5eq : 5 = 3 * k + 2 := (Nat.dvd_prime_two_le h3 (by norm_num)).mp hdvd
    have hk1 : k = 1 := by omega
    rw [hk1] at hk
    norm_num at hk
  have hne2 : k % 5 ≠ 2 := by
    intro h1
    have hdvd : (5 : ℕ) ∣ 2 * k + 1 := by omega
    have h5eq : 5 = 2 * k + 1 := (Nat.dvd_prime_two_le h2 (by norm_num)).mp hdvd
    have hk2 : k = 2 := by omega
    rw [hk2] at h3
    norm_num at h3
  have hne3 : k % 5 ≠ 3 := by
    intro h1
    have hdvd : (5 : ℕ) ∣ 4 * k + 3 := by omega
    have h5eq : 5 = 4 * k + 3 := (Nat.dvd_prime_two_le h4 (by norm_num)).mp hdvd
    omega
  have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The forced residue class.**  For `n ≥ 6` any witness satisfies `k ≡ 29 (mod 30)`: it is odd,
`≡ 2 (mod 3)` and `≡ 4 (mod 5)`, and `29` is the unique class modulo `30` with those residues. -/
theorem residue_forced {n k : ℕ} (hn : 6 ≤ n) (h : Ak n k) : k % 30 = 29 := by
  have h2 := mod_two_of_ak (by omega) h
  have h3 := mod_three_of_ak hn h
  have h5 := mod_five_of_ak hn h
  omega

/-- For `n > 8`, assuming existence of a witness is the same as assuming existence of a witness in
the residue class `29 mod 30`: the forward direction is `residue_forced`, the converse forgets the
class.  This is what makes H2 a lossless form of the open tail. -/
theorem residue_form_iff :
    (∀ n : ℕ, 8 < n → ∃ k : ℕ, Ak n k) ↔ H2 := by
  constructor
  · intro hex n hn
    obtain ⟨k, hk⟩ := hex n hn
    exact ⟨k, residue_forced (by omega) hk, hk⟩
  · rintro h2 n hn
    obtain ⟨k, -, hk⟩ := h2 n hn
    exact ⟨k, hk⟩

theorem main : H1 → H2 → type_of% @OeisA101779.conjecture := by
  intro h1 h2 n hn
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · interval_cases n
    · exact ⟨2, ak_one⟩
    · exact ⟨2, ak_two⟩
    · exact ⟨3, ak_three⟩
    · exact ⟨5, ak_four⟩
    · exact ⟨5, ak_five⟩
  · rcases Nat.lt_or_ge 8 n with h8 | h8le
    · obtain ⟨k, -, hk⟩ := h2 n h8
      exact ⟨k, hk⟩
    · exact h1 n hge h8le

end OMA.R_OeisA101779_conjecture_R1
