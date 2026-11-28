import OMAReductions.R_OeisA234246_conjecture_3_R1

/-!
# Proof of `OeisA234246.conjecture_3.R1.H1`

Proves that for every `n` with `60 ≤ n < 2 ^ 20`, there exists `k` with `0 < k < n` such that
`IsSquare (k + (n - k).totient)`.

For any `n ∈ [60, 2 ^ 20)`, let `s = n.sqrt`. Exactly one of `r ∈ {s, s - 1, s - 2}` yields an
odd gap `d = n - r ^ 2` with `7 ≤ d ≤ 4 * s + 1 < 4100`. A precomputed Goldbach list `goldList`
supplies distinct primes `p < q` with `p + q = d + 1` for every even `e = d + 1 ∈ [8, 4100]`.
- Whenever `p * q < n`, `OMA.R_OeisA234246_conjecture_3_R1.witness` and `totient_product`
  immediately give `k = n - p * q` with `k + (n - k).totient = r ^ 2`.
- Otherwise `n ≤ p * q` and `r ≥ (e - 9) / 4`, which leaves only 212 exception
  values `n` stored in a balanced binary search tree `excTree` with explicit witnesses verified
  in O(N) by `decide +kernel`.
-/

namespace OeisA234246R1H1Proof

private def hasDiv : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | n, d, f + 1 =>
    if d * d > n then false
    else if n % d == 0 then true
    else hasDiv n (d + 1) f

private lemma hasDiv_false_iff (n : ℕ) :
    ∀ f d : ℕ, 2 ≤ d → hasDiv n d f = false →
      ∀ k : ℕ, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _; omega
  | succ f ih =>
    intro d hd hfalse k hdk hklt hsq hdvd
    unfold hasDiv at hfalse
    by_cases hgt : d * d > n
    · have : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      omega
    · simp only [hgt, ↓reduceIte] at hfalse
      by_cases hmod : n % d = 0
      · have : (n % d == 0) = true := by simp [hmod]
        rw [this] at hfalse; simp at hfalse
      · have hbmod : (n % d == 0) = false := by simp [hmod]
        rw [hbmod] at hfalse; simp only [Bool.false_eq_true, ↓reduceIte] at hfalse
        by_cases hkd : k = d
        · subst hkd; exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 1) (by omega) hfalse k (by omega) (by omega) hsq hdvd

private def isPrimeSmall (n : ℕ) : Bool :=
  2 ≤ n && !hasDiv n 2 70

private lemma prime_of_isPrimeSmall {n : ℕ} (h : isPrimeSmall n = true) (hle : n ≤ 4900) :
    n.Prime := by
  unfold isPrimeSmall at h
  rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rw [Nat.prime_def_lt']
  refine ⟨h.1, fun m hm1 hmn hdvd => ?_⟩
  rcases le_or_gt (m * m) n with hsq | hgt
  · have hmlt : m < 72 := by nlinarith
    exact hasDiv_false_iff n 70 2 (by decide) h.2 m hm1 hmlt hsq hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      by_contra hlt; have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> nlinarith
    have hksq : k * k ≤ n := by nlinarith
    have hklt : k < 72 := by nlinarith
    exact hasDiv_false_iff n 70 2 (by decide) h.2 k hk2 hklt hksq ⟨m, by linarith⟩

private def goldList : List ℕ := [
  3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13,
  19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5,
  7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5,
  7, 11, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13,
  31, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 3, 5, 7, 29, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 3, 5,
  7, 11, 11, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7,
  31, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 3, 5,
  7, 3, 5, 7, 47, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5,
  7, 11, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7,
  19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13,
  19, 3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7,
  19, 11, 13, 31, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19,
  31, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13,
  31, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 73, 3, 5, 7, 3, 5, 7, 23, 11, 13, 3, 5, 3, 5, 7, 3, 3, 5,
  7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17,
  19, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11, 13, 41, 17,
  19, 41, 23, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31, 3, 5,
  7, 17, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5, 7, 29, 11, 3, 5, 7,
  19, 11, 13, 37, 17, 19, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 3, 3, 5,
  7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23, 31, 47, 29, 31, 41, 41, 3, 5, 7, 3, 5, 7, 3, 5, 7, 61, 3, 5,
  7, 17, 11, 13, 23, 17, 19, 3, 5, 7, 41, 11, 3, 5, 7, 19, 11, 13, 43, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 3, 5, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5, 7, 29, 11, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 11, 13, 3, 5, 7, 31, 11, 13, 3, 5, 7, 43, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 5, 7, 3, 3, 5, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 7, 17, 11, 3, 5, 7, 19, 11, 13, 31, 17, 19, 31, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17,
  19, 23, 23, 31, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5,
  7, 3, 5, 7, 3, 5, 7, 3, 5, 7, 47, 11, 13, 41, 17, 19, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5,
  7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7, 31, 3, 5, 7, 17, 11, 13, 23, 17, 3, 5, 7, 67, 11, 13, 31, 3, 5,
  7, 3, 5, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13,
  61, 17, 19, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 3, 5, 7, 3, 5, 7,
  37, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 7, 23, 11, 3, 3, 5, 7, 11, 11, 3, 5, 7,
  19, 11, 13, 37, 3, 5, 7, 23, 11, 3, 5, 7, 3, 5, 7, 61, 11, 13, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7,
  19, 11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5,
  7, 17, 11, 13, 23, 17, 19, 3, 5, 7, 47, 11, 13, 41, 17, 19, 47, 23, 43, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5,
  7, 17, 11, 13, 23, 17, 3, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 13, 23, 17, 3, 3, 5, 3, 5, 7, 13, 3, 5,
  7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 31, 3, 5, 7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 11, 13, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13, 61, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3, 5, 7,
  31, 3, 5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 31, 23, 29, 31, 3, 5, 7, 53, 11, 13, 41, 17, 19, 3, 5,
  7, 53, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23, 3, 5, 7,
  31, 11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 5, 7, 61, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7, 103, 11, 13,
  31, 3, 5, 7, 23, 11, 3, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7,
  19, 3, 5, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 13, 11, 13,
  19, 3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 5, 7,
  31, 11, 13, 31, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 3, 5, 7,
  31, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31, 3, 5, 7, 17, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7,
  31, 11, 13, 37, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 43, 29, 29, 3, 3, 5,
  7, 11, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 13, 3, 5,
  7, 3, 5, 7, 53, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 37, 17, 19, 31, 3, 5, 7, 29, 11, 3, 3, 5,
  7, 11, 11, 13, 17, 17, 3, 5, 7, 37, 11, 13, 31, 17, 19, 37, 23, 41, 43, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5,
  7, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7, 3, 5, 7, 31, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 13, 23, 17,
  19, 29, 23, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 29, 17, 19, 41, 23, 37, 41, 29, 3, 3, 5,
  7, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 13, 11, 13, 3, 3, 5,
  7, 11, 11, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 3, 5, 7, 11, 11, 13, 17, 17, 3, 5, 7, 3, 5, 7, 31, 11, 13,
  37, 17, 19, 43, 3, 5, 7, 29, 11, 13, 41, 17, 3, 5, 7, 67, 3, 5, 3, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17,
  19, 23, 23, 3, 5, 7, 31, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 7, 59, 11, 3, 3, 5, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13,
  37, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11, 13, 41, 17, 3, 5, 7,
  31, 11, 13, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 5, 7,
  19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11, 13, 53, 17, 19, 41, 23, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 5, 7,
  19, 11, 13, 61, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 79, 17, 19, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13,
  79, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 13, 23, 17,
  19, 3, 5, 3, 5, 7, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19,
  37, 3, 5, 7, 29, 11, 13, 53, 17, 19, 41, 23, 3, 5, 7, 31, 11, 13, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5,
  7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 3, 5, 7, 3, 5, 7,
  31, 11, 13, 3, 3, 5, 7
]

private lemma goldList_length : goldList.length = 2047 := by decide +kernel

private def checkGoldPair (e p : ℕ) : Bool :=
  let q := e - p
  p < q && isPrimeSmall p && isPrimeSmall q

private def checkGoldList (e : ℕ) : List ℕ → Bool
  | [] => true
  | p :: rest => checkGoldPair e p && checkGoldList (e + 2) rest

private lemma checkGoldList_sound : ∀ (l : List ℕ) (e : ℕ),
    checkGoldList e l = true →
    ∀ (i : ℕ) (hi : i < l.length), checkGoldPair (e + 2 * i) (l[i]'hi) = true := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons p rest ih =>
    intro e h i hi
    unfold checkGoldList at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have hj : j < rest.length := by simpa using hi
      have hres := ih (e + 2) h.2 j hj
      simpa [show e + 2 + 2 * j = e + 2 * (j + 1) by omega] using hres

private lemma checkGoldList_ok : checkGoldList 8 goldList = true := by decide +kernel

private def facProd : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: rest => p ^ e * facProd rest

private def facPhi : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: rest => p ^ (e - 1) * (p - 1) * facPhi rest

private def facValid (prev : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, e) :: rest =>
    prev < p && 1 ≤ e && isPrimeSmall p && facValid p rest

private lemma facProd_coprime : ∀ (prev : ℕ) (l : List (ℕ × ℕ)),
    facValid prev l = true → (∀ x ∈ l, x.1 ≤ 4900) →
    ∀ q : ℕ, q.Prime → q ≤ prev → q.Coprime (facProd l) := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _ _ _ _ _; simp [facProd]
  | cons hd tl ih =>
    rcases hd with ⟨p, e⟩
    intro hv hle q hq hqp
    unfold facValid at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨hlt, he⟩, hp_b⟩, htl⟩
    have hp : p.Prime := prime_of_isPrimeSmall hp_b (hle (p, e) (List.mem_cons_self ..))
    have hcop_pq : q.Coprime p := (Nat.coprime_primes hq hp).mpr (by omega)
    have hcop_tl : q.Coprime (facProd tl) :=
      ih p htl (fun x hx => hle x (List.mem_cons_of_mem _ hx)) q hq (by omega)
    unfold facProd
    exact (hcop_pq.pow_right e).mul_right hcop_tl

private lemma facPhi_eq_totient : ∀ (prev : ℕ) (l : List (ℕ × ℕ)),
    facValid prev l = true → (∀ x ∈ l, x.1 ≤ 4900) →
    (facProd l).totient = facPhi l := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _ _; simp [facProd, facPhi]
  | cons hd tl ih =>
    rcases hd with ⟨p, e⟩
    intro hv hle
    unfold facValid at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases hv with ⟨⟨⟨hlt, he⟩, hp_b⟩, htl⟩
    have hp : p.Prime := prime_of_isPrimeSmall hp_b (hle (p, e) (List.mem_cons_self ..))
    have hcop : (p ^ e).Coprime (facProd tl) :=
      (facProd_coprime p tl htl (fun x hx => hle x (List.mem_cons_of_mem _ hx)) p hp (le_refl p)).pow_left e
    unfold facProd facPhi
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp he,
      ih p htl (fun x hx => hle x (List.mem_cons_of_mem _ hx))]

private inductive ExcWit where
  | pq (r p q : ℕ)
  | fac (m r : ℕ) (facs : List (ℕ × ℕ))

private inductive ExcTree where
  | leaf
  | node (key : ℕ) (w : ExcWit) (left right : ExcTree)

private def checkWit (n : ℕ) : ExcWit → Bool
  | .pq r p q =>
    p < q && p ≤ 4900 && q ≤ 4900 && isPrimeSmall p && isPrimeSmall q &&
      p * q < n && n == r * r + p + q - 1
  | .fac m r facs =>
    0 < m && m < n && facValid 1 facs && facs.all (fun x => x.1 ≤ 4900) &&
      facProd facs == m && (n - m) + facPhi facs == r * r

private lemma solve_of_checkWit {n : ℕ} {w : ExcWit} (h : checkWit n w = true) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k + (n - k).totient) := by
  cases w with
  | pq r p q =>
    unfold checkWit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨hpq, hple⟩, hqle⟩, hpp⟩, hqp⟩, hmul⟩, hneq⟩
    have hp' : p.Prime := prime_of_isPrimeSmall hpp hple
    have hq' : q.Prime := prime_of_isPrimeSmall hqp hqle
    have htot := OMA.R_OeisA234246_conjecture_3_R1.totient_product hp' hq' (by omega)
    exact OMA.R_OeisA234246_conjecture_3_R1.witness (r := r) (Nat.mul_pos hp'.pos hq'.pos) hmul (by omega)
  | fac m r facs =>
    unfold checkWit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨hm0, hmn⟩, hfv⟩, hfle⟩, hfp⟩, hsq⟩
    have htot : m.totient = facPhi facs := by
      rw [← hfp]
      exact facPhi_eq_totient 1 facs hfv (fun x hx => hfle x hx)
    refine ⟨n - m, by omega, by omega, r, ?_⟩
    rw [show n - (n - m) = m by omega, htot]
    omega

private def excTree : ExcTree :=
  (ExcTree.node 1149 (ExcWit.fac 84 33 [(2, 2), (3, 1), (7, 1)]) (ExcTree.node 249 (ExcWit.fac 36 15 [(2, 2), (3, 2)]) (ExcTree.node 122 (ExcWit.fac 2 11 [(2, 1)]) (ExcTree.node 87 (ExcWit.fac 10 9 [(2, 1), (5, 1)]) (ExcTree.node 72 (ExcWit.fac 12 8 [(2, 2), (3, 1)]) (ExcTree.node 67 (ExcWit.fac 9 8 [(3, 2)]) (ExcTree.node 63 (ExcWit.fac 26 7 [(2, 1), (13, 1)]) (ExcTree.node 61 (ExcWit.fac 18 7 [(2, 1), (3, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 65 (ExcWit.fac 2 8 [(2, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 71 (ExcWit.pq 8 3 5) (ExcTree.node 69 (ExcWit.fac 25 8 [(5, 2)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 82 (ExcWit.fac 2 9 [(2, 1)]) (ExcTree.node 78 (ExcWit.fac 26 8 [(2, 1), (13, 1)]) (ExcTree.node 76 (ExcWit.fac 18 8 [(2, 1), (3, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 80 (ExcWit.fac 24 8 [(2, 3), (3, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 86 (ExcWit.fac 25 9 [(5, 2)]) (ExcTree.node 84 (ExcWit.fac 9 9 [(3, 2)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 105 (ExcWit.fac 25 10 [(5, 2)]) (ExcTree.node 99 (ExcWit.fac 34 9 [(2, 1), (17, 1)]) (ExcTree.node 91 (ExcWit.fac 63 8 [(3, 2), (7, 1)]) (ExcTree.node 88 (ExcWit.pq 9 3 5) ExcTree.leaf ExcTree.leaf) (ExcTree.node 93 (ExcWit.fac 18 9 [(2, 1), (3, 2)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 103 (ExcWit.fac 9 10 [(3, 2)]) (ExcTree.node 101 (ExcWit.fac 2 10 [(2, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 110 (ExcWit.fac 66 8 [(2, 1), (3, 1), (11, 1)]) (ExcTree.node 108 (ExcWit.fac 12 10 [(2, 2), (3, 1)]) (ExcTree.node 107 (ExcWit.pq 10 3 5) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 118 (ExcWit.fac 34 10 [(2, 1), (17, 1)]) (ExcTree.node 116 (ExcWit.fac 24 10 [(2, 3), (3, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))) (ExcTree.node 174 (ExcWit.fac 25 13 [(5, 2)]) (ExcTree.node 147 (ExcWit.fac 9 12 [(3, 2)]) (ExcTree.node 135 (ExcWit.fac 26 11 [(2, 1), (13, 1)]) (ExcTree.node 128 (ExcWit.pq 11 3 5) (ExcTree.node 126 (ExcWit.fac 25 11 [(5, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 129 (ExcWit.fac 12 11 [(2, 2), (3, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 141 (ExcWit.fac 38 11 [(2, 1), (19, 1)]) (ExcTree.node 137 (ExcWit.fac 24 11 [(2, 3), (3, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 162 (ExcWit.fac 34 12 [(2, 1), (17, 1)]) (ExcTree.node 151 (ExcWit.pq 12 3 5) (ExcTree.node 150 (ExcWit.fac 10 12 [(2, 1), (5, 1)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 158 (ExcWit.fac 26 12 [(2, 1), (13, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 172 (ExcWit.fac 9 13 [(3, 2)]) (ExcTree.node 168 (ExcWit.fac 36 12 [(2, 2), (3, 2)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 203 (ExcWit.pq 14 3 5) (ExcTree.node 195 (ExcWit.fac 146 11 [(2, 1), (73, 1)]) (ExcTree.node 185 (ExcWit.fac 24 13 [(2, 3), (3, 1)]) (ExcTree.node 181 (ExcWit.fac 18 13 [(2, 1), (3, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 191 (ExcWit.fac 30 13 [(2, 1), (3, 1), (5, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 201 (ExcWit.fac 25 14 [(5, 2)]) (ExcTree.node 197 (ExcWit.fac 2 14 [(2, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 222 (ExcWit.fac 114 12 [(2, 1), (3, 1), (19, 1)]) (ExcTree.node 220 (ExcWit.fac 36 14 [(2, 2), (3, 2)]) (ExcTree.node 206 (ExcWit.fac 122 12 [(2, 1), (61, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 228 (ExcWit.fac 9 15 [(3, 2)]) (ExcTree.node 226 (ExcWit.fac 2 15 [(2, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))))) (ExcTree.node 626 (ExcWit.fac 2 25 [(2, 1)]) (ExcTree.node 348 (ExcWit.fac 36 18 [(2, 2), (3, 2)]) (ExcTree.node 290 (ExcWit.fac 2 17 [(2, 1)]) (ExcTree.node 263 (ExcWit.pq 16 3 5) (ExcTree.node 255 (ExcWit.fac 42 15 [(2, 1), (3, 1), (7, 1)]) (ExcTree.node 253 (ExcWit.fac 52 15 [(2, 2), (13, 1)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 261 (ExcWit.fac 25 16 [(5, 2)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 284 (ExcWit.fac 52 16 [(2, 2), (13, 1)]) (ExcTree.node 278 (ExcWit.fac 30 16 [(2, 1), (3, 1), (5, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 315 (ExcWit.fac 126 15 [(2, 1), (3, 2), (7, 1)]) (ExcTree.node 296 (ExcWit.pq 17 3 5) (ExcTree.node 292 (ExcWit.fac 9 17 [(3, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 309 (ExcWit.fac 38 17 [(2, 1), (19, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 327 (ExcWit.fac 9 18 [(3, 2)]) (ExcTree.node 323 (ExcWit.fac 194 15 [(2, 1), (97, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 489 (ExcWit.fac 25 22 [(5, 2)]) (ExcTree.node 403 (ExcWit.fac 9 20 [(3, 2)]) (ExcTree.node 368 (ExcWit.pq 19 3 5) (ExcTree.node 356 (ExcWit.fac 48 18 [(2, 4), (3, 1)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 391 (ExcWit.fac 42 19 [(2, 1), (3, 1), (7, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 479 (ExcWit.fac 74 21 [(2, 1), (37, 1)]) (ExcTree.node 440 (ExcWit.fac 76 20 [(2, 2), (19, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 573 (ExcWit.fac 60 23 [(2, 2), (3, 1), (5, 1)]) (ExcTree.node 536 (ExcWit.pq 23 3 5) (ExcTree.node 530 (ExcWit.pq 19 3 167) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 581 (ExcWit.pq 20 3 179) (ExcTree.node 579 (ExcWit.fac 9 24 [(3, 2)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))) (ExcTree.node 997 (ExcWit.pq 28 3 211) (ExcTree.node 907 (ExcWit.pq 30 3 5) (ExcTree.node 826 (ExcWit.pq 25 3 199) (ExcTree.node 722 (ExcWit.pq 23 3 191) (ExcTree.node 673 (ExcWit.fac 72 25 [(2, 3), (3, 2)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 773 (ExcWit.fac 60 27 [(2, 2), (3, 1), (5, 1)]) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 905 (ExcWit.pq 26 3 227) (ExcTree.node 881 (ExcWit.fac 76 29 [(2, 2), (19, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 964 (ExcWit.pq 27 3 233) (ExcTree.node 962 (ExcWit.fac 2 31 [(2, 1)]) (ExcTree.node 938 (ExcWit.pq 25 3 311) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 968 (ExcWit.pq 31 3 5) (ExcTree.node 966 (ExcWit.fac 25 31 [(5, 2)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 1084 (ExcWit.pq 29 3 241) (ExcTree.node 1027 (ExcWit.pq 28 3 241) (ExcTree.node 1023 (ExcWit.fac 122 31 [(2, 1), (61, 1)]) (ExcTree.node 1021 (ExcWit.fac 84 31 [(2, 2), (3, 1), (7, 1)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 1025 (ExcWit.pq 28 3 239) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 1082 (ExcWit.pq 29 3 239) (ExcTree.node 1058 (ExcWit.fac 266 30 [(2, 1), (7, 1), (19, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 1121 (ExcWit.fac 48 33 [(2, 4), (3, 1)]) (ExcTree.node 1088 (ExcWit.fac 96 32 [(2, 5), (3, 1)]) (ExcTree.node 1086 (ExcWit.fac 122 32 [(2, 1), (61, 1)]) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 1147 (ExcWit.fac 578 29 [(2, 1), (17, 2)]) (ExcTree.node 1145 (ExcWit.pq 28 3 359) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))))) (ExcTree.node 6548 (ExcWit.pq 77 3 617) (ExcTree.node 1571 (ExcWit.pq 36 5 271) (ExcTree.node 1350 (ExcWit.pq 33 5 257) (ExcTree.node 1253 (ExcWit.pq 32 3 227) (ExcTree.node 1212 (ExcWit.fac 98 34 [(2, 1), (7, 2)]) (ExcTree.node 1186 (ExcWit.pq 31 3 223) (ExcTree.node 1151 (ExcWit.fac 122 33 [(2, 1), (61, 1)]) ExcTree.leaf ExcTree.leaf) (ExcTree.node 1210 (ExcWit.pq 29 3 367) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 1216 (ExcWit.pq 29 3 373) (ExcTree.node 1214 (ExcWit.pq 31 3 251) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 1303 (ExcWit.pq 36 3 5) (ExcTree.node 1281 (ExcWit.pq 30 3 379) (ExcTree.node 1277 (ExcWit.pq 32 3 251) ExcTree.leaf ExcTree.leaf) (ExcTree.node 1283 (ExcWit.pq 32 3 257) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 1346 (ExcWit.pq 31 3 383) (ExcTree.node 1322 (ExcWit.pq 33 5 229) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 1423 (ExcWit.pq 34 5 263) (ExcTree.node 1393 (ExcWit.pq 34 5 233) (ExcTree.node 1372 (ExcWit.pq 33 3 281) (ExcTree.node 1352 (ExcWit.pq 31 3 389) ExcTree.leaf ExcTree.leaf) (ExcTree.node 1374 (ExcWit.pq 33 3 283) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 1421 (ExcWit.pq 34 3 263) (ExcTree.node 1417 (ExcWit.pq 34 5 257) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 1466 (ExcWit.pq 35 3 239) (ExcTree.node 1445 (ExcWit.pq 32 3 419) (ExcTree.node 1443 (ExcWit.pq 34 5 283) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 1518 (ExcWit.fac 146 38 [(2, 1), (73, 1)]) (ExcTree.node 1496 (ExcWit.pq 35 3 269) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))) (ExcTree.node 3583 (ExcWit.pq 56 5 443) (ExcTree.node 2923 (ExcWit.pq 54 3 5) (ExcTree.node 1891 (ExcWit.pq 36 3 593) (ExcTree.node 1727 (ExcWit.pq 38 3 281) (ExcTree.node 1648 (ExcWit.pq 37 3 277) ExcTree.leaf ExcTree.leaf) (ExcTree.node 1808 (ExcWit.pq 39 5 283) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 2063 (ExcWit.pq 42 7 293) (ExcTree.node 1976 (ExcWit.pq 41 3 293) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 3244 (ExcWit.pq 53 3 433) (ExcTree.node 3135 (ExcWit.pq 48 3 829) (ExcTree.node 3028 (ExcWit.pq 51 7 421) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 3468 (ExcWit.pq 55 5 439) (ExcTree.node 3355 (ExcWit.pq 54 7 433) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 4444 (ExcWit.pq 61 5 719) (ExcTree.node 4063 (ExcWit.pq 60 3 461) (ExcTree.node 3819 (ExcWit.pq 58 7 449) (ExcTree.node 3700 (ExcWit.pq 57 3 449) ExcTree.leaf ExcTree.leaf) (ExcTree.node 3940 (ExcWit.pq 59 3 457) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 4315 (ExcWit.pq 62 5 467) (ExcTree.node 4188 (ExcWit.pq 61 5 463) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 6083 (ExcWit.pq 74 7 601) (ExcTree.node 5932 (ExcWit.pq 73 3 601) (ExcTree.node 5783 (ExcWit.pq 76 3 5) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 6391 (ExcWit.pq 76 3 613) (ExcTree.node 6236 (ExcWit.pq 75 5 607) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))))) (ExcTree.node 20155 (ExcWit.pq 138 3 1109) (ExcTree.node 8089 (ExcWit.pq 86 3 691) (ExcTree.node 7532 (ExcWit.pq 83 3 641) (ExcTree.node 7196 (ExcWit.pq 81 5 631) (ExcTree.node 6868 (ExcWit.pq 79 11 617) (ExcTree.node 6707 (ExcWit.pq 78 5 619) ExcTree.leaf ExcTree.leaf) (ExcTree.node 7031 (ExcWit.pq 78 7 941) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 7401 (ExcWit.pq 82 5 673) (ExcTree.node 7363 (ExcWit.pq 78 3 1277) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 7876 (ExcWit.pq 85 5 647) (ExcTree.node 7703 (ExcWit.pq 84 5 643) (ExcTree.node 7570 (ExcWit.pq 83 5 677) ExcTree.leaf ExcTree.leaf) (ExcTree.node 7741 (ExcWit.pq 84 3 683) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 8051 (ExcWit.pq 86 3 653) (ExcTree.node 7914 (ExcWit.pq 85 7 683) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 8994 (ExcWit.pq 91 5 709) (ExcTree.node 8445 (ExcWit.pq 88 11 691) (ExcTree.node 8266 (ExcWit.pq 87 7 691) (ExcTree.node 8228 (ExcWit.pq 87 7 653) ExcTree.leaf ExcTree.leaf) (ExcTree.node 8407 (ExcWit.pq 88 3 661) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 8809 (ExcWit.pq 88 3 1063) (ExcTree.node 8626 (ExcWit.pq 89 5 701) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 19324 (ExcWit.pq 135 3 1097) (ExcTree.node 19051 (ExcWit.pq 138 3 5) (ExcTree.node 9181 (ExcWit.pq 88 5 1433) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 19876 (ExcWit.pq 137 5 1103) (ExcTree.node 19599 (ExcWit.pq 136 7 1097) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))) (ExcTree.node 61016 (ExcWit.pq 247 3 5) (ExcTree.node 22164 (ExcWit.pq 145 11 1129) (ExcTree.node 21291 (ExcWit.pq 142 5 1123) (ExcTree.node 20719 (ExcWit.pq 140 3 1117) (ExcTree.node 20436 (ExcWit.pq 139 7 1109) ExcTree.leaf ExcTree.leaf) (ExcTree.node 21004 (ExcWit.pq 141 7 1117) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 21871 (ExcWit.pq 144 7 1129) (ExcTree.node 21580 (ExcWit.pq 143 3 1129) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 23055 (ExcWit.pq 146 7 1733) (ExcTree.node 22756 (ExcWit.pq 147 19 1129) (ExcTree.node 22459 (ExcWit.pq 144 3 1721) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 23659 (ExcWit.pq 150 7 1153) (ExcTree.node 23356 (ExcWit.pq 149 3 1153) ExcTree.leaf ExcTree.leaf) ExcTree.leaf))) (ExcTree.node 64495 (ExcWit.pq 250 3 1993) (ExcTree.node 62992 (ExcWit.pq 247 5 1979) (ExcTree.node 62000 (ExcWit.pq 245 3 1973) (ExcTree.node 61507 (ExcWit.pq 244 23 1949) ExcTree.leaf ExcTree.leaf) (ExcTree.node 62495 (ExcWit.pq 246 7 1973) ExcTree.leaf ExcTree.leaf)) (ExcTree.node 63992 (ExcWit.pq 249 5 1987) (ExcTree.node 63491 (ExcWit.pq 246 5 2971) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)) (ExcTree.node 66016 (ExcWit.pq 253 5 2003) (ExcTree.node 65507 (ExcWit.pq 252 5 1999) (ExcTree.node 65000 (ExcWit.pq 251 3 1997) ExcTree.leaf ExcTree.leaf) ExcTree.leaf) (ExcTree.node 67040 (ExcWit.pq 255 5 2011) (ExcTree.node 66527 (ExcWit.pq 254 13 1999) ExcTree.leaf ExcTree.leaf) ExcTree.leaf)))))))

private def checkTree : ExcTree → Bool
  | .leaf => true
  | .node k w l r => checkWit k w && checkTree l && checkTree r

private def treeFind (n : ℕ) : ExcTree → Option ExcWit
  | .leaf => none
  | .node k w l r =>
    if n == k then some w
    else if n < k then treeFind n l
    else treeFind n r

private lemma treeFind_sound : ∀ (t : ExcTree) (n : ℕ) (w : ExcWit),
    checkTree t = true → treeFind n t = some w → checkWit n w = true := by
  intro t
  induction t with
  | leaf => intro _ _ _ h; simp [treeFind] at h
  | node k wk l r ihl ihr =>
    intro n w hct hfind
    unfold checkTree at hct
    simp only [Bool.and_eq_true] at hct
    unfold treeFind at hfind
    by_cases hnk : n = k
    · subst hnk
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hfind
      subst hfind
      exact hct.1.1
    · have hbeq : (n == k) = false := beq_false_of_ne hnk
      rw [hbeq] at hfind
      simp only [Bool.false_eq_true, ↓reduceIte] at hfind
      by_cases hlt : n < k
      · simp only [hlt, ↓reduceIte] at hfind
        exact ihl n w hct.1.2 hfind
      · simp only [hlt, ↓reduceIte] at hfind
        exact ihr n w hct.2 hfind

private lemma checkTree_ok : checkTree excTree = true := by decide +kernel

private def treeHas (n : ℕ) (t : ExcTree) : Bool :=
  (treeFind n t).isSome

private def checkRUp (e pq r : ℕ) : ℕ → Bool
  | 0 => false
  | f + 1 =>
    let n := r * r + e - 1
    if pq < n then true
    else (n < 60 || treeHas n excTree) && checkRUp e pq (r + 1) f

private lemma checkRUp_sound : ∀ (f e pq r0 : ℕ),
    checkRUp e pq r0 f = true →
    ∀ r : ℕ, r0 ≤ r →
      60 ≤ r * r + e - 1 → r * r + e - 1 ≤ pq → treeHas (r * r + e - 1) excTree = true := by
  intro f
  induction f with
  | zero => intro _ _ _ h; simp [checkRUp] at h
  | succ f ih =>
    intro e pq r0 h r hr0 h60 hle
    unfold checkRUp at h
    by_cases hgt : pq < r0 * r0 + e - 1
    · have : r0 * r0 ≤ r * r := Nat.mul_le_mul hr0 hr0
      omega
    · simp only [hgt, ↓reduceIte, Bool.and_eq_true] at h
      by_cases hrr0 : r = r0
      · subst hrr0
        have h1 := h.1
        rw [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with hlt60 | hhas
        · omega
        · exact hhas
      · exact ih e pq (r0 + 1) h.2 r (by omega) h60 hle

private def checkExcList (e : ℕ) : List ℕ → Bool
  | [] => true
  | p :: rest =>
    let q := e - p
    let r0 := max 1 ((e - 9) / 4)
    checkRUp e (p * q) r0 19 && checkExcList (e + 2) rest

private lemma checkExcList_sound : ∀ (l : List ℕ) (e : ℕ),
    checkExcList e l = true →
    ∀ (i : ℕ) (hi : i < l.length),
      let ei := e + 2 * i
      let pi := l[i]'hi
      checkRUp ei (pi * (ei - pi)) (max 1 ((ei - 9) / 4)) 19 = true := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons p rest ih =>
    intro e h i hi
    unfold checkExcList at h
    rw [Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have hj : j < rest.length := by simpa using hi
      have hres := ih (e + 2) h.2 j hj
      simpa [show e + 2 + 2 * j = e + 2 * (j + 1) by omega] using hres

private lemma checkExcList_ok : checkExcList 8 goldList = true := by decide +kernel

end OeisA234246R1H1Proof

theorem OMA.solution : OMA.R_OeisA234246_conjecture_3_R1.H1 := by
  intro n h60 hlt
  set s := n.sqrt
  have hs_lo : s * s ≤ n := Nat.sqrt_le n
  have hs_hi : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs_ge7 : 7 ≤ s := by
    by_contra h
    have : s ≤ 6 := by omega
    nlinarith
  have hs_lt : s < 1024 := by
    by_contra h
    have : 1024 ≤ s := by omega
    nlinarith
  have hle_ns : n ≤ s * s + 2 * s := by nlinarith
  have hgap_le : n - s * s ≤ 2 * s := by omega
  have hex_r : ∃ r : ℕ, 1 ≤ r ∧ r * r < n ∧ (n - r * r) % 2 = 1 ∧
      7 ≤ n - r * r ∧ n - r * r ≤ 4 * s + 1 ∧ n - r * r + 1 ≤ 4 * r + 10 := by
    by_cases h1 : (n - s * s) % 2 = 1 ∧ 7 ≤ n - s * s
    · refine ⟨s, by omega, by omega, h1.1, h1.2, by omega, by omega⟩
    · by_cases hpar : (n - s * s) % 2 = 0
      · have hsq1 : (s - 1) * (s - 1) + 2 * s = s * s + 1 := by
          have : 1 ≤ s := by omega
          zify [this]; ring
        have hgap1 : n - (s - 1) * (s - 1) = (n - s * s) + 2 * s - 1 := by omega
        refine ⟨s - 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
      · have hsq2 : (s - 2) * (s - 2) + 4 * s = s * s + 4 := by
          have : 2 ≤ s := by omega
          zify [this]; ring
        have hgap2 : n - (s - 2) * (s - 2) = (n - s * s) + 4 * s - 4 := by omega
        have hsmall_gap : n - s * s ≤ 5 := by omega
        refine ⟨s - 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨r, hr1, hr2, hd_odd, hd7, hd_le, hd_r⟩ := hex_r
  set e := n - r * r + 1
  have he_even : e % 2 = 0 := by omega
  have he_lo : 8 ≤ e := by omega
  have he_hi : e ≤ 4100 := by omega
  set i := (e - 8) / 2
  have hi_lt : i < OeisA234246R1H1Proof.goldList.length := by
    rw [OeisA234246R1H1Proof.goldList_length]
    omega
  have he_eq : 8 + 2 * i = e := by omega
  have hgold := OeisA234246R1H1Proof.checkGoldList_sound
    OeisA234246R1H1Proof.goldList 8 OeisA234246R1H1Proof.checkGoldList_ok i hi_lt
  unfold OeisA234246R1H1Proof.checkGoldPair at hgold
  rw [he_eq] at hgold
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgold
  rcases hgold with ⟨⟨hpq, hpp⟩, hqp⟩
  set p := OeisA234246R1H1Proof.goldList[i]'hi_lt
  set q := e - p
  by_cases hmul : p * q < n
  · have hp' : p.Prime := OeisA234246R1H1Proof.prime_of_isPrimeSmall hpp (by omega)
    have hq' : q.Prime := OeisA234246R1H1Proof.prime_of_isPrimeSmall hqp (by omega)
    have htot := OMA.R_OeisA234246_conjecture_3_R1.totient_product hp' hq' (by omega)
    exact OMA.R_OeisA234246_conjecture_3_R1.witness (r := r) (Nat.mul_pos hp'.pos hq'.pos) hmul (by omega)
  · have hn_le : n ≤ p * q := by omega
    have hexc := OeisA234246R1H1Proof.checkExcList_sound
      OeisA234246R1H1Proof.goldList 8 OeisA234246R1H1Proof.checkExcList_ok i hi_lt
    dsimp only at hexc
    rw [he_eq] at hexc
    have hr_lo : max 1 ((e - 9) / 4) ≤ r := by omega
    have hneq : r * r + e - 1 = n := by omega
    have hhas := OeisA234246R1H1Proof.checkRUp_sound 19 e (p * q)
      (max 1 ((e - 9) / 4)) hexc r hr_lo (by omega) (by omega)
    rw [hneq] at hhas
    unfold OeisA234246R1H1Proof.treeHas at hhas
    rw [Option.isSome_iff_exists] at hhas
    obtain ⟨w, hw⟩ := hhas
    have hchk := OeisA234246R1H1Proof.treeFind_sound
      OeisA234246R1H1Proof.excTree n w OeisA234246R1H1Proof.checkTree_ok hw
    exact OeisA234246R1H1Proof.solve_of_checkWit hchk
