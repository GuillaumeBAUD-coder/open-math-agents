import OMAStatements.S_oeis_a327978

namespace OMA.A327978

-- Square-and-multiply with a fixed fuel bound, evaluated by the kernel in each certificate.
def powBits {p : ℕ} (a : ZMod p) : ℕ → ℕ → ZMod p
  | 0, _ => 1
  | bits + 1, n => (if n % 2 = 0 then 1 else a) * (powBits a bits (n / 2)) ^ 2

theorem powBits_eq {p : ℕ} (a : ZMod p) (bits n : ℕ) (hn : n < 2 ^ bits) :
    powBits a bits n = a ^ n := by
  induction bits generalizing n with
  | zero =>
    have h : n = 0 := by simpa using hn
    simp [powBits, h]
  | succ bits ih =>
    have half_lt : n / 2 < 2 ^ bits := by
      rw [pow_succ] at hn
      omega
    rw [powBits, ih _ half_lt, ← pow_mul]
    have parity : (if n % 2 = 0 then (1 : ZMod p) else a) = a ^ (n % 2) := by
      by_cases h : n % 2 = 0
      · simp [h]
      · have hn' : n % 2 = 1 := by omega
        simp [hn']
    rw [parity, ← pow_add]
    congr 1
    omega

-- Lucas primality criterion, given the prime factors of p - 1 and modular order tests.
theorem certified_prime (p g : ℕ) (factors : List ℕ) (hp : 1 < p) (hsize : p < 2 ^ 64)
    (hprod : factors.prod = p - 1) (hprime : ∀ q ∈ factors, q.Prime)
    (hbase : powBits (g : ZMod p) 64 (p - 1) = 1)
    (horders : ∀ q ∈ factors, powBits (g : ZMod p) 64 ((p - 1) / q) ≠ 1) : p.Prime := by
  have he : p - 1 < 2 ^ 64 := (Nat.sub_le _ _).trans_lt hsize
  apply lucas_primality p (g : ZMod p)
  · rwa [powBits_eq _ _ _ he] at hbase
  · intro q hq hdiv
    have hmem := (Nat.mem_primeFactorsList (by omega : p - 1 ≠ 0)).mpr ⟨hq, hdiv⟩
    have hq' := (Nat.primeFactorsList_unique hprod hprime).mem_iff.mpr hmem
    have hexp := (Nat.div_le_self (p - 1) q).trans_lt he
    simpa only [powBits_eq _ _ _ hexp] using horders q hq'

theorem prime_39139476251 : Nat.Prime 39139476251 := by
  apply certified_prime 39139476251 2 [2, 5, 5, 5, 5, 7, 31, 313, 461] (by decide) (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem prime_4227063435109 : Nat.Prime 4227063435109 := by
  apply certified_prime 4227063435109 2 [2, 2, 3, 3, 3, 39139476251] (by decide) (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_39139476251
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem prime_43054087 : Nat.Prime 43054087 := by
  apply certified_prime 43054087 3 [2, 3, 73, 98297] (by decide) (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem prime_74384363 : Nat.Prime 74384363 := by
  apply certified_prime 74384363 2 [2, 13, 29, 47, 2099] (by decide) (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem prime_2380299617 : Nat.Prime 2380299617 := by
  apply certified_prime 2380299617 3 [2, 2, 2, 2, 2, 74384363] (by decide) (by decide) (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_74384363
  · decide +kernel
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

open OMA.S_oeis_a327978

theorem derivative_of_factors (n : ℕ) (l : List ℕ) (hp : l.prod = n)
    (hs : ∀ p ∈ l, p.Prime) : arithmeticDerivative n = (l.map (fun p => n / p)).sum := by
  exact ((Nat.primeFactorsList_unique hp hs).map (fun p => n / p)).sum_eq.symm

-- A multiple of five whose derivative is the product of the primes through 43.
theorem multiple_of_five : arithmeticDerivative 32442711864461575 = primorial 43 := by
  have h := derivative_of_factors 32442711864461575 [5, 5, 307, 4227063435109]
    (by decide) (by simp [prime_4227063435109]; norm_num)
  rw [h]
  decide +kernel

-- A multiple of three other than nine whose derivative is the product of the primes through 47.
theorem multiple_of_three : arithmeticDerivative 922334641167462111 = primorial 47 := by
  have h := derivative_of_factors 922334641167462111 [3, 3, 43054087, 2380299617]
    (by decide) (by simp [prime_43054087, prime_2380299617]; norm_num)
  rw [h]
  decide +kernel

end OMA.A327978

open OMA.S_oeis_a327978 OMA.A327978

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327978.main) := by
  intro h
  have hf := h 32442711864461575 (by rw [multiple_of_five]; decide) ⟨43, multiple_of_five⟩
  exact hf.1 (by decide)
