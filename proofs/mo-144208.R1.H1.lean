import OMAReductions.R_mo_144208_R1

/-! Let x = 2^a and S = Σ_{i<b} (x+1)^i, so S · x + 1 = (x+1)^b = 1 + 2^c and S · 2^a = 2^c.
Every term of S is odd, so S ≡ b (mod 2). If b were odd, S would be an odd power of 2, hence 1,
but S ≥ b ≥ 2. So b = 2k and y = (1 + 2^a)^k satisfies y^2 = 1 + 2^c, i.e. (y-1)(y+1) = 2^c.
Both factors are powers of 2 differing by 2, so y = 3. This forces k = 1 and a = 1, so b = 2
and c = 3. -/

namespace OMA.Mo144208

open Finset

theorem sq_eq_one_add_two_pow (y c : ℕ) (hy : 2 ≤ y) (h : y ^ 2 = 1 + 2 ^ c) : y = 3 := by
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  have e : (z + 1) ^ 2 = z * (z + 2) + 1 := by ring
  have hprod : z * (z + 2) = 2 ^ c := by omega
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hprod)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hprod)
  rcases i with _ | _ | i
  · rw [pow_zero] at hi
    subst hi
    rcases j with _ | _ | j
    · rw [pow_zero] at hj
      omega
    · rw [pow_one] at hj
      omega
    · have : 4 ≤ 2 ^ (j + 1 + 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · rw [zero_add, pow_one] at hi
    omega
  · have hpos : 0 < 2 ^ i := by positivity
    have hz : z = 4 * 2 ^ i := by rw [hi]; ring
    rcases j with _ | _ | j
    · rw [pow_zero] at hj
      omega
    · rw [pow_one] at hj
      omega
    · have hj2 : z + 2 = 4 * 2 ^ j := by rw [hj]; ring
      omega

end OMA.Mo144208

open Finset in
theorem OMA.solution : OMA.R_mo_144208_R1.H1 := by
  intro a b c ha hb hc h
  have hx : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hbe : Even b := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hgeom := geom_sum_mul_add (2 ^ a) b
    rw [add_comm 1 (2 ^ a)] at h
    rw [h] at hgeom
    have hS : (∑ i ∈ range b, (2 ^ a + 1) ^ i) * 2 ^ a = 2 ^ c := by omega
    have hterm : ∀ i, (2 ^ a + 1) ^ i % 2 = 1 := by
      intro i
      have h2 : (2 ^ a + 1) % 2 = 1 := by
        have : 2 ∣ 2 ^ a := dvd_pow_self 2 ha.ne'
        omega
      rw [Nat.pow_mod, h2, one_pow]
      norm_num
    have hS2 : (∑ i ∈ range b, (2 ^ a + 1) ^ i) % 2 = b % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_one]
    have hSge : b ≤ ∑ i ∈ range b, (2 ^ a + 1) ^ i := by
      have h1 : ∑ _i ∈ range b, 1 ≤ ∑ i ∈ range b, (2 ^ a + 1) ^ i :=
        Finset.sum_le_sum (fun i _ => Nat.one_le_pow _ _ (by omega))
      simpa using h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hS)
    have hodd' := Nat.odd_iff.1 hodd
    rcases k with _ | k
    · rw [pow_zero] at hk
      omega
    · have : 2 ∣ ∑ i ∈ range b, (2 ^ a + 1) ^ i := by
        rw [hk, pow_succ]
        exact dvd_mul_left 2 _
      omega
  obtain ⟨k, rfl⟩ := hbe
  have hk : 1 ≤ k := by omega
  have hy : ((1 + 2 ^ a) ^ k) ^ 2 = 1 + 2 ^ c := by
    rw [← pow_mul, show k * 2 = k + k by ring]
    exact h
  have hy2 : 2 ≤ (1 + 2 ^ a) ^ k :=
    le_trans (by omega : 2 ≤ 1 + 2 ^ a) (Nat.le_self_pow (by omega) _)
  have h3 := OMA.Mo144208.sq_eq_one_add_two_pow _ c hy2 hy
  have hk1 : k = 1 := by
    by_contra hk1
    have h4 : (1 + 2 ^ a) ^ 2 ≤ (1 + 2 ^ a) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : 3 ^ 2 ≤ (1 + 2 ^ a) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  subst hk1
  rw [pow_one] at h3
  have ha1 : a = 1 := by
    have h6 : 2 ^ a = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h6
  subst ha1
  have h9 : (1 + 2 ^ 1) ^ (1 + 1) = 9 := by norm_num
  rw [h9] at h
  have hc3 : c = 3 := by
    have h8 : 2 ^ c = 2 ^ 3 := by omega
    exact Nat.pow_right_injective (le_refl 2) h8
  subst hc3
  rfl
