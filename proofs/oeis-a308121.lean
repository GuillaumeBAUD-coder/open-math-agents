import OMAStatements.S_oeis_a308121
import Mathlib

/-!
# A308121: for odd n > 1, row 2n is row n with its halves interchanged

Let n be odd with n > 1 and write phi(n)/n = 2a/b in lowest terms (the numerator is even, since
phi(n) is even and n is odd). As phi(2n) = phi(n), the reduced form of phi(2n)/(2n) is a/b, and
2a n = b phi(n). Split the coprimes of n into the low ones c < n/2 and the high ones c > n/2. The
map c to n - c shows both parts have phi(n)/2 elements. The coprimes of 2n are the odd coprimes
of n in [1, n], which are exactly 2c - n for c high, in the same order, followed by n + 2c for c
low. Comparing entries, T(2n, k) = T(n, k + phi(n)/2) and T(2n, k + phi(n)/2) = T(n, k) both
reduce to a n = b phi(n)/2. List equalities are proved by comparing strictly increasing lists
with the same members.
-/

namespace OMA.P308121

open OMA.S_oeis_a308121

def low (n : ℕ) : List ℕ := (coprimes n).filter (fun c => 2 * c < n)
def high (n : ℕ) : List ℕ := (coprimes n).filter (fun c => n < 2 * c)

lemma sorted_eq {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; omega
  · exact h₁.imp (fun h => le_of_lt h)
  · exact h₂.imp (fun h => le_of_lt h)
  · exact (List.perm_ext_iff_of_nodup h₁.nodup h₂.nodup).2 h

lemma coprimes_pw (n : ℕ) : (coprimes n).Pairwise (· < ·) :=
  (List.pairwise_lt_range' (s := 1) (n := n)).filter _

lemma mem_coprimes (n x : ℕ) : x ∈ coprimes n ↔ 1 ≤ x ∧ x < 1 + n ∧ x.Coprime n := by
  simp [coprimes, List.mem_range'_1, and_assoc]

lemma low_pw (n : ℕ) : (low n).Pairwise (· < ·) := (coprimes_pw n).filter _
lemma high_pw (n : ℕ) : (high n).Pairwise (· < ·) := (coprimes_pw n).filter _

lemma mem_low (n x : ℕ) : x ∈ low n ↔ x ∈ coprimes n ∧ 2 * x < n := by
  simp [low]

lemma mem_high (n x : ℕ) : x ∈ high n ↔ x ∈ coprimes n ∧ n < 2 * x := by
  simp [high]

lemma split (n : ℕ) (hn : Odd n) : coprimes n = low n ++ high n := by
  rw [Nat.odd_iff] at hn
  apply sorted_eq (coprimes_pw n)
  · rw [List.pairwise_append]
    refine ⟨low_pw n, high_pw n, ?_⟩
    intro a ha b hb
    rw [mem_low] at ha; rw [mem_high] at hb; omega
  · intro x
    rw [List.mem_append, mem_low, mem_high]
    constructor
    · intro h
      by_cases h2 : 2 * x < n
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (h | h) <;> exact h.1

lemma cop_sub (n c : ℕ) (hn : Odd n) (h : n < 2 * c) : (2 * c - n).Coprime n ↔ c.Coprime n := by
  rw [Nat.coprime_sub_self_left (by omega), Nat.coprime_mul_iff_left]
  have : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

lemma cop_add (n c : ℕ) (hn : Odd n) : (n + 2 * c).Coprime n ↔ c.Coprime n := by
  rw [add_comm, Nat.coprime_add_self_left, Nat.coprime_mul_iff_left]
  have : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

lemma double (n : ℕ) (hn : Odd n) :
    coprimes (2 * n) = (high n).map (fun c => 2 * c - n) ++ (low n).map (fun c => n + 2 * c) := by
  have hn' := Nat.odd_iff.1 hn
  apply sorted_eq (coprimes_pw (2 * n))
  · rw [List.pairwise_append, List.pairwise_map, List.pairwise_map]
    refine ⟨?_, ?_, ?_⟩
    · refine (high_pw n).imp_of_mem ?_
      intro a b ha hb hab
      rw [mem_high] at ha hb; omega
    · exact (low_pw n).imp (fun h => by omega)
    · intro a ha b hb
      rw [List.mem_map] at ha hb
      obtain ⟨c, hc, rfl⟩ := ha
      obtain ⟨d, hd, rfl⟩ := hb
      rw [mem_high, mem_coprimes] at hc
      rw [mem_low, mem_coprimes] at hd
      omega
  · intro x
    rw [mem_coprimes, List.mem_append, List.mem_map, List.mem_map, Nat.coprime_mul_iff_right,
      Nat.coprime_two_right, Nat.odd_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hx : x ≤ n
      · left
        refine ⟨(x + n) / 2, ?_, by omega⟩
        rw [mem_high, mem_coprimes]
        have e : 2 * ((x + n) / 2) - n = x := by omega
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        rw [← cop_sub n _ hn (by omega), e]; exact h4
      · right
        refine ⟨(x - n) / 2, ?_, by omega⟩
        rw [mem_low, mem_coprimes]
        have e : n + 2 * ((x - n) / 2) = x := by omega
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        rw [← cop_add n _ hn, e]; exact h4
    · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
      · rw [mem_high, mem_coprimes] at hc
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [cop_sub n c hn hc.2]; exact hc.1.2.2
      · rw [mem_low, mem_coprimes] at hc
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [cop_add n c hn]; exact hc.1.2.2

lemma high_eq (n : ℕ) (hn : Odd n) (hn1 : 1 < n) : high n = ((low n).map (fun c => n - c)).reverse := by
  have hn' := Nat.odd_iff.1 hn
  apply sorted_eq (high_pw n)
  · rw [List.pairwise_reverse, List.pairwise_map]
    refine (low_pw n).imp_of_mem ?_
    intro a b ha hb hab
    rw [mem_low] at ha hb; omega
  · intro x
    rw [List.mem_reverse, List.mem_map, mem_high, mem_coprimes]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      have hx : x ≠ n := by
        rintro rfl
        rw [Nat.coprime_self] at h3; omega
      refine ⟨n - x, ?_, by omega⟩
      rw [mem_low, mem_coprimes]
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [← Nat.coprime_self_sub_left (by omega)]
      have e : n - (n - x) = x := by omega
      rw [e]; exact h3
    · rintro ⟨c, hc, rfl⟩
      rw [mem_low, mem_coprimes] at hc
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [Nat.coprime_self_sub_left (by omega)]; exact hc.1.2.2

lemma len_eq (n : ℕ) (hn : Odd n) (hn1 : 1 < n) : (high n).length = (low n).length := by
  rw [high_eq n hn hn1, List.length_reverse, List.length_map]

lemma coprimes_length (n : ℕ) : (coprimes n).length = Nat.totient n := by
  rw [← Nat.filter_coprime_Ico_eq_totient n 1]
  simp [coprimes, Finset.card, Finset.filter_val, Finset.Ico, LocallyFiniteOrder.finsetIco,
    Nat.coprime_comm]

lemma row_eq (n : ℕ) : row n = ((coprimes n).map (fun a : ℕ => (a : ℤ))).mapIdx
    (fun i (t : ℤ) => den n * ((i : ℤ) + 1) - num n * t) := by
  unfold row
  congr 1
  generalize coprimes n = L
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, ← ih]
    rfl

lemma arith (n : ℕ) (hn : Odd n) (hn1 : 1 < n) : ∃ a1 b0 : ℕ,
    num n = 2 * (a1 : ℤ) ∧ den n = (b0 : ℤ) ∧ num (2 * n) = (a1 : ℤ) ∧ den (2 * n) = (b0 : ℤ) ∧
      2 * a1 * n = b0 * Nat.totient n := by
  set m := Nat.totient n with hm
  have hn0 : 0 < n := by omega
  set g := Nat.gcd m n with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hn0
  obtain ⟨a0, ha0⟩ : g ∣ m := Nat.gcd_dvd_left m n
  obtain ⟨b0, hb0⟩ : g ∣ n := Nat.gcd_dvd_right m n
  have cop : Nat.Coprime a0 b0 := by
    have := Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg
    rw [← hgdef] at this
    have e1 : m / g = a0 := by rw [ha0, Nat.mul_div_cancel_left _ hg]
    have e2 : n / g = b0 := by rw [hb0, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this
  have hgodd : Odd g := Odd.of_dvd_nat hn (Nat.gcd_dvd_right m n)
  have hmeven : Even m := Nat.totient_even (by obtain ⟨k, hk⟩ := hn; omega)
  have h2a0 : 2 ∣ a0 := by
    have h2m : 2 ∣ g * a0 := by rw [← ha0]; exact even_iff_two_dvd.1 hmeven
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_left.2 hgodd) h2m)
  obtain ⟨a1, ha1⟩ := h2a0
  have hb0pos : 0 < b0 := by
    rcases Nat.eq_zero_or_pos b0 with h | h
    · rw [h] at hb0; omega
    · exact h
  have cop1 : Nat.Coprime a1 b0 := Nat.Coprime.coprime_dvd_left ⟨2, by rw [ha1]; ring⟩ cop
  have htot2 : Nat.totient (2 * n) = m := by
    rw [Nat.totient_mul (Nat.coprime_two_left.2 hn), Nat.totient_two, one_mul]
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have q1 : ((m : ℚ) / (n : ℚ)) = (((2 * a1 : ℕ) : ℤ) : ℚ) / ((b0 : ℤ) : ℚ) := by
    rw [ha0, hb0, ha1]; push_cast; field_simp
  have q2 : ((Nat.totient (2 * n) : ℚ) / ((2 * n : ℕ) : ℚ)) = ((a1 : ℤ) : ℚ) / ((b0 : ℤ) : ℚ) := by
    rw [htot2, ha0, hb0, ha1]; push_cast; field_simp
  have hb0z : (0 : ℤ) < (b0 : ℤ) := by exact_mod_cast hb0pos
  have cop0 : Nat.Coprime (2 * a1) b0 := by rw [← ha1]; exact cop
  refine ⟨a1, b0, ?_, ?_, ?_, ?_, ?_⟩
  · unfold num; rw [← hm, q1, Rat.num_div_eq_of_coprime hb0z (by simpa [Int.natAbs_mul] using cop0)]; push_cast; ring
  · unfold den; rw [← hm, q1, Rat.den_div_eq_of_coprime hb0z (by simpa [Int.natAbs_mul] using cop0)]
  · unfold num; rw [q2, Rat.num_div_eq_of_coprime hb0z (by simpa using cop1)]
  · unfold den; rw [q2, Rat.den_div_eq_of_coprime hb0z (by simpa using cop1)]
  · rw [ha0, hb0, ha1]; ring

end OMA.P308121

open OMA.S_oeis_a308121 OMA.P308121 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308121.main := by
  intro n hodd hn1
  obtain ⟨a1, b0, h1, h2, h3, h4, h5⟩ := arith n hodd hn1
  have hsplit := split n hodd
  have h2n := double n hodd
  have hlh := len_eq n hodd hn1
  have htot := coprimes_length n
  rw [hsplit, List.length_append, hlh] at htot
  have hh : Nat.totient n / 2 = (low n).length := by omega
  rw [← htot] at h5
  have hk : (a1 : ℤ) * n = b0 * (low n).length := by
    have : (2 * a1 * n : ℤ) = b0 * ((low n).length + (low n).length) := by exact_mod_cast h5
    linarith
  rw [row_eq, row_eq, h2n, hsplit, h1, h2, h3, h4, List.map_append, List.map_append,
    List.mapIdx_append, List.mapIdx_append, hh,
    List.drop_left' (by simp), List.take_left' (by simp)]
  congr 1
  · apply List.ext_getElem
    · simp [hlh]
    · intro i hi1 hi2
      simp only [List.getElem_mapIdx, List.getElem_map, List.length_map]
      have hc := List.getElem_mem (l := high n) (n := i) (by simpa using hi1)
      rw [mem_high] at hc
      rw [Nat.cast_sub (by omega)]
      push_cast
      linear_combination hk
  · apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_mapIdx, List.getElem_map, List.length_map, hlh]
      push_cast
      linear_combination -hk
