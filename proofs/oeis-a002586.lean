import OMAStatements.S_oeis_a002586
import Mathlib

/-!
# OEIS A002586: least prime factor of `2^(8+48k)+1` and `2^(40+48k)+1` is 257

`257 ∣ 2^n + 1` because `2^16 ≡ 1 (mod 257)` and `2^8 ≡ 2^40 ≡ -1`. For a prime `q < 257`
(odd, since `2^n + 1` is odd) Fermat's little theorem makes `2^(c+48k) mod q` depend only on
`k mod (q-1)`, and a kernel-checked table shows no residue gives `-1`.
-/

namespace OMA.A002586Proof

/-- Bool table: for every `3 ≤ m < 257` and every `r < m - 1`, `m ∤ 2^(c+48r) + 1`. -/
def chk (c : ℕ) : Bool :=
  (List.range 257).all fun m =>
    m < 3 || (List.range (m - 1)).all fun r => (2 ^ (c + 48 * r) + 1) % m != 0

theorem chk8 : chk 8 = true := by decide +kernel

theorem chk40 : chk 40 = true := by decide +kernel

theorem of_chk {c : ℕ} (h : chk c = true) {m r : ℕ} (hm3 : 3 ≤ m) (hm : m < 257)
    (hr : r < m - 1) : ¬ m ∣ 2 ^ (c + 48 * r) + 1 := by
  unfold chk at h
  rw [List.all_eq_true] at h
  have h1 := h m (List.mem_range.2 hm)
  have h2 : ¬ m < 3 := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq, h2, false_or, List.all_eq_true,
    List.mem_range, bne_iff_ne, ne_eq] at h1
  exact fun hd => h1 r hr (Nat.mod_eq_zero_of_dvd hd)

theorem periodic {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (c k : ℕ) :
    (2 : ZMod q) ^ (c + 48 * k) = (2 : ZMod q) ^ (c + 48 * (k % (q - 1))) := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hf : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  conv_lhs => rw [← Nat.div_add_mod k (q - 1)]
  rw [mul_add, ← add_assoc, pow_add _ (c + _), pow_add _ c (48 * ((q - 1) * _)),
    show 48 * ((q - 1) * (k / (q - 1))) = (q - 1) * (48 * (k / (q - 1))) by ring,
    pow_mul, hf, one_pow, mul_one, ← pow_add]

theorem not_dvd {c : ℕ} (h : chk c = true) (k q : ℕ) (hq : q.Prime) (hq3 : 3 ≤ q)
    (hq257 : q < 257) : ¬ q ∣ 2 ^ (c + 48 * k) + 1 := by
  intro hd
  have : Fact q.Prime := ⟨hq⟩
  apply of_chk h hq3 hq257 (Nat.mod_lt k (by omega) : k % (q - 1) < q - 1)
  rw [← ZMod.natCast_eq_zero_iff] at hd ⊢
  push_cast at hd ⊢
  rw [← periodic (by omega)]
  exact hd

theorem dvd257 (c k : ℕ) (hc : (2 : ZMod 257) ^ c + 1 = 0) : 257 ∣ 2 ^ (c + 48 * k) + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have h16 : (2 : ZMod 257) ^ 16 = 1 := by decide
  rw [pow_add, show 48 * k = 16 * (3 * k) by ring, pow_mul, h16, one_pow, mul_one]
  exact hc

theorem minFac_eq {c : ℕ} (h : chk c = true) (hc : (2 : ZMod 257) ^ c + 1 = 0) (k : ℕ) :
    (2 ^ (c + 48 * k) + 1).minFac = 257 := by
  have hd := dvd257 c k hc
  apply le_antisymm (Nat.minFac_le_of_dvd (by norm_num) hd)
  by_contra hlt
  rw [not_le] at hlt
  have hne : 2 ^ (c + 48 * k) + 1 ≠ 1 := by
    have := Nat.one_le_two_pow (n := c + 48 * k); omega
  have hp := Nat.minFac_prime hne
  have hdv := Nat.minFac_dvd (2 ^ (c + 48 * k) + 1)
  have h2 : (2 ^ (c + 48 * k) + 1).minFac ≠ 2 := by
    intro h2
    rw [h2] at hdv
    have hc0 : 0 < c + 48 * k ∨ c + 48 * k = 0 := by omega
    rcases hc0 with hc0 | hc0
    · have : 2 ∣ 2 ^ (c + 48 * k) := dvd_pow_self 2 (by omega)
      omega
    · rw [hc0] at hd; norm_num at hd
  exact not_dvd h k _ hp (by have := hp.two_le; omega) hlt hdv

end OMA.A002586Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a002586.main := by
  intro k
  exact ⟨OMA.A002586Proof.minFac_eq OMA.A002586Proof.chk8 (by decide) k,
    OMA.A002586Proof.minFac_eq OMA.A002586Proof.chk40 (by decide) k⟩
