import OMAStatements.S_oeis_a282059
import Mathlib

namespace OMA.S_oeis_a282059

def g (r : ℕ) : ℕ := ((Finset.range 31).filter (fun d => Nat.Coprime (10 * r + d) 210)).card

lemma cop (k d : ℕ) : Nat.Coprime (10 * k + d) 210 ↔ Nat.Coprime (10 * (k % 21) + d) 210 := by
  have h : (10 * k + d) % 210 = (10 * (k % 21) + d) % 210 := by omega
  unfold Nat.Coprime
  rw [Nat.gcd_comm _ 210, Nat.gcd_comm (10 * (k % 21) + d) 210, Nat.gcd_rec 210, Nat.gcd_rec 210 (10 * (k % 21) + d), h]

lemma prime_cop (m : ℕ) (hm : 10 ≤ m) (hp : m.Prime) : Nat.Coprime m 210 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have : m ∣ 2 * 3 * 5 * 7 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).1 this with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h1; omega

lemma cnt_le (k : ℕ) (hk : 1 ≤ k) : countPrimes k ≤ g (k % 21) := by
  unfold countPrimes g
  have : Finset.Icc (10 * k) (10 * k + 30) = (Finset.range 31).map (addLeftEmbedding (10 * k)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
    constructor
    · intro h; exact ⟨x - 10 * k, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [this, Finset.filter_map, Finset.card_map]
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter, Function.comp, addLeftEmbedding_apply] at hd ⊢
  exact ⟨hd.1, (cop k d).1 (prime_cop _ (by omega) hd.2)⟩

lemma g_le : ∀ r < 21, g r ≤ 8 ∧ (g r = 8 → r = 1 ∨ r = 17) := by decide +kernel

end OMA.S_oeis_a282059

theorem OMA.solution : type_of% @OMA.S_oeis_a282059.main := by
  refine ⟨fun k hk => ?_, fun k hk h => ?_⟩
  · exact (OMA.S_oeis_a282059.cnt_le k hk).trans (OMA.S_oeis_a282059.g_le _ (Nat.mod_lt _ (by norm_num))).1
  · have h1 := OMA.S_oeis_a282059.cnt_le k hk
    have h2 := OMA.S_oeis_a282059.g_le (k % 21) (Nat.mod_lt _ (by norm_num))
    have : OMA.S_oeis_a282059.g (k % 21) = 8 := le_antisymm h2.1 (h ▸ h1)
    exact h2.2 this
