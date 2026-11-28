import OMAStatements.S_oeis_a344734
import Mathlib

open OMA.S_oeis_a344734

namespace OMA.P_oeis_a344734

lemma shift (q k : ℕ) : Nat.Coprime (10 * q + k) 10 ↔ Nat.Coprime k 10 := by
  rw [show 10 * q + k = k + q * 10 by ring]
  exact Nat.coprime_add_mul_right_left k 10 q

lemma count_shift (q b : ℕ) :
    Nat.count (fun k => Nat.Coprime (10 * q + k) 10) b = Nat.count (fun k => Nat.Coprime k 10) b := by
  simp only [shift]

lemma count10 (q : ℕ) : Nat.count (fun k => Nat.Coprime k 10) (10 * q) = 4 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 10 * (q + 1) = 10 * q + 10 by ring, Nat.count_add, ih, count_shift]
    have : Nat.count (fun k => Nat.Coprime k 10) 10 = 4 := by decide
    omega

lemma c_val (q r d : ℕ) (hd : Nat.Coprime d 10) (hr : Nat.count (fun k => Nat.Coprime k 10) d = r) :
    c (4 * q + r + 1) = 10 * q + d := by
  have hp : Nat.Coprime (10 * q + d) 10 := (shift q d).2 hd
  have hc : Nat.count (fun k => Nat.Coprime k 10) (10 * q + d) = 4 * q + r := by
    rw [Nat.count_add, count10, count_shift, hr]
  unfold c
  rw [show 4 * q + r + 1 - 1 = 4 * q + r by omega, ← hc]
  exact Nat.nth_count hp

lemma sInf_eq (m x0 : ℕ) (h0 : 0 < x0) (hd : m ∣ 10 * x0 + 1)
    (hmin : ∀ x, 0 < x → m ∣ 10 * x + 1 → x0 ≤ x) :
    sInf {x : ℕ | 0 < x ∧ m ∣ 10 * x + 1} = x0 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨h0, hd⟩
  · exact le_csInf ⟨x0, h0, hd⟩ (fun x hx => hmin x hx.1 hx.2)

lemma a1 (q : ℕ) (hq : 1 ≤ q) : a (4 * q + 0 + 1) = q := by
  unfold a; rw [c_val q 0 1 (by decide) (by decide)]
  apply sInf_eq _ _ (by omega) ⟨1, by ring⟩
  intro x hx hdx
  have := Nat.le_of_dvd (by omega) hdx
  omega

lemma a3 (q : ℕ) : a (4 * q + 1 + 1) = 7 * q + 2 := by
  unfold a; rw [c_val q 1 3 (by decide) (by decide)]
  apply sInf_eq _ _ (by omega) ⟨7, by ring⟩
  intro x hx ⟨k, hk⟩
  by_contra hlt
  have hk7 : k < 7 := by
    by_contra h7
    have : (10 * q + 3) * 7 ≤ (10 * q + 3) * k := Nat.mul_le_mul_left _ (by omega)
    omega
  interval_cases k <;> omega

lemma a7 (q : ℕ) : a (4 * q + 2 + 1) = 3 * q + 2 := by
  unfold a; rw [c_val q 2 7 (by decide) (by decide)]
  apply sInf_eq _ _ (by omega) ⟨3, by ring⟩
  intro x hx ⟨k, hk⟩
  by_contra hlt
  have hk7 : k < 3 := by
    by_contra h7
    have : (10 * q + 7) * 3 ≤ (10 * q + 7) * k := Nat.mul_le_mul_left _ (by omega)
    omega
  interval_cases k <;> omega

lemma a9 (q : ℕ) : a (4 * q + 3 + 1) = 9 * q + 8 := by
  unfold a; rw [c_val q 3 9 (by decide) (by decide)]
  apply sInf_eq _ _ (by omega) ⟨9, by ring⟩
  intro x hx ⟨k, hk⟩
  by_contra hlt
  have hk7 : k < 9 := by
    by_contra h7
    have : (10 * q + 9) * 9 ≤ (10 * q + 9) * k := Nat.mul_le_mul_left _ (by omega)
    omega
  interval_cases k <;> omega

end OMA.P_oeis_a344734

open OMA.P_oeis_a344734 in
theorem OMA.solution : type_of% @OMA.S_oeis_a344734.main := by
  intro n hn
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r + 1 :=
    ⟨(n - 1) / 4, (n - 1) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  have e4 : 4 * (p + 2) + r + 1 - 4 = 4 * (p + 1) + r + 1 := by omega
  have e8 : 4 * (p + 2) + r + 1 - 8 = 4 * p + r + 1 := by omega
  rw [e4, e8]
  interval_cases r
  · rw [a1 _ (by omega), a1 _ (by omega), a1 _ (by omega)]; push_cast; ring
  · rw [a3, a3, a3]; push_cast; ring
  · rw [a7, a7, a7]; push_cast; ring
  · rw [a9, a9, a9]; push_cast; ring

