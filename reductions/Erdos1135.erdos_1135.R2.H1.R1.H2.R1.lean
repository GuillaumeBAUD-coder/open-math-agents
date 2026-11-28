import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1

-- Reduction Erdos1135.erdos_1135.R2.H1.R1.H2.R1 of step Erdos1135.erdos_1135.R2.H1.R1.H2
-- Credit: @arindale

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H2_R1

open Finset Function

/-- At some descent of the shortcut orbit the drop is at least the number of odd
steps so far. This is the dynamical content; the first descent has drop/odd-count
at least `1.2` in every computed case. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 4 = 3 → ∃ k : ℕ,
    let s := ((range k).filter fun i => T^[i] n % 2 = 1).card
    T^[k] n < n ∧ s ≤ n - T^[k] n

/-- Pure arithmetic: replacing the endpoint `n - s` by the start loses at most
the factor `(n - 2 + 2 s) / (n - 2)`; this holds for every positive `s`. -/
def H2 : Prop :=
  ∀ n s : ℕ, 2048 < n → 1 ≤ s →
    (n - s) ^ 6 * (n - 2 + 2 * s) < n ^ 6 * (n - 2)

theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R2_H1_R1.H2 := by
  intro h1 h2
  intro n hn hmod hdesc
  obtain ⟨k, hklt, hsd⟩ := h1 n hn hmod
  set T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2 with hTdef
  have hT : ∀ v, T v = if v % 2 = 0 then v / 2 else (3 * v + 1) / 2 := fun v => rfl
  set s := ((range k).filter fun i => T^[i] n % 2 = 1).card with hsdef
  have hnodd : n % 2 = 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hklt
    · omega
  have hmem0 : 0 ∈ (range k).filter (fun i => T^[i] n % 2 = 1) := by
    rw [mem_filter, mem_range]
    exact ⟨hk1, by simpa using hnodd⟩
  have hs1 : 1 ≤ s := Nat.succ_le_of_lt (card_pos.mpr ⟨0, hmem0⟩)
  have hxle : T^[k] n ≤ n - s := by omega
  have hx6 : (T^[k] n) ^ 6 ≤ (n - s) ^ 6 := Nat.pow_le_pow_left hxle 6
  have hxk : (T^[k] n) ^ 6 * (n - 2 + 2 * s) < n ^ 6 * (n - 2) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hx6) (h2 n s hn hs1)
  have hxpos : 0 < T^[k] n := OMA.R_Erdos1135_erdos_1135_R2.shortcut_positive hT (by omega) k
  have haff := OMA.R_Erdos1135_erdos_1135_R2.affine_identity
    (x := fun i => T^[i] n)
    (odds := fun k => (range k).filter fun i => T^[i] n % 2 = 1)
    (OMA.R_Erdos1135_erdos_1135_R2.shortcut_rec hT n) (fun _ => rfl) k
  have hcard : ((range k).filter fun i => T^[i] n % 2 = 1).card = s := rfl
  have h3n : 3 ^ s * n ≤ 2 ^ k * T^[k] n := by
    rw [hcard] at haff
    rw [haff]
    exact Nat.le_add_right _ _
  have h6 : 3 ^ (6 * s) * n ^ 6 ≤ 2 ^ (6 * k) * (T^[k] n) ^ 6 := by
    have h := Nat.pow_le_pow_left h3n 6
    rwa [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm s 6, Nat.mul_comm k 6] at h
  have h1' : 3 ^ (6 * s) * ((T^[k] n) ^ 6 * (n - 2 + 2 * s)) <
      3 ^ (6 * s) * (n ^ 6 * (n - 2)) :=
    (Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ (6 * s))).mpr hxk
  have h2' : 3 ^ (6 * s) * (n ^ 6 * (n - 2)) ≤
      (2 ^ (6 * k) * (T^[k] n) ^ 6) * (n - 2) := by
    calc 3 ^ (6 * s) * (n ^ 6 * (n - 2))
        = (3 ^ (6 * s) * n ^ 6) * (n - 2) := by ring
      _ ≤ (2 ^ (6 * k) * (T^[k] n) ^ 6) * (n - 2) := by
          exact Nat.mul_le_mul_right _ h6
  have hchain : (3 ^ (6 * s) * (n - 2 + 2 * s)) * (T^[k] n) ^ 6 <
      (2 ^ (6 * k) * (n - 2)) * (T^[k] n) ^ 6 := by
    calc (3 ^ (6 * s) * (n - 2 + 2 * s)) * (T^[k] n) ^ 6
        = 3 ^ (6 * s) * ((T^[k] n) ^ 6 * (n - 2 + 2 * s)) := by ring
      _ < 3 ^ (6 * s) * (n ^ 6 * (n - 2)) := h1'
      _ ≤ (2 ^ (6 * k) * (T^[k] n) ^ 6) * (n - 2) := h2'
      _ = (2 ^ (6 * k) * (n - 2)) * (T^[k] n) ^ 6 := by ring
  have hmain : 3 ^ (6 * s) * (n - 2 + 2 * s) < 2 ^ (6 * k) * (n - 2) :=
    Nat.lt_of_mul_lt_mul_right hchain
  refine ⟨k, ?_⟩
  dsimp only
  change (n - 2 + 2 * s) * (3 ^ s) ^ 6 < (n - 2) * (2 ^ k) ^ 6
  calc (n - 2 + 2 * s) * (3 ^ s) ^ 6
      = 3 ^ (6 * s) * (n - 2 + 2 * s) := by
        rw [← pow_mul, Nat.mul_comm s 6]; ring
    _ < 2 ^ (6 * k) * (n - 2) := hmain
    _ = (n - 2) * (2 ^ k) ^ 6 := by
        rw [← pow_mul, Nat.mul_comm k 6]; ring

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H2_R1
