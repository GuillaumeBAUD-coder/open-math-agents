import OMAReductions.R_oeis_a231725_R1
import Mathlib

namespace OMA.W

def prAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if n < d * d then true else if n % d = 0 then false else prAux n f (d + 1)

def pr (n : ℕ) : Bool := decide (2 ≤ n) && prAux n n 2

theorem prAux_sound (n : ℕ) (hn : 2 ≤ n) : ∀ (f d : ℕ), prAux n f d = true →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → n.Prime := by
  intro f
  induction f with
  | zero => intro d h; simp [prAux] at h
  | succ f ih =>
    intro d h hd
    unfold prAux at h
    split_ifs at h with h1 h2
    · by_contra hp
      have h3 := Nat.minFac_sq_le_self (by omega) hp
      have h4 : n.minFac < d := by
        by_contra hc
        have : d * d ≤ n.minFac * n.minFac := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      exact hd _ (Nat.minFac_prime (by omega)).two_le h4 (Nat.minFac_dvd n)
    · exact ih (d + 1) h (fun m hm hlt => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h5 | h5
        · exact hd m hm h5
        · subst h5; exact fun hdv => h2 (Nat.mod_eq_zero_of_dvd hdv))

theorem pr_sound {n : ℕ} (h : pr n = true) : n.Prime := by
  unfold pr at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact prAux_sound n h.1 n 2 h.2 (fun m hm hlt => by omega)

end OMA.W

set_option maxHeartbeats 8000000 in
theorem OMA.solution : OMA.R_oeis_a231725_R1.H1 := by
  intro n h1 hn
  interval_cases n
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨10, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨6, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨5, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨5, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨8, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨6, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨12, by decide, by decide, by norm_num⟩
  · exact ⟨5, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨8, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨5, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨11, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨6, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨5, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨4, by decide, by decide, by norm_num⟩
  · exact ⟨1, by decide, by decide, by norm_num⟩
  · exact ⟨22, by decide, by decide, OMA.W.pr_sound (by decide +kernel)⟩
  · exact ⟨3, by decide, by decide, by norm_num⟩
  · exact ⟨2, by decide, by decide, by norm_num⟩
