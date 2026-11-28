import OMAReductions.R_oeis_a227864_R1

namespace OMA.A227864

def nd (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => n < d * d || (n % d != 0 && nd n f (d + 1))

def pr (n : ℕ) : Bool := 2 ≤ n && nd n n 2

def good (p : ℕ) : Bool := (List.range' 2 (p - 2)).any (fun d => p % d == 0) ||
  (List.range' (p + 1) 20).any fun b => b ≤ p ^ 2 && pr ((p ^ 2 % b) * b + p ^ 2 / b)

lemma nd_spec (n : ℕ) : ∀ f d, nd n f d = true → ∀ m, d ≤ m → m * m ≤ n → n % m ≠ 0 := by
  intro f
  induction f with
  | zero => simp [nd]
  | succ f ih =>
    intro d h m hm hn
    simp only [nd, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne] at h
    rcases h with h | ⟨h1, h2⟩
    · have := Nat.mul_le_mul hm hm; omega
    · rcases hm.eq_or_lt with rfl | hm
      · exact h1
      · exact ih _ h2 m hm hn

lemma pr_spec (n : ℕ) (h : pr n = true) : n.Prime := by
  simp only [pr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.prime_def_le_sqrt.2 ⟨h.1, fun m hm hs hd =>
    nd_spec n n 2 h.2 m hm (Nat.le_sqrt.1 hs) (Nat.mod_eq_zero_of_dvd hd)⟩

end OMA.A227864

set_option maxHeartbeats 0 in
open OMA.A227864 in
theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  have key : (List.range' 3 1998).all good = true := by decide +kernel
  intro p h3 h2 hp
  have := List.all_eq_true.1 key p (List.mem_range'_1.2 ⟨h3, by omega⟩)
  simp only [good, Bool.or_eq_true, List.any_eq_true, List.mem_range'_1, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with ⟨d, ⟨hd1, hd2⟩, hd⟩ | ⟨b, ⟨hb1, hb2⟩, hb, hr⟩
  · exact absurd (hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd)) (by omega)
  · exact ⟨b, by omega, by
      rw [OMA.R_oeis_a227864_R1.two_digit_reversal p b (by omega) (by omega) hb]; exact pr_spec _ hr⟩
