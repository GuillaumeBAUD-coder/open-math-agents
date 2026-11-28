import OMAStatements.S_oeis_a191107
import Mathlib

namespace OMA.S_oeis_a191107

def f (t : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 t)

lemma f_zero : f 0 = 0 := by simp [f]

lemma f_double (s : ℕ) : f (2 * s) = 3 * f s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [f_zero]
  · unfold f
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.ofDigits_cons]

lemma f_succ_double (s : ℕ) : f (2 * s + 1) = 3 * f s + 1 := by
  unfold f
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have : (2 * s + 1) / 2 = s := by omega
  simp [Nat.ofDigits_cons, this]
  ring

lemma f_lt_succ (t : ℕ) : f t < f (t + 1) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
    · rw [show 2 * s + 1 = 2 * s + 1 from rfl, f_double, f_succ_double]; omega
    · have h := ih s (by omega)
      rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring, f_succ_double, f_double]; omega

lemma f_mono : StrictMono f := strictMono_nat_of_lt_succ f_lt_succ

def h (t : ℕ) : ℕ := 3 * f t + 1

lemma h_mono : StrictMono h := by
  intro a b hab; have := f_mono hab; unfold h; omega

lemma mem_iff (x : ℕ) : InA191107 x ↔ ∃ t, x = h t := by
  constructor
  · intro hx
    induction hx with
    | base => exact ⟨0, by simp [h, f_zero]⟩
    | step1 _ ih =>
      obtain ⟨t, rfl⟩ := ih
      exact ⟨2 * t, by rw [h, h, f_double]; omega⟩
    | step2 _ ih =>
      obtain ⟨t, rfl⟩ := ih
      exact ⟨2 * t + 1, by rw [h, h, f_succ_double] <;> omega⟩
  · rintro ⟨t, rfl⟩
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simpa [h, f_zero] using InA191107.base
      · obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' t
        · have := InA191107.step1 (ih s (by omega))
          have e : 3 * h s - 2 = h (2 * s) := by rw [h, h, f_double]; omega
          rwa [e] at this
        · have := InA191107.step2 (ih s (by omega))
          have e : 3 * h s + 1 = h (2 * s + 1) := by rw [h, h, f_succ_double] <;> omega
          rwa [e] at this

lemma nth_eq (k : ℕ) : Nat.nth InA191107 k = h k := by
  have hinf : (Set.ofPred InA191107).Infinite := by
    have : Set.range h ⊆ Set.ofPred InA191107 := by
      rintro _ ⟨t, rfl⟩
      exact (mem_iff _).mpr ⟨t, rfl⟩
    exact Set.Infinite.mono this (Set.infinite_range_of_injective h_mono.injective)
  have key := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := InA191107) h
    (by
      intro x hx
      obtain ⟨t, ht⟩ := (mem_iff x).mp hx
      exact ⟨t, fun hf => absurd hf hinf, ht.symm⟩)
    (by
      intro t _
      exact (mem_iff _).mpr ⟨t, rfl⟩)
    (h_mono.strictMonoOn _)
  exact (key (show k ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred InA191107), n < hf.toFinset.card} from fun hf => absurd hf hinf)).symm

theorem sol : type_of% @main := by
  constructor
  · intro n hn
    rw [nth_eq]
    have e1 : A003278 n = 1 + f (n - 1) := rfl
    rw [e1]
    simp only [h]
    omega
  · intro n hn
    rw [nth_eq]
    have e2 : A003278 (2 * n - 1) = 1 + f (2 * n - 1 - 1) := rfl
    have : 2 * n - 1 - 1 = 2 * (n - 1) := by omega
    rw [e2, this, f_double]
    simp only [h]
    omega

end OMA.S_oeis_a191107

theorem OMA.solution : type_of% @OMA.S_oeis_a191107.main := OMA.S_oeis_a191107.sol
