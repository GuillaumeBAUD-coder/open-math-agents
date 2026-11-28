import OMAStatements.S_oeis_a097602
import Mathlib

namespace A097602

lemma card_succ_pos (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (h : p (n + 1)) :
    ((Finset.Icc 1 (n + 1)).filter p).card = ((Finset.Icc 1 n).filter p).card + 1 := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), Finset.filter_insert,
    if_pos h, Finset.card_insert_of_notMem (by simp)]

lemma card_succ_neg (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (h : ¬ p (n + 1)) :
    ((Finset.Icc 1 (n + 1)).filter p).card = ((Finset.Icc 1 n).filter p).card := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), Finset.filter_insert,
    if_neg h]

lemma not_sq (k d x : ℕ) (hx : x = k * k + d) (h1 : 0 < d) (h2 : d < 2 * k + 1) :
    ¬ IsSquare x := by
  rintro ⟨r, hr⟩
  rw [hx] at hr
  have h3 : k < r := by
    by_contra hlt
    have h5 : r ≤ k := by omega
    have h6 : r * r ≤ k * k := Nat.mul_le_mul h5 h5
    omega
  have h4 : r < k + 1 := by
    by_contra hge
    have h5 : k + 1 ≤ r := by omega
    have h6 : (k + 1) * (k + 1) ≤ r * r := Nat.mul_le_mul h5 h5
    have h7 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega
  omega

set_option maxHeartbeats 1000000 in
lemma block (a c : ℕ → ℕ) (hrec : ∀ n, 1 ≤ n → a (n + 1) = a n + c n)
    (hpos : ∀ n, IsSquare (a (n + 1)) → c (n + 1) = c n + 1)
    (hneg : ∀ n, ¬ IsSquare (a (n + 1)) → c (n + 1) = c n) (j : ℕ)
    (hA : a (9 * j + 1) = (3 * j + 1) * (3 * j + 1)) (hC : c (9 * j + 1) = 2 * j + 1) :
    ¬ IsSquare (a (9 * j + 2)) ∧ ¬ IsSquare (a (9 * j + 3)) ∧
    a (9 * j + 4) = (3 * j + 2) * (3 * j + 2) ∧
    ¬ IsSquare (a (9 * j + 5)) ∧ ¬ IsSquare (a (9 * j + 6)) ∧ ¬ IsSquare (a (9 * j + 7)) ∧
    ¬ IsSquare (a (9 * j + 8)) ∧ ¬ IsSquare (a (9 * j + 9)) ∧
    a (9 * j + 10) = (3 * j + 4) * (3 * j + 4) ∧ c (9 * j + 10) = 2 * j + 3 := by
  have a2 : a (9 * j + 2) = (3 * j + 1) * (3 * j + 1) + (2 * j + 1) := by
    have h : a (9 * j + 2) = a (9 * j + 1) + c (9 * j + 1) := hrec (9 * j + 1) (by omega)
    rw [h, hA, hC]
  have s2 : ¬ IsSquare (a (9 * j + 2)) := by
    rw [a2]
    exact not_sq (3 * j + 1) (2 * j + 1) _ rfl (by omega) (by omega)
  have c2 : c (9 * j + 2) = 2 * j + 1 := by
    have h : c (9 * j + 2) = c (9 * j + 1) := hneg (9 * j + 1) s2
    rw [h, hC]
  have a3 : a (9 * j + 3) = (3 * j + 1) * (3 * j + 1) + 2 * (2 * j + 1) := by
    have h : a (9 * j + 3) = a (9 * j + 2) + c (9 * j + 2) := hrec (9 * j + 2) (by omega)
    rw [h, a2, c2]
    ring
  have s3 : ¬ IsSquare (a (9 * j + 3)) := by
    rw [a3]
    exact not_sq (3 * j + 1) (2 * (2 * j + 1)) _ rfl (by omega) (by omega)
  have c3 : c (9 * j + 3) = 2 * j + 1 := by
    have h : c (9 * j + 3) = c (9 * j + 2) := hneg (9 * j + 2) s3
    rw [h, c2]
  have a4 : a (9 * j + 4) = (3 * j + 2) * (3 * j + 2) := by
    have h : a (9 * j + 4) = a (9 * j + 3) + c (9 * j + 3) := hrec (9 * j + 3) (by omega)
    rw [h, a3, c3]
    ring
  have c4 : c (9 * j + 4) = 2 * j + 2 := by
    have s4 : IsSquare (a (9 * j + 4)) := by
      rw [a4]
      exact ⟨3 * j + 2, rfl⟩
    have h : c (9 * j + 4) = c (9 * j + 3) + 1 := hpos (9 * j + 3) s4
    rw [h, c3]
  have a5 : a (9 * j + 5) = (3 * j + 2) * (3 * j + 2) + (2 * j + 2) := by
    have h : a (9 * j + 5) = a (9 * j + 4) + c (9 * j + 4) := hrec (9 * j + 4) (by omega)
    rw [h, a4, c4]
  have s5 : ¬ IsSquare (a (9 * j + 5)) := by
    rw [a5]
    exact not_sq (3 * j + 2) (2 * j + 2) _ rfl (by omega) (by omega)
  have c5 : c (9 * j + 5) = 2 * j + 2 := by
    have h : c (9 * j + 5) = c (9 * j + 4) := hneg (9 * j + 4) s5
    rw [h, c4]
  have a6 : a (9 * j + 6) = (3 * j + 2) * (3 * j + 2) + 2 * (2 * j + 2) := by
    have h : a (9 * j + 6) = a (9 * j + 5) + c (9 * j + 5) := hrec (9 * j + 5) (by omega)
    rw [h, a5, c5]
    ring
  have s6 : ¬ IsSquare (a (9 * j + 6)) := by
    rw [a6]
    exact not_sq (3 * j + 2) (2 * (2 * j + 2)) _ rfl (by omega) (by omega)
  have c6 : c (9 * j + 6) = 2 * j + 2 := by
    have h : c (9 * j + 6) = c (9 * j + 5) := hneg (9 * j + 5) s6
    rw [h, c5]
  have a7 : a (9 * j + 7) = (3 * j + 3) * (3 * j + 3) + 1 := by
    have h : a (9 * j + 7) = a (9 * j + 6) + c (9 * j + 6) := hrec (9 * j + 6) (by omega)
    rw [h, a6, c6]
    ring
  have s7 : ¬ IsSquare (a (9 * j + 7)) := by
    rw [a7]
    exact not_sq (3 * j + 3) (1) _ rfl (by omega) (by omega)
  have c7 : c (9 * j + 7) = 2 * j + 2 := by
    have h : c (9 * j + 7) = c (9 * j + 6) := hneg (9 * j + 6) s7
    rw [h, c6]
  have a8 : a (9 * j + 8) = (3 * j + 3) * (3 * j + 3) + (2 * j + 3) := by
    have h : a (9 * j + 8) = a (9 * j + 7) + c (9 * j + 7) := hrec (9 * j + 7) (by omega)
    rw [h, a7, c7]
    ring
  have s8 : ¬ IsSquare (a (9 * j + 8)) := by
    rw [a8]
    exact not_sq (3 * j + 3) (2 * j + 3) _ rfl (by omega) (by omega)
  have c8 : c (9 * j + 8) = 2 * j + 2 := by
    have h : c (9 * j + 8) = c (9 * j + 7) := hneg (9 * j + 7) s8
    rw [h, c7]
  have a9 : a (9 * j + 9) = (3 * j + 3) * (3 * j + 3) + (4 * j + 5) := by
    have h : a (9 * j + 9) = a (9 * j + 8) + c (9 * j + 8) := hrec (9 * j + 8) (by omega)
    rw [h, a8, c8]
    ring
  have s9 : ¬ IsSquare (a (9 * j + 9)) := by
    rw [a9]
    exact not_sq (3 * j + 3) (4 * j + 5) _ rfl (by omega) (by omega)
  have c9 : c (9 * j + 9) = 2 * j + 2 := by
    have h : c (9 * j + 9) = c (9 * j + 8) := hneg (9 * j + 8) s9
    rw [h, c8]
  have a10 : a (9 * j + 10) = (3 * j + 4) * (3 * j + 4) := by
    have h : a (9 * j + 10) = a (9 * j + 9) + c (9 * j + 9) := hrec (9 * j + 9) (by omega)
    rw [h, a9, c9]
    ring
  have c10 : c (9 * j + 10) = 2 * j + 3 := by
    have s10 : IsSquare (a (9 * j + 10)) := by
      rw [a10]
      exact ⟨3 * j + 4, rfl⟩
    have h : c (9 * j + 10) = c (9 * j + 9) + 1 := hpos (9 * j + 9) s10
    rw [h, c9]
  exact ⟨s2, s3, a4, s5, s6, s7, s8, s9, a10, c10⟩

end A097602

theorem OMA.solution : type_of% @OMA.S_oeis_a097602.main := by
  rintro a ⟨ha1, hrec⟩ m
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ,
      ∀ n, c n = ((Finset.Icc 1 n).filter fun i => IsSquare (a i)).card := ⟨_, fun _ => rfl⟩
  have hrec' : ∀ n, 1 ≤ n → a (n + 1) = a n + c n := by
    intro n hn
    rw [hc]
    convert hrec n hn
  have hpos : ∀ n, IsSquare (a (n + 1)) → c (n + 1) = c n + 1 := by
    intro n h
    rw [hc, hc]
    exact A097602.card_succ_pos (fun i => IsSquare (a i)) n h
  have hneg : ∀ n, ¬ IsSquare (a (n + 1)) → c (n + 1) = c n := by
    intro n h
    rw [hc, hc]
    exact A097602.card_succ_neg (fun i => IsSquare (a i)) n h
  have hc1 : c 1 = 1 := by
    have s1 : IsSquare (a (0 + 1)) := by
      show IsSquare (a 1)
      rw [ha1]
      exact ⟨1, rfl⟩
    have h := hpos 0 s1
    have h0 : c 0 = 0 := by
      rw [hc]
      simp
    rw [h0] at h
    exact h
  have inv : ∀ j, a (9 * j + 1) = (3 * j + 1) * (3 * j + 1) ∧ c (9 * j + 1) = 2 * j + 1 := by
    intro j
    induction j with
    | zero => exact ⟨ha1, hc1⟩
    | succ k ih =>
      obtain ⟨-, -, -, -, -, -, -, -, b9, b10⟩ := A097602.block a c hrec' hpos hneg k ih.1 ih.2
      have e : 9 * (k + 1) + 1 = 9 * k + 10 := by ring
      rw [e]
      refine ⟨?_, ?_⟩
      · rw [b9]
        ring
      · rw [b10]
        ring
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 9 ∧ n = 9 * j + 1 + t :=
      ⟨(n - 1) / 9, (n - 1) % 9, Nat.mod_lt _ (by norm_num), by omega⟩
    have hsq : IsSquare (a (9 * j + 1 + t)) := ⟨m, by rw [hm]; ring⟩
    obtain ⟨s2, s3, a4, s5, s6, s7, s8, s9, -, -⟩ :=
      A097602.block a c hrec' hpos hneg j (inv j).1 (inv j).2
    interval_cases t
    · have h1 : a (9 * j + 1) = m ^ 2 := hm
      rw [(inv j).1] at h1
      have h2 : (3 * j + 1) ^ 2 = m ^ 2 := by
        rw [← h1]
        ring
      have h3 : 3 * j + 1 = m := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h2
      omega
    · exact absurd hsq s2
    · exact absurd hsq s3
    · have h1 : a (9 * j + 4) = m ^ 2 := hm
      rw [a4] at h1
      have h2 : (3 * j + 2) ^ 2 = m ^ 2 := by
        rw [← h1]
        ring
      have h3 : 3 * j + 2 = m := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h2
      omega
    · exact absurd hsq s5
    · exact absurd hsq s6
    · exact absurd hsq s7
    · exact absurd hsq s8
    · exact absurd hsq s9
  · intro hm
    obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 1 ∨ m = 3 * j + 2 := ⟨m / 3, by omega⟩
    rcases hj with rfl | rfl
    · refine ⟨9 * j + 1, by omega, ?_⟩
      rw [(inv j).1]
      ring
    · obtain ⟨-, -, a4, -⟩ := A097602.block a c hrec' hpos hneg j (inv j).1 (inv j).2
      refine ⟨9 * j + 4, by omega, ?_⟩
      rw [a4]
      ring
