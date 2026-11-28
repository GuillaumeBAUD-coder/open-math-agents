import OMAReductions.R_Erdos1135_erdos_1135_R1

-- Reduction Erdos1135.erdos_1135.R1.H1.R1 of step Erdos1135.erdos_1135.R1.H1
-- Credit: @Ciphore

/-! The one-modulo-three Erdős 1135 residue core is refined from modulo `256` to modulo `1024`.
Twelve of the seventy-six lifts descend within ten accelerated steps. The sixty-four remaining
classes are split into four independent groups of sixteen. -/

namespace OMA.R_Erdos1135_erdos_1135_R1_H1_R1

open CollatzConjecture Function

/-- Depth-ten resistant residue classes, group 1. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) → n % 1024 ∈ ([27, 283, 539, 795, 31, 543, 799, 47, 303, 559, 63, 319, 831, 71, 327, 839] : List ℕ) →
    ∃ k : ℕ, collatzStep^[k] n < n

/-- Depth-ten resistant residue classes, group 2. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) → n % 1024 ∈ ([91, 603, 859, 103, 359, 615, 871, 111, 623, 879, 127, 383, 639, 895, 155, 411] : List ℕ) →
    ∃ k : ℕ, collatzStep^[k] n < n

/-- Depth-ten resistant residue classes, group 3. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) → n % 1024 ∈ ([667, 159, 415, 671, 927, 167, 679, 935, 191, 447, 703, 959, 207, 463, 719, 223] : List ℕ) →
    ∃ k : ℕ, collatzStep^[k] n < n

/-- Depth-ten resistant residue classes, group 4. -/
def H4 : Prop :=
  ∀ n : ℕ, 1 < n → n % 27 ∈ ([1, 4, 7, 10, 16, 19, 25] : List ℕ) → n % 1024 ∈ ([479, 991, 231, 487, 743, 239, 495, 751, 1007, 251, 763, 1019, 255, 511, 767, 1023] : List ℕ) →
    ∃ k : ℕ, collatzStep^[k] n < n

lemma not_mem_four_append {x : ℕ} {a b c d : List ℕ}
    (ha : x ∉ a) (hb : x ∉ b) (hc : x ∉ c) (hd : x ∉ d) :
    x ∉ a ++ b ++ c ++ d := by
  intro h
  simp only [List.mem_append] at h
  tauto

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem certificate1024 (T : ℕ → ℕ)
    (hT : T = fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 1024, (r.val + 2) % 1024 ∉ ([27, 283, 539, 795, 31, 543, 799, 47, 303, 559, 63, 319, 831, 71, 327, 839] : List ℕ) ++ ([91, 603, 859, 103, 359, 615, 871, 111, 623, 879, 127, 383, 639, 895, 155, 411] : List ℕ) ++ ([667, 159, 415, 671, 927, 167, 679, 935, 191, 447, 703, 959, 207, 463, 719, 223] : List ℕ) ++ ([479, 991, 231, 487, 743, 239, 495, 751, 1007, 251, 763, 1019, 255, 511, 767, 1023] : List ℕ) →
      ∃ j : Fin 11, T^[j.val] (r.val + 2) < r.val + 2 ∧
        T^[j.val] (1024 + (r.val + 2)) ≤ 1024 + T^[j.val] (r.val + 2) := by
  subst T
  decide +kernel

theorem forward_descent1024 {n : ℕ} (hn : 1 < n)
    (hres : n % 1024 ∉ ([27, 283, 539, 795, 31, 543, 799, 47, 303, 559, 63, 319, 831, 71, 327, 839] : List ℕ) ++ ([91, 603, 859, 103, 359, 615, 871, 111, 623, 879, 127, 383, 639, 895, 155, 411] : List ℕ) ++ ([667, 159, 415, 671, 927, 167, 679, 935, 191, 447, 703, 959, 207, 463, 719, 223] : List ℕ) ++ ([479, 991, 231, 487, 743, 239, 495, 751, 1007, 251, 763, 1019, 255, 511, 767, 1023] : List ℕ)) : ∃ k, collatzStep^[k] n < n := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  let r : Fin 1024 := ⟨(n - 2) % 1024, Nat.mod_lt _ (by decide)⟩
  let b := r.val + 2
  let q := (n - 2) / 1024
  have hnq : n = 1024 * q + b := by dsimp [q, b, r]; omega
  have hb : b % 1024 = n % 1024 := by omega
  obtain ⟨j, hdrop, hslope⟩ := certificate1024 T rfl r (by simpa only [← hb] using hres)
  change T^[j.val] b < b at hdrop
  change T^[j.val] (1024 + b) ≤ 1024 + T^[j.val] b at hslope
  let d := 2 ^ (10 - j.val)
  have hj : j.val ≤ 10 := by omega
  have hd : 2 ^ j.val * d = 1024 := by
    dsimp [d]
    rw [← pow_add, show j.val + (10 - j.val) = 10 by omega]
    decide
  obtain ⟨a, ha⟩ := OMA.R_Erdos1135_erdos_1135_R1.residue_affine T (fun _ => rfl) j.val b
  have ha' := ha d
  rw [hd] at ha'
  have had : a * d ≤ 1024 := by omega
  have hcalc : T^[j.val] n = a * d * q + T^[j.val] b := by
    calc T^[j.val] n = T^[j.val] (2 ^ j.val * (d * q) + b) := by rw [← Nat.mul_assoc, hd, ← hnq]
         _ = _ := by rw [ha, Nat.mul_assoc]
  obtain ⟨k, hk⟩ := OMA.R_Erdos1135_erdos_1135_R1.accelerated_iterate T (fun _ => rfl) n j.val
  exact ⟨k, by rw [hk, hcalc]; have := Nat.mul_le_mul_right q had; omega⟩

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1135_erdos_1135_R1.H1 := by
  intro hA hB hC hD n hn h27 h256
  by_cases hA' : n % 1024 ∈ ([27, 283, 539, 795, 31, 543, 799, 47, 303, 559, 63, 319, 831, 71, 327, 839] : List ℕ)
  · exact hA n hn h27 hA'
  by_cases hB' : n % 1024 ∈ ([91, 603, 859, 103, 359, 615, 871, 111, 623, 879, 127, 383, 639, 895, 155, 411] : List ℕ)
  · exact hB n hn h27 hB'
  by_cases hC' : n % 1024 ∈ ([667, 159, 415, 671, 927, 167, 679, 935, 191, 447, 703, 959, 207, 463, 719, 223] : List ℕ)
  · exact hC n hn h27 hC'
  by_cases hD' : n % 1024 ∈ ([479, 991, 231, 487, 743, 239, 495, 751, 1007, 251, 763, 1019, 255, 511, 767, 1023] : List ℕ)
  · exact hD n hn h27 hD'
  apply forward_descent1024 hn
  exact not_mem_four_append hA' hB' hC' hD'

end OMA.R_Erdos1135_erdos_1135_R1_H1_R1
