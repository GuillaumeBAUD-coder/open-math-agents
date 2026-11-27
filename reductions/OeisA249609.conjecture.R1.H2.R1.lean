import OMAReductions.R_OeisA249609_conjecture_R1

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1

-- For odious odd row indices, a non-exceptional row has an evil entry.
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → Odd n → OeisA249609.isEvil n = false →
    n ∉ ({0, 1, 2, 7, 8} : Finset ℕ) →
    ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true

-- For odious even row indices, a non-exceptional row has an evil entry.
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → Even n → OeisA249609.isEvil n = false →
    n ∉ ({0, 1, 2, 7, 8} : Finset ℕ) →
    ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true

lemma zero_has_no_evil (n : ℕ) (hz : OeisA249609.a n = 0) (k : ℕ)
    (hk : k ∈ List.range' 1 n) : OeisA249609.isEvil (n.choose k) = false := by
  cases hf : (List.range' 1 n).find? (fun m => OeisA249609.isEvil (n.choose m)) with
  | none =>
    have h := (List.find?_eq_none.mp hf) k hk
    simpa using h
  | some t =>
    have ht := List.mem_of_find?_eq_some hf
    obtain ⟨i, hi, hti⟩ := List.mem_range'.mp ht
    have htpos : 1 ≤ t := by omega
    have htzero : t = 0 := by simpa [OeisA249609.a, hf] using hz
    omega

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1.H2 := by
  intro hodd heven n hz
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hone : 1 ∈ List.range' 1 n := by
    apply List.mem_range'.2
    exact ⟨0, hnpos, by simp⟩
  have hnotEvil : OeisA249609.isEvil n = false := by
    simpa using zero_has_no_evil n hz 1 hone
  by_contra hnot
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk, hkEvil⟩ := heven n hnpos he hnotEvil hnot
    have hkFalse := zero_has_no_evil n hz k hk
    simp_all
  · obtain ⟨k, hk, hkEvil⟩ := hodd n hnpos ho hnotEvil hnot
    have hkFalse := zero_has_no_evil n hz k hk
    simp_all

end OMA.R_OeisA249609_conjecture_R1_H2_R1
