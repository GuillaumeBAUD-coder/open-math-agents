import OMAReductions.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1

namespace E10H1

def bits (m : ℕ) : List ℕ := (List.range 9).filter (fun i => m.testBit i)

theorem table : ∀ n < 257, n % 2 = 0 → n ≠ 0 →
    ∃ p ∈ [2, 7, 11, 13, 19, 23, 29, 31, 37, 41, 43], p ≤ n ∧ (bits (n - p)).length ≤ 4 ∧
      ((bits (n - p)).map (2 ^ ·)).sum = n - p := by
  decide +kernel

theorem primes : ∀ p ∈ [2, 7, 11, 13, 19, 23, 29, 31, 37, 41, 43], p.Prime := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end E10H1

theorem OMA.solution : OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1.H1 := by
  intro n hn hn0 hle
  obtain ⟨p, hpL, hpn, hlen, hsum⟩ := E10H1.table n (by omega) (Nat.even_iff.mp hn) hn0
  refine ⟨p, (E10H1.bits (n - p) : Multiset ℕ), E10H1.primes p hpL, by simpa using hlen, ?_⟩
  simp only [Multiset.map_coe, Multiset.sum_coe]
  omega
