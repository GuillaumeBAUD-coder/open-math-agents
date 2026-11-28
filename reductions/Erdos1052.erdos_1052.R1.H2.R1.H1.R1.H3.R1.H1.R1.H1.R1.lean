import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1
-- Credit: @kaleidoKurt

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1

-- The uniform bounds below concern the number of distinct prime divisors.
-- A fixed count gives only finitely many unitary perfect numbers by the
-- Subbarao-Warren theorem already formalized in the root reduction.
-- H1 covers odd multiples of the 53 obstruction indices. The proof below
-- excludes every support of size two in this whole branch.
def H1 : Prop :=
  ∃ K : ℕ, ∀ (n : ℕ), Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    3 ∈ S → 3 ≤ S.card →
    (∃ k ∈ ([
      45, 63, 66, 75, 99, 105, 110, 117, 153, 154, 165, 175, 195, 207, 255, 261,
      273, 279, 286, 333, 345, 374, 391, 418, 425, 429, 435, 465, 483, 493, 555,
      595, 609, 629, 663, 713, 759, 775, 777, 805, 851, 899, 925, 957, 1015,
      1073, 1085, 1131, 1147, 1209, 1221, 1295, 1443] : List ℕ), n.factorization 3 % (2*k) = k) →
    n.primeFactors.card ≤ K

-- H2 covers the remaining exponent classes from the parent table.
def H2 : Prop :=
  ∃ K : ℕ, ∀ (n : ℕ), Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    3 ∈ S → 2 ≤ S.card →
    ¬ (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2*d) ≠ d) →
    (∀ k ∈ ([
      45, 63, 66, 75, 99, 105, 110, 117, 153, 154, 165, 175, 195, 207, 255, 261,
      273, 279, 286, 333, 345, 374, 391, 418, 425, 429, 435, 465, 483, 493, 555,
      595, 609, 629, 663, 713, 759, 775, 777, 805, 851, 899, 925, 957, 1015,
      1073, 1085, 1131, 1147, 1209, 1221, 1295, 1443] : List ℕ), n.factorization 3 % (2*k) ≠ k) →
    n.primeFactors.card ≤ K

theorem forced_pair {s : List Nat} {e k : Nat} (h3 : 3 ∈ s)
    (rows : List (Nat × List Nat))
    (hit : ∀ r ∈ rows, e % (2 * r.1) = r.1 → ∃ x ∈ r.2, x ∈ s)
    (d f : Nat) (he : e % (2*k) = k)
    (hd : 2*d ∣ 2*k) (hf : 2*f ∣ 2*k)
    (hdk : k % (2*d) = d) (hfk : k % (2*f) = f)
    (known : ∃ u ∈ rows, ∃ v ∈ rows, u.1 = d ∧ v.1 = f ∧
      3 ∉ u.2 ∧ 3 ∉ v.2 ∧ ∀ x ∈ u.2, x ∉ v.2) : 3 ≤ s.length := by
  obtain ⟨u,hu,v,hv,hud,hvf,h3u,h3v,huv⟩ := known
  have mod_d : e % (2*d) = d := by rw [← Nat.mod_mod_of_dvd e hd, he, hdk]
  have mod_f : e % (2*f) = f := by rw [← Nat.mod_mod_of_dvd e hf, he, hfk]
  obtain ⟨x,hxu,hxs⟩ := hit u hu (hud ▸ mod_d)
  obtain ⟨y,hyv,hys⟩ := hit v hv (hvf ▸ mod_f)
  have hx : 3 ≠ x := fun eq => h3u (eq ▸ hxu)
  have hy : 3 ≠ y := fun eq => h3v (eq ▸ hyv)
  have hxy : x ≠ y := fun eq => huv x hxu (eq ▸ hyv)
  have nd : [3,x,y].Nodup := by simp [hx,hy,hxy]
  exact nd.length_le_of_subset (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem exclude_two {s : List Nat} {e k : Nat} (h3 : 3 ∈ s)
    (hit : ∀ r ∈ ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (Nat × List Nat)),
      e % (2*r.1) = r.1 → ∃ x ∈ r.2, x ∈ s)
    (hk : k ∈ ([
      45, 63, 66, 75, 99, 105, 110, 117, 153, 154, 165, 175, 195, 207, 255, 261,
      273, 279, 286, 333, 345, 374, 391, 418, 425, 429, 435, 465, 483, 493, 555,
      595, 609, 629, 663, 713, 759, 775, 777, 805, 851, 899, 925, 957, 1015,
      1073, 1085, 1131, 1147, 1209, 1221, 1295, 1443] : List Nat)) (he : e % (2*k) = k) : 3 ≤ s.length := by
  let rows : List (Nat × List Nat) := [(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])]
  let cert : List (Nat × Nat × Nat) := [
      (45, 9, 15), (63, 9, 21), (66, 6, 22), (75, 15, 25), (99, 9, 33), (105, 15,
      21), (110, 10, 22), (117, 9, 39), (153, 9, 17), (154, 14, 22), (165, 15, 33),
      (175, 25, 35), (195, 15, 39), (207, 9, 23), (255, 15, 17), (261, 9, 29), (273,
      21, 39), (279, 9, 31), (286, 22, 26), (333, 9, 37), (345, 15, 23), (374, 22,
      34), (391, 17, 23), (418, 22, 38), (425, 17, 25), (429, 33, 39), (435, 15, 29),
      (465, 15, 31), (483, 21, 23), (493, 17, 29), (555, 15, 37), (595, 17, 35),
      (609, 21, 29), (629, 17, 37), (663, 17, 39), (713, 23, 31), (759, 23, 33),
      (775, 25, 31), (777, 21, 37), (805, 23, 35), (851, 23, 37), (899, 29, 31),
      (925, 25, 37), (957, 29, 33), (1015, 29, 35), (1073, 29, 37), (1085, 31, 35),
      (1131, 29, 39), (1147, 31, 37), (1209, 31, 39), (1221, 33, 37), (1295, 35, 37),
      (1443, 37, 39)]
  have total : ∀ j ∈ ([
      45, 63, 66, 75, 99, 105, 110, 117, 153, 154, 165, 175, 195, 207, 255, 261,
      273, 279, 286, 333, 345, 374, 391, 418, 425, 429, 435, 465, 483, 493, 555,
      595, 609, 629, 663, 713, 759, 775, 777, 805, 851, 899, 925, 957, 1015,
      1073, 1085, 1131, 1147, 1209, 1221, 1295, 1443] : List Nat), ∃ t ∈ cert, t.1 = j := by decide
  have checked : ∀ t ∈ cert,
      2*t.2.1 ∣ 2*t.1 ∧ 2*t.2.2 ∣ 2*t.1 ∧
      t.1 % (2*t.2.1) = t.2.1 ∧ t.1 % (2*t.2.2) = t.2.2 ∧
      ∃ u ∈ rows, ∃ v ∈ rows, u.1 = t.2.1 ∧ v.1 = t.2.2 ∧
        3 ∉ u.2 ∧ 3 ∉ v.2 ∧ ∀ x ∈ u.2, x ∉ v.2 := by decide
  obtain ⟨t,ht,rfl⟩ := total k hk
  obtain ⟨hd,hf,hdk,hfk,hrows⟩ := checked t ht
  exact forced_pair h3 rows hit t.2.1 t.2.2 he hd hf hdk hfk hrows


theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1 := by
  rintro ⟨K₁,h₁⟩ ⟨K₂,h₂⟩
  let K := max K₁ K₂
  have fin := (Set.finite_Iic K).biUnion fun k _ =>
    OMA.R_Erdos1052_erdos_1052_R1.finite_card_primeFactors k
  obtain ⟨A,hA⟩ := (fin.image (padicValNat 2)).bddAbove
  refine ⟨A, ?_⟩
  intro n hn S hS hcard _ h3 hactive hit _ _
  have bound : n.primeFactors.card ≤ K := by
    by_cases h : ∃ k ∈ ([
      45, 63, 66, 75, 99, 105, 110, 117, 153, 154, 165, 175, 195, 207, 255, 261,
      273, 279, 286, 333, 345, 374, 391, 418, 425, 429, 435, 465, 483, 493, 555,
      595, 609, 629, 663, 713, 759, 775, 777, 805, 851, 899, 925, 957, 1015,
      1073, 1085, 1131, 1147, 1209, 1221, 1295, 1443] : List ℕ), n.factorization 3 % (2*k) = k
    · obtain ⟨k,hk,he⟩ := h
      have length_bound := exclude_two (s := S.toList) (e := n.factorization 3)
        (Finset.mem_toList.mpr h3) (by simpa only [Finset.mem_toList] using hit) hk he
      exact (h₁ n hn S hS h3 (by simpa using length_bound) ⟨k,hk,he⟩).trans (le_max_left _ _)
    · exact (h₂ n hn S hS h3 hcard hactive (fun k hk he => h ⟨k,hk,he⟩)).trans (le_max_right _ _)
  exact hA ⟨n, Set.mem_biUnion (x := n.primeFactors.card) (Set.mem_Iic.mpr bound) ⟨hn,rfl⟩, rfl⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1
