import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1

/-!
For each fixed second repeated prime q, separate three sources of unbounded
prime count: the repeated support, the terminal simple primes, and the length
of a chain of simple primes in which each prime divides its successor plus one.
The parent table restricts q to a finite list, so bounds may depend on q.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R3

def H1 : Prop :=
  ∀ q : ℕ, ∃ B : ℕ,
    ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ S : Finset ℕ,
    (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 3 ∈ S → q ∈ S → q ≠ 3 →
    (∃ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ),
      n.factorization 3 % (2 * d) = d) → S.card ≤ B

def H2 : Prop :=
  ∀ q B : ℕ, ∃ W : ℕ,
    ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ S : Finset ℕ,
    (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 3 ∈ S → q ∈ S → q ≠ 3 →
    (∃ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ),
      n.factorization 3 % (2 * d) = d) → S.card ≤ B →
    let P := (n.primeFactors.erase 2).filter (fun p => p ∉ S)
    (P.filter (fun p => ∀ c ∈ P, ¬ c ∣ p + 1)).card ≤ W

def H3 : Prop :=
  ∀ q B W : ℕ, ∃ D : ℕ,
    ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ S : Finset ℕ,
    (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 3 ∈ S → q ∈ S → q ≠ 3 →
    (∃ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ),
      n.factorization 3 % (2 * d) = d) → S.card ≤ B →
    let P := (n.primeFactors.erase 2).filter (fun p => p ∉ S)
    (P.filter (fun p => ∀ c ∈ P, ¬ c ∣ p + 1)).card ≤ W →
    ∀ (f : ℕ → ℕ) (k : ℕ), (∀ i ≤ k, f i ∈ P) →
      (∀ i < k, f i ∣ f (i + 1) + 1) → k ≤ D

-- A simple odd prime can divide at most one other simple component plus one.
-- Starting from a terminal and following its unique parent thus recovers every
-- vertex in at most D steps when every divisibility chain has at most D edges.
theorem terminal_cover {P : Finset ℕ} {D : ℕ}
    (less : ∀ c ∈ P, ∀ p ∈ P, c ∣ p + 1 → c < p)
    (unique : ∀ c ∈ P, ∀ p ∈ P, ∀ q ∈ P, c ∣ p + 1 → c ∣ q + 1 → p = q)
    (depth : ∀ (f : ℕ → ℕ) (k : ℕ), (∀ i ≤ k, f i ∈ P) →
      (∀ i < k, f i ∣ f (i + 1) + 1) → k ≤ D) :
    P.card ≤ (D + 1) * (P.filter (fun p => ∀ c ∈ P, ¬ c ∣ p + 1)).card := by
  classical
  let T := P.filter (fun p => ∀ c ∈ P, ¬ c ∣ p + 1)
  let up (c : ℕ) := if h : ∃ p ∈ P, c ∣ p + 1 then h.choose else 0
  have hup {c p : ℕ} (hc : c ∈ P) (hp : p ∈ P) (hdiv : c ∣ p + 1) : up c = p := by
    have ex : ∃ q ∈ P, c ∣ q + 1 := ⟨p, hp, hdiv⟩
    dsimp only [up]
    rw [dif_pos ex]
    exact unique c hc _ ex.choose_spec.1 p hp ex.choose_spec.2 hdiv
  have reach : ∀ p ∈ P, ∃ t ∈ T, ∃ k : ℕ, up^[k] t = p ∧
      (∀ i ≤ k, up^[i] t ∈ P) ∧ (∀ i < k, up^[i] t ∣ up^[i + 1] t + 1) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      by_cases ht : ∀ c ∈ P, ¬ c ∣ p + 1
      · exact ⟨p, Finset.mem_filter.mpr ⟨hp, ht⟩, 0, rfl,
          fun i hi => by simpa [show i = 0 by omega] using hp,
          fun i hi => by omega⟩
      · push Not at ht
        obtain ⟨c, hc, hd⟩ := ht
        obtain ⟨t, ht, k, he, hm, hs⟩ := ih c (less c hc p hp hd) hc
        have hn : up^[k + 1] t = p := by rw [Function.iterate_succ_apply', he, hup hc hp hd]
        refine ⟨t, ht, k + 1, hn, ?_, ?_⟩
        · intro i hi
          by_cases h : i ≤ k
          · exact hm i h
          · simpa [show i = k + 1 by omega, hn] using hp
        · intro i hi
          by_cases h : i < k
          · exact hs i h
          · simpa only [show i = k by omega, hn, he] using hd
  have cover : P ⊆ (Finset.range (D + 1)).biUnion (fun k => T.image (up^[k])) := by
    intro p hp
    obtain ⟨t, ht, k, he, hm, hs⟩ := reach p hp
    have hk := depth (fun i => up^[i] t) k hm hs
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega),
      Finset.mem_image.mpr ⟨t, ht, he⟩⟩
  calc P.card ≤ _ := Finset.card_le_card cover
       _ ≤ ∑ k ∈ Finset.range (D + 1), (T.image (up^[k])).card := Finset.card_biUnion_le
       _ ≤ ∑ _k ∈ Finset.range (D + 1), T.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
       _ = _ := by simp [T]

-- The unitary balance prevents two different simple parents from consuming
-- the same simple odd prime.
theorem simple_unique {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) :
    let P := (n.primeFactors.erase 2).filter (fun p => p ∉ S)
    ∀ c ∈ P, ∀ p ∈ P, ∀ q ∈ P, c ∣ p + 1 → c ∣ q + 1 → p = q := by
  let P := (n.primeFactors.erase 2).filter (fun p => p ∉ S)
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ S → n.factorization r = 1 := by
    intro r hr hr2 hrS
    have hrp := Nat.prime_of_mem_primeFactors hr
    have h1 := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.fact_pos hr
    by_contra hne
    exact hrS ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)⟩)
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hh), Finset.ne_of_mem_erase hh⟩
  have E := OMA.R_Erdos1052_erdos_1052_R1_H2_R1.kernel_balance (N := S) h
    (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.two_dvd_of_isUnitaryPerfect h) hs
  have hK : ∀ c : ℕ, c.Prime →
      c ∣ ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), z ^ n.factorization z →
      c ∈ S := by
    intro c hc hcd
    obtain ⟨z, hz, hcz⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp hcd
    have hz' := (Finset.mem_filter.mp hz)
    have hzp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hz'.1)
    rw [(Nat.prime_dvd_prime_iff_eq hc hzp).mp (hc.dvd_of_dvd_pow hcz)]
    exact hz'.2
  have hu := (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.facts hP hK E).2.2.1
  change ∀ c ∈ P, ∀ p ∈ P, ∀ q ∈ P, c ∣ p + 1 → c ∣ q + 1 → p = q
  intro c hc p hp q hq
  exact hu c (hP c hc).1 (hP c hc).2 (Finset.mem_filter.mp hc).2 p hp q hq


theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1 := by
  classical
  intro h₁ h₂ h₃
  choose b hb using h₁
  choose w hw using h₂
  choose depth hd using h₃
  let rows := ([(6, [73, 37, 19, 5]), (8, [193, 97, 7]), (9, [37, 19]), (10, [5]),
      (12, [41, 6481, 7]), (14, [29, 5]), (15, [61, 31]), (16, [21523361, 61, 31]),
      (17, [103, 13, 307, 7]), (20, [41, 42521761, 21260881, 10630441, 139, 7]),
      (21, [7]), (22, [5501, 570461, 3067, 13, 7]),
      (23, [23535794707, 79, 74480363, 98519, 5]), (25, [151, 19, 22996651, 29, 5]),
      (26, [4795973261, 266442959, 5]), (28, [41, 430697, 3121, 7]),
      (29, [5385997, 2692999, 5]), (31, [6883, 1721, 41, 7]),
      (32, [926510094425921, 6883, 1721, 41, 7]), (33, [661, 331, 83, 7]),
      (34, [956353, 68311, 8539, 5]), (35, [547, 137, 374857981681, 2851, 23]),
      (37, [18427, 271, 17]), (38, [5301533, 126227, 157, 79, 5]), (39, [157, 79])] : List (ℕ × List ℕ))
  let Q := (rows.flatMap Prod.snd).toFinset
  let bound (q : ℕ) := 1 + b q + (depth q (b q) (w q (b q)) + 1) * w q (b q)
  let K := Q.sup bound
  have fin := (Set.finite_Iic K).biUnion fun k _ =>
    OMA.R_Erdos1052_erdos_1052_R1.finite_card_primeFactors k
  obtain ⟨A, hA⟩ := (fin.image (padicValNat 2)).bddAbove
  refine ⟨A, ?_⟩
  intro n hn S hS _ _ h3 hactive hit _ _
  push Not at hactive
  obtain ⟨d, hdm, hde⟩ := hactive
  have covers : ∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ),
      ∃ t ∈ rows, t.1 = d := by decide
  obtain ⟨t, ht, htd⟩ := covers d hdm
  obtain ⟨q, hqt, hqS⟩ := hit t ht (htd ▸ hde)
  have hqQ : q ∈ Q := List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨t, ht, hqt⟩)
  have hq3 : q ≠ 3 := by
    have h : 3 ∉ Q := by decide
    exact fun e => h (e ▸ hqQ)
  let P := (n.primeFactors.erase 2).filter (fun p => p ∉ S)
  have hcount := hb q n hn S hS h3 hqS hq3 ⟨d, hdm, hde⟩
  have hwidth := hw q (b q) n hn S hS h3 hqS hq3 ⟨d, hdm, hde⟩ hcount
  have hdepth := hd q (b q) (w q (b q)) n hn S hS h3 hqS hq3 ⟨d, hdm, hde⟩ hcount hwidth
  have hpP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h), Finset.ne_of_mem_erase h⟩
  have less : ∀ c ∈ P, ∀ p ∈ P, c ∣ p + 1 → c < p := by
    intro c hc p hp hcdiv
    have hh := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.two_mul_le
      (hpP c hc).1 (hpP c hc).2 (hpP p hp).1 (hpP p hp).2 hcdiv
    have := (hpP c hc).1.two_le
    omega
  have hcP := (terminal_cover less (simple_unique hn hS) hdepth).trans
    (Nat.mul_le_mul_left _ hwidth)
  have hsub : n.primeFactors ⊆ insert 2 (S ∪ P) := by
    intro p hp
    by_cases h2 : p = 2
    · simp [h2]
    by_cases hs : p ∈ S
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hs)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h2, hp⟩, hs⟩))
  have hc : n.primeFactors.card ≤ K := by
    have hu := Finset.card_union_le S P
    have hi := Finset.card_insert_le 2 (S ∪ P)
    have hnP := Finset.card_le_card hsub
    exact (show n.primeFactors.card ≤ bound q by dsimp [bound]; omega).trans (Finset.le_sup hqQ)
  exact hA ⟨n, Set.mem_biUnion (x := n.primeFactors.card) (Set.mem_Iic.mpr hc) ⟨hn, rfl⟩, rfl⟩

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R3
