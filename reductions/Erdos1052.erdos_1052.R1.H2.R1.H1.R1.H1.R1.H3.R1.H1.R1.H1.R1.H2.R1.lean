import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H2.R1 of step
-- Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H2
-- Splits the open step (3 the only repeated odd prime, e = n.factorization 3 > 800, e % 4 != 2)
-- by the residue of e modulo 4, the three cases the step leaves open.  The residue decides
-- v_2(3^e + 1) and the small primes dividing it:
--   e = 0 mod 4: 3^e = 1 mod 8, so v_2(3^e+1) = 1 and 3^e+1 = 2 * odd;
--   e = 1 mod 4: e odd, v_2(3^e+1) = 2 and 3^e = 3 mod 8;
--   e = 3 mod 4: e odd, v_2(3^e+1) = 2 and 7 | 3^e+1 exactly when e = 3 mod 6 (here e = 3 mod 12).
-- The 2-adic part of the balance equation (2^a+1)(3^e+1) prod (q+1) = 2^(a+1) 3^e prod q reads
-- a + 1 = v_2(3^e+1) + sum_q v_2(q+1), which is different in the three cases, so the split carries
-- information (parity bookkeeping of a, and which small primes are forced into n).  Proving the
-- three classes closes the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H2_R1

def H1 : Prop :=
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 ≠ 2 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    n.factorization 3 % 4 = 0 →
    padicValNat 2 n ≤ A

def H2 : Prop :=
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 ≠ 2 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    n.factorization 3 % 4 = 1 →
    padicValNat 2 n ≤ A

def H3 : Prop :=
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 ≠ 2 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    n.factorization 3 % 4 = 3 →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨A1 + A2 + A3, fun n h hiff hbig hne hs1 hs2 hs3 => ?_⟩
  have hlt : n.factorization 3 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k : Fin 4, (k : ℕ) = n.factorization 3 % 4 := ⟨⟨_, hlt⟩, rfl⟩
  have hk2 : (k : ℕ) ≠ 2 := by rw [hk]; exact hne
  fin_cases k
  · have h0 : n.factorization 3 % 4 = 0 := by simpa using hk.symm
    have := h1 n h hiff hbig hne hs1 hs2 hs3 h0
    omega
  · have h1' : n.factorization 3 % 4 = 1 := by simpa using hk.symm
    have := h2 n h hiff hbig hne hs1 hs2 hs3 h1'
    omega
  · exact absurd rfl hk2
  · have h3' : n.factorization 3 % 4 = 3 := by simpa using hk.symm
    have := h3 n h hiff hbig hne hs1 hs2 hs3 h3'
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H2_R1
