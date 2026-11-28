import OMAStatements.S_mo_437111

namespace OMA.Mo437111Aux

open Finset

private def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

private lemma mem_smallPrimes_of_prime_lt {q : ℕ} (hq : q.Prime) (hq41 : q < 41) :
    q ∈ smallPrimes := by
  interval_cases q
  all_goals first | (simp [smallPrimes]; done) | (exfalso; revert hq; decide)

private lemma prime_of_smallPrimes_ok {p : ℕ} (hp1 : 1 < p) (hp2 : p < 1681)
    (hdiv : smallPrimes.all (fun q => Nat.beq q p || (p % q != 0)) = true) :
    p.Prime := by
  by_contra hnp
  let q := p.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqdvd : q ∣ p := Nat.minFac_dvd p
  have hq2 : q ^ 2 ≤ p := Nat.minFac_sq_le_self (by omega) hnp
  have hq41 : q < 41 := by
    have : q * q < 41 * 41 := by
      rw [← sq]
      exact lt_of_le_of_lt hq2 hp2
    nlinarith
  have hqm : q ∈ smallPrimes := mem_smallPrimes_of_prime_lt hq hq41
  rw [List.all_eq_true] at hdiv
  have hqok := hdiv q hqm
  simp only [Bool.or_eq_true, Nat.beq_eq, bne_iff_ne, ne_eq] at hqok
  rcases hqok with hqp | hmod
  · rw [hqp] at hq
    exact hnp hq
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp hqdvd)

private def checkList : ℕ → List ℕ → Bool
  | _, [] => true
  | n, p :: ps =>
      Nat.blt 1 p && Nat.blt p 1681 &&
        (smallPrimes.all (fun q => Nat.beq q p || (p % q != 0))) &&
        Nat.ble ((n - 1) / 2 + 1 + n) p &&
        Nat.blt ((n * (n - 1) / 2 + 3) % p) ((n - 1) / 2 + 1) &&
        checkList (n + 1) ps

private lemma exists_of_checkList (start : ℕ) (ps : List ℕ)
    (h : checkList start ps = true) (n : ℕ) (hn1 : start ≤ n) (hn2 : n < start + ps.length) :
    ∃ p : ℕ, p.Prime ∧ (n - 1) / 2 + 1 + n ≤ p ∧ (n * (n - 1) / 2 + 3) % p < (n - 1) / 2 + 1 := by
  induction ps generalizing start with
  | nil =>
    simp only [List.length_nil, add_zero] at hn2
    omega
  | cons p ps ih =>
    simp only [checkList, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    rcases h with ⟨⟨⟨⟨⟨hp1, hp2⟩, hdiv⟩, hle⟩, hmod⟩, hrest⟩
    by_cases hsn : n = start
    · subst hsn
      exact ⟨p, prime_of_smallPrimes_ok hp1 hp2 hdiv, hle, hmod⟩
    · apply ih (start + 1) hrest (by omega)
      simp only [List.length_cons] at hn2
      omega

private def wits_0 : List ℕ := [11, 17, 11, 29, 19, 23, 19, 23, 79, 23, 53, 29, 67, 31, 29, 31, 41, 113, 41, 67, 43, 41, 43, 47, 67, 53, 151, 61, 53, 61, 53, 79, 73, 139, 61, 71, 67, 71, 89, 67, 89, 73, 71, 101, 83, 101, 79, 83, 97, 83, 113, 109, 113, 97, 89, 97, 101, 157, 97, 167, 103, 101, 137, 103, 137, 109, 107, 127, 113, 149, 131, 149, 127, 149, 127, 131, 179, 127, 131, 139, 131, 151, 149, 173, 139, 137, 151, 139, 157, 167, 193, 151, 149, 157, 151, 197, 157, 197, 163, 157, 181, 163]
private lemma check_wits_0 : checkList 5 wits_0 = true := by rfl
private def wits_1 : List ℕ := [257, 179, 167, 181, 173, 193, 191, 173, 181, 179, 193, 181, 179, 193, 191, 193, 191, 211, 193, 191, 199, 193, 211, 199, 197, 227, 257, 211, 251, 223, 211, 229, 223, 211, 223, 227, 241, 223, 227, 229, 223, 241, 229, 227, 241, 229, 241, 239, 233, 241, 239, 257, 241, 281, 257, 271, 263, 251, 281, 257, 251, 269, 257, 271, 263, 271, 269, 263, 271, 269, 277, 271, 269, 277, 307, 283, 277, 311, 283, 281, 347, 283, 311, 293, 307, 359, 293, 311, 331, 307, 311, 347, 307, 331, 313, 307, 347, 313, 311, 383, 313, 331]
private lemma check_wits_1 : checkList 107 wits_1 = true := by rfl
private def wits_2 : List ℕ := [349, 317, 401, 349, 331, 367, 337, 331, 349, 337, 331, 349, 337, 349, 353, 337, 349, 347, 419, 349, 347, 431, 349, 367, 359, 353, 397, 359, 367, 397, 359, 367, 379, 373, 367, 379, 373, 401, 379, 373, 401, 379, 397, 389, 383, 401, 389, 397, 401, 389, 397, 431, 439, 397, 409, 433, 401, 409, 433, 431, 409, 421, 419, 409, 421, 419, 433, 421, 419, 457, 421, 433, 431, 439, 433, 431, 439, 433, 431, 439, 457, 487, 439, 461, 449, 443, 461, 449, 457, 461, 449, 457, 479, 463, 457, 479, 463, 461, 479, 463, 547, 503]
private lemma check_wits_2 : checkList 209 wits_2 = true := by rfl
private def wits_3 : List ℕ := [467, 479, 487, 491, 479, 487, 491, 479, 487, 499, 503, 487, 499, 503, 491, 499, 521, 541, 499, 521, 509, 499, 521, 509, 503, 521, 509, 521, 643, 523, 521, 571, 523, 521, 569, 523, 521, 563, 541, 587, 547, 541, 569, 547, 541, 563, 547, 541, 563, 547, 569, 557, 547, 569, 557, 601, 563, 557, 617, 563, 557, 569, 563, 571, 569, 577, 571, 569, 577, 571, 593, 577, 599, 587, 601, 593, 587, 619, 593, 587, 599, 593, 601, 599, 593, 601, 599, 607, 601, 613, 607, 619, 613, 607, 619, 613, 677, 619, 617, 659, 619, 631]
private lemma check_wits_3 : checkList 311 wits_3 = true := by rfl
private def wits_4 : List ℕ := [643, 647, 631, 643, 641, 631, 643, 641, 659, 643, 641, 659, 643, 641, 653, 643, 659, 653, 647, 659, 653, 661, 659, 677, 661, 659, 677, 661, 673, 691, 709, 673, 809, 683, 673, 709, 683, 677, 709, 683, 691, 709, 683, 691, 733, 701, 691, 727, 701, 709, 727, 701, 709, 727, 701, 709, 751, 719, 709, 751, 719, 727, 787, 719, 727, 739, 719, 727, 739, 733, 727, 739, 733, 769, 739, 733, 769, 739, 751, 769, 743, 751, 773, 757, 751, 773, 757, 751, 773, 757, 769, 787, 761, 769, 811, 809, 769, 811, 809, 769, 857, 823]
private lemma check_wits_4 : checkList 413 wits_4 = true := by rfl
private def wits_5 : List ℕ := [773, 809, 823, 787, 809, 797, 787, 809, 797, 787, 809, 797, 829, 823, 797, 809, 827, 811, 809, 827, 811, 809, 821, 811, 809, 821, 829, 823, 821, 829, 823, 821, 829, 823, 839, 829, 827, 839, 857, 911, 839, 857, 859, 839, 881, 859, 853, 911, 859, 853, 937, 859, 853, 919, 859, 857, 883, 859, 881, 883, 863, 919, 883, 877, 919, 883, 877, 971, 883, 877, 937, 883, 881, 907, 887, 919, 907, 911, 919, 907, 919, 937, 907, 919, 937, 907, 919, 937, 907, 919, 941, 911, 919, 941, 929, 919, 941, 929, 937, 1033, 929, 937]
private lemma check_wits_5 : checkList 515 wits_5 = true := by rfl
private def wits_6 : List ℕ := [1021, 929, 937, 983, 947, 937, 953, 947, 941, 953, 947, 983, 953, 947, 983, 953, 971, 983, 953, 1009, 983, 967, 1009, 977, 967, 983, 977, 967, 983, 977, 971, 983, 977, 1009, 983, 991, 1013, 983, 991, 1013, 997, 991, 1013, 997, 1009, 1021, 997, 1009, 1021, 1019, 1009, 1021, 1019, 1009, 1021, 1019, 1013, 1021, 1019, 1031, 1021, 1019, 1031, 1021, 1033, 1031, 1039, 1033, 1031, 1039, 1033, 1049, 1039, 1051, 1049, 1039, 1051, 1049, 1061, 1051, 1049, 1061, 1051, 1063, 1061, 1069, 1063, 1061, 1069, 1063, 1061, 1069, 1091, 1093, 1069, 1091, 1093, 1087, 1109, 1093, 1087, 1109]
private lemma check_wits_6 : checkList 617 wits_6 = true := by rfl
private def wits_7 : List ℕ := [1093, 1087, 1103, 1093, 1087, 1103, 1093, 1091, 1103, 1093, 1109, 1103, 1097, 1109, 1103, 1129, 1109, 1117, 1129, 1109, 1117, 1129, 1123, 1117, 1129, 1123, 1163, 1129, 1123, 1153, 1129, 1151, 1153, 1129, 1231, 1153, 1151, 1193, 1153, 1151, 1193, 1153, 1151, 1163, 1153, 1151, 1163, 1153, 1151, 1163, 1171, 1193, 1163, 1171, 1193, 1163, 1171, 1193, 1181, 1171, 1187, 1181, 1193, 1187, 1181, 1193, 1187, 1181, 1193, 1187, 1213, 1193, 1187, 1213, 1193, 1201, 1213, 1231, 1201, 1213, 1249, 1201, 1213, 1249, 1223, 1213, 1229, 1223, 1213, 1229, 1223, 1217, 1229, 1223, 1231, 1229, 1223, 1231, 1229, 1237, 1231, 1291]
private lemma check_wits_7 : checkList 719 wits_7 = true := by rfl
private def wits_8 : List ℕ := [1237, 1249, 1291, 1237, 1249, 1367, 1259, 1249, 1289, 1259, 1249, 1279, 1259, 1277, 1279, 1259, 1291, 1279, 1259, 1319, 1279, 1277, 1319, 1279, 1277, 1289, 1279, 1277, 1289, 1279, 1277, 1289, 1283, 1291, 1289, 1297, 1291, 1289, 1297, 1291, 1303, 1297, 1327, 1303, 1301, 1327, 1303, 1319, 1327, 1307, 1319, 1327, 1321, 1319, 1327, 1321, 1319, 1327, 1321, 1361, 1327, 1367, 1361, 1327, 1367, 1361, 1373, 1367, 1361, 1373, 1367, 1399, 1373, 1361, 1423, 1367, 1361, 1423, 1367, 1361, 1373, 1367, 1361, 1373, 1367, 1361, 1373, 1367, 1423, 1373, 1367, 1427, 1373, 1381, 1427, 1429, 1381, 1451, 1429, 1381, 1471, 1429]
private lemma check_wits_8 : checkList 821 wits_8 = true := by rfl
private def wits_9 : List ℕ := [1399, 1459, 1409, 1399, 1439, 1409, 1399, 1429, 1409, 1399, 1429, 1409, 1459, 1429, 1409, 1459, 1429, 1423, 1459, 1429, 1423, 1439, 1429, 1423, 1439, 1429, 1427, 1439, 1429, 1459, 1439, 1433, 1459, 1439, 1447, 1459, 1439, 1447, 1459, 1453, 1447, 1459, 1453, 1451, 1459, 1453, 1483, 1459, 1471, 1483, 1481, 1471, 1483, 1481, 1471, 1483, 1481, 1471, 1483, 1481, 1489, 1483, 1481, 1489, 1483, 1499, 1489, 1487, 1499, 1489, 1543, 1499, 1493, 1543, 1499, 1511, 1523, 1531, 1511, 1523, 1531, 1511, 1523, 1531, 1511, 1523, 1531, 1543, 1523, 1531, 1543, 1523, 1531, 1543, 1579, 1531, 1543, 1579, 1549, 1543, 1559]
private lemma check_wits_9 : checkList 923 wits_9 = true := by rfl

private lemma small_witnesses (n : ℕ) (hn1 : 5 ≤ n) (hn2 : n < 1024) :
    ∃ p : ℕ, p.Prime ∧ (n - 1) / 2 + 1 + n ≤ p ∧ (n * (n - 1) / 2 + 3) % p < (n - 1) / 2 + 1 := by
  by_cases h_0 : n < 107
  · exact exists_of_checkList 5 wits_0 check_wits_0 n (by omega) h_0
  by_cases h_1 : n < 209
  · exact exists_of_checkList 107 wits_1 check_wits_1 n (by omega) h_1
  by_cases h_2 : n < 311
  · exact exists_of_checkList 209 wits_2 check_wits_2 n (by omega) h_2
  by_cases h_3 : n < 413
  · exact exists_of_checkList 311 wits_3 check_wits_3 n (by omega) h_3
  by_cases h_4 : n < 515
  · exact exists_of_checkList 413 wits_4 check_wits_4 n (by omega) h_4
  by_cases h_5 : n < 617
  · exact exists_of_checkList 515 wits_5 check_wits_5 n (by omega) h_5
  by_cases h_6 : n < 719
  · exact exists_of_checkList 617 wits_6 check_wits_6 n (by omega) h_6
  by_cases h_7 : n < 821
  · exact exists_of_checkList 719 wits_7 check_wits_7 n (by omega) h_7
  by_cases h_8 : n < 923
  · exact exists_of_checkList 821 wits_8 check_wits_8 n (by omega) h_8
  by_cases h_9 : n < 1024
  · exact exists_of_checkList 923 wits_9 check_wits_9 n (by omega) h_9
  omega

private lemma dvd_choose_of_mod_lt (A B p : ℕ) (hp : p.Prime) (_hBA : B ≤ A) (hBp : B < p)
    (hmod : A % p < B) : p ∣ A.choose B := by
  have hdvd_desc : p ∣ A.descFactorial B := by
    have h1 : p ∣ A - A % p := ⟨A / p, by have := Nat.div_add_mod A p; omega⟩
    have h2 : A - A % p ∣ A.descFactorial B := by
      rw [Nat.descFactorial_eq_prod_range]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hmod)
    exact h1.trans h2
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdvd_desc
  have hnot : ¬ (p ∣ B.factorial) := hp.dvd_factorial.not.mpr (by omega)
  exact (hp.dvd_mul.mp hdvd_desc).resolve_left hnot

private lemma gcd_gt_one_of_prime_dvd_choose (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hpM : (n - 1) / 2 + 1 + n ≤ p)
    (hpdvd : p ∣ (n * (n - 1) / 2 + 3).choose ((n - 1) / 2 + 1)) :
    1 < (Finset.range n).gcd (fun k =>
      (n * (n - 1) / 2 + 3 + k).choose ((n - 1) / 2 + 1 + k)) := by
  set A := n * (n - 1) / 2 + 3
  set B := (n - 1) / 2 + 1
  have hBA : B ≤ A := by
    have h1 : n - 1 ≤ n * (n - 1) := Nat.le_mul_of_pos_left (n - 1) (by omega)
    have h2 : (n - 1) / 2 ≤ n * (n - 1) / 2 := Nat.div_le_div_right h1
    omega
  have hdvd_desc : p ∣ A.descFactorial B := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hpdvd _
  rw [Nat.descFactorial_eq_prod_range] at hdvd_desc
  obtain ⟨i, hi_mem, hi_dvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd_desc
  rw [Finset.mem_range] at hi_mem
  have hg_dvd : p ∣ (Finset.range n).gcd (fun k => (A + k).choose (B + k)) := by
    refine Finset.dvd_gcd fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hki_mem : k + i ∈ Finset.range (B + k) := Finset.mem_range.mpr (by omega)
    have hki_eq : A + k - (k + i) = A - i := by omega
    have hdvd_k : p ∣ (A + k).descFactorial (B + k) := by
      rw [Nat.descFactorial_eq_prod_range]
      refine hi_dvd.trans ?_
      rw [← hki_eq]
      exact Finset.dvd_prod_of_mem _ hki_mem
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hdvd_k
    have hnot : ¬ (p ∣ (B + k).factorial) := hp.dvd_factorial.not.mpr (by omega)
    exact (hp.dvd_mul.mp hdvd_k).resolve_left hnot
  have hgcd_ne : (Finset.range n).gcd (fun k => (A + k).choose (B + k)) ≠ 0 := by
    intro h0
    have h0' : (Finset.range n).gcd (fun k => (A + k).choose (B + k)) ∣ (A + 0).choose (B + 0) :=
      Finset.gcd_dvd (Finset.mem_range.mpr (by omega))
    rw [h0, zero_dvd_iff] at h0'
    have hpos : 0 < A.choose B := Nat.choose_pos hBA
    simp only [add_zero] at h0'
    omega
  have hple : p ≤ (Finset.range n).gcd (fun k => (A + k).choose (B + k)) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hgcd_ne) hg_dvd
  exact lt_of_lt_of_le hp.one_lt hple

private lemma four_pow_mul_factorial_sq_le (b : ℕ) :
    4 ^ b * (b.factorial) ^ 2 ≤ (b + 1) ^ (2 * b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h2 : 2 * (b + 1) ^ (b + 1) ≤ (b + 2) ^ (b + 1) := by
      have hexp : (b + 2) ^ (b + 1) =
          ∑ i ∈ Finset.range (b + 2), (b + 1) ^ i * (b + 1).choose i := by
        rw [show b + 2 = (b + 1) + 1 by omega, add_pow]
        simp only [one_pow, mul_one, Nat.cast_id]
      rw [hexp]
      have hsub : ({b, b + 1} : Finset ℕ) ⊆ Finset.range (b + 2) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
      have hle := Finset.sum_le_sum_of_subset
        (f := fun i => (b + 1) ^ i * (b + 1).choose i) hsub
      rw [Finset.sum_pair (by omega)] at hle
      have hcb : (b + 1).choose b = b + 1 := by
        rw [show (b + 1) = 1 + b by omega, ← Nat.choose_symm_add, Nat.choose_one_right]
      simp only [hcb, Nat.choose_self, mul_one] at hle
      have hpow : (b + 1) ^ b * (b + 1) = (b + 1) ^ (b + 1) := by ring
      linarith
    have h4 : 4 * (b + 1) ^ (2 * b + 2) ≤ (b + 2) ^ (2 * b + 2) := by
      calc
        4 * (b + 1) ^ (2 * b + 2) = (2 * (b + 1) ^ (b + 1)) ^ 2 := by ring
        _ ≤ ((b + 2) ^ (b + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (b + 2) ^ (2 * b + 2) := by ring
    calc
      4 ^ (b + 1) * ((b + 1).factorial) ^ 2
          = 4 * (b + 1) ^ 2 * (4 ^ b * (b.factorial) ^ 2) := by rw [Nat.factorial_succ]; ring
      _ ≤ 4 * (b + 1) ^ 2 * (b + 1) ^ (2 * b) := Nat.mul_le_mul_left _ ih
      _ = 4 * (b + 1) ^ (2 * b + 2) := by ring
      _ ≤ (b + 2) ^ (2 * b + 2) := h4
      _ = (b + 1 + 1) ^ (2 * (b + 1)) := by ring_nf

private lemma descFactorial_sq_ge (A B : ℕ) (hBA : B ≤ A) :
    (A * (A - B + 1)) ^ B ≤ (A.descFactorial B) ^ 2 := by
  rw [Nat.descFactorial_eq_prod_range, sq]
  conv_rhs => rhs; rw [← Finset.prod_range_reflect]
  rw [← Finset.prod_mul_distrib]
  calc
    (A * (A - B + 1)) ^ B = ∏ _i ∈ Finset.range B, (A * (A - B + 1)) := by simp
    _ ≤ ∏ i ∈ Finset.range B, (A - i) * (A - (B - 1 - i)) := by
      refine Finset.prod_le_prod' fun i hi => ?_
      rw [Finset.mem_range] at hi
      zify [hBA, show 1 ≤ B by omega, show i ≤ A by omega, show B - 1 - i ≤ A by omega, show i ≤ B - 1 by omega]
      nlinarith

private lemma choose_sq_lower_bound (A B : ℕ) (hBA : B ≤ A) :
    4 ^ B * (A * (A - B + 1)) ^ B ≤ (B + 1) ^ (2 * B) * (A.choose B) ^ 2 := by
  calc
    4 ^ B * (A * (A - B + 1)) ^ B
        ≤ 4 ^ B * (A.descFactorial B) ^ 2 := Nat.mul_le_mul_left _ (descFactorial_sq_ge A B hBA)
    _ = (4 ^ B * (B.factorial) ^ 2) * (A.choose B) ^ 2 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
    _ ≤ (B + 1) ^ (2 * B) * (A.choose B) ^ 2 :=
        Nat.mul_le_mul_right _ (four_pow_mul_factorial_sq_le B)

private lemma prod_primes_Ioc_le_two_pow (b : ℕ) :
    ∏ p ∈ Nat.primesLE b \ Nat.primesLE ((b + 1) / 2), p ≤ 2 ^ b := by
  set h := (b + 1) / 2
  have hdvd : (∏ p ∈ Nat.primesLE b \ Nat.primesLE h, p) ∣ b.choose h := by
    refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
    · exact (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).prime
    · obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
      have hprime := Nat.prime_of_mem_primesLE hp1
      have hpb : p ≤ b := (Nat.mem_primesLE.mp hp1).1
      have hph : h < p := by
        by_contra hle
        exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hprime⟩)
      exact hprime.dvd_choose hph (by omega) hpb
  exact (Nat.le_of_dvd (Nat.choose_pos (by omega)) hdvd).trans (Nat.choose_le_two_pow b h)

private lemma card_primes_Ioc_log_le (b : ℕ) (hb : 3 ≤ b) :
    (((Nat.primesLE b \ Nat.primesLE ((b + 1) / 2)).card : ℝ)) *
      Real.log (((b + 1) / 2 : ℕ) : ℝ) ≤ (b : ℝ) * Real.log 2 := by
  set h := (b + 1) / 2
  have hh_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
  have hpow : h ^ (Nat.primesLE b \ Nat.primesLE h).card ≤ 2 ^ b := by
    calc
      h ^ (Nat.primesLE b \ Nat.primesLE h).card
          = ∏ _p ∈ Nat.primesLE b \ Nat.primesLE h, h := by simp
      _ ≤ ∏ p ∈ Nat.primesLE b \ Nat.primesLE h, p := by
          refine Finset.prod_le_prod' fun p hp => ?_
          obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
          have hprime := Nat.prime_of_mem_primesLE hp1
          by_contra hlt
          exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hprime⟩)
      _ ≤ 2 ^ b := prod_primes_Ioc_le_two_pow b
  have hreal : ((h : ℝ) ^ (Nat.primesLE b \ Nat.primesLE h).card) ≤ (2 : ℝ) ^ b := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hh_pos _) hreal
  rwa [Real.log_pow, Real.log_pow] at hlog

private lemma card_primesLE_le_div_three (m : ℕ) :
    (Nat.primesLE m).card ≤ m / 3 + 3 := by
  let S23 : Finset ℕ := {2, 3}
  let S6 : Finset ℕ := (Nat.primesLE m).filter (fun p => p % 6 = 1 ∨ p % 6 = 5)
  have hsub : Nat.primesLE m ⊆ S23 ∪ S6 := by
    intro p hp
    have hpr := Nat.prime_of_mem_primesLE hp
    by_cases h2 : p = 2
    · exact Finset.mem_union_left _ (by simp [S23, h2])
    by_cases h3 : p = 3
    · exact Finset.mem_union_left _ (by simp [S23, h3])
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, ?_⟩)
    have hd2 : ¬ 2 ∣ p := fun h => h2 (hpr.eq_one_or_self_of_dvd 2 h |>.resolve_left (by omega) |>.symm)
    have hd3 : ¬ 3 ∣ p := fun h => h3 (hpr.eq_one_or_self_of_dvd 3 h |>.resolve_left (by omega) |>.symm)
    omega
  have hS23 : S23.card ≤ 2 := Finset.card_le_two
  have hS6 : S6.card ≤ m / 3 + 1 := by
    let f : ℕ → ℕ := fun p => 2 * (p / 6) + if p % 6 = 1 then 0 else 1
    have hinj : ∀ p ∈ S6, ∀ q ∈ S6, f p = f q → p = q := by
      intro p hp q hq heq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      dsimp only [f] at heq
      rcases hp' with hp1 | hp5 <;> rcases hq' with hq1 | hq5 <;> simp_all <;> omega
    have hmaps : ∀ p ∈ S6, f p ∈ Finset.range (m / 3 + 1) := by
      intro p hp
      obtain ⟨hpm, hp6⟩ := Finset.mem_filter.mp hp
      have hpm' : p ≤ m := (Nat.mem_primesLE.mp hpm).1
      rw [Finset.mem_range]
      dsimp only [f]
      rcases hp6 with hp1 | hp5 <;> simp_all <;> omega
    exact (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq (Finset.card_range _)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

private lemma card_odd_Ioc_le (S H : ℕ) (hSH : S ≤ H) :
    ((Nat.primesLE H \ Nat.primesLE S).filter (fun p => p % 2 = 1)).card ≤ (H - S) / 2 + 1 := by
  let T := (Nat.primesLE H \ Nat.primesLE S).filter (fun p => p % 2 = 1)
  let f : ℕ → ℕ := fun p => (p - (S + 1)) / 2
  have hmaps : ∀ p ∈ T, f p ∈ Finset.range ((H - S) / 2 + 1) := by
    intro p hp
    obtain ⟨hps, hodd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hps
    have hpH : p ≤ H := (Nat.mem_primesLE.mp hp1).1
    have hpr := Nat.prime_of_mem_primesLE hp1
    have hSp : S + 1 ≤ p := by
      by_contra hlt
      exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hpr⟩)
    rw [Finset.mem_range]
    dsimp only [f]
    omega
  have hinj : ∀ p ∈ T, ∀ q ∈ T, f p = f q → p = q := by
    intro p hp q hq heq
    obtain ⟨hps, hpodd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqs, hqodd⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hps
    obtain ⟨hq1, hq2⟩ := Finset.mem_sdiff.mp hqs
    have hppr := Nat.prime_of_mem_primesLE hp1
    have hqpr := Nat.prime_of_mem_primesLE hq1
    have hSp : S + 1 ≤ p := by by_contra h; exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hppr⟩)
    have hSq : S + 1 ≤ q := by by_contra h; exact hq2 (Nat.mem_primesLE.mpr ⟨by omega, hqpr⟩)
    dsimp only [f] at heq
    omega
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq (Finset.card_range _)

private lemma choose_ub_of_no_large_prime (A B M S H : ℕ)
    (hBA : B ≤ A) (hA_pos : 0 < A) (hH_pos : 0 < H) (hS2 : 2 ≤ S)
    (hSH : S ≤ H) (hHM : H ≤ M) (hMA : M ≤ A)
    (hH_eq : H = (M + 1) / 2) (hA_lt_S1 : A < (S + 1) ^ 2)
    (hno : ∀ p : ℕ, p.Prime → M < p → ¬ p ∣ A.choose B) :
    A.choose B ≤ A ^ (Nat.primesLE S).card * H ^ ((H - S) / 2 + 1) * 2 ^ M := by
  have hprod_eq : A.choose B = ∏ p ∈ Nat.primesLE M, p ^ (A.choose B).factorization p := by
    symm
    conv_rhs => rw [← Nat.prod_pow_factorization_choose A B hBA]
    refine Finset.prod_subset (fun p hp => ?_) (fun p _ hnp => ?_)
    · rw [Finset.mem_range]
      have hpM : p ≤ M := (Nat.mem_primesLE.mp hp).1
      omega
    · rw [Nat.mem_primesLE] at hnp
      rcases em' p.Prime with hnp' | hpr
      · rw [Nat.factorization_eq_zero_of_not_prime _ hnp', pow_zero]
      · have hMp : M < p := by
          by_contra hle
          exact hnp ⟨not_lt.mp hle, hpr⟩
        rw [Nat.factorization_eq_zero_of_not_dvd (hno p hpr hMp), pow_zero]
  have hsubSH : Nat.primesLE S ⊆ Nat.primesLE H := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hSH, Nat.prime_of_mem_primesLE hp⟩
  have hsubHM : Nat.primesLE H ⊆ Nat.primesLE M := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hHM, Nat.prime_of_mem_primesLE hp⟩
  have hsplit1 :
      ∏ p ∈ Nat.primesLE M, p ^ (A.choose B).factorization p =
        (∏ p ∈ Nat.primesLE H, p ^ (A.choose B).factorization p) *
          (∏ p ∈ Nat.primesLE M \ Nat.primesLE H, p ^ (A.choose B).factorization p) := by
    rw [← Finset.prod_sdiff hsubHM, mul_comm]
  have hsplit2 :
      ∏ p ∈ Nat.primesLE H, p ^ (A.choose B).factorization p =
        (∏ p ∈ Nat.primesLE S, p ^ (A.choose B).factorization p) *
          (∏ p ∈ Nat.primesLE H \ Nat.primesLE S, p ^ (A.choose B).factorization p) := by
    rw [← Finset.prod_sdiff hsubSH, mul_comm]
  have hP1 : ∏ p ∈ Nat.primesLE S, p ^ (A.choose B).factorization p ≤ A ^ (Nat.primesLE S).card := by
    calc
      ∏ p ∈ Nat.primesLE S, p ^ (A.choose B).factorization p
          ≤ ∏ _p ∈ Nat.primesLE S, A := Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hA_pos
      _ = A ^ (Nat.primesLE S).card := by simp
  have hP2 :
      ∏ p ∈ Nat.primesLE H \ Nat.primesLE S, p ^ (A.choose B).factorization p ≤
        H ^ ((H - S) / 2 + 1) := by
    have hfilt :
        Nat.primesLE H \ Nat.primesLE S =
          (Nat.primesLE H \ Nat.primesLE S).filter (fun p => p % 2 = 1) := by
      ext p
      constructor
      · intro hp
        refine Finset.mem_filter.mpr ⟨hp, ?_⟩
        obtain ⟨hp1, hnot⟩ := Finset.mem_sdiff.mp hp
        have hpr := Nat.prime_of_mem_primesLE hp1
        have hpgt2 : 2 < p := by
          by_contra hle
          exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hpr⟩)
        exact hpr.mod_two_eq_one_iff_ne_two.mpr (by omega)
      · intro hp
        exact (Finset.mem_filter.mp hp).1
    have hle_H :
        ∏ p ∈ Nat.primesLE H \ Nat.primesLE S, p ^ (A.choose B).factorization p ≤
          ∏ _p ∈ Nat.primesLE H \ Nat.primesLE S, H := by
      refine Finset.prod_le_prod' fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
      have hpr := Nat.prime_of_mem_primesLE hp1
      have hpH : p ≤ H := (Nat.mem_primesLE.mp hp1).1
      have hSp : S < p := by by_contra hle; exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hpr⟩)
      have hfz : (A.choose B).factorization p ≤ 1 := by
        refine Nat.factorization_choose_le_one ?_
        exact lt_of_lt_of_le hA_lt_S1 (Nat.pow_le_pow_left hSp 2)
      calc
        p ^ (A.choose B).factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hpr.pos hfz
        _ = p := pow_one p
        _ ≤ H := hpH
    have hcard : (Nat.primesLE H \ Nat.primesLE S).card ≤ (H - S) / 2 + 1 := by
      rw [hfilt]
      exact card_odd_Ioc_le S H hSH
    calc
      ∏ p ∈ Nat.primesLE H \ Nat.primesLE S, p ^ (A.choose B).factorization p
          ≤ H ^ (Nat.primesLE H \ Nat.primesLE S).card := by simpa using hle_H
      _ ≤ H ^ ((H - S) / 2 + 1) := Nat.pow_le_pow_right hH_pos hcard
  have hP3 :
      ∏ p ∈ Nat.primesLE M \ Nat.primesLE H, p ^ (A.choose B).factorization p ≤ 2 ^ M := by
    calc
      ∏ p ∈ Nat.primesLE M \ Nat.primesLE H, p ^ (A.choose B).factorization p
          ≤ ∏ p ∈ Nat.primesLE M \ Nat.primesLE H, p := by
            refine Finset.prod_le_prod' fun p hp => ?_
            obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
            have hpr := Nat.prime_of_mem_primesLE hp1
            have hHp : H < p := by by_contra hle; exact hp2 (Nat.mem_primesLE.mpr ⟨by omega, hpr⟩)
            have hSp : S < p := lt_of_le_of_lt hSH hHp
            have hfz : (A.choose B).factorization p ≤ 1 := by
              refine Nat.factorization_choose_le_one ?_
              exact lt_of_lt_of_le hA_lt_S1 (Nat.pow_le_pow_left hSp 2)
            exact (Nat.pow_le_pow_right hpr.pos hfz).trans_eq (pow_one p)
      _ ≤ 2 ^ M := by rw [hH_eq]; exact prod_primes_Ioc_le_two_pow M
  rw [hprod_eq, hsplit1, hsplit2]
  calc
    (∏ p ∈ Nat.primesLE S, p ^ (A.choose B).factorization p) *
          (∏ p ∈ Nat.primesLE H \ Nat.primesLE S, p ^ (A.choose B).factorization p) *
        (∏ p ∈ Nat.primesLE M \ Nat.primesLE H, p ^ (A.choose B).factorization p)
        ≤ (A ^ (Nat.primesLE S).card * H ^ ((H - S) / 2 + 1)) * 2 ^ M := by gcongr

private lemma choose_log_lb (n A B : ℕ) (hn : 1024 ≤ n) (hBA : B ≤ A) (hnB : n ≤ 2 * B)
    (hAB_quad : 392 * n ^ 2 * (B + 1) ^ 2 ≤ 100 * (4 * A * (A - B + 1))) :
    (n : ℝ) * (0.5 * Real.log (n : ℝ) + 0.5 * Real.log 2 - 1 / 196) ≤
      Real.log (A.choose B : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hB1_rpos : (0 : ℝ) < ((B + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < B + 1)
  have hu_ge : 10 * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h1024 : ((2 ^ 10 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ^ 10 ≤ n)
    have := Real.log_le_log (by positivity) h1024
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_ofNat] at this
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h_lb_nat : 4 ^ B * (A * (A - B + 1)) ^ B ≤ (B + 1) ^ (2 * B) * (A.choose B) ^ 2 :=
    choose_sq_lower_bound A B hBA
  have h_lb_real : ((392 : ℝ) / 100 * (n : ℝ) ^ 2) ^ B ≤ ((A.choose B : ℝ) ^ 2) := by
    have hAB_real :
        (392 : ℝ) / 100 * (n : ℝ) ^ 2 * ((B + 1 : ℕ) : ℝ) ^ 2 ≤
          4 * (A : ℝ) * ((A - B + 1 : ℕ) : ℝ) := by
      have hcast :
          ((392 * n ^ 2 * (B + 1) ^ 2 : ℕ) : ℝ) ≤
            ((100 * (4 * A * (A - B + 1)) : ℕ) : ℝ) := by exact_mod_cast hAB_quad
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
      linarith
    have hdiv :
        (392 : ℝ) / 100 * (n : ℝ) ^ 2 ≤
          4 * (A : ℝ) * ((A - B + 1 : ℕ) : ℝ) / ((B + 1 : ℕ) : ℝ) ^ 2 := by
      rwa [le_div_iff₀ (sq_pos_of_pos hB1_rpos)]
    have hpow1 :
        ((392 : ℝ) / 100 * (n : ℝ) ^ 2) ^ B ≤
          (4 * (A : ℝ) * ((A - B + 1 : ℕ) : ℝ) / ((B + 1 : ℕ) : ℝ) ^ 2) ^ B :=
      pow_le_pow_left₀ (by positivity) hdiv B
    have hlb_r :
        (4 : ℝ) ^ B * ((A : ℝ) * ((A - B + 1 : ℕ) : ℝ)) ^ B ≤
          ((B + 1 : ℕ) : ℝ) ^ (2 * B) * (A.choose B : ℝ) ^ 2 := by
      exact_mod_cast h_lb_nat
    have hpow2 :
        (4 * (A : ℝ) * ((A - B + 1 : ℕ) : ℝ) / ((B + 1 : ℕ) : ℝ) ^ 2) ^ B ≤
          (A.choose B : ℝ) ^ 2 := by
      rw [div_pow, ← pow_mul, div_le_iff₀ (pow_pos hB1_rpos (2 * B))]
      calc
        (4 * (A : ℝ) * ((A - B + 1 : ℕ) : ℝ)) ^ B
            = 4 ^ B * ((A : ℝ) * ((A - B + 1 : ℕ) : ℝ)) ^ B := by
              rw [← mul_pow]; ring_nf
        _ ≤ ((B + 1 : ℕ) : ℝ) ^ (2 * B) * (A.choose B : ℝ) ^ 2 := hlb_r
        _ = (A.choose B : ℝ) ^ 2 * ((B + 1 : ℕ) : ℝ) ^ (2 * B) := mul_comm _ _
    exact hpow1.trans hpow2
  have hlog := Real.log_le_log (by positivity) h_lb_real
  rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hlog
  have h392 :
      2 * Real.log (n : ℝ) + 2 * Real.log 2 - 1 / 49 ≤
        Real.log ((392 : ℝ) / 100 * (n : ℝ) ^ 2) := by
    have hmul : (392 : ℝ) / 100 * (n : ℝ) ^ 2 = (4 * (n : ℝ) ^ 2) / ((100 : ℝ) / 98) := by ring
    rw [hmul, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (pow_ne_zero 2 hn_pos.ne'), Real.log_pow, Nat.cast_ofNat]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
    have h100 : Real.log ((100 : ℝ) / 98) ≤ 1 / 49 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (100 : ℝ) / 98)
      linarith
    linarith
  have hstep1 :
      (B : ℝ) * (2 * Real.log (n : ℝ) + 2 * Real.log 2 - 1 / 49) ≤
        2 * Real.log (A.choose B : ℝ) :=
    (mul_le_mul_of_nonneg_left h392 (by positivity)).trans hlog
  have hBn : (n : ℝ) / 2 ≤ (B : ℝ) := by
    have : (n : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast hnB
    linarith
  have hfac_pos : 0 ≤ 2 * Real.log (n : ℝ) + 2 * Real.log 2 - 1 / 49 := by linarith
  have hstep2 :
      ((n : ℝ) / 2) * (2 * Real.log (n : ℝ) + 2 * Real.log 2 - 1 / 49) ≤
        (B : ℝ) * (2 * Real.log (n : ℝ) + 2 * Real.log 2 - 1 / 49) :=
    mul_le_mul_of_nonneg_right hBn hfac_pos
  linarith

private lemma piS_logA_ub (n A S : ℕ) (hn : 1024 ≤ n) (hA_pos : 0 < A) (hA_le : 2 * A ≤ n ^ 2)
    (hS_lo_sq : 49 * n ^ 2 ≤ 100 * S ^ 2) (hS_lo : 7 * n ≤ 10 * S) (hS_hi : 100 * S ≤ 71 * n) :
    ((Nat.primesLE S).card : ℝ) * Real.log (A : ℝ) ≤
      (n : ℝ) * ((0.038 : ℝ) * Real.log (n : ℝ) - 0.019 * Real.log 2 +
        (0.710 * 2.24 + 0.356 * 2.54 + 0.179 * 2.93 + 0.090 * 3.47) * Real.log 2) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hA_rpos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA_pos
  have hu_ge : 10 * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h1024 : ((2 ^ 10 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ^ 10 ≤ n)
    have := Real.log_le_log (by positivity) h1024
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_ofNat] at this
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlogA_ub : Real.log (A : ℝ) ≤ 2 * Real.log (n : ℝ) - Real.log 2 := by
    have h2A_r : (2 : ℝ) * (A : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hA_le
    have hA_le' : (A : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by linarith
    have hlog := Real.log_le_log hA_rpos hA_le'
    rwa [Real.log_div (pow_ne_zero 2 hn_pos.ne') two_ne_zero, Real.log_pow, Nat.cast_ofNat] at hlog
  have hlogS_lb : Real.log (n : ℝ) - 0.5 * Real.log 2 - 1 / 98 ≤ Real.log (S : ℝ) := by
    have h49 : (49 : ℝ) * (n : ℝ) ^ 2 ≤ 100 * (S : ℝ) ^ 2 := by exact_mod_cast hS_lo_sq
    have h100 : (n : ℝ) ^ 2 / ((100 : ℝ) / 49) ≤ (S : ℝ) ^ 2 := by linarith
    have hlog := Real.log_le_log (by positivity) h100
    rw [Real.log_div (pow_ne_zero 2 hn_pos.ne') (by norm_num),
        Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hlog
    have hdiv2 : (100 : ℝ) / 49 = 2 * ((50 : ℝ) / 49) := by norm_num
    have h50 : Real.log ((50 : ℝ) / 49) ≤ 1 / 49 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (50 : ℝ) / 49)
      linarith
    have h100_49 : Real.log ((100 : ℝ) / 49) ≤ Real.log 2 + 1 / 49 := by
      rw [hdiv2, Real.log_mul two_ne_zero (by norm_num)]
      linarith
    linarith
  set b0 := S
  set b1 := (b0 + 1) / 2
  set b2 := (b1 + 1) / 2
  set b3 := (b2 + 1) / 2
  set b4 := (b3 + 1) / 2
  have hb1_le : b1 ≤ b0 := by dsimp only [b1]; omega
  have hb2_le : b2 ≤ b1 := by dsimp only [b2]; omega
  have hb3_le : b3 ≤ b2 := by dsimp only [b3]; omega
  have hb4_le : b4 ≤ b3 := by dsimp only [b4]; omega
  have hb0_ub : (b0 : ℝ) ≤ (0.710 : ℝ) * (n : ℝ) := by
    have : 1000 * b0 ≤ 710 * n := by omega
    have hcast : ((1000 * b0 : ℕ) : ℝ) ≤ ((710 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast; linarith
  have hb1_ub : (b1 : ℝ) ≤ (0.356 : ℝ) * (n : ℝ) := by
    have : 1000 * b1 ≤ 356 * n := by dsimp only [b1]; omega
    have hcast : ((1000 * b1 : ℕ) : ℝ) ≤ ((356 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast; linarith
  have hb2_ub : (b2 : ℝ) ≤ (0.179 : ℝ) * (n : ℝ) := by
    have : 1000 * b2 ≤ 179 * n := by dsimp only [b2, b1]; omega
    have hcast : ((1000 * b2 : ℕ) : ℝ) ≤ ((179 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast; linarith
  have hb3_ub : (b3 : ℝ) ≤ (0.090 : ℝ) * (n : ℝ) := by
    have : 1000 * b3 ≤ 90 * n := by dsimp only [b3, b2, b1]; omega
    have hcast : ((1000 * b3 : ℕ) : ℝ) ≤ ((90 * n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast; linarith
  have hb4_card : ((Nat.primesLE b4).card : ℝ) ≤ (0.019 : ℝ) * (n : ℝ) := by
    have h1 : (Nat.primesLE b4).card ≤ b4 / 3 + 3 := card_primesLE_le_div_three b4
    have h2 : 1000 * (b4 / 3 + 3) ≤ 19 * n := by dsimp only [b4, b3, b2, b1]; omega
    have h3 : 1000 * (Nat.primesLE b4).card ≤ 19 * n := by omega
    have hcast : ((1000 * (Nat.primesLE b4).card : ℕ) : ℝ) ≤ ((19 * n : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at hcast; linarith
  have hb_ge : 3 ≤ b3 ∧ 3 ≤ b2 ∧ 3 ≤ b1 ∧ 3 ≤ b0 := by
    dsimp only [b3, b2, b1]; omega
  have step_bound : ∀ (b k : ℕ) (cb u_ub : ℝ),
      3 ≤ b → 1 ≤ k → k ≤ 4 → 2 ^ k * ((b + 1) / 2) ≥ S →
      (b : ℝ) ≤ cb * (n : ℝ) → 0 ≤ cb →
      (19 * Real.log 2) / (10 * Real.log 2 - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98) ≤ u_ub →
      (((Nat.primesLE b \ Nat.primesLE ((b + 1) / 2)).card : ℝ)) * Real.log (A : ℝ) ≤
        cb * (n : ℝ) * Real.log 2 * u_ub := by
    intro b k cb u_ub hb3 hk1 hk4 h2k hbub hcb_nn hub
    set h := (b + 1) / 2
    have hh_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
    have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
    have hlogh_lb : Real.log (n : ℝ) - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98 ≤ Real.log (h : ℝ) := by
      have h2kr : (S : ℝ) / (2 : ℝ) ^ k ≤ (h : ℝ) := by
        have hcast : (S : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) * (h : ℝ) := by exact_mod_cast h2k
        rw [Nat.cast_pow, Nat.cast_ofNat] at hcast
        rwa [div_le_iff₀' (by positivity)]
      have hlog := Real.log_le_log (by positivity) h2kr
      rw [Real.log_div hS_pos.ne' (pow_ne_zero k two_ne_zero), Real.log_pow] at hlog
      linarith
    have hk_r1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hk_r4 : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    have hlogh_gt0 : 0 < 10 * Real.log 2 - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98 := by nlinarith
    have hlog_h_pos : 0 < Real.log (h : ℝ) := by linarith
    have hcard_log := card_primes_Ioc_log_le b hb3
    have hcard_le :
        ((Nat.primesLE b \ Nat.primesLE h).card : ℝ) ≤
          (b : ℝ) * Real.log 2 / Real.log (h : ℝ) := by
      rwa [le_div_iff₀ hlog_h_pos]
    have hratio : Real.log (A : ℝ) / Real.log (h : ℝ) ≤ u_ub := by
      have hA_nn : 0 ≤ 2 * Real.log (n : ℝ) - Real.log 2 := by linarith
      have hdiv1 :
          Real.log (A : ℝ) / Real.log (h : ℝ) ≤
            (2 * Real.log (n : ℝ) - Real.log 2) /
              (Real.log (n : ℝ) - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98) :=
        div_le_div₀ hA_nn hlogA_ub (by linarith) hlogh_lb
      have hdiv2 :
          (2 * Real.log (n : ℝ) - Real.log 2) /
              (Real.log (n : ℝ) - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98) ≤
            (19 * Real.log 2) /
              (10 * Real.log 2 - ((k : ℝ) + 0.5) * Real.log 2 - 1 / 98) := by
        rw [div_le_div_iff₀ (by linarith) hlogh_gt0]
        have hdiff : 0 ≤ (2 * (k : ℝ) * Real.log 2 + 1 / 49) * (Real.log (n : ℝ) - 10 * Real.log 2) :=
          mul_nonneg (by positivity) (by linarith)
        linarith only [hdiff]
      exact (hdiv1.trans hdiv2).trans hub
    have hmul1 :
        ((Nat.primesLE b \ Nat.primesLE h).card : ℝ) * Real.log (A : ℝ) ≤
          (b : ℝ) * Real.log 2 * (Real.log (A : ℝ) / Real.log (h : ℝ)) := by
      calc
        ((Nat.primesLE b \ Nat.primesLE h).card : ℝ) * Real.log (A : ℝ)
            ≤ ((b : ℝ) * Real.log 2 / Real.log (h : ℝ)) * Real.log (A : ℝ) :=
              mul_le_mul_of_nonneg_right hcard_le (Real.log_natCast_nonneg A)
        _ = (b : ℝ) * Real.log 2 * (Real.log (A : ℝ) / Real.log (h : ℝ)) := by ring
    calc
      ((Nat.primesLE b \ Nat.primesLE h).card : ℝ) * Real.log (A : ℝ)
          ≤ (b : ℝ) * Real.log 2 * (Real.log (A : ℝ) / Real.log (h : ℝ)) := hmul1
      _ ≤ (cb * (n : ℝ)) * Real.log 2 * u_ub := by
            have h1 : (b : ℝ) * Real.log 2 ≤ cb * (n : ℝ) * Real.log 2 :=
              mul_le_mul_of_nonneg_right hbub (by linarith)
            have h2 : 0 ≤ Real.log (A : ℝ) / Real.log (h : ℝ) :=
              div_nonneg (Real.log_natCast_nonneg A) hlog_h_pos.le
            have h3 : 0 ≤ cb * (n : ℝ) * Real.log 2 := by positivity
            exact (mul_le_mul_of_nonneg_right h1 h2).trans (mul_le_mul_of_nonneg_left hratio h3)
  have hcard_split (x y : ℕ) (hxy : x ≤ y) :
      (Nat.primesLE y).card = (Nat.primesLE x).card + (Nat.primesLE y \ Nat.primesLE x).card := by
    rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right,
        Finset.union_sdiff_of_subset (fun p hp =>
          Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hxy, Nat.prime_of_mem_primesLE hp⟩)]
  have hpiS_eq :
      (Nat.primesLE S).card =
        (Nat.primesLE b4).card +
          (Nat.primesLE b3 \ Nat.primesLE b4).card +
          (Nat.primesLE b2 \ Nat.primesLE b3).card +
          (Nat.primesLE b1 \ Nat.primesLE b2).card +
          (Nat.primesLE b0 \ Nat.primesLE b1).card := by
    rw [show S = b0 from rfl, hcard_split b1 b0 hb1_le, hcard_split b2 b1 hb2_le,
        hcard_split b3 b2 hb3_le, hcard_split b4 b3 hb4_le]
  have hs1 : ((Nat.primesLE b0 \ Nat.primesLE b1).card : ℝ) * Real.log (A : ℝ) ≤
      (0.710 : ℝ) * (n : ℝ) * Real.log 2 * 2.24 := by
    refine step_bound b0 1 0.710 2.24 hb_ge.2.2.2 (by omega) (by omega) (by dsimp only [b1, b0]; omega) hb0_ub (by norm_num) ?_
    rw [div_le_iff₀ (by push_cast; linarith)]; push_cast; linarith
  have hs2 : ((Nat.primesLE b1 \ Nat.primesLE b2).card : ℝ) * Real.log (A : ℝ) ≤
      (0.356 : ℝ) * (n : ℝ) * Real.log 2 * 2.54 := by
    refine step_bound b1 2 0.356 2.54 hb_ge.2.2.1 (by omega) (by omega) (by dsimp only [b2, b1, b0]; omega) hb1_ub (by norm_num) ?_
    rw [div_le_iff₀ (by push_cast; linarith)]; push_cast; linarith
  have hs3 : ((Nat.primesLE b2 \ Nat.primesLE b3).card : ℝ) * Real.log (A : ℝ) ≤
      (0.179 : ℝ) * (n : ℝ) * Real.log 2 * 2.93 := by
    refine step_bound b2 3 0.179 2.93 hb_ge.2.1 (by omega) (by omega) (by dsimp only [b3, b2, b1, b0]; omega) hb2_ub (by norm_num) ?_
    rw [div_le_iff₀ (by push_cast; linarith)]; push_cast; linarith
  have hs4 : ((Nat.primesLE b3 \ Nat.primesLE b4).card : ℝ) * Real.log (A : ℝ) ≤
      (0.090 : ℝ) * (n : ℝ) * Real.log 2 * 3.47 := by
    refine step_bound b3 4 0.090 3.47 hb_ge.1 (by omega) (by omega) (by dsimp only [b4, b3, b2, b1, b0]; omega) hb3_ub (by norm_num) ?_
    rw [div_le_iff₀ (by push_cast; linarith)]; push_cast; linarith
  have hbot : ((Nat.primesLE b4).card : ℝ) * Real.log (A : ℝ) ≤
      (0.019 : ℝ) * (n : ℝ) * (2 * Real.log (n : ℝ) - Real.log 2) := by
    have h1 := mul_le_mul_of_nonneg_right hb4_card (Real.log_natCast_nonneg A)
    have h2 : (0.019 : ℝ) * (n : ℝ) * Real.log (A : ℝ) ≤
        (0.019 : ℝ) * (n : ℝ) * (2 * Real.log (n : ℝ) - Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogA_ub (by positivity)
    exact h1.trans h2
  have hcast_eq : ((Nat.primesLE S).card : ℝ) =
      ((Nat.primesLE b4).card : ℝ) +
        ((Nat.primesLE b3 \ Nat.primesLE b4).card : ℝ) +
        ((Nat.primesLE b2 \ Nat.primesLE b3).card : ℝ) +
        ((Nat.primesLE b1 \ Nat.primesLE b2).card : ℝ) +
        ((Nat.primesLE b0 \ Nat.primesLE b1).card : ℝ) := by exact_mod_cast hpiS_eq
  rw [hcast_eq]
  linarith only [hs1, hs2, hs3, hs4, hbot]

private lemma exists_prime_dvd_choose_large (n : ℕ) (hn : 1024 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (n - 1) / 2 + 1 + n ≤ p ∧
      p ∣ (n * (n - 1) / 2 + 3).choose ((n - 1) / 2 + 1) := by
  by_contra hno
  push Not at hno
  set A := n * (n - 1) / 2 + 3
  set B := (n - 1) / 2 + 1
  set M := B + n - 1
  set S := Nat.sqrt A
  set H := (M + 1) / 2
  have hsub1 : n * (n - 1) + n = n ^ 2 := by zify [show 1 ≤ n by omega]; ring
  have h2A : 2 * A = n * (n - 1) + 6 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    dsimp only [A]; omega
  have hnB : n ≤ 2 * B := by dsimp only [B]; omega
  have hBA : B ≤ A := by
    have h1 : n - 1 ≤ n * (n - 1) := Nat.le_mul_of_pos_left (n - 1) (by omega)
    have h2 : (n - 1) / 2 ≤ n * (n - 1) / 2 := Nat.div_le_div_right h1
    omega
  have hA_pos : 0 < A := by omega
  have hA_le : 2 * A ≤ n ^ 2 := by omega
  have hS_sq_le : S ^ 2 ≤ A := by rw [sq]; exact Nat.sqrt_le A
  have hA_lt_S1 : A < (S + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt A
  have hS_le_n : S ≤ n := by nlinarith only [hS_sq_le, hA_le]
  have hS_lo_sq : 49 * n ^ 2 ≤ 100 * S ^ 2 := by nlinarith only [hn, h2A, hsub1, hA_lt_S1, hS_le_n]
  have hS_lo : 7 * n ≤ 10 * S := by nlinarith only [hS_lo_sq]
  have hS_hi : 100 * S ≤ 71 * n := by nlinarith only [hS_sq_le, hA_le]
  have hM_hi : 1000 * M ≤ 1501 * n := by dsimp only [M, B]; omega
  have hH_hi : 1000 * H ≤ 751 * n := by dsimp only [H, M, B]; omega
  have hSH : S ≤ H := by omega
  have hHM : H ≤ M := by dsimp only [H, M, B]; omega
  have hMA : M ≤ A := by dsimp only [M, B]; omega
  have hH_pos : 0 < H := by omega
  have hS2 : 2 ≤ S := by omega
  have hAB_quad : 392 * n ^ 2 * (B + 1) ^ 2 ≤ 100 * (4 * A * (A - B + 1)) := by
    have h2B' : 2 * B ≤ n + 1 := by dsimp only [B]; omega
    have hAB_sub : A - B + 1 + B = A + 1 := by omega
    have hA_lb : 499 * n ^ 2 ≤ 1000 * A := by nlinarith only [hn, h2A, hsub1]
    have hAB_lb : 498 * n ^ 2 ≤ 1000 * (A - B + 1) := by
      nlinarith only [hn, h2A, hsub1, h2B', hAB_sub]
    have hB1_ub : 1000 * (B + 1) ≤ 502 * n := by omega
    have h_prod1 : 499 * 498 * n ^ 4 ≤ 1000000 * (A * (A - B + 1)) := by
      nlinarith only [hA_lb, hAB_lb]
    have h_prod2 : 1000000 * (B + 1) ^ 2 ≤ 502 ^ 2 * n ^ 2 := by
      nlinarith only [hB1_ub]
    nlinarith only [h_prod1, h_prod2]
  have hchoose_ub :
      A.choose B ≤ A ^ (Nat.primesLE S).card * H ^ ((H - S) / 2 + 1) * 2 ^ M :=
    choose_ub_of_no_large_prime A B M S H hBA hA_pos hH_pos hS2 hSH hHM hMA rfl hA_lt_S1
      (fun p hp hMp => hno p hp (by dsimp only [M, B] at hMp; omega))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hchoose_pos : 0 < A.choose B := Nat.choose_pos hBA
  have hchoose_rpos : (0 : ℝ) < (A.choose B : ℝ) := by exact_mod_cast hchoose_pos
  have hH_rpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hu_ge : 10 * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h1024 : ((2 ^ 10 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ^ 10 ≤ n)
    have := Real.log_le_log (by positivity) h1024
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_ofNat] at this
  have hlog_choose_lb := choose_log_lb n A B hn hBA hnB hAB_quad
  have hpiS_logA := piS_logA_ub n A S hn hA_pos hA_le hS_lo_sq hS_lo hS_hi
  have hlog_choose_ub :
      Real.log (A.choose B : ℝ) ≤
        ((Nat.primesLE S).card : ℝ) * Real.log (A : ℝ) +
          (((H - S) / 2 + 1 : ℕ) : ℝ) * Real.log (H : ℝ) + (M : ℝ) * Real.log 2 := by
    have hreal_ub :
        (A.choose B : ℝ) ≤
          (A : ℝ) ^ (Nat.primesLE S).card * (H : ℝ) ^ ((H - S) / 2 + 1) * (2 : ℝ) ^ M := by
      exact_mod_cast hchoose_ub
    have hlog := Real.log_le_log hchoose_rpos hreal_ub
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    exact hlog
  have hlogH_ub : Real.log (H : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hH_rpos (by exact_mod_cast (by omega : H ≤ n))
  have hmid_term :
      (((H - S) / 2 + 1 : ℕ) : ℝ) * Real.log (H : ℝ) ≤ (n : ℝ) * ((0.027 : ℝ) * Real.log (n : ℝ)) := by
    have h1 : 1000 * ((H - S) / 2 + 1) ≤ 27 * n := by omega
    have h2 : (((H - S) / 2 + 1 : ℕ) : ℝ) ≤ (0.027 : ℝ) * (n : ℝ) := by
      have hcast : ((1000 * ((H - S) / 2 + 1) : ℕ) : ℝ) ≤ ((27 * n : ℕ) : ℝ) := by exact_mod_cast h1
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast
      linarith only [hcast]
    have h3 : (((H - S) / 2 + 1 : ℕ) : ℝ) * Real.log (H : ℝ) ≤
        (0.027 : ℝ) * (n : ℝ) * Real.log (H : ℝ) :=
      mul_le_mul_of_nonneg_right h2 (Real.log_natCast_nonneg H)
    have h4 : (0.027 : ℝ) * (n : ℝ) * Real.log (H : ℝ) ≤ (0.027 : ℝ) * (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogH_ub (by positivity)
    linarith only [h3, h4]
  have hM_term : (M : ℝ) * Real.log 2 ≤ (n : ℝ) * ((1.501 : ℝ) * Real.log 2) := by
    have hM_r : (M : ℝ) ≤ (1.501 : ℝ) * (n : ℝ) := by
      have hcast : ((1000 * M : ℕ) : ℝ) ≤ ((1501 * n : ℕ) : ℝ) := by exact_mod_cast hM_hi
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast
      linarith only [hcast]
    have hmul := mul_le_mul_of_nonneg_right hM_r (by linarith only [hlog2_gt] : (0 : ℝ) ≤ Real.log 2)
    linarith only [hmul]
  have hcomb :
      (n : ℝ) * (0.5 * Real.log (n : ℝ) + 0.5 * Real.log 2 - 1 / 196) ≤
        (n : ℝ) * ((0.065 : ℝ) * Real.log (n : ℝ) +
          (1.482 + (0.710 * 2.24 + 0.356 * 2.54 + 0.179 * 2.93 + 0.090 * 3.47)) * Real.log 2) := by
    linarith only [hlog_choose_lb, hlog_choose_ub, hpiS_logA, hmid_term, hM_term]
  have hfinal :
      0.5 * Real.log (n : ℝ) + 0.5 * Real.log 2 - 1 / 196 ≤
        (0.065 : ℝ) * Real.log (n : ℝ) +
          (1.482 + (0.710 * 2.24 + 0.356 * 2.54 + 0.179 * 2.93 + 0.090 * 3.47)) * Real.log 2 :=
    le_of_mul_le_mul_left hcomb hn_pos
  linarith only [hfinal, hu_ge, hlog2_gt, hlog2_lt]

end OMA.Mo437111Aux

theorem OMA.solution : type_of% @OMA.S_mo_437111.main := by
  intro n hn
  by_cases hn2 : n = 2
  · subst hn2
    decide
  by_cases hn3 : n = 3
  · subst hn3
    decide
  by_cases hn4 : n = 4
  · subst hn4
    decide
  by_cases hn1024 : n < 1024
  · obtain ⟨p, hp, hpM, hmod⟩ := OMA.Mo437111Aux.small_witnesses n (by omega) hn1024
    have hBA : (n - 1) / 2 + 1 ≤ n * (n - 1) / 2 + 3 := by
      have h1 : n - 1 ≤ n * (n - 1) := Nat.le_mul_of_pos_left (n - 1) (by omega)
      have h2 : (n - 1) / 2 ≤ n * (n - 1) / 2 := Nat.div_le_div_right h1
      omega
    exact OMA.Mo437111Aux.gcd_gt_one_of_prime_dvd_choose n p hn hp hpM
      (OMA.Mo437111Aux.dvd_choose_of_mod_lt _ _ p hp hBA (by omega) hmod)
  · obtain ⟨p, hp, hpM, hpdvd⟩ := OMA.Mo437111Aux.exists_prime_dvd_choose_large n (by omega)
    exact OMA.Mo437111Aux.gcd_gt_one_of_prime_dvd_choose n p hn hp hpM hpdvd
