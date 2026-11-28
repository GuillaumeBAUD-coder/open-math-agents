import OMAStatements.S_arxiv_2610_39051

open PowerSeries

namespace PadeDisproof

open OMA.S_arxiv_2610_39051

lemma qc0 : PowerSeries.coeff 0 (qPade 66 5) = (1 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc1 : PowerSeries.coeff 1 (qPade 66 5) = ((-5 : ℚ) / 71) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc2 : PowerSeries.coeff 2 (qPade 66 5) = ((1 : ℚ) / 497) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc3 : PowerSeries.coeff 3 (qPade 66 5) = ((-1 : ℚ) / 34293) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc4 : PowerSeries.coeff 4 (qPade 66 5) = ((1 : ℚ) / 4663848) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc5 : PowerSeries.coeff 5 (qPade 66 5) = ((-1 : ℚ) / 1562389080) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc6 : PowerSeries.coeff 6 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc7 : PowerSeries.coeff 7 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc8 : PowerSeries.coeff 8 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc9 : PowerSeries.coeff 9 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc10 : PowerSeries.coeff 10 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc11 : PowerSeries.coeff 11 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc12 : PowerSeries.coeff 12 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc13 : PowerSeries.coeff 13 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc14 : PowerSeries.coeff 14 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc15 : PowerSeries.coeff 15 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc16 : PowerSeries.coeff 16 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc17 : PowerSeries.coeff 17 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc18 : PowerSeries.coeff 18 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc19 : PowerSeries.coeff 19 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc20 : PowerSeries.coeff 20 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc21 : PowerSeries.coeff 21 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc22 : PowerSeries.coeff 22 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc23 : PowerSeries.coeff 23 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc24 : PowerSeries.coeff 24 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc25 : PowerSeries.coeff 25 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc26 : PowerSeries.coeff 26 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc27 : PowerSeries.coeff 27 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc28 : PowerSeries.coeff 28 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc29 : PowerSeries.coeff 29 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc30 : PowerSeries.coeff 30 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc31 : PowerSeries.coeff 31 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc32 : PowerSeries.coeff 32 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc33 : PowerSeries.coeff 33 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc34 : PowerSeries.coeff 34 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc35 : PowerSeries.coeff 35 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc36 : PowerSeries.coeff 36 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc37 : PowerSeries.coeff 37 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qc38 : PowerSeries.coeff 38 (qPade 66 5) = (0 : ℚ) := by
  simp only [qPade, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

lemma qconst : constantCoeff (qPade 66 5) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact qc0

lemma e0 : PowerSeries.coeff 0 (qPade 66 5)⁻¹ = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv, qconst]
  norm_num

lemma e1 : PowerSeries.coeff 1 (qPade 66 5)⁻¹ = ((5 : ℚ) / 71) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 1 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, e0]
  norm_num

lemma e2 : PowerSeries.coeff 2 (qPade 66 5)⁻¹ = ((104 : ℚ) / 35287) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 2 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, e0, e1]
  norm_num

lemma e3 : PowerSeries.coeff 3 (qPade 66 5)⁻¹ = ((16426 : ℚ) / 172871013) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (3 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 3 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, e0, e1, e2]
  norm_num

lemma e4 : PowerSeries.coeff 4 (qPade 66 5)⁻¹ = ((30386087 : ℚ) / 11684697510696) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (4 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 4 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, e0, e1, e2, e3]
  norm_num

lemma e5 : PowerSeries.coeff 5 (qPade 66 5)⁻¹ = ((17629371097 : ℚ) / 277920530291904360) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (5 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 5 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, e0, e1, e2, e3, e4]
  norm_num

lemma e6 : PowerSeries.coeff 6 (qPade 66 5)⁻¹ = ((159068099753 : ℚ) / 112126220532944426088) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (6 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 6 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, e0, e1, e2, e3, e4, e5]
  norm_num

lemma e7 : PowerSeries.coeff 7 (qPade 66 5)⁻¹ = ((20041818509089 : ℚ) / 676681740916319611441080) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (7 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 7 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, e0, e1, e2, e3, e4, e5, e6]
  norm_num

lemma e8 : PowerSeries.coeff 8 (qPade 66 5)⁻¹ = ((26724791796601183 : ℚ) / 45738272232015875176525479360) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (8 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 8 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, e0, e1, e2, e3, e4, e5, e6, e7]
  norm_num

lemma e9 : PowerSeries.coeff 9 (qPade 66 5)⁻¹ = ((2461785873375280559 : ℚ) / 224071795664645772489798323384640) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (9 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 9 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, e0, e1, e2, e3, e4, e5, e6, e7, e8]
  norm_num

lemma e10 : PowerSeries.coeff 10 (qPade 66 5)⁻¹ = ((160696455579142903487 : ℚ) / 811018122156199954145412431563600800) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (10 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 10 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  norm_num

lemma e11 : PowerSeries.coeff 11 (qPade 66 5)⁻¹ = ((16288708172590005913 : ℚ) / 4729973548146694732569494645512000380) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (11 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 11 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  norm_num

lemma e12 : PowerSeries.coeff 12 (qPade 66 5)⁻¹ = ((715130794182289905312361531 : ℚ) / 12353531496643044923658672579549837091026854400) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (12 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 12 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  norm_num

lemma e13 : PowerSeries.coeff 13 (qPade 66 5)⁻¹ = ((827848175231854168681082291 : ℚ) / 877100736261656189579765753148038433462906662400) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (13 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 13 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]
  norm_num

lemma e14 : PowerSeries.coeff 14 (qPade 66 5)⁻¹ = ((283527213250964903697795007 : ℚ) / 18953002866175788096571459970198917453524548313600) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (14 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 14 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  norm_num

lemma e15 : PowerSeries.coeff 15 (qPade 66 5)⁻¹ = ((165186158276454314606039149335491 : ℚ) / 715415113823949907244723102345804646340113152661054912000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (15 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 15 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  norm_num

lemma e16 : PowerSeries.coeff 16 (qPade 66 5)⁻¹ = ((6722649020428978604276657659609243 : ℚ) / 1934253534943536885219412957350305106216837128586640944476160) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (16 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 16 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  norm_num

lemma e17 : PowerSeries.coeff 17 (qPade 66 5)⁻¹ = ((175381950458140164805700751092034271 : ℚ) / 3433300024524777971264457999296791563534885903241287676445184000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (17 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 17 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16]
  norm_num

lemma e18 : PowerSeries.coeff 18 (qPade 66 5)⁻¹ = ((21600176205953975383567303121320577687 : ℚ) / 29434539435257052742143014542471218272075460569963369572083673728000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (18 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 18 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
  norm_num

lemma e19 : PowerSeries.coeff 19 (qPade 66 5)⁻¹ = ((43107429237589416548612681182174839341 : ℚ) / 4179704599806501489384308065030912994634715400934798479235881669376000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (19 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 19 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  norm_num

lemma e20 : PowerSeries.coeff 20 (qPade 66 5)⁻¹ = ((26864964793200995286354354786919764086727059 : ℚ) / 189284777517781102609210980990151545659344287864589882201702848243629936640000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (20 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 20 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19]
  norm_num

lemma e21 : PowerSeries.coeff 21 (qPade 66 5)⁻¹ = ((14200002156277197464367668896357415119006283 : ℚ) / 7418449000476876973460196766966019377481021329989006663249138028364344476794880) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (21 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 21 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20]
  norm_num

lemma e22 : PowerSeries.coeff 22 (qPade 66 5)⁻¹ = ((2334226098111054261522383608260982981501722079 : ℚ) / 92174228830925196395242944829552790765201690025113407790870540002426980124176384000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (22 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 22 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21]
  norm_num

lemma e23 : PowerSeries.coeff 23 (qPade 66 5)⁻¹ = ((2153157703197784510566508452710515579322846659 : ℚ) / 6544370246995688944062249082898248144329319991783051953151808340172315588816523264000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (23 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 23 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22]
  norm_num

lemma e24 : PowerSeries.coeff 24 (qPade 66 5)⁻¹ = ((25654618109497274404770517097369406827158333651777 : ℚ) / 6104389617542069978077366452155365762286802077007480657120631004739194742854152878351974400) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (24 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 24 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23]
  norm_num

lemma e25 : PowerSeries.coeff 25 (qPade 66 5)⁻¹ = ((27405852592730442578807848462692404588741375787954301 : ℚ) / 518546096618707622959179146658983480914255669291510455105765030170434810567092950755720396800000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (25 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 25 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24]
  norm_num

lemma e26 : PowerSeries.coeff 26 (qPade 66 5)⁻¹ = ((118203975142443801188895881865821970250738785809834437 : ℚ) / 180402187013648382027498425122660353010069547346516487331295653996294270596291637567915126046720000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (26 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 26 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25]
  norm_num

lemma e27 : PowerSeries.coeff 27 (qPade 66 5)⁻¹ = ((17713658258206337794023966845111205715411482277052445173 : ℚ) / 2209475785449658558881786961689782673490826781126460678590043522319614079128081831113040506257203200000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (27 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 27 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26]
  norm_num

lemma e28 : PowerSeries.coeff 28 (qPade 66 5)⁻¹ = ((57864592574438925389498087431328269430955471909194801059609 : ℚ) / 597371549160453285247750977258143161866367855159598920749032887042509419345701228514370535595747514777600000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (28 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 28 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27]
  norm_num

lemma e29 : PowerSeries.coeff 29 (qPade 66 5)⁻¹ = ((2881293040997787676037870373863761006091717224534659385697 : ℚ) / 2494904705317187250152371728548715558383065748019501374893019704706951104326163954383547531017533738188800000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (29 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 29 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28]
  norm_num

lemma e30 : PowerSeries.coeff 30 (qPade 66 5)⁻¹ = ((6601919774533048130913604400216450985857009533219721379175654957 : ℚ) / 487251483403523911994161740598154679555475547703462571897230019357370625686642415077309099265344500134720012288000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (30 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 30 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29]
  norm_num

lemma e31 : PowerSeries.coeff 31 (qPade 66 5)⁻¹ = ((1075966283330149843090551853212517091912329003792889355969283537 : ℚ) / 6918971064330039550317096716493796449687752777389168520940666274874662884750322294097789209567891901913024174489600000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (31 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 31 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30]
  norm_num

lemma e32 : PowerSeries.coeff 32 (qPade 66 5)⁻¹ = ((4039942862146108914880202767070055032440804278625627053048736539761 : ℚ) / 2338335460900980166425166006306243448136472928646443393337107574256641068530218922513288841265564747170525650010505216000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (32 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 32 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31]
  norm_num

lemma e33 : PowerSeries.coeff 33 (qPade 66 5)⁻¹ = ((209096695774793384829926523123111623060914616825381518543330877184649 : ℚ) / 11455505422953901835316888264894286652420580877438926183958490006283284594729542501392602033360001696388405159401465053184000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (33 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 33 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32]
  norm_num

lemma e34 : PowerSeries.coeff 34 (qPade 66 5)⁻¹ = ((126596142197818046022303007984544298837199370801997170343033451939387 : ℚ) / 711673274401011151519061683456557558281628587010893289178421191640349055447572827899015401322490105388129670527816016429056000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (34 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 34 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, qc34, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33]
  norm_num

lemma e35 : PowerSeries.coeff 35 (qPade 66 5)⁻¹ = ((102238992981566109531250793038816495849208544688860231182772842813134307 : ℚ) / 67708595326512200955523528564056886094914143768216387532434992172662809135282078846312325281821708626626656854016415803060387840000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (35 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 35 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, qc34, qc35, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34]
  norm_num

lemma e36 : PowerSeries.coeff 36 (qPade 66 5)⁻¹ = ((1234264354757133296072326458243427370622216175298390703519672452649310193761 : ℚ) / 126313038758545310160806599058567832039997255834043385024148749349795638823986821145286418256389444853950192126116301124108633482723328000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (36 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 36 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, qc34, qc35, qc36, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35]
  norm_num

lemma e37 : PowerSeries.coeff 37 (qPade 66 5)⁻¹ = ((1311402332658709354967161108179637503672420373189750521518234246887628910037 : ℚ) / 44841128759283585107086342665791580374199025821085401683572806019177451782515321506576678481018252923152318204771286899058564886366781440000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (37 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 37 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, qc34, qc35, qc36, qc37, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36]
  norm_num

lemma e38 : PowerSeries.coeff 38 (qPade 66 5)⁻¹ = ((-625387044196041302769979230262974179147391857970590017827905300559706838051 : ℚ) / 22286040993363941798221912304898415445976915833079444636735684591531193535910114788768609205066071702806702147771329588832106748524290375680000000) := by
  rw [PowerSeries.coeff_inv, if_neg (by norm_num : (38 : ℕ) ≠ 0)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if j < 38 then PowerSeries.coeff i (qPade 66 5) * PowerSeries.coeff j (qPade 66 5)⁻¹ else 0)]
  simp [Nat.succ_eq_add_one, qconst, Finset.sum_range_succ, qc0, qc1, qc2, qc3, qc4, qc5, qc6, qc7, qc8, qc9, qc10, qc11, qc12, qc13, qc14, qc15, qc16, qc17, qc18, qc19, qc20, qc21, qc22, qc23, qc24, qc25, qc26, qc27, qc28, qc29, qc30, qc31, qc32, qc33, qc34, qc35, qc36, qc37, qc38, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37]
  norm_num

end PadeDisproof

open PadeDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_39051.main) := by
  intro h
  have hq : OMA.S_arxiv_2610_39051.qPade 66 5 * (OMA.S_arxiv_2610_39051.qPade 66 5)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [PadeDisproof.qconst]; norm_num)
  have hpos := h 66 5 (by decide) (OMA.S_arxiv_2610_39051.qPade 66 5)⁻¹ hq 38
  rw [PadeDisproof.e38] at hpos
  norm_num at hpos
