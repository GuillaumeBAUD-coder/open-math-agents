import OMAStatements.S_mo_121944

-- Problem mo-121944: the characteristic polynomial of the given 8 x 8 rational matrix M equals
-- (X^2 - 2 X - 4) (X^6 + 8 X^3 - 64).
-- Upstream: statements/mo-121944.lean (declaration OMA.S_mo_121944.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: both sides are polynomials of degree 8, so it is enough to show that they agree at the nine points
-- t = 8, 9, ..., 16. The value of the characteristic polynomial at t is det (t I - M). For each t the file gives
-- integer matrices Q and U, both upper triangular, with Q^T (t I - M) = U (the result of fraction-free Gaussian
-- elimination). Then det Q * det (t I - M) = det U, and the determinants of Q and U are the products of their
-- diagonal entries. All matrix identities are checked by the kernel.

open Polynomial Matrix

private def cQ8 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 6, 30, 60;
     0, 5, 15, 5, 45, 30, 150, 300;
     0, 0, 40, 0, 120, 80, -26, -52;
     0, 0, 0, 40, 0, 0, 1278, 2556;
     0, 0, 0, 0, 320, -3, -15, -30;
     0, 0, 0, 0, 0, 649, -163, -326;
     0, 0, 0, 0, 0, 0, 3408, 37;
     0, 0, 0, 0, 0, 0, 0, 20337]

private def cU8 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![5, 0, 0, 0, -1, 0, 0, 0;
     0, 40, 0, 0, 4, 0, 0, 0;
     0, 0, 320, 0, 12, -40, 0, 0;
     0, 0, 0, 320, 4, 40, 0, 0;
     0, 0, 0, 0, 2596, -120, -320, 0;
     0, 0, 0, 0, 0, 5112, 652, 0;
     0, 0, 0, 0, 0, 0, 27116, -3408;
     0, 0, 0, 0, 0, 0, 0, 182996]

private lemma ev8 : (Matrix.scalar (Fin 8) (8 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 11711744 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ8 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ8.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU8 p.1 p.2 = 0 := by decide +kernel
  have hU : cU8.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ8ᵀ * (Matrix.scalar (Fin 8) (8 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU8 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ8 i i = 115151907594240000 := by decide +kernel
  have hu : ∏ i : Fin 8, cU8 i i = 1348629662855394754560000 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (115151907594240000 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ9 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 1, 1, 1, 9, 693, 6237;
     0, 6, 6, 6, 6, 54, 4158, 37422;
     0, 0, 18, 0, 18, 162, -621, -5589;
     0, 0, 0, 54, 0, 0, 39285, 353565;
     0, 0, 0, 0, 54, -5, -385, -3465;
     0, 0, 0, 0, 0, 1473, -4434, -39906;
     0, 0, 0, 0, 0, 0, 117855, 4049;
     0, 0, 0, 0, 0, 0, 0, 3169938]

private def cU9 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![6, 0, 0, 0, -1, 0, 0, 0;
     0, 54, 0, 0, 5, 0, 0, 0;
     0, 0, 162, 0, 5, -18, 0, 0;
     0, 0, 0, 486, 5, 54, 0, 0;
     0, 0, 0, 0, 491, -18, -54, 0;
     0, 0, 0, 0, 0, 13095, 1478, 0;
     0, 0, 0, 0, 0, 0, 1056646, -117855;
     0, 0, 0, 0, 0, 0, 0, 31695331]

private lemma ev9 : (Matrix.scalar (Fin 8) (9 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 31695331 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ9 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ9.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU9 p.1 p.2 = 0 := by decide +kernel
  have hU : cU9.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ9ᵀ * (Matrix.scalar (Fin 8) (9 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU9 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ9 i i = 173305682198377702560 := by decide +kernel
  have hu : ∏ i : Fin 8, cU9 i i = 5492980961458388945658747360 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (173305682198377702560 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ10 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 15, 60, 300;
     0, 7, 21, 7, 63, 105, 420, 2100;
     0, 0, 70, 0, 210, 350, -55, -275;
     0, 0, 0, 70, 0, 0, 4365, 21825;
     0, 0, 0, 0, 700, -9, -36, -180;
     0, 0, 0, 0, 0, 3527, -442, -2210;
     0, 0, 0, 0, 0, 0, 14550, 203;
     0, 0, 0, 0, 0, 0, 0, 217641]

private def cU10 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![7, 0, 0, 0, -1, 0, 0, 0;
     0, 70, 0, 0, 6, 0, 0, 0;
     0, 0, 700, 0, 18, -70, 0, 0;
     0, 0, 0, 700, 6, 70, 0, 0;
     0, 0, 0, 0, 7054, -210, -700, 0;
     0, 0, 0, 0, 0, 34920, 3536, 0;
     0, 0, 0, 0, 0, 0, 145094, -14550;
     0, 0, 0, 0, 0, 0, 0, 2393848]

private lemma ev10 : (Matrix.scalar (Fin 8) (10 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 76603136 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ10 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ10.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU10 p.1 p.2 = 0 := by decide +kernel
  have hU : cU10.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ10ᵀ * (Matrix.scalar (Fin 8) (10 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU10 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ10 i i = 268164525286318500000 := by decide +kernel
  have hu : ∏ i : Fin 8, cU10 i i = 20542243600883294994816000000 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (268164525286318500000 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ11 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 33, 1287, 14157;
     0, 8, 24, 8, 72, 264, 10296, 113256;
     0, 0, 88, 0, 264, 968, -1199, -13189;
     0, 0, 0, 88, 0, 0, 116853, 1285383;
     0, 0, 0, 0, 968, -21, -819, -9009;
     0, 0, 0, 0, 0, 10711, -10732, -118052;
     0, 0, 0, 0, 0, 0, 428461, 9913;
     0, 0, 0, 0, 0, 0, 0, 14109474]

private def cU11 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![8, 0, 0, 0, -1, 0, 0, 0;
     0, 88, 0, 0, 7, 0, 0, 0;
     0, 0, 968, 0, 21, -88, 0, 0;
     0, 0, 0, 968, 7, 88, 0, 0;
     0, 0, 0, 0, 10711, -264, -968, 0;
     0, 0, 0, 0, 0, 116853, 10732, 0;
     0, 0, 0, 0, 0, 0, 4703158, -428461;
     0, 0, 0, 0, 0, 0, 0, 169303775]

private lemma ev11 : (Matrix.scalar (Fin 8) (11 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 169303775 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ11 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ11.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU11 p.1 p.2 = 0 := by decide +kernel
  have hU : cU11.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ11ᵀ * (Matrix.scalar (Fin 8) (11 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU11 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ11 i i = 3883138032959938318393344 := by decide +kernel
  have hu : ∏ i : Fin 8, cU11 i i = 657429927826191981071145074073600 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (3883138032959938318393344 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ12 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 1, 1, 1, 3, 105, 315;
     0, 9, 9, 9, 9, 27, 945, 2835;
     0, 0, 36, 0, 36, 108, -99, -297;
     0, 0, 0, 108, 0, 0, 11637, 34911;
     0, 0, 0, 0, 144, -2, -70, -210;
     0, 0, 0, 0, 0, 1302, -978, -2934;
     0, 0, 0, 0, 0, 0, 46548, 227;
     0, 0, 0, 0, 0, 0, 0, 418251]

private def cU12 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![9, 0, 0, 0, -1, 0, 0, 0;
     0, 108, 0, 0, 8, 0, 0, 0;
     0, 0, 432, 0, 8, -36, 0, 0;
     0, 0, 0, 1296, 8, 108, 0, 0;
     0, 0, 0, 0, 1736, -36, -144, 0;
     0, 0, 0, 0, 0, 15516, 1304, 0;
     0, 0, 0, 0, 0, 0, 557668, -46548;
     0, 0, 0, 0, 0, 0, 0, 5437036]

private lemma ev12 : (Matrix.scalar (Fin 8) (12 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 347970304 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ12 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ12.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU12 p.1 p.2 = 0 := by decide +kernel
  have hU : cU12.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ12ᵀ * (Matrix.scalar (Fin 8) (12 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU12 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ12 i i = 127726277657457604608 := by decide +kernel
  have hu : ∏ i : Fin 8, cU12 i i = 44444951665253930542557560832 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (127726277657457604608 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ13 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 39, 2145, 27885;
     0, 10, 30, 10, 90, 390, 21450, 278850;
     0, 0, 130, 0, 390, 1690, -2041, -26533;
     0, 0, 0, 130, 0, 0, 284973, 3704649;
     0, 0, 0, 0, 1690, -27, -1485, -19305;
     0, 0, 0, 0, 0, 22051, -22078, -287014;
     0, 0, 0, 0, 0, 0, 1234883, 20593;
     0, 0, 0, 0, 0, 0, 0, 48098658]

private def cU13 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![10, 0, 0, 0, -1, 0, 0, 0;
     0, 130, 0, 0, 9, 0, 0, 0;
     0, 0, 1690, 0, 27, -130, 0, 0;
     0, 0, 0, 1690, 9, 130, 0, 0;
     0, 0, 0, 0, 22051, -390, -1690, 0;
     0, 0, 0, 0, 0, 284973, 22078, 0;
     0, 0, 0, 0, 0, 0, 16032886, -1234883;
     0, 0, 0, 0, 0, 0, 0, 673360619]

private lemma ev13 : (Matrix.scalar (Fin 8) (13 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 673360619 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ13 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ13.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU13 p.1 p.2 = 0 := by decide +kernel
  have hU : cU13.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ13ᵀ * (Matrix.scalar (Fin 8) (13 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU13 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ13 i i = 374076537604586613375540000 := by decide +kernel
  have hu : ∏ i : Fin 8, cU13 i i = 251888408914801219221667293859260000 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (374076537604586613375540000 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ14 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 21, 168, 1176;
     0, 11, 33, 11, 99, 231, 1848, 12936;
     0, 0, 154, 0, 462, 1078, -161, -1127;
     0, 0, 0, 154, 0, 0, 26355, 184485;
     0, 0, 0, 0, 2156, -15, -120, -840;
     0, 0, 0, 0, 0, 15137, -1894, -13258;
     0, 0, 0, 0, 0, 0, 122990, 887;
     0, 0, 0, 0, 0, 0, 0, 2580129]

private def cU14 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![11, 0, 0, 0, -1, 0, 0, 0;
     0, 154, 0, 0, 10, 0, 0, 0;
     0, 0, 2156, 0, 30, -154, 0, 0;
     0, 0, 0, 2156, 10, 154, 0, 0;
     0, 0, 0, 0, 30274, -462, -2156, 0;
     0, 0, 0, 0, 0, 210840, 15152, 0;
     0, 0, 0, 0, 0, 0, 1720086, -122990;
     0, 0, 0, 0, 0, 0, 0, 38701048]

private lemma ev14 : (Matrix.scalar (Fin 8) (14 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 1238433536 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ14 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ14.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU14 p.1 p.2 = 0 := by decide +kernel
  have hU : cU14.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ14ᵀ * (Matrix.scalar (Fin 8) (14 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU14 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ14 i i = 2701680050553194208849120 := by decide +kernel
  have hu : ∏ i : Fin 8, cU14 i i = 3345851178147251060159738172088320 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (2701680050553194208849120 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ15 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 1, 1, 1, 15, 3315, 49725;
     0, 12, 12, 12, 12, 180, 39780, 596700;
     0, 0, 60, 0, 60, 900, -3195, -47925;
     0, 0, 0, 180, 0, 0, 606285, 9094275;
     0, 0, 0, 0, 300, -11, -2431, -36465;
     0, 0, 0, 0, 0, 13533, -40632, -609480;
     0, 0, 0, 0, 0, 0, 3031425, 38201;
     0, 0, 0, 0, 0, 0, 0, 136299522]

private def cU15 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![12, 0, 0, 0, -1, 0, 0, 0;
     0, 180, 0, 0, 11, 0, 0, 0;
     0, 0, 900, 0, 11, -60, 0, 0;
     0, 0, 0, 2700, 11, 180, 0, 0;
     0, 0, 0, 0, 4511, -60, -300, 0;
     0, 0, 0, 0, 0, 202095, 13544, 0;
     0, 0, 0, 0, 0, 0, 45433174, -3031425;
     0, 0, 0, 0, 0, 0, 0, 2180754151]

private lemma ev15 : (Matrix.scalar (Fin 8) (15 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 2180754151 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ15 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ15.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU15 p.1 p.2 = 0 := by decide +kernel
  have hU : cU15.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ15ᵀ * (Matrix.scalar (Fin 8) (15 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU15 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ15 i i = 217400980637038291704000000 := by decide +kernel
  have hu : ∏ i : Fin 8, cU15 i i = 474098090955691878979446863304000000 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (217400980637038291704000000 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

private def cQ16 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 1, 3, 1, 9, 12, 252, 1008;
     0, 13, 39, 13, 117, 156, 3276, 13104;
     0, 0, 208, 0, 624, 832, -244, -976;
     0, 0, 0, 208, 0, 0, 53148, 212592;
     0, 0, 0, 0, 3328, -9, -189, -756;
     0, 0, 0, 0, 0, 13339, -3337, -13348;
     0, 0, 0, 0, 0, 0, 283456, 787;
     0, 0, 0, 0, 0, 0, 0, 3399111]

private def cU16 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![13, 0, 0, 0, -1, 0, 0, 0;
     0, 208, 0, 0, 12, 0, 0, 0;
     0, 0, 3328, 0, 36, -208, 0, 0;
     0, 0, 0, 3328, 12, 208, 0, 0;
     0, 0, 0, 0, 53356, -624, -3328, 0;
     0, 0, 0, 0, 0, 212592, 13348, 0;
     0, 0, 0, 0, 0, 0, 4532148, -283456;
     0, 0, 0, 0, 0, 0, 0, 57784100]

private lemma ev16 : (Matrix.scalar (Fin 8) (16 : ℚ) - OMA.S_mo_121944.givenMatrix).det = 3698182400 := by
  have hQ0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cQ16 p.1 p.2 = 0 := by decide +kernel
  have hQ : cQ16.IsUpperTriangular := fun i j hij => hQ0 (i, j) hij
  have hU0 : ∀ p : Fin 8 × Fin 8, p.2 < p.1 → cU16 p.1 p.2 = 0 := by decide +kernel
  have hU : cU16.IsUpperTriangular := fun i j hij => hU0 (i, j) hij
  have hmul : cQ16ᵀ * (Matrix.scalar (Fin 8) (16 : ℚ) - OMA.S_mo_121944.givenMatrix) = cU16 := by
    decide +kernel
  have hq : ∏ i : Fin 8, cQ16 i i = 24056232562374774834069504 := by decide +kernel
  have hu : ∏ i : Fin 8, cU16 i i = 88964335872481294495318760069529600 := by decide +kernel
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hQ,
    Matrix.det_of_isUpperTriangular hU, hq, hu] at hdet
  have h0 : (24056232562374774834069504 : ℚ) ≠ 0 := by norm_num
  refine mul_left_cancel₀ h0 (hdet.trans ?_)
  norm_num

theorem OMA.solution : type_of% @OMA.S_mo_121944.main := by
  have hcard : (({8, 9, 10, 11, 12, 13, 14, 15, 16} : Finset ℚ)).card = 9 := by decide +kernel
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq ({8, 9, 10, 11, 12, 13, 14, 15, 16} : Finset ℚ)
  · rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, hcard]
    exact_mod_cast (show (8 : ℕ) < 9 by norm_num)
  · rw [hcard]
    have hd : ((X ^ 2 - 2 * X - 4) * (X ^ 6 + 8 * X ^ 3 - 64) : ℚ[X]).degree ≤ 8 := by
      compute_degree!
    exact lt_of_le_of_lt hd (by exact_mod_cast (show (8 : ℕ) < 9 by norm_num))
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Matrix.eval_charpoly, ev8]
      norm_num
    · rw [Matrix.eval_charpoly, ev9]
      norm_num
    · rw [Matrix.eval_charpoly, ev10]
      norm_num
    · rw [Matrix.eval_charpoly, ev11]
      norm_num
    · rw [Matrix.eval_charpoly, ev12]
      norm_num
    · rw [Matrix.eval_charpoly, ev13]
      norm_num
    · rw [Matrix.eval_charpoly, ev14]
      norm_num
    · rw [Matrix.eval_charpoly, ev15]
      norm_num
    · rw [Matrix.eval_charpoly, ev16]
      norm_num
