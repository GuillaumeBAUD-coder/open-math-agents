import OMAStatements.S_arxiv_2610_39051
import Mathlib

open PowerSeries OMA.S_arxiv_2610_39051

def qcf (j : ℕ) : ℚ :=
  (((Nat.factorial (44 + 7 - j) * Nat.factorial 7 : ℕ) : ℚ) /
    ((Nat.factorial (44 + 7) * Nat.factorial (7 - j) * Nat.factorial j : ℕ) : ℚ)) * (-1 : ℚ) ^ j

lemma Q_eq : qPade 44 7 = ∑ j ∈ Finset.range (7 + 1), PowerSeries.C (qcf j) * PowerSeries.X ^ j := rfl

lemma qcf_0 : qcf 0 = (1 : ℚ) := by norm_num [qcf]

lemma coeff_mul_Q (c : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (qPade 44 7 * c) =
      PowerSeries.coeff n c +
        ∑ i ∈ Finset.range 7, qcf (i + 1) * (if i + 1 ≤ n then PowerSeries.coeff (n - (i + 1)) c else 0) := by
  rw [Q_eq, Finset.sum_mul, map_sum, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', qcf_0]
  ring

lemma bstep (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) {n : ℕ} (hn : 7 ≤ n) :
    PowerSeries.coeff n c = -(∑ i ∈ Finset.range 7, qcf (i + 1) * PowerSeries.coeff (n - (i + 1)) c) := by
  have h := coeff_mul_Q c n
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by omega : ¬ (n = 0))] at h
  have hsum : (∑ i ∈ Finset.range 7, qcf (i + 1) * (if i + 1 ≤ n then PowerSeries.coeff (n - (i + 1)) c else 0))
      = ∑ i ∈ Finset.range 7, qcf (i + 1) * PowerSeries.coeff (n - (i + 1)) c := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (by have := Finset.mem_range.mp hi; omega)]
  rw [hsum] at h
  linarith

lemma b0 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) : PowerSeries.constantCoeff c = 1 := by
  have h := coeff_mul_Q c 0
  rw [hc, PowerSeries.coeff_one, if_pos rfl] at h
  have hz : (∑ i ∈ Finset.range 7, qcf (i + 1) *
      (if i + 1 ≤ 0 then PowerSeries.coeff (0 - (i + 1)) c else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
    simp
  rw [hz, add_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h.symm

lemma b1 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 1 c = ((7 / 51 : ℚ)) := by
  have h := coeff_mul_Q c 1
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (1 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc] at h
  norm_num at h
  linarith

lemma b2 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 2 c = ((1379 / 130050 : ℚ)) := by
  have h := coeff_mul_Q c 2
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (2 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc] at h
  norm_num at h
  linarith

lemma b3 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 3 c = ((28097 / 46427850 : ℚ)) := by
  have h := coeff_mul_Q c 3
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (3 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc, b2 c hc] at h
  norm_num at h
  linarith

lemma b4 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 4 c = ((26851571 / 947128140000 : ℚ)) := by
  have h := coeff_mul_Q c 4
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (4 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc, b2 c hc, b3 c hc] at h
  norm_num at h
  linarith

lemma b5 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 5 c = ((2613467767 / 2270266151580000 : ℚ)) := by
  have h := coeff_mul_Q c 5
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (5 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc, b2 c hc, b3 c hc, b4 c hc] at h
  norm_num at h
  linarith

lemma b6 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 6 c = ((39008835658453 / 932057768531169000000 : ℚ)) := by
  have h := coeff_mul_Q c 6
  rw [hc, PowerSeries.coeff_one] at h
  rw [if_neg (by norm_num : ¬ (6 = 0))] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc, b2 c hc, b3 c hc, b4 c hc, b5 c hc] at h
  norm_num at h
  linarith

lemma b7 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 7 c = ((66144082380949 / 47534946195089619000000 : ℚ)) := by
  have h := bstep c hc (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b0 c hc, b1 c hc, b2 c hc, b3 c hc, b4 c hc, b5 c hc, b6 c hc] at h
  norm_num at h
  linarith

lemma b8 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 8 c = ((41629375548560521 / 969712902379828227600000000 : ℚ)) := by
  have h := bstep c hc (n := 8) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b1 c hc, b2 c hc, b3 c hc, b4 c hc, b5 c hc, b6 c hc, b7 c hc] at h
  norm_num at h
  linarith

lemma b9 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 9 c = ((17199237364503433 / 13847500245983947090128000000 : ℚ)) := by
  have h := bstep c hc (n := 9) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b2 c hc, b3 c hc, b4 c hc, b5 c hc, b6 c hc, b7 c hc, b8 c hc] at h
  norm_num at h
  linarith

lemma b10 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 10 c = ((1409273988552866071711 / 41490572612029401468796020000000000 : ℚ)) := by
  have h := bstep c hc (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b3 c hc, b4 c hc, b5 c hc, b6 c hc, b7 c hc, b8 c hc, b9 c hc] at h
  norm_num at h
  linarith

lemma b11 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 11 c = ((1869106293542219810587 / 2116019203213499474908597020000000000 : ℚ)) := by
  have h := bstep c hc (n := 11) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b4 c hc, b5 c hc, b6 c hc, b7 c hc, b8 c hc, b9 c hc, b10 c hc] at h
  norm_num at h
  linarith

lemma b12 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 12 c = ((152543161228193073393789197 / 6949853471034417675389796052488000000000000 : ℚ)) := by
  have h := bstep c hc (n := 12) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b5 c hc, b6 c hc, b7 c hc, b8 c hc, b9 c hc, b10 c hc, b11 c hc] at h
  norm_num at h
  linarith

lemma b13 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 13 c = ((185425855279505544968627423 / 354442527022755301444879598676888000000000000 : ℚ)) := by
  have h := bstep c hc (n := 13) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b6 c hc, b7 c hc, b8 c hc, b9 c hc, b10 c hc, b11 c hc, b12 c hc] at h
  norm_num at h
  linarith

lemma b14 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 14 c = ((10844173841571612498327189313 / 903828443908026018684442976626064400000000000000 : ℚ)) := by
  have h := bstep c hc (n := 14) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b7 c hc, b8 c hc, b9 c hc, b10 c hc, b11 c hc, b12 c hc, b13 c hc] at h
  norm_num at h
  linarith

lemma b15 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 15 c = ((175046413238894381175580993399 / 659362498275337763804620378469944981200000000000000 : ℚ)) := by
  have h := bstep c hc (n := 15) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b8 c hc, b9 c hc, b10 c hc, b11 c hc, b12 c hc, b13 c hc, b14 c hc] at h
  norm_num at h
  linarith

lemma b16 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 16 c = ((1757321046402420980534021336992289 / 309372884190788478777127881578098185179040000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 16) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b9 c hc, b10 c hc, b11 c hc, b12 c hc, b13 c hc, b14 c hc, b15 c hc] at h
  norm_num at h
  linarith

lemma b17 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 17 c = ((3512288591114485544142946622663 / 29826119269811365628796827902614380801760000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 17) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b10 c hc, b11 c hc, b12 c hc, b13 c hc, b14 c hc, b15 c hc, b16 c hc] at h
  norm_num at h
  linarith

lemma b18 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 18 c = ((15349204675258054800163291371195224891 / 6477664917830938708059442440876298706187998472000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 18) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b11 c hc, b12 c hc, b13 c hc, b14 c hc, b15 c hc, b16 c hc, b17 c hc] at h
  norm_num at h
  linarith

lemma b19 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 19 c = ((3062610100070260788466541260373778067 / 66072182161875574822206312896938246803117584414400000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 19) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b12 c hc, b13 c hc, b14 c hc, b15 c hc, b16 c hc, b17 c hc, b18 c hc] at h
  norm_num at h
  linarith

lemma b20 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 20 c = ((39942562588453934758074148128401592110677 / 45250005897718786528236723432560279310592242811804800000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 20) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b13 c hc, b14 c hc, b15 c hc, b16 c hc, b17 c hc, b18 c hc, b19 c hc] at h
  norm_num at h
  linarith

lemma b21 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 21 c = ((1852745632418990481059230740889009723338271 / 113079764738399247534063571857968137997170014786700195200000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 21) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b14 c hc, b15 c hc, b16 c hc, b17 c hc, b18 c hc, b19 c hc, b20 c hc] at h
  norm_num at h
  linarith

lemma b22 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 22 c = ((85563685578157470535066205117346814403367317 / 288353400082918081211862108237818751892783537706085497760000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 22) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b15 c hc, b16 c hc, b17 c hc, b18 c hc, b19 c hc, b20 c hc, b21 c hc] at h
  norm_num at h
  linarith

lemma b23 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 23 c = ((77175919477967888896329344185805548020425573 / 14706023404228822141804967520128756346531960423010360385760000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 23) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b16 c hc, b17 c hc, b18 c hc, b19 c hc, b20 c hc, b21 c hc, b22 c hc] at h
  norm_num at h
  linarith

lemma b24 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 24 c = ((4380741508339015359301067369695042520035413373009 / 48300463268849143442544235323110887344549570813335227650990144000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 24) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b17 c hc, b18 c hc, b19 c hc, b20 c hc, b21 c hc, b22 c hc, b23 c hc] at h
  norm_num at h
  linarith

lemma b25 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 25 c = ((177452057664700627033257473159471295267653926825553 / 115776210455431396831778532069496796964885321239564540679423375168000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 25) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b18 c hc, b19 c hc, b20 c hc, b21 c hc, b22 c hc, b23 c hc, b24 c hc] at h
  norm_num at h
  linarith

lemma b26 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 26 c = ((7482686997705348639253360616428616013756351811805017 / 295229336661350061921035256777216832260457569160889578732529606678400000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 26) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b19 c hc, b20 c hc, b21 c hc, b22 c hc, b23 c hc, b24 c hc, b25 c hc] at h
  norm_num at h
  linarith

lemma b27 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 27 c = ((43272767764223655541295168374928527020496892359842907 / 105396873188101972105809586669466409116983352190437579607513069584188800000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 27) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b20 c hc, b21 c hc, b22 c hc, b23 c hc, b24 c hc, b25 c hc, b26 c hc] at h
  norm_num at h
  linarith

lemma b28 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 28 c = ((298579250601424837769019635279720531613242813238794939 / 45746727936963409169330118469300313744392774142232481361558864245052160000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 28) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b21 c hc, b22 c hc, b23 c hc, b24 c hc, b25 c hc, b26 c hc, b27 c hc] at h
  norm_num at h
  linarith

lemma b29 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 29 c = ((2238548478570740848877461574079783525021771226056296507 / 21930981372980258355776858794182570409061895923786251564731319519078005504000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 29) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b22 c hc, b23 c hc, b24 c hc, b25 c hc, b26 c hc, b27 c hc, b28 c hc] at h
  norm_num at h
  linarith

lemma b30 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 30 c = ((3330631362098942913514535662716745614179503874097717563902319 / 2115884634629105590971584503818638756138484922304954711276604158711006662521792000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 30) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b23 c hc, b24 c hc, b25 c hc, b26 c hc, b27 c hc, b28 c hc, b29 c hc] at h
  norm_num at h
  linarith

lemma b31 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 31 c = ((2582276942278733926117341207114719771848586419466819168942903 / 107910116366084385139550809694750576563062731037552690275106812094261339788611392000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 31) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b24 c hc, b25 c hc, b26 c hc, b27 c hc, b28 c hc, b29 c hc, b30 c hc] at h
  norm_num at h
  linarith

lemma b32 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 32 c = ((782992996448509743129961510780971686823488656451595848516581583 / 2201366373868121456846836517772911761886479713166074881612178966722931331687672396800000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 32) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b25 c hc, b26 c hc, b27 c hc, b28 c hc, b29 c hc, b30 c hc, b31 c hc] at h
  norm_num at h
  linarith

lemma b33 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 33 c = ((3962556440757900820951537922712067839572754703543153993356415199 / 785887795470919360094320636844929498993473257600288732735547891120086485412499045657600000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 33) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b26 c hc, b27 c hc, b28 c hc, b29 c hc, b30 c hc, b31 c hc, b32 c hc] at h
  norm_num at h
  linarith

lemma b34 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 34 c = ((128958124833127216222850143280821116206775250197139189357388021899 / 2004013878450844368240517623954570222433356806880736268475647122356220537801872566426880000000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 34) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b27 c hc, b28 c hc, b29 c hc, b30 c hc, b31 c hc, b32 c hc, b33 c hc] at h
  norm_num at h
  linarith

lemma b35 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 35 c = ((3093805391494507052282735140455355843663068848817438808609437763313 / 4803621266646673950672520744619104823172756266093124835536126152287860629111088541725231360000000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 35) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b28 c hc, b29 c hc, b30 c hc, b31 c hc, b32 c hc, b33 c hc, b34 c hc] at h
  norm_num at h
  linarith

lemma b36 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 36 c = ((48174326947951440231074127004816243367591296007872688814630378305853931 / 15777013688174335923588827133626987881228600680356259209834852734574249450252459206442349878784000000000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 36) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b29 c hc, b30 c hc, b31 c hc, b32 c hc, b33 c hc, b34 c hc, b35 c hc] at h
  norm_num at h
  linarith

lemma b37 (c : ℚ⟦X⟧) (hc : qPade 44 7 * c = 1) :
    PowerSeries.coeff 37 c = (-(5486375974533816139751576741498130728308587447879576486804229798429247 / 804627698096891132103030183814976381942658634698169219701577489463286721962875419528559843817984000000000000000000000000000000000000 : ℚ)) := by
  have h := bstep c hc (n := 37) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [qcf] at h
  simp only [b30 c hc, b31 c hc, b32 c hc, b33 c hc, b34 c hc, b35 c hc, b36 c hc] at h
  norm_num at h
  linarith

lemma const_Q : PowerSeries.constantCoeff (qPade 44 7) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h := coeff_mul_Q (1 : ℚ⟦X⟧) 0
  rw [mul_one, PowerSeries.coeff_one, if_pos rfl] at h
  have hz : (∑ i ∈ Finset.range 7, qcf (i + 1) *
      (if i + 1 ≤ 0 then PowerSeries.coeff (0 - (i + 1)) (1 : ℚ⟦X⟧) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]
    simp
  rw [hz, add_zero] at h
  exact h

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_39051.main) := by
  intro h
  have hc : qPade 44 7 * (qPade 44 7)⁻¹ = 1 := by
    rw [mul_comm]
    exact PowerSeries.inv_mul_cancel _ (by rw [const_Q]; norm_num)
  have hpos : 0 < PowerSeries.coeff 37 ((qPade 44 7)⁻¹) := h 44 7 (by decide) _ hc 37
  have h37 := b37 (qPade 44 7)⁻¹ hc
  rw [h37] at hpos
  norm_num at hpos

