import OMAStatements.S_arxiv_2610_39051
import Mathlib

/-!
Disproof of the positivity statement for the reciprocal of the Pade denominator.

Counterexample: k = 66, m = 5 (odd). The reciprocal c of q_{66,5} satisfies the linear
recurrence obtained from comparing coefficients in q * c = 1; solving it exactly for the first
39 coefficients gives a negative coefficient of z^38 (about -2.806e-71).
-/

namespace OMA.Helpers

open PowerSeries OMA.S_arxiv_2610_39051

/-- The coefficient of `z ^ j` in `q_{66,5}`. -/
noncomputable def padeCoef6605 (j : ℕ) : ℚ :=
  (((Nat.factorial (66 + 5 - j) * Nat.factorial 5 : ℕ) : ℚ) /
      ((Nat.factorial (66 + 5) * Nat.factorial (5 - j) * Nat.factorial j : ℕ) : ℚ)) * (-1 : ℚ) ^ j

theorem pade6605_eq : qPade 66 5 = ∑ j ∈ Finset.range 6, C (padeCoef6605 j) * X ^ j := rfl

theorem pade6605_coeff_mul (c : ℚ⟦X⟧) (i : ℕ) :
    coeff i (qPade 66 5 * c) =
      ∑ j ∈ Finset.range 6, padeCoef6605 j * (if j ≤ i then coeff (i - j) c else 0) := by
  rw [pade6605_eq, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']

theorem pade6605_vals : padeCoef6605 0 = (1 : ℚ) ∧ padeCoef6605 1 = (-5 / 71 : ℚ) ∧ padeCoef6605 2 = (1 / 497 : ℚ) ∧
    padeCoef6605 3 = (-1 / 34293 : ℚ) ∧ padeCoef6605 4 = (1 / 4663848 : ℚ) ∧ padeCoef6605 5 = (-1 / 1562389080 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [padeCoef6605, Nat.factorial]

theorem pade6605_const : constantCoeff (qPade 66 5) ≠ 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, pade6605_eq, map_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_C_mul_X_pow]
  obtain ⟨a0, -, -, -, -, -⟩ := pade6605_vals
  norm_num [a0]

theorem pade6605_rec (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) (i : ℕ) :
    coeff (i + 5) c + (-5 / 71 : ℚ) * coeff (i + 4) c + (1 / 497 : ℚ) * coeff (i + 3) c + (-1 / 34293 : ℚ) * coeff (i + 2) c + (1 / 4663848 : ℚ) * coeff (i + 1) c + (-1 / 1562389080 : ℚ) * coeff i c = 0 := by
  have h := pade6605_coeff_mul c (i + 5)
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ i + 5 by omega, show 1 ≤ i + 5 by omega, show 2 ≤ i + 5 by omega,
    show 3 ≤ i + 5 by omega, show 4 ≤ i + 5 by omega, show 5 ≤ i + 5 by omega,
    show ¬ (i + 5 = 0) by omega, if_true, if_false,
    show i + 5 - 0 = i + 5 by omega, show i + 5 - 1 = i + 4 by omega, show i + 5 - 2 = i + 3 by omega,
    show i + 5 - 3 = i + 2 by omega, show i + 5 - 4 = i + 1 by omega, show i + 5 - 5 = i by omega] at h
  linear_combination -h

theorem pade6605_small0 (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) :
    coeff 0 c = 1 := by
  have h := pade6605_coeff_mul c 0
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ 0 by norm_num, show ¬ (1 : ℕ) ≤ 0 by norm_num, show ¬ (2 : ℕ) ≤ 0 by norm_num, show ¬ (3 : ℕ) ≤ 0 by norm_num, show ¬ (4 : ℕ) ≤ 0 by norm_num, show ¬ (5 : ℕ) ≤ 0 by norm_num, show (0 : ℕ) - 0 = 0 by norm_num, eq_self_iff_true, if_true, if_false] at h
  linear_combination -h

theorem pade6605_small1 (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) :
    coeff 1 c + (-5 / 71 : ℚ) * coeff 0 c = 0 := by
  have h := pade6605_coeff_mul c 1
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ 1 by norm_num, show (1 : ℕ) ≤ 1 by norm_num, show ¬ (2 : ℕ) ≤ 1 by norm_num, show ¬ (3 : ℕ) ≤ 1 by norm_num, show ¬ (4 : ℕ) ≤ 1 by norm_num, show ¬ (5 : ℕ) ≤ 1 by norm_num, show (1 : ℕ) - 0 = 1 by norm_num, show (1 : ℕ) - 1 = 0 by norm_num, show ¬ (1 : ℕ) = 0 by norm_num, if_true, if_false] at h
  linear_combination -h

theorem pade6605_small2 (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) :
    coeff 2 c + (-5 / 71 : ℚ) * coeff 1 c + (1 / 497 : ℚ) * coeff 0 c = 0 := by
  have h := pade6605_coeff_mul c 2
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ 2 by norm_num, show (1 : ℕ) ≤ 2 by norm_num, show (2 : ℕ) ≤ 2 by norm_num, show ¬ (3 : ℕ) ≤ 2 by norm_num, show ¬ (4 : ℕ) ≤ 2 by norm_num, show ¬ (5 : ℕ) ≤ 2 by norm_num, show (2 : ℕ) - 0 = 2 by norm_num, show (2 : ℕ) - 1 = 1 by norm_num, show (2 : ℕ) - 2 = 0 by norm_num, show ¬ (2 : ℕ) = 0 by norm_num, if_true, if_false] at h
  linear_combination -h

theorem pade6605_small3 (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) :
    coeff 3 c + (-5 / 71 : ℚ) * coeff 2 c + (1 / 497 : ℚ) * coeff 1 c + (-1 / 34293 : ℚ) * coeff 0 c = 0 := by
  have h := pade6605_coeff_mul c 3
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ 3 by norm_num, show (1 : ℕ) ≤ 3 by norm_num, show (2 : ℕ) ≤ 3 by norm_num, show (3 : ℕ) ≤ 3 by norm_num, show ¬ (4 : ℕ) ≤ 3 by norm_num, show ¬ (5 : ℕ) ≤ 3 by norm_num, show (3 : ℕ) - 0 = 3 by norm_num, show (3 : ℕ) - 1 = 2 by norm_num, show (3 : ℕ) - 2 = 1 by norm_num, show (3 : ℕ) - 3 = 0 by norm_num, show ¬ (3 : ℕ) = 0 by norm_num, if_true, if_false] at h
  linear_combination -h

theorem pade6605_small4 (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) :
    coeff 4 c + (-5 / 71 : ℚ) * coeff 3 c + (1 / 497 : ℚ) * coeff 2 c + (-1 / 34293 : ℚ) * coeff 1 c + (1 / 4663848 : ℚ) * coeff 0 c = 0 := by
  have h := pade6605_coeff_mul c 4
  rw [hc, coeff_one] at h
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := pade6605_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a0, a1, a2, a3, a4, a5] at h
  simp only [show (0 : ℕ) ≤ 4 by norm_num, show (1 : ℕ) ≤ 4 by norm_num, show (2 : ℕ) ≤ 4 by norm_num, show (3 : ℕ) ≤ 4 by norm_num, show (4 : ℕ) ≤ 4 by norm_num, show ¬ (5 : ℕ) ≤ 4 by norm_num, show (4 : ℕ) - 0 = 4 by norm_num, show (4 : ℕ) - 1 = 3 by norm_num, show (4 : ℕ) - 2 = 2 by norm_num, show (4 : ℕ) - 3 = 1 by norm_num, show (4 : ℕ) - 4 = 0 by norm_num, show ¬ (4 : ℕ) = 0 by norm_num, if_true, if_false] at h
  linear_combination -h

theorem pade6605_neg (c : ℚ⟦X⟧) (hc : qPade 66 5 * c = 1) : coeff 38 c < 0 := by
  have h0 : coeff 0 c = (1 : ℚ) := by
    have e := pade6605_small0 c hc
    linear_combination e
  have h1 : coeff 1 c = (5 / 71 : ℚ) := by
    have e := pade6605_small1 c hc
    linear_combination e - (-5 / 71 : ℚ) * h0
  have h2 : coeff 2 c = (104 / 35287 : ℚ) := by
    have e := pade6605_small2 c hc
    linear_combination e - (-5 / 71 : ℚ) * h1 - (1 / 497 : ℚ) * h0
  have h3 : coeff 3 c = (16426 / 172871013 : ℚ) := by
    have e := pade6605_small3 c hc
    linear_combination e - (-5 / 71 : ℚ) * h2 - (1 / 497 : ℚ) * h1 - (-1 / 34293 : ℚ) * h0
  have h4 : coeff 4 c = (30386087 / 11684697510696 : ℚ) := by
    have e := pade6605_small4 c hc
    linear_combination e - (-5 / 71 : ℚ) * h3 - (1 / 497 : ℚ) * h2 - (-1 / 34293 : ℚ) * h1 - (1 / 4663848 : ℚ) * h0
  have h5 : coeff 5 c = (17629371097 / 277920530291904360 : ℚ) := by
    have e := pade6605_rec c hc 0
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h4 - (1 / 497 : ℚ) * h3 - (-1 / 34293 : ℚ) * h2 - (1 / 4663848 : ℚ) * h1 - (-1 / 1562389080 : ℚ) * h0
  have h6 : coeff 6 c = (159068099753 / 112126220532944426088 : ℚ) := by
    have e := pade6605_rec c hc 1
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h5 - (1 / 497 : ℚ) * h4 - (-1 / 34293 : ℚ) * h3 - (1 / 4663848 : ℚ) * h2 - (-1 / 1562389080 : ℚ) * h1
  have h7 : coeff 7 c = (20041818509089 / 676681740916319611441080 : ℚ) := by
    have e := pade6605_rec c hc 2
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h6 - (1 / 497 : ℚ) * h5 - (-1 / 34293 : ℚ) * h4 - (1 / 4663848 : ℚ) * h3 - (-1 / 1562389080 : ℚ) * h2
  have h8 : coeff 8 c = (26724791796601183 / 45738272232015875176525479360 : ℚ) := by
    have e := pade6605_rec c hc 3
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h7 - (1 / 497 : ℚ) * h6 - (-1 / 34293 : ℚ) * h5 - (1 / 4663848 : ℚ) * h4 - (-1 / 1562389080 : ℚ) * h3
  have h9 : coeff 9 c = (2461785873375280559 / 224071795664645772489798323384640 : ℚ) := by
    have e := pade6605_rec c hc 4
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h8 - (1 / 497 : ℚ) * h7 - (-1 / 34293 : ℚ) * h6 - (1 / 4663848 : ℚ) * h5 - (-1 / 1562389080 : ℚ) * h4
  have h10 : coeff 10 c = (160696455579142903487 / 811018122156199954145412431563600800 : ℚ) := by
    have e := pade6605_rec c hc 5
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h9 - (1 / 497 : ℚ) * h8 - (-1 / 34293 : ℚ) * h7 - (1 / 4663848 : ℚ) * h6 - (-1 / 1562389080 : ℚ) * h5
  have h11 : coeff 11 c = (16288708172590005913 / 4729973548146694732569494645512000380 : ℚ) := by
    have e := pade6605_rec c hc 6
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h10 - (1 / 497 : ℚ) * h9 - (-1 / 34293 : ℚ) * h8 - (1 / 4663848 : ℚ) * h7 - (-1 / 1562389080 : ℚ) * h6
  have h12 : coeff 12 c = (715130794182289905312361531 / 12353531496643044923658672579549837091026854400 : ℚ) := by
    have e := pade6605_rec c hc 7
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h11 - (1 / 497 : ℚ) * h10 - (-1 / 34293 : ℚ) * h9 - (1 / 4663848 : ℚ) * h8 - (-1 / 1562389080 : ℚ) * h7
  have h13 : coeff 13 c = (827848175231854168681082291 / 877100736261656189579765753148038433462906662400 : ℚ) := by
    have e := pade6605_rec c hc 8
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h12 - (1 / 497 : ℚ) * h11 - (-1 / 34293 : ℚ) * h10 - (1 / 4663848 : ℚ) * h9 - (-1 / 1562389080 : ℚ) * h8
  have h14 : coeff 14 c = (283527213250964903697795007 / 18953002866175788096571459970198917453524548313600 : ℚ) := by
    have e := pade6605_rec c hc 9
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h13 - (1 / 497 : ℚ) * h12 - (-1 / 34293 : ℚ) * h11 - (1 / 4663848 : ℚ) * h10 - (-1 / 1562389080 : ℚ) * h9
  have h15 : coeff 15 c = (165186158276454314606039149335491 / 715415113823949907244723102345804646340113152661054912000 : ℚ) := by
    have e := pade6605_rec c hc 10
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h14 - (1 / 497 : ℚ) * h13 - (-1 / 34293 : ℚ) * h12 - (1 / 4663848 : ℚ) * h11 - (-1 / 1562389080 : ℚ) * h10
  have h16 : coeff 16 c = (6722649020428978604276657659609243 / 1934253534943536885219412957350305106216837128586640944476160 : ℚ) := by
    have e := pade6605_rec c hc 11
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h15 - (1 / 497 : ℚ) * h14 - (-1 / 34293 : ℚ) * h13 - (1 / 4663848 : ℚ) * h12 - (-1 / 1562389080 : ℚ) * h11
  have h17 : coeff 17 c = (175381950458140164805700751092034271 / 3433300024524777971264457999296791563534885903241287676445184000 : ℚ) := by
    have e := pade6605_rec c hc 12
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h16 - (1 / 497 : ℚ) * h15 - (-1 / 34293 : ℚ) * h14 - (1 / 4663848 : ℚ) * h13 - (-1 / 1562389080 : ℚ) * h12
  have h18 : coeff 18 c = (21600176205953975383567303121320577687 / 29434539435257052742143014542471218272075460569963369572083673728000 : ℚ) := by
    have e := pade6605_rec c hc 13
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h17 - (1 / 497 : ℚ) * h16 - (-1 / 34293 : ℚ) * h15 - (1 / 4663848 : ℚ) * h14 - (-1 / 1562389080 : ℚ) * h13
  have h19 : coeff 19 c = (43107429237589416548612681182174839341 / 4179704599806501489384308065030912994634715400934798479235881669376000 : ℚ) := by
    have e := pade6605_rec c hc 14
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h18 - (1 / 497 : ℚ) * h17 - (-1 / 34293 : ℚ) * h16 - (1 / 4663848 : ℚ) * h15 - (-1 / 1562389080 : ℚ) * h14
  have h20 : coeff 20 c = (26864964793200995286354354786919764086727059 / 189284777517781102609210980990151545659344287864589882201702848243629936640000 : ℚ) := by
    have e := pade6605_rec c hc 15
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h19 - (1 / 497 : ℚ) * h18 - (-1 / 34293 : ℚ) * h17 - (1 / 4663848 : ℚ) * h16 - (-1 / 1562389080 : ℚ) * h15
  have h21 : coeff 21 c = (14200002156277197464367668896357415119006283 / 7418449000476876973460196766966019377481021329989006663249138028364344476794880 : ℚ) := by
    have e := pade6605_rec c hc 16
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h20 - (1 / 497 : ℚ) * h19 - (-1 / 34293 : ℚ) * h18 - (1 / 4663848 : ℚ) * h17 - (-1 / 1562389080 : ℚ) * h16
  have h22 : coeff 22 c = (2334226098111054261522383608260982981501722079 / 92174228830925196395242944829552790765201690025113407790870540002426980124176384000 : ℚ) := by
    have e := pade6605_rec c hc 17
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h21 - (1 / 497 : ℚ) * h20 - (-1 / 34293 : ℚ) * h19 - (1 / 4663848 : ℚ) * h18 - (-1 / 1562389080 : ℚ) * h17
  have h23 : coeff 23 c = (2153157703197784510566508452710515579322846659 / 6544370246995688944062249082898248144329319991783051953151808340172315588816523264000 : ℚ) := by
    have e := pade6605_rec c hc 18
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h22 - (1 / 497 : ℚ) * h21 - (-1 / 34293 : ℚ) * h20 - (1 / 4663848 : ℚ) * h19 - (-1 / 1562389080 : ℚ) * h18
  have h24 : coeff 24 c = (25654618109497274404770517097369406827158333651777 / 6104389617542069978077366452155365762286802077007480657120631004739194742854152878351974400 : ℚ) := by
    have e := pade6605_rec c hc 19
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h23 - (1 / 497 : ℚ) * h22 - (-1 / 34293 : ℚ) * h21 - (1 / 4663848 : ℚ) * h20 - (-1 / 1562389080 : ℚ) * h19
  have h25 : coeff 25 c = (27405852592730442578807848462692404588741375787954301 / 518546096618707622959179146658983480914255669291510455105765030170434810567092950755720396800000 : ℚ) := by
    have e := pade6605_rec c hc 20
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h24 - (1 / 497 : ℚ) * h23 - (-1 / 34293 : ℚ) * h22 - (1 / 4663848 : ℚ) * h21 - (-1 / 1562389080 : ℚ) * h20
  have h26 : coeff 26 c = (118203975142443801188895881865821970250738785809834437 / 180402187013648382027498425122660353010069547346516487331295653996294270596291637567915126046720000 : ℚ) := by
    have e := pade6605_rec c hc 21
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h25 - (1 / 497 : ℚ) * h24 - (-1 / 34293 : ℚ) * h23 - (1 / 4663848 : ℚ) * h22 - (-1 / 1562389080 : ℚ) * h21
  have h27 : coeff 27 c = (17713658258206337794023966845111205715411482277052445173 / 2209475785449658558881786961689782673490826781126460678590043522319614079128081831113040506257203200000 : ℚ) := by
    have e := pade6605_rec c hc 22
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h26 - (1 / 497 : ℚ) * h25 - (-1 / 34293 : ℚ) * h24 - (1 / 4663848 : ℚ) * h23 - (-1 / 1562389080 : ℚ) * h22
  have h28 : coeff 28 c = (57864592574438925389498087431328269430955471909194801059609 / 597371549160453285247750977258143161866367855159598920749032887042509419345701228514370535595747514777600000 : ℚ) := by
    have e := pade6605_rec c hc 23
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h27 - (1 / 497 : ℚ) * h26 - (-1 / 34293 : ℚ) * h25 - (1 / 4663848 : ℚ) * h24 - (-1 / 1562389080 : ℚ) * h23
  have h29 : coeff 29 c = (2881293040997787676037870373863761006091717224534659385697 / 2494904705317187250152371728548715558383065748019501374893019704706951104326163954383547531017533738188800000 : ℚ) := by
    have e := pade6605_rec c hc 24
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h28 - (1 / 497 : ℚ) * h27 - (-1 / 34293 : ℚ) * h26 - (1 / 4663848 : ℚ) * h25 - (-1 / 1562389080 : ℚ) * h24
  have h30 : coeff 30 c = (6601919774533048130913604400216450985857009533219721379175654957 / 487251483403523911994161740598154679555475547703462571897230019357370625686642415077309099265344500134720012288000000 : ℚ) := by
    have e := pade6605_rec c hc 25
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h29 - (1 / 497 : ℚ) * h28 - (-1 / 34293 : ℚ) * h27 - (1 / 4663848 : ℚ) * h26 - (-1 / 1562389080 : ℚ) * h25
  have h31 : coeff 31 c = (1075966283330149843090551853212517091912329003792889355969283537 / 6918971064330039550317096716493796449687752777389168520940666274874662884750322294097789209567891901913024174489600000 : ℚ) := by
    have e := pade6605_rec c hc 26
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h30 - (1 / 497 : ℚ) * h29 - (-1 / 34293 : ℚ) * h28 - (1 / 4663848 : ℚ) * h27 - (-1 / 1562389080 : ℚ) * h26
  have h32 : coeff 32 c = (4039942862146108914880202767070055032440804278625627053048736539761 / 2338335460900980166425166006306243448136472928646443393337107574256641068530218922513288841265564747170525650010505216000000 : ℚ) := by
    have e := pade6605_rec c hc 27
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h31 - (1 / 497 : ℚ) * h30 - (-1 / 34293 : ℚ) * h29 - (1 / 4663848 : ℚ) * h28 - (-1 / 1562389080 : ℚ) * h27
  have h33 : coeff 33 c = (209096695774793384829926523123111623060914616825381518543330877184649 / 11455505422953901835316888264894286652420580877438926183958490006283284594729542501392602033360001696388405159401465053184000000 : ℚ) := by
    have e := pade6605_rec c hc 28
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h32 - (1 / 497 : ℚ) * h31 - (-1 / 34293 : ℚ) * h30 - (1 / 4663848 : ℚ) * h29 - (-1 / 1562389080 : ℚ) * h28
  have h34 : coeff 34 c = (126596142197818046022303007984544298837199370801997170343033451939387 / 711673274401011151519061683456557558281628587010893289178421191640349055447572827899015401322490105388129670527816016429056000000 : ℚ) := by
    have e := pade6605_rec c hc 29
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h33 - (1 / 497 : ℚ) * h32 - (-1 / 34293 : ℚ) * h31 - (1 / 4663848 : ℚ) * h30 - (-1 / 1562389080 : ℚ) * h29
  have h35 : coeff 35 c = (102238992981566109531250793038816495849208544688860231182772842813134307 / 67708595326512200955523528564056886094914143768216387532434992172662809135282078846312325281821708626626656854016415803060387840000000 : ℚ) := by
    have e := pade6605_rec c hc 30
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h34 - (1 / 497 : ℚ) * h33 - (-1 / 34293 : ℚ) * h32 - (1 / 4663848 : ℚ) * h31 - (-1 / 1562389080 : ℚ) * h30
  have h36 : coeff 36 c = (1234264354757133296072326458243427370622216175298390703519672452649310193761 / 126313038758545310160806599058567832039997255834043385024148749349795638823986821145286418256389444853950192126116301124108633482723328000000 : ℚ) := by
    have e := pade6605_rec c hc 31
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h35 - (1 / 497 : ℚ) * h34 - (-1 / 34293 : ℚ) * h33 - (1 / 4663848 : ℚ) * h32 - (-1 / 1562389080 : ℚ) * h31
  have h37 : coeff 37 c = (1311402332658709354967161108179637503672420373189750521518234246887628910037 / 44841128759283585107086342665791580374199025821085401683572806019177451782515321506576678481018252923152318204771286899058564886366781440000000 : ℚ) := by
    have e := pade6605_rec c hc 32
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h36 - (1 / 497 : ℚ) * h35 - (-1 / 34293 : ℚ) * h34 - (1 / 4663848 : ℚ) * h33 - (-1 / 1562389080 : ℚ) * h32
  have h38 : coeff 38 c = (-625387044196041302769979230262974179147391857970590017827905300559706838051 / 22286040993363941798221912304898415445976915833079444636735684591531193535910114788768609205066071702806702147771329588832106748524290375680000000 : ℚ) := by
    have e := pade6605_rec c hc 33
    simp only [Nat.reduceAdd] at e
    linear_combination e - (-5 / 71 : ℚ) * h37 - (1 / 497 : ℚ) * h36 - (-1 / 34293 : ℚ) * h35 - (1 / 4663848 : ℚ) * h34 - (-1 / 1562389080 : ℚ) * h33
  rw [h38]
  norm_num

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_39051.main) := by
  intro h
  have hpos := h 66 5 ⟨2, by norm_num⟩ (OMA.S_arxiv_2610_39051.qPade 66 5)⁻¹
    (PowerSeries.mul_inv_cancel _ OMA.Helpers.pade6605_const) 38
  have hneg := OMA.Helpers.pade6605_neg (OMA.S_arxiv_2610_39051.qPade 66 5)⁻¹
    (PowerSeries.mul_inv_cancel _ OMA.Helpers.pade6605_const)
  linarith
