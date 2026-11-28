import OMAReductions.R_oeis_a159351_R1
import Mathlib

-- Step oeis-a159351.R1.H1: hypothesis H1 of reduction oeis-a159351.R1
-- Credit: @prathameshnium. Finite check for 1 ≤ n ≤ 633.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1595173.

/-! Step oeis-a159351.R1.H1. -/

namespace OMA.Aoeis_a159351Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1265` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1265 2

theorem noDiv_sound (p : ℕ) : ∀ f d, noDiv p f d = true → ∀ m, d ≤ m → m * m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro d h; simp [noDiv] at h
  | succ f ih =>
    intro d h m hdm hmm hdiv
    simp only [noDiv] at h
    by_cases h1 : Nat.blt p (d * d) = true
    · rw [Nat.blt_eq] at h1
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : Nat.beq (p % d) 0 = true
      · rw [if_pos h2] at h; exact Bool.false_ne_true h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with h3 | h3
        · subst h3
          exact h2 (by rw [Nat.beq_eq]; exact Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih (d + 1) h m h3 hmm hdiv

theorem isPrimeB_sound (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨h2, h⟩ := h
  have hnd := noDiv_sound p 1265 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [a, b] => (decide (0 < a) && (decide (a < b) && (decide (a + b = 2 * n + 1) && isPrimeB (a ^ 2 + b ^ 2))))
  | _ => false

def good (n : ℕ) (w : List ℕ) : Bool := core n w

/-- `checkList n l`: entry `i` of `l` is a witness that `good (n + i) _` holds. -/
def checkList : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | n, x :: xs => good n x && checkList (n + 1) xs

theorem checkList_sound : ∀ (l : List (List ℕ)) (n : ℕ), checkList n l = true →
    ∀ i, i < l.length → ∃ x, good (n + i) x = true := by
  intro l
  induction l with
  | nil => intro n _ i hi; simp at hi
  | cons x xs ih =>
    intro n h i hi
    simp only [checkList, Bool.and_eq_true] at h
    cases i with
    | zero => exact ⟨x, by simpa using h.1⟩
    | succ i =>
      obtain ⟨y, hy⟩ := ih (n + 1) h.2 i (by simpa using hi)
      exact ⟨y, by rw [show n + (i + 1) = n + 1 + i by omega]; exact hy⟩

theorem core_sound (n : ℕ) (w : List ℕ) (h : core n w = true) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b = 2 * n + 1 ∧ (a ^ 2 + b ^ 2).Prime := by
  unfold core at h
  split at h
  next a b =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3⟩ := h
    exact ⟨a, b, a0, a1, a2, isPrimeB_sound _ a3⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 1, …, 633`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[1, 2], [1, 4], [1, 6], [2, 7], [1, 10], [3, 10], [1, 14], [1, 16], [2, 17], [1, 20], [3, 20], [1, 24], [1, 26], [2, 27], [5, 26], [4, 29], [2, 33], [1, 36], [2, 37], [1, 40], [3, 40], [4, 41], [2, 45], [2, 47], [5, 46]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 1 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[4, 49], [1, 54], [1, 56], [2, 57], [3, 58], [5, 58], [3, 62], [1, 66], [2, 67], [6, 65], [3, 70], [1, 74], [5, 72], [4, 75], [5, 76], [4, 79], [1, 84], [2, 85], [2, 87], [1, 90], [4, 89], [1, 94], [2, 95], [2, 97], [3, 98]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 26 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[3, 100], [2, 103], [5, 102], [7, 102], [1, 110], [3, 110], [3, 112], [1, 116], [2, 117], [1, 120], [4, 119], [1, 124], [1, 126], [4, 125], [1, 130], [4, 129], [1, 134], [2, 135], [2, 137], [5, 136], [3, 140], [3, 142], [1, 146], [2, 147], [1, 150]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 51 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[5, 148], [4, 151], [1, 156], [5, 154], [1, 160], [3, 160], [2, 163], [10, 157], [2, 167], [1, 170], [3, 170], [6, 169], [1, 176], [2, 177], [1, 180], [4, 179], [1, 184], [5, 182], [10, 179], [3, 188], [3, 190], [2, 193], [10, 187], [7, 192], [8, 193]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 76 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[3, 200], [1, 204], [1, 206], [2, 207], [1, 210], [8, 205], [3, 212], [2, 215], [2, 217], [3, 218], [3, 220], [1, 224], [7, 220], [7, 222], [1, 230], [4, 229], [2, 233], [1, 236], [9, 230], [1, 240], [13, 230], [2, 243], [2, 245], [4, 245], [1, 250]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 101 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[4, 249], [2, 253], [1, 256], [9, 250], [1, 260], [8, 255], [1, 264], [2, 265], [2, 267], [1, 270], [5, 268], [8, 267], [2, 275], [2, 277], [1, 280], [8, 275], [1, 284], [5, 282], [2, 287], [8, 283], [4, 289], [2, 293], [10, 287], [4, 295], [1, 300]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 126 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[4, 299], [2, 303], [1, 306], [2, 307], [3, 308], [5, 308], [1, 314], [5, 312], [2, 317], [5, 316], [3, 320], [6, 319], [1, 326], [9, 320], [8, 323], [5, 328], [3, 332], [6, 331], [4, 335], [1, 340], [5, 338], [16, 329], [5, 342], [2, 347], [1, 350]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 151 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[3, 350], [4, 351], [16, 341], [2, 357], [3, 358], [5, 358], [4, 361], [10, 357], [4, 365], [3, 368], [4, 369], [2, 373], [2, 375], [5, 374], [13, 368], [3, 380], [1, 384], [1, 386], [5, 384], [5, 386], [4, 389], [4, 391], [1, 396], [4, 395], [1, 400]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 176 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[3, 400], [2, 403], [1, 406], [2, 407], [8, 403], [3, 410], [3, 412], [5, 412], [10, 409], [1, 420], [5, 418], [2, 423], [2, 425], [2, 427], [1, 430], [4, 429], [11, 424], [1, 436], [12, 427], [1, 440], [4, 439], [1, 444], [5, 442], [2, 447], [3, 448]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 201 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[14, 439], [2, 453], [2, 455], [4, 455], [6, 455], [5, 458], [1, 464], [1, 466], [9, 460], [1, 470], [4, 469], [1, 474], [2, 475], [2, 477], [5, 476], [5, 478], [2, 483], [7, 480], [2, 487], [1, 490], [3, 490], [8, 487], [1, 496], [12, 487], [13, 488]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 226 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[4, 499], [2, 503], [5, 502], [2, 507], [15, 496], [10, 503], [3, 512], [16, 501], [4, 515], [5, 516], [4, 519], [8, 517], [10, 517], [4, 525], [13, 518], [3, 530], [2, 533], [1, 536], [10, 529], [3, 538], [5, 538], [1, 544], [6, 541], [2, 547], [6, 545]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 251 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[9, 544], [4, 551], [1, 556], [4, 555], [8, 553], [29, 534], [6, 559], [22, 545], [7, 562], [1, 570], [5, 568], [2, 573], [1, 576], [2, 577], [3, 578], [8, 575], [1, 584], [10, 577], [4, 585], [10, 581], [5, 588], [1, 594], [7, 590], [4, 595], [3, 598]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 276 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[10, 593], [4, 601], [2, 605], [2, 607], [3, 608], [4, 609], [2, 613], [2, 615], [4, 615], [8, 613], [5, 618], [2, 623], [26, 601], [5, 624], [3, 628], [4, 629], [1, 634], [1, 636], [4, 635], [6, 635], [3, 640], [1, 644], [1, 646], [7, 642], [26, 625]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 301 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[5, 648], [1, 654], [7, 650], [9, 650], [11, 650], [4, 659], [2, 663], [2, 665], [2, 667], [16, 655], [13, 660], [1, 674], [5, 672], [2, 677], [1, 680], [3, 680], [3, 682], [1, 686], [4, 685], [1, 690], [4, 689], [4, 691], [1, 696], [7, 692], [1, 700]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 326 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[4, 699], [1, 704], [10, 697], [2, 707], [5, 706], [13, 700], [1, 714], [1, 716], [2, 717], [6, 715], [4, 719], [12, 713], [5, 722], [4, 725], [11, 720], [4, 729], [16, 719], [5, 732], [9, 730], [1, 740], [3, 740], [2, 743], [2, 745], [4, 745], [1, 750]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 351 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[5, 748], [2, 753], [2, 755], [4, 755], [1, 760], [13, 750], [1, 764], [11, 756], [2, 767], [11, 760], [4, 769], [4, 771], [5, 772], [4, 775], [1, 780], [4, 779], [1, 784], [2, 785], [2, 787], [6, 785], [8, 785], [4, 791], [2, 795], [4, 795], [8, 793]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 376 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[3, 800], [3, 802], [2, 805], [4, 805], [5, 806], [10, 803], [2, 813], [1, 816], [17, 802], [3, 818], [4, 819], [2, 823], [1, 826], [2, 827], [11, 820], [5, 828], [6, 829], [5, 832], [2, 837], [6, 835], [5, 838], [6, 839], [2, 845], [2, 847], [6, 845]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 401 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[3, 850], [2, 853], [5, 852], [4, 855], [1, 860], [4, 859], [1, 864], [5, 862], [10, 859], [8, 863], [23, 850], [8, 867], [11, 866], [5, 874], [10, 871], [4, 879], [2, 883], [25, 862], [5, 884], [1, 890], [3, 890], [8, 887], [22, 875], [2, 897], [6, 895]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 426 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[4, 899], [2, 903], [1, 906], [19, 890], [1, 910], [3, 910], [7, 908], [5, 912], [5, 914], [1, 920], [10, 913], [3, 922], [10, 917], [4, 925], [1, 930], [14, 919], [4, 931], [1, 936], [5, 934], [5, 936], [9, 934], [4, 941], [1, 946], [4, 945], [1, 950]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 451 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[10, 943], [2, 953], [5, 952], [5, 954], [1, 960], [5, 958], [2, 963], [1, 966], [2, 967], [3, 968], [5, 968], [2, 973], [7, 970], [7, 972], [25, 956], [8, 975], [2, 983], [1, 986], [7, 982], [5, 986], [10, 983], [2, 993], [6, 991], [2, 997], [8, 993]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 476 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[4, 999], [1, 1004], [12, 995], [5, 1004], [1, 1010], [3, 1010], [4, 1011], [10, 1007], [4, 1015], [15, 1006], [5, 1018], [8, 1017], [5, 1022], [2, 1027], [3, 1028], [19, 1014], [4, 1031], [1, 1036], [4, 1035], [5, 1036], [5, 1038], [8, 1037], [10, 1037], [4, 1045], [3, 1048]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 501 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[8, 1045], [1, 1054], [2, 1055], [2, 1057], [1, 1060], [5, 1058], [14, 1051], [1, 1066], [4, 1065], [1, 1070], [4, 1069], [2, 1073], [2, 1075], [7, 1072], [1, 1080], [8, 1075], [2, 1083], [15, 1072], [2, 1087], [3, 1088], [5, 1088], [1, 1094], [1, 1096], [5, 1094], [5, 1096]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 526 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[5, 1098], [3, 1102], [1, 1106], [7, 1102], [6, 1105], [4, 1109], [3, 1112], [11, 1106], [2, 1117], [8, 1113], [4, 1119], [1, 1124], [12, 1115], [12, 1117], [16, 1115], [5, 1128], [3, 1132], [7, 1130], [5, 1134], [1, 1140], [4, 1139], [1, 1144], [1, 1146], [10, 1139], [1, 1150]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 551 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[5, 1148], [8, 1147], [1, 1156], [2, 1157], [11, 1150], [10, 1153], [4, 1161], [7, 1160], [12, 1157], [5, 1166], [4, 1169], [1, 1174], [1, 1176], [2, 1177], [11, 1170], [18, 1165], [1, 1184], [2, 1185], [9, 1180], [8, 1183], [3, 1190], [8, 1187], [2, 1195], [2, 1197], [5, 1196]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 576 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[5, 1198], [2, 1203], [6, 1201], [17, 1192], [1, 1210], [4, 1209], [13, 1202], [5, 1212], [10, 1209], [8, 1213], [5, 1218], [3, 1222], [10, 1217], [7, 1222], [3, 1228], [10, 1223], [4, 1231], [2, 1235], [2, 1237], [6, 1235], [4, 1239], [1, 1244], [1, 1246], [2, 1247], [5, 1246]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 601 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[19, 1234], [3, 1252], [2, 1255], [2, 1257], [3, 1258], [5, 1258], [2, 1263], [11, 1256]]
theorem len25 : w25.length = 8 := rfl
theorem ok25 : checkList 626 w25 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `1 ≤ n ≤ 633` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 633) : ∃ x, good n x = true := by
  by_cases c0 : n < 26
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 51
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 76
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 101
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 126
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 151
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 176
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 201
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 226
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 251
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 276
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 301
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 326
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 351
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 376
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 401
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 426
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 451
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 476
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 501
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 526
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 551
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 576
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 601
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 626
  · exact chunk ok24 len24 (by omega) (by omega)
  exact chunk ok25 len25 (by omega) (by omega)

end OMA.Aoeis_a159351Tab

open OMA.Aoeis_a159351Tab in
theorem OMA.solution : OMA.R_oeis_a159351_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
