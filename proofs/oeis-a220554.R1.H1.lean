import OMAReductions.R_oeis_a220554_R1
import Mathlib

-- Step oeis-a220554.R1.H1: hypothesis H1 of reduction oeis-a220554.R1
-- Credit: @prathameshnium. Finite check for 2 ≤ n ≤ 638.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 1623077.

/-! Step oeis-a220554.R1.H1. -/

namespace OMA.Aoeis_a220554Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1276` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1276 2

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
  have hnd := noDiv_sound p 1276 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [p, q] => (decide (0 < q) && (decide (p + q = 2 * n) && (isPrimeB (p) && (isPrimeB (2 * p + 1) && isPrimeB ((p - 1) ^ 2 + q ^ 2)))))
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
    ∃ p q : ℕ, 0 < q ∧ p + q = 2 * n ∧
    p.Prime ∧ (2 * p + 1).Prime ∧ ((p - 1) ^ 2 + q ^ 2).Prime := by
  unfold core at h
  split at h
  next p q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4⟩ := h
    exact ⟨p, q, a0, a1, isPrimeB_sound _ a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 2, …, 638`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[2, 2], [2, 4], [2, 6], [3, 7], [2, 10], [5, 9], [2, 14], [2, 16], [3, 17], [2, 20], [11, 13], [2, 24], [2, 26], [3, 27], [11, 21], [5, 29], [3, 33], [2, 36], [3, 37], [2, 40], [29, 15], [5, 41], [3, 45], [3, 47], [41, 11]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 2 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[5, 49], [2, 54], [2, 56], [3, 57], [29, 33], [11, 53], [23, 43], [2, 66], [3, 67], [11, 61], [41, 33], [2, 74], [41, 37], [5, 75], [29, 53], [5, 79], [2, 84], [3, 85], [3, 87], [2, 90], [5, 89], [2, 94], [3, 95], [3, 97], [29, 73]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 27 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[5, 99], [3, 103], [41, 67], [11, 99], [2, 110], [5, 109], [23, 93], [2, 116], [3, 117], [2, 120], [5, 119], [2, 124], [2, 126], [5, 125], [2, 130], [5, 129], [2, 134], [3, 135], [3, 137], [29, 113], [11, 133], [53, 93], [2, 146], [3, 147], [2, 150]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 52 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[11, 143], [5, 151], [2, 156], [41, 119], [2, 160], [11, 153], [3, 163], [11, 157], [3, 167], [2, 170], [11, 163], [23, 153], [2, 176], [3, 177], [2, 180], [5, 179], [2, 184], [41, 147], [11, 179], [89, 103], [11, 183], [3, 193], [11, 187], [41, 159], [29, 173]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 77 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[131, 73], [2, 204], [2, 206], [3, 207], [2, 210], [89, 125], [5, 211], [3, 215], [3, 217], [11, 211], [5, 219], [2, 224], [11, 217], [41, 189], [2, 230], [5, 229], [3, 233], [2, 236], [11, 229], [2, 240], [89, 155], [3, 243], [3, 245], [5, 245], [2, 250]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 102 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[5, 249], [3, 253], [2, 256], [53, 207], [2, 260], [11, 253], [2, 264], [3, 265], [3, 267], [2, 270], [41, 233], [53, 223], [3, 275], [3, 277], [2, 280], [29, 255], [2, 284], [11, 277], [3, 287], [41, 251], [5, 289], [3, 293], [11, 287], [5, 295], [2, 300]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 127 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[5, 299], [3, 303], [2, 306], [3, 307], [41, 271], [11, 303], [2, 314], [11, 307], [3, 317], [11, 311], [41, 283], [29, 297], [2, 326], [41, 289], [11, 321], [29, 305], [23, 313], [23, 315], [5, 335], [2, 340], [11, 333], [29, 317], [23, 325], [3, 347], [2, 350]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 152 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[89, 265], [5, 351], [83, 275], [3, 357], [179, 183], [41, 323], [5, 361], [11, 357], [5, 365], [89, 283], [5, 369], [3, 373], [3, 375], [11, 369], [41, 341], [131, 253], [2, 384], [2, 386], [23, 367], [131, 261], [5, 389], [5, 391], [2, 396], [5, 395], [2, 400]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 177 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[239, 165], [3, 403], [2, 406], [3, 407], [41, 371], [41, 373], [5, 411], [11, 407], [11, 409], [2, 420], [11, 413], [3, 423], [3, 425], [3, 427], [2, 430], [5, 429], [23, 413], [2, 436], [191, 249], [2, 440], [5, 439], [2, 444], [41, 407], [3, 447], [11, 441]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 202 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[29, 425], [3, 453], [3, 455], [5, 455], [29, 433], [179, 285], [2, 464], [2, 466], [23, 447], [2, 470], [5, 469], [2, 474], [3, 475], [3, 477], [11, 471], [11, 473], [3, 483], [11, 477], [3, 487], [2, 490], [5, 489], [29, 467], [2, 496], [23, 477], [29, 473]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 227 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[5, 499], [3, 503], [41, 467], [3, 507], [41, 471], [11, 503], [23, 493], [131, 387], [5, 515], [41, 481], [5, 519], [23, 503], [11, 517], [5, 525], [41, 491], [5, 529], [3, 533], [2, 536], [11, 529], [29, 513], [29, 515], [2, 544], [53, 495], [3, 547], [89, 463]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 252 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[11, 543], [5, 551], [2, 556], [5, 555], [131, 431], [41, 523], [23, 543], [23, 545], [11, 559], [2, 570], [29, 545], [3, 573], [2, 576], [3, 577], [11, 571], [11, 573], [2, 584], [11, 577], [5, 585], [11, 581], [29, 565], [2, 594], [113, 485], [5, 595], [11, 591]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 277 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[11, 593], [5, 601], [3, 605], [3, 607], [89, 523], [5, 609], [3, 613], [3, 615], [5, 615], [41, 581], [131, 493], [3, 623], [41, 587], [11, 619], [11, 621], [5, 629], [2, 634], [2, 636], [5, 635], [11, 631], [5, 639], [2, 644], [2, 646], [41, 609], [179, 473]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 302 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[41, 613], [2, 654], [11, 647], [23, 637], [29, 633], [5, 659], [3, 663], [3, 665], [3, 667], [41, 631], [131, 543], [2, 674], [23, 655], [3, 677], [2, 680], [11, 673], [29, 657], [2, 686], [5, 685], [2, 690], [5, 689], [5, 691], [2, 696], [41, 659], [2, 700]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 327 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[5, 699], [2, 704], [11, 697], [3, 707], [11, 701], [89, 625], [2, 714], [2, 716], [3, 717], [89, 633], [5, 719], [23, 703], [23, 705], [5, 725], [41, 691], [5, 729], [53, 683], [11, 727], [41, 699], [2, 740], [5, 739], [3, 743], [3, 745], [5, 745], [2, 750]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 352 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[131, 623], [3, 753], [3, 755], [5, 755], [2, 760], [179, 585], [2, 764], [41, 727], [3, 767], [29, 743], [5, 769], [5, 771], [11, 767], [5, 775], [2, 780], [5, 779], [2, 784], [3, 785], [3, 787], [89, 703], [11, 783], [5, 791], [3, 795], [5, 795], [131, 671]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 377 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[41, 763], [23, 783], [3, 805], [5, 805], [11, 801], [11, 803], [3, 813], [2, 816], [173, 647], [41, 781], [5, 819], [3, 823], [2, 826], [3, 827], [131, 701], [131, 703], [29, 807], [41, 797], [3, 837], [11, 831], [11, 833], [23, 823], [3, 845], [3, 847], [179, 673]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 402 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[29, 825], [3, 853], [41, 817], [5, 855], [2, 860], [5, 859], [2, 864], [11, 857], [11, 859], [41, 831], [29, 845], [173, 703], [23, 855], [23, 857], [11, 871], [5, 879], [3, 883], [41, 847], [83, 807], [2, 890], [131, 763], [53, 843], [23, 875], [3, 897], [11, 891]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 427 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[5, 899], [3, 903], [2, 906], [113, 797], [2, 910], [29, 885], [23, 893], [53, 865], [11, 909], [2, 920], [11, 913], [113, 813], [11, 917], [5, 925], [2, 930], [359, 575], [5, 931], [2, 936], [41, 899], [41, 901], [11, 933], [5, 941], [2, 946], [5, 945], [2, 950]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 452 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[11, 943], [3, 953], [41, 917], [11, 949], [2, 960], [41, 923], [3, 963], [2, 966], [3, 967], [89, 883], [41, 933], [3, 973], [11, 967], [11, 969], [29, 953], [29, 955], [3, 983], [2, 986], [11, 979], [11, 981], [11, 983], [3, 993], [11, 987], [3, 997], [41, 961]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 477 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[5, 999], [2, 1004], [173, 835], [23, 987], [2, 1010], [5, 1009], [5, 1011], [11, 1007], [5, 1015], [179, 843], [29, 995], [23, 1003], [23, 1005], [3, 1027], [131, 901], [29, 1005], [5, 1031], [2, 1036], [5, 1035], [41, 1001], [41, 1003], [179, 867], [11, 1037], [5, 1045], [29, 1023]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 502 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[29, 1025], [2, 1054], [3, 1055], [3, 1057], [2, 1060], [11, 1053], [53, 1013], [2, 1066], [5, 1065], [2, 1070], [5, 1069], [3, 1073], [3, 1075], [41, 1039], [2, 1080], [29, 1055], [3, 1083], [23, 1065], [3, 1087], [41, 1051], [29, 1065], [2, 1094], [2, 1096], [23, 1077], [11, 1091]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 527 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[41, 1063], [23, 1083], [2, 1106], [83, 1027], [11, 1101], [5, 1109], [29, 1087], [23, 1095], [3, 1117], [89, 1033], [5, 1119], [2, 1124], [173, 955], [23, 1107], [29, 1103], [191, 943], [5, 1131], [23, 1115], [83, 1057], [2, 1140], [5, 1139], [2, 1144], [2, 1146], [11, 1139], [2, 1150]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 552 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[29, 1125], [53, 1103], [2, 1156], [3, 1157], [29, 1133], [11, 1153], [5, 1161], [11, 1157], [83, 1087], [41, 1131], [5, 1169], [2, 1174], [2, 1176], [3, 1177], [41, 1141], [41, 1143], [2, 1184], [3, 1185], [53, 1137], [179, 1013], [11, 1183], [173, 1023], [3, 1195], [3, 1197], [11, 1191]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 577 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[29, 1175], [3, 1203], [23, 1185], [41, 1169], [2, 1210], [5, 1209], [29, 1187], [41, 1177], [11, 1209], [239, 983], [131, 1093], [173, 1053], [11, 1217], [23, 1207], [11, 1221], [11, 1223], [5, 1231], [3, 1235], [3, 1237], [11, 1231], [5, 1239], [2, 1244], [2, 1246], [3, 1247], [89, 1163]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 602 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[89, 1165], [5, 1251], [3, 1255], [3, 1257], [191, 1071], [89, 1175], [3, 1263], [23, 1245], [5, 1265], [11, 1261], [5, 1269], [2, 1274]]
theorem len25 : w25.length = 12 := rfl
theorem ok25 : checkList 627 w25 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `2 ≤ n ≤ 638` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 638) : ∃ x, good n x = true := by
  by_cases c0 : n < 27
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 52
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 77
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 102
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 127
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 152
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 177
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 202
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 227
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 252
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 277
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 302
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 327
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 352
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 377
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 402
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 427
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 452
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 477
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 502
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 527
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 552
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 577
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 602
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 627
  · exact chunk ok24 len24 (by omega) (by omega)
  exact chunk ok25 len25 (by omega) (by omega)

end OMA.Aoeis_a220554Tab

open OMA.Aoeis_a220554Tab in
theorem OMA.solution : OMA.R_oeis_a220554_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
