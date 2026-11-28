import OMAReductions.R_oeis_a219923_R1
import Mathlib

-- Step oeis-a219923.R1.H1: hypothesis H1 of reduction oeis-a219923.R1
-- Credit: @prathameshnium. Finite check for 624 ≤ n ≤ 1623.
-- A witness is listed for each n; the Lean kernel checks every one (decide +kernel) with a verified
-- trial-division primality test, so no entry is trusted. Largest number tested: 997021.

/-! Step oeis-a219923.R1.H1. -/

namespace OMA.Aoeis_a219923Tab

/-- `noDiv p f d = true`: no `m` with `d ≤ m`, `m * m ≤ p` divides `p` (checked with fuel `f`). -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if Nat.blt p (d * d) then true else if Nat.beq (p % d) 0 then false else noDiv p f (d + 1)

/-- Trial-division primality test with a fixed divisor budget `1000` (enough for every number checked here;
a budget that ran out would make the check fail, never pass). -/
def isPrimeB (p : ℕ) : Bool := Nat.ble 2 p && noDiv p 1000 2

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
  have hnd := noDiv_sound p 1000 2 h
  by_contra hp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  exact hnd p.minFac hmp.two_le (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd p)

/-- The condition to certify for `n` with witness list `w`. -/
def core (n : ℕ) : List ℕ → Bool
  | [x, y] => (decide (0 < x) && (decide (0 < y) && (decide (n = x + y) && (isPrimeB (x - 1) && (isPrimeB (x + 1) && isPrimeB (2 * x * y + 1))))))
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
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
      (x - 1).Prime ∧ (x + 1).Prime ∧ (2 * x * y + 1).Prime := by
  unfold core at h
  split at h
  next x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
    exact ⟨x, y, a0, a1, a2, isPrimeB_sound _ a3, isPrimeB_sound _ a4, isPrimeB_sound _ a5⟩
  next => exact absurd h Bool.false_ne_true



/-! One witness for each `n = 624, …, 1623`, in chunks of 25 so each kernel check stays small. -/
def w0 : List (List ℕ) := [[6, 618], [4, 621], [12, 614], [60, 567], [4, 624], [6, 623], [4, 626], [30, 601], [432, 200], [138, 495], [6, 628], [6, 629], [6, 630], [6, 631], [180, 458], [4, 635], [12, 628], [6, 635], [12, 630], [4, 639], [102, 542], [6, 639], [6, 640], [12, 635], [4, 644]]
theorem len0 : w0.length = 25 := rfl
theorem ok0 : checkList 624 w0 = true := by decide +kernel

def w1 : List (List ℕ) := [[6, 643], [12, 638], [6, 645], [6, 646], [18, 635], [30, 624], [4, 651], [30, 626], [192, 465], [4, 654], [42, 617], [42, 618], [30, 631], [6, 656], [4, 659], [4, 660], [18, 647], [4, 662], [6, 661], [30, 638], [180, 489], [18, 652], [12, 659], [6, 666], [18, 655]]
theorem len1 : w1.length = 25 := rfl
theorem ok1 : checkList 649 w1 = true := by decide +kernel

def w2 : List (List ℕ) := [[6, 668], [12, 663], [12, 664], [6, 671], [4, 674], [102, 577], [6, 674], [4, 677], [240, 442], [30, 653], [4, 680], [4, 681], [6, 680], [42, 645], [18, 670], [12, 677], [6, 684], [6, 685], [6, 686], [150, 543], [4, 690], [6, 689], [12, 684], [6, 691], [18, 680]]
theorem len2 : w2.length = 25 := rfl
theorem ok2 : checkList 674 w2 = true := by decide +kernel

def w3 : List (List ℕ) := [[6, 693], [4, 696], [192, 509], [6, 696], [108, 595], [6, 698], [6, 699], [12, 694], [60, 647], [18, 690], [4, 705], [30, 680], [4, 707], [60, 652], [108, 605], [18, 696], [4, 711], [6, 710], [12, 705], [30, 688], [18, 701], [12, 708], [4, 717], [12, 710], [60, 663]]
theorem len3 : w3.length = 25 := rfl
theorem ok3 : checkList 699 w3 = true := by decide +kernel

def w4 : List (List ℕ) := [[30, 694], [6, 719], [6, 720], [72, 655], [18, 710], [4, 725], [6, 724], [12, 719], [6, 726], [18, 715], [6, 728], [4, 731], [4, 732], [12, 725], [138, 600], [4, 735], [270, 470], [4, 737], [150, 592], [240, 503], [12, 732], [30, 715], [18, 728], [6, 741], [4, 744]]
theorem len4 : w4.length = 25 := rfl
theorem ok4 : checkList 724 w4 = true := by decide +kernel

def w5 : List (List ℕ) := [[18, 731], [6, 744], [6, 745], [12, 740], [180, 573], [18, 736], [60, 695], [6, 750], [6, 751], [18, 740], [12, 747], [6, 754], [12, 749], [420, 342], [4, 759], [12, 752], [4, 761], [12, 754], [6, 761], [4, 764], [4, 765], [18, 752], [6, 765], [72, 700], [138, 635]]
theorem len5 : w5.length = 25 := rfl
theorem ok5 : checkList 749 w5 = true := by decide +kernel

def w6 : List (List ℕ) := [[12, 762], [12, 763], [6, 770], [312, 465], [18, 760], [6, 773], [12, 768], [4, 777], [12, 770], [18, 765], [6, 778], [6, 779], [4, 782], [42, 745], [30, 758], [6, 783], [18, 772], [6, 785], [6, 786], [18, 775], [30, 764], [4, 791], [4, 792], [30, 767], [4, 794]]
theorem len6 : w6.length = 25 := rfl
theorem ok6 : checkList 774 w6 = true := by decide +kernel

def w7 : List (List ℕ) := [[4, 795], [12, 788], [30, 771], [42, 760], [30, 773], [12, 792], [102, 703], [6, 800], [6, 801], [30, 778], [18, 791], [4, 806], [6, 805], [192, 620], [4, 809], [4, 810], [12, 803], [6, 810], [6, 811], [150, 668], [4, 815], [4, 816], [6, 815], [12, 810], [4, 819]]
theorem len7 : w7.length = 25 := rfl
theorem ok7 : checkList 799 w7 = true := by decide +kernel

def w8 : List (List ℕ) := [[6, 818], [4, 821], [4, 822], [60, 767], [30, 798], [12, 817], [60, 770], [6, 825], [12, 820], [60, 773], [42, 792], [6, 829], [12, 824], [6, 831], [4, 834], [30, 809], [4, 836], [18, 823], [72, 770], [30, 813], [42, 802], [6, 839], [4, 842], [6, 841], [18, 830]]
theorem len8 : w8.length = 25 := rfl
theorem ok8 : checkList 824 w8 = true := by decide +kernel

def w9 : List (List ℕ) := [[4, 845], [12, 838], [6, 845], [12, 840], [4, 849], [6, 848], [12, 843], [18, 838], [72, 785], [4, 854], [4, 855], [12, 848], [4, 857], [6, 856], [150, 713], [180, 684], [18, 847], [6, 860], [6, 861], [270, 598], [6, 863], [6, 864], [30, 841], [12, 860], [18, 855]]
theorem len9 : w9.length = 25 := rfl
theorem ok9 : checkList 849 w9 = true := by decide +kernel

def w10 : List (List ℕ) := [[4, 870], [6, 869], [4, 872], [6, 871], [150, 728], [4, 875], [18, 862], [6, 875], [6, 876], [180, 703], [12, 872], [180, 705], [4, 882], [12, 875], [18, 870], [6, 883], [18, 872], [42, 849], [12, 880], [60, 833], [4, 890], [4, 891], [102, 794], [30, 867], [30, 868]]
theorem len10 : w10.length = 25 := rfl
theorem ok10 : checkList 874 w10 = true := by decide +kernel

def w11 : List (List ℕ) := [[72, 827], [6, 894], [4, 897], [6, 896], [4, 899], [60, 844], [6, 899], [30, 876], [12, 895], [108, 800], [6, 903], [60, 850], [6, 905], [12, 900], [30, 883], [12, 902], [6, 909], [4, 912], [60, 857], [18, 900], [4, 915], [30, 890], [12, 909], [6, 916], [60, 863]]
theorem len11 : w11.length = 25 := rfl
theorem ok11 : checkList 899 w11 = true := by decide +kernel

def w12 : List (List ℕ) := [[60, 864], [4, 921], [12, 914], [12, 915], [4, 924], [18, 911], [18, 912], [4, 927], [6, 926], [4, 929], [12, 922], [6, 929], [4, 932], [6, 931], [60, 878], [4, 935], [4, 936], [150, 791], [30, 912], [18, 925], [6, 938], [4, 941], [4, 942], [12, 935], [240, 708]]
theorem len12 : w12.length = 25 := rfl
theorem ok12 : checkList 924 w12 = true := by decide +kernel

def w13 : List (List ℕ) := [[4, 945], [6, 944], [4, 947], [6, 946], [30, 923], [30, 924], [30, 925], [18, 938], [30, 927], [30, 928], [6, 953], [4, 956], [12, 949], [30, 932], [4, 959], [4, 960], [30, 935], [18, 948], [12, 955], [60, 908], [72, 897], [12, 958], [12, 959], [6, 966], [4, 969]]
theorem len13 : w13.length = 25 := rfl
theorem ok13 : checkList 949 w13 = true := by decide +kernel

def w14 : List (List ℕ) := [[6, 968], [30, 945], [138, 838], [30, 947], [4, 974], [6, 973], [6, 974], [4, 977], [60, 922], [138, 845], [4, 980], [30, 955], [18, 968], [102, 885], [4, 984], [42, 947], [12, 978], [6, 985], [6, 986], [30, 963], [192, 802], [12, 983], [4, 992], [42, 955], [18, 980]]
theorem len14 : w14.length = 25 := rfl
theorem ok14 : checkList 974 w14 = true := by decide +kernel

def w15 : List (List ℕ) := [[12, 987], [18, 982], [6, 995], [6, 996], [4, 999], [30, 974], [4, 1001], [4, 1002], [270, 737], [60, 948], [6, 1003], [6, 1004], [12, 999], [6, 1006], [180, 833], [4, 1010], [4, 1011], [12, 1004], [12, 1005], [30, 988], [6, 1013], [18, 1002], [18, 1003], [150, 872], [30, 993]]
theorem len15 : w15.length = 25 := rfl
theorem ok15 : checkList 999 w15 = true := by decide +kernel

def w16 : List (List ℕ) := [[4, 1020], [108, 917], [6, 1020], [6, 1021], [150, 878], [6, 1023], [4, 1026], [6, 1025], [12, 1020], [4, 1029], [60, 974], [282, 753], [42, 994], [6, 1031], [4, 1034], [150, 889], [6, 1034], [4, 1037], [6, 1036], [18, 1025], [6, 1038], [4, 1041], [30, 1016], [12, 1035], [4, 1044]]
theorem len16 : w16.length = 25 := rfl
theorem ok16 : checkList 1024 w16 = true := by decide +kernel

def w17 : List (List ℕ) := [[6, 1043], [4, 1046], [4, 1047], [6, 1046], [30, 1023], [6, 1048], [6, 1049], [6, 1050], [6, 1051], [18, 1040], [6, 1053], [12, 1048], [18, 1043], [150, 912], [30, 1033], [6, 1058], [18, 1047], [6, 1060], [12, 1055], [4, 1064], [4, 1065], [30, 1040], [4, 1067], [60, 1012], [30, 1043]]
theorem len17 : w17.length = 25 := rfl
theorem ok17 : checkList 1049 w17 = true := by decide +kernel

def w18 : List (List ℕ) := [[42, 1032], [6, 1069], [6, 1070], [6, 1071], [858, 220], [12, 1067], [4, 1076], [12, 1069], [72, 1010], [60, 1023], [4, 1080], [42, 1043], [18, 1068], [6, 1081], [108, 980], [4, 1085], [4, 1086], [18, 1073], [6, 1086], [4, 1089], [12, 1082], [30, 1065], [4, 1092], [6, 1091], [4, 1094]]
theorem len18 : w18.length = 25 := rfl
theorem ok18 : checkList 1074 w18 = true := by decide +kernel

def w19 : List (List ℕ) := [[4, 1095], [12, 1088], [150, 951], [12, 1090], [30, 1073], [6, 1098], [18, 1087], [150, 956], [30, 1077], [18, 1090], [108, 1001], [4, 1106], [42, 1069], [30, 1082], [108, 1005], [6, 1108], [6, 1109], [12, 1104], [102, 1015], [60, 1058], [42, 1077], [4, 1116], [6, 1115], [12, 1110], [30, 1093]]
theorem len19 : w19.length = 25 := rfl
theorem ok19 : checkList 1099 w19 = true := by decide +kernel

def w20 : List (List ℕ) := [[6, 1118], [4, 1121], [6, 1120], [42, 1085], [30, 1098], [4, 1125], [12, 1118], [60, 1071], [6, 1126], [60, 1073], [4, 1130], [4, 1131], [30, 1106], [600, 537], [60, 1078], [6, 1133], [12, 1128], [18, 1123], [6, 1136], [828, 315], [30, 1114], [6, 1139], [4, 1142], [6, 1141], [150, 998]]
theorem len20 : w20.length = 25 := rfl
theorem ok20 : checkList 1124 w20 = true := by decide +kernel

def w21 : List (List ℕ) := [[4, 1145], [6, 1144], [12, 1139], [12, 1140], [108, 1045], [12, 1142], [4, 1151], [12, 1144], [12, 1145], [180, 978], [4, 1155], [18, 1142], [4, 1157], [6, 1156], [18, 1145], [4, 1160], [12, 1153], [6, 1160], [6, 1161], [30, 1138], [192, 977], [12, 1158], [4, 1167], [30, 1142], [30, 1143]]
theorem len21 : w21.length = 25 := rfl
theorem ok21 : checkList 1149 w21 = true := by decide +kernel

def w22 : List (List ℕ) := [[18, 1156], [6, 1169], [4, 1172], [12, 1165], [18, 1160], [150, 1029], [30, 1150], [12, 1169], [12, 1170], [4, 1179], [42, 1142], [6, 1179], [42, 1144], [6, 1181], [4, 1184], [6, 1183], [18, 1172], [4, 1187], [42, 1150], [108, 1085], [4, 1190], [12, 1183], [6, 1190], [6, 1191], [108, 1090]]
theorem len22 : w22.length = 25 := rfl
theorem ok22 : checkList 1174 w22 = true := by decide +kernel

def w23 : List (List ℕ) := [[30, 1169], [12, 1188], [6, 1195], [30, 1172], [30, 1173], [4, 1200], [6, 1199], [6, 1200], [30, 1177], [18, 1190], [6, 1203], [4, 1206], [6, 1205], [30, 1182], [30, 1183], [72, 1142], [4, 1211], [4, 1212], [6, 1211], [18, 1200], [4, 1215], [42, 1178], [12, 1209], [6, 1216], [108, 1115]]
theorem len23 : w23.length = 25 := rfl
theorem ok23 : checkList 1199 w23 = true := by decide +kernel

def w24 : List (List ℕ) := [[42, 1182], [4, 1221], [12, 1214], [6, 1221], [30, 1198], [12, 1217], [18, 1212], [4, 1227], [6, 1226], [4, 1229], [6, 1228], [42, 1193], [4, 1232], [12, 1225], [30, 1208], [6, 1233], [12, 1228], [6, 1235], [42, 1200], [18, 1225], [12, 1232], [4, 1241], [570, 676], [12, 1235], [18, 1230]]
theorem len24 : w24.length = 25 := rfl
theorem ok24 : checkList 1224 w24 = true := by decide +kernel

def w25 : List (List ℕ) := [[30, 1219], [6, 1244], [18, 1233], [12, 1240], [1050, 203], [18, 1236], [4, 1251], [30, 1226], [6, 1251], [18, 1240], [42, 1217], [228, 1032], [6, 1255], [6, 1256], [138, 1125], [60, 1204], [18, 1247], [6, 1260], [522, 745], [60, 1208], [12, 1257], [108, 1162], [42, 1229], [6, 1266], [18, 1255]]
theorem len25 : w25.length = 25 := rfl
theorem ok25 : checkList 1249 w25 = true := by decide +kernel

def w26 : List (List ℕ) := [[6, 1268], [4, 1271], [4, 1272], [30, 1247], [4, 1274], [6, 1273], [6, 1274], [60, 1221], [6, 1276], [18, 1265], [12, 1272], [6, 1279], [6, 1280], [6, 1281], [4, 1284], [12, 1277], [4, 1286], [12, 1279], [30, 1262], [4, 1289], [4, 1290], [42, 1253], [4, 1292], [6, 1291], [30, 1268]]
theorem len26 : w26.length = 25 := rfl
theorem ok26 : checkList 1274 w26 = true := by decide +kernel

def w27 : List (List ℕ) := [[198, 1101], [4, 1296], [6, 1295], [150, 1152], [18, 1285], [30, 1274], [12, 1293], [6, 1300], [12, 1295], [4, 1304], [18, 1291], [6, 1304], [4, 1307], [42, 1270], [138, 1175], [12, 1302], [30, 1285], [60, 1256], [6, 1311], [4, 1314], [42, 1277], [4, 1316], [150, 1171], [30, 1292], [60, 1263]]
theorem len27 : w27.length = 25 := rfl
theorem ok27 : checkList 1299 w27 = true := by decide +kernel

def w28 : List (List ℕ) := [[6, 1318], [12, 1313], [30, 1296], [42, 1285], [18, 1310], [4, 1325], [6, 1324], [6, 1325], [6, 1326], [108, 1225], [6, 1328], [30, 1305], [4, 1332], [6, 1331], [18, 1320], [12, 1327], [12, 1328], [18, 1323], [6, 1336], [18, 1325], [6, 1338], [4, 1341], [18, 1328], [42, 1305], [4, 1344]]
theorem len28 : w28.length = 25 := rfl
theorem ok28 : checkList 1324 w28 = true := by decide +kernel

def w29 : List (List ℕ) := [[12, 1337], [30, 1320], [6, 1345], [72, 1280], [60, 1293], [72, 1282], [6, 1349], [12, 1344], [30, 1327], [108, 1250], [42, 1317], [6, 1354], [12, 1349], [6, 1356], [60, 1303], [42, 1322], [4, 1361], [12, 1354], [6, 1361], [180, 1188], [12, 1357], [6, 1364], [4, 1367], [42, 1330], [18, 1355]]
theorem len29 : w29.length = 25 := rfl
theorem ok29 : checkList 1349 w29 = true := by decide +kernel

def w30 : List (List ℕ) := [[6, 1368], [12, 1363], [18, 1358], [6, 1371], [4, 1374], [6, 1373], [12, 1368], [18, 1363], [180, 1202], [30, 1353], [18, 1366], [138, 1247], [4, 1382], [6, 1381], [60, 1328], [12, 1377], [12, 1378], [18, 1373], [6, 1386], [4, 1389], [6, 1388], [30, 1365], [72, 1324], [6, 1391], [18, 1380]]
theorem len30 : w30.length = 25 := rfl
theorem ok30 : checkList 1374 w30 = true := by decide +kernel

def w31 : List (List ℕ) := [[4, 1395], [6, 1394], [4, 1397], [240, 1162], [150, 1253], [12, 1392], [42, 1363], [12, 1394], [42, 1365], [60, 1348], [12, 1397], [42, 1368], [4, 1407], [12, 1400], [4, 1409], [42, 1372], [30, 1385], [6, 1410], [12, 1405], [240, 1178], [4, 1415], [4, 1416], [6, 1415], [6, 1416], [4, 1419]]
theorem len31 : w31.length = 25 := rfl
theorem ok31 : checkList 1399 w31 = true := by decide +kernel

def w32 : List (List ℕ) := [[12, 1412], [4, 1421], [6, 1420], [6, 1421], [4, 1424], [6, 1423], [12, 1418], [12, 1419], [30, 1402], [30, 1403], [6, 1428], [60, 1375], [180, 1256], [30, 1407], [30, 1408], [18, 1421], [4, 1436], [4, 1437], [270, 1172], [60, 1383], [6, 1438], [72, 1373], [30, 1416], [6, 1441], [18, 1430]]
theorem len32 : w32.length = 25 := rfl
theorem ok32 : checkList 1424 w32 = true := by decide +kernel

def w33 : List (List ℕ) := [[6, 1443], [12, 1438], [6, 1445], [282, 1170], [4, 1449], [6, 1448], [6, 1449], [4, 1452], [30, 1427], [4, 1454], [12, 1447], [6, 1454], [4, 1457], [180, 1282], [18, 1445], [4, 1460], [4, 1461], [12, 1454], [42, 1425], [18, 1450], [18, 1451], [6, 1464], [6, 1465], [42, 1430], [198, 1275]]
theorem len33 : w33.length = 25 := rfl
theorem ok33 : checkList 1449 w33 = true := by decide +kernel

def w34 : List (List ℕ) := [[12, 1462], [18, 1457], [4, 1472], [522, 955], [18, 1460], [4, 1475], [72, 1408], [12, 1469], [6, 1476], [4, 1479], [6, 1478], [6, 1479], [6, 1480], [12, 1475], [30, 1458], [12, 1477], [42, 1448], [4, 1487], [12, 1480], [18, 1475], [12, 1482], [12, 1483], [6, 1490], [60, 1437], [4, 1494]]
theorem len34 : w34.length = 25 := rfl
theorem ok34 : checkList 1474 w34 = true := by decide +kernel

def w35 : List (List ℕ) := [[42, 1457], [4, 1496], [30, 1471], [30, 1472], [150, 1353], [6, 1498], [6, 1499], [18, 1488], [6, 1501], [30, 1478], [4, 1505], [4, 1506], [6, 1505], [60, 1452], [4, 1509], [6, 1508], [12, 1503], [4, 1512], [6, 1511], [4, 1514], [18, 1501], [6, 1514], [6, 1515], [12, 1510], [18, 1505]]
theorem len35 : w35.length = 25 := rfl
theorem ok35 : checkList 1499 w35 = true := by decide +kernel

def w36 : List (List ℕ) := [[4, 1520], [6, 1519], [102, 1424], [6, 1521], [18, 1510], [42, 1487], [6, 1524], [6, 1525], [6, 1526], [18, 1515], [4, 1530], [138, 1397], [42, 1494], [72, 1465], [18, 1520], [4, 1535], [4, 1536], [12, 1529], [6, 1536], [138, 1405], [6, 1538], [4, 1541], [6, 1540], [6, 1541], [30, 1518]]
theorem len36 : w36.length = 25 := rfl
theorem ok36 : checkList 1524 w36 = true := by decide +kernel

def w37 : List (List ℕ) := [[6, 1543], [12, 1538], [4, 1547], [6, 1546], [30, 1523], [4, 1550], [4, 1551], [12, 1544], [30, 1527], [4, 1554], [6, 1553], [30, 1530], [4, 1557], [12, 1550], [4, 1559], [30, 1534], [12, 1553], [4, 1562], [12, 1555], [108, 1460], [6, 1563], [30, 1540], [30, 1541], [6, 1566], [4, 1569]]
theorem len37 : w37.length = 25 := rfl
theorem ok37 : checkList 1549 w37 = true := by decide +kernel

def w38 : List (List ℕ) := [[12, 1562], [4, 1571], [4, 1572], [12, 1565], [150, 1428], [4, 1575], [12, 1568], [12, 1569], [6, 1576], [108, 1475], [4, 1580], [192, 1393], [198, 1388], [6, 1581], [30, 1558], [108, 1481], [4, 1586], [4, 1587], [42, 1550], [4, 1589], [4, 1590], [6, 1589], [6, 1590], [42, 1555], [180, 1418]]
theorem len38 : w38.length = 25 := rfl
theorem ok38 : checkList 1574 w38 = true := by decide +kernel

def w39 : List (List ℕ) := [[72, 1527], [12, 1588], [6, 1595], [30, 1572], [60, 1543], [18, 1586], [4, 1601], [30, 1576], [6, 1601], [18, 1590], [4, 1605], [6, 1604], [12, 1599], [6, 1606], [108, 1505], [12, 1602], [4, 1611], [18, 1598], [6, 1611], [18, 1600], [12, 1607], [12, 1608], [6, 1615], [42, 1580], [4, 1619]]
theorem len39 : w39.length = 25 := rfl
theorem ok39 : checkList 1599 w39 = true := by decide +kernel

theorem chunk {l : List (List ℕ)} {s L n : ℕ} (hok : checkList s l = true) (hlen : l.length = L)
    (h1 : s ≤ n) (h2 : n < s + L) : ∃ x, good n x = true := by
  obtain ⟨x, hx⟩ := checkList_sound l s hok (n - s) (by omega)
  exact ⟨x, by rwa [show s + (n - s) = n by omega] at hx⟩

/-- Every `n` with `624 ≤ n ≤ 1623` has a checked witness. -/
theorem cover (n : ℕ) (h1 : 624 ≤ n) (h2 : n ≤ 1623) : ∃ x, good n x = true := by
  by_cases c0 : n < 649
  · exact chunk ok0 len0 (by omega) (by omega)
  by_cases c1 : n < 674
  · exact chunk ok1 len1 (by omega) (by omega)
  by_cases c2 : n < 699
  · exact chunk ok2 len2 (by omega) (by omega)
  by_cases c3 : n < 724
  · exact chunk ok3 len3 (by omega) (by omega)
  by_cases c4 : n < 749
  · exact chunk ok4 len4 (by omega) (by omega)
  by_cases c5 : n < 774
  · exact chunk ok5 len5 (by omega) (by omega)
  by_cases c6 : n < 799
  · exact chunk ok6 len6 (by omega) (by omega)
  by_cases c7 : n < 824
  · exact chunk ok7 len7 (by omega) (by omega)
  by_cases c8 : n < 849
  · exact chunk ok8 len8 (by omega) (by omega)
  by_cases c9 : n < 874
  · exact chunk ok9 len9 (by omega) (by omega)
  by_cases c10 : n < 899
  · exact chunk ok10 len10 (by omega) (by omega)
  by_cases c11 : n < 924
  · exact chunk ok11 len11 (by omega) (by omega)
  by_cases c12 : n < 949
  · exact chunk ok12 len12 (by omega) (by omega)
  by_cases c13 : n < 974
  · exact chunk ok13 len13 (by omega) (by omega)
  by_cases c14 : n < 999
  · exact chunk ok14 len14 (by omega) (by omega)
  by_cases c15 : n < 1024
  · exact chunk ok15 len15 (by omega) (by omega)
  by_cases c16 : n < 1049
  · exact chunk ok16 len16 (by omega) (by omega)
  by_cases c17 : n < 1074
  · exact chunk ok17 len17 (by omega) (by omega)
  by_cases c18 : n < 1099
  · exact chunk ok18 len18 (by omega) (by omega)
  by_cases c19 : n < 1124
  · exact chunk ok19 len19 (by omega) (by omega)
  by_cases c20 : n < 1149
  · exact chunk ok20 len20 (by omega) (by omega)
  by_cases c21 : n < 1174
  · exact chunk ok21 len21 (by omega) (by omega)
  by_cases c22 : n < 1199
  · exact chunk ok22 len22 (by omega) (by omega)
  by_cases c23 : n < 1224
  · exact chunk ok23 len23 (by omega) (by omega)
  by_cases c24 : n < 1249
  · exact chunk ok24 len24 (by omega) (by omega)
  by_cases c25 : n < 1274
  · exact chunk ok25 len25 (by omega) (by omega)
  by_cases c26 : n < 1299
  · exact chunk ok26 len26 (by omega) (by omega)
  by_cases c27 : n < 1324
  · exact chunk ok27 len27 (by omega) (by omega)
  by_cases c28 : n < 1349
  · exact chunk ok28 len28 (by omega) (by omega)
  by_cases c29 : n < 1374
  · exact chunk ok29 len29 (by omega) (by omega)
  by_cases c30 : n < 1399
  · exact chunk ok30 len30 (by omega) (by omega)
  by_cases c31 : n < 1424
  · exact chunk ok31 len31 (by omega) (by omega)
  by_cases c32 : n < 1449
  · exact chunk ok32 len32 (by omega) (by omega)
  by_cases c33 : n < 1474
  · exact chunk ok33 len33 (by omega) (by omega)
  by_cases c34 : n < 1499
  · exact chunk ok34 len34 (by omega) (by omega)
  by_cases c35 : n < 1524
  · exact chunk ok35 len35 (by omega) (by omega)
  by_cases c36 : n < 1549
  · exact chunk ok36 len36 (by omega) (by omega)
  by_cases c37 : n < 1574
  · exact chunk ok37 len37 (by omega) (by omega)
  by_cases c38 : n < 1599
  · exact chunk ok38 len38 (by omega) (by omega)
  exact chunk ok39 len39 (by omega) (by omega)

end OMA.Aoeis_a219923Tab

open OMA.Aoeis_a219923Tab in
theorem OMA.solution : OMA.R_oeis_a219923_R1.H1 := by
  intro n hh0 hB
  obtain ⟨w, hw⟩ := cover n (by omega) hB
  exact core_sound n w hw
