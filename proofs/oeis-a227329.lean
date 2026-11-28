import OMAStatements.S_oeis_a227329

namespace OMA.P_oeis_a227329

open OMA.S_oeis_a227329

private def lex3Val (r : Fin 8) : ℕ :=
  4 * (r.1 % 2) + 2 * ((r.1 / 2) % 2) + (r.1 / 4)

private def colUpd (cc : ℕ) (r : Fin 8) : Option ℕ :=
  let b0 := r.1 % 2
  let b1 := (r.1 / 2) % 2
  let b2 := r.1 / 4
  let c0 := cc % 2
  let c1 := cc / 2
  if (c0 == 1 || b0 ≤ b1) && (c1 == 1 || b1 ≤ b2) then
    let nc0 := if c0 == 1 || b0 < b1 then 1 else 0
    let nc1 := if c1 == 1 || b1 < b2 then 1 else 0
    some (nc0 + 2 * nc1)
  else none

private def symOf (r1 r2 : Fin 8) : ℕ :=
  let a0 := r1.1 % 2; let a1 := (r1.1 / 2) % 2; let a2 := r1.1 / 4
  let b0 := r2.1 % 2; let b1 := (r2.1 / 2) % 2; let b2 := r2.1 / 4
  let s0 := if a0 + a1 + b0 + b1 == 2 && (a0 == a1 || a0 == b0) then 1 else 0
  let s1 := if a1 + a2 + b1 + b2 == 2 && (a1 == a2 || a1 == b1) then 1 else 0
  s0 + 2 * s1

private def nfaStep (q : Fin 32) (sym : Fin 4) (r2 : Fin 8) : Option (Fin 32) :=
  let r1 : Fin 8 := ⟨q.1 / 4, by have := q.2; omega⟩
  let cc := q.1 % 4
  if lex3Val r1 ≤ lex3Val r2 && symOf r1 r2 == sym.1 then
    match colUpd cc r2 with
    | none => none
    | some ncc =>
      if h : r2.1 * 4 + ncc < 32 then some ⟨r2.1 * 4 + ncc, h⟩ else none
  else none

private def nfaPre (sym : Fin 4) (q : Fin 32) : ℕ :=
  match sym.1 with
  | 0 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 1 else 2) else (if q.1 < 3 then 4 else 8)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 131586) else (if q.1 < 7 then 0 else 526344))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 786444)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 71303232 else 142606464)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 5 else 10)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 167774730))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 196608) else (if q.1 < 27 then 0 else 786432)) else (if q.1 < 30 then (if q.1 < 29 then 286265600 else 572531200) else (if q.1 < 31 then 1145062400 else 2290124800)))))
  | 1 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 32) else (if q.1 < 7 then 0 else 128))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 262148 else 524296)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 160))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 50332416) else (if q.1 < 27 then 0 else 201329664)) else (if q.1 < 30 then (if q.1 < 29 then 65536 else 131072) else (if q.1 < 31 then 262144 else 524288)))))
  | 2 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 33554432) else (if q.1 < 7 then 0 else 134217728))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 17408 else 34816)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 327680 else 655360)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 655360))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 3) else (if q.1 < 27 then 0 else 12)) else (if q.1 < 30 then (if q.1 < 29 then 16 else 32) else (if q.1 < 31 then 64 else 128)))))
  | 3 => (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 3072)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 10485760))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 1 else 2) else (if q.1 < 31 then 4 else 8)))))
  | _ => 0

private lemma nfaPre_testBit : ∀ sym : Fin 4, ∀ q' q : Fin 32,
    (nfaPre sym q').testBit q.1 = decide (∃ r2 : Fin 8, nfaStep q sym r2 = some q') := by decide

private def dfaMask (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 302252033 else 948176897) else (if s.1 < 3 then 1107312640 else 33816608)) else (if s.1 < 6 then (if s.1 < 5 then 268435456 else 3095693441) else (if s.1 < 7 then 1207975936 else (if s.1 < 8 then 33849472 else 276826112)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 1619001344 else 33554432) else (if s.1 < 12 then 16416 else (if s.1 < 13 then 0 else 679479296))) else (if s.1 < 16 then (if s.1 < 15 then 1115701280 else 537133088) else (if s.1 < 17 then 1216364672 else (if s.1 < 18 then 2181333120 else 3229646848))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 134217728 else 16512) else (if s.1 < 22 then 2826995712 else 1115701376)) else (if s.1 < 25 then (if s.1 < 24 then 2147778592 else 2424340608) else (if s.1 < 26 then 32768 else (if s.1 < 27 then 8390656 else 3758129152)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 8388608 else 545259520) else (if s.1 < 31 then 32 else (if s.1 < 32 then 1073741824 else 8388640))) else (if s.1 < 35 then (if s.1 < 34 then 536887296 else 2692776064) else (if s.1 < 36 then 32896 else (if s.1 < 37 then 3766517760 else 41943072)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 536887328 else 671090688) else (if s.1 < 41 then 1082146848 else 537133056)) else (if s.1 < 44 then (if s.1 < 43 then 142606464 else 2147500160) else (if s.1 < 45 then 3221258240 else (if s.1 < 46 then 2155905024 else 128)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 1073774592 else 8388736) else (if s.1 < 50 then 2147500032 else (if s.1 < 51 then 41943168 else 2147500064))) else (if s.1 < 54 then (if s.1 < 53 then 2281703424 else 537165824) else (if s.1 < 55 then 2415951872 else (if s.1 < 56 then 2147516416 else 2147483648))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 2155905152 else 3758096384) else (if s.1 < 60 then 2684387328 else (if s.1 < 61 then 536870912 else 1610612736))) else (if s.1 < 64 then (if s.1 < 63 then 16384 else 2692775936) else (if s.1 < 65 then 536870944 else (if s.1 < 66 then 2048 else 1073758208)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 262144 else 2147483776) else (if s.1 < 70 then 3221225472 else (if s.1 < 71 then 2147483680 else 2818574336))) else (if s.1 < 74 then (if s.1 < 73 then 294912 else 2415919104) else (if s.1 < 75 then 2684354560 else (if s.1 < 76 then 2155872384 else 134219776)))))))

private def dfaTransVal (s : Fin 77) (sym : Fin 4) : ℕ :=
  match s.1 with
  | 0 => (if sym.1 < 2 then (if sym.1 < 1 then 1 else 2) else (if sym.1 < 3 then 3 else 4))
  | 1 => (if sym.1 < 2 then (if sym.1 < 1 then 5 else 6) else (if sym.1 < 3 then 7 else 8))
  | 2 => (if sym.1 < 2 then (if sym.1 < 1 then 9 else 10) else (if sym.1 < 3 then 11 else 12))
  | 3 => (if sym.1 < 2 then (if sym.1 < 1 then 13 else 14) else (if sym.1 < 3 then 15 else 12))
  | 4 => (if sym.1 < 2 then (if sym.1 < 1 then 4 else 12) else (if sym.1 < 3 then 12 else 12))
  | 5 => (if sym.1 < 2 then (if sym.1 < 1 then 5 else 16) else (if sym.1 < 3 then 17 else 8))
  | 6 => (if sym.1 < 2 then (if sym.1 < 1 then 18 else 19) else (if sym.1 < 3 then 20 else 12))
  | 7 => (if sym.1 < 2 then (if sym.1 < 1 then 21 else 22) else (if sym.1 < 3 then 23 else 12))
  | 8 => (if sym.1 < 2 then (if sym.1 < 1 then 24 else 19) else (if sym.1 < 3 then 25 else 26))
  | 9 => (if sym.1 < 2 then (if sym.1 < 1 then 27 else 12) else (if sym.1 < 3 then 12 else 28))
  | 10 => (if sym.1 < 2 then (if sym.1 < 1 then 29 else 10) else (if sym.1 < 3 then 30 else 12))
  | 11 => (if sym.1 < 2 then (if sym.1 < 1 then 31 else 32) else (if sym.1 < 3 then 33 else 12))
  | 12 => (if sym.1 < 2 then (if sym.1 < 1 then 12 else 12) else (if sym.1 < 3 then 12 else 12))
  | 13 => (if sym.1 < 2 then (if sym.1 < 1 then 34 else 19) else (if sym.1 < 3 then 35 else 26))
  | 14 => (if sym.1 < 2 then (if sym.1 < 1 then 36 else 37) else (if sym.1 < 3 then 38 else 28))
  | 15 => (if sym.1 < 2 then (if sym.1 < 1 then 39 else 40) else (if sym.1 < 3 then 41 else 12))
  | 16 => (if sym.1 < 2 then (if sym.1 < 1 then 18 else 42) else (if sym.1 < 3 then 43 else 28))
  | 17 => (if sym.1 < 2 then (if sym.1 < 1 then 21 else 22) else (if sym.1 < 3 then 23 else 12))
  | 18 => (if sym.1 < 2 then (if sym.1 < 1 then 44 else 12) else (if sym.1 < 3 then 25 else 28))
  | 19 => (if sym.1 < 2 then (if sym.1 < 1 then 45 else 19) else (if sym.1 < 3 then 46 else 12))
  | 20 => (if sym.1 < 2 then (if sym.1 < 1 then 47 else 48) else (if sym.1 < 3 then 49 else 12))
  | 21 => (if sym.1 < 2 then (if sym.1 < 1 then 34 else 19) else (if sym.1 < 3 then 35 else 26))
  | 22 => (if sym.1 < 2 then (if sym.1 < 1 then 36 else 50) else (if sym.1 < 3 then 51 else 28))
  | 23 => (if sym.1 < 2 then (if sym.1 < 1 then 52 else 40) else (if sym.1 < 3 then 53 else 12))
  | 24 => (if sym.1 < 2 then (if sym.1 < 1 then 54 else 48) else (if sym.1 < 3 then 55 else 28))
  | 25 => (if sym.1 < 2 then (if sym.1 < 1 then 56 else 12) else (if sym.1 < 3 then 25 else 12))
  | 26 => (if sym.1 < 2 then (if sym.1 < 1 then 57 else 19) else (if sym.1 < 3 then 25 else 26))
  | 27 => (if sym.1 < 2 then (if sym.1 < 1 then 58 else 12) else (if sym.1 < 3 then 25 else 12))
  | 28 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 12) else (if sym.1 < 3 then 12 else 28))
  | 29 => (if sym.1 < 2 then (if sym.1 < 1 then 59 else 12) else (if sym.1 < 3 then 12 else 28))
  | 30 => (if sym.1 < 2 then (if sym.1 < 1 then 12 else 32) else (if sym.1 < 3 then 60 else 12))
  | 31 => (if sym.1 < 2 then (if sym.1 < 1 then 31 else 12) else (if sym.1 < 3 then 12 else 12))
  | 32 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 32) else (if sym.1 < 3 then 60 else 28))
  | 33 => (if sym.1 < 2 then (if sym.1 < 1 then 61 else 12) else (if sym.1 < 3 then 62 else 12))
  | 34 => (if sym.1 < 2 then (if sym.1 < 1 then 59 else 48) else (if sym.1 < 3 then 55 else 28))
  | 35 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 48) else (if sym.1 < 3 then 55 else 12))
  | 36 => (if sym.1 < 2 then (if sym.1 < 1 then 27 else 12) else (if sym.1 < 3 then 25 else 28))
  | 37 => (if sym.1 < 2 then (if sym.1 < 1 then 63 else 37) else (if sym.1 < 3 then 64 else 28))
  | 38 => (if sym.1 < 2 then (if sym.1 < 1 then 61 else 32) else (if sym.1 < 3 then 33 else 12))
  | 39 => (if sym.1 < 2 then (if sym.1 < 1 then 34 else 19) else (if sym.1 < 3 then 35 else 65))
  | 40 => (if sym.1 < 2 then (if sym.1 < 1 then 44 else 32) else (if sym.1 < 3 then 33 else 28))
  | 41 => (if sym.1 < 2 then (if sym.1 < 1 then 39 else 66) else (if sym.1 < 3 then 67 else 12))
  | 42 => (if sym.1 < 2 then (if sym.1 < 1 then 45 else 42) else (if sym.1 < 3 then 68 else 28))
  | 43 => (if sym.1 < 2 then (if sym.1 < 1 then 44 else 48) else (if sym.1 < 3 then 49 else 12))
  | 44 => (if sym.1 < 2 then (if sym.1 < 1 then 69 else 12) else (if sym.1 < 3 then 25 else 12))
  | 45 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 12) else (if sym.1 < 3 then 25 else 28))
  | 46 => (if sym.1 < 2 then (if sym.1 < 1 then 25 else 48) else (if sym.1 < 3 then 56 else 12))
  | 47 => (if sym.1 < 2 then (if sym.1 < 1 then 69 else 12) else (if sym.1 < 3 then 25 else 12))
  | 48 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 48) else (if sym.1 < 3 then 56 else 28))
  | 49 => (if sym.1 < 2 then (if sym.1 < 1 then 69 else 12) else (if sym.1 < 3 then 62 else 12))
  | 50 => (if sym.1 < 2 then (if sym.1 < 1 then 63 else 50) else (if sym.1 < 3 then 70 else 28))
  | 51 => (if sym.1 < 2 then (if sym.1 < 1 then 69 else 32) else (if sym.1 < 3 then 33 else 12))
  | 52 => (if sym.1 < 2 then (if sym.1 < 1 then 57 else 19) else (if sym.1 < 3 then 35 else 65))
  | 53 => (if sym.1 < 2 then (if sym.1 < 1 then 71 else 66) else (if sym.1 < 3 then 72 else 12))
  | 54 => (if sym.1 < 2 then (if sym.1 < 1 then 73 else 12) else (if sym.1 < 3 then 25 else 12))
  | 55 => (if sym.1 < 2 then (if sym.1 < 1 then 56 else 12) else (if sym.1 < 3 then 25 else 12))
  | 56 => (if sym.1 < 2 then (if sym.1 < 1 then 56 else 12) else (if sym.1 < 3 then 12 else 12))
  | 57 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 48) else (if sym.1 < 3 then 55 else 28))
  | 58 => (if sym.1 < 2 then (if sym.1 < 1 then 58 else 12) else (if sym.1 < 3 then 12 else 12))
  | 59 => (if sym.1 < 2 then (if sym.1 < 1 then 74 else 12) else (if sym.1 < 3 then 25 else 12))
  | 60 => (if sym.1 < 2 then (if sym.1 < 1 then 60 else 12) else (if sym.1 < 3 then 12 else 12))
  | 61 => (if sym.1 < 2 then (if sym.1 < 1 then 61 else 12) else (if sym.1 < 3 then 12 else 12))
  | 62 => (if sym.1 < 2 then (if sym.1 < 1 then 31 else 12) else (if sym.1 < 3 then 62 else 12))
  | 63 => (if sym.1 < 2 then (if sym.1 < 1 then 59 else 12) else (if sym.1 < 3 then 25 else 28))
  | 64 => (if sym.1 < 2 then (if sym.1 < 1 then 60 else 32) else (if sym.1 < 3 then 60 else 12))
  | 65 => (if sym.1 < 2 then (if sym.1 < 1 then 75 else 19) else (if sym.1 < 3 then 25 else 65))
  | 66 => (if sym.1 < 2 then (if sym.1 < 1 then 31 else 12) else (if sym.1 < 3 then 62 else 12))
  | 67 => (if sym.1 < 2 then (if sym.1 < 1 then 76 else 66) else (if sym.1 < 3 then 67 else 12))
  | 68 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 48) else (if sym.1 < 3 then 56 else 12))
  | 69 => (if sym.1 < 2 then (if sym.1 < 1 then 69 else 12) else (if sym.1 < 3 then 12 else 12))
  | 70 => (if sym.1 < 2 then (if sym.1 < 1 then 56 else 32) else (if sym.1 < 3 then 60 else 12))
  | 71 => (if sym.1 < 2 then (if sym.1 < 1 then 34 else 19) else (if sym.1 < 3 then 35 else 65))
  | 72 => (if sym.1 < 2 then (if sym.1 < 1 then 52 else 66) else (if sym.1 < 3 then 72 else 12))
  | 73 => (if sym.1 < 2 then (if sym.1 < 1 then 73 else 12) else (if sym.1 < 3 then 12 else 12))
  | 74 => (if sym.1 < 2 then (if sym.1 < 1 then 74 else 12) else (if sym.1 < 3 then 12 else 12))
  | 75 => (if sym.1 < 2 then (if sym.1 < 1 then 55 else 48) else (if sym.1 < 3 then 56 else 28))
  | 76 => (if sym.1 < 2 then (if sym.1 < 1 then 57 else 19) else (if sym.1 < 3 then 35 else 65))
  | _ => 0

private lemma dfaTransVal_lt : ∀ s : Fin 77, ∀ sym : Fin 4, dfaTransVal s sym < 77 := by decide

private def dfaTrans (s : Fin 77) (sym : Fin 4) : Fin 77 :=
  ⟨dfaTransVal s sym, dfaTransVal_lt s sym⟩

private lemma dfaTrans_empty : ∀ sym : Fin 4, dfaTrans ⟨12, by omega⟩ sym = ⟨12, by omega⟩ := by decide

private lemma dfaMask_lt : ∀ s : Fin 77, dfaMask s < 2 ^ 32 := by decide

private lemma dfaMask_ne_zero_iff : ∀ s : Fin 77, dfaMask s ≠ 0 ↔ s.1 ≠ 12 := by decide

private lemma dfaMask_init : ∀ q : Fin 32,
    (dfaMask ⟨0, by omega⟩).testBit q.1 = true ↔ colUpd 0 ⟨q.1 / 4, by have := q.2; omega⟩ = some (q.1 % 4) := by decide

private lemma dfaTrans_spec_bit_0_0 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_16 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_32 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_48 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_64 : ∀ i : Fin 13, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨64 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨64 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0 (s : Fin 77) (q' : Fin 32) :
    (dfaMask (dfaTrans s ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨0, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_32 ⟨s.1 - 32, by omega⟩ q'
  else
  if h48 : s.1 < 64 then
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_48 ⟨s.1 - 48, by omega⟩ q'
  else
    have hs : s = ⟨64 + (s.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_64 ⟨s.1 - 64, by omega⟩ q'
private lemma dfaTrans_spec_bit_1_0 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_16 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_32 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_48 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_64 : ∀ i : Fin 13, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨64 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨64 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1 (s : Fin 77) (q' : Fin 32) :
    (dfaMask (dfaTrans s ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨1, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_32 ⟨s.1 - 32, by omega⟩ q'
  else
  if h48 : s.1 < 64 then
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_48 ⟨s.1 - 48, by omega⟩ q'
  else
    have hs : s = ⟨64 + (s.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_64 ⟨s.1 - 64, by omega⟩ q'
private lemma dfaTrans_spec_bit_2_0 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_16 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_32 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_48 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_64 : ∀ i : Fin 13, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨64 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨64 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2 (s : Fin 77) (q' : Fin 32) :
    (dfaMask (dfaTrans s ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨2, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_32 ⟨s.1 - 32, by omega⟩ q'
  else
  if h48 : s.1 < 64 then
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_48 ⟨s.1 - 48, by omega⟩ q'
  else
    have hs : s = ⟨64 + (s.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_64 ⟨s.1 - 64, by omega⟩ q'
private lemma dfaTrans_spec_bit_3_0 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_16 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_32 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_48 : ∀ i : Fin 16, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨48 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨48 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_64 : ∀ i : Fin 13, ∀ q' : Fin 32,
    (dfaMask (dfaTrans ⟨64 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨64 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3 (s : Fin 77) (q' : Fin 32) :
    (dfaMask (dfaTrans s ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨3, by omega⟩ q') != 0) := by
  if h0 : s.1 < 16 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h16 : s.1 < 32 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h32 : s.1 < 48 then
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_32 ⟨s.1 - 32, by omega⟩ q'
  else
  if h48 : s.1 < 64 then
    have hs : s = ⟨48 + (s.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_48 ⟨s.1 - 48, by omega⟩ q'
  else
    have hs : s = ⟨64 + (s.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_64 ⟨s.1 - 64, by omega⟩ q'

private lemma dfaTrans_spec_bit (s : Fin 77) (sym : Fin 4) (q' : Fin 32) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = ((dfaMask s &&& nfaPre sym q') != 0) := by
  fin_cases sym
  · exact dfaTrans_spec_bit_0 s q'
  · exact dfaTrans_spec_bit_1 s q'
  · exact dfaTrans_spec_bit_2 s q'
  · exact dfaTrans_spec_bit_3 s q'

private lemma and_ne_zero_iff (x y : ℕ) (hx : x < 2 ^ 32) :
    ((x &&& y) != 0) = true ↔ ∃ q : Fin 32, x.testBit q.1 = true ∧ y.testBit q.1 = true := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hall; push Not at hall
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 32
    · have := hall ⟨k, hk⟩
      by_cases hx1 : x.testBit k = true
      · have hy1 : y.testBit k = false := by cases h' : y.testBit k <;> simp_all
        simp [hx1, hy1]
      · have hx0 : x.testBit k = false := by cases h' : x.testBit k <;> simp_all
        simp [hx0]
    · have hpow : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hx0 : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hpow)
      simp [hx0]
  · rintro ⟨q, hxq, hyq⟩ h0
    have := congrArg (fun z => z.testBit q.1) h0
    rw [Nat.testBit_and, Nat.zero_testBit, hxq, hyq] at this
    exact absurd this (by decide)

private lemma dfaMask_empty_iff (s : Fin 77) :
    (∃ q : Fin 32, (dfaMask s).testBit q.1 = true) ↔ s.1 ≠ 12 := by
  rw [← dfaMask_ne_zero_iff s]
  have h := and_ne_zero_iff (dfaMask s) (dfaMask s) (dfaMask_lt s)
  simp only [Nat.and_self, bne_iff_ne, ne_eq, and_self] at h
  exact h.symm

private lemma dfaTrans_iff (s : Fin 77) (sym : Fin 4) (q' : Fin 32) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = true ↔
    ∃ q : Fin 32, (dfaMask s).testBit q.1 = true ∧ ∃ r2 : Fin 8, nfaStep q sym r2 = some q' := by
  rw [dfaTrans_spec_bit, and_ne_zero_iff _ _ (dfaMask_lt s)]
  constructor
  · rintro ⟨q, hq, hpre⟩
    rw [nfaPre_testBit, decide_eq_true_eq] at hpre
    exact ⟨q, hq, hpre⟩
  · rintro ⟨q, hq, hr2⟩
    refine ⟨q, hq, ?_⟩
    rw [nfaPre_testBit, decide_eq_true_eq]; exact hr2

private def runDFA : (n : ℕ) → (Fin n → Fin 4) → Fin 77
  | 0, _ => ⟨0, by omega⟩
  | n + 1, A => dfaTrans (runDFA n (fun i => A i.castSucc)) (A (Fin.last n))

private def runNFA : (n : ℕ) → (Fin n → Fin 4) → (Fin (n + 1) → Fin 8) → Option (Fin 32)
  | 0, _, M =>
    match colUpd 0 (M 0) with
    | none => none
    | some cc => if h : (M 0).1 * 4 + cc < 32 then some ⟨(M 0).1 * 4 + cc, h⟩ else none
  | n + 1, A, M =>
    match runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
    | none => none
    | some q => nfaStep q (A (Fin.last n)) (M (Fin.last (n + 1)))

private lemma runDFA_iff_runNFA (n : ℕ) (A : Fin n → Fin 4) (q : Fin 32) :
    (dfaMask (runDFA n A)).testBit q.1 = true ↔ ∃ M : Fin (n + 1) → Fin 8, runNFA n A M = some q := by
  induction n generalizing q with
  | zero =>
    unfold runDFA; rw [dfaMask_init]
    constructor
    · intro hcc
      refine ⟨fun _ => ⟨q.1 / 4, by have := q.2; omega⟩, ?_⟩
      unfold runNFA; rw [hcc]; dsimp only
      have hlt : q.1 / 4 * 4 + q.1 % 4 < 32 := by have := q.2; omega
      rw [dif_pos hlt]; congr 1; apply Fin.ext; dsimp; omega
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hcc : colUpd 0 (M 0) with
      | none => rw [hcc] at hM; simp at hM
      | some cc =>
        rw [hcc] at hM; dsimp only at hM
        split_ifs at hM with hlt
        · injection hM with hq_eq
          have hqval : q.1 = (M 0).1 * 4 + cc := (congrArg Fin.val hq_eq).symm
          have hcc4 : cc < 4 := by
            unfold colUpd at hcc; dsimp only at hcc
            by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) && (0 / 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ (M 0).1 / 4))) = true
            · rw [if_pos hcond] at hcc; injection hcc with hc; rw [← hc]; split_ifs <;> omega
            · rw [if_neg hcond] at hcc; simp at hcc
          have hdiv : (⟨q.1 / 4, by have := q.2; omega⟩ : Fin 8) = M 0 := by apply Fin.ext; dsimp; omega
          have hmod : q.1 % 4 = cc := by omega
          rw [hdiv, hmod]; exact hcc
  | succ n ih =>
    unfold runDFA; rw [dfaTrans_iff]
    constructor
    · rintro ⟨q0, hq0, rLast, hstep⟩
      obtain ⟨M0, hM0⟩ := (ih (fun i => A i.castSucc) q0).mp hq0
      refine ⟨Fin.snoc M0 rLast, ?_⟩
      unfold runNFA
      have hcast : (fun i : Fin (n + 1) => (Fin.snoc M0 rLast : Fin (n + 2) → Fin 8) i.castSucc) = M0 := by
        funext i; exact Fin.snoc_castSucc _ _ i
      rw [hcast, hM0, Fin.snoc_last]; exact hstep
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hprev : runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
      | none => rw [hprev] at hM; simp at hM
      | some q0 =>
        rw [hprev] at hM
        exact ⟨q0, (ih (fun i => A i.castSucc) q0).mpr ⟨fun i => M i.castSucc, hprev⟩, M (Fin.last (n + 1)), hM⟩

private def enc3 (r : Fin 3 → Fin 2) : Fin 8 :=
  ⟨(r 0).1 + 2 * (r 1).1 + 4 * (r 2).1, by have := (r 0).2; have := (r 1).2; have := (r 2).2; omega⟩

private def dec3 (x : Fin 8) (c : Fin 3) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩
  else if c.1 = 1 then ⟨(x.1 / 2) % 2, Nat.mod_lt _ (by omega)⟩
  else ⟨x.1 / 4, by have := x.2; omega⟩

private lemma dec3_enc3 (r : Fin 3 → Fin 2) : dec3 (enc3 r) = r := by
  funext c; fin_cases c <;> (apply Fin.ext; unfold dec3 enc3; dsimp; have := (r 0).2; have := (r 1).2; have := (r 2).2; omega)

private def encSym (r : Fin 2 → Fin 2) : Fin 4 :=
  ⟨(r 0).1 + 2 * (r 1).1, by have := (r 0).2; have := (r 1).2; omega⟩

private def decSym (x : Fin 4) (c : Fin 2) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩
  else ⟨x.1 / 2, by have := x.2; omega⟩

private lemma runNFA_sound (n : ℕ) (A : Fin n → Fin 4) (M : Fin (n + 1) → Fin 8) (q : Fin 32) (h : runNFA n A M = some q) :
    q.1 / 4 = (M (Fin.last n)).1 ∧
    ((q.1 % 4) % 2 = 0 → ∀ r : Fin (n + 1), (M r).1 % 2 = ((M r).1 / 2) % 2) ∧
    ((q.1 % 4) % 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → (M j).1 % 2 = ((M j).1 / 2) % 2) ∧ (M r).1 % 2 < ((M r).1 / 2) % 2) ∧
    ((q.1 % 4) / 2 = 0 → ∀ r : Fin (n + 1), ((M r).1 / 2) % 2 = (M r).1 / 4) ∧
    ((q.1 % 4) / 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → ((M j).1 / 2) % 2 = (M j).1 / 4) ∧ ((M r).1 / 2) % 2 < (M r).1 / 4) ∧
    (∀ r : Fin n, lex3Val (M ⟨r.1, by omega⟩) ≤ lex3Val (M ⟨r.1 + 1, by omega⟩) ∧
                  symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1) := by
  induction n generalizing q with
  | zero =>
    unfold runNFA at h
    cases hcc : colUpd 0 (M 0) with
    | none => rw [hcc] at h; simp at h
    | some cc =>
      rw [hcc] at h; dsimp only at h
      split_ifs at h with hlt
      · injection h with hq_eq
        have hqval : q.1 = (M 0).1 * 4 + cc := (congrArg Fin.val hq_eq).symm
        unfold colUpd at hcc; dsimp only at hcc
        by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) && (0 / 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ (M 0).1 / 4))) = true
        · rw [if_pos hcond] at hcc
          injection hcc with hcc_eq
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          have hcc_val : cc = (if (M 0).1 % 2 < ((M 0).1 / 2) % 2 then 1 else 0) + 2 * (if ((M 0).1 / 2) % 2 < (M 0).1 / 4 then 1 else 0) := by
            rw [← hcc_eq]; simp
          have hl0 : (Fin.last 0 : Fin 1) = 0 := rfl
          refine ⟨by rw [hl0, hqval, hcc_val]; split_ifs <;> omega,
            fun h0 r => by fin_cases r; dsimp; rw [hqval, hcc_val] at h0; split_ifs at h0 <;> omega,
            fun h1 => ⟨0, fun j hj => by fin_cases j; simp at hj, by rw [hqval, hcc_val] at h1; split_ifs at h1 <;> omega⟩,
            fun h0 r => by fin_cases r; dsimp; rw [hqval, hcc_val] at h0; split_ifs at h0 <;> omega,
            fun h1 => ⟨0, fun j hj => by fin_cases j; simp at hj, by rw [hqval, hcc_val] at h1; split_ifs at h1 <;> omega⟩,
            fun r => r.elim0⟩
        · rw [if_neg hcond] at hcc; simp at hcc
  | succ n ih =>
    unfold runNFA at h
    cases hprev : runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
    | none => rw [hprev] at h; simp at h
    | some q0 =>
      rw [hprev] at h
      obtain ⟨hr0, hc00, hc01, hc10, hc11, hrows0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hprev
      unfold nfaStep at h; dsimp only at h
      split_ifs at h with hstep_ok
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep_ok
        cases hcc : colUpd (q0.1 % 4) (M (Fin.last (n + 1))) with
        | none => rw [hcc] at h; simp at h
        | some ncc =>
          rw [hcc] at h; dsimp only at h
          split_ifs at h with hlt
          · injection h with hq_eq
            have hqval : q.1 = (M (Fin.last (n + 1))).1 * 4 + ncc := (congrArg Fin.val hq_eq).symm
            unfold colUpd at hcc; dsimp only at hcc
            by_cases hcond : (((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) && ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ (M (Fin.last (n + 1))).1 / 4))) = true
            swap
            · rw [if_neg hcond] at hcc; simp at hcc
            rw [if_pos hcond] at hcc
            injection hcc with hncc_eq
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            have hncc_val : ncc = (if (q0.1 % 4) % 2 = 1 ∨ (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 then 1 else 0) +
                2 * (if (q0.1 % 4) / 2 = 1 ∨ ((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4 then 1 else 0) := by
              rw [← hncc_eq]; simp [Bool.or_eq_true]
            refine ⟨by rw [hqval, hncc_val]; split_ifs <;> omega, ?_, ?_, ?_, ?_, ?_⟩
            · intro h0 r
              rw [hqval, hncc_val] at h0
              have hbit0 : (q0.1 % 4) % 2 = 0 ∧ ¬((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2) := by
                split_ifs at h0 with ha hb <;> omega
              refine Fin.lastCases ?_ ?_ r
              · rcases hcond.1 with hc | hle <;> omega
              · intro j; exact hc00 hbit0.1 j
            · intro h1
              by_cases h01 : (q0.1 % 4) % 2 = 1
              · obtain ⟨r, hr1, hr2⟩ := hc01 h01
                refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
                have hjlt : j.1 < n + 1 := by have := r.2; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
              · have h00 : (q0.1 % 4) % 2 = 0 := by omega
                rw [hqval, hncc_val] at h1
                have hlt_last : (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 := by
                  split_ifs at h1 with ha hb <;> omega
                refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
                have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hc00 h00 ⟨j.1, hjlt⟩
            · intro h0 r
              rw [hqval, hncc_val] at h0
              have hbit0 : (q0.1 % 4) / 2 = 0 ∧ ¬(((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4) := by
                split_ifs at h0 with ha hb <;> omega
              refine Fin.lastCases ?_ ?_ r
              · rcases hcond.2 with hc | hle <;> omega
              · intro j; exact hc10 hbit0.1 j
            · intro h1
              by_cases h01 : (q0.1 % 4) / 2 = 1
              · obtain ⟨r, hr1, hr2⟩ := hc11 h01
                refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
                have hjlt : j.1 < n + 1 := by have := r.2; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
              · have h00 : (q0.1 % 4) / 2 = 0 := by omega
                rw [hqval, hncc_val] at h1
                have hlt_last : ((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4 := by
                  split_ifs at h1 with ha hb <;> omega
                refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
                have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
                have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
                rw [← hjeq]; exact hc10 h00 ⟨j.1, hjlt⟩
            · intro r
              by_cases hr : r.1 < n
              · exact hrows0 ⟨r.1, hr⟩
              · have hreq : r.1 = n := by omega
                have e1 : (⟨r.1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by apply Fin.ext; simp [Fin.last, hreq]
                have e2 : (⟨r.1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by apply Fin.ext; simp [Fin.last, hreq]
                have eA : r = Fin.last n := Fin.ext (by simp [Fin.last, hreq])
                have hr0' : (⟨q0.1 / 4, by have := q0.2; omega⟩ : Fin 8) = M (Fin.last n).castSucc := Fin.ext hr0
                rw [e1, e2, eA, ← hr0']
                exact hstep_ok

private lemma runNFA_complete (n : ℕ) (A : Fin n → Fin 4) (M : Fin (n + 1) → Fin 8)
    (hrow : ∀ r : Fin n, lex3Val (M ⟨r.1, by omega⟩) ≤ lex3Val (M ⟨r.1 + 1, by omega⟩) ∧
                         symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1)
    (hcol0 : lexCol (n + 1) (fun r => dec3 (M r) 0) (fun r => dec3 (M r) 1))
    (hcol1 : lexCol (n + 1) (fun r => dec3 (M r) 1) (fun r => dec3 (M r) 2)) :
    ∃ q : Fin 32, runNFA n A M = some q := by
  induction n with
  | zero =>
    unfold runNFA colUpd; dsimp only
    have hc0 : (M 0).1 % 2 ≤ ((M 0).1 / 2) % 2 := by
      rcases hcol0 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec3 at this; dsimp at this; omega
      · fin_cases r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1 : ((M 0).1 / 2) % 2 ≤ (M 0).1 / 4 := by
      rcases hcol1 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec3 at this; dsimp at this; omega
      · fin_cases r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by simp [hc0, hc1])]
    dsimp only
    have hlt : (M 0).1 * 4 + ((if (0 == 1 || decide ((M 0).1 % 2 < ((M 0).1 / 2) % 2)) = true then 1 else 0) +
        2 * if (0 == 1 || decide (((M 0).1 / 2) % 2 < (M 0).1 / 4)) = true then 1 else 0) < 32 := by
      have := (M 0).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩
  | succ n ih =>
    have hcol0_prev : lexCol (n + 1) (fun r => dec3 (M r.castSucc) 0) (fun r => dec3 (M r.castSucc) 1) := by
      rcases hcol0 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    have hcol1_prev : lexCol (n + 1) (fun r => dec3 (M r.castSucc) 1) (fun r => dec3 (M r.castSucc) 2) := by
      rcases hcol1 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    obtain ⟨q0, hq0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc)
      (fun r => hrow ⟨r.1, by omega⟩) hcol0_prev hcol1_prev
    obtain ⟨hr0, hc00, _, hc10, _, _⟩ := runNFA_sound n (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hq0
    unfold runNFA; rw [hq0]; unfold nfaStep; dsimp only
    have hr0' : (⟨q0.1 / 4, by have := q0.2; omega⟩ : Fin 8) = M (Fin.last n).castSucc := Fin.ext hr0
    have hstep := hrow (Fin.last n)
    have e1 : (⟨(Fin.last n).1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := rfl
    have e2 : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
    rw [e1, e2] at hstep
    rw [hr0', if_pos (by simp [hstep.1, hstep.2])]
    unfold colUpd; dsimp only
    have hc0_ok : ((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 4) % 2 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 4) % 2 = 0 := by omega
        rcases hcol0 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec3 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc00 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1_ok : ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ (M (Fin.last (n + 1))).1 / 4)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 4) / 2 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 4) / 2 = 0 := by omega
        rcases hcol1 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec3 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc10 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec3 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by rw [hc0_ok, hc1_ok]; rfl)]; dsimp only
    have hlt : (M (Fin.last (n + 1))).1 * 4 + ((if ((q0.1 % 4) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2)) = true then 1 else 0) +
        2 * if ((q0.1 % 4) / 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 < (M (Fin.last (n + 1))).1 / 4)) = true then 1 else 0) < 32 := by
      have := (M (Fin.last (n + 1))).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩

private lemma lexRow3_iff_lex3Val (r1 r2 : Fin 8) :
    lexRow3 (dec3 r1 0) (dec3 r1 1) (dec3 r1 2) (dec3 r2 0) (dec3 r2 1) (dec3 r2 2) ↔
    lex3Val r1 ≤ lex3Val r2 := by
  revert r1 r2; unfold lexRow3 dec3 lex3Val; decide

private lemma symOf_eq_subVal (r1 r2 : Fin 8) (s : Fin 4) :
    symOf r1 r2 = s.1 ↔
    (decSym s 0 = subVal (dec3 r1 0) (dec3 r1 1) (dec3 r2 0) (dec3 r2 1) ∧
     decSym s 1 = subVal (dec3 r1 1) (dec3 r1 2) (dec3 r2 1) (dec3 r2 2)) := by
  revert r1 r2 s; decide

private lemma isValid_iff_runDFA (n : ℕ) (A : Fin n → Fin 4) :
    isValid n (fun r => decSym (A r)) ↔ (runDFA n A).1 ≠ 12 := by
  rw [← dfaMask_empty_iff]
  simp only [runDFA_iff_runNFA]
  constructor
  · rintro ⟨M, ⟨hMrow, hMcol0, hMcol1⟩, hMA⟩
    let M' : Fin (n + 1) → Fin 8 := fun r => enc3 (M r)
    have hdec : ∀ r, dec3 (M' r) = M r := fun r => dec3_enc3 (M r)
    have hrow' : ∀ r : Fin n, lex3Val (M' ⟨r.1, by omega⟩) ≤ lex3Val (M' ⟨r.1 + 1, by omega⟩) ∧
                              symOf (M' ⟨r.1, by omega⟩) (M' ⟨r.1 + 1, by omega⟩) = (A r).1 := by
      intro r
      constructor
      · rw [← lexRow3_iff_lex3Val, hdec, hdec]; exact hMrow r
      · rw [symOf_eq_subVal, hdec, hdec]
        exact ⟨hMA r 0, hMA r 1⟩
    have hcol0' : lexCol (n + 1) (fun r => dec3 (M' r) 0) (fun r => dec3 (M' r) 1) := by
      simp_rw [hdec]; exact hMcol0
    have hcol1' : lexCol (n + 1) (fun r => dec3 (M' r) 1) (fun r => dec3 (M' r) 2) := by
      simp_rw [hdec]; exact hMcol1
    obtain ⟨q, hq⟩ := runNFA_complete n A M' hrow' hcol0' hcol1'
    exact ⟨q, M', hq⟩
  · rintro ⟨q, M, hrun⟩
    obtain ⟨_, hc00, hc01, hc10, hc11, hrows⟩ := runNFA_sound n A M q hrun
    refine ⟨fun r => dec3 (M r), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro r; rw [lexRow3_iff_lex3Val]; exact (hrows r).1
    · by_cases h0 : (q.1 % 4) % 2 = 0
      · left; funext r; apply Fin.ext; unfold dec3; dsimp; exact hc00 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc01 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec3; dsimp; exact hr1 j hj, by unfold dec3; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · by_cases h0 : (q.1 % 4) / 2 = 0
      · left; funext r; apply Fin.ext; unfold dec3; dsimp; exact hc10 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc11 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec3; dsimp; exact hr1 j hj, by unfold dec3; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · intro r c
      have hsub := (symOf_eq_subVal (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) (A r)).mp (hrows r).2
      fin_cases c
      · exact hsub.1
      · exact hsub.2

private def dp : ℕ → Fin 77 → ℕ
  | 0, s => if s.1 = 0 then 1 else 0
  | n + 1, s' => ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp n s else 0

private lemma dp_succ_eq (n : ℕ) (s' : Fin 77) :
    dp (n + 1) s' = ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp n s else 0 := rfl

private def tbl_0 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 0 else 0) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 0)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 0) else (if s.1 < 12 then 0 else (if s.1 < 13 then 0 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 0 else (if s.1 < 18 then 0 else 0))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 0 else 0) else (if s.1 < 22 then 0 else 0)) else (if s.1 < 25 then (if s.1 < 24 then 0 else 0) else (if s.1 < 26 then 0 else (if s.1 < 27 then 0 else 0)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 0 else 0) else (if s.1 < 31 then 0 else (if s.1 < 32 then 0 else 0))) else (if s.1 < 35 then (if s.1 < 34 then 0 else 0) else (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 0 else 0) else (if s.1 < 45 then 0 else (if s.1 < 46 then 0 else 0)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 0) else (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0))) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else (if s.1 < 56 then 0 else 0))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 0 else 0) else (if s.1 < 60 then 0 else (if s.1 < 61 then 0 else 0))) else (if s.1 < 64 then (if s.1 < 63 then 0 else 0) else (if s.1 < 65 then 0 else (if s.1 < 66 then 0 else 0)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 0 else 0) else (if s.1 < 70 then 0 else (if s.1 < 71 then 0 else 0))) else (if s.1 < 74 then (if s.1 < 73 then 0 else 0) else (if s.1 < 75 then 0 else (if s.1 < 76 then 0 else 0)))))))
private def tbl_1 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 1) else (if s.1 < 3 then 1 else 1)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 0) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 0)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 0) else (if s.1 < 12 then 0 else (if s.1 < 13 then 0 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 0 else (if s.1 < 18 then 0 else 0))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 0 else 0) else (if s.1 < 22 then 0 else 0)) else (if s.1 < 25 then (if s.1 < 24 then 0 else 0) else (if s.1 < 26 then 0 else (if s.1 < 27 then 0 else 0)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 0 else 0) else (if s.1 < 31 then 0 else (if s.1 < 32 then 0 else 0))) else (if s.1 < 35 then (if s.1 < 34 then 0 else 0) else (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 0 else 0) else (if s.1 < 45 then 0 else (if s.1 < 46 then 0 else 0)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 0) else (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0))) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else (if s.1 < 56 then 0 else 0))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 0 else 0) else (if s.1 < 60 then 0 else (if s.1 < 61 then 0 else 0))) else (if s.1 < 64 then (if s.1 < 63 then 0 else 0) else (if s.1 < 65 then 0 else (if s.1 < 66 then 0 else 0)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 0 else 0) else (if s.1 < 70 then 0 else (if s.1 < 71 then 0 else 0))) else (if s.1 < 74 then (if s.1 < 73 then 0 else 0) else (if s.1 < 75 then 0 else (if s.1 < 76 then 0 else 0)))))))
private def tbl_2 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 1 else (if s.1 < 8 then 1 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 1 else 1) else (if s.1 < 12 then 1 else (if s.1 < 13 then 5 else 1))) else (if s.1 < 16 then (if s.1 < 15 then 1 else 1) else (if s.1 < 17 then 0 else (if s.1 < 18 then 0 else 0))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 0 else 0) else (if s.1 < 22 then 0 else 0)) else (if s.1 < 25 then (if s.1 < 24 then 0 else 0) else (if s.1 < 26 then 0 else (if s.1 < 27 then 0 else 0)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 0 else 0) else (if s.1 < 31 then 0 else (if s.1 < 32 then 0 else 0))) else (if s.1 < 35 then (if s.1 < 34 then 0 else 0) else (if s.1 < 36 then 0 else (if s.1 < 37 then 0 else 0)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 0 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 0 else 0) else (if s.1 < 45 then 0 else (if s.1 < 46 then 0 else 0)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 0) else (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0))) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else (if s.1 < 56 then 0 else 0))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 0 else 0) else (if s.1 < 60 then 0 else (if s.1 < 61 then 0 else 0))) else (if s.1 < 64 then (if s.1 < 63 then 0 else 0) else (if s.1 < 65 then 0 else (if s.1 < 66 then 0 else 0)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 0 else 0) else (if s.1 < 70 then 0 else (if s.1 < 71 then 0 else 0))) else (if s.1 < 74 then (if s.1 < 73 then 0 else 0) else (if s.1 < 75 then 0 else (if s.1 < 76 then 0 else 0)))))))
private def tbl_3 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 30 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 3 else 1) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 1 else (if s.1 < 27 then 2 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 2 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 1 else 1))) else (if s.1 < 35 then (if s.1 < 34 then 1 else 1) else (if s.1 < 36 then 1 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 1 else 1) else (if s.1 < 41 then 1 else 1)) else (if s.1 < 44 then (if s.1 < 43 then 0 else 0) else (if s.1 < 45 then 0 else (if s.1 < 46 then 0 else 0)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 0) else (if s.1 < 50 then 0 else (if s.1 < 51 then 0 else 0))) else (if s.1 < 54 then (if s.1 < 53 then 0 else 0) else (if s.1 < 55 then 0 else (if s.1 < 56 then 0 else 0))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 0 else 0) else (if s.1 < 60 then 0 else (if s.1 < 61 then 0 else 0))) else (if s.1 < 64 then (if s.1 < 63 then 0 else 0) else (if s.1 < 65 then 0 else (if s.1 < 66 then 0 else 0)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 0 else 0) else (if s.1 < 70 then 0 else (if s.1 < 71 then 0 else 0))) else (if s.1 < 74 then (if s.1 < 73 then 0 else 0) else (if s.1 < 75 then 0 else (if s.1 < 76 then 0 else 0)))))))
private def tbl_4 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 152 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 8 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 7 else (if s.1 < 27 then 4 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 12 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 1 else 4))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 2 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 1) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 1 else 1) else (if s.1 < 45 then 2 else (if s.1 < 46 then 3 else 3)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 1 else 4) else (if s.1 < 50 then 1 else (if s.1 < 51 then 1 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 1 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 7 else 1))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 2 else 1) else (if s.1 < 60 then 2 else (if s.1 < 61 then 2 else 2))) else (if s.1 < 64 then (if s.1 < 63 then 1 else 1) else (if s.1 < 65 then 1 else (if s.1 < 66 then 1 else 1)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 0) else (if s.1 < 70 then 0 else (if s.1 < 71 then 0 else 0))) else (if s.1 < 74 then (if s.1 < 73 then 0 else 0) else (if s.1 < 75 then 0 else (if s.1 < 76 then 0 else 0)))))))
private def tbl_5 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 739 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 17 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 36 else (if s.1 < 27 then 6 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 38 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 3 else 8))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 3 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 2 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 9 else 8)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 15) else (if s.1 < 50 then 1 else (if s.1 < 51 then 2 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 1 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 34 else 22))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 5 else 2) else (if s.1 < 60 then 4 else (if s.1 < 61 then 9 else 4))) else (if s.1 < 64 then (if s.1 < 63 then 5 else 2) else (if s.1 < 65 then 1 else (if s.1 < 66 then 3 else 2)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 1) else (if s.1 < 70 then 5 else (if s.1 < 71 then 1 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 1 else 1) else (if s.1 < 75 then 2 else (if s.1 < 76 then 1 else 1)))))))
private def tbl_6 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 3413 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 31 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 110 else (if s.1 < 27 then 8 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 92 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 10 else 13))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 4 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 3 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 19 else 17)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 37) else (if s.1 < 50 then 1 else (if s.1 < 51 then 3 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 2 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 91 else 118))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 8 else 3) else (if s.1 < 60 then 5 else (if s.1 < 61 then 21 else 6))) else (if s.1 < 64 then (if s.1 < 63 then 10 else 3) else (if s.1 < 65 then 1 else (if s.1 < 66 then 6 else 3)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 2) else (if s.1 < 70 then 10 else (if s.1 < 71 then 2 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 2 else 2) else (if s.1 < 75 then 6 else (if s.1 < 76 then 3 else 1)))))))
private def tbl_7 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 14915 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 51 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 267 else (if s.1 < 27 then 10 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 191 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 23 else 19))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 5 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 4 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 34 else 31)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 75) else (if s.1 < 50 then 1 else (if s.1 < 51 then 4 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 3 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 193 else 380))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 11 else 4) else (if s.1 < 60 then 6 else (if s.1 < 61 then 39 else 8))) else (if s.1 < 64 then (if s.1 < 63 then 16 else 4) else (if s.1 < 65 then 1 else (if s.1 < 66 then 10 else 4)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 3) else (if s.1 < 70 then 15 else (if s.1 < 71 then 3 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 3 else 3) else (if s.1 < 75 then 11 else (if s.1 < 76 then 6 else 1)))))))
private def tbl_8 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 62630 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 78 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 563 else (if s.1 < 27 then 12 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 358 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 43 else 26))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 6 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 5 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 55 else 51)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 135) else (if s.1 < 50 then 1 else (if s.1 < 51 then 5 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 4 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 363 else 958))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 14 else 5) else (if s.1 < 60 then 7 else (if s.1 < 61 then 64 else 10))) else (if s.1 < 64 then (if s.1 < 63 then 23 else 5) else (if s.1 < 65 then 1 else (if s.1 < 66 then 15 else 5)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 4) else (if s.1 < 70 then 20 else (if s.1 < 71 then 4 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 4 else 4) else (if s.1 < 75 then 17 else (if s.1 < 76 then 10 else 1)))))))
private def tbl_9 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 256761 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 113 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 1079 else (if s.1 < 27 then 14 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 623 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 71 else 34))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 7 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 6 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 83 else 78)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 224) else (if s.1 < 50 then 1 else (if s.1 < 51 then 6 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 5 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 631 else 2088))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 17 else 6) else (if s.1 < 60 then 8 else (if s.1 < 61 then 97 else 12))) else (if s.1 < 64 then (if s.1 < 63 then 31 else 6) else (if s.1 < 65 then 1 else (if s.1 < 66 then 21 else 6)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 5) else (if s.1 < 70 then 25 else (if s.1 < 71 then 5 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 5 else 5) else (if s.1 < 75 then 24 else (if s.1 < 76 then 15 else 1)))))))
private def tbl_10 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 1039119 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 157 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 1928 else (if s.1 < 27 then 16 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 1024 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 108 else 43))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 8 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 7 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 119 else 113)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 350) else (if s.1 < 50 then 1 else (if s.1 < 51 then 7 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 6 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 1035 else 4125))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 20 else 7) else (if s.1 < 60 then 9 else (if s.1 < 61 then 139 else 14))) else (if s.1 < 64 then (if s.1 < 63 then 40 else 7) else (if s.1 < 65 then 1 else (if s.1 < 66 then 28 else 7)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 6) else (if s.1 < 70 then 30 else (if s.1 < 71 then 6 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 6 else 6) else (if s.1 < 75 then 32 else (if s.1 < 76 then 21 else 1)))))))
private def tbl_11 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 4178400 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 211 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 3263 else (if s.1 < 27 then 18 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 1608 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 155 else 53))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 9 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 8 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 164 else 157)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 522) else (if s.1 < 50 then 1 else (if s.1 < 51 then 8 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 7 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 1622 else 7584))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 23 else 8) else (if s.1 < 60 then 10 else (if s.1 < 61 then 191 else 16))) else (if s.1 < 64 then (if s.1 < 63 then 50 else 8) else (if s.1 < 65 then 1 else (if s.1 < 66 then 36 else 8)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 7) else (if s.1 < 70 then 35 else (if s.1 < 71 then 7 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 7 else 7) else (if s.1 < 75 then 41 else (if s.1 < 76 then 28 else 1)))))))
private def tbl_12 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 16751436 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 276 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 5286 else (if s.1 < 27 then 20 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 2432 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 213 else 64))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 10 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 9 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 219 else 211)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 750) else (if s.1 < 50 then 1 else (if s.1 < 51 then 9 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 8 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 2449 else 13190))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 26 else 9) else (if s.1 < 60 then 11 else (if s.1 < 61 then 254 else 18))) else (if s.1 < 64 then (if s.1 < 63 then 61 else 9) else (if s.1 < 65 then 1 else (if s.1 < 66 then 45 else 9)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 8) else (if s.1 < 70 then 40 else (if s.1 < 71 then 8 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 8 else 8) else (if s.1 < 75 then 51 else (if s.1 < 76 then 36 else 1)))))))
private def tbl_13 (s : Fin 77) : ℕ :=
  (if s.1 < 38 then (if s.1 < 19 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 0 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 1)))) else (if s.1 < 14 then (if s.1 < 11 then (if s.1 < 10 then 0 else 1) else (if s.1 < 12 then 0 else (if s.1 < 13 then 67068371 else 0))) else (if s.1 < 16 then (if s.1 < 15 then 0 else 0) else (if s.1 < 17 then 1 else (if s.1 < 18 then 1 else 1))))) else (if s.1 < 28 then (if s.1 < 23 then (if s.1 < 21 then (if s.1 < 20 then 353 else 0) else (if s.1 < 22 then 1 else 1)) else (if s.1 < 25 then (if s.1 < 24 then 1 else 1) else (if s.1 < 26 then 8258 else (if s.1 < 27 then 22 else 1)))) else (if s.1 < 33 then (if s.1 < 30 then (if s.1 < 29 then 3564 else 1) else (if s.1 < 31 then 1 else (if s.1 < 32 then 283 else 76))) else (if s.1 < 35 then (if s.1 < 34 then 2 else 2) else (if s.1 < 36 then 11 else (if s.1 < 37 then 1 else 1)))))) else (if s.1 < 57 then (if s.1 < 47 then (if s.1 < 42 then (if s.1 < 40 then (if s.1 < 39 then 0 else 0) else (if s.1 < 41 then 1 else 0)) else (if s.1 < 44 then (if s.1 < 43 then 10 else 1) else (if s.1 < 45 then 3 else (if s.1 < 46 then 285 else 276)))) else (if s.1 < 52 then (if s.1 < 49 then (if s.1 < 48 then 0 else 1045) else (if s.1 < 50 then 1 else (if s.1 < 51 then 10 else 1))) else (if s.1 < 54 then (if s.1 < 53 then 9 else 1) else (if s.1 < 55 then 1 else (if s.1 < 56 then 3584 else 21938))))) else (if s.1 < 67 then (if s.1 < 62 then (if s.1 < 59 then (if s.1 < 58 then 29 else 10) else (if s.1 < 60 then 12 else (if s.1 < 61 then 329 else 20))) else (if s.1 < 64 then (if s.1 < 63 then 73 else 10) else (if s.1 < 65 then 1 else (if s.1 < 66 then 55 else 10)))) else (if s.1 < 72 then (if s.1 < 69 then (if s.1 < 68 then 1 else 9) else (if s.1 < 70 then 45 else (if s.1 < 71 then 9 else 1))) else (if s.1 < 74 then (if s.1 < 73 then 9 else 9) else (if s.1 < 75 then 62 else (if s.1 < 76 then 45 else 1)))))))

private lemma dp_eq_tbl_0 (s : Fin 77) : dp 0 s = tbl_0 s := by revert s; decide
private lemma dp_step_ok_1_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_0 s else 0) = tbl_1 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_1 (s' : Fin 77) : dp 1 s' = tbl_1 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 0 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_0 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_0]
  rw [h1]; exact dp_step_ok_1 s' 
private lemma dp_step_ok_2_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_1 s else 0) = tbl_2 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_2 (s' : Fin 77) : dp 2 s' = tbl_2 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 1 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_1]
  rw [h1]; exact dp_step_ok_2 s' 
private lemma dp_step_ok_3_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_2 s else 0) = tbl_3 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_3 (s' : Fin 77) : dp 3 s' = tbl_3 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 2 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_2]
  rw [h1]; exact dp_step_ok_3 s' 
private lemma dp_step_ok_4_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_3 s else 0) = tbl_4 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_4 (s' : Fin 77) : dp 4 s' = tbl_4 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 3 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_3]
  rw [h1]; exact dp_step_ok_4 s' 
private lemma dp_step_ok_5_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_4 s else 0) = tbl_5 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_5 (s' : Fin 77) : dp 5 s' = tbl_5 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 4 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_4]
  rw [h1]; exact dp_step_ok_5 s' 
private lemma dp_step_ok_6_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_5 s else 0) = tbl_6 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_6 (s' : Fin 77) : dp 6 s' = tbl_6 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 5 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_5]
  rw [h1]; exact dp_step_ok_6 s' 
private lemma dp_step_ok_7_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_6 s else 0) = tbl_7 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_7 (s' : Fin 77) : dp 7 s' = tbl_7 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 6 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_6]
  rw [h1]; exact dp_step_ok_7 s' 
private lemma dp_step_ok_8_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_7 s else 0) = tbl_8 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_8 (s' : Fin 77) : dp 8 s' = tbl_8 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 7 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_7]
  rw [h1]; exact dp_step_ok_8 s' 
private lemma dp_step_ok_9_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_8 s else 0) = tbl_9 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_9 (s' : Fin 77) : dp 9 s' = tbl_9 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 8 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_8]
  rw [h1]; exact dp_step_ok_9 s' 
private lemma dp_step_ok_10_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_9 s else 0) = tbl_10 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_10 (s' : Fin 77) : dp 10 s' = tbl_10 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 9 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_9]
  rw [h1]; exact dp_step_ok_10 s' 
private lemma dp_step_ok_11_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_10 s else 0) = tbl_11 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_11 (s' : Fin 77) : dp 11 s' = tbl_11 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 10 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_10]
  rw [h1]; exact dp_step_ok_11 s' 
private lemma dp_step_ok_12_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_11 s else 0) = tbl_12 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_12 (s' : Fin 77) : dp 12 s' = tbl_12 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 11 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_11]
  rw [h1]; exact dp_step_ok_12 s' 
private lemma dp_step_ok_13_0 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_16 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_32 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_48 : ∀ i : Fin 16,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨48 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨48 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_64 : ∀ i : Fin 13,
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = ⟨64 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨64 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13 (s' : Fin 77) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_12 s else 0) = tbl_13 s' := by
  if h0 : s'.1 < 16 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_0 ⟨s'.1 - 0, by omega⟩
  else
  if h16 : s'.1 < 32 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_16 ⟨s'.1 - 16, by omega⟩
  else
  if h32 : s'.1 < 48 then
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_32 ⟨s'.1 - 32, by omega⟩
  else
  if h48 : s'.1 < 64 then
    have hs : s' = ⟨48 + (s'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_48 ⟨s'.1 - 48, by omega⟩
  else
    have hs : s' = ⟨64 + (s'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_64 ⟨s'.1 - 64, by omega⟩
private lemma dp_eq_tbl_13 (s' : Fin 77) : dp 13 s' = tbl_13 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then dp 12 s else 0) =
      ∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_12]
  rw [h1]; exact dp_step_ok_13 s' 

private lemma dp_rec_tbl_ok : ∀ s : Fin 77, s.1 ≠ 12 → tbl_13 s + 28 * tbl_11 s + 70 * tbl_9 s + 28 * tbl_7 s + tbl_5 s = 8 * tbl_12 s + 56 * tbl_10 s + 56 * tbl_8 s + 8 * tbl_6 s := by decide

private lemma dp_rec_base : ∀ s : Fin 77, s.1 ≠ 12 → dp 13 s + 28 * dp 11 s + 70 * dp 9 s + 28 * dp 7 s + dp 5 s = 8 * dp 12 s + 56 * dp 10 s + 56 * dp 8 s + 8 * dp 6 s := by
  intro s hs; rw [dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9, dp_eq_tbl_10, dp_eq_tbl_11, dp_eq_tbl_12, dp_eq_tbl_13]; exact dp_rec_tbl_ok s hs

private lemma sum_lin (f0 f1 f2 f3 f4 f5 f6 f7 f8 : Fin 77 → ℕ) (s' : Fin 77) (hs' : s'.1 ≠ 12)
    (h : ∀ s : Fin 77, s.1 ≠ 12 → f8 s + 28 * f6 s + 70 * f4 s + 28 * f2 s + f0 s = 8 * f7 s + 56 * f5 s + 56 * f3 s + 8 * f1 s) :
    (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f8 s else 0) + 28 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f6 s else 0) + 70 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f4 s else 0) + 28 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f2 s else 0) + (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f0 s else 0) = 8 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f7 s else 0) + 56 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f5 s else 0) + 56 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f3 s else 0) + 8 * (∑ s : Fin 77, ∑ sym : Fin 4, if dfaTrans s sym = s' then f1 s else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro sym _
  by_cases htr : dfaTrans s sym = s'
  · simp only [htr, ↓reduceIte]
    have hs : s.1 ≠ 12 := by
      intro heq
      have h1 : s = ⟨12, by omega⟩ := Fin.ext heq
      have h2 : dfaTrans s sym = ⟨12, by omega⟩ := h1 ▸ dfaTrans_empty sym
      rw [htr] at h2; exact hs' (congrArg Fin.val h2)
    exact h s hs
  · simp [htr]

private lemma dp_rec (m : ℕ) : ∀ s : Fin 77, s.1 ≠ 12 → dp (m + 13) s + 28 * dp (m + 11) s + 70 * dp (m + 9) s + 28 * dp (m + 7) s + dp (m + 5) s = 8 * dp (m + 12) s + 56 * dp (m + 10) s + 56 * dp (m + 8) s + 8 * dp (m + 6) s := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro s' hs'; rw [dp_succ_eq (m + 5), dp_succ_eq (m + 6), dp_succ_eq (m + 7), dp_succ_eq (m + 8), dp_succ_eq (m + 9), dp_succ_eq (m + 10), dp_succ_eq (m + 11), dp_succ_eq (m + 12), dp_succ_eq (m + 13)]
    exact sum_lin (dp (m + 5)) (dp (m + 6)) (dp (m + 7)) (dp (m + 8)) (dp (m + 9)) (dp (m + 10)) (dp (m + 11)) (dp (m + 12)) (dp (m + 13)) s' hs' ih

private lemma card_runDFA (n : ℕ) : ∀ s : Fin 77, Fintype.card {A : Fin n → Fin 4 // runDFA n A = s} = dp n s := by
  induction n with
  | zero =>
    intro s; unfold dp
    by_cases hs : s.1 = 0
    · rw [if_pos hs]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨Fin.elim0, Fin.ext (by unfold runDFA; dsimp; omega)⟩, ?_⟩
      rintro ⟨A, _⟩; apply Subtype.ext; funext i; exact i.elim0
    · rw [if_neg hs, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, h⟩ => hs (by unfold runDFA at h; exact (congrArg Fin.val h).symm)⟩
  | succ n ih =>
    intro s'; rw [dp_succ_eq]
    let φ : (Σ s : Fin 77, Σ sym : Fin 4, {A : Fin n → Fin 4 // runDFA n A = s ∧ dfaTrans s sym = s'}) →
        {A : Fin (n + 1) → Fin 4 // runDFA (n + 1) A = s'} :=
      fun ⟨s, sym, ⟨A, hA, htr⟩⟩ =>
        ⟨Fin.snoc A sym, by
          unfold runDFA
          have hc : (fun i : Fin n => (Fin.snoc A sym : Fin (n + 1) → Fin 4) i.castSucc) = A := by
            funext i; exact Fin.snoc_castSucc _ _ i
          rw [hc, hA, Fin.snoc_last]; exact htr⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨sa, syma, ⟨Aa, hAa, _⟩⟩ ⟨sb, symb, ⟨Ab, hAb, _⟩⟩ heq
        have hfun : (Fin.snoc Aa syma : Fin (n + 1) → Fin 4) = Fin.snoc Ab symb := congrArg Subtype.val heq
        have hAeq : Aa = Ab := by funext i; simpa using congrFun hfun i.castSucc
        have hsymeq : syma = symb := by simpa using congrFun hfun (Fin.last n)
        subst hAeq; subst hsymeq
        have hseq : sa = sb := hAa.symm.trans hAb
        subst hseq; rfl
      · rintro ⟨A, hA⟩
        let A0 : Fin n → Fin 4 := fun i => A i.castSucc
        let s := runDFA n A0
        let sym := A (Fin.last n)
        refine ⟨⟨s, sym, ⟨A0, rfl, hA⟩⟩, ?_⟩
        apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
        · dsimp [φ, sym]; rw [Fin.snoc_last]
        · intro j; dsimp [φ, A0]; rw [Fin.snoc_castSucc]
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro s _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro sym _
    by_cases htr : dfaTrans s sym = s'
    · rw [if_pos htr, ← ih s]
      refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, htr⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
    · rw [if_neg htr, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨_, _, h⟩ => htr h⟩

private lemma a_eq_sum_dp (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ s : Fin 77, if s.1 ≠ 12 then dp n s else 0 := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ s : Fin 77, {A : Fin n → Fin 4 // runDFA n A = s ∧ s.1 ≠ 12}) →
      {A : Fin n → Fin 2 → Fin 2 // isValid n A} :=
    fun ⟨s, ⟨A, hA, hs⟩⟩ =>
      ⟨fun r => decSym (A r), (isValid_iff_runDFA n A).mpr (hA.symm ▸ hs)⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨sa, ⟨Aa, hAa, _⟩⟩ ⟨sb, ⟨Ab, hAb, _⟩⟩ heq
      have hfun := congrArg Subtype.val heq
      have hAeq : Aa = Ab := by
        funext r
        have h := congrFun hfun r
        have h0 : (decSym (Aa r) 0) = decSym (Ab r) 0 := congrFun h 0
        have h1 : (decSym (Aa r) 1) = decSym (Ab r) 1 := congrFun h 1
        unfold decSym at h0 h1; simp only [Fin.ext_iff] at h0 h1; dsimp at h0 h1
        have ha := (Aa r).2; have hb := (Ab r).2
        apply Fin.ext; omega
      subst hAeq
      have hseq : sa = sb := hAa.symm.trans hAb
      subst hseq; rfl
    · rintro ⟨A, hA⟩
      let A' : Fin n → Fin 4 := fun r => encSym (A r)
      have hdecA : (fun r => decSym (A' r)) = A := by
        funext r c
        fin_cases c <;> (apply Fin.ext; unfold A' encSym decSym; dsimp; have := (A r 0).2; have := (A r 1).2; omega)
      have hs : (runDFA n A').1 ≠ 12 := (isValid_iff_runDFA n A').mp (hdecA.symm ▸ hA)
      refine ⟨⟨runDFA n A', ⟨A', rfl, hs⟩⟩, ?_⟩
      apply Subtype.ext; exact hdecA
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 12
  · rw [if_pos hs, ← card_runDFA n s]
    refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, hs⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  · rw [if_neg hs, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => hs h⟩

private lemma a_rec_m (m : ℕ) : a (m + 13) + 28 * a (m + 11) + 70 * a (m + 9) + 28 * a (m + 7) + a (m + 5) = 8 * a (m + 12) + 56 * a (m + 10) + 56 * a (m + 8) + 8 * a (m + 6) := by
  rw [a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 8) (by omega), a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 10) (by omega), a_eq_sum_dp (m + 11) (by omega), a_eq_sum_dp (m + 12) (by omega), a_eq_sum_dp (m + 13) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 12
  · simp only [if_pos hs]; exact dp_rec m s hs
  · simp only [if_neg hs, mul_zero, add_zero]

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_sum_ok_1 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_1 s else 0) = 4 := by decide
private lemma a_val_1 : a 1 = 4 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 1 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_1]
  rw [h]; exact a_sum_ok_1
private lemma a_sum_ok_2 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_2 s else 0) = 11 := by decide
private lemma a_val_2 : a 2 = 11 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 2 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_2]
  rw [h]; exact a_sum_ok_2
private lemma a_sum_ok_3 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_3 s else 0) = 34 := by decide
private lemma a_val_3 : a 3 = 34 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 3 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_3]
  rw [h]; exact a_sum_ok_3
private lemma a_sum_ok_4 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_4 s else 0) = 104 := by decide
private lemma a_val_4 : a 4 = 104 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 4 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_4]
  rw [h]; exact a_sum_ok_4
private lemma a_sum_ok_5 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_5 s else 0) = 285 := by decide
private lemma a_val_5 : a 5 = 285 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 5 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_5]
  rw [h]; exact a_sum_ok_5
private lemma a_sum_ok_6 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_6 s else 0) = 683 := by decide
private lemma a_val_6 : a 6 = 683 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 6 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_6]
  rw [h]; exact a_sum_ok_6
private lemma a_sum_ok_7 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_7 s else 0) = 1469 := by decide
private lemma a_val_7 : a 7 = 1469 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 7 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_7]
  rw [h]; exact a_sum_ok_7
private lemma a_sum_ok_8 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_8 s else 0) = 2906 := by decide
private lemma a_val_8 : a 8 = 2906 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 8 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_8]
  rw [h]; exact a_sum_ok_8
private lemma a_sum_ok_9 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_9 s else 0) = 5383 := by decide
private lemma a_val_9 : a 9 = 5383 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 9 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_9]
  rw [h]; exact a_sum_ok_9
private lemma a_sum_ok_10 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_10 s else 0) = 9457 := by decide
private lemma a_val_10 : a 10 = 9457 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 10 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_10]
  rw [h]; exact a_sum_ok_10
private lemma a_sum_ok_11 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_11 s else 0) = 15904 := by decide
private lemma a_val_11 : a 11 = 15904 := by
  rw [a_eq_sum_dp 11 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 11 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_11]
  rw [h]; exact a_sum_ok_11
private lemma a_sum_ok_12 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_12 s else 0) = 25780 := by decide
private lemma a_val_12 : a 12 = 25780 := by
  rw [a_eq_sum_dp 12 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 12 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_12]
  rw [h]; exact a_sum_ok_12
private lemma a_sum_ok_13 : (∑ s : Fin 77, if s.1 ≠ 12 then tbl_13 s else 0) = 40493 := by decide
private lemma a_val_13 : a 13 = 40493 := by
  rw [a_eq_sum_dp 13 (by omega)]
  have h : (∑ s : Fin 77, if s.1 ≠ 12 then dp 13 s else 0) =
      ∑ s : Fin 77, if s.1 ≠ 12 then tbl_13 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_13]
  rw [h]; exact a_sum_ok_13

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a227329.main := by
  have hrec : ∀ n : ℕ, 10 < n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
    intro n hn
    by_cases hn11 : n = 11
    · subst hn11; simp [a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11]
    by_cases hn12 : n = 12
    · subst hn12; simp [a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12]
    · have h := a_rec_m (n - 13)
      simp only [show n - 13 + 13 = n by omega, show n - 13 + 12 = n - 1 by omega, show n - 13 + 11 = n - 2 by omega, show n - 13 + 10 = n - 3 by omega, show n - 13 + 9 = n - 4 by omega, show n - 13 + 8 = n - 5 by omega, show n - 13 + 7 = n - 6 by omega, show n - 13 + 6 = n - 7 by omega, show n - 13 + 5 = n - 8 by omega] at h
      omega
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 8 = 1 - PowerSeries.C 8 * PowerSeries.X ^ 1 + PowerSeries.C 28 * PowerSeries.X ^ 2 - PowerSeries.C 56 * PowerSeries.X ^ 3 + PowerSeries.C 70 * PowerSeries.X ^ 4 - PowerSeries.C 56 * PowerSeries.X ^ 5 + PowerSeries.C 28 * PowerSeries.X ^ 6 - PowerSeries.C 8 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (4 - 21 * PowerSeries.X + 58 * PowerSeries.X ^ 2 - 84 * PowerSeries.X ^ 3 + 69 * PowerSeries.X ^ 4 - 43 * PowerSeries.X ^ 5 + 37 * PowerSeries.X ^ 6 - 30 * PowerSeries.X ^ 7 + 13 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 9) = PowerSeries.C 4 * PowerSeries.X ^ 1 - PowerSeries.C 21 * PowerSeries.X ^ 2 + PowerSeries.C 58 * PowerSeries.X ^ 3 - PowerSeries.C 84 * PowerSeries.X ^ 4 + PowerSeries.C 69 * PowerSeries.X ^ 5 - PowerSeries.C 43 * PowerSeries.X ^ 6 + PowerSeries.C 37 * PowerSeries.X ^ 7 - PowerSeries.C 30 * PowerSeries.X ^ 8 + PowerSeries.C 13 * PowerSeries.X ^ 9 - PowerSeries.C 2 * PowerSeries.X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; norm_num
  · simp [a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]; norm_num
  · simp [a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 11 by omega, show 2 ≤ m + 11 by omega, show 3 ≤ m + 11 by omega, show 4 ≤ m + 11 by omega, show 5 ≤ m + 11 by omega, show 6 ≤ m + 11 by omega, show 7 ≤ m + 11 by omega, show 8 ≤ m + 11 by omega, ↓reduceIte,
      show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show ¬(m + 11 = 1) by omega, show ¬(m + 11 = 2) by omega, show ¬(m + 11 = 3) by omega, show ¬(m + 11 = 4) by omega, show ¬(m + 11 = 5) by omega, show ¬(m + 11 = 6) by omega, show ¬(m + 11 = 7) by omega, show ¬(m + 11 = 8) by omega, show ¬(m + 11 = 9) by omega, show ¬(m + 11 = 10) by omega]
    have hr := hrec (m + 11) (by omega)
    simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega] at hr
    have hrq : (a (m + 11) : ℚ) = 8 * (a (m + 10) : ℚ) - 28 * (a (m + 9) : ℚ) + 56 * (a (m + 8) : ℚ) - 70 * (a (m + 7) : ℚ) + 56 * (a (m + 6) : ℚ) - 28 * (a (m + 5) : ℚ) + 8 * (a (m + 4) : ℚ) - (a (m + 3) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a227329

theorem OMA.solution : type_of% @OMA.S_oeis_a227329.main :=
  OMA.P_oeis_a227329.solution
