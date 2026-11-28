import OMAStatements.S_oeis_a227086

namespace OMA.P_oeis_a227086

open OMA.S_oeis_a227086

private def lex4Val (r : Fin 16) : ℕ :=
  8 * (r.1 % 2) + 4 * ((r.1 / 2) % 2) + 2 * ((r.1 / 4) % 2) + (r.1 / 8)

private def colUpd (cc : ℕ) (r : Fin 16) : Option ℕ :=
  let b0 := r.1 % 2
  let b1 := (r.1 / 2) % 2
  let b2 := (r.1 / 4) % 2
  let b3 := r.1 / 8
  let c0 := cc % 2
  let c1 := (cc / 2) % 2
  let c2 := cc / 4
  if (c0 == 1 || b0 ≤ b1) && (c1 == 1 || b1 ≤ b2) && (c2 == 1 || b2 ≤ b3) then
    let nc0 := if c0 == 1 || b0 < b1 then 1 else 0
    let nc1 := if c1 == 1 || b1 < b2 then 1 else 0
    let nc2 := if c2 == 1 || b2 < b3 then 1 else 0
    some (nc0 + 2 * nc1 + 4 * nc2)
  else none

private def symOf (r1 r2 : Fin 16) : ℕ :=
  let a0 := r1.1 % 2; let a1 := (r1.1 / 2) % 2; let a2 := (r1.1 / 4) % 2; let a3 := r1.1 / 8
  let b0 := r2.1 % 2; let b1 := (r2.1 / 2) % 2; let b2 := (r2.1 / 4) % 2; let b3 := r2.1 / 8
  let s0 := if 2 * a0 + a1 < 2 * b0 + b1 && 2 * a0 + b0 < 2 * a1 + b1 then 1 else 0
  let s1 := if 2 * a1 + a2 < 2 * b1 + b2 && 2 * a1 + b1 < 2 * a2 + b2 then 1 else 0
  let s2 := if 2 * a2 + a3 < 2 * b2 + b3 && 2 * a2 + b2 < 2 * a3 + b3 then 1 else 0
  s0 + 2 * s1 + 4 * s2

private def nfaStep (q : Fin 128) (sym : Fin 8) (r2 : Fin 16) : Option (Fin 128) :=
  let r1 : Fin 16 := ⟨q.1 / 8, by have := q.2; omega⟩
  let cc := q.1 % 8
  if lex4Val r1 ≤ lex4Val r2 && symOf r1 r2 == sym.1 then
    match colUpd cc r2 with
    | none => none
    | some ncc =>
      if h : r2.1 * 8 + ncc < 128 then some ⟨r2.1 * 8 + ncc, h⟩ else none
  else none

private lemma nfaStep_r2_eq (q : Fin 128) (sym : Fin 8) (r2 : Fin 16) (q' : Fin 128)
    (h : nfaStep q sym r2 = some q') : r2 = ⟨q'.1 / 8, by have := q'.2; omega⟩ := by
  unfold nfaStep at h; dsimp only at h
  split_ifs at h with h1
  cases hcc : colUpd (q.1 % 8) r2 with
  | none => rw [hcc] at h; simp at h
  | some ncc =>
    rw [hcc] at h; dsimp only at h
    split_ifs at h with hlt
    injection h with hq_eq
    have hqval : q'.1 = r2.1 * 8 + ncc := (congrArg Fin.val hq_eq).symm
    have hncc8 : ncc < 8 := by
      unfold colUpd at hcc; dsimp only at hcc
      by_cases hc : ((q.1 % 8 % 2 == 1 || decide (r2.1 % 2 ≤ r2.1 / 2 % 2)) &&
          (q.1 % 8 / 2 % 2 == 1 || decide (r2.1 / 2 % 2 ≤ r2.1 / 4 % 2)) &&
          (q.1 % 8 / 4 == 1 || decide (r2.1 / 4 % 2 ≤ r2.1 / 8))) = true
      · rw [if_pos hc] at hcc; injection hcc with h'; rw [← h']; split_ifs <;> omega
      · rw [if_neg hc] at hcc; simp at hcc
    apply Fin.ext; dsimp; omega

private def nfaPre (sym : Fin 8) (q : Fin 128) : ℕ :=
  match sym.1 with
  | 0 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 1 else 2) else (if q.1 < 3 then 4 else 8)) else (if q.1 < 6 then (if q.1 < 5 then 16 else 32) else (if q.1 < 7 then 64 else 128))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 158456325065422163343096939010) else (if q.1 < 11 then 0 else 633825300261688653372387756040)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 2535301201046754613489551024160) else (if q.1 < 15 then 0 else 10141204804187018453958204096640)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 786432)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 12582912))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 18963252907773486171140 else 37926505815546972342280)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 303412046524375778738240 else 606824093048751557476480))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 343597383680 else 687194767360))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 12676506002282294191576087265280)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 13510798885257216) else (if q.1 < 55 then 0 else 54043195541028864))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 1152921504875286544 else 2305843009750573088) else (if q.1 < 63 then 4611686019501146176 else 9223372039002292352)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 313594649253062377472 else 627189298506124754944) else (if q.1 < 71 then 1254378597012249509888 else 2508757194024499019776))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 2693757686672637194400585220096) else (if q.1 < 79 then 0 else 10775030746690548777602340880384)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 246620867201384351640059904))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 21045303043150896821409153024 else 42090606086301793642818306048))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 396140812571321687989194588160 else 792281625142643375978389176320)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 6338253001141147007827113410560 else 12676506002282294015654226821120))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 203616377661659347626446018314240)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 3257862042586549562023136293027840)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 15576890575604482886435913917988864) else (if q.1 < 115 then 0 else 62307562302417931545743655671955456)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 249230249209671726182974622687821824) else (if q.1 < 119 then 0 else 996920996838686904731898490751287296))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 1329227995784915872975864654335049985 else 2658455991569831745951729308670099970) else (if q.1 < 123 then 5316911983139663491903458617340199940 else 10633823966279326983806917234680399880)) else (if q.1 < 126 then (if q.1 < 125 then 21267647932558653967613834469360799760 else 42535295865117307935227668938721599520) else (if q.1 < 127 then 85070591730234615870455337877443199040 else 170141183460469231740910675754886398080)))))))
  | 1 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 10384593719487506896853200961404928) else (if q.1 < 11 then 0 else 41538374877950027587412803845619712)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 166153499511800110349651215382478848) else (if q.1 < 15 then 0 else 664613998047200441398604861529915392)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 221360928884514619404)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 3541774862152233910464))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 20769187438975013793706401922809856 else 41538374877950027587412803845619712)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 332306999023600220699302430764957696 else 664613998047200441398604861529915392))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 0 else 0))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 830767497365572420609915408959406080)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 48) else (if q.1 < 55 then 0 else 192))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 83076749736557242060991540895940608 else 166153499473114484121983081791881216) else (if q.1 < 63 then 332306998946228968243966163583762432 else 664613997892457936487932327167524864)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 176538093231287617246504416341655552) else (if q.1 < 79 then 0 else 706152372925150468986017665366622208)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 3763135791036748529664))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 353076186462575234493008832683311104 else 706152372925150468986017665366622208))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 0 else 0)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 0 else 0))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 51922968585348276288119713059962880)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 830767497365572420609915408959406080)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 3) else (if q.1 < 115 then 0 else 12)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 48) else (if q.1 < 119 then 0 else 192))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 5192296858534827628811971305996288 else 10384593717069655257623942611992576) else (if q.1 < 123 then 20769187434139310515247885223985152 else 41538374868278621030495770447970304)) else (if q.1 < 126 then (if q.1 < 125 then 83076749736557242060991540895940608 else 166153499473114484121983081791881216) else (if q.1 < 127 then 332306998946228968243966163583762432 else 664613997892457936487932327167524864)))))))
  | 2 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 81446551064663739050578407325696 else 162893102129327478101156814651392)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 1303144817034619824809254517211136 else 2606289634069239649618509034422272))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 80 else 160))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 41120)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 325786204258654956202313629302784 else 651572408517309912404627258605568) else (if q.1 < 63 then 1303144817034619824809254517211136 else 2606289634069239649618509034422272)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 0) else (if q.1 < 79 then 0 else 0)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 0))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 1384591368099283563859832924536832 else 2769182736198567127719665849073664))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 5 else 10)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 80 else 160))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 2570)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 41120)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 0) else (if q.1 < 115 then 0 else 0)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 0) else (if q.1 < 119 then 0 else 0))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 20361637766165934762644601831424 else 40723275532331869525289203662848) else (if q.1 < 123 then 81446551064663739050578407325696 else 162893102129327478101156814651392)) else (if q.1 < 126 then (if q.1 < 125 then 325786204258654956202313629302784 else 651572408517309912404627258605568) else (if q.1 < 127 then 1303144817034619824809254517211136 else 2606289634069239649618509034422272)))))))
  | 3 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 950737950171172051174067011584)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 15211807202738752818785072185344))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 0 else 0))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 0)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 3802951800684688204696268046336) else (if q.1 < 55 then 0 else 15211807202738752818785072185344))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 0 else 0) else (if q.1 < 63 then 0 else 0)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 0) else (if q.1 < 79 then 0 else 0)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 16162545152909924869959139196928))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 0 else 0))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 0 else 0)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 0 else 0))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 0)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 0)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 237684487542793012793516752896) else (if q.1 < 115 then 0 else 950737950171172051174067011584)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 3802951800684688204696268046336) else (if q.1 < 119 then 0 else 15211807202738752818785072185344))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 0 else 0) else (if q.1 < 123 then 0 else 0)) else (if q.1 < 126 then (if q.1 < 125 then 0 else 0) else (if q.1 < 127 then 0 else 0)))))))
  | 4 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 0 else 0))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 0)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 58028439341502200385896448) else (if q.1 < 55 then 0 else 232113757366008801543585792))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 4951836010153152193272741888 else 9903672020306304386545483776) else (if q.1 < 63 then 19807344040612608773090967552 else 39614688081225217546181935104)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 17 else 34) else (if q.1 < 71 then 68 else 136))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 8738) else (if q.1 < 79 then 0 else 34952)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 13369344))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 1140868164 else 2281736328))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 0 else 0)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 0 else 0))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 0)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 0)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 3626777458843887524118528) else (if q.1 < 115 then 0 else 14507109835375550096474112)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 58028439341502200385896448) else (if q.1 < 119 then 0 else 232113757366008801543585792))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 309489750634572012079546368 else 618979501269144024159092736) else (if q.1 < 123 then 1237959002538288048318185472 else 2475918005076576096636370944)) else (if q.1 < 126 then (if q.1 < 125 then 4951836010153152193272741888 else 9903672020306304386545483776) else (if q.1 < 127 then 19807344040612608773090967552 else 39614688081225217546181935104)))))))
  | 5 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 0 else 0))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 193428131138340667952988160)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 885443715538058477568) else (if q.1 < 55 then 0 else 3541774862152233910272))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 19342813113834066795298816 else 38685626227668133590597632) else (if q.1 < 63 then 77371252455336267181195264 else 154742504910672534362390528)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 2228224) else (if q.1 < 79 then 0 else 8912896)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 204))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 4456448 else 8912896))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 0 else 0)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 0 else 0))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 12089258196146291747061760)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 193428131138340667952988160)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 55340232221128654848) else (if q.1 < 115 then 0 else 221360928884514619392)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 885443715538058477568) else (if q.1 < 119 then 0 else 3541774862152233910272))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 1208925819614629174706176 else 2417851639229258349412352) else (if q.1 < 123 then 4835703278458516698824704 else 9671406556917033397649408)) else (if q.1 < 126 then (if q.1 < 125 then 19342813113834066795298816 else 38685626227668133590597632) else (if q.1 < 127 then 77371252455336267181195264 else 154742504910672534362390528)))))))
  | 6 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 1475739525896764129280 else 2951479051793528258560))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 758530116310936762449920)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 0 else 0) else (if q.1 < 63 then 0 else 0)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 0) else (if q.1 < 79 then 0 else 0)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 0))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 0 else 0))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 92233720368547758080 else 184467440737095516160)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 1475739525896764129280 else 2951479051793528258560))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 47408132269433547653120)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 758530116310936762449920)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 0) else (if q.1 < 115 then 0 else 0)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 0) else (if q.1 < 119 then 0 else 0))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 0 else 0) else (if q.1 < 123 then 0 else 0)) else (if q.1 < 126 then (if q.1 < 125 then 0 else 0) else (if q.1 < 127 then 0 else 0)))))))
  | 7 => (if q.1 < 64 then (if q.1 < 32 then (if q.1 < 16 then (if q.1 < 8 then (if q.1 < 4 then (if q.1 < 2 then (if q.1 < 1 then 0 else 0) else (if q.1 < 3 then 0 else 0)) else (if q.1 < 6 then (if q.1 < 5 then 0 else 0) else (if q.1 < 7 then 0 else 0))) else (if q.1 < 12 then (if q.1 < 10 then (if q.1 < 9 then 0 else 0) else (if q.1 < 11 then 0 else 0)) else (if q.1 < 14 then (if q.1 < 13 then 0 else 0) else (if q.1 < 15 then 0 else 0)))) else (if q.1 < 24 then (if q.1 < 20 then (if q.1 < 18 then (if q.1 < 17 then 0 else 0) else (if q.1 < 19 then 0 else 0)) else (if q.1 < 22 then (if q.1 < 21 then 0 else 0) else (if q.1 < 23 then 0 else 0))) else (if q.1 < 28 then (if q.1 < 26 then (if q.1 < 25 then 0 else 0) else (if q.1 < 27 then 0 else 0)) else (if q.1 < 30 then (if q.1 < 29 then 0 else 0) else (if q.1 < 31 then 0 else 0))))) else (if q.1 < 48 then (if q.1 < 40 then (if q.1 < 36 then (if q.1 < 34 then (if q.1 < 33 then 0 else 0) else (if q.1 < 35 then 0 else 0)) else (if q.1 < 38 then (if q.1 < 37 then 0 else 0) else (if q.1 < 39 then 0 else 0))) else (if q.1 < 44 then (if q.1 < 42 then (if q.1 < 41 then 0 else 0) else (if q.1 < 43 then 0 else 0)) else (if q.1 < 46 then (if q.1 < 45 then 0 else 0) else (if q.1 < 47 then 0 else 0)))) else (if q.1 < 56 then (if q.1 < 52 then (if q.1 < 50 then (if q.1 < 49 then 0 else 0) else (if q.1 < 51 then 0 else 0)) else (if q.1 < 54 then (if q.1 < 53 then 0 else 0) else (if q.1 < 55 then 0 else 0))) else (if q.1 < 60 then (if q.1 < 58 then (if q.1 < 57 then 0 else 0) else (if q.1 < 59 then 0 else 0)) else (if q.1 < 62 then (if q.1 < 61 then 0 else 0) else (if q.1 < 63 then 0 else 0)))))) else (if q.1 < 96 then (if q.1 < 80 then (if q.1 < 72 then (if q.1 < 68 then (if q.1 < 66 then (if q.1 < 65 then 0 else 0) else (if q.1 < 67 then 0 else 0)) else (if q.1 < 70 then (if q.1 < 69 then 0 else 0) else (if q.1 < 71 then 0 else 0))) else (if q.1 < 76 then (if q.1 < 74 then (if q.1 < 73 then 0 else 0) else (if q.1 < 75 then 0 else 0)) else (if q.1 < 78 then (if q.1 < 77 then 0 else 0) else (if q.1 < 79 then 0 else 0)))) else (if q.1 < 88 then (if q.1 < 84 then (if q.1 < 82 then (if q.1 < 81 then 0 else 0) else (if q.1 < 83 then 0 else 0)) else (if q.1 < 86 then (if q.1 < 85 then 0 else 0) else (if q.1 < 87 then 0 else 0))) else (if q.1 < 92 then (if q.1 < 90 then (if q.1 < 89 then 0 else 0) else (if q.1 < 91 then 0 else 0)) else (if q.1 < 94 then (if q.1 < 93 then 0 else 0) else (if q.1 < 95 then 0 else 0))))) else (if q.1 < 112 then (if q.1 < 104 then (if q.1 < 100 then (if q.1 < 98 then (if q.1 < 97 then 0 else 0) else (if q.1 < 99 then 0 else 0)) else (if q.1 < 102 then (if q.1 < 101 then 0 else 0) else (if q.1 < 103 then 0 else 0))) else (if q.1 < 108 then (if q.1 < 106 then (if q.1 < 105 then 0 else 0) else (if q.1 < 107 then 0 else 0)) else (if q.1 < 110 then (if q.1 < 109 then 0 else 0) else (if q.1 < 111 then 0 else 0)))) else (if q.1 < 120 then (if q.1 < 116 then (if q.1 < 114 then (if q.1 < 113 then 0 else 0) else (if q.1 < 115 then 0 else 0)) else (if q.1 < 118 then (if q.1 < 117 then 0 else 0) else (if q.1 < 119 then 0 else 0))) else (if q.1 < 124 then (if q.1 < 122 then (if q.1 < 121 then 0 else 0) else (if q.1 < 123 then 0 else 0)) else (if q.1 < 126 then (if q.1 < 125 then 0 else 0) else (if q.1 < 127 then 0 else 0)))))))
  | _ => 0

private lemma nfaPre_tb_0_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨0, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_0 (q' q : Fin 128) :
    (nfaPre ⟨0, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨0, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_0_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_1_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨1, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_1 (q' q : Fin 128) :
    (nfaPre ⟨1, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨1, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_1_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_2_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨2, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_2 (q' q : Fin 128) :
    (nfaPre ⟨2, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨2, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_2_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_3_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨3, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_3 (q' q : Fin 128) :
    (nfaPre ⟨3, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨3, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_3_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_4_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨4, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_4 (q' q : Fin 128) :
    (nfaPre ⟨4, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨4, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_4_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_5_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨5, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_5 (q' q : Fin 128) :
    (nfaPre ⟨5, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨5, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_5_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_6_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨6, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_6 (q' q : Fin 128) :
    (nfaPre ⟨6, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨6, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_6_112 ⟨q'.1 - 112, by omega⟩ q
private lemma nfaPre_tb_7_0 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨0 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(0 + i.1) / 8, by omega⟩ = some ⟨0 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_16 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨16 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(16 + i.1) / 8, by omega⟩ = some ⟨16 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_32 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨32 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(32 + i.1) / 8, by omega⟩ = some ⟨32 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_48 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨48 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(48 + i.1) / 8, by omega⟩ = some ⟨48 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_64 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨64 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(64 + i.1) / 8, by omega⟩ = some ⟨64 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_80 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨80 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(80 + i.1) / 8, by omega⟩ = some ⟨80 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_96 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨96 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(96 + i.1) / 8, by omega⟩ = some ⟨96 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7_112 : ∀ i : Fin 16, ∀ q : Fin 128,
    (nfaPre ⟨7, by omega⟩ ⟨112 + i.1, by omega⟩).testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨(112 + i.1) / 8, by omega⟩ = some ⟨112 + i.1, by omega⟩) := by decide
private lemma nfaPre_tb_7 (q' q : Fin 128) :
    (nfaPre ⟨7, by omega⟩ q').testBit q.1 =
    decide (nfaStep q ⟨7, by omega⟩ ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
  if h0 : q'.1 < 16 then
    have hs : q' = ⟨0 + (q'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_0 ⟨q'.1 - 0, by omega⟩ q
  else
  if h16 : q'.1 < 32 then
    have hs : q' = ⟨16 + (q'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_16 ⟨q'.1 - 16, by omega⟩ q
  else
  if h32 : q'.1 < 48 then
    have hs : q' = ⟨32 + (q'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_32 ⟨q'.1 - 32, by omega⟩ q
  else
  if h48 : q'.1 < 64 then
    have hs : q' = ⟨48 + (q'.1 - 48), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_48 ⟨q'.1 - 48, by omega⟩ q
  else
  if h64 : q'.1 < 80 then
    have hs : q' = ⟨64 + (q'.1 - 64), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_64 ⟨q'.1 - 64, by omega⟩ q
  else
  if h80 : q'.1 < 96 then
    have hs : q' = ⟨80 + (q'.1 - 80), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_80 ⟨q'.1 - 80, by omega⟩ q
  else
  if h96 : q'.1 < 112 then
    have hs : q' = ⟨96 + (q'.1 - 96), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_96 ⟨q'.1 - 96, by omega⟩ q
  else
    have hs : q' = ⟨112 + (q'.1 - 112), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact nfaPre_tb_7_112 ⟨q'.1 - 112, by omega⟩ q

private lemma nfaPre_testBit_iff (sym : Fin 8) (q' q : Fin 128) :
    (nfaPre sym q').testBit q.1 = true ↔ ∃ r2 : Fin 16, nfaStep q sym r2 = some q' := by
  have hdir : (nfaPre sym q').testBit q.1 =
      decide (nfaStep q sym ⟨q'.1 / 8, by have := q'.2; omega⟩ = some q') := by
    fin_cases sym
    · exact nfaPre_tb_0 q' q
    · exact nfaPre_tb_1 q' q
    · exact nfaPre_tb_2 q' q
    · exact nfaPre_tb_3 q' q
    · exact nfaPre_tb_4 q' q
    · exact nfaPre_tb_5 q' q
    · exact nfaPre_tb_6 q' q
    · exact nfaPre_tb_7 q' q
  rw [hdir, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨⟨q'.1 / 8, by have := q'.2; omega⟩, h⟩
  · rintro ⟨r2, hr2⟩
    have := nfaStep_r2_eq q sym r2 q' hr2
    rwa [← this]

private def dfaMask (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1339612906414635880366123606467411969 else 2669002844563881730155518519876256256) else (if s.1 < 3 then 5316912319859354177238663013750276096 else 41538375023021125938916504996675584)) else (if s.1 < 6 then (if s.1 < 5 then 21267647932558654262761739648445186048 else 166153499473114484121983081789784064) else (if s.1 < 7 then 5070602400912917606261690728448 else (if s.1 < 8 then 0 else 2658618250846812074898457527217816064)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 10633986265170237453726016857159237632 else 42535295865117459050955120766831558656) else (if s.1 < 12 then 2596148429267413814405985652965376 else 5316912002946704120181312639574474752)) else (if s.1 < 15 then (if s.1 < 14 then 85070591750041656499021422274755428352 else 10633986265170841916635824173894109184) else (if s.1 < 16 then 664613998047200441398604861521526784 else (if s.1 < 17 then 170143779648513184874767057849751175168 else 21267647932558653967613834469092360192))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 42537892013546726464769526752484532224 else 85070591750041656499021422275829170176) else (if s.1 < 21 then 664613998047200441398604861529915392 else 10633824005893408240362625279148949504)) else (if s.1 < 24 then (if s.1 < 23 then 170141183500083312998042844549510856704 else 42535295865117307935227668938184720384) else (if s.1 < 25 then 170141183500083312998042844551658340352 else (if s.1 < 26 then 85070591730234615870455337876369440768 else 180775169725640073657546499926632990720)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 10636582413599504867540422842812203008 else 170141183500083917460952651864098209792) else (if s.1 < 30 then 170143779648513184874767057851898691584 else (if s.1 < 31 then 664613997892457936487932327159136256 else 170143779608898499154725081738391846912))) else (if s.1 < 34 then (if s.1 < 33 then 170143779648513184874767057851898658816 else 170141183460469231740910675752738881536) else (if s.1 < 35 then 170143779648512580411857250537311305728 else (if s.1 < 36 then 180775007466362639981273301034035314688 else 170141183500083917460952651866245693440))))))

private def dfaTransVal (s : Fin 37) (sym : Fin 8) : ℕ :=
  match s.1 with
  | 0 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 0 else 1) else (if sym.1 < 3 then 2 else 3)) else (if sym.1 < 6 then (if sym.1 < 5 then 4 else 5) else (if sym.1 < 7 then 6 else 7)))
  | 1 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 1 else 8) else (if sym.1 < 3 then 9 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 10 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 2 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 2 else 7) else (if sym.1 < 3 then 12 else 3)) else (if sym.1 < 6 then (if sym.1 < 5 then 13 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 3 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 3 else 14) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 15 else 16) else (if sym.1 < 7 then 7 else 7)))
  | 4 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 4 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 17 else 5) else (if sym.1 < 7 then 6 else 7)))
  | 5 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 5 else 18) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 6 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 6 else 7) else (if sym.1 < 3 then 19 else 20)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 7 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 7 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 8 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 8 else 7) else (if sym.1 < 3 then 9 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 10 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 9 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 9 else 7) else (if sym.1 < 3 then 21 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 10 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 10 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 23 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 11 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 11 else 7) else (if sym.1 < 3 then 24 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 12 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 12 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 13 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 13 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 13 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 25 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 14 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 26 else 7) else (if sym.1 < 3 then 27 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 28 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 15 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 15 else 29) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 30 else 31) else (if sym.1 < 7 then 7 else 7)))
  | 16 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 32 else 7) else (if sym.1 < 3 then 24 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 33 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 17 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 17 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 18 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 18 else 7) else (if sym.1 < 3 then 34 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 10 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 19 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 19 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 13 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 20 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 20 else 29) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 15 else 16) else (if sym.1 < 7 then 7 else 7)))
  | 21 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 21 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 22 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 22 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 33 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 23 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 23 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 24 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 24 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 25 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 25 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 26 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 26 else 7) else (if sym.1 < 3 then 27 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 28 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 27 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 27 else 7) else (if sym.1 < 3 then 35 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 28 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 36 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 33 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 29 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 29 else 7) else (if sym.1 < 3 then 34 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 28 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 30 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 30 else 29) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 31 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 31 else 7) else (if sym.1 < 3 then 24 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 32 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 32 else 7) else (if sym.1 < 3 then 24 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 11 else 7)))
  | 33 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 33 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 7 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 34 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 34 else 7) else (if sym.1 < 3 then 24 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 35 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 35 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 7 else 7)))
  | 36 => (if sym.1 < 4 then (if sym.1 < 2 then (if sym.1 < 1 then 36 else 7) else (if sym.1 < 3 then 7 else 7)) else (if sym.1 < 6 then (if sym.1 < 5 then 22 else 7) else (if sym.1 < 7 then 11 else 7)))
  | _ => 0

private lemma dfaTransVal_lt : ∀ s : Fin 37, ∀ sym : Fin 8, dfaTransVal s sym < 37 := by decide

private def dfaTrans (s : Fin 37) (sym : Fin 8) : Fin 37 :=
  ⟨dfaTransVal s sym, dfaTransVal_lt s sym⟩

private lemma dfaTrans_empty : ∀ sym : Fin 8, dfaTrans ⟨7, by omega⟩ sym = ⟨7, by omega⟩ := by decide

private lemma dfaMask_lt : ∀ s : Fin 37, dfaMask s < 2 ^ 128 := by decide

private lemma dfaMask_ne_zero_iff : ∀ s : Fin 37, dfaMask s ≠ 0 ↔ s.1 ≠ 7 := by decide

private lemma dfaMask_init : ∀ q : Fin 128,
    (dfaMask ⟨0, by omega⟩).testBit q.1 = true ↔ colUpd 0 ⟨q.1 / 8, by have := q.2; omega⟩ = some (q.1 % 8) := by decide

private lemma dfaTrans_spec_bit_0_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨0, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_0 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨0, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨0, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_0_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_1_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨1, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_1 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨1, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨1, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_1_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_2_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨2, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_2 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨2, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨2, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_2_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_3_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨3, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_3 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨3, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨3, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_3_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_4_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨4, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_4 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨4, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨4, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_4_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_4_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_4_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_4_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_4_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_5_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨5, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_5 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨5, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨5, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_5_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_5_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_5_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_5_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_5_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_6_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨6, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_6 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨6, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨6, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_6_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_6_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_6_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_6_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_6_32 ⟨s.1 - 32, by omega⟩ q'
private lemma dfaTrans_spec_bit_7_0 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨0 + i.1, by omega⟩ ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask ⟨0 + i.1, by omega⟩ &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7_8 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨8 + i.1, by omega⟩ ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask ⟨8 + i.1, by omega⟩ &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7_16 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨16 + i.1, by omega⟩ ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask ⟨16 + i.1, by omega⟩ &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7_24 : ∀ i : Fin 8, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨24 + i.1, by omega⟩ ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask ⟨24 + i.1, by omega⟩ &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7_32 : ∀ i : Fin 5, ∀ q' : Fin 128,
    (dfaMask (dfaTrans ⟨32 + i.1, by omega⟩ ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask ⟨32 + i.1, by omega⟩ &&& nfaPre ⟨7, by omega⟩ q') != 0) := by decide
private lemma dfaTrans_spec_bit_7 (s : Fin 37) (q' : Fin 128) :
    (dfaMask (dfaTrans s ⟨7, by omega⟩)).testBit q'.1 = ((dfaMask s &&& nfaPre ⟨7, by omega⟩ q') != 0) := by
  if h0 : s.1 < 8 then
    have hs : s = ⟨0 + (s.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_7_0 ⟨s.1 - 0, by omega⟩ q'
  else
  if h8 : s.1 < 16 then
    have hs : s = ⟨8 + (s.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_7_8 ⟨s.1 - 8, by omega⟩ q'
  else
  if h16 : s.1 < 24 then
    have hs : s = ⟨16 + (s.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_7_16 ⟨s.1 - 16, by omega⟩ q'
  else
  if h24 : s.1 < 32 then
    have hs : s = ⟨24 + (s.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_7_24 ⟨s.1 - 24, by omega⟩ q'
  else
    have hs : s = ⟨32 + (s.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dfaTrans_spec_bit_7_32 ⟨s.1 - 32, by omega⟩ q'

private lemma dfaTrans_spec_bit (s : Fin 37) (sym : Fin 8) (q' : Fin 128) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = ((dfaMask s &&& nfaPre sym q') != 0) := by
  fin_cases sym
  · exact dfaTrans_spec_bit_0 s q'
  · exact dfaTrans_spec_bit_1 s q'
  · exact dfaTrans_spec_bit_2 s q'
  · exact dfaTrans_spec_bit_3 s q'
  · exact dfaTrans_spec_bit_4 s q'
  · exact dfaTrans_spec_bit_5 s q'
  · exact dfaTrans_spec_bit_6 s q'
  · exact dfaTrans_spec_bit_7 s q'

private lemma and_ne_zero_iff (x y : ℕ) (hx : x < 2 ^ 128) :
    ((x &&& y) != 0) = true ↔ ∃ q : Fin 128, x.testBit q.1 = true ∧ y.testBit q.1 = true := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro hne
    by_contra hall; push Not at hall
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 128
    · have := hall ⟨k, hk⟩
      by_cases hx1 : x.testBit k = true
      · have hy1 : y.testBit k = false := by cases h' : y.testBit k <;> simp_all
        simp [hx1, hy1]
      · have hx0 : x.testBit k = false := by cases h' : x.testBit k <;> simp_all
        simp [hx0]
    · have hpow : 2 ^ 128 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hx0 : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hpow)
      simp [hx0]
  · rintro ⟨q, hxq, hyq⟩ h0
    have := congrArg (fun z => z.testBit q.1) h0
    rw [Nat.testBit_and, Nat.zero_testBit, hxq, hyq] at this
    exact absurd this (by decide)

private lemma dfaMask_empty_iff (s : Fin 37) :
    (∃ q : Fin 128, (dfaMask s).testBit q.1 = true) ↔ s.1 ≠ 7 := by
  rw [← dfaMask_ne_zero_iff s]
  have h := and_ne_zero_iff (dfaMask s) (dfaMask s) (dfaMask_lt s)
  simp only [Nat.and_self, bne_iff_ne, ne_eq, and_self] at h
  exact h.symm

private lemma dfaTrans_iff (s : Fin 37) (sym : Fin 8) (q' : Fin 128) :
    (dfaMask (dfaTrans s sym)).testBit q'.1 = true ↔
    ∃ q : Fin 128, (dfaMask s).testBit q.1 = true ∧ ∃ r2 : Fin 16, nfaStep q sym r2 = some q' := by
  rw [dfaTrans_spec_bit, and_ne_zero_iff _ _ (dfaMask_lt s)]
  constructor
  · rintro ⟨q, hq, hpre⟩
    exact ⟨q, hq, (nfaPre_testBit_iff sym q' q).mp hpre⟩
  · rintro ⟨q, hq, hr2⟩
    exact ⟨q, hq, (nfaPre_testBit_iff sym q' q).mpr hr2⟩

private def runDFA : (n : ℕ) → (Fin n → Fin 8) → Fin 37
  | 0, _ => ⟨0, by omega⟩
  | n + 1, A => dfaTrans (runDFA n (fun i => A i.castSucc)) (A (Fin.last n))

private def runNFA : (n : ℕ) → (Fin n → Fin 8) → (Fin (n + 1) → Fin 16) → Option (Fin 128)
  | 0, _, M =>
    match colUpd 0 (M 0) with
    | none => none
    | some cc => if h : (M 0).1 * 8 + cc < 128 then some ⟨(M 0).1 * 8 + cc, h⟩ else none
  | n + 1, A, M =>
    match runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
    | none => none
    | some q => nfaStep q (A (Fin.last n)) (M (Fin.last (n + 1)))

private lemma runDFA_iff_runNFA (n : ℕ) (A : Fin n → Fin 8) (q : Fin 128) :
    (dfaMask (runDFA n A)).testBit q.1 = true ↔ ∃ M : Fin (n + 1) → Fin 16, runNFA n A M = some q := by
  induction n generalizing q with
  | zero =>
    unfold runDFA; rw [dfaMask_init]
    constructor
    · intro hcc
      refine ⟨fun _ => ⟨q.1 / 8, by have := q.2; omega⟩, ?_⟩
      unfold runNFA; rw [hcc]; dsimp only
      have hlt : q.1 / 8 * 8 + q.1 % 8 < 128 := by have := q.2; omega
      rw [dif_pos hlt]; congr 1; apply Fin.ext; dsimp; omega
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hcc : colUpd 0 (M 0) with
      | none => rw [hcc] at hM; simp at hM
      | some cc =>
        rw [hcc] at hM; dsimp only at hM
        split_ifs at hM with hlt
        injection hM with hq_eq
        have hqval : q.1 = (M 0).1 * 8 + cc := (congrArg Fin.val hq_eq).symm
        have hcc8 : cc < 8 := by
          unfold colUpd at hcc; dsimp only at hcc
          by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) &&
              (0 / 2 % 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ ((M 0).1 / 4) % 2)) &&
              (0 / 4 == 1 || decide (((M 0).1 / 4) % 2 ≤ (M 0).1 / 8))) = true
          · rw [if_pos hcond] at hcc; injection hcc with hc; rw [← hc]; split_ifs <;> omega
          · rw [if_neg hcond] at hcc; simp at hcc
        have hdiv : (⟨q.1 / 8, by have := q.2; omega⟩ : Fin 16) = M 0 := by apply Fin.ext; dsimp; omega
        have hmod : q.1 % 8 = cc := by omega
        rw [hdiv, hmod]; exact hcc
  | succ n ih =>
    unfold runDFA; rw [dfaTrans_iff]
    constructor
    · rintro ⟨q0, hq0, rLast, hstep⟩
      obtain ⟨M0, hM0⟩ := (ih (fun i => A i.castSucc) q0).mp hq0
      refine ⟨Fin.snoc M0 rLast, ?_⟩
      unfold runNFA
      have hcast : (fun i : Fin (n + 1) => (Fin.snoc M0 rLast : Fin (n + 2) → Fin 16) i.castSucc) = M0 := by
        funext i; exact Fin.snoc_castSucc _ _ i
      rw [hcast, hM0, Fin.snoc_last]; exact hstep
    · rintro ⟨M, hM⟩
      unfold runNFA at hM
      cases hprev : runNFA n (fun i => A i.castSucc) (fun i => M i.castSucc) with
      | none => rw [hprev] at hM; simp at hM
      | some q0 =>
        rw [hprev] at hM
        exact ⟨q0, (ih (fun i => A i.castSucc) q0).mpr ⟨fun i => M i.castSucc, hprev⟩, M (Fin.last (n + 1)), hM⟩

private def enc4 (r : Fin 4 → Fin 2) : Fin 16 :=
  ⟨(r 0).1 + 2 * (r 1).1 + 4 * (r 2).1 + 8 * (r 3).1,
   by have := (r 0).2; have := (r 1).2; have := (r 2).2; have := (r 3).2; omega⟩

private def dec4 (x : Fin 16) (c : Fin 4) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩
  else if c.1 = 1 then ⟨(x.1 / 2) % 2, Nat.mod_lt _ (by omega)⟩
  else if c.1 = 2 then ⟨(x.1 / 4) % 2, Nat.mod_lt _ (by omega)⟩
  else ⟨x.1 / 8, by have := x.2; omega⟩

private lemma dec4_enc4 (r : Fin 4 → Fin 2) : dec4 (enc4 r) = r := by
  funext c; fin_cases c <;> (apply Fin.ext; unfold dec4 enc4; dsimp; have := (r 0).2; have := (r 1).2; have := (r 2).2; have := (r 3).2; omega)

private def encSym (r : Fin 3 → Fin 2) : Fin 8 :=
  ⟨(r 0).1 + 2 * (r 1).1 + 4 * (r 2).1, by have := (r 0).2; have := (r 1).2; have := (r 2).2; omega⟩

private def decSym (x : Fin 8) (c : Fin 3) : Fin 2 :=
  if c.1 = 0 then ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩
  else if c.1 = 1 then ⟨(x.1 / 2) % 2, Nat.mod_lt _ (by omega)⟩
  else ⟨x.1 / 4, by have := x.2; omega⟩

private lemma runNFA_sound (n : ℕ) (A : Fin n → Fin 8) (M : Fin (n + 1) → Fin 16) (q : Fin 128) (h : runNFA n A M = some q) :
    q.1 / 8 = (M (Fin.last n)).1 ∧
    ((q.1 % 8) % 2 = 0 → ∀ r : Fin (n + 1), (M r).1 % 2 = ((M r).1 / 2) % 2) ∧
    ((q.1 % 8) % 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → (M j).1 % 2 = ((M j).1 / 2) % 2) ∧ (M r).1 % 2 < ((M r).1 / 2) % 2) ∧
    (((q.1 % 8) / 2) % 2 = 0 → ∀ r : Fin (n + 1), ((M r).1 / 2) % 2 = ((M r).1 / 4) % 2) ∧
    (((q.1 % 8) / 2) % 2 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → ((M j).1 / 2) % 2 = ((M j).1 / 4) % 2) ∧ ((M r).1 / 2) % 2 < ((M r).1 / 4) % 2) ∧
    ((q.1 % 8) / 4 = 0 → ∀ r : Fin (n + 1), ((M r).1 / 4) % 2 = (M r).1 / 8) ∧
    ((q.1 % 8) / 4 = 1 → ∃ r : Fin (n + 1), (∀ j : Fin (n + 1), j.1 < r.1 → ((M j).1 / 4) % 2 = (M j).1 / 8) ∧ ((M r).1 / 4) % 2 < (M r).1 / 8) ∧
    (∀ r : Fin n, lex4Val (M ⟨r.1, by omega⟩) ≤ lex4Val (M ⟨r.1 + 1, by omega⟩) ∧
                  symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1) := by
  induction n generalizing q with
  | zero =>
    unfold runNFA at h
    cases hcc : colUpd 0 (M 0) with
    | none => rw [hcc] at h; simp at h
    | some cc =>
      rw [hcc] at h; dsimp only at h
      split_ifs at h with hlt
      injection h with hq_eq
      have hqval : q.1 = (M 0).1 * 8 + cc := (congrArg Fin.val hq_eq).symm
      unfold colUpd at hcc; dsimp only at hcc
      by_cases hcond : ((0 % 2 == 1 || decide ((M 0).1 % 2 ≤ ((M 0).1 / 2) % 2)) &&
          (0 / 2 % 2 == 1 || decide (((M 0).1 / 2) % 2 ≤ ((M 0).1 / 4) % 2)) &&
          (0 / 4 == 1 || decide (((M 0).1 / 4) % 2 ≤ (M 0).1 / 8))) = true
      · rw [if_pos hcond] at hcc
        injection hcc with hcc_eq
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        have hcc_val : cc = (if (M 0).1 % 2 < ((M 0).1 / 2) % 2 then 1 else 0) +
            2 * (if ((M 0).1 / 2) % 2 < ((M 0).1 / 4) % 2 then 1 else 0) +
            4 * (if ((M 0).1 / 4) % 2 < (M 0).1 / 8 then 1 else 0) := by
          rw [← hcc_eq]; simp
        have hl0 : (Fin.last 0 : Fin 1) = 0 := rfl
        refine ⟨by rw [hl0, hqval, hcc_val]; split_ifs <;> omega,
          fun h0 r => by fin_cases r; dsimp; rw [hqval, hcc_val] at h0; split_ifs at h0 <;> omega,
          fun h1 => ⟨0, fun j hj => by fin_cases j; simp at hj, by rw [hqval, hcc_val] at h1; split_ifs at h1 <;> omega⟩,
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
      obtain ⟨hr0, hc00, hc01, hc10, hc11, hc20, hc21, hrows0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hprev
      unfold nfaStep at h; dsimp only at h
      split_ifs at h with hstep_ok
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep_ok
      cases hcc : colUpd (q0.1 % 8) (M (Fin.last (n + 1))) with
      | none => rw [hcc] at h; simp at h
      | some ncc =>
        rw [hcc] at h; dsimp only at h
        split_ifs at h with hlt
        injection h with hq_eq
        have hqval : q.1 = (M (Fin.last (n + 1))).1 * 8 + ncc := (congrArg Fin.val hq_eq).symm
        unfold colUpd at hcc; dsimp only at hcc
        by_cases hcond : (((q0.1 % 8) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) &&
            (((q0.1 % 8) / 2) % 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ ((M (Fin.last (n + 1))).1 / 4) % 2)) &&
            ((q0.1 % 8) / 4 == 1 || decide (((M (Fin.last (n + 1))).1 / 4) % 2 ≤ (M (Fin.last (n + 1))).1 / 8))) = true
        swap
        · rw [if_neg hcond] at hcc; simp at hcc
        rw [if_pos hcond] at hcc
        injection hcc with hncc_eq
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        have hncc_val : ncc = (if (q0.1 % 8) % 2 = 1 ∨ (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 then 1 else 0) +
            2 * (if ((q0.1 % 8) / 2) % 2 = 1 ∨ ((M (Fin.last (n + 1))).1 / 2) % 2 < ((M (Fin.last (n + 1))).1 / 4) % 2 then 1 else 0) +
            4 * (if (q0.1 % 8) / 4 = 1 ∨ ((M (Fin.last (n + 1))).1 / 4) % 2 < (M (Fin.last (n + 1))).1 / 8 then 1 else 0) := by
          rw [← hncc_eq]; simp [Bool.or_eq_true]
        refine ⟨by rw [hqval, hncc_val]; split_ifs <;> omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h0 r
          rw [hqval, hncc_val] at h0
          have hbit0 : (q0.1 % 8) % 2 = 0 ∧ ¬((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2) := by
            split_ifs at h0 <;> omega
          refine Fin.lastCases ?_ ?_ r
          · rcases hcond.1.1 with hc | hle <;> omega
          · intro j; exact hc00 hbit0.1 j
        · intro h1
          by_cases h01 : (q0.1 % 8) % 2 = 1
          · obtain ⟨r, hr1, hr2⟩ := hc01 h01
            refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
            have hjlt : j.1 < n + 1 := by have := r.2; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
          · have h00 : (q0.1 % 8) % 2 = 0 := by omega
            rw [hqval, hncc_val] at h1
            have hlt_last : (M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2 := by
              split_ifs at h1 <;> omega
            refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
            have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hc00 h00 ⟨j.1, hjlt⟩
        · intro h0 r
          rw [hqval, hncc_val] at h0
          have hbit0 : ((q0.1 % 8) / 2) % 2 = 0 ∧ ¬(((M (Fin.last (n + 1))).1 / 2) % 2 < ((M (Fin.last (n + 1))).1 / 4) % 2) := by
            split_ifs at h0 <;> omega
          refine Fin.lastCases ?_ ?_ r
          · rcases hcond.1.2 with hc | hle <;> omega
          · intro j; exact hc10 hbit0.1 j
        · intro h1
          by_cases h01 : ((q0.1 % 8) / 2) % 2 = 1
          · obtain ⟨r, hr1, hr2⟩ := hc11 h01
            refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
            have hjlt : j.1 < n + 1 := by have := r.2; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
          · have h00 : ((q0.1 % 8) / 2) % 2 = 0 := by omega
            rw [hqval, hncc_val] at h1
            have hlt_last : ((M (Fin.last (n + 1))).1 / 2) % 2 < ((M (Fin.last (n + 1))).1 / 4) % 2 := by
              split_ifs at h1 <;> omega
            refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
            have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hc10 h00 ⟨j.1, hjlt⟩
        · intro h0 r
          rw [hqval, hncc_val] at h0
          have hbit0 : (q0.1 % 8) / 4 = 0 ∧ ¬(((M (Fin.last (n + 1))).1 / 4) % 2 < (M (Fin.last (n + 1))).1 / 8) := by
            split_ifs at h0 <;> omega
          refine Fin.lastCases ?_ ?_ r
          · rcases hcond.2 with hc | hle <;> omega
          · intro j; exact hc20 hbit0.1 j
        · intro h1
          by_cases h01 : (q0.1 % 8) / 4 = 1
          · obtain ⟨r, hr1, hr2⟩ := hc21 h01
            refine ⟨r.castSucc, fun j hj => ?_, hr2⟩
            have hjlt : j.1 < n + 1 := by have := r.2; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hr1 ⟨j.1, hjlt⟩ hj
          · have h00 : (q0.1 % 8) / 4 = 0 := by omega
            rw [hqval, hncc_val] at h1
            have hlt_last : ((M (Fin.last (n + 1))).1 / 4) % 2 < (M (Fin.last (n + 1))).1 / 8 := by
              split_ifs at h1 <;> omega
            refine ⟨Fin.last (n + 1), fun j hj => ?_, hlt_last⟩
            have hjlt : j.1 < n + 1 := by simp [Fin.last] at hj; omega
            have hjeq : (⟨j.1, hjlt⟩ : Fin (n + 1)).castSucc = j := Fin.ext rfl
            rw [← hjeq]; exact hc20 h00 ⟨j.1, hjlt⟩
        · intro r
          by_cases hr : r.1 < n
          · exact hrows0 ⟨r.1, hr⟩
          · have hreq : r.1 = n := by omega
            have e1 : (⟨r.1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := by apply Fin.ext; simp [Fin.last, hreq]
            have e2 : (⟨r.1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by apply Fin.ext; simp [Fin.last, hreq]
            have eA : r = Fin.last n := Fin.ext (by simp [Fin.last, hreq])
            have hr0' : (⟨q0.1 / 8, by have := q0.2; omega⟩ : Fin 16) = M (Fin.last n).castSucc := Fin.ext hr0
            rw [e1, e2, eA, ← hr0']
            exact hstep_ok

private lemma runNFA_complete (n : ℕ) (A : Fin n → Fin 8) (M : Fin (n + 1) → Fin 16)
    (hrow : ∀ r : Fin n, lex4Val (M ⟨r.1, by omega⟩) ≤ lex4Val (M ⟨r.1 + 1, by omega⟩) ∧
                         symOf (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) = (A r).1)
    (hcol0 : lexCol (n + 1) (fun r => dec4 (M r) 0) (fun r => dec4 (M r) 1))
    (hcol1 : lexCol (n + 1) (fun r => dec4 (M r) 1) (fun r => dec4 (M r) 2))
    (hcol2 : lexCol (n + 1) (fun r => dec4 (M r) 2) (fun r => dec4 (M r) 3)) :
    ∃ q : Fin 128, runNFA n A M = some q := by
  induction n with
  | zero =>
    unfold runNFA colUpd; dsimp only
    have hc0 : (M 0).1 % 2 ≤ ((M 0).1 / 2) % 2 := by
      rcases hcol0 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec4 at this; dsimp at this; omega
      · fin_cases r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1 : ((M 0).1 / 2) % 2 ≤ ((M 0).1 / 4) % 2 := by
      rcases hcol1 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec4 at this; dsimp at this; omega
      · fin_cases r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc2 : ((M 0).1 / 4) % 2 ≤ (M 0).1 / 8 := by
      rcases hcol2 with heq | ⟨r, _, hr2⟩
      · have := congrArg Fin.val (congrFun heq 0); unfold dec4 at this; dsimp at this; omega
      · fin_cases r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by simp [hc0, hc1, hc2])]
    dsimp only
    have hlt : (M 0).1 * 8 + ((if (0 == 1 || decide ((M 0).1 % 2 < ((M 0).1 / 2) % 2)) = true then 1 else 0) +
        2 * (if (0 == 1 || decide (((M 0).1 / 2) % 2 < ((M 0).1 / 4) % 2)) = true then 1 else 0) +
        4 * (if (0 == 1 || decide (((M 0).1 / 4) % 2 < (M 0).1 / 8)) = true then 1 else 0)) < 128 := by
      have := (M 0).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩
  | succ n ih =>
    have hcol0_prev : lexCol (n + 1) (fun r => dec4 (M r.castSucc) 0) (fun r => dec4 (M r.castSucc) 1) := by
      rcases hcol0 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    have hcol1_prev : lexCol (n + 1) (fun r => dec4 (M r.castSucc) 1) (fun r => dec4 (M r.castSucc) 2) := by
      rcases hcol1 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    have hcol2_prev : lexCol (n + 1) (fun r => dec4 (M r.castSucc) 2) (fun r => dec4 (M r.castSucc) 3) := by
      rcases hcol2 with heq | ⟨r, hr1, hr2⟩
      · left; funext i; exact congrFun heq i.castSucc
      · by_cases hr : r.1 < n + 1
        · right; refine ⟨⟨r.1, hr⟩, fun j hj => hr1 j.castSucc hj, hr2⟩
        · left; funext i; exact hr1 i.castSucc (by have := i.2; simp [Fin.val_castSucc]; omega)
    obtain ⟨q0, hq0⟩ := ih (fun i => A i.castSucc) (fun i => M i.castSucc)
      (fun r => hrow ⟨r.1, by omega⟩) hcol0_prev hcol1_prev hcol2_prev
    obtain ⟨hr0, hc00, _, hc10, _, hc20, _, _⟩ := runNFA_sound n (fun i => A i.castSucc) (fun i => M i.castSucc) q0 hq0
    unfold runNFA; rw [hq0]; unfold nfaStep; dsimp only
    have hr0' : (⟨q0.1 / 8, by have := q0.2; omega⟩ : Fin 16) = M (Fin.last n).castSucc := Fin.ext hr0
    have hstep := hrow (Fin.last n)
    have e1 : (⟨(Fin.last n).1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc := rfl
    have e2 : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
    rw [e1, e2] at hstep
    rw [hr0', if_pos (by simp [hstep.1, hstep.2])]
    unfold colUpd; dsimp only
    have hc0_ok : ((q0.1 % 8) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 ≤ ((M (Fin.last (n + 1))).1 / 2) % 2)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 8) % 2 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 8) % 2 = 0 := by omega
        rcases hcol0 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec4 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc00 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc1_ok : (((q0.1 % 8) / 2) % 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 ≤ ((M (Fin.last (n + 1))).1 / 4) % 2)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : ((q0.1 % 8) / 2) % 2 = 1
      · left; exact h1
      · right
        have h0 : ((q0.1 % 8) / 2) % 2 = 0 := by omega
        rcases hcol1 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec4 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc10 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    have hc2_ok : ((q0.1 % 8) / 4 == 1 || decide (((M (Fin.last (n + 1))).1 / 4) % 2 ≤ (M (Fin.last (n + 1))).1 / 8)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h1 : (q0.1 % 8) / 4 = 1
      · left; exact h1
      · right
        have h0 : (q0.1 % 8) / 4 = 0 := by omega
        rcases hcol2 with heq | ⟨r, _, hr2⟩
        · have := congrArg Fin.val (congrFun heq (Fin.last (n + 1))); unfold dec4 at this; dsimp at this; omega
        · by_cases hr : r.1 < n + 1
          · have h0r := hc20 h0 ⟨r.1, hr⟩
            have hreq : (⟨r.1, hr⟩ : Fin (n + 1)).castSucc = r := Fin.ext rfl
            rw [hreq] at h0r; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
          · have hreq : r = Fin.last (n + 1) := Fin.ext (by simp [Fin.last]; omega)
            rw [hreq] at hr2; unfold dec4 at hr2; simp only [Fin.lt_def] at hr2; dsimp at hr2; omega
    rw [if_pos (by rw [hc0_ok, hc1_ok, hc2_ok]; rfl)]; dsimp only
    have hlt : (M (Fin.last (n + 1))).1 * 8 + ((if ((q0.1 % 8) % 2 == 1 || decide ((M (Fin.last (n + 1))).1 % 2 < ((M (Fin.last (n + 1))).1 / 2) % 2)) = true then 1 else 0) +
        2 * (if (((q0.1 % 8) / 2) % 2 == 1 || decide (((M (Fin.last (n + 1))).1 / 2) % 2 < ((M (Fin.last (n + 1))).1 / 4) % 2)) = true then 1 else 0) +
        4 * (if ((q0.1 % 8) / 4 == 1 || decide (((M (Fin.last (n + 1))).1 / 4) % 2 < (M (Fin.last (n + 1))).1 / 8)) = true then 1 else 0)) < 128 := by
      have := (M (Fin.last (n + 1))).2; split_ifs <;> omega
    rw [dif_pos hlt]; exact ⟨_, rfl⟩

private lemma lexRow4_iff_lex4Val (r1 r2 : Fin 16) :
    lexRow4 (dec4 r1 0) (dec4 r1 1) (dec4 r1 2) (dec4 r1 3) (dec4 r2 0) (dec4 r2 1) (dec4 r2 2) (dec4 r2 3) ↔
    lex4Val r1 ≤ lex4Val r2 := by
  revert r1 r2; unfold lexRow4 dec4 lex4Val; decide

private lemma symOf_eq_subVal (r1 r2 : Fin 16) (s : Fin 8) :
    symOf r1 r2 = s.1 ↔
    (decSym s 0 = subVal (dec4 r1 0) (dec4 r1 1) (dec4 r2 0) (dec4 r2 1) ∧
     decSym s 1 = subVal (dec4 r1 1) (dec4 r1 2) (dec4 r2 1) (dec4 r2 2) ∧
     decSym s 2 = subVal (dec4 r1 2) (dec4 r1 3) (dec4 r2 2) (dec4 r2 3)) := by
  revert r1 r2 s; decide

private lemma isValid_iff_runDFA (n : ℕ) (A : Fin n → Fin 8) :
    isValid n (fun r => decSym (A r)) ↔ (runDFA n A).1 ≠ 7 := by
  rw [← dfaMask_empty_iff]
  simp only [runDFA_iff_runNFA]
  constructor
  · rintro ⟨M, ⟨hMrow, hMcol0, hMcol1, hMcol2⟩, hMA⟩
    let M' : Fin (n + 1) → Fin 16 := fun r => enc4 (M r)
    have hdec : ∀ r, dec4 (M' r) = M r := fun r => dec4_enc4 (M r)
    have hrow' : ∀ r : Fin n, lex4Val (M' ⟨r.1, by omega⟩) ≤ lex4Val (M' ⟨r.1 + 1, by omega⟩) ∧
                              symOf (M' ⟨r.1, by omega⟩) (M' ⟨r.1 + 1, by omega⟩) = (A r).1 := by
      intro r
      constructor
      · rw [← lexRow4_iff_lex4Val, hdec, hdec]; exact hMrow r
      · rw [symOf_eq_subVal, hdec, hdec]
        exact ⟨hMA r 0, hMA r 1, hMA r 2⟩
    have hcol0' : lexCol (n + 1) (fun r => dec4 (M' r) 0) (fun r => dec4 (M' r) 1) := by
      simp_rw [hdec]; exact hMcol0
    have hcol1' : lexCol (n + 1) (fun r => dec4 (M' r) 1) (fun r => dec4 (M' r) 2) := by
      simp_rw [hdec]; exact hMcol1
    have hcol2' : lexCol (n + 1) (fun r => dec4 (M' r) 2) (fun r => dec4 (M' r) 3) := by
      simp_rw [hdec]; exact hMcol2
    obtain ⟨q, hq⟩ := runNFA_complete n A M' hrow' hcol0' hcol1' hcol2'
    exact ⟨q, M', hq⟩
  · rintro ⟨q, M, hrun⟩
    obtain ⟨_, hc00, hc01, hc10, hc11, hc20, hc21, hrows⟩ := runNFA_sound n A M q hrun
    refine ⟨fun r => dec4 (M r), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro r; rw [lexRow4_iff_lex4Val]; exact (hrows r).1
    · by_cases h0 : (q.1 % 8) % 2 = 0
      · left; funext r; apply Fin.ext; unfold dec4; dsimp; exact hc00 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc01 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec4; dsimp; exact hr1 j hj, by unfold dec4; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · by_cases h0 : ((q.1 % 8) / 2) % 2 = 0
      · left; funext r; apply Fin.ext; unfold dec4; dsimp; exact hc10 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc11 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec4; dsimp; exact hr1 j hj, by unfold dec4; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · by_cases h0 : (q.1 % 8) / 4 = 0
      · left; funext r; apply Fin.ext; unfold dec4; dsimp; exact hc20 h0 r
      · right; obtain ⟨r, hr1, hr2⟩ := hc21 (by omega)
        refine ⟨r, fun j hj => by apply Fin.ext; unfold dec4; dsimp; exact hr1 j hj, by unfold dec4; simp only [Fin.lt_def]; dsimp; exact hr2⟩
    · intro r c
      have hsub := (symOf_eq_subVal (M ⟨r.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩) (A r)).mp (hrows r).2
      fin_cases c
      · exact hsub.1
      · exact hsub.2.1
      · exact hsub.2.2

private def dp : ℕ → Fin 37 → ℕ
  | 0, s => if s.1 = 0 then 1 else 0
  | n + 1, s' => ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp n s else 0

private lemma dp_succ_eq (n : ℕ) (s' : Fin 37) :
    dp (n + 1) s' = ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp n s else 0 := rfl

private def tbl_0 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 0) else (if s.1 < 3 then 0 else 0)) else (if s.1 < 6 then (if s.1 < 5 then 0 else 0) else (if s.1 < 7 then 0 else (if s.1 < 8 then 0 else 0)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 0 else 0) else (if s.1 < 12 then 0 else 0)) else (if s.1 < 15 then (if s.1 < 14 then 0 else 0) else (if s.1 < 16 then 0 else (if s.1 < 17 then 0 else 0))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 0 else 0) else (if s.1 < 21 then 0 else 0)) else (if s.1 < 24 then (if s.1 < 23 then 0 else 0) else (if s.1 < 25 then 0 else (if s.1 < 26 then 0 else 0)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 0 else 0) else (if s.1 < 30 then 0 else (if s.1 < 31 then 0 else 0))) else (if s.1 < 34 then (if s.1 < 33 then 0 else 0) else (if s.1 < 35 then 0 else (if s.1 < 36 then 0 else 0))))))
private def tbl_1 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 1) else (if s.1 < 3 then 1 else 1)) else (if s.1 < 6 then (if s.1 < 5 then 1 else 1) else (if s.1 < 7 then 1 else (if s.1 < 8 then 1 else 0)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 0 else 0) else (if s.1 < 12 then 0 else 0)) else (if s.1 < 15 then (if s.1 < 14 then 0 else 0) else (if s.1 < 16 then 0 else (if s.1 < 17 then 0 else 0))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 0 else 0) else (if s.1 < 21 then 0 else 0)) else (if s.1 < 24 then (if s.1 < 23 then 0 else 0) else (if s.1 < 25 then 0 else (if s.1 < 26 then 0 else 0)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 0 else 0) else (if s.1 < 30 then 0 else (if s.1 < 31 then 0 else 0))) else (if s.1 < 34 then (if s.1 < 33 then 0 else 0) else (if s.1 < 35 then 0 else (if s.1 < 36 then 0 else 0))))))
private def tbl_2 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 2) else (if s.1 < 3 then 2 else 3)) else (if s.1 < 6 then (if s.1 < 5 then 2 else 3) else (if s.1 < 7 then 3 else (if s.1 < 8 then 35 else 1)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 1 else 1) else (if s.1 < 12 then 1 else 1)) else (if s.1 < 15 then (if s.1 < 14 then 1 else 1) else (if s.1 < 16 then 1 else (if s.1 < 17 then 1 else 1))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 1 else 1) else (if s.1 < 21 then 1 else 0)) else (if s.1 < 24 then (if s.1 < 23 then 0 else 0) else (if s.1 < 25 then 0 else (if s.1 < 26 then 0 else 0)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 0 else 0) else (if s.1 < 30 then 0 else (if s.1 < 31 then 0 else 0))) else (if s.1 < 34 then (if s.1 < 33 then 0 else 0) else (if s.1 < 35 then 0 else (if s.1 < 36 then 0 else 0))))))
private def tbl_3 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 3) else (if s.1 < 3 then 3 else 6)) else (if s.1 < 6 then (if s.1 < 5 then 3 else 6) else (if s.1 < 7 then 6 else (if s.1 < 8 then 413 else 3)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 4 else 5) else (if s.1 < 12 then 8 else 3)) else (if s.1 < 15 then (if s.1 < 14 then 5 else 3) else (if s.1 < 16 then 5 else (if s.1 < 17 then 4 else 3))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 4 else 4) else (if s.1 < 21 then 4 else 1)) else (if s.1 < 24 then (if s.1 < 23 then 1 else 1) else (if s.1 < 25 then 2 else (if s.1 < 26 then 1 else 1)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 1 else 1) else (if s.1 < 30 then 2 else (if s.1 < 31 then 1 else 1))) else (if s.1 < 34 then (if s.1 < 33 then 1 else 1) else (if s.1 < 35 then 1 else (if s.1 < 36 then 0 else 0))))))
private def tbl_4 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 4) else (if s.1 < 3 then 4 else 10)) else (if s.1 < 6 then (if s.1 < 5 then 4 else 10) else (if s.1 < 7 then 10 else (if s.1 < 8 then 3794 else 6)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 10 else 15) else (if s.1 < 12 then 35 else 6)) else (if s.1 < 15 then (if s.1 < 14 then 15 else 6) else (if s.1 < 16 then 15 else (if s.1 < 17 then 10 else 6))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 10 else 10) else (if s.1 < 21 then 10 else 5)) else (if s.1 < 24 then (if s.1 < 23 then 11 else 6) else (if s.1 < 25 then 17 else (if s.1 < 26 then 6 else 4)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 5 else 6) else (if s.1 < 30 then 12 else (if s.1 < 31 then 6 else 6))) else (if s.1 < 34 then (if s.1 < 33 then 5 else 7) else (if s.1 < 35 then 7 else (if s.1 < 36 then 1 else 1))))))
private def tbl_5 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 5) else (if s.1 < 3 then 5 else 15)) else (if s.1 < 6 then (if s.1 < 5 then 5 else 15) else (if s.1 < 7 then 15 else (if s.1 < 8 then 31926 else 10)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 20 else 35) else (if s.1 < 12 then 114 else 10)) else (if s.1 < 15 then (if s.1 < 14 then 35 else 10) else (if s.1 < 16 then 35 else (if s.1 < 17 then 20 else 10))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 20 else 20) else (if s.1 < 21 then 20 else 15)) else (if s.1 < 24 then (if s.1 < 23 then 62 else 21) else (if s.1 < 25 then 80 else (if s.1 < 26 then 21 else 10)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 15 else 22) else (if s.1 < 30 then 43 else (if s.1 < 31 then 21 else 21))) else (if s.1 < 34 then (if s.1 < 33 then 15 else 34) else (if s.1 < 35 then 29 else (if s.1 < 36 then 6 else 7))))))
private def tbl_6 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 6) else (if s.1 < 3 then 6 else 21)) else (if s.1 < 6 then (if s.1 < 5 then 6 else 21) else (if s.1 < 7 then 21 else (if s.1 < 8 then 259967 else 15)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 35 else 70) else (if s.1 < 12 then 311 else 15)) else (if s.1 < 15 then (if s.1 < 14 then 70 else 15) else (if s.1 < 16 then 70 else (if s.1 < 17 then 35 else 15))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 35 else 35) else (if s.1 < 21 then 35 else 35)) else (if s.1 < 24 then (if s.1 < 23 then 249 else 56) else (if s.1 < 25 then 279 else (if s.1 < 26 then 56 else 20)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 35 else 63) else (if s.1 < 30 then 119 else (if s.1 < 31 then 56 else 56))) else (if s.1 < 34 then (if s.1 < 33 then 35 else 138) else (if s.1 < 35 then 92 else (if s.1 < 36 then 21 else 29))))))
private def tbl_7 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 7) else (if s.1 < 3 then 7 else 28)) else (if s.1 < 6 then (if s.1 < 5 then 7 else 28) else (if s.1 < 7 then 28 else (if s.1 < 8 then 2091871 else 21)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 56 else 126) else (if s.1 < 12 then 753 else 21)) else (if s.1 < 15 then (if s.1 < 14 then 126 else 21) else (if s.1 < 16 then 126 else (if s.1 < 17 then 56 else 21))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 56 else 56) else (if s.1 < 21 then 56 else 70)) else (if s.1 < 24 then (if s.1 < 23 then 810 else 126) else (if s.1 < 25 then 808 else (if s.1 < 26 then 126 else 35)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 70 else 154) else (if s.1 < 30 then 280 else (if s.1 < 31 then 126 else 126))) else (if s.1 < 34 then (if s.1 < 33 then 70 else 485) else (if s.1 < 35 then 246 else (if s.1 < 36 then 56 else 92))))))
private def tbl_8 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 8) else (if s.1 < 3 then 8 else 36)) else (if s.1 < 6 then (if s.1 < 5 then 8 else 36) else (if s.1 < 7 then 36 else (if s.1 < 8 then 16765088 else 28)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 84 else 210) else (if s.1 < 12 then 1671 else 28)) else (if s.1 < 15 then (if s.1 < 14 then 210 else 28) else (if s.1 < 16 then 210 else (if s.1 < 17 then 84 else 28))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 84 else 84) else (if s.1 < 21 then 84 else 126)) else (if s.1 < 24 then (if s.1 < 23 then 2278 else 252) else (if s.1 < 25 then 2059 else (if s.1 < 26 then 252 else 56)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 126 else 336) else (if s.1 < 30 then 588 else (if s.1 < 31 then 252 else 252))) else (if s.1 < 34 then (if s.1 < 33 then 126 else 1505) else (if s.1 < 35 then 582 else (if s.1 < 36 then 126 else 246))))))
private def tbl_9 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 9) else (if s.1 < 3 then 9 else 45)) else (if s.1 < 6 then (if s.1 < 5 then 9 else 45) else (if s.1 < 7 then 45 else (if s.1 < 8 then 134191180 else 36)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 120 else 330) else (if s.1 < 12 then 3465 else 36)) else (if s.1 < 15 then (if s.1 < 14 then 330 else 36) else (if s.1 < 16 then 330 else (if s.1 < 17 then 120 else 36))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 120 else 120) else (if s.1 < 21 then 120 else 210)) else (if s.1 < 24 then (if s.1 < 23 then 5753 else 462) else (if s.1 < 25 then 4774 else (if s.1 < 26 then 462 else 84)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 210 else 672) else (if s.1 < 30 then 1134 else (if s.1 < 31 then 462 else 462))) else (if s.1 < 34 then (if s.1 < 33 then 210 else 4203) else (if s.1 < 35 then 1254 else (if s.1 < 36 then 252 else 582))))))
private def tbl_10 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 10) else (if s.1 < 3 then 10 else 55)) else (if s.1 < 6 then (if s.1 < 5 then 10 else 55) else (if s.1 < 7 then 55 else (if s.1 < 8 then 1073686140 else 45)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 165 else 495) else (if s.1 < 12 then 6798 else 45)) else (if s.1 < 15 then (if s.1 < 14 then 495 else 45) else (if s.1 < 16 then 495 else (if s.1 < 17 then 165 else 45))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 165 else 165) else (if s.1 < 21 then 165 else 330)) else (if s.1 < 24 then (if s.1 < 23 then 13365 else 792) else (if s.1 < 25 then 10285 else (if s.1 < 26 then 792 else 120)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 330 else 1254) else (if s.1 < 30 then 2046 else (if s.1 < 31 then 792 else 792))) else (if s.1 < 34 then (if s.1 < 33 then 330 else 10748) else (if s.1 < 35 then 2508 else (if s.1 < 36 then 462 else 1254))))))
private def tbl_11 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 11) else (if s.1 < 3 then 11 else 66)) else (if s.1 < 6 then (if s.1 < 5 then 11 else 66) else (if s.1 < 7 then 66 else (if s.1 < 8 then 8589822203 else 55)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 220 else 715) else (if s.1 < 12 then 12727 else 55)) else (if s.1 < 15 then (if s.1 < 14 then 715 else 55) else (if s.1 < 16 then 715 else (if s.1 < 17 then 220 else 55))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 220 else 220) else (if s.1 < 21 then 220 else 495)) else (if s.1 < 24 then (if s.1 < 23 then 29029 else 1287) else (if s.1 < 25 then 20878 else (if s.1 < 26 then 1287 else 165)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 495 else 2211) else (if s.1 < 30 then 3498 else (if s.1 < 31 then 1287 else 1287))) else (if s.1 < 34 then (if s.1 < 33 then 495 else 25532) else (if s.1 < 35 then 4719 else (if s.1 < 36 then 792 else 2508))))))
private def tbl_12 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 12) else (if s.1 < 3 then 12 else 78)) else (if s.1 < 6 then (if s.1 < 5 then 12 else 78) else (if s.1 < 7 then 78 else (if s.1 < 8 then 68719257685 else 66)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 286 else 1001) else (if s.1 < 12 then 22880 else 66)) else (if s.1 < 15 then (if s.1 < 14 then 1001 else 66) else (if s.1 < 16 then 1001 else (if s.1 < 17 then 286 else 66))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 286 else 286) else (if s.1 < 21 then 286 else 715)) else (if s.1 < 24 then (if s.1 < 23 then 59631 else 2002) else (if s.1 < 25 then 40326 else (if s.1 < 26 then 2002 else 220)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 715 else 3718) else (if s.1 < 30 then 5720 else (if s.1 < 31 then 2002 else 2002))) else (if s.1 < 34 then (if s.1 < 33 then 715 else 56992) else (if s.1 < 35 then 8437 else (if s.1 < 36 then 1287 else 4719))))))
private def tbl_13 (s : Fin 37) : ℕ :=
  (if s.1 < 18 then (if s.1 < 9 then (if s.1 < 4 then (if s.1 < 2 then (if s.1 < 1 then 1 else 13) else (if s.1 < 3 then 13 else 91)) else (if s.1 < 6 then (if s.1 < 5 then 13 else 91) else (if s.1 < 7 then 91 else (if s.1 < 8 then 549755400357 else 78)))) else (if s.1 < 13 then (if s.1 < 11 then (if s.1 < 10 then 364 else 1365) else (if s.1 < 12 then 39689 else 78)) else (if s.1 < 15 then (if s.1 < 14 then 1365 else 78) else (if s.1 < 16 then 1365 else (if s.1 < 17 then 364 else 78))))) else (if s.1 < 27 then (if s.1 < 22 then (if s.1 < 20 then (if s.1 < 19 then 364 else 364) else (if s.1 < 21 then 364 else 1001)) else (if s.1 < 24 then (if s.1 < 23 then 116831 else 3003) else (if s.1 < 25 then 74646 else (if s.1 < 26 then 3003 else 286)))) else (if s.1 < 32 then (if s.1 < 29 then (if s.1 < 28 then 1001 else 6006) else (if s.1 < 30 then 9009 else (if s.1 < 31 then 3003 else 3003))) else (if s.1 < 34 then (if s.1 < 33 then 1001 else 120627) else (if s.1 < 35 then 14443 else (if s.1 < 36 then 2002 else 8437))))))

private lemma dp_eq_tbl_0 (s : Fin 37) : dp 0 s = tbl_0 s := by revert s; decide
private lemma dp_step_ok_1_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_0 s else 0) = tbl_1 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_1 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_0 s else 0) = tbl_1 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_1_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_1 (s' : Fin 37) : dp 1 s' = tbl_1 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 0 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_0 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_0]
  rw [h1]; exact dp_step_ok_1 s' 
private lemma dp_step_ok_2_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_1 s else 0) = tbl_2 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_2 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_1 s else 0) = tbl_2 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_2_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_2 (s' : Fin 37) : dp 2 s' = tbl_2 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 1 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_1]
  rw [h1]; exact dp_step_ok_2 s' 
private lemma dp_step_ok_3_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_2 s else 0) = tbl_3 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_3 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_2 s else 0) = tbl_3 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_3_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_3 (s' : Fin 37) : dp 3 s' = tbl_3 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 2 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_2]
  rw [h1]; exact dp_step_ok_3 s' 
private lemma dp_step_ok_4_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_3 s else 0) = tbl_4 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_4 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_3 s else 0) = tbl_4 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_4_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_4 (s' : Fin 37) : dp 4 s' = tbl_4 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 3 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_3]
  rw [h1]; exact dp_step_ok_4 s' 
private lemma dp_step_ok_5_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_4 s else 0) = tbl_5 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_5 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_4 s else 0) = tbl_5 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_5_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_5 (s' : Fin 37) : dp 5 s' = tbl_5 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 4 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_4]
  rw [h1]; exact dp_step_ok_5 s' 
private lemma dp_step_ok_6_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_5 s else 0) = tbl_6 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_6 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_5 s else 0) = tbl_6 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_6_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_6 (s' : Fin 37) : dp 6 s' = tbl_6 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 5 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_5]
  rw [h1]; exact dp_step_ok_6 s' 
private lemma dp_step_ok_7_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_6 s else 0) = tbl_7 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_7 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_6 s else 0) = tbl_7 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_7_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_7 (s' : Fin 37) : dp 7 s' = tbl_7 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 6 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_6]
  rw [h1]; exact dp_step_ok_7 s' 
private lemma dp_step_ok_8_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_7 s else 0) = tbl_8 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_8 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_7 s else 0) = tbl_8 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_8_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_8 (s' : Fin 37) : dp 8 s' = tbl_8 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 7 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_7]
  rw [h1]; exact dp_step_ok_8 s' 
private lemma dp_step_ok_9_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_8 s else 0) = tbl_9 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_9 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_8 s else 0) = tbl_9 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_9_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_9 (s' : Fin 37) : dp 9 s' = tbl_9 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 8 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_8]
  rw [h1]; exact dp_step_ok_9 s' 
private lemma dp_step_ok_10_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_9 s else 0) = tbl_10 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_10 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_9 s else 0) = tbl_10 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_10_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_10 (s' : Fin 37) : dp 10 s' = tbl_10 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 9 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_9]
  rw [h1]; exact dp_step_ok_10 s' 
private lemma dp_step_ok_11_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_10 s else 0) = tbl_11 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_11 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_10 s else 0) = tbl_11 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_11_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_11 (s' : Fin 37) : dp 11 s' = tbl_11 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 10 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_10]
  rw [h1]; exact dp_step_ok_11 s' 
private lemma dp_step_ok_12_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_11 s else 0) = tbl_12 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_12 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_11 s else 0) = tbl_12 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_12_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_12 (s' : Fin 37) : dp 12 s' = tbl_12 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 11 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_11]
  rw [h1]; exact dp_step_ok_12 s' 
private lemma dp_step_ok_13_0 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨0 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨0 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_8 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨8 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨8 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_16 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨16 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨16 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_24 : ∀ i : Fin 8,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨24 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨24 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13_32 : ∀ i : Fin 5,
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = ⟨32 + i.1, by omega⟩ then tbl_12 s else 0) = tbl_13 ⟨32 + i.1, by omega⟩ := by decide
private lemma dp_step_ok_13 (s' : Fin 37) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_12 s else 0) = tbl_13 s' := by
  if h0 : s'.1 < 8 then
    have hs : s' = ⟨0 + (s'.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_0 ⟨s'.1 - 0, by omega⟩
  else
  if h8 : s'.1 < 16 then
    have hs : s' = ⟨8 + (s'.1 - 8), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_8 ⟨s'.1 - 8, by omega⟩
  else
  if h16 : s'.1 < 24 then
    have hs : s' = ⟨16 + (s'.1 - 16), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_16 ⟨s'.1 - 16, by omega⟩
  else
  if h24 : s'.1 < 32 then
    have hs : s' = ⟨24 + (s'.1 - 24), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_24 ⟨s'.1 - 24, by omega⟩
  else
    have hs : s' = ⟨32 + (s'.1 - 32), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hs]; exact dp_step_ok_13_32 ⟨s'.1 - 32, by omega⟩

private lemma dp_eq_tbl_13 (s' : Fin 37) : dp 13 s' = tbl_13 s' := by
  rw [dp_succ_eq]
  have h1 : (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then dp 12 s else 0) =
      ∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro sym _
    rw [dp_eq_tbl_12]
  rw [h1]; exact dp_step_ok_13 s' 

private lemma dp_rec_tbl_ok : ∀ s : Fin 37, s.1 ≠ 7 → tbl_13 s + 66 * tbl_11 s + 495 * tbl_9 s + 924 * tbl_7 s + 495 * tbl_5 s + 66 * tbl_3 s + tbl_1 s = 12 * tbl_12 s + 220 * tbl_10 s + 792 * tbl_8 s + 792 * tbl_6 s + 220 * tbl_4 s + 12 * tbl_2 s := by decide

private lemma dp_rec_base : ∀ s : Fin 37, s.1 ≠ 7 → dp 13 s + 66 * dp 11 s + 495 * dp 9 s + 924 * dp 7 s + 495 * dp 5 s + 66 * dp 3 s + dp 1 s = 12 * dp 12 s + 220 * dp 10 s + 792 * dp 8 s + 792 * dp 6 s + 220 * dp 4 s + 12 * dp 2 s := by
  intro s hs; rw [dp_eq_tbl_1, dp_eq_tbl_2, dp_eq_tbl_3, dp_eq_tbl_4, dp_eq_tbl_5, dp_eq_tbl_6, dp_eq_tbl_7, dp_eq_tbl_8, dp_eq_tbl_9, dp_eq_tbl_10, dp_eq_tbl_11, dp_eq_tbl_12, dp_eq_tbl_13]; exact dp_rec_tbl_ok s hs

private lemma sum_lin (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 : Fin 37 → ℕ) (s' : Fin 37) (hs' : s'.1 ≠ 7)
    (h : ∀ s : Fin 37, s.1 ≠ 7 → f12 s + 66 * f10 s + 495 * f8 s + 924 * f6 s + 495 * f4 s + 66 * f2 s + f0 s = 12 * f11 s + 220 * f9 s + 792 * f7 s + 792 * f5 s + 220 * f3 s + 12 * f1 s) :
    (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f12 s else 0) + 66 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f10 s else 0) + 495 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f8 s else 0) + 924 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f6 s else 0) + 495 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f4 s else 0) + 66 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f2 s else 0) + (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f0 s else 0) = 12 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f11 s else 0) + 220 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f9 s else 0) + 792 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f7 s else 0) + 792 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f5 s else 0) + 220 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f3 s else 0) + 12 * (∑ s : Fin 37, ∑ sym : Fin 8, if dfaTrans s sym = s' then f1 s else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro sym _
  by_cases htr : dfaTrans s sym = s'
  · simp only [htr, ↓reduceIte]
    have hs : s.1 ≠ 7 := by
      intro heq
      have h1 : s = ⟨7, by omega⟩ := Fin.ext heq
      have h2 : dfaTrans s sym = ⟨7, by omega⟩ := h1 ▸ dfaTrans_empty sym
      rw [htr] at h2; exact hs' (congrArg Fin.val h2)
    exact h s hs
  · simp [htr]

private lemma dp_rec (m : ℕ) : ∀ s : Fin 37, s.1 ≠ 7 → dp (m + 13) s + 66 * dp (m + 11) s + 495 * dp (m + 9) s + 924 * dp (m + 7) s + 495 * dp (m + 5) s + 66 * dp (m + 3) s + dp (m + 1) s = 12 * dp (m + 12) s + 220 * dp (m + 10) s + 792 * dp (m + 8) s + 792 * dp (m + 6) s + 220 * dp (m + 4) s + 12 * dp (m + 2) s := by
  induction m with
  | zero => exact dp_rec_base
  | succ m ih =>
    intro s' hs'; rw [dp_succ_eq (m + 1), dp_succ_eq (m + 2), dp_succ_eq (m + 3), dp_succ_eq (m + 4), dp_succ_eq (m + 5), dp_succ_eq (m + 6), dp_succ_eq (m + 7), dp_succ_eq (m + 8), dp_succ_eq (m + 9), dp_succ_eq (m + 10), dp_succ_eq (m + 11), dp_succ_eq (m + 12), dp_succ_eq (m + 13)]
    exact sum_lin (dp (m + 1)) (dp (m + 2)) (dp (m + 3)) (dp (m + 4)) (dp (m + 5)) (dp (m + 6)) (dp (m + 7)) (dp (m + 8)) (dp (m + 9)) (dp (m + 10)) (dp (m + 11)) (dp (m + 12)) (dp (m + 13)) s' hs' ih

private lemma card_runDFA (n : ℕ) : ∀ s : Fin 37, Fintype.card {A : Fin n → Fin 8 // runDFA n A = s} = dp n s := by
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
    let φ : (Σ s : Fin 37, Σ sym : Fin 8, {A : Fin n → Fin 8 // runDFA n A = s ∧ dfaTrans s sym = s'}) →
        {A : Fin (n + 1) → Fin 8 // runDFA (n + 1) A = s'} :=
      fun ⟨s, sym, ⟨A, hA, htr⟩⟩ =>
        ⟨Fin.snoc A sym, by
          unfold runDFA
          have hc : (fun i : Fin n => (Fin.snoc A sym : Fin (n + 1) → Fin 8) i.castSucc) = A := by
            funext i; exact Fin.snoc_castSucc _ _ i
          rw [hc, hA, Fin.snoc_last]; exact htr⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨sa, syma, ⟨Aa, hAa, _⟩⟩ ⟨sb, symb, ⟨Ab, hAb, _⟩⟩ heq
        have hfun : (Fin.snoc Aa syma : Fin (n + 1) → Fin 8) = Fin.snoc Ab symb := congrArg Subtype.val heq
        have hAeq : Aa = Ab := by funext i; simpa using congrFun hfun i.castSucc
        have hsymeq : syma = symb := by simpa using congrFun hfun (Fin.last n)
        subst hAeq; subst hsymeq
        have hseq : sa = sb := hAa.symm.trans hAb
        subst hseq; rfl
      · rintro ⟨A, hA⟩
        let A0 : Fin n → Fin 8 := fun i => A i.castSucc
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
    a n = ∑ s : Fin 37, if s.1 ≠ 7 then dp n s else 0 := by
  unfold a; rw [if_neg (by omega)]
  let φ : (Σ s : Fin 37, {A : Fin n → Fin 8 // runDFA n A = s ∧ s.1 ≠ 7}) →
      {A : Fin n → Fin 3 → Fin 2 // isValid n A} :=
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
        have h2 : (decSym (Aa r) 2) = decSym (Ab r) 2 := congrFun h 2
        unfold decSym at h0 h1 h2; simp only [Fin.ext_iff] at h0 h1 h2; dsimp at h0 h1 h2
        have ha := (Aa r).2; have hb := (Ab r).2
        apply Fin.ext; omega
      subst hAeq
      have hseq : sa = sb := hAa.symm.trans hAb
      subst hseq; rfl
    · rintro ⟨A, hA⟩
      let A' : Fin n → Fin 8 := fun r => encSym (A r)
      have hdecA : (fun r => decSym (A' r)) = A := by
        funext r c
        fin_cases c <;> (apply Fin.ext; unfold A' encSym decSym; dsimp; have := (A r 0).2; have := (A r 1).2; have := (A r 2).2; omega)
      have hs : (runDFA n A').1 ≠ 7 := (isValid_iff_runDFA n A').mp (hdecA.symm ▸ hA)
      refine ⟨⟨runDFA n A', ⟨A', rfl, hs⟩⟩, ?_⟩
      apply Subtype.ext; exact hdecA
  rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 7
  · rw [if_pos hs, ← card_runDFA n s]
    refine Fintype.card_congr ⟨fun ⟨A, h1, _⟩ => ⟨A, h1⟩, fun ⟨A, h1⟩ => ⟨A, h1, hs⟩, fun ⟨_, _, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
  · rw [if_neg hs, Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨_, _, h⟩ => hs h⟩

private lemma a_rec_m (m : ℕ) : a (m + 13) + 66 * a (m + 11) + 495 * a (m + 9) + 924 * a (m + 7) + 495 * a (m + 5) + 66 * a (m + 3) + a (m + 1) = 12 * a (m + 12) + 220 * a (m + 10) + 792 * a (m + 8) + 792 * a (m + 6) + 220 * a (m + 4) + 12 * a (m + 2) := by
  rw [a_eq_sum_dp (m + 1) (by omega), a_eq_sum_dp (m + 2) (by omega), a_eq_sum_dp (m + 3) (by omega), a_eq_sum_dp (m + 4) (by omega), a_eq_sum_dp (m + 5) (by omega), a_eq_sum_dp (m + 6) (by omega), a_eq_sum_dp (m + 7) (by omega), a_eq_sum_dp (m + 8) (by omega), a_eq_sum_dp (m + 9) (by omega), a_eq_sum_dp (m + 10) (by omega), a_eq_sum_dp (m + 11) (by omega), a_eq_sum_dp (m + 12) (by omega), a_eq_sum_dp (m + 13) (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  by_cases hs : s.1 ≠ 7
  · simp only [if_pos hs]; exact dp_rec m s hs
  · simp only [if_neg hs, mul_zero, add_zero]

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_sum_ok_1 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_1 s else 0) = 7 := by decide
private lemma a_val_1 : a 1 = 7 := by
  rw [a_eq_sum_dp 1 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 1 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_1 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_1]
  rw [h]; exact a_sum_ok_1
private lemma a_sum_ok_2 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_2 s else 0) = 29 := by decide
private lemma a_val_2 : a 2 = 29 := by
  rw [a_eq_sum_dp 2 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 2 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_2 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_2]
  rw [h]; exact a_sum_ok_2
private lemma a_sum_ok_3 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_3 s else 0) = 99 := by decide
private lemma a_val_3 : a 3 = 99 := by
  rw [a_eq_sum_dp 3 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 3 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_3 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_3]
  rw [h]; exact a_sum_ok_3
private lemma a_sum_ok_4 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_4 s else 0) = 302 := by decide
private lemma a_val_4 : a 4 = 302 := by
  rw [a_eq_sum_dp 4 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 4 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_4 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_4]
  rw [h]; exact a_sum_ok_4
private lemma a_sum_ok_5 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_5 s else 0) = 842 := by decide
private lemma a_val_5 : a 5 = 842 := by
  rw [a_eq_sum_dp 5 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 5 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_5 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_5]
  rw [h]; exact a_sum_ok_5
private lemma a_sum_ok_6 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_6 s else 0) = 2177 := by decide
private lemma a_val_6 : a 6 = 2177 := by
  rw [a_eq_sum_dp 6 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 6 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_6 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_6]
  rw [h]; exact a_sum_ok_6
private lemma a_sum_ok_7 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_7 s else 0) = 5281 := by decide
private lemma a_val_7 : a 7 = 5281 := by
  rw [a_eq_sum_dp 7 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 7 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_7 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_7]
  rw [h]; exact a_sum_ok_7
private lemma a_sum_ok_8 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_8 s else 0) = 12128 := by decide
private lemma a_val_8 : a 8 = 12128 := by
  rw [a_eq_sum_dp 8 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 8 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_8 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_8]
  rw [h]; exact a_sum_ok_8
private lemma a_sum_ok_9 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_9 s else 0) = 26548 := by decide
private lemma a_val_9 : a 9 = 26548 := by
  rw [a_eq_sum_dp 9 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 9 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_9 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_9]
  rw [h]; exact a_sum_ok_9
private lemma a_sum_ok_10 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_10 s else 0) = 55684 := by decide
private lemma a_val_10 : a 10 = 55684 := by
  rw [a_eq_sum_dp 10 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 10 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_10 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_10]
  rw [h]; exact a_sum_ok_10
private lemma a_sum_ok_11 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_11 s else 0) = 112389 := by decide
private lemma a_val_11 : a 11 = 112389 := by
  rw [a_eq_sum_dp 11 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 11 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_11 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_11]
  rw [h]; exact a_sum_ok_11
private lemma a_sum_ok_12 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_12 s else 0) = 219051 := by decide
private lemma a_val_12 : a 12 = 219051 := by
  rw [a_eq_sum_dp 12 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 12 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_12 s else 0 := by
    apply Finset.sum_congr rfl; intro s _; split_ifs <;> simp [dp_eq_tbl_12]
  rw [h]; exact a_sum_ok_12
private lemma a_sum_ok_13 : (∑ s : Fin 37, if s.1 ≠ 7 then tbl_13 s else 0) = 413531 := by decide
private lemma a_val_13 : a 13 = 413531 := by
  rw [a_eq_sum_dp 13 (by omega)]
  have h : (∑ s : Fin 37, if s.1 ≠ 7 then dp 13 s else 0) =
      ∑ s : Fin 37, if s.1 ≠ 7 then tbl_13 s else 0 := by
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

theorem solution : type_of% @OMA.S_oeis_a227086.main := by
  have hrec : ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * (a (n - 1) : ℤ) - 66 * (a (n - 2) : ℤ) + 220 * (a (n - 3) : ℤ) - 495 * (a (n - 4) : ℤ) + 792 * (a (n - 5) : ℤ) - 924 * (a (n - 6) : ℤ) + 792 * (a (n - 7) : ℤ) - 495 * (a (n - 8) : ℤ) + 220 * (a (n - 9) : ℤ) - 66 * (a (n - 10) : ℤ) + 12 * (a (n - 11) : ℤ) - (a (n - 12) : ℤ) := by
    intro n hn
    have h := a_rec_m (n - 13)
    simp only [show n - 13 + 13 = n by omega, show n - 13 + 12 = n - 1 by omega, show n - 13 + 11 = n - 2 by omega, show n - 13 + 10 = n - 3 by omega, show n - 13 + 9 = n - 4 by omega, show n - 13 + 8 = n - 5 by omega, show n - 13 + 7 = n - 6 by omega, show n - 13 + 6 = n - 7 by omega, show n - 13 + 5 = n - 8 by omega, show n - 13 + 4 = n - 9 by omega, show n - 13 + 3 = n - 10 by omega, show n - 13 + 2 = n - 11 by omega, show n - 13 + 1 = n - 12 by omega] at h
    omega
  refine ⟨?_, hrec⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 12 = 1 - PowerSeries.C 12 * PowerSeries.X ^ 1 + PowerSeries.C 66 * PowerSeries.X ^ 2 - PowerSeries.C 220 * PowerSeries.X ^ 3 + PowerSeries.C 495 * PowerSeries.X ^ 4 - PowerSeries.C 792 * PowerSeries.X ^ 5 + PowerSeries.C 924 * PowerSeries.X ^ 6 - PowerSeries.C 792 * PowerSeries.X ^ 7 + PowerSeries.C 495 * PowerSeries.X ^ 8 - PowerSeries.C 220 * PowerSeries.X ^ 9 + PowerSeries.C 66 * PowerSeries.X ^ 10 - PowerSeries.C 12 * PowerSeries.X ^ 11 + PowerSeries.X ^ 12 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (PowerSeries.X : PowerSeries ℚ) * (7 - 55 * PowerSeries.X + 213 * PowerSeries.X ^ 2 - 512 * PowerSeries.X ^ 3 + 837 * PowerSeries.X ^ 4 - 964 * PowerSeries.X ^ 5 + 794 * PowerSeries.X ^ 6 - 468 * PowerSeries.X ^ 7 + 197 * PowerSeries.X ^ 8 - 58 * PowerSeries.X ^ 9 + 11 * PowerSeries.X ^ 10 - PowerSeries.X ^ 11) = PowerSeries.C 7 * PowerSeries.X ^ 1 - PowerSeries.C 55 * PowerSeries.X ^ 2 + PowerSeries.C 213 * PowerSeries.X ^ 3 - PowerSeries.C 512 * PowerSeries.X ^ 4 + PowerSeries.C 837 * PowerSeries.X ^ 5 - PowerSeries.C 964 * PowerSeries.X ^ 6 + PowerSeries.C 794 * PowerSeries.X ^ 7 - PowerSeries.C 468 * PowerSeries.X ^ 8 + PowerSeries.C 197 * PowerSeries.X ^ 9 - PowerSeries.C 58 * PowerSeries.X ^ 10 + PowerSeries.C 11 * PowerSeries.X ^ 11 - PowerSeries.X ^ 12 := by
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
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]
  · simp [a_zero, a_val_1, a_val_2]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11]; norm_num
  · simp [a_zero, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 13 by omega, show 2 ≤ m + 13 by omega, show 3 ≤ m + 13 by omega, show 4 ≤ m + 13 by omega, show 5 ≤ m + 13 by omega, show 6 ≤ m + 13 by omega, show 7 ≤ m + 13 by omega, show 8 ≤ m + 13 by omega, show 9 ≤ m + 13 by omega, show 10 ≤ m + 13 by omega, show 11 ≤ m + 13 by omega, show 12 ≤ m + 13 by omega, ↓reduceIte,
      show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13 - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega, show m + 13 - 9 = m + 4 by omega, show m + 13 - 10 = m + 3 by omega, show m + 13 - 11 = m + 2 by omega, show m + 13 - 12 = m + 1 by omega, show ¬(m + 13 = 1) by omega, show ¬(m + 13 = 2) by omega, show ¬(m + 13 = 3) by omega, show ¬(m + 13 = 4) by omega, show ¬(m + 13 = 5) by omega, show ¬(m + 13 = 6) by omega, show ¬(m + 13 = 7) by omega, show ¬(m + 13 = 8) by omega, show ¬(m + 13 = 9) by omega, show ¬(m + 13 = 10) by omega, show ¬(m + 13 = 11) by omega, show ¬(m + 13 = 12) by omega]
    have hr := hrec (m + 13) (by omega)
    simp only [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13 - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega, show m + 13 - 9 = m + 4 by omega, show m + 13 - 10 = m + 3 by omega, show m + 13 - 11 = m + 2 by omega, show m + 13 - 12 = m + 1 by omega] at hr
    have hrq : (a (m + 13) : ℚ) = 12 * (a (m + 12) : ℚ) - 66 * (a (m + 11) : ℚ) + 220 * (a (m + 10) : ℚ) - 495 * (a (m + 9) : ℚ) + 792 * (a (m + 8) : ℚ) - 924 * (a (m + 7) : ℚ) + 792 * (a (m + 6) : ℚ) - 495 * (a (m + 5) : ℚ) + 220 * (a (m + 4) : ℚ) - 66 * (a (m + 3) : ℚ) + 12 * (a (m + 2) : ℚ) - (a (m + 1) : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a227086

theorem OMA.solution : type_of% @OMA.S_oeis_a227086.main :=
  OMA.P_oeis_a227086.solution
