import OMAStatements.S_oeis_a022025

-- Problem: A022025: Define the sequence S(a(0),a(1)) by a(n+2) is the least integer such that a(n+2)/a(n+1) > a(n+1)/a(n) for n >= 0. This is S(6,102).
-- Upstream: formal-conjectures statements/oeis-a022025.lean:0 (declaration OMA.S_oeis_a022025.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: if the g.f. identity held, comparing coefficients would give a(2) = 1735 and
-- a(n) = 17 a(n-1) + a(n-2) - 14 a(n-3) for n >= 3, which determine a(3), ..., a(272) as numerals.
-- But the definition gives a(272) = floor(a(271)^2/a(270)) + 1, so a(271)^2 < a(272) a(270),
-- and for these numerals a(271)^2 >= a(272) a(270) (the entry: the g.f. fails from a(272) on).

open OMA.S_oeis_a022025 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a022025.main) := by
  intro H
  have e : PowerSeries.mk (fun n => (a n : ℚ)) *
      (1 - 17 * PowerSeries.X - PowerSeries.X ^ 2 + 14 * PowerSeries.X ^ 3) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 17 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 17,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14]
    ring
  have e2 : (6 - 5 * PowerSeries.X ^ 2 : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 -
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * PowerSeries.X ^ 2 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
  rw [e, e2] at H
  have h0 : a 0 = 6 := rfl
  have h1 : a 1 = 102 := rfl
  have hdef : ∀ n : ℕ, a (n + 2) = ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌋ + 1 := fun n => rfl
  have hd := hdef 270
  simp only [Nat.reduceAdd] at hd
  have hlt := Int.lt_floor_add_one ((a 271 : ℚ) ^ 2 / (a 270 : ℚ))
  have hfl : ⌊(a 271 : ℚ) ^ 2 / (a 270 : ℚ)⌋ = a 272 - 1 := by omega
  rw [hfl] at hlt
  have r : ∀ n : ℕ, 3 ≤ n → a n = 17 * a (n - 1) + a (n - 2) - 14 * a (n - 3) := by
    intro n hn
    have h := PowerSeries.ext_iff.mp H n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C] at h
    rw [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega),
      if_neg (show ¬ (n = 0) by omega), if_pos (show 2 ≤ n by omega),
      if_neg (show ¬ (n - 2 = 0) by omega)] at h
    have h' : ((a n : ℤ) : ℚ) = ((17 * a (n - 1) + a (n - 2) - 14 * a (n - 3) : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have h2 : a 2 = 1735 := by
    have hq : ∀ n : ℕ, n = 2 → (a n : ℚ) = 1735 := by
      intro n hn
      have h := PowerSeries.ext_iff.mp H n
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C] at h
      rw [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_neg (show ¬ (3 ≤ n) by omega),
        if_neg (show ¬ (n = 0) by omega), if_pos (show 2 ≤ n by omega),
        if_pos (show n - 2 = 0 by omega)] at h
      subst hn
      rw [show 2 - 1 = 1 from rfl, show 2 - 2 = 0 from rfl, h0, h1] at h
      push_cast at h
      linarith
    exact_mod_cast hq 2 rfl
  have h3 : a 3 = 29513 := by
    have e := r 3 (by norm_num)
    simp only [Nat.reduceSub, h2, h1, h0, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h4 : a 4 = 502028 := by
    have e := r 4 (by norm_num)
    simp only [Nat.reduceSub, h3, h2, h1, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h5 : a 5 = 8539699 := by
    have e := r 5 (by norm_num)
    simp only [Nat.reduceSub, h4, h3, h2, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h6 : a 6 = 145263729 := by
    have e := r 6 (by norm_num)
    simp only [Nat.reduceSub, h5, h4, h3, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h7 : a 7 = 2470994700 := by
    have e := r 7 (by norm_num)
    simp only [Nat.reduceSub, h6, h5, h4, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h8 : a 8 = 42032617843 := by
    have e := r 8 (by norm_num)
    simp only [Nat.reduceSub, h7, h6, h5, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h9 : a 9 = 714991805825 := by
    have e := r 9 (by norm_num)
    simp only [Nat.reduceSub, h8, h7, h6, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h10 : a 10 = 12162299391068 := by
    have e := r 10 (by norm_num)
    simp only [Nat.reduceSub, h9, h8, h7, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h11 : a 11 = 206885624804179 := by
    have e := r 11 (by norm_num)
    simp only [Nat.reduceSub, h10, h9, h8, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h12 : a 12 = 3519208035780561 := by
    have e := r 12 (by norm_num)
    simp only [Nat.reduceSub, h11, h10, h9, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h13 : a 13 = 59863150041598764 := by
    have e := r 13 (by norm_num)
    simp only [Nat.reduceSub, h12, h11, h10, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h14 : a 14 = 1018296359995701043 := by
    have e := r 14 (by norm_num)
    simp only [Nat.reduceSub, h13, h12, h11, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h15 : a 15 = 17321632357467588641 := by
    have e := r 15 (by norm_num)
    simp only [Nat.reduceSub, h14, h13, h12, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h16 : a 16 = 294647962336362325244 := by
    have e := r 16 (by norm_num)
    simp only [Nat.reduceSub, h15, h14, h13, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h17 : a 17 = 5012080843035687303187 := by
    have e := r 17 (by norm_num)
    simp only [Nat.reduceSub, h16, h15, h14, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h18 : a 18 = 85257519440938500238449 := by
    have e := r 18 (by norm_num)
    simp only [Nat.reduceSub, h17, h16, h15, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h19 : a 19 = 1450264839866281118803404 := by
    have e := r 19 (by norm_num)
    simp only [Nat.reduceSub, h18, h17, h16, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h20 : a 20 = 24669590665365217897651699 := by
    have e := r 20 (by norm_num)
    simp only [Nat.reduceSub, h19, h18, h17, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h21 : a 21 = 419639700878901846375544001 := by
    have e := r 21 (by norm_num)
    simp only [Nat.reduceSub, h20, h19, h18, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h22 : a 22 = 7138240797848568670618652060 := by
    have e := r 22 (by norm_num)
    simp only [Nat.reduceSub, h21, h20, h19, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h23 : a 23 = 121424358994989456196325505235 := by
    have e := r 23 (by norm_num)
    simp only [Nat.reduceSub, h22, h21, h20, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h24 : a 24 = 2065477387900364698158894625041 := by
    have e := r 24 (by norm_num)
    simp only [Nat.reduceSub, h23, h22, h21, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h25 : a 25 = 35134604582131309363508873002092 := by
    have e := r 25 (by norm_num)
    simp only [Nat.reduceSub, h24, h23, h22, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h26 : a 26 = 597653814258202771491061178587315 := by
    have e := r 26 (by norm_num)
    simp only [Nat.reduceSub, h25, h24, h23, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h27 : a 27 = 10166332763540973318937324384235873 := by
    have e := r 27 (by norm_num)
    simp only [Nat.reduceSub, h26, h25, h24, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h28 : a 28 = 172933426330304910862336451488567868 := by
    have e := r 28 (by norm_num)
    simp only [Nat.reduceSub, h27, h26, h25, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h29 : a 29 = 2941667426979109619177782143189667219 := by
    have e := r 29 (by norm_num)
    simp only [Nat.reduceSub, h28, h27, h26, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h30 : a 30 = 50038951026285594810419510344333608369 := by
    have e := r 30 (by norm_num)
    simp only [Nat.reduceSub, h29, h28, h27, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h31 : a 31 = 851182766905209952644236747676021059340 := by
    have e := r 31 (by norm_num)
    simp only [Nat.reduceSub, h30, h29, h28, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h32 : a 32 = 14478962644437147255093955270832036276083 := by
    have e := r 32 (by norm_num)
    simp only [Nat.reduceSub, h31, h30, h29, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h33 : a 33 = 246293002407968714961895603206999967235585 := by
    have e := r 33 (by norm_num)
    simp only [Nat.reduceSub, h32, h31, h30, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h34 : a 34 = 4189543444843232362270299895322367184450268 := by
    have e := r 34 (by norm_num)
    simp only [Nat.reduceSub, h33, h32, h31, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h35 : a 35 = 71265826087720798811985678449895593595024979 := by
    have e := r 35 (by norm_num)
    simp only [Nat.reduceSub, h34, h33, h32, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h36 : a 36 = 1212260484902385250156560295098649458758576721 := by
    have e := r 36 (by norm_num)
    simp only [Nat.reduceSub, h35, h34, h33, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h37 : a 37 = 20621040461200464798401726496592423251908525484 := by
    have e := r 37 (by norm_num)
    simp only [Nat.reduceSub, h36, h35, h34, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h38 : a 38 = 350772226760082195639618111238871306430873160243 := by
    have e := r 38 (by norm_num)
    simp only [Nat.reduceSub, h37, h36, h35, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h39 : a 39 = 5966777248593964397169717773426023540154132175521 := by
    have e := r 39 (by norm_num)
    simp only [Nat.reduceSub, h38, h37, h36, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h40 : a 40 = 101497290886400670440347196088528977563524400787324 := by
    have e := r 40 (by norm_num)
    simp only [Nat.reduceSub, h39, h38, h37, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h41 : a 41 = 1726509911142764211144117397721074443830036721316627 := by
    have e := r 41 (by norm_num)
    simp only [Nat.reduceSub, h40, h39, h38, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h42 : a 42 = 29368630898833076758329966908518830193111990812712689 := by
    have e := r 42 (by norm_num)
    simp only [Nat.reduceSub, h41, h40, h39, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h43 : a 43 = 499572273118895459716588694097301782040844538926409804 := by
    have e := r 43 (by norm_num)
    simp only [Nat.reduceSub, h42, h41, h40, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h44 : a 44 = 8497926135164057192984320122994554082673848638463246579 := by
    have e := r 44 (by norm_num)
    simp only [Nat.reduceSub, h43, h42, h41, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h45 : a 45 = 144553155738324204665833411248285457564792703521423624001 := by
    have e := r 45 (by norm_num)
    simp only [Nat.reduceSub, h44, h43, h42, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h46 : a 46 = 2458907561863011000076120069626485107735577984957695117340 := by
    have e := r 46 (by norm_num)
    simp only [Nat.reduceSub, h45, h44, h43, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h47 : a 47 = 41827010741517214405258094113176608531912184566863755166675 := by
    have e := r 47 (by norm_num)
    simp only [Nat.reduceSub, h46, h45, h44, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h48 : a 48 = 711494345987319117024142052236152833744335617772341602214801 := by
    have e := r 48 (by norm_num)
    simp only [Nat.reduceSub, h47, h46, h45, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h49 : a 49 = 12102806186659860049814607301153003990677319594907263261175532 := by
    have e := r 49 (by norm_num)
    simp only [Nat.reduceSub, h48, h47, h46, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h50 : a 50 = 205873621368823698962198852854252748155811998147259724469865395 := by
    have e := r 50 (by norm_num)
    simp only [Nat.reduceSub, h49, h48, h47, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h51 : a 51 = 3501993448612840274768857117092143582967060589449509796817880033 := by
    have e := r 51 (by norm_num)
    simp only [Nat.reduceSub, h50, h49, h48, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h52 : a 52 = 59570322961173870329335365341204551602726359544460224584717368508 := by
    have e := r 52 (by norm_num)
    simp only [Nat.reduceSub, h51, h50, h49, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h53 : a 53 = 1013315253089405104087999283977609982355133804871211691594435029139 := by
    have e := r 53 (by norm_num)
    simp only [Nat.reduceSub, h52, h51, h50, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h54 : a 54 = 17236901717200480875978559193321284241478462194102765844534662543409 := by
    have e := r 54 (by norm_num)
    simp only [Nat.reduceSub, h53, h52, h51, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h55 : a 55 = 293206659924041145811112810455662578365050822070995787904497655107980 := by
    have e := r 55 (by norm_num)
    simp only [Nat.reduceSub, h54, h53, h52, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h56 : a 56 = 4987563706882648288207664346963898576694370564132834196538672708971123 := by
    have e := r 56 (by norm_num)
    simp only [Nat.reduceSub, h55, h54, h53, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h57 : a 57 = 84840473052888255313077706880135440402788651941611738407238448432009345 := by
    have e := r 57 (by norm_num)
    simp only [Nat.reduceSub, h56, h55, h54, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h58 : a 58 = 1443170712367046412569173101962887109326990742062538446088929328881618268 := by
    have e := r 58 (by norm_num)
    simp only [Nat.reduceSub, h57, h56, h55, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h59 : a 59 = 24548916691396320192954113139391721718887910079106905643167495621493924179 := by
    have e := r 59 (by norm_num)
    simp only [Nat.reduceSub, h58, h57, h56, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h60 : a 60 = 417586987843364054118406008575300260164782420959697370042235016616230198481 := by
    have e := r 60 (by norm_num)
    simp only [Nat.reduceSub, h59, h58, h57, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h61 : a 61 = 7103323320055446590429887835492015724989611196005086658115917767493064642604 := by
    have e := r 61 (by norm_num)
    simp only [Nat.reduceSub, h60, h59, h58, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h62 : a 62 = 120830398595106407608725141627988083480923742011938673879008492125297414184243 := by
    have e := r 62 (by norm_num)
    simp only [Nat.reduceSub, h61, h60, h59, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h63 : a 63 = 2055373881607057279181099611391235231258386271505526779420668993664921882996001 := by
    have e := r 63 (by norm_num)
    simp only [Nat.reduceSub, h62, h61, h60, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h64 : a 64 = 34962739859434303901421400105582098794723635800861822710816758535684066520119804 := by
    have e := r 64 (by norm_num)
    simp only [Nat.reduceSub, h63, h62, h61, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h65 : a 65 = 594730325911658733896822749423495081572827262497989371428999445210539888926453267 := by
    have e := r 65 (by norm_num)
    simp only [Nat.reduceSub, h64, h63, h62, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h66 : a 66 = 10116603046015133978238872745745521192295169690465603762091917961203553271907881329 := by
    have e := r 66 (by norm_num)
    simp only [Nat.reduceSub, h65, h64, h63, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h67 : a 67 = 172087503750136856109337759825619205967464581099201187809040170166171368580078758604 := by
    have e := r 67 (by norm_num)
    simp only [Nat.reduceSub, h66, h65, h64, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h68 : a 68 = 2927277942235578465562425271289343091497173466701913945315768818553169260688276431859 := by
    have e := r 68 (by norm_num)
    simp only [Nat.reduceSub, h67, h66, h65, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h69 : a 69 = 49794180079110758894975223153304014464727281139365219805507823234113199054474067761601 := by
    have e := r 69 (by norm_num)
    simp only [Nat.reduceSub, h68, h67, h66, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h70 : a 70 = 847019114234616563694610490239898920108316448700521834009622201416151154026626325758620 := by
    have e := r 70 (by norm_num)
    simp only [Nat.reduceSub, h69, h68, h67, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h71 : a 71 = 14408137230876294243185479603433534853025146480514409602734664483848938447857485735612115 := by
    have e := r 71 (by norm_num)
    simp only [Nat.reduceSub, h70, h69, h68, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h72 : a 72 = 245088233518024068073318110624463735219029624681494372003221808901570519980841246882502161 := by
    have e := r 72 (by norm_num)
    simp only [Nat.reduceSub, h71, h70, h69, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h73 : a 73 = 4169049839438000819597868813355958448695012335784111427981370704990721661965785914177528172 := by
    have e := r 73 (by norm_num)
    simp only [Nat.reduceSub, h72, h71, h70, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h74 : a 74 = 70917221582731769881832491223227687875091887282284186913248238490969953635129196987601911475 := by
    have e := r 74 (by norm_num)
    simp only [Nat.reduceSub, h73, h72, h71, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h75 : a 75 = 1206330581476625751857723766059484160032190681389074367745156319726857946179430357247054992993 := by
    have e := r 75 (by norm_num)
    simp only [Nat.reduceSub, h74, h73, h72, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h76 : a 76 = 20520170408933237539988766350847474990140603298195570878589166483977684935417924267389051397948 := by
    have e := r 76 (by norm_num)
    simp only [Nat.reduceSub, h75, h74, h73, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h77 : a 77 = 349056386431183419153321096853341371362171160328761800686975511208473922497392334145034501997459 := by
    have e := r 77 (by norm_num)
    simp only [Nat.reduceSub, h76, h75, h74, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h78 : a 78 = 5937590111598378602620439280132818009906599659347699141408740668551858356144575579731516815452849 := by
    have e := r 78 (by norm_num)
    simp only [Nat.reduceSub, h77, h76, h75, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h79 : a 79 = 101000805897878554338140946130199382889912396923064909212335318545814378387859326249837373645124620 := by
    have e := r 79 (by norm_num)
    simp only [Nat.reduceSub, h78, h77, h76, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h80 : a 80 = 1718064500965497234482870028137575547939346951106848490541491498790477656034789629148936385754606963 := by
    have e := r 80 (by norm_num)
    simp only [Nat.reduceSub, h79, h78, h77, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h81 : a 81 = 29224971060748954240110245274547124245720118170508621460437968428624208513993258963665514696057103105 := by
    have e := r 81 (by norm_num)
    simp only [Nat.reduceSub, h80, h79, h78, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h82 : a 82 = 497128561251127419555623066449615896364722582292830504589014260325760621096490161443964962987693615068 := by
    have e := r 82 (by norm_num)
    simp only [Nat.reduceSub, h81, h80, h79, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h83 : a 83 = 8456357609316398125402942194524091304774853159833131320606099512983488079969838948702984776086284061779 := by
    have e := r 83 (by norm_num)
    simp only [Nat.reduceSub, h82, h81, h80, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h84 : a 84 = 143846058324779410192044096939515508338097144645068942254446574423044319061387846663903388950709723221841 := by
    have e := r 84 (by norm_num)
    simp only [Nat.reduceSub, h83, h82, h81, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h85 : a 85 = 2446879549273050587516373867235993110503320195973905522581951665060176263428212369974845087456323868222124 := by
    have e := r 85 (by norm_num)
    simp only [Nat.reduceSub, h84, h83, h82, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h86 : a 86 = 41622409389436209824214758649228061108627692531963798987659139487264271964221420390954428088843007506133043 := by
    have e := r 86 (by norm_num)
    simp only [Nat.reduceSub, h85, h84, h83, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h87 : a 87 = 708013994353141705856478653546959814840440733214327523121225070906630179188332929162905475152477515347378081 := by
    have e := r 87 (by norm_num)
    simp only [Nat.reduceSub, h86, h85, h84, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h88 : a 88 = 12043603999703022501159122634806241009849073674431897014732338021589134850477886242980699674456572234256450684 := by
    have e := r 88 (by norm_num)
    simp only [Nat.reduceSub, h87, h86, h85, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h89 : a 89 = 204866568257852417288022556824163864126753905503109083587743743485100222829813299174361437947670403392621177107 := by
    have e := r 89 (by norm_num)
    simp only [Nat.reduceSub, h88, h87, h86, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h90 : a 90 = 3484863068462250132515551887495934493756899296962285732682678826275600100448667311198844468132718744693953168369 := by
    have e := r 90 (by norm_num)
    simp only [Nat.reduceSub, h89, h88, h87, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h91 : a 91 = 59278928276120262355036176927367762883856154922419919980987031057868054042550467182152987600761497051910234729804 := by
    have e := r 91 (by norm_num)
    simp only [Nat.reduceSub, h90, h89, h88, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h92 : a 92 = 1008358511806896776326098243857209609421536978301057398239233794401241115704189223219358573549810782979671247095539 := by
    have e := r 92 (by norm_num)
    simp only [Nat.reduceSub, h91, h90, h89, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h93 : a 93 = 17152585546034893958043488596074988040137388195882923689790404032311108619607485919554464915393686745280606090996801 := by
    have e := r 93 (by norm_num)
    simp only [Nat.reduceSub, h92, h91, h90, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h94 : a 94 = 291772407798534410390094897900148857611383150139396881244942283908879934892435743315095120308831824494023231507823900 := by
    have e := r 94 (by norm_num)
    simp only [Nat.reduceSub, h93, h92, h91, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h95 : a 95 = 4963166498955823315721091377484604632901749422869415101278459957361652626171156473151100490135837352181960144264665555 := by
    have e := r 95 (by norm_num)
    simp only [Nat.reduceSub, h94, h93, h92, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h96 : a 96 = 84425466692403042262236039474793377784379199904177092671321695902604619059127590984010040943802555197153417198733183121 := by
    have e := r 96 (by norm_num)
    simp only [Nat.reduceSub, h95, h94, h93, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h97 : a 97 = 1436111286560628060028272433878369942960788783691928434176318098326915857542846102794910464850455630160873727281619244012 := by
    have e := r 97 (by norm_num)
    simp only [Nat.reduceSub, h96, h95, h94, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h98 : a 98 = 24428833007237698536322772136122297943257164030746788662250830928057111060521115147873372536539646545001459338966555013555 := by
    have e := r 98 (by norm_num)
    simp only [Nat.reduceSub, h97, h96, h95, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h99 : a 99 = 415544315875907860585844094195310327689351268507728856395041940132661339219574017342866103012811211122425534648930789910753 := by
    have e := r 99 (by norm_num)
    simp only [Nat.reduceSub, h98, h97, h96, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h100 : a 100 = 7068576644885822535655276559382100689460777685690450349299495359806723055787679564537468377246423856803983316188847314080188 := by
    have e := r 100 (by norm_num)
    simp only [Nat.reduceSub, h99, h98, h97, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h101 : a 101 = 120239343616833563187217026793785309877316971628814929753214951423854153732762831002409601300690461725160121479113803359084179 := by
    have e := r 101 (by norm_num)
    simp only [Nat.reduceSub, h100, h99, h98, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h102 : a 102 = 2045319797708793686670142914734998024016198377616436052164423082403470077763681770362700565046804916228812090976038473359760689 := by
    have e := r 102 (by norm_num)
    simp only [Nat.reduceSub, h101, h100, h99, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h103 : a 103 = 34791715831637924721080472705457402308500238503508561511658214417245551352934325413264794649814924103619709901645123988077893260 := by
    have e := r 103 (by norm_num)
    simp only [Nat.reduceSub, h102, h101, h100, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h104 : a 104 = 591821138124917844060417140532397842930237815334458572733809058855643884925388534161830475193690848213611638718235553023656767603 := by
    have e := r 104 (by norm_num)
    simp only [Nat.reduceSub, h103, h102, h101, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h105 : a 105 = 10067116586787318162134789860949930759786316321902674193256110291809543013995847861379305065031904074907814198837984986763206292865 := by
    have e := r 105 (by norm_num)
    simp only [Nat.reduceSub, h104, h103, h102, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h106 : a 106 = 171245719091866395654256718158804817126978611948630799996924469017776437403913721621824309455638651184195777080340948592165073240668 := by
    have e := r 106 (by norm_num)
    simp only [Nat.reduceSub, h105, h104, h103, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h107 : a 107 = 2912958845214767194467653158593178252117399390033943854122698756770029964491573675954126939158177302331245461622578813311238256637779 := by
    have e := r 107 (by norm_num)
    simp only [Nat.reduceSub, h106, h105, h104, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h108 : a 108 = 49550606455527886247334473356189536072485759814019038881377217790022952231564724342782672004234206133766659225880448985068530547982801 := by
    have e := r 108 (by norm_num)
    simp only [Nat.reduceSub, h107, h106, h105, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h109 : a 109 = 842875828521902703859994106159592024044597615661076773637578458620911347777437095400554010678760740459785711422465438279185946546976044 := by
    have e := r 109 (by norm_num)
    simp only [Nat.reduceSub, h108, h107, h106, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h110 : a 110 = 14337658267494867111144687133848949449301001634591848976762493231750735444945113314688843076394952311717486316945076796344872286253646643 := by
    have e := r 110 (by norm_num)
    simp only [Nat.reduceSub, h109, h108, h107, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h111 : a 111 = 243889357885557253185856992754605079157146824766326242834260682349323092580602457304311928901333671153784319870326444690351055385187209761 := by
    have e := r 111 (by norm_num)
    simp only [Nat.reduceSub, h110, h109, h108, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h112 : a 112 = 4148656480722661533416673646475901006784172656042882902328267994749550550446302768152383878249564711559613924152580120396404210582778547964 := by
    have e := r 112 (by norm_num)
    simp only [Nat.reduceSub, h111, h110, h109, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h113 : a 113 = 70570322314425875181713283362971036902197867954611049696740141687847172153938517929489194056074404435303176222026957416280394423284871472147 := by
    have e := r 113 (by norm_num)
    simp only [Nat.reduceSub, h112, h111, h110, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h114 : a 114 = 1200429684815564738077940492918419057235947872337702160347231027135260953871272673167208315826895768715560629220426285971498194631032972637809 := by
    have e := r 114 (by norm_num)
    simp only [Nat.reduceSub, h113, h112, h111, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h115 : a 115 = 20419793773448909161038868231925432395818333280510947414967071851060789680259325723017897188817808566637999278031137697246200044202686506643404 := by
    have e := r 115 (by norm_num)
    simp only [Nat.reduceSub, h114, h113, h112, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h116 : a 116 = 347348939321045058223194714468569175269516843489659253519033090511538825108124670713458611808944599739467303888641389735328973424150715384965619 := by
    have e := r 116 (by norm_num)
    simp only [Nat.reduceSub, h115, h114, h113, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h117 : a 117 = 5908545746643796992622257847296743545176301402391990426993668376167327163164180910427473381519299463375564316575848795194237773529930386434129601 := by
    have e := r 117 (by norm_num)
    simp only [Nat.reduceSub, h116, h115, h114, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h118 : a 118 = 100506749519437309204547033963266253389725184018226343248601856479441249543375569587858255536993586157191128695785634980275924322814129673672161180 := by
    have e := r 118 (by norm_num)
    simp only [Nat.reduceSub, h117, h116, h115, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h119 : a 119 = 1709660402426583422654797109220263082716731193903384596103958765259507025849035118514029396945085039739272209890490664003590345633432024823471350995 := by
    have e := r 119 (by norm_num)
    simp only [Nat.reduceSub, h118, h117, h116, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h120 : a 120 = 29082013950318342336439386280845584249941687260742276611037989508624718108692674051580373376262169069237560796402065039908592471261739526262607313681 := by
    have e := r 120 (by norm_num)
    simp only [Nat.reduceSub, h119, h118, h117, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h121 : a 121 = 494696803064566280813260705408109467784269262050266918178269354421167537380017236021150361215884049010577129946984597452725799416563606155856385427052 := by
    have e := r 121 (by norm_num)
    simp only [Nat.reduceSub, h120, h119, h118, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h122 : a 122 = 8414992420413972948244704218689622853424484905400632501296161591954839755207099194751940102489059811692698958956673352440196917713974995828292560659635 := by
    have e := r 122 (by norm_num)
    simp only [Nat.reduceSub, h121, h120, h119, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h123 : a 123 = 143142419754797649608263081015199859796501329032210627567658484564532697322379006110082006876262230480817133581060802678377353105956474181869153414249313 := by
    have e := r 123 (by norm_num)
    simp only [Nat.reduceSub, h122, h121, h120, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h124 : a 124 = 2434910373009070088357331431601373706844967308784277564296994628227114348712329961761849951941924601299435890017732534520517038527142145601421911206919228 := by
    have e := r 124 (by norm_num)
    simp only [Nat.reduceSub, h123, h122, h121, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h125 : a 125 = 41418808867023193530407471559176898156213002789689320365598420902138108868859088967335004028454133615207529478457120462593004251219377299464445548082641299 := by
    have e := r 125 (by norm_num)
    simp only [Nat.reduceSub, h124, h123, h122, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h126 : a 126 = 704550667235836193010768664803395844325314996127051774993522931180671507356803536320915770339394524833095997153653929161104306365773165597950828080812330929 := by
    have e := r 126 (by norm_num)
    simp only [Nat.reduceSub, h125, h124, h123, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h127 : a 127 = 11984691406654111493476472133174487019790738394626589609355330326178374133052546586958237200470974111359647378630325660718078973929983202426208616164995397900 := by
    have e := r 127 (by norm_num)
    simp only [Nat.reduceSub, h126, h125, h124, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h128 : a 128 = 203864441256217406872685090326941198606580885665723424648915760583583098245086068269068258121947596547334196021170790474892144803658416324650995065212577117043 := by
    have e := r 128 (by norm_num)
    simp only [Nat.reduceSub, h127, h126, h125, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h129 : a 129 = 3467816483421048321626972246383927321511111384766146083791013939210561643196520457652625804488828592068377635778382608725629080347002236403121813131647433754625 := by
    have e := r 129 (by norm_num)
    simp only [Nat.reduceSub, h128, h127, h126, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h130 : a 130 = 58988958979720881313622542668989262846018404089165434594565178102596633794723198196146291613625440024150718940952850579560533405067676670343754897676909015375068 := by
    have e := r 130 (by norm_num)
    simp only [Nat.reduceSub, h129, h128, h127, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h131 : a 131 = 1003426016961088986956992606354624218923331848501258406246314221035183172778059684836372627622414042650967920887680451394606206939246287803701841142726124615492179 := by
    have e := r 131 (by norm_num)
    simp only [Nat.reduceSub, h130, h129, h128, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h132 : a 132 = 17068681816550338983079719239248226002041504269223832295608832740551762708016986554007344199931820564801648087130623167765707244247396538023631348940177963406177361 := by
    have e := r 132 (by norm_num)
    simp only [Nat.reduceSub, h131, h130, h129, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h133 : a 133 = 290345171472600759360921504076208616573784646768058091347272558316978796335940706328215175943872607483940875336934934395297781891474039960820622204558274776305256364 := by
    have e := r 133 (by norm_num)
    simp only [Nat.reduceSub, h132, h131, h130, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h134 : a 134 = 4938888632613308002301347392045829968691453853447193767511793925034698736000116158545956118459052351194682977922596981568303512502156627842722383050432683415978645043 := by
    have e := r 134 (by norm_num)
    simp only [Nat.reduceSub, h133, h132, h131, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h135 : a 135 = 84012490380467132052720711099505842920299919095601218486909245625539132630425677589853366370948717089886328426801254896707737593008673161754770295176751401360255739041 := by
    have e := r 135 (by norm_num)
    simp only [Nat.reduceSub, h134, h133, h132, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h136 : a 136 = 1429086392699938142267500535026578238981757093423915094766107153742762250304533465297458171961373026374487093978826841144065673647168963818222328690191390659672052619644 := by
    have e := r 136 (by norm_num)
    simp only [Nat.reduceSub, h135, h134, h133, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h137 : a 137 = 24309336725422829238568010943062694286048490153353897116765565744302011605503492961426998904055863432539441364375941196603867940419850865281736244665724335047961449242387 := by
    have e := r 137 (by norm_num)
    simp only [Nat.reduceSub, h136, h135, h134, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h138 : a 138 = 413511635859561495349185596611699299300921890833101749020963995368119411687037954323298492411717769340286581690394609614855912334482512249343171703875030566855973109393649 := by
    have e := r 138 (by norm_num)
    simp only [Nat.reduceSub, h137, h136, h135, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h139 : a 139 = 7033999936840169116182978145851578687055976035008148819146427986849933338780885247943336955495798719848168510785380728873137458195562193610660542608878564502364095572259404 := by
    have e := r 139 (by norm_num)
    simp only [Nat.reduceSub, h138, h137, h136, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h140 : a 140 = 119651179847986516861119861922885659259247835623824677114875521851396758008485038267900048751183513918703599085940603823705738550493161891516628088629490486416374137548410099 := by
    have e := r 140 (by norm_num)
    simp only [Nat.reduceSub, h139, h138, h137, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h141 : a 141 = 2035314894450577094820332032482343995904056275168364235285736803525441147719408004441717986831851486567045340828110121197262710043896559177902533645455966405644740810363720001 := by
    have e := r 141 (by norm_num)
    simp only [Nat.reduceSub, h140, h139, h138, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h142 : a 142 = 34621528386392034761180202720080811488009420848995902593504351189967997202495488720305899107515717603480600034012817333972947884881996797205310452464856619479343870575720018460 := by
    have e := r 142 (by norm_num)
    simp only [Nat.reduceSub, h141, h140, h139, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h143 : a 143 = 588926180945243356798828100206935740062434741009365162845251449727061838978023925713891402132082481550875395531842836345205496413330937845186947432307205630744661302671926292435 := by
    have e := r 143 (by norm_num)
    simp only [Nat.reduceSub, h142, h141, h140, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h144 : a 144 = 10017872195933221021013773257783235576606743230155846571668778681300663083760830513794275683537271983156423689303747493505704708970893388336892781330650968812459559644653374909841 := by
    have e := r 144 (by norm_num)
    simp only [Nat.reduceSub, h143, h142, h141, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h145 : a 145 = 170408052114400512227376450644440809181544937761772814244905428115178782302077205818132295434760486148761349713219370783266564278530170584411489883718865682769846361073719219501292 := by
    have e := r 145 (by norm_num)
    simp only [Nat.reduceSub, h144, h143, h142, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h146 : a 146 = 2898709791607508521891229840810379891301996598806162576455227536343161096473380994462048818444616381770387113276587251100204420494197160193499603540499066697069422439660473138337715 := by
    have e := r 146 (by norm_num)
    simp only [Nat.reduceSub, h145, h144, h143, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h147 : a 147 = 49308224298698980290084090918811933663242992712244354761980410644410708139176902484479842349423717168481152343764950174577661846754289386437188251133573885969575594000276615322504673 := by
    have e := r 147 (by norm_num)
    simp only [Nat.reduceSub, h146, h145, h144, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h148 : a 148 = 838752810139888566282137505151591080837891243578295374130693532497712696510251642349165516622561161439867318061295669027954723915417694341443939014439191008621076671389330864547899068 := by
    have e := r 148 (by norm_num)
    simp only [Nat.reduceSub, h147, h146, h145, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h149 : a 149 = 14267524059594299487779944460724514989429166181159979438913397277596722293462827488497824941474738832301440139799919102134405106521936332948275157047032834098768907093463654688700060819 := by
    have e := r 149 (by norm_num)
    simp only [Nat.reduceSub, h148, h147, h146, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h150 : a 150 = 242696346683061194134480016064604978829848314425326524868990721502620241771429842312029471728801189270205613561847211102868754268933775303052000973298127336284118438944267587957933867569 := by
    have e := r 150 (by norm_num)
    simp only [Nat.reduceSub, h149, h148, h147, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h151 : a 151 = 4128362878329676159845990292486886879965120034001614766973925953367172854656626623800110527098379100165638728238344368484511861543580268764052076556913048876808087295746562017869905222540 := by
    have e := r 151 (by norm_num)
    simp only [Nat.reduceSub, h150, h149, h148, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h152 : a 152 = 70225119941453235718687395765891538728384880565916537851280944366858204658825602862074938883220599548433843831656502607909688729018491235630661450242161498564638837767327330726104521799283 := by
    have e := r 152 (by norm_num)
    simp only [Nat.reduceSub, h151, h150, h149, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h153 : a 153 = 1194557653029471826659648998087738575558890213252628186890584110088919968669891857486705658937645354773758105276533027747509057695092858420242568717047484741767690671195091438130235701664385 := by
    have e := r 153 (by norm_num)
    simp only [Nat.reduceSub, h152, h151, h150, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h154 : a 154 = 20319908141145858822694876499162630906910006825384573108253575852531357252081794407402869593443814323300002691337381153156780503483986960617057600568252619424340067025943429910689932776978268 := by
    have e := r 154 (by norm_num)
    simp only [Nat.reduceSub, h153, h152, h151, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h155 : a 155 = 345649844373328726512410925943129982450831617916867539497283440381985978388836838343266439603117400457195730044368821594902041974716612311611392518073951753975643886383490817289693629605104979 := by
    have e := r 155 (by norm_num)
    simp only [Nat.reduceSub, h154, h153, h152, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h156 : a 156 = 5879643455345321603960445531559143992513223048426595949945603884805048110300929560238118463621312587128794799971735885878026367265935096240127334445786767650625538466148556043701658336240461521 := by
    have e := r 156 (by norm_num)
    simp only [Nat.reduceSub, h155, h154, h153, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h157 : a 157 = 100015109871267753970322256691460301022478883345613614665056999420132364851975494240687640146857217981120507291885155545377155358446837430945137271688493465142669036872545735541468226286815255084 := by
    have e := r 157 (by norm_num)
    simp only [Nat.reduceSub, h156, h155, h154, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h158 : a 158 = 1701297413445670536928265056323180441620342597273021899702952625861707446896440615915122270805750374659776678541398216654961038873216138849944901457897140350520340150890057188806605794397628328243 := by
    have e := r 158 (by norm_num)
    simp only [Nat.reduceSub, h157, h156, h155, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h159 : a 159 = 28939756130072832379295381976743699792673117914309013566316013184681888288547252950954432585353915210977520915296050536277422447061398106532646679373698864676879694063477438160641943514339130373921 := by
    have e := r 159 (by norm_num)
    simp only [Nat.reduceSub, h158, h157, h156, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h160 : a 160 = 492276940086486072429365247067285632702748642773687661921764378773571955244272083862770849259766307909541945136487865155735862463898728225871706529007138931345477772713790865622139090370147431113724 := by
    have e := r 160 (by norm_num)
    simp only [Nat.reduceSub, h159, h158, h157, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h161 : a 161 = 8373829573812096676161508871332074929556715248705176959640469115573341223184622509995247158210100644427953714736010183150617629789114752002452429052084500732642717068085461353093713998685278662711827 := by
    have e := r 161 (by norm_num)
    simp only [Nat.reduceSub, h160, h159, h158, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h162 : a 162 = 142442223109071109913864880712038147638069484219961369785881315158934826313343193212468610482636522450231069802834516271208351654619989938776105946903211867280795352213277949733966289858819136871979889 := by
    have e := r 162 (by norm_num)
    simp only [Nat.reduceSub, h161, h160, h159, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h163 : a 163 = 2422999745266810160197853367517038585918899465989216836052718125514635381176599097947882833473394253987622553131011956681512293683834361516034049635000586299467327015875817534711810694333428541450777804 := by
    have e := r 163 (by norm_num)
    simp only [Nat.reduceSub, h162, h161, h160, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h164 : a 164 = 41216204278611474479811111004303045059245566392554775105247122881289709529190943143186543319315397431217823121023733637292808697462756529183320615735183995947968356583148979580891436097545510440257236979 := by
    have e := r 164 (by norm_num)
    simp only [Nat.reduceSub, h163, h162, h161, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h165 : a 165 = 701104281358134880778192632110700270526160555360340934448251468695214609809035827827144558715078239270387380633294800562862343227386015498489619033876483551272998253998422579113590696294583638109616088001 := by
    have e := r 165 (by norm_num)
    simp only [Nat.reduceSub, h164, h163, h162, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h166 : a 166 = 11926066990933169105466315909740969103801110414994501625020784036942733180946327628833373681807017945471976578143201175812411471451451338942282367496745396159396396096334071379025967923384799358723419843740 := by
    have e := r 166 (by norm_num)
    simp only [Nat.reduceSub, h165, h164, h163, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h167 : a 167 = 202867216267321449030988207543646932404315599680771101708328120376383622752487932313989885542963967748256939685373382518451758036137580186108723377858255642317740174899513550308422565288470535590244152113875 := by
    have e := r 167 (by norm_num)
    simp only [Nat.reduceSub, h166, h165, h164, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h168 : a 168 = 3450853283596383914301371147302189016189800057213058457584323309873731315435914675377081404090183374316054527900624576781612225280606910285811725124612820545843157393832086510514619308079259733459339380547601 := by
    have e := r 168 (by norm_num)
    simp only [Nat.reduceSub, h167, h166, h165, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h169 : a 169 = 58700408099532783624677769288944486640177701026492841857891533411712617720629788826920706523530783079884576241901986371344485827206134736299716097351321769375419866324696307229750587251708498813376885743610732 := by
    have e := r 169 (by norm_num)
    simp only [Nat.reduceSub, h168, h167, h166, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h170 : a 170 = 998517649947911205247389614153747404845550299112060574617823797623718861847607493680633233906512000183878253484639165534379546675278971304775463252807067320935532522465076119711956686673085152062602978892335795 := by
    have e := r 170 (by norm_num)
    simp only [Nat.reduceSub, h169, h168, h167, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h171 : a 171 = 16985188511243673898030082013840419722787875585130539791954715566676701030713854375942406543276972218965390122090159056380854208153020150173481227243326886737637668544717341131185809590381046447609196775585652833 := by
    have e := r 171 (by norm_num)
    simp only [Nat.reduceSub, h170, h169, h168, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h172 : a 172 = 288924916627696908501013295079395659879276947431960337251837506963363659735894314841124654578285608759477126261630715314810078283695735637945760301026445637089520019654114127048654211501626955778031671763437883708 := by
    have e := r 172 (by norm_num)
    simp only [Nat.reduceSub, h171, h170, h169, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h173 : a 173 = 4914729524082820361541792643765414174002658277740887425028542800777126852475050701763532669099441153127502241021027371090670871377526620396984549859153603774766380547350146435282340011504616102545271175049536974739 := by
    have e := r 173 (by norm_num)
    simp only [Nat.reduceSub, h172, h171, h170, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h174 : a 174 = 83601534186878231620139067090897670741805437410835219005649699102241046337381762283557986337662907600861499761909833797066882932787506000284254370725231133393791061964980560751011833072814766048781112892747367314609 := by
    have e := r 174 (by norm_num)
    simp only [Nat.reduceSub, h173, h172, h171, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h175 : a 175 = 1422095861868225001184891747057914277546385216997892165799547702441387823351662489114473555245272871845140318425825371906820339632793388326298068207973712632549961153676862081423802343288332861550931746947066650951180 := by
    have e := r 175 (by norm_num)
    simp only [Nat.reduceSub, h174, h173, h172, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h176 : a 176 = 24190424972609543766701713670062724590594316910486629613647561041394954267380993367404918968139909552824461881626646773017743264490989734861793630208250195433896401346808733894861698908813408786978987014542186915838323 := by
    have e := r 176 (by norm_num)
    simp only [Nat.reduceSub, h175, h174, h173, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h177 : a 177 = 411488898917614173792432077198851664927264496571518902531728989618724235720105205063028284204896454563448931309412082840049519474920593796972810220558073799141275709181915610443558518130096875515510775413665781077798145 := by
    have e := r 177 (by norm_num)
    simp only [Nat.reduceSub, h176, h175, h174, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h178 : a 178 = 6999592364505895348221458541591730228468441365588337482331846716725527531982246204591283120677945816925624329683670499847164089583281976846831394424783872803979884001287898042295423274314423632488949124589601532125090268 := by
    have e := r 178 (by norm_num)
    simp only [Nat.reduceSub, h177, h176, h175, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h179 : a 179 = 119065893145901301480823403292877387404622447274826443287582057319373162919674956775971172470176016608559520069589037525419590636687840343905041404618968408730724754112220860054937690396751910904809940075233301210382596179 := by
    have e := r 179 (by norm_num)
    simp only [Nat.reduceSub, h178, h177, h176, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h180 : a 180 = 2025358931259981422089125265439723392798068342085636608735782615291407157866375038525218819134801677798549180474365539272219511640627679510074915929859433788038322843980495700430026340765275552757040779547764401173540051281 := by
    have e := r 180 (by norm_num)
    simp only [Nat.reduceSub, h179, h178, h177, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h181 : a 181 = 34452173431462502942120852496185890841773226083612412067043240663239137461200299164840413134072313297746936847518231818155290991273192444339322972690282368586126494725762617194773249557566034376919657904642973699710812204204 := by
    have e := r 181 (by norm_num)
    simp only [Nat.reduceSub, h180, h179, h178, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h182 : a 182 = 586045384762079913217412090054499584279278197501649071542444725087885519717396011445948645683781663506976642307310059922556292094371269468463894871999994142029958586624373895970806141153833333207723885997425051079311991176243 := by
    have e := r 182 (by norm_num)
    simp only [Nat.reduceSub, h181, h180, h179, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h183 : a 183 = 9968868689349181287728878629706522696090329626822447715766302610543213272446803243206614326290473369427170167545148132951801183432615985895084486973672150710062885947524391908892457280402018841169627148947200140431585101482401 := by
    have e := r 183 (by norm_num)
    simp only [Nat.reduceSub, h182, h181, h180, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h184 : a 184 = 169574482675657686763418656860118782946030056688312686470630983735037163226856246957650626408744816557600412374709573074649002336571018335464149651806762603052893248768378359706415754414182229151814510207434825806620307345518204 := by
    have e := r 184 (by norm_num)
    simp only [Nat.reduceSub, h183, h182, h181, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h185 : a 185 = 2884530438788860737480802275990962838598691398563115030714898799954944590852959457363023982235379411559536507545305549563069052815818729916227134039480636484620828694797215272374368996345346247757108166271375288137866442098824467 := by
    have e := r 185 (by norm_num)
    simp only [Nat.reduceSub, h184, h183, h182, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h186 : a 186 = 49067027780435401685908853047890595721378519217485753940603182346421490221912911776724165723842128185897740658299271841785497683637432803108794245505346172731666100657055696503346194290359440177246278556735553922184307631604780529 := by
    have e := r 186 (by norm_num)
    simp only [Nat.reduceSub, h185, h184, h183, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h187 : a 187 = 834649959948731481783243442894089427140789097302184554410380164916829758078196472204266732517829131140014721925386992836871443641940182126069231212505070896480204034381986758793369851370657278052818440487871704403978411876542838604 := by
    have e := r 187 (by norm_num)
    simp only [Nat.reduceSub, h186, h185, h184, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h188 : a 188 = 14197732920765826541676316150383537377374411493774739568487057402733158153279311506846176282775642045804314502284243872374717072857199066727458544981538822502110443083423669582177392501642698319606560252522755274755887179343449494259 := by
    have e := r 188 (by norm_num)
    simp only [Nat.reduceSub, h187, h186, h185, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h189 : a 189 = 241509171224041687066677894056743756502406485222427956663521911458530617500719711323715125219569954115210792891541343017422064714643400257249341376461590207014114411043385589904762195659231496548882894833580413620343480153872717313601 := by
    have e := r 189 (by norm_num)
    simp only [Nat.reduceSub, h188, h187, h186, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h190 : a 190 = 4108168544290192265930235106914510145938313612912819419086614229888918039052419653399143570760215254168427587551531657268833617010807840890201292707853501349191332574339630883340027540789388937757876314256559582958939352028908044085020 := by
    have e := r 190 (by norm_num)
    simp only [Nat.reduceSub, h189, h188, h187, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h191 : a 191 = 69881606163266588636297206285498046714170496143827511727177145015931873067245943458013309360184370286337219378235600102374347514878375908456486897780229569628237221971649179232534746894055845661958288393659774750075730044134501173839315 := by
    have e := r 191 (by norm_num)
    simp only [Nat.reduceSub, h190, h189, h188, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h192 : a 192 = 1188714344922685615464049251443586891695803057264866527387808772740311331537223382481093390940820530764288205917075154595388832463938190681048987775701293922131026504337768279577764054000509524239364418478802604543561541380161209956962961 := by
    have e := r 192 (by norm_num)
    simp only [Nat.reduceSub, h191, h190, h189, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h193 : a 193 = 20220511110228859359802111189329672063499686079065779005452713682382779656653309570489012945363490379720878733742791785022220828763676307713826460986792277226967009139672955099687763279331666312602543134133712217829196782578470357825019372 := by
    have e := r 193 (by norm_num)
    simp only [Nat.reduceSub, h192, h191, h190, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h194 : a 194 = 343959060732527562491191778582051039317192079455369524455903461343024519271702042872382127131077575802010505608249237098539902056238138159097708007982246792805774860771174916465014253346122054999215181661240673461138846624596274276548541875 := by
    have e := r 194 (by norm_num)
    simp only [Nat.reduceSub, h193, h192, h191, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h195 : a 195 = 5850882542734279823093565657563987123972023794018639563372382233695435248634066911046249866700510791583199439191140770295865112130316890342840176767825169640015305271188917779090841373407399467959909529516521924593579727821392876119752749793 := by
    have e := r 195 (by norm_num)
    simp only [Nat.reduceSub, h194, h193, h192, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h196 : a 196 = 99525875131672080524044578400519216737952600972665321195710063442612064830857693196671783679804672167400308669585243247137935716668933805679387142607195038791888426343027355789613688915361269681941241579564241420502385464632176583302795017148 := by
    have e := r 196 (by norm_num)
    simp only [Nat.reduceSub, h195, h194, h193, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h197 : a 197 = 1692975332930904262856974713566241957118725551216953926548060812299298194103411022654253222643544851576160299743624786652261213666714857652665053688978389374002837705051857517372013353387703275290972003838851256644678188773824046952395588455059 := by
    have e := r 197 (by norm_num)
    simp only [Nat.reduceSub, h196, h195, h194, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h198 : a 198 = 28798194179358764631569304789820736668020678638544621118625530521258945271107968141564329070486259997879960612162530645551436456480997077436185537380490262021879915138427960302206568917278613357077026573426804297435721478430141474508351260256049 := by
    have e := r 198 (by norm_num)
    simp only [Nat.reduceSub, h197, h196, h195, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h199 : a 199 = 489868914130186493872198532042911496279138925992858198446442138785504798895306861724494442449392699405191886385132452355566749873810300100788307769160812113202874957089524799673829093302309072570053246369980624933164909925581378641428127882567820 := by
    have e := r 199 (by norm_num)
    simp only [Nat.reduceSub, h198, h197, h196, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h200 : a 200 = 8332868079731496500778946703529388786013720262800096639736469038502650351773876863140810305593152521964075784963003473677054527319922090783700106861468598735234714457789623549514092968109105001193908606809353510568213695570480041721452987025538163 := by
    have e := r 200 (by norm_num)
    simp only [Nat.reduceSub, h199, h198, h197, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h201 : a 201 = 141745451551054604302272322224985030545160093892654876378305658366032935545255701981136369030546177932824160782185916075827773603921751884339583526890800126943886701927575133697182517586315193505867421190101015044428697633925720107263011989673131905 := by
    have e := r 201 (by norm_num)
    simp only [Nat.reduceSub, h200, h199, h198, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h202 : a 202 = 2411147379649837158725197645079674147105827371474032980292682471318065487436586514478316161630586679588302122672731722429771271295756359923145583755236819387196468397827313549206183284629235067584959323389346880516791764733349582564212663021112831068 := by
    have e := r 202 (by norm_num)
    simp only [Nat.reduceSub, h201, h200, h199, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h203 : a 203 = 41014590752482045351619727034730034088340033325272014188397597104234109117042392172028539772472215595626463185229143148750460622249300961306842705869856169326990563462582850740509101054729783872433461198313667034681933706362881903114777941530233725779 := by
    have e := r 203 (by norm_num)
    simp only [Nat.reduceSub, h202, h201, h200, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h204 : a 204 = 697674753850129843676028744724340463221254152586601105913755554026173459379523673611227583127230605314178638020617562426126013019078968175758717414166320496168821633434749724266100345968827148189871655798060272259487663006027381854013755501179662322641 := by
    have e := r 204 (by norm_num)
    simp only [Nat.reduceSub, h203, h202, h201, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h205 : a 205 = 11867729342889591667621955620317402470790179044096854352998144460950730001744832632360201026672564292422427079818309460278875884148451170910281000574123989132776207774283745773575328416539982012154062179237887439118737120102561479265449644179288913575724 := by
    have e := r 205 (by norm_num)
    simp only [Nat.reduceSub, h204, h203, h202, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h206 : a 206 = 201874869312438439558326598111633961989417537435679316908244645030729305961403084933326245479746212558156668510338670383084509594831258660192239929292096149382786485907782267964679556012382304380594860246065755398792471632860492182723050815367667920949043 := by
    have e := r 206 (by norm_num)
    simp only [Nat.reduceSub, h205, h204, h203, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h207 : a 207 = 3433973061100441246347709721091953989805790757314432826310364532226982502914283945068349188018576949306687290823287060098749774814012742839717737754741430041693782965338495805033402375783475576407608483181182885406957927596646545239601120928413128297192481 := by
    have e := r 207 (by norm_num)
    simp only [Nat.reduceSub, h206, h205, h204, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h208 : a 208 = 58413268697219485344122684477990408154096797905163681403242467670436121635479802494242219627422138450677926633388762359617926419054969570542649847751858671010318229987822238512702465346499907355139782203816844383169414921094415900546225811579880804183161084 := by
    have e := r 208 (by norm_num)
    simp only [Nat.reduceSub, h207, h206, h205, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h209 : a 209 = 993633292743457553942616773473366017141599509620997506244716889899210840022611283158119515417478483635017246699287505788240315764420857820822073790526249491125744681955607598769469799482108548352455577904622616823703916983341669963967317206371239448517644307 := by
    have e := r 209 (by norm_num)
    simp only [Nat.reduceSub, h208, h207, h206, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h210 : a 210 = 16902103622480591724919739897429925343704007390859719227995084492505842646979071640951317093092296282955677498449750341918320797566813374124761855958131719999564264861718412476323221423281376571277178087817864769990438592651549753654636202626893167632822419569 := by
    have e := r 210 (by norm_num)
    simp only [Nat.reduceSub, h209, h208, h207, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h211 : a 211 = 287511609113152444082760477447090231145952369983563932842515758715112430135770111944411119023202605355572043747477600645365042904533478643954176527210239468089573792111339108357086399480414511557092526119954887885296788183164365659485135600501436757947934521804 := by
    have e := r 211 (by norm_num)
    simp only [Nat.reduceSub, h210, h209, h208, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h212 : a 212 = 4890688592447663735376651221669336730584911903976752612463336946190828203194754416731726667271691888556790179751778936232088685753934058311854253785464835184646558305207104748164019435397578553364915744036386242184503982868678982585406398970262120700468462269939 := by
    have e := r 212 (by norm_num)
    simp only [Nat.reduceSub, h211, h210, h209, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h213 : a 213 = 83192588230008707661336954887261795696277598634116322275527312661064110087388888193410446023338672562859625614549423011804016209555477082707729824896698593527087165272568062052476891701313310646762779681509070898241998356653585373060229011258180984319052279236801 := by
    have e := r 213 (by norm_num)
    simp only [Nat.reduceSub, h212, h211, h210, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h214 : a 214 = 1415139525975011559760946237620860600331260755504184336236632431562269125666905072137487553397704288982192417014627283727865253647533575763327902805648397572591874334849305412123271968764998056386532874964011223081904321011415329205376507691952318739513086125990300 := by
    have e := r 214 (by norm_num)
    simp only [Nat.reduceSub, h213, h212, h211, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h215 : a 215 = 24072094889510937931302149877338521287099521675549575501723791931972967651580048552696454680442507898820335652346688341278264086617071188242916117967922949635003899041437860601673804088610714169470712833653190455900032399790552676108265170188863929866234957949292755 := by
    have e := r 215 (by norm_num)
    simp only [Nat.reduceSub, h214, h213, h212, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h216 : a 216 = 409476056412440834484638776783954057341275242858969339353683712897847821661304286033269470876593597153047863748304637163293098499203967096734993690711784761058278937725476982771843264991328752588333972131527121980807067140457660627823041194745024592685040639354651921 := by
    have e := r 216 (by norm_num)
    simp only [Nat.reduceSub, h215, h214, h213, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h217 : a 217 = 6965353100537354962333508107877865447684140999700969763807034057153514168134416240108352633834965799454883325535320738145070825022019041772051218220789186321609459599686656291953283501378489535381736778820118107006473513293410968740224694373166949543158742621214511212 := by
    have e := r 217 (by norm_num)
    simp only [Nat.reduceSub, h216, h215, h214, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h218 : a 218 = 118483469437094322063116046512424927369952278934317761267049129597459967132824259688137513880544817077302579698715903548851601426660888680586204877792577030933529037545818503897554229531185100855705269232402390274708256339531376391746127133155939071808256375788711243955 := by
    have e := r 218 (by norm_num)
    simp only [Nat.reduceSub, h217, h216, h215, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h219 : a 219 = 2015451668741366658352521355944126273934095029483077340552690665233403085922888570933980316010824545753456068111229416148336191699268271072383244229024633725536787192750444544791569379821646601546134638119819373069315532345360402379634863381297700825985926562078340531553 := by
    have e := r 219 (by norm_num)
    simp only [Nat.reduceSub, h218, h217, h216, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h220 : a 220 = 34283646894632804544583309984052281467981989806150818973969491961765163229468048138204285949190872573693687371032121487736535868763913230326292639716120301756556378879907762577266887717479878473644649802365850078954981677024550463283175658893992515819964785534423497123388 := by
    have e := r 220 (by norm_num)
    simp only [Nat.reduceSub, h219, h218, h217, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h221 : a 221 = 583178680305379723407385166433658962246448589828966551240295366200876738447020167284772916257928030859463905259875272057985523540712540745091151251113973685153925821625540949303762901363542989241525307509085637251458088453009279008709175284714987322760071691386235834213779 := by
    have e := r 221 (by norm_num)
    simp only [Nat.reduceSub, h220, h219, h218, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h222 : a 222 = 9920104888723708969253195840373036871822530686485819107291253048063402073625890451986268137909815853544031691835354534647413729377087350101862498489447328077215780325815597677114154239580207643157928992523144212130772067925347247978024267411710609191177380567231335911315889 := by
    have e := r 222 (by norm_num)
    simp only [Nat.reduceSub, h221, h220, h219, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h223 : a 223 = 168744990732083572937087548112998553842677722402801779909556024295813999704874605177116471257436125325076291043266452660235707420788502707252185528615692866773230402056171992784162648546182354624295293083169415342369213499705568788149157262059279448351296034336837017366856460 := by
    have e := r 223 (by norm_num)
    simp only [Nat.reduceSub, h222, h221, h220, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h224 : a 224 = 2870420445809869132772038121431277226725893531276510545852379530950089122718235896120979458686712953947808484753726795949842642553211657802957740367440630431629977653777981901717626498905590634406796557101276006110886988324577886740391769268433451408644568960614053329468882803 := by
    have e := r 224 (by norm_num)
    simp only [Nat.reduceSub, h223, h222, h221, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h225 : a 225 = 48827011101057726904492190870679488891977352324492679591897930507774441456884122372905959515000818920488204088170927020322496838614107462456107696796254147611401829591720445954504214970587100232535625757909537500257617206066574781903116895081664004866632485036834504915579441665 := by
    have e := r 225 (by norm_num)
    simp only [Nat.reduceSub, h224, h223, h222, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h226 : a 226 = 830567179293542056488020057249400608636543394934012838689383413822974197893880071763042660616096528847696209909053755804188988995101999481655257988503141439690635855084239155229311003919239741622772300338399041695697210502460471216059290783987891621864478670106084918651183400668 := by
    have e := r 226 (by norm_num)
    simp only [Nat.reduceSub, h225, h224, h223, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h227 : a 227 = 14128283172849934519342024630410451954539052556764839789669482652065034557934790039798937477567027827976054453755532600548237512759603135441354085136205489796309391678870894338228744510612984438937969579711275382241557777911350495040545575453117753256841745911391681375373132893779 := by
    have e := r 227 (by norm_num)
    simp only [Nat.reduceSub, h226, h225, h224, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h228 : a 228 = 240327802962327620708639548102037570991312753927393391748784017471819719502388933035124296346045558139553787066518714986839711750167757797510289197548848909910390668781605356661754908674751755800312756394819347014798572794110486839958690436955846400920041304373248985231176330411601 := by
    have e := r 228 (by norm_num)
    simp only [Nat.reduceSub, h227, h226, h225, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h229 : a 229 = 4088072993022309897775382061563557550285944261793376319777346411879478627328032330632229378111716164796522687645846934795564691419680057700373096831627592978117281858994982609414851837926523476661536016086902588050077534330755180177313452932726676086191441218875139241444254182281644 := by
    have e := r 229 (by norm_num)
    simp only [Nat.reduceSub, h228, h227, h226, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h230 : a 230 = 69539772719921696799619346249856769598488818468620083070908300262294045900267851493225838599559281970088774714693339150103764140706094294807673978143311052680755850788192117195979033730277069076901293455756205488514734847526189642923719752236965691320578757582491132550528273568686643 := by
    have e := r 230 (by norm_num)
    simp only [Nat.reduceSub, h229, h228, h227, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h231 : a 231 = 1182899619990218568801383314635700114730717479673351281040735474626272782858848062652979745421774871842351939818501350476743799118920934460265686676502231603812221275895318499947793856531190173202779146174414925034593389923158432294121127574843761578923149741859998906807188436224192161 := by
    have e := r 231 (by norm_num)
    simp only [Nat.reduceSub, h230, h229, h228, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h232 : a 232 = 20121600290651325027854280346194868914316682753250484592286528519142618653718092463965030299476168076982920434002174440167610443482486459311519124123038462015794875594982676859776666669029538684850885274195593294843901278060588966120500500183522739067807444192138220598892512130828010364 := by
    have e := r 232 (by norm_num)
    simp only [Nat.reduceSub, h231, h230, h229, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h233 : a 233 = 342276547742983840287129478352450476883735480826370908186919004096378673253462670029153333096122802232970756471849760085224668640351305422628783361074149731134794524479566135475407420757809468848591210699118914060541708829087804201341697554163412806053161598402054873232272498830338755347 := by
    have e := r 233 (by norm_num)
    simp only [Nat.reduceSub, h232, h231, h230, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h234 : a 234 = 5822262317241513549945836045932953174331589812086129005835339301512812245002559610082429976497658957831692853297989076982312564141789785561557116648912552648853930693885072520942433705560353846686062559112775323373568643913629042336811663134913727779866630520641031080852224354139448161009 := by
    have e := r 234 (by norm_num)
    simp only [Nat.reduceSub, h233, h232, h231, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h235 : a 235 = 99039033536779595638976382334365926275720328727745057223095675730546190177144922746934952509363658732293988376461633626622191712842022849538738498654865006293430488062196041515459907081917411320923742321777561105283394037467933278401452963845127466716836576230609648159335591349369365347404 := by
    have e := r 235 (by norm_num)
    simp only [Nat.reduceSub, h234, h233, h232, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h236 : a 236 = 1684693960774092865648524523033219393185204881452182909083844960663448743830917768927568475972334138175567904662539864088366426321491259951803308626726579563401285104408503852387105150207547013738509405079543649316343683357261265516342728282743792882681344164063376281564305462309793916492019 := by
    have e := r 236 (by norm_num)
    simp only [Nat.reduceSub, h235, h234, h233, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h237 : a 237 = 28657324694254977121964651569256034265983561056045648705566765256787995463872711159974445024368076782307304667693467476051099063280208385032333185519921941847031322233292370516803053388732371691021978752846440744955896050096118640463512470486600814283381554538019031999620597309657913671457601 := by
    have e := r 237 (by norm_num)
    simp only [Nat.reduceSub, h236, h235, h234, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h238 : a 238 = 487472667293593789600101931847704678947045658232039780102595514865831724967186978570036044555098548215147631418181024086184339818105245485607925123484231480874825736237508058056822574059511022002619215810964150458092609018466727087498434385061125851166132059243158385200883761447603155216407580 := by
    have e := r 238 (by norm_num)
    simp only [Nat.reduceSub, h237, h236, h235, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h239 : a 239 = 8292106953234512100204618149657770504861166882660391349722516688526639037492418498085601243797430718505359088111495318843947746002568504001041813963977685002831450846809210303549367340297514087543209515868123387442101437797028821410708098820567327183750087743374824312472744265446574437519498195 := by
    have e := r 239 (by norm_num)
    simp only [Nat.reduceSub, h238, h237, h236, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h240 : a 240 = 141052088326560729813371105354060218781863112808674053643507444506223663425844083489785614958770267687853949863965892899768580634975846896112866097913825969343151051620727990031160824611674997306562873283029211566544434506866611030103046939747893276574950281933082905249242847911704157801647470481 := by
    have e := r 240 (by norm_num)
    simp only [Nat.reduceSub, h239, h238, h237, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h241 : a 241 = 2399352991162656605873111982122813624291275445414870746367912736086207273127301220124460550919120601737010439935677140277703237783138492301121254526770239923104151768091859928020487869701939313991075386306011221912284191528270882153937527993143897267041579031776379996156788786104150812892496790252 := by
    have e := r 241 (by norm_num)
    simp only [Nat.reduceSub, h240, h239, h238, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h242 : a 242 = 40813963440746439860253410147346683044665489348504231263001908724332374360065070966632416563170656467157956401536916343156908354504294256959159607657512217072074090797327017822129763466780478137929239507263066256651186270358313204147291109439706204235709292593724295299540033791966015934848819930035 := by
    have e := r 242 (by norm_num)
    simp only [Nat.reduceSub, h241, h240, h239, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h243 : a 243 = 694262002247280284012793889012059582320658510790665365466391256826649440106271690484018543515397496795792313967967732473348385135466479004061254459333684366577559580599960971043790215260406617696496266783815728623050828704523462798236443731311678863402050249178026239414847963378762563496099371014113 := by
    have e := r 243 (by norm_num)
    simp only [Nat.reduceSub, h242, h241, h240, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h244 : a 244 = 11809677059768234075595525955602640191755782316554007253742502496472165954342901592113205208612060413571309147697888888426191610328470498433784787852955363089967128836243377486574276592717865828582490719423846295741743295565861388424011709149834232320331981422175301045405760368225471483988043172106428 := by
    have e := r 244 (by norm_num)
    simp only [Nat.reduceSub, h243, h242, h241, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h245 : a 245 = 200887376530136809411093187392194089279543641041329729441406906974712817422894687762875653258036035336967836435210562006914409043756404832780974413452369685857009712525574799993296675602929199009667829143887519828639570245539150681148373423746337741449745804329846003877119213750124253568204949817802899 := by
    have e := r 245 (by norm_num)
    simp only [Nat.reduceSub, h244, h243, h242, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h246 : a 246 = 3417175410040632070088000597176733323791508460868090092641130443471016969982064789894223050986009096186883436150725894751344267962290821949653492254112568441527046407642615523778004698828868556345184638430538263181891725867868094488771049700599212332878381951541064999604624522633035106254526798880558129 := by
    have e := r 246 (by norm_num)
    simp only [Nat.reduceSub, h245, h244, h243, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h247 : a 247 = 58127533868384126723848765976018223631050606523367105202788229411031390983757195493675082647099621824723987922929780328341800281858101790998817355703424658108557258838742631419407336683395644535277651812391104145780414503861374697552320054405835268147897591240617496782520055453356564459119327926377801100 := by
    have e := r 247 (by norm_num)
    simp only [Nat.reduceSub, h246, h245, h244, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h248 : a 248 = 988772827901148871043761717565995817801738208383530262327861333733358684249933862553690368906067075621777128415864043608465147332937431601270614897423998580685002310690909302453796574858113816869929915841064883463847984308073689843342134746667350042466840991781420666248165898237192891361328232249853936243 := by
    have e := r 248 (by norm_num)
    simp only [Nat.reduceSub, h247, h246, h245, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h249 : a 249 = 16819425152447346085486565956237472859727519030591228303479455076669534785652883951847892231336435780048318802886508359145730485190322367505304121720353824571572217890877204155801057043487726371535253636172466587346649663578963948711525816051942397017423897104203193913006875582168773226114135900989566903425 := by
    have e := r 249 (by norm_num)
    simp only [Nat.reduceSub, h248, h247, h246, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h250 : a 250 = 286105214945348654550181500249938779302334853237107271948639562425361010566576360307056407144566080630897060946565489224489098191622404254117457241163591071083892904831860983111200063600581923109475354605399521410315966462096401572173548526868006405584602525485867072232409770018759345832873967958103202079068 := by
    have e := r 250 (by norm_num)
    simp only [Nat.reduceSub, h249, h248, h247, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h251 : a 251 = 4866765259632758389243959406159272779550195689144045427757761957635539692837951935096055148524274867446593475096677728564941887680110070645084288612937466052868161567682841186811848986205366825796437263106189422194224207738904759017855060886354708391361131056479003532536498643325756951905912995937246047140179 := by
    have e := r 251 (by norm_num)
    simp only [Nat.reduceSub, h250, h249, h248, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h252 : a 252 = 82785642676567978426500679481570251411619476302257602347581880471156162301812618881614123440818528726302309674349675757800460961960829092075476105957015560425840628504967880300731418030482989792447415276504205166489274402733371809593748222170170855500479895926170082410570790448406264703067796996277432066814161 := by
    have e := r 252 (by norm_num)
    simp only [Nat.reduceSub, h251, h250, h249, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h253 : a 253 = 1408217217752053510476052969589354403866848604882203783529368776093335244675720403878237363942415338085753299085789248762029930866331490976370533688505911718296984345484490752535689154614008046373869841999202083952767465523736875900101145158403107162221334926444568265500986199485969626062398226381240146353873964 := by
    have e := r 253 (by norm_num)
    simp only [Nat.reduceSub, h252, h251, h250, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h254 : a 254 = 23954343630826619039069985730814365298234343019651705286358242406650957766089328157720304538382539428039856085481413416512400099262074634701343368769976390246734420239793750896792081160661744642587084607579452980452817049397915595485063245062614026695784117810693124546471825200703329310437154863534238475422709043 := by
    have e := r 254 (by norm_num)
    simp only [Nat.reduceSub, h253, h252, h251, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h255 : a 255 = 407473059944332625476694800880691580954088007270729587218753343362563430995968922420780816788274126212595074416828921868863625164854148673610151137294706328066820359622908705673790829033436905113260044356978843879319807463650034793811863836112459169013544619165261304401774023545164880197651081748515410179604529441 := by
    have e := r 255 (by norm_num)
    simp only [Nat.reduceSub, h254, h253, h252, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h256 : a 256 = 6931281321635952502996216859128320279863594586153703835035753916704922591272100923656698866843848870308955574984372035704525608869653961212404725231140901203326522752992458876815736526564493018918773660888230969753550799414116190827685332426756776399654943954649911343659616418675702717905631969418958849479745474044 := by
    have e := r 256 (by norm_num)
    simp only [Nat.reduceSub, h255, h254, h253, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h257 : a 257 = 117903894716923952509865401605830735224459915169608570908817554533653134073896434030376577289596349369472281863954413741014625374559302444398671672903910357321163425277137597098986222644380553801736193094950792987963343958812054460527671629660101061589406614198864050402964647588222264474247274393781336512679359661587 := by
    have e := r 257 (by norm_num)
    simp only [Nat.reduceSub, h256, h255, h254, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h258 : a 258 = 2005592868670122488414034316945921136962324920367709195063871634181732313813567914526167581354945950384361416220373800726789066224069837434559281048675491087070169267429610887680148449874565790976848415654054007950819920794727941532684736942942900395053377760667025109932433789088821890457342181519222463822514396308849 := by
    have e := r 258 (by norm_num)
    simp only [Nat.reduceSub, h257, h256, h255, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h259 : a 259 = 34115944723606102920506501753658693579665893237214513033304134780789233552626741568044031676187863621719290979560527817596565392659571383374932783347151286220667469653038628263386089559140096098143296427961433694575352286277389433844580605005714812907901659330173192160443104432236734564198385512648697797602707660275404 := by
    have e := r 259 (by norm_num)
    simp only [Nat.reduceSub, h258, h257, h256, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h260 : a 260 = 580325998643936936801886448506662081698140071140639910768510717144127558831433624494849433994494278628439696122653984907494195986192953120586835194529592611835920865415206365005857863838234871706188580987669115713900321972086979554443167619224853304967129893774827195131823704070878197779190434055034146311891033585728499 := by
    have e := r 260 (by norm_num)
    simp only [Nat.reduceSub, h259, h258, h257, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h261 : a 261 = 9871579621509152313714779645929671186530574553742945067367092123352413481293608407177118063443621356999813065237593038034822850230802796709267301155668768812212339811967532280935447696510888994029673295399179644719569346920629850677920843814627020391818362564852897157862392000589922590344032973906960070606235077069336001 := by
    have e := r 261 (by norm_num)
    simp only [Nat.reduceSub, h260, h259, h258, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h262 : a 262 = 167919556338169040829066049404759850542602584979449702873542818927204107471086002164553240069069427256921191731447888242053130734412606497810881895874038544412356353093720714345221063450695386424836628452782263004222524287614910989005273383997804192585168670265651654188546284252048247949728973593296273577451449436520584860 := by
    have e := r 262 (by norm_num)
    simp only [Nat.reduceSub, h261, h260, h259, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h263 : a 263 = 2856379473389367729292611209247753861267000558208418935166835863845804454666115574461654307161700964823861916754134537364233126591438411915806043838290909727256567450289406787039611516264597170012365716858870283096507877728764898950005364025108150348070145938568083437631303692428417842966827917983173132838914401027719079635 := by
    have e := r 263 (by norm_num)
    simp only [Nat.reduceSub, h262, h261, h260, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h264 : a 264 = 48588168489256292306411449691573560095470184030770170369766613214578946048056940250312196808929775130264576393638408720901528762885634369912583884930640141144403030250646090642085520572197694830718638388917988560618782474819729375229605569997431581824292192550015129533710635567526892662120987117672542090850508975828774234641 := by
    have e := r 264 (by norm_num)
    simp only [Nat.reduceSub, h263, h262, h261, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h265 : a 265 = 826504370002011970366680331274331637576663692891589019380969661046707029767038895799465254698000906197724763924366812357301478265365446209460379741116936769560335092767960857701660366355315673882281505530125724131556694609637555524007226226605475782664845057905106162352072460360856917627727403288110240847213246698005592880492 := by
    have e := r 265 (by norm_num)
    simp only [Nat.reduceSub, h264, h263, h262, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h266 : a 266 = 14059173145896008640329880524425742844841014955372865634753915148914757189722392550798758366374681366984051496273316335271927395501818082163917754870182492487488507663001928976551757187384859790449331112365031114833731480550455464698052376325939005782253676133796866721392104210008096642531951252163782212633730901227535786088115 := by
    have e := r 266 (by norm_num)
    simp only [Nat.reduceSub, h265, h264, h263, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h267 : a 267 = 239152213491384570763684888950829930158537335357799522425020794607593474010374915095873986727742567293102896131059806789887445799115873961817286038145190347080843322940291708190092335263887164383890849478290802836456328909319904244137683145787604531935437248636751628612545895132553123343401204870424992266348731441904511117093473 := by
    have e := r 267 (by norm_num)
    simp only [Nat.reduceSub, h266, h265, h264, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h268 : a 268 = 4068075741319405544037839468050693912613902424337482500588773848223349916949357404639464019172226312662965139029348896390356285284756559186125335086962781278087980306349209516200298211544492234882241831165886919196749529214453901837702564687542739387727379072147903066861743307018359196633564250403355107368701179959832146476350268 := by
    have e := r 268 (by norm_num)
    simp only [Nat.reduceSub, h267, h266, h265, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h269 : a 269 = 69199611391878734698442337518470666044767104339719781913547621402319735461493337298255579695526344343425733538682164616732137312102951926975653133948329917179751669423594826477923437330896867120315711343725257993573526084827329858979308549565451028042349330009277947631162692655504546113118546144197168866557396558141865500209814419 := by
    have e := r 269 (by norm_num)
    simp only [Nat.reduceSub, h268, h267, h266, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h270 : a 270 = 1177113338414378511426865988836740397651435153504564581716948046563152544126190842663642083028931684208796994750791310085778266349847317082306786607674538708474734553986297175726237440143096812978874862781799201570236304366548582845068020343259183752660569867748958489996051875918739899392841231833569275947115560428184882494403886769 := by
    have e := r 270 (by norm_num)
    simp only [Nat.reduceSub, h269, h268, h267, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h271 : a 271 = 20023173304057841751338634395190347711342570079976592916093421579100786086769446658915218494918953807515693132355723551525497677265520750497585270773198009023357007362901757880597155744801919796472836992997989267818836206907150883599407818479345976471843853774731501634627980176975825807038549587809227888464360107317847217854406985740 := by
    have e := r 271 (by norm_num)
    simp only [Nat.reduceSub, h270, h269, h268, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have h272 : a 272 = 340602264947911385998405457981814062165848387052350567208515448191644039722745877322046778380913777591167619975256541381384988857494258748563597245876764073265027336351385853575186956979143177213332683784935463142580422456600530986009290614798224469381413193418054595011835437187330714973464524578571683015709433833017601469016385242483 := by
    have e := r 272 (by norm_num)
    simp only [Nat.reduceSub, h271, h270, h269, Int.reduceMul, Int.reduceAdd, Int.reduceSub] at e
    exact e
  have hpos : (0 : ℚ) < (a 270 : ℚ) := by
    rw [h270]
    norm_num
  rw [div_lt_iff₀ hpos, h270, h271, h272] at hlt
  norm_num at hlt
